/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedWrongDownAllTestsNotSent
public import Bandits.Support.ReferenceGeneratedContinuingLiveDownErrorEvent

import Mathlib.MeasureTheory.Measure.Real
import Lean.Elab.Tactic.Omega

/-!
# All actual generated suffix wrong unique DOWN diagnostics

Sources: `sources/zip4/manuscript/appendix_a_local_protocol.tex:92-155`,
`sources/zip4/manuscript/05_binary_transport.tex:20-42,60-124`,
`sources/zip4/manuscript/06_interruptions.tex:246-295,327-348`,
`sources/zip4/manuscript/07_public_setup.tex:127-164`, and
`sources/zip4/manuscript/08_main_theorem.tex:29-42`.

The event observes every record of the actual generated physical suffix,
including cutoff, collection, replacement and noncontinuing branches. Its
only test is an actual saved ordinary wrong unique DOWN diagnostic. Completion
is proved from that diagnostic. The same source, cut, index and inherited or
later test bank then enter the existing joint cohort union, once.

The suffix is observed through T without stopping physical play. This is an
internal DOWN envelope, not the full manuscript false event: prelaunch
suppression, UP diagnostics, ambiguity and queue failure remain separate.
No source theorem or main regret closure is asserted here.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ReferenceGeneratedDownBatchCalendar
open Bandits.Support.ReferenceDownCompletedAmbiguityMeasurability
open Bandits.Support.ReferenceGeneratedInheritedDownWrongCompletionWitness

namespace Bandits.Support.ReferenceGeneratedAllWrongDownEvent

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
variable (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
variable (C_star C_h : ℝ)

abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput

/-- A wrong unique ordinary DOWN diagnostic at any actual suffix record.
There is no phase, selection, completion, survival or payload gate. -/
def generatedAllWrongDownFibreEvent (s : Fin p.T) :
    Set (LaunchSource rate rewards C_star C_h s.val s.isLt) :=
  {x | ∃ i : Fin (p.m - 1), ∃ n : Fin (p.T - s.val), ∃ cut,
    ((generatedSourceRecordAt rate rewards C_star C_h s.val s.isLt x n).output.followers i).down =
      some cut ∧ ReferenceDownReception.wrongUniqueAccepted cut}

/-- The finite union of genuine launch-fibre images in the original source.
All continuous rows, private arrays and the original J remain coordinates. -/
def generatedAllWrongDownSourceEvent : Set (SourceInput p) :=
  ⋃ s : Fin p.T,
    (Subtype.val : LaunchSource rate rewards C_star C_h s.val s.isLt → SourceInput p) ''
      generatedAllWrongDownFibreEvent rate rewards C_star C_h s

theorem mem_generatedAllWrongDownFibreEvent_iff (s : Fin p.T)
    (x : LaunchSource rate rewards C_star C_h s.val s.isLt) :
    x ∈ generatedAllWrongDownFibreEvent rate rewards C_star C_h s ↔
      ∃ i : Fin (p.m - 1), ∃ n : Fin (p.T - s.val), ∃ cut,
        ((generatedSourceRecordAt rate rewards C_star C_h s.val s.isLt x n).output.followers i).down =
          some cut ∧ ReferenceDownReception.wrongUniqueAccepted cut := Iff.rfl

/-- Exact original-source existential characterization, retaining the literal
subtype value and actual generated record. -/
theorem mem_generatedAllWrongDownSourceEvent_iff (source : SourceInput p) :
    source ∈ generatedAllWrongDownSourceEvent rate rewards C_star C_h ↔
      ∃ s : Fin p.T, ∃ x : LaunchSource rate rewards C_star C_h s.val s.isLt,
        x.val = source ∧ ∃ i : Fin (p.m - 1), ∃ n : Fin (p.T - s.val), ∃ cut,
          ((generatedSourceRecordAt rate rewards C_star C_h s.val s.isLt x n).output.followers i).down =
            some cut ∧ ReferenceDownReception.wrongUniqueAccepted cut := by
  simp [generatedAllWrongDownSourceEvent, generatedAllWrongDownFibreEvent]

def wrongUniqueDiagnostic
    (diagnostic : ReferenceDownCompletedAmbiguityMeasurability.DownDiagnosticCode p rate) : Bool :=
  match diagnostic.2.2 with
  | none => false
  | some fields =>
      decide (fields.1 ≠ none ∧ fields.2.2.1 = some false ∧ fields.2.2.2 = true)

private theorem wrongUniqueDiagnostic_eq_true_iff_record
    (record : ReferenceFollowerDownDecoderReplay.Record p rate)
    (i : Fin (p.m - 1)) :
    wrongUniqueDiagnostic (p := p) (rate := rate)
        ((ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation
          record.input i).2.2.2) = true ↔
      ∃ cut, (record.output.followers i).down = some cut ∧
        ReferenceDownReception.wrongUniqueAccepted cut := by
  rw [ReferenceGeneratedDownBatchBankBridge.roundDownObservation_diagnostics_eq_actual
    record i]
  cases hdown : (record.output.followers i).down with
  | none => simp [wrongUniqueDiagnostic]
  | some cut =>
      have hleft :
          wrongUniqueDiagnostic (p := p) (rate := rate)
              ((record.output.followers i).downInput.map
                (FollowerDownMeasurability.followerStateCode rate),
               (record.output.followers i).failure,
               (record.output.followers i).down.map
                ReferenceDownCompletedAmbiguityMeasurability.cutFields) = true ↔
            cut.raw ≠ none ∧ cut.rawComparison = some false ∧ cut.ordinaryAcceptance := by
        simp [wrongUniqueDiagnostic, hdown,
          ReferenceDownCompletedAmbiguityMeasurability.cutFields]
      rw [hdown] at hleft
      have hright :
          (∃ savedCut, (record.output.followers i).down = some savedCut ∧
            ReferenceDownReception.wrongUniqueAccepted savedCut) ↔
            ReferenceDownReception.wrongUniqueAccepted cut := by
        simp [hdown]
      rw [hdown] at hright
      rw [hleft, hright]
      constructor
      · rintro ⟨hraw, hcomparison, haccept⟩
        exact ⟨hcomparison, hraw, haccept⟩
      · rintro ⟨hcomparison, hraw, haccept⟩
        exact ⟨hraw, hcomparison, haccept⟩

local instance downCallOptionMeasurableSpace : MeasurableSpace
    (Option (ReferenceDownCompletedAmbiguityMeasurability.DownCallCode p)) :=
  LaterAssignmentStartMeasurability.optionMeasurableSpace

local instance downFailureOptionMeasurableSpace : MeasurableSpace
    (Option DeclaredFollowerLocalRound.RoundFailure) :=
  LaterAssignmentStartMeasurability.optionMeasurableSpace

local instance downBoolOptionMeasurableSpace : MeasurableSpace (Option Bool) :=
  LaterAssignmentStartMeasurability.optionMeasurableSpace

local instance downCutFieldsOptionMeasurableSpace : MeasurableSpace
    (Option (ReferenceDownCompletedAmbiguityMeasurability.DownCutFields p)) :=
  LaterAssignmentStartMeasurability.optionMeasurableSpace

private theorem downCallOptionMeasurableSpace_eq :
    (downCallOptionMeasurableSpace (p := p) : MeasurableSpace
      (Option (ReferenceDownCompletedAmbiguityMeasurability.DownCallCode p))) =
      (LaterAssignmentStartMeasurability.optionMeasurableSpace : MeasurableSpace
        (Option (ReferenceDownCompletedAmbiguityMeasurability.DownCallCode p))) := by
  delta downCallOptionMeasurableSpace
  rfl

private theorem downFailureOptionMeasurableSpace_eq :
    downFailureOptionMeasurableSpace =
      LaterAssignmentStartMeasurability.optionMeasurableSpace := by
  delta downFailureOptionMeasurableSpace
  rfl

private theorem downCutFieldsOptionMeasurableSpace_eq :
    (downCutFieldsOptionMeasurableSpace (p := p) : MeasurableSpace
      (Option (ReferenceDownCompletedAmbiguityMeasurability.DownCutFields p))) =
      (LaterAssignmentStartMeasurability.optionMeasurableSpace : MeasurableSpace
        (Option (ReferenceDownCompletedAmbiguityMeasurability.DownCutFields p))) := by
  delta downCutFieldsOptionMeasurableSpace
  rfl

private theorem downBoolOptionMeasurableSpace_eq :
    downBoolOptionMeasurableSpace =
      LaterAssignmentStartMeasurability.optionMeasurableSpace := by
  delta downBoolOptionMeasurableSpace
  rfl

local instance downFollowerStateCodeMeasurableSingleton : MeasurableSingletonClass
    (FollowerDownMeasurability.FollowerStateCode p rate) := ⟨fun _ => trivial⟩

private theorem measurableSet_laterOptionSingleton {α : Type*}
    [MeasurableSpace α] [MeasurableSingletonClass α] (a : Option α) :
    MeasurableSet[LaterAssignmentStartMeasurability.optionMeasurableSpace] {a} := by
  let e := Equiv.optionEquivSumPUnit α
  have he : @Measurable (Option α) (α ⊕ PUnit)
      LaterAssignmentStartMeasurability.optionMeasurableSpace inferInstance e :=
    comap_measurable _
  have hset : ({a} : Set (Option α)) = e ⁻¹' {e a} := by
    ext x
    exact ⟨fun h => congrArg e h, fun h => e.injective h⟩
  rw [hset]
  apply he
  cases h : e a with
  | inl value =>
      simpa only [Set.image_singleton] using
        (measurableSet_singleton value).inl_image (β := PUnit)
  | inr value =>
      simpa only [Set.image_singleton] using
        (measurableSet_singleton value).inr_image (α := α)

local instance laterOptionMeasurableSingletonClass {α : Type*}
    [MeasurableSpace α] [MeasurableSingletonClass α] :
    @MeasurableSingletonClass (Option α)
      LaterAssignmentStartMeasurability.optionMeasurableSpace :=
  ⟨measurableSet_laterOptionSingleton⟩

local instance downFollowerStateOptionMeasurableSingleton : MeasurableSingletonClass
    (Option (FollowerDownMeasurability.FollowerStateCode p rate)) := ⟨fun _ => trivial⟩

/-- The canonical countable diagnostic is measurable on the genuine launch
fibre. The operational input keeps its original continuous measurable space. -/
private theorem measurable_wrongUniqueDiagnostic (s : Fin p.T)
    (i : Fin (p.m - 1)) (n : Fin (p.T - s.val)) :
    Measurable (fun x : LaunchSource rate rewards C_star C_h s.val s.isLt =>
      wrongUniqueDiagnostic (p := p) (rate := rate)
        (((generatedSourceObservation rate rewards C_star C_h s.val s.isLt i x).2 n).2.2.2)) := by
  classical
  let input := fun x : ReferenceGeneratedDownBatchCalendar.LaunchSource
      rate rewards C_star C_h s.val s.isLt =>
    ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput
      rate rewards C_star C_h s.val s.isLt x
  let observation := fun x : ReferenceGeneratedDownBatchCalendar.LaunchSource
      rate rewards C_star C_h s.val s.isLt =>
    ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
      rate rewards C_star C_h s.val s.isLt i x
  have hfiber : Measurable (fun x : ReferenceGeneratedDownBatchCalendar.LaunchSource
      rate rewards C_star C_h s.val s.isLt =>
      ReferenceGeneratedDownAmbiguityMeasurability.generatedActiveRunInput
        (rate := rate) rewards C_star C_h s.val
        (ReferenceGeneratedLiveLaterDownEvent.launchFiberOfSource
          (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) s x)) := by
    have hmap : Measurable (fun x : ReferenceGeneratedDownBatchCalendar.LaunchSource
        rate rewards C_star C_h s.val s.isLt =>
        ReferenceGeneratedLiveLaterDownEvent.launchFiberOfSource
          (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) s x) := by
      have hmap' : Measurable (fun x : ReferenceGeneratedDownBatchCalendar.LaunchSource
          rate rewards C_star C_h s.val s.isLt =>
          (⟨x.1, (ReferenceGeneratedLiveLaterDownEvent.launchFiberOfSource
            (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) s x).property⟩ :
            ReferenceGeneratedDownAmbiguityMeasurability.GeneratedLaunchFiber
              (rate := rate) rewards C_star C_h s.val)) :=
        measurable_subtype_coe.subtype_mk
          (h := fun x => (ReferenceGeneratedLiveLaterDownEvent.launchFiberOfSource
            (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) s x).property)
      have heq : (fun x : ReferenceGeneratedDownBatchCalendar.LaunchSource
          rate rewards C_star C_h s.val s.isLt =>
          (⟨x.1, (ReferenceGeneratedLiveLaterDownEvent.launchFiberOfSource
            (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) s x).property⟩ :
            ReferenceGeneratedDownAmbiguityMeasurability.GeneratedLaunchFiber
              (rate := rate) rewards C_star C_h s.val)) =
        (fun x => ReferenceGeneratedLiveLaterDownEvent.launchFiberOfSource
          (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) s x) := by
        funext x
        apply Subtype.ext
        rfl
      rw [← heq]
      exact hmap'
    exact (ReferenceGeneratedDownAmbiguityMeasurability.measurable_generatedActiveRunInput
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) s.val).comp hmap
  have hinput : Measurable input := by
    have heq : input = fun x =>
        ReferenceGeneratedDownAmbiguityMeasurability.generatedActiveRunInput
          (rate := rate) rewards C_star C_h s.val
          (ReferenceGeneratedLiveLaterDownEvent.launchFiberOfSource
            (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) s x) := by
      funext x
      exact (ReferenceGeneratedLiveLaterDownEvent.generatedActiveRunInput_eq_generatedSourceRunInput
        (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) s x).symm
    rw [heq]
    exact hfiber
  have hobs : Measurable observation := by
    rw [downCallOptionMeasurableSpace_eq, downFailureOptionMeasurableSpace_eq,
      downCutFieldsOptionMeasurableSpace_eq, downBoolOptionMeasurableSpace_eq]
    exact (ReferenceDownCompletedAmbiguityMeasurability.measurable_runDownObservation
      s.val (p.T - s.val) (by omega) i).comp hinput
  have hround (k : Fin (p.T - s.val)) :
      Measurable (fun x : ReferenceGeneratedDownBatchCalendar.LaunchSource
        rate rewards C_star C_h s.val s.isLt => (observation x).2 k) :=
    (measurable_pi_apply k).comp (measurable_snd.comp hobs)
  have hdiagnosticProjection : Measurable
      (fun r : ReferenceDownCompletedAmbiguityMeasurability.DownRoundCode p rate => r.2.2.2) :=
    measurable_snd.comp (measurable_snd.comp measurable_snd)
  have hwrong : Measurable (fun x : ReferenceGeneratedDownBatchCalendar.LaunchSource
      rate rewards C_star C_h s.val s.isLt =>
      wrongUniqueDiagnostic (p := p) (rate := rate) (((observation x).2 n).2.2.2)) :=
    (measurable_of_countable (fun d :
      ReferenceDownCompletedAmbiguityMeasurability.DownDiagnosticCode p rate =>
        wrongUniqueDiagnostic (p := p) (rate := rate) d)).comp
      (hdiagnosticProjection.comp (hround n))
  exact hwrong

/-- The actual diagnostic agrees with the countable current DOWN code,
without reading any dispatch tag or using a selected/live premise. -/
theorem generatedRecord_wrongUnique_iff_code (s : Fin p.T)
    (x : LaunchSource rate rewards C_star C_h s.val s.isLt)
    (i : Fin (p.m - 1)) (n : Fin (p.T - s.val)) :
    (∃ cut,
      ((generatedSourceRecordAt rate rewards C_star C_h s.val s.isLt x n).output.followers i).down =
        some cut ∧ ReferenceDownReception.wrongUniqueAccepted cut) ↔
      wrongUniqueDiagnostic (p := p) (rate := rate)
        (((generatedSourceObservation rate rewards C_star C_h s.val s.isLt i x).2 n).2.2.2) = true := by
  exact (wrongUniqueDiagnostic_eq_true_iff_record (p := p) (rate := rate)
    (generatedSourceRecordAt rate rewards C_star C_h s.val s.isLt x n) i).symm

/-- Borelness uses only finite follower/round unions and the actual diagnostic
projection; no discrete space is installed on physical round inputs. -/
theorem measurableSet_generatedAllWrongDownFibreEvent (s : Fin p.T) :
    MeasurableSet (generatedAllWrongDownFibreEvent rate rewards C_star C_h s) := by
  classical
  have heq : generatedAllWrongDownFibreEvent rate rewards C_star C_h s =
      ⋃ i : Fin (p.m - 1), ⋃ n : Fin (p.T - s.val),
        {x | wrongUniqueDiagnostic (p := p) (rate := rate)
          (((generatedSourceObservation rate rewards C_star C_h s.val s.isLt i x).2 n).2.2.2) = true} := by
    ext x
    simp only [mem_generatedAllWrongDownFibreEvent_iff, Set.mem_iUnion, Set.mem_ofPred_eq]
    exact exists_congr fun i => exists_congr fun n =>
      generatedRecord_wrongUnique_iff_code rate rewards C_star C_h s x i n
  rw [heq]
  apply MeasurableSet.iUnion
  intro i
  apply MeasurableSet.iUnion
  intro n
  exact (measurable_wrongUniqueDiagnostic rate rewards C_star C_h s i n)
    (measurableSet_singleton true)

/-- Genuine measurable subtype images give an ambient Borel event on the
original complete source. -/
theorem measurableSet_generatedAllWrongDownSourceEvent :
    MeasurableSet (generatedAllWrongDownSourceEvent rate rewards C_star C_h) := by
  unfold generatedAllWrongDownSourceEvent
  apply MeasurableSet.iUnion
  intro s
  exact MeasurableSet.subtype_image
    (ReferenceGeneratedDownAmbiguityMeasurability.measurableSet_generatedLaunchFiberSet
      (rate := rate) rewards C_star C_h s.val)
    (measurableSet_generatedAllWrongDownFibreEvent rate rewards C_star C_h s)

/-- The full generated source run is the complete physical suffix on the
same source value, rather than an independently supplied run or record. -/
theorem generatedSourceRun_records_eq_completeSuffixRecords
    (s : Fin p.T) (x : LaunchSource rate rewards C_star C_h s.val s.isLt) :
    (generatedSourceRun rate rewards C_star C_h s.val s.isLt x).records =
      ReferenceCompletePhysicalHistory.completeSuffixRecords rate x.val rewards C_star C_h := by
  let fiber := ReferenceGeneratedLiveLaterDownEvent.launchFiberOfSource
    (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) s x
  have hrecords :=
    ReferenceGeneratedDownAmbiguityMeasurability.generatedRun_records_eq_completeSuffixRecords_take
      (rate := rate) rewards C_star C_h s.val (p.T - s.val) (by omega) fiber
  have hinput :=
    ReferenceGeneratedLiveLaterDownEvent.generatedActiveRunInput_eq_generatedSourceRunInput
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) s x
  change ReferenceGeneratedDownAmbiguityMeasurability.generatedActiveRunInput
    (rate := rate) rewards C_star C_h s.val fiber = _ at hinput
  rw [hinput] at hrecords
  have hstart : ReferenceCompletePhysicalHistory.physicalStart
      rate x.val rewards C_star C_h = s.val := x.property.2
  have hlength := ReferenceCompletePhysicalHistory.completeSuffixRecords_length
    rate x.val rewards C_star C_h
  rw [hstart] at hlength
  change (generatedSourceRun rate rewards C_star C_h s.val s.isLt x).records =
    (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate x.val rewards C_star C_h).take (p.T - s.val) at hrecords
  rw [List.take_of_length_le hlength.le] at hrecords
  exact hrecords

/-- Every actual complete suffix record, and only such a record, has its
literal generated-source finite index. -/
theorem mem_completeSuffixRecords_iff_generatedSourceRecordAt
    (s : Fin p.T) (x : LaunchSource rate rewards C_star C_h s.val s.isLt)
    (record : ReferenceFollowerDownDecoderReplay.Record p rate) :
    record ∈ ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate x.val rewards C_star C_h ↔
      ∃ n : Fin (p.T - s.val),
        generatedSourceRecordAt rate rewards C_star C_h s.val s.isLt x n = record := by
  rw [← generatedSourceRun_records_eq_completeSuffixRecords rate rewards C_star C_h s x]
  change record ∈ (ReferenceActiveHorizonMeasurability.runOfInput
    s.val (p.T - s.val) (by omega)
    (generatedSourceRunInput rate rewards C_star C_h s.val s.isLt x)).records ↔ _
  rw [ReferenceDownCompletedAmbiguityMeasurability.run_records_eq_ofFn]
  exact List.mem_ofFn

/-- The event can be read directly from the original source's complete
physical suffix, with no artificial snapshot, trace or chosen execution. -/
theorem mem_generatedAllWrongDownSourceEvent_iff_completeSuffixRecords
    (source : SourceInput p) :
    source ∈ generatedAllWrongDownSourceEvent rate rewards C_star C_h ↔
      ∃ record ∈ ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h,
        ∃ i : Fin (p.m - 1), ∃ cut,
          (record.output.followers i).down = some cut ∧
            ReferenceDownReception.wrongUniqueAccepted cut := by
  constructor
  · intro hevent
    obtain ⟨s, x, hx, i, n, cut, hcut, hwrong⟩ :=
      (mem_generatedAllWrongDownSourceEvent_iff rate rewards C_star C_h source).mp hevent
    have hmem := (mem_completeSuffixRecords_iff_generatedSourceRecordAt
      rate rewards C_star C_h s x
      (generatedSourceRecordAt rate rewards C_star C_h s.val s.isLt x n)).mpr ⟨n, rfl⟩
    rw [hx] at hmem
    exact ⟨_, hmem, i, cut, hcut, hwrong⟩
  · rintro ⟨record, hmem, i, cut, hcut, hwrong⟩
    have hlength := ReferenceCompletePhysicalHistory.completeSuffixRecords_length
      rate source rewards C_star C_h
    have hpositive := List.length_pos_of_mem hmem
    have hstartLt : ReferenceCompletePhysicalHistory.physicalStart
        rate source rewards C_star C_h < p.T := by omega
    have hsome : (ReferenceCorrectedInitializationLaunch.correctedLaunch
        rate source rewards C_star C_h).isSome = true := by
      cases hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
          rate source rewards C_star C_h with
      | none =>
          have hempty := (ReferenceCompletePhysicalHistory.no_launch_complete_history
            rate source rewards C_star C_h hlaunch).2.1
          rw [hempty] at hmem
          cases hmem
      | some active => rfl
    let s : Fin p.T :=
      ⟨ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h, hstartLt⟩
    let x : LaunchSource rate rewards C_star C_h s.val s.isLt :=
      ⟨source, (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
        rate source rewards C_star C_h).mp hsome, rfl⟩
    obtain ⟨n, hn⟩ := (mem_completeSuffixRecords_iff_generatedSourceRecordAt
      rate rewards C_star C_h s x record).mp hmem
    apply (mem_generatedAllWrongDownSourceEvent_iff rate rewards C_star C_h source).mpr
    refine ⟨s, x, rfl, i, n, cut, ?_, hwrong⟩
    rw [hn]
    exact hcut

/-- Source exhaustion gives an empty physical suffix and no suffix DOWN
error; prelaunch ordinary suppression is a separate diagnostic. -/
theorem generatedAllWrongDownSourceEvent_false_of_no_launch (source : SourceInput p)
    (hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h = none) :
    source ∉ generatedAllWrongDownSourceEvent rate rewards C_star C_h ∧
      ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h = [] := by
  have hempty := (ReferenceCompletePhysicalHistory.no_launch_complete_history
    rate source rewards C_star C_h hlaunch).2.1
  refine ⟨?_, hempty⟩
  rw [mem_generatedAllWrongDownSourceEvent_iff_completeSuffixRecords]
  simp only [hempty, List.not_mem_nil, false_and, exists_false, not_false_eq_true]

/-- A terminal crossing retains its actual launch state but has no suffix
rounds on which an ordinary DOWN diagnostic could be emitted. -/
theorem generatedAllWrongDownSourceEvent_false_of_terminal_launch
    (source : SourceInput p) (active : ReferenceActivePhysicalStep.State p rate)
    (hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h = some active)
    (hterminal : ReferenceCompletePhysicalHistory.physicalStart
      rate source rewards C_star C_h = p.T) :
    source ∉ generatedAllWrongDownSourceEvent rate rewards C_star C_h ∧
      ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h = [] := by
  have hempty := (ReferenceCompletePhysicalHistory.terminal_crossing_complete_history
    rate source rewards C_star C_h active hlaunch hterminal).1
  refine ⟨?_, hempty⟩
  rw [mem_generatedAllWrongDownSourceEvent_iff_completeSuffixRecords]
  simp only [hempty, List.not_mem_nil, false_and, exists_false, not_false_eq_true]

/-- Completion is produced from the saved actual diagnostic, then joined to
its exact generated source observation. No dispatch premise is used. -/
theorem generatedRecord_wrongUnique_implies_completedBatchAtRound
    (s : Fin p.T) (x : LaunchSource rate rewards C_star C_h s.val s.isLt)
    (i : Fin (p.m - 1)) (n : Fin (p.T - s.val))
    (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (hcut : ((generatedSourceRecordAt rate rewards C_star C_h s.val s.isLt x n).output.followers i).down =
      some cut)
    (hwrong : ReferenceDownReception.wrongUniqueAccepted cut) :
    completedBatchAtRound rate
      ((generatedSourceObservation rate rewards C_star C_h s.val s.isLt i x).2 n) := by
  exact ReferenceGeneratedContinuingLiveDownErrorEvent.actualRecord_wrongUniqueAccepted_implies_completedBatchAtRound
    (p := p) (rate := rate)
    (generatedSourceRecordAt rate rewards C_star C_h s.val s.isLt x n) i cut hcut hwrong

/-- Both completion branches enter the same existing joint union. The later
branch keeps its actual greatest earlier completion and bank; the first
branch uses the inherited first-completion theorem. -/
theorem generatedAllWrongDownSourceEvent_subset_downCohortUnion
    (control0 : ContinuousLearningRows.TimeControl p) :
    generatedAllWrongDownSourceEvent rate rewards C_star C_h ⊆
      ReferenceGeneratedDownCohortFiniteUnion.downCohortUnionEvent
        rate rewards C_star C_h control0 (AffineBatchDecoder.quota p) := by
  classical
  intro source hsource
  rcases (mem_generatedAllWrongDownSourceEvent_iff rate rewards C_star C_h source).mp hsource with
    ⟨s, x, hx, i, n, cut, hcut, hwrong⟩
  have hcomplete := generatedRecord_wrongUnique_implies_completedBatchAtRound
    rate rewards C_star C_h s x i n cut hcut hwrong
  obtain ⟨word, hraw, hdetector⟩ :=
    ReferenceGeneratedWrongDownAllTestsNotSent.generated_wrong_down_later_completion_detector
      rate rewards C_star C_h s.val s.isLt x i n cut hcut hwrong control0 hcomplete
  dsimp only at hdetector
  rcases hdetector with hfirst | hlater
  · have hfirstEvent : source ∈
        ReferenceGeneratedInheritedDownFirstEventBound.inheritedFirstWrongEvent
          rate rewards C_star C_h := by
      refine ⟨s.val, s.isLt, x, i, n, hx, ⟨hcomplete, ?_⟩, cut, hcut, hwrong⟩
      intro l hl
      exact hfirst ⟨l, lt_trans hl n.isLt⟩ hl
    exact ReferenceGeneratedInheritedDownFirstEventBound.inheritedFirstWrongEvent_subset_downCohortUnion
      rate rewards C_star C_h control0 hfirstEvent
  · rcases hlater with ⟨m, hmn, hcompm, hgreatest, hnoMiddle, hunique,
      halpha, halphaN, hspanT, halphaT, hboundary,
      callCodeN, loggedN, cutN, testN, hcallN, hactualN, hloggedN, hcutN,
      hcomparisonN, hpositiveN, hquotaN, htestN,
      hlistA, hlistB, hlength, hcountBeforeN, hbank, hrawN, hchron,
      hprovenance, hhash, hnotSent, hgenerated, hunion⟩
    rw [← hx]
    exact hunion

/-- Monotonicity into the single joint envelope, without a second launch,
phase, first/later, or completion multiplicity. -/
theorem generatedAllWrongDownSourceEvent_measure_le_downCohortUnion
    (control0 : ContinuousLearningRows.TimeControl p) :
    BootstrapPrivateRoundStreams.sourceInputLaw p
        (generatedAllWrongDownSourceEvent rate rewards C_star C_h) ≤
      BootstrapPrivateRoundStreams.sourceInputLaw p
        (ReferenceGeneratedDownCohortFiniteUnion.downCohortUnionEvent
          rate rewards C_star C_h control0 (AffineBatchDecoder.quota p)) :=
  measure_mono (generatedAllWrongDownSourceEvent_subset_downCohortUnion
    rate rewards C_star C_h control0)

/-- The original-source ENNReal geometric envelope at the decoder quota. -/
theorem generatedAllWrongDownSourceEvent_measure_le_geometric
    (control0 : ContinuousLearningRows.TimeControl p) :
    BootstrapPrivateRoundStreams.sourceInputLaw p
        (generatedAllWrongDownSourceEvent rate rewards C_star C_h) ≤
      (((p.m - 1 : ℕ) : ENNReal) * (p.T : ENNReal) *
        (2 : ENNReal) ^ AffineBatchDecoder.width p) *
        ((1 : ENNReal) / 2) ^ AffineBatchDecoder.quota p := by
  exact (generatedAllWrongDownSourceEvent_measure_le_downCohortUnion
    rate rewards C_star C_h control0).trans
      (ReferenceGeneratedDownCohortFiniteUnion.downCohortUnionEvent_measure_le_geometric
        rate rewards C_star C_h control0 (AffineBatchDecoder.quota p) le_rfl)

/-- The real original-source quota bound for every actual suffix phase. -/
theorem generatedAllWrongDownSourceEvent_measureReal_quota_bound
    (control0 : ContinuousLearningRows.TimeControl p) :
    (BootstrapPrivateRoundStreams.sourceInputLaw p).real
        (generatedAllWrongDownSourceEvent rate rewards C_star C_h) ≤
      1 / (4 * (ConstructorDimensions.N p : ℝ) ^ 2) := by
  calc
    (BootstrapPrivateRoundStreams.sourceInputLaw p).real
        (generatedAllWrongDownSourceEvent rate rewards C_star C_h) ≤
      (BootstrapPrivateRoundStreams.sourceInputLaw p).real
        (ReferenceGeneratedDownCohortFiniteUnion.downCohortUnionEvent
          rate rewards C_star C_h control0 (AffineBatchDecoder.quota p)) :=
      measureReal_mono (generatedAllWrongDownSourceEvent_subset_downCohortUnion
        rate rewards C_star C_h control0) (by finiteness)
    _ ≤ 1 / (4 * (ConstructorDimensions.N p : ℝ) ^ 2) :=
      ReferenceGeneratedDownCohortFiniteUnion.downCohortUnionEvent_measureReal_quota_bound
        rate rewards C_star C_h control0

/-- The complete-source decoder consumer may use its literal record event
instead of unfolding the finite launch-fibre image presentation. -/
theorem generatedAllWrongDownSourceEvent_eq_completeSuffixEvent :
    generatedAllWrongDownSourceEvent rate rewards C_star C_h =
      {source : SourceInput p |
        ∃ record ∈ ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate source rewards C_star C_h,
          ∃ i : Fin (p.m - 1), ∃ cut,
            (record.output.followers i).down = some cut ∧
              ReferenceDownReception.wrongUniqueAccepted cut} := by
  ext source
  exact mem_generatedAllWrongDownSourceEvent_iff_completeSuffixRecords
    rate rewards C_star C_h source

/-- Ambient Borelness of the complete-source decoder's literal all-phase
wrong-DOWN event, obtained through its exact physical suffix identity. -/
theorem measurableSet_completeSuffixWrongDownEvent :
    MeasurableSet {source : SourceInput p |
      ∃ record ∈ ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h,
        ∃ i : Fin (p.m - 1), ∃ cut,
          (record.output.followers i).down = some cut ∧
            ReferenceDownReception.wrongUniqueAccepted cut} := by
  rw [← generatedAllWrongDownSourceEvent_eq_completeSuffixEvent]
  exact measurableSet_generatedAllWrongDownSourceEvent rate rewards C_star C_h

/-- The original complete-source decoder wrong-DOWN envelope has the quota
bound, with no supplied completed-batch, law or measurability premise. -/
theorem completeSuffixWrongDownEvent_measureReal_quota_bound
    (control0 : ContinuousLearningRows.TimeControl p) :
    (BootstrapPrivateRoundStreams.sourceInputLaw p).real
      {source : SourceInput p |
        ∃ record ∈ ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate source rewards C_star C_h,
          ∃ i : Fin (p.m - 1), ∃ cut,
            (record.output.followers i).down = some cut ∧
              ReferenceDownReception.wrongUniqueAccepted cut} ≤
      1 / (4 * (ConstructorDimensions.N p : ℝ) ^ 2) := by
  rw [← generatedAllWrongDownSourceEvent_eq_completeSuffixEvent]
  exact generatedAllWrongDownSourceEvent_measureReal_quota_bound
    rate rewards C_star C_h control0

/-- The previously constructed selected continuing-LIVE event is a subevent
of the actual all-phase event on precisely the same original source. -/
theorem generatedContinuingLiveWrongDownSourceEvent_subset_allWrongDown :
    ReferenceGeneratedContinuingLiveDownErrorEvent.generatedContinuingLiveWrongDownSourceEvent
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) ⊆
      generatedAllWrongDownSourceEvent rate rewards C_star C_h := by
  intro source hsource
  obtain ⟨s, x, hx, hfibre⟩ :=
    (ReferenceGeneratedContinuingLiveDownErrorEvent.mem_generatedContinuingLiveWrongDownSourceEvent_iff
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) source).mp hsource
  obtain ⟨i, n, _hselected, cut, hcut, hwrong⟩ :=
    (ReferenceGeneratedContinuingLiveDownErrorEvent.mem_generatedContinuingLiveWrongDownFibreEvent_iff
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) s x).mp hfibre
  exact (mem_generatedAllWrongDownSourceEvent_iff rate rewards C_star C_h source).mpr
    ⟨s, x, hx, i, n, cut, hcut, hwrong⟩

end Bandits.Support.ReferenceGeneratedAllWrongDownEvent

end
