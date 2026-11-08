/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedLiveLaterCompletionContainment

import Mathlib.MeasureTheory.Measure.Real
import Lean.Elab.Tactic.Omega

/-!
# Borel actual continuing-LIVE later wrong-DOWN event

Sources: `sources/zip4/manuscript/appendix_a_local_protocol.tex:92-109,111-157`,
`sources/zip4/manuscript/05_binary_transport.tex:20-42,60-124`,
`sources/zip4/manuscript/06_interruptions.tex:246-295,327-348`,
`sources/zip4/manuscript/07_public_setup.tex:127-164`, and
`sources/zip4/manuscript/08_main_theorem.tex:29-42`.

This module defines the actual selected continuing-LIVE later-completion
wrong-ordinary-acceptance subevent on the original source input. It proves its
canonical-code Borel measurability and consumes the admitted containment and
joint cohort quota estimate. It covers no other error-event stratum and makes
no main-regret closure claim.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions

namespace Bandits.Support.ReferenceGeneratedLiveLaterDownEvent

variable {p : ConstructorDimensions.Parameters}

abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput

variable
  (rate : RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ)

open ReferenceGeneratedDownBatchCalendar
open ReferenceDownCompletedAmbiguityMeasurability

def launchFiberOfSource
    (s : Fin p.T)
    (x : ReferenceGeneratedDownBatchCalendar.LaunchSource
      rate rewards C_star C_h s.val s.isLt) :
    ReferenceGeneratedDownAmbiguityMeasurability.GeneratedLaunchFiber
      (rate := rate) rewards C_star C_h s.val :=
  ⟨x.1, by
    change _ ∧ _
    exact x.2⟩

/-- The corrected canonical active input and the generated-source input used
by the accepted completion containment are literally equal. The seed equality
comes from the same corrected launch option and its actual launch payload. -/
theorem generatedActiveRunInput_eq_generatedSourceRunInput
    (s : Fin p.T)
    (x : ReferenceGeneratedDownBatchCalendar.LaunchSource
      rate rewards C_star C_h s.val s.isLt) :
    ReferenceGeneratedDownAmbiguityMeasurability.generatedActiveRunInput
        (rate := rate) rewards C_star C_h s.val (launchFiberOfSource
          (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) s x) =
      ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput
        rate rewards C_star C_h s.val s.isLt x := by
  let fiber := launchFiberOfSource (rate := rate) (rewards := rewards)
    (C_star := C_star) (C_h := C_h) s x
  have hseed := ReferenceGeneratedDownBatchCalendar.generatedSourceSeed_spec
    rate rewards C_star C_h s.val s.isLt x
  have hlaunch := ReferenceCompletePhysicalHistory.correctedLaunch_eq_some_payload
    rate x.1 rewards C_star C_h
      (ReferenceGeneratedDownAmbiguityMeasurability.generatedLaunch_ne_none
        (rate := rate) rewards C_star C_h s.val fiber)
  have hpayload :
      ReferenceCompletePhysicalHistory.correctedLaunchPayload rate x.1 rewards
        C_star C_h
        (ReferenceGeneratedDownAmbiguityMeasurability.generatedLaunch_ne_none
          (rate := rate) rewards C_star C_h s.val fiber) =
        ReferenceGeneratedDownBatchCalendar.generatedSourceSeed
          rate rewards C_star C_h s.val s.isLt x :=
    Option.some.inj (hlaunch.symm.trans hseed.1)
  apply Subtype.ext
  rw [ReferenceGeneratedDownAmbiguityMeasurability.generatedActiveRunInput_val,
    ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput]
  change (ReferenceCompletePhysicalHistory.correctedLaunchPayload rate x.1 rewards
      C_star C_h
        (ReferenceGeneratedDownAmbiguityMeasurability.generatedLaunch_ne_none
          (rate := rate) rewards C_star C_h s.val fiber),
      (x.1.1.2, (ActualInitializationPhysicalStep.selectedRowIndex p x.1, rewards))) =
    (ReferenceGeneratedDownBatchCalendar.generatedSourceSeed
      rate rewards C_star C_h s.val s.isLt x,
      (x.1.1.2, (ActualInitializationPhysicalStep.selectedRowIndex p x.1, rewards)))
  rw [hpayload]

/-- The intentional actual constructor test. Failed, cutoff, collection,
first, and dagger constructors do not satisfy it. -/
def selectedContinuingCoordinator
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (coordinator : ReferenceActivePhysicalStep.DispatchCut x) : Bool :=
  match coordinator with
  | .live _ _ _ (.continuingChosen _ _ _ _) => true
  | _ => false

private abbrev LiveInput :=
  ReferenceFirstLiveCoordinatorStepMeasurability.LiveInput p rate

private abbrev LiveOutcomeData :=
  ReferenceLiveDispatchOutputMeasurability.OutcomeData p

private def outcomeIsContinuing : LiveOutcomeData (p := p) → Bool
  | .continuingChosen _ _ _ => true
  | _ => false

/-- The actual dispatch constructor is precisely the tag retained by the
canonical live dispatch observation. The observation keeps the original live
payload, real row, and the other continuous coordinates on their Borel spaces. -/
private def selectedContinuingLiveDispatchSet :
    Set (ReferenceActivePhysicalStep.RoundInput p rate) :=
  (Subtype.val : LiveInput (p := p) (rate := rate) →
      ReferenceActivePhysicalStep.RoundInput p rate) ''
    {x | outcomeIsContinuing (p := p)
      ((ReferenceLiveDispatchOutputMeasurability.dispatchObservation
        (ReferenceFirstLiveCoordinatorStepMeasurability.liveCoordinates x)).2) = true}

private theorem measurableSet_selectedContinuingLiveDispatchSet :
    MeasurableSet (selectedContinuingLiveDispatchSet (p := p) (rate := rate)) := by
  classical
  apply MeasurableSet.subtype_image
  · exact ReferenceFirstLiveCoordinatorStepMeasurability.measurableSet_liveSet
  · have htag : Measurable (fun code : ReferenceLiveDispatchOutputMeasurability.OutcomeData p =>
        outcomeIsContinuing (p := p) code) := Measurable.of_discrete
    have hcode : Measurable (fun x : LiveInput (p := p) (rate := rate) =>
        outcomeIsContinuing (p := p)
          ((ReferenceLiveDispatchOutputMeasurability.dispatchObservation
            (ReferenceFirstLiveCoordinatorStepMeasurability.liveCoordinates x)).2)) :=
      (htag.comp measurable_snd).comp
        ReferenceFirstLiveCoordinatorStepMeasurability.measurable_liveDispatchObservation
    exact hcode (measurableSet_singleton true)

private theorem liveDispatchObservation_code_flag
    (x : LiveInput (p := p) (rate := rate)) :
    outcomeIsContinuing (p := p)
        ((ReferenceLiveDispatchOutputMeasurability.dispatchObservation
          (ReferenceFirstLiveCoordinatorStepMeasurability.liveCoordinates x)).2) =
      selectedContinuingCoordinator (p := p) (rate := rate)
        (ReferenceActivePhysicalStep.dispatch x.1) := by
  let actualInput := ReferenceActivePhysicalStep.liveInput x.1
    (ReferenceFirstLiveCoordinatorStepMeasurability.liveRegisters x)
    (ReferenceFirstLiveCoordinatorStepMeasurability.liveOwned x)
    (ReferenceFirstLiveCoordinatorStepMeasurability.liveBase x)
  let actualOutcome := CoordinatorRoundDispatch.dispatchLive actualInput
  have hcode := ReferenceLiveDispatchOutputMeasurability.outcomeData_originalInput
    x.1 (ReferenceFirstLiveCoordinatorStepMeasurability.liveRegisters x)
    (ReferenceFirstLiveCoordinatorStepMeasurability.liveOwned x)
    (ReferenceFirstLiveCoordinatorStepMeasurability.liveBase x)
  calc
    outcomeIsContinuing (p := p)
        ((ReferenceLiveDispatchOutputMeasurability.dispatchObservation
          (ReferenceFirstLiveCoordinatorStepMeasurability.liveCoordinates x)).2) =
      outcomeIsContinuing (p := p)
        (ReferenceLiveDispatchOutputMeasurability.outcomeData actualOutcome) := by
          exact congrArg (outcomeIsContinuing (p := p)) hcode
    _ = selectedContinuingCoordinator (p := p) (rate := rate)
        (ReferenceActivePhysicalStep.dispatch x.1) := by
          rw [ReferenceFirstLiveCoordinatorStepMeasurability.live_dispatch_eq x]
          cases hOut : CoordinatorRoundDispatch.dispatchLive actualInput <;>
            simp [actualOutcome, hOut, outcomeIsContinuing,
              ReferenceLiveDispatchOutputMeasurability.outcomeData,
              selectedContinuingCoordinator]

private theorem live_dispatch_code_is_continuing_iff
    (input : ReferenceActivePhysicalStep.RoundInput p rate) :
    input ∈ selectedContinuingLiveDispatchSet (p := p) (rate := rate) ↔
      selectedContinuingCoordinator (p := p) (rate := rate)
        (ReferenceActivePhysicalStep.dispatch input) = true := by
  classical
  cases hstate : input.state.coordinator with
  | first =>
      have hnot : input ∉
          ReferenceFirstLiveCoordinatorStepMeasurability.liveSet (p := p) (rate := rate) := by
        simp [ReferenceFirstLiveCoordinatorStepMeasurability.liveSet,
          ReferenceActivePhysicalStepMeasurability.encodeState,
          ReferenceActivePhysicalStepMeasurability.encodeCoordinator, hstate]
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact False.elim (hnot x.property)
      · intro htag
        rw [ReferenceActivePhysicalStep.dispatch_first input hstate] at htag
        simp [selectedContinuingCoordinator] at htag
  | dagger =>
      have hnot : input ∉
          ReferenceFirstLiveCoordinatorStepMeasurability.liveSet (p := p) (rate := rate) := by
        simp [ReferenceFirstLiveCoordinatorStepMeasurability.liveSet,
          ReferenceActivePhysicalStepMeasurability.encodeState,
          ReferenceActivePhysicalStepMeasurability.encodeCoordinator, hstate]
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact False.elim (hnot x.property)
      · intro htag
        rw [ReferenceActivePhysicalStep.dispatch_dagger input hstate] at htag
        simp [selectedContinuingCoordinator] at htag
  | collection payload ledger proposal =>
      have hnot : input ∉
          ReferenceFirstLiveCoordinatorStepMeasurability.liveSet (p := p) (rate := rate) := by
        simp [ReferenceFirstLiveCoordinatorStepMeasurability.liveSet,
          ReferenceActivePhysicalStepMeasurability.encodeState,
          ReferenceActivePhysicalStepMeasurability.encodeCoordinator, hstate]
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact False.elim (hnot x.property)
      · intro htag
        by_cases hcut : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
        · rw [ReferenceCollectionDispatchMeasurability.dispatch_collection
            input payload ledger proposal hstate hcut] at htag
          simp [selectedContinuingCoordinator] at htag
        · rw [(ReferenceActivePhysicalStep.dispatch_collection_invalid_cutoff
            input payload ledger proposal hstate hcut).1] at htag
          simp [selectedContinuingCoordinator] at htag
  | live registers owned base =>
      let liveInput : LiveInput (p := p) (rate := rate) :=
        ⟨input, by
          unfold ReferenceFirstLiveCoordinatorStepMeasurability.liveSet
          refine ⟨(registers.payload,
            ReferenceActivePhysicalStepMeasurability.encodeLive registers owned base), ?_⟩
          simp [ReferenceActivePhysicalStepMeasurability.encodeState,
            ReferenceActivePhysicalStepMeasurability.encodeCoordinator, hstate]⟩
      have hcode := liveDispatchObservation_code_flag (p := p) (rate := rate) liveInput
      constructor
      · rintro ⟨x, hx, hxval⟩
        have hxEq : x = liveInput := by
          apply Subtype.ext
          simpa [liveInput] using hxval
        subst x
        change liveInput ∈ {x : LiveInput (p := p) (rate := rate) |
          outcomeIsContinuing (p := p)
            ((ReferenceLiveDispatchOutputMeasurability.dispatchObservation
              (ReferenceFirstLiveCoordinatorStepMeasurability.liveCoordinates x)).2) = true} at hx
        simp only [Set.mem_setOf_eq] at hx
        change outcomeIsContinuing (p := p)
          ((ReferenceLiveDispatchOutputMeasurability.dispatchObservation
            (ReferenceFirstLiveCoordinatorStepMeasurability.liveCoordinates liveInput)).2) = true at hx
        rw [hcode] at hx
        exact hx
      · intro htag
        have hx : outcomeIsContinuing (p := p)
            ((ReferenceLiveDispatchOutputMeasurability.dispatchObservation
              (ReferenceFirstLiveCoordinatorStepMeasurability.liveCoordinates liveInput)).2) = true := by
          rw [hcode]
          exact htag
        exact ⟨liveInput, hx, rfl⟩

/-- The actual wrong-acceptance predicate on the retained discrete cut fields.
It is exactly comparison=false, a present raw word, and ordinary acceptance. -/
private def wrongUniqueCutFields
    (fields : ReferenceDownCompletedAmbiguityMeasurability.DownCutFields p) : Bool :=
  decide (fields.1 ≠ none ∧ fields.2.2.1 = some false ∧ fields.2.2.2 = true)

/-- Option-isSome followed by the actual cut predicate. The cut witness is
discrete code; this does not range over a continuous carrier. -/
private def wrongUniqueDiagnostic
    (diagnostic : ReferenceDownCompletedAmbiguityMeasurability.DownDiagnosticCode p rate) : Bool :=
  match diagnostic.2.2 with
  | none => false
  | some fields => wrongUniqueCutFields fields

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
    (downCallOptionMeasurableSpace (p := p) :
      MeasurableSpace (Option (ReferenceDownCompletedAmbiguityMeasurability.DownCallCode p))) =
      (LaterAssignmentStartMeasurability.optionMeasurableSpace :
        MeasurableSpace (Option (ReferenceDownCompletedAmbiguityMeasurability.DownCallCode p))) := by
  delta downCallOptionMeasurableSpace
  rfl

private theorem downFailureOptionMeasurableSpace_eq :
    downFailureOptionMeasurableSpace =
      LaterAssignmentStartMeasurability.optionMeasurableSpace := by
  delta downFailureOptionMeasurableSpace
  rfl

private theorem downCutFieldsOptionMeasurableSpace_eq :
    (downCutFieldsOptionMeasurableSpace (p := p) :
      MeasurableSpace (Option (ReferenceDownCompletedAmbiguityMeasurability.DownCutFields p))) =
      (LaterAssignmentStartMeasurability.optionMeasurableSpace :
        MeasurableSpace (Option (ReferenceDownCompletedAmbiguityMeasurability.DownCutFields p))) := by
  delta downCutFieldsOptionMeasurableSpace
  rfl

private theorem downBoolOptionMeasurableSpace_eq :
    downBoolOptionMeasurableSpace =
      LaterAssignmentStartMeasurability.optionMeasurableSpace := by
  delta downBoolOptionMeasurableSpace
  rfl

local instance downFollowerStateCodeMeasurableSingleton : MeasurableSingletonClass
    (FollowerDownMeasurability.FollowerStateCode p rate) := ⟨fun _ => trivial⟩

local instance downFollowerStateOptionMeasurableSingleton : MeasurableSingletonClass
    (Option (FollowerDownMeasurability.FollowerStateCode p rate)) := ⟨fun _ => trivial⟩

private theorem measurableSet_laterOptionSingleton {α : Type*}
    [MeasurableSpace α] [MeasurableSingletonClass α] (a : Option α) :
    MeasurableSet[LaterAssignmentStartMeasurability.optionMeasurableSpace] {a} := by
  let e := Equiv.optionEquivSumPUnit α
  have he : @Measurable (Option α) (α ⊕ PUnit)
      LaterAssignmentStartMeasurability.optionMeasurableSpace inferInstance e := comap_measurable _
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


/-- The literal physical fibre event: selected continuing constructor,
current completion, an actual earlier completion for the same follower, and
the actual wrong uniquely accepted DOWN cut. -/
def generatedLiveLaterWrongDownFibreEvent
    (s : Fin p.T) :
    Set (ReferenceGeneratedDownBatchCalendar.LaunchSource
      rate rewards C_star C_h s.val s.isLt) :=
  {x | ∃ i : Fin (p.m - 1), ∃ n : Fin (p.T - s.val),
    selectedContinuingCoordinator (p := p) (rate := rate)
      (ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
        rate rewards C_star C_h s.val s.isLt x n).output.preparation.coordinator = true ∧
    ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate
      ((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
        rate rewards C_star C_h s.val s.isLt i x).2 n) ∧
    (∃ m : Fin (p.T - s.val), m.val < n.val ∧
      ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate
        ((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
          rate rewards C_star C_h s.val s.isLt i x).2 m)) ∧
    ∃ cut,
      ((ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
        rate rewards C_star C_h s.val s.isLt x n).output.followers i).down = some cut ∧
      ReferenceDownReception.wrongUniqueAccepted cut}

/-- The same fibre event read through the actual canonical run and dispatch
codes. This presentation exposes only finite-index tests and discrete code
fields; the run input and continuous rows retain their original Borel spaces. -/
private def generatedLiveLaterWrongDownCodeFibreEvent
    (s : Fin p.T) :
    Set (ReferenceGeneratedDownBatchCalendar.LaunchSource
      rate rewards C_star C_h s.val s.isLt) :=
  ⋃ i : Fin (p.m - 1), ⋃ n : Fin (p.T - s.val),
    {x |
    selectedContinuingLiveDispatchSet (p := p) (rate := rate)
      (ReferenceDownCompletedAmbiguityMeasurability.prefixInput
        s.val n.val (by omega)
        (ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput
          rate rewards C_star C_h s.val s.isLt x)) ∧
    ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate
      ((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
        rate rewards C_star C_h s.val s.isLt i x).2 n) ∧
    (∃ m : Fin (p.T - s.val), m.val < n.val ∧
      ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate
        ((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
          rate rewards C_star C_h s.val s.isLt i x).2 m)) ∧
    wrongUniqueDiagnostic (p := p) (rate := rate)
        (((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
        rate rewards C_star C_h s.val s.isLt i x).2 n).2.2.2) = true}

/-- Union the genuine crossing fibres as images in the original source input
space. No source arrays, rows, or J coordinate are resampled or discarded. -/
def generatedLiveLaterWrongDownSourceEvent : Set (SourceInput p) :=
  ⋃ s : Fin p.T,
    (Subtype.val : ReferenceGeneratedDownBatchCalendar.LaunchSource
      rate rewards C_star C_h s.val s.isLt → SourceInput p) ''
      generatedLiveLaterWrongDownFibreEvent
        (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) s
private theorem wrongUniqueCut_at_record_iff
    (record : ReferenceFollowerDownDecoderReplay.Record p rate)
    (i : Fin (p.m - 1)) :
    (∃ cut, (record.output.followers i).down = some cut ∧
        ReferenceDownReception.wrongUniqueAccepted cut) ↔
      wrongUniqueDiagnostic (p := p) (rate := rate)
        (ReferenceDownCompletedAmbiguityMeasurability.diagnosticProjection
          ((ReferenceActiveStepCompositionMeasurability.wholeStepCode
            record.input).2.1 i)) = true := by
  let output := (ReferenceActiveStepCompositionMeasurability.wholeStepCode
    record.input).2.1 i
  have hrec : ReferenceFollowerTailComposition.reconstructFollowerObservable output =
      record.output.followers i := by
    have hwhole := (ReferenceActiveStepCompositionMeasurability.wholeStepCode_reconstructs
      record.input).2.1 i
    simpa [output, ReferenceActivePhysicalStep.step, record.output_eq] using hwhole
  rw [← hrec]
  change (∃ cut,
      (ReferenceFollowerTailComposition.reconstructFollowerObservable output).down =
        some cut ∧ ReferenceDownReception.wrongUniqueAccepted cut) ↔
    wrongUniqueDiagnostic (p := p) (rate := rate)
      (ReferenceDownCompletedAmbiguityMeasurability.diagnosticProjection output) = true
  rcases output with ⟨incoming, failure, downInput, cutCode⟩
  cases downInput with
  | inl absent =>
      simp [ReferenceFollowerTailComposition.reconstructFollowerObservable,
        ReferenceFollowerTailComposition.reconstructDown,
        ReferenceDownCompletedAmbiguityMeasurability.diagnosticProjection,
        wrongUniqueDiagnostic]
  | inr carry =>
      cases cutCode with
      | none =>
          simp [ReferenceFollowerTailComposition.reconstructFollowerObservable,
            ReferenceFollowerTailComposition.reconstructDown,
            ReferenceDownCompletedAmbiguityMeasurability.diagnosticProjection,
            wrongUniqueDiagnostic]
      | some code =>
          simp [ReferenceFollowerTailComposition.reconstructFollowerObservable,
            ReferenceFollowerTailComposition.reconstructDown,
            ReferenceDownCompletedAmbiguityMeasurability.diagnosticProjection,
            ReferenceDownCompletedAmbiguityMeasurability.cutCodeFields,
            ReferenceDownReceptionMeasurability.reconstructReferenceDownCutCode,
            ReferenceDownReception.wrongUniqueAccepted, wrongUniqueDiagnostic,
            wrongUniqueCutFields]
          constructor
          · rintro ⟨hcomparison, hraw, hacceptance⟩
            exact ⟨hraw, hcomparison, hacceptance⟩
          · rintro ⟨hraw, hcomparison, hacceptance⟩
            exact ⟨hcomparison, hraw, hacceptance⟩

/-- The selected-constructor code and cut code are read from the same actual
record that appears in the literal fibre event. -/
private theorem generatedRecord_code_tests_iff
    (s : Fin p.T)
    (x : ReferenceGeneratedDownBatchCalendar.LaunchSource
      rate rewards C_star C_h s.val s.isLt)
    (i : Fin (p.m - 1)) (n : Fin (p.T - s.val)) :
    (selectedContinuingCoordinator (p := p) (rate := rate)
        (ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
          rate rewards C_star C_h s.val s.isLt x n).output.preparation.coordinator = true ∧
      ∃ cut,
        ((ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
          rate rewards C_star C_h s.val s.isLt x n).output.followers i).down = some cut ∧
        ReferenceDownReception.wrongUniqueAccepted cut) ↔
      (selectedContinuingLiveDispatchSet (p := p) (rate := rate)
          (ReferenceDownCompletedAmbiguityMeasurability.prefixInput
            s.val n.val (by omega)
            (ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput
              rate rewards C_star C_h s.val s.isLt x)) ∧
        wrongUniqueDiagnostic (p := p) (rate := rate)
          (((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
            rate rewards C_star C_h s.val s.isLt i x).2 n).2.2.2) = true) := by
  let record := ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
    rate rewards C_star C_h s.val s.isLt x n
  have hselection : selectedContinuingCoordinator (p := p) (rate := rate)
      record.output.preparation.coordinator = true ↔
      record.input ∈ selectedContinuingLiveDispatchSet (p := p) (rate := rate) := by
    have hprep : record.output.preparation.coordinator =
        ReferenceActivePhysicalStep.dispatch record.input := by
      rfl
    rw [hprep]
    exact (live_dispatch_code_is_continuing_iff (p := p) (rate := rate) record.input).symm
  have hwrong := wrongUniqueCut_at_record_iff (p := p) (rate := rate) record i
  constructor
  · rintro ⟨hselected, cut, hcut, hwrongCut⟩
    refine ⟨?_, ?_⟩
    · apply hselection.mp hselected
    · have hdiag :
          ((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
            rate rewards C_star C_h s.val s.isLt i x).2 n).2.2.2 =
            ReferenceDownCompletedAmbiguityMeasurability.diagnosticProjection
              ((ReferenceActiveStepCompositionMeasurability.wholeStepCode
                record.input).2.1 i) := rfl
      rw [hdiag]
      exact hwrong.mp ⟨cut, hcut, hwrongCut⟩
  · rintro ⟨hselected, hwrongCut⟩
    refine ⟨hselection.mpr hselected, ?_⟩
    have hdiag :
        ((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
          rate rewards C_star C_h s.val s.isLt i x).2 n).2.2.2 =
          ReferenceDownCompletedAmbiguityMeasurability.diagnosticProjection
            ((ReferenceActiveStepCompositionMeasurability.wholeStepCode
              record.input).2.1 i) := rfl
    rw [hdiag] at hwrongCut
    exact hwrong.mpr hwrongCut

/-- The original event has exactly the pointwise membership specified by its
literal launch-fibre image. -/
theorem mem_generatedLiveLaterWrongDownFibreEvent_iff
    (s : Fin p.T)
    (x : ReferenceGeneratedDownBatchCalendar.LaunchSource
      rate rewards C_star C_h s.val s.isLt) :
    x ∈ generatedLiveLaterWrongDownFibreEvent
        (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) s ↔
      ∃ i : Fin (p.m - 1), ∃ n : Fin (p.T - s.val),
        selectedContinuingCoordinator (p := p) (rate := rate)
          (ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
            rate rewards C_star C_h s.val s.isLt x n).output.preparation.coordinator = true ∧
        ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate
          ((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
            rate rewards C_star C_h s.val s.isLt i x).2 n) ∧
        (∃ m : Fin (p.T - s.val), m.val < n.val ∧
          ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate
            ((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
              rate rewards C_star C_h s.val s.isLt i x).2 m)) ∧
        ∃ cut,
          ((ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
            rate rewards C_star C_h s.val s.isLt x n).output.followers i).down = some cut ∧
          ReferenceDownReception.wrongUniqueAccepted cut := by
  rfl

/-- Membership in the original event retains its actual crossing index and
the exact source point in that genuine launch fibre. -/
theorem mem_generatedLiveLaterWrongDownSourceEvent_iff
    (source : SourceInput p) :
    source ∈ generatedLiveLaterWrongDownSourceEvent
        (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) ↔
      ∃ s : Fin p.T, ∃ x : ReferenceGeneratedDownBatchCalendar.LaunchSource
        rate rewards C_star C_h s.val s.isLt,
        x.1 = source ∧
          x ∈ generatedLiveLaterWrongDownFibreEvent
            (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) s := by
  simp [generatedLiveLaterWrongDownSourceEvent]

private theorem measurableSet_generatedLiveLaterWrongDownCodeFibreEvent
    (s : Fin p.T) :
    MeasurableSet (generatedLiveLaterWrongDownCodeFibreEvent
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) s) := by
  classical
  unfold generatedLiveLaterWrongDownCodeFibreEvent
  apply MeasurableSet.iUnion
  intro i
  apply MeasurableSet.iUnion
  intro n
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
        (launchFiberOfSource (rate := rate) (rewards := rewards)
          (C_star := C_star) (C_h := C_h) s x)) := by
    have hmap : Measurable (fun x : ReferenceGeneratedDownBatchCalendar.LaunchSource
        rate rewards C_star C_h s.val s.isLt =>
        launchFiberOfSource (rate := rate) (rewards := rewards)
          (C_star := C_star) (C_h := C_h) s x) := by
      have hmap' : Measurable (fun x : ReferenceGeneratedDownBatchCalendar.LaunchSource
          rate rewards C_star C_h s.val s.isLt =>
          (⟨x.1, (launchFiberOfSource (rate := rate) (rewards := rewards)
            (C_star := C_star) (C_h := C_h) s x).property⟩ :
            ReferenceGeneratedDownAmbiguityMeasurability.GeneratedLaunchFiber
              (rate := rate) rewards C_star C_h s.val)) :=
        measurable_subtype_coe.subtype_mk
          (h := fun x => (launchFiberOfSource (rate := rate) (rewards := rewards)
            (C_star := C_star) (C_h := C_h) s x).property)
      have heq : (fun x : ReferenceGeneratedDownBatchCalendar.LaunchSource
          rate rewards C_star C_h s.val s.isLt =>
          (⟨x.1, (launchFiberOfSource (rate := rate) (rewards := rewards)
            (C_star := C_star) (C_h := C_h) s x).property⟩ :
            ReferenceGeneratedDownAmbiguityMeasurability.GeneratedLaunchFiber
              (rate := rate) rewards C_star C_h s.val)) =
        (fun x => launchFiberOfSource (rate := rate) (rewards := rewards)
          (C_star := C_star) (C_h := C_h) s x) := by
        funext x
        apply Subtype.ext
        rfl
      rw [← heq]
      exact hmap'
    exact (ReferenceGeneratedDownAmbiguityMeasurability.measurable_generatedActiveRunInput
        (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) s.val).comp
        hmap
  have hinput : Measurable input := by
    have heq : input = fun x =>
        ReferenceGeneratedDownAmbiguityMeasurability.generatedActiveRunInput
          (rate := rate) rewards C_star C_h s.val
          (launchFiberOfSource (rate := rate) (rewards := rewards)
            (C_star := C_star) (C_h := C_h) s x) := by
      funext x
      exact (generatedActiveRunInput_eq_generatedSourceRunInput
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
  have hcomplete (k : Fin (p.T - s.val)) :
      Measurable (fun x : ReferenceGeneratedDownBatchCalendar.LaunchSource
        rate rewards C_star C_h s.val s.isLt =>
        decide (ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate
          ((observation x).2 k))) := by
    exact (measurable_of_countable (fun r :
        ReferenceDownCompletedAmbiguityMeasurability.DownRoundCode p rate =>
          decide (ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate r))).comp
      (hround k)
  have hdiagnosticProjection : Measurable
      (fun r : ReferenceDownCompletedAmbiguityMeasurability.DownRoundCode p rate =>
        r.2.2.2) :=
    measurable_snd.comp (measurable_snd.comp measurable_snd)
  have hwrong : Measurable (fun x : ReferenceGeneratedDownBatchCalendar.LaunchSource
      rate rewards C_star C_h s.val s.isLt =>
      wrongUniqueDiagnostic (p := p) (rate := rate) (((observation x).2 n).2.2.2)) := by
    exact (measurable_of_countable (fun d :
      ReferenceDownCompletedAmbiguityMeasurability.DownDiagnosticCode p rate =>
        wrongUniqueDiagnostic (p := p) (rate := rate) d)).comp
      (hdiagnosticProjection.comp (hround n))
  have hprefix : Measurable (fun x : ReferenceGeneratedDownBatchCalendar.LaunchSource
      rate rewards C_star C_h s.val s.isLt =>
      ReferenceDownCompletedAmbiguityMeasurability.prefixInput
        s.val n.val (by omega) (input x)) :=
    (ReferenceDownCompletedAmbiguityMeasurability.measurable_prefixInput
      s.val n.val (by omega)).comp hinput
  have hselected : MeasurableSet {x : ReferenceGeneratedDownBatchCalendar.LaunchSource
      rate rewards C_star C_h s.val s.isLt |
      ReferenceDownCompletedAmbiguityMeasurability.prefixInput
        s.val n.val (by omega) (input x) ∈
        selectedContinuingLiveDispatchSet (p := p) (rate := rate)} :=
    (measurableSet_selectedContinuingLiveDispatchSet (p := p) (rate := rate)).preimage hprefix
  have hcurrent : MeasurableSet {x : ReferenceGeneratedDownBatchCalendar.LaunchSource
      rate rewards C_star C_h s.val s.isLt |
      ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate
        ((observation x).2 n)} := by
    have hbool : MeasurableSet {x : ReferenceGeneratedDownBatchCalendar.LaunchSource
        rate rewards C_star C_h s.val s.isLt |
        decide (ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate
          ((observation x).2 n)) = true} :=
      (hcomplete n) (measurableSet_singleton true)
    simpa only [decide_eq_true_eq] using hbool
  have hcut : MeasurableSet {x : ReferenceGeneratedDownBatchCalendar.LaunchSource
      rate rewards C_star C_h s.val s.isLt |
      wrongUniqueDiagnostic (p := p) (rate := rate) (((observation x).2 n).2.2.2)} :=
    hwrong (measurableSet_singleton true)
  have hprevious : MeasurableSet {x : ReferenceGeneratedDownBatchCalendar.LaunchSource
      rate rewards C_star C_h s.val s.isLt |
      ∃ m : Fin (p.T - s.val), m.val < n.val ∧
        ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate
          ((observation x).2 m)} := by
    rw [show {x : ReferenceGeneratedDownBatchCalendar.LaunchSource
        rate rewards C_star C_h s.val s.isLt |
        ∃ m : Fin (p.T - s.val), m.val < n.val ∧
          ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate
            ((observation x).2 m)} =
      ⋃ m : Fin (p.T - s.val),
        {x | m.val < n.val ∧
          ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate
            ((observation x).2 m)} by
          ext x
          simp only [Set.mem_setOf_eq, Set.mem_iUnion]
          ]
    apply MeasurableSet.iUnion
    intro m
    by_cases hm : m.val < n.val
    · have hbool : MeasurableSet {x : ReferenceGeneratedDownBatchCalendar.LaunchSource
          rate rewards C_star C_h s.val s.isLt |
          decide (ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate
            ((observation x).2 m)) = true} :=
        (hcomplete m) (measurableSet_singleton true)
      simpa [hm, decide_eq_true_eq] using hbool
    · simp [hm]
  exact hselected.inter (hcurrent.inter (hprevious.inter hcut))

/-- The actual launch-fibre event is Borel on its genuine subspace carrier. -/
theorem measurableSet_generatedLiveLaterWrongDownFibreEvent
    (s : Fin p.T) :
    MeasurableSet (generatedLiveLaterWrongDownFibreEvent
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) s) := by
  classical
  have heq : generatedLiveLaterWrongDownFibreEvent
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) s =
      generatedLiveLaterWrongDownCodeFibreEvent
        (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) s := by
    ext x
    constructor
    · intro hphysical
      rcases (mem_generatedLiveLaterWrongDownFibreEvent_iff
        (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) s x).1
        hphysical with ⟨i, n, hselected, hcurrent, ⟨m, hmn, hprevious⟩, cut, hcut, hwrong⟩
      have htests := generatedRecord_code_tests_iff
        (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) s x i n
      rcases htests.mp ⟨hselected, ⟨cut, hcut, hwrong⟩⟩ with ⟨hselected', hwrong'⟩
      exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨n,
        ⟨hselected', hcurrent, ⟨m, hmn, hprevious⟩, hwrong'⟩⟩⟩
    · intro hcode
      rcases Set.mem_iUnion.mp hcode with ⟨i, hi⟩
      rcases Set.mem_iUnion.mp hi with ⟨n, hn⟩
      rcases hn with ⟨hselected, hcurrent, hprevious, hwrong⟩
      have htests := generatedRecord_code_tests_iff
        (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) s x i n
      rcases htests.mpr ⟨hselected, hwrong⟩ with ⟨hselected', hcut⟩
      exact (mem_generatedLiveLaterWrongDownFibreEvent_iff
        (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) s x).2
        ⟨i, n, hselected', hcurrent, hprevious, hcut⟩
  rw [heq]
  exact measurableSet_generatedLiveLaterWrongDownCodeFibreEvent
    (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) s

/-- The exact finite image union is Borel in the original source-input
measurable space, retaining all private arrays, whole rows, and original J. -/
theorem measurableSet_generatedLiveLaterWrongDownSourceEvent :
    MeasurableSet (generatedLiveLaterWrongDownSourceEvent
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)) := by
  classical
  unfold generatedLiveLaterWrongDownSourceEvent
  apply MeasurableSet.iUnion
  intro s
  exact MeasurableSet.subtype_image
    (ReferenceGeneratedDownAmbiguityMeasurability.measurableSet_generatedLaunchFiberSet
      (rate := rate) rewards C_star C_h s.val)
    (measurableSet_generatedLiveLaterWrongDownFibreEvent
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) s)

/-- Every original-source event witness enters the admitted global DOWN cohort
union through the accepted continuing-LIVE later-completion containment. -/
theorem generatedLiveLaterWrongDownSourceEvent_subset_downCohortUnion
    (control0 : ContinuousLearningRows.TimeControl p) :
    generatedLiveLaterWrongDownSourceEvent
        (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) ⊆
      ReferenceGeneratedDownCohortFiniteUnion.downCohortUnionEvent
        rate rewards C_star C_h control0 (AffineBatchDecoder.quota p) := by
  classical
  intro source hsource
  rcases (mem_generatedLiveLaterWrongDownSourceEvent_iff
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) source).1 hsource with
    ⟨s, x, rfl, i, n, hselected, hcomplete, hprevious, cut, hcut, hwrong⟩
  have hcontain :=
    ReferenceGeneratedLiveLaterCompletionContainment.generated_live_later_wrong_down_batch_mem_cohort
      rate rewards C_star C_h s.val s.isLt x i n control0 hcomplete hprevious cut hcut hwrong
  cases hcoordinator : (ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
      rate rewards C_star C_h s.val s.isLt x n).output.preparation.coordinator with
  | live registers owned base outcome =>
      rw [hcoordinator] at hselected hcontain
      cases outcome <;> simp [selectedContinuingCoordinator] at hselected ⊢
      exact hcontain
  | first outcome => simp [hcoordinator, selectedContinuingCoordinator] at hselected
  | collection payload ledger clock cutoff outcome =>
      simp [hcoordinator, selectedContinuingCoordinator] at hselected
  | invalidCollectionCutoff => simp [hcoordinator, selectedContinuingCoordinator] at hselected
  | dagger => simp [hcoordinator, selectedContinuingCoordinator] at hselected

/-- Monotonicity of the original source-input measure under the pointwise
containment. The cohort envelope already pays for all finite indices. -/
theorem generatedLiveLaterWrongDownSourceEvent_measure_le_downCohortUnion
    (control0 : ContinuousLearningRows.TimeControl p) :
    BootstrapPrivateRoundStreams.sourceInputLaw p
        (generatedLiveLaterWrongDownSourceEvent
          (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)) ≤
      BootstrapPrivateRoundStreams.sourceInputLaw p
        (ReferenceGeneratedDownCohortFiniteUnion.downCohortUnionEvent
          rate rewards C_star C_h control0 (AffineBatchDecoder.quota p)) :=
  measure_mono (generatedLiveLaterWrongDownSourceEvent_subset_downCohortUnion
    (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) control0)

/-- The Borel actual later subevent inherits the original-law real quota bound.
The envelope's union already includes launch, follower, and batch indices. -/
theorem generatedLiveLaterWrongDownSourceEvent_measureReal_quota_bound
    (control0 : ContinuousLearningRows.TimeControl p) :
    (BootstrapPrivateRoundStreams.sourceInputLaw p).real
        (generatedLiveLaterWrongDownSourceEvent
          (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)) ≤
      1 / (4 * (ConstructorDimensions.N p : ℝ) ^ 2) := by
  calc
    (BootstrapPrivateRoundStreams.sourceInputLaw p).real
        (generatedLiveLaterWrongDownSourceEvent
          (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)) ≤
      (BootstrapPrivateRoundStreams.sourceInputLaw p).real
        (ReferenceGeneratedDownCohortFiniteUnion.downCohortUnionEvent
          rate rewards C_star C_h control0 (AffineBatchDecoder.quota p)) :=
      measureReal_mono
        (generatedLiveLaterWrongDownSourceEvent_subset_downCohortUnion
          (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) control0)
        (by finiteness)
    _ ≤ 1 / (4 * (ConstructorDimensions.N p : ℝ) ^ 2) :=
      ReferenceGeneratedDownCohortFiniteUnion.downCohortUnionEvent_measureReal_quota_bound
        rate rewards C_star C_h control0

end Bandits.Support.ReferenceGeneratedLiveLaterDownEvent

end
