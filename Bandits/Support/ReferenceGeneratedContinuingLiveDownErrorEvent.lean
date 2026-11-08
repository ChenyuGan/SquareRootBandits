/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedLiveLaterDownEvent
public import Bandits.Support.ReferenceGeneratedInheritedDownFirstEventBound

import Mathlib.MeasureTheory.Measure.Real
import Lean.Elab.Tactic.Omega

/-!
# Actual continuing-LIVE wrong-DOWN diagnostics

Sources: `sources/zip4/manuscript/appendix_a_local_protocol.tex:92-109,111-157`,
`sources/zip4/manuscript/05_binary_transport.tex:20-42,60-124`,
`sources/zip4/manuscript/06_interruptions.tex:246-295,327-348`,
`sources/zip4/manuscript/07_public_setup.tex:127-164`, and
`sources/zip4/manuscript/08_main_theorem.tex:29-42`.

This module records actual selected continuing-LIVE wrong unique DOWN
diagnostics on nonterminal generated launch suffixes. The diagnostic event does
not require a completion: its local physical data produces the actual decoder
quota transition, after which the first/later split enters the existing joint
DOWN cohort envelope.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceGeneratedDownBatchCalendar
open Bandits.Support.ReferenceDownCompletedAmbiguityMeasurability

namespace Bandits.Support.ReferenceGeneratedContinuingLiveDownErrorEvent

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
variable (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
variable (C_star C_h : ℝ)

abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput

/-- The literal actual diagnostic on one selected continuing-LIVE suffix
record. Neither completion nor an earlier completion is tested here. -/
def generatedContinuingLiveWrongDownFibreEvent
    (s : Fin p.T) :
    Set (ReferenceGeneratedDownBatchCalendar.LaunchSource
      rate rewards C_star C_h s.val s.isLt) :=
  {x | ∃ i : Fin (p.m - 1), ∃ n : Fin (p.T - s.val),
    ReferenceGeneratedLiveLaterDownEvent.selectedContinuingCoordinator
      (p := p) (rate := rate)
      (ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
        rate rewards C_star C_h s.val s.isLt x n).output.preparation.coordinator = true ∧
    ∃ cut,
      ((ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
        rate rewards C_star C_h s.val s.isLt x n).output.followers i).down = some cut ∧
      ReferenceDownReception.wrongUniqueAccepted cut}

/-- The original source-input event is the finite union of the literal launch
fibres, embedded by their actual subtype values. -/
def generatedContinuingLiveWrongDownSourceEvent : Set (SourceInput p) :=
  ⋃ s : Fin p.T,
    (Subtype.val : ReferenceGeneratedDownBatchCalendar.LaunchSource
      rate rewards C_star C_h s.val s.isLt → SourceInput p) ''
      generatedContinuingLiveWrongDownFibreEvent
        (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) s

theorem mem_generatedContinuingLiveWrongDownFibreEvent_iff
    (s : Fin p.T)
    (x : ReferenceGeneratedDownBatchCalendar.LaunchSource
      rate rewards C_star C_h s.val s.isLt) :
    x ∈ generatedContinuingLiveWrongDownFibreEvent
        (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) s ↔
      ∃ i : Fin (p.m - 1), ∃ n : Fin (p.T - s.val),
        ReferenceGeneratedLiveLaterDownEvent.selectedContinuingCoordinator
          (p := p) (rate := rate)
          (ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
            rate rewards C_star C_h s.val s.isLt x n).output.preparation.coordinator = true ∧
        ∃ cut,
          ((ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
            rate rewards C_star C_h s.val s.isLt x n).output.followers i).down = some cut ∧
          ReferenceDownReception.wrongUniqueAccepted cut := Iff.rfl

theorem mem_generatedContinuingLiveWrongDownSourceEvent_iff
    (source : SourceInput p) :
    source ∈ generatedContinuingLiveWrongDownSourceEvent
        (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) ↔
      ∃ s : Fin p.T,
        ∃ x : ReferenceGeneratedDownBatchCalendar.LaunchSource
          rate rewards C_star C_h s.val s.isLt,
          x.1 = source ∧
            x ∈ generatedContinuingLiveWrongDownFibreEvent
              (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) s := by
  simp [generatedContinuingLiveWrongDownSourceEvent]

private abbrev LiveInput (p : ConstructorDimensions.Parameters)
    (rate : ReferenceActivePhysicalStep.RateInput p) :=
  ReferenceFirstLiveCoordinatorStepMeasurability.LiveInput p rate

private def outcomeIsContinuing :
    ReferenceLiveDispatchOutputMeasurability.OutcomeData p → Bool
  | .continuingChosen _ _ _ => true
  | _ => false

private def selectedContinuingLiveDispatchSet :
    Set (ReferenceActivePhysicalStep.RoundInput p rate) :=
  (Subtype.val : LiveInput p rate → ReferenceActivePhysicalStep.RoundInput p rate) ''
    {x | outcomeIsContinuing (p := p)
      ((ReferenceLiveDispatchOutputMeasurability.dispatchObservation
        (ReferenceFirstLiveCoordinatorStepMeasurability.liveCoordinates x)).2) = true}

private theorem liveDispatchObservation_code_flag
    (x : LiveInput p rate) :
    outcomeIsContinuing (p := p)
        ((ReferenceLiveDispatchOutputMeasurability.dispatchObservation
          (ReferenceFirstLiveCoordinatorStepMeasurability.liveCoordinates x)).2) =
      ReferenceGeneratedLiveLaterDownEvent.selectedContinuingCoordinator
        (p := p) (rate := rate) (ReferenceActivePhysicalStep.dispatch x.1) := by
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
    _ = ReferenceGeneratedLiveLaterDownEvent.selectedContinuingCoordinator
        (p := p) (rate := rate) (ReferenceActivePhysicalStep.dispatch x.1) := by
          rw [ReferenceFirstLiveCoordinatorStepMeasurability.live_dispatch_eq x]
          cases hOut : CoordinatorRoundDispatch.dispatchLive actualInput <;>
            simp [actualOutcome, hOut, outcomeIsContinuing,
              ReferenceLiveDispatchOutputMeasurability.outcomeData,
              ReferenceGeneratedLiveLaterDownEvent.selectedContinuingCoordinator]

private theorem measurableSet_selectedContinuingLiveDispatchSet :
    MeasurableSet (selectedContinuingLiveDispatchSet (p := p) (rate := rate)) := by
  classical
  apply MeasurableSet.subtype_image
  · exact ReferenceFirstLiveCoordinatorStepMeasurability.measurableSet_liveSet
  · have htag : Measurable (fun code : ReferenceLiveDispatchOutputMeasurability.OutcomeData p =>
        outcomeIsContinuing (p := p) code) := Measurable.of_discrete
    have hcode : Measurable (fun x : LiveInput p rate =>
        outcomeIsContinuing (p := p)
          ((ReferenceLiveDispatchOutputMeasurability.dispatchObservation
            (ReferenceFirstLiveCoordinatorStepMeasurability.liveCoordinates x)).2)) :=
      (htag.comp measurable_snd).comp
        ReferenceFirstLiveCoordinatorStepMeasurability.measurable_liveDispatchObservation
    exact hcode (measurableSet_singleton true)

private theorem mem_selectedContinuingLiveDispatchSet_iff
    (input : ReferenceActivePhysicalStep.RoundInput p rate) :
    input ∈ selectedContinuingLiveDispatchSet (p := p) (rate := rate) ↔
      ReferenceGeneratedLiveLaterDownEvent.selectedContinuingCoordinator
        (p := p) (rate := rate) (ReferenceActivePhysicalStep.dispatch input) = true := by
  classical
  cases hstate : input.state.coordinator with
  | first =>
      have hnot : input ∉
          ReferenceFirstLiveCoordinatorStepMeasurability.liveSet
            (p := p) (rate := rate) := by
        simp [ReferenceFirstLiveCoordinatorStepMeasurability.liveSet,
          ReferenceActivePhysicalStepMeasurability.encodeState,
          ReferenceActivePhysicalStepMeasurability.encodeCoordinator, hstate]
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact False.elim (hnot x.property)
      · intro htag
        rw [ReferenceActivePhysicalStep.dispatch_first input hstate] at htag
        simp [ReferenceGeneratedLiveLaterDownEvent.selectedContinuingCoordinator] at htag
  | dagger =>
      have hnot : input ∉
          ReferenceFirstLiveCoordinatorStepMeasurability.liveSet
            (p := p) (rate := rate) := by
        simp [ReferenceFirstLiveCoordinatorStepMeasurability.liveSet,
          ReferenceActivePhysicalStepMeasurability.encodeState,
          ReferenceActivePhysicalStepMeasurability.encodeCoordinator, hstate]
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact False.elim (hnot x.property)
      · intro htag
        rw [ReferenceActivePhysicalStep.dispatch_dagger input hstate] at htag
        simp [ReferenceGeneratedLiveLaterDownEvent.selectedContinuingCoordinator] at htag
  | collection payload ledger proposal =>
      have hnot : input ∉
          ReferenceFirstLiveCoordinatorStepMeasurability.liveSet
            (p := p) (rate := rate) := by
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
          simp [ReferenceGeneratedLiveLaterDownEvent.selectedContinuingCoordinator] at htag
        · rw [(ReferenceActivePhysicalStep.dispatch_collection_invalid_cutoff
            input payload ledger proposal hstate hcut).1] at htag
          simp [ReferenceGeneratedLiveLaterDownEvent.selectedContinuingCoordinator] at htag
  | live registers owned base =>
      let liveInput : LiveInput p rate :=
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

private def wrongUniqueDiagnostic
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

private theorem generatedRecord_selectedWrong_iff_codes
    (s : Fin p.T)
    (x : ReferenceGeneratedDownBatchCalendar.LaunchSource
      rate rewards C_star C_h s.val s.isLt)
    (i : Fin (p.m - 1)) (n : Fin (p.T - s.val)) :
    (ReferenceGeneratedLiveLaterDownEvent.selectedContinuingCoordinator
        (p := p) (rate := rate)
        (ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
          rate rewards C_star C_h s.val s.isLt x n).output.preparation.coordinator = true ∧
      ∃ cut,
        ((ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
          rate rewards C_star C_h s.val s.isLt x n).output.followers i).down = some cut ∧
        ReferenceDownReception.wrongUniqueAccepted cut) ↔
      ReferenceDownCompletedAmbiguityMeasurability.prefixInput
          s.val n.val (by omega)
          (ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput
            rate rewards C_star C_h s.val s.isLt x) ∈
        selectedContinuingLiveDispatchSet (p := p) (rate := rate) ∧
      wrongUniqueDiagnostic (p := p) (rate := rate)
        (((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
          rate rewards C_star C_h s.val s.isLt i x).2 n).2.2.2) = true := by
  let record := ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
    rate rewards C_star C_h s.val s.isLt x n
  have hinput : record.input = ReferenceDownCompletedAmbiguityMeasurability.prefixInput
      s.val n.val (by omega)
      (ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput
        rate rewards C_star C_h s.val s.isLt x) := rfl
  have hround :
      (ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
        rate rewards C_star C_h s.val s.isLt i x).2 n =
        ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation record.input i := rfl
  rw [← hinput]
  constructor
  · rintro ⟨hselected, cut, hcut, hwrong⟩
    exact ⟨(mem_selectedContinuingLiveDispatchSet_iff
      (p := p) (rate := rate) record.input).2 hselected,
      (wrongUniqueDiagnostic_eq_true_iff_record (p := p) (rate := rate) record i).2
        ⟨cut, hcut, hwrong⟩⟩
  · rintro ⟨hselected, hwrong⟩
    exact ⟨(mem_selectedContinuingLiveDispatchSet_iff
      (p := p) (rate := rate) record.input).1 hselected,
      (wrongUniqueDiagnostic_eq_true_iff_record (p := p) (rate := rate) record i).1
        (by simpa [hround] using hwrong)⟩

private def generatedContinuingLiveWrongDownCodeFibreEvent
    (s : Fin p.T) :
    Set (ReferenceGeneratedDownBatchCalendar.LaunchSource
      rate rewards C_star C_h s.val s.isLt) :=
  ⋃ i : Fin (p.m - 1), ⋃ n : Fin (p.T - s.val),
    {x |
      ReferenceDownCompletedAmbiguityMeasurability.prefixInput
        s.val n.val (by omega)
        (ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput
          rate rewards C_star C_h s.val s.isLt x) ∈
        selectedContinuingLiveDispatchSet (p := p) (rate := rate) ∧
      wrongUniqueDiagnostic (p := p) (rate := rate)
        (((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
          rate rewards C_star C_h s.val s.isLt i x).2 n).2.2.2) = true}

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

private theorem measurableSet_generatedContinuingLiveWrongDownCodeFibreEvent
    (s : Fin p.T) :
    MeasurableSet (generatedContinuingLiveWrongDownCodeFibreEvent
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) s) := by
  classical
  unfold generatedContinuingLiveWrongDownCodeFibreEvent
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
  have hwrongSet : MeasurableSet {x : ReferenceGeneratedDownBatchCalendar.LaunchSource
      rate rewards C_star C_h s.val s.isLt |
      wrongUniqueDiagnostic (p := p) (rate := rate) (((observation x).2 n).2.2.2)} :=
    hwrong (measurableSet_singleton true)
  exact hselected.inter hwrongSet

/-- The actual launch-fibre event is Borel on its genuine subspace carrier. -/
theorem measurableSet_generatedContinuingLiveWrongDownFibreEvent
    (s : Fin p.T) :
    MeasurableSet (generatedContinuingLiveWrongDownFibreEvent
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) s) := by
  classical
  have heq : generatedContinuingLiveWrongDownFibreEvent
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) s =
      generatedContinuingLiveWrongDownCodeFibreEvent
        (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) s := by
    ext x
    constructor
    · intro hphysical
      rcases (mem_generatedContinuingLiveWrongDownFibreEvent_iff
        (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) s x).1
        hphysical with ⟨i, n, hselected, cut, hcut, hwrong⟩
      rcases (generatedRecord_selectedWrong_iff_codes
        (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
        s x i n).1 ⟨hselected, cut, hcut, hwrong⟩ with ⟨hselected', hwrong'⟩
      exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨n, ⟨hselected', hwrong'⟩⟩⟩
    · intro hcode
      rcases Set.mem_iUnion.mp hcode with ⟨i, hi⟩
      rcases Set.mem_iUnion.mp hi with ⟨n, hn⟩
      rcases hn with ⟨hselected, hwrong⟩
      rcases (generatedRecord_selectedWrong_iff_codes
        (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
        s x i n).2 ⟨hselected, hwrong⟩ with ⟨hselected', cut, hcut, hwrong'⟩
      exact (mem_generatedContinuingLiveWrongDownFibreEvent_iff
        (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) s x).2
        ⟨i, n, hselected', cut, hcut, hwrong'⟩
  rw [heq]
  exact measurableSet_generatedContinuingLiveWrongDownCodeFibreEvent
    (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) s

/-- The finite image union is Borel in the original source-input space,
retaining all source coordinates and its original finite J coordinate. -/
theorem measurableSet_generatedContinuingLiveWrongDownSourceEvent :
    MeasurableSet (generatedContinuingLiveWrongDownSourceEvent
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)) := by
  classical
  unfold generatedContinuingLiveWrongDownSourceEvent
  apply MeasurableSet.iUnion
  intro s
  exact MeasurableSet.subtype_image
    (ReferenceGeneratedDownAmbiguityMeasurability.measurableSet_generatedLaunchFiberSet
      (rate := rate) rewards C_star C_h s.val)
    (measurableSet_generatedContinuingLiveWrongDownFibreEvent
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) s)

private theorem actualRecord_down_some_logged
    (record : ReferenceFollowerDownDecoderReplay.Record p rate)
    (i : Fin (p.m - 1))
    (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (hcut : (record.output.followers i).down = some cut) :
    ∃ logged, (record.output.followers i).downInput = some logged := by
  rw [← ReferenceDownCompletedAmbiguityMeasurability.record_preparationDiagnostics
    record i] at hcut ⊢
  let prepared := record.output.preparation.followers.followers i
  let observation := ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i
  cases hconfiguration : prepared.configuration with
  | dagger =>
      simp [ReferenceActivePhysicalStep.PreparedRound.observeFollower,
        ReferenceActivePhysicalStep.finishFollower, prepared, hconfiguration] at hcut
  | ordinary state memory =>
      let recorded := ReferenceActivePhysicalStep.recordFollower
        record.output.preparation.coordinator.downView prepared.follower prepared.row
        prepared.activation prepared.time prepared.active prepared.arm observation state
      have hp :
          ((ReferenceActivePhysicalStep.finishFollower
            record.output.preparation.coordinator.downView prepared observation).downInput,
            (ReferenceActivePhysicalStep.finishFollower
              record.output.preparation.coordinator.downView prepared observation).down) =
            (recorded.downInput, recorded.down) := by
        simp only [ReferenceActivePhysicalStep.finishFollower, prepared, hconfiguration]
        cases hresult : (ReferenceActivePhysicalStep.recordFollower
            record.output.preparation.coordinator.downView prepared.follower prepared.row
            prepared.activation prepared.time prepared.active prepared.arm observation state).result with
        | error failure => rfl
        | ok post =>
            dsimp only
            cases hfinish : DeclaredFollowerLocalRound.releaseAndFinish rate prepared.follower
                prepared.row prepared.time observation state memory post with
            | error failure => rfl
            | ok next => cases next; rfl
      have hfinishCut :
          (ReferenceActivePhysicalStep.finishFollower
            record.output.preparation.coordinator.downView prepared observation).down = some cut := by
        simpa [ReferenceActivePhysicalStep.PreparedRound.observeFollower,
          prepared, observation, ReferenceFollowerDownDecoderReplay.preparedOwnObservation] using hcut
      have hrecorded : recorded.down = some cut := by
        exact (congrArg Prod.snd hp).symm.trans hfinishCut
      by_cases hstatus : state.status = .unoccupied
      · cases hlogging : ActiveFollowerLogging.checkedLogging prepared.follower prepared.row
            prepared.activation prepared.time (prepared.arm, observation) state with
        | error failure =>
            simp only [recorded, ReferenceActivePhysicalStep.recordFollower,
              dite_eq_left hstatus, hlogging, reduceCtorEq] at hrecorded
        | ok logged =>
            refine ⟨logged, ?_⟩
            have hrecordedInput : recorded.downInput = some logged := by
              simp only [recorded, ReferenceActivePhysicalStep.recordFollower,
                dite_eq_left hstatus, hlogging]
            calc
              (ReferenceActivePhysicalStep.finishFollower
                record.output.preparation.coordinator.downView prepared observation).downInput =
                  recorded.downInput := congrArg Prod.fst hp
              _ = some logged := hrecordedInput
      · simp only [ReferenceActivePhysicalStep.recordFollower,
          recorded, dite_eq_right hstatus, reduceCtorEq] at hrecorded

/-- Any actual retained wrong unique DOWN cut proves that this same actual
record completed its decoder batch. The local premise is only the physical
DOWN diagnostic; the theorem consumes no run trace, supplied completion,
logged-bank assumption, or probability premise. -/
theorem actualRecord_wrongUniqueAccepted_implies_completedBatchAtRound
    (record : ReferenceFollowerDownDecoderReplay.Record p rate)
    (i : Fin (p.m - 1))
    (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (hcut : (record.output.followers i).down = some cut)
    (hwrong : ReferenceDownReception.wrongUniqueAccepted cut) :
    ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate
      (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation record.input i) := by
  classical
  obtain ⟨logged, hlogged⟩ := actualRecord_down_some_logged
    (p := p) (rate := rate) record i cut hcut
  have hcutActual := ReferenceDownCompletedAmbiguityMeasurability.record_downCut_eq_actual
    record i logged cut hlogged hcut
  let actual := ReferenceDownReception.referenceDownCut p
    record.output.preparation.coordinator.downView i record.input.row record.input.time
      (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i) rate logged
  have hcomparison : actual.rawComparison = some false := by
    change (ReferenceDownReception.referenceDownCut p
      record.output.preparation.coordinator.downView i record.input.row record.input.time
        (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i) rate logged).rawComparison =
      some false
    rw [← hcutActual]
    exact hwrong.1
  have hraw : actual.raw ≠ none := by
    change (ReferenceDownReception.referenceDownCut p
      record.output.preparation.coordinator.downView i record.input.row record.input.time
        (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i) rate logged).raw ≠ none
    rw [← hcutActual]
    exact hwrong.2.1
  have hcompared : actual.rawComparison ≠ none := by
    rw [hcomparison]
    exact Option.some_ne_none false
  have hrawEq := ReferenceDownReception.referenceDownCut_raw_eq_currentDecodeStep_of_compared
    record.output.preparation.coordinator.downView i record.input.row record.input.time
    (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i) rate logged hcompared
  change actual.raw =
      (ActiveFollowerDownAcceptance.currentDecodeStep p i record.input.row record.input.time
        (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i) rate logged).2 at hrawEq
  have hstepNe :
      (ActiveFollowerDownAcceptance.currentDecodeStep p i record.input.row record.input.time
        (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i) rate logged).2 ≠ none := by
    rw [← hrawEq]
    exact hraw
  cases hstep : (ActiveFollowerDownAcceptance.currentDecodeStep p i record.input.row
      record.input.time (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i)
      rate logged).2 with
  | none => exact (hstepNe hstep).elim
  | some word =>
      have hstepOutput :
          AffineBatchDecoder.stepOutput p
            (ActiveFollowerDownAcceptance.currentInputExtension p
              (ActiveFollowerDownAcceptance.currentRoundInput p i record.input.row
                record.input.time (ReferenceFollowerDownDecoderReplay.preparedOwnObservation
                  record i) rate logged)) logged.downBatch record.input.time = some word := by
        change (ActiveFollowerDownAcceptance.currentDecodeStep p i record.input.row
          record.input.time (ReferenceFollowerDownDecoderReplay.preparedOwnObservation
            record i) rate logged).2 = some word
        exact hstep
      have hquota := (AffineBatchDecoder.stepOutput_eq_some_iff p
        (ActiveFollowerDownAcceptance.currentInputExtension p
          (ActiveFollowerDownAcceptance.currentRoundInput p i record.input.row record.input.time
            (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i) rate logged))
        logged.downBatch record.input.time word).mp hstepOutput |>.1
      have hcomparisonSome : cut.rawComparison.isSome = true := by
        calc
          cut.rawComparison.isSome = actual.rawComparison.isSome := by rw [hcutActual]
          _ = true := by rw [hcomparison]; rfl
      apply (ReferenceGeneratedDownResetCompletionCensus.completedBatchAtRound_iff_executed_quota
        record i).2
      exact ⟨logged, cut, hlogged, hcut, hcomparisonSome, hquota⟩

/-- The actual event splits at the first completion for the same follower and
the same launch suffix. Both resulting leaves use their existing containment
into the single joint DOWN cohort union. -/
theorem generatedContinuingLiveWrongDownSourceEvent_subset_downCohortUnion
    (control0 : ContinuousLearningRows.TimeControl p) :
    generatedContinuingLiveWrongDownSourceEvent
        (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) ⊆
      ReferenceGeneratedDownCohortFiniteUnion.downCohortUnionEvent
        rate rewards C_star C_h control0 (AffineBatchDecoder.quota p) := by
  classical
  intro source hsource
  rcases (mem_generatedContinuingLiveWrongDownSourceEvent_iff
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) source).1 hsource with
    ⟨s, x, hsourceEq, hFibre⟩
  rcases (mem_generatedContinuingLiveWrongDownFibreEvent_iff
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) s x).1 hFibre with
    ⟨i, n, hselected, cut, hcut, hwrong⟩
  let record := ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
    rate rewards C_star C_h s.val s.isLt x n
  have hcomplete := actualRecord_wrongUniqueAccepted_implies_completedBatchAtRound
    (p := p) (rate := rate) record i cut hcut hwrong
  have hround :
      (ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
        rate rewards C_star C_h s.val s.isLt i x).2 n =
      ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation record.input i := rfl
  have hcomplete' : ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate
      ((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
        rate rewards C_star C_h s.val s.isLt i x).2 n) := by
    rw [hround]
    exact hcomplete
  by_cases hearli : ∃ m : Fin (p.T - s.val), m.val < n.val ∧
      ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate
        ((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
          rate rewards C_star C_h s.val s.isLt i x).2 m)
  · rcases hearli with ⟨m, hmn, hprevious⟩
    have hlater : x.1 ∈ ReferenceGeneratedLiveLaterDownEvent.generatedLiveLaterWrongDownSourceEvent
        (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) := by
      apply (ReferenceGeneratedLiveLaterDownEvent.mem_generatedLiveLaterWrongDownSourceEvent_iff
        (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) x.1).2
      refine ⟨s, x, rfl, i, n, hselected, hcomplete', ⟨m, hmn, hprevious⟩, cut, hcut, hwrong⟩
    rw [← hsourceEq]
    exact ReferenceGeneratedLiveLaterDownEvent.generatedLiveLaterWrongDownSourceEvent_subset_downCohortUnion
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) control0 hlater
  · have hfirst : source ∈ ReferenceGeneratedInheritedDownFirstEventBound.inheritedFirstWrongEvent
        rate rewards C_star C_h := by
      change ∃ (start : ℕ) (hstart : start < p.T)
          (launch : ReferenceGeneratedDownBatchCalendar.LaunchSource
            rate rewards C_star C_h start hstart)
          (follower : Fin (p.m - 1)) (ordinal : Fin (p.T - start)),
          launch.val = source ∧
            (ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate
                ((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
                  rate rewards C_star C_h start hstart follower launch).2 ordinal) ∧
              ∀ l (hl : l < ordinal.val),
                ¬ ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate
                  ((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
                    rate rewards C_star C_h start hstart follower launch).2
                    ⟨l, lt_trans hl ordinal.isLt⟩)) ∧
            ∃ savedCut,
              ((ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
                rate rewards C_star C_h start hstart launch ordinal).output.followers follower).down =
                some savedCut ∧ ReferenceDownReception.wrongUniqueAccepted savedCut
      refine ⟨s.val, s.isLt, x, i, n, hsourceEq, ?_, cut, hcut, hwrong⟩
      refine ⟨hcomplete', ?_⟩
      intro l hl hEarlier
      exact hearli ⟨⟨l, lt_trans hl n.isLt⟩, hl, hEarlier⟩
    exact ReferenceGeneratedInheritedDownFirstEventBound.inheritedFirstWrongEvent_subset_downCohortUnion
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) control0 hfirst

/-- The source-input measure is bounded by the one existing joint DOWN cohort
envelope. The envelope already accounts for every launch, follower, word,
ordinal and batch index. -/
theorem generatedContinuingLiveWrongDownSourceEvent_measure_le_downCohortUnion
    (control0 : ContinuousLearningRows.TimeControl p) :
    BootstrapPrivateRoundStreams.sourceInputLaw p
        (generatedContinuingLiveWrongDownSourceEvent
          (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)) ≤
      BootstrapPrivateRoundStreams.sourceInputLaw p
        (ReferenceGeneratedDownCohortFiniteUnion.downCohortUnionEvent
          rate rewards C_star C_h control0 (AffineBatchDecoder.quota p)) :=
  measure_mono (generatedContinuingLiveWrongDownSourceEvent_subset_downCohortUnion
    (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) control0)

/-- The Borel actual wrong-DOWN diagnostic event has the shared cohort quota
bound under the original, finite unnormalized source-input law. -/
theorem generatedContinuingLiveWrongDownSourceEvent_measureReal_quota_bound
    (control0 : ContinuousLearningRows.TimeControl p) :
    (BootstrapPrivateRoundStreams.sourceInputLaw p).real
        (generatedContinuingLiveWrongDownSourceEvent
          (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)) ≤
      1 / (4 * (ConstructorDimensions.N p : ℝ) ^ 2) := by
  calc
    (BootstrapPrivateRoundStreams.sourceInputLaw p).real
        (generatedContinuingLiveWrongDownSourceEvent
          (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)) ≤
      (BootstrapPrivateRoundStreams.sourceInputLaw p).real
        (ReferenceGeneratedDownCohortFiniteUnion.downCohortUnionEvent
          rate rewards C_star C_h control0 (AffineBatchDecoder.quota p)) :=
      measureReal_mono
        (generatedContinuingLiveWrongDownSourceEvent_subset_downCohortUnion
          (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) control0)
        (by finiteness)
    _ ≤ 1 / (4 * (ConstructorDimensions.N p : ℝ) ^ 2) :=
      ReferenceGeneratedDownCohortFiniteUnion.downCohortUnionEvent_measureReal_quota_bound
        rate rewards C_star C_h control0

end Bandits.Support.ReferenceGeneratedContinuingLiveDownErrorEvent

end
