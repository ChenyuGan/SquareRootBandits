/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedUpFixedReplySuffix
public import Bandits.Support.ReferenceGeneratedUpAwaitedAmbiguityTail
public import Bandits.Support.ReferenceGeneratedSavedWrongEvent

/-!
# Actual complete-suffix wrong-UP coverage

Sources: `sources/zip4/manuscript/appendix_a_local_protocol.tex:8-14,92-157`,
`sources/zip4/manuscript/05_binary_transport.tex:20-53,70-124`,
`sources/zip4/manuscript/06_interruptions.tex:164-177,246-296,327-361`, and
`sources/zip4/manuscript/08_main_theorem.tex:29-42`.

This module reads only the retained UP diagnostic from each actual complete
physical suffix record. It joins a wrong accepted record to the original
source's generated-UP survival event and embeds that event in the existing
all-J ambiguity envelope. It does not cover DOWN events or identify the
inclusive first-overflow stopped event.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal Classical

namespace Bandits.Support.ReferenceGeneratedUpFalseTail

open Bandits.Support.ConstructorDimensions
open Bandits.Support.AffineChannelLaw
open Bandits.Support.AffineBatchDecoder
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceCompletePhysicalHistory
open Bandits.Support.ReferenceGeneratedDownAmbiguityMeasurability
open Bandits.Support.ReferenceGeneratedAffineHashHalf
open Bandits.Support.ReferenceGeneratedUpBatchPrefixEvent
open Bandits.Support.ReferenceGeneratedUpSourceCalendar
open Bandits.Support.ReferenceGeneratedUpSourceTail
open Bandits.Support.ReferenceSavedWrongUniqueMeasurability
open Bandits.Support.ReferenceActiveHorizonMeasurability

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput

variable {p : Parameters} {rate : RateInput p}

abbrev UpCollectionCode := ReferenceCollectionServiceTailMeasurability.CollectionTailCode p rate

/-- The literal UP-only projection of the retained physical diagnostic. -/
def upWrongRecordFlag
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) : Bool :=
  record.output.coordinator.up.elim false fun diagnostic => diagnostic.wrongUniqueAccepted

/-- The UP-only wrong-unique bit on the canonical retained record code. -/
def upWrongRecordCode
    (code : ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate)) : Bool :=
  ReferenceSavedWrongUniqueMeasurability.savedWrongUpCode
    (ReferenceSavedWrongUniqueMeasurability.roundRecordCollectionCode code)

/-- The UP projection of an observation code reconstructs the literal UP
diagnostic stored on the corresponding physical record. -/
theorem upWrongRecordCode_roundRecordCode
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) :
    upWrongRecordCode (ReferenceActiveHorizonMeasurability.roundRecordCode record) =
      upWrongRecordFlag record := by
  have hdecode := ReferenceActiveHorizonMeasurability.roundRecordCode_reconstructs record
  have hup := congrArg ReferenceActivePhysicalStep.CoordinatorObservation.up hdecode.2.1
  unfold upWrongRecordCode upWrongRecordFlag
  change ReferenceSavedWrongUniqueMeasurability.savedWrongUpCode
      (ReferenceSavedWrongUniqueMeasurability.roundRecordCollectionCode
        (ReferenceActiveHorizonMeasurability.roundRecordCode record)) = _
  unfold ReferenceSavedWrongUniqueMeasurability.savedWrongUpCode
  rw [show ReferenceCollectionServiceTailMeasurability.decodeCollectionObservation
      (ReferenceSavedWrongUniqueMeasurability.roundRecordCollectionCode
        (ReferenceActiveHorizonMeasurability.roundRecordCode record)) =
      record.coordinatorDiagnostics from hdecode.2.1]
  simp [ReferenceActivePhysicalHorizon.RoundRecord.coordinatorDiagnostics]

/-- The prefix code on canonical run observation codes reads only UP wrong
diagnostics. -/
def upWrongPrefixCode (count : ℕ)
    (codes : List (ReferenceActiveHorizonMeasurability.RoundRecordCode
      (p := p) (rate := rate))) : Bool :=
  (codes.take count).any upWrongRecordCode

private def upWrongCodeAtTag
    (tag : Unit ⊕ ReferenceActiveHorizonMeasurability.RoundRecordCode
      (p := p) (rate := rate)) : Bool :=
  tag.elim (fun _ => false) upWrongRecordCode

private def upWrongCodeAt
    (codes : List (ReferenceActiveHorizonMeasurability.RoundRecordCode
      (p := p) (rate := rate))) (index : ℕ) : Bool :=
  upWrongCodeAtTag (ReferenceActiveHorizonMeasurability.listObservationAt codes index)

private theorem upWrongPrefixCode_true_iff_indexed
    (count : ℕ)
    (codes : List (ReferenceActiveHorizonMeasurability.RoundRecordCode
      (p := p) (rate := rate))) :
    upWrongPrefixCode count codes = true ↔
      ∃ index, index < count ∧ upWrongCodeAt codes index = true := by
  unfold upWrongPrefixCode upWrongCodeAt
  rw [List.any_eq_true]
  constructor
  · rintro ⟨code, hmem, hbad⟩
    rcases List.mem_take_iff_getElem.mp hmem with ⟨index, hindex, hcode⟩
    have hcount : index < count := lt_of_lt_of_le hindex (Nat.min_le_left _ _)
    have hlen : index < codes.length := lt_of_lt_of_le hindex (Nat.min_le_right _ _)
    refine ⟨index, hcount, ?_⟩
    simp [ReferenceActiveHorizonMeasurability.listObservationAt,
      List.getElem?_eq_getElem hlen, hcode, upWrongCodeAtTag, hbad]
  · rintro ⟨index, hcount, hbad⟩
    cases htag : ReferenceActiveHorizonMeasurability.listObservationAt codes index with
    | inl missing => simp [htag, upWrongCodeAtTag] at hbad
    | inr code =>
        have hget : codes[index]? = some code := by
          cases hget : codes[index]? with
          | none => simp [ReferenceActiveHorizonMeasurability.listObservationAt, hget] at htag
          | some actual =>
              have hactual : actual = code := by
                simpa [ReferenceActiveHorizonMeasurability.listObservationAt, hget] using htag
              subst code
              rfl
        rcases List.getElem?_eq_some_iff.mp hget with ⟨hlen, hcode⟩
        have hmem : code ∈ codes.take count :=
          List.mem_take_iff_getElem.mpr ⟨index,
            (Nat.lt_min).2 ⟨hcount, hlen⟩, hcode⟩
        exact ⟨code, hmem, by simpa [upWrongCodeAt, htag, upWrongCodeAtTag] using hbad⟩

private theorem measurable_upWrongRecordCode :
    Measurable (upWrongRecordCode (p := p) (rate := rate)) := by
  have hphysical : Measurable (fun code : ReferenceActiveHorizonMeasurability.RoundRecordCode
      (p := p) (rate := rate) => code.2.2.1) :=
    measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_id))
  have htail1 : Measurable (fun code : ReferenceActiveHorizonMeasurability.PhysicalCode
      (p := p) (rate := rate) => code.2) := measurable_snd
  have htail2 : Measurable (fun code : ReferenceActiveHorizonMeasurability.PhysicalCode
      (p := p) (rate := rate) => code.2.2) := measurable_snd.comp htail1
  have htail3 : Measurable (fun code : ReferenceActiveHorizonMeasurability.PhysicalCode
      (p := p) (rate := rate) => code.2.2.2) := measurable_snd.comp htail2
  have hcollection : Measurable (fun code : ReferenceActiveHorizonMeasurability.PhysicalCode
      (p := p) (rate := rate) => code.2.2.2.2) := measurable_snd.comp htail3
  have hdiagnostic : Measurable (fun code : UpCollectionCode (p := p) (rate := rate) =>
      code.2.2.2.2) := by
    have h1 : Measurable (fun code : UpCollectionCode (p := p) (rate := rate) => code.2) :=
      measurable_snd
    have h2 : Measurable (fun code : UpCollectionCode (p := p) (rate := rate) => code.2.2) :=
      measurable_snd.comp h1
    have h3 : Measurable (fun code : UpCollectionCode (p := p) (rate := rate) => code.2.2.2) :=
      measurable_snd.comp h2
    exact measurable_snd.comp h3
  have hflag : Measurable (fun diagnostic : Option
      (ReferenceCollectionServiceTailMeasurability.UpDiagnosticCode p rate) =>
        diagnostic.elim false fun value => value.wrongUniqueAccepted) :=
    Measurable.of_discrete
  have hsaved : Measurable (ReferenceSavedWrongUniqueMeasurability.savedWrongUpCode
      (p := p) (rate := rate)) := by
    have heq : ReferenceSavedWrongUniqueMeasurability.savedWrongUpCode
        (p := p) (rate := rate) = fun code : UpCollectionCode (p := p) (rate := rate) =>
          (code.2.2.2.2).elim false fun value => value.wrongUniqueAccepted := by
      funext code
      cases h : code.2.2.2.2 with
      | none => simp [ReferenceSavedWrongUniqueMeasurability.savedWrongUpCode,
          ReferenceCollectionServiceTailMeasurability.decodeCollectionObservation, h]
      | some diagnostic =>
          simp [ReferenceSavedWrongUniqueMeasurability.savedWrongUpCode,
            ReferenceCollectionServiceTailMeasurability.decodeCollectionObservation,
            ReferenceCollectionServiceTailMeasurability.decodeUpDiagnostic, h]
    rw [heq]
    exact hflag.comp hdiagnostic
  have hround : Measurable (ReferenceSavedWrongUniqueMeasurability.roundRecordCollectionCode
      (p := p) (rate := rate)) := by
    exact hcollection.comp hphysical
  exact hsaved.comp hround

private theorem measurable_upWrongCodeAtTag :
    Measurable (upWrongCodeAtTag (p := p) (rate := rate)) :=
  Measurable.sumElim measurable_const measurable_upWrongRecordCode

private theorem measurable_upWrongCodeAt (index : ℕ) :
    Measurable (fun codes : List (ReferenceActiveHorizonMeasurability.RoundRecordCode
      (p := p) (rate := rate)) => upWrongCodeAt codes index) := by
  have hcoordinates := ReferenceActiveHorizonMeasurability.measurable_listObservationCoordinates
    (α := ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate))
  have hindexTag : Measurable (fun codes : List
      (ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate)) =>
      ReferenceActiveHorizonMeasurability.listObservationAt codes index) := by
    have h := (measurable_pi_apply index).comp (measurable_snd.comp hcoordinates)
    change Measurable (fun codes =>
      (ReferenceActiveHorizonMeasurability.listObservationCoordinates codes).2 index)
    exact h
  exact measurable_upWrongCodeAtTag.comp hindexTag

private theorem measurable_upWrongPrefixCode :
    Measurable (fun input : ℕ × List
      (ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate)) =>
      upWrongPrefixCode input.1 input.2) := by
  have hbad (index : ℕ) : Measurable (fun input : ℕ × List
      (ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate)) =>
      upWrongCodeAt input.2 index) :=
    (measurable_upWrongCodeAt index).comp measurable_snd
  have hlt (index : ℕ) : Measurable (fun input : ℕ × List
      (ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate)) =>
      decide (index < input.1)) :=
    (Measurable.of_discrete (f := fun n : ℕ => decide (index < n))).comp measurable_fst
  have hset : {input : ℕ × List
      (ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate)) |
      ∃ index, decide (index < input.1) = true ∧
        upWrongCodeAt input.2 index = true} =
      ⋃ index : ℕ, {input | decide (index < input.1) = true} ∩
        {input | upWrongCodeAt input.2 index = true} := by
    ext input
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
  have hmeas : MeasurableSet {input : ℕ × List
      (ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate)) |
      ∃ index, index < input.1 ∧ upWrongCodeAt input.2 index = true} := by
    have hmeasBool : MeasurableSet {input : ℕ × List
        (ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate)) |
        ∃ index, decide (index < input.1) = true ∧
          upWrongCodeAt input.2 index = true} := by
      rw [hset]
      exact MeasurableSet.iUnion fun index =>
        (hlt index (measurableSet_singleton true)).inter
          (hbad index (measurableSet_singleton true))
    simpa only [decide_eq_true_eq] using hmeasBool
  have htrueSet : {input : ℕ × List
      (ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate)) |
      upWrongPrefixCode input.1 input.2 = true} =
      {input | ∃ index, index < input.1 ∧ upWrongCodeAt input.2 index = true} := by
    ext input
    exact upWrongPrefixCode_true_iff_indexed input.1 input.2
  apply FollowerDownMeasurability.measurable_of_countable_fibers
  intro bit
  cases bit
  · have hfalseSet : {input : ℕ × List
        (ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate)) |
        upWrongPrefixCode input.1 input.2 = false} =
        {input | upWrongPrefixCode input.1 input.2 = true}ᶜ := by
      ext input
      cases upWrongPrefixCode input.1 input.2 <;> simp
    rw [hfalseSet, htrueSet]
    exact hmeas.compl
  · rw [htrueSet]
    exact hmeas

/-- Literal UP-only diagnostic over the first `prefixCount` actual records of
the complete corrected physical suffix. -/
def generatedUpWrongSuffixPrefixCode
    (r : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (prefixCount : ℕ) (source : SourceInput p) : Bool :=
  (ReferenceCompletePhysicalHistory.completeSuffixRecords r source rewards C_star C_h).take
    prefixCount |>.any (upWrongRecordFlag (rate := r))

/-- The original-source event that this exact complete-suffix prefix contains
a saved wrong UP diagnostic. -/
def generatedUpWrongSuffixPrefixEvent
    (r : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (prefixCount : ℕ) : Set (SourceInput p) :=
  {source | generatedUpWrongSuffixPrefixCode r rewards C_star C_h prefixCount source = true}

/-- Boolean membership is exactly an actual retained UP wrong-unique flag in
the same complete-suffix prefix. -/
theorem generatedUpWrongSuffixPrefixEvent_true_iff
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (prefixCount : ℕ) (source : SourceInput p) :
    source ∈ generatedUpWrongSuffixPrefixEvent (r := rate) rewards C_star C_h prefixCount ↔
      ∃ record ∈
        (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h).take
          prefixCount,
        ∃ diagnostic, record.output.coordinator.up = some diagnostic ∧
          diagnostic.wrongUniqueAccepted = true := by
  change generatedUpWrongSuffixPrefixCode (r := rate) rewards C_star C_h prefixCount source = true ↔ _
  unfold generatedUpWrongSuffixPrefixCode
  rw [List.any_eq_true]
  constructor
  · rintro ⟨record, hrecord, hflag⟩
    cases hdiag : record.output.coordinator.up with
    | none => simp [upWrongRecordFlag, hdiag] at hflag
    | some diagnostic =>
        simp only [upWrongRecordFlag, hdiag, Option.elim_some] at hflag
        exact ⟨record, hrecord, diagnostic, hdiag, hflag⟩
  · rintro ⟨record, hrecord, diagnostic, hdiag, hwrong⟩
    exact ⟨record, hrecord, by simp [upWrongRecordFlag, hdiag, hwrong]⟩

/-- The literal Boolean readout is true exactly when the retained output has
an UP diagnostic whose stored receiver bit is true. -/
theorem upWrongRecordFlag_true_iff
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) :
    upWrongRecordFlag record = true ↔
      ∃ diagnostic, record.output.coordinator.up = some diagnostic ∧
        diagnostic.wrongUniqueAccepted = true := by
  cases hdiagnostic : record.output.coordinator.up with
  | none => simp [upWrongRecordFlag, hdiagnostic]
  | some diagnostic => simp [upWrongRecordFlag, hdiagnostic]

private theorem upTailLedger_success
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ)
    (ledgerStarted : ReferenceActivePhysicalStep.Ledger rate)
    (htail : ReferenceCoordinatorUpPhysicalCall.tailLedger? prepared payload ledger started weights =
      some ledgerStarted) :
    ∃ recording : CoordinatorRecordingOperation.Output p,
      CoordinatorRecorderComplementBridge.run
        (ReferenceActivePhysicalStep.collectionRecordingInput prepared payload started weights) =
          some recording ∧
      CoordinatorCollectionLedger.startRound ledger (x.time.val + 1)
        (ReferenceActivePhysicalStep.collectionEnabled ledger x.time)
        (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) =
          .success ledgerStarted := by
  classical
  let recordingInput := CoordinatorRecorderComplementBridge.run
    (ReferenceActivePhysicalStep.collectionRecordingInput prepared payload started weights)
  cases hrecording : recordingInput with
  | none => simp [ReferenceCoordinatorUpPhysicalCall.tailLedger?, recordingInput, hrecording] at htail
  | some recording =>
      cases hstart : CoordinatorCollectionLedger.startRound ledger (x.time.val + 1)
          (ReferenceActivePhysicalStep.collectionEnabled ledger x.time)
          (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) with
      | invalid => simp [ReferenceCoordinatorUpPhysicalCall.tailLedger?, recordingInput,
          hrecording, hstart] at htail
      | rejected rejectedLedger =>
          simp [ReferenceCoordinatorUpPhysicalCall.tailLedger?, recordingInput,
            hrecording, hstart] at htail
      | success actual =>
          have heq : actual = ledgerStarted := by
            have hsome : some actual = some ledgerStarted := by
              simpa [ReferenceCoordinatorUpPhysicalCall.tailLedger?, recordingInput,
                hrecording, hstart] using htail
            exact Option.some.inj hsome
          subst actual
          exact ⟨recording, by simpa [recordingInput] using hrecording, hstart⟩

/-- A retained UP diagnostic is the diagnostic returned by the actual checked
receiver call that `collectionPostChoice` made at its real site ledger. -/
private theorem retainedUpDiagnostic_actual_receiver
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (diagnostic : ReferenceActivePhysicalStep.UpDiagnostic p rate)
    (hdiagnostic : record.output.coordinator.up = some diagnostic) :
    ∃ ledger, ReferenceCoordinatorUpPhysicalCall.siteLedger?
        (x := record.input) = some ledger ∧
      (ReferenceActivePhysicalStep.receiveUp
        (ReferenceActivePhysicalStep.prepare record.input) ledger).diagnostic = some diagnostic := by
  classical
  have hstep : record.output.coordinator.up =
      (ReferenceActivePhysicalStep.prepare record.input).observeCoordinator.up := by
    rw [record.output_eq]
    rfl
  have hrecorddiag := hdiagnostic
  rw [hstep] at hdiagnostic
  let x := record.input
  let prepared := ReferenceActivePhysicalStep.prepare x
  obtain ⟨siteLedger, hsite, _, _, _⟩ :=
    ReferenceCoordinatorUpPhysicalCall.record_retained_up_input record diagnostic hrecorddiag
  cases hcoord : prepared.coordinator with
  | first outcome =>
      cases outcome <;>
        simp [ReferenceCoordinatorUpPhysicalCall.siteLedger?, prepared, x, hcoord] at hsite
  | live registers owned base outcome =>
      cases outcome with
      | clockFailure failure _ =>
          simp [ReferenceCoordinatorUpPhysicalCall.siteLedger?, prepared, x, hcoord] at hsite
      | initializerFailure dispatched _ _ _ =>
          simp [ReferenceCoordinatorUpPhysicalCall.siteLedger?, prepared, x, hcoord] at hsite
      | localFailure dispatched _ reason =>
          simp [ReferenceCoordinatorUpPhysicalCall.siteLedger?, prepared, x, hcoord] at hsite
      | continuingChosen dispatched startRoundEq continuation selected =>
          simp [ReferenceCoordinatorUpPhysicalCall.siteLedger?, prepared, x, hcoord] at hsite
      | cutoffChosen dispatched hstart ledger hinit hledger hdomain hclock hpending
          hnoassignment selected =>
          by_cases hsel : ReferenceActivePhysicalStep.DispatchCut.selection
              (.live registers owned base
                (.cutoffChosen dispatched hstart ledger hinit hledger hdomain hclock
                  hpending hnoassignment selected)) = none
          · simp [ReferenceCoordinatorUpPhysicalCall.siteLedger?, prepared, x, hcoord, hsel] at hsite
          · let payload := registers.payload
            let baseLedger := ReferenceActivePhysicalStep.sharedLedger ledger
            let started := dispatched.startResult
            let weights :=
              (ReferenceActivePhysicalStep.liveRegistersAt registers x.time).complementWeights
            have heq := ReferenceActivePhysicalStep.observeCoordinator_live_equation
              prepared registers owned base
              (.cutoffChosen dispatched hstart ledger hinit hledger hdomain hclock
                hpending hnoassignment selected) hcoord
            rw [heq, ite_eq_right hsel] at hdiagnostic
            change (ReferenceActivePhysicalStep.collectionPostChoice prepared payload
              baseLedger started weights).up = some diagnostic at hdiagnostic
            have htail : ReferenceCoordinatorUpPhysicalCall.tailLedger? prepared payload
                baseLedger started weights = some siteLedger := by
              simpa [ReferenceCoordinatorUpPhysicalCall.siteLedger?, prepared, x, hcoord, hsel,
                payload, baseLedger, started, weights] using hsite
            obtain ⟨recording, hrecording, hstartRound⟩ :=
              upTailLedger_success x prepared payload baseLedger started weights siteLedger htail
            have hpost := ReferenceActivePhysicalStep.collectionPostChoice_after_start
              prepared payload baseLedger started weights recording siteLedger hrecording hstartRound
            have hreceiver :
                (ReferenceActivePhysicalStep.receiveUp prepared siteLedger).diagnostic =
                  some diagnostic := by
              rw [hpost, ReferenceActiveAffinePositiveTest.collectionFinish_up] at hdiagnostic
              exact hdiagnostic
            refine ⟨siteLedger, ?_, hreceiver⟩
            simpa [ReferenceCoordinatorUpPhysicalCall.siteLedger?, prepared, x, hcoord, hsel,
              payload, baseLedger, started, weights] using htail
  | collection payload ledger clock cutoff outcome =>
      cases outcome with
      | clockFailure failure _ =>
          simp [ReferenceCoordinatorUpPhysicalCall.siteLedger?, prepared, x, hcoord] at hsite
      | localFailure started _ _ =>
          simp [ReferenceCoordinatorUpPhysicalCall.siteLedger?, prepared, x, hcoord] at hsite
      | coreFailure core started _ _ =>
          simp [ReferenceCoordinatorUpPhysicalCall.siteLedger?, prepared, x, hcoord] at hsite
      | laterReconstructionFailure core consistent started _ instruction _ _ =>
          simp [ReferenceCoordinatorUpPhysicalCall.siteLedger?, prepared, x, hcoord] at hsite
      | laterPrefixFailure core consistent started _ instruction _ _ _ =>
          simp [ReferenceCoordinatorUpPhysicalCall.siteLedger?, prepared, x, hcoord] at hsite
      | laterOrientationFailure core consistent started _ instruction _ _ =>
          simp [ReferenceCoordinatorUpPhysicalCall.siteLedger?, prepared, x, hcoord] at hsite
      | laterChoiceFailure core consistent started startRoundEq instruction assignmentStartEq
          output localEq clockData installed reason =>
          simp [ReferenceCoordinatorUpPhysicalCall.siteLedger?, prepared, x, hcoord] at hsite
      | laterChosen core consistent started startRoundEq instruction assignmentStartEq output
          localEq clockData installed selected =>
          simp [ReferenceCoordinatorUpPhysicalCall.siteLedger?, prepared, x, hcoord] at hsite
      | continuing core snapshot boundary scores =>
          by_cases hsel : ReferenceActivePhysicalStep.DispatchCut.selection
              (.collection payload ledger clock cutoff
                (.continuing core snapshot boundary scores)) = none
          · simp [ReferenceCoordinatorUpPhysicalCall.siteLedger?, prepared, x, hcoord, hsel] at hsite
          · let source := ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff
            let weights := CoordinatorCollectionInteractive.PreObservationInputs.weights source
              snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq
            have heq := ReferenceActivePhysicalStep.observeCoordinator_collection_equation
              prepared payload ledger clock cutoff (.continuing core snapshot boundary scores) hcoord
            rw [heq, ite_eq_right hsel] at hdiagnostic
            change (ReferenceActivePhysicalStep.collectionPostChoice prepared payload ledger
              snapshot.clockStarted weights).up = some diagnostic at hdiagnostic
            have htail : ReferenceCoordinatorUpPhysicalCall.tailLedger? prepared payload
                ledger snapshot.clockStarted weights = some siteLedger := by
              simpa [ReferenceCoordinatorUpPhysicalCall.siteLedger?, prepared, x, hcoord, hsel,
                source, weights] using hsite
            obtain ⟨recording, hrecording, hstartRound⟩ :=
              upTailLedger_success x prepared payload ledger snapshot.clockStarted weights
                siteLedger htail
            have hpost := ReferenceActivePhysicalStep.collectionPostChoice_after_start
              prepared payload ledger snapshot.clockStarted weights recording siteLedger
              hrecording hstartRound
            have hreceiver :
                (ReferenceActivePhysicalStep.receiveUp prepared siteLedger).diagnostic =
                  some diagnostic := by
              rw [hpost, ReferenceActiveAffinePositiveTest.collectionFinish_up] at hdiagnostic
              exact hdiagnostic
            refine ⟨siteLedger, ?_, hreceiver⟩
            simpa [ReferenceCoordinatorUpPhysicalCall.siteLedger?, prepared, x, hcoord, hsel,
              source, weights] using htail
  | invalidCollectionCutoff =>
      simp [ReferenceCoordinatorUpPhysicalCall.siteLedger?, prepared, x, hcoord] at hsite
  | dagger =>
      simp [ReferenceCoordinatorUpPhysicalCall.siteLedger?, prepared, x, hcoord] at hsite

/-- Inverting the actual receiver diagnostic shows that its saved wrong-UP
bit records a unique raw word, local acceptance, and mismatch with the actual
prepared UP offer. -/
theorem savedWrongUp_fields_of_actualReceiver
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (diagnostic : ReferenceActivePhysicalStep.UpDiagnostic p rate)
    (hdiagnostic : record.output.coordinator.up = some diagnostic)
    (hwrong : diagnostic.wrongUniqueAccepted = true) :
    ∃ word, diagnostic.raw = some word ∧ diagnostic.locallyAccepted = true ∧
      some word ≠ diagnostic.expected := by
  obtain ⟨ledger, hsite, hreceiver⟩ :=
    retainedUpDiagnostic_actual_receiver (rate := rate) record diagnostic hdiagnostic
  let prepared := ReferenceActivePhysicalStep.prepare record.input
  let inputs := ReferenceActivePhysicalStep.upInputs prepared ledger
  let input := ReferenceUpReception.receptionInputAtRow rate record.input.row inputs record.input.time
  let sender := prepared.followers.followers
    (ReferenceActivePhysicalStep.upSenderIndex record.input)
  have hcheck : CoordinatorUpReception.receptionInputCheck input = true := by
    have hinput := ReferenceCoordinatorUpPhysicalCall.record_retained_up_input record diagnostic
      hdiagnostic
    obtain ⟨ledger', hsite', hcheck, hidentity, _⟩ := hinput
    have heq : ledger' = ledger := Option.some.inj (hsite'.symm.trans hsite)
    subst ledger'
    simpa [ReferenceCoordinatorUpPhysicalCall.actualUpInput,
      ReferenceCoordinatorUpPhysicalCall.siteLedger?, prepared, inputs, input] using hcheck
  have hrow : sender.row = record.input.row := (prepared.follower_alignment _).1
  have hplayer : sender.follower = input.selectedFollower :=
    (prepared.follower_alignment _).2.1
  have htime : sender.time = input.time := (prepared.follower_alignment _).2.2.1
  have htimeInput : inputs.2.2.1 = record.input.time := rfl
  have hcheckCond : CoordinatorUpReception.receptionInputCheck
      (CoordinatorUpMeasurability.receptionInputAtRow record.input.row inputs
        record.input.time) = true := by
    change CoordinatorUpReception.receptionInputCheck input = true
    exact hcheck
  have hactualBit := congrArg
    (Option.map ReferenceActivePhysicalStep.UpDiagnostic.wrongUniqueAccepted) hreceiver
  have hbit :
      ReferenceUpReception.wrongUniqueAndLocalAcceptanceAtRow rate record.input.row inputs
        record.input.time sender hrow hplayer htime htimeInput = true := by
    have hmap := hactualBit
    simp [ReferenceActivePhysicalStep.receiveUp, prepared, inputs, input, hcheck] at hmap
    simpa [hwrong] using hmap
  obtain ⟨word, parsed, hraw, hparsed, haccept, hmismatch⟩ :=
    (ReferenceUpReception.wrongUniqueAndLocalAcceptanceAtRow_eq_true_iff
      rate record.input.row inputs record.input.time sender hrow hplayer htime htimeInput).1 hbit
  have hfields := ReferenceGeneratedUpBatchCalendar.record_up_executed_fields
    record diagnostic hdiagnostic
  obtain ⟨ledger', hsite', hcheck', hinput', hafter', hraw', hparsed', hlocal', hmatch', hexpected,
    _, _, _, _⟩ := hfields
  have heqLedger : ledger' = ledger := Option.some.inj (hsite'.symm.trans hsite)
  subst ledger'
  have hinputEq : diagnostic.input = input := by
    simpa [ReferenceCoordinatorUpPhysicalCall.actualUpInput, prepared, inputs, input] using hinput'
  have hrawDiag : diagnostic.raw = some word := by
    rw [hraw', hinputEq]
    exact hraw
  have hparsedInput : ReferenceUpReception.rawParsedOutput rate input = some parsed := by
    unfold ReferenceUpReception.rawParsedOutput
    rw [hraw]
    exact hparsed
  have hlocalDiag : diagnostic.locallyAccepted = true := by
    rw [hlocal']
    rw [hinputEq]
    exact (ReferenceUpReception.rawParsedLocalAcceptance_eq_true_iff rate input).2
      ⟨parsed, hparsedInput, haccept⟩
  have hexpectedEq : diagnostic.expected =
      ReferenceUpReception.currentOfferWord rate record.input.row input.selectedFollower
        input.time sender hrow hplayer htime := by
    have hmap := congrArg (Option.map ReferenceActivePhysicalStep.UpDiagnostic.expected) hreceiver
    have hcurrent :
        ReferenceUpReception.currentOfferWord rate record.input.row input.selectedFollower
          input.time sender hrow hplayer htime = diagnostic.expected := by
      have hparts :
          CoordinatorUpReception.receptionInputCheck input = true ∧
            ReferenceUpReception.currentOfferWord rate record.input.row input.selectedFollower
              input.time sender hrow hplayer htime = diagnostic.expected := by
        simpa [ReferenceActivePhysicalStep.receiveUp, ReferenceActivePhysicalStep.upExpected,
          ReferenceActivePhysicalStep.upSenderIndex, prepared, inputs, input, sender,
          ReferenceUpReception.receptionInputAtRow,
          CoordinatorUpMeasurability.receptionInputAtRow,
          CoordinatorUpMeasurability.receptionInputAtControl, htimeInput, hcheckCond] using hmap
      exact hparts.2
    exact hcurrent.symm
  have hmismatch' : some word ≠
      ReferenceUpReception.currentOfferWord rate record.input.row input.selectedFollower
        input.time sender hrow hplayer htime := by
    simpa [input, ReferenceUpReception.receptionInputAtRow,
      CoordinatorUpMeasurability.receptionInputAtRow,
      CoordinatorUpMeasurability.receptionInputAtControl] using hmismatch
  exact ⟨word, hrawDiag, hlocalDiag, by rw [hexpectedEq]; exact hmismatch'⟩

/-- The retained receiver bit also follows from coherent actual raw, local,
and wrong-offer fields. Arbitrary diagnostic records cannot satisfy this
converse: the proof uses the physical output equality and receiver call. -/
private theorem actualReceiver_wrongUnique_of_fields
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (diagnostic : ReferenceActivePhysicalStep.UpDiagnostic p rate)
    (hdiagnostic : record.output.coordinator.up = some diagnostic)
    (word : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (hraw : diagnostic.raw = some word)
    (hlocallyAccepted : diagnostic.locallyAccepted = true)
    (hmismatch : some word ≠ diagnostic.expected) :
    diagnostic.wrongUniqueAccepted = true := by
  obtain ⟨ledger, hsite, hreceiver⟩ :=
    retainedUpDiagnostic_actual_receiver (rate := rate) record diagnostic hdiagnostic
  let prepared := ReferenceActivePhysicalStep.prepare record.input
  let inputs := ReferenceActivePhysicalStep.upInputs prepared ledger
  let input := ReferenceUpReception.receptionInputAtRow rate record.input.row inputs record.input.time
  let sender := prepared.followers.followers
    (ReferenceActivePhysicalStep.upSenderIndex record.input)
  have hcheck : CoordinatorUpReception.receptionInputCheck input = true := by
    have hinput := ReferenceCoordinatorUpPhysicalCall.record_retained_up_input record diagnostic
      hdiagnostic
    obtain ⟨ledger', hsite', hcheck, _, _⟩ := hinput
    have heq : ledger' = ledger := Option.some.inj (hsite'.symm.trans hsite)
    subst ledger'
    simpa [ReferenceCoordinatorUpPhysicalCall.actualUpInput,
      ReferenceCoordinatorUpPhysicalCall.siteLedger?, prepared, inputs, input] using hcheck
  have hrow : sender.row = record.input.row := (prepared.follower_alignment _).1
  have hplayer : sender.follower = input.selectedFollower :=
    (prepared.follower_alignment _).2.1
  have htime : sender.time = input.time := (prepared.follower_alignment _).2.2.1
  have htimeInput : inputs.2.2.1 = record.input.time := rfl
  have hfields := ReferenceGeneratedUpBatchCalendar.record_up_executed_fields
    record diagnostic hdiagnostic
  obtain ⟨ledger', hsite', _, hinput', _, hraw', _, hlocal', _, _, _, _, _, _⟩ := hfields
  have heqLedger : ledger' = ledger := Option.some.inj (hsite'.symm.trans hsite)
  subst ledger'
  have hinputEq : diagnostic.input = input := by
    simpa [ReferenceCoordinatorUpPhysicalCall.actualUpInput, prepared, inputs, input] using hinput'
  have hinputEq' : input = diagnostic.input := hinputEq.symm
  have htransitionRaw :
      (CoordinatorUpReception.decoderTransition input).2 = some word :=
    (congrArg (fun x => (CoordinatorUpReception.decoderTransition x).2) hinputEq').trans
      (hraw'.symm.trans hraw)
  have hparsedLocal : ReferenceUpReception.rawParsedLocalAcceptance rate input = true := by
    rw [hlocal'] at hlocallyAccepted
    exact (congrArg (ReferenceUpReception.rawParsedLocalAcceptance rate) hinputEq').trans
      hlocallyAccepted
  obtain ⟨parsed, hparsed, haccept⟩ :=
    (ReferenceUpReception.rawParsedLocalAcceptance_eq_true_iff rate input).1 hparsedLocal
  have hexpectedEq : diagnostic.expected =
      ReferenceUpReception.currentOfferWord rate record.input.row input.selectedFollower
        input.time sender hrow hplayer htime := by
    have hmap := congrArg (Option.map ReferenceActivePhysicalStep.UpDiagnostic.expected) hreceiver
    have hcheckCond : CoordinatorUpReception.receptionInputCheck
        (CoordinatorUpMeasurability.receptionInputAtRow record.input.row inputs
          record.input.time) = true := by
      change CoordinatorUpReception.receptionInputCheck input = true
      exact hcheck
    have hparts : CoordinatorUpReception.receptionInputCheck input = true ∧
        ReferenceUpReception.currentOfferWord rate record.input.row input.selectedFollower
          input.time sender hrow hplayer htime = diagnostic.expected := by
      simpa [ReferenceActivePhysicalStep.receiveUp, ReferenceActivePhysicalStep.upExpected,
        ReferenceActivePhysicalStep.upSenderIndex, prepared, inputs, input, sender,
        ReferenceUpReception.receptionInputAtRow,
        CoordinatorUpMeasurability.receptionInputAtRow,
        CoordinatorUpMeasurability.receptionInputAtControl, htimeInput, hcheckCond] using hmap
    exact hparts.2.symm
  have hmismatch' : some word ≠
      ReferenceUpReception.currentOfferWord rate record.input.row input.selectedFollower
        input.time sender hrow hplayer htime := by
    intro heq
    apply hmismatch
    rw [hexpectedEq]
    exact heq
  have hparsed' : CoordinatorUpReception.parseDecoderOutput (some word) = some parsed := by
    simpa [ReferenceUpReception.rawParsedOutput, htransitionRaw] using hparsed
  have hbit := (ReferenceUpReception.wrongUniqueAndLocalAcceptanceAtRow_eq_true_iff
    rate record.input.row inputs record.input.time sender hrow hplayer htime htimeInput).2
      ⟨word, parsed, htransitionRaw, hparsed', haccept, hmismatch'⟩
  have hflag : (ReferenceActivePhysicalStep.receiveUp prepared ledger).diagnostic.map
      ReferenceActivePhysicalStep.UpDiagnostic.wrongUniqueAccepted = some true := by
    simp [ReferenceActivePhysicalStep.receiveUp, prepared, inputs, input, sender, hcheck, hbit]
  rw [hreceiver] at hflag
  simpa using hflag

/-- Literal event membership is exactly a saved diagnostic produced by the
actual receiver, with raw output, ordinary local acceptance, and a wrong
actual offer. This equivalence excludes absent diagnostics and parse/local
rejections while retaining wrong candidates rejected only by a later filter. -/
theorem generatedUpWrongSuffixPrefixEvent_actual_fields
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (prefixCount : ℕ) (source : SourceInput p) :
    source ∈ generatedUpWrongSuffixPrefixEvent (r := rate) rewards C_star C_h prefixCount ↔
      ∃ record ∈
        (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h).take
          prefixCount,
        ∃ diagnostic, record.output.coordinator.up = some diagnostic ∧
          ∃ word, diagnostic.raw = some word ∧ diagnostic.locallyAccepted = true ∧
            some word ≠ diagnostic.expected := by
  rw [generatedUpWrongSuffixPrefixEvent_true_iff]
  constructor
  · rintro ⟨record, hrecord, diagnostic, hdiagnostic, hwrong⟩
    obtain ⟨word, hraw, hlocal, hmismatch⟩ :=
      savedWrongUp_fields_of_actualReceiver (rate := rate) record diagnostic hdiagnostic hwrong
    exact ⟨record, hrecord, diagnostic, hdiagnostic, word, hraw, hlocal, hmismatch⟩
  · rintro ⟨record, hrecord, diagnostic, hdiagnostic, word, hraw, hlocal, hmismatch⟩
    have hwrong := actualReceiver_wrongUnique_of_fields (rate := rate)
      record diagnostic hdiagnostic word hraw hlocal hmismatch
    exact ⟨record, hrecord, diagnostic, hdiagnostic, hwrong⟩

private theorem completeSuffix_record_upBankInvariant
    (source : SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hrecord : record ∈
      ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h) :
    ReferenceUpDecoderBankInvariant.upBankInvariant record.input.state := by
  let start := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
  have hlen := ReferenceCompletePhysicalHistory.completeSuffixRecords_length
    rate source rewards C_star C_h
  have hpositive : 0 <
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h).length :=
    List.length_pos_of_mem hrecord
  rw [hlen] at hpositive
  have hstartLt : start < p.T := by dsimp [start]; omega
  have hlaunchNone : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h ≠ none := by
    intro hnone
    have hstart := ReferenceCompletePhysicalHistory.correctedLaunch_none_start_eq_T
      rate source rewards C_star C_h hnone
    dsimp [start] at hstartLt
    omega
  obtain ⟨active, hlaunch⟩ : ∃ active,
      ReferenceCorrectedInitializationLaunch.correctedLaunch rate source rewards C_star C_h =
        some active := by
    cases h : ReferenceCorrectedInitializationLaunch.correctedLaunch rate source rewards C_star C_h with
    | none => exact (hlaunchNone h).elim
    | some active => exact ⟨active, rfl⟩
  have hmode := ReferenceCompletePhysicalHistory.activeMode_of_launch_eq_some
    rate source rewards C_star C_h active hlaunch
  have hrunRecords := ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
    rate source rewards C_star C_h active hlaunch
  have hstartLe := ReferenceCompletePhysicalHistory.physicalStart_le_T
    rate source rewards C_star C_h
  have hspan : start + (p.T - start) ≤ p.T := by
    dsimp [start] at hstartLe ⊢
    omega
  have hmemRun : record ∈
      (ReferenceActivePhysicalHorizon.run active source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start (p.T - start)
        hspan hmode).records := by
    rw [← hrunRecords]
    exact hrecord
  have hsome : (ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h).isSome = true := by
    rw [hlaunch]
    rfl
  have hcross := (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
    rate source rewards C_star C_h).mp hsome
  obtain ⟨actual, ⟨hactual, hcoord, hbank, _, _⟩, _⟩ :=
    ReferenceCorrectedInitializationLaunch.correctedLaunch_crossing_characterization
      rate source rewards C_star C_h hcross
  have hactive : active = actual := Option.some.inj (hlaunch.symm.trans hactual)
  subst active
  have hinitial : ReferenceUpDecoderBankInvariant.upBankInvariant actual := by
    simpa [ReferenceUpDecoderBankInvariant.upBankInvariant,
      ReferenceUpDecoderBankInvariant.coordinatorBankInvariant, hcoord, hbank] using
        (ReferenceUpDecoderBankInvariant.firstState_upBankInvariant
          actual.activations actual.followers)
  have hrecordInv := ReferenceUpDecoderBankInvariant.run_record_input_upBankInvariant
    actual source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
    start (p.T - start) hspan hmode hinitial
  exact hrecordInv record hmemRun

private theorem actualUpRawSome_implies_eligible
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (diagnostic : ReferenceActivePhysicalStep.UpDiagnostic p rate)
    (hdiagnostic : record.output.coordinator.up = some diagnostic)
    (i : Fin (p.m - 1)) (hselected : diagnostic.input.selectedFollower = i)
    (word : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (hraw : diagnostic.raw = some word)
    (hinvariant : ReferenceUpDecoderBankInvariant.upBankInvariant record.input.state) :
    AffineBatchDecoder.eligible (CoordinatorUpReception.roundInput diagnostic.input) ∧
      (record.input.state.upDecoderBank i).pending.length + 1 =
        AffineBatchDecoder.quota p ∧
      ReferenceActiveAffinePositiveTest.upPositive record.input = true := by
  obtain ⟨_, _, _, _, _, htransition, _, _, _, _, _, hbank, _, _⟩ :=
    ReferenceGeneratedUpBatchCalendar.record_up_executed_fields
      record diagnostic hdiagnostic
  have hsmall : (diagnostic.input.upDecoderBank i).pending.length <
      AffineBatchDecoder.quota p := by
    change ReferenceUpDecoderBankInvariant.coordinatorBankInvariant
      record.input.state.coordinator record.input.state.upDecoderBank at hinvariant
    have hwellFormed := hinvariant.1 i
    rw [← hbank] at hwellFormed
    exact hwellFormed.1
  let trace := CoordinatorUpReception.traceAt diagnostic.input
  have hstepOutput : AffineBatchDecoder.stepOutput p trace
      (diagnostic.input.upDecoderBank i) diagnostic.input.time = some word := by
    have htransition' : (CoordinatorUpReception.decoderTransition diagnostic.input).2 =
        some word := htransition.symm.trans hraw
    simpa [trace, hselected, CoordinatorUpReception.decoderTransition,
      CoordinatorUpReception.traceAt, AffineBatchDecoder.decodeStep] using htransition'
  have hdecoded := (AffineBatchDecoder.stepOutput_eq_some_iff p trace
    (diagnostic.input.upDecoderBank i) diagnostic.input.time word).mp hstepOutput
  have heligible : AffineBatchDecoder.eligible
      (CoordinatorUpReception.roundInput diagnostic.input) := by
    by_contra hnot
    have hnotTrace : ¬ AffineBatchDecoder.eligible (trace diagnostic.input.time) := by
      simpa [trace, CoordinatorUpReception.traceAt] using hnot
    have hnone : AffineBatchDecoder.positiveAt p trace diagnostic.input.time = [] := by
      simp [AffineBatchDecoder.positiveAt, hnotTrace]
    have hlength : ((diagnostic.input.upDecoderBank i).pending ++
        AffineBatchDecoder.positiveAt p trace diagnostic.input.time).length =
        (diagnostic.input.upDecoderBank i).pending.length := by
      rw [hnone, List.append_nil]
    omega
  have heligibleTrace : AffineBatchDecoder.eligible (trace diagnostic.input.time) := by
    simpa [trace, CoordinatorUpReception.traceAt] using heligible
  have hquota : (diagnostic.input.upDecoderBank i).pending.length + 1 =
      AffineBatchDecoder.quota p := by
    have hle : AffineBatchDecoder.quota p ≤
        (diagnostic.input.upDecoderBank i).pending.length + 1 := by
      simpa [AffineBatchDecoder.positiveAt, heligibleTrace] using hdecoded.1
    omega
  have hupPositive : ReferenceActiveAffinePositiveTest.upPositive record.input = true := by
    rw [ReferenceActiveAffinePositiveTest.record_upPositive record, hdiagnostic]
    simp [ReferenceActiveAffinePositiveTest.upDiagnosticPositive, heligible]
  exact ⟨heligible, by simpa only [hbank] using hquota, hupPositive⟩

private theorem upTail_fold_records_take
    (start : ℕ)
    (input : ReferenceActiveHorizonMeasurability.ActiveRunInput (p := p) (rate := rate) start)
    (entries : List (ReferenceActivePhysicalHorizon.CalendarEntry p start))
    (acc : ReferenceActivePhysicalHorizon.Run input.val.1) :
    ((entries.foldl (ReferenceActivePhysicalHorizon.foldRound input.val.1 input.val.2.1
      input.val.2.2.1 input.val.2.2.2 start input.property) acc).records).take
        acc.records.length = acc.records := by
  induction entries generalizing acc with
  | nil => simp only [List.foldl_nil, List.take_length]
  | cons entry rest ih =>
      let next := ReferenceActivePhysicalHorizon.foldRound input.val.1 input.val.2.1
        input.val.2.2.1 input.val.2.2.2 start input.property acc entry
      have hlen : acc.records.length ≤ next.records.length := by
        simp only [next, ReferenceActivePhysicalHorizon.foldRound,
          List.length_append, List.length_singleton]
        omega
      change ((rest.foldl _ next).records).take acc.records.length = acc.records
      rw [← Nat.min_eq_left hlen, ← List.take_take, ih]
      simp only [next, ReferenceActivePhysicalHorizon.foldRound,
        List.take_append, List.take_length, Nat.sub_self, List.take_zero, List.append_nil]

private theorem upTail_run_records_take (start count n : ℕ)
    (hspan : start + count ≤ p.T)
    (input : ReferenceActiveHorizonMeasurability.ActiveRunInput (p := p) (rate := rate) start)
    (hn : n ≤ count) :
    (ReferenceActiveHorizonMeasurability.runOfInput start n (by omega) input).records =
      (ReferenceActiveHorizonMeasurability.runOfInput start count hspan input).records.take n := by
  have hsplit := ReferenceActivePhysicalHorizon.run_append input.val.1 input.val.2.1
    input.val.2.2.1 input.val.2.2.2 start n (count - n) (by omega) input.property
  have htake := upTail_fold_records_take start input
    (ReferenceActivePhysicalHorizon.calendarEntries start (start + n) (count - n)
      (by omega) (by omega))
    (ReferenceActiveHorizonMeasurability.runOfInput start n (by omega) input)
  have hlen := ReferenceActivePhysicalHorizon.run_record_count input.val.1 input.val.2.1
    input.val.2.2.1 input.val.2.2.2 start n (by omega) input.property
  have hsplit' := hsplit
  simp only [Nat.add_sub_of_le hn] at hsplit'
  change _ = (ReferenceActivePhysicalHorizon.run input.val.1 input.val.2.1 input.val.2.2.1
    input.val.2.2.2 start count hspan input.property).records.take n
  rw [hsplit']
  simpa only [ReferenceActivePhysicalHorizon.foldCalendar,
    ReferenceActiveHorizonMeasurability.runOfInput, hlen] using htake.symm

private theorem upTail_originalSourceCurrentRecord_append
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (start : ℕ)
    (hstart : start ≤ t.val) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1))
    (z : ReferenceGeneratedUpBatchPrefixEvent.UpLaunchSource
      (rate := rate) rewards C_star C_h q t start i) :
    let input := ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
      (rate := rate) rewards C_star C_h q t start hstart control0 i z
    (ReferenceActiveHorizonMeasurability.runOfInput start (t.val - start + 1)
      (by omega) input).records =
      (ReferenceActiveHorizonMeasurability.runOfInput start (t.val - start)
        (by omega) input).records ++
        [ReferenceGeneratedUpPrefixPositiveHalf.originalSourceCurrentRecord
          (rate := rate) rewards C_star C_h q t start hstart control0 i z] := by
  dsimp only [ReferenceActiveHorizonMeasurability.runOfInput]
  rw [ReferenceActivePhysicalHorizon.run_successor_step]
  have hentry : (⟨start + (t.val - start), by omega, by omega⟩ :
      ReferenceActivePhysicalHorizon.CalendarEntry p start) = ⟨t.val, hstart, t.isLt⟩ :=
    Subtype.ext (Nat.add_sub_of_le hstart)
  rw [hentry]
  rfl

private theorem upTail_originalSourceCurrentRecord_get
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (start : ℕ)
    (hstart : start ≤ t.val) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1))
    (z : ReferenceGeneratedUpBatchPrefixEvent.UpLaunchSource
      (rate := rate) rewards C_star C_h q t start i) :
    let input := ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
      (rate := rate) rewards C_star C_h q t start hstart control0 i z
    (ReferenceActiveHorizonMeasurability.runOfInput start (p.T - start)
      (by omega) input).records[t.val - start]? =
        some (ReferenceGeneratedUpPrefixPositiveHalf.originalSourceCurrentRecord
          (rate := rate) rewards C_star C_h q t start hstart control0 i z) := by
  dsimp only
  let input := ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
    (rate := rate) rewards C_star C_h q t start hstart control0 i z
  have hsucc := upTail_run_records_take start (p.T - start) (t.val - start + 1)
    (by omega) input (by omega)
  rw [upTail_originalSourceCurrentRecord_append] at hsucc
  have hlen : (ReferenceActiveHorizonMeasurability.runOfInput start (t.val - start)
      (by omega) input).records.length = t.val - start :=
    ReferenceActivePhysicalHorizon.run_record_count _ _ _ _ _ _ _ _
  change (ReferenceActiveHorizonMeasurability.runOfInput start (t.val - start)
    (by omega) input).records ++ [_] = _ at hsucc
  rw [← List.getElem?_take_of_succ, ← hsucc,
    List.getElem?_append_right (by omega), hlen]
  simp only [Nat.sub_self, List.getElem?_cons_zero]

private theorem upTail_run_record_index (start count : ℕ) (hspan : start + count ≤ p.T)
    (input : ReferenceActiveHorizonMeasurability.ActiveRunInput (p := p) (rate := rate) start)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hmem : record ∈
      (ReferenceActiveHorizonMeasurability.runOfInput start count hspan input).records) :
    ∃ index, index < count ∧
      (ReferenceActiveHorizonMeasurability.runOfInput start count hspan input).records[index]? =
        some record ∧ record.input.time.val = start + index := by
  obtain ⟨index, hget⟩ := List.mem_iff_getElem?.mp hmem
  obtain ⟨hindex, _⟩ := List.getElem?_eq_some_iff.mp hget
  have hlen := ReferenceActivePhysicalHorizon.run_record_count input.val.1 input.val.2.1
    input.val.2.2.1 input.val.2.2.2 start count hspan input.property
  have hindexCount : index < count := by
    change index < (ReferenceActivePhysicalHorizon.run _ _ _ _ _ _ _ _).records.length at hindex
    omega
  have htimes := ReferenceActivePhysicalHorizon.run_time_values input.val.1 input.val.2.1
    input.val.2.2.1 input.val.2.2.2 start count hspan input.property
  have htime := congrArg (fun xs : List ℕ => xs[index]?) htimes
  dsimp only [ReferenceActiveHorizonMeasurability.runOfInput] at hget
  rw [List.getElem?_map, hget] at htime
  have htime' : record.input.time.val = start + index := by
    simpa only [ReferenceActivePhysicalHorizon.calendar, List.getElem?_range', hindexCount,
      ↓reduceIte, Nat.one_mul, Option.map_some, Option.some.injEq] using htime
  exact ⟨index, hindexCount, hget, htime'⟩

/-- A wrong UP record in the literal complete-suffix prefix belongs to the
actual source launch run and is the same record as U's original-source
current record. The final conjunct retains U's full alpha and batch witness. -/
theorem actualSuffix_wrongUp_record_survival
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (prefixCount : ℕ) (source : SourceInput p)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hrecord : record ∈
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h).take
        prefixCount)
    (diagnostic : ReferenceActivePhysicalStep.UpDiagnostic p rate)
    (hdiagnostic : record.output.coordinator.up = some diagnostic)
    (word : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (hraw : diagnostic.raw = some word)
    (hlocallyAccepted : diagnostic.locallyAccepted = true)
    (hmismatch : some word ≠ diagnostic.expected) :
    ∃ (q : Fin (M p)) (start : ℕ) (i : Fin (p.m - 1))
      (hstartTime : start ≤ record.input.time.val)
      (_hselectedFollower : diagnostic.input.selectedFollower = i),
      source ∈ ReferenceGeneratedAffineHashHalf.generatedLaunchBranch (rate := rate)
        rewards C_star C_h q record.input.time (1, i) start ∧
      ∃ z : ReferenceGeneratedUpBatchPrefixEvent.UpLaunchSource
          (rate := rate) rewards C_star C_h q record.input.time start i,
        z.1 = source ∧
        record = ReferenceGeneratedUpPrefixPositiveHalf.originalSourceCurrentRecord
          (rate := rate) rewards C_star C_h q record.input.time start
          hstartTime control0 i z ∧
          let input := ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
            (rate := rate) rewards C_star C_h q record.input.time start hstartTime control0 i z
          let full := ReferenceActiveHorizonMeasurability.runOfInput start (p.T - start)
            (by omega) input
          let current := ReferenceGeneratedUpPrefixPositiveHalf.originalSourceCurrentRecord
            (rate := rate) rewards C_star C_h q record.input.time start hstartTime control0 i z
          let batch := (current.input.state.upDecoderBank i).pending ++
            [AffineBatchDecoder.entry p
              (ReferenceCoordinatorUpDecoderReplay.constantInputTrace diagnostic.input)
              diagnostic.input.time]
          ∃ alpha, start ≤ alpha ∧ alpha ≤ record.input.time.val ∧
            upBatchBirth i start alpha input.val.1
              (full.records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence) ∧
            let kept := (ReferenceGeneratedUpSourceCalendar.originalSourceTests
              (rate := rate) rewards C_star C_h q record.input.time start hstartTime
              control0 alpha i z).take (AffineBatchDecoder.quota p)
            kept.length = AffineBatchDecoder.quota p ∧
            kept.map (fun test => (test.time, test.sample)) =
              batch.map (fun entry => (entry.time.val, entry.sample)) ∧
            (∀ test ∈ kept, test.sent ≠ some word) ∧
            z.1 ∈ ReferenceGeneratedUpSourceCalendar.upSourceSurvivalEvent (rate := rate)
              rewards C_star C_h q control0 alpha word i (AffineBatchDecoder.quota p) := by
  classical
  have hrecordComplete : record ∈
      ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h :=
    List.mem_of_mem_take hrecord
  have hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h ≠ none := by
    intro hnone
    simp [ReferenceCompletePhysicalHistory.completeSuffixRecords, hnone] at hrecordComplete
  have hsome : (ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h).isSome = true :=
    Option.ne_none_iff_isSome.mp hlaunch
  have hcross := (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
    rate source rewards C_star C_h).mp hsome
  let start := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
  have hstartLe := ReferenceCompletePhysicalHistory.physicalStart_le_T
    rate source rewards C_star C_h
  let fiber : ReferenceGeneratedDownAmbiguityMeasurability.GeneratedLaunchFiber
      (rate := rate) rewards C_star C_h start := by
    refine ⟨source, ?_⟩
    constructor
    · simpa [ReferenceGeneratedDownAmbiguityMeasurability.generatedLaunchFiberSet,
        ReferenceCompletePhysicalHistory.generatedBoundary,
        ReferenceCompletePhysicalHistory.generatedInput] using hcross
    · rfl
  let runInput := ReferenceGeneratedDownAmbiguityMeasurability.generatedActiveRunInput
    (rate := rate) rewards C_star C_h start fiber
  have hspan : start + (p.T - start) ≤ p.T := by omega
  have hrunRecords := ReferenceGeneratedDownAmbiguityMeasurability.generatedRun_records_eq_completeSuffixRecords_take
    (rate := rate) rewards C_star C_h start (p.T - start) (by omega) fiber
  have hlen := ReferenceCompletePhysicalHistory.completeSuffixRecords_length
    rate source rewards C_star C_h
  rw [fiber.2.2] at hlen
  have htake :
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h).take
        (p.T - start) =
      ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h :=
    List.take_of_length_le (Nat.le_of_eq hlen)
  rw [htake] at hrunRecords
  have hrecordRun : record ∈
      (ReferenceActiveHorizonMeasurability.runOfInput start (p.T - start) hspan runInput).records := by
    rw [hrunRecords]
    exact hrecordComplete
  obtain ⟨index, hindex, hgetRun, htime⟩ :=
    upTail_run_record_index start (p.T - start) hspan runInput record hrecordRun
  have hstartTime : start ≤ record.input.time.val := by omega
  let q : Fin (M p) := ActualInitializationPhysicalStep.selectedRowIndex p source
  have hrunFields := ReferenceActivePhysicalHorizon.run_record_inputs
    runInput.val.1 runInput.val.2.1 runInput.val.2.2.1 runInput.val.2.2.2 start
    (p.T - start) hspan runInput.property record hrecordRun
  have hrows : record.input.rows = source.1.2 := by
    have hrunRows : runInput.val.2.1 = source.1.2 := by
      rw [ReferenceGeneratedDownAmbiguityMeasurability.generatedActiveRunInput_val]
    exact hrunFields.1.trans hrunRows
  have hselected : record.input.selected = q := by
    rw [hrunFields.2.1, ReferenceGeneratedDownAmbiguityMeasurability.generatedActiveRunInput_val]
  let i : Fin (p.m - 1) := diagnostic.input.selectedFollower
  have hinvariant := completeSuffix_record_upBankInvariant
    (rate := rate) source rewards C_star C_h record hrecordComplete
  have ⟨heligible, hquota, hpositive⟩ := actualUpRawSome_implies_eligible
    (rate := rate) record diagnostic hdiagnostic i rfl word hraw hinvariant
  obtain ⟨ledger, _, _, _, _, _, hselectedInput, _, hslot, _, hgate, _, _, _⟩ :=
    ReferenceCoordinatorUpPhysicalCall.record_retained_up_input_fields
      record diagnostic hdiagnostic
  have hselectedGate :
      (CoordinatorUpReception.roundInput diagnostic.input).selected = true := heligible.1
  rw [hgate] at hselectedGate
  have hup : diagnostic.input.slot = PublicDiscreteDraws.upSlot :=
    (of_decide_eq_true hselectedGate).2.1
  let slice := (record.input.rows record.input.selected).2 record.input.time
  have hfollower : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K slice.1 = i :=
    (CoordinatorUpMeasurability.selectedFollowerIndex_eq_draw slice).symm.trans
      (hselectedInput.symm.trans rfl)
  have hchannel : ReferenceSelectedAffinePairLaw.selectedChannel p slice.1 = some (1, i) := by
    rw [ReferenceSelectedAffinePairLaw.selectedChannel_of_up p slice.1
      (hslot.symm.trans hup), hfollower]
    rfl
  have hchannelSource : ReferenceSelectedAffinePairLaw.selectedChannel p
      ((source.1.2 q).2 record.input.time).1 = some (1, i) := by
    simpa [slice, hrows, hselected] using hchannel
  have hrowIndex : PrivateSourceStreams.coordinatorIndex p source.2.1.2 = q := by
    simp [q, ActualInitializationPhysicalStep.selectedRowIndex]
  have hselector := (ReferenceSelectedAffinePairLaw.selector_eq_iff p q record.input.time
    (1, i) source).2 ⟨hrowIndex, hchannelSource⟩
  have hbranch : source ∈ ReferenceGeneratedAffineHashHalf.generatedLaunchBranch
      (rate := rate) rewards C_star C_h q record.input.time (1, i) start := by
    refine ⟨hselector, hcross, ?_⟩
    simp [start, ReferenceCompletePhysicalHistory.physicalStart,
      ReferenceCompletePhysicalHistory.generatedBoundary,
      ReferenceCompletePhysicalHistory.generatedInput]
  have hstartTime' : start ≤ record.input.time.val := hstartTime
  let z : ReferenceGeneratedUpBatchPrefixEvent.UpLaunchSource
      (rate := rate) rewards C_star C_h q record.input.time start i := ⟨source, hbranch⟩
  let originalInput := ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
    (rate := rate) rewards C_star C_h q record.input.time start hstartTime'
    control0 i z
  have hlaunchOriginal := ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput_launch
    (rate := rate) rewards C_star C_h q record.input.time start hstartTime'
    control0 i z
  have hlaunchPayload := ReferenceCompletePhysicalHistory.correctedLaunch_eq_some_payload
    rate source rewards C_star C_h hlaunch
  have hstate : originalInput.val.1 = runInput.val.1 := by
    rw [ReferenceGeneratedDownAmbiguityMeasurability.generatedActiveRunInput_val]
    exact Option.some.inj (hlaunchOriginal.symm.trans hlaunchPayload)
  have hdata : originalInput.val.2 = runInput.val.2 := by
    rw [ReferenceGeneratedDownAmbiguityMeasurability.generatedActiveRunInput_val]
    rfl
  have hinputEq : originalInput = runInput := Subtype.ext (Prod.ext hstate hdata)
  have hrecordsEq :
      (ReferenceActiveHorizonMeasurability.runOfInput start (p.T - start) hspan
        originalInput).records =
      (ReferenceActiveHorizonMeasurability.runOfInput start (p.T - start) hspan
        runInput).records := by
    rw [hinputEq]
  have hindexTime : record.input.time.val - start = index := by omega
  have hgetOriginal :
      (ReferenceActiveHorizonMeasurability.runOfInput start (p.T - start) hspan
        originalInput).records[index]? = some record := by
    rw [hrecordsEq]
    exact hgetRun
  have hgetCurrent := upTail_originalSourceCurrentRecord_get
    (rate := rate) rewards C_star C_h q record.input.time start hstartTime'
    control0 i z
  have hgetCurrent' :
      (ReferenceActiveHorizonMeasurability.runOfInput start (p.T - start) hspan
        originalInput).records[index]? =
        some (ReferenceGeneratedUpPrefixPositiveHalf.originalSourceCurrentRecord
          (rate := rate) rewards C_star C_h q record.input.time start hstartTime'
          control0 i z) := by
    simpa [hindexTime, originalInput] using hgetCurrent
  have hrecordEq : record =
      ReferenceGeneratedUpPrefixPositiveHalf.originalSourceCurrentRecord
        (rate := rate) rewards C_star C_h q record.input.time start hstartTime'
        control0 i z := Option.some.inj (hgetOriginal.symm.trans hgetCurrent')
  have hcurrent :
      (ReferenceGeneratedUpPrefixPositiveHalf.originalSourceCurrentRecord
        (rate := rate) rewards C_star C_h q record.input.time start hstartTime'
        control0 i z).output.coordinator.up = some diagnostic := by
    rw [← hrecordEq]
    exact hdiagnostic
  have hcoverage := ReferenceGeneratedUpFixedReplySuffix.actual_wrong_local_up_survival
    (rate := rate) rewards C_star C_h q record.input.time start hstartTime'
    control0 i z diagnostic hcurrent rfl word hraw hlocallyAccepted hmismatch
  exact ⟨q, start, i, hstartTime', rfl, hbranch, z, rfl, hrecordEq, hcoverage⟩

/-- The UP-only code on mapped canonical run records is exactly existence of
the same literal UP flag on the corresponding physical prefix. -/
theorem upWrongPrefixCode_true_iff_records
    (prefixCount : ℕ)
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))) :
    upWrongPrefixCode prefixCount
        (records.map ReferenceActiveHorizonMeasurability.roundRecordCode) = true ↔
      ∃ record ∈ records.take prefixCount, upWrongRecordFlag record = true := by
  unfold upWrongPrefixCode
  rw [← List.map_take, List.any_eq_true]
  constructor
  · rintro ⟨code, hcode, hbad⟩
    rcases List.mem_map.mp hcode with ⟨record, hrecord, rfl⟩
    exact ⟨record, hrecord, by simpa [upWrongRecordCode_roundRecordCode] using hbad⟩
  · rintro ⟨record, hrecord, hbad⟩
    exact ⟨ReferenceActiveHorizonMeasurability.roundRecordCode record,
      List.mem_map.mpr ⟨record, hrecord, rfl⟩,
      by simpa [upWrongRecordCode_roundRecordCode] using hbad⟩

/-- The UP-only prefix predicate on the existing varying-calendar run code. -/
def upCalendarPrefixCode
    (input : ReferenceActiveHorizonMeasurability.CalendarRunInput (p := p) (rate := rate))
    (prefixCount : ℕ) : Bool :=
  upWrongPrefixCode prefixCount
    (ReferenceActiveHorizonMeasurability.calendarRunObservation input).2

private def upWrongPrefixOnLaunchFiber
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (start : Fin (p.T + 1)) (prefixCount : ℕ) :
    Set (ReferenceGeneratedDownAmbiguityMeasurability.GeneratedLaunchFiber
      (rate := rate) rewards C_star C_h start.val) :=
  {source | upWrongPrefixCode prefixCount
    (ReferenceActiveHorizonMeasurability.runObservation start.val (p.T - start.val) (by omega)
      (ReferenceGeneratedDownAmbiguityMeasurability.generatedActiveRunInput
        (rate := rate) rewards C_star C_h start.val source)).2 = true}

private theorem upWrongPrefixOnLaunchFiber_iff
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (start : Fin (p.T + 1)) (prefixCount : ℕ)
    (source : ReferenceGeneratedDownAmbiguityMeasurability.GeneratedLaunchFiber
      (rate := rate) rewards C_star C_h start.val) :
    source ∈ upWrongPrefixOnLaunchFiber (rate := rate) rewards C_star C_h start prefixCount ↔
      source.1 ∈ generatedUpWrongSuffixPrefixEvent
        (r := rate) rewards C_star C_h prefixCount := by
  change upWrongPrefixCode prefixCount
      (ReferenceActiveHorizonMeasurability.runObservation start.val (p.T - start.val)
        (by omega)
        (ReferenceGeneratedDownAmbiguityMeasurability.generatedActiveRunInput
          (rate := rate) rewards C_star C_h start.val source)).2 = true ↔ _
  rw [ReferenceActiveHorizonMeasurability.runObservation_records,
    upWrongPrefixCode_true_iff_records]
  have hrecords := ReferenceGeneratedDownAmbiguityMeasurability.generatedRun_records_eq_completeSuffixRecords_take
    (rate := rate) rewards C_star C_h start.val (p.T - start.val) (by omega) source
  have hlength := ReferenceCompletePhysicalHistory.completeSuffixRecords_length
    rate source.1 rewards C_star C_h
  rw [source.2.2] at hlength
  have htake :
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source.1 rewards C_star C_h).take
        (p.T - start.val) =
      ReferenceCompletePhysicalHistory.completeSuffixRecords rate source.1 rewards C_star C_h :=
    List.take_of_length_le (Nat.le_of_eq hlength)
  rw [hrecords, htake]
  have hevent := generatedUpWrongSuffixPrefixEvent_true_iff
    (rate := rate) rewards C_star C_h prefixCount source.1
  constructor
  · rintro ⟨record, hrecord, hflag⟩
    obtain ⟨diagnostic, hdiagnostic, hwrong⟩ :=
      (upWrongRecordFlag_true_iff (rate := rate) record).1 hflag
    exact hevent.mpr ⟨record, hrecord, diagnostic, hdiagnostic, hwrong⟩
  · intro hsource
    obtain ⟨record, hrecord, diagnostic, hdiagnostic, hwrong⟩ := hevent.mp hsource
    exact ⟨record, hrecord,
      (upWrongRecordFlag_true_iff (rate := rate) record).2
        ⟨diagnostic, hdiagnostic, hwrong⟩⟩

private theorem measurableSet_upWrongPrefixOnLaunchFiber
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (start : Fin (p.T + 1)) (prefixCount : ℕ) :
    MeasurableSet (upWrongPrefixOnLaunchFiber
      (rate := rate) rewards C_star C_h start prefixCount) := by
  have hcode : Measurable (fun source :
      ReferenceGeneratedDownAmbiguityMeasurability.GeneratedLaunchFiber
        (rate := rate) rewards C_star C_h start.val =>
      upWrongPrefixCode prefixCount
        (ReferenceActiveHorizonMeasurability.runObservation start.val
          (p.T - start.val) (by omega)
          (ReferenceGeneratedDownAmbiguityMeasurability.generatedActiveRunInput
            (rate := rate) rewards C_star C_h start.val source)).2) := by
    have hrun := ReferenceActiveHorizonMeasurability.measurable_runObservation
      (p := p) (rate := rate) start.val (p.T - start.val) (by omega)
    have hobs := hrun.comp
      (ReferenceGeneratedDownAmbiguityMeasurability.measurable_generatedActiveRunInput
        (rate := rate) rewards C_star C_h start.val)
    exact measurable_upWrongPrefixCode.comp
      (measurable_const.prodMk (measurable_snd.comp hobs))
  exact hcode (measurableSet_singleton true)

private theorem generatedUpWrongSuffixPrefixEvent_eq_launchFiber_union
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (prefixCount : ℕ) :
    generatedUpWrongSuffixPrefixEvent (r := rate) rewards C_star C_h prefixCount =
      ⋃ start : Fin (p.T + 1), Subtype.val '' upWrongPrefixOnLaunchFiber
        (rate := rate) rewards C_star C_h start prefixCount := by
  ext source
  constructor
  · intro hevent
    by_cases hnone : ReferenceCorrectedInitializationLaunch.correctedLaunch
        rate source rewards C_star C_h = none
    · have hrecords : ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h = [] := by
        simp [ReferenceCompletePhysicalHistory.completeSuffixRecords, hnone]
      have hfalse : source ∉ generatedUpWrongSuffixPrefixEvent
          (r := rate) rewards C_star C_h prefixCount := by
        rw [generatedUpWrongSuffixPrefixEvent_true_iff]
        rw [hrecords]
        simp
      exact (hfalse hevent).elim
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
      have hfiber : source ∈ ReferenceGeneratedDownAmbiguityMeasurability.generatedLaunchFiberSet
          (rate := rate) rewards C_star C_h start.val := ⟨hcrossing, rfl⟩
      let fiber : ReferenceGeneratedDownAmbiguityMeasurability.GeneratedLaunchFiber
          (rate := rate) rewards C_star C_h start.val := ⟨source, hfiber⟩
      have hbranch : fiber ∈ upWrongPrefixOnLaunchFiber
          (rate := rate) rewards C_star C_h start prefixCount :=
        (upWrongPrefixOnLaunchFiber_iff (rate := rate) rewards C_star C_h start
          prefixCount fiber).2 hevent
      apply Set.mem_iUnion.mpr
      refine ⟨start, ?_⟩
      exact ⟨fiber, hbranch, rfl⟩
  · intro h
    rcases Set.mem_iUnion.mp h with ⟨start, hmem⟩
    rcases hmem with ⟨fiber, hbranch, hsource⟩
    subst source
    exact (upWrongPrefixOnLaunchFiber_iff (rate := rate) rewards C_star C_h start
      prefixCount fiber).1 hbranch

/-- The literal UP-only suffix-prefix event is Borel on the full original
source carrier, by gluing the actual generated launch fibers. -/
theorem measurableSet_generatedUpWrongSuffixPrefixEvent
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (prefixCount : ℕ) :
    MeasurableSet (generatedUpWrongSuffixPrefixEvent
      (r := rate) rewards C_star C_h prefixCount) := by
  rw [generatedUpWrongSuffixPrefixEvent_eq_launchFiber_union
    (rate := rate) rewards C_star C_h prefixCount]
  apply MeasurableSet.iUnion
  intro start
  exact MeasurableSet.subtype_image
    (ReferenceGeneratedDownAmbiguityMeasurability.measurableSet_generatedLaunchFiberSet
      (rate := rate) rewards C_star C_h start.val)
    (measurableSet_upWrongPrefixOnLaunchFiber
      (rate := rate) rewards C_star C_h start prefixCount)

/-- Every complete-suffix-prefix wrong UP diagnostic enters the existing
all-J survival envelope through its same actual birth and saved raw candidate.
This is a physical-horizon inclusion, with no terminal ordinary-state premise. -/
theorem generatedUpWrongSuffixPrefixEvent_subset_upAwaitedAmbiguityEnvelope
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (prefixCount : ℕ) :
    generatedUpWrongSuffixPrefixEvent (r := rate) rewards C_star C_h prefixCount ⊆
      ReferenceGeneratedUpAwaitedAmbiguityTail.upAwaitedAmbiguityEnvelope
        (rate := rate) rewards C_star C_h control0 := by
  classical
  intro source hsource
  obtain ⟨record, hrecord, diagnostic, hdiagnostic, word, hraw, hlocal, hmismatch⟩ :=
    (generatedUpWrongSuffixPrefixEvent_actual_fields
      (rate := rate) rewards C_star C_h prefixCount source).1 hsource
  obtain ⟨q, start, i, hstartTime, hselectedFollower, hbranch, z, hz,
      hrecordEq, hcoverage⟩ :=
    actualSuffix_wrongUp_record_survival (rate := rate) rewards C_star C_h control0
      prefixCount source record hrecord diagnostic hdiagnostic word hraw hlocal hmismatch
  dsimp only at hcoverage
  obtain ⟨alpha, hstartAlpha, hAlphaTime, hbirth, hkeptLength, hprojection,
      hnever, hsurvival⟩ := hcoverage
  have hAlphaLt : alpha < p.T := lt_of_le_of_lt hAlphaTime record.input.time.isLt
  let alphaFin : Fin p.T := ⟨alpha, hAlphaLt⟩
  have hsourceSurvival : source ∈ ReferenceGeneratedUpSourceCalendar.upSourceSurvivalEvent
      (rate := rate) rewards C_star C_h q control0 alpha word i
      (AffineBatchDecoder.quota p) := by
    simpa only [hz] using hsurvival
  simp only [ReferenceGeneratedUpAwaitedAmbiguityTail.upAwaitedAmbiguityEnvelope,
    Set.mem_iUnion]
  refine ⟨i, alphaFin, word, ?_⟩
  change source ∈ ⋃ q' : Fin (M p),
    ReferenceGeneratedUpSourceCalendar.upSourceSurvivalEvent (rate := rate)
      rewards C_star C_h q' control0 alpha word i (AffineBatchDecoder.quota p)
  exact Set.mem_iUnion.mpr ⟨q, hsourceSurvival⟩

/-- The UP-only complete-suffix prefix event inherits the established
finite-factor ENNReal bound of A's all-J ambiguity envelope. -/
theorem generatedUpWrongSuffixPrefixEvent_measure_le
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (prefixCount : ℕ) :
    BootstrapPrivateRoundStreams.sourceInputLaw p
        (generatedUpWrongSuffixPrefixEvent (r := rate) rewards C_star C_h prefixCount) ≤
      ((p.m - 1 : ℕ) : ℝ≥0∞) * p.T * 2 ^ AffineBatchDecoder.width p *
        ((1 : ℝ≥0∞) / 2) ^ AffineBatchDecoder.quota p := by
  calc
    _ ≤ BootstrapPrivateRoundStreams.sourceInputLaw p
        (ReferenceGeneratedUpAwaitedAmbiguityTail.upAwaitedAmbiguityEnvelope
          (rate := rate) rewards C_star C_h control0) :=
      measure_mono (generatedUpWrongSuffixPrefixEvent_subset_upAwaitedAmbiguityEnvelope
        (rate := rate) rewards C_star C_h control0 prefixCount)
    _ ≤ _ := ReferenceGeneratedUpAwaitedAmbiguityTail.upAwaitedAmbiguityEnvelope_measure_le
      (rate := rate) rewards C_star C_h control0

/-- The literal UP-only event has original-source real measure at most
`1 / (4 N^2)`, by monotonicity through the existing all-J envelope. -/
theorem generatedUpWrongSuffixPrefixEvent_measureReal_le
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (prefixCount : ℕ) :
    (BootstrapPrivateRoundStreams.sourceInputLaw p).real
        (generatedUpWrongSuffixPrefixEvent (r := rate) rewards C_star C_h prefixCount) ≤
      1 / (4 * (N p : ℝ) ^ 2) := by
  calc
    _ ≤ (BootstrapPrivateRoundStreams.sourceInputLaw p).real
        (ReferenceGeneratedUpAwaitedAmbiguityTail.upAwaitedAmbiguityEnvelope
          (rate := rate) rewards C_star C_h control0) :=
      measureReal_mono (generatedUpWrongSuffixPrefixEvent_subset_upAwaitedAmbiguityEnvelope
        (rate := rate) rewards C_star C_h control0 prefixCount)
    _ ≤ _ := ReferenceGeneratedUpAwaitedAmbiguityTail.upAwaitedAmbiguityEnvelope_measureReal_le
      (rate := rate) rewards C_star C_h control0

end Bandits.Support.ReferenceGeneratedUpFalseTail

end
