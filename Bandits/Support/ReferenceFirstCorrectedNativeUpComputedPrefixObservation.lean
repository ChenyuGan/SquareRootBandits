/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionCorrectedAssignedOverflowCover
public import Bandits.Support.ReferenceFirstCorrectedBirthComputedOverflowCover

import Mathlib.Tactic

/-!
# Native UP computed-prefix queue observation

This module observes the exact queue endpoints computed by the literal native
UP decoder on the original source input. It also localizes those endpoints to
the first corrected collection segment. It proves no queue-truth, overflow
probability, or post-cutoff moment statement.

Sources: ZIP4 `appendix_a_local_protocol.tex:28-64`,
`06_interruptions.tex:192-233,246-299`, and
`04_slow_fast_learner.tex:157-187,256-290`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support
open ConstructorDimensions
open BootstrapPrivateRoundStreams (SourceInput)
open ReferenceFirstCollectionCorrectedSliceNumericalPrefix
  (correctedCell sourceRecords sourceStart birthIndex liveTail)

namespace Bandits.Support.ReferenceFirstCorrectedNativeUpComputedPrefixObservation

variable {p : Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ)

local notation "X" => SourceInput p
local notation "Ledger" => ReferenceActivePhysicalStep.Ledger rate
local notation "Up" => OrdinaryMessageCodec.UpRecord
  (CoordinatorCollectionLedger.codecParams p rate.eta.val)
local notation "Record" => ReferenceActivePhysicalHorizon.RoundRecord
  (p := p) (rate := rate)
local notation "Input" => ReferenceActivePhysicalStep.RoundInput p rate
local notation "TailCode" => ReferenceCollectionServiceTailMeasurability.CollectionTailCode p rate
local notation "UpCode" => ReferenceCollectionServiceTailMeasurability.UpDiagnosticCode p rate
local notation "CoordinatorCode" => ReferenceActivePhysicalStepMeasurability.CoordinatorCode p rate

local instance upDiagnosticOptionDiscrete :
    DiscreteMeasurableSpace (Option UpCode) := ⟨fun _ => trivial⟩

open CoordinatorCollectionLedger

/-- The computed queue at a UP replay prefix, only after all checks that
precede `replayOutputDomainsCheck` in the literal `decodeUp` have been reached.
The Boolean prefix-domain family itself is deliberately not used: after the
length and arrival guards, every prefix in that family is observed. -/
def decodePrefixQueue? (l : Ledger) (i : Fin (p.m - 1)) (parsed : Option Up)
    (k : ℕ) : Option (Fin p.K × ℕ) := by
  classical
  exact if hinput : validLedgerCheck l = true ∧ l.phase = .started ∧
      1 ≤ l.cutoff ∧ l.cutoff ≤ l.cursor ∧ l.cursor ≤ p.T then
    match parsed with
    | none => none
    | some M =>
      if acceptUpCheck l i M then
        if hunknown : l.currentRegisters (l.assignment.arm i) = none ∧
            l.cutoffRegisters (l.assignment.arm i) = none then
          let start := l.cutoff - 1
          let prefixLength := l.cursor - l.cutoff
          let hprefix : start + prefixLength ≤ p.T := by
            have := hinput.2.2.1
            have := hinput.2.2.2.1
            have := hinput.2.2.2.2
            omega
          let prefixIndices := calendarIndices p.T start prefixLength hprefix
          let lastIndex : Fin p.T := ⟨l.cursor - 1, by
            have := hinput.2.2.1
            have := hinput.2.2.2.1
            have := hinput.2.2.2.2
            omega⟩
          match replayRecords? l (l.assignment.arm i) prefixIndices,
              replayRecords? l (l.assignment.arm i) [lastIndex] with
          | some past, some [current] =>
              let records := past ++ [current]
              if decide (records.length ≤ p.T) &&
                  records.all (fun record => decide (record.2 ≤ D p)) then
                if k ≤ records.length then
                  some (l.assignment.arm i,
                    (QueueReplay.replay (4 * rate.n) (0, M.val.q)
                      (records.take k)).2)
                else none
              else none
          | _, _ => none
        else none
      else none
  else none

/-- Once the literal decoder has reached the replay records and its two
pre-replay output guards pass, the observer returns exactly the endpoint from
`QueueReplay.replay` for every requested prefix. -/
theorem decodePrefixQueue?_reached
    (l : Ledger) (i : Fin (p.m - 1)) (M : Up) (k : ℕ)
    (hinput : validLedgerCheck l = true ∧ l.phase = .started ∧
      1 ≤ l.cutoff ∧ l.cutoff ≤ l.cursor ∧ l.cursor ≤ p.T)
    (haccepted : acceptUpCheck l i M = true)
    (hunknown : l.currentRegisters (l.assignment.arm i) = none ∧
      l.cutoffRegisters (l.assignment.arm i) = none)
    (past : List (Bool × ℕ)) (current : Bool × ℕ)
    (hpast : replayRecords? l (l.assignment.arm i)
      (calendarIndices p.T (l.cutoff - 1) (l.cursor - l.cutoff) (by
        have := hinput.2.2.1
        have := hinput.2.2.2.1
        have := hinput.2.2.2.2
        omega)) = some past)
    (hcurrent : replayRecords? l (l.assignment.arm i)
      [⟨l.cursor - 1, by
        have := hinput.2.2.1
        have := hinput.2.2.2.1
        have := hinput.2.2.2.2
        omega⟩] = some [current])
    (hdomains : (decide ((past ++ [current]).length ≤ p.T) &&
      (past ++ [current]).all (fun record => decide (record.2 ≤ D p))) = true) :
    decodePrefixQueue? rate l i (some M) k =
      if k ≤ (past ++ [current]).length then
        some (l.assignment.arm i,
          (QueueReplay.replay (4 * rate.n) (0, M.val.q)
            ((past ++ [current]).take k)).2)
      else none := by
  classical
  unfold decodePrefixQueue?
  rw [dite_eq_left hinput]
  simp only [haccepted, hunknown, hpast, hcurrent]
  rw [ite_eq_left hdomains]
  rfl

/-- The zero-length computed prefix is the actual UP seed queue after the
same reached checks; it is not supplied by a default branch. -/
theorem decodePrefixQueue?_zero_of_reached
    (l : Ledger) (i : Fin (p.m - 1)) (M : Up)
    (hinput : validLedgerCheck l = true ∧ l.phase = .started ∧
      1 ≤ l.cutoff ∧ l.cutoff ≤ l.cursor ∧ l.cursor ≤ p.T)
    (haccepted : acceptUpCheck l i M = true)
    (hunknown : l.currentRegisters (l.assignment.arm i) = none ∧
      l.cutoffRegisters (l.assignment.arm i) = none)
    (past : List (Bool × ℕ)) (current : Bool × ℕ)
    (hpast : replayRecords? l (l.assignment.arm i)
      (calendarIndices p.T (l.cutoff - 1) (l.cursor - l.cutoff) (by
        have := hinput.2.2.1
        have := hinput.2.2.2.1
        have := hinput.2.2.2.2
        omega)) = some past)
    (hcurrent : replayRecords? l (l.assignment.arm i)
      [⟨l.cursor - 1, by
        have := hinput.2.2.1
        have := hinput.2.2.2.1
        have := hinput.2.2.2.2
        omega⟩] = some [current])
    (hdomains : (decide ((past ++ [current]).length ≤ p.T) &&
      (past ++ [current]).all (fun record => decide (record.2 ≤ D p))) = true) :
    decodePrefixQueue? rate l i (some M) 0 = some (l.assignment.arm i, M.val.q) := by
  rw [decodePrefixQueue?_reached rate l i M 0 hinput haccepted hunknown past current
    hpast hcurrent hdomains]
  simp [QueueReplay.replay]

/-- Direct projection of the same-round UP diagnostic retained by a physical
record. Parsing uses the same-row expected-word filter, not the diagnostic's
unfiltered `parsed` field or its summary flags. -/
def recordPrefixQueue? (r : Record) (k : ℕ) : Option (Fin p.K × ℕ) :=
  r.output.coordinator.up.bind fun diagnostic =>
    decodePrefixQueue? rate diagnostic.input.ledger diagnostic.input.selectedFollower
      (CoordinatorUpReception.parseDecoderOutput
        (ReferenceUpReception.filterRawByExpected diagnostic.raw diagnostic.expected)) k

/-- The diagnostic coordinate extracted from the existing joint whole-step
code. No execution or queue-state carrier is introduced. -/
def wholeStepTailCode (x : Input) : TailCode :=
  (ReferenceActiveStepCompositionMeasurability.wholeStepCode x).1.2.2.2.2

/-- Lossless final diagnostic projection from the canonical collection code. -/
def tailUpDiagnostic? (code : TailCode) : Option UpCode := code.2.2.2.2

/-- The diagnostic coordinate extracted from the existing joint whole-step
code. No execution or queue-state carrier is introduced. -/
def wholeStepUpDiagnostic? (x : Input) : Option UpCode :=
  tailUpDiagnostic? rate (wholeStepTailCode rate x)

/-- Decode each retained diagnostic and observe the exact filtered parse used
by the receiver. -/
def inputPrefixQueue? (x : Input) (k : ℕ) : Option (Fin p.K × ℕ) :=
  (wholeStepUpDiagnostic? rate x).bind fun code =>
    let diagnostic := ReferenceCollectionServiceTailMeasurability.decodeUpDiagnostic code
    decodePrefixQueue? rate diagnostic.input.ledger diagnostic.input.selectedFollower
      (CoordinatorUpReception.parseDecoderOutput
        (ReferenceUpReception.filterRawByExpected diagnostic.raw diagnostic.expected)) k

/-- On every existing round record, the canonical code observer equals the
literal physical output observer. -/
theorem inputPrefixQueue?_eq_record (r : Record) (k : ℕ) :
    inputPrefixQueue? rate r.input k = recordPrefixQueue? rate r k := by
  have hwhole := ReferenceActiveStepCompositionMeasurability.wholeStepCode_reconstructs r.input
  have hcode := congrArg
    (fun observation : ReferenceActivePhysicalStep.CoordinatorObservation p rate => observation.up)
    hwhole.1
  have houtput : r.output.coordinator =
      (ReferenceActivePhysicalStep.prepare r.input).observeCoordinator := by
    rw [r.output_eq]
    rfl
  have hdiagnostic :
      (tailUpDiagnostic? rate (wholeStepTailCode rate r.input)).map
        ReferenceCollectionServiceTailMeasurability.decodeUpDiagnostic =
      r.output.coordinator.up := by
    have hdecoded :
        (ReferenceCollectionServiceTailMeasurability.decodeCollectionObservation
          (wholeStepTailCode rate r.input)).up = r.output.coordinator.up := by
      change (ReferenceCollectionServiceTailMeasurability.decodeCollectionObservation
        (ReferenceActiveStepCompositionMeasurability.wholeStepCode r.input).1.2.2.2.2).up =
          r.output.coordinator.up
      rw [hcode, houtput]
    simpa only [tailUpDiagnostic?, ReferenceCollectionServiceTailMeasurability.decodeCollectionObservation]
      using hdecoded
  unfold inputPrefixQueue? wholeStepUpDiagnostic? tailUpDiagnostic? wholeStepTailCode
    recordPrefixQueue?
  cases hd : (((ReferenceActiveStepCompositionMeasurability.wholeStepCode r.input).1.2.2.2.2).2.2.2.2) with
  | none =>
      have hnone : r.output.coordinator.up = none := by
        simpa [wholeStepTailCode, tailUpDiagnostic?, hd] using hdiagnostic.symm
      simp [hnone]
  | some code =>
      have hdiagEq : some
          (ReferenceCollectionServiceTailMeasurability.decodeUpDiagnostic code) =
          r.output.coordinator.up := by
        simpa [wholeStepTailCode, tailUpDiagnostic?, hd] using hdiagnostic
      cases hout : r.output.coordinator.up with
      | none => simp [hout] at hdiagEq
      | some diagnostic =>
          have hdecode :
              ReferenceCollectionServiceTailMeasurability.decodeUpDiagnostic code = diagnostic :=
            Option.some.inj (by simpa [hout] using hdiagEq)
          simp [hdecode]

/-- The diagnostic projection from the canonical whole-step code is
measurable. The original State, input, payload, row, and record spaces are
left unchanged. -/
theorem measurable_wholeStepUpDiagnostic? :
    Measurable (wholeStepUpDiagnostic? rate : Input → Option UpCode) := by
  have hwhole := ReferenceActiveStepCompositionMeasurability.measurable_wholeStepCode
    (p := p) (rate := rate)
  have hphysical : Measurable (fun x : Input =>
      (ReferenceActiveStepCompositionMeasurability.wholeStepCode x).1) :=
    measurable_fst.comp hwhole
  have htail : Measurable (wholeStepTailCode rate : Input → TailCode) := by
    have h1 : Measurable (fun x : Input =>
        ((ReferenceActiveStepCompositionMeasurability.wholeStepCode x).1).2) :=
      measurable_snd.comp hphysical
    have h2 : Measurable (fun x : Input =>
        (((ReferenceActiveStepCompositionMeasurability.wholeStepCode x).1).2).2) :=
      measurable_snd.comp h1
    have h3 : Measurable (fun x : Input =>
        ((((ReferenceActiveStepCompositionMeasurability.wholeStepCode x).1).2).2).2) :=
      measurable_snd.comp h2
    have h4 : Measurable (fun x : Input =>
        (((((ReferenceActiveStepCompositionMeasurability.wholeStepCode x).1).2).2).2).2) :=
      measurable_snd.comp h3
    change Measurable (fun x : Input =>
      (ReferenceActiveStepCompositionMeasurability.wholeStepCode x).1.2.2.2.2)
    exact h4
  have hdiag : Measurable (tailUpDiagnostic? rate : TailCode → Option UpCode) := by
    have h1 : Measurable (fun code : TailCode => code.2) := measurable_snd
    have h2 : Measurable (fun code : TailCode => code.2.2) := measurable_snd.comp h1
    have h3 : Measurable (fun code : TailCode => code.2.2.2) := measurable_snd.comp h2
    have h4 : Measurable (fun code : TailCode => code.2.2.2.2) := measurable_snd.comp h3
    change Measurable (fun code : TailCode => code.2.2.2.2)
    exact h4
  change Measurable (tailUpDiagnostic? rate ∘ wholeStepTailCode rate)
  exact hdiag.comp htail

/-- The fixed input-prefix observer is Borel on the original continuous
`RoundInput` carrier. Its varying diagnostic fields use the existing
countable, lossless UP code. -/
theorem measurable_inputPrefixQueue? (k : ℕ) :
    Measurable (fun x : Input => inputPrefixQueue? rate x k) := by
  let observer : Option UpCode → Option (Fin p.K × ℕ) := fun diagnostic? =>
    diagnostic?.bind fun code =>
      let diagnostic := ReferenceCollectionServiceTailMeasurability.decodeUpDiagnostic code
      decodePrefixQueue? rate diagnostic.input.ledger diagnostic.input.selectedFollower
        (CoordinatorUpReception.parseDecoderOutput
          (ReferenceUpReception.filterRawByExpected diagnostic.raw diagnostic.expected)) k
  have hobserver : Measurable observer := Measurable.of_discrete
  have hdiag := measurable_wholeStepUpDiagnostic? (p := p) rate
  change Measurable (fun x : Input => observer (wholeStepUpDiagnostic? rate x))
  exact hobserver.comp hdiag

/-- Apply the record observer to the actual record at one calendar date,
retaining absence when the source suffix has no such round. -/
def sourcePrefixQueue? (q : Fin p.T) (k : ℕ) (z : X) : Option (Fin p.K × ℕ) :=
  (ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h q z).bind
    (fun r => recordPrefixQueue? rate r k)

/-- The same source observation factors through the established actual-input
projection, with the option preserved on absent records. -/
theorem sourcePrefixQueue?_eq_actualInput (q : Fin p.T) (k : ℕ) (z : X) :
    sourcePrefixQueue? rate rewards C_star C_h q k z =
      (ReferenceFirstCollectionCorrectedNextPhysicalReadout.actualInput?
        rate rewards C_star C_h q z).bind (fun x => inputPrefixQueue? rate x k) := by
  unfold sourcePrefixQueue? ReferenceFirstCollectionCorrectedNextPhysicalReadout.actualInput?
    inputPrefixQueue?
  cases hrecord : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h q z <;> simp
  case some r => exact (inputPrefixQueue?_eq_record rate r k).symm

private theorem measurable_optionBind {A B D : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace (Option D)]
    (f : A → Option B) (hf : Measurable f) (g : B → Option D) (hg : Measurable g) :
    Measurable (fun a => (f a).bind g) := by
  have he : Measurable (Equiv.optionEquivSumPUnit B) := comap_measurable _
  have hl : Measurable (Sum.elim g (fun _ : PUnit => (none : Option D))) :=
    measurable_fun_sum hg measurable_const
  convert hl.comp (he.comp hf) using 1
  funext a
  dsimp only [Function.comp_def]
  cases f a <;> rfl

/-- The original-source prefix observer is Borel by the existing Borel
`actualInput?` projection and the fixed-input identity above. -/
theorem measurable_sourcePrefixQueue? (q : Fin p.T) (k : ℕ) :
    Measurable (sourcePrefixQueue? rate rewards C_star C_h q k) := by
  have heq : sourcePrefixQueue? rate rewards C_star C_h q k =
      fun z => (ReferenceFirstCollectionCorrectedNextPhysicalReadout.actualInput?
        rate rewards C_star C_h q z).bind (fun x => inputPrefixQueue? rate x k) := by
    funext z
    exact sourcePrefixQueue?_eq_actualInput rate rewards C_star C_h q k z
  rw [heq]
  exact measurable_optionBind
    (ReferenceFirstCollectionCorrectedNextPhysicalReadout.actualInput?
      rate rewards C_star C_h q)
    (ReferenceFirstCollectionCorrectedNextPhysicalReadout.measurable_actualInput?
      rate rewards C_star C_h q)
    (fun x => inputPrefixQueue? rate x k)
    (measurable_inputPrefixQueue? rate k)

/-- Literal first collection-segment localization in the original physical
suffix. The endpoint index is allowed, so it can inspect the optional first
excluded record when that record exists. -/
def firstPrefixQueueAt (z : X) (j k : ℕ) : Option (Fin p.K × ℕ) := by
  classical
  let R := sourceRecords rate rewards C_star C_h z
  let e := birthIndex rate rewards C_star C_h z + 1 +
    (liveTail rate rewards C_star C_h z).length
  exact match R[e]? with
  | none => none
  | some entry =>
      if ReferenceCollectionPhaseHistory.cutoffChosen entry.input then
        match ReferenceCollectionSegmentExtraction.segmentAt R e with
        | none => none
        | some segment =>
            if j ≤ segment.records.length then
              (R[e + j]?).bind fun record => recordPrefixQueue? rate record k
            else none
      else none


/-- The collection tag of an existing canonical coordinator sum code. The
continuous payload and the ledger stay in their original measurable spaces. -/
def coordinatorCollectionTag (code : CoordinatorCode) : Bool :=
  match code with
  | .inl _ => false
  | .inr (.inl _) => false
  | .inr (.inr (.inl _)) => true
  | .inr (.inr (.inr _)) => false

/-- The same constructor tag on the semantic coordinator configuration. -/
def configurationCollectionTag
    (configuration : ReferenceActivePhysicalStep.CoordinatorConfiguration p rate) : Bool :=
  match configuration with
  | .collection _ _ _ => true
  | _ => false

theorem coordinatorCollectionTag_encode (configuration :
    ReferenceActivePhysicalStep.CoordinatorConfiguration p rate) :
    coordinatorCollectionTag rate
      (ReferenceActivePhysicalStepMeasurability.encodeCoordinator configuration) =
        configurationCollectionTag rate configuration := by
  cases configuration <;> rfl

/-- The input tag is read from the original lossless state code. -/
def inputCollectionTag (x : Input) : Bool :=
  coordinatorCollectionTag rate
    (ReferenceActivePhysicalStepMeasurability.encodeState x.state).1

/-- The output tag is read from the successor coordinate already retained by
the canonical whole-step code. -/
def outputCollectionTag (x : Input) : Bool :=
  coordinatorCollectionTag rate
    ((ReferenceActiveStepCompositionMeasurability.wholeStepCode x).2.2).1

theorem inputCollectionTag_eq_configuration (x : Input) :
    inputCollectionTag rate x =
      configurationCollectionTag rate x.state.coordinator := by
  change coordinatorCollectionTag rate
    (ReferenceActivePhysicalStepMeasurability.encodeCoordinator x.state.coordinator) = _
  exact coordinatorCollectionTag_encode rate x.state.coordinator

theorem outputCollectionTag_eq_next (x : Input) :
    outputCollectionTag rate x =
      configurationCollectionTag rate
        (ReferenceActivePhysicalStep.step x).next.coordinator := by
  change coordinatorCollectionTag rate
    (ReferenceActivePhysicalStepMeasurability.successorCode x).1 = _
  change coordinatorCollectionTag rate
    (ReferenceActivePhysicalStepMeasurability.encodeState
      (ReferenceActivePhysicalStep.step x).next).1 = _
  exact coordinatorCollectionTag_encode rate
    (ReferenceActivePhysicalStep.step x).next.coordinator

theorem outputCollectionTag_eq_recordObservation (r : Record) :
    outputCollectionTag rate r.input =
      configurationCollectionTag rate r.output.coordinator.configuration := by
  rw [outputCollectionTag_eq_next]
  rw [r.output_eq]
  exact congrArg (configurationCollectionTag rate)
    (ReferenceActivePhysicalStep.step_next_fields r.input).1

/-- The live post-choice tail never reports a completed collection tag. -/
private theorem liveTail_not_collection {x : Input}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
    (base : Fin (p.m - 1) → ℕ)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (saved : Option (Fin p.T × Bool)) :
    (ReferenceActivePhysicalStep.livePostChoice prepared registers owned base started).configuration ≠
      .collection payload ledger saved := by
  unfold ReferenceActivePhysicalStep.livePostChoice
  split
  · simp only [ReferenceActivePhysicalStep.coordinatorFailure, ne_eq, reduceCtorEq,
      not_false_eq_true]
  · split
    · simp only [ReferenceActivePhysicalStep.coordinatorFailure, ne_eq, reduceCtorEq,
        not_false_eq_true]
    · split
      · simp only [ReferenceActivePhysicalStep.coordinatorFailure, ne_eq, reduceCtorEq,
          not_false_eq_true]
      · split <;> simp only [ReferenceActivePhysicalStep.coordinatorFailure,
          ne_eq, reduceCtorEq, not_false_eq_true]

/-- A collection output forces the exact actual dispatch choice. -/
private theorem choice_of_collection_output (r : Record)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (saved : Option (Fin p.T × Bool))
    (hout : r.output.next.coordinator = .collection payload ledger saved) :
    ∃ c : ReferenceCollectionSegmentExtraction.Choice rate,
      ReferenceCollectionSegmentExtraction.choice r.input = some c := by
  classical
  let x := r.input
  have h : (ReferenceActivePhysicalStep.prepare x).observeCoordinator.configuration =
      .collection payload ledger saved := by
    rw [r.output_eq] at hout
    exact hout
  have hsel : (ReferenceActivePhysicalStep.prepare x).coordinator.selection ≠ none := by
    intro hn
    simp only [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
      dite_eq_left hn, ReferenceActivePhysicalStep.coordinatorFailure] at h
    cases hh : (ReferenceActivePhysicalStep.prepare x).coordinator <;>
      simp only [hh, reduceCtorEq] at h
  unfold ReferenceCollectionSegmentExtraction.choice
  rw [ite_eq_right hsel]
  cases hd : (ReferenceActivePhysicalStep.prepare x).coordinator with
  | first outcome =>
      cases outcome <;>
        simp only [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator, hd,
          dite_eq_right hsel, ReferenceActivePhysicalStep.coordinatorFailure,
          reduceCtorEq] at h
      exact (liveTail_not_collection (rate := rate) (ReferenceActivePhysicalStep.prepare x) _ _ _ _
        payload ledger saved h).elim
  | live registers owned base outcome =>
      cases outcome <;>
        simp only [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator, hd,
          dite_eq_right hsel, ReferenceActivePhysicalStep.coordinatorFailure,
          reduceCtorEq] at h
      · exact ⟨_, rfl⟩
      · exact (liveTail_not_collection (rate := rate) (ReferenceActivePhysicalStep.prepare x) _ _ _ _
          payload ledger saved h).elim
  | collection oldPayload oldLedger clock cutoff outcome =>
      cases outcome <;>
        simp only [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator, hd,
          dite_eq_right hsel, ReferenceActivePhysicalStep.coordinatorFailure,
          reduceCtorEq] at h
      · exact ⟨_, rfl⟩
      · exact (liveTail_not_collection (rate := rate) (ReferenceActivePhysicalStep.prepare x) _ _ _ _
          payload ledger saved h).elim
  | invalidCollectionCutoff =>
      simp only [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator, hd,
        dite_eq_right hsel, ReferenceActivePhysicalStep.coordinatorFailure,
        reduceCtorEq] at h
  | dagger =>
      simp_all [ReferenceActivePhysicalStep.DispatchCut.selection]

/-- `extractRound` keeps exactly the rounds whose actual output coordinator
tag is collection, including both accepted and rejected UP finishes. -/
theorem extractRound_isSome_eq_outputCollectionTag (r : Record) :
    (ReferenceCollectionSegmentExtraction.extractRound r).isSome =
      outputCollectionTag rate r.input := by
  have hnext : r.output.next.coordinator = r.output.coordinator.configuration := by
    rw [r.output_eq]
    exact (ReferenceActivePhysicalStep.step_next_fields r.input).1
  cases hout : r.output.coordinator.configuration with
  | collection payload ledger saved =>
      have hcollection : r.output.next.coordinator = .collection payload ledger saved := by
        rw [hnext, hout]
      obtain ⟨choice, hchoice⟩ :=
        choice_of_collection_output rate r payload ledger saved hcollection
      obtain ⟨done, hdone⟩ :=
        ReferenceCollectionSegmentExtraction.actual_collection_round_complete
          r choice payload ledger saved hchoice hcollection
      rw [outputCollectionTag_eq_recordObservation rate r]
      rw [hout]
      rw [hdone]
      rfl
  | first =>
      have hnone : ReferenceCollectionSegmentExtraction.extractRound r = none := by
        unfold ReferenceCollectionSegmentExtraction.extractRound
        cases hc : ReferenceCollectionSegmentExtraction.choice r.input <;>
          simp [ReferenceCollectionSegmentExtraction.extractWith, hout]
      rw [outputCollectionTag_eq_recordObservation rate r]
      simp [hnone, hout, configurationCollectionTag]
  | live registers owned base =>
      have hnone : ReferenceCollectionSegmentExtraction.extractRound r = none := by
        unfold ReferenceCollectionSegmentExtraction.extractRound
        cases hc : ReferenceCollectionSegmentExtraction.choice r.input <;>
          simp [ReferenceCollectionSegmentExtraction.extractWith, hout]
      rw [outputCollectionTag_eq_recordObservation rate r]
      simp [hnone, hout, configurationCollectionTag]
  | dagger =>
      have hnone : ReferenceCollectionSegmentExtraction.extractRound r = none := by
        unfold ReferenceCollectionSegmentExtraction.extractRound
        cases hc : ReferenceCollectionSegmentExtraction.choice r.input <;>
          simp [ReferenceCollectionSegmentExtraction.extractWith, hout]
      rw [outputCollectionTag_eq_recordObservation rate r]
      simp [hnone, hout, configurationCollectionTag]

/-- Measurability of the actual incoming and outgoing coordinator tags uses
their canonical sum-code projections. -/
theorem measurable_coordinatorCollectionTag :
    Measurable (coordinatorCollectionTag rate : CoordinatorCode → Bool) := by
  unfold coordinatorCollectionTag
  apply measurable_fun_sum
  · exact measurable_const
  · apply measurable_fun_sum
    · exact measurable_const
    · exact measurable_fun_sum measurable_const measurable_const

theorem measurable_inputCollectionTag : Measurable (inputCollectionTag rate : Input → Bool) := by
  have hstate := ReferenceActivePhysicalStepMeasurability.measurable_state
    (p := p) (rate := rate)
  have hcode := ReferenceActivePhysicalStepMeasurability.measurable_encodeState.comp hstate
  have hcoord : Measurable (fun x : Input =>
      (ReferenceActivePhysicalStepMeasurability.encodeState x.state).1) :=
    measurable_fst.comp hcode
  exact (measurable_coordinatorCollectionTag (p := p) rate).comp hcoord

theorem measurable_outputCollectionTag : Measurable (outputCollectionTag rate : Input → Bool) := by
  have hwhole := ReferenceActiveStepCompositionMeasurability.measurable_wholeStepCode
    (p := p) (rate := rate)
  have hpair := measurable_snd.comp hwhole
  have hsuccessor := measurable_snd.comp hpair
  have hcoord : Measurable (fun x : Input =>
      ((ReferenceActiveStepCompositionMeasurability.wholeStepCode x).2.2).1) :=
    measurable_fst.comp hsuccessor
  exact (measurable_coordinatorCollectionTag (p := p) rate).comp hcoord

/-- The same continuing predicate read from the actual original-calendar
input/output tags. Its range alone is finite and discrete. -/
def horizonCollectionContinuing (q : Fin p.T) (z : X) : Bool :=
  (ReferenceFirstCollectionCorrectedNextPhysicalReadout.actualInput?
    rate rewards C_star C_h q z).elim false fun x =>
      inputCollectionTag rate x && outputCollectionTag rate x

def horizonCompletedCollection (q : Fin p.T) (z : X) : Bool :=
  (ReferenceFirstCollectionCorrectedNextPhysicalReadout.actualInput?
    rate rewards C_star C_h q z).elim false (outputCollectionTag rate)

/-- A count of true collection-continuation flags strictly after one date. -/
def collectionContinuingLength (q : Fin p.T) (z : X) : ℕ :=
  ((List.ofFn fun i : Fin (p.T - (q.val + 1)) =>
    horizonCollectionContinuing rate rewards C_star C_h
      ⟨q.val + 1 + i.val, by have := i.isLt; omega⟩ z).takeWhile id).length

def firstPrefixQueueCodeEval (t : Fin p.T) (j n : ℕ)
    (cut complete continues : Fin p.T → Bool)
    (queues : Fin p.T → Option (Fin p.K × ℕ)) : Option (Fin p.K × ℕ) := by
  classical
  let d := t.val + 1 + n
  exact if hd : d < p.T then
    let date : Fin p.T := ⟨d, hd⟩
    if cut date then
      let length := if complete date then
          1 + ((List.ofFn fun i : Fin (p.T - (d + 1)) =>
            continues ⟨d + 1 + i.val, by have := i.isLt; omega⟩).takeWhile id).length
        else 0
      if hj : j ≤ length then
        if hdate : d + j < p.T then queues ⟨d + j, hdate⟩ else none
      else none
    else none
  else none

/-- Finite-calendar Borel code for the same endpoint. It reads an actual
cutoff at the computed date, counts completed continuing rounds after it,
and retains the optional endpoint record. -/
def firstPrefixQueueCode? (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (t : Fin p.T) (z : X) (j k : ℕ) : Option (Fin p.K × ℕ) :=
  firstPrefixQueueCodeEval t j
    (ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.continuingLength
      rate rewards C_star C_h t z)
    (fun q => ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.horizonCutoff
      rate rewards C_star C_h q z)
    (fun q => horizonCompletedCollection rate rewards C_star C_h q z)
    (fun q => horizonCollectionContinuing rate rewards C_star C_h q z)
    (fun q => sourcePrefixQueue? rate rewards C_star C_h q k z)

private theorem measurable_optionBoolElim {A : Type*} [MeasurableSpace A]
    (f : A → Bool) (hf : Measurable f) : Measurable (fun o : Option A => o.elim false f) := by
  have h := (hf.sumElim (measurable_const (a := false) : Measurable (fun _ : PUnit => false))).comp
    (comap_measurable (Equiv.optionEquivSumPUnit A))
  convert h using 1
  funext o
  cases o <;> rfl

theorem measurable_horizonCompletedCollection (q : Fin p.T) :
    Measurable (horizonCompletedCollection rate rewards C_star C_h q) := by
  exact (measurable_optionBoolElim (outputCollectionTag rate)
    (measurable_outputCollectionTag (p := p) rate)).comp
      (ReferenceFirstCollectionCorrectedNextPhysicalReadout.measurable_actualInput?
        rate rewards C_star C_h q)

theorem measurable_horizonCollectionContinuing (q : Fin p.T) :
    Measurable (horizonCollectionContinuing rate rewards C_star C_h q) := by
  have hpair : Measurable (fun x : Input =>
      (inputCollectionTag rate x, outputCollectionTag rate x)) :=
    (measurable_inputCollectionTag (p := p) rate).prodMk
      (measurable_outputCollectionTag (p := p) rate)
  have hand : Measurable (fun x : Input =>
      inputCollectionTag rate x && outputCollectionTag rate x) :=
    (measurable_of_finite (fun bits : Bool × Bool => bits.1 && bits.2)).comp hpair
  exact (measurable_optionBoolElim _ hand).comp
    (ReferenceFirstCollectionCorrectedNextPhysicalReadout.measurable_actualInput?
      rate rewards C_star C_h q)

theorem measurable_collectionContinuingLength (q : Fin p.T) :
    Measurable (collectionContinuingLength rate rewards C_star C_h q) := by
  have hflags : Measurable (fun z : X => fun i : Fin (p.T - (q.val + 1)) =>
      horizonCollectionContinuing rate rewards C_star C_h
        ⟨q.val + 1 + i.val, by have := i.isLt; omega⟩ z) :=
    Measurable.of_eval (fun _ => measurable_horizonCollectionContinuing
      rate rewards C_star C_h _)
  exact (measurable_of_countable (fun flags : Fin (p.T - (q.val + 1)) → Bool =>
    ((List.ofFn flags).takeWhile id).length)).comp hflags

theorem measurable_firstPrefixQueueCode? (t : Fin p.T) (j k : ℕ) :
    Measurable (fun z => firstPrefixQueueCode? rate rewards C_star C_h t z j k) := by
  let queue := fun q : Fin p.T => sourcePrefixQueue? rate rewards C_star C_h q k
  have hn := ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.measurable_continuingLength
    rate rewards C_star C_h t
  have hcut : Measurable (fun z : X => fun q : Fin p.T =>
      ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.horizonCutoff
        rate rewards C_star C_h q z) :=
    Measurable.of_eval (fun q =>
      ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.measurable_horizonCutoff
        rate rewards C_star C_h q)
  have hcomplete : Measurable (fun z : X => fun q : Fin p.T =>
      horizonCompletedCollection rate rewards C_star C_h q z) :=
    Measurable.of_eval (fun q => measurable_horizonCompletedCollection
      rate rewards C_star C_h q)
  have hcontinue : Measurable (fun z : X => fun q : Fin p.T =>
      horizonCollectionContinuing rate rewards C_star C_h q z) :=
    Measurable.of_eval (fun q => measurable_horizonCollectionContinuing
      rate rewards C_star C_h q)
  have hqueue : Measurable (fun z : X => fun q : Fin p.T => queue q z) :=
    Measurable.of_eval (fun q => measurable_sourcePrefixQueue? rate rewards C_star C_h q k)
  have hdata := hn.prodMk (hcut.prodMk (hcomplete.prodMk (hcontinue.prodMk hqueue)))
  have hcode : Measurable (fun data : ℕ × ((Fin p.T → Bool) × ((Fin p.T → Bool) ×
      ((Fin p.T → Bool) × (Fin p.T → Option (Fin p.K × ℕ))))) =>
      firstPrefixQueueCodeEval t j data.1 data.2.1 data.2.2.1
        data.2.2.2.1 data.2.2.2.2) := Measurable.of_discrete
  exact hcode.comp hdata

private theorem actualRecord_eq_sourceIndex (q : Fin p.T) (i : ℕ) (z : X)
    (hi : sourceStart rate rewards C_star C_h z + i = q.val) :
    ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h q z =
      (sourceRecords rate rewards C_star C_h z)[i]? := by
  have hs : sourceStart rate rewards C_star C_h z ≤ q.val := by omega
  unfold ReferenceSourcePrefixHistoryFiltration.actualRecord
  change (if sourceStart rate rewards C_star C_h z ≤ q.val then
      (sourceRecords rate rewards C_star C_h z)[q.val -
        sourceStart rate rewards C_star C_h z]? else none) = _
  rw [ite_eq_left hs]
  have hindex : q.val - sourceStart rate rewards C_star C_h z = i := by omega
  rw [hindex]

private theorem horizonCompletedCollection_eq_record (q : Fin p.T) (z : X) (r : Record)
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h q z = some r) :
    horizonCompletedCollection rate rewards C_star C_h q z =
      (ReferenceCollectionSegmentExtraction.extractRound r).isSome := by
  simp [horizonCompletedCollection,
    ReferenceFirstCollectionCorrectedNextPhysicalReadout.actualInput?, hr,
    extractRound_isSome_eq_outputCollectionTag rate r]

private theorem liveChoice_initializer_isSome (x : Input)
    (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
    (base : Fin (p.m - 1) → ℕ) (context : ReferenceCollectionSegmentExtraction.Choice rate)
    (hstate : x.state.coordinator = .live registers owned base)
    (hchoice : ReferenceCollectionSegmentExtraction.choice x = some context) :
    context.initializer.isSome = true := by
  have hprep : (ReferenceActivePhysicalStep.prepare x).coordinator =
      .live registers owned base
        (CoordinatorRoundDispatch.dispatchLive
          (ReferenceActivePhysicalStep.liveInput x registers owned base)) := by
    simp only [ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch,
      hstate, CoordinatorRoundDispatch.dispatch]
    rfl
  unfold ReferenceCollectionSegmentExtraction.choice at hchoice
  split at hchoice
  · contradiction
  next _ =>
    rw [hprep] at hchoice
    cases hd : CoordinatorRoundDispatch.dispatchLive
        (ReferenceActivePhysicalStep.liveInput x registers owned base) <;>
      simp only [hd, ReferenceCollectionSegmentExtraction.choiceOfCut, reduceCtorEq] at hchoice
    next =>
      cases Option.some.inj hchoice
      rfl

/-- A continuing completed collection record has both the incoming and
outgoing collection tags. -/
theorem continuing_eq_collectionTags (r : Record) :
    ReferenceCollectionSegmentExtraction.continuing r =
      (inputCollectionTag rate r.input && outputCollectionTag rate r.input) := by
  cases he : ReferenceCollectionSegmentExtraction.extractRound r with
  | none =>
      rw [← extractRound_isSome_eq_outputCollectionTag rate r]
      simp [ReferenceCollectionSegmentExtraction.continuing, he]
  | some done =>
      have hchecked := ReferenceCollectionSegmentExtraction.actual_collection_round_checked
        r done he
      rcases hchecked with ⟨hchoice, _, _, hnextExists⟩
      have hin : done.context.initializer.isNone = inputCollectionTag rate r.input := by
        cases hstate : r.input.state.coordinator with
        | collection payload ledger saved =>
            have hpre := ReferenceCollectionSegmentExtraction.choice_collection_pre
              r.input payload ledger saved done.context hstate hchoice
            rw [inputCollectionTag_eq_configuration rate r.input, hstate]
            simp [configurationCollectionTag, hpre.2]
        | first =>
            have hfalse : False := by
              have hc := ReferenceCollectionSegmentExtraction.choice_first_none
                r.input hstate
              rw [hc] at hchoice
              simp at hchoice
            exact False.elim hfalse
        | live registers owned base =>
            have hinit := liveChoice_initializer_isSome rate r.input registers owned base
              done.context hstate hchoice
            rw [inputCollectionTag_eq_configuration rate r.input, hstate]
            simp [configurationCollectionTag, hinit]
        | dagger =>
            have hfalse : False := by
              unfold ReferenceCollectionSegmentExtraction.choice at hchoice
              split at hchoice
              · contradiction
              next hselection =>
                change ReferenceCollectionSegmentExtraction.choiceOfCut
                  (ReferenceActivePhysicalStep.dispatch r.input) = some done.context at hchoice
                rw [ReferenceActivePhysicalStep.dispatch_dagger r.input hstate] at hchoice
                simp [ReferenceCollectionSegmentExtraction.choiceOfCut] at hchoice
            exact False.elim hfalse
      rw [ReferenceCollectionSegmentExtraction.continuing, he]
      have hout : outputCollectionTag rate r.input = true := by
        rw [← extractRound_isSome_eq_outputCollectionTag rate r]
        simp [he]
      simp [hin, hout]

private theorem horizonCollectionContinuing_eq_record (q : Fin p.T) (z : X) (r : Record)
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h q z = some r) :
    horizonCollectionContinuing rate rewards C_star C_h q z =
      ReferenceCollectionSegmentExtraction.continuing r := by
  simp only [horizonCollectionContinuing,
    ReferenceFirstCollectionCorrectedNextPhysicalReadout.actualInput?, hr,
    Option.map_some, Option.elim_some]
  rw [continuing_eq_collectionTags rate r]

private theorem continuingTest_eq_isContinuingChosen (r : Record) :
    ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest r =
      ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen r := by
  unfold ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest
    ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen
  cases r.output.preparation.coordinator with
  | live registers owned base outcome => cases outcome <;> rfl
  | first outcome => rfl
  | collection payload ledger clock cutoff outcome => rfl
  | invalidCollectionCutoff => rfl
  | dagger => rfl

private theorem liveTail_eq_continuingPrefix (z : X) :
    liveTail rate rewards C_star C_h z =
      ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
        rate rewards C_star C_h z (birthIndex rate rewards C_star C_h z + 1) := by
  simp only [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail,
    ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords,
    ReferenceFirstReplacementLiveFollowerPrefix.continuingTail,
    ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix]
  have hp : (fun r : Record =>
      ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest r) =
      (fun r : Record => ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen r) := by
    funext r
    exact continuingTest_eq_isContinuingChosen rate r
  exact (congrArg (fun pred : Record → Bool => List.takeWhile pred
    (List.drop (birthIndex rate rewards C_star C_h z + 1)
      (sourceRecords rate rewards C_star C_h z))) hp).symm


/-- A literal cutoff dispatch supplies its own choice and initializer, before
any recorder, UP decoder, or FINISH result is inspected. -/
private theorem cutoff_choice (x : Input)
    (hcut : ReferenceCollectionPhaseHistory.cutoffChosen x = true) :
    ∃ c : ReferenceCollectionSegmentExtraction.Choice rate,
      ReferenceCollectionSegmentExtraction.choice x = some c ∧
      c.initializer.isSome = true := by
  unfold ReferenceCollectionPhaseHistory.cutoffChosen at hcut
  cases hd : (ReferenceActivePhysicalStep.prepare x).coordinator with
  | live r q base outcome =>
      cases outcome <;> simp only [hd, Bool.false_eq_true] at hcut
      next dispatched hstart ledger hinit heq hdomain hclock hpending hno selected =>
        have hselection : (ReferenceActivePhysicalStep.prepare x).coordinator.selection ≠ none := by
          simp [hd, ReferenceActivePhysicalStep.DispatchCut.selection,
            ReferenceActivePhysicalStep.selectionAt]
        unfold ReferenceCollectionSegmentExtraction.choice
        rw [ite_eq_right hselection, hd]
        exact ⟨_, rfl, rfl⟩
  | first outcome => simp only [hd, Bool.false_eq_true] at hcut
  | collection payload ledger clock cutoff outcome => simp only [hd, Bool.false_eq_true] at hcut
  | invalidCollectionCutoff => simp only [hd, Bool.false_eq_true] at hcut
  | dagger => simp only [hd, Bool.false_eq_true] at hcut

private theorem horizonCutoff_eq_record (q : Fin p.T) (z : X) (r : Record)
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h q z = some r) :
    ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.horizonCutoff
      rate rewards C_star C_h q z = ReferenceCollectionPhaseHistory.cutoffChosen r.input := by
  unfold ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.horizonCutoff
    ReferenceFirstCollectionCorrectedNextPhysicalReadout.actualInput?
  simp only [hr, Option.map_some, Option.bind_some]
  unfold ReferenceFirstCollectionRenewalNextRecordingPriorView.dispatchTag
    ReferenceCollectionPhaseHistory.cutoffChosen
    ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.chosenCutoffTag
  have hp : (ReferenceActivePhysicalStep.prepare r.input).coordinator =
      ReferenceActivePhysicalStep.dispatch r.input := rfl
  rw [hp]
  cases ReferenceActivePhysicalStep.dispatch r.input with
  | live registers owned base outcome => cases outcome <;> rfl
  | first outcome => rfl
  | collection payload ledger clock cutoff outcome => rfl
  | invalidCollectionCutoff => rfl
  | dagger => rfl

/-- The finite calendar following any existing suffix date is the same list
of continuing flags as the literal physical suffix. -/
private theorem collectionFlags_actual (q : Fin p.T) (i : ℕ) (z : X)
    (hi : sourceStart rate rewards C_star C_h z + i = q.val) :
    (List.ofFn fun h : Fin (p.T - (q.val + 1)) =>
      horizonCollectionContinuing rate rewards C_star C_h
        ⟨q.val + 1 + h.val, by have := h.isLt; omega⟩ z) =
      ((sourceRecords rate rewards C_star C_h z).drop (i + 1)).map
        ReferenceCollectionSegmentExtraction.continuing := by
  have hlen := ReferenceCompletePhysicalHistory.completeSuffixRecords_length
    rate z rewards C_star C_h
  change (sourceRecords rate rewards C_star C_h z).length =
    p.T - sourceStart rate rewards C_star C_h z at hlen
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_map, List.length_drop]
    omega
  · intro h hh hh'
    have hhT : h < p.T - (q.val + 1) := by simpa only [List.length_ofFn] using hh
    let date : Fin p.T := ⟨q.val + 1 + h, by omega⟩
    have hlookup : i + 1 + h < (sourceRecords rate rewards C_star C_h z).length := by
      simp only [List.length_map, List.length_drop] at hh'
      omega
    have hr := actualRecord_eq_sourceIndex rate rewards C_star C_h date (i + 1 + h) z
      (by dsimp only [date]; omega)
    rw [List.getElem?_eq_getElem hlookup] at hr
    simp only [List.getElem_ofFn, List.getElem_map, List.getElem_drop]
    exact horizonCollectionContinuing_eq_record rate rewards C_star C_h date z _ hr

private theorem segmentAt_cutoff_length (R : List Record) (i : ℕ) (entry : Record)
    (hr : R[i]? = some entry)
    (hcut : ReferenceCollectionPhaseHistory.cutoffChosen entry.input = true) :
    ∃ seg : ReferenceCollectionSegmentExtraction.Segment rate,
      ReferenceCollectionSegmentExtraction.segmentAt R i = some seg ∧
      seg.records.length =
        if (ReferenceCollectionSegmentExtraction.extractRound entry).isSome then
          1 + ((R.drop (i + 1)).takeWhile ReferenceCollectionSegmentExtraction.continuing).length
        else 0 := by
  classical
  obtain ⟨c, hc, hinit⟩ := cutoff_choice rate entry.input hcut
  have hi := (List.getElem?_eq_some_iff.mp hr).1
  have he := (List.getElem?_eq_some_iff.mp hr).2
  have hdrop : R.drop i = entry :: R.drop (i + 1) := by
    rw [List.drop_eq_getElem_cons hi, he]
  unfold ReferenceCollectionSegmentExtraction.segmentAt
  rw [hdrop]
  simp only [ReferenceCollectionSegmentExtraction.segment, hc, Option.map_some]
  split
  · refine ⟨⟨entry, c, entry :: (R.drop (i + 1)).takeWhile
        ReferenceCollectionSegmentExtraction.continuing,
        (R.drop (i + 1)).dropWhile ReferenceCollectionSegmentExtraction.continuing⟩, ?_, ?_⟩
    · simp only [Option.bind_some, hinit, or_true, ↓reduceIte]
    · simp only [List.length_cons, Nat.add_comm]
  · refine ⟨⟨entry, c, [], entry :: R.drop (i + 1)⟩, ?_, rfl⟩
    simp only [Option.bind_some, hinit, or_true, ↓reduceIte]


/-- On the original corrected cell the literal first collection segment and
its optional first excluded record are observed at exactly the calendar dates
of the finite Borel code. No success, queue-truth, or future-reception premise
is used. -/
theorem firstCell_nativeUpPrefixObservation (u t : Fin p.T) (z : X)
    (hz : z ∈ correctedCell rate rewards C_star C_h u t) :
    ∀ j k : ℕ, firstPrefixQueueAt rate rewards C_star C_h z j k =
      firstPrefixQueueCode? rate rewards C_star C_h t z j k := by
  intro j k
  classical
  let R := sourceRecords rate rewards C_star C_h z
  let s := sourceStart rate rewards C_star C_h z
  let e := birthIndex rate rewards C_star C_h z + 1 +
    (liveTail rate rewards C_star C_h z).length
  let d := t.val + 1 + (liveTail rate rewards C_star C_h z).length
  have hbirth := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.firstCell_birth_time
    rate rewards C_star C_h u t z hz
  have hde : s + e = d := by dsimp only [s, e, d]; omega
  have hlen := ReferenceCompletePhysicalHistory.completeSuffixRecords_length
    rate z rewards C_star C_h
  change R.length = p.T - s at hlen
  have hn := ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.continuingLength_actual
    rate rewards C_star C_h u t z hz
  unfold firstPrefixQueueCode? firstPrefixQueueCodeEval
  rw [hn]
  change firstPrefixQueueAt rate rewards C_star C_h z j k =
    if hd : d < p.T then
      if ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.horizonCutoff
          rate rewards C_star C_h ⟨d, hd⟩ z then
        let length := if horizonCompletedCollection rate rewards C_star C_h ⟨d, hd⟩ z then
            1 + ((List.ofFn fun i : Fin (p.T - (d + 1)) =>
              horizonCollectionContinuing rate rewards C_star C_h
                ⟨d + 1 + i.val, by have := i.isLt; omega⟩ z).takeWhile id).length
          else 0
        if j ≤ length then
          if hj : d + j < p.T then
            sourcePrefixQueue? rate rewards C_star C_h ⟨d + j, hj⟩ k z
          else none
        else none
      else none
    else none
  by_cases hd : d < p.T
  · rw [dite_eq_left hd]
    let date : Fin p.T := ⟨d, hd⟩
    have he : e < R.length := by omega
    let entry : Record := R[e]
    have hentry : R[e]? = some entry := List.getElem?_eq_getElem he
    have hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
        rate rewards C_star C_h date z = some entry := by
      rw [actualRecord_eq_sourceIndex rate rewards C_star C_h date e z hde]
      exact hentry
    have hcut := horizonCutoff_eq_record rate rewards C_star C_h date z entry hr
    change firstPrefixQueueAt rate rewards C_star C_h z j k =
      if ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.horizonCutoff
          rate rewards C_star C_h date z then _ else none
    rw [hcut]
    unfold firstPrefixQueueAt
    change (match R[e]? with
      | none => none
      | some entry => if ReferenceCollectionPhaseHistory.cutoffChosen entry.input then
          match ReferenceCollectionSegmentExtraction.segmentAt R e with
          | none => none
          | some segment => if j ≤ segment.records.length then
              (R[e + j]?).bind (fun record => recordPrefixQueue? rate record k)
            else none
        else none) = _
    rw [hentry]
    dsimp only
    by_cases hc : ReferenceCollectionPhaseHistory.cutoffChosen entry.input = true
    · rw [ite_eq_left hc, ite_eq_left hc]
      obtain ⟨seg, hseg, hlength⟩ := segmentAt_cutoff_length rate R e entry hentry hc
      rw [hseg]
      dsimp only
      have hcomplete := horizonCompletedCollection_eq_record
        rate rewards C_star C_h date z entry hr
      have hflags := collectionFlags_actual rate rewards C_star C_h date e z hde
      have hlengthCode : seg.records.length =
          if horizonCompletedCollection rate rewards C_star C_h date z then
            1 + ((List.ofFn fun i : Fin (p.T - (d + 1)) =>
              horizonCollectionContinuing rate rewards C_star C_h
                ⟨d + 1 + i.val, by have := i.isLt; omega⟩ z).takeWhile id).length
          else 0 := by
        rw [hcomplete, hlength]
        rw [hflags, List.takeWhile_map, List.length_map]
        rfl
      rw [← hlengthCode]
      by_cases hj : j ≤ seg.records.length
      · rw [ite_eq_left hj, ite_eq_left hj]
        by_cases hjT : d + j < p.T
        · rw [dite_eq_left hjT]
          unfold sourcePrefixQueue?
          rw [actualRecord_eq_sourceIndex rate rewards C_star C_h
            ⟨d + j, hjT⟩ (e + j) z (by dsimp only; omega)]
        · rw [dite_eq_right hjT]
          have hnone : R[e + j]? = none := by
            apply List.getElem?_eq_none_iff.mpr
            omega
          rw [hnone, Option.bind_none]
      · rw [ite_eq_right hj, ite_eq_right hj]
    · rw [ite_eq_right hc, ite_eq_right hc]
  · rw [dite_eq_right hd]
    have hnone : R[e]? = none := by
      apply List.getElem?_eq_none_iff.mpr
      omega
    unfold firstPrefixQueueAt
    change (match R[e]? with
      | none => none
      | some entry => _) = none
    rw [hnone]


/-- A computed native-UP queue endpoint in the same first corrected
collection segment, including its optional first excluded record. -/
def firstNativeUpPrefixEvent (u t : Fin p.T) : Set X :=
  {z | z ∈ correctedCell rate rewards C_star C_h u t ∧
    ∃ j k : ℕ, ∃ a : Fin p.K, ∃ q : ℕ,
      firstPrefixQueueAt rate rewards C_star C_h z j k = some (a, q) ∧
      (q : ℝ) / (rate.n : ℝ) > 1 / (32 * rate.eta.val)}

/-- The event is identified with its original-calendar Borel code only on
the same corrected cell; no arbitrary segment or matching trace is supplied. -/
theorem firstNativeUpPrefixEvent_eq_observed (u t : Fin p.T) :
    firstNativeUpPrefixEvent rate rewards C_star C_h u t =
      correctedCell rate rewards C_star C_h u t ∩
        {z | ∃ j k : ℕ, ∃ a : Fin p.K, ∃ q : ℕ,
          firstPrefixQueueCode? rate rewards C_star C_h t z j k = some (a, q) ∧
          (q : ℝ) / (rate.n : ℝ) > 1 / (32 * rate.eta.val)} := by
  ext z
  constructor
  · rintro ⟨hz, j, k, a, q, hqueue, hthreshold⟩
    refine ⟨hz, j, k, a, q, ?_, hthreshold⟩
    rw [← firstCell_nativeUpPrefixObservation rate rewards C_star C_h u t z hz j k]
    exact hqueue
  · rintro ⟨hz, j, k, a, q, hqueue, hthreshold⟩
    refine ⟨hz, j, k, a, q, ?_, hthreshold⟩
    rw [firstCell_nativeUpPrefixObservation rate rewards C_star C_h u t z hz j k]
    exact hqueue

/-- Ambient Borelness on the original continuous source space. This is not
a factorization through a pre-round filtration or a moment/law statement. -/
theorem measurableSet_firstNativeUpPrefixEvent (u t : Fin p.T) :
    MeasurableSet (firstNativeUpPrefixEvent rate rewards C_star C_h u t) := by
  rw [firstNativeUpPrefixEvent_eq_observed]
  apply (ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.measurableSet_correctedCell
    rate rewards C_star C_h u t).inter
  simp only [Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro j
  apply MeasurableSet.iUnion
  intro k
  apply MeasurableSet.iUnion
  intro a
  apply MeasurableSet.iUnion
  intro q
  by_cases hq : (q : ℝ) / (rate.n : ℝ) > 1 / (32 * rate.eta.val)
  · simp only [hq, and_true]
    exact measurableSet_eq_fun
      (measurable_firstPrefixQueueCode? rate rewards C_star C_h t j k)
      (measurable_const (a := some (a, q)))
  · simp only [hq, and_false, Set.ofPred_false]
    exact MeasurableSet.empty


end Bandits.Support.ReferenceFirstCorrectedNativeUpComputedPrefixObservation

end noncomputable section
