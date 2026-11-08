/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.OrdinaryActivePhysicalStep

/-!
# The ordinary coordinator's local preparation and observation interface

Sources: `sources/zip4/manuscript/06_interruptions.tex:240-296`,
`05_binary_transport.tex:74-124`, `07_public_setup.tex:55-114`,
`appendix_a_local_protocol.tex:6-24`, and
`appendix_b_communication.tex:94-131` (all under the same manuscript directory).

The primitive coordinator configuration, decoder bank, whole continuous row,
and calendar time suffice for PREPARE. Its transient result retains the original
checked dispatcher outcomes. Only OBSERVE accepts the own quantized feedback.
It composes the existing recorder, service, ordinary receiver, and finish
operations, retaining their failure behavior. Neither operation reads followers.

The lossless conversions below compare this local interface to the canonical
common-row round; they do not construct a round input or assert a feedback law.
Mixed-profile physical feedback, horizon construction, probability laws, and
manuscript regret closure remain separate obligations.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
  (RateInput Payload Ledger CoordinatorConfiguration CoordinatorObservation
   coordinatorFallback coordinatorFailure liveRegistersAt liveOwnedAt
   collectionClock sharedLedger collectionEnabled)

namespace Bandits.Support.OrdinaryCoordinatorPhysicalInterface

local instance propDecidable (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

variable {p : Parameters} {rate : RateInput p}

/-- Literal first-start adapter; the rate and exact numerator are unchanged. -/
def firstInput (rate : RateInput p) (row : CompletePublicTable.CompleteRow p)
    (time : Fin p.T) : CoordinatorRoundDispatch.FirstInput p :=
  { eta := rate.eta, eta_le_source_cap := rate.sourceCap
    n := rate.n, n_eq_eta_mul_D := rate.n_scale, time := time, row := row }

/-- Reindex the existing live registers and their owned queues at this time. -/
def liveInput (row : CompletePublicTable.CompleteRow p) (time : Fin p.T)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ) : CoordinatorRoundDispatch.LiveInput p :=
  { eta := rate.eta, registers := liveRegistersAt r time
    ownedRegisters := liveOwnedAt r owned time
    followerBaseScore := base, row := row }

/-- The collection adapter retains the actual ledger, clock, base, and bank. -/
def collectionInput (bank : CoordinatorUpReception.UpDecoderBank p)
    (row : CompletePublicTable.CompleteRow p) (time : Fin p.T)
    (payload : Payload rate) (ledger : Ledger rate)
    (clock : CoordinatorPhaseClock.ClockRegisters p) (cutoff : Fin p.T) :
    CoordinatorRoundDispatch.CollectionInput p :=
  { etaReal := rate.eta.val, etaPositive := rate.eta.property
    n := rate.n, n_cast_identity := rate.n_scale
    payload := payload, baseScores := ledger.baseScore, ledger := ledger
    clock := clock, upDecoderBank := bank
    cutoffIndex := cutoff, time := time, row := row }

/-- Existing dependent outcomes, indexed only by local transient inputs.
No second mutable clock, queue, payload, decoder, or follower store is introduced. -/
inductive Preparation (rate : RateInput p)
    (bank : CoordinatorUpReception.UpDecoderBank p)
    (row : CompletePublicTable.CompleteRow p) (time : Fin p.T) where
  | first (outcome : CoordinatorRoundDispatch.FirstOutcome (firstInput rate row time))
  | live (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
      (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
      (base : Fin (p.m - 1) → ℕ)
      (outcome : CoordinatorRoundDispatch.LiveOutcome (liveInput row time registers owned base))
  | collection (payload : Payload rate) (ledger : Ledger rate)
      (clock : CoordinatorPhaseClock.ClockRegisters p) (cutoff : Fin p.T)
      (outcome : CoordinatorRoundDispatch.CollectionOutcome
        (collectionInput bank row time payload ledger clock cutoff))
  | invalidCollectionCutoff
  | dagger

/-- Call the accepted dispatcher once at the actual phase. The ledger's
literal cutoff is checked before constructing its finite calendar index. -/
def prepareLocal (q : CoordinatorConfiguration p rate)
    (bank : CoordinatorUpReception.UpDecoderBank p)
    (row : CompletePublicTable.CompleteRow p) (time : Fin p.T) :
    Preparation rate bank row time :=
  match q with
  | .first =>
      match CoordinatorRoundDispatch.dispatch (.first (firstInput rate row time)) with
      | .first outcome => .first outcome
  | .live r owned base =>
      match CoordinatorRoundDispatch.dispatch (.live (liveInput row time r owned base)) with
      | .live outcome => .live r owned base outcome
  | .collection payload ledger savedProposal =>
      if hcutoff : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T then
        let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
        let clock := collectionClock payload ledger savedProposal cutoff
        match CoordinatorRoundDispatch.dispatch
            (.collection (collectionInput bank row time payload ledger clock cutoff)) with
        | .collection outcome => .collection payload ledger clock cutoff outcome
      else .invalidCollectionCutoff
  | .dagger => .dagger

/-- First PREPARE retains the complete original first outcome. -/
theorem prepareLocal_first (bank : CoordinatorUpReception.UpDecoderBank p)
    (row : CompletePublicTable.CompleteRow p) (time : Fin p.T) :
    prepareLocal (rate := rate) .first bank row time =
      .first (CoordinatorRoundDispatch.dispatchFirst (firstInput rate row time)) := rfl

/-- Live PREPARE retains the complete original continuing/cutoff/failure outcome. -/
theorem prepareLocal_live (bank : CoordinatorUpReception.UpDecoderBank p)
    (row : CompletePublicTable.CompleteRow p) (time : Fin p.T)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ) :
    prepareLocal (.live r owned base) bank row time =
      .live r owned base (CoordinatorRoundDispatch.dispatchLive (liveInput row time r owned base)) := rfl

/-- On the literal range-check branch, the cutoff, clock, and entire original
collection outcome are retained. The hypothesis is exactly that branch test. -/
theorem prepareLocal_collection (bank : CoordinatorUpReception.UpDecoderBank p)
    (row : CompletePublicTable.CompleteRow p) (time : Fin p.T)
    (payload : Payload rate) (ledger : Ledger rate)
    (savedProposal : Option (Fin p.T × Bool))
    (hcutoff : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T) :
    let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
    let clock := collectionClock payload ledger savedProposal cutoff
    prepareLocal (.collection payload ledger savedProposal) bank row time =
      .collection payload ledger clock cutoff
        (CoordinatorRoundDispatch.dispatchCollection
          (collectionInput bank row time payload ledger clock cutoff)) := by
  dsimp only
  simp only [prepareLocal, dite_eq_left hcutoff, CoordinatorRoundDispatch.dispatch]
  rfl

/-- The failed range check remains a distinct raw failure, with no dispatcher
call. The hypothesis is exactly the failed local test. -/
theorem prepareLocal_invalidCollectionCutoff (bank : CoordinatorUpReception.UpDecoderBank p)
    (row : CompletePublicTable.CompleteRow p) (time : Fin p.T)
    (payload : Payload rate) (ledger : Ledger rate)
    (savedProposal : Option (Fin p.T × Bool))
    (hcutoff : ¬ (1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T)) :
    prepareLocal (.collection payload ledger savedProposal) bank row time =
      .invalidCollectionCutoff := by
  simp only [prepareLocal, dite_eq_right hcutoff]

theorem prepareLocal_dagger (bank : CoordinatorUpReception.UpDecoderBank p)
    (row : CompletePublicTable.CompleteRow p) (time : Fin p.T) :
    prepareLocal (rate := rate) .dagger bank row time = .dagger := rfl

/-- Same-calendar choice evidence before any observation is supplied. -/
structure Selection (rate : RateInput p)
    (row : CompletePublicTable.CompleteRow p) (time : Fin p.T) where
  view : ReferenceDownReception.ChoiceTimeView p rate.eta
  started : CoordinatorPhaseClock.StartRoundResult p
  pending_eq : view.pendingAtChoice = started.pending
  cutoff_eq : view.cutoff = CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u
  arm : Fin p.K
  choice_eq : CoordinatorLocalArmChoice.coordinatorArmChoice view.payload
    view.pendingAtChoice view.cutoff time view.complementWeights row = some arm

/-- The original alignment check, applied to the retained actual selection. -/
def selectionAt (row : CompletePublicTable.CompleteRow p) (time : Fin p.T)
    (payload : Payload rate) (started : CoordinatorPhaseClock.StartRoundResult p)
    (choiceTime : Fin p.T) (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ)
    (selection : CoordinatorRoundDispatch.ArmSelection payload started choiceTime weights row) :
    Option (Selection rate row time) := by
  classical
  if htime : choiceTime = time then
    exact some {
      view := {
        payload := payload
        pendingAtChoice := started.pending
        cutoff := CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u
        complementWeights := weights }
      started := started, pending_eq := rfl, cutoff_eq := rfl
      arm := selection.arm
      choice_eq := by simpa only [htime] using selection.armChoice_eq }
  else exact none

variable {bank : CoordinatorUpReception.UpDecoderBank p}
variable {row : CompletePublicTable.CompleteRow p} {time : Fin p.T}

/-- Project the original selected payload, start result, and weights, including
continuing collection and the changed first-cutoff clock. -/
def Preparation.selection (cut : Preparation rate bank row time) :
    Option (Selection rate row time) := by
  classical
  match cut with
  | .first (.chosen installed selected) =>
      exact selectionAt row time installed.registers.payload installed.startRoundResult
        installed.registers.time installed.registers.complementWeights selected
  | .live r q base (.continuingChosen dispatched _ _ selected) =>
      exact selectionAt row time r.payload dispatched.startResult time
        (liveRegistersAt r time).complementWeights selected
  | .live r q base (.cutoffChosen dispatched _ _ _ _ _ _ _ _ selected) =>
      exact selectionAt row time r.payload dispatched.startResult time
        (liveRegistersAt r time).complementWeights selected
  | .collection payload ledger clock cutoff (.continuing _ prepared boundary _) =>
      let source := collectionInput bank row time payload ledger clock cutoff
      have hcutoff : CoordinatorLiveChoiceRecorderStep.cutoffFromClock p prepared.clockStarted.clock.u =
          some (CoordinatorCollectionUpRoundStep.localCutoff cutoff) := by
        rw [prepared.clockStarted_frame.1]
        change CoordinatorLiveChoiceRecorderStep.cutoffFromClock p clock.u = _
        have hc : clock.u = some cutoff := prepared.inputsValid.clock_cutoff_eq
        rw [hc]
        rfl
      exact some {
        view := {
          payload := payload
          pendingAtChoice := prepared.clockStarted.pending
          cutoff := CoordinatorLiveChoiceRecorderStep.cutoffFromClock p prepared.clockStarted.clock.u
          complementWeights := CoordinatorCollectionInteractive.PreObservationInputs.weights source
            prepared.inputsValid.ledger_valid prepared.inputsValid.assignment_eq }
        started := prepared.clockStarted, pending_eq := rfl, cutoff_eq := rfl
        arm := prepared.arm
        choice_eq := by
          change CoordinatorLocalArmChoice.coordinatorArmChoice payload
            prepared.clockStarted.pending _ time _ row = some prepared.arm
          rw [hcutoff]
          exact prepared.armChoice_eq }
  | .collection _ _ _ _
      (.laterChosen _ _ started _ instruction _ _ _ _ installed selected) =>
      exact selectionAt row time installed.registers.payload started instruction.time
        installed.registers.complementWeights selected
  | _ => exact none

def Preparation.arm (cut : Preparation rate bank row time) : Fin p.K :=
  match cut.selection with
  | some selected => selected.arm
  | none => coordinatorFallback p

def Preparation.downView (cut : Preparation rate bank row time) :
    Option (ReferenceDownReception.ChoiceTimeView p rate.eta) := cut.selection.map Selection.view

/-- Every failed selection uses the source fallback and exposes no DOWN view.
The only hypothesis is the actual local selection result. -/
theorem Preparation.fallback_of_selection_none (cut : Preparation rate bank row time)
    (hselection : cut.selection = none) :
    cut.arm = coordinatorFallback p ∧ cut.downView = none := by
  simp only [Preparation.arm, Preparation.downView, hselection, Option.map_none,
    and_self]

/-- The primitive first input is definitionally the canonical first input. -/
theorem firstInput_specialization (x : ReferenceActivePhysicalStep.RoundInput p rate) :
    firstInput rate x.row x.time = ReferenceActivePhysicalStep.firstInput x := rfl

/-- All live registers and owned fields specialize literally. -/
theorem liveInput_specialization (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ) :
    liveInput x.row x.time r owned base =
      ReferenceActivePhysicalStep.liveInput x r owned base := rfl

/-- Collection specialization preserves every actual input field. -/
theorem collectionInput_specialization (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : Payload rate) (ledger : Ledger rate)
    (clock : CoordinatorPhaseClock.ClockRegisters p) (cutoff : Fin p.T) :
    collectionInput x.state.upDecoderBank x.row x.time payload ledger clock cutoff =
      ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff := rfl

/-- Lossless reindexing of the wrapper, retaining each existing dependent
outcome verbatim. This is not equality between differently indexed cut types. -/
def Preparation.toCanonical {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (cut : Preparation rate x.state.upDecoderBank x.row x.time) :
    ReferenceActivePhysicalStep.DispatchCut x :=
  match cut with
  | .first outcome => .first outcome
  | .live r owned base outcome => .live r owned base outcome
  | .collection payload ledger clock cutoff outcome =>
      .collection payload ledger clock cutoff outcome
  | .invalidCollectionCutoff => .invalidCollectionCutoff
  | .dagger => .dagger

/-- Inverse reindexing; no outcome is erased or reconstructed. -/
def ofCanonical {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (cut : ReferenceActivePhysicalStep.DispatchCut x) :
    Preparation rate x.state.upDecoderBank x.row x.time :=
  match cut with
  | .first outcome => .first outcome
  | .live r owned base outcome => .live r owned base outcome
  | .collection payload ledger clock cutoff outcome =>
      .collection payload ledger clock cutoff outcome
  | .invalidCollectionCutoff => .invalidCollectionCutoff
  | .dagger => .dagger

theorem toCanonical_ofCanonical {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (cut : ReferenceActivePhysicalStep.DispatchCut x) :
    (ofCanonical cut).toCanonical = cut := by cases cut <;> rfl

theorem ofCanonical_toCanonical {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (cut : Preparation rate x.state.upDecoderBank x.row x.time) :
    ofCanonical cut.toCanonical = cut := by cases cut <;> rfl

/-- Complete raw dispatch correspondence, including all failure tags and all
retained installations, selections, weights, ledgers, and StartRound results. -/
theorem prepareLocal_specialization (x : ReferenceActivePhysicalStep.RoundInput p rate) :
    prepareLocal x.state.coordinator x.state.upDecoderBank x.row x.time =
      ofCanonical (ReferenceActivePhysicalStep.dispatch x) := by
  cases hq : x.state.coordinator with
  | first =>
      simp only [prepareLocal, ReferenceActivePhysicalStep.dispatch, hq,
        CoordinatorRoundDispatch.dispatch]
      rfl
  | live r owned base =>
      simp only [prepareLocal, ReferenceActivePhysicalStep.dispatch, hq,
        CoordinatorRoundDispatch.dispatch]
      rfl
  | collection payload ledger savedProposal =>
      simp only [prepareLocal, ReferenceActivePhysicalStep.dispatch, hq]
      split
      · simp only [CoordinatorRoundDispatch.dispatch]
        rfl
      · rfl
  | dagger => simp only [prepareLocal, ReferenceActivePhysicalStep.dispatch, hq, ofCanonical]

theorem prepareLocal_toCanonical (x : ReferenceActivePhysicalStep.RoundInput p rate) :
    (prepareLocal x.state.coordinator x.state.upDecoderBank x.row x.time).toCanonical =
      (ReferenceActivePhysicalStep.prepare x).coordinator := by
  rw [prepareLocal_specialization, toCanonical_ofCanonical]
  rfl

/-- Reindex the same choice evidence; its original start result is retained. -/
def Selection.toCanonical {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (selected : Selection rate x.row x.time) : ReferenceActivePhysicalStep.Selection x :=
  { view := selected.view, started := selected.started
    pending_eq := selected.pending_eq, cutoff_eq := selected.cutoff_eq
    arm := selected.arm, choice_eq := selected.choice_eq }

theorem selectionAt_specialization (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : Payload rate) (started : CoordinatorPhaseClock.StartRoundResult p)
    (choiceTime : Fin p.T) (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ)
    (selection : CoordinatorRoundDispatch.ArmSelection payload started choiceTime weights x.row) :
    (selectionAt x.row x.time payload started choiceTime weights selection).map
        Selection.toCanonical =
      ReferenceActivePhysicalStep.selectionAt x payload started choiceTime weights selection := by
  unfold selectionAt ReferenceActivePhysicalStep.selectionAt
  split <;> rfl

/-- Selection correspondence on the entire raw outcome carrier. -/
theorem selection_ofCanonical {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (cut : ReferenceActivePhysicalStep.DispatchCut x) :
    (ofCanonical cut).selection.map Selection.toCanonical = cut.selection := by
  cases cut with
  | first outcome =>
      cases outcome <;> first | rfl | exact selectionAt_specialization _ _ _ _ _ _
  | live r owned base outcome =>
      cases outcome <;> first | rfl | exact selectionAt_specialization _ _ _ _ _ _
  | collection payload ledger clock cutoff outcome =>
      cases outcome <;> first | rfl | exact selectionAt_specialization _ _ _ _ _ _
  | invalidCollectionCutoff => rfl
  | dagger => rfl

theorem selection_none_ofCanonical {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (cut : ReferenceActivePhysicalStep.DispatchCut x) :
    (ofCanonical cut).selection = none ↔ cut.selection = none := by
  rw [← selection_ofCanonical cut]
  exact Option.map_eq_none_iff.symm

theorem arm_ofCanonical {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (cut : ReferenceActivePhysicalStep.DispatchCut x) :
    (ofCanonical cut).arm = cut.arm := by
  have h := selection_ofCanonical cut
  unfold Preparation.arm ReferenceActivePhysicalStep.DispatchCut.arm
  rw [← h]
  cases (ofCanonical cut).selection <;> rfl

theorem downView_ofCanonical {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (cut : ReferenceActivePhysicalStep.DispatchCut x) :
    (ofCanonical cut).downView = cut.downView := by
  unfold Preparation.downView ReferenceActivePhysicalStep.DispatchCut.downView
  rw [← selection_ofCanonical cut]
  cases (ofCanonical cut).selection <;> rfl

/-- The own arm is fixed from local inputs, before feedback is supplied. -/
theorem prepareLocal_arm (x : ReferenceActivePhysicalStep.RoundInput p rate) :
    (prepareLocal x.state.coordinator x.state.upDecoderBank x.row x.time).arm =
      (ReferenceActivePhysicalStep.prepare x).coordinator.arm := by
  rw [prepareLocal_specialization, arm_ofCanonical]
  rfl

theorem prepareLocal_downView (x : ReferenceActivePhysicalStep.RoundInput p rate) :
    (prepareLocal x.state.coordinator x.state.upDecoderBank x.row x.time).downView =
      (ReferenceActivePhysicalStep.prepare x).coordinator.downView := by
  rw [prepareLocal_specialization, downView_ofCanonical]
  rfl

/-- Literal live recorder input using only the already chosen own arm and Y. -/
def liveRecordingInput (row : CompletePublicTable.CompleteRow p) (time : Fin p.T)
    (arm : Fin p.K) (Y : Fin (D p + 1))
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (started : CoordinatorPhaseClock.StartRoundResult p) :
    CoordinatorRecorderComplementBridge.Input r.payload := {
  currentWeights := r.complementWeights
  time := time
  gridBoundary := started.clock.g
  row := row
  ownArm := arm
  observation := Y
  mode := .live (decide (started.pending = ∅)) }

/-- Direct live post-choice tail. This consumes the original start result;
it creates no unchanged-clock continuation and never calls StartRound.
All scores/queues are the actual accepted service-pass outputs.
-/
def livePostChoice (bank : CoordinatorUpReception.UpDecoderBank p)
    (row : CompletePublicTable.CompleteRow p) (time : Fin p.T)
    (arm : Fin p.K) (Y : Fin (D p + 1))
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ) (started : CoordinatorPhaseClock.StartRoundResult p) :
    CoordinatorObservation p rate := by
  classical
  match CoordinatorRecorderComplementBridge.run (liveRecordingInput row time arm Y r started) with
  | none => exact coordinatorFailure bank (.live .recorderRejected) none none
  | some recording =>
      match CoordinatorLiveServiceFinish.servicePass r q recording with
      | .error reason =>
          exact coordinatorFailure bank (.live reason) (some recording) none
      | .ok serviced =>
          match CoordinatorLocalArmChoice.confirmationUpdate r.payload started.pending
              (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
              time row Y with
          | none =>
              exact coordinatorFailure bank (.live .confirmationRejected)
                (some recording) none
          | some pending =>
              match CoordinatorPhaseClock.finishRound p rate.eta.val time started.clock
                  pending row with
              | .error reason =>
                  exact coordinatorFailure bank
                    (.live (CoordinatorLiveServiceFinish.finishFailureCode reason))
                    (some recording) none
              | .ok finished =>
                  let next : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta := {
                    payload := r.payload
                    priorClock := finished.clock
                    pendingAtChoice := finished.pending
                    time := time
                    gridBoundary := finished.clock.g
                    complementScores := serviced.score }
                  exact ⟨.live next {
                      queue := serviced.queue, previousService := serviced.previousService } base,
                    bank, none, some recording, none⟩

/-- Finish the ordinary checked receiver result. Returned banks survive both
later finish failures; invalid reception retains the incoming bank. -/
def collectionFinish (bank : CoordinatorUpReception.UpDecoderBank p)
    (row : CompletePublicTable.CompleteRow p) (time : Fin p.T) (payload : Payload rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (recording : CoordinatorRecordingOperation.Output p) (cut : ReferenceActivePhysicalStep.UpCut p rate) :
    CoordinatorObservation p rate := by
  let finish := fun (ledger : Ledger rate) (receivedBank : CoordinatorUpReception.UpDecoderBank p) =>
    match CoordinatorCollectionLedger.finishRound ledger with
    | .invalid => coordinatorFailure receivedBank (.collection .ledgerFinishDomain) (some recording)
        cut.diagnostic
    | .rejected _ => coordinatorFailure receivedBank (.collection .ledgerFinishDomain) (some recording)
        cut.diagnostic
    | .success ledgerFinished =>
        match CoordinatorPhaseClock.finishRound p rate.eta.val time started.clock
            ledgerFinished.pending row with
        | .error reason => coordinatorFailure receivedBank (.collection (.clockFinish reason))
            (some recording) cut.diagnostic
        | .ok clockFinished =>
            ⟨.collection payload ledgerFinished clockFinished.clock.lastProposal, receivedBank, none,
              some recording, cut.diagnostic⟩
  exact match cut.result with
  | .invalid => coordinatorFailure bank (.collection .upReceptionDomain)
      (some recording) cut.diagnostic
  | .success (ledger, bank) => finish ledger bank
  | .rejected (ledger, bank) => finish ledger bank

/-- The collection recorder reads the same retained choice and local Y. -/
def collectionRecordingInput (row : CompletePublicTable.CompleteRow p) (time : Fin p.T)
    (arm : Fin p.K) (Y : Fin (D p + 1))
    (payload : Payload rate) (started : CoordinatorPhaseClock.StartRoundResult p)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ) :
    CoordinatorRecorderComplementBridge.Input payload := {
  currentWeights := weights
  time := time
  gridBoundary := started.clock.g
  row := row
  ownArm := arm
  observation := Y
  mode := .collection }

/-- Recorder, ledger service, ordinary unfiltered UP reception, ledger finish,
and phase finish, in source order. Decoder rejection is an ordinary result. -/
def collectionPostChoice (bank : CoordinatorUpReception.UpDecoderBank p)
    (row : CompletePublicTable.CompleteRow p) (time : Fin p.T)
    (arm : Fin p.K) (Y : Fin (D p + 1))
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ) :
    ReferenceActivePhysicalStep.CoordinatorObservation p rate := by
  classical
  match CoordinatorRecorderComplementBridge.run
      (collectionRecordingInput row time arm Y payload started weights) with
  | none =>
      exact ReferenceActivePhysicalStep.coordinatorFailure bank
        (.collection .recorderDomain) none none
  | some recording =>
      let enabled := ReferenceActivePhysicalStep.collectionEnabled ledger time
      let raw := CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording
      match CoordinatorCollectionLedger.startRound ledger (time.val + 1) enabled raw with
      | .invalid =>
          exact ReferenceActivePhysicalStep.coordinatorFailure bank
            (.collection .ledgerStartDomain) (some recording) none
      | .rejected _ =>
          exact ReferenceActivePhysicalStep.coordinatorFailure bank
            (.collection .ledgerStartDomain) (some recording) none
      | .success ledgerStarted =>
          let input := ReferenceUpReception.receptionInputAtRow rate row
            (ledgerStarted, (bank, (time, Y))) time
          let ordinaryResult := CoordinatorUpReception.receiveUp input
          let cut : ReferenceActivePhysicalStep.UpCut p rate := ⟨ordinaryResult, none⟩
          exact collectionFinish bank row time
            payload started recording cut

/-- Consume the SAME local preparation and own feedback. No dispatcher,
StartRound, sender oracle, or follower snapshot is read here. -/
def observeLocal (prepared : Preparation rate bank row time) (Y : Fin (D p + 1)) :
    ReferenceActivePhysicalStep.CoordinatorObservation p rate := by
  classical
  exact if prepared.selection = none then
    match prepared with
    | .dagger => ⟨.dagger, bank, none, none, none⟩
    | _ => ReferenceActivePhysicalStep.coordinatorFailure bank
        .dispatchRejected none none
  else
    match prepared with
    | .first (.chosen installed _) =>
        livePostChoice bank row time prepared.arm Y installed.registers
          installed.ownedRegisters installed.followerBaseScore installed.startRoundResult
    | .live r q base (.continuingChosen dispatched _ _ _) =>
        livePostChoice bank row time prepared.arm Y
          (ReferenceActivePhysicalStep.liveRegistersAt r time)
          (ReferenceActivePhysicalStep.liveOwnedAt r q time) base dispatched.startResult
    | .live r q _ (.cutoffChosen dispatched _ ledger _ _ _ _ _ _ _) =>
        collectionPostChoice bank row time prepared.arm Y r.payload
          (ReferenceActivePhysicalStep.sharedLedger ledger) dispatched.startResult
          (ReferenceActivePhysicalStep.liveRegistersAt r time).complementWeights
    | .collection payload ledger clock cutoff (.continuing _ snapshot _ _) =>
        let source := collectionInput bank row time payload ledger clock cutoff
        collectionPostChoice bank row time prepared.arm Y payload ledger snapshot.clockStarted
          (CoordinatorCollectionInteractive.PreObservationInputs.weights source
            snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq)
    | .collection _ _ _ _
        (.laterChosen _ _ started _ _ _ _ _ _ installed _) =>
        livePostChoice bank row time prepared.arm Y installed.registers
          installed.ownedRegisters installed.retainedBaseScore started
    | _ => ReferenceActivePhysicalStep.coordinatorFailure bank
        .dispatchRejected none none

/-- Literal specialization of the live composition, for all recorder, service,
confirmation, and clock outcomes. No success premise is supplied. -/
theorem livePostChoice_specialization
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ) (started : CoordinatorPhaseClock.StartRoundResult p) :
    livePostChoice x.state.upDecoderBank x.row x.time prepared.coordinator.arm
        prepared.coordinatorObservation r owned base started =
      ReferenceActivePhysicalStep.livePostChoice prepared r owned base started := rfl

/-- The entire finish output specializes, including banks on failed finishes. -/
theorem collectionFinish_specialization (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : Payload rate) (started : CoordinatorPhaseClock.StartRoundResult p)
    (recording : CoordinatorRecordingOperation.Output p)
    (cut : ReferenceActivePhysicalStep.UpCut p rate) :
    collectionFinish x.state.upDecoderBank x.row x.time payload started recording cut =
      ReferenceActivePhysicalStep.collectionFinish (x := x) payload started recording cut := rfl

/-- Literal specialization of ordinary collection, including invalid domains,
ordinary decoder rejection, and every ledger/clock finish failure. -/
theorem collectionPostChoice_specialization
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (payload : Payload rate) (ledger : Ledger rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ) :
    collectionPostChoice x.state.upDecoderBank x.row x.time prepared.coordinator.arm
        prepared.coordinatorObservation payload ledger started weights =
      OrdinaryActivePhysicalStep.collectionPostChoice prepared payload ledger started weights := rfl

/-- Full observation correspondence on arbitrary retained canonical outcomes.
The whole configuration, bank, failure, recorder output, and diagnostic agree. -/
theorem observeLocal_ofCanonical {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x) :
    observeLocal (ofCanonical prepared.coordinator) prepared.coordinatorObservation =
      OrdinaryActivePhysicalStep.observeCoordinator prepared := by
  unfold observeLocal OrdinaryActivePhysicalStep.observeCoordinator
  simp only [selection_none_ofCanonical]
  split
  · cases prepared.coordinator <;> rfl
  · simp only [arm_ofCanonical]
    dsimp only [livePostChoice, ReferenceActivePhysicalStep.livePostChoice,
      liveRecordingInput, ReferenceActivePhysicalStep.liveRecordingInput,
      collectionPostChoice, OrdinaryActivePhysicalStep.collectionPostChoice,
      collectionRecordingInput, ReferenceActivePhysicalStep.collectionRecordingInput,
      ReferenceActivePhysicalStep.upInputs]
    cases prepared.coordinator with
    | first outcome => cases outcome <;> rfl
    | live r owned base outcome => cases outcome <;> rfl
    | collection payload ledger clock cutoff outcome => cases outcome <;> rfl
    | invalidCollectionCutoff => rfl
    | dagger => rfl

/-- The live tail always has the ordinary, absent UP diagnostic. -/
theorem livePostChoice_up (bank : CoordinatorUpReception.UpDecoderBank p)
    (row : CompletePublicTable.CompleteRow p) (time : Fin p.T)
    (arm : Fin p.K) (Y : Fin (D p + 1))
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ) (started : CoordinatorPhaseClock.StartRoundResult p) :
    (livePostChoice bank row time arm Y r owned base started).up = none := by
  unfold livePostChoice
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · split <;> rfl

/-- Finishing preserves the supplied transient annotation on every branch;
the ordinary collection composition below supplies `none`. -/
theorem collectionFinish_up_eq_diagnostic (bank : CoordinatorUpReception.UpDecoderBank p)
    (row : CompletePublicTable.CompleteRow p) (time : Fin p.T)
    (payload : Payload rate) (started : CoordinatorPhaseClock.StartRoundResult p)
    (recording : CoordinatorRecordingOperation.Output p)
    (cut : ReferenceActivePhysicalStep.UpCut p rate) :
    (collectionFinish bank row time payload started recording cut).up = cut.diagnostic := by
  cases cut with
  | mk result diagnostic =>
      cases result with
      | invalid => rfl
      | success output | rejected output =>
          rcases output with ⟨ledger, receivedBank⟩
          dsimp only [collectionFinish]
          cases CoordinatorCollectionLedger.finishRound ledger with
          | invalid => rfl
          | rejected rejectedLedger => rfl
          | success ledgerFinished =>
              dsimp only
              cases CoordinatorPhaseClock.finishRound p rate.eta.val time started.clock
                  ledgerFinished.pending row <;> rfl

/-- No oracle or expected-sent-word diagnostic is generated by ordinary UP. -/
theorem collectionPostChoice_up (bank : CoordinatorUpReception.UpDecoderBank p)
    (row : CompletePublicTable.CompleteRow p) (time : Fin p.T)
    (arm : Fin p.K) (Y : Fin (D p + 1))
    (payload : Payload rate) (ledger : Ledger rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ) :
    (collectionPostChoice bank row time arm Y payload ledger started weights).up = none := by
  unfold collectionPostChoice
  split
  · rfl
  · dsimp only
    split
    · rfl
    · rfl
    · apply collectionFinish_up_eq_diagnostic

/-- Ordinary diagnostics are absent for arbitrary local data and feedback,
including every dispatch or post-choice failure. -/
theorem observeLocal_up (prepared : Preparation rate bank row time) (Y : Fin (D p + 1)) :
    (observeLocal prepared Y).up = none := by
  unfold observeLocal
  split
  · split <;> rfl
  · split <;> first | rfl | apply livePostChoice_up | apply collectionPostChoice_up

/-- Dagger has its source fallback arm and performs no local update for any Y. -/
theorem dagger_equations (Y : Fin (D p + 1)) :
    (Preparation.dagger : Preparation rate bank row time).arm = coordinatorFallback p ∧
    (Preparation.dagger : Preparation rate bank row time).downView = none ∧
    observeLocal (Preparation.dagger : Preparation rate bank row time) Y =
      ⟨.dagger, bank, none, none, none⟩ := ⟨rfl, rfl, rfl⟩

/-- Required unconditional consumption theorem for EVERY canonical input x.
There is no matching-trace, truth, all-success, or no-overflow hypothesis. -/
theorem observeLocal_prepareLocal (x : ReferenceActivePhysicalStep.RoundInput p rate) :
    observeLocal (prepareLocal x.state.coordinator x.state.upDecoderBank x.row x.time)
        (ReferenceActivePhysicalStep.prepare x).coordinatorObservation =
      OrdinaryActivePhysicalStep.observeCoordinator (ReferenceActivePhysicalStep.prepare x) := by
  rw [prepareLocal_specialization]
  exact observeLocal_ofCanonical (ReferenceActivePhysicalStep.prepare x)

/-- Public next-configuration, bank, recorder, and failure projections of the
whole equality. The ordinary diagnostic is included in the equality itself. -/
theorem observeLocal_prepareLocal_fields (x : ReferenceActivePhysicalStep.RoundInput p rate) :
    let localOutput := observeLocal
      (prepareLocal x.state.coordinator x.state.upDecoderBank x.row x.time)
      (ReferenceActivePhysicalStep.prepare x).coordinatorObservation
    localOutput.configuration = (OrdinaryActivePhysicalStep.step x).next.coordinator ∧
    localOutput.upDecoderBank = (OrdinaryActivePhysicalStep.step x).next.upDecoderBank ∧
    localOutput.recording = (OrdinaryActivePhysicalStep.step x).coordinator.recording ∧
    localOutput.failure = (OrdinaryActivePhysicalStep.step x).coordinator.failure := by
  dsimp only
  rw [observeLocal_prepareLocal]
  exact ⟨rfl, rfl, rfl, rfl⟩

end Bandits.Support.OrdinaryCoordinatorPhysicalInterface
