/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveOccupiedPreparationControl
public import Bandits.Support.ReferenceContinuingLiveSlicePreparation

/-!
# First-live whole-control transport on the actual generated run

Sources: `sources/zip4/manuscript/05_binary_transport.tex:74-124,293-345`,
`sources/zip4/manuscript/06_interruptions.tex:435-492`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-79`.

At an actual selected-empty first-live record, this module constructs the
continuing PREPARE branch and transports that current record across every
whole continuous control, including its affine pairs. The actual replacement
run has the same current first-live index, whole payload, pending set, cutoff,
complement weights, and all ordinary follower PREPARE states and memories.

The only branch inputs are computed window membership, an actual selection,
and its empty pending set. No seed, occupancy, successful tail, queue truth,
or transport law is supplied. The current arm, post-choice tail and future
records may depend on the replacement control. This is an internal transport
result; physical release flags, probability mass, source cylinders, stopped
support, conditional service, and manuscript closure are outside its scope.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceGeneratedActivePrefixFactor
open Bandits.Support.ReferenceRetainedBoundaryMeasurability
open Bandits.Support.ReferenceFirstLiveReleaseGeometry
open Bandits.Support.ReferenceFirstLiveConfirmationHistory
open Bandits.Support.ActiveRoundActions
open Bandits.Support.PublicDiscreteDraws
open scoped Classical

namespace Bandits.Support.ReferenceFirstLiveReleaseControlTransport

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev TimeControl := ContinuousLearningRows.TimeControl
abbrev Selection (p : Parameters) (rate : RateInput p) :=
  ReferenceActivePhysicalStep.Selection (p := p) (rate := rate)
abbrev Record (p : Parameters) (rate : RateInput p) :=
  ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)
abbrev RetainedLaunchStart (p : Parameters) (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p) :=
  ReferenceRetainedBoundaryMeasurability.RetainedLaunchStart
    rate rewards C_star C_h q t s hs control0

variable {p : Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}

/-- The existing generated physical run at a replacement of the retained
current control. Its seed, selected original row, whole rewards, and calendar
are the source-generated ones. -/
def retainedRun
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p)
    (x : RetainedLaunchStart p rate rewards C_star C_h q t s hs control0)
    (control : TimeControl p) : ReferenceActivePhysicalHorizon.Run
      (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed rate rewards C_star C_h q t
        control x.1 x.2.1 s hs
        ((ReferenceInitializationControlRemainder.launchStartRemainderEvent_control_independent
          rate rewards C_star C_h q t s x.1 x.2.1 control0 control).mp x.2.2)) :=
  let hstart := (ReferenceInitializationControlRemainder.launchStartRemainderEvent_control_independent
    rate rewards C_star C_h q t s x.1 x.2.1 control0 control).mp x.2.2
  let source := ReferenceGeneratedActivePrefixFactor.splitSource q t control x.1
  let seed := ReferenceGeneratedActivePrefixFactor.generatedActiveSeed rate rewards C_star C_h q t
    control x.1 x.2.1 s hs hstart
  let hmode := (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec rate rewards C_star C_h
    q t control x.1 x.2.1 s hs hstart).2.1
  ReferenceActivePhysicalHorizon.run seed source.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s (t.val - s + 1)
    (by omega) hmode

/-- The actual first-live window of `retainedRun`. -/
def retainedWindow
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p)
    (x : RetainedLaunchStart p rate rewards C_star C_h q t s hs control0)
    (control : TimeControl p) :=
  ReferenceFirstLiveConfirmationHistory.firstLiveWindow
    (retainedRun rewards C_star C_h q t s hs control0 x control).records

/-- The run alias is literally the existing horizon run of the generated
seed, for the current round and its strict prefix. -/
theorem retainedRun_eq_run
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p)
    (x : RetainedLaunchStart p rate rewards C_star C_h q t s hs control0)
    (control : TimeControl p) :
    retainedRun rewards C_star C_h q t s hs control0 x control =
      let hstart :=
        (ReferenceInitializationControlRemainder.launchStartRemainderEvent_control_independent
          rate rewards C_star C_h q t s x.1 x.2.1 control0 control).mp x.2.2
      let source := ReferenceGeneratedActivePrefixFactor.splitSource q t control x.1
      let seed := ReferenceGeneratedActivePrefixFactor.generatedActiveSeed
        rate rewards C_star C_h q t control x.1 x.2.1 s hs hstart
      ReferenceActivePhysicalHorizon.run seed source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s (t.val - s + 1)
        (by omega) ((ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
          rate rewards C_star C_h q t control x.1 x.2.1 s hs hstart).2.1) := rfl

/-- The window alias uses the computed records of that same run. -/
theorem retainedWindow_eq
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p)
    (x : RetainedLaunchStart p rate rewards C_star C_h q t s hs control0)
    (control : TimeControl p) :
    retainedWindow rewards C_star C_h q t s hs control0 x control =
      ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (retainedRun rewards C_star C_h q t s hs control0 x control).records := rfl

/-- The class of coordinator observations that records a selected first
cutoff from a live input. A failed cutoff remains visible through its
collection failure tag. -/
private def collectionObservation (o : ReferenceActivePhysicalStep.CoordinatorObservation p rate) : Bool :=
  match o with
  | ⟨.collection _ _ _, _, _, _, _⟩ => true
  | ⟨.dagger, _, some (.collection _), _, _⟩ => true
  | _ => false

/-- Recover the cutoff bit from the actual before-state and coordinator
observation retained in `RoundEvidence`. This is used only to compare the
same physical prefix when the source changes at a later time. -/
private def evidenceCutoff
    (e : ReferenceActivePhysicalHorizon.RoundEvidence (p := p) (rate := rate)) : Bool :=
  match e.before.coordinator with
  | .live _ _ _ => collectionObservation e.coordinator
  | _ => false

private def dispatchOrigin
    (x : ReferenceActivePhysicalStep.RoundInput p rate) :
    ReferenceActivePhysicalStep.DispatchCut x → Prop
  | .live registers owned base _ => x.state.coordinator = .live registers owned base
  | .collection payload ledger _ _ _ =>
      ∃ proposal, x.state.coordinator = .collection payload ledger proposal
  | .first _ => x.state.coordinator = .first
  | .dagger => x.state.coordinator = .dagger
  | .invalidCollectionCutoff => ∃ payload ledger proposal,
      x.state.coordinator = .collection payload ledger proposal

private theorem dispatch_origin (x : ReferenceActivePhysicalStep.RoundInput p rate) :
    dispatchOrigin x (ReferenceActivePhysicalStep.prepare x).coordinator := by
  change dispatchOrigin x (ReferenceActivePhysicalStep.dispatch x)
  unfold ReferenceActivePhysicalStep.dispatch
  cases hc : x.state.coordinator with
  | first => simp only [CoordinatorRoundDispatch.dispatch]; exact hc
  | live r q base =>
      simp only [CoordinatorRoundDispatch.dispatch]
      exact hc
  | collection payload ledger proposal =>
      simp only [CoordinatorRoundDispatch.dispatch]
      split
      · exact ⟨proposal, hc⟩
      · exact ⟨payload, ledger, proposal, hc⟩
  | dagger => exact hc

private theorem collectionFinish_collectionObservation
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (recording : CoordinatorRecordingOperation.Output p)
    (ledgerStarted : ReferenceActivePhysicalStep.Ledger rate) :
    collectionObservation
      (ReferenceActivePhysicalStep.collectionFinish (x := x) payload started recording
        (ReferenceActivePhysicalStep.receiveUp prepared ledgerStarted)) = true := by
  classical
  unfold ReferenceActivePhysicalStep.collectionFinish
  cases hcut : (ReferenceActivePhysicalStep.receiveUp prepared ledgerStarted).result with
  | invalid => simp [collectionObservation, ReferenceActivePhysicalStep.coordinatorFailure]
  | success pair =>
      rcases pair with ⟨ledger, bank⟩
      cases hledger : CoordinatorCollectionLedger.finishRound ledger with
      | invalid => simp [hledger, collectionObservation,
          ReferenceActivePhysicalStep.coordinatorFailure]
      | rejected bad => simp [hledger, collectionObservation,
          ReferenceActivePhysicalStep.coordinatorFailure]
      | success ledgerFinished =>
          cases hclock : CoordinatorPhaseClock.finishRound p rate.eta.val x.time started.clock
              ledgerFinished.pending x.row with
          | error reason => simp [hledger, hclock, collectionObservation,
              ReferenceActivePhysicalStep.coordinatorFailure]
          | ok clockFinished => simp [hledger, hclock, collectionObservation]
  | rejected pair =>
      rcases pair with ⟨ledger, bank⟩
      cases hledger : CoordinatorCollectionLedger.finishRound ledger with
      | invalid => simp [hledger, collectionObservation,
          ReferenceActivePhysicalStep.coordinatorFailure]
      | rejected bad => simp [hledger, collectionObservation,
          ReferenceActivePhysicalStep.coordinatorFailure]
      | success ledgerFinished =>
          cases hclock : CoordinatorPhaseClock.finishRound p rate.eta.val x.time started.clock
              ledgerFinished.pending x.row with
          | error reason => simp [hledger, hclock, collectionObservation,
              ReferenceActivePhysicalStep.coordinatorFailure]
          | ok clockFinished => simp [hledger, hclock, collectionObservation]

private theorem collectionPostChoice_collectionObservation
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ) :
    collectionObservation
      (ReferenceActivePhysicalStep.collectionPostChoice prepared payload ledger started weights) = true := by
  classical
  unfold ReferenceActivePhysicalStep.collectionPostChoice
  cases hrec : CoordinatorRecorderComplementBridge.run
      (ReferenceActivePhysicalStep.collectionRecordingInput prepared payload started weights) with
  | none => simp [collectionObservation, ReferenceActivePhysicalStep.coordinatorFailure]
  | some recording =>
      cases hstart : CoordinatorCollectionLedger.startRound ledger (x.time.val + 1)
          (ReferenceActivePhysicalStep.collectionEnabled ledger x.time)
          (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) with
      | invalid => simp [hstart, collectionObservation, ReferenceActivePhysicalStep.coordinatorFailure]
      | rejected bad => simp [hstart, collectionObservation, ReferenceActivePhysicalStep.coordinatorFailure]
      | success ledgerStarted =>
          have hfinish := collectionFinish_collectionObservation prepared payload started
            recording ledgerStarted
          simpa [hrec, hstart] using hfinish

private theorem livePostChoice_not_collectionObservation
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ)
    (started : CoordinatorPhaseClock.StartRoundResult p) :
    collectionObservation
      (ReferenceActivePhysicalStep.livePostChoice prepared r q base started) = false := by
  classical
  unfold ReferenceActivePhysicalStep.livePostChoice
  cases hrec : CoordinatorRecorderComplementBridge.run
      (ReferenceActivePhysicalStep.liveRecordingInput prepared r started) with
  | none => simp [collectionObservation, ReferenceActivePhysicalStep.coordinatorFailure]
  | some recording =>
      cases hservice : CoordinatorLiveServiceFinish.servicePass r q recording with
      | error reason => simp [hservice, collectionObservation, ReferenceActivePhysicalStep.coordinatorFailure]
      | ok serviced =>
          cases hconfirm : CoordinatorLocalArmChoice.confirmationUpdate r.payload started.pending
              (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
              x.time x.row prepared.coordinatorObservation with
          | none => simp [hservice, collectionObservation,
              ReferenceActivePhysicalStep.coordinatorFailure]
          | some pending =>
              cases hclock : CoordinatorPhaseClock.finishRound p rate.eta.val x.time started.clock
                  pending x.row with
              | error reason => simp [hservice, hclock, collectionObservation,
                  ReferenceActivePhysicalStep.coordinatorFailure]
              | ok finished => simp [hservice, hclock, collectionObservation]

/-- Every actual round's cutoff bit is encoded by its evidence. In particular,
a collection-tail failure still witnesses a chosen cutoff, whereas a
continuing-tail failure retains a live failure tag. No successful tail is
required. -/
private theorem cutoffChosen_eq_evidence
    (record : Record (p := p) (rate := rate)) :
    ReferenceCollectionPhaseHistory.cutoffChosen record.input = evidenceCutoff record.evidence := by
  classical
  have hdiag : record.coordinatorDiagnostics =
      (ReferenceActivePhysicalStep.prepare record.input).observeCoordinator := by
    change record.output.coordinator = _
    calc
      record.output.coordinator =
          (ReferenceActivePhysicalStep.step record.input).coordinator :=
        congrArg (fun out : ReferenceActivePhysicalStep.RoundOutput record.input => out.coordinator)
          record.output_eq
      _ = (ReferenceActivePhysicalStep.prepare record.input).observeCoordinator := rfl
  cases hstate : record.input.state.coordinator with
  | first =>
      have hcut : ReferenceCollectionPhaseHistory.cutoffChosen record.input = false := by
        by_contra hn
        have htrue : ReferenceCollectionPhaseHistory.cutoffChosen record.input = true :=
          Bool.eq_true_of_not_eq_false hn
        unfold ReferenceCollectionPhaseHistory.cutoffChosen at htrue
        cases hprep : (ReferenceActivePhysicalStep.prepare record.input).coordinator with
        | live r q base outcome =>
            cases outcome with
            | cutoffChosen dispatched hstart ledger hinitialization hledger hvalid
                hclock hpending hnone arm =>
                have horigin := dispatch_origin record.input
                dsimp [dispatchOrigin] at horigin
                rw [hprep] at horigin
                rw [hstate] at horigin
                contradiction
            | continuingChosen dispatched hstart continuation arm => simp [hprep] at htrue
            | clockFailure failure hfailure => simp [hprep] at htrue
            | initializerFailure dispatched hstart checked hfailure => simp [hprep] at htrue
            | localFailure dispatched hstart failure => simp [hprep] at htrue
        | first outcome => simp [hprep] at htrue
        | collection payload ledger clock cutoff outcome => simp [hprep] at htrue
        | dagger => simp [hprep] at htrue
        | invalidCollectionCutoff => simp [hprep] at htrue
      rw [hcut]
      simp [evidenceCutoff, ReferenceActivePhysicalHorizon.RoundRecord.evidence, hstate]
  | live r q base =>
      have hdispatch : ReferenceActivePhysicalStep.dispatch record.input =
          .live r q base (CoordinatorRoundDispatch.dispatchLive
            (ReferenceActivePhysicalStep.liveInput record.input r q base)) := by
        simp only [ReferenceActivePhysicalStep.dispatch, hstate,
          CoordinatorRoundDispatch.dispatch]
        rfl
      cases hout : CoordinatorRoundDispatch.dispatchLive
          (ReferenceActivePhysicalStep.liveInput record.input r q base) with
      | cutoffChosen dispatched hstart ledger hinit hledger hvalid hclock hpending hnone arm =>
          have hprep : (ReferenceActivePhysicalStep.prepare record.input).coordinator =
              .live r q base (.cutoffChosen dispatched hstart ledger hinit hledger hvalid
                hclock hpending hnone arm) := by
            simp [ReferenceActivePhysicalStep.prepare, hdispatch, hout]
          have hobs := ReferenceActivePhysicalStep.observeCoordinator_live_equation
            (ReferenceActivePhysicalStep.prepare record.input) r q base
            (.cutoffChosen dispatched hstart ledger hinit hledger hvalid hclock hpending hnone arm)
            hprep
          have hselected : (ReferenceActivePhysicalStep.DispatchCut.live r q base
              (.cutoffChosen dispatched hstart ledger hinit hledger hvalid hclock hpending hnone arm)).selection ≠ none := by
            simp [ReferenceActivePhysicalStep.DispatchCut.selection,
              ReferenceActivePhysicalStep.selectionAt,
              ReferenceActivePhysicalStep.liveRegistersAt]
          rw [ReferenceCollectionPhaseHistory.cutoffChosen, hprep]
          unfold evidenceCutoff ReferenceActivePhysicalHorizon.RoundRecord.evidence
          simp only [hstate]
          change true = collectionObservation record.coordinatorDiagnostics
          have hobs' : record.coordinatorDiagnostics =
              ReferenceActivePhysicalStep.collectionPostChoice
                (ReferenceActivePhysicalStep.prepare record.input) r.payload
                (ReferenceActivePhysicalStep.sharedLedger ledger) dispatched.startResult
                (ReferenceActivePhysicalStep.liveRegistersAt r record.input.time).complementWeights := by
            rw [hdiag, hobs]
            simp [hselected]
          rw [hobs']
          exact (collectionPostChoice_collectionObservation
            (prepared := ReferenceActivePhysicalStep.prepare record.input)
            (payload := r.payload) (ledger := ReferenceActivePhysicalStep.sharedLedger ledger)
            (started := dispatched.startResult)
            (weights := (ReferenceActivePhysicalStep.liveRegistersAt r record.input.time).complementWeights)).symm
      | continuingChosen dispatched hstart continuation arm =>
          have hprep : (ReferenceActivePhysicalStep.prepare record.input).coordinator =
              .live r q base (.continuingChosen dispatched hstart continuation arm) := by
            simp [ReferenceActivePhysicalStep.prepare, hdispatch, hout]
          have hobs := ReferenceActivePhysicalStep.observeCoordinator_live_equation
            (ReferenceActivePhysicalStep.prepare record.input) r q base
            (.continuingChosen dispatched hstart continuation arm) hprep
          have hselected : (ReferenceActivePhysicalStep.DispatchCut.live r q base
              (.continuingChosen dispatched hstart continuation arm)).selection ≠ none := by
            simp [ReferenceActivePhysicalStep.DispatchCut.selection,
              ReferenceActivePhysicalStep.selectionAt,
              ReferenceActivePhysicalStep.liveRegistersAt]
          rw [ReferenceCollectionPhaseHistory.cutoffChosen, hprep]
          unfold evidenceCutoff ReferenceActivePhysicalHorizon.RoundRecord.evidence
          simp only [hstate]
          change false = collectionObservation record.coordinatorDiagnostics
          have hobs' : record.coordinatorDiagnostics =
              ReferenceActivePhysicalStep.livePostChoice
                (ReferenceActivePhysicalStep.prepare record.input)
                (ReferenceActivePhysicalStep.liveRegistersAt r record.input.time)
                (ReferenceActivePhysicalStep.liveOwnedAt r q record.input.time) base
                dispatched.startResult := by
            rw [hdiag, hobs]
            simp [hselected]
          rw [hobs']
          exact (livePostChoice_not_collectionObservation
            (prepared := ReferenceActivePhysicalStep.prepare record.input)
            (r := ReferenceActivePhysicalStep.liveRegistersAt r record.input.time)
            (q := ReferenceActivePhysicalStep.liveOwnedAt r q record.input.time)
            (base := base) (started := dispatched.startResult)).symm
      | clockFailure failure hfailure =>
          have hprep : (ReferenceActivePhysicalStep.prepare record.input).coordinator =
              .live r q base (.clockFailure failure hfailure) := by
            simp [ReferenceActivePhysicalStep.prepare, hdispatch, hout]
          have hobs := ReferenceActivePhysicalStep.observeCoordinator_live_equation
            (ReferenceActivePhysicalStep.prepare record.input) r q base
            (.clockFailure failure hfailure) hprep
          rw [ReferenceCollectionPhaseHistory.cutoffChosen, hprep]
          unfold evidenceCutoff ReferenceActivePhysicalHorizon.RoundRecord.evidence
          simp only [hstate]
          change false = collectionObservation record.coordinatorDiagnostics
          rw [hdiag, hobs]
          have hnone : (ReferenceActivePhysicalStep.DispatchCut.live r q base
              (.clockFailure failure hfailure)).selection = none := by
            simp [ReferenceActivePhysicalStep.DispatchCut.selection]
          simp [hnone, collectionObservation, ReferenceActivePhysicalStep.coordinatorFailure]
      | initializerFailure dispatched hstart checked hfailure =>
          have hprep : (ReferenceActivePhysicalStep.prepare record.input).coordinator =
              .live r q base (.initializerFailure dispatched hstart checked hfailure) := by
            simp [ReferenceActivePhysicalStep.prepare, hdispatch, hout]
          have hobs := ReferenceActivePhysicalStep.observeCoordinator_live_equation
            (ReferenceActivePhysicalStep.prepare record.input) r q base
            (.initializerFailure dispatched hstart checked hfailure) hprep
          rw [ReferenceCollectionPhaseHistory.cutoffChosen, hprep]
          unfold evidenceCutoff ReferenceActivePhysicalHorizon.RoundRecord.evidence
          simp only [hstate]
          change false = collectionObservation record.coordinatorDiagnostics
          rw [hdiag, hobs]
          have hnone : (ReferenceActivePhysicalStep.DispatchCut.live r q base
              (.initializerFailure dispatched hstart checked hfailure)).selection = none := by
            simp [ReferenceActivePhysicalStep.DispatchCut.selection]
          simp [hnone, collectionObservation, ReferenceActivePhysicalStep.coordinatorFailure]
      | localFailure dispatched hstart failure =>
          have hprep : (ReferenceActivePhysicalStep.prepare record.input).coordinator =
              .live r q base (.localFailure dispatched hstart failure) := by
            simp [ReferenceActivePhysicalStep.prepare, hdispatch, hout]
          have hobs := ReferenceActivePhysicalStep.observeCoordinator_live_equation
            (ReferenceActivePhysicalStep.prepare record.input) r q base
            (.localFailure dispatched hstart failure) hprep
          rw [ReferenceCollectionPhaseHistory.cutoffChosen, hprep]
          unfold evidenceCutoff ReferenceActivePhysicalHorizon.RoundRecord.evidence
          simp only [hstate]
          change false = collectionObservation record.coordinatorDiagnostics
          rw [hdiag, hobs]
          have hnone : (ReferenceActivePhysicalStep.DispatchCut.live r q base
              (.localFailure dispatched hstart failure)).selection = none := by
            simp [ReferenceActivePhysicalStep.DispatchCut.selection]
          simp [hnone, collectionObservation, ReferenceActivePhysicalStep.coordinatorFailure]
  | collection payload ledger proposal =>
      have hcut : ReferenceCollectionPhaseHistory.cutoffChosen record.input = false := by
        by_contra hn
        have htrue : ReferenceCollectionPhaseHistory.cutoffChosen record.input = true :=
          Bool.eq_true_of_not_eq_false hn
        unfold ReferenceCollectionPhaseHistory.cutoffChosen at htrue
        cases hprep : (ReferenceActivePhysicalStep.prepare record.input).coordinator with
        | live r q base outcome =>
            cases outcome with
            | cutoffChosen dispatched hstart ledger hinitialization hledger hvalid
                hclock hpending hnone arm =>
                have horigin := dispatch_origin record.input
                dsimp [dispatchOrigin] at horigin
                rw [hprep] at horigin
                rw [hstate] at horigin
                simp_all
            | continuingChosen dispatched hstart continuation arm => simp [hprep] at htrue
            | clockFailure failure hfailure => simp [hprep] at htrue
            | initializerFailure dispatched hstart checked hfailure => simp [hprep] at htrue
            | localFailure dispatched hstart failure => simp [hprep] at htrue
        | first outcome => simp [hprep] at htrue
        | collection payload ledger clock cutoff outcome => simp [hprep] at htrue
        | dagger => simp [hprep] at htrue
        | invalidCollectionCutoff => simp [hprep] at htrue
      simp [hcut, evidenceCutoff,
        ReferenceActivePhysicalHorizon.RoundRecord.evidence, hstate]
  | dagger =>
      have hcut : ReferenceCollectionPhaseHistory.cutoffChosen record.input = false := by
        by_contra hn
        have htrue : ReferenceCollectionPhaseHistory.cutoffChosen record.input = true :=
          Bool.eq_true_of_not_eq_false hn
        unfold ReferenceCollectionPhaseHistory.cutoffChosen at htrue
        cases hprep : (ReferenceActivePhysicalStep.prepare record.input).coordinator with
        | live r q base outcome =>
            cases outcome with
            | cutoffChosen dispatched hstart ledger hinitialization hledger hvalid
                hclock hpending hnone arm =>
                have horigin := dispatch_origin record.input
                dsimp [dispatchOrigin] at horigin
                rw [hprep] at horigin
                rw [hstate] at horigin
                simp_all
            | continuingChosen dispatched hstart continuation arm => simp [hprep] at htrue
            | clockFailure failure hfailure => simp [hprep] at htrue
            | initializerFailure dispatched hstart checked hfailure => simp [hprep] at htrue
            | localFailure dispatched hstart failure => simp [hprep] at htrue
        | first outcome => simp [hprep] at htrue
        | collection payload ledger clock cutoff outcome => simp [hprep] at htrue
        | dagger => simp [hprep] at htrue
        | invalidCollectionCutoff => simp [hprep] at htrue
      rw [hcut]
      simp [evidenceCutoff, ReferenceActivePhysicalHorizon.RoundRecord.evidence, hstate]

/-- A prefix whose actual cutoff bits are false remains in the computed
first-live window. -/
private theorem takeWhile_length_succ_of_true
    {α : Type} (pred : α → Bool) (xs : List α) (n : ℕ)
    (hcurrentIndex : n < xs.length)
    (hprior : ∀ j (hj : j < n), pred (xs[j]'(by omega)) = true)
    (hcurrent : pred (xs[n]'hcurrentIndex) = true) :
    n + 1 ≤ (xs.takeWhile pred).length := by
  induction n generalizing xs with
  | zero =>
      cases xs with
      | nil => simp at hcurrentIndex
      | cons a tail =>
          have ha : pred a = true := by simpa using hcurrent
          simp [ha]
  | succ n ih =>
      cases xs with
      | nil => simp at hcurrentIndex
      | cons a tail =>
          simp only [List.length_cons] at hcurrentIndex
          have hhead : pred a = true := by
            simpa using hprior 0 (by omega)
          have htail : ∀ j (hj : j < n), pred (tail[j]'(by omega)) = true := by
            intro j hj
            have h := hprior (j + 1) (by omega)
            simpa only [List.getElem_cons_succ] using h
          have htailCurrentIndex : n < tail.length := by omega
          have hlast : pred (tail[n]'htailCurrentIndex) = true := by
            simpa only [List.getElem_cons_succ] using hcurrent
          have htailTake := ih tail htailCurrentIndex htail hlast
          simp [hhead] at htailTake ⊢
          omega

private theorem firstLive_prefix_transfer
    (baseline changed : List (Record (p := p) (rate := rate))) (n : ℕ)
    (hbaselineLength : n ≤ baseline.length)
    (hn : n < (ReferenceFirstLiveConfirmationHistory.firstLiveWindow baseline).length)
    (hchangedLength : n < changed.length)
    (hsame : ∀ j (hj : j < n),
      (baseline[j]'(by omega)).evidence = (changed[j]'(by omega)).evidence)
    (hcurrent : ReferenceCollectionPhaseHistory.cutoffChosen
      (changed[n]'(by omega)).input = false) :
    n < (ReferenceFirstLiveConfirmationHistory.firstLiveWindow changed).length := by
  let baselineWindow := ReferenceFirstLiveConfirmationHistory.firstLiveWindow baseline
  have hnWindow : n < baselineWindow.length := by
    simpa [baselineWindow] using hn
  have hwindowLength : baselineWindow.length ≤ baseline.length := by
    simp only [baselineWindow, ReferenceFirstLiveConfirmationHistory.firstLiveWindow]
    exact (List.takeWhile_prefix _).length_le
  have hprefix : baselineWindow.IsPrefix baseline := by
    simp only [baselineWindow, ReferenceFirstLiveConfirmationHistory.firstLiveWindow]
    exact List.takeWhile_prefix _
  have hprior : ∀ j (hj : j < n),
      (!ReferenceCollectionPhaseHistory.cutoffChosen (changed[j]'(by omega)).input) = true := by
    intro j hj
    have hjWindow : j < baselineWindow.length := by omega
    have hmem := List.getElem_mem hjWindow
    have hgoodWindow :
        (!ReferenceCollectionPhaseHistory.cutoffChosen baselineWindow[j].input) = true :=
      by
        simpa only [baselineWindow, ReferenceFirstLiveConfirmationHistory.firstLiveWindow] using
          (List.all_eq_true.mp List.all_takeWhile baselineWindow[j] (by
            simpa only [baselineWindow, ReferenceFirstLiveConfirmationHistory.firstLiveWindow]
              using hmem))
    have hrecord : baselineWindow[j] = baseline[j] := hprefix.getElem hjWindow
    have hgoodBaseline :
        (!ReferenceCollectionPhaseHistory.cutoffChosen (baseline[j]'(by omega)).input) = true := by
      simpa [hrecord] using hgoodWindow
    have hcutEq : ReferenceCollectionPhaseHistory.cutoffChosen
        (baseline[j]'(by omega)).input =
          ReferenceCollectionPhaseHistory.cutoffChosen (changed[j]'(by omega)).input := by
      rw [cutoffChosen_eq_evidence, cutoffChosen_eq_evidence]
      exact congrArg evidenceCutoff (hsame j hj)
    simpa only [hcutEq] using hgoodBaseline
  have hgoodCurrent :
      (!ReferenceCollectionPhaseHistory.cutoffChosen (changed[n]'(by omega)).input) = true := by
    simp [hcurrent]
  exact takeWhile_length_succ_of_true
    (fun record : Record (p := p) (rate := rate) =>
      !ReferenceCollectionPhaseHistory.cutoffChosen record.input)
    changed n hchangedLength hprior hgoodCurrent

/-- A selected live PREPARE with no actual cutoff dispatch must be the
continuing constructor. Failed constructors have no selection. -/
private theorem selected_live_continuing_constructor
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ)
    (hstate : x.state.coordinator = .live r owned base)
    (hselected : (ReferenceActivePhysicalStep.DispatchCut.live r owned base
      (CoordinatorRoundDispatch.dispatchLive
        (ReferenceActivePhysicalStep.liveInput x r owned base))).selection ≠ none)
    (hnoCut : ReferenceCollectionPhaseHistory.cutoffChosen x = false) :
    ∃ d hs c arm,
      (ReferenceActivePhysicalStep.prepare x).coordinator =
        .live r owned base (.continuingChosen d hs c arm) := by
  have hdispatch : ReferenceActivePhysicalStep.dispatch x =
      .live r owned base (CoordinatorRoundDispatch.dispatchLive
        (ReferenceActivePhysicalStep.liveInput x r owned base)) := by
    simp only [ReferenceActivePhysicalStep.dispatch, hstate,
      CoordinatorRoundDispatch.dispatch]
    rfl
  cases hout : CoordinatorRoundDispatch.dispatchLive
      (ReferenceActivePhysicalStep.liveInput x r owned base) with
  | continuingChosen d hs c arm =>
      exact ⟨d, hs, c, arm, by simp [ReferenceActivePhysicalStep.prepare, hdispatch, hout]⟩
  | cutoffChosen d hs ledger hinit hledger hvalid hclock hpending hnone arm =>
      have hcut : ReferenceCollectionPhaseHistory.cutoffChosen x = true := by
        simp [ReferenceCollectionPhaseHistory.cutoffChosen,
          ReferenceActivePhysicalStep.prepare, hdispatch, hout]
      rw [hnoCut] at hcut
      cases hcut
  | clockFailure failure hfailure
  | initializerFailure _ _ _ _
  | localFailure _ _ _ =>
      rw [hout] at hselected
      simp only [ReferenceActivePhysicalStep.DispatchCut.selection, ne_eq, not_true_eq_false] at hselected

private theorem selected_fields_of_continuing
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ)
    (d : CoordinatorStartRoundCutoffDispatch.Output
      (ReferenceActivePhysicalStep.liveRegistersAt r x.time)
      (ReferenceActivePhysicalStep.liveOwnedAt r owned x.time) base)
    (hs : CoordinatorPhaseClock.startRound p rate.eta.val x.time r.priorClock
      r.clockPending = .ok d.startResult)
    (c : CoordinatorLiveChoiceRecorderStep.Continuation
      (ReferenceActivePhysicalStep.liveRegistersAt r x.time) x.row)
    (a : CoordinatorRoundDispatch.ArmSelection
      (ReferenceActivePhysicalStep.liveRegistersAt r x.time).payload d.startResult x.time
      (ReferenceActivePhysicalStep.liveRegistersAt r x.time).complementWeights x.row)
    (selected : Selection (p := p) (rate := rate) x)
    (hctor : (ReferenceActivePhysicalStep.prepare x).coordinator =
      .live r owned base (.continuingChosen d hs c a))
    (hselected : (ReferenceActivePhysicalStep.prepare x).coordinator.selection = some selected) :
    selected.view.payload = r.payload ∧
      selected.view.pendingAtChoice = d.startResult.pending ∧
      selected.view.cutoff = CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
        d.startResult.clock.u ∧
      HEq selected.view.complementWeights
        (ReferenceActivePhysicalStep.liveRegistersAt r x.time).complementWeights ∧
      selected.started = d.startResult ∧ selected.arm = a.arm := by
  have hcut :
      (ReferenceActivePhysicalStep.DispatchCut.live r owned base
        (.continuingChosen d hs c a)).selection = some selected := by
    simpa only [hctor] using hselected
  have hrecord :
      ({ view :=
          { payload := r.payload
            pendingAtChoice := d.startResult.pending
            cutoff := CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u
            complementWeights :=
              (ReferenceActivePhysicalStep.liveRegistersAt r x.time).complementWeights }
         started := d.startResult
         pending_eq := rfl
         cutoff_eq := rfl
         arm := a.arm
         choice_eq := a.armChoice_eq } : Selection (p := p) (rate := rate) x) = selected := by
    simpa [ReferenceActivePhysicalStep.DispatchCut.selection,
      ReferenceActivePhysicalStep.selectionAt] using hcut
  cases hrecord
  exact ⟨rfl, rfl, rfl, HEq.rfl, rfl, rfl⟩

private theorem inputAtControl_eq_withControl
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (u : TimeControl p) :
    ReferenceContinuingLiveSlicePreparation.inputAtControl x u =
      ReferenceLaterOptionalControlResampling.withControl x u := by
  cases x
  rfl

/-- At the same retained remainder, every whole replacement control preserves
the first-live current index, actual live selection, payload, pending set,
cutoff, and complement weights. The current action arm may vary with the
replacement slice. The source-generated prefix and physical run are reused.
There is no positive-prefix-length premise: the branch selectors also apply
at `s = t.val`. A terminal `s = p.T` cannot supply `hs` for `t : Fin p.T`. -/
theorem retained_first_live_control_transport
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p)
    (x : RetainedLaunchStart p rate rewards C_star C_h q t s hs control0)
    (hn : t.val - s < (retainedWindow rewards C_star C_h q t s hs control0 x control0).length)
    (selected0 : Selection (p := p) (rate := rate)
      (retainedWindow rewards C_star C_h q t s hs control0 x control0)[t.val - s].input)
    (hselected :
      (retainedWindow rewards C_star C_h q t s hs control0 x control0)[t.val - s].output.preparation.coordinator.selection =
        some selected0)
    (hempty : selected0.view.pendingAtChoice = ∅) :
    let source0 := ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.1
    let beta := ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary
      rate rewards C_star C_h q t s hs control0 x
    let generated := ReferenceGeneratedActivePrefixFactor.generatedActiveSeed
      rate rewards C_star C_h q t control0 x.1 x.2.1 s hs x.2.2
    let hmode := (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
      rate rewards C_star C_h q t control0 x.1 x.2.1 s hs x.2.2).2.1
    let E := ReferenceActivePhysicalHorizon.run generated source0.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source0) rewards s
      (t.val - s + 1) (by omega) hmode
    let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records
    ∃ r owned base,
      beta = W[t.val - s].input ∧
      W[t.val - s].input.state.coordinator = .live r owned base ∧
      r.time.val + 1 = W[t.val - s].input.time.val ∧
      r.priorClock.u = none ∧ r.pendingAtChoice = ∅ ∧
      ReferenceCollectionPhaseHistory.cutoffChosen W[t.val - s].input = false ∧
      selected0.view.payload = r.payload ∧ selected0.view.cutoff = none ∧
      HEq selected0.view.complementWeights r.complementWeights ∧
      ∃ (d : CoordinatorStartRoundCutoffDispatch.Output
          (ReferenceActivePhysicalStep.liveRegistersAt r W[t.val - s].input.time)
          (ReferenceActivePhysicalStep.liveOwnedAt r owned W[t.val - s].input.time) base)
        (hsStart : CoordinatorPhaseClock.startRound p rate.eta.val
          W[t.val - s].input.time r.priorClock r.clockPending = .ok d.startResult)
        (c : CoordinatorLiveChoiceRecorderStep.Continuation
          (ReferenceActivePhysicalStep.liveRegistersAt r W[t.val - s].input.time)
          W[t.val - s].input.row)
        (arm : CoordinatorRoundDispatch.ArmSelection
          (ReferenceActivePhysicalStep.liveRegistersAt r W[t.val - s].input.time).payload
          d.startResult W[t.val - s].input.time
          (ReferenceActivePhysicalStep.liveRegistersAt r W[t.val - s].input.time).complementWeights
          W[t.val - s].input.row),
        (ReferenceActivePhysicalStep.prepare W[t.val - s].input).coordinator =
          .live r owned base (.continuingChosen d hsStart c arm) ∧
        CoordinatorLocalArmChoice.ChoiceInputsValid
          selected0.view.payload selected0.view.cutoff W[t.val - s].input.time
          selected0.view.complementWeights ∧
        ∃ states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta,
          ∃ memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p,
            (∀ j, ((ReferenceActivePhysicalStep.prepare W[t.val - s].input).followers.followers j).configuration =
              .ordinary (states j) (memories j)) ∧
            (∀ j, (states j).status ≠ .unoccupied ∧
              (states j).lastDown = some (selected0.view.payload.downRecord j)) ∧
            (∀ j, j ∈ ReferencePhysicalReleaseQuota.pendingAtStart
                selected0.view.payload beta.time beta.state ↔ (states j).status = .pending) ∧
            ∀ u : TimeControl p,
              let E_u := retainedRun rewards C_star C_h q t s hs control0 x u
              let W_u := ReferenceFirstLiveConfirmationHistory.firstLiveWindow E_u.records
              ∃ hwindow : t.val - s < W_u.length,
                (W_u[t.val - s]'hwindow).input =
                  ReferenceLaterOptionalControlResampling.withControl beta u ∧
                ReferenceContinuingLiveSlicePreparation.inputAtControl W[t.val - s].input u =
                  ReferenceLaterOptionalControlResampling.withControl beta u ∧
                ReferenceCollectionPhaseHistory.cutoffChosen
                  (W_u[t.val - s]'hwindow).input = false ∧
                (∀ j, ((ReferenceActivePhysicalStep.prepare
                    (W_u[t.val - s]'hwindow).input).followers.followers j).configuration =
                  .ordinary (states j) (memories j)) ∧
                ∃ selectedU : Selection (p := p) (rate := rate)
                    (W_u[t.val - s]'hwindow).input,
                  (ReferenceActivePhysicalStep.prepare
                    (W_u[t.val - s]'hwindow).input).coordinator.selection = some selectedU ∧
                  (W_u[t.val - s]'hwindow).output.preparation.coordinator.selection =
                    some selectedU ∧
                  selectedU.view.payload = selected0.view.payload ∧
                  selectedU.view.pendingAtChoice = selected0.view.pendingAtChoice ∧
                  selectedU.view.cutoff = selected0.view.cutoff ∧
                  HEq selectedU.view.complementWeights selected0.view.complementWeights ∧
                  (∀ j, j ∈ ReferencePhysicalReleaseQuota.pendingAtStart
                    selectedU.view.payload (W_u[t.val - s]'hwindow).input.time
                    (W_u[t.val - s]'hwindow).input.state ↔ (states j).status = .pending) := by
  intro source0 beta generated hmode E W
  have hnRoot : t.val - s < W.length := by
    exact hn
  have hselectedRoot :
      W[t.val - s].output.preparation.coordinator.selection = some selected0 := by
    exact hselected
  obtain ⟨r, owned, base, hbeta, hstate, htimeNext, hprior, hpending,
      hnoCut, _, hvalid, hpayload, hcutoff, hweights, states, memories,
      hprepared, hfields, hcontrols, hpendingStatus, _⟩ :=
    ReferenceFirstLiveOccupiedPreparationControl.retained_first_live_occupied_prepare_all_controls
      rewards C_star C_h q t s hs control0 x hnRoot selected0 hselectedRoot hempty
  let x0 := W[t.val - s].input
  have hbeta0 : beta = x0 := by
    simpa only [beta, W, E, generated, hmode, source0] using hbeta
  have hvalid0 : CoordinatorLocalArmChoice.ChoiceInputsValid selected0.view.payload
      selected0.view.cutoff x0.time selected0.view.complementWeights := hvalid
  have hstate0 : x0.state.coordinator = .live r owned base := hstate
  have hnoCut0 : ReferenceCollectionPhaseHistory.cutoffChosen x0 = false := hnoCut
  have hselectedPrep :
      (ReferenceActivePhysicalStep.prepare x0).coordinator.selection = some selected0 := by
    have h := hselectedRoot
    rw [W[t.val - s].output_eq] at h
    exact h
  have hdispatch : ReferenceActivePhysicalStep.dispatch x0 =
      .live r owned base
        (CoordinatorRoundDispatch.dispatchLive
          (ReferenceActivePhysicalStep.liveInput x0 r owned base)) := by
    simp only [ReferenceActivePhysicalStep.dispatch, hstate0,
      CoordinatorRoundDispatch.dispatch]
    rfl
  have hcutSelected :
      (ReferenceActivePhysicalStep.DispatchCut.live r owned base
        (CoordinatorRoundDispatch.dispatchLive
          (ReferenceActivePhysicalStep.liveInput x0 r owned base))).selection = some selected0 := by
    simpa only [ReferenceActivePhysicalStep.prepare, hdispatch]
      using hselectedPrep
  have hdispatchSelected :
      (ReferenceActivePhysicalStep.DispatchCut.live r owned base
        (CoordinatorRoundDispatch.dispatchLive
          (ReferenceActivePhysicalStep.liveInput x0 r owned base))).selection ≠ none := by
    rw [hcutSelected]
    exact Option.some_ne_none _
  obtain ⟨d, hsStart, c, arm, hctor⟩ :=
    selected_live_continuing_constructor r owned base hstate0 hdispatchSelected hnoCut0
  have hbaseView := selected_fields_of_continuing r owned base d hsStart c arm
    selected0 hctor hselectedPrep
  rcases hbaseView with ⟨hbasePayload, hbasePending, hbaseCutoff, hbaseWeights, _, _⟩
  have hcontrolsConstructor :=
    ReferenceContinuingLiveSlicePreparation.continuing_cut_at_control
      x0 r owned base d hsStart c arm hctor
  let n := t.val - s
  have hnPrefix : s + n ≤ t.val := by dsimp [n]; omega
  have hctorBeta : (ReferenceActivePhysicalStep.prepare x0).coordinator =
      .live r owned base (.continuingChosen d hsStart c arm) := by
    exact hctor
  have hordinaryBeta : ∀ j,
      ((ReferenceActivePhysicalStep.prepare x0).followers.followers j).configuration =
        .ordinary (states j) (memories j) := by
    intro j
    have h := hprepared j
    rw [W[t.val - s].output_eq] at h
    simpa only [ReferenceActivePhysicalStep.step] using h
  refine ⟨r, owned, base, hbeta, hstate, htimeNext, hprior, hpending, hnoCut,
    hpayload, hcutoff, hweights, d, hsStart, c, arm, hctorBeta, hvalid0, states, memories,
    ?_, ?_, ?_, ?_⟩
  · exact hordinaryBeta
  · exact hfields
  · exact hpendingStatus
  · intro u
    let E_u := retainedRun rewards C_star C_h q t s hs control0 x u
    let W_u := ReferenceFirstLiveConfirmationHistory.firstLiveWindow E_u.records
    let y := ReferenceContinuingLiveSlicePreparation.inputAtControl x0 u
    rcases hcontrolsConstructor u with ⟨cU, armU, hctorInput⟩
    have hinputAt : ReferenceContinuingLiveSlicePreparation.inputAtControl x0 u =
        ReferenceLaterOptionalControlResampling.withControl beta u := by
      calc
        ReferenceContinuingLiveSlicePreparation.inputAtControl x0 u =
            ReferenceLaterOptionalControlResampling.withControl x0 u :=
          inputAtControl_eq_withControl x0 u
        _ = ReferenceLaterOptionalControlResampling.withControl beta u :=
          congrArg (fun z => ReferenceLaterOptionalControlResampling.withControl z u)
            hbeta0.symm
    have hctorY : (ReferenceActivePhysicalStep.prepare y).coordinator =
        .live r owned base (.continuingChosen d hsStart cU armU) := hctorInput
    have hnoCutU : ReferenceCollectionPhaseHistory.cutoffChosen y = false := by
      simp [ReferenceCollectionPhaseHistory.cutoffChosen, hctorY]
    have hstartU :=
      (ReferenceInitializationControlRemainder.launchStartRemainderEvent_control_independent
        rate rewards C_star C_h q t s x.1 x.2.1 control0 u).mp x.2.2
    let prefix0 := ReferenceGeneratedActivePrefixFactor.generatedActivePrefixFactor
      rate rewards C_star C_h q t control0 x.1 x.2.1 s n hs x.2.2 hnPrefix
    let prefixU := ReferenceGeneratedActivePrefixFactor.generatedActivePrefixFactor
      rate rewards C_star C_h q t u x.1 x.2.1 s n hs hstartU hnPrefix
    obtain ⟨_, _, _, _, _, _, _, hevidence⟩ :=
      ReferenceGeneratedActivePrefixFactor.generatedActivePrefixFactor_control_independent
        rate rewards C_star C_h q t x.1 x.2.1 control0 s n hs hnPrefix x.2.2 u control0
    have hprefixEvidence :
        prefix0.records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence =
          prefixU.records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence := by
      simpa only [prefix0, prefixU] using hevidence.symm
    have hmodeU : ReferenceActivePhysicalHorizon.allActiveAtStart
        (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed rate rewards C_star C_h q t u
          x.1 x.2.1 s hs hstartU) s :=
      (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
        rate rewards C_star C_h q t u x.1 x.2.1 s hs hstartU).2.1
    have hrecords0 : E.records = prefix0.records ++
        [ReferenceActivePhysicalHorizon.RoundRecord.mk
          (ReferenceActivePhysicalHorizon.roundInputAt generated source0.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p source0) rewards s hmode
            prefix0 ⟨s + n, by omega, by omega⟩)
          (ReferenceActivePhysicalStep.step
            (ReferenceActivePhysicalHorizon.roundInputAt generated source0.1.2
              (ActualInitializationPhysicalStep.selectedRowIndex p source0) rewards s hmode
              prefix0 ⟨s + n, by omega, by omega⟩)) rfl] := by
      dsimp [E, n, prefix0, ReferenceGeneratedActivePrefixFactor.generatedActivePrefixFactor]
      rw [ReferenceActivePhysicalHorizon.run_successor_step]
      exact (ReferenceActivePhysicalHorizon.foldRound_equations generated source0.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source0) rewards s hmode _
        ⟨s + n, by omega, by omega⟩).2
    have hrecordsU : E_u.records = prefixU.records ++
        [ReferenceActivePhysicalHorizon.RoundRecord.mk
          (ReferenceActivePhysicalHorizon.roundInputAt
            (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed rate rewards C_star C_h q t
              u x.1 x.2.1 s hs hstartU)
            (ReferenceGeneratedActivePrefixFactor.splitSource q t u x.1).1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p
              (ReferenceGeneratedActivePrefixFactor.splitSource q t u x.1)) rewards s hmodeU
            prefixU ⟨s + n, by omega, by omega⟩)
          (ReferenceActivePhysicalStep.step
            (ReferenceActivePhysicalHorizon.roundInputAt
              (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed rate rewards C_star C_h q t
                u x.1 x.2.1 s hs hstartU)
              (ReferenceGeneratedActivePrefixFactor.splitSource q t u x.1).1.2
              (ActualInitializationPhysicalStep.selectedRowIndex p
                (ReferenceGeneratedActivePrefixFactor.splitSource q t u x.1)) rewards s hmodeU
              prefixU ⟨s + n, by omega, by omega⟩)) rfl] := by
      dsimp [E_u, retainedRun, n, prefixU,
        ReferenceGeneratedActivePrefixFactor.generatedActivePrefixFactor]
      rw [ReferenceActivePhysicalHorizon.run_successor_step]
      exact (ReferenceActivePhysicalHorizon.foldRound_equations
        (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed rate rewards C_star C_h q t
          u x.1 x.2.1 s hs hstartU)
        (ReferenceGeneratedActivePrefixFactor.splitSource q t u x.1).1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p
          (ReferenceGeneratedActivePrefixFactor.splitSource q t u x.1)) rewards s hmodeU _
        ⟨s + n, by omega, by omega⟩).2
    have hlenPrefix0 : prefix0.records.length = n := by
      dsimp [prefix0, ReferenceGeneratedActivePrefixFactor.generatedActivePrefixFactor]
      exact ReferenceActivePhysicalHorizon.run_record_count generated source0.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source0) rewards s n (by omega) hmode
    have hlenPrefixU : prefixU.records.length = n := by
      dsimp [prefixU, ReferenceGeneratedActivePrefixFactor.generatedActivePrefixFactor]
      exact ReferenceActivePhysicalHorizon.run_record_count
        (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed rate rewards C_star C_h q t
          u x.1 x.2.1 s hs hstartU)
        (ReferenceGeneratedActivePrefixFactor.splitSource q t u x.1).1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p
          (ReferenceGeneratedActivePrefixFactor.splitSource q t u x.1)) rewards s n
        (by omega) hmodeU
    have hlenFull0 : n < E.records.length := by
      have h := ReferenceActivePhysicalHorizon.run_record_count generated source0.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source0) rewards s (n + 1)
        (by omega) hmode
      have hcount : E.records.length = n + 1 := by simpa [E] using h
      rw [hcount]
      omega
    have hlenFullU : n < E_u.records.length := by
      have h := ReferenceActivePhysicalHorizon.run_record_count
        (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed rate rewards C_star C_h q t
          u x.1 x.2.1 s hs hstartU)
        (ReferenceGeneratedActivePrefixFactor.splitSource q t u x.1).1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p
          (ReferenceGeneratedActivePrefixFactor.splitSource q t u x.1)) rewards s (n + 1)
        (by omega) hmodeU
      have hcount : E_u.records.length = n + 1 := by
        dsimp [E_u, retainedRun]
        simpa [n] using h
      rw [hcount]
      omega
    have hsameEvidence : ∀ j (hj : j < n),
        (E.records[j]'(by omega)).evidence = (E_u.records[j]'(by omega)).evidence := by
      intro j hj
      have hj0 : j < prefix0.records.length := by omega
      have hjU : j < prefixU.records.length := by omega
      have hrecord0 : E.records[j]'(by omega) = prefix0.records[j]'hj0 := by
        apply Option.some.inj
        calc
          some (E.records[j]'(by omega)) = E.records[j]? :=
            (List.getElem?_eq_getElem (by omega)).symm
          _ = (prefix0.records ++ _)[j]? :=
            congrArg (fun rs : List (Record (p := p) (rate := rate)) => rs[j]?) hrecords0
          _ = prefix0.records[j]? :=
            List.getElem?_append_left (by rw [hlenPrefix0]; omega)
          _ = some (prefix0.records[j]'hj0) := List.getElem?_eq_getElem hj0
      have hrecordU : E_u.records[j]'(by omega) = prefixU.records[j]'hjU := by
        apply Option.some.inj
        calc
          some (E_u.records[j]'(by omega)) = E_u.records[j]? :=
            (List.getElem?_eq_getElem (by omega)).symm
          _ = (prefixU.records ++ _)[j]? :=
            congrArg (fun rs : List (Record (p := p) (rate := rate)) => rs[j]?) hrecordsU
          _ = prefixU.records[j]? :=
            List.getElem?_append_left (by rw [hlenPrefixU]; omega)
          _ = some (prefixU.records[j]'hjU) := List.getElem?_eq_getElem hjU
      rw [hrecord0, hrecordU]
      have hjMap : j < (prefix0.records.map
          ReferenceActivePhysicalHorizon.RoundRecord.evidence).length := by
        simpa only [List.length_map] using hj0
      simpa only [List.getElem_map] using List.getElem_of_eq hprefixEvidence hjMap
    have hlastRecord : E_u.records[n]'hlenFullU =
        ReferenceActivePhysicalHorizon.RoundRecord.mk
          (ReferenceActivePhysicalHorizon.roundInputAt
            (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed rate rewards C_star C_h q t
              u x.1 x.2.1 s hs hstartU)
            (ReferenceGeneratedActivePrefixFactor.splitSource q t u x.1).1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p
              (ReferenceGeneratedActivePrefixFactor.splitSource q t u x.1)) rewards s hmodeU
            prefixU ⟨s + n, by omega, by omega⟩)
          (ReferenceActivePhysicalStep.step
            (ReferenceActivePhysicalHorizon.roundInputAt
              (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed rate rewards C_star C_h q t
                u x.1 x.2.1 s hs hstartU)
              (ReferenceGeneratedActivePrefixFactor.splitSource q t u x.1).1.2
              (ActualInitializationPhysicalStep.selectedRowIndex p
                (ReferenceGeneratedActivePrefixFactor.splitSource q t u x.1)) rewards s hmodeU
              prefixU ⟨s + n, by omega, by omega⟩)) rfl :=
      List.getElem_of_append hrecordsU hlenPrefixU
    have hnextInput :
        (ReferenceActivePhysicalHorizon.roundInputAt
          (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed rate rewards C_star C_h q t
            u x.1 x.2.1 s hs hstartU)
          (ReferenceGeneratedActivePrefixFactor.splitSource q t u x.1).1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p
            (ReferenceGeneratedActivePrefixFactor.splitSource q t u x.1)) rewards s hmodeU
          prefixU ⟨s + n, by omega, by omega⟩) =
          ReferenceRetainedBoundaryMeasurability.retainedGeneratedNextInput
            rate rewards C_star C_h q t s hs control0 x u := by
      have hrun :
          ReferenceActivePhysicalHorizon.run
              (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed rate rewards C_star C_h q t
                u x.1 x.2.1 s hs hstartU)
              (ReferenceGeneratedActivePrefixFactor.splitSource q t u x.1).1.2
              (ActualInitializationPhysicalStep.selectedRowIndex p
                (ReferenceGeneratedActivePrefixFactor.splitSource q t u x.1)) rewards s
              (t.val - s) (by omega) hmodeU = prefixU := by
        dsimp [prefixU, ReferenceGeneratedActivePrefixFactor.generatedActivePrefixFactor]
      have hentry :
          (⟨t.val, by constructor <;> omega⟩ : ReferenceActivePhysicalHorizon.CalendarEntry p s) =
            ⟨s + n, by constructor <;> omega⟩ := by
        apply Subtype.ext
        simp [n, Nat.add_sub_of_le hs]
      dsimp [ReferenceRetainedBoundaryMeasurability.retainedGeneratedNextInput,
        ReferenceGeneratedActivePrefixFactor.generatedActivePrefixFactor, prefixU]
      rw [hrun, hentry]
    have hnextWithControl :=
      ReferenceFirstLiveOccupiedPreparationControl.retained_generated_next_input_eq_withControl
        rewards C_star C_h q t s hs control0 x u
    have hlastInput : (E_u.records[n]'hlenFullU).input = y := by
      rw [hlastRecord]
      calc
        _ = ReferenceRetainedBoundaryMeasurability.retainedGeneratedNextInput
            rate rewards C_star C_h q t s hs control0 x u := hnextInput
        _ = ReferenceLaterOptionalControlResampling.withControl beta u := hnextWithControl
        _ = y := hinputAt.symm
    have hnoCutCurrent : ReferenceCollectionPhaseHistory.cutoffChosen
        (E_u.records[n]'hlenFullU).input = false := by
      rw [hlastInput]
      exact hnoCutU
    have hbaselineLength : n ≤ E.records.length := by omega
    have hwindowLength := firstLive_prefix_transfer E.records E_u.records n
      hbaselineLength hn hlenFullU hsameEvidence hnoCutCurrent
    have hwindowPrefixU : W_u.IsPrefix E_u.records := by
      simp only [W_u, ReferenceFirstLiveConfirmationHistory.firstLiveWindow]
      exact List.takeWhile_prefix _
    have hwindowRecord : W_u[n]'hwindowLength = E_u.records[n]'hlenFullU :=
      hwindowPrefixU.getElem hwindowLength
    have hinputCurrent : (W_u[n]'hwindowLength).input = y := by
      rw [hwindowRecord]
      exact hlastInput
    have hinputActual : (W_u[n]'hwindowLength).input =
        ReferenceLaterOptionalControlResampling.withControl beta u :=
      hinputCurrent.trans hinputAt
    let selectedU : Selection (p := p) (rate := rate) y := {
      view := {
        payload := r.payload
        pendingAtChoice := d.startResult.pending
        cutoff := CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u
        complementWeights := (ReferenceActivePhysicalStep.liveRegistersAt r y.time).complementWeights }
      started := d.startResult
      pending_eq := rfl
      cutoff_eq := rfl
      arm := armU.arm
      choice_eq := by
        exact armU.armChoice_eq }
    have hselectedU : (ReferenceActivePhysicalStep.prepare y).coordinator.selection =
        some selectedU := by
      rw [hctorY]
      simp [ReferenceActivePhysicalStep.DispatchCut.selection,
        ReferenceActivePhysicalStep.selectionAt, selectedU]
    have hviewU := selected_fields_of_continuing (x := y) r owned base d hsStart cU armU
      selectedU hctorY hselectedU
    rcases hviewU with ⟨hpayloadU, hpendingU, hcutoffU, hweightsU, _hstartedU, _harmU⟩
    have hselectedPayload : selectedU.view.payload = selected0.view.payload :=
      hpayloadU.trans hbasePayload.symm
    have hselectedPending : selectedU.view.pendingAtChoice = selected0.view.pendingAtChoice :=
      hpendingU.trans hbasePending.symm
    have hselectedCutoff : selectedU.view.cutoff = selected0.view.cutoff :=
      hcutoffU.trans hbaseCutoff.symm
    have hselectedWeights : HEq selectedU.view.complementWeights selected0.view.complementWeights := by
      have htime : y.time = x0.time := by
        simp [y, ReferenceContinuingLiveSlicePreparation.inputAtControl_time]
      rw [htime] at hweightsU
      exact HEq.trans hweightsU hbaseWeights.symm
    have hordinaryU : ∀ j,
        ((ReferenceActivePhysicalStep.prepare y).followers.followers j).configuration =
          .ordinary (states j) (memories j) := by
      dsimp only [y]
      rw [hinputAt]
      exact hcontrols u
    refine ⟨hwindowLength, hinputActual, hinputAt, ?_, ?_, ?_⟩
    · rw [hinputCurrent]
      exact hnoCutU
    · rw [hinputCurrent]
      exact hordinaryU
    · have houtput : (W_u[n]'hwindowLength).output.preparation =
          ReferenceActivePhysicalStep.prepare (W_u[n]'hwindowLength).input := by
        rw [(W_u[n]'hwindowLength).output_eq]
        rfl
      rw [houtput, hinputCurrent]
      refine ⟨selectedU, hselectedU, hselectedU, hselectedPayload, hselectedPending,
        hselectedCutoff, hselectedWeights, ?_⟩
      intro j
      rw [hselectedPayload]
      change j ∈ ReferencePhysicalReleaseQuota.pendingAtStart
        selected0.view.payload x0.time x0.state ↔ (states j).status = .pending
      rw [← hbeta0]
      exact hpendingStatus j

end Bandits.Support.ReferenceFirstLiveReleaseControlTransport

end
