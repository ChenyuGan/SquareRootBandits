/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveReleaseSliceMass
public import Mathlib.Data.List.TakeWhile

/-!
# First-live selected-empty release branch

Sources: `sources/zip4/manuscript/05_binary_transport.tex:74-124,293-345`,
`sources/zip4/manuscript/06_interruptions.tex:435-492`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-79`.

This module defines the computed selected-empty incoming-release branch on the
accepted retained remainder and identifies its actual whole-control UP and
DATA section masses.  Original-source cylinder events and their integral
identities are not exported here.  The source law remains unnormalized; the
original selected row, generated seed, whole rewards, current time, and all
exceptional physical paths are retained.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceActiveHorizonMeasurability
open Bandits.Support.ReferenceGeneratedActivePrefixFactor
open Bandits.Support.ReferenceRetainedBoundaryMeasurability
open Bandits.Support.ReferenceFirstLiveReleaseControlTransport
open Bandits.Support.ReferenceFirstLiveReleaseGeometry
open Bandits.Support.ReferenceFirstLiveConfirmationHistory
open Bandits.Support.ReferenceRetainedSourceCoupling
open Bandits.Support.ReferencePhysicalReleaseQuota
open Bandits.Support.ReferencePhysicalReleaseObservability
open Bandits.Support.ReferenceLiveDispatchOutputMeasurability
open Bandits.Support.ReferenceDownReceptionMeasurability
open Bandits.Support.ReferenceCollectionServiceTailMeasurability
open Bandits.Support.ReferenceLaterOptionalControlResampling
open Bandits.Support.CoordinatorPhaseClock
open Bandits.Support.CoordinatorLiveChoiceRecorderStep
open Bandits.Support.CoordinatorRoundDispatch
open Bandits.Support.CoordinatorStartRoundCutoffDispatch
open Bandits.Support.CoordinatorLiveServiceFinish
open Bandits.Support.CoordinatorRecorderComplementBridge
open Bandits.Support.CoordinatorCollectionLedger
open Bandits.Support.CoordinatorCollectionUpRoundStep
open Bandits.Support.CoordinatorRecordingOperation
open scoped Classical ENNReal

namespace Bandits.Support.ReferenceFirstLiveReleaseSourceCylinder

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev TimeControl := ContinuousLearningRows.TimeControl
abbrev Selection := ReferenceFirstLiveReleaseControlTransport.Selection
abbrev RetainedLaunchStart := ReferenceFirstLiveReleaseControlTransport.RetainedLaunchStart
abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput

variable {p : Parameters} {rate : RateInput p}

abbrev Record (p : Parameters) (rate : RateInput p) :=
  ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)

local instance choiceCutoffMeasurableSpace :
    MeasurableSpace (Option (CoordinatorLocalArmChoice.Cutoff p)) := ⊤

local instance coordinatorFailureDiscrete :
    DiscreteMeasurableSpace ReferenceActivePhysicalStep.CoordinatorFailure := ⟨fun _ => trivial⟩

local notation "B" => ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary
local notation "T" => ReferenceFirstLiveReleaseControlTransport.retainedWindow

private def collectionObservation
    (o : ReferenceActivePhysicalStep.CoordinatorObservation p rate) : Bool :=
  match o with
  | ⟨.collection _ _ _, _, _, _, _⟩ => true
  | ⟨.dagger, _, some (.collection _), _, _⟩ => true
  | _ => false

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
  | live r q base => simp only [CoordinatorRoundDispatch.dispatch]; exact hc
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
      | invalid => simp [hledger, collectionObservation, ReferenceActivePhysicalStep.coordinatorFailure]
      | rejected bad => simp [hledger, collectionObservation, ReferenceActivePhysicalStep.coordinatorFailure]
      | success ledgerFinished =>
          cases hclock : CoordinatorPhaseClock.finishRound p rate.eta.val x.time started.clock
              ledgerFinished.pending x.row with
          | error reason => simp [hledger, hclock, collectionObservation,
              ReferenceActivePhysicalStep.coordinatorFailure]
          | ok clockFinished => simp [hledger, hclock, collectionObservation]
  | rejected pair =>
      rcases pair with ⟨ledger, bank⟩
      cases hledger : CoordinatorCollectionLedger.finishRound ledger with
      | invalid => simp [hledger, collectionObservation, ReferenceActivePhysicalStep.coordinatorFailure]
      | rejected bad => simp [hledger, collectionObservation, ReferenceActivePhysicalStep.coordinatorFailure]
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

/-- The physical take-while cutoff is recovered from the actual encoded
before-state and full coordinator diagnostic, including failed collection
tails and dagger. -/
private theorem cutoffChosen_eq_evidence
    (record : Record p rate) :
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
            | cutoffChosen dispatched hstart ledger hinitialization hledger hvalid hclock hpending hnone arm =>
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
            | cutoffChosen dispatched hstart ledger hinitialization hledger hvalid hclock hpending hnone arm =>
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
      simp [hcut, evidenceCutoff, ReferenceActivePhysicalHorizon.RoundRecord.evidence, hstate]
  | dagger =>
      have hcut : ReferenceCollectionPhaseHistory.cutoffChosen record.input = false := by
        by_contra hn
        have htrue : ReferenceCollectionPhaseHistory.cutoffChosen record.input = true :=
          Bool.eq_true_of_not_eq_false hn
        unfold ReferenceCollectionPhaseHistory.cutoffChosen at htrue
        cases hprep : (ReferenceActivePhysicalStep.prepare record.input).coordinator with
        | live r q base outcome =>
            cases outcome with
            | cutoffChosen dispatched hstart ledger hinitialization hledger hvalid hclock hpending hnone arm =>
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

/-- The computed selected-empty incoming-release branch on the actual
retained remainder subtype. Every witness is read from its baseline run. -/
def selectedEmptyPendingRemainder
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p) (i : Fin (p.m - 1)) :
    Set (RetainedLaunchStart (p := p) (rate := rate)
      rewards C_star C_h q t s hs control0) :=
  {x | ∃ hn : t.val - s < (T rewards C_star C_h q t s hs control0 x control0).length,
    ∃ selected0 : Selection (p := p) (rate := rate)
      ((T rewards C_star C_h q t s hs control0 x control0).get ⟨t.val - s, hn⟩).input,
      ((T rewards C_star C_h q t s hs control0 x control0).get ⟨t.val - s, hn⟩).output.preparation.coordinator.selection = some selected0 ∧
      selected0.view.pendingAtChoice = ∅ ∧
      i ∈ ReferencePhysicalReleaseQuota.pendingAtStart selected0.view.payload
        (B rate rewards C_star C_h q t s hs control0 x).time
        (B rate rewards C_star C_h q t s hs control0 x).state}

/-- The literal branch is exactly the complete telescope consumed by M; its
window, optional-selection, empty-pending, and incoming-pending witnesses are
not caller inputs. -/
theorem mem_selectedEmptyPendingRemainder_iff
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p) (i : Fin (p.m - 1))
    (x : RetainedLaunchStart (p := p) (rate := rate)
      rewards C_star C_h q t s hs control0) :
    x ∈ selectedEmptyPendingRemainder rewards C_star C_h q t s hs control0 i ↔
      ∃ hn : t.val - s < (T rewards C_star C_h q t s hs control0 x control0).length,
      ∃ selected0 : Selection (p := p) (rate := rate)
        ((T rewards C_star C_h q t s hs control0 x control0).get ⟨t.val - s, hn⟩).input,
        ((T rewards C_star C_h q t s hs control0 x control0).get ⟨t.val - s, hn⟩).output.preparation.coordinator.selection = some selected0 ∧
        selected0.view.pendingAtChoice = ∅ ∧
        i ∈ ReferencePhysicalReleaseQuota.pendingAtStart selected0.view.payload
          (B rate rewards C_star C_h q t s hs control0 x).time
          (B rate rewards C_star C_h q t s hs control0 x).state := by
  rfl

private def retainedRunInput
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p)
    (x : RetainedLaunchStart (p := p) (rate := rate)
      rewards C_star C_h q t s hs control0) :
    ReferenceActiveHorizonMeasurability.ActiveRunInput (p := p) (rate := rate) s := by
  let seed := ReferenceRetainedBoundaryMeasurability.retainedGeneratedActiveSeed
    rate rewards C_star C_h q t s hs control0 x
  let source := ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.1
  have hmode : ReferenceActivePhysicalHorizon.allActiveAtStart seed s := by
    simpa [seed, ReferenceRetainedBoundaryMeasurability.retainedGeneratedActiveSeed] using
      (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
      rate rewards C_star C_h q t control0 x.1 x.2.1 s hs x.2.2).2.1
  exact ⟨(seed, (source.1.2, (q, rewards))), hmode⟩

/-- The count-bounded observation of the same generated source run used by
T. Its calendar is the original interval `s,...,t`, including the current
round and with no terminal sentinel. -/
private def retainedRunObservation
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p)
    (x : RetainedLaunchStart (p := p) (rate := rate)
      rewards C_star C_h q t s hs control0) :
    ReferenceActiveHorizonMeasurability.RunObservationCode (p := p) (rate := rate) :=
  ReferenceActiveHorizonMeasurability.runObservation s (t.val - s + 1) (by omega)
    (retainedRunInput rewards C_star C_h q t s hs control0 x)

private theorem retainedRunObservation_records_eq
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p)
    (x : RetainedLaunchStart (p := p) (rate := rate)
      rewards C_star C_h q t s hs control0) :
    (retainedRunObservation rewards C_star C_h q t s hs control0 x).2 =
      (ReferenceFirstLiveReleaseControlTransport.retainedRun
        rewards C_star C_h q t s hs control0 x control0).records.map
        ReferenceActiveHorizonMeasurability.roundRecordCode := by
  let source := ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.1
  have hindex : ActualInitializationPhysicalStep.selectedRowIndex p source = q :=
    ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_symm_coordinatorIndex
      p q t control0 x.1 x.2.1
  have hrun :
      ReferenceActiveHorizonMeasurability.runOfInput s (t.val - s + 1) (by omega)
          (retainedRunInput rewards C_star C_h q t s hs control0 x) =
        ReferenceFirstLiveReleaseControlTransport.retainedRun
          rewards C_star C_h q t s hs control0 x control0 := by
    rw [ReferenceFirstLiveReleaseControlTransport.retainedRun_eq_run
      rewards C_star C_h q t s hs control0 x control0]
    simp [ReferenceActiveHorizonMeasurability.runOfInput, retainedRunInput,
      ReferenceRetainedBoundaryMeasurability.retainedGeneratedActiveSeed,
      source, hindex]
  unfold retainedRunObservation
  rw [ReferenceActiveHorizonMeasurability.runObservation_records]
  change (ReferenceActiveHorizonMeasurability.runOfInput s (t.val - s + 1) (by omega)
      (retainedRunInput rewards C_star C_h q t s hs control0 x)).records.map _ = _
  rw [hrun]

private theorem retainedRun_records_length
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p)
    (x : RetainedLaunchStart (p := p) (rate := rate)
      rewards C_star C_h q t s hs control0) :
    (ReferenceFirstLiveReleaseControlTransport.retainedRun
      rewards C_star C_h q t s hs control0 x control0).records.length = t.val - s + 1 := by
  have hcount := ReferenceActiveHorizonMeasurability.runObservation_recordCount
    s (t.val - s + 1) (by omega)
    (retainedRunInput rewards C_star C_h q t s hs control0 x)
  change (retainedRunObservation rewards C_star C_h q t s hs control0 x).2.length =
    t.val - s + 1 at hcount
  rw [retainedRunObservation_records_eq] at hcount
  simpa using hcount

private theorem retainedRunObservation_at
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p)
    (x : RetainedLaunchStart (p := p) (rate := rate)
      rewards C_star C_h q t s hs control0)
    (k : Fin (t.val - s + 1)) :
    ReferenceActiveHorizonMeasurability.listObservationAt
        (retainedRunObservation rewards C_star C_h q t s hs control0 x).2 k.val =
      Sum.inr (ReferenceActiveHorizonMeasurability.roundRecordCode
        ((ReferenceFirstLiveReleaseControlTransport.retainedRun
          rewards C_star C_h q t s hs control0 x control0).records.get
            ⟨k.val, by
              rw [retainedRun_records_length]
              exact k.isLt⟩)) := by
  rw [retainedRunObservation_records_eq]
  unfold ReferenceActiveHorizonMeasurability.listObservationAt
  have hindex : k.val <
      (ReferenceFirstLiveReleaseControlTransport.retainedRun
        rewards C_star C_h q t s hs control0 x control0).records.length := by
    rw [retainedRun_records_length]
    exact k.isLt
  rw [List.getElem?_map, List.getElem?_eq_getElem hindex]
  rfl

private theorem measurable_retainedRunObservation
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p) :
    Measurable (fun x : RetainedLaunchStart (p := p) (rate := rate)
      rewards C_star C_h q t s hs control0 =>
        retainedRunObservation rewards C_star C_h q t s hs control0 x) := by
  let source := fun x : RetainedLaunchStart (p := p) (rate := rate)
      rewards C_star C_h q t s hs control0 =>
    ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.1
  have hsource : Measurable source := by
    change Measurable (fun x : RetainedLaunchStart (p := p) (rate := rate)
      rewards C_star C_h q t s hs control0 =>
        (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).symm
          (control0, x.1))
    exact (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).symm.measurable.comp
      (measurable_const.prodMk measurable_subtype_coe)
  have hseed := ReferenceRetainedBoundaryMeasurability.measurable_retainedGeneratedActiveSeed
    rate rewards C_star C_h q t s hs control0
  have hdata : Measurable (fun x : RetainedLaunchStart (p := p) (rate := rate)
      rewards C_star C_h q t s hs control0 =>
        (ReferenceRetainedBoundaryMeasurability.retainedGeneratedActiveSeed
          rate rewards C_star C_h q t s hs control0 x,
          ((source x).1.2, (q, rewards)))) := by
    exact hseed.prodMk ((measurable_snd.comp (measurable_fst.comp hsource)).prodMk
      (measurable_const.prodMk measurable_const))
  have hmode : ∀ x : RetainedLaunchStart (p := p) (rate := rate)
      rewards C_star C_h q t s hs control0,
      ReferenceActivePhysicalHorizon.allActiveAtStart
        (ReferenceRetainedBoundaryMeasurability.retainedGeneratedActiveSeed
          rate rewards C_star C_h q t s hs control0 x) s := by
    intro x
    exact (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec rate rewards C_star C_h q t
      control0 x.1 x.2.1 s hs x.2.2).2.1
  let runInput : RetainedLaunchStart (p := p) (rate := rate)
      rewards C_star C_h q t s hs control0 →
      ReferenceActiveHorizonMeasurability.ActiveRunInput (p := p) (rate := rate) s :=
    fun x =>
    ⟨(ReferenceRetainedBoundaryMeasurability.retainedGeneratedActiveSeed
        rate rewards C_star C_h q t s hs control0 x,
      ((source x).1.2, (q, rewards))), hmode x⟩
  have hrunInput : Measurable runInput := hdata.subtype_mk
  exact (ReferenceActiveHorizonMeasurability.measurable_runObservation
    s (t.val - s + 1) (by omega)).comp hrunInput

/-- The actual code at elapsed index `n`, retaining absence separately from
all encoded physical fields. -/
private def retainedCurrentCode
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p)
    (x : RetainedLaunchStart (p := p) (rate := rate)
      rewards C_star C_h q t s hs control0) :
    Unit ⊕ ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate) :=
  ReferenceActiveHorizonMeasurability.listObservationAt
    (retainedRunObservation rewards C_star C_h q t s hs control0 x).2
    (t.val - s)

private theorem measurable_retainedCurrentCode
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p) :
    Measurable (fun x : RetainedLaunchStart (p := p) (rate := rate)
      rewards C_star C_h q t s hs control0 =>
        retainedCurrentCode rewards C_star C_h q t s hs control0 x) := by
  have hobs := measurable_retainedRunObservation (rate := rate)
    rewards C_star C_h q t s hs control0
  have hcoords := ReferenceActiveHorizonMeasurability.measurable_listObservationCoordinates.comp
    (measurable_snd.comp hobs)
  exact (measurable_pi_apply (t.val - s)).comp (measurable_snd.comp hcoords)

private def retainedSelectionDataAt
    (code : Unit ⊕ ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate)) :
    Option (ReferenceLiveDispatchOutputMeasurability.SelectionData p rate) :=
  match code with
  | .inl _ => none
  | .inr record => record.2.2.1.1

private theorem measurable_retainedSelectionDataAt :
    Measurable (retainedSelectionDataAt (p := p) (rate := rate)) := by
  exact Measurable.sumElim measurable_const
    (measurable_fst.comp (measurable_fst.comp
      (measurable_snd.comp (measurable_snd.comp measurable_id))))

private def retainedPayloadAt
    (code : Unit ⊕ ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate)) :
    Option (ReferenceActivePhysicalStep.Payload rate) :=
  (retainedSelectionDataAt code).map fun selection => selection.1.payload

private theorem measurable_retainedPayloadAt :
    Measurable (retainedPayloadAt (p := p) (rate := rate)) := by
  have hviewObs : Measurable
      (ReferenceDownReceptionMeasurability.choiceTimeViewObservation
        (p := p) (rate := rate)) := comap_measurable _
  have hpayload : Measurable (fun view : ReferenceDownReception.ChoiceTimeView p rate.eta =>
      view.payload) := measurable_fst.comp hviewObs
  apply LaterAssignmentFullOutputMeasurability.measurable_optionMap
    (fun selection : ReferenceLiveDispatchOutputMeasurability.SelectionData p rate =>
      selection.1.payload)
  · exact hpayload.comp measurable_fst
  · exact measurable_retainedSelectionDataAt

private def selectedEmptyPendingAtSelection (i : Fin (p.m - 1))
    (z : Option (ReferenceLiveDispatchOutputMeasurability.SelectionData p rate) ×
      (Fin p.T × ReferenceActivePhysicalStep.State p rate)) : Bool :=
  match z.1 with
  | none => false
  | some selection => decide (selection.1.pendingAtChoice = ∅) &&
      decide (i ∈ ReferencePhysicalReleaseQuota.pendingAtStart
        selection.1.payload z.2.1 z.2.2)

private theorem measurable_selectedEmptyPendingAtSelection (i : Fin (p.m - 1)) :
    Measurable (selectedEmptyPendingAtSelection (p := p) (rate := rate) i) := by
  let viewObservation := ReferenceDownReceptionMeasurability.choiceTimeViewObservation
    (p := p) (rate := rate)
  have hviewObservation : Measurable viewObservation := comap_measurable _
  have hviewPayload : Measurable (fun view :
      ReferenceDownReception.ChoiceTimeView p rate.eta => view.payload) :=
    measurable_fst.comp hviewObservation
  have hviewPending : Measurable (fun view :
      ReferenceDownReception.ChoiceTimeView p rate.eta => view.pendingAtChoice) :=
    measurable_fst.comp (measurable_snd.comp hviewObservation)
  have hselectionView : Measurable (fun z :
      ReferenceLiveDispatchOutputMeasurability.SelectionData p rate ×
        (Fin p.T × ReferenceActivePhysicalStep.State p rate) => z.1.1) := by
    exact (measurable_fst : Measurable
      (fun z : ReferenceLiveDispatchOutputMeasurability.SelectionData p rate => z.1)).comp
        measurable_fst
  have hpayload : Measurable (fun z :
      ReferenceLiveDispatchOutputMeasurability.SelectionData p rate ×
        (Fin p.T × ReferenceActivePhysicalStep.State p rate) => z.1.1.payload) :=
    hviewPayload.comp hselectionView
  have hpending : Measurable (fun z :
      ReferenceLiveDispatchOutputMeasurability.SelectionData p rate ×
        (Fin p.T × ReferenceActivePhysicalStep.State p rate) => z.1.1.pendingAtChoice) :=
    hviewPending.comp hselectionView
  have hpendingSet : Measurable (fun z :
      ReferenceLiveDispatchOutputMeasurability.SelectionData p rate ×
        (Fin p.T × ReferenceActivePhysicalStep.State p rate) =>
      ReferencePhysicalReleaseQuota.pendingAtStart z.1.1.payload z.2.1 z.2.2) :=
    ReferencePhysicalReleaseObservability.measurable_pendingAtStart.comp
      (hpayload.prodMk measurable_snd)
  have hempty : Measurable (fun z :
      ReferenceLiveDispatchOutputMeasurability.SelectionData p rate ×
        (Fin p.T × ReferenceActivePhysicalStep.State p rate) =>
      decide (z.1.1.pendingAtChoice = (∅ : Finset (Fin (p.m - 1))))) := by
    convert (measurable_of_finite fun P : Finset (Fin (p.m - 1)) =>
      decide (P = ∅)).comp hpending using 1
    funext z
    exact decide_eq_decide.mpr Iff.rfl
  have hmember : Measurable (fun z :
      ReferenceLiveDispatchOutputMeasurability.SelectionData p rate ×
        (Fin p.T × ReferenceActivePhysicalStep.State p rate) =>
      decide (i ∈ ReferencePhysicalReleaseQuota.pendingAtStart
        z.1.1.payload z.2.1 z.2.2)) :=
    (measurable_of_finite fun P : Finset (Fin (p.m - 1)) => decide (i ∈ P)).comp
      hpendingSet
  have hbase : Measurable (fun z :
      ReferenceLiveDispatchOutputMeasurability.SelectionData p rate ×
        (Fin p.T × ReferenceActivePhysicalStep.State p rate) =>
      decide (z.1.1.pendingAtChoice = ∅) &&
        decide (i ∈ ReferencePhysicalReleaseQuota.pendingAtStart
          z.1.1.payload z.2.1 z.2.2)) := by
    convert (measurable_of_finite fun b : Bool × Bool => b.1 && b.2).comp
      (hempty.prodMk hmember) using 1
    funext z
    apply congrArg₂ Bool.and
    · exact decide_eq_decide.mpr Iff.rfl
    · exact decide_eq_decide.mpr Iff.rfl
  let e : (Option (ReferenceLiveDispatchOutputMeasurability.SelectionData p rate) ×
      (Fin p.T × ReferenceActivePhysicalStep.State p rate)) ≃ᵐ
      ((ReferenceLiveDispatchOutputMeasurability.SelectionData p rate ×
          (Fin p.T × ReferenceActivePhysicalStep.State p rate)) ⊕
        (PUnit × (Fin p.T × ReferenceActivePhysicalStep.State p rate))) := by
    let optionEquiv : Option (ReferenceLiveDispatchOutputMeasurability.SelectionData p rate) ≃ᵐ
        ReferenceLiveDispatchOutputMeasurability.SelectionData p rate ⊕ PUnit := {
      toEquiv := Equiv.optionEquivSumPUnit _
      measurable_toFun := comap_measurable _
      measurable_invFun := by
        rw [measurable_comap_iff]
        exact measurable_id }
    exact (MeasurableEquiv.prodCongr optionEquiv
        (MeasurableEquiv.refl (Fin p.T × ReferenceActivePhysicalStep.State p rate))).trans
      (MeasurableEquiv.sumProdDistrib
        (ReferenceLiveDispatchOutputMeasurability.SelectionData p rate) PUnit
        (Fin p.T × ReferenceActivePhysicalStep.State p rate))
  let read : ((ReferenceLiveDispatchOutputMeasurability.SelectionData p rate ×
      (Fin p.T × ReferenceActivePhysicalStep.State p rate)) ⊕
        (PUnit × (Fin p.T × ReferenceActivePhysicalStep.State p rate))) → Bool :=
    Sum.elim (fun z => decide (z.1.1.pendingAtChoice = ∅) &&
      decide (i ∈ ReferencePhysicalReleaseQuota.pendingAtStart
        z.1.1.payload z.2.1 z.2.2)) (fun _ => false)
  have hread : Measurable read := Measurable.sumElim hbase measurable_const
  have hcompose := hread.comp e.measurable_toFun
  have heq : (fun z => read (e z)) = selectedEmptyPendingAtSelection i := by
    funext z
    rcases z with ⟨selection?, beta⟩
    cases selection? <;> rfl
  exact heq ▸ hcompose

private def selectedEmptyPendingCode
    (code : Unit ⊕ ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate))
    (beta : ReferenceActivePhysicalStep.RoundInput p rate) (i : Fin (p.m - 1)) : Bool :=
  selectedEmptyPendingAtSelection i
    (retainedSelectionDataAt code, (beta.time, beta.state))

private theorem measurable_selectedEmptyPendingCode (i : Fin (p.m - 1)) :
    Measurable (fun z :
      (Unit ⊕ ReferenceActiveHorizonMeasurability.RoundRecordCode
          (p := p) (rate := rate)) × ReferenceActivePhysicalStep.RoundInput p rate =>
      selectedEmptyPendingCode z.1 z.2 i) := by
  have hselected : Measurable (fun z :
      (Unit ⊕ ReferenceActiveHorizonMeasurability.RoundRecordCode
          (p := p) (rate := rate)) × ReferenceActivePhysicalStep.RoundInput p rate =>
      retainedSelectionDataAt z.1) :=
    measurable_retainedSelectionDataAt.comp measurable_fst
  have hencoded := ReferenceActivePhysicalStepMeasurability.measurable_encodeRoundInput.comp
    (measurable_snd : Measurable (fun z :
      (Unit ⊕ ReferenceActiveHorizonMeasurability.RoundRecordCode
          (p := p) (rate := rate)) × ReferenceActivePhysicalStep.RoundInput p rate => z.2))
  have hvalue := measurable_subtype_coe.comp hencoded
  have htime : Measurable (fun z :
      (Unit ⊕ ReferenceActiveHorizonMeasurability.RoundRecordCode
          (p := p) (rate := rate)) × ReferenceActivePhysicalStep.RoundInput p rate =>
      (ReferenceActivePhysicalStepMeasurability.encodeRoundInput z.2).val.2.2.2.1) :=
    measurable_fst.comp (measurable_snd.comp (measurable_snd.comp
      (measurable_snd.comp hvalue)))
  have hstate : Measurable (fun z :
      (Unit ⊕ ReferenceActiveHorizonMeasurability.RoundRecordCode
          (p := p) (rate := rate)) × ReferenceActivePhysicalStep.RoundInput p rate =>
      (ReferenceActivePhysicalStepMeasurability.encodeRoundInput z.2).val.1) :=
    measurable_fst.comp hvalue
  exact (measurable_selectedEmptyPendingAtSelection i).comp
    (hselected.prodMk (htime.prodMk hstate))

private theorem outputSelection_eq_dispatch (record : Record p rate) :
    record.output.preparation.coordinator.selection =
      (ReferenceActivePhysicalStep.dispatch record.input).selection := by
  calc
    record.output.preparation.coordinator.selection =
        (ReferenceActivePhysicalStep.step record.input).preparation.coordinator.selection :=
      congrArg (fun output : ReferenceActivePhysicalStep.RoundOutput record.input =>
        output.preparation.coordinator.selection) record.output_eq
    _ = (ReferenceActivePhysicalStep.prepare record.input).coordinator.selection := rfl
    _ = (ReferenceActivePhysicalStep.dispatch record.input).selection :=
      congrArg (fun cut : ReferenceActivePhysicalStep.DispatchCut record.input => cut.selection)
        (ReferenceActivePhysicalStep.prepare record.input).coordinator_eq

private theorem retainedSelectionDataAt_roundRecord (record : Record p rate) :
    retainedSelectionDataAt
        (Sum.inr (ReferenceActiveHorizonMeasurability.roundRecordCode record)) =
      record.output.preparation.coordinator.selection.map
        (ReferenceLiveDispatchOutputMeasurability.encodeSelection) := by
  change (ReferenceActiveHorizonMeasurability.roundRecordCode record).2.2.1.1 = _
  rw [ReferenceActiveHorizonMeasurability.roundRecordCode_front record |>.1,
    outputSelection_eq_dispatch]

private theorem selectedEmptyPendingCode_roundRecord_iff
    (record : Record p rate) (beta : ReferenceActivePhysicalStep.RoundInput p rate)
    (i : Fin (p.m - 1)) :
    selectedEmptyPendingCode
        (Sum.inr (ReferenceActiveHorizonMeasurability.roundRecordCode record)) beta i = true ↔
      ∃ selected0 : Selection (p := p) (rate := rate) record.input,
        record.output.preparation.coordinator.selection = some selected0 ∧
        selected0.view.pendingAtChoice = ∅ ∧
        i ∈ ReferencePhysicalReleaseQuota.pendingAtStart selected0.view.payload
          beta.time beta.state := by
  cases hselected : record.output.preparation.coordinator.selection with
  | none =>
      simp [selectedEmptyPendingCode, selectedEmptyPendingAtSelection,
        retainedSelectionDataAt_roundRecord, hselected]
  | some selected0 =>
      simp [selectedEmptyPendingCode, selectedEmptyPendingAtSelection,
        retainedSelectionDataAt_roundRecord, hselected,
        ReferenceLiveDispatchOutputMeasurability.encodeSelection]

private abbrev CoordinatorCode (p : Parameters) (rate : RateInput p) :=
  ReferenceActivePhysicalStepMeasurability.CoordinatorCode p rate

private def coordinatorCodeTag {p : Parameters} {rate : RateInput p}
    (code : CoordinatorCode p rate) : Fin 4 :=
  match code with
  | .inl _ => 0
  | .inr (.inl _) => 1
  | .inr (.inr (.inl _)) => 2
  | .inr (.inr (.inr _)) => 3

private theorem measurable_coordinatorCodeTag {p : Parameters} {rate : RateInput p} : Measurable
    (coordinatorCodeTag (p := p) (rate := rate)) := by
  let deep :
      (ReferenceActivePhysicalStep.Payload rate ×
        (ReferenceActivePhysicalStep.Ledger rate × Option (Fin p.T × Bool))) ⊕ Unit → Fin 4 :=
    Sum.elim (fun _ => (2 : Fin 4)) (fun _ => (3 : Fin 4))
  have hdeep : Measurable deep := Measurable.sumElim measurable_const measurable_const
  have hmiddle : Measurable (Sum.elim
      (fun _ : ReferenceActivePhysicalStep.Payload rate ×
        ReferenceActivePhysicalStepMeasurability.LiveDiscrete p => (1 : Fin 4))
      (fun z : (ReferenceActivePhysicalStep.Payload rate ×
        (ReferenceActivePhysicalStep.Ledger rate × Option (Fin p.T × Bool))) ⊕ Unit => deep z)) := by
    exact Measurable.sumElim measurable_const hdeep
  exact Measurable.sumElim measurable_const hmiddle

private def failureIsCollectionCode (failure : Option ReferenceActivePhysicalStep.CoordinatorFailure) : Bool :=
  match failure with
  | some (.collection _) => true
  | _ => false

private theorem measurable_failureIsCollectionCode :
    Measurable failureIsCollectionCode := by
  have hfailure : Measurable (fun failure :
      ReferenceActivePhysicalStep.CoordinatorFailure =>
        match failure with
        | .collection _ => true
        | _ => false) := by
    intro s hs
    exact MeasurableSet.of_discrete
  have hm := ReferenceCollectionOutcomeMeasurability.measurable_optionalElim
    false (fun failure : ReferenceActivePhysicalStep.CoordinatorFailure => match failure with
      | .collection _ => true
      | _ => false) hfailure
  have heq : ReferenceCollectionOutcomeMeasurability.optionalElim false
      (fun failure : ReferenceActivePhysicalStep.CoordinatorFailure => match failure with
        | .collection _ => true
        | _ => false) = failureIsCollectionCode := by
    funext failure
    cases failure with
    | none => rfl
    | some failure => cases failure <;> rfl
  exact heq ▸ hm

private def collectionDiagnosticCodeTag
    (tag : Fin 4) (failure : Option ReferenceActivePhysicalStep.CoordinatorFailure) : Bool :=
  tag = 2 ∨ (tag = 3 ∧ failureIsCollectionCode failure)

private theorem measurable_collectionDiagnosticCodeTag :
    Measurable (fun z : Fin 4 × Option ReferenceActivePhysicalStep.CoordinatorFailure =>
      collectionDiagnosticCodeTag z.1 z.2) := by
  have htag : Measurable (fun z : Fin 4 × Option ReferenceActivePhysicalStep.CoordinatorFailure =>
      decide (z.1 = 2)) :=
    (measurable_of_finite (fun z : Fin 4 => decide (z = 2))).comp measurable_fst
  have htail : Measurable (fun z : Fin 4 × Option ReferenceActivePhysicalStep.CoordinatorFailure =>
      decide (z.1 = 3) && failureIsCollectionCode z.2) := by
    have hcoord : Measurable (fun z : Fin 4 × Option ReferenceActivePhysicalStep.CoordinatorFailure =>
        (z.1, failureIsCollectionCode z.2)) :=
      measurable_fst.prodMk (measurable_failureIsCollectionCode.comp measurable_snd)
    exact (measurable_of_finite
      (fun z : Fin 4 × Bool => decide (z.1 = 3) && z.2)).comp hcoord
  have hbool : Measurable (fun z : Bool × Bool => z.1 || z.2) := measurable_of_finite _
  exact hbool.comp (htag.prodMk htail)

private def roundCodeCutoff {p : Parameters} {rate : RateInput p}
    (code : ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate)) : Bool :=
  decide (coordinatorCodeTag code.2.1.1 = 1) &&
    collectionDiagnosticCodeTag
      (coordinatorCodeTag (code.2.2.1.2.2.2.2).1)
      (code.2.2.1.2.2.2.2).2.2.1

private theorem measurable_roundCodeCutoff {p : Parameters} {rate : RateInput p} :
    Measurable (roundCodeCutoff (p := p) (rate := rate)) := by
  have hstate : Measurable (fun code :
      ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate) => code.2.1) :=
    measurable_fst.comp (measurable_snd.comp measurable_id)
  have hleft : Measurable (fun code :
      ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate) =>
        coordinatorCodeTag code.2.1.1) :=
    measurable_coordinatorCodeTag.comp (measurable_fst.comp hstate)
  have hwhole : Measurable (fun code :
      ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate) => code.2.2) :=
    measurable_snd.comp (measurable_snd.comp measurable_id)
  have hphysical : Measurable (fun code :
      ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate) => code.2.2.1) :=
    measurable_fst.comp hwhole
  have hdiag : Measurable (fun code :
      ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate) =>
        (coordinatorCodeTag (code.2.2.1.2.2.2.2).1,
          (code.2.2.1.2.2.2.2).2.2.1)) := by
    have htail : Measurable (fun code :
        ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate) =>
          code.2.2.1.2.2.2.2) := by
      exact measurable_snd.comp (measurable_snd.comp (measurable_snd.comp
        (measurable_snd.comp hphysical)))
    exact (measurable_coordinatorCodeTag.comp (measurable_fst.comp htail)).prodMk
      (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp htail)))
  have hbits : Measurable (fun code :
      ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate) =>
        (coordinatorCodeTag code.2.1.1,
          (coordinatorCodeTag code.2.2.1.2.2.2.2.1,
            code.2.2.1.2.2.2.2.2.2.1))) := hleft.prodMk hdiag
  have htag : Measurable (fun z : Fin 4 => decide (z = 1)) := measurable_of_finite _
  have htest : Measurable (fun z : Fin 4 × (Fin 4 ×
      Option ReferenceActivePhysicalStep.CoordinatorFailure) =>
      decide (z.1 = 1) && collectionDiagnosticCodeTag z.2.1 z.2.2) := by
    have hdiagTest : Measurable (fun z : Fin 4 × Option ReferenceActivePhysicalStep.CoordinatorFailure =>
        collectionDiagnosticCodeTag z.1 z.2) := measurable_collectionDiagnosticCodeTag
    exact (measurable_of_finite (fun z : Bool × Bool => z.1 && z.2)).comp
      ((htag.comp measurable_fst).prodMk (hdiagTest.comp measurable_snd))
  exact htest.comp hbits

private theorem coordinatorCodeTag_encodeCoordinator {p : Parameters} {rate : RateInput p}
    (config : ReferenceActivePhysicalStep.CoordinatorConfiguration p rate) :
    coordinatorCodeTag
        (ReferenceActivePhysicalStepMeasurability.encodeCoordinator config) =
      match config with
      | .first => 0
      | .live _ _ _ => 1
      | .collection _ _ _ => 2
      | .dagger => 3 := by
  cases config <;> rfl

private theorem collectionDiagnosticCodeTag_encode {p : Parameters} {rate : RateInput p}
    (diagnostic : ReferenceActivePhysicalStep.CoordinatorObservation p rate) :
    collectionDiagnosticCodeTag
        (coordinatorCodeTag
          (ReferenceActivePhysicalStepMeasurability.encodeCoordinator
            diagnostic.configuration)) diagnostic.failure =
      collectionObservation diagnostic := by
  cases diagnostic with
  | mk config bank failure recording up =>
      cases config <;> cases failure with
      | none => rfl
      | some failure => cases failure <;> rfl

private theorem roundCodeCutoff_eq_evidence (record : Record p rate) :
    roundCodeCutoff (ReferenceActiveHorizonMeasurability.roundRecordCode record) =
      evidenceCutoff record.evidence := by
  have hobs : (ReferenceActivePhysicalStep.prepare record.input).observeCoordinator =
      record.coordinatorDiagnostics := by
    change (ReferenceActivePhysicalStep.prepare record.input).observeCoordinator =
      record.output.coordinator
    exact (congrArg
      (fun output : ReferenceActivePhysicalStep.RoundOutput record.input => output.coordinator)
      record.output_eq).symm
  have hstateTag :
      coordinatorCodeTag
          (ReferenceActiveHorizonMeasurability.roundRecordCode record).2.1.1 =
        (match record.input.state.coordinator with
        | .first => (0 : Fin 4)
        | .live _ _ _ => 1
        | .collection _ _ _ => 2
        | .dagger => 3) := by
    change coordinatorCodeTag
      (ReferenceActivePhysicalStepMeasurability.encodeCoordinator
        record.input.state.coordinator) = _
    exact coordinatorCodeTag_encodeCoordinator _
  have hdiagTag :
      collectionDiagnosticCodeTag
        (coordinatorCodeTag
          ((ReferenceActiveHorizonMeasurability.roundRecordCode record).2.2.1.2.2.2.2).1)
        ((ReferenceActiveHorizonMeasurability.roundRecordCode record).2.2.1.2.2.2.2).2.2.1 =
        collectionObservation record.coordinatorDiagnostics := by
    change collectionDiagnosticCodeTag
      (coordinatorCodeTag
        (ReferenceActivePhysicalStepMeasurability.encodeCoordinator
          (ReferenceActivePhysicalStep.prepare record.input).observeCoordinator.configuration))
      (ReferenceActivePhysicalStep.prepare record.input).observeCoordinator.failure = _
    rw [hobs]
    exact collectionDiagnosticCodeTag_encode _
  rw [roundCodeCutoff, hstateTag, hdiagTag]
  cases hcoord : record.input.state.coordinator <;>
    simp [evidenceCutoff, ReferenceActivePhysicalHorizon.RoundRecord.evidence, hcoord]

private theorem roundCodeCutoff_eq_cutoffChosen (record : Record p rate) :
    roundCodeCutoff (ReferenceActiveHorizonMeasurability.roundRecordCode record) =
      ReferenceCollectionPhaseHistory.cutoffChosen record.input := by
  rw [roundCodeCutoff_eq_evidence, cutoffChosen_eq_evidence]

private theorem firstLive_index_full_iff
    (records : List (Record p rate)) (n : ℕ) (hlen : records.length = n + 1) :
    n < (ReferenceFirstLiveConfirmationHistory.firstLiveWindow records).length ↔
      ∀ record ∈ records,
        ReferenceCollectionPhaseHistory.cutoffChosen record.input = false := by
  let pred := fun record : Record p rate =>
    !ReferenceCollectionPhaseHistory.cutoffChosen record.input
  change n < (records.takeWhile pred).length ↔ ∀ record ∈ records,
    ReferenceCollectionPhaseHistory.cutoffChosen record.input = false
  constructor
  · intro hn record hrecord
    have hprefix := List.takeWhile_prefix (p := pred) (l := records)
    have hlenWindow : (records.takeWhile pred).length = records.length := by
      apply le_antisymm hprefix.length_le
      omega
    have hrecords : records.takeWhile pred = records := hprefix.eq_of_length hlenWindow
    rw [← hrecords] at hrecord
    have hpred := List.mem_takeWhile_imp hrecord
    simpa [pred] using hpred
  · intro hall
    have hself : records.takeWhile pred = records :=
      (List.takeWhile_eq_self_iff).2 (fun record hrecord => by
        simpa [pred] using hall record hrecord)
    simp [hself, hlen]

private def liveRoundCodeTag
    (tag : Unit ⊕ ReferenceActiveHorizonMeasurability.RoundRecordCode
      (p := p) (rate := rate)) : Bool :=
  match tag with
  | .inl _ => false
  | .inr code => !roundCodeCutoff code

private theorem measurable_liveRoundCodeTag :
    Measurable (liveRoundCodeTag (p := p) (rate := rate)) := by
  exact Measurable.sumElim measurable_const
    ((measurable_of_finite fun b : Bool => !b).comp measurable_roundCodeCutoff)

private def observationNoCutoff
    (coordinates : ℕ → Unit ⊕ ReferenceActiveHorizonMeasurability.RoundRecordCode
      (p := p) (rate := rate)) (n : ℕ) : Bool :=
  decide (∀ k : Fin (n + 1), liveRoundCodeTag (coordinates k.val) = true)

private theorem measurable_observationNoCutoff (n : ℕ) :
    Measurable (fun coordinates : ℕ → Unit ⊕
      ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate) =>
        observationNoCutoff coordinates n) := by
  have hcoords : Measurable (fun coordinates : ℕ → Unit ⊕
      ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate) =>
        fun k : Fin (n + 1) => liveRoundCodeTag (coordinates k.val)) := by
    apply measurable_pi_iff.mpr
    intro k
    exact measurable_liveRoundCodeTag.comp (measurable_pi_apply k.val)
  exact (measurable_of_finite (fun values : Fin (n + 1) → Bool =>
    decide (∀ k, values k = true))).comp hcoords

private theorem observationNoCutoff_records_iff
    (coordinates : ℕ → Unit ⊕ ReferenceActiveHorizonMeasurability.RoundRecordCode
      (p := p) (rate := rate)) (records : List (Record p rate)) (n : ℕ)
    (hlen : records.length = n + 1)
    (hcoordinates : ∀ k : Fin (n + 1),
      coordinates k.val = Sum.inr
        (ReferenceActiveHorizonMeasurability.roundRecordCode
          (records.get ⟨k.val, by rw [hlen]; exact k.isLt⟩))) :
    observationNoCutoff coordinates n = true ↔
      ∀ record ∈ records,
        ReferenceCollectionPhaseHistory.cutoffChosen record.input = false := by
  rw [observationNoCutoff, decide_eq_true_eq]
  constructor
  · intro hall record hrecord
    obtain ⟨j, hj⟩ := List.mem_iff_get.mp hrecord
    let k : Fin (n + 1) := ⟨j.val, by omega⟩
    have hget : records.get ⟨k.val, by omega⟩ = record := by
      simpa [k] using hj
    have h := hall k
    rw [hcoordinates k] at h
    have h' : ReferenceCollectionPhaseHistory.cutoffChosen
        (records.get ⟨k.val, by omega⟩).input = false := by
      simpa [liveRoundCodeTag, roundCodeCutoff_eq_cutoffChosen] using h
    rw [hget] at h'
    exact h'
  · intro hall k
    have hmem : records.get ⟨k.val, by omega⟩ ∈ records :=
      List.get_mem records ⟨k.val, by omega⟩
    have h := hall _ hmem
    rw [hcoordinates k]
    simpa [liveRoundCodeTag, roundCodeCutoff_eq_cutoffChosen] using h

private def actualBranchCode
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p) (i : Fin (p.m - 1))
    (x : RetainedLaunchStart (p := p) (rate := rate)
      rewards C_star C_h q t s hs control0) : Bool :=
  let observation := retainedRunObservation rewards C_star C_h q t s hs control0 x
  let coordinates := ReferenceActiveHorizonMeasurability.listObservationCoordinates observation.2
  observationNoCutoff coordinates.2 (t.val - s) &&
    selectedEmptyPendingCode (retainedCurrentCode rewards C_star C_h q t s hs control0 x)
      (B rate rewards C_star C_h q t s hs control0 x) i

private theorem measurable_actualBranchCode
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p) (i : Fin (p.m - 1)) :
    Measurable (actualBranchCode (rate := rate) rewards C_star C_h q t s hs control0 i) := by
  have hobs := measurable_retainedRunObservation (rate := rate)
    rewards C_star C_h q t s hs control0
  let coordinates := fun x : RetainedLaunchStart (p := p) (rate := rate)
      rewards C_star C_h q t s hs control0 =>
    ReferenceActiveHorizonMeasurability.listObservationCoordinates
      (retainedRunObservation rewards C_star C_h q t s hs control0 x).2
  have hcoordinates : Measurable coordinates :=
    ReferenceActiveHorizonMeasurability.measurable_listObservationCoordinates.comp
      (measurable_snd.comp hobs)
  have hprefix : Measurable (fun x : RetainedLaunchStart (p := p) (rate := rate)
      rewards C_star C_h q t s hs control0 => observationNoCutoff
        (coordinates x).2 (t.val - s)) :=
    (measurable_observationNoCutoff (t.val - s)).comp
      (measurable_snd.comp hcoordinates)
  have hcode := measurable_retainedCurrentCode (rate := rate)
    rewards C_star C_h q t s hs control0
  have hbeta := ReferenceRetainedBoundaryMeasurability.measurable_retainedIncomingBoundary
    rate rewards C_star C_h q t s hs control0
  have hselected := (measurable_selectedEmptyPendingCode (p := p) (rate := rate) i).comp
    (hcode.prodMk hbeta)
  have hpair : Measurable (fun x : RetainedLaunchStart (p := p) (rate := rate)
      rewards C_star C_h q t s hs control0 =>
      (observationNoCutoff (coordinates x).2 (t.val - s),
        selectedEmptyPendingCode
          (retainedCurrentCode rewards C_star C_h q t s hs control0 x)
          (B rate rewards C_star C_h q t s hs control0 x) i)) :=
    hprefix.prodMk hselected
  exact (measurable_of_finite (fun b : Bool × Bool => b.1 && b.2)).comp hpair

private theorem actualBranchCode_mem_iff
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p) (i : Fin (p.m - 1))
    (x : RetainedLaunchStart (p := p) (rate := rate)
      rewards C_star C_h q t s hs control0) :
    actualBranchCode (rate := rate) rewards C_star C_h q t s hs control0 i x = true ↔
      x ∈ selectedEmptyPendingRemainder (rate := rate)
        rewards C_star C_h q t s hs control0 i := by
  let n := t.val - s
  let run := ReferenceFirstLiveReleaseControlTransport.retainedRun
    rewards C_star C_h q t s hs control0 x control0
  let records := run.records
  let obs := retainedRunObservation rewards C_star C_h q t s hs control0 x
  let coordinates := ReferenceActiveHorizonMeasurability.listObservationCoordinates obs.2
  have hlen : records.length = n + 1 := by
    simpa [run, n] using retainedRun_records_length
      (rate := rate) rewards C_star C_h q t s hs control0 x
  have hcoordinates : ∀ k : Fin (n + 1), coordinates.2 k.val = Sum.inr
      (ReferenceActiveHorizonMeasurability.roundRecordCode
        (records.get ⟨k.val, by rw [hlen]; exact k.isLt⟩)) := by
    intro k
    change ReferenceActiveHorizonMeasurability.listObservationAt obs.2 k.val = _
    simpa [run, obs] using retainedRunObservation_at
      (rate := rate) rewards C_star C_h q t s hs control0 x k
  have hcut : observationNoCutoff coordinates.2 n = true ↔
      ∀ record ∈ records,
        ReferenceCollectionPhaseHistory.cutoffChosen record.input = false :=
    observationNoCutoff_records_iff coordinates.2 records n hlen hcoordinates
  have hcurrent : retainedCurrentCode rewards C_star C_h q t s hs control0 x =
      Sum.inr (ReferenceActiveHorizonMeasurability.roundRecordCode
        (records.get ⟨n, by omega⟩)) := by
    change ReferenceActiveHorizonMeasurability.listObservationAt obs.2 n = _
    simpa [obs, run, n] using retainedRunObservation_at
      (rate := rate) rewards C_star C_h q t s hs control0 x ⟨n, by omega⟩
  change (observationNoCutoff coordinates.2 n &&
    selectedEmptyPendingCode
      (retainedCurrentCode rewards C_star C_h q t s hs control0 x)
      (B rate rewards C_star C_h q t s hs control0 x) i = true) ↔ _
  rw [Bool.and_eq_true]
  constructor
  · rintro ⟨hprefix, hselection⟩
    have hnoCut := hcut.mp hprefix
    have hwindowEq : T rewards C_star C_h q t s hs control0 x control0 = records := by
      rw [ReferenceFirstLiveReleaseControlTransport.retainedWindow_eq]
      exact (List.takeWhile_eq_self_iff).2 (fun record hrecord => by
        simpa using hnoCut record hrecord)
    have hwindow : n < (T rewards C_star C_h q t s hs control0 x control0).length := by
      rw [hwindowEq]
      simp [hlen, n]
    have hrecCodeEq : ReferenceActiveHorizonMeasurability.roundRecordCode
        (records.get ⟨n, by omega⟩) =
      ReferenceActiveHorizonMeasurability.roundRecordCode
        ((T rewards C_star C_h q t s hs control0 x control0).get ⟨n, hwindow⟩) :=
      congrArg ReferenceActiveHorizonMeasurability.roundRecordCode
        (List.getElem_of_eq hwindowEq hwindow).symm
    have hcurrentWindow : retainedCurrentCode rewards C_star C_h q t s hs control0 x =
        Sum.inr (ReferenceActiveHorizonMeasurability.roundRecordCode
          ((T rewards C_star C_h q t s hs control0 x control0).get ⟨n, hwindow⟩)) := by
      rw [hcurrent]
      exact congrArg Sum.inr hrecCodeEq
    have hselectionWindow := hselection
    rw [hcurrentWindow] at hselectionWindow
    obtain ⟨selected0, hselected, hempty, hi⟩ :=
      (selectedEmptyPendingCode_roundRecord_iff
        ((T rewards C_star C_h q t s hs control0 x control0).get ⟨n, hwindow⟩)
        (B rate rewards C_star C_h q t s hs control0 x) i).mp hselectionWindow
    exact ⟨hwindow, selected0, hselected, hempty, hi⟩
  · rintro ⟨hn, selected0, hselected, hempty, hi⟩
    have hn' : n < (ReferenceFirstLiveConfirmationHistory.firstLiveWindow records).length := by
      simpa [ReferenceFirstLiveReleaseControlTransport.retainedWindow_eq, run, records, n] using hn
    have hnoCut : ∀ record ∈ records,
        ReferenceCollectionPhaseHistory.cutoffChosen record.input = false :=
      (firstLive_index_full_iff records n hlen).mp hn'
    have hwindowEq : T rewards C_star C_h q t s hs control0 x control0 = records := by
      rw [ReferenceFirstLiveReleaseControlTransport.retainedWindow_eq]
      exact (List.takeWhile_eq_self_iff).2 (fun record hrecord => by
        simpa using hnoCut record hrecord)
    have hprefix := hcut.mpr hnoCut
    have hrecCodeEq : ReferenceActiveHorizonMeasurability.roundRecordCode
        (records.get ⟨n, by omega⟩) =
      ReferenceActiveHorizonMeasurability.roundRecordCode
        ((T rewards C_star C_h q t s hs control0 x control0).get ⟨n, hn⟩) :=
      congrArg ReferenceActiveHorizonMeasurability.roundRecordCode
        (List.getElem_of_eq hwindowEq hn).symm
    have hcurrentWindow : retainedCurrentCode rewards C_star C_h q t s hs control0 x =
        Sum.inr (ReferenceActiveHorizonMeasurability.roundRecordCode
          ((T rewards C_star C_h q t s hs control0 x control0).get ⟨n, hn⟩)) := by
      rw [hcurrent]
      exact congrArg Sum.inr hrecCodeEq
    have hselection := (selectedEmptyPendingCode_roundRecord_iff
      ((T rewards C_star C_h q t s hs control0 x control0).get ⟨n, hn⟩)
      (B rate rewards C_star C_h q t s hs control0 x) i).mpr
      ⟨selected0, hselected, hempty, hi⟩
    rw [hcurrentWindow]
    exact ⟨hprefix, hselection⟩

/-- The computed selected-empty incoming-release branch is Borel in the
retained boundary's existing inherited measurable space. -/
theorem measurableSet_selectedEmptyPendingRemainder
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p) (i : Fin (p.m - 1)) :
    MeasurableSet (selectedEmptyPendingRemainder (rate := rate)
      rewards C_star C_h q t s hs control0 i) := by
  have hbranch := measurable_actualBranchCode (rate := rate)
    rewards C_star C_h q t s hs control0 i
  have hset : MeasurableSet {x : RetainedLaunchStart (p := p) (rate := rate)
      rewards C_star C_h q t s hs control0 |
        actualBranchCode (rate := rate) rewards C_star C_h q t s hs control0 i x = true} :=
    (measurableSet_singleton true).preimage hbranch
  convert hset using 1
  ext x
  exact (actualBranchCode_mem_iff (rate := rate)
    rewards C_star C_h q t s hs control0 i x).symm

/-- The branch's selected witness is the unique value of the actual optional
selection readout at the baseline physical record. -/
theorem selectedEmptyPendingRemainder_selection_unique
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p) (i : Fin (p.m - 1))
    (x : RetainedLaunchStart (p := p) (rate := rate)
      rewards C_star C_h q t s hs control0)
    (hn₁ hn₂ : t.val - s < (T rewards C_star C_h q t s hs control0 x control0).length)
    (selected₁ : Selection (p := p) (rate := rate)
      ((T rewards C_star C_h q t s hs control0 x control0).get ⟨t.val - s, hn₁⟩).input)
    (selected₂ : Selection (p := p) (rate := rate)
      ((T rewards C_star C_h q t s hs control0 x control0).get ⟨t.val - s, hn₂⟩).input)
    (hselected₁ : ((T rewards C_star C_h q t s hs control0 x control0).get
      ⟨t.val - s, hn₁⟩).output.preparation.coordinator.selection = some selected₁)
    (hselected₂ : ((T rewards C_star C_h q t s hs control0 x control0).get
      ⟨t.val - s, hn₂⟩).output.preparation.coordinator.selection = some selected₂) :
    selected₁ = selected₂ := by
  have hindex : (⟨t.val - s, hn₁⟩ : Fin
      (T rewards C_star C_h q t s hs control0 x control0).length) =
      ⟨t.val - s, hn₂⟩ := Fin.ext rfl
  cases hindex
  exact Option.some.inj (hselected₁.symm.trans hselected₂)

/-- On every point of the computed branch, M's whole-control section masses
are the literal UP and DATA formulas. The baseline record and optional
selection witnesses are outputs of branch membership; M supplies validity. -/
theorem selectedEmptyPendingRemainder_control_section_masses
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p) (i : Fin (p.m - 1))
    (x : RetainedLaunchStart (p := p) (rate := rate)
      rewards C_star C_h q t s hs control0)
    (hx : x ∈ selectedEmptyPendingRemainder (rate := rate)
      rewards C_star C_h q t s hs control0 i) :
    ∃ hn : t.val - s < (T rewards C_star C_h q t s hs control0 x control0).length,
    ∃ selected0 : Selection (p := p) (rate := rate)
      ((T rewards C_star C_h q t s hs control0 x control0).get ⟨t.val - s, hn⟩).input,
    ∃ hselected : ((T rewards C_star C_h q t s hs control0 x control0).get
      ⟨t.val - s, hn⟩).output.preparation.coordinator.selection = some selected0,
    ∃ hempty : selected0.view.pendingAtChoice = ∅,
    ∃ hi : i ∈ ReferencePhysicalReleaseQuota.pendingAtStart selected0.view.payload
      (B rate rewards C_star C_h q t s hs control0 x).time
      (B rate rewards C_star C_h q t s hs control0 x).state,
    ∃ hvalid : CoordinatorLocalArmChoice.ChoiceInputsValid selected0.view.payload
      selected0.view.cutoff
      (T rewards C_star C_h q t s hs control0 x control0)[t.val - s].input.time
      selected0.view.complementWeights,
      ContinuousLearningRows.timeControlLaw p
          (ReferenceFirstLiveReleaseSliceMass.retainedUpFlagEvent
            rewards C_star C_h q t s hs control0 x hn selected0 i) =
        ENNReal.ofReal
          (ReleaseRoundKernel.chi
              (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t)
              selected0.view.payload.assignment.auxiliary *
            (1 - CanonicalFastSampling.qGamma p rate.eta rate.eta.property
              selected0.view.payload.eta_le_source_cap selected0.view.payload.anchor
              (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights selected0)
              selected0.view.payload.anchor_pos
              (fun a => (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights_bounds
                selected0 hvalid a).1)
              (fun a => (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights_bounds
                selected0 hvalid a).2.1)
              (fun a => (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights_bounds
                selected0 hvalid a).2.2)
              selected0.view.payload.slowSet
              (ReleaseRoundKernel.auxiliaryFastArm selected0.view.payload.assignment
                selected0.view.payload.slowSet selected0.view.payload.assignment_image.symm)) /
            (4 * (p.m - 1 : ℝ) * (p.K : ℝ))) ∧
      ENNReal.ofReal
          (ReleaseRoundKernel.chi
            (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t)
            selected0.view.payload.assignment.auxiliary /
            (12 * (p.m - 1 : ℝ) * (p.K : ℝ))) ≤
        ContinuousLearningRows.timeControlLaw p
          (ReferenceFirstLiveReleaseSliceMass.retainedUpFlagEvent
            rewards C_star C_h q t s hs control0 x hn selected0 i) ∧
      ContinuousLearningRows.timeControlLaw p
          (ReferenceFirstLiveReleaseSliceMass.retainedDataFlagEvent
            rewards C_star C_h q t s hs control0 x hn selected0 i) =
        ENNReal.ofReal
          (ReleaseRoundKernel.chi
            (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t)
            (selected0.view.payload.assignment.assigned i) / (2 * (p.K : ℝ))) := by
  obtain ⟨hn, selected0, hselected, hempty, hi⟩ :=
    (mem_selectedEmptyPendingRemainder_iff (rate := rate)
      rewards C_star C_h q t s hs control0 i x).mp hx
  obtain ⟨hvalid, hup⟩ := ReferenceFirstLiveReleaseSliceMass.retained_up_release_mass
    (rate := rate) rewards C_star C_h q t s hs control0 x hn selected0 hselected hempty i hi
  have hlower := ReferenceFirstLiveReleaseSliceMass.retained_up_release_mass_lower_bound
    (rate := rate) rewards C_star C_h q t s hs control0 x hn selected0 hselected hempty i hi
  have hdata := ReferenceFirstLiveReleaseSliceMass.retained_data_release_mass
    (rate := rate) rewards C_star C_h q t s hs control0 x hn selected0 hselected hempty i hi
  refine ⟨hn, selected0, hselected, hempty, hi, hvalid, ?_, hlower, hdata⟩
  simpa [ReferenceFirstLiveReleaseSliceMass.upReleaseMassFormula] using hup

end Bandits.Support.ReferenceFirstLiveReleaseSourceCylinder

end
