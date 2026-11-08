/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteLiveChoiceDomains
public import Bandits.Support.ReferenceCompleteSelectedLiveCoordinatorServiceFinish

/-!
# Complete-source cutoff last-service bounds

The assigned-arm part of the actual collection cutoff-register bound follows
from the checked complete-source assigned-score span. The complementary
registers require a separate actual live-service and collection-frame argument.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceCompletePhysicalHistory
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ActualInitializationPhysicalStep
open Bandits.Support.CoordinatorCollectionLedger

namespace Bandits.Support.ReferenceCompleteCollectionCutoffLastServiceBounds

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

private theorem selected_live_output_last_service_bound
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (v : ReferenceActivePhysicalStep.Selection
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val]'k.isLt).input)
    (hselected : ((ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val]'k.isLt).output.preparation.coordinator.selection =
        some v)
    (hlive : CoordinatorLocalArmChoice.assignmentIsLive v.view.payload v.view.cutoff
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val]'k.isLt).input.time)
    (next : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (nextOwned : CoordinatorLiveServiceFinish.OwnedRegisters next)
    (nextBase : Fin (p.m - 1) → ℕ)
    (hnext : ((ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val]'k.isLt).output.next.coordinator =
        .live next nextOwned nextBase) :
    ∀ j : CanonicalFastSampling.FastArm next.payload.slowSet,
      nextOwned.previousService j ≤ next.complementScores j ∧
        nextOwned.previousService j ≤ 4 * rate.n := by
  let record := (ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h)[k.val]'k.isLt
  have hresult :=
    ReferenceCompleteSelectedLiveCoordinatorServiceFinish.complete_selected_live_coordinator_service_finish
      rewards C_star C_h source k v hselected hlive
  dsimp only at hresult
  rcases hresult with ⟨r, q, base, started, _hbranch, valid, o, serviced,
    pending, finished, hdata⟩
  rcases hdata with ⟨_, _, _, _, _, _, _, _, _, _, _, hserviceEq, _,
    hscoreEq, hpreviousEq, _, _, _, hpost, _, hnextCoordinator, _⟩
  have hconfiguration :
      ReferenceActivePhysicalStep.CoordinatorConfiguration.live
          { payload := r.payload
            priorClock := finished.clock
            pendingAtChoice := finished.pending
            time := record.input.time
            gridBoundary := finished.clock.g
            complementScores := serviced.score }
          { queue := serviced.queue
            previousService := serviced.previousService } base =
      ReferenceActivePhysicalStep.CoordinatorConfiguration.live
        next nextOwned nextBase := by
    calc
      ReferenceActivePhysicalStep.CoordinatorConfiguration.live
          { payload := r.payload
            priorClock := finished.clock
            pendingAtChoice := finished.pending
            time := record.input.time
            gridBoundary := finished.clock.g
            complementScores := serviced.score }
          { queue := serviced.queue
            previousService := serviced.previousService } base =
          (ReferenceActivePhysicalStep.livePostChoice record.output.preparation
            r q base started).configuration := by
              rw [hpost]
      _ = record.output.next.coordinator := hnextCoordinator.symm
      _ = ReferenceActivePhysicalStep.CoordinatorConfiguration.live
        next nextOwned nextBase := hnext
  have hfields := ReferenceActivePhysicalStep.CoordinatorConfiguration.live.inj
    hconfiguration
  rcases hfields with ⟨hregisters, howned, _hbase⟩
  cases hregisters
  have hownedEq := eq_of_heq howned
  subst nextOwned
  intro j
  have hscore := hscoreEq j
  have hprevious := hpreviousEq j
  have hserviceCap : serviced.service j ≤ 4 * rate.n := by
    rw [hserviceEq j]
    have hcap := CappedService.service_le_capacity
      (4 * r.payload.n) (q.queue j) (serviced.arrival j)
    simpa only [ReferenceActivePhysicalStep.payload_n_eq r.payload] using hcap
  constructor
  · change serviced.previousService j ≤ serviced.score j
    rw [hprevious, hscore]
    exact Nat.le_add_left _ _
  · change serviced.previousService j ≤ 4 * rate.n
    rw [hprevious]
    exact hserviceCap

private theorem live_post_choice_last_service_bound
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (next : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (nextOwned : CoordinatorLiveServiceFinish.OwnedRegisters next)
    (nextBase : Fin (p.m - 1) → ℕ)
    (hnext : (ReferenceActivePhysicalStep.livePostChoice prepared r q base started).configuration =
      .live next nextOwned nextBase) :
    ∀ j : CanonicalFastSampling.FastArm next.payload.slowSet,
      nextOwned.previousService j ≤ next.complementScores j ∧
        nextOwned.previousService j ≤ 4 * rate.n := by
  unfold ReferenceActivePhysicalStep.livePostChoice at hnext
  cases hrecord : CoordinatorRecorderComplementBridge.run
      (ReferenceActivePhysicalStep.liveRecordingInput prepared r started) with
  | none => simp [hrecord, ReferenceActivePhysicalStep.coordinatorFailure] at hnext
  | some recording =>
      cases hservice : CoordinatorLiveServiceFinish.servicePass r q recording with
      | error reason =>
          simp [hrecord, hservice, ReferenceActivePhysicalStep.coordinatorFailure] at hnext
      | ok serviced =>
          cases hconfirmation : CoordinatorLocalArmChoice.confirmationUpdate r.payload
              started.pending
              (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
              x.time x.row prepared.coordinatorObservation with
          | none =>
              simp [hrecord, hservice, hconfirmation,
                ReferenceActivePhysicalStep.coordinatorFailure] at hnext
          | some pending =>
              cases hfinish : CoordinatorPhaseClock.finishRound p rate.eta.val x.time
                  started.clock pending x.row with
              | error reason =>
                  simp [hrecord, hservice, hconfirmation, hfinish,
                    ReferenceActivePhysicalStep.coordinatorFailure] at hnext
              | ok finished =>
                  simp only [hrecord, hservice, hconfirmation, hfinish] at hnext
                  have hregisters : next =
                      { payload := r.payload
                        priorClock := finished.clock
                        pendingAtChoice := finished.pending
                        time := x.time
                        gridBoundary := finished.clock.g
                        complementScores := serviced.score } := by
                    cases hnext
                    rfl
                  cases hregisters
                  have howned : nextOwned =
                      { queue := serviced.queue
                        previousService := serviced.previousService } := by
                    cases hnext
                    rfl
                  cases howned
                  intro j
                  constructor
                  · change serviced.previousService j ≤ serviced.score j
                    rw [serviced.previousService_eq j, serviced.score_eq j]
                    exact Nat.le_add_left _ _
                  · change serviced.previousService j ≤ 4 * rate.n
                    rw [serviced.previousService_eq j, serviced.service_eq j]
                    have hcap := CappedService.service_le_capacity
                      (4 * r.payload.n) (q.queue j) (serviced.arrival j)
                    have hn : r.payload.n = rate.n := by
                      apply Nat.cast_injective (R := ℝ)
                      rw [ReferenceActivePhysicalStep.payload_n_eq r.payload,
                        rate.n_scale]
                    simpa only [hn] using hcap

private def liveInputLastServiceBound
    (configuration : ReferenceActivePhysicalStep.CoordinatorConfiguration p rate) : Prop :=
  match configuration with
  | .live r q _ => ∀ j : CanonicalFastSampling.FastArm r.payload.slowSet,
      q.previousService j ≤ r.complementScores j ∧ q.previousService j ≤ 4 * rate.n
  | _ => True

private theorem collection_post_choice_not_live
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ)
    (h : (ReferenceActivePhysicalStep.collectionPostChoice prepared payload ledger
      started weights).configuration = .live r q base) : False := by
  unfold ReferenceActivePhysicalStep.collectionPostChoice at h
  cases hrecord : CoordinatorRecorderComplementBridge.run
      (ReferenceActivePhysicalStep.collectionRecordingInput prepared payload started weights) with
  | none => simp [hrecord, ReferenceActivePhysicalStep.coordinatorFailure] at h
  | some recording =>
      cases hstart : CoordinatorCollectionLedger.startRound ledger (x.time.val + 1)
          (ReferenceActivePhysicalStep.collectionEnabled ledger x.time)
          (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) with
      | invalid => simp [hrecord, hstart, ReferenceActivePhysicalStep.coordinatorFailure] at h
      | rejected bad => simp [hrecord, hstart, ReferenceActivePhysicalStep.coordinatorFailure] at h
      | success startedLedger =>
          unfold ReferenceActivePhysicalStep.collectionFinish at h
          cases hreceive : (ReferenceActivePhysicalStep.receiveUp prepared startedLedger).result with
          | invalid => simp [hrecord, hstart, hreceive,
              ReferenceActivePhysicalStep.coordinatorFailure] at h
          | success pair | rejected pair =>
              rcases pair with ⟨decoded, bank⟩
              cases hfinish : CoordinatorCollectionLedger.finishRound decoded with
              | invalid => simp [hrecord, hstart, hreceive, hfinish,
                  ReferenceActivePhysicalStep.coordinatorFailure] at h
              | rejected bad => simp [hrecord, hstart, hreceive, hfinish,
                  ReferenceActivePhysicalStep.coordinatorFailure] at h
              | success finished =>
                  cases hclock : CoordinatorPhaseClock.finishRound p rate.eta.val x.time
                      started.clock finished.pending x.row with
                  | error reason => simp [hrecord, hstart, hreceive, hfinish, hclock,
                      ReferenceActivePhysicalStep.coordinatorFailure] at h
                  | ok clockFinished =>
                      simp [hrecord, hstart, hreceive, hfinish, hclock] at h

private theorem live_post_choice_bound
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ)
    (started : CoordinatorPhaseClock.StartRoundResult p) :
    liveInputLastServiceBound
      (ReferenceActivePhysicalStep.livePostChoice prepared r q base started).configuration := by
  classical
  cases h : (ReferenceActivePhysicalStep.livePostChoice prepared r q base started).configuration with
  | first => trivial
  | collection payload ledger saved => trivial
  | dagger => trivial
  | live next nextOwned nextBase =>
      exact live_post_choice_last_service_bound x prepared r q base started
        next nextOwned nextBase h

private theorem collection_post_choice_bound
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ) :
    liveInputLastServiceBound
      (ReferenceActivePhysicalStep.collectionPostChoice prepared payload ledger started weights).configuration := by
  cases h : (ReferenceActivePhysicalStep.collectionPostChoice prepared payload ledger started weights).configuration with
  | first => trivial
  | collection payload ledger saved => trivial
  | dagger => trivial
  | live r q base => exact False.elim (collection_post_choice_not_live
      x prepared payload ledger started weights r q base h)

private theorem round_live_input_last_service_bound
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (_hin : liveInputLastServiceBound
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val].input.state.coordinator)) :
    liveInputLastServiceBound
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val].output.next.coordinator) := by
  classical
  let record := (ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h)[k.val]
  have hprep : record.output.preparation = ReferenceActivePhysicalStep.prepare record.input := by
    rw [record.output_eq]
    rfl
  have hout : record.output.next.coordinator =
      record.output.preparation.observeCoordinator.configuration := by
    rw [record.output_eq]
    rfl
  rw [hout]
  by_cases hselected : record.output.preparation.coordinator.selection = none
  · simp only [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
      dite_eq_left hselected]
    cases record.output.preparation.coordinator <;> trivial
  · simp only [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
      dite_eq_right hselected]
    have hactual : record.output.preparation.coordinator =
        ReferenceActivePhysicalStep.dispatch record.input := by
      rw [hprep]
      rfl
    cases hconfiguration : record.input.state.coordinator with
    | first =>
        have hcut : record.output.preparation.coordinator =
            .first (CoordinatorRoundDispatch.dispatchFirst
              (ReferenceActivePhysicalStep.firstInput record.input)) := by
          rw [hactual]
          simp only [ReferenceActivePhysicalStep.dispatch, hconfiguration,
            CoordinatorRoundDispatch.dispatch]
          rfl
        rw [hcut]
        cases ho : CoordinatorRoundDispatch.dispatchFirst
            (ReferenceActivePhysicalStep.firstInput record.input)
        all_goals try trivial
        case chosen installed selected =>
          have hpost := live_post_choice_bound record.input record.output.preparation
            installed.registers installed.ownedRegisters installed.followerBaseScore
            installed.startRoundResult
          have hbranch := hcut.trans (congrArg DispatchCut.first ho)
          simpa [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
            hbranch, ho, hselected] using hpost
    | live r q base =>
        have hcut : record.output.preparation.coordinator = .live r q base
            (CoordinatorRoundDispatch.dispatchLive
              (ReferenceActivePhysicalStep.liveInput record.input r q base)) := by
          rw [hactual]
          simp only [ReferenceActivePhysicalStep.dispatch, hconfiguration,
            CoordinatorRoundDispatch.dispatch]
          rfl
        rw [hcut]
        cases ho : CoordinatorRoundDispatch.dispatchLive
            (ReferenceActivePhysicalStep.liveInput record.input r q base)
        all_goals try trivial
        case continuingChosen dispatched hstart hno selected =>
          have hex := ReferenceCompleteLiveChoiceDomains.complete_live_dispatch_choice_exists
            rate rewards C_star C_h source k r q base hconfiguration
          rcases hex with ⟨_hprepared, hchoices⟩
          have ho' : CoordinatorRoundDispatch.dispatchLive
              (ReferenceActivePhysicalStep.liveInput
                (ReferenceCompletePhysicalHistory.completeSuffixRecords
                  rate source rewards C_star C_h)[k.val].input r q base) =
                .continuingChosen dispatched hstart hno selected := by
            simpa only [record] using ho
          simp only [ho'] at hchoices
          rcases hchoices with ⟨_hclockFrame, hclockNone, hvalid, _hboundary,
            _harm, v, hvselected, hpayload, _hpending, hcutoff, _hstarted,
            _harmEq, _hpendingEq, _hcutoffEq, _hchoice⟩
          have hlive : CoordinatorLocalArmChoice.assignmentIsLive
              v.view.payload v.view.cutoff record.input.time := by
            rw [hpayload, hcutoff]
            have htime := hvalid.time
            refine ⟨htime.assignment_started, ?_⟩
            simp [
              CoordinatorLocalArmChoice.sourceRound,
              CoordinatorLocalArmChoice.cutoffRound,
              CoordinatorLiveChoiceRecorderStep.cutoffFromClock, hclockNone]
          have hvselected' : record.output.preparation.coordinator.selection = some v := by
            rw [hprep]
            exact hvselected
          have hbranch : record.output.preparation.coordinator =
              .live r q base (.continuingChosen dispatched hstart hno selected) :=
            hcut.trans (congrArg (DispatchCut.live r q base) ho)
          have hobs := ReferenceActivePhysicalStep.observeCoordinator_live_equation
            record.output.preparation r q base
            (.continuingChosen dispatched hstart hno selected) hbranch
          have hselection :
              (DispatchCut.live r q base
                (.continuingChosen dispatched hstart hno selected)).selection = some v := by
            rw [← hbranch]
            exact hvselected'
          have hselNe : (DispatchCut.live r q base
              (.continuingChosen dispatched hstart hno selected)).selection ≠ none := by
            rw [hselection]
            simp
          cases hpost : (ReferenceActivePhysicalStep.livePostChoice
              record.output.preparation
              (ReferenceActivePhysicalStep.liveRegistersAt r record.input.time)
              (ReferenceActivePhysicalStep.liveOwnedAt r q record.input.time) base
              dispatched.startResult).configuration with
          | first =>
              trivial
          | collection payload ledger saved =>
              trivial
          | dagger =>
              trivial
          | live next nextOwned nextBase =>
              have hnext : record.output.next.coordinator = .live next nextOwned nextBase := by
                rw [hout, hobs]
                simp [hselNe, hpost]
              have hbound := selected_live_output_last_service_bound
                rewards C_star C_h source k v hvselected' hlive next nextOwned nextBase hnext
              simpa [hout, hobs, hselNe, hpost,
                liveInputLastServiceBound] using hbound
        case cutoffChosen dispatched hstart ledger hinit hcandidate hdomains hclock
            hpending hno selected =>
          have hpost := collection_post_choice_bound record.input record.output.preparation
            r.payload (ReferenceActivePhysicalStep.sharedLedger ledger)
            dispatched.startResult
            (ReferenceActivePhysicalStep.liveRegistersAt r record.input.time).complementWeights
          have hbranch : record.output.preparation.coordinator =
              .live r q base (CoordinatorRoundDispatch.dispatchLive
                (ReferenceActivePhysicalStep.liveInput record.input r q base)) := hcut
          simpa [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
            hbranch, ho, hselected] using hpost
    | collection old ledger saved =>
        by_cases hcutoff : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
        · let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
          let clock := ReferenceActivePhysicalStep.collectionClock old ledger saved cutoff
          have hcut : record.output.preparation.coordinator =
              .collection old ledger clock cutoff
                (CoordinatorRoundDispatch.dispatchCollection
                  (ReferenceActivePhysicalStep.collectionInput record.input old ledger clock cutoff)) := by
            rw [hactual]
            simp only [ReferenceActivePhysicalStep.dispatch, hconfiguration,
              dite_eq_left hcutoff, CoordinatorRoundDispatch.dispatch]
            rfl
          rw [hcut]
          cases ho : CoordinatorRoundDispatch.dispatchCollection
              (ReferenceActivePhysicalStep.collectionInput record.input old ledger clock cutoff)
          all_goals try trivial
          case continuing core snapshot hcontinue selected =>
            have hpost := collection_post_choice_bound record.input record.output.preparation
              old ledger snapshot.clockStarted
              (CoordinatorCollectionInteractive.PreObservationInputs.weights
                (ReferenceActivePhysicalStep.collectionInput record.input old ledger clock cutoff)
                snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq)
            have hbranch := hcut.trans
              (congrArg (DispatchCut.collection old ledger clock cutoff) ho)
            simpa [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
              hbranch, ho, hselected] using hpost
          case laterChosen core consistent started hstart instruction hinstruction output hlocal
              clockData installed selected =>
            have hpost := live_post_choice_bound record.input record.output.preparation
              installed.registers installed.ownedRegisters installed.retainedBaseScore started
            have hbranch := hcut.trans
              (congrArg (DispatchCut.collection old ledger clock cutoff) ho)
            simpa [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
              hbranch, ho, hselected] using hpost
        · have hcut : record.output.preparation.coordinator = .invalidCollectionCutoff := by
            rw [hactual]
            simp only [ReferenceActivePhysicalStep.dispatch, hconfiguration,
              dite_eq_right hcutoff]
          rw [hcut]
          trivial
    | dagger =>
        have hcut : record.output.preparation.coordinator = .dagger := by
          rw [hactual]
          simp only [ReferenceActivePhysicalStep.dispatch, hconfiguration]
        rw [hcut]
        trivial

private theorem connected_first_input
    {initial final : ReferenceActivePhysicalHorizon.State p rate}
    {records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))}
    (hconnected : ReferenceActivePhysicalHorizon.Connected initial records final)
    (hfirst : 0 < records.length) : records[0].input.state = initial := by
  cases records with
  | nil => simp only [List.length_nil] at hfirst; omega
  | cons record rest => exact hconnected.1

private theorem connected_succ_input
    {initial final : ReferenceActivePhysicalHorizon.State p rate}
    {records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))}
    (hconnected : ReferenceActivePhysicalHorizon.Connected initial records final)
    (n : ℕ) (hn : n + 1 < records.length) :
    records[n + 1].input.state = records[n].output.next := by
  induction records generalizing initial n with
  | nil => simp only [List.length_nil] at hn; omega
  | cons record rest ih =>
      cases n with
      | zero =>
          cases rest with
          | nil => simp only [List.length_cons, List.length_nil] at hn; omega
          | cons next tail => exact hconnected.2.1
      | succ n => exact ih hconnected.2 n (by simp only [List.length_cons] at hn; omega)

private theorem complete_live_input_last_service_bound
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length) :
    liveInputLastServiceBound
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val].input.state.coordinator := by
  classical
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
  cases hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h with
  | none =>
      have hlength := k.isLt
      simp only [ReferenceCompletePhysicalHistory.completeSuffixRecords,
        hlaunch, dite_true, List.length_nil] at hlength
      omega
  | some active =>
      have hc := (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
        rate source rewards C_star C_h).mp (by rw [hlaunch]; rfl)
      let initial := ReferenceFirstLaunchNumericalCell.launchState
        rate source rewards C_star C_h hc
      let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
        rate source rewards C_star C_h hc
      have hcanonical := ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
        rate source rewards C_star C_h hc
      have hconnected := ReferenceCompletePhysicalHistory.completeSuffix_connected_on_launch
        rate source rewards C_star C_h initial hcanonical
      have hfold : ∀ n (hn : n < R.length),
          liveInputLastServiceBound R[n].input.state.coordinator ∧
          liveInputLastServiceBound R[n].output.next.coordinator := by
        intro n
        induction n with
        | zero =>
            intro hn
            have hstate := connected_first_input hconnected hn
            have hin : liveInputLastServiceBound R[0].input.state.coordinator := by
              rw [hstate, seed.coordinatorFirst]
              trivial
            have hout := round_live_input_last_service_bound
              rewards C_star C_h source ⟨0, hn⟩ hin
            exact ⟨hin, hout⟩
        | succ n ih =>
            intro hn
            have hnprev : n < R.length := by omega
            obtain ⟨_hin, hout⟩ := ih hnprev
            have hstate := connected_succ_input hconnected n hn
            have hin : liveInputLastServiceBound R[n + 1].input.state.coordinator := by
              rw [hstate]
              exact hout
            have hnext := round_live_input_last_service_bound
              rewards C_star C_h source ⟨n + 1, hn⟩ hin
            exact ⟨hin, hnext⟩
      exact (hfold k.val k.isLt).1

private def cutoffLastServiceFrame
    (P : ReferenceActivePhysicalStep.Payload rate)
    (l : ReferenceActivePhysicalStep.Ledger rate) : Prop :=
  ∀ j : CanonicalFastSampling.FastArm P.slowSet,
    ∃ cut : CoordinatorCollectionLedger.CutoffRegister,
      ∃ current : CoordinatorCollectionLedger.CurrentRegister,
        l.cutoffRegisters j.1 = some cut ∧
        l.currentRegisters j.1 = some current ∧
        cut.lastService ≤ cut.score ∧ cut.lastService ≤ 4 * rate.n

private theorem checked_round_cutoff_last_service_frame
    (P : ReferenceActivePhysicalStep.Payload rate)
    (l started decoded finished : ReferenceActivePhysicalStep.Ledger rate)
    (input : CollectionCheckedExecution.RoundInput (p := p) (eta := rate.eta.val))
    (hframe : cutoffLastServiceFrame P l)
    (hstart : CoordinatorCollectionLedger.startRound l
      (CoordinatorCollectionLedger.sourceRound input.round) input.enabled input.raw =
      .success started)
    (hdecode : CoordinatorCollectionLedger.decodeUp started input.selectedFollower input.parsed =
      .success decoded ∨ CoordinatorCollectionLedger.decodeUp started input.selectedFollower input.parsed =
      .rejected decoded)
    (hfinish : CoordinatorCollectionLedger.finishRound decoded = .success finished) :
    cutoffLastServiceFrame P finished := by
  intro j
  obtain ⟨cut, current, hcut, hcurrent, hscore, hcap⟩ := hframe j
  obtain ⟨hnext, _hinc, _ha, _hs, _hcutoff, _hf, hcutFrame⟩ :=
    CollectionKnownQueueContinuation.checkedRound_known_transition
      l started decoded finished input j.1 current hcurrent hstart hdecode hfinish
  exact ⟨cut, _, hcutFrame.trans hcut, hnext, hscore, hcap⟩

private theorem collection_tail_cutoff_last_service_frame
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (c : ReferenceCollectionSegmentExtraction.Choice rate)
    (hframe : cutoffLastServiceFrame c.payload c.preLedger) :
    match (ReferenceActivePhysicalStep.collectionPostChoice
      (ReferenceActivePhysicalStep.prepare x) c.payload c.preLedger c.started c.weights).configuration with
    | .collection P final _ => cutoffLastServiceFrame P final
    | _ => True := by
  unfold ReferenceActivePhysicalStep.collectionPostChoice
  cases hrecord : CoordinatorRecorderComplementBridge.run
      (ReferenceActivePhysicalStep.collectionRecordingInput
        (ReferenceActivePhysicalStep.prepare x) c.payload c.started c.weights) with
  | none => trivial
  | some recording =>
      dsimp only
      cases hstart : CoordinatorCollectionLedger.startRound c.preLedger (x.time.val + 1)
          (ReferenceActivePhysicalStep.collectionEnabled c.preLedger x.time)
          (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) with
      | invalid => trivial
      | rejected bad => trivial
      | success started =>
          dsimp only
          unfold ReferenceActivePhysicalStep.collectionFinish
          have hdecodeResult := ReferenceCollectionSegmentExtraction.receiveUp_decode_result x started
          cases hreceive : (ReferenceActivePhysicalStep.receiveUp
              (ReferenceActivePhysicalStep.prepare x) started).result with
          | invalid => trivial
          | success pair | rejected pair =>
              rcases pair with ⟨decoded, bank⟩
              simp only [hreceive] at hdecodeResult ⊢
              cases hfinish : CoordinatorCollectionLedger.finishRound decoded with
              | invalid => trivial
              | rejected bad => trivial
              | success finished =>
                  dsimp only
                  cases hclock : CoordinatorPhaseClock.finishRound p rate.eta.val x.time
                      c.started.clock finished.pending x.row with
                  | error reason => trivial
                  | ok clockFinished =>
                      dsimp only
                      let input := ReferenceCollectionSegmentExtraction.inputOf
                        x c.preLedger recording started
                      have hdecode :
                          CoordinatorCollectionLedger.decodeUp started input.selectedFollower input.parsed =
                            .success decoded ∨
                          CoordinatorCollectionLedger.decodeUp started input.selectedFollower input.parsed =
                            .rejected decoded := by
                        first | exact Or.inl hdecodeResult | exact Or.inr hdecodeResult
                      exact checked_round_cutoff_last_service_frame c.payload
                        c.preLedger started decoded finished input hframe hstart hdecode hfinish

private theorem live_tail_no_collection
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ)
    (started : CoordinatorPhaseClock.StartRoundResult p) :
    match (ReferenceActivePhysicalStep.livePostChoice
      (ReferenceActivePhysicalStep.prepare x) r q base started).configuration with
    | .collection _ _ _ => False
    | _ => True := by
  unfold ReferenceActivePhysicalStep.livePostChoice
  cases hrecord : CoordinatorRecorderComplementBridge.run
      (ReferenceActivePhysicalStep.liveRecordingInput
        (ReferenceActivePhysicalStep.prepare x) r started) with
  | none => simp [ReferenceActivePhysicalStep.coordinatorFailure]
  | some recording =>
      cases hservice : CoordinatorLiveServiceFinish.servicePass r q recording with
      | error reason => simp [hservice, ReferenceActivePhysicalStep.coordinatorFailure]
      | ok serviced =>
          cases hconfirmation : CoordinatorLocalArmChoice.confirmationUpdate r.payload
              started.pending
              (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
              x.time x.row (ReferenceActivePhysicalStep.prepare x).coordinatorObservation with
          | none => simp [hservice,
              ReferenceActivePhysicalStep.coordinatorFailure]
          | some pending =>
              cases hfinish : CoordinatorPhaseClock.finishRound p rate.eta.val x.time
                  started.clock pending x.row with
              | error reason => simp [hservice, hfinish,
                  ReferenceActivePhysicalStep.coordinatorFailure]
              | ok finished => simp [hservice, hfinish]

private theorem cutoff_choice_last_service_frame
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ)
    (hlive : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val].input.state.coordinator = .live r q base)
    (hbound : ∀ j : CanonicalFastSampling.FastArm r.payload.slowSet,
      q.previousService j ≤ r.complementScores j ∧ q.previousService j ≤ 4 * rate.n)
    (c : ReferenceCollectionSegmentExtraction.Choice rate)
    (hchoice : ReferenceCollectionSegmentExtraction.choice
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val].input = some c) :
    cutoffLastServiceFrame c.payload c.preLedger := by
  classical
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
  let x := R[k.val].input
  have hcut : (ReferenceActivePhysicalStep.prepare x).coordinator = .live r q base
      (CoordinatorRoundDispatch.dispatchLive (ReferenceActivePhysicalStep.liveInput x r q base)) := by
    change x.state.coordinator = .live r q base at hlive
    change ReferenceActivePhysicalStep.dispatch x = _
    simp only [ReferenceActivePhysicalStep.dispatch, hlive, CoordinatorRoundDispatch.dispatch]
    rfl
  have hc := hchoice
  change ReferenceCollectionSegmentExtraction.choice x = some c at hc
  unfold ReferenceCollectionSegmentExtraction.choice at hc
  split at hc
  · cases hc
  · rw [hcut] at hc
    cases ho : CoordinatorRoundDispatch.dispatchLive (ReferenceActivePhysicalStep.liveInput x r q base)
    all_goals simp only [ho, ReferenceCollectionSegmentExtraction.choiceOfCut] at hc
    all_goals try cases hc
    case isFalse.cutoffChosen.refl dispatched hstart ledger hinit hcandidate hdomains hclock
        hpending hno selected =>
      change ∀ j : CanonicalFastSampling.FastArm r.payload.slowSet, _
      intro j
      let cut : CoordinatorCollectionLedger.CutoffRegister :=
        ⟨r.complementScores j, q.queue j, q.previousService j⟩
      let current : CoordinatorCollectionLedger.CurrentRegister :=
        ⟨q.queue j, q.previousService j⟩
      refine ⟨cut, current, ?_, ?_, ?_, ?_⟩
      · change (ReferenceActivePhysicalStep.sharedLedger ledger).cutoffRegisters j.1 = some cut
        rw [hcandidate]
        change CoordinatorStartRoundCutoffDispatch.outsideRegisters
          (ReferenceActivePhysicalStep.liveRegistersAt r x.time)
          (ReferenceActivePhysicalStep.liveOwnedAt r q x.time) j.1 = some cut
        unfold CoordinatorStartRoundCutoffDispatch.outsideRegisters
        have hj : j.1 ∈ CanonicalFastSampling.fastArmFinset
            (ReferenceActivePhysicalStep.liveRegistersAt r x.time).payload.slowSet := j.property
        rw [dite_eq_left hj]
        rfl
      · change (ReferenceActivePhysicalStep.sharedLedger ledger).currentRegisters j.1 = some current
        rw [hcandidate]
        change Option.map (fun c : CoordinatorCollectionLedger.CutoffRegister =>
          (⟨c.queue, c.lastService⟩ : CoordinatorCollectionLedger.CurrentRegister))
          (CoordinatorStartRoundCutoffDispatch.outsideRegisters
            (ReferenceActivePhysicalStep.liveRegistersAt r x.time)
            (ReferenceActivePhysicalStep.liveOwnedAt r q x.time) j.1) = some current
        unfold CoordinatorStartRoundCutoffDispatch.outsideRegisters
        have hj : j.1 ∈ CanonicalFastSampling.fastArmFinset
            (ReferenceActivePhysicalStep.liveRegistersAt r x.time).payload.slowSet := j.property
        rw [dite_eq_left hj]
        rfl
      · exact (hbound j).1
      · exact (hbound j).2

private theorem coordinator_round_cutoff_last_service_frame
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (hcollection : ∀ P l saved,
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val].input.state.coordinator = .collection P l saved →
      cutoffLastServiceFrame P l)
    (hlive : ∀ r q base,
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val].input.state.coordinator = .live r q base →
      ∀ j : CanonicalFastSampling.FastArm r.payload.slowSet,
        q.previousService j ≤ r.complementScores j ∧ q.previousService j ≤ 4 * rate.n) :
    match (ReferenceActivePhysicalStep.prepare
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val].input).observeCoordinator.configuration with
    | .collection P final _ => cutoffLastServiceFrame P final
    | _ => True := by
  classical
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
  let x := R[k.val].input
  change match (ReferenceActivePhysicalStep.prepare x).observeCoordinator.configuration with
    | .collection P final _ => cutoffLastServiceFrame P final
    | _ => True
  by_cases hselected : (ReferenceActivePhysicalStep.prepare x).coordinator.selection = none
  · simp only [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
      dite_eq_left hselected]
    cases (ReferenceActivePhysicalStep.prepare x).coordinator <;> trivial
  · simp only [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
      dite_eq_right hselected]
    have hactual : (ReferenceActivePhysicalStep.prepare x).coordinator =
        ReferenceActivePhysicalStep.dispatch x := rfl
    cases hconfiguration : x.state.coordinator with
    | first =>
        have hcut : (ReferenceActivePhysicalStep.prepare x).coordinator =
            .first (CoordinatorRoundDispatch.dispatchFirst
              (ReferenceActivePhysicalStep.firstInput x)) := by
          rw [hactual]
          simp only [ReferenceActivePhysicalStep.dispatch, hconfiguration,
            CoordinatorRoundDispatch.dispatch]
          rfl
        rw [hcut]
        cases ho : CoordinatorRoundDispatch.dispatchFirst
            (ReferenceActivePhysicalStep.firstInput x)
        all_goals try trivial
        case chosen installed selected =>
          have hnoCollection := live_tail_no_collection x installed.registers
            installed.ownedRegisters installed.followerBaseScore installed.startRoundResult
          split at hnoCollection <;> simp_all only
    | live r q base =>
        have hcut : (ReferenceActivePhysicalStep.prepare x).coordinator =
            .live r q base (CoordinatorRoundDispatch.dispatchLive
              (ReferenceActivePhysicalStep.liveInput x r q base)) := by
          rw [hactual]
          simp only [ReferenceActivePhysicalStep.dispatch, hconfiguration,
            CoordinatorRoundDispatch.dispatch]
          rfl
        rw [hcut]
        cases ho : CoordinatorRoundDispatch.dispatchLive
            (ReferenceActivePhysicalStep.liveInput x r q base)
        all_goals try trivial
        case continuingChosen dispatched hstart continuation selected =>
          have hnoCollection := live_tail_no_collection x
            (ReferenceActivePhysicalStep.liveRegistersAt r x.time)
            (ReferenceActivePhysicalStep.liveOwnedAt r q x.time) base dispatched.startResult
          split at hnoCollection <;> simp_all only
        case cutoffChosen dispatched hstart ledger hinit hcandidate hdomains hclock
            hpending hno selected =>
          let c : ReferenceCollectionSegmentExtraction.Choice rate :=
            ⟨r.payload, ReferenceActivePhysicalStep.sharedLedger ledger,
              dispatched.startResult,
              (ReferenceActivePhysicalStep.liveRegistersAt r x.time).complementWeights,
              some (ReferenceCollectionSegmentExtraction.cutoffInitializer
                (ReferenceActivePhysicalStep.liveRegistersAt r x.time)
                (ReferenceActivePhysicalStep.liveOwnedAt r q x.time) base x.time)⟩
          have hchoice : ReferenceCollectionSegmentExtraction.choice x = some c := by
            unfold ReferenceCollectionSegmentExtraction.choice
            rw [ite_eq_right hselected, hcut, ho]
            rfl
          have hbound := hlive r q base hconfiguration
          have hframe := cutoff_choice_last_service_frame rate rewards C_star C_h source k
            r q base hconfiguration hbound c hchoice
          exact collection_tail_cutoff_last_service_frame x c hframe
    | collection old ledger saved =>
        by_cases hcutoff : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
        · let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
          let clock := ReferenceActivePhysicalStep.collectionClock old ledger saved cutoff
          have hcut : (ReferenceActivePhysicalStep.prepare x).coordinator =
              .collection old ledger clock cutoff
                (CoordinatorRoundDispatch.dispatchCollection
                  (ReferenceActivePhysicalStep.collectionInput x old ledger clock cutoff)) := by
            rw [hactual]
            simp only [ReferenceActivePhysicalStep.dispatch, hconfiguration,
              dite_eq_left hcutoff, CoordinatorRoundDispatch.dispatch]
            rfl
          rw [hcut]
          cases ho : CoordinatorRoundDispatch.dispatchCollection
              (ReferenceActivePhysicalStep.collectionInput x old ledger clock cutoff)
          all_goals try trivial
          case continuing core snapshot hcontinue selected =>
            let c : ReferenceCollectionSegmentExtraction.Choice rate :=
              ⟨old, ledger, snapshot.clockStarted,
                CoordinatorCollectionInteractive.PreObservationInputs.weights
                  (ReferenceActivePhysicalStep.collectionInput x old ledger clock cutoff)
                  snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq, none⟩
            exact collection_tail_cutoff_last_service_frame x c
              (hcollection old ledger saved hconfiguration)
          case laterChosen core consistent started hstart instruction hinstruction output hlocal
              clockData installed selected =>
            have hnoCollection := live_tail_no_collection x installed.registers
              installed.ownedRegisters installed.retainedBaseScore started
            split at hnoCollection <;> simp_all only
        · have hcut : (ReferenceActivePhysicalStep.prepare x).coordinator =
            .invalidCollectionCutoff := by
            rw [hactual]
            simp only [ReferenceActivePhysicalStep.dispatch, hconfiguration,
              dite_eq_right hcutoff]
          rw [hcut]
          trivial
    | dagger =>
        have hcut : (ReferenceActivePhysicalStep.prepare x).coordinator = .dagger := by
          rw [hactual]
          simp only [ReferenceActivePhysicalStep.dispatch, hconfiguration]
        rw [hcut]
        trivial

private theorem complete_collection_input_cutoff_last_service_frame
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (P : ReferenceActivePhysicalStep.Payload rate)
    (l : ReferenceActivePhysicalStep.Ledger rate)
    (saved : Option (Fin p.T × Bool))
    (hinput : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val].input.state.coordinator = .collection P l saved) :
    cutoffLastServiceFrame P l := by
  classical
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
  cases hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h with
  | none =>
      have hlength := k.isLt
      simp only [ReferenceCompletePhysicalHistory.completeSuffixRecords,
        hlaunch, dite_true, List.length_nil] at hlength
      omega
  | some active =>
      have hc := (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
        rate source rewards C_star C_h).mp (by rw [hlaunch]; rfl)
      let initial := ReferenceFirstLaunchNumericalCell.launchState
        rate source rewards C_star C_h hc
      let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
        rate source rewards C_star C_h hc
      have hcanonical := ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
        rate source rewards C_star C_h hc
      have hconnected := ReferenceCompletePhysicalHistory.completeSuffix_connected_on_launch
        rate source rewards C_star C_h initial hcanonical
      have hstep : ∀ (n : Fin R.length),
          (∀ P l saved, R[n.val].input.state.coordinator = .collection P l saved →
            cutoffLastServiceFrame P l) →
          ∀ P l saved, R[n.val].output.next.coordinator = .collection P l saved →
            cutoffLastServiceFrame P l := by
        intro n hin P l saved hout
        have hlive : ∀ r q base,
            R[n.val].input.state.coordinator = .live r q base →
            ∀ j : CanonicalFastSampling.FastArm r.payload.slowSet,
              q.previousService j ≤ r.complementScores j ∧ q.previousService j ≤ 4 * rate.n := by
          intro r q base hconfiguration j
          have hbound := complete_live_input_last_service_bound
            rate rewards C_star C_h source n
          rw [hconfiguration] at hbound
          exact hbound j
        have ht := coordinator_round_cutoff_last_service_frame
          rate rewards C_star C_h source n hin hlive
        have heq : R[n.val].output.next.coordinator =
            (ReferenceActivePhysicalStep.prepare R[n.val].input).observeCoordinator.configuration := by
          rw [R[n.val].output_eq]
          rfl
        rw [← heq, hout] at ht
        exact ht
      have hfold : ∀ n (hn : n < R.length),
          (∀ P l saved, R[n].input.state.coordinator = .collection P l saved →
            cutoffLastServiceFrame P l) ∧
          (∀ P l saved, R[n].output.next.coordinator = .collection P l saved →
            cutoffLastServiceFrame P l) := by
        intro n
        induction n with
        | zero =>
            intro hn
            have hstate := connected_first_input hconnected hn
            have hin : ∀ P l saved, R[0].input.state.coordinator = .collection P l saved →
                cutoffLastServiceFrame P l := by
              intro P l saved hconfiguration
              rw [hstate, seed.coordinatorFirst] at hconfiguration
              cases hconfiguration
            exact ⟨hin, hstep ⟨0, hn⟩ hin⟩
        | succ n ih =>
            intro hn
            obtain ⟨_hin, hout⟩ := ih (by omega)
            have hstate := connected_succ_input hconnected n hn
            have hin : ∀ P l saved, R[n + 1].input.state.coordinator = .collection P l saved →
                cutoffLastServiceFrame P l := by
              intro P l saved he
              rw [hstate] at he
              exact hout P l saved he
            exact ⟨hin, hstep ⟨n + 1, hn⟩ hin⟩
      exact (hfold k.val k.isLt).1 P l saved hinput

/-- The actual complete-source assigned-arm cutoff entries satisfy both
last-service bounds. Current-register presence is derived from the checked
ledger's pending/register consistency, so it is not an extra input. -/
theorem complete_collection_input_assigned_cutoff_last_service_bound
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (P : ReferenceActivePhysicalStep.Payload rate)
    (l : ReferenceActivePhysicalStep.Ledger rate)
    (saved : Option (Fin p.T × Bool))
    (hinput : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val].input.state.coordinator =
        .collection P l saved) :
    ∀ i : Fin (p.m - 1), ∀ cut : CoordinatorCollectionLedger.CutoffRegister,
      l.cutoffRegisters (l.assignment.arm i) = some cut →
        cut.lastService ≤ cut.score ∧ cut.lastService ≤ 4 * rate.n := by
  intro i cut hcut
  have hcore := ReferenceCompleteCollectionDispatchCore.complete_collection_dispatch_core
    rate rewards C_star C_h source k P l saved hinput
  obtain ⟨u, _hu, hvalidCore, _hcurrentScores, _hstarted⟩ := hcore
  have hpresence := ReferenceFirstCutoffRecordedService.validLedger_pendingChecks
    l hvalidCore.ledger_valid
  have hcutNone : (l.cutoffRegisters (l.assignment.arm i)).isNone = false := by
    rw [hcut]
    rfl
  have hpendingFalse : CoordinatorCollectionLedger.armPendingCheck l
      (l.assignment.arm i) = false := by
    have h := hpresence.2 (l.assignment.arm i)
    rw [hcutNone] at h
    exact h.symm
  have hcurrentNone : (l.currentRegisters (l.assignment.arm i)).isNone = false := by
    rw [hpresence.1 (l.assignment.arm i), hpendingFalse]
  obtain ⟨current, hcurrent⟩ : ∃ current : CoordinatorCollectionLedger.CurrentRegister,
      l.currentRegisters (l.assignment.arm i) = some current := by
    cases h : l.currentRegisters (l.assignment.arm i) with
    | none => simp [h] at hcurrentNone
    | some current => exact ⟨current, rfl⟩
  have hspan := ReferenceCompleteCollectionAssignedScoreSpan.complete_collection_input_assigned_score_span
    rate rewards C_star C_h source k P l saved hinput
  dsimp only at hspan
  obtain ⟨_birthIndex, _hprior, _hb, _hbase, _hassignedArm, _hsigma,
    _hcutoff, _hfreeze, _hcutPos, _hcutFreeze, _hterminal, _hcursor,
    _htime, _hincrement, hassigned⟩ := hspan
  have hbounds := hassigned i cut current hcut hcurrent
  exact ⟨hbounds.2.2.1, hbounds.2.2.2.1⟩

/-- Every queried cutoff register at the actual complete-source collection
input has a bounded last service. Assigned entries use the checked assigned
score span; complement entries retain the service fields initialized from
the actual preceding LIVE coordinator through every checked collection round.
-/
theorem complete_collection_input_cutoff_last_service_bound
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (P : ReferenceActivePhysicalStep.Payload rate)
    (l : ReferenceActivePhysicalStep.Ledger rate)
    (saved : Option (Fin p.T × Bool))
    (hinput : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val].input.state.coordinator = .collection P l saved) :
    ∀ a : Fin p.K, ∀ cut : CoordinatorCollectionLedger.CutoffRegister,
      l.cutoffRegisters a = some cut →
        cut.lastService ≤ cut.score ∧ cut.lastService ≤ 4 * rate.n := by
  intro a cut hcut
  have hdata := ReferenceCompleteCollectionAssignedScoreSpan.complete_collection_input_assigned_score_span
    rate rewards C_star C_h source k P l saved hinput
  dsimp only at hdata
  obtain ⟨_birth, _hprior, _hb, _hbase, hassignment, _hsigma, _hcutoff,
    _hfreeze, _hpositive, _hcutFreeze, _hterminal, _hcursor, _htime,
    _hincrement, _hassignedBounds⟩ := hdata
  by_cases ha : a ∈ P.slowSet.1
  · rw [← P.assignment_image] at ha
    obtain ⟨i, _hi, harm⟩ := Finset.mem_image.mp ha
    have hArm : l.assignment.arm i = a := by
      rw [hassignment]
      exact harm
    have hcutI : l.cutoffRegisters (l.assignment.arm i) = some cut := by
      rw [hArm]
      exact hcut
    exact complete_collection_input_assigned_cutoff_last_service_bound
      rate rewards C_star C_h source k P l saved hinput i cut hcutI
  · let j : CanonicalFastSampling.FastArm P.slowSet := ⟨a, by
      simp [ha]⟩
    have hframe := complete_collection_input_cutoff_last_service_frame
      rate rewards C_star C_h source k P l saved hinput
    obtain ⟨cut', current, hcut', _hcurrent, hscore, hcap⟩ := hframe j
    have hcut'At : l.cutoffRegisters a = some cut' := by
      simpa only [j] using hcut'
    have hEq : cut' = cut := Option.some.inj (hcut'At.symm.trans hcut)
    rw [← hEq]
    exact ⟨hscore, hcap⟩

end Bandits.Support.ReferenceCompleteCollectionCutoffLastServiceBounds

end
