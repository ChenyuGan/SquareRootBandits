/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceLaterCollectionArrivalReadout

import Lean.Elab.Tactic.Omega

/-!
# Actual collection cutoff source history

The source first interruption of a retained collection payload is no later
than its actual collection ledger cutoff.  The result is proved along the
existing physical horizon run, starting at the corrected initialization
launch.  It retains the actual coordinator, banks, follower states, rows,
selected index, rewards, and every checked failure branch.

Sources: `sources/zip4/manuscript/06_interruptions.tex:9-14,40-70,246-295`,
`sources/zip4/manuscript/05_binary_transport.tex:72-88`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-60`.

This is an internal source-timing result.  It establishes no local domain
success, numerical replay or credit, queue or score truth, overflow or law,
section closure, or regret conclusion.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceCompletePhysicalHistory
open Bandits.Support.FollowerCutoffScan
open Bandits.Support.ReferenceCoordinatorClockDomains
open Bandits.Support.CoordinatorPhaseClock
open Bandits.Support.CoordinatorRoundDispatch

namespace Bandits.Support.ReferenceCollectionCutoffSourceHistory

variable {p : ConstructorDimensions.Parameters}
    {rate : ReferenceActivePhysicalStep.RateInput p}

private def sourceBound (row : CompletePublicTable.CompleteRow p)
    (configuration : ReferenceActivePhysicalStep.CoordinatorConfiguration p rate) : Prop :=
  match configuration with
  | .collection payload ledger _ =>
      FollowerCutoffScan.firstCutoff p rate.eta.val payload.sigma
        (FollowerCutoffScan.completeRowProposalBit p rate.eta.val row) ≤ ledger.cutoff
  | _ => True

private theorem startRound_cutoff_decision_of_cutoff_frame
    (time : Fin p.T) (clock : CoordinatorPhaseClock.ClockRegisters p)
    (pending : Finset (Fin (p.m - 1)))
    (result : CoordinatorPhaseClock.StartRoundResult p) (sigma : Fin p.T)
    (hparameter : CoordinatorPhaseClock.proposalParameterValid p rate.eta.val)
    (hvalid : CoordinatorPhaseClock.clockRegistersValid p rate.eta.val clock)
    (htime : CoordinatorPhaseClock.startRoundTimeValid p time clock)
    (hstart : CoordinatorPhaseClock.startRound p rate.eta.val time clock pending = .ok result)
    (hsigma : clock.sigma = some sigma) (hu : clock.u = none)
    (hcutoff : result.clock = { clock with u := some time }) :
    CoordinatorPhaseClock.detectCutoff clock time = .ok (.cutoff sigma hsigma) := by
  have hresultU : result.clock.u = some time := by rw [hcutoff]
  have hstart' := hstart
  unfold CoordinatorPhaseClock.startRound at hstart'
  simp only [hparameter, hvalid, htime] at hstart'
  cases hdetect : CoordinatorPhaseClock.detectCutoff clock time with
  | error failure => simp [hdetect] at hstart'
  | ok decision =>
      cases decision with
      | cutoff other hsigmaOther =>
          have heq : other = sigma := Option.some.inj (hsigmaOther.symm.trans hsigma)
          subst other
          have hproof : hsigmaOther = hsigma := Subsingleton.elim _ _
          cases hproof
          rfl
      | noCutoff =>
          have hnotready :
              ¬ CoordinatorPhaseClock.sourceStartTest clock.sigma clock.u time pending := by
            simp [CoordinatorPhaseClock.sourceStartTest,
              CoordinatorPhaseClock.cutoffAtOrBefore, hsigma, hu]
          simp only [hdetect, hnotready] at hstart'
          have huResult := congrArg
            (fun started : CoordinatorPhaseClock.StartRoundResult p => started.clock.u)
            (Except.ok.inj hstart')
          have hnone : (none : Option (Fin p.T)) = result.clock.u := by
            simpa [hu] using huResult
          have habsurd := hnone.trans hresultU
          cases habsurd

private theorem cutoff_decision_has_grid_or_true_prior
    (time stamp : Fin p.T) (clock : CoordinatorPhaseClock.ClockRegisters p)
    (sigma : Fin p.T) (bit : Bool)
    (hsigma : clock.sigma = some sigma) (hu : clock.u = none)
    (hstamp : stamp.val + 1 = time.val)
    (hproposal : clock.lastProposal = some (stamp, bit))
    (hdetect : CoordinatorPhaseClock.detectCutoff clock time =
      .ok (.cutoff sigma hsigma)) :
    FollowerCutoffScan.calendarRound time = clock.g ∨ bit = true := by
  classical
  cases clock with
  | mk savedSigma savedU boundary savedProposal =>
      cases savedSigma with
      | none => simp at hsigma
      | some actualSigma =>
          have hsame : actualSigma = sigma := Option.some.inj hsigma
          subst actualSigma
          cases savedU with
          | some oldCutoff => simp at hu
          | none =>
              by_cases hgrid : FollowerCutoffScan.calendarRound time = boundary
              · exact Or.inl hgrid
              · right
                cases savedProposal with
                | none => simp at hproposal
                | some token =>
                    rcases token with ⟨actualStamp, actualBit⟩
                    have hpair := Option.some.inj hproposal
                    cases hpair
                    cases bit with
                    | false =>
                        simp only [CoordinatorPhaseClock.detectCutoff, hgrid,
                          CoordinatorPhaseClock.savedPriorProposal, hstamp] at hdetect
                        change Except.ok CoordinatorPhaseClock.CutoffDecision.noCutoff =
                          Except.ok (.cutoff sigma hsigma) at hdetect
                        cases hdetect
                    | true => rfl

private theorem liveCutoff_sourceBound
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
    (base : Fin (p.m - 1) → ℕ)
    (dispatched : CoordinatorStartRoundCutoffDispatch.Output
      (ReferenceActivePhysicalStep.liveRegistersAt registers x.time)
      (ReferenceActivePhysicalStep.liveOwnedAt registers owned x.time) base)
    (ledger : CoordinatorStartRoundCutoffDispatch.NewLedger
      (ReferenceActivePhysicalStep.liveRegistersAt registers x.time))
    (hstate : x.state.coordinator = .live registers owned base)
    (hclock : ReferenceCoordinatorClockDomains.clockAt x.rows x.selected
      x.time.val x.state)
    (hstart : CoordinatorPhaseClock.startRound p rate.eta.val x.time
      (ReferenceActivePhysicalStep.liveRegistersAt registers x.time).priorClock
      (ReferenceActivePhysicalStep.liveRegistersAt registers x.time).clockPending =
        .ok dispatched.startResult)
    (hledger : ledger = CoordinatorStartRoundCutoffDispatch.collectionStartLedger
      (ReferenceActivePhysicalStep.liveRegistersAt registers x.time)
      (ReferenceActivePhysicalStep.liveOwnedAt registers owned x.time) base x.time)
    (hcutoffClock : dispatched.startResult.clock =
      { (ReferenceActivePhysicalStep.liveRegistersAt registers x.time).priorClock with
        u := some x.time }) :
    FollowerCutoffScan.firstCutoff p rate.eta.val registers.payload.sigma
      (FollowerCutoffScan.completeRowProposalBit p rate.eta.val x.row) ≤
        (ReferenceActivePhysicalStep.sharedLedger ledger).cutoff := by
  have hclock' := hclock
  simp only [ReferenceCoordinatorClockDomains.clockAt, hstate] at hclock'
  rcases hclock' with ⟨hprevious, hvalid, hsigma, hu, hgrid, hlive, hbefore,
    hproposal⟩
  have hparameter :=
    ReferenceCoordinatorClockDomains.proposalParameterValid_of_rate rate
  have htime : CoordinatorPhaseClock.startRoundTimeValid p x.time registers.priorClock := by
    simp [CoordinatorPhaseClock.startRoundTimeValid, hsigma, hu,
      FollowerCutoffScan.calendarRound]
    omega
  have hstart' : CoordinatorPhaseClock.startRound p rate.eta.val x.time
      (ReferenceActivePhysicalStep.liveRegistersAt registers x.time).priorClock
      (ReferenceActivePhysicalStep.liveRegistersAt registers x.time).clockPending =
        .ok dispatched.startResult := hstart
  have hcutoffClock' : dispatched.startResult.clock =
      { (ReferenceActivePhysicalStep.liveRegistersAt registers x.time).priorClock with
        u := some x.time } := hcutoffClock
  have hdecision := startRound_cutoff_decision_of_cutoff_frame
    (rate := rate) x.time
    (ReferenceActivePhysicalStep.liveRegistersAt registers x.time).priorClock
    (ReferenceActivePhysicalStep.liveRegistersAt registers x.time).clockPending
    dispatched.startResult registers.payload.sigma hparameter hvalid htime hstart'
    hsigma hu hcutoffClock'
  have hevent := cutoff_decision_has_grid_or_true_prior
    x.time registers.time registers.priorClock registers.payload.sigma
    (FollowerCutoffScan.completeRowProposalBit p rate.eta.val x.row registers.time)
    hsigma hu hprevious hproposal hdecision
  have hfields := CoordinatorStartRoundCutoffDispatch.collectionStartLedger_fields
    (ReferenceActivePhysicalStep.liveRegistersAt registers x.time)
    (ReferenceActivePhysicalStep.liveOwnedAt registers owned x.time) base x.time
  have hledgerCutoff : ledger.cutoff = x.time.val + 1 := by
    rw [hledger]
    exact hfields.2.2.1
  have hshared := ReferenceActivePhysicalStep.sharedLedger_fields ledger
  have hsharedCutoff :
      (ReferenceActivePhysicalStep.sharedLedger ledger).cutoff = x.time.val + 1 := by
    rw [hshared.2.2.1, hledgerCutoff]
  let bits := FollowerCutoffScan.completeRowProposalBit p rate.eta.val x.row
  rcases hevent with hgridEvent | htrueEvent
  · have hboundary : registers.priorClock.g =
        FollowerCutoffScan.gridBoundary p rate.eta.val registers.payload.sigma := by
      simpa only [CoordinatorPhaseClock.boundaryFromSigma, hsigma] using hvalid.1
    have hgridState : registers.gridBoundary =
        FollowerCutoffScan.gridBoundary p rate.eta.val registers.payload.sigma :=
      hgrid.trans hboundary
    have hgridTime :
        FollowerCutoffScan.gridBoundary p rate.eta.val registers.payload.sigma =
          x.time.val + 1 := by
      calc
        FollowerCutoffScan.gridBoundary p rate.eta.val registers.payload.sigma =
            registers.gridBoundary := hgridState.symm
        _ = registers.priorClock.g := hgrid
        _ = FollowerCutoffScan.calendarRound x.time := hgridEvent.symm
        _ = x.time.val + 1 := by simp [FollowerCutoffScan.calendarRound]
    have hmem : FollowerCutoffScan.gridBoundary p rate.eta.val registers.payload.sigma ∈
        FollowerCutoffScan.firstCutoffCarrier p rate.eta.val registers.payload.sigma bits :=
      Finset.mem_insert_self _ _
    have hmin := Finset.min'_le
      (FollowerCutoffScan.firstCutoffCarrier p rate.eta.val registers.payload.sigma bits)
      (FollowerCutoffScan.gridBoundary p rate.eta.val registers.payload.sigma)
      hmem
    rw [hsharedCutoff, ← hgridTime]
    exact hmin
  · have hcoordinate : registers.time ∈
        FollowerCutoffScan.proposalCoordinates p registers.payload.sigma := by
      simp only [FollowerCutoffScan.proposalCoordinates, Finset.mem_filter,
        Finset.mem_univ, true_and]
      constructor <;> omega
    have hendpoint : FollowerCutoffScan.proposalEndpoint registers.time =
        x.time.val + 1 := by
      simp only [FollowerCutoffScan.proposalEndpoint]
      omega
    have hcarrier : x.time.val + 1 ∈
        FollowerCutoffScan.firstCutoffCarrier p rate.eta.val registers.payload.sigma bits := by
      rw [← hendpoint]
      apply Finset.mem_insert_of_mem
      rw [FollowerCutoffScan.trueProposalEndpoints]
      apply Finset.mem_image.mpr
      exact ⟨registers.time,
        Finset.mem_filter.mpr ⟨hcoordinate, htrueEvent⟩, rfl⟩
    have hmin := Finset.min'_le
      (FollowerCutoffScan.firstCutoffCarrier p rate.eta.val registers.payload.sigma bits)
      (x.time.val + 1) hcarrier
    rw [hsharedCutoff]
    exact hmin

private theorem livePostChoice_not_collection
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
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
  classical
  unfold ReferenceActivePhysicalStep.livePostChoice
  cases hrecord : CoordinatorRecorderComplementBridge.run
      (ReferenceActivePhysicalStep.liveRecordingInput prepared registers started) with
  | none => simp [ReferenceActivePhysicalStep.coordinatorFailure]
  | some recording =>
      cases hservice : CoordinatorLiveServiceFinish.servicePass registers owned recording with
      | error reason => simp [hservice, ReferenceActivePhysicalStep.coordinatorFailure]
      | ok serviced =>
          cases hconfirmation : CoordinatorLocalArmChoice.confirmationUpdate
              registers.payload started.pending
              (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
              x.time x.row prepared.coordinatorObservation with
          | none =>
              simp [hservice,
                ReferenceActivePhysicalStep.coordinatorFailure]
          | some pending =>
              cases hfinish : CoordinatorPhaseClock.finishRound p rate.eta.val x.time
                  started.clock pending x.row with
              | error reason =>
                  simp [hservice, hfinish,
                    ReferenceActivePhysicalStep.coordinatorFailure]
              | ok finished => simp [hservice, hfinish]

private theorem collectionPostChoice_frame
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ)
    (payload' : ReferenceActivePhysicalStep.Payload rate)
    (ledger' : ReferenceActivePhysicalStep.Ledger rate)
    (saved' : Option (Fin p.T × Bool))
    (hout : (ReferenceActivePhysicalStep.collectionPostChoice prepared payload ledger
      started weights).configuration = .collection payload' ledger' saved') :
    payload' = payload ∧ ledger'.cutoff = ledger.cutoff := by
  classical
  have hpayloadFrame :=
    ReferenceAssignmentPayloadPersistence.collectionPostChoice_payload_frame
      prepared payload ledger started weights
  have hstored : ReferenceAssignmentPayloadPersistence.storedPayload
      ((ReferenceActivePhysicalStep.collectionPostChoice prepared payload ledger
        started weights).configuration) = some payload' := by
    rw [hout]
    rfl
  unfold ReferenceActivePhysicalStep.collectionPostChoice at hout
  cases hrecord : CoordinatorRecorderComplementBridge.run
      (ReferenceActivePhysicalStep.collectionRecordingInput prepared payload started weights) with
  | none => simp [hrecord, ReferenceActivePhysicalStep.coordinatorFailure] at hout
  | some recording =>
      cases hstart : CoordinatorCollectionLedger.startRound ledger (x.time.val + 1)
          (ReferenceActivePhysicalStep.collectionEnabled ledger x.time)
          (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) with
      | invalid => simp [hrecord, hstart, ReferenceActivePhysicalStep.coordinatorFailure] at hout
      | rejected rejected =>
          simp [hrecord, hstart, ReferenceActivePhysicalStep.coordinatorFailure] at hout
      | success startedLedger =>
          unfold ReferenceActivePhysicalStep.collectionFinish at hout
          cases hreceive : (ReferenceActivePhysicalStep.receiveUp prepared startedLedger).result with
          | invalid =>
              simp [hrecord, hstart, hreceive,
                ReferenceActivePhysicalStep.coordinatorFailure] at hout
          | success pair =>
              rcases pair with ⟨received, bank⟩
              cases hfinish : CoordinatorCollectionLedger.finishRound received with
              | invalid =>
                  simp [hrecord, hstart, hreceive, hfinish,
                    ReferenceActivePhysicalStep.coordinatorFailure] at hout
              | rejected rejected =>
                  simp [hrecord, hstart, hreceive, hfinish,
                    ReferenceActivePhysicalStep.coordinatorFailure] at hout
              | success finished =>
                  cases hclockFinish : CoordinatorPhaseClock.finishRound p rate.eta.val
                      x.time started.clock finished.pending x.row with
                  | error reason =>
                      simp [hrecord, hstart, hreceive, hfinish, hclockFinish,
                        ReferenceActivePhysicalStep.coordinatorFailure] at hout
                  | ok clockFinished =>
                      have hstartFrame := ReferenceCollectionClockPreservation.ledger_startRound_frame
                        ledger startedLedger x.time (ReferenceActivePhysicalStep.collectionEnabled ledger x.time)
                        (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) hstart
                      have hreceiveFrame := ReferenceCollectionClockPreservation.receiveUp_frame
                        prepared startedLedger (received, bank) (Or.inl hreceive)
                      have hfinishFrame := ReferenceCollectionClockPreservation.ledger_finishRound_frame
                        received finished hfinish
                      have hcutoff : finished.cutoff = ledger.cutoff :=
                        hfinishFrame.2.1.trans (hreceiveFrame.2.1.trans hstartFrame.2.1)
                      simp [hrecord, hstart, hreceive, hfinish, hclockFinish] at hout
                      rcases hout with ⟨_, hledgerEq, _⟩
                      have hpayload : payload' = payload := by
                        rcases hpayloadFrame with hnone | hsome
                        · rw [hstored] at hnone
                          cases hnone
                        · rw [hstored] at hsome
                          exact Option.some.inj hsome
                      have hledgerCutoff : ledger'.cutoff = ledger.cutoff := by
                        rw [← hledgerEq]
                        exact hcutoff
                      exact ⟨hpayload, hledgerCutoff⟩
          | rejected pair =>
              rcases pair with ⟨received, bank⟩
              cases hfinish : CoordinatorCollectionLedger.finishRound received with
              | invalid =>
                  simp [hrecord, hstart, hreceive, hfinish,
                    ReferenceActivePhysicalStep.coordinatorFailure] at hout
              | rejected rejected =>
                  simp [hrecord, hstart, hreceive, hfinish,
                    ReferenceActivePhysicalStep.coordinatorFailure] at hout
              | success finished =>
                  cases hclockFinish : CoordinatorPhaseClock.finishRound p rate.eta.val
                      x.time started.clock finished.pending x.row with
                  | error reason =>
                      simp [hrecord, hstart, hreceive, hfinish, hclockFinish,
                        ReferenceActivePhysicalStep.coordinatorFailure] at hout
                  | ok clockFinished =>
                      have hstartFrame := ReferenceCollectionClockPreservation.ledger_startRound_frame
                        ledger startedLedger x.time (ReferenceActivePhysicalStep.collectionEnabled ledger x.time)
                        (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) hstart
                      have hreceiveFrame := ReferenceCollectionClockPreservation.receiveUp_frame
                        prepared startedLedger (received, bank) (Or.inr hreceive)
                      have hfinishFrame := ReferenceCollectionClockPreservation.ledger_finishRound_frame
                        received finished hfinish
                      have hcutoff : finished.cutoff = ledger.cutoff :=
                        hfinishFrame.2.1.trans (hreceiveFrame.2.1.trans hstartFrame.2.1)
                      simp [hrecord, hstart, hreceive, hfinish, hclockFinish] at hout
                      rcases hout with ⟨_, hledgerEq, _⟩
                      have hpayload : payload' = payload := by
                        rcases hpayloadFrame with hnone | hsome
                        · rw [hstored] at hnone
                          cases hnone
                        · rw [hstored] at hsome
                          exact Option.some.inj hsome
                      have hledgerCutoff : ledger'.cutoff = ledger.cutoff := by
                        rw [← hledgerEq]
                        exact hcutoff
                      exact ⟨hpayload, hledgerCutoff⟩

private theorem collectionPostChoice_sourceBound
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ)
    (hbound : FollowerCutoffScan.firstCutoff p rate.eta.val payload.sigma
      (FollowerCutoffScan.completeRowProposalBit p rate.eta.val x.row) ≤ ledger.cutoff) :
    sourceBound x.row (ReferenceActivePhysicalStep.collectionPostChoice
      prepared payload ledger started weights).configuration := by
  classical
  cases hconfiguration : (ReferenceActivePhysicalStep.collectionPostChoice
      prepared payload ledger started weights).configuration with
  | first => simp [sourceBound]
  | live registers owned base => simp [sourceBound]
  | collection payload' ledger' saved =>
      obtain ⟨hpayload, hledger⟩ := collectionPostChoice_frame prepared payload ledger
        started weights payload' ledger' saved hconfiguration
      change FollowerCutoffScan.firstCutoff p rate.eta.val payload'.sigma
          (FollowerCutoffScan.completeRowProposalBit p rate.eta.val x.row) ≤ ledger'.cutoff
      rw [hpayload, hledger]
      exact hbound
  | dagger => simp [sourceBound]

private theorem actualStep_sourceBound
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (hbound : sourceBound x.row x.state.coordinator)
    (hclock : ReferenceCoordinatorClockDomains.clockAt x.rows x.selected
      x.time.val x.state) :
    sourceBound x.row (ReferenceActivePhysicalStep.step x).next.coordinator := by
  classical
  unfold sourceBound
  rw [(ReferenceActivePhysicalStep.step_next_fields x).1]
  cases hstate : x.state.coordinator with
  | first =>
      have hdispatch := ReferenceActivePhysicalStep.dispatch_first x hstate
      have hprepared : (ReferenceActivePhysicalStep.prepare x).coordinator =
          .first (CoordinatorRoundDispatch.dispatchFirst
            (ReferenceActivePhysicalStep.firstInput x)) := by
        rw [(ReferenceActivePhysicalStep.prepare x).coordinator_eq, hdispatch]
      cases hfirst : CoordinatorRoundDispatch.dispatchFirst
          (ReferenceActivePhysicalStep.firstInput x) with
      | choiceDomainFailure installed =>
          have hobs : (ReferenceActivePhysicalStep.prepare x).observeCoordinator =
              ReferenceActivePhysicalStep.coordinatorFailure x.state.upDecoderBank
                .dispatchRejected none none := by
            simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
              hprepared, hfirst, ReferenceActivePhysicalStep.coordinatorFailure]
          rw [hobs]
          simp [ReferenceActivePhysicalStep.coordinatorFailure]
      | recorderBoundaryFailure installed =>
          have hobs : (ReferenceActivePhysicalStep.prepare x).observeCoordinator =
              ReferenceActivePhysicalStep.coordinatorFailure x.state.upDecoderBank
                .dispatchRejected none none := by
            simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
              hprepared, hfirst, ReferenceActivePhysicalStep.coordinatorFailure]
          rw [hobs]
          simp [ReferenceActivePhysicalStep.coordinatorFailure]
      | choiceRejected installed =>
          have hobs : (ReferenceActivePhysicalStep.prepare x).observeCoordinator =
              ReferenceActivePhysicalStep.coordinatorFailure x.state.upDecoderBank
                .dispatchRejected none none := by
            simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
              hprepared, hfirst, ReferenceActivePhysicalStep.coordinatorFailure]
          rw [hobs]
          simp [ReferenceActivePhysicalStep.coordinatorFailure]
      | chosen installed selection =>
          have hprepared' := hprepared
          rw [hfirst] at hprepared'
          have hobs := ReferenceActivePhysicalStep.observeCoordinator_first_equation
            (ReferenceActivePhysicalStep.prepare x)
            (.chosen installed selection) hprepared'
          rw [hobs]
          by_cases hselected :
              (ReferenceActivePhysicalStep.DispatchCut.first
                (.chosen installed selection)).selection = none
          · simp [hselected, ReferenceActivePhysicalStep.coordinatorFailure]
          · simp only [hselected, ite_false]
            cases hconfiguration :
                (ReferenceActivePhysicalStep.livePostChoice
                  (ReferenceActivePhysicalStep.prepare x) installed.registers
                  installed.ownedRegisters installed.followerBaseScore
                  installed.startRoundResult).configuration with
            | collection payload ledger saved =>
                exact False.elim (livePostChoice_not_collection
                  (ReferenceActivePhysicalStep.prepare x) installed.registers
                  installed.ownedRegisters installed.followerBaseScore
                  installed.startRoundResult payload ledger saved hconfiguration)
            | first => trivial
            | live registers owned base => trivial
            | dagger => trivial
  | live registers owned base =>
      cases hlive : CoordinatorRoundDispatch.dispatchLive
          (ReferenceActivePhysicalStep.liveInput x registers owned base) with
      | clockFailure failure hdispatch =>
          have hprepared : (ReferenceActivePhysicalStep.prepare x).coordinator =
              .live registers owned base (.clockFailure failure hdispatch) := by
            simp [ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch,
              hstate, CoordinatorRoundDispatch.dispatch, hlive]; rfl
          have hobs := ReferenceActivePhysicalStep.observeCoordinator_live_equation
            (ReferenceActivePhysicalStep.prepare x) registers owned base
            (.clockFailure failure hdispatch) hprepared
          rw [hobs]
          simp [ReferenceActivePhysicalStep.DispatchCut.selection,
            ReferenceActivePhysicalStep.coordinatorFailure]
      | initializerFailure dispatched hstart checked hinitialization =>
          have hprepared : (ReferenceActivePhysicalStep.prepare x).coordinator =
              .live registers owned base
                (.initializerFailure dispatched hstart checked hinitialization) := by
            simp [ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch,
              hstate, CoordinatorRoundDispatch.dispatch, hlive]; rfl
          have hobs := ReferenceActivePhysicalStep.observeCoordinator_live_equation
            (ReferenceActivePhysicalStep.prepare x) registers owned base
            (.initializerFailure dispatched hstart checked hinitialization) hprepared
          rw [hobs]
          simp [ReferenceActivePhysicalStep.DispatchCut.selection,
            ReferenceActivePhysicalStep.coordinatorFailure]
      | localFailure dispatched hstart reason =>
          have hprepared : (ReferenceActivePhysicalStep.prepare x).coordinator =
              .live registers owned base (.localFailure dispatched hstart reason) := by
            simp [ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch,
              hstate, CoordinatorRoundDispatch.dispatch, hlive]; rfl
          have hobs := ReferenceActivePhysicalStep.observeCoordinator_live_equation
            (ReferenceActivePhysicalStep.prepare x) registers owned base
            (.localFailure dispatched hstart reason) hprepared
          rw [hobs]
          simp [ReferenceActivePhysicalStep.DispatchCut.selection,
            ReferenceActivePhysicalStep.coordinatorFailure]
      | continuingChosen dispatched hstart continuation selection =>
          have hprepared : (ReferenceActivePhysicalStep.prepare x).coordinator =
              .live registers owned base
                (.continuingChosen dispatched hstart continuation selection) := by
            simp [ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch,
              hstate, CoordinatorRoundDispatch.dispatch, hlive]; rfl
          have hobs := ReferenceActivePhysicalStep.observeCoordinator_live_equation
            (ReferenceActivePhysicalStep.prepare x) registers owned base
            (.continuingChosen dispatched hstart continuation selection) hprepared
          have hselected :
              (ReferenceActivePhysicalStep.DispatchCut.live registers owned base
                (.continuingChosen dispatched hstart continuation selection)).selection ≠ none := by
            simp [ReferenceActivePhysicalStep.DispatchCut.selection,
              ReferenceActivePhysicalStep.selectionAt]
          have hobs' : (ReferenceActivePhysicalStep.prepare x).observeCoordinator =
              ReferenceActivePhysicalStep.livePostChoice (ReferenceActivePhysicalStep.prepare x)
                (ReferenceActivePhysicalStep.liveRegistersAt registers x.time)
                (ReferenceActivePhysicalStep.liveOwnedAt registers owned x.time) base
                dispatched.startResult := by
            simpa [hselected] using hobs
          rw [hobs']
          cases hconfiguration :
              (ReferenceActivePhysicalStep.livePostChoice
                (ReferenceActivePhysicalStep.prepare x)
                (ReferenceActivePhysicalStep.liveRegistersAt registers x.time)
                (ReferenceActivePhysicalStep.liveOwnedAt registers owned x.time) base
                dispatched.startResult).configuration with
          | collection payload ledger saved =>
              exact False.elim (livePostChoice_not_collection
                (ReferenceActivePhysicalStep.prepare x)
                (ReferenceActivePhysicalStep.liveRegistersAt registers x.time)
                (ReferenceActivePhysicalStep.liveOwnedAt registers owned x.time) base
                dispatched.startResult payload ledger saved hconfiguration)
          | first => trivial
          | live registers owned base => trivial
          | dagger => trivial
      | cutoffChosen dispatched hstart ledger hinitialization hcandidate hdomains
          hcutoffClock hcutoffPending hnoAssignment selection =>
          have hprepared : (ReferenceActivePhysicalStep.prepare x).coordinator =
              .live registers owned base
                (.cutoffChosen dispatched hstart ledger hinitialization hcandidate hdomains
                  hcutoffClock hcutoffPending hnoAssignment selection) := by
            simp [ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch,
              hstate, CoordinatorRoundDispatch.dispatch, hlive]; rfl
          have hselected :
              (ReferenceActivePhysicalStep.DispatchCut.live registers owned base
                (.cutoffChosen dispatched hstart ledger hinitialization hcandidate hdomains
                  hcutoffClock hcutoffPending hnoAssignment selection)).selection ≠ none := by
            simp [ReferenceActivePhysicalStep.DispatchCut.selection,
              ReferenceActivePhysicalStep.selectionAt]
          have hobs := ReferenceActivePhysicalStep.observeCoordinator_live_equation
            (ReferenceActivePhysicalStep.prepare x) registers owned base
            (.cutoffChosen dispatched hstart ledger hinitialization hcandidate hdomains
              hcutoffClock hcutoffPending hnoAssignment selection) hprepared
          have hobs' : (ReferenceActivePhysicalStep.prepare x).observeCoordinator =
              ReferenceActivePhysicalStep.collectionPostChoice
                (ReferenceActivePhysicalStep.prepare x) registers.payload
                (ReferenceActivePhysicalStep.sharedLedger ledger) dispatched.startResult
                (ReferenceActivePhysicalStep.liveRegistersAt registers x.time).complementWeights := by
            simpa [hselected] using hobs
          have hstart' : CoordinatorPhaseClock.startRound
              p (ReferenceActivePhysicalStep.liveInput x registers owned base).eta.val
              (ReferenceActivePhysicalStep.liveInput x registers owned base).registers.time
              (ReferenceActivePhysicalStep.liveInput x registers owned base).registers.priorClock
              (ReferenceActivePhysicalStep.liveInput x registers owned base).registers.clockPending =
                .ok dispatched.startResult := hstart
          have hboundBirth := liveCutoff_sourceBound registers owned base dispatched ledger
            hstate hclock hstart' hcandidate hcutoffClock
          rw [hobs']
          exact collectionPostChoice_sourceBound
            (ReferenceActivePhysicalStep.prepare x) registers.payload
            (ReferenceActivePhysicalStep.sharedLedger ledger) dispatched.startResult
            (ReferenceActivePhysicalStep.liveRegistersAt registers x.time).complementWeights
            hboundBirth
  | collection payload ledger saved =>
      have hclock' := hclock
      simp only [ReferenceCoordinatorClockDomains.clockAt, hstate] at hclock'
      have hcutoffValid : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T :=
        ⟨hclock'.2.2.1, hclock'.2.2.2.1⟩
      let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
      let clock := ReferenceActivePhysicalStep.collectionClock payload ledger saved cutoff
      have hdispatch : ReferenceActivePhysicalStep.dispatch x =
          .collection payload ledger clock cutoff
            (CoordinatorRoundDispatch.dispatchCollection
              (ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff)) := by
        simp [ReferenceActivePhysicalStep.dispatch, hstate, hcutoffValid,
          cutoff, clock, ReferenceActivePhysicalStep.collectionClock,
          CoordinatorRoundDispatch.dispatch]; rfl
      have hprepared : (ReferenceActivePhysicalStep.prepare x).coordinator =
          .collection payload ledger clock cutoff
            (CoordinatorRoundDispatch.dispatchCollection
              (ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff)) := by
        rw [(ReferenceActivePhysicalStep.prepare x).coordinator_eq, hdispatch]
      have hsource : FollowerCutoffScan.firstCutoff p rate.eta.val payload.sigma
          (FollowerCutoffScan.completeRowProposalBit p rate.eta.val x.row) ≤ ledger.cutoff := by
        simpa [sourceBound, hstate] using hbound
      cases hcollection : CoordinatorRoundDispatch.dispatchCollection
          (ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff) with
      | clockFailure failure hstart =>
          have hprepared' := hprepared
          rw [hcollection] at hprepared'
          have hobs := ReferenceActivePhysicalStep.observeCoordinator_collection_equation
            (ReferenceActivePhysicalStep.prepare x) payload ledger clock cutoff
            (.clockFailure failure hstart) hprepared'
          rw [hobs]
          simp [ReferenceActivePhysicalStep.DispatchCut.selection,
            ReferenceActivePhysicalStep.coordinatorFailure]
      | localFailure started hstart hcore reason =>
          have hprepared' := hprepared
          rw [hcollection] at hprepared'
          have hobs := ReferenceActivePhysicalStep.observeCoordinator_collection_equation
            (ReferenceActivePhysicalStep.prepare x) payload ledger clock cutoff
            (.localFailure started hstart hcore reason) hprepared'
          rw [hobs]
          simp [ReferenceActivePhysicalStep.DispatchCut.selection,
            ReferenceActivePhysicalStep.coordinatorFailure]
      | coreFailure core started hstart reason =>
          have hprepared' := hprepared
          rw [hcollection] at hprepared'
          have hobs := ReferenceActivePhysicalStep.observeCoordinator_collection_equation
            (ReferenceActivePhysicalStep.prepare x) payload ledger clock cutoff
            (.coreFailure core started hstart reason) hprepared'
          rw [hobs]
          simp [ReferenceActivePhysicalStep.DispatchCut.selection,
            ReferenceActivePhysicalStep.coordinatorFailure]
      | continuing core snapshot boundary scores =>
          have hprepared' := hprepared
          rw [hcollection] at hprepared'
          have hobs := ReferenceActivePhysicalStep.observeCoordinator_collection_equation
            (ReferenceActivePhysicalStep.prepare x) payload ledger clock cutoff
            (.continuing core snapshot boundary scores) hprepared'
          have hselected :
              (ReferenceActivePhysicalStep.DispatchCut.collection payload ledger clock cutoff
                (.continuing core snapshot boundary scores)).selection ≠ none := by
            simp [ReferenceActivePhysicalStep.DispatchCut.selection]
          have hobs' : (ReferenceActivePhysicalStep.prepare x).observeCoordinator =
              ReferenceActivePhysicalStep.collectionPostChoice
                (ReferenceActivePhysicalStep.prepare x) payload ledger snapshot.clockStarted
                (CoordinatorCollectionInteractive.PreObservationInputs.weights
                  (ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff)
                  snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq) := by
            simpa [hselected] using hobs
          rw [hobs']
          exact collectionPostChoice_sourceBound
            (ReferenceActivePhysicalStep.prepare x) payload ledger snapshot.clockStarted
            (CoordinatorCollectionInteractive.PreObservationInputs.weights
              (ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff)
              snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq) hsource
      | laterReconstructionFailure core consistent started hstart instruction hinstruction reason hlater =>
          have hprepared' := hprepared
          rw [hcollection] at hprepared'
          have hobs := ReferenceActivePhysicalStep.observeCoordinator_collection_equation
            (ReferenceActivePhysicalStep.prepare x) payload ledger clock cutoff
            (.laterReconstructionFailure core consistent started hstart instruction hinstruction reason hlater)
            hprepared'
          rw [hobs]
          simp [ReferenceActivePhysicalStep.DispatchCut.selection,
            ReferenceActivePhysicalStep.coordinatorFailure]
      | laterPrefixFailure core consistent started hstart instruction hinstruction arm reason hlater =>
          have hprepared' := hprepared
          rw [hcollection] at hprepared'
          have hobs := ReferenceActivePhysicalStep.observeCoordinator_collection_equation
            (ReferenceActivePhysicalStep.prepare x) payload ledger clock cutoff
            (.laterPrefixFailure core consistent started hstart instruction hinstruction arm reason hlater)
            hprepared'
          rw [hobs]
          simp [ReferenceActivePhysicalStep.DispatchCut.selection,
            ReferenceActivePhysicalStep.coordinatorFailure]
      | laterOrientationFailure core consistent started hstart instruction hinstruction set hlater =>
          have hprepared' := hprepared
          rw [hcollection] at hprepared'
          have hobs := ReferenceActivePhysicalStep.observeCoordinator_collection_equation
            (ReferenceActivePhysicalStep.prepare x) payload ledger clock cutoff
            (.laterOrientationFailure core consistent started hstart instruction hinstruction set hlater)
            hprepared'
          rw [hobs]
          simp [ReferenceActivePhysicalStep.DispatchCut.selection,
            ReferenceActivePhysicalStep.coordinatorFailure]
      | laterChoiceFailure core consistent started hstart instruction hinstruction output hconsistency
          clockData installation reason =>
          have hprepared' := hprepared
          rw [hcollection] at hprepared'
          have hobs := ReferenceActivePhysicalStep.observeCoordinator_collection_equation
            (ReferenceActivePhysicalStep.prepare x) payload ledger clock cutoff
            (.laterChoiceFailure core consistent started hstart instruction hinstruction output
              hconsistency clockData installation reason) hprepared'
          rw [hobs]
          simp [ReferenceActivePhysicalStep.DispatchCut.selection,
            ReferenceActivePhysicalStep.coordinatorFailure]
      | laterChosen core consistent started hstart instruction hinstruction output hconsistency
          clockData installation selection =>
          have hprepared' := hprepared
          rw [hcollection] at hprepared'
          have hobs := ReferenceActivePhysicalStep.observeCoordinator_collection_equation
            (ReferenceActivePhysicalStep.prepare x) payload ledger clock cutoff
            (.laterChosen core consistent started hstart instruction hinstruction output
              hconsistency clockData installation selection) hprepared'
          have hselected :
              (ReferenceActivePhysicalStep.DispatchCut.collection payload ledger clock cutoff
                (.laterChosen core consistent started hstart instruction hinstruction output
                  hconsistency clockData installation selection)).selection ≠ none := by
            have hinstructionTime := ReferenceActivePhysicalStep.later_instruction_time
              x payload ledger clock cutoff core started instruction hstart hinstruction
            simp [ReferenceActivePhysicalStep.DispatchCut.selection,
              ReferenceActivePhysicalStep.selectionAt, hinstructionTime]
          have hobs' : (ReferenceActivePhysicalStep.prepare x).observeCoordinator =
              ReferenceActivePhysicalStep.livePostChoice
                (ReferenceActivePhysicalStep.prepare x) installation.registers
                installation.ownedRegisters installation.retainedBaseScore started := by
            simpa [hselected] using hobs
          rw [hobs']
          cases hconfiguration : (ReferenceActivePhysicalStep.livePostChoice
              (ReferenceActivePhysicalStep.prepare x) installation.registers
              installation.ownedRegisters installation.retainedBaseScore started).configuration with
          | collection payload' ledger' saved' =>
              exact False.elim (livePostChoice_not_collection
                (ReferenceActivePhysicalStep.prepare x) installation.registers
                installation.ownedRegisters installation.retainedBaseScore started
                payload' ledger' saved' hconfiguration)
          | first => trivial
          | live registers' owned' base' => trivial
          | dagger => trivial
  | dagger =>
      have hdispatch := ReferenceActivePhysicalStep.dispatch_dagger x hstate
      have hprepared : (ReferenceActivePhysicalStep.prepare x).coordinator = .dagger := by
        rw [(ReferenceActivePhysicalStep.prepare x).coordinator_eq, hdispatch]
      have hobs := ReferenceActivePhysicalStep.observeCoordinator_dagger
        (ReferenceActivePhysicalStep.prepare x) hprepared
      rw [hobs]
      simp

private theorem run_prefix_sourceBound
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hseed : ReferenceCoordinatorClockDomains.clockAt rows selected start initial)
    (hfirst : initial.coordinator = .first) :
    ∀ n (hn : n ≤ count),
          sourceBound (rows selected)
          (ReferenceActivePhysicalHorizon.run initial rows selected rewards start n
            (by omega) hmode).finalState.coordinator ∧
        ∀ record ∈ (ReferenceActivePhysicalHorizon.run initial rows selected rewards start n
            (by omega) hmode).records,
          sourceBound (rows selected) record.input.state.coordinator := by
  intro n
  induction n with
  | zero =>
      intro hn
      rw [ReferenceActivePhysicalHorizon.run_zero_final]
      simp [sourceBound, hfirst, ReferenceActivePhysicalHorizon.run_zero_records]
  | succ n ih =>
      intro hn
      have hprev := ih (by omega)
      let record := ReferenceAssignmentPayloadChronology.actualRunRecordAt
        initial rows selected rewards start n (by omega) hmode
      have hrow : record.input.row = rows selected := by
        simp [record, ReferenceAssignmentPayloadChronology.actualRunRecordAt,
          ReferenceActivePhysicalStep.RoundInput.row,
          ReferenceActivePhysicalHorizon.roundInputAt]
      have hrecords := ReferenceAssignmentPayloadChronology.run_successor_actualRunRecordAt
        initial rows selected rewards start n (by omega) hmode
      have hmem : record ∈
          (ReferenceActivePhysicalHorizon.run initial rows selected rewards start (n + 1)
            (by omega) hmode).records := by
        rw [hrecords]
        simp [record]
      have hclockRun := ReferenceRunClockPreservation.run_clockAt initial rows selected rewards
        start (n + 1) (by omega) hmode hseed
      have hclockRecord := (hclockRun).2.2.2 record hmem
      have hrecordState : record.input.state =
          (ReferenceActivePhysicalHorizon.run initial rows selected rewards start n
            (by omega) hmode).finalState := by
        rfl
      have hstepBound : sourceBound record.input.row
          (ReferenceActivePhysicalStep.step record.input).next.coordinator := by
        have hcurrent : sourceBound record.input.row record.input.state.coordinator := by
          rw [hrecordState]
          simpa [hrow] using hprev.1
        exact actualStep_sourceBound hcurrent hclockRecord.1
      have hfinal := ReferenceAssignmentPayloadChronology.run_successor_finalState_eq_actualRunRecordAt
        initial rows selected rewards start n (by omega) hmode
      refine ⟨?_, ?_⟩
      · rw [hfinal]
        rw [hrow] at hstepBound
        simpa [record, ReferenceAssignmentPayloadChronology.actualRunRecordAt] using hstepBound
      · intro current hcurrent
        rw [hrecords] at hcurrent
        rcases List.mem_append.mp hcurrent with hprevious | hlast
        · exact hprev.2 current hprevious
        · have heq : current = record := List.mem_singleton.mp hlast
          subst current
          simpa [hrecordState, hrow] using hprev.1

/-- The actual source cutoff recorded by any continuing collection is no
later than its ledger cutoff, and that cutoff is no later than the current
physical time. -/
theorem complete_continuing_collection_cutoff_source_bound
    {p : ConstructorDimensions.Parameters}
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length) :
    let records := ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h
    let r := records.get k
    let x := r.input
    let prep := r.output.preparation
    let t := x.time
    match prep.coordinator with
    | .collection payload ledger _ _ (.continuing _ _ _ _) =>
        FollowerCutoffScan.firstCutoff p rate.eta.val payload.sigma
          (FollowerCutoffScan.completeRowProposalBit p rate.eta.val x.row) ≤ ledger.cutoff ∧
        ledger.cutoff ≤ t.val
    | _ => True := by
  classical
  let records := ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h
  let record := records.get k
  change match record.output.preparation.coordinator with
    | .collection payload ledger _ _ (.continuing _ _ _ _) =>
        FollowerCutoffScan.firstCutoff p rate.eta.val payload.sigma
          (FollowerCutoffScan.completeRowProposalBit p rate.eta.val record.input.row) ≤ ledger.cutoff ∧
          ledger.cutoff ≤ record.input.time.val
    | _ => True
  let start := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
  rcases ReferenceLaterCollectionArrivalReadout.source_launch_split
      rate rewards C_star C_h source with hnone | ⟨initial, hlaunch, hrecords, hseedData⟩
  · have hlength := congrArg List.length hnone.2.1
    exact False.elim (Nat.not_lt_zero k.val (k.isLt.trans_eq hlength))
  · rcases hseedData with ⟨hc, hstate, seed, hfirst, hunoccupied, hbuffer⟩
    have hspan : start + (p.T - start) ≤ p.T := by
      have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T rate source rewards
        C_star C_h
      omega
    have hmode := ReferenceCompletePhysicalHistory.activeMode_of_launch_eq_some
      rate source rewards C_star C_h initial hlaunch
    have hfirstState : initial.coordinator = .first := by
      rw [hstate]
      exact hfirst
    have hseedClock : ReferenceCoordinatorClockDomains.clockAt
        source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
        start initial := by
      simp [ReferenceCoordinatorClockDomains.clockAt, hfirstState]
    have hrunRecords : (ReferenceActivePhysicalHorizon.run initial source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start
        (p.T - start) hspan hmode).records = records := by
      exact hrecords.symm
    have hrowInputs := ReferenceLaterCollectionArrivalReadout.sourceIndexedReadout_inputs
      rate rewards C_star C_h source k
    have hrowInputs' : record.input.rows = source.1.2 ∧
        record.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p source ∧
        record.input.rewards = rewards := by
      simpa [records, record] using hrowInputs
    have hrecordMem : record ∈
        (ReferenceActivePhysicalHorizon.run initial source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start
          (p.T - start) hspan hmode).records := by
      rw [hrunRecords]
      exact List.get_mem records k
    have hprefix := run_prefix_sourceBound initial source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start (p.T - start)
      hspan hmode hseedClock hfirstState (p.T - start) le_rfl
    have hsourceState := hprefix.2 record hrecordMem
    have hclockRun := ReferenceRunClockPreservation.run_clockAt initial source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start
      (p.T - start) hspan hmode hseedClock
    have hclockRecord := (hclockRun).2.2.2 record hrecordMem
    have hrow : record.input.row =
        source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) := by
      change record.input.rows record.input.selected = _
      rw [hrowInputs'.1, hrowInputs'.2.1]
    cases hcoord : record.output.preparation.coordinator with
    | collection payload ledger clock cutoff outcome =>
        cases outcome with
        | continuing core snapshot boundary scores =>
            have houtput : record.output = ReferenceActivePhysicalStep.step record.input := by
              exact record.output_eq
            have hprepared : (ReferenceActivePhysicalStep.prepare record.input).coordinator =
                .collection payload ledger clock cutoff
                  (.continuing core snapshot boundary scores) := by
              have hcoord' := hcoord
              rw [houtput] at hcoord'
              simpa only [ReferenceActivePhysicalStep.step] using hcoord'
            cases hinput : record.input.state.coordinator with
            | first =>
                have hfalse : False := by
                  have hdispatch := ReferenceActivePhysicalStep.dispatch_first record.input hinput
                  rw [(ReferenceActivePhysicalStep.prepare record.input).coordinator_eq,
                    hdispatch] at hprepared
                  cases hprepared
                exact hfalse.elim
            | live registers owned base =>
                have hfalse : False := by
                  cases hdispatchEq : CoordinatorRoundDispatch.dispatch
                      (.live (ReferenceActivePhysicalStep.liveInput record.input registers owned base)) with
                  | live outcome =>
                      simp [ReferenceActivePhysicalStep.prepare,
                        ReferenceActivePhysicalStep.dispatch, hinput,
                        CoordinatorRoundDispatch.dispatch] at hprepared
                      cases hprepared
                exact hfalse.elim
            | collection oldPayload oldLedger saved =>
                have hcutoffValid : 1 ≤ oldLedger.cutoff ∧ oldLedger.cutoff ≤ p.T := by
                  have hclockInput := hclockRecord.1
                  simp only [ReferenceCoordinatorClockDomains.clockAt, hinput] at hclockInput
                  exact ⟨hclockInput.2.2.1, hclockInput.2.2.2.1⟩
                simp [ReferenceActivePhysicalStep.prepare,
                  ReferenceActivePhysicalStep.dispatch, hinput, hcutoffValid] at hprepared
                injection hprepared with hpayload hledger hclock hcutoff houtcome
                subst oldPayload
                subst oldLedger
                have hstate : record.input.state.coordinator = .collection payload ledger saved := by
                  rw [hinput]
                have hsourceCutoff : FollowerCutoffScan.firstCutoff p rate.eta.val payload.sigma
                    (FollowerCutoffScan.completeRowProposalBit p rate.eta.val record.input.row) ≤
                      ledger.cutoff := by
                  simpa [sourceBound, hstate, hrow] using hsourceState
                have hclockInput :
                    ledger.sigma = payload.sigma.val + 1 ∧
                      payload.sigma.val + 1 < ledger.cutoff ∧
                      1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T ∧
                      ledger.cutoff ≤ record.input.time.val ∧
                      ledger.freezeAt = FollowerCutoffScan.gridBoundary p rate.eta.val payload.sigma ∧
                      ledger.cutoff ≤ ledger.freezeAt ∧ ledger.freezeAt ≤ p.T + 1 := by
                  simpa [ReferenceCoordinatorClockDomains.clockAt, hstate] using hclockRecord.1
                have htimeCutoff : ledger.cutoff ≤ record.input.time.val :=
                  hclockInput.2.2.2.2.1
                exact ⟨hsourceCutoff, htimeCutoff⟩
            | dagger =>
                have hfalse : False := by
                  rw [(ReferenceActivePhysicalStep.prepare record.input).coordinator_eq] at hprepared
                  simp [ReferenceActivePhysicalStep.dispatch, hinput] at hprepared
                exact hfalse.elim
        | _ => trivial
    | _ => trivial

end Bandits.Support.ReferenceCollectionCutoffSourceHistory

end
