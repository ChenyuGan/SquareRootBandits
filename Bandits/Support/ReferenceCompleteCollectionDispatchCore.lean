/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteContinuingCollectionStart

import Lean.Elab.Tactic.Omega

/-!
# Actual complete-source collection dispatch core

Sources: `sources/zip4/manuscript/appendix_a_local_protocol.tex:6-64` and
`sources/zip4/manuscript/06_interruptions.tex:9-100,246-299`.

For a retained collection input on the original complete physical suffix,
this module reconstructs the local core, current complement-score check, and
the source phase-clock start result from its actual previous output. It makes
no claim about arm-choice validity, later reconstruction, envelope bounds,
or manuscript closure.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.CoordinatorCollectionLedger
open Bandits.Support.ReferenceCollectionSegmentExtraction

namespace Bandits.Support.ReferenceCompleteCollectionDispatchCore

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

private theorem complete_suffix_member_clockAt
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length) :
    let record := (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val]'k.isLt
    ReferenceCoordinatorClockDomains.clockAt record.input.rows record.input.selected
      record.input.time.val record.input.state := by
  classical
  cases hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h with
  | none =>
      have hlength := k.isLt
      simp only [ReferenceCompletePhysicalHistory.completeSuffixRecords,
        hlaunch, dite_true, List.length_nil] at hlength
      omega
  | some active =>
      let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h
      obtain ⟨seed, hseedLaunch, hfirst, _hbank, _hdisabled, _hlearner, _hzero⟩ :=
        ReferenceCorrectedInitializationLaunch.correctedLaunch_coordinator_provenance
          rate source rewards C_star C_h
          ((ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
            rate source rewards C_star C_h).mp (by rw [hlaunch]; rfl))
      have hseedEq : seed = active := Option.some.inj (hseedLaunch.symm.trans hlaunch)
      let start := ReferenceCompletePhysicalHistory.physicalStart
        rate source rewards C_star C_h
      have hspan : start + (p.T - start) ≤ p.T := by
        have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T
          rate source rewards C_star C_h
        omega
      have hmode := ReferenceCompletePhysicalHistory.activeMode_of_launch_eq_some
        rate source rewards C_star C_h active hlaunch
      have hrecords := ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
        rate source rewards C_star C_h active hlaunch
      generalize hR : ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h = records at k ⊢
      rw [hR] at hrecords
      subst records
      have hseedClock : ReferenceCoordinatorClockDomains.clockAt source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) start active := by
        have hcoord : active.coordinator = .first := by
          rw [← hseedEq]
          exact hfirst
        simp [ReferenceCoordinatorClockDomains.clockAt, hcoord]
      have hclock := ReferenceRunClockPreservation.run_clockAt active source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
        start (p.T - start) hspan hmode hseedClock
      have hmember : (ReferenceActivePhysicalHorizon.run active source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
          start (p.T - start) hspan hmode).records[k.val]'k.isLt ∈
            (ReferenceActivePhysicalHorizon.run active source.1.2
              (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
              start (p.T - start) hspan hmode).records :=
        List.getElem_mem k.isLt
      have hrecord := hclock.2.2.2 _ hmember
      dsimp only
      rw [hrecord.2.2.1, hrecord.2.2.2.1]
      exact hrecord.1

private theorem connected_adjacent_inputs
    {initial final : ReferenceActivePhysicalStep.State p rate}
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (hconnected : ReferenceActivePhysicalHorizon.Connected initial records final)
    (k : ℕ) (hk : k < records.length) (hkpos : 0 < k) :
    (records[k - 1]'(by omega)).output.next = (records[k]'hk).input.state := by
  induction records generalizing initial final k with
  | nil => simp at hk
  | cons head tail ih =>
      have hhead : head.input.state = initial ∧
          ReferenceActivePhysicalHorizon.Connected head.output.next tail final := by
        simpa [ReferenceActivePhysicalHorizon.Connected] using hconnected
      cases k with
      | zero => omega
      | succ j =>
          have hj : j < tail.length := by simpa using hk
          by_cases hjzero : j = 0
          · subst j
            cases tail with
            | nil => simp at hj
            | cons next rest =>
                have hnext : next.input.state = head.output.next := by
                  simpa [ReferenceActivePhysicalHorizon.Connected] using hhead.2.1
                simpa using hnext.symm
          · cases j with
            | zero => contradiction
            | succ q =>
                have hrec := ih hhead.2 (q + 1) (by omega) (by omega)
                simpa using hrec

private theorem complete_suffix_member_time
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length) :
    ((ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val]'k.isLt).input.time.val =
      ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h + k.val := by
  have hvalues := ReferenceCompletePhysicalHistory.completeSuffixRecords_time_values
    rate source rewards C_star C_h
  have hk : k.val < p.T - ReferenceCompletePhysicalHistory.physicalStart
      rate source rewards C_star C_h := by
    rw [← ReferenceCompletePhysicalHistory.completeSuffixRecords_length
      rate source rewards C_star C_h]
    exact k.isLt
  have hget := congrArg (fun values : List ℕ => values[k.val]?) hvalues
  rw [List.getElem?_map, List.getElem?_eq_getElem k.isLt, Option.map_some,
    ReferenceActivePhysicalHorizon.calendar, List.getElem?_range' hk, Nat.one_mul] at hget
  exact Option.some.inj hget

private theorem livePostChoice_not_collection
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
    (base : Fin (p.m - 1) → ℕ) (started : CoordinatorPhaseClock.StartRoundResult p)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (saved : Option (Fin p.T × Bool)) :
    (ReferenceActivePhysicalStep.livePostChoice prepared registers owned base started).configuration ≠
      .collection payload ledger saved := by
  unfold ReferenceActivePhysicalStep.livePostChoice
  split
  · simp [ReferenceActivePhysicalStep.coordinatorFailure]
  · rename_i recording hrecord
    cases hservice : CoordinatorLiveServiceFinish.servicePass registers owned recording with
    | error failure => simp [ReferenceActivePhysicalStep.coordinatorFailure]
    | ok serviced =>
        cases hconfirmation : CoordinatorLocalArmChoice.confirmationUpdate registers.payload
            started.pending (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
            x.time x.row prepared.coordinatorObservation with
        | none =>
            simp [ReferenceActivePhysicalStep.coordinatorFailure]
        | some pending =>
            cases hfinish : CoordinatorPhaseClock.finishRound p rate.eta.val x.time
                started.clock pending x.row with
            | error failure =>
                  simp [hfinish, ReferenceActivePhysicalStep.coordinatorFailure]
            | ok finished =>
                simp [hfinish]

private theorem collectionPostChoice_origin
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (pre : ReferenceActivePhysicalStep.Ledger rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ)
    (targetPayload : ReferenceActivePhysicalStep.Payload rate)
    (targetLedger : ReferenceActivePhysicalStep.Ledger rate)
    (saved : Option (Fin p.T × Bool))
    (houtput : (ReferenceActivePhysicalStep.collectionPostChoice prepared payload pre
      started weights).configuration = .collection targetPayload targetLedger saved) :
    ∃ (recording : CoordinatorRecordingOperation.Output p)
      (startedLedger decoded : ReferenceActivePhysicalStep.Ledger rate)
      (bank : CoordinatorUpReception.UpDecoderBank p)
      (clockFinished : CoordinatorPhaseClock.FinishRoundResult p),
      CoordinatorRecorderComplementBridge.run
        (ReferenceActivePhysicalStep.collectionRecordingInput prepared payload started weights) =
          some recording ∧
      CoordinatorCollectionLedger.startRound pre (x.time.val + 1)
        (ReferenceActivePhysicalStep.collectionEnabled pre x.time)
        (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) =
          .success startedLedger ∧
      ((ReferenceActivePhysicalStep.receiveUp prepared startedLedger).result =
          .success (decoded, bank) ∨
        (ReferenceActivePhysicalStep.receiveUp prepared startedLedger).result =
          .rejected (decoded, bank)) ∧
      CoordinatorCollectionLedger.finishRound decoded = .success targetLedger ∧
      CoordinatorPhaseClock.finishRound p rate.eta.val x.time started.clock
        targetLedger.pending x.row = .ok clockFinished ∧
      targetPayload = payload ∧ saved = clockFinished.clock.lastProposal ∧
      (ReferenceActivePhysicalStep.collectionPostChoice prepared payload pre started weights).upDecoderBank =
        bank := by
  classical
  unfold ReferenceActivePhysicalStep.collectionPostChoice at houtput
  cases hrecord : CoordinatorRecorderComplementBridge.run
      (ReferenceActivePhysicalStep.collectionRecordingInput prepared payload started weights) with
  | none => simp [hrecord, ReferenceActivePhysicalStep.coordinatorFailure] at houtput
  | some recording =>
      let raw := CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording
      cases hstart : CoordinatorCollectionLedger.startRound pre (x.time.val + 1)
          (ReferenceActivePhysicalStep.collectionEnabled pre x.time) raw with
      | invalid => simp [hrecord, raw, hstart, ReferenceActivePhysicalStep.coordinatorFailure] at houtput
      | rejected bad => simp [hrecord, raw, hstart, ReferenceActivePhysicalStep.coordinatorFailure] at houtput
      | success startedLedger =>
          cases hcut : ReferenceActivePhysicalStep.receiveUp prepared startedLedger with
          | mk result diagnostic =>
              cases hreceive : result with
              | invalid =>
                  simp [hrecord, raw, hstart, hcut, hreceive,
                    ReferenceActivePhysicalStep.collectionFinish,
                    ReferenceActivePhysicalStep.coordinatorFailure] at houtput
              | success out =>
                  rcases out with ⟨decoded, bank⟩
                  cases hfinish : CoordinatorCollectionLedger.finishRound decoded with
                  | invalid =>
                      simp [hrecord, raw, hstart, hcut, hreceive, hfinish,
                        ReferenceActivePhysicalStep.collectionFinish,
                        ReferenceActivePhysicalStep.coordinatorFailure] at houtput
                  | rejected bad =>
                      simp [hrecord, raw, hstart, hcut, hreceive, hfinish,
                        ReferenceActivePhysicalStep.collectionFinish,
                        ReferenceActivePhysicalStep.coordinatorFailure] at houtput
                  | success ledgerFinished =>
                      cases hclock : CoordinatorPhaseClock.finishRound p rate.eta.val x.time
                          started.clock ledgerFinished.pending x.row with
                      | error failure =>
                          simp [hrecord, raw, hstart, hcut, hreceive, hfinish, hclock,
                            ReferenceActivePhysicalStep.collectionFinish,
                            ReferenceActivePhysicalStep.coordinatorFailure] at houtput
                      | ok clockFinished =>
                          have hfields : payload = targetPayload ∧
                              ledgerFinished = targetLedger ∧
                              clockFinished.clock.lastProposal = saved := by
                            simpa [hrecord, raw, hstart, hcut, hreceive, hfinish, hclock,
                              ReferenceActivePhysicalStep.collectionFinish] using houtput
                          rcases hfields with ⟨hpayload, hledger, hsaved⟩
                          subst targetLedger
                          have hreception :
                              (ReferenceActivePhysicalStep.receiveUp prepared startedLedger).result =
                                .success (decoded, bank) := by
                            rw [hcut, hreceive]
                          refine ⟨recording, startedLedger, decoded, bank, clockFinished,
                            rfl, by simpa [raw] using hstart, Or.inl hreception, hfinish, hclock,
                            hpayload.symm, hsaved.symm, by
                              simp [ReferenceActivePhysicalStep.collectionPostChoice,
                                ReferenceActivePhysicalStep.collectionFinish, hrecord, raw,
                                hstart, hcut, hreceive, hfinish, hclock]⟩
              | rejected out =>
                  rcases out with ⟨decoded, bank⟩
                  cases hfinish : CoordinatorCollectionLedger.finishRound decoded with
                  | invalid =>
                      simp [hrecord, raw, hstart, hcut, hreceive, hfinish,
                        ReferenceActivePhysicalStep.collectionFinish,
                        ReferenceActivePhysicalStep.coordinatorFailure] at houtput
                  | rejected bad =>
                      simp [hrecord, raw, hstart, hcut, hreceive, hfinish,
                        ReferenceActivePhysicalStep.collectionFinish,
                        ReferenceActivePhysicalStep.coordinatorFailure] at houtput
                  | success ledgerFinished =>
                      cases hclock : CoordinatorPhaseClock.finishRound p rate.eta.val x.time
                          started.clock ledgerFinished.pending x.row with
                      | error failure =>
                          simp [hrecord, raw, hstart, hcut, hreceive, hfinish, hclock,
                            ReferenceActivePhysicalStep.collectionFinish,
                            ReferenceActivePhysicalStep.coordinatorFailure] at houtput
                      | ok clockFinished =>
                          have hfields : payload = targetPayload ∧
                              ledgerFinished = targetLedger ∧
                              clockFinished.clock.lastProposal = saved := by
                            simpa [hrecord, raw, hstart, hcut, hreceive, hfinish, hclock,
                              ReferenceActivePhysicalStep.collectionFinish] using houtput
                          rcases hfields with ⟨hpayload, hledger, hsaved⟩
                          subst targetLedger
                          have hreception :
                              (ReferenceActivePhysicalStep.receiveUp prepared startedLedger).result =
                                .rejected (decoded, bank) := by
                            rw [hcut, hreceive]
                          refine ⟨recording, startedLedger, decoded, bank, clockFinished,
                            rfl, by simpa [raw] using hstart, Or.inr hreception, hfinish, hclock,
                            hpayload.symm, hsaved.symm, by
                              simp [ReferenceActivePhysicalStep.collectionPostChoice,
                                ReferenceActivePhysicalStep.collectionFinish, hrecord, raw,
                                hstart, hcut, hreceive, hfinish, hclock]⟩

private theorem finishRound_success_valid
    (before after : ReferenceActivePhysicalStep.Ledger rate)
    (hfinish : CoordinatorCollectionLedger.finishRound before = .success after) :
    CoordinatorCollectionLedger.validLedgerCheck after = true ∧
      after.phase = .ready := by
  have hcand := CollectionCheckedExecution.finishRound_success_candidate before after hfinish
  have hvalid : CoordinatorCollectionLedger.validLedgerCheck
      (CoordinatorCollectionLedger.finishRoundCandidate before) = true := by
    unfold CoordinatorCollectionLedger.finishRound at hfinish
    split at hfinish
    · dsimp only at hfinish
      split at hfinish
      · assumption
      · cases hfinish
    · cases hfinish
  rw [hcand]
  exact ⟨hvalid, by simp [CoordinatorCollectionLedger.finishRoundCandidate]⟩

private theorem observe_collection_postChoice_origin
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (saved : Option (Fin p.T × Bool))
    (houtput : prepared.observeCoordinator.configuration = .collection payload ledger saved) :
    ∃ (prePayload : ReferenceActivePhysicalStep.Payload rate)
      (preLedger : ReferenceActivePhysicalStep.Ledger rate)
      (started : CoordinatorPhaseClock.StartRoundResult p)
      (weights : CanonicalFastSampling.FastArm prePayload.slowSet → ℝ),
      (ReferenceActivePhysicalStep.collectionPostChoice prepared prePayload preLedger
        started weights).configuration = .collection payload ledger saved ∧
      prepared.observeCoordinator = ReferenceActivePhysicalStep.collectionPostChoice
        prepared prePayload preLedger started weights := by
  classical
  cases hcut : prepared.coordinator with
  | first outcome =>
      cases outcome with
      | choiceDomainFailure installation =>
          rw [ReferenceActivePhysicalStep.observeCoordinator_first_equation
            prepared _ hcut] at houtput
          simp [ReferenceActivePhysicalStep.DispatchCut.selection,
            ReferenceActivePhysicalStep.coordinatorFailure] at houtput
      | recorderBoundaryFailure installation =>
          rw [ReferenceActivePhysicalStep.observeCoordinator_first_equation
            prepared _ hcut] at houtput
          simp [ReferenceActivePhysicalStep.DispatchCut.selection,
            ReferenceActivePhysicalStep.coordinatorFailure] at houtput
      | choiceRejected installation =>
          rw [ReferenceActivePhysicalStep.observeCoordinator_first_equation
            prepared _ hcut] at houtput
          simp [ReferenceActivePhysicalStep.DispatchCut.selection,
            ReferenceActivePhysicalStep.coordinatorFailure] at houtput
      | chosen installation selection =>
          have heq := ReferenceActivePhysicalStep.observeCoordinator_first_equation
            prepared (.chosen installation selection) hcut
          have hsel : (ReferenceActivePhysicalStep.DispatchCut.first
              (.chosen installation selection)).selection ≠ none := by
            intro hs
            rw [heq, hs] at houtput
            simp [ReferenceActivePhysicalStep.coordinatorFailure] at houtput
          have hpost : (ReferenceActivePhysicalStep.livePostChoice prepared
              installation.registers installation.ownedRegisters
              installation.followerBaseScore installation.startRoundResult).configuration =
                .collection payload ledger saved := by
            rw [heq] at houtput
            simpa [hsel] using houtput
          exact False.elim (livePostChoice_not_collection prepared installation.registers
            installation.ownedRegisters installation.followerBaseScore
            installation.startRoundResult payload ledger saved hpost)
  | live registers owned base outcome =>
      have heq := ReferenceActivePhysicalStep.observeCoordinator_live_equation
        prepared registers owned base outcome hcut
      cases outcome with
      | clockFailure failure startEq =>
          rw [heq] at houtput
          simp [ReferenceActivePhysicalStep.DispatchCut.selection,
            ReferenceActivePhysicalStep.coordinatorFailure] at houtput
      | initializerFailure dispatched startEq checked checkedEq =>
          rw [heq] at houtput
          simp [ReferenceActivePhysicalStep.DispatchCut.selection,
            ReferenceActivePhysicalStep.coordinatorFailure] at houtput
      | localFailure dispatched startEq reason =>
          rw [heq] at houtput
          simp [ReferenceActivePhysicalStep.DispatchCut.selection,
            ReferenceActivePhysicalStep.coordinatorFailure] at houtput
      | cutoffChosen dispatched startEq newLedger initEq ledgerEq initDomain
          cutoffClock cutoffPending noAssignment selection =>
          have hsel : (ReferenceActivePhysicalStep.DispatchCut.live registers owned base
              (.cutoffChosen dispatched startEq newLedger initEq ledgerEq initDomain
                cutoffClock cutoffPending noAssignment selection)).selection ≠ none := by
            intro hs
            rw [heq, hs] at houtput
            simp [ReferenceActivePhysicalStep.coordinatorFailure] at houtput
          have hpost : (ReferenceActivePhysicalStep.collectionPostChoice prepared
              registers.payload (ReferenceActivePhysicalStep.sharedLedger newLedger)
              dispatched.startResult (ReferenceActivePhysicalStep.liveRegistersAt
                registers x.time).complementWeights).configuration =
                  .collection payload ledger saved := by
            rw [heq] at houtput
            simpa [hsel] using houtput
          exact ⟨registers.payload, ReferenceActivePhysicalStep.sharedLedger newLedger,
            dispatched.startResult,
            (ReferenceActivePhysicalStep.liveRegistersAt registers x.time).complementWeights,
            hpost, by
              rw [heq]
              simp [hsel]⟩
      | continuingChosen dispatched startEq continuation selection =>
          have hsel : (ReferenceActivePhysicalStep.DispatchCut.live registers owned base
              (.continuingChosen dispatched startEq continuation selection)).selection ≠ none := by
            intro hs
            rw [heq, hs] at houtput
            simp [ReferenceActivePhysicalStep.coordinatorFailure] at houtput
          have hpost : (ReferenceActivePhysicalStep.livePostChoice prepared
              (ReferenceActivePhysicalStep.liveRegistersAt registers x.time)
              (ReferenceActivePhysicalStep.liveOwnedAt registers owned x.time) base
              dispatched.startResult).configuration = .collection payload ledger saved := by
            rw [heq] at houtput
            simpa [hsel] using houtput
          exact False.elim (livePostChoice_not_collection prepared
            (ReferenceActivePhysicalStep.liveRegistersAt registers x.time)
            (ReferenceActivePhysicalStep.liveOwnedAt registers owned x.time) base
            dispatched.startResult payload ledger saved hpost)
  | collection prePayload preLedger clock cutoff outcome =>
      have heq := ReferenceActivePhysicalStep.observeCoordinator_collection_equation
        prepared prePayload preLedger clock cutoff outcome hcut
      cases outcome with
      | clockFailure failure startEq =>
          rw [heq] at houtput
          simp [ReferenceActivePhysicalStep.DispatchCut.selection,
            ReferenceActivePhysicalStep.coordinatorFailure] at houtput
      | localFailure started startEq coreInvalid reason =>
          rw [heq] at houtput
          simp [ReferenceActivePhysicalStep.DispatchCut.selection,
            ReferenceActivePhysicalStep.coordinatorFailure] at houtput
      | coreFailure core started startEq reason =>
          rw [heq] at houtput
          simp [ReferenceActivePhysicalStep.DispatchCut.selection,
            ReferenceActivePhysicalStep.coordinatorFailure] at houtput
      | continuing core snapshot boundary scores =>
          have hsel : (ReferenceActivePhysicalStep.DispatchCut.collection prePayload
              preLedger clock cutoff (.continuing core snapshot boundary scores)).selection ≠ none := by
            intro hs
            rw [heq, hs] at houtput
            simp [ReferenceActivePhysicalStep.coordinatorFailure] at houtput
          let sourceInput := ReferenceActivePhysicalStep.collectionInput x prePayload
            preLedger clock cutoff
          let actualWeights := CoordinatorCollectionInteractive.PreObservationInputs.weights
            sourceInput snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq
          have hpost : (ReferenceActivePhysicalStep.collectionPostChoice prepared prePayload
              preLedger snapshot.clockStarted actualWeights).configuration =
                .collection payload ledger saved := by
            rw [heq] at houtput
            simpa [hsel, sourceInput, actualWeights] using houtput
          exact ⟨prePayload, preLedger, snapshot.clockStarted, actualWeights, hpost, by
            rw [heq]
            simp [hsel, sourceInput, actualWeights]⟩
      | laterReconstructionFailure core consistent started startEq instruction assignmentEq
          failure laterEq =>
          rw [heq] at houtput
          simp [ReferenceActivePhysicalStep.DispatchCut.selection,
            ReferenceActivePhysicalStep.coordinatorFailure] at houtput
      | laterPrefixFailure core consistent started startEq instruction assignmentEq arm failure
          laterEq =>
          rw [heq] at houtput
          simp [ReferenceActivePhysicalStep.DispatchCut.selection,
            ReferenceActivePhysicalStep.coordinatorFailure] at houtput
      | laterOrientationFailure core consistent started startEq instruction assignmentEq set laterEq =>
          rw [heq] at houtput
          simp [ReferenceActivePhysicalStep.DispatchCut.selection,
            ReferenceActivePhysicalStep.coordinatorFailure] at houtput
      | laterChoiceFailure core consistent started startEq instruction assignmentEq output consistency
          clockData installation reason =>
          rw [heq] at houtput
          simp [ReferenceActivePhysicalStep.DispatchCut.selection,
            ReferenceActivePhysicalStep.coordinatorFailure] at houtput
      | laterChosen core consistent started startEq instruction assignmentEq output consistency
          clockData installation selection =>
          have hsel : (ReferenceActivePhysicalStep.DispatchCut.collection prePayload
              preLedger clock cutoff (.laterChosen core consistent started startEq instruction
                assignmentEq output consistency clockData installation selection)).selection ≠ none := by
            intro hs
            rw [heq, hs] at houtput
            simp [ReferenceActivePhysicalStep.coordinatorFailure] at houtput
          have hpost : (ReferenceActivePhysicalStep.livePostChoice prepared
              installation.registers installation.ownedRegisters
              installation.retainedBaseScore started).configuration = .collection payload ledger saved := by
            rw [heq] at houtput
            simpa [hsel] using houtput
          exact False.elim (livePostChoice_not_collection prepared installation.registers
            installation.ownedRegisters installation.retainedBaseScore started payload ledger saved hpost)
  | invalidCollectionCutoff =>
      simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator, hcut,
        ReferenceActivePhysicalStep.DispatchCut.selection] at houtput
      cases houtput
  | dagger =>
      simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator, hcut,
        ReferenceActivePhysicalStep.DispatchCut.selection] at houtput

private theorem actual_previous_collection_postChoice
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (saved : Option (Fin p.T × Bool))
    (hstate : ((ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val]'k.isLt).input.state.coordinator =
        .collection payload ledger saved) :
    ∃ (previous : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (prePayload : ReferenceActivePhysicalStep.Payload rate)
      (preLedger : ReferenceActivePhysicalStep.Ledger rate)
      (started : CoordinatorPhaseClock.StartRoundResult p)
      (weights : CanonicalFastSampling.FastArm prePayload.slowSet → ℝ)
      (recording : CoordinatorRecordingOperation.Output p)
      (startedLedger decoded : ReferenceActivePhysicalStep.Ledger rate)
      (bank : CoordinatorUpReception.UpDecoderBank p)
      (clockFinished : CoordinatorPhaseClock.FinishRoundResult p),
      previous.output.next =
        ((ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h)[k.val]'k.isLt).input.state ∧
      previous.input.time.val + 1 =
        ((ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h)[k.val]'k.isLt).input.time.val ∧
      CoordinatorRecorderComplementBridge.run
        (ReferenceActivePhysicalStep.collectionRecordingInput
          (ReferenceActivePhysicalStep.prepare previous.input) prePayload started weights) =
            some recording ∧
      CoordinatorCollectionLedger.startRound preLedger (previous.input.time.val + 1)
        (ReferenceActivePhysicalStep.collectionEnabled preLedger previous.input.time)
        (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) =
          .success startedLedger ∧
      ((ReferenceActivePhysicalStep.receiveUp (ReferenceActivePhysicalStep.prepare previous.input)
        startedLedger).result = .success (decoded, bank) ∨
       (ReferenceActivePhysicalStep.receiveUp (ReferenceActivePhysicalStep.prepare previous.input)
        startedLedger).result = .rejected (decoded, bank)) ∧
      CoordinatorCollectionLedger.finishRound decoded = .success ledger ∧
      CoordinatorPhaseClock.finishRound p rate.eta.val previous.input.time started.clock
        ledger.pending previous.input.row = .ok clockFinished ∧
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val]'k.isLt).input.state.upDecoderBank = bank ∧
      payload = prePayload ∧ saved = clockFinished.clock.lastProposal := by
  classical
  let records := ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h
  let current := records[k.val]'k.isLt
  have hbirth := ReferenceAssignmentRetainedBirthProvenance.complete_coordinator_retained_birth
    rate rewards C_star C_h source k
  dsimp only at hbirth
  rw [hstate] at hbirth
  rcases hbirth with ⟨⟨_birth, hbval, _hbproof, _hbase⟩,
    _hassignment, _hsigma, _hcutoff⟩
  have hkpos : 0 < k.val := by omega
  cases hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h with
  | none =>
      have hlength := k.isLt
      simp only [ReferenceCompletePhysicalHistory.completeSuffixRecords,
        hlaunch, dite_true, List.length_nil] at hlength
      omega
  | some active =>
      have hprevLt : k.val - 1 < records.length := by
        have hklt : k.val < records.length := k.isLt
        omega
      let previousIndex : Fin records.length := ⟨k.val - 1, hprevLt⟩
      let previous : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) :=
        records[previousIndex.val]'previousIndex.isLt
      have hcurrentTime := complete_suffix_member_time rate rewards C_star C_h source k
      have hpreviousTime := complete_suffix_member_time rate rewards C_star C_h source previousIndex
      have htime : previous.input.time.val + 1 = current.input.time.val := by
        have htc : current.input.time.val =
            ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h + k.val := by
          simpa [current, records] using hcurrentTime
        have htp : previous.input.time.val =
            ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h + previousIndex.val := by
          simpa [previous, previousIndex, records] using hpreviousTime
        have hi : previousIndex.val + 1 = k.val := by
          simp [previousIndex]
          omega
        omega
      have hconnected := ReferenceCompletePhysicalHistory.completeSuffix_connected_on_launch
        rate source rewards C_star C_h active hlaunch
      have hadj := connected_adjacent_inputs records hconnected k.val k.isLt hkpos
      have hnext : previous.output.next = current.input.state := by
        simpa [previous, previousIndex, current, records] using hadj
      have houtput : previous.output.coordinator.configuration = .collection payload ledger saved := by
        calc
          previous.output.coordinator.configuration =
              (ReferenceActivePhysicalStep.prepare previous.input).observeCoordinator.configuration := by
            rw [previous.output_eq]
            rfl
          _ = previous.output.next.coordinator := by
            rw [previous.output_eq]
            exact (ReferenceActivePhysicalStep.step_next_fields previous.input).1.symm
          _ = current.input.state.coordinator := congrArg
            ReferenceActivePhysicalStep.State.coordinator hnext
          _ = .collection payload ledger saved := hstate
      have hbank : previous.output.coordinator.upDecoderBank = current.input.state.upDecoderBank := by
        calc
          previous.output.coordinator.upDecoderBank = previous.output.next.upDecoderBank := by
            rw [previous.output_eq]
            exact (ReferenceActivePhysicalStep.step_next_fields previous.input).2.1.symm
          _ = current.input.state.upDecoderBank := congrArg
            ReferenceActivePhysicalStep.State.upDecoderBank hnext
      have hobs : (ReferenceActivePhysicalStep.prepare previous.input).observeCoordinator.configuration =
          .collection payload ledger saved := by
        calc
          _ = previous.output.coordinator.configuration := by
            rw [previous.output_eq]
            rfl
          _ = .collection payload ledger saved := houtput
      obtain ⟨prePayload, preLedger, started, weights, hpost, hroute⟩ :=
        observe_collection_postChoice_origin (ReferenceActivePhysicalStep.prepare previous.input)
          payload ledger saved hobs
      obtain ⟨recording, startedLedger, decoded, bank, clockFinished,
        hrecord, hstart, hreceive, hfinish, hclock, hpayload, hsaved, hpostBank⟩ :=
        collectionPostChoice_origin (ReferenceActivePhysicalStep.prepare previous.input)
          prePayload preLedger started weights payload ledger saved hpost
      have hcurrentBank : current.input.state.upDecoderBank = bank := by
        calc
          current.input.state.upDecoderBank = previous.output.coordinator.upDecoderBank := hbank.symm
          _ = (ReferenceActivePhysicalStep.prepare previous.input).observeCoordinator.upDecoderBank := by
            rw [previous.output_eq]
            rfl
          _ = (ReferenceActivePhysicalStep.collectionPostChoice
                (ReferenceActivePhysicalStep.prepare previous.input) prePayload preLedger started weights).upDecoderBank :=
              congrArg (fun observation : ReferenceActivePhysicalStep.CoordinatorObservation p rate =>
                observation.upDecoderBank) hroute
          _ = bank := hpostBank
      refine ⟨previous, prePayload, preLedger, started, weights, recording,
        startedLedger, decoded, bank, clockFinished, hnext, htime, hrecord, hstart,
        hreceive, hfinish, hclock, hcurrentBank, hpayload, hsaved⟩

/-- Every queried collection state in the original complete suffix carries a
valid local core and the source clock's literal START result. Both nonempty
continuation and empty-pending later-start results retain their exact command
fields; the source is the actual retained predecessor and its checked
post-choice operations. -/
theorem complete_collection_dispatch_core
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p) :
    let records := ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h
    ∀ (k : Fin records.length),
      let record := records[k.val]'k.isLt
      let x := record.input
      ∀ (payload : ReferenceActivePhysicalStep.Payload rate)
        (ledger : ReferenceActivePhysicalStep.Ledger rate)
        (saved : Option (Fin p.T × Bool)),
        x.state.coordinator = .collection payload ledger saved →
        ∃ u : Fin p.T, u.val + 1 = ledger.cutoff ∧
          let input := ReferenceActivePhysicalStep.collectionInput x payload ledger
            (ReferenceActivePhysicalStep.collectionClock payload ledger saved u) u
          CoordinatorRoundDispatch.CollectionCoreValid input ∧
          CoordinatorRoundDispatch.collectionCurrentScoresCheck input = true ∧
          ∃ started : CoordinatorPhaseClock.StartRoundResult p,
            CoordinatorPhaseClock.startRound p rate.eta.val x.time input.clock
              ledger.pending = .ok started ∧
            (ledger.pending.Nonempty → started.clock = input.clock ∧
              started.pending = ledger.pending ∧ started.ledgerCommand = none ∧
              started.assignmentStart = none) ∧
            (ledger.pending = ∅ → ∃ assignment,
              started.assignmentStart = some assignment ∧ assignment.time = x.time) := by
  classical
  dsimp only
  intro k
  let records := ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h
  let record := records[k.val]'k.isLt
  let x := record.input
  intro payload ledger saved hstate
  change x.state.coordinator = .collection payload ledger saved at hstate
  obtain ⟨previous, prePayload, preLedger, started, weights, recording,
    startedLedger, decoded, bank, clockFinished, hnext, htime, hrecord, hstart,
    hreceive, hfinish, hclockFinish, hbank, hpayload, hsaved⟩ :=
    actual_previous_collection_postChoice rate rewards C_star C_h source k
      payload ledger saved hstate
  have hbirth := ReferenceAssignmentRetainedBirthProvenance.complete_coordinator_retained_birth
    rate rewards C_star C_h source k
  dsimp only at hbirth
  rw [hstate] at hbirth
  rcases hbirth with ⟨_birth, hassignment, hsigma, _hcutoff⟩
  have hfinishFacts := finishRound_success_valid decoded ledger hfinish
  have hfinishChron := CollectionCheckedExecution.finishRound_success_chronology
    decoded ledger hfinish
  have hcutoffBounds : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T := by
    have hcheck := hfinishFacts.1
    simp [CoordinatorCollectionLedger.validLedgerCheck] at hcheck
    omega
  let u : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
  have hu : u.val + 1 = ledger.cutoff := by
    simp [u]
    omega
  have hucut : u.val = ledger.cutoff - 1 := by omega
  have hclockAt := complete_suffix_member_clockAt rate rewards C_star C_h source k
  obtain ⟨hparam, hclockValid, hstartTime⟩ :=
    ReferenceCollectionClockPreservation.collection_clock_fields
      payload ledger saved hstate hclockAt u hucut
  have hreceiverNoninvalid :
      (ReferenceActivePhysicalStep.receiveUp
        (ReferenceActivePhysicalStep.prepare previous.input) startedLedger).result ≠ .invalid := by
    intro hbad
    rcases hreceive with hsuccess | hrejected
    · rw [hbad] at hsuccess
      cases hsuccess
    · rw [hbad] at hrejected
      cases hrejected
  have hreceiverInput := ReferenceCollectionSegmentExtraction.receiveUp_input_check
    previous.input startedLedger hreceiverNoninvalid
  have hfiltered :
      ReferenceUpReception.receiveUpFilteredAtRow rate previous.input.row
        (ReferenceActivePhysicalStep.upInputs
          (ReferenceActivePhysicalStep.prepare previous.input) startedLedger)
        previous.input.time
        ((ReferenceActivePhysicalStep.prepare previous.input).followers.followers
          (ReferenceActivePhysicalStep.upSenderIndex previous.input))
        ((ReferenceActivePhysicalStep.prepare previous.input).follower_alignment _).1
        ((ReferenceActivePhysicalStep.prepare previous.input).follower_alignment _).2.1
        ((ReferenceActivePhysicalStep.prepare previous.input).follower_alignment _).2.2.1 rfl =
          .success (decoded, bank) ∨
      ReferenceUpReception.receiveUpFilteredAtRow rate previous.input.row
        (ReferenceActivePhysicalStep.upInputs
          (ReferenceActivePhysicalStep.prepare previous.input) startedLedger)
        previous.input.time
        ((ReferenceActivePhysicalStep.prepare previous.input).followers.followers
          (ReferenceActivePhysicalStep.upSenderIndex previous.input))
        ((ReferenceActivePhysicalStep.prepare previous.input).follower_alignment _).1
        ((ReferenceActivePhysicalStep.prepare previous.input).follower_alignment _).2.1
        ((ReferenceActivePhysicalStep.prepare previous.input).follower_alignment _).2.2.1 rfl =
          .rejected (decoded, bank) := by
    simpa [ReferenceActivePhysicalStep.receiveUp] using hreceive
  have hbankWellFormed := ReferenceUpReception.receiveUpFilteredAtRow_bank_wellFormed
    rate previous.input.row
    (ReferenceActivePhysicalStep.upInputs
      (ReferenceActivePhysicalStep.prepare previous.input) startedLedger)
    previous.input.time
    ((ReferenceActivePhysicalStep.prepare previous.input).followers.followers
      (ReferenceActivePhysicalStep.upSenderIndex previous.input))
    ((ReferenceActivePhysicalStep.prepare previous.input).follower_alignment _).1
    ((ReferenceActivePhysicalStep.prepare previous.input).follower_alignment _).2.1
    ((ReferenceActivePhysicalStep.prepare previous.input).follower_alignment _).2.2.1
    rfl hreceiverInput (decoded, bank) hfiltered
  have hdecodedEq := ReferenceCollectionSegmentExtraction.receiveUp_decode_result
    previous.input startedLedger
  have hdecodedCursor : decoded.cursor = startedLedger.cursor := by
    have hcursorBehavior := CollectionCheckedExecution.decodeUp_cursor_behavior
      startedLedger (ReferenceActivePhysicalStep.upSenderIndex previous.input)
      (ReferenceCollectionSegmentExtraction.effectiveParse previous.input startedLedger)
    rcases hreceive with hsuccess | hrejected
    · rw [hsuccess] at hdecodedEq
      rw [hdecodedEq] at hcursorBehavior
      exact hcursorBehavior.1
    · rw [hrejected] at hdecodedEq
      rw [hdecodedEq] at hcursorBehavior
      exact hcursorBehavior.1
  have hstartCursor := CollectionCheckedExecution.startRound_success_cursor
    preLedger startedLedger (previous.input.time.val + 1)
    (ReferenceActivePhysicalStep.collectionEnabled preLedger previous.input.time)
    (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) hstart
  have htimeLocal : previous.input.time.val + 1 = x.time.val := by
    simpa [records, record, x] using htime
  have hledgerCursor : ledger.cursor = x.time.val + 1 := by
    calc
      ledger.cursor = decoded.cursor + 1 := hfinishChron.1
      _ = startedLedger.cursor + 1 := by rw [hdecodedCursor]
      _ = (previous.input.time.val + 1) + 1 := by rw [hstartCursor]
      _ = x.time.val + 1 := by rw [htimeLocal]
  let clock := ReferenceActivePhysicalStep.collectionClock payload ledger saved u
  let input := ReferenceActivePhysicalStep.collectionInput x payload ledger clock u
  have hcore : CoordinatorRoundDispatch.CollectionCoreValid input := {
    payload_n_eq := ReferenceActivePhysicalStep.payload_n_eq payload
    ledger_valid := by
      simpa [input, ReferenceActivePhysicalStep.collectionInput,
        CoordinatorCollectionLedger.validLedger] using hfinishFacts.1
    ledger_ready := hfinishFacts.2
    assignment_eq := fun i => by
      simpa [input, ReferenceActivePhysicalStep.collectionInput] using
        congrFun hassignment i
    base_score_eq := rfl
    clock_parameter_valid := hparam
    clock_registers_valid := hclockValid
    clock_start_time_valid := by simpa [input] using hstartTime
    clock_sigma_eq := by rfl
    clock_cutoff_eq := by rfl
    ledger_sigma_eq := by
      simpa [input, ReferenceActivePhysicalStep.collectionInput,
        CoordinatorRecorderComplementBridge.sourceStart] using hsigma
    ledger_cutoff_eq := by
      simpa [input, ReferenceActivePhysicalStep.collectionInput,
        CoordinatorCollectionUpRoundStep.sourceCutoff] using hu.symm
    ledger_freeze_eq := by rfl
    ledger_cursor_eq := by
      simpa [input, ReferenceActivePhysicalStep.collectionInput,
        CoordinatorCollectionUpRoundStep.sourceRound] using hledgerCursor
    decoder_bank_valid := by
      have hinBank : input.upDecoderBank = bank := by
        simpa [input, ReferenceActivePhysicalStep.collectionInput] using hbank
      apply (CoordinatorUpReception.decoderBankCheck_eq_true_iff p _).2
      rw [hinBank]
      exact hbankWellFormed }
  have hmassRoot := ReferenceCompleteCoordinatorMass.complete_coordinator_input_output_mass
    rate rewards C_star C_h source
  dsimp only at hmassRoot
  have hmass := (hmassRoot k).1
  unfold ReferenceCompleteCoordinatorMass.coordinatorInputMass at hmass
  rw [hstate] at hmass
  have hscores : CoordinatorRoundDispatch.collectionCurrentScoresCheck input = true := by
    apply (CoordinatorRoundDispatch.collectionCurrentScoresCheck_iff input hcore).2
    intro arm hnotSlow
    obtain ⟨cut, hcut, current, hcurrent⟩ :=
      CoordinatorCollectionUpRoundStep.complementRegisters_known ledger payload
        hcore.ledger_valid hcore.assignment_eq arm hnotSlow
    rw [CoordinatorRoundDispatch.collection_complementCurrentScore_eq
      input hcore arm hnotSlow cut hcut]
    have hmassBound : cut.score + ledger.increment arm + current.queue ≤
        x.time.val * D p := by
      simpa [records, record, x] using (hmass arm cut current hcut hcurrent).1
    have htimeBound : x.time.val ≤ p.T := by omega
    have hscoreTime : cut.score + ledger.increment arm ≤ x.time.val * D p := by omega
    have htimeProduct : x.time.val * D p ≤ p.T * D p :=
      Nat.mul_le_mul_right (D p) htimeBound
    exact hscoreTime.trans htimeProduct
  have hcall := ReferenceCollectionClockPreservation.collection_clock_call
    payload ledger saved hstate hclockAt u hucut
  obtain ⟨result, hstartClock⟩ := hcall
  have hclockAndTime := hstartTime
  have hut : u.val ≤ x.time.val := hclockAndTime.2
  by_cases hpending : ledger.pending.Nonempty
  · have hknown := CoordinatorPhaseClock.startRound_collection_pending
      p rate.eta.val x.time payload.sigma u clock ledger.pending
      hparam hclockValid rfl rfl hut (Finset.nonempty_iff_ne_empty.mp hpending)
    have hresult : result = {
        clock := clock
        gridDomain := CoordinatorPhaseClock.clockRegistersValid_gridDomain
          p rate.eta.val clock hclockValid
        pending := ledger.pending, ledgerCommand := none, assignmentStart := none } :=
      Except.ok.inj (hstartClock.symm.trans hknown)
    refine ⟨u, hu, hcore, hscores, result, hstartClock, ?_, ?_⟩
    · intro _
      rw [hresult]
      exact ⟨rfl, rfl, rfl, rfl⟩
    · intro hempty
      exact False.elim ((Finset.nonempty_iff_ne_empty.mp hpending) hempty)
  · have hempty : ledger.pending = ∅ := Finset.not_nonempty_iff_eq_empty.mp hpending
    have hgrid : CoordinatorPhaseClock.newGridBoundaryValid p x.time
        (FollowerCutoffScan.gridBoundary p rate.eta.val x.time) := by
      simpa [CoordinatorPhaseClock.newGridBoundaryValid,
        FollowerCutoffScan.calendarRound] using
        FollowerCutoffScan.gridBoundary_bounds p rate.eta.val rate.eta.property
          rate.sourceCap x.time
    have hemptyResult := CoordinatorPhaseClock.startRound_collection_empty
      p rate.eta.val x.time payload.sigma u clock hparam hclockValid rfl rfl hut hgrid
    have hstartClockEmpty := hstartClock
    rw [hempty] at hstartClockEmpty
    have hresult : result = {
        clock := {
          sigma := some x.time, u := none
          g := FollowerCutoffScan.gridBoundary p rate.eta.val x.time
          lastProposal := clock.lastProposal }
        gridDomain := hgrid, pending := Finset.univ, ledgerCommand := none
        assignmentStart := some ⟨x.time,
          CoordinatorPhaseClock.classifyAssignmentStart clock.sigma x.time clock.g⟩ } :=
      Except.ok.inj (hstartClockEmpty.symm.trans hemptyResult)
    refine ⟨u, hu, hcore, hscores, result, hstartClock, ?_, ?_⟩
    · intro hp
      exact False.elim (hpending hp)
    · intro _
      rw [hresult]
      exact ⟨⟨x.time, CoordinatorPhaseClock.classifyAssignmentStart clock.sigma x.time clock.g⟩,
        rfl, rfl⟩

end Bandits.Support.ReferenceCompleteCollectionDispatchCore

end
