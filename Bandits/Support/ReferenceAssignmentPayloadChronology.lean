/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceLaterInstallationProvenance

/-!
# Assignment payload chronology on actual finite runs

The source specifies the complete assignment handover record and its DOWN
fields in `sources/zip4/manuscript/05_binary_transport.tex:60-68`. The same
assignment remains live until cutoff, and its DOWN words continue during UP
collection, as stated in `sources/zip4/manuscript/06_interruptions.tex:41-70,273-282,327-348`.

This module follows only the accepted finite physical horizon and its literal
one-round transition. Selection-time word claims retain the actual selected
view and the pending DOWN sender branch as explicit premises. No equality with
a moving collection queue or physical replay queue is asserted here.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceAssignmentPayloadPersistence
open Bandits.Support.ReferenceDownReception
open Bandits.Support.CoordinatorLocalArmChoice

namespace Bandits.Support.ReferenceAssignmentPayloadChronology

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput

variable {p : Parameters} {rate : RateInput p}

/-- A retained actual coordinator selection encodes its DOWN word on the
selected pending DOWN sender branch. The branch premise is exactly the local
channel condition; no claim is made that it holds on every physical slot. -/
theorem actualSelection_expectedDownFlatWord
    (record : RoundRecord (p := p) (rate := rate))
    (selected : Selection record.input)
    (hselected : record.output.preparation.coordinator.selection = some selected)
    (i : ActiveRoundActions.Follower p.m)
    (hbranch : selectedDownSenderBranch selected.view i
      record.input.row record.input.time) :
    expectedDownFlatWord (some selected.view) i record.input.row record.input.time =
        some (storedDownFlatWord selected.view.payload i) ∧
      selectedPayload record = some selected.view.payload := by
  have hprojection : selectedPayload record = some selected.view.payload := by
    unfold selectedPayload
    rw [hselected]
    rfl
  exact ⟨Selection.expected_down_word selected i hbranch, hprojection⟩

/-- If an actual selected view carries a known assignment payload, the
expected DOWN word is the original word encoded by that payload. The explicit
sender branch remains the exact channel condition for a defined word. -/
theorem actualSelection_expectedDownFlatWord_of_payload_eq
    (record : RoundRecord (p := p) (rate := rate))
    (selected : Selection record.input)
    (hselected : record.output.preparation.coordinator.selection = some selected)
    (payload : Payload rate) (hpayload : selected.view.payload = payload)
    (i : ActiveRoundActions.Follower p.m)
    (hbranch : selectedDownSenderBranch selected.view i
      record.input.row record.input.time) :
    expectedDownFlatWord (some selected.view) i record.input.row record.input.time =
        some (storedDownFlatWord payload i) ∧
      selectedPayload record = some payload := by
  obtain ⟨hword, hprojection⟩ :=
    actualSelection_expectedDownFlatWord record selected hselected i hbranch
  exact ⟨by simpa [hpayload] using hword,
    by simpa [hpayload] using hprojection⟩

/-- The actual selected-payload projection reads the payload in the retained
choice view, not a separately supplied sender word. -/
theorem selectedPayload_eq_of_actualSelection
    (record : RoundRecord (p := p) (rate := rate))
    (selected : Selection record.input)
    (hselected : record.output.preparation.coordinator.selection = some selected) :
    selectedPayload record = some selected.view.payload := by
  unfold selectedPayload
  rw [hselected]
  rfl

/-- Whole DOWN records are fixed whenever the whole assignment payload is
fixed. This preserves every encoded field, including its original queue seed. -/
theorem downRecord_eq_of_payload_eq
    (left right : Payload rate) (hpayload : left = right)
    (i : ActiveRoundActions.Follower p.m) :
    left.downRecord i = right.downRecord i := by
  cases hpayload
  rfl

/-- If the literal computed dispatcher has no successful choice view, the
one-round transition stores no payload. This covers dispatch and choice
failures, malformed cutoffs, and the absorbing dagger branch. -/
theorem actualRecord_next_storedPayload_none_of_no_selection
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hnone : record.output.preparation.coordinator.selection = none) :
    storedPayload record.output.next.coordinator = none := by
  have hprepared : record.output.preparation = prepare record.input := by
    rw [record.output_eq]
    rfl
  have hnone' : (prepare record.input).coordinator.selection = none := by
    simpa [hprepared] using hnone
  rw [record.output_eq]
  change storedPayload (prepare record.input).observeCoordinator.configuration = none
  unfold PreparedRound.observeCoordinator
  simp only [dif_pos hnone']
  cases (prepare record.input).coordinator with
  | dagger => rfl
  | first outcome => simp [coordinatorFailure, storedPayload]
  | live registers owned base outcome => simp [coordinatorFailure, storedPayload]
  | collection payload ledger clock cutoff outcome =>
      simp [coordinatorFailure, storedPayload]
  | invalidCollectionCutoff => simp [coordinatorFailure, storedPayload]

/-- The sole actual one-round record for a supplied physical input. Its output
is the accepted transition itself, rather than a separately chosen outcome. -/
def actualStepRecord (x : ReferenceActivePhysicalStep.RoundInput p rate) :
    ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) :=
  ⟨x, ReferenceActivePhysicalStep.step x, rfl⟩

/-- One actual physical step either drops its stored payload, retains the
whole old payload, or stores a payload born in this very dispatch. The birth
cases are exactly the first chosen install and the later chosen constructor;
all checked failures and malformed cutoffs are included. -/
theorem actualStep_payload_classification
    (x : ReferenceActivePhysicalStep.RoundInput p rate) :
    storedPayload (ReferenceActivePhysicalStep.step x).next.coordinator = none ∨
      (∃ old : Payload rate,
        storedPayload x.state.coordinator = some old ∧
        storedPayload (ReferenceActivePhysicalStep.step x).next.coordinator = some old) ∨
      (∃ fresh : Payload rate,
        InstallationBirth (actualStepRecord x) fresh ∧
        storedPayload (ReferenceActivePhysicalStep.step x).next.coordinator = some fresh) := by
  classical
  cases hstate : x.state.coordinator with
  | first =>
      have hfirst := ReferenceActivePhysicalStep.dispatch_first x hstate
      cases hdispatch : CoordinatorRoundDispatch.dispatchFirst
          (ReferenceActivePhysicalStep.firstInput x) with
      | choiceDomainFailure installed =>
          have hnone : (actualStepRecord x).output.preparation.coordinator.selection = none := by
            simp [actualStepRecord, ReferenceActivePhysicalStep.step,
              ReferenceActivePhysicalStep.prepare, hfirst, hdispatch,
              ReferenceActivePhysicalStep.DispatchCut.selection]
          exact Or.inl (actualRecord_next_storedPayload_none_of_no_selection
            (actualStepRecord x) hnone)
      | recorderBoundaryFailure installed =>
          have hnone : (actualStepRecord x).output.preparation.coordinator.selection = none := by
            simp [actualStepRecord, ReferenceActivePhysicalStep.step,
              ReferenceActivePhysicalStep.prepare, hfirst, hdispatch,
              ReferenceActivePhysicalStep.DispatchCut.selection]
          exact Or.inl (actualRecord_next_storedPayload_none_of_no_selection
            (actualStepRecord x) hnone)
      | choiceRejected installed =>
          have hnone : (actualStepRecord x).output.preparation.coordinator.selection = none := by
            simp [actualStepRecord, ReferenceActivePhysicalStep.step,
              ReferenceActivePhysicalStep.prepare, hfirst, hdispatch,
              ReferenceActivePhysicalStep.DispatchCut.selection]
          exact Or.inl (actualRecord_next_storedPayload_none_of_no_selection
            (actualStepRecord x) hnone)
      | chosen installed selected =>
          have htime := ReferenceAssignmentPayloadPersistence.firstChosen_payload_time
            x installed selected hdispatch
          have hclock := ReferenceActivePhysicalStep.dispatchFirst_chosen_time
            x installed selected hdispatch
          have htail := ReferenceAssignmentPayloadPersistence.livePostChoice_payload_frame
            (ReferenceActivePhysicalStep.prepare x) installed.registers installed.ownedRegisters
            installed.followerBaseScore installed.startRoundResult
          have hcut : ReferenceActivePhysicalStep.dispatch x =
              .first (.chosen installed selected) := by
            rw [hfirst, hdispatch]
          have hpreparedCut : (ReferenceActivePhysicalStep.prepare x).coordinator =
              .first (.chosen installed selected) := hcut
          have hselection : (ReferenceActivePhysicalStep.prepare x).coordinator.selection ≠ none := by
            simp [hpreparedCut, ReferenceActivePhysicalStep.DispatchCut.selection,
              ReferenceActivePhysicalStep.selectionAt, hclock]
          have hnext :
              storedPayload (ReferenceActivePhysicalStep.step x).next.coordinator = none ∨
                storedPayload (ReferenceActivePhysicalStep.step x).next.coordinator =
                  some installed.registers.payload := by
            change storedPayload (ReferenceActivePhysicalStep.prepare x).observeCoordinator.configuration = none ∨
              storedPayload (ReferenceActivePhysicalStep.prepare x).observeCoordinator.configuration =
                some installed.registers.payload
            unfold ReferenceActivePhysicalStep.PreparedRound.observeCoordinator
            rw [dif_neg hselection, hpreparedCut]
            exact htail
          have hbirth : InstallationBirth (actualStepRecord x)
              installed.registers.payload := by
            unfold InstallationBirth actualStepRecord
            simp only [ReferenceActivePhysicalStep.step, ReferenceActivePhysicalStep.prepare,
              hfirst, hdispatch]
            exact ⟨rfl, htime⟩
          rcases hnext with hnone | hstored
          · exact Or.inl hnone
          · refine Or.inr (Or.inr ⟨installed.registers.payload, hbirth, hstored⟩)
  | live registers owned base =>
      cases hdispatch : CoordinatorRoundDispatch.dispatch
          (.live (ReferenceActivePhysicalStep.liveInput x registers owned base)) with
      | live outcome =>
          have hcut : ReferenceActivePhysicalStep.dispatch x =
              .live registers owned base outcome := by
            simp only [ReferenceActivePhysicalStep.dispatch, hstate, hdispatch]
            rfl
          cases outcome with
          | clockFailure failure dispatch_eq =>
              have hnone : (actualStepRecord x).output.preparation.coordinator.selection = none := by
                simp [actualStepRecord, ReferenceActivePhysicalStep.step,
                  ReferenceActivePhysicalStep.prepare, hcut,
                  ReferenceActivePhysicalStep.DispatchCut.selection]
              exact Or.inl (actualRecord_next_storedPayload_none_of_no_selection
                (actualStepRecord x) hnone)
          | initializerFailure dispatched startRound_eq checked checked_eq =>
              have hnone : (actualStepRecord x).output.preparation.coordinator.selection = none := by
                simp [actualStepRecord, ReferenceActivePhysicalStep.step,
                  ReferenceActivePhysicalStep.prepare, hcut,
                  ReferenceActivePhysicalStep.DispatchCut.selection]
              exact Or.inl (actualRecord_next_storedPayload_none_of_no_selection
                (actualStepRecord x) hnone)
          | localFailure dispatched startRound_eq reason =>
              have hnone : (actualStepRecord x).output.preparation.coordinator.selection = none := by
                simp [actualStepRecord, ReferenceActivePhysicalStep.step,
                  ReferenceActivePhysicalStep.prepare, hcut,
                  ReferenceActivePhysicalStep.DispatchCut.selection]
              exact Or.inl (actualRecord_next_storedPayload_none_of_no_selection
                (actualStepRecord x) hnone)
          | cutoffChosen dispatched startRound_eq ledger initialization_eq ledger_eq_candidate
              initializationDomainValid cutoff_clock cutoff_pending no_assignment selected =>
              have htail := ReferenceAssignmentPayloadPersistence.collectionPostChoice_payload_frame
                (ReferenceActivePhysicalStep.prepare x) registers.payload
                (ReferenceActivePhysicalStep.sharedLedger ledger) dispatched.startResult
                (ReferenceActivePhysicalStep.liveRegistersAt registers x.time).complementWeights
              have hnext :
                  storedPayload (ReferenceActivePhysicalStep.step x).next.coordinator = none ∨
                    storedPayload (ReferenceActivePhysicalStep.step x).next.coordinator =
                      some registers.payload := by
                simpa [actualStepRecord, ReferenceActivePhysicalStep.step,
                  ReferenceActivePhysicalStep.prepare,
                  ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
                  ReferenceActivePhysicalStep.DispatchCut.selection,
                  ReferenceActivePhysicalStep.selectionAt, hcut] using htail
              rcases hnext with hnone | hstored
              · exact Or.inl hnone
              · exact Or.inr (Or.inl ⟨registers.payload,
                  by simp [hstate, storedPayload], hstored⟩)
          | continuingChosen dispatched startRound_eq continuation selected =>
              have htail := ReferenceAssignmentPayloadPersistence.livePostChoice_payload_frame
                (ReferenceActivePhysicalStep.prepare x)
                (ReferenceActivePhysicalStep.liveRegistersAt registers x.time)
                (ReferenceActivePhysicalStep.liveOwnedAt registers owned x.time)
                base dispatched.startResult
              have hnext :
                  storedPayload (ReferenceActivePhysicalStep.step x).next.coordinator = none ∨
                    storedPayload (ReferenceActivePhysicalStep.step x).next.coordinator =
                      some registers.payload := by
                simpa [actualStepRecord, ReferenceActivePhysicalStep.step,
                  ReferenceActivePhysicalStep.prepare,
                  ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
                  ReferenceActivePhysicalStep.DispatchCut.selection,
                  ReferenceActivePhysicalStep.selectionAt,
                  ReferenceActivePhysicalStep.liveRegistersAt, hcut] using htail
              rcases hnext with hnone | hstored
              · exact Or.inl hnone
              · exact Or.inr (Or.inl ⟨registers.payload,
                  by simp [hstate, storedPayload], hstored⟩)
  | collection payload ledger savedProposal =>
      by_cases hvalid : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
      · let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
        let clock := ReferenceActivePhysicalStep.collectionClock payload ledger
          savedProposal cutoff
        let source := ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff
        cases hdispatch : CoordinatorRoundDispatch.dispatch (.collection source) with
        | collection outcome =>
            have hcut : ReferenceActivePhysicalStep.dispatch x =
                .collection payload ledger clock cutoff outcome := by
              simp [ReferenceActivePhysicalStep.dispatch, hstate, hvalid,
                cutoff, clock, source, hdispatch]
              rfl
            cases outcome with
            | clockFailure failure startRound_eq =>
                have hnone : (actualStepRecord x).output.preparation.coordinator.selection = none := by
                  simp [actualStepRecord, ReferenceActivePhysicalStep.step,
                    ReferenceActivePhysicalStep.prepare, hcut,
                    ReferenceActivePhysicalStep.DispatchCut.selection]
                exact Or.inl (actualRecord_next_storedPayload_none_of_no_selection
                  (actualStepRecord x) hnone)
            | localFailure started startRound_eq core_invalid reason =>
                have hnone : (actualStepRecord x).output.preparation.coordinator.selection = none := by
                  simp [actualStepRecord, ReferenceActivePhysicalStep.step,
                    ReferenceActivePhysicalStep.prepare, hcut,
                    ReferenceActivePhysicalStep.DispatchCut.selection]
                exact Or.inl (actualRecord_next_storedPayload_none_of_no_selection
                  (actualStepRecord x) hnone)
            | coreFailure core started startRound_eq reason =>
                have hnone : (actualStepRecord x).output.preparation.coordinator.selection = none := by
                  simp [actualStepRecord, ReferenceActivePhysicalStep.step,
                    ReferenceActivePhysicalStep.prepare, hcut,
                    ReferenceActivePhysicalStep.DispatchCut.selection]
                exact Or.inl (actualRecord_next_storedPayload_none_of_no_selection
                  (actualStepRecord x) hnone)
            | continuing core snapshot boundary currentScoresChecked =>
                let weights := CoordinatorCollectionInteractive.PreObservationInputs.weights
                  source snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq
                have htail := ReferenceAssignmentPayloadPersistence.collectionPostChoice_payload_frame
                  (ReferenceActivePhysicalStep.prepare x) payload ledger snapshot.clockStarted weights
                have hnext :
                    storedPayload (ReferenceActivePhysicalStep.step x).next.coordinator = none ∨
                      storedPayload (ReferenceActivePhysicalStep.step x).next.coordinator =
                        some payload := by
                  simpa [actualStepRecord, ReferenceActivePhysicalStep.step,
                    ReferenceActivePhysicalStep.prepare,
                    ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
                    ReferenceActivePhysicalStep.DispatchCut.selection,
                    hcut, source, weights] using htail
                rcases hnext with hnone | hstored
                · exact Or.inl hnone
                · exact Or.inr (Or.inl ⟨payload,
                    by simp [hstate, storedPayload], hstored⟩)
            | laterReconstructionFailure core consistent started startRound_eq instruction
                assignmentStart_eq reason later_eq =>
                have hnone : (actualStepRecord x).output.preparation.coordinator.selection = none := by
                  simp [actualStepRecord, ReferenceActivePhysicalStep.step,
                    ReferenceActivePhysicalStep.prepare, hcut,
                    ReferenceActivePhysicalStep.DispatchCut.selection]
                exact Or.inl (actualRecord_next_storedPayload_none_of_no_selection
                  (actualStepRecord x) hnone)
            | laterPrefixFailure core consistent started startRound_eq instruction
                assignmentStart_eq arm reason later_eq =>
                have hnone : (actualStepRecord x).output.preparation.coordinator.selection = none := by
                  simp [actualStepRecord, ReferenceActivePhysicalStep.step,
                    ReferenceActivePhysicalStep.prepare, hcut,
                    ReferenceActivePhysicalStep.DispatchCut.selection]
                exact Or.inl (actualRecord_next_storedPayload_none_of_no_selection
                  (actualStepRecord x) hnone)
            | laterOrientationFailure core consistent started startRound_eq instruction
                assignmentStart_eq set later_eq =>
                have hnone : (actualStepRecord x).output.preparation.coordinator.selection = none := by
                  simp [actualStepRecord, ReferenceActivePhysicalStep.step,
                    ReferenceActivePhysicalStep.prepare, hcut,
                    ReferenceActivePhysicalStep.DispatchCut.selection]
                exact Or.inl (actualRecord_next_storedPayload_none_of_no_selection
                  (actualStepRecord x) hnone)
            | laterChoiceFailure core consistent started startRound_eq instruction
                assignmentStart_eq output consistency clockData installed reason =>
                have hnone : (actualStepRecord x).output.preparation.coordinator.selection = none := by
                  simp [actualStepRecord, ReferenceActivePhysicalStep.step,
                    ReferenceActivePhysicalStep.prepare, hcut,
                    ReferenceActivePhysicalStep.DispatchCut.selection]
                exact Or.inl (actualRecord_next_storedPayload_none_of_no_selection
                  (actualStepRecord x) hnone)
            | laterChosen core consistent started startRound_eq instruction assignmentStart_eq
                output consistency clockData installed selected =>
                have hprov := ReferenceLaterInstallationProvenance.dispatch_laterChosen_provenance x
                rw [hcut] at hprov
                have htime : instruction.time = x.time := by
                  apply Fin.ext
                  calc
                    instruction.time.val = output.payload.sigma.val :=
                      (congrArg Fin.val output.payload_start).symm
                    _ = installed.registers.payload.sigma.val := by rw [hprov.2.1]
                    _ = x.time.val := hprov.2.2.1
                have htail := ReferenceAssignmentPayloadPersistence.livePostChoice_payload_frame
                  (ReferenceActivePhysicalStep.prepare x) installed.registers
                  installed.ownedRegisters installed.retainedBaseScore started
                have hpreparedCut : (ReferenceActivePhysicalStep.prepare x).coordinator =
                    .collection payload ledger clock cutoff
                      (.laterChosen core consistent started startRound_eq instruction
                        assignmentStart_eq output consistency clockData installed selected) := hcut
                have hselection :
                    (ReferenceActivePhysicalStep.prepare x).coordinator.selection ≠ none := by
                  simp [hpreparedCut, ReferenceActivePhysicalStep.DispatchCut.selection,
                    ReferenceActivePhysicalStep.selectionAt, htime]
                have hnext :
                    storedPayload (ReferenceActivePhysicalStep.step x).next.coordinator = none ∨
                      storedPayload (ReferenceActivePhysicalStep.step x).next.coordinator =
                        some installed.registers.payload := by
                  change storedPayload (ReferenceActivePhysicalStep.prepare x).observeCoordinator.configuration = none ∨
                    storedPayload (ReferenceActivePhysicalStep.prepare x).observeCoordinator.configuration =
                      some installed.registers.payload
                  unfold ReferenceActivePhysicalStep.PreparedRound.observeCoordinator
                  rw [dif_neg hselection, hpreparedCut]
                  exact htail
                have hbirth : InstallationBirth (actualStepRecord x)
                    installed.registers.payload := by
                  simpa [actualStepRecord, InstallationBirth,
                    ReferenceActivePhysicalStep.step,
                    ReferenceActivePhysicalStep.prepare, hcut] using
                    ReferenceLaterInstallationProvenance.record_laterChosen_birth
                      (actualStepRecord x)
                rcases hnext with hnone | hstored
                · exact Or.inl hnone
                · exact Or.inr (Or.inr ⟨installed.registers.payload, hbirth, hstored⟩)
      · have hnone : (actualStepRecord x).output.preparation.coordinator.selection = none := by
          simp [actualStepRecord, ReferenceActivePhysicalStep.step,
            ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch,
            hstate, hvalid, ReferenceActivePhysicalStep.DispatchCut.selection]
        exact Or.inl (actualRecord_next_storedPayload_none_of_no_selection
          (actualStepRecord x) hnone)
  | dagger =>
      have hnone : (actualStepRecord x).output.preparation.coordinator.selection = none := by
        simp [actualStepRecord, ReferenceActivePhysicalStep.step,
          ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch,
          hstate, ReferenceActivePhysicalStep.DispatchCut.selection]
      exact Or.inl (actualRecord_next_storedPayload_none_of_no_selection
        (actualStepRecord x) hnone)

/-- The record computed at calendar index `index` by the accepted horizon.
Its output is the literal `ReferenceActivePhysicalStep.step` on the run's
computed prefix state and original row and reward table. -/
def actualRunRecordAt
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start index : ℕ) (hspan : start + (index + 1) ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start) :
    ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) :=
  let prior := ReferenceActivePhysicalHorizon.run initial rows selected rewards
    start index (by omega) hmode
  let input := ReferenceActivePhysicalHorizon.roundInputAt initial rows selected
    rewards start hmode prior ⟨start + index, by omega, by omega⟩
  ⟨input, ReferenceActivePhysicalStep.step input, rfl⟩

/-- The accepted horizon successor appends exactly the record computed at
that physical calendar coordinate. -/
theorem run_successor_actualRunRecordAt
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start index : ℕ) (hspan : start + (index + 1) ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start) :
    (ReferenceActivePhysicalHorizon.run initial rows selected rewards start
      (index + 1) hspan hmode).records =
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start
        index (by omega) hmode).records ++
        [actualRunRecordAt initial rows selected rewards start index hspan hmode] := by
  rw [ReferenceActivePhysicalHorizon.run_successor_step]
  rfl

/-- The same actual successor equation exposes the computed final state. -/
theorem run_successor_finalState_eq_actualRunRecordAt
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start index : ℕ) (hspan : start + (index + 1) ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start) :
    (ReferenceActivePhysicalHorizon.run initial rows selected rewards start
      (index + 1) hspan hmode).finalState =
      (actualRunRecordAt initial rows selected rewards start index hspan hmode).output.next := by
  rw [ReferenceActivePhysicalHorizon.run_successor_step]
  rfl

/-- A birth payload's timestamp is the physical time of the record whose
actual dispatcher result installed it. -/
theorem installationBirth_time_eq
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (payload : Payload rate)
    (hbirth : InstallationBirth record payload) :
    payload.sigma.val = record.input.time.val := by
  cases hcoord : record.output.preparation.coordinator with
  | first outcome =>
      cases outcome with
      | chosen installed selected =>
          simp [InstallationBirth, hcoord] at hbirth
          rcases hbirth with ⟨rfl, htime⟩
          exact htime
      | choiceDomainFailure installed =>
          simp [InstallationBirth, hcoord] at hbirth
      | recorderBoundaryFailure installed =>
          simp [InstallationBirth, hcoord] at hbirth
      | choiceRejected installed =>
          simp [InstallationBirth, hcoord] at hbirth
  | live registers owned base outcome =>
      simp [InstallationBirth, hcoord] at hbirth
  | collection payload ledger clock cutoff outcome =>
      cases outcome with
      | laterChosen core consistent started startRound_eq instruction assignmentStart_eq
          output localConsistency_eq clockData installed selected =>
          simp [InstallationBirth, hcoord] at hbirth
          rcases hbirth with ⟨rfl, htime⟩
          exact htime
      | clockFailure failure startRound_eq =>
          simp [InstallationBirth, hcoord] at hbirth
      | localFailure started startRound_eq core_invalid reason =>
          simp [InstallationBirth, hcoord] at hbirth
      | coreFailure core started startRound_eq reason =>
          simp [InstallationBirth, hcoord] at hbirth
      | continuing core prepared boundary checked =>
          simp [InstallationBirth, hcoord] at hbirth
      | laterReconstructionFailure core consistent started startRound_eq instruction
          assignmentStart_eq reason later_eq =>
          simp [InstallationBirth, hcoord] at hbirth
      | laterPrefixFailure core consistent started startRound_eq instruction
          assignmentStart_eq arm reason later_eq =>
          simp [InstallationBirth, hcoord] at hbirth
      | laterOrientationFailure core consistent started startRound_eq instruction
          assignmentStart_eq set later_eq =>
          simp [InstallationBirth, hcoord] at hbirth
      | laterChoiceFailure core consistent started startRound_eq instruction
          assignmentStart_eq output consistency clockData installed reason =>
          simp [InstallationBirth, hcoord] at hbirth
  | invalidCollectionCutoff =>
      simp [InstallationBirth, hcoord] at hbirth
  | dagger =>
      simp [InstallationBirth, hcoord] at hbirth

/-- A first chosen dispatcher result is a literal output-record birth. Its
timestamp is fixed by the checked actual dispatcher result, independently of
whether the later post-choice tail retains the payload. -/
theorem actualFirstChosen_installationBirth
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (hfirst : x.state.coordinator = .first)
    (installed : CoordinatorAssignmentRegisterInstall.FirstInstallation
      (CoordinatorRoundDispatch.firstLaunchInput (ReferenceActivePhysicalStep.firstInput x)))
    (selected : CoordinatorRoundDispatch.ArmSelection installed.registers.payload
      installed.startRoundResult installed.registers.time installed.registers.complementWeights x.row)
    (hchosen : CoordinatorRoundDispatch.dispatchFirst
      (ReferenceActivePhysicalStep.firstInput x) = .chosen installed selected) :
    InstallationBirth (actualStepRecord x) installed.registers.payload := by
  have hcoord : (actualStepRecord x).output.preparation.coordinator =
      .first (.chosen installed selected) := by
    simp [actualStepRecord, ReferenceActivePhysicalStep.step,
      ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch,
      CoordinatorRoundDispatch.dispatch, hfirst, hchosen] <;> rfl
  unfold InstallationBirth
  rw [hcoord]
  exact ⟨rfl,
    ReferenceAssignmentPayloadPersistence.firstChosen_payload_time
      x installed selected hchosen⟩

/-- In every actual prefix begun from the first coordinator phase, a retained
payload has an earlier actual installation record in that same prefix. Its
birth time is exactly its assignment sigma, and lies in the half-open physical
calendar interval. -/
private theorem run_finalStoredPayload_has_birth
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hinitial : initial.coordinator = .first)
    (payload : Payload rate)
    (hstored : storedPayload
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards
        start count hspan hmode).finalState.coordinator = some payload) :
    ∃ record,
      record ∈ (ReferenceActivePhysicalHorizon.run initial rows selected rewards
        start count hspan hmode).records ∧
      InstallationBirth record payload ∧
      payload.sigma.val = record.input.time.val ∧
      start ≤ payload.sigma.val ∧ payload.sigma.val < start + count := by
  induction count generalizing payload with
  | zero =>
      rw [ReferenceActivePhysicalHorizon.run_zero_final] at hstored
      simp [hinitial, storedPayload] at hstored
  | succ count ih =>
      let previous := ReferenceActivePhysicalHorizon.run initial rows selected rewards
        start count (by omega) hmode
      let record := actualRunRecordAt initial rows selected rewards start count hspan hmode
      have hfinal := run_successor_finalState_eq_actualRunRecordAt initial rows selected
        rewards start count hspan hmode
      rw [hfinal] at hstored
      have hstoredStep : storedPayload (ReferenceActivePhysicalStep.step record.input).next.coordinator =
          some payload := by
        simpa [record, actualRunRecordAt] using hstored
      have hrecord : actualStepRecord record.input = record := by
        rfl
      have hclass := actualStep_payload_classification record.input
      rw [hrecord] at hclass
      have hinput : record.input.state = previous.finalState := by
        rfl
      rw [hinput] at hclass
      rcases hclass with hnone | ⟨old, hprevious, hnext⟩ |
        ⟨fresh, hfreshBirth, hnext⟩
      · rw [hnone] at hstoredStep
        cases hstoredStep
      · have hold : old = payload := Option.some.inj (hnext.symm.trans hstoredStep)
        subst old
        obtain ⟨birthRecord, hbirthMem, hbirth, hbirthSigma, hbirthLower, hbirthUpper⟩ :=
          ih (by omega) payload hprevious
        have hrecords := run_successor_actualRunRecordAt initial rows selected rewards
          start count hspan hmode
        have hbirthMem' : birthRecord ∈
            (ReferenceActivePhysicalHorizon.run initial rows selected rewards
              start (count + 1) hspan hmode).records := by
          rw [hrecords]
          exact List.mem_append_left _ hbirthMem
        exact ⟨birthRecord, hbirthMem', hbirth, hbirthSigma, hbirthLower,
          by omega⟩
      · have hfreshEq : fresh = payload := Option.some.inj (hnext.symm.trans hstoredStep)
        subst fresh
        have hbTime := installationBirth_time_eq record payload hfreshBirth
        have hrecordTime : record.input.time.val = start + count := by
          rfl
        have hrecords := run_successor_actualRunRecordAt initial rows selected rewards
          start count hspan hmode
        have hrecordMem : record ∈
            (ReferenceActivePhysicalHorizon.run initial rows selected rewards
              start (count + 1) hspan hmode).records := by
          rw [hrecords]
          apply List.mem_append_right
          simp [record]
        exact ⟨record, hrecordMem, hfreshBirth, hbTime,
          by omega, by omega⟩

/-- Prefix form of the actual birth theorem. `prefix ≤ totalCount` is kept
explicit for callers who parameterize the full requested horizon while
asking about an intermediate computed prefix. -/
theorem run_prefix_storedPayload_has_birth
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start totalCount : ℕ) (hspan : start + totalCount ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hinitial : initial.coordinator = .first)
    (prefixLength : ℕ) (hprefix : prefixLength ≤ totalCount)
    (payload : Payload rate)
    (hstored : storedPayload
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards
        start prefixLength (by omega) hmode).finalState.coordinator = some payload) :
    ∃ record,
      record ∈ (ReferenceActivePhysicalHorizon.run initial rows selected rewards
        start prefixLength (by omega) hmode).records ∧
      InstallationBirth record payload ∧
      record.input.time.val = payload.sigma.val ∧
      start ≤ payload.sigma.val ∧ payload.sigma.val < start + prefixLength := by
  obtain ⟨record, hmem, hbirth, htime, hlower, hupper⟩ :=
    run_finalStoredPayload_has_birth initial rows selected rewards start prefixLength
      (by omega) hmode hinitial payload hstored
  exact ⟨record, hmem, hbirth, htime.symm, hlower, hupper⟩

/-- Physical calendar coordinates occur at most once among the actual records
of one finite horizon run. This is derived from the canonical calendar list,
not an assumed ordering of assignment starts. -/
theorem run_records_time_injective
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    {left right : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)}
    (hleft : left ∈ (ReferenceActivePhysicalHorizon.run initial rows selected rewards
      start count hspan hmode).records)
    (hright : right ∈ (ReferenceActivePhysicalHorizon.run initial rows selected rewards
      start count hspan hmode).records)
    (htime : left.input.time.val = right.input.time.val) :
    left = right := by
  have hnodup : ((ReferenceActivePhysicalHorizon.run initial rows selected rewards
      start count hspan hmode).records.map (fun record => record.input.time.val)).Nodup := by
    rw [ReferenceActivePhysicalHorizon.run_time_values]
    simp [ReferenceActivePhysicalHorizon.calendar, List.nodup_range']
  exact List.inj_on_of_nodup_map hnodup hleft hright htime

/-- One actual record cannot give two different payloads the same
`InstallationBirth`; the installing constructor fixes the whole payload. -/
theorem installationBirth_payload_unique
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (left right : Payload rate)
    (hleft : InstallationBirth record left)
    (hright : InstallationBirth record right) :
    left = right := by
  cases hcoord : record.output.preparation.coordinator with
  | first outcome =>
      cases outcome with
      | chosen installed selected =>
          simp [InstallationBirth, hcoord] at hleft hright
          rcases hleft with ⟨rfl, _⟩
          rcases hright with ⟨rfl, _⟩
          rfl
      | choiceDomainFailure installed =>
          simp [InstallationBirth, hcoord] at hleft
      | recorderBoundaryFailure installed =>
          simp [InstallationBirth, hcoord] at hleft
      | choiceRejected installed =>
          simp [InstallationBirth, hcoord] at hleft
  | live registers owned base outcome =>
      simp [InstallationBirth, hcoord] at hleft
  | collection payload ledger clock cutoff outcome =>
      cases outcome with
      | laterChosen core consistent started startRound_eq instruction assignmentStart_eq
          output localConsistency_eq clockData installed selected =>
          simp [InstallationBirth, hcoord] at hleft hright
          rcases hleft with ⟨rfl, _⟩
          rcases hright with ⟨rfl, _⟩
          rfl
      | clockFailure failure startRound_eq =>
          simp [InstallationBirth, hcoord] at hleft
      | localFailure started startRound_eq core_invalid reason =>
          simp [InstallationBirth, hcoord] at hleft
      | coreFailure core started startRound_eq reason =>
          simp [InstallationBirth, hcoord] at hleft
      | continuing core prepared boundary checked =>
          simp [InstallationBirth, hcoord] at hleft
      | laterReconstructionFailure core consistent started startRound_eq instruction
          assignmentStart_eq reason later_eq =>
          simp [InstallationBirth, hcoord] at hleft
      | laterPrefixFailure core consistent started startRound_eq instruction
          assignmentStart_eq arm reason later_eq =>
          simp [InstallationBirth, hcoord] at hleft
      | laterOrientationFailure core consistent started startRound_eq instruction
          assignmentStart_eq set later_eq =>
          simp [InstallationBirth, hcoord] at hleft
      | laterChoiceFailure core consistent started startRound_eq instruction
          assignmentStart_eq output consistency clockData installed reason =>
          simp [InstallationBirth, hcoord] at hleft
  | invalidCollectionCutoff =>
      simp [InstallationBirth, hcoord] at hleft
  | dagger =>
      simp [InstallationBirth, hcoord] at hleft

/-- Distinct actual birth records in one run have strictly separated physical
timestamps. The calendar induction proves this even when assignment starts
are not assumed monotone. -/
theorem run_birth_records_strictly_separated
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    {left right : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)}
    (hleft : left ∈ (ReferenceActivePhysicalHorizon.run initial rows selected rewards
      start count hspan hmode).records)
    (hright : right ∈ (ReferenceActivePhysicalHorizon.run initial rows selected rewards
      start count hspan hmode).records)
    (hne : left ≠ right) :
    left.input.time.val < right.input.time.val ∨
      right.input.time.val < left.input.time.val := by
  have hneq := fun heq => hne (run_records_time_injective initial rows selected rewards
    start count hspan hmode hleft hright heq)
  exact lt_or_gt_of_ne hneq

/-- Equal assignment timestamps identify whole payloads when the payloads
were installed by actual records in the same physical run. -/
theorem run_birth_payload_eq_of_equal_sigma
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (leftRecord rightRecord : ReferenceActivePhysicalHorizon.RoundRecord
      (p := p) (rate := rate))
    (leftPayload rightPayload : Payload rate)
    (hleft : leftRecord ∈ (ReferenceActivePhysicalHorizon.run initial rows selected
      rewards start count hspan hmode).records)
    (hright : rightRecord ∈ (ReferenceActivePhysicalHorizon.run initial rows selected
      rewards start count hspan hmode).records)
    (hleftBirth : InstallationBirth leftRecord leftPayload)
    (hrightBirth : InstallationBirth rightRecord rightPayload)
    (hsigma : leftPayload.sigma.val = rightPayload.sigma.val) :
    leftPayload = rightPayload := by
  have hleftTime := installationBirth_time_eq leftRecord leftPayload hleftBirth
  have hrightTime := installationBirth_time_eq rightRecord rightPayload hrightBirth
  have hrecordTime : leftRecord.input.time.val = rightRecord.input.time.val :=
    hleftTime.symm.trans (hsigma.trans hrightTime)
  have hrecord := run_records_time_injective initial rows selected rewards start count
    hspan hmode hleft hright hrecordTime
  subst rightRecord
  exact installationBirth_payload_unique leftRecord leftPayload rightPayload
    hleftBirth hrightBirth

private theorem foldCalendar_contains_acc_record
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (origin intervalStart count : ℕ) (horigin : origin ≤ intervalStart)
    (hspan : intervalStart + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial origin)
    (acc : ReferenceActivePhysicalHorizon.Run initial)
    {record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)}
    (hrecord : record ∈ acc.records) :
    record ∈ (ReferenceActivePhysicalHorizon.foldCalendar initial rows selected rewards
      origin intervalStart count horigin hspan hmode acc).records := by
  change record ∈
    ((ReferenceActivePhysicalHorizon.calendarEntries origin intervalStart count horigin hspan).foldl
      (ReferenceActivePhysicalHorizon.foldRound initial rows selected rewards origin hmode) acc).records
  induction ReferenceActivePhysicalHorizon.calendarEntries origin intervalStart count
      horigin hspan generalizing acc with
  | nil => simpa
  | cons entry rest ih =>
      simp only [List.foldl_cons]
      apply ih
      change record ∈ acc.records ++ [_]
      exact List.mem_append_left _ hrecord

/-- Retained payloads at any two endpoints in one computed prefix are equal
when their assignment timestamps agree. Both endpoint births are found by the
actual prefix induction and embedded into the common physical calendar; the
calendar then identifies their installing records. -/
theorem run_prefix_storedPayload_eq_of_equal_sigma
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start totalCount : ℕ) (hspan : start + totalCount ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hinitial : initial.coordinator = .first)
    (leftPrefix rightPrefix : ℕ)
    (hleftPrefix : leftPrefix ≤ totalCount)
    (hrightPrefix : rightPrefix ≤ totalCount)
    (leftPayload rightPayload : Payload rate)
    (hleft : storedPayload
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards
        start leftPrefix (by omega) hmode).finalState.coordinator = some leftPayload)
    (hright : storedPayload
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards
        start rightPrefix (by omega) hmode).finalState.coordinator = some rightPayload)
    (hsigma : leftPayload.sigma.val = rightPayload.sigma.val) :
    leftPayload = rightPayload := by
  obtain ⟨leftBirth, hleftBirthMem, hleftBirth, _, _, _⟩ :=
    run_prefix_storedPayload_has_birth initial rows selected rewards start totalCount hspan
      hmode hinitial leftPrefix hleftPrefix leftPayload hleft
  obtain ⟨rightBirth, hrightBirthMem, hrightBirth, _, _, _⟩ :=
    run_prefix_storedPayload_has_birth initial rows selected rewards start totalCount hspan
      hmode hinitial rightPrefix hrightPrefix rightPayload hright
  have hleftSplit : leftPrefix + (totalCount - leftPrefix) = totalCount :=
    Nat.add_sub_of_le hleftPrefix
  have hrightSplit : rightPrefix + (totalCount - rightPrefix) = totalCount :=
    Nat.add_sub_of_le hrightPrefix
  have hleftAppend :
      ReferenceActivePhysicalHorizon.run initial rows selected rewards
          start totalCount hspan hmode =
        ReferenceActivePhysicalHorizon.foldCalendar initial rows selected rewards
          start (start + leftPrefix) (totalCount - leftPrefix) (by omega) (by omega)
          hmode (ReferenceActivePhysicalHorizon.run initial rows selected rewards
            start leftPrefix (by omega) hmode) := by
    have h := ReferenceActivePhysicalHorizon.run_append initial rows selected rewards start
      leftPrefix (totalCount - leftPrefix) (by omega) hmode
    simpa [hleftSplit] using h
  have hrightAppend :
      ReferenceActivePhysicalHorizon.run initial rows selected rewards
          start totalCount hspan hmode =
        ReferenceActivePhysicalHorizon.foldCalendar initial rows selected rewards
          start (start + rightPrefix) (totalCount - rightPrefix) (by omega) (by omega)
          hmode (ReferenceActivePhysicalHorizon.run initial rows selected rewards
            start rightPrefix (by omega) hmode) := by
    have h := ReferenceActivePhysicalHorizon.run_append initial rows selected rewards start
      rightPrefix (totalCount - rightPrefix) (by omega) hmode
    simpa [hrightSplit] using h
  have hleftTotal : leftBirth ∈
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards
        start totalCount hspan hmode).records := by
    rw [hleftAppend]
    exact foldCalendar_contains_acc_record initial rows selected rewards start
      (start + leftPrefix) (totalCount - leftPrefix) (by omega) (by omega) hmode
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start leftPrefix
        (by omega) hmode) hleftBirthMem
  have hrightTotal : rightBirth ∈
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards
        start totalCount hspan hmode).records := by
    rw [hrightAppend]
    exact foldCalendar_contains_acc_record initial rows selected rewards start
      (start + rightPrefix) (totalCount - rightPrefix) (by omega) (by omega) hmode
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start rightPrefix
        (by omega) hmode) hrightBirthMem
  exact run_birth_payload_eq_of_equal_sigma initial rows selected rewards start totalCount
    hspan hmode leftBirth rightBirth leftPayload rightPayload hleftTotal hrightTotal
    hleftBirth hrightBirth hsigma

/-- The whole DOWN record, including its immutable initial q seed, is shared
by every retained endpoint carrying the same assignment timestamp. -/
theorem run_prefix_storedDownRecord_eq_of_equal_sigma
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start totalCount : ℕ) (hspan : start + totalCount ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hinitial : initial.coordinator = .first)
    (leftPrefix rightPrefix : ℕ)
    (hleftPrefix : leftPrefix ≤ totalCount)
    (hrightPrefix : rightPrefix ≤ totalCount)
    (leftPayload rightPayload : Payload rate)
    (hleft : storedPayload
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards
        start leftPrefix (by omega) hmode).finalState.coordinator = some leftPayload)
    (hright : storedPayload
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards
        start rightPrefix (by omega) hmode).finalState.coordinator = some rightPayload)
    (hsigma : leftPayload.sigma.val = rightPayload.sigma.val)
    (i : ActiveRoundActions.Follower p.m) :
    leftPayload.downRecord i = rightPayload.downRecord i := by
  exact downRecord_eq_of_payload_eq leftPayload rightPayload
    (run_prefix_storedPayload_eq_of_equal_sigma initial rows selected rewards start totalCount
      hspan hmode hinitial leftPrefix rightPrefix hleftPrefix hrightPrefix
      leftPayload rightPayload hleft hright hsigma) i

/-- A selected view that was already stored at the actual pre-state agrees in
all payload fields with any retained endpoint payload having the same sigma.
The pre-state is tied to a literal run prefix, and the selected view comes
from this record's actual preparation. -/
theorem run_actualRetainedSelection_eq_of_equal_sigma
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selectedRow : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start totalCount : ℕ) (hspan : start + totalCount ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hinitial : initial.coordinator = .first)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (view : Selection record.input)
    (hrecord : record ∈ (ReferenceActivePhysicalHorizon.run initial rows selectedRow rewards
      start totalCount hspan hmode).records)
    (hview : record.output.preparation.coordinator.selection = some view)
    (inputPrefix : ℕ) (hinputPrefix : inputPrefix ≤ totalCount)
    (hinputState : record.input.state =
      (ReferenceActivePhysicalHorizon.run initial rows selectedRow rewards start inputPrefix
        (by omega) hmode).finalState)
    (hinputPayload : storedPayload record.input.state.coordinator = some view.view.payload)
    (endpointPrefix : ℕ) (hendpointPrefix : endpointPrefix ≤ totalCount)
    (endpointPayload : Payload rate)
    (hendpoint : storedPayload
      (ReferenceActivePhysicalHorizon.run initial rows selectedRow rewards start endpointPrefix
        (by omega) hmode).finalState.coordinator = some endpointPayload)
    (hsigma : view.view.payload.sigma.val = endpointPayload.sigma.val) :
    record ∈ (ReferenceActivePhysicalHorizon.run initial rows selectedRow rewards
      start totalCount hspan hmode).records ∧
    selectedPayload record = some endpointPayload ∧ view.view.payload = endpointPayload := by
  have hinput : storedPayload
      (ReferenceActivePhysicalHorizon.run initial rows selectedRow rewards start inputPrefix
        (by omega) hmode).finalState.coordinator = some view.view.payload := by
    rw [← hinputState]
    exact hinputPayload
  have hpayload := run_prefix_storedPayload_eq_of_equal_sigma initial rows selectedRow rewards
    start totalCount hspan hmode hinitial inputPrefix endpointPrefix hinputPrefix hendpointPrefix
    view.view.payload endpointPayload hinput hendpoint hsigma
  have hprojection := selectedPayload_eq_of_actualSelection record view hview
  exact ⟨hrecord, hprojection.trans (congrArg some hpayload), hpayload⟩

/-- During a continuing retained assignment, an actual selected DOWN view
encodes the fixed endpoint word on precisely its pending sender branch. -/
theorem run_actualRetainedSelection_expectedDownFlatWord
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selectedRow : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start totalCount : ℕ) (hspan : start + totalCount ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hinitial : initial.coordinator = .first)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (view : Selection record.input)
    (hrecord : record ∈ (ReferenceActivePhysicalHorizon.run initial rows selectedRow rewards
      start totalCount hspan hmode).records)
    (hview : record.output.preparation.coordinator.selection = some view)
    (inputPrefix : ℕ) (hinputPrefix : inputPrefix ≤ totalCount)
    (hinputState : record.input.state =
      (ReferenceActivePhysicalHorizon.run initial rows selectedRow rewards start inputPrefix
        (by omega) hmode).finalState)
    (hinputPayload : storedPayload record.input.state.coordinator = some view.view.payload)
    (endpointPrefix : ℕ) (hendpointPrefix : endpointPrefix ≤ totalCount)
    (endpointPayload : Payload rate)
    (hendpoint : storedPayload
      (ReferenceActivePhysicalHorizon.run initial rows selectedRow rewards start endpointPrefix
        (by omega) hmode).finalState.coordinator = some endpointPayload)
    (hsigma : view.view.payload.sigma.val = endpointPayload.sigma.val)
    (i : ActiveRoundActions.Follower p.m)
    (hbranch : selectedDownSenderBranch view.view i record.input.row record.input.time) :
    expectedDownFlatWord (some view.view) i record.input.row record.input.time =
      some (storedDownFlatWord endpointPayload i) := by
  have hpayload := run_actualRetainedSelection_eq_of_equal_sigma initial rows selectedRow rewards
    start totalCount hspan hmode hinitial record view hrecord hview inputPrefix hinputPrefix
    hinputState hinputPayload endpointPrefix hendpointPrefix endpointPayload hendpoint hsigma
  exact (actualSelection_expectedDownFlatWord_of_payload_eq record view hview endpointPayload
    hpayload.2.2 i hbranch).1

/-- A selected payload on an actual installation round agrees in all fields
with a later retained endpoint payload when their assignment timestamps
agree. The selection may survive in the preparation record even when the
post-choice tail stores `none`; no tail-success premise is used. -/
theorem run_actualInstallationSelection_eq_of_equal_sigma
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selectedRow : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start totalCount : ℕ) (hspan : start + totalCount ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hinitial : initial.coordinator = .first)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (selectedValue : Payload rate)
    (hrecord : record ∈ (ReferenceActivePhysicalHorizon.run initial rows selectedRow rewards
      start totalCount hspan hmode).records)
    (hselected : selectedPayload record = some selectedValue)
    (hbirth : InstallationBirth record selectedValue)
    (prefixLength : ℕ) (hprefix : prefixLength ≤ totalCount)
    (endpointPayload : Payload rate)
    (hendpoint : storedPayload
      (ReferenceActivePhysicalHorizon.run initial rows selectedRow rewards start prefixLength
        (by omega) hmode).finalState.coordinator = some endpointPayload)
    (hsigma : selectedValue.sigma.val = endpointPayload.sigma.val) :
    selectedPayload record = some endpointPayload ∧ selectedValue = endpointPayload := by
  obtain ⟨endpointBirth, hendpointBirthMem, hendpointBirth, _, _, _⟩ :=
    run_prefix_storedPayload_has_birth initial rows selectedRow rewards start totalCount hspan
      hmode hinitial prefixLength hprefix endpointPayload hendpoint
  have hsplit : prefixLength + (totalCount - prefixLength) = totalCount :=
    Nat.add_sub_of_le hprefix
  have happend :
      ReferenceActivePhysicalHorizon.run initial rows selectedRow rewards
          start totalCount hspan hmode =
        ReferenceActivePhysicalHorizon.foldCalendar initial rows selectedRow rewards
          start (start + prefixLength) (totalCount - prefixLength) (by omega) (by omega)
          hmode (ReferenceActivePhysicalHorizon.run initial rows selectedRow rewards
            start prefixLength (by omega) hmode) := by
    have h := ReferenceActivePhysicalHorizon.run_append initial rows selectedRow rewards start
      prefixLength (totalCount - prefixLength) (by omega) hmode
    simpa [hsplit] using h
  have hendpointBirthTotal : endpointBirth ∈
      (ReferenceActivePhysicalHorizon.run initial rows selectedRow rewards
        start totalCount hspan hmode).records := by
    rw [happend]
    exact foldCalendar_contains_acc_record initial rows selectedRow rewards start
      (start + prefixLength) (totalCount - prefixLength) (by omega) (by omega) hmode
      (ReferenceActivePhysicalHorizon.run initial rows selectedRow rewards start prefixLength
        (by omega) hmode) hendpointBirthMem
  have hpayloadEq := run_birth_payload_eq_of_equal_sigma initial rows selectedRow rewards start totalCount
    hspan hmode record endpointBirth selectedValue endpointPayload hrecord
    hendpointBirthTotal hbirth hendpointBirth hsigma
  exact ⟨hselected.trans (congrArg some hpayloadEq), hpayloadEq⟩

/-- The actual expected DOWN word on an installation selection is the word
encoded by the matching retained endpoint, under the actual pending sender
branch. This does not assert that the branch is active on every slot. -/
theorem run_actualInstallationSelection_expectedDownFlatWord
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selectedRow : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start totalCount : ℕ) (hspan : start + totalCount ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hinitial : initial.coordinator = .first)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (selectedValue : Payload rate)
    (hrecord : record ∈ (ReferenceActivePhysicalHorizon.run initial rows selectedRow rewards
      start totalCount hspan hmode).records)
    (hselected : selectedPayload record = some selectedValue)
    (hbirth : InstallationBirth record selectedValue)
    (prefixLength : ℕ) (hprefix : prefixLength ≤ totalCount)
    (endpointPayload : Payload rate)
    (hendpoint : storedPayload
      (ReferenceActivePhysicalHorizon.run initial rows selectedRow rewards start prefixLength
        (by omega) hmode).finalState.coordinator = some endpointPayload)
    (hsigma : selectedValue.sigma.val = endpointPayload.sigma.val)
    (view : Selection record.input)
    (hview : record.output.preparation.coordinator.selection = some view)
    (i : ActiveRoundActions.Follower p.m)
    (hbranch : selectedDownSenderBranch view.view i record.input.row record.input.time) :
    expectedDownFlatWord (some view.view) i record.input.row record.input.time =
      some (storedDownFlatWord endpointPayload i) := by
  have hpayload := run_actualInstallationSelection_eq_of_equal_sigma initial rows selectedRow
    rewards start totalCount hspan hmode hinitial record selectedValue hrecord hselected hbirth
    prefixLength hprefix endpointPayload hendpoint hsigma
  have hviewPayload : view.view.payload = endpointPayload := by
    have hviewProjection := selectedPayload_eq_of_actualSelection record view hview
    exact Option.some.inj (hviewProjection.symm.trans hpayload.1)
  exact (actualSelection_expectedDownFlatWord_of_payload_eq record view hview endpointPayload
    hviewPayload i hbranch).1

/-- Specialize the actual-run prefix birth result to the accepted launched
boundary. Every source-facing boundary binder remains exposed. Activity comes
from the accepted boundary construction and the initial `.first` equation;
the computed run has no added no-dagger or fixed-word premise. -/
theorem actualBoundary_run_prefix_storedPayload_has_birth
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (rate : RateInput p) (C_star C_h : ℝ)
    (b : ReferenceInitializationRun.Boundary p)
    (h : b.completed < BootstrapDimensions.n_boot p)
    (actual : ActualInitializationRun.BlockCarry p rate
      (ReferenceInitializationRun.nextBlock b h))
    (past : List (ActualInitializationRun.PhysicalRoundRecord p rate source rewards))
    (hr : ActualReferenceInitializationBlock.BlockStartRelated source rewards
      C_star C_h rate (ReferenceInitializationRun.nextBlock b h) actual b past)
    (hdown : ∀ i, ¬ InitializationFailureProvenance.generatedBlockDown
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate) b h i)
    (hclean : ∀ (i : Fin (p.m - 1))
      (hi : ActualReferenceInitializationBlock.refFollower i ∈
        (ReferenceInitializationRun.physical
          (ActualReferenceInitializationBlock.referenceInput
            source rewards C_star C_h rate) b h).uninformed),
      BootstrapAllCandidateController.cleanPrefix
        (ReferenceInitializationRun.physical
          (ActualReferenceInitializationBlock.referenceInput
            source rewards C_star C_h rate) b h)
        source.1.2 ⟨ActualReferenceInitializationBlock.refFollower i, hi⟩
        (ActualInitializationPhysicalStep.selectedRowIndex p source) p.T)
    (hforce : ∀ i, ReferenceInitializationRun.forced
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
        b h i = false)
    (launch : BootstrapCoordinatorLocalRound.LaunchedBlock p)
    (learnerSeed : ActualInitializationRun.CoordinatorLearnerZeroSeed p)
    (hlaunched : (ActualInitializationRun.combinedBoundaryHandoff p rate
      (ReferenceInitializationRun.nextBlock b h) source rewards actual.C_star actual.C_h
      (ActualInitializationRun.foldBlock p rate (ReferenceInitializationRun.nextBlock b h)
        source rewards actual)).disposition = .launched launch learnerSeed)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (runRewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (totalCount : ℕ)
    (hspan : BootstrapObservedFollower.blockStop p
        (ReferenceInitializationRun.nextBlock b h) + totalCount ≤ p.T)
    (prefixLength : ℕ) (hprefix : prefixLength ≤ totalCount)
    (payload : Payload rate)
    (hstored :
      let initial := ActualInitializationLaunchState.ofActualLaunchedBoundary
        source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed
        hlaunched
      let hmode := (ReferenceAssignmentPayloadPersistence.actualBoundary_payload_mode_and_activity
        source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed
        hlaunched).2.1
      storedPayload
        ((ReferenceActivePhysicalHorizon.run initial rows selected runRewards
          (BootstrapObservedFollower.blockStop p
            (ReferenceInitializationRun.nextBlock b h)) prefixLength (by omega) hmode).finalState.coordinator)
        = some payload) :
    let initial := ActualInitializationLaunchState.ofActualLaunchedBoundary
      source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed
      hlaunched
    let hmode := (ReferenceAssignmentPayloadPersistence.actualBoundary_payload_mode_and_activity
      source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed
      hlaunched).2.1
    ∃ record,
      record ∈ (ReferenceActivePhysicalHorizon.run initial rows selected runRewards
        (BootstrapObservedFollower.blockStop p
          (ReferenceInitializationRun.nextBlock b h)) prefixLength (by omega) hmode).records ∧
      InstallationBirth record payload ∧
      record.input.time.val = payload.sigma.val ∧
      BootstrapObservedFollower.blockStop p (ReferenceInitializationRun.nextBlock b h) ≤
        payload.sigma.val ∧
      payload.sigma.val < BootstrapObservedFollower.blockStop p
        (ReferenceInitializationRun.nextBlock b h) + prefixLength := by
  let initial := ActualInitializationLaunchState.ofActualLaunchedBoundary
    source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed
    hlaunched
  let hmode := (ReferenceAssignmentPayloadPersistence.actualBoundary_payload_mode_and_activity
    source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed
    hlaunched).2.1
  have hinitial : initial.coordinator = .first := by
    dsimp [initial]
    exact ActualInitializationLaunchState.ofActualLaunchedBoundary_coordinator
      source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed
      hlaunched
  dsimp [initial, hmode] at hstored ⊢
  exact run_prefix_storedPayload_has_birth initial rows selected runRewards
    (BootstrapObservedFollower.blockStop p (ReferenceInitializationRun.nextBlock b h))
    totalCount hspan (ReferenceAssignmentPayloadPersistence.actualBoundary_payload_mode_and_activity
      source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed
      hlaunched).2.1 hinitial prefixLength hprefix payload hstored

end Bandits.Support.ReferenceAssignmentPayloadChronology

end
