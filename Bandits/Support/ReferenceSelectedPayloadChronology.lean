/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceAssignmentPayloadChronology
import Lean.Elab.Tactic.Omega

/-!
# Chronology of payloads in actual selected views

The assignment DOWN record and its immutable fields are specified in
`sources/zip4/manuscript/05_binary_transport.tex:60-78`. The same record is
sent during a live assignment and UP collection, including interruption
paths, in `sources/zip4/manuscript/06_interruptions.tex:41-70,273-282,327-348`.

For each successful selection in the accepted physical step, the selected
payload is either the whole payload stored before that step or an actual
installation in that dispatcher result. Run-prefix states and births are
derived from the accepted finite run; no selection provenance or history is
an extra input. The expected DOWN word conclusions retain their actual
selected sender branch and the original complete payload.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceAssignmentPayloadPersistence
open Bandits.Support.ReferenceAssignmentPayloadChronology
open Bandits.Support.ReferenceDownReception
open Bandits.Support.CoordinatorLocalArmChoice

namespace Bandits.Support.ReferenceSelectedPayloadChronology

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput

variable {p : Parameters} {rate : RateInput p}

private theorem selectionAt_payload_eq
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : Payload rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (time : Fin p.T)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ)
    (choice : CoordinatorRoundDispatch.ArmSelection payload started time weights x.row)
    (selected : Selection x)
    (hselection : ReferenceActivePhysicalStep.selectionAt x payload started time weights choice =
      some selected) :
    selected.view.payload = payload := by
  by_cases htime : time = x.time
  · simp only [ReferenceActivePhysicalStep.selectionAt, dif_pos htime] at hselection
    exact (congrArg (fun value : Selection x => value.view.payload)
      (Option.some.inj hselection)).symm
  · simp only [ReferenceActivePhysicalStep.selectionAt, dif_neg htime] at hselection
    cases hselection

private theorem inputCoordinator_eq_first_of_dispatch_eq_first
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (outcome : CoordinatorRoundDispatch.FirstOutcome (ReferenceActivePhysicalStep.firstInput x))
    (hdispatch : ReferenceActivePhysicalStep.dispatch x = .first outcome) :
    x.state.coordinator = .first := by
  cases hstate : x.state.coordinator with
  | first => rfl
  | live registers owned base =>
      cases hresult : CoordinatorRoundDispatch.dispatch
          (.live (ReferenceActivePhysicalStep.liveInput x registers owned base)) with
      | live actualOutcome =>
          have hcut : ReferenceActivePhysicalStep.dispatch x =
              .live registers owned base actualOutcome := by
            unfold ReferenceActivePhysicalStep.dispatch
            simp only [hstate]
            rw [hresult]
            rfl
          rw [hcut] at hdispatch
          cases hdispatch
  | collection payload ledger savedProposal =>
      by_cases hcutoff : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
      · let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
        let clock := ReferenceActivePhysicalStep.collectionClock payload ledger savedProposal cutoff
        cases hresult : CoordinatorRoundDispatch.dispatch
            (.collection (ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff)) with
        | collection actualOutcome =>
            have hcut : ReferenceActivePhysicalStep.dispatch x =
                .collection payload ledger clock cutoff actualOutcome := by
              unfold ReferenceActivePhysicalStep.dispatch
              simp only [hstate]
              simp only [dif_pos hcutoff, cutoff, clock, hresult]
              rfl
            rw [hcut] at hdispatch
            cases hdispatch
      · have hcut : ReferenceActivePhysicalStep.dispatch x = .invalidCollectionCutoff := by
          unfold ReferenceActivePhysicalStep.dispatch
          simp only [hstate]
          simp only [dif_neg hcutoff]
        rw [hcut] at hdispatch
        cases hdispatch
  | dagger =>
      have hcut : ReferenceActivePhysicalStep.dispatch x = .dagger := by
        unfold ReferenceActivePhysicalStep.dispatch
        simp only [hstate]
      rw [hcut] at hdispatch
      cases hdispatch

private theorem storedPayload_eq_of_dispatch_live
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
    (base : Fin (p.m - 1) → ℕ)
    (outcome : CoordinatorRoundDispatch.LiveOutcome
      (ReferenceActivePhysicalStep.liveInput x registers owned base))
    (hdispatch : ReferenceActivePhysicalStep.dispatch x = .live registers owned base outcome) :
    storedPayload x.state.coordinator = some registers.payload := by
  cases hstate : x.state.coordinator with
  | first =>
      cases hresult : CoordinatorRoundDispatch.dispatch
          (.first (ReferenceActivePhysicalStep.firstInput x)) with
      | first actualOutcome =>
          have hcut : ReferenceActivePhysicalStep.dispatch x = .first actualOutcome := by
            unfold ReferenceActivePhysicalStep.dispatch
            simp only [hstate]
            rw [hresult]
            rfl
          rw [hcut] at hdispatch
          cases hdispatch
  | live actualRegisters actualOwned actualBase =>
      cases hresult : CoordinatorRoundDispatch.dispatch
          (.live (ReferenceActivePhysicalStep.liveInput x actualRegisters actualOwned actualBase)) with
      | live actualOutcome =>
          have hcut : ReferenceActivePhysicalStep.dispatch x =
              .live actualRegisters actualOwned actualBase actualOutcome := by
            unfold ReferenceActivePhysicalStep.dispatch
            simp only [hstate]
            rw [hresult]
            rfl
          rw [hcut] at hdispatch
          change DispatchCut.live actualRegisters actualOwned actualBase actualOutcome =
            .live registers owned base outcome at hdispatch
          have hregisters : actualRegisters = registers := by
            injection hdispatch with hregisters _ _ _
          simp [hstate, storedPayload, hregisters]
  | collection payload ledger savedProposal =>
      by_cases hcutoff : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
      · let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
        let clock := ReferenceActivePhysicalStep.collectionClock payload ledger savedProposal cutoff
        cases hresult : CoordinatorRoundDispatch.dispatch
            (.collection (ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff)) with
        | collection actualOutcome =>
            have hcut : ReferenceActivePhysicalStep.dispatch x =
                .collection payload ledger clock cutoff actualOutcome := by
              unfold ReferenceActivePhysicalStep.dispatch
              simp only [hstate]
              simp only [dif_pos hcutoff, cutoff, clock, hresult]
              rfl
            rw [hcut] at hdispatch
            cases hdispatch
      · have hcut : ReferenceActivePhysicalStep.dispatch x = .invalidCollectionCutoff := by
          unfold ReferenceActivePhysicalStep.dispatch
          simp only [hstate]
          simp only [dif_neg hcutoff]
        rw [hcut] at hdispatch
        cases hdispatch
  | dagger =>
      have hcut : ReferenceActivePhysicalStep.dispatch x = .dagger := by
        unfold ReferenceActivePhysicalStep.dispatch
        simp only [hstate]
      rw [hcut] at hdispatch
      cases hdispatch

private theorem storedPayload_eq_of_dispatch_collection
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : Payload rate) (ledger : Ledger rate)
    (clock : CoordinatorPhaseClock.ClockRegisters p) (cutoff : Fin p.T)
    (outcome : CoordinatorRoundDispatch.CollectionOutcome
      (ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff))
    (hdispatch : ReferenceActivePhysicalStep.dispatch x =
      .collection payload ledger clock cutoff outcome) :
    storedPayload x.state.coordinator = some payload := by
  cases hstate : x.state.coordinator with
  | first =>
      cases hresult : CoordinatorRoundDispatch.dispatch
          (.first (ReferenceActivePhysicalStep.firstInput x)) with
      | first actualOutcome =>
          have hcut : ReferenceActivePhysicalStep.dispatch x = .first actualOutcome := by
            unfold ReferenceActivePhysicalStep.dispatch
            simp only [hstate]
            rw [hresult]
            rfl
          rw [hcut] at hdispatch
          cases hdispatch
  | live registers owned base =>
      cases hresult : CoordinatorRoundDispatch.dispatch
          (.live (ReferenceActivePhysicalStep.liveInput x registers owned base)) with
      | live actualOutcome =>
          have hcut : ReferenceActivePhysicalStep.dispatch x = .live registers owned base actualOutcome := by
            unfold ReferenceActivePhysicalStep.dispatch
            simp only [hstate]
            rw [hresult]
            rfl
          rw [hcut] at hdispatch
          cases hdispatch
  | collection actualPayload actualLedger savedProposal =>
      by_cases hcutoff : 1 ≤ actualLedger.cutoff ∧ actualLedger.cutoff ≤ p.T
      ·
        let actualCutoff : Fin p.T := ⟨actualLedger.cutoff - 1, by omega⟩
        let actualClock := ReferenceActivePhysicalStep.collectionClock actualPayload
          actualLedger savedProposal actualCutoff
        let actualInput := ReferenceActivePhysicalStep.collectionInput x actualPayload
          actualLedger actualClock actualCutoff
        cases hresult : CoordinatorRoundDispatch.dispatch (.collection actualInput) with
        | collection actualOutcome =>
            have hcut : ReferenceActivePhysicalStep.dispatch x =
                .collection actualPayload actualLedger actualClock actualCutoff actualOutcome := by
              unfold ReferenceActivePhysicalStep.dispatch
              simp only [hstate]
              simp only [dif_pos hcutoff, actualCutoff, actualClock, actualInput,
                hresult]
              rfl
            rw [hcut] at hdispatch
            change DispatchCut.collection actualPayload actualLedger actualClock
              actualCutoff actualOutcome = .collection payload ledger clock cutoff outcome at hdispatch
            have hpayload : actualPayload = payload := by
              injection hdispatch with hpayload _ _ _ _
            simp [hstate, storedPayload, hpayload]
      · have hcut : ReferenceActivePhysicalStep.dispatch x = .invalidCollectionCutoff := by
          unfold ReferenceActivePhysicalStep.dispatch
          simp only [hstate]
          simp only [dif_neg hcutoff]
        rw [hcut] at hdispatch
        cases hdispatch
  | dagger =>
      have hcut : ReferenceActivePhysicalStep.dispatch x = .dagger := by
        unfold ReferenceActivePhysicalStep.dispatch
        simp only [hstate]
      rw [hcut] at hdispatch
      cases hdispatch

/-- Every successful actual selection reads either the whole payload already
stored by its incoming coordinator or a payload installed by this actual
dispatcher result. The selected view, dispatcher outcome, and birth witness
all come from the record's literal output. -/
theorem actualSelectedPayload_local_stored_or_birth
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (selected : Selection record.input)
    (hselected : record.output.preparation.coordinator.selection = some selected) :
    storedPayload record.input.state.coordinator = some selected.view.payload ∨
      InstallationBirth record selected.view.payload := by
  have hactual : record.output.preparation.coordinator =
      ReferenceActivePhysicalStep.dispatch record.input := by
    rw [record.output_eq]
    exact (ReferenceActivePhysicalStep.prepare record.input).coordinator_eq
  cases hcut : record.output.preparation.coordinator with
  | first outcome =>
      cases outcome with
      | choiceDomainFailure installed =>
          simp [hcut, DispatchCut.selection] at hselected
      | recorderBoundaryFailure installed =>
          simp [hcut, DispatchCut.selection] at hselected
      | choiceRejected installed =>
          simp [hcut, DispatchCut.selection] at hselected
      | chosen installed choice =>
          have hselectionAt :
              ReferenceActivePhysicalStep.selectionAt record.input installed.registers.payload
                installed.startRoundResult installed.registers.time
                installed.registers.complementWeights choice = some selected := by
            simpa [hcut, DispatchCut.selection] using hselected
          have hviewPayload := selectionAt_payload_eq record.input installed.registers.payload
            installed.startRoundResult installed.registers.time
            installed.registers.complementWeights choice selected hselectionAt
          have hdispatch : ReferenceActivePhysicalStep.dispatch record.input =
              .first (.chosen installed choice) := by
            simpa [hcut] using hactual.symm
          have hfirst : record.input.state.coordinator = .first :=
            inputCoordinator_eq_first_of_dispatch_eq_first record.input
              (.chosen installed choice) hdispatch
          have hchosen : CoordinatorRoundDispatch.dispatchFirst
              (ReferenceActivePhysicalStep.firstInput record.input) = .chosen installed choice := by
            have h := hdispatch
            rw [ReferenceActivePhysicalStep.dispatch_first record.input hfirst] at h
            injection h with hchosen
          have hbirth : InstallationBirth record installed.registers.payload := by
            unfold InstallationBirth
            rw [hcut]
            exact ⟨rfl, ReferenceAssignmentPayloadPersistence.firstChosen_payload_time
              record.input installed choice hchosen⟩
          exact Or.inr (by simpa [hviewPayload] using hbirth)
  | live registers owned base outcome =>
      cases outcome with
      | clockFailure failure dispatch_eq =>
          simp [hcut, DispatchCut.selection] at hselected
      | initializerFailure dispatched startRound_eq checked checked_eq =>
          simp [hcut, DispatchCut.selection] at hselected
      | localFailure dispatched startRound_eq reason =>
          simp [hcut, DispatchCut.selection] at hselected
      | cutoffChosen dispatched startRound_eq ledger initialization_eq ledger_eq_candidate
          initializationDomainValid cutoff_clock cutoff_pending no_assignment choice =>
          have hselectionAt :
              ReferenceActivePhysicalStep.selectionAt record.input registers.payload
                dispatched.startResult record.input.time
                (ReferenceActivePhysicalStep.liveRegistersAt registers record.input.time).complementWeights
                choice = some selected := by
            simpa [hcut, DispatchCut.selection] using hselected
          have hviewPayload := selectionAt_payload_eq record.input registers.payload
            dispatched.startResult record.input.time
            (ReferenceActivePhysicalStep.liveRegistersAt registers record.input.time).complementWeights
            choice selected hselectionAt
          have hdispatch : ReferenceActivePhysicalStep.dispatch record.input =
              .live registers owned base
                (.cutoffChosen dispatched startRound_eq ledger initialization_eq ledger_eq_candidate
                  initializationDomainValid cutoff_clock cutoff_pending no_assignment choice) := by
            simpa [hcut] using hactual.symm
          have hstored := storedPayload_eq_of_dispatch_live record.input registers owned base
            (.cutoffChosen dispatched startRound_eq ledger initialization_eq ledger_eq_candidate
              initializationDomainValid cutoff_clock cutoff_pending no_assignment choice) hdispatch
          exact Or.inl (hstored.trans (congrArg some hviewPayload.symm))
      | continuingChosen dispatched startRound_eq continuation choice =>
          have hselectionAt :
              ReferenceActivePhysicalStep.selectionAt record.input registers.payload
                dispatched.startResult record.input.time
                (ReferenceActivePhysicalStep.liveRegistersAt registers record.input.time).complementWeights
                choice = some selected := by
            simpa [hcut, DispatchCut.selection] using hselected
          have hviewPayload := selectionAt_payload_eq record.input registers.payload
            dispatched.startResult record.input.time
            (ReferenceActivePhysicalStep.liveRegistersAt registers record.input.time).complementWeights
            choice selected hselectionAt
          have hdispatch : ReferenceActivePhysicalStep.dispatch record.input =
              .live registers owned base
                (.continuingChosen dispatched startRound_eq continuation choice) := by
            simpa [hcut] using hactual.symm
          have hstored := storedPayload_eq_of_dispatch_live record.input registers owned base
            (.continuingChosen dispatched startRound_eq continuation choice) hdispatch
          exact Or.inl (hstored.trans (congrArg some hviewPayload.symm))
  | collection payload ledger clock cutoff outcome =>
      cases outcome with
      | clockFailure failure startRound_eq =>
          simp [hcut, DispatchCut.selection] at hselected
      | localFailure started startRound_eq core_invalid reason =>
          simp [hcut, DispatchCut.selection] at hselected
      | coreFailure core started startRound_eq reason =>
          simp [hcut, DispatchCut.selection] at hselected
      | continuing core prepared boundary currentScoresChecked =>
          have hselection :
              (DispatchCut.collection payload ledger clock cutoff
                (.continuing core prepared boundary currentScoresChecked)).selection = some selected := by
            rw [← hcut]
            exact hselected
          have hviewPayload : selected.view.payload = payload := by
            have hmapped :
                (DispatchCut.collection payload ledger clock cutoff
                  (.continuing core prepared boundary currentScoresChecked)).selection.map
                    (fun value => value.view.payload) = some payload := by
              simp [DispatchCut.selection]
            rw [hselection] at hmapped
            exact Option.some.inj hmapped
          have hdispatch : ReferenceActivePhysicalStep.dispatch record.input =
              .collection payload ledger clock cutoff
                (.continuing core prepared boundary currentScoresChecked) := by
            simpa [hcut] using hactual.symm
          have hstored := storedPayload_eq_of_dispatch_collection record.input payload ledger
            clock cutoff (.continuing core prepared boundary currentScoresChecked) hdispatch
          exact Or.inl (hstored.trans (congrArg some hviewPayload.symm))
      | laterReconstructionFailure core consistent started startRound_eq instruction
          assignmentStart_eq reason later_eq =>
          simp [hcut, DispatchCut.selection] at hselected
      | laterPrefixFailure core consistent started startRound_eq instruction
          assignmentStart_eq arm reason later_eq =>
          simp [hcut, DispatchCut.selection] at hselected
      | laterOrientationFailure core consistent started startRound_eq instruction
          assignmentStart_eq set later_eq =>
          simp [hcut, DispatchCut.selection] at hselected
      | laterChoiceFailure core consistent started startRound_eq instruction
          assignmentStart_eq output consistency clockData installed reason =>
          simp [hcut, DispatchCut.selection] at hselected
      | laterChosen core consistent started startRound_eq instruction assignmentStart_eq
          output consistency clockData installed choice =>
          have hselectionAt :
              ReferenceActivePhysicalStep.selectionAt record.input installed.registers.payload
                started instruction.time installed.registers.complementWeights choice =
                  some selected := by
            simpa [hcut, DispatchCut.selection] using hselected
          have hviewPayload := selectionAt_payload_eq record.input installed.registers.payload
            started instruction.time installed.registers.complementWeights choice selected hselectionAt
          have hbirth : InstallationBirth record installed.registers.payload := by
            have h := ReferenceLaterInstallationProvenance.record_laterChosen_birth record
            simpa [hcut] using h
          exact Or.inr (by simpa [hviewPayload] using hbirth)
  | invalidCollectionCutoff =>
      simp [hcut, DispatchCut.selection] at hselected
  | dagger =>
      simp [hcut, DispatchCut.selection] at hselected

private theorem Connected.functional {initial finalLeft finalRight :
    ReferenceActivePhysicalStep.State p rate}
    {records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))}
    (hleft : ReferenceActivePhysicalHorizon.Connected initial records finalLeft)
    (hright : ReferenceActivePhysicalHorizon.Connected initial records finalRight) :
    finalLeft = finalRight := by
  induction records generalizing initial finalLeft finalRight with
  | nil =>
      change finalLeft = initial at hleft
      change finalRight = initial at hright
      exact hleft.trans hright.symm
  | cons record rest ih =>
      simp only [ReferenceActivePhysicalHorizon.Connected] at hleft hright
      exact ih hleft.2 hright.2

private theorem Connected.append_one_parts
    {initial final : ReferenceActivePhysicalStep.State p rate}
    {records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))}
    {record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)}
    (hconnected : ReferenceActivePhysicalHorizon.Connected initial
      (records ++ [record]) final) :
    ∃ current,
      ReferenceActivePhysicalHorizon.Connected initial records current ∧
      record.input.state = current ∧ final = record.output.next := by
  induction records generalizing initial final with
  | nil =>
      simp only [List.nil_append, ReferenceActivePhysicalHorizon.Connected] at hconnected
      rcases hconnected with ⟨hpre, hfinal⟩
      exact ⟨initial, by simp [ReferenceActivePhysicalHorizon.Connected], hpre, hfinal⟩
  | cons head rest ih =>
      simp only [List.cons_append, ReferenceActivePhysicalHorizon.Connected] at hconnected
      rcases hconnected with ⟨hhead, hrest⟩
      obtain ⟨current, hprefix, hpre, hfinal⟩ := ih hrest
      exact ⟨current, ⟨hhead, hprefix⟩, hpre, hfinal⟩

/-- A record in the accepted finite run is exactly the actual record at a
genuine prefix boundary. Its time and input state are derived from the
successor step and the connected run. -/
theorem actualRunRecord_has_prefix
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selectedRow : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hrecord : record ∈ (ReferenceActivePhysicalHorizon.run initial rows selectedRow rewards
      start count hspan hmode).records) :
    ∃ prefixLength, ∃ hprefix : prefixLength < count,
      record.input.time.val = start + prefixLength ∧
      record.input.state = (ReferenceActivePhysicalHorizon.run initial rows selectedRow rewards
        start prefixLength (by omega) hmode).finalState := by
  induction count with
  | zero =>
      have hrecords := ReferenceActivePhysicalHorizon.run_zero_records initial rows selectedRow
        rewards start hspan hmode
      rw [hrecords] at hrecord
      exact False.elim (List.not_mem_nil hrecord)
  | succ count ih =>
      have hsuccessor := ReferenceActivePhysicalHorizon.run_successor_step initial rows selectedRow
        rewards start count hspan hmode
      have hrecords :
          (ReferenceActivePhysicalHorizon.run initial rows selectedRow rewards start
            (count + 1) hspan hmode).records =
            (ReferenceActivePhysicalHorizon.run initial rows selectedRow rewards start
              count (by omega) hmode).records ++
              [actualRunRecordAt initial rows selectedRow rewards start count hspan hmode] := by
        rw [hsuccessor]
        rfl
      rw [hrecords] at hrecord
      rcases List.mem_append.mp hrecord with hprefix | hlast
      · obtain ⟨prefixLength, hlt, htime, hstate⟩ := ih (by omega) hprefix
        exact ⟨prefixLength, by omega, htime, hstate⟩
      · have hrecordEq : record = actualRunRecordAt initial rows selectedRow rewards
          start count hspan hmode := List.mem_singleton.mp hlast
        subst record
        let prefixRun := ReferenceActivePhysicalHorizon.run initial rows selectedRow rewards
          start count (by omega) hmode
        have hconnected := ReferenceActivePhysicalHorizon.run_connected initial rows selectedRow
          rewards start (count + 1) hspan hmode
        rw [hrecords] at hconnected
        obtain ⟨current, hprefixConnected, hpre, _⟩ := Connected.append_one_parts hconnected
        have hpriorConnected := ReferenceActivePhysicalHorizon.run_connected initial rows selectedRow
          rewards start count (by omega) hmode
        have hcurrent : current = prefixRun.finalState := by
          exact Connected.functional hprefixConnected (by simpa [prefixRun] using hpriorConnected)
        exact ⟨count, by omega, rfl, hpre.trans hcurrent⟩

private theorem foldCalendar_contains_acc_record
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selectedRow : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (origin intervalStart count : ℕ) (horigin : origin ≤ intervalStart)
    (hspan : intervalStart + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial origin)
    (acc : ReferenceActivePhysicalHorizon.Run initial)
    {record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)}
    (hrecord : record ∈ acc.records) :
    record ∈ (ReferenceActivePhysicalHorizon.foldCalendar initial rows selectedRow rewards
      origin intervalStart count horigin hspan hmode acc).records := by
  change record ∈
    ((ReferenceActivePhysicalHorizon.calendarEntries origin intervalStart count horigin hspan).foldl
      (ReferenceActivePhysicalHorizon.foldRound initial rows selectedRow rewards origin hmode) acc).records
  induction ReferenceActivePhysicalHorizon.calendarEntries origin intervalStart count
      horigin hspan generalizing acc with
  | nil => simpa
  | cons entry rest ih =>
      simp only [List.foldl_cons]
      apply ih
      change record ∈ acc.records ++ [_]
      exact List.mem_append_left _ hrecord

private theorem run_prefix_record_mem
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selectedRow : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start totalCount : ℕ) (hspan : start + totalCount ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (prefixLength : ℕ) (hprefix : prefixLength ≤ totalCount)
    {record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)}
    (hrecord : record ∈ (ReferenceActivePhysicalHorizon.run initial rows selectedRow rewards
      start prefixLength (by omega) hmode).records) :
    record ∈ (ReferenceActivePhysicalHorizon.run initial rows selectedRow rewards
      start totalCount hspan hmode).records := by
  have hsplit : prefixLength + (totalCount - prefixLength) = totalCount :=
    Nat.add_sub_of_le hprefix
  have happend := ReferenceActivePhysicalHorizon.run_append initial rows selectedRow rewards
    start prefixLength (totalCount - prefixLength) (by omega) hmode
  have happend' :
      ReferenceActivePhysicalHorizon.run initial rows selectedRow rewards
        start totalCount hspan hmode =
      ReferenceActivePhysicalHorizon.foldCalendar initial rows selectedRow rewards
        start (start + prefixLength) (totalCount - prefixLength) (by omega) (by omega) hmode
        (ReferenceActivePhysicalHorizon.run initial rows selectedRow rewards
          start prefixLength (by omega) hmode) := by
    simpa [hsplit] using happend
  rw [happend']
  exact foldCalendar_contains_acc_record initial rows selectedRow rewards start
    (start + prefixLength) (totalCount - prefixLength) (by omega) (by omega) hmode _ hrecord

/-- Every selected payload in this original finite run has a genuine
installation record in the same run. The birth time is its sigma and is no
later than the selected record, even when a chosen installation's following
tail failure leaves no payload in the next state. -/
theorem actualRun_selectedPayload_has_birth
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selectedRow : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start totalCount : ℕ) (hspan : start + totalCount ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hinitial : initial.coordinator = .first)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (selected : Selection record.input)
    (hrecord : record ∈ (ReferenceActivePhysicalHorizon.run initial rows selectedRow rewards
      start totalCount hspan hmode).records)
    (hselected : record.output.preparation.coordinator.selection = some selected) :
    ∃ birthRecord,
      birthRecord ∈ (ReferenceActivePhysicalHorizon.run initial rows selectedRow rewards
        start totalCount hspan hmode).records ∧
      InstallationBirth birthRecord selected.view.payload ∧
      birthRecord.input.time.val = selected.view.payload.sigma.val ∧
      selected.view.payload.sigma.val ≤ record.input.time.val := by
  obtain ⟨prefixLength, hprefix, htime, hstate⟩ := actualRunRecord_has_prefix initial rows selectedRow
    rewards start totalCount hspan hmode record hrecord
  have hlocal := actualSelectedPayload_local_stored_or_birth record selected hselected
  rcases hlocal with hstored | hbirth
  · have hstoredPrefix : storedPayload
        ((ReferenceActivePhysicalHorizon.run initial rows selectedRow rewards start prefixLength
          (by omega) hmode).finalState.coordinator) = some selected.view.payload := by
      rw [← hstate]
      exact hstored
    obtain ⟨birthRecord, hbirthMem, hbirth, hbirthTime, _, hbirthBeforePrefix⟩ :=
      run_prefix_storedPayload_has_birth initial rows selectedRow rewards start totalCount hspan
        hmode hinitial prefixLength (by omega) selected.view.payload hstoredPrefix
    have hbirthMemFull := run_prefix_record_mem initial rows selectedRow rewards start totalCount
      hspan hmode prefixLength (by omega) hbirthMem
    exact ⟨birthRecord, hbirthMemFull, hbirth, hbirthTime, by omega⟩
  · have hbirthTime := installationBirth_time_eq record selected.view.payload hbirth
    exact ⟨record, hrecord, hbirth, hbirthTime.symm, by omega⟩

/-- Two actual selected payloads in one run are equal in every field whenever
their assignment sigma values agree. Both local selection inputs and both
installation records are derived from this same accepted run. -/
theorem run_two_actualSelectedPayloads_eq_of_equal_sigma
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selectedRow : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start totalCount : ℕ) (hspan : start + totalCount ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hinitial : initial.coordinator = .first)
    (leftRecord rightRecord : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (leftSelected : Selection leftRecord.input) (rightSelected : Selection rightRecord.input)
    (hleftRecord : leftRecord ∈
      (ReferenceActivePhysicalHorizon.run initial rows selectedRow rewards start totalCount
        hspan hmode).records)
    (hrightRecord : rightRecord ∈
      (ReferenceActivePhysicalHorizon.run initial rows selectedRow rewards start totalCount
        hspan hmode).records)
    (hleftSelected : leftRecord.output.preparation.coordinator.selection = some leftSelected)
    (hrightSelected : rightRecord.output.preparation.coordinator.selection = some rightSelected)
    (hsigma : leftSelected.view.payload.sigma.val = rightSelected.view.payload.sigma.val) :
    leftSelected.view.payload = rightSelected.view.payload := by
  obtain ⟨leftBirth, hleftBirthMem, hleftBirth, _, _⟩ :=
    actualRun_selectedPayload_has_birth initial rows selectedRow rewards start totalCount hspan
      hmode hinitial leftRecord leftSelected hleftRecord hleftSelected
  obtain ⟨rightBirth, hrightBirthMem, hrightBirth, _, _⟩ :=
    actualRun_selectedPayload_has_birth initial rows selectedRow rewards start totalCount hspan
      hmode hinitial rightRecord rightSelected hrightRecord hrightSelected
  exact run_birth_payload_eq_of_equal_sigma initial rows selectedRow rewards start totalCount
    hspan hmode leftBirth rightBirth leftSelected.view.payload rightSelected.view.payload
    hleftBirthMem hrightBirthMem hleftBirth hrightBirth hsigma

/-- Actual selected payloads with equal sigma carry exactly equal DOWN
records, including the original queue seed `q`. This supplies fixed-DOWN
batch coverage and current-offer consistency from whole-payload identity. -/
theorem run_two_actualSelectedPayloads_downRecord_eq_of_equal_sigma
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selectedRow : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start totalCount : ℕ) (hspan : start + totalCount ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hinitial : initial.coordinator = .first)
    (leftRecord rightRecord : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (leftSelected : Selection leftRecord.input) (rightSelected : Selection rightRecord.input)
    (hleftRecord : leftRecord ∈
      (ReferenceActivePhysicalHorizon.run initial rows selectedRow rewards start totalCount
        hspan hmode).records)
    (hrightRecord : rightRecord ∈
      (ReferenceActivePhysicalHorizon.run initial rows selectedRow rewards start totalCount
        hspan hmode).records)
    (hleftSelected : leftRecord.output.preparation.coordinator.selection = some leftSelected)
    (hrightSelected : rightRecord.output.preparation.coordinator.selection = some rightSelected)
    (hsigma : leftSelected.view.payload.sigma.val = rightSelected.view.payload.sigma.val)
    (i : ActiveRoundActions.Follower p.m) :
    leftSelected.view.payload.downRecord i = rightSelected.view.payload.downRecord i := by
  exact downRecord_eq_of_payload_eq leftSelected.view.payload rightSelected.view.payload
    (run_two_actualSelectedPayloads_eq_of_equal_sigma initial rows selectedRow rewards start
      totalCount hspan hmode hinitial leftRecord rightRecord leftSelected rightSelected
      hleftRecord hrightRecord hleftSelected hrightSelected hsigma) i

/-- The expected word on the selected record's actual pending DOWN sender
branch is encoded by the other equal-sigma selected payload. The branch
condition remains explicit, and the word uses the original stored payload. -/
theorem run_two_actualSelectedPayloads_expectedDownFlatWord_of_equal_sigma
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selectedRow : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start totalCount : ℕ) (hspan : start + totalCount ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hinitial : initial.coordinator = .first)
    (leftRecord rightRecord : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (leftSelected : Selection leftRecord.input) (rightSelected : Selection rightRecord.input)
    (hleftRecord : leftRecord ∈
      (ReferenceActivePhysicalHorizon.run initial rows selectedRow rewards start totalCount
        hspan hmode).records)
    (hrightRecord : rightRecord ∈
      (ReferenceActivePhysicalHorizon.run initial rows selectedRow rewards start totalCount
        hspan hmode).records)
    (hleftSelected : leftRecord.output.preparation.coordinator.selection = some leftSelected)
    (hrightSelected : rightRecord.output.preparation.coordinator.selection = some rightSelected)
    (hsigma : leftSelected.view.payload.sigma.val = rightSelected.view.payload.sigma.val)
    (i : ActiveRoundActions.Follower p.m)
    (hbranch : selectedDownSenderBranch leftSelected.view i leftRecord.input.row
      leftRecord.input.time) :
    expectedDownFlatWord (some leftSelected.view) i leftRecord.input.row leftRecord.input.time =
      some (storedDownFlatWord rightSelected.view.payload i) := by
  have hpayload := run_two_actualSelectedPayloads_eq_of_equal_sigma initial rows selectedRow
    rewards start totalCount hspan hmode hinitial leftRecord rightRecord leftSelected rightSelected
    hleftRecord hrightRecord hleftSelected hrightSelected hsigma
  exact (actualSelection_expectedDownFlatWord_of_payload_eq leftRecord leftSelected hleftSelected
    rightSelected.view.payload hpayload i hbranch).1

/-- An actual selected payload agrees in every field with any endpoint payload
stored at a genuine prefix of the same run when their sigma values agree. The
prefix state and the selected record's installation are both produced from
the original run. -/
theorem run_actualSelectedPayload_eq_of_prefix_storedPayload_equal_sigma
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selectedRow : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start totalCount : ℕ) (hspan : start + totalCount ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hinitial : initial.coordinator = .first)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (selected : Selection record.input)
    (hrecord : record ∈
      (ReferenceActivePhysicalHorizon.run initial rows selectedRow rewards start totalCount
        hspan hmode).records)
    (hselected : record.output.preparation.coordinator.selection = some selected)
    (endpointPrefix : ℕ) (hendpointPrefix : endpointPrefix ≤ totalCount)
    (endpointPayload : Payload rate)
    (hendpoint : storedPayload
      (ReferenceActivePhysicalHorizon.run initial rows selectedRow rewards start endpointPrefix
        (by omega) hmode).finalState.coordinator = some endpointPayload)
    (hsigma : selected.view.payload.sigma.val = endpointPayload.sigma.val) :
    selected.view.payload = endpointPayload ∧
      selectedPayload record = some endpointPayload := by
  obtain ⟨selectedBirth, hselectedBirthMem, hselectedBirth, _, _⟩ :=
    actualRun_selectedPayload_has_birth initial rows selectedRow rewards start totalCount hspan
      hmode hinitial record selected hrecord hselected
  obtain ⟨endpointBirth, hendpointBirthMemPrefix, hendpointBirth, _, _⟩ :=
    run_prefix_storedPayload_has_birth initial rows selectedRow rewards start totalCount hspan
      hmode hinitial endpointPrefix hendpointPrefix endpointPayload hendpoint
  have hendpointBirthMem := run_prefix_record_mem initial rows selectedRow rewards start totalCount
    hspan hmode endpointPrefix hendpointPrefix hendpointBirthMemPrefix
  have hpayload := run_birth_payload_eq_of_equal_sigma initial rows selectedRow rewards start
    totalCount hspan hmode selectedBirth endpointBirth selected.view.payload endpointPayload
    hselectedBirthMem hendpointBirthMem hselectedBirth hendpointBirth hsigma
  have hprojection := selectedPayload_eq_of_actualSelection record selected hselected
  exact ⟨hpayload, hprojection.trans (congrArg some hpayload)⟩

/-- Every follower's DOWN record on an actual selected choice agrees with a
genuine equal-sigma prefix endpoint, preserving all fields including its
original `q` seed. -/
theorem run_actualSelectedPayload_downRecord_eq_of_prefix_storedPayload_equal_sigma
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selectedRow : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start totalCount : ℕ) (hspan : start + totalCount ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hinitial : initial.coordinator = .first)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (selected : Selection record.input)
    (hrecord : record ∈
      (ReferenceActivePhysicalHorizon.run initial rows selectedRow rewards start totalCount
        hspan hmode).records)
    (hselected : record.output.preparation.coordinator.selection = some selected)
    (endpointPrefix : ℕ) (hendpointPrefix : endpointPrefix ≤ totalCount)
    (endpointPayload : Payload rate)
    (hendpoint : storedPayload
      (ReferenceActivePhysicalHorizon.run initial rows selectedRow rewards start endpointPrefix
        (by omega) hmode).finalState.coordinator = some endpointPayload)
    (hsigma : selected.view.payload.sigma.val = endpointPayload.sigma.val)
    (i : ActiveRoundActions.Follower p.m) :
    selected.view.payload.downRecord i = endpointPayload.downRecord i := by
  exact downRecord_eq_of_payload_eq selected.view.payload endpointPayload
    (run_actualSelectedPayload_eq_of_prefix_storedPayload_equal_sigma initial rows selectedRow
      rewards start totalCount hspan hmode hinitial record selected hrecord hselected endpointPrefix
      hendpointPrefix endpointPayload hendpoint hsigma).1 i

/-- On the actual selected pending DOWN sender branch, the expected flat word
is the one encoded by a genuine equal-sigma prefix endpoint. The full original
word and the branch selector are retained for sparse-recovery consumers. -/
theorem run_actualSelectedPayload_expectedDownFlatWord_of_prefix_storedPayload_equal_sigma
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selectedRow : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start totalCount : ℕ) (hspan : start + totalCount ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hinitial : initial.coordinator = .first)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (selected : Selection record.input)
    (hrecord : record ∈
      (ReferenceActivePhysicalHorizon.run initial rows selectedRow rewards start totalCount
        hspan hmode).records)
    (hselected : record.output.preparation.coordinator.selection = some selected)
    (endpointPrefix : ℕ) (hendpointPrefix : endpointPrefix ≤ totalCount)
    (endpointPayload : Payload rate)
    (hendpoint : storedPayload
      (ReferenceActivePhysicalHorizon.run initial rows selectedRow rewards start endpointPrefix
        (by omega) hmode).finalState.coordinator = some endpointPayload)
    (hsigma : selected.view.payload.sigma.val = endpointPayload.sigma.val)
    (i : ActiveRoundActions.Follower p.m)
    (hbranch : selectedDownSenderBranch selected.view i record.input.row record.input.time) :
    expectedDownFlatWord (some selected.view) i record.input.row record.input.time =
      some (storedDownFlatWord endpointPayload i) := by
  have hpayload := run_actualSelectedPayload_eq_of_prefix_storedPayload_equal_sigma initial rows
    selectedRow rewards start totalCount hspan hmode hinitial record selected hrecord hselected
    endpointPrefix hendpointPrefix endpointPayload hendpoint hsigma
  exact (actualSelection_expectedDownFlatWord_of_payload_eq record selected hselected
    endpointPayload hpayload.1 i hbranch).1

end Bandits.Support.ReferenceSelectedPayloadChronology

end
