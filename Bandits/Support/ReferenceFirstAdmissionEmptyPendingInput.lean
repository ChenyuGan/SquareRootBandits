/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedFirstCollectionAdmissionBoundary

import Lean.Elab.Tactic.Omega

/-!
# Original next input after an empty-pending first admission

At an accepted first-collection FINISH whose actual pending set is empty, the
next input is constructed from the accepted output's original physical prefix.
The result keeps every FINISH ledger, row, decoder-bank, and register fact
literal. It also retains the terminal prefix state at `T`, without constructing
a round input there. A finite-run record equality is asserted only when that
record belongs to the requested run.

Mathematical sources: `sources/zip4/manuscript/06_interruptions.tex:9-100,
246-299`, `sources/zip4/manuscript/appendix_a_local_protocol.tex:28-82`, and
`sources/zip4/manuscript/04_slow_fast_learner.tex:97-174,219-243`.
-/

@[expose] public section

noncomputable section

open Bandits.Support

namespace Bandits.Support.ReferenceFirstAdmissionEmptyPendingInput

private theorem original_run_record_input_eq_prefix
    {p : ConstructorDimensions.Parameters}
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p)
    (selected : Fin (ConstructorDimensions.M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (j : ℕ) (hj : j < count) :
    ((ReferenceActivePhysicalHorizon.run initial rows selected rewards start count
      hspan hmode).records[j]'(by
        rw [ReferenceActivePhysicalHorizon.run_record_count]
        exact hj)).input =
      ReferenceActivePhysicalHorizon.roundInputAt initial rows selected rewards start
        hmode (ReferenceActivePhysicalHorizon.run initial rows selected rewards start j
          (by omega) hmode) ⟨start + j, by omega, by omega⟩ := by
  let actual := ReferenceAssignmentPayloadChronology.actualRunRecordAt initial rows selected
    rewards start j (by omega) hmode
  have hsuccessor :=
    ReferenceAssignmentPayloadChronology.run_successor_actualRunRecordAt
      initial rows selected rewards start j (by omega) hmode
  obtain ⟨suffix, hprefix⟩ := ReferenceCollectionPhaseHistory.run_records_prefix
    initial rows selected rewards start (j + 1) (count - (j + 1)) (by omega) hmode
  have hprefixCount :
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count
        hspan hmode).records =
        (ReferenceActivePhysicalHorizon.run initial rows selected rewards start (j + 1)
          (by omega) hmode).records ++ suffix := by
    simpa [Nat.add_sub_of_le (by omega : j + 1 ≤ count)] using hprefix
  have hjFull : j <
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count
        hspan hmode).records.length := by
    rw [ReferenceActivePhysicalHorizon.run_record_count]
    exact hj
  have hjPrefix : j <
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start (j + 1)
        (by omega) hmode).records.length := by
    rw [ReferenceActivePhysicalHorizon.run_record_count]
    omega
  have hprefixAt := List.getElem_of_eq hprefixCount hjFull
  have hsuccessorAt := List.getElem_of_eq hsuccessor hjPrefix
  have hprefixAt' :
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count
        hspan hmode).records.get ⟨j, hjFull⟩ =
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start (j + 1)
        (by omega) hmode).records.get ⟨j, hjPrefix⟩ := by
    simpa [List.getElem_append, ReferenceActivePhysicalHorizon.run_record_count] using
      hprefixAt
  have hsuccessorAt' :
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start (j + 1)
        (by omega) hmode).records.get ⟨j, hjPrefix⟩ = actual := by
    simpa [actual, List.getElem_append, ReferenceActivePhysicalHorizon.run_record_count] using
      hsuccessorAt
  have hactual :
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count
        hspan hmode).records.get ⟨j, hjFull⟩ = actual :=
    hprefixAt'.trans hsuccessorAt'
  change ((ReferenceActivePhysicalHorizon.run initial rows selected rewards start count
      hspan hmode).records.get ⟨j, hjFull⟩).input = _
  rw [hactual]
  rfl

private theorem round_input_ext
    {p : ConstructorDimensions.Parameters}
    {rate : ReferenceActivePhysicalStep.RateInput p}
    {left right : ReferenceActivePhysicalStep.RoundInput p rate}
    (hstate : left.state = right.state) (hrows : left.rows = right.rows)
    (hselected : left.selected = right.selected) (htime : left.time = right.time)
    (hrewards : left.rewards = right.rewards) : left = right := by
  cases left
  cases right
  cases hstate
  cases hrows
  cases hselected
  cases htime
  cases hrewards
  rfl

/-- Literal state and ledger facts at the empty-pending FINISH boundary,
together with the actual next input whenever its calendar index is below `T`.
The finite original run is used only for the guarded existing-record equation.
The structure is conditional on an empty pending set at the produced boundary;
it makes no claim that every first admission has that property. -/
structure EmptyPendingBoundaryOutput
    {p : ConstructorDimensions.Parameters}
    {rate : ReferenceActivePhysicalStep.RateInput p}
    {source : ReferenceGeneratedFirstCollectionAdmission.SourceInput p}
    {wholeRewards : ReferenceGeneratedFirstCollectionAdmission.RewardTable p}
    {C_star C_h : ℝ}
    {hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source wholeRewards C_star C_h rate)).crossing.isSome = true}
    {s : ℕ}
    {hsElapsed : s = ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source wholeRewards C_star C_h rate)).completed}
    {count : ℕ} {hspan : s + count ≤ p.T}
    {execution : ReferenceActivePhysicalHorizon.Run
      (ReferenceFirstLaunchNumericalCell.launchState rate source wholeRewards C_star C_h hcross)}
    {window : List (ReferenceGeneratedFirstCollectionAdmission.Record p rate)}
    {payload : ReferenceGeneratedFirstCollectionAdmission.Payload p rate}
    {ledger : ReferenceGeneratedFirstCollectionAdmission.Ledger p rate}
    {saved : Option (Fin p.T × Bool)} {w qLength k : ℕ}
    (admission : ReferenceGeneratedFirstCollectionAdmission.AcceptedAdmissionOutput
      source wholeRewards C_star C_h hcross s hsElapsed count hspan execution window
      payload ledger saved w qLength k)
    (boundary : ReferenceGeneratedFirstCollectionAdmissionBoundary.AcceptedBoundaryOutput
      admission) : Type where
  pending_empty : boundary.finished.pending = ∅
  prefixState : ReferenceActivePhysicalHorizon.State p rate
  prefixState_is_actual_next : prefixState = admission.actualPrefixNext.finalState
  prefixState_is_record_next : prefixState = admission.record.output.next
  finished_coordinator : prefixState.coordinator = .collection payload boundary.finished saved
  finished_valid :
    CoordinatorCollectionLedger.validLedgerCheck boundary.finished = true
  finished_ready :
    boundary.finished.phase = CoordinatorCollectionLedger.Phase.ready
  finished_sigma : boundary.finished.sigma = payload.sigma.val + 1
  finished_sigma_lt_cutoff : boundary.finished.sigma < boundary.finished.cutoff
  finished_cutoff_lt_cursor : boundary.finished.cutoff < boundary.finished.cursor
  finished_cursor : boundary.finished.cursor = s + k + 2
  finished_freezeAt :
    boundary.finished.freezeAt = FollowerCutoffScan.gridBoundary p rate.eta.val payload.sigma
  finished_assignment : boundary.finished.assignment.arm = payload.assignment.assigned
  finished_anchor : ∀ a, payload.anchor a = 1
  finished_joint_mass :
    ∀ a c q, boundary.finished.cutoffRegisters a = some c →
      boundary.finished.currentRegisters a = some q →
      c.score + boundary.finished.increment a + q.queue ≤
        (boundary.finished.cursor - boundary.finished.sigma) * ConstructorDimensions.D p
  finished_joint_service :
    ∀ a c q, boundary.finished.cutoffRegisters a = some c →
      boundary.finished.currentRegisters a = some q →
      c.score + boundary.finished.increment a ≤
        4 * rate.n * (min boundary.finished.cursor boundary.finished.freezeAt -
          boundary.finished.sigma)
  decoder_bank_check :
    CoordinatorUpReception.decoderBankCheck p prefixState.upDecoderBank = true
  all_registers_known :
    ∀ a, ∃ q, boundary.finished.currentRegisters a = some q ∧
      ∃ c, boundary.finished.cutoffRegisters a = some c
  actual_run_record_count : admission.actualRun.records.length = count
  next_input :
    ∀ hbefore : s + k + 1 < p.T,
      ∃ next : ReferenceActivePhysicalStep.RoundInput p rate,
        next = ReferenceActivePhysicalHorizon.roundInputAt
          (ReferenceFirstCollectionEpochAlignment.actualLaunchState
            rate source wholeRewards C_star C_h hcross)
          source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
          wholeRewards
          (ReferenceInitializationRun.elapsed p
            (ReferenceInitializationRun.output
              (ActualReferenceInitializationBlock.referenceInput
                source wholeRewards C_star C_h rate)).completed)
          admission.actualMode admission.actualPrefixNext
          ⟨s + k + 1, by omega, hbefore⟩ ∧
        next.state = admission.actualPrefixNext.finalState ∧
        next.state = admission.record.output.next ∧
        next.rows = source.1.2 ∧
        next.selected = ActualInitializationPhysicalStep.selectedRowIndex p source ∧
        next.rewards = wholeRewards ∧
        next.time.val = s + k + 1 ∧
        boundary.finished.cursor = next.time.val + 1 ∧
        CoordinatorUpReception.decoderBankCheck p next.state.upDecoderBank = true ∧
        (∀ (hnext : k + 1 < count),
          next = (admission.actualRun.records[k + 1]'(by
            rw [ReferenceGeneratedFirstCollectionAdmissionBoundary.admission_actual_run_record_count
              admission]
            exact hnext)).input)
  terminal_cursor : s + k + 1 = p.T → boundary.finished.cursor = p.T + 1
  prefix_next_is_execution_final_when_last :
    k + 1 = count → prefixState = execution.finalState

private def empty_pending_boundary_output
    {p : ConstructorDimensions.Parameters}
    {rate : ReferenceActivePhysicalStep.RateInput p}
    {source : ReferenceGeneratedFirstCollectionAdmission.SourceInput p}
    {wholeRewards : ReferenceGeneratedFirstCollectionAdmission.RewardTable p}
    {C_star C_h : ℝ}
    {hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source wholeRewards C_star C_h rate)).crossing.isSome = true}
    {s : ℕ}
    {hsElapsed : s = ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source wholeRewards C_star C_h rate)).completed}
    {count : ℕ} {hspan : s + count ≤ p.T}
    {execution : ReferenceActivePhysicalHorizon.Run
      (ReferenceFirstLaunchNumericalCell.launchState rate source wholeRewards C_star C_h hcross)}
    {window : List (ReferenceGeneratedFirstCollectionAdmission.Record p rate)}
    {payload : ReferenceGeneratedFirstCollectionAdmission.Payload p rate}
    {ledger : ReferenceGeneratedFirstCollectionAdmission.Ledger p rate}
    {saved : Option (Fin p.T × Bool)} {w qLength k : ℕ}
    (admission : ReferenceGeneratedFirstCollectionAdmission.AcceptedAdmissionOutput
      source wholeRewards C_star C_h hcross s hsElapsed count hspan execution window
      payload ledger saved w qLength k)
    (boundary : ReferenceGeneratedFirstCollectionAdmissionBoundary.AcceptedBoundaryOutput
      admission)
    (hempty : boundary.finished.pending = ∅) : EmptyPendingBoundaryOutput admission boundary := by
  classical
  let prefixState := admission.actualPrefixNext.finalState
  have hemptyErase :
      ledger.pending.erase
        (ReferenceActivePhysicalStep.upSenderIndex admission.record.input) = ∅ := by
    calc
      ledger.pending.erase
          (ReferenceActivePhysicalStep.upSenderIndex admission.record.input) =
          boundary.finished.pending := boundary.pending_finished.symm
      _ = ∅ := hempty
  rcases admission.hReady with
    ⟨_hstate, _hphase, _hsigmaLower, _hsigmaUpper, hsigmaCutoff, hsigmaPayload,
      _hcutoffLower, _hcutoffUpper, _hcutoffFreeze, _hfreezeUpper, hfreeze,
      hcursorInput, hcutoffCursor, _hcursorUpper, hassignment, _hbase, hanchor,
      _hn, _hpending, _hregister, _hgamma, _hcutoffMass, _hcurrentMass, _hservice,
      _hraw, _hhistory, _hbank⟩
  have hrecordTime : admission.record.input.time.val = s + k := admission.round_time
  have hledgerCursor : ledger.cursor = s + k + 1 := by
    omega
  have hfinishedOrder :
      boundary.finished.sigma < boundary.finished.cutoff := by
    rw [boundary.sigma_finished, boundary.cutoff_finished]
    exact hsigmaCutoff
  have hfinishedCursorOrder :
      boundary.finished.cutoff < boundary.finished.cursor := by
    rw [boundary.cutoff_finished, boundary.cursor_finished]
    rw [hledgerCursor] at hcutoffCursor
    omega
  have hfinishedAssignment :
      boundary.finished.assignment.arm = payload.assignment.assigned := by
    rw [boundary.assignment_finished]
    exact hassignment
  have hactualRun : admission.actualRun =
      ReferenceActivePhysicalHorizon.run
        (ReferenceFirstCollectionEpochAlignment.actualLaunchState
          rate source wholeRewards C_star C_h hcross)
        source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
        wholeRewards
        (ReferenceInitializationRun.elapsed p
          (ReferenceInitializationRun.output
            (ActualReferenceInitializationBlock.referenceInput
              source wholeRewards C_star C_h rate)).completed)
        count admission.hspanActual admission.actualMode := by
    simpa [ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun] using
      admission.actualRun_is_original
  have hcount :=
    ReferenceGeneratedFirstCollectionAdmissionBoundary.admission_actual_run_record_count
      admission
  have hbankState : prefixState.upDecoderBank = admission.receiver.bank := by
    calc
      prefixState.upDecoderBank = admission.record.output.next.upDecoderBank := by
        exact congrArg (fun state : ReferenceActivePhysicalStep.State p rate =>
          state.upDecoderBank) boundary.record_output_is_original_next_prefix_boundary.symm
      _ = admission.receiver.bank := boundary.decoder_bank_next_is_receiver_bank
  have hbankCheck :
      CoordinatorUpReception.decoderBankCheck p prefixState.upDecoderBank = true := by
    rw [hbankState]
    exact (CoordinatorUpReception.decoderBankCheck_eq_true_iff p admission.receiver.bank).2
      admission.receiver.bank_well_formed
  have hregisters := boundary.all_known_registers_when_pending_empty hemptyErase
  have hservice := boundary.joint_mass_and_service_span
  refine
    { pending_empty := hempty
      prefixState := prefixState
      prefixState_is_actual_next := rfl
      prefixState_is_record_next := boundary.record_output_is_original_next_prefix_boundary.symm
      finished_coordinator := ?_
      finished_valid := boundary.finish_valid
      finished_ready := boundary.phase_ready
      finished_sigma := boundary.sigma_finished.trans hsigmaPayload
      finished_sigma_lt_cutoff := hfinishedOrder
      finished_cutoff_lt_cursor := hfinishedCursorOrder
      finished_cursor := boundary.cursor_finished
      finished_freezeAt := boundary.freeze_finished.trans hfreeze
      finished_assignment := hfinishedAssignment
      finished_anchor := hanchor
      finished_joint_mass := ?_
      finished_joint_service := ?_
      decoder_bank_check := hbankCheck
      all_registers_known := hregisters
      actual_run_record_count := hcount
      next_input := ?_
      terminal_cursor := ?_
      prefix_next_is_execution_final_when_last := by
        intro hlast
        change admission.actualPrefixNext.finalState = execution.finalState
        exact boundary.prefix_next_is_execution_final_when_last hlast }
  · calc
      prefixState.coordinator = admission.record.output.next.coordinator := by
        exact congrArg (fun state : ReferenceActivePhysicalStep.State p rate =>
          state.coordinator) boundary.record_output_is_original_next_prefix_boundary.symm
      _ = .collection payload boundary.finished saved :=
        boundary.coordinator_next_is_finished_collection
  · intro a c q hcut hcurrent
    rcases hservice a c q hcut hcurrent with ⟨hmass, hcap⟩
    simpa [boundary.cursor_finished, boundary.sigma_finished] using hmass
  · intro a c q hcut hcurrent
    rcases hservice a c q hcut hcurrent with ⟨_, hcap⟩
    simpa [boundary.cursor_finished, boundary.freeze_finished,
      boundary.sigma_finished] using hcap
  · intro hbefore
    let initial := ReferenceFirstCollectionEpochAlignment.actualLaunchState
      rate source wholeRewards C_star C_h hcross
    let start := ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput
          source wholeRewards C_star C_h rate)).completed
    let selected := ActualInitializationPhysicalStep.selectedRowIndex p source
    let next := ReferenceActivePhysicalHorizon.roundInputAt initial source.1.2 selected
      wholeRewards start admission.actualMode admission.actualPrefixNext
      ⟨s + k + 1, by omega, hbefore⟩
    have hprefixRun : admission.actualPrefixNext =
        ReferenceActivePhysicalHorizon.run initial source.1.2 selected wholeRewards
          start (k + 1) (by omega) admission.actualMode := by
      simpa [start] using admission.actualPrefixNext_eq
    have hnextPrefix : next =
        ReferenceActivePhysicalHorizon.roundInputAt initial source.1.2 selected wholeRewards
          start admission.actualMode
          (ReferenceActivePhysicalHorizon.run initial source.1.2 selected wholeRewards
            start (k + 1) (by omega) admission.actualMode)
          ⟨start + (k + 1), by omega, by omega⟩ := by
      apply round_input_ext
      · change admission.actualPrefixNext.finalState =
          (ReferenceActivePhysicalHorizon.run initial source.1.2 selected wholeRewards
            start (k + 1) (by omega) admission.actualMode).finalState
        exact congrArg (fun run : ReferenceActivePhysicalHorizon.Run initial => run.finalState)
          hprefixRun
      · rfl
      · rfl
      · apply Fin.ext
        change s + k + 1 = start + (k + 1)
        simp [start, hsElapsed, Nat.add_assoc]
      · rfl
    refine ⟨next, ?_, rfl, ?_, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
    · rfl
    · calc
        next.state = admission.actualPrefixNext.finalState := rfl
        _ = admission.record.output.next :=
          boundary.record_output_is_original_next_prefix_boundary.symm
    · have htime : next.time.val = s + k + 1 := rfl
      calc
        boundary.finished.cursor = s + k + 2 := boundary.cursor_finished
        _ = (s + k + 1) + 1 := by omega
        _ = next.time.val + 1 := by rw [htime]
    · change CoordinatorUpReception.decoderBankCheck p prefixState.upDecoderBank = true
      exact hbankCheck
    · intro hnext
      have hnextRecord :
          (admission.actualRun.records[k + 1]'(by
            rw [hcount]
            exact hnext)).input =
          ReferenceActivePhysicalHorizon.roundInputAt initial source.1.2 selected wholeRewards
            start admission.actualMode
            (ReferenceActivePhysicalHorizon.run initial source.1.2 selected wholeRewards
              start (k + 1) (by omega) admission.actualMode)
            ⟨start + (k + 1), by omega, by omega⟩ := by
        have hrecordList : admission.actualRun.records =
            (ReferenceActivePhysicalHorizon.run initial source.1.2 selected wholeRewards
              start count admission.hspanActual admission.actualMode).records :=
          congrArg (fun run : ReferenceActivePhysicalHorizon.Run initial => run.records)
            hactualRun
        have hrecord := List.getElem_of_eq hrecordList (by rw [hcount]; exact hnext)
        have hrecordInput := congrArg
          (fun record : ReferenceActivePhysicalHorizon.RoundRecord => record.input) hrecord
        calc
          (admission.actualRun.records[k + 1]'(by rw [hcount]; exact hnext)).input =
              ((ReferenceActivePhysicalHorizon.run initial source.1.2 selected wholeRewards
                start count admission.hspanActual admission.actualMode).records[k + 1]'
                  (by rw [ReferenceActivePhysicalHorizon.run_record_count]; exact hnext)).input :=
            hrecordInput
          _ = ReferenceActivePhysicalHorizon.roundInputAt initial source.1.2 selected
              wholeRewards start admission.actualMode
              (ReferenceActivePhysicalHorizon.run initial source.1.2 selected wholeRewards
                start (k + 1) (by omega) admission.actualMode)
              ⟨start + (k + 1), by omega, by omega⟩ :=
            original_run_record_input_eq_prefix initial source.1.2 selected wholeRewards
              start count admission.hspanActual admission.actualMode (k + 1) hnext
      calc
        next = ReferenceActivePhysicalHorizon.roundInputAt initial source.1.2 selected
            wholeRewards start admission.actualMode
            (ReferenceActivePhysicalHorizon.run initial source.1.2 selected wholeRewards
              start (k + 1) (by omega) admission.actualMode)
            ⟨start + (k + 1), by omega, by omega⟩ := hnextPrefix
        _ = (admission.actualRun.records[k + 1]'(by
            rw [hcount]
            exact hnext)).input := hnextRecord.symm
  · intro hterminal
    rw [boundary.cursor_finished]
    omega

/-- Apply the admitted original-source first-admission constructor and retain
its exhausted rejected-prefix alternative. At the accepted output, either the
actual FINISH is empty-pending and the local actual-prefix result is attached,
or the produced FINISH still has nonempty pending. No source-level success or
empty-pending condition is added to the root telescope. -/
theorem first_admission_empty_pending_input
    {p : ConstructorDimensions.Parameters}
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : ReferenceGeneratedFirstCollectionAdmission.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput
        source rewards C_star C_h rate)).crossing.isSome = true)
    (s : ℕ)
    (hsElapsed : s = ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed)
    (count : ℕ) (hspan : s + count ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun
        rate source rewards C_star C_h hcross s hsElapsed count hspan).records).length < count) :
    let initial := ReferenceFirstLaunchNumericalCell.launchState
      rate source rewards C_star C_h hcross
    let execution := ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun
      rate source rewards C_star C_h hcross s hsElapsed count hspan
    let firstWindow := ReferenceFirstLiveConfirmationHistory.firstLiveWindow execution.records
    let w := firstWindow.length
    let b := w + 1
    let Q := (execution.records.drop b).takeWhile
      (fun record => ReferenceGeneratedFirstCollectionRejectedPrefix.rejectionEligible record.input)
    let hcount : execution.records.length = count := by
      simpa [execution, ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun] using
        ReferenceActivePhysicalHorizon.run_record_count initial source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s count hspan
          (ReferenceGeneratedFirstCutoffSurvival.generatedLaunchActive
            rate source rewards C_star C_h hcross s hsElapsed)
    let htail : b + Q.length ≤ count := by
      have hw : w < count := by simpa [execution, firstWindow, w] using hshort
      have hprefix : Q <+: execution.records.drop b := List.takeWhile_prefix _
      have hlen := hprefix.length_le
      have hdrop : (execution.records.drop b).length = count - b := by
        simp [List.length_drop, hcount]
      omega
    let k := b + Q.length
    let prefixAt := fun (j : ℕ) (hj : j ≤ Q.length) =>
      ReferenceActivePhysicalHorizon.run initial source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s (b + j)
        (by omega)
        (ReferenceGeneratedFirstCutoffSurvival.generatedLaunchActive
          rate source rewards C_star C_h hcross s hsElapsed)
    let B := ReferenceCollectionPhaseHistory.collectionWindow execution.records w
    ∃ cut payload saved,
      cut = execution.records[w]'(by
        have hw : w < count := by simpa [execution, firstWindow, w] using hshort
        simpa [execution, firstWindow, w] using Nat.lt_of_lt_of_eq hw hcount.symm) ∧
      (∃ ledger,
        (prefixAt Q.length (by omega)).finalState.coordinator =
          .collection payload ledger saved ∧
        ledger.pending = Finset.univ ∧ ledger.sigma = s + 1 ∧ ledger.cutoff = s + b ∧
        ((k = count ∧
          (prefixAt Q.length (by omega)).finalState = execution.finalState ∧
          (∀ htime : s + k < p.T,
            ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain
              (ReferenceActivePhysicalHorizon.roundInputAt initial source.1.2
                (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s
                (ReferenceGeneratedFirstCutoffSurvival.generatedLaunchActive
                  rate source rewards C_star C_h hcross s hsElapsed)
                (prefixAt Q.length (by omega)) ⟨s + k, by omega, htime⟩)
              payload ledger saved) ∧
          (s + k = p.T →
            ReferenceContinuingCollectionRejectedFinishDomains.continuingCollectionReadyBoundaryDomain
              (prefixAt Q.length (by omega)).finalState payload ledger saved)) ∨
         (∃ hendpoint : k < count,
          ∃ output : ReferenceGeneratedFirstCollectionAdmission.AcceptedAdmissionOutput
            source rewards C_star C_h hcross s hsElapsed count hspan execution B payload ledger
            saved w Q.length k,
            output.k_before_end = hendpoint ∧
            ∃ boundary : ReferenceGeneratedFirstCollectionAdmissionBoundary.AcceptedBoundaryOutput
              output,
              ((boundary.finished.pending = ∅ ∧
                Nonempty (EmptyPendingBoundaryOutput output boundary)) ∨
                boundary.finished.pending.Nonempty)))) := by
  classical
  have hAdmission :=
    ReferenceGeneratedFirstCollectionAdmissionBoundary.actual_generated_first_collection_admission_boundary
      rate source rewards C_star C_h hcross s hsElapsed count hspan hshort
  dsimp only at hAdmission
  rcases hAdmission with ⟨cut, payload, saved, hcut, hrest⟩
  rcases hrest with ⟨ledger, hcoordinator, hpending, hsigma, hcutoff, hbranch⟩
  refine ⟨cut, payload, saved, hcut, ledger, hcoordinator, hpending, hsigma,
    hcutoff, ?_⟩
  rcases hbranch with hexhausted | haccepted
  · exact Or.inl hexhausted
  · rcases haccepted with ⟨hendpoint, output, hendpointEq, houtput⟩
    refine Or.inr ⟨hendpoint, output, hendpointEq, ?_⟩
    rcases houtput with ⟨boundary⟩
    by_cases hempty : boundary.finished.pending = ∅
    · exact ⟨boundary, Or.inl ⟨hempty,
        ⟨empty_pending_boundary_output output boundary hempty⟩⟩⟩
    · exact ⟨boundary, Or.inr (Finset.nonempty_iff_ne_empty.mpr hempty)⟩

end Bandits.Support.ReferenceFirstAdmissionEmptyPendingInput

end
