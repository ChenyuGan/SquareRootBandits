/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionReadyInitialization
public import Bandits.Support.ReferenceContinuingCollectionRejectedFinishDomains

import Lean.Elab.Tactic.Omega
import Mathlib.Data.List.TakeWhile

/-!
# Generated first-collection rejected prefix

Sources: `sources/zip4/manuscript/06_interruptions.tex:41-70,246-295`,
`sources/zip4/manuscript/04_slow_fast_learner.tex:157-174`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-64`, and
`sources/zip4/manuscript/07_public_setup.tex:127-164`.

This module carries the actual first cutoff ready state along the contiguous
original-run prefix whose filtered local UP attempt is rejected. It stops at
the first locally admissible filtered UP parse, or at the end of the retained
run. This is an internal operational result, not collection safety or
manuscript closure.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions
open ReferenceActivePhysicalStep
open ReferenceActivePhysicalHorizon
open ReferenceGeneratedFirstCutoffSurvival
open ReferenceFirstLiveConfirmationHistory
open ReferenceCollectionPhaseHistory
open ReferenceAssignmentPayloadChronology
open ReferenceCollectionSegmentExtraction
open ReferenceContinuingCollectionStartDomains
open ReferenceContinuingCollectionRejectedFinishDomains

open scoped Classical

namespace Bandits.Support.ReferenceGeneratedFirstCollectionRejectedPrefix

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput
abbrev RewardTable := ActualInitializationPhysicalStep.GridRewardTable

variable {p : Parameters} {rate : RateInput p}

/-- Literal projection of the existing dispatch, recorder, checked START,
and filtered UP acceptance operations. `false` means only that this exact
operation was not witnessed by the projection. -/
def rejectionEligible (x : ReferenceActivePhysicalStep.RoundInput p rate) : Bool :=
  match ReferenceCollectionSegmentExtraction.choice x with
  | none => false
  | some c =>
      match CoordinatorRecorderComplementBridge.run
        (ReferenceActivePhysicalStep.collectionRecordingInput
          (ReferenceActivePhysicalStep.prepare x) c.payload c.started c.weights) with
      | none => false
      | some o =>
          match CoordinatorCollectionLedger.startRound c.preLedger (x.time.val + 1)
            (ReferenceActivePhysicalStep.collectionEnabled c.preLedger x.time)
            (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder o) with
          | .success l1 =>
              match ReferenceCollectionSegmentExtraction.effectiveParse x l1 with
              | none => true
              | some M =>
                  !(CoordinatorCollectionLedger.acceptUpCheck l1
                    (ReferenceActivePhysicalStep.upSenderIndex x) M)
          | _ => false

private theorem getElem_takeWhile_eq {α : Type} (pred : α → Bool)
    (xs : List α) (j : ℕ) (hj : j < (xs.takeWhile pred).length) :
    (xs.takeWhile pred)[j]'hj = xs[j]'(by
      exact Nat.lt_of_lt_of_le hj (List.takeWhile_prefix pred).length_le) :=
  (List.takeWhile_prefix pred).getElem hj

private theorem next_input_eq_record
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (s count index : ℕ) (hspan : s + count ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial s)
    (hindex : index < count) :
    let prior := ReferenceActivePhysicalHorizon.run initial rows J rewards s index
      (by omega) active
    ReferenceActivePhysicalHorizon.roundInputAt initial rows J rewards s active prior
      ⟨s + index, by omega, by omega⟩ =
      ((ReferenceActivePhysicalHorizon.run initial rows J rewards s count hspan active).records[index]'(by
        rw [ReferenceActivePhysicalHorizon.run_record_count]
        exact hindex)).input := by
  have hstepSpan : s + (index + 1) ≤ p.T := by omega
  obtain ⟨tail, hprefixRecords⟩ := ReferenceCollectionPhaseHistory.run_records_prefix
    initial rows J rewards s (index + 1) (count - (index + 1)) (by omega) active
  have hcountEq : index + 1 + (count - (index + 1)) = count := by omega
  have hprefixRecordsCount :
      (ReferenceActivePhysicalHorizon.run initial rows J rewards s count hspan active).records =
        (ReferenceActivePhysicalHorizon.run initial rows J rewards s (index + 1)
          hstepSpan active).records ++ tail := by
    simpa only [hcountEq] using hprefixRecords
  rw [ReferenceAssignmentPayloadChronology.run_successor_actualRunRecordAt] at hprefixRecordsCount
  have hlen := ReferenceActivePhysicalHorizon.run_record_count initial rows J rewards s index
    (by omega) active
  have hprefixRecords' :
      (ReferenceActivePhysicalHorizon.run initial rows J rewards s count hspan active).records =
        (ReferenceActivePhysicalHorizon.run initial rows J rewards s index (by omega) active).records ++
          ReferenceAssignmentPayloadChronology.actualRunRecordAt initial rows J rewards
            s index hstepSpan active :: tail := by
    simpa only [List.append_assoc, List.singleton_append] using hprefixRecordsCount
  have hget := List.getElem_of_append hprefixRecords' hlen
  exact (congrArg (fun rec : ReferenceActivePhysicalHorizon.RoundRecord
    (p := p) (rate := rate) => rec.input) hget).symm

private theorem round_input_ext {left right : ReferenceActivePhysicalStep.RoundInput p rate}
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

private theorem run_successor_state_eq
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (s count : ℕ) (hspan : s + (count + 1) ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial s)
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (hinput : ReferenceActivePhysicalHorizon.roundInputAt initial rows J rewards s active
      (ReferenceActivePhysicalHorizon.run initial rows J rewards s count (by omega) active)
      ⟨s + count, by omega, by omega⟩ = x) :
    (ReferenceActivePhysicalHorizon.run initial rows J rewards s (count + 1) hspan active).finalState =
      (ReferenceActivePhysicalStep.step x).next := by
  rw [ReferenceActivePhysicalHorizon.run_successor_step]
  unfold ReferenceActivePhysicalHorizon.foldRound
  change (ReferenceActivePhysicalStep.step
    (ReferenceActivePhysicalHorizon.roundInputAt initial rows J rewards s active
      (ReferenceActivePhysicalHorizon.run initial rows J rewards s count (by omega) active)
      ⟨s + count, by omega, by omega⟩)).next = _
  rw [hinput]

private theorem ready_attempt_witnesses
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (l : ReferenceActivePhysicalStep.Ledger rate)
    (saved : Option (Fin p.T × Bool))
    (hready : ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain
      x payload l saved) :
    ∃ cutoff : Fin p.T, cutoff.val + 1 = l.cutoff ∧
    let clock := ReferenceActivePhysicalStep.collectionClock payload l saved cutoff
    let input := ReferenceActivePhysicalStep.collectionInput x payload l clock cutoff
    ∃ (core : CoordinatorRoundDispatch.CollectionCoreValid input)
      (snap : CoordinatorCollectionInteractive.PreparedSnapshot input)
      (hb : snap.clockStarted.clock.g ≤ p.T + 1)
      (hs : CoordinatorRoundDispatch.collectionCurrentScoresCheck input = true),
      let prepared := ReferenceActivePhysicalStep.prepare x
      let weights := CoordinatorCollectionInteractive.PreObservationInputs.weights input
        snap.inputsValid.ledger_valid snap.inputsValid.assignment_eq
      let recordingInput := ReferenceActivePhysicalStep.collectionRecordingInput prepared
        payload snap.clockStarted weights
      prepared.coordinator = .collection payload l clock cutoff (.continuing core snap hb hs) ∧
      prepared.coordinator.arm = snap.arm ∧
      CoordinatorRecorderComplementBridge.LocalInputsValid recordingInput ∧
      CoordinatorRecordingOperation.InputsValid
        (CoordinatorRecorderComplementBridge.recorderInput recordingInput) ∧
      ∃ (c : ReferenceCollectionSegmentExtraction.Choice rate)
        (o : CoordinatorRecordingOperation.Output p)
        (l1 : ReferenceActivePhysicalStep.Ledger rate),
        ReferenceCollectionSegmentExtraction.choice x = some c ∧
        CoordinatorRecorderComplementBridge.run
          (ReferenceActivePhysicalStep.collectionRecordingInput
            (ReferenceActivePhysicalStep.prepare x) c.payload c.started c.weights) = some o ∧
        CoordinatorCollectionLedger.startRound c.preLedger (x.time.val + 1)
          (ReferenceActivePhysicalStep.collectionEnabled c.preLedger x.time)
          (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder o) = .success l1 ∧
        c.payload = payload ∧ c.preLedger = l ∧
        c.started = snap.clockStarted ∧ c.initializer = none ∧
        (rejectionEligible x = false →
          ∃ M, ReferenceCollectionSegmentExtraction.effectiveParse x l1 = some M ∧
            CoordinatorCollectionLedger.acceptUpCheck l1
              (ReferenceActivePhysicalStep.upSenderIndex x) M = true) := by
  classical
  have hS := ReferenceContinuingCollectionStartDomains.continuing_collection_start_domains
    x payload l saved hready
  dsimp only at hS
  obtain ⟨cutoff, hcutoff, core, snap, hb, hs, hcoord, harm, hlocal, hrecordInputs,
    o, l1, hrecord, hstart, _⟩ := hS
  let input := ReferenceActivePhysicalStep.collectionInput x payload l
    (ReferenceActivePhysicalStep.collectionClock payload l saved cutoff) cutoff
  let weights := CoordinatorCollectionInteractive.PreObservationInputs.weights input
    snap.inputsValid.ledger_valid snap.inputsValid.assignment_eq
  let c : ReferenceCollectionSegmentExtraction.Choice rate :=
    ⟨payload, l, snap.clockStarted, weights, none⟩
  have hchoice : ReferenceCollectionSegmentExtraction.choice x = some c := by
    unfold ReferenceCollectionSegmentExtraction.choice
    rw [hcoord]
    simp [ReferenceCollectionSegmentExtraction.choiceOfCut,
      ReferenceActivePhysicalStep.DispatchCut.selection,
      c, weights, input]
  have hrecording : CoordinatorRecorderComplementBridge.run
      (ReferenceActivePhysicalStep.collectionRecordingInput
        (ReferenceActivePhysicalStep.prepare x) c.payload c.started c.weights) = some o := by
    simpa [c] using hrecord
  have hstarted : CoordinatorCollectionLedger.startRound c.preLedger (x.time.val + 1)
      (ReferenceActivePhysicalStep.collectionEnabled c.preLedger x.time)
      (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder o) = .success l1 := by
    simpa [c, ReferenceContinuingCollectionStartDomains.sourceRound] using hstart
  refine ⟨cutoff, hcutoff, core, snap, hb, hs, hcoord, harm, hlocal, hrecordInputs,
    c, o, l1, hchoice, hrecording, hstarted, rfl, rfl, rfl, rfl, ?_⟩
  intro hfalse
  have hprojected : rejectionEligible x =
      (match ReferenceCollectionSegmentExtraction.effectiveParse x l1 with
      | none => true
      | some M => !CoordinatorCollectionLedger.acceptUpCheck l1
          (ReferenceActivePhysicalStep.upSenderIndex x) M) := by
    simp [rejectionEligible, hchoice, hrecording, hstarted]
  rw [hprojected] at hfalse
  cases hp : ReferenceCollectionSegmentExtraction.effectiveParse x l1 with
  | none => simp [hp] at hfalse
  | some M =>
      cases ha : CoordinatorCollectionLedger.acceptUpCheck l1
          (ReferenceActivePhysicalStep.upSenderIndex x) M with
      | false => simp [hp, ha] at hfalse
      | true => exact ⟨M, rfl, ha⟩

private theorem takeWhile_false_at_stop {α : Type} (pred : α → Bool) (xs : List α)
    (hshort : (xs.takeWhile pred).length < xs.length) :
    pred (xs[(xs.takeWhile pred).length]'hshort) = false := by
  induction xs with
  | nil => simp at hshort
  | cons head tail ih =>
      cases hp : pred head
      · simp [List.takeWhile, hp]
      · have htail : (tail.takeWhile pred).length < tail.length := by
          simpa [List.takeWhile, hp] using hshort
        have h := ih htail
        simpa [List.takeWhile, hp] using h

private theorem seed_ready_boundary
    (rate : RateInput p) (z : SourceInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (s : ℕ)
    (hsElapsed : s = ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed)
    (count : ℕ) (hspan : s + count ≤ p.T)
    (hshort : (firstLiveWindow
      (generatedFirstCutoffRun rate z rewards C_star C_h hc s hsElapsed count hspan).records).length < count) :
    let initial := ReferenceFirstLaunchNumericalCell.launchState rate z rewards C_star C_h hc
    let execution := generatedFirstCutoffRun rate z rewards C_star C_h hc s hsElapsed count hspan
    let window := firstLiveWindow execution.records
    let w := window.length
    let b := w + 1
    let active := generatedLaunchActive rate z rewards C_star C_h hc s hsElapsed
    let htail : b ≤ count := by
      have hw : w < count := by simpa [execution, window] using hshort
      omega
    let prefixAt := fun (j : ℕ) (hj : j ≤ 0) =>
      ReferenceActivePhysicalHorizon.run initial z.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s (b + j)
        (by omega) active
    ∃ cut payload l saved,
      cut = execution.records[w]'(by
        have hw : w < count := by simpa [execution, window] using hshort
        have hlen := ReferenceActivePhysicalHorizon.run_record_count initial z.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s count hspan active
        simpa [execution, generatedFirstCutoffRun] using Nat.lt_of_lt_of_eq hw hlen.symm) ∧
      (prefixAt 0 (by omega)).finalState = cut.output.next ∧
      (prefixAt 0 (by omega)).finalState.coordinator = .collection payload l saved ∧
      l.pending = Finset.univ ∧ l.sigma = s + 1 ∧ l.cutoff = s + b ∧
      (∀ htime : s + b < p.T,
        ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain
          (ReferenceActivePhysicalHorizon.roundInputAt initial z.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s active
            (prefixAt 0 (by omega)) ⟨s + b, by omega, htime⟩) payload l saved) ∧
      (s + b = p.T →
        ReferenceContinuingCollectionRejectedFinishDomains.continuingCollectionReadyBoundaryDomain
          (prefixAt 0 (by omega)).finalState payload l saved) := by
  classical
  let initial := ReferenceFirstLaunchNumericalCell.launchState rate z rewards C_star C_h hc
  let execution := generatedFirstCutoffRun rate z rewards C_star C_h hc s hsElapsed count hspan
  let window := firstLiveWindow execution.records
  let w := window.length
  let b := w + 1
  let active := generatedLaunchActive rate z rewards C_star C_h hc s hsElapsed
  have hw : w < count := by simpa [execution, window] using hshort
  have htail : b ≤ count := by omega
  let prefixAt := fun (j : ℕ) (hj : j ≤ 0) =>
    ReferenceActivePhysicalHorizon.run initial z.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s (b + j)
      (by omega) active
  let successorRun := ReferenceActivePhysicalHorizon.run initial z.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s (w + 1)
    (by omega) active
  have hA := ReferenceFirstCollectionReadyInitialization.actual_first_collection_ready_initialization
    rate z rewards C_star C_h hc s hsElapsed count hspan hshort
  dsimp only at hA
  rcases hA with ⟨hsT, cut, suffix, hsplit, hindex, htime, hstate, hrows, hselected,
    hrewards, r, q, base, hlive, hsigma, dispatched, hstart, ledger, hinit, hledger,
    hdomain, hclock, hpending, hnoAssignment, selected, hbranch, huTime, huT, hug,
    hledgerSigma, hledgerCut, o, hactualInput, htrace, hrecording, hrecorder,
    started, hstartSuccess, hstartCandidate, input, decoded, bank, diagnostic, finished,
    hinput, hinputDomain, hinputCheck, htransition, hquota, hdecoded, hreceive,
    hbank, hbankUpdate, hbankFrame, hrawParsed, hreceiveDiagnostic, hdiagnosticInput,
    hdiagnosticExpected, hdiagnosticAfter, hdiagnosticRaw, hdiagnosticParsed,
    hdiagnosticAccepted, hdiagnosticWrong, hfinish, hvalid, hclockFinish,
    hconfiguration, hfailure, hcommitted, hrecordingOut, hupOut, hnext, hnextBank,
    hsuccessor, hsuccessorCoordinator, hsuccessorBank, hphase, hfSigmaNamed,
    hfCutNamed, hfCursorNamed, hgrid, hgridT, hfassignment, hfbase, hanchor, hn,
    hfpending, hnonempty, hfSigmaPos, hfSigmaT, hfBefore, hfSigmaPayload,
    hfCutPos, hfCutT, hfCutGrid, hfCursorAfter, hfCursorT, hoptions, hzero,
    hcutMass, hpaired, hservice, hraw, hhistory, hhistoryAt, hhistoryOther,
    hrawOther, hfuture, hbankFields, hterminal, hnextReady⟩
  have hcutEq : cut = execution.records[w]'(by
      have hlen := ReferenceActivePhysicalHorizon.run_record_count initial z.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s count hspan active
      simpa [execution, generatedFirstCutoffRun] using Nat.lt_of_lt_of_eq hw hlen.symm) := by
    exact hindex
  have hsuccessorEq :
      (prefixAt 0 (by omega)).finalState = cut.output.next := by
    simpa [prefixAt, successorRun, b] using hsuccessor
  have hprefixRun : (prefixAt 0 (by omega)).finalState = successorRun.finalState := by
    calc
      _ = cut.output.next := hsuccessorEq
      _ = successorRun.finalState := hsuccessor.symm
  have hcoord : (prefixAt 0 (by omega)).finalState.coordinator =
      .collection r.payload finished dispatched.startResult.clock.lastProposal := by
    rw [hprefixRun]
    exact hsuccessorCoordinator
  have hpend : finished.pending = Finset.univ := hfpending
  have hnextReadyNamed : ∀ htime : s + b < p.T,
      ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain
        (ReferenceActivePhysicalHorizon.roundInputAt initial z.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s active
          (prefixAt 0 (by omega)) ⟨s + b, by omega, htime⟩)
        r.payload finished dispatched.startResult.clock.lastProposal := by
    intro htime
    have htimeA : s + window.length + 1 < p.T := by omega
    have hnext := hnextReady htimeA
    simpa [prefixAt, successorRun, b, w, window, Nat.add_assoc] using hnext.1
  have hboundary :
      s + b = p.T →
        ReferenceContinuingCollectionRejectedFinishDomains.continuingCollectionReadyBoundaryDomain
          (prefixAt 0 (by omega)).finalState r.payload finished
          dispatched.startResult.clock.lastProposal := by
    intro htime
    have htimeA : s + window.length + 1 = p.T := by omega
    have hcursorTerminal : finished.cursor = p.T + 1 := hterminal htimeA
    refine ⟨hcoord, hphase, hfSigmaPos, hfSigmaT, hfBefore, hfSigmaPayload,
      hfCutPos, hfCutT, hfCutGrid, hgridT, hgrid, hcursorTerminal,
      hfCursorAfter, hfCursorT, hfassignment, hfbase, hanchor, hn,
      hnonempty, hoptions, hzero, hcutMass, hpaired, hservice, hraw,
      hhistory, ?_⟩
    intro i
    rw [hprefixRun, hsuccessorBank]
    exact hbankFields i
  refine ⟨cut, r.payload, finished, dispatched.startResult.clock.lastProposal,
    hcutEq, hsuccessorEq, hcoord, hpend, hfSigmaNamed,
    by simpa [b, w, Nat.add_assoc] using hfCutNamed, hnextReadyNamed, hboundary⟩

/-- The actual generated original-run first-collection prefix ending before
the first locally admissible filtered UP attempt. Every retained record is
the original indexed physical record. At each boundary the same collection
payload and actual ledger remain in the original horizon run. -/
theorem actual_generated_first_collection_rejected_prefix
    (rate : RateInput p) (z : SourceInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (s : ℕ)
    (hsElapsed : s = ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed)
    (count : ℕ) (hspan : s + count ≤ p.T)
    (hshort : (firstLiveWindow
      (generatedFirstCutoffRun rate z rewards C_star C_h hc s hsElapsed count hspan).records).length < count) :
    let initial := ReferenceFirstLaunchNumericalCell.launchState rate z rewards C_star C_h hc
    let execution := generatedFirstCutoffRun rate z rewards C_star C_h hc s hsElapsed count hspan
    let window := firstLiveWindow execution.records
    let w := window.length
    let b := w + 1
    let Q := (execution.records.drop b).takeWhile
      (fun record => rejectionEligible record.input)
    let active := generatedLaunchActive rate z rewards C_star C_h hc s hsElapsed
    let htail : b + Q.length ≤ count := by
      classical
      have hcount : execution.records.length = count := by
        simpa [execution, generatedFirstCutoffRun] using
          ReferenceActivePhysicalHorizon.run_record_count initial z.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s count hspan active
      have hprefix : Q <+: execution.records.drop b := List.takeWhile_prefix _
      have hlength := hprefix.length_le
      have hdrop : (execution.records.drop b).length = count - b := by
        simp [List.length_drop, hcount]
      have hw : w < count := by simpa [execution, window] using hshort
      omega
    let prefixAt := fun (j : ℕ) (hj : j ≤ Q.length) =>
      ReferenceActivePhysicalHorizon.run initial z.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s (b + j)
        (by omega) active
    ∃ cut payload saved,
      cut = execution.records[w]'(by
        have hw : w < count := by simpa [execution, window] using hshort
        have hlen := ReferenceActivePhysicalHorizon.run_record_count initial z.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s count hspan active
        simpa [execution, generatedFirstCutoffRun] using Nat.lt_of_lt_of_eq hw hlen.symm) ∧
      (prefixAt 0 (by omega)).finalState = cut.output.next ∧
      ∀ (j : ℕ) (hj : j ≤ Q.length),
        ∃ l : ReferenceActivePhysicalStep.Ledger rate,
          (prefixAt j hj).finalState.coordinator = .collection payload l saved ∧
          l.pending = Finset.univ ∧ l.sigma = s + 1 ∧ l.cutoff = s + b ∧
          (∀ htime : s + b + j < p.T,
            ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain
              (ReferenceActivePhysicalHorizon.roundInputAt initial z.1.2
                (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s active
                (prefixAt j hj) ⟨s + b + j, by omega, htime⟩) payload l saved) ∧
          (∀ hindex : b + j < count,
            ReferenceActivePhysicalHorizon.roundInputAt initial z.1.2
              (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s active
              (prefixAt j hj) ⟨s + b + j, by omega, by omega⟩ =
            (execution.records[b + j]'(by
              have hcount : execution.records.length = count := by
                simpa [execution, generatedFirstCutoffRun] using
                  ReferenceActivePhysicalHorizon.run_record_count initial z.1.2
                    (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s count hspan active
              rw [hcount]
              exact hindex)).input) ∧
          (s + b + j = p.T →
            ReferenceContinuingCollectionRejectedFinishDomains.continuingCollectionReadyBoundaryDomain
              (prefixAt j hj).finalState payload l saved) ∧
          (∀ hstep : j < Q.length,
            let record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) :=
              execution.records[b + j]'(by
                have hcount : execution.records.length = count := by
                  simpa [execution, generatedFirstCutoffRun] using
                    ReferenceActivePhysicalHorizon.run_record_count initial z.1.2
                      (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s count hspan active
                have hindex : b + j < count := by omega
                rw [hcount]
                exact hindex)
            ∃ _hready :
                ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain
                  record.input payload l saved,
              ∃ cutoff : Fin p.T, cutoff.val + 1 = l.cutoff ∧
              ∃ (core : CoordinatorRoundDispatch.CollectionCoreValid
                    (ReferenceActivePhysicalStep.collectionInput record.input payload l
                      (ReferenceActivePhysicalStep.collectionClock payload l saved cutoff) cutoff))
                (snap : CoordinatorCollectionInteractive.PreparedSnapshot
                    (ReferenceActivePhysicalStep.collectionInput record.input payload l
                      (ReferenceActivePhysicalStep.collectionClock payload l saved cutoff) cutoff))
                (hb : snap.clockStarted.clock.g ≤ p.T + 1)
                (hs : CoordinatorRoundDispatch.collectionCurrentScoresCheck
                    (ReferenceActivePhysicalStep.collectionInput record.input payload l
                      (ReferenceActivePhysicalStep.collectionClock payload l saved cutoff) cutoff) = true),
              let prepared := ReferenceActivePhysicalStep.prepare record.input
              let weights := CoordinatorCollectionInteractive.PreObservationInputs.weights
                (ReferenceActivePhysicalStep.collectionInput record.input payload l
                  (ReferenceActivePhysicalStep.collectionClock payload l saved cutoff) cutoff)
                snap.inputsValid.ledger_valid snap.inputsValid.assignment_eq
              let recordingInput := ReferenceActivePhysicalStep.collectionRecordingInput
                prepared payload snap.clockStarted weights
              prepared.coordinator = .collection payload l
                (ReferenceActivePhysicalStep.collectionClock payload l saved cutoff)
                cutoff (.continuing core snap hb hs) ∧
              prepared.coordinator.arm = snap.arm ∧
              CoordinatorRecorderComplementBridge.LocalInputsValid recordingInput ∧
              CoordinatorRecordingOperation.InputsValid
                (CoordinatorRecorderComplementBridge.recorderInput recordingInput) ∧
              ∃ (c : ReferenceCollectionSegmentExtraction.Choice rate)
                (o : CoordinatorRecordingOperation.Output p)
                (l1 : ReferenceActivePhysicalStep.Ledger rate),
                ReferenceCollectionSegmentExtraction.choice record.input = some c ∧
                CoordinatorRecorderComplementBridge.run
                  (ReferenceActivePhysicalStep.collectionRecordingInput
                    prepared c.payload c.started c.weights) = some o ∧
                c.payload = payload ∧ c.preLedger = l ∧
                c.started = snap.clockStarted ∧ c.initializer = none ∧
                CoordinatorCollectionLedger.startRound c.preLedger
                  (record.input.time.val + 1)
                  (ReferenceActivePhysicalStep.collectionEnabled c.preLedger record.input.time)
                  (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder o) = .success l1 ∧
                let receptionInput := ReferenceUpReception.receptionInputAtRow rate record.input.row
                  (ReferenceActivePhysicalStep.upInputs prepared l1) record.input.time
                let expected := ReferenceActivePhysicalStep.upExpected prepared
                let decoderRaw := (CoordinatorUpReception.decoderTransition receptionInput).2
                let filteredParsed := CoordinatorUpReception.parseDecoderOutput (eta := rate.eta.val)
                  (ReferenceUpReception.filterRawByExpected decoderRaw expected)
                (filteredParsed = none ∨
                  ∃ M, filteredParsed = some M ∧
                    CoordinatorCollectionLedger.acceptUpCheck l1
                      (ReferenceActivePhysicalStep.upSenderIndex record.input) M = false) ∧
                ∃ (decoded : ReferenceActivePhysicalStep.Ledger rate)
                  (bank : CoordinatorUpReception.UpDecoderBank p),
                  (ReferenceActivePhysicalStep.receiveUp prepared l1).result =
                    .rejected (decoded, bank) ∧
                  decoded = { l1 with phase := CoordinatorCollectionLedger.Phase.decoded } ∧
                  bank = CoordinatorUpReception.decoderBankAfter receptionInput ∧
                  (ReferenceActivePhysicalStep.receiveUp prepared l1).diagnostic =
                    some {
                      input := receptionInput
                      expected := expected
                      decoderAfter := (CoordinatorUpReception.decoderTransition receptionInput).1
                      raw := decoderRaw
                      parsed := ReferenceUpReception.rawParsedOutput rate receptionInput
                      locallyAccepted :=
                        ReferenceUpReception.rawParsedLocalAcceptance rate receptionInput
                      rawMatches := decide (decoderRaw = expected)
                      wrongUniqueAccepted :=
                        ReferenceUpReception.wrongUniqueAndLocalAcceptanceAtRow rate record.input.row
                          (ReferenceActivePhysicalStep.upInputs prepared l1) record.input.time
                          (prepared.followers.followers
                            (ReferenceActivePhysicalStep.upSenderIndex record.input))
                          (prepared.follower_alignment _).1
                          (prepared.follower_alignment _).2.1
                          (prepared.follower_alignment _).2.2.1 rfl } ∧
                  ∃ finished : ReferenceActivePhysicalStep.Ledger rate,
                    CoordinatorCollectionLedger.finishRound decoded = .success finished ∧
                    finished = CoordinatorCollectionLedger.finishRoundCandidate decoded ∧
                    finished.increment = (fun a => l.increment a + l1.gammaLoc a) ∧
                    finished.gammaLoc = (fun _ => 0) ∧
                    finished.phase = CoordinatorCollectionLedger.Phase.ready ∧
                    finished.pending = l.pending ∧
                    finished.assignment = l.assignment ∧
                    finished.baseScore = l.baseScore ∧
                    finished.currentRegisters = l1.currentRegisters ∧
                    finished.rawBuffer = l1.rawBuffer ∧
                    finished.enabledHistory = l1.enabledHistory ∧
                    CoordinatorCollectionLedger.validLedgerCheck finished = true ∧
                    ∃ clockFinished : CoordinatorPhaseClock.FinishRoundResult p,
                      CoordinatorPhaseClock.finishRound p rate.eta.val record.input.time
                        snap.clockStarted.clock finished.pending record.input.row = .ok clockFinished ∧
                      clockFinished.clock = snap.clockStarted.clock ∧
                      clockFinished.pending = finished.pending ∧
                      clockFinished.ledgerCommand =
                        some (.accumulateLocalServiceAt record.input.time) ∧
                      clockFinished.clock.lastProposal = saved ∧
                      ReferenceActivePhysicalStep.collectionFinish (x := record.input) payload
                        snap.clockStarted o (ReferenceActivePhysicalStep.receiveUp prepared l1) =
                          { configuration := .collection payload finished clockFinished.clock.lastProposal
                            upDecoderBank := bank
                            failure := none
                            recording := some o
                            up := (ReferenceActivePhysicalStep.receiveUp prepared l1).diagnostic } ∧
                      prepared.observeCoordinator =
                        ReferenceActivePhysicalStep.collectionFinish (x := record.input) payload
                          snap.clockStarted o (ReferenceActivePhysicalStep.receiveUp prepared l1) ∧
                      (ReferenceActivePhysicalStep.step record.input).coordinator =
                        (ReferenceActivePhysicalStep.prepare record.input).observeCoordinator ∧
                      (ReferenceActivePhysicalStep.step record.input).coordinator.failure = none ∧
                      (ReferenceActivePhysicalStep.step record.input).next.coordinator =
                        .collection payload finished clockFinished.clock.lastProposal ∧
                      (ReferenceActivePhysicalStep.step record.input).next.upDecoderBank = bank ∧
                      (ReferenceActivePhysicalStep.step record.input).next.activations =
                        record.input.state.activations ∧
                      (∀ i, (ReferenceActivePhysicalStep.step record.input).followers i =
                        (ReferenceActivePhysicalStep.prepare record.input).observeFollower i) ∧
                      (ReferenceActivePhysicalStep.step record.input).ownEntries =
                        (ReferenceActivePhysicalStep.prepare record.input).feedback.ownEntries ∧
                      (ReferenceContinuingCollectionStartDomains.sourceRound record.input.time < p.T →
                        ∃ xNext : ReferenceActivePhysicalStep.RoundInput p rate,
                          xNext.state = (ReferenceActivePhysicalStep.step record.input).next ∧
                          xNext.rows = record.input.rows ∧
                          xNext.selected = record.input.selected ∧
                          xNext.rewards = record.input.rewards ∧
                          xNext.time.val = record.input.time.val + 1 ∧
                          ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain
                            xNext payload finished clockFinished.clock.lastProposal) ∧
                      (ReferenceContinuingCollectionStartDomains.sourceRound record.input.time = p.T →
                        ReferenceContinuingCollectionRejectedFinishDomains.continuingCollectionReadyBoundaryDomain
                          (ReferenceActivePhysicalStep.step record.input).next payload finished
                          clockFinished.clock.lastProposal) ∧
              rejectionEligible record.input = true ∧
              record.output = ReferenceActivePhysicalStep.step record.input ∧
              record.output.next = (prefixAt (j + 1) (by omega)).finalState) ∧
          (∀ _hend : j = Q.length, (hindexStop : b + j < count) →
            let record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) :=
              execution.records[b + j]'(by
                have hcount : execution.records.length = count := by
                  simpa [execution, generatedFirstCutoffRun] using
                    ReferenceActivePhysicalHorizon.run_record_count initial z.1.2
                      (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s count hspan active
                rw [hcount]
                exact hindexStop)
            ∃ _hready :
                ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain
                  record.input payload l saved,
              ∃ cutoff : Fin p.T, cutoff.val + 1 = l.cutoff ∧
              ∃ (core : CoordinatorRoundDispatch.CollectionCoreValid
                    (ReferenceActivePhysicalStep.collectionInput record.input payload l
                      (ReferenceActivePhysicalStep.collectionClock payload l saved cutoff) cutoff))
                (snap : CoordinatorCollectionInteractive.PreparedSnapshot
                    (ReferenceActivePhysicalStep.collectionInput record.input payload l
                      (ReferenceActivePhysicalStep.collectionClock payload l saved cutoff) cutoff))
                (hb : snap.clockStarted.clock.g ≤ p.T + 1)
                (hs : CoordinatorRoundDispatch.collectionCurrentScoresCheck
                    (ReferenceActivePhysicalStep.collectionInput record.input payload l
                      (ReferenceActivePhysicalStep.collectionClock payload l saved cutoff) cutoff) = true),
              let prepared := ReferenceActivePhysicalStep.prepare record.input
              let weights := CoordinatorCollectionInteractive.PreObservationInputs.weights
                (ReferenceActivePhysicalStep.collectionInput record.input payload l
                  (ReferenceActivePhysicalStep.collectionClock payload l saved cutoff) cutoff)
                snap.inputsValid.ledger_valid snap.inputsValid.assignment_eq
              let recordingInput := ReferenceActivePhysicalStep.collectionRecordingInput
                prepared payload snap.clockStarted weights
              prepared.coordinator = .collection payload l
                (ReferenceActivePhysicalStep.collectionClock payload l saved cutoff)
                cutoff (.continuing core snap hb hs) ∧
              prepared.coordinator.arm = snap.arm ∧
              CoordinatorRecorderComplementBridge.LocalInputsValid recordingInput ∧
              CoordinatorRecordingOperation.InputsValid
                (CoordinatorRecorderComplementBridge.recorderInput recordingInput) ∧
              ∃ (c : ReferenceCollectionSegmentExtraction.Choice rate)
                (o : CoordinatorRecordingOperation.Output p)
                (l1 : ReferenceActivePhysicalStep.Ledger rate),
                ReferenceCollectionSegmentExtraction.choice record.input = some c ∧
                CoordinatorRecorderComplementBridge.run
                  (ReferenceActivePhysicalStep.collectionRecordingInput
                    prepared c.payload c.started c.weights) = some o ∧
                c.payload = payload ∧ c.preLedger = l ∧
                c.started = snap.clockStarted ∧ c.initializer = none ∧
                CoordinatorCollectionLedger.startRound c.preLedger
                  (record.input.time.val + 1)
                  (ReferenceActivePhysicalStep.collectionEnabled c.preLedger record.input.time)
                  (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder o) = .success l1 ∧
                ∃ M,
                  ReferenceCollectionSegmentExtraction.effectiveParse record.input l1 = some M ∧
                  CoordinatorCollectionLedger.acceptUpCheck l1
                    (ReferenceActivePhysicalStep.upSenderIndex record.input) M = true ∧
                  rejectionEligible record.input = false) ∧
          (∀ _hend : j = Q.length, b + j = count →
            (prefixAt j hj).finalState = execution.finalState) := by
  classical
  let initial := ReferenceFirstLaunchNumericalCell.launchState rate z rewards C_star C_h hc
  let execution := generatedFirstCutoffRun rate z rewards C_star C_h hc s hsElapsed count hspan
  let window := firstLiveWindow execution.records
  let w := window.length
  let b := w + 1
  let Q := (execution.records.drop b).takeWhile
    (fun record => rejectionEligible record.input)
  let active := generatedLaunchActive rate z rewards C_star C_h hc s hsElapsed
  have hcount : execution.records.length = count := by
    simpa [execution, generatedFirstCutoffRun] using
      ReferenceActivePhysicalHorizon.run_record_count initial z.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s count hspan active
  have htail : b + Q.length ≤ count := by
    have hw : w < count := by simpa [execution, window] using hshort
    have hprefix : Q <+: execution.records.drop b := List.takeWhile_prefix _
    have hlength := hprefix.length_le
    have hdrop : (execution.records.drop b).length = count - b := by
      simp [List.length_drop, hcount]
    omega
  let prefixAt := fun (j : ℕ) (hj : j ≤ Q.length) =>
    ReferenceActivePhysicalHorizon.run initial z.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s (b + j)
      (by omega) active
  have hseed := seed_ready_boundary rate z rewards C_star C_h hc s hsElapsed count hspan hshort
  dsimp only at hseed
  obtain ⟨cut, payload, ledger0, saved, hcut, hcutNext, hseedCoord,
    hseedPending, hseedSigma, hseedCutoff, hseedReady, hseedBoundary⟩ := hseed
  have hseedPrefix :
      (prefixAt 0 (by omega)).finalState = cut.output.next := by
    simpa [prefixAt, initial, execution, window, w, b, active] using hcutNext

  have hboundary : ∀ j (hj : j ≤ Q.length),
      ∃ l : ReferenceActivePhysicalStep.Ledger rate,
        (prefixAt j hj).finalState.coordinator = .collection payload l saved ∧
        l.pending = Finset.univ ∧ l.sigma = s + 1 ∧ l.cutoff = s + b ∧
        (∀ htime : s + b + j < p.T,
          ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain
            (ReferenceActivePhysicalHorizon.roundInputAt initial z.1.2
              (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s active
              (prefixAt j hj) ⟨s + b + j, by omega, htime⟩) payload l saved) ∧
        (∀ hindex : b + j < count,
          ReferenceActivePhysicalHorizon.roundInputAt initial z.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s active
            (prefixAt j hj) ⟨s + b + j, by omega, by omega⟩ =
          (execution.records[b + j]'(by
            rw [hcount]
            exact hindex)).input) ∧
        (s + b + j = p.T →
          ReferenceContinuingCollectionRejectedFinishDomains.continuingCollectionReadyBoundaryDomain
            (prefixAt j hj).finalState payload l saved) := by
    intro j
    induction j with
    | zero =>
        intro hj
        refine ⟨ledger0, ?_, hseedPending, hseedSigma, hseedCutoff, ?_, ?_, ?_⟩
        · simpa [prefixAt] using hseedCoord
        · intro htime
          have hready := hseedReady (by simpa using htime)
          simpa [prefixAt, initial, execution, window, w, b, active] using hready
        · intro hindex
          have hrecord := next_input_eq_record initial z.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s count b
            hspan active hindex
          simpa only [prefixAt, Nat.add_zero, execution, generatedFirstCutoffRun] using hrecord
        · intro hterminal
          exact hseedBoundary (by simpa using hterminal)
    | succ j ih =>
        intro hj
        have hjlt : j < Q.length := by omega
        have hjprev : j ≤ Q.length := Nat.le_of_lt hjlt
        obtain ⟨l, hstate, hpending, hsigmaBoundary, hcutoffBoundary,
          hreadyBoundary, hinputBoundary, hterminalBoundary⟩ :=
          ih hjprev
        have hdropLength : (execution.records.drop b).length = count - b := by
          simp [List.length_drop, hcount]
        have hdropIndex : j < (execution.records.drop b).length := by
          have hprefix : Q <+: execution.records.drop b := List.takeWhile_prefix _
          have hlen := hprefix.length_le
          omega
        have hrecordEq : Q[j]'hjlt = execution.records[b + j]'(by
            rw [hcount]
            have hjb : b + j < b + Q.length := Nat.add_lt_add_left hjlt b
            omega) := by
          have htake := getElem_takeWhile_eq
            (fun record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) =>
              rejectionEligible record.input)
            (execution.records.drop b) j hjlt
          have hdrop : (execution.records.drop b)[j]'hdropIndex =
              execution.records[b + j]'(by
                rw [hcount]
                omega) := by
            simp only [List.getElem_drop]
          exact htake.trans hdrop
        have hmem : Q[j]'hjlt ∈ Q := List.getElem_mem _
        have heligible : rejectionEligible (execution.records[b + j]'(by
            rw [hcount]
            omega)).input = true := by
          have hp := List.mem_takeWhile_imp hmem
          simpa [hrecordEq] using hp
        have hindex : b + j < count := by
          have hjb : b + j < b + Q.length := Nat.add_lt_add_left hjlt b
          omega
        let record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) :=
          execution.records[b + j]'(by rw [hcount]; exact hindex)
        let current := prefixAt j hjprev
        let xBoundary := ReferenceActivePhysicalHorizon.roundInputAt initial z.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s active current
          ⟨s + b + j, by omega, by omega⟩
        have hinput : xBoundary = record.input := by
          have h := hinputBoundary hindex
          simpa [current, prefixAt, record] using h
        have hready : ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain
            record.input payload l saved := by
          rw [← hinput]
          exact hreadyBoundary (by omega)
        have hR := ReferenceContinuingCollectionRejectedFinishDomains.continuing_collection_rejected_finish_domains
          record.input payload l saved hready
        dsimp only at hR
        obtain ⟨cutoff, hcutoff, core, snap, hb, hs, hcoord, harm, hlocal,
          hrecordInputs, o, l1, hrecording, hstart, hl1Candidate, hvalid, hphase,
          hcursor1, hσ1, hcut1, hfreeze1, hpending1, hassignment1, hbase1,
          hcutRegisters1, hincrement1, hregisters1, hmass, hcurrent1, hcutDomain1,
          hzero1, hgamma1, hraw1, hhistory1, hbranch⟩ := hR
        let input := ReferenceActivePhysicalStep.collectionInput record.input payload l
          (ReferenceActivePhysicalStep.collectionClock payload l saved cutoff) cutoff
        let prepared := ReferenceActivePhysicalStep.prepare record.input
        let weights := CoordinatorCollectionInteractive.PreObservationInputs.weights input
          snap.inputsValid.ledger_valid snap.inputsValid.assignment_eq
        let recordingInput := ReferenceActivePhysicalStep.collectionRecordingInput prepared
          payload snap.clockStarted weights
        let c : ReferenceCollectionSegmentExtraction.Choice rate :=
          ⟨payload, l, snap.clockStarted, weights, none⟩
        have hrecordingChoice : CoordinatorRecorderComplementBridge.run
            (ReferenceActivePhysicalStep.collectionRecordingInput
              (ReferenceActivePhysicalStep.prepare record.input)
              c.payload c.started c.weights) = some o := by
          simpa [c, recordingInput, weights, input] using hrecording
        have hchoice : ReferenceCollectionSegmentExtraction.choice record.input = some c := by
          unfold ReferenceCollectionSegmentExtraction.choice
          rw [hcoord]
          simp [ReferenceCollectionSegmentExtraction.choiceOfCut,
            ReferenceActivePhysicalStep.DispatchCut.selection,
            c, weights, input]
        have hstart' : CoordinatorCollectionLedger.startRound c.preLedger
            (record.input.time.val + 1)
            (ReferenceActivePhysicalStep.collectionEnabled c.preLedger record.input.time)
            (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder o) = .success l1 := by
          simpa [c, ReferenceContinuingCollectionStartDomains.sourceRound] using hstart
        have hprojected : rejectionEligible record.input =
            (match ReferenceCollectionSegmentExtraction.effectiveParse record.input l1 with
            | none => true
            | some M => !CoordinatorCollectionLedger.acceptUpCheck l1
                (ReferenceActivePhysicalStep.upSenderIndex record.input) M) := by
          unfold rejectionEligible
          simp only [hchoice, hrecordingChoice, hstart']
        have hselector : rejectionEligible record.input = true := heligible
        let receptionInput := ReferenceUpReception.receptionInputAtRow rate record.input.row
          (ReferenceActivePhysicalStep.upInputs prepared l1) record.input.time
        let expected := ReferenceActivePhysicalStep.upExpected prepared
        let decoderRaw := (CoordinatorUpReception.decoderTransition receptionInput).2
        let filteredParsed := CoordinatorUpReception.parseDecoderOutput (eta := rate.eta.val)
          (ReferenceUpReception.filterRawByExpected decoderRaw expected)
        have hfilter : filteredParsed = none ∨
            ∃ M, filteredParsed = some M ∧
              CoordinatorCollectionLedger.acceptUpCheck l1
                (ReferenceActivePhysicalStep.upSenderIndex record.input) M = false := by
          cases hp : ReferenceCollectionSegmentExtraction.effectiveParse record.input l1 with
          | none => left; simpa only [filteredParsed, ReferenceCollectionSegmentExtraction.effectiveParse,
                prepared, receptionInput, decoderRaw, expected] using hp
          | some M =>
              right
              have hacc : CoordinatorCollectionLedger.acceptUpCheck l1
                  (ReferenceActivePhysicalStep.upSenderIndex record.input) M = false := by
                have hselector' :
                    !CoordinatorCollectionLedger.acceptUpCheck l1
                      (ReferenceActivePhysicalStep.upSenderIndex record.input) M = true := by
                  rw [hprojected, hp] at hselector
                  exact hselector
                cases ha : CoordinatorCollectionLedger.acceptUpCheck l1
                    (ReferenceActivePhysicalStep.upSenderIndex record.input) M with
                | false => rfl
                | true => simp [ha] at hselector'
              exact ⟨M, by simpa only [filteredParsed, ReferenceCollectionSegmentExtraction.effectiveParse,
                prepared, receptionInput, decoderRaw, expected] using hp,
                hacc⟩
        have hbranchResult := hbranch hfilter
        rcases hbranchResult with ⟨decoded, bank, hreceive, hdecoded, hreceiveDomain,
          hreceiveCheck, hdiagnostic, finished, hfinish, hfinishedCandidate,
          hincrement, hgamma, hcursor, hfinishedPhase, hfinishedPending,
          hfinishedAssignment, hfinishedBase, hfinishedCutoffRegisters,
          hfinishedCurrentRegisters, hfinishedRawBuffer, hfinishedHistory,
          hfinishedBudgets, hfinishedRawDomain, hfinishedHistoryDomain,
          hfinishedValid, clockFinished, hclockFinish, hclockSame, hclockPending,
          hclockCommand, hproposalSaved, hcollectionFinish, hobserve,
          hstepCoordinator, hnextCoordinator, hnextBank, hactivations,
          hfollowers, hownEntries, hnextReady, hterminal⟩
        have hfinishedUniv : finished.pending = Finset.univ := by
          rw [hfinishedPending, hpending]
        have hfinishedSigma : finished.sigma = s + 1 := by
          calc
            finished.sigma = l1.sigma := by rw [hfinishedCandidate, hdecoded]; rfl
            _ = s + 1 := hσ1.trans hsigmaBoundary
        have hfinishedCutoff : finished.cutoff = s + b := by
          calc
            finished.cutoff = l1.cutoff := by rw [hfinishedCandidate, hdecoded]; rfl
            _ = s + b := hcut1.trans hcutoffBoundary
        have hnextState : (prefixAt (j + 1) (by omega)).finalState =
            (ReferenceActivePhysicalStep.step record.input).next := by
          have hrun := run_successor_state_eq initial z.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s (b + j)
            (by omega) active record.input (by
              simpa only [current, prefixAt, xBoundary, Nat.add_assoc] using hinput)
          simpa [prefixAt, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hrun
        have hnextBoundary :
            ∃ lnext : ReferenceActivePhysicalStep.Ledger rate,
              (prefixAt (j + 1) (by omega)).finalState.coordinator =
                .collection payload lnext saved ∧ lnext.pending = Finset.univ ∧
              lnext.sigma = s + 1 ∧ lnext.cutoff = s + b ∧
              (∀ htime : s + b + (j + 1) < p.T,
                ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain
                  (ReferenceActivePhysicalHorizon.roundInputAt initial z.1.2
                    (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s active
                    (prefixAt (j + 1) (by omega)) ⟨s + b + (j + 1), by omega, htime⟩)
                  payload lnext saved) ∧
              (∀ hindex : b + (j + 1) < count,
                ReferenceActivePhysicalHorizon.roundInputAt initial z.1.2
                  (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s active
                  (prefixAt (j + 1) (by omega)) ⟨s + b + (j + 1), by omega, by omega⟩ =
                (execution.records[b + (j + 1)]'(by rw [hcount]; exact hindex)).input) ∧
              (s + b + (j + 1) = p.T →
                ReferenceContinuingCollectionRejectedFinishDomains.continuingCollectionReadyBoundaryDomain
                  (prefixAt (j + 1) (by omega)).finalState payload lnext saved) := by
          have hcalendar : ReferenceContinuingCollectionStartDomains.sourceRound record.input.time =
              s + b + j + 1 := by
            have ht := congrArg (fun y : ReferenceActivePhysicalStep.RoundInput p rate => y.time.val) hinput
            change s + b + j = record.input.time.val at ht
            change record.input.time.val + 1 = s + b + j + 1
            omega
          by_cases hnextTime : s + b + j + 1 < p.T
          · obtain ⟨xNext, hstateNext, hrowsNext, hselectedNext, hrewardsNext,
              htimeNext, hnextReadyDomain⟩ := hnextReady (by simpa [hcalendar] using hnextTime)
            have hnextInput : xNext =
                ReferenceActivePhysicalHorizon.roundInputAt initial z.1.2
                  (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s active
                  (prefixAt (j + 1) (by omega))
                  ⟨s + b + (j + 1), by omega, hnextTime⟩ := by
              apply round_input_ext
              · simpa only [ReferenceActivePhysicalHorizon.roundInputAt] using
                  hstateNext.trans hnextState.symm
              · simpa only [← hinput, xBoundary, ReferenceActivePhysicalHorizon.roundInputAt] using
                  hrowsNext
              · simpa only [← hinput, xBoundary, ReferenceActivePhysicalHorizon.roundInputAt] using
                  hselectedNext
              · apply Fin.ext
                change xNext.time.val = s + b + (j + 1)
                calc
                  xNext.time.val = record.input.time.val + 1 := htimeNext
                  _ = s + b + (j + 1) := by
                    simpa only [ReferenceContinuingCollectionStartDomains.sourceRound,
                      Nat.add_assoc] using hcalendar
              · simpa only [← hinput, xBoundary, ReferenceActivePhysicalHorizon.roundInputAt] using
                  hrewardsNext
            refine ⟨finished, ?_, hfinishedUniv, hfinishedSigma, hfinishedCutoff, ?_, ?_, ?_⟩
            · rw [hnextState, hnextCoordinator, hproposalSaved]
            · intro htime
              have hdom := hnextReadyDomain
              rw [hproposalSaved] at hdom
              rw [← hnextInput]
              exact hdom
            · intro hindex
              simpa only [prefixAt, execution, generatedFirstCutoffRun, Nat.add_assoc] using
                next_input_eq_record initial z.1.2
                  (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s count
                  (b + (j + 1)) hspan active hindex
            · intro hterminal
              omega
          · have hterminalTime : s + b + j + 1 = p.T := by omega
            have hboundaryNext := hterminal
              (by simpa [hcalendar] using hterminalTime)
            refine ⟨finished, ?_, hfinishedUniv, hfinishedSigma, hfinishedCutoff, ?_, ?_, ?_⟩
            · rw [hnextState, hnextCoordinator, hproposalSaved]
            · intro htime
              omega
            · intro hindex
              simpa only [prefixAt, execution, generatedFirstCutoffRun, Nat.add_assoc] using
                next_input_eq_record initial z.1.2
                  (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s count
                  (b + (j + 1)) hspan active hindex
            · intro hterminal
              simpa [hnextState, hproposalSaved] using hboundaryNext
        rcases hnextBoundary with ⟨lnext, hnextCoordBoundary, hnextPendBoundary, hnextSigmaBoundary,
          hnextCutoffBoundary, hnextReadyBoundary, hnextIndexBoundary, hnextTerminalBoundary⟩
        refine ⟨lnext, hnextCoordBoundary, hnextPendBoundary, hnextSigmaBoundary,
          hnextCutoffBoundary, hnextReadyBoundary, hnextIndexBoundary, hnextTerminalBoundary⟩

  refine ⟨cut, payload, saved, hcut, hseedPrefix, ?_⟩
  intro j hj
  obtain ⟨l, hstate, hpending, hsigma, hcutoff, hready, hindex, hterminal⟩ := hboundary j hj
  refine ⟨l, hstate, hpending, hsigma, hcutoff, hready, hindex, hterminal, ?_, ?_, ?_⟩
  · intro hstep
    have hstepQ : j < Q.length := hstep
    have hindexQ : b + j < count := by
      have hjlt : j < Q.length := hstep
      have hjb : b + j < b + Q.length := Nat.add_lt_add_left hjlt b
      omega
    let record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) :=
      execution.records[b + j]'(by rw [hcount]; exact hindexQ)
    have hmem : Q[j]'hstep ∈ Q := List.getElem_mem _
    have heligible : rejectionEligible record.input = true := by
      have htake := List.mem_takeWhile_imp hmem
      have hget := getElem_takeWhile_eq
        (fun record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) =>
          rejectionEligible record.input)
        (execution.records.drop b) j hstep
      have hdropIndex : j < (execution.records.drop b).length := by
        have hpref : Q <+: execution.records.drop b := List.takeWhile_prefix _
        exact Nat.lt_of_lt_of_le hstep hpref.length_le
      have hdrop : (execution.records.drop b)[j]'hdropIndex = record := by
        simp [record, List.getElem_drop]
      rw [hget, hdrop] at htake
      exact htake
    have hrecordInput :
        ReferenceActivePhysicalHorizon.roundInputAt initial z.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s active
          (prefixAt j (Nat.le_of_lt hstep)) ⟨s + b + j, by omega, by omega⟩ = record.input := by
      simpa [record] using hindex hindexQ
    have hreadyStep : ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain
        record.input payload l saved := by
      rw [← hrecordInput]
      exact hready (by omega)
    have hR := ReferenceContinuingCollectionRejectedFinishDomains.continuing_collection_rejected_finish_domains
      record.input payload l saved hreadyStep
    dsimp only at hR
    obtain ⟨cutoff, hcutoff, core, snap, hb, hs, hcoord, harm, hlocal,
      hrecordInputs, o, l1, hrecording, hstart, hl1Candidate, hvalid, hphase,
      hcursor1, hσ1, hcut1, hfreeze1, hpending1, hassignment1, hbase1,
      hcutRegisters1, hincrement1, hregisters1, hmass, hcurrent1, hcutDomain1,
      hzero1, hgamma1, hraw1, hhistory1, hbranch⟩ := hR
    let input := ReferenceActivePhysicalStep.collectionInput record.input payload l
      (ReferenceActivePhysicalStep.collectionClock payload l saved cutoff) cutoff
    let prepared := ReferenceActivePhysicalStep.prepare record.input
    let weights := CoordinatorCollectionInteractive.PreObservationInputs.weights input
      snap.inputsValid.ledger_valid snap.inputsValid.assignment_eq
    let recordingInput := ReferenceActivePhysicalStep.collectionRecordingInput prepared
      payload snap.clockStarted weights
    let c : ReferenceCollectionSegmentExtraction.Choice rate :=
      ⟨payload, l, snap.clockStarted, weights, none⟩
    have hchoice : ReferenceCollectionSegmentExtraction.choice record.input = some c := by
      unfold ReferenceCollectionSegmentExtraction.choice
      rw [hcoord]
      simp [ReferenceCollectionSegmentExtraction.choiceOfCut,
        ReferenceActivePhysicalStep.DispatchCut.selection, c, weights, input]
    have hrecording' : CoordinatorRecorderComplementBridge.run
        (ReferenceActivePhysicalStep.collectionRecordingInput
          (ReferenceActivePhysicalStep.prepare record.input)
          c.payload c.started c.weights) = some o := by
      simpa only [c, recordingInput, prepared] using hrecording
    have hstart' : CoordinatorCollectionLedger.startRound c.preLedger
        (record.input.time.val + 1)
        (ReferenceActivePhysicalStep.collectionEnabled c.preLedger record.input.time)
        (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder o) = .success l1 := by
      simpa [c, ReferenceContinuingCollectionStartDomains.sourceRound] using hstart
    let receptionInput := ReferenceUpReception.receptionInputAtRow rate record.input.row
      (ReferenceActivePhysicalStep.upInputs prepared l1) record.input.time
    let expected := ReferenceActivePhysicalStep.upExpected prepared
    let decoderRaw := (CoordinatorUpReception.decoderTransition receptionInput).2
    let filteredParsed := CoordinatorUpReception.parseDecoderOutput (eta := rate.eta.val)
      (ReferenceUpReception.filterRawByExpected decoderRaw expected)
    have hfilter : filteredParsed = none ∨
        ∃ M, filteredParsed = some M ∧
          CoordinatorCollectionLedger.acceptUpCheck l1
            (ReferenceActivePhysicalStep.upSenderIndex record.input) M = false := by
      cases hp : ReferenceCollectionSegmentExtraction.effectiveParse record.input l1 with
      | none => left; simpa only [filteredParsed, ReferenceCollectionSegmentExtraction.effectiveParse,
                prepared, receptionInput, decoderRaw, expected] using hp
      | some M =>
          right
          have hacc : CoordinatorCollectionLedger.acceptUpCheck l1
              (ReferenceActivePhysicalStep.upSenderIndex record.input) M = false := by
            have hproj : rejectionEligible record.input =
                (match ReferenceCollectionSegmentExtraction.effectiveParse record.input l1 with
                | none => true
                | some M => !CoordinatorCollectionLedger.acceptUpCheck l1
                    (ReferenceActivePhysicalStep.upSenderIndex record.input) M) := by
              simp [rejectionEligible, hchoice, hrecording', hstart']
            rw [hproj, hp] at heligible
            cases ha : CoordinatorCollectionLedger.acceptUpCheck l1
                (ReferenceActivePhysicalStep.upSenderIndex record.input) M with
            | false => rfl
            | true => simp [ha] at heligible
          exact ⟨M, by
            simpa only [filteredParsed, ReferenceCollectionSegmentExtraction.effectiveParse,
                prepared, receptionInput, decoderRaw, expected] using hp,
            hacc⟩
    rcases hbranch hfilter with ⟨decoded, bank, hreceive, hdecoded, hreceiveDomain,
      hreceiveCheck, hdiagnostic, finished, hfinish, hfinishedCandidate,
      hincrement, hgamma, hcursor, hfinishedPhase, hfinishedPending,
      hfinishedAssignment, hfinishedBase, hfinishedCutoffRegisters,
      hfinishedCurrentRegisters, hfinishedRawBuffer, hfinishedHistory,
      hfinishedBudgets, hfinishedRawDomain, hfinishedHistoryDomain,
      hfinishedValid, clockFinished, hclockFinish, hclockSame, hclockPending,
      hclockCommand, hproposalSaved, hcollectionFinish, hobserve,
      hstepCoordinator, hnextCoordinator, hnextBank, hactivations,
      hfollowers, hownEntries, hnextReady, hterminalStep⟩
    have hnextState : (prefixAt (j + 1) (by omega)).finalState =
        (ReferenceActivePhysicalStep.step record.input).next := by
      have hrun := run_successor_state_eq initial z.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s (b + j)
        (by omega) active record.input (by
          simpa only [prefixAt, Nat.add_assoc] using hrecordInput)
      simpa [prefixAt, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hrun
    have hbank : bank = CoordinatorUpReception.decoderBankAfter receptionInput := by
      have hpacked := ReferenceUpReception.receiveUpFilteredAtRow_eq_filtered_decode
        rate record.input.row (ReferenceActivePhysicalStep.upInputs prepared l1) record.input.time
        (prepared.followers.followers (ReferenceActivePhysicalStep.upSenderIndex record.input))
        (prepared.follower_alignment _).1 (prepared.follower_alignment _).2.1
        (prepared.follower_alignment _).2.2.1 rfl hreceiveCheck
      have hreceiver := hreceive
      change ReferenceUpReception.receiveUpFilteredAtRow rate record.input.row
        (ReferenceActivePhysicalStep.upInputs prepared l1) record.input.time
        (prepared.followers.followers (ReferenceActivePhysicalStep.upSenderIndex record.input))
        (prepared.follower_alignment _).1 (prepared.follower_alignment _).2.1
        (prepared.follower_alignment _).2.2.1 rfl = .rejected (decoded, bank) at hreceiver
      rw [hpacked] at hreceiver
      exact CoordinatorUpReception.packDecodeResult_output_bank _ _ _ (Or.inr hreceiver)
    have hfailure : (ReferenceActivePhysicalStep.step record.input).coordinator.failure = none := by
      rw [hstepCoordinator, hobserve, hcollectionFinish]
    refine ⟨hreadyStep, cutoff, hcutoff, core, snap, hb, hs, hcoord, harm, hlocal,
      hrecordInputs, c, o, l1, hchoice, hrecording', rfl, rfl, rfl, rfl, hstart', hfilter,
      decoded, bank, hreceive, hdecoded, hbank, hdiagnostic, finished, hfinish,
      hfinishedCandidate, hincrement, hgamma,
      hfinishedPhase, hfinishedPending, hfinishedAssignment, hfinishedBase,
      hfinishedCurrentRegisters, hfinishedRawBuffer, hfinishedHistory,
      hfinishedValid, clockFinished, hclockFinish, hclockSame, hclockPending,
      hclockCommand, hproposalSaved, hcollectionFinish, hobserve, hstepCoordinator, hfailure,
      hnextCoordinator, hnextBank, hactivations, hfollowers, hownEntries,
      hnextReady, hterminalStep, heligible, ?_, ?_⟩
    · exact ReferenceActivePhysicalHorizon.RoundRecord.output_eq record
    · rw [ReferenceActivePhysicalHorizon.RoundRecord.output_eq, hnextState]
  · intro hend hstop
    let record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) :=
      execution.records[b + j]'(by rw [hcount]; exact hstop)
    have hstopQ : b + Q.length < count := by simpa [hend] using hstop
    have htime : s + b + j < p.T := by
      have htime' : s + (b + Q.length) < p.T :=
        Nat.lt_of_lt_of_le (Nat.add_lt_add_left hstopQ s) hspan
      simpa [hend, Nat.add_assoc] using htime'
    have hreadyStop : ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain
        record.input payload l saved := by
      have h := hready htime
      have hrecordInput := hindex hstop
      rw [← hrecordInput]
      exact h
    have hstopWitness := ready_attempt_witnesses record.input payload l saved hreadyStop
    dsimp only at hstopWitness
    obtain ⟨cutoff, hcutoff, core, snap, hb, hs, hcoord, harm, hlocal,
      hrecordInputs, c, o, l1, hchoice, hrecord, hstart, hcp, hcl,
      hcstarted, hcinit, hfalse⟩ := hstopWitness
    have hxs : (execution.records.drop b).length = count - b := by
      simp [List.length_drop, hcount]
    have hshortQ : Q.length < (execution.records.drop b).length := by
      rw [hxs]
      omega
    have hpred := takeWhile_false_at_stop
      (fun r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) =>
        rejectionEligible r.input)
      (execution.records.drop b) hshortQ
    have hdropIndex : Q.length < (execution.records.drop b).length := hshortQ
    have hdrop : (execution.records.drop b)[Q.length]'hdropIndex = record := by
      have hjEq : j = Q.length := hend
      subst j
      change (execution.records.drop b)[Q.length]'hdropIndex =
        execution.records[b + Q.length]'(by rw [hcount]; omega)
      simp only [List.getElem_drop]
    have hstopRecord : rejectionEligible record.input = false := by
      have hpredQ : rejectionEligible ((execution.records.drop b)[Q.length]'hdropIndex).input = false := by
        simpa [Q] using hpred
      rw [← hdrop]
      exact hpredQ
    obtain ⟨M, hparse, haccepted⟩ := hfalse hstopRecord
    refine ⟨hreadyStop, cutoff, hcutoff, core, snap, hb, hs, hcoord, harm, hlocal,
      hrecordInputs, c, o, l1, hchoice, hrecord, hcp, hcl, hcstarted, hcinit,
      hstart, M, hparse, haccepted,
      hstopRecord⟩
  · intro hend hfinal
    subst j
    have hspanEq : b + Q.length = count := hfinal
    change (ReferenceActivePhysicalHorizon.run initial z.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s (b + Q.length)
      (by omega) active).finalState = execution.finalState
    simp only [hspanEq, execution, generatedFirstCutoffRun, initial]

end Bandits.Support.ReferenceGeneratedFirstCollectionRejectedPrefix

end
