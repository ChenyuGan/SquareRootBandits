/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bandits Lean regret formalization contributors.
-/
module

public import Bandits.Support.ReferenceGeneratedFirstCutoffFollowerSeed
public import Bandits.Support.ReferenceGeneratedFirstCutoffCoordinatorEndpoint
public import Bandits.Support.ReferenceFirstCollectionFollowerPreparation
public import Bandits.Support.ReferenceFirstCollectionFollowerObservation

import Lean.Elab.Tactic.Omega

/-!
# Generated first-collection follower prefix

Sources: `sources/zip4/manuscript/06_interruptions.tex:9-100,246-295`,
`sources/zip4/manuscript/04_slow_fast_learner.tex:157-174`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-64`,
`sources/zip4/manuscript/07_public_setup.tex:127-164`, and
`sources/zip4/manuscript/05_binary_transport.tex:70-124`.

This module joins the actual generated cutoff follower seed to the same
cutoff's coordinator endpoint, then carries the resulting local follower and
coordinator fields along the original physical collection prefix. It proves
no source-law, probability, regret, section, or main-theorem closure.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceFirstLiveConfirmationHistory
open Bandits.Support.ReferenceCollectionPhaseHistory
open Bandits.Support.ReferenceAssignmentPayloadChronology
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.ActiveFollowerLifecycle
open Bandits.Support.CoordinatorUpReception
open Bandits.Support.CoordinatorCollectionLedger
open Bandits.Support.FollowerCutoffScan

namespace Bandits.Support.ReferenceGeneratedFirstCollectionFollowerPrefix

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput
abbrev RewardTable := ActualInitializationPhysicalStep.GridRewardTable

variable {p : Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}

private theorem first_collection_window_length_bound
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hshort : (firstLiveWindow
      (ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan active).records).length
        < count) :
    let execution := ReferenceActivePhysicalHorizon.run initial rows J rewards
      start count hspan active
    let d := (firstLiveWindow execution.records).length
    let b := d + 1
    let W := (execution.records.drop b).takeWhile
      (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input)
    b + W.length ≤ count := by
  classical
  let execution := ReferenceActivePhysicalHorizon.run initial rows J rewards
    start count hspan active
  let d := (firstLiveWindow execution.records).length
  let b := d + 1
  let W := (execution.records.drop b).takeWhile
    (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input)
  have hcount : execution.records.length = count := by
    simpa [execution] using ReferenceActivePhysicalHorizon.run_record_count
      initial rows J rewards start count hspan active
  have hd : d < count := by simpa [execution, d] using hshort
  have hprefix : W <+: execution.records.drop b := List.takeWhile_prefix _
  have hlength := hprefix.length_le
  have hdrop : (execution.records.drop b).length = count - b := by
    simp [List.length_drop, hcount]
  have hbound : b + W.length ≤ count := by
    have htail : W.length ≤ count - b := by simpa [hdrop] using hlength
    omega
  simpa [execution, d, b, W] using hbound

/-- The actual records of a physical run are indexed by the literal
`actualRunRecordAt` constructor at the same original calendar coordinate. -/
private theorem run_records_getElem?_actualRunRecordAt
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (index : ℕ) (hindex : index < count) :
    (ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan active).records[index]? =
      some (ReferenceAssignmentPayloadChronology.actualRunRecordAt initial rows J rewards
        start index (by omega) active) := by
  induction count generalizing index with
  | zero => omega
  | succ count ih =>
      have hspan' : start + (count + 1) ≤ p.T := by omega
      have hprefixSpan : start + count ≤ p.T := by omega
      have hprefixLength :
          (ReferenceActivePhysicalHorizon.run initial rows J rewards start count
            hprefixSpan active).records.length = count :=
        ReferenceActivePhysicalHorizon.run_record_count initial rows J rewards start count
          hprefixSpan active
      rw [ReferenceAssignmentPayloadChronology.run_successor_actualRunRecordAt
        initial rows J rewards start count hspan' active]
      by_cases hlt : index < count
      · rw [List.getElem?_append_left (by simpa [hprefixLength] using hlt)]
        exact ih hprefixSpan index hlt
      · have hlast : index = count := by omega
        subst index
        simp [hprefixLength]

private theorem first_collection_follower_cutoff_seed
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
      (ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun
        rate z rewards C_star C_h hc s hsElapsed count hspan).records).length < count) :
    let initial := ReferenceFirstLaunchNumericalCell.launchState rate z rewards C_star C_h hc
    let execution := ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun
      rate z rewards C_star C_h hc s hsElapsed count hspan
    let window := firstLiveWindow execution.records
    let w := window.length
    let b := w + 1
    let cut := execution.records[w]'(by
      have hw : w < count := by simpa [execution, window, w] using hshort
      have hlen := ReferenceActivePhysicalHorizon.run_record_count initial z.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s count hspan
        (ReferenceGeneratedFirstCutoffSurvival.generatedLaunchActive
          rate z rewards C_star C_h hc s hsElapsed)
      simpa [execution, ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun] using
        Nat.lt_of_lt_of_eq hw hlen.symm)
    let successorSpan : s + b ≤ p.T := by
      have hw : w < count := by simpa [execution, window, w] using hshort
      have : s + (w + 1) ≤ s + count := Nat.add_le_add_left (Nat.succ_le_of_lt hw) s
      omega
    let successor := ReferenceActivePhysicalHorizon.run initial z.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s b successorSpan
      (ReferenceGeneratedFirstCutoffSurvival.generatedLaunchActive
        rate z rewards C_star C_h hc s hsElapsed)
    ∃ (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
      (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
      (base : Fin (p.m - 1) → ℕ),
      cut.input.state.coordinator = .live r q base ∧
      r.payload.sigma.val = s ∧
      (∀ i : Fin (p.m - 1), (r.payload.downRecord i).val.q = 0) ∧
      ∃ (dispatched : CoordinatorStartRoundCutoffDispatch.Output
          (ReferenceActivePhysicalStep.liveInput cut.input r q base).registers
          (ReferenceActivePhysicalStep.liveInput cut.input r q base).ownedRegisters base)
        (hstart : CoordinatorPhaseClock.startRound p rate.eta.val
          (ReferenceActivePhysicalStep.liveInput cut.input r q base).registers.time
          (ReferenceActivePhysicalStep.liveInput cut.input r q base).registers.priorClock
          (ReferenceActivePhysicalStep.liveInput cut.input r q base).registers.clockPending =
            .ok dispatched.startResult)
        (ledger : CoordinatorStartRoundCutoffDispatch.NewLedger
          (ReferenceActivePhysicalStep.liveInput cut.input r q base).registers)
        (hinit : dispatched.collectionInitialization = .success (some ledger))
        (hledger : ledger = CoordinatorStartRoundCutoffDispatch.collectionStartLedger
          (ReferenceActivePhysicalStep.liveInput cut.input r q base).registers
          (ReferenceActivePhysicalStep.liveInput cut.input r q base).ownedRegisters base
          (ReferenceActivePhysicalStep.liveInput cut.input r q base).registers.time)
        (hdomain : CoordinatorStartRoundCutoffDispatch.initializationDomainValid
          (ReferenceActivePhysicalStep.liveInput cut.input r q base).registers
          (ReferenceActivePhysicalStep.liveInput cut.input r q base).ownedRegisters base
          (ReferenceActivePhysicalStep.liveInput cut.input r q base).registers.time)
        (hclock : dispatched.startResult.clock =
          {(ReferenceActivePhysicalStep.liveInput cut.input r q base).registers.priorClock with
            u := some (ReferenceActivePhysicalStep.liveInput cut.input r q base).registers.time})
        (hpending : dispatched.startResult.pending = Finset.univ)
        (hnoAssignment : dispatched.startResult.assignmentStart = none)
        (selected : CoordinatorRoundDispatch.ArmSelection
          (ReferenceActivePhysicalStep.liveInput cut.input r q base).registers.payload
          dispatched.startResult
          (ReferenceActivePhysicalStep.liveInput cut.input r q base).registers.time
          (ReferenceActivePhysicalStep.liveInput cut.input r q base).registers.complementWeights
          cut.input.row),
        cut.output.preparation.coordinator = .live r q base
          (.cutoffChosen dispatched hstart ledger hinit hledger hdomain hclock hpending
            hnoAssignment selected) ∧
        let u := cut.input.time.val + 1
        u = s + w + 1 ∧ u ≤ p.T ∧ u ≤ r.gridBoundary ∧
        ledger.sigma = r.payload.sigma.val + 1 ∧ ledger.cutoff = u ∧
        FollowerCutoffScan.firstCutoff p rate.eta.val r.payload.sigma
          (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
            (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z))) = u ∧
        successor.finalState = cut.output.next ∧
        ∃ movingLedger movingSaved,
          successor.finalState.coordinator = .collection r.payload movingLedger movingSaved ∧
          (∀ i : Fin (p.m - 1),
            ∃ post μ,
              successor.finalState.followers i = .ordinary post μ ∧
              post.status = .unoccupied ∧
              localStateDomainValid post ∧ localBufferValid post ∧ downDecoderStateValid post ∧
              post.S + post.backlog ≤ w * D p ∧
              post.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) ∧
              (∀ saved ∈ post.buffer, saved.calendarRound < s + b + 1) ∧
              ((post.lastDown = none ∧ post.S = 0 ∧ post.delta = 0 ∧ post.backlog = 0) ∨
                post.lastDown = some (r.payload.downRecord i))) := by
  classical
  let initial := ReferenceFirstLaunchNumericalCell.launchState rate z rewards C_star C_h hc
  let execution := ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun
    rate z rewards C_star C_h hc s hsElapsed count hspan
  let window := firstLiveWindow execution.records
  let w := window.length
  let b := w + 1
  let active := ReferenceGeneratedFirstCutoffSurvival.generatedLaunchActive
    rate z rewards C_star C_h hc s hsElapsed
  let cut := execution.records[w]'(by
    have hw : w < count := by simpa [execution, window, w] using hshort
    have hlen := ReferenceActivePhysicalHorizon.run_record_count initial z.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s count hspan active
    simpa [execution, ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun] using
      Nat.lt_of_lt_of_eq hw hlen.symm)
  let successorSpan : s + b ≤ p.T := by
    have hw : w < count := by simpa [execution, window, w] using hshort
    omega
  let successor := ReferenceActivePhysicalHorizon.run initial z.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s b successorSpan active

  have hcore := ReferenceGeneratedFirstCutoffSurvival.run_generated_first_cutoff_survival
    rate z rewards C_star C_h hc s hsElapsed count hspan hshort
  dsimp only [initial, execution, window, w] at hcore
  have hactive : ReferenceActivePhysicalHorizon.allActiveAtStart initial s := hcore.1
  have hfirst : initial.coordinator = .first := hcore.2.1

  have hseed := ReferenceGeneratedFirstCutoffFollowerSeed.actual_first_cutoff_follower_seed
    rate z rewards C_star C_h hc s hsElapsed count hspan hshort
  dsimp only [initial, execution, window, w, b] at hseed
  rcases hseed with ⟨rF, qF, baseF, hliveF, hsigmaF, hqzeroF,
    dispatchedF, hstartF, ledgerF, hinitF, hledgerF, hdomainF, hclockF,
    hpendingF, hnoAssignmentF, selectedF, hcutBranchF, huF, huBoundF,
    hfirstCutoffF, hfollowersF, hsTF, hsuccessorF⟩

  have hendpoint :=
    ReferenceGeneratedFirstCutoffCoordinatorEndpoint.actual_first_cutoff_coordinator_endpoint
      rate z rewards C_star C_h hc s hsElapsed count hspan hshort
  dsimp only [initial, execution, window, w, b] at hendpoint
  rcases hendpoint with ⟨_, cutE, suffixE, hsplitE, hindexE, htimeE,
    hstateE, hrowsE, hselectedE, hrewardsE,
    rE, qE, baseE, hliveE, hsigmaE,
    dispatchedE, hstartE, ledgerE, hinitE, hledgerE, hdomainE, hclockE,
    hpendingE, hnoAssignmentE, selectedE, hcutBranchE, hrestE⟩
  rcases hrestE with ⟨huE, huBoundE, huGridE, hledgerSigmaE, hledgerCutE,
    recordingE, hrestE⟩
  rcases hrestE with ⟨_, hrestE⟩
  rcases hrestE with ⟨_, hrestE⟩
  rcases hrestE with ⟨_, hrestE⟩
  rcases hrestE with ⟨_, hrestE⟩
  rcases hrestE with ⟨ledgerStartedE, hrestE⟩
  rcases hrestE with ⟨_, hrestE⟩
  rcases hrestE with ⟨_, hrestE⟩
  rcases hrestE with ⟨inputE, decodedE, bankE, diagnosticE, finishedE, hrestE⟩
  rcases hrestE with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _hfinishE, _hvalidE, _hclockAllE, hrestE⟩
  rcases hrestE with ⟨_, _, _, _, _, _, _, hsuccessorE, hsuccessorCoordinatorE, _⟩

  have hliveF' : cutE.input.state.coordinator = .live rF qF baseF := by
    rw [hindexE]
    exact hliveF
  have hcoordEq : CoordinatorConfiguration.live rF qF baseF =
      CoordinatorConfiguration.live rE qE baseE := hliveF'.symm.trans hliveE
  cases hcoordEq
  have hw : w < count := by simpa [execution, window, w] using hshort
  have hrunLength := ReferenceActivePhysicalHorizon.run_record_count initial z.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s count hspan active
  have hcutIndexBound : w < execution.records.length := by
    rw [show execution.records.length = count by
      simpa [execution, ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun] using hrunLength]
    exact hw
  have hcutJoin : cutE = cut := by
    have hindexF : cut = execution.records[w]'hcutIndexBound := rfl
    exact hindexE.trans hindexF.symm
  subst cutE
  have hcutPayload : cut.output.preparation.coordinator =
      .live rF qF baseF
        (.cutoffChosen dispatchedE hstartE ledgerE hinitE hledgerE hdomainE hclockE
          hpendingE hnoAssignmentE selectedE) := hcutBranchE
  refine ⟨rF, qF, baseF, ?_, hsigmaE, hqzeroF,
    dispatchedE, hstartE, ledgerE, hinitE, hledgerE, hdomainE, hclockE,
    hpendingE, hnoAssignmentE, selectedE, ?_, ?_⟩
  · exact hliveE
  · exact hcutPayload
  · refine ⟨huF, ?_, ?_, ?_, ?_, hfirstCutoffF, hsuccessorE,
      ⟨finishedE, dispatchedE.startResult.clock.lastProposal, hsuccessorCoordinatorE, ?_⟩⟩
    · rw [htimeE]
      exact huBoundE
    · rw [htimeE]
      exact huGridE
    · exact hledgerSigmaE
    · rw [htimeE]
      exact hledgerCutE
    · intro i
      obtain ⟨old, μ, c, logged, d, recordPost, post,
        hstate, _hwasUnoccupied, _hwasOccupied, hdom, hbuffer, hdecoder, hpair, hstamps,
        _hstart, _hprepared, _hcEq, _hcDom, _hcBuffer, _hcDecoder, _hcMass, _hcPair,
        _hcStamps, _hS, _hdelta, _hbacklog, _hlastDown, _hbufferFrame, _hbatchFrame,
        _hfailureFrame, hlogging, _hloggedBuffer, _hdiagnostic, hrecordResult,
        hdownInput, hdown, hrelease, hconfiguration, hnext, _hfailure,
        hstatus, hpostDom, hpostBuffer, hpostDecoder, hmass, hpostPair, hpostStamps,
        _houtInput, _houtDown, halt⟩ := hfollowersF i
      refine ⟨post, μ, ?_, hstatus, hpostDom, hpostBuffer, hpostDecoder,
        hmass, hpostPair, ?_, halt⟩
      · rw [hsuccessorF]
        exact hnext
      · intro saved hsaved
        have hstamp := hpostStamps saved hsaved
        have htime : cut.input.time.val = s + w := by
          exact htimeE
        omega

/-- Every boundary from the actual first cutoff through the last record before
`laterChosen` retains the original payload shape and a valid, unoccupied
follower state. All induction fields used by the conditional PREPARE and
observation producers are returned literally. -/
theorem actual_first_collection_follower_prefix_boundary
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
      (ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun
        rate z rewards C_star C_h hc s hsElapsed count hspan).records).length < count) :
    let initial := ReferenceFirstLaunchNumericalCell.launchState rate z rewards C_star C_h hc
    let execution := ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun
      rate z rewards C_star C_h hc s hsElapsed count hspan
    let window := firstLiveWindow execution.records
    let w := window.length
    let b := w + 1
    let W := (execution.records.drop b).takeWhile
      (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input)
    let active := ReferenceGeneratedFirstCutoffSurvival.generatedLaunchActive
      rate z rewards C_star C_h hc s hsElapsed
    let htail : b + W.length ≤ count := by
      classical
      have hcount : execution.records.length = count := by
        simpa [execution, ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun] using
          ReferenceActivePhysicalHorizon.run_record_count initial z.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s count hspan active
      have hprefix : W <+: execution.records.drop b := List.takeWhile_prefix _
      have hlength := hprefix.length_le
      have hdrop : (execution.records.drop b).length = count - b := by
        simp [List.length_drop, hcount]
      have _htailLength : W.length ≤ count - b := by simpa [hdrop] using hlength
      have hw : w < count := by simpa [execution, window, w] using hshort
      omega
    let prefixAt := fun (j : ℕ) (hj : j ≤ W.length) =>
      ReferenceActivePhysicalHorizon.run initial z.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s (b + j)
        (by omega) active
    let successor := prefixAt 0 (by omega)
    let cut := execution.records[w]'(by
      have hw : w < count := by simpa [execution, window, w] using hshort
      have hlen := ReferenceActivePhysicalHorizon.run_record_count initial z.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s count hspan active
      have hrun : execution.records.length = count := by
        simpa [execution, ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun] using hlen
      rw [hrun]
      exact hw)
    ∃ (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
      (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
      (base : Fin (p.m - 1) → ℕ),
      cut.input.state.coordinator = .live r q base ∧
      r.payload.sigma.val = s ∧
      (∀ i : Fin (p.m - 1), (r.payload.downRecord i).val.q = 0) ∧
      ∃ (dispatched : CoordinatorStartRoundCutoffDispatch.Output
          (ReferenceActivePhysicalStep.liveInput cut.input r q base).registers
          (ReferenceActivePhysicalStep.liveInput cut.input r q base).ownedRegisters base)
        (hstart : CoordinatorPhaseClock.startRound p rate.eta.val
          (ReferenceActivePhysicalStep.liveInput cut.input r q base).registers.time
          (ReferenceActivePhysicalStep.liveInput cut.input r q base).registers.priorClock
          (ReferenceActivePhysicalStep.liveInput cut.input r q base).registers.clockPending =
            .ok dispatched.startResult)
        (ledger : CoordinatorStartRoundCutoffDispatch.NewLedger
          (ReferenceActivePhysicalStep.liveInput cut.input r q base).registers)
        (hinit : dispatched.collectionInitialization = .success (some ledger))
        (hledger : ledger = CoordinatorStartRoundCutoffDispatch.collectionStartLedger
          (ReferenceActivePhysicalStep.liveInput cut.input r q base).registers
          (ReferenceActivePhysicalStep.liveInput cut.input r q base).ownedRegisters base
          (ReferenceActivePhysicalStep.liveInput cut.input r q base).registers.time)
        (hdomain : CoordinatorStartRoundCutoffDispatch.initializationDomainValid
          (ReferenceActivePhysicalStep.liveInput cut.input r q base).registers
          (ReferenceActivePhysicalStep.liveInput cut.input r q base).ownedRegisters base
          (ReferenceActivePhysicalStep.liveInput cut.input r q base).registers.time)
        (hclock : dispatched.startResult.clock =
          {(ReferenceActivePhysicalStep.liveInput cut.input r q base).registers.priorClock with
            u := some (ReferenceActivePhysicalStep.liveInput cut.input r q base).registers.time})
        (hpending : dispatched.startResult.pending = Finset.univ)
        (hnoAssignment : dispatched.startResult.assignmentStart = none)
        (selected : CoordinatorRoundDispatch.ArmSelection
          (ReferenceActivePhysicalStep.liveInput cut.input r q base).registers.payload
          dispatched.startResult
          (ReferenceActivePhysicalStep.liveInput cut.input r q base).registers.time
          (ReferenceActivePhysicalStep.liveInput cut.input r q base).registers.complementWeights
          cut.input.row),
        cut.output.preparation.coordinator = .live r q base
          (.cutoffChosen dispatched hstart ledger hinit hledger hdomain hclock hpending
            hnoAssignment selected) ∧
        let u := cut.input.time.val + 1
        u = s + w + 1 ∧ u ≤ p.T ∧ u ≤ r.gridBoundary ∧
        ledger.sigma = r.payload.sigma.val + 1 ∧ ledger.cutoff = u ∧
        FollowerCutoffScan.firstCutoff p rate.eta.val r.payload.sigma
          (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
            (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z))) = u ∧
        successor.finalState = cut.output.next ∧
        (∃ movingLedger movingSaved,
          successor.finalState.coordinator = .collection r.payload movingLedger movingSaved) ∧
        (∀ j : ℕ, ∀ hj : j ≤ W.length,
          let boundaryRun := prefixAt j hj
          (boundaryRun.finalState.coordinator = .dagger ∨
            ∃ movingLedger movingSaved,
              boundaryRun.finalState.coordinator = .collection r.payload movingLedger movingSaved) ∧
          (∀ i : Fin (p.m - 1),
            ∃ post μ,
              boundaryRun.finalState.followers i = .ordinary post μ ∧
              post.status = .unoccupied ∧
              localStateDomainValid post ∧ localBufferValid post ∧ downDecoderStateValid post ∧
              post.S ≤ p.T * D p ∧ post.delta ≤ D p ∧ post.backlog ≤ p.T * D p ∧
              post.S + post.backlog ≤ w * D p ∧
              (∀ saved ∈ post.buffer, 1 ≤ saved.calendarRound ∧ saved.calendarRound ≤ p.T) ∧
              (post.buffer.map (fun saved => (saved.calendarRound, saved.pilot))).Nodup ∧
              (∀ saved ∈ post.buffer, ∃ q : ℕ, q ≤ D p ∧
                saved.observation.val = (q : ℝ) / (D p : ℝ)) ∧
              post.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) ∧
              (∀ saved ∈ post.buffer, saved.calendarRound < s + b + j + 1) ∧
              post.downBatch.pending.length < AffineBatchDecoder.quota p ∧
              (∀ batch ∈ post.downBatch.completed,
                batch.length = AffineBatchDecoder.quota p) ∧
              ((post.lastDown = none ∧ post.S = 0 ∧ post.delta = 0 ∧ post.backlog = 0) ∨
                post.lastDown = some (r.payload.downRecord i)))) ∧
      (∀ (j : ℕ) (hj : j < W.length),
        let current := prefixAt j (Nat.le_of_lt hj)
        let next := prefixAt (j + 1) (by
          exact Nat.succ_le_of_lt hj)
        let record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) :=
          execution.records[b + j]'(by
            have hcount : execution.records.length = count := by
              simpa [execution, ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun] using
                ReferenceActivePhysicalHorizon.run_record_count initial z.1.2
                  (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s count hspan active
            have hindex : b + j < count := by
              have hjdrop : b + j < b + W.length := Nat.add_lt_add_left hj b
              exact Nat.lt_of_lt_of_le hjdrop htail
            rw [hcount]
            exact hindex)
        ∀ i : Fin (p.m - 1),
          ∃ incoming μ,
            current.finalState.followers i = .ordinary incoming μ ∧
            incoming.status = .unoccupied ∧
            localStateDomainValid incoming ∧ localBufferValid incoming ∧
            downDecoderStateValid incoming ∧
            incoming.S ≤ p.T * D p ∧ incoming.delta ≤ D p ∧
            incoming.backlog ≤ p.T * D p ∧ incoming.S + incoming.backlog ≤ w * D p ∧
            (∀ saved ∈ incoming.buffer,
              1 ≤ saved.calendarRound ∧ saved.calendarRound ≤ p.T) ∧
            (incoming.buffer.map (fun saved => (saved.calendarRound, saved.pilot))).Nodup ∧
            (∀ saved ∈ incoming.buffer, ∃ q : ℕ, q ≤ D p ∧
              saved.observation.val = (q : ℝ) / (D p : ℝ)) ∧
            incoming.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) ∧
            (∀ saved ∈ incoming.buffer, saved.calendarRound < s + b + j + 1) ∧
            incoming.downBatch.pending.length < AffineBatchDecoder.quota p ∧
            (∀ batch ∈ incoming.downBatch.completed,
              batch.length = AffineBatchDecoder.quota p) ∧
            ((incoming.lastDown = none ∧ incoming.S = 0 ∧ incoming.delta = 0 ∧
                incoming.backlog = 0) ∨
              incoming.lastDown = some (r.payload.downRecord i)) ∧
            ActiveFollowerLifecycle.startRound rate.eta record.input.time incoming μ =
              .ok (incoming, μ) ∧
            (record.output.preparation.followers.followers i).configuration =
              .ordinary incoming μ ∧
            (∀ _hselected : ActiveFollowerQueueOperation.selectedUpRound i record.input.row
                (record.input.state.activations i) record.input.time,
              ∃ offered : OrdinaryMessageCodec.UpRecord
                  (ReferencePrelaunchFollower.codecParams p rate.eta),
                ActiveFollowerQueueOperation.checkedUpOffer rate.eta i record.input.row
                  (record.input.state.activations i) record.input.time incoming =
                    .offer offered ∧
                offered.val = ActiveFollowerQueueOperation.upOfferFields incoming ∧
                OrdinaryMessageCodec.upAdmissible
                  (ReferencePrelaunchFollower.codecParams p rate.eta) offered.val ∧
                record.output.preparation.arms.actions
                  (PublicDiscreteDraws.followerPlayer p.two_le_m i) =
                  ActiveRoundActions.sendArm
                    (ActiveFollowerArmChoice.offeredUpBit rate.eta
                      (record.input.row.2 record.input.time) i offered)
                    ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K
                      (record.input.row.2 record.input.time).1).val
                        (PublicDiscreteDraws.followerPlayer p.two_le_m i))
                    ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K
                      (record.input.row.2 record.input.time).1).val
                        (ActiveRoundActions.coordinator p.two_le_m))) ∧
            (¬ ActiveFollowerQueueOperation.selectedUpRound i record.input.row
                (record.input.state.activations i) record.input.time →
              ActiveFollowerQueueOperation.checkedUpOffer rate.eta i record.input.row
                (record.input.state.activations i) record.input.time incoming = .noOffer) ∧
            (PublicDiscreteDraws.slotDraw (record.input.row.2 record.input.time).1 =
                PublicDiscreteDraws.dataSlot →
              record.output.preparation.arms.actions
                (PublicDiscreteDraws.followerPlayer p.two_le_m i) =
                PublicDiscreteDraws.pilotDraw (K_pos p)
                  (PublicDiscreteDraws.followerPlayer p.two_le_m i)
                  (record.input.row.2 record.input.time).1) ∧
            (PublicDiscreteDraws.slotDraw (record.input.row.2 record.input.time).1 ≠
                PublicDiscreteDraws.dataSlot →
              ¬ (PublicDiscreteDraws.slotDraw (record.input.row.2 record.input.time).1 =
                  PublicDiscreteDraws.upSlot ∧
                PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
                  (record.input.row.2 record.input.time).1 = i) →
              record.output.preparation.arms.actions
                (PublicDiscreteDraws.followerPlayer p.two_le_m i) =
                (OrderedTupleSampler.sample p.two_le_m p.m_lt_K
                  (record.input.row.2 record.input.time).1).val
                  (PublicDiscreteDraws.followerPlayer p.two_le_m i)) ∧
            (∃ logged diagnostic post,
              ActiveFollowerLogging.checkedLogging i record.input.row
                (record.input.state.activations i) record.input.time
                ((record.output.preparation.followers.followers i).arm,
                  record.output.preparation.feedback.observations
                    (PublicDiscreteDraws.followerPlayer p.two_le_m i)) incoming =
                  .ok logged ∧
              logged.buffer = incoming.buffer ++ ReferencePrelaunchFollower.logAt i
                record.input.row (record.input.state.activations i) record.input.time
                ((record.output.preparation.followers.followers i).arm,
                  record.output.preparation.feedback.observations
                    (PublicDiscreteDraws.followerPlayer p.two_le_m i)) ∧
              diagnostic = ReferenceDownReception.referenceDownCut p
                record.output.preparation.coordinator.downView i record.input.row
                record.input.time
                (record.output.preparation.feedback.observations
                  (PublicDiscreteDraws.followerPlayer p.two_le_m i)) rate logged ∧
              (ReferenceActivePhysicalStep.recordFollower
                record.output.preparation.coordinator.downView i record.input.row
                (record.input.state.activations i) record.input.time (record.input.active i)
                (record.output.preparation.followers.followers i).arm
                (record.output.preparation.feedback.observations
                  (PublicDiscreteDraws.followerPlayer p.two_le_m i)) incoming).result =
                  .ok post ∧
              (ReferenceActivePhysicalStep.recordFollower
                record.output.preparation.coordinator.downView i record.input.row
                (record.input.state.activations i) record.input.time (record.input.active i)
                (record.output.preparation.followers.followers i).arm
                (record.output.preparation.feedback.observations
                  (PublicDiscreteDraws.followerPlayer p.two_le_m i)) incoming).downInput =
                  some logged ∧
              (ReferenceActivePhysicalStep.recordFollower
                record.output.preparation.coordinator.downView i record.input.row
                (record.input.state.activations i) record.input.time (record.input.active i)
                (record.output.preparation.followers.followers i).arm
                (record.output.preparation.feedback.observations
                  (PublicDiscreteDraws.followerPlayer p.two_le_m i)) incoming).down =
                  some diagnostic ∧
              DeclaredFollowerLocalRound.releaseAndFinish rate i record.input.row
                record.input.time
                (record.output.preparation.feedback.observations
                  (PublicDiscreteDraws.followerPlayer p.two_le_m i)) incoming μ post =
                  .ok (post, μ) ∧
              (record.output.followers i).configuration = .ordinary post μ ∧
              (record.output.followers i).failure = none ∧
              (record.output.followers i).downInput = some logged ∧
              (record.output.followers i).down = some diagnostic ∧
              post.status = .unoccupied ∧ post.S ≤ p.T * D p ∧ post.delta ≤ D p ∧
              post.backlog ≤ p.T * D p ∧ post.S + post.backlog ≤ w * D p ∧
              (∀ saved ∈ post.buffer,
                1 ≤ saved.calendarRound ∧ saved.calendarRound ≤ p.T) ∧
              (post.buffer.map (fun saved => (saved.calendarRound, saved.pilot))).Nodup ∧
              (∀ saved ∈ post.buffer, ∃ q : ℕ, q ≤ D p ∧
                saved.observation.val = (q : ℝ) / (D p : ℝ)) ∧
              post.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) ∧
              (∀ saved ∈ post.buffer, saved.calendarRound < s + b + j + 2) ∧
              post.downBatch.pending.length < AffineBatchDecoder.quota p ∧
              (∀ batch ∈ post.downBatch.completed,
                batch.length = AffineBatchDecoder.quota p) ∧
              ((post.lastDown = none ∧ post.S = 0 ∧ post.delta = 0 ∧ post.backlog = 0) ∨
                post.lastDown = some (r.payload.downRecord i)) ∧
              post.initializationFailure = incoming.initializationFailure) ∧
            record.output.next = next.finalState) := by
  classical
  let initial := ReferenceFirstLaunchNumericalCell.launchState rate z rewards C_star C_h hc
  let execution := ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun
    rate z rewards C_star C_h hc s hsElapsed count hspan
  let window := firstLiveWindow execution.records
  let w := window.length
  let b := w + 1
  let W := (execution.records.drop b).takeWhile
    (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input)
  let active := ReferenceGeneratedFirstCutoffSurvival.generatedLaunchActive
    rate z rewards C_star C_h hc s hsElapsed
  have htail : b + W.length ≤ count := by
    simpa [execution, window, w, b, W,
      ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun] using
      first_collection_window_length_bound initial z.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s count hspan active hshort
  let prefixAt := fun (j : ℕ) (hj : j ≤ W.length) =>
    ReferenceActivePhysicalHorizon.run initial z.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s (b + j)
      (by omega) active
  let successor := prefixAt 0 (by omega)
  let cut := execution.records[w]'(by
    have hw : w < count := by simpa [execution, window, w] using hshort
    have hlen := ReferenceActivePhysicalHorizon.run_record_count initial z.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s count hspan active
    have hrun : execution.records.length = count := by
      simpa [execution, ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun] using hlen
    rw [hrun]
    exact hw)

  have hsetup := first_collection_follower_cutoff_seed
    rate z rewards C_star C_h hc s hsElapsed count hspan hshort
  dsimp only [initial, execution, window, w, b, active, successor, cut] at hsetup
  rcases hsetup with ⟨r, q, base, hlive, hsigma, hqzero,
    dispatched, hstart, ledger, hinit, hledger, hdomain, hclock, hpending,
    hnoAssignment, selected, hcutBranch, hu, huBound, huGrid, hledgerSigma,
    hledgerCut, hfirstCutoff, hsuccessor, movingLedger, movingSaved,
    hsuccessorCoordinator, hseedFollowers⟩

  have hcore := ReferenceGeneratedFirstCutoffSurvival.run_generated_first_cutoff_survival
    rate z rewards C_star C_h hc s hsElapsed count hspan hshort
  have hfirst : initial.coordinator = .first := by
    simpa only [initial] using hcore.2.1

  have hprepAll :=
    ReferenceFirstCollectionFollowerPreparation.run_first_collection_follower_preparation_step
      initial z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards
      s count hspan active hfirst hshort
  dsimp only [execution, window, w, b, W] at hprepAll
  rcases hprepAll with ⟨cutP, suffixP, hsplitP, hindexP, htimeP,
    rP, qP, baseP, hcutStateP, hprefixLiveP, dispatchedP, hstartP,
    ledgerP, hinitP, hledgerP, hdomainP,
    hclockP, hpendingP, hnoAssignmentP, selectedP, hcutBranchP, hsigmaP,
    hfirstCutoffP, huBoundP, hqzeroP, hprepSteps⟩
  have hcutP : cutP = cut := by
    exact hindexP.trans rfl
  subst cutP
  have hcutRootEq :
      DispatchCut.live r q base
        (.cutoffChosen dispatched hstart ledger hinit hledger hdomain hclock hpending
          hnoAssignment selected) =
      DispatchCut.live rP qP baseP
        (.cutoffChosen dispatchedP hstartP ledgerP hinitP hledgerP hdomainP hclockP
          hpendingP hnoAssignmentP selectedP) := hcutBranch.symm.trans hcutBranchP
  cases hcutRootEq

  have hobsAll :=
    ReferenceFirstCollectionFollowerObservation.run_first_collection_follower_observation_step
      initial z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards
      s count hspan active hfirst
  dsimp only [execution, window, w, b, W] at hobsAll
  obtain ⟨cutO, hindexO, rO, qO, baseO, dispatchedO, hstartO, ledgerO, hinitO,
    hledgerO, hdomainO, hclockO, hpendingO, hnoAssignmentO, selectedO,
    hcutBranchO, htimeO, hsigmaO, hcutoffO, hqzeroO, hobsFor⟩ := hobsAll hshort
  have hcutO : cutO = cut := by exact hindexO.trans rfl
  subst cutO
  have hobsRootEq :
      DispatchCut.live r q base
        (.cutoffChosen dispatched hstart ledger hinit hledger hdomain hclock hpending
          hnoAssignment selected) =
      DispatchCut.live rO qO baseO
        (.cutoffChosen dispatchedO hstartO ledgerO hinitO hledgerO hdomainO hclockO
          hpendingO hnoAssignmentO selectedO) := hcutBranch.symm.trans hcutBranchO
  cases hobsRootEq

  have hboundary : ∀ (j : ℕ) (hj : j ≤ W.length),
      let boundaryRun := prefixAt j hj
      (boundaryRun.finalState.coordinator = .dagger ∨
        ∃ movingLedger movingSaved,
          boundaryRun.finalState.coordinator = .collection r.payload movingLedger movingSaved) ∧
      (∀ i : Fin (p.m - 1),
        ∃ post μ,
          boundaryRun.finalState.followers i = .ordinary post μ ∧
          post.status = .unoccupied ∧
          localStateDomainValid post ∧ localBufferValid post ∧ downDecoderStateValid post ∧
          post.S ≤ p.T * D p ∧ post.delta ≤ D p ∧ post.backlog ≤ p.T * D p ∧
          post.S + post.backlog ≤ w * D p ∧
          (∀ saved ∈ post.buffer, 1 ≤ saved.calendarRound ∧ saved.calendarRound ≤ p.T) ∧
          (post.buffer.map (fun saved => (saved.calendarRound, saved.pilot))).Nodup ∧
          (∀ saved ∈ post.buffer, ∃ q : ℕ, q ≤ D p ∧
            saved.observation.val = (q : ℝ) / (D p : ℝ)) ∧
          post.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) ∧
          (∀ saved ∈ post.buffer, saved.calendarRound < s + b + j + 1) ∧
          post.downBatch.pending.length < AffineBatchDecoder.quota p ∧
          (∀ batch ∈ post.downBatch.completed,
            batch.length = AffineBatchDecoder.quota p) ∧
          ((post.lastDown = none ∧ post.S = 0 ∧ post.delta = 0 ∧ post.backlog = 0) ∨
            post.lastDown = some (r.payload.downRecord i))) := by
    intro j hj
    induction j with
    | zero =>
        constructor
        · dsimp only [prefixAt, b]
          exact Or.inr ⟨movingLedger, movingSaved, hsuccessorCoordinator⟩
        · intro i
          obtain ⟨post, μ, hstate, hstatus, hdom, hbuffer, hdecoder,
            hmass, hpair, hstamps, halt⟩ := hseedFollowers i
          have hdomOrig := hdom
          rcases hdom with ⟨⟨hS, hdelta, hbacklog⟩, hdomBuffer, hdomDecoder⟩
          rcases hdomBuffer with ⟨hcalendar, hkeys, hquant⟩
          rcases hdomDecoder with ⟨hpendingLocal, hcompleted⟩
          refine ⟨post, μ, ?_, hstatus, hdomOrig, hbuffer, hdecoder,
            hS, hdelta, hbacklog, hmass, hcalendar, hkeys, hquant,
            hpair, ?_, hpendingLocal, hcompleted, halt⟩
          · change successor.finalState.followers i = .ordinary post μ
            exact hstate
          · intro saved hsaved
            have hs := hstamps saved hsaved
            omega
    | succ j ih =>
        have hjlt : j < W.length := by omega
        have hjle : j ≤ W.length := by omega
        have hprev := ih hjle
        rcases hprev with ⟨hcoordPrev, hfollowersPrev⟩
        have hrecordBound : b + j < execution.records.length := by
          have hcount := ReferenceActivePhysicalHorizon.run_record_count initial z.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s count hspan active
          rw [show execution.records.length = count by
            simpa [execution, ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun] using hcount]
          omega
        let current := prefixAt j hjle
        let next := prefixAt (j + 1) hj
        let record := execution.records[b + j]'hrecordBound
        have hrecordIndex : record =
            ReferenceAssignmentPayloadChronology.actualRunRecordAt initial z.1.2
              (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s (b + j)
              (by omega) active := by
          have hindex : b + j < count := by omega
          have hget := run_records_getElem?_actualRunRecordAt initial z.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s count hspan active
            (b + j) hindex
          change execution.records[b + j]? =
            some (ReferenceAssignmentPayloadChronology.actualRunRecordAt initial z.1.2
              (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s (b + j)
              (by omega) active) at hget
          have hthis : execution.records[b + j]? = some record := by
            simp [record]
          rw [hthis] at hget
          exact Option.some.inj hget
        have hnextState : next.finalState = record.output.next := by
          dsimp only [next, prefixAt]
          rw [hrecordIndex]
          exact ReferenceAssignmentPayloadChronology.run_successor_finalState_eq_actualRunRecordAt
            initial z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s
            (b + j) (by omega) active
        have hPstepFor := hprepSteps j (Nat.le_of_lt hjlt) hrecordBound
        have hcoordAt : current.finalState.coordinator = .dagger ∨
            ∃ movingLedger movingSaved,
              current.finalState.coordinator = .collection r.payload movingLedger movingSaved := by
          simpa only [current] using hcoordPrev
        have hOFor := hobsFor j hjlt hrecordBound
        let i0 : Fin (p.m - 1) := ⟨0, by have := p.two_le_m; omega⟩
        obtain ⟨state0, μ0, hstate0, hstatus0, hdom0, hbuffer0, hdecoder0,
          hS0, hdelta0, hbacklog0, hmass0,
          hcalendar0, hkeys0, hquant0, hpair0, hbefore0, hpending0, hcompleted0, hlast0⟩ :=
            hfollowersPrev i0
        have hstate0Current : current.finalState.followers i0 = .ordinary state0 μ0 := by
          simpa [current, prefixAt] using hstate0
        have hOzero := hOFor i0 state0 μ0 hstate0Current
          hstatus0 hS0 hdelta0 hbacklog0 hmass0 hcalendar0 hkeys0 hquant0 hpair0
          hbefore0 hpending0 hcompleted0 hlast0 hcoordAt
        have hnextCoord : next.finalState.coordinator = .dagger ∨
            ∃ movingLedger movingSaved,
              next.finalState.coordinator = .collection r.payload movingLedger movingSaved := by
          exact hOzero.1
        refine ⟨hnextCoord, ?_⟩
        intro i
        obtain ⟨state, μ, hstate, hstatus, hdom, hbuffer, hdecoder,
          hS, hdelta, hbacklog, hmass, hcalendar, hkeys, hquant, hpair, hbefore,
          hpendingLocal, hcompleted, hlast⟩ :=
            hfollowersPrev i
        have hstateCurrent : current.finalState.followers i = .ordinary state μ := by
          simpa [current, prefixAt] using hstate
        have hPstep := hPstepFor i state μ
          hstateCurrent
          hstatus hS hdelta hbacklog hmass hcalendar hkeys hquant hpair hbefore
          hpendingLocal hcompleted hlast
        have hprepared := hPstep.2.1
        have hOstep := hOFor i state μ hstateCurrent
          hstatus hS hdelta hbacklog hmass hcalendar hkeys hquant hpair hbefore
          hpendingLocal hcompleted hlast hcoordAt
        have hOstep' := hOstep
        rw [hprepared] at hOstep'
        simp only at hOstep'
        rcases hOstep'.2 with ⟨_hchoice, _hmemory, hordinaryBody⟩
        rcases hordinaryBody with ⟨logged, diagnostic, post, hlogging, hlogBuffer,
          hdiagnostic, hrecordResult, hdownInput, hdown, hrelease,
          hconfiguration, _hfailure, hdiagInput, hdiagDown, hstatusPost,
          hSPost, hdeltaPost, hbacklogPost, hmassPost, hcalendarPost,
          hkeysPost, hquantPost, hpairPost, hbeforePost, hpendingPost,
          hcompletedPost, hlastPost, _hfailureFrame⟩
        have hnextFollower : record.output.next.followers i = .ordinary post μ := by
          have hconfigurationLocal := hconfiguration
          change (record.output.followers i).configuration = .ordinary post μ
            at hconfigurationLocal
          have hconfig' :
              ((ReferenceActivePhysicalStep.prepare record.input).observeFollower i).configuration =
                .ordinary post μ := by
            have hconfigurationStep :
                ((ReferenceActivePhysicalStep.step record.input).followers i).configuration =
                  .ordinary post μ := by
              rw [← record.output_eq]
              exact hconfigurationLocal
            simpa [ReferenceActivePhysicalStep.step] using hconfigurationStep
          rw [record.output_eq]
          rw [(ReferenceActivePhysicalStep.step_next_fields record.input).2.2.2 i]
          exact hconfig'
        have hnextFollower' : next.finalState.followers i = .ordinary post μ := by
          rw [hnextState]
          exact hnextFollower
        have hdomainPost : localStateDomainValid post := by
          exact ⟨⟨hSPost, hdeltaPost, hbacklogPost⟩,
            ⟨hcalendarPost, hkeysPost, hquantPost⟩,
            ⟨hpendingPost, hcompletedPost⟩⟩
        have hbufferPost : localBufferValid post :=
          ⟨hcalendarPost, hkeysPost, hquantPost⟩
        have hdecoderPost : downDecoderStateValid post :=
          ⟨hpendingPost, hcompletedPost⟩
        refine ⟨post, μ, hnextFollower', hstatusPost, hdomainPost, hbufferPost,
          hdecoderPost, hSPost, hdeltaPost, hbacklogPost, hmassPost,
          hcalendarPost, hkeysPost, hquantPost, hpairPost, ?_,
          hpendingPost, hcompletedPost, hlastPost⟩
        · intro saved hsaved
          exact hbeforePost saved hsaved

  refine ⟨r, q, base, hlive, hsigma, hqzero,
    dispatched, hstart, ledger, hinit, hledger, hdomain, hclock, hpending,
    hnoAssignment, selected, hcutBranch, hu, huBound, huGrid, hledgerSigma,
    hledgerCut, hfirstCutoff, hsuccessor, ⟨movingLedger, movingSaved, hsuccessorCoordinator⟩,
    hboundary, ?_⟩
  intro j hj
  let hjle : j ≤ W.length := Nat.le_of_lt hj
  intro current next record i
  have hrecordBound : b + j < execution.records.length := by
    have hcount := ReferenceActivePhysicalHorizon.run_record_count initial z.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s count hspan active
    have hcount' : execution.records.length = count := by
      simpa [execution, ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun] using hcount
    have hindex : b + j < count := by
      have hjdrop : b + j < b + W.length := Nat.add_lt_add_left hj b
      exact Nat.lt_of_lt_of_le hjdrop htail
    rw [hcount']
    exact hindex
  obtain ⟨hcoord, hfollowers⟩ := hboundary j hjle
  have hcoordAt : current.finalState.coordinator = .dagger ∨
      ∃ movingLedger movingSaved,
        current.finalState.coordinator = .collection r.payload movingLedger movingSaved := by
    simpa [current, prefixAt] using hcoord
  obtain ⟨incoming, μ, hstate, hstatus, hdom, hbuffer, hdecoder,
    hS, hdelta, hbacklog, hmass, hcalendar, hkeys, hquant, hpair, hbefore,
    hpendingLocal, hcompleted, hlast⟩ := hfollowers i
  have hstateCurrent : current.finalState.followers i = .ordinary incoming μ := by
    simpa [current, prefixAt] using hstate
  have hPstep := hprepSteps j hjle hrecordBound i incoming μ hstateCurrent
    hstatus hS hdelta hbacklog hmass hcalendar hkeys hquant hpair hbefore
    hpendingLocal hcompleted hlast
  rcases hPstep with ⟨hstartRound, hprepare, hselectedOffer, hnoOffer,
    hdataArm, hotherArm⟩
  have hOstep := hobsFor j hj hrecordBound i incoming μ hstateCurrent
    hstatus hS hdelta hbacklog hmass hcalendar hkeys hquant hpair hbefore
    hpendingLocal hcompleted hlast hcoordAt
  have hOstep' := hOstep
  rw [hprepare] at hOstep'
  simp only at hOstep'
  rcases hOstep'.2 with ⟨_hchoice, _hmemory, hordinaryBody⟩
  rcases hordinaryBody with ⟨logged, diagnostic, post, hlogging, hlogBuffer,
    hdiagnostic, hrecordResult, hdownInput, hdown, hrelease,
    hconfiguration, _hfailure, hdiagInput, hdiagDown, hstatusPost,
    hSPost, hdeltaPost, hbacklogPost, hmassPost, hcalendarPost,
    hkeysPost, hquantPost, hpairPost, hbeforePost, hpendingPost,
    hcompletedPost, hlastPost, hfailureFrame⟩
  have hjnext : j + 1 ≤ W.length := Nat.succ_le_of_lt hj
  have hindexNext : b + (j + 1) ≤ count :=
    Nat.le_trans (Nat.add_le_add_left hjnext b) htail
  have hsuccessorSpan : s + (b + j + 1) ≤ p.T := by
    have hindexNext' : b + j + 1 ≤ count := by omega
    calc
      s + (b + j + 1) ≤ s + count := Nat.add_le_add_left hindexNext' s
      _ ≤ p.T := hspan
  have hrecordIndex : record =
      ReferenceAssignmentPayloadChronology.actualRunRecordAt initial z.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s (b + j)
        hsuccessorSpan active := by
    have hindex : b + j < count := by
      have hcount := ReferenceActivePhysicalHorizon.run_record_count initial z.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s count hspan active
      rw [show execution.records.length = count by
        simpa [execution, ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun] using hcount]
        at hrecordBound
      exact hrecordBound
    have hget := run_records_getElem?_actualRunRecordAt initial z.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s count hspan active
      (b + j) hindex
    change execution.records[b + j]? =
      some (ReferenceAssignmentPayloadChronology.actualRunRecordAt initial z.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s (b + j)
        (by omega) active) at hget
    have hthis : execution.records[b + j]? = some record := by
      change execution.records[b + j]? =
        some (execution.records[b + j]'hrecordBound)
      exact List.getElem?_eq_getElem hrecordBound
    rw [hthis] at hget
    exact Option.some.inj hget
  have hnextState : next.finalState = record.output.next := by
    dsimp only [next, prefixAt]
    rw [hrecordIndex]
    exact ReferenceAssignmentPayloadChronology.run_successor_finalState_eq_actualRunRecordAt
      initial z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s
      (b + j) hsuccessorSpan active
  refine ⟨incoming, μ, hstate, hstatus, hdom, hbuffer, hdecoder,
    hS, hdelta, hbacklog, hmass, hcalendar, hkeys, hquant, hpair, hbefore,
    hpendingLocal, hcompleted, hlast, hstartRound, hprepare,
    hselectedOffer, hnoOffer, hdataArm, hotherArm,
    ⟨logged, diagnostic, post, hlogging, hlogBuffer, hdiagnostic,
      hrecordResult, hdownInput, hdown, hrelease, hconfiguration,
      _hfailure, hdiagInput, hdiagDown, hstatusPost, hSPost, hdeltaPost,
      hbacklogPost, hmassPost, hcalendarPost, hkeysPost, hquantPost,
      hpairPost, hbeforePost, hpendingPost, hcompletedPost, hlastPost,
      hfailureFrame⟩, ?_⟩
  exact hnextState.symm

end Bandits.Support.ReferenceGeneratedFirstCollectionFollowerPrefix

end
