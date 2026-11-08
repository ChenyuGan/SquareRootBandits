/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceActualCollectionHiddenRefreshPath
public import Bandits.Support.ReferenceCollectionOldEpisodeOperationPreservation

import Mathlib.Tactic

/-!
# Enabled original collection prefixes and their signed endpoint atom

For a literal actual collection-prefix cell, derive the trigger and every
window enabled bit from the original physical suffix. The signed endpoint atom
then uses the same retained original word and old payload anchor.

Sources: ZIP4 `06_interruptions.tex:381-426`,
`04_slow_fast_learner.tex:176-215,323-366`, and
`appendix_a_local_protocol.tex:28-79` under `sources/zip4/manuscript/`.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceCompletePhysicalHistory
open Bandits.Support.ReferenceActualCollectionHiddenRefreshPath
open Bandits.Support.ReferenceCollectionOldEpisodeOperationPreservation
open Bandits.Support.ReferenceCollectionPhaseHistory
open Bandits.Support.ReferenceFirstLaunchNumericalCell
open Bandits.Support.ReferenceFirstCollectionCurrentRetainedGate
open Bandits.Support.DeferredRefreshWindow
open Bandits.Support.RecordedSlowRefresh
open Bandits.Support.ReferenceFirstCollectionAuxiliarySeeds

namespace Bandits.Support.ReferenceActualCollectionEnabledPrefixEndpoint

variable {p : ConstructorDimensions.Parameters}

private theorem originalCell_eq_collectionWord
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (e b : ℕ)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : z ∈ collectionPrefixCell rate rewards C_star C_h e b)
    (k : Fin (completeSuffixRecords rate z rewards C_star C_h).length) :
    cell0 rate ((completeSuffixRecords rate z rewards C_star C_h)[k.val]'k.isLt) =
      some ((collectionWord rate rewards C_star C_h e b z hz)[k.val]'(by
        rw [collectionWord, actualOriginalWord_length]
        exact k.isLt)) := by
  have hlaunch := collectionPrefixCell_launch rate rewards C_star C_h e b z hz
  have hcells := ReferenceCompleteOriginalCalendarCellPresence.complete_original_calendar_cells
    rate rewards C_star C_h z
  rw [Classical.choose_spec hlaunch] at hcells
  obtain ⟨L, hlen, hmap, hprefix, _⟩ := hcells
  have hlength := completeSuffixRecords_length rate z rewards C_star C_h
  have hdate : physicalStart rate z rewards C_star C_h +
      (completeSuffixRecords rate z rewards C_star C_h).length = p.T := by
    have hs := physicalStart_le_T rate z rewards C_star C_h
    omega
  have hprefixEnd := hprefix (completeSuffixRecords rate z rewards C_star C_h).length le_rfl
  rw [hdate, ← hlen, List.take_length] at hprefixEnd
  have hspec := actualOriginalWord_spec rate rewards C_star C_h z
    (collectionPrefixCell_launch rate rewards C_star C_h e b z hz)
  have hword : L = collectionWord rate rewards C_star C_h e b z hz := by
    apply Option.some.inj
    calc
      some L = ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
          rate rewards C_star C_h p.T z := hprefixEnd.symm
      _ = some (collectionWord rate rewards C_star C_h e b z hz) := by
        simpa only [collectionWord] using hspec
  have hkL : k.val < L.length := by
    exact Nat.lt_of_lt_of_eq k.isLt hlen.symm
  have hmapAt := congrArg
    (fun xs : List (Option (RecordedQueueRun.RoundInput p.K)) => xs[k.val]?) hmap
  have hcell : cell0 rate ((completeSuffixRecords rate z rewards C_star C_h)[k.val]'k.isLt) =
      some (L[k.val]'hkL) := by
    rw [List.getElem?_map, List.getElem?_eq_getElem k.isLt, Option.map_some] at hmapAt
    rw [List.getElem?_map, List.getElem?_eq_getElem hkL, Option.map_some] at hmapAt
    exact Option.some.inj hmapAt
  have hkWord : k.val < (collectionWord rate rewards C_star C_h e b z hz).length :=
    Nat.lt_of_lt_of_eq hkL (congrArg List.length hword)
  have hwordAt := congrArg
    (fun xs : List (RecordedQueueRun.RoundInput p.K) => xs[k.val]?) hword
  have hindices : L[k.val]'hkL =
      (collectionWord rate rewards C_star C_h e b z hz)[k.val]'hkWord := by
    exact Option.some.inj (by
      simpa only [List.getElem?_eq_getElem hkL, List.getElem?_eq_getElem hkWord] using hwordAt)
  exact hcell.trans (congrArg some hindices)

private theorem suffixRecord_time
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (completeSuffixRecords rate z rewards C_star C_h).length) :
    ((completeSuffixRecords rate z rewards C_star C_h)[k.val]'k.isLt).input.time.val =
      physicalStart rate z rewards C_star C_h + k.val := by
  have htimes := completeSuffixRecords_time_values rate z rewards C_star C_h
  have hcal : k.val < (ReferenceActivePhysicalHorizon.calendar
      (physicalStart rate z rewards C_star C_h)
      (p.T - physicalStart rate z rewards C_star C_h)).length := by
    rw [← htimes, List.length_map]
    exact k.isLt
  have heq : ((completeSuffixRecords rate z rewards C_star C_h).map
      (fun r => r.input.time.val))[k.val]'(by rw [List.length_map]; exact k.isLt) =
      (ReferenceActivePhysicalHorizon.calendar
        (physicalStart rate z rewards C_star C_h)
        (p.T - physicalStart rate z rewards C_star C_h))[k.val]'hcal := by
    simp only [htimes]
  simpa only [List.getElem_map, ReferenceActivePhysicalHorizon.calendar,
    List.getElem_range', Nat.one_mul] using heq

private theorem emptyPending_forces_laterChoice
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (completeSuffixRecords rate z rewards C_star C_h).length)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (saved : Option (Fin p.T × Bool))
    (hstate : ((completeSuffixRecords rate z rewards C_star C_h)[k.val]'k.isLt).input.state.coordinator =
      .collection payload ledger saved)
    (hempty : ledger.pending = ∅)
    (hbefore : ((completeSuffixRecords rate z rewards C_star C_h)[k.val]'k.isLt).input.time.val + 1 <
      ledger.freezeAt) :
    laterChosen ((completeSuffixRecords rate z rewards C_star C_h)[k.val]'k.isLt).input = true := by
  have hdomains := ReferenceCompleteEmptyCollectionCorrectedChoiceDomains.complete_empty_corrected_choice_domains
    rate rewards C_star C_h z
  dsimp only at hdomains
  obtain ⟨u, hu, core, started, hstart, instruction, hassignment, htime, hkind,
    hsigma, huNone, consistent, output, hlocal, hsuccess, clockData, installation,
    selected, hprior, hresult, hpending, hinstall, hdispatch, _⟩ :=
    hdomains k payload ledger saved hstate hempty hbefore
  have hcutoffRange : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T := by omega
  have hcutoffVal : ledger.cutoff - 1 = u.val := by omega
  let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
  have hcutoff : cutoff = u := Fin.ext hcutoffVal
  let clock := ReferenceActivePhysicalStep.collectionClock payload ledger saved u
  let input := ReferenceActivePhysicalStep.collectionInput
    ((completeSuffixRecords rate z rewards C_star C_h)[k.val]'k.isLt).input
    payload ledger clock u
  have hprepare :
      (ReferenceActivePhysicalStep.prepare
        ((completeSuffixRecords rate z rewards C_star C_h)[k.val]'k.isLt).input).coordinator =
        .collection payload ledger clock u
          (.laterChosen core consistent started hstart instruction hassignment output hlocal
            clockData installation selected) := by
    simp only [ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch,
      hstate, dite_eq_left hcutoffRange, CoordinatorRoundDispatch.dispatch]
    change DispatchCut.collection payload ledger
      (ReferenceActivePhysicalStep.collectionClock payload ledger saved cutoff) cutoff
      (CoordinatorRoundDispatch.dispatchCollection
        (ReferenceActivePhysicalStep.collectionInput
          ((completeSuffixRecords rate z rewards C_star C_h)[k.val]'k.isLt).input
          payload ledger
          (ReferenceActivePhysicalStep.collectionClock payload ledger saved cutoff) cutoff)) = _
    rw [hcutoff]
    change DispatchCut.collection payload ledger clock u
        (CoordinatorRoundDispatch.dispatchCollection input) =
      DispatchCut.collection payload ledger clock u
        (.laterChosen core consistent started hstart instruction hassignment output hlocal
          clockData installation selected)
    rw [hdispatch]
  simp only [ReferenceCollectionPhaseHistory.laterChosen, hprepare]

private theorem continuingCollectionStep
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (completeSuffixRecords rate z rewards C_star C_h).length)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (saved : Option (Fin p.T × Bool))
    (hstate : ((completeSuffixRecords rate z rewards C_star C_h)[k.val]'k.isLt).input.state.coordinator =
      .collection payload ledger saved)
    (hbefore : ((completeSuffixRecords rate z rewards C_star C_h)[k.val]'k.isLt).input.time.val + 1 <
      ledger.freezeAt)
    (hnoInstall : laterChosen
      ((completeSuffixRecords rate z rewards C_star C_h)[k.val]'k.isLt).input = false) :
    ∃ cell : RecordedQueueRun.RoundInput p.K,
      cell0 rate ((completeSuffixRecords rate z rewards C_star C_h)[k.val]'k.isLt) = some cell ∧
      cell.enabled = true ∧
      ∃ (finished : ReferenceActivePhysicalStep.Ledger rate)
        (clockFinished : CoordinatorPhaseClock.FinishRoundResult p),
        ((completeSuffixRecords rate z rewards C_star C_h)[k.val]'k.isLt).output.next.coordinator =
          .collection payload finished clockFinished.clock.lastProposal ∧
        finished.sigma = ledger.sigma ∧ finished.cutoff = ledger.cutoff ∧
        finished.freezeAt = ledger.freezeAt := by
  have hnonempty : ledger.pending.Nonempty := by
    by_contra hempty
    have hempty' : ledger.pending = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
    have hlater := emptyPending_forces_laterChoice rate rewards C_star C_h z k
      payload ledger saved hstate hempty' hbefore
    rw [hlater] at hnoInstall
    cases hnoInstall
  have hdomains := ReferenceCompleteContinuingCollectionChoiceDomains.complete_nonempty_continuing_collection_choice_domains
    rate rewards C_star C_h z
  dsimp only at hdomains
  obtain ⟨u, hu, core, scores, started, hstart, hframe, choiceInputs,
    snapshot, boundaryValid, hdispatch, _⟩ := hdomains k payload ledger saved hstate hnonempty
  have hcutoffRange : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T := by omega
  have hcutoffVal : ledger.cutoff - 1 = u.val := by omega
  let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
  have hcutoff : cutoff = u := Fin.ext hcutoffVal
  let clock := ReferenceActivePhysicalStep.collectionClock payload ledger saved u
  let input := ReferenceActivePhysicalStep.collectionInput
    ((completeSuffixRecords rate z rewards C_star C_h)[k.val]'k.isLt).input
    payload ledger clock u
  have hprepare :
      (ReferenceActivePhysicalStep.prepare
        ((completeSuffixRecords rate z rewards C_star C_h)[k.val]'k.isLt).input).coordinator =
        .collection payload ledger clock u (.continuing core snapshot boundaryValid scores) := by
    simp only [ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch,
      hstate, dite_eq_left hcutoffRange, CoordinatorRoundDispatch.dispatch]
    change DispatchCut.collection payload ledger
      (ReferenceActivePhysicalStep.collectionClock payload ledger saved cutoff) cutoff
      (CoordinatorRoundDispatch.dispatchCollection
        (ReferenceActivePhysicalStep.collectionInput
          ((completeSuffixRecords rate z rewards C_star C_h)[k.val]'k.isLt).input
          payload ledger
          (ReferenceActivePhysicalStep.collectionClock payload ledger saved cutoff) cutoff)) = _
    rw [hcutoff]
    change DispatchCut.collection payload ledger clock u
        (CoordinatorRoundDispatch.dispatchCollection input) =
      DispatchCut.collection payload ledger clock u
        (.continuing core snapshot boundaryValid scores)
    rw [hdispatch]
  let record := (completeSuffixRecords rate z rewards C_star C_h)[k.val]'k.isLt
  have hcontinuing :
      ((completeSuffixRecords rate z rewards C_star C_h)[k.val]'k.isLt).output.preparation.coordinator =
        .collection payload ledger clock u (.continuing core snapshot boundaryValid scores) := by
    have hstepCoord := congrArg
      (fun out => out.preparation.coordinator)
      record.output_eq
    simpa only [record] using hstepCoord.trans hprepare
  have hframes := complete_suffix_continuing_collection_operation_frames
    (rate := rate) rewards C_star C_h z k payload ledger clock u core snapshot boundaryValid scores hcontinuing
  obtain ⟨cell, hcell, hrate, henabled, hstartedCall, hclockAt⟩ := hframes
  obtain ⟨startedFromCall, hcall, hoperations⟩ := hstartedCall
  obtain ⟨recording, startedLedger, decoded, finished, bank, clockFinished,
    hrecording, hstart, hreceive, hfinish, hclock, hstartedSigma,
    hstartedCutoff, hstartedFreeze, hdecodedSigma, hdecodedCutoff,
    hdecodedFreeze, hfinishedSigma, hfinishedCutoff, hfinishedFreeze,
    hpost⟩ := hoperations
  have hstrict : ((completeSuffixRecords rate z rewards C_star C_h)[k.val]'k.isLt).input.time.val +
      1 < ledger.freezeAt := hbefore
  have henabled' : cell.enabled = true := by
    rw [henabled]
    exact decide_eq_true hstrict
  have hfollowers : ReferenceLaterCollectionArrivalReadout.preparedFollowersUnoccupied
      ((completeSuffixRecords rate z rewards C_star C_h)[k.val]'k.isLt) := by
    by_contra hnot
    simp [ReferenceLaterCollectionArrivalReadout.laterCollectionCall, hnot] at hcall
  have hcallExpected :
      ReferenceLaterCollectionArrivalReadout.laterCollectionCall 0
        ((completeSuffixRecords rate z rewards C_star C_h)[k.val]'k.isLt) =
        some ⟨payload, ledger, snapshot.clockStarted,
          CoordinatorCollectionInteractive.PreObservationInputs.weights
            (ReferenceActivePhysicalStep.collectionInput
              ((completeSuffixRecords rate z rewards C_star C_h)[k.val]'k.isLt).input
              payload ledger clock u)
            snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq⟩ := by
    simp [ReferenceLaterCollectionArrivalReadout.laterCollectionCall, hfollowers, hcontinuing]
  have hargs := Option.some.inj (hcallExpected.symm.trans hcall)
  rcases hargs with ⟨rfl, rfl, rfl⟩
  have hselected :
      (ReferenceActivePhysicalStep.DispatchCut.collection payload ledger clock u
        (.continuing core snapshot boundaryValid scores)).selection ≠ none := by
    simp [ReferenceActivePhysicalStep.DispatchCut.selection]
  have hobserve := ReferenceActivePhysicalStep.observeCoordinator_collection_equation
    record.output.preparation
    payload ledger clock u (.continuing core snapshot boundaryValid scores) hcontinuing
  rw [ite_eq_right hselected] at hobserve
  have hdiagnostics :
      record.output.coordinator =
        ReferenceActivePhysicalStep.collectionPostChoice
          record.output.preparation
          payload ledger snapshot.clockStarted
          (CoordinatorCollectionInteractive.PreObservationInputs.weights
            (ReferenceActivePhysicalStep.collectionInput
              ((completeSuffixRecords rate z rewards C_star C_h)[k.val]'k.isLt).input
              payload ledger clock u)
            snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq) := by
    calc
      _ = record.output.preparation.observeCoordinator := by
        rw [record.output_eq]
        rfl
      _ = _ := hobserve
  have hnextStep : record.output.next.coordinator = record.output.coordinator.configuration := by
    rw [record.output_eq]
    exact (ReferenceActivePhysicalStep.step_next_fields record.input).1
  have hnext :
      record.output.next.coordinator =
        .collection payload finished clockFinished.clock.lastProposal := by
    rw [hnextStep, hdiagnostics, hpost]
  exact ⟨cell, hcell, henabled', finished, clockFinished,
    hnext, hfinishedSigma, hfinishedCutoff, hfinishedFreeze⟩

private theorem actualWindowState
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (e b : ℕ)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : z ∈ collectionPrefixCell rate rewards C_star C_h e b)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ)
    (hlive : ((completeSuffixRecords rate z rewards C_star C_h)[e]'(collectionPrefixCell_live
      rate rewards C_star C_h e b z hz).1).input.state.coordinator = .live r q base)
    (he : e < (completeSuffixRecords rate z rewards C_star C_h).length)
    (hcutoff : ReferenceCollectionPhaseHistory.cutoffChosen
      ((completeSuffixRecords rate z rewards C_star C_h)[e]'he).input = true)
    (hboundary : physicalStart rate z rewards C_star C_h + b + 1 < r.gridBoundary)
    (hno : ∀ k : Fin (completeSuffixRecords rate z rewards C_star C_h).length,
      e < k.val → k.val < b →
        laterChosen ((completeSuffixRecords rate z rewards C_star C_h)[k.val]'k.isLt).input = false) :
    ∃ cutoffCell : RecordedQueueRun.RoundInput p.K,
      cell0 rate ((completeSuffixRecords rate z rewards C_star C_h)[e]'he) = some cutoffCell ∧
      cutoffCell.enabled = true ∧
    ∀ n : ℕ, (hn : e + 1 + n < b) →
      ∃ (payload : ReferenceActivePhysicalStep.Payload rate)
        (ledger : ReferenceActivePhysicalStep.Ledger rate)
        (saved : Option (Fin p.T × Bool)),
        ((completeSuffixRecords rate z rewards C_star C_h)[e + 1 + n]'(by
          have hlen := hz.2.1
          exact hn.trans_le hlen)).input.state.coordinator = .collection payload ledger saved ∧
        payload = r.payload ∧ ledger.sigma = (r.payload).sigma.val + 1 ∧
        ledger.cutoff = physicalStart rate z rewards C_star C_h + e + 1 ∧
        ledger.freezeAt = r.gridBoundary := by
  let records := completeSuffixRecords rate z rewards C_star C_h
  have hpos := collectionPrefixCell_trigger_positive rate rewards C_star C_h e b z hz
  have hbe : e ≤ b := hz.1
  have hlive' : (records[e]'he).input.state.coordinator = .live r q base := by
    simpa only [records] using hlive
  let outcome := CoordinatorRoundDispatch.dispatchLive
    (ReferenceActivePhysicalStep.liveInput (records[e]'he).input r q base)
  have hprepEq : (records[e]'he).output.preparation =
      ReferenceActivePhysicalStep.prepare (records[e]'he).input := by
    rw [(records[e]'he).output_eq]
    rfl
  have hcut : (records[e]'he).output.preparation.coordinator = .live r q base outcome := by
    rw [hprepEq]
    simp only [ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch,
      hlive', CoordinatorRoundDispatch.dispatch]
    rfl
  have hcutoff' := hcutoff
  unfold ReferenceCollectionPhaseHistory.cutoffChosen at hcutoff'
  rw [← hprepEq, hcut] at hcutoff'
  cases houtcome : outcome with
  | clockFailure failure _ =>
      simp [houtcome] at hcutoff'
  | initializerFailure dispatched hstart checked hchecked =>
      simp [houtcome] at hcutoff'
  | localFailure dispatched hstart reason =>
      simp [houtcome] at hcutoff'
  | continuingChosen dispatched hstart continuation selection =>
      simp [houtcome] at hcutoff'
  | cutoffChosen dispatched hstart newLedger initializationEq ledgerEq initDomain clockEq
      pendingEq noAssignment selection =>
      have hcut' : (records[e]'he).output.preparation.coordinator =
          .live r q base
            (.cutoffChosen dispatched hstart newLedger initializationEq ledgerEq initDomain
              clockEq pendingEq noAssignment selection) := by
        simpa only [houtcome] using hcut
      have hframes := complete_suffix_live_cutoff_operation_frames
        (rate := rate) rewards C_star C_h z ⟨e, he⟩ r q base
        (.cutoffChosen dispatched hstart newLedger initializationEq ledgerEq initDomain
          clockEq pendingEq noAssignment selection) hcut'
      obtain ⟨cutoffCell, hcutoffCell, hrate, henabled, hledgerCut, hclock, hpostFrames⟩ := hframes
      have hnewFields := CoordinatorStartRoundCutoffDispatch.collectionStartLedger_fields
        (ReferenceActivePhysicalStep.liveRegistersAt r (records[e]'he).input.time)
        (ReferenceActivePhysicalStep.liveOwnedAt r q (records[e]'he).input.time)
        base (records[e]'he).input.time
      have hledgerEq' : newLedger =
          CoordinatorStartRoundCutoffDispatch.collectionStartLedger
            (ReferenceActivePhysicalStep.liveRegistersAt r (records[e]'he).input.time)
            (ReferenceActivePhysicalStep.liveOwnedAt r q (records[e]'he).input.time)
            base (records[e]'he).input.time := by
        simpa only [ReferenceActivePhysicalStep.liveInput,
          ReferenceActivePhysicalStep.liveOwnedAt, ReferenceActivePhysicalStep.liveRegistersAt]
          using ledgerEq
      rw [← hledgerEq'] at hnewFields
      have hshared := ReferenceActivePhysicalStep.sharedLedger_fields newLedger
      have hfreeze := hshared.2.2.2.1.trans hnewFields.2.2.2.1
      have hliveBoundary := (ReferenceActivePhysicalStep.liveRegistersAt_fields r
        (records[e]'he).input.time).2.2.2.1
      have hfreezeR : (ReferenceActivePhysicalStep.sharedLedger newLedger).freezeAt = r.gridBoundary :=
        hfreeze.trans hliveBoundary
      have hcutoffCellEnabled : cutoffCell.enabled = true := by
        have hdate := suffixRecord_time rate rewards C_star C_h z ⟨e, he⟩
        have hstrict : (records[e]'he).input.time.val + 1 <
            (ReferenceActivePhysicalStep.sharedLedger newLedger).freezeAt := by
          rw [hdate, hfreezeR]
          have hdateLe : physicalStart rate z rewards C_star C_h + e + 1 ≤
              physicalStart rate z rewards C_star C_h + b + 1 := by omega
          exact lt_of_le_of_lt hdateLe hboundary
        rw [henabled]
        exact decide_eq_true hstrict
      rcases hpostFrames with ⟨recording, startedLedger, decoded, finished, bank,
        clockFinished, hrecording, hstartLedger, hreceive, hfinish, hclockFinish,
        hstartedSigma, hstartedCutoff, hstartedFreeze, hdecodedSigma, hdecodedCutoff,
        hdecodedFreeze, hfinishedSigma, hfinishedCutoff, hfinishedFreeze, hpost⟩
      have hselected :
          (ReferenceActivePhysicalStep.DispatchCut.live r q base
            (.cutoffChosen dispatched hstart newLedger initializationEq ledgerEq initDomain
              clockEq pendingEq noAssignment selection)).selection ≠ none := by
        simp [ReferenceActivePhysicalStep.DispatchCut.selection,
          ReferenceActivePhysicalStep.selectionAt]
      have hobserve := ReferenceActivePhysicalStep.observeCoordinator_live_equation
        (records[e]'he).output.preparation r q base
        (.cutoffChosen dispatched hstart newLedger initializationEq ledgerEq initDomain
          clockEq pendingEq noAssignment selection) hcut'
      rw [ite_eq_right hselected] at hobserve
      have hdiagnostics : (records[e]'he).output.coordinator =
          ReferenceActivePhysicalStep.collectionPostChoice
            (records[e]'he).output.preparation r.payload
            (ReferenceActivePhysicalStep.sharedLedger newLedger) dispatched.startResult
            (ReferenceActivePhysicalStep.liveRegistersAt r (records[e]'he).input.time).complementWeights := by
        calc
          _ = (records[e]'he).output.preparation.observeCoordinator := by
            rw [(records[e]'he).output_eq]
            rfl
          _ = _ := hobserve
      have hnextStep : (records[e]'he).output.next.coordinator =
          (records[e]'he).output.coordinator.configuration := by
        rw [(records[e]'he).output_eq]
        exact (ReferenceActivePhysicalStep.step_next_fields (records[e]'he).input).1
      have hnext : (records[e]'he).output.next.coordinator =
          .collection r.payload finished clockFinished.clock.lastProposal := by
        rw [hnextStep, hdiagnostics, hpost]
      have hcutoffDate : (records[e]'he).input.time.val + 1 =
          physicalStart rate z rewards C_star C_h + e + 1 := by
        rw [suffixRecord_time rate rewards C_star C_h z ⟨e, he⟩]
      have hbaseFields : finished.sigma = r.payload.sigma.val + 1 ∧
          finished.cutoff = physicalStart rate z rewards C_star C_h + e + 1 ∧
          finished.freezeAt = r.gridBoundary := by
        refine ⟨?_, ?_, ?_⟩
        · rw [hfinishedSigma]
          exact hshared.2.1.trans hnewFields.2.1
        · rw [hfinishedCutoff, hledgerCut, hcutoffDate]
        · rw [hfinishedFreeze, hfreezeR]
      refine ⟨cutoffCell, hcutoffCell, hcutoffCellEnabled, ?_⟩
      intro n
      induction n with
      | zero =>
          intro hn
          have hnextBound : e + 1 < records.length := by
            have hnb : e + 1 < b := by simpa using hn
            exact hnb.trans_le hz.2.1
          have hnextState : (records[e+1]'hnextBound).input.state.coordinator =
              .collection r.payload finished clockFinished.clock.lastProposal := by
            have hadj := ReferenceCompleteLaterLiveComplementPrefixReplay.complete_adjacent
              rewards C_star C_h z e hnextBound
            have hadj' : (records[e+1]'hnextBound).input.state =
                (records[e]'he).output.next := by
              simpa only [records] using hadj
            have hcoord := congrArg (fun state : ReferenceActivePhysicalStep.State p rate =>
              state.coordinator) hadj'
            exact hcoord.trans hnext
          exact ⟨r.payload, finished, clockFinished.clock.lastProposal, hnextState,
            rfl, hbaseFields.1, hbaseFields.2.1, hbaseFields.2.2⟩
      | succ n ih =>
          intro hn
          have hn' : e + 1 + n < b := by omega
          have hnextBound : e + 1 + n < records.length := hn'.trans_le hz.2.1
          obtain ⟨payload, ledger, saved, hstate, hpayload, hsigma, hcutoffLedger,
            hfreezeLedger⟩ := ih hn'
          let k : Fin records.length := ⟨e + 1 + n, hnextBound⟩
          have hnot : laterChosen (records[k.val]'k.isLt).input = false :=
            hno k (by dsimp [k]; omega) (by dsimp [k]; omega)
          have hbefore : (records[k.val]'k.isLt).input.time.val + 1 < ledger.freezeAt := by
            rw [suffixRecord_time rate rewards C_star C_h z k, hfreezeLedger]
            have hdateLe : physicalStart rate z rewards C_star C_h + (e + 1 + n) + 1 ≤
                physicalStart rate z rewards C_star C_h + b + 1 := by omega
            exact lt_of_le_of_lt hdateLe hboundary
          obtain ⟨cell, hcell, henabled, nextLedger, clockFinished, hnext,
            hnextSigma, hnextCutoff, hnextFreeze⟩ :=
            continuingCollectionStep rate rewards C_star C_h z k payload ledger saved
              hstate hbefore hnot
          have hadj := ReferenceCompleteLaterLiveComplementPrefixReplay.complete_adjacent
            rewards C_star C_h z (e + 1 + n) (by
              have hn'' : e + 1 + (n + 1) < b := by simpa [Nat.add_assoc] using hn
              exact hn''.trans_le hz.2.1)
          have hnextNextBound : e + 1 + (n + 1) < records.length := by
            have hn'' : e + 1 + (n + 1) < b := by simpa [Nat.add_assoc] using hn
            exact hn''.trans_le hz.2.1
          have hadj' :
              (records[e + 1 + (n + 1)]'hnextNextBound).input.state =
                (records[e + 1 + n]'hnextBound).output.next := by
            simpa only [records, Nat.add_assoc, Nat.add_sub_cancel_left] using hadj
          have hstateNext : (records[e + 1 + (n + 1)]'hnextNextBound).input.state.coordinator =
              .collection payload nextLedger clockFinished.clock.lastProposal := by
            have hc := congrArg
              (fun state : ReferenceActivePhysicalStep.State p rate => state.coordinator) hadj'
            exact hc.trans hnext
          exact ⟨payload, nextLedger, clockFinished.clock.lastProposal, hstateNext,
            hpayload, hnextSigma.trans hsigma, hnextCutoff.trans hcutoffLedger,
            hnextFreeze.trans hfreezeLedger⟩

private theorem actualCollectionIntervalEnabled
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (e b : ℕ)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : z ∈ collectionPrefixCell rate rewards C_star C_h e b) :
    ((collectionWord rate rewards C_star C_h e b z hz)[e - 1]'(by
      have hpos := collectionPrefixCell_trigger_positive rate rewards C_star C_h e b z hz
      have hbe : e ≤ b := hz.1
      have hbound := collectionWord_bound rate rewards C_star C_h e b z hz
      omega)).enabled = true ∧
    ∀ n : ℕ, (hn : n < b - e) →
      ((collectionWord rate rewards C_star C_h e b z hz)[e + n]'(by
        have hbe : e ≤ b := hz.1
        have hbound := collectionWord_bound rate rewards C_star C_h e b z hz
        have hsum : e + n < b := by omega
        exact hsum.trans_le hbound)).enabled = true := by
  obtain ⟨he, r, q, base, hlive, hcutoff, hboundary, hpayload⟩ :=
    collectionPrefixCell_live rate rewards C_star C_h e b z hz
  have hpos := collectionPrefixCell_trigger_positive rate rewards C_star C_h e b z hz
  have hbe : e ≤ b := hz.1
  have hno : ∀ k : Fin (completeSuffixRecords rate z rewards C_star C_h).length,
      e < k.val → k.val < b →
        laterChosen ((completeSuffixRecords rate z rewards C_star C_h)[k.val]'k.isLt).input = false := by
    obtain ⟨_, _, _, hcell⟩ := hz
    rw [hlive] at hcell
    exact hcell.2.2.1
  let cutoffIndex : Fin (completeSuffixRecords rate z rewards C_star C_h).length := ⟨e, he⟩
  have hpred := complete_suffix_live_successor_predecessor_enabled
    (rate := rate) rewards C_star C_h z cutoffIndex hpos r q base
    (by simpa [cutoffIndex] using hlive)
  obtain ⟨triggerCell, htriggerCell, htriggerEnabled⟩ := hpred
  let predecessor : Fin (completeSuffixRecords rate z rewards C_star C_h).length :=
    ⟨e - 1, by omega⟩
  have htriggerWord := originalCell_eq_collectionWord rate rewards C_star C_h e b z hz predecessor
  have htriggerEq : triggerCell =
      (collectionWord rate rewards C_star C_h e b z hz)[e - 1]'(by
        have hpos := collectionPrefixCell_trigger_positive rate rewards C_star C_h e b z hz
        have hbe : e ≤ b := hz.1
        have hbound := collectionWord_bound rate rewards C_star C_h e b z hz
        omega) := by
    exact Option.some.inj (htriggerCell.symm.trans (by simpa [predecessor] using htriggerWord))
  have htrigger :
      ((collectionWord rate rewards C_star C_h e b z hz)[e - 1]'(by
        have hpos := collectionPrefixCell_trigger_positive rate rewards C_star C_h e b z hz
        have hbe : e ≤ b := hz.1
        have hbound := collectionWord_bound rate rewards C_star C_h e b z hz
        omega)).enabled = true := by
    simpa only [← htriggerEq] using htriggerEnabled
  obtain ⟨cutoffCell, hcutoffCell, hcutoffCellEnabled, hwindowState⟩ :=
    actualWindowState rate rewards C_star C_h e b z hz r q base
      hlive he hcutoff hboundary hno
  constructor
  · exact htrigger
  · intro n hn
    by_cases hn0 : n = 0
    · subst n
      let k : Fin (completeSuffixRecords rate z rewards C_star C_h).length := ⟨e, by omega⟩
      have hcellWord := originalCell_eq_collectionWord rate rewards C_star C_h e b z hz k
      have hcellEq : cutoffCell =
          (collectionWord rate rewards C_star C_h e b z hz)[e]'(by
            have hbe : e ≤ b := hz.1
            have hbound := collectionWord_bound rate rewards C_star C_h e b z hz
            omega) := by
        exact Option.some.inj (hcutoffCell.symm.trans (by simpa [k] using hcellWord))
      simpa only [Nat.add_zero, ← hcellEq] using hcutoffCellEnabled
    · have hnpos : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
      have hkBound : e + 1 + (n - 1) < b := by omega
      have hdateLT : e + n < b := by omega
      obtain ⟨payload, ledger, saved, hstate, hpayload', hsigma, hcutoffLedger, hfreeze⟩ :=
        hwindowState (n - 1) hkBound
      let k : Fin (completeSuffixRecords rate z rewards C_star C_h).length :=
        ⟨e + n, hdateLT.trans_le hz.2.1⟩
      have hindex : e + 1 + (n - 1) = e + n := by omega
      have hnoK : laterChosen
          ((completeSuffixRecords rate z rewards C_star C_h)[k.val]'k.isLt).input = false :=
        hno k (by dsimp [k]; omega) (by dsimp [k]; omega)
      have hbefore :
          ((completeSuffixRecords rate z rewards C_star C_h)[k.val]'k.isLt).input.time.val + 1 <
            ledger.freezeAt := by
        rw [suffixRecord_time rate rewards C_star C_h z k, hfreeze]
        have hactualDate : physicalStart rate z rewards C_star C_h + (e + n) + 1 <
            r.gridBoundary := by omega
        omega
      obtain ⟨cell, hcell, henabled, _, _, _, _, _, _⟩ :=
        continuingCollectionStep rate rewards C_star C_h z k payload ledger saved
          (by simpa [k, hindex] using hstate) hbefore hnoK
      have hcellWord := originalCell_eq_collectionWord rate rewards C_star C_h e b z hz k
      have hcellEq : cell =
          (collectionWord rate rewards C_star C_h e b z hz)[e + n]'(by
            have hbe : e ≤ b := hz.1
            have hbound := collectionWord_bound rate rewards C_star C_h e b z hz
            omega) := by
        exact Option.some.inj (hcell.symm.trans (by simpa [k] using hcellWord))
      simpa only [← hcellEq] using henabled

/-- The literal predecessor trigger and every original round in the half-open
collection window are enabled. The trigger is the actual word entry `e - 1`;
the window entries are `e + n`. -/
theorem actual_collection_enabled_prefix
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (e b : ℕ)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : z ∈ collectionPrefixCell rate rewards C_star C_h e b) :
    ((collectionWord rate rewards C_star C_h e b z hz)[e - 1]'(by
      have hpos := collectionPrefixCell_trigger_positive rate rewards C_star C_h e b z hz
      have hbe : e ≤ b := hz.1
      have hbound := collectionWord_bound rate rewards C_star C_h e b z hz
      omega)).enabled = true ∧
    ∀ n : ℕ, (hn : n < b - e) →
      ((collectionWord rate rewards C_star C_h e b z hz)[e + n]'(by
        have hbe : e ≤ b := hz.1
        have hbound := collectionWord_bound rate rewards C_star C_h e b z hz
        have hsum : e + n < b := by omega
        exact hsum.trans_le hbound)).enabled = true :=
  actualCollectionIntervalEnabled rate rewards C_star C_h e b z hz

private theorem actualWindowEnabledList
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (e b : ℕ)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : z ∈ collectionPrefixCell rate rewards C_star C_h e b) :
    ∀ (n : ℕ) (hn : n < (refreshWindowRounds
        (collectionWord rate rewards C_star C_h e b z hz) e b).length),
      ((refreshWindowRounds
        (collectionWord rate rewards C_star C_h e b z hz) e b)[n]'hn).enabled = true := by
  let L := collectionWord rate rewards C_star C_h e b z hz
  have hbound := collectionWord_bound rate rewards C_star C_h e b z hz
  have hinterval := actual_collection_enabled_prefix rate rewards C_star C_h e b z hz
  have hbe : e ≤ b := hz.1
  have hlength : (refreshWindowRounds L e b).length = b - e := by
    simp only [refreshWindowRounds, List.length_take, List.length_drop]
    exact Nat.min_eq_left (Nat.sub_le_sub_right (show b ≤ L.length by simpa [L] using hbound) e)
  have hboundL : b ≤ L.length := by simpa [L] using hbound
  intro n hn
  have hn' : n < b - e := by rw [← hlength]; exact hn
  have hsum : e + n < b := by omega
  have hget : (refreshWindowRounds L e b)[n]'hn =
      L[e + n]'(hsum.trans_le hboundL) := by
    simp only [refreshWindowRounds, List.getElem_take, List.getElem_drop]
  rw [hget]
  exact hinterval.2 n hn'

/-- Every proposal in the retained actual trigger/window trace has the source
hazard `h = 4 * m * eta`, including an empty window. -/
theorem actual_collection_refresh_hazard
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (e b : ℕ)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : z ∈ collectionPrefixCell rate rewards C_star C_h e b) :
    RecordedSlowRefresh.proposalProbability p (queueParameters rate)
        (RecordedQueueRun.run (queueParameters rate)
          ((collectionWord rate rewards C_star C_h e b z hz).take (e - 1)))
        ((collectionWord rate rewards C_star C_h e b z hz)[e - 1]'(by
          have hpos := collectionPrefixCell_trigger_positive rate rewards C_star C_h e b z hz
          have hbe : e ≤ b := hz.1
          have hbound := collectionWord_bound rate rewards C_star C_h e b z hz
          omega)) = 4 * (p.m : ℝ) * rate.eta.val ∧
    ∀ n : ℕ, (hn : n < b - e) →
      RecordedSlowRefresh.proposalProbability p (queueParameters rate)
        (RecordedQueueRun.run (queueParameters rate)
          ((collectionWord rate rewards C_star C_h e b z hz).take (e + n)))
        ((collectionWord rate rewards C_star C_h e b z hz)[e + n]'(by
          have hbe : e ≤ b := hz.1
          have hbound := collectionWord_bound rate rewards C_star C_h e b z hz
          have hsum : e + n < b := by omega
          exact hsum.trans_le hbound)) = 4 * (p.m : ℝ) * rate.eta.val := by
  let L := collectionWord rate rewards C_star C_h e b z hz
  let Q := queueParameters rate
  have hpos := collectionPrefixCell_trigger_positive rate rewards C_star C_h e b z hz
  have huv : e ≤ b := hz.1
  have hbound := collectionWord_bound rate rewards C_star C_h e b z hz
  have henabled := actual_collection_enabled_prefix rate rewards C_star C_h e b z hz
  have hwindow := actualWindowEnabledList rate rewards C_star C_h e b z hz
  have hretain : (RecordedQueueRun.run Q (L.take b)).overflow = false := by
    simpa [L, Q, ReferenceActualCollectionHiddenRefreshPath.collectionState,
      ReferenceFirstLaunchNumericalCell.queueParameters] using
      collectionWord_retained rate rewards C_star C_h e b z hz
  have htrace := DeferredRefreshWindow.refreshWindow_trace_active p Q L e b
    hpos huv hbound henabled.1 hwindow hretain
  have hhazard : RecordedSlowRefresh.hazard p Q =
      4 * (p.m : ℝ) * rate.eta.val := by
    rfl
  constructor
  · calc
      _ = RecordedSlowRefresh.hazard p Q := htrace.1
      _ = _ := hhazard
  · intro n hn
    have hlen : (refreshWindowRounds L e b).length = b - e := by
      simp only [refreshWindowRounds, List.length_take, List.length_drop]
      exact Nat.min_eq_left (Nat.sub_le_sub_right (show b ≤ L.length by simpa [L] using hbound) e)
    have hboundL : b ≤ L.length := by simpa [L] using hbound
    have hstep := htrace.2 n hn
    have hsum : e + n < b := by omega
    have hwindowIndex : (refreshWindowRounds L e b)[n]'
        (Nat.lt_of_lt_of_eq hn hlen.symm) =
        L[e + n]'(hsum.trans_le hboundL) := by
      simp only [refreshWindowRounds, List.getElem_take, List.getElem_drop]
    have hstep' : RecordedSlowRefresh.proposalProbability p Q
        (RecordedQueueRun.run Q (L.take (e + n))) (L[e + n]'(hsum.trans_le hboundL)) =
          RecordedSlowRefresh.hazard p Q := by
      rw [← hwindowIndex]
      exact hstep
    simpa only [Q, L] using hstep'.trans hhazard

/-- The atom of the actual endpoint sampled from the original retained array,
with the source's signed finite-window correction and the same old anchor. -/
theorem actual_collection_endpoint_atom
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (e b : ℕ)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : z ∈ collectionPrefixCell rate rewards C_star C_h e b)
    (U : CanonicalOrientedSetLaw.SlowSet p.K p.m) :
    (auxiliaryUniformLaw p).real
      {array : AuxiliaryArray p |
        sampledArrayPath rate rewards C_star C_h e b z hz (b - e) (by omega) array
          (Fin.last (b - e)) = U} =
      DeferredRefreshWindow.slowMassAt p (queueParameters rate)
          (collectionWord rate rewards C_star C_h e b z hz)
          (oldPayload rate rewards C_star C_h e b z hz).anchor
          (oldPayload rate rewards C_star C_h e b z hz).anchor_pos b U +
        (1 - 4 * (p.m : ℝ) * rate.eta.val) ^ (b - e + 1) /
          (4 * (p.m : ℝ) * rate.eta.val) *
          (DeferredRefreshWindow.slowMassAt p (queueParameters rate)
              (collectionWord rate rewards C_star C_h e b z hz)
              (oldPayload rate rewards C_star C_h e b z hz).anchor
              (oldPayload rate rewards C_star C_h e b z hz).anchor_pos e U -
            DeferredRefreshWindow.slowMassAt p (queueParameters rate)
              (collectionWord rate rewards C_star C_h e b z hz)
              (oldPayload rate rewards C_star C_h e b z hz).anchor
              (oldPayload rate rewards C_star C_h e b z hz).anchor_pos (e - 1) U) := by
  let Q := queueParameters rate
  let L := collectionWord rate rewards C_star C_h e b z hz
  let n := b - e
  let anchor := (oldPayload rate rewards C_star C_h e b z hz).anchor
  let hanchor := (oldPayload rate rewards C_star C_h e b z hz).anchor_pos
  have hpos := collectionPrefixCell_trigger_positive rate rewards C_star C_h e b z hz
  have huv : e ≤ b := hz.1
  have hbound := collectionWord_bound rate rewards C_star C_h e b z hz
  have henabled := actual_collection_enabled_prefix rate rewards C_star C_h e b z hz
  have hwindow := actualWindowEnabledList rate rewards C_star C_h e b z hz
  have hcap : Q.eta ≤ 1 /
      (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (CanonicalRecordingRates.L_stab p : ℝ)) := by
    simpa only [Q, ReferenceFirstLaunchNumericalCell.queueParameters] using rate.sourceCap
  have hretain : (RecordedQueueRun.run Q (L.take b)).overflow = false := by
    simpa [L, Q, ReferenceActualCollectionHiddenRefreshPath.collectionState,
      ReferenceFirstLaunchNumericalCell.queueParameters] using
      collectionWord_retained rate rewards C_star C_h e b z hz
  have hformula := DeferredRefreshWindow.deferredRefreshWindowPMF_toReal
    p Q L e b hpos huv hbound anchor hanchor hcap henabled.1 hwindow hretain U
  have hhazard := actual_collection_refresh_hazard rate rewards C_star C_h e b z hz
  have htrace := DeferredRefreshWindow.refreshWindow_trace_active p Q L e b
    hpos huv hbound henabled.1 hwindow hretain
  have hconstant : RecordedSlowRefresh.hazard p Q =
      4 * (p.m : ℝ) * rate.eta.val := by
    exact htrace.1.symm.trans hhazard.1
  rw [hconstant] at hformula
  have hprefixMap := sampledPrefix_map rate rewards C_star C_h e b z hz n (by omega)
  have harrayPathMap := sampledArrayPath_map rate rewards C_star C_h e b z hz n (by omega)
  let endpoint := fun array : AuxiliaryArray p =>
    sampledArrayPath rate rewards C_star C_h e b z hz n (by omega) array (Fin.last n)
  let pathEndpoint := fun path : Fin (n + 1) → CanonicalOrientedSetLaw.SlowSet p.K p.m =>
    path (Fin.last n)
  have hmeasPathEndpoint : Measurable pathEndpoint := measurable_pi_apply _
  have hmeasArrayPath := measurable_sampledArrayPath rate rewards C_star C_h e b z hz n (by omega)
  have hmeasEndpoint : Measurable endpoint := hmeasPathEndpoint.comp hmeasArrayPath
  have hendpointMap :
      (auxiliaryUniformLaw p).map endpoint =
        (prefixUniformLaw n).map
          (sampledPrefix rate rewards C_star C_h e b z hz n (by omega)) := by
    calc
      _ = ((auxiliaryUniformLaw p).map
          (sampledArrayPath rate rewards C_star C_h e b z hz n (by omega))).map
            pathEndpoint := by
              symm
              exact MeasureTheory.Measure.map_map hmeasPathEndpoint hmeasArrayPath
      _ = ((prefixUniformLaw n).map
          (sampledPath rate rewards C_star C_h e b z hz n (by omega))).map
            pathEndpoint := by
              rw [harrayPathMap]
      _ = (prefixUniformLaw n).map
          (sampledPrefix rate rewards C_star C_h e b z hz n (by omega)) := by
              rw [MeasureTheory.Measure.map_map hmeasPathEndpoint
                (measurable_sampledPath rate rewards C_star C_h e b z hz n (by omega))]
              have hfun : (fun coordinates =>
                  pathEndpoint (sampledPath rate rewards C_star C_h e b z hz n (by omega) coordinates)) =
                  sampledPrefix rate rewards C_star C_h e b z hz n (by omega) := by
                funext coordinates
                exact sampledPath_last rate rewards C_star C_h e b z hz n (by omega) coordinates
              exact congrArg (fun f => (prefixUniformLaw n).map f) hfun
  calc
    (auxiliaryUniformLaw p).real {array | endpoint array = U} =
        ((auxiliaryUniformLaw p).map endpoint).real {U} := by
          have hset : {array : AuxiliaryArray p | endpoint array = U} = endpoint ⁻¹' {U} := by
            ext array
            simp
          simp only [MeasureTheory.Measure.real_def]
          rw [MeasureTheory.Measure.map_apply hmeasEndpoint (measurableSet_singleton U), ← hset]
    _ = ((prefixUniformLaw n).map
          (sampledPrefix rate rewards C_star C_h e b z hz n (by omega))).real {U} := by
          rw [hendpointMap]
    _ = ((DeferredRefreshWindow.deferredRefreshWindowPMF
          p Q L e b hpos huv hbound anchor hanchor hcap).toMeasure {U}).toReal := by
          rw [hprefixMap]
          simp only [MeasureTheory.Measure.real_def,
            DeferredRefreshWindow.deferredRefreshWindowPMF, Q, L, n, anchor]
    _ = (DeferredRefreshWindow.deferredRefreshWindowPMF
          p Q L e b hpos huv hbound anchor hanchor hcap U).toReal := by
          rw [PMF.toMeasure_apply_singleton
            (DeferredRefreshWindow.deferredRefreshWindowPMF
              p Q L e b hpos huv hbound anchor hanchor hcap) U (measurableSet_singleton U)]
    _ = _ := by simpa only [Q, L, anchor, hanchor] using hformula

end Bandits.Support.ReferenceActualCollectionEnabledPrefixEndpoint

end
