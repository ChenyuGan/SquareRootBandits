/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCorrectedCurrentCutoffReplyRetention

import Lean.Elab.Tactic.Omega

/-!
# Original first-launch source cells for the corrected inherited follower queue

This module joins the first-launch physical recording word to the actual first
corrected replacement.  The current payload and its live suffix remain those
of the admitted current-retention producer. The actual prior UPs supply the
OLD terminal fields at birth, throughout that live suffix, at cutoff, and
through the actual collection and its first excluded INPUT/CHOICE boundary.

Sources: `sources/zip4/manuscript/appendix_a_local_protocol.tex:28-64`,
`sources/zip4/manuscript/06_interruptions.tex:40-100,192-233,246-299`, and
`sources/zip4/manuscript/04_slow_fast_learner.tex:157-174`.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open Bandits.Support.ConstructorDimensions

namespace Bandits.Support.ReferenceFirstCorrectedInheritedFollowerCutoffQueue

variable {p : ConstructorDimensions.Parameters}

private theorem prefix_map_eq_of_coverage {α β : Type*} (R : List α)
    (f : α → Option β) (L : List β) (hN : L.length ≤ R.length)
    (h : ∀ k : Fin L.length, ∃ r, R[k.val]? = some r ∧ f r = some L[k.val]) :
    (R.take L.length).map f = L.map some := by
  apply List.ext_getElem
  · simp [List.length_take, Nat.min_eq_left hN]
  · intro k hk hk'
    have hkL : k < L.length := by simpa using hk'
    obtain ⟨r, hr, hf⟩ := h ⟨k, hkL⟩
    have he : R[k]'(by omega) = r := (List.getElem?_eq_some_iff.mp hr).2
    simpa only [List.getElem_map, List.getElem_take, he] using hf

/-- Reconstruct the original first-live recording word and identify its
complete physical-prefix cells on the same source run. The cutoff crossing,
full-horizon span, and strict shortness all come from corrected-cell
membership. -/
theorem actual_first_live_source_prefix
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : z ∈ ReferenceFirstCollectionCorrectedSliceNumericalPrefix.correctedCell
      rate rewards C_star C_h u t) :
    ∃ (hc : (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
      (hspan : ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed +
          (p.T - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) ≤ p.T),
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun rate z rewards C_star C_h
          hc (p.T - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) hspan).records).length <
            (p.T - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) ∧
      ∃ (L0 : List (RecordedQueueRun.RoundInput p.K)),
      L0 = ReferenceFirstWindowNumericalStream.actualLiveSourceCells rate z rewards C_star C_h
        hc (p.T - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) hspan ∧
      List.map (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate)
        ((ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).take L0.length) =
        L0.map some := by
  classical
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  let count := p.T - s
  obtain ⟨hc, hspan, hshort, f, head, valid, D, L, _hsu, _hut, _hu, _ht,
      _hpending, _hrecord, _hchoice, _hDlen, _hDzero, _hDread, hL, _hpast,
      hLlen, hcoverage⟩ :=
    ReferenceFirstCollectionCurrentRetainedGate.firstCell_prefix_coverage
      rate rewards C_star C_h u t z hz.1
  have hshort' : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun rate z rewards C_star C_h
        hc count hspan).records).length < count := by
    simpa only [ReferenceFirstCollectionReadyStream.actualEpoch,
      ReferenceFirstCollectionReadyStream.startTime, s, count] using hshort
  let L0 := ReferenceFirstWindowNumericalStream.actualLiveSourceCells
    rate z rewards C_star C_h hc count hspan
  have hepoch := ReferenceCompleteFirstPhaseObservationRecovery.completeSuffixRecords_eq_actualFirstLiveRun
    rate rewards C_star C_h z hc
  have hwindow : ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
      rate z rewards C_star C_h hc count hspan =
      ReferenceFirstLiveConfirmationHistory.firstLiveWindow R := by
    unfold ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
    rw [← hepoch]
  have hlen0 : L0.length =
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length := by
    exact (ReferenceFirstWindowNumericalStream.actualLiveSourceCells_length
      rate z rewards C_star C_h hc count hspan).trans (congrArg List.length hwindow)
  have hL0 : L = L0 ++ D := by simpa only [L0] using hL
  have hbound : L0.length ≤ L.length := by
    rw [hL0, List.length_append]
    omega
  have hRlen : R.length = count := by
    simp only [R, count, s, ReferenceCompletePhysicalHistory.completeSuffixRecords_length]
  have hL0R : L0.length ≤ R.length := by
    rw [hRlen]
    have ht : t.val - s ≤ p.T - s := by omega
    omega
  have hsource : (R.take L0.length).map
      (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate) = L0.map some := by
    apply prefix_map_eq_of_coverage R (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate)
      L0 hL0R
    intro k
    have hkL : k.val < L.length := by
      rw [hL0, List.length_append]
      omega
    obtain ⟨r, hr, _, hcell⟩ := hcoverage ⟨k.val, hkL⟩
    have hword : L[k.val] = L0[k.val] := by
      simp only [hL0, List.getElem_append_left k.isLt]
    exact ⟨r, hr, hcell.trans (congrArg some hword)⟩
  refine ⟨hc, ?_, ?_⟩
  · simpa [s, ReferenceCompletePhysicalHistory.physicalStart,
      ReferenceCompletePhysicalHistory.generatedBoundary,
      ReferenceCompletePhysicalHistory.generatedInput] using hspan
  · exact ⟨hshort', L0, rfl, by simpa only [R] using hsource⟩

/-- Eliminate the actual executed receiver, retaining its literal collection
choice and the candidate used by the canonical first-cutoff API. -/
private theorem acceptedUp_choice_receipt
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1))
    (M : ReferenceCollectionPhaseHistory.UpRecord p rate)
    (haccepted : ReferenceCollectionPhaseHistory.AcceptedUp r.input i M) :
    ∃ c : ReferenceCollectionSegmentExtraction.Choice rate,
      ReferenceCollectionSegmentExtraction.choice r.input = some c ∧
      i = ReferenceActivePhysicalStep.upSenderIndex r.input ∧
      let candidate := CoordinatorCollectionLedger.startRoundCandidate c.preLedger r.input.time
        (ReferenceActivePhysicalStep.collectionEnabled c.preLedger r.input.time)
        (ReferenceCollectionRawBufferHistory.rawDiagnostic r)
      ReferenceCollectionSegmentExtraction.effectiveParse r.input candidate = some M ∧
      CoordinatorCollectionLedger.acceptUpCheck candidate i M = true := by
  classical
  obtain ⟨tail, recording, started, decoded, bank, htail, hrecording, hstarted,
    hreceived, hparsed, hi⟩ := haccepted
  have hchoice : ∃ initializer : Option (ReferenceCollectionSegmentExtraction.Initializer p),
      ReferenceCollectionSegmentExtraction.choice r.input =
        some ⟨tail.payload, tail.ledger, tail.started, tail.weights, initializer⟩ := by
    unfold ReferenceCollectionPhaseHistory.executedTail at htail
    dsimp only at htail
    split at htail
    · contradiction
    next hn =>
      cases hd : (ReferenceActivePhysicalStep.prepare r.input).coordinator with
      | first outcome => cases outcome <;> simp only [hd] at htail <;> contradiction
      | live registers owned base outcome =>
          cases outcome <;> simp only [hd] at htail <;> try contradiction
          cases Option.some.inj htail
          refine ⟨some (ReferenceCollectionSegmentExtraction.cutoffInitializer
            (ReferenceActivePhysicalStep.liveRegistersAt registers r.input.time)
            (ReferenceActivePhysicalStep.liveOwnedAt registers owned r.input.time) base r.input.time), ?_⟩
          unfold ReferenceCollectionSegmentExtraction.choice
          rw [ite_eq_right hn, hd]
          rfl
      | collection payload ledger clock cutoff outcome =>
          cases outcome <;> simp only [hd] at htail <;> try contradiction
          cases Option.some.inj htail
          refine ⟨none, ?_⟩
          unfold ReferenceCollectionSegmentExtraction.choice
          rw [ite_eq_right hn, hd]
          rfl
      | invalidCollectionCutoff => simp only [hd] at htail; contradiction
      | dagger => simp only [hd] at htail; contradiction
  obtain ⟨initializer, hc⟩ := hchoice
  let c : ReferenceCollectionSegmentExtraction.Choice rate :=
    ⟨tail.payload, tail.ledger, tail.started, tail.weights, initializer⟩
  have hrecord : r.output.coordinator.recording = some recording := by
    rw [r.output_eq]
    change (ReferenceActivePhysicalStep.prepare r.input).observeCoordinator.recording = _
    rw [ReferenceCollectionSegmentExtraction.choice_tail r.input c hc]
    dsimp only [c]
    simp only [ReferenceActivePhysicalStep.collectionPostChoice, hrecording, hstarted,
      ReferenceCollectionSegmentExtraction.collectionFinish_recording]
  have hraw : ReferenceCollectionRawBufferHistory.rawDiagnostic r =
      CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording := by
    simp only [ReferenceCollectionRawBufferHistory.rawDiagnostic, hrecord, Option.bind_some]
    rfl
  have hcandidate : started = CoordinatorCollectionLedger.startRoundCandidate
      c.preLedger r.input.time
      (ReferenceActivePhysicalStep.collectionEnabled c.preLedger r.input.time)
      (ReferenceCollectionRawBufferHistory.rawDiagnostic r) := by
    rw [hraw]
    exact CollectionCheckedExecution.startRound_success_candidate _ _ _ _ _ hstarted
  have hdecode := ReferenceCollectionSegmentExtraction.receiveUp_decode_result r.input started
  rw [hreceived] at hdecode
  have hparse : ReferenceCollectionSegmentExtraction.effectiveParse r.input started = some M :=
    hparsed
  have haccept : CoordinatorCollectionLedger.acceptUpCheck started i M = true := by
    rw [hparse, ← hi] at hdecode
    by_contra hnot
    simp [CoordinatorCollectionLedger.decodeUp, hnot] at hdecode
    repeat (first | split at hdecode | contradiction)
  refine ⟨c, hc, hi, ?_⟩
  dsimp only
  rw [← hcandidate]
  exact ⟨hparse, haccept⟩

/-- Every follower has an accepted UP in the actual first collection interval
strictly before the actual corrected replacement. The witness is read from
the original complete suffix through `laterChosen_pending_empty` and
`acceptedLabel_witness` in the run-history producer. -/
theorem actual_prior_first_collection_accepted_up_in_window
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : z ∈ ReferenceFirstCollectionCorrectedSliceNumericalPrefix.correctedCell
      rate rewards C_star C_h u t)
    (i : Fin (p.m - 1)) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let b := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex
      rate rewards C_star C_h z
    ∃ currentBirth currentPayload,
      R[b]? = some currentBirth ∧
      ReferenceAssignmentPayloadPersistence.InstallationBirth currentBirth currentPayload ∧
      currentPayload.sigma = t ∧
    ∃ k r message sender state memory prior,
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length ≤ k ∧
      k < b ∧ R[k]? = some r ∧
      ReferenceCollectionPhaseHistory.AcceptedUp r.input i message ∧
      sender = (ReferenceActivePhysicalStep.prepare r.input).followers.followers
        (ReferenceActivePhysicalStep.upSenderIndex r.input) ∧
      sender.configuration = .ordinary state memory ∧ state.status = .unoccupied ∧
      message.val.S = state.S ∧ message.val.delta = state.delta ∧
      message.val.q = state.backlog ∧ state.lastDown = some prior ∧
      prior.val.sigma = message.val.sigma := by
  classical
  obtain ⟨hc, hspan, _hshort, _L0, _hL0, _hsource⟩ :=
    actual_first_live_source_prefix rate rewards C_star C_h u t z hz
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let s := ReferenceInitializationRun.elapsed p
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed
  let count := p.T - s
  let b := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex
    rate rewards C_star C_h z
  have hretention := ReferenceFirstCorrectedCurrentCutoffReplyRetention.actual_first_corrected_current_cutoff_reply_retention
    rate rewards C_star C_h u t z hz
  dsimp only at hretention
  obtain ⟨_currentL, _currentCell, currentBirth, currentPayload, _currentBase, hroot⟩ := hretention
  have hrootLookup : R[b]? = some currentBirth := hroot.2.2.2.2.1
  have hrootInstallation :
      ReferenceAssignmentPayloadPersistence.InstallationBirth currentBirth currentPayload :=
    hroot.2.2.2.2.2.1
  have hrootSigma : currentPayload.sigma = t := hroot.2.2.2.2.2.2.1
  let initial := ReferenceFirstCollectionEpochAlignment.actualLaunchState
    rate z rewards C_star C_h hc
  let active := (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
    rate z rewards C_star C_h hc).1
  have hspan' : s + count ≤ p.T := by
    simpa [s, count, ReferenceCompletePhysicalHistory.physicalStart,
      ReferenceCompletePhysicalHistory.generatedBoundary,
      ReferenceCompletePhysicalHistory.generatedInput] using hspan
  let epoch := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
    rate z rewards C_star C_h hc count hspan'
  have htime := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.firstCell_birth_time
    rate rewards C_star C_h u t z hz
  have hbtime : s + b = t.val := by
    simpa [s, b, ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart,
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex,
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords, R,
      ReferenceCompletePhysicalHistory.physicalStart,
      ReferenceCompletePhysicalHistory.generatedBoundary,
      ReferenceCompletePhysicalHistory.generatedInput] using htime
  have hspanB : s + (b + 1) ≤ p.T := by omega
  obtain ⟨sourceBirth, hbirth, _hactual, _hbTime, hlater⟩ :=
    ReferenceFirstCollectionCorrectedNextPhysicalReadout.firstCell_firstReplacement_record
      rate rewards C_star C_h u t z hz.1
  have hbirthR : R[b]? = some sourceBirth := by
    simpa [R, b, ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex,
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords] using hbirth
  have hsameBirth : currentBirth = sourceBirth :=
    Option.some.inj (hrootLookup.symm.trans hbirthR)
  subst sourceBirth
  have hrecords : R = epoch.records := by
    have hepoch := ReferenceCompleteFirstPhaseObservationRecovery.completeSuffixRecords_eq_actualFirstLiveRun
      rate rewards C_star C_h z hc
    simpa [R, epoch, ReferenceFirstWindowNumericalStream.actualFirstLiveRun,
      ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun,
      ReferenceFirstCollectionEpochAlignment.actualLaunchState,
      ReferenceFirstLaunchNumericalCell.launchState, s, count,
      ReferenceCompletePhysicalHistory.physicalStart,
      ReferenceCompletePhysicalHistory.generatedBoundary,
      ReferenceCompletePhysicalHistory.generatedInput] using hepoch
  have hcount : R.length = count := by
    simp [R, count, s, ReferenceCompletePhysicalHistory.completeSuffixRecords_length,
      ReferenceCompletePhysicalHistory.physicalStart,
      ReferenceCompletePhysicalHistory.generatedBoundary,
      ReferenceCompletePhysicalHistory.generatedInput]
  have hbLt : b < count := by
    have hlt := (List.getElem?_eq_some_iff.mp hbirthR).1
    rw [hcount] at hlt
    exact hlt
  let row := ActualInitializationPhysicalStep.selectedRowIndex p z
  have hprefixBirth : epoch.records[b]? = some currentBirth := by
    rw [← hrecords]
    exact hbirthR
  have hnextRecord :
      (ReferenceCollectionPhaseHistory.nextInput initial z.1.2 row rewards s b hspanB active) =
        (ReferenceAssignmentPayloadChronology.actualRunRecordAt initial z.1.2 row rewards
          s b hspanB active).input := by
    rfl
  obtain ⟨suffixShort, hprefixShortRun⟩ :=
    ReferenceCollectionPhaseHistory.run_records_prefix initial z.1.2 row rewards s
      (b + 1) (count - (b + 1)) (by omega) active
  have hprefixShortRun' : epoch.records =
      (ReferenceActivePhysicalHorizon.run initial z.1.2 row rewards s (b + 1)
        (by omega) active).records ++ suffixShort := by
    have hadd : (b + 1) + (count - (b + 1)) = count := by omega
    simpa [epoch, ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun,
      initial, active, row, hadd] using hprefixShortRun
  have hsuccRecord := ReferenceAssignmentPayloadChronology.run_successor_actualRunRecordAt
    initial z.1.2 row rewards s b hspanB active
  have hnextAt : epoch.records[b]? = some
      (ReferenceAssignmentPayloadChronology.actualRunRecordAt initial z.1.2 row rewards
        s b hspanB active) := by
    rw [hprefixShortRun', hsuccRecord]
    have hRunLength := ReferenceActivePhysicalHorizon.run_record_count initial z.1.2 row
      rewards s b (by omega) active
    rw [List.append_assoc]
    rw [List.getElem?_append_right (by rw [hRunLength])]
    simp [hRunLength]
  have hbirthEq : currentBirth = ReferenceAssignmentPayloadChronology.actualRunRecordAt
      initial z.1.2 row rewards s b hspanB active :=
    Option.some.inj (hprefixBirth.symm.trans hnextAt)
  have hlaterNext : ReferenceCollectionPhaseHistory.laterChosen
      (ReferenceCollectionPhaseHistory.nextInput initial z.1.2 row rewards s b hspanB active) = true := by
    rw [hnextRecord, ← hbirthEq]
    exact hlater
  have hfirst := (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
    rate z rewards C_star C_h hc).2
  obtain ⟨before, cutoff, during, payload, old, proposal, he, hcut,
      _hc, _hempty, _hwindow, hall⟩ :=
    ReferenceCollectionPhaseHistory.run_laterStart_all_up_accepted initial z.1.2 row rewards
      s b hspanB active hfirst
      hlaterNext
  obtain ⟨k, r, message, hbefore, hk, hr, haccepted, _hsigma⟩ := hall i
  obtain ⟨suffix, hp⟩ := ReferenceCollectionPhaseHistory.run_records_prefix initial
      z.1.2 row rewards s b (count - b) (by omega) active
  have hRunPrefix : epoch.records =
      (ReferenceActivePhysicalHorizon.run initial z.1.2 row rewards s b (by omega) active).records ++
        suffix := by
    have hadd : b + (count - b) = count := by omega
    simpa [epoch, ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun,
      initial, active, row, hadd] using hp
  have hcutR : R[before.length]? = some cutoff := by
    rw [hrecords, hRunPrefix, he, List.append_assoc]
    rw [List.getElem?_append_right (by omega), Nat.sub_self]
    rfl
  have hwbefore : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length ≤
      before.length := by
    by_contra hnot
    have hlt : before.length <
        (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length := by omega
    have hp : ReferenceFirstLiveConfirmationHistory.firstLiveWindow R <+: R :=
      List.takeWhile_prefix _
    have hget := hp.getElem hlt
    have hcget := (List.getElem?_eq_some_iff.mp hcutR).2
    have hmem : cutoff ∈ ReferenceFirstLiveConfirmationHistory.firstLiveWindow R := by
      rw [← hcget, ← hget]
      exact List.getElem_mem hlt
    have htag := List.mem_takeWhile_imp hmem
    change (!ReferenceCollectionPhaseHistory.cutoffChosen cutoff.input) = true at htag
    rw [hcut] at htag
    cases htag
  have hRrecord : R[k]? = some r := by
    rw [hrecords, hRunPrefix]
    have hRunLength := ReferenceActivePhysicalHorizon.run_record_count initial z.1.2 row
      rewards s b (by omega) active
    rw [List.getElem?_append_left (by simpa [hRunLength] using hk)]
    exact hr
  obtain ⟨sender, state, memory, hsender, _hi, hconfiguration, hunoccupied,
      _hoffer, _hstart, _hstarted, hS, hdelta, hq, hprior, _hpositive, _hslot⟩ :=
    ReferenceAcceptedUpFollowerHistory.acceptedUp_current_choice haccepted
  obtain ⟨prior, hlastDown, hpriorSigma⟩ := hprior
  refine ⟨currentBirth, currentPayload, hrootLookup, hrootInstallation, hrootSigma, ?_⟩
  exact ⟨k, r, message, sender, state, memory, prior, hwbefore.trans hbefore, hk, hRrecord, haccepted,
    hsender, hconfiguration, hunoccupied, hS, hdelta, hq, hlastDown, hpriorSigma⟩

/-- Forget only the window lower bound from the actual accepted reply. -/
theorem actual_prior_first_collection_accepted_up
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : z ∈ ReferenceFirstCollectionCorrectedSliceNumericalPrefix.correctedCell
      rate rewards C_star C_h u t)
    (i : Fin (p.m - 1)) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let b := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex
      rate rewards C_star C_h z
    ∃ currentBirth currentPayload,
      R[b]? = some currentBirth ∧
      ReferenceAssignmentPayloadPersistence.InstallationBirth currentBirth currentPayload ∧
      currentPayload.sigma = t ∧
    ∃ k r message sender state memory prior,
      k < b ∧ R[k]? = some r ∧
      ReferenceCollectionPhaseHistory.AcceptedUp r.input i message ∧
      sender = (ReferenceActivePhysicalStep.prepare r.input).followers.followers
        (ReferenceActivePhysicalStep.upSenderIndex r.input) ∧
      sender.configuration = .ordinary state memory ∧ state.status = .unoccupied ∧
      message.val.S = state.S ∧ message.val.delta = state.delta ∧
      message.val.q = state.backlog ∧ state.lastDown = some prior ∧
      prior.val.sigma = message.val.sigma := by
  obtain ⟨birth, P, hb, hborn, hsigma, k, r, M, sender, state, memory, prior,
    _hw, hk, hr, hM, hsender, hconfiguration, hu, hS, hd, hq, hlast, hsig⟩ :=
    actual_prior_first_collection_accepted_up_in_window rate rewards C_star C_h u t z hz i
  exact ⟨birth, P, hb, hborn, hsigma, k, r, M, sender, state, memory, prior,
    hk, hr, hM, hsender, hconfiguration, hu, hS, hd, hq, hlast, hsig⟩

private theorem collectionWindow_prefix
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (R : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (w : ℕ) : ReferenceCollectionPhaseHistory.collectionWindow R w <+: R.drop w := by
  refine ⟨(R.drop (w + 1)).dropWhile
    (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input), ?_⟩
  rw [ReferenceCollectionPhaseHistory.collectionWindow, List.append_assoc,
    List.takeWhile_append_dropWhile]
  simp only [← List.drop_drop, List.take_append_drop]

/-- Disabled cells have no service, independently of their unused arrival. -/
private theorem replay_eq_unstopped
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (cells : List (RecordedQueueRun.RoundInput p.K))
    (a : Fin p.K) (initial : ℕ × ℕ) :
    QueueReplay.replay (4 * rate.n) initial
      (cells.map fun c => (c.enabled, RecordedQueueRun.quantizedArrival
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a)) =
    QueueReplay.replay (4 * rate.n) initial
      (cells.map fun c => UnstoppedRecordedQueueComparison.unstoppedRecord
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a) := by
  induction cells generalizing initial with
  | nil => rfl
  | cons c cells ih =>
      change QueueReplay.replay (4 * rate.n)
          (QueueReplay.transition (4 * rate.n) initial
            (c.enabled, RecordedQueueRun.quantizedArrival
              (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a)) _ =
        QueueReplay.replay (4 * rate.n)
          (QueueReplay.transition (4 * rate.n) initial
            (UnstoppedRecordedQueueComparison.unstoppedRecord
              (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a)) _
      rw [ih]
      congr 1
      cases he : c.enabled <;>
        simp only [UnstoppedRecordedQueueComparison.unstoppedRecord, he,
          Bool.false_eq_true, ite_false, ite_true, QueueReplay.transition]

private theorem retained_before_replacement_origin
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : z ∈ ReferenceFirstCollectionCorrectedSliceNumericalPrefix.correctedCell
      rate rewards C_star C_h u t)
    (originalBirth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (P0 : ReferenceActivePhysicalStep.Payload rate)
    (hzero : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[0]? = some originalBirth)
    (hborn : ReferenceAssignmentPayloadPersistence.InstallationBirth originalBirth P0) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let b := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex rate rewards C_star C_h z
    ∀ (j : Fin R.length), j.val < b → ∀ i M,
      ReferenceAcceptedUpFollowerHistory.RetainedDown R[j.val] i M → M = P0.downRecord i := by
  classical
  intro R b
  obtain ⟨hc, hspan, hshort, _L0, _hL0, _hsource⟩ :=
    actual_first_live_source_prefix rate rewards C_star C_h u t z hz
  let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  let count := p.T - s
  let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
    rate z rewards C_star C_h hc count hspan
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length
  let B := ReferenceCollectionPhaseHistory.collectionWindow E.records w
  have hrecords : R = E.records :=
    ReferenceCompleteFirstPhaseObservationRecovery.completeSuffixRecords_eq_actualFirstLiveRun
      rate rewards C_star C_h z hc
  have hb : b = w + B.length := by
    change _ + _ = _
    simp only [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords,
      R, hrecords, w, B]
  obtain ⟨cut, P', birth', _registers, _owned, _base, _hcutIndex, _hcutUnique,
    _hcutState, _hcutoff, _hP', _hP'sigma, _hqueues, _hfirstCutoff,
    hbirthMember, hbirthInstall, hbirthTime, _hbirthFirst, _hwindow,
    _hselected, hretained, hprior⟩ :=
    (ReferenceFirstCollectionDownPayloadOrigin.actual_first_collection_down_payload_origin
      rate z rewards C_star C_h count hc hspan hshort).origin
  have hbirthEq : birth' = originalBirth := by
    obtain ⟨n, hn, hget⟩ := List.mem_iff_getElem.mp hbirthMember
    have hlookup : R[n]? = some birth' := by
      rw [hrecords, List.getElem?_eq_getElem hn, hget]
    have htime := ReferenceFirstCollectionRenewalRecordingFeedback.complete_record_time
      rate z rewards C_star C_h n birth' hlookup
    have hnzero : n = 0 := by omega
    rw [hnzero, hzero] at hlookup
    exact Option.some.inj hlookup.symm
  subst birth'
  have hP' : P' = P0 := ReferenceAssignmentPayloadChronology.installationBirth_payload_unique
    originalBirth P' P0 hbirthInstall hborn
  obtain ⟨_cb, _cp, _hb, _hcb, _hsigma, k, _r, _M, _sender, _state, _memory, _prior,
    hwk, hkb, _hr, _haccepted, _hrest⟩ :=
    actual_prior_first_collection_accepted_up_in_window rate rewards C_star C_h u t z hz
      ⟨0, by have hm := p.two_le_m; omega⟩
  have hwR : w = (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length := by
    rw [hrecords]
  have hBpositive : 0 < B.length := by rw [← hwR] at hwk; omega
  intro j hj i M hM
  have hlookup : E.records[j.val]? = some R[j.val] := by
    rw [← hrecords]
    exact List.getElem?_eq_getElem j.isLt
  by_cases hjw : j.val < w
  · have h := hprior ⟨0, hBpositive⟩ j.val (by omega) R[j.val] hlookup i M hM
    exact h.1.trans (congrArg (fun P : ReferenceActivePhysicalStep.Payload rate => P.downRecord i) hP')
  · let n : Fin B.length := ⟨j.val - w, by omega⟩
    have hsum : w + n.val = j.val := by dsimp only [n]; omega
    have hlookup' : E.records[w + n.val]? = some R[j.val] := by rw [hsum]; exact hlookup
    have h := hretained n R[j.val] hlookup' i M hM
    exact h.1.trans (congrArg (fun P : ReferenceActivePhysicalStep.Payload rate => P.downRecord i) hP')

private theorem mapM_some_at {α β : Type*} (f : α → Option β)
    (xs : List α) (ys : List β) (h : xs.mapM f = some ys)
    (n : ℕ) (x : α) (hx : xs[n]? = some x) : ∃ y, f x = some y := by
  induction xs generalizing ys n with
  | nil => simp only [List.getElem?_nil, reduceCtorEq] at hx
  | cons head rest ih =>
      cases hf : f head with
      | none => simp only [List.mapM_cons, hf] at h; cases h
      | some y =>
          cases ht : rest.mapM f with
          | none => simp only [List.mapM_cons, hf, ht] at h; cases h
          | some tail =>
              cases n with
              | zero =>
                  have heq : head = x := Option.some.inj hx
                  exact ⟨y, heq ▸ hf⟩
              | succ n => exact ih tail ht n (by simpa only [List.getElem?_cons_succ] using hx)

private theorem attributedArrival_selected
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (P : ReferenceActivePhysicalStep.Payload rate) (i : Fin (p.m - 1))
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (value : Bool × ℕ)
    (h : ReferenceFirstCorrectedAssignedArrivalPrefix.attributedArrival? P i r = some value) :
    ∃ selected : ReferenceActivePhysicalStep.Selection r.input,
      r.output.preparation.coordinator.selection = some selected ∧ selected.view.payload = P := by
  classical
  unfold ReferenceFirstCorrectedAssignedArrivalPrefix.attributedArrival? at h
  cases hs : r.output.preparation.coordinator.selection with
  | none => simp only [hs, reduceCtorEq] at h
  | some selected =>
      simp only [hs] at h
      split at h
      · exact ⟨selected, rfl, by assumption⟩
      · contradiction

private theorem retainedDown_selected_record
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (P : ReferenceActivePhysicalStep.Payload rate) (i : Fin (p.m - 1))
    (M : ReferenceAcceptedUpFollowerHistory.DownRecord (p := p) (rate := rate))
    (hM : ReferenceAcceptedUpFollowerHistory.RetainedDown r i M)
    (selected : ReferenceActivePhysicalStep.Selection r.input)
    (hs : r.output.preparation.coordinator.selection = some selected)
    (hp : selected.view.payload = P) : M = P.downRecord i := by
  obtain ⟨logged, cut, after, raw, scan, registers, lastService, _hinput, hdown, houtcome⟩ := hM
  obtain ⟨_choice, _memory, _logged, _hchoice, _hu, _hlogging, _hlogged, hcall⟩ :=
    ReferenceFollowerSparseEmissionRecovery.actualDownDiagnostic_choice r i cut hdown
  have haccepted := hcall ▸ houtcome
  have hview : r.output.preparation.coordinator.downView = some selected.view := by
    change r.output.preparation.coordinator.selection.map
      ReferenceActivePhysicalStep.Selection.view = some selected.view
    rw [hs]
    rfl
  rw [hview] at haccepted
  have hfields := ReferenceActiveDataOwnership.referenceDown_accepted_fields
    selected.view _ _ _ _ _ _ _ _ _ _ _ _ haccepted
  rw [(r.output.preparation.follower_alignment i).2.1, hp] at hfields
  exact hfields.1

private theorem old_output_choice_frame
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (P : ReferenceActivePhysicalStep.Payload rate) (i : Fin (p.m - 1))
    (selected : ReferenceActivePhysicalStep.Selection r.input)
    (hs : r.output.preparation.coordinator.selection = some selected)
    (hp : selected.view.payload = P)
    (next : ReferencePrelaunchFollower.State p rate.eta)
    (nextMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hout : r.output.next.followers i = .ordinary next nextMemory)
    (hold : next.lastDown ≠ some (P.downRecord i)) :
    ∃ choice memory,
      (ReferenceFollowerFixedReply.actualChoice r i).configuration = .ordinary choice memory ∧
      next.lastDown = choice.lastDown ∧
      (choice.status = .unoccupied → next.status = .unoccupied ∧
        ReferenceFollowerReplyChronology.reply next = ReferenceFollowerReplyChronology.reply choice) ∧
      (∀ sigma, ¬ ReferenceFollowerReplyChronology.appliedDown r i sigma) := by
  have hfinish : (ReferenceActivePhysicalStep.finishFollower
      r.output.preparation.coordinator.downView
      (r.output.preparation.followers.followers i)
      (r.output.preparation.feedback.observations
        (PublicDiscreteDraws.followerPlayer p.two_le_m i))).configuration = .ordinary next nextMemory := by
    rw [← ReferenceFollowerBufferProvenance.roundRecord_follower_eq_finishFollower i r]
    simpa only [r.output_eq, ReferenceActivePhysicalStep.step] using hout
  obtain ⟨choice, memory, post, hchoice, hrecord, hrelease, _hdiagInput, _hdiag⟩ :=
    ReferenceFollowerReplyChronology.finishFollower_ordinary_inversion _ _ _ next nextMemory hfinish
  have hframe := ReferenceFollowerReplyChronology.releaseAndFinish_frame
    _ _ _ _ choice post next memory nextMemory hrelease
  have hinv := ReferenceFollowerReplyChronology.recordFollower_ordinary_inversion
    _ _ _ _ _ _ _ _ choice post hrecord
  rcases hinv with ⟨hpost, hkeep⟩ | ⟨logged, cut, raw, M, scan, registers, lastService,
    _hlogged, _hcut, hcall, haccepted, _hstrict, _hlast⟩
  · have hlast : next.lastDown = choice.lastDown := (congrArg Prod.fst hframe.1).trans hpost
    refine ⟨choice, memory, hchoice, hlast, ?_, ?_⟩
    · intro hu
      obtain ⟨hreply, hstatus⟩ := hkeep hu
      exact ⟨(hframe.2 hu).trans hstatus, hframe.1.trans hreply⟩
    · intro sigma happ
      obtain ⟨other, otherMemory, hother, hstrict, hnextStart⟩ :=
        ReferenceFollowerReplyChronology.record_appliedDown_strict r i sigma happ next nextMemory hout
      have heq : other = choice := (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
        (hother.symm.trans hchoice)).1
      subst other
      have hsame : ReferencePrelaunchFollower.acceptedStart next =
          ReferencePrelaunchFollower.acceptedStart choice := by
        simp only [ReferencePrelaunchFollower.acceptedStart, hlast]
      omega
  · have hview : r.output.preparation.coordinator.downView = some selected.view := by
      change r.output.preparation.coordinator.selection.map
        ReferenceActivePhysicalStep.Selection.view = some selected.view
      rw [hs]
      rfl
    rw [hcall, hview] at haccepted
    have hfields := ReferenceActiveDataOwnership.referenceDown_accepted_fields
      selected.view _ _ _ _ _ _ _ _ _ _ _ _ haccepted
    rw [(r.output.preparation.follower_alignment i).2.1, hp] at hfields
    exact (hold ((congrArg Prod.fst hframe.1).trans hfields.2)).elim

private theorem old_choice_reply_of_actual_origins
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (P0 P : ReferenceActivePhysicalStep.Payload rate)
    (i : Fin (p.m - 1))
    (a k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).length)
    (hak : a.val ≤ k.val)
    (seed state : ReferencePrelaunchFollower.State p rate.eta)
    (seedMemory memory : ActiveFollowerLifecycle.LocalMemory p)
    (hseed : (ReferenceFollowerFixedReply.actualChoice
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[a.val] i).configuration =
      .ordinary seed seedMemory)
    (hu : seed.status = .unoccupied) (hdown : seed.lastDown = some (P0.downRecord i))
    (hstate : (ReferenceFollowerFixedReply.actualChoice
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val] i).configuration =
      .ordinary state memory)
    (hold : P = P0 ∨ state.lastDown ≠ some (P.downRecord i))
    (horigin : ∀ (j : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h).length), j.val < k.val → ∀ M,
      ReferenceAcceptedUpFollowerHistory.RetainedDown
        (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[j.val] i M →
        M = P0.downRecord i ∨ M = P.downRecord i) :
    state.status = .unoccupied ∧
    ReferenceFollowerReplyChronology.reply state = ReferenceFollowerReplyChronology.reply seed ∧
    (∀ (j : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).length),
      a.val ≤ j.val → j.val < k.val → ∀ sigma,
      ¬ ReferenceFollowerReplyChronology.appliedDown
        (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[j.val] i sigma) := by
  classical
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  have chain := ReferenceCompletePhysicalHistory.completeSuffix_connected_on_launch
    rate z rewards C_star C_h
    (ReferenceFirstLaunchNumericalCell.launchState rate z rewards C_star C_h hc)
    (ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
      rate z rewards C_star C_h hc)
  have hchrono := ReferenceFollowerReplyChronology.connected_choice_chronology chain i
    a.val k.val a.isLt k.isLt hak seed state seedMemory memory hseed hstate
  have hpositive : 0 < ReferencePrelaunchFollower.acceptedStart seed := by
    simp only [ReferencePrelaunchFollower.acceptedStart, hdown]
    rw [P0.downRecord_fields i]
    exact Nat.zero_lt_succ _
  obtain ⟨M, hlast⟩ : ∃ M, state.lastDown = some M := by
    cases hlast : state.lastDown with
    | some M => exact ⟨M, rfl⟩
    | none =>
        have hzero : ReferencePrelaunchFollower.acceptedStart state = 0 := by
          simp only [ReferencePrelaunchFollower.acceptedStart, hlast]
        have hm := hchrono.1
        omega
  obtain ⟨_birth, j, _payload, _base, _hbj, hjk, _hborn, _hbase, hretained, _hmessage,
      _hmass, _hdelta⟩ :=
    ReferenceCompleteOrdinaryFollowerMass.complete_ordinary_follower_choice_mass
      rewards C_star C_h z k i state memory hstate M hlast
  have hM : M = P0.downRecord i := by
    rcases horigin j hjk M hretained with hM | hM
    · exact hM
    · rcases hold with rfl | hold
      · exact hM
      · exact (hold (hlast.trans (congrArg some hM))).elim
  have hsame : ReferencePrelaunchFollower.acceptedStart seed =
      ReferencePrelaunchFollower.acceptedStart state := by
    simp only [ReferencePrelaunchFollower.acceptedStart, hdown, hlast, hM]
  obtain ⟨hstateU, hreply⟩ := hchrono.2.1 hu hsame
  refine ⟨hstateU, hreply, ?_⟩
  intro j haj hjk sigma happ
  obtain ⟨before, beforeMemory, hinput, hframe, _hbeforeU⟩ :=
    ReferenceFollowerReplyChronology.record_input_to_choice R[k.val] i state memory hstate
  have hprefix := ReferenceFollowerReplyChronology.connected_take_to_input chain k.val k.isLt
  obtain ⟨out, outMemory, hout, hbound⟩ :=
    ReferenceFollowerReplyChronology.connected_output_chronology hprefix i before beforeMemory
      hinput j.val (by rw [List.length_take]; exact lt_min hjk j.isLt)
  rw [List.getElem_take] at hout
  obtain ⟨choice, choiceMemory, hchoice, hstrict, houtStart⟩ :=
    ReferenceFollowerReplyChronology.record_appliedDown_strict R[j.val] i sigma happ out outMemory hout
  have hmono := (ReferenceFollowerReplyChronology.connected_choice_chronology chain i
    a.val j.val a.isLt j.isLt haj seed choice seedMemory choiceMemory hseed hchoice).1
  have hframeStart := ReferenceFollowerReplyChronology.acceptedStart_eq_of_reply_eq hframe
  omega

private theorem old_input_reply_of_actual_origins
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (P0 P : ReferenceActivePhysicalStep.Payload rate)
    (i : Fin (p.m - 1))
    (a k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).length)
    (hak : a.val < k.val)
    (seed state : ReferencePrelaunchFollower.State p rate.eta)
    (seedMemory memory : ActiveFollowerLifecycle.LocalMemory p)
    (hseed : (ReferenceFollowerFixedReply.actualChoice
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[a.val] i).configuration =
      .ordinary seed seedMemory)
    (hu : seed.status = .unoccupied) (hdown : seed.lastDown = some (P0.downRecord i))
    (hstate : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[k.val].input.state.followers i = .ordinary state memory)
    (hold : P = P0 ∨ state.lastDown ≠ some (P.downRecord i))
    (horigin : ∀ (j : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h).length), j.val < k.val → ∀ M,
      ReferenceAcceptedUpFollowerHistory.RetainedDown
        (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[j.val] i M →
        M = P0.downRecord i ∨ M = P.downRecord i) :
    state.status = .unoccupied ∧
    ReferenceFollowerReplyChronology.reply state = ReferenceFollowerReplyChronology.reply seed ∧
    (∀ (j : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).length),
      a.val ≤ j.val → j.val < k.val → ∀ sigma,
      ¬ ReferenceFollowerReplyChronology.appliedDown
        (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[j.val] i sigma) := by
  classical
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  have chain := ReferenceCompletePhysicalHistory.completeSuffix_connected_on_launch
    rate z rewards C_star C_h
    (ReferenceFirstLaunchNumericalCell.launchState rate z rewards C_star C_h hc)
    (ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
      rate z rewards C_star C_h hc)
  have hprefix := ReferenceFollowerReplyChronology.connected_take_to_input chain k.val k.isLt
  have haPrefix : a.val < (R.take k.val).length := by
    rw [List.length_take]; exact lt_min hak a.isLt
  obtain ⟨out, outMemory, hout, hbound⟩ :=
    ReferenceFollowerReplyChronology.connected_output_chronology hprefix i state memory hstate a.val haPrefix
  rw [List.getElem_take] at hout
  obtain ⟨choice, choiceMemory, hchoice, hleft, hleftKeep, _hleftApplied⟩ :=
    ReferenceFollowerReplyChronology.record_choice_chronology R[a.val] i out outMemory hout
  have hchoiceEq : choice = seed := (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
    (hchoice.symm.trans hseed)).1
  subst choice
  have htail := ReferenceFollowerReplyChronology.connected_drop_from_output hprefix a.val haPrefix
  obtain ⟨middle, middleMemory, hmiddle, hright, hrightKeep, _hrightApplied⟩ :=
    ReferenceFollowerReplyChronology.connected_ordinary_chronology htail i state memory hstate
  rw [List.getElem_take] at hmiddle
  have hmiddleEq : middle = out := (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
    (hmiddle.symm.trans hout)).1
  subst middle
  have hchrono : ReferencePrelaunchFollower.acceptedStart seed ≤ ReferencePrelaunchFollower.acceptedStart state ∧
      (seed.status = .unoccupied → ReferencePrelaunchFollower.acceptedStart seed =
        ReferencePrelaunchFollower.acceptedStart state → state.status = .unoccupied ∧
          ReferenceFollowerReplyChronology.reply state = ReferenceFollowerReplyChronology.reply seed) := by
    refine ⟨hleft.trans hright, ?_⟩
    intro hu heq
    obtain ⟨houtU, houtReply⟩ := hleftKeep hu (by omega)
    obtain ⟨hstateU, hstateReply⟩ := hrightKeep houtU (by omega)
    exact ⟨hstateU, hstateReply.trans houtReply⟩
  have hpositive : 0 < ReferencePrelaunchFollower.acceptedStart seed := by
    simp only [ReferencePrelaunchFollower.acceptedStart, hdown]
    rw [P0.downRecord_fields i]
    exact Nat.zero_lt_succ _
  obtain ⟨M, hlast⟩ : ∃ M, state.lastDown = some M := by
    cases hlast : state.lastDown with
    | some M => exact ⟨M, rfl⟩
    | none =>
        have hzero : ReferencePrelaunchFollower.acceptedStart state = 0 := by
          simp only [ReferencePrelaunchFollower.acceptedStart, hlast]
        have hm := hchrono.1
        omega
  obtain ⟨_birth, j, _payload, _base, _hbj, hjk, _hborn, _hbase, hretained, _hmessage,
      _hmass, _hdelta⟩ :=
    ReferenceCompleteOrdinaryFollowerMass.complete_ordinary_follower_input_mass
      rewards C_star C_h z k i state memory hstate M hlast
  have hM : M = P0.downRecord i := by
    rcases horigin j hjk M hretained with hM | hM
    · exact hM
    · rcases hold with rfl | hold
      · exact hM
      · exact (hold (hlast.trans (congrArg some hM))).elim
  have hsame : ReferencePrelaunchFollower.acceptedStart seed =
      ReferencePrelaunchFollower.acceptedStart state := by
    simp only [ReferencePrelaunchFollower.acceptedStart, hdown, hlast, hM]
  obtain ⟨hstateU, hreply⟩ := hchrono.2 hu hsame
  refine ⟨hstateU, hreply, ?_⟩
  intro j haj hjk sigma happ
  obtain ⟨out, outMemory, hout, hbound⟩ :=
    ReferenceFollowerReplyChronology.connected_output_chronology hprefix i state memory
      hstate j.val (by rw [List.length_take]; exact lt_min hjk j.isLt)
  rw [List.getElem_take] at hout
  obtain ⟨choice, choiceMemory, hchoice, hstrict, houtStart⟩ :=
    ReferenceFollowerReplyChronology.record_appliedDown_strict R[j.val] i sigma happ out outMemory hout
  have hmono := (ReferenceFollowerReplyChronology.connected_choice_chronology chain i
    a.val j.val a.isLt j.isLt haj seed choice seedMemory choiceMemory hseed hchoice).1
  omega

private theorem old_sites_reply_of_actual_origins
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (P0 P : ReferenceActivePhysicalStep.Payload rate)
    (i : Fin (p.m - 1))
    (a k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).length)
    (hak : a.val < k.val)
    (seed state : ReferencePrelaunchFollower.State p rate.eta)
    (seedMemory memory : ActiveFollowerLifecycle.LocalMemory p)
    (hseed : (ReferenceFollowerFixedReply.actualChoice
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[a.val] i).configuration =
      .ordinary seed seedMemory)
    (hu : seed.status = .unoccupied) (hdown : seed.lastDown = some (P0.downRecord i))
    (hsite :
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val].input.state.followers i =
        .ordinary state memory ∨
      (ReferenceFollowerFixedReply.actualChoice
        (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val] i).configuration =
        .ordinary state memory ∨
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val].output.next.followers i =
        .ordinary state memory)
    (hold : state.lastDown ≠ some (P.downRecord i))
    (hselected : (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val].output.next.followers i =
        .ordinary state memory → ∃ selected : ReferenceActivePhysicalStep.Selection
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val].input,
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val].output.preparation.coordinator.selection =
        some selected ∧ selected.view.payload = P)
    (horigin : ∀ (j : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h).length), j.val < k.val → ∀ M,
      ReferenceAcceptedUpFollowerHistory.RetainedDown
        (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[j.val] i M →
        M = P0.downRecord i ∨ M = P.downRecord i) :
    state.status = .unoccupied ∧ state.lastDown = some (P0.downRecord i) ∧
    ReferenceFollowerReplyChronology.reply state = ReferenceFollowerReplyChronology.reply seed ∧
    (∀ (j : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).length),
      a.val ≤ j.val → j.val < k.val → ∀ sigma,
      ¬ ReferenceFollowerReplyChronology.appliedDown
        (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[j.val] i sigma) ∧
    ((ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val].output.next.followers i =
      .ordinary state memory → ∀ sigma, ¬ ReferenceFollowerReplyChronology.appliedDown
        (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val] i sigma) := by
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  have houtputNo : R[k.val].output.next.followers i = .ordinary state memory → ∀ sigma,
      ¬ ReferenceFollowerReplyChronology.appliedDown R[k.val] i sigma := by
    intro hout
    obtain ⟨selected, hs, hp⟩ := hselected hout
    obtain ⟨_choice, _memory, _hchoice, _hlast, _hkeep, hno⟩ :=
      old_output_choice_frame R[k.val] P i selected hs hp state memory hout hold
    exact hno
  suffices state.status = .unoccupied ∧
      ReferenceFollowerReplyChronology.reply state = ReferenceFollowerReplyChronology.reply seed ∧
      (∀ j : Fin R.length, a.val ≤ j.val → j.val < k.val → ∀ sigma,
        ¬ ReferenceFollowerReplyChronology.appliedDown R[j.val] i sigma) by
    exact ⟨this.1, (congrArg Prod.fst this.2.1).trans hdown, this.2.1, this.2.2, houtputNo⟩
  rcases hsite with hin | hchoiceSite | hout
  · exact old_input_reply_of_actual_origins rate rewards C_star C_h z hc P0 P i a k hak
      seed state seedMemory memory hseed hu hdown hin (Or.inr hold) horigin
  · exact old_choice_reply_of_actual_origins rate rewards C_star C_h z hc P0 P i a k (Nat.le_of_lt hak)
      seed state seedMemory memory hseed hu hdown hchoiceSite (Or.inr hold) horigin
  · obtain ⟨selected, hs, hp⟩ := hselected hout
    obtain ⟨choice, choiceMemory, hchoice, hlast, hkeep, _hno⟩ :=
      old_output_choice_frame R[k.val] P i selected hs hp state memory hout hold
    have hchoiceOld : choice.lastDown ≠ some (P.downRecord i) := fun heq => hold (hlast.trans heq)
    obtain ⟨hchoiceU, hchoiceReply, hno⟩ := old_choice_reply_of_actual_origins
      rate rewards C_star C_h z hc P0 P i a k (Nat.le_of_lt hak)
      seed choice seedMemory choiceMemory hseed hu hdown hchoice (Or.inr hchoiceOld) horigin
    obtain ⟨hstateU, hreply⟩ := hkeep hchoiceU
    exact ⟨hstateU, hreply.trans hchoiceReply, hno⟩

private theorem live_prefix_inherited_choice
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : z ∈ ReferenceFirstCollectionCorrectedSliceNumericalPrefix.correctedCell
      rate rewards C_star C_h u t)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (birth0 birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (P0 P : ReferenceActivePhysicalStep.Payload rate)
    (hbirth0Lookup : (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[0]? = some birth0)
    (hbirth0Install : ReferenceAssignmentPayloadPersistence.InstallationBirth birth0 P0)
    (hbirthLookup : (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex rate rewards C_star C_h z]? = some birth)
    (hbirthInstall : ReferenceAssignmentPayloadPersistence.InstallationBirth birth P)
    (a : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).length)
    (ha : a.val < ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex rate rewards C_star C_h z)
    (i : Fin (p.m - 1)) (seed : ReferencePrelaunchFollower.State p rate.eta)
    (seedMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hseed : (ReferenceFollowerFixedReply.actualChoice
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[a.val] i).configuration =
      .ordinary seed seedMemory)
    (hu : seed.status = .unoccupied) (hdown : seed.lastDown = some (P0.downRecord i)) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let b := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex rate rewards C_star C_h z
    let W := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail rate rewards C_star C_h z
    let V := (R.drop b).take (1 + W.length)
    ∀ (j : ℕ) (hj : j < V.length)
      (stored : ReferencePrelaunchFollower.State p rate.eta)
      (storedMemory : ActiveFollowerLifecycle.LocalMemory p),
      (V[j].input.state.followers i = .ordinary stored storedMemory ∨
        (ReferenceFollowerFixedReply.actualChoice V[j] i).configuration = .ordinary stored storedMemory ∨
        V[j].output.next.followers i = .ordinary stored storedMemory) →
      stored.lastDown ≠ some (P.downRecord i) →
      stored.status = .unoccupied ∧ stored.lastDown = some (P0.downRecord i) ∧
      ReferenceFollowerReplyChronology.reply stored = ReferenceFollowerReplyChronology.reply seed ∧
      (∀ (q : Fin R.length), a.val ≤ q.val → q.val < b + j → ∀ sigma,
        ¬ ReferenceFollowerReplyChronology.appliedDown R[q.val] i sigma) ∧
      (V[j].output.next.followers i = .ordinary stored storedMemory → ∀ sigma,
        ¬ ReferenceFollowerReplyChronology.appliedDown V[j] i sigma) := by
  classical
  intro R b W V
  obtain ⟨_L, _c, birth', P', _base, _hpast, _hcurrent, _hprefix, _hLlen,
    hb', hborn', _hPsigma, _hPqueues, _hbase, hV, _hVbound,
    _hterminal, hVfields, _hremaining⟩ :=
    ReferenceFirstCorrectedCurrentCutoffReplyRetention.actual_first_corrected_current_cutoff_reply_retention
      rate rewards C_star C_h u t z hz
  have hbirthEq : birth' = birth := Option.some.inj (hb'.symm.trans hbirthLookup)
  have hP' : P' = P := ReferenceAssignmentPayloadChronology.installationBirth_payload_unique
    birth P' P (hbirthEq ▸ hborn') hbirthInstall
  subst P'
  have hV' : V = birth' :: W := hV
  have hwordBound : V.length ≤ 1 + W.length := by rw [hV']; simp only [List.length_cons]; omega
  obtain ⟨word, hword, _hunique⟩ := _hremaining.2.1 i V.length hwordBound
  change (V.take V.length).mapM
    (ReferenceFirstCorrectedAssignedArrivalPrefix.attributedArrival? P i) = some word at hword
  rw [List.take_length] at hword
  have hselection : ∀ (q : ℕ) (hq : q < V.length), ∃ selected : ReferenceActivePhysicalStep.Selection V[q].input,
      V[q].output.preparation.coordinator.selection = some selected ∧ selected.view.payload = P := by
    intro q hq
    obtain ⟨value, hvalue⟩ := mapM_some_at
      (ReferenceFirstCorrectedAssignedArrivalPrefix.attributedArrival? P i) V word hword
      q V[q] (List.getElem?_eq_getElem hq)
    exact attributedArrival_selected P i V[q] value hvalue
  intro j hj stored storedMemory hsite hold
  obtain ⟨_in, _im, _ch, _out, _om, hsiteLookup, _hsiteRest⟩ := hVfields i j hj
  change R[b + j]? = some V[j] at hsiteLookup
  have hjR : b + j < R.length := (List.getElem?_eq_some_iff.mp hsiteLookup).1
  have hsame : R[b + j] = V[j] := (List.getElem?_eq_some_iff.mp hsiteLookup).2
  rw [← hsame] at hsite
  have horigins : ∀ (q : Fin R.length), q.val < b + j → ∀ M,
      ReferenceAcceptedUpFollowerHistory.RetainedDown R[q.val] i M →
      M = P0.downRecord i ∨ M = P.downRecord i := by
    intro q hq M hM
    by_cases hqb : q.val < b
    · exact Or.inl (retained_before_replacement_origin rate rewards C_star C_h u t z hz
        birth0 P0 hbirth0Lookup hbirth0Install q hqb i M hM)
    · have hf : q.val - b < V.length := by omega
      obtain ⟨_in, _im, _ch, _out, _om, hqLookup, _hrest⟩ := hVfields i (q.val - b) hf
      change R[b + (q.val - b)]? = some V[q.val - b] at hqLookup
      have hsum : b + (q.val - b) = q.val := by omega
      rw [hsum] at hqLookup
      have hsame : R[q.val] = V[q.val - b] := (List.getElem?_eq_some_iff.mp hqLookup).2
      obtain ⟨selected, hs, hp⟩ : ∃ selected : ReferenceActivePhysicalStep.Selection R[q.val].input,
          R[q.val].output.preparation.coordinator.selection = some selected ∧ selected.view.payload = P := by
        rw [hsame]
        exact hselection (q.val - b) hf
      exact Or.inr (retainedDown_selected_record R[q.val] P i M hM selected hs hp)
  change (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[b + j] = V[j] at hsame
  have hresult := old_sites_reply_of_actual_origins rate rewards C_star C_h z hc P0 P i
    a ⟨b + j, hjR⟩ (by change a.val < b + j; omega) seed stored seedMemory storedMemory
    hseed hu hdown hsite hold (fun _ => by rw [hsame]; exact hselection j hj) horigins
  rw [← hsame]
  exact hresult

private theorem collection_inherited_sites
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : z ∈ ReferenceFirstCollectionCorrectedSliceNumericalPrefix.correctedCell
      rate rewards C_star C_h u t)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (birth0 birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (P0 P : ReferenceActivePhysicalStep.Payload rate)
    (hbirth0Lookup : (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[0]? = some birth0)
    (hbirth0Install : ReferenceAssignmentPayloadPersistence.InstallationBirth birth0 P0)
    (hbirthLookup : (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex rate rewards C_star C_h z]? = some birth)
    (hbirthInstall : ReferenceAssignmentPayloadPersistence.InstallationBirth birth P)
    (a : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).length)
    (ha : a.val < ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex rate rewards C_star C_h z)
    (i : Fin (p.m - 1)) (seed : ReferencePrelaunchFollower.State p rate.eta)
    (seedMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hseed : (ReferenceFollowerFixedReply.actualChoice
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[a.val] i).configuration =
      .ordinary seed seedMemory)
    (hu : seed.status = .unoccupied) (hdown : seed.lastDown = some (P0.downRecord i)) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let b := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex rate rewards C_star C_h z
    let W := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail rate rewards C_star C_h z
    let e := b + (1 + W.length)
    e = R.length ∨ ∃ (he : e < R.length) (seg : ReferenceCollectionSegmentExtraction.Segment rate),
    ReferenceCollectionSegmentExtraction.segmentAt R e = some seg ∧
    seg.entry = R[e] ∧ seg.context.payload = P ∧
    seg.records ++ seg.remaining = R.drop e ∧
    ∀ (q : Fin R.length), e ≤ q.val → q.val ≤ e + seg.records.length →
    ∀ (stored : ReferencePrelaunchFollower.State p rate.eta)
      (storedMemory : ActiveFollowerLifecycle.LocalMemory p),
    (R[q.val].input.state.followers i = .ordinary stored storedMemory ∨
      (ReferenceFollowerFixedReply.actualChoice R[q.val] i).configuration = .ordinary stored storedMemory ∨
      (q.val < e + seg.records.length ∧ R[q.val].output.next.followers i = .ordinary stored storedMemory)) →
    stored.lastDown ≠ some (P.downRecord i) →
    stored.status = .unoccupied ∧ stored.lastDown = some (P0.downRecord i) ∧
    ReferenceFollowerReplyChronology.reply stored = ReferenceFollowerReplyChronology.reply seed ∧
    (∀ (j : Fin R.length), a.val ≤ j.val → j.val < q.val → ∀ sigma,
      ¬ ReferenceFollowerReplyChronology.appliedDown R[j.val] i sigma) ∧
    (q.val < e + seg.records.length → R[q.val].output.next.followers i = .ordinary stored storedMemory →
      ∀ sigma, ¬ ReferenceFollowerReplyChronology.appliedDown R[q.val] i sigma) := by
  classical
  intro R b W e
  let V := (R.drop b).take (1 + W.length)
  obtain ⟨_L, _c, birth', P', _base, _hpast, _hcurrent, _hprefix, _hLlen,
    hb', hborn', _hPsigma, _hPqueues, _hbase, hV, _hVbound,
    _hterminal, hVfields, _hremaining⟩ :=
    ReferenceFirstCorrectedCurrentCutoffReplyRetention.actual_first_corrected_current_cutoff_reply_retention
      rate rewards C_star C_h u t z hz
  have hbirthEq : birth' = birth := Option.some.inj (hb'.symm.trans hbirthLookup)
  have hP' : P' = P := ReferenceAssignmentPayloadChronology.installationBirth_payload_unique
    birth P' P (hbirthEq ▸ hborn') hbirthInstall
  subst P'
  have hV' : V = birth' :: W := hV
  rcases _hremaining.2.2 with hend | ⟨he, seg, hseg, hentry, hpayload, hpartition,
    _hcutoff, hsegSelected, _hrest⟩
  · exact Or.inl hend
  · refine Or.inr ⟨he, seg, hseg, hentry, hpayload, hpartition, ?_⟩
    have hVlength : V.length = 1 + W.length := by rw [hV']; simp only [List.length_cons]; omega
    obtain ⟨word, hword, _hunique⟩ := _hremaining.2.1 i V.length (Nat.le_of_eq hVlength)
    change (V.take V.length).mapM
      (ReferenceFirstCorrectedAssignedArrivalPrefix.attributedArrival? P i) = some word at hword
    rw [List.take_length] at hword
    have hmember : ∀ (q : Fin R.length), e ≤ q.val → q.val < e + seg.records.length →
        R[q.val] ∈ seg.records := by
      intro q hqe hqend
      have hn : q.val - e < seg.records.length := by omega
      have hget : (seg.records ++ seg.remaining)[q.val - e]? = some R[q.val] := by
        rw [hpartition, List.getElem?_drop, Nat.add_sub_of_le hqe, List.getElem?_eq_getElem q.isLt]
      rw [List.getElem?_append_left hn] at hget
      rw [← (List.getElem?_eq_some_iff.mp hget).2]
      exact List.getElem_mem hn
    have hselected : ∀ (q : Fin R.length), b ≤ q.val → q.val < e + seg.records.length →
        ∃ selected : ReferenceActivePhysicalStep.Selection R[q.val].input,
          R[q.val].output.preparation.coordinator.selection = some selected ∧ selected.view.payload = P := by
      intro q hqb hqend
      by_cases hqe : e ≤ q.val
      · exact hsegSelected R[q.val] (hmember q hqe hqend)
      · have hv : q.val - b < V.length := by omega
        obtain ⟨_in, _im, _ch, _out, _om, hlookup, _hrest⟩ := hVfields i (q.val - b) hv
        change R[b + (q.val - b)]? = some V[q.val - b] at hlookup
        have hsum : b + (q.val - b) = q.val := by omega
        rw [hsum] at hlookup
        have hget : V[q.val - b]? = some R[q.val] := by
          rw [List.getElem?_eq_getElem hv, ← (List.getElem?_eq_some_iff.mp hlookup).2]
        obtain ⟨value, hvalue⟩ := mapM_some_at
          (ReferenceFirstCorrectedAssignedArrivalPrefix.attributedArrival? P i) V word hword
          (q.val - b) R[q.val] hget
        exact attributedArrival_selected P i R[q.val] value hvalue
    intro q hqe hqend stored storedMemory hsite hold
    have horigins : ∀ (j : Fin R.length), j.val < q.val → ∀ down,
        ReferenceAcceptedUpFollowerHistory.RetainedDown R[j.val] i down →
        down = P0.downRecord i ∨ down = P.downRecord i := by
      intro j hj down hdown
      by_cases hjb : j.val < b
      · exact Or.inl (retained_before_replacement_origin rate rewards C_star C_h u t z hz
          birth0 P0 hbirth0Lookup hbirth0Install j hjb i down hdown)
      · obtain ⟨selected, hs, hp⟩ := hselected j (by omega) (by omega)
        exact Or.inr (retainedDown_selected_record R[j.val] P i down hdown selected hs hp)
    have houtputNo : q.val < e + seg.records.length →
        R[q.val].output.next.followers i = .ordinary stored storedMemory → ∀ sigma,
          ¬ ReferenceFollowerReplyChronology.appliedDown R[q.val] i sigma := by
      intro hq hout
      obtain ⟨selected, hs, hp⟩ := hselected q (by omega) hq
      obtain ⟨_choice, _cm, _hc, _hdown, _hkeep, hno⟩ :=
        old_output_choice_frame R[q.val] P i selected hs hp stored storedMemory hout hold
      exact hno
    suffices stored.status = .unoccupied ∧
        ReferenceFollowerReplyChronology.reply stored = ReferenceFollowerReplyChronology.reply seed ∧
        (∀ j : Fin R.length, a.val ≤ j.val → j.val < q.val → ∀ sigma,
          ¬ ReferenceFollowerReplyChronology.appliedDown R[j.val] i sigma) by
      exact ⟨this.1, (congrArg Prod.fst this.2.1).trans hdown, this.2.1, this.2.2, houtputNo⟩
    rcases hsite with hin | hcSite | ⟨hq, hout⟩
    · exact old_input_reply_of_actual_origins rate rewards C_star C_h z hc P0 P i
        a q (by change a.val < q.val; omega) seed stored seedMemory storedMemory
        hseed hu hdown hin (Or.inr hold) horigins
    · exact old_choice_reply_of_actual_origins rate rewards C_star C_h z hc P0 P i
        a q (by change a.val ≤ q.val; omega) seed stored seedMemory storedMemory
        hseed hu hdown hcSite (Or.inr hold) horigins
    · have hretained := old_sites_reply_of_actual_origins rate rewards C_star C_h z hc P0 P i
        a q (by change a.val < q.val; omega) seed stored seedMemory storedMemory
        hseed hu hdown (Or.inr (Or.inr hout)) hold (fun _ => hselected q (by omega) hq) horigins
      exact ⟨hretained.1, hretained.2.2.1, hretained.2.2.2.1⟩

/-- The original FIRST payload and canonical source word are shared by all
actual earlier accepted replies. Each terminal UP queue is distinguished from
the zero initial DOWN queue. No delivery, receiver certificate, or replay
identity is an additional root input. Birth INPUT/CHOICE and all three ordinary
sites in the current live word retain this OLD reply until CURRENT DOWN. The
same collection and its first excluded INPUT/CHOICE boundary retain them too;
the boundary OUTPUT may install a newer payload and is excluded. -/
theorem actual_prior_first_collection_canonical_replies
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : z ∈ ReferenceFirstCollectionCorrectedSliceNumericalPrefix.correctedCell
      rate rewards C_star C_h u t) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    let b := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex
      rate rewards C_star C_h z
    let W := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail rate rewards C_star C_h z
    let V := (R.drop b).take (1 + W.length)
    let e := b + (1 + W.length)
    ∃ (hc : (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
      (hspan : ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed +
          (p.T - s) ≤ p.T),
      let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate z rewards C_star C_h hc (p.T - s) hspan
      let L0 := ReferenceFirstWindowNumericalStream.actualLiveSourceCells
        rate z rewards C_star C_h hc (p.T - s) hspan
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length < p.T - s ∧
      (R.take L0.length).map (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate) = L0.map some ∧
      ∃ (currentBirth originalBirth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
        (P P0 : ReferenceActivePhysicalStep.Payload rate),
        R[b]? = some currentBirth ∧
        ReferenceAssignmentPayloadPersistence.InstallationBirth currentBirth P ∧ P.sigma = t ∧
        R[0]? = some originalBirth ∧
        ReferenceAssignmentPayloadPersistence.InstallationBirth originalBirth P0 ∧
        originalBirth.input.time.val = s ∧ P0.sigma.val = s ∧
        (∃ installed selection,
          originalBirth.output.preparation.coordinator = .first (.chosen installed selection) ∧
          installed.registers.payload = P0) ∧
        (∀ a, P0.queues a = 0) ∧
        ∀ i : Fin (p.m - 1),
        ∃ (k : ℕ) (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
          (M : ReferenceCollectionPhaseHistory.UpRecord p rate)
          (state : ReferencePrelaunchFollower.State p rate.eta)
          (memory : ActiveFollowerLifecycle.LocalMemory p),
          (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length ≤ k ∧ k < b ∧
          R[k]? = some r ∧ ReferenceCollectionPhaseHistory.AcceptedUp r.input i M ∧
          (ReferenceFollowerFixedReply.actualChoice r i).configuration = .ordinary state memory ∧
          state.status = .unoccupied ∧ state.lastDown = some (P0.downRecord i) ∧
          M.val.sigma = P0.sigma.val + 1 ∧
          M.val.S = state.S ∧ M.val.delta = state.delta ∧ M.val.q = state.backlog ∧
          (P0.downRecord i).val.q = 0 ∧
          M.val.S = (UnstoppedRecordedQueueComparison.unstoppedReplay
            (ReferenceFirstLaunchNumericalCell.queueParameters rate) L0 L0.length
            (P0.assignment.assigned i)).1 ∧
          M.val.q = (UnstoppedRecordedQueueComparison.unstoppedReplay
            (ReferenceFirstLaunchNumericalCell.queueParameters rate) L0 L0.length
            (P0.assignment.assigned i)).2 ∧
          M.val.delta =
            (UnstoppedRecordedQueueComparison.unstoppedReplay
              (ReferenceFirstLaunchNumericalCell.queueParameters rate) L0 L0.length
              (P0.assignment.assigned i)).1 -
            (UnstoppedRecordedQueueComparison.unstoppedReplay
              (ReferenceFirstLaunchNumericalCell.queueParameters rate) L0 (L0.length - 1)
              (P0.assignment.assigned i)).1 ∧
          ∃ (input : ReferencePrelaunchFollower.State p rate.eta)
            (inputMemory : ActiveFollowerLifecycle.LocalMemory p)
            (choice : ReferencePrelaunchFollower.State p rate.eta),
            currentBirth.input.state.followers i = .ordinary input inputMemory ∧
            input.status = .unoccupied ∧ input.lastDown = some (P0.downRecord i) ∧
            ReferenceFollowerReplyChronology.reply input = ReferenceFollowerReplyChronology.reply state ∧
            ActiveFollowerLifecycle.startRound rate.eta currentBirth.input.time input inputMemory =
              .ok (choice, inputMemory) ∧
            (ReferenceFollowerFixedReply.actualChoice currentBirth i).configuration =
              .ordinary choice inputMemory ∧
            choice.status = .unoccupied ∧
            ReferenceFollowerReplyChronology.reply choice = ReferenceFollowerReplyChronology.reply state ∧
            (∀ (j : Fin R.length), k ≤ j.val → j.val < b → ∀ sigma,
              ¬ ReferenceFollowerReplyChronology.appliedDown R[j.val] i sigma) ∧
            (∀ (j : ℕ) (hj : j < V.length)
              (stored : ReferencePrelaunchFollower.State p rate.eta)
              (storedMemory : ActiveFollowerLifecycle.LocalMemory p),
              let physical := V[j]
              (physical.input.state.followers i = .ordinary stored storedMemory ∨
                (ReferenceFollowerFixedReply.actualChoice physical i).configuration = .ordinary stored storedMemory ∨
                physical.output.next.followers i = .ordinary stored storedMemory) →
              stored.lastDown ≠ some (P.downRecord i) →
              stored.status = .unoccupied ∧ stored.lastDown = some (P0.downRecord i) ∧
              ReferenceFollowerReplyChronology.reply stored = ReferenceFollowerReplyChronology.reply state ∧
              (∀ (q : Fin R.length), k ≤ q.val → q.val < b + j → ∀ sigma,
                ¬ ReferenceFollowerReplyChronology.appliedDown R[q.val] i sigma) ∧
              (physical.output.next.followers i = .ordinary stored storedMemory → ∀ sigma,
                ¬ ReferenceFollowerReplyChronology.appliedDown physical i sigma)) ∧
            (∀ cutoff, R[e]? = some cutoff → ∃ endpoint endpointMemory,
              cutoff.input.state.followers i = .ordinary endpoint endpointMemory ∧
              (ReferenceFollowerFixedReply.actualChoice cutoff i).configuration =
                .ordinary {endpoint with status := .unoccupied} endpointMemory ∧
              (endpoint.lastDown ≠ some (P.downRecord i) →
                endpoint.status = .unoccupied ∧ endpoint.lastDown = some (P0.downRecord i) ∧
                ReferenceFollowerReplyChronology.reply endpoint = ReferenceFollowerReplyChronology.reply state)) ∧
            (e = R.length ∨ ∃ (he : e < R.length) (seg : ReferenceCollectionSegmentExtraction.Segment rate),
              ReferenceCollectionSegmentExtraction.segmentAt R e = some seg ∧
              seg.entry = R[e] ∧ seg.context.payload = P ∧
              seg.records ++ seg.remaining = R.drop e ∧
              ∀ (q : Fin R.length), e ≤ q.val → q.val ≤ e + seg.records.length →
              ∀ (stored : ReferencePrelaunchFollower.State p rate.eta)
                (storedMemory : ActiveFollowerLifecycle.LocalMemory p),
              (R[q.val].input.state.followers i = .ordinary stored storedMemory ∨
                (ReferenceFollowerFixedReply.actualChoice R[q.val] i).configuration = .ordinary stored storedMemory ∨
                (q.val < e + seg.records.length ∧ R[q.val].output.next.followers i = .ordinary stored storedMemory)) →
              stored.lastDown ≠ some (P.downRecord i) →
              stored.status = .unoccupied ∧ stored.lastDown = some (P0.downRecord i) ∧
              ReferenceFollowerReplyChronology.reply stored = ReferenceFollowerReplyChronology.reply state ∧
              (∀ (j : Fin R.length), k ≤ j.val → j.val < q.val → ∀ sigma,
                ¬ ReferenceFollowerReplyChronology.appliedDown R[j.val] i sigma) ∧
              (q.val < e + seg.records.length → R[q.val].output.next.followers i = .ordinary stored storedMemory →
                ∀ sigma, ¬ ReferenceFollowerReplyChronology.appliedDown R[q.val] i sigma)) := by
  classical
  intro R s b W V e
  obtain ⟨hc, hspan, hshort, L0, hL0, hsource⟩ :=
    actual_first_live_source_prefix rate rewards C_star C_h u t z hz
  subst L0
  let count := p.T - s
  let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
    rate z rewards C_star C_h hc count hspan
  let L0 := ReferenceFirstWindowNumericalStream.actualLiveSourceCells
    rate z rewards C_star C_h hc count hspan
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length
  let B := ReferenceCollectionPhaseHistory.collectionWindow E.records w
  have hrecords : R = E.records := by
    exact ReferenceCompleteFirstPhaseObservationRecovery.completeSuffixRecords_eq_actualFirstLiveRun
      rate rewards C_star C_h z hc
  have hwR : w = (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length := by
    rw [hrecords]
  have hb : b = w + B.length := by
    change _ + _ = _
    simp only [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords, R, hrecords, w, B]
  have hOrigin := ReferenceFirstCollectionDownPayloadOrigin.actual_first_collection_down_payload_origin
    rate z rewards C_star C_h count hc hspan hshort
  obtain ⟨cut, P0, birth0, registers, owned, base, _hcutIndex, _hcutUnique,
    _hcutState, _hcutoff, _hP0, hP0sigma, hqueues, _hfirstCutoff,
    hbirth0Member, hbirth0Install, hbirth0Time, hbirth0First, _hwindow,
    _hselected, _hretained, _hprior⟩ := hOrigin.origin
  have hbirth0Lookup : R[0]? = some birth0 := by
    obtain ⟨n, hn, hget⟩ := List.mem_iff_getElem.mp hbirth0Member
    have hlookup : R[n]? = some birth0 := by
      rw [hrecords, List.getElem?_eq_getElem hn, hget]
    have htime := ReferenceFirstCollectionRenewalRecordingFeedback.complete_record_time
      rate z rewards C_star C_h n birth0 hlookup
    have hnzero : n = 0 := by omega
    simpa only [hnzero] using hlookup
  have hbirthUnique : ∀ birth,
      birth ∈ E.records → birth.input.time.val = s → birth = birth0 := by
    intro birth hmem htime
    apply ReferenceAssignmentPayloadChronology.run_records_time_injective
      (ReferenceFirstCollectionEpochAlignment.actualLaunchState rate z rewards C_star C_h hc)
      z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards
      (ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed)
      count hspan
      (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
        rate z rewards C_star C_h hc).1 hmem hbirth0Member
    exact htime.trans hbirth0Time.symm
  have hretention := ReferenceFirstCorrectedCurrentCutoffReplyRetention.actual_first_corrected_current_cutoff_reply_retention
    rate rewards C_star C_h u t z hz
  dsimp only at hretention
  obtain ⟨_L, _c, birth, P, _base, _hpast, _hcurrent, _hprefix, _hLlen,
    hbirthLookup, hbirthInstall, hPsigma, _hPqueues, _hbase,
    hV, _hVbound, _hterminal, hVfields, _hremaining⟩ := hretention
  refine ⟨hc, hspan, hshort, hsource, birth, birth0, P, P0,
    hbirthLookup, hbirthInstall, hPsigma,
    hbirth0Lookup, hbirth0Install, hbirth0Time, hP0sigma, hbirth0First, hqueues, ?_⟩
  intro i
  obtain ⟨_birth, _P, _hb, _hborn, _hsigma, k, r, M, sender, state, memory, prior,
    hwk, hkb, hr, haccepted, hsender, hconfiguration, hu, hS, hd, hq, _hlast, _hpriorSigma⟩ :=
    actual_prior_first_collection_accepted_up_in_window rate rewards C_star C_h u t z hz i
  have hwk' : w ≤ k := by rw [hwR]; exact hwk
  have hnk : k - w < B.length := by omega
  let n : Fin B.length := ⟨k - w, hnk⟩
  have hwr : B[n] = r := by
    have hpref := collectionWindow_prefix E.records w
    have hget := List.prefix_iff_getElem?.mp hpref n.val n.isLt
    have hsum : w + n.val = k := by dsimp only [n]; omega
    have hlookup : E.records[k]? = some r := by rw [← hrecords]; exact hr
    rw [List.getElem?_drop, hsum, hlookup] at hget
    exact Option.some.inj hget.symm
  obtain ⟨c, hcChoice, hi, hparse, haccept⟩ := acceptedUp_choice_receipt r i M haccepted
  have hcB : ReferenceCollectionSegmentExtraction.choice B[n].input = some c := by
    rw [hwr]
    exact hcChoice
  have hparseB : ReferenceCollectionSegmentExtraction.effectiveParse B[n].input
      (CoordinatorCollectionLedger.startRoundCandidate c.preLedger B[n].input.time
        (ReferenceActivePhysicalStep.collectionEnabled c.preLedger B[n].input.time)
        (ReferenceCollectionRawBufferHistory.rawDiagnostic B[n])) = some M := by
    rw [hwr]
    exact hparse
  have hacceptB : CoordinatorCollectionLedger.acceptUpCheck
      (CoordinatorCollectionLedger.startRoundCandidate c.preLedger B[n].input.time
        (ReferenceActivePhysicalStep.collectionEnabled c.preLedger B[n].input.time)
        (ReferenceCollectionRawBufferHistory.rawDiagnostic B[n]))
      (ReferenceActivePhysicalStep.upSenderIndex B[n].input) M = true := by
    rw [hwr, ← hi]
    exact haccept
  have hcanonical :=
    ReferenceFirstCollectionParsedUpCanonicalCutoff.actual_first_collection_parsed_up_canonical_cutoff
      rate z rewards C_star C_h count hc hspan hshort n c hcB M hparseB hacceptB
  obtain ⟨Pc, bc, _d, down, hcMember, hcBorn, hcTime, hcPayload, hdown,
    hdownZero, _hdownRetained, _hdownBefore, hMsigma, hMS, hMq, hMd⟩ := hcanonical
  have hbc : bc = birth0 := hbirthUnique bc hcMember hcTime
  subst bc
  have hPc : Pc = P0 := ReferenceAssignmentPayloadChronology.installationBirth_payload_unique
    birth0 Pc P0 hcBorn hbirth0Install
  have hcPayload0 : c.payload = P0 := hcPayload.symm.trans hPc
  have hbudget :=
    ReferenceFirstCollectionParsedUpBudgets.actual_first_collection_parsed_up_budget_calendar_replay_join
      rate z rewards C_star C_h count hc hspan hshort n c hcB M hparseB hacceptB
  obtain ⟨Pb, bb, sb, mb, _offered, _j, downb, _hinit, _hlSigma, _hlCut,
    hassign, _hvalid, _hpending, _hunknown, _hcutUnknown, _hplusSigma, _hplusCut,
    _hPbSigma, _hPbQueues, hbMember, hbBorn, hbTime, hbConfiguration,
    _hoffer, _hofferEq, _hword, hbLast, _hrest⟩ := hbudget
  have hbb : bb = birth0 := hbirthUnique bb hbMember hbTime
  subst bb
  have hPb : Pb = P0 := ReferenceAssignmentPayloadChronology.installationBirth_payload_unique
    birth0 Pb P0 hbBorn hbirth0Install
  have hdownb : downb = Pb.downRecord (ReferenceActivePhysicalStep.upSenderIndex B[n].input) :=
    _hrest.2.2.2.1
  have hsenderActual : sender = ReferenceFollowerFixedReply.actualChoice r i := by
    unfold ReferenceFollowerFixedReply.actualChoice
    rw [r.output_eq]
    simpa only [ReferenceActivePhysicalStep.step, hi] using hsender
  have hsActual : (ReferenceFollowerFixedReply.actualChoice r i).configuration =
      .ordinary state memory := by rw [← hsenderActual]; exact hconfiguration
  change (ReferenceFollowerFixedReply.actualChoice B[n]
    (ReferenceActivePhysicalStep.upSenderIndex B[n].input)).configuration = .ordinary sb mb
    at hbConfiguration
  have hbConfiguration' : (ReferenceFollowerFixedReply.actualChoice r i).configuration =
      .ordinary sb mb := by
    rw [hwr, ← hi] at hbConfiguration
    exact hbConfiguration
  obtain ⟨hstates, hmemories⟩ := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
    (hsActual.symm.trans hbConfiguration')
  subst sb
  subst mb
  have hlast : state.lastDown = some (P0.downRecord i) := by
    simpa only [hdownb, hPb, hwr, ← hi] using hbLast
  have harm : c.preLedger.assignment.arm (ReferenceActivePhysicalStep.upSenderIndex B[n].input) =
      P0.assignment.assigned i := by rw [hassign, hcPayload0, hwr, ← hi]
  have hlength : L0.length = w :=
    ReferenceFirstWindowNumericalStream.actualLiveSourceCells_length
      rate z rewards C_star C_h hc count hspan
  have hreplay : ∀ h, QueueReplay.replay (4 * rate.n) (0, 0)
      ((L0.take h).map fun cell => (cell.enabled,
        RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate)
          cell (P0.assignment.assigned i))) =
      UnstoppedRecordedQueueComparison.unstoppedReplay
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) L0 h (P0.assignment.assigned i) := by
    intro h
    exact replay_eq_unstopped rate (L0.take h) (P0.assignment.assigned i) (0, 0)
  change M.val.S = (QueueReplay.replay (4 * rate.n) (0, 0)
    ((L0.take w).map fun cell => (cell.enabled,
      RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        cell (c.preLedger.assignment.arm
          (ReferenceActivePhysicalStep.upSenderIndex B[n].input))))).1 at hMS
  change M.val.q = (QueueReplay.replay (4 * rate.n) (0, 0)
    ((L0.take w).map fun cell => (cell.enabled,
      RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        cell (c.preLedger.assignment.arm
          (ReferenceActivePhysicalStep.upSenderIndex B[n].input))))).2 at hMq
  change M.val.delta = (QueueReplay.replay (4 * rate.n) (0, 0)
    ((L0.take w).map fun cell => (cell.enabled,
      RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        cell (c.preLedger.assignment.arm
          (ReferenceActivePhysicalStep.upSenderIndex B[n].input))))).1 -
    (QueueReplay.replay (4 * rate.n) (0, 0)
    ((L0.take (w - 1)).map fun cell => (cell.enabled,
      RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        cell (c.preLedger.assignment.arm
          (ReferenceActivePhysicalStep.upSenderIndex B[n].input))))).1 at hMd
  rw [harm, hreplay] at hMS hMq
  rw [harm, hreplay, hreplay] at hMd
  refine ⟨k, r, M, state, memory, hwk, hkb, hr, haccepted, hsActual,
    hu, hlast, ?_, hS, hd, hq, ?_, ?_, ?_, ?_, ?_⟩
  · exact hMsigma.trans (congrArg (· + 1) hP0sigma.symm)
  · change down = Pc.downRecord (ReferenceActivePhysicalStep.upSenderIndex B[n].input) at hdown
    rw [hdown, hPc, hwr, ← hi] at hdownZero
    exact hdownZero
  · change M.val.S = (UnstoppedRecordedQueueComparison.unstoppedReplay
      (ReferenceFirstLaunchNumericalCell.queueParameters rate) L0 L0.length
      (P0.assignment.assigned i)).1
    rw [hlength]
    exact hMS
  · change M.val.q = (UnstoppedRecordedQueueComparison.unstoppedReplay
      (ReferenceFirstLaunchNumericalCell.queueParameters rate) L0 L0.length
      (P0.assignment.assigned i)).2
    rw [hlength]
    exact hMq
  · change M.val.delta =
      (UnstoppedRecordedQueueComparison.unstoppedReplay
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) L0 L0.length
        (P0.assignment.assigned i)).1 -
      (UnstoppedRecordedQueueComparison.unstoppedReplay
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) L0 (L0.length - 1)
        (P0.assignment.assigned i)).1
    rw [hlength]
    exact hMd
  · have hV' : V = birth :: W := hV
    have hpos : 0 < V.length := by rw [hV']; simp only [List.length_cons]; omega
    have hV0 : V[0] = birth := by
      have hlookup : V[0]? = some birth := by rw [hV']; rfl
      exact (List.getElem?_eq_some_iff.mp hlookup).2
    obtain ⟨input, inputMemory, choice, _next, _nextMemory, _hindex, hinput,
      hstart, hchoice, _hnext, _hfailure, _hnextState, hinputU, _hinputBusy,
      _hnextBusy, _hadj⟩ := hVfields i 0 hpos
    change V[0].input.state.followers i = .ordinary input inputMemory at hinput
    change ActiveFollowerLifecycle.startRound rate.eta V[0].input.time input inputMemory =
      .ok (choice, inputMemory) at hstart
    change (V[0].output.preparation.followers.followers i).configuration =
      .ordinary choice inputMemory at hchoice
    rw [hV0] at hinput hstart hchoice
    have hchoice' : (ReferenceFollowerFixedReply.actualChoice birth i).configuration =
        .ordinary choice inputMemory := hchoice
    have hkbR : k < R.length := (List.getElem?_eq_some_iff.mp hr).1
    have hbR : b < R.length := (List.getElem?_eq_some_iff.mp hbirthLookup).1
    have hseed' : (ReferenceFollowerFixedReply.actualChoice R[k] i).configuration =
        .ordinary state memory := by rw [(List.getElem?_eq_some_iff.mp hr).2]; exact hsActual
    have hchoiceR : (ReferenceFollowerFixedReply.actualChoice R[b] i).configuration =
        .ordinary choice inputMemory := by
      rw [(List.getElem?_eq_some_iff.mp hbirthLookup).2]
      exact hchoice'
    obtain ⟨hchoiceU, hchoiceReply, hno⟩ := old_choice_reply_of_actual_origins
      rate rewards C_star C_h z hc P0 P0 i ⟨k, hkbR⟩ ⟨b, hbR⟩ (by change k ≤ b; omega)
      state choice memory inputMemory hseed' hu hlast hchoiceR (Or.inl rfl)
      (fun j hj M hM => Or.inl (retained_before_replacement_origin
        rate rewards C_star C_h u t z hz birth0 P0 hbirth0Lookup hbirth0Install j hj i M hM))
    obtain ⟨before, beforeMemory, hbefore, hframe, _hbeforeU⟩ :=
      ReferenceFollowerReplyChronology.record_input_to_choice birth i choice inputMemory hchoice'
    obtain ⟨heq, hmemory⟩ := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
      (hbefore.symm.trans hinput)
    subst before
    subst beforeMemory
    have hinputReply : ReferenceFollowerReplyChronology.reply input =
        ReferenceFollowerReplyChronology.reply state := hframe.symm.trans hchoiceReply
    have hinputLast : input.lastDown = some (P0.downRecord i) :=
      (congrArg Prod.fst hinputReply).trans hlast
    have hLive := live_prefix_inherited_choice rate rewards C_star C_h u t z hz hc birth0 birth P0 P
      hbirth0Lookup hbirth0Install hbirthLookup hbirthInstall ⟨k, hkbR⟩ hkb i state memory
      hseed' hu hlast
    refine ⟨input, inputMemory, choice, hinput, hinputU rfl, hinputLast, hinputReply,
      hstart, hchoice', hchoiceU, hchoiceReply, hno, ?_, ?_, ?_⟩
    · exact hLive
    · intro cutoff hcutoff
      obtain ⟨endpoint, endpointMemory, hlastV, _hconfiguration, hout, hin, _htime,
        _hstart, hcChoice, _hbusy⟩ := _hremaining.1 cutoff hcutoff i
      refine ⟨endpoint, endpointMemory, hin, hcChoice, ?_⟩
      intro hold
      have hretained := hLive (V.length - 1) hlastV endpoint endpointMemory (Or.inr (Or.inr hout)) hold
      exact ⟨hretained.1, hretained.2.1, hretained.2.2.1⟩
    · exact collection_inherited_sites rate rewards C_star C_h u t z hz hc birth0 birth P0 P
        hbirth0Lookup hbirth0Install hbirthLookup hbirthInstall ⟨k, hkbR⟩ hkb i state memory
        hseed' hu hlast

end Bandits.Support.ReferenceFirstCorrectedInheritedFollowerCutoffQueue

end
