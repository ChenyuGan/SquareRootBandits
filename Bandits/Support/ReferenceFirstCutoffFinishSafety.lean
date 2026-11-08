/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCutoffRecordedService

import Lean.Elab.Tactic.Omega

/-!
# First-cutoff collection finish domains

Sources: `sources/zip4/manuscript/06_interruptions.tex:41-70,277-294`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:8-14,28-62`, and
`sources/zip4/manuscript/04_slow_fast_learner.tex:157-174`.

This module continues the actual first-cutoff recorded-service construction.
It proves ledger and clock finish domains from the concrete checked receiver
branches, and retains the bank, recording, and diagnostic in the resulting
collection observation. It does not assert a truthful UP word or a later
collection/follower survival result.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceFirstLiveConfirmationHistory
open Bandits.Support.CoordinatorCollectionLedger
open Bandits.Support.CoordinatorPhaseClock

namespace Bandits.Support.ReferenceFirstCutoffFinishSafety

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev State := ReferenceActivePhysicalHorizon.State

variable {p : Parameters} {rate : RateInput p}

private theorem finishCandidate_valid_of_domains
    (ledger : CoordinatorCollectionLedger.Ledger p rate.eta.val rate.eta.property
      rate.sourceCap rate.n rate.n_scale)
    (hvalid : CoordinatorCollectionLedger.validLedgerCheck ledger = true)
    (hphase : ledger.phase = .decoded)
    (hcursor : ledger.cursor ≤ p.T)
    (hseparated : ∀ a, ledger.increment a = 0 ∨ ledger.gammaLoc a = 0) :
    CoordinatorCollectionLedger.validLedgerCheck
      (CoordinatorCollectionLedger.finishRoundCandidate ledger) = true := by
  classical
  have hparts := hvalid
  simp only [CoordinatorCollectionLedger.validLedgerCheck, Bool.and_eq_true] at hparts
  have hcutoffCursor := hparts.1.1.1.1.1.1.1.1.1.1.1.2
  have hstartedHistory := hparts.1.1.1.1.1.1.2
  have hcurrentPending := hparts.1.1.1.1.1.2
  have hcutoffPending := hparts.1.1.1.1.2
  have hpendingGamma := hparts.1.1.1.2
  have hpendingIncrement := hparts.1.1.2
  have hregisterDomains := hparts.1.2
  have hraw := hparts.2
  simp [hphase] at hstartedHistory
  have htime : 1 ≤ p.T := p.one_le_T
  have hdomains := hregisterDomains
  simp only [CoordinatorCollectionLedger.registerDomainsCheck,
    Bool.and_eq_true] at hdomains
  have hcurrentDomains := hdomains.1.1.1.1
  have hcutoffDomains := hdomains.1.1.1.2
  have hbaseDomains := hdomains.1.1.2
  have hincrementDomains := hdomains.1.2
  have hgammaDomains := hdomains.2
  have hincrementBound : ∀ a, ledger.increment a ≤ p.T * D p := by
    intro a
    have h := (ReferenceFirstCutoffRecordedService.allFin_eq_true_iff _).mp
      hincrementDomains a
    exact of_decide_eq_true h
  have hgammaBound : ∀ a, ledger.gammaLoc a ≤ D p := by
    intro a
    have h := (ReferenceFirstCutoffRecordedService.allFin_eq_true_iff _).mp
      hgammaDomains a
    exact of_decide_eq_true h
  let finished := CoordinatorCollectionLedger.finishRoundCandidate ledger
  have hreadyHistoryFinished :
      CoordinatorCollectionLedger.readyHistoryCheck finished = true := by
    apply (ReferenceFirstCutoffRecordedService.allFin_eq_true_iff _).2
    intro r
    have h := (ReferenceFirstCutoffRecordedService.allFin_eq_true_iff _).mp
      hstartedHistory r
    change (decide (CoordinatorCollectionLedger.sourceRound r < ledger.cutoff) ||
      ((ledger.enabledHistory r).isSome ==
        decide (CoordinatorCollectionLedger.sourceRound r ≤ ledger.cursor))) = true at h
    change (decide (CoordinatorCollectionLedger.sourceRound r < ledger.cutoff) ||
      ((ledger.enabledHistory r).isSome ==
        decide (CoordinatorCollectionLedger.sourceRound r < ledger.cursor + 1))) = true
    simpa only [Nat.lt_succ_iff] using h
  have hcurrentPendingFinished : CoordinatorCollectionLedger.allFin p.K (fun a =>
      (finished.currentRegisters a).isNone ==
        CoordinatorCollectionLedger.armPendingCheck finished a) = true := by
    change CoordinatorCollectionLedger.allFin p.K (fun a =>
      (ledger.currentRegisters a).isNone ==
        CoordinatorCollectionLedger.armPendingCheck ledger a) = true
    exact hcurrentPending
  have hcutoffPendingFinished : CoordinatorCollectionLedger.allFin p.K (fun a =>
      (finished.cutoffRegisters a).isNone ==
        CoordinatorCollectionLedger.armPendingCheck finished a) = true := by
    change CoordinatorCollectionLedger.allFin p.K (fun a =>
      (ledger.cutoffRegisters a).isNone ==
        CoordinatorCollectionLedger.armPendingCheck ledger a) = true
    exact hcutoffPending
  have hpendingGammaFinished : CoordinatorCollectionLedger.allFin p.K (fun a =>
      (!CoordinatorCollectionLedger.armPendingCheck finished a) ||
        decide (finished.gammaLoc a = 0)) = true := by
    apply (ReferenceFirstCutoffRecordedService.allFin_eq_true_iff _).2
    intro a
    simp [finished, CoordinatorCollectionLedger.finishRoundCandidate]
  have hpendingIncrementFinished : CoordinatorCollectionLedger.allFin p.K (fun a =>
      (!CoordinatorCollectionLedger.armPendingCheck finished a) ||
        decide (finished.increment a = 0)) = true := by
    apply (ReferenceFirstCutoffRecordedService.allFin_eq_true_iff _).2
    intro a
    have hinc := (ReferenceFirstCutoffRecordedService.allFin_eq_true_iff _).mp
      hpendingIncrement a
    have hgam := (ReferenceFirstCutoffRecordedService.allFin_eq_true_iff _).mp
      hpendingGamma a
    have hpendingSame : CoordinatorCollectionLedger.armPendingCheck finished a =
        CoordinatorCollectionLedger.armPendingCheck ledger a := by
      rfl
    by_cases hpending : CoordinatorCollectionLedger.armPendingCheck ledger a = true
    · simp only [hpending, Bool.not_true, Bool.false_or] at hinc hgam
      have hincZero : ledger.increment a = 0 := of_decide_eq_true hinc
      have hgamZero : ledger.gammaLoc a = 0 := of_decide_eq_true hgam
      rw [hpendingSame, hpending]
      simp [finished, CoordinatorCollectionLedger.finishRoundCandidate,
        hincZero, hgamZero]
    · have hpendingFalse : CoordinatorCollectionLedger.armPendingCheck ledger a = false := by
        cases h : CoordinatorCollectionLedger.armPendingCheck ledger a with
        | false => rfl
        | true => exact False.elim (hpending h)
      rw [hpendingSame, hpendingFalse]
      simp [finished, CoordinatorCollectionLedger.finishRoundCandidate]
  have hrawFinished : CoordinatorCollectionLedger.rawEntryDomainsCheck finished = true := by
    simp only [finished, CoordinatorCollectionLedger.finishRoundCandidate,
      CoordinatorCollectionLedger.rawEntryDomainsCheck]
    apply (ReferenceFirstCutoffRecordedService.allFin_eq_true_iff _).2
    intro a
    apply (ReferenceFirstCutoffRecordedService.allFin_eq_true_iff _).2
    intro r
    cases hcell : ledger.rawBuffer a r with
    | none => rfl
    | some amount =>
        have h := (ReferenceFirstCutoffRecordedService.allFin_eq_true_iff _).mp
          ((ReferenceFirstCutoffRecordedService.allFin_eq_true_iff _).mp hraw a) r
        simp only [hcell, hphase] at h
        simp only [ite_true, Nat.lt_succ_iff]
        exact h
  have hregisterDomainsFinished :
      CoordinatorCollectionLedger.registerDomainsCheck finished = true := by
    unfold CoordinatorCollectionLedger.registerDomainsCheck
    simp only [Bool.and_eq_true]
    constructor
    · constructor
      · constructor
        · constructor
          · simpa [finished, CoordinatorCollectionLedger.finishRoundCandidate] using
              hcurrentDomains
          · simpa [finished, CoordinatorCollectionLedger.finishRoundCandidate] using
              hcutoffDomains
        · exact hbaseDomains
      · apply (ReferenceFirstCutoffRecordedService.allFin_eq_true_iff _).2
        intro a
        have hbound := hincrementBound a
        rcases hseparated a with hzeroIncrement | hzeroGamma
        · have hgammaTotal : ledger.gammaLoc a ≤ p.T * D p := by
            have hscale : D p ≤ p.T * D p := by
              simpa using Nat.mul_le_mul_right (D p) p.one_le_T
            exact (hgammaBound a).trans hscale
          have hnewIncrement : finished.increment a =
              ledger.increment a + ledger.gammaLoc a := by
            simp [finished, CoordinatorCollectionLedger.finishRoundCandidate]
          rw [hnewIncrement, hzeroIncrement]
          exact decide_eq_true (by simpa using hgammaTotal)
        · have hnewIncrement : finished.increment a =
              ledger.increment a + ledger.gammaLoc a := by
            simp [finished, CoordinatorCollectionLedger.finishRoundCandidate]
          rw [hnewIncrement, hzeroGamma]
          exact decide_eq_true (by simpa using hbound)
    · apply (ReferenceFirstCutoffRecordedService.allFin_eq_true_iff _).2
      intro a
      exact decide_eq_true (show finished.gammaLoc a ≤ D p by
        simp [finished, CoordinatorCollectionLedger.finishRoundCandidate])
  have hcursorFinished : finished.cursor ≤ p.T + 1 := by
    simp [finished, CoordinatorCollectionLedger.finishRoundCandidate]
    omega
  have hcutoffLeCursor : ledger.cutoff ≤ ledger.cursor := of_decide_eq_true hcutoffCursor
  have hcutoffCursorFinished : finished.cutoff ≤ finished.cursor := by
    simp [finished, CoordinatorCollectionLedger.finishRoundCandidate]
    exact hcutoffLeCursor.trans (Nat.le_succ _)
  change CoordinatorCollectionLedger.validLedgerCheck finished = true
  simp_all [CoordinatorCollectionLedger.validLedgerCheck, finished,
    CoordinatorCollectionLedger.finishRoundCandidate]

private theorem finishRound_success_of_domains
    (ledger : CoordinatorCollectionLedger.Ledger p rate.eta.val rate.eta.property
      rate.sourceCap rate.n rate.n_scale)
    (hvalid : CoordinatorCollectionLedger.validLedgerCheck ledger = true)
    (hphase : ledger.phase = .decoded)
    (hcursor : ledger.cursor ≤ p.T)
    (hseparated : ∀ a, ledger.increment a = 0 ∨ ledger.gammaLoc a = 0) :
    ∃ finished,
      CoordinatorCollectionLedger.finishRound ledger = .success finished ∧
      CoordinatorCollectionLedger.validLedgerCheck finished = true := by
  let finished := CoordinatorCollectionLedger.finishRoundCandidate ledger
  have hfinishedValid := finishCandidate_valid_of_domains ledger hvalid hphase
    hcursor hseparated
  refine ⟨finished, ?_, hfinishedValid⟩
  simp [CoordinatorCollectionLedger.finishRound, hvalid, hphase, hcursor,
    finished, hfinishedValid]

private theorem decodeUp_success_unknown
    (ledger : CoordinatorCollectionLedger.Ledger p rate.eta.val rate.eta.property
      rate.sourceCap rate.n rate.n_scale)
    (i : Fin (p.m - 1))
    (parsed : Option (OrdinaryMessageCodec.UpRecord
      (CoordinatorCollectionLedger.codecParams p rate.eta.val)))
    (out : CoordinatorCollectionLedger.Ledger p rate.eta.val rate.eta.property
      rate.sourceCap rate.n rate.n_scale)
    (hdomain : CoordinatorCollectionLedger.validLedgerCheck ledger = true ∧
      ledger.phase = .started ∧ 1 ≤ ledger.cutoff ∧
      ledger.cutoff ≤ ledger.cursor ∧ ledger.cursor ≤ p.T)
    (hdecode : CoordinatorCollectionLedger.decodeUp ledger i parsed = .success out) :
    ledger.currentRegisters (ledger.assignment.arm i) = none ∧
      ledger.cutoffRegisters (ledger.assignment.arm i) = none := by
  classical
  have hdecodedValid := CoordinatorUpReception.validLedgerCheck_after_decode
    ledger hdomain.1 hdomain.2.1
  have hdecodedValid' : CoordinatorCollectionLedger.validLedgerCheck
      (show CoordinatorCollectionLedger.Ledger p rate.eta.val rate.eta.property
        rate.sourceCap rate.n rate.n_scale from
        { ledger with phase := CoordinatorCollectionLedger.Phase.decoded }) = true := by
    simpa [CoordinatorUpReception.decodePhaseCandidate] using hdecodedValid
  cases parsed with
  | none =>
      unfold CoordinatorCollectionLedger.decodeUp at hdecode
      rw [dite_eq_left hdomain] at hdecode
      simp [hdecodedValid'] at hdecode
  | some M =>
      unfold CoordinatorCollectionLedger.decodeUp at hdecode
      rw [dite_eq_left hdomain] at hdecode
      by_cases haccept : CoordinatorCollectionLedger.acceptUpCheck ledger i M = true
      · by_cases hunknown :
            ledger.currentRegisters (ledger.assignment.arm i) = none ∧
              ledger.cutoffRegisters (ledger.assignment.arm i) = none
        · exact hunknown
        · simp [haccept, hunknown] at hdecode
      · simp [haccept, hdecodedValid'] at hdecode

private theorem decodeUp_success_valid
    (ledger : CoordinatorCollectionLedger.Ledger p rate.eta.val rate.eta.property
      rate.sourceCap rate.n rate.n_scale)
    (i : Fin (p.m - 1))
    (parsed : Option (OrdinaryMessageCodec.UpRecord
      (CoordinatorCollectionLedger.codecParams p rate.eta.val)))
    (out : CoordinatorCollectionLedger.Ledger p rate.eta.val rate.eta.property
      rate.sourceCap rate.n rate.n_scale)
    (hdomain : CoordinatorCollectionLedger.validLedgerCheck ledger = true ∧
      ledger.phase = .started ∧ 1 ≤ ledger.cutoff ∧
      ledger.cutoff ≤ ledger.cursor ∧ ledger.cursor ≤ p.T)
    (hdecode : CoordinatorCollectionLedger.decodeUp ledger i parsed = .success out) :
    CoordinatorCollectionLedger.validLedgerCheck out = true := by
  classical
  rcases CoordinatorCollectionUpRoundStep.InputsValid.decodeUp_success_candidate
      ledger i parsed out hdomain hdecode with
    ⟨M, past, current, hparsed, hout, hpast, hcurrent⟩
  have hunknown := decodeUp_success_unknown ledger i parsed out hdomain hdecode
  have haccept : CoordinatorCollectionLedger.acceptUpCheck ledger i M = true := by
    by_contra hnot
    have hdecodedValid := CoordinatorUpReception.validLedgerCheck_after_decode
      ledger hdomain.1 hdomain.2.1
    have hdecodedValid' : CoordinatorCollectionLedger.validLedgerCheck
        (show CoordinatorCollectionLedger.Ledger p rate.eta.val rate.eta.property
          rate.sourceCap rate.n rate.n_scale from
          { ledger with phase := CoordinatorCollectionLedger.Phase.decoded }) = true := by
      simpa [CoordinatorUpReception.decodePhaseCandidate] using hdecodedValid
    have h := hdecode
    rw [hparsed] at h
    unfold CoordinatorCollectionLedger.decodeUp at h
    rw [dite_eq_left hdomain] at h
    simp [hnot, hdecodedValid'] at h
  have hout' := hout
  rw [hout'] at hdecode
  have hvalidNext : CoordinatorCollectionLedger.validLedgerCheck
      (CoordinatorCollectionLedger.acceptUpCandidate ledger i M past current) = true := by
    cases houtput : CoordinatorCollectionLedger.replayOutputDomainsCheck
        (p := p) (4 * rate.n) M.val.q (past ++ [current]) with
    | false =>
        have hbad : CoordinatorCollectionLedger.decodeUp ledger i (some M) = .invalid := by
          unfold CoordinatorCollectionLedger.decodeUp
          rw [dite_eq_left hdomain]
          simp [haccept, hunknown.1, hunknown.2, hpast, hcurrent, houtput]
        rw [hparsed] at hdecode
        rw [hbad] at hdecode
        cases hdecode
    | true =>
        cases hcheck : CoordinatorCollectionLedger.validLedgerCheck
            (CoordinatorCollectionLedger.acceptUpCandidate ledger i M past current) with
        | false =>
            have hbad : CoordinatorCollectionLedger.decodeUp ledger i (some M) = .invalid := by
              unfold CoordinatorCollectionLedger.decodeUp
              rw [dite_eq_left hdomain]
              simp [haccept, hunknown.1, hunknown.2, hpast, hcurrent, houtput, hcheck]
            rw [hparsed] at hdecode
            rw [hbad] at hdecode
            cases hdecode
        | true => rfl
  simpa [hout] using hvalidNext

private theorem decodeUp_rejected_phase
    (ledger : CoordinatorCollectionLedger.Ledger p rate.eta.val rate.eta.property
      rate.sourceCap rate.n rate.n_scale)
    (i : Fin (p.m - 1))
    (parsed : Option (OrdinaryMessageCodec.UpRecord
      (CoordinatorCollectionLedger.codecParams p rate.eta.val)))
    (out : CoordinatorCollectionLedger.Ledger p rate.eta.val rate.eta.property
      rate.sourceCap rate.n rate.n_scale)
    (hdomain : CoordinatorCollectionLedger.validLedgerCheck ledger = true ∧
      ledger.phase = .started ∧ 1 ≤ ledger.cutoff ∧
      ledger.cutoff ≤ ledger.cursor ∧ ledger.cursor ≤ p.T)
    (hdecode : CoordinatorCollectionLedger.decodeUp ledger i parsed = .rejected out) :
    out = { ledger with phase := CoordinatorCollectionLedger.Phase.decoded } := by
  classical
  have hdecodedValid := CoordinatorUpReception.validLedgerCheck_after_decode
    ledger hdomain.1 hdomain.2.1
  have hdecodedValid' : CoordinatorCollectionLedger.validLedgerCheck
      (show CoordinatorCollectionLedger.Ledger p rate.eta.val rate.eta.property
        rate.sourceCap rate.n rate.n_scale from
        { ledger with phase := CoordinatorCollectionLedger.Phase.decoded }) = true := by
    simpa [CoordinatorUpReception.decodePhaseCandidate] using hdecodedValid
  cases parsed with
  | none =>
      unfold CoordinatorCollectionLedger.decodeUp at hdecode
      rw [dite_eq_left hdomain] at hdecode
      simp [hdecodedValid'] at hdecode
      exact hdecode.symm
  | some M =>
      unfold CoordinatorCollectionLedger.decodeUp at hdecode
      rw [dite_eq_left hdomain] at hdecode
      by_cases haccept : CoordinatorCollectionLedger.acceptUpCheck ledger i M = true
      · by_cases hunknown :
            ledger.currentRegisters (ledger.assignment.arm i) = none ∧
              ledger.cutoffRegisters (ledger.assignment.arm i) = none
        · cases hpast : CoordinatorCollectionLedger.replayRecords? ledger
              (ledger.assignment.arm i)
              (CoordinatorCollectionLedger.calendarIndices p.T
                (ledger.cutoff - 1) (ledger.cursor - ledger.cutoff)
                (by omega)) with
          | none => simp [haccept, hunknown, hpast] at hdecode
          | some past =>
              cases hlast : CoordinatorCollectionLedger.replayRecords? ledger
                  (ledger.assignment.arm i)
                  [⟨ledger.cursor - 1, by omega⟩] with
              | none => simp [haccept, hunknown, hpast, hlast] at hdecode
              | some last =>
                  cases last with
                  | nil => simp [haccept, hunknown, hpast, hlast] at hdecode
                  | cons current tail =>
                      cases tail with
                      | nil =>
                          cases houtdom : CoordinatorCollectionLedger.replayOutputDomainsCheck
                              (p := p) (4 * rate.n) M.val.q (past ++ [current]) with
                          | false => simp [haccept, hunknown, hpast, hlast, houtdom] at hdecode
                          | true =>
                              cases hvalid : CoordinatorCollectionLedger.validLedgerCheck
                                  (CoordinatorCollectionLedger.acceptUpCandidate
                                    ledger i M past current) with
                              | false =>
                                  simp [haccept, hunknown, hpast, hlast, houtdom, hvalid] at hdecode
                              | true =>
                                  simp [haccept, hunknown, hpast, hlast, houtdom, hvalid] at hdecode
                      | cons other rest =>
                          simp [haccept, hunknown, hpast, hlast] at hdecode
        · simp [haccept, hunknown] at hdecode
      · simp [haccept, hdecodedValid'] at hdecode
        exact hdecode.symm

private theorem actual_receive_finish_domains
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (recording : CoordinatorRecordingOperation.Output p)
    (ledgerStarted : CoordinatorCollectionLedger.Ledger p rate.eta.val
      rate.eta.property rate.sourceCap rate.n rate.n_scale)
    (hincrementZero : ledgerStarted.increment = fun _ => 0)
    (hunknownZero : ∀ a, ledgerStarted.currentRegisters a = none →
      ledgerStarted.gammaLoc a = 0)
    (hclockValid : CoordinatorPhaseClock.clockRegistersValid p rate.eta.val
      started.clock)
    (hfinishTime : CoordinatorPhaseClock.finishRoundTimeValid x.time started.clock)
    (hsigma : started.clock.sigma ≠ none)
    (hu : started.clock.u = some x.time)
    (ledgerDecoded : CoordinatorCollectionLedger.Ledger p rate.eta.val
      rate.eta.property rate.sourceCap rate.n rate.n_scale)
    (bank : CoordinatorUpReception.UpDecoderBank p)
    (hreception : (ReferenceActivePhysicalStep.receiveUp prepared ledgerStarted).result =
        .success (ledgerDecoded, bank) ∨
      (ReferenceActivePhysicalStep.receiveUp prepared ledgerStarted).result =
        .rejected (ledgerDecoded, bank)) :
    ∃ ledgerFinished,
      CoordinatorCollectionLedger.finishRound ledgerDecoded = .success ledgerFinished ∧
      CoordinatorCollectionLedger.validLedgerCheck ledgerFinished = true ∧
      (∀ pending : Finset (Fin (p.m - 1)),
        ∃ clockFinished,
          CoordinatorPhaseClock.finishRound p rate.eta.val x.time started.clock
            pending x.row = .ok clockFinished ∧
          clockFinished.clock = started.clock ∧
          clockFinished.pending = pending ∧
          clockFinished.ledgerCommand =
            some (.accumulateLocalServiceAt x.time)) ∧
      ReferenceActivePhysicalStep.collectionFinish (x := x) payload started recording
          (ReferenceActivePhysicalStep.receiveUp prepared ledgerStarted) =
        ⟨.collection payload ledgerFinished started.clock.lastProposal, bank, none,
          some recording,
          (ReferenceActivePhysicalStep.receiveUp prepared ledgerStarted).diagnostic⟩ := by
  classical
  let inputs := ReferenceActivePhysicalStep.upInputs prepared ledgerStarted
  let input := ReferenceUpReception.receptionInputAtRow rate x.row inputs x.time
  let sender := prepared.followers.followers
    (ReferenceActivePhysicalStep.upSenderIndex x)
  have hrow : sender.row = x.row := (prepared.follower_alignment _).1
  have hplayer : sender.follower = input.selectedFollower :=
    (prepared.follower_alignment _).2.1
  have htime : sender.time = input.time :=
    (prepared.follower_alignment _).2.2.1
  have hresult : (ReferenceActivePhysicalStep.receiveUp prepared ledgerStarted).result =
      ReferenceUpReception.receiveUpFilteredAtRow rate x.row inputs x.time sender
        hrow hplayer htime rfl := rfl
  have hnoninvalid : (ReferenceActivePhysicalStep.receiveUp prepared ledgerStarted).result ≠
      .invalid := by
    intro hbad
    rcases hreception with hs | hr
    · rw [hbad] at hs
      cases hs
    · rw [hbad] at hr
      cases hr
  have hcheck : CoordinatorUpReception.receptionInputCheck input = true := by
    by_contra hnot
    have hfalse : CoordinatorUpReception.receptionInputCheck input = false := by
      cases hc : CoordinatorUpReception.receptionInputCheck input with
      | false => rfl
      | true => exact False.elim (hnot hc)
    obtain ⟨hinvalid, _⟩ :=
      ReferenceUpReception.receiveUpFilteredAtRow_input_invalid rate x.row inputs x.time
        sender hrow hplayer htime rfl hfalse
    exact hnoninvalid (by rw [hresult, hinvalid])
  have hfiltered := ReferenceUpReception.receiveUpFilteredAtRow_eq_filtered_decode
    rate x.row inputs x.time sender hrow hplayer htime rfl hcheck
  have hpacked := hreception
  rw [hresult, hfiltered] at hpacked
  let parsed : Option (OrdinaryMessageCodec.UpRecord
      (CoordinatorCollectionLedger.codecParams p rate.eta.val)) :=
    CoordinatorUpReception.parseDecoderOutput (p := p) (eta := rate.eta.val)
    (ReferenceUpReception.filterRawByExpected
      (CoordinatorUpReception.decoderTransition input).2
      (ReferenceUpReception.currentOfferWord rate x.row input.selectedFollower input.time
        sender hrow hplayer htime))
  have hdecodeResult :
      CoordinatorCollectionLedger.decodeUp input.ledger input.selectedFollower parsed =
          .success ledgerDecoded ∨
        CoordinatorCollectionLedger.decodeUp input.ledger input.selectedFollower parsed =
          .rejected ledgerDecoded := by
    have hpacked' :
        CoordinatorUpReception.packDecodeResult
            (CoordinatorCollectionLedger.decodeUp input.ledger input.selectedFollower parsed)
            (CoordinatorUpReception.decoderBankAfter input) =
          .success (ledgerDecoded, bank) ∨
        CoordinatorUpReception.packDecodeResult
            (CoordinatorCollectionLedger.decodeUp input.ledger input.selectedFollower parsed)
            (CoordinatorUpReception.decoderBankAfter input) =
          .rejected (ledgerDecoded, bank) := by
      simpa [parsed, input, inputs, ReferenceActivePhysicalStep.upInputs] using hpacked
    cases hdecode : CoordinatorCollectionLedger.decodeUp input.ledger
        input.selectedFollower parsed with
    | success decoded =>
        left
        rcases hpacked' with hs | hr
        · have hp : (decoded, CoordinatorUpReception.decoderBankAfter input) =
              (ledgerDecoded, bank) := by
            simpa [CoordinatorUpReception.packDecodeResult, hdecode] using hs
          have hledgerEq : decoded = ledgerDecoded := congrArg Prod.fst hp
          exact congrArg CoordinatorCollectionLedger.Checked.success hledgerEq
        · simp [CoordinatorUpReception.packDecodeResult, hdecode] at hr
    | rejected decoded =>
        right
        rcases hpacked' with hs | hr
        · simp [CoordinatorUpReception.packDecodeResult, hdecode] at hs
        · have hp : (decoded, CoordinatorUpReception.decoderBankAfter input) =
              (ledgerDecoded, bank) := by
            simpa [CoordinatorUpReception.packDecodeResult, hdecode] using hr
          have hledgerEq : decoded = ledgerDecoded := congrArg Prod.fst hp
          exact congrArg CoordinatorCollectionLedger.Checked.rejected hledgerEq
    | invalid =>
        rcases hpacked' with hs | hr
        · simp [CoordinatorUpReception.packDecodeResult, hdecode] at hs
        · simp [CoordinatorUpReception.packDecodeResult, hdecode] at hr
  have hdomain := (CoordinatorUpReception.receptionInputCheck_eq_true_iff input).mp hcheck
  rcases CoordinatorUpReception.receptionInputDomain_parts input hdomain with
    ⟨hinputValid, _, hinputPhase, hcutoffPos, hcutoffCursor, hcursorT, _, _⟩
  have hdecodeDomain :
      CoordinatorCollectionLedger.validLedgerCheck input.ledger = true ∧
        input.ledger.phase = .started ∧ 1 ≤ input.ledger.cutoff ∧
        input.ledger.cutoff ≤ input.ledger.cursor ∧ input.ledger.cursor ≤ p.T :=
    ⟨hinputValid, hinputPhase, hcutoffPos, hcutoffCursor, hcursorT⟩
  have hincrementInput : input.ledger.increment = fun _ => 0 := by
    change ledgerStarted.increment = fun _ => 0
    exact hincrementZero
  have hunknownZeroInput : ∀ a, input.ledger.currentRegisters a = none →
      input.ledger.gammaLoc a = 0 := by
    intro a hnone
    change ledgerStarted.gammaLoc a = 0
    apply hunknownZero a
    exact hnone
  have hdecodedFields :
      CoordinatorCollectionLedger.validLedgerCheck ledgerDecoded = true ∧
        ledgerDecoded.phase = .decoded ∧ ledgerDecoded.cursor ≤ p.T ∧
        ∀ a, ledgerDecoded.increment a = 0 ∨ ledgerDecoded.gammaLoc a = 0 := by
    rcases hdecodeResult with hsuccess | hrejected
    · have hvalid := decodeUp_success_valid input.ledger input.selectedFollower parsed
        ledgerDecoded hdecodeDomain hsuccess
      have hfields :=
        CoordinatorCollectionUpRoundStep.InputsValid.decodeUp_success_candidate
          input.ledger input.selectedFollower parsed ledgerDecoded hdecodeDomain hsuccess
      rcases hfields with ⟨M, past, current, hparsed, hcand, _, _⟩
      have hunknown := decodeUp_success_unknown input.ledger input.selectedFollower
        parsed ledgerDecoded hdecodeDomain hsuccess
      have hgammaZero := hunknownZeroInput _ hunknown.1
      have hphase : ledgerDecoded.phase = .decoded := by
        rw [hcand]
        simp [CoordinatorCollectionLedger.acceptUpCandidate]
      have hcursor : ledgerDecoded.cursor ≤ p.T := by
        rw [hcand]
        simpa [CoordinatorCollectionLedger.acceptUpCandidate] using hcursorT
      refine ⟨hvalid, hphase, hcursor, ?_⟩
      intro a
      by_cases ha : a = input.ledger.assignment.arm input.selectedFollower
      · right
        rw [hcand]
        simpa [CoordinatorCollectionLedger.acceptUpCandidate, ha] using hgammaZero
      · left
        rw [hcand]
        simp [CoordinatorCollectionLedger.acceptUpCandidate, ha, hincrementInput]
    · have hphaseEq := decodeUp_rejected_phase input.ledger input.selectedFollower
        parsed ledgerDecoded hdecodeDomain hrejected
      have hvalidDecoded := CoordinatorUpReception.validLedgerCheck_after_decode
        input.ledger hinputValid hinputPhase
      have hvalid : CoordinatorCollectionLedger.validLedgerCheck ledgerDecoded = true := by
        simpa [hphaseEq, CoordinatorUpReception.decodePhaseCandidate] using hvalidDecoded
      have hphase : ledgerDecoded.phase = .decoded := by
        rw [hphaseEq]
      have hcursor : ledgerDecoded.cursor ≤ p.T := by
        rw [hphaseEq]
        exact hcursorT
      refine ⟨hvalid, hphase, hcursor, ?_⟩
      intro a
      left
      rw [hphaseEq]
      simp [hincrementInput]
  rcases finishRound_success_of_domains ledgerDecoded hdecodedFields.1
      hdecodedFields.2.1 hdecodedFields.2.2.1 hdecodedFields.2.2.2 with
    ⟨ledgerFinished, hledgerFinish, hledgerFinishedValid⟩
  have hclockAll : ∀ pending : Finset (Fin (p.m - 1)),
      ∃ clockFinished,
        CoordinatorPhaseClock.finishRound p rate.eta.val x.time started.clock
          pending x.row = .ok clockFinished ∧
        clockFinished.clock = started.clock ∧
        clockFinished.pending = pending ∧
        clockFinished.ledgerCommand = some (.accumulateLocalServiceAt x.time) := by
    intro pending
    exact CoordinatorPhaseClock.finishRound_collection_effect p rate.eta.val x.time
      started.clock pending x.row hclockValid hfinishTime hsigma x.time hu
  obtain ⟨clockFinished, hclockFinish, hclockEq, _, _⟩ :=
    hclockAll ledgerFinished.pending
  have hcollection := ReferenceActivePhysicalStep.collectionFinish_success
    payload started recording (ReferenceActivePhysicalStep.receiveUp prepared ledgerStarted)
    ledgerDecoded ledgerFinished bank clockFinished hreception hledgerFinish hclockFinish
  refine ⟨ledgerFinished, hledgerFinish, hledgerFinishedValid, hclockAll, ?_⟩
  simpa [hclockEq] using hcollection

private theorem firstCutoffClock_after_start
    (prior : CoordinatorPhaseClock.ClockRegisters p)
    (time sigma : Fin p.T)
    (hvalid : CoordinatorPhaseClock.clockRegistersValid p rate.eta.val prior)
    (hsigma : prior.sigma = some sigma)
    (hu : prior.u = none)
    (hsigmaTime : sigma.val < time.val)
    (htimeGrid : time.val < prior.g) :
    CoordinatorPhaseClock.clockRegistersValid p rate.eta.val
        { prior with u := some time } ∧
      CoordinatorPhaseClock.finishRoundTimeValid time
        { prior with u := some time } := by
  rcases hvalid with ⟨hgridEq, hfields⟩
  rw [hsigma] at hgridEq
  rw [hsigma, hu] at hfields
  rcases hfields with ⟨hsigmaGrid, hgridBound, _⟩
  constructor
  · simp only [CoordinatorPhaseClock.clockRegistersValid, hsigma]
    exact ⟨hgridEq, hsigmaGrid, hgridBound, hsigmaTime, by omega⟩
  · simp only [CoordinatorPhaseClock.finishRoundTimeValid, hsigma]
    exact ⟨hsigmaTime.le, le_rfl⟩

/-- From the original run roots, retain the exact first-cutoff B0 service
record and prove the subsequent actual receiver's finish domain. Both
ordinary reception selectors are covered; the receiver's invalid result
remains an explicit unselected branch.

Sources: `sources/zip4/manuscript/06_interruptions.tex:41-70,277-294`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:8-14,28-62`, and
`sources/zip4/manuscript/04_slow_fast_learner.tex:157-174`.
-/
theorem run_first_cutoff_finish_domains
    (initial : State p rate) (rows : CompletePublicTable.CompleteRows p)
    (J : Fin (M p)) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (active : allActiveAtStart initial start)
    (hfirst : initial.coordinator = .first)
    (hshort : (firstLiveWindow
      (ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan active).records).length
        < count) :
    let execution := ReferenceActivePhysicalHorizon.run initial rows J rewards
      start count hspan active
    let window := firstLiveWindow execution.records
    let k := window.length
    ∃ cut suffix,
      execution.records = window ++ cut :: suffix ∧
      cut = execution.records[k]'(by
        simpa [execution, ReferenceActivePhysicalHorizon.run_record_count] using hshort) ∧
      cut.input.time.val = start + k ∧
      ∃ (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
        (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
        (base : Fin (p.m - 1) → ℕ),
        cut.input.state = (ReferenceActivePhysicalHorizon.run initial rows J rewards
          start k (by
            have hk : k < count := by simpa [window, execution] using hshort
            exact le_trans (Nat.add_le_add_left (Nat.le_of_lt hk) start) hspan) active).finalState ∧
        (ReferenceActivePhysicalHorizon.run initial rows J rewards
          start k (by
            have hk : k < count := by simpa [window, execution] using hshort
            exact le_trans (Nat.add_le_add_left (Nat.le_of_lt hk) start) hspan) active).finalState.coordinator =
          .live r q base ∧
        let callInput := ReferenceActivePhysicalStep.liveInput cut.input r q base
        ∃ (dispatched : CoordinatorStartRoundCutoffDispatch.Output
            callInput.registers callInput.ownedRegisters base)
          (hstart : CoordinatorPhaseClock.startRound p rate.eta.val
            callInput.registers.time callInput.registers.priorClock
            callInput.registers.clockPending = .ok dispatched.startResult)
          (ledger : CoordinatorStartRoundCutoffDispatch.NewLedger callInput.registers)
          (hinit : dispatched.collectionInitialization = .success (some ledger))
          (hledger : ledger = CoordinatorStartRoundCutoffDispatch.collectionStartLedger
            callInput.registers callInput.ownedRegisters base callInput.registers.time)
          (hdomain : CoordinatorStartRoundCutoffDispatch.initializationDomainValid
            callInput.registers callInput.ownedRegisters base callInput.registers.time)
          (hclock : dispatched.startResult.clock =
            { callInput.registers.priorClock with u := some callInput.registers.time })
          (hpending : dispatched.startResult.pending = Finset.univ)
          (hnoAssignment : dispatched.startResult.assignmentStart = none)
          (selected : CoordinatorRoundDispatch.ArmSelection callInput.registers.payload
            dispatched.startResult callInput.registers.time
            callInput.registers.complementWeights cut.input.row),
          cut.output.preparation.coordinator = .live r q base
            (.cutoffChosen dispatched hstart ledger hinit hledger hdomain hclock hpending
              hnoAssignment selected) ∧
          ∃ output,
            ReferenceCoordinatorRecorderCallTrace.actualBranchInput cut =
              some (CoordinatorRecorderComplementBridge.recorderInput
                (ReferenceActivePhysicalStep.collectionRecordingInput
                  cut.output.preparation callInput.registers.payload dispatched.startResult
                  callInput.registers.complementWeights)) ∧
            ReferenceCoordinatorRecorderCallTrace.recording
              (ReferenceActiveHorizonMeasurability.roundRecordCode cut) = some output ∧
            cut.coordinatorDiagnostics.recording = some output ∧
            CoordinatorRecordingOperation.run
              (CoordinatorRecorderComplementBridge.recorderInput
                (ReferenceActivePhysicalStep.collectionRecordingInput
                  cut.output.preparation callInput.registers.payload dispatched.startResult
                  callInput.registers.complementWeights)) = some output ∧
            let shared := ReferenceActivePhysicalStep.sharedLedger ledger
            let raw := CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder output
            let enabled := ReferenceActivePhysicalStep.collectionEnabled shared cut.input.time
            ∃ ledgerStarted,
              CoordinatorCollectionLedger.startRound shared (cut.input.time.val + 1)
                enabled raw = .success ledgerStarted ∧
              ledgerStarted = CoordinatorCollectionLedger.startRoundCandidate shared
                cut.input.time enabled raw ∧
              (∀ a current, shared.currentRegisters a = some current →
                ledgerStarted.currentRegisters a = some ⟨
                  (QueueReplay.transition (4 * rate.n) (0, current.queue)
                    (CoordinatorCollectionLedger.localQueueRecord shared cut.input.time
                      enabled raw a)).2,
                  (QueueReplay.transition (4 * rate.n) (0, current.queue)
                    (CoordinatorCollectionLedger.localQueueRecord shared cut.input.time
                      enabled raw a)).1⟩) ∧
              (∀ a, shared.currentRegisters a = none →
                ledgerStarted.currentRegisters a = none ∧ ledgerStarted.gammaLoc a = 0) ∧
              (∀ a amount, shared.currentRegisters a = none → 0 < amount →
                CoordinatorCollectionLedger.sourceRound cut.input.time < shared.freezeAt →
                raw = some (a, amount) → ledgerStarted.rawBuffer a cut.input.time = some amount) ∧
              (∀ a amount other armRound, shared.currentRegisters a = none →
                0 < amount →
                CoordinatorCollectionLedger.sourceRound cut.input.time < shared.freezeAt →
                raw = some (a, amount) → (other ≠ a ∨ armRound ≠ cut.input.time) →
                ledgerStarted.rawBuffer other armRound = shared.rawBuffer other armRound) ∧
              (∀ a current, shared.currentRegisters a = some current →
                (QueueReplay.transition (4 * rate.n) (0, current.queue)
                  (CoordinatorCollectionLedger.localQueueRecord shared cut.input.time
                    enabled raw a)).2 ≤ (k + 1) * D p ∧
                (QueueReplay.transition (4 * rate.n) (0, current.queue)
                  (CoordinatorCollectionLedger.localQueueRecord shared cut.input.time
                    enabled raw a)).2 ≤ p.T * D p ∧
                (QueueReplay.transition (4 * rate.n) (0, current.queue)
                  (CoordinatorCollectionLedger.localQueueRecord shared cut.input.time
                    enabled raw a)).1 ≤ 4 * rate.n ∧
                (QueueReplay.transition (4 * rate.n) (0, current.queue)
                  (CoordinatorCollectionLedger.localQueueRecord shared cut.input.time
                    enabled raw a)).1 ≤ D p) ∧
              ∀ ledgerDecoded bank,
                ((ReferenceActivePhysicalStep.receiveUp cut.output.preparation ledgerStarted).result =
                    .success (ledgerDecoded, bank) ∨
                  (ReferenceActivePhysicalStep.receiveUp cut.output.preparation ledgerStarted).result =
                    .rejected (ledgerDecoded, bank)) →
                ∃ ledgerFinished,
                  CoordinatorCollectionLedger.finishRound ledgerDecoded = .success ledgerFinished ∧
                  CoordinatorCollectionLedger.validLedgerCheck ledgerFinished = true ∧
                  (∀ pending : Finset (Fin (p.m - 1)),
                    ∃ clockFinished,
                      CoordinatorPhaseClock.finishRound p rate.eta.val cut.input.time
                        dispatched.startResult.clock pending cut.input.row = .ok clockFinished ∧
                      clockFinished.clock = dispatched.startResult.clock ∧
                      clockFinished.pending = pending ∧
                      clockFinished.ledgerCommand =
                        some (.accumulateLocalServiceAt cut.input.time)) ∧
                  cut.output.coordinator.configuration =
                    .collection callInput.registers.payload ledgerFinished
                      dispatched.startResult.clock.lastProposal ∧
                  cut.output.coordinator.upDecoderBank = bank ∧
                  cut.output.coordinator.failure = none ∧
                  cut.output.coordinator.recording = some output ∧
                  cut.output.coordinator.up =
                    (ReferenceActivePhysicalStep.receiveUp cut.output.preparation
                      ledgerStarted).diagnostic := by
  classical
  let execution := ReferenceActivePhysicalHorizon.run initial rows J rewards
    start count hspan active
  let window := firstLiveWindow execution.records
  let k := window.length
  have hservice := ReferenceFirstCutoffRecordedService.run_first_cutoff_recorded_service
    initial rows J rewards start count hspan active hfirst (by
      simpa [execution, window] using hshort)
  dsimp only [execution, window, k] at hservice
  rcases hservice with
    ⟨cut, suffix, hsplit, hindex, htime, r, q, base, hstate, hprefix, hcall⟩
  rcases hcall with
    ⟨dispatched, hstart, ledger, hinit, hledger, hdomain, hclock, hpending,
      hnoAssignment, selected, hbranch, hrecordRest⟩
  rcases hrecordRest with
    ⟨output, hactualInput, htrace, hdiagnostic, hrecorderRun, hnextRest⟩
  rcases hnextRest with
    ⟨ledgerStarted, hstartSuccess, hstartCandidate, hknownTransition,
      hunknownStageOne, hrawArrival, hrawFrame, hqueueDomains⟩
  let callInput := ReferenceActivePhysicalStep.liveInput cut.input r q base
  let shared := ReferenceActivePhysicalStep.sharedLedger ledger
  let raw := CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder output
  let enabled := ReferenceActivePhysicalStep.collectionEnabled shared cut.input.time
  have hsharedIncrement : shared.increment = fun _ => 0 := by
    simp [shared, ReferenceActivePhysicalStep.sharedLedger, hledger,
      ReferenceActivePhysicalStep.liveInput, ReferenceActivePhysicalStep.liveRegistersAt,
      CoordinatorStartRoundCutoffDispatch.collectionStartLedger]
  have hincrementZero : ledgerStarted.increment = fun _ => 0 := by
    rw [hstartCandidate]
    change shared.increment = fun _ => 0
    exact hsharedIncrement
  have hunknownZero : ∀ a, ledgerStarted.currentRegisters a = none →
      ledgerStarted.gammaLoc a = 0 := by
    intro a hnone
    have hsharedUnknown : shared.currentRegisters a = none := by
      by_contra hknown
      cases hcurrent : shared.currentRegisters a with
      | none => exact hknown hcurrent
      | some current =>
          have hknown' := hknownTransition a current hcurrent
          rw [hnone] at hknown'
          cases hknown'
    exact (hunknownStageOne a hsharedUnknown).2
  have hseed : ReferenceCoordinatorClockDomains.clockAt rows J start initial := by
    simp [ReferenceCoordinatorClockDomains.clockAt, hfirst]
  have hk : k < count := by simpa [window, execution] using hshort
  have hprefixSpan : start + k ≤ p.T :=
    le_trans (Nat.add_le_add_left (Nat.le_of_lt hk) start) hspan
  have hrunClock := ReferenceRunClockPreservation.run_clockAt initial rows J rewards
    start k hprefixSpan active hseed
  have hclockAtPrefix := hrunClock.2.1 k (Nat.le_refl k)
  have hprefix' :
      (ReferenceActivePhysicalHorizon.run initial rows J rewards start k hprefixSpan active).finalState.coordinator =
        .live r q base := by
    simpa [k, window, execution] using hprefix
  simp only [ReferenceCoordinatorClockDomains.clockAt, hprefix'] at hclockAtPrefix
  rcases hclockAtPrefix with
    ⟨hclockIndex, hpriorValid, hpriorSigma, hpriorU, hgridEq, hsigmaBefore,
      htimeBeforeGrid, _⟩
  have htime' : cut.input.time.val = start + k := by
    simpa [window, execution, k] using htime
  have hnowSigma : r.payload.sigma.val < cut.input.time.val := by
    calc
      r.payload.sigma.val < start + k := by
        simpa [window, execution, k] using hsigmaBefore
      _ = cut.input.time.val := htime'.symm
  have hnowGrid : cut.input.time.val < r.priorClock.g := by
    have hgridNow : cut.input.time.val < r.gridBoundary := by
      rw [htime']
      simpa [window, execution, k] using htimeBeforeGrid
    rw [hgridEq] at hgridNow
    exact hgridNow
  have hpriorStarted := firstCutoffClock_after_start r.priorClock cut.input.time
    r.payload.sigma (by simpa [callInput, ReferenceActivePhysicalStep.liveInput,
      ReferenceActivePhysicalStep.liveRegistersAt] using hpriorValid)
    (by simpa [callInput, ReferenceActivePhysicalStep.liveInput,
      ReferenceActivePhysicalStep.liveRegistersAt] using hpriorSigma)
    (by simpa [callInput, ReferenceActivePhysicalStep.liveInput,
      ReferenceActivePhysicalStep.liveRegistersAt] using hpriorU)
    hnowSigma hnowGrid
  have hclockValid : CoordinatorPhaseClock.clockRegistersValid p rate.eta.val
      dispatched.startResult.clock := by
    rw [hclock]
    simpa [callInput, ReferenceActivePhysicalStep.liveInput,
      ReferenceActivePhysicalStep.liveRegistersAt] using hpriorStarted.1
  have hfinishTime : CoordinatorPhaseClock.finishRoundTimeValid cut.input.time
      dispatched.startResult.clock := by
    rw [hclock]
    simpa [callInput, ReferenceActivePhysicalStep.liveInput,
      ReferenceActivePhysicalStep.liveRegistersAt] using hpriorStarted.2
  have hsigma : dispatched.startResult.clock.sigma ≠ none := by
    rw [hclock]
    simp [ReferenceActivePhysicalStep.liveInput,
      ReferenceActivePhysicalStep.liveRegistersAt, hpriorSigma]
  have hu : dispatched.startResult.clock.u = some cut.input.time := by
    rw [hclock]
    rfl
  have hselection :
      (ReferenceActivePhysicalStep.DispatchCut.live r q base
        (.cutoffChosen dispatched hstart ledger hinit hledger hdomain hclock hpending
          hnoAssignment selected)).selection ≠ none := by
    simp [ReferenceActivePhysicalStep.DispatchCut.selection,
      ReferenceActivePhysicalStep.selectionAt,
      ReferenceActivePhysicalStep.liveRegistersAt]
  have hobserve := ReferenceActivePhysicalStep.observeCoordinator_live_equation
    cut.output.preparation r q base
      (.cutoffChosen dispatched hstart ledger hinit hledger hdomain hclock hpending
        hnoAssignment selected) hbranch
  have hcollectionPost : cut.output.coordinator =
      ReferenceActivePhysicalStep.collectionPostChoice cut.output.preparation
        callInput.registers.payload (sharedLedger ledger) dispatched.startResult
        callInput.registers.complementWeights := by
    have hprep : cut.output.preparation = ReferenceActivePhysicalStep.prepare cut.input :=
      congrArg ReferenceActivePhysicalStep.RoundOutput.preparation cut.output_eq
    calc
      cut.output.coordinator = (ReferenceActivePhysicalStep.step cut.input).coordinator :=
        congrArg ReferenceActivePhysicalStep.RoundOutput.coordinator cut.output_eq
      _ = (ReferenceActivePhysicalStep.prepare cut.input).observeCoordinator := rfl
      _ = cut.output.preparation.observeCoordinator := by rw [hprep]
      _ = ReferenceActivePhysicalStep.collectionPostChoice cut.output.preparation
          callInput.registers.payload (sharedLedger ledger) dispatched.startResult
          callInput.registers.complementWeights := by
        rw [hobserve, ite_eq_right hselection]
        rfl
  have hbridgeRun :
      CoordinatorRecorderComplementBridge.run
        (ReferenceActivePhysicalStep.collectionRecordingInput cut.output.preparation
          callInput.registers.payload dispatched.startResult callInput.registers.complementWeights) =
        some output := by
    simpa [CoordinatorRecorderComplementBridge.run] using hrecorderRun
  have hcollectionPostStart := ReferenceActivePhysicalStep.collectionPostChoice_after_start
    cut.output.preparation callInput.registers.payload (sharedLedger ledger)
    dispatched.startResult callInput.registers.complementWeights output ledgerStarted
    hbridgeRun (by simpa [shared, raw, enabled] using hstartSuccess)
  refine ⟨cut, suffix, hsplit, hindex, htime, r, q, base, hstate, hprefix,
    dispatched, hstart, ledger, hinit, hledger, hdomain, hclock, hpending,
    hnoAssignment, selected, hbranch, output, hactualInput, htrace, hdiagnostic,
    hrecorderRun, ledgerStarted, ?_⟩
  refine ⟨by simpa [shared, raw, enabled] using hstartSuccess, hstartCandidate,
    hknownTransition, hunknownStageOne, hrawArrival, hrawFrame, hqueueDomains, ?_⟩
  intro ledgerDecoded bank hreception
  obtain ⟨ledgerFinished, hledgerFinish, hledgerFinishedValid, hclockAll,
    hcollectionFinish⟩ := actual_receive_finish_domains cut.output.preparation
      callInput.registers.payload dispatched.startResult output ledgerStarted
      hincrementZero hunknownZero hclockValid hfinishTime hsigma hu
      ledgerDecoded bank hreception
  have hactualObservation : cut.output.coordinator =
      ⟨.collection callInput.registers.payload ledgerFinished
        dispatched.startResult.clock.lastProposal, bank, none, some output,
        (ReferenceActivePhysicalStep.receiveUp cut.output.preparation
          ledgerStarted).diagnostic⟩ := by
    calc
      cut.output.coordinator =
          ReferenceActivePhysicalStep.collectionPostChoice cut.output.preparation
            callInput.registers.payload (sharedLedger ledger) dispatched.startResult
            callInput.registers.complementWeights := hcollectionPost
      _ = ReferenceActivePhysicalStep.collectionFinish
            (x := cut.input) callInput.registers.payload dispatched.startResult output
            (ReferenceActivePhysicalStep.receiveUp cut.output.preparation ledgerStarted) :=
        hcollectionPostStart
      _ = _ := hcollectionFinish
  refine ⟨ledgerFinished, hledgerFinish, hledgerFinishedValid, hclockAll, ?_, ?_, ?_, ?_, ?_⟩
  · exact congrArg ReferenceActivePhysicalStep.CoordinatorObservation.configuration
      hactualObservation
  · exact congrArg ReferenceActivePhysicalStep.CoordinatorObservation.upDecoderBank
      hactualObservation
  · exact congrArg ReferenceActivePhysicalStep.CoordinatorObservation.failure
      hactualObservation
  · exact congrArg ReferenceActivePhysicalStep.CoordinatorObservation.recording
      hactualObservation
  · exact congrArg ReferenceActivePhysicalStep.CoordinatorObservation.up
      hactualObservation

end Bandits.Support.ReferenceFirstCutoffFinishSafety

end
