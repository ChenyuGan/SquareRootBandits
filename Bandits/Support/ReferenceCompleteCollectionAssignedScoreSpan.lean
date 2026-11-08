/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteCollectionIncrementSpan
public import Bandits.Support.ReferenceCompleteFollowerServiceSpan

import Lean.Elab.Tactic.Omega

/-!
# Assigned-arm cutoff scores on the complete physical suffix

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:157-188`,
`sources/zip4/manuscript/06_interruptions.tex:9-100,246-349`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:8-64`.

This module joins the retained installation base to each actually accepted
assigned-arm cutoff register, then combines that cutoff score with the actual
clipped collection increment on the original physical suffix.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceCompleteCollectionAssignedScoreSpan

open ConstructorDimensions
open ReferenceActivePhysicalStep
open ReferenceActivePhysicalHorizon
open CoordinatorCollectionLedger
open CollectionKnownQueueContinuation
open ReferenceCollectionPhaseHistory

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

@[expose] def assignedScoreInvariant (l : Ledger rate) : Prop :=
  ∀ i cut current,
    l.cutoffRegisters (l.assignment.arm i) = some cut →
    l.currentRegisters (l.assignment.arm i) = some current →
    l.baseScore i ≤ cut.score ∧
      cut.score ≤ l.baseScore i + (4 * rate.n) * (l.cutoff - l.sigma) ∧
      cut.lastService ≤ cut.score ∧ cut.lastService ≤ 4 * rate.n

private theorem accepted_up_cutoff_score_bounds
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (c : ReferenceCollectionSegmentExtraction.Choice rate)
    (hchoice : ReferenceCollectionSegmentExtraction.choice
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val].input = some c)
    (i : Fin (p.m - 1)) (U : UpRecord p rate)
    (haccepted : AcceptedUp
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val].input i U) :
    let sigma := c.payload.sigma.val + 1
    let u := FollowerCutoffScan.firstCutoff p rate.eta.val c.payload.sigma
      (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
        (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h)[k.val].input.row)
    ∃ (b j : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length),
      b.val ≤ j.val ∧ j.val < k.val ∧
      ReferenceAssignmentPayloadPersistence.InstallationBirth
        (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h)[b.val] c.payload ∧
      ReferenceAssignmentCollectionMassSteps.installedBaseScore
        (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h)[b.val] = some c.preLedger.baseScore ∧
      c.preLedger.sigma = sigma ∧
      U.val.S ≤ (4 * rate.n) * (u - sigma) ∧
      U.val.delta ≤ U.val.S ∧ U.val.delta ≤ 4 * rate.n := by
  dsimp only
  obtain ⟨b, j, _F, _mu, hbj, hjk, hbirth, hbase, _hretained,
    _hinput, _hlastDown, _hpositive, _hstart, _hUsigma, hledgerSigma,
    _hUS, _hUdelta, _hUq, _hQ, _hbaseQ, hS, _hmass, hdeltaS, hdeltaC⟩ :=
    ReferenceCompleteFollowerServiceSpan.complete_accepted_up_service_span
      rewards C_star C_h source k c hchoice i U haccepted
  exact ⟨b, j, hbj, hjk, hbirth, hbase, hledgerSigma, hS, hdeltaS, hdeltaC⟩

private theorem accepted_cut_register_bounds
    (base : Fin (p.m - 1) → ℕ) (i : Fin (p.m - 1))
    (sigma cutoff capacity service lastService : ℕ)
    (hservice : service ≤ capacity * (cutoff - sigma))
    (hlastService : lastService ≤ service) (hlastCap : lastService ≤ capacity) :
    base i ≤ base i + service ∧
      base i + service ≤ base i + capacity * (cutoff - sigma) ∧
      lastService ≤ base i + service ∧ lastService ≤ capacity := by
  exact ⟨Nat.le_add_right _ _, Nat.add_le_add_left hservice _,
    Nat.le_trans hlastService (Nat.le_add_left _ _), hlastCap⟩

private theorem decode_round_score_frame
    (started decoded : Ledger rate)
    (input : CollectionCheckedExecution.RoundInput (p := p) (eta := rate.eta.val))
    (hdecode : decodeUp started input.selectedFollower input.parsed = .success decoded ∨
      decodeUp started input.selectedFollower input.parsed = .rejected decoded) :
    decoded.assignment = started.assignment ∧ decoded.baseScore = started.baseScore ∧
      decoded.sigma = started.sigma ∧ decoded.cutoff = started.cutoff := by
  rcases hdecode with hsuccess | hrejected
  · cases hparsed : input.parsed with
    | none =>
        simp only [hparsed, decodeUp] at hsuccess
        split at hsuccess
        · split at hsuccess <;> cases hsuccess
        · cases hsuccess
    | some U =>
        have hsuccess' : decodeUp started input.selectedFollower (some U) =
            .success decoded := by simpa only [hparsed] using hsuccess
        obtain ⟨_, _, _, _, _, _, _, _, hcandidate⟩ :=
          CollectionCheckedExecution.decodeUp_success_candidate started decoded
            input.selectedFollower U hsuccess'
        rw [hcandidate]
        simp [CoordinatorCollectionLedger.acceptUpCandidate]
  · rw [CollectionKnownQueueContinuation.decodeUp_rejected_candidate
      started decoded input.selectedFollower input.parsed hrejected]
    exact ⟨rfl, rfl, rfl, rfl⟩

private theorem checked_round_assigned_score
    (l started decoded finished : Ledger rate)
    (input : CollectionCheckedExecution.RoundInput (p := p) (eta := rate.eta.val))
    (hinvariant : assignedScoreInvariant l)
    (hstart : startRound l (sourceRound input.round) input.enabled input.raw =
      .success started)
    (hdecode : decodeUp started input.selectedFollower input.parsed = .success decoded ∨
      decodeUp started input.selectedFollower input.parsed = .rejected decoded)
    (hfinish : finishRound decoded = .success finished)
    (hnew : ∀ U : UpRecord p rate,
      input.parsed = some U →
      decodeUp started input.selectedFollower (some U) = .success decoded →
      l.baseScore input.selectedFollower ≤ l.baseScore input.selectedFollower + U.val.S ∧
      l.baseScore input.selectedFollower + U.val.S ≤
        l.baseScore input.selectedFollower + (4 * rate.n) * (l.cutoff - l.sigma) ∧
      U.val.delta ≤ l.baseScore input.selectedFollower + U.val.S ∧
      U.val.delta ≤ 4 * rate.n) :
    finished.cutoff = l.cutoff ∧ assignedScoreInvariant finished := by
  have hstartFrame := CollectionCheckedExecution.startRound_success_candidate
    l started (sourceRound input.round) input.enabled input.raw hstart
  have hstartAssignment : started.assignment = l.assignment := by
    rw [hstartFrame]
    rfl
  have hstartBase : started.baseScore = l.baseScore := by
    rw [hstartFrame]
    rfl
  have hstartSigma : started.sigma = l.sigma := by
    rw [hstartFrame]
    rfl
  have hstartCutoff : started.cutoff = l.cutoff := by
    rw [hstartFrame]
    rfl
  have hdecodeFrame := decode_round_score_frame started decoded input hdecode
  have hfinishFrame := CollectionCheckedExecution.finishRound_success_candidate
    decoded finished hfinish
  have hfinishAssignment : finished.assignment = l.assignment := by
    calc
      finished.assignment = decoded.assignment := by rw [hfinishFrame]; rfl
      _ = started.assignment := hdecodeFrame.1
      _ = l.assignment := hstartAssignment
  have hfinishBase : finished.baseScore = l.baseScore := by
    calc
      finished.baseScore = decoded.baseScore := by rw [hfinishFrame]; rfl
      _ = started.baseScore := hdecodeFrame.2.1
      _ = l.baseScore := hstartBase
  have hfinishSigma : finished.sigma = l.sigma := by
    calc
      finished.sigma = decoded.sigma := by rw [hfinishFrame]; rfl
      _ = started.sigma := hdecodeFrame.2.2.1
      _ = l.sigma := hstartSigma
  have hfinishCutoff : finished.cutoff = l.cutoff := by
    calc
      finished.cutoff = decoded.cutoff := by rw [hfinishFrame]; rfl
      _ = started.cutoff := hdecodeFrame.2.2.2
      _ = l.cutoff := hstartCutoff
  constructor
  · exact hfinishCutoff
  · intro i cut current hcut hcurrent
    have hcut' : finished.cutoffRegisters (l.assignment.arm i) = some cut := by
      simpa [hfinishAssignment] using hcut
    have hcurrent' : finished.currentRegisters (l.assignment.arm i) = some current := by
      simpa [hfinishAssignment] using hcurrent
    cases hknown : l.currentRegisters (l.assignment.arm i) with
    | some previous =>
        have htransition := CollectionKnownQueueContinuation.checkedRound_known_transition
          l started decoded finished input (l.assignment.arm i) previous hknown hstart
          hdecode hfinish
        rcases htransition with
          ⟨_, _, _, _, _, _, hcutoffPreserved⟩
        have hcutOld : l.cutoffRegisters (l.assignment.arm i) = some cut := by
          rw [hcutoffPreserved] at hcut'
          exact hcut'
        have hbounds := hinvariant i cut previous hcutOld hknown
        simpa [hfinishBase, hfinishSigma, hfinishCutoff] using hbounds
    | none =>
        have hstartCurrent : started.currentRegisters (l.assignment.arm i) = none := by
          rw [hstartFrame]
          simp [CoordinatorCollectionLedger.startRoundCandidate, hknown]
        rcases hdecode with hsuccess | hrejected
        · cases hparsed : input.parsed with
          | none =>
              simp only [hparsed, decodeUp] at hsuccess
              split at hsuccess
              · split at hsuccess <;> cases hsuccess
              · cases hsuccess
          | some U =>
              have hsuccess' : decodeUp started input.selectedFollower (some U) =
                  .success decoded := by simpa only [hparsed] using hsuccess
              obtain ⟨_, _, _, past, currentRecord, _, _, hunknown, hcandidate⟩ :=
                CollectionCheckedExecution.decodeUp_success_candidate started decoded
                  input.selectedFollower U hsuccess'
              have hcurrentCandidate :
                  (CoordinatorCollectionLedger.acceptUpCandidate started
                    input.selectedFollower U past currentRecord).currentRegisters
                      (l.assignment.arm i) = some current := by
                have hdecodedCurrent : decoded.currentRegisters
                    (l.assignment.arm i) = some current := by
                  calc
                    decoded.currentRegisters (l.assignment.arm i) =
                        finished.currentRegisters (l.assignment.arm i) := by
                      rw [hfinishFrame]
                      rfl
                    _ = some current := hcurrent'
                rw [← hcandidate]
                exact hdecodedCurrent
              have harm : l.assignment.arm i =
                  l.assignment.arm input.selectedFollower := by
                by_contra hne
                have hne' : l.assignment.arm i ≠
                    started.assignment.arm input.selectedFollower := by
                  simpa [hstartAssignment] using hne
                have hfalse := hcurrentCandidate
                simp only [CoordinatorCollectionLedger.acceptUpCandidate] at hfalse
                rw [Function.update_of_ne hne'] at hfalse
                rw [hstartCurrent] at hfalse
                cases hfalse
              have hindex : i = input.selectedFollower := l.assignment.injective harm
              subst i
              have hcutCandidate :
                  finished.cutoffRegisters (l.assignment.arm input.selectedFollower) =
                    some ⟨l.baseScore input.selectedFollower + U.val.S,
                      U.val.q, U.val.delta⟩ := by
                have hfields := CoordinatorCollectionLedger.acceptUpCandidate_recovered_fields
                  started input.selectedFollower U past currentRecord
                rw [hfinishFrame, hcandidate]
                simpa [CoordinatorCollectionLedger.finishRoundCandidate,
                  hstartAssignment, hstartBase] using hfields.2.2
              have hcutValue : cut =
                  ⟨l.baseScore input.selectedFollower + U.val.S,
                    U.val.q, U.val.delta⟩ := by
                exact Option.some.inj (hcut'.symm.trans hcutCandidate)
              have hbounds := hnew U hparsed hsuccess'
              simpa [hfinishBase, hfinishSigma, hfinishCutoff, hcutValue] using hbounds
        · have hdecoded := CollectionKnownQueueContinuation.decodeUp_rejected_candidate
            started decoded input.selectedFollower input.parsed hrejected
          rw [hfinishFrame, hdecoded, CoordinatorCollectionLedger.finishRoundCandidate,
            hstartFrame] at hcurrent'
          simp [CoordinatorCollectionLedger.startRoundCandidate, hknown] at hcurrent'

private theorem choice_executed_tail
    (x : RoundInput p rate) (c : ReferenceCollectionSegmentExtraction.Choice rate)
    (hchoice : ReferenceCollectionSegmentExtraction.choice x = some c) :
    ReferenceCollectionPhaseHistory.executedTail x =
      some ⟨c.payload, c.preLedger, c.started, c.weights⟩ := by
  unfold ReferenceCollectionSegmentExtraction.choice at hchoice
  split at hchoice
  · contradiction
  next hselected =>
    unfold ReferenceCollectionPhaseHistory.executedTail
    dsimp only
    split
    · contradiction
    next _ =>
      cases hc : (prepare x).coordinator with
      | first outcome =>
          cases outcome <;>
            simp only [hc, ReferenceCollectionSegmentExtraction.choiceOfCut] at hchoice
          all_goals contradiction
      | live r q base outcome =>
          cases outcome <;>
            simp only [hc, ReferenceCollectionSegmentExtraction.choiceOfCut] at hchoice
          all_goals first | contradiction | (cases Option.some.inj hchoice; rfl)
      | collection payload ledger clock cutoff outcome =>
          cases outcome <;>
            simp only [hc, ReferenceCollectionSegmentExtraction.choiceOfCut] at hchoice
          all_goals first | contradiction | (cases Option.some.inj hchoice; rfl)
      | invalidCollectionCutoff =>
          simp only [hc, ReferenceCollectionSegmentExtraction.choiceOfCut] at hchoice
          contradiction
      | dagger =>
          simp only [hc, ReferenceCollectionSegmentExtraction.choiceOfCut] at hchoice
          contradiction

private theorem collection_tail_assigned_score
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (c : ReferenceCollectionSegmentExtraction.Choice rate)
    (hchoice : ReferenceCollectionSegmentExtraction.choice
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val].input = some c)
    (hinvariant : assignedScoreInvariant c.preLedger)
    (hcutoff : c.preLedger.cutoff =
      FollowerCutoffScan.firstCutoff p rate.eta.val c.payload.sigma
        (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
          (ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate source rewards C_star C_h)[k.val].input.row)) :
    match (collectionPostChoice (prepare
        (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h)[k.val].input)
        c.payload c.preLedger c.started c.weights).configuration with
    | .collection P final _ => P = c.payload ∧ final.cutoff = c.preLedger.cutoff ∧ assignedScoreInvariant final
    | _ => True := by
  let x := (ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h)[k.val].input
  change match (collectionPostChoice (prepare x) c.payload c.preLedger c.started
      c.weights).configuration with
    | .collection P final _ => P = c.payload ∧ final.cutoff = c.preLedger.cutoff ∧ assignedScoreInvariant final
    | _ => True
  unfold collectionPostChoice
  cases hrecord : CoordinatorRecorderComplementBridge.run
      (collectionRecordingInput (prepare x) c.payload c.started c.weights) with
  | none => trivial
  | some recording =>
      dsimp only
      cases hstart : startRound c.preLedger (x.time.val + 1)
          (collectionEnabled c.preLedger x.time)
          (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) with
      | invalid => trivial
      | rejected bad => trivial
      | success started =>
          dsimp only
          unfold collectionFinish
          have hdecodeResult :=
            ReferenceCollectionSegmentExtraction.receiveUp_decode_result x started
          cases hreceive : (receiveUp (prepare x) started).result with
          | invalid => trivial
          | success pair | rejected pair =>
              rcases pair with ⟨decoded, bank⟩
              simp only [hreceive] at hdecodeResult ⊢
              cases hfinish : finishRound decoded with
              | invalid => trivial
              | rejected bad => trivial
              | success finished =>
                  dsimp only
                  cases hclock : CoordinatorPhaseClock.finishRound p rate.eta.val x.time
                      c.started.clock finished.pending x.row with
                  | error reason => trivial
                  | ok clockFinished =>
                      dsimp only
                      let input := ReferenceCollectionSegmentExtraction.inputOf
                        x c.preLedger recording started
                      have hdecode :
                          decodeUp started input.selectedFollower input.parsed =
                            .success decoded ∨
                          decodeUp started input.selectedFollower input.parsed =
                            .rejected decoded := by
                        first | exact Or.inl hdecodeResult | exact Or.inr hdecodeResult
                      have hnew : ∀ U : UpRecord p rate,
                          input.parsed = some U →
                          decodeUp started input.selectedFollower (some U) =
                            .success decoded →
                          c.preLedger.baseScore input.selectedFollower ≤
                              c.preLedger.baseScore input.selectedFollower + U.val.S ∧
                            c.preLedger.baseScore input.selectedFollower + U.val.S ≤
                              c.preLedger.baseScore input.selectedFollower +
                                (4 * rate.n) *
                                  (c.preLedger.cutoff - c.preLedger.sigma) ∧
                            U.val.delta ≤ c.preLedger.baseScore input.selectedFollower +
                                U.val.S ∧ U.val.delta ≤ 4 * rate.n := by
                        intro U hparsed hsuccess
                        have hreception :
                            (receiveUp (prepare x) started).result ≠ .invalid := by
                          rw [hreceive]
                          intro h
                          cases h
                        have hcheck :=
                          ReferenceCollectionSegmentExtraction.receiveUp_input_check
                            x started hreception
                        change ReferenceCollectionSegmentExtraction.effectiveParse
                          x started = some U at hparsed
                        have hrealReceive :
                            (receiveUp (prepare x) started).result =
                              .success (decoded,
                                CoordinatorUpReception.decoderBankAfter
                                  (ReferenceUpReception.receptionInputAtRow rate x.row
                                    (upInputs (prepare x) started) x.time)) := by
                          rw [ReferenceCollectionSegmentExtraction.receiveUp_filtered
                            x started hcheck, hparsed]
                          have hraw : decodeUp started (upSenderIndex x) (some U) =
                              .success decoded := by
                            simpa [input,
                              ReferenceCollectionSegmentExtraction.inputOf] using hsuccess
                          rw [hraw]
                          rfl
                        have haccepted : AcceptedUp x (upSenderIndex x) U := by
                          exact ⟨⟨c.payload, c.preLedger, c.started, c.weights⟩,
                            recording, started, decoded, _,
                            choice_executed_tail x c hchoice, hrecord, hstart,
                            hrealReceive, hparsed, rfl⟩
                        obtain ⟨_b, _j, _hbj, _hjk, _hbirth, _hbase,
                          hledgerSigma, hservice, hlastService, hlastCap⟩ :=
                          accepted_up_cutoff_score_bounds
                            rewards C_star C_h source k c hchoice
                            (upSenderIndex x) U haccepted
                        have hb := accepted_cut_register_bounds
                          c.preLedger.baseScore input.selectedFollower
                          c.preLedger.sigma c.preLedger.cutoff (4 * rate.n)
                          U.val.S U.val.delta
                          (by rw [hcutoff, hledgerSigma]; exact hservice)
                          hlastService hlastCap
                        exact hb
                      have hresult := checked_round_assigned_score
                        c.preLedger started decoded finished input hinvariant
                        hstart hdecode hfinish hnew
                      exact ⟨rfl, hresult.1, hresult.2⟩

private theorem collection_tail_cutoff_frame
    (x : RoundInput p rate) (c : ReferenceCollectionSegmentExtraction.Choice rate) :
    match (collectionPostChoice (prepare x) c.payload c.preLedger c.started c.weights).configuration with
    | .collection P final _ => P = c.payload ∧ final.cutoff = c.preLedger.cutoff
    | _ => True := by
  unfold collectionPostChoice
  cases hrecord : CoordinatorRecorderComplementBridge.run
      (collectionRecordingInput (prepare x) c.payload c.started c.weights) with
  | none => trivial
  | some recording =>
      dsimp only
      cases hstart : startRound c.preLedger (x.time.val + 1)
          (collectionEnabled c.preLedger x.time)
          (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) with
      | invalid => trivial
      | rejected bad => trivial
      | success started =>
          dsimp only
          unfold collectionFinish
          have hdecodeResult := ReferenceCollectionSegmentExtraction.receiveUp_decode_result x started
          cases hreceive : (receiveUp (prepare x) started).result with
          | invalid => trivial
          | success pair | rejected pair =>
              rcases pair with ⟨decoded, bank⟩
              simp only [hreceive] at hdecodeResult ⊢
              cases hfinish : finishRound decoded with
              | invalid => trivial
              | rejected bad => trivial
              | success finished =>
                  dsimp only
                  cases hclock : CoordinatorPhaseClock.finishRound p rate.eta.val x.time
                      c.started.clock finished.pending x.row with
                  | error reason => trivial
                  | ok clockFinished =>
                      dsimp only
                      let input := ReferenceCollectionSegmentExtraction.inputOf
                        x c.preLedger recording started
                      have hdecode :
                          decodeUp started input.selectedFollower input.parsed = .success decoded ∨
                          decodeUp started input.selectedFollower input.parsed = .rejected decoded := by
                        first | exact Or.inl hdecodeResult | exact Or.inr hdecodeResult
                      have hframes := decode_round_score_frame started decoded input hdecode
                      have hstartFrame := CollectionCheckedExecution.startRound_success_candidate
                        c.preLedger started (sourceRound input.round) input.enabled input.raw hstart
                      have hfinishFrame := CollectionCheckedExecution.finishRound_success_candidate
                        decoded finished hfinish
                      constructor
                      · rfl
                      · calc
                          finished.cutoff = decoded.cutoff := by rw [hfinishFrame]; rfl
                          _ = started.cutoff := hframes.2.2.2
                          _ = c.preLedger.cutoff := by rw [hstartFrame]; rfl

private theorem live_tail_no_collection
    (x : RoundInput p rate) (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r) (base : Fin (p.m - 1) → ℕ)
    (started : CoordinatorPhaseClock.StartRoundResult p) :
    match (livePostChoice (prepare x) r q base started).configuration with
    | .collection _ _ _ => False
    | _ => True := by
  unfold livePostChoice
  cases hr : CoordinatorRecorderComplementBridge.run (liveRecordingInput (prepare x) r started) with
  | none => trivial
  | some recording =>
      dsimp only
      cases hs : CoordinatorLiveServiceFinish.servicePass r q recording with
      | error reason => trivial
      | ok serviced =>
          dsimp only
          cases hc : CoordinatorLocalArmChoice.confirmationUpdate r.payload started.pending
              (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
              x.time x.row (prepare x).coordinatorObservation with
          | none => trivial
          | some pending =>
              dsimp only
              cases hf : CoordinatorPhaseClock.finishRound p rate.eta.val x.time
                  started.clock pending x.row with
              | error reason => trivial
              | ok finished => trivial

private theorem complete_record_row
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length) :
    (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val].input.row =
      source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) := by
  cases hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h with
  | none =>
      have hlength := k.isLt
      simp only [ReferenceCompletePhysicalHistory.completeSuffixRecords, hlaunch,
        dite_true, List.length_nil] at hlength
      omega
  | some active =>
      have hrecords := ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
        rate source rewards C_star C_h active hlaunch
      let start := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
      have hspan : start + (p.T - start) ≤ p.T := by
        have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T
          rate source rewards C_star C_h
        dsimp only [start]
        omega
      let execution := ReferenceActivePhysicalHorizon.run active source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start (p.T - start)
        hspan (ReferenceCompletePhysicalHistory.activeMode_of_launch_eq_some
          rate source rewards C_star C_h active hlaunch)
      have hrun : ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h = execution.records := hrecords
      have hmem : (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h)[k.val] ∈ execution.records := by
        rw [← hrun]
        exact List.getElem_mem k.isLt
      have hdata := ReferenceActivePhysicalHorizon.run_record_inputs active source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
        start (p.T - start) hspan _ _ hmem
      exact congrArg₂ (fun rows selected => rows selected) hdata.1 hdata.2.1

private theorem collectionStartLedger_assigned_score
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ) (time : Fin p.T) :
    assignedScoreInvariant
      (ReferenceActivePhysicalStep.sharedLedger
        (CoordinatorStartRoundCutoffDispatch.collectionStartLedger r q base time)) := by
  intro i cut current hcut hcurrent
  have hmem : r.payload.assignment.assigned i ∈ r.payload.slowSet.1 := by
    rw [← r.payload.assignment_image]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have hnone :
      (ReferenceActivePhysicalStep.sharedLedger
        (CoordinatorStartRoundCutoffDispatch.collectionStartLedger r q base time)).cutoffRegisters
          ((ReferenceActivePhysicalStep.sharedLedger
            (CoordinatorStartRoundCutoffDispatch.collectionStartLedger r q base time)).assignment.arm i) =
        none := by
    simp [ReferenceActivePhysicalStep.sharedLedger,
      CoordinatorStartRoundCutoffDispatch.collectionStartLedger,
      CoordinatorStartRoundCutoffDispatch.outsideRegisters,
      CoordinatorStartRoundCutoffDispatch.ledgerAssignment, hmem,
      CanonicalFastSampling.fastArmFinset]
  rw [hnone] at hcut
  cases hcut

private theorem complete_tail_assigned_score
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (c : ReferenceCollectionSegmentExtraction.Choice rate)
    (hchoice : ReferenceCollectionSegmentExtraction.choice
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val].input = some c)
    (hinvariant : assignedScoreInvariant c.preLedger) :
    let x := (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val].input
    match (collectionPostChoice (prepare x) c.payload c.preLedger c.started c.weights).configuration with
    | .collection P final _ => P = c.payload ∧ final.cutoff = c.preLedger.cutoff ∧
        assignedScoreInvariant final
    | _ => True := by
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
  let x := R[k.val].input
  change match (collectionPostChoice (prepare x) c.payload c.preLedger c.started c.weights).configuration with
    | .collection P final _ => P = c.payload ∧ final.cutoff = c.preLedger.cutoff ∧
        assignedScoreInvariant final
    | _ => True
  have hchoiceTail := ReferenceCollectionSegmentExtraction.choice_tail x c hchoice
  have hsuccessor : R[k.val].output.next.coordinator =
      (collectionPostChoice (prepare x) c.payload c.preLedger c.started c.weights).configuration := by
    rw [R[k.val].output_eq]
    exact congrArg ReferenceActivePhysicalStep.CoordinatorObservation.configuration hchoiceTail
  cases he : (collectionPostChoice (prepare x) c.payload c.preLedger c.started c.weights).configuration with
  | first => simp only [x, he]
  | live registers owned base => simp only [x, he]
  | dagger => simp only [x, he]
  | collection P final saved =>
      have hout : R[k.val].output.next.coordinator = .collection P final saved := by
        rw [hsuccessor, he]
      obtain ⟨_b, _hbk, _hbirth, _hbase, _ha, _hsigma, hcutoff, _hfreeze,
        _h1, _h2, _hterminal, _hcursor, _hincrement⟩ :=
        ReferenceCompleteCollectionIncrementSpan.complete_collection_successor_increment_span
          rate rewards C_star C_h source k P final saved hout
      have hframe := collection_tail_cutoff_frame x c
      simp only [he] at hframe
      have hpayload := hframe.1
      have hpreCutoff : c.preLedger.cutoff =
          FollowerCutoffScan.firstCutoff p rate.eta.val c.payload.sigma
            (FollowerCutoffScan.completeRowProposalBit p rate.eta.val x.row) := by
        have hrow := complete_record_row rate rewards C_star C_h source k
        rw [hpayload] at hcutoff
        rw [← hrow] at hcutoff
        exact hframe.2.symm.trans hcutoff
      have hscore := collection_tail_assigned_score rewards C_star C_h source k c hchoice
        hinvariant hpreCutoff
      change match (collectionPostChoice (prepare x) c.payload c.preLedger c.started c.weights).configuration with
        | .collection P final _ => P = c.payload ∧ final.cutoff = c.preLedger.cutoff ∧
            assignedScoreInvariant final
        | _ => True at hscore
      have hscore' : P = c.payload ∧ final.cutoff = c.preLedger.cutoff ∧
          assignedScoreInvariant final := by
        simpa only [he] using hscore
      exact hscore'

private theorem coordinator_round_assigned_score
    (x : RoundInput p rate)
    (hcollection : ∀ P l saved, x.state.coordinator = .collection P l saved →
      assignedScoreInvariant l)
    (htail : ∀ (c : ReferenceCollectionSegmentExtraction.Choice rate),
      ReferenceCollectionSegmentExtraction.choice x = some c →
      assignedScoreInvariant c.preLedger →
      match (collectionPostChoice (prepare x) c.payload c.preLedger c.started c.weights).configuration with
      | .collection P final _ => P = c.payload ∧ final.cutoff = c.preLedger.cutoff ∧
          assignedScoreInvariant final
      | _ => True) :
    match (prepare x).observeCoordinator.configuration with
    | .collection P final _ =>
        ∃ c : ReferenceCollectionSegmentExtraction.Choice rate,
          ReferenceCollectionSegmentExtraction.choice x = some c ∧ P = c.payload ∧
          final.cutoff = c.preLedger.cutoff ∧ assignedScoreInvariant final
    | _ => True := by
  classical
  by_cases hselected : (prepare x).coordinator.selection = none
  · simp only [PreparedRound.observeCoordinator, dite_eq_left hselected]
    cases (prepare x).coordinator <;> trivial
  · simp only [PreparedRound.observeCoordinator, dite_eq_right hselected]
    have hactual : (prepare x).coordinator = dispatch x := rfl
    cases hconfiguration : x.state.coordinator with
    | first =>
        have hcut : (prepare x).coordinator =
            .first (CoordinatorRoundDispatch.dispatchFirst (firstInput x)) := by
          rw [hactual]
          simp only [dispatch, hconfiguration, CoordinatorRoundDispatch.dispatch]
          rfl
        rw [hcut]
        cases ho : CoordinatorRoundDispatch.dispatchFirst (firstInput x)
        all_goals try trivial
        case chosen installed selected =>
          have ht := live_tail_no_collection x installed.registers installed.ownedRegisters
            installed.followerBaseScore installed.startRoundResult
          split at ht <;> simp_all only
    | live r q base =>
        have hcut : (prepare x).coordinator = .live r q base
            (CoordinatorRoundDispatch.dispatchLive (liveInput x r q base)) := by
          rw [hactual]
          simp only [dispatch, hconfiguration, CoordinatorRoundDispatch.dispatch]
          rfl
        rw [hcut]
        cases ho : CoordinatorRoundDispatch.dispatchLive (liveInput x r q base)
        all_goals try trivial
        case continuingChosen dispatched hstart hno selected =>
          have ht := live_tail_no_collection x (liveRegistersAt r x.time)
            (liveOwnedAt r q x.time) base dispatched.startResult
          split at ht <;> simp_all only
        case cutoffChosen dispatched hstart ledger hinit hcandidate hdomains hclock
            hpending hno selected =>
          let c : ReferenceCollectionSegmentExtraction.Choice rate :=
            ⟨r.payload, sharedLedger ledger, dispatched.startResult,
              (liveRegistersAt r x.time).complementWeights,
              some (ReferenceCollectionSegmentExtraction.cutoffInitializer
                (liveRegistersAt r x.time) (liveOwnedAt r q x.time) base x.time)⟩
          have hchoice : ReferenceCollectionSegmentExtraction.choice x = some c := by
            unfold ReferenceCollectionSegmentExtraction.choice
            rw [ite_eq_right hselected, hcut, ho]
            rfl
          have hinv : assignedScoreInvariant c.preLedger := by
            dsimp only [c]
            rw [hcandidate]
            exact collectionStartLedger_assigned_score
              (liveRegistersAt r x.time) (liveOwnedAt r q x.time) base x.time
          have ht := htail c hchoice hinv
          change match (collectionPostChoice (prepare x) c.payload c.preLedger c.started c.weights).configuration with
            | .collection P final _ => _
            | _ => True
          cases he : (collectionPostChoice (prepare x) c.payload c.preLedger c.started c.weights).configuration <;>
            simp only [he] at ht ⊢
          exact ⟨c, hchoice, ht⟩
    | collection old ledger saved =>
        by_cases hcutoff : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
        · let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
          let clock := collectionClock old ledger saved cutoff
          have hcut : (prepare x).coordinator = .collection old ledger clock cutoff
              (CoordinatorRoundDispatch.dispatchCollection
                (collectionInput x old ledger clock cutoff)) := by
            rw [hactual]
            simp only [dispatch, hconfiguration, dite_eq_left hcutoff,
              CoordinatorRoundDispatch.dispatch]
            rfl
          rw [hcut]
          cases ho : CoordinatorRoundDispatch.dispatchCollection
              (collectionInput x old ledger clock cutoff)
          all_goals try trivial
          case continuing core snapshot hcontinue selected =>
            let c : ReferenceCollectionSegmentExtraction.Choice rate :=
              ⟨old, ledger, snapshot.clockStarted,
                CoordinatorCollectionInteractive.PreObservationInputs.weights
                  (collectionInput x old ledger clock cutoff)
                  snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq, none⟩
            have hchoice : ReferenceCollectionSegmentExtraction.choice x = some c := by
              unfold ReferenceCollectionSegmentExtraction.choice
              rw [ite_eq_right hselected, hcut, ho]
              rfl
            have ht := htail c hchoice (hcollection old ledger saved hconfiguration)
            change match (collectionPostChoice (prepare x) c.payload c.preLedger c.started c.weights).configuration with
              | .collection P final _ => _
              | _ => True
            cases he : (collectionPostChoice (prepare x) c.payload c.preLedger c.started c.weights).configuration <;>
              simp only [he] at ht ⊢
            exact ⟨c, hchoice, ht⟩
          case laterChosen core consistent started hstart instruction hinstruction output
              hlocal clockData installed selected =>
            have ht := live_tail_no_collection x installed.registers installed.ownedRegisters
              installed.retainedBaseScore started
            split at ht <;> simp_all only
        · have hcut : (prepare x).coordinator = .invalidCollectionCutoff := by
            rw [hactual]
            simp only [dispatch, hconfiguration, dite_eq_right hcutoff]
          rw [hcut]
          trivial
    | dagger =>
        have hcut : (prepare x).coordinator = .dagger := by
          rw [hactual]
          simp only [dispatch, hconfiguration]
        rw [hcut]
        trivial

private theorem connected_first_input
    {initial final : ReferenceActivePhysicalHorizon.State p rate}
    {records : List (RoundRecord (p := p) (rate := rate))}
    (hconnected : ReferenceActivePhysicalHorizon.Connected initial records final)
    (hfirst : 0 < records.length) :
    records[0].input.state = initial := by
  cases records with
  | nil => simp only [List.length_nil] at hfirst; omega
  | cons record rest =>
      exact hconnected.1

private theorem connected_succ_input
    {initial final : ReferenceActivePhysicalHorizon.State p rate}
    {records : List (RoundRecord (p := p) (rate := rate))}
    (hconnected : ReferenceActivePhysicalHorizon.Connected initial records final)
    (n : ℕ) (hn : n + 1 < records.length) :
    records[n + 1].input.state = records[n].output.next := by
  induction records generalizing initial n with
  | nil => simp only [List.length_nil] at hn; omega
  | cons record rest ih =>
      cases n with
      | zero =>
          cases rest with
          | nil => simp only [List.length_cons, List.length_nil] at hn; omega
          | cons next tail => exact hconnected.2.1
      | succ n => exact ih hconnected.2 n (by simp only [List.length_cons] at hn; omega)

theorem complete_collection_input_output_assigned_score_invariant
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h
    ∀ k : Fin R.length,
      (∀ P l saved, R[k.val].input.state.coordinator = .collection P l saved →
        assignedScoreInvariant l) ∧
      (∀ P l saved, R[k.val].output.next.coordinator = .collection P l saved →
        assignedScoreInvariant l) := by
  classical
  dsimp only
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
  intro k
  cases hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h with
  | none =>
      have hlength := k.isLt
      simp only [ReferenceCompletePhysicalHistory.completeSuffixRecords,
        hlaunch, dite_true, List.length_nil] at hlength
      omega
  | some active =>
      have hc := (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
        rate source rewards C_star C_h).mp (by rw [hlaunch]; rfl)
      let initial := ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hc
      let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
        rate source rewards C_star C_h hc
      have hcanonical := ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
        rate source rewards C_star C_h hc
      have hconnected := ReferenceCompletePhysicalHistory.completeSuffix_connected_on_launch
        rate source rewards C_star C_h initial hcanonical
      have hstep : ∀ (n : Fin R.length),
          (∀ P l saved, R[n.val].input.state.coordinator = .collection P l saved →
            assignedScoreInvariant l) →
          ∀ P l saved, R[n.val].output.next.coordinator = .collection P l saved →
            assignedScoreInvariant l := by
        intro n hinvariant P l saved hout
        have ht := coordinator_round_assigned_score R[n.val].input
          (by intro old ledger proposal hinput; exact hinvariant old ledger proposal hinput)
          (by
            intro c hchoice hInv
            have htail := complete_tail_assigned_score rate rewards C_star C_h source n c hchoice hInv
            simpa only [R] using htail)
        have heq : R[n.val].output.next.coordinator =
            (prepare R[n.val].input).observeCoordinator.configuration := by
          rw [R[n.val].output_eq]
          rfl
        have houtObs : (prepare R[n.val].input).observeCoordinator.configuration =
            .collection P l saved := heq.symm.trans hout
        rw [houtObs] at ht
        obtain ⟨c, _hchoice, _hpayload, _hcutoff, hfinal⟩ := ht
        exact hfinal
      have hfold : ∀ n (hn : n < R.length),
          (∀ P l saved, R[n].input.state.coordinator = .collection P l saved →
            assignedScoreInvariant l) ∧
          (∀ P l saved, R[n].output.next.coordinator = .collection P l saved →
            assignedScoreInvariant l) := by
        intro n
        induction n with
        | zero =>
            intro hn
            have hstate := connected_first_input hconnected hn
            have hin : ∀ P l saved, R[0].input.state.coordinator = .collection P l saved →
                assignedScoreInvariant l := by
              intro P l saved hconfiguration
              rw [hstate, seed.coordinatorFirst] at hconfiguration
              cases hconfiguration
            exact ⟨hin, hstep ⟨0, hn⟩ hin⟩
        | succ n ih =>
            intro hn
            have hnprev : n < R.length := by omega
            obtain ⟨_hin, hout⟩ := ih hnprev
            have hstate := connected_succ_input hconnected n hn
            have hin : ∀ P l saved, R[n + 1].input.state.coordinator = .collection P l saved →
                assignedScoreInvariant l := by
              intro P l saved he
              rw [hstate] at he
              exact hout P l saved he
            exact ⟨hin, hstep ⟨n + 1, hn⟩ hin⟩
      exact hfold k.val k.isLt

/-- Incoming collection endpoint: retains C's actual installation/birth and
clock witnesses, and bounds every queried assigned-arm cutoff and clipped
current score from that same retained base. -/
theorem complete_collection_input_assigned_score_span
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (P : Payload rate) (l : Ledger rate) (saved : Option (Fin p.T × Bool))
    (hinput : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val].input.state.coordinator = .collection P l saved) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
    let J := ActualInitializationPhysicalStep.selectedRowIndex p source
    let bits := FollowerCutoffScan.completeRowProposalBit p rate.eta.val (source.1.2 J)
    ∃ b : Fin R.length, b.val < k.val ∧
      ReferenceAssignmentPayloadPersistence.InstallationBirth R[b.val] P ∧
      ReferenceAssignmentCollectionMassSteps.installedBaseScore R[b.val] = some l.baseScore ∧
      l.assignment.arm = P.assignment.assigned ∧ l.sigma = P.sigma.val + 1 ∧
      l.cutoff = FollowerCutoffScan.firstCutoff p rate.eta.val P.sigma bits ∧
      l.freezeAt = FollowerCutoffScan.gridBoundary p rate.eta.val P.sigma ∧
      1 ≤ l.cutoff ∧ l.cutoff ≤ l.freezeAt ∧ l.freezeAt ≤ p.T + 1 ∧
      l.cutoff ≤ l.cursor ∧ l.cursor = R[k.val].input.time.val + 1 ∧
      (∀ a cut current, l.cutoffRegisters a = some cut →
        l.currentRegisters a = some current →
        l.increment a ≤ 4 * rate.n * (min l.cursor l.freezeAt - l.cutoff)) ∧
    (∀ i cut current, l.cutoffRegisters (l.assignment.arm i) = some cut →
      l.currentRegisters (l.assignment.arm i) = some current →
      l.baseScore i ≤ cut.score ∧
      cut.score ≤ l.baseScore i + (4 * rate.n) * (l.cutoff - l.sigma) ∧
      cut.lastService ≤ cut.score ∧ cut.lastService ≤ 4 * rate.n ∧
      cut.score + l.increment (l.assignment.arm i) ≤
        l.baseScore i + (4 * rate.n) * (min l.cursor l.freezeAt - l.sigma)) := by
  have hspan := ReferenceCompleteCollectionIncrementSpan.complete_collection_input_increment_span
    rate rewards C_star C_h source k P l saved hinput
  have hinvariant := (complete_collection_input_output_assigned_score_invariant
    rate rewards C_star C_h source k).1 P l saved hinput
  have hdata := hspan
  dsimp only at hdata
  obtain ⟨b, hbk, hbirth, hbase, hassignment, hsigma, hcutoff, hfreeze,
    hpositive, hcutFreeze, hterminal, hcutCursor, htime, hincrement⟩ := hdata
  have hfirst := FollowerCutoffScan.firstCutoff_bounds p rate.eta.val
    rate.eta.property rate.sourceCap P.sigma
    (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
      (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)))
  have hsigmaCut : l.sigma ≤ l.cutoff := by
    have hbefore := hfirst.1
    rw [hsigma, hcutoff]
    omega
  have hcutMin : l.cutoff ≤ min l.cursor l.freezeAt :=
    Nat.le_min.mpr ⟨hcutCursor, hcutFreeze⟩
  have hinterval : (l.cutoff - l.sigma) + (min l.cursor l.freezeAt - l.cutoff) =
      min l.cursor l.freezeAt - l.sigma := by omega
  refine ⟨b, hbk, hbirth, hbase, hassignment, hsigma, hcutoff, hfreeze,
    hpositive, hcutFreeze, hterminal, hcutCursor, htime, hincrement, ?_⟩
  intro i cut current hcut hcurrent
  have hscore := hinvariant i cut current hcut hcurrent
  have hinc := hincrement (l.assignment.arm i) cut current hcut hcurrent
  have hcombined : cut.score + l.increment (l.assignment.arm i) ≤
      l.baseScore i + (4 * rate.n) * (min l.cursor l.freezeAt - l.sigma) := by
    calc
      cut.score + l.increment (l.assignment.arm i) ≤
          (l.baseScore i + (4 * rate.n) * (l.cutoff - l.sigma)) +
            (4 * rate.n) * (min l.cursor l.freezeAt - l.cutoff) :=
        Nat.add_le_add hscore.2.1 hinc
      _ = l.baseScore i + (4 * rate.n) *
          ((l.cutoff - l.sigma) + (min l.cursor l.freezeAt - l.cutoff)) := by
        rw [Nat.mul_add]
        omega
      _ = l.baseScore i + (4 * rate.n) * (min l.cursor l.freezeAt - l.sigma) := by
        rw [hinterval]
  exact ⟨hscore.1, hscore.2.1, hscore.2.2.1, hscore.2.2.2, hcombined⟩

/-- Successor collection endpoint: the same actual installation witness and
assigned-arm inequalities hold on the computed output, including cursor T+1. -/
theorem complete_collection_successor_assigned_score_span
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (P : Payload rate) (l : Ledger rate) (saved : Option (Fin p.T × Bool))
    (houtput : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val].output.next.coordinator = .collection P l saved) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
    let J := ActualInitializationPhysicalStep.selectedRowIndex p source
    let bits := FollowerCutoffScan.completeRowProposalBit p rate.eta.val (source.1.2 J)
    ∃ b : Fin R.length, b.val < k.val ∧
      ReferenceAssignmentPayloadPersistence.InstallationBirth R[b.val] P ∧
      ReferenceAssignmentCollectionMassSteps.installedBaseScore R[b.val] = some l.baseScore ∧
      l.assignment.arm = P.assignment.assigned ∧ l.sigma = P.sigma.val + 1 ∧
      l.cutoff = FollowerCutoffScan.firstCutoff p rate.eta.val P.sigma bits ∧
      l.freezeAt = FollowerCutoffScan.gridBoundary p rate.eta.val P.sigma ∧
      1 ≤ l.cutoff ∧ l.cutoff ≤ l.freezeAt ∧ l.freezeAt ≤ p.T + 1 ∧
      l.cutoff ≤ l.cursor ∧ l.cursor = R[k.val].input.time.val + 2 ∧
      (∀ a cut current, l.cutoffRegisters a = some cut →
        l.currentRegisters a = some current →
        l.increment a ≤ 4 * rate.n * (min l.cursor l.freezeAt - l.cutoff)) ∧
    (∀ i cut current, l.cutoffRegisters (l.assignment.arm i) = some cut →
      l.currentRegisters (l.assignment.arm i) = some current →
      l.baseScore i ≤ cut.score ∧
      cut.score ≤ l.baseScore i + (4 * rate.n) * (l.cutoff - l.sigma) ∧
      cut.lastService ≤ cut.score ∧ cut.lastService ≤ 4 * rate.n ∧
      cut.score + l.increment (l.assignment.arm i) ≤
        l.baseScore i + (4 * rate.n) * (min l.cursor l.freezeAt - l.sigma)) := by
  have hspan := ReferenceCompleteCollectionIncrementSpan.complete_collection_successor_increment_span
    rate rewards C_star C_h source k P l saved houtput
  have hinvariant := (complete_collection_input_output_assigned_score_invariant
    rate rewards C_star C_h source k).2 P l saved houtput
  have hdata := hspan
  dsimp only at hdata
  obtain ⟨b, hbk, hbirth, hbase, hassignment, hsigma, hcutoff, hfreeze,
    hpositive, hcutFreeze, hterminal, hcutCursor, htime, hincrement⟩ := hdata
  have hfirst := FollowerCutoffScan.firstCutoff_bounds p rate.eta.val
    rate.eta.property rate.sourceCap P.sigma
    (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
      (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)))
  have hsigmaCut : l.sigma ≤ l.cutoff := by
    have hbefore := hfirst.1
    rw [hsigma, hcutoff]
    omega
  have hcutMin : l.cutoff ≤ min l.cursor l.freezeAt :=
    Nat.le_min.mpr ⟨hcutCursor, hcutFreeze⟩
  have hinterval : (l.cutoff - l.sigma) + (min l.cursor l.freezeAt - l.cutoff) =
      min l.cursor l.freezeAt - l.sigma := by omega
  refine ⟨b, hbk, hbirth, hbase, hassignment, hsigma, hcutoff, hfreeze,
    hpositive, hcutFreeze, hterminal, hcutCursor, htime, hincrement, ?_⟩
  intro i cut current hcut hcurrent
  have hscore := hinvariant i cut current hcut hcurrent
  have hinc := hincrement (l.assignment.arm i) cut current hcut hcurrent
  have hcombined : cut.score + l.increment (l.assignment.arm i) ≤
      l.baseScore i + (4 * rate.n) * (min l.cursor l.freezeAt - l.sigma) := by
    calc
      cut.score + l.increment (l.assignment.arm i) ≤
          (l.baseScore i + (4 * rate.n) * (l.cutoff - l.sigma)) +
            (4 * rate.n) * (min l.cursor l.freezeAt - l.cutoff) :=
        Nat.add_le_add hscore.2.1 hinc
      _ = l.baseScore i + (4 * rate.n) *
          ((l.cutoff - l.sigma) + (min l.cursor l.freezeAt - l.cutoff)) := by
        rw [Nat.mul_add]
        omega
      _ = l.baseScore i + (4 * rate.n) * (min l.cursor l.freezeAt - l.sigma) := by
        rw [hinterval]
  exact ⟨hscore.1, hscore.2.1, hscore.2.2.1, hscore.2.2.2, hcombined⟩

end Bandits.Support.ReferenceCompleteCollectionAssignedScoreSpan

end
