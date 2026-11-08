/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteCoordinatorMass

import Lean.Elab.Tactic.Omega

/-!
# Actual continuing collection ledger finish

Sources: `sources/zip4/manuscript/06_interruptions.tex:9-100,164-177,246-299`,
`sources/zip4/manuscript/04_slow_fast_learner.tex:157-174`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:8-64`.

The producer below follows the actual complete physical suffix and the
literal continuing collection recorder, START, and filtered UP reception.
It proves the checked ledger FINISH after either ordinary acceptance or
rejection. It does not establish the recorder, START, reception, or phase
clock finish checks.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceCompleteContinuingCollectionFinish

open ConstructorDimensions
open ReferenceActivePhysicalStep
open CoordinatorCollectionLedger
open ReferenceCollectionSegmentExtraction
open ReferenceCollectionPhaseHistory
open CollectionKnownQueueContinuation

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

private theorem allFin_eq_true_iff {length : ℕ} (test : Fin length → Bool) :
    CoordinatorCollectionLedger.allFin length test = true ↔ ∀ i, test i = true := by
  unfold CoordinatorCollectionLedger.allFin
  rw [List.all_eq_true]
  constructor
  · intro hall i
    exact hall (test i) (by simp)
  · intro hall value hvalue
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp hvalue
    subst value
    exact hall i

private theorem registerDomainsCheck_of_validLedgerCheck
    (l : Ledger rate) (h : validLedgerCheck l = true) :
    registerDomainsCheck l = true := by
  have hparts := h
  simp only [validLedgerCheck, Bool.and_eq_true] at hparts
  exact hparts.1.2

private theorem increment_le_of_registerDomainsCheck
    (l : Ledger rate) (h : registerDomainsCheck l = true) (a : Fin p.K) :
    l.increment a ≤ p.T * D p := by
  have hparts := h
  simp only [registerDomainsCheck, Bool.and_eq_true] at hparts
  have hall : allFin p.K
      (fun a : Fin p.K => decide (l.increment a ≤ p.T * D p)) = true := hparts.1.2
  have hall := (allFin_eq_true_iff _).1 hall
  exact of_decide_eq_true (hall a)

private theorem armPendingCheck_eq_true_iff
    (l : Ledger rate) (a : Fin p.K) :
    armPendingCheck l a = true ↔ armPending l a := by
  unfold armPendingCheck anyFin
  rw [List.any_eq_true]
  simp [armPending]

private theorem armPendingCheck_finishRoundCandidate
    (l : Ledger rate) (a : Fin p.K) :
    armPendingCheck (finishRoundCandidate l) a = armPendingCheck l a := by
  rfl

private theorem currentRegister_none_iff_cutoffRegister_none
    (l : Ledger rate) (hvalid : validLedgerCheck l = true) (a : Fin p.K)
    : l.currentRegisters a = none ↔ l.cutoffRegisters a = none := by
  have hparts := hvalid
  simp only [validLedgerCheck, Bool.and_eq_true] at hparts
  rcases hparts with ⟨hparts, _⟩
  rcases hparts with ⟨hparts, _⟩
  rcases hparts with ⟨hparts, _⟩
  rcases hparts with ⟨hparts, _⟩
  rcases hparts with ⟨hparts, hcutoffPending⟩
  rcases hparts with ⟨_, hcurrentPending⟩
  have hcurrentBool : (l.currentRegisters a).isNone = armPendingCheck l a := by
    have h := (allFin_eq_true_iff _).1 hcurrentPending a
    simpa only [beq_iff_eq] using h
  have hcutoffBool : (l.cutoffRegisters a).isNone = armPendingCheck l a := by
    have h := (allFin_eq_true_iff _).1 hcutoffPending a
    simpa only [beq_iff_eq] using h
  have hsame : (l.currentRegisters a).isNone = (l.cutoffRegisters a).isNone :=
    hcurrentBool.trans hcutoffBool.symm
  constructor
  · intro hcurrent
    have hcurrentNone : (l.currentRegisters a).isNone = true := by simp [hcurrent]
    have hcutoffNone : (l.cutoffRegisters a).isNone = true := by
      rw [← hsame]
      exact hcurrentNone
    cases hc : l.cutoffRegisters a with
    | none => rfl
    | some current => simp [hc] at hcutoffNone
  · intro hcutoff
    have hcutoffNone : (l.cutoffRegisters a).isNone = true := by simp [hcutoff]
    have hcurrentNone : (l.currentRegisters a).isNone = true := by
      rw [hsame]
      exact hcutoffNone
    cases hc : l.currentRegisters a with
    | none => rfl
    | some current => simp [hc] at hcurrentNone

private theorem armPendingCheckFunction_finishRoundCandidate
    (l : Ledger rate) :
    armPendingCheck (finishRoundCandidate l) = armPendingCheck l := by
  funext a
  exact armPendingCheck_finishRoundCandidate l a

private theorem finishCandidate_valid_of_checked
    (l : Ledger rate)
    (hvalid : validLedgerCheck l = true)
    (hphase : l.phase = Phase.decoded)
    (hcursor : l.cursor ≤ p.T)
    (hslack : ∀ a, l.increment a + l.gammaLoc a ≤ p.T * D p) :
    validLedgerCheck (finishRoundCandidate l) = true := by
  classical
  have hparts := hvalid
  simp [validLedgerCheck, hphase, Bool.and_eq_true] at hparts
  rcases hparts with ⟨hparts, hraw⟩
  rcases hparts with ⟨hparts, hregisters⟩
  rcases hparts with ⟨hparts, hincrementPending⟩
  rcases hparts with ⟨hparts, hgammaPending⟩
  rcases hparts with ⟨hparts, hcutoffPending⟩
  rcases hparts with ⟨hparts, hcurrentPending⟩
  rcases hparts with ⟨hscalars, hstartedHistory⟩
  have hregisterParts := hregisters
  simp only [registerDomainsCheck, Bool.and_eq_true] at hregisterParts
  rcases hregisterParts with ⟨hregisterParts, hgammaDomain⟩
  rcases hregisterParts with ⟨hregisterParts, hincrementDomain⟩
  rcases hregisterParts with ⟨hregisterParts, hbaseDomain⟩
  rcases hregisterParts with ⟨hcurrentDomain, hcutoffDomain⟩
  have hreadyHistory : readyHistoryCheck (finishRoundCandidate l) = true := by
    apply (allFin_eq_true_iff _).2
    intro r
    have hr := (allFin_eq_true_iff _).1 hstartedHistory r
    by_cases hbefore : sourceRound r < l.cutoff
    · simp [finishRoundCandidate, hbefore]
    · have hentry : (l.enabledHistory r).isSome = decide (sourceRound r ≤ l.cursor) := by
        simpa [startedHistoryCheck, hbefore] using hr
      have hdate : sourceRound r < l.cursor + 1 ↔ sourceRound r ≤ l.cursor := by omega
      simp [finishRoundCandidate, hbefore, hentry, hdate]
  have hcurrentPendingCandidate : allFin p.K (fun a : Fin p.K =>
      ((finishRoundCandidate l).currentRegisters a).isNone ==
        armPendingCheck (finishRoundCandidate l) a) = true := by
    change allFin p.K (fun a : Fin p.K =>
      (l.currentRegisters a).isNone == armPendingCheck l a) = true
    exact hcurrentPending
  have hcutoffPendingCandidate : allFin p.K (fun a : Fin p.K =>
      ((finishRoundCandidate l).cutoffRegisters a).isNone ==
        armPendingCheck (finishRoundCandidate l) a) = true := by
    change allFin p.K (fun a : Fin p.K =>
      (l.cutoffRegisters a).isNone == armPendingCheck l a) = true
    exact hcutoffPending
  have hpendingIncrementCandidate : allFin p.K (fun a : Fin p.K =>
      (!armPendingCheck (finishRoundCandidate l) a) ||
        decide ((finishRoundCandidate l).increment a = 0)) = true := by
    apply (allFin_eq_true_iff _).2
    intro a
    by_cases hp : armPendingCheck l a = true
    · have hgamma := (allFin_eq_true_iff _).1 hgammaPending a
      have hinc := (allFin_eq_true_iff _).1 hincrementPending a
      have hgammaZero : l.gammaLoc a = 0 := of_decide_eq_true (by
        simpa [hp] using hgamma)
      have hincZero : l.increment a = 0 := of_decide_eq_true (by
        simpa [hp] using hinc)
      rw [armPendingCheck_finishRoundCandidate]
      simp [finishRoundCandidate, hp, hgammaZero, hincZero]
    · have hpFalse : armPendingCheck l a = false := Bool.eq_false_of_not_eq_true hp
      rw [armPendingCheck_finishRoundCandidate]
      simp [hpFalse]
  have hpendingGammaCandidate : allFin p.K (fun a : Fin p.K =>
      (!armPendingCheck (finishRoundCandidate l) a) ||
        decide ((finishRoundCandidate l).gammaLoc a = 0)) = true := by
    apply (allFin_eq_true_iff _).2
    intro a
    rw [armPendingCheck_finishRoundCandidate]
    simp [finishRoundCandidate]
  have hphaseReady : decide ((finishRoundCandidate l).phase = Phase.ready) = true := by
    simp [finishRoundCandidate]
  have hnumeric : registerDomainsCheck (finishRoundCandidate l) = true := by
    have hnewIncrement : allFin p.K (fun a : Fin p.K =>
        decide ((finishRoundCandidate l).increment a ≤ p.T * D p)) = true := by
      apply (allFin_eq_true_iff _).2
      intro a
      exact decide_eq_true (by simpa [finishRoundCandidate] using hslack a)
    have hnewGamma : allFin p.K (fun a : Fin p.K =>
        decide ((finishRoundCandidate l).gammaLoc a ≤ D p)) = true := by
      apply (allFin_eq_true_iff _).2
      intro a
      simp [finishRoundCandidate]
    unfold registerDomainsCheck
    simp only [Bool.and_eq_true]
    exact ⟨⟨⟨⟨hcurrentDomain, hcutoffDomain⟩, hbaseDomain⟩,
      hnewIncrement⟩, hnewGamma⟩
  have hraw : rawEntryDomainsCheck (finishRoundCandidate l) = true := by
    apply (allFin_eq_true_iff _).2
    intro a
    apply (allFin_eq_true_iff _).2
    intro r
    have hrawSource := hraw
    unfold rawEntryDomainsCheck at hrawSource
    rw [hphase] at hrawSource
    have houter : allFin p.K (fun a : Fin p.K => allFin p.T (fun r : Fin p.T =>
        match l.rawBuffer a r with
        | none => true
        | some amount => decide (0 < amount) && decide (amount ≤ D p) &&
            decide (l.cutoff ≤ sourceRound r) && decide (sourceRound r < l.freezeAt) &&
            decide (sourceRound r ≤ l.cursor) && armPendingCheck l a)) = true := by
      exact hrawSource
    have hrow := (allFin_eq_true_iff _).1 houter a
    have hcell := (allFin_eq_true_iff _).1 hrow r
    have hdate : sourceRound r < l.cursor + 1 ↔ sourceRound r ≤ l.cursor := by omega
    rw [armPendingCheck_finishRoundCandidate]
    change (match l.rawBuffer a r with
      | none => true
      | some amount => decide (0 < amount) && decide (amount ≤ D p) &&
          decide (l.cutoff ≤ sourceRound r) && decide (sourceRound r < l.freezeAt) &&
          decide (sourceRound r ≤ l.cursor) && armPendingCheck l a) = true
    exact hcell
  have hnewGammaZero : allFin p.K (fun a : Fin p.K =>
      decide ((finishRoundCandidate l).gammaLoc a = 0)) = true := by
    apply (allFin_eq_true_iff _).2
    intro a
    simp [finishRoundCandidate]
  have hscalar :
      1 ≤ l.sigma ∧ l.sigma ≤ p.T ∧ 1 ≤ l.cutoff ∧ l.cutoff ≤ l.freezeAt ∧
      l.cutoff ≤ p.T ∧ l.freezeAt ≤ p.T + 1 ∧ l.cutoff ≤ l.cursor ∧
      l.cursor ≤ p.T + 1 ∧ l.cursor ≤ p.T := by omega
  rcases hscalar with ⟨hsigmaPos, hsigmaT, hcutPos, hcutFreeze, hcutT,
    hfreeze, hcutCursorOld, hcursorT1, hcursorT⟩
  have hcursorBound : (finishRoundCandidate l).cursor ≤ p.T + 1 := by
    simp [finishRoundCandidate]
    omega
  have hcutCursor : (finishRoundCandidate l).cutoff ≤
      (finishRoundCandidate l).cursor := by
    simp [finishRoundCandidate]
    omega
  have hscalarCandidate :
      1 ≤ (finishRoundCandidate l).sigma ∧
      (finishRoundCandidate l).sigma ≤ p.T ∧
      1 ≤ (finishRoundCandidate l).cutoff ∧
      (finishRoundCandidate l).cutoff ≤ (finishRoundCandidate l).freezeAt ∧
      (finishRoundCandidate l).cutoff ≤ p.T ∧
      (finishRoundCandidate l).freezeAt ≤ p.T + 1 ∧
      (finishRoundCandidate l).cutoff ≤ (finishRoundCandidate l).cursor ∧
      (finishRoundCandidate l).cursor ≤ p.T + 1 := by
    exact ⟨hsigmaPos, hsigmaT, hcutPos, hcutFreeze, hcutT, hfreeze,
      hcutCursor, hcursorBound⟩
  simp only [validLedgerCheck, Bool.and_eq_true]
  simp [hscalarCandidate, hphaseReady, hreadyHistory,
    hcurrentPendingCandidate, hcutoffPendingCandidate, hpendingGammaCandidate,
    hpendingIncrementCandidate, hnumeric, hnewGammaZero, hraw]

private theorem decodeUp_tag_domain
    (l : Ledger rate) (i : Fin (p.m - 1))
    (parsed : Option (OrdinaryMessageCodec.UpRecord (codecParams p rate.eta.val)))
    (decoded : Ledger rate)
    (hdecode : decodeUp l i parsed = .success decoded ∨
      decodeUp l i parsed = .rejected decoded) :
    validLedgerCheck l = true ∧ l.phase = Phase.started ∧
      1 ≤ l.cutoff ∧ l.cutoff ≤ l.cursor ∧ l.cursor ≤ p.T := by
  by_contra hnot
  unfold decodeUp at hdecode
  rw [dite_eq_right hnot] at hdecode
  cases hdecode <;> simp at *

private theorem decodeUp_success_valid
    (l : Ledger rate) (i : Fin (p.m - 1))
    (parsed : Option (OrdinaryMessageCodec.UpRecord (codecParams p rate.eta.val)))
    (decoded : Ledger rate)
    (hdomain : validLedgerCheck l = true ∧ l.phase = Phase.started ∧
      1 ≤ l.cutoff ∧ l.cutoff ≤ l.cursor ∧ l.cursor ≤ p.T)
    (hdecode : decodeUp l i parsed = .success decoded) :
    validLedgerCheck decoded = true := by
  classical
  cases parsed with
  | none =>
      have hdecodedValid := CoordinatorUpReception.validLedgerCheck_after_decode
        l hdomain.1 hdomain.2.1
      have hdecodedValid' : validLedgerCheck
          (show Ledger rate from { l with phase := Phase.decoded }) = true := by
        simpa [CoordinatorUpReception.decodePhaseCandidate] using hdecodedValid
      simp [decodeUp, hdomain, hdecodedValid'] at hdecode
  | some M =>
      obtain ⟨hbound, lastIndex, hindex, past, current, hpast, hcurrent,
        hunknown, hcandidate⟩ :=
        CollectionCheckedExecution.decodeUp_success_candidate l decoded i M hdecode
      have hcutoffUnknown :=
        (currentRegister_none_iff_cutoffRegister_none l hdomain.1
          (l.assignment.arm i)).1 hunknown
      have haccept : acceptUpCheck l i M = true := by
        by_contra hnot
        have hdecodedValid := CoordinatorUpReception.validLedgerCheck_after_decode
          l hdomain.1 hdomain.2.1
        have hdecodedValid' : validLedgerCheck
            (show Ledger rate from { l with phase := Phase.decoded }) = true := by
          simpa [CoordinatorUpReception.decodePhaseCandidate] using hdecodedValid
        unfold decodeUp at hdecode
        rw [dite_eq_left hdomain] at hdecode
        simp [hnot, hdecodedValid'] at hdecode
      have hcandidateValid : validLedgerCheck
          (acceptUpCandidate l i M past current) = true := by
        have hlast : lastIndex =
            (⟨l.cursor - 1, by omega⟩ : Fin p.T) := by
          apply Fin.ext
          have hsucc : lastIndex.val + 1 = l.cursor := by
            simpa [sourceRound] using hindex
          calc
            lastIndex.val = (lastIndex.val + 1) - 1 := by omega
            _ = l.cursor - 1 := by rw [hsucc]
        have hcurrentCanonical : replayRecords? l (l.assignment.arm i)
            [⟨l.cursor - 1, by omega⟩] = some [current] := by
          rw [← hlast]
          exact hcurrent
        by_cases hout : replayOutputDomainsCheck (p := p) (4 * rate.n) M.val.q
            (past ++ [current]) = true
        · by_cases hvalid : validLedgerCheck
              (acceptUpCandidate l i M past current) = true
          · exact hvalid
          · have hbad : decodeUp l i (some M) = .invalid := by
              unfold decodeUp
              rw [dite_eq_left hdomain]
              simp [haccept, hunknown, hcutoffUnknown,
                hpast, hcurrentCanonical, hout, hvalid]
            rw [hbad] at hdecode
            cases hdecode
        · have hbad : decodeUp l i (some M) = .invalid := by
            unfold decodeUp
            rw [dite_eq_left hdomain]
            simp [haccept, hunknown, hcutoffUnknown,
              hpast, hcurrentCanonical, hout]
          rw [hbad] at hdecode
          cases hdecode
      simpa [hcandidate] using hcandidateValid

private theorem startRound_success_input
    (l started : Ledger rate) (t : ℕ) (enabled : Bool)
    (raw : Option (Fin p.K × ℕ))
    (hstart : startRound l t enabled raw = .success started) :
    validLedgerCheck l = true ∧ l.phase = Phase.ready ∧ t = l.cursor ∧
      1 ≤ t ∧ t ≤ p.T ∧ rawInputDomainCheck raw = true := by
  classical
  unfold startRound at hstart
  by_cases hinput : validLedgerCheck l = true ∧ l.phase = Phase.ready ∧
      t = l.cursor ∧ 1 ≤ t ∧ t ≤ p.T ∧ rawInputDomainCheck raw = true
  · rw [dite_eq_left hinput] at hstart
    exact hinput
  · rw [dite_eq_right hinput] at hstart
    cases hstart

private theorem collection_start_arrival_cap
    (l started : Ledger rate) (r : Fin p.T) (enabled : Bool)
    (raw : Option (Fin p.K × ℕ))
    (hstart : startRound l (sourceRound r) enabled raw = .success started)
    (a : Fin p.K) :
    (localQueueRecord l r enabled raw a).2 ≤ D p := by
  have hinput := startRound_success_input l started (sourceRound r) enabled raw hstart
  have hcap : rawInputDomainCheck raw = true := hinput.2.2.2.2.2
  unfold localQueueRecord
  split
  · dsimp only
    cases raw with
    | none => exact Nat.zero_le _
    | some entry =>
        rcases entry with ⟨arm, amount⟩
        have ham : amount ≤ D p := by simpa [rawInputDomainCheck] using hcap
        change (if arm = a then amount else 0) ≤ D p
        split
        · exact ham
        · exact Nat.zero_le _
  · exact Nat.zero_le _

private theorem choice_executedTail
    (x : RoundInput p rate) (c : Choice rate)
    (hchoice : choice x = some c) :
    ReferenceCollectionPhaseHistory.executedTail x =
      some ⟨c.payload, c.preLedger, c.started, c.weights⟩ := by
  unfold choice at hchoice
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
            simp only [hc, choiceOfCut] at hchoice
          all_goals contradiction
      | live r q base outcome =>
          cases outcome <;>
            simp only [hc, choiceOfCut] at hchoice
          all_goals first | contradiction | (cases Option.some.inj hchoice; rfl)
      | collection payload ledger clock cutoff outcome =>
          cases outcome <;>
            simp only [hc, choiceOfCut] at hchoice
          all_goals first | contradiction | (cases Option.some.inj hchoice; rfl)
      | invalidCollectionCutoff =>
          simp only [hc, choiceOfCut] at hchoice
          contradiction
      | dagger =>
          simp only [hc, choiceOfCut] at hchoice
          contradiction

private theorem choice_preLedger_eq
    (x : RoundInput p rate) (P : Payload rate) (l : Ledger rate)
    (saved : Option (Fin p.T × Bool)) (c : Choice rate)
    (hstate : x.state.coordinator = .collection P l saved)
    (hchoice : choice x = some c) : c.preLedger = l := by
  let tail : ReferenceCollectionPhaseHistory.Tail x :=
    ⟨c.payload, c.preLedger, c.started, c.weights⟩
  have htail : ReferenceCollectionPhaseHistory.executedTail x = some tail := by
    simpa [tail] using choice_executedTail x c hchoice
  have horigin := ReferenceCollectionPhaseHistory.executedTail_origin htail
  have hcutoffFalse : cutoffChosen x = false := by
    unfold cutoffChosen
    cases he : (ReferenceActivePhysicalStep.prepare x).coordinator with
    | live registers owned base outcome =>
        simp only [ReferenceActivePhysicalStep.prepare,
          ReferenceActivePhysicalStep.dispatch, hstate] at he
        split at he
        · split at he; cases he
        · cases he
    | first outcome => rfl
    | collection payload ledger clock cutoff outcome => rfl
    | invalidCollectionCutoff => rfl
    | dagger => rfl
  rcases horigin.2 with hcutoff | hcontinuing
  · rw [hcutoffFalse] at hcutoff
    cases hcutoff.1
  · rcases hcontinuing with ⟨_, payload, ledger, saved', hstate', hledger⟩
    rw [hstate] at hstate'
    cases hstate'
    exact (show tail.ledger = c.preLedger from rfl).symm.trans hledger

private theorem startRound_success_valid
    (l started : Ledger rate) (r : Fin p.T) (enabled : Bool)
    (raw : Option (Fin p.K × ℕ))
    (hstart : startRound l (sourceRound r) enabled raw = .success started) :
    validLedgerCheck started = true ∧ started.phase = Phase.started ∧
      started.cursor = sourceRound r := by
  have hinput := startRound_success_input l started (sourceRound r) enabled raw hstart
  have hvalidStarted : validLedgerCheck started = true := by
    unfold startRound at hstart
    by_cases hcond : validLedgerCheck l = true ∧ l.phase = Phase.ready ∧
        sourceRound r = l.cursor ∧ 1 ≤ sourceRound r ∧
        sourceRound r ≤ p.T ∧ rawInputDomainCheck raw = true
    · rcases hcond with ⟨hlvalid, hlphase, htime, hlow, hhigh, hraw⟩
      rw [htime] at hstart
      have hlowCursor : 1 ≤ l.cursor := by omega
      have hhighCursor : l.cursor ≤ p.T := by omega
      let idx : Fin p.T := ⟨l.cursor - 1, by omega⟩
      by_cases hslot : rawSlotFreshCheck l idx raw = true
      · let candidate := startRoundCandidate l idx enabled raw
        by_cases hcandidate : validLedgerCheck candidate = true
        · have heq : startRound l l.cursor enabled raw = .success candidate := by
            simp [startRound, hlvalid, hlphase, hraw,
              hlowCursor, hhighCursor, idx, hslot, candidate, hcandidate]
          have hresult : candidate = started :=
            Checked.success.inj (heq.symm.trans hstart)
          rw [← hresult]
          exact hcandidate
        · simp [hlvalid, hlphase, hraw,
            hlowCursor, hhighCursor, idx, hslot, candidate, hcandidate] at hstart
      · simp [hlvalid, hlphase, hlowCursor, hhighCursor, hraw,
          idx, hslot] at hstart
    · simp [hcond] at hstart
  have hcursor := CollectionCheckedExecution.startRound_success_cursor
    l started (sourceRound r) enabled raw hstart
  have hcand := CollectionCheckedExecution.startRound_success_candidate
    l started (sourceRound r) enabled raw hstart
  have hphase : started.phase = Phase.started := by
    rw [hcand]
    simp [startRoundCandidate]
  exact ⟨hvalidStarted, hphase, hcursor⟩

private theorem decoded_tag_fields
    (started decoded : Ledger rate) (i : Fin (p.m - 1))
    (parsed : Option (OrdinaryMessageCodec.UpRecord (codecParams p rate.eta.val)))
    (hdecode : decodeUp started i parsed = .success decoded ∨
      decodeUp started i parsed = .rejected decoded) :
    validLedgerCheck decoded = true ∧ decoded.phase = Phase.decoded ∧
      decoded.cursor = started.cursor ∧
      (∀ a, decoded.gammaLoc a = started.gammaLoc a) := by
  have hdomain := decodeUp_tag_domain started i parsed decoded hdecode
  rcases hdecode with hsuccess | hrejected
  · have hvalid := decodeUp_success_valid started i parsed decoded hdomain hsuccess
    have hphase : decoded.phase = Phase.decoded := by
      cases parsed with
      | none =>
          have hdecodedValid := CoordinatorUpReception.validLedgerCheck_after_decode
            started hdomain.1 hdomain.2.1
          have hdecodedValid' : validLedgerCheck
              (show Ledger rate from { started with phase := Phase.decoded }) = true := by
            simpa [CoordinatorUpReception.decodePhaseCandidate] using hdecodedValid
          unfold decodeUp at hsuccess
          rw [dite_eq_left hdomain] at hsuccess
          simp [hdecodedValid'] at hsuccess
      | some M =>
          obtain ⟨_, _, _, _, _, _, _, _, hcandidate⟩ :=
            CollectionCheckedExecution.decodeUp_success_candidate
              started decoded i M hsuccess
          rw [hcandidate]
          rfl
    have hcursor := CollectionCheckedExecution.decodeUp_cursor_behavior
      started i parsed
    have hcursor' : decoded.cursor = started.cursor := by
      rw [hsuccess] at hcursor
      exact hcursor.1
    have hgamma : ∀ a, decoded.gammaLoc a = started.gammaLoc a := by
      intro a
      cases parsed with
      | none =>
          have hdecodedValid := CoordinatorUpReception.validLedgerCheck_after_decode
            started hdomain.1 hdomain.2.1
          have hdecodedValid' : validLedgerCheck
              (show Ledger rate from { started with phase := Phase.decoded }) = true := by
            simpa [CoordinatorUpReception.decodePhaseCandidate] using hdecodedValid
          unfold decodeUp at hsuccess
          rw [dite_eq_left hdomain] at hsuccess
          simp [hdecodedValid'] at hsuccess
      | some M =>
          obtain ⟨_, _, _, _, _, _, _, _, hcandidate⟩ :=
            CollectionCheckedExecution.decodeUp_success_candidate
              started decoded i M hsuccess
          rw [hcandidate]
          rfl
    exact ⟨hvalid, hphase, hcursor', hgamma⟩
  · have hcandidate := CollectionBufferProvenance.decodeUp_rejected_phase_candidate
      started decoded i parsed hrejected
    have hvalid := CoordinatorUpReception.validLedgerCheck_after_decode
      started hdomain.1 hdomain.2.1
    rw [hcandidate]
    exact ⟨hvalid, rfl, rfl, fun _ => rfl⟩

private theorem decodeUp_preserves_known_registers
    (started decoded : Ledger rate) (i : Fin (p.m - 1))
    (parsed : Option (OrdinaryMessageCodec.UpRecord (codecParams p rate.eta.val)))
    (a : Fin p.K) (current : CurrentRegister)
    (hknown : started.currentRegisters a = some current)
    (hdecode : decodeUp started i parsed = .success decoded ∨
      decodeUp started i parsed = .rejected decoded) :
    decoded.increment a = started.increment a ∧
      decoded.gammaLoc a = started.gammaLoc a := by
  rcases hdecode with hsuccess | hrejected
  · cases parsed with
    | none =>
        have hdomain := decodeUp_tag_domain started i none decoded (Or.inl hsuccess)
        have hdecodedValid := CoordinatorUpReception.validLedgerCheck_after_decode
          started hdomain.1 hdomain.2.1
        have hdecodedValid' : validLedgerCheck
            (show Ledger rate from { started with phase := Phase.decoded }) = true := by
          simpa [CoordinatorUpReception.decodePhaseCandidate] using hdecodedValid
        unfold decodeUp at hsuccess
        rw [dite_eq_left hdomain] at hsuccess
        simp [hdecodedValid'] at hsuccess
    | some M =>
        have hpreserve := CollectionKnownQueueContinuation.decodeUp_success_preserves_known
          started decoded i M a current hknown hsuccess
        exact ⟨hpreserve.2.1, hpreserve.2.2.1⟩
  · have hpreserve := CollectionKnownQueueContinuation.decodeUp_rejected_preserves_known
      started decoded i parsed a current hknown hrejected
    exact ⟨hpreserve.2.1, hpreserve.2.2.1⟩

private theorem decoded_all_arm_slack_of_input_mass
    (l started decoded : Ledger rate) (r : Fin p.T)
    (enabled : Bool) (raw : Option (Fin p.K × ℕ))
    (i : Fin (p.m - 1))
    (parsed : Option (OrdinaryMessageCodec.UpRecord (codecParams p rate.eta.val)))
    (hstart : startRound l (sourceRound r) enabled raw = .success started)
    (hdecode : decodeUp started i parsed = .success decoded ∨
      decodeUp started i parsed = .rejected decoded)
    (hvalidDecoded : validLedgerCheck decoded = true)
    (hgammaPreserved : ∀ a, decoded.gammaLoc a = started.gammaLoc a)
    (hmass : ∀ (a : Fin p.K) (cutoff : CutoffRegister) (current : CurrentRegister),
      l.cutoffRegisters a = some cutoff → l.currentRegisters a = some current →
      cutoff.score + l.increment a + current.queue ≤ r.val * D p) :
    ∀ a, decoded.increment a + decoded.gammaLoc a ≤ p.T * D p := by
  have hstartFields := startRound_success_valid l started r enabled raw hstart
  have hindex : (⟨sourceRound r - 1, by
      have hr := r.isLt
      simp [sourceRound]⟩ : Fin p.T) = r := by
    apply Fin.ext
    simp [sourceRound]
  have hcandidateStart := CollectionCheckedExecution.startRound_success_candidate
    l started (sourceRound r) enabled raw hstart
  have hstartedCandidate : started = startRoundCandidate l r enabled raw := by
    simpa [hindex] using hcandidateStart
  intro a
  cases hcurrent : l.currentRegisters a with
  | none =>
      have hstartedUnknown : started.currentRegisters a = none := by
        rw [hstartedCandidate]
        simp [startRoundCandidate, hcurrent]
      have hstartedGamma : started.gammaLoc a = 0 := by
        rw [hstartedCandidate]
        exact CoordinatorCollectionLedger.startRoundCandidate_unknown_zero
          l r enabled raw a hcurrent
      have hdecodedGamma : decoded.gammaLoc a = 0 := by
        rw [hgammaPreserved a, hstartedGamma]
      have hinc := increment_le_of_registerDomainsCheck decoded
        (registerDomainsCheck_of_validLedgerCheck decoded hvalidDecoded) a
      simpa [hdecodedGamma] using hinc
  | some current =>
      have hcutoffSome : ∃ cutoff, l.cutoffRegisters a = some cutoff := by
        cases hc : l.cutoffRegisters a with
        | none =>
            have hnone := (currentRegister_none_iff_cutoffRegister_none l
              (startRound_success_input l started (sourceRound r) enabled raw hstart).1 a).2 hc
            rw [hcurrent] at hnone
            cases hnone
        | some cutoff => exact ⟨cutoff, rfl⟩
      obtain ⟨cutoff, hcutoff⟩ := hcutoffSome
      have hcredit := hmass a cutoff current hcutoff hcurrent
      have hcreditNoCutoff : l.increment a + current.queue ≤ r.val * D p := by
        omega
      let record := localQueueRecord l r enabled raw a
      let step := QueueReplay.transition (4 * rate.n) (0, current.queue) record
      have hstartedRegister : started.currentRegisters a = some ⟨step.2, step.1⟩ := by
        rw [hstartedCandidate]
        rw [← CoordinatorCollectionLedger.startRoundCandidate_known_transition
          l r enabled raw a current hcurrent]
      have hstartedGamma : started.gammaLoc a = step.1 := by
        rw [hstartedCandidate]
        simp [startRoundCandidate, hcurrent, step, record]
      have hstartedIncrement : started.increment a = l.increment a := by
        rw [hstartedCandidate]
        rfl
      have hdecodedKnown := decodeUp_preserves_known_registers
        started decoded i parsed a ⟨step.2, step.1⟩ hstartedRegister hdecode
      have htotal : step.1 + step.2 = current.queue +
          RecordedQueueRun.acceptedArrival record := by
        have h := RecordedQueueRun.transition_total (4 * rate.n)
          (0, current.queue) record
        change step.1 + step.2 = 0 + current.queue +
          RecordedQueueRun.acceptedArrival record at h
        simpa [step] using h
      have harrivalCap : record.2 ≤ D p := by
        exact collection_start_arrival_cap l started r enabled raw hstart a
      have harrivalLE : RecordedQueueRun.acceptedArrival record ≤ record.2 := by
        cases record with
        | mk wasEnabled amount =>
            cases wasEnabled <;> simp [RecordedQueueRun.acceptedArrival]
      have htotalEndpoint : l.increment a + step.1 + step.2 ≤ (r.val + 1) * D p := by
        calc
          l.increment a + step.1 + step.2 =
              l.increment a + (step.1 + step.2) := by omega
          _ = l.increment a +
              (current.queue + RecordedQueueRun.acceptedArrival record) := by rw [htotal]
          _ ≤ r.val * D p + D p := by
              calc
                l.increment a + (current.queue +
                    RecordedQueueRun.acceptedArrival record) =
                    (l.increment a + current.queue) +
                      RecordedQueueRun.acceptedArrival record := by omega
                _ ≤ r.val * D p + D p := Nat.add_le_add hcreditNoCutoff
                  (Nat.le_trans harrivalLE harrivalCap)
          _ = (r.val + 1) * D p := by rw [Nat.add_mul, Nat.one_mul]
      have hdecodedEndpoint : decoded.increment a + decoded.gammaLoc a + step.2 ≤
          (r.val + 1) * D p := by
        rw [hdecodedKnown.1, hdecodedKnown.2, hstartedIncrement, hstartedGamma]
        exact htotalEndpoint
      have hroundBound : r.val + 1 ≤ p.T := Nat.succ_le_of_lt r.isLt
      have hscaled := Nat.mul_le_mul_right (D p) hroundBound
      have hbound : (r.val + 1) * D p ≤ p.T * D p := by
        simpa only [Nat.one_mul] using hscaled
      exact Nat.le_trans (by omega) hbound

/-- The actual whole-source continuing-collection branch reaches a checked
ledger FINISH after either accepted or rejected UP reception. The only
numerical input is the independently checked complete-history mass root; the
recorder, START, and receiver are the literal operations on this same round. -/
theorem actual_continuing_collection_finish
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length) :
    let x := (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val]'k.isLt |>.input
    ∀ (P : Payload rate) (l : Ledger rate)
      (saved : Option (Fin p.T × Bool)),
      x.state.coordinator = .collection P l saved →
      ∀ (c : Choice rate), choice x = some c →
      ∀ (recording : CoordinatorRecordingOperation.Output p),
        CoordinatorRecorderComplementBridge.run
          (ReferenceActivePhysicalStep.collectionRecordingInput
            (ReferenceActivePhysicalStep.prepare x) c.payload c.started c.weights) =
              some recording →
        ∀ (started : Ledger rate),
          startRound c.preLedger (x.time.val + 1)
            (ReferenceActivePhysicalStep.collectionEnabled c.preLedger x.time)
            (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) =
              .success started →
          ∀ (decoded : Ledger rate) (bank : CoordinatorUpReception.UpDecoderBank p),
            ((ReferenceActivePhysicalStep.receiveUp
                (ReferenceActivePhysicalStep.prepare x) started).result =
                  .success (decoded, bank) ∨
              (ReferenceActivePhysicalStep.receiveUp
                (ReferenceActivePhysicalStep.prepare x) started).result =
                  .rejected (decoded, bank)) →
            ∃ finished,
              finishRound decoded = .success finished ∧
              finished = finishRoundCandidate decoded ∧
              validLedgerCheck finished = true ∧
              finished.phase = Phase.ready ∧
              finished.cursor = x.time.val + 2 ∧
              (∀ a, finished.increment a = decoded.increment a + decoded.gammaLoc a ∧
                finished.gammaLoc a = 0) ∧
              finished.assignment = decoded.assignment ∧
              finished.sigma = decoded.sigma ∧
              finished.cutoff = decoded.cutoff ∧
              finished.freezeAt = decoded.freezeAt ∧
              finished.baseScore = decoded.baseScore ∧
              finished.pending = decoded.pending ∧
              finished.cutoffRegisters = decoded.cutoffRegisters ∧
              finished.currentRegisters = decoded.currentRegisters ∧
              finished.rawBuffer = decoded.rawBuffer ∧
              finished.enabledHistory = decoded.enabledHistory ∧
              ((ReferenceActivePhysicalStep.receiveUp
                  (ReferenceActivePhysicalStep.prepare x) started).result =
                    .success (decoded, bank) →
                ∃ (M : OrdinaryMessageCodec.UpRecord
                    (codecParams p rate.eta.val))
                  (hbound : started.cutoff - 1 +
                    (started.cursor - started.cutoff) ≤ p.T)
                  (lastIndex : Fin p.T) (past : List (Bool × ℕ))
                  (current : Bool × ℕ),
                  effectiveParse x started = some M ∧
                  decodeUp started (ReferenceActivePhysicalStep.upSenderIndex x)
                    (some M) = .success decoded ∧
                  sourceRound lastIndex = started.cursor ∧
                  replayRecords? started (started.assignment.arm
                    (ReferenceActivePhysicalStep.upSenderIndex x))
                    (calendarIndices p.T (started.cutoff - 1)
                      (started.cursor - started.cutoff) hbound) = some past ∧
                  replayRecords? started (started.assignment.arm
                    (ReferenceActivePhysicalStep.upSenderIndex x))
                    [lastIndex] = some [current] ∧
                  started.currentRegisters (started.assignment.arm
                    (ReferenceActivePhysicalStep.upSenderIndex x)) = none ∧
                  started.cutoffRegisters (started.assignment.arm
                    (ReferenceActivePhysicalStep.upSenderIndex x)) = none ∧
                  ReferenceCollectionPhaseHistory.AcceptedUp x
                    (ReferenceActivePhysicalStep.upSenderIndex x) M ∧
                  decoded = acceptUpCandidate started
                    (ReferenceActivePhysicalStep.upSenderIndex x) M past current ∧
                  decoded.cutoffRegisters (started.assignment.arm
                    (ReferenceActivePhysicalStep.upSenderIndex x)) =
                    some ⟨started.baseScore (ReferenceActivePhysicalStep.upSenderIndex x) +
                      M.val.S, M.val.q, M.val.delta⟩ ∧
                  finished.increment (started.assignment.arm
                    (ReferenceActivePhysicalStep.upSenderIndex x)) =
                    (replayResult (4 * rate.n) M.val.q past current).registers.1) := by
  dsimp only
  intro P l saved hstate c hchoice recording hrecord started hstart decoded bank hreceive
  let x : RoundInput p rate :=
    (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val]'k.isLt |>.input
  have hpre : c.preLedger = l := choice_preLedger_eq x P l saved c hstate hchoice
  let enabled := ReferenceActivePhysicalStep.collectionEnabled l x.time
  let raw := CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording
  have hstart' : startRound l (sourceRound x.time) enabled raw = .success started := by
    simpa [enabled, raw, hpre, sourceRound] using hstart
  have hstartIndex : (⟨sourceRound x.time - 1, by
      change x.time.val + 1 - 1 < p.T
      omega⟩ : Fin p.T) = x.time := by
    apply Fin.ext
    simp [sourceRound]
  have hstartedCandidate : started = startRoundCandidate l x.time enabled raw := by
    simpa [hstartIndex] using CollectionCheckedExecution.startRound_success_candidate
      l started (sourceRound x.time) enabled raw hstart'
  have hstartedFields := startRound_success_valid l started x.time enabled raw
    (by simpa [sourceRound] using hstart')
  have hstartInput := startRound_success_input l started (sourceRound x.time)
    enabled raw hstart'
  have hroot := ReferenceCompleteCoordinatorMass.complete_coordinator_input_output_mass
    rate rewards C_star C_h source
  dsimp only at hroot
  have hincoming := (hroot k).1
  unfold ReferenceCompleteCoordinatorMass.coordinatorInputMass at hincoming
  rw [hstate] at hincoming
  have hmass : ∀ (a : Fin p.K) (cutoff : CutoffRegister)
      (current : CurrentRegister),
      l.cutoffRegisters a = some cutoff → l.currentRegisters a = some current →
      cutoff.score + l.increment a + current.queue ≤ x.time.val * D p := by
    change ∀ (a : Fin p.K) (cutoff : CutoffRegister) (current : CurrentRegister),
      l.cutoffRegisters a = some cutoff → l.currentRegisters a = some current →
      cutoff.score + l.increment a + current.queue ≤ x.time.val * D p ∧
        cutoff.score + cutoff.queue ≤ (l.cutoff - 1) * D p ∧
        cutoff.lastService ≤ D p ∧ current.lastService ≤ D p at hincoming
    intro a cutoff current hcut hcurrent
    exact (hincoming a cutoff current hcut hcurrent).1
  have hdecodeResult := ReferenceCollectionSegmentExtraction.receiveUp_decode_result
    x started
  have hdecode : decodeUp started (ReferenceActivePhysicalStep.upSenderIndex x)
      (effectiveParse x started) = .success decoded ∨
      decodeUp started (ReferenceActivePhysicalStep.upSenderIndex x)
        (effectiveParse x started) = .rejected decoded := by
    rcases hreceive with hsuccess | hrejected
    · rw [hsuccess] at hdecodeResult
      exact Or.inl hdecodeResult
    · rw [hrejected] at hdecodeResult
      exact Or.inr hdecodeResult
  have hdecodedFields := decoded_tag_fields started decoded
    (ReferenceActivePhysicalStep.upSenderIndex x) (effectiveParse x started) hdecode
  have hslack := decoded_all_arm_slack_of_input_mass l started decoded x.time
    enabled raw (ReferenceActivePhysicalStep.upSenderIndex x)
    (effectiveParse x started) (by simpa [sourceRound] using hstart') hdecode
    hdecodedFields.1 hdecodedFields.2.2.2 hmass
  have hcursorBound : decoded.cursor ≤ p.T := by
    rw [hdecodedFields.2.2.1, hstartedFields.2.2]
    exact Nat.succ_le_of_lt x.time.isLt
  have hcandidateValid := finishCandidate_valid_of_checked decoded
    hdecodedFields.1 hdecodedFields.2.1 hcursorBound hslack
  let finished := finishRoundCandidate decoded
  have hfinish : finishRound decoded = .success finished := by
    simp [finishRound, finished, hdecodedFields.1, hdecodedFields.2.1,
      hcursorBound, hcandidateValid]
  have hdecodedCursor : decoded.cursor = x.time.val + 1 := by
    calc
      decoded.cursor = started.cursor := hdecodedFields.2.2.1
      _ = sourceRound x.time := hstartedFields.2.2
      _ = x.time.val + 1 := rfl
  have hphaseFinished : finished.phase = Phase.ready := by
    simp [finished, finishRoundCandidate]
  have hcursorFinished : finished.cursor = x.time.val + 2 := by
    simp [finished, finishRoundCandidate, hdecodedCursor]
  have hincrementFinished : ∀ a,
      finished.increment a = decoded.increment a + decoded.gammaLoc a ∧
        finished.gammaLoc a = 0 := by
    intro a
    simp [finished, finishRoundCandidate]
  have hunchanged :
      finished.assignment = decoded.assignment ∧
      finished.sigma = decoded.sigma ∧
      finished.cutoff = decoded.cutoff ∧
      finished.freezeAt = decoded.freezeAt ∧
      finished.baseScore = decoded.baseScore ∧
      finished.pending = decoded.pending ∧
      finished.cutoffRegisters = decoded.cutoffRegisters ∧
      finished.currentRegisters = decoded.currentRegisters ∧
      finished.rawBuffer = decoded.rawBuffer ∧
      finished.enabledHistory = decoded.enabledHistory := by
    simp [finished, finishRoundCandidate]
  rcases hunchanged with ⟨hassignmentOut, hsigmaOut, hcutoffOut, hfreezeOut,
    hbaseOut, hpendingOut, hcutoffRegistersOut, hcurrentRegistersOut,
    hrawOut, hhistoryOut⟩
  refine ⟨finished, hfinish, rfl, hcandidateValid, hphaseFinished,
    hcursorFinished, hincrementFinished, hassignmentOut, hsigmaOut,
    hcutoffOut, hfreezeOut, hbaseOut, hpendingOut, hcutoffRegistersOut,
    hcurrentRegistersOut, hrawOut, hhistoryOut, ?_⟩
  intro hsuccess
  rcases hreceive with hsuccess' | hrejected
  · have hdecodeSuccess : decodeUp started (ReferenceActivePhysicalStep.upSenderIndex x)
        (effectiveParse x started) = .success decoded := by
      rw [hsuccess'] at hdecodeResult
      exact hdecodeResult
    cases hparse : effectiveParse x started with
    | none =>
        rw [hparse] at hdecodeSuccess
        have hdomain := decodeUp_tag_domain started
          (ReferenceActivePhysicalStep.upSenderIndex x) none decoded (Or.inl hdecodeSuccess)
        have hdecodedValid := CoordinatorUpReception.validLedgerCheck_after_decode
          started hdomain.1 hdomain.2.1
        have hdecodedValid' : validLedgerCheck
            (show Ledger rate from { started with phase := Phase.decoded }) = true := by
          simpa [CoordinatorUpReception.decodePhaseCandidate] using hdecodedValid
        unfold decodeUp at hdecodeSuccess
        rw [dite_eq_left hdomain] at hdecodeSuccess
        simp [hdecodedValid'] at hdecodeSuccess
    | some M =>
        rw [hparse] at hdecodeSuccess
        obtain ⟨hbound, lastIndex, hindex, past, current, hpast, hcurrent,
          hunknown, hcandidate⟩ := CollectionCheckedExecution.decodeUp_success_candidate
            started decoded (ReferenceActivePhysicalStep.upSenderIndex x) M hdecodeSuccess
        have hdomain := decodeUp_tag_domain started
          (ReferenceActivePhysicalStep.upSenderIndex x) (some M) decoded
          (Or.inl hdecodeSuccess)
        have hcutoffUnknown :=
          (currentRegister_none_iff_cutoffRegister_none started hdomain.1
            (started.assignment.arm (ReferenceActivePhysicalStep.upSenderIndex x))).1 hunknown
        have hassignment : started.assignment = l.assignment := by
          rw [hstartedCandidate]
          simp [startRoundCandidate]
        have hpreUnknown : l.currentRegisters
            (l.assignment.arm (ReferenceActivePhysicalStep.upSenderIndex x)) = none := by
          rw [hassignment] at hunknown
          rw [hstartedCandidate] at hunknown
          cases hp : l.currentRegisters
              (l.assignment.arm (ReferenceActivePhysicalStep.upSenderIndex x)) with
          | none => rfl
          | some current => simp [startRoundCandidate, hp] at hunknown
        have hgammaStarted : started.gammaLoc
            (started.assignment.arm (ReferenceActivePhysicalStep.upSenderIndex x)) = 0 := by
          have hunknownPre := CoordinatorCollectionLedger.startRoundCandidate_unknown_zero
            l x.time enabled raw (l.assignment.arm (ReferenceActivePhysicalStep.upSenderIndex x))
            hpreUnknown
          rw [hassignment]
          rw [hstartedCandidate]
          exact hunknownPre
        have honce := CoordinatorCollectionLedger.finish_recovered_increment_once
          started (ReferenceActivePhysicalStep.upSenderIndex x) M past current
          hunknown hgammaStarted
        let tail : ReferenceCollectionPhaseHistory.Tail x :=
          ⟨c.payload, c.preLedger, c.started, c.weights⟩
        have htail : ReferenceCollectionPhaseHistory.executedTail x = some tail := by
          simpa [tail] using choice_executedTail x c hchoice
        have haccepted : ReferenceCollectionPhaseHistory.AcceptedUp x
            (ReferenceActivePhysicalStep.upSenderIndex x) M := by
          refine ⟨tail, recording, started, decoded, bank, htail, ?_, ?_,
            hsuccess', ?_, rfl⟩
          · simpa [tail] using hrecord
          · simpa [tail, hpre, sourceRound] using hstart
          · simpa [ReferenceCollectionPhaseHistory.filteredParsed,
              ReferenceCollectionSegmentExtraction.effectiveParse] using hparse
        have hcutoffValue : decoded.cutoffRegisters
            (started.assignment.arm (ReferenceActivePhysicalStep.upSenderIndex x)) =
              some ⟨started.baseScore (ReferenceActivePhysicalStep.upSenderIndex x) +
                M.val.S, M.val.q, M.val.delta⟩ := by
          rw [hcandidate]
          simp [acceptUpCandidate, Function.update_self]
        have hfinishedOnce : finished.increment
            (started.assignment.arm (ReferenceActivePhysicalStep.upSenderIndex x)) =
              (replayResult (4 * rate.n) M.val.q past current).registers.1 := by
          rw [show finished = finishRoundCandidate decoded from rfl, hcandidate]
          exact honce.2.2
        refine ⟨M, hbound, lastIndex, past, current, rfl, hdecodeSuccess,
          hindex, hpast, hcurrent, hunknown, hcutoffUnknown, haccepted,
          hcandidate, hcutoffValue, hfinishedOnce⟩
  · rw [hrejected] at hsuccess
    cases hsuccess

end Bandits.Support.ReferenceCompleteContinuingCollectionFinish
