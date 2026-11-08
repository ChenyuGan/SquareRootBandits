/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteContinuingCollectionFinish
public import Bandits.Support.ReferenceContinuingCollectionStartDomains

import Lean.Elab.Tactic.Omega

/-!
# Actual continuing collection recorder and START

This module proves the checked recorder and ledger START for the actual
continuing-collection choice on one record of the complete physical suffix.
Its incoming ledger is the same carried snapshot used by that choice. The
proof does not assert success of an arbitrary local choice or a physical
reward, collision, score, or queue law.

Mathematical source: `sources/zip4/manuscript/06_interruptions.tex:35-100,164-177,246-299`,
`sources/zip4/manuscript/04_slow_fast_learner.tex:157-188`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:8-64`.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceCompleteContinuingCollectionStart

open ConstructorDimensions
open ReferenceActivePhysicalStep
open CoordinatorCollectionLedger
open ReferenceCollectionSegmentExtraction

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

private theorem armPendingCheck_eq_true_iff
    (l : Ledger rate) (a : Fin p.K) :
    armPendingCheck l a = true ↔ armPending l a := by
  unfold armPendingCheck anyFin
  rw [List.any_eq_true]
  simp [armPending]

private theorem currentRegister_none_iff_cutoffRegister_none
    (l : Ledger rate) (hvalid : validLedgerCheck l = true) (a : Fin p.K) :
    l.currentRegisters a = none ↔ l.cutoffRegisters a = none := by
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

private theorem choice_continuing_snapshot
    (x : RoundInput p rate) (P : Payload rate) (l : Ledger rate)
    (saved : Option (Fin p.T × Bool)) (c : Choice rate)
    (hstate : x.state.coordinator = .collection P l saved)
    (hchoice : choice x = some c) :
    ∃ (cutoff : Fin p.T) (clock : CoordinatorPhaseClock.ClockRegisters p)
      (core : CoordinatorRoundDispatch.CollectionCoreValid
        (ReferenceActivePhysicalStep.collectionInput x P l clock cutoff))
      (snapshot : CoordinatorCollectionInteractive.PreparedSnapshot
        (ReferenceActivePhysicalStep.collectionInput x P l clock cutoff))
      (boundary : snapshot.clockStarted.clock.g ≤ p.T + 1)
      (scores : CoordinatorRoundDispatch.collectionCurrentScoresCheck
        (ReferenceActivePhysicalStep.collectionInput x P l clock cutoff) = true),
      CoordinatorRoundDispatch.dispatchCollection
          (ReferenceActivePhysicalStep.collectionInput x P l clock cutoff) =
        .continuing core snapshot boundary scores ∧
      (prepare x).coordinator =
        .collection P l clock cutoff (.continuing core snapshot boundary scores) ∧
      c = ⟨P, l, snapshot.clockStarted,
        CoordinatorCollectionInteractive.PreObservationInputs.weights
          (ReferenceActivePhysicalStep.collectionInput x P l clock cutoff)
          snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq,
        none⟩ ∧ (prepare x).coordinator.arm = snapshot.arm := by
  classical
  have hcutoffDomain : 1 ≤ l.cutoff ∧ l.cutoff ≤ p.T := by
    by_contra hbad
    have hcut : (prepare x).coordinator.selection = none := by
      simp [ReferenceActivePhysicalStep.prepare,
        ReferenceActivePhysicalStep.dispatch, hstate, hbad,
        ReferenceActivePhysicalStep.DispatchCut.selection]
    unfold choice at hchoice
    simp [hcut] at hchoice
  let cutoff : Fin p.T := ⟨l.cutoff - 1, by omega⟩
  let clock := ReferenceActivePhysicalStep.collectionClock P l saved cutoff
  have hchoiceCut :
      choiceOfCut (prepare x).coordinator = some c := by
    unfold choice at hchoice
    by_cases hselection : (prepare x).coordinator.selection = none
    · simp [hselection] at hchoice
    · simpa [hselection] using hchoice
  have hpreparedDispatch : (prepare x).coordinator =
      .collection P l clock cutoff
        (CoordinatorRoundDispatch.dispatchCollection
          (ReferenceActivePhysicalStep.collectionInput x P l clock cutoff)) := by
    simp [ReferenceActivePhysicalStep.prepare,
      ReferenceActivePhysicalStep.dispatch, CoordinatorRoundDispatch.dispatch,
      hstate, hcutoffDomain, cutoff, clock]
    rfl
  rw [hpreparedDispatch] at hchoiceCut
  cases houtcome : CoordinatorRoundDispatch.dispatchCollection
      (ReferenceActivePhysicalStep.collectionInput x P l clock cutoff) with
  | continuing core snapshot boundary scores =>
      simp only [ReferenceCollectionSegmentExtraction.choiceOfCut, houtcome] at hchoiceCut
      have hchoiceEq := Option.some.inj hchoiceCut
      have hpreparedContinue : (prepare x).coordinator =
          .collection P l clock cutoff (.continuing core snapshot boundary scores) := by
        rw [hpreparedDispatch, houtcome]
      have harm : (prepare x).coordinator.arm = snapshot.arm := by
        rw [hpreparedContinue]
        simp [ReferenceActivePhysicalStep.DispatchCut.arm,
          ReferenceActivePhysicalStep.DispatchCut.selection]
      exact ⟨cutoff, clock, core, snapshot, boundary, scores,
        houtcome, hpreparedContinue, hchoiceEq.symm, harm⟩
  | _ => simp [ReferenceCollectionSegmentExtraction.choiceOfCut, houtcome] at hchoiceCut

private theorem raw_slot_fresh_of_ready_valid
    (l : Ledger rate) (r : Fin p.T) (raw : Option (Fin p.K × ℕ))
    (hvalid : validLedgerCheck l = true) (hready : l.phase = Phase.ready)
    (hcursor : l.cursor = CoordinatorCollectionLedger.sourceRound r) :
    rawSlotFreshCheck l r raw = true := by
  classical
  cases raw with
  | none => rfl
  | some pair =>
      rcases pair with ⟨a, amount⟩
      have hparts := hvalid
      simp [validLedgerCheck, hready, Bool.and_eq_true] at hparts
      rcases hparts with ⟨hparts, hraw⟩
      have hrawEq := (allFin_eq_true_iff _).1 hraw a
      have hrawEq := (allFin_eq_true_iff _).1 hrawEq r
      have hslot : l.rawBuffer a r = none := by
        cases hcell : l.rawBuffer a r with
        | none => rfl
        | some old =>
            simp [hcell, hready] at hrawEq
            omega
      simp [rawSlotFreshCheck, hslot]

private theorem transition_service_le_D
    (current : CurrentRegister) (record : Bool × ℕ) :
    (QueueReplay.transition (4 * rate.n) (0, current.queue) record).1 ≤ D p := by
  have hcapacity := ActiveFollowerDownAcceptance.four_n_le_D p rate
  cases record with
  | mk enabled arrival =>
      cases enabled
      · simp [QueueReplay.transition]
      · have hmin : min (4 * rate.n) (current.queue + arrival) ≤ D p :=
          Nat.le_trans (Nat.min_le_left _ _) hcapacity
        simpa [QueueReplay.transition] using hmin

private theorem localQueueRecord_arrival_le_D
    (l : Ledger rate) (r : Fin p.T) (enabled : Bool)
    (raw : Option (Fin p.K × ℕ)) (a : Fin p.K)
    (hraw : rawInputDomainCheck raw = true) :
    (localQueueRecord l r enabled raw a).2 ≤ D p := by
  unfold localQueueRecord
  split
  · cases raw with
    | none => simp [localArrival]
    | some pair =>
        rcases pair with ⟨arm, amount⟩
        have hamount : amount ≤ D p := by
          simpa [rawInputDomainCheck] using hraw
        by_cases harm : arm = a
        · simp [localArrival, harm, hamount]
        · simp [localArrival, harm]
  · exact Nat.zero_le _

private theorem localQueueRecord_acceptedArrival_le
    (l : Ledger rate) (r : Fin p.T) (enabled : Bool)
    (raw : Option (Fin p.K × ℕ)) (a : Fin p.K) :
    RecordedQueueRun.acceptedArrival (localQueueRecord l r enabled raw a) ≤
      (localQueueRecord l r enabled raw a).2 := by
  cases localQueueRecord l r enabled raw a with
  | mk active amount =>
      cases active <;> simp [RecordedQueueRun.acceptedArrival]

private theorem startRoundCandidate_valid
    (l : Ledger rate) (r : Fin p.T) (enabled : Bool)
    (raw : Option (Fin p.K × ℕ))
    (hvalid : validLedgerCheck l = true) (hready : l.phase = Phase.ready)
    (hcursor : l.cursor = CoordinatorCollectionLedger.sourceRound r)
    (htimes : 1 ≤ l.sigma ∧ l.sigma ≤ p.T ∧ 1 ≤ l.cutoff ∧
      l.cutoff ≤ l.freezeAt ∧ l.cutoff ≤ p.T ∧ l.freezeAt ≤ p.T + 1 ∧
      l.cutoff ≤ l.cursor ∧ l.cursor ≤ p.T + 1)
    (hrawInput : rawInputDomainCheck raw = true)
    (hfresh : rawSlotFreshCheck l r raw = true)
    (hmass : ∀ (a : Fin p.K) (cutoff : CutoffRegister)
      (current : CurrentRegister),
      l.cutoffRegisters a = some cutoff →
      l.currentRegisters a = some current →
      cutoff.score + l.increment a + current.queue ≤ r.val * D p) :
    validLedgerCheck (startRoundCandidate l r enabled raw) = true := by
  classical
  have hparts := hvalid
  simp [validLedgerCheck, hready, Bool.and_eq_true] at hparts
  rcases hparts with ⟨hparts, hrawEntries⟩
  rcases hparts with ⟨hparts, hregisterDomains⟩
  rcases hparts with ⟨hparts, hincrementPending⟩
  rcases hparts with ⟨hparts, hgammaPending⟩
  rcases hparts with ⟨hparts, hcutoffPending⟩
  rcases hparts with ⟨hparts, hcurrentPending⟩
  rcases hparts with ⟨hparts, hreadyHistory⟩
  rcases hparts with ⟨_scalarChecks, hgammaZero⟩
  have hcurrentAll := (allFin_eq_true_iff _).1 hcurrentPending
  have hcutoffAll := (allFin_eq_true_iff _).1 hcutoffPending
  have hincrementPendingAll := (allFin_eq_true_iff _).1 hincrementPending
  have hreadyHistoryAll := (allFin_eq_true_iff _).1 hreadyHistory
  have hregisterParts := hregisterDomains
  simp only [registerDomainsCheck, Bool.and_eq_true] at hregisterParts
  rcases hregisterParts with ⟨⟨⟨⟨hcurrentDomains, hcutoffDomains⟩,
      hbaseDomains⟩, hincrementDomains⟩, _hgammaDomains⟩
  have hcurrentDomainsAll := (allFin_eq_true_iff _).1 hcurrentDomains
  have hcutoffDomainsAll := (allFin_eq_true_iff _).1 hcutoffDomains
  have hbaseDomainsAll := (allFin_eq_true_iff _).1 hbaseDomains
  have hincrementDomainsAll := (allFin_eq_true_iff _).1 hincrementDomains
  have hslotEmpty (a : Fin p.K) : l.rawBuffer a r = none := by
    have hcell := (allFin_eq_true_iff _).1
      ((allFin_eq_true_iff _).1 hrawEntries a) r
    cases hc : l.rawBuffer a r with
    | none => rfl
    | some amount =>
        simp [hc, hready] at hcell
        rw [hcursor] at hcell
        omega
  have hnewCursor : CoordinatorCollectionLedger.sourceRound r ≤ p.T :=
    Nat.succ_le_of_lt r.isLt
  have hcutoffTime : l.cutoff ≤ CoordinatorCollectionLedger.sourceRound r := by
    omega
  have hnewTimes :
      1 ≤ l.sigma ∧ l.sigma ≤ p.T ∧ 1 ≤ l.cutoff ∧
      l.cutoff ≤ l.freezeAt ∧ l.cutoff ≤ p.T ∧
      l.freezeAt ≤ p.T + 1 ∧
      l.cutoff ≤ CoordinatorCollectionLedger.sourceRound r ∧
      CoordinatorCollectionLedger.sourceRound r ≤ p.T + 1 ∧
      CoordinatorCollectionLedger.sourceRound r ≤ p.T := by
    rcases htimes with ⟨hσ1, hσT, hcut1, hcutFreeze, hcutT, hfreeze,
      hcutCursor, hcursorT⟩
    rw [hcursor] at hcutCursor
    exact ⟨hσ1, hσT, hcut1, hcutFreeze, hcutT, hfreeze,
      hcutCursor, by omega, hnewCursor⟩
  have hstartedHistory :
      startedHistoryCheck (startRoundCandidate l r enabled raw) = true := by
    apply (allFin_eq_true_iff _).2
    intro q
    have hreadyQ := hreadyHistoryAll q
    by_cases hbefore : CoordinatorCollectionLedger.sourceRound q < l.cutoff
    · simp [startRoundCandidate.eq_def, hbefore]
    · by_cases hsame : q = r
      · subst q
        simp [startRoundCandidate.eq_def, hbefore]
      · have hqOld : (l.enabledHistory q).isSome =
          decide (CoordinatorCollectionLedger.sourceRound q < l.cursor) := by
          simpa [readyHistoryCheck, hbefore] using hreadyQ
        have hroundNe : CoordinatorCollectionLedger.sourceRound q ≠ l.cursor := by
          rw [hcursor]
          intro heq
          apply hsame
          apply Fin.ext
          dsimp [CoordinatorCollectionLedger.sourceRound] at heq
          omega
        have hdate :
            (CoordinatorCollectionLedger.sourceRound q ≤
              (startRoundCandidate l r enabled raw).cursor) =
            (CoordinatorCollectionLedger.sourceRound q < l.cursor) := by
          simp [startRoundCandidate.eq_def, hcursor]
          omega
        have hdateProp : CoordinatorCollectionLedger.sourceRound q < l.cursor ↔
            CoordinatorCollectionLedger.sourceRound q ≤
              CoordinatorCollectionLedger.sourceRound r := by
          rw [hcursor]
          omega
        have hdateBool :
            decide (CoordinatorCollectionLedger.sourceRound q < l.cursor) =
              decide (CoordinatorCollectionLedger.sourceRound q ≤
                CoordinatorCollectionLedger.sourceRound r) := by
          by_cases hlt : CoordinatorCollectionLedger.sourceRound q < l.cursor
          · have hle := hdateProp.mp hlt
            simp [hlt, hle]
          · have hle : ¬CoordinatorCollectionLedger.sourceRound q ≤
              CoordinatorCollectionLedger.sourceRound r := by
              intro h
              exact hlt (hdateProp.mpr h)
            simp [hlt, hle]
        have hhistoryPoint :
            ((Function.update l.enabledHistory r (some enabled) q).isSome ==
              decide (CoordinatorCollectionLedger.sourceRound q ≤
                CoordinatorCollectionLedger.sourceRound r)) = true := by
          rw [Function.update_of_ne hsame, hqOld, hdateBool]
          simp
        simp [startRoundCandidate.eq_def, hbefore,
          hhistoryPoint]
  have hcurrentConsistency :
      allFin p.K (fun a : Fin p.K =>
        ((startRoundCandidate l r enabled raw).currentRegisters a).isNone ==
          armPendingCheck (startRoundCandidate l r enabled raw) a) = true := by
    apply (allFin_eq_true_iff _).2
    intro a
    have hnone :
        ((startRoundCandidate l r enabled raw).currentRegisters a).isNone =
          (l.currentRegisters a).isNone := by
      cases hc : l.currentRegisters a <;>
        simp [startRoundCandidate, hc]
    have hpending :
        armPendingCheck (startRoundCandidate l r enabled raw) a =
          armPendingCheck l a := rfl
    rw [hnone, hpending]
    exact hcurrentAll a
  have hcutoffConsistency :
      allFin p.K (fun a : Fin p.K =>
        ((startRoundCandidate l r enabled raw).cutoffRegisters a).isNone ==
          armPendingCheck (startRoundCandidate l r enabled raw) a) = true := by
    apply (allFin_eq_true_iff _).2
    intro a
    have hpending :
        armPendingCheck (startRoundCandidate l r enabled raw) a =
          armPendingCheck l a := rfl
    change ((l.cutoffRegisters a).isNone == armPendingCheck l a) = true
    exact hcutoffAll a
  have hpendingGamma :
      allFin p.K (fun a : Fin p.K =>
        (!armPendingCheck (startRoundCandidate l r enabled raw) a) ||
          decide ((startRoundCandidate l r enabled raw).gammaLoc a = 0)) = true := by
    apply (allFin_eq_true_iff _).2
    intro a
    have hpending :
        armPendingCheck (startRoundCandidate l r enabled raw) a =
          armPendingCheck l a := rfl
    by_cases hp : armPendingCheck l a = true
    · have hcurrentNone : l.currentRegisters a = none := by
        have h := hcurrentAll a
        simp [hp] at h
        cases hc : l.currentRegisters a with
        | none => rfl
        | some current => simp [hc] at h
      rw [hpending]
      simp [startRoundCandidate, hcurrentNone, hp]
    · have hpFalse : armPendingCheck l a = false := Bool.eq_false_of_not_eq_true hp
      rw [hpending]
      simp [hpFalse]
  have hpendingIncrement :
      allFin p.K (fun a : Fin p.K =>
        (!armPendingCheck (startRoundCandidate l r enabled raw) a) ||
          decide ((startRoundCandidate l r enabled raw).increment a = 0)) = true := by
    apply (allFin_eq_true_iff _).2
    intro a
    have hpending :
        armPendingCheck (startRoundCandidate l r enabled raw) a =
          armPendingCheck l a := rfl
    rw [hpending]
    exact hincrementPendingAll a
  have hgammaDomainCandidate :
      allFin p.K (fun a : Fin p.K =>
        decide ((startRoundCandidate l r enabled raw).gammaLoc a ≤ D p)) = true := by
    apply (allFin_eq_true_iff _).2
    intro a
    cases hc : l.currentRegisters a with
    | none => simp [startRoundCandidate, hc]
    | some current =>
        apply decide_eq_true
        simpa [startRoundCandidate.eq_def, hc] using
          (transition_service_le_D (rate := rate) current
            (localQueueRecord l r enabled raw a))
  have hcurrentDomainCandidate :
      allFin p.K (fun a : Fin p.K =>
        match (startRoundCandidate l r enabled raw).currentRegisters a with
        | none => true
        | some current => decide (current.queue ≤ p.T * D p) &&
            decide (current.lastService ≤ D p)) = true := by
    apply (allFin_eq_true_iff _).2
    intro a
    cases hc : l.currentRegisters a with
    | none => simp [startRoundCandidate, hc]
    | some current =>
        have hcutSome : ∃ cutoff, l.cutoffRegisters a = some cutoff := by
          cases hcut : l.cutoffRegisters a with
          | none =>
              have hnone := (currentRegister_none_iff_cutoffRegister_none
                l hvalid a).2 hcut
              rw [hc] at hnone
              simp at hnone
          | some cutoff => exact ⟨cutoff, rfl⟩
        obtain ⟨cutoff, hcutoff⟩ := hcutSome
        have hcredit := hmass a cutoff current hcutoff hc
        have hcreditNoCutoff : l.increment a + current.queue ≤ r.val * D p := by
          omega
        let record := localQueueRecord l r enabled raw a
        let transition := QueueReplay.transition (4 * rate.n)
          (0, current.queue) record
        have htotal : transition.1 + transition.2 =
            current.queue + RecordedQueueRun.acceptedArrival record := by
          have h := RecordedQueueRun.transition_total (4 * rate.n)
            (0, current.queue) record
          simpa [transition, record] using h
        have harrival := localQueueRecord_arrival_le_D l r enabled raw a hrawInput
        have haccepted := localQueueRecord_acceptedArrival_le l r enabled raw a
        have hjoint : l.increment a + transition.1 + transition.2 ≤
            (r.val + 1) * D p := by
          have hacceptedD : RecordedQueueRun.acceptedArrival record ≤ D p :=
            le_trans haccepted harrival
          have hserviceQueue : transition.1 + transition.2 ≤
              current.queue + D p := by
            rw [htotal]
            exact Nat.add_le_add_left hacceptedD current.queue
          calc
            l.increment a + transition.1 + transition.2 ≤
                l.increment a + (current.queue + D p) := by omega
            _ ≤ (r.val + 1) * D p := by
                rw [Nat.add_mul, Nat.one_mul]
                simpa [Nat.add_assoc] using
                  Nat.add_le_add_right hcreditNoCutoff (D p)
        have hsumBound : l.increment a + transition.1 + transition.2 ≤
            p.T * D p := by
          have hround := Nat.mul_le_mul_right (D p) hnewCursor
          exact Nat.le_trans hjoint (by
            simpa [Nat.one_mul, CoordinatorCollectionLedger.sourceRound] using hround)
        have hqueueBound : transition.2 ≤ p.T * D p := by omega
        have hserviceBound : transition.1 ≤ D p :=
          transition_service_le_D (rate := rate) current record
        simpa [startRoundCandidate, hc, transition, record] using
          (show decide (transition.2 ≤ p.T * D p) &&
              decide (transition.1 ≤ D p) = true by
            simp [hqueueBound, hserviceBound])
  have hcutoffDomainCandidate :
      allFin p.K (fun a : Fin p.K =>
        match (startRoundCandidate l r enabled raw).cutoffRegisters a with
        | none => true
        | some cutoff => decide (cutoff.score ≤ p.T * D p) &&
            decide (cutoff.queue ≤ p.T * D p) && decide (cutoff.lastService ≤ D p)) = true := by
    apply (allFin_eq_true_iff _).2
    intro a
    change (match l.cutoffRegisters a with
      | none => true
      | some cutoff => decide (cutoff.score ≤ p.T * D p) &&
          decide (cutoff.queue ≤ p.T * D p) && decide (cutoff.lastService ≤ D p)) = true
    exact hcutoffDomainsAll a
  have hbaseDomainCandidate :
      allFin (p.m - 1) (fun i : Fin (p.m - 1) =>
        decide ((startRoundCandidate l r enabled raw).baseScore i ≤ p.T * D p)) = true := by
    apply (allFin_eq_true_iff _).2
    intro i
    simpa [startRoundCandidate] using hbaseDomainsAll i
  have hincrementDomainCandidate :
      allFin p.K (fun a : Fin p.K =>
        decide ((startRoundCandidate l r enabled raw).increment a ≤ p.T * D p)) = true := by
    apply (allFin_eq_true_iff _).2
    intro a
    simpa [startRoundCandidate] using hincrementDomainsAll a
  have hregistersCandidate :
      registerDomainsCheck (startRoundCandidate l r enabled raw) = true := by
    unfold registerDomainsCheck
    simp only [Bool.and_eq_true]
    exact ⟨⟨⟨⟨hcurrentDomainCandidate, hcutoffDomainCandidate⟩,
      hbaseDomainCandidate⟩, hincrementDomainCandidate⟩, hgammaDomainCandidate⟩
  have hrawDomainCandidate :
      rawEntryDomainsCheck (startRoundCandidate l r enabled raw) = true := by
    apply (allFin_eq_true_iff _).2
    intro a
    apply (allFin_eq_true_iff _).2
    intro q
    have hcellDomain := (allFin_eq_true_iff _).1
      ((allFin_eq_true_iff _).1 hrawEntries a) q
    cases raw with
    | none =>
        cases hold : l.rawBuffer a q with
        | none => simp [startRoundCandidate, hold]
        | some amount =>
            have holdDomain : 0 < amount ∧ amount ≤ D p ∧
                l.cutoff ≤ CoordinatorCollectionLedger.sourceRound q ∧
                CoordinatorCollectionLedger.sourceRound q < l.freezeAt ∧
                CoordinatorCollectionLedger.sourceRound q < l.cursor ∧
                armPendingCheck l a = true := by
              have h := hcellDomain
              simp [hold, hready] at h
              rcases h with ⟨⟨⟨⟨⟨hpos, hupper⟩, hcutoff⟩,
                hfreeze⟩, hcursorLt⟩, hpending⟩
              exact ⟨hpos, hupper, hcutoff, hfreeze, hcursorLt, hpending⟩
            have hdate : CoordinatorCollectionLedger.sourceRound q ≤
                CoordinatorCollectionLedger.sourceRound r := by
              rw [← hcursor]
              omega
            have hpendingBool : anyFin (p.m - 1) (fun i =>
                decide (i ∈ l.pending) && decide (l.assignment.arm i = a)) = true := by
              simpa [armPendingCheck] using holdDomain.2.2.2.2.2
            simp [startRoundCandidate.eq_def, hold,
              holdDomain.1, holdDomain.2.1,
              holdDomain.2.2.1, holdDomain.2.2.2.1, hdate,
              hpendingBool, armPendingCheck]
    | some pair =>
        rcases pair with ⟨arm, amount⟩
        have hamount : amount ≤ D p := by
          simpa [rawInputDomainCheck] using hrawInput
        by_cases hinsert : l.currentRegisters arm = none ∧ 0 < amount ∧
            CoordinatorCollectionLedger.sourceRound r < l.freezeAt
        · have hempty : l.rawBuffer arm r = none := by
            have h := hfresh
            simp [rawSlotFreshCheck, hinsert.1, hinsert.2.1, hinsert.2.2] at h
            exact h
          by_cases hnewCell : a = arm ∧ q = r
          · rcases hnewCell with ⟨ha, hq⟩
            subst a
            subst q
            have hpending : armPendingCheck l arm = true := by
              have h := hcurrentAll arm
              rw [hinsert.1] at h
              simp at h
              exact h
            have hpendingBool : anyFin (p.m - 1) (fun i =>
                decide (i ∈ l.pending) && decide (l.assignment.arm i = arm)) = true := by
              simpa [armPendingCheck] using hpending
            have hnewCellBuffer :
                (startRoundCandidate l r enabled (some (arm, amount))).rawBuffer arm r =
                  some amount := by
              simp [startRoundCandidate.eq_def, hinsert, putRaw]
            change (match (startRoundCandidate l r enabled (some (arm, amount))).rawBuffer arm r with
              | none => true
              | some value => decide (0 < value) && decide (value ≤ D p) &&
                  decide (l.cutoff ≤ CoordinatorCollectionLedger.sourceRound r) &&
                  decide (CoordinatorCollectionLedger.sourceRound r < l.freezeAt) &&
                  (if (startRoundCandidate l r enabled (some (arm, amount))).phase = Phase.ready
                    then decide (CoordinatorCollectionLedger.sourceRound r <
                      (startRoundCandidate l r enabled (some (arm, amount))).cursor)
                    else decide (CoordinatorCollectionLedger.sourceRound r ≤
                      (startRoundCandidate l r enabled (some (arm, amount))).cursor)) &&
                  armPendingCheck (startRoundCandidate l r enabled (some (arm, amount))) arm) = true
            rw [hnewCellBuffer]
            simp [startRoundCandidate.eq_def, hamount, hinsert,
              hcutoffTime, hpendingBool, armPendingCheck]
          · cases hold : l.rawBuffer a q with
            | none => simp [startRoundCandidate.eq_def, putRaw, hinsert,
                hold, hnewCell]
            | some old =>
                have holdDomain : 0 < old ∧ old ≤ D p ∧
                    l.cutoff ≤ CoordinatorCollectionLedger.sourceRound q ∧
                    CoordinatorCollectionLedger.sourceRound q < l.freezeAt ∧
                    CoordinatorCollectionLedger.sourceRound q < l.cursor ∧
                    armPendingCheck l a = true := by
                  have h := hcellDomain
                  simp [hold, hready] at h
                  rcases h with ⟨⟨⟨⟨⟨hpos, hupper⟩, hcutoff⟩,
                    hfreeze⟩, hcursorLt⟩, hpending⟩
                  exact ⟨hpos, hupper, hcutoff, hfreeze, hcursorLt, hpending⟩
                have hnotOverwrite : a ≠ arm ∨ q ≠ r := by
                  exact not_and_or.mp hnewCell
                have hpendingBool : anyFin (p.m - 1) (fun i =>
                    decide (i ∈ l.pending) && decide (l.assignment.arm i = a)) = true := by
                  simpa [armPendingCheck] using holdDomain.2.2.2.2.2
                have hbuffer :
                    (startRoundCandidate l r enabled (some (arm, amount))).rawBuffer a q =
                      some old := by
                  have hnewBuffer :
                      (startRoundCandidate l r enabled (some (arm, amount))).rawBuffer =
                        putRaw l.rawBuffer arm r amount := by
                    simp [startRoundCandidate.eq_def, hinsert]
                  rw [hnewBuffer]
                  exact (CoordinatorCollectionLedger.putRaw_other l.rawBuffer
                    arm a r q amount hnotOverwrite).trans hold
                have hdateRound : CoordinatorCollectionLedger.sourceRound q ≤
                    CoordinatorCollectionLedger.sourceRound r := by
                  rw [← hcursor]
                  omega
                change (match (startRoundCandidate l r enabled
                    (some (arm, amount))).rawBuffer a q with
                  | none => true
                  | some value => decide (0 < value) && decide (value ≤ D p) &&
                      decide (l.cutoff ≤ CoordinatorCollectionLedger.sourceRound q) &&
                      decide (CoordinatorCollectionLedger.sourceRound q < l.freezeAt) &&
                      (if (startRoundCandidate l r enabled (some (arm, amount))).phase = Phase.ready
                        then decide (CoordinatorCollectionLedger.sourceRound q <
                          (startRoundCandidate l r enabled (some (arm, amount))).cursor)
                        else decide (CoordinatorCollectionLedger.sourceRound q ≤
                          (startRoundCandidate l r enabled (some (arm, amount))).cursor)) &&
                      armPendingCheck (startRoundCandidate l r enabled (some (arm, amount))) a) = true
                rw [hbuffer]
                simp [startRoundCandidate.eq_def, holdDomain.1, holdDomain.2.1,
                  holdDomain.2.2.1, holdDomain.2.2.2.1, hdateRound,
                  hpendingBool, armPendingCheck]
        · cases hold : l.rawBuffer a q with
          | none => simp [startRoundCandidate.eq_def, hinsert, hold]
          | some old =>
              have holdDomain : 0 < old ∧ old ≤ D p ∧
                  l.cutoff ≤ CoordinatorCollectionLedger.sourceRound q ∧
                  CoordinatorCollectionLedger.sourceRound q < l.freezeAt ∧
                  CoordinatorCollectionLedger.sourceRound q < l.cursor ∧
                  armPendingCheck l a = true := by
                have h := hcellDomain
                simp [hold, hready] at h
                rcases h with ⟨⟨⟨⟨⟨hpos, hupper⟩, hcutoff⟩,
                  hfreeze⟩, hcursorLt⟩, hpending⟩
                exact ⟨hpos, hupper, hcutoff, hfreeze, hcursorLt, hpending⟩
              have hbuffer :
                  (startRoundCandidate l r enabled (some (arm, amount))).rawBuffer a q =
                    some old := by
                have hnewBuffer :
                    (startRoundCandidate l r enabled (some (arm, amount))).rawBuffer =
                      l.rawBuffer := by
                  simp [startRoundCandidate.eq_def, hinsert]
                rw [hnewBuffer]
                exact hold
              have hdateRound : CoordinatorCollectionLedger.sourceRound q ≤
                  CoordinatorCollectionLedger.sourceRound r := by
                rw [← hcursor]
                omega
              have hpendingBool : anyFin (p.m - 1) (fun i =>
                  decide (i ∈ l.pending) && decide (l.assignment.arm i = a)) = true := by
                simpa [armPendingCheck] using holdDomain.2.2.2.2.2
              change (match (startRoundCandidate l r enabled
                  (some (arm, amount))).rawBuffer a q with
                | none => true
                | some value => decide (0 < value) && decide (value ≤ D p) &&
                    decide (l.cutoff ≤ CoordinatorCollectionLedger.sourceRound q) &&
                    decide (CoordinatorCollectionLedger.sourceRound q < l.freezeAt) &&
                    (if (startRoundCandidate l r enabled (some (arm, amount))).phase = Phase.ready
                      then decide (CoordinatorCollectionLedger.sourceRound q <
                        (startRoundCandidate l r enabled (some (arm, amount))).cursor)
                      else decide (CoordinatorCollectionLedger.sourceRound q ≤
                        (startRoundCandidate l r enabled (some (arm, amount))).cursor)) &&
                    armPendingCheck (startRoundCandidate l r enabled (some (arm, amount))) a) = true
              rw [hbuffer]
              simp [startRoundCandidate.eq_def, holdDomain.1, holdDomain.2.1,
                holdDomain.2.2.1, holdDomain.2.2.2.1, hdateRound,
                hpendingBool, armPendingCheck]
  have hphaseCandidate : (startRoundCandidate l r enabled raw).phase = Phase.started := by
    rfl
  have hcursorCandidate :
      (startRoundCandidate l r enabled raw).cursor =
        CoordinatorCollectionLedger.sourceRound r := by
    rfl
  have hscalarCandidate :
      1 ≤ (startRoundCandidate l r enabled raw).sigma ∧
      (startRoundCandidate l r enabled raw).sigma ≤ p.T ∧
      1 ≤ (startRoundCandidate l r enabled raw).cutoff ∧
      (startRoundCandidate l r enabled raw).cutoff ≤
        (startRoundCandidate l r enabled raw).freezeAt ∧
      (startRoundCandidate l r enabled raw).cutoff ≤ p.T ∧
      (startRoundCandidate l r enabled raw).freezeAt ≤ p.T + 1 ∧
      (startRoundCandidate l r enabled raw).cutoff ≤
        (startRoundCandidate l r enabled raw).cursor ∧
      (startRoundCandidate l r enabled raw).cursor ≤ p.T + 1 := by
    rcases hnewTimes with ⟨hσ1, hσT, hcut1, hcutFreeze, hcutT, hfreeze,
      hcutCursor, hcursorT1, _⟩
    exact ⟨hσ1, hσT, hcut1, hcutFreeze, hcutT, hfreeze,
      hcutCursor, hcursorT1⟩
  rcases hscalarCandidate with ⟨hσ1, hσT, hcut1, hcutFreeze, hcutT,
    hfreeze, hcutCursor, hcursorT1⟩
  simp [validLedgerCheck, hphaseCandidate, hcursorCandidate,
    hσ1, hσT, hcut1, hcutFreeze, hcutT, hfreeze,
    hnewCursor, hstartedHistory, hcurrentConsistency,
    hcutoffConsistency, hpendingGamma, hpendingIncrement,
    hregistersCandidate, hrawDomainCandidate] ; omega

/-- On an actual continuing choice, the checked collection recorder and
stage-(1) START use the same carried ledger and the same source round. This
conditional producer proves nothing about whether an arbitrary collection
input has a successful choice. The receiver result is only its checked INPUT
domain, not a reception effect. -/
theorem actual_continuing_collection_recorder_start
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
      ∃ (o : CoordinatorRecordingOperation.Output p) (s : Ledger rate),
        c.payload = P ∧ c.preLedger = l ∧ c.initializer = none ∧
        CoordinatorRecorderComplementBridge.LocalInputsValid
          (ReferenceActivePhysicalStep.collectionRecordingInput
            (ReferenceActivePhysicalStep.prepare x) c.payload c.started c.weights) ∧
        CoordinatorRecorderComplementBridge.run
          (ReferenceActivePhysicalStep.collectionRecordingInput
            (ReferenceActivePhysicalStep.prepare x) c.payload c.started c.weights) = some o ∧
        CoordinatorCollectionLedger.rawSlotFreshCheck l x.time
          (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder o) = true ∧
        CoordinatorCollectionLedger.startRound l (x.time.val + 1)
          (ReferenceActivePhysicalStep.collectionEnabled c.preLedger x.time)
          (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder o) =
            .success s ∧
        s = CoordinatorCollectionLedger.startRoundCandidate l x.time
          (ReferenceActivePhysicalStep.collectionEnabled c.preLedger x.time)
          (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder o) ∧
        CoordinatorCollectionLedger.validLedgerCheck s = true ∧
        s.phase = CoordinatorCollectionLedger.Phase.started ∧
        s.cursor = x.time.val + 1 ∧
        CoordinatorUpReception.receptionInputCheck
          (ReferenceUpReception.receptionInputAtRow rate x.row
            (ReferenceActivePhysicalStep.upInputs (ReferenceActivePhysicalStep.prepare x) s)
            x.time) = true := by
  classical
  dsimp only
  intro P l saved hstate c hchoice
  let x : ReferenceActivePhysicalStep.RoundInput p rate :=
    (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val]'k.isLt |>.input
  obtain ⟨cutoff, clock, core, snapshot, boundary, scores,
    hdispatch, hprepared, hchoiceEq, harm⟩ :=
      choice_continuing_snapshot x P l saved c hstate hchoice
  subst c
  let sourceInput := ReferenceActivePhysicalStep.collectionInput x P l clock cutoff
  let inp := ReferenceActivePhysicalStep.collectionRecordingInput
    (ReferenceActivePhysicalStep.prepare x) P snapshot.clockStarted
    (CoordinatorCollectionInteractive.PreObservationInputs.weights sourceInput
      snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq)
  let en := ReferenceActivePhysicalStep.collectionEnabled l x.time
  let hinput := snapshot.inputsValid.toInputsValid
    (ReferenceActivePhysicalStep.prepare x).coordinatorObservation
  have hinpEq : inp =
      CoordinatorCollectionUpRoundStep.InputsValid.recorderInput hinput snapshot.arm := by
    simp [inp, sourceInput, ReferenceActivePhysicalStep.collectionRecordingInput,
        CoordinatorCollectionUpRoundStep.InputsValid.recorderInput,
        CoordinatorCollectionUpRoundStep.Inputs.weights,
        CoordinatorCollectionInteractive.PreObservationInputs.weights,
        CoordinatorCollectionInteractive.attachOwnObservation,
        snapshot.clockStarted_frame.1,
        snapshot.inputsValid.ledger_freeze_eq]
    rw [harm]
    rfl
  have hlocalCanonical :=
    CoordinatorCollectionUpRoundStep.InputsValid.recorderInput_valid hinput snapshot.arm
  have hlocal : CoordinatorRecorderComplementBridge.LocalInputsValid inp := by
    rw [hinpEq]
    exact hlocalCanonical
  obtain ⟨o, hrecord⟩ :=
    ReferenceContinuingCollectionStartDomains.collection_recorder_run_total inp hlocal rfl
  let raw := CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder o
  have hrawDomain : CoordinatorCollectionLedger.rawInputDomainCheck raw = true := by
    cases hgate : o.gateArm with
    | none => simp [raw, CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder,
        hgate, CoordinatorCollectionLedger.rawInputDomainCheck]
    | some arm =>
        simpa [raw, CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder,
          hgate, CoordinatorCollectionLedger.rawInputDomainCheck] using o.rawArrival_le_D
  have hroot := ReferenceCompleteCoordinatorMass.complete_coordinator_input_output_mass
    rate rewards C_star C_h source
  dsimp only at hroot
  have hincoming := (hroot k).1
  unfold ReferenceCompleteCoordinatorMass.coordinatorInputMass at hincoming
  rw [hstate] at hincoming
  have hmass : ∀ (a : Fin p.K) (cut : CoordinatorCollectionLedger.CutoffRegister)
      (current : CoordinatorCollectionLedger.CurrentRegister),
      l.cutoffRegisters a = some cut → l.currentRegisters a = some current →
      cut.score + l.increment a + current.queue ≤ x.time.val * D p := by
    intro a cut current hcut hcurrent
    exact (hincoming a cut current hcut hcurrent).1
  have htimes := hinput.ledger_time_bounds
  have hcursor := hinput.ledger_cursor_eq
  have htimesLedger : 1 ≤ l.sigma ∧ l.sigma ≤ p.T ∧ 1 ≤ l.cutoff ∧
      l.cutoff ≤ l.freezeAt ∧ l.cutoff ≤ p.T ∧ l.freezeAt ≤ p.T + 1 ∧
      l.cutoff ≤ l.cursor ∧ l.cursor ≤ p.T + 1 := by
    simpa [CoordinatorCollectionInteractive.attachOwnObservation,
      ReferenceActivePhysicalStep.collectionInput] using htimes
  have hcursorLedger : l.cursor = CoordinatorCollectionUpRoundStep.sourceRound x.time := by
    simpa [CoordinatorCollectionInteractive.attachOwnObservation,
      ReferenceActivePhysicalStep.collectionInput] using hcursor
  have hfresh := raw_slot_fresh_of_ready_valid l x.time raw hinput.ledger_valid
    hinput.ledger_ready hcursor
  have hvalidCandidate := startRoundCandidate_valid l x.time en raw
    hinput.ledger_valid hinput.ledger_ready hcursor htimes hrawDomain hfresh hmass
  let candidate := CoordinatorCollectionLedger.startRoundCandidate l x.time en raw
  have hstartDomain : CoordinatorCollectionLedger.validLedgerCheck l = true ∧
      l.phase = CoordinatorCollectionLedger.Phase.ready ∧
      x.time.val + 1 = l.cursor ∧ 1 ≤ x.time.val + 1 ∧
      x.time.val + 1 ≤ p.T ∧
      CoordinatorCollectionLedger.rawInputDomainCheck raw = true := by
    refine ⟨hinput.ledger_valid, hinput.ledger_ready, ?_, ?_, ?_, hrawDomain⟩
    · simpa [CoordinatorCollectionUpRoundStep.sourceRound] using hcursorLedger.symm
    · have hcutCursor := htimesLedger.2.2.2.2.2.2.1
      rw [hcursorLedger] at hcutCursor
      omega
    · exact Nat.succ_le_of_lt x.time.isLt
  let index : Fin p.T := ⟨x.time.val + 1 - 1,
    by have := x.time.isLt; omega⟩
  have hindex : index = x.time := by
    apply Fin.ext
    simp [index]
  have hfreshIndex : CoordinatorCollectionLedger.rawSlotFreshCheck l index raw = true := by
    rw [hindex]
    exact hfresh
  have hstart : CoordinatorCollectionLedger.startRound l (x.time.val + 1) en raw =
      .success candidate := by
    unfold CoordinatorCollectionLedger.startRound
    rw [dite_eq_left hstartDomain]
    change (if CoordinatorCollectionLedger.rawSlotFreshCheck l index raw then
      (let next := CoordinatorCollectionLedger.startRoundCandidate l index en raw
       if CoordinatorCollectionLedger.validLedgerCheck next then
         CoordinatorCollectionLedger.Checked.success next
       else CoordinatorCollectionLedger.Checked.invalid)
      else CoordinatorCollectionLedger.Checked.invalid) =
        CoordinatorCollectionLedger.Checked.success candidate
    rw [ite_eq_left (by simpa using hfreshIndex)]
    have hcandidateIndex : CoordinatorCollectionLedger.startRoundCandidate l index en raw =
        candidate := by
      rw [hindex]
    rw [hcandidateIndex]
    change (if CoordinatorCollectionLedger.validLedgerCheck candidate then
      CoordinatorCollectionLedger.Checked.success candidate else
        CoordinatorCollectionLedger.Checked.invalid) =
      CoordinatorCollectionLedger.Checked.success candidate
    rw [ite_eq_left (by simpa using hvalidCandidate)]
  have hphase : candidate.phase = CoordinatorCollectionLedger.Phase.started := rfl
  have hcursorCandidate : candidate.cursor = x.time.val + 1 := rfl
  let ri := ReferenceUpReception.receptionInputAtRow rate x.row
    (ReferenceActivePhysicalStep.upInputs (ReferenceActivePhysicalStep.prepare x) candidate)
    x.time
  have hreceiverDomain : CoordinatorUpReception.receptionInputDomain ri := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [ri, ReferenceUpReception.receptionInputAtRow,
        CoordinatorUpMeasurability.receptionInputAtRow,
        CoordinatorUpMeasurability.receptionInputAtControl,
        ReferenceActivePhysicalStep.upInputs] using hvalidCandidate
    · simpa [ri, ReferenceUpReception.receptionInputAtRow,
        CoordinatorUpMeasurability.receptionInputAtRow,
        CoordinatorUpMeasurability.receptionInputAtControl,
        ReferenceActivePhysicalStep.upInputs, candidate,
        CoordinatorCollectionLedger.startRoundCandidate] using htimesLedger.1
    · exact hphase
    · simpa [ri, ReferenceUpReception.receptionInputAtRow,
        CoordinatorUpMeasurability.receptionInputAtRow,
        CoordinatorUpMeasurability.receptionInputAtControl,
        ReferenceActivePhysicalStep.upInputs, candidate,
        CoordinatorCollectionLedger.startRoundCandidate] using htimesLedger.2.2.1
    · have hcutCursor := htimesLedger.2.2.2.2.2.2.1
      have hcutCursorTime : l.cutoff ≤ x.time.val + 1 := by
        calc
          l.cutoff ≤ l.cursor := hcutCursor
          _ = CoordinatorCollectionUpRoundStep.sourceRound x.time := hcursorLedger
          _ = x.time.val + 1 := rfl
      simpa [ri, ReferenceUpReception.receptionInputAtRow,
        CoordinatorUpMeasurability.receptionInputAtRow,
        CoordinatorUpMeasurability.receptionInputAtControl,
        ReferenceActivePhysicalStep.upInputs, candidate,
        CoordinatorCollectionLedger.startRoundCandidate,
        CoordinatorCollectionLedger.sourceRound,
        CoordinatorCollectionUpRoundStep.sourceRound] using hcutCursorTime
    · change x.time.val + 1 ≤ p.T
      exact Nat.succ_le_of_lt x.time.isLt
    · change x.time.val + 1 = CoordinatorCollectionLedger.sourceRound x.time
      rfl
    · simpa [ri, ReferenceUpReception.receptionInputAtRow,
        CoordinatorUpMeasurability.receptionInputAtRow,
        CoordinatorUpMeasurability.receptionInputAtControl,
        ReferenceActivePhysicalStep.upInputs, sourceInput,
        ReferenceActivePhysicalStep.collectionInput] using snapshot.inputsValid.decoder_bank_valid
  have hreceiver :=
    (CoordinatorUpReception.receptionInputCheck_eq_true_iff ri).2 hreceiverDomain
  refine ⟨o, candidate, ?_, ?_, ?_, ?_, hrecord, ?_, hstart, rfl,
    hvalidCandidate, hphase, hcursorCandidate, ?_⟩
  · rfl
  · rfl
  · rfl
  · exact hlocal
  · simpa [raw] using hfresh
  · exact hreceiver
