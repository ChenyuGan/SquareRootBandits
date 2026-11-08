/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteLiveChoiceDomains
public import Bandits.Support.ReferenceCompleteContinuingCollectionChoiceDomains

import Lean.Elab.Tactic.Omega

/-!
# Complete-source live cutoff post-choice execution

This module follows the actual live dispatch on a complete-source record
through a cutoff selection and the physical collection tail.

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:140-188`,
`sources/zip4/manuscript/06_interruptions.tex:9-100,246-299,355-426`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-84`.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.CoordinatorCollectionLedger

variable {p : ConstructorDimensions.Parameters}

variable {rate : ReferenceActivePhysicalStep.RateInput p}

open ReferenceCollectionSegmentExtraction

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

private theorem finishCandidate_valid (l : Ledger rate)
    (hvalid : validLedgerCheck l = true) (hphase : l.phase = Phase.decoded)
    (hsum : ∀ a, l.increment a + l.gammaLoc a ≤ p.T * D p) :
    validLedgerCheck (finishRoundCandidate l) = true := by
  classical
  have hparts := hvalid
  simp [validLedgerCheck, hphase, Bool.and_eq_true] at hparts
  rcases hparts with ⟨hparts, hraw⟩
  rcases hparts with ⟨hparts, hregs⟩
  rcases hparts with ⟨hparts, hinc⟩
  rcases hparts with ⟨hparts, hgamma⟩
  rcases hparts with ⟨hparts, hcut⟩
  rcases hparts with ⟨hparts, hcur⟩
  rcases hparts with ⟨hscalar, hhistory⟩
  have hready : readyHistoryCheck (finishRoundCandidate l) = true := by
    apply (allFin_eq_true_iff _).2
    intro r
    have h := (allFin_eq_true_iff _).1 hhistory r
    by_cases hb : sourceRound r < l.cutoff
    · simp [finishRoundCandidate, hb]
    · have hh : (l.enabledHistory r).isSome = decide (sourceRound r ≤ l.cursor) := by
        simpa [hb] using h
      simp [finishRoundCandidate, hb, hh]
  have hraw' : rawEntryDomainsCheck (finishRoundCandidate l) = true := by
    unfold rawEntryDomainsCheck at hraw ⊢
    apply (allFin_eq_true_iff _).2
    intro a
    apply (allFin_eq_true_iff _).2
    intro r
    have h := (allFin_eq_true_iff _).1 ((allFin_eq_true_iff _).1 hraw a) r
    cases hc : l.rawBuffer a r with
    | none => simp [finishRoundCandidate, hc]
    | some amount =>
        simp [hc, hphase] at h
        rcases h with ⟨⟨⟨⟨⟨hp, hD⟩, hcut⟩, hg⟩, ht⟩, hpend⟩
        simp [finishRoundCandidate, hc, hp, hD, hcut, hg, ht,
          armPendingCheck] at hpend ⊢
        exact hpend
  have hinc' : allFin p.K (fun a : Fin p.K =>
      (!armPendingCheck (finishRoundCandidate l) a) ||
        decide ((finishRoundCandidate l).increment a = 0)) = true := by
    apply (allFin_eq_true_iff _).2
    intro a
    have hi := (allFin_eq_true_iff _).1 hinc a
    have hg := (allFin_eq_true_iff _).1 hgamma a
    change (!armPendingCheck l a || decide (l.increment a + l.gammaLoc a = 0)) = true
    cases hp : armPendingCheck l a <;> simp [hp] at hi hg ⊢
    exact ⟨hi, hg⟩
  have hregs' : registerDomainsCheck (finishRoundCandidate l) = true := by
    simp only [registerDomainsCheck, Bool.and_eq_true] at hregs ⊢
    rcases hregs with ⟨⟨⟨⟨hc, hk⟩, hb⟩, _⟩, _⟩
    refine ⟨⟨⟨⟨hc, hk⟩, hb⟩, ?_⟩, ?_⟩
    · exact (allFin_eq_true_iff _).2 (fun a => decide_eq_true (hsum a))
    · apply (allFin_eq_true_iff _).2
      intro a
      simp [finishRoundCandidate]
  have hzero : allFin p.K (fun a : Fin p.K =>
      decide ((finishRoundCandidate l).gammaLoc a = 0)) = true := by
    apply (allFin_eq_true_iff _).2
    intro a
    simp [finishRoundCandidate]
  have hgamma' : allFin p.K (fun a : Fin p.K =>
      (!armPendingCheck (finishRoundCandidate l) a) ||
        decide ((finishRoundCandidate l).gammaLoc a = 0)) = true := by
    apply (allFin_eq_true_iff _).2
    intro a
    simp [finishRoundCandidate]
  have hcur' : allFin p.K (fun a : Fin p.K =>
      ((finishRoundCandidate l).currentRegisters a).isNone ==
        armPendingCheck (finishRoundCandidate l) a) = true := hcur
  have hcut' : allFin p.K (fun a : Fin p.K =>
      ((finishRoundCandidate l).cutoffRegisters a).isNone ==
        armPendingCheck (finishRoundCandidate l) a) = true := hcut
  rcases hscalar with ⟨⟨⟨⟨⟨⟨⟨⟨hs1, hsT⟩, hu1⟩, hug⟩, huT⟩, hgT⟩, huc⟩, _⟩, hcT⟩
  have huc' : l.cutoff ≤ l.cursor + 1 := by omega
  have hcT' : l.cursor + 1 ≤ p.T + 1 := by omega
  simp only [validLedgerCheck, show (finishRoundCandidate l).phase = Phase.ready from rfl,
    decide_true, Bool.true_or, Bool.not_true, Bool.false_or, Bool.and_true]
  rw [hzero, hready, hcur', hcut', hgamma', hinc', hregs', hraw']
  simp [finishRoundCandidate, hs1, hsT, hu1, hug, huT, hgT, huc', hcT']

/-- An arbitrary row in the actual complete suffix keeps the live choice
domain theorem's complete physical selection and initialized ledger, and
exposes the actual post-choice continuation. The continuing choice is an
explicitly excluded branch. -/
theorem complete_live_cutoff_post_choice
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ)
    (hstate : ((ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val]'k.isLt).input.state.coordinator =
        .live r q base) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h
    let x := (R[k.val]'k.isLt).input
    let current := ReferenceActivePhysicalStep.liveInput x r q base
    let prepared := ReferenceActivePhysicalStep.prepare x
    let chosen := CoordinatorRoundDispatch.dispatchLive
      current
    prepared.coordinator = .live r q base chosen ∧
    (show Prop from match chosen with
    | .continuingChosen _ _ _ _ => True
    | .cutoffChosen dispatched _ ledger _ _ _ _ _ _ selection =>
        dispatched.startResult.ledgerCommand = some (.initializeAt x.time) ∧
        dispatched.startResult.clock =
          { (ReferenceActivePhysicalStep.liveRegistersAt r x.time).priorClock with
              u := some x.time } ∧
        dispatched.startResult.pending = Finset.univ ∧
        dispatched.startResult.assignmentStart = none ∧
        dispatched.collectionInitialization = .success (some ledger) ∧
        ledger = CoordinatorStartRoundCutoffDispatch.collectionStartLedger
          (ReferenceActivePhysicalStep.liveRegistersAt r x.time)
          (ReferenceActivePhysicalStep.liveOwnedAt r q x.time) base x.time ∧
        ledger.sigma = r.payload.sigma.val + 1 ∧
        ledger.cutoff = x.time.val + 1 ∧
        ledger.freezeAt = (ReferenceActivePhysicalStep.liveRegistersAt r x.time).gridBoundary ∧
        ledger.pending = Finset.univ ∧
        ledger.cursor = x.time.val + 1 ∧
        ledger.increment = (fun _ : Fin p.K => 0) ∧
        ledger.gammaLoc = (fun _ : Fin p.K => 0) ∧
        ledger.rawBuffer = (fun _ _ => none) ∧
        ledger.phase = CoordinatorCollectionLedger.Phase.ready ∧
        CoordinatorLocalArmChoice.ChoiceInputsValid r.payload
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
            dispatched.startResult.clock.u) x.time
          (ReferenceActivePhysicalStep.liveRegistersAt r x.time).complementWeights ∧
        dispatched.startResult.clock.g ≤ p.T + 1 ∧
        CoordinatorLocalArmChoice.coordinatorArmChoice r.payload
          dispatched.startResult.pending
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p dispatched.startResult.clock.u)
          x.time (ReferenceActivePhysicalStep.liveRegistersAt r x.time).complementWeights
          x.row = some selection.arm ∧
        ∃ physical : ReferenceActivePhysicalStep.Selection x,
          prepared.coordinator.selection = some physical ∧
          physical.view.payload = r.payload ∧
          physical.view.pendingAtChoice = dispatched.startResult.pending ∧
          physical.view.cutoff =
            CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
              dispatched.startResult.clock.u ∧
          physical.started = dispatched.startResult ∧
          physical.arm = selection.arm ∧
          physical.view.pendingAtChoice = physical.started.pending ∧
          physical.view.cutoff = CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
            physical.started.clock.u ∧
          CoordinatorLocalArmChoice.coordinatorArmChoice physical.view.payload
            physical.view.pendingAtChoice physical.view.cutoff x.time
            physical.view.complementWeights x.row = some physical.arm ∧
        ∃ recording : CoordinatorRecordingOperation.Output p,
          CoordinatorRecorderComplementBridge.run
            (ReferenceActivePhysicalStep.collectionRecordingInput prepared r.payload
              dispatched.startResult
              (ReferenceActivePhysicalStep.liveRegistersAt r x.time).complementWeights) =
                some recording ∧
          let initialized := ReferenceActivePhysicalStep.sharedLedger ledger
          let enabled := ReferenceActivePhysicalStep.collectionEnabled initialized x.time
          let raw := CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording
          ∃ startedLedger : ReferenceActivePhysicalStep.Ledger rate,
            CoordinatorCollectionLedger.startRound
              (ReferenceActivePhysicalStep.sharedLedger ledger) (x.time.val + 1)
              (ReferenceActivePhysicalStep.collectionEnabled
                (ReferenceActivePhysicalStep.sharedLedger ledger) x.time)
              (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) =
                .success startedLedger ∧
            startedLedger = CoordinatorCollectionLedger.startRoundCandidate
              (ReferenceActivePhysicalStep.sharedLedger ledger) x.time
              (ReferenceActivePhysicalStep.collectionEnabled
                (ReferenceActivePhysicalStep.sharedLedger ledger) x.time)
              (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) ∧
            CoordinatorCollectionLedger.validLedgerCheck startedLedger = true ∧
            startedLedger.phase = CoordinatorCollectionLedger.Phase.started ∧
            startedLedger.cursor = x.time.val + 1 ∧
            startedLedger.increment = initialized.increment ∧
            startedLedger.enabledHistory =
              Function.update initialized.enabledHistory x.time (some enabled) ∧
            startedLedger.rawBuffer = (match raw with
              | none => initialized.rawBuffer
              | some (a, amount) =>
                  if initialized.currentRegisters a = none ∧ 0 < amount ∧
                      sourceRound x.time < initialized.freezeAt then
                    putRaw initialized.rawBuffer a x.time amount
                  else initialized.rawBuffer) ∧
            (∀ a current, initialized.currentRegisters a = some current →
              let transition := QueueReplay.transition (4 * rate.n) (0, current.queue)
                (localQueueRecord initialized x.time enabled raw a)
              startedLedger.currentRegisters a = some ⟨transition.2, transition.1⟩ ∧
              startedLedger.gammaLoc a = transition.1) ∧
            (∀ a, initialized.currentRegisters a = none →
              startedLedger.currentRegisters a = none ∧ startedLedger.gammaLoc a = 0) ∧
            (∀ a, localQueueRecord initialized x.time enabled raw a =
              if enabled then (true, localArrival raw a) else (false, 0)) ∧
            (∀ a current, initialized.currentRegisters a = some current → enabled = false →
              startedLedger.currentRegisters a = some ⟨current.queue, 0⟩ ∧
              startedLedger.gammaLoc a = 0) ∧
            (∀ a current, initialized.currentRegisters a = some current → enabled = true →
              localArrival raw a = 0 →
              startedLedger.currentRegisters a = some
                ⟨current.queue - min (4 * rate.n) current.queue,
                  min (4 * rate.n) current.queue⟩ ∧
              startedLedger.gammaLoc a = min (4 * rate.n) current.queue) ∧
            (∀ i, (x.state.upDecoderBank i).pending = []) ∧
            ∃ decoded bank,
              (ReferenceActivePhysicalStep.receiveUp prepared startedLedger).result =
                .rejected (decoded, bank) ∧
              decoded = { startedLedger with phase := CoordinatorCollectionLedger.Phase.decoded } ∧
              bank = CoordinatorUpReception.decoderBankAfter
                (ReferenceUpReception.receptionInputAtRow rate x.row
                  (ReferenceActivePhysicalStep.upInputs prepared startedLedger) x.time) ∧
              ∃ (finishedLedger : Ledger rate)
                (finished : CoordinatorPhaseClock.FinishRoundResult p)
                (diagnostic : ReferenceActivePhysicalStep.UpDiagnostic p rate),
                CoordinatorCollectionLedger.finishRound decoded = .success finishedLedger ∧
                finishedLedger = CoordinatorCollectionLedger.finishRoundCandidate decoded ∧
                CoordinatorCollectionLedger.validLedgerCheck finishedLedger = true ∧
                finishedLedger.increment =
                  (fun a => startedLedger.increment a + startedLedger.gammaLoc a) ∧
                finishedLedger.gammaLoc = (fun _ => 0) ∧
                finishedLedger.cursor = x.time.val + 2 ∧
                finishedLedger.phase = Phase.ready ∧
                finishedLedger.cutoffRegisters = startedLedger.cutoffRegisters ∧
                finishedLedger.currentRegisters = startedLedger.currentRegisters ∧
                finishedLedger.rawBuffer = startedLedger.rawBuffer ∧
                finishedLedger.pending = startedLedger.pending ∧
                CoordinatorPhaseClock.finishRound p rate.eta.val x.time
                  dispatched.startResult.clock finishedLedger.pending x.row = .ok finished ∧
                finished.clock = dispatched.startResult.clock ∧
                finished.pending = finishedLedger.pending ∧
                finished.ledgerCommand = some (.accumulateLocalServiceAt x.time) ∧
                (ReferenceActivePhysicalStep.receiveUp prepared startedLedger).diagnostic =
                  some diagnostic ∧
                diagnostic.input = ReferenceUpReception.receptionInputAtRow rate x.row
                  (ReferenceActivePhysicalStep.upInputs prepared startedLedger) x.time ∧
                diagnostic.raw = none ∧
                ReferenceActivePhysicalStep.collectionPostChoice prepared r.payload
                  (ReferenceActivePhysicalStep.sharedLedger ledger) dispatched.startResult
                  (ReferenceActivePhysicalStep.liveRegistersAt r x.time).complementWeights =
                    ⟨.collection r.payload finishedLedger finished.clock.lastProposal,
                      bank, none, some recording, some diagnostic⟩ ∧
                prepared.observeCoordinator =
                  ⟨.collection r.payload finishedLedger finished.clock.lastProposal,
                    bank, none, some recording, some diagnostic⟩ ∧
                (R[k.val]'k.isLt).output.coordinator =
                  ⟨.collection r.payload finishedLedger finished.clock.lastProposal,
                    bank, none, some recording, some diagnostic⟩ ∧
                (R[k.val]'k.isLt).output.next.coordinator =
                  .collection r.payload finishedLedger finished.clock.lastProposal ∧
                (R[k.val]'k.isLt).output.next.upDecoderBank = bank
    | _ => False) := by
  classical
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h
  let x := (R[k.val]'k.isLt).input
  let current := ReferenceActivePhysicalStep.liveInput x r q base
  let prepared := ReferenceActivePhysicalStep.prepare x
  have hC := ReferenceCompleteLiveChoiceDomains.complete_live_dispatch_choice_exists
    rate rewards C_star C_h source k r q base hstate
  rcases hC with ⟨hprepared, hbranch⟩
  refine ⟨hprepared, ?_⟩
  generalize hchosen : CoordinatorRoundDispatch.dispatchLive current = outcome at hbranch ⊢
  cases outcome with
  | continuingChosen dispatched startRoundEq continuation selection =>
      trivial
  | cutoffChosen dispatched startRoundEq ledger hinit hledger hvalid hclock hpending
      hassignment selection =>
      have hdomains := hvalid
      rcases hbranch with ⟨hcommand, hclockShape, hpendingShape, hassignment,
        hinitialized, hledgerField, hchoice, hgrid, harm, ⟨physical, hphysicalSelection,
          hphysicalPayload, hphysicalPending, hphysicalCutoff, hphysicalStarted,
          hphysicalArm, hphysicalPendingStarted,
          ⟨hphysicalCutoffStarted, hphysicalChoice⟩⟩⟩
      have hfields := CoordinatorStartRoundCutoffDispatch.collectionStartLedger_fields
        (ReferenceActivePhysicalStep.liveRegistersAt r x.time)
        (ReferenceActivePhysicalStep.liveOwnedAt r q x.time) base x.time
      rcases hfields with ⟨_, hsigma, hcutoff, hfreeze, _, hpendingLedger, _, _, _,
        hincrement, hgamma, hraw, _, hcursor, hphase⟩
      have hledgerShape :
          ledger.sigma = r.payload.sigma.val + 1 ∧
          ledger.cutoff = x.time.val + 1 ∧
          ledger.freezeAt = (ReferenceActivePhysicalStep.liveRegistersAt r x.time).gridBoundary ∧
          ledger.pending = Finset.univ ∧
          ledger.cursor = x.time.val + 1 ∧
          ledger.increment = (fun _ : Fin p.K => 0) ∧
          ledger.gammaLoc = (fun _ : Fin p.K => 0) ∧
          ledger.rawBuffer = (fun _ _ => none) ∧
          ledger.phase = Phase.ready := by
        rw [hledgerField]
        exact ⟨hsigma, hcutoff, hfreeze, hpendingLedger, hcursor,
          hincrement, hgamma, hraw, hphase⟩
      rcases hledgerShape with ⟨hsigmaLedger, hcutoffLedger, hfreezeLedger,
        hpendingLedger, hcursorLedger, hincrementLedger, hgammaLedger,
        hrawLedger, hphaseLedger⟩
      refine ⟨hcommand, hclockShape, hpendingShape, hassignment, hinitialized,
        hledgerField, hsigmaLedger, hcutoffLedger, hfreezeLedger, hpendingLedger,
        hcursorLedger, hincrementLedger, hgammaLedger, hrawLedger, hphaseLedger,
        hchoice, hgrid, harm, physical, hphysicalSelection, hphysicalPayload,
        hphysicalPending, hphysicalCutoff, hphysicalStarted, hphysicalArm,
        hphysicalPendingStarted, hphysicalCutoffStarted, hphysicalChoice, ?_⟩
      let recordingInput := ReferenceActivePhysicalStep.collectionRecordingInput
        prepared r.payload dispatched.startResult
        (ReferenceActivePhysicalStep.liveRegistersAt r x.time).complementWeights
      have hlocal : CoordinatorRecorderComplementBridge.LocalInputsValid
          recordingInput := by
        refine ⟨?_, ?_⟩
        · simpa [recordingInput,
            ReferenceActivePhysicalStep.collectionRecordingInput] using hgrid
        · intro j
          exact ⟨hchoice.anchor_le_current j, hchoice.current_le_twice_anchor j⟩
      obtain ⟨recording, hrecording⟩ :=
        ReferenceContinuingCollectionStartDomains.collection_recorder_run_total
          recordingInput hlocal rfl
      refine ⟨recording, ?_, ?_⟩
      · simpa [recordingInput, prepared, x] using hrecording
      · let raw := CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording
        let l := ReferenceActivePhysicalStep.sharedLedger ledger
        let enabled := ReferenceActivePhysicalStep.collectionEnabled l x.time
        let candidate := CoordinatorCollectionLedger.startRoundCandidate l x.time enabled raw
        let regs := ReferenceActivePhysicalStep.liveRegistersAt r x.time
        let owned := ReferenceActivePhysicalStep.liveOwnedAt r q x.time
        rcases hvalid with ⟨_, _, hbefore, htimeGrid, hgridBound, _, _, _, _, _,
          _, hledgerValid⟩
        have hvalidInitial : CoordinatorCollectionLedger.validLedgerCheck ledger = true := by
          rw [hledgerField]
          simpa [current, ReferenceActivePhysicalStep.liveInput,
            ReferenceActivePhysicalStep.liveRegistersAt,
            ReferenceActivePhysicalStep.liveOwnedAt,
            CoordinatorStartRoundCutoffDispatch.collectionStartLedger] using hledgerValid
        have hvalidL : CoordinatorCollectionLedger.validLedgerCheck l = true := by
          have hcheckEq : CoordinatorCollectionLedger.validLedgerCheck l =
              CoordinatorCollectionLedger.validLedgerCheck ledger := by
            cases ledger
            rfl
          rw [hcheckEq]
          exact hvalidInitial
        have hshapeL :
            l.sigma = r.payload.sigma.val + 1 ∧
            l.cutoff = x.time.val + 1 ∧
            l.freezeAt = (ReferenceActivePhysicalStep.liveRegistersAt r x.time).gridBoundary ∧
            l.pending = Finset.univ ∧ l.cursor = x.time.val + 1 ∧
            l.increment = (fun _ : Fin p.K => 0) ∧
            l.gammaLoc = (fun _ : Fin p.K => 0) ∧
            l.rawBuffer = (fun _ _ => none) ∧ l.phase = Phase.ready := by
          simpa [l, ReferenceActivePhysicalStep.sharedLedger] using
            (show ledger.sigma = r.payload.sigma.val + 1 ∧
              ledger.cutoff = x.time.val + 1 ∧
              ledger.freezeAt = (ReferenceActivePhysicalStep.liveRegistersAt r x.time).gridBoundary ∧
              ledger.pending = Finset.univ ∧ ledger.cursor = x.time.val + 1 ∧
              ledger.increment = (fun _ : Fin p.K => 0) ∧
              ledger.gammaLoc = (fun _ : Fin p.K => 0) ∧
              ledger.rawBuffer = (fun _ _ => none) ∧ ledger.phase = Phase.ready from
                ⟨hsigmaLedger, hcutoffLedger, hfreezeLedger, hpendingLedger,
                  hcursorLedger, hincrementLedger, hgammaLedger, hrawLedger,
                  hphaseLedger⟩)
        rcases hshapeL with ⟨hsigmaL, hcutoffL, hfreezeL, hpendingL,
          hcursorL, hincrementL, hgammaL, hrawL, hphaseL⟩
        have htimeGridX : x.time.val + 1 ≤ r.gridBoundary := by
          simpa [current, ReferenceActivePhysicalStep.liveInput,
            ReferenceActivePhysicalStep.liveRegistersAt] using htimeGrid
        have htimes :
            1 ≤ l.sigma ∧ l.sigma ≤ p.T ∧ 1 ≤ l.cutoff ∧
            l.cutoff ≤ l.freezeAt ∧ l.cutoff ≤ p.T ∧
            l.freezeAt ≤ p.T + 1 ∧ l.cutoff ≤ l.cursor ∧
            l.cursor ≤ p.T + 1 := by
          rw [hsigmaL, hcutoffL, hfreezeL, hcursorL]
          refine ⟨by omega, by omega, by omega, ?_, by omega, ?_, by omega, by omega⟩
          · simpa [ReferenceActivePhysicalStep.liveRegistersAt] using htimeGridX
          · exact hgridBound
        have hcursor : l.cursor = CoordinatorCollectionLedger.sourceRound x.time := by
          simpa [CoordinatorCollectionLedger.sourceRound,
            ReferenceActivePhysicalStep.liveRegistersAt] using hcursorL
        have hrawDomain : CoordinatorCollectionLedger.rawInputDomainCheck raw = true := by
          cases hgate : recording.gateArm with
          | none =>
              simp [raw, CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder,
                CoordinatorCollectionLedger.rawInputDomainCheck, hgate]
          | some arm =>
              simpa [raw, CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder,
                CoordinatorCollectionLedger.rawInputDomainCheck, hgate] using
                recording.rawArrival_le_D
        have hfresh := raw_slot_fresh_of_ready_valid l x.time raw hvalidL hphaseL hcursor
        have hmassAll := ReferenceCompleteCoordinatorMass.complete_coordinator_input_output_mass
          rate rewards C_star C_h source
        dsimp only at hmassAll
        have hinputMass := (hmassAll k).1
        unfold ReferenceCompleteCoordinatorMass.coordinatorInputMass at hinputMass
        have hxstate :
            ((ReferenceCompletePhysicalHistory.completeSuffixRecords
              rate source rewards C_star C_h)[k.val]'k.isLt).input.state.coordinator =
                .live r q base := by
          simpa [R, x] using hstate
        rw [hxstate] at hinputMass
        rcases hinputMass with ⟨hfastMass, _⟩
        have hjoint : ∀ (a : Fin p.K) (cut : CoordinatorCollectionLedger.CutoffRegister)
            (cur : CoordinatorCollectionLedger.CurrentRegister),
            l.cutoffRegisters a = some cut → l.currentRegisters a = some cur →
            cut.score + l.increment a + cur.queue ≤ x.time.val * D p := by
          intro a cut cur hcut hcur
          have hcut' : CoordinatorStartRoundCutoffDispatch.outsideRegisters regs owned a =
              some cut := by
            simpa [l, ReferenceActivePhysicalStep.sharedLedger, hledgerField,
              CoordinatorStartRoundCutoffDispatch.collectionStartLedger] using hcut
          have hfast : a ∈ CanonicalFastSampling.fastArmFinset r.payload.slowSet := by
            by_contra hnot
            have hnone : CoordinatorStartRoundCutoffDispatch.outsideRegisters regs owned a = none := by
              unfold CoordinatorStartRoundCutoffDispatch.outsideRegisters
              split
              · rename_i hmem
                exact False.elim (hnot hmem)
              · rfl
            rw [hnone] at hcut'
            cases hcut'
          let j : CanonicalFastSampling.FastArm r.payload.slowSet := ⟨a, hfast⟩
          let reg : CoordinatorCollectionLedger.CutoffRegister := {
            score := r.complementScores j
            queue := q.queue j
            lastService := q.previousService j }
          have houtside :
              CoordinatorStartRoundCutoffDispatch.outsideRegisters regs owned a = some reg := by
            simp [CoordinatorStartRoundCutoffDispatch.outsideRegisters, regs, owned,
              ReferenceActivePhysicalStep.liveRegistersAt,
              ReferenceActivePhysicalStep.liveOwnedAt, hfast, j, reg]
          have hcutEq : cut = reg := Option.some.inj (hcut'.symm.trans houtside)
          have hcur' :
              (CoordinatorStartRoundCutoffDispatch.outsideRegisters regs owned a).map
                (fun reg => ⟨reg.queue, reg.lastService⟩) = some cur := by
            simpa [l, ReferenceActivePhysicalStep.sharedLedger, hledgerField,
              CoordinatorStartRoundCutoffDispatch.collectionStartLedger] using hcur
          have hcurEq : cur = ⟨reg.queue, reg.lastService⟩ := by
            rw [houtside] at hcur'
            exact (Option.some.inj (by simpa using hcur')).symm
          subst cut
          subst cur
          have hincrementAt : l.increment a = 0 := congrFun hincrementL a
          simpa [reg, hincrementAt] using hfastMass j
        have hvalidCandidate := startRoundCandidate_valid l x.time enabled raw
          hvalidL hphaseL hcursor htimes hrawDomain hfresh hjoint
        have hstartDomain :
            CoordinatorCollectionLedger.validLedgerCheck l = true ∧
            l.phase = CoordinatorCollectionLedger.Phase.ready ∧
            x.time.val + 1 = l.cursor ∧ 1 ≤ x.time.val + 1 ∧
            x.time.val + 1 ≤ p.T ∧
            CoordinatorCollectionLedger.rawInputDomainCheck raw = true := by
          exact ⟨hvalidL, hphaseL, hcursor.symm, by omega, by omega, hrawDomain⟩
        let index : Fin p.T := ⟨x.time.val + 1 - 1, by omega⟩
        have hindex : index = x.time := by
          apply Fin.ext
          simp [index]
        have hfreshIndex : CoordinatorCollectionLedger.rawSlotFreshCheck l index raw = true := by
          rw [hindex]
          exact hfresh
        have hstart : CoordinatorCollectionLedger.startRound l (x.time.val + 1)
            enabled raw = .success candidate := by
          unfold CoordinatorCollectionLedger.startRound
          rw [dite_eq_left hstartDomain]
          change (if CoordinatorCollectionLedger.rawSlotFreshCheck l index raw then
            (let next := CoordinatorCollectionLedger.startRoundCandidate l index enabled raw
             if CoordinatorCollectionLedger.validLedgerCheck next then
               Checked.success next else Checked.invalid)
            else Checked.invalid) = Checked.success candidate
          rw [ite_eq_left (by simpa using hfreshIndex)]
          have hcandidateIndex :
              CoordinatorCollectionLedger.startRoundCandidate l index enabled raw = candidate := by
            rw [hindex]
          rw [hcandidateIndex]
          change (if CoordinatorCollectionLedger.validLedgerCheck candidate then
            Checked.success candidate else Checked.invalid) = Checked.success candidate
          rw [ite_eq_left hvalidCandidate]
        have hlaunchNone : ReferenceCorrectedInitializationLaunch.correctedLaunch
            rate source rewards C_star C_h ≠ none := by
          intro hnone
          have hempty : R = [] := by simp [R, ReferenceCompletePhysicalHistory.completeSuffixRecords, hnone]
          have hlt : k.val < 0 := by simpa [hempty, R] using k.isLt
          omega
        let initial := ReferenceCompletePhysicalHistory.correctedLaunchPayload
          rate source rewards C_star C_h hlaunchNone
        have hlaunch := ReferenceCompletePhysicalHistory.correctedLaunch_eq_some_payload
          rate source rewards C_star C_h hlaunchNone
        have hmode := ReferenceCompletePhysicalHistory.activeMode_of_launch_eq_some
          rate source rewards C_star C_h initial hlaunch
        have hspan : ReferenceCompletePhysicalHistory.physicalStart rate source rewards
            C_star C_h + (p.T - ReferenceCompletePhysicalHistory.physicalStart rate source
              rewards C_star C_h) ≤ p.T := by
          have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T rate source rewards
            C_star C_h
          omega
        let run := ReferenceActivePhysicalHorizon.run initial source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
          (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
          (p.T - ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
          hspan hmode
        have hrecords := ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
          rate source rewards C_star C_h initial hlaunch
        let record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) :=
          R[k.val]'k.isLt
        have hrecordMem : record ∈ run.records := by
          rw [← hrecords]
          exact List.getElem_mem k.isLt
        have hinitial : ReferenceUpDecoderBankInvariant.upBankInvariant initial := by
          simpa [ReferenceUpDecoderBankInvariant.upBankInvariant,
            ReferenceUpDecoderBankInvariant.coordinatorBankInvariant, initial,
            ReferenceCompletePhysicalHistory.correctedLaunchPayload,
            ReferenceCorrectedInitializationLaunch.correctedLaunch, hlaunch] using
              (ReferenceUpDecoderBankInvariant.firstState_upBankInvariant
                (p := p) (rate := rate) initial.activations initial.followers)
        have hrecordState : record.input.state.coordinator = .live r q base := by
          simpa [record, R, x] using hstate
        let cutoffOutcome : CoordinatorRoundDispatch.LiveOutcome current :=
          .cutoffChosen dispatched startRoundEq ledger hinit hledger hdomains hclock hpending
            hassignment selection
        have hdispatchRecordLive : CoordinatorRoundDispatch.dispatchLive
            (ReferenceActivePhysicalStep.liveInput record.input r q base) = cutoffOutcome := by
          simpa [cutoffOutcome, record, R, x, current,
            ReferenceActivePhysicalStep.liveInput] using hchosen
        have hdispatchRecord : ReferenceActivePhysicalStep.dispatch record.input =
            ReferenceActivePhysicalStep.DispatchCut.live r q base cutoffOutcome := by
          simp only [ReferenceActivePhysicalStep.dispatch, hrecordState,
            CoordinatorRoundDispatch.dispatch, hdispatchRecordLive]
          rfl
        have hcut : ReferenceUpDecoderBankInvariant.isActualCutoffChosen
            record.output.preparation.coordinator := by
          rw [record.output_eq]
          change ReferenceUpDecoderBankInvariant.isActualCutoffChosen
            (ReferenceActivePhysicalStep.dispatch record.input)
          exact ⟨r, q, base, cutoffOutcome, hrecordState, hdispatchRecord, by
            simp [cutoffOutcome]⟩
        have hempty := ReferenceUpDecoderBankInvariant.run_cutoff_up_pending_empty
          initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
          rewards (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
          (p.T - ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
          hspan hmode hinitial record hrecordMem hcut
        have hinvRecord := ReferenceUpDecoderBankInvariant.run_record_input_upBankInvariant
          initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
          rewards (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
          (p.T - ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
          hspan hmode hinitial record hrecordMem
        have hbankWellFormed : CoordinatorUpReception.decoderBankWellFormed p
            x.state.upDecoderBank := by
          have hparts : ReferenceUpDecoderBankInvariant.coordinatorBankInvariant
              record.input.state.coordinator record.input.state.upDecoderBank := by
            simpa [ReferenceUpDecoderBankInvariant.upBankInvariant] using hinvRecord
          have hparts' := hparts
          simp [ReferenceUpDecoderBankInvariant.coordinatorBankInvariant, hrecordState] at hparts'
          simpa [record, R, x] using hparts'.1
        let receiveInput := ReferenceUpReception.receptionInputAtRow rate x.row
          (ReferenceActivePhysicalStep.upInputs prepared candidate) x.time
        have hreceiverDomain : CoordinatorUpReception.receptionInputDomain receiveInput := by
          have hphaseCandidate : candidate.phase = CoordinatorCollectionLedger.Phase.started := rfl
          have hsigmaCandidate : candidate.sigma = r.payload.sigma.val + 1 := by
            simp [candidate, CoordinatorCollectionLedger.startRoundCandidate, hsigmaL]
          have hcutoffCandidate : candidate.cutoff = x.time.val + 1 := by
            simp [candidate, CoordinatorCollectionLedger.startRoundCandidate, hcutoffL]
          have hcursorCandidate : candidate.cursor = CoordinatorCollectionLedger.sourceRound x.time := by
            simp [candidate, CoordinatorCollectionLedger.startRoundCandidate,
              CoordinatorCollectionLedger.sourceRound]
          have hbankCheck : CoordinatorUpReception.decoderBankCheck p
              receiveInput.upDecoderBank = true :=
            (CoordinatorUpReception.decoderBankCheck_eq_true_iff p _).2 hbankWellFormed
          have hsigma : 1 ≤ receiveInput.ledger.sigma := by
            change 1 ≤ candidate.sigma
            rw [hsigmaCandidate]
            omega
          have hcutoff : 1 ≤ receiveInput.ledger.cutoff := by
            change 1 ≤ candidate.cutoff
            rw [hcutoffCandidate]
            omega
          have hcutCursor : receiveInput.ledger.cutoff ≤ receiveInput.ledger.cursor := by
            change candidate.cutoff ≤ candidate.cursor
            rw [hcutoffCandidate, hcursorCandidate]
            simp [CoordinatorCollectionLedger.sourceRound]
          have hcursorTime : receiveInput.ledger.cursor ≤ p.T := by
            change candidate.cursor ≤ p.T
            rw [hcursorCandidate]
            simp [CoordinatorCollectionLedger.sourceRound]
          refine ⟨hvalidCandidate, hsigma, hphaseCandidate, hcutoff, hcutCursor,
            hcursorTime, ?_, hbankCheck⟩
          change candidate.cursor = CoordinatorCollectionLedger.sourceRound x.time
          exact hcursorCandidate
        have hquota : 1 < AffineBatchDecoder.quota p := by
          have hfield : 0 < OrdinaryMessageCodec.fieldWidth p.T (D p) := by
            unfold OrdinaryMessageCodec.fieldWidth
            have hprod : 0 < p.T * D p := Nat.mul_pos (T_pos p) (D_pos p)
            exact Nat.clog_pos (by decide) (by omega)
          have hwidth : 1 < AffineBatchDecoder.width p := by
            unfold AffineBatchDecoder.width
            omega
          unfold AffineBatchDecoder.quota
          omega
        let channel := receiveInput.upDecoderBank receiveInput.selectedFollower
        have hchannelEmpty : channel.pending = [] := by
          change (x.state.upDecoderBank (ReferenceActivePhysicalStep.upSenderIndex x)).pending = []
          simpa [record, R, x] using
              hempty (ReferenceActivePhysicalStep.upSenderIndex x)
        have hpositive :
            (AffineBatchDecoder.positiveAt p
              (CoordinatorUpReception.traceAt receiveInput) receiveInput.time).length ≤ 1 := by
          unfold AffineBatchDecoder.positiveAt
          split <;> simp
        have hshort :
            (channel.pending ++ AffineBatchDecoder.positiveAt p
              (CoordinatorUpReception.traceAt receiveInput) receiveInput.time).length <
                AffineBatchDecoder.quota p := by
          rw [hchannelEmpty]
          simpa using Nat.lt_of_le_of_lt hpositive hquota
        have hshort' :
            ((receiveInput.upDecoderBank receiveInput.selectedFollower).pending ++
              AffineBatchDecoder.positiveAt p (CoordinatorUpReception.traceAt receiveInput)
                receiveInput.time).length < AffineBatchDecoder.quota p := by
          simpa [channel] using hshort
        have hrawNone : (CoordinatorUpReception.decoderTransition receiveInput).2 = none := by
          simp only [CoordinatorUpReception.decoderTransition, AffineBatchDecoder.decodeStep]
          unfold AffineBatchDecoder.stepOutput
          rw [ite_eq_left hshort']
        have hinputCheck : CoordinatorUpReception.receptionInputCheck receiveInput = true :=
          (CoordinatorUpReception.receptionInputCheck_eq_true_iff receiveInput).2 hreceiverDomain
        have hdecodeNone :=
          CoordinatorUpReception.decodeUp_none_rejected receiveInput hreceiverDomain
        have hrawInline : (CoordinatorUpReception.decoderTransition
            (ReferenceUpReception.receptionInputAtRow rate x.row
              (ReferenceActivePhysicalStep.upInputs prepared candidate) x.time)).2 = none := by
          simpa [receiveInput] using hrawNone
        have hfilteredNone : ReferenceUpReception.filterRawByExpected
            (CoordinatorUpReception.decoderTransition
              (ReferenceUpReception.receptionInputAtRow rate x.row
                (ReferenceActivePhysicalStep.upInputs prepared candidate) x.time)).2
            (ReferenceActivePhysicalStep.upExpected prepared) = none := by
          rw [hrawInline]
          simp [ReferenceUpReception.filterRawByExpected]
        have heffective : ReferenceCollectionSegmentExtraction.effectiveParse x candidate = none := by
          unfold ReferenceCollectionSegmentExtraction.effectiveParse
          rw [hfilteredNone]
          rfl
        have hreceiverEq := ReferenceCollectionSegmentExtraction.receiveUp_filtered
          x candidate hinputCheck
        have hdecodeCandidate : CoordinatorCollectionLedger.decodeUp candidate
            (ReferenceActivePhysicalStep.upSenderIndex x) none =
              .rejected { candidate with phase := CoordinatorCollectionLedger.Phase.decoded } := by
          have hinputLedger : receiveInput.ledger = candidate := rfl
          have hinputSender : receiveInput.selectedFollower =
              ReferenceActivePhysicalStep.upSenderIndex x := rfl
          rw [← hinputLedger, ← hinputSender]
          exact hdecodeNone
        rw [heffective, hdecodeCandidate] at hreceiverEq
        simp only [CoordinatorUpReception.packDecodeResult] at hreceiverEq
        have hrejected : (ReferenceActivePhysicalStep.receiveUp prepared candidate).result =
            .rejected ({candidate with phase := CoordinatorCollectionLedger.Phase.decoded},
              CoordinatorUpReception.decoderBankAfter receiveInput) := by
          simpa [receiveInput] using hreceiverEq
        let decoded : Ledger rate :=
          {candidate with phase := CoordinatorCollectionLedger.Phase.decoded}
        let bank : CoordinatorUpReception.UpDecoderBank p :=
          CoordinatorUpReception.decoderBankAfter receiveInput
        have hdecodedValid : validLedgerCheck decoded = true := by
          exact CoordinatorUpReception.validLedgerCheck_after_decode candidate hvalidCandidate rfl
        have hsum (a : Fin p.K) : decoded.increment a + decoded.gammaLoc a ≤ p.T * D p := by
          cases hc : l.currentRegisters a with
          | none => simp [decoded, candidate, startRoundCandidate, hc, hincrementL]
          | some cur =>
              obtain ⟨cut, hcut⟩ : ∃ cut, l.cutoffRegisters a = some cut := by
                cases hk : l.cutoffRegisters a with
                | some cut => exact ⟨cut, rfl⟩
                | none =>
                    have hn := (currentRegister_none_iff_cutoffRegister_none l hvalidL a).2 hk
                    rw [hc] at hn
                    cases hn
              have hmass := hjoint a cut cur hcut hc
              let entry := localQueueRecord l x.time enabled raw a
              let update := QueueReplay.transition (4 * rate.n) (0, cur.queue) entry
              have htotal : update.1 + update.2 =
                  cur.queue + RecordedQueueRun.acceptedArrival entry := by
                simpa [update] using
                  RecordedQueueRun.transition_total (4 * rate.n) (0, cur.queue) entry
              have harrival : RecordedQueueRun.acceptedArrival entry ≤ D p :=
                (localQueueRecord_acceptedArrival_le l x.time enabled raw a).trans
                  (localQueueRecord_arrival_le_D l x.time enabled raw a hrawDomain)
              have hcalendar : l.increment a + update.1 ≤ (x.time.val + 1) * D p := by
                rw [Nat.add_mul, Nat.one_mul]
                omega
              have hbound := hcalendar.trans
                (Nat.mul_le_mul_right (D p) (Nat.succ_le_of_lt x.time.isLt))
              simpa [decoded, candidate, startRoundCandidate, hc, update, entry] using hbound
        let finishedLedger := finishRoundCandidate decoded
        have hfinishedValid : validLedgerCheck finishedLedger = true :=
          finishCandidate_valid decoded hdecodedValid rfl hsum
        have hfinish : CoordinatorCollectionLedger.finishRound decoded =
            .success finishedLedger := by
          have hinput : validLedgerCheck decoded = true ∧
              decoded.phase = Phase.decoded ∧ decoded.cursor ≤ p.T :=
            ⟨hdecodedValid, rfl, Nat.succ_le_of_lt x.time.isLt⟩
          simp only [CoordinatorCollectionLedger.finishRound, dite_eq_left hinput]
          exact ite_eq_left hfinishedValid
        have hpriorValid : CoordinatorPhaseClock.clockRegistersValid p rate.eta.val
            r.priorClock := by
          by_contra hv
          have hs := startRoundEq
          have hp := ReferenceCoordinatorClockDomains.proposalParameterValid_of_rate rate
          simp [CoordinatorPhaseClock.startRound, current, liveInput, liveRegistersAt,
            hp, hv] at hs
        have hpriorSigma : r.priorClock.sigma = some r.payload.sigma := hdomains.1
        have hpriorGrid : r.gridBoundary = r.priorClock.g := hdomains.2.1
        have hclockValid : CoordinatorPhaseClock.clockRegistersValid p rate.eta.val
            dispatched.startResult.clock := by
          rw [hclockShape]
          simp only [CoordinatorPhaseClock.clockRegistersValid, liveRegistersAt,
            hpriorSigma] at hpriorValid ⊢
          exact ⟨hpriorValid.1, hpriorValid.2.1, hpriorValid.2.2.1,
            hbefore, by simpa [hpriorGrid] using htimeGridX⟩
        let finished : CoordinatorPhaseClock.FinishRoundResult p := {
          clock := dispatched.startResult.clock
          pending := finishedLedger.pending
          ledgerCommand := some (.accumulateLocalServiceAt x.time) }
        have hclockFinish : CoordinatorPhaseClock.finishRound p rate.eta.val x.time
            dispatched.startResult.clock finishedLedger.pending x.row = .ok finished := by
          apply CoordinatorPhaseClock.finishRound_collection p rate.eta.val x.time
            r.payload.sigma x.time dispatched.startResult.clock finishedLedger.pending
            x.row hclockValid
          · rw [hclockShape]
            exact hpriorSigma
          · rw [hclockShape]
          · exact Nat.le_refl _
        obtain ⟨diagnostic, hdiagnostic, hdiagnosticInput, hdiagnosticRaw⟩ :
            ∃ diagnostic : UpDiagnostic p rate,
              (receiveUp prepared candidate).diagnostic = some diagnostic ∧
              diagnostic.input = receiveInput ∧ diagnostic.raw = none := by
          simp only [receiveUp, show CoordinatorUpReception.receptionInputCheck
            (ReferenceUpReception.receptionInputAtRow rate x.row
              (upInputs prepared candidate) x.time) = true from hinputCheck,
            ite_true]
          exact ⟨_, rfl, rfl, hrawNone⟩
        have htail : collectionPostChoice prepared r.payload l dispatched.startResult
            (liveRegistersAt r x.time).complementWeights =
              ⟨.collection r.payload finishedLedger finished.clock.lastProposal,
                bank, none, some recording, some diagnostic⟩ := by
          rw [collectionPostChoice_after_start prepared r.payload l dispatched.startResult
            (liveRegistersAt r x.time).complementWeights recording candidate hrecording hstart]
          rw [collectionFinish_success r.payload dispatched.startResult recording
            (receiveUp prepared candidate) decoded finishedLedger bank finished
            (Or.inr hrejected) hfinish hclockFinish, hdiagnostic]
        have hpreparedCut : prepared.coordinator = .live r q base cutoffOutcome := by
          simpa [prepared, record, R, x, prepare] using hdispatchRecord
        have hobserve : prepared.observeCoordinator =
              ⟨.collection r.payload finishedLedger finished.clock.lastProposal,
                bank, none, some recording, some diagnostic⟩ := by
          rw [observeCoordinator_live_equation prepared r q base cutoffOutcome hpreparedCut]
          have hselected : (DispatchCut.live r q base cutoffOutcome).selection ≠ none := by
            rw [← hpreparedCut, hphysicalSelection]
            exact Option.some_ne_none _
          rw [ite_eq_right hselected]
          exact htail
        have houtput : record.output.coordinator =
              ⟨.collection r.payload finishedLedger finished.clock.lastProposal,
                bank, none, some recording, some diagnostic⟩ := by
          rw [record.output_eq]
          exact hobserve
        have hqueueRecord (a : Fin p.K) : localQueueRecord l x.time enabled raw a =
            if enabled then (true, localArrival raw a) else (false, 0) := by
          cases he : enabled with
          | false => simp [localQueueRecord]
          | true =>
              have ht : sourceRound x.time < l.freezeAt :=
                (of_decide_eq_true he).2.2
              simp [localQueueRecord, ht]
        have hknown (a : Fin p.K) (cur : CurrentRegister)
            (hc : l.currentRegisters a = some cur) :
            candidate.currentRegisters a = some
              ⟨(QueueReplay.transition (4 * rate.n) (0, cur.queue)
                (localQueueRecord l x.time enabled raw a)).2,
                (QueueReplay.transition (4 * rate.n) (0, cur.queue)
                  (localQueueRecord l x.time enabled raw a)).1⟩ ∧
            candidate.gammaLoc a = (QueueReplay.transition (4 * rate.n) (0, cur.queue)
              (localQueueRecord l x.time enabled raw a)).1 := by
          exact ⟨startRoundCandidate_known_transition l x.time enabled raw a cur hc,
            by simp [candidate, startRoundCandidate, hc]⟩
        have hdisabled (a : Fin p.K) (cur : CurrentRegister)
            (hc : l.currentRegisters a = some cur) (he : enabled = false) :
            candidate.currentRegisters a = some ⟨cur.queue, 0⟩ ∧ candidate.gammaLoc a = 0 := by
          have hk := hknown a cur hc
          rw [hqueueRecord] at hk
          simpa [he, QueueReplay.transition] using hk
        have hzeroArrival (a : Fin p.K) (cur : CurrentRegister)
            (hc : l.currentRegisters a = some cur) (he : enabled = true)
            (hz : localArrival raw a = 0) :
            candidate.currentRegisters a = some ⟨cur.queue - min (4 * rate.n) cur.queue,
              min (4 * rate.n) cur.queue⟩ ∧
            candidate.gammaLoc a = min (4 * rate.n) cur.queue := by
          have hk := hknown a cur hc
          rw [hqueueRecord] at hk
          simpa [he, hz, QueueReplay.transition] using hk
        refine ⟨candidate, hstart, rfl, hvalidCandidate, rfl, rfl, rfl, rfl, ?_,
          hknown, ?_, hqueueRecord, hdisabled, hzeroArrival,
          (by intro i; simpa [record, R, x] using hempty i),
          decoded, bank, hrejected, rfl, rfl, finishedLedger, finished, diagnostic,
          hfinish, rfl, hfinishedValid, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
          hclockFinish, rfl, rfl, rfl, hdiagnostic, hdiagnosticInput,
          hdiagnosticRaw, htail, hobserve, houtput, ?_, ?_⟩
        · change candidate.rawBuffer = (match (motive := Option (Fin p.K × ℕ) →
              Fin p.K → Fin p.T → Option ℕ) raw with
            | none => l.rawBuffer
            | some (a, amount) =>
                if l.currentRegisters a = none ∧ 0 < amount ∧
                    sourceRound x.time < l.freezeAt then
                  putRaw l.rawBuffer a x.time amount else l.rawBuffer)
          cases hr : raw with
          | none => simp [candidate, startRoundCandidate, hr]
          | some pair =>
              rcases pair with ⟨a, amount⟩
              simp [candidate, startRoundCandidate, hr]
        · intro a ha
          change l.currentRegisters a = none at ha
          exact ⟨by simp [candidate, startRoundCandidate, ha],
            startRoundCandidate_unknown_zero l x.time enabled raw a ha⟩
        · rw [record.output_eq]
          exact congrArg CoordinatorObservation.configuration hobserve
        · rw [record.output_eq]
          exact congrArg CoordinatorObservation.upDecoderBank hobserve
  | clockFailure failure hdispatch =>
      simp at hbranch
  | initializerFailure dispatched hstart checked hchecked =>
      simp at hbranch
  | localFailure dispatched hstart reason =>
      simp at hbranch

end Bandits.Support

end
