/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceContinuingCollectionStartDomains

import Lean.Elab.Tactic.Omega

/-!
# Continuing collection rejection and finish domains

This module continues the actual post-cutoff collection operation from the
proved START producer. It filters the actual UP decoder output against the
same-row prepared sender, handles only the local parse/acceptance rejection
branch, and proves the actual ledger and clock finish operations. The literal
ready-state input remains an internal induction condition; this is not a
generated-run invariant or a manuscript theorem.

Source evidence: `sources/zip4/manuscript/06_interruptions.tex:41-70,246-295`,
`sources/zip4/manuscript/04_slow_fast_learner.tex:157-174`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-64`.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions

namespace Bandits.Support.ReferenceContinuingCollectionRejectedFinishDomains

abbrev Parameters := ReferenceContinuingCollectionStartDomains.Parameters
abbrev RateInput := ReferenceContinuingCollectionStartDomains.RateInput
abbrev State := ReferenceContinuingCollectionStartDomains.State
abbrev RoundInput := ReferenceContinuingCollectionStartDomains.RoundInput
abbrev Payload {p : Parameters} (rate : RateInput p) :=
  ReferenceContinuingCollectionStartDomains.Payload rate
abbrev Ledger {p : Parameters} (rate : RateInput p) :=
  ReferenceContinuingCollectionStartDomains.Ledger rate
abbrev sourceRound {p : Parameters} (r : Fin p.T) :=
  ReferenceContinuingCollectionStartDomains.sourceRound r

variable {p : Parameters} {rate : RateInput p}

/-- Literal ready boundary fields after physical round `T`. This records the
same ledger, queue, cap, raw-history, and decoder-bank conditions as the
continuing ready domain, with the terminal cursor `T + 1`; it supplies no
physical input at that cursor. -/
def continuingCollectionReadyBoundaryDomain
    (state : State p rate) (payload : Payload rate) (l : Ledger rate)
    (saved : Option (Fin p.T × Bool)) : Prop :=
  state.coordinator = ReferenceActivePhysicalStep.CoordinatorConfiguration.collection
      payload l saved ∧
  l.phase = CoordinatorCollectionLedger.Phase.ready ∧
  1 ≤ l.sigma ∧ l.sigma ≤ p.T ∧ l.sigma < l.cutoff ∧
  l.sigma = payload.sigma.val + 1 ∧
  1 ≤ l.cutoff ∧ l.cutoff ≤ p.T ∧ l.cutoff ≤ l.freezeAt ∧
  l.freezeAt ≤ p.T + 1 ∧
  l.freezeAt = FollowerCutoffScan.gridBoundary p rate.eta.val payload.sigma ∧
  l.cursor = p.T + 1 ∧ l.cutoff < l.cursor ∧ l.cursor ≤ p.T + 1 ∧
  l.assignment.arm = payload.assignment.assigned ∧
  l.baseScore = (fun _ : Fin (p.m - 1) => (0 : ℕ)) ∧
  (∀ a : Fin p.K, payload.anchor a = 1) ∧ payload.n = rate.n ∧
  l.pending.Nonempty ∧
  (∀ a : Fin p.K,
    (l.currentRegisters a = none ↔ CoordinatorCollectionLedger.armPending l a) ∧
    (l.cutoffRegisters a = none ↔ CoordinatorCollectionLedger.armPending l a)) ∧
  (∀ a : Fin p.K,
    l.gammaLoc a = 0 ∧
      (CoordinatorCollectionLedger.armPending l a → l.increment a = 0)) ∧
  (∀ a c, l.cutoffRegisters a = some c →
    c.score + c.queue ≤ (l.cutoff - l.sigma) * D p ∧ c.lastService ≤ D p) ∧
  (∀ a c q, l.cutoffRegisters a = some c → l.currentRegisters a = some q →
    q.lastService ≤ D p ∧
    c.score + l.increment a + q.queue ≤ (l.cursor - l.sigma) * D p) ∧
  (∀ a c q, l.cutoffRegisters a = some c → l.currentRegisters a = some q →
    c.score + l.increment a ≤
      4 * rate.n * (min l.cursor l.freezeAt - l.sigma)) ∧
  (∀ a r amount, l.rawBuffer a r = some amount →
    0 < amount ∧ amount ≤ D p ∧ l.cutoff ≤ sourceRound r ∧
    sourceRound r < min l.cursor l.freezeAt ∧
    CoordinatorCollectionLedger.armPending l a) ∧
  (∀ r,
    l.enabledHistory r =
      if l.cutoff ≤ sourceRound r ∧ sourceRound r < l.cursor then
        some (decide (sourceRound r < l.freezeAt)) else none) ∧
  (∀ i : Fin (p.m - 1),
    (state.upDecoderBank i).pending.length < AffineBatchDecoder.quota p ∧
    (∀ batch, batch ∈ (state.upDecoderBank i).completed →
      batch.length = AffineBatchDecoder.quota p) ∧
    (i ∉ l.pending → (state.upDecoderBank i).pending = []))

private theorem armPendingCheck_eq_true_iff
    (l : Ledger rate) (a : Fin p.K) :
    CoordinatorCollectionLedger.armPendingCheck l a = true ↔
      CoordinatorCollectionLedger.armPending l a := by
  unfold CoordinatorCollectionLedger.armPendingCheck
  unfold CoordinatorCollectionLedger.anyFin
  rw [List.any_eq_true]
  simp [CoordinatorCollectionLedger.armPending]

private theorem armPendingCheck_finishRoundCandidate
    (l : Ledger rate) (a : Fin p.K) :
    CoordinatorCollectionLedger.armPendingCheck
        (CoordinatorCollectionLedger.finishRoundCandidate l) a =
      CoordinatorCollectionLedger.armPendingCheck l a := by
  rfl

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

private theorem finishCandidate_valid
    (l : Ledger rate)
    (hsigmaPos : 1 ≤ l.sigma) (hsigmaT : l.sigma ≤ p.T)
    (hcutPos : 1 ≤ l.cutoff) (hcutFreeze : l.cutoff ≤ l.freezeAt)
    (hcutT : l.cutoff ≤ p.T) (hfreeze : l.freezeAt ≤ p.T + 1)
    (hcutCursor : l.cutoff ≤ l.cursor) (hcursorT : l.cursor + 1 ≤ p.T + 1)
    (hcurrentPending : ∀ a,
      (l.currentRegisters a = none ↔ CoordinatorCollectionLedger.armPending l a))
    (hcutoffPending : ∀ a,
      (l.cutoffRegisters a = none ↔ CoordinatorCollectionLedger.armPending l a))
    (hpendingZero : ∀ a, CoordinatorCollectionLedger.armPending l a →
      l.increment a = 0 ∧ l.gammaLoc a = 0)
    (hcurrentDomain : ∀ a q, l.currentRegisters a = some q →
      q.queue ≤ p.T * D p ∧ q.lastService ≤ D p)
    (hcutoffDomain : ∀ a c, l.cutoffRegisters a = some c →
      c.score ≤ p.T * D p ∧ c.queue ≤ p.T * D p ∧ c.lastService ≤ D p)
    (hbaseDomain : ∀ i, l.baseScore i ≤ p.T * D p)
    (hincrementDomain : ∀ a, l.increment a + l.gammaLoc a ≤ p.T * D p)
    (hraw : ∀ a r amount, l.rawBuffer a r = some amount →
      0 < amount ∧ amount ≤ D p ∧ l.cutoff ≤ sourceRound r ∧
      sourceRound r < min (l.cursor + 1) l.freezeAt ∧
      CoordinatorCollectionLedger.armPending l a)
    (hhistory : ∀ r, l.enabledHistory r =
      if l.cutoff ≤ sourceRound r ∧ sourceRound r ≤ l.cursor then
        some (decide (sourceRound r < l.freezeAt)) else none) :
    CoordinatorCollectionLedger.validLedgerCheck
      (CoordinatorCollectionLedger.finishRoundCandidate l) = true := by
  classical
  let finished := CoordinatorCollectionLedger.finishRoundCandidate l
  have hcurrentCheck : CoordinatorCollectionLedger.allFin p.K
      (fun a : Fin p.K => match finished.currentRegisters a with
        | none => true
        | some q => decide (q.queue ≤ p.T * D p) && decide (q.lastService ≤ D p)) = true := by
    apply (allFin_eq_true_iff _).2
    intro a
    cases hq : l.currentRegisters a with
    | none => simp [finished, CoordinatorCollectionLedger.finishRoundCandidate, hq]
    | some q =>
      have hdomain := hcurrentDomain a q hq
      simp [finished, CoordinatorCollectionLedger.finishRoundCandidate, hq,
        hdomain.1, hdomain.2]
  have hcutoffCheck : CoordinatorCollectionLedger.allFin p.K
      (fun a : Fin p.K => match finished.cutoffRegisters a with
        | none => true
        | some c => decide (c.score ≤ p.T * D p) &&
          decide (c.queue ≤ p.T * D p) && decide (c.lastService ≤ D p)) = true := by
    apply (allFin_eq_true_iff _).2
    intro a
    cases hc : l.cutoffRegisters a with
    | none => simp [finished, CoordinatorCollectionLedger.finishRoundCandidate, hc]
    | some c =>
      have hdomain := hcutoffDomain a c hc
      simp [finished, CoordinatorCollectionLedger.finishRoundCandidate, hc,
        hdomain.1, hdomain.2.1, hdomain.2.2]
  have hbaseCheck : CoordinatorCollectionLedger.allFin (p.m - 1)
      (fun i : Fin (p.m - 1) => decide (finished.baseScore i ≤ p.T * D p)) = true := by
    apply (allFin_eq_true_iff _).2
    intro i
    exact decide_eq_true (by simpa [finished,
      CoordinatorCollectionLedger.finishRoundCandidate] using hbaseDomain i)
  have hincrementCheck : CoordinatorCollectionLedger.allFin p.K
      (fun a : Fin p.K => decide (finished.increment a ≤ p.T * D p)) = true := by
    apply (allFin_eq_true_iff _).2
    intro a
    exact decide_eq_true (by simpa [finished,
      CoordinatorCollectionLedger.finishRoundCandidate] using hincrementDomain a)
  have hgammaCheck : CoordinatorCollectionLedger.allFin p.K
      (fun a : Fin p.K => decide (finished.gammaLoc a ≤ D p)) = true := by
    apply (allFin_eq_true_iff _).2
    intro a
    simp [finished, CoordinatorCollectionLedger.finishRoundCandidate]
  have hregisterCheck : CoordinatorCollectionLedger.registerDomainsCheck finished = true := by
    change (CoordinatorCollectionLedger.allFin p.K (fun a : Fin p.K =>
      match finished.currentRegisters a with
      | none => true
      | some q => decide (q.queue ≤ p.T * D p) && decide (q.lastService ≤ D p)) &&
      CoordinatorCollectionLedger.allFin p.K (fun a : Fin p.K =>
        match finished.cutoffRegisters a with
        | none => true
        | some c => decide (c.score ≤ p.T * D p) &&
          decide (c.queue ≤ p.T * D p) && decide (c.lastService ≤ D p)) &&
      CoordinatorCollectionLedger.allFin (p.m - 1) (fun i : Fin (p.m - 1) =>
        decide (finished.baseScore i ≤ p.T * D p)) &&
      CoordinatorCollectionLedger.allFin p.K (fun a : Fin p.K =>
        decide (finished.increment a ≤ p.T * D p)) &&
      CoordinatorCollectionLedger.allFin p.K (fun a : Fin p.K =>
        decide (finished.gammaLoc a ≤ D p)) = true)
    simp [hcurrentCheck, hcutoffCheck, hbaseCheck, hincrementCheck, hgammaCheck]
  have hcurrentPendingCheck : CoordinatorCollectionLedger.allFin p.K
      (fun a : Fin p.K =>
        (finished.currentRegisters a).isNone ==
          CoordinatorCollectionLedger.armPendingCheck finished a) = true := by
    apply (allFin_eq_true_iff _).2
    intro a
    by_cases hp : CoordinatorCollectionLedger.armPending l a
    · have hn := (hcurrentPending a).2 hp
      have hpc := (armPendingCheck_eq_true_iff l a).2 hp
      have hpc' : CoordinatorCollectionLedger.armPendingCheck finished a = true := by
        simpa [finished] using
          (armPendingCheck_finishRoundCandidate (l := l) a).trans hpc
      simp [finished, CoordinatorCollectionLedger.finishRoundCandidate, hn]
      exact hpc'
    · have hpc : CoordinatorCollectionLedger.armPendingCheck l a = false := by
        cases h : CoordinatorCollectionLedger.armPendingCheck l a with
        | false => rfl
        | true => exact False.elim (hp ((armPendingCheck_eq_true_iff l a).1 h))
      have hsome : l.currentRegisters a ≠ none := by
        intro hnone
        exact hp ((hcurrentPending a).1 hnone)
      cases hreg : l.currentRegisters a with
      | none => exact False.elim (hsome hreg)
      | some q =>
        have hpc' : CoordinatorCollectionLedger.armPendingCheck finished a = false := by
          simpa [finished] using
            (armPendingCheck_finishRoundCandidate (l := l) a).trans hpc
        simp [finished, CoordinatorCollectionLedger.finishRoundCandidate, hreg]
        exact hpc'
  have hcutoffPendingCheck : CoordinatorCollectionLedger.allFin p.K
      (fun a : Fin p.K =>
        (finished.cutoffRegisters a).isNone ==
          CoordinatorCollectionLedger.armPendingCheck finished a) = true := by
    apply (allFin_eq_true_iff _).2
    intro a
    by_cases hp : CoordinatorCollectionLedger.armPending l a
    · have hn := (hcutoffPending a).2 hp
      have hpc := (armPendingCheck_eq_true_iff l a).2 hp
      have hpc' : CoordinatorCollectionLedger.armPendingCheck finished a = true := by
        simpa [finished] using
          (armPendingCheck_finishRoundCandidate (l := l) a).trans hpc
      simp [finished, CoordinatorCollectionLedger.finishRoundCandidate, hn]
      exact hpc'
    · have hpc : CoordinatorCollectionLedger.armPendingCheck l a = false := by
        cases h : CoordinatorCollectionLedger.armPendingCheck l a with
        | false => rfl
        | true => exact False.elim (hp ((armPendingCheck_eq_true_iff l a).1 h))
      have hsome : l.cutoffRegisters a ≠ none := by
        intro hnone
        exact hp ((hcutoffPending a).1 hnone)
      cases hreg : l.cutoffRegisters a with
      | none => exact False.elim (hsome hreg)
      | some c =>
        have hpc' : CoordinatorCollectionLedger.armPendingCheck finished a = false := by
          simpa [finished] using
            (armPendingCheck_finishRoundCandidate (l := l) a).trans hpc
        simp [finished, CoordinatorCollectionLedger.finishRoundCandidate, hreg]
        exact hpc'
  have hzeroPendingIncrement : CoordinatorCollectionLedger.allFin p.K
      (fun a : Fin p.K => (!CoordinatorCollectionLedger.armPendingCheck finished a) ||
        decide (finished.increment a = 0)) = true := by
    apply (allFin_eq_true_iff _).2
    intro a
    by_cases hp : CoordinatorCollectionLedger.armPending l a
    · have hpc := (armPendingCheck_eq_true_iff l a).2 hp
      have hpc' : CoordinatorCollectionLedger.armPendingCheck finished a = true := by
        simpa [finished] using
          (armPendingCheck_finishRoundCandidate (l := l) a).trans hpc
      have hz := hpendingZero a hp
      simp [finished, CoordinatorCollectionLedger.finishRoundCandidate,
        hz.1, hz.2]
    · have hpc : CoordinatorCollectionLedger.armPendingCheck l a = false := by
        cases h : CoordinatorCollectionLedger.armPendingCheck l a with
        | false => rfl
        | true => exact False.elim (hp ((armPendingCheck_eq_true_iff l a).1 h))
      have hpc' : CoordinatorCollectionLedger.armPendingCheck finished a = false := by
        simpa [finished] using
          (armPendingCheck_finishRoundCandidate (l := l) a).trans hpc
      simp [finished, CoordinatorCollectionLedger.finishRoundCandidate]
      exact Or.inl hpc'
  have hzeroGamma : CoordinatorCollectionLedger.allFin p.K
      (fun a : Fin p.K => decide (finished.gammaLoc a = 0)) = true := by
    apply (allFin_eq_true_iff _).2
    intro a
    simp [finished, CoordinatorCollectionLedger.finishRoundCandidate]
  have hpendingGamma : CoordinatorCollectionLedger.allFin p.K
      (fun a : Fin p.K => (!CoordinatorCollectionLedger.armPendingCheck finished a) ||
        decide (finished.gammaLoc a = 0)) = true := by
    apply (allFin_eq_true_iff _).2
    intro a
    simp [finished, CoordinatorCollectionLedger.finishRoundCandidate]
  have hrawCheck : CoordinatorCollectionLedger.rawEntryDomainsCheck finished = true := by
    unfold CoordinatorCollectionLedger.rawEntryDomainsCheck
    apply (allFin_eq_true_iff _).2
    intro a
    apply (allFin_eq_true_iff _).2
    intro r
    cases hcell : l.rawBuffer a r with
    | none => simp [finished, CoordinatorCollectionLedger.finishRoundCandidate, hcell]
    | some amount =>
      rcases hraw a r amount hcell with ⟨hpos, hD, hcut, hmin, hpending⟩
      have hcursor : sourceRound r < l.cursor + 1 :=
        lt_of_lt_of_le hmin (Nat.min_le_left _ _)
      have hfreezeRound : sourceRound r < l.freezeAt :=
        lt_of_lt_of_le hmin (Nat.min_le_right _ _)
      have hpc := (armPendingCheck_eq_true_iff l a).2 hpending
      have hpc' : CoordinatorCollectionLedger.armPendingCheck finished a = true := by
        simpa [finished] using
          (armPendingCheck_finishRoundCandidate (l := l) a).trans hpc
      simp [finished, CoordinatorCollectionLedger.finishRoundCandidate, hcell,
        hpos, hD]
      refine ⟨⟨⟨hcut, hfreezeRound⟩, ?_⟩, ?_⟩
      · have hcursor' : r.val + 1 < l.cursor + 1 := by
          simpa [sourceRound,
            ReferenceContinuingCollectionStartDomains.sourceRound,
            CoordinatorCollectionLedger.sourceRound] using hcursor
        have hroundLe : r.val + 1 ≤ l.cursor := by omega
        simpa [sourceRound,
          ReferenceContinuingCollectionStartDomains.sourceRound,
          CoordinatorCollectionLedger.sourceRound] using hroundLe
      · exact hpc'
  have hreadyHistory : CoordinatorCollectionLedger.readyHistoryCheck finished = true := by
    unfold CoordinatorCollectionLedger.readyHistoryCheck
    apply (allFin_eq_true_iff _).2
    intro r
    by_cases hbefore : sourceRound r < l.cutoff
    · change (decide (sourceRound r < l.cutoff) ||
        ((finished.enabledHistory r).isSome ==
          decide (sourceRound r < finished.cursor))) = true
      simp [hbefore]
    · have hafter : l.cutoff ≤ sourceRound r := by omega
      have hh := hhistory r
      have hh' : l.enabledHistory r =
          if sourceRound r ≤ l.cursor then
            some (decide (sourceRound r < l.freezeAt)) else none := by
        rw [hh]
        simp [hafter]
      have hcursor : (r.val < l.cursor) ↔ sourceRound r ≤ l.cursor := by
        simp [sourceRound]
      have hsome : (l.enabledHistory r).isSome = decide (sourceRound r ≤ l.cursor) := by
        rw [hh']
        by_cases hle : sourceRound r ≤ l.cursor <;> simp [hle]
      change (decide (sourceRound r < l.cutoff) ||
        ((finished.enabledHistory r).isSome ==
          decide (sourceRound r < finished.cursor))) = true
      simp [hbefore, finished, CoordinatorCollectionLedger.finishRoundCandidate,
        hsome]
  have hcutoffCursorSucc : l.cutoff ≤ l.cursor + 1 :=
    hcutCursor.trans (Nat.le_succ _)
  change CoordinatorCollectionLedger.validLedgerCheck finished = true
  simp_all [CoordinatorCollectionLedger.validLedgerCheck, finished,
    CoordinatorCollectionLedger.finishRoundCandidate]

/-- Continue one actual first-collection round under the literal S ready
domain. The only branch condition is on the ordinary filtered parse produced
after S has produced the actual recorder and started ledger. A mismatch, no
offer, no unique decoder word, parser failure, and local acceptance rejection
therefore all follow the existing rejected receiver path. -/
theorem continuing_collection_rejected_finish_domains
    (x : RoundInput p rate) (payload : Payload rate) (l : Ledger rate)
    (saved : Option (Fin p.T × Bool))
    (h : ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain
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
    ∃ (o : CoordinatorRecordingOperation.Output p) (l1 : Ledger rate),
      CoordinatorRecorderComplementBridge.run recordingInput = some o ∧
      let raw := CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder o
      CoordinatorCollectionLedger.startRound l (sourceRound x.time)
        (ReferenceActivePhysicalStep.collectionEnabled l x.time) raw = .success l1 ∧
      l1 = CoordinatorCollectionLedger.startRoundCandidate l x.time
        (ReferenceActivePhysicalStep.collectionEnabled l x.time) raw ∧
      CoordinatorCollectionLedger.validLedgerCheck l1 = true ∧
      l1.phase = .started ∧ l1.cursor = sourceRound x.time ∧
      l1.sigma = l.sigma ∧ l1.cutoff = l.cutoff ∧ l1.freezeAt = l.freezeAt ∧
      l1.pending = l.pending ∧ l1.assignment = l.assignment ∧
      l1.baseScore = l.baseScore ∧ l1.cutoffRegisters = l.cutoffRegisters ∧
      l1.increment = l.increment ∧
      (∀ a, (l1.currentRegisters a = none ↔
          CoordinatorCollectionLedger.armPending l1 a) ∧
        (l1.cutoffRegisters a = none ↔ CoordinatorCollectionLedger.armPending l1 a) ∧
        (l.currentRegisters a = none →
          l1.currentRegisters a = none ∧ l1.gammaLoc a = 0)) ∧
      (∀ a c q, l.cutoffRegisters a = some c → l1.currentRegisters a = some q →
        c.score + l.increment a + l1.gammaLoc a + q.queue ≤
          (sourceRound x.time + 1 - l.sigma) * D p ∧
        c.score + l.increment a + l1.gammaLoc a ≤
          4 * rate.n * (min (sourceRound x.time + 1) l.freezeAt - l.sigma) ∧
        q.queue ≤ p.T * D p ∧ q.lastService ≤ D p) ∧
      (∀ a q, l1.currentRegisters a = some q →
        q.queue ≤ p.T * D p ∧ q.lastService ≤ D p) ∧
      (∀ a c, l1.cutoffRegisters a = some c →
        c.score ≤ p.T * D p ∧ c.queue ≤ p.T * D p ∧ c.lastService ≤ D p) ∧
      (∀ a, CoordinatorCollectionLedger.armPending l1 a →
        l1.increment a = 0 ∧ l1.gammaLoc a = 0) ∧
      (∀ a, l1.gammaLoc a ≤ 4 * rate.n ∧ l1.gammaLoc a ≤ D p ∧
        l1.increment a + l1.gammaLoc a ≤ p.T * D p) ∧
      (∀ a r amount, l1.rawBuffer a r = some amount →
        0 < amount ∧ amount ≤ D p ∧ l.cutoff ≤ sourceRound r ∧
        sourceRound r < min (sourceRound x.time + 1) l.freezeAt ∧
        CoordinatorCollectionLedger.armPending l1 a) ∧
      (∀ r, l1.enabledHistory r =
        if l.cutoff ≤ sourceRound r ∧ sourceRound r ≤ sourceRound x.time then
          some (decide (sourceRound r < l.freezeAt)) else none) ∧
      let receptionInput := ReferenceUpReception.receptionInputAtRow rate x.row
        (ReferenceActivePhysicalStep.upInputs prepared l1) x.time
      let expected := ReferenceActivePhysicalStep.upExpected prepared
      let decoderRaw := (CoordinatorUpReception.decoderTransition receptionInput).2
      let filteredParsed := CoordinatorUpReception.parseDecoderOutput
        (ReferenceUpReception.filterRawByExpected decoderRaw expected)
      (filteredParsed = none ∨
        ∃ M, filteredParsed = some M ∧
          CoordinatorCollectionLedger.acceptUpCheck l1
            (ReferenceActivePhysicalStep.upSenderIndex x) M = false) →
      ∃ (l2 : Ledger rate) (bank : CoordinatorUpReception.UpDecoderBank p),
        (ReferenceActivePhysicalStep.receiveUp prepared l1).result =
          .rejected (l2, bank) ∧
        l2 = {l1 with phase := CoordinatorCollectionLedger.Phase.decoded} ∧
        CoordinatorUpReception.receptionInputDomain receptionInput ∧
        CoordinatorUpReception.receptionInputCheck receptionInput = true ∧
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
              ReferenceUpReception.wrongUniqueAndLocalAcceptanceAtRow rate x.row
                (ReferenceActivePhysicalStep.upInputs prepared l1) x.time
                (prepared.followers.followers (ReferenceActivePhysicalStep.upSenderIndex x))
                (prepared.follower_alignment _).1
                (prepared.follower_alignment _).2.1
                (prepared.follower_alignment _).2.2.1 rfl } ∧
        ∃ finished : Ledger rate,
        CoordinatorCollectionLedger.finishRound l2 = .success finished ∧
        finished = CoordinatorCollectionLedger.finishRoundCandidate l2 ∧
        finished.increment = (fun a => l.increment a + l1.gammaLoc a) ∧
        finished.gammaLoc = (fun _ => 0) ∧
        finished.cursor = sourceRound x.time + 1 ∧
        finished.phase = CoordinatorCollectionLedger.Phase.ready ∧
        finished.pending = l.pending ∧
        finished.assignment = l.assignment ∧
        finished.baseScore = l.baseScore ∧
        finished.cutoffRegisters = l.cutoffRegisters ∧
        finished.currentRegisters = l1.currentRegisters ∧
        finished.rawBuffer = l1.rawBuffer ∧
        finished.enabledHistory = l1.enabledHistory ∧
        (∀ a c q, l.cutoffRegisters a = some c → l1.currentRegisters a = some q →
          c.score + finished.increment a + q.queue ≤
            (sourceRound x.time + 1 - l.sigma) * D p ∧
          c.score + finished.increment a ≤
            4 * rate.n * (min (sourceRound x.time + 1) l.freezeAt - l.sigma)) ∧
        (∀ a r amount, finished.rawBuffer a r = some amount →
          0 < amount ∧ amount ≤ D p ∧ l.cutoff ≤ sourceRound r ∧
          sourceRound r < min finished.cursor finished.freezeAt ∧
          CoordinatorCollectionLedger.armPending finished a) ∧
        (∀ r, finished.enabledHistory r =
          if l.cutoff ≤ sourceRound r ∧ sourceRound r < finished.cursor then
            some (decide (sourceRound r < finished.freezeAt)) else none) ∧
        CoordinatorCollectionLedger.validLedgerCheck finished = true ∧
        ∃ clockFinished : CoordinatorPhaseClock.FinishRoundResult p,
          CoordinatorPhaseClock.finishRound p rate.eta.val x.time
            snap.clockStarted.clock finished.pending x.row = .ok clockFinished ∧
          clockFinished.clock = snap.clockStarted.clock ∧
          clockFinished.pending = finished.pending ∧
          clockFinished.ledgerCommand =
            some (.accumulateLocalServiceAt x.time) ∧
          let actualLastProposal := clockFinished.clock.lastProposal
          actualLastProposal = saved ∧
          ReferenceActivePhysicalStep.collectionFinish (x := x) payload
            snap.clockStarted o (ReferenceActivePhysicalStep.receiveUp prepared l1) =
              { configuration := .collection payload finished actualLastProposal
                upDecoderBank := bank
                failure := none
                recording := some o
                up := (ReferenceActivePhysicalStep.receiveUp prepared l1).diagnostic } ∧
          prepared.observeCoordinator =
              ReferenceActivePhysicalStep.collectionFinish (x := x) payload
                snap.clockStarted o (ReferenceActivePhysicalStep.receiveUp prepared l1) ∧
          (ReferenceActivePhysicalStep.step x).coordinator =
              prepared.observeCoordinator ∧
          (ReferenceActivePhysicalStep.step x).next.coordinator =
              .collection payload finished actualLastProposal ∧
          (ReferenceActivePhysicalStep.step x).next.upDecoderBank = bank ∧
          (ReferenceActivePhysicalStep.step x).next.activations = x.state.activations ∧
          (∀ i, (ReferenceActivePhysicalStep.step x).followers i =
            (prepared.observeFollower i)) ∧
          (ReferenceActivePhysicalStep.step x).ownEntries =
            prepared.feedback.ownEntries ∧
          (sourceRound x.time < p.T →
            ∃ xNext : RoundInput p rate,
              xNext.state = (ReferenceActivePhysicalStep.step x).next ∧
              xNext.rows = x.rows ∧ xNext.selected = x.selected ∧
              xNext.rewards = x.rewards ∧
              xNext.time.val = x.time.val + 1 ∧
              ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain
                xNext payload finished actualLastProposal) ∧
          (sourceRound x.time = p.T →
            continuingCollectionReadyBoundaryDomain
              (ReferenceActivePhysicalStep.step x).next payload finished
              actualLastProposal)
    := by
  classical
  have hReady := h
  rcases h with ⟨hstate, hphaseReady, hσpos, hσT, hσcut, hσpayload,
    hcutPos, hcutT, hcutFreeze, hfreezeT, hgrid, hcursor, hcutCursor,
    hcursorT, hassignment, hbaseZero, hanchor, hn, hpending, hregisters,
    hgammaZero, hcutDomain, hpaired, hcap, hrawReady, hhistoryReady, hbank⟩
  obtain ⟨cutoff, hcutoff, core, snap, hb, hs, hcoord, harm, hlocal,
    hrecordInputs, o, l1, hrecord, hstart, hl1Candidate, hvalid, hphase,
    hcursor1, hσ1, hcut1, hfreeze1, hpending1, hassignment1, hbase1,
    hcutRegisters1, hincrement1, htransition, hconservation, hfrozen,
    hrawNone, hregisters1, hmass, hcurrent1, hcutDomain1, hzero1,
    hgamma1, hcutMass1, hraw1, hhistory1, hrawBuffer1, hrawFrame1,
    hfresh, hfuture, hobserve, hrecording, hdiagnostic⟩ :=
      ReferenceContinuingCollectionStartDomains.continuing_collection_start_domains
        x payload l saved hReady
  let clock := ReferenceActivePhysicalStep.collectionClock payload l saved cutoff
  let input := ReferenceActivePhysicalStep.collectionInput x payload l clock cutoff
  let prepared := ReferenceActivePhysicalStep.prepare x
  let weights := CoordinatorCollectionInteractive.PreObservationInputs.weights input
    snap.inputsValid.ledger_valid snap.inputsValid.assignment_eq
  let recordingInput := ReferenceActivePhysicalStep.collectionRecordingInput prepared
    payload snap.clockStarted weights
  refine ⟨cutoff, hcutoff, core, snap, hb, hs, ?_⟩
  change
    prepared.coordinator = .collection payload l clock cutoff (.continuing core snap hb hs) ∧
      prepared.coordinator.arm = snap.arm ∧
      CoordinatorRecorderComplementBridge.LocalInputsValid recordingInput ∧
      CoordinatorRecordingOperation.InputsValid
        (CoordinatorRecorderComplementBridge.recorderInput recordingInput) ∧ _
  refine ⟨hcoord, harm, hlocal, hrecordInputs, o, l1, hrecord, ?_⟩
  let raw := CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder o
  refine ⟨hstart, hl1Candidate, hvalid, hphase, hcursor1, hσ1, hcut1,
    hfreeze1, hpending1, hassignment1, hbase1, hcutRegisters1, hincrement1,
    hregisters1, hmass, hcurrent1, hcutDomain1, hzero1, hgamma1, hraw1,
    hhistory1, ?_⟩
  let receptionInput := ReferenceUpReception.receptionInputAtRow rate x.row
    (ReferenceActivePhysicalStep.upInputs prepared l1) x.time
  let expected := ReferenceActivePhysicalStep.upExpected prepared
  let decoderRaw := (CoordinatorUpReception.decoderTransition receptionInput).2
  let filteredParsed := CoordinatorUpReception.parseDecoderOutput (p := p)
    (eta := rate.eta.val)
    (ReferenceUpReception.filterRawByExpected decoderRaw expected)
  change (filteredParsed = none ∨
    ∃ M, filteredParsed = some M ∧
      CoordinatorCollectionLedger.acceptUpCheck l1
        (ReferenceActivePhysicalStep.upSenderIndex x) M = false) → _
  intro hbranch
  let l2 : Ledger rate :=
    { l1 with phase := CoordinatorCollectionLedger.Phase.decoded }
  let bank : CoordinatorUpReception.UpDecoderBank p :=
    CoordinatorUpReception.decoderBankAfter receptionInput
  have hbankCheck : CoordinatorUpReception.decoderBankCheck p
      x.state.upDecoderBank = true := by
    apply (CoordinatorUpReception.decoderBankCheck_eq_true_iff p _).2
    intro i
    exact ⟨(hbank i).1, (hbank i).2.1⟩
  have hdomain : CoordinatorUpReception.receptionInputDomain receptionInput := by
    refine ⟨hvalid, ?_, hphase, ?_, ?_, ?_, ?_, hbankCheck⟩
    · change 1 ≤ l1.sigma
      rw [hσ1]
      exact hσpos
    · change 1 ≤ l1.cutoff
      rw [hcut1]
      exact hcutPos
    · change l1.cutoff ≤ l1.cursor
      rw [hcut1, hcursor1]
      have hcutTime : l.cutoff < ↑x.time + 1 := by
        rw [← hcursor]
        exact hcutCursor
      change l.cutoff ≤ ↑x.time + 1
      exact Nat.le_of_lt hcutTime
    · change l1.cursor ≤ p.T
      rw [hcursor1]
      change x.time.val + 1 ≤ p.T
      omega
    · change l1.cursor = CoordinatorCollectionLedger.sourceRound receptionInput.time
      rw [hcursor1]
      rfl
  have hinputCheck : CoordinatorUpReception.receptionInputCheck receptionInput = true :=
    (CoordinatorUpReception.receptionInputCheck_eq_true_iff receptionInput).2 hdomain
  let sender := prepared.followers.followers (ReferenceActivePhysicalStep.upSenderIndex x)
  have hrow : sender.row = x.row :=
    (prepared.follower_alignment _).1
  have hplayer : sender.follower = receptionInput.selectedFollower :=
    (prepared.follower_alignment _).2.1
  have hsenderIndex : ReferenceActivePhysicalStep.upSenderIndex x =
      receptionInput.selectedFollower := rfl
  have htime : sender.time = receptionInput.time :=
    (prepared.follower_alignment _).2.2.1
  have hexpected :
      ReferenceUpReception.currentOfferWord rate x.row receptionInput.selectedFollower
        receptionInput.time sender hrow hplayer htime = expected := by
    rfl
  have hfilteredDecode :=
    ReferenceUpReception.receiveUpFilteredAtRow_eq_filtered_decode rate x.row
      (ReferenceActivePhysicalStep.upInputs prepared l1) x.time sender hrow hplayer htime
      rfl hinputCheck
  have hdecoded :
      CoordinatorCollectionLedger.decodeUp l1 (ReferenceActivePhysicalStep.upSenderIndex x)
        filteredParsed =
          .rejected { l1 with phase := CoordinatorCollectionLedger.Phase.decoded } := by
    rcases hbranch with hnone | ⟨M, hparsed, haccept⟩
    · rw [hnone]
      have hdecodeNone :=
        CoordinatorUpReception.decodeUp_none_rejected receptionInput hdomain
      rw [← hsenderIndex] at hdecodeNone
      change CoordinatorCollectionLedger.decodeUp l1
          (ReferenceActivePhysicalStep.upSenderIndex x) none =
        .rejected { l1 with phase := CoordinatorCollectionLedger.Phase.decoded } at hdecodeNone
      exact hdecodeNone
    · rw [hparsed]
      have hnot : ¬ CoordinatorCollectionLedger.acceptUpCheck l1
          (ReferenceActivePhysicalStep.upSenderIndex x) M := by
        intro htrue
        rw [haccept] at htrue
        cases htrue
      have hdecodeRejected :=
        CoordinatorUpReception.decodeUp_unaccepted_rejected receptionInput hdomain M hnot
      rw [← hsenderIndex] at hdecodeRejected
      change CoordinatorCollectionLedger.decodeUp l1
          (ReferenceActivePhysicalStep.upSenderIndex x) (some M) =
        .rejected { l1 with phase := CoordinatorCollectionLedger.Phase.decoded } at hdecodeRejected
      exact hdecodeRejected
  have hreceiveResult :
      (ReferenceActivePhysicalStep.receiveUp prepared l1).result = .rejected (l2, bank) := by
    change ReferenceUpReception.receiveUpFilteredAtRow rate x.row
      (ReferenceActivePhysicalStep.upInputs prepared l1) x.time sender hrow hplayer htime rfl =
        .rejected (l2, bank)
    have hfilteredDecode' := hfilteredDecode
    rw [hexpected] at hfilteredDecode'
    rw [hfilteredDecode']
    change CoordinatorUpReception.packDecodeResult
      (CoordinatorCollectionLedger.decodeUp l1
        (ReferenceActivePhysicalStep.upSenderIndex x) filteredParsed)
      (CoordinatorUpReception.decoderBankAfter receptionInput) =
        .rejected (l2, bank)
    rw [hdecoded]
    rfl
  have hdiagnosticResult :
      (ReferenceActivePhysicalStep.receiveUp prepared l1).diagnostic =
        some {
          input := receptionInput
          expected := expected
          decoderAfter := (CoordinatorUpReception.decoderTransition receptionInput).1
          raw := decoderRaw
          parsed := ReferenceUpReception.rawParsedOutput rate receptionInput
          locallyAccepted := ReferenceUpReception.rawParsedLocalAcceptance rate receptionInput
          rawMatches := decide (decoderRaw = expected)
          wrongUniqueAccepted :=
            ReferenceUpReception.wrongUniqueAndLocalAcceptanceAtRow rate x.row
              (ReferenceActivePhysicalStep.upInputs prepared l1) x.time
              (prepared.followers.followers
                (ReferenceActivePhysicalStep.upSenderIndex x))
              (prepared.follower_alignment _).1
              (prepared.follower_alignment _).2.1
              (prepared.follower_alignment _).2.2.1 rfl } := by
    unfold ReferenceActivePhysicalStep.receiveUp
    dsimp only
    rw [hinputCheck]
    rfl
  have hdecodedValid : CoordinatorCollectionLedger.validLedgerCheck l2 = true := by
    simpa [l2, CoordinatorUpReception.decodePhaseCandidate] using
      CoordinatorUpReception.validLedgerCheck_after_decode l1 hvalid hphase
  have hl2Phase : l2.phase = CoordinatorCollectionLedger.Phase.decoded := rfl
  have hcurrentPending2 : ∀ a,
      (l2.currentRegisters a = none ↔ CoordinatorCollectionLedger.armPending l2 a) := by
    intro a
    change l1.currentRegisters a = none ↔ CoordinatorCollectionLedger.armPending l1 a
    exact (hregisters1 a).1
  have hcutoffPending2 : ∀ a,
      (l2.cutoffRegisters a = none ↔ CoordinatorCollectionLedger.armPending l2 a) := by
    intro a
    change l1.cutoffRegisters a = none ↔ CoordinatorCollectionLedger.armPending l1 a
    exact (hregisters1 a).2.1
  have hpendingZero2 : ∀ a, CoordinatorCollectionLedger.armPending l2 a →
      l2.increment a = 0 ∧ l2.gammaLoc a = 0 := by
    intro a hp
    change CoordinatorCollectionLedger.armPending l1 a at hp
    have hz := hzero1 a hp
    simpa [l2] using hz
  have hcurrentDomain2 : ∀ a q, l2.currentRegisters a = some q →
      q.queue ≤ p.T * D p ∧ q.lastService ≤ D p := by
    intro a q hq
    have hq1 : l1.currentRegisters a = some q := by simpa [l2] using hq
    exact hcurrent1 a q hq1
  have hcutoffDomain2 : ∀ a c, l2.cutoffRegisters a = some c →
      c.score ≤ p.T * D p ∧ c.queue ≤ p.T * D p ∧ c.lastService ≤ D p := by
    intro a c hc
    have hc1 : l1.cutoffRegisters a = some c := by simpa [l2] using hc
    exact hcutDomain1 a c hc1
  have hbaseDomain2 : ∀ i, l2.baseScore i ≤ p.T * D p := by
    intro i
    rw [hbase1, hbaseZero]
    exact Nat.zero_le _
  have hincrementDomain2 : ∀ a, l2.increment a + l2.gammaLoc a ≤ p.T * D p := by
    intro a
    by_cases hp : CoordinatorCollectionLedger.armPending l2 a
    · have hz := hpendingZero2 a hp
      simp [hz.1, hz.2]
    · have hcurrentSome : l2.currentRegisters a ≠ none := by
        intro hn
        exact hp ((hcurrentPending2 a).mp hn)
      have hcutoffSome : l2.cutoffRegisters a ≠ none := by
        intro hn
        exact hp ((hcutoffPending2 a).mp hn)
      obtain ⟨q, hq⟩ : ∃ q, l1.currentRegisters a = some q := by
        cases hq : l2.currentRegisters a with
        | none => exact False.elim (hcurrentSome hq)
        | some q => exact ⟨q, rfl⟩
      obtain ⟨c, hc⟩ : ∃ c, l.cutoffRegisters a = some c := by
        cases hc : l2.cutoffRegisters a with
        | none => exact False.elim (hcutoffSome hc)
        | some c => exact ⟨c, by simpa [l2, hcutRegisters1] using hc⟩
      have hmassHere := hmass a c q hc (by simpa [l2] using hq)
      have htimeBound : sourceRound x.time + 1 - l.sigma ≤ p.T := by
        change x.time.val + 1 + 1 - l.sigma ≤ p.T
        have htimeLe : x.time.val + 1 ≤ p.T := Nat.succ_le_of_lt x.time.isLt
        omega
      have hscaled := Nat.mul_le_mul_right (D p) htimeBound
      have hincrementEq : l2.increment a = l.increment a := by
        simp [l2, hincrement1]
      have hgammaEq : l2.gammaLoc a = l1.gammaLoc a := by
        rfl
      rw [hincrementEq, hgammaEq]
      have hjoint := hmassHere.1
      have htotal : c.score + l.increment a + l1.gammaLoc a + q.queue ≤ p.T * D p :=
        Nat.le_trans hjoint hscaled
      have hdrop : l.increment a + l1.gammaLoc a ≤
          c.score + l.increment a + l1.gammaLoc a + q.queue := by omega
      exact hdrop.trans htotal
  have hraw2 : ∀ a r amount, l2.rawBuffer a r = some amount →
      0 < amount ∧ amount ≤ D p ∧ l2.cutoff ≤ sourceRound r ∧
      sourceRound r < min (l2.cursor + 1) l2.freezeAt ∧
      CoordinatorCollectionLedger.armPending l2 a := by
    intro a r amount hcell
    have hcell1 : l1.rawBuffer a r = some amount := by simpa [l2] using hcell
    have hr := hraw1 a r amount hcell1
    simpa [l2, hcursor1, hcut1, hfreeze1, sourceRound,
      ReferenceContinuingCollectionStartDomains.sourceRound,
      CoordinatorCollectionLedger.sourceRound,
      CoordinatorCollectionLedger.armPending] using hr
  have hhistory2 : ∀ r, l2.enabledHistory r =
      if l2.cutoff ≤ sourceRound r ∧ sourceRound r ≤ l2.cursor then
        some (decide (sourceRound r < l2.freezeAt)) else none := by
    intro r
    have hr := hhistory1 r
    simpa [l2, hcut1, hcursor1, hfreeze1, sourceRound,
      ReferenceContinuingCollectionStartDomains.sourceRound,
      CoordinatorCollectionLedger.sourceRound] using hr
  have hcutoffAtTime : l.cutoff ≤ sourceRound x.time := by
    have hlt : l.cutoff < ↑x.time + 1 := by
      rw [← hcursor]
      exact hcutCursor
    change l.cutoff ≤ ↑x.time + 1
    exact Nat.le_of_lt hlt
  have hfinishCandidateValid := finishCandidate_valid l2
    (by simpa [l2, hσ1] using hσpos)
    (by simpa [l2, hσ1] using hσT)
    (by simpa [l2, hcut1] using hcutPos)
    (by simpa [l2, hcut1, hfreeze1] using hcutFreeze)
    (by simpa [l2, hcut1] using hcutT)
    (by simpa [l2, hfreeze1] using hfreezeT)
    (by simpa [l2, hcut1, hcursor1] using hcutoffAtTime)
    (by
      simp [l2, hcursor1,
        ReferenceContinuingCollectionStartDomains.sourceRound])
    hcurrentPending2 hcutoffPending2 hpendingZero2
    hcurrentDomain2 hcutoffDomain2 hbaseDomain2 hincrementDomain2 hraw2 hhistory2
  let finished := CoordinatorCollectionLedger.finishRoundCandidate l2
  have hfinishInput : CoordinatorCollectionLedger.validLedgerCheck l2 = true ∧
      l2.phase = CoordinatorCollectionLedger.Phase.decoded ∧ l2.cursor ≤ p.T := by
    refine ⟨hdecodedValid, hl2Phase, ?_⟩
    change l1.cursor ≤ p.T
    rw [hcursor1]
    change x.time.val + 1 ≤ p.T
    exact Nat.succ_le_of_lt x.time.isLt
  have hfinish : CoordinatorCollectionLedger.finishRound l2 = .success finished := by
    unfold CoordinatorCollectionLedger.finishRound
    simp [hfinishInput, hfinishCandidateValid, finished]
  have hclockValid : CoordinatorPhaseClock.clockRegistersValid p rate.eta.val
      snap.clockStarted.clock := by
    rw [snap.clockStarted_frame.1]
    change CoordinatorPhaseClock.clockRegistersValid p rate.eta.val input.clock
    simpa [input, ReferenceActivePhysicalStep.collectionInput] using
      core.clock_registers_valid
  have hclockFrame := snap.clockStarted_frame.1
  have hclockSigma : snap.clockStarted.clock.sigma = some payload.sigma := by
    rw [hclockFrame]
    rfl
  have hclockCutoff : snap.clockStarted.clock.u = some cutoff := by
    rw [hclockFrame]
    rfl
  have hcutoffTime : cutoff.val ≤ x.time.val := by
    have hlt := hcutCursor
    rw [hcursor, ← hcutoff] at hlt
    omega
  have hclockFinish :=
    CoordinatorPhaseClock.finishRound_collection p rate.eta.val x.time payload.sigma cutoff
      snap.clockStarted.clock l2.pending x.row hclockValid hclockSigma hclockCutoff
      hcutoffTime
  let clockFinished : CoordinatorPhaseClock.FinishRoundResult p := {
    clock := snap.clockStarted.clock
    pending := l2.pending
    ledgerCommand := some (.accumulateLocalServiceAt x.time) }
  have hclockFinished : CoordinatorPhaseClock.finishRound p rate.eta.val x.time
      snap.clockStarted.clock finished.pending x.row = .ok clockFinished := by
    simpa [clockFinished, finished, CoordinatorCollectionLedger.finishRoundCandidate] using
      hclockFinish
  let actualLastProposal := clockFinished.clock.lastProposal
  have hlastProposal : actualLastProposal = saved := by
    dsimp [actualLastProposal, clockFinished]
    simpa [input, clock] using hclockFrame.symm ▸ rfl
  have hfinishObservation :
      ReferenceActivePhysicalStep.collectionFinish (x := x) payload snap.clockStarted o
        (ReferenceActivePhysicalStep.receiveUp prepared l1) =
        { configuration := .collection payload finished actualLastProposal
          upDecoderBank := bank
          failure := none
          recording := some o
          up := (ReferenceActivePhysicalStep.receiveUp prepared l1).diagnostic } := by
    unfold ReferenceActivePhysicalStep.collectionFinish
    simp only [hreceiveResult, hfinish, hclockFinished]
    rfl
  have hobserveFinish : prepared.observeCoordinator =
      ReferenceActivePhysicalStep.collectionFinish (x := x) payload snap.clockStarted o
        (ReferenceActivePhysicalStep.receiveUp prepared l1) := hobserve
  have hstepFields := ReferenceActivePhysicalStep.step_next_fields x
  have hstepCoordinator : (ReferenceActivePhysicalStep.step x).next.coordinator =
      .collection payload finished actualLastProposal := by
    simpa [ReferenceActivePhysicalStep.step, hfinishObservation] using
      congrArg ReferenceActivePhysicalStep.CoordinatorObservation.configuration hobserveFinish
  have hfinishedIncrement : finished.increment = fun a => l.increment a + l1.gammaLoc a := by
    funext a
    simp [finished, CoordinatorCollectionLedger.finishRoundCandidate, l2, hincrement1]
  have hfinishedGamma : finished.gammaLoc = fun _ => 0 := by
    funext a
    rfl
  have hfinishedCursor : finished.cursor = sourceRound x.time + 1 := by
    simp [finished, CoordinatorCollectionLedger.finishRoundCandidate, l2, hcursor1]
  have hfinishedFreeze : finished.freezeAt = l.freezeAt := by
    simp [finished, CoordinatorCollectionLedger.finishRoundCandidate, l2, hfreeze1]
  have hfinishedSigma : finished.sigma = l.sigma := by
    simp [finished, CoordinatorCollectionLedger.finishRoundCandidate, l2, hσ1]
  have hfinishedCutoff : finished.cutoff = l.cutoff := by
    simp [finished, CoordinatorCollectionLedger.finishRoundCandidate, l2, hcut1]
  have hfinishedPhase : finished.phase = CoordinatorCollectionLedger.Phase.ready := rfl
  have hfinishedPending : finished.pending = l.pending := by
    simpa [finished, CoordinatorCollectionLedger.finishRoundCandidate, l2] using hpending1
  have hfinishedAssignment : finished.assignment = l.assignment := by
    simpa [finished, CoordinatorCollectionLedger.finishRoundCandidate, l2] using hassignment1
  have hfinishedBase : finished.baseScore = l.baseScore := by
    simpa [finished, CoordinatorCollectionLedger.finishRoundCandidate, l2] using hbase1
  have hfinishedCutoffRegisters : finished.cutoffRegisters = l.cutoffRegisters := by
    simpa [finished, CoordinatorCollectionLedger.finishRoundCandidate, l2] using
      hcutRegisters1
  have hfinishedCurrent : finished.currentRegisters = l1.currentRegisters := rfl
  have hfinishedRawBuffer : finished.rawBuffer = l1.rawBuffer := rfl
  have hfinishedHistory : finished.enabledHistory = l1.enabledHistory := rfl
  have hpendingEq : l1.pending = l.pending := by
    simpa [l2] using hpending1
  have hassignmentEq : l1.assignment = l.assignment := by
    simpa [l2] using hassignment1
  have hfinishedArmEq : ∀ a,
      CoordinatorCollectionLedger.armPending finished a ↔
        CoordinatorCollectionLedger.armPending l1 a := by
    intro a
    constructor
    · intro ha
      rcases ha with ⟨i, hi, hassignmentArm⟩
      exact ⟨i, by simpa [hfinishedPending, hpendingEq] using hi,
        by simpa [hfinishedAssignment, hassignmentEq] using hassignmentArm⟩
    · intro ha
      rcases ha with ⟨i, hi, hassignmentArm⟩
      exact ⟨i, by simpa [hfinishedPending, hpendingEq] using hi,
        by simpa [hfinishedAssignment, hassignmentEq] using hassignmentArm⟩
  have hfinishedMass : ∀ a c q, l.cutoffRegisters a = some c →
      l1.currentRegisters a = some q →
      c.score + finished.increment a + q.queue ≤
        (sourceRound x.time + 1 - l.sigma) * D p ∧
      c.score + finished.increment a ≤
        4 * rate.n * (min (sourceRound x.time + 1) l.freezeAt - l.sigma) := by
    intro a c q hc hq
    have hm := hmass a c q hc hq
    refine ⟨?_, ?_⟩ <;> rw [hfinishedIncrement]
    · simpa [Nat.add_assoc] using hm.1
    · simpa [Nat.add_assoc] using hm.2.1
  have hfinishedRaw : ∀ a r amount, finished.rawBuffer a r = some amount →
      0 < amount ∧ amount ≤ D p ∧ l.cutoff ≤ sourceRound r ∧
      sourceRound r < min finished.cursor finished.freezeAt ∧
      CoordinatorCollectionLedger.armPending finished a := by
    intro a r amount hcell
    have hcell1 : l1.rawBuffer a r = some amount := by simpa [hfinishedRawBuffer] using hcell
    have hr := hraw1 a r amount hcell1
    rcases hr with ⟨hpos, hbound, hcut, hspan, hpendingL1⟩
    refine ⟨hpos, hbound, ?_, ?_, (hfinishedArmEq a).2 hpendingL1⟩
    · simpa [finished, CoordinatorCollectionLedger.finishRoundCandidate, l2,
        hcut1] using hcut
    · have hspan' : sourceRound r < min (sourceRound x.time + 1) l.freezeAt := by
        simpa [hcursor1, hfreeze1] using hspan
      simpa [hfinishedCursor, hfinishedFreeze] using hspan'
  have hfinishedHistoryEq : ∀ r, finished.enabledHistory r =
      if l.cutoff ≤ sourceRound r ∧ sourceRound r < finished.cursor then
        some (decide (sourceRound r < finished.freezeAt)) else none := by
    intro r
    have hr := hhistory1 r
    have hcursorIff : sourceRound r < sourceRound x.time + 1 ↔
        sourceRound r ≤ sourceRound x.time := by
      dsimp [sourceRound]
      omega
    simpa [hfinishedHistory, hfinishedCursor, hfinishedFreeze, hcut1, hcursor1,
      hfreeze1, hcursorIff,
      sourceRound, ReferenceContinuingCollectionStartDomains.sourceRound,
      CoordinatorCollectionLedger.sourceRound] using hr
  have hbankWellFormed :=
    CoordinatorUpReception.decoderBankAfter_wellFormed receptionInput hdomain
  have hinputBank : receptionInput.upDecoderBank = x.state.upDecoderBank := rfl
  have hbankReady : ∀ i : Fin (p.m - 1),
      (bank i).pending.length < AffineBatchDecoder.quota p ∧
      (∀ batch, batch ∈ (bank i).completed →
        batch.length = AffineBatchDecoder.quota p) ∧
      (i ∉ finished.pending → (bank i).pending = []) := by
    intro i
    have hwf := hbankWellFormed i
    refine ⟨hwf.1, hwf.2, ?_⟩
    intro hout
    by_cases hi : i = receptionInput.selectedFollower
    · subst i
      have hout1 : receptionInput.selectedFollower ∉ l1.pending := by
        simpa [finished, CoordinatorCollectionLedger.finishRoundCandidate, l2] using hout
      have hinputLedger : receptionInput.ledger = l1 := rfl
      have houtLedger : receptionInput.selectedFollower ∉ receptionInput.ledger.pending := by
        simpa [hinputLedger] using hout1
      have hnotEligible : ¬ AffineBatchDecoder.eligible
          ((CoordinatorUpReception.traceAt receptionInput) receptionInput.time) := by
        intro hEligible
        have hselected := hEligible.1
        have hgate : CoordinatorUpReception.receptionGate receptionInput := by
          simpa [CoordinatorUpReception.traceAt, CoordinatorUpReception.roundInput] using hselected
        exact houtLedger hgate.2.2
      have hunchanged := CoordinatorUpReception.decoderTransition_ineligible
        receptionInput hdomain hnotEligible
      have houtOriginal : receptionInput.selectedFollower ∉ l.pending := by
        simpa [hpending1] using hout1
      have hempty := (hbank receptionInput.selectedFollower).2.2 houtOriginal
      simpa [bank, CoordinatorUpReception.decoderBankAfter, hunchanged, hinputBank] using hempty
    · have hunchanged := CoordinatorUpReception.decoderBankAfter_unselected
        receptionInput i hi
      have houtOriginal : i ∉ l.pending := by
        simpa [hfinishedPending] using hout
      simpa [bank, hunchanged, hinputBank] using (hbank i).2.2 houtOriginal
  have hvalidFinished : CoordinatorCollectionLedger.validLedgerCheck finished = true := by
    simpa [finished] using hfinishCandidateValid
  have hfinishedIncrementBound : ∀ a, finished.increment a ≤ p.T * D p := by
    intro a
    have h := hincrementDomain2 a
    simpa [finished, CoordinatorCollectionLedger.finishRoundCandidate, l2,
      hincrement1] using h
  have hfinishedRegisters : ∀ a,
      (finished.currentRegisters a = none ↔
        CoordinatorCollectionLedger.armPending finished a) ∧
      (finished.cutoffRegisters a = none ↔
        CoordinatorCollectionLedger.armPending finished a) := by
    intro a
    constructor
    · change l1.currentRegisters a = none ↔
        CoordinatorCollectionLedger.armPending finished a
      exact Iff.trans (hregisters1 a).1 (hfinishedArmEq a).symm
    · change l1.cutoffRegisters a = none ↔
        CoordinatorCollectionLedger.armPending finished a
      exact Iff.trans (hregisters1 a).2.1 (hfinishedArmEq a).symm
  have hfinishedGammaPending : ∀ a,
      CoordinatorCollectionLedger.armPending finished a →
        finished.increment a = 0 ∧ finished.gammaLoc a = 0 := by
    intro a hp
    have hp2 : CoordinatorCollectionLedger.armPending l2 a := by
      rcases hp with ⟨i, hi, ha⟩
      exact ⟨i, by simpa [hfinishedPending, l2, hpendingEq] using hi,
        by simpa [hfinishedAssignment, l2, hassignmentEq] using ha⟩
    have hz := hpendingZero2 a hp2
    constructor
    · dsimp [finished, CoordinatorCollectionLedger.finishRoundCandidate]
      omega
    · rfl
  have hstepBank : (ReferenceActivePhysicalStep.step x).next.upDecoderBank = bank := by
    calc
      (ReferenceActivePhysicalStep.step x).next.upDecoderBank =
          (ReferenceActivePhysicalStep.prepare x).observeCoordinator.upDecoderBank :=
        hstepFields.2.1
      _ = bank := by rw [hobserveFinish, hfinishObservation]
  have hbankReadyNext : ∀ i : Fin (p.m - 1),
      ((ReferenceActivePhysicalStep.step x).next.upDecoderBank i).pending.length <
        AffineBatchDecoder.quota p ∧
      (∀ batch, batch ∈ ((ReferenceActivePhysicalStep.step x).next.upDecoderBank i).completed →
        batch.length = AffineBatchDecoder.quota p) ∧
      (i ∉ finished.pending →
        ((ReferenceActivePhysicalStep.step x).next.upDecoderBank i).pending = []) := by
    simpa [hstepBank] using hbankReady
  have hstepActivations :
      (ReferenceActivePhysicalStep.step x).next.activations = x.state.activations :=
    hstepFields.2.2.1
  have hstepFollowers : ∀ i,
      (ReferenceActivePhysicalStep.step x).followers i = prepared.observeFollower i := by
    intro i
    rfl
  have hstepOwnEntries :
      (ReferenceActivePhysicalStep.step x).ownEntries = prepared.feedback.ownEntries := rfl
  have hnextInput : sourceRound x.time < p.T →
      ∃ xNext : RoundInput p rate,
        xNext.state = (ReferenceActivePhysicalStep.step x).next ∧
        xNext.rows = x.rows ∧ xNext.selected = x.selected ∧
        xNext.rewards = x.rewards ∧ xNext.time.val = x.time.val + 1 ∧
        ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain
          xNext payload finished actualLastProposal := by
    intro htimeNext
    let nextTime : Fin p.T := ⟨x.time.val + 1, by
      dsimp [sourceRound] at htimeNext
      omega⟩
    let xNext : RoundInput p rate := {
      state := (ReferenceActivePhysicalStep.step x).next
      rows := x.rows
      selected := x.selected
      time := nextTime
      active := by
        intro i
        have hi := hstepActivations
        rw [hi]
        have hactive := x.active i
        dsimp [nextTime]
        omega
      rewards := x.rewards }
    refine ⟨xNext, rfl, rfl, rfl, rfl, rfl, ?_⟩
    refine ⟨?_, hfinishedPhase, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hbankReadyNext⟩
    · simpa [xNext] using hstepCoordinator
    · simpa [finished, CoordinatorCollectionLedger.finishRoundCandidate, l2, hσ1] using hσpos
    · simpa [finished, CoordinatorCollectionLedger.finishRoundCandidate, l2, hσ1] using hσT
    · simpa [finished, CoordinatorCollectionLedger.finishRoundCandidate, l2,
        hσ1, hcut1] using hσcut
    · simpa [finished, CoordinatorCollectionLedger.finishRoundCandidate, l2, hσ1] using
        hσpayload
    · simpa [finished, CoordinatorCollectionLedger.finishRoundCandidate, l2, hcut1] using hcutPos
    · simpa [finished, CoordinatorCollectionLedger.finishRoundCandidate, l2, hcut1] using hcutT
    · simpa [finished, CoordinatorCollectionLedger.finishRoundCandidate, l2,
        hcut1, hfreeze1] using hcutFreeze
    · simpa [finished, CoordinatorCollectionLedger.finishRoundCandidate, l2,
        hfreeze1] using hfreezeT
    · simpa [finished, CoordinatorCollectionLedger.finishRoundCandidate, l2,
        hfreeze1] using hgrid
    · simpa [xNext, nextTime, sourceRound,
        ReferenceContinuingCollectionStartDomains.sourceRound,
        CoordinatorCollectionLedger.sourceRound] using hfinishedCursor
    · rw [hfinishedCutoff, hfinishedCursor]
      have hcutBefore : l.cutoff < sourceRound x.time := by
        simpa [hcursor] using hcutCursor
      exact Nat.lt_succ_of_lt hcutBefore
    · rw [hfinishedCursor]
      exact Nat.le_trans (Nat.succ_le_of_lt htimeNext) (Nat.le_succ _)
    · simpa [finished, CoordinatorCollectionLedger.finishRoundCandidate, l2,
        hassignment1] using hassignment
    · simpa [finished, CoordinatorCollectionLedger.finishRoundCandidate, l2,
        hbase1] using hbaseZero
    · exact hanchor
    · exact hn
    · simpa [finished, CoordinatorCollectionLedger.finishRoundCandidate, l2,
        hpending1] using hpending
    · intro a
      exact hfinishedRegisters a
    · intro a
      constructor
      · simp [finished, CoordinatorCollectionLedger.finishRoundCandidate]
      · intro hp
        exact (hfinishedGammaPending a hp).1
    · intro a c hc
      have hc1 : l1.cutoffRegisters a = some c := by
        simpa [finished, CoordinatorCollectionLedger.finishRoundCandidate, l2,
          hcutRegisters1] using hc
      have hc0 : l.cutoffRegisters a = some c := by
        simpa [hcutRegisters1] using hc1
      simpa [finished, CoordinatorCollectionLedger.finishRoundCandidate, l2,
        hcut1, hσ1] using (hcutDomain a c hc0)
    · intro a c q hc hq
      have hc1 : l.cutoffRegisters a = some c := by
        simpa [finished, CoordinatorCollectionLedger.finishRoundCandidate, l2,
          hcutRegisters1] using hc
      have hq1 : l1.currentRegisters a = some q := by
        simpa [finished, CoordinatorCollectionLedger.finishRoundCandidate, l2] using hq
      refine ⟨(hcurrent1 a q hq1).2, ?_⟩
      simpa [hfinishedCursor, hfinishedFreeze, sourceRound,
        ReferenceContinuingCollectionStartDomains.sourceRound,
        CoordinatorCollectionLedger.sourceRound, hfinishedSigma] using
          (hfinishedMass a c q hc1 hq1).1
    · intro a c q hc hq
      have hc1 : l.cutoffRegisters a = some c := by
        simpa [finished, CoordinatorCollectionLedger.finishRoundCandidate, l2,
          hcutRegisters1] using hc
      have hq1 : l1.currentRegisters a = some q := by
        simpa [finished, CoordinatorCollectionLedger.finishRoundCandidate, l2] using hq
      simpa [hfinishedCursor, hfinishedFreeze, sourceRound,
        ReferenceContinuingCollectionStartDomains.sourceRound,
        CoordinatorCollectionLedger.sourceRound, hfinishedSigma] using
          (hfinishedMass a c q hc1 hq1).2
    · intro a r amount hcell
      simpa [finished, CoordinatorCollectionLedger.finishRoundCandidate, l2,
        hcut1] using hfinishedRaw a r amount hcell
    · intro r
      simpa [finished, CoordinatorCollectionLedger.finishRoundCandidate, l2,
        hcut1] using hfinishedHistoryEq r
  have hboundary : sourceRound x.time = p.T →
      continuingCollectionReadyBoundaryDomain
        (ReferenceActivePhysicalStep.step x).next payload finished actualLastProposal := by
    intro hterminal
    refine ⟨hstepCoordinator, hfinishedPhase, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hbankReadyNext⟩
    · simpa [finished, CoordinatorCollectionLedger.finishRoundCandidate, l2, hσ1] using hσpos
    · simpa [finished, CoordinatorCollectionLedger.finishRoundCandidate, l2, hσ1] using hσT
    · simpa [finished, CoordinatorCollectionLedger.finishRoundCandidate, l2,
        hσ1, hcut1] using hσcut
    · simpa [finished, CoordinatorCollectionLedger.finishRoundCandidate, l2, hσ1] using
        hσpayload
    · simpa [finished, CoordinatorCollectionLedger.finishRoundCandidate, l2, hcut1] using hcutPos
    · simpa [finished, CoordinatorCollectionLedger.finishRoundCandidate, l2, hcut1] using hcutT
    · simpa [finished, CoordinatorCollectionLedger.finishRoundCandidate, l2,
        hcut1, hfreeze1] using hcutFreeze
    · simpa [finished, CoordinatorCollectionLedger.finishRoundCandidate, l2,
        hfreeze1] using hfreezeT
    · simpa [finished, CoordinatorCollectionLedger.finishRoundCandidate, l2,
        hfreeze1] using hgrid
    · rw [hfinishedCursor, hterminal]
    · rw [hfinishedCutoff, hfinishedCursor]
      have hcutBefore : l.cutoff < sourceRound x.time := by
        simpa [hcursor] using hcutCursor
      exact Nat.lt_succ_of_lt hcutBefore
    · rw [hfinishedCursor, hterminal]
    · simpa [finished, CoordinatorCollectionLedger.finishRoundCandidate, l2,
        hassignment1] using hassignment
    · simpa [finished, CoordinatorCollectionLedger.finishRoundCandidate, l2,
        hbase1] using hbaseZero
    · exact hanchor
    · exact hn
    · simpa [finished, CoordinatorCollectionLedger.finishRoundCandidate, l2,
        hpending1] using hpending
    · intro a
      exact hfinishedRegisters a
    · intro a
      constructor
      · simp [finished, CoordinatorCollectionLedger.finishRoundCandidate]
      · intro hp
        exact (hfinishedGammaPending a hp).1
    · intro a c hc
      have hc1 : l1.cutoffRegisters a = some c := by
        simpa [finished, CoordinatorCollectionLedger.finishRoundCandidate, l2,
          hcutRegisters1] using hc
      have hc0 : l.cutoffRegisters a = some c := by
        simpa [hcutRegisters1] using hc1
      simpa [finished, CoordinatorCollectionLedger.finishRoundCandidate, l2,
        hcut1, hσ1] using (hcutDomain a c hc0)
    · intro a c q hc hq
      have hc1 : l.cutoffRegisters a = some c := by
        simpa [finished, CoordinatorCollectionLedger.finishRoundCandidate, l2,
          hcutRegisters1] using hc
      have hq1 : l1.currentRegisters a = some q := by
        simpa [finished, CoordinatorCollectionLedger.finishRoundCandidate, l2] using hq
      refine ⟨(hcurrent1 a q hq1).2, ?_⟩
      simpa [hfinishedCursor, hfinishedFreeze, sourceRound,
        ReferenceContinuingCollectionStartDomains.sourceRound,
        CoordinatorCollectionLedger.sourceRound, hfinishedSigma] using
          (hfinishedMass a c q hc1 hq1).1
    · intro a c q hc hq
      have hc1 : l.cutoffRegisters a = some c := by
        simpa [finished, CoordinatorCollectionLedger.finishRoundCandidate, l2,
          hcutRegisters1] using hc
      have hq1 : l1.currentRegisters a = some q := by
        simpa [finished, CoordinatorCollectionLedger.finishRoundCandidate, l2] using hq
      simpa [hfinishedCursor, hfinishedFreeze, sourceRound,
        ReferenceContinuingCollectionStartDomains.sourceRound,
        CoordinatorCollectionLedger.sourceRound, hfinishedSigma] using
          (hfinishedMass a c q hc1 hq1).2
    · intro a r amount hcell
      simpa [finished, CoordinatorCollectionLedger.finishRoundCandidate, l2,
        hcut1] using hfinishedRaw a r amount hcell
    · intro r
      simpa [finished, CoordinatorCollectionLedger.finishRoundCandidate, l2,
        hcut1] using hfinishedHistoryEq r
  refine ⟨l2, bank, hreceiveResult, rfl, hdomain, hinputCheck,
    hdiagnosticResult, finished, hfinish, rfl, hfinishedIncrement, hfinishedGamma,
    hfinishedCursor, hfinishedPhase, hfinishedPending, hfinishedAssignment,
    hfinishedBase, hfinishedCutoffRegisters, hfinishedCurrent, hfinishedRawBuffer,
    hfinishedHistory, hfinishedMass, hfinishedRaw, hfinishedHistoryEq,
    hvalidFinished, clockFinished, hclockFinished, rfl, rfl, rfl, hlastProposal,
    hfinishObservation, hobserveFinish, ?_, hstepCoordinator, hstepBank,
    hstepActivations, hstepFollowers, hstepOwnEntries, hnextInput, ?_⟩
  · rfl
  · intro hterminal
    exact hboundary hterminal

end Bandits.Support.ReferenceContinuingCollectionRejectedFinishDomains

end
