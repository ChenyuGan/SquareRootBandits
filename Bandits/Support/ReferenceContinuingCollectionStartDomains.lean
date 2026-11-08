/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCutoffFinishSafety
public import Bandits.Support.ReferenceFirstLaunchNumericalCell
public import Bandits.Support.ReferenceCollectionUpAcceptance

import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Continuing first-collection start domains

This module records a literal, local induction domain for one continuing
operation after its cutoff. It is intentionally distinct from any manuscript
theorem or whole-run invariant. Its source evidence is
`sources/zip4/manuscript/06_interruptions.tex:41-70,246-295`,
`sources/zip4/manuscript/04_slow_fast_learner.tex:157-174`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-64`.

The ready predicate spells out its complete state, queue, weight-cap, raw
history, enable history, and decoder-bank contents. In particular, it does
not assert that a physical operation succeeds, that a receiver accepts a word,
or that an arbitrary source-facing theorem holds.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions

namespace Bandits.Support.ReferenceContinuingCollectionStartDomains

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev State := ReferenceActivePhysicalStep.State
abbrev RoundInput := ReferenceActivePhysicalStep.RoundInput
abbrev Payload {p : Parameters} (rate : RateInput p) :=
  ReferenceActivePhysicalStep.Payload rate
abbrev Ledger {p : Parameters} (rate : RateInput p) :=
  ReferenceActivePhysicalStep.Ledger rate

variable {p : Parameters} {rate : RateInput p}

private theorem clippedGridSpan_le_episodeHorizon
    (sigma : Fin p.T) (cursor freezeAt : ℕ)
    (hfreeze : freezeAt = FollowerCutoffScan.gridBoundary p rate.eta.val sigma) :
    min cursor freezeAt - (sigma.val + 1) ≤
      ReplayWeightStability.episodeHorizon rate.eta.val := by
  let H := ReplayWeightStability.episodeHorizon rate.eta.val
  have hH : 0 < H := by
    exact FollowerCutoffScan.episodeHorizon_pos_of_source_cap p rate.eta.val
      rate.eta.property rate.sourceCap
  have hmod : (sigma.val + 1) % H < H := Nat.mod_lt _ hH
  have hdiv : (sigma.val + 1) % H + H * ((sigma.val + 1) / H) =
      sigma.val + 1 := Nat.mod_add_div _ _
  have hrounded : H * ((sigma.val + 1) / H + 1) ≤ sigma.val + 1 + H := by
    rw [Nat.mul_succ]
    omega
  have hclip : freezeAt ≤ H * ((sigma.val + 1) / H + 1) := by
    rw [hfreeze]
    exact Nat.min_le_right _ _
  dsimp [H] at *
  omega

/-- The source one-based round attached to a zero-based calendar index. -/
abbrev sourceRound (r : Fin p.T) : ℕ := r.val + 1

/-- Literal ready-state domain for a continuing first collection operation.

The clauses are, in order: (1) the actual collection state and exact local
clock coordinates; (2) the two known-register maps agree with the pending
assignment arms; (3) zero ready service, disjoint pending increments, cutoff
queue and service domains, and joint current score/queue domains; (4) the
joint current score/service-cap budget; (5) positive raw-buffer entries and
the exact enable-history interval; and (6) the current physical decoder-bank
quota domains. The assignment, zero base scores, unit anchors, and shared
integer numerator are also literal fields. Sources: the ranges in the module
docstring. -/
def continuingCollectionReadyDomain
    (x : RoundInput p rate) (payload : Payload rate) (l : Ledger rate)
    (saved : Option (Fin p.T × Bool)) : Prop :=
  x.state.coordinator = .collection payload l saved ∧
  l.phase = CoordinatorCollectionLedger.Phase.ready ∧
  1 ≤ l.sigma ∧ l.sigma ≤ p.T ∧ l.sigma < l.cutoff ∧
  l.sigma = payload.sigma.val + 1 ∧
  1 ≤ l.cutoff ∧ l.cutoff ≤ p.T ∧
  l.cutoff ≤ l.freezeAt ∧ l.freezeAt ≤ p.T + 1 ∧
  l.freezeAt = FollowerCutoffScan.gridBoundary p rate.eta.val payload.sigma ∧
  l.cursor = x.time.val + 1 ∧
  l.cutoff < l.cursor ∧ l.cursor ≤ p.T + 1 ∧
  l.assignment.arm = payload.assignment.assigned ∧
  l.baseScore = (fun _ : Fin (p.m - 1) => (0 : ℕ)) ∧
  (∀ a : Fin p.K, payload.anchor a = 1) ∧
  payload.n = rate.n ∧
  l.pending.Nonempty ∧
  (∀ a : Fin p.K,
    (l.currentRegisters a = none ↔ CoordinatorCollectionLedger.armPending l a) ∧
    (l.cutoffRegisters a = none ↔ CoordinatorCollectionLedger.armPending l a)) ∧
  (∀ a : Fin p.K,
    l.gammaLoc a = 0 ∧
    (CoordinatorCollectionLedger.armPending l a → l.increment a = 0)) ∧
  (∀ a c, l.cutoffRegisters a = some c →
    c.score + c.queue ≤ (l.cutoff - l.sigma) * D p ∧
    c.lastService ≤ D p) ∧
  (∀ a c q, l.cutoffRegisters a = some c → l.currentRegisters a = some q →
    q.lastService ≤ D p ∧
    c.score + l.increment a + q.queue ≤ (l.cursor - l.sigma) * D p) ∧
  (∀ a c q, l.cutoffRegisters a = some c → l.currentRegisters a = some q →
    c.score + l.increment a ≤
      4 * rate.n * (min l.cursor l.freezeAt - l.sigma)) ∧
  (∀ a r amount, l.rawBuffer a r = some amount →
    0 < amount ∧ amount ≤ D p ∧
    l.cutoff ≤ sourceRound r ∧
    sourceRound r < min l.cursor l.freezeAt ∧
    CoordinatorCollectionLedger.armPending l a) ∧
  (∀ r,
    l.enabledHistory r =
      if l.cutoff ≤ sourceRound r ∧ sourceRound r < l.cursor then
        some (decide (sourceRound r < l.freezeAt))
      else none) ∧
  (∀ i : Fin (p.m - 1),
    (x.state.upDecoderBank i).pending.length < AffineBatchDecoder.quota p ∧
    (∀ batch, batch ∈ (x.state.upDecoderBank i).completed →
      batch.length = AffineBatchDecoder.quota p) ∧
    (i ∉ l.pending → (x.state.upDecoderBank i).pending = []) )

private theorem allFin_eq_true_iff {length : ℕ} (test : Fin length → Bool) :
    CoordinatorCollectionLedger.allFin length test = true ↔ ∀ i, test i = true := by
  unfold CoordinatorCollectionLedger.allFin
  rw [List.all_eq_true]
  constructor
  · intro h i
    exact h (test i) (by simp)
  · intro h b hb
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp hb
    subst b
    exact h i

private theorem armPendingCheck_eq_true_iff
    {p : Parameters} {rate : RateInput p} (l : Ledger rate) (a : Fin p.K) :
    CoordinatorCollectionLedger.armPendingCheck l a = true ↔
      CoordinatorCollectionLedger.armPending l a := by
  unfold CoordinatorCollectionLedger.armPendingCheck
  unfold CoordinatorCollectionLedger.anyFin
  rw [List.any_eq_true]
  simp [CoordinatorCollectionLedger.armPending]

/-- The literal ready-domain facts imply the ledger's executable validity
check. This derives every register, ready-history, pending-arm, and raw-entry
test from the predicate fields. -/
theorem ready_domain_validLedgerCheck
    (x : RoundInput p rate) (payload : Payload rate) (l : Ledger rate)
    (saved : Option (Fin p.T × Bool))
    (h : continuingCollectionReadyDomain x payload l saved) :
    CoordinatorCollectionLedger.validLedgerCheck l = true := by
  classical
  rcases h with ⟨hstate, hphase, hσpos, hσT, _hσu, hσpayload, huPos, huT,
    hug, hgT, hvEq, hcursorEq, huv, hvT, hassign, hbase, hanchor, hn, hpending,
    hregister, hgamma, hcutoff, hpaired, hcap, hraw, hhistory, hbank⟩
  have hcursorD : (l.cursor - l.sigma) * D p ≤ p.T * D p := by
    exact Nat.mul_le_mul_right (D p) (by omega)
  have hcutoffD : (l.cutoff - l.sigma) * D p ≤ p.T * D p := by
    exact Nat.mul_le_mul_right (D p) (by omega)
  have hcurrentDomain : ∀ a q, l.currentRegisters a = some q →
      q.queue ≤ p.T * D p ∧ q.lastService ≤ D p := by
    intro a q hq
    have hnotPending : ¬ CoordinatorCollectionLedger.armPending l a := by
      intro hp
      have hnone := (hregister a).1.mpr hp
      rw [hq] at hnone
      cases hnone
    have hc : ∃ c, l.cutoffRegisters a = some c := by
      cases hcut : l.cutoffRegisters a with
      | none => exact False.elim (hnotPending ((hregister a).2.mp hcut))
      | some c => exact ⟨c, rfl⟩
    rcases hc with ⟨c, hc⟩
    have hmass := (hpaired a c q hc hq).2
    constructor
    · omega
    · exact (hpaired a c q hc hq).1
  have hcutoffDomain : ∀ a c, l.cutoffRegisters a = some c →
      c.score ≤ p.T * D p ∧ c.queue ≤ p.T * D p ∧ c.lastService ≤ D p := by
    intro a c hc
    have hdomain := hcutoff a c hc
    constructor
    · omega
    constructor
    · omega
    · exact hdomain.2
  have hincrementDomain : ∀ a, l.increment a ≤ p.T * D p := by
    intro a
    by_cases hp : CoordinatorCollectionLedger.armPending l a
    · have hz := (hgamma a).2 hp
      simp [hz]
    · have hc : ∃ c, l.cutoffRegisters a = some c := by
        cases hcut : l.cutoffRegisters a with
        | none => exact False.elim (hp ((hregister a).2.mp hcut))
        | some c => exact ⟨c, rfl⟩
      rcases hc with ⟨c, hcutc⟩
      have hq : ∃ q, l.currentRegisters a = some q := by
        cases hcur : l.currentRegisters a with
        | none => exact False.elim (hp ((hregister a).1.mp hcur))
        | some q => exact ⟨q, rfl⟩
      rcases hq with ⟨q, hcur⟩
      have hmass := (hpaired a c q hcutc hcur).2
      omega
  have hcurrentCheck : CoordinatorCollectionLedger.allFin p.K
      (fun a : Fin p.K => match l.currentRegisters a with
        | none => true
        | some q => decide (q.queue ≤ p.T * D p) && decide (q.lastService ≤ D p)) = true := by
    apply (allFin_eq_true_iff _).2
    intro a
    cases hq : l.currentRegisters a with
    | none => simp
    | some q => simp [hcurrentDomain a q hq]
  have hcutoffCheck : CoordinatorCollectionLedger.allFin p.K
      (fun a : Fin p.K => match l.cutoffRegisters a with
        | none => true
        | some c => decide (c.score ≤ p.T * D p) &&
          decide (c.queue ≤ p.T * D p) && decide (c.lastService ≤ D p)) = true := by
    apply (allFin_eq_true_iff _).2
    intro a
    cases hc : l.cutoffRegisters a with
    | none => simp
    | some c => simp [hcutoffDomain a c hc]
  have hbaseCheck : CoordinatorCollectionLedger.allFin (p.m - 1)
      (fun i : Fin (p.m - 1) => decide (l.baseScore i ≤ p.T * D p)) = true := by
    apply (allFin_eq_true_iff _).2
    intro i
    have htd : 0 ≤ p.T * D p := Nat.zero_le _
    rw [hbase]
    exact decide_eq_true (show (0 : ℕ) ≤ p.T * D p from htd)
  have hincrementCheck : CoordinatorCollectionLedger.allFin p.K
      (fun a : Fin p.K => decide (l.increment a ≤ p.T * D p)) = true := by
    apply (allFin_eq_true_iff _).2
    intro a
    exact decide_eq_true (hincrementDomain a)
  have hgammaCheck : CoordinatorCollectionLedger.allFin p.K
      (fun a : Fin p.K => decide (l.gammaLoc a ≤ D p)) = true := by
    apply (allFin_eq_true_iff _).2
    intro a
    have hz := (hgamma a).1
    simp [hz]
  have hregisterCheck : CoordinatorCollectionLedger.registerDomainsCheck l = true := by
    change (CoordinatorCollectionLedger.allFin p.K (fun a : Fin p.K =>
      match l.currentRegisters a with
      | none => true
      | some r => decide (r.queue ≤ p.T * D p) && decide (r.lastService ≤ D p)) &&
      CoordinatorCollectionLedger.allFin p.K (fun a : Fin p.K =>
        match l.cutoffRegisters a with
        | none => true
        | some r => decide (r.score ≤ p.T * D p) &&
          decide (r.queue ≤ p.T * D p) && decide (r.lastService ≤ D p)) &&
      CoordinatorCollectionLedger.allFin (p.m - 1) (fun i : Fin (p.m - 1) =>
        decide (l.baseScore i ≤ p.T * D p)) &&
      CoordinatorCollectionLedger.allFin p.K (fun a : Fin p.K =>
        decide (l.increment a ≤ p.T * D p)) &&
      CoordinatorCollectionLedger.allFin p.K (fun a : Fin p.K =>
        decide (l.gammaLoc a ≤ D p)) = true)
    rw [hcurrentCheck, hcutoffCheck, hbaseCheck, hincrementCheck, hgammaCheck]
    simp
  have hpendingCurrent : CoordinatorCollectionLedger.allFin p.K
      (fun a : Fin p.K =>
        (l.currentRegisters a).isNone == CoordinatorCollectionLedger.armPendingCheck l a) = true := by
    apply (allFin_eq_true_iff _).2
    intro a
    by_cases hp : CoordinatorCollectionLedger.armPending l a
    · have hnone := (hregister a).1.mpr hp
      have hpc := (armPendingCheck_eq_true_iff l a).2 hp
      simp [hnone, hpc]
    · have hpc : CoordinatorCollectionLedger.armPendingCheck l a = false := by
        cases h : CoordinatorCollectionLedger.armPendingCheck l a with
        | false => rfl
        | true => exact False.elim (hp ((armPendingCheck_eq_true_iff l a).mp h))
      have hsome : l.currentRegisters a ≠ none := by
        intro hn
        exact hp ((hregister a).1.mp hn)
      cases hc : l.currentRegisters a with
      | none => exact False.elim (hsome hc)
      | some q => simp [hpc]
  have hpendingCutoff : CoordinatorCollectionLedger.allFin p.K
      (fun a : Fin p.K =>
        (l.cutoffRegisters a).isNone == CoordinatorCollectionLedger.armPendingCheck l a) = true := by
    apply (allFin_eq_true_iff _).2
    intro a
    by_cases hp : CoordinatorCollectionLedger.armPending l a
    · have hnone := (hregister a).2.mpr hp
      have hpc := (armPendingCheck_eq_true_iff l a).2 hp
      simp [hnone, hpc]
    · have hpc : CoordinatorCollectionLedger.armPendingCheck l a = false := by
        cases h : CoordinatorCollectionLedger.armPendingCheck l a with
        | false => rfl
        | true => exact False.elim (hp ((armPendingCheck_eq_true_iff l a).mp h))
      have hsome : l.cutoffRegisters a ≠ none := by
        intro hn
        exact hp ((hregister a).2.mp hn)
      cases hc : l.cutoffRegisters a with
      | none => exact False.elim (hsome hc)
      | some c => simp [hpc]
  have hzeroPendingIncrement : CoordinatorCollectionLedger.allFin p.K
      (fun a : Fin p.K => (!CoordinatorCollectionLedger.armPendingCheck l a) ||
        decide (l.increment a = 0)) = true := by
    apply (allFin_eq_true_iff _).2
    intro a
    by_cases hp : CoordinatorCollectionLedger.armPending l a
    · have hpc := (armPendingCheck_eq_true_iff l a).2 hp
      have hz := (hgamma a).2 hp
      simp [hpc, hz]
    · have hpc : CoordinatorCollectionLedger.armPendingCheck l a = false := by
        cases h : CoordinatorCollectionLedger.armPendingCheck l a with
        | false => rfl
        | true => exact False.elim (hp ((armPendingCheck_eq_true_iff l a).mp h))
      simp [hpc]
  have hzeroGamma : CoordinatorCollectionLedger.allFin p.K
      (fun a : Fin p.K => decide (l.gammaLoc a = 0)) = true := by
    apply (allFin_eq_true_iff _).2
    intro a
    exact decide_eq_true (hgamma a).1
  have hrawCheck : CoordinatorCollectionLedger.rawEntryDomainsCheck l = true := by
    unfold CoordinatorCollectionLedger.rawEntryDomainsCheck
    apply (allFin_eq_true_iff _).2
    intro a
    apply (allFin_eq_true_iff _).2
    intro r
    cases hcell : l.rawBuffer a r with
    | none => simp
    | some amount =>
      rcases hraw a r amount hcell with ⟨hpos, hD, hu, hmin, hp⟩
      have hsourceCursor : sourceRound r < l.cursor :=
        lt_of_lt_of_le hmin (Nat.min_le_left _ _)
      have hsourceFreeze : sourceRound r < l.freezeAt :=
        lt_of_lt_of_le hmin (Nat.min_le_right _ _)
      have hpc := (armPendingCheck_eq_true_iff l a).2 hp
      simp [hphase, hpos, hD, hu, hsourceCursor, hsourceFreeze, hpc,
        CoordinatorCollectionLedger.sourceRound]
  have hreadyHistory : CoordinatorCollectionLedger.readyHistoryCheck l = true := by
    unfold CoordinatorCollectionLedger.readyHistoryCheck
    apply (allFin_eq_true_iff _).2
    intro r
    by_cases hbefore : sourceRound r < l.cutoff
    · simp [CoordinatorCollectionLedger.sourceRound, hbefore]
    · have hu : l.cutoff ≤ sourceRound r := by omega
      by_cases htime : sourceRound r < l.cursor
      · have hflag := hhistory r
        simp [sourceRound, hu, htime] at hflag
        simp [hbefore, hflag, htime, CoordinatorCollectionLedger.sourceRound]
      · have hcursor : l.cursor ≤ sourceRound r := by omega
        have hflag := hhistory r
        simp [sourceRound, hu, htime] at hflag
        simp [hbefore, hflag, htime, CoordinatorCollectionLedger.sourceRound]
  have hcutoffCursor : l.cutoff ≤ l.cursor := by omega
  have hcursorT1 : l.cursor ≤ p.T + 1 := by omega
  have hpendingGamma : CoordinatorCollectionLedger.allFin p.K
      (fun a : Fin p.K => (!CoordinatorCollectionLedger.armPendingCheck l a) ||
        decide (l.gammaLoc a = 0)) = true := by
    apply (allFin_eq_true_iff _).2
    intro a
    simp [(hgamma a).1]
  simp [CoordinatorCollectionLedger.validLedgerCheck, hphase,
    hσpos, hσT, huPos, huT, hug, hgT, hcutoffCursor, hcursorT1,
    hzeroGamma, hpendingGamma,
    hreadyHistory, hregisterCheck, hrawCheck, hpendingCurrent,
    hpendingCutoff, hzeroPendingIncrement]

private theorem ready_collectionCoreValid
    (x : RoundInput p rate) (payload : Payload rate) (l : Ledger rate)
    (saved : Option (Fin p.T × Bool)) (cutoff : Fin p.T)
    (hcutoff : cutoff.val + 1 = l.cutoff)
    (h : continuingCollectionReadyDomain x payload l saved) :
    CoordinatorRoundDispatch.CollectionCoreValid
      (ReferenceActivePhysicalStep.collectionInput x payload l
        (ReferenceActivePhysicalStep.collectionClock payload l saved cutoff) cutoff) := by
  classical
  have hledgerValid := ready_domain_validLedgerCheck x payload l saved h
  rcases h with ⟨hstate, hphase, hσpos, hσT, hσu, hσpayload, huPos, huT,
    hug, hgT, hfreeze, hcursor, huv, hvT, hassign, hbase, hanchor, hn,
    hpending, hregister, hgamma, hcutoffDomain, hpaired, hcap, hraw,
    hhistory, hbank⟩
  let clock := ReferenceActivePhysicalStep.collectionClock payload l saved cutoff
  refine {
    payload_n_eq := ?_
    ledger_valid := ?_
    ledger_ready := hphase
    assignment_eq := ?_
    base_score_eq := rfl
    clock_parameter_valid := ?_
    clock_registers_valid := ?_
    clock_start_time_valid := ?_
    clock_sigma_eq := rfl
    clock_cutoff_eq := rfl
    ledger_sigma_eq := ?_
    ledger_cutoff_eq := ?_
    ledger_freeze_eq := rfl
    ledger_cursor_eq := ?_
    decoder_bank_valid := ?_ }
  · exact ReferenceActivePhysicalStep.payload_n_eq payload
  · change CoordinatorCollectionLedger.validLedgerCheck l = true
    exact hledgerValid
  · intro i
    exact congrArg (fun f : Fin (p.m - 1) → Fin p.K => f i) hassign
  · exact ReferenceCoordinatorClockDomains.proposalParameterValid_of_rate rate
  · change CoordinatorPhaseClock.clockRegistersValid p rate.eta.val clock
    unfold CoordinatorPhaseClock.clockRegistersValid
    simp only [clock, ReferenceActivePhysicalStep.collectionClock,
      CoordinatorPhaseClock.boundaryFromSigma, hfreeze]
    constructor
    · trivial
    · constructor
      · rw [← hfreeze]
        omega
      · constructor
        · omega
        · rw [← hfreeze]
          omega
  · change CoordinatorPhaseClock.startRoundTimeValid p x.time clock
    simp [clock, ReferenceActivePhysicalStep.collectionClock,
      CoordinatorPhaseClock.startRoundTimeValid]
    omega
  · change l.sigma = CoordinatorRecorderComplementBridge.sourceStart payload
    simpa [CoordinatorRecorderComplementBridge.sourceStart] using hσpayload
  · change l.cutoff = CoordinatorCollectionUpRoundStep.sourceCutoff cutoff
    simp only [CoordinatorCollectionUpRoundStep.sourceCutoff]
    omega
  · change l.cursor = CoordinatorCollectionUpRoundStep.sourceRound x.time
    simpa [CoordinatorCollectionUpRoundStep.sourceRound] using hcursor
  · apply (CoordinatorUpReception.decoderBankCheck_eq_true_iff p
      x.state.upDecoderBank).2
    intro i
    exact ⟨(hbank i).1, (hbank i).2.1⟩

private theorem ready_complement_weightEnvelope
    (x : RoundInput p rate) (payload : Payload rate) (l : Ledger rate)
    (saved : Option (Fin p.T × Bool)) (cutoff : Fin p.T)
    (core : CoordinatorRoundDispatch.CollectionCoreValid
      (ReferenceActivePhysicalStep.collectionInput x payload l
        (ReferenceActivePhysicalStep.collectionClock payload l saved cutoff) cutoff))
    (h : continuingCollectionReadyDomain x payload l saved) :
    ∀ j : CanonicalFastSampling.FastArm payload.slowSet,
      payload.anchor j.1 ≤
          (CoordinatorCollectionInteractive.PreObservationInputs.weights
            (ReferenceActivePhysicalStep.collectionInput x payload l
              (ReferenceActivePhysicalStep.collectionClock payload l saved cutoff) cutoff)
            core.ledger_valid core.assignment_eq) j ∧
        (CoordinatorCollectionInteractive.PreObservationInputs.weights
            (ReferenceActivePhysicalStep.collectionInput x payload l
              (ReferenceActivePhysicalStep.collectionClock payload l saved cutoff) cutoff)
            core.ledger_valid core.assignment_eq) j ≤ 2 * payload.anchor j.1 := by
  classical
  rcases h with ⟨_, _, _, _, _, hσpayload, _, _, _, _, hfreeze, hcursor,
    _, _, hassign, _, hanchor, _, _, hregister, hgamma, hcutoffDomain,
    hpaired, hcap, _, _, _⟩
  let span := min l.cursor l.freezeAt - l.sigma
  have hspan : span ≤ ReplayWeightStability.episodeHorizon rate.eta.val := by
    dsimp [span]
    rw [hσpayload]
    exact clippedGridSpan_le_episodeHorizon payload.sigma l.cursor l.freezeAt hfreeze
  have hD : 0 < (D p : ℝ) := by exact_mod_cast ConstructorDimensions.D_pos p
  have heta : 0 < rate.eta.val := rate.eta.property
  have hnscale : (rate.n : ℝ) = rate.eta.val * (D p : ℝ) := rate.n_scale
  intro j
  have ha : j.1 ∉ payload.slowSet.1 := (Finset.mem_sdiff.mp j.2).2
  obtain ⟨c, hc, q, hq⟩ := CoordinatorCollectionUpRoundStep.complementRegisters_known
    l payload core.ledger_valid core.assignment_eq j.1 ha
  have hscoreCap := hcap j.1 c q hc hq
  have hchosen := Classical.choose_spec
    (CoordinatorCollectionUpRoundStep.complementRegisters_known
      l payload core.ledger_valid core.assignment_eq j.1 ha)
  have hchosenEq : Classical.choose
      (CoordinatorCollectionUpRoundStep.complementRegisters_known
        l payload core.ledger_valid core.assignment_eq j.1 ha) = c :=
    Option.some.inj (hchosen.1.symm.trans hc)
  have hscore :
      CoordinatorCollectionUpRoundStep.complementCurrentScore l payload
        core.ledger_valid core.assignment_eq j.1 ha = c.score + l.increment j.1 := by
    unfold CoordinatorCollectionUpRoundStep.complementCurrentScore
    rw [hchosenEq]
  let z := CoordinatorCollectionUpRoundStep.complementCurrentScore l payload
    core.ledger_valid core.assignment_eq j.1 ha
  have hz : z ≤ 4 * rate.n * span := by
    dsimp [z, span]
    rw [hscore]
    exact hscoreCap
  let w := (CoordinatorCollectionInteractive.PreObservationInputs.weights
    (ReferenceActivePhysicalStep.collectionInput x payload l
      (ReferenceActivePhysicalStep.collectionClock payload l saved cutoff) cutoff)
    core.ledger_valid core.assignment_eq) j
  have hw : w = ScoreWeights.scoreWeight
      (AssignmentScoreReconstruction.sourceWeightBase p) z := rfl
  have hscoreReal : (z : ℝ) ≤ 4 * (rate.n : ℝ) * (span : ℝ) := by
    exact_mod_cast hz
  have hlogBase := ScoreWeightLogBounds.source_base_log_pow_le hD z
  have hlog : Real.log w ≤ (1 : ℝ) / 16 := by
    rw [hw]
    change Real.log ((1 + 1 / (D p : ℝ)) ^ z) ≤ (1 : ℝ) / 16
    calc
      Real.log ((1 + 1 / (D p : ℝ)) ^ z) ≤ (z : ℝ) / (D p : ℝ) := by
        simpa [ReplayWeightStability.sourceBase] using hlogBase
      _ ≤ (4 * (rate.n : ℝ) * (span : ℝ)) / (D p : ℝ) :=
        div_le_div_of_nonneg_right hscoreReal hD.le
      _ = 4 * rate.eta.val * (span : ℝ) := by
        rw [hnscale]
        field_simp [ne_of_gt hD]
      _ ≤ 4 * rate.eta.val *
          (ReplayWeightStability.episodeHorizon rate.eta.val : ℝ) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hspan) (by positivity)
      _ ≤ 4 * rate.eta.val * (1 / (64 * rate.eta.val)) :=
        mul_le_mul_of_nonneg_left
          (ReplayWeightStability.episodeHorizon_cast_le heta) (by positivity)
      _ = (1 : ℝ) / 16 := by
        field_simp [ne_of_gt rate.eta.property]
        norm_num
  have hweightPos : 0 < w := by
    rw [hw]
    change 0 < ScoreWeights.scoreWeight
      (ReplayWeightStability.sourceBase (D p)) z
    exact ReplayWeightStability.source_weight_pos (D := D p) (score := z)
      (ConstructorDimensions.D_pos p)
  have hweightLeTwo : w ≤ 2 := by
    have hlogTwo : Real.log w ≤ Real.log 2 :=
      hlog.trans ReplayWeightStability.one_sixteenth_lt_log_two.le
    exact (Real.log_le_log_iff hweightPos (by norm_num)).mp hlogTwo
  have hweightLower : 1 ≤ w := by
    rw [hw]
    have hbase : 1 ≤ AssignmentScoreReconstruction.sourceWeightBase p := by
      unfold AssignmentScoreReconstruction.sourceWeightBase
      exact ScoreWeights.sourceBase_one_le hD
    exact ScoreWeights.scoreWeight_mono hbase (Nat.zero_le z)
  have hanchorOne := hanchor j.1
  rw [hanchorOne]
  exact ⟨hweightLower, by simpa [hanchorOne] using hweightLeTwo⟩

private theorem ready_collectionCurrentScoresCheck
    (x : RoundInput p rate) (payload : Payload rate) (l : Ledger rate)
    (saved : Option (Fin p.T × Bool)) (cutoff : Fin p.T)
    (hcutoff : cutoff.val + 1 = l.cutoff)
    (core : CoordinatorRoundDispatch.CollectionCoreValid
      (ReferenceActivePhysicalStep.collectionInput x payload l
        (ReferenceActivePhysicalStep.collectionClock payload l saved cutoff) cutoff))
    (h : continuingCollectionReadyDomain x payload l saved) :
    CoordinatorRoundDispatch.collectionCurrentScoresCheck
      (ReferenceActivePhysicalStep.collectionInput x payload l
        (ReferenceActivePhysicalStep.collectionClock payload l saved cutoff) cutoff) = true := by
  classical
  rcases h with ⟨_, _, hσpos, _, _, _, _, _, _, _, _, hcursor, _, hvT,
    _, _, _, _, _, hregister, _, _, hpaired, hcap, _, _, _⟩
  apply (CoordinatorRoundDispatch.collectionCurrentScoresCheck_iff _ core).2
  intro a ha
  obtain ⟨c, hc, q, hq⟩ := CoordinatorCollectionUpRoundStep.complementRegisters_known
    l payload core.ledger_valid core.assignment_eq a ha
  have hcapA := hcap a c q hc hq
  have hscore := CoordinatorRoundDispatch.collection_complementCurrentScore_eq
    _ core a ha c hc
  have hspan : min l.cursor l.freezeAt - l.sigma ≤ p.T := by omega
  have hcapacity : 4 * rate.n ≤ D p :=
    ActiveFollowerDownAcceptance.four_n_le_D p rate
  have hbound : 4 * rate.n * (min l.cursor l.freezeAt - l.sigma) ≤ p.T * D p := by
    calc
      4 * rate.n * (min l.cursor l.freezeAt - l.sigma) ≤
          D p * (min l.cursor l.freezeAt - l.sigma) :=
        Nat.mul_le_mul_right _ hcapacity
      _ ≤ D p * p.T := Nat.mul_le_mul_left _ hspan
      _ = p.T * D p := Nat.mul_comm _ _
  rw [hscore]
  exact hcapA.trans hbound

private theorem ready_preInputsValid
    (x : RoundInput p rate) (payload : Payload rate) (l : Ledger rate)
    (saved : Option (Fin p.T × Bool)) (cutoff : Fin p.T)
    (hcutoff : cutoff.val + 1 = l.cutoff)
    (core : CoordinatorRoundDispatch.CollectionCoreValid
      (ReferenceActivePhysicalStep.collectionInput x payload l
        (ReferenceActivePhysicalStep.collectionClock payload l saved cutoff) cutoff))
    (h : continuingCollectionReadyDomain x payload l saved) :
    CoordinatorCollectionInteractive.PreInputsValid
      (ReferenceActivePhysicalStep.collectionInput x payload l
        (ReferenceActivePhysicalStep.collectionClock payload l saved cutoff) cutoff) := by
  classical
  have hweightEnvelope := ready_complement_weightEnvelope x payload l saved cutoff
    core h
  rcases h with ⟨_, _, _, _, hσu, hσpayload, _, _, _, _, hfreeze, hcursor,
    huv, _, hassign, _, hanchor, _, hpending, _, _, _, _, _, _, _, _⟩
  let input := ReferenceActivePhysicalStep.collectionInput x payload l
    (ReferenceActivePhysicalStep.collectionClock payload l saved cutoff) cutoff
  let weights := CoordinatorCollectionInteractive.PreObservationInputs.weights
    input core.ledger_valid core.assignment_eq
  have hchoice : CoordinatorLocalArmChoice.ChoiceInputsValid payload
      (some (CoordinatorCollectionUpRoundStep.localCutoff cutoff)) x.time weights := by
    apply CoordinatorLocalArmChoice.choiceInputsValid_mk
    · simp only [CoordinatorLocalArmChoice.assignmentStart,
        CoordinatorLocalArmChoice.sourceRound]
      omega
    · simp [CoordinatorLocalArmChoice.assignmentStart,
        CoordinatorLocalArmChoice.cutoffRound,
        CoordinatorCollectionUpRoundStep.localCutoff,
        CoordinatorCollectionUpRoundStep.sourceCutoff]
      omega
    · intro j
      have henv := hweightEnvelope j
      have hanchorPos : 0 < payload.anchor j.1 := by rw [hanchor j.1]; norm_num
      refine ⟨by linarith [hanchorPos, henv.1], henv.1, ?_⟩
      simpa [hanchor j.1] using henv.2
  refine {
    ledger_valid := core.ledger_valid
    ledger_ready := core.ledger_ready
    pending_nonempty := ?_
    assignment_eq := core.assignment_eq
    base_score_eq := core.base_score_eq
    clock_parameter_valid := core.clock_parameter_valid
    clock_registers_valid := core.clock_registers_valid
    clock_start_time_valid := core.clock_start_time_valid
    clock_sigma_eq := core.clock_sigma_eq
    clock_cutoff_eq := core.clock_cutoff_eq
    ledger_sigma_eq := core.ledger_sigma_eq
    ledger_cutoff_eq := core.ledger_cutoff_eq
    ledger_freeze_eq := core.ledger_freeze_eq
    ledger_cursor_eq := core.ledger_cursor_eq
    decoder_bank_valid := core.decoder_bank_valid
    choice_valid := ?_ }
  · exact hpending
  · simpa [input, weights,
      CoordinatorCollectionInteractive.PreObservationInputs.weights,
      CoordinatorRoundDispatch.CollectionInput,
      ReferenceActivePhysicalStep.collectionInput] using hchoice

/-- Compute the actual collection dispatcher's complete pre-choice domain from
the literal ready predicate. The caller still supplies the actual finite
clock cutoff index and its ledger projection; no start outcome or selected arm
is assumed. This result stops before executing the physical recorder. -/
theorem ready_collection_prechoice_domains
    (x : RoundInput p rate) (payload : Payload rate) (l : Ledger rate)
    (saved : Option (Fin p.T × Bool)) (cutoff : Fin p.T)
    (hcutoff : cutoff.val + 1 = l.cutoff)
    (h : continuingCollectionReadyDomain x payload l saved) :
    let input := ReferenceActivePhysicalStep.collectionInput x payload l
      (ReferenceActivePhysicalStep.collectionClock payload l saved cutoff) cutoff
    ∃ core : CoordinatorRoundDispatch.CollectionCoreValid input,
      CoordinatorRoundDispatch.collectionCurrentScoresCheck input = true ∧
      CoordinatorCollectionInteractive.PreInputsValid input ∧
      ∀ j : CanonicalFastSampling.FastArm payload.slowSet,
        payload.anchor j.1 ≤
          CoordinatorCollectionInteractive.PreObservationInputs.weights input
            core.ledger_valid core.assignment_eq j ∧
        CoordinatorCollectionInteractive.PreObservationInputs.weights input
            core.ledger_valid core.assignment_eq j ≤ 2 * payload.anchor j.1 := by
  classical
  dsimp only
  let input := ReferenceActivePhysicalStep.collectionInput x payload l
    (ReferenceActivePhysicalStep.collectionClock payload l saved cutoff) cutoff
  let core := ready_collectionCoreValid x payload l saved cutoff hcutoff h
  have hcurrent := ready_collectionCurrentScoresCheck x payload l saved cutoff
    hcutoff core h
  have hpre := ready_preInputsValid x payload l saved cutoff hcutoff core h
  have henvelope := ready_complement_weightEnvelope x payload l saved cutoff core h
  refine ⟨core, hcurrent, hpre, ?_⟩
  intro j
  simpa [input, ReferenceActivePhysicalStep.collectionInput,
    CoordinatorRoundDispatch.CollectionInput] using henvelope j

/-- The checked collection recorder returns its actual output for every valid
collection-mode input. The local boundary and current-weight envelope are
explicit helper inputs so downstream producers must derive them from their
own domain. The branch proof retains zero-floor successful gates. -/
theorem collection_recorder_run_total
    {eta : ReferencePrelaunchFollower.LearningRate}
    {s : AssignmentStartPayload.Input p eta}
    (input : CoordinatorRecorderComplementBridge.Input s)
    (hvalid : CoordinatorRecorderComplementBridge.LocalInputsValid input)
    (hmode : input.mode = .collection) :
    ∃ out : CoordinatorRecordingOperation.Output p,
      CoordinatorRecorderComplementBridge.run input = some out := by
  classical
  by_cases hdata : CoordinatorRecorderComplementBridge.selectedSlot input =
      PublicDiscreteDraws.dataSlot
  · by_cases hsource : CoordinatorRecorderComplementBridge.selectedRecorder input =
        ActiveRoundActions.coordinator p.two_le_m
    · by_cases hfrozen : CoordinatorRecorderComplementBridge.isFrozen input
      · exact ⟨CoordinatorRecordingOperation.zeroOutput p,
          CoordinatorRecorderComplementBridge.run_zero_of_frozen input hvalid
            hdata hsource hfrozen⟩
      · have howned : CoordinatorRecorderComplementBridge.ownsArm input := by
          simp [CoordinatorRecorderComplementBridge.ownsArm,
            CoordinatorRecorderComplementBridge.operationMode, hmode,
            CoordinatorRecordingOperation.ownsArm]
        by_cases hmask : CoordinatorRecorderComplementBridge.ownMaskPasses input
        · by_cases hthin : CoordinatorRecorderComplementBridge.thinScalar input ≤
              CoordinatorRecorderComplementBridge.threshold input hvalid
          · obtain ⟨out, hout, _, _⟩ :=
              CoordinatorRecorderComplementBridge.run_gate_and_floor input hvalid
                hdata hsource hfrozen howned hmask hthin
            exact ⟨out, hout⟩
          · exact ⟨CoordinatorRecordingOperation.zeroOutput p,
              CoordinatorRecorderComplementBridge.run_zero_of_thinning_rejected input
                hvalid hdata hsource hfrozen howned hmask hthin⟩
        · exact ⟨CoordinatorRecordingOperation.zeroOutput p,
            CoordinatorRecorderComplementBridge.run_zero_of_mask_rejected input
              hvalid hdata hsource hfrozen howned hmask⟩
    · exact ⟨CoordinatorRecordingOperation.zeroOutput p,
        CoordinatorRecorderComplementBridge.run_zero_of_other_source input hvalid
          hdata hsource⟩
  · exact ⟨CoordinatorRecordingOperation.zeroOutput p,
      CoordinatorRecorderComplementBridge.run_zero_of_not_data input hvalid hdata⟩

/-- The full ready-state joint service cap and register matching bound each
disjoint arm increment by the episode-wide `T * D` budget. Pending increments
are zero by the literal predicate. -/
theorem ready_increment_le_total
    (x : RoundInput p rate) (payload : Payload rate) (l : Ledger rate)
    (saved : Option (Fin p.T × Bool))
    (h : continuingCollectionReadyDomain x payload l saved)
    (a : Fin p.K) : l.increment a ≤ p.T * D p := by
  classical
  rcases h with ⟨_, _, hσpos, _, _, _, _, _, _, _, _, _, _, hvT,
    _, _, _, _, _, hregister, hgamma, _, hpaired, _, _, _, _⟩
  by_cases hpending : CoordinatorCollectionLedger.armPending l a
  · rw [(hgamma a).2 hpending]
    exact Nat.zero_le _
  · have hc : ∃ c, l.cutoffRegisters a = some c := by
      cases hcut : l.cutoffRegisters a with
      | none => exact False.elim (hpending ((hregister a).2.mp hcut))
      | some c => exact ⟨c, rfl⟩
    have hq : ∃ q, l.currentRegisters a = some q := by
      cases hcur : l.currentRegisters a with
      | none => exact False.elim (hpending ((hregister a).1.mp hcur))
      | some q => exact ⟨q, rfl⟩
    rcases hc with ⟨c, hc⟩
    rcases hq with ⟨q, hq⟩
    have hmass := (hpaired a c q hc hq).2
    have hspan : l.cursor - l.sigma ≤ p.T := by omega
    have hspanD : (l.cursor - l.sigma) * D p ≤ p.T * D p :=
      Nat.mul_le_mul_right (D p) hspan
    omega

private theorem start_candidate_budgets
    (x : RoundInput p rate) (payload : Payload rate) (l : Ledger rate)
    (saved : Option (Fin p.T × Bool))
    (h : continuingCollectionReadyDomain x payload l saved)
    (o : CoordinatorRecordingOperation.Output p) :
    let raw := CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder o
    let next := CoordinatorCollectionLedger.startRoundCandidate l x.time
      (ReferenceActivePhysicalStep.collectionEnabled l x.time) raw
    (∀ a c qNew, l.cutoffRegisters a = some c → next.currentRegisters a = some qNew →
      c.score + l.increment a + next.gammaLoc a + qNew.queue ≤
        (x.time.val + 2 - l.sigma) * D p ∧
      c.score + l.increment a + next.gammaLoc a ≤
        4 * rate.n * (min (x.time.val + 2) l.freezeAt - l.sigma) ∧
      qNew.queue ≤ p.T * D p ∧ qNew.lastService ≤ D p) ∧
    (∀ a, next.gammaLoc a ≤ 4 * rate.n ∧ next.gammaLoc a ≤ D p ∧
      l.increment a + next.gammaLoc a ≤ p.T * D p) ∧
    (∀ a, (next.currentRegisters a = none ↔ CoordinatorCollectionLedger.armPending l a) ∧
      (CoordinatorCollectionLedger.armPending l a → next.gammaLoc a = 0)) ∧
    (∀ a r amount, next.rawBuffer a r = some amount →
      0 < amount ∧ amount ≤ D p ∧ l.cutoff ≤ sourceRound r ∧
      sourceRound r < min (x.time.val + 2) l.freezeAt ∧ CoordinatorCollectionLedger.armPending l a) ∧
    (∀ r, next.enabledHistory r =
      if l.cutoff ≤ sourceRound r ∧ sourceRound r < x.time.val + 2 then
        some (decide (sourceRound r < l.freezeAt)) else none) ∧
    CoordinatorCollectionLedger.rawSlotFreshCheck l x.time raw = true ∧
    (∀ a qOld qNew, l.currentRegisters a = some qOld → next.currentRegisters a = some qNew →
      if sourceRound x.time < l.freezeAt then
        next.gammaLoc a + qNew.queue = qOld.queue + CoordinatorCollectionLedger.localArrival raw a
      else next.gammaLoc a = 0 ∧ qNew.queue = qOld.queue) := by
  classical
  dsimp only
  let raw := CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder o
  let next := CoordinatorCollectionLedger.startRoundCandidate l x.time
      (ReferenceActivePhysicalStep.collectionEnabled l x.time) raw
  rcases h with ⟨_, _, hσpos, hσT, hσu, _, huPos, huT, hug, hgT, _, hv,
    huv, hvT, _, _, _, _, _, hregs, hzero, hcut, hpaired, hcap, hraw, hhist, _⟩
  have htime : x.time.val + 1 ≤ p.T := Nat.succ_le_of_lt x.time.isLt
  have hen : ReferenceActivePhysicalStep.collectionEnabled l x.time = decide (sourceRound x.time < l.freezeAt) := by
    have hs : 0 < l.sigma := by omega
    have hu : l.cutoff ≤ x.time.val + 1 := by omega
    simp only [ReferenceActivePhysicalStep.collectionEnabled, sourceRound, hs, hu, true_and]
  have hlocal : ∀ a, CoordinatorCollectionLedger.localArrival raw a ≤ D p := by
    intro a
    cases hg : o.gateArm with
    | none => simp [raw, CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder,
        hg, CoordinatorCollectionLedger.localArrival]
    | some b =>
        simp only [raw, CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder,
          hg, Option.map_some, CoordinatorCollectionLedger.localArrival]
        split
        · exact o.rawArrival_le_D
        · exact Nat.zero_le _
  have hnextKnown : ∀ a q, l.currentRegisters a = some q →
      ∃ qNew, next.currentRegisters a = some qNew ∧
        qNew.lastService = next.gammaLoc a ∧ next.gammaLoc a ≤ 4 * rate.n ∧
        (if sourceRound x.time < l.freezeAt then
          next.gammaLoc a + qNew.queue = q.queue + CoordinatorCollectionLedger.localArrival raw a
        else next.gammaLoc a = 0 ∧ qNew.queue = q.queue) := by
    intro a q hq
    by_cases hf : sourceRound x.time < l.freezeAt
    · have hmin := Nat.min_le_right (4 * rate.n) (q.queue + CoordinatorCollectionLedger.localArrival raw a)
      refine ⟨⟨q.queue + CoordinatorCollectionLedger.localArrival raw a - min (4 * rate.n)
        (q.queue + CoordinatorCollectionLedger.localArrival raw a), min (4 * rate.n)
        (q.queue + CoordinatorCollectionLedger.localArrival raw a)⟩, ?_⟩
      simp only [next, CoordinatorCollectionLedger.startRoundCandidate, hq, hen, hf, decide_true,
        CoordinatorCollectionLedger.localQueueRecord, CoordinatorCollectionLedger.sourceRound, sourceRound, Bool.true_and,
        QueueReplay.transition, ↓reduceIte, Nat.zero_add, true_and] at *
      exact ⟨Nat.min_le_left _ _, by omega⟩
    · refine ⟨⟨q.queue, 0⟩, ?_⟩
      simp [next, CoordinatorCollectionLedger.startRoundCandidate, hq, CoordinatorCollectionLedger.localQueueRecord, hen,
        hf, CoordinatorCollectionLedger.sourceRound, sourceRound, QueueReplay.transition]
  have hunknown : ∀ a, (next.currentRegisters a = none ↔ CoordinatorCollectionLedger.armPending l a) ∧
      (CoordinatorCollectionLedger.armPending l a → next.gammaLoc a = 0) := by
    intro a
    constructor
    · cases hq : l.currentRegisters a with
      | none => simpa [next, CoordinatorCollectionLedger.startRoundCandidate, hq] using (hregs a).1
      | some q => simpa [next, CoordinatorCollectionLedger.startRoundCandidate, hq] using (hregs a).1
    · intro hp
      exact CoordinatorCollectionLedger.startRoundCandidate_unknown_zero l x.time _ raw a ((hregs a).1.mpr hp)
  have hmass : ∀ a c qNew, l.cutoffRegisters a = some c →
      next.currentRegisters a = some qNew →
      c.score + l.increment a + next.gammaLoc a + qNew.queue ≤
        (x.time.val + 2 - l.sigma) * D p ∧
      c.score + l.increment a + next.gammaLoc a ≤
        4 * rate.n * (min (x.time.val + 2) l.freezeAt - l.sigma) ∧
      qNew.queue ≤ p.T * D p ∧ qNew.lastService ≤ D p := by
    intro a c qNew hc hn
    have hnPending : ¬ CoordinatorCollectionLedger.armPending l a := by
      intro hp
      rw [(hunknown a).1.mpr hp] at hn
      cases hn
    obtain ⟨q, hq⟩ : ∃ q, l.currentRegisters a = some q := by
      cases hq : l.currentRegisters a with
      | none => exact False.elim (hnPending ((hregs a).1.mp hq))
      | some q => exact ⟨q, rfl⟩
    obtain ⟨qNew', hn', hlast, hservice, hconserve⟩ := hnextKnown a q hq
    have heq : qNew' = qNew := Option.some.inj (hn'.symm.trans hn)
    subst qNew'
    have hprior := (hpaired a c q hc hq).2
    have hpriorCap := hcap a c q hc hq
    have hDcap := ActiveFollowerDownAcceptance.four_n_le_D p rate
    have hbound : (x.time.val + 2 - l.sigma) * D p ≤ p.T * D p :=
      Nat.mul_le_mul_right _ (by omega)
    have hspan : x.time.val + 2 - l.sigma = (l.cursor - l.sigma) + 1 := by omega
    have hpostMass : c.score + l.increment a + next.gammaLoc a + qNew.queue ≤
        (x.time.val + 2 - l.sigma) * D p := by
      rw [hspan, Nat.add_mul, Nat.one_mul]
      have harr := hlocal a
      by_cases hf : sourceRound x.time < l.freezeAt
      · simp only [hf, ↓reduceIte] at hconserve
        omega
      · simp only [hf, ↓reduceIte] at hconserve
        omega
    have hpostCap : c.score + l.increment a + next.gammaLoc a ≤
        4 * rate.n * (min (x.time.val + 2) l.freezeAt - l.sigma) := by
      by_cases hf : sourceRound x.time < l.freezeAt
      · have hstep : min (x.time.val + 2) l.freezeAt - l.sigma =
            (min l.cursor l.freezeAt - l.sigma) + 1 := by
          dsimp [sourceRound] at hf
          omega
        rw [hstep, Nat.mul_add, Nat.mul_one]
        omega
      · simp only [hf, ↓reduceIte] at hconserve
        have hmono : min l.cursor l.freezeAt - l.sigma ≤
            min (x.time.val + 2) l.freezeAt - l.sigma := by omega
        have hmul := Nat.mul_le_mul_left (4 * rate.n) hmono
        omega
    exact ⟨hpostMass, hpostCap, by omega, hlast ▸ hservice.trans hDcap⟩
  have hserviceAll : ∀ a, next.gammaLoc a ≤ 4 * rate.n ∧
      next.gammaLoc a ≤ D p ∧ l.increment a + next.gammaLoc a ≤ p.T * D p := by
    intro a
    by_cases hp : CoordinatorCollectionLedger.armPending l a
    · simp [(hunknown a).2 hp, (hzero a).2 hp]
    · obtain ⟨q, hq⟩ : ∃ q, next.currentRegisters a = some q := by
        cases hq : next.currentRegisters a with
        | none => exact False.elim (hp ((hunknown a).1.mp hq))
        | some q => exact ⟨q, rfl⟩
      obtain ⟨c, hc⟩ : ∃ c, l.cutoffRegisters a = some c := by
        cases hc : l.cutoffRegisters a with
        | none => exact False.elim (hp ((hregs a).2.mp hc))
        | some c => exact ⟨c, rfl⟩
      have hm := hmass a c q hc hq
      have hbound := Nat.mul_le_mul_right (D p)
        (show x.time.val + 2 - l.sigma ≤ p.T by omega)
      have hs : next.gammaLoc a ≤ 4 * rate.n := by
        cases hold : l.currentRegisters a with
        | none => exact False.elim (hp ((hregs a).1.mp hold))
        | some old =>
          obtain ⟨_, _, _, hs, _⟩ := hnextKnown a old hold
          exact hs
      exact ⟨hs, hs.trans (ActiveFollowerDownAcceptance.four_n_le_D p rate), by omega⟩
  have hrawNext : ∀ a r amount, next.rawBuffer a r = some amount →
      0 < amount ∧ amount ≤ D p ∧ l.cutoff ≤ sourceRound r ∧
      sourceRound r < min (x.time.val + 2) l.freezeAt ∧ CoordinatorCollectionLedger.armPending l a := by
    intro a r amount hr
    have old : l.rawBuffer a r = some amount →
        0 < amount ∧ amount ≤ D p ∧ l.cutoff ≤ sourceRound r ∧
        sourceRound r < min (x.time.val + 2) l.freezeAt ∧ CoordinatorCollectionLedger.armPending l a := by
      intro ho
      rcases hraw a r amount ho with ⟨hpos, hD, hu, ht, hp⟩
      exact ⟨hpos, hD, hu, by omega, hp⟩
    cases hg : o.gateArm with
    | none => exact old (by simpa [next, raw, CoordinatorCollectionLedger.startRoundCandidate,
        CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder, hg] using hr)
    | some b =>
        dsimp [next, raw, CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder,
          CoordinatorCollectionLedger.startRoundCandidate] at hr
        rw [hg] at hr
        simp only [Option.map_some] at hr
        split at hr
        next hw =>
          by_cases hcell : a = b ∧ r = x.time
          · obtain ⟨rfl, rfl⟩ := hcell
            have hamt : o.rawArrival = amount := by simpa [CoordinatorCollectionLedger.putRaw] using hr
            subst amount
            exact ⟨hw.2.1, o.rawArrival_le_D, by dsimp [sourceRound]; omega, by
              dsimp [sourceRound, CoordinatorCollectionLedger.sourceRound] at *
              omega, (hregs _).1.mp hw.1⟩
          · exact old (by simpa [CoordinatorCollectionLedger.putRaw, hcell] using hr)
        next hw => exact old hr
  have hhistory : ∀ r, next.enabledHistory r =
      if l.cutoff ≤ sourceRound r ∧ sourceRound r < x.time.val + 2 then
        some (decide (sourceRound r < l.freezeAt)) else none := by
    intro r
    by_cases heq : r = x.time
    · subst r
      have hu : l.cutoff ≤ sourceRound x.time := by dsimp [sourceRound]; omega
      simp [next, CoordinatorCollectionLedger.startRoundCandidate, hen, hu, sourceRound]
    · have hne : sourceRound r ≠ sourceRound x.time := by
        intro he
        apply heq
        apply Fin.ext
        dsimp [sourceRound] at he
        omega
      have hinterval : (l.cutoff ≤ sourceRound r ∧ sourceRound r < x.time.val + 2) ↔
          (l.cutoff ≤ sourceRound r ∧ sourceRound r < l.cursor) := by
        dsimp [sourceRound] at hne ⊢
        omega
      change Function.update l.enabledHistory x.time
        (some (ReferenceActivePhysicalStep.collectionEnabled l x.time)) r = _
      rw [Function.update_of_ne heq]
      simpa only [hinterval] using hhist r
  have hfresh : ∀ a, l.rawBuffer a x.time = none := by
    intro a
    cases hr : l.rawBuffer a x.time with
    | none => rfl
    | some amount =>
        have ht := (hraw a x.time amount hr).2.2.2.1
        dsimp [sourceRound] at ht
        omega
  refine ⟨hmass, hserviceAll, hunknown, hrawNext, hhistory, ?_, ?_⟩
  · cases hg : o.gateArm with
    | none => simp [CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder,
        hg, CoordinatorCollectionLedger.rawSlotFreshCheck]
    | some b => simp [CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder,
        hg, CoordinatorCollectionLedger.rawSlotFreshCheck, hfresh]
  · intro a qOld qNew hold hnew
    obtain ⟨qNew', hnew', _, _, hconserve⟩ := hnextKnown a qOld hold
    have heq : qNew' = qNew := Option.some.inj (hnew'.symm.trans hnew)
    subst qNew'
    exact hconserve

private theorem start_candidate_valid
    (x : RoundInput p rate) (payload : Payload rate) (l : Ledger rate)
    (saved : Option (Fin p.T × Bool))
    (h : continuingCollectionReadyDomain x payload l saved)
    (o : CoordinatorRecordingOperation.Output p) :
    CoordinatorCollectionLedger.validLedgerCheck
      (CoordinatorCollectionLedger.startRoundCandidate l x.time
        (ReferenceActivePhysicalStep.collectionEnabled l x.time)
        (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder o)) = true := by
  classical
  let next := CoordinatorCollectionLedger.startRoundCandidate l x.time
    (ReferenceActivePhysicalStep.collectionEnabled l x.time)
    (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder o)
  obtain ⟨hmass, hservice, hunknown, hraw, hhistory, _⟩ :=
    start_candidate_budgets x payload l saved h o
  have hvalid := ready_domain_validLedgerCheck x payload l saved h
  have hparts := hvalid
  simp only [CoordinatorCollectionLedger.validLedgerCheck, Bool.and_eq_true] at hparts
  have hcurrentPending := hparts.1.1.1.1.1.2
  have hcutoffPending := hparts.1.1.1.1.2
  have hpendingIncrement := hparts.1.1.2
  have hdomains := hparts.1.2
  simp only [CoordinatorCollectionLedger.registerDomainsCheck, Bool.and_eq_true] at hdomains
  rcases h with ⟨_, _, hσpos, hσT, _, _, huPos, huT, hug, hgT, _, hv,
    huv, hvT, _, _, _, _, _, hregs, hzero, _, _, _, _, _, _⟩
  have hpcheck : ∀ a, CoordinatorCollectionLedger.armPendingCheck next a =
      CoordinatorCollectionLedger.armPendingCheck l a := fun _ => rfl
  have hcurrent : CoordinatorCollectionLedger.allFin p.K (fun a =>
      (next.currentRegisters a).isNone == CoordinatorCollectionLedger.armPendingCheck next a) = true := by
    have heq : ∀ a, (next.currentRegisters a).isNone = (l.currentRegisters a).isNone := by
      intro a
      cases hq : l.currentRegisters a <;>
        simp [next, CoordinatorCollectionLedger.startRoundCandidate, hq]
    simpa only [heq, hpcheck] using hcurrentPending
  have hcutoff : CoordinatorCollectionLedger.allFin p.K (fun a =>
      (next.cutoffRegisters a).isNone == CoordinatorCollectionLedger.armPendingCheck next a) = true :=
    hcutoffPending
  have hinc : CoordinatorCollectionLedger.allFin p.K (fun a =>
      (!CoordinatorCollectionLedger.armPendingCheck next a) || decide (next.increment a = 0)) = true :=
    hpendingIncrement
  have hgammaPending : CoordinatorCollectionLedger.allFin p.K (fun a =>
      (!CoordinatorCollectionLedger.armPendingCheck next a) || decide (next.gammaLoc a = 0)) = true := by
    apply (allFin_eq_true_iff _).2
    intro a
    by_cases hp : CoordinatorCollectionLedger.armPending l a
    · have hz := (hunknown a).2 hp
      change next.gammaLoc a = 0 at hz
      simp only [hz, decide_true, Bool.or_true]
    · have hn : CoordinatorCollectionLedger.armPendingCheck next a = false := by
        rw [hpcheck]
        apply Bool.eq_false_iff.mpr
        exact fun he => hp ((armPendingCheck_eq_true_iff l a).mp he)
      simp only [hn, Bool.not_false, Bool.true_or]
  have hcurrentDomains : CoordinatorCollectionLedger.allFin p.K (fun a =>
      match next.currentRegisters a with
      | none => true
      | some q => decide (q.queue ≤ p.T * D p) && decide (q.lastService ≤ D p)) = true := by
    apply (allFin_eq_true_iff _).2
    intro a
    cases hq : next.currentRegisters a with
    | none => rfl
    | some q =>
      obtain ⟨c, hc⟩ : ∃ c, l.cutoffRegisters a = some c := by
        cases hc : l.cutoffRegisters a with
        | some c => exact ⟨c, rfl⟩
        | none =>
          have hp := (hregs a).2.mp hc
          have hn := (hunknown a).1.mpr hp
          rw [hq] at hn
          cases hn
      have hd := (hmass a c q hc hq).2.2
      simp only [decide_eq_true_eq, Bool.and_eq_true]
      exact hd
  have hgammaDomains : CoordinatorCollectionLedger.allFin p.K
      (fun a => decide (next.gammaLoc a ≤ D p)) = true := by
    apply (allFin_eq_true_iff _).2
    exact fun a => decide_eq_true (hservice a).2.1
  have hregister : CoordinatorCollectionLedger.registerDomainsCheck next = true := by
    simp only [CoordinatorCollectionLedger.registerDomainsCheck, Bool.and_eq_true]
    exact ⟨⟨⟨⟨hcurrentDomains, hdomains.1.1.1.2⟩, hdomains.1.1.2⟩,
      hdomains.1.2⟩, hgammaDomains⟩
  have hrawCheck : CoordinatorCollectionLedger.rawEntryDomainsCheck next = true := by
    apply (allFin_eq_true_iff _).2
    intro a
    apply (allFin_eq_true_iff _).2
    intro r
    cases hr : next.rawBuffer a r with
    | none => rfl
    | some amount =>
      obtain ⟨hpos, hD, hu, ht, hp⟩ := hraw a r amount hr
      have hg : sourceRound r < l.freezeAt := lt_of_lt_of_le ht (Nat.min_le_right _ _)
      have hv : sourceRound r ≤ x.time.val + 1 := by omega
      have hp' : CoordinatorCollectionLedger.armPendingCheck next a = true :=
        (armPendingCheck_eq_true_iff l a).2 hp
      change (decide (0 < amount) && decide (amount ≤ D p) &&
        decide (l.cutoff ≤ CoordinatorCollectionLedger.sourceRound r) &&
        decide (CoordinatorCollectionLedger.sourceRound r < l.freezeAt) &&
        decide (CoordinatorCollectionLedger.sourceRound r ≤ CoordinatorCollectionLedger.sourceRound x.time) &&
        CoordinatorCollectionLedger.armPendingCheck next a) = true
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨⟨⟨⟨hpos, hD⟩, hu⟩, hg⟩, hv⟩, hp'⟩
  have hhistCheck : CoordinatorCollectionLedger.startedHistoryCheck next = true := by
    apply (allFin_eq_true_iff _).2
    intro r
    change (decide (sourceRound r < l.cutoff) ||
      ((next.enabledHistory r).isSome == decide (sourceRound r ≤ sourceRound x.time))) = true
    by_cases hb : sourceRound r < l.cutoff
    · simp only [hb, decide_true, Bool.true_or]
    · have hu : l.cutoff ≤ sourceRound r := by omega
      have hh : next.enabledHistory r =
          if l.cutoff ≤ sourceRound r ∧ sourceRound r < x.time.val + 2 then
            some (decide (sourceRound r < l.freezeAt)) else none := hhistory r
      rw [hh]
      by_cases ht : r ≤ x.time <;> simp [hb, hu, sourceRound, ht]
  simp only [CoordinatorCollectionLedger.validLedgerCheck, Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨?_, hcurrent⟩, hcutoff⟩, hgammaPending⟩, hinc⟩, hregister⟩, hrawCheck⟩
  have hcutCursor : l.cutoff ≤ sourceRound x.time := by dsimp [sourceRound]; omega
  have hcursorT : sourceRound x.time ≤ p.T := Nat.succ_le_of_lt x.time.isLt
  have hcursorT1 : decide (CoordinatorCollectionLedger.sourceRound x.time ≤ p.T + 1) = true :=
    decide_eq_true (by dsimp [CoordinatorCollectionLedger.sourceRound]; omega)
  simp only [CoordinatorCollectionLedger.startRoundCandidate, reduceCtorEq,
    decide_false, Bool.false_or, Bool.not_false, Bool.true_or, and_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨decide_eq_true hσpos, decide_eq_true hσT⟩, decide_eq_true huPos⟩,
      decide_eq_true hug⟩, decide_eq_true huT⟩, decide_eq_true hgT⟩,
      decide_eq_true hcutCursor⟩, hcursorT1⟩,
      decide_eq_true hcursorT⟩, hhistCheck⟩

private theorem ready_actual_dispatch
    (x : RoundInput p rate) (payload : Payload rate) (l : Ledger rate)
    (saved : Option (Fin p.T × Bool))
    (h : continuingCollectionReadyDomain x payload l saved) :
    ∃ cutoff : Fin p.T, cutoff.val + 1 = l.cutoff ∧
    let clock := ReferenceActivePhysicalStep.collectionClock payload l saved cutoff
    let input := ReferenceActivePhysicalStep.collectionInput x payload l clock cutoff
    ∃ (core : CoordinatorRoundDispatch.CollectionCoreValid input)
      (snap : CoordinatorCollectionInteractive.PreparedSnapshot input)
      (hb : snap.clockStarted.clock.g ≤ p.T + 1)
      (hs : CoordinatorRoundDispatch.collectionCurrentScoresCheck input = true),
      (ReferenceActivePhysicalStep.prepare x).coordinator =
        .collection payload l clock cutoff (.continuing core snap hb hs) := by
  classical
  have hI := h
  rcases h with ⟨hstate, _, _, _, _, _, huPos, huT, _, hgT, _, hv, huv, _,
    _, _, _, _, hpending, _⟩
  let cutoff : Fin p.T := ⟨l.cutoff - 1, by omega⟩
  have hcutoff : cutoff.val + 1 = l.cutoff := by dsimp [cutoff]; omega
  refine ⟨cutoff, hcutoff, ?_⟩
  dsimp only
  let clock := ReferenceActivePhysicalStep.collectionClock payload l saved cutoff
  let input := ReferenceActivePhysicalStep.collectionInput x payload l clock cutoff
  obtain ⟨core, hscores, hpre, _⟩ := ready_collection_prechoice_domains
    x payload l saved cutoff hcutoff hI
  have hclock := CoordinatorPhaseClock.startRound_collection_pending p rate.eta.val
    x.time payload.sigma cutoff clock l.pending core.clock_parameter_valid
    core.clock_registers_valid core.clock_sigma_eq core.clock_cutoff_eq
    (by omega) (Finset.nonempty_iff_ne_empty.mp hpending)
  have hdispatch : ∃ (snap : CoordinatorCollectionInteractive.PreparedSnapshot input)
      (hb : snap.clockStarted.clock.g ≤ p.T + 1),
      CoordinatorRoundDispatch.dispatchCollection input = .continuing core snap hb hscores := by
    unfold CoordinatorRoundDispatch.dispatchCollection
    split
    · rename_i failure hfailure
      have hbad := hfailure.symm.trans hclock
      cases hbad
    · rename_i started hstart
      split
      · rename_i hcore
        dsimp only
        split
        · rename_i hp
          split
          · rename_i hchoice
            split
            · contradiction
            · refine ⟨_, ?_, rfl⟩
              have heq := Except.ok.inj (hstart.symm.trans hclock)
              change started.clock.g ≤ p.T + 1
              rw [heq]
              exact hgT
          · rename_i hchoice
            exact False.elim (hchoice hpre.choice_valid)
        · rename_i hp
          exact False.elim (hp hpending)
      · rename_i hc
        exact False.elim (hc core)
  obtain ⟨snap, hb, hdispatch⟩ := hdispatch
  refine ⟨core, snap, hb, hscores, ?_⟩
  change ReferenceActivePhysicalStep.dispatch x = _
  unfold ReferenceActivePhysicalStep.dispatch
  have hcut : 1 ≤ l.cutoff ∧ l.cutoff ≤ p.T := ⟨huPos, huT⟩
  simp only [hstate, dite_eq_left hcut]
  change ReferenceActivePhysicalStep.DispatchCut.collection payload l _ _
    (CoordinatorRoundDispatch.dispatchCollection input) = _
  rw [hdispatch]

private theorem recorder_frozen_gate_none
    {eta : ReferencePrelaunchFollower.LearningRate}
    {payload : AssignmentStartPayload.Input p eta}
    (input : CoordinatorRecorderComplementBridge.Input payload)
    (hlocal : CoordinatorRecorderComplementBridge.LocalInputsValid input)
    (hfrozen : CoordinatorRecorderComplementBridge.isFrozen input)
    (o : CoordinatorRecordingOperation.Output p)
    (hrecord : CoordinatorRecorderComplementBridge.run input = some o) : o.gateArm = none := by
  classical
  have hzero : CoordinatorRecorderComplementBridge.run input =
      some (CoordinatorRecordingOperation.zeroOutput p) := by
    by_cases hd : CoordinatorRecorderComplementBridge.selectedSlot input = PublicDiscreteDraws.dataSlot
    · by_cases hs : CoordinatorRecorderComplementBridge.selectedRecorder input =
          ActiveRoundActions.coordinator p.two_le_m
      · exact CoordinatorRecorderComplementBridge.run_zero_of_frozen input hlocal hd hs hfrozen
      · exact CoordinatorRecorderComplementBridge.run_zero_of_other_source input hlocal hd hs
    · exact CoordinatorRecorderComplementBridge.run_zero_of_not_data input hlocal hd
  have heq := Option.some.inj (hrecord.symm.trans hzero)
  exact congrArg CoordinatorRecordingOperation.Output.gateArm heq

private theorem collectionFinish_diagnostics
    (x : RoundInput p rate) (payload : Payload rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (o : CoordinatorRecordingOperation.Output p) (cut : ReferenceActivePhysicalStep.UpCut p rate) :
    (ReferenceActivePhysicalStep.collectionFinish (x := x) payload started o cut).recording = some o ∧
    (ReferenceActivePhysicalStep.collectionFinish (x := x) payload started o cut).up = cut.diagnostic := by
  classical
  unfold ReferenceActivePhysicalStep.collectionFinish
  split
  · exact ⟨rfl, rfl⟩
  all_goals
    dsimp only
    split
    · exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩
    · split <;> exact ⟨rfl, rfl⟩

/-- One actual continuing first-collection START, strictly before UP reception.
The only logical input is the exposed literal local ready domain. Preparation,
recorder totality, checked ledger start, new-queue joint mass and service cap
are produced here. The final equality exposes the remaining receiver/finish
expression without asserting that either succeeds. Sources: the module ranges. -/
theorem continuing_collection_start_domains
    (x : RoundInput p rate) (payload : Payload rate) (l : Ledger rate)
    (saved : Option (Fin p.T × Bool))
    (h : continuingCollectionReadyDomain x payload l saved) :
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
      l1.pending = l.pending ∧ l1.assignment = l.assignment ∧ l1.baseScore = l.baseScore ∧
      l1.cutoffRegisters = l.cutoffRegisters ∧ l1.increment = l.increment ∧
      (∀ a qOld, l.currentRegisters a = some qOld →
        let transition := QueueReplay.transition (4 * rate.n) (0, qOld.queue)
          (CoordinatorCollectionLedger.localQueueRecord l x.time
            (ReferenceActivePhysicalStep.collectionEnabled l x.time) raw a)
        l1.currentRegisters a = some ⟨transition.2, transition.1⟩ ∧
        l1.gammaLoc a = transition.1) ∧
      (∀ a qOld qNew, l.currentRegisters a = some qOld → l1.currentRegisters a = some qNew →
        if sourceRound x.time < l.freezeAt then
          l1.gammaLoc a + qNew.queue = qOld.queue + CoordinatorCollectionLedger.localArrival raw a
        else l1.gammaLoc a = 0 ∧ qNew.queue = qOld.queue) ∧
      (l.freezeAt ≤ sourceRound x.time → o.gateArm = none ∧
        ∀ a qOld, l.currentRegisters a = some qOld →
          l1.currentRegisters a = some ⟨qOld.queue, 0⟩ ∧ l1.gammaLoc a = 0) ∧
      (raw = none → sourceRound x.time < l.freezeAt →
        ∀ a qOld, l.currentRegisters a = some qOld →
          l1.currentRegisters a = some ⟨qOld.queue - min (4 * rate.n) qOld.queue,
            min (4 * rate.n) qOld.queue⟩) ∧
      (∀ a, (l1.currentRegisters a = none ↔ CoordinatorCollectionLedger.armPending l1 a) ∧
        (l1.cutoffRegisters a = none ↔ CoordinatorCollectionLedger.armPending l1 a) ∧
        (l.currentRegisters a = none → l1.currentRegisters a = none ∧ l1.gammaLoc a = 0)) ∧
      (∀ a c qNew, l.cutoffRegisters a = some c → l1.currentRegisters a = some qNew →
        c.score + l.increment a + l1.gammaLoc a + qNew.queue ≤
          (sourceRound x.time + 1 - l.sigma) * D p ∧
        c.score + l.increment a + l1.gammaLoc a ≤
          4 * rate.n * (min (sourceRound x.time + 1) l.freezeAt - l.sigma) ∧
        qNew.queue ≤ p.T * D p ∧ qNew.lastService ≤ D p) ∧
      (∀ a qNew, l1.currentRegisters a = some qNew →
        qNew.queue ≤ p.T * D p ∧ qNew.lastService ≤ D p) ∧
      (∀ a c, l1.cutoffRegisters a = some c →
        c.score ≤ p.T * D p ∧ c.queue ≤ p.T * D p ∧ c.lastService ≤ D p) ∧
      (∀ a, CoordinatorCollectionLedger.armPending l1 a →
        l1.increment a = 0 ∧ l1.gammaLoc a = 0) ∧
      (∀ a, l1.gammaLoc a ≤ 4 * rate.n ∧ l1.gammaLoc a ≤ D p ∧
        l1.increment a + l1.gammaLoc a ≤ p.T * D p) ∧
      (∀ a c, l1.cutoffRegisters a = some c →
        c.score + c.queue ≤ (l.cutoff - l.sigma) * D p ∧ c.lastService ≤ D p) ∧
      (∀ a r amount, l1.rawBuffer a r = some amount →
        0 < amount ∧ amount ≤ D p ∧ l.cutoff ≤ sourceRound r ∧
        sourceRound r < min (sourceRound x.time + 1) l.freezeAt ∧
        CoordinatorCollectionLedger.armPending l1 a) ∧
      (∀ r, l1.enabledHistory r =
        if l.cutoff ≤ sourceRound r ∧ sourceRound r ≤ sourceRound x.time then
          some (decide (sourceRound r < l.freezeAt)) else none) ∧
      l1.rawBuffer = (match raw with
        | none => l.rawBuffer
        | some (a, amount) =>
          if l.currentRegisters a = none ∧ 0 < amount ∧ sourceRound x.time < l.freezeAt then
            CoordinatorCollectionLedger.putRaw l.rawBuffer a x.time amount else l.rawBuffer) ∧
      (∀ a r, r ≠ x.time → l1.rawBuffer a r = l.rawBuffer a r) ∧
      CoordinatorCollectionLedger.rawSlotFreshCheck l x.time raw = true ∧
      (∀ r rawNext, sourceRound x.time < sourceRound r →
        CoordinatorCollectionLedger.rawSlotFreshCheck l1 r rawNext = true) ∧
      prepared.observeCoordinator =
        ReferenceActivePhysicalStep.collectionFinish (x := x) payload snap.clockStarted o
          (ReferenceActivePhysicalStep.receiveUp prepared l1) ∧
      prepared.observeCoordinator.recording = some o ∧
      prepared.observeCoordinator.up = (ReferenceActivePhysicalStep.receiveUp prepared l1).diagnostic := by
  classical
  obtain ⟨cutoff, hcutoff, core, snap, hb, hs, hdispatch⟩ :=
    ready_actual_dispatch x payload l saved h
  let clock := ReferenceActivePhysicalStep.collectionClock payload l saved cutoff
  let input := ReferenceActivePhysicalStep.collectionInput x payload l clock cutoff
  let prepared := ReferenceActivePhysicalStep.prepare x
  let weights := CoordinatorCollectionInteractive.PreObservationInputs.weights input
    snap.inputsValid.ledger_valid snap.inputsValid.assignment_eq
  let recordingInput := ReferenceActivePhysicalStep.collectionRecordingInput prepared
    payload snap.clockStarted weights
  have hlocal : CoordinatorRecorderComplementBridge.LocalInputsValid recordingInput :=
    ⟨hb, ready_complement_weightEnvelope x payload l saved cutoff core h⟩
  obtain ⟨o, hrecord⟩ := collection_recorder_run_total recordingInput hlocal rfl
  let raw := CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder o
  let next := CoordinatorCollectionLedger.startRoundCandidate l x.time
    (ReferenceActivePhysicalStep.collectionEnabled l x.time) raw
  obtain ⟨hmass, hservice, hunknown, hraw, hhistory, hfresh, hconservation⟩ :=
    start_candidate_budgets x payload l saved h o
  have hvalid := start_candidate_valid x payload l saved h o
  have hincoming := ready_domain_validLedgerCheck x payload l saved h
  rcases h with ⟨_, hphase, hσpos, _, _, _, _, huT, _, _, _, hv, huv, hvT,
    _, _, _, _, _, hregs, hzero, hcut, _⟩
  have hrawDomain : CoordinatorCollectionLedger.rawInputDomainCheck raw = true := by
    cases hg : o.gateArm with
    | none => simp [raw, CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder,
        hg, CoordinatorCollectionLedger.rawInputDomainCheck]
    | some a =>
      simp [raw, CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder,
        hg, CoordinatorCollectionLedger.rawInputDomainCheck, o.rawArrival_le_D]
  have hinput : CoordinatorCollectionLedger.validLedgerCheck l = true ∧ l.phase = .ready ∧
      sourceRound x.time = l.cursor ∧ 1 ≤ sourceRound x.time ∧ sourceRound x.time ≤ p.T ∧
      CoordinatorCollectionLedger.rawInputDomainCheck raw = true :=
    ⟨hincoming, hphase, hv.symm, by dsimp [sourceRound]; omega,
      Nat.succ_le_of_lt x.time.isLt, hrawDomain⟩
  have hstart : CoordinatorCollectionLedger.startRound l (sourceRound x.time)
      (ReferenceActivePhysicalStep.collectionEnabled l x.time) raw = .success next := by
    unfold CoordinatorCollectionLedger.startRound
    rw [dite_eq_left hinput]
    simp only [sourceRound, Nat.add_sub_cancel, Fin.eta]
    change CoordinatorCollectionLedger.rawSlotFreshCheck l x.time raw = true at hfresh
    change CoordinatorCollectionLedger.validLedgerCheck next = true at hvalid
    rw [ite_eq_left hfresh, ite_eq_left hvalid]
  have harm : prepared.coordinator.arm = snap.arm := by
    rw [hdispatch]
    exact ReferenceActivePhysicalStep.collection_arm_equation payload l clock cutoff
      (.continuing core snap hb hs)
  have hobserve : prepared.observeCoordinator = ReferenceActivePhysicalStep.collectionPostChoice
      prepared payload l snap.clockStarted weights := by
    rw [ReferenceActivePhysicalStep.observeCoordinator_collection_equation prepared
      payload l clock cutoff (.continuing core snap hb hs) hdispatch]
    simp only [ReferenceActivePhysicalStep.DispatchCut.selection, Option.some_ne_none, ↓reduceIte]
    rfl
  have hpost := ReferenceActivePhysicalStep.collectionPostChoice_after_start prepared payload l
    snap.clockStarted weights o next hrecord hstart
  refine ⟨cutoff, hcutoff, core, snap, hb, hs, hdispatch, harm, hlocal,
    CoordinatorRecorderComplementBridge.recorderInput_inputsValid recordingInput hlocal,
    o, next, hrecord,
    hstart, rfl, hvalid, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_,
    hconservation, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, hservice, hcut, ?_, ?_, ?_, ?_, hfresh, ?_, hobserve.trans hpost, ?_⟩
  · intro a qOld hq
    exact ⟨CoordinatorCollectionLedger.startRoundCandidate_known_transition l x.time
      (ReferenceActivePhysicalStep.collectionEnabled l x.time) raw a qOld hq,
      by simp only [next, CoordinatorCollectionLedger.startRoundCandidate, hq]; rfl⟩
  · intro hfrozen
    have hgrid : snap.clockStarted.clock.g = l.freezeAt :=
      congrArg CoordinatorPhaseClock.ClockRegisters.g snap.clockStarted_frame.1
    have hf : CoordinatorRecorderComplementBridge.isFrozen recordingInput := by
      change 0 < payload.sigma.val + 1 ∧ x.time.val + 1 ≥ snap.clockStarted.clock.g
      rw [hgrid]
      exact ⟨by omega, hfrozen⟩
    refine ⟨recorder_frozen_gate_none recordingInput hlocal hf o hrecord, ?_⟩
    intro a qOld hold
    exact ReferenceActivePhysicalStep.collection_started_frozen l next x.time raw a qOld
      hold hfrozen hstart
  · intro hrawNone hbefore a qOld hold
    have hen : ReferenceActivePhysicalStep.collectionEnabled l x.time = true := by
      apply decide_eq_true
      dsimp [sourceRound] at hbefore
      omega
    have hsNone : CoordinatorCollectionLedger.startRound l (sourceRound x.time)
        (ReferenceActivePhysicalStep.collectionEnabled l x.time) none = .success next := by
      have hnone : raw = none := hrawNone
      calc
        CoordinatorCollectionLedger.startRound l (sourceRound x.time)
            (ReferenceActivePhysicalStep.collectionEnabled l x.time) none =
            CoordinatorCollectionLedger.startRound l (sourceRound x.time)
              (ReferenceActivePhysicalStep.collectionEnabled l x.time) raw := by rw [hnone]
        _ = .success next := hstart
    exact ReferenceActivePhysicalStep.collection_started_zero_arrival l next x.time a qOld
      hold hen hsNone
  · intro a
    refine ⟨(hunknown a).1, (hregs a).2, ?_⟩
    intro hn
    exact ⟨by simp only [next, CoordinatorCollectionLedger.startRoundCandidate, hn],
      CoordinatorCollectionLedger.startRoundCandidate_unknown_zero l x.time _ raw a hn⟩
  · simpa only [sourceRound, Nat.add_assoc] using hmass
  · intro a qNew hq
    obtain ⟨c, hc⟩ : ∃ c, l.cutoffRegisters a = some c := by
      cases hc : l.cutoffRegisters a with
      | some c => exact ⟨c, rfl⟩
      | none =>
        have hp := (hregs a).2.mp hc
        have hn := (hunknown a).1.mpr hp
        rw [hq] at hn
        cases hn
    exact (hmass a c qNew hc hq).2.2
  · intro a c hc
    have hbound := Nat.mul_le_mul_right (D p)
      (show l.cutoff - l.sigma ≤ p.T by omega)
    have hd := hcut a c hc
    exact ⟨by omega, by omega, hd.2⟩
  · intro a hp
    exact ⟨(hzero a).2 hp, (hunknown a).2 hp⟩
  · exact hraw
  · intro r
    have hh := hhistory r
    have ht : (sourceRound r < x.time.val + 2) ↔ sourceRound r ≤ sourceRound x.time := by
      dsimp [sourceRound]
      omega
    simpa only [ht] using hh
  · cases hg : o.gateArm with
    | none => simp [next, CoordinatorCollectionLedger.startRoundCandidate, raw,
        CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder, hg]
    | some a =>
      by_cases hw : l.currentRegisters a = none ∧ 0 < o.rawArrival ∧
          sourceRound x.time < l.freezeAt <;>
        simp [next, CoordinatorCollectionLedger.startRoundCandidate, raw,
          CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder, hg,
          sourceRound, CoordinatorCollectionLedger.sourceRound] at hw ⊢
  · intro a r hr
    change (CoordinatorCollectionLedger.startRoundCandidate l x.time
      (ReferenceActivePhysicalStep.collectionEnabled l x.time) raw).rawBuffer a r = _
    cases hrRaw : raw with
    | none => simp only [CoordinatorCollectionLedger.startRoundCandidate]
    | some pair =>
      obtain ⟨b, amount⟩ := pair
      simp only [CoordinatorCollectionLedger.startRoundCandidate]
      split
      · exact CoordinatorCollectionLedger.putRaw_other l.rawBuffer b a x.time r amount (Or.inr hr)
      · rfl
  · intro r rawNext hfuture
    have hnone : ∀ a, next.rawBuffer a r = none := by
      intro a
      cases hr : next.rawBuffer a r with
      | none => rfl
      | some amount =>
        have ht := (hraw a r amount hr).2.2.2.1
        dsimp [sourceRound] at ht hfuture
        omega
    cases rawNext with
    | none => rfl
    | some pair => simp [CoordinatorCollectionLedger.rawSlotFreshCheck, hnone]
  · rw [hobserve, hpost]
    exact collectionFinish_diagnostics x payload snap.clockStarted o
      (ReferenceActivePhysicalStep.receiveUp prepared next)

end Bandits.Support.ReferenceContinuingCollectionStartDomains
