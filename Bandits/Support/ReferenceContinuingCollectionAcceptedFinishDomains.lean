/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceContinuingCollectionAcceptedDecodeDomains
import Lean.Elab.Tactic.Omega

/-!
# Continuing collection accepted-UP finish domains

This module applies the accepted decode/replay result to the actual collection
FINISH operation. The ready-state induction domain and the checked UP record's
two joint budgets remain explicit inputs; the result preserves the resulting
ready state for a next round or its terminal boundary, and also handles the
all-known ledger without asserting a pending-only ready predicate.

Source evidence: `sources/zip4/manuscript/06_interruptions.tex:9-100,164-177,246-295`,
`sources/zip4/manuscript/04_slow_fast_learner.tex:157-174`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-64`.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions

namespace Bandits.Support.ReferenceContinuingCollectionAcceptedFinishDomains

abbrev Parameters := ReferenceContinuingCollectionAcceptedDecodeDomains.Parameters
abbrev RateInput := ReferenceContinuingCollectionAcceptedDecodeDomains.RateInput
abbrev State := ReferenceContinuingCollectionAcceptedDecodeDomains.State
abbrev RoundInput := ReferenceContinuingCollectionAcceptedDecodeDomains.RoundInput
abbrev Payload {p : Parameters} (rate : RateInput p) :=
  ReferenceContinuingCollectionAcceptedDecodeDomains.Payload rate
abbrev Ledger {p : Parameters} (rate : RateInput p) :=
  ReferenceContinuingCollectionAcceptedDecodeDomains.Ledger rate
abbrev sourceRound {p : Parameters} (r : Fin p.T) :=
  ReferenceContinuingCollectionAcceptedDecodeDomains.sourceRound r

variable {p : Parameters} {rate : RateInput p}

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

private theorem registerDomainsCheck_of_validLedgerCheck
    (l : Ledger rate)
    (h : CoordinatorCollectionLedger.validLedgerCheck l = true) :
    CoordinatorCollectionLedger.registerDomainsCheck l = true := by
  have hparts := h
  simp only [CoordinatorCollectionLedger.validLedgerCheck,
    Bool.and_eq_true] at hparts
  exact hparts.1.2

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

/-! The conditional inputs after the actual START witnesses are precisely the
effective filtered parse, the existing acceptance check, and the offered UP
record's joint queue/mass and service-span bounds. -/
theorem continuing_collection_accepted_finish_domains
    (x : RoundInput p rate) (payload : Payload rate) (l : Ledger rate)
    (saved : Option (Fin p.T × Bool))
    (hReady : ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain
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
        (l1.cutoffRegisters a = none ↔ CoordinatorCollectionLedger.armPending l1 a)) ∧
      prepared.observeCoordinator =
        ReferenceActivePhysicalStep.collectionFinish (x := x) payload snap.clockStarted o
          (ReferenceActivePhysicalStep.receiveUp prepared l1) ∧
      prepared.observeCoordinator.recording = some o ∧
      prepared.observeCoordinator.up =
        (ReferenceActivePhysicalStep.receiveUp prepared l1).diagnostic ∧
      let i := ReferenceActivePhysicalStep.upSenderIndex x
      let σ := l.sigma
      let u := l.cutoff
      let g := l.freezeAt
      let v := x.time.val + 1
      let C := 4 * rate.n
      let a := l1.assignment.arm i
      let hindices : (u - 1) + (v - u) ≤ p.T := by
        rcases hReady with ⟨_, _, _, _, _, _, _, _, _, _, _, hcursorReady,
          hcutCursorReady, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
        dsimp [u, v] at hcursorReady hcutCursorReady ⊢
        omega
      let indices := CoordinatorCollectionLedger.calendarIndices p.T
        (u - 1) (v - u) hindices
      let current := (decide (sourceRound x.time < g),
        CoordinatorCollectionLedger.bufferedArrival l1 a x.time)
      let receptionInput := ReferenceUpReception.receptionInputAtRow rate x.row
        (ReferenceActivePhysicalStep.upInputs prepared l1) x.time
      CoordinatorUpReception.receptionInputDomain receptionInput ∧
      CoordinatorUpReception.receptionInputCheck receptionInput = true ∧
      receptionInput.upDecoderBank = x.state.upDecoderBank ∧
      ∀ (M : OrdinaryMessageCodec.UpRecord
        (CoordinatorCollectionLedger.codecParams p rate.eta.val)),
        ReferenceCollectionSegmentExtraction.effectiveParse x l1 = some M →
        CoordinatorCollectionLedger.acceptUpCheck l1 i M = true →
        M.val.S + M.val.q ≤ (l.cutoff - l.sigma) * D p →
        M.val.S ≤ C * (l.cutoff - l.sigma) →
        ∃ past : List (Bool × ℕ),
        ∃ currentRecord : Bool × ℕ,
          l1.currentRegisters a = none ∧ l1.cutoffRegisters a = none ∧
          CoordinatorCollectionLedger.replayRecords? l1 a indices = some past ∧
          CoordinatorCollectionLedger.replayRecords? l1 a [x.time] =
            some [currentRecord] ∧
          past = indices.map (fun r =>
            (decide (sourceRound r < g),
              CoordinatorCollectionLedger.bufferedArrival l1 a r)) ∧
          currentRecord = current ∧
          let records := past ++ [currentRecord]
          records.length = v - u + 1 ∧
          (∀ r ∈ records, r.2 ≤ D p) ∧ C ≤ D p ∧
          (∀ h, h ≤ records.length →
            let Rh := QueueReplay.replay C (0, M.val.q) (records.take h)
            M.val.S + Rh.1 + Rh.2 ≤ (u - σ + h) * D p ∧
            Rh.1 ≤ C * (min (u + h) g - u) ∧
            Rh.1 ≤ p.T * D p ∧ Rh.2 ≤ p.T * D p ∧
            (0 < h → Rh.1 -
              (QueueReplay.replay C (0, M.val.q)
                (records.take (h - 1))).1 ≤ C)) ∧
          (∀ j : Fin records.length,
            (records.get j).1 = decide (u + j.val < g)) ∧
          CoordinatorCollectionLedger.replayOutputDomainsCheck
            (p := p) C M.val.q records = true ∧
          M.val.S + (QueueReplay.replay C (0, M.val.q) records).1 ≤
            C * (min (v + 1) g - σ) ∧
          ∃ l2 : Ledger rate, ∃ bank : CoordinatorUpReception.UpDecoderBank p,
            l2 = CoordinatorCollectionLedger.acceptUpCandidate
              l1 i M past currentRecord ∧
            CoordinatorCollectionLedger.validLedgerCheck l2 = true ∧
            CoordinatorCollectionLedger.decodeUp l1 i (some M) = .success l2 ∧
            (ReferenceActivePhysicalStep.receiveUp prepared l1).result =
              .success (l2, bank) ∧
            bank = CoordinatorUpReception.decoderBankAfter receptionInput ∧
            (CoordinatorUpReception.decoderTransition receptionInput).2 =
              ReferenceActivePhysicalStep.upExpected prepared ∧
            CoordinatorUpReception.parseDecoderOutput
              (CoordinatorUpReception.decoderTransition receptionInput).2 = some M ∧
            (ReferenceActivePhysicalStep.receiveUp prepared l1).diagnostic =
              some {
                input := receptionInput
                expected := ReferenceActivePhysicalStep.upExpected prepared
                decoderAfter :=
                  (CoordinatorUpReception.decoderTransition receptionInput).1
                raw := (CoordinatorUpReception.decoderTransition receptionInput).2
                parsed := ReferenceUpReception.rawParsedOutput rate receptionInput
                locallyAccepted :=
                  ReferenceUpReception.rawParsedLocalAcceptance rate receptionInput
                rawMatches := decide ((CoordinatorUpReception.decoderTransition
                  receptionInput).2 = ReferenceActivePhysicalStep.upExpected prepared)
                wrongUniqueAccepted :=
                  ReferenceUpReception.wrongUniqueAndLocalAcceptanceAtRow
                    rate x.row (ReferenceActivePhysicalStep.upInputs prepared l1) x.time
                    (prepared.followers.followers i)
                    (prepared.follower_alignment _).1
                    (prepared.follower_alignment _).2.1
                    (prepared.follower_alignment _).2.2.1 rfl } ∧
            let R := QueueReplay.replay C (0, M.val.q) records
            l2.phase = .decoded ∧ l2.pending = l.pending.erase i ∧
            l2.sigma = l.sigma ∧ l2.cutoff = l.cutoff ∧ l2.cursor = v ∧
            l2.freezeAt = l.freezeAt ∧ l2.assignment = l.assignment ∧
            l2.baseScore = l.baseScore ∧
            l2.cutoffRegisters a = some ⟨M.val.S, M.val.q, M.val.delta⟩ ∧
            l2.currentRegisters a = some ⟨R.2, R.1 -
              (QueueReplay.replay C (0, M.val.q)
                (records.take (records.length - 1))).1⟩ ∧
            l2.increment a = R.1 ∧ l2.gammaLoc a = 0 ∧
            (∀ b, l2.gammaLoc b = l1.gammaLoc b) ∧
            l2.rawBuffer a = (fun _ => none) ∧
            (∀ b, b ≠ a →
              l2.currentRegisters b = l1.currentRegisters b ∧
              l2.cutoffRegisters b = l1.cutoffRegisters b ∧
              l2.increment b = l1.increment b ∧
              l2.rawBuffer b = l1.rawBuffer b) ∧
            (∀ b, (l2.currentRegisters b = none ↔
                CoordinatorCollectionLedger.armPending l2 b) ∧
              (l2.cutoffRegisters b = none ↔
                CoordinatorCollectionLedger.armPending l2 b)) ∧
            (∀ b, CoordinatorCollectionLedger.armPending l2 b →
              l2.increment b = 0 ∧ l2.gammaLoc b = 0) ∧
            (∀ b c, l2.cutoffRegisters b = some c →
              c.score + c.queue ≤ (u - σ) * D p) ∧
            (∀ b c q, l2.cutoffRegisters b = some c →
              l2.currentRegisters b = some q →
              c.score + l2.increment b + l2.gammaLoc b + q.queue ≤
                (v + 1 - σ) * D p ∧
              c.score + l2.increment b + l2.gammaLoc b ≤
                C * (min (v + 1) g - σ)) ∧
            (∀ b r amount, l2.rawBuffer b r = some amount →
              0 < amount ∧ amount ≤ D p ∧ u ≤ sourceRound r ∧
              sourceRound r ≤ l2.cursor ∧ sourceRound r < l2.freezeAt ∧
              CoordinatorCollectionLedger.armPending l2 b) ∧
            (∀ r, l2.enabledHistory r =
              if u ≤ sourceRound r ∧ sourceRound r ≤ v then
                some (decide (sourceRound r < g)) else none) ∧
            CoordinatorUpReception.decoderBankWellFormed p bank ∧
            (x.state.upDecoderBank i).pending.length + 1 =
              AffineBatchDecoder.quota p ∧
            (bank i).pending = [] ∧
            (∃ batch, batch ∈ (bank i).completed ∧
              batch.length = AffineBatchDecoder.quota p) ∧
            (CoordinatorUpReception.decoderTransition receptionInput).1 =
              ⟨[], (x.state.upDecoderBank i).completed ++
                [(x.state.upDecoderBank i).pending ++
                  [AffineBatchDecoder.entry p
                    (CoordinatorUpReception.traceAt receptionInput)
                    receptionInput.time]]⟩ ∧
            (∀ j, j ≠ i → bank j = x.state.upDecoderBank j) ∧
            (∀ j, j ∉ l2.pending → (bank j).pending = []) ∧
          ∃ finished : Ledger rate,
            CoordinatorCollectionLedger.finishRound l2 = .success finished ∧
            finished = CoordinatorCollectionLedger.finishRoundCandidate l2 ∧
            CoordinatorCollectionLedger.validLedgerCheck finished = true ∧
            finished.increment = (fun b => l2.increment b + l2.gammaLoc b) ∧
            finished.gammaLoc = (fun _ => 0) ∧
            finished.cursor = v + 1 ∧
            finished.phase = CoordinatorCollectionLedger.Phase.ready ∧
            finished.pending = l.pending.erase i ∧
            finished.sigma = l.sigma ∧ finished.cutoff = l.cutoff ∧
            finished.freezeAt = l.freezeAt ∧
            finished.assignment = l.assignment ∧ finished.baseScore = l.baseScore ∧
            finished.cutoffRegisters = l2.cutoffRegisters ∧
            finished.currentRegisters = l2.currentRegisters ∧
            finished.rawBuffer = l2.rawBuffer ∧
            finished.enabledHistory = l2.enabledHistory ∧
            finished.increment a = R.1 ∧
            (∀ b, b ≠ a →
              finished.increment b = l1.increment b + l1.gammaLoc b) ∧
            (∀ b, finished.gammaLoc b = 0) ∧
            (∀ b, (finished.currentRegisters b = none ↔
                CoordinatorCollectionLedger.armPending finished b) ∧
              (finished.cutoffRegisters b = none ↔
                CoordinatorCollectionLedger.armPending finished b)) ∧
            (∀ b c, finished.cutoffRegisters b = some c →
              c.score + c.queue ≤ (u - σ) * D p) ∧
            (∀ b c q, finished.cutoffRegisters b = some c →
              finished.currentRegisters b = some q →
              c.score + finished.increment b + q.queue ≤
                (v + 1 - σ) * D p ∧
              c.score + finished.increment b ≤
                C * (min (v + 1) g - σ)) ∧
            (∀ b r amount, finished.rawBuffer b r = some amount →
              0 < amount ∧ amount ≤ D p ∧ u ≤ sourceRound r ∧
              sourceRound r < min finished.cursor finished.freezeAt ∧
              CoordinatorCollectionLedger.armPending finished b) ∧
            (∀ r, finished.enabledHistory r =
              if u ≤ sourceRound r ∧ sourceRound r < finished.cursor then
                some (decide (sourceRound r < finished.freezeAt)) else none) ∧
            let clockFinished :=
              { clock := snap.clockStarted.clock
                pending := finished.pending
                ledgerCommand := some (.accumulateLocalServiceAt x.time) }
            CoordinatorPhaseClock.finishRound p rate.eta.val x.time
              snap.clockStarted.clock finished.pending x.row = .ok clockFinished ∧
            clockFinished.clock = snap.clockStarted.clock ∧
            clockFinished.pending = finished.pending ∧
            clockFinished.ledgerCommand = some (.accumulateLocalServiceAt x.time) ∧
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
              ReferenceActivePhysicalStep.collectionFinish (x := x) payload
                snap.clockStarted o (ReferenceActivePhysicalStep.receiveUp prepared l1) ∧
            (ReferenceActivePhysicalStep.step x).next.coordinator =
              .collection payload finished actualLastProposal ∧
            (ReferenceActivePhysicalStep.step x).next.upDecoderBank = bank ∧
            (ReferenceActivePhysicalStep.step x).next.activations = x.state.activations ∧
            (∀ j, (ReferenceActivePhysicalStep.step x).followers j =
              prepared.observeFollower j) ∧
            (ReferenceActivePhysicalStep.step x).ownEntries =
              prepared.feedback.ownEntries ∧
            ((l.pending.erase i).Nonempty →
              ((v < p.T → ∃ xNext : RoundInput p rate,
                xNext.state = (ReferenceActivePhysicalStep.step x).next ∧
                xNext.rows = x.rows ∧ xNext.selected = x.selected ∧
                xNext.rewards = x.rewards ∧ xNext.time.val = v ∧
                ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain
                  xNext payload finished actualLastProposal) ∧
               (v = p.T →
                ReferenceContinuingCollectionRejectedFinishDomains.continuingCollectionReadyBoundaryDomain
                    (ReferenceActivePhysicalStep.step x).next payload finished
                    actualLastProposal))) ∧
          (l.pending.erase i = ∅ →
              (∀ b, ∃ q, finished.currentRegisters b = some q ∧
                ∃ c, finished.cutoffRegisters b = some c)) := by
  classical
  have hReadyCopy := hReady
  rcases hReady with ⟨hstate, hphaseReady, hσpos, hσT, hσcut, hσpayload,
    hcutPos, hcutT, hcutFreeze, hfreezeT, hgrid, hcursor, hcutCursor,
    hcursorT, hassignment, hbaseZero, hanchor, hn, hpending, hregisters,
    hgammaZero, hcutDomain, hpaired, hcap, hrawReady, hhistoryReady, hbank⟩
  obtain ⟨cutoff, hcutoff, core, snap, hb, hs, hcoord, harm, hlocal,
    hrecordInputs, o, l1, hrecord, hstart, hl1Candidate, hvalid, hphase,
    hcursor1, hσ1, hcut1, hfreeze1, hpending1, hassignment1, hbase1,
    hcutRegisters1, hincrement1, hcurrentUpdate, hstartMass, hfreezeCurrent,
    hrawNone, hregisters1, hknownStart, hcurrent1, hcutDomain1, hzero1,
    hgamma1, hcutMass1, hraw1, hhistory1, hrawBuffer1, hrawFrame1, hfresh,
    hfuture, hobserve, hrecording, hdiagnostic, hdomain, hinputCheck, hbankInput,
    hmessages⟩ :=
      ReferenceContinuingCollectionAcceptedDecodeDomains.continuing_collection_accepted_decode_domains
        x payload l saved hReadyCopy
  let clock := ReferenceActivePhysicalStep.collectionClock payload l saved cutoff
  let input := ReferenceActivePhysicalStep.collectionInput x payload l clock cutoff
  let prepared := ReferenceActivePhysicalStep.prepare x
  let weights := CoordinatorCollectionInteractive.PreObservationInputs.weights input
    snap.inputsValid.ledger_valid snap.inputsValid.assignment_eq
  let recordingInput := ReferenceActivePhysicalStep.collectionRecordingInput prepared
    payload snap.clockStarted weights
  let raw := CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder o
  let i := ReferenceActivePhysicalStep.upSenderIndex x
  let σ := l.sigma
  let u := l.cutoff
  let g := l.freezeAt
  let v := x.time.val + 1
  let C := 4 * rate.n
  let a := l1.assignment.arm i
  have hindices : (u - 1) + (v - u) ≤ p.T := by
    have hu : l.cutoff ≤ x.time.val + 1 := by
      have hle : l.cutoff ≤ l.cursor := Nat.le_of_lt hcutCursor
      calc
        l.cutoff ≤ l.cursor := hle
        _ = x.time.val + 1 := hcursor
    have hv : x.time.val < p.T := x.time.isLt
    dsimp [u, v]
    omega
  let indices := CoordinatorCollectionLedger.calendarIndices p.T (u - 1)
    (v - u) hindices
  let current := (decide (sourceRound x.time < g),
    CoordinatorCollectionLedger.bufferedArrival l1 a x.time)
  let receptionInput := ReferenceUpReception.receptionInputAtRow rate x.row
    (ReferenceActivePhysicalStep.upInputs prepared l1) x.time
  refine ⟨cutoff, hcutoff, core, snap, hb, hs, hcoord, harm, hlocal,
    hrecordInputs, o, l1, hrecord, hstart, hl1Candidate, hvalid, hphase,
    hcursor1, hσ1, hcut1, hfreeze1, hpending1, hassignment1, hbase1,
    hcutRegisters1, hincrement1,
    fun a => ⟨(hregisters1 a).1, (hregisters1 a).2.1⟩,
    hobserve, hrecording, hdiagnostic,
    hdomain, hinputCheck, hbankInput, ?_⟩
  intro M hparse haccept hmessageMass hmessageSpan
  obtain ⟨past, currentRecord, hcurrentNone, hcutoffNone, hPastSome,
    hCurrentSome, hpastMap,
    hcurrentEq, hrecordsLength, harrivals, hfourN, hprefix, hbits,
    hreplayCheck, hendpointScore, l2, bank,
    hacceptedCandidate, hdecodedValid,
    hdecoded, hreceiveResult, hbankAfter, hrawEq, hparseActual, hdiagnosticM,
    hphaseAfter, hpendingAfter, hσAfter, hcutAfter, hcursorAfter, hfreezeAfter,
    hassignmentAfter, hbaseAfter, hcutRecovered, hcurrentRecovered,
    hincrementRecovered, hgammaRecovered, hgammaFrame, hrawCleared, hframe,
    hregistersAfter, hzeroPendingAfter, hcutoffMassAfter, hknownMassAfter,
    hrawSupportAfter, hhistoryAfter, hbankWellFormed, hquota, hselectedClear,
    hselectedBatch, htransitionSelected, hbankUnselected, hbankEmptyOutside⟩ :=
      hmessages M hparse haccept hmessageMass hmessageSpan
  let records := past ++ [currentRecord]
  let R := QueueReplay.replay C (0, M.val.q) records
  have hcurrentPending2 : ∀ b,
      (l2.currentRegisters b = none ↔ CoordinatorCollectionLedger.armPending l2 b) :=
    fun b => (hregistersAfter b).1
  have hcutoffPending2 : ∀ b,
      (l2.cutoffRegisters b = none ↔ CoordinatorCollectionLedger.armPending l2 b) :=
    fun b => (hregistersAfter b).2
  have hpendingZero2 : ∀ b, CoordinatorCollectionLedger.armPending l2 b →
      l2.increment b = 0 ∧ l2.gammaLoc b = 0 := hzeroPendingAfter
  have hregisterDomains :=
    registerDomainsCheck_of_validLedgerCheck l2 hdecodedValid
  have hregisterChecks := hregisterDomains
  unfold CoordinatorCollectionLedger.registerDomainsCheck at hregisterChecks
  have hparts1 := Bool.and_eq_true_iff.mp hregisterChecks
  have hparts2 := Bool.and_eq_true_iff.mp hparts1.1
  have hparts3 := Bool.and_eq_true_iff.mp hparts2.1
  have hparts4 := Bool.and_eq_true_iff.mp hparts3.1
  have hcurrentChecks := hparts4.1
  have hcutoffChecks := hparts4.2
  have hbaseChecks := hparts3.2
  have hincrementChecks := hparts2.2
  have hgammaChecks := hparts1.2
  have hcurrentDomain2 : ∀ b q, l2.currentRegisters b = some q →
      q.queue ≤ p.T * D p ∧ q.lastService ≤ D p := by
    intro b q hq
    have hcheck := (allFin_eq_true_iff _).mp hcurrentChecks b
    rw [hq] at hcheck
    rcases Bool.and_eq_true_iff.mp hcheck with ⟨hqueue, hservice⟩
    exact ⟨of_decide_eq_true hqueue, of_decide_eq_true hservice⟩
  have hcutoffDomain2 : ∀ b c, l2.cutoffRegisters b = some c →
      c.score ≤ p.T * D p ∧ c.queue ≤ p.T * D p ∧ c.lastService ≤ D p := by
    intro b c hc
    have hcheck := (allFin_eq_true_iff _).mp hcutoffChecks b
    rw [hc] at hcheck
    have hsplit := Bool.and_eq_true_iff.mp hcheck
    have hscoreQueue := Bool.and_eq_true_iff.mp hsplit.1
    have hscore := hscoreQueue.1
    have hqueue := hscoreQueue.2
    have hservice := hsplit.2
    exact ⟨of_decide_eq_true hscore, of_decide_eq_true hqueue,
      of_decide_eq_true hservice⟩
  have hbaseDomain2 : ∀ j, l2.baseScore j ≤ p.T * D p := by
    intro j
    have hcheck := (allFin_eq_true_iff _).mp hbaseChecks j
    exact of_decide_eq_true hcheck
  have hincrementDomain2 : ∀ b,
      l2.increment b + l2.gammaLoc b ≤ p.T * D p := by
    intro b
    by_cases hpending : CoordinatorCollectionLedger.armPending l2 b
    · rcases hpendingZero2 b hpending with ⟨hinc, hgamma⟩
      rw [hinc, hgamma]
      exact Nat.zero_le _
    · have hcurrentSome : l2.currentRegisters b ≠ none := by
        intro hnone
        exact hpending ((hcurrentPending2 b).mp hnone)
      have hcutoffSome : l2.cutoffRegisters b ≠ none := by
        intro hnone
        exact hpending ((hcutoffPending2 b).mp hnone)
      obtain ⟨q, hq⟩ : ∃ q, l2.currentRegisters b = some q := by
        cases hq : l2.currentRegisters b with
        | none => exact False.elim (hcurrentSome hq)
        | some q => exact ⟨q, rfl⟩
      obtain ⟨c, hc⟩ : ∃ c, l2.cutoffRegisters b = some c := by
        cases hc : l2.cutoffRegisters b with
        | none => exact False.elim (hcutoffSome hc)
        | some c => exact ⟨c, rfl⟩
      have hmass := hknownMassAfter b c q hc hq
      have htimeBound : v + 1 - σ ≤ p.T := by
        dsimp [v, σ]
        omega
      have hscaled := Nat.mul_le_mul_right (D p) htimeBound
      have hdrop : l2.increment b + l2.gammaLoc b ≤
          c.score + l2.increment b + l2.gammaLoc b + q.queue := by omega
      exact hdrop.trans (Nat.le_trans hmass.1 hscaled)
  have hraw2 : ∀ b r amount, l2.rawBuffer b r = some amount →
      0 < amount ∧ amount ≤ D p ∧ l2.cutoff ≤ sourceRound r ∧
      sourceRound r < min (l2.cursor + 1) l2.freezeAt ∧
      CoordinatorCollectionLedger.armPending l2 b := by
    intro b r amount hcell
    rcases hrawSupportAfter b r amount hcell with
      ⟨hpos, hbound, hcutRaw, hcursorRaw, hfreezeRaw, hpendingRaw⟩
    have hspan : sourceRound r < min (l2.cursor + 1) l2.freezeAt := by
      apply Nat.lt_min.mpr
      constructor
      · have hle : sourceRound r ≤ l2.cursor := by
          simpa [hcursorAfter, v] using hcursorRaw
        exact Nat.lt_succ_of_le hle
      · exact hfreezeRaw
    exact ⟨hpos, hbound, by simpa [hcutAfter] using hcutRaw,
      hspan, hpendingRaw⟩
  have hhistory2 : ∀ r, l2.enabledHistory r =
      if l2.cutoff ≤ sourceRound r ∧ sourceRound r ≤ l2.cursor then
        some (decide (sourceRound r < l2.freezeAt)) else none := by
    intro r
    simpa [hcutAfter, hcursorAfter, hfreezeAfter, u, v, g,
      sourceRound, ReferenceContinuingCollectionStartDomains.sourceRound,
      CoordinatorCollectionLedger.sourceRound] using hhistoryAfter r
  have hcutoffAtTime : l.cutoff ≤ sourceRound x.time := by
    have hlt : l.cutoff < sourceRound x.time := by
      simpa [sourceRound, ReferenceContinuingCollectionStartDomains.sourceRound,
        CoordinatorCollectionLedger.sourceRound, hcursor] using hcutCursor
    exact Nat.le_of_lt hlt
  have hfinishCandidateValid := finishCandidate_valid l2
    (by simpa [hσAfter] using hσpos)
    (by simpa [hσAfter] using hσT)
    (by simpa [hcutAfter] using hcutPos)
    (by simpa [hcutAfter, hfreezeAfter] using hcutFreeze)
    (by simpa [hcutAfter] using hcutT)
    (by simpa [hfreezeAfter] using hfreezeT)
    (by simpa [hcutAfter, hcursorAfter, sourceRound,
      ReferenceContinuingCollectionStartDomains.sourceRound,
      CoordinatorCollectionLedger.sourceRound, v] using hcutoffAtTime)
    (by
      have htime : x.time.val + 1 ≤ p.T := Nat.succ_le_of_lt x.time.isLt
      rw [hcursorAfter]
      omega)
    hcurrentPending2 hcutoffPending2 hpendingZero2 hcurrentDomain2
    hcutoffDomain2 hbaseDomain2 hincrementDomain2 hraw2 hhistory2
  let finished := CoordinatorCollectionLedger.finishRoundCandidate l2
  have hfinishInput : CoordinatorCollectionLedger.validLedgerCheck l2 = true ∧
      l2.phase = CoordinatorCollectionLedger.Phase.decoded ∧ l2.cursor ≤ p.T := by
    refine ⟨hdecodedValid, hphaseAfter, ?_⟩
    rw [hcursorAfter]
    exact Nat.succ_le_of_lt x.time.isLt
  have hfinish : CoordinatorCollectionLedger.finishRound l2 = .success finished := by
    unfold CoordinatorCollectionLedger.finishRound
    simp [hfinishInput, hfinishCandidateValid, finished]
  have hfinishedIncrement : finished.increment = fun b => l2.increment b + l2.gammaLoc b := by
    funext b
    simp [finished, CoordinatorCollectionLedger.finishRoundCandidate]
  have hfinishedGamma : finished.gammaLoc = fun _ => 0 := by
    funext b
    rfl
  have hfinishedCursor : finished.cursor = v + 1 := by
    change l2.cursor + 1 = v + 1
    rw [hcursorAfter]
  have hfinishedPhase : finished.phase = CoordinatorCollectionLedger.Phase.ready := rfl
  have hfinishedPending : finished.pending = l.pending.erase i := by
    simpa [finished, CoordinatorCollectionLedger.finishRoundCandidate] using hpendingAfter
  have hfinishedSigma : finished.sigma = l.sigma := by
    simpa [finished, CoordinatorCollectionLedger.finishRoundCandidate] using hσAfter
  have hfinishedCutoff : finished.cutoff = l.cutoff := by
    simpa [finished, CoordinatorCollectionLedger.finishRoundCandidate] using hcutAfter
  have hfinishedFreeze : finished.freezeAt = l.freezeAt := by
    simpa [finished, CoordinatorCollectionLedger.finishRoundCandidate] using hfreezeAfter
  have hfinishedAssignment : finished.assignment = l.assignment := by
    simpa [finished, CoordinatorCollectionLedger.finishRoundCandidate] using hassignmentAfter
  have hfinishedBase : finished.baseScore = l.baseScore := by
    simpa [finished, CoordinatorCollectionLedger.finishRoundCandidate] using hbaseAfter
  have hfinishedCutoffRegisters : finished.cutoffRegisters = l2.cutoffRegisters := rfl
  have hfinishedCurrent : finished.currentRegisters = l2.currentRegisters := rfl
  have hfinishedRaw : finished.rawBuffer = l2.rawBuffer := rfl
  have hfinishedHistory : finished.enabledHistory = l2.enabledHistory := rfl
  have hfinishedAtRecoveredArm : finished.increment a = R.1 := by
    change l2.increment a + l2.gammaLoc a = R.1
    have hinc : l2.increment a = R.1 := by
      simpa [R] using hincrementRecovered
    have hgam : l2.gammaLoc a = 0 := hgammaRecovered
    calc
      _ = R.1 + 0 := by rw [hinc, hgam]
      _ = R.1 := Nat.add_zero _
  have hfinishedOtherIncrement : ∀ b, b ≠ a →
      finished.increment b = l1.increment b + l1.gammaLoc b := by
    intro b hba
    have hfields := hframe b hba
    change l2.increment b + l2.gammaLoc b = l1.increment b + l1.gammaLoc b
    rw [hfields.2.2.1, hgammaFrame b]
  have hfinishedGammaZero : ∀ b, finished.gammaLoc b = 0 := by
    intro b
    simp [hfinishedGamma]
  have hfinishedArmEq : ∀ b,
      CoordinatorCollectionLedger.armPending finished b ↔
        CoordinatorCollectionLedger.armPending l2 b := by
    intro b
    constructor
    · rintro ⟨j, hj, harm⟩
      exact ⟨j, by simpa [finished, CoordinatorCollectionLedger.finishRoundCandidate] using hj,
        by simpa [finished, CoordinatorCollectionLedger.finishRoundCandidate] using harm⟩
    · rintro ⟨j, hj, harm⟩
      exact ⟨j, by simpa [finished, CoordinatorCollectionLedger.finishRoundCandidate] using hj,
        by simpa [finished, CoordinatorCollectionLedger.finishRoundCandidate] using harm⟩
  have hfinishedRegisters : ∀ b,
      (finished.currentRegisters b = none ↔
        CoordinatorCollectionLedger.armPending finished b) ∧
      (finished.cutoffRegisters b = none ↔
        CoordinatorCollectionLedger.armPending finished b) := by
    intro b
    exact ⟨Iff.trans (hcurrentPending2 b) (hfinishedArmEq b).symm,
      Iff.trans (hcutoffPending2 b) (hfinishedArmEq b).symm⟩
  have hfinishedCutoffMass : ∀ b c, finished.cutoffRegisters b = some c →
      c.score + c.queue ≤ (u - σ) * D p := by
    intro b c hc
    exact hcutoffMassAfter b c (by simpa [hfinishedCutoffRegisters] using hc)
  have hfinishedMass : ∀ b c q, finished.cutoffRegisters b = some c →
      finished.currentRegisters b = some q →
      c.score + finished.increment b + q.queue ≤ (v + 1 - σ) * D p ∧
      c.score + finished.increment b ≤ C * (min (v + 1) g - σ) := by
    intro b c q hc hq
    have hc2 : l2.cutoffRegisters b = some c := by
      simpa [hfinishedCutoffRegisters] using hc
    have hq2 : l2.currentRegisters b = some q := by
      simpa [hfinishedCurrent] using hq
    have hbudget := hknownMassAfter b c q hc2 hq2
    simpa [hfinishedIncrement, v, σ, C, Nat.add_assoc, Nat.add_left_comm,
      Nat.add_comm] using hbudget
  have hfinishedRawSupport : ∀ b r amount,
      finished.rawBuffer b r = some amount →
      0 < amount ∧ amount ≤ D p ∧ u ≤ sourceRound r ∧
      sourceRound r < min finished.cursor finished.freezeAt ∧
      CoordinatorCollectionLedger.armPending finished b := by
    intro b r amount hcell
    have hcell2 : l2.rawBuffer b r = some amount := by
      simpa [hfinishedRaw] using hcell
    rcases hrawSupportAfter b r amount hcell2 with
      ⟨hpos, hbound, hcutRaw, hcursorRaw, hfreezeRaw, hpendingRaw⟩
    have hcursor : sourceRound r < finished.cursor := by
      have hle : sourceRound r ≤ v := by
        change sourceRound r ≤ l2.cursor at hcursorRaw
        rw [hcursorAfter] at hcursorRaw
        exact hcursorRaw
      rw [hfinishedCursor]
      exact Nat.lt_succ_of_le hle
    have hfreeze : sourceRound r < finished.freezeAt := by
      simpa [hfinishedFreeze, hfreezeAfter] using hfreezeRaw
    exact ⟨hpos, hbound, hcutRaw, Nat.lt_min.mpr ⟨hcursor, hfreeze⟩,
      (hfinishedArmEq b).2 hpendingRaw⟩
  have hfinishedHistoryEq : ∀ r, finished.enabledHistory r =
      if u ≤ sourceRound r ∧ sourceRound r < finished.cursor then
        some (decide (sourceRound r < finished.freezeAt)) else none := by
    intro r
    have hcursorIff : sourceRound r < v + 1 ↔ sourceRound r ≤ v := by omega
    simpa [hfinishedHistory, hfinishedCursor, hfinishedFreeze,
      hcutAfter, hcursorAfter, hfreezeAfter, u, v, g, hcursorIff] using
        hhistoryAfter r
  have hvalidFinished :
      CoordinatorCollectionLedger.validLedgerCheck finished = true := by
    simpa [finished] using hfinishCandidateValid
  let clockFinished : CoordinatorPhaseClock.FinishRoundResult p := {
    clock := snap.clockStarted.clock
    pending := finished.pending
    ledgerCommand := some (.accumulateLocalServiceAt x.time) }
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
    rw [hreceiveResult]
    simp [hfinish, hclockFinished, actualLastProposal, clockFinished]
  have hobserveFinish : prepared.observeCoordinator =
      ReferenceActivePhysicalStep.collectionFinish (x := x) payload snap.clockStarted o
        (ReferenceActivePhysicalStep.receiveUp prepared l1) := hobserve
  have hstepFields := ReferenceActivePhysicalStep.step_next_fields x
  have hstepCoordinator : (ReferenceActivePhysicalStep.step x).next.coordinator =
      .collection payload finished actualLastProposal := by
    simpa [ReferenceActivePhysicalStep.step, hfinishObservation] using
      congrArg ReferenceActivePhysicalStep.CoordinatorObservation.configuration hobserveFinish
  have hstepObserve : (ReferenceActivePhysicalStep.step x).coordinator =
      ReferenceActivePhysicalStep.collectionFinish (x := x) payload
        snap.clockStarted o (ReferenceActivePhysicalStep.receiveUp prepared l1) := by
    calc
      (ReferenceActivePhysicalStep.step x).coordinator = prepared.observeCoordinator := rfl
      _ = ReferenceActivePhysicalStep.collectionFinish (x := x) payload
          snap.clockStarted o (ReferenceActivePhysicalStep.receiveUp prepared l1) := hobserveFinish
  have hstepBank : (ReferenceActivePhysicalStep.step x).next.upDecoderBank = bank := by
    calc
      (ReferenceActivePhysicalStep.step x).next.upDecoderBank =
          prepared.observeCoordinator.upDecoderBank := hstepFields.2.1
      _ = bank := by simp [hobserveFinish, hfinishObservation]
  have hstepActivations :
      (ReferenceActivePhysicalStep.step x).next.activations = x.state.activations :=
    hstepFields.2.2.1
  have hstepFollowers : ∀ j,
      (ReferenceActivePhysicalStep.step x).followers j = prepared.observeFollower j := by
    intro j
    rfl
  have hstepOwnEntries : (ReferenceActivePhysicalStep.step x).ownEntries =
      prepared.feedback.ownEntries := rfl
  have hbankReady : ∀ j : Fin (p.m - 1),
      (bank j).pending.length < AffineBatchDecoder.quota p ∧
      (∀ batch, batch ∈ (bank j).completed →
        batch.length = AffineBatchDecoder.quota p) ∧
      (j ∉ finished.pending → (bank j).pending = []) := by
    intro j
    have hwf := hbankWellFormed j
    refine ⟨hwf.1, hwf.2, ?_⟩
    intro hout
    have hnot : j ∉ l2.pending := by
      rw [hpendingAfter, ← hfinishedPending]
      exact hout
    exact hbankEmptyOutside j hnot
  have hnextBankReady : ∀ j : Fin (p.m - 1),
      ((ReferenceActivePhysicalStep.step x).next.upDecoderBank j).pending.length <
        AffineBatchDecoder.quota p ∧
      (∀ batch, batch ∈ ((ReferenceActivePhysicalStep.step x).next.upDecoderBank j).completed →
        batch.length = AffineBatchDecoder.quota p) ∧
      (j ∉ finished.pending →
        ((ReferenceActivePhysicalStep.step x).next.upDecoderBank j).pending = []) := by
    intro j
    simpa [hstepBank] using hbankReady j
  have hnextInput : (l.pending.erase i).Nonempty → v < p.T →
      ∃ xNext : RoundInput p rate,
        xNext.state = (ReferenceActivePhysicalStep.step x).next ∧
        xNext.rows = x.rows ∧ xNext.selected = x.selected ∧
        xNext.rewards = x.rewards ∧ xNext.time.val = v ∧
        ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain
          xNext payload finished actualLastProposal := by
    intro hpendingNext hvT
    let nextTime : Fin p.T := ⟨v, hvT⟩
    let xNext : RoundInput p rate := {
      state := (ReferenceActivePhysicalStep.step x).next
      rows := x.rows
      selected := x.selected
      time := nextTime
      active := by
        intro j
        rw [hstepActivations]
        have hj := x.active j
        dsimp [nextTime, v]
        omega
      rewards := x.rewards }
    refine ⟨xNext, rfl, rfl, rfl, rfl, ?_, ?_⟩
    · rfl
    · refine ⟨?_, hfinishedPhase,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        hanchor, hn, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hnextBankReady⟩
      · simpa [xNext] using hstepCoordinator
      · simpa [hfinishedSigma] using hσpos
      · simpa [hfinishedSigma] using hσT
      · simpa [hfinishedSigma, hfinishedCutoff] using hσcut
      · simpa [hfinishedSigma] using hσpayload
      · simpa [hfinishedCutoff] using hcutPos
      · simpa [hfinishedCutoff] using hcutT
      · simpa [hfinishedCutoff, hfinishedFreeze] using hcutFreeze
      · simpa [hfinishedFreeze] using hfreezeT
      · simpa [hfinishedFreeze] using hgrid
      · simpa [xNext, nextTime, v, sourceRound,
          ReferenceContinuingCollectionStartDomains.sourceRound] using hfinishedCursor
      · rw [hfinishedCutoff, hfinishedCursor]
        have hcutBefore : l.cutoff < sourceRound x.time := by
          simpa [hcursor] using hcutCursor
        dsimp [sourceRound, ReferenceContinuingCollectionStartDomains.sourceRound] at hcutBefore ⊢
        omega
      · rw [hfinishedCursor]
        omega
      · simpa [hfinishedAssignment] using hassignment
      · simpa [hfinishedBase] using hbaseZero
      · rw [hfinishedPending]
        exact hpendingNext
      · intro b
        exact hfinishedRegisters b
      · intro b
        constructor
        · exact hfinishedGammaZero b
        · intro hbPending
          have hbPending2 : CoordinatorCollectionLedger.armPending l2 b :=
            (hfinishedArmEq b).mp hbPending
          have hzero := hzeroPendingAfter b hbPending2
          rw [hfinishedIncrement]
          simp [hzero.1, hzero.2]
      · intro b c hc
        have hc2 : l2.cutoffRegisters b = some c := by
          simpa [hfinishedCutoffRegisters] using hc
        have hdomain := hcutoffDomain2 b c hc2
        refine ⟨?_, hdomain.2.2⟩
        simpa [u, σ, hfinishedCutoff, hfinishedSigma] using
          hcutoffMassAfter b c hc2
      · intro b c q hc hq
        have hc2 : l2.cutoffRegisters b = some c := by
          simpa [hfinishedCutoffRegisters] using hc
        have hq2 : l2.currentRegisters b = some q := by
          simpa [hfinishedCurrent] using hq
        refine ⟨(hcurrentDomain2 b q hq2).2, ?_⟩
        simpa [hfinishedCursor, hfinishedFreeze, hfinishedSigma] using
          (hfinishedMass b c q hc hq).1
      · intro b c q hc hq
        simpa [hfinishedCursor, hfinishedFreeze, hfinishedSigma] using
          (hfinishedMass b c q hc hq).2
      · intro b r amount hcell
        simpa [hfinishedCutoff, hfinishedCursor, hfinishedFreeze,
          hfinishedRaw] using hfinishedRawSupport b r amount hcell
      · intro r
        simpa [hfinishedCutoff, hfinishedCursor, hfinishedFreeze,
          hfinishedHistory] using hfinishedHistoryEq r
  have hboundary : (l.pending.erase i).Nonempty → v = p.T →
      ReferenceContinuingCollectionRejectedFinishDomains.continuingCollectionReadyBoundaryDomain
        (ReferenceActivePhysicalStep.step x).next payload finished actualLastProposal := by
    intro hpendingNext hvT
    refine ⟨hstepCoordinator, hfinishedPhase,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      hanchor, hn, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hnextBankReady⟩
    · simpa [hfinishedSigma] using hσpos
    · simpa [hfinishedSigma] using hσT
    · simpa [hfinishedSigma, hfinishedCutoff] using hσcut
    · simpa [hfinishedSigma] using hσpayload
    · simpa [hfinishedCutoff] using hcutPos
    · simpa [hfinishedCutoff] using hcutT
    · simpa [hfinishedCutoff, hfinishedFreeze] using hcutFreeze
    · simpa [hfinishedFreeze] using hfreezeT
    · simpa [hfinishedFreeze] using hgrid
    · simp [hfinishedCursor, hvT]
    · rw [hfinishedCutoff, hfinishedCursor]
      have hcutBefore : l.cutoff < sourceRound x.time := by
        simpa [hcursor] using hcutCursor
      dsimp [sourceRound, ReferenceContinuingCollectionStartDomains.sourceRound] at hcutBefore ⊢
      omega
    · simp [hfinishedCursor, hvT]
    · simpa [hfinishedAssignment] using hassignment
    · simpa [hfinishedBase] using hbaseZero
    · rw [hfinishedPending]
      exact hpendingNext
    · intro b
      exact hfinishedRegisters b
    · intro b
      constructor
      · exact hfinishedGammaZero b
      · intro hbPending
        have hbPending2 : CoordinatorCollectionLedger.armPending l2 b :=
          (hfinishedArmEq b).mp hbPending
        have hzero := hzeroPendingAfter b hbPending2
        rw [hfinishedIncrement]
        simp [hzero.1, hzero.2]
    · intro b c hc
      have hc2 : l2.cutoffRegisters b = some c := by
        simpa [hfinishedCutoffRegisters] using hc
      have hdomain := hcutoffDomain2 b c hc2
      refine ⟨?_, hdomain.2.2⟩
      simpa [u, σ, hfinishedCutoff, hfinishedSigma] using
        hcutoffMassAfter b c hc2
    · intro b c q hc hq
      have hq2 : l2.currentRegisters b = some q := by
        simpa [hfinishedCurrent] using hq
      refine ⟨(hcurrentDomain2 b q hq2).2, ?_⟩
      simpa [hfinishedCursor, hfinishedFreeze, hfinishedSigma] using
        (hfinishedMass b c q hc hq).1
    · intro b c q hc hq
      simpa [hfinishedCursor, hfinishedFreeze, hfinishedSigma] using
        (hfinishedMass b c q hc hq).2
    · intro b r amount hcell
      simpa [hfinishedCutoff, hfinishedCursor, hfinishedFreeze,
        hfinishedRaw] using hfinishedRawSupport b r amount hcell
    · intro r
      simpa [hfinishedCutoff, hfinishedCursor, hfinishedFreeze,
        hfinishedHistory] using hfinishedHistoryEq r
  have hknownRegisters : l.pending.erase i = ∅ →
      ∀ b, ∃ q, finished.currentRegisters b = some q ∧
        ∃ c, finished.cutoffRegisters b = some c := by
    intro hempty b
    have hnotPending : ¬ CoordinatorCollectionLedger.armPending l2 b := by
      intro hmem
      rcases hmem with ⟨j, hj, hassign⟩
      have hjErase : j ∈ l.pending.erase i := by
        simpa [hpendingAfter] using hj
      simp [hempty] at hjErase
    have hcurrentNotNone : l2.currentRegisters b ≠ none := by
      intro hnone
      exact hnotPending ((hregistersAfter b).1.mp hnone)
    have hcutoffNotNone : l2.cutoffRegisters b ≠ none := by
      intro hnone
      exact hnotPending ((hregistersAfter b).2.mp hnone)
    obtain ⟨q, hq⟩ : ∃ q, l2.currentRegisters b = some q := by
      cases hq : l2.currentRegisters b with
      | none => exact False.elim (hcurrentNotNone hq)
      | some q => exact ⟨q, rfl⟩
    obtain ⟨c, hc⟩ : ∃ c, l2.cutoffRegisters b = some c := by
      cases hc : l2.cutoffRegisters b with
      | none => exact False.elim (hcutoffNotNone hc)
      | some c => exact ⟨c, rfl⟩
    exact ⟨q, by simpa [hfinishedCurrent] using hq, c,
      by simpa [hfinishedCutoffRegisters] using hc⟩
  refine ⟨past, currentRecord, hcurrentNone, hcutoffNone, hPastSome,
    hCurrentSome, hpastMap, hcurrentEq, hrecordsLength, harrivals, hfourN,
    hprefix, hbits, hreplayCheck, hendpointScore, l2, bank, hacceptedCandidate,
    hdecodedValid, hdecoded, hreceiveResult, hbankAfter, hrawEq, hparseActual,
    hdiagnosticM, hphaseAfter, hpendingAfter, hσAfter, hcutAfter, hcursorAfter,
    hfreezeAfter, hassignmentAfter, hbaseAfter, hcutRecovered, hcurrentRecovered,
    hincrementRecovered, hgammaRecovered, hgammaFrame, hrawCleared, hframe,
    hregistersAfter, hzeroPendingAfter, hcutoffMassAfter, hknownMassAfter,
    hrawSupportAfter, hhistoryAfter, hbankWellFormed, hquota, hselectedClear,
    hselectedBatch, htransitionSelected, hbankUnselected, hbankEmptyOutside,
    finished, hfinish, rfl, hvalidFinished, hfinishedIncrement, hfinishedGamma,
    hfinishedCursor, hfinishedPhase, hfinishedPending, hfinishedSigma,
    hfinishedCutoff, hfinishedFreeze, hfinishedAssignment, hfinishedBase,
    hfinishedCutoffRegisters, hfinishedCurrent, hfinishedRaw, hfinishedHistory,
    hfinishedAtRecoveredArm, hfinishedOtherIncrement, hfinishedGammaZero,
    hfinishedRegisters, hfinishedCutoffMass, hfinishedMass, hfinishedRawSupport,
    hfinishedHistoryEq, hclockFinished, rfl, rfl, rfl,
    hlastProposal, hfinishObservation, hobserveFinish, hstepObserve,
    hstepCoordinator, hstepBank, hstepActivations, hstepFollowers,
    hstepOwnEntries, ?_, ?_⟩
  · intro hpending
    refine ⟨?_, ?_⟩
    · intro hvT
      exact hnextInput hpending hvT
    · intro hvT
      exact hboundary hpending hvT
  · exact hknownRegisters

end Bandits.Support.ReferenceContinuingCollectionAcceptedFinishDomains

end
