/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceContinuingCollectionRejectedFinishDomains

import Lean.Elab.Tactic.Omega

/-!
# Continuing collection accepted-UP replay domains

This module proves the local stored-calendar replay and accepted decode step
after the actual continuing-collection START producer. Its only induction
condition is `ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain`;
the accepted record budgets remain explicit conditional inputs. No collection
finish, later ready state, physical queue identity, or manuscript theorem is
claimed here. The future actual admission consumer must discharge the two
budgets from `ReferenceFirstCollectionOfferedSenderReplay.run_first_collection_offered_sender_replay`
and `ReplayWeightStability.replay_score_envelope` at the same offered word and cutoff.

Source evidence: `sources/zip4/manuscript/06_interruptions.tex:9-100,164-177,246-295`,
`sources/zip4/manuscript/04_slow_fast_learner.tex:157-174`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-64`.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions

namespace Bandits.Support.ReferenceContinuingCollectionAcceptedDecodeDomains

abbrev Parameters := ReferenceContinuingCollectionRejectedFinishDomains.Parameters
abbrev RateInput := ReferenceContinuingCollectionRejectedFinishDomains.RateInput
abbrev State := ReferenceContinuingCollectionRejectedFinishDomains.State
abbrev RoundInput := ReferenceContinuingCollectionRejectedFinishDomains.RoundInput
abbrev Payload {p : Parameters} (rate : RateInput p) :=
  ReferenceContinuingCollectionRejectedFinishDomains.Payload rate
abbrev Ledger {p : Parameters} (rate : RateInput p) :=
  ReferenceContinuingCollectionRejectedFinishDomains.Ledger rate
abbrev sourceRound {p : Parameters} (r : Fin p.T) :=
  ReferenceContinuingCollectionRejectedFinishDomains.sourceRound r

variable {p : Parameters} {rate : RateInput p}

private theorem armPendingCheck_eq_true_iff
    (l : Ledger rate) (a : Fin p.K) :
    CoordinatorCollectionLedger.armPendingCheck l a = true ↔
      CoordinatorCollectionLedger.armPending l a := by
  unfold CoordinatorCollectionLedger.armPendingCheck
  unfold CoordinatorCollectionLedger.anyFin
  rw [List.any_eq_true]
  simp [CoordinatorCollectionLedger.armPending]

private theorem allFin_option_isNone_eq_pendingCheck
    (l : Ledger rate) {α : Type*} (registers : Fin p.K → Option α)
    (hregisters : ∀ a, registers a = none ↔
      CoordinatorCollectionLedger.armPending l a) :
    CoordinatorCollectionLedger.allFin p.K (fun a =>
      (registers a).isNone == CoordinatorCollectionLedger.armPendingCheck l a) = true := by
  apply (ReferenceFirstCutoffRecordedService.allFin_eq_true_iff _).2
  intro a
  by_cases hp : CoordinatorCollectionLedger.armPending l a
  · have hnone : registers a = none := (hregisters a).mpr hp
    have hcheck : CoordinatorCollectionLedger.armPendingCheck l a = true :=
      (armPendingCheck_eq_true_iff l a).2 hp
    simp [hnone, hcheck]
  · have hnotNone : registers a ≠ none := by
      intro hnone
      exact hp ((hregisters a).mp hnone)
    have hcheck : CoordinatorCollectionLedger.armPendingCheck l a = false := by
      cases h : CoordinatorCollectionLedger.armPendingCheck l a with
      | false => rfl
      | true => exact False.elim (hp ((armPendingCheck_eq_true_iff l a).mp h))
    cases hreg : registers a with
    | none => exact False.elim (hnotNone hreg)
    | some value => simp [hcheck]

private theorem allFin_pending_field_zero
    (l : Ledger rate) (field : Fin p.K → ℕ)
    (hzero : ∀ a, CoordinatorCollectionLedger.armPending l a → field a = 0) :
    CoordinatorCollectionLedger.allFin p.K (fun a =>
      (!CoordinatorCollectionLedger.armPendingCheck l a) || decide (field a = 0)) = true := by
  apply (ReferenceFirstCutoffRecordedService.allFin_eq_true_iff _).2
  intro a
  by_cases hp : CoordinatorCollectionLedger.armPending l a
  · have hcheck : CoordinatorCollectionLedger.armPendingCheck l a = true :=
      (armPendingCheck_eq_true_iff l a).2 hp
    simp [hcheck, hzero a hp]
  · have hcheck : CoordinatorCollectionLedger.armPendingCheck l a = false := by
      cases h : CoordinatorCollectionLedger.armPendingCheck l a with
      | false => rfl
      | true => exact False.elim (hp ((armPendingCheck_eq_true_iff l a).mp h))
    simp [hcheck]

private theorem replayRecords?_eq_some_map
    (l : Ledger rate) (a : Fin p.K) (indices : List (Fin p.T))
    (enabled : Fin p.T → Bool)
    (henabled : ∀ r ∈ indices, l.enabledHistory r = some (enabled r)) :
    CoordinatorCollectionLedger.replayRecords? l a indices =
      some (indices.map fun r =>
        (enabled r && decide (sourceRound r < l.freezeAt),
          CoordinatorCollectionLedger.bufferedArrival l a r)) := by
  induction indices with
  | nil => rfl
  | cons r rest ih =>
      have hr := henabled r (by simp)
      have hrest : ∀ s ∈ rest, l.enabledHistory s = some (enabled s) := by
        intro s hs
        exact henabled s (by simp [hs])
      simp [CoordinatorCollectionLedger.replayRecords?, hr, ih hrest, sourceRound,
        ReferenceContinuingCollectionRejectedFinishDomains.sourceRound,
        CoordinatorCollectionLedger.sourceRound,
        ReferenceContinuingCollectionStartDomains.sourceRound]
      rfl

private theorem transition_mass_le (capacity score backlog arrival : ℕ)
    (flag : Bool) :
    (QueueReplay.transition capacity (score, backlog) (flag, arrival)).1 +
        (QueueReplay.transition capacity (score, backlog) (flag, arrival)).2 ≤
      score + backlog + arrival := by
  cases flag with
  | false => simp [QueueReplay.transition]
  | true =>
      change (score + min capacity (backlog + arrival)) +
          (backlog + arrival - min capacity (backlog + arrival)) ≤
        score + backlog + arrival
      have hservice : min capacity (backlog + arrival) ≤ backlog + arrival :=
        Nat.min_le_right _ _
      have hcancel := Nat.sub_add_cancel hservice
      omega

private theorem replay_mass_bound (capacity initialScore initialBacklog D : ℕ)
    (records : List (Bool × ℕ))
    (harrival : ∀ record ∈ records, record.2 ≤ D) :
    let endpoint := QueueReplay.replay capacity (initialScore, initialBacklog) records
    endpoint.1 + endpoint.2 ≤ initialScore + initialBacklog + records.length * D := by
  induction records generalizing initialScore initialBacklog with
  | nil => simp [QueueReplay.replay]
  | cons record rest ih =>
      have hhead := harrival record (by simp)
      have htail : ∀ next ∈ rest, next.2 ≤ D := by
        intro next hnext
        exact harrival next (by simp [hnext])
      let advanced := QueueReplay.transition capacity
        (initialScore, initialBacklog) record
      have hstep : advanced.1 + advanced.2 ≤
          initialScore + initialBacklog + record.2 := by
        cases record with
        | mk flag arrival =>
            simpa [advanced] using transition_mass_le capacity
              initialScore initialBacklog arrival flag
      have hrest := ih advanced.1 advanced.2 htail
      change (QueueReplay.replay capacity advanced rest).1 +
          (QueueReplay.replay capacity advanced rest).2 ≤ _
      calc
        _ ≤ advanced.1 + advanced.2 + rest.length * D := hrest
        _ ≤ initialScore + initialBacklog + record.2 + rest.length * D :=
          Nat.add_le_add_right hstep _
        _ ≤ initialScore + initialBacklog + D + rest.length * D := by omega
        _ = initialScore + initialBacklog + (rest.length + 1) * D := by
          rw [Nat.add_mul]
          simp
          omega

private theorem replay_prefix_score_span (capacity initialQueue u freezeAt : ℕ)
    (records : List (Bool × ℕ))
    (hbit : ∀ j : Fin records.length,
      (records.get j).1 = decide (u + j.val < freezeAt)) :
    ∀ h, h ≤ records.length →
      (QueueReplay.replay capacity (0, initialQueue) (records.take h)).1 ≤
        capacity * (min (u + h) freezeAt - u) := by
  intro h
  induction h with
  | zero =>
      intro _
      simp [QueueReplay.replay]
  | succ h ih =>
      intro hbound
      have hlt : h < records.length := by omega
      have htake0 := List.take_succ_drop (l := records) (n := h) (stop := 0)
        (by simpa using hlt)
      simp only [List.drop_zero, Nat.zero_add] at htake0
      rw [htake0, QueueReplay.replay_append]
      let previous := QueueReplay.replay capacity (0, initialQueue) (records.take h)
      have hprevious := ih (by omega)
      have hbit' : (records.get ⟨h, hlt⟩).1 = decide (u + h < freezeAt) :=
        hbit ⟨h, hlt⟩
      by_cases hbefore : u + h < freezeAt
      · have hstep := ReplayWeightStability.transition_score_envelope capacity
          previous.1 previous.2 (records.get ⟨h, hlt⟩)
        have hminOld : min (u + h) freezeAt = u + h := Nat.min_eq_left (by omega)
        have hminNew : min (u + (h + 1)) freezeAt = u + (h + 1) :=
          Nat.min_eq_left (by omega)
        change (QueueReplay.transition capacity previous
          (records.get ⟨h, hlt⟩)).1 ≤ _
        calc
          _ ≤ previous.1 + capacity := hstep.2
          _ ≤ capacity * h + capacity := by
            rw [hminOld] at hprevious
            simpa [Nat.mul_comm] using Nat.add_le_add_right hprevious capacity
          _ = capacity * (h + 1) := by rw [Nat.mul_succ]
          _ = capacity * (min (u + (h + 1)) freezeAt - u) := by
            rw [hminNew]
            congr 1
            omega
      · have hfalse : (records.get ⟨h, hlt⟩).1 = false := by
          simpa [hbefore] using hbit'
        have hminOld : min (u + h) freezeAt = freezeAt :=
          Nat.min_eq_right (by omega)
        have hminNew : min (u + (h + 1)) freezeAt = freezeAt :=
          Nat.min_eq_right (by omega)
        have htrans : QueueReplay.transition capacity previous
            (records.get ⟨h, hlt⟩) = previous := by
          simp only [QueueReplay.transition, hfalse, Bool.false_eq_true, ite_false]
        change (QueueReplay.transition capacity previous
          (records.get ⟨h, hlt⟩)).1 ≤ _
        rw [htrans]
        rw [hminOld] at hprevious
        rw [hminNew]
        exact hprevious

private theorem replay_prefix_last_service_le (capacity initialQueue : ℕ)
    (records : List (Bool × ℕ)) :
    ∀ h, h ≤ records.length → 0 < h →
      let endpoint := QueueReplay.replay capacity (0, initialQueue) (records.take h)
      let previous := QueueReplay.replay capacity (0, initialQueue)
        (records.take (h - 1))
      endpoint.1 - previous.1 ≤ capacity := by
  intro h hbound hpositive
  have hprevlt : h - 1 < records.length := by omega
  have htake0 := List.take_succ_drop (l := records) (n := h - 1) (stop := 0)
    (by simpa using hprevlt)
  simp only [List.drop_zero, Nat.zero_add] at htake0
  have hsucc : (h - 1) + 1 = h := by omega
  rw [← hsucc, htake0, QueueReplay.replay_append]
  let previous := QueueReplay.replay capacity (0, initialQueue)
    (records.take (h - 1))
  have hstep := ReplayWeightStability.transition_score_envelope capacity
    previous.1 previous.2 records[h - 1]
  change (QueueReplay.transition capacity (previous.1, previous.2)
    records[h - 1]).1 - previous.1 ≤ capacity
  omega

private theorem calendarIndices_source_at
    (start length : ℕ) (hbound : start + length ≤ p.T) (j : Fin length) :
    sourceRound ((CoordinatorCollectionLedger.calendarIndices p.T start length hbound).get
      ⟨j.val, by simp [CoordinatorCollectionLedger.calendarIndices]⟩) = start + j.val + 1 := by
  simp [CoordinatorCollectionLedger.calendarIndices, sourceRound,
    ReferenceContinuingCollectionRejectedFinishDomains.sourceRound,
    ReferenceContinuingCollectionStartDomains.sourceRound]

private theorem calendarIndices_source_bounds
    (start length : ℕ) (hbound : start + length ≤ p.T)
    (r : Fin p.T)
    (hr : r ∈ CoordinatorCollectionLedger.calendarIndices p.T start length hbound) :
    start + 1 ≤ sourceRound r ∧ sourceRound r < start + length + 1 := by
  rw [CoordinatorCollectionLedger.calendarIndices] at hr
  obtain ⟨j, hj⟩ := List.mem_ofFn.mp hr
  have hval : r.val = start + j.val := by
    have := congrArg Fin.val hj
    simpa using this.symm
  constructor <;>
    dsimp [sourceRound, ReferenceContinuingCollectionRejectedFinishDomains.sourceRound,
      ReferenceContinuingCollectionStartDomains.sourceRound,
      CoordinatorCollectionLedger.sourceRound] <;> omega

private theorem ready_cutoff_before_time
    (x : RoundInput p rate) (payload : Payload rate) (l : Ledger rate)
    (saved : Option (Fin p.T × Bool))
    (h : ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain
      x payload l saved) :
    l.cutoff ≤ x.time.val + 1 := by
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, hcursor, hcutCursor, _⟩
  rw [hcursor] at hcutCursor
  omega

/-- One conditional accepted-UP step from an actual continuing START. The
started ledger and recorder are produced by `continuing_collection_start_domains`;
the only message-side assumptions are the literal effective parse, the
existing acceptance check, and the two offered-replay scalar budgets. -/
theorem continuing_collection_accepted_decode_domains
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
      prepared.observeCoordinator.up = (ReferenceActivePhysicalStep.receiveUp prepared l1).diagnostic ∧
      let i := ReferenceActivePhysicalStep.upSenderIndex x
      let σ := l.sigma
      let u := l.cutoff
      let g := l.freezeAt
      let v := x.time.val + 1
      let C := 4 * rate.n
      let a := l1.assignment.arm i
      let hindices : (u - 1) + (v - u) ≤ p.T := by
        have hu : l.cutoff ≤ x.time.val + 1 :=
          ready_cutoff_before_time x payload l saved hReady
        dsimp [u, v]
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
              (QueueReplay.replay C (0, M.val.q) (records.take (h - 1))).1 ≤ C)) ∧
          (∀ j : Fin records.length,
            (records.get j).1 = decide (u + j.val < g)) ∧
          CoordinatorCollectionLedger.replayOutputDomainsCheck (p := p) C M.val.q records = true ∧
          M.val.S +
            (QueueReplay.replay C (0, M.val.q) records).1 ≤
              C * (min (v + 1) g - σ) ∧
          ∃ l2 : Ledger rate, ∃ bank : CoordinatorUpReception.UpDecoderBank p,
            l2 = CoordinatorCollectionLedger.acceptUpCandidate l1 i M past currentRecord ∧
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
                decoderAfter := (CoordinatorUpReception.decoderTransition receptionInput).1
                raw := (CoordinatorUpReception.decoderTransition receptionInput).2
                parsed := ReferenceUpReception.rawParsedOutput rate receptionInput
                locallyAccepted := ReferenceUpReception.rawParsedLocalAcceptance rate receptionInput
                rawMatches := decide ((CoordinatorUpReception.decoderTransition receptionInput).2 =
                  ReferenceActivePhysicalStep.upExpected prepared)
                wrongUniqueAccepted := ReferenceUpReception.wrongUniqueAndLocalAcceptanceAtRow
                  rate x.row (ReferenceActivePhysicalStep.upInputs prepared l1) x.time
                  (prepared.followers.followers i)
                  (prepared.follower_alignment _).1
                  (prepared.follower_alignment _).2.1
                  (prepared.follower_alignment _).2.2.1 rfl } ∧
            let R := QueueReplay.replay C (0, M.val.q) records
            l2.phase = .decoded ∧ l2.pending = l.pending.erase i ∧
            l2.sigma = l.sigma ∧ l2.cutoff = l.cutoff ∧
            l2.cursor = v ∧ l2.freezeAt = l.freezeAt ∧
            l2.assignment = l.assignment ∧ l2.baseScore = l.baseScore ∧
            l2.cutoffRegisters a = some ⟨M.val.S, M.val.q, M.val.delta⟩ ∧
            l2.currentRegisters a = some ⟨R.2, R.1 -
              (QueueReplay.replay C (0, M.val.q) (records.take (records.length - 1))).1⟩ ∧
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
            (x.state.upDecoderBank i).pending.length + 1 = AffineBatchDecoder.quota p ∧
            (bank i).pending = [] ∧
            (∃ batch, batch ∈ (bank i).completed ∧
              batch.length = AffineBatchDecoder.quota p) ∧
            (CoordinatorUpReception.decoderTransition receptionInput).1 =
              ⟨[], (x.state.upDecoderBank i).completed ++
                [(x.state.upDecoderBank i).pending ++
                  [AffineBatchDecoder.entry p
                    (CoordinatorUpReception.traceAt receptionInput) receptionInput.time]]⟩ ∧
            (∀ j, j ≠ i → bank j = x.state.upDecoderBank j) ∧
            (∀ j, j ∉ l2.pending → (bank j).pending = []) := by
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
    hrawNone, hregisters1, hknownStart, hcurrent1, hcutDomain1, hzero1, hgamma1,
    hcutMass1, hraw1, hhistory1, hrawBuffer1, hrawFrame1, hfresh, hfuture,
    hobserve, hrecording, hdiagnostic⟩ :=
      ReferenceContinuingCollectionStartDomains.continuing_collection_start_domains
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
    have hu : l.cutoff ≤ x.time.val + 1 := ready_cutoff_before_time
      x payload l saved hReadyCopy
    have hv : x.time.val < p.T := x.time.isLt
    dsimp [u, v]
    omega
  let indices := CoordinatorCollectionLedger.calendarIndices p.T (u - 1) (v - u) hindices
  let current := (decide (sourceRound x.time < g),
    CoordinatorCollectionLedger.bufferedArrival l1 a x.time)
  let receptionInput := ReferenceUpReception.receptionInputAtRow rate x.row
    (ReferenceActivePhysicalStep.upInputs prepared l1) x.time
  have hbankCheck : CoordinatorUpReception.decoderBankCheck p
      x.state.upDecoderBank = true := by
    apply (CoordinatorUpReception.decoderBankCheck_eq_true_iff p _).2
    intro j
    exact ⟨hbank j |>.1, (hbank j).2.1⟩
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
      have hcutTime : l.cutoff < x.time.val + 1 := by
        rw [← hcursor]
        exact hcutCursor
      change l.cutoff ≤ x.time.val + 1
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
  refine ⟨cutoff, hcutoff, core, snap, hb, hs, ?_⟩
  refine ⟨hcoord, harm, hlocal, hrecordInputs, o, l1, hrecord, ?_⟩
  refine ⟨hstart, hl1Candidate, hvalid, hphase, hcursor1, hσ1, hcut1,
    hfreeze1, hpending1, hassignment1, hbase1, hcutRegisters1, hincrement1,
    hcurrentUpdate, hstartMass, hfreezeCurrent, hrawNone, hregisters1,
    hknownStart, hcurrent1, hcutDomain1, hzero1, hgamma1, hcutMass1, hraw1,
    hhistory1, hrawBuffer1, hrawFrame1, hfresh, hfuture, hobserve, hrecording,
    hdiagnostic, ?_⟩
  refine ⟨hdomain, hinputCheck, rfl, ?_⟩
  intro M hparse haccept hmessageMass hmessageSpan
  have hacceptFields :=
    (CoordinatorCollectionLedger.acceptUpCheck_iff l1 i M).mp haccept
  have hiPending : i ∈ l1.pending :=
    (CoordinatorCollectionLedger.pendingNaturalLabels_mem_iff l1 i).mp
      hacceptFields.2.1
  have hmessageSigma : M.val.sigma = l1.sigma := hacceptFields.2.2
  have hassignedPending : CoordinatorCollectionLedger.armPending l1 a :=
    ⟨i, hiPending, rfl⟩
  have hunknown : l1.currentRegisters a = none ∧ l1.cutoffRegisters a = none :=
    ⟨(hregisters1 a).1.mpr hassignedPending,
      (hregisters1 a).2.1.mpr hassignedPending⟩
  have hgammaAssigned : l1.gammaLoc a = 0 := (hzero1 a hassignedPending).2
  have hfourN : C ≤ D p := ActiveFollowerDownAcceptance.four_n_le_D p rate
  have hMnotPlaceholder : M.val ≠ OrdinaryMessageCodec.upPlaceholder := by
    intro hplaceholder
    have hsigma := congrArg OrdinaryMessageCodec.UpFields.sigma hplaceholder
    rw [hmessageSigma, hσ1] at hsigma
    simp [OrdinaryMessageCodec.upPlaceholder] at hsigma
    omega
  obtain ⟨hMscore, hMdelta, hMqueue⟩ :
      M.val.S ≤ p.T * D p ∧ M.val.delta ≤ D p ∧ M.val.q ≤ p.T * D p := by
    rcases M.property with hplaceholder | hfields
    · exact False.elim (hMnotPlaceholder hplaceholder)
    · rcases hfields with ⟨_, _, hscore, hdelta, hqueue⟩
      exact ⟨hscore, hdelta, hqueue⟩
  have hsourceCurrent : sourceRound x.time = v := rfl
  have hEnabledIndices : ∀ r ∈ indices,
      l1.enabledHistory r = some (decide (sourceRound r < g)) := by
    intro r hr
    have hrange := calendarIndices_source_bounds (p := p) (u - 1) (v - u)
      hindices r hr
    have hrange' : u ≤ sourceRound r ∧ sourceRound r < v := by
      dsimp [u, v] at hrange ⊢
      omega
    have hinterval : l.cutoff ≤ sourceRound r ∧
        sourceRound r ≤ sourceRound x.time := by
      constructor
      · simpa [u] using hrange'.1
      · rw [hsourceCurrent]
        exact Nat.le_of_lt hrange'.2
    rw [hhistory1 r]
    simp [hinterval, g, ReferenceContinuingCollectionStartDomains.sourceRound]
  have hcurrentEnabled :
      l1.enabledHistory x.time = some (decide (sourceRound x.time < g)) := by
    have hcutTime : l.cutoff ≤ sourceRound x.time := by
      change l.cutoff ≤ x.time.val + 1
      rw [← hcursor]
      exact Nat.le_of_lt hcutCursor
    have hinterval : l.cutoff ≤ sourceRound x.time ∧
        sourceRound x.time ≤ sourceRound x.time := ⟨hcutTime, le_rfl⟩
    rw [hhistory1 x.time]
    simp [hinterval, g, ReferenceContinuingCollectionStartDomains.sourceRound]
  have hbuffered : ∀ r, l.cutoff ≤ sourceRound r →
      sourceRound r ≤ v →
      CoordinatorCollectionLedger.bufferedArrival l1 a r ≤ D p := by
    intro r hcutRound htimeRound
    cases hrawCell : l1.rawBuffer a r with
    | none => simp [CoordinatorCollectionLedger.bufferedArrival, hrawCell]
    | some amount =>
        have hrawDomain := hraw1 a r amount hrawCell
        simpa [CoordinatorCollectionLedger.bufferedArrival, hrawCell] using
          hrawDomain.2.1
  let past : List (Bool × ℕ) := indices.map fun r =>
    (decide (sourceRound r < g),
      CoordinatorCollectionLedger.bufferedArrival l1 a r)
  have hPastSome : CoordinatorCollectionLedger.replayRecords? l1 a indices = some past := by
    have h := replayRecords?_eq_some_map l1 a indices
      (fun r => decide (sourceRound r < g)) hEnabledIndices
    simpa [past, g, hfreeze1, Bool.and_self,
      ReferenceContinuingCollectionStartDomains.sourceRound,
      CoordinatorCollectionLedger.sourceRound] using h
  have hCurrentSome : CoordinatorCollectionLedger.replayRecords? l1 a [x.time] =
      some [current] := by
    have h := replayRecords?_eq_some_map l1 a [x.time]
      (fun r => decide (sourceRound r < g)) (by
        intro r hr
        simp only [List.mem_singleton] at hr
        subst r
        exact hcurrentEnabled)
    simpa [current, g, hfreeze1, Bool.and_self,
      ReferenceContinuingCollectionStartDomains.sourceRound,
      CoordinatorCollectionLedger.sourceRound] using h
  have hindicesLength : indices.length = v - u := by
    simp [indices, CoordinatorCollectionLedger.calendarIndices_length]
  have hpastLength : past.length = v - u := by
    simp [past, hindicesLength]
  let records := past ++ [current]
  have hrecordsLength : records.length = v - u + 1 := by
    simp [records, hpastLength]
  have hindexBounds : ∀ r ∈ indices, u ≤ sourceRound r ∧ sourceRound r < v := by
    intro r hr
    have hb := calendarIndices_source_bounds (p := p) (u - 1) (v - u)
      hindices r hr
    dsimp [u, v] at hb ⊢
    omega
  have hcurrentArrival :
      CoordinatorCollectionLedger.bufferedArrival l1 a x.time ≤ D p := by
    apply hbuffered x.time
    · change l.cutoff ≤ x.time.val + 1
      rw [← hcursor]
      exact Nat.le_of_lt hcutCursor
    · rw [hsourceCurrent]
  have hrecordsArrival : ∀ record ∈ records, record.2 ≤ D p := by
    intro record hmem
    rcases List.mem_append.mp hmem with hpastMem | hcurrentMem
    · rcases List.mem_map.mp hpastMem with ⟨r, hr, hrecord⟩
      have hsecond := congrArg Prod.snd hrecord
      rw [← hsecond]
      exact hbuffered r (by simpa [u] using (hindexBounds r hr).1)
        (by simpa [v] using Nat.le_of_lt (hindexBounds r hr).2)
    · simp only [List.mem_singleton] at hcurrentMem
      subst record
      exact hcurrentArrival
  have hbits : ∀ j : Fin records.length,
      (records.get j).1 = decide (u + j.val < g) := by
    intro j
    have hlastIndex : j.val < past.length ∨ j.val = past.length := by
      have hj := j.isLt
      simp only [records, List.length_append, List.length_singleton] at hj
      omega
    rcases hlastIndex with hjpast | hjlast
    · have hjindices : j.val < indices.length := by
        rw [hindicesLength]
        simpa [hpastLength] using hjpast
      have hjcalendar : j.val < v - u := by simpa [hindicesLength] using hjindices
      have huPositive : 1 ≤ u := by dsimp [u]; exact hcutPos
      have hindexValue : (indices[j.val]).val = u - 1 + j.val := by
        simpa [indices, Nat.sub_add_cancel huPositive] using
          calendarIndices_source_at (p := p) (u - 1) (v - u) hindices
            ⟨j.val, hjcalendar⟩
      have hsource : sourceRound indices[j.val] = u + j.val := by
        change (indices[j.val]).val + 1 = u + j.val
        rw [hindexValue]
        omega
      have hgetRecords : records.get j = past.get ⟨j.val, by
          simpa [hpastLength] using hjpast⟩ := by
        simp [records, hjpast]
      rw [hgetRecords]
      simp only [past, List.get_eq_getElem, List.getElem_map]
      rw [hsource]
    · have hfin : j = ⟨past.length, by
          simp [records]⟩ := Fin.ext hjlast
      subst j
      have hsum : u + past.length = v := by
        rw [hpastLength]
        dsimp [u, v]
        omega
      simp [records, current, hsum, hsourceCurrent]
  have huFreeze : u ≤ g := by
    dsimp [u, g]
    exact hcutFreeze
  have htimeSpan : ∀ h, h ≤ records.length → u - σ + h ≤ p.T := by
    intro h hh
    have hvT : v ≤ p.T := by
      dsimp [v]
      omega
    have hsigmapos : 1 ≤ σ := by dsimp [σ]; exact hσpos
    rw [hrecordsLength] at hh
    dsimp [u, σ, v] at *
    omega
  have hprefixMass : ∀ h, h ≤ records.length →
      let Rh := QueueReplay.replay C (0, M.val.q) (records.take h)
      M.val.S + Rh.1 + Rh.2 ≤ (u - σ + h) * D p := by
    intro h hh
    have htakeArrival : ∀ record ∈ records.take h, record.2 ≤ D p := by
      intro record hmem
      apply hrecordsArrival record
      rw [← List.take_append_drop h records]
      exact List.mem_append_left _ hmem
    have hmassReplay := replay_mass_bound C 0 M.val.q (D p) (records.take h)
      htakeArrival
    have htakeLength : (records.take h).length ≤ h := by simp
    have hmul := Nat.mul_le_mul_right (D p) htakeLength
    have hmassReplay' :
        (QueueReplay.replay C (0, M.val.q) (records.take h)).1 +
          (QueueReplay.replay C (0, M.val.q) (records.take h)).2 ≤
        M.val.q + h * D p := by
      calc
        _ ≤ 0 + M.val.q + (records.take h).length * D p := hmassReplay
        _ ≤ M.val.q + h * D p := by
          simpa [Nat.zero_add] using Nat.add_le_add_left hmul M.val.q
    have hcombined : M.val.S +
        (QueueReplay.replay C (0, M.val.q) (records.take h)).1 +
        (QueueReplay.replay C (0, M.val.q) (records.take h)).2 ≤
        (u - σ + h) * D p := by
      calc
        _ ≤ M.val.S + M.val.q + h * D p := by omega
        _ ≤ (u - σ) * D p + h * D p := by
          exact Nat.add_le_add_right hmessageMass _
        _ = (u - σ + h) * D p := by rw [Nat.add_mul]
    exact hcombined
  have hprefixSpan : ∀ h, h ≤ records.length →
      (QueueReplay.replay C (0, M.val.q) (records.take h)).1 ≤
        C * (min (u + h) g - u) :=
    replay_prefix_score_span C M.val.q u g records hbits
  have hprefixService : ∀ h, h ≤ records.length → 0 < h →
      (QueueReplay.replay C (0, M.val.q) (records.take h)).1 -
        (QueueReplay.replay C (0, M.val.q) (records.take (h - 1))).1 ≤ C :=
    replay_prefix_last_service_le C M.val.q records
  have hfullMass := hprefixMass records.length (by omega)
  have hfullSpan := hprefixSpan records.length (by omega)
  have hfullService := hprefixService records.length (by omega) (by omega)
  have hrecordsLengthLe : records.length ≤ p.T := by
    rw [hrecordsLength]
    have hvT : v ≤ p.T := by dsimp [v]; omega
    have hsigmapos : 1 ≤ σ := by dsimp [σ]; exact hσpos
    dsimp [u, σ, v] at *
    omega
  have harrivalAll : records.all (fun record => decide (record.2 ≤ D p)) = true := by
    apply List.all_eq_true.mpr
    intro record hrecord
    exact decide_eq_true (hrecordsArrival record hrecord)
  have hprefixBounds : ∀ h, h ≤ records.length →
      (QueueReplay.replay C (0, M.val.q) (records.take h)).1 ≤ p.T * D p ∧
      (QueueReplay.replay C (0, M.val.q) (records.take h)).2 ≤ p.T * D p := by
    intro h hh
    have hm := hprefixMass h hh
    have ht := Nat.mul_le_mul_right (D p) (htimeSpan h hh)
    constructor <;> omega
  have hfullBounds := hprefixBounds records.length (by omega)
  rw [List.take_length] at hfullBounds
  have hprefixCheck : ∀ h : Fin (records.length + 1),
      CoordinatorCollectionLedger.replayPrefixOutputDomainsCheck (p := p)
        C M.val.q records h = true := by
    intro h
    obtain ⟨hscoreBound, hqueueBound⟩ := hprefixBounds h.val (by omega)
    by_cases hzero : h.val = 0
    · rw [hzero] at hscoreBound hqueueBound
      simp only [CoordinatorCollectionLedger.replayPrefixOutputDomainsCheck, hzero,
        ↓reduceIte, hscoreBound, hqueueBound, decide_true, Bool.and_self]
    · have hservice := hprefixService h.val (by omega) (by omega)
      have hserviceLe :
          (QueueReplay.replay C (0, M.val.q) (records.take h.val)).1 -
            (QueueReplay.replay C (0, M.val.q) (records.take (h.val - 1))).1 ≤ D p :=
        Nat.le_trans hservice hfourN
      simp [CoordinatorCollectionLedger.replayPrefixOutputDomainsCheck,
        hzero, hscoreBound, hqueueBound, hserviceLe]
  have hprefixAll : CoordinatorCollectionLedger.allFin (records.length + 1)
      (fun h => CoordinatorCollectionLedger.replayPrefixOutputDomainsCheck
        (p := p) C M.val.q records h) = true :=
    (ReferenceFirstCutoffRecordedService.allFin_eq_true_iff _).2 hprefixCheck
  have hreplayCheck :
      CoordinatorCollectionLedger.replayOutputDomainsCheck (p := p) C M.val.q records = true := by
    simp [CoordinatorCollectionLedger.replayOutputDomainsCheck,
      hrecordsLengthLe, harrivalAll, hprefixAll]
  have hendpointScore : M.val.S +
      (QueueReplay.replay C (0, M.val.q) records).1 ≤
        C * (min (v + 1) g - σ) := by
    have hscoreStart : M.val.S ≤ C * (u - σ) := by
      simpa [C, u, σ] using hmessageSpan
    have hspanEnd :
        (QueueReplay.replay C (0, M.val.q) records).1 ≤
          C * (min (v + 1) g - u) := by
      have hfullSpan' := hfullSpan
      rw [List.take_length] at hfullSpan'
      rw [hrecordsLength] at hfullSpan'
      have hsum : u + (v - u + 1) = v + 1 := by omega
      rw [hsum] at hfullSpan'
      simpa [records] using hfullSpan'
    have hmin : u - σ + (min (v + 1) g - u) = min (v + 1) g - σ := by
      have hσu : σ ≤ u := by dsimp [σ, u]; exact Nat.le_of_lt hσcut
      have huMin : u ≤ min (v + 1) g := by
        exact le_min (by omega) (by omega)
      omega
    calc
      _ ≤ C * (u - σ) + C * (min (v + 1) g - u) :=
        Nat.add_le_add hscoreStart hspanEnd
      _ = C * ((u - σ) + (min (v + 1) g - u)) := by rw [Nat.mul_add]
      _ = C * (min (v + 1) g - σ) := by rw [hmin]
  let l2 := CoordinatorCollectionLedger.acceptUpCandidate l1 i M past current
  have hgammaAssignedAfter : l2.gammaLoc a = 0 := by
    simpa [l2, CoordinatorCollectionLedger.acceptUpCandidate] using hgammaAssigned
  have hArmAfter : ∀ b,
      CoordinatorCollectionLedger.armPending l2 b ↔
        b ≠ a ∧ CoordinatorCollectionLedger.armPending l1 b := by
    intro b
    change (∃ j, j ∈ l1.pending.erase i ∧ l1.assignment.arm j = b) ↔ _
    constructor
    · rintro ⟨j, hj, hjarm⟩
      rcases Finset.mem_erase.mp hj with ⟨hji, hjpending⟩
      have hbne : b ≠ a := by
        intro hba
        apply hji
        apply l1.assignment.injective
        calc
          l1.assignment.arm j = b := hjarm
          _ = a := hba
          _ = l1.assignment.arm i := rfl
      exact ⟨hbne, ⟨j, hjpending, hjarm⟩⟩
    · rintro ⟨hbne, ⟨j, hjpending, hjarm⟩⟩
      have hji : j ≠ i := by
        intro hji
        subst j
        apply hbne
        simpa [a] using hjarm.symm
      exact ⟨j, Finset.mem_erase.mpr ⟨hji, hjpending⟩, hjarm⟩
  have hacceptedFields := CoordinatorCollectionLedger.acceptUpCandidate_recovered_fields
    l1 i M past current
  have hcutoffRecovered : l2.cutoffRegisters a =
      some ⟨M.val.S, M.val.q, M.val.delta⟩ := by
    have h := hacceptedFields.2.2
    rw [show l1.baseScore i = 0 by rw [hbase1, hbaseZero]] at h
    simpa [l2, a] using h
  have hrecordsPrev : records.take (records.length - 1) = past := by
    simp [records, hpastLength]
  have hcurrentRecovered : l2.currentRegisters a =
      some ⟨(QueueReplay.replay C (0, M.val.q) records).2,
        (QueueReplay.replay C (0, M.val.q) records).1 -
          (QueueReplay.replay C (0, M.val.q)
            (records.take (records.length - 1))).1⟩ := by
    have h := hacceptedFields.1
    simpa [l2, a, C, records, hrecordsPrev] using h
  have hincrementRecovered : l2.increment a =
      (QueueReplay.replay C (0, M.val.q) records).1 := by
    have h := hacceptedFields.2.1
    simpa [l2, a, C, records] using h
  have hpendingAfter : l2.pending = l.pending.erase i := by
    simp [l2, CoordinatorCollectionLedger.acceptUpCandidate, hpending1]
  have hphaseAfter : l2.phase = CoordinatorCollectionLedger.Phase.decoded := by
    rfl
  have hframeAfter : ∀ b, b ≠ a →
      l2.currentRegisters b = l1.currentRegisters b ∧
      l2.cutoffRegisters b = l1.cutoffRegisters b ∧
      l2.increment b = l1.increment b := by
    intro b hba
    simp only [l2, CoordinatorCollectionLedger.acceptUpCandidate,
      Function.update_of_ne (show b ≠ l1.assignment.arm i from hba), and_self]
  have hregistersAfter : ∀ b,
      (l2.currentRegisters b = none ↔
        CoordinatorCollectionLedger.armPending l2 b) ∧
      (l2.cutoffRegisters b = none ↔
        CoordinatorCollectionLedger.armPending l2 b) := by
    intro b
    by_cases hba : b = a
    · subst b
      have hnotArm : ¬ CoordinatorCollectionLedger.armPending l2 a := by
        intro hp
        exact (hArmAfter a).mp hp |>.1 rfl
      simp only [hcurrentRecovered, hcutoffRecovered, Option.some_ne_none, false_iff]
      exact ⟨hnotArm, hnotArm⟩
    · have hArmEq : CoordinatorCollectionLedger.armPending l2 b ↔
          CoordinatorCollectionLedger.armPending l1 b := by
        rw [hArmAfter b]
        simp [hba]
      obtain ⟨hcurrentEq, hcutoffEq, _⟩ := hframeAfter b hba
      constructor
      · rw [hcurrentEq, hArmEq]
        exact (hregisters1 b).1
      · rw [hcutoffEq, hArmEq]
        exact (hregisters1 b).2.1
  have hzeroPendingAfter : ∀ b,
      CoordinatorCollectionLedger.armPending l2 b →
        l2.increment b = 0 ∧ l2.gammaLoc b = 0 := by
    intro b hb
    have hbne := (hArmAfter b).mp hb |>.1
    have hbOld := (hArmAfter b).mp hb |>.2
    have hzeroOld := hzero1 b hbOld
    have hincEq := (hframeAfter b hbne).2.2
    have hgammaEq : l2.gammaLoc b = l1.gammaLoc b := rfl
    exact ⟨hincEq.trans hzeroOld.1, hgammaEq.trans hzeroOld.2⟩
  have hcurrentDomainAfter : ∀ b q, l2.currentRegisters b = some q →
      q.queue ≤ p.T * D p ∧ q.lastService ≤ D p := by
    intro b q hq
    by_cases hba : b = a
    · subst b
      have hqEq : q = ⟨(QueueReplay.replay C (0, M.val.q) records).2,
          (QueueReplay.replay C (0, M.val.q) records).1 -
            (QueueReplay.replay C (0, M.val.q)
              (records.take (records.length - 1))).1⟩ := by
        exact (Option.some.inj (hcurrentRecovered.symm.trans hq)).symm
      subst q
      constructor
      · exact hfullBounds.2
      · have hserviceFull := hfullService
        rw [List.take_length] at hserviceFull
        exact Nat.le_trans hserviceFull hfourN
    · have hqOld : l1.currentRegisters b = some q := by
        exact (hframeAfter b hba).1.symm.trans hq
      exact hcurrent1 b q hqOld
  have hcutoffDomainAfter : ∀ b c, l2.cutoffRegisters b = some c →
      c.score ≤ p.T * D p ∧ c.queue ≤ p.T * D p ∧ c.lastService ≤ D p := by
    intro b c hc
    by_cases hba : b = a
    · subst b
      have hcEq : c = ⟨M.val.S, M.val.q, M.val.delta⟩ :=
        (Option.some.inj (hcutoffRecovered.symm.trans hc)).symm
      subst c
      exact ⟨hMscore, hMqueue, hMdelta⟩
    · have hcOld : l1.cutoffRegisters b = some c := by
        exact (hframeAfter b hba).2.1.symm.trans hc
      exact hcutDomain1 b c hcOld
  have hincrementGammaDomainAfter : ∀ b,
      l2.increment b + l2.gammaLoc b ≤ p.T * D p := by
    intro b
    by_cases hba : b = a
    · subst b
      rw [hincrementRecovered, hgammaAssignedAfter, Nat.add_zero]
      exact hfullBounds.1
    · rw [(hframeAfter b hba).2.2]
      exact (hgamma1 b).2.2
  have hgammaDomainAfter : ∀ b, l2.gammaLoc b ≤ D p := by
    intro b
    rw [show l2.gammaLoc b = l1.gammaLoc b by rfl]
    exact (hgamma1 b).2.1
  have hbaseDomainAfter : ∀ j, l2.baseScore j ≤ p.T * D p := by
    intro j
    change l1.baseScore j ≤ p.T * D p
    rw [hbase1, hbaseZero]
    exact Nat.zero_le _
  have hcutoffMassAfter : ∀ b c, l2.cutoffRegisters b = some c →
      c.score + c.queue ≤ (u - σ) * D p := by
    intro b c hc
    by_cases hba : b = a
    · subst b
      have hcEq : c = ⟨M.val.S, M.val.q, M.val.delta⟩ :=
        (Option.some.inj (hcutoffRecovered.symm.trans hc)).symm
      subst c
      exact hmessageMass
    · have hcOld : l1.cutoffRegisters b = some c := by
        exact (hframeAfter b hba).2.1.symm.trans hc
      exact (hcutMass1 b c hcOld).1
  have hknownMassAfter : ∀ b c q, l2.cutoffRegisters b = some c →
      l2.currentRegisters b = some q →
      c.score + l2.increment b + l2.gammaLoc b + q.queue ≤
          (v + 1 - σ) * D p ∧
        c.score + l2.increment b + l2.gammaLoc b ≤
          C * (min (v + 1) g - σ) := by
    intro b c q hc hq
    by_cases hba : b = a
    · subst b
      have hcEq : c = ⟨M.val.S, M.val.q, M.val.delta⟩ :=
        (Option.some.inj (hcutoffRecovered.symm.trans hc)).symm
      subst c
      have hqEq : q = ⟨(QueueReplay.replay C (0, M.val.q) records).2,
          (QueueReplay.replay C (0, M.val.q) records).1 -
            (QueueReplay.replay C (0, M.val.q)
              (records.take (records.length - 1))).1⟩ :=
        (Option.some.inj (hcurrentRecovered.symm.trans hq)).symm
      subst q
      constructor
      · have htotal := hprefixMass records.length (by omega)
        rw [List.take_length] at htotal
        have htime := htimeSpan records.length (by omega)
        have htimeScale := Nat.mul_le_mul_right (D p) htime
        rw [hincrementRecovered, hgammaAssignedAfter]
        have hlenIdentity : u - σ + records.length = v + 1 - σ := by
          rw [hrecordsLength]
          omega
        rw [hlenIdentity] at htotal
        calc
          _ ≤ (M.val.S +
              (QueueReplay.replay C (0, M.val.q) records).1 +
              (QueueReplay.replay C (0, M.val.q) records).2) := by rfl
          _ ≤ (v + 1 - σ) * D p := htotal
      · simpa [hincrementRecovered, hgammaAssignedAfter] using hendpointScore
    · have hcOld : l1.cutoffRegisters b = some c := by
        exact (hframeAfter b hba).2.1.symm.trans hc
      have hcOrig : l.cutoffRegisters b = some c := by
        rw [← hcutRegisters1]
        exact hcOld
      have hqOld : l1.currentRegisters b = some q := by
        exact (hframeAfter b hba).1.symm.trans hq
      have hmassOld := hknownStart b c q hcOrig hqOld
      have hincEq : l2.increment b = l.increment b := by
        simp [l2, CoordinatorCollectionLedger.acceptUpCandidate, a, hba,
          hincrement1]
      have hgammaEq : l2.gammaLoc b = l1.gammaLoc b := rfl
      have htimeIdentity : sourceRound x.time + 1 - l.sigma = v + 1 - σ := by
        rfl
      have hspanIdentity :
          4 * rate.n * (min (sourceRound x.time + 1) l.freezeAt - l.sigma) =
            C * (min (v + 1) g - σ) := by
        rfl
      constructor
      · simpa [hincEq, hgammaEq, htimeIdentity] using hmassOld.1
      · simpa [hincEq, hgammaEq, hspanIdentity] using hmassOld.2.1
  have hrawCleared : ∀ r, l2.rawBuffer a r = none := by
    intro r
    simpa [l2, CoordinatorCollectionLedger.acceptUpCandidate] using
      CoordinatorCollectionLedger.clearRawArm_same l1.rawBuffer a r
  have hrawFrameAfter : ∀ b, b ≠ a → l2.rawBuffer b = l1.rawBuffer b := by
    intro b hba
    funext r
    simpa [l2, CoordinatorCollectionLedger.acceptUpCandidate] using
      CoordinatorCollectionLedger.clearRawArm_other l1.rawBuffer a b r hba
  have hrawSupportAfter : ∀ b r amount, l2.rawBuffer b r = some amount →
      0 < amount ∧ amount ≤ D p ∧ u ≤ sourceRound r ∧
        sourceRound r ≤ l2.cursor ∧ sourceRound r < l2.freezeAt ∧
        CoordinatorCollectionLedger.armPending l2 b := by
    intro b r amount hcell
    by_cases hba : b = a
    · subst b
      rw [hrawCleared r] at hcell
      cases hcell
    · have hcellOld : l1.rawBuffer b r = some amount := by
        have hframe := congrFun (hrawFrameAfter b hba) r
        exact hframe.symm.trans hcell
      have hdomRaw := hraw1 b r amount hcellOld
      have hpendingAfter := (hArmAfter b).2
        (show b ≠ a ∧ CoordinatorCollectionLedger.armPending l1 b from
          ⟨hba, hdomRaw.2.2.2.2⟩)
      have htimeParts := lt_min_iff.mp hdomRaw.2.2.2.1
      have hcursorEq : l2.cursor = sourceRound x.time := by
        simp [l2, CoordinatorCollectionLedger.acceptUpCandidate, hcursor1]
      have htimeAfter : sourceRound r ≤ l2.cursor ∧
          sourceRound r < l2.freezeAt := by
        rw [hcursorEq]
        exact ⟨Nat.le_of_lt_succ (by
          simpa [ReferenceContinuingCollectionStartDomains.sourceRound] using htimeParts.1),
          by simpa [l2, CoordinatorCollectionLedger.acceptUpCandidate, hfreeze1] using
            htimeParts.2⟩
      exact ⟨hdomRaw.1, hdomRaw.2.1, by simpa [u] using hdomRaw.2.2.1,
        htimeAfter.1, htimeAfter.2, hpendingAfter⟩
  have hhistoryAfter : ∀ r, l2.enabledHistory r =
      if u ≤ sourceRound r ∧ sourceRound r ≤ v then
        some (decide (sourceRound r < g)) else none := by
    intro r
    simpa [l2, CoordinatorCollectionLedger.acceptUpCandidate,
      u, v, g, hcut1, hfreeze1] using hhistory1 r
  have hcurrentPendingCheck : CoordinatorCollectionLedger.allFin p.K
      (fun b => (l2.currentRegisters b).isNone ==
        CoordinatorCollectionLedger.armPendingCheck l2 b) = true :=
    allFin_option_isNone_eq_pendingCheck l2 l2.currentRegisters
      (fun b => (hregistersAfter b).1)
  have hcutoffPendingCheck : CoordinatorCollectionLedger.allFin p.K
      (fun b => (l2.cutoffRegisters b).isNone ==
        CoordinatorCollectionLedger.armPendingCheck l2 b) = true :=
    allFin_option_isNone_eq_pendingCheck l2 l2.cutoffRegisters
      (fun b => (hregistersAfter b).2)
  have hgammaPendingCheck : CoordinatorCollectionLedger.allFin p.K
      (fun b => (!CoordinatorCollectionLedger.armPendingCheck l2 b) ||
        decide (l2.gammaLoc b = 0)) = true :=
    allFin_pending_field_zero l2 l2.gammaLoc (fun b hb =>
      (hzeroPendingAfter b hb).2)
  have hincrementPendingCheck : CoordinatorCollectionLedger.allFin p.K
      (fun b => (!CoordinatorCollectionLedger.armPendingCheck l2 b) ||
        decide (l2.increment b = 0)) = true :=
    allFin_pending_field_zero l2 l2.increment (fun b hb =>
      (hzeroPendingAfter b hb).1)
  have hcurrentDomainsCheck : CoordinatorCollectionLedger.allFin p.K
      (fun b => match l2.currentRegisters b with
        | none => true
        | some q => decide (q.queue ≤ p.T * D p) && decide (q.lastService ≤ D p)) = true := by
    apply (ReferenceFirstCutoffRecordedService.allFin_eq_true_iff _).2
    intro b
    cases hq : l2.currentRegisters b with
    | none => simp
    | some q =>
        have hdomQ := hcurrentDomainAfter b q hq
        simp [hdomQ]
  have hcutoffDomainsCheck : CoordinatorCollectionLedger.allFin p.K
      (fun b => match l2.cutoffRegisters b with
        | none => true
        | some c => decide (c.score ≤ p.T * D p) &&
          decide (c.queue ≤ p.T * D p) && decide (c.lastService ≤ D p)) = true := by
    apply (ReferenceFirstCutoffRecordedService.allFin_eq_true_iff _).2
    intro b
    cases hc : l2.cutoffRegisters b with
    | none => simp
    | some c =>
        have hdomC := hcutoffDomainAfter b c hc
        simp [hdomC]
  have hbaseDomainsCheck : CoordinatorCollectionLedger.allFin (p.m - 1)
      (fun j => decide (l2.baseScore j ≤ p.T * D p)) = true := by
    apply (ReferenceFirstCutoffRecordedService.allFin_eq_true_iff _).2
    intro j
    exact decide_eq_true (hbaseDomainAfter j)
  have hincrementDomainsCheck : CoordinatorCollectionLedger.allFin p.K
      (fun b => decide (l2.increment b ≤ p.T * D p)) = true := by
    apply (ReferenceFirstCutoffRecordedService.allFin_eq_true_iff _).2
    intro b
    exact decide_eq_true (Nat.le_trans (Nat.le_add_right _ _) (hincrementGammaDomainAfter b))
  have hgammaDomainsCheck : CoordinatorCollectionLedger.allFin p.K
      (fun b => decide (l2.gammaLoc b ≤ D p)) = true := by
    apply (ReferenceFirstCutoffRecordedService.allFin_eq_true_iff _).2
    intro b
    exact decide_eq_true (hgammaDomainAfter b)
  have hregisterDomainsAfter :
      CoordinatorCollectionLedger.registerDomainsCheck l2 = true := by
    simp only [CoordinatorCollectionLedger.registerDomainsCheck, Bool.and_eq_true]
    exact ⟨⟨⟨⟨hcurrentDomainsCheck, hcutoffDomainsCheck⟩, hbaseDomainsCheck⟩,
      hincrementDomainsCheck⟩, hgammaDomainsCheck⟩
  have hrawDomainsAfter :
      CoordinatorCollectionLedger.rawEntryDomainsCheck l2 = true := by
    apply (ReferenceFirstCutoffRecordedService.allFin_eq_true_iff _).2
    intro b
    apply (ReferenceFirstCutoffRecordedService.allFin_eq_true_iff _).2
    intro r
    cases hcell : l2.rawBuffer b r with
    | none => rfl
    | some amount =>
        obtain ⟨hpos, hD, hround, hcursorBound, hbeforeFreeze, hpending2⟩ :=
          hrawSupportAfter b r amount hcell
        have hfreeze : sourceRound r < l2.freezeAt := hbeforeFreeze
        have hround' : l2.cutoff ≤ CoordinatorCollectionLedger.sourceRound r := by
          simpa [u, l2, CoordinatorCollectionLedger.acceptUpCandidate,
            hcut1, CoordinatorCollectionLedger.sourceRound,
            ReferenceContinuingCollectionStartDomains.sourceRound] using hround
        have hcursor' : CoordinatorCollectionLedger.sourceRound r ≤ l2.cursor := by
          simpa [CoordinatorCollectionLedger.sourceRound,
            ReferenceContinuingCollectionStartDomains.sourceRound] using hcursorBound
        have hinterval : l2.cutoff ≤ CoordinatorCollectionLedger.sourceRound r ∧
            CoordinatorCollectionLedger.sourceRound r < l2.freezeAt :=
          ⟨hround', hfreeze⟩
        have hcursorCheck := decide_eq_true hcursor'
        have hpendingCheck : CoordinatorCollectionLedger.armPendingCheck l2 b = true :=
          (armPendingCheck_eq_true_iff l2 b).2 hpending2
        simp [hphaseAfter, hpos, hD, hcursorCheck, hpendingCheck]
        exact hinterval
  have hstartedHistoryCheck :
      CoordinatorCollectionLedger.startedHistoryCheck l2 = true := by
    have hcursorEq : l2.cursor = v := by
      simp [l2, CoordinatorCollectionLedger.acceptUpCandidate, v, hcursor1,
        ReferenceContinuingCollectionStartDomains.sourceRound]
    have hcutEq : l2.cutoff = u := by
      simp [l2, CoordinatorCollectionLedger.acceptUpCandidate, u, hcut1]
    apply (ReferenceFirstCutoffRecordedService.allFin_eq_true_iff _).2
    intro r
    change (decide (sourceRound r < l2.cutoff) ||
      ((l2.enabledHistory r).isSome == decide (sourceRound r ≤ l2.cursor))) = true
    rw [hcutEq, hcursorEq, hhistoryAfter r]
    by_cases hbelow : sourceRound r < u
    · simp [hbelow]
    · have hcutRound : u ≤ sourceRound r := by omega
      by_cases hwithin : sourceRound r ≤ v <;> simp [hbelow, hcutRound, hwithin]
  have htimeBoundsAfter :
      1 ≤ l2.sigma ∧ l2.sigma ≤ p.T ∧
      1 ≤ l2.cutoff ∧ l2.cutoff ≤ l2.freezeAt ∧ l2.cutoff ≤ p.T ∧
      l2.freezeAt ≤ p.T + 1 ∧ l2.cutoff ≤ l2.cursor ∧
      l2.cursor ≤ p.T + 1 ∧ l2.cursor ≤ p.T := by
    change 1 ≤ l1.sigma ∧ l1.sigma ≤ p.T ∧
      1 ≤ l1.cutoff ∧ l1.cutoff ≤ l1.freezeAt ∧ l1.cutoff ≤ p.T ∧
      l1.freezeAt ≤ p.T + 1 ∧ l1.cutoff ≤ l1.cursor ∧
      l1.cursor ≤ p.T + 1 ∧ l1.cursor ≤ p.T
    rw [hσ1, hcut1, hfreeze1, hcursor1]
    refine ⟨hσpos, hσT, hcutPos, hcutFreeze, hcutT, hfreezeT, ?_, ?_, ?_⟩
    · change l.cutoff ≤ x.time.val + 1
      rw [← hcursor]
      exact Nat.le_of_lt hcutCursor
    · have htimeT : sourceRound x.time ≤ p.T := by
        dsimp [sourceRound]
        exact Nat.succ_le_of_lt x.time.isLt
      exact Nat.le_trans htimeT (Nat.le_succ _)
    · exact Nat.succ_le_of_lt x.time.isLt
  have hacceptedCandidate :
      CoordinatorCollectionLedger.validLedgerCheck l2 = true := by
    have hreadyFalse : decide (l2.phase = CoordinatorCollectionLedger.Phase.ready) = false := by
      simp [hphaseAfter]
    rcases htimeBoundsAfter with
      ⟨hsigPos, hsigT, hcutPos', hcutFreeze', hcutT', hfreezeT',
        hcutCursor', hcursorT1, hcursorT⟩
    simp [CoordinatorCollectionLedger.validLedgerCheck, hreadyFalse,
      decide_eq_true hsigPos, decide_eq_true hsigT,
      decide_eq_true hcutPos', decide_eq_true hcutFreeze', decide_eq_true hcutT',
      decide_eq_true hfreezeT', decide_eq_true hcutCursor',
      decide_eq_true hcursorT1, decide_eq_true hcursorT,
      hstartedHistoryCheck, hcurrentPendingCheck, hcutoffPendingCheck,
      hgammaPendingCheck, hincrementPendingCheck, hregisterDomainsAfter,
      hrawDomainsAfter]
  have hdecodeInput :
      CoordinatorCollectionLedger.validLedgerCheck l1 = true ∧
        l1.phase = CoordinatorCollectionLedger.Phase.started ∧
        1 ≤ l1.cutoff ∧ l1.cutoff ≤ l1.cursor ∧ l1.cursor ≤ p.T := by
    refine ⟨hvalid, hphase, ?_, ?_, ?_⟩
    · rw [hcut1]
      exact hcutPos
    · rw [hcut1, hcursor1]
      have hcutTime : l.cutoff < x.time.val + 1 := by
        simpa [hcursor] using hcutCursor
      simpa [ReferenceContinuingCollectionStartDomains.sourceRound] using
        Nat.le_of_lt hcutTime
    · rw [hcursor1]
      simp [ReferenceContinuingCollectionStartDomains.sourceRound]
  have hcursorV : l1.cursor = v := by
    simpa [v, ReferenceContinuingCollectionStartDomains.sourceRound] using hcursor1
  have hcutU : l1.cutoff = u := by
    simp [u, hcut1]
  have hdecodePastActual :
      CoordinatorCollectionLedger.replayRecords? l1 a
        (CoordinatorCollectionLedger.calendarIndices p.T (u - 1)
          (x.time.val + 1 - u) hindices) = some past := hPastSome
  have hdecodeCutoffTime : 1 ≤ u ∧ u ≤ x.time.val + 1 := by
    constructor
    · simpa [u] using hcutPos
    · have hcutTime : l.cutoff < x.time.val + 1 := by
        simpa [hcursor] using hcutCursor
      dsimp [u]
      omega
  have hdecodeAccept : CoordinatorCollectionLedger.acceptUpCheck l1 i M = true := by
    simpa [i] using haccept
  have hdecodeReplayCheck :
      CoordinatorCollectionLedger.replayOutputDomainsCheck (p := p) (4 * rate.n) M.val.q
        (past ++ [current]) = true := by
    simpa [C, records] using hreplayCheck
  have hdecoded : CoordinatorCollectionLedger.decodeUp l1 i (some M) = .success l2 := by
    simp [CoordinatorCollectionLedger.decodeUp, hdecodeInput, hdecodeCutoffTime,
      hdecodeAccept, hunknown,
      hdecodePastActual, hCurrentSome, hdecodeReplayCheck, hacceptedCandidate, l2,
      a, hcursorV, hcutU, v]
  let bank := CoordinatorUpReception.decoderBankAfter receptionInput
  have hselected : receptionInput.selectedFollower = i := by
    change ReferenceActivePhysicalStep.upSenderIndex x = i
    rfl
  have hinputBank : receptionInput.upDecoderBank = x.state.upDecoderBank := rfl
  let decoderRaw := (CoordinatorUpReception.decoderTransition receptionInput).2
  let expected := ReferenceActivePhysicalStep.upExpected prepared
  have hfilteredParse : CoordinatorUpReception.parseDecoderOutput
      (ReferenceUpReception.filterRawByExpected decoderRaw expected) = some M := by
    simpa [ReferenceCollectionSegmentExtraction.effectiveParse, decoderRaw, expected]
      using hparse
  have hrawEq : decoderRaw = expected := by
    by_contra hne
    have hnone := ReferenceUpReception.filterRawByExpected_eq_none_of_ne
      decoderRaw expected hne
    have hparseNone : CoordinatorUpReception.parseDecoderOutput none = some M := by
      simpa [hnone] using hfilteredParse
    change OrdinaryMessageCodec.parseUp
      (CoordinatorCollectionLedger.codecParams p rate.eta.val) none = some M at hparseNone
    simp [OrdinaryMessageCodec.parseUp] at hparseNone
  have hfilteredSame :
      ReferenceUpReception.filterRawByExpected decoderRaw expected = decoderRaw := by
    exact ReferenceUpReception.filterRawByExpected_eq_raw_of_eq decoderRaw expected hrawEq
  have hparseActual : CoordinatorUpReception.parseDecoderOutput decoderRaw = some M := by
    rw [← hfilteredSame]
    exact hfilteredParse
  have hrawDecision : ∃ word,
      (CoordinatorUpReception.decoderTransition receptionInput).2 = some word := by
    cases hraw : decoderRaw with
    | none =>
        have hparseNone : CoordinatorUpReception.parseDecoderOutput none = some M := by
          simpa [hraw, ReferenceUpReception.filterRawByExpected] using hfilteredParse
        change OrdinaryMessageCodec.parseUp
          (CoordinatorCollectionLedger.codecParams p rate.eta.val) none = some M at hparseNone
        simp [OrdinaryMessageCodec.parseUp] at hparseNone
    | some word => exact ⟨word, hraw⟩
  rcases hrawDecision with ⟨word, hdecision⟩
  let tr := CoordinatorUpReception.traceAt receptionInput
  let s := receptionInput.upDecoderBank receptionInput.selectedFollower
  have hstepOutput : AffineBatchDecoder.stepOutput p tr s receptionInput.time =
      some word := by
    simpa [CoordinatorUpReception.decoderTransition, tr, s,
      AffineBatchDecoder.decodeStep] using hdecision
  have hfull := (AffineBatchDecoder.stepOutput_eq_some_iff p tr s
    receptionInput.time word).mp hstepOutput
  have hpendingLt : s.pending.length < AffineBatchDecoder.quota p := by
    simpa [s, hinputBank, hselected] using (hbank i).1
  have heligible : AffineBatchDecoder.eligible (tr receptionInput.time) := by
    by_contra hnot
    simp [AffineBatchDecoder.positiveAt, hnot] at hfull
    omega
  have hsize : (s.pending ++
      AffineBatchDecoder.positiveAt p tr receptionInput.time).length =
        AffineBatchDecoder.quota p := by
    have hupper : (s.pending ++
        AffineBatchDecoder.positiveAt p tr receptionInput.time).length ≤
          AffineBatchDecoder.quota p := by
      simp [AffineBatchDecoder.positiveAt, heligible]
      omega
    exact Nat.le_antisymm hupper hfull.1
  have hquota : s.pending.length + 1 = AffineBatchDecoder.quota p := by
    simpa [AffineBatchDecoder.positiveAt, heligible] using hsize
  have hcomplete := AffineBatchDecoder.decodeStep_complete p tr s
    receptionInput.time heligible hquota
  have htransition : CoordinatorUpReception.decoderTransition receptionInput =
      (⟨[], s.completed ++ [s.pending ++
        [AffineBatchDecoder.entry p tr receptionInput.time]]⟩,
        AffineBatchDecoder.batchOutput (s.pending ++
          [AffineBatchDecoder.entry p tr receptionInput.time])) := by
    simpa [CoordinatorUpReception.decoderTransition, tr, s] using hcomplete
  have htransitionSelected :
      (CoordinatorUpReception.decoderTransition receptionInput).1 =
        ⟨[], (x.state.upDecoderBank i).completed ++
          [(x.state.upDecoderBank i).pending ++
            [AffineBatchDecoder.entry p
              (CoordinatorUpReception.traceAt receptionInput) receptionInput.time]]⟩ := by
    simpa [hselected, hinputBank, s, tr] using congrArg Prod.fst htransition
  have hdecisionClears := CoordinatorUpReception.decoderTransition_decision_clears
    receptionInput hdomain word hdecision
  have hselectedClear : (bank i).pending = [] := by
    simpa [bank, CoordinatorUpReception.decoderBankAfter, hselected] using
      hdecisionClears.1
  have hselectedBatch : ∃ batch, batch ∈ (bank i).completed ∧
      batch.length = AffineBatchDecoder.quota p := by
    rcases hdecisionClears.2 with ⟨batch, hmem, hlen⟩
    refine ⟨batch, ?_, hlen⟩
    simpa [bank, CoordinatorUpReception.decoderBankAfter, hselected] using hmem
  have hbankUnselected : ∀ j, j ≠ i → bank j = x.state.upDecoderBank j := by
    intro j hji
    have hjselected : j ≠ receptionInput.selectedFollower := by
      simpa [hselected] using hji
    calc
      bank j = CoordinatorUpReception.decoderBankAfter receptionInput j := rfl
      _ = receptionInput.upDecoderBank j :=
        CoordinatorUpReception.decoderBankAfter_unselected receptionInput j hjselected
      _ = x.state.upDecoderBank j := congrFun hinputBank j
  have hbankEmptyOutside : ∀ j, j ∉ l2.pending → (bank j).pending = [] := by
    intro j hjout
    by_cases hji : j = i
    · subst j
      exact hselectedClear
    · have hjold : j ∉ l.pending := by
        intro hj
        apply hjout
        rw [hpendingAfter]
        exact Finset.mem_erase.mpr ⟨hji, hj⟩
      rw [hbankUnselected j hji]
      simpa [hinputBank] using (hbank j).2.2 hjold
  have hactualBankFacts :
      CoordinatorUpReception.decoderBankWellFormed p bank := by
    simpa [bank] using
      CoordinatorUpReception.decoderBankAfter_wellFormed receptionInput hdomain
  have hactualU := CoordinatorUpReception.receiveUp_eq_existing_decodeUp
    receptionInput hinputCheck
  have hactualUResult : CoordinatorUpReception.receiveUp receptionInput =
      .success (l2, bank) := by
    rw [hactualU]
    have hparseRaw : OrdinaryMessageCodec.parseUp
        (CoordinatorCollectionLedger.codecParams p rate.eta.val)
        (decoderRaw.map (OrdinaryMessageCodec.wordEquivFlat
          (CoordinatorCollectionLedger.codecParams p rate.eta.val)).symm) = some M := by
      simpa [CoordinatorUpReception.parseDecoderOutput] using hparseActual
    have hdecodeActual : CoordinatorCollectionLedger.decodeUp receptionInput.ledger
        receptionInput.selectedFollower
        (OrdinaryMessageCodec.parseUp
          (CoordinatorCollectionLedger.codecParams p rate.eta.val)
          (decoderRaw.map (OrdinaryMessageCodec.wordEquivFlat
            (CoordinatorCollectionLedger.codecParams p rate.eta.val)).symm)) = .success l2 := by
      rw [show receptionInput.ledger = l1 by rfl, hselected, hparseRaw]
      exact hdecoded
    have hbankUpdate : Function.update receptionInput.upDecoderBank
        receptionInput.selectedFollower (CoordinatorUpReception.decoderTransition receptionInput).1 =
          bank := rfl
    rw [hdecodeActual, hbankUpdate]
    rfl
  have hphysicalMatch :
      (CoordinatorUpReception.decoderTransition
        (ReferenceUpReception.receptionInputAtRow rate x.row
          (ReferenceActivePhysicalStep.upInputs prepared l1) x.time)).2 =
        ReferenceActivePhysicalStep.upExpected prepared := by
    simpa [receptionInput, decoderRaw, expected] using hrawEq
  have hphysicalReceive := ReferenceActivePhysicalStep.receiveUp_eq_ordinary_of_no_mismatch
    prepared l1 hphysicalMatch
  have hreceiveSuccess :
      (ReferenceActivePhysicalStep.receiveUp prepared l1).result =
        .success (l2, bank) := by
    rw [hphysicalReceive, hactualUResult]
  have hdiagnostic :
      (ReferenceActivePhysicalStep.receiveUp prepared l1).diagnostic =
        some {
          input := receptionInput
          expected := ReferenceActivePhysicalStep.upExpected prepared
          decoderAfter := (CoordinatorUpReception.decoderTransition receptionInput).1
          raw := (CoordinatorUpReception.decoderTransition receptionInput).2
          parsed := ReferenceUpReception.rawParsedOutput rate receptionInput
          locallyAccepted := ReferenceUpReception.rawParsedLocalAcceptance rate receptionInput
          rawMatches := decide ((CoordinatorUpReception.decoderTransition receptionInput).2 =
            ReferenceActivePhysicalStep.upExpected prepared)
          wrongUniqueAccepted := ReferenceUpReception.wrongUniqueAndLocalAcceptanceAtRow
            rate x.row (ReferenceActivePhysicalStep.upInputs prepared l1) x.time
            (prepared.followers.followers i)
            (prepared.follower_alignment _).1
            (prepared.follower_alignment _).2.1
            (prepared.follower_alignment _).2.2.1 rfl } := by
    unfold ReferenceActivePhysicalStep.receiveUp
    dsimp only
    rw [hinputCheck]
    rfl
  refine ⟨past, current, hunknown.1, hunknown.2, hPastSome, hCurrentSome,
    rfl, rfl, ?_, ?_, hfourN, ?_, ?_, hreplayCheck, hendpointScore, ?_⟩
  · simpa [records] using hrecordsLength
  · simpa [records] using hrecordsArrival
  · intro h hh
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [records] using hprefixMass h (by simpa [records] using hh)
    · simpa [records] using hprefixSpan h (by simpa [records] using hh)
    · exact (hprefixBounds h hh).1
    · exact (hprefixBounds h hh).2
    · intro hpos
      apply hprefixService h (by simpa [records] using hh)
      exact hpos
  · simpa [records] using hbits
  · refine ⟨l2, bank, rfl, hacceptedCandidate, hdecoded, hreceiveSuccess,
      rfl, hphysicalMatch, hparseActual, hdiagnostic, ?_⟩
    refine ⟨hphaseAfter, hpendingAfter, hσ1, hcut1, ?_, hfreeze1,
      hassignment1, hbase1, hcutoffRecovered, ?_, hincrementRecovered,
      hgammaAssignedAfter, ?_, ?_, ?_, hregistersAfter,
      hzeroPendingAfter, hcutoffMassAfter, hknownMassAfter,
      hrawSupportAfter, hhistoryAfter, hactualBankFacts,
      by simpa [s, hinputBank, hselected] using hquota, hselectedClear,
      hselectedBatch, htransitionSelected, hbankUnselected,
      hbankEmptyOutside⟩
    · simpa [l2, CoordinatorCollectionLedger.acceptUpCandidate, v,
        ReferenceContinuingCollectionStartDomains.sourceRound] using hcursor1
    · simpa [records] using hcurrentRecovered
    · intro b
      rfl
    · change l2.rawBuffer (l1.assignment.arm i) = fun _ => none
      funext r
      simpa [a] using hrawCleared r
    · intro b hb
      have hba : b ≠ a := by simpa [a] using hb
      exact ⟨(hframeAfter b hba).1, (hframeAfter b hba).2.1,
        (hframeAfter b hba).2.2, hrawFrameAfter b hba⟩

end Bandits.Support.ReferenceContinuingCollectionAcceptedDecodeDomains

end
