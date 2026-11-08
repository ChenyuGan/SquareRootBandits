/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedFirstCutoffCoordinatorEndpoint
public import Bandits.Support.ReferenceContinuingCollectionStartDomains

import Lean.Elab.Tactic.Omega

/-!
# Actual first-collection ready initialization

Sources: `sources/zip4/manuscript/06_interruptions.tex:41-70,246-295`,
`sources/zip4/manuscript/04_slow_fast_learner.tex:157-174`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-64`, and
`sources/zip4/manuscript/07_public_setup.tex:127-164`.

The intended consumer is the first-collection coordinator domain induction.
This file concerns its initial boundary, including the terminal boundary.
Raw buffers and enable history are empty before the cutoff operation; its
one-round updates survive reception and finish. No analytical queue
identity, accepted-UP producer, or manuscript closure is asserted.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions
open ReferenceActivePhysicalStep
open ReferenceActivePhysicalHorizon
open ReferenceFirstLiveConfirmationHistory
open ReferenceGeneratedFirstCutoffSurvival

open scoped Classical

namespace Bandits.Support.ReferenceFirstCollectionReadyInitialization

variable {p : ConstructorDimensions.Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}

private theorem armPendingCheck_iff (l : Ledger rate) (a : Fin p.K) :
    CoordinatorCollectionLedger.armPendingCheck l a = true ↔
      CoordinatorCollectionLedger.armPending l a := by
  unfold CoordinatorCollectionLedger.armPendingCheck CoordinatorCollectionLedger.anyFin
  rw [List.any_eq_true]
  simp [CoordinatorCollectionLedger.armPending]

/-- Extract the literal option, zero-service and strict raw-support clauses
from a checked ready ledger. No numeric conservation is inferred here. -/
private theorem checked_ready_fields (l : Ledger rate)
    (hvalid : CoordinatorCollectionLedger.validLedgerCheck l = true)
    (hphase : l.phase = .ready) :
    (∀ a, (l.currentRegisters a = none ↔ CoordinatorCollectionLedger.armPending l a) ∧
      (l.cutoffRegisters a = none ↔ CoordinatorCollectionLedger.armPending l a)) ∧
    (∀ a, l.gammaLoc a = 0 ∧
      (CoordinatorCollectionLedger.armPending l a → l.increment a = 0)) ∧
    (∀ a r amount, l.rawBuffer a r = some amount →
      0 < amount ∧ amount ≤ D p ∧ l.cutoff ≤ r.val + 1 ∧
      r.val + 1 < min l.cursor l.freezeAt ∧ CoordinatorCollectionLedger.armPending l a) := by
  have hp := ReferenceFirstCutoffRecordedService.validLedger_pendingChecks l hvalid
  have hparts := hvalid
  simp only [CoordinatorCollectionLedger.validLedgerCheck, Bool.and_eq_true] at hparts
  have hzero := hparts.1.1.1.1.1.1.1.1.2
  have hinc := hparts.1.1.2
  have hraw := hparts.2
  refine ⟨?_, ?_, ?_⟩
  · intro a
    constructor
    · rw [← armPendingCheck_iff, ← hp.1 a]
      exact Option.isNone_iff_eq_none.symm
    · rw [← armPendingCheck_iff, ← hp.2 a]
      exact Option.isNone_iff_eq_none.symm
  · intro a
    have hz := hzero
    simp only [hphase, decide_true, Bool.not_true, Bool.false_or] at hz
    have hzA := (ReferenceFirstCutoffRecordedService.allFin_eq_true_iff _).mp hz a
    refine ⟨of_decide_eq_true hzA, ?_⟩
    intro ha
    have hi := (ReferenceFirstCutoffRecordedService.allFin_eq_true_iff _).mp hinc a
    rw [(armPendingCheck_iff l a).mpr ha] at hi
    exact of_decide_eq_true hi
  · intro a r amount hr
    simp only [CoordinatorCollectionLedger.rawEntryDomainsCheck] at hraw
    have hrA := (ReferenceFirstCutoffRecordedService.allFin_eq_true_iff _).mp hraw a
    have hrR := (ReferenceFirstCutoffRecordedService.allFin_eq_true_iff _).mp hrA r
    simp only [hr, hphase, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq,
      CoordinatorCollectionLedger.sourceRound] at hrR
    exact ⟨hrR.1.1.1.1.1, hrR.1.1.1.1.2,
      of_decide_eq_true hrR.1.1.1.2,
      lt_min (of_decide_eq_true hrR.1.2) (of_decide_eq_true hrR.1.1.2),
      (armPendingCheck_iff l a).mp hrR.2⟩

private theorem finish_eq_candidate (l finished : Ledger rate)
    (h : CoordinatorCollectionLedger.finishRound l = .success finished) :
    finished = CoordinatorCollectionLedger.finishRoundCandidate l := by
  unfold CoordinatorCollectionLedger.finishRound at h
  split at h
  · dsimp only at h
    split at h
    · exact (CoordinatorCollectionLedger.Checked.success.inj h).symm
    · cases h
  · cases h

/-- Local arithmetic for the actual cutoff START followed by rejected decode
and FINISH. The old queue is used only in conservation; the conclusion bounds
the returned current queue. All conditional helper inputs are explicit. -/
private theorem cutoff_finish_budgets
    (l : Ledger rate) (t : Fin p.T) (o : CoordinatorRecordingOperation.Output p)
    (hσ : 1 ≤ l.sigma) (hσu : l.sigma ≤ t.val + 1)
    (hu : l.cutoff = t.val + 1) (hug : l.cutoff ≤ l.freezeAt)
    (hinc : l.increment = fun _ => 0)
    (hcurrent : l.currentRegisters = fun a =>
      (l.cutoffRegisters a).map (fun c => ⟨c.queue, c.lastService⟩))
    (hmass : ∀ a c, l.cutoffRegisters a = some c →
      c.score + c.queue ≤ (l.cutoff - l.sigma) * D p ∧ c.lastService ≤ D p)
    (hcap : ∀ a c, l.cutoffRegisters a = some c →
      c.score ≤ 4 * rate.n * (l.cutoff - l.sigma)) :
    let raw := CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder o
    let started := CoordinatorCollectionLedger.startRoundCandidate l t (collectionEnabled l t) raw
    let finished : Ledger rate := CoordinatorCollectionLedger.finishRoundCandidate
      { started with phase := CoordinatorCollectionLedger.Phase.decoded }
    (∀ a c qNew, finished.cutoffRegisters a = some c →
      finished.currentRegisters a = some qNew →
      qNew.lastService ≤ D p ∧
      c.score + finished.increment a + qNew.queue ≤ (t.val + 2 - l.sigma) * D p ∧
      c.score + finished.increment a ≤
        4 * rate.n * (min (t.val + 2) l.freezeAt - l.sigma)) := by
  classical
  dsimp only
  let raw := CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder o
  let started := CoordinatorCollectionLedger.startRoundCandidate l t (collectionEnabled l t) raw
  let finished : Ledger rate := CoordinatorCollectionLedger.finishRoundCandidate
    { started with phase := CoordinatorCollectionLedger.Phase.decoded }
  have hen : collectionEnabled l t = decide (t.val + 1 < l.freezeAt) := by
    simp only [collectionEnabled, show 0 < l.sigma by omega, ← hu, le_refl, true_and]
  have harr : ∀ a, CoordinatorCollectionLedger.localArrival raw a ≤ D p := by
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
  intro a c qNew hc hq
  change l.cutoffRegisters a = some c at hc
  have hold : l.currentRegisters a = some ⟨c.queue, c.lastService⟩ := by
    simp only [hcurrent, hc, Option.map_some]
  have hpre := (hmass a c hc).1
  have hscore := hcap a c hc
  have hD := ActiveFollowerDownAcceptance.four_n_le_D p rate
  have hspan : t.val + 2 - l.sigma = (l.cutoff - l.sigma) + 1 := by omega
  have hincA : l.increment a = 0 := congrFun hinc a
  by_cases hf : t.val + 1 < l.freezeAt
  · let service := min (4 * rate.n) (c.queue + CoordinatorCollectionLedger.localArrival raw a)
    have hs : service ≤ 4 * rate.n := Nat.min_le_left _ _
    have hsQ : service ≤ c.queue + CoordinatorCollectionLedger.localArrival raw a :=
      Nat.min_le_right _ _
    have hqEq : qNew = ⟨c.queue + CoordinatorCollectionLedger.localArrival raw a - service,
        service⟩ := by
      simp only [CoordinatorCollectionLedger.finishRoundCandidate,
        CoordinatorCollectionLedger.startRoundCandidate, hold, hen,
        CoordinatorCollectionLedger.localQueueRecord, CoordinatorCollectionLedger.sourceRound,
        hf, decide_true, Bool.true_and, ↓reduceIte, QueueReplay.transition,
        Nat.zero_add] at hq
      exact (Option.some.inj hq).symm
    have hi : finished.increment a = service := by
      simp [finished, CoordinatorCollectionLedger.finishRoundCandidate, started,
        CoordinatorCollectionLedger.startRoundCandidate, hold, hen,
        CoordinatorCollectionLedger.localQueueRecord, CoordinatorCollectionLedger.sourceRound,
        hf, QueueReplay.transition, hincA, service]
    have hcapSpan : min (t.val + 2) l.freezeAt - l.sigma =
        (l.cutoff - l.sigma) + 1 := by omega
    rw [hqEq, hi]
    refine ⟨hs.trans hD, ?_, ?_⟩
    · change c.score + service + (c.queue + CoordinatorCollectionLedger.localArrival raw a - service) ≤ _
      rw [hspan, Nat.add_mul, Nat.one_mul]
      have ha := harr a
      omega
    · rw [hcapSpan, Nat.mul_add, Nat.mul_one]
      exact Nat.add_le_add hscore hs
  · have hqEq : qNew = ⟨c.queue, 0⟩ := by
      simp only [CoordinatorCollectionLedger.finishRoundCandidate,
        CoordinatorCollectionLedger.startRoundCandidate, hold, hen,
        CoordinatorCollectionLedger.localQueueRecord, CoordinatorCollectionLedger.sourceRound,
        hf, decide_false, Bool.false_and, QueueReplay.transition] at hq
      exact (Option.some.inj hq).symm
    have hi : finished.increment a = 0 := by
      simp [finished, CoordinatorCollectionLedger.finishRoundCandidate, started,
        CoordinatorCollectionLedger.startRoundCandidate, hold, hen,
        CoordinatorCollectionLedger.localQueueRecord, CoordinatorCollectionLedger.sourceRound,
        hf, QueueReplay.transition, hincA]
    have hcapSpan : min (t.val + 2) l.freezeAt - l.sigma = l.cutoff - l.sigma := by omega
    rw [hqEq, hi]
    refine ⟨Nat.zero_le _, ?_, ?_⟩
    · simpa only [Nat.add_zero] using hpre.trans
        (Nat.mul_le_mul_right (D p) (by omega : l.cutoff - l.sigma ≤ t.val + 2 - l.sigma))
    · simpa only [Nat.add_zero, hcapSpan] using hscore

/-- Bounds for the literal outside-register initializer. The mass and replay
inputs here are diagnostic prefix facts, produced from the same original run
in the public theorem. -/
private theorem outside_register_budgets
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r) (t : Fin p.T)
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (k : ℕ)
    (hmass : ∀ a, r.complementScores a + q.queue a ≤ k * D p)
    (hlast : ∀ a, q.previousService a ≤ D p)
    (hreplay : ∀ a : CanonicalFastSampling.FastArm r.payload.slowSet,
      let rs := ReferenceFirstComplementReplay.liveDiagnosticQueueRecords r.payload a.1 records k
      rs.length = k ∧ (r.complementScores a, q.queue a) =
        QueueReplay.replay (4 * r.payload.n) (0, 0) rs) :
    ∀ a c, CoordinatorStartRoundCutoffDispatch.outsideRegisters
      (liveRegistersAt r t) (liveOwnedAt r q t) a = some c →
      (c.score + c.queue ≤ k * D p ∧ c.lastService ≤ D p) ∧
      c.score ≤ 4 * rate.n * k := by
  intro a c hc
  simp only [CoordinatorStartRoundCutoffDispatch.outsideRegisters] at hc
  split at hc
  · rename_i ha
    have hcEq := Option.some.inj hc
    subst c
    have hr := hreplay ⟨a, ha⟩
    have hs := (ReplayWeightStability.replay_score_envelope (4 * r.payload.n) 0 0
      (ReferenceFirstComplementReplay.liveDiagnosticQueueRecords r.payload a records k)).2
    have hrLength : (ReferenceFirstComplementReplay.liveDiagnosticQueueRecords
        r.payload a records k).length = k := hr.1
    rw [hrLength] at hs
    have hz : r.complementScores ⟨a, ha⟩ = (QueueReplay.replay (4 * r.payload.n) (0, 0)
        (ReferenceFirstComplementReplay.liveDiagnosticQueueRecords r.payload a records k)).1 :=
      congrArg Prod.fst hr.2
    refine ⟨⟨hmass ⟨a, ha⟩, hlast ⟨a, ha⟩⟩, ?_⟩
    simpa only [liveRegistersAt, Nat.zero_add, payload_n_eq r.payload] using hz.trans_le hs
  · cases hc

/-- Exact one-round history and raw-buffer frames. Both buffers are empty
only in the incoming initializer; the optional cutoff write is retained. -/
private theorem initial_finish_history
    (l : Ledger rate) (t : Fin p.T) (o : CoordinatorRecordingOperation.Output p)
    (finished : Ledger rate)
    (hσ : 1 ≤ l.sigma) (hu : l.cutoff = t.val + 1)
    (hraw : l.rawBuffer = fun _ _ => none)
    (hhistory : l.enabledHistory = fun _ => none)
    (hf : finished = CoordinatorCollectionLedger.finishRoundCandidate
      { CoordinatorCollectionLedger.startRoundCandidate l t (collectionEnabled l t)
          (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder o) with
        phase := CoordinatorCollectionLedger.Phase.decoded }) :
    (∀ j : Fin p.T, finished.enabledHistory j =
      if finished.cutoff ≤ j.val + 1 ∧ j.val + 1 < finished.cursor then
        some (decide (j.val + 1 < finished.freezeAt)) else none) ∧
    finished.enabledHistory t = some (decide (t.val + 1 < finished.freezeAt)) ∧
    (∀ j, j ≠ t → finished.enabledHistory j = none) ∧
    (∀ a j, j ≠ t → finished.rawBuffer a j = none) ∧
    (∀ a j, t.val + 1 < j.val + 1 → finished.rawBuffer a j = none) := by
  classical
  have hen : collectionEnabled l t = decide (t.val + 1 < l.freezeAt) := by
    simp only [collectionEnabled, show 0 < l.sigma by omega, ← hu, le_refl, true_and]
  have hh : ∀ j : Fin p.T, finished.enabledHistory j =
      if finished.cutoff ≤ j.val + 1 ∧ j.val + 1 < finished.cursor then
        some (decide (j.val + 1 < finished.freezeAt)) else none := by
    intro j
    rw [hf]
    change Function.update l.enabledHistory t (some (collectionEnabled l t)) j =
      if l.cutoff ≤ j.val + 1 ∧ j.val + 1 < t.val + 2 then
        some (decide (j.val + 1 < l.freezeAt)) else none
    by_cases hj : j = t
    · subst j
      simp only [Function.update_self, hen, hu, le_refl, Nat.lt_succ_self, and_self, ↓reduceIte]
    · have hval : j.val ≠ t.val := fun h => hj (Fin.ext h)
      rw [Function.update_of_ne hj, hhistory]
      have hout : ¬ (l.cutoff ≤ j.val + 1 ∧ j.val + 1 < t.val + 2) := by rw [hu]; omega
      rw [ite_eq_right hout]
  have hat : finished.enabledHistory t = some (decide (t.val + 1 < finished.freezeAt)) := by
    rw [hf]
    change Function.update l.enabledHistory t (some (collectionEnabled l t)) t = _
    rw [Function.update_self, hen]
    rfl
  have hother : ∀ j, j ≠ t → finished.enabledHistory j = none := by
    intro j hj
    rw [hf]
    change Function.update l.enabledHistory t (some (collectionEnabled l t)) j = none
    rw [Function.update_of_ne hj, hhistory]
  have hrawOther : ∀ a j, j ≠ t → finished.rawBuffer a j = none := by
    intro a j hj
    rw [hf]
    change (CoordinatorCollectionLedger.startRoundCandidate l t (collectionEnabled l t)
      (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder o)).rawBuffer a j = none
    cases hr : CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder o with
    | none => simp only [CoordinatorCollectionLedger.startRoundCandidate, hraw]
    | some pair =>
      obtain ⟨b, amount⟩ := pair
      simp only [CoordinatorCollectionLedger.startRoundCandidate]
      split
      · rw [CoordinatorCollectionLedger.putRaw_other l.rawBuffer b a t j amount (Or.inr hj), hraw]
      · rw [hraw]
  refine ⟨hh, hat, hother, hrawOther, ?_⟩
  intro a j hj
  exact hrawOther a j (by intro heq; subst j; omega)

/-- Clock arithmetic at a completed cutoff boundary, including the terminal
cursor. These are natural-number consequences of the actual clock fields. -/
private theorem boundary_time_fields
    (T sigma cutoff cursor freezeAt payloadSigma s k : ℕ)
    (hσ : sigma = s + 1) (hu : cutoff = s + k + 1)
    (hv : cursor = s + k + 2) (hpayload : sigma = payloadSigma + 1)
    (hbefore : sigma < cutoff) (huT : cutoff ≤ T) (hug : cutoff ≤ freezeAt) :
    1 ≤ sigma ∧ sigma ≤ T ∧ sigma < cutoff ∧ sigma = payloadSigma + 1 ∧
    1 ≤ cutoff ∧ cutoff ≤ T ∧ cutoff ≤ freezeAt ∧ cutoff < cursor ∧
    cursor ≤ T + 1 ∧ (cutoff = T → cursor = T + 1) := by
  refine ⟨?_, ?_, hbefore, hpayload, ?_, huT, hug, ?_, ?_, ?_⟩ <;> omega

/-- Indexed successor/prefix transport on the original horizon fold. Calendar
time alone is not used to identify the next retained record. -/
private theorem next_input_eq_record
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (s count index : ℕ) (hspan : s + count ≤ p.T)
    (active : allActiveAtStart initial s) (hi : index < count) :
    let priorRun := run initial rows J rewards s index (by omega) active
    roundInputAt initial rows J rewards s active priorRun ⟨s + index, by omega, by omega⟩ =
      ((run initial rows J rewards s count hspan active).records[index]'(by
        rw [run_record_count]; exact hi)).input := by
  have hstepSpan : s + (index + 1) ≤ p.T := by omega
  obtain ⟨tail, hprefixRecords⟩ := ReferenceCollectionPhaseHistory.run_records_prefix initial
    rows J rewards s (index + 1) (count - (index + 1)) (by omega) active
  have hcountEq : index + 1 + (count - (index + 1)) = count := by omega
  have hprefixRecordsCount : (run initial rows J rewards s count hspan active).records =
      (run initial rows J rewards s (index + 1) hstepSpan active).records ++ tail := by
    simpa only [hcountEq] using hprefixRecords
  rw [ReferenceAssignmentPayloadChronology.run_successor_actualRunRecordAt] at hprefixRecordsCount
  have hlen := run_record_count initial rows J rewards s index (by omega) active
  have hprefixRecords' : (run initial rows J rewards s count hspan active).records =
      (run initial rows J rewards s index (by omega) active).records ++
        ReferenceAssignmentPayloadChronology.actualRunRecordAt initial rows J rewards
          s index hstepSpan active :: tail := by
    simpa only [List.append_assoc, List.singleton_append] using hprefixRecordsCount
  have hget := List.getElem_of_append hprefixRecords' hlen
  exact (congrArg (fun rec : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) =>
    rec.input) hget).symm

/-- Construct every incoming local ready-domain field from the original
first cutoff and its actual rejected coordinator endpoint. The literal
boundary facts apply also at `u = T`; only the next physical input requires
`u < T`. This is an internal initialization theorem, not manuscript closure. -/
theorem actual_first_collection_ready_initialization
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (s : ℕ)
    (hsElapsed : s = ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed)
    (count : ℕ) (hspan : s + count ≤ p.T)
    (hshort : (firstLiveWindow
      (generatedFirstCutoffRun rate z rewards C_star C_h hc s hsElapsed count hspan).records).length < count) :
    let initial := ReferenceFirstLaunchNumericalCell.launchState rate z rewards C_star C_h hc
    let execution := generatedFirstCutoffRun rate z rewards C_star C_h hc s hsElapsed count hspan
    let window := firstLiveWindow execution.records
    let k := window.length
    let hprefixSpan : s + k ≤ p.T := by
      have hk : k < count := by simpa [window, execution] using hshort
      exact le_trans (Nat.add_le_add_left (Nat.le_of_lt hk) s) hspan
    let hsuccessorSpan : s + (k + 1) ≤ p.T := by
      have hk : k < count := by simpa [window, execution] using hshort
      omega
    let prefixRun := ReferenceActivePhysicalHorizon.run initial z.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s k hprefixSpan
      (generatedLaunchActive rate z rewards C_star C_h hc s hsElapsed)
    let successorRun := ReferenceActivePhysicalHorizon.run initial z.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s (k + 1) hsuccessorSpan
      (generatedLaunchActive rate z rewards C_star C_h hc s hsElapsed)
    s < p.T ∧
    ∃ cut suffix,
      execution.records = window ++ cut :: suffix ∧
      cut = execution.records[k]'(by
        have hlen : execution.records.length = count :=
          ReferenceActivePhysicalHorizon.run_record_count initial z.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s count hspan
            (generatedLaunchActive rate z rewards C_star C_h hc s hsElapsed)
        have hk : k < count := by simpa [window, execution] using hshort
        omega) ∧
      cut.input.time.val = s + k ∧
      cut.input.state = prefixRun.finalState ∧
      cut.input.rows = z.1.2 ∧
      cut.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p z ∧
      cut.input.rewards = rewards ∧
      ∃ r q base,
        cut.input.state.coordinator = .live r q base ∧
        r.payload.sigma.val = s ∧
        ∃ dispatched hstart ledger hinit hledger hdomain hclock hpending hnoAssignment selected,
          cut.output.preparation.coordinator = .live r q base
            (.cutoffChosen dispatched hstart ledger hinit hledger hdomain hclock hpending
              hnoAssignment selected) ∧
          let u := s + k + 1
          u = cut.input.time.val + 1 ∧
          u ≤ p.T ∧
          u ≤ r.gridBoundary ∧
          ledger.sigma = r.payload.sigma.val + 1 ∧
          ledger.cutoff = u ∧
          ∃ recording,
            ReferenceCoordinatorRecorderCallTrace.actualBranchInput cut =
              some (CoordinatorRecorderComplementBridge.recorderInput
                (collectionRecordingInput cut.output.preparation r.payload
                  dispatched.startResult (liveRegistersAt r cut.input.time).complementWeights)) ∧
            ReferenceCoordinatorRecorderCallTrace.recording
              (ReferenceActiveHorizonMeasurability.roundRecordCode cut) = some recording ∧
            cut.coordinatorDiagnostics.recording = some recording ∧
            CoordinatorRecordingOperation.run
              (CoordinatorRecorderComplementBridge.recorderInput
                (collectionRecordingInput cut.output.preparation r.payload
                  dispatched.startResult (liveRegistersAt r cut.input.time).complementWeights)) =
              some recording ∧
            ∃ ledgerStarted,
              CoordinatorCollectionLedger.startRound (sharedLedger ledger) (cut.input.time.val + 1)
                (collectionEnabled (sharedLedger ledger) cut.input.time)
                (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) =
                  .success ledgerStarted ∧
              ledgerStarted = CoordinatorCollectionLedger.startRoundCandidate (sharedLedger ledger)
                cut.input.time (collectionEnabled (sharedLedger ledger) cut.input.time)
                (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) ∧
              ∃ input decoded bank diagnostic finished,
                input = ReferenceUpReception.receptionInputAtRow rate cut.input.row
                  (upInputs cut.output.preparation ledgerStarted) cut.input.time ∧
                CoordinatorUpReception.receptionInputDomain input ∧
                CoordinatorUpReception.receptionInputCheck input = true ∧
                CoordinatorUpReception.decoderTransition input =
                  (⟨if CoordinatorUpReception.receptionGate input ∧
                      0 < input.ownObservation.val then
                        [AffineBatchDecoder.entry p (CoordinatorUpReception.traceAt input) input.time]
                      else [], []⟩, none) ∧
                AffineBatchDecoder.quota p > 1 ∧
                decoded = { input.ledger with phase := CoordinatorCollectionLedger.Phase.decoded } ∧
                (receiveUp cut.output.preparation ledgerStarted).result = .rejected (decoded, bank) ∧
                bank = CoordinatorUpReception.decoderBankAfter input ∧
                bank = Function.update input.upDecoderBank input.selectedFollower
                  (CoordinatorUpReception.decoderTransition input).1 ∧
                (∀ i, i ≠ input.selectedFollower → bank i = input.upDecoderBank i) ∧
                ReferenceUpReception.rawParsedOutput rate input = none ∧
                (receiveUp cut.output.preparation ledgerStarted).diagnostic = some diagnostic ∧
                diagnostic.input = input ∧
                diagnostic.expected = upExpected cut.output.preparation ∧
                diagnostic.decoderAfter = (CoordinatorUpReception.decoderTransition input).1 ∧
                diagnostic.raw = none ∧ diagnostic.parsed = none ∧
                diagnostic.locallyAccepted = false ∧
                diagnostic.wrongUniqueAccepted = false ∧
                CoordinatorCollectionLedger.finishRound decoded = .success finished ∧
                CoordinatorCollectionLedger.validLedgerCheck finished = true ∧
                (∀ pending : Finset (Fin (p.m - 1)),
                  ∃ clockFinished,
                    CoordinatorPhaseClock.finishRound p rate.eta.val cut.input.time
                      dispatched.startResult.clock pending cut.input.row = .ok clockFinished ∧
                    clockFinished.clock = dispatched.startResult.clock ∧
                    clockFinished.pending = pending ∧
                    clockFinished.ledgerCommand =
                      some (.accumulateLocalServiceAt cut.input.time)) ∧
                cut.output.coordinator.configuration =
                  .collection r.payload finished dispatched.startResult.clock.lastProposal ∧
                cut.output.coordinator.failure = none ∧
                cut.output.coordinator.upDecoderBank = bank ∧
                cut.output.coordinator.recording = some recording ∧
                cut.output.coordinator.up = some diagnostic ∧
                cut.output.next.coordinator =
                  .collection r.payload finished dispatched.startResult.clock.lastProposal ∧
                cut.output.next.upDecoderBank = bank ∧
                successorRun.finalState = cut.output.next ∧
                successorRun.finalState.coordinator =
                  .collection r.payload finished dispatched.startResult.clock.lastProposal ∧
                successorRun.finalState.upDecoderBank = bank ∧
                finished.phase = .ready ∧
                finished.sigma = s + 1 ∧ finished.cutoff = u ∧
                finished.cursor = u + 1 ∧
                finished.freezeAt = FollowerCutoffScan.gridBoundary p rate.eta.val r.payload.sigma ∧
                finished.freezeAt ≤ p.T + 1 ∧
                finished.assignment.arm = r.payload.assignment.assigned ∧
                finished.baseScore = (fun _ : Fin (p.m - 1) => (0 : ℕ)) ∧
                (∀ a : Fin p.K, r.payload.anchor a = 1) ∧
                r.payload.n = rate.n ∧
                finished.pending = Finset.univ ∧ finished.pending.Nonempty ∧
                1 ≤ finished.sigma ∧ finished.sigma ≤ p.T ∧
                finished.sigma < finished.cutoff ∧
                finished.sigma = r.payload.sigma.val + 1 ∧
                1 ≤ finished.cutoff ∧ finished.cutoff ≤ p.T ∧
                finished.cutoff ≤ finished.freezeAt ∧
                finished.cutoff < finished.cursor ∧ finished.cursor ≤ p.T + 1 ∧
                (∀ a, (finished.currentRegisters a = none ↔
                    CoordinatorCollectionLedger.armPending finished a) ∧
                  (finished.cutoffRegisters a = none ↔
                    CoordinatorCollectionLedger.armPending finished a)) ∧
                (∀ a, finished.gammaLoc a = 0 ∧
                  (CoordinatorCollectionLedger.armPending finished a → finished.increment a = 0)) ∧
                (∀ a c, finished.cutoffRegisters a = some c →
                  c.score + c.queue ≤ (finished.cutoff - finished.sigma) * D p ∧
                  c.lastService ≤ D p) ∧
                (∀ a c qNew, finished.cutoffRegisters a = some c →
                  finished.currentRegisters a = some qNew →
                  qNew.lastService ≤ D p ∧
                  c.score + finished.increment a + qNew.queue ≤
                    (finished.cursor - finished.sigma) * D p) ∧
                (∀ a c qNew, finished.cutoffRegisters a = some c →
                  finished.currentRegisters a = some qNew →
                  c.score + finished.increment a ≤
                    4 * rate.n * (min finished.cursor finished.freezeAt - finished.sigma)) ∧
                (∀ a r amount, finished.rawBuffer a r = some amount →
                  0 < amount ∧ amount ≤ D p ∧ finished.cutoff ≤ r.val + 1 ∧
                  r.val + 1 < min finished.cursor finished.freezeAt ∧
                  CoordinatorCollectionLedger.armPending finished a) ∧
                (∀ r, finished.enabledHistory r =
                  if finished.cutoff ≤ r.val + 1 ∧ r.val + 1 < finished.cursor then
                    some (decide (r.val + 1 < finished.freezeAt)) else none) ∧
                finished.enabledHistory cut.input.time = some (decide (u < finished.freezeAt)) ∧
                (∀ r, r ≠ cut.input.time → finished.enabledHistory r = none) ∧
                (∀ a r, r ≠ cut.input.time → finished.rawBuffer a r = none) ∧
                (∀ a r, u < r.val + 1 → finished.rawBuffer a r = none) ∧
                (∀ i : Fin (p.m - 1),
                  (bank i).pending.length < AffineBatchDecoder.quota p ∧
                  (∀ batch, batch ∈ (bank i).completed → batch.length = AffineBatchDecoder.quota p) ∧
                  (i ∉ finished.pending → (bank i).pending = [])) ∧
                (u = p.T → finished.cursor = p.T + 1) ∧
                (∀ hu : u < p.T,
                  let next := roundInputAt initial z.1.2
                    (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s
                    (generatedLaunchActive rate z rewards C_star C_h hc s hsElapsed)
                    successorRun ⟨u, by omega, hu⟩
                  ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain
                    next r.payload finished dispatched.startResult.clock.lastProposal ∧
                  ∀ hmore : k + 1 < count,
                    next = (execution.records[k + 1]'(by
                      have hlen := run_record_count initial z.1.2
                        (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s count hspan
                        (generatedLaunchActive rate z rewards C_star C_h hc s hsElapsed)
                      change execution.records.length = count at hlen
                      omega)).input) := by
  classical
  let initial := ReferenceFirstLaunchNumericalCell.launchState rate z rewards C_star C_h hc
  let active := generatedLaunchActive rate z rewards C_star C_h hc s hsElapsed
  let execution := generatedFirstCutoffRun rate z rewards C_star C_h hc s hsElapsed count hspan
  let window := firstLiveWindow execution.records
  let k := window.length
  have hk : k < count := hshort
  have hprefixSpan : s + k ≤ p.T := by omega
  have hsuccessorSpan : s + (k + 1) ≤ p.T := by omega
  let prefixRun := run initial z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)
    rewards s k hprefixSpan active
  let successorRun := run initial z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)
    rewards s (k + 1) hsuccessorSpan active
  have hE := ReferenceGeneratedFirstCutoffCoordinatorEndpoint.actual_first_cutoff_coordinator_endpoint
    rate z rewards C_star C_h hc s hsElapsed count hspan hshort
  dsimp only at hE
  rcases hE with ⟨hsT, cut, suffix, hsplit, hindex, htime, hstate, hrows, hselected,
    hrewards, r, q, base, hlive, hsigma, dispatched, hstart, ledger, hinit, hledger,
    hdomain, hclock, hpending, hnoAssignment, selected, hbranch, huTime, huT, hug,
    hledgerSigma, hledgerCut, o, hactualInput, htrace, hrecording, hrecorder,
    started, hstartSuccess, hstartCandidate, input, decoded, bank, diagnostic, finished,
    hinput, hinputDomain, hinputCheck, htransition, hquota, hdecoded, hreceive,
    hbank, hbankUpdate, hbankFrame, hrawParsed, hreceiveDiagnostic, hdiagnosticInput,
    hdiagnosticExpected, hdiagnosticAfter, hdiagnosticRaw, hdiagnosticParsed,
    hdiagnosticAccepted, hdiagnosticWrong, hfinish, hvalid, hclockFinish,
    hconfiguration, hfailure, hcommitted, hrecordingOut, hupOut, hnext, hnextBank,
    hsuccessor, hsuccessorCoordinator, hsuccessorBank, _⟩
  have hseed := ReferenceFirstLaunchNumericalCell.actual_launch_seed
    rate z rewards C_star C_h hc
  have hfirst : initial.coordinator = .first := hseed.2.2.2.1
  have hO := ReferenceFirstCutoffOutsideInitialization.run_first_cutoff_outside_initializer
    initial z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s count
    hspan active hfirst hshort
  dsimp only at hO
  rcases hO with ⟨cutO, suffixO, hsplitO, hindexO, htimeO, hactualO, rO, qO, baseO,
    hstateO, hliveO, dispatchedO, hstartO, ledgerO, hinitO, hledgerO, hdomainO,
    hclockO, hpendingO, hnoAssignmentO, selectedO, hbranchO, hkpos, hsigmaO,
    hbase, hbirth, hproposals, hreplay, huO, hsigmaBefore, huTO, hugO, hgTO,
    hσO, huLedgerO, hgLedgerO, hcutoffO, houtsideNone, houtsideSome,
    hcutoffRegisters, hcurrentRegisters, hbaseLedger, hpendingLedger, hincLedger,
    hgammaLedger, hrawLedger, hhistoryLedger, hcursorLedger, hphaseLedger, _⟩
  have hcutO : cutO = cut := hindexO.trans hindex.symm
  clear hindexO hactualO
  subst cutO
  have hOlive : cut.input.state.coordinator = .live rO qO baseO := by
    rw [hstateO]
    exact hliveO
  have htags := hlive.symm.trans hOlive
  cases htags
  have houtcome := hbranch.symm.trans hbranchO
  cases houtcome
  let l := sharedLedger ledger
  have hσ : l.sigma = r.payload.sigma.val + 1 := hledgerSigma
  have hu : l.cutoff = cut.input.time.val + 1 := by
    exact hledgerCut.trans huTime
  have hg : l.freezeAt = r.gridBoundary := hgLedgerO
  have htimeNamed : cut.input.time.val = s + k := htime
  have hσNamed : l.sigma = s + 1 := hσ.trans (congrArg (fun v => v + 1) hsigma)
  have huNamed : l.cutoff = s + k + 1 := hledgerCut
  have hlength : l.cutoff - l.sigma = k := by
    rw [huNamed, hσNamed]
    omega
  have hσpos : 1 ≤ l.sigma := by rw [hσNamed]; omega
  have hσu : l.sigma < l.cutoff := by
    rw [hσ, hu]
    exact hsigmaBefore
  have hinc : l.increment = fun _ => 0 := hincLedger
  have hcur : l.currentRegisters = fun a =>
      (l.cutoffRegisters a).map (fun c => ⟨c.queue, c.lastService⟩) := by
    change ledger.currentRegisters = fun a => (ledger.cutoffRegisters a).map
      (fun c => (⟨c.queue, c.lastService⟩ : CoordinatorCollectionLedger.CurrentRegister))
    rw [hcurrentRegisters, hcutoffRegisters]
  have hprefix : prefixRun.finalState.coordinator = .live r q base := by
    rw [← hstate]
    exact hlive
  have hmassRun := ReferenceFirstComplementMassBudget.run_first_complement_mass
    initial z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s count
    hspan active hfirst k (Nat.le_of_lt hk) (by rfl)
  change (match prefixRun.finalState.coordinator with
    | .first => k = 0 | .collection _ _ _ => False | .dagger => True
    | .live r q base => _) at hmassRun
  rw [hprefix] at hmassRun
  have houtsideBudgets := outside_register_budgets r q cut.input.time window k
    hmassRun.1 hmassRun.2.1 (fun a => ⟨(hreplay a).1, (hreplay a).2.2.1⟩)
  have hmass : ∀ a c, l.cutoffRegisters a = some c →
      c.score + c.queue ≤ (l.cutoff - l.sigma) * D p ∧ c.lastService ≤ D p := by
    intro a c hcReg
    change ledger.cutoffRegisters a = some c at hcReg
    rw [hcutoffRegisters] at hcReg
    simpa only [hlength] using (houtsideBudgets a c hcReg).1
  have hcap : ∀ a c, l.cutoffRegisters a = some c →
      c.score ≤ 4 * rate.n * (l.cutoff - l.sigma) := by
    intro a c hcReg
    change ledger.cutoffRegisters a = some c at hcReg
    rw [hcutoffRegisters] at hcReg
    simpa only [hlength] using (houtsideBudgets a c hcReg).2
  have hinputLedger : input.ledger = started := by rw [hinput]; rfl
  have hfinished : finished = CoordinatorCollectionLedger.finishRoundCandidate
      { started with phase := CoordinatorCollectionLedger.Phase.decoded } := by
    rw [finish_eq_candidate decoded finished hfinish, hdecoded, hinputLedger]
  have hf : finished = CoordinatorCollectionLedger.finishRoundCandidate
      { CoordinatorCollectionLedger.startRoundCandidate l cut.input.time (collectionEnabled l cut.input.time)
          (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder o) with
        phase := CoordinatorCollectionLedger.Phase.decoded } := by
    rw [hfinished, hstartCandidate]
  have hphase : finished.phase = .ready := by rw [hf]; rfl
  have hfsigma : finished.sigma = l.sigma := by rw [hf]; rfl
  have hfcut : finished.cutoff = l.cutoff := by rw [hf]; rfl
  have hfcursor : finished.cursor = cut.input.time.val + 2 := by rw [hf]; rfl
  have hffreeze : finished.freezeAt = l.freezeAt := by rw [hf]; rfl
  have hfpending : finished.pending = Finset.univ := by rw [hf]; exact hpendingLedger
  have hfassignment : finished.assignment.arm = r.payload.assignment.assigned := by
    rw [hf]
    change ledger.assignment.arm = _
    rw [hledger]
    rfl
  have hfbase : finished.baseScore = fun _ => 0 := by
    rw [hf]
    change ledger.baseScore = _
    rw [hbaseLedger]
    exact funext hbase
  have hnonempty : finished.pending.Nonempty := by
    rw [hfpending]
    exact ⟨⟨0, by have hm := p.two_le_m; omega⟩, Finset.mem_univ _⟩
  obtain ⟨hoptions, hzero, hraw⟩ := checked_ready_fields finished hvalid hphase
  have hbudgets := cutoff_finish_budgets l cut.input.time o hσpos (by omega) hu
    (by rw [hg, hu]; exact huTime.symm.trans_le hug) hinc hcur hmass hcap
  dsimp only at hf hbudgets
  rw [← hf] at hbudgets
  have hcutMass : ∀ a c, finished.cutoffRegisters a = some c →
      c.score + c.queue ≤ (finished.cutoff - finished.sigma) * D p ∧ c.lastService ≤ D p := by
    simpa only [hf, CoordinatorCollectionLedger.finishRoundCandidate,
      CoordinatorCollectionLedger.startRoundCandidate] using hmass
  have hpaired : ∀ a c qNew, finished.cutoffRegisters a = some c →
      finished.currentRegisters a = some qNew → qNew.lastService ≤ D p ∧
      c.score + finished.increment a + qNew.queue ≤ (finished.cursor - finished.sigma) * D p := by
    intro a c qNew hcReg hq
    have hb := hbudgets a c qNew hcReg hq
    exact ⟨hb.1, by simpa only [hfcursor, hfsigma] using hb.2.1⟩
  have hservice : ∀ a c qNew, finished.cutoffRegisters a = some c →
      finished.currentRegisters a = some qNew → c.score + finished.increment a ≤
        4 * rate.n * (min finished.cursor finished.freezeAt - finished.sigma) := by
    intro a c qNew hcReg hq
    simpa only [hfcursor, hffreeze, hfsigma] using (hbudgets a c qNew hcReg hq).2.2
  have hclockSeed : ReferenceCoordinatorClockDomains.clockAt z.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p z) s initial := by
    simp only [ReferenceCoordinatorClockDomains.clockAt, hfirst]
  have hrunClock := (ReferenceRunClockPreservation.run_clockAt initial z.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s (k + 1)
    hsuccessorSpan active hclockSeed).1
  change ReferenceCoordinatorClockDomains.clockAt _ _ _ successorRun.finalState at hrunClock
  have hsuccessorCoordinatorNamed : successorRun.finalState.coordinator =
      .collection r.payload finished dispatched.startResult.clock.lastProposal := hsuccessorCoordinator
  have hsuccessorBankNamed : successorRun.finalState.upDecoderBank = bank := hsuccessorBank
  simp only [ReferenceCoordinatorClockDomains.clockAt, hsuccessorCoordinatorNamed] at hrunClock
  have hgrid := hrunClock.2.2.2.2.2.1
  have hgridT := hrunClock.2.2.2.2.2.2.2
  obtain ⟨birth, hbirthMem, hborn, hbirthTime, installed, birthSelection, hchosen, hwhole⟩ := hbirth
  have hdispatchBirth : CoordinatorRoundDispatch.dispatchFirst (firstInput birth.input) =
      .chosen installed birthSelection := by
    have hprep : birth.output.preparation = prepare birth.input := by rw [birth.output_eq]; rfl
    rw [hprep] at hchosen
    change dispatch birth.input = _ at hchosen
    cases hcBirth : birth.input.state.coordinator with
    | first =>
      rw [dispatch_first birth.input hcBirth] at hchosen
      exact DispatchCut.first.inj hchosen
    | live rr qq bb =>
      simp only [dispatch, hcBirth, CoordinatorRoundDispatch.dispatch] at hchosen
      cases hchosen
    | collection payload old saved =>
      simp only [dispatch, hcBirth, CoordinatorRoundDispatch.dispatch] at hchosen
      split at hchosen <;> cases hchosen
    | dagger =>
      simp only [dispatch, hcBirth] at hchosen
      cases hchosen
  have hanchor : ∀ a, r.payload.anchor a = 1 := by
    intro a
    rw [← hwhole, dispatchFirst_chosen_installation birth.input installed birthSelection hdispatchBirth]
    exact CoordinatorAssignmentRegisterInstall.first_payload_anchor_one _ a
  have hbankSeed : ReferenceUpDecoderBankInvariant.upBankInvariant initial := by
    change ReferenceUpDecoderBankInvariant.coordinatorBankInvariant initial.coordinator initial.upDecoderBank
    rw [hfirst, hseed.2.2.2.2.1]
    exact ⟨CoordinatorUpReception.initialUpDecoderBank_wellFormed p, fun _ => rfl⟩
  have hbankRun := ReferenceUpDecoderBankInvariant.run_upBankInvariant initial z.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s (k + 1)
    hsuccessorSpan active hbankSeed
  change ReferenceUpDecoderBankInvariant.coordinatorBankInvariant
    successorRun.finalState.coordinator successorRun.finalState.upDecoderBank at hbankRun
  rw [hsuccessorCoordinatorNamed, hsuccessorBankNamed] at hbankRun
  have hbankFields : ∀ i : Fin (p.m - 1),
      (bank i).pending.length < AffineBatchDecoder.quota p ∧
      (∀ batch, batch ∈ (bank i).completed → batch.length = AffineBatchDecoder.quota p) ∧
      (i ∉ finished.pending → (bank i).pending = []) := by
    intro i
    exact ⟨(hbankRun.1 i).1, (hbankRun.1 i).2, hbankRun.2 i⟩
  obtain ⟨hhistory, hhistoryAtTime, hhistoryOther, hrawOther, hfutureTime⟩ :=
    initial_finish_history l cut.input.time o finished hσpos hu hrawLedger hhistoryLedger hf
  have hhistoryAt : finished.enabledHistory cut.input.time =
      some (decide (s + k + 1 < finished.freezeAt)) := by
    simpa only [htimeNamed] using hhistoryAtTime
  have hfuture : ∀ a j, s + k + 1 < j.val + 1 → finished.rawBuffer a j = none := by
    simpa only [htimeNamed] using hfutureTime
  have hfSigmaNamed : finished.sigma = s + 1 := hfsigma.trans hσNamed
  have hfCutNamed : finished.cutoff = s + k + 1 := hfcut.trans huNamed
  have hfCursorNamed : finished.cursor = s + k + 2 :=
    hfcursor.trans (congrArg (fun v => v + 2) htimeNamed)
  have hfSigmaPayload : finished.sigma = r.payload.sigma.val + 1 := hfsigma.trans hσ
  have hfBefore : finished.sigma < finished.cutoff := by
    rw [hfsigma, hfcut]
    exact hσu
  have huTNamed : s + k + 1 ≤ p.T := huT
  have hugNamed : s + k + 1 ≤ r.gridBoundary := hug
  have hfCutT : finished.cutoff ≤ p.T := hfCutNamed.trans_le huTNamed
  have hfCutGrid : finished.cutoff ≤ finished.freezeAt := by
    rw [hfcut, hffreeze, hg]
    exact huNamed.trans_le hugNamed
  obtain ⟨hfSigmaPos, hfSigmaT, hfBefore, hfSigmaPayload, hfCutPos, hfCutT,
    hfCutGrid, hfCursorAfter, hfCursorT, hfTerminal⟩ :=
    boundary_time_fields p.T finished.sigma finished.cutoff finished.cursor finished.freezeAt
      r.payload.sigma.val s k hfSigmaNamed hfCutNamed hfCursorNamed hfSigmaPayload hfBefore hfCutT hfCutGrid
  have hbankStateFields : ∀ i : Fin (p.m - 1),
      (successorRun.finalState.upDecoderBank i).pending.length < AffineBatchDecoder.quota p ∧
      (∀ batch, batch ∈ (successorRun.finalState.upDecoderBank i).completed →
        batch.length = AffineBatchDecoder.quota p) ∧
      (i ∉ finished.pending → (successorRun.finalState.upDecoderBank i).pending = []) := by
    simpa only [hsuccessorBankNamed] using hbankFields
  have hnextReady : ∀ hu : s + k + 1 < p.T,
      let next := roundInputAt initial z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)
        rewards s active successorRun ⟨s + k + 1, by omega, hu⟩
      ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain
        next r.payload finished dispatched.startResult.clock.lastProposal := by
    intro hu
    dsimp only
    exact ⟨hsuccessorCoordinatorNamed, hphase, hfSigmaPos, hfSigmaT, hfBefore,
      hfSigmaPayload, hfCutPos, hfCutT, hfCutGrid, hgridT, hgrid, hfCursorNamed,
      hfCursorAfter, hfCursorT, hfassignment, hfbase, hanchor, payload_n_eq r.payload,
      hnonempty, hoptions, hzero, hcutMass, hpaired, hservice, hraw, hhistory, hbankStateFields⟩
  refine ⟨hsT, cut, suffix, hsplit, hindex, htime, hstate, hrows, hselected, hrewards,
    r, q, base, hlive, hsigma, dispatched, hstart, ledger, hinit, hledger, hdomain,
    hclock, hpending, hnoAssignment, selected, hbranch, huTime, huT, hug,
    hledgerSigma, hledgerCut, o, hactualInput, htrace, hrecording, hrecorder,
    started, hstartSuccess, hstartCandidate, input, decoded, bank, diagnostic, finished,
    hinput, hinputDomain, hinputCheck, htransition, hquota, hdecoded, hreceive,
    hbank, hbankUpdate, hbankFrame, hrawParsed, hreceiveDiagnostic, hdiagnosticInput,
    hdiagnosticExpected, hdiagnosticAfter, hdiagnosticRaw, hdiagnosticParsed,
    hdiagnosticAccepted, hdiagnosticWrong, hfinish, hvalid, hclockFinish,
    hconfiguration, hfailure, hcommitted, hrecordingOut, hupOut, hnext, hnextBank,
    hsuccessor, hsuccessorCoordinator, hsuccessorBank, hphase, hfSigmaNamed, hfCutNamed, hfCursorNamed, hgrid,
    hgridT, hfassignment, hfbase, hanchor, payload_n_eq r.payload, hfpending, hnonempty,
    hfSigmaPos, hfSigmaT, hfBefore, hfSigmaPayload, hfCutPos, hfCutT, hfCutGrid,
    hfCursorAfter, hfCursorT, hoptions, hzero, hcutMass, hpaired, hservice,
    hraw, hhistory, hhistoryAt, hhistoryOther, hrawOther, hfuture, hbankFields, ?_, ?_⟩
  · intro hterminal
    exact hfTerminal (hfCutNamed.trans hterminal)
  intro hu
  refine ⟨hnextReady hu, ?_⟩
  intro hmore
  exact next_input_eq_record initial z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)
    rewards s count (k + 1) hspan active hmore

end Bandits.Support.ReferenceFirstCollectionReadyInitialization
