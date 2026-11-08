/-
Copyright (c) 2026 Bandits Lean regret formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.CoordinatorPhaseClock
public import Bandits.Support.CoordinatorLocalArmChoice
public import Bandits.Support.AssignmentStartPayload
public import Bandits.Support.CoordinatorRecorderComplementBridge
public import Bandits.Support.CoordinatorRecordingMeasurability
public import Bandits.Support.CoordinatorCollectionLedger
public import Bandits.Support.CoordinatorUpReception
public import Bandits.Support.CoordinatorUpMeasurability
public import Bandits.Support.AssignmentScoreReconstruction
public import Bandits.Support.CoordinatorRecordingOperation
public import Bandits.Support.ScoreWeights
public import Bandits.Support.CompletePublicTable

import Lean.Elab.Tactic.Omega

/-!
# One checked coordinator collection round with local UP reception

This module composes the source's existing row-based coordinator arm choice,
one own-row complement recorder call, known-queue service and unknown-arrival
buffering, the actual local UP DecodeStep, and ledger/clock finishing in
source order. The input is one already-ready collection ledger and one supplied
complete coordinator row. All carried-state compatibility, local source-time,
rate, register, and envelope conditions remain explicit.

Sources: sources/zip4/manuscript/06_interruptions.tex:9-14,37-70,235-296,
sources/zip4/manuscript/05_binary_transport.tex:74-120,352-429, and
sources/zip4/manuscript/appendix_a_local_protocol.tex:8-14.

This is a one-row internal operation. It establishes no physical row, sender,
raw-buffer, score, queue, or envelope provenance and makes no reachable-run or
manuscript-closure claim.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.CoordinatorCollectionUpRoundStep

open Bandits.Support.ConstructorDimensions
open Bandits.Support.CompletePublicTable
open Bandits.Support.CoordinatorCollectionLedger
open Bandits.Support.CoordinatorPhaseClock
open Bandits.Support.CoordinatorLocalArmChoice
open Bandits.Support.AssignmentStartPayload
open Bandits.Support.CoordinatorRecorderComplementBridge
open Bandits.Support.CoordinatorUpReception
open Bandits.Support.CoordinatorUpMeasurability
open Bandits.Support.AssignmentScoreReconstruction
open Bandits.Support.ScoreWeights
open Bandits.Support.CanonicalRecordingRates
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.QueueReplay

abbrev Parameters := ConstructorDimensions.Parameters

/-- The source one-based round denoted by a calendar index. -/
def sourceRound {p : Parameters} (t : Fin p.T) : ℕ := t.val + 1

/-- The collection cutoff endpoint stored by the old phase clock. -/
def sourceCutoff {p : Parameters} (u : Fin p.T) : ℕ := u.val + 1

/-- Convert the old clock's zero-based cutoff index to the accepted activation
carrier used by local arm choice. -/
def localCutoff {p : Parameters} (u : Fin p.T) : Cutoff p :=
  ⟨sourceCutoff u, by
    constructor
    · simp [sourceCutoff]
    · have hu := u.isLt
      simp only [sourceCutoff]
      omega⟩

@[simp] theorem localCutoff_round {p : Parameters} (u : Fin p.T) :
    CoordinatorLocalArmChoice.cutoffRound (some (localCutoff u)) = sourceCutoff u := rfl

/-- The payload's source learning cap, transported to the shared real rate. -/
theorem payloadSourceCap {p : Parameters} {eta : ℝ} {heta : 0 < eta}
    (s : AssignmentStartPayload.Input p (⟨eta, heta⟩ : LearningRate)) :
    CoordinatorCollectionLedger.sourceLearningCap p eta :=
  s.eta_le_source_cap

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
    {p : Parameters} {eta : ℝ} {heta : 0 < eta}
    {hcap : CoordinatorCollectionLedger.sourceLearningCap p eta}
    {n : ℕ} {hn : (n : ℝ) = eta * (ConstructorDimensions.D p : ℝ)}
    (l : CoordinatorCollectionLedger.Ledger p eta heta hcap n hn) (a : Fin p.K) :
    CoordinatorCollectionLedger.armPendingCheck l a = true ↔
      CoordinatorCollectionLedger.armPending l a := by
  unfold CoordinatorCollectionLedger.armPendingCheck
  unfold CoordinatorCollectionLedger.anyFin
  rw [List.any_eq_true]
  simp [CoordinatorCollectionLedger.armPending]

/-- The numeric and register-consistency conjuncts extracted directly from a
valid ledger check. -/
private theorem validLedger_registerFacts
    {p : Parameters} {eta : ℝ} {heta : 0 < eta}
    {hcap : CoordinatorCollectionLedger.sourceLearningCap p eta}
    {n : ℕ} {hn : (n : ℝ) = eta * (ConstructorDimensions.D p : ℝ)}
    (l : CoordinatorCollectionLedger.Ledger p eta heta hcap n hn)
    (hvalid : CoordinatorCollectionLedger.validLedger l) :
    (1 ≤ l.sigma ∧ l.sigma ≤ p.T ∧ 1 ≤ l.cutoff ∧
      l.cutoff ≤ l.freezeAt ∧ l.cutoff ≤ p.T ∧ l.freezeAt ≤ p.T + 1 ∧
      l.cutoff ≤ l.cursor ∧ l.cursor ≤ p.T + 1) ∧
    CoordinatorCollectionLedger.allFin p.K (fun a =>
      (l.currentRegisters a).isNone == CoordinatorCollectionLedger.armPendingCheck l a) = true ∧
    CoordinatorCollectionLedger.allFin p.K (fun a =>
      (l.cutoffRegisters a).isNone == CoordinatorCollectionLedger.armPendingCheck l a) = true ∧
    CoordinatorCollectionLedger.allFin p.K (fun a =>
      (!CoordinatorCollectionLedger.armPendingCheck l a) ||
        decide (l.gammaLoc a = 0)) = true := by
  have hcheck : CoordinatorCollectionLedger.validLedgerCheck l = true := hvalid
  simp only [CoordinatorCollectionLedger.validLedgerCheck, Bool.and_eq_true,
    decide_eq_true_eq] at hcheck
  constructor
  · tauto
  constructor
  · tauto
  constructor
  · tauto
  · tauto

/-- Every actual complement arm has known cutoff score and current queue
registers. This follows from ledger validity and the payload assignment-image
identity; unknown pending slow-arm registers remain options and are not filled
with defaults. -/
theorem complementRegisters_known
    {p : Parameters} {eta : ℝ} {heta : 0 < eta}
    {hcap : CoordinatorCollectionLedger.sourceLearningCap p eta}
    {n : ℕ} {hn : (n : ℝ) = eta * (ConstructorDimensions.D p : ℝ)}
    (l : CoordinatorCollectionLedger.Ledger p eta heta hcap n hn)
    (s : AssignmentStartPayload.Input p (⟨eta, heta⟩ : LearningRate))
    (hvalid : CoordinatorCollectionLedger.validLedger l)
    (hassignment : ∀ i : Fin (p.m - 1),
      l.assignment.arm i = s.assignment.assigned i)
    (a : Fin p.K) (ha : a ∉ s.slowSet.1) :
    ∃ cutoff : CoordinatorCollectionLedger.CutoffRegister,
      l.cutoffRegisters a = some cutoff ∧
    ∃ current : CoordinatorCollectionLedger.CurrentRegister,
      l.currentRegisters a = some current := by
  have hnotPending : ¬ CoordinatorCollectionLedger.armPending l a := by
    intro hpending
    rcases hpending with ⟨i, hi, harm⟩
    have hslow : s.assignment.assigned i ∈ s.slowSet.1 := by
      rw [← s.assignment_image]
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
    have hsame : s.assignment.assigned i = a := (hassignment i).symm.trans harm
    exact ha (hsame ▸ hslow)
  have hcheckFalse : CoordinatorCollectionLedger.armPendingCheck l a = false := by
    cases h : CoordinatorCollectionLedger.armPendingCheck l a with
    | false => rfl
    | true => exact False.elim (hnotPending
        ((armPendingCheck_eq_true_iff l a).mp h))
  rcases validLedger_registerFacts l hvalid with
    ⟨_, hcurrentAll, hcutoffAll, _⟩
  have hcurrentEntry := (allFin_eq_true_iff _).mp hcurrentAll a
  have hcutoffEntry := (allFin_eq_true_iff _).mp hcutoffAll a
  have hcurrentNone : (l.currentRegisters a).isNone = false := by
    simpa [hcheckFalse] using hcurrentEntry
  have hcutoffNone : (l.cutoffRegisters a).isNone = false := by
    simpa [hcheckFalse] using hcutoffEntry
  cases hcurrent : l.currentRegisters a with
  | none => simp [hcurrent] at hcurrentNone
  | some current =>
      cases hcutoff : l.cutoffRegisters a with
      | none => simp [hcutoff] at hcutoffNone
      | some cutoff => exact ⟨cutoff, rfl, current, rfl⟩

/-- The source score on a complement arm is the known cutoff score plus the
ledger's accumulated increment. -/
noncomputable def complementCurrentScore
    {p : Parameters} {eta : ℝ} {heta : 0 < eta}
    {hcap : CoordinatorCollectionLedger.sourceLearningCap p eta}
    {n : ℕ} {hn : (n : ℝ) = eta * (ConstructorDimensions.D p : ℝ)}
    (l : CoordinatorCollectionLedger.Ledger p eta heta hcap n hn)
    (s : AssignmentStartPayload.Input p (⟨eta, heta⟩ : LearningRate))
    (hvalid : CoordinatorCollectionLedger.validLedger l)
    (hassignment : ∀ i : Fin (p.m - 1),
      l.assignment.arm i = s.assignment.assigned i)
    (a : Fin p.K) (ha : a ∉ s.slowSet.1) : ℕ :=
  (Classical.choose (complementRegisters_known l s hvalid hassignment a ha)).score +
    l.increment a

/-- The literal source weight on an actual complement arm, using the accepted
(1 + 1/D)^z score base. -/
noncomputable def complementCurrentWeight
    {p : Parameters} {eta : ℝ} {heta : 0 < eta}
    {hcap : CoordinatorCollectionLedger.sourceLearningCap p eta}
    {n : ℕ} {hn : (n : ℝ) = eta * (ConstructorDimensions.D p : ℝ)}
    (l : CoordinatorCollectionLedger.Ledger p eta heta hcap n hn)
    (s : AssignmentStartPayload.Input p (⟨eta, heta⟩ : LearningRate))
    (hvalid : CoordinatorCollectionLedger.validLedger l)
    (hassignment : ∀ i : Fin (p.m - 1),
      l.assignment.arm i = s.assignment.assigned i)
    (a : Fin p.K) (ha : a ∉ s.slowSet.1) : ℝ :=
  ScoreWeights.scoreWeight (AssignmentScoreReconstruction.sourceWeightBase p)
    (complementCurrentScore l s hvalid hassignment a ha)

/-- Only the fast complement is materialized as a current weight function. -/
noncomputable def complementWeights
    {p : Parameters} {eta : ℝ} {heta : 0 < eta}
    {hcap : CoordinatorCollectionLedger.sourceLearningCap p eta}
    {n : ℕ} {hn : (n : ℝ) = eta * (ConstructorDimensions.D p : ℝ)}
    (l : CoordinatorCollectionLedger.Ledger p eta heta hcap n hn)
    (s : AssignmentStartPayload.Input p (⟨eta, heta⟩ : LearningRate))
    (hvalid : CoordinatorCollectionLedger.validLedger l)
    (hassignment : ∀ i : Fin (p.m - 1),
      l.assignment.arm i = s.assignment.assigned i) :
    CanonicalFastSampling.FastArm s.slowSet → ℝ :=
  fun j => complementCurrentWeight l s hvalid hassignment j.1
    (Finset.mem_sdiff.mp j.2).2

/-- One supplied source row and all carried state for a single collection
round. The payload is indexed by the LearningRate built from etaReal, while
the ledger uses that same real value and the single n/n_cast_identity pair. -/
structure Inputs (p : Parameters) where
  etaReal : ℝ
  etaPositive : 0 < etaReal
  n : ℕ
  n_cast_identity : (n : ℝ) = etaReal * (ConstructorDimensions.D p : ℝ)
  payload : AssignmentStartPayload.Input p (⟨etaReal, etaPositive⟩ : LearningRate)
  baseScores : Fin (p.m - 1) → ℕ
  ledger : CoordinatorCollectionLedger.Ledger p etaReal etaPositive
    (payloadSourceCap payload) n n_cast_identity
  clock : CoordinatorPhaseClock.ClockRegisters p
  upDecoderBank : CoordinatorUpReception.UpDecoderBank p
  cutoffIndex : Fin p.T
  time : Fin p.T
  row : CompletePublicTable.CompleteRow p
  ownObservation : Fin (ConstructorDimensions.D p + 1)

namespace Inputs

variable {p : Parameters} (x : Inputs p)

/-- The payload index and ledger index have the same source n. The equality
follows by casting both stored identities through the one shared real eta. -/
theorem payload_rate_eq_shared_rate :
    (⟨x.etaReal, x.etaPositive⟩ : LearningRate).val = x.etaReal := rfl

theorem payload_n_eq_ledger_n : x.payload.n = x.n := by
  have hcast : (x.payload.n : ℝ) = (x.n : ℝ) := by
    calc
      (x.payload.n : ℝ) = x.etaReal * (ConstructorDimensions.D p : ℝ) :=
        x.payload.n_eq_eta_mul_D
      _ = (x.n : ℝ) := x.n_cast_identity.symm
  exact_mod_cast hcast

/-- The exact source time of this one collection input. -/
def sourceTime : ℕ := CoordinatorCollectionUpRoundStep.sourceRound x.time

/-- Only this arm-indexed fast-complement weight function is passed to arm
choice and the recorder. -/
def weights (hvalid : CoordinatorCollectionLedger.validLedger x.ledger)
    (hassignment : ∀ i : Fin (p.m - 1),
      x.ledger.assignment.arm i = x.payload.assignment.assigned i) :=
  complementWeights x.ledger x.payload hvalid hassignment

end Inputs

/-- The local row and carried-register checks required to attempt one actual
checked collection round. These are operation-domain and state-matching facts,
not conclusions about a physical execution. -/
structure InputsValid {p : Parameters} (x : Inputs p) where
  ledger_valid : CoordinatorCollectionLedger.validLedger x.ledger
  ledger_ready : x.ledger.phase = CoordinatorCollectionLedger.Phase.ready
  pending_nonempty : x.ledger.pending.Nonempty
  assignment_eq : ∀ i : Fin (p.m - 1),
    x.ledger.assignment.arm i = x.payload.assignment.assigned i
  base_score_eq : x.ledger.baseScore = x.baseScores
  clock_parameter_valid : CoordinatorPhaseClock.proposalParameterValid p x.etaReal
  clock_registers_valid : CoordinatorPhaseClock.clockRegistersValid p x.etaReal x.clock
  clock_start_time_valid : CoordinatorPhaseClock.startRoundTimeValid p x.time x.clock
  clock_sigma_eq : x.clock.sigma = some x.payload.sigma
  clock_cutoff_eq : x.clock.u = some x.cutoffIndex
  ledger_sigma_eq : x.ledger.sigma =
    CoordinatorRecorderComplementBridge.sourceStart x.payload
  ledger_cutoff_eq : x.ledger.cutoff = sourceCutoff x.cutoffIndex
  ledger_freeze_eq : x.ledger.freezeAt = x.clock.g
  ledger_cursor_eq : x.ledger.cursor = sourceRound x.time
  decoder_bank_valid : CoordinatorUpReception.decoderBankCheck p x.upDecoderBank = true
  choice_valid : CoordinatorLocalArmChoice.ChoiceInputsValid x.payload
    (some (localCutoff x.cutoffIndex)) x.time
    (Inputs.weights (x := x) ledger_valid assignment_eq)

namespace InputsValid

variable {p : Parameters} {x : Inputs p}

/-- The collection ledger's own checked time tuple, unpacked from validity. -/
theorem ledger_time_bounds (h : InputsValid x) :
    1 ≤ x.ledger.sigma ∧ x.ledger.sigma ≤ p.T ∧
      1 ≤ x.ledger.cutoff ∧ x.ledger.cutoff ≤ x.ledger.freezeAt ∧
      x.ledger.cutoff ≤ p.T ∧ x.ledger.freezeAt ≤ p.T + 1 ∧
      x.ledger.cutoff ≤ x.ledger.cursor ∧ x.ledger.cursor ≤ p.T + 1 :=
  (validLedger_registerFacts x.ledger h.ledger_valid).1

/-- Every actual complement entry has both ledger registers present, despite
the still-pending slow-arm entries. -/
theorem complementRegisters_known (h : InputsValid x)
    (j : CanonicalFastSampling.FastArm x.payload.slowSet) :
    ∃ cutoff : CoordinatorCollectionLedger.CutoffRegister,
      x.ledger.cutoffRegisters j.1 = some cutoff ∧
    ∃ current : CoordinatorCollectionLedger.CurrentRegister,
      x.ledger.currentRegisters j.1 = some current :=
  CoordinatorCollectionUpRoundStep.complementRegisters_known x.ledger x.payload
    h.ledger_valid h.assignment_eq j.1 (Finset.mem_sdiff.mp j.2).2

/-- The source score/weight formulas for every actual complement arm. -/
theorem complement_score_formula (h : InputsValid x)
    (j : CanonicalFastSampling.FastArm x.payload.slowSet) :
    complementCurrentScore x.ledger x.payload h.ledger_valid h.assignment_eq j.1
      (Finset.mem_sdiff.mp j.2).2 =
      (Classical.choose (InputsValid.complementRegisters_known h j)).score + x.ledger.increment j.1 := rfl

theorem complement_weight_formula (h : InputsValid x)
    (j : CanonicalFastSampling.FastArm x.payload.slowSet) :
    complementCurrentWeight x.ledger x.payload h.ledger_valid h.assignment_eq j.1
      (Finset.mem_sdiff.mp j.2).2 =
      ScoreWeights.scoreWeight (AssignmentScoreReconstruction.sourceWeightBase p)
        (complementCurrentScore x.ledger x.payload h.ledger_valid h.assignment_eq j.1
          (Finset.mem_sdiff.mp j.2).2) := rfl

/-- The exact pre-choice clock result: the old cutoff is already in force,
so the pending collection continues and no new assignment is requested. -/
theorem startRound_frame (h : InputsValid x) :
    CoordinatorPhaseClock.startRound p x.etaReal x.time x.clock x.ledger.pending =
      .ok ⟨x.clock, CoordinatorPhaseClock.clockRegistersValid_gridDomain p x.etaReal
        x.clock h.clock_registers_valid, x.ledger.pending, none, none⟩ := by
  have hcutoffByTime : x.cutoffIndex.val ≤ x.time.val := by
    have hle := (InputsValid.ledger_time_bounds h).2.2.2.2.2.2.1
    rw [h.ledger_cutoff_eq, h.ledger_cursor_eq] at hle
    simp only [sourceCutoff, sourceRound] at hle
    omega
  exact CoordinatorPhaseClock.startRound_collection_pending p x.etaReal x.time
    x.payload.sigma x.cutoffIndex x.clock x.ledger.pending
    h.clock_parameter_valid h.clock_registers_valid h.clock_sigma_eq
    h.clock_cutoff_eq hcutoffByTime (by
      intro hempty
      rcases h.pending_nonempty with ⟨i, hi⟩
      rw [hempty] at hi
      simp at hi)

/-- Any successful collection stage-(1) result is the literal candidate from
the current zero-based calendar index. -/
theorem startRound_success_candidate
    {p : Parameters} {eta : ℝ} {heta : 0 < eta}
    {hcap : CoordinatorCollectionLedger.sourceLearningCap p eta}
    {n : ℕ} {hn : (n : ℝ) = eta * (ConstructorDimensions.D p : ℝ)}
    (l : CoordinatorCollectionLedger.Ledger p eta heta hcap n hn)
    (t : ℕ) (ht : 1 ≤ t) (hT : t ≤ p.T) (enabled : Bool)
    (raw : Option (Fin p.K × ℕ))
    (out : CoordinatorCollectionLedger.Ledger p eta heta hcap n hn)
    (h : CoordinatorCollectionLedger.startRound l t enabled raw = .success out) :
    out = CoordinatorCollectionLedger.startRoundCandidate l
      ⟨t - 1, by omega⟩ enabled raw := by
  classical
  unfold CoordinatorCollectionLedger.startRound at h
  let P := CoordinatorCollectionLedger.validLedgerCheck l = true ∧
      l.phase = .ready ∧ t = l.cursor ∧ 1 ≤ t ∧ t ≤ p.T ∧
        CoordinatorCollectionLedger.rawInputDomainCheck raw = true
  by_cases hinput : P
  · rw [dite_eq_left hinput] at h
    have ht : t = l.cursor := hinput.2.2.1
    subst t
    let r : Fin p.T := ⟨l.cursor - 1, by omega⟩
    cases hslot : CoordinatorCollectionLedger.rawSlotFreshCheck l r raw with
    | false => simp [r, hslot] at h
    | true =>
      cases hvalid : CoordinatorCollectionLedger.validLedgerCheck
          (CoordinatorCollectionLedger.startRoundCandidate l r enabled raw) with
      | false => simp [r, hslot, hvalid] at h
      | true =>
        simp [r, hslot, hvalid] at h
        exact h.symm
  · rw [dite_eq_right hinput] at h
    cases h

/-- A successful collection finish is the literal source stage-(3)
candidate; its only increment is the already-produced `gammaLoc`. -/
theorem finishRound_success_candidate
    {p : Parameters} {eta : ℝ} {heta : 0 < eta}
    {hcap : CoordinatorCollectionLedger.sourceLearningCap p eta}
    {n : ℕ} {hn : (n : ℝ) = eta * (ConstructorDimensions.D p : ℝ)}
    (l out : CoordinatorCollectionLedger.Ledger p eta heta hcap n hn)
    (h : CoordinatorCollectionLedger.finishRound l = .success out) :
    out = CoordinatorCollectionLedger.finishRoundCandidate l := by
  classical
  unfold CoordinatorCollectionLedger.finishRound at h
  let P := CoordinatorCollectionLedger.validLedgerCheck l = true ∧
      l.phase = .decoded ∧ l.cursor ≤ p.T
  by_cases hinput : P
  · rw [dite_eq_left hinput] at h
    cases hvalid : CoordinatorCollectionLedger.validLedgerCheck
        (CoordinatorCollectionLedger.finishRoundCandidate l) with
    | false => simp [hvalid] at h
    | true =>
      simp [hvalid] at h
      exact h.symm
  · rw [dite_eq_right hinput] at h
    cases h

/-- A successful UP ledger decode is exactly an `acceptUpCandidate` built
from the parser output and the replay prefix/current record read from that
same ledger. -/
theorem decodeUp_success_candidate
    {p : Parameters} {eta : ℝ} {heta : 0 < eta}
    {hcap : CoordinatorCollectionLedger.sourceLearningCap p eta}
    {n : ℕ} {hn : (n : ℝ) = eta * (ConstructorDimensions.D p : ℝ)}
    (l : CoordinatorCollectionLedger.Ledger p eta heta hcap n hn)
    (i : Fin (p.m - 1))
    (parsed : Option (OrdinaryMessageCodec.UpRecord
      (CoordinatorCollectionLedger.codecParams p eta)))
    (out : CoordinatorCollectionLedger.Ledger p eta heta hcap n hn)
    (hdomain : CoordinatorCollectionLedger.validLedgerCheck l = true ∧
      l.phase = .started ∧ 1 ≤ l.cutoff ∧ l.cutoff ≤ l.cursor ∧ l.cursor ≤ p.T)
    (h : CoordinatorCollectionLedger.decodeUp l i parsed = .success out) :
    ∃ M past current, parsed = some M ∧
      out = CoordinatorCollectionLedger.acceptUpCandidate l i M past current ∧
      CoordinatorCollectionLedger.replayRecords? l (l.assignment.arm i)
        (CoordinatorCollectionLedger.calendarIndices p.T (l.cutoff - 1)
          (l.cursor - l.cutoff) (by
            rcases hdomain with ⟨_, _, hcut, hcutCursor, hcursor⟩
            omega)) = some past ∧
      CoordinatorCollectionLedger.replayRecords? l (l.assignment.arm i)
        [⟨l.cursor - 1, by
          rcases hdomain with ⟨_, _, hcut, hcutCursor, hcursor⟩
          omega⟩] = some [current] := by
  classical
  cases parsed with
  | none =>
      unfold CoordinatorCollectionLedger.decodeUp at h
      rw [dite_eq_left hdomain] at h
      dsimp only at h
      split_ifs at h
  | some M =>
      unfold CoordinatorCollectionLedger.decodeUp at h
      rw [dite_eq_left hdomain] at h
      dsimp only at h
      by_cases haccept : CoordinatorCollectionLedger.acceptUpCheck l i M = true
      · by_cases hunknown : l.currentRegisters (l.assignment.arm i) = none ∧
            l.cutoffRegisters (l.assignment.arm i) = none
        · rw [ite_eq_left haccept, dite_eq_left hunknown] at h
          split at h
          · case h_1 pastOption lastOption past last hpast hlast =>
              cases last with
              | nil => simp at h
              | cons record tail =>
                  cases tail with
                  | nil =>
                      dsimp only at h
                      split_ifs at h
                      · injection h with hout
                        subst out
                        have hpast' :
                            CoordinatorCollectionLedger.replayRecords? l
                                (l.assignment.arm i)
                                (CoordinatorCollectionLedger.calendarIndices p.T
                                  (l.cutoff - 1) (l.cursor - l.cutoff) (by
                                    rcases hdomain with
                                      ⟨_, _, hcut, hcutCursor, hcursor⟩
                                    omega)) =
                              some past := by
                          simpa using hpast
                        have hlast' :
                            CoordinatorCollectionLedger.replayRecords? l
                                (l.assignment.arm i) [⟨l.cursor - 1, by
                                  rcases hdomain with
                                    ⟨_, _, hcut, hcutCursor, hcursor⟩
                                  omega⟩] =
                              some [record] := by
                          simpa using hlast
                        exact ⟨M, past, record, rfl, rfl, hpast', hlast'⟩
                  | cons record' tail' => simp at h
          · simp_all
        · rw [ite_eq_left haccept, dite_eq_right hunknown] at h
          cases h
      · rw [ite_eq_right haccept] at h
        split_ifs at h

/-- In an already-started collection round the phase-clock finish time check
is implied by the same clock's accepted start-time check. -/
theorem clock_finish_time_valid (h : InputsValid x) :
    CoordinatorPhaseClock.finishRoundTimeValid x.time x.clock := by
  have ht := h.clock_start_time_valid
  simp only [CoordinatorPhaseClock.startRoundTimeValid, h.clock_sigma_eq,
    h.clock_cutoff_eq] at ht
  simp only [CoordinatorPhaseClock.finishRoundTimeValid, h.clock_sigma_eq,
    h.clock_cutoff_eq]
  rcases ht with ⟨hsigma, hcutoff⟩
  exact ⟨by omega, hcutoff⟩

/-- The exact accepted complement recorder input. -/
def recorderInput (h : InputsValid x) (arm : Fin p.K) :
    CoordinatorRecorderComplementBridge.Input x.payload where
  currentWeights := Inputs.weights (x := x) h.ledger_valid h.assignment_eq
  time := x.time
  gridBoundary := x.ledger.freezeAt
  row := x.row
  ownArm := arm
  observation := x.ownObservation
  mode := .collection

/-- The recorder's explicit local boundary/envelope check follows from the
same actual complement envelope already supplied to arm choice and the
ledger's checked freeze range. -/
theorem recorderInput_valid (h : InputsValid x) (arm : Fin p.K) :
    CoordinatorRecorderComplementBridge.LocalInputsValid (recorderInput (x := x) h arm) := by
  refine ⟨(InputsValid.ledger_time_bounds h).2.2.2.2.2.1, ?_⟩
  intro j
  exact ⟨h.choice_valid.anchor_le_current j, h.choice_valid.current_le_twice_anchor j⟩

/-- The literal source enable bit in collection: the collection ledger is
active after cutoff, and coordinator queue service is enabled before the
inclusive freeze boundary. The recorder gate is a separate option. -/
def sourceLearningEnabled (x : Inputs p) : Bool :=
  decide (0 < x.ledger.sigma ∧ x.ledger.cutoff ≤ sourceRound x.time ∧
    sourceRound x.time < x.ledger.freezeAt)

/-- Route a successful recorder output through its actual gate arm. some arm
is retained when the floored arrival is zero; only gate failure becomes none. -/
def rawInputOfRecorder (output : CoordinatorRecordingOperation.Output p) :
    Option (Fin p.K × ℕ) :=
  output.gateArm.map fun arm => (arm, output.rawArrival)

/-- The single ledger stage-(1) call, after the actual recorder output. -/
def ledgerStart (x : Inputs p) (output : CoordinatorRecordingOperation.Output p) :=
  CoordinatorCollectionLedger.startRound x.ledger (sourceRound x.time)
    (sourceLearningEnabled x) (rawInputOfRecorder output)

/-- Exact row-derived UP inputs after stage (1). The selected follower, UP
slot, and affine sample are obtained from this same complete row and time. -/
def upInputs (x : Inputs p) (started : CoordinatorCollectionLedger.Ledger p x.etaReal
    (x.etaPositive)
    (payloadSourceCap x.payload)
    x.n x.n_cast_identity) :
    CoordinatorUpMeasurability.ReceptionLocalInputs p x.etaReal
      (x.etaPositive)
      (payloadSourceCap x.payload)
      x.n x.n_cast_identity :=
  (started, (x.upDecoderBank, (x.time, x.ownObservation)))

/-- The actual row-facing accepted UP receiver call; it does not accept a sent
word, parsed record, chosen follower, or purported affine sample. -/
def receiveUp (x : Inputs p) (started : CoordinatorCollectionLedger.Ledger p x.etaReal
    (x.etaPositive)
    (payloadSourceCap x.payload)
    x.n x.n_cast_identity) :=
  CoordinatorUpMeasurability.receiveUpAtRow x.row (upInputs x started) x.time

end InputsValid

/-- Local run failures remain ordinary results for a later sticky-dagger
caller. Decoder rejection is deliberately not a failure case. -/
inductive Failure where
  | clockStart (reason : CoordinatorPhaseClock.ClockFailure)
  | wrongClockBranch
  | armChoiceDomain
  | recorderDomain
  | ledgerStartDomain
  | upReceptionDomain
  | ledgerFinishDomain
  | clockFinish (reason : CoordinatorPhaseClock.ClockFailure)
  deriving DecidableEq

/-- Successful one-round trace. It retains the pre-choice arm, actual recorder
output, service/buffering input, actual checked reception tag and persistent
decoder bank, and the two source-ordered finish outputs. -/
structure Trace {p : Parameters} (x : Inputs p) where
  inputsValid : InputsValid x
  clockStarted : CoordinatorPhaseClock.StartRoundResult p
  clockStarted_eq : CoordinatorPhaseClock.startRound p x.etaReal x.time x.clock
    x.ledger.pending = .ok clockStarted
  clockStarted_frame : clockStarted.clock = x.clock ∧
    clockStarted.pending = x.ledger.pending ∧
    clockStarted.ledgerCommand = none ∧ clockStarted.assignmentStart = none
  arm : Fin p.K
  armChoice_eq : CoordinatorLocalArmChoice.coordinatorArmChoice x.payload
    clockStarted.pending (some (localCutoff x.cutoffIndex)) x.time
    (Inputs.weights (x := x) inputsValid.ledger_valid
      inputsValid.assignment_eq) x.row = some arm
  recorder : CoordinatorRecordingOperation.Output p
  recorder_eq : CoordinatorRecorderComplementBridge.run
    (InputsValid.recorderInput (x := x) inputsValid arm) =
      some recorder
  enabled : Bool
  enabled_eq : enabled = InputsValid.sourceLearningEnabled x
  rawInput : Option (Fin p.K × ℕ)
  rawInput_eq : rawInput = InputsValid.rawInputOfRecorder recorder
  ledgerStarted : CoordinatorCollectionLedger.Ledger p x.etaReal
    (x.etaPositive)
    (payloadSourceCap x.payload)
    x.n x.n_cast_identity
  ledgerStart_eq : CoordinatorCollectionLedger.startRound x.ledger
    (sourceRound x.time) enabled rawInput = .success ledgerStarted
  receptionInput : CoordinatorUpReception.ReceptionInput p x.etaReal
    x.etaPositive (payloadSourceCap x.payload) x.n x.n_cast_identity
  receptionInput_eq : receptionInput = CoordinatorUpMeasurability.receptionInputAtRow
    x.row (InputsValid.upInputs (x := x) ledgerStarted) x.time
  reception : CoordinatorCollectionLedger.Checked
    (CoordinatorCollectionLedger.Ledger p x.etaReal x.etaPositive
      (payloadSourceCap x.payload) x.n x.n_cast_identity ×
      CoordinatorUpReception.UpDecoderBank p)
  reception_eq : CoordinatorUpMeasurability.receiveUpAtRow x.row
    (InputsValid.upInputs (x := x) ledgerStarted) x.time = reception
  ledgerDecoded : CoordinatorCollectionLedger.Ledger p x.etaReal x.etaPositive
    (payloadSourceCap x.payload) x.n x.n_cast_identity
  decoderBankAfter : CoordinatorUpReception.UpDecoderBank p
  reception_outcome : reception = .success (ledgerDecoded, decoderBankAfter) ∨
    reception = .rejected (ledgerDecoded, decoderBankAfter)
  reception_not_invalid : reception ≠ .invalid
  ledgerFinished : CoordinatorCollectionLedger.Ledger p x.etaReal x.etaPositive
    (payloadSourceCap x.payload) x.n x.n_cast_identity
  ledgerFinish_eq : CoordinatorCollectionLedger.finishRound ledgerDecoded =
    .success ledgerFinished
  clockFinished : CoordinatorPhaseClock.FinishRoundResult p
  clockFinish_eq : CoordinatorPhaseClock.finishRound p x.etaReal x.time
    clockStarted.clock ledgerFinished.pending x.row = .ok clockFinished

/-- A non-invalid accepted UP operation must have passed its local input
domain check. -/
theorem receiveUp_noninvalid_domain {p : Parameters} {eta : ℝ} {heta : 0 < eta}
    {hcap : CoordinatorCollectionLedger.sourceLearningCap p eta}
    {n : ℕ} {hn : (n : ℝ) = eta * (ConstructorDimensions.D p : ℝ)}
    (input : CoordinatorUpReception.ReceptionInput p eta heta hcap n hn)
    (hne : CoordinatorUpReception.receiveUp input ≠ .invalid) :
    CoordinatorUpReception.receptionInputDomain input := by
  have hcheck : CoordinatorUpReception.receptionInputCheck input = true := by
    by_contra hfalse
    have hzero : CoordinatorUpReception.receptionInputCheck input = false := by
      cases hc : CoordinatorUpReception.receptionInputCheck input with
      | false => rfl
      | true => exact False.elim (hfalse hc)
    exact hne (CoordinatorUpReception.receiveUp_invalid_of_domain_check input hzero)
  exact (CoordinatorUpReception.receptionInputCheck_eq_true_iff input).mp hcheck

namespace Trace

variable {p : Parameters} {x : Inputs p} (tr : Trace x)

/-- The current zero-based table index is used consistently as source round
`t = index + 1`; the cutoff index is shifted the same way. -/
@[simp] theorem source_time_shift :
    sourceRound x.time = x.time.val + 1 := rfl

@[simp] theorem cutoff_time_shift :
    sourceCutoff x.cutoffIndex = x.cutoffIndex.val + 1 := rfl

/-- Stage (1) preserves assignment identity, source sigma, cutoff, freeze,
base scores, and the pending-UP set while moving the cursor to this round. -/
theorem ledgerStarted_frame :
    tr.ledgerStarted.assignment = x.ledger.assignment ∧
    tr.ledgerStarted.sigma = x.ledger.sigma ∧
    tr.ledgerStarted.cutoff = x.ledger.cutoff ∧
    tr.ledgerStarted.freezeAt = x.ledger.freezeAt ∧
    tr.ledgerStarted.baseScore = x.ledger.baseScore ∧
    tr.ledgerStarted.pending = x.ledger.pending ∧
    tr.ledgerStarted.cursor = sourceRound x.time ∧
    tr.ledgerStarted.phase = CoordinatorCollectionLedger.Phase.started := by
  have hcand := InputsValid.startRound_success_candidate x.ledger
    (sourceRound x.time) (by simp [sourceRound])
    (by simp [sourceRound])
    tr.enabled tr.rawInput tr.ledgerStarted tr.ledgerStart_eq
  rw [hcand]
  simp [CoordinatorCollectionLedger.startRoundCandidate, sourceRound,
    CoordinatorCollectionLedger.sourceRound]

/-- Stage (3) advances one cursor position and preserves the newly decoded
pending set and the frozen assignment data. -/
theorem ledgerFinished_frame :
    tr.ledgerFinished.assignment = tr.ledgerDecoded.assignment ∧
    tr.ledgerFinished.sigma = tr.ledgerDecoded.sigma ∧
    tr.ledgerFinished.cutoff = tr.ledgerDecoded.cutoff ∧
    tr.ledgerFinished.freezeAt = tr.ledgerDecoded.freezeAt ∧
    tr.ledgerFinished.baseScore = tr.ledgerDecoded.baseScore ∧
    tr.ledgerFinished.pending = tr.ledgerDecoded.pending ∧
    tr.ledgerFinished.cursor = tr.ledgerDecoded.cursor + 1 ∧
    tr.ledgerFinished.phase = CoordinatorCollectionLedger.Phase.ready := by
  rw [InputsValid.finishRound_success_candidate tr.ledgerDecoded
    tr.ledgerFinished tr.ledgerFinish_eq]
  simp [CoordinatorCollectionLedger.finishRoundCandidate]

/-- The actual row adapter takes its slot, follower, and affine sample from
the coordinator's same current time control. -/
theorem receptionInput_row_fields :
    tr.receptionInput.slot =
      PublicDiscreteDraws.slotDraw (x.row.2 x.time).1 ∧
    tr.receptionInput.selectedFollower =
      CoordinatorUpMeasurability.selectedFollowerIndex (x.row.2 x.time) ∧
    tr.receptionInput.affineSample =
      (x.row.2 x.time).2
        (1, CoordinatorUpMeasurability.selectedChannelFollower (x.row.2 x.time)) := by
  rw [tr.receptionInput_eq]
  change
    (CoordinatorUpMeasurability.receptionInputAtControl (x.row.2 x.time)
      (InputsValid.upInputs (x := x) tr.ledgerStarted)).slot = _ ∧
    (CoordinatorUpMeasurability.receptionInputAtControl (x.row.2 x.time)
      (InputsValid.upInputs (x := x) tr.ledgerStarted)).selectedFollower = _ ∧
    (CoordinatorUpMeasurability.receptionInputAtControl (x.row.2 x.time)
      (InputsValid.upInputs (x := x) tr.ledgerStarted)).affineSample = _
  exact ⟨CoordinatorUpMeasurability.receptionInputAtControl_slot _ _,
    CoordinatorUpMeasurability.receptionInputAtControl_selectedFollower _ _,
    CoordinatorUpMeasurability.receptionInputAtControl_affineSample _ _⟩

/-- The successful stage-(1) ledger and carried bank pass the receiver's
actual local domain test in every completed trace. -/
theorem receptionInput_domain :
    CoordinatorUpReception.receptionInputDomain tr.receptionInput := by
  have hneRow : CoordinatorUpMeasurability.receiveUpAtRow x.row
      (InputsValid.upInputs (x := x) tr.ledgerStarted) x.time ≠ .invalid := by
    intro hbad
    apply tr.reception_not_invalid
    rw [← tr.reception_eq]
    exact hbad
  have hne : CoordinatorUpReception.receiveUp tr.receptionInput ≠ .invalid := by
    simpa [CoordinatorUpMeasurability.receiveUpAtRow,
      tr.receptionInput_eq] using hneRow
  exact receiveUp_noninvalid_domain tr.receptionInput hne

/-- A successful reception contains a record parsed from this row's actual
DecodeStep output and passing the source ledger's literal UP acceptance test.
The parsed record is derived from the operator; it is never a supplied premise. -/
theorem successful_reception_is_literal_acceptance
    (haccepted : tr.reception = .success (tr.ledgerDecoded, tr.decoderBankAfter)) :
    ∃ M, CoordinatorUpReception.parsedDecoderOutput tr.receptionInput = some M ∧
      OrdinaryMessageCodec.acceptUp
        (CoordinatorCollectionLedger.codecParams p x.etaReal)
        tr.receptionInput.ledger.cutoff tr.receptionInput.ledger.cursor
        tr.receptionInput.selectedFollower.val
        (CoordinatorCollectionLedger.pendingNaturalLabels tr.receptionInput.ledger)
        tr.receptionInput.ledger.sigma M := by
  have hresult : CoordinatorUpReception.receiveUp tr.receptionInput =
      .success (tr.ledgerDecoded, tr.decoderBankAfter) := by
    calc
      CoordinatorUpReception.receiveUp tr.receptionInput =
          CoordinatorUpReception.receiveUp
            (CoordinatorUpMeasurability.receptionInputAtRow x.row
              (InputsValid.upInputs (x := x) tr.ledgerStarted) x.time) := by
        rw [tr.receptionInput_eq]
      _ = CoordinatorUpMeasurability.receiveUpAtRow x.row
          (InputsValid.upInputs (x := x) tr.ledgerStarted) x.time := rfl
      _ = tr.reception := tr.reception_eq
      _ = .success (tr.ledgerDecoded, tr.decoderBankAfter) := haccepted
  exact CoordinatorUpReception.receiveUp_success_implies_literal_acceptUp
    tr.receptionInput tr.receptionInput_domain
    (tr.ledgerDecoded, tr.decoderBankAfter) hresult

/-- On successful acceptance, the replay prefix and current record are the
records actually read by `decodeUp` from the stage-(1) ledger. The finished
increment is the replay through this source round, with no second addition of
local service. -/
theorem successful_reception_replay_increment
    (haccepted : tr.reception = .success (tr.ledgerDecoded, tr.decoderBankAfter)) :
    ∃ M past current,
      CoordinatorUpReception.parsedDecoderOutput tr.receptionInput = some M ∧
      tr.ledgerDecoded = CoordinatorCollectionLedger.acceptUpCandidate
        tr.ledgerStarted tr.receptionInput.selectedFollower M past current ∧
      CoordinatorCollectionLedger.replayRecords? tr.ledgerStarted
        (tr.ledgerStarted.assignment.arm tr.receptionInput.selectedFollower)
        [tr.receptionInput.time] = some [current] ∧
      tr.ledgerFinished.increment
          (tr.ledgerStarted.assignment.arm tr.receptionInput.selectedFollower) =
        (CoordinatorCollectionLedger.replayResult (4 * x.n) M.val.q
          past current).registers.1 := by
  rcases tr.successful_reception_is_literal_acceptance haccepted with
    ⟨acceptedRecord, hparsedAccepted, hcodecAccepted⟩
  have hcheck : CoordinatorUpReception.receptionInputCheck tr.receptionInput = true :=
    (CoordinatorUpReception.receptionInputCheck_eq_true_iff tr.receptionInput).2
      tr.receptionInput_domain
  have hreceive : CoordinatorUpReception.receiveUp tr.receptionInput =
      .success (tr.ledgerDecoded, tr.decoderBankAfter) := by
    calc
      CoordinatorUpReception.receiveUp tr.receptionInput =
          CoordinatorUpReception.receiveUp
            (CoordinatorUpMeasurability.receptionInputAtRow x.row
              (InputsValid.upInputs (x := x) tr.ledgerStarted) x.time) := by
        rw [tr.receptionInput_eq]
      _ = CoordinatorUpMeasurability.receiveUpAtRow x.row
          (InputsValid.upInputs (x := x) tr.ledgerStarted) x.time := rfl
      _ = tr.reception := tr.reception_eq
      _ = .success (tr.ledgerDecoded, tr.decoderBankAfter) := haccepted
  rw [CoordinatorUpReception.receiveUp_eq_existing_decodeUp
    tr.receptionInput hcheck] at hreceive
  change CoordinatorUpReception.packDecodeResult
      (CoordinatorCollectionLedger.decodeUp tr.receptionInput.ledger
        tr.receptionInput.selectedFollower
        (CoordinatorUpReception.parsedDecoderOutput tr.receptionInput))
      (CoordinatorUpReception.decoderBankAfter tr.receptionInput) =
        .success (tr.ledgerDecoded, tr.decoderBankAfter) at hreceive
  have hdecode :
      CoordinatorCollectionLedger.decodeUp tr.receptionInput.ledger
        tr.receptionInput.selectedFollower
        (CoordinatorUpReception.parsedDecoderOutput tr.receptionInput) =
        .success tr.ledgerDecoded := by
    cases hcase : CoordinatorCollectionLedger.decodeUp tr.receptionInput.ledger
        tr.receptionInput.selectedFollower
        (CoordinatorUpReception.parsedDecoderOutput tr.receptionInput) with
    | success decoded =>
        simp [CoordinatorUpReception.packDecodeResult, hcase] at hreceive
        have hdecoded : decoded = tr.ledgerDecoded := hreceive.1
        rw [← hdecoded]
    | rejected decoded =>
        simp [CoordinatorUpReception.packDecodeResult, hcase] at hreceive
    | invalid =>
        simp [CoordinatorUpReception.packDecodeResult, hcase] at hreceive
  have hinputLedger : tr.receptionInput.ledger = tr.ledgerStarted := by
    rw [tr.receptionInput_eq]
    rfl
  rcases CoordinatorUpReception.receptionInputDomain_parts tr.receptionInput
      tr.receptionInput_domain with
    ⟨hledgerValid, _, hphase, hcutoff, hcutCursor, hcursorT, hsourceCursor, _⟩
  have hdecodeDomain :
      CoordinatorCollectionLedger.validLedgerCheck tr.ledgerStarted = true ∧
        tr.ledgerStarted.phase = CoordinatorCollectionLedger.Phase.started ∧
        1 ≤ tr.ledgerStarted.cutoff ∧
        tr.ledgerStarted.cutoff ≤ tr.ledgerStarted.cursor ∧
        tr.ledgerStarted.cursor ≤ p.T := by
    exact ⟨by simpa [hinputLedger] using hledgerValid,
      by simpa [hinputLedger] using hphase,
      by simpa [hinputLedger] using hcutoff,
      by simpa [hinputLedger] using hcutCursor,
      by simpa [hinputLedger] using hcursorT⟩
  have htimeAsCursor : tr.ledgerStarted.cursor = tr.receptionInput.time.val + 1 := by
    simpa [hinputLedger, CoordinatorCollectionLedger.sourceRound] using hsourceCursor
  have hroundIndex :
      (⟨tr.ledgerStarted.cursor - 1, by omega⟩ : Fin p.T) = tr.receptionInput.time := by
    apply Fin.ext
    change tr.ledgerStarted.cursor - 1 = tr.receptionInput.time.val
    omega
  have hdecodeStarted :
      CoordinatorCollectionLedger.decodeUp tr.ledgerStarted
        tr.receptionInput.selectedFollower
        (CoordinatorUpReception.parsedDecoderOutput tr.receptionInput) =
        .success tr.ledgerDecoded := by
    simpa [hinputLedger] using hdecode
  rcases InputsValid.decodeUp_success_candidate
      tr.ledgerStarted tr.receptionInput.selectedFollower
      (CoordinatorUpReception.parsedDecoderOutput tr.receptionInput)
      tr.ledgerDecoded hdecodeDomain hdecodeStarted with
    ⟨record, past, current, hparsed, hcandidate, _, hcurrentSource⟩
  have hcurrentAtTime :
      CoordinatorCollectionLedger.replayRecords? tr.ledgerStarted
        (tr.ledgerStarted.assignment.arm tr.receptionInput.selectedFollower)
        [tr.receptionInput.time] = some [current] := by
    rw [← hroundIndex]
    exact hcurrentSource
  have hrecordEq : acceptedRecord = record :=
    Option.some.inj (hparsedAccepted.symm.trans hparsed)
  subst acceptedRecord
  have hcodecOnStarted :
      OrdinaryMessageCodec.acceptUp
        (CoordinatorCollectionLedger.codecParams p x.etaReal)
        tr.ledgerStarted.cutoff tr.ledgerStarted.cursor
        tr.receptionInput.selectedFollower.val
        (CoordinatorCollectionLedger.pendingNaturalLabels tr.ledgerStarted)
        tr.ledgerStarted.sigma record := by
    simpa [hinputLedger] using hcodecAccepted
  have hacceptCheck : CoordinatorCollectionLedger.acceptUpCheck tr.ledgerStarted
      tr.receptionInput.selectedFollower record = true :=
    (CoordinatorCollectionLedger.acceptUpCheck_iff tr.ledgerStarted
      tr.receptionInput.selectedFollower record).2 hcodecOnStarted
  have hacceptFields := hacceptCheck
  simp only [CoordinatorCollectionLedger.acceptUpCheck, Bool.and_eq_true,
    decide_eq_true_eq] at hacceptFields
  have hpending : tr.receptionInput.selectedFollower ∈ tr.ledgerStarted.pending :=
    hacceptFields.2.1
  have hpendingArm : CoordinatorCollectionLedger.armPending tr.ledgerStarted
      (tr.ledgerStarted.assignment.arm tr.receptionInput.selectedFollower) :=
    ⟨tr.receptionInput.selectedFollower, hpending, rfl⟩
  rcases tr.ledgerStarted_frame with
    ⟨hassignment, _, _, _, _, hpendingFrame, _, _⟩
  have hpendingSource : tr.receptionInput.selectedFollower ∈ x.ledger.pending := by
    rw [← hpendingFrame]
    simpa [hinputLedger] using hpending
  let sourceArm := x.ledger.assignment.arm tr.receptionInput.selectedFollower
  have hsourcePendingArm : CoordinatorCollectionLedger.armPending x.ledger sourceArm :=
    ⟨tr.receptionInput.selectedFollower, hpendingSource, rfl⟩
  rcases validLedger_registerFacts x.ledger tr.inputsValid.ledger_valid with
    ⟨_, hcurrentAll, _, _⟩
  have hcurrentEntry := (allFin_eq_true_iff _).mp hcurrentAll sourceArm
  have hsourceArmPendingCheck :
      CoordinatorCollectionLedger.armPendingCheck x.ledger sourceArm = true :=
    (armPendingCheck_eq_true_iff x.ledger sourceArm).2 hsourcePendingArm
  have hsourceCurrentNone : (x.ledger.currentRegisters sourceArm).isNone = true := by
    simpa [hsourceArmPendingCheck] using hcurrentEntry
  have hunknownSource : x.ledger.currentRegisters sourceArm = none := by
    cases hcurrent : x.ledger.currentRegisters sourceArm with
    | none => rfl
    | some current' => simp [hcurrent] at hsourceCurrentNone
  have hstartCandidate := InputsValid.startRound_success_candidate x.ledger
    (sourceRound x.time) (by simp [sourceRound]) (by simp [sourceRound])
    tr.enabled tr.rawInput tr.ledgerStarted tr.ledgerStart_eq
  have hroundIndex :
      (⟨sourceRound x.time - 1, by simp [sourceRound]⟩ : Fin p.T) = x.time := by
    apply Fin.ext
    simp [sourceRound]
  rw [hroundIndex] at hstartCandidate
  have hserviceReplay :=
    CoordinatorCollectionLedger.finish_recovered_increment_once_after_stageOne
      x.ledger x.time tr.enabled tr.rawInput tr.receptionInput.selectedFollower
      record past current hunknownSource
  have hfinishCandidate := InputsValid.finishRound_success_candidate
    tr.ledgerDecoded tr.ledgerFinished tr.ledgerFinish_eq
  refine ⟨record, past, current, hparsed, hcandidate,
    hcurrentAtTime, ?_⟩
  rw [hfinishCandidate, hcandidate, hassignment, hstartCandidate]
  exact hserviceReplay

/-- The frozen collection choice depends on the complete row only through its
current time control. -/
theorem armChoice_same_current_control
    (row₁ row₂ : CompletePublicTable.CompleteRow p)
    (hcontrol : row₁.2 x.time = row₂.2 x.time) :
    CoordinatorLocalArmChoice.coordinatorArmChoice x.payload
        tr.clockStarted.pending (some (localCutoff x.cutoffIndex)) x.time
        (Inputs.weights (x := x) tr.inputsValid.ledger_valid
          tr.inputsValid.assignment_eq) row₁ =
      CoordinatorLocalArmChoice.coordinatorArmChoice x.payload
        tr.clockStarted.pending (some (localCutoff x.cutoffIndex)) x.time
        (Inputs.weights (x := x) tr.inputsValid.ledger_valid
          tr.inputsValid.assignment_eq) row₂ :=
  CoordinatorLocalArmChoice.coordinatorArmChoice_eq_of_same_current_timeControl
    x.payload tr.clockStarted.pending (some (localCutoff x.cutoffIndex))
    x.time
    (Inputs.weights (x := x) tr.inputsValid.ledger_valid
      tr.inputsValid.assignment_eq)
    row₁ row₂ hcontrol

/-- For a fixed retained envelope, arm, and typed observation, the actual
complement recorder call is invariant when only the current time control is
fixed; the other row coordinates remain unrestricted. -/
theorem recorder_same_current_control
    (arm : Fin p.K) (row₁ row₂ : CompletePublicTable.CompleteRow p)
    (hcontrol : row₁.2 x.time = row₂.2 x.time) :
    CoordinatorRecorderComplementBridge.run
        ({InputsValid.recorderInput (x := x) tr.inputsValid arm with row := row₁}) =
      CoordinatorRecorderComplementBridge.run
        ({InputsValid.recorderInput (x := x) tr.inputsValid arm with row := row₂}) := by
  let bridgeBase := InputsValid.recorderInput (x := x) tr.inputsValid arm
  let bridgeLeft : CoordinatorRecorderComplementBridge.Input x.payload :=
    { bridgeBase with row := row₁ }
  let bridgeRight : CoordinatorRecorderComplementBridge.Input x.payload :=
    { bridgeBase with row := row₂ }
  let operationBase := CoordinatorRecorderComplementBridge.recorderInput bridgeBase
  let recorderLeft : CoordinatorRecordingMeasurability.RecorderDomain p :=
    (row₁, (arm, x.ownObservation))
  let recorderRight : CoordinatorRecordingMeasurability.RecorderDomain p :=
    (row₂, (arm, x.ownObservation))
  have hleft : CoordinatorRecorderComplementBridge.recorderInput bridgeLeft =
      CoordinatorRecordingMeasurability.inputAt operationBase recorderLeft := rfl
  have hright : CoordinatorRecorderComplementBridge.recorderInput bridgeRight =
      CoordinatorRecordingMeasurability.inputAt operationBase recorderRight := rfl
  have hslice : ContinuousLearningRows.sliceAt x.time row₁.2 =
      ContinuousLearningRows.sliceAt x.time row₂.2 :=
    congrArg Prod.fst hcontrol
  calc
    CoordinatorRecorderComplementBridge.run bridgeLeft =
        CoordinatorRecordingOperation.run
          (CoordinatorRecorderComplementBridge.recorderInput bridgeLeft) :=
      CoordinatorRecorderComplementBridge.run_eq_accepted bridgeLeft
    _ = CoordinatorRecordingOperation.run
          (CoordinatorRecorderComplementBridge.recorderInput bridgeRight) := by
      rw [hleft, hright]
      exact CoordinatorRecordingMeasurability.run_eq_of_current_slice_eq
        operationBase recorderLeft recorderRight hslice rfl rfl
    _ = CoordinatorRecorderComplementBridge.run bridgeRight :=
      (CoordinatorRecorderComplementBridge.run_eq_accepted bridgeRight).symm

/-- With carried weights, time, arm, and observation fixed, the actual
recorder result is measurable over complete rows by the accepted row
operation's measurability theorem. -/
theorem recorder_measurable_at_fixed_registers (arm : Fin p.K) :
    Measurable (fun row : CompletePublicTable.CompleteRow p =>
      CoordinatorRecorderComplementBridge.run
        ({InputsValid.recorderInput (x := x) tr.inputsValid arm with row := row})) := by
  let bridgeBase := InputsValid.recorderInput (x := x) tr.inputsValid arm
  let operationBase := CoordinatorRecorderComplementBridge.recorderInput bridgeBase
  let rowValue : CompletePublicTable.CompleteRow p →
      CoordinatorRecordingMeasurability.RecorderDomain p :=
    fun row => (row, (arm, x.ownObservation))
  have hrowValue : Measurable rowValue := by
    exact measurable_id.prodMk measurable_const
  have hresult :
      (fun row : CompletePublicTable.CompleteRow p =>
        CoordinatorRecorderComplementBridge.run
          ({bridgeBase with row := row})) =
      (fun row : CompletePublicTable.CompleteRow p =>
        CoordinatorRecordingOperation.run
          (CoordinatorRecordingMeasurability.inputAt operationBase (rowValue row))) := by
    funext row
    rw [CoordinatorRecorderComplementBridge.run_eq_accepted]
    rfl
  rw [hresult]
  exact (CoordinatorRecordingMeasurability.measurable_run operationBase).comp hrowValue

/-- The UP receiver itself reads a complete row only through the current time
control, for fixed post-service ledger, persistent bank, and typed observation. -/
theorem receiveUp_same_current_control
    (row₁ row₂ : CompletePublicTable.CompleteRow p)
    (hcontrol : row₁.2 x.time = row₂.2 x.time) :
    CoordinatorUpMeasurability.receiveUpAtRow row₁
        (InputsValid.upInputs (x := x) tr.ledgerStarted) x.time =
      CoordinatorUpMeasurability.receiveUpAtRow row₂
        (InputsValid.upInputs (x := x) tr.ledgerStarted) x.time :=
  CoordinatorUpMeasurability.receiveUpAtRow_eq_of_same_current_control
    row₁ row₂ (InputsValid.upInputs (x := x) tr.ledgerStarted) x.time hcontrol

/-- The selected follower's decode result leaves every unselected UP decoder
channel exactly as it was before this round. -/
theorem decoderBankAfter_unselected
    (i : Fin (p.m - 1)) (hi : i ≠ tr.receptionInput.selectedFollower) :
    tr.decoderBankAfter i = x.upDecoderBank i := by
  have hneRow : CoordinatorUpMeasurability.receiveUpAtRow x.row
      (InputsValid.upInputs (x := x) tr.ledgerStarted) x.time ≠ .invalid := by
    intro hbad
    apply tr.reception_not_invalid
    rw [← tr.reception_eq]
    exact hbad
  have hne : CoordinatorUpReception.receiveUp tr.receptionInput ≠ .invalid := by
    simpa [CoordinatorUpMeasurability.receiveUpAtRow, tr.receptionInput_eq] using hneRow
  have hdom : CoordinatorUpReception.receptionInputDomain tr.receptionInput :=
    receiveUp_noninvalid_domain tr.receptionInput hne
  have hresult :
      CoordinatorUpReception.receiveUp tr.receptionInput =
        .success (tr.ledgerDecoded, tr.decoderBankAfter) ∨
      CoordinatorUpReception.receiveUp tr.receptionInput =
        .rejected (tr.ledgerDecoded, tr.decoderBankAfter) := by
    have h := tr.reception_outcome
    rw [← tr.reception_eq] at h
    simpa [CoordinatorUpMeasurability.receiveUpAtRow,
      tr.receptionInput_eq] using h
  have hbank := CoordinatorUpReception.receiveUp_preserves_unselected_bank
    tr.receptionInput hdom (tr.ledgerDecoded, tr.decoderBankAfter) hresult i hi
  have hinputBank : tr.receptionInput.upDecoderBank = x.upDecoderBank := by
    rw [tr.receptionInput_eq]
    rfl
  have hbank' : tr.decoderBankAfter i = tr.receptionInput.upDecoderBank i := by
    simpa using hbank
  exact hbank'.trans (congrArg (fun bank : CoordinatorUpReception.UpDecoderBank p => bank i)
    hinputBank)

/-- The selected channel is the actual state returned by this round's
DecodeStep, whether the parsed UP is accepted or ordinarily rejected. -/
theorem decoderBankAfter_selected_transition :
    tr.decoderBankAfter tr.receptionInput.selectedFollower =
      (CoordinatorUpReception.decoderTransition tr.receptionInput).1 := by
  have hneRow : CoordinatorUpMeasurability.receiveUpAtRow x.row
      (InputsValid.upInputs (x := x) tr.ledgerStarted) x.time ≠ .invalid := by
    intro hbad
    apply tr.reception_not_invalid
    rw [← tr.reception_eq]
    exact hbad
  have hne : CoordinatorUpReception.receiveUp tr.receptionInput ≠ .invalid := by
    simpa [CoordinatorUpMeasurability.receiveUpAtRow,
      tr.receptionInput_eq] using hneRow
  have hdom : CoordinatorUpReception.receptionInputDomain tr.receptionInput :=
    receiveUp_noninvalid_domain tr.receptionInput hne
  have hresult :
      CoordinatorUpReception.receiveUp tr.receptionInput =
        .success (tr.ledgerDecoded, tr.decoderBankAfter) ∨
      CoordinatorUpReception.receiveUp tr.receptionInput =
        .rejected (tr.ledgerDecoded, tr.decoderBankAfter) := by
    have h := tr.reception_outcome
    rw [← tr.reception_eq] at h
    simpa [CoordinatorUpMeasurability.receiveUpAtRow,
      tr.receptionInput_eq] using h
  have hcheck := (CoordinatorUpReception.receptionInputCheck_eq_true_iff
    tr.receptionInput).2 hdom
  rw [CoordinatorUpReception.receiveUp_eq_existing_decodeUp
    tr.receptionInput hcheck] at hresult
  have hbank : tr.decoderBankAfter =
      CoordinatorUpReception.decoderBankAfter tr.receptionInput := by
    cases hresult with
    | inl hs =>
        exact CoordinatorUpReception.packDecodeResult_output_bank _ _
          (tr.ledgerDecoded, tr.decoderBankAfter) (.inl hs)
    | inr hr =>
        exact CoordinatorUpReception.packDecodeResult_output_bank _ _
          (tr.ledgerDecoded, tr.decoderBankAfter) (.inr hr)
  have hinputBank : tr.receptionInput.upDecoderBank = x.upDecoderBank := by
    rw [tr.receptionInput_eq]
    rfl
  rw [hbank, CoordinatorUpReception.decoderBankAfter, hinputBank]
  simp [Function.update_self]

/-- A successful recorder gate retains `some arm` even when its raw floor is
zero. Disabled recorder output remains `none`, so the raw service input keeps
the source distinction between enabled-zero and disabled. -/
theorem rawInput_gate_arm_cases :
    (tr.rawInput = none ↔ tr.recorder.gateArm = none) ∧
    (∀ a amount, tr.rawInput = some (a, amount) ↔
      tr.recorder.gateArm = some a ∧ amount = tr.recorder.rawArrival) := by
  rw [tr.rawInput_eq]
  constructor
  · simp [InputsValid.rawInputOfRecorder]
  · intro a amount
    constructor
    · intro h
      simp [InputsValid.rawInputOfRecorder] at h
      rcases h with ⟨hgate, hamount⟩
      exact ⟨hgate, hamount.symm⟩
    · rintro ⟨hgate, rfl⟩
      simp [InputsValid.rawInputOfRecorder, hgate]

/-- The exact source enable bit is determined by active collection and the
pre-freeze coordinator service interval, independently of whether recording
produced a positive arrival. -/
theorem enabled_iff_source_rule :
    tr.enabled = true ↔
      0 < x.ledger.sigma ∧ x.ledger.cutoff ≤ sourceRound x.time ∧
        sourceRound x.time < x.ledger.freezeAt := by
  rw [tr.enabled_eq]
  simp only [InputsValid.sourceLearningEnabled, decide_eq_true_eq]

/-- A known queue's current-register transition is the exact source
`QueueReplay.transition` on this one round's enabled/raw input. -/
theorem known_queue_transition
    (a : Fin p.K) (current : CoordinatorCollectionLedger.CurrentRegister)
    (hknown : x.ledger.currentRegisters a = some current) :
    tr.ledgerStarted.currentRegisters a =
      some ⟨(QueueReplay.transition (4 * x.n) (0, current.queue)
          (CoordinatorCollectionLedger.localQueueRecord x.ledger x.time
            tr.enabled tr.rawInput a)).2,
        (QueueReplay.transition (4 * x.n) (0, current.queue)
          (CoordinatorCollectionLedger.localQueueRecord x.ledger x.time
            tr.enabled tr.rawInput a)).1⟩ := by
  have hcand := InputsValid.startRound_success_candidate x.ledger
    (sourceRound x.time) (by simp [sourceRound])
    (by simp [sourceRound])
    tr.enabled tr.rawInput tr.ledgerStarted tr.ledgerStart_eq
  rw [hcand]
  exact CoordinatorCollectionLedger.startRoundCandidate_known_transition
    x.ledger x.time tr.enabled tr.rawInput a current hknown

/-- A positive arrival from the recorder's actual routed arm is buffered at
this calendar index when that arm's source register is still unknown. Zero
arrivals are handled separately and are not inserted into raw history. -/
theorem unknown_positive_arrival_buffered
    (a : Fin p.K) (amount : ℕ)
    (hunknown : x.ledger.currentRegisters a = none)
    (hraw : tr.rawInput = some (a, amount)) (hpositive : 0 < amount)
    (hbeforeFreeze : sourceRound x.time < x.ledger.freezeAt) :
    tr.ledgerStarted.rawBuffer a x.time = some amount := by
  have hcand := InputsValid.startRound_success_candidate x.ledger
    (sourceRound x.time) (by simp [sourceRound]) (by simp [sourceRound])
    tr.enabled tr.rawInput tr.ledgerStarted tr.ledgerStart_eq
  have hbefore : CoordinatorCollectionLedger.sourceRound x.time <
      x.ledger.freezeAt := by
    simpa [CoordinatorCollectionLedger.sourceRound, sourceRound] using hbeforeFreeze
  rw [hcand, hraw]
  exact CoordinatorCollectionLedger.startRoundCandidate_rawBuffer_positive
    x.ledger x.time tr.enabled a amount hunknown hpositive hbefore

/-- If an actual successful recorder gate routed a zero floor to a known
queue while collection is enabled, stage (1) records `(true, 0)` and therefore
executes the enabled zero-arrival queue transition. -/
theorem known_queue_enabled_zero_arrival
    (a : Fin p.K) (current : CoordinatorCollectionLedger.CurrentRegister)
    (hknown : x.ledger.currentRegisters a = some current)
    (hraw : tr.rawInput = some (a, 0)) (henabled : tr.enabled = true)
    (hbeforeFreeze : sourceRound x.time < x.ledger.freezeAt) :
    CoordinatorCollectionLedger.localQueueRecord x.ledger x.time tr.enabled
      tr.rawInput a = (true, 0) ∧
    tr.ledgerStarted.currentRegisters a =
      some ⟨(QueueReplay.transition (4 * x.n) (0, current.queue) (true, 0)).2,
        (QueueReplay.transition (4 * x.n) (0, current.queue) (true, 0)).1⟩ := by
  have hrecord : CoordinatorCollectionLedger.localQueueRecord x.ledger x.time
      tr.enabled tr.rawInput a = (true, 0) := by
    have hbefore : CoordinatorCollectionLedger.sourceRound x.time < x.ledger.freezeAt := by
      simpa [sourceRound, CoordinatorCollectionLedger.sourceRound] using hbeforeFreeze
    simp [CoordinatorCollectionLedger.localQueueRecord, hraw, henabled,
      hbefore, CoordinatorCollectionLedger.localArrival]
  constructor
  · exact hrecord
  · rw [known_queue_transition tr a current hknown]
    rw [hrecord]

/-- When the source enable bit is false, a known queue gets a disabled zero
record: its backlog is preserved and its current-round service is zero. -/
theorem known_queue_disabled_preserves
    (a : Fin p.K) (current : CoordinatorCollectionLedger.CurrentRegister)
    (hknown : x.ledger.currentRegisters a = some current)
    (hdisabled : tr.enabled = false) :
    tr.ledgerStarted.currentRegisters a = some ⟨current.queue, 0⟩ := by
  rw [known_queue_transition tr a current hknown]
  simp [CoordinatorCollectionLedger.localQueueRecord, hdisabled,
    QueueReplay.transition]

/-- Collection's clock finish emits exactly the local-service accumulation
command and retains the same clock and resulting pending set. The ledger finish
has already incorporated `gammaLoc`, so this descriptive command is not a
second accumulator update here. -/
theorem clockFinished_collection_command :
    tr.clockFinished.clock = x.clock ∧
    tr.clockFinished.pending = tr.ledgerFinished.pending ∧
    tr.clockFinished.ledgerCommand =
      some (.accumulateLocalServiceAt x.time) := by
  have hcutoff := (InputsValid.ledger_time_bounds tr.inputsValid).2.2.2.2.2.2.1
  rw [tr.inputsValid.ledger_cutoff_eq, tr.inputsValid.ledger_cursor_eq] at hcutoff
  simp only [sourceCutoff, sourceRound] at hcutoff
  have hclockFinish := CoordinatorPhaseClock.finishRound_collection p x.etaReal
    x.time x.payload.sigma x.cutoffIndex x.clock tr.ledgerFinished.pending
    x.row tr.inputsValid.clock_registers_valid tr.inputsValid.clock_sigma_eq
    tr.inputsValid.clock_cutoff_eq (by omega)
  have hclockFinishEq := tr.clockFinish_eq
  rw [tr.clockStarted_frame.1] at hclockFinishEq
  rw [hclockFinish] at hclockFinishEq
  let expected : CoordinatorPhaseClock.FinishRoundResult p :=
    { clock := x.clock, pending := tr.ledgerFinished.pending,
      ledgerCommand := some (.accumulateLocalServiceAt x.time) }
  have hresult : expected = tr.clockFinished := Except.ok.inj hclockFinishEq
  exact ⟨(congrArg (fun z : CoordinatorPhaseClock.FinishRoundResult p => z.clock) hresult).symm,
    (congrArg (fun z : CoordinatorPhaseClock.FinishRoundResult p => z.pending) hresult).symm,
    (congrArg (fun z : CoordinatorPhaseClock.FinishRoundResult p => z.ledgerCommand) hresult).symm⟩

end Trace

/-- A checked source-ordered collection round either returns the full trace or
the exact local stage where a runtime check failed. -/
inductive Result {p : Parameters} (x : Inputs p) where
  | failed (reason : Failure)
  | completed (trace : Trace x)

open InputsValid

/-- Execute one coordinator collection round in source order. Every call is
the accepted operation; the decoder bank is threaded whole. -/
def run {p : Parameters} (x : Inputs p) (h : InputsValid x) : Result x := by
  classical
  match hclockStart : CoordinatorPhaseClock.startRound p x.etaReal x.time x.clock
      x.ledger.pending with
  | .error reason => exact .failed (.clockStart reason)
  | .ok clockStarted =>
    if hbranch : clockStarted.clock = x.clock ∧
        clockStarted.pending = x.ledger.pending ∧
        clockStarted.ledgerCommand = none ∧ clockStarted.assignmentStart = none then
      let weights := Inputs.weights (x := x) h.ledger_valid h.assignment_eq
      match hchoice : CoordinatorLocalArmChoice.coordinatorArmChoice x.payload
          clockStarted.pending (some (localCutoff x.cutoffIndex)) x.time weights x.row with
      | none => exact .failed .armChoiceDomain
      | some arm =>
        let recordInput := InputsValid.recorderInput (x := x) h arm
        match hrecorder : CoordinatorRecorderComplementBridge.run recordInput with
        | none => exact .failed .recorderDomain
        | some recorder =>
          let enabled := InputsValid.sourceLearningEnabled x
          let raw := InputsValid.rawInputOfRecorder recorder
          match hstart : CoordinatorCollectionLedger.startRound x.ledger
              (sourceRound x.time) enabled raw with
          | .invalid => exact .failed .ledgerStartDomain
          | .rejected _ => exact .failed .ledgerStartDomain
          | .success ledgerStarted =>
            let receptionInput :=
              CoordinatorUpMeasurability.receptionInputAtRow x.row
                (InputsValid.upInputs (x := x) ledgerStarted) x.time
            match hreception : CoordinatorUpMeasurability.receiveUpAtRow x.row
                (InputsValid.upInputs (x := x) ledgerStarted) x.time with
            | .invalid => exact .failed .upReceptionDomain
            | .success (ledgerDecoded, bankAfter) =>
              match hfinish : CoordinatorCollectionLedger.finishRound ledgerDecoded with
              | .invalid => exact .failed .ledgerFinishDomain
              | .rejected _ => exact .failed .ledgerFinishDomain
              | .success ledgerFinished =>
                match hclockFinish : CoordinatorPhaseClock.finishRound p x.etaReal x.time
                    clockStarted.clock ledgerFinished.pending x.row with
                | .error reason => exact .failed (.clockFinish reason)
                | .ok clockFinished =>
                  exact .completed {
                    inputsValid := h
                    clockStarted := clockStarted
                    clockStarted_eq := hclockStart
                    clockStarted_frame := hbranch
                    arm := arm
                    armChoice_eq := hchoice
                    recorder := recorder
                    recorder_eq := hrecorder
                    enabled := enabled
                    enabled_eq := rfl
                    rawInput := raw
                    rawInput_eq := rfl
                    ledgerStarted := ledgerStarted
                    ledgerStart_eq := hstart
                    receptionInput := receptionInput
                    receptionInput_eq := rfl
                    reception := .success (ledgerDecoded, bankAfter)
                    reception_eq := hreception
                    ledgerDecoded := ledgerDecoded
                    reception_outcome := .inl rfl
                    reception_not_invalid := by simp
                    decoderBankAfter := bankAfter
                    ledgerFinished := ledgerFinished
                    ledgerFinish_eq := hfinish
                    clockFinished := clockFinished
                    clockFinish_eq := hclockFinish }
            | .rejected (ledgerDecoded, bankAfter) =>
              match hfinish : CoordinatorCollectionLedger.finishRound ledgerDecoded with
              | .invalid => exact .failed .ledgerFinishDomain
              | .rejected _ => exact .failed .ledgerFinishDomain
              | .success ledgerFinished =>
                match hclockFinish : CoordinatorPhaseClock.finishRound p x.etaReal x.time
                    clockStarted.clock ledgerFinished.pending x.row with
                | .error reason => exact .failed (.clockFinish reason)
                | .ok clockFinished =>
                  exact .completed {
                    inputsValid := h
                    clockStarted := clockStarted
                    clockStarted_eq := hclockStart
                    clockStarted_frame := hbranch
                    arm := arm
                    armChoice_eq := hchoice
                    recorder := recorder
                    recorder_eq := hrecorder
                    enabled := enabled
                    enabled_eq := rfl
                    rawInput := raw
                    rawInput_eq := rfl
                    ledgerStarted := ledgerStarted
                    ledgerStart_eq := hstart
                    receptionInput := receptionInput
                    receptionInput_eq := rfl
                    reception := .rejected (ledgerDecoded, bankAfter)
                    reception_eq := hreception
                    ledgerDecoded := ledgerDecoded
                    reception_outcome := .inr rfl
                    reception_not_invalid := by simp
                    decoderBankAfter := bankAfter
                    ledgerFinished := ledgerFinished
                    ledgerFinish_eq := hfinish
                    clockFinished := clockFinished
                    clockFinish_eq := hclockFinish }
    else
      exact .failed .wrongClockBranch

end Bandits.Support.CoordinatorCollectionUpRoundStep

end
