/-
Copyright (c) 2026 Bandits Lean regret formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.AffineBatchDecoder
public import Bandits.Support.FollowerCutoffScan
public import Bandits.Support.OrdinaryMessageCodec
public import Bandits.Support.PrelaunchBufferRecovery
public import Bandits.Support.ReferencePrelaunchFollower
public import Bandits.Support.SparseCalendarReplay

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Ordinary active follower DOWN acceptance

This file implements the selected-unoccupied DOWN decoder and register
transition after the current round has already been logged. It consumes the
existing follower state, decoder, codec, cutoff scan, sparse contribution,
and queue replay APIs. The input buffer is carried data; this module does not
assert physical provenance, message authenticity, or currentness.

The total-trace adapter below is administrative only. A separate theorem
proves that `decodeStep` reads only the current `RoundInput`, so the adapter
does not represent or assert an execution history. The operation contains no
reference-word suppression and does not expose a decoded word as an input.

Sources: `sources/zip4/manuscript/06_interruptions.tex:164-177,192-209,270-276,286-295`,
`sources/zip4/manuscript/05_binary_transport.tex:36-43`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:8-14`.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ActiveFollowerDownAcceptance

open Bandits.Support.ConstructorDimensions
open Bandits.Support.CompletePublicTable
open Bandits.Support.PublicDiscreteDraws
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.OrdinaryMessageCodec
open Bandits.Support.AffineBatchDecoder
open Bandits.Support.FollowerCutoffScan
open Bandits.Support.PrelaunchBufferRecovery
open Bandits.Support.SparseCalendarReplay
open Bandits.Support.QueueReplay
open Bandits.Support.ReplayWeightStability
open Bandits.Support.CanonicalRecordingRates
open Bandits.Support.AffineChannelLaw

/-- Checked replay carries the actual last calendar service as well as the
existing `(served sum, queue)` registers. No boundedness is assumed here. -/
structure ReplayRegisters where
  registers : ℕ × ℕ
  lastService : ℕ
  deriving DecidableEq

/-- A check's position distinguishes invalid incoming registers from invalid
raw arrivals and computed outputs. -/
inductive ReplayFailureKind where
  | inputRegisters
  | arrival
  | service
  | servedSum
  | backlog
  deriving DecidableEq

/-- `completed` counts successful calendar updates before the first failure.
It is an offset into the replay, not an assertion of physical provenance. -/
structure ReplayFailure where
  completed : ℕ
  kind : ReplayFailureKind
  deriving DecidableEq

/-- Literal source register bounds, including initial and terminal fields
(Appendix A:8-14,54-60). Naturals provide the lower bounds and integrality. -/
def replay_register_domain (D Q : ℕ) (s : ReplayRegisters) : Prop :=
  s.registers.1 ≤ Q ∧ s.lastService ≤ D ∧ s.registers.2 ≤ Q

instance instDecidableReplayRegisterDomain (D Q : ℕ) (s : ReplayRegisters) :
    Decidable (replay_register_domain D Q s) :=
  inferInstanceAs (Decidable (s.registers.1 ≤ Q ∧ s.lastService ≤ D ∧ s.registers.2 ≤ Q))

/-- The actual service of one calendar record; disabled records serve zero. -/
def replayService (capacity : ℕ) (s : ReplayRegisters) (r : Bool × ℕ) : ℕ :=
  if r.1 then min capacity (s.registers.2 + r.2) else 0

/-- One update AFTER its incoming register check in `checkedReplay`. The raw
arrival is checked before service, service before queue arithmetic, and both
computed registers before returning a state. The temporary `queue + arrival`
is not a queue field and has no extra `Q` check (source queue rule:04:157-165). -/
def checkedReplayUpdate (D Q capacity : ℕ) (s : ReplayRegisters)
    (r : Bool × ℕ) : Except ReplayFailureKind ReplayRegisters :=
  if r.2 ≤ D then
    let service := replayService capacity s r
    if service ≤ D then
      let next := QueueReplay.transition capacity s.registers r
      if next.1 ≤ Q then
        if next.2 ≤ Q then .ok ⟨next, service⟩
        else .error .backlog
      else .error .servedSum
    else .error .service
  else .error .arrival

/-- Chronological checked replay. On the first bad input/output, return
immediately without running any later update. Bounds are COMPUTED checks,
not hypotheses on the carried buffer or parsed initial queue. In particular
an empty replay checks its initial/terminal registers too. -/
def checkedReplay (D Q capacity offset : ℕ) (s : ReplayRegisters)
    (records : List (Bool × ℕ)) : Except ReplayFailure ReplayRegisters :=
  if replay_register_domain D Q s then
    match records with
    | [] => .ok s
    | r :: rest =>
        match checkedReplayUpdate D Q capacity s r with
        | .error reason => .error ⟨offset, reason⟩
        | .ok next => checkedReplay D Q capacity (offset + 1) next rest
  else .error ⟨offset, .inputRegisters⟩

/-- A successful checked update agrees with the existing queue transition and
returns exactly its service, with every raw/output bound checked. This helper
does not certify the incoming registers; `checkedReplay` checks them first. -/
theorem checkedReplayUpdate_success (D Q capacity : ℕ) (s next : ReplayRegisters)
    (r : Bool × ℕ) (h : checkedReplayUpdate D Q capacity s r = .ok next) :
    r.2 ≤ D ∧ replay_register_domain D Q next ∧
      next.registers = QueueReplay.transition capacity s.registers r ∧
      next.lastService = replayService capacity s r := by
  by_cases ha : r.2 ≤ D
  · by_cases hs : replayService capacity s r ≤ D
    · by_cases hsum : (QueueReplay.transition capacity s.registers r).1 ≤ Q
      · by_cases hb : (QueueReplay.transition capacity s.registers r).2 ≤ Q
        · simp only [checkedReplayUpdate, ite_eq_left ha, ite_eq_left hs,
            ite_eq_left hsum, ite_eq_left hb] at h
          cases h
          exact ⟨ha, ⟨hsum, hs, hb⟩, rfl, rfl⟩
        · simp only [checkedReplayUpdate, ite_eq_left ha, ite_eq_left hs,
            ite_eq_left hsum, ite_eq_right hb] at h
          contradiction
      · simp only [checkedReplayUpdate, ite_eq_left ha, ite_eq_left hs,
          ite_eq_right hsum] at h
        contradiction
    · simp only [checkedReplayUpdate, ite_eq_left ha, ite_eq_right hs] at h
      contradiction
  · simp only [checkedReplayUpdate, ite_eq_right ha] at h
    contradiction

/-- Success checks the initial fields too, even when no round is visited. -/
theorem checkedReplay_success_input (D Q capacity offset : ℕ)
    (s final : ReplayRegisters) (records : List (Bool × ℕ))
    (h : checkedReplay D Q capacity offset s records = .ok final) :
    replay_register_domain D Q s := by
  by_contra hi
  rw [checkedReplay.eq_def, ite_eq_right hi] at h
  contradiction

/-- Invalid initial/terminal input fields fail before any arrival is read. -/
theorem checkedReplay_invalid_input (D Q capacity offset : ℕ) (s : ReplayRegisters)
    (records : List (Bool × ℕ)) (hi : ¬ replay_register_domain D Q s) :
    checkedReplay D Q capacity offset s records = .error ⟨offset, .inputRegisters⟩ := by
  rw [checkedReplay.eq_def, ite_eq_right hi]

/-- Success agrees with pure INTERNAL arithmetic and certifies terminal
fields and every raw arrival. No initialRecords bound is an input to the replay. -/
theorem checkedReplay_success (D Q capacity offset : ℕ)
    (s final : ReplayRegisters) (records : List (Bool × ℕ))
    (h : checkedReplay D Q capacity offset s records = .ok final) :
    replay_register_domain D Q final ∧
      final.registers = QueueReplay.replay capacity s.registers records ∧
      ∀ r ∈ records, r.2 ≤ D := by
  induction records generalizing offset s with
  | nil =>
      have hi := checkedReplay_success_input D Q capacity offset s final [] h
      simp only [checkedReplay, ite_eq_left hi] at h
      cases h
      exact ⟨hi, rfl, by simp only [List.not_mem_nil, false_implies, forall_const]⟩
  | cons r rest ih =>
      have hi := checkedReplay_success_input D Q capacity offset s final (r :: rest) h
      rw [checkedReplay, ite_eq_left hi] at h
      cases hu : checkedReplayUpdate D Q capacity s r with
      | error reason => simp only [hu] at h; contradiction
      | ok next =>
          simp only [hu] at h
          obtain ⟨ha, _, heq, _⟩ := checkedReplayUpdate_success D Q capacity s next r hu
          obtain ⟨hb, hr, hall⟩ := ih (offset + 1) next h
          refine ⟨hb, ?_, ?_⟩
          · rw [hr, heq]
            rfl
          · intro x hx
            rcases List.mem_cons.mp hx with hxr | hxrest
            · subst x; exact ha
            · exact hall x hxrest

/-- Concatenation runs the suffix only after successful checked prefix replay.
An error, with its original position/reason, bypasses the entire suffix. -/
theorem checkedReplay_append (D Q capacity offset : ℕ) (s : ReplayRegisters)
    (initialRecords suffix : List (Bool × ℕ)) :
    checkedReplay D Q capacity offset s (initialRecords ++ suffix) =
      match checkedReplay D Q capacity offset s initialRecords with
      | .error failure => .error failure
      | .ok middle => checkedReplay D Q capacity (offset + initialRecords.length) middle suffix := by
  induction initialRecords generalizing offset s with
  | nil =>
      by_cases hi : replay_register_domain D Q s
      · simp only [List.nil_append, List.length_nil, Nat.add_zero,
          checkedReplay, ite_eq_left hi]
      · simp only [List.nil_append, checkedReplay, ite_eq_right hi]
        rw [checkedReplay.eq_def, ite_eq_right hi]
  | cons r rest ih =>
      by_cases hi : replay_register_domain D Q s
      · cases hu : checkedReplayUpdate D Q capacity s r with
        | error reason =>
            simp only [List.cons_append, checkedReplay, ite_eq_left hi, hu]
        | ok next =>
            simp only [List.cons_append, checkedReplay, ite_eq_left hi, hu]
            simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm,
              Nat.add_left_comm] using ih (offset + 1) next
      · simp only [List.cons_append, checkedReplay, ite_eq_right hi]

/-- A failed prefix stays failed under every later suffix, even if pure
arithmetic on that suffix would drain an overflowing queue. -/
theorem checkedReplay_failure_append (D Q capacity offset : ℕ) (s : ReplayRegisters)
    (initialRecords suffix : List (Bool × ℕ)) (failure : ReplayFailure)
    (h : checkedReplay D Q capacity offset s initialRecords = .error failure) :
    checkedReplay D Q capacity offset s (initialRecords ++ suffix) = .error failure := by
  rw [checkedReplay_append, h]

/-- Every visited prefix of a successful run is itself successful, has the
source register bounds, and agrees with pure replay. Includes the empty and
terminal prefixes and each prefix's actual last service bound. -/
theorem checkedReplay_success_prefix (D Q capacity offset : ℕ)
    (s final : ReplayRegisters) (records : List (Bool × ℕ))
    (h : checkedReplay D Q capacity offset s records = .ok final) (k : ℕ) :
    ∃ middle, checkedReplay D Q capacity offset s (records.take k) = .ok middle ∧
      replay_register_domain D Q middle ∧
      middle.registers = QueueReplay.replay capacity s.registers (records.take k) := by
  have happ := checkedReplay_append D Q capacity offset s
    (records.take k) (records.drop k)
  rw [List.take_append_drop, h] at happ
  cases hp : checkedReplay D Q capacity offset s (records.take k) with
  | error failure => rw [hp] at happ; contradiction
  | ok middle =>
      obtain ⟨hb, heq, _⟩ := checkedReplay_success D Q capacity offset s middle _ hp
      exact ⟨middle, rfl, hb, heq⟩

/-- Last service is the service of the actual final record, computed from the
successful prefix's queue, rather than the terminal queue. -/
theorem checkedReplay_success_last_service (D Q capacity offset : ℕ)
    (s final : ReplayRegisters) (initialRecords : List (Bool × ℕ)) (r : Bool × ℕ)
    (h : checkedReplay D Q capacity offset s (initialRecords ++ [r]) = .ok final) :
    final.lastService = if r.1 then
      min capacity ((QueueReplay.replay capacity s.registers initialRecords).2 + r.2) else 0 := by
  rw [checkedReplay_append] at h
  cases hp : checkedReplay D Q capacity offset s initialRecords with
  | error failure => rw [hp] at h; contradiction
  | ok middle =>
      obtain ⟨hb, heq, _⟩ := checkedReplay_success D Q capacity offset s middle initialRecords hp
      simp only [hp] at h
      rw [checkedReplay, ite_eq_left hb] at h
      cases hu : checkedReplayUpdate D Q capacity middle r with
      | error reason => rw [hu] at h; contradiction
      | ok next =>
          obtain ⟨_, hn, _, hs⟩ := checkedReplayUpdate_success D Q capacity middle next r hu
          simp only [hu] at h
          rw [checkedReplay, ite_eq_left hn] at h
          cases h
          rw [hs, replayService, heq]

/-- A successful prefix followed by the first invalid update returns that update's
error without evaluating any later update. No bounded-prefix assumption is
supplied to the operation; the premise records an actual computed success. -/
theorem checkedReplay_first_invalid (D Q capacity offset : ℕ)
    (s middle : ReplayRegisters) (initialRecords suffix : List (Bool × ℕ))
    (r : Bool × ℕ) (reason : ReplayFailureKind)
    (hp : checkedReplay D Q capacity offset s initialRecords = .ok middle)
    (hu : checkedReplayUpdate D Q capacity middle r = .error reason) :
    checkedReplay D Q capacity offset s (initialRecords ++ r :: suffix) =
      .error ⟨offset + initialRecords.length, reason⟩ := by
  have hb := (checkedReplay_success D Q capacity offset s middle initialRecords hp).1
  rw [checkedReplay_append]
  simp only [hp]
  rw [checkedReplay, ite_eq_left hb, hu]

/-- Parameterized first-overflow regression: a valid computed prefix plus an
in-domain arrival and service, but overflowing resulting queue, cannot be
rescued by later draining. The transient addition has no extra upper bound. -/
theorem checkedReplay_first_backlog_overflow (D Q capacity offset : ℕ)
    (s middle : ReplayRegisters) (initialRecords suffix : List (Bool × ℕ)) (a : ℕ)
    (hp : checkedReplay D Q capacity offset s initialRecords = .ok middle)
    (ha : a ≤ D) (hs : min capacity (middle.registers.2 + a) ≤ D)
    (hS : middle.registers.1 + min capacity (middle.registers.2 + a) ≤ Q)
    (hq : Q < middle.registers.2 + a - min capacity (middle.registers.2 + a)) :
    checkedReplay D Q capacity offset s (initialRecords ++ (true, a) :: suffix) =
      .error ⟨offset + initialRecords.length, .backlog⟩ := by
  apply checkedReplay_first_invalid D Q capacity offset s middle initialRecords suffix
    (true, a) .backlog hp
  simp only [checkedReplayUpdate, ite_eq_left ha, replayService,
    ite_true, ite_eq_left hs, QueueReplay.transition, ite_eq_left hS,
    ite_eq_right (Nat.not_le.mpr hq)]

/-- The review's first overflow is rejected for EVERY suffix, including its
255 zero-arrival drain rounds. This is the queue-arithmetic instance, not a
claim that a supplied parser/buffer history is a physical execution. -/
theorem review_0133_first_overflow (suffix : List (Bool × ℕ)) :
    checkedReplay 1048576 68719476736 4 0 ⟨(0, 68719476736), 0⟩
      ((true, 128) :: suffix) = .error ⟨0, .backlog⟩ := by
  apply checkedReplay_first_backlog_overflow 1048576 68719476736 4 0
    ⟨(0, 68719476736), 0⟩ ⟨(0, 68719476736), 0⟩ [] suffix 128
  · rfl
  all_goals norm_num

/-- A temporary sum beyond the queue bound is allowed when the actual
resulting queue and accumulated service are within their source domains. -/
theorem checkedReplay_temporary_addition_allowed :
    checkedReplay 128 128 128 0 ⟨(0, 128), 0⟩ [(true, 128)] =
      .ok ⟨(128, 128), 128⟩ := rfl

/-- Calendar implementation computes only the current arrival before its
checks; no later arrival or update is evaluated after a failure. -/
def checkedCalendarReplay (D Q capacity offset : ℕ) (s : ReplayRegisters)
    (arrivalAt : ℕ → ℕ) (rounds : List ℕ) : Except ReplayFailure ReplayRegisters :=
  if replay_register_domain D Q s then
    match rounds with
    | [] => .ok s
    | r :: rest =>
        match checkedReplayUpdate D Q capacity s (true, arrivalAt r) with
        | .error reason => .error ⟨offset, reason⟩
        | .ok next => checkedCalendarReplay D Q capacity (offset + 1) next arrivalAt rest
  else .error ⟨offset, .inputRegisters⟩

/-- The chronological calendar implementation has exactly the checked record
semantics. This equation is for proofs, not eager computation of future arrivals. -/
theorem checkedCalendarReplay_eq (D Q capacity offset : ℕ) (s : ReplayRegisters)
    (arrivalAt : ℕ → ℕ) (rounds : List ℕ) :
    checkedCalendarReplay D Q capacity offset s arrivalAt rounds =
      checkedReplay D Q capacity offset s (rounds.map fun r => (true, arrivalAt r)) := by
  induction rounds generalizing offset s with
  | nil => rfl
  | cons r rest ih =>
      by_cases hi : replay_register_domain D Q s
      · cases hu : checkedReplayUpdate D Q capacity s (true, arrivalAt r) with
        | error reason =>
            simp only [checkedCalendarReplay, checkedReplay, ite_eq_left hi, List.map_cons, hu]
        | ok next =>
            simpa only [checkedCalendarReplay, checkedReplay, ite_eq_left hi, List.map_cons, hu]
              using ih (offset + 1) next
      · simp only [checkedCalendarReplay, checkedReplay, List.map_cons, ite_eq_right hi]

/-- Calendar failure persists with the original position/reason for arbitrary
later calendar rounds. The later arrival values are immaterial. -/
theorem checkedCalendarReplay_failure_append (D Q capacity offset : ℕ)
    (s : ReplayRegisters) (arrivalAt : ℕ → ℕ) (first rest : List ℕ)
    (failure : ReplayFailure)
    (h : checkedCalendarReplay D Q capacity offset s arrivalAt first = .error failure) :
    checkedCalendarReplay D Q capacity offset s arrivalAt (first ++ rest) =
      .error failure := by
  rw [checkedCalendarReplay_eq] at h ⊢
  rw [List.map_append]
  exact checkedReplay_failure_append _ _ _ _ _ _ _ failure h

/-- The source-capped positive rate and its exact integer scale `n = eta * D`.
The carried follower state uses the existing positive `LearningRate` carrier. -/
structure RateInput (p : Parameters) where
  eta : LearningRate
  sourceCap : eta.val ≤
    1 / (1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ))
  n : ℕ
  n_scale : (n : ℝ) = eta.val * (D p : ℝ)

/-- The exact source cap implies the integer service capacity is at most `D`. -/
theorem four_n_le_D (p : Parameters) (rate : RateInput p) :
    4 * rate.n ≤ D p := by
  have hm : (1 : ℝ) ≤ (p.m : ℝ) := by
    exact_mod_cast (Nat.le_trans (by decide) p.two_le_m)
  have hK : (1 : ℝ) ≤ (p.K : ℝ) := by
    have htwo : 2 ≤ p.K := p.two_le_m.trans (Nat.le_of_lt p.m_lt_K)
    exact_mod_cast (Nat.le_trans (by decide) htwo)
  have hLnat : 1 ≤ L_stab p := L_stab_ge_one p
  have hL : (1 : ℝ) ≤ (L_stab p : ℝ) := by exact_mod_cast hLnat
  have hden : 0 < 1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ) := by
    positivity
  have hdenLower : (1024 : ℝ) ≤
      1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ) := by
    calc
      (1024 : ℝ) = 1024 * 1 * 1 * 1 := by ring
      _ ≤ 1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ) := by
        gcongr
  have hetaDen : rate.eta.val *
      (1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ)) ≤ 1 :=
    (le_div_iff₀ hden).mp rate.sourceCap
  have heta1024 : rate.eta.val * 1024 ≤ 1 := by
    calc
      rate.eta.val * 1024 ≤ rate.eta.val *
          (1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ)) :=
        mul_le_mul_of_nonneg_left hdenLower (le_of_lt rate.eta.property)
      _ ≤ 1 := hetaDen
  have heta4 : 4 * rate.eta.val ≤ 1 := by nlinarith
  have hDnonneg : (0 : ℝ) ≤ (D p : ℝ) := Nat.cast_nonneg _
  have hreal : ((4 * rate.n : ℕ) : ℝ) ≤ (D p : ℝ) := by
    calc
      ((4 * rate.n : ℕ) : ℝ) = 4 * (rate.n : ℝ) := by norm_num
      _ = (4 * rate.eta.val) * (D p : ℝ) := by rw [rate.n_scale]; ring
      _ ≤ 1 * (D p : ℝ) := mul_le_mul_of_nonneg_right heta4 hDnonneg
      _ = (D p : ℝ) := by ring
  exact_mod_cast hreal

/-- The integer scale is positive under the exact source witness. -/
theorem rate_n_pos (p : Parameters) (rate : RateInput p) : 0 < rate.n := by
  have hD : 0 < (D p : ℝ) := Nat.cast_pos.mpr (D_pos p)
  have hn : 0 < (rate.n : ℝ) := by
    rw [rate.n_scale]
    exact mul_pos rate.eta.property hD
  exact_mod_cast hn

/-- The decoder's current round input, formed only from the selected public
row, the supplied typed feedback, and the carried pre-choice follower status. -/
def currentRoundInput (p : Parameters) (i : Fin (p.m - 1))
    (row : CompleteRow p) (t : Fin p.T) (feedback : Observation p)
    (rate : RateInput p)
    (state : ReferencePrelaunchFollower.State p rate.eta) : RoundInput (width p) := by
  classical
  exact {
    selected := decide (slotDraw (row.2 t).1 = downSlot ∧
      selectedFollowerDraw p.two_le_m p.m_lt_K (row.2 t).1 = i)
    receiverEnabled := decide (state.status = .unoccupied)
    sample := (row.2 t).2 (0, i)
    roundedReward := feedback.val.val
  }

/-- The single local selection test derived from the current complete row. -/
def downSelected (p : Parameters) (i : Fin (p.m - 1))
    (row : CompleteRow p) (t : Fin p.T) : Prop :=
  slotDraw (row.2 t).1 = downSlot ∧
    selectedFollowerDraw p.two_le_m p.m_lt_K (row.2 t).1 = i

/-- The decoder input is eligible exactly on a selected DOWN round while this
follower was unoccupied at arm choice and its own typed feedback is positive. -/
theorem currentRoundInput_eligible_iff (p : Parameters) (i : Fin (p.m - 1))
    (row : CompleteRow p) (t : Fin p.T) (feedback : Observation p)
    (rate : RateInput p) (state : ReferencePrelaunchFollower.State p rate.eta) :
    AffineBatchDecoder.eligible (currentRoundInput p i row t feedback rate state) ↔
      downSelected p i row t ∧ state.status = .unoccupied ∧ 0 < feedback.val.val := by
  simp only [AffineBatchDecoder.eligible, currentRoundInput, downSelected,
    decide_eq_true_eq]

/-- Dependence of the existing total-trace decoder on only its current input.
No observations or rounds away from `t` are part of this statement. -/
theorem decodeStep_depends_on_current_input (p : Parameters)
    (trace trace' : AffineBatchDecoder.Trace p)
    (batch : AffineBatchDecoder.State p.T (AffineBatchDecoder.width p))
    (t : Fin p.T) (hcurrent : trace t = trace' t) :
    AffineBatchDecoder.decodeStep p trace batch t =
      AffineBatchDecoder.decodeStep p trace' batch t := by
  have hpositive : AffineBatchDecoder.positiveAt p trace t =
      AffineBatchDecoder.positiveAt p trace' t := by
    unfold AffineBatchDecoder.positiveAt AffineBatchDecoder.entry
    rw [hcurrent]
  unfold AffineBatchDecoder.decodeStep
  congr 1
  · unfold AffineBatchDecoder.step
    simp only [hpositive]
  · unfold AffineBatchDecoder.stepOutput
    simp only [hpositive]

/-- A total function containing the supplied current round input. This is an
administrative extension required by `decodeStep`'s API, not a history. -/
def currentInputExtension (p : Parameters)
    (input : AffineBatchDecoder.RoundInput (AffineBatchDecoder.width p)) :
    AffineBatchDecoder.Trace p := fun _ => input

/-- Call the existing decoder on the carried batch and the current row-derived
observation. The extension's other coordinates are erased by the theorem above. -/
def currentDecodeStep (p : Parameters) (i : Fin (p.m - 1))
    (row : CompleteRow p) (t : Fin p.T) (feedback : Observation p)
    (rate : RateInput p)
    (state : ReferencePrelaunchFollower.State p rate.eta) :=
  AffineBatchDecoder.decodeStep p
    (currentInputExtension p (currentRoundInput p i row t feedback rate state))
    state.downBatch t

/-- The decoder's actual optional word, flattened by the existing codec
equivalence and parsed by the existing DOWN parser. -/
noncomputable def parsedCurrentOutput (p : Parameters) (i : Fin (p.m - 1))
    (row : CompleteRow p) (t : Fin p.T) (feedback : Observation p)
    (rate : RateInput p)
    (state : ReferencePrelaunchFollower.State p rate.eta) :
    Option (DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)) :=
  parseDown (ReferencePrelaunchFollower.codecParams p rate.eta)
    ((currentDecodeStep p i row t feedback rate state).2.map
      (wordEquivFlat (ReferencePrelaunchFollower.codecParams p rate.eta)).symm)

/-- Convert a parsed one-based DOWN start into its actual finite table index. -/
def downStart (p : Parameters) (rate : RateInput p)
    (M : DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)) : Fin p.T := by
  have hdom := M.property
  simp only [downAdmissible] at hdom
  have hsigma := PrelaunchBufferRecovery.down_sigma_pos rate.eta M
  have hsub : M.val.sigma - 1 < M.val.sigma := Nat.sub_lt hsigma (by decide)
  exact ⟨M.val.sigma - 1, hsub.trans_le hdom.2.1⟩

/-- The finite start denotes precisely the parsed source calendar round. -/
theorem downStart_val_add_one (p : Parameters) (rate : RateInput p)
    (M : DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)) :
    (downStart p rate M).val + 1 = M.val.sigma := by
  have hdom := M.property
  simp only [downAdmissible] at hdom
  simp only [downStart]
  omega

/-- The source proposal scan, at the actual finite start from parsed `M`. -/
noncomputable def acceptedCutoffScan (p : Parameters) (rate : RateInput p)
    (M : DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)) (t : Fin p.T)
    (hstart : (downStart p rate M).val ≤ t.val) (row : CompleteRow p) :
    FollowerCutoffScan.ScanResult p.T :=
  FollowerCutoffScan.completeRowCutoffScan p rate.eta.val
    (downStart p rate M) t hstart row

/-- The start bound induced by a locally accepted DOWN record. Keeping this
proof-producing function explicit makes every operation equation refer to the
same scan input. -/
theorem acceptedDownStartLE (p : Parameters) (rate : RateInput p)
    (M : DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (t : Fin p.T) (state : ReferencePrelaunchFollower.State p rate.eta)
    (haccepted : acceptDown (ReferencePrelaunchFollower.codecParams p rate.eta)
      (ReferencePrelaunchFollower.acceptedStart state) (t.val + 1) M) :
    (downStart p rate M).val ≤ t.val := by
  have hsigma := downStart_val_add_one p rate M
  have htime := haccepted.2
  omega

/-- Every accepted start yields a nonempty source interval, an endpoint at or
before `t+2`, and no more than `T` calendar rounds to recover. -/
theorem acceptedCutoff_interval_bounds (p : Parameters) (rate : RateInput p)
    (M : DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)) (t : Fin p.T)
    (row : CompleteRow p)
    (state : ReferencePrelaunchFollower.State p rate.eta) (haccepted :
      acceptDown (ReferencePrelaunchFollower.codecParams p rate.eta)
        (ReferencePrelaunchFollower.acceptedStart state)
        (t.val + 1) M) :
    M.val.sigma < (acceptedCutoffScan p rate M t
        (acceptedDownStartLE p rate M t state haccepted) row).endpoint ∧
      (acceptedCutoffScan p rate M t
        (acceptedDownStartLE p rate M t state haccepted) row).endpoint ≤ t.val + 2 ∧
      (acceptedCutoffScan p rate M t
        (acceptedDownStartLE p rate M t state haccepted) row).endpoint ≤ p.T + 1 ∧
      (acceptedCutoffScan p rate M t
        (acceptedDownStartLE p rate M t state haccepted) row).endpoint - M.val.sigma ≤ p.T := by
  let sigma := downStart p rate M
  have hsigma : sigma.val ≤ t.val := by
    have hstart := downStart_val_add_one p rate M
    have hcurrent := haccepted.2
    omega
  have hscan := FollowerCutoffScan.followerCutoffScan_endpoint_bounds
    p rate.eta.val rate.eta.property rate.sourceCap sigma t hsigma
    (FollowerCutoffScan.completeRowProposalBit p rate.eta.val row)
  have hscan' : sigma.val + 1 <
        (acceptedCutoffScan p rate M t hsigma row).endpoint ∧
      (acceptedCutoffScan p rate M t hsigma row).endpoint ≤ t.val + 2 := by
    change sigma.val + 1 < (FollowerCutoffScan.followerCutoffScan p rate.eta.val
      sigma t hsigma (FollowerCutoffScan.completeRowProposalBit p rate.eta.val row)).endpoint ∧
      (FollowerCutoffScan.followerCutoffScan p rate.eta.val sigma t hsigma
        (FollowerCutoffScan.completeRowProposalBit p rate.eta.val row)).endpoint ≤ t.val + 2
    exact ⟨hscan.1, hscan.2.1⟩
  have hstart := downStart_val_add_one p rate M
  have hsigmapos := PrelaunchBufferRecovery.down_sigma_pos rate.eta M
  refine ⟨?_, hscan'.2, ?_, ?_⟩
  · rw [← hstart]
    exact hscan'.1
  · omega
  · omega

/-- The carried integer registers satisfy the source field domains. -/
def registerInputDomain (p : Parameters) (rate : RateInput p)
    (state : ReferencePrelaunchFollower.State p rate.eta) : Prop :=
  state.S ≤ p.T * D p ∧ state.delta ≤ D p ∧ state.backlog ≤ p.T * D p

/-- The decoder batch is in its source pre-call domain: pending is below quota
and every retained completed batch has exactly quota entries. -/
def decoderInputDomain (p : Parameters)
    (batch : AffineBatchDecoder.State p.T (AffineBatchDecoder.width p)) : Prop :=
  batch.pending.length < AffineBatchDecoder.quota p ∧
    ∀ completed ∈ batch.completed, completed.length = AffineBatchDecoder.quota p

/-- One carried buffer record has a source-valid one-based calendar stamp and a
quantized observation. No assertion of logging or execution provenance is made. -/
def bufferRecordDomain (p : Parameters)
    (record : SparseCalendarReplay.SparseCalendarRecord p.K) : Prop :=
  1 ≤ record.calendarRound ∧ record.calendarRound ≤ p.T ∧
    ∃ q : Fin (D p + 1),
      record.observation.val = (q.val : ℝ) / (D p : ℝ)

/-- The carried sparse buffer has source calendar domains and at most one
record for each arm and calendar round. -/
def bufferInputDomain (p : Parameters)
    (buffer : List (SparseCalendarReplay.SparseCalendarRecord p.K)) : Prop :=
  (∀ record ∈ buffer, bufferRecordDomain p record) ∧
    (buffer.map fun record => (record.calendarRound, record.pilot)).Nodup

/-- Input-domain checks required before the selected DOWN operation is
evaluated. The fields in these predicates remain explicit at each call site. -/
def operationInputDomain (p : Parameters) (rate : RateInput p)
    (state : ReferencePrelaunchFollower.State p rate.eta) : Prop :=
  registerInputDomain p rate state ∧ decoderInputDomain p state.downBatch ∧
    bufferInputDomain p state.buffer

/-- Every calendar round in the nonempty accepted interval is represented by
an enabled queue record, including zero arrivals. -/
def recoveryRounds (p : Parameters) (rate : RateInput p)
    (M : DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (ell : ℕ) : List ℕ :=
  SparseCalendarReplay.sparseCalendarRounds M.val.sigma ell

/-- The arrival recomputed from the carried buffer on one source calendar
round, using the parsed DOWN arm and exponent. -/
noncomputable def bufferArrivalAt (p : Parameters) (rate : RateInput p)
    (M : DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (state : ReferencePrelaunchFollower.State p rate.eta) (r : ℕ) : ℕ :=
  SparseCalendarReplay.sparseBufferContribution (p.m - 1) (D p : ℝ)
    rate.eta.val M.val.h (PrelaunchBufferRecovery.downArm rate.eta M) r state.buffer

/-- The actual buffer-derived arrivals on every round of `[M.sigma, ell)`. -/
noncomputable def recoveryArrivals (p : Parameters) (rate : RateInput p)
    (M : DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (state : ReferencePrelaunchFollower.State p rate.eta) (ell : ℕ)
    : List ℕ :=
  (recoveryRounds p rate M ell).map (bufferArrivalAt p rate M state)

/-- The queue receives one enabled record per calendar round, even when its
buffer-derived arrival is zero. -/
noncomputable def recoveryQueueRecords (p : Parameters)
    (rate : RateInput p) (M : DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (state : ReferencePrelaunchFollower.State p rate.eta) (ell : ℕ) :
    List (Bool × ℕ) :=
  (recoveryArrivals p rate M state ell).map fun arrival => (true, arrival)

/-- INTERNAL unchecked arithmetic from score zero and the parsed DOWN backlog.
This is not the ordinary checked operation and is not used to install fields. -/
noncomputable def recoveredRegisters (p : Parameters) (rate : RateInput p)
    (M : DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (state : ReferencePrelaunchFollower.State p rate.eta) (ell : ℕ) : ℕ × ℕ :=
  QueueReplay.replay (4 * rate.n) (0, M.val.q)
    (recoveryQueueRecords p rate M state ell)

/-- The queue state immediately before its final scanned calendar round. -/
noncomputable def recoveredRegistersBeforeLast (p : Parameters)
    (rate : RateInput p) (M : DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (state : ReferencePrelaunchFollower.State p rate.eta) (ell : ℕ)
    (_hinterval : M.val.sigma < ell) : ℕ × ℕ :=
  QueueReplay.replay (4 * rate.n) (0, M.val.q)
    (recoveryQueueRecords p rate M state (ell - 1))

/-- The final enabled queue transition at calendar round `ell-1`. -/
noncomputable def recoveredLastTransition (p : Parameters)
    (rate : RateInput p) (M : DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (state : ReferencePrelaunchFollower.State p rate.eta) (ell : ℕ)
    (hinterval : M.val.sigma < ell) : ℕ × ℕ :=
  QueueReplay.transition (4 * rate.n)
    (recoveredRegistersBeforeLast p rate M state ell hinterval)
    (true, bufferArrivalAt p rate M state (ell - 1))

/-- The service on `ell-1`, computed as the score increment of the existing
last `QueueReplay.transition`. -/
noncomputable def recoveredLastService (p : Parameters)
    (rate : RateInput p) (M : DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (state : ReferencePrelaunchFollower.State p rate.eta) (ell : ℕ)
    (hinterval : M.val.sigma < ell) : ℕ :=
  (recoveredLastTransition p rate M state ell hinterval).1 -
    (recoveredRegistersBeforeLast p rate M state ell hinterval).1

/-- The record list's final entry is the actual calendar round `ell-1`. -/
theorem recoveryQueueRecords_append_last (p : Parameters) (rate : RateInput p)
    (M : DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (state : ReferencePrelaunchFollower.State p rate.eta) (ell : ℕ)
    (hinterval : M.val.sigma < ell) :
    recoveryQueueRecords p rate M state ell =
      recoveryQueueRecords p rate M state (ell - 1) ++
        [(true, bufferArrivalAt p rate M state (ell - 1))] := by
  simp only [recoveryQueueRecords, recoveryArrivals, recoveryRounds]
  rw [SparseCalendarReplay.sparseCalendarRounds_append_last hinterval, List.map_append]
  rw [List.map_append]
  rfl

/-- The final replay is exactly the saved all-calendar-round replay followed by
the `ell-1` transition. -/
theorem recoveredRegisters_eq_lastTransition (p : Parameters) (rate : RateInput p)
    (M : DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (state : ReferencePrelaunchFollower.State p rate.eta) (ell : ℕ)
    (hinterval : M.val.sigma < ell) :
    recoveredRegisters p rate M state ell =
      recoveredLastTransition p rate M state ell hinterval := by
  rw [recoveredRegisters, recoveryQueueRecords_append_last p rate M state ell hinterval,
    QueueReplay.replay_append]
  rfl

/-- The recovered last service is the last enabled transition's capped service. -/
theorem recoveredLastService_eq_min (p : Parameters) (rate : RateInput p)
    (M : DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (state : ReferencePrelaunchFollower.State p rate.eta) (ell : ℕ)
    (hinterval : M.val.sigma < ell) :
    recoveredLastService p rate M state ell hinterval =
      min (4 * rate.n)
        ((recoveredRegistersBeforeLast p rate M state ell hinterval).2 +
          bufferArrivalAt p rate M state (ell - 1)) := by
  simp [recoveredLastService, recoveredLastTransition, QueueReplay.transition]

/-- INTERNAL terminal-only predicate retained for arithmetic clients. It does
not certify intermediate queues and is NOT the operation's acceptance guard. -/
def recoveredOutputDomain (p : Parameters) (rate : RateInput p)
    (M : DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (state : ReferencePrelaunchFollower.State p rate.eta) (ell : ℕ)
    (hinterval : M.val.sigma < ell) : Prop :=
  (∀ arrival ∈ recoveryArrivals p rate M state ell,
      arrival ≤ D p) ∧
    (recoveredRegisters p rate M state ell).1 ≤ p.T * D p ∧
    recoveredLastService p rate M state ell hinterval ≤ D p ∧
    (recoveredRegisters p rate M state ell).2 ≤ p.T * D p

/-- Actual chronological recovery from the CARRIED buffer. Initial parsed
queue and zero sum/service are checked, then every calendar round is checked,
including missing-record/zero-arrival rounds (06:192-209; Appendix A:8-14).
The recursive calendar implementation never evaluates a later arrival after
failure and never supplies an invalid queue to a later update. -/
noncomputable def checkedRecovery (p : Parameters) (rate : RateInput p)
    (M : DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (state : ReferencePrelaunchFollower.State p rate.eta) (ell : ℕ) :
    Except ReplayFailure ReplayRegisters :=
  checkedCalendarReplay (D p) (p.T * D p) (4 * rate.n) 0 ⟨(0, M.val.q), 0⟩
    (bufferArrivalAt p rate M state) (recoveryRounds p rate M ell)

/-- Record semantics of the actual checked calendar implementation. -/
theorem checkedRecovery_eq_checkedReplay (p : Parameters) (rate : RateInput p)
    (M : DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (state : ReferencePrelaunchFollower.State p rate.eta) (ell : ℕ) :
    checkedRecovery p rate M state ell =
      checkedReplay (D p) (p.T * D p) (4 * rate.n) 0 ⟨(0, M.val.q), 0⟩
        (recoveryQueueRecords p rate M state ell) := by
  rw [checkedRecovery, checkedCalendarReplay_eq]
  simp only [recoveryQueueRecords, recoveryArrivals, List.map_map, Function.comp_def]

/-- Successful recovery agrees with pure queue replay and checks all returned
fields and raw arrivals. The only extra premise is its computed success branch. -/
theorem checkedRecovery_success (p : Parameters) (rate : RateInput p)
    (M : DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (state : ReferencePrelaunchFollower.State p rate.eta) (ell : ℕ)
    (final : ReplayRegisters) (h : checkedRecovery p rate M state ell = .ok final) :
    replay_register_domain (D p) (p.T * D p) final ∧
      final.registers = recoveredRegisters p rate M state ell ∧
      ∀ arrival ∈ recoveryArrivals p rate M state ell, arrival ≤ D p := by
  rw [checkedRecovery_eq_checkedReplay] at h
  obtain ⟨hb, heq, ha⟩ := checkedReplay_success _ _ _ _ _ final _ h
  refine ⟨hb, heq, ?_⟩
  intro arrival harrival
  exact ha (true, arrival) (List.mem_map.mpr ⟨arrival, harrival, rfl⟩)

/-- Each visited calendar prefix has checked source bounds; prefix zero is
the parsed initial queue, and the full prefix is the terminal queue. -/
theorem checkedRecovery_success_prefix (p : Parameters) (rate : RateInput p)
    (M : DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (state : ReferencePrelaunchFollower.State p rate.eta) (ell : ℕ)
    (final : ReplayRegisters) (h : checkedRecovery p rate M state ell = .ok final)
    (k : ℕ) :
    ∃ middle, checkedReplay (D p) (p.T * D p) (4 * rate.n) 0 ⟨(0, M.val.q), 0⟩
        ((recoveryQueueRecords p rate M state ell).take k) = .ok middle ∧
      replay_register_domain (D p) (p.T * D p) middle ∧
      middle.registers = QueueReplay.replay (4 * rate.n) (0, M.val.q)
        ((recoveryQueueRecords p rate M state ell).take k) := by
  rw [checkedRecovery_eq_checkedReplay] at h
  exact checkedReplay_success_prefix _ _ _ _ _ final _ h k

/-- Successful recovery returns service on `ell-1`, from the genuine final
transition, even when that round has no saved arrival. -/
theorem checkedRecovery_success_last_service (p : Parameters) (rate : RateInput p)
    (M : DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (state : ReferencePrelaunchFollower.State p rate.eta) (ell : ℕ)
    (hinterval : M.val.sigma < ell) (final : ReplayRegisters)
    (h : checkedRecovery p rate M state ell = .ok final) :
    final.lastService = recoveredLastService p rate M state ell hinterval := by
  rw [checkedRecovery_eq_checkedReplay,
    recoveryQueueRecords_append_last p rate M state ell hinterval] at h
  have hs := checkedReplay_success_last_service _ _ _ _ _ final _ _ h
  rw [recoveredLastService_eq_min]
  exact hs

/-- All arrival entries fed to `QueueReplay` are enabled, including zero. -/
theorem recoveryQueueRecords_all_enabled (p : Parameters) (rate : RateInput p)
    (M : DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (state : ReferencePrelaunchFollower.State p rate.eta) (ell : ℕ) :
    ∀ record ∈ recoveryQueueRecords p rate M state ell,
      record.1 = true := by
  intro record hrecord
  obtain ⟨arrival, _, rfl⟩ := List.mem_map.mp hrecord
  rfl

/-- The interval has exactly `ell - sigma` calendar entries. -/
theorem recoveryRounds_length (p : Parameters) (rate : RateInput p)
    (M : DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)) (ell : ℕ) :
    (recoveryRounds p rate M ell).length = ell - M.val.sigma := by
  simp [recoveryRounds, SparseCalendarReplay.sparseCalendarRounds_length]

/-- Reasons for not entering this local operation. In particular, an occupied
pre-choice status is a no-op, not an acceptance or a decoder update. -/
inductive SkipReason where
  | notSelectedDown
  | occupiedAtChoice
  deriving DecidableEq

/-- Input-domain failures checked before calling the decoder. -/
inductive InputFailure where
  | registers
  | decoderBatch
  | sparseBuffer
  deriving DecidableEq

/-- Output-domain failures checked before installing any recovered registers. -/
inductive OutputFailure where
  | arrival
  | servedSum
  | lastService
  | backlog
  | replay (failure : ReplayFailure)
  deriving DecidableEq

/-- The result of the ordinary local DOWN operation. Rejected words retain the
advanced decoder batch; accepted results expose the exact reply, scan, and
queue calculations. Domain failures carry no next state for the protocol to
store. -/
inductive LocalDownResult (p : Parameters) (rate : RateInput p) where
  | skipped
      (before : ReferencePrelaunchFollower.State p rate.eta)
      (reason : SkipReason)
  | inputFailure
      (before : ReferencePrelaunchFollower.State p rate.eta)
      (reason : InputFailure)
  | decodeOrParseRejected
      (before after : ReferencePrelaunchFollower.State p rate.eta)
      (raw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)))
  | parsedButUnaccepted
      (before after : ReferencePrelaunchFollower.State p rate.eta)
      (raw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)))
      (reply : DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
  | outputFailure
      (before : ReferencePrelaunchFollower.State p rate.eta)
      (reason : OutputFailure)
  | accepted
      (before after : ReferencePrelaunchFollower.State p rate.eta)
      (raw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)))
      (reply : DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
      (scan : FollowerCutoffScan.ScanResult p.T)
      (registers : ℕ × ℕ)
      (lastService : ℕ)

/-- The ordinary selected-unoccupied DOWN transition after logging. The
decoder call, parser, acceptance predicate, cutoff scan, carried-buffer
recovery, and output-domain checks all occur inside this definition. -/
noncomputable def downTransition (p : Parameters)
    (i : Fin (p.m - 1)) (row : CompleteRow p) (t : Fin p.T)
    (feedback : Observation p) (rate : RateInput p)
    (state : ReferencePrelaunchFollower.State p rate.eta) :
    LocalDownResult p rate := by
  classical
  exact if hselected : downSelected p i row t then
    if hstatus : state.status = .unoccupied then
      if hregisters : registerInputDomain p rate state then
        if hbatch : decoderInputDomain p state.downBatch then
          if hbuffer : bufferInputDomain p state.buffer then
            let decoded := currentDecodeStep p i row t feedback rate state
            let parsed := parseDown (ReferencePrelaunchFollower.codecParams p rate.eta)
              (decoded.2.map (wordEquivFlat (ReferencePrelaunchFollower.codecParams p rate.eta)).symm)
            let afterDecode := { state with downBatch := decoded.1 }
            match parsed with
            | none =>
                .decodeOrParseRejected state afterDecode decoded.2
            | some M =>
                if haccepted : acceptDown (ReferencePrelaunchFollower.codecParams p rate.eta)
                    (ReferencePrelaunchFollower.acceptedStart state) (t.val + 1) M then
                  have hstart := acceptedDownStartLE p rate M t state haccepted
                  let scan := acceptedCutoffScan p rate M t hstart row
                  match checkedRecovery p rate M state scan.endpoint with
                  | .error failure => .outputFailure state (.replay failure)
                  | .ok recovered =>
                      .accepted state
                        { afterDecode with
                          lastDown := some M
                          S := recovered.registers.1
                          delta := recovered.lastService
                          backlog := recovered.registers.2
                          status := if scan.endpoint = t.val + 2 then
                            .pending else .unoccupied
                          buffer := [] }
                        decoded.2 M scan recovered.registers recovered.lastService
                else
                  .parsedButUnaccepted state afterDecode decoded.2 M
          else .inputFailure state .sparseBuffer
        else .inputFailure state .decoderBatch
      else .inputFailure state .registers
    else .skipped state .occupiedAtChoice
  else .skipped state .notSelectedDown

/-- No DOWN selection means the carried state is returned without a decoder or
install update. -/
theorem downTransition_notSelected (p : Parameters) (i : Fin (p.m - 1))
    (row : CompleteRow p) (t : Fin p.T) (feedback : Observation p)
    (rate : RateInput p)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (hselected : ¬ downSelected p i row t) :
    downTransition p i row t feedback rate state =
      .skipped state .notSelectedDown := by
  simp [downTransition, hselected]

/-- An occupied pre-choice status means this selected DOWN slot is a no-op for
this follower's decoder and install registers. -/
theorem downTransition_occupied (p : Parameters) (i : Fin (p.m - 1))
    (row : CompleteRow p) (t : Fin p.T) (feedback : Observation p)
    (rate : RateInput p)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (hselected : downSelected p i row t)
    (hoccupied : state.status ≠ .unoccupied) :
    downTransition p i row t feedback rate state =
      .skipped state .occupiedAtChoice := by
  simp [downTransition, hselected, hoccupied]

/-- A parser rejection keeps exactly the decoder's resulting batch and all
other carried registers and the already-logged buffer. The result is ordinary
rejection, not a domain failure. -/
theorem downTransition_rejected_equation (p : Parameters) (i : Fin (p.m - 1))
    (row : CompleteRow p) (t : Fin p.T) (feedback : Observation p)
    (rate : RateInput p)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (hselected : downSelected p i row t)
    (hstatus : state.status = .unoccupied)
    (hregisters : registerInputDomain p rate state)
    (hbatch : decoderInputDomain p state.downBatch)
    (hbuffer : bufferInputDomain p state.buffer)
    (hparsed : parsedCurrentOutput p i row t feedback rate state = none) :
    downTransition p i row t feedback rate state =
      .decodeOrParseRejected state
        { state with downBatch := (currentDecodeStep p i row t feedback rate state).1 }
        (currentDecodeStep p i row t feedback rate state).2 := by
  have hparsed' : parseDown (ReferencePrelaunchFollower.codecParams p rate.eta)
      (((currentDecodeStep p i row t feedback rate state).2).map
        (wordEquivFlat (ReferencePrelaunchFollower.codecParams p rate.eta)).symm) = none := by
    simpa only [parsedCurrentOutput] using hparsed
  simp [downTransition, hselected, hstatus, hregisters, hbatch, hbuffer, hparsed']

/-- A parsed but stale or otherwise locally unaccepted reply preserves every
field except the decoder batch, while exposing the exact parsed reply. -/
theorem downTransition_unaccepted_equation (p : Parameters) (i : Fin (p.m - 1))
    (row : CompleteRow p) (t : Fin p.T) (feedback : Observation p)
    (rate : RateInput p)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (hselected : downSelected p i row t)
    (hstatus : state.status = .unoccupied)
    (hregisters : registerInputDomain p rate state)
    (hbatch : decoderInputDomain p state.downBatch)
    (hbuffer : bufferInputDomain p state.buffer)
    (M : DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hparsed : parsedCurrentOutput p i row t feedback rate state = some M)
    (hnotaccepted : ¬ acceptDown (ReferencePrelaunchFollower.codecParams p rate.eta)
      (ReferencePrelaunchFollower.acceptedStart state) (t.val + 1) M) :
    downTransition p i row t feedback rate state =
      .parsedButUnaccepted state
        { state with downBatch := (currentDecodeStep p i row t feedback rate state).1 }
        (currentDecodeStep p i row t feedback rate state).2 M := by
  have hparsed' : parseDown (ReferencePrelaunchFollower.codecParams p rate.eta)
      (((currentDecodeStep p i row t feedback rate state).2).map
        (wordEquivFlat (ReferencePrelaunchFollower.codecParams p rate.eta)).symm) = some M := by
    simpa only [parsedCurrentOutput] using hparsed
  simp [downTransition, hselected, hstatus, hregisters, hbatch, hbuffer,
    hparsed', hnotaccepted]

/-- The accepted branch consumes the COMPUTED checked success, not terminal
bounds or a supplied all-prefix invariant. All installed fields and the exact
reply are visible; unrelated fields are inherited from the incoming state. -/
theorem downTransition_accepted_equation (p : Parameters) (i : Fin (p.m - 1))
    (row : CompleteRow p) (t : Fin p.T) (feedback : Observation p)
    (rate : RateInput p) (state : ReferencePrelaunchFollower.State p rate.eta)
    (hselected : downSelected p i row t)
    (hstatus : state.status = .unoccupied)
    (hregisters : registerInputDomain p rate state)
    (hbatch : decoderInputDomain p state.downBatch)
    (hbuffer : bufferInputDomain p state.buffer)
    (M : DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hparsed : parsedCurrentOutput p i row t feedback rate state = some M)
    (haccepted : acceptDown (ReferencePrelaunchFollower.codecParams p rate.eta)
      (ReferencePrelaunchFollower.acceptedStart state) (t.val + 1) M)
    (recovered : ReplayRegisters)
    (hchecked : checkedRecovery p rate M state
      (acceptedCutoffScan p rate M t
        (acceptedDownStartLE p rate M t state haccepted) row).endpoint = .ok recovered) :
    downTransition p i row t feedback rate state =
      let decoded := currentDecodeStep p i row t feedback rate state
      let scan := acceptedCutoffScan p rate M t
        (acceptedDownStartLE p rate M t state haccepted) row
      .accepted state
        { state with
          lastDown := some M
          S := recovered.registers.1
          delta := recovered.lastService
          backlog := recovered.registers.2
          status := if scan.endpoint = t.val + 2 then .pending else .unoccupied
          downBatch := decoded.1
          buffer := [] }
        decoded.2 M scan recovered.registers recovered.lastService := by
  have hparsed' : parseDown (ReferencePrelaunchFollower.codecParams p rate.eta)
      (((currentDecodeStep p i row t feedback rate state).2).map
        (wordEquivFlat (ReferencePrelaunchFollower.codecParams p rate.eta)).symm) = some M :=
    hparsed
  simp only [downTransition, dite_eq_left hselected, dite_eq_left hstatus,
    dite_eq_left hregisters, dite_eq_left hbatch, dite_eq_left hbuffer,
    hparsed', dite_eq_left haccepted, hchecked]

/-- A computed intermediate failure is returned with its FIRST offset/reason
and no next state. Later calendar rounds cannot install a drained terminal
queue. The decoder/parser/acceptance conditions are the actual branch tests. -/
theorem downTransition_recovery_failure_equation (p : Parameters) (i : Fin (p.m - 1))
    (row : CompleteRow p) (t : Fin p.T) (feedback : Observation p)
    (rate : RateInput p) (state : ReferencePrelaunchFollower.State p rate.eta)
    (hselected : downSelected p i row t)
    (hstatus : state.status = .unoccupied)
    (hregisters : registerInputDomain p rate state)
    (hbatch : decoderInputDomain p state.downBatch)
    (hbuffer : bufferInputDomain p state.buffer)
    (M : DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hparsed : parsedCurrentOutput p i row t feedback rate state = some M)
    (haccepted : acceptDown (ReferencePrelaunchFollower.codecParams p rate.eta)
      (ReferencePrelaunchFollower.acceptedStart state) (t.val + 1) M)
    (failure : ReplayFailure)
    (hchecked : checkedRecovery p rate M state
      (acceptedCutoffScan p rate M t
        (acceptedDownStartLE p rate M t state haccepted) row).endpoint = .error failure) :
    downTransition p i row t feedback rate state = .outputFailure state (.replay failure) := by
  have hparsed' : parseDown (ReferencePrelaunchFollower.codecParams p rate.eta)
      (((currentDecodeStep p i row t feedback rate state).2).map
        (wordEquivFlat (ReferencePrelaunchFollower.codecParams p rate.eta)).symm) = some M :=
    hparsed
  simp only [downTransition, dite_eq_left hselected, dite_eq_left hstatus,
    dite_eq_left hregisters, dite_eq_left hbatch, dite_eq_left hbuffer,
    hparsed', dite_eq_left haccepted, hchecked]

/-- Inversion of an ACTUAL accepted result: the reply is the actual parser
output, the returned values come from checked success, and the nonempty
interval is the bounded source scan. The exact installed state preserves the
unrelated initialization flag and advances the actual decoder batch. No
domain/success premise is added. -/
theorem downTransition_accepted_checked (p : Parameters) (i : Fin (p.m - 1))
    (row : CompleteRow p) (t : Fin p.T) (feedback : Observation p)
    (rate : RateInput p) (state after : ReferencePrelaunchFollower.State p rate.eta)
    (raw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)))
    (M : DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (scan : FollowerCutoffScan.ScanResult p.T) (registers : ℕ × ℕ) (lastService : ℕ)
    (h : downTransition p i row t feedback rate state =
      .accepted state after raw M scan registers lastService) :
    parsedCurrentOutput p i row t feedback rate state = some M ∧
      checkedRecovery p rate M state scan.endpoint = .ok ⟨registers, lastService⟩ ∧
      M.val.sigma < scan.endpoint ∧ scan.endpoint ≤ t.val + 2 ∧
      scan.endpoint ≤ p.T + 1 ∧
      raw = (currentDecodeStep p i row t feedback rate state).2 ∧
      after = { state with
        lastDown := some M
        S := registers.1
        delta := lastService
        backlog := registers.2
        status := if scan.endpoint = t.val + 2 then .pending else .unoccupied
        downBatch := (currentDecodeStep p i row t feedback rate state).1
        buffer := [] } := by
  unfold downTransition at h
  split at h
  next hselected =>
    split at h
    next hstatus =>
      split at h
      next hregisters =>
        split at h
        next hbatch =>
          split at h
          next hbuffer =>
            dsimp only at h
            split at h
            next hparsed => contradiction
            next reply hparsed =>
              split at h
              next haccepted =>
                have hb := acceptedCutoff_interval_bounds p rate reply t row state haccepted
                split at h
                next failure hfailed => contradiction
                next recovered hchecked =>
                  cases h
                  exact ⟨hparsed, hchecked, hb.1, hb.2.1, hb.2.2.1, rfl, rfl⟩
              next hnotaccepted => contradiction
          next hbuffer => contradiction
        next hbatch => contradiction
      next hregisters => contradiction
    next hstatus => contradiction
  next hselected => contradiction

/-- Every actually accepted output has the checked source bounds and exact
pure replay and final-service arithmetic. These facts follow from the
computed result, not from extra bounds supplied by a caller. -/
theorem downTransition_accepted_agreement (p : Parameters) (i : Fin (p.m - 1))
    (row : CompleteRow p) (t : Fin p.T) (feedback : Observation p)
    (rate : RateInput p) (state after : ReferencePrelaunchFollower.State p rate.eta)
    (raw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)))
    (M : DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (scan : FollowerCutoffScan.ScanResult p.T) (registers : ℕ × ℕ) (lastService : ℕ)
    (h : downTransition p i row t feedback rate state =
      .accepted state after raw M scan registers lastService) :
    registers.1 ≤ p.T * D p ∧ lastService ≤ D p ∧ registers.2 ≤ p.T * D p ∧
      registers = recoveredRegisters p rate M state scan.endpoint ∧
      ∃ hi : M.val.sigma < scan.endpoint,
        lastService = recoveredLastService p rate M state scan.endpoint hi := by
  obtain ⟨_, hc, hi, _⟩ := downTransition_accepted_checked
    p i row t feedback rate state after raw M scan registers lastService h
  obtain ⟨hb, heq, _⟩ := checkedRecovery_success p rate M state scan.endpoint _ hc
  exact ⟨hb.1, hb.2.1, hb.2.2, heq, hi,
    checkedRecovery_success_last_service p rate M state scan.endpoint hi _ hc⟩

/-- All calendar prefixes of an actually accepted operation satisfy the
source bounds, including initial and terminal queue and service fields. -/
theorem downTransition_accepted_prefix_bounds (p : Parameters) (i : Fin (p.m - 1))
    (row : CompleteRow p) (t : Fin p.T) (feedback : Observation p)
    (rate : RateInput p) (state after : ReferencePrelaunchFollower.State p rate.eta)
    (raw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)))
    (M : DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (scan : FollowerCutoffScan.ScanResult p.T) (registers : ℕ × ℕ) (lastService : ℕ)
    (h : downTransition p i row t feedback rate state =
      .accepted state after raw M scan registers lastService) (k : ℕ) :
    ∃ middle, checkedReplay (D p) (p.T * D p) (4 * rate.n) 0 ⟨(0, M.val.q), 0⟩
        ((recoveryQueueRecords p rate M state scan.endpoint).take k) = .ok middle ∧
      replay_register_domain (D p) (p.T * D p) middle ∧
      middle.registers = QueueReplay.replay (4 * rate.n) (0, M.val.q)
        ((recoveryQueueRecords p rate M state scan.endpoint).take k) := by
  have hc := (downTransition_accepted_checked
    p i row t feedback rate state after raw M scan registers lastService h).2.1
  exact checkedRecovery_success_prefix p rate M state scan.endpoint _ hc k

/-- The accepted cutoff result reads only the selected row's `prop` values at
the coordinates inspected by its first scan. -/
theorem acceptedCutoffScan_noninterference (p : Parameters) (rate : RateInput p)
    (M : DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (t : Fin p.T) (hstart : (downStart p rate M).val ≤ t.val)
    (row row' : CompleteRow p)
    (hprop : ∀ j ∈ (acceptedCutoffScan p rate M t hstart row).inspected,
      (CompletePublicTable.completeRowLearning p row j).1
          ContinuousControlSlice.Label.prop =
        (CompletePublicTable.completeRowLearning p row' j).1
          ContinuousControlSlice.Label.prop) :
    acceptedCutoffScan p rate M t hstart row =
      acceptedCutoffScan p rate M t hstart row' := by
  exact FollowerCutoffScan.completeRowCutoffScan_noninterference
    p rate.eta.val (downStart p rate M) t hstart row row' hprop

end Bandits.Support.ActiveFollowerDownAcceptance

end
