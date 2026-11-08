/-
Copyright (c) 2026 Bandits Lean preparation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.CappedService
public import Bandits.Support.QueueConservation
public import Bandits.Support.QueueReplay
public import Bandits.Support.ScoreWeights
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Semiring
public import Batteries.Data.List.Lemmas

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Finite recorded queue runs

This module gives a deterministic, finite execution of the integer queue
recurrence in `sources/zip4/manuscript/04_slow_fast_learner.tex:140-174` and
its first-overflow continuation in `:182-215`. The round inputs are explicit:
the enabled flag, recorded arm, reward vector, and positive rate vector. This
does not assert the protocol's conditional recording law or derive its schedule.
The local domain checks are supported by
`sources/zip4/manuscript/appendix_a_local_protocol.tex:26-48`.
-/

@[expose] public section

namespace Bandits.Support.RecordedQueueRun

variable {K : ℕ}

/-- Integer and real parameters for the quantized queue. -/
structure Parameters where
  D : ℕ
  n : ℕ
  eta : ℝ
  D_pos : 0 < D
  n_pos : 0 < n
  capacity_le_D : 4 * n ≤ D
  eta_pos : 0 < eta
  n_eq_eta_mul_D : (n : ℝ) = eta * (D : ℝ)

/-- One scheduled round and its explicit deterministic recording outcome. -/
structure RoundInput (K : ℕ) where
  enabled : Bool
  recordedArm : Option (Fin K)
  reward : Fin K → ℝ
  rate : Fin K → ℝ
  reward_nonneg : ∀ i, 0 ≤ reward i
  reward_le_one : ∀ i, reward i ≤ 1
  rate_pos : ∀ i, 0 < rate i

/-- One arm's score and integer backlog. -/
abbrev Registers := ℕ × ℕ

/-- A finite machine state. `records i` is the exact chronological input
history sent to `QueueReplay` for arm `i`; it has one entry per processed
round, including disabled and post-overflow no-op records. -/
structure RunState (K : ℕ) where
  registers : Fin K → Registers
  overflow : Bool
  records : Fin K → List (Bool × ℕ)

/-- The all-zero initial state. -/
def initialState (K : ℕ) : RunState K where
  registers := fun _ => (0, 0)
  overflow := false
  records := fun _ => []

/-- Quantized arrival before applying enabled/frozen control. -/
noncomputable def quantizedArrival (p : Parameters) (round : RoundInput K)
    (i : Fin K) : ℕ :=
  if round.recordedArm = some i then
    Nat.floor ((p.n : ℝ) * round.reward i / round.rate i)
  else 0

/-- The exact queue record accepted for one arm in one machine step. -/
noncomputable def acceptedRecord (p : Parameters) (state : RunState K)
    (round : RoundInput K) (i : Fin K) : Bool × ℕ :=
  if state.overflow then (false, 0)
  else if round.enabled then (true, quantizedArrival p round i)
  else (false, 0)

/-- Service represented by a queue record. Disabled records have zero service. -/
def recordService (capacity : ℕ) (registers : Registers)
    (record : Bool × ℕ) : ℕ :=
  if record.1 then CappedService.service capacity registers.2 record.2 else 0

/-- Apply one scheduled input. Every arm passes through `QueueReplay.transition`,
including zero-arrival enabled arms. The current update is retained before the
overflow flag is set. -/
noncomputable def step (p : Parameters) (state : RunState K)
    (round : RoundInput K) : RunState K := by
  classical
  let recs := fun i => acceptedRecord p state round i
  let registers := fun i =>
    QueueReplay.transition (4 * p.n) (state.registers i) (recs i)
  let overflow := state.overflow || decide (∃ i, 32 * (registers i).2 > p.D)
  exact ⟨registers, overflow, fun i => state.records i ++ [recs i]⟩

/-- Execute a genuinely finite chronological list of rounds. -/
noncomputable def execute (p : Parameters) : List (RoundInput K) → RunState K → RunState K
  | [], state => state
  | round :: rounds, state => execute p rounds (step p state round)

/-- Execute a finite list starting from zero score and backlog registers. -/
noncomputable def run (p : Parameters) (rounds : List (RoundInput K)) : RunState K :=
  execute p rounds (initialState K)

/-- Total arrival accepted by a queue history; false records are not arrivals. -/
def acceptedArrival (record : Bool × ℕ) : ℕ := if record.1 then record.2 else 0

/-- Sum of accepted arrivals in a finite queue history. -/
def acceptedTotal : List (Bool × ℕ) → ℕ
  | [] => 0
  | record :: records => acceptedArrival record + acceptedTotal records

/-- Appending a record adds its accepted arrival to the finite history total. -/
theorem acceptedTotal_append_one (records : List (Bool × ℕ))
    (record : Bool × ℕ) :
    acceptedTotal (records ++ [record]) = acceptedTotal records + acceptedArrival record := by
  induction records with
  | nil => simp [acceptedTotal]
  | cons head records ih => simp [acceptedTotal, ih, Nat.add_assoc]

/-- The score weight associated with an arm in a run state. -/
noncomputable def scoreWeight (p : Parameters) (state : RunState K)
    (i : Fin K) : ℝ :=
  ScoreWeights.scoreWeight (1 + 1 / (p.D : ℝ)) (state.registers i).1

/-- The Nat floor is at most `D` under the source reward and rate bounds. -/
theorem quantizedArrival_le_D (p : Parameters) (round : RoundInput K)
    (hfeasible : ∀ i, (p.n : ℝ) ≤ (p.D : ℝ) * round.rate i)
    (i : Fin K) : quantizedArrival p round i ≤ p.D := by
  unfold quantizedArrival
  split
  · have hnum : (p.n : ℝ) * round.reward i ≤ (p.n : ℝ) := by
      simpa using mul_le_mul_of_nonneg_left (round.reward_le_one i)
        (Nat.cast_nonneg p.n)
    have hratio : (p.n : ℝ) * round.reward i / round.rate i ≤ (p.D : ℝ) := by
      calc
        (p.n : ℝ) * round.reward i / round.rate i ≤
            (p.n : ℝ) / round.rate i :=
          div_le_div_of_nonneg_right hnum (round.rate_pos i).le
        _ ≤ (p.D : ℝ) := (div_le_iff₀ (round.rate_pos i)).2 (hfeasible i)
    exact Nat.floor_le_of_le hratio
  · exact Nat.zero_le _

/-- On the recorded arm, the arrival is exactly the manuscript's Nat floor. -/
theorem quantizedArrival_eq_floor (p : Parameters) (round : RoundInput K)
    (i : Fin K) (hrecorded : round.recordedArm = some i) :
    quantizedArrival p round i =
      Nat.floor ((p.n : ℝ) * round.reward i / round.rate i) := by
  simp [quantizedArrival, hrecorded]

/-- Every arm other than the recorded arm has zero nominal arrival. -/
theorem quantizedArrival_eq_zero (p : Parameters) (round : RoundInput K)
    (i : Fin K) (hnotRecorded : round.recordedArm ≠ some i) :
    quantizedArrival p round i = 0 := by
  simp [quantizedArrival, hnotRecorded]

/-- Every accepted arrival is at most the integer denominator. -/
theorem acceptedRecord_arrival_le_D (p : Parameters) (state : RunState K)
    (round : RoundInput K)
    (hfeasible : ∀ i, (p.n : ℝ) ≤ (p.D : ℝ) * round.rate i)
    (i : Fin K) : (acceptedRecord p state round i).2 ≤ p.D := by
  unfold acceptedRecord
  split
  · exact Nat.zero_le _
  · split
    · exact quantizedArrival_le_D p round hfeasible i
    · exact Nat.zero_le _

/-- Every record's service is bounded by the queue capacity. -/
theorem recordService_le_capacity (p : Parameters) (registers : Registers)
    (record : Bool × ℕ) : recordService (4 * p.n) registers record ≤ 4 * p.n := by
  unfold recordService
  split
  · exact CappedService.service_le_capacity _ _ _
  · exact Nat.zero_le _

/-- Service never exceeds the current backlog plus the accepted arrival. -/
theorem recordService_le_total (capacity : ℕ) (registers : Registers)
    (record : Bool × ℕ) :
    recordService capacity registers record ≤ registers.2 + acceptedArrival record := by
  cases record with
  | mk enabled arrival =>
    cases enabled
    · simp [recordService, acceptedArrival]
    · exact CappedService.service_le_total capacity registers.2 arrival

/-- The first overflow test is exactly the post-transition integer cutoff. -/
theorem step_overflow_if_cutoff (p : Parameters) (state : RunState K)
    (round : RoundInput K) (i : Fin K)
    (hcutoff : 32 * ((step p state round).registers i).2 > p.D) :
    (step p state round).overflow = true := by
  have hcutoff' : ∃ j, 32 * (QueueReplay.transition (4 * p.n)
      (state.registers j) (acceptedRecord p state round j)).2 > p.D :=
    ⟨i, by simpa [step] using hcutoff⟩
  change state.overflow || decide (∃ j,
    32 * (QueueReplay.transition (4 * p.n) (state.registers j)
      (acceptedRecord p state round j)).2 > p.D) = true
  simp [hcutoff']

/-- All services actually emitted by a machine step obey the capacity bound. -/
theorem step_service_le_capacity (p : Parameters) (state : RunState K)
    (round : RoundInput K) (i : Fin K) :
    recordService (4 * p.n) (state.registers i)
      (acceptedRecord p state round i) ≤ 4 * p.n :=
  recordService_le_capacity p (state.registers i) (acceptedRecord p state round i)

/-- The parameter condition `4*n ≤ D` also bounds every served increment by D. -/
theorem step_service_le_D (p : Parameters) (state : RunState K)
    (round : RoundInput K) (i : Fin K) :
    recordService (4 * p.n) (state.registers i)
      (acceptedRecord p state round i) ≤ p.D :=
  (step_service_le_capacity p state round i).trans p.capacity_le_D

/-- The score coordinate of a transition is the old score plus its service. -/
theorem transition_score_eq_add_recordService (capacity : ℕ)
    (registers : Registers) (record : Bool × ℕ) :
    (QueueReplay.transition capacity registers record).1 =
      registers.1 + recordService capacity registers record := by
  cases record with
  | mk enabled arrival =>
    cases enabled <;> simp [QueueReplay.transition, recordService,
      CappedService.service]

/-- The queue coordinates conserve the old total plus the accepted arrival. -/
theorem transition_total (capacity : ℕ) (registers : Registers)
    (record : Bool × ℕ) :
    let next := QueueReplay.transition capacity registers record
    next.1 + next.2 = registers.1 + registers.2 + acceptedArrival record := by
  cases record with
  | mk enabled arrival =>
    cases enabled
    · simp [QueueReplay.transition, acceptedArrival]
    · have h := CappedService.residual_add_service capacity registers.2 arrival
      dsimp [QueueReplay.transition, acceptedArrival,
        CappedService.service, CappedService.residual] at h ⊢
      omega

/-- Exact conservation for any finite replay, proved from its transitions. -/
theorem replay_total (capacity : ℕ) (registers : Registers)
    (records : List (Bool × ℕ)) :
    let final := QueueReplay.replay capacity registers records
    final.1 + final.2 = registers.1 + registers.2 + acceptedTotal records := by
  induction records generalizing registers with
  | nil => simp [QueueReplay.replay, acceptedTotal]
  | cons record records ih =>
    change (QueueReplay.replay capacity registers (record :: records)).1 +
        (QueueReplay.replay capacity registers (record :: records)).2 = _
    rw [show record :: records = [record] ++ records by rfl,
      QueueReplay.replay_append capacity registers [record] records]
    rw [show QueueReplay.replay capacity registers [record] =
        QueueReplay.transition capacity registers record by rfl]
    rw [ih (QueueReplay.transition capacity registers record)]
    rw [show acceptedTotal ([record] ++ records) =
        acceptedArrival record + acceptedTotal records by rfl]
    have hfirst :
        (QueueReplay.transition capacity registers record).1 +
            (QueueReplay.transition capacity registers record).2 =
          registers.1 + registers.2 + acceptedArrival record := by
      simpa using transition_total capacity registers record
    omega

/-- Backlog recurrence for one checked replay transition. -/
private theorem transition_backlog_eq (capacity : ℕ) (registers : Registers)
    (record : Bool × ℕ) :
    (QueueReplay.transition capacity registers record).2 =
      registers.2 + acceptedArrival record - recordService capacity registers record := by
  cases record with
  | mk enabled arrival =>
    cases enabled <;> simp [QueueReplay.transition, acceptedArrival,
      recordService, CappedService.service]

/-- State after the first `t` records of a finite history. This is a prefix
map used only to apply the Nat-indexed conservation API to a finite list. For
indices beyond its length, `take` returns that same finite history; no extra
round or default record is added to the run. -/
private def finitePrefixState (capacity : ℕ) (initial : Registers)
    (records : List (Bool × ℕ)) (t : ℕ) : Registers :=
  QueueReplay.replay capacity initial (records.take t)

/-- Accepted arrivals in a finite prefix. -/
private def finitePrefixAccepted (records : List (Bool × ℕ)) (t : ℕ) : ℕ :=
  acceptedTotal (records.take t)

/-- Increment between two consecutive finite-prefix arrival totals. -/
private def finitePrefixArrival (records : List (Bool × ℕ)) (t : ℕ) : ℕ :=
  finitePrefixAccepted records (t + 1) - finitePrefixAccepted records t

/-- Score increment between two consecutive finite-prefix states. -/
private def finitePrefixService (capacity : ℕ) (initial : Registers)
    (records : List (Bool × ℕ)) (t : ℕ) : ℕ :=
  (finitePrefixState capacity initial records (t + 1)).1 -
    (finitePrefixState capacity initial records t).1

private theorem finitePrefix_state_succ_of_lt (capacity : ℕ) (initial : Registers)
    (records : List (Bool × ℕ)) (t : ℕ) (hlt : t < records.length) :
    finitePrefixState capacity initial records (t + 1) =
      QueueReplay.transition capacity (finitePrefixState capacity initial records t)
        records[t] := by
  unfold finitePrefixState
  rw [← List.take_append_getElem hlt, QueueReplay.replay_append]
  rfl

private theorem finitePrefix_state_succ_of_length_le (capacity : ℕ)
    (initial : Registers) (records : List (Bool × ℕ)) (t : ℕ)
    (hle : records.length ≤ t) :
    finitePrefixState capacity initial records (t + 1) =
      finitePrefixState capacity initial records t := by
  unfold finitePrefixState
  rw [List.take_of_length_le hle,
    List.take_of_length_le (Nat.le_trans hle (Nat.le_succ t))]

private theorem finitePrefix_arrival_of_lt (records : List (Bool × ℕ))
    (t : ℕ) (hlt : t < records.length) :
    finitePrefixArrival records t = acceptedArrival records[t] := by
  unfold finitePrefixArrival finitePrefixAccepted
  rw [← List.take_append_getElem hlt, acceptedTotal_append_one]
  simp

private theorem finitePrefix_arrival_of_length_le (records : List (Bool × ℕ))
    (t : ℕ) (hle : records.length ≤ t) : finitePrefixArrival records t = 0 := by
  unfold finitePrefixArrival finitePrefixAccepted
  rw [List.take_of_length_le hle,
    List.take_of_length_le (Nat.le_trans hle (Nat.le_succ t))]
  omega

private theorem finitePrefix_service_of_lt (capacity : ℕ) (initial : Registers)
    (records : List (Bool × ℕ)) (t : ℕ) (hlt : t < records.length) :
    finitePrefixService capacity initial records t =
      recordService capacity (finitePrefixState capacity initial records t) records[t] := by
  unfold finitePrefixService
  rw [finitePrefix_state_succ_of_lt capacity initial records t hlt,
    transition_score_eq_add_recordService]
  simp

private theorem finitePrefix_service_of_length_le (capacity : ℕ)
    (initial : Registers) (records : List (Bool × ℕ)) (t : ℕ)
    (hle : records.length ≤ t) :
    finitePrefixService capacity initial records t = 0 := by
  unfold finitePrefixService
  rw [finitePrefix_state_succ_of_length_le capacity initial records t hle]
  simp

private theorem finitePrefix_score_recurrence (capacity : ℕ) (initial : Registers)
    (records : List (Bool × ℕ)) (t : ℕ) :
    (finitePrefixState capacity initial records t).1 +
        finitePrefixService capacity initial records t =
      (finitePrefixState capacity initial records (t + 1)).1 := by
  by_cases hlt : t < records.length
  · rw [finitePrefix_service_of_lt capacity initial records t hlt,
      finitePrefix_state_succ_of_lt capacity initial records t hlt,
      transition_score_eq_add_recordService]
  · have hle : records.length ≤ t := Nat.le_of_not_gt hlt
    rw [finitePrefix_service_of_length_le capacity initial records t hle,
      finitePrefix_state_succ_of_length_le capacity initial records t hle]
    omega

private theorem finitePrefix_backlog_recurrence (capacity : ℕ)
    (initial : Registers) (records : List (Bool × ℕ)) (t : ℕ) :
    (finitePrefixState capacity initial records (t + 1)).2 =
      (finitePrefixState capacity initial records t).2 +
        finitePrefixArrival records t - finitePrefixService capacity initial records t := by
  by_cases hlt : t < records.length
  · rw [finitePrefix_state_succ_of_lt capacity initial records t hlt,
      finitePrefix_arrival_of_lt records t hlt,
      finitePrefix_service_of_lt capacity initial records t hlt]
    exact transition_backlog_eq capacity
      (finitePrefixState capacity initial records t) records[t]
  · have hle : records.length ≤ t := Nat.le_of_not_gt hlt
    rw [finitePrefix_state_succ_of_length_le capacity initial records t hle,
      finitePrefix_arrival_of_length_le records t hle,
      finitePrefix_service_of_length_le capacity initial records t hle]
    simp

private theorem finitePrefix_accepted_succ (records : List (Bool × ℕ)) (t : ℕ) :
    finitePrefixAccepted records (t + 1) =
      finitePrefixAccepted records t + finitePrefixArrival records t := by
  by_cases hlt : t < records.length
  · unfold finitePrefixAccepted
    rw [← List.take_append_getElem hlt, acceptedTotal_append_one,
      finitePrefix_arrival_of_lt records t hlt]
  · have hle : records.length ≤ t := Nat.le_of_not_gt hlt
    have hle' : records.length ≤ t + 1 := by omega
    change acceptedTotal (records.take (t + 1)) =
      acceptedTotal (records.take t) +
        (acceptedTotal (records.take (t + 1)) - acceptedTotal (records.take t))
    rw [List.take_of_length_le hle', List.take_of_length_le hle]
    simp

private theorem finitePrefix_sum_arrivals (records : List (Bool × ℕ)) (n : ℕ) :
    (∑ t ∈ Finset.range n, finitePrefixArrival records t) =
      finitePrefixAccepted records n := by
  induction n with
  | zero => simp [finitePrefixAccepted, acceptedTotal]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, finitePrefix_accepted_succ]

/-- Finite replay conservation obtained from the checked Nat-indexed queue
conservation theorem, using only its finite-list prefix states. -/
private theorem replay_total_via_queueConservation (capacity : ℕ)
    (initial : Registers) (records : List (Bool × ℕ)) :
    let final := QueueReplay.replay capacity initial records
    final.1 + final.2 = initial.1 + initial.2 + acceptedTotal records := by
  let score := fun t => (finitePrefixState capacity initial records t).1
  let backlog := fun t => (finitePrefixState capacity initial records t).2
  let arrivals := finitePrefixArrival records
  let service := finitePrefixService capacity initial records
  have hservice : ∀ t, service t ≤ backlog t + arrivals t := by
    intro t
    change finitePrefixService capacity initial records t ≤
      (finitePrefixState capacity initial records t).2 + finitePrefixArrival records t
    by_cases hlt : t < records.length
    · rw [finitePrefix_service_of_lt capacity initial records t hlt,
        finitePrefix_arrival_of_lt records t hlt]
      exact recordService_le_total capacity
        (finitePrefixState capacity initial records t) records[t]
    · have hle : records.length ≤ t := Nat.le_of_not_gt hlt
      rw [finitePrefix_service_of_length_le capacity initial records t hle,
        finitePrefix_arrival_of_length_le records t hle]
      exact Nat.zero_le _
  have hbacklog : ∀ t, backlog (t + 1) = backlog t + arrivals t - service t := by
    intro t
    exact finitePrefix_backlog_recurrence capacity initial records t
  have hscore : ∀ t, score (t + 1) = score t + service t := by
    intro t
    have hrec := finitePrefix_score_recurrence capacity initial records t
    dsimp [score, service] at hrec ⊢
    omega
  have hconservation := QueueConservation.score_add_backlog_eq_initial_total_add_sum_arrivals
    score backlog arrivals service hservice hbacklog hscore records.length
  have hstart : finitePrefixState capacity initial records 0 = initial := by
    simp [finitePrefixState, QueueReplay.replay]
  have hfinish : finitePrefixState capacity initial records records.length =
      QueueReplay.replay capacity initial records := by
    simp [finitePrefixState, List.take_of_length_le]
  have hsum :
      (∑ t ∈ Finset.range records.length, finitePrefixArrival records t) =
        acceptedTotal records := by
    rw [finitePrefix_sum_arrivals]
    simp [finitePrefixAccepted, List.take_of_length_le]
  dsimp [score, backlog, arrivals, service] at hconservation
  rw [hstart, hfinish, hsum] at hconservation
  simpa using hconservation

/-- One machine step extends each per-arm replay history by exactly the record
used in `QueueReplay.transition`. -/
theorem step_replay_projection (p : Parameters) (state : RunState K)
    (round : RoundInput K)
    (hprojection : ∀ i, state.registers i =
      QueueReplay.replay (4 * p.n) (0, 0) (state.records i)) :
    ∀ i, (step p state round).registers i =
      QueueReplay.replay (4 * p.n) (0, 0) ((step p state round).records i) := by
  intro i
  change QueueReplay.transition (4 * p.n) (state.registers i)
      (acceptedRecord p state round i) =
    QueueReplay.replay (4 * p.n) (0, 0)
      (state.records i ++ [acceptedRecord p state round i])
  rw [QueueReplay.replay_append, hprojection i]
  rfl

/-- Replay characterization for every finite execution prefix. -/
theorem execute_replay_projection (p : Parameters) (rounds : List (RoundInput K))
    (state : RunState K)
    (hprojection : ∀ i, state.registers i =
      QueueReplay.replay (4 * p.n) (0, 0) (state.records i)) :
    ∀ i, (execute p rounds state).registers i =
      QueueReplay.replay (4 * p.n) (0, 0) ((execute p rounds state).records i) := by
  induction rounds generalizing state with
  | nil => simpa [execute] using hprojection
  | cons round rounds ih =>
    simp only [execute]
    exact ih (step p state round) (step_replay_projection p state round hprojection)

/-- The constructed run is exactly replay of its finite accepted records. -/
theorem run_replay_projection (p : Parameters) (rounds : List (RoundInput K))
    (i : Fin K) :
    (run p rounds).registers i =
      QueueReplay.replay (4 * p.n) (0, 0) ((run p rounds).records i) := by
  exact execute_replay_projection p rounds (initialState K)
    (by intro i; rfl) i

/-- Exact score-plus-backlog conservation for the constructed finite run. -/
theorem run_score_add_backlog_eq_accepted (p : Parameters)
    (rounds : List (RoundInput K)) (i : Fin K) :
    ((run p rounds).registers i).1 + ((run p rounds).registers i).2 =
      acceptedTotal ((run p rounds).records i) := by
  rw [run_replay_projection]
  simpa using replay_total_via_queueConservation (4 * p.n) (0, 0)
    ((run p rounds).records i)

/-- Total arrivals in one emitted record obey the per-round denominator bound. -/
theorem step_acceptedArrival_le_D (p : Parameters) (state : RunState K)
    (round : RoundInput K)
    (hfeasible : ∀ i, (p.n : ℝ) ≤ (p.D : ℝ) * round.rate i)
    (i : Fin K) : acceptedArrival (acceptedRecord p state round i) ≤ p.D := by
  by_cases hrecord : (acceptedRecord p state round i).1
  · simp only [acceptedArrival, hrecord]
    exact acceptedRecord_arrival_le_D p state round hfeasible i
  · simp [acceptedArrival, hrecord]

/-- A list of executed rounds contributes at most `D` accepted units per round. -/
theorem execute_acceptedTotal_le (p : Parameters) (rounds : List (RoundInput K))
    (state : RunState K)
    (hfeasible : ∀ round ∈ rounds, ∀ i, (p.n : ℝ) ≤ (p.D : ℝ) * round.rate i) :
    ∀ i, acceptedTotal ((execute p rounds state).records i) ≤
      acceptedTotal (state.records i) + rounds.length * p.D := by
  induction rounds generalizing state with
  | nil =>
    intro i
    simp [execute]
  | cons round rounds ih =>
    intro i
    have hfirst := step_acceptedArrival_le_D p state round (hfeasible round (by simp) ) i
    have htail : ∀ next ∈ rounds, ∀ j, (p.n : ℝ) ≤ (p.D : ℝ) * next.rate j := by
      intro next hnext j
      exact hfeasible next (by simp [hnext]) j
    have hrest := ih (step p state round) htail i
    have happend : acceptedTotal ((step p state round).records i) ≤
        acceptedTotal (state.records i) + p.D := by
      rw [step, acceptedTotal_append_one]
      exact Nat.add_le_add_left hfirst _
    simp only [execute, List.length_cons]
    calc
      acceptedTotal ((execute p rounds (step p state round)).records i) ≤
          acceptedTotal ((step p state round).records i) + rounds.length * p.D := hrest
      _ ≤ (acceptedTotal (state.records i) + p.D) + rounds.length * p.D :=
        Nat.add_le_add_right happend _
      _ = acceptedTotal (state.records i) + (rounds.length + 1) * p.D := by
        rw [Nat.add_mul]
        simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Exact conservation and the finite-horizon prefix bound. -/
theorem run_score_add_backlog_le_prefixLength_mul_D (p : Parameters)
    (rounds : List (RoundInput K))
    (hfeasible : ∀ round ∈ rounds, ∀ i,
      (p.n : ℝ) ≤ (p.D : ℝ) * round.rate i)
    (i : Fin K) :
    ((run p rounds).registers i).1 + ((run p rounds).registers i).2 ≤
      rounds.length * p.D := by
  rw [run_score_add_backlog_eq_accepted]
  have h := execute_acceptedTotal_le p rounds (initialState K) hfeasible i
  simpa [run, initialState, acceptedTotal] using h

/-- Prefix form of the finite-horizon score-plus-backlog bound. -/
theorem run_prefix_score_add_backlog_le (p : Parameters)
    (rounds : List (RoundInput K)) (prefixLength : ℕ)
    (hfeasible : ∀ round ∈ rounds.take prefixLength, ∀ i,
      (p.n : ℝ) ≤ (p.D : ℝ) * round.rate i)
    (i : Fin K) :
    ((run p (rounds.take prefixLength)).registers i).1 +
        ((run p (rounds.take prefixLength)).registers i).2 ≤
      (rounds.take prefixLength).length * p.D :=
  run_score_add_backlog_le_prefixLength_mul_D p (rounds.take prefixLength)
    hfeasible i

/-- Disabled rounds preserve all score and backlog registers and accept no arrival. -/
theorem step_disabled_preserves (p : Parameters) (state : RunState K)
    (round : RoundInput K) (henabled : round.enabled = false) (i : Fin K) :
    (step p state round).registers i = state.registers i ∧
      acceptedArrival (acceptedRecord p state round i) = 0 := by
  constructor
  · change QueueReplay.transition (4 * p.n) (state.registers i)
      (acceptedRecord p state round i) = state.registers i
    simp [acceptedRecord, henabled, QueueReplay.transition]
  · simp [acceptedArrival, acceptedRecord, henabled]

/-- A post-overflow step emits a no-op record and preserves every register. -/
theorem step_after_overflow_preserves (p : Parameters) (state : RunState K)
    (round : RoundInput K) (hoverflow : state.overflow = true) (i : Fin K) :
    (step p state round).registers i = state.registers i ∧
      acceptedRecord p state round i = (false, 0) := by
  constructor
  · change QueueReplay.transition (4 * p.n) (state.registers i)
      (acceptedRecord p state round i) = state.registers i
    simp [acceptedRecord, hoverflow, QueueReplay.transition]
  · simp [acceptedRecord, hoverflow]

/-- One step sets the overflow flag exactly when a post-transition backlog
crosses the integer cutoff, assuming the incoming flag matches its registers. -/
theorem step_overflow_iff_cutoff (p : Parameters) (state : RunState K)
    (round : RoundInput K)
    (hstate : state.overflow = true ↔ ∃ i, 32 * (state.registers i).2 > p.D) :
    (step p state round).overflow = true ↔
      ∃ i, 32 * ((step p state round).registers i).2 > p.D := by
  cases hflag : state.overflow
  · simp [step, hflag]
  · have hbefore := hstate.mp hflag
    constructor
    · intro _
      obtain ⟨i, hi⟩ := hbefore
      refine ⟨i, ?_⟩
      rw [(step_after_overflow_preserves p state round hflag i).1]
      exact hi
    · intro _
      simp [step, hflag]

/-- The overflow invariant is preserved over every finite list execution. -/
theorem execute_overflow_iff_cutoff (p : Parameters) (rounds : List (RoundInput K))
    (state : RunState K)
    (hstate : state.overflow = true ↔ ∃ i, 32 * (state.registers i).2 > p.D) :
    (execute p rounds state).overflow = true ↔
      ∃ i, 32 * ((execute p rounds state).registers i).2 > p.D := by
  induction rounds generalizing state with
  | nil => simpa [execute] using hstate
  | cons round rounds ih =>
    simp only [execute]
    exact ih (step p state round) (step_overflow_iff_cutoff p state round hstate)

/-- Every constructed run's absorbing flag records whether a post-update
backlog crossed the exact integer cutoff. -/
theorem run_overflow_iff_cutoff (p : Parameters) (rounds : List (RoundInput K)) :
    (run p rounds).overflow = true ↔
      ∃ i, 32 * ((run p rounds).registers i).2 > p.D := by
  exact execute_overflow_iff_cutoff p rounds (initialState K) (by
    simp [initialState])

/-- Any finite suffix after an overflow leaves every score and backlog fixed. -/
theorem execute_after_overflow_preserves (p : Parameters)
    (rounds : List (RoundInput K)) (state : RunState K)
    (hoverflow : state.overflow = true) :
    (execute p rounds state).overflow = true ∧
      ∀ i, (execute p rounds state).registers i = state.registers i := by
  induction rounds generalizing state with
  | nil =>
    constructor
    · exact hoverflow
    · intro i
      rfl
  | cons round rounds ih =>
    have hstep : (step p state round).overflow = true := by
      simp [step, hoverflow]
    have htail := ih (step p state round) hstep
    constructor
    · exact htail.1
    · intro i
      calc
        (execute p rounds (step p state round)).registers i =
            (step p state round).registers i := htail.2 i
        _ = state.registers i := (step_after_overflow_preserves p state round
          hoverflow i).1

/-- The update that first crosses the integer cutoff is retained in full. -/
theorem step_retains_first_overflow_update (p : Parameters) (state : RunState K)
    (round : RoundInput K) (hnotOverflow : state.overflow = false)
    (hcross : (step p state round).overflow = true) :
    (∃ i, 32 * ((step p state round).registers i).2 > p.D) ∧
      ∀ i, (step p state round).registers i = QueueReplay.transition (4 * p.n)
        (state.registers i) (acceptedRecord p state round i) := by
  constructor
  · simpa [step, hnotOverflow] using hcross
  · intro i
    rfl

/-- The public source cutoff `b > 1/(32 eta)` is exactly the integer test
`32 * backlog > D` when `n = eta * D` and both parameters are positive. -/
theorem overflowCutoff_iff (p : Parameters) (backlog : ℕ) :
    (backlog : ℝ) / (p.n : ℝ) > 1 / (32 * p.eta) ↔
      32 * backlog > p.D := by
  have hn : 0 < (p.n : ℝ) := Nat.cast_pos.mpr p.n_pos
  have hcancel : (1 / (32 * p.eta)) * (p.n : ℝ) = (p.D : ℝ) / 32 := by
    rw [p.n_eq_eta_mul_D]
    field_simp [ne_of_gt p.eta_pos]
  constructor
  · intro h
    have h' : 1 / (32 * p.eta) < (backlog : ℝ) / (p.n : ℝ) := h
    have h'' := (lt_div_iff₀ hn).1 h'
    rw [hcancel] at h''
    exact_mod_cast (by nlinarith : (p.D : ℝ) < 32 * (backlog : ℝ))
  · intro h
    have h' : (p.D : ℝ) / 32 < (backlog : ℝ) := by
      have hcast : (p.D : ℝ) < 32 * (backlog : ℝ) := by
        exact_mod_cast h
      nlinarith
    have h'' : (1 / (32 * p.eta)) * (p.n : ℝ) < (backlog : ℝ) := by
      rw [hcancel]
      exact h'
    exact (lt_div_iff₀ hn).2 h''

/-- The weight ratio after one constructed transition is exactly the source
base raised to the served integer increment. -/
theorem step_scoreWeight_ratio (p : Parameters) (state : RunState K)
    (round : RoundInput K) (i : Fin K) :
    scoreWeight p (step p state round) i / scoreWeight p state i =
      (1 + 1 / (p.D : ℝ)) ^
        recordService (4 * p.n) (state.registers i)
          (acceptedRecord p state round i) := by
  change ScoreWeights.scoreWeight (1 + 1 / (p.D : ℝ))
      (QueueReplay.transition (4 * p.n) (state.registers i)
        (acceptedRecord p state round i)).1 /
      ScoreWeights.scoreWeight (1 + 1 / (p.D : ℝ)) (state.registers i).1 = _
  rw [transition_score_eq_add_recordService]
  exact ScoreWeights.scoreWeight_update_ratio
    (ScoreWeights.sourceBase_pos (Nat.cast_pos.mpr p.D_pos)) _ _

end Bandits.Support.RecordedQueueRun

end
