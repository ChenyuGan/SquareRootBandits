/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.CanonicalRecordingRates
public import Bandits.Support.ConstructorDimensions
public import Bandits.Support.OrdinaryMessageCodec
public import Bandits.Support.QueueReplay

import Mathlib.Data.Finset.Basic
import Lean.Elab.Tactic.Omega

/-!
# Coordinator collection queue ledger

The local storage and operation order are transcribed from
`sources/zip4/manuscript/06_interruptions.tex:16-28,41-69,80-100,257-285`
and `sources/zip4/manuscript/appendix_a_local_protocol.tex:8-14,46-64`.
This module contains only the collection queue/score substate. It does not
construct a coordinator run, decoder, physical history, or probability law.
Initial cutoff registers, assignment, base scores, recorder outputs, enable
flags, and parsed UP records are explicit local inputs.
-/

@[expose] public section

namespace Bandits.Support.CoordinatorCollectionLedger

open Bandits.Support.ConstructorDimensions
open Bandits.Support.OrdinaryMessageCodec

variable {p : ConstructorDimensions.Parameters}

/-- The source stability cap on the learning rate. -/
def sourceLearningCap (p : ConstructorDimensions.Parameters) (eta : ℝ) : Prop :=
  eta ≤ 1 / (1024 * (p.m : ℝ) * p.K *
    (Bandits.Support.CanonicalRecordingRates.L_stab p : ℝ))

/-- The codec domain induced by the source constructor dimensions and rate. -/
noncomputable def codecParams (p : ConstructorDimensions.Parameters) (eta : ℝ) :
    OrdinaryMessageCodec.CodecParams where
  m := p.m
  K := p.K
  T := p.T
  D := ConstructorDimensions.D p
  bN := ConstructorDimensions.b_N p
  beta := Bandits.Support.CanonicalRecordingRates.beta p eta
  hT := ConstructorDimensions.T_pos p
  hD := ConstructorDimensions.D_pos p
  hKD := ConstructorDimensions.K_le_D p
  hbN := ConstructorDimensions.b_N_le_D p

/-- Follower labels `0,...,m-2` and their current slow-arm assignment. -/
structure Assignment (p : ConstructorDimensions.Parameters) where
  arm : Fin (p.m - 1) → Fin p.K
  injective : Function.Injective arm

/-- A known cutoff register contains the score, queue, and prior service. -/
structure CutoffRegister where
  score : ℕ
  queue : ℕ
  lastService : ℕ
  deriving DecidableEq, Repr

/-- The working current queue and its most recent calendar-round service. -/
structure CurrentRegister where
  queue : ℕ
  lastService : ℕ
  deriving DecidableEq, Repr

/-- One stamped positive raw arrival. The ledger stores arrivals in a finite
arm-by-round partial map, so each arm/round key occurs at most once. -/
structure RawArrival (K T : ℕ) where
  arm : Fin K
  round : Fin T
  amount : ℕ
  positive : 0 < amount

/-- The within-round phase of the collection substate. -/
inductive Phase where
  | ready
  | started
  | decoded
  deriving DecidableEq, Repr

/-- A checked result distinguishes local domain failure from a parser or
acceptance rejection. A rejection carries the logical registers unchanged. -/
inductive Checked (α : Type*) where
  | success (value : α)
  | rejected (value : α)
  | invalid

/-- The local collection ledger. `none` is genuine unknown queue/cutoff-score
information. Per-follower base scores remain available while those entries are
unknown. `increment` is the partial collection service sum. `rawBuffer` stores
only positive arrivals for currently unknown queues. `enabledHistory` records
the supplied calendar enable bit once per started round. -/
structure Ledger (p : ConstructorDimensions.Parameters) (eta : ℝ)
    (heta : 0 < eta) (hcap : sourceLearningCap p eta) (n : ℕ)
    (hn : (n : ℝ) = eta * (ConstructorDimensions.D p : ℝ)) where
  assignment : Assignment p
  sigma : ℕ
  cutoff : ℕ
  freezeAt : ℕ
  baseScore : Fin (p.m - 1) → ℕ
  pending : Finset (Fin (p.m - 1))
  cutoffRegisters : Fin p.K → Option CutoffRegister
  currentRegisters : Fin p.K → Option CurrentRegister
  increment : Fin p.K → ℕ
  gammaLoc : Fin p.K → ℕ
  rawBuffer : Fin p.K → Fin p.T → Option ℕ
  enabledHistory : Fin p.T → Option Bool
  cursor : ℕ
  phase : Phase

variable {eta : ℝ} {heta : 0 < eta} {hcap : sourceLearningCap p eta}
  {n : ℕ} {hn : (n : ℝ) = eta * (ConstructorDimensions.D p : ℝ)}

/-- The pending natural labels passed to the literal codec acceptance test. -/
def pendingNaturalLabels (l : Ledger p eta heta hcap n hn) : Set ℕ :=
  ↑(l.pending.image fun i : Fin (p.m - 1) => i.val)

theorem pendingNaturalLabels_mem_iff (l : Ledger p eta heta hcap n hn)
    (i : Fin (p.m - 1)) :
    i.val ∈ pendingNaturalLabels l ↔ i ∈ l.pending := by
  change i.val ∈ l.pending.image (fun j : Fin (p.m - 1) => j.val) ↔
    i ∈ l.pending
  rw [Finset.mem_image]
  constructor
  · rintro ⟨j, hj, hval⟩
    have hji : j = i := Fin.ext hval
    subst j
    exact hj
  · intro hi
    exact ⟨i, hi, rfl⟩

/-- Executable form of the codec's UP acceptance test on this ledger. -/
def acceptUpCheck (l : Ledger p eta heta hcap n hn)
    (i : Fin (p.m - 1)) (M : OrdinaryMessageCodec.UpRecord (codecParams p eta)) :
    Bool :=
  decide (l.cutoff ≤ l.cursor) &&
    (decide (i ∈ l.pending) && decide (M.val.sigma = l.sigma))

/-- The executable UP test is exactly `OrdinaryMessageCodec.acceptUp` with the
current assignment, cutoff, and pending set. -/
theorem acceptUpCheck_iff (l : Ledger p eta heta hcap n hn)
    (i : Fin (p.m - 1)) (M : OrdinaryMessageCodec.UpRecord (codecParams p eta)) :
    acceptUpCheck l i M = true ↔
      OrdinaryMessageCodec.acceptUp (codecParams p eta) l.cutoff l.cursor i.val
        (pendingNaturalLabels l) l.sigma M := by
  simp [acceptUpCheck, OrdinaryMessageCodec.acceptUp,
    pendingNaturalLabels_mem_iff]

/-- An arm is still unknown exactly when it belongs to a pending follower. -/
def armPending (l : Ledger p eta heta hcap n hn) (a : Fin p.K) : Prop :=
  ∃ i : Fin (p.m - 1), i ∈ l.pending ∧ l.assignment.arm i = a

/-- The source round label represented by a zero-based finite calendar index. -/
def sourceRound {T : ℕ} (r : Fin T) : ℕ := r.val + 1

/-- The raw-buffer observation at one arm and round; absence is source zero. -/
def bufferedArrival (l : Ledger p eta heta hcap n hn)
    (a : Fin p.K) (r : Fin p.T) : ℕ :=
  (l.rawBuffer a r).getD 0

/-! ## Executable domain checks -/

/-- A finite executable universal check over an existing `Fin` carrier. -/
def allFin (length : ℕ) (test : Fin length → Bool) : Bool :=
  (List.ofFn test).all id

/-- A finite executable existential check over an existing `Fin` carrier. -/
def anyFin (length : ℕ) (test : Fin length → Bool) : Bool :=
  (List.ofFn test).any id

/-- Executable pending-arm membership, computed from the finite follower set. -/
def armPendingCheck (l : Ledger p eta heta hcap n hn) (a : Fin p.K) : Bool :=
  anyFin (p.m - 1) fun i =>
    decide (i ∈ l.pending) && decide (l.assignment.arm i = a)

/-- Executable domain checks for every positive stamped raw arrival. -/
def rawEntryDomainsCheck (l : Ledger p eta heta hcap n hn) : Bool :=
  allFin p.K fun a => allFin p.T fun r =>
    match l.rawBuffer a r with
    | none => true
    | some amount => decide (0 < amount) &&
        decide (amount ≤ ConstructorDimensions.D p) &&
        decide (l.cutoff ≤ sourceRound r) &&
        decide (sourceRound r < l.freezeAt) &&
        (if l.phase = .ready then decide (sourceRound r < l.cursor)
          else decide (sourceRound r ≤ l.cursor)) && armPendingCheck l a

/-- Executable checks for all known current and cutoff registers, base scores,
partial accumulators, and pre-decode services. -/
def registerDomainsCheck (l : Ledger p eta heta hcap n hn) : Bool :=
  allFin p.K (fun a : Fin p.K =>
    match l.currentRegisters a with
    | none => true
    | some r => decide (r.queue ≤ p.T * ConstructorDimensions.D p) &&
        decide (r.lastService ≤ ConstructorDimensions.D p)) &&
  allFin p.K (fun a : Fin p.K =>
    match l.cutoffRegisters a with
    | none => true
    | some r => decide (r.score ≤ p.T * ConstructorDimensions.D p) &&
        decide (r.queue ≤ p.T * ConstructorDimensions.D p) &&
        decide (r.lastService ≤ ConstructorDimensions.D p)) &&
  allFin (p.m - 1) (fun i : Fin (p.m - 1) =>
    decide (l.baseScore i ≤ p.T * ConstructorDimensions.D p)) &&
  allFin p.K (fun a : Fin p.K =>
    decide (l.increment a ≤ p.T * ConstructorDimensions.D p)) &&
  allFin p.K (fun a : Fin p.K => decide (l.gammaLoc a ≤ ConstructorDimensions.D p))

/-- Enable-history consistency for a completed round boundary. -/
def readyHistoryCheck (l : Ledger p eta heta hcap n hn) : Bool :=
  allFin p.T fun r => decide (sourceRound r < l.cutoff) ||
    ((l.enabledHistory r).isSome == decide (sourceRound r < l.cursor))

/-- Enable-history consistency during a round after stage (1). -/
def startedHistoryCheck (l : Ledger p eta heta hcap n hn) : Bool :=
  allFin p.T fun r => decide (sourceRound r < l.cutoff) ||
    ((l.enabledHistory r).isSome == decide (sourceRound r ≤ l.cursor))

/-- Executable state check: finite source time domains, consistency of known
versus pending queues, and all stored numeric domains. -/
def validLedgerCheck (l : Ledger p eta heta hcap n hn) : Bool := by
  let ready := decide (l.phase = .ready)
  exact decide (1 ≤ l.sigma) && decide (l.sigma ≤ p.T) &&
    decide (1 ≤ l.cutoff) && decide (l.cutoff ≤ l.freezeAt) &&
    decide (l.cutoff ≤ p.T) &&
    decide (l.freezeAt ≤ p.T + 1) && decide (l.cutoff ≤ l.cursor) &&
    decide (l.cursor ≤ p.T + 1) &&
    (ready || decide (l.cursor ≤ p.T)) &&
    ((!ready) || allFin p.K (fun a : Fin p.K => decide (l.gammaLoc a = 0))) &&
    ((!ready) || readyHistoryCheck l) &&
    (ready || startedHistoryCheck l) &&
    allFin p.K (fun a : Fin p.K =>
      (l.currentRegisters a).isNone == armPendingCheck l a) &&
    allFin p.K (fun a : Fin p.K =>
      (l.cutoffRegisters a).isNone == armPendingCheck l a) &&
    allFin p.K (fun a : Fin p.K =>
      (!armPendingCheck l a) || decide (l.gammaLoc a = 0)) &&
    allFin p.K (fun a : Fin p.K =>
      (!armPendingCheck l a) || decide (l.increment a = 0)) &&
    registerDomainsCheck l && rawEntryDomainsCheck l

/-- The logical validity predicate is exactly the executable ledger check. -/
def validLedger (l : Ledger p eta heta hcap n hn) : Prop :=
  validLedgerCheck l = true

/-- Executable input checks for supplied cutoff registers and follower base
scores. Old-slow arms must be unknown and every outside arm must supply a
known cutoff register. -/
def validInitialInputsCheck (assignment : Assignment p) (sigma cutoff freezeAt : ℕ)
    (baseScore : Fin (p.m - 1) → ℕ)
    (outside : Fin p.K → Option CutoffRegister) : Bool :=
  decide (1 ≤ sigma) && decide (sigma ≤ p.T) &&
  decide (1 ≤ cutoff) && decide (cutoff ≤ freezeAt) &&
  decide (cutoff ≤ p.T) &&
  decide (freezeAt ≤ p.T + 1) &&
  allFin (p.m - 1) (fun i : Fin (p.m - 1) =>
    decide (baseScore i ≤ p.T * ConstructorDimensions.D p)) &&
  allFin p.K (fun a : Fin p.K =>
    if anyFin (p.m - 1) (fun i : Fin (p.m - 1) =>
        decide (assignment.arm i = a)) then
      decide (outside a = none)
    else
      match outside a with
      | none => false
      | some r => decide (r.score ≤ p.T * ConstructorDimensions.D p) &&
          decide (r.queue ≤ p.T * ConstructorDimensions.D p) &&
          decide (r.lastService ≤ ConstructorDimensions.D p))

/-- Initial collection state from supplied cutoff registers. Invalid times or
stored values are rejected before a ledger is returned. -/
def startCollectionChecked (p : ConstructorDimensions.Parameters) (eta : ℝ)
    (heta : 0 < eta) (hcap : sourceLearningCap p eta) (n : ℕ)
    (hn : (n : ℝ) = eta * (ConstructorDimensions.D p : ℝ))
    (assignment : Assignment p) (sigma cutoff freezeAt : ℕ)
    (baseScore : Fin (p.m - 1) → ℕ)
    (outside : Fin p.K → Option CutoffRegister) :
    Checked (Ledger p eta heta hcap n hn) := by
  exact if validInitialInputsCheck assignment sigma cutoff freezeAt baseScore outside then
    let initial : Ledger p eta heta hcap n hn := {
      assignment := assignment
      sigma := sigma
      cutoff := cutoff
      freezeAt := freezeAt
      baseScore := baseScore
      pending := Finset.univ
      cutoffRegisters := outside
      currentRegisters := fun a => (outside a).map fun q =>
        ⟨q.queue, q.lastService⟩
      increment := fun _ => 0
      gammaLoc := fun _ => 0
      rawBuffer := fun _ _ => none
      enabledHistory := fun _ => none
      cursor := cutoff
      phase := .ready
    }
    if validLedgerCheck initial then .success initial else .invalid
  else
    .invalid

/-- Store an arrival in exactly one arm/calendar slot. -/
def putRaw (buffer : Fin p.K → Fin p.T → Option ℕ) (a : Fin p.K)
    (r : Fin p.T) (amount : ℕ) : Fin p.K → Fin p.T → Option ℕ :=
  fun a' r' => if a' = a ∧ r' = r then some amount else buffer a' r'

theorem putRaw_same (buffer : Fin p.K → Fin p.T → Option ℕ)
    (a : Fin p.K) (r : Fin p.T) (amount : ℕ) :
    putRaw buffer a r amount a r = some amount := by
  simp [putRaw]

theorem putRaw_other (buffer : Fin p.K → Fin p.T → Option ℕ)
    (a a' : Fin p.K) (r r' : Fin p.T) (amount : ℕ)
    (h : a' ≠ a ∨ r' ≠ r) :
    putRaw buffer a r amount a' r' = buffer a' r' := by
  have hnot : ¬ (a' = a ∧ r' = r) := by
    rintro ⟨ha, hr⟩
    rcases h with h | h
    · exact h ha
    · exact h hr
  simp [putRaw, hnot]

/-- Remove one recovered arm's raw-arrival column and retain every other arm. -/
def clearRawArm (buffer : Fin p.K → Fin p.T → Option ℕ) (a : Fin p.K) :=
  fun a' r => if a' = a then none else buffer a' r

theorem clearRawArm_same (buffer : Fin p.K → Fin p.T → Option ℕ)
    (a : Fin p.K) (r : Fin p.T) : clearRawArm buffer a a r = none := by
  simp [clearRawArm]

theorem clearRawArm_other (buffer : Fin p.K → Fin p.T → Option ℕ)
    (a a' : Fin p.K) (r : Fin p.T) (h : a' ≠ a) :
    clearRawArm buffer a a' r = buffer a' r := by
  simp [clearRawArm, h]

/-- The exact amount presented to the queue rule for a known arm. -/
def localArrival (raw : Option (Fin p.K × ℕ)) (a : Fin p.K) : ℕ :=
  match raw with
  | none => 0
  | some (b, amount) => if b = a then amount else 0

/-- Queue input for a working current register. At and after `freezeAt`, the
queue update is disabled and therefore preserves the queue. -/
def localQueueRecord (l : Ledger p eta heta hcap n hn) (r : Fin p.T)
    (enabled : Bool) (raw : Option (Fin p.K × ℕ)) (a : Fin p.K) : Bool × ℕ :=
  if enabled && decide (sourceRound r < l.freezeAt) then
    (true, localArrival raw a)
  else
    (false, 0)

/-- Pure result of stage (1), after its explicit input checks. -/
def startRoundCandidate (l : Ledger p eta heta hcap n hn) (r : Fin p.T)
    (enabled : Bool) (raw : Option (Fin p.K × ℕ)) :
    Ledger p eta heta hcap n hn := by
  let rawBuffer : Fin p.K → Fin p.T → Option ℕ := match raw with
    | some (a, amount) =>
        if l.currentRegisters a = none ∧ amount > 0 ∧
            sourceRound r < l.freezeAt then
          putRaw l.rawBuffer a r amount
        else l.rawBuffer
    | none => l.rawBuffer
  let currentRegisters : Fin p.K → Option CurrentRegister := fun a =>
    match l.currentRegisters a with
    | none => none
    | some current =>
        let next := QueueReplay.transition (4 * n) (0, current.queue)
          (localQueueRecord l r enabled raw a)
        some ⟨next.2, next.1⟩
  let gammaLoc : Fin p.K → ℕ := fun a =>
    match l.currentRegisters a with
    | none => 0
    | some current =>
        (QueueReplay.transition (4 * n) (0, current.queue)
          (localQueueRecord l r enabled raw a)).1
  exact { l with
    rawBuffer := rawBuffer
    currentRegisters := currentRegisters
    gammaLoc := gammaLoc
    enabledHistory := Function.update l.enabledHistory r (some enabled)
    cursor := sourceRound r
    phase := .started }

/-- A raw record is within its checked natural arrival domain. -/
def rawInputDomainCheck (raw : Option (Fin p.K × ℕ)) : Bool :=
  match raw with
  | none => true
  | some (_, amount) => decide (amount ≤ ConstructorDimensions.D p)

/-- A newly buffered arm/round cell must be empty before stage (1) writes it. -/
def rawSlotFreshCheck (l : Ledger p eta heta hcap n hn) (r : Fin p.T)
    (raw : Option (Fin p.K × ℕ)) : Bool :=
  match raw with
  | none => true
  | some (a, amount) =>
      if (l.currentRegisters a).isNone && decide (0 < amount) &&
          decide (sourceRound r < l.freezeAt) then
        decide (l.rawBuffer a r = none)
      else true

/-- Stage (1): consume the recorder result, update every known queue on this
calendar round, and buffer a positive arrival only when its queue is unknown. -/
def startRound (l : Ledger p eta heta hcap n hn) (t : ℕ) (enabled : Bool)
    (raw : Option (Fin p.K × ℕ)) : Checked (Ledger p eta heta hcap n hn) := by
  exact if hinput : validLedgerCheck l = true ∧ l.phase = .ready ∧
      t = l.cursor ∧ 1 ≤ t ∧ t ≤ p.T ∧ rawInputDomainCheck raw = true then
    let r : Fin p.T := ⟨t - 1, by omega⟩
    if rawSlotFreshCheck l r raw then
      let next := startRoundCandidate l r enabled raw
      if validLedgerCheck next then .success next else .invalid
    else
      .invalid
  else
    .invalid

/-- Finite list of calendar indices, in source order, from `start` for
`length` rounds. -/
def calendarIndices (T start length : ℕ) (hbound : start + length ≤ T) :
    List (Fin T) := by
  exact List.ofFn fun i : Fin length =>
    ⟨start + i.val, by have hi := i.isLt; omega⟩

/-- The chronological source labels in `calendarIndices`. -/
def calendarLabels (T start length : ℕ) (hbound : start + length ≤ T) :
    List ℕ := (calendarIndices T start length hbound).map sourceRound

theorem calendarIndices_length (T start length : ℕ) (hbound : start + length ≤ T) :
    (calendarIndices T start length hbound).length = length := by
  simp [calendarIndices]

/-- Turn a raw buffer and complete enable history into literal queue records.
Missing enable flags return `none`, rather than a guessed Boolean value. -/
def replayRecords? (l : Ledger p eta heta hcap n hn) (a : Fin p.K) :
    List (Fin p.T) → Option (List (Bool × ℕ))
  | [] => some []
  | r :: rest => do
      let enabled ← l.enabledHistory r
      let tail ← replayRecords? l a rest
      pure ((enabled && decide (sourceRound r < l.freezeAt),
        bufferedArrival l a r) :: tail)

/-- A supplied per-round arrival sequence retained for a direct replay
comparison. -/
def explicitArrival (sequence : Fin p.T → Option (Fin p.K × ℕ))
    (a : Fin p.K) (r : Fin p.T) : ℕ :=
  match sequence r with
  | none => 0
  | some (b, amount) => if b = a then amount else 0

/-- The option stored in a generated buffer cell from the explicit recorder
sequence. -/
def explicitArrivalCell (sequence : Fin p.T → Option (Fin p.K × ℕ))
    (a : Fin p.K) (r : Fin p.T) : Option ℕ :=
  match sequence r with
  | none => none
  | some (b, amount) => if b = a then some amount else none

/-- The queue input arrival after the source freeze boundary. -/
def replayArrival (sequence : Fin p.T → Option (Fin p.K × ℕ))
    (freezeAt : ℕ) (a : Fin p.K) (r : Fin p.T) : ℕ :=
  if sourceRound r < freezeAt then explicitArrival sequence a r else 0

/-- Direct all-calendar queue records from an explicit recorder sequence and
the supplied enable bits. -/
def directRecords (sequence : Fin p.T → Option (Fin p.K × ℕ))
    (enabledHistory : Fin p.T → Bool) (freezeAt : ℕ) (a : Fin p.K)
    (indices : List (Fin p.T)) : List (Bool × ℕ) :=
  indices.map fun r =>
    (enabledHistory r && decide (sourceRound r < freezeAt),
      replayArrival sequence freezeAt a r)

/-- Check one literal replay prefix's stored queue and accumulated service,
and the service added by its final record. Prefixes are evaluated only with
`QueueReplay.replay`; this check introduces no alternate queue recurrence. -/
def replayPrefixOutputDomainsCheck (capacity initialQueue : ℕ)
    (records : List (Bool × ℕ)) (prefixLength : Fin (records.length + 1)) : Bool :=
  let endpoint := QueueReplay.replay capacity (0, initialQueue)
    (records.take prefixLength.val)
  let endpointCheck := decide (endpoint.1 ≤ p.T * ConstructorDimensions.D p) &&
    decide (endpoint.2 ≤ p.T * ConstructorDimensions.D p)
  if prefixLength.val = 0 then endpointCheck
  else
    let previous := QueueReplay.replay capacity (0, initialQueue)
      (records.take (prefixLength.val - 1))
    endpointCheck && decide (endpoint.1 - previous.1 ≤ ConstructorDimensions.D p)

/-- Executable checks for every supplied replay input and every intermediate
all-calendar endpoint before a recovered ledger is stored. -/
def replayOutputDomainsCheck (capacity initialQueue : ℕ)
    (records : List (Bool × ℕ)) : Bool :=
  decide (records.length ≤ p.T) &&
  records.all (fun record => decide (record.2 ≤ ConstructorDimensions.D p)) &&
  allFin (records.length + 1) fun prefixLength =>
    replayPrefixOutputDomainsCheck (p := p) capacity initialQueue records prefixLength

/-- The exact update to one raw-buffer cell made by stage (1). -/
def stageOneBufferCell (old : Option ℕ) (known : Bool) (beforeFreeze : Bool)
    (raw : Option ℕ) : Option ℕ :=
  match raw with
  | none => old
  | some amount =>
      if amount = 0 then old
      else if known then old
      else if beforeFreeze then some amount else old

theorem stageOneBufferCell_positive (old : Option ℕ) (beforeFreeze : Bool)
    (amount : ℕ) (hpositive : 0 < amount) :
    stageOneBufferCell old false beforeFreeze (some amount) =
      if beforeFreeze then some amount else old := by
  have hne : amount ≠ 0 := by omega
  cases beforeFreeze <;> simp [stageOneBufferCell, hne]

theorem stageOneBufferCell_zero (old : Option ℕ) (known beforeFreeze : Bool) :
    stageOneBufferCell old known beforeFreeze (some 0) = old := by
  cases known <;> cases beforeFreeze <;> simp [stageOneBufferCell]

/-- The generated positive-arrival buffer obtained by applying stage (1)'s
buffer-cell update to an explicit finite sequence of round inputs. The Boolean
records whether that arm's queue was already known before the round. -/
def generatedBuffer (initial : Fin p.K → Fin p.T → Option ℕ)
    (sequence : Fin p.T → Option (Fin p.K × ℕ))
    (knownBefore : Fin p.T → Fin p.K → Bool)
    (freezeAt : ℕ) : Fin p.K → Fin p.T → Option ℕ :=
  fun a r => stageOneBufferCell (initial a r) (knownBefore r a)
    (decide (sourceRound r < freezeAt)) (explicitArrivalCell sequence a r)

/-- For an unknown queue, a positive recorder arrival occupies exactly its
arm/round buffer cell. -/
theorem generatedBuffer_at_positive (initial : Fin p.K → Fin p.T → Option ℕ)
    (sequence : Fin p.T → Option (Fin p.K × ℕ))
    (unknownBefore : Fin p.T → Fin p.K → Bool) (freezeAt : ℕ)
    (a : Fin p.K) (r : Fin p.T) (amount : ℕ)
    (hraw : sequence r = some (a, amount)) (hunknown : unknownBefore r a = false)
    (hpositive : 0 < amount) (hbefore : sourceRound r < freezeAt) :
    generatedBuffer initial sequence unknownBefore freezeAt a r = some amount := by
  have hne : amount ≠ 0 := by omega
  simp [generatedBuffer, explicitArrivalCell, hraw, hunknown, hbefore,
    hne, stageOneBufferCell]

/-- With an empty prior cell, a missing, other-arm, or zero recorder input
leaves the buffer empty and therefore contributes zero to replay. -/
theorem generatedBuffer_at_missing (initial : Fin p.K → Fin p.T → Option ℕ)
    (sequence : Fin p.T → Option (Fin p.K × ℕ))
    (unknownBefore : Fin p.T → Fin p.K → Bool) (freezeAt : ℕ)
    (a : Fin p.K) (r : Fin p.T) (hinitial : initial a r = none)
    (hraw : sequence r = none ∨ ∃ b amount, sequence r = some (b, amount) ∧
      (b ≠ a ∨ amount = 0)) :
    generatedBuffer initial sequence unknownBefore freezeAt a r = none := by
  rcases hraw with hnone | ⟨b, amount, hsome, hmiss⟩
  · simp [generatedBuffer, explicitArrivalCell, hnone, hinitial, stageOneBufferCell]
  · rcases hmiss with hne | hzero
    · simp [generatedBuffer, explicitArrivalCell, hsome, hne, hinitial,
        stageOneBufferCell]
    · subst amount
      by_cases hba : b = a
      · simp [generatedBuffer, explicitArrivalCell, hsome, hba, hinitial,
          stageOneBufferCell]
      · simp [generatedBuffer, explicitArrivalCell, hsome, hba, hinitial,
          stageOneBufferCell]

/-- If an arm remains unknown throughout collection, its generated stamped
buffer yields the source arrival before freeze and zero thereafter. -/
theorem generatedBuffer_arrival_eq_replayArrival
    (initial : Fin p.K → Fin p.T → Option ℕ)
    (sequence : Fin p.T → Option (Fin p.K × ℕ))
    (unknownBefore : Fin p.T → Fin p.K → Bool) (freezeAt : ℕ)
    (a : Fin p.K) (r : Fin p.T)
    (hinitial : initial a r = none)
    (hunknown : unknownBefore r a = false) :
    (generatedBuffer initial sequence unknownBefore freezeAt a r).getD 0 =
      replayArrival sequence freezeAt a r := by
  by_cases hbefore : sourceRound r < freezeAt
  · cases hraw : sequence r with
    | none => simp [generatedBuffer, explicitArrivalCell, explicitArrival,
        hraw, hinitial,
        replayArrival, hbefore, stageOneBufferCell]
    | some value =>
        rcases value with ⟨b, amount⟩
        by_cases hba : b = a
        · subst b
          by_cases hzero : amount = 0
          · subst amount
            simp [generatedBuffer, explicitArrivalCell, explicitArrival,
              hraw, hinitial,
              replayArrival, hbefore, stageOneBufferCell]
          · have hpositive : 0 < amount := by omega
            simp [generatedBuffer, explicitArrivalCell, explicitArrival,
              hraw, hunknown, replayArrival, hbefore, hzero,
              stageOneBufferCell]
        · simp [generatedBuffer, explicitArrivalCell, explicitArrival,
            hraw, hinitial,
            replayArrival, hbefore, hba, stageOneBufferCell]
  · cases hraw : sequence r with
    | none => simp [generatedBuffer, explicitArrivalCell,
        hraw, hinitial,
        replayArrival, hbefore, stageOneBufferCell]
    | some value =>
        rcases value with ⟨b, amount⟩
        by_cases hba : b = a
        · subst b
          by_cases hzero : amount = 0
          · subst amount
            simp [generatedBuffer, explicitArrivalCell,
              hraw, hinitial,
              replayArrival, hbefore, stageOneBufferCell]
          · have hpositive : 0 < amount := by omega
            simp [generatedBuffer, explicitArrivalCell,
              hraw, hinitial,
              hunknown, replayArrival, hbefore, hzero,
              stageOneBufferCell]
        · simp [generatedBuffer, explicitArrivalCell,
            hraw, hinitial,
            replayArrival, hbefore, hba, stageOneBufferCell]

/-- When the raw recorder returns a positive arrival to an unknown queue,
stage (1) writes that arm/round cell, provided its checked slot is empty. -/
theorem startRoundCandidate_rawBuffer_positive
    (l : Ledger p eta heta hcap n hn) (r : Fin p.T)
    (enabled : Bool) (a : Fin p.K) (amount : ℕ)
    (hunknown : l.currentRegisters a = none) (hpositive : 0 < amount)
    (hbefore : sourceRound r < l.freezeAt) :
    (startRoundCandidate l r enabled (some (a, amount))).rawBuffer a r =
      some amount := by
  simp [startRoundCandidate, hunknown, hpositive, hbefore, putRaw]

/-- Every calendar cell not named by a positive recorder arrival is stored as
`none` when the initial arm/time buffer is empty. -/
theorem generatedBuffer_cell_empty_of_no_arrival
    (initial : Fin p.K → Fin p.T → Option ℕ)
    (sequence : Fin p.T → Option (Fin p.K × ℕ))
    (unknownBefore : Fin p.T → Fin p.K → Bool) (freezeAt : ℕ)
    (a : Fin p.K) (r : Fin p.T) (hinitial : initial a r = none)
    (hraw : sequence r = none ∨ ∃ b amount,
      sequence r = some (b, amount) ∧ (b ≠ a ∨ amount = 0)) :
    (generatedBuffer initial sequence unknownBefore freezeAt a r).getD 0 = 0 := by
  rw [generatedBuffer_at_missing initial sequence unknownBefore freezeAt a r
    hinitial hraw]
  rfl

/-- Stage (1)'s stamped buffer agrees cell-by-cell with the explicit
finite recorder sequence on every round whose enable history and buffer were
supplied. Missing cells contribute the source's zero arrival. -/
theorem replayRecords?_equals_directRecords
    (l : Ledger p eta heta hcap n hn) (a : Fin p.K)
    (sequence : Fin p.T → Option (Fin p.K × ℕ))
    (enabledHistory : Fin p.T → Bool) (indices : List (Fin p.T))
    (henabled : ∀ r ∈ indices,
      l.enabledHistory r = some (enabledHistory r))
    (harrival : ∀ r ∈ indices,
      bufferedArrival l a r = replayArrival sequence l.freezeAt a r) :
    replayRecords? l a indices =
      some (directRecords sequence enabledHistory l.freezeAt a indices) := by
  induction indices with
  | nil => rfl
  | cons r rest ih =>
      have henabledHead := henabled r (by simp)
      have harrivalHead := harrival r (by simp)
      have henabledTail : ∀ s ∈ rest,
          l.enabledHistory s = some (enabledHistory s) := by
        intro s hs
        exact henabled s (by simp [hs])
      have harrivalTail : ∀ s ∈ rest,
          bufferedArrival l a s = replayArrival sequence l.freezeAt a s := by
        intro s hs
        exact harrival s (by simp [hs])
      simp [replayRecords?, directRecords, henabledHead, harrivalHead,
        ih henabledTail harrivalTail]

/-- When a ledger buffer is the result of stage (1) over an explicit finite
recorder sequence, its complete calendar records are exactly the records used
by direct `QueueReplay`. The inputs are the initial empty cells, the unknown
status before each listed round, and the already supplied enable history. -/
theorem replayRecords?_generatedBuffer
    (l : Ledger p eta heta hcap n hn) (a : Fin p.K)
    (initial : Fin p.K → Fin p.T → Option ℕ)
    (sequence : Fin p.T → Option (Fin p.K × ℕ))
    (unknownBefore : Fin p.T → Fin p.K → Bool)
    (enabledHistory : Fin p.T → Bool) (indices : List (Fin p.T))
    (hbuffer : ∀ r ∈ indices,
      l.rawBuffer a r = generatedBuffer initial sequence unknownBefore l.freezeAt a r)
    (hinitial : ∀ r ∈ indices, initial a r = none)
    (hunknown : ∀ r ∈ indices, unknownBefore r a = false)
    (henabled : ∀ r ∈ indices,
      l.enabledHistory r = some (enabledHistory r)) :
    replayRecords? l a indices =
      some (directRecords sequence enabledHistory l.freezeAt a indices) := by
  apply replayRecords?_equals_directRecords l a sequence enabledHistory indices
    henabled
  intro r hr
  unfold bufferedArrival
  rw [hbuffer r hr]
  exact generatedBuffer_arrival_eq_replayArrival initial sequence unknownBefore
    l.freezeAt a r (hinitial r hr) (hunknown r hr)

/-- Complete replay plus its last service, calculated with the literal queue
replay for the prefix and the literal transition on the acceptance round. -/
structure ReplayResult where
  registers : ℕ × ℕ
  lastService : ℕ
  prefixRegisters : ℕ × ℕ
  deriving DecidableEq, Repr

/-- The exposed replay calculation. `current` is expected to be the single
acceptance-round record, as enforced by the checked operation. -/
def replayResult (capacity initialQueue : ℕ)
    (past : List (Bool × ℕ)) (current : Bool × ℕ) : ReplayResult := by
  let prefixRegisters := QueueReplay.replay capacity (0, initialQueue) past
  let currentRegisters := QueueReplay.replay capacity (0, initialQueue)
    (past ++ [current])
  let lastTransition := QueueReplay.transition capacity prefixRegisters current
  exact ⟨currentRegisters, lastTransition.1 - prefixRegisters.1, prefixRegisters⟩

/-- Appending the single acceptance-round record is the literal transition
from the all-calendar prefix endpoint. -/
theorem queueReplay_append_current (capacity : ℕ) (initial : ℕ × ℕ)
    (past : List (Bool × ℕ)) (current : Bool × ℕ) :
    QueueReplay.replay capacity initial (past ++ [current]) =
      QueueReplay.transition capacity (QueueReplay.replay capacity initial past)
        current := by
  rw [QueueReplay.replay_append]
  rfl

/-- The completed replay endpoint is the direct all-calendar `QueueReplay`
result through the acceptance round. -/
theorem replayResult_registers_eq_all_calendar
    (capacity initialQueue : ℕ) (past : List (Bool × ℕ))
    (current : Bool × ℕ) :
    (replayResult capacity initialQueue past current).registers =
      QueueReplay.replay capacity (0, initialQueue) (past ++ [current]) := by
  rfl

/-- The recorded last service is exactly the score difference from the
all-calendar replay prefix to its acceptance-round endpoint. -/
theorem replayResult_lastService_eq_all_calendar_difference
    (capacity initialQueue : ℕ) (past : List (Bool × ℕ))
    (current : Bool × ℕ) :
    (replayResult capacity initialQueue past current).lastService =
      (QueueReplay.replay capacity (0, initialQueue) (past ++ [current])).1 -
        (QueueReplay.replay capacity (0, initialQueue) past).1 := by
  unfold replayResult
  rw [QueueReplay.replay_append]
  rfl

/-- With one current record, the replay endpoint is the literal transition from
the prefix endpoint. -/
theorem replayResult_one_round (capacity initialQueue : ℕ)
    (past : List (Bool × ℕ)) (record : Bool × ℕ) :
    (replayResult capacity initialQueue past record).registers =
      QueueReplay.transition capacity
        (QueueReplay.replay capacity (0, initialQueue) past) record := by
  simp [replayResult, QueueReplay.replay]

/-- The last service is the exact score difference across the acceptance
round, so adding it to the prefix score counts that round once. -/
theorem replayResult_lastService_add_prefix (capacity initialQueue : ℕ)
    (past : List (Bool × ℕ)) (record : Bool × ℕ) :
    (QueueReplay.transition capacity
        (QueueReplay.replay capacity (0, initialQueue) past) record).1 =
      (QueueReplay.replay capacity (0, initialQueue) past).1 +
        ((QueueReplay.transition capacity
          (QueueReplay.replay capacity (0, initialQueue) past) record).1 -
          (QueueReplay.replay capacity (0, initialQueue) past).1) := by
  cases hbit : record.1 <;> simp [QueueReplay.transition, hbit]

/-- Pure accepted-UP candidate. The checked wrapper validates the local state,
acceptance predicate, input domains, and computed output before returning it. -/
def acceptUpCandidate (l : Ledger p eta heta hcap n hn)
    (i : Fin (p.m - 1)) (M : OrdinaryMessageCodec.UpRecord (codecParams p eta))
    (past : List (Bool × ℕ)) (current : Bool × ℕ) :
    Ledger p eta heta hcap n hn := by
  let a := l.assignment.arm i
  let result := replayResult (4 * n) M.val.q past current
  let cut : CutoffRegister := ⟨l.baseScore i + M.val.S, M.val.q, M.val.delta⟩
  let now : CurrentRegister := ⟨result.registers.2, result.lastService⟩
  exact { l with
    cutoffRegisters := Function.update l.cutoffRegisters a (some cut)
    currentRegisters := Function.update l.currentRegisters a (some now)
    increment := Function.update l.increment a result.registers.1
    rawBuffer := clearRawArm l.rawBuffer a
    pending := l.pending.erase i
    phase := .decoded }

/-- Recovering one arm leaves every pre-decode local service value intact. -/
theorem acceptUpCandidate_preserves_gammaLoc
    (l : Ledger p eta heta hcap n hn) (i : Fin (p.m - 1))
    (M : OrdinaryMessageCodec.UpRecord (codecParams p eta))
    (past : List (Bool × ℕ)) (current : Bool × ℕ) (a : Fin p.K) :
    (acceptUpCandidate l i M past current).gammaLoc a = l.gammaLoc a := rfl

/-- The accepted candidate stores the literal replay endpoint, score sum, and
UP cutoff fields at exactly the assigned arm. -/
theorem acceptUpCandidate_recovered_fields
    (l : Ledger p eta heta hcap n hn) (i : Fin (p.m - 1))
    (M : OrdinaryMessageCodec.UpRecord (codecParams p eta))
    (past : List (Bool × ℕ)) (current : Bool × ℕ) :
    let a := l.assignment.arm i
    (acceptUpCandidate l i M past current).currentRegisters a =
        some ⟨(QueueReplay.replay (4 * n) (0, M.val.q)
            (past ++ [current])).2,
          (QueueReplay.replay (4 * n) (0, M.val.q)
            (past ++ [current])).1 -
            (QueueReplay.replay (4 * n) (0, M.val.q) past).1⟩ ∧
      (acceptUpCandidate l i M past current).increment a =
        (QueueReplay.replay (4 * n) (0, M.val.q)
          (past ++ [current])).1 ∧
      (acceptUpCandidate l i M past current).cutoffRegisters a =
        some ⟨l.baseScore i + M.val.S, M.val.q, M.val.delta⟩ := by
  constructor
  · simp [acceptUpCandidate, replayResult, Function.update_self,
      queueReplay_append_current]
  constructor
  · simp [acceptUpCandidate, replayResult, Function.update_self]
  · simp [acceptUpCandidate, Function.update_self]

/-- Stage (2): test the codec's actual current-UP acceptance predicate.
Rejection leaves data registers, pending membership, accumulator, and raw
storage unchanged while advancing the round phase. Acceptance recovers cutoff
data and replays every round from cutoff through the acceptance round,
including enabled zero-arrival service. -/
def decodeUp (l : Ledger p eta heta hcap n hn) (i : Fin (p.m - 1))
    (parsed : Option (OrdinaryMessageCodec.UpRecord (codecParams p eta))) :
    Checked (Ledger p eta heta hcap n hn) := by
  exact if hinput : validLedgerCheck l = true ∧ l.phase = .started ∧
      1 ≤ l.cutoff ∧ l.cutoff ≤ l.cursor ∧ l.cursor ≤ p.T then
    match parsed with
    | none =>
        let next := { l with phase := .decoded }
        if validLedgerCheck next then .rejected next else .invalid
    | some M =>
        if acceptUpCheck l i M then
          if hunknown : l.currentRegisters (l.assignment.arm i) = none ∧
              l.cutoffRegisters (l.assignment.arm i) = none then
            let start := l.cutoff - 1
            let prefixLength := l.cursor - l.cutoff
            let hprefix : start + prefixLength ≤ p.T := by
              have hcutPos := hinput.2.2.1
              have hcutCursor := hinput.2.2.2.1
              have hcursorT := hinput.2.2.2.2
              omega
            let prefixIndices := calendarIndices p.T start prefixLength hprefix
            let lastIndex : Fin p.T := ⟨l.cursor - 1, by
              have hcutPos := hinput.2.2.1
              have hcutCursor := hinput.2.2.2.1
              have hcursorT := hinput.2.2.2.2
              omega⟩
            let past? := replayRecords? l (l.assignment.arm i) prefixIndices
            let last? := replayRecords? l (l.assignment.arm i) [lastIndex]
            match past?, last? with
            | some past, some last =>
                match last with
                | [] => .invalid
                | record :: [] =>
                    let records := past ++ [record]
                    if replayOutputDomainsCheck (p := p) (4 * n) M.val.q records then
                      let next := acceptUpCandidate l i M past record
                      if validLedgerCheck next then .success next else .invalid
                    else
                      .invalid
                | _ => .invalid
            | _, _ => .invalid
          else
            .invalid
        else
          let next := { l with phase := .decoded }
          if validLedgerCheck next then .rejected next else .invalid
  else
    .invalid

/-- Pure finish-round candidate. -/
def finishRoundCandidate (l : Ledger p eta heta hcap n hn) :
    Ledger p eta heta hcap n hn :=
  { l with
    increment := fun a => l.increment a + l.gammaLoc a
    gammaLoc := fun _ => 0
    cursor := l.cursor + 1
    phase := .ready }

/-- Stage (3): add pre-decode local service to the partial accumulator and
advance the local round cursor. -/
def finishRound (l : Ledger p eta heta hcap n hn) :
    Checked (Ledger p eta heta hcap n hn) := by
  exact if hinput : validLedgerCheck l = true ∧
      l.phase = .decoded ∧ l.cursor ≤ p.T then
    let next := finishRoundCandidate l
    if validLedgerCheck next then .success next else .invalid
  else
    .invalid

/-- A known queue is updated by the literal `QueueReplay.transition`. -/
theorem startRoundCandidate_known_transition (l : Ledger p eta heta hcap n hn)
    (r : Fin p.T) (enabled : Bool) (raw : Option (Fin p.K × ℕ))
    (a : Fin p.K) (current : CurrentRegister)
    (hknown : l.currentRegisters a = some current) :
    (startRoundCandidate l r enabled raw).currentRegisters a =
      some ⟨(QueueReplay.transition (4 * n) (0, current.queue)
        (localQueueRecord l r enabled raw a)).2,
        (QueueReplay.transition (4 * n) (0, current.queue)
          (localQueueRecord l r enabled raw a)).1⟩ := by
  simp [startRoundCandidate, hknown]

/-- Unknown queues contribute zero to pre-decode local service. -/
theorem startRoundCandidate_unknown_zero (l : Ledger p eta heta hcap n hn)
    (r : Fin p.T) (enabled : Bool) (raw : Option (Fin p.K × ℕ))
    (a : Fin p.K) (hunknown : l.currentRegisters a = none) :
    (startRoundCandidate l r enabled raw).gammaLoc a = 0 := by
  simp [startRoundCandidate, hunknown]

/-- A recovered unknown arm is not charged again by `FinishRound`: its local
service was zero before decoding, while the accumulator already contains the
entire replay through the current acceptance round. -/
theorem finish_recovered_increment_once
    (l : Ledger p eta heta hcap n hn) (i : Fin (p.m - 1))
    (M : OrdinaryMessageCodec.UpRecord (codecParams p eta))
    (past : List (Bool × ℕ)) (current : Bool × ℕ)
    (hunknown : l.currentRegisters (l.assignment.arm i) = none)
    (hgamma : l.gammaLoc (l.assignment.arm i) = 0) :
    l.currentRegisters (l.assignment.arm i) = none ∧
      l.gammaLoc (l.assignment.arm i) = 0 ∧
      (finishRoundCandidate (acceptUpCandidate l i M past current)).increment
        (l.assignment.arm i) =
        (replayResult (4 * n) M.val.q past current).registers.1 := by
  refine ⟨hunknown, hgamma, ?_⟩
  simp [finishRoundCandidate, acceptUpCandidate, hgamma, replayResult]

/-- Stage (1)'s unknown-arm branch forces zero local service, and stage (2)
preserves that zero, so stage (3) retains the complete replay score without
counting acceptance-round service a second time. -/
theorem finish_recovered_increment_once_after_stageOne
    (l : Ledger p eta heta hcap n hn) (r : Fin p.T) (enabled : Bool)
    (raw : Option (Fin p.K × ℕ)) (i : Fin (p.m - 1))
    (M : OrdinaryMessageCodec.UpRecord (codecParams p eta))
    (past : List (Bool × ℕ)) (current : Bool × ℕ)
    (hunknown : l.currentRegisters (l.assignment.arm i) = none) :
    (finishRoundCandidate (acceptUpCandidate
      (startRoundCandidate l r enabled raw) i M past current)).increment
        (l.assignment.arm i) =
      (replayResult (4 * n) M.val.q past current).registers.1 := by
  let started := startRoundCandidate l r enabled raw
  have hunknownStarted : started.currentRegisters (l.assignment.arm i) = none := by
    simp [started, startRoundCandidate, hunknown]
  have hzeroStarted : started.gammaLoc (l.assignment.arm i) = 0 := by
    exact startRoundCandidate_unknown_zero l r enabled raw (l.assignment.arm i) hunknown
  exact (finish_recovered_increment_once started i M past current
    hunknownStarted hzeroStarted).2.2

/-- Online continuation from a replay prefix equals replay on the appended
calendar record. -/
theorem replay_online_append (capacity : ℕ) (initial : ℕ × ℕ)
    (past : List (Bool × ℕ)) (record : Bool × ℕ) :
    QueueReplay.transition capacity (QueueReplay.replay capacity initial past) record =
      QueueReplay.replay capacity initial (past ++ [record]) := by
  symm
  rw [QueueReplay.replay_append]
  simp [QueueReplay.replay]

/-- The queue score extends by precisely the one-round service when a known
queue continues online after a replay prefix. -/
theorem replay_online_service_append (capacity : ℕ) (initial : ℕ × ℕ)
    (past : List (Bool × ℕ)) (record : Bool × ℕ) :
    (QueueReplay.replay capacity initial (past ++ [record])).1 =
      (QueueReplay.replay capacity initial past).1 +
        ((QueueReplay.transition capacity
          (QueueReplay.replay capacity initial past) record).1 -
          (QueueReplay.replay capacity initial past).1) := by
  rw [QueueReplay.replay_append]
  cases QueueReplay.replay capacity initial past with
  | mk score backlog =>
      cases hbit : record.1 <;>
        simp [QueueReplay.replay, QueueReplay.transition, hbit]

end Bandits.Support.CoordinatorCollectionLedger

end
