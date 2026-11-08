/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferencePrelaunchFollower
public import Bandits.Support.PrelaunchBufferRecovery
public import Bandits.Support.FollowerCutoffScan
public import Bandits.Support.ActiveRoundActions
public import Bandits.Support.OrdinaryMessageCodec
public import Bandits.Support.CompletePublicTable
public import Mathlib.Data.List.Nodup

import Lean.Elab.Tactic.Omega

/-!
# Literal active follower lifecycle operations

This module implements only the follower's local start interruption, pending
release, and end-of-round proposal read from
`sources/zip4/manuscript/06_interruptions.tex:9-14,108-114,164-177,193-203,235-348`
and `sources/zip4/manuscript/appendix_a_local_protocol.tex:8-14`.

It reuses `ReferencePrelaunchFollower.State`, the accepted DOWN codec record,
the accepted one-based-to-`Fin` arm conversion, and
`FollowerCutoffScan.gridBoundary` / `completeRowProposalBit`. The only added
local memory is an optional timestamped bit for the last proposal actually
read. These checked operations do not construct a physical run, decoder or
queue transition, source invariant, global release law, or endpoint theorem.
Their state and post-service inputs are supplied explicitly.
Proposal-token provenance, the choice of the player's declared row, and the
relation between the supplied pre-choice and post-service snapshots are
application obligations. These operations do not certify arbitrary snapshots
or saved tokens as a chronological physical execution. Nonpending release is
an unused-operation no-op, not a validation of the supplied snapshots.
-/

@[expose] public section

namespace Bandits.Support.ActiveFollowerLifecycle

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.OrdinaryMessageCodec
open Bandits.Support.ActiveRoundActions
open Bandits.Support.PublicDiscreteDraws
open Bandits.Support.FollowerCutoffScan
open Bandits.Support.FiniteBanditModel
open Bandits.Support.OrderedTupleSampler

/-- Reasons this local operation rejects a source-domain violation. -/
inductive LifecycleFailure where
  | invalidLocalStateDomain
  | missingAcceptedDown
  | incompatibleAcceptedDown
  | missedGridBoundary
  | missingProposalRead
  | staleProposalRead
  deriving DecidableEq, Repr

/-- A checked local result. Failure is left for the later shared wrapper to
interpret as the absorbing error state. -/
abbrev LifecycleCheck (α : Type) := Except LifecycleFailure α

/-- A saved proposal token. `finishRound` produces this from the actual read;
provenance of supplied tokens belongs to the future chronological wrapper.
The timestamp is the zero-based table coordinate of the supplying row. -/
structure ProposalRead (p : Parameters) where
  timestamp : Fin p.T
  bit : Bool
  deriving DecidableEq

/-- The one-bit local proposal memory beside the existing follower state. -/
structure LocalMemory (p : Parameters) where
  lastProposalRead : Option (ProposalRead p)
  deriving DecidableEq

/-- Initial local proposal memory contains no fabricated history. -/
def initialMemory (p : Parameters) : LocalMemory p := ⟨none⟩

/-- Queue and service registers in their source integer domains. -/
def serviceRegistersValid {eta : LearningRate} (p : Parameters) (s : State p eta) : Prop :=
  s.S ≤ p.T * D p ∧ s.delta ≤ D p ∧ s.backlog ≤ p.T * D p

/-- Literal sparse-log domains from `06_interruptions.tex:193-203` and
`appendix_a_local_protocol.tex:8-14`: horizon timestamps, no repeated LIST
keys `(calendarRound, pilot)`, and denominator-`D` observations. The record's
arm and thinning scalar are bounded by their existing types. Its observation's
`Icc` type alone does not enforce quantization. No entries are deduplicated. -/
def localBufferValid {p : Parameters} {eta : LearningRate} (s : State p eta) : Prop :=
  (∀ record ∈ s.buffer, 1 ≤ record.calendarRound ∧ record.calendarRound ≤ p.T) ∧
  (s.buffer.map (fun record => (record.calendarRound, record.pilot))).Nodup ∧
  (∀ record ∈ s.buffer, ∃ q : ℕ, q ≤ D p ∧
    record.observation.val = (q : ℝ) / (D p : ℝ))

/-- Every saved timestamp is a source horizon round. -/
theorem localBufferValid_timestamp {p : Parameters} {eta : LearningRate}
    {s : State p eta} (h : localBufferValid s)
    (record : SparseCalendarReplay.SparseCalendarRecord p.K) (hr : record ∈ s.buffer) :
    1 ≤ record.calendarRound ∧ record.calendarRound ≤ p.T :=
  h.1 record hr

/-- No two LIST positions have the same calendar-round/arm key. -/
theorem localBufferValid_keys_nodup {p : Parameters} {eta : LearningRate}
    {s : State p eta} (h : localBufferValid s) :
    (s.buffer.map (fun record => (record.calendarRound, record.pilot))).Nodup :=
  h.2.1

/-- Repeated identical entries are forbidden as well as distinct entries with
the same key; equality of their values does not excuse a repeated position. -/
theorem localBufferValid_buffer_nodup {p : Parameters} {eta : LearningRate}
    {s : State p eta} (h : localBufferValid s) : s.buffer.Nodup :=
  (localBufferValid_keys_nodup h).of_map _

/-- In particular the buffer cannot contain two copies of any one record. -/
theorem localBufferValid_no_duplicate_record {p : Parameters} {eta : LearningRate}
    {s : State p eta} (h : localBufferValid s)
    (record : SparseCalendarReplay.SparseCalendarRecord p.K) :
    ¬ List.Sublist [record, record] s.buffer :=
  List.nodup_iff_sublist.mp (localBufferValid_buffer_nodup h) record

/-- Equal keys in the buffer identify the same record; unlike the old
validator, this is a consequence of no repeated keys, not its replacement. -/
theorem localBufferValid_record_eq_of_key_eq {p : Parameters} {eta : LearningRate}
    {s : State p eta} (h : localBufferValid s)
    (record other : SparseCalendarReplay.SparseCalendarRecord p.K)
    (hr : record ∈ s.buffer) (ho : other ∈ s.buffer)
    (hround : record.calendarRound = other.calendarRound)
    (harm : record.pilot = other.pilot) : record = other :=
  List.inj_on_of_nodup_map (localBufferValid_keys_nodup h) hr ho
    (Prod.ext hround harm)

/-- Equal round and pilot fields force equality of list POSITIONS, even when
the stored records would otherwise be identical. -/
theorem localBufferValid_key_positions {p : Parameters} {eta : LearningRate}
    {s : State p eta} (h : localBufferValid s)
    (i j : ℕ) (hi : i < s.buffer.length) (hj : j < s.buffer.length)
    (hround : s.buffer[i].calendarRound = s.buffer[j].calendarRound)
    (harm : s.buffer[i].pilot = s.buffer[j].pilot) : i = j := by
  have hiKeys : i < (s.buffer.map
      (fun record => (record.calendarRound, record.pilot))).length := by
    simpa only [List.length_map] using hi
  have hjKeys : j < (s.buffer.map
      (fun record => (record.calendarRound, record.pilot))).length := by
    simpa only [List.length_map] using hj
  apply (localBufferValid_keys_nodup h).getElem_inj_iff.mp
    (show (s.buffer.map (fun record => (record.calendarRound, record.pilot)))[i]'hiKeys =
      (s.buffer.map (fun record => (record.calendarRound, record.pilot)))[j]'hjKeys from ?_)
  simp only [List.getElem_map]
  exact Prod.ext hround harm

/-- The saved observation has the same denominator-`D` grid domain as the
existing `ReferencePrelaunchFollower.Observation`, in the record's actual type. -/
theorem localBufferValid_observation_grid {p : Parameters} {eta : LearningRate}
    {s : State p eta} (h : localBufferValid s)
    (record : SparseCalendarReplay.SparseCalendarRecord p.K) (hr : record ∈ s.buffer) :
    ∃ q : ℕ, q ≤ D p ∧ record.observation.val = (q : ℝ) / (D p : ℝ) :=
  h.2.2 record hr

/-- A saved observation can be retyped as the existing quantized observation
without changing its value or choosing a guessed replacement. -/
theorem localBufferValid_observation_typed {p : Parameters} {eta : LearningRate}
    {s : State p eta} (h : localBufferValid s)
    (record : SparseCalendarReplay.SparseCalendarRecord p.K) (hr : record ∈ s.buffer) :
    ∃ own : Observation p, own.val = record.observation := by
  obtain ⟨q, hq, hy⟩ := localBufferValid_observation_grid h record hr
  exact ⟨⟨record.observation, ⟨⟨q, by omega⟩, hy⟩⟩, rfl⟩

/-- The partial DOWN decoder's pending bound and completed-batch size domain. -/
def downDecoderStateValid {p : Parameters} {eta : LearningRate} (s : State p eta) : Prop :=
  s.downBatch.pending.length < AffineBatchDecoder.quota p ∧
  ∀ batch ∈ s.downBatch.completed, batch.length = AffineBatchDecoder.quota p

/-- Common carried-field domains. Accepted-record existence and start times
are checked separately in the applicable occupied branches. This predicate
does not assert zero initialization, authenticity, or physical reachability. -/
def localStateDomainValid {p : Parameters} {eta : LearningRate} (s : State p eta) : Prop :=
  serviceRegistersValid p s ∧ localBufferValid s ∧ downDecoderStateValid s

/-- Convert the accepted one-based start field to the cutoff scanner's
zero-based coordinate. The subtype proof is the existing DOWN admissibility
check. -/
def acceptedStartCoordinate {p : Parameters} {eta : LearningRate}
    (M : DownRecord (codecParams p eta)) : Fin p.T := by
  have h := M.property
  change 1 ≤ M.val.sigma ∧ M.val.sigma ≤ p.T ∧
    1 ≤ M.val.a ∧ M.val.a ≤ p.K ∧ 1 ≤ M.val.e ∧ M.val.e ≤ p.K ∧
    M.val.a ≠ M.val.e ∧ M.val.h ≤ (codecParams p eta).bN ∧
    (codecParams p eta).beta ≤ dyadicRate M.val.h ∧
    dyadicRate M.val.h ≤ 1 / ((16 : ℝ) * (p.m : ℝ) * (p.K : ℝ)) ∧
    M.val.q ≤ p.T * D p at h
  exact ⟨M.val.sigma - 1, by omega⟩

/-- Convert the accepted one-based escape arm to the action carrier. -/
def acceptedEscapeArm {p : Parameters} {eta : LearningRate}
    (M : DownRecord (codecParams p eta)) : Fin p.K := by
  have h := M.property
  change 1 ≤ M.val.sigma ∧ M.val.sigma ≤ p.T ∧
    1 ≤ M.val.a ∧ M.val.a ≤ p.K ∧ 1 ≤ M.val.e ∧ M.val.e ≤ p.K ∧
    M.val.a ≠ M.val.e ∧ M.val.h ≤ (codecParams p eta).bN ∧
    (codecParams p eta).beta ≤ dyadicRate M.val.h ∧
    dyadicRate M.val.h ≤ 1 / ((16 : ℝ) * (p.m : ℝ) * (p.K : ℝ)) ∧
    M.val.q ≤ p.T * D p at h
  exact ⟨M.val.e - 1, by omega⟩

/-- The accepted escape arm retains its literal one-based source label. -/
theorem accepted_escape_arm_one_based {p : Parameters} {eta : LearningRate}
    (M : DownRecord (codecParams p eta)) :
    (acceptedEscapeArm M).val + 1 = M.val.e := by
  have h := M.property
  simp only [downAdmissible] at h
  change M.val.e - 1 + 1 = M.val.e
  omega

/-- The accepted start coordinate retains its literal one-based source round. -/
theorem accepted_start_coordinate_one_based {p : Parameters} {eta : LearningRate}
    (M : DownRecord (codecParams p eta)) :
    (acceptedStartCoordinate M).val + 1 = M.val.sigma := by
  have h := M.property
  simp only [downAdmissible] at h
  change M.val.sigma - 1 + 1 = M.val.sigma
  omega

/-- Public fields of the current declared row used by the release test. -/
structure FollowerPublicRow (m K : ℕ) where
  slot : Slot
  selected : ActiveRoundActions.Follower m
  tuple : OrderedTupleSampler.Tuple m K
  pilots : Player m → Arm K

/-- Project exactly the public release-test fields from the accepted active
row carrier. Transport words, rewards, and other players' data are omitted. -/
def publicRowOfActionInput {m K B : ℕ} {a : Assignment m K}
    (r : RoundInput a B) : FollowerPublicRow m K :=
  ⟨r.slot, r.selected, r.tuple, r.pilots⟩

/-- Literal release coordinates from one supplied declared complete row. No
shared-row assumption or distribution is introduced by this projection. -/
noncomputable def publicRowOfCompleteRow {p : Parameters}
    (row : CompletePublicTable.CompleteRow p) (t : Fin p.T) :
    FollowerPublicRow p.m p.K where
  slot := slotDraw (row.2 t).1
  selected := selectedFollowerDraw p.two_le_m p.m_lt_K (row.2 t).1
  tuple := OrderedTupleSampler.sample p.two_le_m p.m_lt_K (row.2 t).1
  pilots := fun player => pilotDraw (K_pos p) player (row.2 t).1

/-- The literal UP or DATA arm-choice test for the accepted local record. -/
def releaseTests {p : Parameters} (eta : LearningRate)
    (i : ActiveRoundActions.Follower p.m) (row : FollowerPublicRow p.m p.K)
    (M : DownRecord (codecParams p eta)) : Prop :=
  (row.slot = upSlot ∧ row.selected = i ∧
      row.tuple.val (ActiveRoundActions.coordinator p.two_le_m) = acceptedEscapeArm M) ∨
    (row.slot = dataSlot ∧
      row.pilots (ActiveRoundActions.coordinator p.two_le_m) =
        Bandits.Support.PrelaunchBufferRecovery.downArm eta M)

/-- Release requires both one of the literal local arm tests and positive own
typed, quantized scalar feedback. -/
def releaseCondition {p : Parameters} (eta : LearningRate)
    (i : ActiveRoundActions.Follower p.m) (row : FollowerPublicRow p.m p.K)
    (own : Observation p) (M : DownRecord (codecParams p eta)) : Prop :=
  0 < own.val.val ∧ releaseTests eta i row M

/-- Expanded tests on the player's declared complete row: only own positive
feedback, UP/selected/escape-tuple, and DATA/assigned-pilot coordinates occur. -/
theorem releaseCondition_complete_row {p : Parameters} (eta : LearningRate)
    (i : ActiveRoundActions.Follower p.m) (t : Fin p.T)
    (row : CompletePublicTable.CompleteRow p) (own : Observation p)
    (M : DownRecord (codecParams p eta)) :
    releaseCondition eta i (publicRowOfCompleteRow row t) own M ↔
      0 < own.val.val ∧
        ((slotDraw (row.2 t).1 = upSlot ∧
          selectedFollowerDraw p.two_le_m p.m_lt_K (row.2 t).1 = i ∧
          (OrderedTupleSampler.sample p.two_le_m p.m_lt_K (row.2 t).1).val
            (ActiveRoundActions.coordinator p.two_le_m) = acceptedEscapeArm M) ∨
        (slotDraw (row.2 t).1 = dataSlot ∧
          pilotDraw (K_pos p) (ActiveRoundActions.coordinator p.two_le_m) (row.2 t).1 =
            Bandits.Support.PrelaunchBufferRecovery.downArm eta M)) :=
  Iff.rfl

/-- The release predicate does not inspect other players' tuple/pilot fields,
feedback magnitudes beyond positivity, words, or proposal bits. -/
theorem releaseCondition_noninterference {p : Parameters} (eta : LearningRate)
    (i : ActiveRoundActions.Follower p.m) (row row' : FollowerPublicRow p.m p.K)
    (own own' : Observation p) (M : DownRecord (codecParams p eta))
    (hslot : row.slot = row'.slot) (hselected : row.selected = row'.selected)
    (htuple : row.tuple.val (ActiveRoundActions.coordinator p.two_le_m) =
      row'.tuple.val (ActiveRoundActions.coordinator p.two_le_m))
    (hpilot : row.pilots (ActiveRoundActions.coordinator p.two_le_m) =
      row'.pilots (ActiveRoundActions.coordinator p.two_le_m))
    (hpositive : 0 < own.val.val ↔ 0 < own'.val.val) :
    releaseCondition eta i row own M ↔ releaseCondition eta i row' own' M := by
  simp only [releaseCondition, releaseTests, hslot, hselected, htuple, hpilot, hpositive]

noncomputable local instance {p : Parameters} (eta : LearningRate)
    (i : ActiveRoundActions.Follower p.m) (row : FollowerPublicRow p.m p.K)
    (own : Observation p) (M : DownRecord (codecParams p eta)) :
    Decidable (releaseCondition eta i row own M) := Classical.propDecidable _

/-- The local decision for `StartRound`. An occupied follower must have an
accepted record, must not have passed its grid endpoint unnoticed, and must
have the immediately preceding row's saved proposal token. -/
noncomputable def interruptionDecision {p : Parameters} (eta : LearningRate)
    (t : Fin p.T) (s : State p eta) (memory : LocalMemory p) :
    LifecycleCheck Bool := by
  classical
  if hregs : localStateDomainValid s then
    if hu : s.status = .unoccupied then
      exact .ok false
    else
      match s.lastDown with
      | none => exact .error .missingAcceptedDown
      | some M =>
        let sigma := acceptedStartCoordinate M
        let boundary := gridBoundary p eta.val sigma
        if hstarted : M.val.sigma ≤ t.val then
          if hnotmissed : t.val + 1 ≤ boundary then
            match memory.lastProposalRead with
            | none => exact .error .missingProposalRead
            | some token =>
              if hstamp : token.timestamp.val + 1 = t.val then
                exact .ok (boundary = t.val + 1 || token.bit)
              else exact .error .staleProposalRead
          else exact .error .missedGridBoundary
        else exact .error .incompatibleAcceptedDown
  else exact .error .invalidLocalStateDomain

/-- Beginning-of-round local interruption, before arm choice. It can only
change pending or released status to unoccupied; all other registers and the
one-bit memory are framed. -/
noncomputable def startRound {p : Parameters} (eta : LearningRate)
    (t : Fin p.T) (s : State p eta) (memory : LocalMemory p) :
    LifecycleCheck (State p eta × LocalMemory p) := do
  let interrupted ← interruptionDecision eta t s memory
  pure ({ s with status := if interrupted then .unoccupied else s.status }, memory)

/-- The proposal token required at the start of zero-based round `t` is the
token saved by coordinate `t-1`, exactly the prior calendar row. -/
def isPriorProposalRead {p : Parameters} (t : Fin p.T) (token : ProposalRead p) : Prop :=
  token.timestamp.val + 1 = t.val

/-- Apply pending-only release using the saved PRE-CHOICE state and the
separately supplied post-service state. No relation asserting a physical run
between these two arguments is bundled here. The accepted PRE-CHOICE start
must be at most `t.val`, by the earlier-round acceptance test of
`06_interruptions.tex:164-177`. The computed output is checked separately:
any occupied result must retain a record started by `t.val + 1`. In particular,
a passing test cannot manufacture an occupied output with no accepted record.
These checks do not assert equality of the two supplied records. -/
noncomputable def releaseAfterService {p : Parameters} (eta : LearningRate)
    (i : ActiveRoundActions.Follower p.m) (t : Fin p.T)
    (row : FollowerPublicRow p.m p.K) (own : Observation p)
    (preChoice postService : State p eta) : LifecycleCheck (State p eta) := by
  classical
  if hpending : preChoice.status = .pending then
    if hpreRegs : localStateDomainValid preChoice then
      match preChoice.lastDown with
      | none => exact .error .missingAcceptedDown
      | some M =>
        if hpreTime : M.val.sigma ≤ t.val then
          if hpostRegs : localStateDomainValid postService then
            let out := if releaseCondition eta i row own M then
              { postService with status := .released } else postService
            if houtputRecord : out.status = .unoccupied ∨
                (∃ M', out.lastDown = some M' ∧ M'.val.sigma ≤ t.val + 1) then
              exact .ok out
            else exact .error .incompatibleAcceptedDown
          else exact .error .invalidLocalStateDomain
        else exact .error .incompatibleAcceptedDown
    else exact .error .invalidLocalStateDomain
  else exact .ok postService

/-- End-of-round read of this row's actual proposal bit, and only while the
final follower status remains pending or released. -/
noncomputable def finishRound {p : Parameters} (eta : LearningRate)
    (t : Fin p.T) (row : CompletePublicTable.CompleteRow p)
    (s : State p eta) (memory : LocalMemory p) :
    LifecycleCheck (State p eta × LocalMemory p) := by
  classical
  if hregs : localStateDomainValid s then
    if hu : s.status = .unoccupied then
      exact .ok (s, memory)
    else
      match s.lastDown with
      | none => exact .error .missingAcceptedDown
      | some M =>
        if htime : M.val.sigma ≤ t.val + 1 then
          exact .ok (s, ⟨some ⟨t, completeRowProposalBit p eta.val row t⟩⟩)
        else exact .error .incompatibleAcceptedDown
  else exact .error .invalidLocalStateDomain

/-- Invalid carried-field domains are rejected before any interruption or
proposal-memory inspection. This includes duplicate keys and non-grid logs. -/
theorem interruptionDecision_invalid_domain {p : Parameters} (eta : LearningRate)
    (t : Fin p.T) (s : State p eta) (memory : LocalMemory p)
    (h : ¬ localStateDomainValid s) :
    interruptionDecision eta t s memory = .error .invalidLocalStateDomain := by
  simp only [interruptionDecision, dite_eq_right h]

/-- An unoccupied start round is a no-op and does not inspect proposal memory. -/
theorem interruptionDecision_unoccupied {p : Parameters} (eta : LearningRate)
    (t : Fin p.T) (s : State p eta) (memory : LocalMemory p)
    (hregs : localStateDomainValid s)
    (h : s.status = .unoccupied) :
    interruptionDecision eta t s memory = .ok false := by
  simp [interruptionDecision, hregs, h]

/-- Exact start-round equation on an unoccupied input, for arbitrary supplied
proposal memory. The partial decoder and all retained registers are untouched. -/
theorem startRound_unoccupied {p : Parameters} (eta : LearningRate)
    (t : Fin p.T) (s : State p eta) (memory : LocalMemory p)
    (hregs : localStateDomainValid s)
    (h : s.status = .unoccupied) :
    startRound eta t s memory = .ok (s, memory) := by
  cases s with
  | mk lastDown S delta backlog status downBatch buffer initializationFailure =>
    cases status <;> simp_all [startRound, interruptionDecision]

/-- A missing accepted DOWN record is a checked failure for an occupied
start-round input. -/
theorem interruptionDecision_missing_record {p : Parameters} (eta : LearningRate)
    (t : Fin p.T) (s : State p eta) (memory : LocalMemory p)
    (hstatus : s.status ≠ .unoccupied) (hregs : localStateDomainValid s)
    (hrecord : s.lastDown = none) :
    interruptionDecision eta t s memory = .error .missingAcceptedDown := by
  simp [interruptionDecision, hstatus, hregs, hrecord]

/-- A start not yet accepted by an earlier round is incompatible with an
occupied pre-choice state. -/
theorem interruptionDecision_incompatible_start {p : Parameters} (eta : LearningRate)
    (t : Fin p.T) (s : State p eta) (memory : LocalMemory p)
    (hstatus : s.status ≠ .unoccupied) (hregs : localStateDomainValid s)
    (M : DownRecord (codecParams p eta)) (hrecord : s.lastDown = some M)
    (htime : t.val < M.val.sigma) :
    interruptionDecision eta t s memory = .error .incompatibleAcceptedDown := by
  simp [interruptionDecision, hstatus, hregs, hrecord, Nat.not_le.mpr htime]

/-- A missed grid boundary is a checked failure, not a late guessed cutoff. -/
theorem interruptionDecision_missed_grid {p : Parameters} (eta : LearningRate)
    (t : Fin p.T) (s : State p eta) (memory : LocalMemory p)
    (hstatus : s.status ≠ .unoccupied) (hregs : localStateDomainValid s)
    (M : DownRecord (codecParams p eta)) (hrecord : s.lastDown = some M)
    (hstarted : M.val.sigma ≤ t.val)
    (hmissed : gridBoundary p eta.val (acceptedStartCoordinate M) < t.val + 1) :
    interruptionDecision eta t s memory = .error .missedGridBoundary := by
  simp [interruptionDecision, hstatus, hregs, hrecord, hstarted,
    Nat.not_le.mpr hmissed]

/-- Missing required prior proposal memory is a checked failure for an
otherwise compatible occupied input. -/
theorem interruptionDecision_missing_token {p : Parameters} (eta : LearningRate)
    (t : Fin p.T) (s : State p eta) (memory : LocalMemory p)
    (hstatus : s.status ≠ .unoccupied) (hregs : localStateDomainValid s)
    (M : DownRecord (codecParams p eta)) (hrecord : s.lastDown = some M)
    (hstarted : M.val.sigma ≤ t.val)
    (hnotmissed : t.val + 1 ≤ gridBoundary p eta.val (acceptedStartCoordinate M))
    (hread : memory.lastProposalRead = none) :
    interruptionDecision eta t s memory = .error .missingProposalRead := by
  simp [interruptionDecision, hstatus, hregs, hrecord, hstarted, hnotmissed, hread]

/-- A token with the wrong calendar timestamp is rejected rather than used as
a guessed interruption bit. -/
theorem interruptionDecision_stale_token {p : Parameters} (eta : LearningRate)
    (t : Fin p.T) (s : State p eta) (memory : LocalMemory p)
    (hstatus : s.status ≠ .unoccupied) (hregs : localStateDomainValid s)
    (M : DownRecord (codecParams p eta)) (hrecord : s.lastDown = some M)
    (hstarted : M.val.sigma ≤ t.val)
    (hnotmissed : t.val + 1 ≤ gridBoundary p eta.val (acceptedStartCoordinate M))
    (token : ProposalRead p) (hread : memory.lastProposalRead = some token)
    (hstale : ¬ isPriorProposalRead t token) :
    interruptionDecision eta t s memory = .error .staleProposalRead := by
  change token.timestamp.val + 1 ≠ t.val at hstale
  simp [interruptionDecision, hstatus, hregs, hrecord, hstarted, hnotmissed,
    hread, hstale]

/-- StartRound depends on the one-bit memory only through its sole stored
token. In particular it has no current-row or future-coordinate input. -/
theorem startRound_memory_noninterference {p : Parameters} (eta : LearningRate)
    (t : Fin p.T) (s : State p eta) (memory memory' : LocalMemory p)
    (h : memory.lastProposalRead = memory'.lastProposalRead) :
    startRound eta t s memory = startRound eta t s memory' := by
  cases memory with
  | mk token =>
    cases memory' with
    | mk token' =>
      simp only at h
      subst token'
      rfl

/-- StartRound does not clear the partial DOWN decoder, saved log buffer, or
accepted reply fields when a public interruption changes status. -/
theorem startRound_frame {p : Parameters} (eta : LearningRate)
    (t : Fin p.T) (s s' : State p eta) (memory memory' : LocalMemory p)
    (h : startRound eta t s memory = .ok (s', memory')) :
    s'.lastDown = s.lastDown ∧ s'.S = s.S ∧ s'.delta = s.delta ∧
      s'.backlog = s.backlog ∧ s'.downBatch = s.downBatch ∧
      s'.buffer = s.buffer ∧ s'.initializationFailure = s.initializationFailure ∧
      memory' = memory := by
  simp only [startRound] at h
  cases hd : interruptionDecision eta t s memory with
  | error e => simp [hd] at h
  | ok interrupted =>
    rw [hd] at h
    injection h with hpair
    cases hpair
    simp

/-- A successful occupied start round interrupts exactly at the grid boundary
or when its correctly timestamped saved prior proposal bit is true. -/
theorem startRound_occupied_branch {p : Parameters} (eta : LearningRate)
    (t : Fin p.T) (s : State p eta) (memory : LocalMemory p)
    (hstatus : s.status ≠ .unoccupied)
    (hregs : localStateDomainValid s)
    (M : DownRecord (codecParams p eta)) (hrecord : s.lastDown = some M)
    (hstarted : M.val.sigma ≤ t.val)
    (hnotmissed : t.val + 1 ≤ gridBoundary p eta.val (acceptedStartCoordinate M))
    (token : ProposalRead p) (hread : memory.lastProposalRead = some token)
    (hstamp : isPriorProposalRead t token) :
    startRound eta t s memory =
      .ok ({s with status := if gridBoundary p eta.val (acceptedStartCoordinate M) =
          t.val + 1 || token.bit then .unoccupied else s.status}, memory) := by
  change token.timestamp.val + 1 = t.val at hstamp
  have hdecision : interruptionDecision eta t s memory =
      .ok (gridBoundary p eta.val (acceptedStartCoordinate M) = t.val + 1 || token.bit) := by
    simp [interruptionDecision, hstatus, hregs, hrecord, hstarted, hnotmissed,
      hread, hstamp]
  simp [startRound, hdecision]

/-- The exact post-service branch for a pending pre-choice input. The accepted
record and positive typed feedback determine only the literal test; all other
post-service fields are preserved. -/
theorem releaseAfterService_pending_branch {p : Parameters} (eta : LearningRate)
    (i : ActiveRoundActions.Follower p.m) (t : Fin p.T)
    (row : FollowerPublicRow p.m p.K) (own : Observation p)
    (preChoice postService : State p eta)
    (hpending : preChoice.status = .pending)
    (hpreRegs : localStateDomainValid preChoice)
    (M : DownRecord (codecParams p eta)) (hrecord : preChoice.lastDown = some M)
    (htime : M.val.sigma ≤ t.val)
    (hpostRegs : localStateDomainValid postService)
    (hpostRecord : (¬ releaseCondition eta i row own M ∧
        postService.status = .unoccupied) ∨
      (∃ M', postService.lastDown = some M' ∧ M'.val.sigma ≤ t.val + 1)) :
    releaseAfterService eta i t row own preChoice postService =
      .ok (if releaseCondition eta i row own M then
        {postService with status := .released} else postService) := by
  classical
  by_cases htest : releaseCondition eta i row own M
  · have hrecordOut := hpostRecord.resolve_left (fun h => h.1 htest)
    simp [releaseAfterService, hpending, hpreRegs, hrecord, htime,
      hpostRegs, htest, hrecordOut]
  · have hrecordOut : postService.status = .unoccupied ∨
        (∃ M', postService.lastDown = some M' ∧ M'.val.sigma ≤ t.val + 1) :=
      hpostRecord.elim (fun h => Or.inl h.2) Or.inr
    simp [releaseAfterService, hpending, hpreRegs, hrecord, htime,
      hpostRegs, htest, hrecordOut]

/-- An unoccupied pre-choice state cannot release a just-accepted follower in
the same round: the release guard is read exclusively from pre-choice status. -/
theorem releaseAfterService_unoccupied {p : Parameters} (eta : LearningRate)
    (i : ActiveRoundActions.Follower p.m) (t : Fin p.T)
    (row : FollowerPublicRow p.m p.K) (own : Observation p)
    (preChoice postService : State p eta)
    (h : preChoice.status = .unoccupied) :
    releaseAfterService eta i t row own preChoice postService = .ok postService := by
  simp [releaseAfterService, h]

/-- The same no-op covers an already released pre-choice status. The unused
release branch does not inspect row coordinates or feedback. -/
theorem releaseAfterService_not_pending {p : Parameters} (eta : LearningRate)
    (i : ActiveRoundActions.Follower p.m) (t : Fin p.T)
    (row : FollowerPublicRow p.m p.K) (own : Observation p)
    (preChoice postService : State p eta) (h : preChoice.status ≠ .pending) :
    releaseAfterService eta i t row own preChoice postService = .ok postService := by
  simp [releaseAfterService, h]

/-- A pending pre-choice state requires an actual accepted DOWN record. -/
theorem releaseAfterService_missing_record {p : Parameters} (eta : LearningRate)
    (i : ActiveRoundActions.Follower p.m) (t : Fin p.T)
    (row : FollowerPublicRow p.m p.K) (own : Observation p)
    (preChoice postService : State p eta)
    (hpending : preChoice.status = .pending)
    (hpreRegs : localStateDomainValid preChoice) (hrecord : preChoice.lastDown = none) :
    releaseAfterService eta i t row own preChoice postService =
      .error .missingAcceptedDown := by
  simp [releaseAfterService, hpending, hpreRegs, hrecord]

/-- PRE-CHOICE starts later than the prior source round are checked failures,
regardless of the supplied post-state or a passing local release test. -/
theorem releaseAfterService_incompatible_start {p : Parameters} (eta : LearningRate)
    (i : ActiveRoundActions.Follower p.m) (t : Fin p.T)
    (row : FollowerPublicRow p.m p.K) (own : Observation p)
    (preChoice postService : State p eta)
    (hpending : preChoice.status = .pending)
    (hpreRegs : localStateDomainValid preChoice)
    (M : DownRecord (codecParams p eta)) (hrecord : preChoice.lastDown = some M)
    (htime : t.val < M.val.sigma) :
    releaseAfterService eta i t row own preChoice postService =
      .error .incompatibleAcceptedDown := by
  simp [releaseAfterService, hpending, hpreRegs, hrecord, Nat.not_le.mpr htime]

/-- The former off-by-one case is rejected: an assignment starting in the
current source round cannot already be pending at arm choice. The end-round
operation deliberately keeps its different `≤ t.val + 1` bound. -/
theorem releaseAfterService_current_round_start {p : Parameters} (eta : LearningRate)
    (i : ActiveRoundActions.Follower p.m) (t : Fin p.T)
    (row : FollowerPublicRow p.m p.K) (own : Observation p)
    (preChoice postService : State p eta)
    (hpending : preChoice.status = .pending)
    (hpreRegs : localStateDomainValid preChoice)
    (M : DownRecord (codecParams p eta)) (hrecord : preChoice.lastDown = some M)
    (htime : M.val.sigma = t.val + 1) :
    releaseAfterService eta i t row own preChoice postService =
      .error .incompatibleAcceptedDown := by
  apply releaseAfterService_incompatible_start eta i t row own preChoice postService
    hpending hpreRegs M hrecord
  omega

/-- A passing release test cannot create occupied status without a stored
accepted record in the output. This is an output-domain failure. -/
theorem releaseAfterService_missing_output_record {p : Parameters} (eta : LearningRate)
    (i : ActiveRoundActions.Follower p.m) (t : Fin p.T)
    (row : FollowerPublicRow p.m p.K) (own : Observation p)
    (preChoice postService : State p eta)
    (hpending : preChoice.status = .pending)
    (hpreRegs : localStateDomainValid preChoice)
    (M : DownRecord (codecParams p eta)) (hrecord : preChoice.lastDown = some M)
    (htime : M.val.sigma ≤ t.val) (hpostRegs : localStateDomainValid postService)
    (htest : releaseCondition eta i row own M) (hmissing : postService.lastDown = none) :
    releaseAfterService eta i t row own preChoice postService =
      .error .incompatibleAcceptedDown := by
  simp [releaseAfterService, hpending, hpreRegs, hrecord, htime, hpostRegs,
    htest, hmissing]

/-- Carried-field failures on the applicable pending release branch are
checked failures before the row test is evaluated. -/
theorem releaseAfterService_invalid_pre_domain {p : Parameters} (eta : LearningRate)
    (i : ActiveRoundActions.Follower p.m) (t : Fin p.T)
    (row : FollowerPublicRow p.m p.K) (own : Observation p)
    (preChoice postService : State p eta)
    (hpending : preChoice.status = .pending) (h : ¬ localStateDomainValid preChoice) :
    releaseAfterService eta i t row own preChoice postService =
      .error .invalidLocalStateDomain := by
  simp only [releaseAfterService, dite_eq_left hpending, dite_eq_right h]

/-- Release reads the supplied public row and own observation only through
the literal release predicate for the accepted PRE-CHOICE record. -/
theorem releaseAfterService_noninterference {p : Parameters} (eta : LearningRate)
    (i : ActiveRoundActions.Follower p.m) (t : Fin p.T)
    (row row' : FollowerPublicRow p.m p.K) (own own' : Observation p)
    (preChoice postService : State p eta)
    (htest : ∀ M, preChoice.lastDown = some M →
      (releaseCondition eta i row own M ↔ releaseCondition eta i row' own' M)) :
    releaseAfterService eta i t row own preChoice postService =
      releaseAfterService eta i t row' own' preChoice postService := by
  classical
  by_cases hpending : preChoice.status = .pending
  · cases hrecord : preChoice.lastDown with
    | none => simp [releaseAfterService, hpending, hrecord]
    | some M =>
      have heq := propext (htest M hrecord)
      simp only [releaseAfterService, hpending, hrecord, heq]
  · rw [releaseAfterService_not_pending eta i t row own preChoice postService hpending,
      releaseAfterService_not_pending eta i t row' own' preChoice postService hpending]

/-- A failed local release test preserves the post-service state as a success;
it does not create a checked failure or dagger transition. -/
theorem releaseAfterService_failed_test {p : Parameters} (eta : LearningRate)
    (i : ActiveRoundActions.Follower p.m) (t : Fin p.T)
    (row : FollowerPublicRow p.m p.K) (own : Observation p)
    (preChoice postService : State p eta)
    (hpending : preChoice.status = .pending)
    (hpreRegs : localStateDomainValid preChoice)
    (M : DownRecord (codecParams p eta)) (hrecord : preChoice.lastDown = some M)
    (htime : M.val.sigma ≤ t.val)
    (hpostRegs : localStateDomainValid postService)
    (hpostRecord : (¬ releaseCondition eta i row own M ∧
        postService.status = .unoccupied) ∨
      (∃ M', postService.lastDown = some M' ∧ M'.val.sigma ≤ t.val + 1))
    (hfailed : ¬ releaseCondition eta i row own M) :
    releaseAfterService eta i t row own preChoice postService = .ok postService := by
  rw [releaseAfterService_pending_branch eta i t row own preChoice postService
    hpending hpreRegs M hrecord htime hpostRegs hpostRecord]
  simp [hfailed]

/-- Pending release updates no accepted fields, queue/service values, decoder,
buffer, or initialization-failure flag, even when the supplied post-state is
otherwise unrelated to the pre-choice state. -/
theorem releaseAfterService_pending_frame {p : Parameters} (eta : LearningRate)
    (i : ActiveRoundActions.Follower p.m) (t : Fin p.T)
    (row : FollowerPublicRow p.m p.K) (own : Observation p)
    (preChoice postService out : State p eta)
    (hpending : preChoice.status = .pending)
    (hpreRegs : localStateDomainValid preChoice)
    (M : DownRecord (codecParams p eta)) (hrecord : preChoice.lastDown = some M)
    (htime : M.val.sigma ≤ t.val)
    (hpostRegs : localStateDomainValid postService)
    (hpostRecord : (¬ releaseCondition eta i row own M ∧
        postService.status = .unoccupied) ∨
      (∃ M', postService.lastDown = some M' ∧ M'.val.sigma ≤ t.val + 1))
    (hout : releaseAfterService eta i t row own preChoice postService = .ok out) :
    out.lastDown = postService.lastDown ∧ out.S = postService.S ∧
      out.delta = postService.delta ∧ out.backlog = postService.backlog ∧
      out.downBatch = postService.downBatch ∧ out.buffer = postService.buffer ∧
      out.initializationFailure = postService.initializationFailure := by
  rw [releaseAfterService_pending_branch eta i t row own preChoice postService
    hpending hpreRegs M hrecord htime hpostRegs hpostRecord] at hout
  injection hout with houtState
  subst out
  by_cases htest : releaseCondition eta i row own M <;> simp [htest]

/-- For arbitrary explicitly supplied post-service state, the resulting status
is released exactly when the local test passes or the supplied state was
already released. This records the operation's behavior without treating the
two state arguments as a physical run. -/
theorem releaseAfterService_status_formula {p : Parameters} (eta : LearningRate)
    (i : ActiveRoundActions.Follower p.m) (t : Fin p.T)
    (row : FollowerPublicRow p.m p.K) (own : Observation p)
    (preChoice postService : State p eta)
    (hpending : preChoice.status = .pending)
    (hpreRegs : localStateDomainValid preChoice)
    (M : DownRecord (codecParams p eta)) (hrecord : preChoice.lastDown = some M)
    (htime : M.val.sigma ≤ t.val)
    (hpostRegs : localStateDomainValid postService)
    (hpostRecord : (¬ releaseCondition eta i row own M ∧
        postService.status = .unoccupied) ∨
      (∃ M', postService.lastDown = some M' ∧ M'.val.sigma ≤ t.val + 1)) :
    (releaseAfterService eta i t row own preChoice postService).map
      (fun s => s.status = .released) =
        .ok (releaseCondition eta i row own M ∨ postService.status = .released) := by
  classical
  rw [releaseAfterService_pending_branch eta i t row own preChoice postService
    hpending hpreRegs M hrecord htime hpostRegs hpostRecord]
  by_cases hc : releaseCondition eta i row own M <;> simp [hc, Except.map]

/-- When the post-service status is pending, the operation changes it to
released if and only if the literal local feedback/arm tests pass. -/
theorem releaseAfterService_status_iff {p : Parameters} (eta : LearningRate)
    (i : ActiveRoundActions.Follower p.m) (t : Fin p.T)
    (row : FollowerPublicRow p.m p.K) (own : Observation p)
    (preChoice postService : State p eta)
    (hpending : preChoice.status = .pending)
    (hpreRegs : localStateDomainValid preChoice)
    (M : DownRecord (codecParams p eta)) (hrecord : preChoice.lastDown = some M)
    (htime : M.val.sigma ≤ t.val)
    (hpostRegs : localStateDomainValid postService)
    (hpostRecord : (¬ releaseCondition eta i row own M ∧
        postService.status = .unoccupied) ∨
      (∃ M', postService.lastDown = some M' ∧ M'.val.sigma ≤ t.val + 1))
    (hpostPending : postService.status = .pending) :
    (releaseAfterService eta i t row own preChoice postService).map
      (fun s => s.status = .released) =
        .ok (releaseCondition eta i row own M) := by
  rw [releaseAfterService_status_formula eta i t row own preChoice postService
    hpending hpreRegs M hrecord htime hpostRegs hpostRecord]
  simp [hpostPending]

/-- EndRound on an unoccupied state performs no proposal read and preserves
both the prior one-bit memory and every state field. -/
theorem finishRound_unoccupied {p : Parameters} (eta : LearningRate)
    (t : Fin p.T) (row : CompletePublicTable.CompleteRow p)
    (s : State p eta) (memory : LocalMemory p)
    (hregs : localStateDomainValid s)
    (h : s.status = .unoccupied) :
    finishRound eta t row s memory = .ok (s, memory) := by
  simp [finishRound, hregs, h]

/-- Invalid carried fields fail before the end-round proposal read. -/
theorem finishRound_invalid_domain {p : Parameters} (eta : LearningRate)
    (t : Fin p.T) (row : CompletePublicTable.CompleteRow p)
    (s : State p eta) (memory : LocalMemory p) (h : ¬ localStateDomainValid s) :
    finishRound eta t row s memory = .error .invalidLocalStateDomain := by
  simp only [finishRound, dite_eq_right h]

/-- An occupied end-round state cannot read without a stored accepted DOWN. -/
theorem finishRound_missing_record {p : Parameters} (eta : LearningRate)
    (t : Fin p.T) (row : CompletePublicTable.CompleteRow p)
    (s : State p eta) (memory : LocalMemory p)
    (hstatus : s.status ≠ .unoccupied) (hregs : localStateDomainValid s)
    (hrecord : s.lastDown = none) :
    finishRound eta t row s memory = .error .missingAcceptedDown := by
  simp [finishRound, hstatus, hregs, hrecord]

/-- The POST-update guard permits a start in this round, but rejects a start
later than this round. It is deliberately different from the pre-choice guard. -/
theorem finishRound_incompatible_start {p : Parameters} (eta : LearningRate)
    (t : Fin p.T) (row : CompletePublicTable.CompleteRow p)
    (s : State p eta) (memory : LocalMemory p)
    (hstatus : s.status ≠ .unoccupied) (hregs : localStateDomainValid s)
    (M : DownRecord (codecParams p eta)) (hrecord : s.lastDown = some M)
    (htime : t.val + 1 < M.val.sigma) :
    finishRound eta t row s memory = .error .incompatibleAcceptedDown := by
  simp [finishRound, hstatus, hregs, hrecord, Nat.not_le.mpr htime]

/-- Changing the current row cannot affect an unoccupied EndRound, since its
branch does not read `B_t`. -/
theorem finishRound_unoccupied_noninterference {p : Parameters} (eta : LearningRate)
    (t : Fin p.T) (row row' : CompletePublicTable.CompleteRow p)
    (s : State p eta) (memory : LocalMemory p)
    (hregs : localStateDomainValid s)
    (h : s.status = .unoccupied) :
    finishRound eta t row s memory = finishRound eta t row' s memory := by
  rw [finishRound_unoccupied eta t row s memory hregs h,
    finishRound_unoccupied eta t row' s memory hregs h]

/-- A successful occupied EndRound saves precisely this row's actual scanned
proposal bit at this row's timestamp. -/
theorem finishRound_occupied_read {p : Parameters} (eta : LearningRate)
    (t : Fin p.T) (row : CompletePublicTable.CompleteRow p)
    (s : State p eta) (memory : LocalMemory p)
    (hstatus : s.status ≠ .unoccupied)
    (hregs : localStateDomainValid s)
    (M : DownRecord (codecParams p eta)) (hrecord : s.lastDown = some M)
    (htime : M.val.sigma ≤ t.val + 1) :
    finishRound eta t row s memory =
      .ok (s, ⟨some ⟨t, completeRowProposalBit p eta.val row t⟩⟩) := by
  simp [finishRound, hstatus, hregs, hrecord, htime]

/-- Every successful end-round proposal read frames the entire follower state,
including the buffer and partial DOWN batch. Only proposal memory can change. -/
theorem finishRound_frame {p : Parameters} (eta : LearningRate)
    (t : Fin p.T) (row : CompletePublicTable.CompleteRow p)
    (s s' : State p eta) (memory memory' : LocalMemory p)
    (hout : finishRound eta t row s memory = .ok (s', memory')) : s' = s := by
  classical
  by_cases hregs : localStateDomainValid s
  · by_cases hu : s.status = .unoccupied
    · rw [finishRound_unoccupied eta t row s memory hregs hu] at hout
      exact (Prod.mk.inj (Except.ok.inj hout)).1.symm
    · cases hrecord : s.lastDown with
      | none => simp [finishRound, hregs, hu, hrecord] at hout
      | some M =>
        by_cases htime : M.val.sigma ≤ t.val + 1
        · rw [finishRound_occupied_read eta t row s memory hu hregs M hrecord htime]
            at hout
          exact (Prod.mk.inj (Except.ok.inj hout)).1.symm
        · simp [finishRound, hregs, hu, hrecord, htime] at hout
  · rw [finishRound_invalid_domain eta t row s memory hregs] at hout
    cases hout

/-- On an occupied final state, changing any other coordinate of the declared
row while keeping its actual `B_t` token fixed cannot affect EndRound. -/
theorem finishRound_occupied_noninterference {p : Parameters} (eta : LearningRate)
    (t : Fin p.T) (row row' : CompletePublicTable.CompleteRow p)
    (s : State p eta) (memory : LocalMemory p)
    (hstatus : s.status ≠ .unoccupied)
    (hregs : localStateDomainValid s)
    (M : DownRecord (codecParams p eta)) (hrecord : s.lastDown = some M)
    (htime : M.val.sigma ≤ t.val + 1)
    (hbit : completeRowProposalBit p eta.val row t =
      completeRowProposalBit p eta.val row' t) :
    finishRound eta t row s memory = finishRound eta t row' s memory := by
  rw [finishRound_occupied_read eta t row s memory hstatus hregs M hrecord htime,
    finishRound_occupied_read eta t row' s memory hstatus hregs M hrecord htime]
  rw [hbit]

/-- The release tests agree with `ActiveRoundActions.releaseObservation` when
the accepted record is the live assignment's follower arm and auxiliary arm,
and the supplied quantized scalar is the corresponding physical feedback. -/
theorem releaseCondition_eq_activeRoundActions {p : Parameters} (eta : LearningRate)
    {B : ℕ} (a : ActiveRoundActions.Assignment p.m p.K)
    (snapshot : ActiveRoundActions.Snapshot a)
    (r : ActiveRoundActions.RoundInput a B)
    (reward : ActiveRoundActions.RewardRow p.K)
    (i : ActiveRoundActions.Follower p.m)
    (M : DownRecord (codecParams p eta)) (own : Observation p)
    (hassigned : a.assigned i =
      Bandits.Support.PrelaunchBufferRecovery.downArm eta M)
    (hauxiliary : a.auxiliary = acceptedEscapeArm M)
    (hfeedback : own.val.val = ActiveRoundActions.feedback p.two_le_m snapshot r
      reward (followerPlayer p.two_le_m i)) :
    releaseCondition eta i (publicRowOfActionInput r) own M =
      ActiveRoundActions.releaseObservation p.two_le_m snapshot r reward i := by
  classical
  simp only [publicRowOfActionInput]
  unfold releaseCondition releaseTests ActiveRoundActions.releaseObservation
  rw [hfeedback, hassigned, hauxiliary]

end Bandits.Support.ActiveFollowerLifecycle
