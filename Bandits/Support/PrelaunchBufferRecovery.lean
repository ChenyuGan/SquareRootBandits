/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.List.Intervals
public import Bandits.Support.QueueReplay
public import Bandits.Support.SparseCalendarReplay
public import Bandits.Support.ReferencePrelaunchFollower
public import Bandits.Support.OrdinaryMessageCodec

import Bandits.Support.QueueTraceConservation
import Lean.Elab.Tactic.Omega

/-!
# Recovery from the integrated prelaunch follower buffer

This module connects the actual finite replay buffer from
`ReferencePrelaunchFollower` to sparse arrival recovery and integer queue
replay. The logging fields follow
`sources/zip4/manuscript/06_interruptions.tex:192-233`, the saved contribution
is `sources/zip4/manuscript/05_binary_transport.tex:428-431`, the queue update
is `sources/zip4/manuscript/04_slow_fast_learner.tex:158-174`, the accepted-DOWN
recovery step is `sources/zip4/manuscript/06_interruptions.tex:270-275`, and
the prelaunch rejection rule is
`sources/zip4/manuscript/07_public_setup.tex:129-140`. Launch preservation
follows `sources/zip4/manuscript/appendix_b_communication.tex:737-744`.

The input history is exactly the supplied finite prefix through decision round
`t`; all recovery indices are proof-carrying members of its valid calendar
interval. The supplied admissible DOWN record and its interval bounds do not
certify message authenticity, currentness, a physical reference run, or a
correspondence with `CanonicalQueueProcess`.
-/

public section

namespace Bandits.Support.PrelaunchBufferRecovery

open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.OrdinaryMessageCodec
open Bandits.Support.SparseCalendarReplay

theorem down_sigma_pos {p : ConstructorDimensions.Parameters}
    (eta : LearningRate) (M : DownRecord (codecParams p eta)) :
    1 ≤ M.val.sigma := by
  have h := M.property
  simp only [downAdmissible] at h
  exact h.1

/-- Convert the one-based arm in an admissible DOWN record to the existing
zero-based finite arm carrier. -/
@[expose] def downArm {p : ConstructorDimensions.Parameters} (eta : LearningRate)
    (M : DownRecord (codecParams p eta)) : Fin p.K := by
  have h := M.property
  simp only [downAdmissible] at h
  have ha : 1 ≤ M.val.a := h.2.2.1
  have haK : M.val.a ≤ p.K := h.2.2.2.1
  exact ⟨M.val.a - 1, by omega⟩

/-- The finite-arm conversion is exactly the source's one-based arm index. -/
theorem down_arm_one_based {p : ConstructorDimensions.Parameters} (eta : LearningRate)
    (M : DownRecord (codecParams p eta)) :
    (downArm eta M).val + 1 = M.val.a := by
  have h := M.property
  simp only [downAdmissible] at h
  have ha : 1 ≤ M.val.a := h.2.2.1
  have hval : (downArm eta M).val = M.val.a - 1 := by
    simp [downArm]
  rw [hval]
  omega

/-- The existing `ReferencePrelaunchFollower.replay`, instantiated on the
supplied history through the zero-based decision index `t`. -/
@[expose] noncomputable def prefixState {p : ConstructorDimensions.Parameters} (eta : LearningRate)
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (alpha : Activation p) (t : Fin p.T)
    (history : LocalHistory p (t.val + 1)) : State p eta :=
  ReferencePrelaunchFollower.replay eta i row alpha history (by omega)

/-- The actual saved-list contribution at source calendar round `r`, evaluated
on the buffer built by the existing finite follower replay. -/
@[expose] noncomputable def bufferArrival {p : ConstructorDimensions.Parameters}
    (eta : LearningRate) (i : Fin (p.m - 1))
    (row : CompletePublicTable.CompleteRow p) (alpha : Activation p)
    (t : Fin p.T) (history : LocalHistory p (t.val + 1))
    (M : DownRecord (codecParams p eta)) (r : ℕ) : ℕ :=
  SparseCalendarReplay.sparseBufferContribution (p.m - 1) (ConstructorDimensions.D p)
    eta.val M.val.h (downArm eta M) r
    (prefixState eta i row alpha t history).buffer

/-- The chronological finite list of source rounds in `[sigma, ell)`. -/
@[expose] def recoveryRounds (sigma ell : ℕ) : List ℕ :=
  List.Ico sigma ell

/-- A round together with its proof that it belongs to the scanned interval. -/
abbrev RecoveryRound (sigma ell : ℕ) :=
  {r : ℕ // r ∈ recoveryRounds sigma ell}

/-- Turn a valid one-based calendar round into the matching finite supplied
history index. The proof arguments prevent off-domain reads. -/
@[expose] def historyIndex {p : ConstructorDimensions.Parameters} (eta : LearningRate)
    (t : Fin p.T) (M : DownRecord (codecParams p eta)) (sigma ell : ℕ)
    (hsigma : M.val.sigma ≤ sigma) (hell : ell ≤ t.val + 2)
    (r : RecoveryRound sigma ell) : Fin (t.val + 1) := by
  have hrange : sigma ≤ r.val ∧ r.val < ell := by
    simpa only [recoveryRounds, List.Ico.mem] using r.property
  have hsig := down_sigma_pos eta M
  exact ⟨r.val - 1, by omega⟩

/-- The finite index and one-based source calendar stamp agree. -/
theorem history_index_round {p : ConstructorDimensions.Parameters} (eta : LearningRate)
    (t : Fin p.T) (M : DownRecord (codecParams p eta)) (sigma ell : ℕ)
    (hsigma : M.val.sigma ≤ sigma) (hell : ell ≤ t.val + 2)
    (r : RecoveryRound sigma ell) :
    (historyIndex eta t M sigma ell hsigma hell r).val + 1 = r.val := by
  have hrange : sigma ≤ r.val ∧ r.val < ell := by
    simpa only [recoveryRounds, List.Ico.mem] using r.property
  have hsig := down_sigma_pos eta M
  simp only [historyIndex]
  omega

/-- The one-round direct arrival: the exact logging-test and selected-arm
indicator multiplied once by the existing saved-contribution function. -/
@[expose] noncomputable def oneRoundArrival {p : ConstructorDimensions.Parameters}
    (eta : LearningRate) (i : Fin (p.m - 1))
    (row : CompletePublicTable.CompleteRow p) (alpha : Activation p)
    (t : Fin p.T) (history : LocalHistory p (t.val + 1))
    (M : DownRecord (codecParams p eta)) (u : Fin (t.val + 1)) : ℕ := by
  classical
  exact (if loggingTestsPass
      (ReferencePrelaunchFollower.loggingRound i row alpha
        (ReferencePrelaunchFollower.calendar (by omega) u) (history u)) ∧
      (history u).1 = downArm eta M then 1 else 0) *
    SparseCalendarReplay.savedContribution p.K (p.m - 1) (ConstructorDimensions.D p)
      eta.val M.val.h (history u).2.val
      ((row.2 (ReferencePrelaunchFollower.calendar (by omega) u)).1
        ContinuousControlSlice.Label.thin)

/-- Every scanned round is fed to the existing integer queue as an enabled
record, even when the actual sparse buffer yields zero arrival. -/
@[expose] noncomputable def bufferQueueRecords {p : ConstructorDimensions.Parameters}
    (eta : LearningRate) (i : Fin (p.m - 1))
    (row : CompletePublicTable.CompleteRow p) (alpha : Activation p)
    (t : Fin p.T) (history : LocalHistory p (t.val + 1))
    (M : DownRecord (codecParams p eta)) (sigma ell : ℕ) : List (Bool × ℕ) :=
  (recoveryRounds sigma ell).map (fun r =>
    (true, bufferArrival eta i row alpha t history M r))

/-- The direct one-round indicator records over the same valid interval.
`attach` carries the range proof used to index only the supplied finite
history. -/
@[expose] noncomputable def directQueueRecords {p : ConstructorDimensions.Parameters}
    (eta : LearningRate) (i : Fin (p.m - 1))
    (row : CompletePublicTable.CompleteRow p) (alpha : Activation p)
    (t : Fin p.T) (history : LocalHistory p (t.val + 1))
    (M : DownRecord (codecParams p eta)) (sigma ell : ℕ)
    (hsigma : M.val.sigma ≤ sigma) (hell : ell ≤ t.val + 2) : List (Bool × ℕ) :=
  (recoveryRounds sigma ell).attach.map (fun r =>
    (true, oneRoundArrival eta i row alpha t history M
      (historyIndex eta t M sigma ell hsigma hell r)))

/-- The one-round arrivals from the actual log list on valid source rounds. -/
@[expose] noncomputable def bufferArrivalList {p : ConstructorDimensions.Parameters}
    (eta : LearningRate) (i : Fin (p.m - 1))
    (row : CompletePublicTable.CompleteRow p) (alpha : Activation p)
    (t : Fin p.T) (history : LocalHistory p (t.val + 1))
    (M : DownRecord (codecParams p eta)) (sigma ell : ℕ) : List ℕ :=
  (recoveryRounds sigma ell).map (bufferArrival eta i row alpha t history M)

/-- Every source calendar index in the scan satisfies the half-open interval
bounds. -/
theorem recovery_rounds_mem_bounds (sigma ell r : ℕ)
    (hr : r ∈ recoveryRounds sigma ell) : sigma ≤ r ∧ r < ell := by
  simpa only [recoveryRounds, List.Ico.mem] using hr

section BufferFoldLemmas

noncomputable local instance (P : Prop) : Decidable P := Classical.propDecidable P

private theorem sparseBufferContribution_eq_singleton_of_nodup {K : ℕ}
    (d : ℕ) (D eta : ℝ) (h : ℕ) (arm : Fin K) (r : ℕ)
    (buffer : List (SparseCalendarRecord K)) (target : SparseCalendarRecord K)
    (hnodup : buffer.Nodup) (htargetRound : target.calendarRound = r)
    (htargetPilot : target.pilot = arm)
    (hmatch : ∀ record ∈ buffer, record.calendarRound = r → record.pilot = arm →
      record = target) :
    SparseCalendarReplay.sparseBufferContribution d D eta h arm r buffer =
      if target ∈ buffer then
        SparseCalendarReplay.savedContribution K d D eta h
          target.observation target.thinScalar else 0 := by
  classical
  induction buffer with
  | nil => simp [SparseCalendarReplay.sparseBufferContribution]
  | cons record tail ih =>
    have hnodup' := List.nodup_cons.mp hnodup
    have hmatch' : ∀ b ∈ tail, b.calendarRound = r → b.pilot = arm → b = target := by
      intro b hb hround hp
      exact hmatch b (List.mem_cons_of_mem _ hb) hround hp
    have htail := ih hnodup'.2 hmatch'
    change (if record.calendarRound = r ∧ record.pilot = arm then
        SparseCalendarReplay.savedContribution K d D eta h
          record.observation record.thinScalar else 0) +
        SparseCalendarReplay.sparseBufferContribution d D eta h arm r tail =
      if target ∈ record :: tail then
        SparseCalendarReplay.savedContribution K d D eta h
          target.observation target.thinScalar else 0
    by_cases hrecord : record.calendarRound = r ∧ record.pilot = arm
    · have heq := hmatch record (by simp) hrecord.1 hrecord.2
      subst record
      have htailzero :
          SparseCalendarReplay.sparseBufferContribution d D eta h arm r tail = 0 := by
        rw [htail]
        simp [hnodup'.1]
      rw [htailzero]
      simp [htargetRound, htargetPilot, hnodup'.1]
    · have hne : record ≠ target := by
        intro heq
        subst record
        exact hrecord ⟨htargetRound, htargetPilot⟩
      rw [htail]
      simp [hrecord, Ne.symm hne]

private theorem sparseBufferContribution_eq_zero_of_no_matching_record {K : ℕ}
    (d : ℕ) (D eta : ℝ) (h : ℕ) (arm : Fin K) (r : ℕ)
    (buffer : List (SparseCalendarRecord K))
    (hno : ∀ record ∈ buffer,
      ¬ (record.calendarRound = r ∧ record.pilot = arm)) :
    SparseCalendarReplay.sparseBufferContribution d D eta h arm r buffer = 0 := by
  classical
  induction buffer with
  | nil => simp [SparseCalendarReplay.sparseBufferContribution]
  | cons record tail ih =>
    have hhead := hno record (by simp)
    have htail : ∀ b ∈ tail, ¬ (b.calendarRound = r ∧ b.pilot = arm) := by
      intro b hb
      exact hno b (List.mem_cons_of_mem _ hb)
    change (if record.calendarRound = r ∧ record.pilot = arm then
        SparseCalendarReplay.savedContribution K d D eta h
          record.observation record.thinScalar else 0) +
        SparseCalendarReplay.sparseBufferContribution d D eta h arm r tail = 0
    rw [ih htail]
    simp [hhead]

end BufferFoldLemmas

/-- The actual buffer contribution at any scanned round is exactly its actual
one-round logging-test indicator times `savedContribution`. Logging does not
test observation positivity and performs no thinning; thinning occurs exactly
once, inside the existing `savedContribution`. -/
theorem buffer_arrival_eq_one_round {p : ConstructorDimensions.Parameters}
    (eta : LearningRate) (i : Fin (p.m - 1))
    (row : CompletePublicTable.CompleteRow p) (alpha : Activation p)
    (t : Fin p.T) (history : LocalHistory p (t.val + 1))
    (M : DownRecord (codecParams p eta)) (sigma ell : ℕ)
    (hsigma : M.val.sigma ≤ sigma) (hell : ell ≤ t.val + 2)
    (r : RecoveryRound sigma ell) :
    bufferArrival eta i row alpha t history M r.val =
      oneRoundArrival eta i row alpha t history M
        (historyIndex eta t M sigma ell hsigma hell r) := by
  classical
  let u := historyIndex eta t M sigma ell hsigma hell r
  let snap := ReferencePrelaunchFollower.loggingRound i row alpha
    (ReferencePrelaunchFollower.calendar (by omega) u) (history u)
  let target := SparseCalendarReplay.recordAt r.val snap
  have hround : u.val + 1 = r.val := by
    exact history_index_round eta t M sigma ell hsigma hell r
  have hpair := ReferencePrelaunchFollower.replay_buffer_pairwise eta i row alpha history
    (by omega)
  have hnodup : (prefixState eta i row alpha t history).buffer.Nodup := by
    have hne : List.Pairwise (fun a b : SparseCalendarRecord p.K => a ≠ b)
        (prefixState eta i row alpha t history).buffer := by
      apply hpair.imp
      intro a b hab heq
      have h' := congrArg (fun x : SparseCalendarRecord p.K => x.calendarRound) heq
      omega
    exact hne.nodup
  have hmatch : ∀ a ∈ (prefixState eta i row alpha t history).buffer,
      a.calendarRound = r.val → a.pilot = downArm eta M → a = target := by
    intro a ha haround hapilot
    obtain ⟨v, hvlog, hva⟩ :=
      (ReferencePrelaunchFollower.replay_buffer_mem_iff eta i row alpha history
        (by omega) a).mp ha
    have hstamp : a.calendarRound = v.val + 1 := by
      simpa only [SparseCalendarReplay.recordAt] using
        congrArg SparseCalendarRecord.calendarRound hva
    have hvround : v.val + 1 = r.val := by omega
    have hvu : v = u := by
      apply Fin.ext
      omega
    subst v
    have htarget : target ∈ (prefixState eta i row alpha t history).buffer :=
      (ReferencePrelaunchFollower.replay_buffer_mem_iff eta i row alpha history
        (by omega) target).mpr ⟨u, hvlog, by
          simp [target, snap, SparseCalendarReplay.recordAt, hround]⟩
    have hsameRound : a.calendarRound = target.calendarRound := by
      simpa [target, SparseCalendarReplay.recordAt] using haround
    exact ReferencePrelaunchFollower.replay_buffer_unique_round eta i row alpha history
      (by omega) ha htarget hsameRound
  have hmem : target ∈ (prefixState eta i row alpha t history).buffer ↔
      loggingTestsPass snap := by
    constructor
    · intro htarget
      obtain ⟨v, hvlog, hva⟩ :=
        (ReferencePrelaunchFollower.replay_buffer_mem_iff eta i row alpha history
          (by omega) target).mp htarget
      have hvround : v.val + 1 = r.val := by
        simpa [target, SparseCalendarReplay.recordAt] using
          congrArg SparseCalendarRecord.calendarRound hva.symm
      have hvu : v = u := by
        apply Fin.ext
        omega
      subst v
      exact hvlog
    · intro hlog
      exact (ReferencePrelaunchFollower.replay_buffer_mem_iff eta i row alpha history
        (by omega) target).mpr ⟨u, hlog, by
          simp [target, snap, SparseCalendarReplay.recordAt, hround]⟩
  by_cases harm : (history u).1 = downArm eta M
  · have htargetPilot : target.pilot = downArm eta M := by
      simp [target, SparseCalendarReplay.recordAt, snap,
        ReferencePrelaunchFollower.loggingRound, harm]
    have htargetRound : target.calendarRound = r.val := by
      simp [target, SparseCalendarReplay.recordAt]
    have hcontribution :=
      sparseBufferContribution_eq_singleton_of_nodup
        (d := p.m - 1) (D := ConstructorDimensions.D p) (eta := eta.val)
        (h := M.val.h) (arm := downArm eta M) (r := r.val)
        (buffer := (prefixState eta i row alpha t history).buffer)
        (target := target) hnodup htargetRound htargetPilot hmatch
    change SparseCalendarReplay.sparseBufferContribution (p.m - 1)
        (ConstructorDimensions.D p) eta.val M.val.h (downArm eta M) r.val
        (prefixState eta i row alpha t history).buffer = _
    rw [hcontribution]
    have hsave :
        SparseCalendarReplay.savedContribution p.K (p.m - 1) (ConstructorDimensions.D p)
          eta.val M.val.h target.observation target.thinScalar =
        SparseCalendarReplay.savedContribution p.K (p.m - 1) (ConstructorDimensions.D p)
          eta.val M.val.h (history u).2.val
          ((row.2 (ReferencePrelaunchFollower.calendar (by omega) u)).1
            ContinuousControlSlice.Label.thin) := by
      simp [target, snap, SparseCalendarReplay.recordAt,
        ReferencePrelaunchFollower.loggingRound]
    change (if target ∈ (prefixState eta i row alpha t history).buffer then
        SparseCalendarReplay.savedContribution p.K (p.m - 1)
          (ConstructorDimensions.D p) eta.val M.val.h target.observation target.thinScalar
        else 0) =
      (if loggingTestsPass snap ∧ (history u).1 = downArm eta M then 1 else 0) *
        SparseCalendarReplay.savedContribution p.K (p.m - 1)
          (ConstructorDimensions.D p) eta.val M.val.h (history u).2.val
          ((row.2 (ReferencePrelaunchFollower.calendar (by omega) u)).1
            ContinuousControlSlice.Label.thin)
    by_cases hlog : loggingTestsPass snap
    · have htargetmem := hmem.mpr hlog
      simp [htargetmem, hlog, harm, hsave]
    · have htargetnot : target ∉ (prefixState eta i row alpha t history).buffer := by
        intro htargetmem
        exact hlog (hmem.mp htargetmem)
      simp [htargetnot, hlog, harm]
  · have hnomatch : ∀ a ∈ (prefixState eta i row alpha t history).buffer,
      ¬ (a.calendarRound = r.val ∧ a.pilot = downArm eta M) := by
      intro a ha hfields
      have hsame := hmatch a ha hfields.1 hfields.2
      have hpilot : target.pilot = (history u).1 := by
        simp [target, SparseCalendarReplay.recordAt, snap,
          ReferencePrelaunchFollower.loggingRound]
      have hown : (history u).1 = downArm eta M := by
        have hp : target.pilot = downArm eta M := by
          rw [← hsame]
          exact hfields.2
        exact hpilot.symm.trans hp
      exact harm hown
    have hzero := sparseBufferContribution_eq_zero_of_no_matching_record
      (d := p.m - 1) (D := ConstructorDimensions.D p) (eta := eta.val)
      (h := M.val.h) (arm := downArm eta M) (r := r.val)
      (buffer := (prefixState eta i row alpha t history).buffer) hnomatch
    rw [bufferArrival, hzero]
    simp [oneRoundArrival, u, harm]

/-- A saved zero-observation record remains in the actual buffer and its
existing saved contribution evaluates to zero without a positivity filter. -/
theorem logged_zero_observation_is_retained {p : ConstructorDimensions.Parameters}
    (eta : LearningRate) (i : Fin (p.m - 1))
    (row : CompletePublicTable.CompleteRow p) (alpha : Activation p)
    (t : Fin p.T) (history : LocalHistory p (t.val + 1))
    (M : DownRecord (codecParams p eta)) (u : Fin (t.val + 1))
    (hlog : loggingTestsPass
      (ReferencePrelaunchFollower.loggingRound i row alpha
        (ReferencePrelaunchFollower.calendar (by omega) u) (history u)))
    (hzero : (history u).2.val.1 = 0) :
    SparseCalendarReplay.recordAt (u.val + 1)
        (ReferencePrelaunchFollower.loggingRound i row alpha
          (ReferencePrelaunchFollower.calendar (by omega) u) (history u)) ∈
      (prefixState eta i row alpha t history).buffer ∧
    SparseCalendarReplay.savedContribution p.K (p.m - 1) (ConstructorDimensions.D p)
      eta.val M.val.h (history u).2.val
      ((row.2 (ReferencePrelaunchFollower.calendar (by omega) u)).1
        ContinuousControlSlice.Label.thin) = 0 := by
  refine ⟨?_, ?_⟩
  · exact (ReferencePrelaunchFollower.replay_buffer_mem_iff eta i row alpha history
      (by omega) _).mpr ⟨u, hlog, rfl⟩
  · simp [SparseCalendarReplay.savedContribution, hzero]

/-- The queue list has one enabled entry per integer in `[sigma, ell)`,
including rounds with no matching saved record. -/
theorem buffer_queue_records_all_enabled {p : ConstructorDimensions.Parameters}
    (eta : LearningRate) (i : Fin (p.m - 1))
    (row : CompletePublicTable.CompleteRow p) (alpha : Activation p)
    (t : Fin p.T) (history : LocalHistory p (t.val + 1))
    (M : DownRecord (codecParams p eta)) (sigma ell : ℕ) :
    ∀ record ∈ bufferQueueRecords eta i row alpha t history M sigma ell,
      record.1 = true := by
  intro record hrecord
  rcases List.mem_map.mp hrecord with ⟨r, _, rfl⟩
  rfl

/-- Every queue entry comes from one calendar index in the requested
half-open interval, so saved records outside it are never replayed. -/
theorem buffer_queue_records_entries_in_interval {p : ConstructorDimensions.Parameters}
    (eta : LearningRate) (i : Fin (p.m - 1))
    (row : CompletePublicTable.CompleteRow p) (alpha : Activation p)
    (t : Fin p.T) (history : LocalHistory p (t.val + 1))
    (M : DownRecord (codecParams p eta)) (sigma ell : ℕ) :
    ∀ record ∈ bufferQueueRecords eta i row alpha t history M sigma ell,
      ∃ r, sigma ≤ r ∧ r < ell ∧
        record = (true, bufferArrival eta i row alpha t history M r) := by
  intro record hrecord
  obtain ⟨r, hr, hrecord⟩ := List.mem_map.mp hrecord
  subst record
  obtain ⟨hlo, hhi⟩ := recovery_rounds_mem_bounds sigma ell r hr
  exact ⟨r, hlo, hhi, rfl⟩

/-- The queue list length is exactly the number of calendar rounds in the
source interval. -/
theorem buffer_queue_records_length {p : ConstructorDimensions.Parameters}
    (eta : LearningRate) (i : Fin (p.m - 1))
    (row : CompletePublicTable.CompleteRow p) (alpha : Activation p)
    (t : Fin p.T) (history : LocalHistory p (t.val + 1))
    (M : DownRecord (codecParams p eta)) (sigma ell : ℕ) :
    (bufferQueueRecords eta i row alpha t history M sigma ell).length = ell - sigma := by
  simp [bufferQueueRecords, recoveryRounds]

/-- The actual-buffer arrival list agrees round by round with the direct
one-round indicator arrival list. -/
theorem buffer_queue_records_eq_direct {p : ConstructorDimensions.Parameters}
    (eta : LearningRate) (i : Fin (p.m - 1))
    (row : CompletePublicTable.CompleteRow p) (alpha : Activation p)
    (t : Fin p.T) (history : LocalHistory p (t.val + 1))
    (M : DownRecord (codecParams p eta)) (sigma ell : ℕ)
    (hsigma : M.val.sigma ≤ sigma) (hell : ell ≤ t.val + 2) :
    bufferQueueRecords eta i row alpha t history M sigma ell =
      directQueueRecords eta i row alpha t history M sigma ell hsigma hell := by
  have hattach :
      bufferQueueRecords eta i row alpha t history M sigma ell =
        (recoveryRounds sigma ell).attach.map (fun r =>
          (true, bufferArrival eta i row alpha t history M r.val)) := by
    unfold bufferQueueRecords
    have hval : (recoveryRounds sigma ell).attach.map Subtype.val =
        recoveryRounds sigma ell := List.attach_map_subtype_val _
    calc
      (recoveryRounds sigma ell).map
          (fun r => (true, bufferArrival eta i row alpha t history M r)) =
          (recoveryRounds sigma ell).map
            (fun r => (true, bufferArrival eta i row alpha t history M r)) := rfl
      _ = ((recoveryRounds sigma ell).attach.map Subtype.val).map
          (fun r => (true, bufferArrival eta i row alpha t history M r)) := by
            rw [hval]
      _ = (recoveryRounds sigma ell).attach.map
          (fun r => (true, bufferArrival eta i row alpha t history M r.val)) := by
            rw [List.map_map]
            rfl
  rw [hattach]
  unfold directQueueRecords
  apply List.map_congr_left
  intro r hr
  congr 1
  exact buffer_arrival_eq_one_round eta i row alpha t history M sigma ell hsigma hell
    ⟨r.val, r.property⟩

/-- Replay queue records from an arbitrary existing register pair. -/
@[expose] noncomputable def bufferQueueReplayFrom {p : ConstructorDimensions.Parameters}
    (eta : LearningRate) (i : Fin (p.m - 1))
    (row : CompletePublicTable.CompleteRow p) (alpha : Activation p)
    (t : Fin p.T) (history : LocalHistory p (t.val + 1))
    (M : DownRecord (codecParams p eta)) (n : ℕ) (initial : ℕ × ℕ)
    (sigma ell : ℕ) : ℕ × ℕ :=
  QueueReplay.replay (4 * n) initial
    (bufferQueueRecords eta i row alpha t history M sigma ell)

/-- The initial local queue replay starts from score zero and the DOWN
backlog. -/
@[expose] noncomputable def bufferQueueReplay {p : ConstructorDimensions.Parameters}
    (eta : LearningRate) (i : Fin (p.m - 1))
    (row : CompletePublicTable.CompleteRow p) (alpha : Activation p)
    (t : Fin p.T) (history : LocalHistory p (t.val + 1))
    (M : DownRecord (codecParams p eta)) (n ell : ℕ) : ℕ × ℕ :=
  bufferQueueReplayFrom eta i row alpha t history M n (0, M.val.q) M.val.sigma ell

/-- Replay the direct one-round indicator list from score zero and the DOWN
backlog. -/
@[expose] noncomputable def directQueueReplay {p : ConstructorDimensions.Parameters}
    (eta : LearningRate) (i : Fin (p.m - 1))
    (row : CompletePublicTable.CompleteRow p) (alpha : Activation p)
    (t : Fin p.T) (history : LocalHistory p (t.val + 1))
    (M : DownRecord (codecParams p eta)) (n ell : ℕ)
    (hell : ell ≤ t.val + 2) : ℕ × ℕ :=
  QueueReplay.replay (4 * n) (0, M.val.q)
    (directQueueRecords eta i row alpha t history M M.val.sigma ell (by omega) hell)

/-- Sparse-buffer replay agrees exactly with replay driven by the direct
one-round indicator arrivals. -/
theorem buffer_queue_replay_eq_direct {p : ConstructorDimensions.Parameters}
    (eta : LearningRate) (i : Fin (p.m - 1))
    (row : CompletePublicTable.CompleteRow p) (alpha : Activation p)
    (t : Fin p.T) (history : LocalHistory p (t.val + 1))
    (M : DownRecord (codecParams p eta)) (n ell : ℕ)
    (hell : ell ≤ t.val + 2) :
    bufferQueueReplay eta i row alpha t history M n ell =
      directQueueReplay eta i row alpha t history M n ell hell := by
  simp only [bufferQueueReplay, bufferQueueReplayFrom, directQueueReplay]
  rw [buffer_queue_records_eq_direct eta i row alpha t history M M.val.sigma ell
    (by omega) hell]

/-- The integer queue capacity is the source capacity `4 eta D` under the
explicit exact natural scale witness. -/
theorem queue_capacity_cast_eq {p : ConstructorDimensions.Parameters}
    (eta : LearningRate) (n : ℕ)
    (hproduct : eta.val * (ConstructorDimensions.D p : ℝ) = (n : ℝ)) :
    ((4 * n : ℕ) : ℝ) = 4 * eta.val * (ConstructorDimensions.D p : ℝ) :=
  SparseCalendarReplay.sparseQueueCapacity_cast_eq_of_product
    (ConstructorDimensions.D p) eta.val n hproduct

/-- Positivity of the honest integer scale follows from `eta > 0`, `D > 0`,
and the explicit product equality. -/
theorem queue_scale_pos {p : ConstructorDimensions.Parameters}
    (eta : LearningRate) (n : ℕ)
    (hproduct : eta.val * (ConstructorDimensions.D p : ℝ) = (n : ℝ)) : 0 < n :=
  SparseCalendarReplay.sparseQueueScale_pos_of_product (ConstructorDimensions.D p)
    eta.val n (by exact_mod_cast ConstructorDimensions.D_pos p) eta.property hproduct

/-- A list of the literal score increments made by `QueueReplay.transition`.
For enabled queue records each head is exactly that round's capped service. -/
@[expose] def serviceTrace (capacity : ℕ) (initial : ℕ × ℕ) :
    List (Bool × ℕ) → List ℕ
  | [] => []
  | record :: records =>
      let next := QueueReplay.transition capacity initial record
      (next.1 - initial.1) :: serviceTrace capacity next records

/-- The queue score is the initial score plus the exact sum of transition
service increments. -/
theorem queue_replay_score_eq_service_trace_sum (capacity : ℕ) (initial : ℕ × ℕ)
    (records : List (Bool × ℕ)) :
    (QueueReplay.replay capacity initial records).1 =
      initial.1 + (serviceTrace capacity initial records).sum := by
  induction records generalizing initial with
  | nil => simp [serviceTrace, QueueReplay.replay]
  | cons record records ih =>
      have hsplit : record :: records = [record] ++ records := rfl
      rw [hsplit, QueueReplay.replay_append]
      have hsingle : QueueReplay.replay capacity initial [record] =
          QueueReplay.transition capacity initial record := rfl
      rw [hsingle, ih]
      have hmono : initial.1 ≤
          (QueueReplay.transition capacity initial record).1 := by
        cases record with
        | mk enabled arrival => cases enabled <;>
            simp [QueueReplay.transition]
      change (QueueReplay.transition capacity initial record).1 +
          (serviceTrace capacity (QueueReplay.transition capacity initial record) records).sum =
        initial.1 + ((QueueReplay.transition capacity initial record).1 - initial.1 +
          (serviceTrace capacity (QueueReplay.transition capacity initial record) records).sum)
      omega

/-- On an enabled record, the service trace entry is exactly the capped
service from `QueueReplay.transition`. -/
theorem service_trace_cons_enabled (capacity score backlog arrival : ℕ)
    (records : List (Bool × ℕ)) :
    serviceTrace capacity (score, backlog) ((true, arrival) :: records) =
      Bandits.Support.CappedService.service capacity backlog arrival ::
        serviceTrace capacity
          (QueueReplay.transition capacity (score, backlog) (true, arrival)) records := by
  simp [serviceTrace, QueueReplay.transition, Bandits.Support.CappedService.service]

/-- The returned score equals the sum of every service increment over the
enabled buffer-derived interval records. -/
theorem buffer_queue_replay_total_service {p : ConstructorDimensions.Parameters}
    (eta : LearningRate) (i : Fin (p.m - 1))
    (row : CompletePublicTable.CompleteRow p) (alpha : Activation p)
    (t : Fin p.T) (history : LocalHistory p (t.val + 1))
    (M : DownRecord (codecParams p eta)) (n ell : ℕ) :
    (bufferQueueReplay eta i row alpha t history M n ell).1 =
      (serviceTrace (4 * n) (0, M.val.q)
        (bufferQueueRecords eta i row alpha t history M M.val.sigma ell)).sum := by
  simpa [bufferQueueReplay, bufferQueueReplayFrom] using
    (queue_replay_score_eq_service_trace_sum (4 * n) (0, M.val.q)
      (bufferQueueRecords eta i row alpha t history M M.val.sigma ell))

/-- Score plus terminal backlog is the initial DOWN backlog plus all actual
buffer-derived arrivals. -/
theorem buffer_queue_replay_conservation {p : ConstructorDimensions.Parameters}
    (eta : LearningRate) (i : Fin (p.m - 1))
    (row : CompletePublicTable.CompleteRow p) (alpha : Activation p)
    (t : Fin p.T) (history : LocalHistory p (t.val + 1))
    (M : DownRecord (codecParams p eta)) (n ell : ℕ) :
    (bufferQueueReplay eta i row alpha t history M n ell).1 +
        (bufferQueueReplay eta i row alpha t history M n ell).2 =
      M.val.q + (bufferArrivalList eta i row alpha t history M M.val.sigma ell).sum := by
  dsimp [bufferQueueReplay, bufferQueueReplayFrom]
  have h := QueueTraceConservation.replay_score_add_backlog (4 * n)
    (0, M.val.q) (bufferQueueRecords eta i row alpha t history M M.val.sigma ell)
  have hsum :
      ((bufferQueueRecords eta i row alpha t history M M.val.sigma ell).map
        QueueTraceConservation.acceptedArrival).sum =
        (bufferArrivalList eta i row alpha t history M M.val.sigma ell).sum := by
    have hlist :
        (bufferQueueRecords eta i row alpha t history M M.val.sigma ell).map
            QueueTraceConservation.acceptedArrival =
          bufferArrivalList eta i row alpha t history M M.val.sigma ell := by
      unfold bufferQueueRecords bufferArrivalList recoveryRounds
      rw [List.map_map]
      apply List.map_congr_left
      intro r hr
      rfl
    exact congrArg List.sum hlist
  rw [hsum, Nat.zero_add] at h
  exact h

/-- Splitting the calendar interval at a supplied intermediate boundary
appends the two enabled lists without resetting the buffer-derived arrival
function. -/
theorem buffer_queue_records_append {p : ConstructorDimensions.Parameters}
    (eta : LearningRate) (i : Fin (p.m - 1))
    (row : CompletePublicTable.CompleteRow p) (alpha : Activation p)
    (t : Fin p.T) (history : LocalHistory p (t.val + 1))
    (M : DownRecord (codecParams p eta)) (sigma mid ell : ℕ)
    (hsigmamid : sigma ≤ mid) (hmidell : mid ≤ ell) :
    bufferQueueRecords eta i row alpha t history M sigma ell =
      bufferQueueRecords eta i row alpha t history M sigma mid ++
        bufferQueueRecords eta i row alpha t history M mid ell := by
  unfold bufferQueueRecords recoveryRounds
  rw [← List.Ico.append_consecutive hsigmamid hmidell, List.map_append]

/-- Online continuation from any interval boundary is exactly
`QueueReplay.replay_append` from the prefix's current registers. -/
theorem buffer_queue_replay_from_append {p : ConstructorDimensions.Parameters}
    (eta : LearningRate) (i : Fin (p.m - 1))
    (row : CompletePublicTable.CompleteRow p) (alpha : Activation p)
    (t : Fin p.T) (history : LocalHistory p (t.val + 1))
    (M : DownRecord (codecParams p eta)) (n : ℕ) (initial : ℕ × ℕ)
    (sigma mid ell : ℕ) (hsigmamid : sigma ≤ mid) (hmidell : mid ≤ ell) :
    bufferQueueReplayFrom eta i row alpha t history M n initial sigma ell =
      QueueReplay.replay (4 * n)
        (bufferQueueReplayFrom eta i row alpha t history M n initial sigma mid)
        (bufferQueueRecords eta i row alpha t history M mid ell) := by
  simp only [bufferQueueReplayFrom]
  rw [buffer_queue_records_append eta i row alpha t history M sigma mid ell
    hsigmamid hmidell, QueueReplay.replay_append]

/-- The final service and terminal backlog come from the actual last calendar
round `ell - 1`; a nonempty interval supplies that round explicitly. -/
theorem buffer_queue_replay_last_service {p : ConstructorDimensions.Parameters}
    (eta : LearningRate) (i : Fin (p.m - 1))
    (row : CompletePublicTable.CompleteRow p) (alpha : Activation p)
    (t : Fin p.T) (history : LocalHistory p (t.val + 1))
    (M : DownRecord (codecParams p eta)) (n ell : ℕ)
    (hell : ell ≤ t.val + 2) (hnonempty : M.val.sigma < ell) :
    bufferQueueReplay eta i row alpha t history M n ell =
      let before := bufferQueueReplay eta i row alpha t history M n (ell - 1)
      let service := min (4 * n) (before.2 +
        bufferArrival eta i row alpha t history M (ell - 1))
      (before.1 + service, before.2 +
        bufferArrival eta i row alpha t history M (ell - 1) - service) := by
  have hrounds : recoveryRounds M.val.sigma ell =
      recoveryRounds M.val.sigma (ell - 1) ++ [ell - 1] := by
    unfold recoveryRounds
    cases ell with
    | zero => omega
    | succ ell =>
      have hle : M.val.sigma ≤ ell := by omega
      simpa using (List.Ico.succ_top (n := M.val.sigma) (m := ell) hle)
  have hrecords : bufferQueueRecords eta i row alpha t history M M.val.sigma ell =
      bufferQueueRecords eta i row alpha t history M M.val.sigma (ell - 1) ++
        [(true, bufferArrival eta i row alpha t history M (ell - 1))] := by
    change (recoveryRounds M.val.sigma ell).map
        (fun r => (true, bufferArrival eta i row alpha t history M r)) =
      (recoveryRounds M.val.sigma (ell - 1)).map
          (fun r => (true, bufferArrival eta i row alpha t history M r)) ++
        [(true, bufferArrival eta i row alpha t history M (ell - 1))]
    rw [hrounds, List.map_append, List.map_singleton]
  simp only [bufferQueueReplay, bufferQueueReplayFrom]
  rw [hrecords, QueueReplay.replay_append]
  simp [QueueReplay.replay, QueueReplay.transition]

/-- A round without a saved record for this arm still has enabled zero-arrival
service. Positive backlog receives positive service at positive capacity. -/
theorem missing_record_service_pos {p : ConstructorDimensions.Parameters}
    (eta : LearningRate) (i : Fin (p.m - 1))
    (row : CompletePublicTable.CompleteRow p) (alpha : Activation p)
    (t : Fin p.T) (history : LocalHistory p (t.val + 1))
    (M : DownRecord (codecParams p eta)) (n sigma ell : ℕ)
    (hsigma : M.val.sigma ≤ sigma) (hell : ell ≤ t.val + 2)
    (hproduct : eta.val * (ConstructorDimensions.D p : ℝ) = (n : ℝ))
    (r : RecoveryRound sigma ell) (score backlog : ℕ) (hbacklog : 0 < backlog)
    (hmiss : ¬ (loggingTestsPass
      (ReferencePrelaunchFollower.loggingRound i row alpha
        (ReferencePrelaunchFollower.calendar (by omega)
          (historyIndex eta t M sigma ell hsigma hell r))
        (history (historyIndex eta t M sigma ell hsigma hell r))) ∧
      (history (historyIndex eta t M sigma ell hsigma hell r)).1 = downArm eta M)) :
    0 < (QueueReplay.transition (4 * n) (score, backlog)
      (true, bufferArrival eta i row alpha t history M r.val)).1 - score := by
  classical
  have harrival : bufferArrival eta i row alpha t history M r.val = 0 := by
    rw [buffer_arrival_eq_one_round eta i row alpha t history M sigma ell hsigma hell r]
    simp [oneRoundArrival, hmiss]
  have hn := queue_scale_pos eta n hproduct
  have hcapacity : 0 < 4 * n := by omega
  have hservice := QueueReplay.transition_zero_arrival_service_pos
    (capacity := 4 * n) (_score := score) (backlog := backlog) hcapacity hbacklog
  have htransition : QueueReplay.transition (4 * n) (score, backlog)
      (true, bufferArrival eta i row alpha t history M r.val) =
        (score + min (4 * n) backlog, backlog - min (4 * n) backlog) := by
    rw [harrival]
    exact QueueReplay.transition_enabled_zero_arrival (4 * n) score backlog
  rw [htransition]
  omega

/-- Split a supplied local-history prefix at its launch boundary. `run_append`
shows the suffix continues from the prefix state, and `atLaunch` preserves both
the exact replay buffer and the possibly partial DOWN batch. -/
theorem run_through_launch {p : ConstructorDimensions.Parameters} {n : ℕ}
    (eta : LearningRate) (i : Fin (p.m - 1))
    (row : CompletePublicTable.CompleteRow p) (alpha : Activation p)
    (history : LocalHistory p n) (hn : n ≤ p.T)
    (before after : List (Fin n))
    (hsplit : before ++ after = List.ofFn (fun u : Fin n => u)) :
    ReferencePrelaunchFollower.run i row alpha history hn
        (List.ofFn (fun u : Fin n => u)) (ReferencePrelaunchFollower.initial p eta) =
      ReferencePrelaunchFollower.run i row alpha history hn after
        (ReferencePrelaunchFollower.atLaunch
          (ReferencePrelaunchFollower.run i row alpha history hn before
            (ReferencePrelaunchFollower.initial p eta))) ∧
    (ReferencePrelaunchFollower.atLaunch
        (ReferencePrelaunchFollower.run i row alpha history hn before
          (ReferencePrelaunchFollower.initial p eta))).buffer =
      (ReferencePrelaunchFollower.run i row alpha history hn before
        (ReferencePrelaunchFollower.initial p eta)).buffer ∧
    (ReferencePrelaunchFollower.atLaunch
        (ReferencePrelaunchFollower.run i row alpha history hn before
          (ReferencePrelaunchFollower.initial p eta))).downBatch =
      (ReferencePrelaunchFollower.run i row alpha history hn before
        (ReferencePrelaunchFollower.initial p eta)).downBatch := by
  have happ := ReferencePrelaunchFollower.run_append i row alpha history hn
    before after (ReferencePrelaunchFollower.initial p eta)
  refine ⟨?_, ?_⟩
  · rw [← hsplit, happ]
    rfl
  · exact ReferencePrelaunchFollower.atLaunch_preserves _

/-- A clean concrete replay prefix has no accepted DOWN decision according to
the existing parser-and-acceptance audit. -/
theorem no_accepted_down_of_clean_prefix {p : ConstructorDimensions.Parameters}
    (eta : LearningRate) (i : Fin (p.m - 1))
    (row : CompletePublicTable.CompleteRow p) (alpha : Activation p)
    (t : Fin p.T) (history : LocalHistory p (t.val + 1))
    (hclean : (prefixState eta i row alpha t history).initializationFailure = false) :
    ¬ ∃ d ∈ ReferencePrelaunchFollower.decisions i row alpha history (by omega)
        (List.ofFn (fun u : Fin (t.val + 1) => u)) (ReferencePrelaunchFollower.initial p eta),
      acceptDown (codecParams p eta) 0 (d.1.val + 1) d.2 := by
  intro haccepted
  have hfailure := (ReferencePrelaunchFollower.replay_failure_iff eta i row alpha history
    (by omega)).mpr haccepted
  change (prefixState eta i row alpha t history).initializationFailure = true at hfailure
  rw [hclean] at hfailure
  contradiction

/-- The actual prelaunch replay remains unoccupied and has no accepted DOWN
register. -/
theorem prefix_state_registers {p : ConstructorDimensions.Parameters}
    (eta : LearningRate) (i : Fin (p.m - 1))
    (row : CompletePublicTable.CompleteRow p) (alpha : Activation p)
    (t : Fin p.T) (history : LocalHistory p (t.val + 1)) :
    (prefixState eta i row alpha t history).lastDown = none ∧
    (prefixState eta i row alpha t history).status = .unoccupied := by
  obtain ⟨hdown, _, _, _, _, hstatus⟩ :=
    ReferencePrelaunchFollower.replay_registers eta i row alpha history (by omega)
  exact ⟨hdown, hstatus⟩

/-- The bridge's explicit source-side inputs produce an actual-buffer queue
replay, its direct-arrival replay, exact interval endpoints, scale identity,
and conservation. This is deterministic local recovery only; it makes no
physical-run, message-authenticity, current-word, or canonical-process claim. -/
theorem sparse_buffer_recovery_bridge {p : ConstructorDimensions.Parameters}
    (eta : LearningRate) (i : Fin (p.m - 1))
    (row : CompletePublicTable.CompleteRow p) (alpha : Activation p)
    (t : Fin p.T) (history : LocalHistory p (t.val + 1))
    (M : DownRecord (codecParams p eta)) (ell n : ℕ)
    (hactivation : alpha.val ≤ M.val.sigma)
    (hdecision : M.val.sigma ≤ t.val + 1)
    (hinterval : M.val.sigma < ell) (hell : ell ≤ t.val + 2)
    (hproduct : eta.val * (ConstructorDimensions.D p : ℝ) = (n : ℝ))
    (hclean : (prefixState eta i row alpha t history).initializationFailure = false) :
    alpha.val ≤ t.val + 1 ∧
    M.val.sigma < ell ∧ ell ≤ t.val + 2 ∧
    (¬ ∃ d ∈ ReferencePrelaunchFollower.decisions i row alpha history (by omega)
      (List.ofFn (fun u : Fin (t.val + 1) => u)) (ReferencePrelaunchFollower.initial p eta),
      acceptDown (codecParams p eta) 0 (d.1.val + 1) d.2) ∧
    (prefixState eta i row alpha t history).lastDown = none ∧
    (prefixState eta i row alpha t history).status = .unoccupied ∧
    bufferQueueReplay eta i row alpha t history M n ell =
      directQueueReplay eta i row alpha t history M n ell hell ∧
    bufferQueueReplay eta i row alpha t history M n ell =
      (let before := bufferQueueReplay eta i row alpha t history M n (ell - 1)
       let service := min (4 * n) (before.2 +
         bufferArrival eta i row alpha t history M (ell - 1))
       (before.1 + service, before.2 +
         bufferArrival eta i row alpha t history M (ell - 1) - service)) ∧
    (bufferQueueReplay eta i row alpha t history M n ell).1 =
      (serviceTrace (4 * n) (0, M.val.q)
        (bufferQueueRecords eta i row alpha t history M M.val.sigma ell)).sum ∧
    0 < n ∧
    ((4 * n : ℕ) : ℝ) = 4 * eta.val * (ConstructorDimensions.D p : ℝ) ∧
    (bufferQueueReplay eta i row alpha t history M n ell).1 +
      (bufferQueueReplay eta i row alpha t history M n ell).2 =
      M.val.q + (bufferArrivalList eta i row alpha t history M M.val.sigma ell).sum := by
  have hclean' := no_accepted_down_of_clean_prefix eta i row alpha t history hclean
  have hregisters := prefix_state_registers eta i row alpha t history
  have hdirect := buffer_queue_replay_eq_direct eta i row alpha t history M n ell hell
  have hlast := buffer_queue_replay_last_service eta i row alpha t history M n ell hell hinterval
  have hservice := buffer_queue_replay_total_service eta i row alpha t history M n ell
  have hn := queue_scale_pos eta n hproduct
  have hcapacity := queue_capacity_cast_eq eta n hproduct
  have hconservation := buffer_queue_replay_conservation eta i row alpha t history M n ell
  have hactive : alpha.val ≤ t.val + 1 := hactivation.trans hdecision
  exact ⟨hactive, hinterval, hell, hclean', hregisters.1, hregisters.2, hdirect,
    hlast, hservice, hn, hcapacity, hconservation⟩

end Bandits.Support.PrelaunchBufferRecovery

end
