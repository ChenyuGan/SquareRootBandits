/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ActiveFollowerLifecycle
public import Bandits.Support.ActiveFollowerArmChoice
public import Bandits.Support.ReferencePrelaunchFollower

import Lean.Elab.Tactic.Omega

/-!
# Checked active unoccupied-follower logging

This module implements the local unoccupied-follower logging stage from
`sources/zip4/manuscript/06_interruptions.tex:193-233,241-275` and the buffer
domain in `sources/zip4/manuscript/appendix_a_local_protocol.tex:8-14`. It
reuses the reference follower state, the literal `logAt` record formula, the
integrated buffer-domain predicate, and the integrated arm-choice operation.
The supplied local observations are inputs to a bounded fold; they are not a
physical execution. This module does not process pending DOWN messages,
recover queues, authenticate buffers, or prove physical recording equivalence.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ActiveFollowerLogging

open Bandits.Support.ConstructorDimensions
open Bandits.Support.CompletePublicTable
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.SparseCalendarReplay
open Bandits.Support.ActiveFollowerLifecycle
open Bandits.Support.OrdinaryMessageCodec
open Bandits.Support.PublicDiscreteDraws
open Bandits.Support.ContinuousControlSlice

/-- Local failures of the checked logging stage, distinct from the retained
initialization-failure flag in the follower state. -/
inductive LoggingFailure where
  | invalidInputBuffer
  | invalidOutputBuffer
  deriving DecidableEq, Repr

/-- The arm-choice-time gate for this stage. -/
def loggingBranch {p : Parameters} {eta : LearningRate}
    (alpha : Activation p) (t : Fin p.T) (s : State p eta) : Prop :=
  alpha.val ≤ t.val + 1 ∧ s.status = .unoccupied

noncomputable local instance {p : Parameters} {eta : LearningRate}
    (alpha : Activation p) (t : Fin p.T) (s : State p eta) :
    Decidable (loggingBranch alpha t s) := Classical.propDecidable _

/-- The literal buffer-only state update. The source's `logAt` is evaluated
only on the active unoccupied branch. -/
def loggingUpdate {p : Parameters} {eta : LearningRate}
    (i : Fin (p.m - 1)) (row : CompleteRow p) (alpha : Activation p)
    (t : Fin p.T) (own : Fin p.K × Observation p) (s : State p eta) : State p eta := by
  classical
  exact if loggingBranch alpha t s then
    { s with buffer := s.buffer ++ logAt i row alpha t own }
  else s

/-- Check the carried buffer before use, apply the literal append, and check
the resulting buffer before storing it. -/
noncomputable def checkedLogging {p : Parameters} {eta : LearningRate}
    (i : Fin (p.m - 1)) (row : CompleteRow p) (alpha : Activation p)
    (t : Fin p.T) (own : Fin p.K × Observation p) (s : State p eta) :
    Except LoggingFailure (State p eta) := by
  classical
  if hin : localBufferValid s then
    let out := loggingUpdate i row alpha t own s
    if hout : localBufferValid out then
      exact .ok out
    else exact .error .invalidOutputBuffer
  else exact .error .invalidInputBuffer

/-- The gate inherited from `logAt`: activation, DATA, this source, and the
source/mask tests on the actual declared learning row. There is no reward
positivity or thinning comparison in this characterization. -/
theorem loggingTestsPass_iff_source_mask {p : Parameters}
    (i : Fin (p.m - 1)) (row : CompleteRow p) (alpha : Activation p)
    (t : Fin p.T) (own : Fin p.K × Observation p) :
    loggingTestsPass (loggingRound i row alpha t own) ↔
      alpha.val ≤ t.val + 1 ∧
      slotDraw (row.2 t).1 = dataSlot ∧
      recorderSourceDraw p.two_le_m p.m_lt_K (row.2 t).1 =
        followerPlayer p.two_le_m i ∧
      ∀ j : Fin p.m, j ≠ followerPlayer p.two_le_m i →
        pilotDraw (K_pos p) j (row.2 t).1 ≠ own.1 :=
  ReferencePrelaunchFollower.loggingTestsPass_iff i row alpha t own

/-- Changing the observation while retaining the arm does not change the
logging gate. The gate has no positivity or thinning test. -/
theorem loggingTestsPass_observation_independent {p : Parameters}
    (i : Fin (p.m - 1)) (row : CompleteRow p) (alpha : Activation p)
    (t : Fin p.T) (arm : Fin p.K) (y y' : Observation p) :
    loggingTestsPass (loggingRound i row alpha t (arm, y)) ↔
      loggingTestsPass (loggingRound i row alpha t (arm, y')) := by
  rw [loggingTestsPass_iff_source_mask, loggingTestsPass_iff_source_mask]

/-- Passing the existing tests creates exactly the single literal record. -/
theorem logAt_eq_singleton_of_tests {p : Parameters} (i : Fin (p.m - 1))
    (row : CompleteRow p) (alpha : Activation p) (t : Fin p.T)
    (own : Fin p.K × Observation p)
    (h : loggingTestsPass (loggingRound i row alpha t own)) :
    logAt i row alpha t own = [recordAt (t.val + 1) (loggingRound i row alpha t own)] := by
  simp [ReferencePrelaunchFollower.logAt, h]

/-- Failing any existing test creates no record. -/
theorem logAt_eq_nil_of_not_tests {p : Parameters} (i : Fin (p.m - 1))
    (row : CompleteRow p) (alpha : Activation p) (t : Fin p.T)
    (own : Fin p.K × Observation p)
    (h : ¬ loggingTestsPass (loggingRound i row alpha t own)) :
    logAt i row alpha t own = [] := by
  simp [ReferencePrelaunchFollower.logAt, h]

/-- Every member of `logAt` has the exact source timestamp, played arm,
quantized observation, and saved thinning scalar. -/
theorem logAt_member_fields {p : Parameters} (i : Fin (p.m - 1))
    (row : CompleteRow p) (alpha : Activation p) (t : Fin p.T)
    (own : Fin p.K × Observation p) (r : SparseCalendarRecord p.K)
    (hr : r ∈ logAt i row alpha t own) :
    r.calendarRound = t.val + 1 ∧ r.pilot = own.1 ∧
      r.observation = own.2.val ∧ r.thinScalar = (row.2 t).1 Label.thin := by
  obtain ⟨_, rfl⟩ := ReferencePrelaunchFollower.mem_logAt_iff i row alpha t own r |>.mp hr
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- A valid incoming buffer can append one source record when all carried
timestamps precede its timestamp. -/
theorem localBufferValid_append_record {p : Parameters} {eta : LearningRate}
    (s : State p eta) (r : SparseCalendarRecord p.K)
    (hvalid : localBufferValid s)
    (hrange : 1 ≤ r.calendarRound ∧ r.calendarRound ≤ p.T)
    (hbefore : ∀ old ∈ s.buffer, old.calendarRound < r.calendarRound)
    (hgrid : ∃ q : ℕ, q ≤ D p ∧ r.observation.val = (q : ℝ) / (D p : ℝ)) :
    localBufferValid {s with buffer := s.buffer ++ [r]} := by
  refine ⟨?_, ?_, ?_⟩
  · intro record hrecord
    rcases List.mem_append.mp hrecord with hold | hnew
    · exact hvalid.1 record hold
    · simp only [List.mem_singleton] at hnew
      subst record
      exact hrange
  · rw [List.map_append, List.map_singleton]
    rw [List.nodup_append']
    refine ⟨localBufferValid_keys_nodup hvalid, by simp, ?_⟩
    simp only [List.disjoint_iff_ne]
    intro key hkey other hother heq
    obtain ⟨old, hold, hkeyeq⟩ := List.mem_map.mp hkey
    simp only [List.mem_singleton] at hother
    have hkeyToOther : (old.calendarRound, old.pilot) = (r.calendarRound, r.pilot) :=
      hkeyeq.trans (heq.trans hother)
    have hroundEq := congrArg Prod.fst hkeyToOther
    exact (Nat.ne_of_lt (hbefore old hold)) hroundEq
  · intro record hrecord
    rcases List.mem_append.mp hrecord with hold | hnew
    · exact hvalid.2.2 record hold
    · simp only [List.mem_singleton] at hnew
      subst record
      exact hgrid

/-- The observation stored by `recordAt` inherits its denominator-`D` grid
witness from the supplied typed observation. -/
theorem recordAt_observation_grid {p : Parameters} (i : Fin (p.m - 1))
    (row : CompleteRow p) (alpha : Activation p) (t : Fin p.T)
    (own : Fin p.K × Observation p) :
    ∃ q : ℕ, q ≤ D p ∧
      (recordAt (t.val + 1) (loggingRound i row alpha t own)).observation.val =
        (q : ℝ) / (D p : ℝ) := by
  obtain ⟨q, hq⟩ := own.2.property
  refine ⟨q.val, ?_, ?_⟩
  · have := q.isLt
    omega
  · simpa only [recordAt, loggingRound] using hq

/-- A chronological incoming buffer remains in the integrated domain after
the exact `logAt` append. -/
theorem localBufferValid_loggingUpdate_of_chronological {p : Parameters}
    {eta : LearningRate} (i : Fin (p.m - 1)) (row : CompleteRow p)
    (alpha : Activation p) (t : Fin p.T) (own : Fin p.K × Observation p)
    (s : State p eta) (hvalid : localBufferValid s)
    (hbefore : ∀ r ∈ s.buffer, r.calendarRound < t.val + 1)
    (hstatus : s.status = .unoccupied) :
    localBufferValid (loggingUpdate i row alpha t own s) := by
  classical
  by_cases hactive : alpha.val ≤ t.val + 1
  · have hbranch : loggingBranch alpha t s := ⟨hactive, hstatus⟩
    by_cases htests : loggingTestsPass (loggingRound i row alpha t own)
    · change localBufferValid (if loggingBranch alpha t s then
        {s with buffer := s.buffer ++ logAt i row alpha t own} else s)
      rw [ite_eq_left hbranch, logAt_eq_singleton_of_tests i row alpha t own htests]
      apply localBufferValid_append_record s _ hvalid
      · change 1 ≤ t.val + 1 ∧ t.val + 1 ≤ p.T
        exact ⟨by omega, Nat.succ_le_of_lt t.isLt⟩
      · intro old hold
        exact hbefore old hold
      · exact recordAt_observation_grid i row alpha t own
    · change localBufferValid (if loggingBranch alpha t s then
        {s with buffer := s.buffer ++ logAt i row alpha t own} else s)
      rw [ite_eq_left hbranch, logAt_eq_nil_of_not_tests i row alpha t own htests]
      simpa using hvalid
  · have htests : ¬ loggingTestsPass (loggingRound i row alpha t own) := by
      intro hpass
      have hgate := (loggingTestsPass_iff_source_mask i row alpha t own).mp hpass
      omega
    have hbranch : ¬ loggingBranch alpha t s := by
      simp [loggingBranch, hactive]
    change localBufferValid (if loggingBranch alpha t s then
      {s with buffer := s.buffer ++ logAt i row alpha t own} else s)
    rw [ite_eq_right hbranch]
    exact hvalid

/-- On a failed input-domain check, no update is evaluated or stored. -/
theorem checkedLogging_invalid_input {p : Parameters} {eta : LearningRate}
    (i : Fin (p.m - 1)) (row : CompleteRow p) (alpha : Activation p)
    (t : Fin p.T) (own : Fin p.K × Observation p) (s : State p eta)
    (h : ¬ localBufferValid s) :
    checkedLogging i row alpha t own s = .error .invalidInputBuffer := by
  simp [checkedLogging, h]

/-- Repeated carried list keys fail the input check instead of being
deduplicated or discarded. -/
theorem checkedLogging_duplicate_key_fails {p : Parameters} {eta : LearningRate}
    (i : Fin (p.m - 1)) (row : CompleteRow p) (alpha : Activation p)
    (t : Fin p.T) (own : Fin p.K × Observation p) (s : State p eta)
    (hduplicate : ¬ (s.buffer.map (fun r => (r.calendarRound, r.pilot))).Nodup) :
    checkedLogging i row alpha t own s = .error .invalidInputBuffer := by
  apply checkedLogging_invalid_input
  intro hvalid
  exact hduplicate (localBufferValid_keys_nodup hvalid)

/-- An off-grid carried observation fails the input check. -/
theorem checkedLogging_offGrid_input_fails {p : Parameters} {eta : LearningRate}
    (i : Fin (p.m - 1)) (row : CompleteRow p) (alpha : Activation p)
    (t : Fin p.T) (own : Fin p.K × Observation p) (s : State p eta)
    (record : SparseCalendarRecord p.K) (hrecord : record ∈ s.buffer)
    (hoffGrid : ¬ ∃ q : ℕ, q ≤ D p ∧
      record.observation.val = (q : ℝ) / (D p : ℝ)) :
    checkedLogging i row alpha t own s = .error .invalidInputBuffer := by
  apply checkedLogging_invalid_input
  intro hvalid
  exact hoffGrid (hvalid.2.2 record hrecord)

/-- A valid input whose computed append is outside the buffer domain is an
explicit output-domain failure. -/
theorem checkedLogging_invalid_output {p : Parameters} {eta : LearningRate}
    (i : Fin (p.m - 1)) (row : CompleteRow p) (alpha : Activation p)
    (t : Fin p.T) (own : Fin p.K × Observation p) (s : State p eta)
    (hin : localBufferValid s)
    (hout : ¬ localBufferValid (loggingUpdate i row alpha t own s)) :
    checkedLogging i row alpha t own s = .error .invalidOutputBuffer := by
  simp [checkedLogging, hin, hout]

/-- A newly logged key that already occurs in a valid input buffer fails the
output check; the operation never silently drops the appended record. -/
theorem checkedLogging_duplicate_output_key_fails {p : Parameters} {eta : LearningRate}
    (i : Fin (p.m - 1)) (row : CompleteRow p) (alpha : Activation p)
    (t : Fin p.T) (own : Fin p.K × Observation p) (s : State p eta)
    (hin : localBufferValid s) (hbranch : loggingBranch alpha t s)
    (htests : loggingTestsPass (loggingRound i row alpha t own))
    (old : SparseCalendarRecord p.K) (hold : old ∈ s.buffer)
    (hround : old.calendarRound = t.val + 1) (harm : old.pilot = own.1) :
    checkedLogging i row alpha t own s = .error .invalidOutputBuffer := by
  apply checkedLogging_invalid_output i row alpha t own s hin
  intro hout
  have hkeys := localBufferValid_keys_nodup hout
  have hbuf : (loggingUpdate i row alpha t own s).buffer =
      s.buffer ++ logAt i row alpha t own := by
    simp [loggingUpdate, hbranch]
  rw [hbuf, List.map_append] at hkeys
  let key : ℕ × Fin p.K := (t.val + 1, own.1)
  have hleft : key ∈ s.buffer.map (fun r => (r.calendarRound, r.pilot)) := by
    apply List.mem_map.mpr
    refine ⟨old, hold, ?_⟩
    exact Prod.ext hround harm
  have hright : key ∈ (logAt i row alpha t own).map
      (fun r => (r.calendarRound, r.pilot)) := by
    rw [logAt_eq_singleton_of_tests i row alpha t own htests]
    simp [key, recordAt, loggingRound]
  have hdis := (List.nodup_append'.mp hkeys).2.2
  have hne := (List.disjoint_iff_ne.mp hdis) key hleft key hright
  exact hne rfl

/-- Exact success characterization, including the output check. -/
theorem checkedLogging_success_iff {p : Parameters} {eta : LearningRate}
    (i : Fin (p.m - 1)) (row : CompleteRow p) (alpha : Activation p)
    (t : Fin p.T) (own : Fin p.K × Observation p) (s out : State p eta) :
    checkedLogging i row alpha t own s = .ok out ↔
      localBufferValid s ∧ out = loggingUpdate i row alpha t own s ∧
        localBufferValid out := by
  classical
  by_cases hin : localBufferValid s
  · by_cases hout : localBufferValid (loggingUpdate i row alpha t own s)
    · unfold checkedLogging
      rw [dite_eq_left hin, dite_eq_left hout]
      constructor
      · intro heq
        have heq' : loggingUpdate i row alpha t own s = out := Except.ok.inj heq
        exact ⟨hin, heq'.symm, heq' ▸ hout⟩
      · rintro ⟨_, heq, _⟩
        subst out
        rfl
    · unfold checkedLogging
      rw [dite_eq_left hin, dite_eq_right hout]
      constructor
      · intro h
        cases h
      · rintro ⟨_, heq, hvalid⟩
        exact False.elim (hout (heq ▸ hvalid))
  · unfold checkedLogging
    rw [dite_eq_right hin]
    constructor
    · intro h
      cases h
    · rintro ⟨hvalid, _, _⟩
      exact False.elim (hin hvalid)

/-- Successful logging changes only the existing buffer field. -/
theorem checkedLogging_success_frame {p : Parameters} {eta : LearningRate}
    (i : Fin (p.m - 1)) (row : CompleteRow p) (alpha : Activation p)
    (t : Fin p.T) (own : Fin p.K × Observation p) (s out : State p eta)
    (h : checkedLogging i row alpha t own s = .ok out) :
    out.lastDown = s.lastDown ∧ out.S = s.S ∧ out.delta = s.delta ∧
      out.backlog = s.backlog ∧ out.status = s.status ∧
      out.downBatch = s.downBatch ∧
      out.initializationFailure = s.initializationFailure := by
  classical
  have hs := (checkedLogging_success_iff i row alpha t own s out).mp h
  rw [hs.2.1]
  by_cases hbranch : loggingBranch alpha t s <;> simp [loggingUpdate, hbranch]

/-- Exact successful buffer equation: append `logAt` only on the active,
unoccupied arm-choice branch. -/
theorem checkedLogging_success_buffer {p : Parameters} {eta : LearningRate}
    (i : Fin (p.m - 1)) (row : CompleteRow p) (alpha : Activation p)
    (t : Fin p.T) (own : Fin p.K × Observation p) (s out : State p eta)
    (h : checkedLogging i row alpha t own s = .ok out) :
    out.buffer = if loggingBranch alpha t s then
      s.buffer ++ logAt i row alpha t own else s.buffer := by
  classical
  have hs := (checkedLogging_success_iff i row alpha t own s out).mp h
  rw [hs.2.1]
  by_cases hbranch : loggingBranch alpha t s <;> simp [loggingUpdate, hbranch]

/-- Exact one-call buffer membership: the new record occurs precisely on the
active unoccupied branch when the existing source/mask tests pass. -/
theorem checkedLogging_success_mem_iff {p : Parameters} {eta : LearningRate}
    (i : Fin (p.m - 1)) (row : CompleteRow p) (alpha : Activation p)
    (t : Fin p.T) (own : Fin p.K × Observation p) (s out : State p eta)
    (h : checkedLogging i row alpha t own s = .ok out)
    (r : SparseCalendarRecord p.K) :
    r ∈ out.buffer ↔ r ∈ s.buffer ∨
      (loggingBranch alpha t s ∧
        loggingTestsPass (loggingRound i row alpha t own) ∧
        r = recordAt (t.val + 1) (loggingRound i row alpha t own)) := by
  classical
  rw [checkedLogging_success_buffer i row alpha t own s out h]
  by_cases hbranch : loggingBranch alpha t s
  · rw [ite_eq_left hbranch, List.mem_append,
      ReferencePrelaunchFollower.mem_logAt_iff]
    simp [hbranch]
  · rw [ite_eq_right hbranch]
    simp [hbranch]

/-- Inactive and non-unoccupied calls are checked no-ops, and do not request
or inspect an offered UP payload. -/
theorem checkedLogging_noop {p : Parameters} {eta : LearningRate}
    (i : Fin (p.m - 1)) (row : CompleteRow p) (alpha : Activation p)
    (t : Fin p.T) (own : Fin p.K × Observation p) (s : State p eta)
    (hvalid : localBufferValid s) (hbranch : ¬ loggingBranch alpha t s) :
    checkedLogging i row alpha t own s = .ok s := by
  classical
  simp [checkedLogging, hvalid, loggingUpdate, hbranch]

/-- The logging stage depends on its declared complete row only through this
follower's learning row; changing public proposal bits cannot affect it. -/
theorem checkedLogging_eq_of_same_learning_row {p : Parameters} {eta : LearningRate}
    (i : Fin (p.m - 1)) (row₁ row₂ : CompleteRow p) (alpha : Activation p)
    (t : Fin p.T) (own : Fin p.K × Observation p) (s : State p eta)
    (hrow : row₁.2 = row₂.2) :
    checkedLogging i row₁ alpha t own s = checkedLogging i row₂ alpha t own s := by
  classical
  have hlog : logAt i row₁ alpha t own = logAt i row₂ alpha t own := by
    rcases row₁ with ⟨forward₁, learning₁⟩
    rcases row₂ with ⟨forward₂, learning₂⟩
    change learning₁ = learning₂ at hrow
    subst learning₂
    rfl
  have hupdate : loggingUpdate i row₁ alpha t own s =
      loggingUpdate i row₂ alpha t own s := by
    unfold loggingUpdate
    rw [hlog]
  unfold checkedLogging
  rw [hupdate]

/-- The active unoccupied DATA arm-choice branch returns this follower's
public pilot. -/
theorem data_armChoice_eq_public_pilot {p : Parameters} {eta : LearningRate}
    (s : State p eta) (row : CompleteRow p) (t : Fin p.T)
    (i : Fin (p.m - 1))
    (offeredUp : Option (UpRecord (codecParams p eta)))
    (own : Fin p.K × Observation p)
    (hstatus : s.status = .unoccupied)
    (hdata : slotDraw (row.2 t).1 = dataSlot)
    (hchoice : ActiveFollowerArmChoice.followerArmChoice s row t i offeredUp = some own.1) :
    own.1 = pilotDraw (K_pos p) (followerPlayer p.two_le_m i) (row.2 t).1 := by
  rw [ActiveFollowerArmChoice.followerArmChoice_eq_core,
    ActiveFollowerArmChoice.followerArmChoiceCore_unoccupied_data
      s (row.2 t) i offeredUp hstatus hdata] at hchoice
  exact (Option.some.inj hchoice).symm

/-- When the supplied own arm is the actual DATA arm choice, the literal
logged record agrees with the public pilot in the declared row. -/
theorem logAt_member_pilot_eq_public_pilot {p : Parameters} {eta : LearningRate}
    (s : State p eta) (row : CompleteRow p) (alpha : Activation p)
    (t : Fin p.T) (i : Fin (p.m - 1))
    (offeredUp : Option (UpRecord (codecParams p eta)))
    (own : Fin p.K × Observation p) (r : SparseCalendarRecord p.K)
    (hstatus : s.status = .unoccupied)
    (hdata : slotDraw (row.2 t).1 = dataSlot)
    (hchoice : ActiveFollowerArmChoice.followerArmChoice s row t i offeredUp = some own.1)
    (hr : r ∈ logAt i row alpha t own) :
    r.pilot = pilotDraw (K_pos p) (followerPlayer p.two_le_m i) (row.2 t).1 := by
  have hp := data_armChoice_eq_public_pilot s row t i offeredUp own hstatus hdata hchoice
  have hfields := logAt_member_fields i row alpha t own r hr
  exact hfields.2.1.trans hp

/-- The typed own observation and chronological input domain suffice for this
stage to succeed; the output buffer is checked before it is returned. -/
theorem checkedLogging_success_of_chronological {p : Parameters} {eta : LearningRate}
    (i : Fin (p.m - 1)) (row : CompleteRow p) (alpha : Activation p)
    (t : Fin p.T) (own : Fin p.K × Observation p) (s : State p eta)
    (hvalid : localBufferValid s)
    (hbefore : ∀ r ∈ s.buffer, r.calendarRound < t.val + 1)
    (hstatus : s.status = .unoccupied) :
    ∃ out, checkedLogging i row alpha t own s = .ok out ∧
      out.buffer = s.buffer ++ logAt i row alpha t own ∧
      out.status = s.status ∧ out.initializationFailure = s.initializationFailure ∧
      localBufferValid out := by
  classical
  have hout := localBufferValid_loggingUpdate_of_chronological
    i row alpha t own s hvalid hbefore hstatus
  have hsuccess : checkedLogging i row alpha t own s =
      .ok (loggingUpdate i row alpha t own s) :=
    (checkedLogging_success_iff i row alpha t own s
      (loggingUpdate i row alpha t own s)).mpr ⟨hvalid, rfl, hout⟩
  have hframe := checkedLogging_success_frame i row alpha t own s
    (loggingUpdate i row alpha t own s) hsuccess
  have hbuffer := checkedLogging_success_buffer i row alpha t own s
    (loggingUpdate i row alpha t own s) hsuccess
  refine ⟨loggingUpdate i row alpha t own s, hsuccess, ?_, hframe.2.2.2.2.1,
    hframe.2.2.2.2.2.2, hout⟩
  rw [hbuffer]
  by_cases hactive : alpha.val ≤ t.val + 1
  · simp [loggingBranch, hstatus, hactive]
  · have htests : ¬ loggingTestsPass (loggingRound i row alpha t own) := by
      intro hpass
      have hgate := (loggingTestsPass_iff_source_mask i row alpha t own).mp hpass
      omega
    have hnil := logAt_eq_nil_of_not_tests i row alpha t own htests
    simp [loggingBranch, hstatus, hactive, hnil]

/-- A checked operation over the first `k` supplied local observations. Its
recursive order is calendar `0,1,...,k-1`; every step is this operation alone. -/
noncomputable def foldPrefix {p : Parameters} {n : ℕ} {eta : LearningRate}
    (i : Fin (p.m - 1)) (row : CompleteRow p) (alpha : Activation p)
    (history : LocalHistory p n) (hn : n ≤ p.T) :
    (k : ℕ) → k ≤ n → State p eta → Except LoggingFailure (State p eta)
  | 0, _, s => .ok s
  | k + 1, hk, s => do
      let prior ← foldPrefix i row alpha history hn k (by omega) s
      checkedLogging i row alpha (calendar hn ⟨k, by omega⟩)
        (history ⟨k, by omega⟩) prior

/-- The chronological list of source log contributions made by the first `k`
bounded calls. Its recursive append order is increasing calendar order. -/
def foldRecords {p : Parameters} {n : ℕ}
    (i : Fin (p.m - 1)) (row : CompleteRow p) (alpha : Activation p)
    (history : LocalHistory p n) (hn : n ≤ p.T) :
    (k : ℕ) → k ≤ n → List (SparseCalendarRecord p.K)
  | 0, _ => []
  | k + 1, hk =>
      foldRecords i row alpha history hn k (by omega) ++
        logAt i row alpha (calendar hn ⟨k, by omega⟩) (history ⟨k, by omega⟩)

/-- Membership in the call list names exactly one supplied calendar offset. -/
theorem foldRecords_mem_iff {p : Parameters} {n k : ℕ}
    (i : Fin (p.m - 1)) (row : CompleteRow p) (alpha : Activation p)
    (history : LocalHistory p n) (hn : n ≤ p.T) (hk : k ≤ n)
    (r : SparseCalendarRecord p.K) :
    r ∈ foldRecords i row alpha history hn k hk ↔
      ∃ u : ℕ, ∃ hu : u < n, u < k ∧
        r ∈ logAt i row alpha (calendar hn ⟨u, hu⟩) (history ⟨u, hu⟩) := by
  induction k with
  | zero => simp [foldRecords]
  | succ k ih =>
      change r ∈
          (foldRecords i row alpha history hn k (by omega) ++
            logAt i row alpha (calendar hn ⟨k, by omega⟩) (history ⟨k, by omega⟩)) ↔ _
      rw [List.mem_append, ih]
      constructor
      · rintro (⟨u, huN, huK, hr⟩ | hr)
        · exact ⟨u, huN, by omega, hr⟩
        · exact ⟨k, by omega, by omega, hr⟩
      · rintro ⟨u, huN, huK, hr⟩
        by_cases hlt : u < k
        · exact Or.inl ⟨u, huN, hlt, hr⟩
        · have heq : u = k := by omega
          subst u
          exact Or.inr hr

/-- Full bounded increasing-calendar fold over the supplied local history. -/
noncomputable def boundedFold {p : Parameters} {n : ℕ} {eta : LearningRate}
    (i : Fin (p.m - 1)) (row : CompleteRow p) (alpha : Activation p)
    (history : LocalHistory p n) (hn : n ≤ p.T) :
    Except LoggingFailure (State p eta) :=
  foldPrefix i row alpha history hn n (Nat.le_refl n) (initial p eta)

/-- Prefix induction: a valid unoccupied incoming state whose saved records
end by round `k` yields a valid unoccupied result after the first `k` calls. -/
theorem foldPrefix_success {p : Parameters} {n k : ℕ} {eta : LearningRate}
    (i : Fin (p.m - 1)) (row : CompleteRow p) (alpha : Activation p)
    (history : LocalHistory p n) (hn : n ≤ p.T) (hk : k ≤ n)
    (s : State p eta) (hstatus : s.status = .unoccupied)
    (hvalid : localBufferValid s)
    (hbufferEmpty : s.buffer = []) :
    ∃ out, foldPrefix i row alpha history hn k hk s = .ok out ∧
      out.status = .unoccupied ∧ localBufferValid out ∧
      (∀ r ∈ out.buffer, r.calendarRound ≤ k) ∧
      out.initializationFailure = s.initializationFailure ∧
      out.buffer = s.buffer ++ foldRecords i row alpha history hn k hk := by
  induction k with
  | zero =>
      refine ⟨s, rfl, hstatus, hvalid, ?_, rfl, ?_⟩
      · intro r hr
        rw [hbufferEmpty] at hr
        simp at hr
      · simp [foldRecords, hbufferEmpty]
  | succ k ih =>
      have hk' : k ≤ n := by omega
      obtain ⟨mid, hmid, hmidStatus, hmidValid, hmidBound, hmidInit, hmidBuffer⟩ :=
        ih hk'
      let t : Fin p.T := calendar hn ⟨k, by omega⟩
      have htval : t.val = k := by simp [t, calendar]
      have hbefore : ∀ r ∈ mid.buffer, r.calendarRound < t.val + 1 := by
        intro r hr
        have hpriorRound := hmidBound r hr
        rw [htval]
        omega
      have hstep := checkedLogging_success_of_chronological
        i row alpha t (history ⟨k, by omega⟩) mid hmidValid hbefore
        hmidStatus
      obtain ⟨out, hout, hbuffer, houtStatus, houtInit, houtValid⟩ := hstep
      have houtUnoccupied : out.status = .unoccupied := houtStatus.trans hmidStatus
      refine ⟨out, ?_, houtUnoccupied, houtValid, ?_, ?_, ?_⟩
      · change (do
          let prior ← foldPrefix i row alpha history hn k hk' s
          checkedLogging i row alpha t (history ⟨k, by omega⟩) prior) = .ok out
        rw [hmid]
        exact hout
      · intro r hr
        rw [hbuffer, List.mem_append] at hr
        rcases hr with hr | hr
        · have := hmidBound r hr
          omega
        · have hm := logAt_member_fields i row alpha t
            (history ⟨k, by omega⟩) r hr
          rw [hm.1]
          rw [htval]
      · rw [houtInit, hmidInit]
      · rw [hbuffer, hmidBuffer]
        simp only [t, foldRecords, List.append_assoc]

/-- The bounded fold succeeds from the ordinary unoccupied initial state and
returns an in-domain buffer. -/
theorem boundedFold_success {p : Parameters} {n : ℕ} {eta : LearningRate}
    (i : Fin (p.m - 1)) (row : CompleteRow p) (alpha : Activation p)
    (history : LocalHistory p n) (hn : n ≤ p.T) :
    ∃ out, boundedFold (eta := eta) i row alpha history hn = .ok out ∧
      out.status = .unoccupied ∧ localBufferValid out ∧
      out.initializationFailure = false ∧
      ∀ r ∈ out.buffer, r.calendarRound ≤ n := by
  have hstart : localBufferValid (initial p eta) := by
    unfold localBufferValid
    simp [initial]
  obtain ⟨out, hout, hstatus, hvalid, hbound, hinit, _⟩ :=
    foldPrefix_success i row alpha history hn (Nat.le_refl n)
      (initial p eta) rfl hstart (by rfl)
  refine ⟨out, ?_, hstatus, hvalid, ?_, hbound⟩
  · simpa [boundedFold] using hout
  · simpa [initial] using hinit

/-- Exact record membership in the successful bounded fold: every record came
from one of the supplied local calls and passed precisely `logAt`'s tests. -/
theorem boundedFold_mem_iff {p : Parameters} {n : ℕ} {eta : LearningRate}
    (i : Fin (p.m - 1)) (row : CompleteRow p) (alpha : Activation p)
    (history : LocalHistory p n) (hn : n ≤ p.T)
    (out : State p eta)
    (hout : boundedFold (eta := eta) i row alpha history hn = .ok out)
    (r : SparseCalendarRecord p.K) :
    r ∈ out.buffer ↔
      ∃ u : Fin n,
        loggingTestsPass (loggingRound i row alpha (calendar hn u) (history u)) ∧
        r = recordAt (u.val + 1)
          (loggingRound i row alpha (calendar hn u) (history u)) := by
  have hstart : localBufferValid (initial p eta) := by
    unfold localBufferValid
    simp [initial]
  obtain ⟨out', hfold, _, _, _, _, hbuffer⟩ :=
    foldPrefix_success i row alpha history hn (Nat.le_refl n)
      (initial p eta) rfl hstart (by rfl)
  change foldPrefix i row alpha history hn n (Nat.le_refl n) (initial p eta) = .ok out at hout
  have heq : out' = out := Except.ok.inj (hfold.symm.trans hout)
  have hbuf : out.buffer = foldRecords i row alpha history hn n (Nat.le_refl n) := by
    rw [← heq]
    simpa [initial] using hbuffer
  rw [hbuf]
  rw [foldRecords_mem_iff i row alpha history hn (Nat.le_refl n) r]
  constructor
  · rintro ⟨u, huN, hu, hr⟩
    obtain ⟨htests, heq⟩ := ReferencePrelaunchFollower.mem_logAt_iff i row alpha
      (calendar hn ⟨u, huN⟩) (history ⟨u, huN⟩) r |>.mp hr
    refine ⟨⟨u, huN⟩, htests, ?_⟩
    rw [heq]
    simp only [calendar]
  · rintro ⟨u, htests, heq⟩
    refine ⟨u.val, u.isLt, u.isLt, ?_⟩
    apply (ReferencePrelaunchFollower.mem_logAt_iff i row alpha
      (calendar hn u) (history u) r).mpr
    refine ⟨htests, ?_⟩
    simpa only [calendar] using heq

/-- Calls at distinct increasing calendar coordinates have unique list keys,
as certified by the integrated local buffer invariant. -/
theorem boundedFold_keys_nodup {p : Parameters} {n : ℕ} {eta : LearningRate}
    (i : Fin (p.m - 1)) (row : CompleteRow p) (alpha : Activation p)
    (history : LocalHistory p n) (hn : n ≤ p.T)
    (out : State p eta)
    (hout : boundedFold (eta := eta) i row alpha history hn = .ok out) :
    (out.buffer.map (fun r => (r.calendarRound, r.pilot))).Nodup := by
  obtain ⟨out', hout', _, hvalid, _, _⟩ := boundedFold_success i row alpha history hn
  have houtEq : out' = out := Except.ok.inj (hout'.symm.trans hout)
  subst out
  exact localBufferValid_keys_nodup hvalid

end Bandits.Support.ActiveFollowerLogging

end
