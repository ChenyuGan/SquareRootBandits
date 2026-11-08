/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.DeclaredFollowerLocalRound
public import Bandits.Support.FollowerDownJointMeasurability
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# Joint measurability of unoccupied follower logging followed by DOWN

This module codes the existing observation-side composition on the genuine
unoccupied branch: checked logging, the actual DOWN transition, and the
existing `consumeDownResult`. The public input varies a complete row, a time in
the finite active-time subtype, the played arm, finite-grid feedback, and every
saved observation/thinning coordinate in its original product.

Sources: `sources/zip4/manuscript/06_interruptions.tex:192-209,256-276`,
`sources/zip4/manuscript/05_binary_transport.tex:366-381`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:8-14`.

The code preserves checked logging failures, DOWN input/output failures, and
the complete next discrete state. Its buffer recipe retains the original
continuous saved coordinates, appends the literal current record with the
same row's thinning coordinate, or clears the buffer after acceptance.
This is a local measurable composition and asserts no physical provenance or
manuscript theorem closure.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.FollowerLoggingDownMeasurability

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.CompletePublicTable
open Bandits.Support.ContinuousLearningRows
open Bandits.Support.ContinuousControlSlice
open Bandits.Support.PublicDiscreteDraws
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.SparseCalendarReplay
open Bandits.Support.ActiveFollowerLifecycle
open Bandits.Support.ActiveFollowerLogging
open Bandits.Support.ActiveFollowerDownAcceptance
open Bandits.Support.DeclaredFollowerLocalRound
open Bandits.Support.FollowerDownMeasurability
open Bandits.Support.FollowerDownJointMeasurability

abbrev Parameters := ConstructorDimensions.Parameters

/-- The actual active calendar-time subtype for one fixed activation. -/
abbrev ActiveTime (p : Parameters) (activation : Activation p) :=
  {t : Fin p.T // activation.val ≤ t.val + 1}

/-- The complete fixed-skeleton input carrier. Feedback is represented by its
actual `Fin (D+1)` index; the played arm is an independent local input. -/
abbrev LoggingDownInput (p : Parameters) (rate : RateInput p)
    (activation : Activation p) (state : State p rate.eta) :=
  ((CompleteRow p × ActiveTime p activation) ×
    (Fin (D p + 1) × Fin p.K)) × SavedScalarFamily state.buffer.length

def inputRow {p : Parameters} {rate : RateInput p} {activation : Activation p}
    {state : State p rate.eta} (x : LoggingDownInput p rate activation state) :
    CompleteRow p := x.1.1.1

def inputTime {p : Parameters} {rate : RateInput p} {activation : Activation p}
    {state : State p rate.eta} (x : LoggingDownInput p rate activation state) :
    Fin p.T := x.1.1.2.1

def inputFeedbackIndex {p : Parameters} {rate : RateInput p}
    {activation : Activation p} {state : State p rate.eta}
    (x : LoggingDownInput p rate activation state) : Fin (D p + 1) := x.1.2.1

def inputPlayedArm {p : Parameters} {rate : RateInput p} {activation : Activation p}
    {state : State p rate.eta} (x : LoggingDownInput p rate activation state) :
    Fin p.K := x.1.2.2

def inputSavedScalars {p : Parameters} {rate : RateInput p}
    {activation : Activation p} {state : State p rate.eta}
    (x : LoggingDownInput p rate activation state) : SavedScalarFamily state.buffer.length :=
  x.2

/-- The exact finite key test used to detect a duplicate current record. -/
def currentKeyFresh {p : Parameters} {rate : RateInput p}
    {activation : Activation p} {state : State p rate.eta}
    (x : LoggingDownInput p rate activation state) : Prop :=
  ∀ old ∈ state.buffer,
    (old.calendarRound, old.pilot) ≠ ((inputTime x).val + 1, inputPlayedArm x)

/-- A recipe for the continuous buffer left by the composition. -/
inductive LoggingDownBufferRecipe where
  | retained
  | appendedCurrent
  | cleared
  deriving DecidableEq, Countable

/-- A countable code for the complete observable result of the existing
composition. The DOWN constructor retains its complete accepted code, while
the separate recipe reconstructs its continuous buffer. -/
inductive LoggingDownResultCode (p : Parameters) (rate : RateInput p) where
  | loggingFailure (reason : Fin 2)
  | down (result : LocalDownResultCode p rate)
  | logged (state : FollowerStateCode p rate) (recipe : LoggingDownBufferRecipe)
  deriving Countable

instance loggingDownResultCodeMeasurableSpace (p : Parameters) (rate : RateInput p) :
    MeasurableSpace (LoggingDownResultCode p rate) := ⊤

def loggingFailureCode (reason : LoggingFailure) : Fin 2 :=
  match reason with
  | .invalidInputBuffer => 0
  | .invalidOutputBuffer => 1

def loggingFailureOfCode (reason : Fin 2) : LoggingFailure :=
  if reason.val = 0 then .invalidInputBuffer else .invalidOutputBuffer

theorem loggingFailureOfCode_code (reason : LoggingFailure) :
    loggingFailureOfCode (loggingFailureCode reason) = reason := by
  cases reason <;> rfl

/-- The literal record that checked logging may append at the current time.
Its thin scalar is read from this same complete row. -/
def currentLoggingRecord {p : Parameters} {rate : RateInput p}
    {state : State p rate.eta}
    (i : Fin (p.m - 1))
    (activation : Activation p) (x : LoggingDownInput p rate activation state) :
    SparseCalendarRecord p.K :=
  recordAt ((inputTime x).val + 1)
    (loggingRound i (inputRow x) activation (inputTime x)
      (inputPlayedArm x, feedbackAtGrid p (inputFeedbackIndex x)))

/-- Reconstruct the actual continuous buffer from its original saved product
and the code's explicit recipe. -/
def reconstructedBuffer {p : Parameters} {rate : RateInput p}
    {activation : Activation p} {state : State p rate.eta}
    (i : Fin (p.m - 1)) (x : LoggingDownInput p rate activation state)
    (recipe : LoggingDownBufferRecipe) : List (SparseCalendarRecord p.K) :=
  match recipe with
  | .retained => replaceBufferScalars state.buffer (inputSavedScalars x)
  | .appendedCurrent =>
      replaceBufferScalars state.buffer (inputSavedScalars x) ++ [currentLoggingRecord i activation x]
  | .cleared => []

/-- Decode the composition code using the original continuous inputs. -/
def reconstructLoggingDownResult {p : Parameters} (i : Fin (p.m - 1))
    (rate : RateInput p) (activation : Activation p)
    (state : State p rate.eta) (x : LoggingDownInput p rate activation state)
    (code : LoggingDownResultCode p rate) : Except RoundFailure (State p rate.eta) :=
  match code with
  | LoggingDownResultCode.loggingFailure reason =>
      .error (.logging (loggingFailureOfCode reason))
  | LoggingDownResultCode.down result =>
      consumeDownResult rate
        (reconstructLocalDownResult result
          (replaceBufferScalars state.buffer (inputSavedScalars x)))
  | LoggingDownResultCode.logged code recipe =>
      .ok (followerStateOfCode rate code
        (reconstructedBuffer i x recipe))

/-- The code obtained from the literal existing local operation. The active
subtype makes the real arm-choice activation test true. -/
def recordOrServiceThenDownCode {p : Parameters} (i : Fin (p.m - 1))
    (rate : RateInput p) (activation : Activation p)
    (state : State p rate.eta) (_hstatus : state.status = .unoccupied)
    (x : LoggingDownInput p rate activation state) : LoggingDownResultCode p rate := by
  classical
  let localState := adaptedInputState rate state (inputSavedScalars x)
  if hin : localBufferValid localState then
    if htests : loggingTestsPass
        (loggingRound i (inputRow x) activation (inputTime x)
          (inputPlayedArm x, feedbackAtGrid p (inputFeedbackIndex x))) then
      if hfresh : currentKeyFresh x then
        exact .logged (followerStateCode rate state) .appendedCurrent
      else exact .loggingFailure 1
    else if hselected : downSelected p i (inputRow x) (inputTime x) then
      exact .down (downTransitionCode i (inputRow x) (inputTime x)
        (inputFeedbackIndex x) rate state (inputSavedScalars x))
    else exact .logged (followerStateCode rate state) .retained
  else exact .loggingFailure 0

/-- A successful append is valid exactly when its carried input is valid and
its `(calendarRound,pilot)` key is fresh. No chronological-order hypothesis
is used: the existing checked domain requires timestamps, no duplicate keys,
and quantized observations, while the saved thin coordinate retains its
original type. -/
theorem localBufferValid_append_iff {p : Parameters} {eta : LearningRate}
    (s : State p eta) (r : SparseCalendarRecord p.K)
    (hrange : 1 ≤ r.calendarRound ∧ r.calendarRound ≤ p.T)
    (hgrid : ∃ q : ℕ, q ≤ D p ∧ r.observation.val = (q : ℝ) / (D p : ℝ)) :
    localBufferValid {s with buffer := s.buffer ++ [r]} ↔
      localBufferValid s ∧
        ∀ old ∈ s.buffer,
          (old.calendarRound, old.pilot) ≠ (r.calendarRound, r.pilot) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · intro old hold
        exact h.1 old (List.mem_append.mpr (Or.inl hold))
      · have hkeys := localBufferValid_keys_nodup h
        rw [List.map_append, List.map_singleton, List.nodup_append'] at hkeys
        exact hkeys.1
      · intro old hold
        exact h.2.2 old (List.mem_append.mpr (Or.inl hold))
    · intro old hold heq
      have hkeys := localBufferValid_keys_nodup h
      rw [List.map_append, List.map_singleton, List.nodup_append'] at hkeys
      have hleft : (old.calendarRound, old.pilot) ∈
          s.buffer.map (fun z => (z.calendarRound, z.pilot)) :=
        List.mem_map.mpr ⟨old, hold, rfl⟩
      have hright : (r.calendarRound, r.pilot) ∈
          [r].map (fun z => (z.calendarRound, z.pilot)) := by simp
      exact (List.disjoint_iff_ne.mp hkeys.2.2)
        (old.calendarRound, old.pilot) hleft (r.calendarRound, r.pilot) hright heq
  · rintro ⟨hvalid, hfresh⟩
    refine ⟨?_, ?_, ?_⟩
    · intro old hold
      rcases List.mem_append.mp hold with hold | hold
      · exact hvalid.1 old hold
      · simp only [List.mem_singleton] at hold
        subst old
        exact hrange
    · rw [List.map_append, List.map_singleton, List.nodup_append']
      refine ⟨localBufferValid_keys_nodup hvalid, by simp, ?_⟩
      apply List.disjoint_iff_ne.mpr
      intro key hkey other hother heq
      obtain ⟨old, hold, hkeyeq⟩ := List.mem_map.mp hkey
      have hotherEq : other = (r.calendarRound, r.pilot) := by
        simpa only [List.map_singleton, List.mem_singleton] using hother
      have hkeyr : key = (r.calendarRound, r.pilot) := by
        calc
          key = other := heq
          _ = (r.calendarRound, r.pilot) := hotherEq
      exact hfresh old hold (hkeyeq.trans hkeyr)
    · intro old hold
      rcases List.mem_append.mp hold with hold | hold
      · exact hvalid.2.2 old hold
      · simp only [List.mem_singleton] at hold
        subst old
        exact hgrid

/-- The logger's unoccupied state with independently varying saved scalars
has exactly the same validity test as the accepted DOWN buffer domain. -/
theorem adaptedState_localBufferValid_iff {p : Parameters} (rate : RateInput p)
    (state : State p rate.eta) (values : SavedScalarFamily state.buffer.length) :
    localBufferValid (adaptedInputState rate state values) ↔
      ActiveFollowerDownAcceptance.bufferInputDomain p
        (replaceBufferScalars state.buffer values) := by
  change localBufferValid {state with buffer := replaceBufferScalars state.buffer values} ↔ _
  constructor
  · intro h
    refine ⟨?_, h.2.1⟩
    intro record hrecord
    refine ⟨(h.1 record hrecord).1, (h.1 record hrecord).2, ?_⟩
    obtain ⟨q, hq, hvalue⟩ := h.2.2 record hrecord
    exact ⟨⟨q, Nat.lt_succ_of_le hq⟩, hvalue⟩
  · rintro ⟨hrecords, hkeys⟩
    refine ⟨?_, hkeys, ?_⟩
    · intro record hrecord
      rcases hrecords record hrecord with ⟨hlower, hupper, q, hvalue⟩
      exact ⟨hlower, hupper⟩
    · intro record hrecord
      obtain ⟨_, _, q, hvalue⟩ := hrecords record hrecord
      exact ⟨q.val, Nat.le_of_lt_succ q.isLt, hvalue⟩

private theorem replaceBufferScalars_keys {p : Parameters}
    (buffer : List (SparseCalendarRecord p.K))
    (values : SavedScalarFamily buffer.length) :
    (replaceBufferScalars buffer values).map (fun r => (r.calendarRound, r.pilot)) =
      buffer.map (fun r => (r.calendarRound, r.pilot)) := by
  unfold replaceBufferScalars
  simp only [List.map_ofFn, Function.comp_def]
  change List.ofFn (fun j : Fin buffer.length =>
    (buffer[j].calendarRound, buffer[j].pilot)) =
      buffer.map (fun r => (r.calendarRound, r.pilot))
  exact List.ofFn_getElem_eq_map buffer (fun r => (r.calendarRound, r.pilot))

private theorem adaptedAppendValid_iff {p : Parameters} {rate : RateInput p}
    {activation : Activation p} {state : State p rate.eta}
    (i : Fin (p.m - 1)) (x : LoggingDownInput p rate activation state) :
    localBufferValid
        {adaptedInputState rate state (inputSavedScalars x) with
          buffer := (adaptedInputState rate state (inputSavedScalars x)).buffer ++
            [currentLoggingRecord i activation x]} ↔
      localBufferValid (adaptedInputState rate state (inputSavedScalars x)) ∧
        currentKeyFresh x := by
  classical
  let localState := adaptedInputState rate state (inputSavedScalars x)
  have hrange : 1 ≤ (currentLoggingRecord i activation x).calendarRound ∧
      (currentLoggingRecord i activation x).calendarRound ≤ p.T := by
    simp [currentLoggingRecord, recordAt]
  have hgrid : ∃ q : ℕ, q ≤ D p ∧
      (currentLoggingRecord i activation x).observation.val =
        (q : ℝ) / (D p : ℝ) := by
    exact ActiveFollowerLogging.recordAt_observation_grid i (inputRow x)
      activation (inputTime x) (inputPlayedArm x,
        feedbackAtGrid p (inputFeedbackIndex x))
  have hkeys : localState.buffer.map (fun r => (r.calendarRound, r.pilot)) =
      state.buffer.map (fun r => (r.calendarRound, r.pilot)) := by
    simp [localState, adaptedInputState, replaceBufferScalars_keys]
  rw [localBufferValid_append_iff localState
    (currentLoggingRecord i activation x) hrange hgrid]
  constructor
  · rintro ⟨hvalid, hfresh⟩
    refine ⟨hvalid, ?_⟩
    intro old hold heq
    have hmem : (old.calendarRound, old.pilot) ∈
        state.buffer.map (fun r => (r.calendarRound, r.pilot)) := by
      exact List.mem_map.mpr ⟨old, hold, rfl⟩
    rw [← hkeys] at hmem
    obtain ⟨original, horiginal, hkey⟩ := List.mem_map.mp hmem
    apply hfresh original horiginal
    simpa [currentLoggingRecord, recordAt, ReferencePrelaunchFollower.loggingRound] using
      hkey.trans heq
  · rintro ⟨hvalid, hfresh⟩
    refine ⟨hvalid, ?_⟩
    intro old hold heq
    have hmem : (old.calendarRound, old.pilot) ∈
        state.buffer.map (fun r => (r.calendarRound, r.pilot)) := by
      rw [← hkeys]
      exact List.mem_map.mpr ⟨old, hold, rfl⟩
    obtain ⟨original, horiginal, hkey⟩ := List.mem_map.mp hmem
    apply hfresh original horiginal
    calc
      (original.calendarRound, original.pilot) = (old.calendarRound, old.pilot) := hkey
      _ = ((inputTime x).val + 1, inputPlayedArm x) := by
        simpa [currentLoggingRecord, recordAt, ReferencePrelaunchFollower.loggingRound] using heq

private theorem downSelected_excludes_logging {p : Parameters}
    (i : Fin (p.m - 1)) (row : CompleteRow p) (activation : Activation p)
    (t : Fin p.T) (arm : Fin p.K) (observation : Observation p)
    (hselected : downSelected p i row t) :
    ¬ loggingTestsPass (loggingRound i row activation t (arm, observation)) := by
  intro htests
  have htests' := (ActiveFollowerLogging.loggingTestsPass_iff_source_mask
    i row activation t (arm, observation)).mp htests
  have hslot := htests'.2.1
  have hdown := hselected.1
  have hne : dataSlot ≠ downSlot := by decide
  exact hne (hslot.symm.trans hdown)

/-- Exact reconstruction of the actual checked-logging-then-DOWN operation.
The proof uses the checked logger's real input and output tests, the actual
selected-DOWN operation, and its accepted code reconstruction. -/
theorem reconstruct_recordOrServiceThenDownCode {p : Parameters}
    (i : Fin (p.m - 1)) (rate : RateInput p) (activation : Activation p)
    (state : State p rate.eta) (hstatus : state.status = .unoccupied)
    (x : LoggingDownInput p rate activation state) :
    reconstructLoggingDownResult i rate activation state x
      (recordOrServiceThenDownCode i rate activation state hstatus x) =
    DeclaredFollowerLocalRound.recordOrServiceThenDown rate i (inputRow x)
      activation (inputTime x) (x.1.1.2).property (inputPlayedArm x)
      (feedbackAtGrid p (inputFeedbackIndex x))
      (adaptedInputState rate state (inputSavedScalars x)) := by
  classical
  let observation := feedbackAtGrid p (inputFeedbackIndex x)
  let localState := adaptedInputState rate state (inputSavedScalars x)
  have hactive : activation.val ≤ (inputTime x).val + 1 := (x.1.1.2).property
  have hlocalStatus : localState.status = .unoccupied := by
    simpa [localState, adaptedInputState] using hstatus
  rw [DeclaredFollowerLocalRound.recordOrServiceThenDown_unoccupied
    rate i (inputRow x) activation (inputTime x) hactive (inputPlayedArm x)
    observation localState hlocalStatus]
  by_cases hin : localBufferValid localState
  · by_cases htests : loggingTestsPass
        (loggingRound i (inputRow x) activation (inputTime x)
          (inputPlayedArm x, observation))
    · by_cases hfresh : currentKeyFresh x
      · have hlogged :
            ActiveFollowerLogging.checkedLogging i (inputRow x) activation
              (inputTime x) (inputPlayedArm x, observation) localState =
              .ok {localState with buffer := localState.buffer ++
                [currentLoggingRecord i activation x]} := by
          apply (ActiveFollowerLogging.checkedLogging_success_iff i (inputRow x)
            activation (inputTime x) (inputPlayedArm x, observation) localState _).2
          have hupdate : loggingUpdate i (inputRow x) activation
              (inputTime x) (inputPlayedArm x, observation) localState =
              {localState with buffer := localState.buffer ++
                [currentLoggingRecord i activation x]} := by
            simp [ActiveFollowerLogging.loggingUpdate,
              ActiveFollowerLogging.loggingBranch, hactive, hlocalStatus,
              ActiveFollowerLogging.logAt_eq_singleton_of_tests, htests,
              currentLoggingRecord, observation]
          have hout : localBufferValid
              {localState with buffer := localState.buffer ++
                [currentLoggingRecord i activation x]} := by
            have happend := (adaptedAppendValid_iff i x).2 ⟨hin, hfresh⟩
            simpa [localState] using happend
          exact ⟨hin, hupdate.symm, hout⟩
        have hnotSelected : ¬ downSelected p i (inputRow x) (inputTime x) := by
          intro hselected
          exact downSelected_excludes_logging i (inputRow x) activation
            (inputTime x) (inputPlayedArm x) observation hselected htests
        have hdown : ActiveFollowerDownAcceptance.downTransition p i
            (inputRow x) (inputTime x) observation rate
            {localState with buffer := localState.buffer ++
              [currentLoggingRecord i activation x]} =
            .skipped {localState with buffer := localState.buffer ++
              [currentLoggingRecord i activation x]} .notSelectedDown :=
          ActiveFollowerDownAcceptance.downTransition_notSelected p i
            (inputRow x) (inputTime x) observation rate _ hnotSelected
        have hcode : followerStateCode rate state =
            followerStateCode rate
              {localState with buffer := localState.buffer ++
                [currentLoggingRecord i activation x]} := by
          rfl
        have hbuffer : reconstructedBuffer i x .appendedCurrent =
            (localState.buffer ++ [currentLoggingRecord i activation x]) := by
          simp [reconstructedBuffer, currentLoggingRecord, localState,
            adaptedInputState]
        have hresultCode : recordOrServiceThenDownCode i rate activation state
            hstatus x = .logged (followerStateCode rate state) .appendedCurrent := by
          simp [recordOrServiceThenDownCode, localState, hin, htests, hfresh, observation]
        simp only [hresultCode, reconstructLoggingDownResult, hlogged]
        rw [hdown]
        simp only [DeclaredFollowerLocalRound.consumeDownResult]
        rw [hcode, hbuffer]
        exact congrArg Except.ok
          (FollowerDownMeasurability.followerStateOfCode_code_eq rate
            {localState with buffer := localState.buffer ++
              [currentLoggingRecord i activation x]}
            (localState.buffer ++ [currentLoggingRecord i activation x]) rfl)
      · have hupdate : loggingUpdate i (inputRow x) activation
            (inputTime x) (inputPlayedArm x, observation) localState =
            {localState with buffer := localState.buffer ++
              [currentLoggingRecord i activation x]} := by
          simp [ActiveFollowerLogging.loggingUpdate,
            ActiveFollowerLogging.loggingBranch, hactive, hlocalStatus,
            ActiveFollowerLogging.logAt_eq_singleton_of_tests, htests,
            currentLoggingRecord, observation]
        have hout : ¬ localBufferValid
            (loggingUpdate i (inputRow x) activation
              (inputTime x) (inputPlayedArm x, observation) localState) := by
          rw [hupdate]
          intro hv
          exact hfresh ((adaptedAppendValid_iff i x).1 hv).2
        have hlogged : ActiveFollowerLogging.checkedLogging i
            (inputRow x) activation (inputTime x)
            (inputPlayedArm x, observation) localState =
            .error .invalidOutputBuffer :=
          ActiveFollowerLogging.checkedLogging_invalid_output i (inputRow x)
            activation (inputTime x) (inputPlayedArm x, observation) localState hin hout
        have hresultCode : recordOrServiceThenDownCode i rate activation state
            hstatus x = .loggingFailure 1 := by
          simp [recordOrServiceThenDownCode, localState, hin, htests, hfresh, observation]
        simp [hresultCode, reconstructLoggingDownResult, hlogged,
          loggingFailureOfCode]
    · have hupdate : loggingUpdate i (inputRow x) activation
            (inputTime x) (inputPlayedArm x, observation) localState = localState := by
          have hbranch : loggingBranch activation (inputTime x) localState :=
            ⟨hactive, hlocalStatus⟩
          unfold ActiveFollowerLogging.loggingUpdate
          rw [ite_eq_left hbranch]
          rw [ActiveFollowerLogging.logAt_eq_nil_of_not_tests i (inputRow x)
            activation (inputTime x) (inputPlayedArm x, observation) htests]
          rw [List.append_nil]
      have hlogged : ActiveFollowerLogging.checkedLogging i
          (inputRow x) activation (inputTime x)
          (inputPlayedArm x, observation) localState = .ok localState := by
        apply (ActiveFollowerLogging.checkedLogging_success_iff i (inputRow x)
          activation (inputTime x) (inputPlayedArm x, observation) localState _).2
        exact ⟨hin, hupdate.symm, hin⟩
      by_cases hselected : downSelected p i (inputRow x) (inputTime x)
      · have hdownCode := FollowerDownJointMeasurability.downTransitionCode_joint_reconstruct
          i rate state
            (((inputRow x, inputTime x), inputFeedbackIndex x),
              inputSavedScalars x)
        have hdown : reconstructLocalDownResult
            (downTransitionCode i (inputRow x) (inputTime x)
              (inputFeedbackIndex x) rate state (inputSavedScalars x))
            (replaceBufferScalars state.buffer (inputSavedScalars x)) =
            ActiveFollowerDownAcceptance.downTransition p i (inputRow x)
              (inputTime x) observation rate localState := by
          simpa [FollowerDownJointMeasurability.downTransitionCodeAt,
            FollowerDownJointMeasurability.jointRow,
            FollowerDownJointMeasurability.jointRowTime,
            FollowerDownJointMeasurability.jointTime,
            FollowerDownJointMeasurability.jointFeedbackIndex,
            FollowerDownJointMeasurability.jointValues,
              FollowerDownMeasurability.adaptedInputState, localState,
            observation] using hdownCode
        have hresultCode : recordOrServiceThenDownCode i rate activation state
            hstatus x = .down (downTransitionCode i (inputRow x) (inputTime x)
              (inputFeedbackIndex x) rate state (inputSavedScalars x)) := by
          simp [recordOrServiceThenDownCode, localState, hin, htests, hselected,
            observation]
        simp only [hresultCode, reconstructLoggingDownResult, hlogged]
        exact congrArg (consumeDownResult rate) hdown
      · have hdown : ActiveFollowerDownAcceptance.downTransition p i
            (inputRow x) (inputTime x) observation rate localState =
            .skipped localState .notSelectedDown :=
          ActiveFollowerDownAcceptance.downTransition_notSelected p i
            (inputRow x) (inputTime x) observation rate localState hselected
        simp only [hlogged]
        have hstateCode : followerStateCode rate state =
            followerStateCode rate localState := rfl
        have hbuffer : replaceBufferScalars state.buffer (inputSavedScalars x) =
            localState.buffer := rfl
        have hresultCode : recordOrServiceThenDownCode i rate activation state
            hstatus x = .logged (followerStateCode rate state) .retained := by
          simp [recordOrServiceThenDownCode, localState, hin, htests, hselected,
            observation]
        simp only [hresultCode, reconstructLoggingDownResult]
        rw [hdown]
        simp [reconstructedBuffer, hstateCode, hbuffer,
          DeclaredFollowerLocalRound.consumeDownResult,
          FollowerDownMeasurability.followerStateOfCode_code_eq]
  · have hlogged := ActiveFollowerLogging.checkedLogging_invalid_input i
      (inputRow x) activation (inputTime x) (inputPlayedArm x, observation)
      localState hin
    have hresultCode : recordOrServiceThenDownCode i rate activation state
        hstatus x = .loggingFailure 0 := by
      simp [recordOrServiceThenDownCode, localState, hin]
    simp [hresultCode, reconstructLoggingDownResult, hlogged,
      loggingFailureOfCode]

/-- The actual checked input-domain event is measurable on the original saved
scalar product, including off-grid observations and invalid fixed skeletons. -/
theorem measurableSet_adaptedState_localBufferValid {p : Parameters}
    (rate : RateInput p) (activation : Activation p) (state : State p rate.eta) :
    MeasurableSet {x : LoggingDownInput p rate activation state |
      localBufferValid (adaptedInputState rate state (inputSavedScalars x))} := by
  classical
  have hvalues : Measurable (inputSavedScalars (p := p) (rate := rate)
      (activation := activation) (state := state)) := measurable_snd
  have hbit : Measurable (fun x : LoggingDownInput p rate activation state =>
      bufferInputValidAt state.buffer (inputSavedScalars x)) :=
    (measurable_bufferInputValidAt state.buffer).comp hvalues
  have hset : {x : LoggingDownInput p rate activation state |
      localBufferValid (adaptedInputState rate state (inputSavedScalars x))} =
      {x | bufferInputValidAt state.buffer (inputSavedScalars x) = true} := by
    ext x
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq]
    rw [bufferInputValidAt_true_iff]
    exact adaptedState_localBufferValid_iff rate state (inputSavedScalars x)
  rw [hset]
  exact hbit (measurableSet_singleton true)

/-- The key-freshness event is a finite-coordinate test; it does not impose
chronological ordering on the carried skeleton. -/
theorem measurableSet_currentKeyFresh {p : Parameters} (rate : RateInput p)
    (activation : Activation p) (state : State p rate.eta) :
    MeasurableSet {x : LoggingDownInput p rate activation state | currentKeyFresh x} := by
  classical
  let keyFresh : Fin p.T × Fin p.K → Bool := fun key =>
    decide (∀ old ∈ state.buffer,
      (old.calendarRound, old.pilot) ≠ (key.1.val + 1, key.2))
  have hkey : Measurable (fun x : LoggingDownInput p rate activation state =>
      (inputTime x, inputPlayedArm x)) := by
    exact (measurable_subtype_coe.comp
      (measurable_snd.comp (measurable_fst.comp measurable_fst))).prodMk
        (measurable_snd.comp (measurable_snd.comp measurable_fst))
  have hbit : Measurable keyFresh := measurable_of_finite keyFresh
  have htest : Measurable (fun x : LoggingDownInput p rate activation state =>
      decide (currentKeyFresh x)) := by
    convert hbit.comp hkey using 1
    funext x
    simp [keyFresh, currentKeyFresh]
  have hset : {x : LoggingDownInput p rate activation state | currentKeyFresh x} =
      (fun x => decide (currentKeyFresh x)) ⁻¹' {true} := by
    ext x
    simp
  rw [hset]
  exact htest (measurableSet_singleton true)

/-- A generic finite-index evaluation lemma used to retain the genuine time
coordinate of the complete row. -/
private theorem measurable_fin_eval {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] (n : ℕ) (f : Fin n → α → β)
    (hf : ∀ j, Measurable (f j)) :
    Measurable (fun z : α × Fin n => f z.2 z.1) := by
  intro s hs
  have hset : (fun z : α × Fin n => f z.2 z.1) ⁻¹' s =
      ⋃ j : Fin n, {z | z.2 = j} ∩ {z | f j z.1 ∈ s} := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro hz
      exact ⟨z.2, rfl, hz⟩
    · rintro ⟨j, hj, hz⟩
      change f z.2 z.1 ∈ s
      rw [hj]
      exact hz
  rw [hset]
  apply MeasurableSet.iUnion
  intro j
  have hindex : MeasurableSet {z : α × Fin n | z.2 = j} :=
    (measurableSet_singleton j).preimage measurable_snd
  have hvalue : MeasurableSet {z : α × Fin n | f j z.1 ∈ s} :=
    ((hf j) hs).preimage measurable_fst
  exact hindex.inter hvalue

private theorem measurable_inputRowTime {p : Parameters} {rate : RateInput p}
    {activation : Activation p} {state : State p rate.eta} :
    Measurable (fun x : LoggingDownInput p rate activation state =>
      (inputRow x, inputTime x)) := by
  have hrow : Measurable (inputRow (p := p) (rate := rate)
      (activation := activation) (state := state)) :=
    measurable_fst.comp (measurable_fst.comp measurable_fst)
  have hactive : Measurable (fun x : LoggingDownInput p rate activation state =>
      x.1.1.2) := measurable_snd.comp (measurable_fst.comp measurable_fst)
  have htime : Measurable (inputTime (p := p) (rate := rate)
      (activation := activation) (state := state)) :=
    measurable_subtype_coe.comp hactive
  exact hrow.prodMk htime

def inputSliceAt {p : Parameters} {rate : RateInput p}
    {activation : Activation p} {state : State p rate.eta}
    (x : LoggingDownInput p rate activation state) : Slice p.m p.K :=
  sliceAt (inputTime x) (completeRowLearning p (inputRow x))

private theorem measurable_inputSliceAt {p : Parameters} {rate : RateInput p}
    {activation : Activation p} {state : State p rate.eta} :
    Measurable (inputSliceAt (p := p) (rate := rate)
      (activation := activation) (state := state)) := by
  have hfixed : ∀ t : Fin p.T,
      Measurable (fun row : CompleteRow p =>
        sliceAt t (completeRowLearning p row)) := by
    intro t
    exact (ContinuousLearningRows.measurable_sliceAt t).comp
      (CompletePublicTable.measurable_completeRowLearning p)
  have heval := measurable_fin_eval p.T
    (fun t row => sliceAt t (completeRowLearning p row)) hfixed
  change Measurable (fun x : LoggingDownInput p rate activation state =>
    (fun z : CompleteRow p × Fin p.T => sliceAt z.2
      (completeRowLearning p z.1)) (inputRow x, inputTime x))
  exact heval.comp measurable_inputRowTime

/-- The exact source/mask logging test as a finite-valued function of the
complete current row, carried arm, and active time. -/
def loggingGateBit {p : Parameters} (i : Fin (p.m - 1))
    {rate : RateInput p} {activation : Activation p}
    {state : State p rate.eta} (x : LoggingDownInput p rate activation state) : Bool :=
  decide (slotDraw (inputSliceAt x) = dataSlot) &&
    decide (recorderSourceDraw p.two_le_m p.m_lt_K (inputSliceAt x) =
      followerPlayer p.two_le_m i) &&
    decide (∀ j : Fin p.m, j ≠ followerPlayer p.two_le_m i →
      pilotDraw (K_pos p) j (inputSliceAt x) ≠ inputPlayedArm x)

theorem loggingGateBit_true_iff_testsPass {p : Parameters} (i : Fin (p.m - 1))
    (rate : RateInput p) (activation : Activation p) (state : State p rate.eta)
    (x : LoggingDownInput p rate activation state) :
    loggingGateBit i x = true ↔ loggingTestsPass
      (loggingRound i (inputRow x) activation (inputTime x)
        (inputPlayedArm x, feedbackAtGrid p (inputFeedbackIndex x))) := by
  rw [loggingTestsPass_iff_source_mask]
  have hactive : activation.val ≤ (inputTime x).val + 1 := (x.1.1.2).property
  have hslice : inputSliceAt x = ((inputRow x).2 (inputTime x)).1 := by rfl
  simp only [loggingGateBit, Bool.and_eq_true, decide_eq_true_eq]
  rw [hslice]
  simp only [hactive, true_and]
  exact and_assoc

theorem measurable_loggingGateBit {p : Parameters} (i : Fin (p.m - 1))
    (rate : RateInput p) (activation : Activation p) (state : State p rate.eta) :
    Measurable (loggingGateBit i :
      LoggingDownInput p rate activation state → Bool) := by
  have hslice := measurable_inputSliceAt (p := p) (rate := rate)
    (activation := activation) (state := state)
  let slotBit : LoggingDownInput p rate activation state → Bool := fun x =>
    decide (slotDraw (inputSliceAt x) = dataSlot)
  have hslot : Measurable slotBit := by
    exact (measurable_of_finite (fun s : Slot => decide (s = dataSlot))).comp
      ((PublicDiscreteDraws.measurable_slotDraw).comp hslice)
  let sourceBit : LoggingDownInput p rate activation state → Bool := fun x =>
    decide (recorderSourceDraw p.two_le_m p.m_lt_K (inputSliceAt x) =
      followerPlayer p.two_le_m i)
  have hsource : Measurable sourceBit := by
    exact (measurable_of_finite (fun s : Fin p.m =>
      decide (s = followerPlayer p.two_le_m i))).comp
        ((PublicDiscreteDraws.measurable_recorderSourceDraw p.two_le_m p.m_lt_K).comp hslice)
  have hpilots : Measurable (fun x : LoggingDownInput p rate activation state =>
      fun j : Fin p.m => pilotDraw (K_pos p) j (inputSliceAt x)) := by
    rw [measurable_pi_iff]
    intro j
    exact (PublicDiscreteDraws.measurable_pilotDraw (K_pos p) j).comp hslice
  have harm : Measurable (inputPlayedArm (p := p) (rate := rate)
      (activation := activation) (state := state)) :=
    measurable_snd.comp (measurable_snd.comp measurable_fst)
  let maskBit : LoggingDownInput p rate activation state → Bool := fun x =>
    decide (∀ j : Fin p.m, j ≠ followerPlayer p.two_le_m i →
      pilotDraw (K_pos p) j (inputSliceAt x) ≠ inputPlayedArm x)
  have hmaskBit : Measurable maskBit := by
    let mask : (Fin p.m → Fin p.K) × Fin p.K → Bool := fun z =>
      decide (∀ j : Fin p.m, j ≠ followerPlayer p.two_le_m i → z.1 j ≠ z.2)
    have hmask : Measurable (fun x : LoggingDownInput p rate activation state =>
        mask (fun j => pilotDraw (K_pos p) j (inputSliceAt x), inputPlayedArm x)) := by
      exact (measurable_of_finite mask).comp (hpilots.prodMk harm)
    convert hmask using 1
  let combine : Bool × (Bool × Bool) → Bool := fun z => z.1 && z.2.1 && z.2.2
  have hcombine : Measurable combine := measurable_of_finite combine
  have heq : loggingGateBit i = fun x =>
      combine (slotBit x, (sourceBit x, maskBit x)) := by
    funext x
    rfl
  rw [heq]
  exact hcombine.comp (hslot.prodMk (hsource.prodMk hmaskBit))

private theorem measurable_downSelectedInput {p : Parameters} (i : Fin (p.m - 1))
    (rate : RateInput p) (activation : Activation p) (state : State p rate.eta) :
    Measurable (fun x : LoggingDownInput p rate activation state =>
      downSelectionBit i (inputRow x) (inputTime x)) := by
  have hfixed : ∀ t : Fin p.T,
      Measurable (fun row : CompleteRow p => downSelectionBit i row t) := by
    intro t
    exact FollowerDownJointMeasurability.measurable_downSelectedAt p i t
  have heval := measurable_fin_eval p.T
    (fun t row => downSelectionBit i row t) hfixed
  change Measurable (fun x : LoggingDownInput p rate activation state =>
    (fun z : CompleteRow p × Fin p.T => downSelectionBit i z.1 z.2)
      (inputRow x, inputTime x))
  exact heval.comp measurable_inputRowTime

private theorem measurable_downJointInputMap {p : Parameters} {rate : RateInput p}
    {activation : Activation p} {state : State p rate.eta} :
    Measurable (fun x : LoggingDownInput p rate activation state =>
      (((inputRow x, inputTime x), inputFeedbackIndex x), inputSavedScalars x)) := by
  have hrowtime := measurable_inputRowTime (p := p) (rate := rate)
    (activation := activation) (state := state)
  have hfeedback : Measurable (inputFeedbackIndex (p := p) (rate := rate)
      (activation := activation) (state := state)) :=
    measurable_fst.comp (measurable_snd.comp measurable_fst)
  have hvalues : Measurable (inputSavedScalars (p := p) (rate := rate)
      (activation := activation) (state := state)) := measurable_snd
  exact (hrowtime.prodMk hfeedback).prodMk hvalues

/-- Measurability of the countable code for the complete actual operation on
the fixed unoccupied branch. The code's conditional branches are measurable
by the exact checked-buffer, DATA/source/mask, and selected-DOWN events. -/
theorem measurable_recordOrServiceThenDownCode {p : Parameters}
    (i : Fin (p.m - 1)) (rate : RateInput p) (activation : Activation p)
    (state : State p rate.eta) (hstatus : state.status = .unoccupied) :
    Measurable (recordOrServiceThenDownCode i rate activation state hstatus) := by
  classical
  let hinSet : Set (LoggingDownInput p rate activation state) :=
    {x | localBufferValid (adaptedInputState rate state (inputSavedScalars x))}
  have hin : MeasurableSet hinSet :=
    measurableSet_adaptedState_localBufferValid rate activation state
  let htestsBit := measurable_loggingGateBit i rate activation state
  have htests : MeasurableSet {x : LoggingDownInput p rate activation state |
      loggingTestsPass (loggingRound i (inputRow x) activation (inputTime x)
        (inputPlayedArm x, feedbackAtGrid p (inputFeedbackIndex x)))} := by
    have hset : {x : LoggingDownInput p rate activation state |
        loggingTestsPass (loggingRound i (inputRow x) activation (inputTime x)
          (inputPlayedArm x, feedbackAtGrid p (inputFeedbackIndex x)))} =
        (fun x => loggingGateBit i x) ⁻¹' {true} := by
      ext x
      exact (loggingGateBit_true_iff_testsPass i rate activation state x).symm
    rw [hset]
    exact htestsBit (measurableSet_singleton true)
  have hfresh : MeasurableSet
      {x : LoggingDownInput p rate activation state | currentKeyFresh x} :=
    measurableSet_currentKeyFresh rate activation state
  have hselectedBit := measurable_downSelectedInput i rate activation state
  have hselected : MeasurableSet
      {x : LoggingDownInput p rate activation state |
        downSelected p i (inputRow x) (inputTime x)} := by
    have hset : {x : LoggingDownInput p rate activation state |
        downSelected p i (inputRow x) (inputTime x)} =
        (fun x => downSelectionBit i (inputRow x) (inputTime x)) ⁻¹' {true} := by
      ext x
      exact (FollowerDownJointMeasurability.downSelectionBit_eq_true i
        (inputRow x) (inputTime x)).symm
    rw [hset]
    exact hselectedBit (measurableSet_singleton true)
  have hdown : Measurable (fun x : LoggingDownInput p rate activation state =>
      LoggingDownResultCode.down
        (downTransitionCode i (inputRow x) (inputTime x)
          (inputFeedbackIndex x) rate state (inputSavedScalars x))) := by
    have hjoint := (FollowerDownJointMeasurability.measurable_downTransitionCode_joint
      i rate state).comp (measurable_downJointInputMap (p := p) (rate := rate)
        (activation := activation) (state := state))
    have hjointCode : Measurable (fun x : LoggingDownInput p rate activation state =>
        FollowerDownMeasurability.downTransitionCode i (inputRow x) (inputTime x)
          (inputFeedbackIndex x) rate state (inputSavedScalars x)) := by
      convert hjoint using 1
      funext x
      rfl
    change Measurable (fun x : LoggingDownInput p rate activation state =>
      LoggingDownResultCode.down
        (FollowerDownMeasurability.downTransitionCode i (inputRow x) (inputTime x)
          (inputFeedbackIndex x) rate state (inputSavedScalars x)))
    have htag : Measurable (fun c : LocalDownResultCode p rate =>
        LoggingDownResultCode.down c) := by
      intro s hs
      change MeasurableSet[⊤] _
      exact MeasurableSpace.measurableSet_top
    exact htag.comp hjointCode
  let stateCode := FollowerDownMeasurability.followerStateCode rate state
  let retainedFun : LoggingDownInput p rate activation state → LoggingDownResultCode p rate :=
    fun _ => LoggingDownResultCode.logged stateCode .retained
  have hstate : Measurable retainedFun := measurable_const
  let appendedFun : LoggingDownInput p rate activation state → LoggingDownResultCode p rate :=
    fun _ => LoggingDownResultCode.logged stateCode .appendedCurrent
  have happended : Measurable appendedFun := measurable_const
  let logFun : LoggingDownInput p rate activation state → LoggingDownResultCode p rate :=
    fun x => if currentKeyFresh x then appendedFun x else LoggingDownResultCode.loggingFailure 1
  have hlog : Measurable logFun := by
    convert Measurable.piecewise hfresh happended
      (measurable_const : Measurable (fun _ : LoggingDownInput p rate activation state =>
        LoggingDownResultCode.loggingFailure 1)) using 1
    funext x
    rfl
  let downOrStateFun : LoggingDownInput p rate activation state → LoggingDownResultCode p rate :=
    fun x => if downSelected p i (inputRow x) (inputTime x) then
        LoggingDownResultCode.down
          (downTransitionCode i (inputRow x) (inputTime x)
            (inputFeedbackIndex x) rate state (inputSavedScalars x))
      else retainedFun x
  have hdownOrState : Measurable downOrStateFun := by
    convert Measurable.piecewise hselected hdown hstate using 1
    funext x
    rfl
  let afterTestsFun : LoggingDownInput p rate activation state → LoggingDownResultCode p rate :=
    fun x =>
      if loggingTestsPass (loggingRound i (inputRow x) activation (inputTime x)
          (inputPlayedArm x, feedbackAtGrid p (inputFeedbackIndex x))) then logFun x
      else downOrStateFun x
  have hafterTests : Measurable afterTestsFun := by
    convert Measurable.piecewise htests hlog hdownOrState using 1
    funext x
    rfl
  let inputFailureFun : LoggingDownInput p rate activation state → LoggingDownResultCode p rate :=
    fun _ => LoggingDownResultCode.loggingFailure 0
  have hinputFailure : Measurable inputFailureFun := measurable_const
  let resultFun : LoggingDownInput p rate activation state → LoggingDownResultCode p rate :=
    fun x =>
      if localBufferValid (adaptedInputState rate state (inputSavedScalars x)) then
        afterTestsFun x else inputFailureFun x
  have hresult : Measurable resultFun := by
    convert Measurable.piecewise hin hafterTests hinputFailure using 1
    funext x
    rfl
  have hcode : recordOrServiceThenDownCode i rate activation state hstatus = resultFun := by
    funext x
    simp [recordOrServiceThenDownCode, retainedFun, appendedFun, logFun,
      downOrStateFun, afterTestsFun, inputFailureFun, resultFun, stateCode]
  rw [hcode]
  exact hresult

end Bandits.Support.FollowerLoggingDownMeasurability
