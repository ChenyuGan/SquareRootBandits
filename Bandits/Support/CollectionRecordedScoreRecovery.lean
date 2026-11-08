/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.AssignmentScoreReconstruction
public import Bandits.Support.AssignmentStartPayload
public import Bandits.Support.CollectionFullInputReplay
public import Bandits.Support.CollectionKnownQueueContinuation
public import Bandits.Support.RecordedQueueRun

import Lean.Elab.Tactic.Omega

/-!
# Conditional collection-to-recorded-run score recovery

The source evidence is `sources/zip4/manuscript/06_interruptions.tex:16-28,
80-100,257-294` and `sources/zip4/manuscript/04_slow_fast_learner.tex:140-174`.

This module relates the actual checked collection ledger to the actual finite
`RecordedQueueRun` through explicit base-score, accepted-UP, outside-register,
and raw queue-record provenance. It does not construct physical inputs or
authenticate messages. After the recorded run's analytical overflow stop, the
identified object is that stopped auxiliary run only.
-/

@[expose] public section

namespace Bandits.Support.CollectionRecordedScoreRecovery

open Bandits.Support.AssignmentScoreReconstruction
open Bandits.Support.AssignmentStartPayload
open Bandits.Support.CollectionCheckedExecution
open Bandits.Support.CollectionFullInputReplay
open Bandits.Support.CoordinatorCollectionLedger
open Bandits.Support.ReferencePrelaunchFollower

variable {p : ConstructorDimensions.Parameters}
variable {eta : LearningRate}
variable {old : AssignmentStartPayload.Input p eta}

/-- The ledger cap inherited from the actual retained assignment payload. -/
abbrev payloadCap (old : AssignmentStartPayload.Input p eta) :
    CoordinatorCollectionLedger.sourceLearningCap p eta.val :=
  old.eta_le_source_cap

/-- The natural queue numerator inherited from the same assignment payload. -/
abbrev payloadN (old : AssignmentStartPayload.Input p eta) : ℕ := old.n

/-- The exact numerator identity inherited from the same assignment payload. -/
abbrev payloadN_eq (old : AssignmentStartPayload.Input p eta) :
    (old.n : ℝ) = eta.val * (ConstructorDimensions.D p : ℝ) :=
  old.n_eq_eta_mul_D

/-- The state after processing the first `prefixLength` rounds of the supplied
finite recorded run. Source round `r` observes prefix length `r - 1`. -/
noncomputable def recordedQueuePrefix
    (parameters : RecordedQueueRun.Parameters)
    (rounds : List (RecordedQueueRun.RoundInput p.K))
    (prefixLength : ℕ) : RecordedQueueRun.RunState p.K :=
  RecordedQueueRun.run parameters (rounds.take prefixLength)

/-- The source score register immediately before calendar round `r`. -/
noncomputable def recordedScoreBefore
    (parameters : RecordedQueueRun.Parameters)
    (rounds : List (RecordedQueueRun.RoundInput p.K))
    (r : ℕ) (a : Fin p.K) : ℕ :=
  ((recordedQueuePrefix parameters rounds (r - 1)).registers a).1

/-- The source backlog immediately before calendar round `r`. -/
noncomputable def recordedQueueBefore
    (parameters : RecordedQueueRun.Parameters)
    (rounds : List (RecordedQueueRun.RoundInput p.K))
    (r : ℕ) (a : Fin p.K) : ℕ :=
  ((recordedQueuePrefix parameters rounds (r - 1)).registers a).2

/-- The preceding calendar-round service, expressed as the difference of the
actual recorded-run prefix scores. -/
noncomputable def recordedPrecedingService
    (parameters : RecordedQueueRun.Parameters)
    (rounds : List (RecordedQueueRun.RoundInput p.K))
    (r : ℕ) (a : Fin p.K) : ℕ :=
  recordedScoreBefore parameters rounds r a -
    recordedScoreBefore parameters rounds (r - 1) a

private theorem execute_append (parameters : RecordedQueueRun.Parameters)
    (first second : List (RecordedQueueRun.RoundInput p.K))
    (state : RecordedQueueRun.RunState p.K) :
    RecordedQueueRun.execute parameters (first ++ second) state =
      RecordedQueueRun.execute parameters second
        (RecordedQueueRun.execute parameters first state) := by
  induction first generalizing state with
  | nil => simp [RecordedQueueRun.execute]
  | cons round first ih =>
      simp only [List.cons_append, RecordedQueueRun.execute]
      exact ih (RecordedQueueRun.step parameters state round)

private theorem take_eq_take_append_drop_take
    (rounds : List (RecordedQueueRun.RoundInput p.K))
    (start finish : ℕ) (hstart : start ≤ finish) :
    rounds.take finish = rounds.take start ++
      (rounds.drop start).take (finish - start) := by
  by_cases hlen : start ≤ rounds.length
  · have htakeLength : (rounds.take start).length = start := by
      rw [List.length_take, Nat.min_eq_left hlen]
    calc
      rounds.take finish = (rounds.take start ++ rounds.drop start).take finish := by
        rw [List.take_append_drop]
      _ = rounds.take start ++ (rounds.drop start).take (finish - start) := by
        rw [List.take_append]
        rw [List.take_of_length_le (by rw [htakeLength]; exact hstart), htakeLength]
  · have hlen' : rounds.length ≤ start := Nat.le_of_not_ge hlen
    have htakeStart : rounds.take start = rounds := List.take_of_length_le hlen'
    have htakeFinish : rounds.take finish = rounds :=
      List.take_of_length_le (hlen'.trans hstart)
    have hdrop : rounds.drop start = [] := List.drop_eq_nil_of_le hlen'
    simp [htakeStart, htakeFinish, hdrop]

private theorem run_take_eq_execute_drop (parameters : RecordedQueueRun.Parameters)
    (rounds : List (RecordedQueueRun.RoundInput p.K))
    (start finish : ℕ) (hstart : start ≤ finish) :
    RecordedQueueRun.run parameters (rounds.take finish) =
      RecordedQueueRun.execute parameters ((rounds.drop start).take (finish - start))
        (RecordedQueueRun.run parameters (rounds.take start)) := by
  rw [RecordedQueueRun.run,
    take_eq_take_append_drop_take rounds start finish hstart, execute_append]
  rfl

private theorem step_score_ge (parameters : RecordedQueueRun.Parameters)
    (state : RecordedQueueRun.RunState p.K)
    (round : RecordedQueueRun.RoundInput p.K) (a : Fin p.K) :
    (state.registers a).1 ≤
      ((RecordedQueueRun.step parameters state round).registers a).1 := by
  change (state.registers a).1 ≤
    (Bandits.Support.QueueReplay.transition (4 * parameters.n)
      (state.registers a) (RecordedQueueRun.acceptedRecord parameters state round a)).1
  cases hrecord : RecordedQueueRun.acceptedRecord parameters state round a with
  | mk enabled arrival =>
      cases enabled <;> simp [Bandits.Support.QueueReplay.transition]

private theorem execute_score_ge (parameters : RecordedQueueRun.Parameters)
    (rounds : List (RecordedQueueRun.RoundInput p.K))
    (state : RecordedQueueRun.RunState p.K) (a : Fin p.K) :
    (state.registers a).1 ≤
      ((RecordedQueueRun.execute parameters rounds state).registers a).1 := by
  induction rounds generalizing state with
  | nil => simp [RecordedQueueRun.execute]
  | cons round rest ih =>
      simp only [RecordedQueueRun.execute]
      exact (step_score_ge parameters state round a).trans
        (ih (RecordedQueueRun.step parameters state round))

/-- Scores in the actual finite run are monotone across its take-prefixes. -/
theorem recordedPrefixScore_mono
    (parameters : RecordedQueueRun.Parameters)
    (rounds : List (RecordedQueueRun.RoundInput p.K))
    (start finish : ℕ) (hstart : start ≤ finish) (a : Fin p.K) :
    ((recordedQueuePrefix parameters rounds start).registers a).1 ≤
      ((recordedQueuePrefix parameters rounds finish).registers a).1 := by
  unfold recordedQueuePrefix
  rw [run_take_eq_execute_drop parameters rounds start finish hstart]
  exact execute_score_ge parameters ((rounds.drop start).take (finish - start))
    (RecordedQueueRun.run parameters (rounds.take start)) a

private theorem queueReplay_score_shift (capacity score backlog : ℕ)
    (records : List (Bool × ℕ)) :
    Bandits.Support.QueueReplay.replay capacity (score, backlog) records =
      (score + (Bandits.Support.QueueReplay.replay capacity (0, backlog) records).1,
        (Bandits.Support.QueueReplay.replay capacity (0, backlog) records).2) := by
  induction records generalizing score backlog with
  | nil => simp [Bandits.Support.QueueReplay.replay]
  | cons record rest ih =>
      have hstep : Bandits.Support.QueueReplay.transition capacity
          (score, backlog) record =
          (score + (Bandits.Support.QueueReplay.transition capacity
            (0, backlog) record).1,
            (Bandits.Support.QueueReplay.transition capacity
              (0, backlog) record).2) := by
        cases record with
        | mk enabled arrival =>
            cases enabled <;> simp [Bandits.Support.QueueReplay.transition]
      change Bandits.Support.QueueReplay.replay capacity
          (Bandits.Support.QueueReplay.transition capacity (score, backlog) record) rest =
        (score + (Bandits.Support.QueueReplay.replay capacity
          (Bandits.Support.QueueReplay.transition capacity (0, backlog) record) rest).1,
          (Bandits.Support.QueueReplay.replay capacity
            (Bandits.Support.QueueReplay.transition capacity (0, backlog) record) rest).2)
      rw [hstep]
      have hzero := ih
        (Bandits.Support.QueueReplay.transition capacity (0, backlog) record).1
        (Bandits.Support.QueueReplay.transition capacity (0, backlog) record).2
      rw [hzero]
      simpa [Nat.add_assoc] using
        ih (score + (Bandits.Support.QueueReplay.transition capacity
          (0, backlog) record).1)
          (Bandits.Support.QueueReplay.transition capacity (0, backlog) record).2

/-- If the checked input records are the exact chronological segment between
two actual recorded-run prefixes, replay from the earlier actual registers
reaches the later actual registers. -/
private theorem recordedPrefix_replay_segment
    (parameters : RecordedQueueRun.Parameters)
    (rounds : List (RecordedQueueRun.RoundInput p.K))
    (start finish : ℕ)
    (a : Fin p.K) (records : List (Bool × ℕ))
    (hrecords : (recordedQueuePrefix parameters rounds finish).records a =
      (recordedQueuePrefix parameters rounds start).records a ++ records) :
    Bandits.Support.QueueReplay.replay (4 * parameters.n)
        ((recordedQueuePrefix parameters rounds start).registers a) records =
      (recordedQueuePrefix parameters rounds finish).registers a := by
  have hstartReplay := RecordedQueueRun.run_replay_projection parameters
    (rounds.take start) a
  have hfinishReplay := RecordedQueueRun.run_replay_projection parameters
    (rounds.take finish) a
  change (recordedQueuePrefix parameters rounds start).registers a =
      Bandits.Support.QueueReplay.replay (4 * parameters.n) (0, 0)
        ((recordedQueuePrefix parameters rounds start).records a) at hstartReplay
  change (recordedQueuePrefix parameters rounds finish).registers a =
      Bandits.Support.QueueReplay.replay (4 * parameters.n) (0, 0)
        ((recordedQueuePrefix parameters rounds finish).records a) at hfinishReplay
  rw [hrecords, Bandits.Support.QueueReplay.replay_append] at hfinishReplay
  rw [← hstartReplay] at hfinishReplay
  exact hfinishReplay.symm

private theorem recordedPrefix_reset_replay
    (parameters : RecordedQueueRun.Parameters)
    (rounds : List (RecordedQueueRun.RoundInput p.K))
    (start finish : ℕ)
    (a : Fin p.K) (records : List (Bool × ℕ))
    (hrecords : (recordedQueuePrefix parameters rounds finish).records a =
      (recordedQueuePrefix parameters rounds start).records a ++ records) :
    Bandits.Support.QueueReplay.replay (4 * parameters.n)
        (0, ((recordedQueuePrefix parameters rounds start).registers a).2) records =
      (((recordedQueuePrefix parameters rounds finish).registers a).1 -
          ((recordedQueuePrefix parameters rounds start).registers a).1,
        ((recordedQueuePrefix parameters rounds finish).registers a).2) := by
  let startState := (recordedQueuePrefix parameters rounds start).registers a
  let finishState := (recordedQueuePrefix parameters rounds finish).registers a
  have hsegment := recordedPrefix_replay_segment parameters rounds start finish
    a records hrecords
  rw [queueReplay_score_shift] at hsegment
  have hscoreEq : startState.1 +
      (Bandits.Support.QueueReplay.replay (4 * parameters.n)
        (0, startState.2) records).1 = finishState.1 := by
    simpa [startState, finishState] using congrArg Prod.fst hsegment
  have hqueueEq : (Bandits.Support.QueueReplay.replay (4 * parameters.n)
      (0, startState.2) records).2 = finishState.2 := by
    simpa [startState, finishState] using congrArg Prod.snd hsegment
  change Bandits.Support.QueueReplay.replay (4 * parameters.n)
      (0, startState.2) records = (finishState.1 - startState.1, finishState.2)
  apply Prod.ext
  · change (Bandits.Support.QueueReplay.replay (4 * parameters.n)
      (0, startState.2) records).1 = finishState.1 - startState.1
    omega
  · exact hqueueEq

private theorem startAndRunChecked_success_fold
    (assignment : Assignment p) (sigma cutoff freezeAt : ℕ)
    (baseScore : Fin (p.m - 1) → ℕ)
    (outside : Fin p.K → Option CutoffRegister)
    (inputs : List (RoundInput (p := p) (eta := eta.val)))
    (execution : Execution p eta.val eta.property
      (payloadCap old) (payloadN old)
      (payloadN_eq old))
    (h : startAndRunChecked p eta.val eta.property
      (payloadCap old) (payloadN old)
      (payloadN_eq old) assignment sigma cutoff freezeAt
      baseScore outside inputs = .success execution) :
    startCollectionChecked p eta.val eta.property
        (payloadCap old) (payloadN old)
        (payloadN_eq old) assignment sigma cutoff freezeAt
        baseScore outside = .success execution.initial ∧
      checkedRounds execution.initial inputs =
        some (execution.accepted, execution.final) := by
  unfold startAndRunChecked at h
  cases hstart : startCollectionChecked p eta.val eta.property
      (payloadCap old) (payloadN old)
      (payloadN_eq old) assignment sigma cutoff freezeAt
      baseScore outside with
  | invalid => simp [hstart] at h
  | rejected bad => simp [hstart] at h
  | success initial =>
      cases hfold : checkedRounds initial inputs with
      | none => simp [hstart, hfold] at h
      | some pair =>
          simp only [hstart, hfold] at h
          injection h with hexecution
          have hinitial : execution.initial = initial := by
            cases hexecution
            rfl
          have haccepted : execution.accepted = pair.1 := by
            cases hexecution
            rfl
          have hfinal : execution.final = pair.2 := by
            cases hexecution
            rfl
          exact ⟨by simp [hinitial],
            by simpa [hinitial, haccepted, hfinal] using hfold⟩

private theorem startCollectionChecked_success_valid
    (assignment : Assignment p) (sigma cutoff freezeAt : ℕ)
    (baseScore : Fin (p.m - 1) → ℕ)
    (outside : Fin p.K → Option CutoffRegister)
    (initial : Ledger p eta.val eta.property
      (payloadCap old) (payloadN old)
      (payloadN_eq old))
    (h : startCollectionChecked p eta.val eta.property
      (payloadCap old) (payloadN old)
      (payloadN_eq old) assignment sigma cutoff freezeAt
      baseScore outside = .success initial) :
    validLedgerCheck initial = true := by
  unfold startCollectionChecked at h
  repeat (first | split at h | dsimp only at h)
  all_goals
    first
    | contradiction
    | (injection h with heq; cases heq; assumption)

private theorem finishRound_success_valid
    (l result : Ledger p eta.val eta.property
      (payloadCap old) (payloadN old)
      (payloadN_eq old))
    (h : finishRound l = .success result) : validLedgerCheck result = true := by
  unfold finishRound at h
  repeat (first | split at h | dsimp only at h)
  all_goals
    first
    | contradiction
    | (injection h with heq; cases heq; assumption)

private theorem checkedRounds_success_valid
    (l final : Ledger p eta.val eta.property
      (payloadCap old) (payloadN old)
      (payloadN_eq old))
    (inputs : List (RoundInput (p := p) (eta := eta.val)))
    (accepted : List Bool) (hvalid : validLedgerCheck l = true)
    (hfold : checkedRounds l inputs = some (accepted, final)) :
    validLedgerCheck final = true := by
  induction inputs generalizing l accepted final with
  | nil =>
      simp only [checkedRounds] at hfold
      rcases hfold with ⟨rfl, rfl⟩
      exact hvalid
  | cons input rest ih =>
      cases hstart : startRound l (sourceRound input.round) input.enabled input.raw with
      | invalid => simp [checkedRounds, hstart] at hfold
      | rejected bad => simp [checkedRounds, hstart] at hfold
      | success started =>
          cases hdecode : decodeUp started input.selectedFollower input.parsed with
          | invalid => simp [checkedRounds, hstart, hdecode] at hfold
          | rejected decoded =>
              cases hfinish : finishRound decoded with
              | invalid => simp [checkedRounds, hstart, hdecode, hfinish] at hfold
              | rejected bad => simp [checkedRounds, hstart, hdecode, hfinish] at hfold
              | success finished =>
                  cases htail : checkedRounds finished rest with
                  | none => simp [checkedRounds, hstart, hdecode, hfinish, htail] at hfold
                  | some pair =>
                      have hfold' : false :: pair.1 = accepted ∧ pair.2 = final := by
                        simpa [checkedRounds, hstart, hdecode, hfinish, htail] using hfold
                      rcases hfold' with ⟨rfl, rfl⟩
                      exact ih finished pair.2 pair.1
                        (finishRound_success_valid decoded finished hfinish) htail

          | success decoded =>
              cases hfinish : finishRound decoded with
              | invalid => simp [checkedRounds, hstart, hdecode, hfinish] at hfold
              | rejected bad => simp [checkedRounds, hstart, hdecode, hfinish] at hfold
              | success finished =>
                  cases htail : checkedRounds finished rest with
                  | none => simp [checkedRounds, hstart, hdecode, hfinish, htail] at hfold
                  | some pair =>
                      have hfold' : true :: pair.1 = accepted ∧ pair.2 = final := by
                        simpa [checkedRounds, hstart, hdecode, hfinish, htail] using hfold
                      rcases hfold' with ⟨rfl, rfl⟩
                      exact ih finished pair.2 pair.1
                        (finishRound_success_valid decoded finished hfinish) htail

private theorem checkedRounds_append
    (initial middle final : Ledger p eta.val eta.property
      (payloadCap old) (payloadN old) (payloadN_eq old))
    (first second : List (RoundInput (p := p) (eta := eta.val)))
    (acceptedFirst acceptedSecond : List Bool)
    (hfirst : checkedRounds initial first = some (acceptedFirst, middle))
    (hsecond : checkedRounds middle second = some (acceptedSecond, final)) :
    checkedRounds initial (first ++ second) =
      some (acceptedFirst ++ acceptedSecond, final) := by
  induction first generalizing initial acceptedFirst middle with
  | nil =>
      simp only [checkedRounds] at hfirst
      rcases hfirst with ⟨rfl, rfl⟩
      simpa using hsecond
  | cons input rest ih =>
      cases hstart : startRound initial (sourceRound input.round)
          input.enabled input.raw with
      | invalid => simp [checkedRounds, hstart] at hfirst
      | rejected bad => simp [checkedRounds, hstart] at hfirst
      | success started =>
          cases hdecode : decodeUp started input.selectedFollower input.parsed with
          | invalid => simp [checkedRounds, hstart, hdecode] at hfirst
          | success decoded =>
              cases hfinish : finishRound decoded with
              | invalid => simp [checkedRounds, hstart, hdecode, hfinish] at hfirst
              | rejected bad => simp [checkedRounds, hstart, hdecode, hfinish] at hfirst
              | success finished =>
                  cases htail : checkedRounds finished rest with
                  | none => simp [checkedRounds, hstart, hdecode, hfinish, htail] at hfirst
                  | some pair =>
                      have hfirst' : true :: pair.1 = acceptedFirst ∧
                          pair.2 = middle := by
                        simpa [checkedRounds, hstart, hdecode, hfinish, htail]
                          using hfirst
                      rcases hfirst' with ⟨rfl, rfl⟩
                      have hrest := ih finished pair.2 pair.1 htail hsecond
                      rw [List.cons_append]
                      simp only [checkedRounds, hstart, hdecode, hfinish]
                      rw [hrest]
                      rfl
          | rejected decoded =>
              cases hfinish : finishRound decoded with
              | invalid => simp [checkedRounds, hstart, hdecode, hfinish] at hfirst
              | rejected bad => simp [checkedRounds, hstart, hdecode, hfinish] at hfirst
              | success finished =>
                  cases htail : checkedRounds finished rest with
                  | none => simp [checkedRounds, hstart, hdecode, hfinish, htail] at hfirst
                  | some pair =>
                      have hfirst' : false :: pair.1 = acceptedFirst ∧
                          pair.2 = middle := by
                        simpa [checkedRounds, hstart, hdecode, hfinish, htail]
                          using hfirst
                      rcases hfirst' with ⟨rfl, rfl⟩
                      have hrest := ih finished pair.2 pair.1 htail hsecond
                      rw [List.cons_append]
                      simp only [checkedRounds, hstart, hdecode, hfinish]
                      rw [hrest]
                      rfl

private theorem allFin_eq_true_iff_local {length : ℕ}
    (test : Fin length → Bool) :
    allFin length test = true ↔ ∀ i, test i = true := by
  unfold allFin
  rw [List.all_eq_true]
  constructor
  · intro h i
    exact h (test i) (by simp)
  · intro h value hvalue
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hvalue
    exact h i

private theorem startCollectionChecked_success_inputs_valid
    (assignment : Assignment p) (sigma cutoff freezeAt : ℕ)
    (baseScore : Fin (p.m - 1) → ℕ)
    (outside : Fin p.K → Option CutoffRegister)
    (initial : Ledger p eta.val eta.property
      (payloadCap old) (payloadN old)
      (payloadN_eq old))
    (h : startCollectionChecked p eta.val eta.property
      (payloadCap old) (payloadN old)
      (payloadN_eq old) assignment sigma cutoff freezeAt
      baseScore outside = .success initial) :
    validInitialInputsCheck assignment sigma cutoff freezeAt baseScore outside = true := by
  unfold startCollectionChecked at h
  repeat (first | split at h | dsimp only at h)
  all_goals
    first
    | contradiction
    | injection h with heq

private theorem startCollectionChecked_success_initial
    (assignment : Assignment p) (sigma cutoff freezeAt : ℕ)
    (baseScore : Fin (p.m - 1) → ℕ)
    (outside : Fin p.K → Option CutoffRegister)
    (initial : Ledger p eta.val eta.property
      (payloadCap old) (payloadN old)
      (payloadN_eq old))
    (h : startCollectionChecked p eta.val eta.property
      (payloadCap old) (payloadN old)
      (payloadN_eq old) assignment sigma cutoff freezeAt
      baseScore outside = .success initial) :
    initial = {
      assignment := assignment
      sigma := sigma
      cutoff := cutoff
      freezeAt := freezeAt
      baseScore := baseScore
      pending := Finset.univ
      cutoffRegisters := outside
      currentRegisters := fun a => (outside a).map fun q => ⟨q.queue, q.lastService⟩
      increment := fun _ => 0
      gammaLoc := fun _ => 0
      rawBuffer := fun _ _ => none
      enabledHistory := fun _ => none
      cursor := cutoff
      phase := .ready
    } := by
  unfold startCollectionChecked at h
  repeat (first | split at h | dsimp only at h)
  all_goals
    first
    | contradiction
    | (injection h with heq; cases heq; rfl)

private theorem outside_register_exists_of_unassigned
    (assignment : Assignment p) (sigma cutoff freezeAt : ℕ)
    (baseScore : Fin (p.m - 1) → ℕ)
    (outside : Fin p.K → Option CutoffRegister)
    (initial : Ledger p eta.val eta.property
      (payloadCap old) (payloadN old)
      (payloadN_eq old))
    (hinit : startCollectionChecked p eta.val eta.property
      (payloadCap old) (payloadN old)
      (payloadN_eq old) assignment sigma cutoff freezeAt
      baseScore outside = .success initial)
    (a : Fin p.K) (hnotAssigned : ¬ ∃ i, assignment.arm i = a) :
    ∃ register, outside a = some register := by
  have hinputs := startCollectionChecked_success_inputs_valid assignment sigma
    cutoff freezeAt baseScore outside initial hinit
  unfold validInitialInputsCheck at hinputs
  simp only [Bool.and_eq_true] at hinputs
  rcases hinputs with ⟨_, hall⟩
  have hentry := (allFin_eq_true_iff_local _).mp hall a
  have hany : anyFin (p.m - 1) (fun i : Fin (p.m - 1) =>
      decide (assignment.arm i = a)) = false := by
    cases h : anyFin (p.m - 1) (fun i : Fin (p.m - 1) =>
        decide (assignment.arm i = a)) with
    | false => rfl
    | true =>
        have hmem : ∃ b ∈ List.ofFn (fun i : Fin (p.m - 1) =>
            decide (assignment.arm i = a)), b = true := by
          apply List.any_eq_true.mp
          simpa [anyFin] using h
        obtain ⟨value, hmem, hvalue⟩ := hmem
        obtain ⟨i, hi⟩ := List.mem_ofFn.mp hmem
        have hassign : assignment.arm i = a := by
          exact of_decide_eq_true (hi.trans hvalue)
        exact False.elim (hnotAssigned ⟨i, hassign⟩)
  have houtsideTest : (match outside a with
      | none => false
      | some r => decide (r.score ≤ p.T * ConstructorDimensions.D p) &&
          decide (r.queue ≤ p.T * ConstructorDimensions.D p) &&
          decide (r.lastService ≤ ConstructorDimensions.D p)) = true := by
    have hcondition : ¬ (anyFin (p.m - 1) (fun i : Fin (p.m - 1) =>
        decide (assignment.arm i = a)) = true) := by
      simp [hany]
    rw [ite_eq_right hcondition] at hentry
    exact hentry
  cases houtside : outside a with
  | none => simp [houtside] at houtsideTest
  | some register => exact ⟨register, rfl⟩

private theorem recordedPrefix_registers_le
    (parameters : RecordedQueueRun.Parameters)
    (rounds : List (RecordedQueueRun.RoundInput p.K))
    (hD : parameters.D = ConstructorDimensions.D p)
    (horizon : rounds.length = p.T)
    (hfeasible : ∀ round ∈ rounds, ∀ a,
      (parameters.n : ℝ) ≤ (parameters.D : ℝ) * round.rate a)
    (prefixLength : ℕ)
    (a : Fin p.K) :
    ((recordedQueuePrefix parameters rounds prefixLength).registers a).1 ≤
        p.T * ConstructorDimensions.D p ∧
      ((recordedQueuePrefix parameters rounds prefixLength).registers a).2 ≤
        p.T * ConstructorDimensions.D p := by
  have hprefixFeasible : ∀ round ∈ rounds.take prefixLength, ∀ i,
      (parameters.n : ℝ) ≤ (parameters.D : ℝ) * round.rate i := by
    intro round hmem i
    have hsubset : rounds.take prefixLength <+: rounds := List.take_prefix _ _
    obtain ⟨suffix, hsplit⟩ := hsubset
    have hmem' : round ∈ rounds := by
      rw [← hsplit]
      exact List.mem_append.mpr (Or.inl hmem)
    exact hfeasible round hmem' i
  have hsum := RecordedQueueRun.run_score_add_backlog_le_prefixLength_mul_D
    parameters (rounds.take prefixLength) hprefixFeasible a
  have htakeLen : (rounds.take prefixLength).length ≤ p.T := by
    rw [List.length_take, horizon]
    exact Nat.min_le_right _ _
  have hmul : (rounds.take prefixLength).length * parameters.D ≤
      p.T * ConstructorDimensions.D p := by
    calc
      (rounds.take prefixLength).length * parameters.D ≤
          p.T * parameters.D := Nat.mul_le_mul_right parameters.D htakeLen
      _ = p.T * ConstructorDimensions.D p := by rw [hD]
  have htotal :
      ((recordedQueuePrefix parameters rounds prefixLength).registers a).1 +
          ((recordedQueuePrefix parameters rounds prefixLength).registers a).2 ≤
        p.T * ConstructorDimensions.D p := by
    simpa [recordedQueuePrefix, RecordedQueueRun.run] using hsum.trans hmul
  constructor <;> omega

/-- A successful checked fold returns a valid final ledger. This validity is
derived from the checked initializer and every actual successful operation. -/
theorem checked_collection_success_valid
    (assignment : Assignment p) (sigma cutoff freezeAt : ℕ)
    (baseScore : Fin (p.m - 1) → ℕ)
    (outside : Fin p.K → Option CutoffRegister)
    (inputs : List (RoundInput (p := p) (eta := eta.val)))
    (execution : Execution p eta.val eta.property (payloadCap old) (payloadN old)
      (payloadN_eq old))
    (hRun : startAndRunChecked p eta.val eta.property (payloadCap old) (payloadN old) (payloadN_eq old) assignment sigma cutoff freezeAt
      baseScore outside inputs = .success execution) :
    validLedgerCheck execution.final = true := by
  obtain ⟨hinit, hfold⟩ := startAndRunChecked_success_fold assignment sigma cutoff
    freezeAt baseScore outside inputs execution hRun
  exact checkedRounds_success_valid execution.initial execution.final inputs
    execution.accepted
    (startCollectionChecked_success_valid assignment sigma cutoff freezeAt
      baseScore outside execution.initial hinit) hfold

/-- For one actual successful checked collection, explicit source-prefix,
message, outside-register, and raw-record provenance identify every arm's
cutoff/current registers with the same supplied finite all-zero recorded run.

The accepted-UP premise is restricted to successful `decodeUp` steps in the
actual checked fold, and explicitly names the returned true acceptance flag.
No parser authenticity or physical UP generation is included. -/
theorem successful_collection_recorded_prefix_identities
    (assignment : Assignment p) (sigma cutoff freezeAt : ℕ)
    (baseScore : Fin (p.m - 1) → ℕ)
    (outside : Fin p.K → Option CutoffRegister)
    (inputs : List (RoundInput (p := p) (eta := eta.val)))
    (execution : Execution p eta.val eta.property
      (payloadCap old) (payloadN old) (payloadN_eq old))
    (runParameters : RecordedQueueRun.Parameters)
    (rounds : List (RecordedQueueRun.RoundInput p.K))
    (time : Fin p.T)
    (hRun : startAndRunChecked p eta.val eta.property (payloadCap old)
      (payloadN old) (payloadN_eq old) assignment sigma cutoff freezeAt
      baseScore outside inputs = .success execution)
    (hempty : execution.final.pending = ∅)
    (hsourceSigma : sigma = old.sigma.val + 1)
    (hsigmaCutoff : sigma < cutoff)
    (hfinalTime : execution.final.cursor = time.val + 1)
    (hD : runParameters.D = ConstructorDimensions.D p)
    (hN : runParameters.n = payloadN old)
    (_hEta : runParameters.eta = eta.val)
    (horizon : rounds.length = p.T)
    (hfeasible : ∀ round ∈ rounds, ∀ a,
      (runParameters.n : ℝ) ≤ (runParameters.D : ℝ) * round.rate a)
    (hbase : ∀ i, baseScore i =
      recordedScoreBefore runParameters rounds sigma (assignment.arm i))
    (houtside : ∀ a register, outside a = some register →
      register.score = recordedScoreBefore runParameters rounds cutoff a ∧
      register.queue = recordedQueueBefore runParameters rounds cutoff a ∧
      register.lastService = recordedPrecedingService
        runParameters rounds cutoff a)
    (hacceptedUP : ∀ (i : Fin (p.m - 1))
        (pre : List (RoundInput (p := p) (eta := eta.val)))
        (input : RoundInput (p := p) (eta := eta.val))
        (suffix : List (RoundInput (p := p) (eta := eta.val)))
        (prefixAccepted : List Bool)
        (before started decoded finished : Ledger p eta.val eta.property
          (payloadCap old) (payloadN old) (payloadN_eq old))
        (suffixAccepted : List Bool)
        (M : Bandits.Support.OrdinaryMessageCodec.UpRecord
          (Bandits.Support.ReferencePrelaunchFollower.codecParams p eta)),
      inputs = pre ++ input :: suffix →
      input.selectedFollower = i → input.parsed = some M →
      checkedRounds execution.initial pre = some (prefixAccepted, before) →
      before.currentRegisters (execution.initial.assignment.arm i) = none →
      startRound before (sourceRound input.round) input.enabled input.raw =
        .success started →
      decodeUp started input.selectedFollower input.parsed = .success decoded →
      finishRound decoded = .success finished →
      checkedRounds finished suffix = some (suffixAccepted, execution.final) →
      execution.accepted = prefixAccepted ++ true :: suffixAccepted →
      M.val.S = recordedScoreBefore runParameters rounds cutoff
          (assignment.arm i) -
        recordedScoreBefore runParameters rounds sigma (assignment.arm i) ∧
      M.val.q = recordedQueueBefore runParameters rounds cutoff
        (assignment.arm i) ∧
      M.val.delta = recordedPrecedingService runParameters rounds cutoff
        (assignment.arm i))
    (hrecordSegment : ∀ a,
      (recordedQueuePrefix runParameters rounds time.val).records a =
        (recordedQueuePrefix runParameters rounds (cutoff - 1)).records a ++
          Bandits.Support.CollectionKnownQueueContinuation.inputQueueRecords
            execution.initial a inputs) :
    ∀ a, ∃ cutoffRegister currentRegister,
      execution.final.cutoffRegisters a = some cutoffRegister ∧
      execution.final.currentRegisters a = some currentRegister ∧
      cutoffRegister.score = recordedScoreBefore runParameters rounds cutoff a ∧
      cutoffRegister.queue = recordedQueueBefore runParameters rounds cutoff a ∧
      cutoffRegister.lastService = recordedPrecedingService
        runParameters rounds cutoff a ∧
      currentRegister.queue = recordedQueueBefore runParameters rounds
        (time.val + 1) a ∧
      execution.final.increment a = recordedScoreBefore runParameters rounds
        (time.val + 1) a - recordedScoreBefore runParameters rounds cutoff a ∧
      cutoffRegister.score + execution.final.increment a =
        recordedScoreBefore runParameters rounds (time.val + 1) a ∧
      cutoffRegister.score - cutoffRegister.lastService =
        recordedScoreBefore runParameters rounds (cutoff - 1) a ∧
      cutoffRegister.lastService ≤ cutoffRegister.score ∧
      cutoffRegister.score - cutoffRegister.lastService ≤
        p.T * ConstructorDimensions.D p ∧
      cutoffRegister.score + execution.final.increment a ≤
        p.T * ConstructorDimensions.D p ∧
      currentRegister.queue ≤ p.T * ConstructorDimensions.D p ∧
      Bandits.Support.ScoreWeights.scoreWeight
          (AssignmentScoreReconstruction.sourceWeightBase p)
          (cutoffRegister.score + execution.final.increment a) =
        RecordedQueueRun.scoreWeight runParameters
          (recordedQueuePrefix runParameters rounds time.val) a ∧
      Bandits.Support.ScoreWeights.scoreWeight
          (AssignmentScoreReconstruction.sourceWeightBase p)
          cutoffRegister.score =
        RecordedQueueRun.scoreWeight runParameters
          (recordedQueuePrefix runParameters rounds (cutoff - 1)) a ∧
      Bandits.Support.ScoreWeights.scoreWeight
          (AssignmentScoreReconstruction.sourceWeightBase p)
          (cutoffRegister.score - cutoffRegister.lastService) =
        RecordedQueueRun.scoreWeight runParameters
          (recordedQueuePrefix runParameters rounds (cutoff - 2)) a := by
  classical
  intro a
  obtain ⟨hinit, hfold⟩ := startAndRunChecked_success_fold assignment sigma cutoff
    freezeAt baseScore outside inputs execution hRun
  have hinitShape := startCollectionChecked_success_initial assignment sigma cutoff
    freezeAt baseScore outside execution.initial hinit
  have hinitialAssignment : execution.initial.assignment = assignment := by
    simp [hinitShape]
  have hinitialCursor : execution.initial.cursor = cutoff := by
    simp [hinitShape]
  have hchronology := CollectionCheckedExecution.startAndRunChecked_success_chronology
    p eta.val eta.property (payloadCap old) (payloadN old) (payloadN_eq old)
    assignment sigma cutoff freezeAt baseScore outside inputs execution hRun
  have hcursorAlignment : cutoff + inputs.length = time.val + 1 := by
    omega
  have hcutoffPrefixLe : cutoff - 1 ≤ time.val := by omega
  have hsigmaIndex : sigma - 1 = old.sigma.val := by omega
  have htimeIndex : time.val + 1 - 1 = time.val := by omega
  have hprevIndex : cutoff - 1 - 1 = cutoff - 2 := by omega
  have hsegment : ∀ arm,
      Bandits.Support.QueueReplay.replay (4 * runParameters.n)
        (0, recordedQueueBefore runParameters rounds cutoff arm)
        (Bandits.Support.CollectionKnownQueueContinuation.inputQueueRecords
          execution.initial arm inputs) =
        (recordedScoreBefore runParameters rounds (time.val + 1) arm -
            recordedScoreBefore runParameters rounds cutoff arm,
          recordedQueueBefore runParameters rounds (time.val + 1) arm) := by
    intro arm
    have h := recordedPrefix_reset_replay runParameters rounds (cutoff - 1)
      time.val arm
      (Bandits.Support.CollectionKnownQueueContinuation.inputQueueRecords
        execution.initial arm inputs) (hrecordSegment arm)
    simpa [recordedScoreBefore, recordedQueueBefore] using h
  have hscoreOrderFinal : ∀ arm,
      recordedScoreBefore runParameters rounds cutoff arm ≤
        recordedScoreBefore runParameters rounds (time.val + 1) arm := by
    intro arm
    unfold recordedScoreBefore
    rw [htimeIndex]
    exact recordedPrefixScore_mono runParameters rounds (cutoff - 1) time.val
      hcutoffPrefixLe arm
  have hscoreOrderPrevious : ∀ arm,
      recordedScoreBefore runParameters rounds (cutoff - 1) arm ≤
        recordedScoreBefore runParameters rounds cutoff arm := by
    intro arm
    unfold recordedScoreBefore
    rw [hprevIndex]
    exact recordedPrefixScore_mono runParameters rounds (cutoff - 2)
      (cutoff - 1) (by omega) arm
  have hcurrentBounds : ∀ arm,
      recordedScoreBefore runParameters rounds (time.val + 1) arm ≤
        p.T * ConstructorDimensions.D p ∧
      recordedQueueBefore runParameters rounds (time.val + 1) arm ≤
        p.T * ConstructorDimensions.D p := by
    intro arm
    have hb := recordedPrefix_registers_le runParameters rounds hD horizon
      hfeasible time.val arm
    simpa [recordedScoreBefore, recordedQueueBefore, htimeIndex] using hb
  have hpreviousBounds : ∀ arm,
      recordedScoreBefore runParameters rounds (cutoff - 1) arm ≤
        p.T * ConstructorDimensions.D p := by
    intro arm
    have hb := recordedPrefix_registers_le runParameters rounds hD horizon
      hfeasible (cutoff - 2) arm
    simpa [recordedScoreBefore, hprevIndex] using hb.1
  by_cases hassigned : ∃ i, assignment.arm i = a
  · obtain ⟨i, hi⟩ := hassigned
    obtain ⟨pre, input, suffix, prefixAccepted, before, started, decoded,
        finished, suffixAccepted, M, hsplit, hselected, hparsed, hprefixFold,
        hbeforeUnknown, hstart, hdecode, hfinish, hsuffix, _, hcurrentRaw,
        hincrementRaw, hcutoffRaw, _, _, _, _, _, _, _⟩ :=
      CollectionFullInputReplay.assigned_follower_full_input_queue_replay_of_empty_pending
        assignment sigma cutoff freezeAt baseScore outside inputs execution i hRun hempty
    have hsingle : checkedRounds before [input] = some ([true], finished) := by
      simp [checkedRounds, hstart, hdecode, hfinish]
    have hprefixThenInput := checkedRounds_append execution.initial before finished
      pre [input] prefixAccepted [true] hprefixFold hsingle
    have hprefixThenInputThenSuffix := checkedRounds_append execution.initial
      finished execution.final (pre ++ [input]) suffix (prefixAccepted ++ [true])
      suffixAccepted hprefixThenInput hsuffix
    have hwhole : checkedRounds execution.initial inputs =
        some (prefixAccepted ++ true :: suffixAccepted, execution.final) := by
      rw [hsplit]
      simpa [List.append_assoc] using hprefixThenInputThenSuffix
    have hactualFlags := Option.some.inj (hfold.symm.trans hwhole)
    have hacceptedConcat : execution.accepted = prefixAccepted ++ true :: suffixAccepted :=
      congrArg Prod.fst hactualFlags
    have hmessage := hacceptedUP i pre input suffix prefixAccepted before started
      decoded finished suffixAccepted M hsplit hselected hparsed hprefixFold
      hbeforeUnknown hstart hdecode hfinish hsuffix hacceptedConcat
    rcases hmessage with ⟨hmessageScore, hmessageQueue, hmessageService⟩
    have hbaseMono : recordedScoreBefore runParameters rounds sigma
        (assignment.arm i) ≤ recordedScoreBefore runParameters rounds cutoff
          (assignment.arm i) := by
      unfold recordedScoreBefore
      rw [hsigmaIndex]
      exact recordedPrefixScore_mono runParameters rounds old.sigma.val
        (cutoff - 1) (by omega) (assignment.arm i)
    have hcutoffScore : baseScore i + M.val.S =
        recordedScoreBefore runParameters rounds cutoff (assignment.arm i) := by
      rw [hbase i, hmessageScore]
      omega
    have hcutoffRaw' : execution.final.cutoffRegisters (assignment.arm i) =
        some ⟨baseScore i + M.val.S, M.val.q, M.val.delta⟩ := by
      simpa [hinitialAssignment] using hcutoffRaw
    have hcutoffEq : execution.final.cutoffRegisters (assignment.arm i) =
        some ⟨recordedScoreBefore runParameters rounds cutoff (assignment.arm i),
          recordedQueueBefore runParameters rounds cutoff (assignment.arm i),
          recordedPrecedingService runParameters rounds cutoff (assignment.arm i)⟩ := by
      rw [hcutoffScore, hmessageQueue, hmessageService] at hcutoffRaw'
      exact hcutoffRaw'
    have hsegmentPayload :
        Bandits.Support.QueueReplay.replay (4 * payloadN old)
          (0, M.val.q)
          (Bandits.Support.CollectionKnownQueueContinuation.inputQueueRecords
            execution.initial (assignment.arm i) inputs) =
          (recordedScoreBefore runParameters rounds (time.val + 1)
              (assignment.arm i) -
            recordedScoreBefore runParameters rounds cutoff (assignment.arm i),
            recordedQueueBefore runParameters rounds (time.val + 1)
              (assignment.arm i)) := by
      have h := hsegment (assignment.arm i)
      rw [hN, ← hmessageQueue] at h
      exact h
    have hcurrentRaw' : execution.final.currentRegisters (assignment.arm i) =
        some ⟨
          (Bandits.Support.QueueReplay.replay (4 * payloadN old) (0, M.val.q)
            (Bandits.Support.CollectionKnownQueueContinuation.inputQueueRecords
              execution.initial (assignment.arm i) inputs)).2,
          Bandits.Support.CollectionKnownQueueContinuation.replayLastService
            (4 * payloadN old) (0, M.val.q) M.val.delta
            (Bandits.Support.CollectionKnownQueueContinuation.inputQueueRecords
              execution.initial (assignment.arm i) inputs)⟩ := by
      simpa [hinitialAssignment] using hcurrentRaw
    have hincrementReplay : execution.final.increment (assignment.arm i) =
        (Bandits.Support.QueueReplay.replay (4 * payloadN old) (0, M.val.q)
          (Bandits.Support.CollectionKnownQueueContinuation.inputQueueRecords
            execution.initial (assignment.arm i) inputs)).1 := by
      simpa [hinitialAssignment] using hincrementRaw
    have hincrementEq : execution.final.increment (assignment.arm i) =
        recordedScoreBefore runParameters rounds (time.val + 1) (assignment.arm i) -
          recordedScoreBefore runParameters rounds cutoff (assignment.arm i) := by
      rw [hincrementReplay]
      exact congrArg Prod.fst hsegmentPayload
    let currentRegister : CurrentRegister := ⟨
      (Bandits.Support.QueueReplay.replay (4 * payloadN old) (0, M.val.q)
        (Bandits.Support.CollectionKnownQueueContinuation.inputQueueRecords
          execution.initial (assignment.arm i) inputs)).2,
      Bandits.Support.CollectionKnownQueueContinuation.replayLastService
        (4 * payloadN old) (0, M.val.q) M.val.delta
        (Bandits.Support.CollectionKnownQueueContinuation.inputQueueRecords
          execution.initial (assignment.arm i) inputs)⟩
    have hcurrentQueue : currentRegister.queue =
        recordedQueueBefore runParameters rounds (time.val + 1) (assignment.arm i) := by
      simpa [currentRegister] using congrArg Prod.snd hsegmentPayload
    have hcurrentEq : execution.final.currentRegisters (assignment.arm i) =
        some currentRegister := by
      simpa [currentRegister] using hcurrentRaw'
    have hscoreCurrent :
        recordedScoreBefore runParameters rounds cutoff (assignment.arm i) +
          execution.final.increment (assignment.arm i) =
        recordedScoreBefore runParameters rounds (time.val + 1) (assignment.arm i) := by
      rw [hincrementEq]
      have horder := hscoreOrderFinal (assignment.arm i)
      omega
    have hprevEq :
        recordedScoreBefore runParameters rounds cutoff (assignment.arm i) -
          recordedPrecedingService runParameters rounds cutoff (assignment.arm i) =
        recordedScoreBefore runParameters rounds (cutoff - 1) (assignment.arm i) := by
      unfold recordedPrecedingService
      have horder := hscoreOrderPrevious (assignment.arm i)
      omega
    have hweightsCurrent :
        Bandits.Support.ScoreWeights.scoreWeight
            (AssignmentScoreReconstruction.sourceWeightBase p)
            (recordedScoreBefore runParameters rounds (time.val + 1)
              (assignment.arm i)) =
          RecordedQueueRun.scoreWeight runParameters
            (recordedQueuePrefix runParameters rounds time.val)
            (assignment.arm i) := by
      simp [RecordedQueueRun.scoreWeight,
        AssignmentScoreReconstruction.sourceWeightBase, recordedScoreBefore,
        recordedQueuePrefix, hD]
    have hweightsCutoff :
        Bandits.Support.ScoreWeights.scoreWeight
            (AssignmentScoreReconstruction.sourceWeightBase p)
            (recordedScoreBefore runParameters rounds cutoff (assignment.arm i)) =
          RecordedQueueRun.scoreWeight runParameters
            (recordedQueuePrefix runParameters rounds (cutoff - 1)) (assignment.arm i) := by
      simp [RecordedQueueRun.scoreWeight,
        AssignmentScoreReconstruction.sourceWeightBase, recordedScoreBefore,
        recordedQueuePrefix, hD]
    have hweightsPrevious :
        Bandits.Support.ScoreWeights.scoreWeight
            (AssignmentScoreReconstruction.sourceWeightBase p)
            (recordedScoreBefore runParameters rounds (cutoff - 1)
              (assignment.arm i)) =
          RecordedQueueRun.scoreWeight runParameters
            (recordedQueuePrefix runParameters rounds (cutoff - 2))
            (assignment.arm i) := by
      simp [RecordedQueueRun.scoreWeight,
        AssignmentScoreReconstruction.sourceWeightBase, recordedScoreBefore,
        recordedQueuePrefix, hD, hprevIndex]
    have hcutoffPresent : execution.final.cutoffRegisters a = some
        ⟨recordedScoreBefore runParameters rounds cutoff a,
          recordedQueueBefore runParameters rounds cutoff a,
          recordedPrecedingService runParameters rounds cutoff a⟩ := by
      simpa [hi] using hcutoffEq
    have hcurrentPresent : execution.final.currentRegisters a = some currentRegister := by
      simpa [hi] using hcurrentEq
    have hqueueCurrent : currentRegister.queue =
        recordedQueueBefore runParameters rounds (time.val + 1) a := by
      simpa [hi] using hcurrentQueue
    have hincrement : execution.final.increment a =
        recordedScoreBefore runParameters rounds (time.val + 1) a -
          recordedScoreBefore runParameters rounds cutoff a := by
      simpa [hi] using hincrementEq
    have hscoreCurrent' :
        recordedScoreBefore runParameters rounds cutoff a +
          execution.final.increment a =
        recordedScoreBefore runParameters rounds (time.val + 1) a := by
      simpa [hi] using hscoreCurrent
    have hprevEq' :
        recordedScoreBefore runParameters rounds cutoff a -
          recordedPrecedingService runParameters rounds cutoff a =
        recordedScoreBefore runParameters rounds (cutoff - 1) a := by
      simpa [hi] using hprevEq
    have hserviceGuard :
        recordedPrecedingService runParameters rounds cutoff a ≤
          recordedScoreBefore runParameters rounds cutoff a := by
      unfold recordedPrecedingService
      exact Nat.sub_le _ _
    have hprevBound :
        recordedScoreBefore runParameters rounds cutoff a -
          recordedPrecedingService runParameters rounds cutoff a ≤
            p.T * ConstructorDimensions.D p := by
      rw [hprevEq']
      exact hpreviousBounds a
    have hcurrentScoreBound :
        recordedScoreBefore runParameters rounds cutoff a +
          execution.final.increment a ≤ p.T * ConstructorDimensions.D p := by
      rw [hscoreCurrent']
      exact (hcurrentBounds a).1
    have hcurrentQueueBound :
        currentRegister.queue ≤ p.T * ConstructorDimensions.D p := by
      rw [hqueueCurrent]
      exact (hcurrentBounds a).2
    refine ⟨⟨recordedScoreBefore runParameters rounds cutoff a,
        recordedQueueBefore runParameters rounds cutoff a,
        recordedPrecedingService runParameters rounds cutoff a⟩,
      currentRegister, hcutoffPresent, hcurrentPresent, rfl, rfl, rfl,
      hqueueCurrent, hincrement, hscoreCurrent', hprevEq', hserviceGuard,
      hprevBound, hcurrentScoreBound, hcurrentQueueBound, ?_, ?_, ?_⟩
    · simpa [hi, hscoreCurrent'] using hweightsCurrent
    · simpa [hi] using hweightsCutoff
    · simpa [hi, hprevEq'] using hweightsPrevious
  · obtain ⟨register, houtsideArm⟩ :=
      outside_register_exists_of_unassigned assignment sigma cutoff freezeAt
        baseScore outside execution.initial hinit a hassigned
    obtain ⟨hregisterScore, hregisterQueue, hregisterService⟩ :=
      houtside a register houtsideArm
    have hinitialCutoff : execution.initial.cutoffRegisters a = some register := by
      rw [hinitShape]
      simp [houtsideArm]
    have hinitialKnown : execution.initial.currentRegisters a =
        some ⟨register.queue, register.lastService⟩ := by
      rw [hinitShape]
      simp [houtsideArm]
    have hinitialIncrement : execution.initial.increment a = 0 := by
      rw [hinitShape]
    have hcontinuation :=
      CollectionKnownQueueContinuation.checkedRounds_known_queue_continuation
        execution.initial execution.final a ⟨register.queue, register.lastService⟩
        inputs execution.accepted hinitialKnown hfold
    rcases hcontinuation with
      ⟨hcurrentRaw, hincrementRaw, _, _, _, _, hcutoffPreserved⟩
    have hcutoffEq : execution.final.cutoffRegisters a = some
        ⟨recordedScoreBefore runParameters rounds cutoff a,
          recordedQueueBefore runParameters rounds cutoff a,
          recordedPrecedingService runParameters rounds cutoff a⟩ := by
      have hfinalCutoff := hcutoffPreserved.trans hinitialCutoff
      have hregisterEq : register =
          ⟨recordedScoreBefore runParameters rounds cutoff a,
            recordedQueueBefore runParameters rounds cutoff a,
            recordedPrecedingService runParameters rounds cutoff a⟩ := by
        cases register with
        | mk score queue lastService =>
            simp only [CutoffRegister.mk.injEq]
            exact ⟨hregisterScore, hregisterQueue, hregisterService⟩
      rw [hregisterEq] at hfinalCutoff
      exact hfinalCutoff
    have hsegOutside :
        Bandits.Support.QueueReplay.replay (4 * payloadN old)
          (0, register.queue)
          (Bandits.Support.CollectionKnownQueueContinuation.inputQueueRecords
            execution.initial a inputs) =
          (recordedScoreBefore runParameters rounds (time.val + 1) a -
              recordedScoreBefore runParameters rounds cutoff a,
            recordedQueueBefore runParameters rounds (time.val + 1) a) := by
      simpa [hN, hregisterQueue] using hsegment a
    have hincrement : execution.final.increment a =
        recordedScoreBefore runParameters rounds (time.val + 1) a -
          recordedScoreBefore runParameters rounds cutoff a := by
      calc
        execution.final.increment a =
            (Bandits.Support.QueueReplay.replay (4 * payloadN old)
              (0, register.queue)
              (Bandits.Support.CollectionKnownQueueContinuation.inputQueueRecords
                execution.initial a inputs)).1 := by
          simpa [hinitialKnown, hinitialIncrement] using hincrementRaw
        _ = recordedScoreBefore runParameters rounds (time.val + 1) a -
            recordedScoreBefore runParameters rounds cutoff a :=
          congrArg Prod.fst hsegOutside
    let currentRegister : CurrentRegister := ⟨
      (Bandits.Support.QueueReplay.replay (4 * payloadN old) (0, register.queue)
        (Bandits.Support.CollectionKnownQueueContinuation.inputQueueRecords
          execution.initial a inputs)).2,
      CollectionKnownQueueContinuation.replayLastService (4 * payloadN old)
        (0, register.queue) register.lastService
        (CollectionKnownQueueContinuation.inputQueueRecords execution.initial a inputs)⟩
    have hcurrent : execution.final.currentRegisters a = some currentRegister := by
      simpa [currentRegister, hinitialKnown, hinitialIncrement] using hcurrentRaw
    have hqueue : currentRegister.queue =
        recordedQueueBefore runParameters rounds (time.val + 1) a := by
      simpa [currentRegister] using congrArg Prod.snd hsegOutside
    have hscoreCurrent :
        recordedScoreBefore runParameters rounds cutoff a +
          execution.final.increment a =
        recordedScoreBefore runParameters rounds (time.val + 1) a := by
      rw [hincrement]
      have horder := hscoreOrderFinal a
      omega
    have hprevEq :
        recordedScoreBefore runParameters rounds cutoff a -
          recordedPrecedingService runParameters rounds cutoff a =
        recordedScoreBefore runParameters rounds (cutoff - 1) a := by
      unfold recordedPrecedingService
      have horder := hscoreOrderPrevious a
      omega
    have hserviceGuard :
        recordedPrecedingService runParameters rounds cutoff a ≤
          recordedScoreBefore runParameters rounds cutoff a := by
      unfold recordedPrecedingService
      exact Nat.sub_le _ _
    have hprevBound :
        recordedScoreBefore runParameters rounds cutoff a -
          recordedPrecedingService runParameters rounds cutoff a ≤
            p.T * ConstructorDimensions.D p := by
      rw [hprevEq]
      exact hpreviousBounds a
    have hcurrentScoreBound :
        recordedScoreBefore runParameters rounds cutoff a +
          execution.final.increment a ≤ p.T * ConstructorDimensions.D p := by
      rw [hscoreCurrent]
      exact (hcurrentBounds a).1
    have hcurrentQueueBound :
        currentRegister.queue ≤ p.T * ConstructorDimensions.D p := by
      rw [hqueue]
      exact (hcurrentBounds a).2
    have hweightsCurrent :
        Bandits.Support.ScoreWeights.scoreWeight
            (AssignmentScoreReconstruction.sourceWeightBase p)
            (recordedScoreBefore runParameters rounds (time.val + 1) a) =
          RecordedQueueRun.scoreWeight runParameters
            (recordedQueuePrefix runParameters rounds time.val) a := by
      simp [RecordedQueueRun.scoreWeight,
        AssignmentScoreReconstruction.sourceWeightBase, recordedScoreBefore,
        recordedQueuePrefix, hD]
    have hweightsCutoff :
        Bandits.Support.ScoreWeights.scoreWeight
            (AssignmentScoreReconstruction.sourceWeightBase p)
            (recordedScoreBefore runParameters rounds cutoff a) =
          RecordedQueueRun.scoreWeight runParameters
            (recordedQueuePrefix runParameters rounds (cutoff - 1)) a := by
      simp [RecordedQueueRun.scoreWeight,
        AssignmentScoreReconstruction.sourceWeightBase, recordedScoreBefore,
        recordedQueuePrefix, hD]
    have hweightsPrevious :
        Bandits.Support.ScoreWeights.scoreWeight
            (AssignmentScoreReconstruction.sourceWeightBase p)
            (recordedScoreBefore runParameters rounds (cutoff - 1) a) =
          RecordedQueueRun.scoreWeight runParameters
            (recordedQueuePrefix runParameters rounds (cutoff - 2)) a := by
      simp [RecordedQueueRun.scoreWeight,
        AssignmentScoreReconstruction.sourceWeightBase, recordedScoreBefore,
        recordedQueuePrefix, hD, hprevIndex]
    refine ⟨⟨recordedScoreBefore runParameters rounds cutoff a,
        recordedQueueBefore runParameters rounds cutoff a,
        recordedPrecedingService runParameters rounds cutoff a⟩,
      currentRegister, hcutoffEq, hcurrent, rfl, rfl, rfl, hqueue,
      hincrement, hscoreCurrent, hprevEq, hserviceGuard, hprevBound,
      hcurrentScoreBound, hcurrentQueueBound, ?_, ?_, ?_⟩
    · simpa [hscoreCurrent] using hweightsCurrent
    · exact hweightsCutoff
    · simpa [hprevEq] using hweightsPrevious

/-- Apply the existing later-start reconstruction to the actual completed
checked ledger. The register identities, output-domain checks, and checked
success are all consequences of the explicit provenance and the recorded-run
prefix bounds above. -/
theorem successful_collection_later_start_reconstruction
    (assignment : Assignment p) (sigma cutoff freezeAt : ℕ)
    (baseScore : Fin (p.m - 1) → ℕ)
    (outside : Fin p.K → Option CutoffRegister)
    (inputs : List (RoundInput (p := p) (eta := eta.val)))
    (execution : Execution p eta.val eta.property
      (payloadCap old) (payloadN old) (payloadN_eq old))
    (runParameters : RecordedQueueRun.Parameters)
    (rounds : List (RecordedQueueRun.RoundInput p.K))
    (instruction : Bandits.Support.CoordinatorPhaseClock.AssignmentStartInstruction p)
    (hRun : startAndRunChecked p eta.val eta.property (payloadCap old)
      (payloadN old) (payloadN_eq old) assignment sigma cutoff freezeAt
      baseScore outside inputs = .success execution)
    (hempty : execution.final.pending = ∅)
    (hsourceSigma : sigma = old.sigma.val + 1)
    (hsigmaCutoff : sigma < cutoff)
    (hfinalTime : execution.final.cursor = instruction.time.val + 1)
    (hkind : instruction.kind =
      AssignmentScoreReconstruction.expectedLaterStartKind
        execution.final.freezeAt instruction.time)
    (hD : runParameters.D = ConstructorDimensions.D p)
    (hN : runParameters.n = payloadN old)
    (_hEta : runParameters.eta = eta.val)
    (horizon : rounds.length = p.T)
    (hfeasible : ∀ round ∈ rounds, ∀ a,
      (runParameters.n : ℝ) ≤ (runParameters.D : ℝ) * round.rate a)
    (hbase : ∀ i, baseScore i =
      recordedScoreBefore runParameters rounds sigma (assignment.arm i))
    (houtside : ∀ a register, outside a = some register →
      register.score = recordedScoreBefore runParameters rounds cutoff a ∧
      register.queue = recordedQueueBefore runParameters rounds cutoff a ∧
      register.lastService = recordedPrecedingService
        runParameters rounds cutoff a)
    (hacceptedUP : ∀ (i : Fin (p.m - 1))
        (pre : List (RoundInput (p := p) (eta := eta.val)))
        (input : RoundInput (p := p) (eta := eta.val))
        (suffix : List (RoundInput (p := p) (eta := eta.val)))
        (prefixAccepted : List Bool)
        (before started decoded finished : Ledger p eta.val eta.property
          (payloadCap old) (payloadN old) (payloadN_eq old))
        (suffixAccepted : List Bool)
        (M : Bandits.Support.OrdinaryMessageCodec.UpRecord
          (Bandits.Support.ReferencePrelaunchFollower.codecParams p eta)),
      inputs = pre ++ input :: suffix →
      input.selectedFollower = i → input.parsed = some M →
      checkedRounds execution.initial pre = some (prefixAccepted, before) →
      before.currentRegisters (execution.initial.assignment.arm i) = none →
      startRound before (sourceRound input.round) input.enabled input.raw =
        .success started →
      decodeUp started input.selectedFollower input.parsed = .success decoded →
      finishRound decoded = .success finished →
      checkedRounds finished suffix = some (suffixAccepted, execution.final) →
      execution.accepted = prefixAccepted ++ true :: suffixAccepted →
      M.val.S = recordedScoreBefore runParameters rounds cutoff
          (assignment.arm i) -
        recordedScoreBefore runParameters rounds sigma (assignment.arm i) ∧
      M.val.q = recordedQueueBefore runParameters rounds cutoff
        (assignment.arm i) ∧
      M.val.delta = recordedPrecedingService runParameters rounds cutoff
        (assignment.arm i))
    (hrecordSegment : ∀ a,
      (recordedQueuePrefix runParameters rounds instruction.time.val).records a =
        (recordedQueuePrefix runParameters rounds (cutoff - 1)).records a ++
          Bandits.Support.CollectionKnownQueueContinuation.inputQueueRecords
            execution.initial a inputs) :
    AssignmentScoreReconstruction.currentOutputDomainsCheck execution.final = true ∧
    AssignmentScoreReconstruction.previousOutputDomainsCheck execution.final
      instruction = true ∧
    AssignmentScoreReconstruction.isSuccess
      (AssignmentScoreReconstruction.reconstructLaterStart execution.final
        instruction) = true := by
  let identities := successful_collection_recorded_prefix_identities
    assignment sigma cutoff freezeAt baseScore outside inputs execution
    runParameters rounds instruction.time hRun hempty hsourceSigma hsigmaCutoff
    hfinalTime hD hN _hEta horizon hfeasible hbase houtside hacceptedUP
    hrecordSegment
  have hcurrentCheck :
      AssignmentScoreReconstruction.currentOutputDomainsCheck execution.final = true := by
    unfold AssignmentScoreReconstruction.currentOutputDomainsCheck
    apply (allFin_eq_true_iff_local _).2
    intro a
    obtain ⟨register, current, hcutoff, hcurrent, _, _, _, _, _, _, _, _, _,
        hcurrentScoreBound, hcurrentQueueBound, _, _, _⟩ := identities a
    rw [hcutoff, hcurrent]
    simp [hcurrentScoreBound, hcurrentQueueBound]
  have hpreviousCheck :
      AssignmentScoreReconstruction.previousOutputDomainsCheck execution.final
        instruction = true := by
    by_cases hcorrected : instruction.time.val + 1 < execution.final.freezeAt
    · unfold AssignmentScoreReconstruction.previousOutputDomainsCheck
      rw [ite_eq_left hcorrected]
      apply (allFin_eq_true_iff_local _).2
      intro a
      obtain ⟨register, current, hcutoff, hcurrent, _, _, _, _, _, _, _,
        hserviceGuard, hpreviousScoreBound, _, _, _, _, _⟩ := identities a
      rw [hcutoff]
      simp [hserviceGuard, hpreviousScoreBound]
    · have hrenewal : execution.final.freezeAt ≤ instruction.time.val + 1 := by
        omega
      simp [AssignmentScoreReconstruction.previousOutputDomainsCheck,
        hrenewal]
  have hvalid := checked_collection_success_valid assignment sigma cutoff
    freezeAt baseScore outside inputs execution hRun
  have hchronology := CollectionCheckedExecution.startAndRunChecked_success_chronology
    p eta.val eta.property (payloadCap old) (payloadN old) (payloadN_eq old)
    assignment sigma cutoff freezeAt baseScore outside inputs execution hRun
  have hsuccess :=
    (AssignmentScoreReconstruction.reconstructLaterStart_success_iff
      execution.final instruction).2
      ⟨hvalid, hchronology.2, hfinalTime, hempty, hkind, hcurrentCheck,
        hpreviousCheck⟩
  exact ⟨hcurrentCheck, hpreviousCheck, hsuccess⟩

end Bandits.Support.CollectionRecordedScoreRecovery

end
