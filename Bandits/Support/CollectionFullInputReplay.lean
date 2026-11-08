/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.CollectionBufferProvenance
public import Bandits.Support.CollectionKnownQueueContinuation

import Lean.Elab.Tactic.Omega

/-!
# Full checked collection replay for a recovered follower queue

The mathematical evidence is
`sources/zip4/manuscript/06_interruptions.tex:16-28,80-100,257-283`.
The theorem composes only the actual checked initializer, its chronological
fold, the accepted local UP computation, and the supplied per-round inputs.
It proves no physical source or message-authenticity claim.
-/

@[expose] public section

namespace Bandits.Support.CollectionFullInputReplay

open Bandits.Support.CoordinatorCollectionLedger
open Bandits.Support.CollectionCheckedExecution
open Bandits.Support.CollectionBufferProvenance
open Bandits.Support.CollectionKnownQueueContinuation
open Bandits.Support.OrdinaryMessageCodec
open Bandits.Support.QueueReplay

variable {p : ConstructorDimensions.Parameters}
variable {eta : ℝ} {heta : 0 < eta}
  {hcap : sourceLearningCap p eta} {n : ℕ}
  {hn : (n : ℝ) = eta * (ConstructorDimensions.D p : ℝ)}

/-- A successful checked initializer leaves every assigned follower arm
unknown.  This is derived from its checked input condition: assigned arms must
have no outside cutoff register. -/
private theorem startCollectionChecked_assigned_arm_unknown
    (assignment : Assignment p) (sigma cutoff freezeAt : ℕ)
    (baseScore : Fin (p.m - 1) → ℕ)
    (outside : Fin p.K → Option CutoffRegister)
    (initial : Ledger p eta heta hcap n hn) (i : Fin (p.m - 1))
    (hinit : startCollectionChecked p eta heta hcap n hn assignment sigma
      cutoff freezeAt baseScore outside = .success initial) :
    initial.currentRegisters (assignment.arm i) = none := by
  have hinputs : validInitialInputsCheck assignment sigma cutoff freezeAt
      baseScore outside = true := by
    unfold startCollectionChecked at hinit
    by_cases h : validInitialInputsCheck assignment sigma cutoff freezeAt
        baseScore outside = true
    · exact h
    · simp [h] at hinit
  have houtside : allFin p.K (fun a : Fin p.K =>
      if anyFin (p.m - 1) (fun j : Fin (p.m - 1) =>
          decide (assignment.arm j = a)) then
        decide (outside a = none)
      else
        match outside a with
        | none => false
        | some r => decide (r.score ≤ p.T * ConstructorDimensions.D p) &&
            decide (r.queue ≤ p.T * ConstructorDimensions.D p) &&
            decide (r.lastService ≤ ConstructorDimensions.D p)) = true := by
    have hparts := hinputs
    simp only [validInitialInputsCheck, Bool.and_eq_true] at hparts
    exact hparts.2
  let test : Fin p.K → Bool := fun a =>
    if anyFin (p.m - 1) (fun j : Fin (p.m - 1) =>
        decide (assignment.arm j = a)) then
      decide (outside a = none)
    else
      match outside a with
      | none => false
      | some r => decide (r.score ≤ p.T * ConstructorDimensions.D p) &&
          decide (r.queue ≤ p.T * ConstructorDimensions.D p) &&
          decide (r.lastService ≤ ConstructorDimensions.D p)
  have htest : test (assignment.arm i) = true := by
    have hall : ∀ b ∈ List.ofFn test, b = true := by
      have hall' : (List.ofFn test).all id = true := by
        simpa only [allFin, test] using houtside
      exact (List.all_eq_true.mp hall')
    have hmem : test (assignment.arm i) ∈ List.ofFn test :=
      List.mem_ofFn.mpr ⟨assignment.arm i, rfl⟩
    exact hall _ hmem
  have hany : anyFin (p.m - 1) (fun j : Fin (p.m - 1) =>
      decide (assignment.arm j = assignment.arm i)) = true := by
    have hmem : true ∈ List.ofFn (fun j : Fin (p.m - 1) =>
        decide (assignment.arm j = assignment.arm i)) := by
      exact List.mem_ofFn.mpr ⟨i, by simp⟩
    have hany' : (List.ofFn (fun j : Fin (p.m - 1) =>
        decide (assignment.arm j = assignment.arm i))).any id = true :=
      List.any_eq_true.mpr ⟨true, hmem, rfl⟩
    simpa only [anyFin] using hany'
  have houtsideArm : outside (assignment.arm i) = none := by
    have htest' := htest
    simp [test, hany] at htest'
    exact htest'
  unfold startCollectionChecked at hinit
  by_cases hvalid : validInitialInputsCheck assignment sigma cutoff freezeAt
      baseScore outside = true
  · simp only [hvalid] at hinit
    let candidate : Ledger p eta heta hcap n hn := {
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
    by_cases hledger : validLedgerCheck candidate = true
    · simp [candidate, hledger] at hinit
      cases hinit
      simp [houtsideArm]
    · simp [candidate, hledger] at hinit
  · simp [hvalid] at hinit

private theorem allFin_eq_true_iff_local {length : ℕ}
    (test : Fin length → Bool) :
    allFin length test = true ↔ ∀ i, test i = true := by
  unfold allFin
  rw [List.all_eq_true]
  constructor
  · intro h i
    exact h (test i) (by simp)
  · intro h b hb
    obtain ⟨i, hi⟩ := (List.mem_ofFn.mp hb)
    subst b
    exact h i

private theorem armPendingCheck_eq_true_iff_local
    (l : Ledger p eta heta hcap n hn) (a : Fin p.K) :
    armPendingCheck l a = true ↔ armPending l a := by
  unfold armPendingCheck anyFin
  rw [List.any_eq_true]
  simp [armPending]

private theorem armPendingCheck_eq_false_of_empty
    (l : Ledger p eta heta hcap n hn) (hpending : l.pending = ∅)
    (a : Fin p.K) : armPendingCheck l a = false := by
  cases h : armPendingCheck l a with
  | false => rfl
  | true =>
      have hArm := (armPendingCheck_eq_true_iff_local l a).mp h
      rcases hArm with ⟨i, hi, _⟩
      simp [hpending] at hi

private theorem startCollectionChecked_success_valid
    (assignment : Assignment p) (sigma cutoff freezeAt : ℕ)
    (baseScore : Fin (p.m - 1) → ℕ)
    (outside : Fin p.K → Option CutoffRegister)
    (initial : Ledger p eta heta hcap n hn)
    (h : startCollectionChecked p eta heta hcap n hn assignment sigma cutoff
      freezeAt baseScore outside = .success initial) :
    validLedgerCheck initial = true := by
  unfold startCollectionChecked at h
  repeat (first | split at h | dsimp only at h)
  all_goals
    first
    | contradiction
    | (injection h with heq; cases heq; assumption)

private theorem finishRound_success_valid
    (l result : Ledger p eta heta hcap n hn)
    (h : finishRound l = .success result) : validLedgerCheck result = true := by
  unfold finishRound at h
  repeat (first | split at h | dsimp only at h)
  all_goals
    first
    | contradiction
    | (injection h with heq; cases heq; assumption)

private theorem checkedRounds_success_valid
    (l final : Ledger p eta heta hcap n hn)
    (inputs : List (RoundInput (p := p) (eta := eta)))
    (accepted : List Bool)
    (hvalid : validLedgerCheck l = true)
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
                        simpa [checkedRounds, hstart, hdecode, hfinish, htail]
                          using hfold
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
                        simpa [checkedRounds, hstart, hdecode, hfinish, htail]
                          using hfold
                      rcases hfold' with ⟨rfl, rfl⟩
                      exact ih finished pair.2 pair.1
                        (finishRound_success_valid decoded finished hfinish) htail

private theorem currentRegister_present_of_empty_pending
    (l : Ledger p eta heta hcap n hn)
    (hvalid : validLedgerCheck l = true) (hpending : l.pending = ∅)
    (a : Fin p.K) : ∃ current, l.currentRegisters a = some current := by
  have hconsistency : allFin p.K (fun b =>
      (l.currentRegisters b).isNone == armPendingCheck l b) = true := by
    have h := hvalid
    simp only [validLedgerCheck, Bool.and_eq_true] at h
    tauto
  have hentry := (allFin_eq_true_iff_local _).mp hconsistency a
  have hpendingArm := armPendingCheck_eq_false_of_empty l hpending a
  have hnotNone : (l.currentRegisters a).isNone = false := by
    simpa [hpendingArm] using hentry
  cases hregister : l.currentRegisters a with
  | none => simp [hregister] at hnotNone
  | some current => exact ⟨current, rfl⟩

/-- A chronological input list is recovered by its own unique round lookups
when `suppliedReplayRecords?` traverses its round labels. -/
private theorem suppliedReplayRecords?_map_aux
    (lookupInputs : List (RoundInput (p := p) (eta := eta)))
    (inputs : List (RoundInput (p := p) (eta := eta)))
    (a : Fin p.K) (freezeAt : ℕ)
    (hlookup : ∀ input ∈ inputs,
      findRoundInput? lookupInputs input.round = some input) :
    suppliedReplayRecords? lookupInputs a freezeAt
        (inputs.map RoundInput.round) =
      some (inputs.map fun input => suppliedReplayRecord input a freezeAt) := by
  induction inputs generalizing lookupInputs with
  | nil => rfl
  | cons head rest ih =>
      have hhead := hlookup head (by simp)
      have htail : ∀ input ∈ rest,
          findRoundInput? lookupInputs input.round = some input := by
        intro input hmem
        exact hlookup input (by simp [hmem])
      simp [suppliedReplayRecords?, hhead, ih lookupInputs htail]

private theorem suppliedReplayRecords?_map
    (inputs : List (RoundInput (p := p) (eta := eta)))
    (a : Fin p.K) (freezeAt : ℕ)
    (hlookup : ∀ input ∈ inputs,
      findRoundInput? inputs input.round = some input) :
    suppliedReplayRecords? inputs a freezeAt (inputs.map RoundInput.round) =
      some (inputs.map fun input => suppliedReplayRecord input a freezeAt) :=
  suppliedReplayRecords?_map_aux inputs inputs a freezeAt hlookup

/-- The decoder calendar pre is exactly the chronological input pre.
The successor split of `calendarIndices` follows from its existing `List.ofFn`
definition. -/
private theorem calendarIndices_succ (T start length : ℕ)
    (hbound : start + (length + 1) ≤ T) :
    calendarIndices T start (length + 1) hbound =
      (⟨start, by omega⟩ : Fin T) ::
        calendarIndices T (start + 1) length (by omega) := by
  simp only [calendarIndices, List.ofFn_succ]
  apply congrArg (fun tail => (⟨start, by omega⟩ : Fin T) :: tail)
  apply congrArg List.ofFn
  funext i
  apply Fin.ext
  simp
  omega

private theorem calendarIndices_eq_input_rounds
    (cursor : ℕ) (inputs : List (RoundInput (p := p) (eta := eta)))
    (hchron : chronologicalFrom cursor inputs)
    (hbound : cursor - 1 + inputs.length ≤ p.T) :
    calendarIndices p.T (cursor - 1) inputs.length (by omega) =
      inputs.map RoundInput.round := by
  induction inputs generalizing cursor with
  | nil => simp [calendarIndices]
  | cons head rest ih =>
      rcases hchron with ⟨hhead, htail⟩
      have hcursor : 1 ≤ cursor := by
        have hpos := head.round.isLt
        dsimp [sourceRound] at hhead
        omega
      have hbound' : cursor - 1 + (rest.length + 1) ≤ p.T := by
        simpa [List.length_cons] using hbound
      have htailBound : cursor + rest.length ≤ p.T := by
        omega
      have hsplit := calendarIndices_succ p.T (cursor - 1) rest.length hbound'
      have hfirst : (⟨cursor - 1, by omega⟩ : Fin p.T) = head.round := by
        apply Fin.ext
        dsimp [sourceRound] at hhead ⊢
        omega
      have htailIndices : calendarIndices p.T cursor rest.length
          (by omega) = rest.map RoundInput.round := by
        have h := ih (cursor + 1) htail (by omega)
        simpa using h
      simp only [List.length_cons]
      have hstart : cursor - 1 + 1 = cursor := by omega
      have hsplit' : calendarIndices p.T (cursor - 1) (rest.length + 1)
          hbound' =
        (⟨cursor - 1, by omega⟩ : Fin p.T) ::
          calendarIndices p.T cursor rest.length htailBound := by
        simpa [hstart] using hsplit
      rw [hsplit', hfirst, htailIndices]
      simp

/-- Append one input to a chronological pre using its actual next cursor. -/
private theorem chronologicalFrom_append_one
    (cursor : ℕ) (pre : List (RoundInput (p := p) (eta := eta)))
    (input : RoundInput (p := p) (eta := eta))
    (hchron : chronologicalFrom cursor pre)
    (hnext : sourceRound input.round = cursor + pre.length) :
    chronologicalFrom cursor (pre ++ [input]) := by
  induction pre generalizing cursor with
  | nil => simpa [chronologicalFrom] using hnext
  | cons head rest ih =>
      rcases hchron with ⟨hhead, htail⟩
      have hnext' : sourceRound input.round =
          (cursor + 1) + rest.length := by
        simp only [List.length_cons] at hnext
        omega
      exact ⟨hhead, ih (cursor + 1) htail hnext'⟩

private theorem decodeUp_none_not_success
    (l : Ledger p eta heta hcap n hn) (i : Fin (p.m - 1))
    (result : Ledger p eta heta hcap n hn) :
    decodeUp l i none ≠ .success result := by
  intro h
  by_cases hinput : validLedgerCheck l = true ∧ l.phase = .started ∧
      1 ≤ l.cutoff ∧ l.cutoff ≤ l.cursor ∧ l.cursor ≤ p.T
  · let next : Ledger p eta heta hcap n hn := { l with phase := .decoded }
    by_cases hvalid : validLedgerCheck next = true
    · simp [decodeUp, hinput, next, hvalid] at h
    · simp [decodeUp, hinput, next, hvalid] at h
  · simp [decodeUp, hinput] at h

/-- The queue replay ignores the raw arrival field of a disabled record.
`suppliedReplayRecord` keeps that raw value for provenance, while the existing
known-queue map stores zero on disabled rounds. -/
private theorem replay_supplied_map_eq_inputQueueRecords
    (capacity : ℕ) (initial : ℕ × ℕ)
    (l : Ledger p eta heta hcap n hn) (a : Fin p.K) (freezeAt : ℕ)
    (hfreeze : l.freezeAt = freezeAt)
    (inputs : List (RoundInput (p := p) (eta := eta))) :
    QueueReplay.replay capacity initial
        (inputs.map fun input => suppliedReplayRecord input a freezeAt) =
      QueueReplay.replay capacity initial (inputQueueRecords l a inputs) := by
  induction inputs generalizing initial with
  | nil => rfl
  | cons input rest ih =>
      change QueueReplay.replay capacity
          (QueueReplay.transition capacity initial
            (suppliedReplayRecord input a freezeAt))
          (rest.map fun input => suppliedReplayRecord input a freezeAt) =
        QueueReplay.replay capacity
          (QueueReplay.transition capacity initial
            (localQueueRecord l input.round input.enabled input.raw a))
          (inputQueueRecords l a rest)
      have hstep : QueueReplay.transition capacity initial
          (suppliedReplayRecord input a freezeAt) =
        QueueReplay.transition capacity initial
          (localQueueRecord l input.round input.enabled input.raw a) := by
        cases henabled : input.enabled <;>
          by_cases hbefore : sourceRound input.round < freezeAt <;>
          simp [suppliedReplayRecord, localQueueRecord, hfreeze, hbefore,
            henabled, QueueReplay.transition]
      rw [hstep, ih]

/-- Last-service replay is unchanged by the supplied-record map's disabled
arrival field, using the same per-step transition identity as queue replay. -/
private theorem replayLastService_supplied_map_eq_inputQueueRecords
    (capacity : ℕ) (initial : ℕ × ℕ) (retained : ℕ)
    (l : Ledger p eta heta hcap n hn) (a : Fin p.K) (freezeAt : ℕ)
    (hfreeze : l.freezeAt = freezeAt)
    (inputs : List (RoundInput (p := p) (eta := eta))) :
    replayLastService capacity initial retained
        (inputs.map fun input => suppliedReplayRecord input a freezeAt) =
      replayLastService capacity initial retained (inputQueueRecords l a inputs) := by
  induction inputs generalizing initial retained with
  | nil => rfl
  | cons input rest ih =>
      have hstep : QueueReplay.transition capacity initial
          (suppliedReplayRecord input a freezeAt) =
        QueueReplay.transition capacity initial
          (localQueueRecord l input.round input.enabled input.raw a) := by
        cases henabled : input.enabled <;>
          by_cases hbefore : sourceRound input.round < freezeAt <;>
          simp [suppliedReplayRecord, localQueueRecord, hfreeze, hbefore,
            henabled, QueueReplay.transition]
      cases rest with
      | nil =>
          simp only [List.map_cons, inputQueueRecords]
          rw [replayLastService_cons, replayLastService_cons, hstep]
          simp
      | cons head tail =>
          simp only [List.map_cons, inputQueueRecords]
          rw [replayLastService_cons, replayLastService_cons, hstep]
          exact ih _ _

/-- The last-service projection composes across an appended suffix. When the
suffix is nonempty, its final service depends on the prefix only through the
replayed registers. -/
private theorem replayLastService_append
    (capacity : ℕ) (initial : ℕ × ℕ) (retained : ℕ)
    (left right : List (Bool × ℕ)) :
    replayLastService capacity initial retained (left ++ right) =
      match right with
      | [] => replayLastService capacity initial retained left
      | _ :: _ => replayLastService capacity
          (QueueReplay.replay capacity initial left)
          (replayLastService capacity initial retained left) right := by
  cases right with
  | nil => simp
  | cons head tail =>
      induction left generalizing initial retained with
      | nil => simp [QueueReplay.replay, replayLastService]
      | cons first rest ih =>
          let firstService :=
            (QueueReplay.transition capacity initial first).1 - initial.1
          cases rest with
          | nil =>
              have hleft : replayLastService capacity initial retained
                  (first :: head :: tail) =
                replayLastService capacity (QueueReplay.transition capacity
                  initial first) firstService (head :: tail) := by
                rw [replayLastService_cons]
              have hstate : QueueReplay.replay capacity initial [first] =
                  QueueReplay.transition capacity initial first := by
                rfl
              have hservice : replayLastService capacity initial retained
                  [first] = firstService := by
                simp [replayLastService, QueueReplay.replay, firstService]
              calc
                replayLastService capacity initial retained
                    ([first] ++ head :: tail) =
                    replayLastService capacity initial retained
                      (first :: head :: tail) := by simp
                _ = replayLastService capacity
                    (QueueReplay.transition capacity initial first)
                    firstService (head :: tail) := hleft
                _ = replayLastService capacity
                    (QueueReplay.replay capacity initial [first])
                    (replayLastService capacity initial retained [first])
                    (head :: tail) := by rw [hstate, hservice]
          | cons second restTail =>
              have hleft : replayLastService capacity initial retained
                  (first :: (second :: restTail ++ head :: tail)) =
                replayLastService capacity (QueueReplay.transition capacity
                  initial first) firstService
                  (second :: restTail ++ head :: tail) := by
                rw [replayLastService_cons]
                simp [firstService, List.cons_append]
              have hstate : QueueReplay.replay capacity initial
                  (first :: second :: restTail) =
                QueueReplay.replay capacity (QueueReplay.transition capacity
                  initial first) (second :: restTail) := by
                rfl
              have hservice : replayLastService capacity initial retained
                  (first :: second :: restTail) =
                replayLastService capacity (QueueReplay.transition capacity
                  initial first) firstService (second :: restTail) := by
                rw [replayLastService_cons]
              calc
                replayLastService capacity initial retained
                    (first :: (second :: restTail ++ head :: tail)) =
                    replayLastService capacity (QueueReplay.transition capacity
                      initial first) firstService
                      (second :: restTail ++ head :: tail) := hleft
                _ = replayLastService capacity
                    (QueueReplay.replay capacity (QueueReplay.transition
                      capacity initial first) (second :: restTail))
                    (replayLastService capacity (QueueReplay.transition
                      capacity initial first) firstService (second :: restTail))
                    (head :: tail) := ih _ _
                _ = replayLastService capacity
                    (QueueReplay.replay capacity initial
                      (first :: second :: restTail))
                    (replayLastService capacity initial retained
                      (first :: second :: restTail)) (head :: tail) := by
                    rw [← hstate, ← hservice]

/-- On a nonempty replay ending in one record, the last-service projection is
the score difference across that final transition. -/
private theorem replayLastService_append_single
    (capacity : ℕ) (initial : ℕ × ℕ) (retained : ℕ)
    (past : List (Bool × ℕ)) (current : Bool × ℕ) :
    replayLastService capacity initial retained (past ++ [current]) =
      (QueueReplay.transition capacity
        (QueueReplay.replay capacity initial past) current).1 -
        (QueueReplay.replay capacity initial past).1 := by
  rw [replayLastService_append]
  simp [replayLastService, QueueReplay.replay]

/-- At an actual checked fold head, successful acceptance can only make the
selected follower's previously unknown assigned arm known. The fold recursion
therefore exposes the unique first accepting input and its actual parsed UP
record. -/
private theorem checkedRounds_extract_first_follower_acceptance
    (l final : Ledger p eta heta hcap n hn)
    (owner : Fin (p.m - 1))
    (inputs : List (RoundInput (p := p) (eta := eta)))
    (accepted : List Bool)
    (hunknown : l.currentRegisters (l.assignment.arm owner) = none)
    (hknown : ∃ current,
      final.currentRegisters (l.assignment.arm owner) = some current)
    (hfold : checkedRounds l inputs = some (accepted, final)) :
    ∃ pre input suffix prefixAccepted before started decoded finished
        suffixAccepted, ∃ M : UpRecord (codecParams p eta),
      inputs = pre ++ input :: suffix ∧
      checkedRounds l pre = some (prefixAccepted, before) ∧
      before.currentRegisters (l.assignment.arm owner) = none ∧
      startRound before (sourceRound input.round) input.enabled input.raw =
        .success started ∧
      decodeUp started input.selectedFollower input.parsed = .success decoded ∧
      finishRound decoded = .success finished ∧
      checkedRounds finished suffix = some (suffixAccepted, final) ∧
      input.selectedFollower = owner ∧ input.parsed = some M := by
  induction inputs generalizing l accepted final with
  | nil =>
      simp only [checkedRounds] at hfold
      rcases hfold with ⟨rfl, rfl⟩
      rcases hknown with ⟨current, hcurrent⟩
      rw [hunknown] at hcurrent
      cases hcurrent
  | cons input rest ih =>
      cases hs : startRound l (sourceRound input.round) input.enabled input.raw with
      | invalid => simp [checkedRounds, hs] at hfold
      | rejected bad => simp [checkedRounds, hs] at hfold
      | success started =>
          have hstartUnknown :
              started.currentRegisters (l.assignment.arm owner) = none := by
            rw [startRound_success_candidate l started (sourceRound input.round)
              input.enabled input.raw hs]
            simp [startRoundCandidate, hunknown]
          cases hd : decodeUp started input.selectedFollower input.parsed with
          | invalid => simp [checkedRounds, hs, hd] at hfold
          | rejected decoded =>
              cases hf : finishRound decoded with
              | invalid => simp [checkedRounds, hs, hd, hf] at hfold
              | rejected bad => simp [checkedRounds, hs, hd, hf] at hfold
              | success finished =>
                  cases hr : checkedRounds finished rest with
                  | none => simp [checkedRounds, hs, hd, hf, hr] at hfold
                  | some pair =>
                      have hfold' : false :: pair.1 = accepted ∧
                          pair.2 = final := by
                        simpa [checkedRounds, hs, hd, hf, hr] using hfold
                      rcases hfold' with ⟨rfl, rfl⟩
                      have hdecodedUnknown :
                          decoded.currentRegisters (l.assignment.arm owner) = none := by
                        rw [(decodeUp_rejected_preserves_arm started decoded
                          input.selectedFollower input.parsed
                          (l.assignment.arm owner) hd).1, hstartUnknown]
                      have hfinishedUnknown :
                          finished.currentRegisters (l.assignment.arm owner) = none := by
                        rw [finishRound_success_candidate decoded finished hf]
                        exact hdecodedUnknown
                      have hcontext := checkedRound_success_context l started
                        decoded finished input hs (Or.inr hd) hf
                      have hassignment : finished.assignment = l.assignment := by
                        exact congrArg (fun context => context.1) hcontext
                      have hfinishedUnknownIh :
                          finished.currentRegisters
                            (finished.assignment.arm owner) = none := by
                        rw [hassignment]
                        exact hfinishedUnknown
                      have hknownTail : ∃ current,
                          pair.2.currentRegisters
                            (finished.assignment.arm owner) = some current := by
                        rcases hknown with ⟨current, hcurrent⟩
                        exact ⟨current, by rw [hassignment]; exact hcurrent⟩
                      obtain ⟨pre, witness, suffix, prefixAccepted, before,
                        started', decoded', finished', suffixAccepted, M,
                        hsplit, hprefixFold, hbeforeUnknown, hwStart, hwDecode,
                        hwFinish, hwSuffix, hwSelected, hwParsed⟩ :=
                        ih finished pair.2 pair.1 hfinishedUnknownIh hknownTail hr
                      have hbeforeUnknown' :
                          before.currentRegisters (l.assignment.arm owner) = none := by
                        rw [hassignment] at hbeforeUnknown
                        exact hbeforeUnknown
                      have hprefixFold' :
                          checkedRounds l (input :: pre) =
                            some (false :: prefixAccepted, before) := by
                        simp only [checkedRounds, hs, hd, hf, hprefixFold]
                      refine ⟨input :: pre, witness, suffix,
                        false :: prefixAccepted, before, started', decoded',
                        finished', suffixAccepted, M, ?_, hprefixFold',
                        hbeforeUnknown', hwStart, hwDecode, hwFinish, hwSuffix,
                        hwSelected, hwParsed⟩
                      simp [hsplit]
          | success decoded =>
              cases hcurrent : decoded.currentRegisters (l.assignment.arm owner) with
              | some current =>
                  cases hparsed : input.parsed with
                  | none =>
                      have hsuccess : decodeUp started input.selectedFollower none =
                          .success decoded := by
                        simpa [hparsed] using hd
                      exact False.elim (decodeUp_none_not_success started
                        input.selectedFollower decoded hsuccess)
                  | some M =>
                      obtain ⟨_, _, _, _, _, _, _, _, hcandidate⟩ :=
                        decodeUp_success_candidate started decoded
                          input.selectedFollower M (by simpa [hparsed] using hd)
                      have hselectedArm :
                          started.assignment.arm input.selectedFollower =
                            l.assignment.arm owner := by
                        by_cases heq : started.assignment.arm
                            input.selectedFollower = l.assignment.arm owner
                        · exact heq
                        · have hnone :
                              decoded.currentRegisters
                                (l.assignment.arm owner) = none := by
                            rw [hcandidate]
                            simp [acceptUpCandidate,
                              Function.update_of_ne (Ne.symm heq), hstartUnknown]
                          rw [hnone] at hcurrent
                          cases hcurrent
                      have hstartedAssignment :
                          started.assignment = l.assignment := by
                        rw [startRound_success_candidate l started
                          (sourceRound input.round) input.enabled input.raw hs]
                        rfl
                      have hselected : input.selectedFollower = owner := by
                        apply l.assignment.injective
                        simpa [hstartedAssignment] using hselectedArm
                      cases hf : finishRound decoded with
                      | invalid => simp [checkedRounds, hs, hd, hf] at hfold
                      | rejected bad => simp [checkedRounds, hs, hd, hf] at hfold
                      | success finished =>
                          cases hr : checkedRounds finished rest with
                          | none => simp [checkedRounds, hs, hd, hf, hr] at hfold
                          | some pair =>
                              have hfold' : true :: pair.1 = accepted ∧
                                  pair.2 = final := by
                                simpa [checkedRounds, hs, hd, hf, hr] using hfold
                              rcases hfold' with ⟨rfl, rfl⟩
                              exact ⟨[], input, rest, [], l, started, decoded,
                                finished, pair.1, M, rfl, by simp [checkedRounds],
                                hunknown, hs, by simpa [hparsed] using hd, hf, hr,
                                hselected, hparsed⟩
              | none =>
                  cases hf : finishRound decoded with
                  | invalid => simp [checkedRounds, hs, hd, hf] at hfold
                  | rejected bad => simp [checkedRounds, hs, hd, hf] at hfold
                  | success finished =>
                      cases hr : checkedRounds finished rest with
                      | none => simp [checkedRounds, hs, hd, hf, hr] at hfold
                      | some pair =>
                          have hfold' : true :: pair.1 = accepted ∧
                              pair.2 = final := by
                            simpa [checkedRounds, hs, hd, hf, hr] using hfold
                          rcases hfold' with ⟨rfl, rfl⟩
                          have hfinishedUnknown :
                              finished.currentRegisters (l.assignment.arm owner) = none := by
                            rw [finishRound_success_candidate decoded finished hf]
                            exact hcurrent
                          have hcontext := checkedRound_success_context l started
                            decoded finished input hs (Or.inl hd) hf
                          have hassignment : finished.assignment = l.assignment := by
                            exact congrArg (fun context => context.1) hcontext
                          have hfinishedUnknownIh :
                              finished.currentRegisters
                                (finished.assignment.arm owner) = none := by
                            rw [hassignment]
                            exact hfinishedUnknown
                          have hknownTail : ∃ current,
                              pair.2.currentRegisters
                                (finished.assignment.arm owner) = some current := by
                            rcases hknown with ⟨current, hcurrent⟩
                            exact ⟨current, by rw [hassignment]; exact hcurrent⟩
                          obtain ⟨pre, witness, suffix, prefixAccepted, before,
                            started', decoded', finished', suffixAccepted, M,
                            hsplit, hprefixFold, hbeforeUnknown, hwStart, hwDecode,
                            hwFinish, hwSuffix, hwSelected, hwParsed⟩ :=
                            ih finished pair.2 pair.1 hfinishedUnknownIh hknownTail hr
                          have hbeforeUnknown' :
                              before.currentRegisters (l.assignment.arm owner) = none := by
                            rw [hassignment] at hbeforeUnknown
                            exact hbeforeUnknown
                          have hprefixFold' :
                              checkedRounds l (input :: pre) =
                                some (true :: prefixAccepted, before) := by
                            simp only [checkedRounds, hs, hd, hf, hprefixFold]
                          refine ⟨input :: pre, witness, suffix,
                            true :: prefixAccepted, before, started', decoded',
                            finished', suffixAccepted, M, ?_, hprefixFold',
                            hbeforeUnknown', hwStart, hwDecode, hwFinish, hwSuffix,
                            hwSelected, hwParsed⟩
                          simp [hsplit]

/-- Once this follower's assigned arm is known, no later successful decoder
step can accept an input selected for that follower. The proof follows each
actual checked transition, preserving the known arm and using assignment
injectivity at the decoder. -/
private theorem checkedRounds_known_owner_acceptance_unique
    (l final : Ledger p eta heta hcap n hn)
    (owner : Fin (p.m - 1)) (current : CurrentRegister)
    (inputs : List (RoundInput (p := p) (eta := eta)))
    (accepted : List Bool)
    (hknown : l.currentRegisters (l.assignment.arm owner) = some current)
    (hfold : checkedRounds l inputs = some (accepted, final)) :
    ∀ pair ∈ List.zip inputs accepted,
      pair.2 = true → pair.1.selectedFollower ≠ owner := by
  induction inputs generalizing l accepted final current with
  | nil =>
      simp only [checkedRounds] at hfold
      rcases hfold with ⟨rfl, rfl⟩
      simp
  | cons input rest ih =>
      cases hs : startRound l (sourceRound input.round) input.enabled input.raw with
      | invalid => simp [checkedRounds, hs] at hfold
      | rejected bad => simp [checkedRounds, hs] at hfold
      | success started =>
          have hstartKnown : ∃ now,
              started.currentRegisters (l.assignment.arm owner) = some now := by
            rw [startRound_success_candidate l started
              (sourceRound input.round) input.enabled input.raw hs]
            simp [startRoundCandidate, hknown]
          obtain ⟨now, hknownStarted⟩ := hstartKnown
          have hstartedAssignment : started.assignment = l.assignment := by
            rw [startRound_success_candidate l started
              (sourceRound input.round) input.enabled input.raw hs]
            rfl
          have hknownStarted' :
              started.currentRegisters (started.assignment.arm owner) = some now := by
            simpa [hstartedAssignment] using hknownStarted
          cases hd : decodeUp started input.selectedFollower input.parsed with
          | invalid => simp [checkedRounds, hs, hd] at hfold
          | rejected decoded =>
              cases hf : finishRound decoded with
              | invalid => simp [checkedRounds, hs, hd, hf] at hfold
              | rejected bad => simp [checkedRounds, hs, hd, hf] at hfold
              | success finished =>
                  cases hr : checkedRounds finished rest with
                  | none => simp [checkedRounds, hs, hd, hf, hr] at hfold
                  | some pair =>
                      have hfold' : false :: pair.1 = accepted ∧
                          pair.2 = final := by
                        simpa [checkedRounds, hs, hd, hf, hr] using hfold
                      rcases hfold' with ⟨rfl, rfl⟩
                      have hstep := checkedRound_known_transition l started
                        decoded finished input (l.assignment.arm owner) current
                        hknown hs (Or.inr hd) hf
                      obtain ⟨hnext, _, hfinishedAssignment, _, _, _, _⟩ := hstep
                      let next : CurrentRegister := ⟨
                        (QueueReplay.transition (4 * n)
                          (l.increment (l.assignment.arm owner), current.queue)
                          (localQueueRecord l input.round input.enabled input.raw
                            (l.assignment.arm owner))).2,
                        (QueueReplay.transition (4 * n)
                          (l.increment (l.assignment.arm owner), current.queue)
                          (localQueueRecord l input.round input.enabled input.raw
                            (l.assignment.arm owner))).1 -
                          l.increment (l.assignment.arm owner)⟩
                      have hknownNext : finished.currentRegisters
                          (finished.assignment.arm owner) = some next := by
                        rw [hfinishedAssignment]
                        simpa [next] using hnext
                      have htail := ih finished pair.2 next pair.1
                        hknownNext hr
                      intro candidate hmem htrue
                      simp only [List.zip_cons_cons, List.mem_cons] at hmem
                      rcases hmem with heq | hmem
                      · subst candidate
                        simp at htrue
                      · exact htail candidate hmem htrue
          | success decoded =>
              cases hf : finishRound decoded with
              | invalid => simp [checkedRounds, hs, hd, hf] at hfold
              | rejected bad => simp [checkedRounds, hs, hd, hf] at hfold
              | success finished =>
                  cases hr : checkedRounds finished rest with
                  | none => simp [checkedRounds, hs, hd, hf, hr] at hfold
                  | some pair =>
                      have hfold' : true :: pair.1 = accepted ∧
                          pair.2 = final := by
                        simpa [checkedRounds, hs, hd, hf, hr] using hfold
                      rcases hfold' with ⟨rfl, rfl⟩
                      have hnotOwner : input.selectedFollower ≠ owner := by
                        cases hparsed : input.parsed with
                        | none =>
                            have hsuccess : decodeUp started
                                input.selectedFollower none = .success decoded := by
                              simpa [hparsed] using hd
                            exact False.elim (decodeUp_none_not_success started
                              input.selectedFollower decoded hsuccess)
                        | some M =>
                            have hseparates :=
                              decodeUp_success_separates_assigned_known_arm
                                started decoded input.selectedFollower owner M now
                                hknownStarted' (by simpa [hparsed] using hd)
                            exact hseparates.1.symm
                      have hstep := checkedRound_known_transition l started
                        decoded finished input (l.assignment.arm owner) current
                        hknown hs (Or.inl hd) hf
                      obtain ⟨hnext, _, hfinishedAssignment, _, _, _, _⟩ := hstep
                      let next : CurrentRegister := ⟨
                        (QueueReplay.transition (4 * n)
                          (l.increment (l.assignment.arm owner), current.queue)
                          (localQueueRecord l input.round input.enabled input.raw
                            (l.assignment.arm owner))).2,
                        (QueueReplay.transition (4 * n)
                          (l.increment (l.assignment.arm owner), current.queue)
                          (localQueueRecord l input.round input.enabled input.raw
                            (l.assignment.arm owner))).1 -
                          l.increment (l.assignment.arm owner)⟩
                      have hknownNext : finished.currentRegisters
                          (finished.assignment.arm owner) = some next := by
                        rw [hfinishedAssignment]
                        simpa [next] using hnext
                      have htail := ih finished pair.2 next pair.1
                        hknownNext hr
                      intro candidate hmem htrue
                      simp only [List.zip_cons_cons, List.mem_cons] at hmem
                      rcases hmem with heq | hmem
                      · subst candidate
                        exact hnotOwner
                      · exact htail candidate hmem htrue

/-- Full-input queue replay for an assigned follower whose queue is known at
the returned state. The accepted input and its parsed UP record are extracted
from the actual checked fold. The conclusion replays the original input list
from the actual returned `M.q`, including every pre-acceptance calendar round
and each suffix round exactly once. -/
theorem assigned_follower_full_input_queue_replay
    (assignment : Assignment p) (sigma cutoff freezeAt : ℕ)
    (baseScore : Fin (p.m - 1) → ℕ)
    (outside : Fin p.K → Option CutoffRegister)
    (inputs : List (RoundInput (p := p) (eta := eta)))
    (execution : Execution p eta heta hcap n hn)
    (i : Fin (p.m - 1))
    (hRun : startAndRunChecked p eta heta hcap n hn assignment sigma cutoff
      freezeAt baseScore outside inputs = .success execution)
    (hknownFinal : ∃ current,
      execution.final.currentRegisters (execution.initial.assignment.arm i) =
        some current) :
    ∃ pre input suffix prefixAccepted before started decoded finished
        suffixAccepted, ∃ M : UpRecord (codecParams p eta),
      inputs = pre ++ input :: suffix ∧
      input.selectedFollower = i ∧ input.parsed = some M ∧
      checkedRounds execution.initial pre = some (prefixAccepted, before) ∧
      before.currentRegisters (execution.initial.assignment.arm i) = none ∧
      startRound before (sourceRound input.round) input.enabled input.raw =
        .success started ∧
      decodeUp started input.selectedFollower input.parsed = .success decoded ∧
      finishRound decoded = .success finished ∧
      checkedRounds finished suffix = some (suffixAccepted, execution.final) ∧
      (∀ pair ∈ List.zip suffix suffixAccepted,
        pair.2 = true → pair.1.selectedFollower ≠ i) ∧
      execution.final.currentRegisters (execution.initial.assignment.arm i) =
        some ⟨
          (QueueReplay.replay (4 * n) (0, M.val.q)
            (inputQueueRecords execution.initial
              (execution.initial.assignment.arm i) inputs)).2,
          replayLastService (4 * n) (0, M.val.q) M.val.delta
            (inputQueueRecords execution.initial
              (execution.initial.assignment.arm i) inputs)⟩ ∧
      execution.final.increment (execution.initial.assignment.arm i) =
        (QueueReplay.replay (4 * n) (0, M.val.q)
          (inputQueueRecords execution.initial
            (execution.initial.assignment.arm i) inputs)).1 ∧
      execution.final.cutoffRegisters (execution.initial.assignment.arm i) =
        some ⟨baseScore i + M.val.S, M.val.q, M.val.delta⟩ ∧
      execution.initial.cursor = cutoff ∧
      execution.final.cursor = execution.initial.cursor + inputs.length ∧
      chronologicalFrom execution.initial.cursor inputs ∧
      (∀ a r, execution.initial.rawBuffer a r = none) ∧
      (∀ supplied ∈ inputs,
        execution.final.enabledHistory supplied.round = some supplied.enabled) ∧
      execution.final.assignment = assignment ∧
      execution.final.cutoff = cutoff ∧ execution.final.freezeAt = freezeAt := by
  obtain ⟨acceptedAll, hinitial, hfold⟩ :=
    startAndRunChecked_success_components assignment sigma cutoff freezeAt
      baseScore outside inputs execution hRun
  obtain ⟨hinitialAssignment, hinitialSigma, hinitialCursor, hinitialCutoff,
      hinitialFreeze, hinitialBase⟩ :=
    startCollectionChecked_success_context assignment sigma cutoff freezeAt
      baseScore outside execution.initial hinitial
  let arm := execution.initial.assignment.arm i
  have hinitialUnknown := startCollectionChecked_assigned_arm_unknown
    assignment sigma cutoff freezeAt baseScore outside execution.initial i hinitial
  have hinitialUnknown' : execution.initial.currentRegisters
      (execution.initial.assignment.arm i) = none := by
    simpa [hinitialAssignment] using hinitialUnknown
  obtain ⟨pre, input, suffix, prefixAccepted, before, started, decoded, finished,
      suffixAccepted, M, hsplit, hprefixFold, hbeforeUnknown, hstart, hdecode,
      hfinish, hsuffix, hselected, hparsed⟩ :=
    checkedRounds_extract_first_follower_acceptance execution.initial
      execution.final i inputs acceptedAll hinitialUnknown' hknownFinal hfold
  let prefixExecution : Execution p eta heta hcap n hn :=
    ⟨execution.initial, prefixAccepted, before⟩
  have hRunPrefix : startAndRunChecked p eta heta hcap n hn assignment sigma
      cutoff freezeAt baseScore outside pre = .success prefixExecution := by
    simp [startAndRunChecked, hinitial, hprefixFold, prefixExecution]
  have hprefixChron := startAndRunChecked_success_input_chronology p eta heta
    hcap n hn assignment sigma cutoff freezeAt baseScore outside pre
    prefixExecution hRunPrefix
  have hprefixEnd := startAndRunChecked_success_chronology p eta heta hcap n hn
    assignment sigma cutoff freezeAt baseScore outside pre prefixExecution hRunPrefix
  have hprefixCursor : before.cursor = execution.initial.cursor + pre.length := by
    simpa [prefixExecution] using hprefixEnd.1
  have hshortChron := chronologicalFrom_append_one execution.initial.cursor
    pre input hprefixChron (by
      calc
        sourceRound input.round = before.cursor :=
          startRound_success_time before started (sourceRound input.round)
            input.enabled input.raw hstart
        _ = execution.initial.cursor + pre.length := hprefixCursor)
  have hbeforeContext := checkedRounds_success_preserves_context
    execution.initial before pre prefixAccepted hprefixFold
  have hbeforeAssignment : before.assignment = execution.initial.assignment :=
    congrArg (fun context => context.1) hbeforeContext
  have hbeforeCutoff : before.cutoff = execution.initial.cutoff :=
    congrArg (fun context => context.2.2.1) hbeforeContext
  have hbeforeFreeze : before.freezeAt = execution.initial.freezeAt :=
    congrArg (fun context => context.2.2.2.1) hbeforeContext
  have hbeforeBase : before.baseScore = execution.initial.baseScore :=
    congrArg (fun context => context.2.2.2.2) hbeforeContext
  have hstartedAssignment : started.assignment = execution.initial.assignment := by
    rw [startRound_success_candidate before started (sourceRound input.round)
      input.enabled input.raw hstart]
    exact hbeforeAssignment
  have hstartedCutoff : started.cutoff = cutoff := by
    rw [startRound_success_candidate before started (sourceRound input.round)
      input.enabled input.raw hstart]
    exact hbeforeCutoff.trans hinitialCutoff
  have hstartedFreeze : started.freezeAt = freezeAt := by
    rw [startRound_success_candidate before started (sourceRound input.round)
      input.enabled input.raw hstart]
    exact hbeforeFreeze.trans hinitialFreeze
  have hstartedBase : started.baseScore = baseScore := by
    rw [startRound_success_candidate before started (sourceRound input.round)
      input.enabled input.raw hstart]
    exact hbeforeBase.trans hinitialBase
  have hstartedCursor : started.cursor = sourceRound input.round :=
    startRound_success_cursor before started (sourceRound input.round)
      input.enabled input.raw hstart
  have hstartedCursorEnd : started.cursor = execution.initial.cursor + pre.length := by
    calc
      started.cursor = sourceRound input.round := hstartedCursor
      _ = before.cursor :=
        startRound_success_time before started (sourceRound input.round)
          input.enabled input.raw hstart
      _ = execution.initial.cursor + pre.length := hprefixCursor
  have hinputSource : sourceRound input.round = started.cursor := by
    calc
      sourceRound input.round = before.cursor :=
        startRound_success_time before started (sourceRound input.round)
          input.enabled input.raw hstart
      _ = execution.initial.cursor + pre.length := hprefixCursor
      _ = started.cursor := hstartedCursorEnd.symm
  have hcalendarBound : execution.initial.cursor - 1 + pre.length ≤ p.T := by
    have hroundBound : input.round.val + 1 ≤ p.T :=
      Nat.succ_le_of_lt input.round.isLt
    have hcursorEq : input.round.val + 1 =
        execution.initial.cursor + pre.length := by
      have h := hinputSource.trans hstartedCursorEnd
      simpa [sourceRound] using h
    rw [hinitialCursor]
    omega
  have hdecodeAccepted : decodeUp started i (some M) = .success decoded := by
    simpa [hselected, hparsed] using hdecode
  obtain ⟨hbound, lastIndex, hlastSource, past, current, hpast, hcurrent,
      hsupplied, hstartedUnknown, hacceptedCurrent, hincrement, hcutoffRegister⟩ :=
    successful_decode_records_are_replayRecords assignment sigma cutoff freezeAt
      baseScore outside pre prefixExecution input started decoded finished i M
      hRunPrefix (by
        simpa [prefixExecution, hbeforeAssignment] using hbeforeUnknown)
      hstart hdecodeAccepted hfinish
  have hindices : calendarIndices p.T (started.cutoff - 1)
      (started.cursor - started.cutoff) hbound = pre.map RoundInput.round := by
    have h := calendarIndices_eq_input_rounds execution.initial.cursor pre
      hprefixChron hcalendarBound
    simpa [hstartedCutoff, hstartedCursorEnd, hinitialCursor] using h
  have hlastRound : lastIndex = input.round := by
    apply Fin.ext
    have hlabels : sourceRound lastIndex = sourceRound input.round :=
      hlastSource.trans hinputSource.symm
    dsimp [sourceRound] at hlabels ⊢
    omega
  have hallIndices :
      calendarIndices p.T (started.cutoff - 1)
          (started.cursor - started.cutoff) hbound ++ [lastIndex] =
        (pre ++ [input]).map RoundInput.round := by
    rw [hindices, hlastRound]
    simp
  have hlookup : ∀ supplied ∈ pre ++ [input],
      findRoundInput? (pre ++ [input]) supplied.round = some supplied := by
    intro supplied hmem
    exact chronologicalFrom_findRoundInput?_of_mem execution.initial.cursor
      (pre ++ [input]) hshortChron supplied hmem
  have hsuppliedMap := suppliedReplayRecords?_map (pre ++ [input]) arm
    started.freezeAt hlookup
  have hsuppliedActual := hsupplied
  rw [hallIndices] at hsuppliedActual
  have hprefixArm : prefixExecution.final.assignment.arm i = arm := by
    simp [prefixExecution, arm, hbeforeAssignment]
  rw [hprefixArm] at hsuppliedActual
  have hacceptanceRecords : past ++ [current] =
      (pre ++ [input]).map fun supplied =>
        suppliedReplayRecord supplied arm started.freezeAt :=
    Option.some.inj (hsuppliedActual.symm.trans hsuppliedMap)
  have hinitialStartedFreeze : execution.initial.freezeAt = started.freezeAt :=
    hinitialFreeze.trans hstartedFreeze.symm
  have hacceptanceReplay :
      QueueReplay.replay (4 * n) (0, M.val.q) (past ++ [current]) =
        QueueReplay.replay (4 * n) (0, M.val.q)
          (inputQueueRecords execution.initial arm (pre ++ [input])) := by
    calc
      QueueReplay.replay (4 * n) (0, M.val.q) (past ++ [current]) =
          QueueReplay.replay (4 * n) (0, M.val.q)
            ((pre ++ [input]).map fun supplied =>
              suppliedReplayRecord supplied arm started.freezeAt) := by
                rw [hacceptanceRecords]
      _ = QueueReplay.replay (4 * n) (0, M.val.q)
          (inputQueueRecords execution.initial arm (pre ++ [input])) :=
            replay_supplied_map_eq_inputQueueRecords (4 * n) (0, M.val.q)
              execution.initial arm started.freezeAt hinitialStartedFreeze
              (pre ++ [input])
  have hacceptedRun :=
    checked_acceptance_then_checked_suffix_one_replay before started decoded
      finished execution.final (sourceRound input.round) input.enabled input.raw
      i M suffix suffixAccepted hstart hdecodeAccepted hfinish hsuffix
  obtain ⟨hboundCont, lastIndexCont, hlastCont, pastCont, currentCont,
      hpastCont, hcurrentCont, hunknownCont, hfinalCurrentCont,
      hfinalIncrementCont, hfinalCutoffCont, hfinalAssignmentCont,
      hfinalFreezeCont⟩ := hacceptedRun
  have hcontinuedAcceptance : pastCont ++ [currentCont] = past ++ [current] := by
    have hstartedArm : started.assignment.arm i = arm := by
      simp [arm, hstartedAssignment]
    have hpastProvenance :
        replayRecords? started arm
          (calendarIndices p.T (started.cutoff - 1)
            (started.cursor - started.cutoff) hbound) = some past := by
      simpa [prefixExecution, arm, hbeforeAssignment] using hpast
    have hcurrentProvenance :
        replayRecords? started arm [lastIndex] = some [current] := by
      simpa [prefixExecution, arm, hbeforeAssignment] using hcurrent
    have hpastContinuation :
        replayRecords? started arm
          (calendarIndices p.T (started.cutoff - 1)
            (started.cursor - started.cutoff) hboundCont) = some pastCont := by
      simpa [hstartedArm] using hpastCont
    have hlastContinuation : replayRecords? started arm [lastIndex] =
        some [currentCont] := by
      have hlastEq : lastIndexCont = lastIndex := by
        apply Fin.ext
        have hlabels := (hlastCont.trans hinputSource).trans hlastSource.symm
        dsimp [sourceRound] at hlabels ⊢
        omega
      simpa [hlastEq, hstartedArm] using hcurrentCont
    have hpastEq : pastCont = past :=
      Option.some.inj (hpastContinuation.symm.trans hpastProvenance)
    have hcurrentEq : currentCont = current := by
      have hrecords := Option.some.inj (hlastContinuation.symm.trans
        hcurrentProvenance)
      injection hrecords with hrecord
    rw [hpastEq, hcurrentEq]
  have hfullSplit : inputs = (pre ++ [input]) ++ suffix := by
    simpa [List.append_assoc] using hsplit
  have hfinalContext := checkedRounds_success_preserves_context
    execution.initial execution.final inputs acceptedAll hfold
  have hfinalAssignment : execution.final.assignment = assignment := by
    exact (congrArg (fun context => context.1) hfinalContext).trans
      hinitialAssignment
  have hfinalCutoff : execution.final.cutoff = cutoff := by
    exact (congrArg (fun context => context.2.2.1) hfinalContext).trans
      hinitialCutoff
  have hfinalFreeze : execution.final.freezeAt = freezeAt := by
    exact (congrArg (fun context => context.2.2.2.1) hfinalContext).trans
      hinitialFreeze
  have hwholeChron := startAndRunChecked_success_input_chronology p eta heta
    hcap n hn assignment sigma cutoff freezeAt baseScore outside inputs execution hRun
  have hwholeEnd := startAndRunChecked_success_chronology p eta heta hcap n hn
    assignment sigma cutoff freezeAt baseScore outside inputs execution hRun
  have hwholeEnables := startAndRunChecked_success_records_supplied_enables
    p eta heta hcap n hn assignment sigma cutoff freezeAt baseScore outside
    inputs execution hRun
  have hinitialBufferEmpty :=
    startCollectionChecked_success_empty_rawBuffer assignment sigma cutoff
      freezeAt baseScore outside execution.initial hinitial
  have hfreezeStarted : execution.initial.freezeAt = started.freezeAt :=
    hinitialStartedFreeze
  have hqueueRecordSplit :
      inputQueueRecords execution.initial arm inputs =
        inputQueueRecords execution.initial arm (pre ++ [input]) ++
          inputQueueRecords started arm suffix := by
    calc
      inputQueueRecords execution.initial arm inputs =
          inputQueueRecords execution.initial arm ((pre ++ [input]) ++ suffix) := by
            rw [hfullSplit]
      _ = inputQueueRecords execution.initial arm (pre ++ [input]) ++
          inputQueueRecords execution.initial arm suffix := by
            simp [inputQueueRecords]
      _ = inputQueueRecords execution.initial arm (pre ++ [input]) ++
          inputQueueRecords started arm suffix := by
            rw [inputQueueRecords_freezeAt_eq execution.initial started arm suffix
              hfreezeStarted]
  let acceptanceRecords := pastCont ++ [currentCont]
  let prefixReplay := QueueReplay.replay (4 * n) (0, M.val.q)
    acceptanceRecords
  let acceptedLast := prefixReplay.1 -
    (QueueReplay.replay (4 * n) (0, M.val.q) pastCont).1
  let suffixRecords := inputQueueRecords started arm suffix
  have hcontinuedAcceptanceReplay :
      QueueReplay.replay (4 * n) (0, M.val.q) acceptanceRecords =
        QueueReplay.replay (4 * n) (0, M.val.q)
          (inputQueueRecords execution.initial arm (pre ++ [input])) := by
    change QueueReplay.replay (4 * n) (0, M.val.q)
        (pastCont ++ [currentCont]) = _
    rw [hcontinuedAcceptance]
    exact hacceptanceReplay
  have hcombinedReplay :
      QueueReplay.replay (4 * n) (0, M.val.q)
          (acceptanceRecords ++ suffixRecords) =
        QueueReplay.replay (4 * n) (0, M.val.q)
          (inputQueueRecords execution.initial arm inputs) := by
    calc
      QueueReplay.replay (4 * n) (0, M.val.q)
          (acceptanceRecords ++ suffixRecords) =
          QueueReplay.replay (4 * n)
            (QueueReplay.replay (4 * n) (0, M.val.q) acceptanceRecords)
            suffixRecords := QueueReplay.replay_append _ _ _ _
      _ = QueueReplay.replay (4 * n)
          (QueueReplay.replay (4 * n) (0, M.val.q)
            (inputQueueRecords execution.initial arm (pre ++ [input])))
          suffixRecords := by rw [hcontinuedAcceptanceReplay]
      _ = QueueReplay.replay (4 * n) (0, M.val.q)
          (inputQueueRecords execution.initial arm inputs) := by
            rw [hqueueRecordSplit, QueueReplay.replay_append]
  have hacceptedLast : replayLastService (4 * n) (0, M.val.q) M.val.delta
      acceptanceRecords = acceptedLast := by
    rw [replayLastService_append_single]
    simp [acceptanceRecords, prefixReplay, acceptedLast,
      QueueReplay.replay_append]
    simp [QueueReplay.replay]
  have hacceptanceInputService :
      replayLastService (4 * n) (0, M.val.q) M.val.delta acceptanceRecords =
        replayLastService (4 * n) (0, M.val.q) M.val.delta
          (inputQueueRecords execution.initial arm (pre ++ [input])) := by
    change replayLastService (4 * n) (0, M.val.q) M.val.delta
        (pastCont ++ [currentCont]) = _
    rw [hcontinuedAcceptance, hacceptanceRecords]
    exact replayLastService_supplied_map_eq_inputQueueRecords (4 * n)
      (0, M.val.q) M.val.delta execution.initial arm started.freezeAt
      hinitialStartedFreeze (pre ++ [input])
  have hlastServiceAppendAccepted :
      replayLastService (4 * n) (0, M.val.q) M.val.delta
          (acceptanceRecords ++ suffixRecords) =
        replayLastService (4 * n) prefixReplay acceptedLast suffixRecords := by
    change replayLastService (4 * n) (0, M.val.q) M.val.delta
        (acceptanceRecords ++ inputQueueRecords started arm suffix) =
      replayLastService (4 * n) prefixReplay acceptedLast
        (inputQueueRecords started arm suffix)
    cases hsuffix : inputQueueRecords started arm suffix with
    | nil =>
        simp only [List.append_nil]
        simp only [replayLastService]
        exact hacceptedLast
    | cons head tail =>
        rw [replayLastService_append, hacceptedLast]
  have hlastServiceAppendSource :
      replayLastService (4 * n) (0, M.val.q) M.val.delta
          (inputQueueRecords execution.initial arm inputs) =
        replayLastService (4 * n) prefixReplay acceptedLast suffixRecords := by
    rw [hqueueRecordSplit]
    change replayLastService (4 * n) (0, M.val.q) M.val.delta
        (inputQueueRecords execution.initial arm (pre ++ [input]) ++
          inputQueueRecords started arm suffix) =
      replayLastService (4 * n) prefixReplay acceptedLast
        (inputQueueRecords started arm suffix)
    cases hsuffix : inputQueueRecords started arm suffix with
    | nil =>
        simp only [List.append_nil]
        simp only [replayLastService]
        exact hacceptanceInputService.symm.trans hacceptedLast
    | cons head tail =>
        have hservicePrefix :
            replayLastService (4 * n) (0, M.val.q) M.val.delta
                (inputQueueRecords execution.initial arm (pre ++ [input])) =
              acceptedLast :=
          hacceptanceInputService.symm.trans hacceptedLast
        rw [replayLastService_append, ← hcontinuedAcceptanceReplay,
          hservicePrefix]
  have hlastServiceFull :=
    hlastServiceAppendAccepted.trans hlastServiceAppendSource.symm
  have hlastServiceResult :
      replayLastService (4 * n) prefixReplay acceptedLast suffixRecords =
        replayLastService (4 * n) (0, M.val.q) M.val.delta
          (inputQueueRecords execution.initial arm inputs) := by
    calc
      replayLastService (4 * n) prefixReplay acceptedLast suffixRecords =
          replayLastService (4 * n) (0, M.val.q) M.val.delta
            (acceptanceRecords ++ suffixRecords) :=
              hlastServiceAppendAccepted.symm
      _ = replayLastService (4 * n) (0, M.val.q) M.val.delta
          (inputQueueRecords execution.initial arm inputs) := hlastServiceFull
  have hfinalCurrentArm : execution.final.currentRegisters arm = some ⟨
      (QueueReplay.replay (4 * n) (0, M.val.q)
        (acceptanceRecords ++ suffixRecords)).2,
      replayLastService (4 * n) prefixReplay acceptedLast suffixRecords⟩ := by
    simpa [arm, hstartedAssignment, acceptanceRecords, prefixReplay,
      acceptedLast, suffixRecords] using hfinalCurrentCont
  have hfinalCurrent : execution.final.currentRegisters arm = some ⟨
      (QueueReplay.replay (4 * n) (0, M.val.q)
        (inputQueueRecords execution.initial arm inputs)).2,
      replayLastService (4 * n) (0, M.val.q) M.val.delta
        (inputQueueRecords execution.initial arm inputs)⟩ := by
    rw [hfinalCurrentArm, hcombinedReplay]
    apply congrArg some
    exact congrArg (fun service =>
      (⟨(QueueReplay.replay (4 * n) (0, M.val.q)
        (inputQueueRecords execution.initial arm inputs)).2, service⟩ : CurrentRegister))
      hlastServiceResult
  have hfinalIncrementArm : execution.final.increment arm =
      (QueueReplay.replay (4 * n) (0, M.val.q)
        (acceptanceRecords ++ suffixRecords)).1 := by
    simpa [arm, hstartedAssignment, acceptanceRecords, prefixReplay,
      acceptedLast, suffixRecords] using hfinalIncrementCont
  have hfinalIncrement : execution.final.increment arm =
      (QueueReplay.replay (4 * n) (0, M.val.q)
        (inputQueueRecords execution.initial arm inputs)).1 := by
    rw [hfinalIncrementArm, hcombinedReplay]
  have hfinalCutoffArm : execution.final.cutoffRegisters arm =
      some ⟨started.baseScore i + M.val.S, M.val.q, M.val.delta⟩ := by
    simpa [arm, hstartedAssignment] using hfinalCutoffCont
  have hfinalCutoffRegister : execution.final.cutoffRegisters arm =
      some ⟨baseScore i + M.val.S, M.val.q, M.val.delta⟩ := by
    simpa [hstartedBase] using hfinalCutoffArm
  let acceptedCurrent : CurrentRegister := ⟨
    (QueueReplay.replay (4 * n) (0, M.val.q) (past ++ [current])).2,
    (QueueReplay.replay (4 * n) (0, M.val.q) (past ++ [current])).1 -
      (QueueReplay.replay (4 * n) (0, M.val.q) past).1⟩
  have hfinishedContext := checkedRound_success_context before started decoded
    finished input hstart (Or.inl hdecode) hfinish
  have hfinishedAssignment : finished.assignment = before.assignment :=
    congrArg (fun context => context.1) hfinishedContext
  have hprovenanceCurrent :
      finished.currentRegisters (before.assignment.arm i) =
        some acceptedCurrent := by
    simpa [prefixExecution, acceptedCurrent] using hacceptedCurrent
  have hknownAfterAcceptance :
      finished.currentRegisters (finished.assignment.arm i) = some acceptedCurrent := by
    rw [hfinishedAssignment]
    exact hprovenanceCurrent
  have huniqueAfterAcceptance :=
    checkedRounds_known_owner_acceptance_unique finished execution.final i
      acceptedCurrent suffix suffixAccepted hknownAfterAcceptance hsuffix
  refine ⟨pre, input, suffix, prefixAccepted, before, started, decoded, finished,
    suffixAccepted, M, hsplit, hselected, hparsed, hprefixFold, hbeforeUnknown,
    hstart, hdecode, hfinish, hsuffix, huniqueAfterAcceptance, hfinalCurrent,
    hfinalIncrement, hfinalCutoffRegister, hinitialCursor, hwholeEnd.1,
    hwholeChron, hinitialBufferEmpty, hwholeEnables, hfinalAssignment,
    hfinalCutoff, hfinalFreeze⟩

/-- Empty final pending state supplies the known-register premise for every
assigned follower, so the extracted acceptance replay applies to each arm. -/
theorem assigned_follower_full_input_queue_replay_of_empty_pending
    (assignment : Assignment p) (sigma cutoff freezeAt : ℕ)
    (baseScore : Fin (p.m - 1) → ℕ)
    (outside : Fin p.K → Option CutoffRegister)
    (inputs : List (RoundInput (p := p) (eta := eta)))
    (execution : Execution p eta heta hcap n hn)
    (i : Fin (p.m - 1))
    (hRun : startAndRunChecked p eta heta hcap n hn assignment sigma cutoff
      freezeAt baseScore outside inputs = .success execution)
    (hempty : execution.final.pending = ∅) :
    ∃ pre input suffix prefixAccepted before started decoded finished
        suffixAccepted, ∃ M : UpRecord (codecParams p eta),
      inputs = pre ++ input :: suffix ∧
      input.selectedFollower = i ∧ input.parsed = some M ∧
      checkedRounds execution.initial pre = some (prefixAccepted, before) ∧
      before.currentRegisters (execution.initial.assignment.arm i) = none ∧
      startRound before (sourceRound input.round) input.enabled input.raw =
        .success started ∧
      decodeUp started input.selectedFollower input.parsed = .success decoded ∧
      finishRound decoded = .success finished ∧
      checkedRounds finished suffix = some (suffixAccepted, execution.final) ∧
      (∀ pair ∈ List.zip suffix suffixAccepted,
        pair.2 = true → pair.1.selectedFollower ≠ i) ∧
      execution.final.currentRegisters (execution.initial.assignment.arm i) =
        some ⟨
          (QueueReplay.replay (4 * n) (0, M.val.q)
            (inputQueueRecords execution.initial
              (execution.initial.assignment.arm i) inputs)).2,
          replayLastService (4 * n) (0, M.val.q) M.val.delta
            (inputQueueRecords execution.initial
              (execution.initial.assignment.arm i) inputs)⟩ ∧
      execution.final.increment (execution.initial.assignment.arm i) =
        (QueueReplay.replay (4 * n) (0, M.val.q)
          (inputQueueRecords execution.initial
            (execution.initial.assignment.arm i) inputs)).1 ∧
      execution.final.cutoffRegisters (execution.initial.assignment.arm i) =
        some ⟨baseScore i + M.val.S, M.val.q, M.val.delta⟩ ∧
      execution.initial.cursor = cutoff ∧
      execution.final.cursor = execution.initial.cursor + inputs.length ∧
      chronologicalFrom execution.initial.cursor inputs ∧
      (∀ a r, execution.initial.rawBuffer a r = none) ∧
      (∀ supplied ∈ inputs,
        execution.final.enabledHistory supplied.round = some supplied.enabled) ∧
      execution.final.assignment = assignment ∧
      execution.final.cutoff = cutoff ∧ execution.final.freezeAt = freezeAt := by
  exact assigned_follower_full_input_queue_replay assignment sigma cutoff freezeAt
    baseScore outside inputs execution i hRun (by
      obtain ⟨acceptedAll, hinitial, hfold⟩ :=
        startAndRunChecked_success_components assignment sigma cutoff freezeAt
          baseScore outside inputs execution hRun
      have hinitialValid := startCollectionChecked_success_valid assignment sigma
        cutoff freezeAt baseScore outside execution.initial hinitial
      have hfinalValid := checkedRounds_success_valid execution.initial
        execution.final inputs acceptedAll hinitialValid hfold
      exact currentRegister_present_of_empty_pending execution.final hfinalValid
        hempty (execution.initial.assignment.arm i))

end Bandits.Support.CollectionFullInputReplay

end
