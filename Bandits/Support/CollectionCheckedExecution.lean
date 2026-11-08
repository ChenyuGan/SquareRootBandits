/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.CoordinatorCollectionLedger

import Lean.Elab.Tactic.Omega

/-!
# Checked chronological collection executions

This module composes the checked local operations from
`CoordinatorCollectionLedger`.  Its per-round inputs are the supplied enable
bit, raw recorder result, selected follower, and already parsed optional UP
record.  It contains no recorder, raw decoder, or physical-history model.

The mathematical evidence is `sources/zip4/manuscript/06_interruptions.tex:16-28,64-100,257-283`
and `sources/zip4/manuscript/appendix_a_local_protocol.tex:8-14,46-64`.
-/

@[expose] public section

namespace Bandits.Support.CollectionCheckedExecution

open Bandits.Support.CoordinatorCollectionLedger
open Bandits.Support.OrdinaryMessageCodec

variable {p : ConstructorDimensions.Parameters}
variable {eta : ℝ} {heta : 0 < eta}
  {hcap : sourceLearningCap p eta} {n : ℕ}
  {hn : (n : ℝ) = eta * (ConstructorDimensions.D p : ℝ)}

/-- Honest supplied local inputs for one calendar round.  The raw arrival is
an arm or no record; the natural amount is checked by `startRound`.  `parsed`
is the result already supplied by a parser, and is not reconstructed here. -/
structure RoundInput where
  round : Fin p.T
  enabled : Bool
  raw : Option (Fin p.K × ℕ)
  selectedFollower : Fin (p.m - 1)
  parsed : Option (UpRecord (codecParams p eta))

/-- The finite trace returned by a successful checked execution. -/
structure Execution (p : ConstructorDimensions.Parameters) (eta : ℝ)
    (heta : 0 < eta) (hcap : sourceLearningCap p eta) (n : ℕ)
    (hn : (n : ℝ) = eta * (ConstructorDimensions.D p : ℝ)) where
  initial : Ledger p eta heta hcap n hn
  accepted : List Bool
  final : Ledger p eta heta hcap n hn

/-- The source-round labels in a successful local trace, stated recursively
without adding any protocol input assumptions. -/
def chronologicalFrom (cursor : ℕ) :
    List (RoundInput (p := p) (eta := eta)) → Prop
  | [] => True
  | input :: rest =>
      sourceRound input.round = cursor ∧ chronologicalFrom (cursor + 1) rest

/-- Execute supplied rounds chronologically from the current ledger cursor.
Each list cell runs actual `startRound`, then actual `decodeUp`, then actual
`finishRound`.  Parser/acceptance rejection keeps the returned ledger and the
fold proceeds; any invalid result terminates the fold immediately. -/
def checkedRounds (l : Ledger p eta heta hcap n hn) :
    List (RoundInput (p := p) (eta := eta)) →
      Option (List Bool ×
        Ledger p eta heta hcap n hn)
  | [] => some ([], l)
  | input :: rest =>
      match startRound l (sourceRound input.round) input.enabled input.raw with
      | .success started =>
          match decodeUp started input.selectedFollower input.parsed with
          | .success decoded =>
              match finishRound decoded with
              | .success finished =>
                  match checkedRounds finished rest with
                  | none => none
                  | some (accepted, final) => some (true :: accepted, final)
              | .rejected _ => none
              | .invalid => none
          | .rejected decoded =>
              match finishRound decoded with
              | .success finished =>
                  match checkedRounds finished rest with
                  | none => none
                  | some (accepted, final) => some (false :: accepted, final)
              | .rejected _ => none
              | .invalid => none
          | .invalid => none
      | .rejected _ => none
      | .invalid => none

/-- Run the checked collection fold from the *actual* checked initializer.
An invalid initializer or any invalid intermediate operation short-circuits. -/
def startAndRunChecked (p : ConstructorDimensions.Parameters) (eta : ℝ)
    (heta : 0 < eta) (hcap : sourceLearningCap p eta) (n : ℕ)
    (hn : (n : ℝ) = eta * (ConstructorDimensions.D p : ℝ))
    (assignment : Assignment p) (sigma cutoff freezeAt : ℕ)
    (baseScore : Fin (p.m - 1) → ℕ)
    (outside : Fin p.K → Option CutoffRegister)
    (inputs : List (RoundInput (p := p) (eta := eta))) :
    Checked (Execution p eta heta hcap n hn) := by
  exact match startCollectionChecked p eta heta hcap n hn assignment sigma cutoff
      freezeAt baseScore outside with
    | .success initial =>
        match checkedRounds initial inputs with
        | none => .invalid
        | some (accepted, final) => .success ⟨initial, accepted, final⟩
    | .rejected _ => .invalid
    | .invalid => .invalid

/-- A successful checked finish advances the cursor by exactly one and returns
to the ready phase. -/
theorem finishRound_success_chronology
    (l result : Ledger p eta heta hcap n hn)
    (h : finishRound l = .success result) :
    result.cursor = l.cursor + 1 ∧ result.phase = .ready ∧
      result.enabledHistory = l.enabledHistory := by
  unfold finishRound at h
  repeat (first | split at h | dsimp only at h)
  all_goals
    first
    | contradiction
    | (injection h with heq; cases heq; simp [finishRoundCandidate])

/-- A successful checked finish returns exactly the existing finish candidate. -/
theorem finishRound_success_candidate
    (l result : Ledger p eta heta hcap n hn)
    (h : finishRound l = .success result) :
    result = finishRoundCandidate l := by
  unfold finishRound at h
  repeat (first | split at h | dsimp only at h)
  all_goals first | contradiction | (injection h with heq; cases heq; rfl)

/-- A successful `StartRound` returns the same cursor it was asked to start. -/
theorem startRound_success_cursor
    (l result : Ledger p eta heta hcap n hn) (t : ℕ) (enabled : Bool)
    (raw : Option (Fin p.K × ℕ))
    (h : startRound l t enabled raw = .success result) : result.cursor = t := by
  unfold startRound at h
  repeat (first | split at h | dsimp only at h)
  all_goals
    first
    | contradiction
    | (injection h with hresult; cases hresult;
        simp [startRoundCandidate, sourceRound]; omega)

/-- A successful checked start must use the ledger's current chronological
source round. -/
theorem startRound_success_time
    (l result : Ledger p eta heta hcap n hn) (t : ℕ) (enabled : Bool)
    (raw : Option (Fin p.K × ℕ))
    (h : startRound l t enabled raw = .success result) : t = l.cursor := by
  unfold startRound at h
  repeat (first | split at h | dsimp only at h)
  all_goals first | contradiction | omega

/-- The checked stage (1) writes exactly its supplied enable bit at the
calendar index that names the current source round. -/
theorem startRound_success_history_update
    (l result : Ledger p eta heta hcap n hn) (r : Fin p.T) (enabled : Bool)
    (raw : Option (Fin p.K × ℕ))
    (h : startRound l (sourceRound r) enabled raw = .success result) :
    result.enabledHistory = Function.update l.enabledHistory r (some enabled) := by
  unfold startRound at h
  repeat (first | split at h | dsimp only at h)
  all_goals
    first
    | contradiction
    | (injection h with hresult; cases hresult
       have hfin : (⟨sourceRound r - 1, by omega⟩ : Fin p.T) = r := by
         apply Fin.ext
         simp [sourceRound]
       rw [hfin]
       simp [startRoundCandidate])

/-- The raw recorder result supplied for one calendar round, extended by
absence at every other calendar index. -/
def singleRoundSequence (r : Fin p.T)
    (raw : Option (Fin p.K × ℕ)) : Fin p.T → Option (Fin p.K × ℕ) :=
  fun s => if s = r then raw else none

/-- A successful checked stage (1) has exactly the literal candidate value. -/
theorem startRound_success_candidate
    (l result : Ledger p eta heta hcap n hn) (t : ℕ) (enabled : Bool)
    (raw : Option (Fin p.K × ℕ))
    (h : startRound l t enabled raw = .success result) :
    result = startRoundCandidate l ⟨t - 1, by
      have hinput : validLedgerCheck l = true ∧ l.phase = .ready ∧
          t = l.cursor ∧ 1 ≤ t ∧ t ≤ p.T ∧ rawInputDomainCheck raw = true := by
        unfold startRound at h
        by_contra hnot
        simp [hnot] at h
      rcases hinput with ⟨_, _, _, _, ht, _⟩
      omega⟩ enabled raw := by
  unfold startRound at h
  repeat (first | split at h | dsimp only at h)
  all_goals first | contradiction | (injection h with heq; cases heq; rfl)

/-- The actual checked stage (1) realizes the existing cellwise generated
buffer formula for its explicit one-round recorder sequence. `knownBefore`
is read from the input ledger; no generated-buffer equality is assumed. -/
theorem startRound_success_generatedBuffer
    (l result : Ledger p eta heta hcap n hn) (r : Fin p.T) (enabled : Bool)
    (raw : Option (Fin p.K × ℕ))
    (h : startRound l (sourceRound r) enabled raw = .success result) :
    result.rawBuffer = generatedBuffer l.rawBuffer (singleRoundSequence r raw)
      (fun _ a => decide ((l.currentRegisters a).isSome)) l.freezeAt := by
  have hcand := startRound_success_candidate l result (sourceRound r)
    enabled raw h
  have hindex : (⟨sourceRound r - 1, by
      simp [sourceRound]⟩ : Fin p.T) = r := by
    apply Fin.ext
    simp [sourceRound]
  rw [hcand]
  simp only [hindex]
  funext a s
  by_cases hround : s = r
  · subst s
    cases raw with
    | none => simp [startRoundCandidate, generatedBuffer, explicitArrivalCell,
        singleRoundSequence, stageOneBufferCell]
    | some pair =>
        rcases pair with ⟨b, amount⟩
        by_cases harm : b = a
        · subst b
          by_cases hzero : amount = 0
          · simp [startRoundCandidate, generatedBuffer, explicitArrivalCell,
              singleRoundSequence, stageOneBufferCell, hzero]
          · by_cases hknown : l.currentRegisters a = none
            · have hpositive : 0 < amount := by omega
              by_cases hbefore : sourceRound r < l.freezeAt
              · simp [startRoundCandidate, generatedBuffer, explicitArrivalCell,
                  singleRoundSequence, stageOneBufferCell, hzero, hpositive,
                  hknown, hbefore]
                exact putRaw_same l.rawBuffer a r amount
              · simp [startRoundCandidate, generatedBuffer, explicitArrivalCell,
                  singleRoundSequence, stageOneBufferCell, hzero, hpositive,
                  hknown, hbefore]
            · cases hreg : l.currentRegisters a with
              | none => exact (hknown hreg).elim
              | some reg =>
                  simp [startRoundCandidate, generatedBuffer, explicitArrivalCell,
                    singleRoundSequence, stageOneBufferCell, hzero, hreg]
        · by_cases hcond : l.currentRegisters b = none ∧ 0 < amount ∧
              sourceRound r < l.freezeAt
          · simp [startRoundCandidate, generatedBuffer, explicitArrivalCell,
              singleRoundSequence, stageOneBufferCell, hcond, harm, putRaw,
              (show a ≠ b from fun hab => harm hab.symm)]
          · simp [startRoundCandidate, generatedBuffer, explicitArrivalCell,
              singleRoundSequence, stageOneBufferCell, harm, hcond]
  · cases raw with
    | none => simp [startRoundCandidate, generatedBuffer, explicitArrivalCell,
        singleRoundSequence, stageOneBufferCell]
    | some pair =>
        rcases pair with ⟨b, amount⟩
        by_cases hcond : l.currentRegisters b = none ∧ 0 < amount ∧
            sourceRound r < l.freezeAt
        · simp [startRoundCandidate, generatedBuffer, explicitArrivalCell,
            singleRoundSequence, stageOneBufferCell, hround, hcond, putRaw]
        · simp [startRoundCandidate, generatedBuffer, explicitArrivalCell,
            singleRoundSequence, stageOneBufferCell, hround, hcond]

/-- Every non-invalid result of the literal UP decoder preserves the
calendar cursor; rejection remains a returned ordinary ledger. -/
theorem decodeUp_cursor_behavior
    (l : Ledger p eta heta hcap n hn) (i : Fin (p.m - 1))
    (parsed : Option (UpRecord (codecParams p eta))) :
    (match decodeUp l i parsed with
      | .success result =>
          result.cursor = l.cursor ∧ result.enabledHistory = l.enabledHistory
      | .rejected result =>
          result.cursor = l.cursor ∧ result.enabledHistory = l.enabledHistory
      | .invalid => True) := by
  cases parsed with
  | none =>
      by_cases hinput : validLedgerCheck l = true ∧ l.phase = .started ∧
          1 ≤ l.cutoff ∧ l.cutoff ≤ l.cursor ∧ l.cursor ≤ p.T
      · let next : Ledger p eta heta hcap n hn := { l with phase := .decoded }
        by_cases hvalid : validLedgerCheck next = true <;>
          simp [decodeUp, hinput, next, hvalid]
      · simp [decodeUp, hinput]

  | some M =>
      by_cases hinput : validLedgerCheck l = true ∧ l.phase = .started ∧
          1 ≤ l.cutoff ∧ l.cutoff ≤ l.cursor ∧ l.cursor ≤ p.T
      · by_cases haccept : acceptUpCheck l i M = true
        · by_cases hunknown :
              l.currentRegisters (l.assignment.arm i) = none ∧
                l.cutoffRegisters (l.assignment.arm i) = none
          · let prefixIndices := calendarIndices p.T (l.cutoff - 1)
                (l.cursor - l.cutoff) (by omega)
            let lastIndex : Fin p.T := ⟨l.cursor - 1, by omega⟩
            cases hpast : replayRecords? l (l.assignment.arm i) prefixIndices with
            | none => simp [decodeUp, hinput, haccept, hunknown, prefixIndices,
                hpast]
            | some past =>
                cases hlast : replayRecords? l (l.assignment.arm i) [lastIndex] with
                | none => simp [decodeUp, hinput, haccept, hunknown, prefixIndices,
                    lastIndex, hpast, hlast]
                | some records =>
                    cases records with
                    | nil => simp [decodeUp, hinput, haccept, hunknown,
                        prefixIndices, lastIndex, hpast, hlast]
                    | cons record tail =>
                        cases tail with
                        | nil =>
                            by_cases hdomain : replayOutputDomainsCheck (p := p)
                                (4 * n) M.val.q (past ++ [record]) = true
                            · by_cases hvalid : validLedgerCheck
                                  (acceptUpCandidate l i M past record) = true
                              · simp only [decodeUp, hinput, haccept, hunknown,
                                  prefixIndices, lastIndex, hpast, hlast, hdomain, hvalid]
                                simp [acceptUpCandidate]
                              · simp [decodeUp, hinput, haccept, hunknown,
                                  prefixIndices, lastIndex, hpast, hlast, hdomain, hvalid]
                            · simp [decodeUp, hinput, haccept, hunknown,
                                prefixIndices, lastIndex, hpast, hlast, hdomain]
                        | cons _ _ => simp [decodeUp, hinput, haccept, hunknown,
                            prefixIndices, lastIndex, hpast, hlast]
          · simp [decodeUp, hinput, haccept, hunknown]
        · let next : Ledger p eta heta hcap n hn := { l with phase := .decoded }
          by_cases hvalid : validLedgerCheck next = true <;>
            simp [decodeUp, hinput, haccept, next, hvalid]
      · simp [decodeUp, hinput]

/-- Successful decoding is the literal accepted candidate built from the
decoder's actual replay prefix and its actual acceptance-round record. -/
theorem decodeUp_success_candidate
    (l result : Ledger p eta heta hcap n hn) (i : Fin (p.m - 1))
    (M : UpRecord (codecParams p eta))
    (h : decodeUp l i (some M) = .success result) :
    ∃ hbound : l.cutoff - 1 + (l.cursor - l.cutoff) ≤ p.T,
      ∃ lastIndex : Fin p.T,
        sourceRound lastIndex = l.cursor ∧
        ∃ past current,
          replayRecords? l (l.assignment.arm i)
              (calendarIndices p.T (l.cutoff - 1)
                (l.cursor - l.cutoff) hbound) = some past ∧
          replayRecords? l (l.assignment.arm i) [lastIndex] = some [current] ∧
          l.currentRegisters (l.assignment.arm i) = none ∧
          result = acceptUpCandidate l i M past current := by
  by_cases hinput : validLedgerCheck l = true ∧ l.phase = .started ∧
      1 ≤ l.cutoff ∧ l.cutoff ≤ l.cursor ∧ l.cursor ≤ p.T
  · by_cases haccept : acceptUpCheck l i M = true
    · by_cases hunknown : l.currentRegisters (l.assignment.arm i) = none ∧
          l.cutoffRegisters (l.assignment.arm i) = none
      · have hcutPos := hinput.2.2.1
        have hcutCursor := hinput.2.2.2.1
        have hcursorT := hinput.2.2.2.2
        have hprefix : l.cutoff - 1 + (l.cursor - l.cutoff) ≤ p.T := by omega
        let prefixIndices := calendarIndices p.T (l.cutoff - 1)
          (l.cursor - l.cutoff) hprefix
        let lastIndex : Fin p.T := ⟨l.cursor - 1, by omega⟩
        cases hpast : replayRecords? l (l.assignment.arm i) prefixIndices with
        | none => simp [decodeUp, hinput, haccept, hunknown, prefixIndices,
            hpast] at h
        | some past =>
            cases hlast : replayRecords? l (l.assignment.arm i) [lastIndex] with
            | none => simp [decodeUp, hinput, haccept, hunknown, prefixIndices,
                lastIndex, hpast, hlast] at h
            | some records =>
                cases records with
                | nil => simp [decodeUp, hinput, haccept, hunknown,
                    prefixIndices, lastIndex, hpast, hlast] at h
                | cons current tail =>
                    cases tail with
                    | nil =>
                        by_cases hdomain : replayOutputDomainsCheck (p := p)
                            (4 * n) M.val.q (past ++ [current]) = true
                        · by_cases hvalid : validLedgerCheck
                              (acceptUpCandidate l i M past current) = true
                          · simp only [decodeUp, hinput, haccept, hunknown,
                              prefixIndices, lastIndex, hpast, hlast, hdomain,
                              hvalid] at h
                            injection h with hresult
                            subst result
                            have hlastSource : sourceRound lastIndex = l.cursor := by
                              dsimp [sourceRound, lastIndex]
                              omega
                            exact ⟨hprefix, lastIndex, hlastSource, past,
                              current, hpast, hlast, hunknown.1, rfl⟩
                          · simp [decodeUp, hinput, haccept, hunknown,
                              prefixIndices, lastIndex, hpast, hlast, hdomain,
                              hvalid] at h
                        · simp [decodeUp, hinput, haccept, hunknown,
                            prefixIndices, lastIndex, hpast, hlast, hdomain] at h
                    | cons _ _ => simp [decodeUp, hinput, haccept, hunknown,
                        prefixIndices, lastIndex, hpast, hlast] at h
      · simp [decodeUp, hinput, haccept, hunknown] at h
    · let next : Ledger p eta heta hcap n hn := { l with phase := .decoded }
      by_cases hvalid : validLedgerCheck next = true <;>
        simp [decodeUp, hinput, haccept, next, hvalid] at h
  · simp [decodeUp, hinput] at h

/-- On an actual successful acceptance round, the actual checked finish adds
no local service a second time: the completed increment is the `M.q` replay
through the decoder's supplied current record. -/
theorem checked_acceptance_finish_once
    (l started decoded finished : Ledger p eta heta hcap n hn)
    (t : ℕ) (enabled : Bool) (raw : Option (Fin p.K × ℕ))
    (i : Fin (p.m - 1)) (M : UpRecord (codecParams p eta))
    (hstart : startRound l t enabled raw = .success started)
    (hdecode : decodeUp started i (some M) = .success decoded)
    (hfinish : finishRound decoded = .success finished) :
    ∃ hbound : started.cutoff - 1 + (started.cursor - started.cutoff) ≤ p.T,
      ∃ lastIndex : Fin p.T,
        sourceRound lastIndex = t ∧
        ∃ past current,
          replayRecords? started (started.assignment.arm i)
              (calendarIndices p.T (started.cutoff - 1)
                (started.cursor - started.cutoff) hbound) = some past ∧
          replayRecords? started (started.assignment.arm i) [lastIndex] =
            some [current] ∧
          started.currentRegisters (started.assignment.arm i) = none ∧
          finished.currentRegisters (started.assignment.arm i) =
              some ⟨(QueueReplay.replay (4 * n) (0, M.val.q)
                  (past ++ [current])).2,
                (QueueReplay.replay (4 * n) (0, M.val.q)
                  (past ++ [current])).1 -
                  (QueueReplay.replay (4 * n) (0, M.val.q) past).1⟩ ∧
            finished.increment (started.assignment.arm i) =
              (QueueReplay.replay (4 * n) (0, M.val.q)
                (past ++ [current])).1 ∧
            finished.cutoffRegisters (started.assignment.arm i) =
              some ⟨started.baseScore i + M.val.S, M.val.q, M.val.delta⟩ := by
  obtain ⟨hbound, lastIndex, hlastSource, past, current,
      hpast, hlast, hunknown, hdecodedCandidate⟩ :=
    decodeUp_success_candidate started decoded i M hdecode
  have hstartedCandidate := startRound_success_candidate l started t
    enabled raw hstart
  have hstartedCursor := startRound_success_cursor l started t enabled raw hstart
  have hlastSourceT : sourceRound lastIndex = t := hlastSource.trans hstartedCursor
  have hassign : started.assignment = l.assignment := by
    rw [hstartedCandidate]
    rfl
  have harm := congrArg (fun assignment : Assignment p => assignment.arm i) hassign
  have hinitialUnknown : l.currentRegisters (l.assignment.arm i) = none := by
    have htemp := hunknown
    rw [hstartedCandidate] at htemp
    cases hreg : l.currentRegisters (l.assignment.arm i) with
    | none => rfl
    | some currentReg => simp [startRoundCandidate, hreg] at htemp
  have hgamma : started.gammaLoc (l.assignment.arm i) = 0 := by
    rw [hstartedCandidate]
    simp [startRoundCandidate, hinitialUnknown]
  have hgammaStarted : started.gammaLoc (started.assignment.arm i) = 0 := by
    rw [harm]
    exact hgamma
  have honce := finish_recovered_increment_once started i M past current
    hunknown hgammaStarted
  have hfinishedCandidate := finishRound_success_candidate decoded finished hfinish
  have hfields := acceptUpCandidate_recovered_fields started i M past current
  have hcurrent : finished.currentRegisters (started.assignment.arm i) =
      some ⟨(QueueReplay.replay (4 * n) (0, M.val.q)
          (past ++ [current])).2,
        (QueueReplay.replay (4 * n) (0, M.val.q)
          (past ++ [current])).1 -
          (QueueReplay.replay (4 * n) (0, M.val.q) past).1⟩ := by
    rw [hfinishedCandidate, hdecodedCandidate]
    simpa [finishRoundCandidate] using hfields.1
  have hincrement : finished.increment (started.assignment.arm i) =
      (QueueReplay.replay (4 * n) (0, M.val.q)
        (past ++ [current])).1 := by
    calc
    finished.increment (started.assignment.arm i) =
        (finishRoundCandidate decoded).increment (started.assignment.arm i) := by
      rw [hfinishedCandidate]
    _ = (finishRoundCandidate
        (acceptUpCandidate started i M past current)).increment
          (started.assignment.arm i) := by rw [hdecodedCandidate]
    _ = (replayResult (4 * n) M.val.q past current).registers.1 := honce.2.2
    _ = (QueueReplay.replay (4 * n) (0, M.val.q)
        (past ++ [current])).1 := rfl
  have hcutoff : finished.cutoffRegisters (started.assignment.arm i) =
      some ⟨started.baseScore i + M.val.S, M.val.q, M.val.delta⟩ := by
    rw [hfinishedCandidate, hdecodedCandidate]
    simpa [finishRoundCandidate] using hfields.2.2
  exact ⟨hbound, lastIndex, hlastSourceT, past, current,
    hpast, hlast, hunknown, hcurrent, hincrement, hcutoff⟩

/-- Every successful execution has one successful `FinishRound` for each
supplied input, starts at the actual checked initializer cursor, and ends
ready at the cursor advanced by the exact number of inputs. -/
theorem checkedRounds_success_chronology
    (l final : Ledger p eta heta hcap n hn) (hready : l.phase = .ready)
    (inputs : List (RoundInput (p := p) (eta := eta)))
    (accepted : List Bool)
    (h : checkedRounds l inputs = some (accepted, final)) :
    final.cursor = l.cursor + inputs.length ∧ final.phase = .ready := by
  induction inputs generalizing l accepted final with
  | nil =>
      simp [checkedRounds] at h
      rcases h with ⟨rfl, rfl⟩
      exact ⟨rfl, hready⟩
  | cons input rest ih =>
      cases hs : startRound l (sourceRound input.round) input.enabled input.raw with
      | invalid => simp [checkedRounds, hs] at h
      | rejected bad => simp [checkedRounds, hs] at h
      | success started =>
          cases hd : decodeUp started input.selectedFollower input.parsed with
          | invalid => simp [checkedRounds, hs, hd] at h
          | rejected badDecode =>
              cases hf : finishRound badDecode with
              | invalid => simp [checkedRounds, hs, hd, hf] at h
              | rejected badFinish => simp [checkedRounds, hs, hd, hf] at h
              | success finished =>
                  cases hr : checkedRounds finished rest with
                  | none => simp [checkedRounds, hs, hd, hf, hr] at h
                  | some pair =>
                      simp [checkedRounds, hs, hd, hf, hr] at h
                      rcases h with ⟨rfl, rfl⟩
                      have hfinish := finishRound_success_chronology badDecode finished hf
                      obtain ⟨hcursor, hphase⟩ :=
                        ih finished pair.2 hfinish.2.1 pair.1 hr
                      have hstart := startRound_success_cursor l started
                        (sourceRound input.round)
                        input.enabled input.raw hs
                      have htime := startRound_success_time l started
                        (sourceRound input.round) input.enabled input.raw hs
                      have hdecode := decodeUp_cursor_behavior started
                        input.selectedFollower input.parsed
                      rw [hd] at hdecode
                      simp at hdecode
                      constructor
                      · rw [hcursor, hfinish.1]
                        rw [hdecode.1, hstart, htime]
                        simp [List.length, Nat.add_assoc]
                        omega
                      · exact hphase
          | success decoded =>
              cases hf : finishRound decoded with
              | invalid => simp [checkedRounds, hs, hd, hf] at h
              | rejected bad => simp [checkedRounds, hs, hd, hf] at h
              | success finished =>
                  cases hr : checkedRounds finished rest with
                  | none => simp [checkedRounds, hs, hd, hf, hr] at h
                  | some pair =>
                      simp [checkedRounds, hs, hd, hf, hr] at h
                      rcases h with ⟨rfl, rfl⟩
                      have hfinish := finishRound_success_chronology decoded finished hf
                      obtain ⟨hcursor, hphase⟩ :=
                        ih finished pair.2 hfinish.2.1 pair.1 hr
                      have hstart := startRound_success_cursor l started
                        (sourceRound input.round) input.enabled input.raw hs
                      have htime := startRound_success_time l started
                        (sourceRound input.round) input.enabled input.raw hs
                      have hdecode := decodeUp_cursor_behavior started
                        input.selectedFollower input.parsed
                      rw [hd] at hdecode
                      simp at hdecode
                      constructor
                      · rw [hcursor, hfinish.1]
                        rw [hdecode.1, hstart, htime]
                        simp [List.length, Nat.add_assoc]
                        omega
                      · exact hphase

/-- Every supplied round label in a successful fold equals the cursor at its
actual `StartRound` call, in list order. -/
theorem checkedRounds_success_input_chronology
    (l final : Ledger p eta heta hcap n hn)
    (inputs : List (RoundInput (p := p) (eta := eta)))
    (accepted : List Bool)
    (h : checkedRounds l inputs = some (accepted, final)) :
    chronologicalFrom l.cursor inputs := by
  induction inputs generalizing l accepted final with
  | nil => simp [checkedRounds, chronologicalFrom] at h ⊢
  | cons input rest ih =>
      cases hs : startRound l (sourceRound input.round) input.enabled input.raw with
      | invalid => simp [checkedRounds, hs] at h
      | rejected bad => simp [checkedRounds, hs] at h
      | success started =>
          cases hd : decodeUp started input.selectedFollower input.parsed with
          | invalid => simp [checkedRounds, hs, hd] at h
          | rejected decoded =>
              cases hf : finishRound decoded with
              | invalid => simp [checkedRounds, hs, hd, hf] at h
              | rejected bad => simp [checkedRounds, hs, hd, hf] at h
              | success finished =>
                  cases hr : checkedRounds finished rest with
                  | none => simp [checkedRounds, hs, hd, hf, hr] at h
                  | some pair =>
                      simp [checkedRounds, hs, hd, hf, hr] at h
                      rcases h with ⟨rfl, rfl⟩
                      have htail := ih finished pair.2 pair.1 hr
                      have hstart := startRound_success_cursor l started
                        (sourceRound input.round) input.enabled input.raw hs
                      have htime := startRound_success_time l started
                        (sourceRound input.round) input.enabled input.raw hs
                      have hdecode := decodeUp_cursor_behavior started
                        input.selectedFollower input.parsed
                      rw [hd] at hdecode
                      simp at hdecode
                      have hfinish := finishRound_success_chronology decoded finished hf
                      have hnext : finished.cursor = l.cursor + 1 := by
                        rw [hfinish.1, hdecode.1, hstart, htime]
                      exact ⟨htime, by simpa [hnext] using htail⟩
          | success decoded =>
              cases hf : finishRound decoded with
              | invalid => simp [checkedRounds, hs, hd, hf] at h
              | rejected bad => simp [checkedRounds, hs, hd, hf] at h
              | success finished =>
                  cases hr : checkedRounds finished rest with
                  | none => simp [checkedRounds, hs, hd, hf, hr] at h
                  | some pair =>
                      simp [checkedRounds, hs, hd, hf, hr] at h
                      rcases h with ⟨rfl, rfl⟩
                      have htail := ih finished pair.2 pair.1 hr
                      have hstart := startRound_success_cursor l started
                        (sourceRound input.round) input.enabled input.raw hs
                      have htime := startRound_success_time l started
                        (sourceRound input.round) input.enabled input.raw hs
                      have hdecode := decodeUp_cursor_behavior started
                        input.selectedFollower input.parsed
                      rw [hd] at hdecode
                      simp at hdecode
                      have hfinish := finishRound_success_chronology decoded finished hf
                      have hnext : finished.cursor = l.cursor + 1 := by
                        rw [hfinish.1, hdecode.1, hstart, htime]
                      exact ⟨htime, by simpa [hnext] using htail⟩

/-- A successful continuation never rewrites enable-history entries from
strictly earlier source rounds. -/
theorem checkedRounds_preserves_past_history
    (l final : Ledger p eta heta hcap n hn)
    (inputs : List (RoundInput (p := p) (eta := eta)))
    (accepted : List Bool)
    (h : checkedRounds l inputs = some (accepted, final))
    (r : Fin p.T) (hpast : sourceRound r < l.cursor) :
    final.enabledHistory r = l.enabledHistory r := by
  induction inputs generalizing l accepted final r with
  | nil =>
      simp [checkedRounds] at h
      rcases h with ⟨rfl, rfl⟩
      rfl
  | cons input rest ih =>
      cases hs : startRound l (sourceRound input.round) input.enabled input.raw with
      | invalid => simp [checkedRounds, hs] at h
      | rejected bad => simp [checkedRounds, hs] at h
      | success started =>
          cases hd : decodeUp started input.selectedFollower input.parsed with
          | invalid => simp [checkedRounds, hs, hd] at h
          | rejected decoded =>
              cases hf : finishRound decoded with
              | invalid => simp [checkedRounds, hs, hd, hf] at h
              | rejected bad => simp [checkedRounds, hs, hd, hf] at h
              | success finished =>
                  cases hr : checkedRounds finished rest with
                  | none => simp [checkedRounds, hs, hd, hf, hr] at h
                  | some pair =>
                      simp [checkedRounds, hs, hd, hf, hr] at h
                      rcases h with ⟨rfl, rfl⟩
                      have hstart := startRound_success_cursor l started
                        (sourceRound input.round) input.enabled input.raw hs
                      have htime := startRound_success_time l started
                        (sourceRound input.round) input.enabled input.raw hs
                      have hstartHistory := startRound_success_history_update l
                        started input.round input.enabled input.raw hs
                      have hdecode := decodeUp_cursor_behavior started
                        input.selectedFollower input.parsed
                      rw [hd] at hdecode
                      simp at hdecode
                      have hfinish := finishRound_success_chronology decoded finished hf
                      have hfuture : sourceRound r < finished.cursor := by
                        rw [hfinish.1, hdecode.1, hstart, htime]
                        omega
                      have htail := ih finished pair.2 pair.1 hr r hfuture
                      have hne : r ≠ input.round := by
                        intro heq
                        subst r
                        omega
                      calc
                        pair.2.enabledHistory r = finished.enabledHistory r := htail
                        _ = decoded.enabledHistory r := congrFun hfinish.2.2 r
                        _ = started.enabledHistory r := congrFun hdecode.2 r
                        _ = l.enabledHistory r := by
                          rw [hstartHistory, Function.update_of_ne hne]
          | success decoded =>
              cases hf : finishRound decoded with
              | invalid => simp [checkedRounds, hs, hd, hf] at h
              | rejected bad => simp [checkedRounds, hs, hd, hf] at h
              | success finished =>
                  cases hr : checkedRounds finished rest with
                  | none => simp [checkedRounds, hs, hd, hf, hr] at h
                  | some pair =>
                      simp [checkedRounds, hs, hd, hf, hr] at h
                      rcases h with ⟨rfl, rfl⟩
                      have hstart := startRound_success_cursor l started
                        (sourceRound input.round) input.enabled input.raw hs
                      have htime := startRound_success_time l started
                        (sourceRound input.round) input.enabled input.raw hs
                      have hstartHistory := startRound_success_history_update l
                        started input.round input.enabled input.raw hs
                      have hdecode := decodeUp_cursor_behavior started
                        input.selectedFollower input.parsed
                      rw [hd] at hdecode
                      simp at hdecode
                      have hfinish := finishRound_success_chronology decoded finished hf
                      have hfuture : sourceRound r < finished.cursor := by
                        rw [hfinish.1, hdecode.1, hstart, htime]
                        omega
                      have htail := ih finished pair.2 pair.1 hr r hfuture
                      have hne : r ≠ input.round := by
                        intro heq
                        subst r
                        omega
                      calc
                        pair.2.enabledHistory r = finished.enabledHistory r := htail
                        _ = decoded.enabledHistory r := congrFun hfinish.2.2 r
                        _ = started.enabledHistory r := congrFun hdecode.2 r
                        _ = l.enabledHistory r := by
                          rw [hstartHistory, Function.update_of_ne hne]

/-- Every supplied calendar-round enable bit is present unchanged in the
terminal checked ledger. This follows from the checked stage (1), decode, and
finish calls in the fold. -/
theorem checkedRounds_records_supplied_enables
    (l final : Ledger p eta heta hcap n hn)
    (inputs : List (RoundInput (p := p) (eta := eta)))
    (accepted : List Bool)
    (h : checkedRounds l inputs = some (accepted, final)) :
    ∀ input ∈ inputs, final.enabledHistory input.round = some input.enabled := by
  induction inputs generalizing l accepted final with
  | nil =>
      simp [checkedRounds] at h
      rcases h with ⟨rfl, rfl⟩
      simp
  | cons input rest ih =>
      cases hs : startRound l (sourceRound input.round) input.enabled input.raw with
      | invalid => simp [checkedRounds, hs] at h
      | rejected bad => simp [checkedRounds, hs] at h
      | success started =>
          cases hd : decodeUp started input.selectedFollower input.parsed with
          | invalid => simp [checkedRounds, hs, hd] at h
          | rejected decoded =>
              cases hf : finishRound decoded with
              | invalid => simp [checkedRounds, hs, hd, hf] at h
              | rejected bad => simp [checkedRounds, hs, hd, hf] at h
              | success finished =>
                  cases hr : checkedRounds finished rest with
                  | none => simp [checkedRounds, hs, hd, hf, hr] at h
                  | some pair =>
                      simp [checkedRounds, hs, hd, hf, hr] at h
                      rcases h with ⟨rfl, rfl⟩
                      intro current hmember
                      simp only [List.mem_cons] at hmember
                      rcases hmember with heq | hmember
                      · cases heq
                        have hstart := startRound_success_cursor l started
                          (sourceRound input.round) input.enabled input.raw hs
                        have htime := startRound_success_time l started
                          (sourceRound input.round) input.enabled input.raw hs
                        have hstartHistory := startRound_success_history_update l
                          started input.round input.enabled input.raw hs
                        have hdecode := decodeUp_cursor_behavior started
                          input.selectedFollower input.parsed
                        rw [hd] at hdecode
                        simp at hdecode
                        have hfinish := finishRound_success_chronology decoded finished hf
                        have hfuture : sourceRound input.round < finished.cursor := by
                          rw [hfinish.1, hdecode.1, hstart, htime]
                          omega
                        have htail := checkedRounds_preserves_past_history
                          finished pair.2 rest pair.1 hr input.round hfuture
                        calc
                          pair.2.enabledHistory input.round =
                              finished.enabledHistory input.round := htail
                          _ = decoded.enabledHistory input.round :=
                            congrFun hfinish.2.2 input.round
                          _ = started.enabledHistory input.round :=
                            congrFun hdecode.2 input.round
                          _ = some input.enabled := by
                            rw [hstartHistory, Function.update_self]
                      · exact ih finished pair.2 pair.1 hr current hmember
          | success decoded =>
              cases hf : finishRound decoded with
              | invalid => simp [checkedRounds, hs, hd, hf] at h
              | rejected bad => simp [checkedRounds, hs, hd, hf] at h
              | success finished =>
                  cases hr : checkedRounds finished rest with
                  | none => simp [checkedRounds, hs, hd, hf, hr] at h
                  | some pair =>
                      simp [checkedRounds, hs, hd, hf, hr] at h
                      rcases h with ⟨rfl, rfl⟩
                      intro current hmember
                      simp only [List.mem_cons] at hmember
                      rcases hmember with heq | hmember
                      · cases heq
                        have hstart := startRound_success_cursor l started
                          (sourceRound input.round) input.enabled input.raw hs
                        have htime := startRound_success_time l started
                          (sourceRound input.round) input.enabled input.raw hs
                        have hstartHistory := startRound_success_history_update l
                          started input.round input.enabled input.raw hs
                        have hdecode := decodeUp_cursor_behavior started
                          input.selectedFollower input.parsed
                        rw [hd] at hdecode
                        simp at hdecode
                        have hfinish := finishRound_success_chronology decoded finished hf
                        have hfuture : sourceRound input.round < finished.cursor := by
                          rw [hfinish.1, hdecode.1, hstart, htime]
                          omega
                        have htail := checkedRounds_preserves_past_history
                          finished pair.2 rest pair.1 hr input.round hfuture
                        calc
                          pair.2.enabledHistory input.round =
                              finished.enabledHistory input.round := htail
                          _ = decoded.enabledHistory input.round :=
                            congrFun hfinish.2.2 input.round
                          _ = started.enabledHistory input.round :=
                            congrFun hdecode.2 input.round
                          _ = some input.enabled := by
                            rw [hstartHistory, Function.update_self]
                      · exact ih finished pair.2 pair.1 hr current hmember

/-- A successful top-level fold exposes the exact cursor/phase chronology
from the successful value returned by `startCollectionChecked`. -/
theorem startCollectionChecked_success_ready
    (p : ConstructorDimensions.Parameters) (eta : ℝ) (heta : 0 < eta)
    (hcap : sourceLearningCap p eta) (n : ℕ)
    (hn : (n : ℝ) = eta * (ConstructorDimensions.D p : ℝ))
    (assignment : Assignment p) (sigma cutoff freezeAt : ℕ)
    (baseScore : Fin (p.m - 1) → ℕ)
    (outside : Fin p.K → Option CutoffRegister)
    (initial : Ledger p eta heta hcap n hn)
    (h : startCollectionChecked p eta heta hcap n hn assignment sigma cutoff
      freezeAt baseScore outside = .success initial) : initial.phase = .ready := by
  unfold startCollectionChecked at h
  repeat (first | split at h | dsimp only at h)
  all_goals
    first
    | contradiction
    | (injection h with heq; cases heq; rfl)

/-- The actual checked initializer starts with every arm/calendar raw-buffer
cell empty. -/
theorem startCollectionChecked_success_empty_rawBuffer
    (p : ConstructorDimensions.Parameters) (eta : ℝ) (heta : 0 < eta)
    (hcap : sourceLearningCap p eta) (n : ℕ)
    (hn : (n : ℝ) = eta * (ConstructorDimensions.D p : ℝ))
    (assignment : Assignment p) (sigma cutoff freezeAt : ℕ)
    (baseScore : Fin (p.m - 1) → ℕ)
    (outside : Fin p.K → Option CutoffRegister)
    (initial : Ledger p eta heta hcap n hn)
    (h : startCollectionChecked p eta heta hcap n hn assignment sigma cutoff
      freezeAt baseScore outside = .success initial) :
    ∀ a r, initial.rawBuffer a r = none := by
  unfold startCollectionChecked at h
  repeat (first | split at h | dsimp only at h)
  all_goals
    first
    | contradiction
    | (injection h with heq; cases heq; intro a r; rfl)

theorem startAndRunChecked_success_chronology
    (p : ConstructorDimensions.Parameters) (eta : ℝ) (heta : 0 < eta)
    (hcap : sourceLearningCap p eta) (n : ℕ)
    (hn : (n : ℝ) = eta * (ConstructorDimensions.D p : ℝ))
    (assignment : Assignment p) (sigma cutoff freezeAt : ℕ)
    (baseScore : Fin (p.m - 1) → ℕ)
    (outside : Fin p.K → Option CutoffRegister)
    (inputs : List (RoundInput (p := p) (eta := eta)))
    (execution : Execution p eta heta hcap n hn)
    (h : startAndRunChecked p eta heta hcap n hn assignment sigma cutoff
      freezeAt baseScore outside inputs = .success execution) :
    execution.final.cursor = execution.initial.cursor + inputs.length ∧
      execution.final.phase = .ready := by
  cases hs : startCollectionChecked p eta heta hcap n hn assignment sigma cutoff
      freezeAt baseScore outside with
  | invalid => simp [startAndRunChecked, hs] at h
  | rejected bad => simp [startAndRunChecked, hs] at h
  | success initial =>
      cases hr : checkedRounds initial inputs with
      | none => simp [startAndRunChecked, hs, hr] at h
      | some pair =>
          simp [startAndRunChecked, hs, hr] at h
          cases h
          exact checkedRounds_success_chronology initial pair.2
            (startCollectionChecked_success_ready p eta heta hcap n hn assignment
              sigma cutoff freezeAt baseScore outside initial hs)
            inputs pair.1 hr

/-- Every supplied enable bit survives into its actual calendar entry in the
terminal ledger returned by the checked initializer and fold. -/
theorem startAndRunChecked_success_records_supplied_enables
    (p : ConstructorDimensions.Parameters) (eta : ℝ) (heta : 0 < eta)
    (hcap : sourceLearningCap p eta) (n : ℕ)
    (hn : (n : ℝ) = eta * (ConstructorDimensions.D p : ℝ))
    (assignment : Assignment p) (sigma cutoff freezeAt : ℕ)
    (baseScore : Fin (p.m - 1) → ℕ)
    (outside : Fin p.K → Option CutoffRegister)
    (inputs : List (RoundInput (p := p) (eta := eta)))
    (execution : Execution p eta heta hcap n hn)
    (h : startAndRunChecked p eta heta hcap n hn assignment sigma cutoff
      freezeAt baseScore outside inputs = .success execution) :
    ∀ input ∈ inputs,
      execution.final.enabledHistory input.round = some input.enabled := by
  cases hs : startCollectionChecked p eta heta hcap n hn assignment sigma cutoff
      freezeAt baseScore outside with
  | invalid => simp [startAndRunChecked, hs] at h
  | rejected bad => simp [startAndRunChecked, hs] at h
  | success initial =>
      cases hr : checkedRounds initial inputs with
      | none => simp [startAndRunChecked, hs, hr] at h
      | some pair =>
          simp [startAndRunChecked, hs, hr] at h
          cases h
          exact checkedRounds_records_supplied_enables initial pair.2
            inputs pair.1 hr

/-- The successful top-level fold uses every supplied calendar index in the
exact order from the actual initializer cursor. -/
theorem startAndRunChecked_success_input_chronology
    (p : ConstructorDimensions.Parameters) (eta : ℝ) (heta : 0 < eta)
    (hcap : sourceLearningCap p eta) (n : ℕ)
    (hn : (n : ℝ) = eta * (ConstructorDimensions.D p : ℝ))
    (assignment : Assignment p) (sigma cutoff freezeAt : ℕ)
    (baseScore : Fin (p.m - 1) → ℕ)
    (outside : Fin p.K → Option CutoffRegister)
    (inputs : List (RoundInput (p := p) (eta := eta)))
    (execution : Execution p eta heta hcap n hn)
    (h : startAndRunChecked p eta heta hcap n hn assignment sigma cutoff
      freezeAt baseScore outside inputs = .success execution) :
    chronologicalFrom execution.initial.cursor inputs := by
  cases hs : startCollectionChecked p eta heta hcap n hn assignment sigma cutoff
      freezeAt baseScore outside with
  | invalid => simp [startAndRunChecked, hs] at h
  | rejected bad => simp [startAndRunChecked, hs] at h
  | success initial =>
      cases hr : checkedRounds initial inputs with
      | none => simp [startAndRunChecked, hs, hr] at h
      | some pair =>
          simp [startAndRunChecked, hs, hr] at h
          cases h
          exact checkedRounds_success_input_chronology initial pair.2
            inputs pair.1 hr

end Bandits.Support.CollectionCheckedExecution

end
