/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bandits Lean regret formalization contributors
-/
module

public import Bandits.Support.CollectionCheckedExecution

import Lean.Elab.Tactic.Omega

/-!
# Online continuation of a known collection queue

These conditional checked-operation identities use the coordinator ledger and
the actual `checkedRounds` fold.  The mathematical evidence is
`sources/zip4/manuscript/06_interruptions.tex:16-28,80-100,257-294` and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:46-64`.

The per-round enable bits, recorder results, selected followers, and parsed
records remain explicit inputs.  This module does not certify that those inputs
come from a physical execution or reconstruct the raw decoder buffer.
-/

@[expose] public section

namespace Bandits.Support.CollectionKnownQueueContinuation

open Bandits.Support.CoordinatorCollectionLedger
open Bandits.Support.CollectionCheckedExecution
open Bandits.Support.OrdinaryMessageCodec
open Bandits.Support.QueueReplay

variable {p : ConstructorDimensions.Parameters}
variable {eta : ℝ} {heta : 0 < eta}
  {hcap : sourceLearningCap p eta} {n : ℕ}
  {hn : (n : ℝ) = eta * (ConstructorDimensions.D p : ℝ)}

/-- Map each supplied checked-round input to the existing local known-queue
record, with this ledger's unchanged freeze boundary.  This is only a record
map; execution remains `CollectionCheckedExecution.checkedRounds`. -/
def inputQueueRecords (l : Ledger p eta heta hcap n hn) (a : Fin p.K)
    (inputs : List (RoundInput (p := p) (eta := eta))) : List (Bool × ℕ) :=
  inputs.map fun input => localQueueRecord l input.round input.enabled input.raw a

/-- The service stored by the last replay record, retaining the supplied
service when the record list is empty. -/
def replayLastService (capacity : ℕ) (initial : ℕ × ℕ)
    (retained : ℕ) (records : List (Bool × ℕ)) : ℕ :=
  match records.getLast? with
  | none => retained
  | some record =>
      let before := QueueReplay.replay capacity initial records.dropLast
      (QueueReplay.transition capacity before record).1 - before.1

/-- `localQueueRecord` sends an enabled zero-arrival queue through the literal
service transition. -/
theorem localQueueRecord_enabled_zero_arrival
    (l : Ledger p eta heta hcap n hn) (r : Fin p.T)
    (raw : Option (Fin p.K × ℕ)) (a : Fin p.K)
    (hbefore : sourceRound r < l.freezeAt)
    (hzero : localArrival raw a = 0) :
    localQueueRecord l r true raw a = (true, 0) := by
  simp [localQueueRecord, hbefore, hzero]

/-- Once disabled, or at and after the freeze boundary, the literal local
record preserves a known queue even if collection continues through later
calendar rounds. -/
theorem localQueueRecord_disabled_or_frozen
    (l : Ledger p eta heta hcap n hn) (r : Fin p.T) (enabled : Bool)
    (raw : Option (Fin p.K × ℕ)) (a : Fin p.K)
    (hdisabled : enabled = false ∨ ¬ sourceRound r < l.freezeAt) :
    localQueueRecord l r enabled raw a = (false, 0) := by
  rcases hdisabled with hdisabled | hfrozen
  · subst enabled
    simp [localQueueRecord]
  · cases enabled <;> simp [localQueueRecord, hfrozen]

/-- Enabled zero-arrival service is the literal capped backlog service. -/
theorem known_transition_enabled_zero_arrival
    (capacity score backlog : ℕ) (l : Ledger p eta heta hcap n hn)
    (r : Fin p.T) (raw : Option (Fin p.K × ℕ)) (a : Fin p.K)
    (hbefore : sourceRound r < l.freezeAt)
    (hzero : localArrival raw a = 0) :
    QueueReplay.transition capacity (score, backlog)
        (localQueueRecord l r true raw a) =
      (score + min capacity backlog, backlog - min capacity backlog) := by
  rw [localQueueRecord_enabled_zero_arrival l r raw a hbefore hzero]
  exact QueueReplay.transition_enabled_zero_arrival capacity score backlog

/-- Disabled and frozen rounds preserve both queue registers under the
existing transition, including supplied rounds after the old grid boundary. -/
theorem known_transition_disabled_or_frozen
    (capacity score backlog : ℕ) (l : Ledger p eta heta hcap n hn)
    (r : Fin p.T) (enabled : Bool) (raw : Option (Fin p.K × ℕ))
    (a : Fin p.K)
    (hdisabled : enabled = false ∨ ¬ sourceRound r < l.freezeAt) :
    QueueReplay.transition capacity (score, backlog)
        (localQueueRecord l r enabled raw a) = (score, backlog) := by
  rw [localQueueRecord_disabled_or_frozen l r enabled raw a hdisabled]
  rfl

/-- The final last-service projection splits into the first record and the
literal replay of its remaining records. -/
theorem replayLastService_cons
    (capacity : ℕ) (initial : ℕ × ℕ) (retained : ℕ)
    (record : Bool × ℕ) (rest : List (Bool × ℕ)) :
    replayLastService capacity initial retained (record :: rest) =
      match rest with
      | [] =>
          (QueueReplay.transition capacity initial record).1 - initial.1
      | next :: tail =>
          replayLastService capacity
            (QueueReplay.transition capacity initial record)
            ((QueueReplay.transition capacity initial record).1 - initial.1)
            (next :: tail) := by
  cases rest with
  | nil => simp [replayLastService, QueueReplay.replay]
  | cons next tail =>
      cases hlast : (next :: tail).getLast? with
      | none => simp at hlast
      | some last =>
          simp [replayLastService, QueueReplay.replay,
            List.getLast?_cons_cons, List.dropLast_cons_cons, hlast]

/-- Changing the ledger used for the record map does not change its records
when the literal freeze boundary is the same. -/
theorem inputQueueRecords_freezeAt_eq
    (left right : Ledger p eta heta hcap n hn) (a : Fin p.K)
    (inputs : List (RoundInput (p := p) (eta := eta)))
    (hfreeze : left.freezeAt = right.freezeAt) :
    inputQueueRecords left a inputs = inputQueueRecords right a inputs := by
  simp [inputQueueRecords, localQueueRecord, hfreeze]

/-- Adding an existing accumulator to a one-record queue transition changes
only its score base, not its queue update. -/
theorem queueReplay_transition_add_score
    (capacity score backlog : ℕ) (record : Bool × ℕ) :
    QueueReplay.transition capacity (score, backlog) record =
      (score + (QueueReplay.transition capacity (0, backlog) record).1,
        (QueueReplay.transition capacity (0, backlog) record).2) := by
  cases record with
  | mk enabled arrival =>
      cases enabled <;> simp [QueueReplay.transition]

/-- A successful decode of another follower cannot overwrite a known assigned
arm.  The runtime unknown-arm test rules out the same follower, and assignment
injectivity rules out a different follower naming that arm. -/
theorem decodeUp_success_separates_assigned_known_arm
    (l result : Ledger p eta heta hcap n hn) (i owner : Fin (p.m - 1))
    (M : UpRecord (codecParams p eta)) (current : CurrentRegister)
    (hknown : l.currentRegisters (l.assignment.arm owner) = some current)
    (hdecode : decodeUp l i (some M) = .success result) :
    owner ≠ i ∧ l.assignment.arm i ≠ l.assignment.arm owner := by
  obtain ⟨_, _, _, _, _, _, _, hunknown, _⟩ :=
    decodeUp_success_candidate l result i M hdecode
  have howner : owner ≠ i := by
    intro heq
    have hknown' : l.currentRegisters (l.assignment.arm i) = some current := by
      rw [heq] at hknown
      exact hknown
    have hfalse : (some current : Option CurrentRegister) = none :=
      hknown'.symm.trans hunknown
    cases hfalse
  constructor
  · exact howner
  · intro harm
    have hi : i = owner := l.assignment.injective harm
    exact howner hi.symm

/-- A successful accepting decode leaves every already-known current queue,
its partial accumulator, and its pre-decode local service unchanged.  The
accepted candidate can update only its own unknown arm. -/
theorem decodeUp_success_preserves_known
    (l result : Ledger p eta heta hcap n hn) (i : Fin (p.m - 1))
    (M : UpRecord (codecParams p eta)) (a : Fin p.K)
    (current : CurrentRegister)
    (hknown : l.currentRegisters a = some current)
    (hdecode : decodeUp l i (some M) = .success result) :
    result.currentRegisters a = some current ∧
    result.increment a = l.increment a ∧
    result.gammaLoc a = l.gammaLoc a ∧
    result.cutoffRegisters a = l.cutoffRegisters a ∧
    result.assignment = l.assignment ∧ result.sigma = l.sigma ∧
    result.cutoff = l.cutoff ∧ result.freezeAt = l.freezeAt := by
  obtain ⟨_, _, _, _, _, _, _, hunknown, hcandidate⟩ :=
    decodeUp_success_candidate l result i M hdecode
  have htarget : l.assignment.arm i ≠ a := by
    by_cases howner : ∃ j, l.assignment.arm j = a
    · obtain ⟨j, hj⟩ := howner
      have hknown' : l.currentRegisters (l.assignment.arm j) = some current := by
        rw [hj]
        exact hknown
      have hseparated := decodeUp_success_separates_assigned_known_arm
        l result i j M current hknown' hdecode
      intro htarget
      exact hseparated.2 (htarget.trans hj.symm)
    · intro htarget
      exact howner ⟨i, htarget⟩
  rw [hcandidate]
  have htarget' : a ≠ l.assignment.arm i := Ne.symm htarget
  simp [acceptUpCandidate, htarget', hknown]

/-- Every rejected branch of the literal decoder returns the phase-only
candidate.  The accepting branch returns either success or invalid, never
rejection. -/
theorem decodeUp_rejected_candidate
    (l result : Ledger p eta heta hcap n hn) (i : Fin (p.m - 1))
    (parsed : Option (UpRecord (codecParams p eta)))
    (hdecode : decodeUp l i parsed = .rejected result) :
    result = { l with phase := .decoded } := by
  by_cases hinput : validLedgerCheck l = true ∧ l.phase = .started ∧
      1 ≤ l.cutoff ∧ l.cutoff ≤ l.cursor ∧ l.cursor ≤ p.T
  · cases parsed with
    | none =>
        let next : Ledger p eta heta hcap n hn := { l with phase := .decoded }
        by_cases hvalid : validLedgerCheck next = true
        · have hEq : Checked.rejected next = Checked.rejected result := by
            simpa [decodeUp, hinput, next, hvalid] using hdecode
          injection hEq with hresult
          exact hresult.symm
        · exact False.elim (by
            simp [decodeUp, hinput, next, hvalid] at hdecode)
    | some M =>
        by_cases haccept : acceptUpCheck l i M = true
        · by_cases hunknown :
              l.currentRegisters (l.assignment.arm i) = none ∧
                l.cutoffRegisters (l.assignment.arm i) = none
          · have hcutPos := hinput.2.2.1
            have hcutCursor := hinput.2.2.2.1
            have hcursorT := hinput.2.2.2.2
            have hprefix : l.cutoff - 1 + (l.cursor - l.cutoff) ≤ p.T := by
              omega
            let prefixIndices := calendarIndices p.T (l.cutoff - 1)
              (l.cursor - l.cutoff) hprefix
            let lastIndex : Fin p.T := ⟨l.cursor - 1, by omega⟩
            cases hpast : replayRecords? l (l.assignment.arm i) prefixIndices with
            | none =>
                simp [decodeUp, hinput, haccept, hunknown, prefixIndices,
                  hpast] at hdecode
            | some past =>
                cases hlast : replayRecords? l (l.assignment.arm i)
                    [lastIndex] with
                | none =>
                    simp [decodeUp, hinput, haccept, hunknown, prefixIndices,
                      lastIndex, hpast, hlast] at hdecode
                | some records =>
                    cases records with
                    | nil =>
                        simp [decodeUp, hinput, haccept, hunknown,
                          prefixIndices, lastIndex, hpast, hlast] at hdecode
                    | cons current tail =>
                        cases tail with
                        | nil =>
                            by_cases hdomain : replayOutputDomainsCheck
                                (p := p) (4 * n) M.val.q (past ++ [current]) = true
                            · by_cases hvalid : validLedgerCheck
                                  (acceptUpCandidate l i M past current) = true
                              · simp [decodeUp, hinput, haccept, hunknown,
                                  prefixIndices, lastIndex, hpast, hlast,
                                  hdomain, hvalid] at hdecode
                              · simp [decodeUp, hinput, haccept, hunknown,
                                  prefixIndices, lastIndex, hpast, hlast,
                                  hdomain, hvalid] at hdecode
                            · simp [decodeUp, hinput, haccept, hunknown,
                                prefixIndices, lastIndex, hpast, hlast,
                                hdomain] at hdecode
                        | cons _ _ =>
                            simp [decodeUp, hinput, haccept, hunknown,
                              prefixIndices, lastIndex, hpast, hlast] at hdecode
          · simp [decodeUp, hinput, haccept, hunknown] at hdecode
        · let next : Ledger p eta heta hcap n hn := { l with phase := .decoded }
          by_cases hvalid : validLedgerCheck next = true
          · have hEq : Checked.rejected next = Checked.rejected result := by
              simpa [decodeUp, hinput, haccept, next, hvalid] using hdecode
            injection hEq with hresult
            exact hresult.symm
          · exact False.elim (by
              simp [decodeUp, hinput, haccept, next, hvalid] at hdecode)
  · exact False.elim (by simp [decodeUp, hinput] at hdecode)

/-- A rejected decode only advances the phase.  It preserves a known queue,
its accumulator, and all comparison data at that arm. -/
theorem decodeUp_rejected_preserves_known
    (l result : Ledger p eta heta hcap n hn) (i : Fin (p.m - 1))
    (parsed : Option (UpRecord (codecParams p eta))) (a : Fin p.K)
    (current : CurrentRegister)
    (hknown : l.currentRegisters a = some current)
    (hdecode : decodeUp l i parsed = .rejected result) :
    result.currentRegisters a = some current ∧
    result.increment a = l.increment a ∧
    result.gammaLoc a = l.gammaLoc a ∧
    result.cutoffRegisters a = l.cutoffRegisters a ∧
    result.assignment = l.assignment ∧ result.sigma = l.sigma ∧
    result.cutoff = l.cutoff ∧ result.freezeAt = l.freezeAt := by
  have hcandidate := decodeUp_rejected_candidate l result i parsed hdecode
  rw [hcandidate]
  simp [hknown]

/-- One actual successful start/decode/finish round applies exactly one
`localQueueRecord` transition to a known queue.  A successful decoder, whether
accepting this arm or another follower, leaves that arm's pre-decode local
service and partial accumulator alone; finish then adds the local service once. -/
theorem checkedRound_known_transition
    (l started decoded finished : Ledger p eta heta hcap n hn)
    (input : RoundInput (p := p) (eta := eta)) (a : Fin p.K)
    (current : CurrentRegister)
    (hknown : l.currentRegisters a = some current)
    (hstart : startRound l (sourceRound input.round) input.enabled input.raw =
      .success started)
    (hdecode : decodeUp started input.selectedFollower input.parsed =
        .success decoded ∨
      decodeUp started input.selectedFollower input.parsed =
        .rejected decoded)
    (hfinish : finishRound decoded = .success finished) :
    let record := localQueueRecord l input.round input.enabled input.raw a
    let next := QueueReplay.transition (4 * n)
      (l.increment a, current.queue) record
    finished.currentRegisters a = some ⟨next.2, next.1 - l.increment a⟩ ∧
    finished.increment a = next.1 ∧
    finished.assignment = l.assignment ∧ finished.sigma = l.sigma ∧
    finished.cutoff = l.cutoff ∧ finished.freezeAt = l.freezeAt ∧
    finished.cutoffRegisters a = l.cutoffRegisters a := by
  let record := localQueueRecord l input.round input.enabled input.raw a
  let next := QueueReplay.transition (4 * n)
    (l.increment a, current.queue) record
  have hstartCandidate := startRound_success_candidate l started
    (sourceRound input.round) input.enabled input.raw hstart
  have hindex :
      (⟨sourceRound input.round - 1, by simp [sourceRound]⟩ : Fin p.T) =
        input.round := by
    apply Fin.ext
    simp [sourceRound]
  have hstartedCurrent : started.currentRegisters a =
      some ⟨(QueueReplay.transition (4 * n) (0, current.queue) record).2,
        (QueueReplay.transition (4 * n) (0, current.queue) record).1⟩ := by
    rw [hstartCandidate, hindex]
    exact startRoundCandidate_known_transition l input.round input.enabled
      input.raw a current hknown
  have hstartedGamma : started.gammaLoc a =
      (QueueReplay.transition (4 * n) (0, current.queue) record).1 := by
    rw [hstartCandidate, hindex]
    simp [startRoundCandidate, record, hknown]
  have hstartedIncrement : started.increment a = l.increment a := by
    rw [hstartCandidate]
    rfl
  have hstartedAssignment : started.assignment = l.assignment := by
    rw [hstartCandidate]
    rfl
  have hstartedSigma : started.sigma = l.sigma := by
    rw [hstartCandidate]
    rfl
  have hstartedCutoff : started.cutoff = l.cutoff := by
    rw [hstartCandidate]
    rfl
  have hstartedFreeze : started.freezeAt = l.freezeAt := by
    rw [hstartCandidate]
    rfl
  have hstartedCutoffRegister : started.cutoffRegisters a = l.cutoffRegisters a := by
    rw [hstartCandidate]
    rfl
  have hdecodedFields :=
    show decoded.currentRegisters a =
        some ⟨(QueueReplay.transition (4 * n) (0, current.queue) record).2,
          (QueueReplay.transition (4 * n) (0, current.queue) record).1⟩ ∧
      decoded.increment a = started.increment a ∧
      decoded.gammaLoc a = started.gammaLoc a ∧
      decoded.cutoffRegisters a = started.cutoffRegisters a ∧
      decoded.assignment = started.assignment ∧ decoded.sigma = started.sigma ∧
      decoded.cutoff = started.cutoff ∧ decoded.freezeAt = started.freezeAt
    from by
      rcases hdecode with hs | hr
      · cases hparsed : input.parsed with
        | none =>
            by_cases hinput : validLedgerCheck started = true ∧
                started.phase = .started ∧ 1 ≤ started.cutoff ∧
                started.cutoff ≤ started.cursor ∧ started.cursor ≤ p.T
            · let next : Ledger p eta heta hcap n hn :=
                { started with phase := .decoded }
              by_cases hvalid : validLedgerCheck next = true
              · simp [hparsed, decodeUp, hinput, next, hvalid] at hs
              · simp [hparsed, decodeUp, hinput, next, hvalid] at hs
            · simp [decodeUp, hinput] at hs
        | some M =>
            have hs' : decodeUp started input.selectedFollower (some M) =
                .success decoded := by simpa [hparsed] using hs
            exact decodeUp_success_preserves_known started decoded
              input.selectedFollower M a
              ⟨(QueueReplay.transition (4 * n) (0, current.queue) record).2,
                (QueueReplay.transition (4 * n) (0, current.queue) record).1⟩
              (by rw [hstartedCurrent]) hs'
      · exact decodeUp_rejected_preserves_known started decoded
          input.selectedFollower input.parsed a
          ⟨(QueueReplay.transition (4 * n) (0, current.queue) record).2,
            (QueueReplay.transition (4 * n) (0, current.queue) record).1⟩
          (by rw [hstartedCurrent]) hr
  have hfinishCandidate := finishRound_success_candidate decoded finished hfinish
  have htransition := queueReplay_transition_add_score (4 * n)
    (l.increment a) current.queue record
  constructor
  · change finished.currentRegisters a = some ⟨next.2, next.1 - l.increment a⟩
    rw [hfinishCandidate]
    simp only [finishRoundCandidate]
    rw [hdecodedFields.1]
    simp [next, htransition]
  constructor
  · change finished.increment a = next.1
    rw [hfinishCandidate]
    simp only [finishRoundCandidate]
    rw [hdecodedFields.2.1, hdecodedFields.2.2.1,
      hstartedIncrement, hstartedGamma]
    simp [next, htransition]
  constructor
  · rw [hfinishCandidate]
    simp only [finishRoundCandidate]
    rw [hdecodedFields.2.2.2.2.1, hstartedAssignment]
  constructor
  · rw [hfinishCandidate]
    simp only [finishRoundCandidate]
    rw [hdecodedFields.2.2.2.2.2.1, hstartedSigma]
  constructor
  · rw [hfinishCandidate]
    simp only [finishRoundCandidate]
    rw [hdecodedFields.2.2.2.2.2.2.1, hstartedCutoff]
  constructor
  · rw [hfinishCandidate]
    simp only [finishRoundCandidate]
    rw [hdecodedFields.2.2.2.2.2.2.2, hstartedFreeze]
  · rw [hfinishCandidate]
    simp only [finishRoundCandidate]
    rw [hdecodedFields.2.2.2.1, hstartedCutoffRegister]

/-- A successful `checkedRounds` run continues an initially known queue
online through exactly the supplied inputs.  Its queue, partial service
accumulator, last transition service, assignment, freeze boundary, and
arm-specific cutoff register are all identified with the literal
`QueueReplay.replay` and `localQueueRecord` list. -/
theorem checkedRounds_known_queue_continuation
    (l final : Ledger p eta heta hcap n hn) (a : Fin p.K)
    (current : CurrentRegister)
    (inputs : List (RoundInput (p := p) (eta := eta)))
    (accepted : List Bool)
    (hknown : l.currentRegisters a = some current)
    (h : checkedRounds l inputs = some (accepted, final)) :
    let records := inputQueueRecords l a inputs
    let replayed := QueueReplay.replay (4 * n)
      (l.increment a, current.queue) records
    final.currentRegisters a = some ⟨replayed.2,
      replayLastService (4 * n) (l.increment a, current.queue)
        current.lastService records⟩ ∧
    final.increment a = replayed.1 ∧
    final.assignment = l.assignment ∧ final.sigma = l.sigma ∧
    final.cutoff = l.cutoff ∧ final.freezeAt = l.freezeAt ∧
    final.cutoffRegisters a = l.cutoffRegisters a := by
  induction inputs generalizing l current accepted final with
  | nil =>
      simp only [checkedRounds] at h
      rcases h with ⟨rfl, rfl⟩
      cases current with
      | mk queue lastService =>
          simp [inputQueueRecords, replayLastService, QueueReplay.replay, hknown]
  | cons input rest ih =>
      cases hs : startRound l (sourceRound input.round) input.enabled input.raw with
      | invalid => simp [checkedRounds, hs] at h
      | rejected bad => simp [checkedRounds, hs] at h
      | success started =>
          cases hd : decodeUp started input.selectedFollower input.parsed with
          | invalid => simp [checkedRounds, hs, hd] at h
          | success decoded =>
              cases hf : finishRound decoded with
              | invalid => simp [checkedRounds, hs, hd, hf] at h
              | rejected bad => simp [checkedRounds, hs, hd, hf] at h
              | success finished =>
                  cases hr : checkedRounds finished rest with
                  | none => simp [checkedRounds, hs, hd, hf, hr] at h
                  | some pair =>
                      cases pair with
                      | mk acceptedRest finalRest =>
                          simp [checkedRounds, hs, hd, hf, hr] at h
                          rcases h with ⟨rfl, rfl⟩
                          have hstep := checkedRound_known_transition l started
                            decoded finished input a current hknown hs
                            (Or.inl hd) hf
                          rcases hstep with
                            ⟨hcurrent, hincrement, hassignment, hsigma,
                              hcutoff, hfreeze, hcutoffRegister⟩
                          let record := localQueueRecord l input.round
                            input.enabled input.raw a
                          let nextReplay := QueueReplay.transition (4 * n)
                            (l.increment a, current.queue) record
                          let next : CurrentRegister :=
                            ⟨nextReplay.2, nextReplay.1 - l.increment a⟩
                          have hnext : finished.currentRegisters a = some next := by
                            simpa [nextReplay, next, record] using hcurrent
                          have htail := ih finished finalRest next acceptedRest hnext hr
                          have htailRecords :
                              inputQueueRecords l a rest =
                                inputQueueRecords finished a rest :=
                            inputQueueRecords_freezeAt_eq l finished a rest
                              hfreeze.symm
                          have hrecordsHead :
                              inputQueueRecords l a (input :: rest) =
                                record :: inputQueueRecords finished a rest := by
                            change localQueueRecord l input.round input.enabled
                              input.raw a :: inputQueueRecords l a rest =
                                record :: inputQueueRecords finished a rest
                            rw [htailRecords]
                          have hwholeReplay :
                              QueueReplay.replay (4 * n)
                                  (l.increment a, current.queue)
                                  (inputQueueRecords l a (input :: rest)) =
                                QueueReplay.replay (4 * n)
                                  (finished.increment a, next.queue)
                                  (inputQueueRecords finished a rest) := by
                            rw [hrecordsHead]
                            change QueueReplay.replay (4 * n)
                                (l.increment a, current.queue)
                                ([record] ++ inputQueueRecords finished a rest) = _
                            rw [QueueReplay.replay_append]
                            simp only [QueueReplay.replay]
                            have hpair : (finished.increment a, next.queue) =
                                QueueReplay.transition (4 * n)
                                  (l.increment a, current.queue) record := by
                              exact Prod.ext hincrement rfl
                            rw [hpair]
                            rfl
                          have hwholeLastService :
                              replayLastService (4 * n)
                                  (l.increment a, current.queue) current.lastService
                                  (inputQueueRecords l a (input :: rest)) =
                                replayLastService (4 * n)
                                  (finished.increment a, next.queue)
                                  next.lastService
                                  (inputQueueRecords finished a rest) := by
                            rw [hrecordsHead]
                            conv_lhs => rw [replayLastService_cons]
                            have hpair : (finished.increment a, next.queue) =
                                QueueReplay.transition (4 * n)
                                  (l.increment a, current.queue) record := by
                              exact Prod.ext hincrement rfl
                            rw [hpair]
                            cases hrecords : inputQueueRecords finished a rest with
                            | nil =>
                                simp [replayLastService, next, nextReplay]
                            | cons head tail =>
                                simp [next, nextReplay]
                          have htailQueue :
                              finalRest.currentRegisters a = some ⟨
                                (QueueReplay.replay (4 * n)
                                  (finished.increment a, next.queue)
                                  (inputQueueRecords finished a rest)).2,
                                replayLastService (4 * n)
                                  (finished.increment a, next.queue)
                                  next.lastService
                                  (inputQueueRecords finished a rest)⟩ := htail.1
                          have htailAccumulator : finalRest.increment a =
                              (QueueReplay.replay (4 * n)
                                (finished.increment a, next.queue)
                                (inputQueueRecords finished a rest)).1 := htail.2.1
                          have hfinalCurrent : finalRest.currentRegisters a =
                              some ⟨
                                (QueueReplay.replay (4 * n)
                                  (l.increment a, current.queue)
                                  (inputQueueRecords l a (input :: rest))).2,
                                replayLastService (4 * n)
                                  (l.increment a, current.queue) current.lastService
                                  (inputQueueRecords l a (input :: rest))⟩ := by
                            rw [hwholeReplay, hwholeLastService]
                            exact htailQueue
                          have hfinalAccumulator : finalRest.increment a =
                              (QueueReplay.replay (4 * n)
                                (l.increment a, current.queue)
                                (inputQueueRecords l a (input :: rest))).1 := by
                            rw [hwholeReplay]
                            exact htailAccumulator
                          exact ⟨hfinalCurrent, hfinalAccumulator,
                            htail.2.2.1.trans hassignment,
                            htail.2.2.2.1.trans hsigma,
                            htail.2.2.2.2.1.trans hcutoff,
                            htail.2.2.2.2.2.1.trans hfreeze,
                            htail.2.2.2.2.2.2.trans hcutoffRegister⟩
          | rejected decoded =>
              cases hf : finishRound decoded with
              | invalid => simp [checkedRounds, hs, hd, hf] at h
              | rejected bad => simp [checkedRounds, hs, hd, hf] at h
              | success finished =>
                  cases hr : checkedRounds finished rest with
                  | none => simp [checkedRounds, hs, hd, hf, hr] at h
                  | some pair =>
                      cases pair with
                      | mk acceptedRest finalRest =>
                          simp [checkedRounds, hs, hd, hf, hr] at h
                          rcases h with ⟨rfl, rfl⟩
                          have hstep := checkedRound_known_transition l started
                            decoded finished input a current hknown hs
                            (Or.inr hd) hf
                          rcases hstep with
                            ⟨hcurrent, hincrement, hassignment, hsigma,
                              hcutoff, hfreeze, hcutoffRegister⟩
                          let record := localQueueRecord l input.round
                            input.enabled input.raw a
                          let nextReplay := QueueReplay.transition (4 * n)
                            (l.increment a, current.queue) record
                          let next : CurrentRegister :=
                            ⟨nextReplay.2, nextReplay.1 - l.increment a⟩
                          have hnext : finished.currentRegisters a = some next := by
                            simpa [nextReplay, next, record] using hcurrent
                          have htail := ih finished finalRest next acceptedRest hnext hr
                          have htailRecords :
                              inputQueueRecords l a rest =
                                inputQueueRecords finished a rest :=
                            inputQueueRecords_freezeAt_eq l finished a rest
                              hfreeze.symm
                          have hrecordsHead :
                              inputQueueRecords l a (input :: rest) =
                                record :: inputQueueRecords finished a rest := by
                            change localQueueRecord l input.round input.enabled
                              input.raw a :: inputQueueRecords l a rest =
                                record :: inputQueueRecords finished a rest
                            rw [htailRecords]
                          have hwholeReplay :
                              QueueReplay.replay (4 * n)
                                  (l.increment a, current.queue)
                                  (inputQueueRecords l a (input :: rest)) =
                                QueueReplay.replay (4 * n)
                                  (finished.increment a, next.queue)
                                  (inputQueueRecords finished a rest) := by
                            rw [hrecordsHead]
                            change QueueReplay.replay (4 * n)
                                (l.increment a, current.queue)
                                ([record] ++ inputQueueRecords finished a rest) = _
                            rw [QueueReplay.replay_append]
                            simp only [QueueReplay.replay]
                            have hpair : (finished.increment a, next.queue) =
                                QueueReplay.transition (4 * n)
                                  (l.increment a, current.queue) record := by
                              exact Prod.ext hincrement rfl
                            rw [hpair]
                            rfl
                          have hwholeLastService :
                              replayLastService (4 * n)
                                  (l.increment a, current.queue) current.lastService
                                  (inputQueueRecords l a (input :: rest)) =
                                replayLastService (4 * n)
                                  (finished.increment a, next.queue)
                                  next.lastService
                                  (inputQueueRecords finished a rest) := by
                            rw [hrecordsHead]
                            conv_lhs => rw [replayLastService_cons]
                            have hpair : (finished.increment a, next.queue) =
                                QueueReplay.transition (4 * n)
                                  (l.increment a, current.queue) record := by
                              exact Prod.ext hincrement rfl
                            rw [hpair]
                            cases hrecords : inputQueueRecords finished a rest with
                            | nil =>
                                simp [replayLastService, next, nextReplay]
                            | cons head tail =>
                                simp [next, nextReplay]
                          have htailQueue :
                              finalRest.currentRegisters a = some ⟨
                                (QueueReplay.replay (4 * n)
                                  (finished.increment a, next.queue)
                                  (inputQueueRecords finished a rest)).2,
                                replayLastService (4 * n)
                                  (finished.increment a, next.queue)
                                  next.lastService
                                  (inputQueueRecords finished a rest)⟩ := htail.1
                          have htailAccumulator : finalRest.increment a =
                              (QueueReplay.replay (4 * n)
                                (finished.increment a, next.queue)
                                (inputQueueRecords finished a rest)).1 := htail.2.1
                          have hfinalCurrent : finalRest.currentRegisters a =
                              some ⟨
                                (QueueReplay.replay (4 * n)
                                  (l.increment a, current.queue)
                                  (inputQueueRecords l a (input :: rest))).2,
                                replayLastService (4 * n)
                                  (l.increment a, current.queue) current.lastService
                                  (inputQueueRecords l a (input :: rest))⟩ := by
                            rw [hwholeReplay, hwholeLastService]
                            exact htailQueue
                          have hfinalAccumulator : finalRest.increment a =
                              (QueueReplay.replay (4 * n)
                                (l.increment a, current.queue)
                                (inputQueueRecords l a (input :: rest))).1 := by
                            rw [hwholeReplay]
                            exact htailAccumulator
                          exact ⟨hfinalCurrent, hfinalAccumulator,
                            htail.2.2.1.trans hassignment,
                            htail.2.2.2.1.trans hsigma,
                            htail.2.2.2.2.1.trans hcutoff,
                            htail.2.2.2.2.2.1.trans hfreeze,
                            htail.2.2.2.2.2.2.trans hcutoffRegister⟩

/-- Compose the actual accepted-UP replay prefix/current record with a
successful checked suffix.  The endpoint is one `QueueReplay.replay` of the
decoder's own `past ++ [current]` records followed by the suffix inputs mapped
through the same freeze boundary.  The decoder records remain exactly its
`replayRecords?` outputs; no equality to an earlier raw-input list is asserted.
-/
theorem checked_acceptance_then_checked_suffix_one_replay
    (l started decoded finished final : Ledger p eta heta hcap n hn)
    (t : ℕ) (enabled : Bool) (raw : Option (Fin p.K × ℕ))
    (i : Fin (p.m - 1)) (M : UpRecord (codecParams p eta))
    (suffix : List (RoundInput (p := p) (eta := eta)))
    (suffixAccepted : List Bool)
    (hstart : startRound l t enabled raw = .success started)
    (hdecode : decodeUp started i (some M) = .success decoded)
    (hfinish : finishRound decoded = .success finished)
    (hsuffix : checkedRounds finished suffix = some (suffixAccepted, final)) :
    ∃ hbound : started.cutoff - 1 + (started.cursor - started.cutoff) ≤ p.T,
    ∃ lastIndex : Fin p.T, sourceRound lastIndex = t ∧
    ∃ past current,
      replayRecords? started (started.assignment.arm i)
          (calendarIndices p.T (started.cutoff - 1)
            (started.cursor - started.cutoff) hbound) = some past ∧
      replayRecords? started (started.assignment.arm i) [lastIndex] =
        some [current] ∧
      started.currentRegisters (started.assignment.arm i) = none ∧
      let arm := started.assignment.arm i
      let acceptanceRecords := past ++ [current]
      let prefixReplay := QueueReplay.replay (4 * n) (0, M.val.q)
        acceptanceRecords
      let suffixRecords := inputQueueRecords started arm suffix
      final.currentRegisters arm = some ⟨
        (QueueReplay.replay (4 * n) (0, M.val.q)
          (acceptanceRecords ++ suffixRecords)).2,
        replayLastService (4 * n) prefixReplay
          (prefixReplay.1 -
            (QueueReplay.replay (4 * n) (0, M.val.q) past).1)
          suffixRecords⟩ ∧
      final.increment arm =
        (QueueReplay.replay (4 * n) (0, M.val.q)
          (acceptanceRecords ++ suffixRecords)).1 ∧
      final.cutoffRegisters arm =
        some ⟨started.baseScore i + M.val.S, M.val.q, M.val.delta⟩ ∧
      final.assignment = started.assignment ∧ final.freezeAt = started.freezeAt := by
  obtain ⟨hbound, lastIndex, hlastSource, past, current, hpast, hlast,
      hunknown, hfinishedCurrent, hfinishedIncrement, hfinishedCutoff⟩ :=
    checked_acceptance_finish_once l started decoded finished t enabled raw i M
      hstart hdecode hfinish
  let arm := started.assignment.arm i
  let acceptanceRecords := past ++ [current]
  let prefixReplay := QueueReplay.replay (4 * n) (0, M.val.q)
    acceptanceRecords
  let acceptedLast := prefixReplay.1 -
    (QueueReplay.replay (4 * n) (0, M.val.q) past).1
  let currentRegister : CurrentRegister := ⟨prefixReplay.2, acceptedLast⟩
  have hknown : finished.currentRegisters arm = some currentRegister := by
    simpa [arm, prefixReplay, acceptedLast, currentRegister] using
      hfinishedCurrent
  have hdecodeCandidate := decodeUp_success_candidate started decoded i M hdecode
  obtain ⟨_, _, _, _, _, _, _, _, hdecodedCandidate⟩ := hdecodeCandidate
  have hfinishCandidate := finishRound_success_candidate decoded finished hfinish
  have hfinishedAssignment : finished.assignment = started.assignment := by
    rw [hfinishCandidate, hdecodedCandidate]
    rfl
  have hfinishedFreeze : finished.freezeAt = started.freezeAt := by
    rw [hfinishCandidate, hdecodedCandidate]
    rfl
  have hrecords : inputQueueRecords finished arm suffix =
      inputQueueRecords started arm suffix :=
    inputQueueRecords_freezeAt_eq finished started arm suffix hfinishedFreeze
  have hcontinuation := checkedRounds_known_queue_continuation finished final arm
    currentRegister suffix suffixAccepted hknown hsuffix
  rw [hrecords] at hcontinuation
  let suffixRecords := inputQueueRecords started arm suffix
  have hprefixState : (finished.increment arm, currentRegister.queue) =
      prefixReplay := by
    exact Prod.ext (by simpa [arm, prefixReplay] using hfinishedIncrement) rfl
  have hwholeReplay :
      QueueReplay.replay (4 * n) (0, M.val.q)
          (acceptanceRecords ++ suffixRecords) =
        QueueReplay.replay (4 * n)
          (finished.increment arm, currentRegister.queue) suffixRecords := by
    rw [QueueReplay.replay_append, hprefixState]
  have hfinalCurrent : final.currentRegisters arm = some ⟨
      (QueueReplay.replay (4 * n) (0, M.val.q)
        (acceptanceRecords ++ suffixRecords)).2,
      replayLastService (4 * n) prefixReplay acceptedLast suffixRecords⟩ := by
    rw [hcontinuation.1, hwholeReplay]
    simp [suffixRecords, currentRegister, acceptedLast, hprefixState]
  have hfinalIncrement : final.increment arm =
      (QueueReplay.replay (4 * n) (0, M.val.q)
        (acceptanceRecords ++ suffixRecords)).1 := by
    rw [hwholeReplay]
    exact hcontinuation.2.1
  have hfinalCutoff : final.cutoffRegisters arm =
      some ⟨started.baseScore i + M.val.S, M.val.q, M.val.delta⟩ := by
    rw [hcontinuation.2.2.2.2.2.2, hfinishedCutoff]
  have hfinalAssignment : final.assignment = started.assignment := by
    rw [hcontinuation.2.2.1, hfinishedAssignment]
  have hfinalFreeze : final.freezeAt = started.freezeAt := by
    rw [hcontinuation.2.2.2.2.2.1, hfinishedFreeze]
  exact ⟨hbound, lastIndex, hlastSource, past, current, hpast, hlast,
    hunknown, by simpa [arm, acceptanceRecords, prefixReplay, suffixRecords,
      acceptedLast] using hfinalCurrent,
    hfinalIncrement, hfinalCutoff, hfinalAssignment, hfinalFreeze⟩

end Bandits.Support.CollectionKnownQueueContinuation

end
