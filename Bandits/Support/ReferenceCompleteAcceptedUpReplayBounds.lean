/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteAcceptedUpBaseCredit

import Lean.Elab.Tactic.Omega

/-!
# Numerical bounds for an actual accepted UP replay prefix

Sources: `sources/zip4/manuscript/06_interruptions.tex:164-177,246-299,303-348`
and `sources/zip4/manuscript/appendix_a_local_protocol.tex:8-64`.

The event premise is the actual filtered receiver-success branch on one record
of the original physical suffix. It does not assert that other physical
branches succeed or that arbitrary accepted words were sent. This result keeps
the accepted message's retained installation base and bounds the decoder's
actual replay prefixes; it makes no ordinary-history, score-truth, queue-truth,
or FINISH-success claim.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceCompleteAcceptedUpReplayBounds

open ConstructorDimensions
open ReferenceActivePhysicalStep
open ReferenceActivePhysicalHorizon
open CoordinatorCollectionLedger
open ReferenceCollectionPhaseHistory
open ReferenceCollectionSegmentExtraction
open CollectionKnownQueueContinuation

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

private theorem replay_records_length
    (l : Ledger rate) (a : Fin p.K) (indices : List (Fin p.T))
    (records : List (Bool × ℕ))
    (hcall : replayRecords? l a indices = some records) :
    records.length = indices.length := by
  induction indices generalizing records with
  | nil =>
      have heq : [] = records := Option.some.inj hcall
      subst records
      rfl
  | cons index indices ih =>
      cases he : l.enabledHistory index with
      | none => simp [replayRecords?, he] at hcall
      | some enabled =>
          cases ht : replayRecords? l a indices with
          | none => simp [replayRecords?, he, ht] at hcall
          | some tail =>
              simp [replayRecords?, he, ht] at hcall
              subst records
              simp only [List.length_cons, ih tail ht]

/-- Reconstruct the decoder's checked replay list and its pointwise arrival
caps from the literal success branch. The lists are the actual two
`replayRecords?` results used by `decodeUp`, not an arbitrary queue trace. -/
private theorem decode_replay_caps
    (l result : Ledger rate) (i : Fin (p.m - 1))
    (M : OrdinaryMessageCodec.UpRecord (codecParams p rate.eta.val))
    (hdecode : decodeUp l i (some M) = .success result) :
    1 ≤ l.cutoff ∧ l.cutoff ≤ l.cursor ∧
      l.currentRegisters (l.assignment.arm i) = none ∧
      l.cutoffRegisters (l.assignment.arm i) = none ∧
      ∃ hbound : l.cutoff - 1 + (l.cursor - l.cutoff) ≤ p.T,
      ∃ lastIndex : Fin p.T, sourceRound lastIndex = l.cursor ∧
      ∃ past current,
        replayRecords? l (l.assignment.arm i)
          (calendarIndices p.T (l.cutoff - 1) (l.cursor - l.cutoff) hbound) =
            some past ∧
        replayRecords? l (l.assignment.arm i) [lastIndex] = some [current] ∧
        replayOutputDomainsCheck (p := p) (4 * rate.n) M.val.q
          (past ++ [current]) = true ∧
        (∀ record ∈ past ++ [current], record.2 ≤ D p) := by
  by_cases hinput : validLedgerCheck l = true ∧ l.phase = .started ∧
      1 ≤ l.cutoff ∧ l.cutoff ≤ l.cursor ∧ l.cursor ≤ p.T
  · by_cases haccept : acceptUpCheck l i M = true
    · by_cases hunknown : l.currentRegisters (l.assignment.arm i) = none ∧
          l.cutoffRegisters (l.assignment.arm i) = none
      · have hcutPos := hinput.2.2.1
        have hcutCursor := hinput.2.2.2.1
        have hcursorT := hinput.2.2.2.2
        have hprefix : l.cutoff - 1 + (l.cursor - l.cutoff) ≤ p.T := by omega
        let indices := calendarIndices p.T (l.cutoff - 1)
          (l.cursor - l.cutoff) hprefix
        let lastIndex : Fin p.T := ⟨l.cursor - 1, by omega⟩
        cases hpast : replayRecords? l (l.assignment.arm i) indices with
        | none =>
            exfalso
            simp [decodeUp, hinput, haccept, hunknown, indices,
              hpast] at hdecode
        | some past =>
            cases hlast : replayRecords? l (l.assignment.arm i) [lastIndex] with
            | none =>
                exfalso
                simp [decodeUp, hinput, haccept, hunknown, indices,
                  lastIndex, hpast, hlast] at hdecode
            | some records =>
                cases records with
                | nil =>
                    exfalso
                    simp [decodeUp, hinput, haccept, hunknown, indices,
                      lastIndex, hpast, hlast] at hdecode
                | cons current rest =>
                    cases rest with
                    | nil =>
                        by_cases hdomain : replayOutputDomainsCheck (p := p)
                            (4 * rate.n) M.val.q (past ++ [current]) = true
                        · have hcap : (past ++ [current]).all
                              (fun record => decide (record.2 ≤ D p)) = true := by
                            have hc := hdomain
                            simp only [replayOutputDomainsCheck,
                              Bool.and_eq_true] at hc
                            exact hc.1.2
                          refine ⟨hcutPos, hcutCursor, hunknown.1, hunknown.2,
                            hprefix, lastIndex, ?_, past, current, ?_, ?_,
                            hdomain, ?_⟩
                          · dsimp only [sourceRound, lastIndex]
                            omega
                          · simpa only [indices]
                          · simpa only [lastIndex]
                          · intro record hrecord
                            exact of_decide_eq_true
                              ((List.all_eq_true.mp hcap) record hrecord)
                        · exfalso
                          simp [decodeUp, hinput, haccept, hunknown, indices,
                            lastIndex, hpast, hlast, hdomain] at hdecode
                    | cons _ _ =>
                        exfalso
                        simp [decodeUp, hinput, haccept, hunknown, indices,
                          lastIndex, hpast, hlast] at hdecode
      · exfalso
        simp [decodeUp, hinput, haccept, hunknown] at hdecode
    · let next : Ledger rate := { l with phase := .decoded }
      by_cases hvalid : validLedgerCheck next = true
      · exfalso
        simp [decodeUp, hinput, haccept, next, hvalid] at hdecode
      · exfalso
        simp [decodeUp, hinput, haccept, next, hvalid] at hdecode
  · exfalso
    simp [decodeUp, hinput] at hdecode

private theorem accepted_total_le
    (records : List (Bool × ℕ)) (bound : ℕ)
    (hcap : ∀ record ∈ records, record.2 ≤ bound) :
    RecordedQueueRun.acceptedTotal records ≤ records.length * bound := by
  induction records with
  | nil => exact Nat.zero_le _
  | cons head tail ih =>
      have hh : RecordedQueueRun.acceptedArrival head ≤ bound := by
        unfold RecordedQueueRun.acceptedArrival
        split
        · exact hcap head List.mem_cons_self
        · exact Nat.zero_le _
      have ht : RecordedQueueRun.acceptedTotal tail ≤ tail.length * bound :=
        ih (fun record hmem => hcap record (List.mem_cons_of_mem _ hmem))
      change RecordedQueueRun.acceptedArrival head +
        RecordedQueueRun.acceptedTotal tail ≤ (tail.length + 1) * bound
      calc
        _ ≤ bound + tail.length * bound := Nat.add_le_add hh ht
        _ = (tail.length + 1) * bound := by
          rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]

private theorem replay_last_service_le
    (capacity : ℕ) (initial : ℕ × ℕ) (retained : ℕ)
    (records : List (Bool × ℕ)) (hne : records ≠ []) :
    replayLastService capacity initial retained records ≤ capacity := by
  induction records generalizing initial retained with
  | nil => contradiction
  | cons record rest ih =>
      cases rest with
      | nil =>
          cases henabled : record.1
          · simp [replayLastService, QueueReplay.replay, henabled,
              QueueReplay.transition]
          · simp [replayLastService, QueueReplay.replay, henabled,
              QueueReplay.transition]
      | cons next tail =>
          rw [replayLastService_cons]
          exact ih _ _ (by simp)

private theorem replay_final_increment_le
    (capacity : ℕ) (initialQueue : ℕ)
    (past : List (Bool × ℕ)) (current : Bool × ℕ) :
    (QueueReplay.replay capacity (0, initialQueue) (past ++ [current])).1 -
      (QueueReplay.replay capacity (0, initialQueue) past).1 ≤ capacity := by
  rw [QueueReplay.replay_append]
  change (QueueReplay.transition capacity
      (QueueReplay.replay capacity (0, initialQueue) past) current).1 -
      (QueueReplay.replay capacity (0, initialQueue) past).1 ≤ capacity
  rw [RecordedQueueRun.transition_score_eq_add_recordService, Nat.add_sub_cancel_left]
  unfold RecordedQueueRun.recordService
  cases hcurrent : current.1
  · simp
  · exact CappedService.service_le_capacity _ _ _

private theorem accepted_up_choice_tail
    (x : RoundInput p rate) (c : Choice rate)
    (hchoice : choice x = some c) :
    executedTail x = some ⟨c.payload, c.preLedger, c.started, c.weights⟩ := by
  unfold choice at hchoice
  split at hchoice
  · contradiction
  next hselected =>
    unfold executedTail
    dsimp only
    split
    · contradiction
    next _ =>
      cases hc : (prepare x).coordinator with
      | first outcome =>
          cases outcome <;>
            simp only [hc, choiceOfCut] at hchoice <;> contradiction
      | live registers owned base outcome =>
          cases outcome <;>
            simp only [hc, choiceOfCut] at hchoice
          all_goals first | contradiction | (cases Option.some.inj hchoice; rfl)
      | collection payload ledger clock cutoff outcome =>
          cases outcome <;>
            simp only [hc, choiceOfCut] at hchoice
          all_goals first | contradiction | (cases Option.some.inj hchoice; rfl)
      | invalidCollectionCutoff =>
          simp only [hc, choiceOfCut] at hchoice
          contradiction
      | dagger =>
          simp only [hc, choiceOfCut] at hchoice
          contradiction

/-- The actual accepted UP's same-installation base credit controls every
prefix of the exact replay list computed by that event's executed decoder. -/
theorem complete_accepted_up_replay_prefix_credit
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (c : Choice rate)
    (hchoice : choice
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val]'k.isLt).input = some c)
    (i : Fin (p.m - 1)) (U : UpRecord p rate)
    (haccepted : AcceptedUp
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val]'k.isLt).input i U) :
    let R : List (ReferenceCompletePhysicalHistory.RoundRecord p rate) :=
      ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
    ∃ (b j : Fin R.length) (F : ReferencePrelaunchFollower.State p rate.eta)
      (mu : ActiveFollowerLifecycle.LocalMemory p),
      b.val ≤ j.val ∧ j.val < k.val ∧
      ReferenceAssignmentPayloadPersistence.InstallationBirth R[b.val] c.payload ∧
      ReferenceAssignmentCollectionMassSteps.installedBaseScore R[b.val] =
        some c.preLedger.baseScore ∧
      ReferenceAcceptedUpFollowerHistory.RetainedDown R[j.val] i
        (c.payload.downRecord i) ∧
      R[k.val].input.state.followers i = .ordinary F mu ∧
      F.lastDown = some (c.payload.downRecord i) ∧
      U.val.sigma = c.preLedger.sigma ∧
      c.preLedger.sigma = c.payload.sigma.val + 1 ∧
      U.val.S = F.S ∧ U.val.delta = F.delta ∧ U.val.q = F.backlog ∧
      c.preLedger.baseScore i + F.S + F.backlog ≤
        min R[k.val].input.time.val (c.preLedger.cutoff - 1) * D p ∧
      F.delta ≤ D p ∧
      c.preLedger.baseScore i + U.val.S + U.val.q ≤
        (c.preLedger.cutoff - 1) * D p ∧
      U.val.delta ≤ D p ∧
      ∃ (tail : Tail R[k.val].input) (recording : CoordinatorRecordingOperation.Output p)
        (started decoded : Ledger rate) (bank : CoordinatorUpReception.UpDecoderBank p),
        executedTail R[k.val].input = some tail ∧
        tail = ⟨c.payload, c.preLedger, c.started, c.weights⟩ ∧
        CoordinatorRecorderComplementBridge.run
          (collectionRecordingInput (prepare R[k.val].input) c.payload c.started c.weights) =
            some recording ∧
        startRound c.preLedger (R[k.val].input.time.val + 1)
          (ReferenceActivePhysicalStep.collectionEnabled c.preLedger R[k.val].input.time)
          (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) =
            .success started ∧
        started.assignment = c.preLedger.assignment ∧
        started.baseScore = c.preLedger.baseScore ∧
        (ReferenceActivePhysicalStep.receiveUp
          (ReferenceActivePhysicalStep.prepare R[k.val].input) started).result =
            .success (decoded, bank) ∧
        filteredParsed R[k.val].input started = some U ∧
        effectiveParse R[k.val].input started = some U ∧
        decodeUp started i (some U) = .success decoded ∧
        ∃ hbound : started.cutoff - 1 +
            (started.cursor - started.cutoff) ≤ p.T,
          started.cutoff = c.preLedger.cutoff ∧
          started.cursor = R[k.val].input.time.val + 1 ∧
          1 ≤ c.preLedger.cutoff ∧
          c.preLedger.cutoff ≤ R[k.val].input.time.val + 1 ∧
          R[k.val].input.time.val + 1 ≤ p.T ∧
          ∃ lastIndex : Fin p.T,
            lastIndex = R[k.val].input.time ∧
            ∃ (past : List (Bool × ℕ)) (current : Bool × ℕ),
              replayRecords? started (started.assignment.arm i)
                (calendarIndices p.T (started.cutoff - 1)
                  (started.cursor - started.cutoff) hbound) = some past ∧
              replayRecords? started (started.assignment.arm i) [lastIndex] =
                some [current] ∧
              (∀ record ∈ past ++ [current], record.2 ≤ D p) ∧
              (past ++ [current]).length =
                R[k.val].input.time.val + 1 - c.preLedger.cutoff + 1 ∧
              QueueReplay.replay (4 * rate.n) (0, U.val.q) [] = (0, U.val.q) ∧
              replayLastService (4 * rate.n) (0, U.val.q) U.val.delta [] =
                U.val.delta ∧
              (c.preLedger.baseScore i + U.val.S ≤ p.T * D p) ∧
              U.val.q ≤ p.T * D p ∧ U.val.delta ≤ D p ∧
              (∀ h : ℕ, h ≤ (past ++ [current]).length →
                let P := QueueReplay.replay (4 * rate.n) (0, U.val.q)
                  ((past ++ [current]).take h)
                c.preLedger.baseScore i + U.val.S + P.1 + P.2 ≤
                    (c.preLedger.cutoff - 1 + h) * D p ∧
                (c.preLedger.cutoff - 1 + h) * D p ≤ p.T * D p ∧
                P.1 ≤ p.T * D p ∧ P.2 ≤ p.T * D p ∧
                c.preLedger.baseScore i + U.val.S + P.1 ≤ p.T * D p ∧
                replayLastService (4 * rate.n) (0, U.val.q) U.val.delta
                  ((past ++ [current]).take h) ≤ D p) ∧
              decoded.currentRegisters (started.assignment.arm i) =
                some ⟨(QueueReplay.replay (4 * rate.n) (0, U.val.q)
                    (past ++ [current])).2,
                  (QueueReplay.replay (4 * rate.n) (0, U.val.q)
                      (past ++ [current])).1 -
                    (QueueReplay.replay (4 * rate.n) (0, U.val.q) past).1⟩ ∧
              decoded.increment (started.assignment.arm i) =
                (QueueReplay.replay (4 * rate.n) (0, U.val.q)
                  (past ++ [current])).1 ∧
              decoded.cutoffRegisters (started.assignment.arm i) =
                some ⟨c.preLedger.baseScore i + U.val.S, U.val.q, U.val.delta⟩ ∧
              decoded.pending = started.pending.erase i ∧
              started.currentRegisters (started.assignment.arm i) = none ∧
              started.cutoffRegisters (started.assignment.arm i) = none ∧
              started.gammaLoc (started.assignment.arm i) = 0 ∧
              c.preLedger.baseScore i + U.val.S +
                  decoded.increment (started.assignment.arm i) +
                  (QueueReplay.replay (4 * rate.n) (0, U.val.q)
                    (past ++ [current])).2 ≤
                started.cursor * D p ∧
              (c.preLedger.baseScore i + U.val.S) + U.val.q ≤
                (c.preLedger.cutoff - 1) * D p ∧
              (QueueReplay.replay (4 * rate.n) (0, U.val.q)
                (past ++ [current])).1 -
                  (QueueReplay.replay (4 * rate.n) (0, U.val.q) past).1 ≤ D p := by
  let R : List (ReferenceCompletePhysicalHistory.RoundRecord p rate) :=
    ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
  let record := R[k.val]'k.isLt
  let x := record.input
  obtain ⟨b, j, F, mu, hb, hj, hbirth, hbase, hretained, hinput,
      hlast, hUsigma, hledgerSigma, hUS, hUdelta, hUq, hmass,
      hdelta, hreply, hmessageDelta⟩ :=
    ReferenceCompleteAcceptedUpBaseCredit.complete_accepted_up_base_credit
      rewards C_star C_h source k c hchoice i U haccepted
  rcases haccepted with
    ⟨tail, recording, started, decoded, bank, htail, hrecording, hstart,
      hreceive, hparsed, hi⟩
  have htailChoice : executedTail x =
      some ⟨c.payload, c.preLedger, c.started, c.weights⟩ :=
    accepted_up_choice_tail x c hchoice
  have htailEq : tail = ⟨c.payload, c.preLedger, c.started, c.weights⟩ :=
    Option.some.inj (htail.symm.trans htailChoice)
  subst tail
  have hparse : effectiveParse x started = some U := by
    simpa only [filteredParsed, effectiveParse] using hparsed
  have hdecodeSender := receiveUp_decode_result x started
  rw [hreceive] at hdecodeSender
  have hdecode : decodeUp started i (some U) = .success decoded := by
    rw [hparse, ← hi] at hdecodeSender
    exact hdecodeSender
  obtain ⟨hcutPos, hcutCursor, hunknownStart, hunknownCutoff,
      hbound, lastIndex, hlastSource,
      past, current, hpast, hcurrent, hguard, hrecordCaps⟩ :=
    decode_replay_caps started decoded i U hdecode
  have hstartCursor := CollectionCheckedExecution.startRound_success_cursor
    c.preLedger started (x.time.val + 1)
    (ReferenceActivePhysicalStep.collectionEnabled c.preLedger x.time)
    (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) hstart
  have hlastIndex : lastIndex = x.time := by
    apply Fin.ext
    have heq := hlastSource.trans hstartCursor
    change lastIndex.val + 1 = x.time.val + 1 at heq
    omega
  have hstartCandidate := CollectionCheckedExecution.startRound_success_candidate
    c.preLedger started (x.time.val + 1)
    (ReferenceActivePhysicalStep.collectionEnabled c.preLedger x.time)
    (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) hstart
  have hstartedCutoff : started.cutoff = c.preLedger.cutoff := by
    rw [hstartCandidate]
    rfl
  have hstartedAssignment : started.assignment = c.preLedger.assignment := by
    rw [hstartCandidate]
    rfl
  have hstartedBase : started.baseScore = c.preLedger.baseScore := by
    rw [hstartCandidate]
    rfl
  have hpastLength : past.length = started.cursor - started.cutoff := by
    rw [replay_records_length started (started.assignment.arm i) _ past hpast,
      calendarIndices_length]
  have hrecordsLength : (past ++ [current]).length =
      x.time.val + 1 - c.preLedger.cutoff + 1 := by
    rw [List.length_append, List.length_singleton, hpastLength,
      hstartCursor, hstartedCutoff]
  have hcapsIndex : lastIndex = x.time := hlastIndex
  let records := past ++ [current]
  have hreplyExact : c.preLedger.baseScore i + U.val.S + U.val.q ≤
      (c.preLedger.cutoff - 1) * D p := hreply
  have hbaseTD : c.preLedger.baseScore i + U.val.S ≤ p.T * D p := by
    have hle := hreplyExact
    have hu : c.preLedger.cutoff - 1 ≤ p.T := by
      rw [← hstartedCutoff]
      omega
    have hmul := Nat.mul_le_mul_right (D p) hu
    omega
  have hqueueTD : U.val.q ≤ p.T * D p := by
    have hu : c.preLedger.cutoff - 1 ≤ p.T := by
      rw [← hstartedCutoff]
      omega
    have hmul := Nat.mul_le_mul_right (D p) hu
    omega
  have hdecodeFields :=
    CollectionCheckedExecution.decodeUp_success_candidate started decoded i U hdecode
  obtain ⟨_candidateBound, candidateLast, candidateLastSource,
      candidatePast, candidateCurrent, candidatePastEq, candidateCurrentEq,
      hunknown, hcand⟩ := hdecodeFields
  have hcandidateLast : candidateLast = lastIndex := by
    apply Fin.ext
    have heq := candidateLastSource.trans hlastSource.symm
    change candidateLast.val + 1 = lastIndex.val + 1 at heq
    exact Nat.add_right_cancel heq
  subst candidateLast
  have hcandidatePast : candidatePast = past := Option.some.inj
    (candidatePastEq.symm.trans hpast)
  subst candidatePast
  have hcandidateCurrent : candidateCurrent = current := by
    have hsome : some [candidateCurrent] = some [current] :=
      candidateCurrentEq.symm.trans hcurrent
    exact (List.cons.inj (Option.some.inj hsome)).1
  subst candidateCurrent
  have hfields := acceptUpCandidate_recovered_fields started i U past current
  have hdecodedCurrent : decoded.currentRegisters (started.assignment.arm i) =
      some ⟨(QueueReplay.replay (4 * rate.n) (0, U.val.q) records).2,
        (QueueReplay.replay (4 * rate.n) (0, U.val.q) records).1 -
          (QueueReplay.replay (4 * rate.n) (0, U.val.q) past).1⟩ := by
    rw [hcand]
    exact hfields.1
  have hdecodedIncrement : decoded.increment (started.assignment.arm i) =
      (QueueReplay.replay (4 * rate.n) (0, U.val.q) records).1 := by
    rw [hcand]
    exact hfields.2.1
  have hdecodedCutoff : decoded.cutoffRegisters (started.assignment.arm i) =
      some ⟨started.baseScore i + U.val.S, U.val.q, U.val.delta⟩ := by
    rw [hcand]
    exact hfields.2.2
  rw [hstartedBase] at hdecodedCutoff
  have hdecodedPending : decoded.pending = started.pending.erase i := by
    rw [hcand]
    rfl
  have hstartUnknown : c.preLedger.currentRegisters
      (c.preLedger.assignment.arm i) = none := by
    have h := hunknownStart
    rw [hstartedAssignment] at h
    rw [hstartCandidate] at h
    cases hcur : c.preLedger.currentRegisters (c.preLedger.assignment.arm i) with
    | none => rfl
    | some current => simp [startRoundCandidate, hcur] at h
  have hpreService : started.gammaLoc (started.assignment.arm i) = 0 := by
    rw [hstartedAssignment]
    rw [hstartCandidate]
    simp [startRoundCandidate, hstartUnknown]
  have hcapacity : 4 * rate.n ≤ D p := ActiveFollowerDownAcceptance.four_n_le_D p rate
  have hprefixBound : ∀ h : ℕ, h ≤ records.length →
      c.preLedger.baseScore i + U.val.S +
          (QueueReplay.replay (4 * rate.n) (0, U.val.q) (records.take h)).1 +
          (QueueReplay.replay (4 * rate.n) (0, U.val.q) (records.take h)).2 ≤
        (c.preLedger.cutoff - 1 + h) * D p := by
    intro h hh
    let prefixRecords := records.take h
    have hprefixCap : ∀ record ∈ prefixRecords, record.2 ≤ D p := by
      intro record hmem
      exact hrecordCaps record (List.mem_of_mem_take hmem)
    have hacceptedCap := accepted_total_le prefixRecords (D p) hprefixCap
    have hprefixLength : prefixRecords.length ≤ h := by
      simp [prefixRecords, List.length_take]
    have hacceptedSmall : RecordedQueueRun.acceptedTotal prefixRecords ≤ h * D p :=
      hacceptedCap.trans (Nat.mul_le_mul_right (D p) hprefixLength)
    have htotal := RecordedQueueRun.replay_total (4 * rate.n) (0, U.val.q) prefixRecords
    change (QueueReplay.replay (4 * rate.n) (0, U.val.q) prefixRecords).1 +
        (QueueReplay.replay (4 * rate.n) (0, U.val.q) prefixRecords).2 =
      0 + U.val.q + RecordedQueueRun.acceptedTotal prefixRecords at htotal
    calc
      c.preLedger.baseScore i + U.val.S +
          (QueueReplay.replay (4 * rate.n) (0, U.val.q) prefixRecords).1 +
          (QueueReplay.replay (4 * rate.n) (0, U.val.q) prefixRecords).2 =
        c.preLedger.baseScore i + U.val.S + U.val.q +
          RecordedQueueRun.acceptedTotal prefixRecords := by
            calc
              _ = c.preLedger.baseScore i + U.val.S +
                  ((QueueReplay.replay (4 * rate.n) (0, U.val.q)
                    prefixRecords).1 +
                    (QueueReplay.replay (4 * rate.n) (0, U.val.q)
                      prefixRecords).2) := by omega
              _ = c.preLedger.baseScore i + U.val.S + U.val.q +
                  RecordedQueueRun.acceptedTotal prefixRecords := by
                    rw [htotal]
                    omega
      _ ≤ (c.preLedger.cutoff - 1) * D p + h * D p :=
        Nat.add_le_add hreplyExact hacceptedSmall
      _ = (c.preLedger.cutoff - 1 + h) * D p := by rw [← Nat.add_mul]
  have hdates : c.preLedger.cutoff - 1 + records.length ≤ p.T := by
    rw [hrecordsLength]
    have hv := x.time.isLt
    have hcursorCutoff := hcutCursor
    rw [hstartedCutoff, hstartCursor] at hcursorCutoff
    omega
  have hprefixDomains : ∀ h : ℕ, h ≤ records.length →
      let P := QueueReplay.replay (4 * rate.n) (0, U.val.q) (records.take h)
      (c.preLedger.cutoff - 1 + h) * D p ≤ p.T * D p ∧
      P.1 ≤ p.T * D p ∧ P.2 ≤ p.T * D p ∧
      c.preLedger.baseScore i + U.val.S + P.1 ≤ p.T * D p ∧
      replayLastService (4 * rate.n) (0, U.val.q) U.val.delta
        (records.take h) ≤ D p := by
    intro h hh
    let P := QueueReplay.replay (4 * rate.n) (0, U.val.q) (records.take h)
    have hcreditPrefix := hprefixBound h hh
    have hcalendar : c.preLedger.cutoff - 1 + h ≤ p.T := by omega
    have htimeCredit := hcreditPrefix.trans
      (Nat.mul_le_mul_right (D p) hcalendar)
    refine ⟨Nat.mul_le_mul_right (D p) hcalendar, ?_, ?_, ?_, ?_⟩
    · have : P.1 ≤ c.preLedger.baseScore i + U.val.S + P.1 + P.2 := by omega
      omega
    · have : P.2 ≤ c.preLedger.baseScore i + U.val.S + P.1 + P.2 := by omega
      omega
    · have : c.preLedger.baseScore i + U.val.S + P.1 ≤
          c.preLedger.baseScore i + U.val.S + P.1 + P.2 := by omega
      omega
    · by_cases hzero : h = 0
      · subst h
        simpa [replayLastService] using hmessageDelta
      · have htakeLength : (records.take h).length = h := by
          simp only [List.length_take]
          omega
        have hne : records.take h ≠ [] := by
          intro hempty
          have hzero' : (records.take h).length = 0 := by simp [hempty]
          rw [htakeLength] at hzero'
          omega
        exact (replay_last_service_le (4 * rate.n) (0, U.val.q)
          U.val.delta (records.take h) hne).trans hcapacity
  have hprefixZero : QueueReplay.replay (4 * rate.n) (0, U.val.q) [] =
      (0, U.val.q) := rfl
  have hlastZero : replayLastService (4 * rate.n) (0, U.val.q)
      U.val.delta [] = U.val.delta := rfl
  have hendpoint := hprefixBound records.length (Nat.le_refl _)
  have hendpointCursor : c.preLedger.cutoff - 1 + records.length = started.cursor := by
    rw [hrecordsLength, hstartCursor]
    omega
  have hendpointBound : c.preLedger.baseScore i + U.val.S +
      (QueueReplay.replay (4 * rate.n) (0, U.val.q) records).1 +
      (QueueReplay.replay (4 * rate.n) (0, U.val.q) records).2 ≤
      started.cursor * D p := by
    calc
      _ = c.preLedger.baseScore i + U.val.S +
          (QueueReplay.replay (4 * rate.n) (0, U.val.q)
            (records.take records.length)).1 +
          (QueueReplay.replay (4 * rate.n) (0, U.val.q)
            (records.take records.length)).2 := by simp
      _ ≤ (c.preLedger.cutoff - 1 + records.length) * D p := hendpoint
      _ = started.cursor * D p := by rw [← hendpointCursor]
  have hcurrentIncrement :
      (QueueReplay.replay (4 * rate.n) (0, U.val.q) records).1 -
        (QueueReplay.replay (4 * rate.n) (0, U.val.q) past).1 ≤ D p :=
    (replay_final_increment_le (4 * rate.n) U.val.q past current).trans hcapacity
  have hdecodedCutoffCredit :
      (c.preLedger.baseScore i + U.val.S) + U.val.q ≤
        (c.preLedger.cutoff - 1) * D p := hreplyExact
  have hu : 1 ≤ c.preLedger.cutoff := by
    rw [← hstartedCutoff]
    exact hcutPos
  have huv : c.preLedger.cutoff ≤ x.time.val + 1 := by
    rw [← hstartedCutoff, ← hstartCursor]
    exact hcutCursor
  have hvT : x.time.val + 1 ≤ p.T := by omega
  refine ⟨b, j, F, mu, hb, hj, hbirth, hbase, hretained, hinput,
    hlast, hUsigma, hledgerSigma, hUS, hUdelta, hUq, hmass,
    hdelta, hreply, hmessageDelta, ?_⟩
  refine ⟨⟨c.payload, c.preLedger, c.started, c.weights⟩,
    recording, started, decoded, bank, htailChoice, rfl, hrecording,
    hstart, hstartedAssignment, hstartedBase, hreceive, hparsed,
    hparse, hdecode, hbound,
    hstartedCutoff, hstartCursor, hu, huv, hvT, lastIndex,
    hlastIndex, past, current, hpast, ?_, hrecordCaps, hrecordsLength,
    hprefixZero, hlastZero, hbaseTD, hqueueTD, hmessageDelta,
    ?_, hdecodedCurrent, hdecodedIncrement, hdecodedCutoff,
    hdecodedPending, hunknownStart, hunknownCutoff, hpreService,
    ?_, hdecodedCutoffCredit, hcurrentIncrement⟩
  · simpa only [hlastIndex] using hcurrent
  · intro h hh
    simpa [records] using And.intro (hprefixBound h hh)
      (hprefixDomains h hh)
  · rw [hdecodedIncrement]
    exact hendpointBound

end Bandits.Support.ReferenceCompleteAcceptedUpReplayBounds

end
