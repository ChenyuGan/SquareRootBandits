/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteCoordinatorMass

import Lean.Elab.Tactic.Omega

/-!
# Collection increment spans on the complete physical suffix

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:157-188,245-290`,
`sources/zip4/manuscript/06_interruptions.tex:9-100,246-349,355-390`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:8-64`.
The named consumer is `ReferenceCompleteEpisodeScoreGrowth`.

The public source-root results in this module follow the original complete
physical suffix.  Collection service is clipped at the ledger's actual
freeze boundary, including when the physical collection continues afterward.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceCompleteCollectionIncrementSpan

open ConstructorDimensions
open ReferenceActivePhysicalStep
open ReferenceActivePhysicalHorizon
open CoordinatorCollectionLedger
open CollectionKnownQueueContinuation
open ReferenceCollectionPhaseHistory

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

private theorem queueReplay_score_le_capacity_length (capacity : ℕ)
    (initial : ℕ × ℕ) (records : List (Bool × ℕ)) :
    (QueueReplay.replay capacity initial records).1 ≤
      initial.1 + capacity * records.length := by
  induction records generalizing initial with
  | nil => simp [QueueReplay.replay]
  | cons record rest ih =>
      change (QueueReplay.replay capacity initial ([record] ++ rest)).1 ≤ _
      rw [QueueReplay.replay_append]
      have hhead :
          (QueueReplay.transition capacity initial record).1 ≤ initial.1 + capacity := by
        cases record with
        | mk enabled arrival =>
            cases enabled
            · simp [QueueReplay.transition]
            · simp only [QueueReplay.transition, ite_true]
              exact Nat.add_le_add_left (Nat.min_le_left _ _) _
      have htail := ih (QueueReplay.transition capacity initial record)
      simpa [List.length_cons, QueueReplay.replay] using
        (calc
          (QueueReplay.replay capacity (QueueReplay.transition capacity initial record)
              rest).1 ≤ (QueueReplay.transition capacity initial record).1 +
                capacity * rest.length := htail
          _ ≤ initial.1 + capacity + capacity * rest.length :=
            Nat.add_le_add_right hhead _
          _ = initial.1 + capacity * (rest.length + 1) := by
            rw [Nat.mul_add, Nat.mul_one]
            omega)

private theorem queueReplay_replay_disabled (capacity : ℕ)
    (initial : ℕ × ℕ) (records : List (Bool × ℕ))
    (hdisabled : ∀ record ∈ records, record.1 = false) :
    QueueReplay.replay capacity initial records = initial := by
  induction records generalizing initial with
  | nil => simp [QueueReplay.replay]
  | cons record rest ih =>
      have hhead := hdisabled record (by simp)
      have htail : ∀ item ∈ rest, item.1 = false := by
        intro item hitem
        exact hdisabled item (by simp [hitem])
      change QueueReplay.replay capacity initial ([record] ++ rest) = initial
      rw [QueueReplay.replay_append]
      have hsingle : QueueReplay.replay capacity initial [record] = initial := by
        cases record with
        | mk enabled arrival =>
            cases enabled <;> simp_all [QueueReplay.replay, QueueReplay.transition]
      rw [hsingle, ih initial htail]

/-- A replay whose post-freeze records are disabled accumulates at most one
capacity for each record in the retained prefix. -/
private theorem queueReplay_score_le_retained_prefix
    (capacity : ℕ) (initial : ℕ × ℕ) (firstRecords suffix : List (Bool × ℕ))
    (retained : ℕ) (hlength : firstRecords.length ≤ retained)
    (hdisabled : ∀ record ∈ suffix, record.1 = false) :
    (QueueReplay.replay capacity initial (firstRecords ++ suffix)).1 ≤
      initial.1 + capacity * retained := by
  rw [QueueReplay.replay_append,
    queueReplay_replay_disabled capacity (QueueReplay.replay capacity initial firstRecords)
      suffix hdisabled]
  have hprefix := queueReplay_score_le_capacity_length capacity initial firstRecords
  exact Nat.le_trans hprefix (Nat.add_le_add_left
    (Nat.mul_le_mul_left capacity hlength) _)

private theorem calendarIndices_append (T start first second : ℕ)
    (hfirst : start + first ≤ T) (htotal : start + (first + second) ≤ T) :
    calendarIndices T start (first + second) htotal =
      calendarIndices T start first hfirst ++
        calendarIndices T (start + first) second (by omega) := by
  let left : Fin first → Fin T := fun i => ⟨start + i.val, by omega⟩
  let right : Fin second → Fin T := fun i => ⟨start + first + i.val, by omega⟩
  let joined : Fin (first + second) → Fin T := fun i => ⟨start + i.val, by omega⟩
  have hjoined : Fin.append left right = joined := by
    funext i
    refine Fin.addCases ?_ ?_ i
    · intro j
      apply Fin.ext
      simp [Fin.append, left, joined]
    · intro j
      apply Fin.ext
      simp [Fin.append, right, joined, Nat.add_assoc]
  change List.ofFn joined = List.ofFn left ++ List.ofFn right
  rw [← hjoined, List.ofFn_fin_append]

private theorem replayRecords?_append
    (ledger : Ledger rate) (arm : Fin p.K)
    (firstIndices secondIndices : List (Fin p.T))
    (firstRecords secondRecords : List (Bool × ℕ))
    (hfirst : replayRecords? ledger arm firstIndices = some firstRecords)
    (hsecond : replayRecords? ledger arm secondIndices = some secondRecords) :
    replayRecords? ledger arm (firstIndices ++ secondIndices) =
      some (firstRecords ++ secondRecords) := by
  induction firstIndices generalizing firstRecords with
  | nil =>
      simp only [replayRecords?] at hfirst
      cases Option.some.inj hfirst
      simpa using hsecond
  | cons index rest ih =>
      cases henabled : ledger.enabledHistory index with
      | none => simp [replayRecords?, henabled] at hfirst
      | some enabled =>
          cases htail : replayRecords? ledger arm rest with
          | none => simp [replayRecords?, henabled, htail] at hfirst
          | some tail =>
              have hrecord :
                  (enabled && decide (sourceRound index < ledger.freezeAt),
                    bufferedArrival ledger arm index) :: tail = firstRecords := by
                simpa [replayRecords?, henabled, htail] using hfirst
              change replayRecords? ledger arm (index :: (rest ++ secondIndices)) = _
              have htailAppend := ih tail htail
              calc
                replayRecords? ledger arm (index :: (rest ++ secondIndices)) =
                    (do
                      let enabled ← ledger.enabledHistory index
                      let tail ← replayRecords? ledger arm (rest ++ secondIndices)
                      pure ((enabled && decide (sourceRound index < ledger.freezeAt),
                        bufferedArrival ledger arm index) :: tail)) := rfl
                _ = some ((enabled && decide (sourceRound index < ledger.freezeAt),
                    bufferedArrival ledger arm index) :: (tail ++ secondRecords)) := by
                      simp [henabled, htailAppend]
                _ = some (firstRecords ++ secondRecords) := by
                      rw [← hrecord]
                      simp

private theorem replayRecords?_split
    (ledger : Ledger rate) (arm : Fin p.K)
    (firstIndices secondIndices : List (Fin p.T))
    (records : List (Bool × ℕ))
    (hrecords : replayRecords? ledger arm (firstIndices ++ secondIndices) =
      some records) :
    ∃ firstRecords secondRecords,
      replayRecords? ledger arm firstIndices = some firstRecords ∧
      replayRecords? ledger arm secondIndices = some secondRecords ∧
      records = firstRecords ++ secondRecords := by
  induction firstIndices generalizing records with
  | nil =>
      simp only [List.nil_append] at hrecords
      exact ⟨[], records, rfl, hrecords, by simp⟩
  | cons index rest ih =>
      cases henabled : ledger.enabledHistory index with
      | none => simp [replayRecords?, henabled] at hrecords
      | some enabled =>
          cases htail : replayRecords? ledger arm (rest ++ secondIndices) with
          | none => simp [replayRecords?, henabled, htail] at hrecords
          | some tail =>
              have hrecord :
                  (enabled && decide (sourceRound index < ledger.freezeAt),
                    bufferedArrival ledger arm index) :: tail = records := by
                simpa [replayRecords?, henabled, htail] using hrecords
              obtain ⟨firstTail, secondRecords, hfirstTail, hsecond, htailEq⟩ :=
                ih tail htail
              refine ⟨(enabled && decide (sourceRound index < ledger.freezeAt),
                bufferedArrival ledger arm index) :: firstTail, secondRecords, ?_,
                hsecond, ?_⟩
              · simp [replayRecords?, henabled, hfirstTail]
              · rw [← hrecord, htailEq, List.cons_append]

private theorem replayRecords?_length
    (ledger : Ledger rate) (arm : Fin p.K)
    (indices : List (Fin p.T)) (records : List (Bool × ℕ))
    (hrecords : replayRecords? ledger arm indices = some records) :
    records.length = indices.length := by
  induction indices generalizing records with
  | nil =>
      simp only [replayRecords?] at hrecords
      cases Option.some.inj hrecords
      rfl
  | cons index rest ih =>
      cases henabled : ledger.enabledHistory index with
      | none => simp [replayRecords?, henabled] at hrecords
      | some enabled =>
          cases htail : replayRecords? ledger arm rest with
          | none => simp [replayRecords?, henabled, htail] at hrecords
          | some tail =>
              have hrecord :
                  (enabled && decide (sourceRound index < ledger.freezeAt),
                    bufferedArrival ledger arm index) :: tail = records := by
                simpa [replayRecords?, henabled, htail] using hrecords
              rw [← hrecord, List.length_cons, List.length_cons,
                ih tail htail]

private theorem calendarIndices_singleton (T start : ℕ) (hbound : start + 1 ≤ T)
    (last : Fin T) (hlast : last.val = start) :
    calendarIndices T start 1 hbound = [last] := by
  simp [calendarIndices]
  exact Fin.ext hlast.symm

private theorem replayRecords?_disabled_of_frozen_indices
    (ledger : Ledger rate) (arm : Fin p.K)
    (indices : List (Fin p.T)) (records : List (Bool × ℕ))
    (hrecords : replayRecords? ledger arm indices = some records)
    (hafter : ∀ index ∈ indices, ledger.freezeAt ≤ sourceRound index) :
    ∀ record ∈ records, record.1 = false := by
  induction indices generalizing records with
  | nil =>
      simp only [replayRecords?] at hrecords
      cases Option.some.inj hrecords
      simp
  | cons index rest ih =>
      cases henabled : ledger.enabledHistory index with
      | none => simp [replayRecords?, henabled] at hrecords
      | some enabled =>
          cases htail : replayRecords? ledger arm rest with
          | none => simp [replayRecords?, henabled, htail] at hrecords
          | some tail =>
              have hrecord :
                  (enabled && decide (sourceRound index < ledger.freezeAt),
                    bufferedArrival ledger arm index) :: tail = records := by
                simpa [replayRecords?, henabled, htail] using hrecords
              have hhead : (enabled && decide (sourceRound index < ledger.freezeAt)) = false := by
                simp [Nat.not_lt_of_ge (hafter index (by simp))]
              have htailAfter : ∀ item ∈ rest, ledger.freezeAt ≤ sourceRound item := by
                intro item hitem
                exact hafter item (by simp [hitem])
              cases hrecord
              intro record hmem
              simp only [List.mem_cons] at hmem
              rcases hmem with rfl | hmem
              · exact hhead
              · exact ih tail htail htailAfter _ hmem

private theorem calendarIndices_frozen
    (T start length freezeAt : ℕ) (hbound : start + length ≤ T)
    (hfreeze : freezeAt ≤ start + 1) :
    ∀ index ∈ calendarIndices T start length hbound,
      freezeAt ≤ sourceRound index := by
  intro index hmem
  have hinterval := CollectionBufferProvenance.calendarIndices_sourceRound_bounds
    T start length hbound index hmem
  exact hfreeze.trans hinterval.1

/- The exact accepted-UP replay after the decoded arm is recovered has no
score contribution after the ledger's own freeze boundary. -/
theorem accepted_up_decoded_increment_span
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (c : ReferenceCollectionSegmentExtraction.Choice rate)
    (hchoice : ReferenceCollectionSegmentExtraction.choice
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val]'k.isLt).input = some c)
    (i : Fin (p.m - 1)) (U : UpRecord p rate)
    (haccepted : AcceptedUp
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val]'k.isLt).input i U) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h
    let x := (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val]'k.isLt |>.input
    ∃ (b j : Fin R.length) (F : ReferencePrelaunchFollower.State p rate.eta)
      (mu : ActiveFollowerLifecycle.LocalMemory p)
      (started decoded : Ledger rate) (bank : CoordinatorUpReception.UpDecoderBank p)
      (recording : CoordinatorRecordingOperation.Output p)
      (past : List (Bool × ℕ)) (currentRecord : Bool × ℕ),
      b.val ≤ j.val ∧ j.val < k.val ∧
      ReferenceAssignmentPayloadPersistence.InstallationBirth R[b.val] c.payload ∧
      ReferenceAssignmentCollectionMassSteps.installedBaseScore R[b.val] =
        some c.preLedger.baseScore ∧
      ReferenceAcceptedUpFollowerHistory.RetainedDown R[j.val] i
        (c.payload.downRecord i) ∧
      R[k.val].input.state.followers i = .ordinary F mu ∧
      F.lastDown = some (c.payload.downRecord i) ∧
      U.val.S = F.S ∧ U.val.q = F.backlog ∧
      CoordinatorRecorderComplementBridge.run
        (ReferenceActivePhysicalStep.collectionRecordingInput
          (ReferenceActivePhysicalStep.prepare x) c.payload c.started c.weights) =
        some recording ∧
      startRound c.preLedger (x.time.val + 1)
        (ReferenceActivePhysicalStep.collectionEnabled c.preLedger x.time)
        (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) =
          .success started ∧
      (ReferenceActivePhysicalStep.receiveUp
        (ReferenceActivePhysicalStep.prepare x) started).result = .success (decoded, bank) ∧
      filteredParsed x started = some U ∧
      decodeUp started i (some U) = .success decoded ∧
      started.cutoff = c.preLedger.cutoff ∧
      started.cursor = x.time.val + 1 ∧
      started.freezeAt = c.preLedger.freezeAt ∧
      decoded.increment (started.assignment.arm i) =
        (QueueReplay.replay (4 * rate.n) (0, U.val.q)
          (past ++ [currentRecord])).1 ∧
      started.gammaLoc (started.assignment.arm i) = 0 ∧
      decoded.increment (started.assignment.arm i) ≤
        4 * rate.n * (min (x.time.val + 2) c.preLedger.freezeAt - c.preLedger.cutoff) := by
  classical
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h
  let x := (R[k.val]'k.isLt).input
  -- The admitted decoded numerical-mass API supplies the calendar domain
  -- of this real accepted event. The stronger public prefix chronology below
  -- also retains its actual START, so the freeze mask is the source mask.
  obtain ⟨massStarted, massDecoded, _massBank, _massBound, _massIndex,
    _massPast, _massRecord, _massCut, _massCurrent, _massReceive, _massFiltered,
    _massEffective, hmassDecode, _massAssignment, _massBase, hmassCutoff,
    hmassCursor, _massReplay⟩ :=
    ReferenceCompleteCoordinatorMass.complete_accepted_up_decoded_numerical_mass
      rate rewards C_star C_h source k c hchoice i U haccepted
  have hmassInput : validLedgerCheck massStarted = true ∧ massStarted.phase = .started ∧
      1 ≤ massStarted.cutoff ∧ massStarted.cutoff ≤ massStarted.cursor ∧
      massStarted.cursor ≤ p.T := by
    by_contra hnot
    simp only [decodeUp, dite_eq_right hnot] at hmassDecode
    cases hmassDecode
  have hcutoffPositive : 1 ≤ c.preLedger.cutoff := by
    rw [← hmassCutoff]
    exact hmassInput.2.2.1
  have hcutoffCurrent : c.preLedger.cutoff ≤ x.time.val + 1 := by
    rw [← hmassCutoff, ← hmassCursor]
    exact hmassInput.2.2.2.1
  have hendpoint : x.time.val + 1 ≤ p.T := by
    rw [← hmassCursor]
    exact hmassInput.2.2.2.2
  obtain ⟨b, j, F, mu, hbj, hjk, hbirth, hbase, hretained,
    hinput, hlastDown, _hUsigma, _hledgerSigma, hUS, _hUdelta, hUq, _hmass,
    _hdelta, _hreply, _hmessageDelta, htailData⟩ :=
    ReferenceCompleteAcceptedUpReplayBounds.complete_accepted_up_replay_prefix_credit
      rewards C_star C_h source k c hchoice i U haccepted
  rcases htailData with
    ⟨_tail, recording, started, decoded, bank, _executed, _tailEq, hrecording,
      hstart, _startedAssignment, _startedBase, hreceive, hfiltered, _heffective,
      hdecode, hdata⟩
  rcases hdata with
    ⟨hbound, hcutoff, hcursor, _, _, _, hindexData⟩
  rcases hindexData with ⟨lastIndex, hindexData⟩
  rcases hindexData with ⟨hlastIndex, hrecordsData⟩
  rcases hrecordsData with
    ⟨past, currentRecord, hpast, hcurrentRecord, _caps, _length,
      _emptyQueue, _emptyLast, _baseBound, _queueBound, _deltaBound, _prefix,
      _decodedCurrent, hdecodedIncrement, _decodedCutoff, _pending,
      _startedCurrent, _startedCutoff, hgamma, _joint, _cutBudget, _currentService⟩
  let arm := started.assignment.arm i
  have hstartFreeze := CollectionCheckedExecution.startRound_success_candidate
    c.preLedger started (x.time.val + 1)
    (ReferenceActivePhysicalStep.collectionEnabled c.preLedger x.time)
    (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) hstart
  have hfreeze : started.freezeAt = c.preLedger.freezeAt := by
    rw [hstartFreeze]
    rfl
  have hpastLength : past.length = started.cursor - started.cutoff := by
    rw [replayRecords?_length started arm _ past hpast, calendarIndices_length]
  let pastIndices := calendarIndices p.T (started.cutoff - 1)
    (started.cursor - started.cutoff) hbound
  have hfullBound : started.cutoff - 1 +
      (started.cursor - started.cutoff + 1) ≤ p.T := by
    rw [hcursor]
    omega
  have hlastValue : lastIndex.val = x.time.val := by
    have h := hlastIndex
    exact congrArg Fin.val h
  have hlastStart : started.cutoff - 1 +
      (started.cursor - started.cutoff) = lastIndex.val := by
    rw [hcursor, hlastValue]
    omega
  have hlastList : calendarIndices p.T
      (started.cutoff - 1 + (started.cursor - started.cutoff)) 1 hfullBound =
        [lastIndex] := by
    exact calendarIndices_singleton p.T _ hfullBound lastIndex hlastStart.symm
  have hfullIndices :
      calendarIndices p.T (started.cutoff - 1)
        (started.cursor - started.cutoff + 1) hfullBound =
      pastIndices ++ [lastIndex] := by
    calc
      calendarIndices p.T (started.cutoff - 1)
          (started.cursor - started.cutoff + 1) hfullBound =
        calendarIndices p.T (started.cutoff - 1)
            (started.cursor - started.cutoff) hbound ++
          calendarIndices p.T
            (started.cutoff - 1 + (started.cursor - started.cutoff)) 1 hfullBound := by
              simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
                calendarIndices_append p.T (started.cutoff - 1)
                  (started.cursor - started.cutoff) 1 hbound hfullBound
      _ = pastIndices ++ [lastIndex] := by rw [hlastList]
  have hfullRecords :
      replayRecords? started arm
        (calendarIndices p.T (started.cutoff - 1)
          (started.cursor - started.cutoff + 1) hfullBound) =
        some (past ++ [currentRecord]) := by
    rw [hfullIndices]
    exact replayRecords?_append started arm pastIndices [lastIndex]
      past [currentRecord] hpast hcurrentRecord
  let total := started.cursor - started.cutoff + 1
  let retained := min total (started.freezeAt - started.cutoff)
  let suffixLength := total - retained
  have hsplitBounds :
      started.cutoff - 1 + retained ≤ p.T ∧
      (started.cutoff - 1 + retained) + suffixLength ≤ p.T := by
    dsimp [total, suffixLength]
    omega
  let firstIndices := calendarIndices p.T (started.cutoff - 1) retained
    hsplitBounds.1
  let suffixIndices := calendarIndices p.T (started.cutoff - 1 + retained)
    suffixLength hsplitBounds.2
  have hsplitIndices :
      calendarIndices p.T (started.cutoff - 1) total hfullBound =
        firstIndices ++ suffixIndices := by
    dsimp [firstIndices, suffixIndices]
    have htotalBound : started.cutoff - 1 + (retained + suffixLength) ≤ p.T := by
      omega
    have hsum : total = retained + suffixLength := by
      dsimp [suffixLength]
      omega
    simpa only [hsum] using calendarIndices_append p.T
      (started.cutoff - 1) retained suffixLength hsplitBounds.1 htotalBound
  have hsplitRecords :
      replayRecords? started arm (firstIndices ++ suffixIndices) =
        some (past ++ [currentRecord]) := by
    rw [← hsplitIndices]
    simpa only [total] using hfullRecords
  obtain ⟨firstRecords, suffixRecords, hfirstRecords, hsuffixRecords,
      hrecordsEq⟩ := replayRecords?_split started arm firstIndices suffixIndices
        (past ++ [currentRecord]) hsplitRecords
  have hfirstLength : firstRecords.length = retained := by
    rw [replayRecords?_length started arm firstIndices firstRecords hfirstRecords]
    exact calendarIndices_length _ _ _ _
  have hsuffixFrozen : ∀ index ∈ suffixIndices,
      started.freezeAt ≤ sourceRound index := by
    by_cases hempty : suffixLength = 0
    · intro index hmem
      simp [suffixIndices, hempty, calendarIndices] at hmem
    · have hretained : retained = started.freezeAt - started.cutoff := by
        dsimp [suffixLength, retained, total] at hempty ⊢
        omega
      have hfreezeStart : started.freezeAt ≤
          started.cutoff - 1 + retained + 1 := by
        rw [hretained]
        omega
      have hsuffixBound :
          (started.cutoff - 1 + retained) + suffixLength ≤ p.T := hsplitBounds.2
      exact calendarIndices_frozen p.T (started.cutoff - 1 + retained)
        suffixLength started.freezeAt hsuffixBound hfreezeStart
  have hsuffixDisabled := replayRecords?_disabled_of_frozen_indices started arm
    suffixIndices suffixRecords hsuffixRecords hsuffixFrozen
  have hqueueBound := queueReplay_score_le_retained_prefix (4 * rate.n)
    (0, U.val.q) firstRecords suffixRecords retained hfirstLength.le hsuffixDisabled
  have hdecodedIncrement' := hdecodedIncrement
  rw [hrecordsEq] at hdecodedIncrement'
  have hretainedEq : retained =
      min (x.time.val + 2) c.preLedger.freezeAt - c.preLedger.cutoff := by
    dsimp [retained, total]
    rw [hcursor, hcutoff, hfreeze]
    omega
  have hbound' : decoded.increment arm ≤
      4 * rate.n * (min (x.time.val + 2) c.preLedger.freezeAt - c.preLedger.cutoff) := by
    calc
      decoded.increment arm =
          (QueueReplay.replay (4 * rate.n) (0, U.val.q)
            (firstRecords ++ suffixRecords)).1 := hdecodedIncrement'
      _ ≤ 0 + 4 * rate.n * retained := hqueueBound
      _ = 4 * rate.n *
          (min (x.time.val + 2) c.preLedger.freezeAt - c.preLedger.cutoff) := by
            rw [hretainedEq]
            omega
  exact ⟨b, j, F, mu, started, decoded, bank, recording, past, currentRecord,
    hbj, hjk, hbirth, hbase, hretained, hinput, hlastDown, hUS, hUq,
    hrecording, hstart, hreceive, hfiltered, hdecode,
    hcutoff, hcursor, hfreeze, hdecodedIncrement, hgamma, hbound'⟩

/-- A single checked continuation adds at most one service capacity, and adds
it only before the actual freeze boundary.  The source cursor advances once
from the incoming ready cursor, including on a disabled round. -/
theorem checked_known_increment_span
    (l started decoded finished : Ledger rate)
    (input : CollectionCheckedExecution.RoundInput (p := p) (eta := rate.eta.val))
    (a : Fin p.K) (current : CurrentRegister)
    (hcut : l.cutoff ≤ l.cursor)
    (hknown : l.currentRegisters a = some current)
    (hspan : l.increment a ≤ 4 * rate.n * (min l.cursor l.freezeAt - l.cutoff))
    (hstart : startRound l (sourceRound input.round) input.enabled input.raw =
      .success started)
    (hdecode : decodeUp started input.selectedFollower input.parsed = .success decoded ∨
      decodeUp started input.selectedFollower input.parsed = .rejected decoded)
    (hfinish : finishRound decoded = .success finished) :
    finished.increment a ≤
      4 * rate.n * (min finished.cursor finished.freezeAt - finished.cutoff) ∧
    finished.cutoff = l.cutoff ∧ finished.freezeAt = l.freezeAt ∧
    finished.cursor = l.cursor + 1 := by
  have htransition := checkedRound_known_transition l started decoded finished
    input a current hknown hstart hdecode hfinish
  rcases htransition with ⟨_, hincrement, _, _, hcutoff, hfreeze, _⟩
  have hstartCursor := CollectionCheckedExecution.startRound_success_cursor l started
    (sourceRound input.round) input.enabled input.raw hstart
  have hstartTime := CollectionCheckedExecution.startRound_success_time l started
    (sourceRound input.round) input.enabled input.raw hstart
  have hdcursor : decoded.cursor = started.cursor := by
    rcases hdecode with hsuccess | hrejected
    · cases hp : input.parsed with
      | none =>
          simp only [hp, decodeUp] at hsuccess
          split at hsuccess
          · split at hsuccess <;> cases hsuccess
          · cases hsuccess
      | some U =>
          rw [hp] at hsuccess
          obtain ⟨_, _, _, _, _, _, _, _, hcandidate⟩ :=
            CollectionCheckedExecution.decodeUp_success_candidate
              started decoded input.selectedFollower U hsuccess
          rw [hcandidate]
          rfl
    · rw [decodeUp_rejected_candidate started decoded input.selectedFollower
        input.parsed hrejected]
  have hfinishCursor := CollectionCheckedExecution.finishRound_success_chronology
    decoded finished hfinish
  have hcursor : finished.cursor = l.cursor + 1 := by
    rw [hfinishCursor.1, hdcursor, hstartCursor, hstartTime]
  have hstepCursor : sourceRound input.round = l.cursor := by
    exact hstartTime
  let record := localQueueRecord l input.round input.enabled input.raw a
  let next := QueueReplay.transition (4 * rate.n) (l.increment a, current.queue) record
  have hstep : next.1 ≤ l.increment a + 4 * rate.n := by
    change (QueueReplay.transition (4 * rate.n)
      (l.increment a, current.queue) record).1 ≤ _
    cases hrecord : record.1 with
    | false => simp [QueueReplay.transition, hrecord]
    | true =>
        simp only [QueueReplay.transition, hrecord, ite_true]
        exact Nat.add_le_add_left (Nat.min_le_left _ _) _
  have hincrement' : finished.increment a = next.1 := by
    simpa [next, record] using hincrement
  have hscoreStep : finished.increment a ≤ l.increment a + 4 * rate.n := by
    rw [hincrement']
    exact hstep
  by_cases hbefore : l.cursor < l.freezeAt
  · rw [hcutoff, hfreeze, hcursor]
    have hmin : min (l.cursor + 1) l.freezeAt = l.cursor + 1 := by omega
    rw [hmin]
    have hminOld : min l.cursor l.freezeAt = l.cursor := Nat.min_eq_left (by omega)
    rw [hminOld] at hspan
    refine ⟨?_, rfl, rfl, rfl⟩
    calc
      finished.increment a ≤ l.increment a + 4 * rate.n := hscoreStep
      _ ≤ 4 * rate.n * (l.cursor - l.cutoff) + 4 * rate.n :=
        Nat.add_le_add_right hspan _
      _ = 4 * rate.n * (l.cursor + 1 - l.cutoff) := by
        have hsub : l.cursor + 1 - l.cutoff = (l.cursor - l.cutoff) + 1 := by omega
        rw [hsub, Nat.mul_add, Nat.mul_one]
  · have hmin : min (l.cursor + 1) l.freezeAt = min l.cursor l.freezeAt := by
      rw [Nat.min_eq_right (by omega : l.freezeAt ≤ l.cursor + 1),
        Nat.min_eq_right (by omega : l.freezeAt ≤ l.cursor)]
    have hrecordFalse : localQueueRecord l input.round input.enabled input.raw a =
        (false, 0) := by
      apply localQueueRecord_disabled_or_frozen
      right
      rw [hstepCursor]
      omega
    rw [hcutoff, hfreeze, hcursor, hmin]
    have hunchanged : finished.increment a = l.increment a := by
      rw [hincrement']
      simp [next, record, hrecordFalse, QueueReplay.transition]
    exact ⟨by simpa [hunchanged] using hspan, rfl, rfl, rfl⟩

private theorem decode_frame (started decoded : Ledger rate)
    (i : Fin (p.m - 1)) (parsed : Option (UpRecord p rate))
    (hdecode : decodeUp started i parsed = .success decoded ∨
      decodeUp started i parsed = .rejected decoded) :
    decoded.cursor = started.cursor ∧ decoded.cutoff = started.cutoff ∧
      decoded.freezeAt = started.freezeAt ∧ decoded.baseScore = started.baseScore ∧
      decoded.assignment = started.assignment ∧ decoded.sigma = started.sigma := by
  rcases hdecode with hs | hr
  · cases hp : parsed with
    | none =>
        simp only [hp, decodeUp] at hs
        split at hs
        · split at hs <;> cases hs
        · cases hs
    | some U =>
        rw [hp] at hs
        obtain ⟨_, _, _, _, _, _, _, _, hc⟩ :=
          CollectionCheckedExecution.decodeUp_success_candidate started decoded i U hs
        rw [hc]
        exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · rw [decodeUp_rejected_candidate started decoded i parsed hr]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem checked_round_span
    (l started decoded finished : Ledger rate)
    (input : CollectionCheckedExecution.RoundInput (p := p) (eta := rate.eta.val))
    (hspan : ∀ a cut current, l.cutoffRegisters a = some cut →
      l.currentRegisters a = some current →
      l.increment a ≤ 4 * rate.n * (min l.cursor l.freezeAt - l.cutoff))
    (hnew : ∀ U : UpRecord p rate, input.parsed = some U →
      decodeUp started input.selectedFollower (some U) = .success decoded →
      decoded.increment (started.assignment.arm input.selectedFollower) ≤
        4 * rate.n * (min (input.round.val + 2) l.freezeAt - l.cutoff))
    (hstart : startRound l (sourceRound input.round) input.enabled input.raw = .success started)
    (hdecode : decodeUp started input.selectedFollower input.parsed = .success decoded ∨
      decodeUp started input.selectedFollower input.parsed = .rejected decoded)
    (hfinish : finishRound decoded = .success finished) :
    finished.cursor = input.round.val + 2 ∧ finished.cutoff = l.cutoff ∧
      finished.freezeAt = l.freezeAt ∧ finished.baseScore = l.baseScore ∧
      finished.assignment = l.assignment ∧ finished.sigma = l.sigma ∧
      ∀ a cut current, finished.cutoffRegisters a = some cut →
        finished.currentRegisters a = some current →
        finished.increment a ≤
          4 * rate.n * (min finished.cursor finished.freezeAt - finished.cutoff) := by
  have hs := CollectionCheckedExecution.startRound_success_candidate l started
    (sourceRound input.round) input.enabled input.raw hstart
  have hindex : (⟨sourceRound input.round - 1, by simp [sourceRound]⟩ : Fin p.T) =
      input.round := by
    apply Fin.ext
    simp only [sourceRound, Nat.add_sub_cancel]
  rw [hindex] at hs
  have hf := CollectionCheckedExecution.finishRound_success_candidate decoded finished hfinish
  obtain ⟨hdcursor, hdcut, hdfreeze, hdbase, hdassignment, hdsigma⟩ :=
    decode_frame started decoded input.selectedFollower input.parsed hdecode
  have hcursor : finished.cursor = input.round.val + 2 := by
    rw [(CollectionCheckedExecution.finishRound_success_chronology decoded finished hfinish).1,
      hdcursor, CollectionCheckedExecution.startRound_success_cursor l started
        (sourceRound input.round) input.enabled input.raw hstart]
    rfl
  have hcut : finished.cutoff = l.cutoff := by
    rw [hf]
    change decoded.cutoff = _
    rw [hdcut, hs]
    rfl
  have hfreeze : finished.freezeAt = l.freezeAt := by
    rw [hf]
    change decoded.freezeAt = _
    rw [hdfreeze, hs]
    rfl
  have hbase : finished.baseScore = l.baseScore := by
    rw [hf]
    change decoded.baseScore = _
    rw [hdbase, hs]
    rfl
  have hassignment : finished.assignment = l.assignment := by
    rw [hf]
    change decoded.assignment = _
    rw [hdassignment, hs]
    rfl
  have hsigma : finished.sigma = l.sigma := by
    rw [hf]
    change decoded.sigma = _
    rw [hdsigma, hs]
    rfl
  refine ⟨hcursor, hcut, hfreeze, hbase, hassignment, hsigma, ?_⟩
  intro a cut current hc hq
  cases hknown : l.currentRegisters a with
  | some previous =>
      have ht := checkedRound_known_transition l started decoded finished input a previous
        hknown hstart hdecode hfinish
      have hcutOld : l.cutoffRegisters a = some cut := ht.2.2.2.2.2.2.symm.trans hc
      have hvalid : validLedgerCheck l = true := by
        unfold startRound at hstart
        split at hstart
        · rename_i hin
          exact hin.1
        · contradiction
      have hcutCursor : l.cutoff ≤ l.cursor := by
        simp only [validLedgerCheck, Bool.and_eq_true, decide_eq_true_eq] at hvalid
        tauto
      exact (checked_known_increment_span l started decoded finished input a previous
        hcutCursor hknown (hspan a cut previous hcutOld hknown) hstart hdecode hfinish).1
  | none =>
      have hstartedNone : started.currentRegisters a = none := by
        rw [hs]
        simp only [startRoundCandidate, hknown]
      rcases hdecode with hsuccess | hrejected
      · cases hp : input.parsed with
        | none =>
            simp only [hp, decodeUp] at hsuccess
            split at hsuccess
            · split at hsuccess <;> cases hsuccess
            · cases hsuccess
        | some U =>
            have hd : decodeUp started input.selectedFollower (some U) = .success decoded := by
              simpa only [hp] using hsuccess
            obtain ⟨_, _, _, _, _, _, _, hunknown, hdCandidate⟩ :=
              CollectionCheckedExecution.decodeUp_success_candidate started decoded
                input.selectedFollower U hd
            have harm : a = started.assignment.arm input.selectedFollower := by
              by_contra hne
              have hnone : finished.currentRegisters a = none := by
                rw [hf, hdCandidate]
                simp only [finishRoundCandidate, acceptUpCandidate,
                  Function.update_of_ne hne, hstartedNone]
              rw [hnone] at hq
              cases hq
            have hgamma : started.gammaLoc a = 0 := by
              rw [hs]
              simp only [startRoundCandidate, hknown]
            have hfinished : finished.increment a = decoded.increment a := by
              rw [hf]
              change decoded.increment a + decoded.gammaLoc a = decoded.increment a
              have hg : decoded.gammaLoc a = 0 := by rw [hdCandidate]; exact hgamma
              rw [hg, Nat.add_zero]
            rw [hfinished, hcursor, hcut, hfreeze, harm]
            exact hnew U hp hd
      · have hnone : finished.currentRegisters a = none := by
          rw [hf, decodeUp_rejected_candidate started decoded input.selectedFollower
            input.parsed hrejected]
          exact hstartedNone
        rw [hnone] at hq
        cases hq

private theorem choice_executed_tail
    (x : RoundInput p rate) (c : ReferenceCollectionSegmentExtraction.Choice rate)
    (hchoice : ReferenceCollectionSegmentExtraction.choice x = some c) :
    executedTail x = some ⟨c.payload, c.preLedger, c.started, c.weights⟩ := by
  unfold ReferenceCollectionSegmentExtraction.choice at hchoice
  split at hchoice
  · contradiction
  next hn =>
    unfold executedTail
    dsimp only
    split
    · contradiction
    next _ =>
      cases hc : (prepare x).coordinator with
      | first outcome =>
          cases outcome <;>
            simp only [hc, ReferenceCollectionSegmentExtraction.choiceOfCut] at hchoice
          all_goals contradiction
      | live r q base outcome =>
          cases outcome <;>
            simp only [hc, ReferenceCollectionSegmentExtraction.choiceOfCut] at hchoice
          all_goals first | contradiction | (cases Option.some.inj hchoice; rfl)
      | collection payload ledger clock cutoff outcome =>
          cases outcome <;>
            simp only [hc, ReferenceCollectionSegmentExtraction.choiceOfCut] at hchoice
          all_goals first | contradiction | (cases Option.some.inj hchoice; rfl)
      | invalidCollectionCutoff =>
          simp only [hc, ReferenceCollectionSegmentExtraction.choiceOfCut] at hchoice
          contradiction
      | dagger =>
          simp only [hc, ReferenceCollectionSegmentExtraction.choiceOfCut] at hchoice
          contradiction

private theorem collection_tail_span
    (x : RoundInput p rate) (c : ReferenceCollectionSegmentExtraction.Choice rate)
    (hchoice : ReferenceCollectionSegmentExtraction.choice x = some c)
    (hspan : ∀ a cut current, c.preLedger.cutoffRegisters a = some cut →
      c.preLedger.currentRegisters a = some current → c.preLedger.increment a ≤
        4 * rate.n * (min c.preLedger.cursor c.preLedger.freezeAt - c.preLedger.cutoff))
    (hacceptedSpan : ∀ i U, AcceptedUp x i U →
      ∀ started decoded recording bank,
      CoordinatorRecorderComplementBridge.run
        (collectionRecordingInput (prepare x) c.payload c.started c.weights) = some recording →
      startRound c.preLedger (x.time.val + 1) (collectionEnabled c.preLedger x.time)
        (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) = .success started →
      (receiveUp (prepare x) started).result = .success (decoded, bank) →
      decoded.increment (started.assignment.arm i) ≤
        4 * rate.n * (min (x.time.val + 2) c.preLedger.freezeAt - c.preLedger.cutoff)) :
    match (collectionPostChoice (prepare x) c.payload c.preLedger c.started c.weights).configuration with
    | .collection P final _ =>
        P = c.payload ∧ final.cursor = x.time.val + 2 ∧
        final.cutoff = c.preLedger.cutoff ∧ final.freezeAt = c.preLedger.freezeAt ∧
        final.baseScore = c.preLedger.baseScore ∧ final.assignment = c.preLedger.assignment ∧
        final.sigma = c.preLedger.sigma ∧
        ∀ a cut current, final.cutoffRegisters a = some cut →
          final.currentRegisters a = some current → final.increment a ≤
            4 * rate.n * (min final.cursor final.freezeAt - final.cutoff)
    | _ => True := by
  unfold collectionPostChoice
  cases hrecord : CoordinatorRecorderComplementBridge.run
      (collectionRecordingInput (prepare x) c.payload c.started c.weights) with
  | none => trivial
  | some recording =>
      dsimp only
      cases hstart : startRound c.preLedger (x.time.val + 1)
          (collectionEnabled c.preLedger x.time)
          (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) with
      | invalid => trivial
      | rejected bad => trivial
      | success started =>
          dsimp only
          unfold collectionFinish
          have hdecode := ReferenceCollectionSegmentExtraction.receiveUp_decode_result x started
          cases hreceive : (receiveUp (prepare x) started).result with
          | invalid => trivial
          | success pair | rejected pair =>
              rcases pair with ⟨decoded, bank⟩
              simp only [hreceive] at hdecode ⊢
              cases hfinish : finishRound decoded with
              | invalid => trivial
              | rejected bad => trivial
              | success finished =>
                  dsimp only
                  cases hclock : CoordinatorPhaseClock.finishRound p rate.eta.val x.time
                      c.started.clock finished.pending x.row with
                  | error reason => trivial
                  | ok clockFinished =>
                      dsimp only
                      let input := ReferenceCollectionSegmentExtraction.inputOf
                        x c.preLedger recording started
                      have hd : decodeUp started input.selectedFollower input.parsed =
                          .success decoded ∨ decodeUp started input.selectedFollower input.parsed =
                            .rejected decoded := by
                        first | exact Or.inl hdecode | exact Or.inr hdecode
                      refine ⟨rfl, checked_round_span c.preLedger started decoded finished input
                        hspan ?_ hstart hd hfinish⟩
                      intro U hparsed hsuccess
                      have hreception : (receiveUp (prepare x) started).result ≠ .invalid := by
                        rw [hreceive]; intro h; cases h
                      have heffective : ReferenceCollectionSegmentExtraction.effectiveParse x started =
                          some U := hparsed
                      have hsRaw : decodeUp started (upSenderIndex x) (some U) =
                          .success decoded := hsuccess
                      have hrealReceive : (receiveUp (prepare x) started).result =
                          .success (decoded, CoordinatorUpReception.decoderBankAfter
                            (ReferenceUpReception.receptionInputAtRow rate x.row
                              (upInputs (prepare x) started) x.time)) := by
                        rw [ReferenceCollectionSegmentExtraction.receiveUp_filtered x started
                          (ReferenceCollectionSegmentExtraction.receiveUp_input_check x started hreception),
                          heffective, hsRaw]
                        rfl
                      have ha : AcceptedUp x (upSenderIndex x) U := by
                        exact ⟨⟨c.payload, c.preLedger, c.started, c.weights⟩, recording,
                          started, decoded, _, choice_executed_tail x c hchoice,
                          hrecord, hstart, hrealReceive, heffective, rfl⟩
                      exact hacceptedSpan _ U ha started decoded recording _
                        hrecord hstart hrealReceive

private theorem live_tail_no_collection
    (x : RoundInput p rate) (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r) (base : Fin (p.m - 1) → ℕ)
    (started : CoordinatorPhaseClock.StartRoundResult p) :
    match (livePostChoice (prepare x) r q base started).configuration with
    | .collection _ _ _ => False
    | _ => True := by
  unfold livePostChoice
  cases hr : CoordinatorRecorderComplementBridge.run (liveRecordingInput (prepare x) r started) with
  | none => trivial
  | some recording =>
      dsimp only
      cases hs : CoordinatorLiveServiceFinish.servicePass r q recording with
      | error reason => trivial
      | ok serviced =>
          dsimp only
          cases hc : CoordinatorLocalArmChoice.confirmationUpdate r.payload started.pending
              (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
              x.time x.row (prepare x).coordinatorObservation with
          | none => trivial
          | some pending =>
              dsimp only
              cases hf : CoordinatorPhaseClock.finishRound p rate.eta.val x.time
                  started.clock pending x.row with
              | error reason => trivial
              | ok finished => trivial

private theorem complete_tail_span
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (c : ReferenceCollectionSegmentExtraction.Choice rate)
    (hchoice : ReferenceCollectionSegmentExtraction.choice
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val].input = some c)
    (hspan : ∀ a cut current, c.preLedger.cutoffRegisters a = some cut →
      c.preLedger.currentRegisters a = some current → c.preLedger.increment a ≤
        4 * rate.n * (min c.preLedger.cursor c.preLedger.freezeAt - c.preLedger.cutoff)) :
    let x := (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val].input
    match (collectionPostChoice (prepare x) c.payload c.preLedger c.started c.weights).configuration with
    | .collection P final _ =>
        P = c.payload ∧ final.cursor = x.time.val + 2 ∧
        final.cutoff = c.preLedger.cutoff ∧ final.freezeAt = c.preLedger.freezeAt ∧
        final.baseScore = c.preLedger.baseScore ∧ final.assignment = c.preLedger.assignment ∧
        final.sigma = c.preLedger.sigma ∧
        ∀ a cut current, final.cutoffRegisters a = some cut →
          final.currentRegisters a = some current → final.increment a ≤
            4 * rate.n * (min final.cursor final.freezeAt - final.cutoff)
    | _ => True := by
  let x := (ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h)[k.val].input
  have ht := collection_tail_span x c hchoice hspan (by
    intro i U ha started decoded recording bank hr hs hd
    obtain ⟨b, j, F, mu, started', decoded', bank', recording', past, current,
      _hbj, _hjk, _hbirth, _hbase, _hretained, _hinput, _hdown, _hS, _hq,
      hr', hs', hd', _hfiltered, _hdecode, _hcut, _hcursor, _hfreeze,
      _hincrement, _hgamma, hbound⟩ :=
      accepted_up_decoded_increment_span rate rewards C_star C_h source k c hchoice i U ha
    have hrecordEq : recording' = recording := Option.some.inj (hr'.symm.trans hr)
    subst recording'
    have hstartEq : started' = started := by
      injection hs'.symm.trans hs
    subst started'
    have hpair : (decoded', bank') = (decoded, bank) := by
      injection hd'.symm.trans hd
    have hdecodedEq : decoded' = decoded := congrArg Prod.fst hpair
    subst decoded'
    exact hbound)
  exact ht

private theorem coordinator_round_span
    (x : RoundInput p rate)
    (hcollection : ∀ P l saved, x.state.coordinator = .collection P l saved →
      ∀ a cut current, l.cutoffRegisters a = some cut → l.currentRegisters a = some current →
        l.increment a ≤ 4 * rate.n * (min l.cursor l.freezeAt - l.cutoff))
    (htail : ∀ (c : ReferenceCollectionSegmentExtraction.Choice rate),
      ReferenceCollectionSegmentExtraction.choice x = some c →
      (∀ a cut current, c.preLedger.cutoffRegisters a = some cut →
        c.preLedger.currentRegisters a = some current → c.preLedger.increment a ≤
          4 * rate.n * (min c.preLedger.cursor c.preLedger.freezeAt - c.preLedger.cutoff)) →
      match (collectionPostChoice (prepare x) c.payload c.preLedger c.started c.weights).configuration with
      | .collection P final _ =>
          P = c.payload ∧ final.cursor = x.time.val + 2 ∧
          final.cutoff = c.preLedger.cutoff ∧ final.freezeAt = c.preLedger.freezeAt ∧
          final.baseScore = c.preLedger.baseScore ∧ final.assignment = c.preLedger.assignment ∧
          final.sigma = c.preLedger.sigma ∧
          ∀ a cut current, final.cutoffRegisters a = some cut →
            final.currentRegisters a = some current → final.increment a ≤
              4 * rate.n * (min final.cursor final.freezeAt - final.cutoff)
      | _ => True) :
    match (prepare x).observeCoordinator.configuration with
    | .collection P final _ =>
        ∃ c : ReferenceCollectionSegmentExtraction.Choice rate,
          ReferenceCollectionSegmentExtraction.choice x = some c ∧
          P = c.payload ∧ final.cursor = x.time.val + 2 ∧
          final.cutoff = c.preLedger.cutoff ∧ final.freezeAt = c.preLedger.freezeAt ∧
          final.baseScore = c.preLedger.baseScore ∧ final.assignment = c.preLedger.assignment ∧
          final.sigma = c.preLedger.sigma ∧
          ∀ a cut current, final.cutoffRegisters a = some cut →
            final.currentRegisters a = some current → final.increment a ≤
              4 * rate.n * (min final.cursor final.freezeAt - final.cutoff)
    | _ => True := by
  classical
  by_cases hselected : (prepare x).coordinator.selection = none
  · simp only [PreparedRound.observeCoordinator, dite_eq_left hselected]
    cases (prepare x).coordinator <;> trivial
  · simp only [PreparedRound.observeCoordinator, dite_eq_right hselected]
    have hactual : (prepare x).coordinator = dispatch x := rfl
    cases hconfiguration : x.state.coordinator with
    | first =>
        have hcut : (prepare x).coordinator =
            .first (CoordinatorRoundDispatch.dispatchFirst (firstInput x)) := by
          rw [hactual]
          simp only [dispatch, hconfiguration, CoordinatorRoundDispatch.dispatch]
          rfl
        rw [hcut]
        cases ho : CoordinatorRoundDispatch.dispatchFirst (firstInput x)
        all_goals try trivial
        case chosen installed selected =>
          have ht := live_tail_no_collection x installed.registers installed.ownedRegisters
            installed.followerBaseScore installed.startRoundResult
          split at ht <;> simp_all only
    | live r q base =>
        have hcut : (prepare x).coordinator = .live r q base
            (CoordinatorRoundDispatch.dispatchLive (liveInput x r q base)) := by
          rw [hactual]
          simp only [dispatch, hconfiguration, CoordinatorRoundDispatch.dispatch]
          rfl
        rw [hcut]
        cases ho : CoordinatorRoundDispatch.dispatchLive (liveInput x r q base)
        all_goals try trivial
        case continuingChosen dispatched hstart hno selected =>
          have ht := live_tail_no_collection x (liveRegistersAt r x.time)
            (liveOwnedAt r q x.time) base dispatched.startResult
          split at ht <;> simp_all only
        case cutoffChosen dispatched hstart ledger hinit hcandidate hdomains hclock
            hpending hno selected =>
          let c : ReferenceCollectionSegmentExtraction.Choice rate :=
            ⟨r.payload, sharedLedger ledger, dispatched.startResult,
              (liveRegistersAt r x.time).complementWeights,
              some (ReferenceCollectionSegmentExtraction.cutoffInitializer
                (liveRegistersAt r x.time) (liveOwnedAt r q x.time) base x.time)⟩
          have hchoice : ReferenceCollectionSegmentExtraction.choice x = some c := by
            unfold ReferenceCollectionSegmentExtraction.choice
            rw [ite_eq_right hselected, hcut, ho]
            rfl
          have hz : ∀ a, c.preLedger.increment a = 0 := by
            intro a
            dsimp only [c]
            rw [(sharedLedger_fields ledger).2.2.2.2.2.2.2.2.1, hcandidate]
            rfl
          have ht := htail c hchoice (by intro a cut current _ _; rw [hz a]; exact Nat.zero_le _)
          change match (collectionPostChoice (prepare x) c.payload c.preLedger c.started c.weights).configuration with
            | .collection P final _ => _
            | _ => True
          cases he : (collectionPostChoice (prepare x) c.payload c.preLedger c.started c.weights).configuration <;>
            simp only [he] at ht ⊢
          exact ⟨c, hchoice, ht⟩
    | collection old ledger saved =>
        by_cases hcutoff : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
        · let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
          let clock := collectionClock old ledger saved cutoff
          have hcut : (prepare x).coordinator = .collection old ledger clock cutoff
              (CoordinatorRoundDispatch.dispatchCollection
                (collectionInput x old ledger clock cutoff)) := by
            rw [hactual]
            simp only [dispatch, hconfiguration, dite_eq_left hcutoff,
              CoordinatorRoundDispatch.dispatch]
            rfl
          rw [hcut]
          cases ho : CoordinatorRoundDispatch.dispatchCollection
              (collectionInput x old ledger clock cutoff)
          all_goals try trivial
          case continuing core snapshot hcontinue selected =>
            let c : ReferenceCollectionSegmentExtraction.Choice rate :=
              ⟨old, ledger, snapshot.clockStarted,
                CoordinatorCollectionInteractive.PreObservationInputs.weights
                  (collectionInput x old ledger clock cutoff)
                  snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq, none⟩
            have hchoice : ReferenceCollectionSegmentExtraction.choice x = some c := by
              unfold ReferenceCollectionSegmentExtraction.choice
              rw [ite_eq_right hselected, hcut, ho]
              rfl
            have ht := htail c hchoice (hcollection old ledger saved hconfiguration)
            change match (collectionPostChoice (prepare x) c.payload c.preLedger c.started c.weights).configuration with
              | .collection P final _ => _
              | _ => True
            cases he : (collectionPostChoice (prepare x) c.payload c.preLedger c.started c.weights).configuration <;>
              simp only [he] at ht ⊢
            exact ⟨c, hchoice, ht⟩
          case laterChosen core consistent started hstart instruction hinstruction output
              hlocal clockData installed selected =>
            have ht := live_tail_no_collection x installed.registers installed.ownedRegisters
              installed.retainedBaseScore started
            split at ht <;> simp_all only
        · have hcut : (prepare x).coordinator = .invalidCollectionCutoff := by
            rw [hactual]
            simp only [dispatch, hconfiguration, dite_eq_right hcutoff]
          rw [hcut]
          trivial
    | dagger =>
        have hcut : (prepare x).coordinator = .dagger := by
          rw [hactual]
          simp only [dispatch, hconfiguration]
        rw [hcut]
        trivial

private theorem connected_first_input
    {initial final : ReferenceActivePhysicalHorizon.State p rate}
    {records : List (RoundRecord (p := p) (rate := rate))}
    (hconnected : ReferenceActivePhysicalHorizon.Connected initial records final)
    (h : 0 < records.length) : records[0].input.state = initial := by
  cases records with
  | nil => simp only [List.length_nil] at h; omega
  | cons record rest => exact hconnected.1

private theorem connected_succ_input
    {initial final : ReferenceActivePhysicalHorizon.State p rate}
    {records : List (RoundRecord (p := p) (rate := rate))}
    (hconnected : ReferenceActivePhysicalHorizon.Connected initial records final)
    (n : ℕ) (h : n + 1 < records.length) :
    records[n + 1].input.state = records[n].output.next := by
  induction records generalizing initial n with
  | nil => simp only [List.length_nil] at h; omega
  | cons record rest ih =>
      cases n with
      | zero =>
          cases rest with
          | nil => simp only [List.length_cons, List.length_nil] at h; omega
          | cons next tail => exact hconnected.2.1
      | succ n => exact ih hconnected.2 n (by simp only [List.length_cons] at h; omega)

/-- All actual incoming collection ledgers and all collection successors obey
this clipped increment span on the complete original physical suffix. The
successor cursor includes the terminal endpoint after physical round T. -/
theorem complete_collection_input_output_increment_span
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h
    ∀ k : Fin R.length,
      (∀ P l saved, R[k.val].input.state.coordinator = .collection P l saved →
        l.cursor = R[k.val].input.time.val + 1 ∧
        ∀ a cut current, l.cutoffRegisters a = some cut → l.currentRegisters a = some current →
          l.increment a ≤ 4 * rate.n * (min l.cursor l.freezeAt - l.cutoff)) ∧
      (∀ P l saved, R[k.val].output.next.coordinator = .collection P l saved →
        l.cursor = R[k.val].input.time.val + 2 ∧
        ∀ a cut current, l.cutoffRegisters a = some cut → l.currentRegisters a = some current →
          l.increment a ≤ 4 * rate.n * (min l.cursor l.freezeAt - l.cutoff)) := by
  classical
  dsimp only
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
  intro k
  cases hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h with
  | none =>
      have hlength := k.isLt
      simp only [ReferenceCompletePhysicalHistory.completeSuffixRecords,
        hlaunch, dite_true, List.length_nil] at hlength
      omega
  | some active =>
      have hc := (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
        rate source rewards C_star C_h).mp (by rw [hlaunch]; rfl)
      let initial := ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hc
      let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
        rate source rewards C_star C_h hc
      have hcanonical := ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
        rate source rewards C_star C_h hc
      have hconnected := ReferenceCompletePhysicalHistory.completeSuffix_connected_on_launch
        rate source rewards C_star C_h initial hcanonical
      have hstep : ∀ (n : Fin R.length),
          (∀ P l saved, R[n.val].input.state.coordinator = .collection P l saved →
            ∀ a cut current, l.cutoffRegisters a = some cut →
              l.currentRegisters a = some current → l.increment a ≤
                4 * rate.n * (min l.cursor l.freezeAt - l.cutoff)) →
          ∀ P l saved, R[n.val].output.next.coordinator = .collection P l saved →
            l.cursor = R[n.val].input.time.val + 2 ∧
            ∀ a cut current, l.cutoffRegisters a = some cut →
              l.currentRegisters a = some current → l.increment a ≤
                4 * rate.n * (min l.cursor l.freezeAt - l.cutoff) := by
        intro n hin P l saved hout
        have ht := coordinator_round_span R[n.val].input hin (by
          intro c hchoice hspan
          exact complete_tail_span rate rewards C_star C_h source n c hchoice hspan)
        have heq : R[n.val].output.next.coordinator =
            (prepare R[n.val].input).observeCoordinator.configuration := by
          rw [R[n.val].output_eq]
          rfl
        rw [← heq, hout] at ht
        obtain ⟨c, _hchoice, hframes⟩ := ht
        exact ⟨hframes.2.1, hframes.2.2.2.2.2.2.2⟩
      have hfold : ∀ n (hn : n < R.length),
          (∀ P l saved, R[n].input.state.coordinator = .collection P l saved →
            l.cursor = R[n].input.time.val + 1 ∧
            ∀ a cut current, l.cutoffRegisters a = some cut →
              l.currentRegisters a = some current → l.increment a ≤
                4 * rate.n * (min l.cursor l.freezeAt - l.cutoff)) ∧
          (∀ P l saved, R[n].output.next.coordinator = .collection P l saved →
            l.cursor = R[n].input.time.val + 2 ∧
            ∀ a cut current, l.cutoffRegisters a = some cut →
              l.currentRegisters a = some current → l.increment a ≤
                4 * rate.n * (min l.cursor l.freezeAt - l.cutoff)) := by
        intro n
        induction n with
        | zero =>
            intro hn
            have hstate := connected_first_input hconnected hn
            have hin : ∀ P l saved, R[0].input.state.coordinator = .collection P l saved →
                l.cursor = R[0].input.time.val + 1 ∧
                ∀ a cut current, l.cutoffRegisters a = some cut →
                  l.currentRegisters a = some current → l.increment a ≤
                    4 * rate.n * (min l.cursor l.freezeAt - l.cutoff) := by
              intro P l saved hconfiguration
              rw [hstate, seed.coordinatorFirst] at hconfiguration
              cases hconfiguration
            exact ⟨hin, hstep ⟨0, hn⟩ (by intro P l saved he; exact (hin P l saved he).2)⟩
        | succ n ih =>
            intro hn
            have hnprev : n < R.length := by omega
            obtain ⟨_hin, hout⟩ := ih hnprev
            have hstate := connected_succ_input hconnected n hn
            have htime : R[n + 1].input.time.val = R[n].input.time.val + 1 := by
              have hp := ReferenceAssignmentFollowerMassSteps.complete_record_time
                rate rewards C_star C_h source ⟨n, hnprev⟩
              have hn' := ReferenceAssignmentFollowerMassSteps.complete_record_time
                rate rewards C_star C_h source ⟨n + 1, hn⟩
              change R[n].input.time.val = _ + n at hp
              change R[n + 1].input.time.val = _ + (n + 1) at hn'
              omega
            have hin : ∀ P l saved, R[n + 1].input.state.coordinator = .collection P l saved →
                l.cursor = R[n + 1].input.time.val + 1 ∧
                ∀ a cut current, l.cutoffRegisters a = some cut →
                  l.currentRegisters a = some current → l.increment a ≤
                    4 * rate.n * (min l.cursor l.freezeAt - l.cutoff) := by
              intro P l saved he
              rw [hstate] at he
              have ht := hout P l saved he
              rw [htime]
              exact ht
            exact ⟨hin, hstep ⟨n + 1, hn⟩ (by
              intro P l saved he
              exact (hin P l saved he).2)⟩
      exact hfold k.val k.isLt

private theorem complete_record_clocks
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length) :
    let record := (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val]
    let J := ActualInitializationPhysicalStep.selectedRowIndex p source
    ReferenceCoordinatorClockDomains.clockAt source.1.2 J record.input.time.val record.input.state ∧
      ReferenceCoordinatorClockDomains.clockAt source.1.2 J
        (record.input.time.val + 1) record.output.next := by
  classical
  cases hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h with
  | none =>
      have hlength := k.isLt
      simp only [ReferenceCompletePhysicalHistory.completeSuffixRecords, hlaunch,
        dite_true, List.length_nil] at hlength
      omega
  | some active =>
      have hc := (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
        rate source rewards C_star C_h).1 (by rw [hlaunch]; rfl)
      let initial := ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hc
      have hcanonical := ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
        rate source rewards C_star C_h hc
      let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
        rate source rewards C_star C_h hc
      have hrecords := ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
        rate source rewards C_star C_h initial hcanonical
      have hseed : ReferenceCoordinatorClockDomains.clockAt source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source)
          (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
          initial := by
        have hfirst : initial.coordinator = .first := seed.coordinatorFirst
        simp only [ReferenceCoordinatorClockDomains.clockAt, hfirst]
      have hclock := ReferenceRunClockPreservation.run_clockAt initial source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
        (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
        (p.T - ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
        (by have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T
              rate source rewards C_star C_h; omega)
        (ReferenceCompletePhysicalHistory.activeMode_of_launch_eq_some
          rate source rewards C_star C_h initial hcanonical) hseed
      have hrecord := hclock.2.2.2
        ((ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h)[k.val])
        (by rw [← hrecords]; exact List.getElem_mem k.isLt)
      exact ⟨hrecord.1, hrecord.2.1⟩

/-- Actual incoming endpoint, with the very same retained installation, base,
source first cutoff and grid boundary. No restriction on later initial queues
or base scores is added. -/
theorem complete_collection_input_increment_span
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (P : Payload rate) (l : Ledger rate) (saved : Option (Fin p.T × Bool))
    (hinput : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val].input.state.coordinator = .collection P l saved) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
    let J := ActualInitializationPhysicalStep.selectedRowIndex p source
    let bits := FollowerCutoffScan.completeRowProposalBit p rate.eta.val (source.1.2 J)
    ∃ b : Fin R.length, b.val < k.val ∧
      ReferenceAssignmentPayloadPersistence.InstallationBirth R[b.val] P ∧
      ReferenceAssignmentCollectionMassSteps.installedBaseScore R[b.val] = some l.baseScore ∧
      l.assignment.arm = P.assignment.assigned ∧ l.sigma = P.sigma.val + 1 ∧
      l.cutoff = FollowerCutoffScan.firstCutoff p rate.eta.val P.sigma bits ∧
      l.freezeAt = FollowerCutoffScan.gridBoundary p rate.eta.val P.sigma ∧
      1 ≤ l.cutoff ∧ l.cutoff ≤ l.freezeAt ∧ l.freezeAt ≤ p.T + 1 ∧
      l.cutoff ≤ l.cursor ∧ l.cursor = R[k.val].input.time.val + 1 ∧
      ∀ a cut current, l.cutoffRegisters a = some cut → l.currentRegisters a = some current →
        l.increment a ≤ 4 * rate.n * (min l.cursor l.freezeAt - l.cutoff) := by
  have hb := ReferenceAssignmentRetainedBirthProvenance.complete_coordinator_retained_birth
    rate rewards C_star C_h source k
  dsimp only at hb ⊢
  rw [hinput] at hb
  obtain ⟨⟨b, hbk, hbirth, hbase⟩, hassignment, hsigma, hcutoff⟩ := hb
  have hspan := (complete_collection_input_output_increment_span
    rate rewards C_star C_h source k).1 P l saved hinput
  obtain ⟨cutoff, hcut, _hsigma, _horder, htime, hcutFreeze, hfreeze, hterminal⟩ :=
    ReferenceRunClockPreservation.collection_clockAt_cutoff_geometry source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) _ _ P l saved hinput
      (complete_record_clocks rate rewards C_star C_h source k).1
  have hbase' : ReferenceAssignmentCollectionMassSteps.installedBaseScore
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h)[b.val] =
        some l.baseScore := by
    unfold ReferenceAssignmentCollectionMassSteps.installedBaseScore
    split at hbase <;> simp_all only
  refine ⟨b, hbk, hbirth, hbase',
    hassignment, hsigma, hcutoff, hfreeze, ?_, ?_, hterminal, ?_, hspan⟩
  · omega
  · omega
  · have hc := hspan.1
    omega

/-- Actual successor endpoint, including cursor T+1. Its collection payload,
base and first cutoff come from the same earlier installation that supplied
the actual choice and replay. This asserts a bound only when that ledger is
present in the computed successor. -/
theorem complete_collection_successor_increment_span
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (P : Payload rate) (l : Ledger rate) (saved : Option (Fin p.T × Bool))
    (houtput : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val].output.next.coordinator = .collection P l saved) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
    let J := ActualInitializationPhysicalStep.selectedRowIndex p source
    let bits := FollowerCutoffScan.completeRowProposalBit p rate.eta.val (source.1.2 J)
    ∃ b : Fin R.length, b.val < k.val ∧
      ReferenceAssignmentPayloadPersistence.InstallationBirth R[b.val] P ∧
      ReferenceAssignmentCollectionMassSteps.installedBaseScore R[b.val] = some l.baseScore ∧
      l.assignment.arm = P.assignment.assigned ∧ l.sigma = P.sigma.val + 1 ∧
      l.cutoff = FollowerCutoffScan.firstCutoff p rate.eta.val P.sigma bits ∧
      l.freezeAt = FollowerCutoffScan.gridBoundary p rate.eta.val P.sigma ∧
      1 ≤ l.cutoff ∧ l.cutoff ≤ l.freezeAt ∧ l.freezeAt ≤ p.T + 1 ∧
      l.cutoff ≤ l.cursor ∧ l.cursor = R[k.val].input.time.val + 2 ∧
      ∀ a cut current, l.cutoffRegisters a = some cut → l.currentRegisters a = some current →
        l.increment a ≤ 4 * rate.n * (min l.cursor l.freezeAt - l.cutoff) := by
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
  let x := R[k.val].input
  have ht := coordinator_round_span x (by
    intro old ledger proposal hin
    exact ((complete_collection_input_output_increment_span
      rate rewards C_star C_h source k).1 old ledger proposal hin).2) (by
    intro c hchoice hspan
    exact complete_tail_span rate rewards C_star C_h source k c hchoice hspan)
  have heq : R[k.val].output.next.coordinator = (prepare x).observeCoordinator.configuration := by
    rw [R[k.val].output_eq]
    rfl
  rw [← heq, houtput] at ht
  obtain ⟨c, hchoice, hP, hcursor, hcutoff, _hfreeze, hbase, hassignment, hsigma, hspan⟩ := ht
  obtain ⟨b, hbk, hbirth, ha, hs, hu, hb⟩ :=
    ReferenceAssignmentRetainedBirthProvenance.complete_collection_choice_birth_provenance
      rate rewards C_star C_h source k c hchoice
  obtain ⟨cutoff, hcut, _hsigma, _horder, htime, hcutFreeze, hfreeze, hterminal⟩ :=
    ReferenceRunClockPreservation.collection_clockAt_cutoff_geometry source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) _ _ P l saved houtput
      (complete_record_clocks rate rewards C_star C_h source k).2
  dsimp only at hbirth ha hs hu hb ⊢
  refine ⟨b, hbk, ?_, ?_, ?_, ?_, ?_, hfreeze, ?_, ?_, hterminal, ?_, hcursor, hspan⟩
  · rw [hP]
    exact hbirth
  · rw [hbase]
    unfold ReferenceAssignmentCollectionMassSteps.installedBaseScore
    split at hb <;> simp_all only
  · rw [hassignment, ha, hP]
  · rw [hsigma, hs, hP]
  · rw [hcutoff, hu, hP]
  · omega
  · omega
  · change cutoff.val + 1 ≤ x.time.val + 1 at htime
    change l.cursor = x.time.val + 2 at hcursor
    omega

end Bandits.Support.ReferenceCompleteCollectionIncrementSpan

end
