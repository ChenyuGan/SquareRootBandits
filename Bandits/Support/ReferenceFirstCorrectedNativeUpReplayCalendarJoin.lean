/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCorrectedNativeUpComputedPrefixObservation

import Mathlib.Tactic

/-!
# Native UP prefixes on the first corrected collection calendar

This module identifies queue prefixes returned by the literal native UP
observer on the original first corrected source run.  Its source-facing result
is deterministic and does not use a collection probability extension.

Sources: ZIP4 `04_slow_fast_learner.tex:157-187,256-290`,
`06_interruptions.tex:192-233,246-299`, and
`appendix_a_local_protocol.tex:28-64`.
-/

@[expose] public section
noncomputable section

open Bandits.Support
open ConstructorDimensions
open ReferenceActivePhysicalStep
open ReferenceActivePhysicalHorizon
open CoordinatorCollectionLedger
open ReferenceCollectionPhaseHistory
open ReferenceCollectionSegmentExtraction
open ReferenceFirstCollectionCorrectedSliceNumericalPrefix
open ReferenceFirstCorrectedNativeUpComputedPrefixObservation

namespace Bandits.Support.ReferenceFirstCorrectedNativeUpReplayCalendarJoin

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ)

/-- A nonempty observer result has reached every guard before native queue
replay.  The returned records are the actual prefix and terminal records read
from the diagnostic ledger, and the returned queue is their literal replay
endpoint. -/
private theorem decodePrefixQueue?_some_guards
    (l : ReferenceActivePhysicalStep.Ledger rate) (i : Fin (p.m - 1))
    (M : OrdinaryMessageCodec.UpRecord
      (CoordinatorCollectionLedger.codecParams p rate.eta.val)) (k : ℕ)
    (a : Fin p.K) (q : ℕ)
    (hdecoded : decodePrefixQueue? rate l i (some M) k = some (a, q)) :
    ∃ (_hinput : validLedgerCheck l = true ∧ l.phase = .started ∧
        1 ≤ l.cutoff ∧ l.cutoff ≤ l.cursor ∧ l.cursor ≤ p.T)
      ,
      acceptUpCheck l i M = true ∧
      l.currentRegisters (l.assignment.arm i) = none ∧
      l.cutoffRegisters (l.assignment.arm i) = none := by
  classical
  unfold decodePrefixQueue? at hdecoded
  by_cases hinput : validLedgerCheck l = true ∧ l.phase = .started ∧
      1 ≤ l.cutoff ∧ l.cutoff ≤ l.cursor ∧ l.cursor ≤ p.T
  · rw [dite_eq_left hinput] at hdecoded
    by_cases haccepted : acceptUpCheck l i M = true
    · simp only [haccepted] at hdecoded
      by_cases hcurrent : l.currentRegisters (l.assignment.arm i) = none
      · by_cases hcutoff : l.cutoffRegisters (l.assignment.arm i) = none
        · have hunknown : l.currentRegisters (l.assignment.arm i) = none ∧
              l.cutoffRegisters (l.assignment.arm i) = none := ⟨hcurrent, hcutoff⟩
          rw [dite_eq_left hunknown] at hdecoded
          exact ⟨hinput, haccepted, hcurrent, hcutoff⟩
        · simp [hcutoff] at hdecoded
      · simp [hcurrent] at hdecoded
    · simp [haccepted] at hdecoded
  · simp [hinput] at hdecoded

/-- A present guarded decoder result identifies the exact records read by the
literal replay and its requested take-prefix endpoint. -/
private theorem decodePrefixQueue?_some_replay_data
    (l : ReferenceActivePhysicalStep.Ledger rate) (i : Fin (p.m - 1))
    (M : OrdinaryMessageCodec.UpRecord
      (CoordinatorCollectionLedger.codecParams p rate.eta.val)) (k : ℕ)
    (a : Fin p.K) (q : ℕ)
    (hdecoded : decodePrefixQueue? rate l i (some M) k = some (a, q)) :
    ∃ (past : List (Bool × ℕ)) (current : Bool × ℕ),
      replayRecords? l (l.assignment.arm i)
        (calendarIndices p.T (l.cutoff - 1) (l.cursor - l.cutoff) (by
          have hinput := decodePrefixQueue?_some_guards rate l i M k a q hdecoded
          rcases hinput with ⟨hinput, _, _, _⟩
          omega)) = some past ∧
      replayRecords? l (l.assignment.arm i)
        [⟨l.cursor - 1, by
          have hinput := decodePrefixQueue?_some_guards rate l i M k a q hdecoded
          rcases hinput with ⟨hinput, _, _, _⟩
          omega⟩] = some [current] ∧
      (decide ((past ++ [current]).length ≤ p.T) &&
        (past ++ [current]).all (fun record => decide (record.2 ≤ D p))) = true ∧
      k ≤ (past ++ [current]).length ∧
      q = (QueueReplay.replay (4 * rate.n) (0, M.val.q)
        ((past ++ [current]).take k)).2 := by
  classical
  obtain ⟨hinput, haccepted, hcurrentNone, hcutoffNone⟩ :=
    decodePrefixQueue?_some_guards rate l i M k a q hdecoded
  have hdomain : validLedgerCheck l = true ∧ l.phase = .started ∧
      1 ≤ l.cutoff ∧ l.cutoff ≤ l.cursor ∧ l.cursor ≤ p.T := hinput
  have hindices : (l.cutoff - 1) + (l.cursor - l.cutoff) ≤ p.T := by omega
  have hlast : l.cursor - 1 < p.T := by omega
  let indices := calendarIndices p.T (l.cutoff - 1) (l.cursor - l.cutoff) hindices
  let last : Fin p.T := ⟨l.cursor - 1, hlast⟩
  unfold decodePrefixQueue? at hdecoded
  rw [dite_eq_left hdomain] at hdecoded
  simp only [haccepted, dite_eq_left (show
    l.currentRegisters (l.assignment.arm i) = none ∧
      l.cutoffRegisters (l.assignment.arm i) = none from
        ⟨hcurrentNone, hcutoffNone⟩)] at hdecoded
  change (match replayRecords? l (l.assignment.arm i) indices,
      replayRecords? l (l.assignment.arm i) [last] with
    | some past, some [current] =>
        if decide ((past ++ [current]).length ≤ p.T) &&
            (past ++ [current]).all (fun record => decide (record.2 ≤ D p)) then
          if k ≤ (past ++ [current]).length then
            some (l.assignment.arm i,
              (QueueReplay.replay (4 * rate.n) (0, M.val.q)
                ((past ++ [current]).take k)).2)
          else none
        else none
    | _, _ => none) = some (a, q) at hdecoded
  cases hpast : replayRecords? l (l.assignment.arm i) indices with
  | none => simp [hpast] at hdecoded
  | some past =>
      cases hcurrent : replayRecords? l (l.assignment.arm i) [last] with
      | none => simp [hpast, hcurrent] at hdecoded
      | some values =>
          cases values with
          | nil => simp [hpast, hcurrent] at hdecoded
          | cons current tail =>
              cases tail with
              | nil =>
                  simp only [hpast, hcurrent] at hdecoded
                  split at hdecoded
                  · split at hdecoded
                    · simp only [Option.some.injEq, Prod.mk.injEq] at hdecoded
                      rcases hdecoded with ⟨ha, hq⟩
                      subst a
                      exact ⟨past, current, rfl, rfl, by assumption,
                        by assumption, hq.symm⟩
                    · contradiction
                  · contradiction
              | cons _ _ => simp [hpast, hcurrent] at hdecoded

/-- Expand a present first corrected observer branch down to the actual
physical record, its retained UP diagnostic, the same-row filtered word, and
the exact guarded replay value.  This characterization has no acceptance or
queue-truth premise: the true parse and all pre-replay checks are consequences
of the literal returned `some`. -/
theorem firstCell_nativeUp_observer_replay_data
    (u t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (_hz : z ∈ correctedCell rate rewards C_star C_h u t)
    (j k : ℕ) (a : Fin p.K) (q : ℕ)
    (hqueue : firstPrefixQueueAt rate rewards C_star C_h z j k = some (a, q)) :
    let R := sourceRecords rate rewards C_star C_h z
    let e := birthIndex rate rewards C_star C_h z + 1 +
      (liveTail rate rewards C_star C_h z).length
    ∃ (entry : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (seg : ReferenceCollectionSegmentExtraction.Segment rate)
      (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (diagnostic : ReferenceActivePhysicalStep.UpDiagnostic p rate)
      (message : OrdinaryMessageCodec.UpRecord
        (CoordinatorCollectionLedger.codecParams p rate.eta.val)),
      validLedgerCheck diagnostic.input.ledger = true ∧
        diagnostic.input.ledger.phase = .started ∧
        1 ≤ diagnostic.input.ledger.cutoff ∧
        diagnostic.input.ledger.cutoff ≤ diagnostic.input.ledger.cursor ∧
        diagnostic.input.ledger.cursor ≤ p.T ∧
      R[e]? = some entry ∧
      ReferenceCollectionPhaseHistory.cutoffChosen entry.input = true ∧
      segmentAt R e = some seg ∧ j ≤ seg.records.length ∧
      R[e + j]? = some record ∧
      record.output.coordinator.up = some diagnostic ∧
      CoordinatorUpReception.parseDecoderOutput
        (ReferenceUpReception.filterRawByExpected diagnostic.raw diagnostic.expected) =
          some message ∧
      acceptUpCheck diagnostic.input.ledger diagnostic.input.selectedFollower message = true ∧
      diagnostic.input.ledger.currentRegisters
        (diagnostic.input.ledger.assignment.arm diagnostic.input.selectedFollower) = none ∧
      diagnostic.input.ledger.cutoffRegisters
        (diagnostic.input.ledger.assignment.arm diagnostic.input.selectedFollower) = none ∧
      decodePrefixQueue? rate diagnostic.input.ledger diagnostic.input.selectedFollower
        (some message) k = some (a, q) := by
  classical
  dsimp only
  let R := sourceRecords rate rewards C_star C_h z
  let e := birthIndex rate rewards C_star C_h z + 1 +
    (liveTail rate rewards C_star C_h z).length
  change (match R[e]? with
    | none => none
    | some entry =>
        if ReferenceCollectionPhaseHistory.cutoffChosen entry.input then
          match segmentAt R e with
          | none => none
          | some seg' =>
              if j ≤ seg'.records.length then
                (R[e + j]?).bind fun record => recordPrefixQueue? rate record k
              else none
        else none) = some (a, q) at hqueue
  cases hentry : R[e]? with
  | none =>
      exact False.elim (by simp [hentry] at hqueue)
  | some entry =>
      by_cases hcut : ReferenceCollectionPhaseHistory.cutoffChosen entry.input
      · simp only [hentry, ite_eq_left hcut] at hqueue
        cases hsegment : segmentAt R e with
        | none =>
            exact False.elim (by simp [hsegment] at hqueue)
        | some seg =>
            simp only [hsegment] at hqueue
            by_cases hlength : j ≤ seg.records.length
            · simp only [ite_eq_left hlength] at hqueue
              cases hrecord : R[e + j]? with
              | none => exact False.elim (by simp [hrecord] at hqueue)
              | some record =>
                  simp only [hrecord, Option.bind_some] at hqueue
                  have hqueue' : recordPrefixQueue? rate record k = some (a, q) := hqueue
                  unfold recordPrefixQueue? at hqueue'
                  cases hdiagnostic : record.output.coordinator.up with
                  | none => exact False.elim (by simp [hdiagnostic] at hqueue')
                  | some diagnostic =>
                      simp only [hdiagnostic, Option.bind_some] at hqueue'
                      let filtered : Option (OrdinaryMessageCodec.UpRecord
                          (CoordinatorCollectionLedger.codecParams p rate.eta.val)) :=
                        CoordinatorUpReception.parseDecoderOutput (p := p)
                          (eta := rate.eta.val)
                          (ReferenceUpReception.filterRawByExpected
                            diagnostic.raw diagnostic.expected)
                      cases hparsed : filtered with
                      | none =>
                          exact False.elim (by
                            simp [decodePrefixQueue?, filtered, hparsed] at hqueue')
                      | some message =>
                          simp only [filtered, hparsed] at hqueue'
                          obtain ⟨hinput, haccepted, hcurrent, hcutoff⟩ :=
                            decodePrefixQueue?_some_guards rate diagnostic.input.ledger
                              diagnostic.input.selectedFollower message k a q hqueue'
                          obtain ⟨hvalid, hphase, hcutoffBound, hcursorBound, htimeBound⟩ := hinput
                          refine ⟨entry, seg, record, diagnostic, message,
                            hvalid, hphase, hcutoffBound, hcursorBound, htimeBound,
                            rfl, hcut, rfl, hlength, rfl, hdiagnostic,
                            ?_, haccepted, hcurrent, hcutoff, hqueue'⟩
                          simpa only [filtered] using hparsed
            · exact False.elim (by simp [hlength] at hqueue)
      · have hcutFalse :
            ReferenceCollectionPhaseHistory.cutoffChosen entry.input = false := by
          cases h : ReferenceCollectionPhaseHistory.cutoffChosen entry.input with
          | false => rfl
          | true => exact False.elim (hcut h)
        simp [hentry, hcutFalse] at hqueue

/-- The observer's present branch reads an actual past list and the current
terminal record from its diagnostic ledger.  Its returned value at `k` is
the unstopped replay of exactly that list's first `k` records. -/
theorem firstCell_nativeUp_observer_replay_records
    (u t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : z ∈ correctedCell rate rewards C_star C_h u t)
    (j k : ℕ) (a : Fin p.K) (q : ℕ)
    (hqueue : firstPrefixQueueAt rate rewards C_star C_h z j k = some (a, q)) :
    let R := sourceRecords rate rewards C_star C_h z
    let e := birthIndex rate rewards C_star C_h z + 1 +
      (liveTail rate rewards C_star C_h z).length
    ∃ (entry : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (seg : ReferenceCollectionSegmentExtraction.Segment rate)
      (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (diagnostic : ReferenceActivePhysicalStep.UpDiagnostic p rate)
      (message : OrdinaryMessageCodec.UpRecord
        (CoordinatorCollectionLedger.codecParams p rate.eta.val)),
      validLedgerCheck diagnostic.input.ledger = true ∧
      diagnostic.input.ledger.phase = .started ∧
      1 ≤ diagnostic.input.ledger.cutoff ∧
      diagnostic.input.ledger.cutoff ≤ diagnostic.input.ledger.cursor ∧
      diagnostic.input.ledger.cursor ≤ p.T ∧
      R[e]? = some entry ∧
      ReferenceCollectionPhaseHistory.cutoffChosen entry.input = true ∧
      segmentAt R e = some seg ∧ j ≤ seg.records.length ∧
      R[e + j]? = some record ∧
      record.output.coordinator.up = some diagnostic ∧
      CoordinatorUpReception.parseDecoderOutput
        (ReferenceUpReception.filterRawByExpected diagnostic.raw diagnostic.expected) =
          some message ∧
      acceptUpCheck diagnostic.input.ledger diagnostic.input.selectedFollower message = true ∧
      diagnostic.input.ledger.currentRegisters
        (diagnostic.input.ledger.assignment.arm diagnostic.input.selectedFollower) = none ∧
      diagnostic.input.ledger.cutoffRegisters
        (diagnostic.input.ledger.assignment.arm diagnostic.input.selectedFollower) = none ∧
      ∃ (hprefix : (diagnostic.input.ledger.cutoff - 1) +
          (diagnostic.input.ledger.cursor - diagnostic.input.ledger.cutoff) ≤ p.T)
        (hlast : diagnostic.input.ledger.cursor - 1 < p.T)
        (past : List (Bool × ℕ)) (current : Bool × ℕ),
        replayRecords? diagnostic.input.ledger
          (diagnostic.input.ledger.assignment.arm diagnostic.input.selectedFollower)
          (calendarIndices p.T (diagnostic.input.ledger.cutoff - 1)
            (diagnostic.input.ledger.cursor - diagnostic.input.ledger.cutoff) hprefix) =
              some past ∧
        replayRecords? diagnostic.input.ledger
          (diagnostic.input.ledger.assignment.arm diagnostic.input.selectedFollower)
          [⟨diagnostic.input.ledger.cursor - 1, hlast⟩] = some [current] ∧
        (decide ((past ++ [current]).length ≤ p.T) &&
          (past ++ [current]).all (fun record => decide (record.2 ≤ D p))) = true ∧
        k ≤ (past ++ [current]).length ∧
        q = (QueueReplay.replay (4 * rate.n) (0, message.val.q)
          ((past ++ [current]).take k)).2 := by
  classical
  dsimp only
  obtain ⟨entry, seg, record, diagnostic, message, hvalid, hphase,
    hcutPos, hcutCursor, hcursor, hentry, hcutoff, hsegment, hlength,
    hrecord, hdiagnostic, hparsed, haccepted, hcurrentNone, hcutoffNone,
    hdecoded⟩ :=
      firstCell_nativeUp_observer_replay_data rate rewards C_star C_h u t z hz j k a q hqueue
  obtain ⟨past, current, hpast, hcurrent, hdomains, hk, hq⟩ :=
    decodePrefixQueue?_some_replay_data rate diagnostic.input.ledger
      diagnostic.input.selectedFollower message k a q hdecoded
  have hprefix : (diagnostic.input.ledger.cutoff - 1) +
      (diagnostic.input.ledger.cursor - diagnostic.input.ledger.cutoff) ≤ p.T := by
    omega
  have hlast : diagnostic.input.ledger.cursor - 1 < p.T := by omega
  refine ⟨entry, seg, record, diagnostic, message, hvalid, hphase,
    hcutPos, hcutCursor, hcursor, hentry, hcutoff, hsegment, hlength,
    hrecord, hdiagnostic, hparsed, haccepted, hcurrentNone, hcutoffNone,
    hprefix, hlast, past, current, ?_, ?_, hdomains, hk, hq⟩
  · simpa only using hpast
  · simpa only using hcurrent

private theorem cutoffChosen_live_input
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (hcut : ReferenceCollectionPhaseHistory.cutoffChosen x = true) :
    ∃ reg owned base, x.state.coordinator = .live reg owned base := by
  cases hstate : x.state.coordinator with
  | first =>
      have hd := ReferenceActivePhysicalStep.dispatch_first x hstate
      simp [ReferenceCollectionPhaseHistory.cutoffChosen,
        ReferenceActivePhysicalStep.prepare, hd] at hcut
  | collection payload ledger proposal =>
      by_cases hvalid : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
      · let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
        let clock := ReferenceActivePhysicalStep.collectionClock payload ledger proposal cutoff
        let input := ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff
        cases hd : CoordinatorRoundDispatch.dispatch (.collection input) with
        | collection outcome =>
            have hdispatch : ReferenceActivePhysicalStep.dispatch x =
                .collection payload ledger clock cutoff outcome := by
              simp [ReferenceActivePhysicalStep.dispatch, hstate, hvalid,
                cutoff, clock, input, hd]
              rfl
            unfold ReferenceCollectionPhaseHistory.cutoffChosen at hcut
            change (match ReferenceActivePhysicalStep.dispatch x with
              | .live _ _ _ (.cutoffChosen _ _ _ _ _ _ _ _ _ _) => true
              | _ => false) = true at hcut
            rw [hdispatch] at hcut
            simp at hcut
      · simp [ReferenceCollectionPhaseHistory.cutoffChosen,
          ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch,
          hstate, hvalid] at hcut
  | dagger =>
      simp [ReferenceCollectionPhaseHistory.cutoffChosen,
        ReferenceActivePhysicalStep.prepare,
        ReferenceActivePhysicalStep.dispatch_dagger x hstate] at hcut
  | live reg owned base => exact ⟨reg, owned, base, rfl⟩

/-- The first cutoff record cannot produce a native UP diagnostic.  Therefore
every present observer branch is a positive offset into its initialized
collection segment. -/
theorem firstCell_nativeUp_observer_offset_positive
    (u t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : z ∈ correctedCell rate rewards C_star C_h u t)
    (j k : ℕ) (a : Fin p.K) (q : ℕ)
    (hqueue : firstPrefixQueueAt rate rewards C_star C_h z j k = some (a, q)) :
    1 ≤ j := by
  classical
  obtain ⟨entry, seg, record, d, message, _hvalid, _hphase, _hcutPos,
    _hcutCursor, _hcursor, hentry, hcut, _hsegment, _hlength, hrecord,
    hrecordDiag, hparsed, _haccepted, _hcurrent, _hcutoff, _hdecoded⟩ :=
      firstCell_nativeUp_observer_replay_data rate rewards C_star C_h u t z hz j k a q hqueue
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate z rewards C_star C_h
  let e := birthIndex rate rewards C_star C_h z + 1 +
    (liveTail rate rewards C_star C_h z).length
  change R[e]? = some entry at hentry
  change R[e + j]? = some record at hrecord
  by_contra hpositive
  have hj : j = 0 := by omega
  have hrecord' : R[e]? = some record := by simpa [hj] using hrecord
  have hsame : record = entry := Option.some.inj (hrecord'.symm.trans hentry)
  subst record
  have hrawSome : d.raw ≠ none := by
    intro hraw
    have hfiltered := hparsed
    have hfilter : ReferenceUpReception.filterRawByExpected d.raw d.expected = none := by
      rw [hraw]
      unfold ReferenceUpReception.filterRawByExpected
      split <;> rfl
    rw [hfilter] at hfiltered
    have hnone : CoordinatorUpReception.parseDecoderOutput (p := p)
        (eta := rate.eta.val)
        (none : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p))) = none := rfl
    rw [hnone] at hfiltered
    cases hfiltered
  have hentryBound : e < R.length :=
    (List.getElem?_eq_some_iff.mp hentry).1
  let ix : Fin R.length := ⟨e, hentryBound⟩
  have hget : R[ix.val]'ix.isLt = entry := by
    simpa [ix] using (List.getElem?_eq_some_iff.mp hentry).2
  obtain ⟨r, owned, base, hstate⟩ := cutoffChosen_live_input rate entry.input hcut
  have hstateIx :
      (R[ix.val]'ix.isLt).input.state.coordinator =
        .live r owned base := by
    rw [hget]
    exact hstate
  have hpost :=
    Bandits.Support.complete_live_cutoff_post_choice
      rate rewards C_star C_h z ix r owned base hstateIx
  dsimp only at hpost
  rcases hpost with ⟨hprepared, hbranch⟩
  rw [hget] at hbranch
  rw [hget] at hprepared
  generalize hd : CoordinatorRoundDispatch.dispatchLive
    (ReferenceActivePhysicalStep.liveInput entry.input r owned base) = outcome at hbranch
  cases outcome with
  | clockFailure => exact False.elim hbranch
  | initializerFailure => exact False.elim hbranch
  | localFailure => exact False.elim hbranch
  | continuingChosen =>
      rw [hd] at hprepared
      unfold ReferenceCollectionPhaseHistory.cutoffChosen at hcut
      rw [hprepared] at hcut
      simp at hcut
  | cutoffChosen dispatched hstart ledger hinit hledger hdomain hclock hpending hno selected =>
      simp only at hbranch
      rcases hbranch with ⟨_hcommand, _hclock, _hpending, _hno, _hinitialized,
        _hledger, _hsigma, _hcutoff, _hfreeze, _hlpending, _hcursor, _hinc,
        _hgamma, _hrawBuffer, _hphase, _hchoice, _hgrid, _harm, physical,
        _hphysical, _hphysicalPayload, _hphysicalPending, _hphysicalCutoff,
        _hphysicalStarted, _hphysicalArm, _hphysicalPendingStarted,
        _hphysicalCutoffStarted, _hphysicalChoice, recording, _hrecording,
        started, _hstartLedger, _hstarted, _hvalidStarted, _hstartedPhase,
        _hstartedCursor, _hstartedIncrement, _hstartedHistory, _hstartedRaw,
        _hknown, _hunknown, _hlocal, _hdisabled, _hzero, _hbankPending,
        decoded, bank, _hreceive, _hdecoded, _hbank, finishedLedger,
        clockFinished, diagnostic, _hfinish, _hfinished, _hfinishedValid,
        _hfinishedIncrement, _hfinishedGamma, _hfinishedCursor,
        _hfinishedPhase, _hfinishedCutoff, _hfinishedCurrent, _hfinishedRaw,
        _hfinishedPending, _hclockFinish, _hclockEq, _hclockPending,
        _hclockCommand, _hdiagnostic, _hdiagnosticInput, hdiagnosticRaw,
        _hpost, hobserve, _hcoord, _hnext, _hnextBank⟩
      have hdiagObserve : entry.output.coordinator.up = (prepare entry.input).observeCoordinator.up := by
        rw [entry.output_eq]
        rfl
      have hdiag : d = diagnostic := by
        apply Option.some.inj
        calc
          some d = entry.output.coordinator.up := hrecordDiag.symm
          _ = (prepare entry.input).observeCoordinator.up := hdiagObserve
          _ = some diagnostic := by rw [hobserve]
      rw [hdiag] at hrawSome
      exact hrawSome hdiagnosticRaw

private theorem livePostChoice_up_none
    {x : ReferenceActivePhysicalStep.RoundInput p rate} (prepared : PreparedRound x)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ) (started : CoordinatorPhaseClock.StartRoundResult p) :
    (livePostChoice prepared r owned base started).up = none := by
  unfold livePostChoice
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · split <;> rfl

private theorem diagnostic_choice
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (d : UpDiagnostic p rate) (hd : record.output.coordinator.up = some d) :
    ∃ c : Choice rate, choice record.input = some c := by
  have hobs : (prepare record.input).observeCoordinator.up = some d := by
    rw [record.output_eq] at hd
    exact hd
  unfold PreparedRound.observeCoordinator at hobs
  split at hobs
  · split at hobs <;> cases hobs
  next hn =>
    unfold choice
    rw [ite_eq_right hn]
    cases hc : (prepare record.input).coordinator with
    | first outcome =>
        cases outcome <;> simp only [hc] at hobs
        all_goals first | contradiction |
          (unfold livePostChoice at hobs;
            repeat' (first | split at hobs | simp [coordinatorFailure] at hobs))
    | live r owned base outcome =>
        cases outcome <;> simp only [hc] at hobs
        all_goals first | contradiction |
          (unfold livePostChoice at hobs;
            repeat' (first | split at hobs | simp [coordinatorFailure] at hobs)) |
          (exact ⟨_, rfl⟩)
    | collection payload ledger clock cutoff outcome =>
        cases outcome <;> simp only [hc] at hobs
        all_goals first | contradiction |
          (unfold livePostChoice at hobs;
            repeat' (first | split at hobs | simp [coordinatorFailure] at hobs)) |
          (exact ⟨_, rfl⟩)
    | invalidCollectionCutoff => simp [hc, coordinatorFailure] at hobs
    | dagger => simp [hc, coordinatorFailure] at hobs

private theorem choice_executedTail
    (x : ReferenceActivePhysicalStep.RoundInput p rate) (c : Choice rate)
    (hc : choice x = some c) :
    executedTail x = some ⟨c.payload, c.preLedger, c.started, c.weights⟩ := by
  unfold choice at hc
  unfold executedTail
  split at hc
  · contradiction
  next hn =>
    rw [ite_eq_right hn]
    cases hd : (prepare x).coordinator with
    | first outcome => cases outcome <;> simp [hd, choiceOfCut] at hc
    | live r owned base outcome =>
        cases outcome <;> simp only [hd, choiceOfCut, reduceCtorEq] at hc
        next => cases Option.some.inj hc; rfl
    | collection payload ledger clock cutoff outcome =>
        cases outcome <;> simp only [hd, choiceOfCut, reduceCtorEq] at hc
        next => cases Option.some.inj hc; rfl
    | invalidCollectionCutoff => simp [hd, choiceOfCut] at hc
    | dagger => simp [hd, choiceOfCut] at hc

private theorem choice_diagnostic_start
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (c : Choice rate) (hc : choice record.input = some c)
    (d : UpDiagnostic p rate) (hd : record.output.coordinator.up = some d) :
    ∃ (recording : CoordinatorRecordingOperation.Output p) (started : Ledger rate),
      CoordinatorRecorderComplementBridge.run
        (collectionRecordingInput (prepare record.input) c.payload c.started c.weights) =
          some recording ∧
      startRound c.preLedger (record.input.time.val + 1)
        (collectionEnabled c.preLedger record.input.time)
        (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) =
          .success started ∧
      (receiveUp (prepare record.input) started).diagnostic = some d := by
  have htail : record.output.coordinator = collectionPostChoice (prepare record.input)
      c.payload c.preLedger c.started c.weights := by
    rw [record.output_eq]
    exact choice_tail record.input c hc
  rw [htail] at hd
  unfold collectionPostChoice at hd
  cases hr : CoordinatorRecorderComplementBridge.run
      (collectionRecordingInput (prepare record.input) c.payload c.started c.weights) with
  | none => simp [hr, coordinatorFailure] at hd
  | some recording =>
      simp only [hr] at hd
      cases hs : startRound c.preLedger (record.input.time.val + 1)
          (collectionEnabled c.preLedger record.input.time)
          (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) with
      | invalid => simp [hs, coordinatorFailure] at hd
      | rejected _ => simp [hs, coordinatorFailure] at hd
      | success started =>
          simp only [hs] at hd
          rw [ReferenceActiveAffinePositiveTest.collectionFinish_up] at hd
          exact ⟨recording, started, rfl, hs, hd⟩

private theorem receive_diagnostic_fields
    (x : ReferenceActivePhysicalStep.RoundInput p rate) (started : Ledger rate)
    (d : UpDiagnostic p rate)
    (hd : (receiveUp (prepare x) started).diagnostic = some d) :
    d.input.ledger = started ∧ d.input.selectedFollower = upSenderIndex x ∧
      d.raw = (CoordinatorUpReception.decoderTransition
        (ReferenceUpReception.receptionInputAtRow rate x.row
          (upInputs (prepare x) started) x.time)).2 ∧
      d.expected = upExpected (prepare x) ∧
      CoordinatorUpReception.receptionInputCheck
        (ReferenceUpReception.receptionInputAtRow rate x.row
          (upInputs (prepare x) started) x.time) = true := by
  unfold receiveUp at hd
  dsimp only at hd
  split at hd
  next hcheck =>
    cases Option.some.inj hd
    exact ⟨rfl, rfl, rfl, rfl, hcheck⟩
  next => contradiction

/-- A present native observer branch has an actual accepted filtered UP on
its original source record. Checked replay validity is derived from the
accepted source-domain theorem, rather than supplied as an input. -/
theorem firstCell_nativeUp_observer_accepted
    (u t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : z ∈ correctedCell rate rewards C_star C_h u t)
    (j k : ℕ) (a : Fin p.K) (q : ℕ)
    (hqueue : firstPrefixQueueAt rate rewards C_star C_h z j k = some (a, q)) :
    let R := sourceRecords rate rewards C_star C_h z
    let e := birthIndex rate rewards C_star C_h z + 1 +
      (liveTail rate rewards C_star C_h z).length
    ∃ (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (d : UpDiagnostic p rate) (M : UpRecord p rate),
      R[e + j]? = some record ∧ record.output.coordinator.up = some d ∧
      d.input.selectedFollower = upSenderIndex record.input ∧
      CoordinatorUpReception.parseDecoderOutput
        (ReferenceUpReception.filterRawByExpected d.raw d.expected) = some M ∧
      AcceptedUp record.input (upSenderIndex record.input) M := by
  classical
  obtain ⟨entry, seg, record, d, M, _hvalid, _hphase, _hcutPos,
    _hcutCursor, _hcursor, _hentry, _hcut, _hsegment, _hlength, hrecord,
    hd, hparsed, haccept, _hcurrent, _hcutoff, _hdecoded⟩ :=
      firstCell_nativeUp_observer_replay_data rate rewards C_star C_h u t z hz j k a q hqueue
  obtain ⟨c, hc⟩ := diagnostic_choice rate record d hd
  obtain ⟨recording, started, hr, hs, hdiag⟩ :=
    choice_diagnostic_start rate record c hc d hd
  obtain ⟨hledger, hsender, hraw, hexpected, hcheck⟩ :=
    receive_diagnostic_fields rate record.input started d hdiag
  have hparse : effectiveParse record.input started = some M := by
    simpa only [effectiveParse, ← hraw, ← hexpected] using hparsed
  have haccept' : acceptUpCheck started (upSenderIndex record.input) M = true := by
    simpa only [hledger, hsender] using haccept
  let R := sourceRecords rate rewards C_star C_h z
  let n := birthIndex rate rewards C_star C_h z + 1 +
    (liveTail rate rewards C_star C_h z).length + j
  have hn : n < R.length := (List.getElem?_eq_some_iff.mp hrecord).1
  dsimp only [R, sourceRecords] at hn
  have hget : R[n]'hn = record := (List.getElem?_eq_some_iff.mp hrecord).2
  dsimp only [R, sourceRecords] at hget
  subst record
  let record := (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[n]
  have hdomains :=
    ReferenceCompleteCollectionUpDecodeDomains.complete_filtered_up_decode_domains
      rate rewards C_star C_h z ⟨n, hn⟩ c hc recording started hs M hparse haccept'
  dsimp only at hdomains
  obtain ⟨hprefix, hlast, past, current, hpast, hcurrent, _hlen,
    houtput, hcandidate, _hbound, _hcapacity⟩ := hdomains
  have hguards := decodePrefixQueue?_some_guards rate d.input.ledger
    d.input.selectedFollower M k a q _hdecoded
  obtain ⟨hinput, _, hcurrentNone, hcutoffNone⟩ := hguards
  rw [hledger] at hinput
  rw [hledger, hsender] at hcurrentNone hcutoffNone
  have hdecode : decodeUp started (upSenderIndex record.input) (some M) =
      .success (acceptUpCandidate started (upSenderIndex record.input) M past current) := by
    dsimp only [record]
    unfold decodeUp
    rw [dite_eq_left hinput]
    simp only [haccept', dite_eq_left (And.intro hcurrentNone hcutoffNone), ↓reduceIte]
    rw [hpast, hcurrent]
    simp only [houtput, hcandidate, ↓reduceIte]
  have hreceive := receiveUp_filtered record.input started hcheck
  rw [hparse, hdecode] at hreceive
  refine ⟨record, d, M, hrecord, hd, hsender, hparsed, ?_⟩
  exact ⟨⟨c.payload, c.preLedger, c.started, c.weights⟩, recording, started,
    acceptUpCandidate started (upSenderIndex record.input) M past current,
    CoordinatorUpReception.decoderBankAfter
      (ReferenceUpReception.receptionInputAtRow rate record.input.row
        (upInputs (prepare record.input) started) record.input.time),
    choice_executedTail rate record.input c hc, hr, hs, hreceive, hparse, rfl⟩

private theorem segment_record_get
    (R : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (e : ℕ) (seg : Segment rate) (hseg : segmentAt R e = some seg)
    (j : ℕ) (hj : j < seg.records.length) :
    R[e + j]? = some seg.records[j] := by
  have hpart := segmentAt_partition R e seg hseg
  calc
    R[e + j]? = (R.drop e)[j]? := (List.getElem?_drop ..).symm
    _ = (seg.records ++ seg.remaining)[j]? := by rw [hpart]
    _ = some seg.records[j] := by
      rw [List.getElem?_append_left hj, List.getElem?_eq_getElem hj]

private theorem segment_positive_input_collection
    (z : BootstrapPrivateRoundStreams.SourceInput p) (e : ℕ) (seg : Segment rate)
    (hseg : segmentAt (sourceRecords rate rewards C_star C_h z) e = some seg)
    (j : ℕ) (hjpos : 1 ≤ j) (hj : j ≤ seg.records.length)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hrecord : (sourceRecords rate rewards C_star C_h z)[e + j]? = some record) :
    ∃ P l saved, record.input.state.coordinator = .collection P l saved := by
  let R := sourceRecords rate rewards C_star C_h z
  have hp : j - 1 < seg.records.length := by omega
  have hprev := segment_record_get rate R e seg hseg (j - 1) hp
  have hgood := segment_all_completed (R.drop e) seg (segmentAt_branch R e seg hseg).1
    seg.records[j - 1] (List.getElem_mem hp)
  cases he : extractRound seg.records[j - 1] with
  | none => simp [he] at hgood
  | some done =>
      obtain ⟨_, _, _, P, saved, hnext⟩ :=
        actual_collection_round_checked seg.records[j - 1] done he
      have hn : e + j < R.length := (List.getElem?_eq_some_iff.mp hrecord).1
      have hpget := (List.getElem?_eq_some_iff.mp hprev).2
      have hrget := (List.getElem?_eq_some_iff.mp hrecord).2
      have hadj := ReferenceCompleteLaterLiveComplementPrefixReplay.complete_adjacent
        (rate := rate) rewards C_star C_h z (e + (j - 1)) (by change _ < R.length; omega)
      change (R[e + (j - 1) + 1]).input.state = (R[e + (j - 1)]).output.next at hadj
      have hindex : e + (j - 1) + 1 = e + j := by omega
      have hleft : R[e + (j - 1) + 1] = record := by
        simpa only [hindex] using hrget
      rw [hleft, hpget] at hadj
      exact ⟨P, done.final, saved, congrArg State.coordinator hadj |>.trans hnext⟩

private theorem dropWhile_first_false {α : Type*} (f : α → Bool) (xs : List α)
    (x : α) (h : (xs.dropWhile f)[0]? = some x) : f x = false := by
  induction xs with
  | nil => simp at h
  | cons y ys ih =>
      cases hy : f y with
      | true =>
          simp only [List.dropWhile_cons, hy, ↓reduceIte] at h
          exact ih h
      | false =>
          simp only [List.dropWhile_cons, hy, Bool.false_eq_true, ↓reduceIte,
            List.getElem?_cons_zero, Option.some.injEq] at h
          exact h ▸ hy

private theorem segment_boundary_not_continuing
    (R : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (e : ℕ) (seg : Segment rate) (hseg : segmentAt R e = some seg)
    (hne : seg.records ≠ [])
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hrecord : R[e + seg.records.length]? = some record) :
    continuing record = false := by
  have hs := (segmentAt_branch R e seg hseg).1
  have hhead : seg.remaining[0]? = some record := by
    have hpart := segmentAt_partition R e seg hseg
    have hh : (R.drop e)[seg.records.length]? = some record := by
      simpa only [List.getElem?_drop] using hrecord
    rw [← hpart, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self] at hh
    exact hh
  cases hd : R.drop e with
  | nil => simp [hd, ReferenceCollectionSegmentExtraction.segment] at hs
  | cons entry rest =>
      rw [hd] at hs
      unfold ReferenceCollectionSegmentExtraction.segment at hs
      cases hc : choice entry.input with
      | none => simp [hc] at hs
      | some c =>
          simp only [hc, Option.map_some] at hs
          split at hs
          · cases Option.some.inj hs
            exact dropWhile_first_false continuing rest record hhead
          · cases Option.some.inj hs
            exact False.elim (hne rfl)

/-- Every present observer branch lies strictly inside its original collection
segment. In particular, the optional first excluded record cannot survive on
this actual first corrected source cell. -/
theorem firstCell_nativeUp_observer_support
    (u t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : z ∈ correctedCell rate rewards C_star C_h u t)
    (j k : ℕ) (a : Fin p.K) (q : ℕ)
    (hqueue : firstPrefixQueueAt rate rewards C_star C_h z j k = some (a, q)) :
    let R := sourceRecords rate rewards C_star C_h z
    let e := birthIndex rate rewards C_star C_h z + 1 +
      (liveTail rate rewards C_star C_h z).length
    ∃ (entry : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (seg : Segment rate)
      (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (M : UpRecord p rate),
      R[e]? = some entry ∧ cutoffChosen entry.input = true ∧
      segmentAt R e = some seg ∧ 1 ≤ j ∧ j < seg.records.length ∧
      R[e + j]? = some record ∧ record ∈ seg.records ∧
      AcceptedUp record.input (upSenderIndex record.input) M := by
  classical
  dsimp only
  obtain ⟨entry, seg, record, d, M, _hvalid, _hphase, _hcutPos,
    _hcutCursor, _hcursor, hentry, hcut, hseg, hj, hrecord,
    hd, _hparsed, _haccept, _hcurrent, _hcutoff, _hdecoded⟩ :=
      firstCell_nativeUp_observer_replay_data rate rewards C_star C_h u t z hz j k a q hqueue
  obtain ⟨record', d', M', hrecord', _hd', _hsender, _hparse, hacc⟩ :=
    firstCell_nativeUp_observer_accepted rate rewards C_star C_h u t z hz j k a q hqueue
  have heq : record' = record := Option.some.inj (hrecord'.symm.trans hrecord)
  subst record'
  have hjpos := firstCell_nativeUp_observer_offset_positive rate rewards C_star C_h
    u t z hz j k a q hqueue
  let R := sourceRecords rate rewards C_star C_h z
  let e := birthIndex rate rewards C_star C_h z + 1 +
    (liveTail rate rewards C_star C_h z).length
  have hn : e + j < R.length := (List.getElem?_eq_some_iff.mp hrecord).1
  dsimp only [R, sourceRecords] at hn
  have hget : R[e + j]'hn = record := (List.getElem?_eq_some_iff.mp hrecord).2
  obtain ⟨c, hc⟩ := diagnostic_choice rate record d hd
  dsimp only [R, sourceRecords] at hget
  subst record
  let record := (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[e + j]
  have hloc := ReferenceCompleteAcceptedUpCollectionLocalization.complete_accepted_up_collection_localization
    rewards C_star C_h z ⟨e + j, hn⟩ (upSenderIndex record.input) M' hacc c hc
  dsimp only at hloc
  obtain ⟨segA, done, c0, I, _ho, _hoR, _hn, _hsegment, _hentry, _hcontext,
    _hc0, _hpayload, _hI, _hchecked, _hsigma, _hcutoff, _htime, _hlive,
    _hrecordA, hdone, _hcontextA, _haccepted, _hparsedA, _hsenderA, _rest⟩ := hloc
  have hjlt : j < seg.records.length := by
    by_contra hnot
    have hjeq : j = seg.records.length := by omega
    obtain ⟨P, l, saved, hstate⟩ := segment_positive_input_collection
      rate rewards C_star C_h z e seg hseg j hjpos hj record hrecord
    have hdoneRecord : extractRound record = some done := hdone
    have hcontinue : continuing record = true := by
      rw [continuing_eq_collectionTags, inputCollectionTag_eq_configuration,
        hstate, ← extractRound_isSome_eq_outputCollectionTag, hdoneRecord]
      rfl
    have hboundary := segment_boundary_not_continuing rate R e seg hseg
      (by intro hempty; simp only [hempty, List.length_nil] at hj; omega) record
      (by simpa only [← hjeq] using hrecord)
    rw [hcontinue] at hboundary
    contradiction
  have hmem : record ∈ seg.records := by
    have hg := segment_record_get rate R e seg hseg j hjlt
    have heq : seg.records[j] = record := Option.some.inj (hg.symm.trans hrecord)
    rw [← heq]
    exact List.getElem_mem hjlt
  exact ⟨entry, seg, record, M', hentry, hcut, hseg, hjpos, hjlt, hrecord, hmem, hacc⟩

variable {rate rewards C_star C_h}

private theorem live_readout_zero (s : ℕ)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) (c : RecordedQueueRun.RoundInput p.K)
    (hc : ReferenceLaterLiveNumericalReadout.laterLiveReadout s r = some c) :
    ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r = some c := by
  obtain ⟨selected, ho, hselection, hbase, hlive, hcell⟩ :=
    ReferenceLaterLiveNumericalReadout.laterLiveReadout_some s r c hc
  have hz : 0 < selected.view.payload.sigma.val := by omega
  unfold ReferenceLaterLiveNumericalReadout.laterLiveReadout
  simp only [hselection, hz, hlive, and_self, ite_true, dite_eq_left ho]
  exact congrArg some hcell.symm

private theorem cell0_of_live (s : ℕ)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) (c : RecordedQueueRun.RoundInput p.K)
    (hc : ReferenceLaterLiveNumericalReadout.laterLiveReadout s r = some c) :
    ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r = some c := by
  simp only [ReferenceFirstCollectionCurrentRetainedGate.cell0,
    live_readout_zero s r c hc, Option.some_or]

private theorem mapM_id_some {α : Type*} (slots : List (Option α)) (cells : List α)
    (h : slots.mapM id = some cells) : slots = cells.map some := by
  induction slots generalizing cells with
  | nil =>
    have he : cells = [] := (Option.some.inj h).symm
    subst cells
    rfl
  | cons slot slots ih =>
    cases slot with
    | none => simp [List.mapM_cons] at h
    | some a =>
      cases ht : slots.mapM id with
      | none => simp [List.mapM_cons, ht] at h
      | some tail =>
        have he : a :: tail = cells := by simpa [List.mapM_cons, ht] using h
        rw [← he, List.map_cons, ← ih tail ht]

private theorem prefixInputs_readout
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (q : ℕ) (G : List (RecordedQueueRun.RoundInput p.K))
    (hlen : G.length = q)
    (hq : q ≤ (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).length)
    (hprefix : ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
      rate rewards C_star C_h
        (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + q) z = some G) :
    ∀ k : Fin q,
      ReferenceFirstCollectionCurrentRetainedGate.cell0 rate
        ((ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val]'(by omega)) =
          some (G[k.val]'(by omega)) := by
  have hs := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs_launch
    rate rewards C_star C_h _ z G hprefix
  simp only [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs,
    ite_eq_left hs, ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart,
    Nat.add_sub_cancel_left] at hprefix
  have hmap := mapM_id_some _ G hprefix
  intro k
  have he := congrArg (fun L => L[k.val]?) hmap
  simpa only [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords,
    List.getElem?_map, List.getElem?_take, show k.val < q from k.isLt, ite_true,
    List.getElem?_eq_getElem (show k.val <
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).length by omega),
    List.getElem?_eq_getElem (show k.val < G.length by omega), Option.map_some, Option.some.injEq] using he

private theorem assigned_live_cells_eq
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (b e : ℕ)
    (L B : List (RecordedQueueRun.RoundInput p.K)) (c : RecordedQueueRun.RoundInput p.K)
    (hL : L.length = b) (hlen : ((L ++ [c]) ++ B).length = e)
    (he : e ≤ (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).length)
    (hprefix : ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
      rate rewards C_star C_h
      (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + e) z = some ((L ++ [c]) ++ B))
    (P : Payload rate)
    (hlater : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h < P.sigma.val)
    (N : ℕ) (hN : N = e - b)
    (hw : (((ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).drop b).take N).length = N)
    (v : ∀ n : Fin N, Selection
      ((((ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).drop b).take N)[n.val]'(by omega)).input)
    (ho : ∀ n : Fin N, ReferenceLaterLiveNumericalReadout.preparedOrdinary
      ((((ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).drop b).take N)[n.val]'(by omega)))
    (hv : ∀ n : Fin N,
      let r := (((ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).drop b).take N)[n.val]'(by omega)
      r.output.preparation.coordinator.selection = some (v n) ∧
      (v n).view.payload = P ∧ (v n).view.cutoff = none ∧
      CoordinatorLocalArmChoice.assignmentIsLive (v n).view.payload (v n).view.cutoff r.input.time) :
    let Cells : Fin N → RecordedQueueRun.RoundInput p.K := fun n =>
      ReferenceFirstWindowNumericalStream.sourceCell
        ((((ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h).drop b).take N)[n.val]'(by omega))
        (v n).view.payload (v n).view.pendingAtChoice
        (ReferenceLaterLiveNumericalReadout.preparedStates _ (ho n))
        (v n).view.complementWeights (v n).view.cutoff
        (ReferenceLaterLiveNumericalReadout.selection_choiceValid (v n))
    List.ofFn Cells = [c] ++ B := by
  intro Cells
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let A := (L ++ [c]) ++ B
  change A.length = e at hlen
  change e ≤ R.length at he
  change ((R.drop b).take N).length = N at hw
  have hbe : b < e := by
    have hAlen := hlen
    simp only [A, List.length_append, List.length_singleton] at hAlen
    omega
  have hAread := prefixInputs_readout rewards C_star C_h z e A hlen he hprefix
  have hCells : ∀ n : Fin N,
      Cells n = A[b + n.val]'(by have hn := n.isLt; omega) := by
    intro n
    let r := ((R.drop b).take N)[n.val]'(by omega)
    obtain ⟨hselected, hpay, _hcut, hlive⟩ := hv n
    change r.output.preparation.coordinator.selection = some (v n) at hselected
    change CoordinatorLocalArmChoice.assignmentIsLive (v n).view.payload (v n).view.cutoff r.input.time at hlive
    have hbase : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h <
        (v n).view.payload.sigma.val := by rw [hpay]; exact hlater
    have hor : ReferenceLaterLiveNumericalReadout.preparedOrdinary r := ho n
    have hread : ReferenceLaterLiveNumericalReadout.laterLiveReadout
        (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) r = some (Cells n) := by
      unfold ReferenceLaterLiveNumericalReadout.laterLiveReadout
      simp only [hselected, hbase, hlive, and_self, ite_true, dite_eq_left hor]
      rfl
    have hcell := cell0_of_live _ r (Cells n) hread
    have hnR : b + n.val < R.length := by have hn := n.isLt; omega
    have hr : r = R[b + n.val]'hnR := by
      simp only [r, List.getElem_take, List.getElem_drop]
    rw [hr] at hcell
    exact Option.some.inj (hcell.symm.trans (hAread ⟨b + n.val, by have hn := n.isLt; omega⟩))
  have heq : List.ofFn Cells = A.drop b := by
    apply List.ext_getElem
    · simp only [List.length_ofFn, List.length_drop]
      exact hN.trans (congrArg (fun k => k - b) hlen).symm
    · intro n hn hn'
      simp only [List.getElem_ofFn, List.getElem_drop]
      exact hCells ⟨n, by simpa only [List.length_ofFn] using hn⟩
  rw [heq]
  change ((L ++ [c]) ++ B).drop b = [c] ++ B
  rw [List.append_assoc, ← hL, List.drop_append_length]

private theorem mapM_map_some {α : Type*} (L : List α) :
    (L.map some).mapM id = some L := by
  induction L with
  | nil => rfl
  | cons a L ih => simp only [List.map_cons, List.mapM_cons, ih]; rfl

private theorem prefixInputs_take
    (z : BootstrapPrivateRoundStreams.SourceInput p) (n h : ℕ)
    (G : List (RecordedQueueRun.RoundInput p.K))
    (hG : prefixInputs rate rewards C_star C_h n z = some G)
    (hlaunch : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
      rate rewards C_star C_h (sourceStart rate rewards C_star C_h z + h) z)
    (hn : h ≤ n - sourceStart rate rewards C_star C_h z) :
    prefixInputs rate rewards C_star C_h
      (sourceStart rate rewards C_star C_h z + h) z = some (G.take h) := by
  have hlaunchG := prefixInputs_launch rate rewards C_star C_h n z G hG
  simp only [prefixInputs, ite_eq_left hlaunchG] at hG
  have hmap := mapM_id_some _ G hG
  have htake := congrArg (List.take h) hmap
  simp only [← List.map_take, List.take_take, Nat.min_eq_left hn] at htake
  rw [prefixInputs, ite_eq_left hlaunch, Nat.add_sub_cancel_left, htake]
  exact mapM_map_some _

private theorem replay_backlog_origin (cap score backlog : ℕ)
    (records : List (Bool × ℕ)) :
    (QueueReplay.replay cap (score, backlog) records).2 =
      (QueueReplay.replay cap (0, backlog) records).2 := by
  have htranslate : QueueReplay.replay cap (score + 0, backlog) records =
      (score + (QueueReplay.replay cap (0, backlog) records).1,
        (QueueReplay.replay cap (0, backlog) records).2) := by
    have commute (s : ℕ × ℕ) (r : Bool × ℕ) :
        QueueReplay.transition cap (score + s.1, s.2) r =
          (score + (QueueReplay.transition cap s r).1,
            (QueueReplay.transition cap s r).2) := by
      rcases r with ⟨enabled, arrival⟩
      cases enabled <;> simp only [QueueReplay.transition, Bool.false_eq_true,
        ↓reduceIte, Nat.add_assoc]
    exact List.foldl_hom (l := records) (init := (0, backlog))
      (fun s : ℕ × ℕ => (score + s.1, s.2)) commute
  simpa only [Nat.add_zero] using congrArg (fun x : ℕ × ℕ => x.2) htranslate


private theorem liveTail_eq_continuingPrefix
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    liveTail rate rewards C_star C_h z =
      ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
        rate rewards C_star C_h z (birthIndex rate rewards C_star C_h z + 1) := by
  simp only [liveTail, sourceRecords, ReferenceFirstReplacementLiveFollowerPrefix.continuingTail,
    ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix]
  congr 1
  funext r
  unfold ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest
    ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen
  cases r.output.preparation.coordinator with
  | live registers owned base outcome => cases outcome <;> rfl
  | first outcome => rfl
  | collection payload ledger clock cutoff outcome => rfl
  | invalidCollectionCutoff => rfl
  | dagger => rfl

private theorem firstCell_native_calendar_data
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : z ∈ correctedCell rate rewards C_star C_h u t)
    (he : birthIndex rate rewards C_star C_h z + 1 +
      (liveTail rate rewards C_star C_h z).length < (sourceRecords rate rewards C_star C_h z).length) :
    let R := sourceRecords rate rewards C_star C_h z
    let s := sourceStart rate rewards C_star C_h z
    let b := birthIndex rate rewards C_star C_h z
    let e := b + 1 + (liveTail rate rewards C_star C_h z).length
    ∃ (L B : List (RecordedQueueRun.RoundInput p.K)) (c : RecordedQueueRun.RoundInput p.K)
      (birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (payload : Payload rate) (seg : Segment rate) (D : List (RecordedQueueRun.RoundInput p.K)),
      ReferenceFirstCollectionCurrentRetainedGate.pastCells? rate rewards C_star C_h t z = some L ∧
      prefixInputs rate rewards C_star C_h (t.val + 1) z = some (L ++ [c]) ∧
      L.length = b ∧ s + b = t.val ∧ R[b]? = some birth ∧
      ReferenceAssignmentPayloadPersistence.InstallationBirth birth payload ∧
      payload.sigma = t ∧ s < payload.sigma.val ∧
      segmentAt R e = some seg ∧ seg.entry = R[e] ∧
      seg.context.payload = payload ∧
      FollowerCutoffScan.firstCutoff p rate.eta.val payload.sigma
        (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
          (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z))) = s + e + 1 ∧
      let A := (L ++ [c]) ++ B
      A.length = e ∧ e ≤ R.length ∧
      prefixInputs rate rewards C_star C_h (s + e) z = some A ∧
      D.length = seg.records.length ∧
      (∀ a h, (seg.records.take h).map
        (ReferenceCollectionRawBufferHistory.physicalQueueRecord seg.context.preLedger a) =
        (D.take h).map (fun cell => (cell.enabled, RecordedQueueRun.quantizedArrival
          (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell a))) ∧
      s + e + seg.records.length ≤ p.T ∧
      prefixInputs rate rewards C_star C_h (s + e + seg.records.length) z = some (A ++ D) ∧
      (∀ a h, ((A ++ D).take h).map (fun cell =>
          UnstoppedRecordedQueueComparison.unstoppedRecord
            (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell a) =
        ((A ++ D).take h).map (fun cell => (cell.enabled, RecordedQueueRun.quantizedArrival
          (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell a))) := by
  classical
  intro R s b e
  change e < R.length at he
  obtain ⟨L, c, birth, hL, _hc, hprefixBirth, hLb, hdateBirth, hb,
    _hbirthTime, _hrows, _hselected, _hrewards, _henabled, _hbirthRead, _hbirthCell,
    _hmode, hcalendar⟩ :=
    ReferenceFirstCorrectedCollectionCalendarNumericalJoin.firstCell_collection_calendar_numerical_values
      rate rewards C_star C_h u t z hz
  obtain ⟨birthR, rout, qout, beta, hbR, _hdateR, _htR, _hrowsR, _hJR,
    _hrewardsR, hbornR, hsigmaR, hlaterR, hliveR, _hcontR⟩ :=
    ReferenceFirstCorrectedReplacementCollectionReadout.firstCell_collection_readout_cover
      rate rewards C_star C_h u t z hz
  have hbirthEq : birthR = birth := Option.some.inj (hbR.symm.trans hb)
  subst birthR
  have hlenR := ReferenceCompletePhysicalHistory.completeSuffixRecords_length rate z rewards C_star C_h
  change R.length = p.T - s at hlenR
  have htT : t.val + 1 < p.T := by
    change s + b = t.val at hdateBirth
    change e < R.length at he
    dsimp only [e] at he
    omega
  obtain ⟨_hsigma, hcalendar⟩ := hcalendar rout qout beta hliveR
  obtain ⟨hk, hstate, hlater, _hBlen, heR, _heT, hAlen, _hAdate, hprefixA,
    _hwindow, _hWcells, _rE, _qE, _hpayE, _hstateE, hboundary⟩ := hcalendar htT
  let B := ReferenceCompleteLaterLiveComplementPrefixReplay.prefixCells
    rewards C_star C_h z ⟨b + 1, hk⟩ rout qout beta hstate hlater
  let A := (L ++ [c]) ++ B
  have hW := liveTail_eq_continuingPrefix (rate := rate) (rewards := rewards)
    (C_star := C_star) (C_h := C_h) z
  simp only [← hW] at hAlen hprefixA hboundary heR
  change A.length = e at hAlen
  change prefixInputs rate rewards C_star C_h (s + e) z = some A at hprefixA
  rcases hboundary with hterminal | ⟨_he, seg, _IC, l0, hseg, hentry,
    hpay, hpre, _hIC, _hICdef, _hICchecked, _harmIC, _hIsigmaC,
    hIcut, hIscan, _hfreezeC, _hbaseC, _hcutC, _hneC, _hpartC,
    D, hDlen, _hDcells, hDwords, _hGlen, _hGbound, hGT, _hGrecords,
    hprefixG, _hGread, _hGdisabled, hGwords, _hGfinal⟩
  · change e = R.length at hterminal
    omega
  refine ⟨L, B, c, birth, rout.payload, seg, D, hL, hprefixBirth, hLb,
    hdateBirth, hb, hbornR, hsigmaR, hlaterR, hseg, hentry, hpay, ?_,
    hAlen, heR, hprefixA, hDlen, ?_, ?_, ?_, ?_⟩
  · rw [← hIscan, hIcut]
    rfl
  · intro a h
    simpa only [← hpre] using (hDwords a).2.2 h
  · change s + (e + seg.records.length) ≤ p.T at hGT
    simpa only [← Nat.add_assoc] using hGT
  · change prefixInputs rate rewards C_star C_h (s + (e + seg.records.length)) z =
      some (A ++ D) at hprefixG
    simpa only [← Nat.add_assoc] using hprefixG
  · intro a h
    exact (hGwords a).2.2 h


variable (rate rewards C_star C_h)

/-- Every reached native UP prefix on the first corrected collection is a
prefix of the same initialized, original dated calendar. Acceptance and strict
segment support follow from the actual observer branch. The queue comparison
is unstopped and includes the returned cutoff queue at prefix zero. -/
theorem firstCell_nativeUp_replay_calendar_join
    (u t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : z ∈ correctedCell rate rewards C_star C_h u t)
    (j k : ℕ) (a : Fin p.K) (q : ℕ)
    (hqueue : firstPrefixQueueAt rate rewards C_star C_h z j k = some (a, q)) :
    let R := sourceRecords rate rewards C_star C_h z
    let s := sourceStart rate rewards C_star C_h z
    let e := birthIndex rate rewards C_star C_h z + 1 +
      (liveTail rate rewards C_star C_h z).length
    ∃ (entry record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (seg : Segment rate) (d : UpDiagnostic p rate) (M : UpRecord p rate)
      (past : List (Bool × ℕ)) (current : Bool × ℕ)
      (A D P : List (RecordedQueueRun.RoundInput p.K)),
      R[e]? = some entry ∧ seg.entry = entry ∧ cutoffChosen entry.input = true ∧
      segmentAt R e = some seg ∧ 1 ≤ j ∧ j < seg.records.length ∧
      e + j < R.length ∧ k ≤ j + 1 ∧
      R[e + j]? = some record ∧ record.output.coordinator.up = some d ∧
      d.input.selectedFollower = upSenderIndex record.input ∧
      CoordinatorUpReception.parseDecoderOutput
        (ReferenceUpReception.filterRawByExpected d.raw d.expected) = some M ∧
      AcceptedUp record.input (upSenderIndex record.input) M ∧
      a = seg.context.payload.assignment.assigned (upSenderIndex record.input) ∧
      decodePrefixQueue? rate d.input.ledger d.input.selectedFollower (some M) k = some (a, q) ∧
      (∃ (hp : d.input.ledger.cutoff - 1 +
          (d.input.ledger.cursor - d.input.ledger.cutoff) ≤ p.T)
        (hl : d.input.ledger.cursor - 1 < p.T),
        replayRecords? d.input.ledger (d.input.ledger.assignment.arm d.input.selectedFollower)
          (calendarIndices p.T (d.input.ledger.cutoff - 1)
            (d.input.ledger.cursor - d.input.ledger.cutoff) hp) = some past ∧
        replayRecords? d.input.ledger (d.input.ledger.assignment.arm d.input.selectedFollower)
          [⟨d.input.ledger.cursor - 1, hl⟩] = some [current]) ∧
      past ++ [current] = (seg.records.take (j + 1)).map
        (ReferenceCollectionRawBufferHistory.physicalQueueRecord seg.context.preLedger a) ∧
      q = (QueueReplay.replay (4 * rate.n) (0, M.val.q)
        ((past ++ [current]).take k)).2 ∧
      A.length = e ∧ D.length = seg.records.length ∧ P = A ++ D.take k ∧
      P.length = e + k ∧
      prefixInputs rate rewards C_star C_h (s + e) z = some A ∧
      prefixInputs rate rewards C_star C_h (s + e + seg.records.length) z = some (A ++ D) ∧
      prefixInputs rate rewards C_star C_h (s + e + k) z = some P ∧
      t.val + 1 ≤ s + e + k ∧ s + e + k ≤ s + e + seg.records.length ∧
      s + e + seg.records.length ≤ p.T ∧
      q = (UnstoppedRecordedQueueComparison.unstoppedReplay
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) P P.length a).2 := by
  classical
  dsimp only
  let R := sourceRecords rate rewards C_star C_h z
  let s := sourceStart rate rewards C_star C_h z
  let b := birthIndex rate rewards C_star C_h z
  let e := b + 1 + (liveTail rate rewards C_star C_h z).length
  obtain ⟨entry, seg, record, d, M, hvalid, hphase, hcutPos, hcutCursor,
    hcursorT, hentry, hcut, hseg, hjle, hrecord, hd, hparsed, haccept,
    hcurrentNone, hcutoffNone, hdecoded⟩ :=
    firstCell_nativeUp_observer_replay_data rate rewards C_star C_h u t z hz j k a q hqueue
  obtain ⟨past, current, hpast, hcurrent, hdomains, hkword, hq⟩ :=
    decodePrefixQueue?_some_replay_data rate d.input.ledger d.input.selectedFollower M k a q hdecoded
  obtain ⟨recordA, dA, MA, hrecordA, hdA, hsender, hparseA, hacc⟩ :=
    firstCell_nativeUp_observer_accepted rate rewards C_star C_h u t z hz j k a q hqueue
  have hrA : recordA = record := Option.some.inj (hrecordA.symm.trans hrecord)
  subst recordA
  have hdEq : dA = d := Option.some.inj (hdA.symm.trans hd)
  subst dA
  have hMEq : MA = M := Option.some.inj (hparseA.symm.trans hparsed)
  subst MA
  obtain ⟨_, segS, _, _, _, _, hsegS, hjpos, hjlt, _⟩ :=
    firstCell_nativeUp_observer_support rate rewards C_star C_h u t z hz j k a q hqueue
  have hsegEq : segS = seg := Option.some.inj (hsegS.symm.trans hseg)
  subst segS
  have hn : e + j < R.length := (List.getElem?_eq_some_iff.mp hrecord).1
  dsimp only [R, sourceRecords] at hn
  have hget : R[e + j]'hn = record := (List.getElem?_eq_some_iff.mp hrecord).2
  dsimp only [R, sourceRecords] at hget
  obtain ⟨L, B, cB, birth, payload, segC, D, hL, hprefixBirth, hLb,
    hdateBirth, hb, hbornR, hsigmaR, hlater, hsegC, hentryC, hpayC,
    hcutoffDatePayload, hAlen, heR, hprefixA, hDlen, hDwords, hGT,
    hprefixG, hGwords⟩ := firstCell_native_calendar_data rate rewards C_star C_h
      u t z hz (by
        change e < R.length
        exact Nat.lt_of_le_of_lt (Nat.le_add_right e j) hn)
  have hsegCEq : segC = seg := Option.some.inj (hsegC.symm.trans hseg)
  subst segC
  let A := (L ++ [cB]) ++ B
  change L.length = b at hLb
  change s + b = t.val at hdateBirth
  change A.length = e at hAlen
  change e ≤ R.length at heR
  change prefixInputs rate rewards C_star C_h (s + e) z = some A at hprefixA
  change D.length = seg.records.length at hDlen
  change s + e + seg.records.length ≤ p.T at hGT
  change prefixInputs rate rewards C_star C_h (s + e + seg.records.length) z = some (A ++ D) at hprefixG
  have hentryEq : seg.entry = entry :=
    hentryC.trans (List.getElem?_eq_some_iff.mp hentry).2
  have hne : seg.records ≠ [] := by intro h; simp only [h, List.length_nil] at hjlt; omega
  have hpayAll := (ReferenceFirstCorrectedReplacementCollectionBoundaryHistory.firstCell_collection_boundary_history
    rate rewards C_star C_h u t z hz e seg hseg hne (hentryEq ▸ hcut)).2.2.1
  have hcutoffDate : FollowerCutoffScan.firstCutoff p rate.eta.val seg.context.payload.sigma
      (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
        (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z))) = s + e + 1 := by
    rw [hpayC]
    exact hcutoffDatePayload
  obtain ⟨c, bi, downIndex, logged, after, cut, raw, scan, registers, lastService,
    hc, _hbdown, _hdownk, hborn, _hretained, _hlogged, _hdown, _houtcome,
    _hscan, _hchecked, hdownQueue, _hdpos, _hdle, _htimes, hLiveLen, v, ho,
    hselected, _hprepared, _hQ, _hEd, hLiveWordLen, _hLiveEnabled,
    _hregisters, _hlastService, terminalIndexBound, _hterminalIndex,
    terminal, terminalMemory, _hterminalChoice, _hterminalStatus, _hterminalDown,
    _hterminalRegisters, _hterminalDelta, _hUsigma, _hUSterminal, _hUdterminal,
    _hUqterminal, hUNumerical, _hUDNumerical, hledger⟩ :=
    ReferenceCompleteAcceptedUpLedgerNumericalReplay.complete_accepted_up_collection_ledger_numerical_replay
      (rate := rate) rewards C_star C_h z ⟨e + j, hn⟩ (upSenderIndex record.input) M
      (by rw [hget]; exact hacc)
  have hcRecord : choice record.input = some c := by rw [hget] at hc; exact hc
  have hmem : record ∈ seg.records := by
    have hr := segment_record_get rate R e seg hseg j hjlt
    have heq := Option.some.inj (hr.symm.trans hrecord)
    rw [← heq]
    exact List.getElem_mem hjlt
  have hpay : c.payload = seg.context.payload := hpayAll record hmem c hcRecord
  have hbtime := ReferenceAssignmentPayloadChronology.installationBirth_time_eq R[bi.val] c.payload hborn
  dsimp only [R, sourceRecords] at hbtime
  have hbitime := ReferenceAssignmentFollowerMassSteps.complete_record_time rate rewards C_star C_h z bi
  have hbdate := hbtime.trans hbitime
  have hbi : bi.val = b := by
    rw [hpay, hpayC, hsigmaR] at hbdate
    change t.val = s + bi.val at hbdate
    change s + b = t.val at hdateBirth
    omega
  let N := FollowerCutoffScan.firstCutoff p rate.eta.val c.payload.sigma
      (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
        (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z))) - (c.payload.sigma.val + 1)
  have hN : N = e - b := by
    dsimp only [N]
    rw [hpay, hcutoffDate, hpayC, hsigmaR]
    change s + b = t.val at hdateBirth
    omega
  obtain ⟨segF, done, c0, I, _hok, _hoR, _hnF, hsegment, _hentryF,
    hsegContext, _hc0, _hP0, _hI, _hIchecked, _hIsigma, _hIcutoff,
    _hentryTime, _hlive, _hrecordF, _hdone, _hcontext, _haccepted,
    _hparsedF, _hsenderF, _hprefix, _hlabels, _hpartition, _hexit, _hoffset,
    hIarm, _hfreeze, _hbase, _initialF, _spanF, _activeF, _hlaunchF, _hfirstF,
    _hrunF, _hwhole, _prefixExecution, _hprefixRun, _hprefixInitial,
    _hprefixFinal, recording, started, decoded, bank, finished, _hrecording,
    hrecorder, hstart, _hreceive, _hdecode, _hfinish, _hfinished, _hinput,
    hbound, lastIndex, hlastRound, hlastIndex, hcursor, hassignment, _hstartedSigma,
    _hstartedCutoff, _hstartedFreeze, _hstartedBase, _hcutpos, _hcutcursor, _hcursorT,
    _hprefixUnknown, _hstartedUnknown, pastF, currentF, hpastF, hcurrentF, _hsupplied,
    _hpastPhysical, _hcurrentPhysical, hpastCurrentF, _hphysicalAppend, _hrestLedger⟩ := hledger
  clear _hrestLedger
  let o := FollowerCutoffScan.firstCutoff p rate.eta.val c.payload.sigma
      (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
        (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z))) - (s + 1)
  change segmentAt R o = some segF at hsegment
  change started.cursor - started.cutoff = e + j - o at hcursor
  have hoE : o = e := by
    dsimp only [o]
    rw [hpay, hcutoffDate]
    omega
  have hsegFEq : segF = seg := by
    have hs : segmentAt R e = some segF := by simpa only [hoE] using hsegment
    exact Option.some.inj (hs.symm.trans hseg)
  subst segF
  have hstartDiag := choice_diagnostic_start rate record c hcRecord d hd
  obtain ⟨recordingD, startedD, hrD, hsD, hdD⟩ := hstartDiag
  have hrecorderRecord : CoordinatorRecorderComplementBridge.run
      (collectionRecordingInput (prepare record.input) c.payload c.started c.weights) = some recording := by
    rw [_hcontext, hget] at hrecorder
    exact hrecorder
  have hrecordingEq : recordingD = recording := Option.some.inj (hrD.symm.trans hrecorderRecord)
  subst recordingD
  have hstartRecord : startRound c.preLedger (record.input.time.val + 1)
      (collectionEnabled c.preLedger record.input.time)
      (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) = .success started := by
    rw [_hcontext, hget] at hstart
    exact hstart
  have hstartedEq : startedD = started := Checked.success.inj (hsD.symm.trans hstartRecord)
  subst startedD
  obtain ⟨hledgerD, _hsenderD, _hrawD, _hexpectedD, _hcheckD⟩ :=
    receive_diagnostic_fields rate record.input started d hdD
  have harm : d.input.ledger.assignment.arm d.input.selectedFollower =
      seg.context.payload.assignment.assigned (upSenderIndex record.input) := by
    rw [hledgerD, hsender, hassignment, hIarm, hpay]
  have hreach := decodePrefixQueue?_reached rate d.input.ledger d.input.selectedFollower M k
    ⟨hvalid, hphase, hcutPos, hcutCursor, hcursorT⟩ haccept
    ⟨hcurrentNone, hcutoffNone⟩ past current hpast hcurrent hdomains
  rw [ite_eq_left hkword, hdecoded] at hreach
  have ha : a = d.input.ledger.assignment.arm d.input.selectedFollower :=
    (Prod.mk.inj (Option.some.inj hreach)).1
  have hlastVal : lastIndex = ⟨d.input.ledger.cursor - 1, by omega⟩ := by
    apply Fin.ext
    change lastIndex.val = d.input.ledger.cursor - 1
    rw [hledgerD]
    dsimp only [sourceRound] at hlastRound
    omega
  have hpastEq : pastF = past := by
    have hpastD : replayRecords? started (started.assignment.arm (upSenderIndex record.input))
        (calendarIndices p.T (started.cutoff - 1) (started.cursor - started.cutoff) hbound) = some past := by
      simpa only [hledgerD, hsender] using hpast
    exact Option.some.inj (hpastF.symm.trans hpastD)
  have hcurrentEq : currentF = current := by
    have hcurrentD : replayRecords? started (started.assignment.arm (upSenderIndex record.input))
        [lastIndex] = some [current] := by
      simpa only [hlastVal, hledgerD, hsender] using hcurrent
    exact List.singleton_inj.mp (Option.some.inj (hcurrentF.symm.trans hcurrentD))
  have hArm : started.assignment.arm (upSenderIndex record.input) = a := by
    rw [← hledgerD, ← hsender, ← ha]
  have hword : past ++ [current] = (seg.records.take (j + 1)).map
      (ReferenceCollectionRawBufferHistory.physicalQueueRecord seg.context.preLedger a) := by
    change pastF ++ [currentF] = (seg.records.take (e + j - o + 1)).map
      (ReferenceCollectionRawBufferHistory.physicalQueueRecord seg.context.preLedger
        (started.assignment.arm (upSenderIndex record.input))) at hpastCurrentF
    simpa only [hoE, Nat.add_sub_cancel_left, hpastEq, hcurrentEq, hArm] using hpastCurrentF
  have hwordLen : (past ++ [current]).length = j + 1 := by
    rw [hword, List.length_map, List.length_take, Nat.min_eq_left (by omega)]
  have hkle : k ≤ j + 1 := by omega
  have hrawPrefix : (past ++ [current]).take k = (D.take k).map
      (fun cell => (cell.enabled, RecordedQueueRun.quantizedArrival
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell a)) := by
    rw [hword, ← List.map_take, List.take_take, Nat.min_eq_left hkle]
    exact hDwords a k
  obtain ⟨Lseed, cseed, birthseed, Pseed, baseseed, hLseed, _hcseed,
    _hprefixSeed, _hLseedLen, hbseed, _harseed, _htseed, _hrowseed,
    _hJseed, _hrewardseed, _hsourceSeed, _hlaterSeed, _henabledSeed,
    hbornSeed, _hsigmaSeed, _hrateSeed, _hrewSeed, hseedQueues, _hseedRest⟩ :=
    ReferenceFirstCorrectedAssignedArrivalPrefix.firstCell_total_assigned_arrival_prefix
      rate rewards C_star C_h u t z hz
  clear _hseedRest
  have hLseedEq : Lseed = L := Option.some.inj (hLseed.symm.trans hL)
  subst Lseed
  have hbirthseedEq : birthseed = birth := Option.some.inj (hbseed.symm.trans hb)
  subst birthseed
  have hPseedEq : Pseed = payload :=
    ReferenceAssignmentPayloadChronology.installationBirth_payload_unique birth Pseed payload
      hbornSeed hbornR
  have hseedQueue : c.payload.queues a =
      (UnstoppedRecordedQueueComparison.unstoppedReplay
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) L L.length a).2 := by
    rw [hpay, hpayC, ← hPseedEq]
    exact hseedQueues a
  let qp := ReferenceFirstLaunchNumericalCell.queueParameters rate
  let rawWord := fun (xs : List (RecordedQueueRun.RoundInput p.K)) =>
    xs.map (fun cell => (cell.enabled, RecordedQueueRun.quantizedArrival qp cell a))
  have htakeL : (A ++ D).take b = L := by
    simp only [A, List.append_assoc]
    rw [← hLb, List.take_left]
  have hrawL : L.map (fun cell => UnstoppedRecordedQueueComparison.unstoppedRecord qp cell a) =
      rawWord L := by
    have hh := hGwords a b
    change ((A ++ D).take b).map (fun cell =>
      UnstoppedRecordedQueueComparison.unstoppedRecord qp cell a) = rawWord ((A ++ D).take b) at hh
    rw [htakeL] at hh
    exact hh
  have hseedRaw : c.payload.queues a = (QueueReplay.replay (4 * rate.n) (0, 0) (rawWord L)).2 := by
    rw [UnstoppedRecordedQueueComparison.unstoppedReplay, List.take_length] at hseedQueue
    change c.payload.queues a = (QueueReplay.replay (4 * rate.n) (0, 0)
      (L.map (fun cell => UnstoppedRecordedQueueComparison.unstoppedRecord qp cell a))).2 at hseedQueue
    rw [hrawL] at hseedQueue
    exact hseedQueue
  change ((R.drop bi.val).take N).length = N at hLiveLen
  have hCells := assigned_live_cells_eq rewards C_star C_h z bi.val e L B cB
    (hLb.trans hbi.symm) hAlen heR hprefixA c.payload (by rw [hpay, hpayC]; exact hlater)
    N (by rw [hbi]; exact hN) hLiveLen v ho hselected
  let Cells : Fin N → RecordedQueueRun.RoundInput p.K := fun n =>
    ReferenceFirstWindowNumericalStream.sourceCell
      (((R.drop bi.val).take N)[n.val]'(by simpa only [hLiveLen] using n.isLt))
      (v n).view.payload (v n).view.pendingAtChoice
      (ReferenceLaterLiveNumericalReadout.preparedStates _ (ho n))
      (v n).view.complementWeights (v n).view.cutoff
      (ReferenceLaterLiveNumericalReadout.selection_choiceValid (v n))
  let liveWord := List.ofFn (fun n : Fin N => ((Cells n).enabled,
    RecordedQueueRun.quantizedArrival qp (Cells n) a))
  have haPayload : a = c.payload.assignment.assigned (upSenderIndex record.input) := by
    rw [ha, harm, hpay]
  have hLiveWord : liveWord = rawWord ([cB] ++ B) := by
    have hh := congrArg (List.map (fun cell : RecordedQueueRun.RoundInput p.K =>
      (cell.enabled, RecordedQueueRun.quantizedArrival qp cell a))) hCells
    simpa only [liveWord, Cells, rawWord, List.map_ofFn, Function.comp_def, R, sourceRecords, N] using hh
  have hUNum : M.val.q = (QueueReplay.replay (4 * rate.n)
      (0, c.payload.queues a) liveWord).2 := by
    have hh := congrArg (fun x : ℕ × ℕ => x.2) hUNumerical
    simpa only [← haPayload, hdownQueue, liveWord, Cells, qp, R, sourceRecords, N] using hh
  have hcutoffQueue : M.val.q = (QueueReplay.replay (4 * rate.n) (0, 0) (rawWord A)).2 := by
    rw [hUNum, hseedRaw, hLiveWord]
    rw [show rawWord A = rawWord L ++ rawWord ([cB] ++ B) by
      simp only [rawWord, A, List.map_append, List.append_assoc]]
    rw [QueueReplay.replay_append]
    exact (replay_backlog_origin (4 * rate.n)
      (QueueReplay.replay (4 * rate.n) (0, 0) (rawWord L)).1
      (QueueReplay.replay (4 * rate.n) (0, 0) (rawWord L)).2 (rawWord ([cB] ++ B))).symm
  let P := A ++ D.take k
  have hkD : k ≤ D.length := by omega
  have hPlen : P.length = e + k := by simp only [P, List.length_append,
    List.length_take, Nat.min_eq_left hkD, hAlen]
  have htakeP : (A ++ D).take (e + k) = P := by
    rw [List.take_append, List.take_of_length_le (by omega : A.length ≤ e + k),
      hAlen, Nat.add_sub_cancel_left]
  have hlaunch := prefixInputs_launch rate rewards C_star C_h (t.val + 1) z (L ++ [cB]) hprefixBirth
  have hprefixP : prefixInputs rate rewards C_star C_h (s + e + k) z = some P := by
    have hh := prefixInputs_take z (s + e + seg.records.length) (e + k) (A ++ D)
      (by simpa only [Nat.add_assoc, s, e, b] using hprefixG)
      ⟨hlaunch.1, by change s ≤ s + (e + k); omega⟩ (by omega)
    simpa only [← Nat.add_assoc, htakeP] using hh
  have hwordP : P.map (fun cell => UnstoppedRecordedQueueComparison.unstoppedRecord qp cell a) =
      rawWord P := by
    have hh := hGwords a (e + k)
    change ((A ++ D).take (e + k)).map (fun cell =>
      UnstoppedRecordedQueueComparison.unstoppedRecord qp cell a) = rawWord ((A ++ D).take (e + k)) at hh
    rw [htakeP] at hh
    exact hh
  have hqCalendar : q = (UnstoppedRecordedQueueComparison.unstoppedReplay qp P P.length a).2 := by
    rw [hq, hrawPrefix, hcutoffQueue]
    change (QueueReplay.replay (4 * rate.n) (0,
      (QueueReplay.replay (4 * rate.n) (0, 0) (rawWord A)).2) (rawWord (D.take k))).2 = _
    rw [UnstoppedRecordedQueueComparison.unstoppedReplay, List.take_length, hwordP]
    change _ = (QueueReplay.replay (4 * rate.n) (0, 0) (rawWord P)).2
    rw [show rawWord P = rawWord A ++ rawWord (D.take k) by simp only [P, rawWord, List.map_append],
      QueueReplay.replay_append]
    exact (replay_backlog_origin (4 * rate.n)
      (QueueReplay.replay (4 * rate.n) (0, 0) (rawWord A)).1
      (QueueReplay.replay (4 * rate.n) (0, 0) (rawWord A)).2 (rawWord (D.take k))).symm
  refine ⟨entry, record, seg, d, M, past, current, A, D, P,
    hentry, hentryEq, hcut, hseg, hjpos, hjlt, hn, hkle, hrecord, hd,
    hsender, hparsed, hacc, ha.trans harm, hdecoded, ?_, hword, hq,
    hAlen, hDlen, rfl, hPlen, hprefixA, ?_, hprefixP, ?_, ?_, ?_, hqCalendar⟩
  · exact ⟨by omega, by omega, hpast, hcurrent⟩
  · exact hprefixG
  · change t.val + 1 ≤ s + e + k
    change t.val + 1 ≤ s + (b + 1 + (liveTail rate rewards C_star C_h z).length) + k
    omega
  · omega
  · omega

end Bandits.Support.ReferenceFirstCorrectedNativeUpReplayCalendarJoin
