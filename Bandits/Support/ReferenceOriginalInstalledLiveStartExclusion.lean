/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceOriginalStoppedPhysicalTransferStarts
public import Bandits.Support.ReferencePostReplacementCollectionReleaseBoundary
public import Bandits.Support.ReferenceCompleteOriginalCalendarRawLearningComparison

import Mathlib.Tactic

/-!
# Actual no-start interval after a later installation

On the original complete physical suffix, the later installation record and
its maximal continuing-LIVE prefix contain no physical transfer start. The
first record after that interval is either the suffix endpoint or the actual
cutoff whose successful `StartRound` issues `initializeAt`.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open scoped Classical

namespace Bandits.Support.ReferenceOriginalInstalledLiveStartExclusion

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev SourceInput (p : Parameters) := BootstrapPrivateRoundStreams.SourceInput p
abbrev GridRewardTable (p : Parameters) := ActualInitializationPhysicalStep.GridRewardTable p

variable {p : Parameters}

private theorem complete_suffix_record_source_date
    (rate : RateInput p) (rewards : GridRewardTable p) (C_star C_h : ℝ)
    (z : SourceInput p)
    (j : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length) :
    (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[j.val].input.time.val =
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + j.val := by
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  have htimes := ReferenceCompletePhysicalHistory.completeSuffixRecords_time_values
    rate z rewards C_star C_h
  have hjR : j.val < R.length := by
    simpa only [R] using j.isLt
  have htimeOption : (R.map (fun record => record.input.time.val))[j.val]? =
      (ReferenceActivePhysicalHorizon.calendar s (p.T - s))[j.val]? := by
    exact congrArg (fun records : List ℕ => records[j.val]?) htimes
  have hmap : (R.map (fun record => record.input.time.val))[j.val]? =
      some (R[j.val].input.time.val) := by
    rw [List.getElem?_map, List.getElem?_eq_getElem hjR]
    rfl
  have hjCalendar : j.val < (ReferenceActivePhysicalHorizon.calendar s (p.T - s)).length := by
    rw [← htimes]
    simpa only [List.length_map] using j.isLt
  have hcalendar :
      (ReferenceActivePhysicalHorizon.calendar s (p.T - s))[j.val]? = some (s + j.val) := by
    rw [List.getElem?_eq_getElem hjCalendar]
    simp only [ReferenceActivePhysicalHorizon.calendar, List.getElem_range', Nat.one_mul]
  have hvalue := hmap.symm.trans (htimeOption.trans hcalendar)
  exact Option.some.inj hvalue

private theorem complete_suffix_record_actual_lookup
    (rate : RateInput p) (rewards : GridRewardTable p) (C_star C_h : ℝ)
    (z : SourceInput p)
    (j : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length) :
    ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualRecordAt rate rewards C_star C_h
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
        )[j.val].input.time z =
      some (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
        )[j.val] := by
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  have hdate := complete_suffix_record_source_date rate rewards C_star C_h z j
  change (if s ≤ R[j.val].input.time.val then R[R[j.val].input.time.val - s]?
    else none) = some R[j.val]
  rw [hdate, ite_eq_left (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
  exact List.getElem?_eq_getElem j.isLt

private theorem complete_suffix_record_phase_exhaustion
    (rate : RateInput p) (rewards : GridRewardTable p) (C_star C_h : ℝ)
    (z : SourceInput p)
    (j : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length) :
    let r := (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[j.val]
    r.input.state.coordinator ≠ .dagger ∧
    r.output.preparation.coordinator.selection ≠ none ∧
    r.output.coordinator.failure = none ∧
    r.output.next.coordinator ≠ .first ∧
    r.output.next.coordinator ≠ .dagger := by
  exact (ReferenceCompleteCoordinatorPhaseExhaustion.complete_coordinator_phase_exhaustion
    rate rewards C_star C_h z).1 j

private theorem actual_no_transfer_start_of_live_no_initializeAt
    (rate : RateInput p) (rewards : GridRewardTable p) (C_star C_h : ℝ)
    (z : SourceInput p)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
    (base : Fin (p.m - 1) → ℕ)
    (hlookup : ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualRecordAt
      rate rewards C_star C_h record.input.time z = some record)
    (hstate : record.input.state.coordinator = .live registers owned base)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (hstart : CoordinatorPhaseClock.startRound p rate.eta.val record.input.time
      registers.priorClock registers.clockPending = .ok started)
    (hu : started.clock.u = none) :
    ¬ ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferStartAt
      rate rewards C_star C_h record.input.time z := by
  change ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferInitialMarkerAt
      rate rewards C_star C_h record.input.time z ∨
    ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferLiveStartAt
      rate rewards C_star C_h record.input.time z → _
  intro hstartAt
  rcases hstartAt with hfirst | hlive
  · obtain ⟨other, hother, hotherFirst⟩ :=
      (ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferInitialMarkerAt_iff_record_first
        rate rewards C_star C_h record.input.time z).mp hfirst
    have heq : other = record := Option.some.inj (hother.symm.trans hlookup)
    subst other
    rw [hstate] at hotherFirst
    cases hotherFirst
  · obtain ⟨other, otherRegisters, otherOwned, otherBase, otherStarted,
      hother, hotherState, hotherStart, hotherCommand⟩ :=
      (ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferLiveStartAt_iff
        rate rewards C_star C_h record.input.time z).mp hlive
    have heq : other = record := Option.some.inj (hother.symm.trans hlookup)
    subst other
    have hfields := ReferenceActivePhysicalStep.CoordinatorConfiguration.live.inj
      (hotherState.symm.trans hstate)
    rcases hfields with ⟨rfl, rfl, rfl⟩
    have hstarted : started = otherStarted := Except.ok.inj (hstart.symm.trans hotherStart)
    have hu' : otherStarted.clock.u = none := by
      simpa [hstarted] using hu
    let timedRegisters := { otherRegisters with time := record.input.time }
    have hotherStartTimed :
        CoordinatorPhaseClock.startRound p rate.eta.val timedRegisters.time
          timedRegisters.priorClock timedRegisters.clockPending = .ok otherStarted := by
      simpa [timedRegisters, CoordinatorLiveChoiceRecorderStep.Registers.clockPending] using
        hotherStart
    have hshape := CoordinatorStartRoundCutoffDispatch.startRound_initializeAt_shape
      timedRegisters otherStarted hotherStartTimed
      (by simpa [timedRegisters] using hotherCommand)
    rw [hshape.1] at hu'
    simp at hu'

/-- The same later installation and its actual continuing-LIVE prefix have
no physical transfer start. Each member is located at its original suffix
index and date, has its actual-record lookup and phase-exhaustion equations,
and exposes the literal birth or continuing dispatcher. The first excluded
record is the actual next cutoff with an `initializeAt` live start, unless the
interval reaches the honest complete-suffix endpoint. -/
public theorem actual_later_installation_live_start_exclusion
    (rate : RateInput p) (rewards : GridRewardTable p) (C_star C_h : ℝ)
    (z : SourceInput p)
    (b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (hb : ReferenceCollectionPhaseHistory.laterChosen
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[b.val].input = true) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
      rate rewards C_star C_h z (b.val + 1)
    let V := R[b.val] :: W
    let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    (∀ j : Fin V.length,
      let r := V[j.val]
      R[b.val + j.val]? = some r ∧
      r.input.time.val + 1 = s + b.val + j.val + 1 ∧
      ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualRecordAt
        rate rewards C_star C_h r.input.time z = some r ∧
      r.output.preparation = ReferenceActivePhysicalStep.prepare r.input ∧
      r.input.state.coordinator ≠ .dagger ∧
      r.output.preparation.coordinator.selection ≠ none ∧
      r.output.coordinator.failure = none ∧
      r.output.next.coordinator ≠ .first ∧
      r.output.next.coordinator ≠ .dagger ∧
      ((j.val = 0 ∧
          ReferenceCollectionPhaseHistory.laterChosen r.input = true ∧
          ∃ payload ledger saved,
            r.input.state.coordinator = .collection payload ledger saved) ∨
        (0 < j.val ∧
          ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest r = true ∧
          ∃ registers owned base,
            r.input.state.coordinator = .live registers owned base ∧
            r.output.preparation.coordinator = .live registers owned base
              (CoordinatorRoundDispatch.dispatchLive
                (ReferenceActivePhysicalStep.liveInput r.input registers owned base)) ∧
            ∃ outcome : CoordinatorRoundDispatch.LiveOutcome
                (ReferenceActivePhysicalStep.liveInput r.input registers owned base),
              CoordinatorRoundDispatch.dispatchLive
                (ReferenceActivePhysicalStep.liveInput r.input registers owned base) = outcome ∧
              (match outcome with
                | .continuingChosen dispatched _ continuation _ =>
                    CoordinatorPhaseClock.startRound p rate.eta.val r.input.time
                      registers.priorClock registers.clockPending = .ok dispatched.startResult ∧
                    continuation.startRoundResult.ledgerCommand = none
                | _ => False))) ∧
      ¬ ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferStartAt
        rate rewards C_star C_h r.input.time z) ∧
    (b.val + V.length = R.length ∨
      ∃ e : Fin R.length,
        e.val = b.val + V.length ∧
        R[e.val]? = some R[e.val] ∧
        R[e.val].input.time.val + 1 = s + e.val + 1 ∧
        ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualRecordAt
          rate rewards C_star C_h R[e.val].input.time z = some R[e.val] ∧
        R[e.val].output.preparation = ReferenceActivePhysicalStep.prepare R[e.val].input ∧
        R[e.val].input.state.coordinator ≠ .dagger ∧
        R[e.val].output.preparation.coordinator.selection ≠ none ∧
        R[e.val].output.coordinator.failure = none ∧
        R[e.val].output.next.coordinator ≠ .first ∧
        R[e.val].output.next.coordinator ≠ .dagger ∧
        ReferenceCollectionPhaseHistory.cutoffChosen R[e.val].input = true ∧
        ∃ registers owned base,
          R[e.val].input.state.coordinator = .live registers owned base ∧
          R[e.val].output.preparation.coordinator = .live registers owned base
            (CoordinatorRoundDispatch.dispatchLive
              (ReferenceActivePhysicalStep.liveInput R[e.val].input registers owned base)) ∧
          (∃ started : CoordinatorPhaseClock.StartRoundResult p,
            CoordinatorPhaseClock.startRound p rate.eta.val R[e.val].input.time
              registers.priorClock registers.clockPending = .ok started ∧
            started.ledgerCommand =
              some (CoordinatorPhaseClock.CollectionLedgerCommand.initializeAt
                R[e.val].input.time)) ∧
          ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferLiveStartAt
            rate rewards C_star C_h R[e.val].input.time z) := by
  classical
  intro R W V s
  have hphaseAll := ReferenceCompleteCoordinatorPhaseExhaustion.complete_coordinator_phase_exhaustion
    rate rewards C_star C_h z
  have hhistory :=
    ReferenceCompleteLaterInstallationChoiceHistory.actual_later_installation_choice_history
      rate rewards C_star C_h z b
  rw [ite_eq_left hb] at hhistory
  obtain ⟨birthRegisters, birthOwned, birthBase, birthSelected, _hbirthNext,
    _hbirth, hlater, _hbselection, _hbpayload, _hbpending, _hrbpending,
    _hnoEvent, _hfollowers, htail, _hnoRelease, hframesBirth⟩ := hhistory
  have hprepEq (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) :
      r.output.preparation = ReferenceActivePhysicalStep.prepare r.input := by
    rw [r.output_eq]
    rfl
  have hWle : W.length ≤ R.length - (b.val + 1) := by
    change ((R.drop (b.val + 1)).takeWhile
      ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest).length ≤ _
    simpa only [List.length_drop] using
      (List.takeWhile_prefix (l := R.drop (b.val + 1))
        ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest).length_le
  have hbLater : ReferenceCollectionPhaseHistory.laterChosen R[b.val].input = true := hb
  have hBirthState := ReferenceCollectionPhaseHistory.laterChosen_pending_empty
    R[b.val].input hbLater
  obtain ⟨birthPayload, birthLedger, birthSaved, hBirthState, _hBirthPending⟩ := hBirthState
  have hBirthLookup := complete_suffix_record_actual_lookup rate rewards C_star C_h z b
  have hBirthPhase := complete_suffix_record_phase_exhaustion rate rewards C_star C_h z b
  have hBirthDate := complete_suffix_record_source_date rate rewards C_star C_h z b
  have hBirthNoStart :=
    ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferStartAt_false_of_collection
      rate rewards C_star C_h R[b.val].input.time z R[b.val] hBirthLookup
      birthPayload birthLedger birthSaved hBirthState
  have hbirthInterval : ∀ j : Fin V.length,
      let r := V[j.val]
      R[b.val + j.val]? = some r ∧
      r.input.time.val + 1 = s + b.val + j.val + 1 ∧
      ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualRecordAt
        rate rewards C_star C_h r.input.time z = some r ∧
      r.output.preparation = ReferenceActivePhysicalStep.prepare r.input ∧
      r.input.state.coordinator ≠ .dagger ∧
      r.output.preparation.coordinator.selection ≠ none ∧
      r.output.coordinator.failure = none ∧
      r.output.next.coordinator ≠ .first ∧
      r.output.next.coordinator ≠ .dagger ∧
      ((j.val = 0 ∧ ReferenceCollectionPhaseHistory.laterChosen r.input = true ∧
          ∃ payload ledger saved,
            r.input.state.coordinator = .collection payload ledger saved) ∨
        (0 < j.val ∧ ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest r = true ∧
          ∃ registers owned base,
            r.input.state.coordinator = .live registers owned base ∧
            r.output.preparation.coordinator = .live registers owned base
              (CoordinatorRoundDispatch.dispatchLive
                (ReferenceActivePhysicalStep.liveInput r.input registers owned base)) ∧
            ∃ outcome : CoordinatorRoundDispatch.LiveOutcome
                (ReferenceActivePhysicalStep.liveInput r.input registers owned base),
              CoordinatorRoundDispatch.dispatchLive
                (ReferenceActivePhysicalStep.liveInput r.input registers owned base) = outcome ∧
              (match outcome with
                | .continuingChosen dispatched _ continuation _ =>
                    CoordinatorPhaseClock.startRound p rate.eta.val r.input.time
                      registers.priorClock registers.clockPending = .ok dispatched.startResult ∧
                    continuation.startRoundResult.ledgerCommand = none
                | _ => False))) ∧
      ¬ ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferStartAt
        rate rewards C_star C_h r.input.time z := by
    intro j
    dsimp only
    rcases j with ⟨i, hi⟩
    cases i with
    | zero =>
        have hrec : (V[0]'(by simp [V])).input = R[b.val].input := by
          simp only [V, List.getElem_cons_zero]
        have hdate := hBirthDate
        have hphase := hBirthPhase
        have hdate' : R[b.val].input.time.val = s + b.val := by
          simpa only [s] using hdate
        have hrecord : V[0]'(by simp [V]) = R[b.val] := by
          simp only [V, List.getElem_cons_zero]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simpa only [Nat.add_zero, V, List.getElem_cons_zero] using
            (List.getElem?_eq_getElem b.isLt)
        · change R[b.val].input.time.val + 1 = s + b.val + 0 + 1
          simpa [Nat.add_assoc] using congrArg (fun t : ℕ => t + 1) hdate'
        · simpa only [hrecord] using hBirthLookup
        · exact hprepEq R[b.val]
        · exact hphase.1
        · exact hphase.2.1
        · exact hphase.2.2.1
        · exact hphase.2.2.2.1
        · exact hphase.2.2.2.2
        · left
          refine ⟨rfl, ?_, ?_⟩
          · simpa only [hrec] using hbLater
          · exact ⟨birthPayload, birthLedger, birthSaved, by simpa only [hrec] using hBirthState⟩
        · simpa only [hrec] using hBirthNoStart
    | succ n =>
        have hn : n < W.length := by
          simp only [V, List.length_cons] at hi
          omega
        rcases htail with hterminal | ⟨k, hk, hkstate, hframes⟩
        · have : W.length = 0 := by
            have hterminalR : b.val + 1 = R.length := by simpa only [R] using hterminal
            rw [hterminalR] at hWle
            simp only [Nat.sub_self] at hWle
            omega
          rw [this] at hn
          omega
        · have hWk : ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
              rate rewards C_star C_h z k.val = W := by
            simp only [W, hk]
          have hnPrefix : n < (ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
              rate rewards C_star C_h z k.val).length := by
            simpa only [hWk] using hn
          have hWbound := ReferenceCompleteLaterLiveComplementPrefixReplay.prefix_length_le
            (rate := rate) rewards C_star C_h z k
          have hindex : b.val + (n + 1) < R.length := by omega
          let r := V[n + 1]
          have hrec : r = R[b.val + (n + 1)] := by
            have hprefix := ReferenceCompleteLaterLiveComplementPrefixReplay.prefix_index
              (rate := rate) rewards C_star C_h z k n hnPrefix
            have hsum : k.val + n = b.val + (n + 1) := by omega
            have hprefixW : W[n] = R[b.val + (n + 1)] := by
              simpa only [hWk, hsum, Nat.add_assoc] using hprefix
            change (R[b.val] :: W)[n + 1] = R[b.val + (n + 1)]
            rw [List.getElem_cons_succ]
            exact hprefixW
          have hrecV : V[n + 1] = R[b.val + (n + 1)] := by
            simpa only [r] using hrec
          have hgetW := hframes ⟨n, hnPrefix⟩
          obtain ⟨registers, owned, _selected, _next, _ownedNext, hstateW,
            _hpayloadW, _hselectedW, _hselectedPayloadW, _hselectedPendingW,
            _hnextW, _hnextPayloadW, _hnextPendingW⟩ := hgetW
          have hstateR : (R[b.val + (n + 1)]).input.state.coordinator =
              .live registers owned birthBase := by
            have hstateV : (V[n + 1]).input.state.coordinator =
                .live registers owned birthBase := by
              simpa only [V, List.getElem_cons_succ, hWk] using hstateW
            simpa only [hrecV] using hstateV
          let jR : Fin R.length := ⟨b.val + (n + 1), hindex⟩
          have hlookup := complete_suffix_record_actual_lookup rate rewards C_star C_h z jR
          have hdate := complete_suffix_record_source_date rate rewards C_star C_h z jR
          have hphase := complete_suffix_record_phase_exhaustion rate rewards C_star C_h z jR
          have hlookupR : ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualRecordAt
              rate rewards C_star C_h (R[b.val + (n + 1)]).input.time z =
              some (R[b.val + (n + 1)]) := by
            simpa only [jR, Fin.val_mk] using hlookup
          have hlookupV : ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualRecordAt
              rate rewards C_star C_h r.input.time z = some r := by
            rw [hrec]
            exact hlookupR
          have hdate' : (R[b.val + (n + 1)]).input.time.val =
              s + b.val + (n + 1) := by
            simpa only [jR, Fin.val_mk, s, Nat.add_assoc] using hdate
          have hdateV : r.input.time.val = s + b.val + (n + 1) := by
            rw [hrec]
            exact hdate'
          have hphaseV :
              r.input.state.coordinator ≠ .dagger ∧
              r.output.preparation.coordinator.selection ≠ none ∧
              r.output.coordinator.failure = none ∧
              r.output.next.coordinator ≠ .first ∧
              r.output.next.coordinator ≠ .dagger := by
            have hphaseR :
                (R[b.val + (n + 1)]).input.state.coordinator ≠ .dagger ∧
                (R[b.val + (n + 1)]).output.preparation.coordinator.selection ≠ none ∧
                (R[b.val + (n + 1)]).output.coordinator.failure = none ∧
                (R[b.val + (n + 1)]).output.next.coordinator ≠ .first ∧
                (R[b.val + (n + 1)]).output.next.coordinator ≠ .dagger := by
              simpa only [jR, Fin.val_mk] using hphase
            rw [hrec]
            exact hphaseR
          have hroot := ReferenceCompleteLiveChoiceDomains.complete_live_dispatch_choice_exists
            rate rewards C_star C_h z jR registers owned birthBase hstateR
          dsimp only at hroot
          rcases hroot with ⟨hprepRoot, hbranches⟩
          have hprepRootR : (ReferenceActivePhysicalStep.prepare
              (R[b.val + (n + 1)]).input).coordinator =
              .live registers owned birthBase
                (CoordinatorRoundDispatch.dispatchLive
                  (ReferenceActivePhysicalStep.liveInput
                    (R[b.val + (n + 1)]).input registers owned birthBase)) := by
            simpa only [jR, Fin.val_mk] using hprepRoot
          have hprepRoot' : (ReferenceActivePhysicalStep.prepare r.input).coordinator =
              .live registers owned birthBase
                (CoordinatorRoundDispatch.dispatchLive
                  (ReferenceActivePhysicalStep.liveInput r.input registers owned birthBase)) := by
            rw [hrec]
            exact hprepRootR
          have hprep : r.output.preparation = ReferenceActivePhysicalStep.prepare r.input :=
            hprepEq r
          have hdispatch : r.output.preparation.coordinator =
              .live registers owned birthBase
                (CoordinatorRoundDispatch.dispatchLive
                  (ReferenceActivePhysicalStep.liveInput r.input registers owned birthBase)) := by
            rw [hprep]
            exact hprepRoot'
          have hdispatchR : (R[b.val + (n + 1)]).output.preparation.coordinator =
              .live registers owned birthBase
                (CoordinatorRoundDispatch.dispatchLive
                  (ReferenceActivePhysicalStep.liveInput
                    (R[b.val + (n + 1)]).input registers owned birthBase)) := by
            rw [hprepEq (R[b.val + (n + 1)])]
            exact hprepRootR
          have hbranchesR := hbranches
          dsimp only [jR, Fin.val_mk] at hbranchesR
          have htestW := ReferenceCompleteLaterLiveComplementPrefixReplay.prefix_test
            (rate := rate) rewards C_star C_h z k n hnPrefix
          have htest : ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest r = true := by
            simpa only [r, V, List.getElem_cons_succ, hWk] using htestW
          have htestR : ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest
              (R[b.val + (n + 1)]) = true := by
            rw [hrec] at htest
            exact htest
          have hnoStart : ¬ ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferStartAt
              rate rewards C_star C_h r.input.time z := by
            cases hdispatchResult : CoordinatorRoundDispatch.dispatchLive
                (ReferenceActivePhysicalStep.liveInput
                  (R[b.val + (n + 1)]).input registers owned birthBase) with
            | continuingChosen dispatched hstart continuation selection =>
                rw [hdispatchResult] at hbranchesR
                rcases hbranchesR with ⟨_hframe, hu, _rest⟩
                have hstart' : CoordinatorPhaseClock.startRound p rate.eta.val
                    (R[b.val + (n + 1)]).input.time registers.priorClock
                    registers.clockPending = .ok dispatched.startResult := by
                  simpa [ReferenceActivePhysicalStep.liveInput,
                    ReferenceActivePhysicalStep.liveRegistersAt,
                    CoordinatorLiveChoiceRecorderStep.Registers.clockPending_eq] using hstart
                have hnoStartR := actual_no_transfer_start_of_live_no_initializeAt
                  rate rewards C_star C_h z (R[b.val + (n + 1)]) registers owned birthBase
                  hlookupR hstateR dispatched.startResult hstart' hu
                rw [hrec]
                exact hnoStartR
            | cutoffChosen =>
                simp only [ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest,
                  hdispatchR, hdispatchResult] at htestR
                cases htestR
            | clockFailure =>
                simp only [ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest,
                  hdispatchR, hdispatchResult] at htestR
                cases htestR
            | initializerFailure =>
                simp only [ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest,
                  hdispatchR, hdispatchResult] at htestR
                cases htestR
            | localFailure =>
                simp only [ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest,
                  hdispatchR, hdispatchResult] at htestR
                cases htestR
          refine ⟨?_, ?_, hlookupV, hprep, hphaseV.1, hphaseV.2.1,
            hphaseV.2.2.1, hphaseV.2.2.2.1, hphaseV.2.2.2.2, ?_, hnoStart⟩
          · simpa only [hrecV] using (List.getElem?_eq_getElem jR.isLt)
          · change r.input.time.val + 1 = s + b.val + (n + 1) + 1
            omega
          · right
            refine ⟨by simp, htest, registers, owned, birthBase, ?_, ?_, ?_⟩
            · simpa only [← hrec] using hstateR
            · exact hdispatch
            · refine ⟨CoordinatorRoundDispatch.dispatchLive
                (ReferenceActivePhysicalStep.liveInput r.input registers owned birthBase),
                rfl, ?_⟩
              cases hdispatchResult : CoordinatorRoundDispatch.dispatchLive
                  (ReferenceActivePhysicalStep.liveInput r.input registers owned birthBase) with
              | continuingChosen dispatched hstart continuation selection =>
                  exact ⟨hstart,
                    (by
                      rcases continuation.clockFrame with ⟨_, _, hcommand, _⟩
                      exact hcommand)⟩
              | cutoffChosen => simp [ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest,
                  hdispatch, hdispatchResult] at htest ⊢
              | clockFailure => simp [ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest,
                  hdispatch, hdispatchResult] at htest ⊢
              | initializerFailure => simp [ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest,
                  hdispatch, hdispatchResult] at htest ⊢
              | localFailure => simp [ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest,
                  hdispatch, hdispatchResult] at htest ⊢
  rcases htail with hterminal | ⟨k, hk, hkstate, hframes⟩
  · have hWnil : W = [] := by
      apply List.length_eq_zero_iff.mp
      have hterminalR : b.val + 1 = R.length := by
        simpa only [R] using hterminal
      rw [hterminalR] at hWle
      simp only [Nat.sub_self] at hWle
      omega
    have hinterval := hbirthInterval
    have hend : b.val + V.length = R.length := by
      simp only [V, List.length_cons, hWnil]
      have hterminalR : b.val + 1 = R.length := by
        simpa only [R] using hterminal
      omega
    exact ⟨hinterval, Or.inl hend⟩
  · have hWk : ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
        rate rewards C_star C_h z k.val = W := by
      simp only [W, hk]
    have hmax := ReferenceCompleteLaterLiveComplementPrefixReplay.prefix_maximal
      (rate := rate) rewards C_star C_h z k birthRegisters birthOwned birthBase hkstate hlater
    have hlength : (ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
        rate rewards C_star C_h z k.val).length = W.length := by
      rw [hWk]
    rcases hmax with hend | ⟨hnext, registers, owned, _hpayload, hstateNext,
      outcome, hpreparedNext, hcutoffOutcome⟩
    · have hend' : b.val + V.length = R.length := by
        simp only [V, List.length_cons]
        have hendK : k.val + W.length = R.length := by
          simpa only [hWk] using hend
        rw [hk] at hendK
        omega
      exact ⟨hbirthInterval, Or.inl hend'⟩
    · let e : Fin R.length := ⟨k.val +
        (ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
          rate rewards C_star C_h z k.val).length, hnext⟩
      have heval : e.val = b.val + V.length := by
        dsimp only [e, V, List.length_cons]
        omega
      have hstateE : (R[e.val]).input.state.coordinator = .live registers owned birthBase := by
        simpa only [e] using hstateNext
      have hlookupE := complete_suffix_record_actual_lookup rate rewards C_star C_h z e
      have hdateE := complete_suffix_record_source_date rate rewards C_star C_h z e
      have hphaseE := complete_suffix_record_phase_exhaustion rate rewards C_star C_h z e
      have hprepE := hprepEq R[e.val]
      have hcutE : ReferenceCollectionPhaseHistory.cutoffChosen R[e.val].input = true := by
        unfold ReferenceCollectionPhaseHistory.cutoffChosen
        rw [← hprepE, hpreparedNext]
        cases outcome <;> cases hcutoffOutcome
        rfl
      have hroot := ReferenceCompleteLiveChoiceDomains.complete_live_dispatch_choice_exists
        rate rewards C_star C_h z e registers owned birthBase hstateE
      dsimp only at hroot
      rcases hroot with ⟨hprepRoot, hbranches⟩
      have hdispatchE : R[e.val].output.preparation.coordinator =
          .live registers owned birthBase
            (CoordinatorRoundDispatch.dispatchLive
              (ReferenceActivePhysicalStep.liveInput R[e.val].input registers owned birthBase)) := by
        rw [hprepE]
        exact hprepRoot
      have hcutoffActual : match
          CoordinatorRoundDispatch.dispatchLive
            (ReferenceActivePhysicalStep.liveInput R[e.val].input registers owned birthBase) with
          | .cutoffChosen .. => True
          | _ => False := by
        unfold ReferenceCollectionPhaseHistory.cutoffChosen at hcutE
        rw [← hprepE, hdispatchE] at hcutE
        cases hresult : CoordinatorRoundDispatch.dispatchLive
            (ReferenceActivePhysicalStep.liveInput R[e.val].input registers owned birthBase) <;>
          simp [hresult] at hcutE ⊢
      have hcommandStart : ∃ started,
          CoordinatorPhaseClock.startRound p rate.eta.val R[e.val].input.time
            registers.priorClock registers.clockPending = .ok started ∧
          started.ledgerCommand = some (.initializeAt R[e.val].input.time) := by
        cases hresult : CoordinatorRoundDispatch.dispatchLive
            (ReferenceActivePhysicalStep.liveInput R[e.val].input registers owned birthBase) with
        | cutoffChosen dispatched hstart ledger hinitialization hledger hdomains hclock
            hpending hassignment selection =>
            rw [hresult] at hbranches
            rcases hbranches with ⟨hcommand, _rest⟩
            have hstart' : CoordinatorPhaseClock.startRound p rate.eta.val R[e.val].input.time
                registers.priorClock registers.clockPending = .ok dispatched.startResult := by
              simpa [ReferenceActivePhysicalStep.liveInput,
                ReferenceActivePhysicalStep.liveRegistersAt,
                CoordinatorLiveChoiceRecorderStep.Registers.clockPending_eq] using hstart
            exact ⟨dispatched.startResult, hstart', hcommand⟩
        | continuingChosen => simp [hresult] at hcutoffActual
        | clockFailure => simp [hresult] at hcutoffActual
        | initializerFailure => simp [hresult] at hcutoffActual
        | localFailure => simp [hresult] at hcutoffActual
      obtain ⟨started, hstart, hcommand⟩ := hcommandStart
      have hliveStart : ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferLiveStartAt
          rate rewards C_star C_h R[e.val].input.time z := by
        apply (ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferLiveStartAt_iff
          rate rewards C_star C_h R[e.val].input.time z).mpr
        exact ⟨R[e.val], registers, owned, birthBase, started,
          hlookupE, hstateE, hstart, hcommand⟩
      have hinterval := hbirthInterval
      have hlookupOut := hlookupE
      have hdateOut := hdateE
      have hphaseOut := hphaseE
      have hprepOut := hprepE
      refine ⟨hinterval, Or.inr ⟨e, heval, ?_, ?_, hlookupOut, hprepOut,
        hphaseOut.1, hphaseOut.2.1, hphaseOut.2.2.1, hphaseOut.2.2.2.1,
        hphaseOut.2.2.2.2, hcutE, registers, owned, birthBase, hstateE,
        hdispatchE, ?_, hliveStart⟩⟩
      · exact List.getElem?_eq_getElem e.isLt
      · change R[e.val].input.time.val + 1 = s + e.val + 1
        have hdateE' : R[e.val].input.time.val = s + e.val := by
          simpa only [R, s] using hdateE
        exact congrArg (fun t : ℕ => t + 1) hdateE'
      · exact ⟨started, hstart, hcommand⟩

end Bandits.Support.ReferenceOriginalInstalledLiveStartExclusion

end
