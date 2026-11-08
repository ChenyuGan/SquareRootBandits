/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceOriginalStoppedPhysicalTransferStarts
public import Bandits.Support.ReferencePostReplacementCollectionReleaseBoundary
public import Bandits.Support.ReferenceCompleteOriginalCalendarRawLearningComparison

import Mathlib.Data.List.GetD
import Mathlib.Data.List.TakeWhile
import Mathlib.Tactic

/-!
# Raw geometry of the original initial-transfer window

This module records the actual first-live window on the complete source
calendar before applying any analytical bad-date restriction.  Its dates,
selections, pending sets, and boundary records all come from the same original
run and the same source input.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support
open Bandits.Support.ReferenceActivePhysicalStep
open scoped Classical

namespace Bandits.Support.ReferenceOriginalInitialTransferWindowGeometry

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ)

abbrev SourceInput (p : ConstructorDimensions.Parameters) := BootstrapPrivateRoundStreams.SourceInput p
abbrev Record := ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)

public def rawInitialTransferWindow (z : SourceInput p) :=
  ReferenceFirstLiveSourceStoppedHandoverEndpoint.window rate rewards C_star C_h z

public def rawCompleteSuffixRecords (z : SourceInput p) :=
  ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h

/-- The first zero-based index whose actual choice-time missing set is empty,
or the length of the raw window if it remains nonempty through the window. -/
def rawMissingPrefixLength (z : SourceInput p) : ℕ :=
  ((rawInitialTransferWindow rate rewards C_star C_h z).takeWhile
    ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice).length

/-- The one-based date immediately after the raw initial-transfer window.
It is the actual first excluded record's date when one exists, and `T + 1`
when the original suffix is exhausted. -/
def rawInitialTransferWindowFirstExcludedDate (z : SourceInput p) : ℕ :=
  ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart rate rewards C_star C_h z +
    (rawInitialTransferWindow rate rewards C_star C_h z).length + 1

private theorem crossing_of_nonempty_window (z : SourceInput p)
    (hne : 0 < (rawInitialTransferWindow rate rewards C_star C_h z).length) :
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true := by
  cases hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h with
  | none =>
      change 0 < (ReferenceFirstLiveSourceStoppedHandoverEndpoint.window
        rate rewards C_star C_h z).length at hne
      rw [ReferenceFirstLiveSourceStoppedHandoverEndpoint.window_eq_nil_of_no_launch
        rate rewards C_star C_h z hlaunch] at hne
      simp at hne
  | some active =>
      exact (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
        rate z rewards C_star C_h).mp (by simp [hlaunch])

private theorem raw_window_provenance_of_nonempty (z : SourceInput p)
    (hne : 0 < (rawInitialTransferWindow rate rewards C_star C_h z).length) :
    let window := rawInitialTransferWindow rate rewards C_star C_h z
    window.length = 0 ∨
      ∃ hW : 0 < window.length,
      ∃ firstInstalled : CoordinatorAssignmentRegisterInstall.FirstInstallation
        (CoordinatorRoundDispatch.firstLaunchInput
          (ReferenceActivePhysicalStep.firstInput (window.get ⟨0, hW⟩).input)),
      ∃ firstSelected : ReferenceActivePhysicalStep.Selection (window.get ⟨0, hW⟩).input,
        (window.get ⟨0, hW⟩).output.preparation.coordinator.selection = some firstSelected ∧
        firstInstalled = CoordinatorAssignmentRegisterInstall.installFirst
          (CoordinatorRoundDispatch.firstLaunchInput
            (ReferenceActivePhysicalStep.firstInput ((window.get ⟨0, hW⟩).input))) ∧
        firstSelected.view.payload = firstInstalled.registers.payload ∧
        firstSelected.view.pendingAtChoice = Finset.univ ∧
        ReferenceFirstLiveSourceStoppedHandoverEndpoint.payload0 rate rewards C_star C_h z =
          some firstInstalled.registers.payload ∧
        (∀ k : Fin window.length,
          let r := window.get k
          ∃ selected : ReferenceActivePhysicalStep.Selection r.input,
            r.output.preparation.coordinator.selection = some selected ∧
            selected.view.payload = firstInstalled.registers.payload ∧
            (match r.input.state.coordinator with
              | .first => selected.view.pendingAtChoice = Finset.univ
              | .live incoming _ _ =>
                  selected.view.payload = incoming.payload ∧
                  selected.view.pendingAtChoice = incoming.pendingAtChoice
              | _ => False) ∧
            ∃ next : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta,
            ∃ owned : CoordinatorLiveServiceFinish.OwnedRegisters next,
            ∃ base : Fin (p.m - 1) → ℕ,
              r.output.next.coordinator = .live next owned base ∧
              next.payload = selected.view.payload ∧
              next.pendingAtChoice =
                (if ReferenceFirstLiveMissingSetProvenance.actualDownConfirmationEvent r selected then
                  selected.view.pendingAtChoice.erase
                    (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
                      (r.input.row.2 r.input.time).1)
                else selected.view.pendingAtChoice) ∧
              r.output.coordinator.failure = none ∧
              (∀ i : Fin (p.m - 1),
                ∃ choice choiceMemory nextFollower nextMemory,
                  (r.output.preparation.followers.followers i).configuration =
                    .ordinary choice choiceMemory ∧
                  (r.output.followers i).configuration =
                    .ordinary nextFollower nextMemory ∧
                  (r.output.followers i).failure = none)) := by
  exact ReferenceFirstLiveSourceStoppedHandoverEndpoint.source_window_provenance
    rate rewards C_star C_h z (crossing_of_nonempty_window rate rewards C_star C_h z hne)

/-- The actual raw-window provenance, obtained from the computed corrected
launch.  No launch or terminal launch gives the empty window; a nonterminal
launch supplies the original first installation and every actual selected
record/update on this same window. -/
theorem raw_initial_transfer_window_provenance (z : SourceInput p) :
    let window := rawInitialTransferWindow rate rewards C_star C_h z
    window.length = 0 ∨
      ∃ hW : 0 < window.length,
      ∃ firstInstalled : CoordinatorAssignmentRegisterInstall.FirstInstallation
        (CoordinatorRoundDispatch.firstLaunchInput
          (ReferenceActivePhysicalStep.firstInput (window.get ⟨0, hW⟩).input)),
      ∃ firstSelected : ReferenceActivePhysicalStep.Selection (window.get ⟨0, hW⟩).input,
        (window.get ⟨0, hW⟩).output.preparation.coordinator.selection = some firstSelected ∧
        firstInstalled = CoordinatorAssignmentRegisterInstall.installFirst
          (CoordinatorRoundDispatch.firstLaunchInput
            (ReferenceActivePhysicalStep.firstInput ((window.get ⟨0, hW⟩).input))) ∧
        firstSelected.view.payload = firstInstalled.registers.payload ∧
        firstSelected.view.pendingAtChoice = Finset.univ ∧
        ReferenceFirstLiveSourceStoppedHandoverEndpoint.payload0 rate rewards C_star C_h z =
          some firstInstalled.registers.payload ∧
        (∀ k : Fin window.length,
          let r := window.get k
          ∃ selected : ReferenceActivePhysicalStep.Selection r.input,
            r.output.preparation.coordinator.selection = some selected ∧
            selected.view.payload = firstInstalled.registers.payload ∧
            (match r.input.state.coordinator with
              | .first => selected.view.pendingAtChoice = Finset.univ
              | .live incoming _ _ =>
                  selected.view.payload = incoming.payload ∧
                  selected.view.pendingAtChoice = incoming.pendingAtChoice
              | _ => False) ∧
            ∃ next : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta,
            ∃ owned : CoordinatorLiveServiceFinish.OwnedRegisters next,
            ∃ base : Fin (p.m - 1) → ℕ,
              r.output.next.coordinator = .live next owned base ∧
              next.payload = selected.view.payload ∧
              next.pendingAtChoice =
                (if ReferenceFirstLiveMissingSetProvenance.actualDownConfirmationEvent r selected then
                  selected.view.pendingAtChoice.erase
                    (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
                      (r.input.row.2 r.input.time).1)
                else selected.view.pendingAtChoice) ∧
              r.output.coordinator.failure = none ∧
              (∀ i : Fin (p.m - 1),
                ∃ choice choiceMemory nextFollower nextMemory,
                  (r.output.preparation.followers.followers i).configuration =
                    .ordinary choice choiceMemory ∧
                  (r.output.followers i).configuration =
                    .ordinary nextFollower nextMemory ∧
                  (r.output.followers i).failure = none)) := by
  by_cases hwindow : 0 < (rawInitialTransferWindow rate rewards C_star C_h z).length
  · exact raw_window_provenance_of_nonempty rate rewards C_star C_h z hwindow
  · exact Or.inl (Nat.eq_zero_of_not_pos hwindow)

/-- Each raw window index is the actual original record at its original
calendar date, exactly as in the complete-source lookup. -/
theorem raw_window_record_calendar (z : SourceInput p)
    (k : Fin (rawInitialTransferWindow rate rewards C_star C_h z).length) :
    let r := (rawInitialTransferWindow rate rewards C_star C_h z)[k.val]
    r.input.time.val =
        ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart rate rewards C_star C_h z + k.val ∧
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
        r.input.time z = some r :=
  ReferenceFirstLiveSourceStoppedHandoverEndpoint.source_window_record_calendar
    rate rewards C_star C_h z k

/-- The literal raw window is the takeWhile prefix of the actual complete
suffix, using only the actual collection cutoff predicate. -/
theorem raw_window_eq_complete_suffix_takeWhile (z : SourceInput p) :
    rawInitialTransferWindow rate rewards C_star C_h z =
      (rawCompleteSuffixRecords rate rewards C_star C_h z).takeWhile
        (fun r => !ReferenceCollectionPhaseHistory.cutoffChosen r.input) := by
  simp [rawInitialTransferWindow, rawCompleteSuffixRecords,
    ReferenceFirstLiveSourceStoppedHandoverEndpoint.window,
    ReferenceFirstLiveSourceStoppedHandoverEndpoint.completeRecords,
    ReferenceFirstLiveSourceStoppedReleaseEndpoint.completeRecords,
    ReferenceFirstLiveConfirmationHistory.firstLiveWindow]

/-- Every retained raw record precedes the actual collection cutoff. -/
theorem raw_window_no_collection_choice (z : SourceInput p)
    (k : Fin (rawInitialTransferWindow rate rewards C_star C_h z).length) :
    ReferenceCollectionPhaseHistory.cutoffChosen
      ((rawInitialTransferWindow rate rewards C_star C_h z)[k.val]).input = false :=
  ReferenceFirstLiveSourceStoppedHandoverEndpoint.source_window_no_cutoff
    rate rewards C_star C_h z k

/-- The first raw record is the actual launch marker and starts with every
follower missing. -/
theorem raw_window_first_is_initial_marker (z : SourceInput p)
    (hW : 0 < (rawInitialTransferWindow rate rewards C_star C_h z).length) :
    ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferInitialMarkerAt
        rate rewards C_star C_h ((rawInitialTransferWindow rate rewards C_star C_h z)[0]).input.time z ∧
      ReferenceFirstLiveSourceStoppedHandoverEndpoint.missing rate
        ((rawInitialTransferWindow rate rewards C_star C_h z)[0]) = Finset.univ := by
  have htime := (raw_window_record_calendar rate rewards C_star C_h z ⟨0, hW⟩).1
  have hmarker :=
    ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferInitialMarkerAt_of_launch
      rate rewards C_star C_h
      ((rawInitialTransferWindow rate rewards C_star C_h z)[0]).input.time z htime
  have hmissing := ReferenceFirstLiveSourceStoppedHandoverEndpoint.source_window_initial_missing
    rate rewards C_star C_h z (by simpa only [rawInitialTransferWindow] using hW)
  exact ⟨hmarker, by simpa only [rawInitialTransferWindow, List.get_eq_getElem] using hmissing⟩

/-- With no corrected launch, the raw suffix and its first-live window are
empty. -/
theorem raw_window_empty_of_no_launch (z : SourceInput p)
    (hnone : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h = none) :
    rawInitialTransferWindow rate rewards C_star C_h z = [] := by
  simpa only [rawInitialTransferWindow] using
    ReferenceFirstLiveSourceStoppedHandoverEndpoint.window_eq_nil_of_no_launch
      rate rewards C_star C_h z hnone

/-- A terminal corrected crossing has an empty physical suffix, hence an
empty raw first-live window. -/
theorem raw_window_empty_of_terminal_crossing (z : SourceInput p)
    (active : ReferenceCompletePhysicalHistory.State p rate)
    (hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h = some active)
    (hterminal : ReferenceCompletePhysicalHistory.physicalStart
      rate z rewards C_star C_h = p.T) :
    rawInitialTransferWindow rate rewards C_star C_h z = [] := by
  have hhistory := ReferenceCompletePhysicalHistory.terminal_crossing_complete_history
    rate z rewards C_star C_h active hlaunch hterminal
  have hrecords : ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h = [] := hhistory.1
  simp [rawInitialTransferWindow,
    ReferenceFirstLiveSourceStoppedHandoverEndpoint.window,
    ReferenceFirstLiveSourceStoppedHandoverEndpoint.completeRecords,
    ReferenceFirstLiveSourceStoppedReleaseEndpoint.completeRecords,
    ReferenceFirstLiveConfirmationHistory.firstLiveWindow, hrecords]

/-- The no-launch branch retains the one-based terminal sentinel `T + 1`. -/
theorem raw_window_sentinel_of_no_launch (z : SourceInput p)
    (hnone : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h = none) :
    rawInitialTransferWindowFirstExcludedDate rate rewards C_star C_h z = p.T + 1 := by
  have hstart := ReferenceCompletePhysicalHistory.correctedLaunch_none_start_eq_T
    rate z rewards C_star C_h hnone
  rw [rawInitialTransferWindowFirstExcludedDate,
    raw_window_empty_of_no_launch rate rewards C_star C_h z hnone]
  simp [ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart, hstart]

/-- A terminal corrected crossing also retains the one-based terminal
sentinel, without manufacturing a release record. -/
theorem raw_window_sentinel_of_terminal_crossing (z : SourceInput p)
    (active : ReferenceCompletePhysicalHistory.State p rate)
    (hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h = some active)
    (hterminal : ReferenceCompletePhysicalHistory.physicalStart
      rate z rewards C_star C_h = p.T) :
    rawInitialTransferWindowFirstExcludedDate rate rewards C_star C_h z = p.T + 1 := by
  rw [rawInitialTransferWindowFirstExcludedDate,
    raw_window_empty_of_terminal_crossing rate rewards C_star C_h z active hlaunch hterminal]
  simp [ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart, hterminal]

private theorem actual_live_initializeAt_cutoff
    (z : SourceInput p)
    (i : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
    (base : Fin (p.m - 1) → ℕ)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (hstate : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[i.val].input.state.coordinator =
      .live registers owned base)
    (hstart : CoordinatorPhaseClock.startRound p rate.eta.val
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[i.val].input.time
      registers.priorClock registers.clockPending = .ok started)
    (hcommand : started.ledgerCommand = some (.initializeAt
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[i.val].input.time)) :
    ReferenceCollectionPhaseHistory.cutoffChosen
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[i.val].input = true := by
  let r := (ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate z rewards C_star C_h)[i.val]
  obtain ⟨hprepared, hbranch⟩ :=
    ReferenceCompleteLiveChoiceDomains.complete_live_dispatch_choice_exists
      rate rewards C_star C_h z i registers owned base hstate
  change (prepare r.input).coordinator = _ at hprepared
  cases hd : CoordinatorRoundDispatch.dispatchLive (liveInput r.input registers owned base) with
  | continuingChosen dispatched hs continuation selection =>
      rw [hd] at hbranch
      have hsame : dispatched.startResult = started := Except.ok.inj (hs.symm.trans hstart)
      have hshape := CoordinatorStartRoundCutoffDispatch.startRound_initializeAt_shape
        (liveRegistersAt registers r.input.time) started hstart hcommand
      have hu := hbranch.2.1
      rw [hsame, hshape.1] at hu
      cases hu
  | cutoffChosen dispatched hs ledger hinit hledger hdomain hclock hpending hnone selected =>
      rw [hd] at hprepared
      change ReferenceCollectionPhaseHistory.cutoffChosen r.input = true
      unfold ReferenceCollectionPhaseHistory.cutoffChosen
      rw [hprepared]
  | clockFailure => rw [hd] at hbranch; exact False.elim hbranch
  | initializerFailure dispatched hstart checked hchecked =>
      rw [hd] at hbranch
      exact False.elim hbranch
  | localFailure dispatched hstart reason => rw [hd] at hbranch; exact False.elim hbranch

/-- No actual physical transfer starts occur at positive positions of this
raw first-live window. The first position is handled by the genuine launch
marker, while every later live `initializeAt` would be the first cutoff and
therefore lies beyond the window. -/
theorem raw_window_no_positive_transfer_start (z : SourceInput p)
    (k : Fin (rawInitialTransferWindow rate rewards C_star C_h z).length)
    (hkpos : 0 < k.val) :
    ¬ ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferStartAt
      rate rewards C_star C_h ((rawInitialTransferWindow rate rewards C_star C_h z)[k.val]).input.time z := by
  let W := rawInitialTransferWindow rate rewards C_star C_h z
  let r := W[k.val]
  have hkW : k.val < W.length := by simpa only [W] using k.isLt
  let prev : Fin (rawInitialTransferWindow rate rewards C_star C_h z).length :=
    ⟨k.val - 1, by have := k.isLt; omega⟩
  have hprev : prev.val + 1 <
      (rawInitialTransferWindow rate rewards C_star C_h z).length := by
    dsimp only [prev]
    have := k.isLt
    omega
  have hpk : prev.val + 1 = k.val := by dsimp only [prev]; omega
  have hW : 0 < W.length := by omega
  have hprovenance := raw_window_provenance_of_nonempty rate rewards C_star C_h z hW
  dsimp only at hprovenance
  rcases hprovenance with hzero | ⟨_, installed, firstSelected, _, _, _, _, _, hrows⟩
  · have := k.isLt
    simp [hzero] at this
  · obtain ⟨_, _, _, _, next, owned, base, hnext, _, _, _, _⟩ := hrows prev
    have hlink := ReferenceFirstLiveSourceStoppedHandoverEndpoint.source_window_successor
      rate rewards C_star C_h z prev.val (by
        simpa only [rawInitialTransferWindow] using hprev)
    have hlink' : (rawInitialTransferWindow rate rewards C_star C_h z)[prev.val + 1].input.state =
        (rawInitialTransferWindow rate rewards C_star C_h z)[prev.val].output.next := by
      change (rawInitialTransferWindow rate rewards C_star C_h z)[prev.val + 1].input.state =
        (rawInitialTransferWindow rate rewards C_star C_h z)[prev.val].output.next
      exact hlink
    have hrecordIndex : (rawInitialTransferWindow rate rewards C_star C_h z)[k.val] =
        (rawInitialTransferWindow rate rewards C_star C_h z)[prev.val + 1] := by
      simp only [hpk.symm]
    have hlive : r.input.state.coordinator = .live next owned base := by
      change (rawInitialTransferWindow rate rewards C_star C_h z)[k.val].input.state.coordinator =
        .live next owned base
      calc
        _ = (rawInitialTransferWindow rate rewards C_star C_h z)[prev.val + 1].input.state.coordinator :=
          congrArg (fun record => record.input.state.coordinator) hrecordIndex
        _ = .live next owned base :=
          (congrArg (fun state => state.coordinator) hlink').trans hnext
    have hlookup : ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualRecordAt
        rate rewards C_star C_h r.input.time z = some r := by
      change ReferenceSourcePrefixHistoryFiltration.actualRecord
        rate rewards C_star C_h r.input.time z = some r
      exact (raw_window_record_calendar rate rewards C_star C_h z k).2
    rintro (hfirst | hliveStart)
    · obtain ⟨record, hrecord, hstate⟩ :=
        (ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferInitialMarkerAt_iff_record_first
          rate rewards C_star C_h r.input.time z).mp hfirst
      have heq : record = r := Option.some.inj (hrecord.symm.trans hlookup)
      subst record
      rw [hlive] at hstate
      cases hstate
    · obtain ⟨record, registers, liveOwned, liveBase, started, hrecord, hstate,
          hstart, hcommand⟩ :=
        (ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferLiveStartAt_iff
          rate rewards C_star C_h r.input.time z).mp hliveStart
      have heq : record = r := Option.some.inj (hrecord.symm.trans hlookup)
      subst record
      obtain ⟨i, hsame⟩ :=
        ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualRecord_suffix_index
          rate rewards C_star C_h r.input.time z r hlookup
      have hstateR : (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)[i.val].input.state.coordinator =
          .live registers liveOwned liveBase := by
        exact (congrArg (fun record => record.input.state.coordinator) hsame).trans hstate
      have htimeR : (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)[i.val].input.time = r.input.time :=
        congrArg (fun record => record.input.time) hsame
      have hstartR := hstart
      have hcommandR := hcommand
      rw [← htimeR] at hstartR hcommandR
      have hcut := actual_live_initializeAt_cutoff rate rewards C_star C_h z i
        registers liveOwned liveBase started hstateR hstartR hcommandR
      have hinputR : (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)[i.val].input = r.input :=
        congrArg (fun record => record.input) hsame
      have hcut' : ReferenceCollectionPhaseHistory.cutoffChosen r.input = true := by
        rw [← hinputR]
        exact hcut
      have hnocut := ReferenceFirstLiveSourceStoppedHandoverEndpoint.source_window_no_cutoff
        rate rewards C_star C_h z k
      have hnocut' : ReferenceCollectionPhaseHistory.cutoffChosen r.input = false := by
        simpa only [r, W, rawInitialTransferWindow] using hnocut
      exact Bool.noConfusion (hcut'.symm.trans hnocut')

private theorem takeWhile_getElem_eq_true_iff {α : Type*}
    (test : α → Bool) (xs : List α)
    (hanti : ∀ i j (hi : i < xs.length) (hj : j < xs.length),
      i ≤ j → test (xs.get ⟨j, hj⟩) = true → test (xs.get ⟨i, hi⟩) = true)
    (k : ℕ) (hk : k < xs.length) :
    test (xs.get ⟨k, hk⟩) = true ↔ k < (xs.takeWhile test).length := by
  induction xs generalizing k with
  | nil => simp at hk
  | cons head tail ih =>
      cases hhead : test head with
      | false =>
          cases k with
          | zero => simp [hhead]
          | succ k =>
              have hk' : k < tail.length := by simp at hk; omega
              have hfalse : test (tail.get ⟨k, hk'⟩) ≠ true := by
                intro htrue
                have hback := hanti 0 (k + 1) (by simp) (by simp [hk'])
                  (by omega) (by simpa using htrue)
                simp [hhead] at hback
              cases hv : test (tail.get ⟨k, hk'⟩) with
              | false =>
                  constructor
                  · intro htrue
                    change test (tail.get ⟨k, hk'⟩) = true at htrue
                    exact (hfalse htrue).elim
                  · intro hlt
                    have hnil : List.takeWhile test (head :: tail) = [] := by
                      apply List.takeWhile_eq_nil_iff.mpr
                      intro hl
                      simp [hhead]
                    simp [hnil] at hlt
              | true => exact (hfalse hv).elim
      | true =>
          cases k with
          | zero => simp [hhead]
          | succ k =>
              have hk' : k < tail.length := by simp at hk; omega
              have hanti' : ∀ i j (hi : i < tail.length) (hj : j < tail.length),
                  i ≤ j → test (tail.get ⟨j, hj⟩) = true →
                    test (tail.get ⟨i, hi⟩) = true := by
                intro i j hi hj hij htrue
                have hback := hanti (i + 1) (j + 1) (by simp [hi]) (by simp [hj])
                  (by omega) (by simpa using htrue)
                simpa using hback
              simpa [List.takeWhile_cons, hhead] using ih hanti' k hk'

private theorem takeWhile_boundary_false {α : Type*} (test : α → Bool)
    (xs : List α) (hshort : (xs.takeWhile test).length < xs.length) :
    test (xs.get ⟨(xs.takeWhile test).length, hshort⟩) = false := by
  induction xs with
  | nil => simp at hshort
  | cons head tail ih =>
      cases hhead : test head with
      | false =>
          have hnil : (head :: tail).takeWhile test = [] := by
            apply List.takeWhile_eq_nil_iff.mpr
            intro hl
            simp [hhead]
          simpa [hnil] using hhead
      | true =>
          have htake : (head :: tail).takeWhile test = head :: tail.takeWhile test := by
            simp [hhead]
          have hshort' : (tail.takeWhile test).length < tail.length := by
            rw [htake, List.length_cons, List.length_cons] at hshort
            omega
          have hfalse := ih hshort'
          simpa [htake] using hfalse

private theorem raw_complete_suffix_record_source_date (z : SourceInput p)
    (i : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length) :
    (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[i.val].input.time.val + 1 =
        ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + i.val + 1 := by
  have htimes := ReferenceCompletePhysicalHistory.completeSuffixRecords_time_values
    rate z rewards C_star C_h
  have hindex : i.val < p.T - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h := by
    rw [← ReferenceCompletePhysicalHistory.completeSuffixRecords_length rate z rewards C_star C_h]
    exact i.isLt
  have hget := congrArg (fun dates : List ℕ => dates[i.val]?) htimes
  rw [List.getElem?_map, List.getElem?_eq_getElem i.isLt, Option.map_some,
    ReferenceActivePhysicalHorizon.calendar, List.getElem?_range' hindex,
    Nat.one_mul] at hget
  have htime := Option.some.inj hget
  omega

/-- If the raw first-live window ends before the complete suffix, the next
record is the actual first collection cutoff on the original source date. -/
theorem raw_first_excluded_record (z : SourceInput p)
    (hshort : (rawInitialTransferWindow rate rewards C_star C_h z).length <
      (rawCompleteSuffixRecords rate rewards C_star C_h z).length) :
    ∃ r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate),
      (rawCompleteSuffixRecords rate rewards C_star C_h z)[
        (rawInitialTransferWindow rate rewards C_star C_h z).length] = r ∧
      r.input.time.val + 1 = rawInitialTransferWindowFirstExcludedDate
        rate rewards C_star C_h z ∧
      ReferenceCollectionPhaseHistory.cutoffChosen r.input = true ∧
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
        r.input.time z = some r := by
  let R := rawCompleteSuffixRecords rate rewards C_star C_h z
  let W := rawInitialTransferWindow rate rewards C_star C_h z
  let test : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) → Bool :=
    fun r => !ReferenceCollectionPhaseHistory.cutoffChosen r.input
  have hwindow := raw_window_eq_complete_suffix_takeWhile rate rewards C_star C_h z
  have hshort' : (R.takeWhile test).length < R.length := by
    exact hshort
  have hfalse := takeWhile_boundary_false test R hshort'
  have hlen : W.length = (R.takeWhile test).length := by
    exact congrArg List.length hwindow
  have hfalse' : test (R.get ⟨W.length, hshort⟩) = false := by
    simpa only [hlen] using hfalse
  have hcut : ReferenceCollectionPhaseHistory.cutoffChosen (R[W.length]).input = true := by
    change (!ReferenceCollectionPhaseHistory.cutoffChosen (R[W.length]).input) = false at hfalse'
    cases hc : ReferenceCollectionPhaseHistory.cutoffChosen (R[W.length]).input with
    | false => simp [hc] at hfalse'
    | true => rfl
  let r := R[W.length]
  have hdate := raw_complete_suffix_record_source_date rate rewards C_star C_h z
    ⟨W.length, hshort⟩
  have hdate' : r.input.time.val + 1 =
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + W.length + 1 := by
    dsimp only [r, R, rawCompleteSuffixRecords]
    exact hdate
  have hlookup : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h r.input.time z = some r := by
    have hstart : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h ≤
        r.input.time.val := by omega
    have hindex : r.input.time.val -
        ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h = W.length := by omega
    unfold ReferenceSourcePrefixHistoryFiltration.actualRecord
    rw [ite_eq_left hstart, hindex]
    exact List.getElem?_eq_getElem hshort
  refine ⟨r, rfl, ?_, ?_, hlookup⟩
  · change r.input.time.val + 1 =
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + W.length + 1
    exact hdate
  · exact hcut

private def rawDispatchOrigin (x : ReferenceActivePhysicalStep.RoundInput p rate) :
    ReferenceActivePhysicalStep.DispatchCut x → Prop
  | .live registers owned base _ => x.state.coordinator = .live registers owned base
  | .collection payload ledger _ _ _ =>
      ∃ proposal, x.state.coordinator = .collection payload ledger proposal
  | .first _ => x.state.coordinator = .first
  | .dagger => x.state.coordinator = .dagger
  | .invalidCollectionCutoff =>
      ∃ payload ledger proposal, x.state.coordinator = .collection payload ledger proposal

private theorem raw_dispatch_origin (x : ReferenceActivePhysicalStep.RoundInput p rate) :
    rawDispatchOrigin rate x (ReferenceActivePhysicalStep.prepare x).coordinator := by
  change rawDispatchOrigin rate x (ReferenceActivePhysicalStep.dispatch x)
  unfold ReferenceActivePhysicalStep.dispatch
  cases hc : x.state.coordinator with
  | first => simp only [CoordinatorRoundDispatch.dispatch]; exact hc
  | live registers owned base =>
      simp only [CoordinatorRoundDispatch.dispatch]
      exact hc
  | collection payload ledger proposal =>
      simp only [CoordinatorRoundDispatch.dispatch]
      split
      · exact ⟨proposal, hc⟩
      · exact ⟨payload, ledger, proposal, hc⟩
  | dagger => exact hc

/-- The first raw record excluded by the actual first cutoff is itself the
retained live `initializeAt` transfer start. This is derived from its actual
dispatcher output on the complete suffix, before any analytical date filter.
-/
theorem raw_first_excluded_live_transfer_start (z : SourceInput p)
    (hshort : (rawInitialTransferWindow rate rewards C_star C_h z).length <
      (rawCompleteSuffixRecords rate rewards C_star C_h z).length) :
    ∃ r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate),
      (rawCompleteSuffixRecords rate rewards C_star C_h z)[
        (rawInitialTransferWindow rate rewards C_star C_h z).length] = r ∧
      ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferLiveStartAt
        rate rewards C_star C_h r.input.time z := by
  obtain ⟨r, hrecord, _hdate, hcut, hlookup⟩ :=
    raw_first_excluded_record rate rewards C_star C_h z hshort
  subst r
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  have hshortR : (rawInitialTransferWindow rate rewards C_star C_h z).length < R.length := by
    simpa only [rawCompleteSuffixRecords, R] using hshort
  let i : Fin R.length := ⟨(rawInitialTransferWindow rate rewards C_star C_h z).length, hshortR⟩
  let x := R[i.val].input
  have hcut' : ReferenceCollectionPhaseHistory.cutoffChosen x = true := by
    simpa only [R, i, rawCompleteSuffixRecords] using hcut
  have hlookup' : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h x.time z = some (R[i.val]) := by
    simpa only [R, i, x, rawCompleteSuffixRecords] using hlookup
  have hcutValue : (match ReferenceActivePhysicalStep.dispatch x with
      | .live _ _ _ (.cutoffChosen _ _ _ _ _ _ _ _ _ _) => true
      | _ => false) = true := hcut'
  cases hdispatch : ReferenceActivePhysicalStep.dispatch x with
  | first outcome =>
      simp [hdispatch] at hcutValue
  | live registers owned base outcome =>
      cases outcome with
      | cutoffChosen dispatched hstart ledger hinit hledger hdomain hclock hpending hnone selected =>
          have horigin := raw_dispatch_origin rate x
          change rawDispatchOrigin rate x (ReferenceActivePhysicalStep.dispatch x) at horigin
          rw [hdispatch] at horigin
          have hstate : x.state.coordinator = .live registers owned base := horigin
          have hchoices := ReferenceCompleteLiveChoiceDomains.complete_live_dispatch_choice_exists
            rate rewards C_star C_h z i registers owned base (by
              simpa only [R, i, x] using hstate)
          have heq : ReferenceActivePhysicalStep.DispatchCut.live registers owned base
              (CoordinatorRoundDispatch.dispatchLive
                (ReferenceActivePhysicalStep.liveInput x registers owned base)) =
            ReferenceActivePhysicalStep.DispatchCut.live registers owned base
              (.cutoffChosen dispatched hstart ledger hinit hledger hdomain hclock hpending hnone selected) := by
            have hh := hdispatch
            unfold ReferenceActivePhysicalStep.dispatch at hh
            rw [hstate] at hh
            dsimp at hh
            rw [show CoordinatorRoundDispatch.dispatch
              (.live (ReferenceActivePhysicalStep.liveInput x registers owned base)) =
                .live (CoordinatorRoundDispatch.dispatchLive
                  (ReferenceActivePhysicalStep.liveInput x registers owned base)) from rfl] at hh
            exact hh
          have hchoice : CoordinatorRoundDispatch.dispatchLive
              (ReferenceActivePhysicalStep.liveInput x registers owned base) =
                .cutoffChosen dispatched hstart ledger hinit hledger hdomain hclock hpending hnone selected := by
            injection heq
          have hcommand : dispatched.startResult.ledgerCommand = some (.initializeAt x.time) := by
            have hbranch := hchoices.2
            rw [hchoice] at hbranch
            exact hbranch.1
          have hstart' : CoordinatorPhaseClock.startRound p rate.eta.val x.time
              registers.priorClock registers.clockPending = .ok dispatched.startResult := by
            simpa only [ReferenceActivePhysicalStep.liveInput,
              CoordinatorLiveChoiceRecorderStep.Registers.clockPending_eq,
              ReferenceActivePhysicalStep.liveRegistersAt] using hstart
          refine ⟨R[i.val], ?_, ?_⟩
          · simp only [R, i, rawCompleteSuffixRecords]
          · apply (ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferLiveStartAt_iff
              rate rewards C_star C_h x.time z).2
            exact ⟨R[i.val], registers, owned, base, dispatched.startResult,
              hlookup', hstate, hstart', hcommand⟩
      | continuingChosen dispatched hstart continuation selection =>
          simp [hdispatch] at hcutValue
      | clockFailure failure hdispatch' =>
          simp [hdispatch] at hcutValue
      | initializerFailure dispatched hstart checked hchecked =>
          simp [hdispatch] at hcutValue
      | localFailure dispatched hstart failure =>
          simp [hdispatch] at hcutValue
  | collection payload ledger clock cutoff outcome =>
      simp [hdispatch] at hcutValue
  | invalidCollectionCutoff =>
      simp [hdispatch] at hcutValue
  | dagger =>
      simp [hdispatch] at hcutValue

/-- If the raw window consumes the whole complete suffix, its endpoint is the
original `T + 1` sentinel. -/
theorem raw_window_reaches_horizon_sentinel (z : SourceInput p)
    (hwhole : (rawInitialTransferWindow rate rewards C_star C_h z).length =
      (rawCompleteSuffixRecords rate rewards C_star C_h z).length) :
    rawInitialTransferWindowFirstExcludedDate rate rewards C_star C_h z = p.T + 1 := by
  have hrecords := ReferenceCompletePhysicalHistory.completeSuffixRecords_length
    rate z rewards C_star C_h
  have hstart := ReferenceCompletePhysicalHistory.physicalStart_le_T rate z rewards C_star C_h
  unfold rawInitialTransferWindowFirstExcludedDate
  rw [hwhole]
  change ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h +
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).length + 1 =
    p.T + 1
  rw [hrecords]
  omega

/-- The raw endpoint either names the first actual collection cutoff in the
complete suffix, or is exactly the one-past-horizon sentinel. -/
theorem raw_initial_transfer_window_endpoint_alternative (z : SourceInput p) :
    (∃ hshort : (rawInitialTransferWindow rate rewards C_star C_h z).length <
        (rawCompleteSuffixRecords rate rewards C_star C_h z).length,
      ∃ r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate),
      (rawCompleteSuffixRecords rate rewards C_star C_h z)[
        (rawInitialTransferWindow rate rewards C_star C_h z).length]'hshort = r ∧
      r.input.time.val + 1 = rawInitialTransferWindowFirstExcludedDate
        rate rewards C_star C_h z ∧
      ReferenceCollectionPhaseHistory.cutoffChosen r.input = true ∧
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
        r.input.time z = some r) ∨
    (rawInitialTransferWindowFirstExcludedDate rate rewards C_star C_h z = p.T + 1 ∧
      (rawInitialTransferWindow rate rewards C_star C_h z).length =
        (rawCompleteSuffixRecords rate rewards C_star C_h z).length) := by
  let W := rawInitialTransferWindow rate rewards C_star C_h z
  let R := rawCompleteSuffixRecords rate rewards C_star C_h z
  let test : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) → Bool :=
    fun r => !ReferenceCollectionPhaseHistory.cutoffChosen r.input
  have hle : W.length ≤ R.length := by
    have hprefix : W <+: R := by
      have hwindow := raw_window_eq_complete_suffix_takeWhile rate rewards C_star C_h z
      have hwindow' : W = R.takeWhile test := by
        simpa only [W, R, test] using hwindow
      rw [hwindow']
      exact List.takeWhile_prefix test
    exact hprefix.length_le
  by_cases hshort : W.length < R.length
  · exact Or.inl ⟨hshort, raw_first_excluded_record rate rewards C_star C_h z hshort⟩
  · have hwhole : W.length = R.length := by omega
    exact Or.inr ⟨raw_window_reaches_horizon_sentinel rate rewards C_star C_h z hwhole,
      hwhole⟩

private theorem missingAtChoice_iff_nonempty (z : SourceInput p)
    (k : Fin (rawInitialTransferWindow rate rewards C_star C_h z).length) :
    ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice
        ((rawInitialTransferWindow rate rewards C_star C_h z)[k.val]) = true ↔
      (ReferenceFirstLiveSourceStoppedHandoverEndpoint.missing rate
        ((rawInitialTransferWindow rate rewards C_star C_h z)[k.val])).Nonempty := by
  have hprov := raw_window_provenance_of_nonempty rate rewards C_star C_h z
    (by have := k.isLt; omega)
  dsimp only at hprov
  rcases hprov with hzero | ⟨hW, _installed, _firstSelected, _hselected0,
      _hinstall, _hpayload0, _hinitial, _hpayload, hrows⟩
  · have := k.isLt
    omega
  · obtain ⟨selected, hselected, _hpayload, _hphase, _next, _owned, _base,
        _hnext, _hnextPayload, _hupdate, _hfailure, _hfollowers⟩ :=
      hrows k
    have hm : ReferenceFirstLiveSourceStoppedHandoverEndpoint.missing rate
        ((rawInitialTransferWindow rate rewards C_star C_h z).get k) =
        selected.view.pendingAtChoice := by
      unfold ReferenceFirstLiveSourceStoppedHandoverEndpoint.missing
        ReferenceFirstLiveSourceStoppedHandoverEndpoint.actualSelection
      rw [hselected]
      rfl
    change ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice
        ((rawInitialTransferWindow rate rewards C_star C_h z).get k) = true ↔
      (ReferenceFirstLiveSourceStoppedHandoverEndpoint.missing rate
        ((rawInitialTransferWindow rate rewards C_star C_h z).get k)).Nonempty
    unfold ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice
    rw [hselected, hm]
    simp only [decide_eq_true_eq]
    exact Iff.rfl

/-- Every consecutive raw-window missing set is antitone in the original
physical run. -/
theorem raw_missing_antitone (z : SourceInput p)
    (a b : Fin (rawInitialTransferWindow rate rewards C_star C_h z).length) (hab : a.val ≤ b.val) :
    ReferenceFirstLiveSourceStoppedHandoverEndpoint.missing rate
      ((rawInitialTransferWindow rate rewards C_star C_h z)[b.val]) ⊆
    ReferenceFirstLiveSourceStoppedHandoverEndpoint.missing rate
      ((rawInitialTransferWindow rate rewards C_star C_h z)[a.val]) :=
  ReferenceFirstLiveSourceStoppedHandoverEndpoint.source_window_missing_antitone
    rate rewards C_star C_h z a b hab

/-- The actual missing set is nonempty exactly before the literal raw
`takeWhile` boundary. This theorem makes no appeal to analytically stopped
support or the first global bad date. -/
theorem raw_missing_prefix_iff (z : SourceInput p)
    (k : Fin (rawInitialTransferWindow rate rewards C_star C_h z).length) :
    (ReferenceFirstLiveSourceStoppedHandoverEndpoint.missing rate
      ((rawInitialTransferWindow rate rewards C_star C_h z)[k.val])).Nonempty ↔
        k.val < rawMissingPrefixLength rate rewards C_star C_h z := by
  rw [← missingAtChoice_iff_nonempty rate rewards C_star C_h z k]
  have hanti : ∀ i j (hi : i < (rawInitialTransferWindow rate rewards C_star C_h z).length)
      (hj : j < (rawInitialTransferWindow rate rewards C_star C_h z).length),
      i ≤ j →
      ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice
        ((rawInitialTransferWindow rate rewards C_star C_h z).get ⟨j, hj⟩) = true →
      ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice
        ((rawInitialTransferWindow rate rewards C_star C_h z).get ⟨i, hi⟩) = true := by
    intro i j hi hj hij htrue
    have hnonempty := (missingAtChoice_iff_nonempty rate rewards C_star C_h z
      ⟨j, hj⟩).mp htrue
    have hsubset := raw_missing_antitone rate rewards C_star C_h z ⟨i, hi⟩ ⟨j, hj⟩ hij
    exact (missingAtChoice_iff_nonempty rate rewards C_star C_h z ⟨i, hi⟩).mpr
      (hnonempty.mono hsubset)
  exact takeWhile_getElem_eq_true_iff
    ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice
    (rawInitialTransferWindow rate rewards C_star C_h z) hanti k.val k.isLt

/-- An actual adjacent empty choice after nonempty pending has the raw first
clearing confirmation and the unique last missing follower on the preceding
record. No filtered-support premise is used. -/
theorem raw_adjacent_clearing_confirmation (z : SourceInput p)
    (k : Fin (ReferenceFirstLiveSourceStoppedHandoverEndpoint.window rate rewards C_star C_h z).length)
    (hk : k.val + 1 <
      (ReferenceFirstLiveSourceStoppedHandoverEndpoint.window rate rewards C_star C_h z).length)
    (hcurrent : (ReferenceFirstLiveSourceStoppedHandoverEndpoint.missing rate
      ((ReferenceFirstLiveSourceStoppedHandoverEndpoint.window rate rewards C_star C_h z)[k.val])).Nonempty)
    (hnext : ReferenceFirstLiveSourceStoppedHandoverEndpoint.missing rate
      ((ReferenceFirstLiveSourceStoppedHandoverEndpoint.window rate rewards C_star C_h z)[k.val + 1]) = ∅) :
    ∃ selected : ReferenceActivePhysicalStep.Selection
        ((ReferenceFirstLiveSourceStoppedHandoverEndpoint.window rate rewards C_star C_h z)[k.val]).input,
      ReferenceFirstLiveSourceStoppedHandoverEndpoint.actualSelection rate
        ((ReferenceFirstLiveSourceStoppedHandoverEndpoint.window rate rewards C_star C_h z)[k.val]) = some selected ∧
      ReferenceFirstLiveMissingSetProvenance.actualDownConfirmationEvent
        ((ReferenceFirstLiveSourceStoppedHandoverEndpoint.window rate rewards C_star C_h z)[k.val]) selected ∧
      ReferenceFirstLiveSourceStoppedHandoverEndpoint.missing rate
        ((ReferenceFirstLiveSourceStoppedHandoverEndpoint.window rate rewards C_star C_h z)[k.val]) =
        {PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
          (((ReferenceFirstLiveSourceStoppedHandoverEndpoint.window rate rewards C_star C_h z)[k.val]).input.row.2
            ((ReferenceFirstLiveSourceStoppedHandoverEndpoint.window rate rewards C_star C_h z)[k.val]).input.time).1} := by
  obtain ⟨selected, hselected, _hpayload, hstep⟩ :=
    ReferenceFirstLiveSourceStoppedHandoverEndpoint.source_window_missing_step
      rate rewards C_star C_h z k.val hk
  have hconfirmation : ReferenceFirstLiveMissingSetProvenance.actualDownConfirmationEvent
      ((ReferenceFirstLiveSourceStoppedHandoverEndpoint.window rate rewards C_star C_h z)[k.val]) selected := by
    by_contra hno
    rw [ite_eq_right hno, hnext] at hstep
    exact hcurrent.ne_empty hstep.symm
  have hsingle : ReferenceFirstLiveSourceStoppedHandoverEndpoint.missing rate
      ((ReferenceFirstLiveSourceStoppedHandoverEndpoint.window rate rewards C_star C_h z)[k.val]) =
      {PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
        (((ReferenceFirstLiveSourceStoppedHandoverEndpoint.window rate rewards C_star C_h z)[k.val]).input.row.2
          ((ReferenceFirstLiveSourceStoppedHandoverEndpoint.window rate rewards C_star C_h z)[k.val]).input.time).1} := by
    rw [ite_eq_left hconfirmation, hnext] at hstep
    exact ((Finset.erase_eq_empty_iff _ _).mp hstep.symm).resolve_left hcurrent.ne_empty
  exact ⟨selected, hselected, hconfirmation, hsingle⟩

/-- When the raw pending prefix ends before the physical window does, its
predecessor is the first actual clearing confirmation and the next record is
the first raw release record. Only its selected empty pending set is asserted;
no follower status is introduced. -/
theorem raw_first_release_after_clearing (z : SourceInput p)
    (hh : rawMissingPrefixLength rate rewards C_star C_h z <
      (rawInitialTransferWindow rate rewards C_star C_h z).length) :
    let h := rawMissingPrefixLength rate rewards C_star C_h z
    (∃ selected : ReferenceActivePhysicalStep.Selection ((rawInitialTransferWindow rate rewards C_star C_h z)[h - 1]).input,
      ReferenceFirstLiveSourceStoppedHandoverEndpoint.actualSelection rate
        ((rawInitialTransferWindow rate rewards C_star C_h z)[h - 1]) = some selected ∧
      ReferenceFirstLiveMissingSetProvenance.actualDownConfirmationEvent
        ((rawInitialTransferWindow rate rewards C_star C_h z)[h - 1]) selected ∧
      ReferenceFirstLiveSourceStoppedHandoverEndpoint.missing rate
        ((rawInitialTransferWindow rate rewards C_star C_h z)[h - 1]) =
        {PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
          (((rawInitialTransferWindow rate rewards C_star C_h z)[h - 1]).input.row.2
            ((rawInitialTransferWindow rate rewards C_star C_h z)[h - 1]).input.time).1}) ∧
    (ReferenceFirstLiveSourceStoppedHandoverEndpoint.missing rate
      ((rawInitialTransferWindow rate rewards C_star C_h z)[h])).Nonempty = False ∧
    ((rawInitialTransferWindow rate rewards C_star C_h z)[h]).input.time.val =
      ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart rate rewards C_star C_h z + h := by
  let h := rawMissingPrefixLength rate rewards C_star C_h z
  have hW : 0 < (rawInitialTransferWindow rate rewards C_star C_h z).length := by omega
  have hfirst : (ReferenceFirstLiveSourceStoppedHandoverEndpoint.missing rate
      ((rawInitialTransferWindow rate rewards C_star C_h z)[0])).Nonempty := by
    have hm := ReferenceFirstLiveSourceStoppedHandoverEndpoint.source_window_initial_missing
      rate rewards C_star C_h z (by simpa only [rawInitialTransferWindow] using hW)
    have hm' : ReferenceFirstLiveSourceStoppedHandoverEndpoint.missing rate
        ((rawInitialTransferWindow rate rewards C_star C_h z)[0]) = Finset.univ := by
      simpa only [rawInitialTransferWindow, List.get_eq_getElem] using hm
    rw [hm']
    exact ⟨⟨0, by have := p.two_le_m; omega⟩, Finset.mem_univ _⟩
  have hzero : 0 < h := by
    have hiff := raw_missing_prefix_iff rate rewards C_star C_h z ⟨0, hW⟩
    change 0 < h
    exact hiff.mp hfirst
  let k : Fin (rawInitialTransferWindow rate rewards C_star C_h z).length := ⟨h - 1, by omega⟩
  have hkval : k.val + 1 = h := by dsimp [k]; omega
  have hcur : (ReferenceFirstLiveSourceStoppedHandoverEndpoint.missing rate
      ((rawInitialTransferWindow rate rewards C_star C_h z)[k.val])).Nonempty := by
    exact (raw_missing_prefix_iff rate rewards C_star C_h z k).2 (by
      change k.val < h
      omega)
  have hnxt : ReferenceFirstLiveSourceStoppedHandoverEndpoint.missing rate
      ((rawInitialTransferWindow rate rewards C_star C_h z)[k.val + 1]) = ∅ := by
    apply Finset.not_nonempty_iff_eq_empty.mp
    intro hn
    have hiff := raw_missing_prefix_iff rate rewards C_star C_h z
      ⟨k.val + 1, by omega⟩
    have : k.val + 1 < h := by
      have hlt := hiff.mp hn
      change k.val + 1 < h at hlt
      exact hlt
    omega
  have hk : k.val + 1 < (rawInitialTransferWindow rate rewards C_star C_h z).length := by omega
  have hclear := raw_adjacent_clearing_confirmation rate rewards C_star C_h z k hk hcur hnxt
  have htime := (raw_window_record_calendar rate rewards C_star C_h z
    ⟨h, hh⟩).1
  refine ⟨?_, ?_, htime⟩
  · exact hclear
  · rw [raw_missing_prefix_iff rate rewards C_star C_h z ⟨h, hh⟩]
    simp [h]

/-- At the physical horizon, if the raw pending prefix reaches the final
record, its actual last update either clears the singleton pending follower
at the terminal state or leaves pending nonempty. The endpoint is the `T + 1`
sentinel, so this case has no release record and asserts no follower status
after the terminal update.
-/
theorem raw_terminal_update_without_release_record (z : SourceInput p)
    (hwhole : (rawInitialTransferWindow rate rewards C_star C_h z).length =
      (rawCompleteSuffixRecords rate rewards C_star C_h z).length)
    (hprefix : rawMissingPrefixLength rate rewards C_star C_h z =
      (rawInitialTransferWindow rate rewards C_star C_h z).length)
    (hne : 0 < (rawInitialTransferWindow rate rewards C_star C_h z).length) :
    rawInitialTransferWindowFirstExcludedDate rate rewards C_star C_h z = p.T + 1 ∧
    ∃ r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate),
    ∃ selected : ReferenceActivePhysicalStep.Selection r.input,
    ∃ next : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta,
    ∃ owned : CoordinatorLiveServiceFinish.OwnedRegisters next,
    ∃ base : Fin (p.m - 1) → ℕ,
      (rawInitialTransferWindow rate rewards C_star C_h z)[
        (rawInitialTransferWindow rate rewards C_star C_h z).length - 1] = r ∧
      r.input.time.val + 1 = p.T ∧
      ReferenceFirstLiveSourceStoppedHandoverEndpoint.actualSelection rate r = some selected ∧
      (ReferenceFirstLiveSourceStoppedHandoverEndpoint.missing rate r).Nonempty ∧
      r.output.next.coordinator = .live next owned base ∧
      next.pendingAtChoice =
        (if ReferenceFirstLiveMissingSetProvenance.actualDownConfirmationEvent r selected then
          selected.view.pendingAtChoice.erase
            (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
              ((r.input.row.2 r.input.time).1))
        else selected.view.pendingAtChoice) ∧
      ((ReferenceFirstLiveMissingSetProvenance.actualDownConfirmationEvent r selected ∧
        ReferenceFirstLiveSourceStoppedHandoverEndpoint.missing rate r =
          {PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
            ((r.input.row.2 r.input.time).1)} ∧ next.pendingAtChoice = ∅) ∨
        next.pendingAtChoice.Nonempty) := by
  let W := rawInitialTransferWindow rate rewards C_star C_h z
  let R := rawCompleteSuffixRecords rate rewards C_star C_h z
  have hendpoint := raw_window_reaches_horizon_sentinel rate rewards C_star C_h z hwhole
  have hW : 0 < W.length := by simpa only [W] using hne
  let k : Fin W.length := ⟨W.length - 1, by omega⟩
  have hkval : k.val + 1 = W.length := by dsimp [k]; omega
  have hnonempty : (ReferenceFirstLiveSourceStoppedHandoverEndpoint.missing rate
      (W[k.val])).Nonempty := by
    apply (raw_missing_prefix_iff rate rewards C_star C_h z k).2
    rw [hprefix]
    exact k.isLt
  have hprovenance := raw_window_provenance_of_nonempty rate rewards C_star C_h z hW
  dsimp only at hprovenance
  rcases hprovenance with hzero | ⟨_hW, _installed, _firstSelected, _hselection0,
      _hinstalled, _hpayload0, _hinitial, _hpayload, hrows⟩
  · omega
  · obtain ⟨selected, hselected, _hpayload, _hphase, next, owned, base,
        hnext, _hnextPayload, hupdate, _hfailure, _hfollowers⟩ := hrows k
    let r := W[k.val]
    have hselected' : ReferenceFirstLiveSourceStoppedHandoverEndpoint.actualSelection rate r =
        some selected := by
      change ((ReferenceFirstLiveSourceStoppedHandoverEndpoint.window rate rewards C_star C_h z).get k).output.preparation.coordinator.selection =
        some selected
      exact hselected
    have hmissing : ReferenceFirstLiveSourceStoppedHandoverEndpoint.missing rate r =
        selected.view.pendingAtChoice := by
      unfold ReferenceFirstLiveSourceStoppedHandoverEndpoint.missing
      rw [hselected']
      rfl
    have hnonemptyR : (ReferenceFirstLiveSourceStoppedHandoverEndpoint.missing rate r).Nonempty := by
      simpa only [r, W, rawInitialTransferWindow, List.get_eq_getElem] using hnonempty
    have hpendingNonempty : selected.view.pendingAtChoice.Nonempty := by
      rw [← hmissing]
      exact hnonemptyR
    have hdate := (raw_window_record_calendar rate rewards C_star C_h z k).1
    have hlength := ReferenceCompletePhysicalHistory.completeSuffixRecords_length
      rate z rewards C_star C_h
    have hWlen : W.length = p.T -
        ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h := by
      calc
        W.length = R.length := by simpa only [W, R] using hwhole
        _ = p.T - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h := by
          simpa only [R, rawCompleteSuffixRecords] using hlength
    have hdate' : r.input.time.val =
        ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + k.val := by
      simpa [r, W, rawInitialTransferWindow,
        ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart] using hdate
    have hterminalDate : r.input.time.val + 1 = p.T := by
      rw [hdate']
      dsimp [k]
      rw [hWlen]
      omega
    have hnextLive : r.output.next.coordinator = .live next owned base := by
      change ((ReferenceFirstLiveSourceStoppedHandoverEndpoint.window rate rewards C_star C_h z).get k).output.next.coordinator =
        .live next owned base
      exact hnext
    have hupdate' : next.pendingAtChoice =
        (if ReferenceFirstLiveMissingSetProvenance.actualDownConfirmationEvent r selected then
          selected.view.pendingAtChoice.erase
            (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
              ((r.input.row.2 r.input.time).1))
        else selected.view.pendingAtChoice) := by
      change next.pendingAtChoice =
        (if ReferenceFirstLiveMissingSetProvenance.actualDownConfirmationEvent
            ((ReferenceFirstLiveSourceStoppedHandoverEndpoint.window rate rewards C_star C_h z).get k) selected then
          selected.view.pendingAtChoice.erase
            (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
              ((((ReferenceFirstLiveSourceStoppedHandoverEndpoint.window rate rewards C_star C_h z).get k).input.row.2
                ((ReferenceFirstLiveSourceStoppedHandoverEndpoint.window rate rewards C_star C_h z).get k).input.time).1))
        else selected.view.pendingAtChoice)
      exact hupdate
    have hterminalClearOrPending :
        (ReferenceFirstLiveMissingSetProvenance.actualDownConfirmationEvent r selected ∧
          ReferenceFirstLiveSourceStoppedHandoverEndpoint.missing rate r =
            {PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
              ((r.input.row.2 r.input.time).1)} ∧ next.pendingAtChoice = ∅) ∨
          next.pendingAtChoice.Nonempty := by
      by_cases hevent : ReferenceFirstLiveMissingSetProvenance.actualDownConfirmationEvent r selected
      · by_cases hempty : selected.view.pendingAtChoice.erase
            (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
              ((r.input.row.2 r.input.time).1)) = ∅
        · left
          have hsingle : selected.view.pendingAtChoice =
              {PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
                ((r.input.row.2 r.input.time).1)} := by
            exact ((Finset.erase_eq_empty_iff _ _).mp hempty).resolve_left (by
              rw [← hmissing]
              exact hnonemptyR.ne_empty)
          have hmissingSingle := hmissing.trans hsingle
          have hnextEmpty : next.pendingAtChoice = ∅ := by
            simp [hupdate', hevent, hempty]
          exact ⟨hevent, hmissingSingle, hnextEmpty⟩
        · right
          have herase : (selected.view.pendingAtChoice.erase
              (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
                ((r.input.row.2 r.input.time).1))).Nonempty := by
            by_contra hnot
            exact hempty (Finset.not_nonempty_iff_eq_empty.mp hnot)
          simpa [hupdate', hevent] using herase
      · right
        simpa [hupdate', hevent] using hpendingNonempty
    refine ⟨hendpoint, r, selected, next, owned, base, ?_, hterminalDate,
      hselected', hnonemptyR, hnextLive, hupdate', hterminalClearOrPending⟩
    · simpa only [r, W, R, rawInitialTransferWindow, rawCompleteSuffixRecords] using
        (show W[W.length - 1] = r by rfl)

end Bandits.Support.ReferenceOriginalInitialTransferWindowGeometry

end
