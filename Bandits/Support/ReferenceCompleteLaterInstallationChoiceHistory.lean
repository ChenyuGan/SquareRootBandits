/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteInstallationCollectionPrefixNumericalTruth

import Mathlib.Tactic

/-!
# Actual later-installation choice-history basis

This internal basis retains one actual later installation, its continuing
choice history, and the actual follower states through missing-set release.
It uses the literal complete physical history and the accepted numerical-prefix
result; it asserts no regret closure.
-/

@[expose] public section
noncomputable section

open Bandits.Support
open ConstructorDimensions BootstrapPrivateRoundStreams

namespace Bandits.Support.ReferenceCompleteLaterInstallationChoiceHistory

variable {p : ConstructorDimensions.Parameters}

private theorem complete_generated_records
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hne : 0 < (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length) :
    let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    ∃ hs : s < p.T,
      ∃ x : ReferenceGeneratedDownBatchCalendar.LaunchSource rate rewards C_star C_h s hs,
        x.val = z ∧
        ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h =
          (ReferenceGeneratedDownBatchCalendar.generatedSourceRun
            rate rewards C_star C_h s hs x).records := by
  let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  have hlen := ReferenceCompletePhysicalHistory.completeSuffixRecords_length
    rate z rewards C_star C_h
  have hs : s < p.T := by dsimp only [s]; omega
  have hn : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h ≠ none := by
    intro hn
    have := ReferenceCompletePhysicalHistory.correctedLaunch_none_start_eq_T
      rate z rewards C_star C_h hn
    dsimp only [s] at hs
    omega
  have hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true :=
    (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
      rate z rewards C_star C_h).mp (Option.isSome_iff_ne_none.mpr hn)
  let x : ReferenceGeneratedDownBatchCalendar.LaunchSource
      rate rewards C_star C_h s hs := ⟨z, hc, rfl⟩
  let seed := ReferenceGeneratedDownBatchCalendar.generatedSourceSeed
    rate rewards C_star C_h s hs x
  have hseed := ReferenceGeneratedDownBatchCalendar.generatedSourceSeed_spec
    rate rewards C_star C_h s hs x
  refine ⟨hs, x, rfl, ?_⟩
  rw [ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
    rate z rewards C_star C_h seed hseed.1]
  rfl


open scoped Classical

open ReferenceActivePhysicalStep ReferenceActivePhysicalHorizon
open ReferenceAssignmentPayloadPersistence

private abbrev Record {rate : ReferenceActivePhysicalStep.RateInput p} :=
  ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)

variable {rate : ReferenceActivePhysicalStep.RateInput p}

private theorem selectionAt_fields
    (x : RoundInput p rate) (payload : Payload rate)
    (started : CoordinatorPhaseClock.StartRoundResult p) (time : Fin p.T)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ)
    (arm : CoordinatorRoundDispatch.ArmSelection payload started time weights x.row)
    (selected : Selection x)
    (hselected : selectionAt x payload started time weights arm = some selected) :
    selected.view.payload = payload ∧
      selected.view.pendingAtChoice = started.pending ∧
      selected.view.cutoff = CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u ∧
      selected.started = started := by
  unfold selectionAt at hselected
  split at hselected
  · cases hselected
    exact ⟨rfl, rfl, rfl, rfl⟩
  · cases hselected

private theorem livePostChoice_live_success
    (x : RoundInput p rate) (prepared : PreparedRound x)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ) (started : CoordinatorPhaseClock.StartRoundResult p)
    (next : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters next)
    (baseNext : Fin (p.m - 1) → ℕ)
    (h : (livePostChoice prepared r q base started).configuration = .live next owned baseNext) :
    ∃ recording serviced pending finished,
      CoordinatorRecorderComplementBridge.run (liveRecordingInput prepared r started) =
        some recording ∧
      CoordinatorLiveServiceFinish.servicePass r q recording = .ok serviced ∧
      CoordinatorLocalArmChoice.confirmationUpdate r.payload started.pending
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
        x.time x.row prepared.coordinatorObservation = some pending ∧
      CoordinatorPhaseClock.finishRound p rate.eta.val x.time started.clock pending x.row =
        .ok finished ∧
      next.payload = r.payload ∧ next.pendingAtChoice = finished.pending := by
  unfold livePostChoice at h
  split at h
  · cases h
  · rename_i recording hrecord
    split at h
    · cases h
    · rename_i serviced hservice
      split at h
      · cases h
      · rename_i pending hpending
        split at h
        · cases h
        · rename_i finished hfinish
          cases h
          exact ⟨recording, serviced, pending, finished,
            hrecord, hservice, hpending, hfinish, rfl, rfl⟩

private theorem record_live_tail_origin
    (record : Record (p := p) (rate := rate)) (selected : Selection record.input)
    (hselected : record.output.preparation.coordinator.selection = some selected)
    (hlater : ReferenceCollectionPhaseHistory.laterChosen record.input = true) :
    ∃ registers registersOwned liveBase started,
      record.output.preparation.observeCoordinator =
        livePostChoice record.output.preparation registers registersOwned liveBase started ∧
      selected.view.payload = registers.payload ∧
      selected.view.pendingAtChoice = started.pending ∧
      selected.view.cutoff = CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u ∧
      selected.started = started := by
  have hp : record.output.preparation = prepare record.input := by rw [record.output_eq]; rfl
  unfold ReferenceCollectionPhaseHistory.laterChosen at hlater
  rw [← hp] at hlater
  cases hcoord : record.output.preparation.coordinator
    <;> try simp only [hcoord, Bool.false_eq_true] at hlater
  rename_i payload ledger clock cutoff outcome
  cases outcome <;> try simp only [Bool.false_eq_true] at hlater
  rename_i core consistent started hstart instruction hinstruction output hlocal clockData installed arm
  have hselAt : selectionAt record.input installed.registers.payload
      started instruction.time installed.registers.complementWeights arm =
        some selected := by
    simpa only [hcoord, DispatchCut.selection] using hselected
  have hfields := selectionAt_fields record.input installed.registers.payload
    started instruction.time installed.registers.complementWeights arm selected hselAt
  have heq := observeCoordinator_collection_equation record.output.preparation
    payload ledger clock cutoff (.laterChosen core consistent started hstart
      instruction hinstruction output hlocal clockData installed arm) hcoord
  have hnon : (DispatchCut.collection payload ledger clock cutoff
      (.laterChosen core consistent started hstart instruction hinstruction
        output hlocal clockData installed arm)).selection ≠ none := by
    rw [← hcoord, hselected]
    exact Option.some_ne_none _
  have hobs : record.output.preparation.observeCoordinator =
      livePostChoice record.output.preparation installed.registers
        installed.ownedRegisters installed.retainedBaseScore started := by
    rw [heq, ite_eq_right hnon]
  exact ⟨installed.registers, installed.ownedRegisters,
    installed.retainedBaseScore, started, hobs, hfields.1, hfields.2.1,
    hfields.2.2.1, hfields.2.2.2⟩

private theorem selected_live_pending_update
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (record : Record (p := p) (rate := rate)) (selected : Selection record.input)
    (hselected : record.output.preparation.coordinator.selection = some selected)
    (hlater : ReferenceCollectionPhaseHistory.laterChosen record.input = true)
    (next : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters next)
    (base : Fin (p.m - 1) → ℕ)
    (hnext : record.output.next.coordinator = .live next owned base) :
    next.payload = selected.view.payload ∧
    next.pendingAtChoice =
      if ReferenceFirstLiveMissingSetProvenance.actualDownConfirmationEvent record selected then
        selected.view.pendingAtChoice.erase (PublicDiscreteDraws.selectedFollowerDraw
          p.two_le_m p.m_lt_K (record.input.row.2 record.input.time).1)
      else selected.view.pendingAtChoice := by
  classical
  obtain ⟨r, q, beta, started, hobs, hpayload, hpending, hcutoff, _⟩ :=
    record_live_tail_origin record selected hselected hlater
  have hconfig : record.output.next.coordinator =
      record.output.preparation.observeCoordinator.configuration := by
    rw [record.output_eq]
    rfl
  rw [hconfig, hobs] at hnext
  obtain ⟨recording, serviced, pending, finished, _hr, _hs, hu, hf, hnp, hnpending⟩ :=
    livePostChoice_live_success record.input record.output.preparation r q beta started
      next owned base hnext
  have hcore : CoordinatorLocalArmChoice.confirmationUpdateCore selected.view.payload
      selected.view.pendingAtChoice selected.view.cutoff record.input.time
      (record.input.row.2 record.input.time)
      record.output.preparation.coordinatorObservation = some pending := by
    simpa only [CoordinatorLocalArmChoice.confirmationUpdate, hpayload, hpending, hcutoff] using hu
  have hv : CoordinatorLocalArmChoice.ConfirmationInputsValid selected.view.payload
      selected.view.cutoff record.input.time := by
    by_contra hnot
    simp only [CoordinatorLocalArmChoice.confirmationUpdateCore, hnot] at hcore
    cases hcore
  have hfinish := CoordinatorPhaseClock.finishRound_pending_frame p rate.eta.val
    record.input.time started.clock pending record.input.row finished hf
  refine ⟨hnp.trans hpayload.symm, ?_⟩
  rw [hnpending, hfinish]
  by_cases he : ReferenceFirstLiveMissingSetProvenance.actualDownConfirmationEvent record selected
  · rw [ite_eq_left he]
    exact Option.some.inj (hcore.symm.trans
      (CoordinatorLocalArmChoice.confirmationUpdateCore_removes _ _ _ _ _ _ hv he))
  · rw [ite_eq_right he]
    exact Option.some.inj (hcore.symm.trans
      (CoordinatorLocalArmChoice.confirmationUpdateCore_preserves _ _ _ _ _ _ hv he))

private theorem birth_selection_pending
    (record : Record (p := p) (rate := rate)) (payload : Payload rate)
    (hbirth : InstallationBirth record payload)
    (hlater : ReferenceCollectionPhaseHistory.laterChosen record.input = true)
    (selected : Selection record.input)
    (hselected : record.output.preparation.coordinator.selection = some selected) :
    selected.view.payload = payload ∧
      selected.view.pendingAtChoice = Finset.univ ∧ selected.started.pending = Finset.univ := by
  have hp : record.output.preparation = prepare record.input := by rw [record.output_eq]; rfl
  unfold ReferenceCollectionPhaseHistory.laterChosen at hlater
  rw [← hp] at hlater
  cases hcut : record.output.preparation.coordinator with
  | first _ => simp only [hcut, Bool.false_eq_true] at hlater
  | live _ _ _ outcome => cases outcome <;> simp only [InstallationBirth, hcut] at hbirth
  | collection old ledger clock cutoff outcome =>
      cases outcome <;> try simp only [InstallationBirth, hcut] at hbirth
      rename_i core consistent started hstart instruction hinstruction output hlocal
        clockData installed arm
      have hfields := selectionAt_fields record.input installed.registers.payload
        started instruction.time installed.registers.complementWeights arm selected
        (by simpa only [hcut, DispatchCut.selection] using hselected)
      obtain ⟨_, _, _, _, _, _, hpending, _⟩ :=
        CoordinatorPhaseClock.startRound_assignment_effect p rate.eta.val record.input.time
          clock ledger.pending started instruction core.clock_parameter_valid
          core.clock_registers_valid core.clock_start_time_valid hstart hinstruction
      refine ⟨hfields.1.trans hbirth.1.symm, hfields.2.1.trans hpending, ?_⟩
      rw [hfields.2.2.2, hpending]
  | invalidCollectionCutoff => simp only [InstallationBirth, hcut] at hbirth
  | dagger => simp only [InstallationBirth, hcut] at hbirth


/-- Every omitted follower has a strictly prior, occupied, same-payload
confirmation in the original suffix, without a success or history premise. -/

private theorem continuing_not_cutoff
    (record : Record (p := p) (rate := rate))
    (hc : ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest record = true) :
    ReferenceCollectionPhaseHistory.cutoffChosen record.input = false := by
  have hp : record.output.preparation = prepare record.input := by rw [record.output_eq]; rfl
  unfold ReferenceCollectionPhaseHistory.cutoffChosen
  rw [← hp]
  unfold ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest at hc
  cases hcoord : record.output.preparation.coordinator with
  | first _ => rfl
  | collection _ _ _ _ _ => rfl
  | dagger => rfl
  | invalidCollectionCutoff => rfl
  | live r q base outcome => cases outcome <;> simp_all only [Bool.false_eq_true]

private theorem complete_clock
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).length) :
    let r := (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val]
    ReferenceCoordinatorClockDomains.clockAt r.input.rows r.input.selected r.input.time.val r.input.state := by
  obtain ⟨hc, _, hr⟩ := ReferenceLaterLiveNumericalReadout.source_record_prefix
    rate rewards C_star C_h z k
  let initial := ReferenceFirstLaunchNumericalCell.launchState rate z rewards C_star C_h hc
  have hl := ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
    rate z rewards C_star C_h hc
  have hrecords := ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
    rate z rewards C_star C_h initial hl
  have hseed : ReferenceCoordinatorClockDomains.clockAt z.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p z)
      (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) initial := by
    have hf := (ReferenceFirstWindowNumericalStream.actualFirstLiveSeed rate z rewards C_star C_h hc).coordinatorFirst
    simp only [ReferenceCoordinatorClockDomains.clockAt, show initial.coordinator = .first from hf]
  have hrun := ReferenceRunClockPreservation.run_clockAt initial z.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards
    (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
    (p.T - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
    (by have := ReferenceCompletePhysicalHistory.physicalStart_le_T rate z rewards C_star C_h; omega)
    (ReferenceCompletePhysicalHistory.activeMode_of_launch_eq_some rate z rewards C_star C_h initial hl) hseed
  have h := hrun.2.2.2 _ (by rw [← hrecords]; exact List.getElem_mem k.isLt)
  simpa only [h.2.2.1, h.2.2.2.1] using h.1

private theorem startRound_no_cutoff
    (t : Fin p.T) (clock : CoordinatorPhaseClock.ClockRegisters p)
    (pending : Finset (Fin (p.m - 1))) (out : CoordinatorPhaseClock.StartRoundResult p)
    (h : CoordinatorPhaseClock.startRound p rate.eta.val t clock pending = .ok out)
    (hu : out.clock.u = none) :
    CoordinatorPhaseClock.detectCutoff clock t = .ok .noCutoff := by
  classical
  have hp : CoordinatorPhaseClock.proposalParameterValid p rate.eta.val := by
    by_contra hn
    simp only [CoordinatorPhaseClock.startRound, hn, ↓reduceIte] at h
    cases h
  have hv : CoordinatorPhaseClock.clockRegistersValid p rate.eta.val clock := by
    by_contra hn
    simp only [CoordinatorPhaseClock.startRound, hp, hn, ↓reduceDIte, ↓reduceIte] at h
    cases h
  have ht : CoordinatorPhaseClock.startRoundTimeValid p t clock := by
    by_contra hn
    simp only [CoordinatorPhaseClock.startRound, hp, hv, hn, ↓reduceDIte, ↓reduceIte] at h
    cases h
  cases hd : CoordinatorPhaseClock.detectCutoff clock t with
  | error failure =>
      simp only [CoordinatorPhaseClock.startRound, hp, hv, ht, hd, ↓reduceDIte, ↓reduceIte] at h
      cases h
  | ok decision =>
      cases decision with
      | noCutoff => rfl
      | cutoff sigma hsigma =>
          obtain ⟨result, hr, hc, _⟩ := CoordinatorPhaseClock.startRound_cutoff_effect
            p rate.eta.val t sigma clock pending hp hv ht hsigma hd
          have he := Except.ok.inj (h.symm.trans hr)
          rw [he, hc] at hu
          cases hu

/-- PREPARE on an actual continuing record preserves an occupied current
payload's entire local state and memory. Its cutoff test reads the same prior
proposal coordinate as the coordinator; no new launch or reset occurs. -/
private theorem complete_continuing_prepare_occupied
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).length)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r) (base : Fin (p.m - 1) → ℕ)
    (hin : (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val].input.state.coordinator = .live r q base)
    (hc : ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val] = true)
    (i : Fin (p.m - 1)) (before : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hf : (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val].input.state.followers i = .ordinary before memory)
    (ho : before.status ≠ .unoccupied) (hd : before.lastDown = some (r.payload.downRecord i)) :
    (ReferenceFollowerFixedReply.actualChoice
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val] i).configuration = .ordinary before memory := by
  classical
  let record := (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val]
  have hclock := complete_clock rewards C_star C_h z k
  change ReferenceCoordinatorClockDomains.clockAt record.input.rows record.input.selected
    record.input.time.val record.input.state at hclock
  change record.input.state.coordinator = .live r q base at hin
  change ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest record = true at hc
  simp only [ReferenceCoordinatorClockDomains.clockAt, hin] at hclock
  obtain ⟨hst, _hvalid, hsigma, hu, _hg, hstarted, _hgrid, hproposal⟩ := hclock
  have hp : record.output.preparation = prepare record.input := by rw [record.output_eq]; rfl
  have hdata := ReferenceCompleteLiveChoiceDomains.complete_live_dispatch_choice_exists
    rate rewards C_star C_h z k r q base hin
  have hdispatch : record.output.preparation.coordinator = .live r q base
      (CoordinatorRoundDispatch.dispatchLive (liveInput record.input r q base)) := hp ▸ hdata.1
  unfold ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest at hc
  rw [hdispatch] at hc
  cases hchosen : CoordinatorRoundDispatch.dispatchLive (liveInput record.input r q base)
    <;> simp only [hchosen, Bool.false_eq_true] at hc
  rename_i dispatched hstart continuation arm
  have hbranch := hdata.2
  rw [hchosen] at hbranch
  have hnone := hbranch.2.1
  have hdetect := startRound_no_cutoff (rate := rate) record.input.time r.priorClock
    (liveRegistersAt r record.input.time).clockPending dispatched.startResult hstart hnone
  have hread := CoordinatorPhaseClock.savedPriorProposal_correct r.priorClock record.input.time
    r.time _ hproposal hst
  have hcauses : record.input.time.val + 1 ≠ r.priorClock.g ∧
      FollowerCutoffScan.completeRowProposalBit p rate.eta.val record.input.row r.time = false := by
    change CoordinatorPhaseClock.savedPriorProposal r.priorClock record.input.time =
      .ok (FollowerCutoffScan.completeRowProposalBit p rate.eta.val record.input.row r.time) at hread
    generalize heq : r.priorClock = clock at hsigma hu hdetect hread ⊢
    rcases clock with ⟨sigma, u, g, token⟩
    change sigma = some r.payload.sigma at hsigma
    change u = none at hu
    subst sigma
    subst u
    by_cases hg : record.input.time.val + 1 = g
    · simp [CoordinatorPhaseClock.detectCutoff, FollowerCutoffScan.calendarRound, hg] at hdetect
    · refine ⟨hg, ?_⟩
      cases hb : FollowerCutoffScan.completeRowProposalBit p rate.eta.val record.input.row r.time with
      | false => rfl
      | true =>
          simp [CoordinatorPhaseClock.detectCutoff, hread,
            FollowerCutoffScan.calendarRound, hg, hb] at hdetect
          cases hdetect
  obtain ⟨choice, hv, hlocal, hchoice, _⟩ :=
    ReferenceCompleteFollowerPreparation.complete_ordinary_input_prepare
      rewards C_star C_h z k i before memory hf
  obtain ⟨stamp, hstamp, htoken⟩ :=
    ReferenceCompleteFollowerCutoffPhase.complete_ordinary_follower_token
      rate rewards C_star C_h z k i before memory hf ho
  change stamp.val + 1 = record.input.time.val at hstamp
  have he : stamp = r.time := Fin.ext (by omega)
  rw [he] at htoken
  change memory.lastProposalRead = some ⟨r.time,
    FollowerCutoffScan.completeRowProposalBit p rate.eta.val record.input.row r.time⟩ at htoken
  have hfield : (r.payload.downRecord i).val.sigma = r.payload.sigma.val + 1 := by
    rw [r.payload.downRecord_fields i]
  have hcoord : ActiveFollowerLifecycle.acceptedStartCoordinate (r.payload.downRecord i) = r.payload.sigma := by
    apply Fin.ext
    have := ActiveFollowerLifecycle.accepted_start_coordinate_one_based (r.payload.downRecord i)
    omega
  have hgridEq : r.priorClock.g = FollowerCutoffScan.gridBoundary p rate.eta.val r.payload.sigma :=
    by simpa only [CoordinatorPhaseClock.boundaryFromSigma, hsigma] using _hvalid.1
  have hsame : choice = before := by
    have hbound : record.input.time.val + 1 ≤ FollowerCutoffScan.gridBoundary p rate.eta.val r.payload.sigma := by
      rw [← hgridEq]
      omega
    have hs := ActiveFollowerLifecycle.startRound_occupied_branch rate.eta record.input.time
      before memory ho hv (r.payload.downRecord i) hd
      (by rw [hfield]; omega)
      (by simpa only [hcoord] using hbound) _ htoken hst
    rw [hcoord, ← hgridEq, hcauses.2] at hs
    simp only [hcauses.1.symm, decide_false, Bool.false_or, Bool.false_eq_true, ite_false] at hs
    change ActiveFollowerLifecycle.startRound rate.eta record.input.time before memory = .ok (choice, memory) at hlocal
    exact (Prod.mk.inj (Except.ok.inj (hlocal.symm.trans hs))).1
  simpa only [hsame] using hchoice

private theorem complete_selected_fields
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (record : Record (p := p) (rate := rate))
    (hr : record ∈ ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)
    (selected : Selection record.input)
    (hs : record.output.preparation.coordinator.selection = some selected) :
    ∃ (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
      (memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p),
      (∀ i, (ReferenceFollowerFixedReply.actualChoice record i).configuration = .ordinary (states i) (memories i)) ∧
      ∀ i, (states i).status ≠ .unoccupied → (states i).lastDown = some (selected.view.payload.downRecord i) := by
  obtain ⟨index, hi, heq⟩ := List.mem_iff_getElem.mp hr
  subst record
  obtain ⟨states, memories, hc, hf, _⟩ :=
    ReferenceCompletePayloadChoiceChronology.complete_selected_payload_choice_fields
      (rate := rate) rewards C_star C_h z ⟨index, hi⟩ selected hs
  exact ⟨states, memories, hc, hf⟩

private theorem complete_occupied_tail
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).length)
    (i : Fin (p.m - 1)) (choice : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hc : (ReferenceFollowerFixedReply.actualChoice
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val] i).configuration = .ordinary choice memory)
    (ho : choice.status ≠ .unoccupied) :
    let record := (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val]
    ∃ next nextMemory, record.output.next.followers i = .ordinary next nextMemory ∧
      next.status ≠ .unoccupied ∧ next.lastDown = choice.lastDown ∧
      (choice.status = .released → next.status = .released) ∧
      (∀ selected : Selection record.input,
        record.output.preparation.coordinator.selection = some selected →
        selected.view.pendingAtChoice.Nonempty → choice.status = .pending → next.status = .pending) := by
  classical
  let record := (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val]
  obtain ⟨M, hdown, _ht, _hv, b, j, P, beta, hmass⟩ :=
    ReferenceCompleteOccupiedServiceForward.complete_ordinary_occupied_service_forward
      rewards C_star C_h z k i choice memory hc ho
  obtain ⟨_, _, _, _, _, _, _, _, _, hprepared⟩ := hmass
  obtain ⟨_, _, _, _, serviced, next, nextMemory, ht⟩ := hprepared
  rcases ht with ⟨_hchecked, _ha, _hs, _hso, _hab, _hsb, hrecord, _hri, _hrd,
    hfinish, _hstep, _hf, _hdi, _hdd, _hS, _hdelta, _hbacklog, _htransition,
    _hconservation, _hmass, _hvalid, hnextDown, _hbuffer, _hbatch, _hfailure,
    hreleased, _hpending, hnextOccupied, _hread, _houtput, _hfailureOut,
    _hdownInputOut, _hdownOut, hnext⟩
  refine ⟨next, nextMemory, hnext, hnextOccupied, hnextDown,
    (fun hr => hreleased.mpr (Or.inl hr)), ?_⟩
  intro selected hselected hn hpending
  obtain ⟨states, memories, hchoices, hfields, _⟩ :=
    ReferenceCompletePayloadChoiceChronology.complete_selected_payload_choice_fields
      rewards C_star C_h z k selected hselected
  have he := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
    ((hchoices i).symm.trans hc)
  have hlast : choice.lastDown = some (selected.view.payload.downRecord i) := by
    rw [← he.1]
    exact hfields i (by rw [he.1]; exact ho)
  have hprep : record.output.preparation = prepare record.input := by rw [record.output_eq]; rfl
  have h := ReferenceActiveConfirmationRelease.pending_choice_successful_finish_preserves_status
    (prepare record.input) selected (by rw [← hprep]; exact hselected) i choice memory hn
    (by rw [← hprep]; exact hc) hpending hlast serviced.output hrecord next nextMemory hfinish
  exact h.2.1

/-- The actual later birth and continuing prefix obey the literal missing-set
initializer and erase/preserve updates, retaining terminal alternatives. -/
private theorem actual_later_installation_pending_history
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    ∀ b : Fin R.length,
      if ReferenceCollectionPhaseHistory.laterChosen R[b.val].input = true then
      ∃ (rb : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
        (qb : CoordinatorLiveServiceFinish.OwnedRegisters rb)
        (beta : Fin (p.m - 1) → ℕ) (birthSelected : Selection R[b.val].input),
        R[b.val].output.next.coordinator = .live rb qb beta ∧
        InstallationBirth R[b.val] rb.payload ∧
        ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h <
          rb.payload.sigma.val ∧
        R[b.val].output.preparation.coordinator.selection = some birthSelected ∧
        birthSelected.view.payload = rb.payload ∧
        birthSelected.view.pendingAtChoice = Finset.univ ∧
        rb.pendingAtChoice =
          (if ReferenceFirstLiveMissingSetProvenance.actualDownConfirmationEvent R[b.val] birthSelected then
            Finset.univ.erase (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
              (R[b.val].input.row.2 R[b.val].input.time).1)
          else Finset.univ) ∧
        (b.val + 1 = R.length ∨
          ∃ k : Fin R.length, k.val = b.val + 1 ∧
          R[k.val].input.state.coordinator = .live rb qb beta ∧
          let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
            rate rewards C_star C_h z k.val
          ∀ j : Fin W.length,
            ∃ (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
              (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
              (selected : Selection W[j.val].input)
              (next : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
              (owned : CoordinatorLiveServiceFinish.OwnedRegisters next),
              W[j.val].input.state.coordinator = .live r q beta ∧
              r.payload = rb.payload ∧
              W[j.val].output.preparation.coordinator.selection = some selected ∧
              selected.view.payload = rb.payload ∧
              selected.view.pendingAtChoice = r.pendingAtChoice ∧
              W[j.val].output.next.coordinator = .live next owned beta ∧
              next.payload = rb.payload ∧
              next.pendingAtChoice =
                (if ReferenceFirstLiveMissingSetProvenance.actualDownConfirmationEvent W[j.val] selected then
                  selected.view.pendingAtChoice.erase (PublicDiscreteDraws.selectedFollowerDraw
                    p.two_le_m p.m_lt_K (W[j.val].input.row.2 W[j.val].input.time).1)
                else selected.view.pendingAtChoice))
      else True := by
  classical
  intro R b
  split
  · rename_i hb
    obtain ⟨P0, rb, qb, beta, cell, native, _hlen, _hmap, _hprefix, _hinit,
      hnext, hbirth, hlater, _hbase, _hcell0, _hnativeInput, hnp,
      _henabled, _hprefixNext, _hmapNext, _hdown, _hcontinuation⟩ :=
      ReferenceCompleteInstallationCollectionPrefixNumericalTruth.actual_later_installation_collection_prefix_numerical_truth
        rate rewards C_star C_h z b hb
    have hbp := birth_selection_pending R[b.val] rb.payload hbirth hb
      native.selected native.selection_actual
    have hupdate := selected_live_pending_update R[b.val] native.selected native.selection_actual
      hb rb qb beta hnext
    refine ⟨rb, qb, beta, native.selected, hnext, hbirth, hlater,
      native.selection_actual, hnp, hbp.2.1, ?_, ?_⟩
    · simpa only [hbp.2.1] using hupdate.2
    · by_cases hbound : b.val + 1 < R.length
      · right
        let k : Fin R.length := ⟨b.val + 1, hbound⟩
        have hadj := ReferenceCompleteLaterLiveComplementPrefixReplay.complete_adjacent
          (rate := rate) rewards C_star C_h z b.val (by omega)
        have hstate : R[k.val].input.state.coordinator = .live rb qb beta := by
          rw [show R[k.val].input.state = R[b.val].output.next from hadj]
          exact hnext
        refine ⟨k, rfl, hstate, ?_⟩
        intro W j
        obtain ⟨r, q, hp, _hprior, hin⟩ :=
          ReferenceCompleteLaterLiveComplementPrefixReplay.prefix_live
            rewards C_star C_h z k rb qb beta hstate hlater j.val (Nat.le_of_lt j.isLt)
        obtain ⟨next, owned, hnextp, hout, _hinNext⟩ :=
          ReferenceCompleteLaterLiveComplementPrefixReplay.prefix_live
            rewards C_star C_h z k rb qb beta hstate hlater (j.val + 1) (Nat.succ_le_of_lt j.isLt)
        have hrec := ReferenceCompleteLaterLiveComplementPrefixReplay.prefix_index
          rewards C_star C_h z k j.val j.isLt
        have hlength : k.val + W.length ≤ R.length :=
          ReferenceCompleteLaterLiveComplementPrefixReplay.prefix_length_le
            rewards C_star C_h z k
        have hinput : W[j.val].input.state.coordinator = .live r q beta := by
          rw [hrec]
          exact hin (by change k.val + j.val < R.length; have := j.isLt; omega)
        have hn : W[j.val].output.next.coordinator = .live next owned beta := by
          have hidx : j.val + 1 - 1 = j.val := by omega
          have h := hout (Nat.zero_lt_succ j.val)
          have hrecordEq : W[j.val + 1 - 1]'(by have := j.isLt; omega) = W[j.val] :=
            getElem_congr_idx hidx
          exact (congrArg (fun r : Record (p := p) (rate := rate) =>
            r.output.next.coordinator) hrecordEq).symm.trans h
        have htest := ReferenceCompleteLaterLiveComplementPrefixReplay.prefix_test
          rewards C_star C_h z k j.val j.isLt
        have hprep : W[j.val].output.preparation = prepare W[j.val].input := by
          rw [(W[j.val]).output_eq]
          rfl
        obtain ⟨selected, hselected, hpay, hpend, _hstart, _hnp, hafter⟩ :=
          ReferenceFirstLiveMissingSetProvenance.first_live_actual_continuing_pending_frame
            W[j.val].input r q beta hinput (continuing_not_cutoff W[j.val] htest)
            next owned beta (by rw [← (W[j.val]).output_eq]; exact hn)
        refine ⟨r, q, selected, next, owned, hinput, hp, ?_, hpay.trans hp,
          hpend, hn, hnextp, ?_⟩
        · rw [hprep]
          exact hselected
        · have he := (W[j.val]).output_eq
          simpa only [ReferenceFirstLiveMissingSetProvenance.actualDownConfirmationEvent,
            ← hprep, ← he, hpend] using hafter
      · left
        have := b.isLt
        omega
  · trivial


/-- The literal selected missing-set test, evaluated at actual arm choice. -/
public def missingAtChoice
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) : Bool :=
  match record.output.preparation.coordinator.selection with
  | none => false
  | some selected => decide selected.view.pendingAtChoice.Nonempty

private def NoReleased (state : ReferenceActivePhysicalStep.State p rate) : Prop :=
  ∀ i choice memory, state.followers i = .ordinary choice memory →
    choice.status ≠ .released

private theorem prepare_no_released
    (record : Record (p := p) (rate := rate)) (hi : NoReleased record.input.state) :
    ∀ i choice memory, (ReferenceFollowerFixedReply.actualChoice record i).configuration =
      .ordinary choice memory → choice.status ≠ .released := by
  intro i choice memory hc
  have hp : (ReferenceFollowerFixedReply.actualChoice record i).configuration =
      ((prepare record.input).followers.followers i).configuration := by
    change (record.output.preparation.followers.followers i).configuration = _
    rw [record.output_eq]
    rfl
  rw [hp] at hc
  obtain ⟨before, beforeMemory, _offered, hin, hs, _⟩ :=
    ReferenceActiveDataOwnership.prepare_ordinary_choice i record.input.row
      (record.input.state.activations i) record.input.time (record.input.active i)
      (record.input.state.followers i) choice memory hc
  rcases ReferenceActiveDataOwnership.startRound_status record.input.time before choice
      beforeMemory memory hs with hu | he
  · rw [hu]
    decide
  · rw [he]
    exact hi i before beforeMemory hin

private theorem prefix_no_released
    (initial final : ReferenceActivePhysicalStep.State p rate)
    (records segment : List (Record (p := p) (rate := rate)))
    (chain : Connected initial records final) (hp : segment.IsPrefix records)
    (hi : NoReleased initial)
    (hf : ∀ r ∈ segment, ∀ selected : Selection r.input,
      r.output.preparation.coordinator.selection = some selected →
      ∀ i, ReferenceActiveDataOwnership.occupiedFields selected.view.payload i
        (ReferenceFollowerFixedReply.actualChoice r i).configuration)
    (hm : ∀ r ∈ segment, missingAtChoice r = true) :
    ∀ r ∈ segment, ∀ i choice memory,
      (ReferenceFollowerFixedReply.actualChoice r i).configuration = .ordinary choice memory →
      choice.status ≠ .released := by
  obtain ⟨tail, rfl⟩ := hp
  induction segment generalizing initial with
  | nil => simp only [List.not_mem_nil, false_implies, implies_true]
  | cons head rest ih =>
    obtain ⟨hinput, hrest⟩ := chain
    have hbefore : NoReleased head.input.state := hinput ▸ hi
    have hchoice := prepare_no_released head hbefore
    have hmissing := hm head List.mem_cons_self
    cases hselected : head.output.preparation.coordinator.selection with
    | none => simp only [missingAtChoice, hselected, Bool.false_eq_true] at hmissing
    | some selected =>
      have hn : selected.view.pendingAtChoice.Nonempty := by
        exact of_decide_eq_true (by simpa only [missingAtChoice, hselected] using hmissing)
      have hnext : NoReleased head.output.next := by
        intro i next nextMemory hout
        have heq : head.output.preparation = prepare head.input := by rw [head.output_eq]; rfl
        apply ReferenceFirstLiveConfirmationHistory.selected_output_not_released head.input selected
          (by rw [← heq]; exact hselected) hn i
          (by rw [← heq]; exact hf head List.mem_cons_self selected hselected i)
          (by
            intro choice memory hc
            apply hchoice i choice memory
            change (head.output.preparation.followers.followers i).configuration = _
            rw [heq]
            exact hc)
          next nextMemory
        rw [← head.output_eq]
        exact hout
      have hrestChoices := ih head.output.next hnext
        (fun r hr => hf r (List.mem_cons_of_mem head hr))
        (fun r hr => hm r (List.mem_cons_of_mem head hr)) hrest
      intro r hmem
      rcases List.mem_cons.mp hmem with he | he
      · subst r
        exact hchoice
      · exact hrestChoices r he

private theorem actual_birth_initializer
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (P : Payload rate)
    (hb : InstallationBirth (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[b.val] P) :
    ∀ (i : Fin (p.m - 1)) (choice : ReferencePrelaunchFollower.State p rate.eta)
      (memory : ActiveFollowerLifecycle.LocalMemory p),
      (ReferenceFollowerFixedReply.actualChoice
        (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[b.val] i).configuration = .ordinary choice memory →
      choice.status = .unoccupied ∧ ∃ before beforeMemory,
        (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[b.val].input.state.followers i = .ordinary before beforeMemory ∧
        before.status = .unoccupied ∧ ReferenceFollowerReplyChronology.reply choice = ReferenceFollowerReplyChronology.reply before ∧
        choice.downBatch = before.downBatch ∧ choice.buffer = before.buffer ∧
        choice.initializationFailure = before.initializationFailure ∧ memory = beforeMemory := by
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  have hlen : R.length = p.T - s :=
    ReferenceCompletePhysicalHistory.completeSuffixRecords_length rate z rewards C_star C_h
  have hbnd : b.val < R.length := b.isLt
  obtain ⟨hs, x, _hx, hrecords⟩ := complete_generated_records rate rewards C_star C_h z
    (by change 0 < R.length; omega)
  let n : Fin (p.T - s) := ⟨b.val, by omega⟩
  have hget := ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt_getElem?
    rate rewards C_star C_h s hs x n
  rw [← hrecords] at hget
  have hrecord : R[b.val] = ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
      rate rewards C_star C_h s hs x n :=
    Option.some.inj ((List.getElem?_eq_getElem b.isLt).symm.trans hget)
  have hbirth := hb
  change InstallationBirth R[b.val] P at hbirth
  rw [hrecord] at hbirth
  intro i choice memory hc
  have hcGen : (ReferenceFollowerFixedReply.actualChoice
      (ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
        rate rewards C_star C_h s hs x n) i).configuration = .ordinary choice memory := by
    rw [← hrecord]
    exact hc
  have hinit := ReferenceGeneratedInstallationFollowerSeed.generated_installation_choice_unoccupied
    rate rewards C_star C_h s hs x i n P hbirth choice memory hcGen
  rw [← hrecord] at hinit
  obtain ⟨hchoice, before, beforeMemory, hin, hu, hr, hd, hb, hf, hm, _⟩ := hinit
  exact ⟨hchoice, before, beforeMemory, hin, hu, hr, hd, hb, hf, hm⟩

private theorem actual_birth_no_confirmation
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).length)
    (P : Payload rate) (hb : InstallationBirth
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[b.val] P)
    (selected : Selection (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[b.val].input)
    (hs : (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[b.val].output.preparation.coordinator.selection = some selected) :
    ¬ ReferenceFirstLiveMissingSetProvenance.actualDownConfirmationEvent
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[b.val] selected := by
  intro he
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let i := PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K (R[b.val].input.row.2 R[b.val].input.time).1
  obtain ⟨_before, memory, choice, _hin, _hv, _hstart, hc, _⟩ :=
    ReferenceCompleteSuffixFollowerPreservation.complete_suffix_follower_choice
      (rate := rate) rewards C_star C_h z b i
  have hu := (actual_birth_initializer rate rewards C_star C_h z b P hb i choice memory hc).1
  have ho := ReferenceActiveConfirmationRelease.downConfirmationEvent_implies_occupied
    R[b.val].output.preparation selected hs choice memory hc he
  rcases ho with ho | ho <;> rw [hu] at ho <;> cases ho

/-- No follower is released on the actual pre-clear prefix. The connected
induction retains the inherited decoder bank, buffer, word, reply, and memory. -/
private theorem actual_later_installation_no_release_before_clear
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    ∀ b : Fin R.length,
      if ReferenceCollectionPhaseHistory.laterChosen R[b.val].input = true then
        let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
          rate rewards C_star C_h z (b.val + 1)
        let V := R[b.val] :: W
        let H := V.takeWhile missingAtChoice
        ∀ r ∈ H, ∀ (i : Fin (p.m - 1))
          (choice : ReferencePrelaunchFollower.State p rate.eta)
          (memory : ActiveFollowerLifecycle.LocalMemory p),
          (ReferenceFollowerFixedReply.actualChoice r i).configuration = .ordinary choice memory →
          choice.status ≠ .released
      else True := by
  classical
  intro R b
  split
  · rename_i hb
    have hh := actual_later_installation_pending_history rate rewards C_star C_h z b
    rw [ite_eq_left hb] at hh
    obtain ⟨rb, _qb, _beta, _selected, _hnext, hbirth, _hlater, _⟩ := hh
    have hbefore : NoReleased R[b.val].input.state := by
      intro i before memory hin
      obtain ⟨_input, cm, choice, _hin, _hv, _hs, hc, _⟩ :=
        ReferenceCompleteSuffixFollowerPreservation.complete_suffix_follower_choice
          (rate := rate) rewards C_star C_h z b i
      obtain ⟨_, old, oldMemory, hold, hu, _⟩ :=
        actual_birth_initializer rate rewards C_star C_h z b rb.payload hbirth i choice cm hc
      have he := (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj (hold.symm.trans hin)).1
      rw [← he, hu]
      decide
    intro W V H
    have hW : W.IsPrefix (R.drop (b.val + 1)) := List.takeWhile_prefix _
    have hV : V.IsPrefix (R.drop b.val) := by
      rw [List.drop_eq_getElem_cons b.isLt]
      obtain ⟨tail, htail⟩ := hW
      exact ⟨tail, by simpa only [V, List.cons_append] using congrArg (List.cons R[b.val]) htail⟩
    have hH : H.IsPrefix (R.drop b.val) := (List.takeWhile_prefix missingAtChoice).trans hV
    obtain ⟨hc, _⟩ := ReferenceLaterLiveNumericalReadout.source_record_prefix
      rate rewards C_star C_h z b
    have hchain := ReferenceCompletePhysicalHistory.completeSuffix_connected_on_launch
      rate z rewards C_star C_h
      (ReferenceFirstLaunchNumericalCell.launchState rate z rewards C_star C_h hc)
      (ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
        rate z rewards C_star C_h hc)
    have hdrop := ReferenceFollowerReplyChronology.connected_drop_from_input hchain b.val b.isLt
    apply prefix_no_released R[b.val].input.state _ (R.drop b.val) H hdrop hH hbefore
    · intro r hr selected hselected i
      have hrR : r ∈ R := List.mem_of_mem_drop (hH.subset hr)
      obtain ⟨states, memories, hchoices, hdowns⟩ :=
        complete_selected_fields rewards C_star C_h z r hrR selected hselected
      rw [hchoices i]
      exact hdowns i
    · intro r hr
      exact List.mem_takeWhile_imp hr
  · trivial


/-- Omitted followers are occupied at the current CHOICE. Actual service
preserves occupancy and released status, keeps pending while missing, and
passes its entire successor through the next continuing PREPARE. -/
private theorem actual_later_installation_occupancy_history
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    ∀ b : Fin R.length,
      if ReferenceCollectionPhaseHistory.laterChosen R[b.val].input = true then
        ∃ (birthRegisters : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
          (birthOwned : CoordinatorLiveServiceFinish.OwnedRegisters birthRegisters)
          (birthBeta : Fin (p.m - 1) → ℕ)
          (birthChoice : Selection R[b.val].input) (P : Payload rate),
          R[b.val].output.next.coordinator = .live birthRegisters birthOwned birthBeta ∧
          InstallationBirth R[b.val] P ∧
          R[b.val].output.preparation.coordinator.selection = some birthChoice ∧
          birthChoice.view.payload = birthRegisters.payload ∧
          P = birthRegisters.payload ∧
        let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
          rate rewards C_star C_h z (b.val + 1)
        ∀ j : Fin W.length,
          ∃ (selected : Selection W[j.val].input)
            (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
            (memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p),
            W[j.val].output.preparation.coordinator.selection = some selected ∧
            selected.view.payload = P ∧
            (∀ i, (ReferenceFollowerFixedReply.actualChoice W[j.val] i).configuration =
              .ordinary (states i) (memories i)) ∧
            (∀ i, i ∉ selected.view.pendingAtChoice → (states i).status ≠ .unoccupied) ∧
            (ReferenceFirstLiveMissingSetProvenance.actualDownConfirmationEvent W[j.val] selected →
              selected.view.pendingAtChoice.erase (PublicDiscreteDraws.selectedFollowerDraw
                p.two_le_m p.m_lt_K (W[j.val].input.row.2 W[j.val].input.time).1) = ∅ →
              ∀ i, (states i).status ≠ .unoccupied) ∧
            ∀ i, (states i).status = .unoccupied ∨
              ∃ next nextMemory, W[j.val].output.next.followers i = .ordinary next nextMemory ∧
                next.status ≠ .unoccupied ∧ next.lastDown = (states i).lastDown ∧
                ((states i).status = .released → next.status = .released) ∧
                (selected.view.pendingAtChoice.Nonempty → (states i).status = .pending →
                  next.status = .pending) ∧
                ∀ h : j.val + 1 < W.length,
                  (ReferenceFollowerFixedReply.actualChoice W[j.val + 1] i).configuration =
                    .ordinary next nextMemory
      else True := by
  classical
  intro R b
  have hRlen : R.length = (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).length := rfl
  split
  · rename_i hb
    have hh := actual_later_installation_pending_history rate rewards C_star C_h z b
    rw [ite_eq_left hb] at hh
    obtain ⟨rb, qb, beta, birthSelected, hnext, hbirth, _hlater,
      hbs, hbp, hfull, hupdate, htail⟩ := hh
    have hnoEvent := actual_birth_no_confirmation rewards C_star C_h z b rb.payload hbirth birthSelected hbs
    rw [ite_eq_right hnoEvent] at hupdate
    rcases htail with hterminal | ⟨k, hk, hinput, hframes⟩
    · refine ⟨rb, qb, beta, birthSelected, rb.payload, hnext, hbirth,
        hbs, hbp, rfl, ?_⟩
      intro W j
      have hlength := ReferenceCompletePhysicalHistory.completeSuffixRecords_length rate z rewards C_star C_h
      have hW : W = [] := by
        simp only [W, ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix,
          hterminal, List.drop_length, List.takeWhile_nil]
      have := j.isLt
      simp only [hW, List.length_nil] at this
      omega
    · rcases k with ⟨kval, hkbound⟩
      change kval = b.val + 1 at hk
      subst kval
      let k : Fin R.length := ⟨b.val + 1, hkbound⟩
      let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
        rate rewards C_star C_h z k.val
      have hlen : k.val + W.length ≤ R.length :=
        ReferenceCompleteLaterLiveComplementPrefixReplay.prefix_length_le rewards C_star C_h z k
      change ∀ j : Fin W.length, _ at hframes
      have hindex : ∀ j (hj : j < W.length), W[j] = R[k.val + j]'(by omega) := fun j hj => ReferenceCompleteLaterLiveComplementPrefixReplay.prefix_index
            rewards C_star C_h z k j hj
      have hmember : ∀ j (hj : j < W.length), W[j] ∈ R := by
        intro j hj
        rw [hindex j hj]
        exact List.getElem_mem _
      have hadj : ∀ j (hj : j + 1 < W.length), W[j + 1].input.state = W[j].output.next := by
        intro j hj
        rw [hindex (j + 1) hj, hindex j (by omega)]
        have ha := ReferenceCompleteLaterLiveComplementPrefixReplay.complete_adjacent
          (rate := rate) rewards C_star C_h z (k.val + j)
          (by omega)
        simpa only [Nat.add_assoc] using ha
      have hocc : ∀ n (hn : n < W.length), ∀ (selected : Selection W[n].input),
          W[n].output.preparation.coordinator.selection = some selected →
          ∀ i choice memory, (ReferenceFollowerFixedReply.actualChoice W[n] i).configuration =
            .ordinary choice memory → i ∉ selected.view.pendingAtChoice → choice.status ≠ .unoccupied := by
        intro n
        induction n with
        | zero =>
          intro hn selected hs i choice memory _hc hi
          obtain ⟨r, q, sel, next, owned, hin, _hrpayload, hsel, _hp, hpend, _⟩ :=
            hframes ⟨0, hn⟩
          have hselEq := Option.some.inj (hsel.symm.trans hs)
          subst sel
          have hin0 : W[0].input.state.coordinator = .live rb qb beta := by
            rw [hindex 0 hn]
            simpa only [Nat.add_zero] using hinput
          have hr := (CoordinatorConfiguration.live.inj (hin.symm.trans hin0)).1
          have hfull0 : selected.view.pendingAtChoice = Finset.univ := by
            rw [hpend, hr, hupdate]
          exact False.elim (hi (hfull0 ▸ Finset.mem_univ i))
        | succ n ih =>
          intro hn selected hs i choice memory hc hi
          obtain ⟨r0, q0, sel0, out0, own0, _hin0, _hrpayload0, hs0, hp0,
            _hpend0, hout0, hpout0, hu0⟩ := hframes ⟨n, by omega⟩
          obtain ⟨r1, q1, sel1, out1, own1, hin1, _hrpayload1, hs1, hp1,
            hpend1, _hout1, _hpout1, _hu1⟩ := hframes ⟨n + 1, hn⟩
          have hselEq := Option.some.inj (hs1.symm.trans hs)
          subst sel1
          have hr := (CoordinatorConfiguration.live.inj
            (hin1.symm.trans ((congrArg (fun s : ReferenceActivePhysicalStep.State p rate => s.coordinator) (hadj n hn)).trans hout0))).1
          have hi0 : i ∉ out0.pendingAtChoice := by simpa only [hpend1, hr] using hi
          obtain ⟨_before, mem0, choice0, _hin, _hv, _hs, hc0, _⟩ :=
            ReferenceCompleteSuffixFollowerPreservation.complete_suffix_follower_choice
              (rate := rate)               rewards C_star C_h z ⟨k.val + n, by omega⟩ i
          rw [← hindex n (by omega)] at hc0
          have ho0 : choice0.status ≠ .unoccupied := by
            by_cases hiMissing : i ∈ sel0.view.pendingAtChoice
            · have he : ReferenceFirstLiveMissingSetProvenance.actualDownConfirmationEvent W[n] sel0 := by
                by_contra hne
                rw [hu0, ite_eq_right hne] at hi0
                exact hi0 hiMissing
              have hiDraw : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
                  (W[n].input.row.2 W[n].input.time).1 = i := by
                by_contra hne
                rw [hu0, ite_eq_left he] at hi0
                exact hi0 (Finset.mem_erase.mpr ⟨Ne.symm hne, hiMissing⟩)
              have hoc := ReferenceActiveConfirmationRelease.downConfirmationEvent_implies_occupied
                W[n].output.preparation sel0 hs0 choice0 mem0 (by rw [hiDraw]; exact hc0) he
              rcases hoc with hoc | hoc <;> rw [hoc] <;> decide
            · exact ih (by omega) sel0 hs0 i choice0 mem0 hc0 hiMissing
          obtain ⟨next, nextMemory, hnextF, hnextO, hnextD, _⟩ :=
            complete_occupied_tail rewards C_star C_h z
              ⟨k.val + n, by omega⟩
              i choice0 mem0 (by rw [← hindex n (by omega)]; exact hc0) ho0
          rw [← hindex n (by omega)] at hnextF
          obtain ⟨states, memories, hchoices, hfields⟩ :=
            complete_selected_fields rewards C_star C_h z W[n] (hmember n (by omega)) sel0 hs0
          have hcd : choice0.lastDown = some (rb.payload.downRecord i) := by
            have heq := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
              ((hchoices i).symm.trans hc0)
            simpa only [heq.1, hp0] using hfields i (by rw [heq.1]; exact ho0)
          have hprep := complete_continuing_prepare_occupied rewards C_star C_h z
            ⟨k.val + (n + 1), by omega⟩
            r1 q1 beta (by rw [← hindex (n + 1) hn]; exact hin1)
            (by rw [← hindex (n + 1) hn]; exact
              ReferenceCompleteLaterLiveComplementPrefixReplay.prefix_test rewards C_star C_h z k (n + 1) hn)
            i next nextMemory (by rw [← hindex (n + 1) hn, hadj n hn]; exact hnextF)
            hnextO (by rw [hnextD, hcd, hr, hpout0])
          rw [← hindex (n + 1) hn] at hprep
          have heq := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj (hprep.symm.trans hc)
          exact heq.1 ▸ hnextO
      refine ⟨rb, qb, beta, birthSelected, rb.payload, hnext, hbirth,
        hbs, hbp, rfl, ?_⟩
      dsimp only
      intro j
      have hj : j.val < W.length := j.isLt
      obtain ⟨r, q, sel, out, owned, hin, _hrpayload, hs, hp, _hpend,
        hout, hpout, _⟩ := hframes j
      let idx : Fin R.length := ⟨k.val + j.val, by omega⟩
      obtain ⟨states, memories, hchoices, hfields⟩ :=
        complete_selected_fields rewards C_star C_h z W[j.val] (hmember j.val j.isLt) sel hs
      refine ⟨sel, states, memories, hs, hp, hchoices, ?_, ?_, ?_⟩
      · intro i hi
        exact hocc j.val j.isLt sel hs i (states i) (memories i) (hchoices i) hi
      · intro he hempty i
        by_cases hi : i ∈ sel.view.pendingAtChoice
        · have hdraw : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
              (W[j.val].input.row.2 W[j.val].input.time).1 = i := by
            by_contra hne
            have hm := Finset.mem_erase.mpr ⟨Ne.symm hne, hi⟩
            rw [hempty] at hm
            exact Finset.notMem_empty i hm
          have hoc := ReferenceActiveConfirmationRelease.downConfirmationEvent_implies_occupied
            W[j.val].output.preparation sel hs (states i) (memories i)
            (by rw [hdraw]; exact hchoices i) he
          rcases hoc with hoc | hoc <;> rw [hoc] <;> decide
        · exact hocc j.val j.isLt sel hs i (states i) (memories i) (hchoices i) hi
      · intro i
        by_cases ho : (states i).status = .unoccupied
        · exact Or.inl ho
        · right
          obtain ⟨next, nextMemory, hn, hno, hnd, hrel, hpend⟩ := complete_occupied_tail
            rewards C_star C_h z idx i (states i) (memories i)
            (by rw [← hindex j.val j.isLt]; exact hchoices i) ho
          change ∀ selected : Selection (R[idx.val]).input, _ at hpend
          rw [← hindex j.val j.isLt] at hn hpend
          refine ⟨next, nextMemory, hn, hno, hnd, hrel, hpend sel hs, ?_⟩
          intro hj
          have hjNext : j.val + 1 < W.length := hj
          obtain ⟨r1, q1, sel1, out1, own1, hin1, _hrpayload1, hs1, hp1,
            _hpend1, _hout1, _hpout1, _hupdate1⟩ := hframes ⟨j.val + 1, hj⟩
          have hr := (CoordinatorConfiguration.live.inj
            (hin1.symm.trans ((congrArg (fun s : ReferenceActivePhysicalStep.State p rate => s.coordinator)
              (hadj j.val hj)).trans hout))).1
          rw [hindex (j.val + 1) hj]
          apply complete_continuing_prepare_occupied rewards C_star C_h z
            ⟨k.val + (j.val + 1), by omega⟩
            r1 q1 beta (by rw [← hindex (j.val + 1) hj]; exact hin1)
            (by rw [← hindex (j.val + 1) hj]; exact
              ReferenceCompleteLaterLiveComplementPrefixReplay.prefix_test rewards C_star C_h z k (j.val + 1) hj)
            i next nextMemory (by rw [← hindex (j.val + 1) hj, hadj j.val hj]; exact hn) hno
          rw [hnd]
          have hd := hfields i ho
          simpa only [hp, hr, hpout] using hd
  · trivial


/-- The actual later installation carries one common payload, missing-set
history, follower initialization, and occupied-choice continuation. Every
witness below belongs to the original complete physical run and is identified
through its actual output or choice-selection equation. -/
public theorem actual_later_installation_choice_history
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    ∀ b : Fin R.length,
      if ReferenceCollectionPhaseHistory.laterChosen R[b.val].input = true then
        ∃ (rb : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
          (qb : CoordinatorLiveServiceFinish.OwnedRegisters rb)
          (beta : Fin (p.m - 1) → ℕ) (birthSelected : Selection R[b.val].input),
          R[b.val].output.next.coordinator = .live rb qb beta ∧
          InstallationBirth R[b.val] rb.payload ∧
          ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h <
            rb.payload.sigma.val ∧
          R[b.val].output.preparation.coordinator.selection = some birthSelected ∧
          birthSelected.view.payload = rb.payload ∧
          birthSelected.view.pendingAtChoice = Finset.univ ∧
          rb.pendingAtChoice = Finset.univ ∧
          ¬ ReferenceFirstLiveMissingSetProvenance.actualDownConfirmationEvent
            R[b.val] birthSelected ∧
          (∀ i : Fin (p.m - 1),
            ∃ (before : ReferencePrelaunchFollower.State p rate.eta)
              (beforeMemory : ActiveFollowerLifecycle.LocalMemory p)
              (choice : ReferencePrelaunchFollower.State p rate.eta)
              (choiceMemory : ActiveFollowerLifecycle.LocalMemory p),
              R[b.val].input.state.followers i = .ordinary before beforeMemory ∧
              before.status = .unoccupied ∧
              (ReferenceFollowerFixedReply.actualChoice R[b.val] i).configuration =
                .ordinary choice choiceMemory ∧
              choice.status = .unoccupied ∧
              ReferenceFollowerReplyChronology.reply choice =
                ReferenceFollowerReplyChronology.reply before ∧
              choice.downBatch = before.downBatch ∧
              choice.buffer = before.buffer ∧
              choice.initializationFailure = before.initializationFailure ∧
              choiceMemory = beforeMemory) ∧
          (b.val + 1 = R.length ∨
            ∃ k : Fin R.length, k.val = b.val + 1 ∧
              R[k.val].input.state.coordinator = .live rb qb beta ∧
              let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
                rate rewards C_star C_h z k.val
              ∀ j : Fin W.length,
                ∃ (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
                  (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
                  (selected : Selection W[j.val].input)
                  (next : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
                  (owned : CoordinatorLiveServiceFinish.OwnedRegisters next),
                  W[j.val].input.state.coordinator = .live r q beta ∧
                  r.payload = rb.payload ∧
                  W[j.val].output.preparation.coordinator.selection = some selected ∧
                  selected.view.payload = rb.payload ∧
                  selected.view.pendingAtChoice = r.pendingAtChoice ∧
                  W[j.val].output.next.coordinator = .live next owned beta ∧
                  next.payload = rb.payload ∧
                  next.pendingAtChoice =
                    (if ReferenceFirstLiveMissingSetProvenance.actualDownConfirmationEvent
                        W[j.val] selected then
                      selected.view.pendingAtChoice.erase
                        (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
                          (W[j.val].input.row.2 W[j.val].input.time).1)
                    else selected.view.pendingAtChoice)) ∧
          (let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
              rate rewards C_star C_h z (b.val + 1)
            let V := R[b.val] :: W
            let H := V.takeWhile missingAtChoice
            ∀ r ∈ H, ∀ (i : Fin (p.m - 1))
              (choice : ReferencePrelaunchFollower.State p rate.eta)
              (memory : ActiveFollowerLifecycle.LocalMemory p),
              (ReferenceFollowerFixedReply.actualChoice r i).configuration =
                .ordinary choice memory →
              choice.status ≠ .released) ∧
          (let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
              rate rewards C_star C_h z (b.val + 1)
            ∀ j : Fin W.length,
              ∃ (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
                (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
                (selected : Selection W[j.val].input)
                (next : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
                (owned : CoordinatorLiveServiceFinish.OwnedRegisters next)
                (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
                (memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p),
                W[j.val].input.state.coordinator = .live r q beta ∧
                r.payload = rb.payload ∧
                W[j.val].output.preparation.coordinator.selection = some selected ∧
                selected.view.payload = rb.payload ∧
                selected.view.pendingAtChoice = r.pendingAtChoice ∧
                W[j.val].output.next.coordinator = .live next owned beta ∧
                next.payload = rb.payload ∧
                next.pendingAtChoice =
                  (if ReferenceFirstLiveMissingSetProvenance.actualDownConfirmationEvent
                      W[j.val] selected then
                    selected.view.pendingAtChoice.erase
                      (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
                        (W[j.val].input.row.2 W[j.val].input.time).1)
                  else selected.view.pendingAtChoice) ∧
                (∀ i, (ReferenceFollowerFixedReply.actualChoice W[j.val] i).configuration =
                  .ordinary (states i) (memories i)) ∧
                (∀ i, i ∉ selected.view.pendingAtChoice →
                  (states i).status ≠ .unoccupied) ∧
                (ReferenceFirstLiveMissingSetProvenance.actualDownConfirmationEvent
                    W[j.val] selected →
                  selected.view.pendingAtChoice.erase
                    (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
                      (W[j.val].input.row.2 W[j.val].input.time).1) = ∅ →
                  ∀ i, (states i).status ≠ .unoccupied) ∧
                ∀ i, (states i).status = .unoccupied ∨
                  ∃ (nextFollower : ReferencePrelaunchFollower.State p rate.eta)
                    (nextMemory : ActiveFollowerLifecycle.LocalMemory p),
                    W[j.val].output.next.followers i =
                      .ordinary nextFollower nextMemory ∧
                    nextFollower.status ≠ .unoccupied ∧
                    nextFollower.lastDown = (states i).lastDown ∧
                    ((states i).status = .released →
                      nextFollower.status = .released) ∧
                    (selected.view.pendingAtChoice.Nonempty →
                      (states i).status = .pending →
                      nextFollower.status = .pending) ∧
                    ∀ h : j.val + 1 < W.length,
                      (ReferenceFollowerFixedReply.actualChoice W[j.val + 1] i).configuration =
                        .ordinary nextFollower nextMemory)
      else True := by
  classical
  intro R b
  split
  · rename_i hb
    have hpending :=
      actual_later_installation_pending_history rate rewards C_star C_h z b
    rw [ite_eq_left hb] at hpending
    obtain ⟨rb, qb, beta, birthSelected, hnext, hbirth, hlater,
      hbirthSelection, hbirthPayload, hbirthPending, hbirthUpdate, htail⟩ := hpending
    have hnoBirthEvent := actual_birth_no_confirmation
      rewards C_star C_h z b rb.payload hbirth birthSelected hbirthSelection
    have hafterBirth : rb.pendingAtChoice = Finset.univ := by
      rw [ite_eq_right hnoBirthEvent] at hbirthUpdate
      exact hbirthUpdate
    have hfollowers :
        ∀ i : Fin (p.m - 1),
          ∃ (before : ReferencePrelaunchFollower.State p rate.eta)
            (beforeMemory : ActiveFollowerLifecycle.LocalMemory p)
            (choice : ReferencePrelaunchFollower.State p rate.eta)
            (choiceMemory : ActiveFollowerLifecycle.LocalMemory p),
            R[b.val].input.state.followers i = .ordinary before beforeMemory ∧
            before.status = .unoccupied ∧
            (ReferenceFollowerFixedReply.actualChoice R[b.val] i).configuration =
              .ordinary choice choiceMemory ∧
            choice.status = .unoccupied ∧
            ReferenceFollowerReplyChronology.reply choice =
              ReferenceFollowerReplyChronology.reply before ∧
            choice.downBatch = before.downBatch ∧
            choice.buffer = before.buffer ∧
            choice.initializationFailure = before.initializationFailure ∧
            choiceMemory = beforeMemory := by
      intro i
      obtain ⟨before, beforeMemory, choice, _hinput, _hvalid, _hstart,
        hchoice, _hchoiceDomain, _hoperationDomain⟩ :=
        ReferenceCompleteSuffixFollowerPreservation.complete_suffix_follower_choice
          (rate := rate) rewards C_star C_h z b i
      obtain ⟨hchoiceUnoccupied, old, oldMemory, hinput, hbeforeUnoccupied,
        hreply, hbatch, hbuffer, hfailure, hmemory⟩ :=
        actual_birth_initializer rate rewards C_star C_h z b rb.payload hbirth
          i choice beforeMemory hchoice
      exact ⟨old, oldMemory, choice, beforeMemory, hinput, hbeforeUnoccupied,
        hchoice, hchoiceUnoccupied, hreply, hbatch, hbuffer, hfailure, hmemory⟩
    have hnoRelease :=
      actual_later_installation_no_release_before_clear rate rewards C_star C_h z b
    rw [ite_eq_left hb] at hnoRelease
    have hoccupancy :=
      actual_later_installation_occupancy_history rate rewards C_star C_h z b
    rw [ite_eq_left hb] at hoccupancy
    obtain ⟨birthRegisters, _birthOwned, _birthBeta, birthChoice, P,
      hbirthOutputOcc, _hbirthOcc, hbirthSelectionOcc, _hbirthPayloadOcc,
      hP, hoccupancyFrames⟩ := hoccupancy
    have hbirthRegistersEq : birthRegisters = rb :=
      (CoordinatorConfiguration.live.inj (hbirthOutputOcc.symm.trans hnext)).1
    have hpayloadEq : P = rb.payload :=
      hP.trans (congrArg (fun registers => registers.payload) hbirthRegistersEq)
    have hbirthChoiceEq : birthChoice = birthSelected :=
      Option.some.inj (hbirthSelectionOcc.symm.trans hbirthSelection)
    subst birthChoice
    have hcombined :
        let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
          rate rewards C_star C_h z (b.val + 1)
        ∀ j : Fin W.length,
          ∃ (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
            (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
            (selected : Selection W[j.val].input)
            (next : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
            (owned : CoordinatorLiveServiceFinish.OwnedRegisters next)
            (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
            (memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p),
            W[j.val].input.state.coordinator = .live r q beta ∧
            r.payload = rb.payload ∧
            W[j.val].output.preparation.coordinator.selection = some selected ∧
            selected.view.payload = rb.payload ∧
            selected.view.pendingAtChoice = r.pendingAtChoice ∧
            W[j.val].output.next.coordinator = .live next owned beta ∧
            next.payload = rb.payload ∧
            next.pendingAtChoice =
              (if ReferenceFirstLiveMissingSetProvenance.actualDownConfirmationEvent
                  W[j.val] selected then
                selected.view.pendingAtChoice.erase
                  (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
                    (W[j.val].input.row.2 W[j.val].input.time).1)
              else selected.view.pendingAtChoice) ∧
            (∀ i, (ReferenceFollowerFixedReply.actualChoice W[j.val] i).configuration =
              .ordinary (states i) (memories i)) ∧
            (∀ i, i ∉ selected.view.pendingAtChoice →
              (states i).status ≠ .unoccupied) ∧
            (ReferenceFirstLiveMissingSetProvenance.actualDownConfirmationEvent
                W[j.val] selected →
              selected.view.pendingAtChoice.erase
                (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
                  (W[j.val].input.row.2 W[j.val].input.time).1) = ∅ →
              ∀ i, (states i).status ≠ .unoccupied) ∧
            ∀ i, (states i).status = .unoccupied ∨
              ∃ (nextFollower : ReferencePrelaunchFollower.State p rate.eta)
                (nextMemory : ActiveFollowerLifecycle.LocalMemory p),
                W[j.val].output.next.followers i = .ordinary nextFollower nextMemory ∧
                nextFollower.status ≠ .unoccupied ∧
                nextFollower.lastDown = (states i).lastDown ∧
                ((states i).status = .released → nextFollower.status = .released) ∧
                (selected.view.pendingAtChoice.Nonempty →
                  (states i).status = .pending →
                  nextFollower.status = .pending) ∧
                ∀ h : j.val + 1 < W.length,
                  (ReferenceFollowerFixedReply.actualChoice W[j.val + 1] i).configuration =
                    .ordinary nextFollower nextMemory := by
      intro W j
      rcases htail with hterminal | ⟨k, hk, hnextInput, hframes⟩
      · have hW : W = [] := by
          simp only [W, ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix,
            hterminal, List.drop_length, List.takeWhile_nil]
        have hj := j.isLt
        simp only [hW, List.length_nil] at hj
        omega
      · rcases k with ⟨kval, hkbound⟩
        change kval = b.val + 1 at hk
        subst kval
        obtain ⟨r, q, selectedC, next, owned, hinput, hrPayload,
          hselectedC, hselectedPayloadC, hpending, houtput, hnextPayload,
          hupdate⟩ := hframes j
        obtain ⟨selectedE, states, memories, hselectedE, hselectedPayloadE,
          hchoices, homitted, hlast, hsteps⟩ := hoccupancyFrames j
        have hselectedEq : selectedE = selectedC :=
          Option.some.inj (hselectedE.symm.trans hselectedC)
        subst selectedE
        have hselectedPayload : selectedC.view.payload = rb.payload := by
          rw [hpayloadEq] at hselectedPayloadE
          exact hselectedPayloadE
        exact ⟨r, q, selectedC, next, owned, states, memories,
          hinput, hrPayload, hselectedC, hselectedPayload, hpending,
          houtput, hnextPayload, hupdate, hchoices, homitted, hlast, hsteps⟩
    refine ⟨rb, qb, beta, birthSelected, hnext, hbirth, hlater,
      hbirthSelection, hbirthPayload, hbirthPending, hafterBirth,
      hnoBirthEvent, hfollowers, htail, hnoRelease, hcombined⟩
  · trivial
