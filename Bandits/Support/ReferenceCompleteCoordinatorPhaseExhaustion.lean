/-
Copyright (c) 2026 The Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteEmptyCorrectedCoordinatorStep
public import Bandits.Support.ReferenceCompleteEmptyRenewalCoordinatorStep
public import Bandits.Support.ReferenceCompleteContinuingLiveCoordinatorStep
public import Bandits.Support.ReferenceCompleteCutoffCoordinatorPostChoice

/-!
# Coordinator phase exhaustion along the actual complete suffix

The local phase results are applied at their original complete-source indices.
Induction over the connected physical records then removes the incoming
non-dagger condition. This concerns coordinator reachability and local phase
success only.

Sources: `sources/zip4/manuscript/06_interruptions.tex:9-100,246-299,355-390`
and `sources/zip4/manuscript/appendix_a_local_protocol.tex:28-84`.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceCompletePhysicalHistory

namespace Bandits.Support.ReferenceCompleteCoordinatorPhaseExhaustion

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

private theorem record_next_coordinator (r : RoundRecord p rate) :
    r.output.next.coordinator = r.output.coordinator.configuration := by
  rw [r.output_eq]
  exact (ReferenceActivePhysicalStep.step_next_fields r.input).1

private theorem selected_live_success
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (completeSuffixRecords rate source rewards C_star C_h).length)
    (v : Selection ((completeSuffixRecords rate source rewards C_star C_h)[k.val]'k.isLt).input)
    (hselected :
      ((completeSuffixRecords rate source rewards C_star C_h)[k.val]'k.isLt).output.preparation.coordinator.selection =
        some v)
    (hlive : CoordinatorLocalArmChoice.assignmentIsLive v.view.payload v.view.cutoff
      ((completeSuffixRecords rate source rewards C_star C_h)[k.val]'k.isLt).input.time) :
    let r := (completeSuffixRecords rate source rewards C_star C_h)[k.val]'k.isLt
    r.output.coordinator.failure = none ∧
      r.output.next.coordinator ≠ .first ∧ r.output.next.coordinator ≠ .dagger := by
  obtain ⟨a, q, base, started, _hinstalled, valid, o, serviced, pending, finished, h⟩ :=
    ReferenceCompleteSelectedLiveCoordinatorServiceFinish.complete_selected_live_coordinator_service_finish
      rewards C_star C_h source k v hselected hlive
  dsimp only at h ⊢
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hout, _, _⟩
  rw [record_next_coordinator, hout]
  simp

private theorem first_success
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (completeSuffixRecords rate source rewards C_star C_h).length)
    (hfirst :
      ((completeSuffixRecords rate source rewards C_star C_h)[k.val]'k.isLt).input.state.coordinator =
        .first) :
    let r := (completeSuffixRecords rate source rewards C_star C_h)[k.val]'k.isLt
    r.output.preparation.coordinator.selection ≠ none ∧
      r.output.coordinator.failure = none ∧
      r.output.next.coordinator ≠ .first ∧ r.output.next.coordinator ≠ .dagger := by
  let r := (completeSuffixRecords rate source rewards C_star C_h)[k.val]'k.isLt
  let x := r.input
  let v := ReferenceFirstDispatchMeasurability.firstSelectionAt x
  have hprepare : r.output.preparation = prepare x := by rw [r.output_eq]; rfl
  have hselected : r.output.preparation.coordinator.selection = some v := by
    rw [hprepare]
    exact ReferenceFirstDispatchMeasurability.dispatch_first_selection x hfirst
  have hlive : CoordinatorLocalArmChoice.assignmentIsLive v.view.payload v.view.cutoff
      x.time := by
    change x.time.val + 1 ≤ x.time.val + 1 ∧ x.time.val + 1 < p.T + 1
    exact ⟨le_rfl, Nat.add_lt_add_right x.time.isLt 1⟩
  exact ⟨by rw [hselected]; exact Option.some_ne_none _,
    selected_live_success rewards C_star C_h source k v hselected hlive⟩

private theorem live_success
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (completeSuffixRecords rate source rewards C_star C_h).length)
    (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters registers)
    (base : Fin (p.m - 1) → ℕ)
    (hstate :
      ((completeSuffixRecords rate source rewards C_star C_h)[k.val]'k.isLt).input.state.coordinator =
        .live registers q base) :
    let r := (completeSuffixRecords rate source rewards C_star C_h)[k.val]'k.isLt
    r.output.preparation.coordinator.selection ≠ none ∧
      r.output.coordinator.failure = none ∧
      r.output.next.coordinator ≠ .first ∧ r.output.next.coordinator ≠ .dagger := by
  let r := (completeSuffixRecords rate source rewards C_star C_h)[k.val]'k.isLt
  let x := r.input
  let current := liveInput x registers q base
  have hcontinuing :=
    ReferenceCompleteContinuingLiveCoordinatorStep.complete_live_continuing_coordinator_step
      rewards C_star C_h source k registers q base hstate
  have hcutoff := complete_live_cutoff_post_choice
    rate rewards C_star C_h source k registers q base hstate
  dsimp only at hcontinuing hcutoff
  rcases hcontinuing with ⟨hprepared, hcontinuing⟩
  rcases hcutoff with ⟨_, hcutoff⟩
  have hprepare : r.output.preparation = prepare x := by rw [r.output_eq]; rfl
  cases hc : CoordinatorRoundDispatch.dispatchLive current with
  | continuingChosen dispatched hstart continuation selected =>
      rw [hc] at hcontinuing
      obtain ⟨v, _, _, _, _, _, _, hselected, a, owned, followerBase, started,
        _, _, _, _, valid, o, serviced, pending, finished, h⟩ := hcontinuing
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hout, _, _⟩
      change r.output.preparation.coordinator.selection ≠ none ∧ _
      refine ⟨by rw [hselected]; exact Option.some_ne_none _, ?_⟩
      rw [record_next_coordinator, hout]
      simp
  | cutoffChosen dispatched hstart ledger hinit hledger hvalid hclock hpending
      hassignment selected =>
      rw [hc] at hcutoff
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, physical,
        hselected, _, _, _, _, _, _, _, _, recording, _, startedLedger, h⟩ := hcutoff
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, decoded, bank,
        _, _, _, finishedLedger, finished, diagnostic, hfinished⟩
      rcases hfinished with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        hout, hnext, _⟩
      have hselection : r.output.preparation.coordinator.selection ≠ none := by
        rw [hprepare, hselected]
        exact Option.some_ne_none _
      refine ⟨hselection, ?_⟩
      rw [hout, hnext]
      simp
  | clockFailure failure heq =>
      rw [hc] at hcontinuing
      exact hcontinuing.elim
  | initializerFailure dispatched hstart checked heq =>
      rw [hc] at hcontinuing
      exact hcontinuing.elim
  | localFailure dispatched hstart reason =>
      rw [hc] at hcontinuing
      exact hcontinuing.elim

private theorem empty_corrected_success
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (completeSuffixRecords rate source rewards C_star C_h).length)
    (P : Payload rate) (l : Ledger rate) (saved : Option (Fin p.T × Bool))
    (hstate :
      ((completeSuffixRecords rate source rewards C_star C_h)[k.val]'k.isLt).input.state.coordinator =
        .collection P l saved)
    (hempty : l.pending = ∅)
    (hbefore :
      ((completeSuffixRecords rate source rewards C_star C_h)[k.val]'k.isLt).input.time.val + 1 <
        l.freezeAt) :
    let r := (completeSuffixRecords rate source rewards C_star C_h)[k.val]'k.isLt
    r.output.preparation.coordinator.selection ≠ none ∧
      r.output.coordinator.failure = none ∧
      r.output.next.coordinator ≠ .first ∧ r.output.next.coordinator ≠ .dagger := by
  obtain ⟨u, _hu, core, started, hstart, instruction, hassignment,
    _htime, _hkind, _hsigma, _hcutoff, consistent, output, hlocal, _hlater,
    clockData, installation, selected, _hprior, _hresult, _hpending, _hinstall,
    _hdispatch, _hscore, _hqueue, _hprevious, _hbaseBound, _henvelope, _hpayload,
    _hanchor, _hlawAnchor, _hcutoffRegisters, _hcurrentRegisters, _hsourceScore,
    _hinitialQueue, _hqueues, _hvector, v, _hprepareSelection, hselected,
    _hviewPayload, _hstarted, _hviewCutoff, _harm, _hlive, _hprepared,
    a, owned, followerBase, liveStarted, _ha, _howned, _hbase, _hliveStarted,
    valid, o, serviced, pending, finished, h⟩ :=
    ReferenceCompleteEmptyCorrectedCoordinatorStep.complete_empty_corrected_coordinator_step
      rewards C_star C_h source k P l saved hstate hempty hbefore
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hout, _, _⟩
  dsimp only
  refine ⟨by rw [hselected]; exact Option.some_ne_none _, ?_⟩
  rw [record_next_coordinator, hout]
  simp

private theorem empty_renewal_success
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (completeSuffixRecords rate source rewards C_star C_h).length)
    (P : Payload rate) (l : Ledger rate) (saved : Option (Fin p.T × Bool))
    (hstate :
      ((completeSuffixRecords rate source rewards C_star C_h)[k.val]'k.isLt).input.state.coordinator =
        .collection P l saved)
    (hempty : l.pending = ∅)
    (hafter : l.freezeAt ≤
      ((completeSuffixRecords rate source rewards C_star C_h)[k.val]'k.isLt).input.time.val + 1) :
    let r := (completeSuffixRecords rate source rewards C_star C_h)[k.val]'k.isLt
    r.output.preparation.coordinator.selection ≠ none ∧
      r.output.coordinator.failure = none ∧
      r.output.next.coordinator ≠ .first ∧ r.output.next.coordinator ≠ .dagger := by
  obtain ⟨u, _hu, core, _hscores, started, hstart, instruction, hassignment,
    hinstructionTime, _hrenewal, output, hlocal, _hlater, _hsourceScore,
    _hinitialQueue, _hcurrentWeight, _hanchor, _hqueues, _hdomains, _hbaseBound,
    _hclockFacts, mass, sampled, _hmass, _hsampled, _hvector, selection,
    _hdispatch, _hprepared, physical, _hphysical, _hpayload, _hcutoff, _hlive,
    hselected, a, q, base, liveStarted, _hinstalled,
    valid, o, serviced, pending, finished, h⟩ :=
    ReferenceCompleteEmptyRenewalCoordinatorStep.complete_empty_renewal_coordinator_step
      rate rewards C_star C_h source k P l saved hstate hempty hafter
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hout, _, _⟩
  dsimp only
  refine ⟨by rw [hselected]; exact Option.some_ne_none _, ?_⟩
  rw [record_next_coordinator, hout]
  simp

private theorem nonempty_collection_success
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (completeSuffixRecords rate source rewards C_star C_h).length)
    (P : Payload rate) (l : Ledger rate) (saved : Option (Fin p.T × Bool))
    (hstate :
      ((completeSuffixRecords rate source rewards C_star C_h)[k.val]'k.isLt).input.state.coordinator =
        .collection P l saved)
    (hpending : l.pending.Nonempty) :
    let r := (completeSuffixRecords rate source rewards C_star C_h)[k.val]'k.isLt
    r.output.preparation.coordinator.selection ≠ none ∧
      r.output.coordinator.failure = none ∧
      r.output.next.coordinator ≠ .first ∧ r.output.next.coordinator ≠ .dagger := by
  classical
  let r := (completeSuffixRecords rate source rewards C_star C_h)[k.val]'k.isLt
  let x := r.input
  obtain ⟨u, hu, _⟩ := ReferenceCompleteCollectionDispatchCore.complete_collection_dispatch_core
    rate rewards C_star C_h source k P l saved hstate
  obtain ⟨v, hv, core, scores, started, _hstart, _hframe, choiceInputs,
    snapshot, boundary, hdispatch, _hchoiceInputs, _hclockStarted, _harm,
    c, _hchoice, _hc, _hvalid, _hchoiceArm, o, startedLedger, finished, bank,
    clockFinished, hobserve, _⟩ :=
    ReferenceCompleteContinuingCollectionChoiceDomains.complete_nonempty_continuing_collection_choice_domains
      rate rewards C_star C_h source k P l saved hstate hpending
  have hindex : v = u := Fin.ext (by omega)
  subst v
  let clock := collectionClock P l saved u
  let input := collectionInput x P l clock u
  have hrange : 1 ≤ l.cutoff ∧ l.cutoff ≤ p.T := by
    have := u.isLt
    omega
  let cutoff : Fin p.T := ⟨l.cutoff - 1, by omega⟩
  have hcutoff : cutoff = u := by apply Fin.ext; dsimp only [cutoff]; omega
  have hstate' : x.state.coordinator = .collection P l saved := hstate
  have hprepared : (prepare x).coordinator =
      .collection P l clock u (.continuing core snapshot boundary scores) := by
    simp only [prepare, dispatch, hstate', dite_eq_left hrange,
      CoordinatorRoundDispatch.dispatch]
    change DispatchCut.collection P l (collectionClock P l saved cutoff) cutoff
      (CoordinatorRoundDispatch.dispatchCollection
        (collectionInput x P l (collectionClock P l saved cutoff) cutoff)) = _
    rw [hcutoff]
    exact congrArg (DispatchCut.collection P l clock u) hdispatch
  have hprepare : r.output.preparation = prepare x := by rw [r.output_eq]; rfl
  have hselection : r.output.preparation.coordinator.selection ≠ none := by
    rw [hprepare, hprepared]
    simp only [DispatchCut.selection]
    exact Option.some_ne_none _
  have hout : r.output.coordinator = (prepare x).observeCoordinator := by
    rw [r.output_eq]
    rfl
  dsimp only
  refine ⟨hselection, ?_⟩
  rw [record_next_coordinator, hout, hobserve]
  simp

private theorem complete_step
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (completeSuffixRecords rate source rewards C_star C_h).length)
    (hincoming :
      ((completeSuffixRecords rate source rewards C_star C_h)[k.val]'k.isLt).input.state.coordinator ≠
        .dagger) :
    let r := (completeSuffixRecords rate source rewards C_star C_h)[k.val]'k.isLt
    r.output.preparation.coordinator.selection ≠ none ∧
      r.output.coordinator.failure = none ∧
      r.output.next.coordinator ≠ .first ∧ r.output.next.coordinator ≠ .dagger := by
  classical
  let r := (completeSuffixRecords rate source rewards C_star C_h)[k.val]'k.isLt
  cases hstate : r.input.state.coordinator with
  | first => exact first_success rewards C_star C_h source k hstate
  | live registers q base =>
      exact live_success rewards C_star C_h source k registers q base hstate
  | collection P l saved =>
      by_cases hempty : l.pending = ∅
      · by_cases hbefore : r.input.time.val + 1 < l.freezeAt
        · exact empty_corrected_success rewards C_star C_h source k P l saved
            hstate hempty hbefore
        · exact empty_renewal_success rewards C_star C_h source k P l saved
            hstate hempty (Nat.le_of_not_gt hbefore)
      · exact nonempty_collection_success rewards C_star C_h source k P l saved
          hstate (Finset.nonempty_iff_ne_empty.mpr hempty)
  | dagger => exact (hincoming hstate).elim

/-- Every actual complete-suffix coordinator phase has a selection and finishes
without a coordinator failure, reaching neither FIRST nor dagger. The actual
terminal coordinator is also non-dagger, including a launch at the horizon
with an empty suffix. No source-validity or reachability premise is supplied.
-/
theorem complete_coordinator_phase_exhaustion
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h
    (∀ k : Fin R.length, let r := R[k.val]'k.isLt
      r.input.state.coordinator ≠ .dagger ∧
      r.output.preparation.coordinator.selection ≠ none ∧
      r.output.coordinator.failure = none ∧
      r.output.next.coordinator ≠ .first ∧
      r.output.next.coordinator ≠ .dagger) ∧
    (∀ terminal : ReferenceActivePhysicalStep.State p rate,
      ReferenceCompletePhysicalHistory.completeTerminalState
        rate source rewards C_star C_h = some terminal →
      terminal.coordinator ≠ .dagger) := by
  classical
  let R := completeSuffixRecords rate source rewards C_star C_h
  -- The induction retains membership in the original source list. Each local
  -- theorem is therefore applied at an original index, never a replacement run.
  have chain : ∀ (records : List (RoundRecord p rate))
      (initial terminal : ReferenceActivePhysicalStep.State p rate), Connected initial records terminal →
      (∀ r ∈ records, r ∈ R) → initial.coordinator ≠ .dagger →
      (∀ r ∈ records, r.input.state.coordinator ≠ .dagger ∧
        r.output.preparation.coordinator.selection ≠ none ∧
        r.output.coordinator.failure = none ∧
        r.output.next.coordinator ≠ .first ∧ r.output.next.coordinator ≠ .dagger) ∧
      terminal.coordinator ≠ .dagger := by
    intro records
    induction records with
    | nil =>
        intro initial terminal hchain _ hinitial
        change terminal = initial at hchain
        subst terminal
        exact ⟨by simp, hinitial⟩
    | cons r rest ih =>
        intro initial terminal hchain hmem hinitial
        rcases hchain with ⟨hpre, hrest⟩
        have hin : r.input.state.coordinator ≠ .dagger := by
          rw [hpre]
          exact hinitial
        obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp (hmem r (by simp))
        let k : Fin R.length := ⟨i, hi⟩
        have hstep : r.output.preparation.coordinator.selection ≠ none ∧
            r.output.coordinator.failure = none ∧
            r.output.next.coordinator ≠ .first ∧ r.output.next.coordinator ≠ .dagger := by
          have hindexed : (R[k.val]'k.isLt).input.state.coordinator ≠ .dagger := by
            simpa only [k, heq] using hin
          rw [← heq]
          exact complete_step rewards C_star C_h source k hindexed
        obtain ⟨hrecords, hterminal⟩ := ih r.output.next terminal hrest
          (fun s hs => hmem s (List.mem_cons_of_mem r hs)) hstep.2.2.2
        refine ⟨?_, hterminal⟩
        intro s hs
        rcases List.mem_cons.mp hs with heq | hs
        · subst s
          exact ⟨hin, hstep⟩
        · exact hrecords s hs
  cases hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h with
  | none =>
      obtain ⟨_, hrecords, hterminal, _⟩ := no_launch_complete_history
        rate source rewards C_star C_h hlaunch
      constructor
      · intro k
        have hlength : (completeSuffixRecords rate source rewards C_star C_h).length = 0 :=
          congrArg List.length hrecords
        have hk := k.isLt
        omega
      · intro terminal hsome
        rw [hterminal] at hsome
        cases hsome
  | some active =>
      have hsome : (ReferenceCorrectedInitializationLaunch.correctedLaunch
          rate source rewards C_star C_h).isSome = true := by rw [hlaunch]; rfl
      have hcross := (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
        rate source rewards C_star C_h).mp hsome
      obtain ⟨launched, hlaunched, hfirst, _⟩ :=
        ReferenceCorrectedInitializationLaunch.correctedLaunch_coordinator_provenance
          rate source rewards C_star C_h hcross
      have heq : launched = active := Option.some.inj (hlaunched.symm.trans hlaunch)
      subst launched
      have hinitial : active.coordinator ≠ .dagger := by rw [hfirst]; simp
      have hconnected := completeSuffix_connected_on_launch
        rate source rewards C_star C_h active hlaunch
      obtain ⟨hrecords, hterminal⟩ := chain R active _ hconnected
        (fun _ h => h) hinitial
      constructor
      · intro k
        exact hrecords (R[k.val]'k.isLt) (List.getElem_mem k.isLt)
      · intro terminal hsome
        rw [completeTerminalState_on_launch rate source rewards C_star C_h active hlaunch]
          at hsome
        have heq := Option.some.inj hsome
        rw [← heq]
        exact hterminal

end Bandits.Support.ReferenceCompleteCoordinatorPhaseExhaustion
