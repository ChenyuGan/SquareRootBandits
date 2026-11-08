/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCoordinatorUpWindowCompletedCut
public import Bandits.Support.ReferenceAcceptedUpFollowerHistory
public import Bandits.Support.ReferenceUpPhysicalHashRule
public import Bandits.Support.ReferenceAssignmentPayloadPersistence

/-!
# Adjacent cutoff UP offer seed

Sources: `sources/zip4/manuscript/05_binary_transport.tex:36-53,70-124`,
`sources/zip4/manuscript/06_interruptions.tex:9-70,164-177,192-209,277-284,327-348`,
and `sources/zip4/manuscript/appendix_a_local_protocol.tex:92-109,151-157`.

This module is restricted to the actual local branch immediately after a
retained, accepted DOWN at a source cutoff. It preserves the original run,
whole rows and reward table, private arrays, complete payload, decoder banks,
and the physical receiver diagnostic. It does not assert eventual delivery,
numeric source truth, a positive observation, or manuscript closure.

-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions

namespace Bandits.Support.ReferenceCutoffUpOfferConstruction

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev State := ReferenceActivePhysicalStep.State
abbrev Record (p : Parameters) (rate : RateInput p) :=
  ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)

variable {p : Parameters} {rate : RateInput p}

private theorem connected_adjacent
    {initial final : State p rate}
    {records : List (Record (p := p) (rate := rate))}
    (hchain : ReferenceActivePhysicalHorizon.Connected initial records final)
    (k : Fin records.length) (hk : k.val + 1 < records.length) :
    (records[k.val]'k.isLt).output.next = (records[k.val + 1]'hk).input.state := by
  have hdrop := ReferenceFollowerReplyChronology.connected_drop_from_output
    hchain k.val k.isLt
  have hsplit : records.drop (k.val + 1) =
      records[k.val + 1]'hk :: records.drop (k.val + 2) := List.drop_eq_getElem_cons hk
  rw [hsplit] at hdrop
  exact hdrop.1.symm

private theorem retainedDown_output_lastDown
    (record : Record (p := p) (rate := rate)) (i : Fin (p.m - 1))
    (target : ReferenceAcceptedUpFollowerHistory.DownRecord (p := p) (rate := rate))
    (next : ReferencePrelaunchFollower.State p rate.eta)
    (nextMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hout : record.output.next.followers i = .ordinary next nextMemory)
    (hretained : ReferenceAcceptedUpFollowerHistory.RetainedDown record i target) :
    next.lastDown = some target := by
  rcases record with ⟨input, output, output_eq⟩
  cases output_eq
  let prepared := ReferenceActivePhysicalStep.prepare input
  let sender := prepared.followers.followers i
  let view := prepared.coordinator.downView
  let observation := prepared.feedback.observations
    (PublicDiscreteDraws.followerPlayer p.two_le_m i)
  have houtFinish :
      (ReferenceActivePhysicalStep.finishFollower view sender observation).configuration =
        .ordinary next nextMemory := by
    simpa only [ReferenceActivePhysicalStep.step,
      ReferenceActivePhysicalStep.PreparedRound.observeFollower,
      prepared, sender, view, observation] using hout
  obtain ⟨choice, memory, post, hchoice, hrecord, hfinish,
    hfinishDownInput, hfinishDown⟩ :=
    ReferenceFollowerReplyChronology.finishFollower_ordinary_inversion
      view sender observation next nextMemory houtFinish
  rcases hretained with ⟨logged, cut, after, raw, scan, registers, lastService,
    hretainedInput, hretainedDown, hretainedOutcome⟩
  have halignment := prepared.follower_alignment i
  have hfinishRetainedInput :
      (ReferenceActivePhysicalStep.finishFollower view sender observation).downInput =
        some logged := by
    simpa only [ReferenceActivePhysicalStep.step,
      ReferenceActivePhysicalStep.PreparedRound.observeFollower,
      prepared, sender, view, observation, halignment.1, halignment.2.1] using
        hretainedInput
  have hfinishRetainedDown :
      (ReferenceActivePhysicalStep.finishFollower view sender observation).down =
        some cut := by
    simpa only [ReferenceActivePhysicalStep.step,
      ReferenceActivePhysicalStep.PreparedRound.observeFollower,
      prepared, sender, view, observation, halignment.1, halignment.2.1] using
        hretainedDown
  have hrecordInput :
      (ReferenceActivePhysicalStep.recordFollower view sender.follower sender.row
        sender.activation sender.time sender.active sender.arm observation choice).downInput =
          some logged := hfinishDownInput.symm.trans hfinishRetainedInput
  have hrecordDown :
      (ReferenceActivePhysicalStep.recordFollower view sender.follower sender.row
        sender.activation sender.time sender.active sender.arm observation choice).down =
          some cut := hfinishDown.symm.trans hfinishRetainedDown
  have hchoiceUnoccupied : choice.status = .unoccupied := by
    classical
    by_contra hstatus
    simp [ReferenceActivePhysicalStep.recordFollower, hstatus] at hrecordInput
  have hlogging : ActiveFollowerLogging.checkedLogging sender.follower sender.row
      sender.activation sender.time (sender.arm, observation) choice = .ok logged := by
    classical
    unfold ReferenceActivePhysicalStep.recordFollower at hrecordInput
    simp only [dite_eq_left hchoiceUnoccupied] at hrecordInput
    cases hlog : ActiveFollowerLogging.checkedLogging sender.follower sender.row
        sender.activation sender.time (sender.arm, observation) choice with
    | error reason => simp [hlog] at hrecordInput
    | ok actual =>
        have heq : actual = logged := by simpa [hlog] using hrecordInput
        simp [heq]
  have hcut : cut = ReferenceDownReception.referenceDownCut p view
      sender.follower sender.row sender.time observation rate logged := by
    classical
    unfold ReferenceActivePhysicalStep.recordFollower at hrecordDown
    simp only [dite_eq_left hchoiceUnoccupied, hlogging] at hrecordDown
    exact Option.some.inj hrecordDown.symm
  have hpostAfter : post = after := by
    have hresult : DeclaredFollowerLocalRound.consumeDownResult rate cut.outcome =
        .ok post := by
      classical
      unfold ReferenceActivePhysicalStep.recordFollower at hrecord
      simp only [dite_eq_left hchoiceUnoccupied, hlogging] at hrecord
      rw [← hcut] at hrecord
      exact hrecord
    rw [hretainedOutcome] at hresult
    simp only [DeclaredFollowerLocalRound.consumeDownResult, Except.ok.injEq] at hresult
    exact hresult.symm
  have haccepted := ReferenceFollowerReplyChronology.referenceDownCut_accepted
    view sender.follower sender.row sender.time observation logged after raw target
    scan registers lastService (by rw [← hcut]; exact hretainedOutcome)
  have hnextPost := ReferenceFollowerReplyChronology.releaseAndFinish_frame
    sender.follower sender.row sender.time observation choice post next memory nextMemory hfinish
  have hlast : next.lastDown = post.lastDown := by
    have h := congrArg Prod.fst hnextPost.1
    change next.lastDown = post.lastDown at h
    exact h
  rw [hpostAfter] at hlast
  exact hlast.trans haccepted.2

private theorem adjacent_local_states
    (prev current : Record (p := p) (rate := rate))
    (i : Fin (p.m - 1))
    (target : ReferenceAcceptedUpFollowerHistory.DownRecord (p := p) (rate := rate))
    (next : ReferencePrelaunchFollower.State p rate.eta)
    (nextMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hadjacent : prev.output.next = current.input.state)
    (hretained : ReferenceAcceptedUpFollowerHistory.RetainedDown prev i target)
    (hout : current.output.next.followers i = .ordinary next nextMemory) :
    ∃ state memory choice choiceMemory,
      current.input.state.followers i = .ordinary state memory ∧
      (ReferenceFollowerFixedReply.actualChoice current i).configuration =
        .ordinary choice choiceMemory ∧
      ActiveFollowerLifecycle.startRound rate.eta current.input.time state memory =
        .ok (choice, choiceMemory) ∧
      state.lastDown = some target := by
  obtain ⟨choice, choiceMemory, hchoice, _, _, _⟩ :=
    ReferenceFollowerReplyChronology.record_choice_chronology
      current i next nextMemory hout
  have hactual : ReferenceFollowerFixedReply.actualChoice current i =
      DeclaredFollowerLocalRound.prepare rate i current.input.row
        (current.input.state.activations i) current.input.time
        (current.input.active i) (current.input.state.followers i) :=
    current.output.preparation.followers.followers_eq i
  have hchoiceActual := hchoice
  rw [hactual] at hchoice
  obtain ⟨state, memory, hinput, hstart, _, _⟩ :=
    ReferenceFollowerReplyChronology.prepare_ordinary_inversion
      i current.input.row (current.input.state.activations i) current.input.time
      (current.input.active i) (current.input.state.followers i) choice choiceMemory hchoice
  have hprevOutput : prev.output.next.followers i = .ordinary state memory := by
    calc
      prev.output.next.followers i = current.input.state.followers i :=
        congrArg (fun successor : State p rate => successor.followers i) hadjacent
      _ = .ordinary state memory := hinput
  have hlast := retainedDown_output_lastDown prev i target state memory
    hprevOutput hretained
  exact ⟨state, memory, choice, choiceMemory, hinput, hchoiceActual, hstart, hlast⟩

private theorem cutoff_decision_fields
    (p : Parameters) (sigma : Fin p.T) (g : ℕ)
    (lastProposal : Option (Fin p.T × Bool)) (t : Fin p.T)
    (h : CoordinatorPhaseClock.detectCutoff
      { sigma := some sigma, u := none, g := g, lastProposal := lastProposal } t =
      .ok (.cutoff sigma rfl)) :
    FollowerCutoffScan.calendarRound t = g ∨
      ∃ stamp, lastProposal = some (stamp, true) ∧ stamp.val + 1 = t.val := by
  by_cases hgrid : FollowerCutoffScan.calendarRound t = g
  · exact Or.inl hgrid
  · right
    cases lastProposal with
    | none =>
        simp [CoordinatorPhaseClock.detectCutoff,
          CoordinatorPhaseClock.savedPriorProposal, hgrid] at h
        cases h
    | some token =>
        rcases token with ⟨stamp, bit⟩
        by_cases hstamp : stamp.val + 1 = t.val
        · have hbit : bit = true := by
            cases bit with
            | false =>
                simp [CoordinatorPhaseClock.detectCutoff,
                  CoordinatorPhaseClock.savedPriorProposal, hgrid, hstamp] at h
                cases h
            | true => rfl
          exact ⟨stamp, by simp [hbit], hstamp⟩
        · simp [CoordinatorPhaseClock.detectCutoff,
            CoordinatorPhaseClock.savedPriorProposal, hgrid, hstamp] at h
          cases h

private theorem detectCutoff_cutoff_inputs
    (p : Parameters) (clock : CoordinatorPhaseClock.ClockRegisters p)
    (sigma t : Fin p.T) (hsigma : clock.sigma = some sigma)
    (hcutoff : CoordinatorPhaseClock.detectCutoff clock t =
      .ok (.cutoff sigma hsigma)) :
    clock.u = none ∧
      (FollowerCutoffScan.calendarRound t = clock.g ∨
        ∃ stamp, clock.lastProposal = some (stamp, true) ∧
          stamp.val + 1 = t.val) := by
  have hu : clock.u = none := by
    cases he : clock.u with
    | none => rfl
    | some u =>
        rw [CoordinatorPhaseClock.detectCutoff_collection_noRead clock t u he] at hcutoff
        cases hcutoff
  refine ⟨hu, ?_⟩
  rcases clock with ⟨sigmaOpt, uOpt, g, lastProposal⟩
  change sigmaOpt = some sigma at hsigma
  change uOpt = none at hu
  subst sigmaOpt uOpt
  exact cutoff_decision_fields p sigma g lastProposal t hcutoff

private theorem startRound_initializeAt_cutoff_inputs
    (p : Parameters) (eta : ℝ) (clock : CoordinatorPhaseClock.ClockRegisters p)
    (pending : Finset (Fin (p.m - 1))) (t : Fin p.T)
    (result : CoordinatorPhaseClock.StartRoundResult p)
    (hstart : CoordinatorPhaseClock.startRound p eta t clock pending = .ok result)
    (hcommand : result.ledgerCommand = some (.initializeAt t)) :
    ∃ sigma : Fin p.T, clock.sigma = some sigma ∧ clock.u = none ∧
      (FollowerCutoffScan.calendarRound t = clock.g ∨
        ∃ stamp bit, clock.lastProposal = some (stamp, bit) ∧
          stamp.val + 1 = t.val ∧ bit = true) := by
  classical
  by_cases hp : CoordinatorPhaseClock.proposalParameterValid p eta
  · by_cases hc : CoordinatorPhaseClock.clockRegistersValid p eta clock
    · by_cases ht : CoordinatorPhaseClock.startRoundTimeValid p t clock
      · cases hd : CoordinatorPhaseClock.detectCutoff clock t with
        | error failure =>
            simp [CoordinatorPhaseClock.startRound, hp, hc, ht, hd] at hstart
        | ok decision =>
            cases decision with
            | cutoff sigma hsigma =>
                obtain ⟨hu, hfields⟩ := detectCutoff_cutoff_inputs
                  p clock sigma t hsigma hd
                refine ⟨sigma, hsigma, hu, ?_⟩
                rcases hfields with hgrid | ⟨stamp, htoken, hstamp⟩
                · exact Or.inl hgrid
                · exact Or.inr ⟨stamp, true, htoken, hstamp, rfl⟩
            | noCutoff =>
                by_cases hsource : CoordinatorPhaseClock.sourceStartTest
                    clock.sigma clock.u t pending
                · by_cases hgrid : CoordinatorPhaseClock.newGridBoundaryValid p t
                      (FollowerCutoffScan.gridBoundary p eta t)
                  · simp only [CoordinatorPhaseClock.startRound, hp, hc, ht, hd,
                      hsource, hgrid] at hstart
                    have hEq := Except.ok.inj hstart
                    cases hEq
                    cases hcommand
                  · simp [CoordinatorPhaseClock.startRound, hp, hc, ht, hd,
                      hsource, hgrid] at hstart
                · simp only [CoordinatorPhaseClock.startRound, hp, hc, ht, hd,
                    hsource] at hstart
                  have hEq := Except.ok.inj hstart
                  cases hEq
                  cases hcommand
      · simp [CoordinatorPhaseClock.startRound, hp, hc, ht] at hstart
    · simp [CoordinatorPhaseClock.startRound, hp, hc] at hstart
  · simp [CoordinatorPhaseClock.startRound, hp] at hstart

private theorem dispatch_live_origin
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
    (base : Fin (p.m - 1) → ℕ)
    (outcome : CoordinatorRoundDispatch.LiveOutcome
      (ReferenceActivePhysicalStep.liveInput x registers owned base))
    (hdispatch : ReferenceActivePhysicalStep.dispatch x =
      .live registers owned base outcome) :
    x.state.coordinator = .live registers owned base := by
  classical
  cases hstate : x.state.coordinator with
  | first =>
      rw [ReferenceActivePhysicalStep.dispatch_first x hstate] at hdispatch
      cases hdispatch
  | live actualRegisters actualOwned actualBase =>
      simp only [ReferenceActivePhysicalStep.dispatch, hstate,
        CoordinatorRoundDispatch.dispatch] at hdispatch
      have hfields := ReferenceActivePhysicalStep.DispatchCut.live.inj hdispatch
      cases hfields.1
      cases hfields.2.1
      cases hfields.2.2.1
      rfl
  | collection payload ledger proposal =>
      by_cases hvalid : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
      · let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
        let clock := ReferenceActivePhysicalStep.collectionClock payload ledger proposal cutoff
        let input := ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff
        cases houter : CoordinatorRoundDispatch.dispatch (.collection input) with
        | collection result =>
          have hcollection : ReferenceActivePhysicalStep.dispatch x =
              .collection payload ledger clock cutoff result := by
            simp [ReferenceActivePhysicalStep.dispatch, hstate, hvalid,
              cutoff, clock, input, houter]
            rfl
          have hfalse : False := by
            have hcontra := hcollection.symm.trans hdispatch
            cases hcontra
          exact hfalse.elim
      · have hinvalid : ReferenceActivePhysicalStep.dispatch x =
            .invalidCollectionCutoff := by
          simp [ReferenceActivePhysicalStep.dispatch, hstate, hvalid]
        have hfalse : False := by
          have hcontra := hinvalid.symm.trans hdispatch
          cases hcontra
        exact hfalse.elim
  | dagger =>
      rw [ReferenceActivePhysicalStep.dispatch_dagger x hstate] at hdispatch
      cases hdispatch

private theorem cutoff_input_live
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (hcutoff : ReferenceCollectionPhaseHistory.cutoffChosen x = true) :
    ∃ (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
      (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
      (base : Fin (p.m - 1) → ℕ),
      x.state.coordinator = .live registers owned base := by
  classical
  unfold ReferenceCollectionPhaseHistory.cutoffChosen at hcutoff
  rw [(ReferenceActivePhysicalStep.prepare x).coordinator_eq] at hcutoff
  cases hdispatch : ReferenceActivePhysicalStep.dispatch x with
  | first outcome => simp [hdispatch] at hcutoff
  | live registers owned base outcome =>
      exact ⟨registers, owned, base,
        dispatch_live_origin x registers owned base outcome hdispatch⟩
  | collection payload ledger clock cutoff outcome => simp [hdispatch] at hcutoff
  | invalidCollectionCutoff => simp [hdispatch] at hcutoff
  | dagger => simp [hdispatch] at hcutoff

private theorem finishRound_proposal_read_of_success
    (t : Fin p.T) (row : CompletePublicTable.CompleteRow p)
    (state state' : ReferencePrelaunchFollower.State p rate.eta)
    (memory memory' : ActiveFollowerLifecycle.LocalMemory p)
    (hfinish : ActiveFollowerLifecycle.finishRound rate.eta t row state memory =
      .ok (state', memory'))
    (hoccupied : state'.status ≠ .unoccupied) :
    ∃ M, state.lastDown = some M ∧ M.val.sigma ≤ t.val + 1 ∧
      memory'.lastProposalRead = some ⟨t,
        FollowerCutoffScan.completeRowProposalBit p rate.eta.val row t⟩ := by
  have hstate := ActiveFollowerLifecycle.finishRound_frame rate.eta t row
    state state' memory memory' hfinish
  subst state'
  by_cases hregs : ActiveFollowerLifecycle.localStateDomainValid state
  · by_cases hunoccupied : state.status = .unoccupied
    · simp [ActiveFollowerLifecycle.finishRound, hregs, hunoccupied] at hfinish
      exact (hoccupied hunoccupied).elim
    · cases hrecord : state.lastDown with
      | none =>
          simp [ActiveFollowerLifecycle.finishRound, hregs, hunoccupied,
            hrecord] at hfinish
      | some M =>
          by_cases htime : M.val.sigma ≤ t.val + 1
          · have hmemory :
                (⟨some ⟨t,
                  FollowerCutoffScan.completeRowProposalBit p rate.eta.val row t⟩⟩ :
                  ActiveFollowerLifecycle.LocalMemory p) = memory' := by
              simpa [ActiveFollowerLifecycle.finishRound, hregs, hunoccupied,
                hrecord, htime] using hfinish
            exact ⟨M, rfl, htime,
              congrArg ActiveFollowerLifecycle.LocalMemory.lastProposalRead hmemory |>.symm⟩
          · simp [ActiveFollowerLifecycle.finishRound, hregs, hunoccupied,
              hrecord, htime] at hfinish
  · simp [ActiveFollowerLifecycle.finishRound, hregs] at hfinish

private theorem releaseAndFinish_proposal_read_of_occupied_output
    (i : Fin (p.m - 1)) (t : Fin p.T)
    (row : CompletePublicTable.CompleteRow p)
    (observation : ReferencePrelaunchFollower.Observation p)
    (choice post next : ReferencePrelaunchFollower.State p rate.eta)
    (memory nextMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hfinish : DeclaredFollowerLocalRound.releaseAndFinish rate i row t
      observation choice memory post = .ok (next, nextMemory))
    (hoccupied : next.status ≠ .unoccupied) :
    nextMemory.lastProposalRead = some ⟨t,
      FollowerCutoffScan.completeRowProposalBit p rate.eta.val row t⟩ := by
  unfold DeclaredFollowerLocalRound.releaseAndFinish at hfinish
  cases hrelease : ActiveFollowerLifecycle.releaseAfterService rate.eta i t
      (ActiveFollowerLifecycle.publicRowOfCompleteRow row t) observation choice post with
  | error failure => simp [hrelease] at hfinish
  | ok released =>
      cases hround : ActiveFollowerLifecycle.finishRound rate.eta t row released memory with
      | error failure => simp [hrelease, hround] at hfinish
      | ok result =>
          have hresult : result = (next, nextMemory) := by
            simpa [hrelease, hround] using hfinish
          cases hresult
          obtain ⟨_, _, _, hread⟩ := finishRound_proposal_read_of_success
            t row released next memory nextMemory hround hoccupied
          exact hread

private theorem coordinator_finish_savedProposal_of_none_output
    (t : Fin p.T) (clock : CoordinatorPhaseClock.ClockRegisters p)
    (pending : Finset (Fin (p.m - 1)))
    (row : CompletePublicTable.CompleteRow p)
    (result : CoordinatorPhaseClock.FinishRoundResult p)
    (hfinish : CoordinatorPhaseClock.finishRound p rate.eta.val t clock pending row =
      .ok result)
    (hnone : result.clock.u = none) :
    result.clock.lastProposal = some
      (t, FollowerCutoffScan.completeRowProposalBit p rate.eta.val row t) := by
  classical
  by_cases hclock : CoordinatorPhaseClock.clockRegistersValid p rate.eta.val clock
  · by_cases htime : CoordinatorPhaseClock.finishRoundTimeValid t clock
    · cases hsigma : clock.sigma with
      | none =>
          simp [CoordinatorPhaseClock.finishRound, hclock,
            htime, hsigma] at hfinish
      | some sigma =>
          cases hu : clock.u with
          | some u =>
              let expected : CoordinatorPhaseClock.FinishRoundResult p := {
                clock := clock
                pending := pending
                ledgerCommand := some (.accumulateLocalServiceAt t) }
              have hsuccess : CoordinatorPhaseClock.finishRound p rate.eta.val t
                  clock pending row = .ok expected := by
                simp [CoordinatorPhaseClock.finishRound, hclock, htime,
                  hsigma, hu, expected]
                rfl
              have hresult := congrArg CoordinatorPhaseClock.FinishRoundResult.clock
                (Except.ok.inj (hsuccess.symm.trans hfinish))
              have hcontr : result.clock.u = some u := by
                simpa [expected, hu] using congrArg CoordinatorPhaseClock.ClockRegisters.u
                  hresult.symm
              rw [hnone] at hcontr
              cases hcontr
          | none =>
              by_cases hparam : CoordinatorPhaseClock.proposalParameterValid p rate.eta.val
              · let expected : CoordinatorPhaseClock.FinishRoundResult p := {
                  clock := ⟨clock.sigma, clock.u, clock.g,
                    some (t, FollowerCutoffScan.completeRowProposalBit p rate.eta.val row t)⟩
                  pending := pending
                  ledgerCommand := none }
                have hsuccess : CoordinatorPhaseClock.finishRound p rate.eta.val t
                    clock pending row = .ok expected := by
                  simp [CoordinatorPhaseClock.finishRound, hclock, htime,
                    hsigma, hu, hparam, expected]
                  rfl
                have hresult := congrArg CoordinatorPhaseClock.FinishRoundResult.clock
                  (Except.ok.inj (hsuccess.symm.trans hfinish))
                have hproposal : result.clock.lastProposal = some
                    (t, FollowerCutoffScan.completeRowProposalBit p rate.eta.val row t) := by
                  simpa [expected] using congrArg
                    CoordinatorPhaseClock.ClockRegisters.lastProposal hresult.symm
                exact hproposal
              · simp [CoordinatorPhaseClock.finishRound, hclock, htime,
                  hsigma, hu, hparam] at hfinish
    · simp [CoordinatorPhaseClock.finishRound, hclock, htime] at hfinish
      cases hfinish
  · simp [CoordinatorPhaseClock.finishRound, hclock] at hfinish
    cases hfinish

private theorem livePostChoice_savedProposal
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (nextRegisters : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (nextOwned : CoordinatorLiveServiceFinish.OwnedRegisters nextRegisters)
    (nextBase : Fin (p.m - 1) → ℕ)
    (houtput : (ReferenceActivePhysicalStep.livePostChoice prepared r q base started).configuration =
      .live nextRegisters nextOwned nextBase)
    (hnone : nextRegisters.priorClock.u = none) :
    nextRegisters.priorClock.lastProposal = some
      (x.time, FollowerCutoffScan.completeRowProposalBit p rate.eta.val x.row x.time) := by
  classical
  unfold ReferenceActivePhysicalStep.livePostChoice at houtput
  cases hrecord : CoordinatorRecorderComplementBridge.run
      (ReferenceActivePhysicalStep.liveRecordingInput prepared r started) with
  | none => simp [hrecord, ReferenceActivePhysicalStep.coordinatorFailure] at houtput
  | some recording =>
      cases hservice : CoordinatorLiveServiceFinish.servicePass r q recording with
      | error failure =>
          simp [hrecord, hservice, ReferenceActivePhysicalStep.coordinatorFailure] at houtput
      | ok serviced =>
          cases hconfirmation : CoordinatorLocalArmChoice.confirmationUpdate r.payload
              started.pending
              (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
              x.time x.row prepared.coordinatorObservation with
          | none =>
              simp [hrecord, hservice, hconfirmation,
                ReferenceActivePhysicalStep.coordinatorFailure] at houtput
          | some pending =>
              cases hfinish : CoordinatorPhaseClock.finishRound p rate.eta.val x.time
                  started.clock pending x.row with
              | error failure =>
                  simp [hrecord, hservice, hconfirmation, hfinish,
                    ReferenceActivePhysicalStep.coordinatorFailure] at houtput
              | ok finished =>
                  let constructed :
                      CoordinatorLiveChoiceRecorderStep.Registers p rate.eta := {
                    payload := r.payload
                    priorClock := finished.clock
                    pendingAtChoice := finished.pending
                    time := x.time
                    gridBoundary := finished.clock.g
                    complementScores := serviced.score }
                  have hregisters :
                      constructed = nextRegisters := by
                    have hcfg' :
                        (ReferenceActivePhysicalStep.CoordinatorConfiguration.live constructed
                          { queue := serviced.queue
                            previousService := serviced.previousService } base) =
                            ReferenceActivePhysicalStep.CoordinatorConfiguration.live
                              nextRegisters nextOwned nextBase := by
                      simpa [hrecord, hservice, hconfirmation, hfinish] using houtput
                    exact (ReferenceActivePhysicalStep.CoordinatorConfiguration.live.inj
                      hcfg').1
                  have hfinishedNone : finished.clock.u = none := by
                    have hprior := congrArg
                      CoordinatorLiveChoiceRecorderStep.Registers.priorClock hregisters
                    rw [← hprior] at hnone
                    exact hnone
                  have hproposal := coordinator_finish_savedProposal_of_none_output
                    x.time started.clock pending x.row finished hfinish hfinishedNone
                  have hprior := congrArg
                    CoordinatorLiveChoiceRecorderStep.Registers.priorClock hregisters
                  have hlast := congrArg CoordinatorPhaseClock.ClockRegisters.lastProposal hprior
                  exact hlast.symm.trans hproposal

private theorem record_live_savedProposal
    (record : Record (p := p) (rate := rate))
    (nextRegisters : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (nextOwned : CoordinatorLiveServiceFinish.OwnedRegisters nextRegisters)
    (nextBase : Fin (p.m - 1) → ℕ)
    (houtput : record.output.next.coordinator =
      .live nextRegisters nextOwned nextBase)
    (hnone : nextRegisters.priorClock.u = none) :
    nextRegisters.priorClock.lastProposal = some
      (record.input.time, FollowerCutoffScan.completeRowProposalBit p rate.eta.val
        record.input.row record.input.time) := by
  have hstep : (ReferenceActivePhysicalStep.step record.input).next.coordinator =
      .live nextRegisters nextOwned nextBase := by
    simpa [record.output_eq] using houtput
  have hobs :
      (ReferenceActivePhysicalStep.prepare record.input).observeCoordinator.configuration =
        .live nextRegisters nextOwned nextBase :=
    (ReferenceActivePhysicalStep.step_next_fields record.input).1.symm.trans hstep
  let prepared := ReferenceActivePhysicalStep.prepare record.input
  cases hprep : prepared.coordinator with
  | first outcome =>
      have heq := ReferenceActivePhysicalStep.observeCoordinator_first_equation
        prepared outcome hprep
      rw [heq] at hobs
      cases outcome with
      | chosen installed selection =>
          by_cases hsel : (ReferenceActivePhysicalStep.DispatchCut.first
              (.chosen installed selection)).selection = none
          · simp [hsel, ReferenceActivePhysicalStep.coordinatorFailure] at hobs
          · have hlive :
                (ReferenceActivePhysicalStep.livePostChoice prepared installed.registers
                  installed.ownedRegisters installed.followerBaseScore
                  installed.startRoundResult).configuration =
                    .live nextRegisters nextOwned nextBase := by
              simpa [hsel] using hobs
            exact livePostChoice_savedProposal prepared installed.registers
              installed.ownedRegisters installed.followerBaseScore
              installed.startRoundResult nextRegisters nextOwned nextBase hlive hnone
      | choiceDomainFailure installation =>
          cases hsel : (ReferenceActivePhysicalStep.DispatchCut.first
              (.choiceDomainFailure installation)).selection <;>
            simp [hsel, ReferenceActivePhysicalStep.coordinatorFailure] at hobs
      | recorderBoundaryFailure installation =>
          cases hsel : (ReferenceActivePhysicalStep.DispatchCut.first
              (.recorderBoundaryFailure installation)).selection <;>
            simp [hsel, ReferenceActivePhysicalStep.coordinatorFailure] at hobs
      | choiceRejected installation =>
          cases hsel : (ReferenceActivePhysicalStep.DispatchCut.first
              (.choiceRejected installation)).selection <;>
            simp [hsel, ReferenceActivePhysicalStep.coordinatorFailure] at hobs
  | live registers owned base outcome =>
      have heq := ReferenceActivePhysicalStep.observeCoordinator_live_equation
        prepared registers owned base outcome hprep
      rw [heq] at hobs
      cases outcome with
      | clockFailure failure dispatchEq =>
          cases hsel : (ReferenceActivePhysicalStep.DispatchCut.live
              registers owned base (.clockFailure failure dispatchEq)).selection <;>
            simp [hsel, ReferenceActivePhysicalStep.coordinatorFailure] at hobs
      | initializerFailure dispatched startEq checked checkedEq =>
          cases hsel : (ReferenceActivePhysicalStep.DispatchCut.live
              registers owned base
              (.initializerFailure dispatched startEq checked checkedEq)).selection <;>
            simp [hsel, ReferenceActivePhysicalStep.coordinatorFailure] at hobs
      | localFailure dispatched startEq reason =>
          cases hsel : (ReferenceActivePhysicalStep.DispatchCut.live
              registers owned base (.localFailure dispatched startEq reason)).selection <;>
            simp [hsel, ReferenceActivePhysicalStep.coordinatorFailure] at hobs
      | cutoffChosen dispatched startEq ledger initEq candidate domain clock pending noAssign selection =>
          cases hsel : (ReferenceActivePhysicalStep.DispatchCut.live
              registers owned base
              (.cutoffChosen dispatched startEq ledger initEq candidate domain clock pending
                noAssign selection)).selection with
          | none => simp [hsel, ReferenceActivePhysicalStep.coordinatorFailure] at hobs
          | some selected =>
              have hcollection :
                  (ReferenceActivePhysicalStep.collectionPostChoice prepared registers.payload
                    (ReferenceActivePhysicalStep.sharedLedger ledger) dispatched.startResult
                    (ReferenceActivePhysicalStep.liveRegistersAt registers record.input.time).complementWeights).configuration =
                      .live nextRegisters nextOwned nextBase := by
                simpa [hsel] using hobs
              have hphase := ReferenceCollectionPhaseHistory.collectionPostChoice_no_installation
                prepared registers.payload (ReferenceActivePhysicalStep.sharedLedger ledger)
                dispatched.startResult
                (ReferenceActivePhysicalStep.liveRegistersAt registers record.input.time).complementWeights
              rw [hcollection] at hphase
              simp [ReferenceCollectionPhaseHistory.CollectionPhase] at hphase
      | continuingChosen dispatched startEq continuation selection =>
          by_cases hsel : (ReferenceActivePhysicalStep.DispatchCut.live
              registers owned base
              (.continuingChosen dispatched startEq continuation selection)).selection = none
          · simp [hsel, ReferenceActivePhysicalStep.coordinatorFailure] at hobs
          · have hlive :
                (ReferenceActivePhysicalStep.livePostChoice prepared
                  (ReferenceActivePhysicalStep.liveRegistersAt registers record.input.time)
                  (ReferenceActivePhysicalStep.liveOwnedAt registers owned record.input.time)
                  base dispatched.startResult).configuration =
                    .live nextRegisters nextOwned nextBase := by
              simpa [hsel] using hobs
            exact livePostChoice_savedProposal prepared
              (ReferenceActivePhysicalStep.liveRegistersAt registers record.input.time)
              (ReferenceActivePhysicalStep.liveOwnedAt registers owned record.input.time)
              base dispatched.startResult nextRegisters nextOwned nextBase hlive hnone
  | collection payload ledger clock cutoff outcome =>
      have heq := ReferenceActivePhysicalStep.observeCoordinator_collection_equation
        prepared payload ledger clock cutoff outcome hprep
      rw [heq] at hobs
      cases outcome with
      | clockFailure failure startEq =>
          cases hsel : (ReferenceActivePhysicalStep.DispatchCut.collection
              payload ledger clock cutoff (.clockFailure failure startEq)).selection <;>
            simp [hsel, ReferenceActivePhysicalStep.coordinatorFailure] at hobs
      | localFailure started startEq coreInvalid reason =>
          cases hsel : (ReferenceActivePhysicalStep.DispatchCut.collection
              payload ledger clock cutoff
              (.localFailure started startEq coreInvalid reason)).selection <;>
            simp [hsel, ReferenceActivePhysicalStep.coordinatorFailure] at hobs
      | coreFailure core started startEq reason =>
          cases hsel : (ReferenceActivePhysicalStep.DispatchCut.collection
              payload ledger clock cutoff
              (.coreFailure core started startEq reason)).selection <;>
            simp [hsel, ReferenceActivePhysicalStep.coordinatorFailure] at hobs
      | continuing core snapshot boundary scores =>
          cases hsel : (ReferenceActivePhysicalStep.DispatchCut.collection
              payload ledger clock cutoff
              (.continuing core snapshot boundary scores)).selection with
          | none => simp [hsel, ReferenceActivePhysicalStep.coordinatorFailure] at hobs
          | some selected =>
              have hcollection :
                  (ReferenceActivePhysicalStep.collectionPostChoice prepared payload ledger
                    snapshot.clockStarted
                    (CoordinatorCollectionInteractive.PreObservationInputs.weights
                      (ReferenceActivePhysicalStep.collectionInput record.input payload ledger clock cutoff)
                      snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq)).configuration =
                        .live nextRegisters nextOwned nextBase := by
                simpa [hsel] using hobs
              have hphase := ReferenceCollectionPhaseHistory.collectionPostChoice_no_installation
                prepared payload ledger snapshot.clockStarted
                (CoordinatorCollectionInteractive.PreObservationInputs.weights
                  (ReferenceActivePhysicalStep.collectionInput record.input payload ledger clock cutoff)
                  snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq)
              rw [hcollection] at hphase
              simp [ReferenceCollectionPhaseHistory.CollectionPhase] at hphase
      | laterReconstructionFailure core consistent started startEq instruction assignmentEq reason laterEq =>
          cases hsel : (ReferenceActivePhysicalStep.DispatchCut.collection payload ledger clock
              cutoff (.laterReconstructionFailure core consistent started startEq instruction
                assignmentEq reason laterEq)).selection <;>
            simp [hsel, ReferenceActivePhysicalStep.coordinatorFailure] at hobs
      | laterPrefixFailure core consistent started startEq instruction assignmentEq arm reason laterEq =>
          cases hsel : (ReferenceActivePhysicalStep.DispatchCut.collection payload ledger clock
              cutoff (.laterPrefixFailure core consistent started startEq instruction
                assignmentEq arm reason laterEq)).selection <;>
            simp [hsel, ReferenceActivePhysicalStep.coordinatorFailure] at hobs
      | laterOrientationFailure core consistent started startEq instruction assignmentEq set laterEq =>
          cases hsel : (ReferenceActivePhysicalStep.DispatchCut.collection payload ledger clock
              cutoff (.laterOrientationFailure core consistent started startEq instruction
                assignmentEq set laterEq)).selection <;>
            simp [hsel, ReferenceActivePhysicalStep.coordinatorFailure] at hobs
      | laterChoiceFailure core consistent started startEq instruction assignmentEq output consistencyEq
          clockData installation reason =>
          cases hsel : (ReferenceActivePhysicalStep.DispatchCut.collection payload ledger clock
              cutoff (.laterChoiceFailure core consistent started startEq instruction assignmentEq
                output consistencyEq clockData installation reason)).selection <;>
            simp [hsel, ReferenceActivePhysicalStep.coordinatorFailure] at hobs
      | laterChosen core consistent started startEq instruction assignmentEq output consistencyEq
          clockData installation selection =>
          by_cases hsel : (ReferenceActivePhysicalStep.DispatchCut.collection payload ledger clock
              cutoff (.laterChosen core consistent started startEq instruction assignmentEq output
                consistencyEq clockData installation selection)).selection = none
          · simp [hsel, ReferenceActivePhysicalStep.coordinatorFailure] at hobs
          · have hlive :
                (ReferenceActivePhysicalStep.livePostChoice prepared installation.registers
                  installation.ownedRegisters installation.retainedBaseScore started).configuration =
                    .live nextRegisters nextOwned nextBase := by
              simpa [hsel] using hobs
            exact livePostChoice_savedProposal prepared installation.registers
              installation.ownedRegisters installation.retainedBaseScore started
              nextRegisters nextOwned nextBase hlive hnone
  | invalidCollectionCutoff =>
      have hdagger : prepared.observeCoordinator.configuration = .dagger := by
        unfold ReferenceActivePhysicalStep.PreparedRound.observeCoordinator
        simp [hprep, ReferenceActivePhysicalStep.DispatchCut.selection,
          ReferenceActivePhysicalStep.coordinatorFailure]
      rw [hdagger] at hobs
      cases hobs

  | dagger =>
      have hdagger : prepared.observeCoordinator.configuration = .dagger := by
        unfold ReferenceActivePhysicalStep.PreparedRound.observeCoordinator
        simp [hprep, ReferenceActivePhysicalStep.DispatchCut.selection]
      rw [hdagger] at hobs
      cases hobs

private theorem actual_previous_proposal_read
    (record : Record (p := p) (rate := rate)) (i : Fin (p.m - 1))
    (next : ReferencePrelaunchFollower.State p rate.eta)
    (nextMemory : ActiveFollowerLifecycle.LocalMemory p)
    (houtput : record.output.next.followers i = .ordinary next nextMemory)
    (hoccupied : next.status ≠ .unoccupied) :
    nextMemory.lastProposalRead = some ⟨record.input.time,
      FollowerCutoffScan.completeRowProposalBit p rate.eta.val record.input.row
        record.input.time⟩ := by
  rcases record with ⟨input, output, outputEq⟩
  cases outputEq
  let prepared := ReferenceActivePhysicalStep.prepare input
  let sender := prepared.followers.followers i
  let view := prepared.coordinator.downView
  let observation := prepared.feedback.observations
    (PublicDiscreteDraws.followerPlayer p.two_le_m i)
  have hfinishFollower :
      (ReferenceActivePhysicalStep.finishFollower view sender observation).configuration =
        .ordinary next nextMemory := by
    simpa only [ReferenceActivePhysicalStep.step,
      ReferenceActivePhysicalStep.PreparedRound.observeFollower,
      prepared, sender, view, observation] using houtput
  obtain ⟨choice, memory, post, hchoice, hrecord, hfinish, _, _⟩ :=
    ReferenceFollowerReplyChronology.finishFollower_ordinary_inversion
      view sender observation next nextMemory hfinishFollower
  have halign := prepared.follower_alignment i
  have hread := releaseAndFinish_proposal_read_of_occupied_output
    sender.follower sender.time sender.row observation choice post next memory nextMemory
    hfinish hoccupied
  simpa only [sender, halign.1, halign.2.2.1] using hread

private theorem cutoff_choice_unoccupied
    (prev current : Record (p := p) (rate := rate))
    (i : Fin (p.m - 1))
    (target : ReferenceAcceptedUpFollowerHistory.DownRecord (p := p) (rate := rate))
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (choice : ReferencePrelaunchFollower.State p rate.eta)
    (choiceMemory : ActiveFollowerLifecycle.LocalMemory p)
    (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (hprevTime : prev.input.time.val + 1 = current.input.time.val)
    (hprevOutput : prev.output.next.followers i = .ordinary state memory)
    (hrecord : state.lastDown = some target)
    (hstart : ActiveFollowerLifecycle.startRound rate.eta current.input.time
      state memory = .ok (choice, choiceMemory))
    (hpriorProposal : registers.priorClock.lastProposal = some
      (prev.input.time, FollowerCutoffScan.completeRowProposalBit p rate.eta.val
        prev.input.row prev.input.time))
    (hcutoffAlternative :
      FollowerCutoffScan.calendarRound current.input.time = registers.priorClock.g ∨
      ∃ stamp, registers.priorClock.lastProposal = some (stamp, true) ∧
        stamp.val + 1 = current.input.time.val)
    (hboundaryFrame :
      FollowerCutoffScan.gridBoundary p rate.eta.val
        (ActiveFollowerLifecycle.acceptedStartCoordinate target) = registers.priorClock.g)
    (hstarted : target.val.sigma ≤ current.input.time.val)
    (hnotmissed : current.input.time.val + 1 ≤
      FollowerCutoffScan.gridBoundary p rate.eta.val
        (ActiveFollowerLifecycle.acceptedStartCoordinate target)) :
    choice.status = .unoccupied := by
  have hdomain : ActiveFollowerLifecycle.localStateDomainValid state := by
    by_contra hbad
    simp [ActiveFollowerLifecycle.startRound, ActiveFollowerLifecycle.interruptionDecision,
      hbad] at hstart
  by_cases hunoccupied : state.status = .unoccupied
  · rw [ActiveFollowerLifecycle.startRound_unoccupied rate.eta current.input.time
      state memory hdomain hunoccupied] at hstart
    have hpair := Except.ok.inj hstart
    have hstatus := congrArg (fun pair :
        ReferencePrelaunchFollower.State p rate.eta × ActiveFollowerLifecycle.LocalMemory p =>
        pair.1.status) hpair
    simpa [hunoccupied] using hstatus.symm
  · obtain hread := actual_previous_proposal_read prev i state memory hprevOutput hunoccupied
    have hcut :
        FollowerCutoffScan.gridBoundary p rate.eta.val
            (ActiveFollowerLifecycle.acceptedStartCoordinate target) =
          current.input.time.val + 1 ∨
        FollowerCutoffScan.completeRowProposalBit p rate.eta.val prev.input.row
          prev.input.time = true := by
      rcases hcutoffAlternative with hgrid | ⟨stamp, hproposal, hstamp⟩
      · left
        calc
          FollowerCutoffScan.gridBoundary p rate.eta.val
              (ActiveFollowerLifecycle.acceptedStartCoordinate target) = registers.priorClock.g :=
            hboundaryFrame
          _ = FollowerCutoffScan.calendarRound current.input.time := hgrid.symm
          _ = current.input.time.val + 1 := by rfl
      · right
        have htoken : (stamp, true) =
            (prev.input.time,
              FollowerCutoffScan.completeRowProposalBit p rate.eta.val prev.input.row
                prev.input.time) := Option.some.inj (hproposal.symm.trans hpriorProposal)
        exact (Prod.mk.inj htoken).2.symm
    let token : ActiveFollowerLifecycle.ProposalRead p :=
      ⟨prev.input.time, FollowerCutoffScan.completeRowProposalBit p rate.eta.val
        prev.input.row prev.input.time⟩
    have hread' : memory.lastProposalRead = some token := by
      simpa [token] using hread
    have hstamp : ActiveFollowerLifecycle.isPriorProposalRead current.input.time token := by
      change prev.input.time.val + 1 = current.input.time.val
      exact hprevTime
    have hbranch := ActiveFollowerLifecycle.startRound_occupied_branch rate.eta
      current.input.time state memory hunoccupied hdomain target hrecord hstarted
      hnotmissed token hread' hstamp
    have hinterrupt :
        FollowerCutoffScan.gridBoundary p rate.eta.val
            (ActiveFollowerLifecycle.acceptedStartCoordinate target) =
          current.input.time.val + 1 ∨ token.bit = true := by
      rcases hcut with hgrid | hbit
      · exact Or.inl hgrid
      · exact Or.inr (by simpa [token] using hbit)
    have hdecision :
        (FollowerCutoffScan.gridBoundary p rate.eta.val
            (ActiveFollowerLifecycle.acceptedStartCoordinate target) =
              current.input.time.val + 1 || token.bit) = true := by
      rcases hinterrupt with hgrid | hbit
      · simp [hgrid]
      · simp [hbit]
    rw [hbranch, hdecision] at hstart
    have hpair := Except.ok.inj hstart
    have hstatus := congrArg (fun pair :
        ReferencePrelaunchFollower.State p rate.eta × ActiveFollowerLifecycle.LocalMemory p =>
        pair.1.status) hpair
    simpa using hstatus.symm

private theorem dispatchLive_cutoff_command
    (input : CoordinatorRoundDispatch.LiveInput p)
    (out : CoordinatorStartRoundCutoffDispatch.Output input.registers
      input.ownedRegisters input.followerBaseScore)
    (hs ledger hi he hd hc hp hn selection)
    (h : CoordinatorRoundDispatch.dispatchLive input =
      .cutoffChosen out hs ledger hi he hd hc hp hn selection) :
    out.startResult.ledgerCommand = some (.initializeAt input.registers.time) := by
  classical
  unfold CoordinatorRoundDispatch.dispatchLive at h
  dsimp only at h
  split at h
  · cases h
  · rename_i actual hactual
    have hstart := CoordinatorRoundDispatch.cutoffDispatch_startResult_eq
      input.registers input.ownedRegisters input.followerBaseScore actual hactual
    split at h
    · cases h
    · cases h
    · have hframe : CoordinatorLiveChoiceRecorderStep.unchangedLiveClockFrame input.registers actual.startResult := by
        by_contra hbad
        rw [dite_eq_right hbad] at h
        cases h
      rw [dite_eq_left hframe] at h
      have hpayload : input.registers.priorClock.sigma = some input.registers.payload.sigma := by
        by_contra hbad
        rw [dite_eq_right hbad] at h
        cases h
      rw [dite_eq_left hpayload] at h
      have hgrid : input.registers.gridBoundary = input.registers.priorClock.g := by
        by_contra hbad
        rw [dite_eq_right hbad] at h
        cases h
      rw [dite_eq_left hgrid] at h
      have hscore : input.registers.scoreDomainValid := by
        by_contra hbad
        rw [dite_eq_right hbad] at h
        cases h
      rw [dite_eq_left hscore] at h
      have hqueue : input.ownedRegisters.queueDomainValid := by
        by_contra hbad
        rw [dite_eq_right hbad] at h
        cases h
      rw [dite_eq_left hqueue] at h
      have hprevious : input.ownedRegisters.previousServiceDomainValid := by
        by_contra hbad
        rw [dite_eq_right hbad] at h
        cases h
      rw [dite_eq_left hprevious] at h
      have hbase : ∀ i, input.followerBaseScore i ≤ p.T * D p := by
        by_contra hbad
        rw [dite_eq_right hbad] at h
        cases h
      rw [dite_eq_left hbase] at h
      have hlive : CoordinatorLocalArmChoice.assignmentIsLive input.registers.payload
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p actual.startResult.clock.u)
          input.registers.time := by
        by_contra hbad
        rw [dite_eq_right hbad] at h
        cases h
      rw [dite_eq_left hlive] at h
      have hchoice : CoordinatorLocalArmChoice.ChoiceInputsValid input.registers.payload
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p actual.startResult.clock.u)
          input.registers.time input.registers.complementWeights := by
        by_contra hbad
        rw [dite_eq_right hbad] at h
        cases h
      rw [dite_eq_left hchoice] at h
      have hboundary : actual.startResult.clock.g ≤ p.T + 1 := by
        by_contra hbad
        rw [dite_eq_right hbad] at h
        cases h
      rw [dite_eq_left hboundary] at h
      have henvelope : input.registers.complementEnvelopeValid := by
        by_contra hbad
        rw [dite_eq_right hbad] at h
        cases h
      rw [dite_eq_left henvelope] at h
      split at h
      · rename_i ha
        exact (CoordinatorLiveChoiceRecorderStep.coordinatorArmChoice_ne_none
          _ _ _ _ _ _ hchoice ha).elim
      · cases h
    · rename_i candidate hcandidate
      have hcommand := (CoordinatorRoundDispatch.cutoffDispatch_ledger_eq_candidate
        input.registers input.ownedRegisters input.followerBaseScore actual candidate
        hactual hcandidate).1
      have hresults := Except.ok.inj (hstart.symm.trans hs)
      exact (congrArg CoordinatorPhaseClock.StartRoundResult.ledgerCommand hresults).symm.trans
        hcommand

private theorem parse_expected_down
    (view : ReferenceDownReception.ChoiceTimeView p rate.eta)
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p) (t : Fin p.T)
    (M : ReferenceAcceptedUpFollowerHistory.DownRecord (p := p) (rate := rate))
    (h : ReferenceDownReception.ordinaryParse p rate
      (ReferenceDownReception.expectedDownFlatWord (some view) i row t) = some M) :
    M = view.payload.downRecord i := by
  simp only [ReferenceDownReception.expectedDownFlatWord] at h
  split at h
  · change OrdinaryMessageCodec.parseDown (ReferencePrelaunchFollower.codecParams p rate.eta)
      (some ((OrdinaryMessageCodec.wordEquivFlat
        (ReferencePrelaunchFollower.codecParams p rate.eta)).symm
          ((OrdinaryMessageCodec.wordEquivFlat
            (ReferencePrelaunchFollower.codecParams p rate.eta)) (view.payload.downWord i)))) =
        some M at h
    rw [Equiv.symm_apply_apply, view.payload.parseDown_downWord i] at h
    exact (Option.some.inj h).symm
  · cases h

private theorem accepted_down_current
    (view : ReferenceDownReception.ChoiceTimeView p rate.eta)
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p) (t : Fin p.T)
    (observation : ReferencePrelaunchFollower.Observation p)
    (before after : ReferencePrelaunchFollower.State p rate.eta)
    (raw M scan registers lastService)
    (h : (ReferenceDownReception.referenceDownCut p (some view) i row t
      observation rate before).outcome =
        .accepted before after raw M scan registers lastService) :
    M = view.payload.downRecord i := by
  classical
  unfold ReferenceDownReception.referenceDownCut at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  dsimp only at h
  split at h
  · rename_i hmatches
    dsimp only at h
    split at h <;> try contradiction
    rename_i parsed hparse
    have hrecord := parse_expected_down view i row t parsed (hmatches ▸ hparse)
    split at h <;> try contradiction
    split at h <;> try contradiction
    cases h
    exact hrecord
  · cases h

private theorem cutoff_tail_follower_frame
    (record : Record (p := p) (rate := rate)) (i : Fin (p.m - 1))
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (choice next : ReferencePrelaunchFollower.State p rate.eta)
    (memory nextMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hchoice : (ReferenceFollowerFixedReply.actualChoice record i).configuration =
      .ordinary choice memory)
    (hu : choice.status = .unoccupied)
    (hlast : choice.lastDown = some (payload.downRecord i))
    (view : ReferenceDownReception.ChoiceTimeView p rate.eta)
    (hview : record.output.preparation.coordinator.downView = some view)
    (hpayload : view.payload = payload)
    (hout : record.output.next.followers i = .ordinary next nextMemory) :
    next.status = .unoccupied ∧
      ReferenceFollowerReplyChronology.reply next = ReferenceFollowerReplyChronology.reply choice := by
  have hstart : ReferencePrelaunchFollower.acceptedStart choice = payload.sigma.val + 1 := by
    rw [ReferencePrelaunchFollower.acceptedStart, hlast]
    exact congrArg OrdinaryMessageCodec.DownFields.sigma (payload.downRecord_fields i)
  rcases record with ⟨input, output, outputEq⟩
  cases outputEq
  change (ReferenceActivePhysicalStep.prepare input).coordinator.downView = some view at hview
  change (ReferenceActivePhysicalStep.finishFollower _ _ _).configuration = _ at hout
  obtain ⟨actual, actualMemory, post, hc, hr, hf, _, _⟩ :=
    ReferenceFollowerReplyChronology.finishFollower_ordinary_inversion _ _ _ next nextMemory hout
  have hsame := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj (hc.symm.trans hchoice)
  obtain ⟨hactual, hmemory⟩ := hsame
  subst actual actualMemory
  have halign := (ReferenceActivePhysicalStep.prepare input).follower_alignment i
  simp only [halign.1, halign.2.1, halign.2.2.1, halign.2.2.2] at hr hf
  have hinv := ReferenceFollowerReplyChronology.recordFollower_ordinary_inversion
    _ _ _ _ _ _ _ _ choice post hr
  have hframe := ReferenceFollowerReplyChronology.releaseAndFinish_frame
    _ _ _ _ choice post next memory nextMemory hf
  rcases hinv with hkeep | ⟨logged, cut, raw, M, scan, registers, lastService,
    _, _, hcut, haccepted, hstrict, _⟩
  · exact ⟨(hframe.2 hu).trans (hkeep.2 hu).2, hframe.1.trans (hkeep.2 hu).1⟩
  · rw [hcut, hview] at haccepted
    have hm := accepted_down_current view i input.row input.time _ logged post
      raw M scan registers lastService haccepted
    have hsigma : M.val.sigma = payload.sigma.val + 1 := by
      rw [hm, hpayload]
      exact congrArg OrdinaryMessageCodec.DownFields.sigma (payload.downRecord_fields i)
    exact (Nat.lt_irrefl _ (hstart ▸ hsigma ▸ hstrict)).elim

private theorem collection_output
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (payload : ReferenceActivePhysicalStep.Payload rate) (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ)
    (ho : (ReferenceActivePhysicalStep.collectionPostChoice
      (ReferenceActivePhysicalStep.prepare x) payload ledger started weights).configuration ≠ .dagger) :
    ∃ out saved, (ReferenceActivePhysicalStep.collectionPostChoice
      (ReferenceActivePhysicalStep.prepare x) payload ledger started weights).configuration =
        .collection payload out saved := by
  have hphase := ReferenceCollectionPhaseHistory.collectionPostChoice_no_installation
    (ReferenceActivePhysicalStep.prepare x) payload ledger started weights
  have hp := ReferenceAssignmentPayloadPersistence.collectionPostChoice_payload_frame
    (ReferenceActivePhysicalStep.prepare x) payload ledger started weights
  cases he : (ReferenceActivePhysicalStep.collectionPostChoice
      (ReferenceActivePhysicalStep.prepare x) payload ledger started weights).configuration with
  | first => simp [he, ReferenceCollectionPhaseHistory.CollectionPhase] at hphase
  | live r q base => simp [he, ReferenceCollectionPhaseHistory.CollectionPhase] at hphase
  | dagger => exact (ho he).elim
  | collection actual out saved =>
      simp only [he, ReferenceAssignmentPayloadPersistence.storedPayload,
        Option.some_ne_none, false_or, Option.some.injEq] at hp
      subst actual
      exact ⟨out, saved, rfl⟩

private theorem cutoff_call
    (record : Record (p := p) (rate := rate)) (payload : ReferenceActivePhysicalStep.Payload rate)
    (hp : ReferenceAssignmentPayloadPersistence.storedPayload record.input.state.coordinator = some payload)
    (hc : ReferenceCollectionPhaseHistory.cutoffChosen record.input = true)
    (ho : record.output.next.coordinator ≠ .dagger) :
    ∃ d L, record.output.coordinator.up = some d ∧
      d.expected = ReferenceActivePhysicalStep.upExpected (ReferenceActivePhysicalStep.prepare record.input) ∧
      ReferenceCoordinatorUpPhysicalCall.siteLedger? (x := record.input) = some L ∧
      CoordinatorUpReception.receptionInputCheck
        (ReferenceCoordinatorUpPhysicalCall.actualUpInput record.input L) = true ∧
      d.input = ReferenceCoordinatorUpPhysicalCall.actualUpInput record.input L ∧
      L.sigma = payload.sigma.val + 1 ∧ L.cutoff = record.input.time.val + 1 ∧
      L.cursor = record.input.time.val + 1 ∧ L.pending = Finset.univ := by
  classical
  let x := record.input
  let prepared := ReferenceActivePhysicalStep.prepare x
  obtain ⟨r, q, base, hstate⟩ := cutoff_input_live x hc
  have hpayload : r.payload = payload := by
    rw [hstate, ReferenceAssignmentPayloadPersistence.storedPayload_live] at hp
    exact Option.some.inj hp
  let input := ReferenceActivePhysicalStep.liveInput x r q base
  have hdispatch : prepared.coordinator =
      .live r q base (CoordinatorRoundDispatch.dispatchLive input) := by
    rw [prepared.coordinator_eq]
    simp only [ReferenceActivePhysicalStep.dispatch, hstate, CoordinatorRoundDispatch.dispatch]
    rfl
  unfold ReferenceCollectionPhaseHistory.cutoffChosen at hc
  rw [hdispatch] at hc
  cases hlive : CoordinatorRoundDispatch.dispatchLive input with
  | cutoffChosen dispatched hclock ledger hinit hledger hdomain hclockFrame hpending hnone selected =>
    have hobserve := ReferenceActivePhysicalStep.observeCoordinator_live_equation
      prepared r q base _ (hdispatch.trans
        (congrArg (fun o => ReferenceActivePhysicalStep.DispatchCut.live r q base o) hlive))
    simp only [ReferenceActivePhysicalStep.DispatchCut.selection, ReferenceActivePhysicalStep.selectionAt,
      ↓reduceDIte, reduceCtorEq, ↓reduceIte] at hobserve
    have houtput : record.output.coordinator = ReferenceActivePhysicalStep.collectionPostChoice
        prepared r.payload (ReferenceActivePhysicalStep.sharedLedger ledger) dispatched.startResult
        (ReferenceActivePhysicalStep.liveRegistersAt r x.time).complementWeights := by
      rw [record.output_eq]; exact hobserve
    have hordinary : (ReferenceActivePhysicalStep.collectionPostChoice prepared r.payload
        (ReferenceActivePhysicalStep.sharedLedger ledger) dispatched.startResult
        (ReferenceActivePhysicalStep.liveRegistersAt r x.time).complementWeights).configuration ≠ .dagger := by
      rw [← houtput, record.output_eq]
      rw [record.output_eq] at ho
      exact ho
    cases hr : CoordinatorRecorderComplementBridge.run
        (ReferenceActivePhysicalStep.collectionRecordingInput prepared r.payload dispatched.startResult
          (ReferenceActivePhysicalStep.liveRegistersAt r x.time).complementWeights) with
    | none => simp [ReferenceActivePhysicalStep.collectionPostChoice, hr,
        ReferenceActivePhysicalStep.coordinatorFailure] at hordinary
    | some recording =>
      cases hs : CoordinatorCollectionLedger.startRound (ReferenceActivePhysicalStep.sharedLedger ledger)
          (x.time.val + 1) (ReferenceActivePhysicalStep.collectionEnabled
            (ReferenceActivePhysicalStep.sharedLedger ledger) x.time)
          (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) with
      | invalid => simp [ReferenceActivePhysicalStep.collectionPostChoice, hr, hs,
          ReferenceActivePhysicalStep.coordinatorFailure] at hordinary
      | rejected out => simp [ReferenceActivePhysicalStep.collectionPostChoice, hr, hs,
          ReferenceActivePhysicalStep.coordinatorFailure] at hordinary
      | success L =>
        have hcheck : CoordinatorUpReception.receptionInputCheck
            (ReferenceCoordinatorUpPhysicalCall.actualUpInput x L) = true := by
          by_contra hbad
          change ¬ CoordinatorUpReception.receptionInputCheck
            (ReferenceUpReception.receptionInputAtRow rate x.row
              (ReferenceActivePhysicalStep.upInputs prepared L) x.time) = true at hbad
          have hresult : (ReferenceActivePhysicalStep.receiveUp prepared L).result = .invalid := by
            simp only [ReferenceActivePhysicalStep.receiveUp,
              ReferenceUpReception.receiveUpFilteredAtRow, ite_eq_right hbad]
          simp only [ReferenceActivePhysicalStep.collectionPostChoice, hr, hs,
            ReferenceActivePhysicalStep.collectionFinish, hresult,
            ReferenceActivePhysicalStep.coordinatorFailure, ne_eq, not_true_eq_false] at hordinary
        have hdiag : ∃ d, (ReferenceActivePhysicalStep.receiveUp prepared L).diagnostic = some d ∧
            d.expected = ReferenceActivePhysicalStep.upExpected prepared := by
          change CoordinatorUpReception.receptionInputCheck
            (ReferenceUpReception.receptionInputAtRow rate x.row
              (ReferenceActivePhysicalStep.upInputs prepared L) x.time) = true at hcheck
          simp only [ReferenceActivePhysicalStep.receiveUp, hcheck, ↓reduceIte]
          exact ⟨_, rfl, rfl⟩
        obtain ⟨d, hdiag, hexpected⟩ := hdiag
        have hretained : record.output.coordinator.up = some d := by
          rw [houtput]
          simp only [ReferenceActivePhysicalStep.collectionPostChoice, hr, hs]
          have hframe : (ReferenceActivePhysicalStep.collectionFinish (x := x) r.payload
              dispatched.startResult recording (ReferenceActivePhysicalStep.receiveUp prepared L)).up =
              (ReferenceActivePhysicalStep.receiveUp prepared L).diagnostic := by
            unfold ReferenceActivePhysicalStep.collectionFinish
            split <;> dsimp only
            all_goals repeat' (first | split | rfl)
          exact hframe.trans hdiag
        obtain ⟨actual, hsite, hvalid, hinput, _⟩ :=
          ReferenceCoordinatorUpPhysicalCall.record_retained_up_input record d hretained
        have hcut : (ReferenceActivePhysicalStep.prepare x).coordinator =
            .live r q base (.cutoffChosen dispatched hclock ledger hinit hledger hdomain
              hclockFrame hpending hnone selected) := by
          exact hdispatch.trans
            (congrArg (fun o => ReferenceActivePhysicalStep.DispatchCut.live r q base o) hlive)
        have hr' : CoordinatorRecorderComplementBridge.run
            (ReferenceActivePhysicalStep.collectionRecordingInput (ReferenceActivePhysicalStep.prepare x)
              r.payload dispatched.startResult
              (ReferenceActivePhysicalStep.liveRegistersAt r x.time).complementWeights) = some recording := hr
        have hsiteL : ReferenceCoordinatorUpPhysicalCall.siteLedger? (x := x) = some L := by
          simp only [ReferenceCoordinatorUpPhysicalCall.siteLedger?, hcut,
            ReferenceActivePhysicalStep.DispatchCut.selection, ReferenceActivePhysicalStep.selectionAt,
            ↓reduceDIte, reduceCtorEq, ReferenceCoordinatorUpPhysicalCall.tailLedger?, hr', hs]
        have hsame : actual = L := Option.some.inj (hsite.symm.trans hsiteL)
        subst actual
        have hcandidate := ReferenceActivePhysicalStep.collection_started_candidate
          (ReferenceActivePhysicalStep.sharedLedger ledger) L x.time _ hs
        have hfields : L.sigma = payload.sigma.val + 1 ∧ L.cutoff = x.time.val + 1 ∧
            L.cursor = x.time.val + 1 ∧ L.pending = Finset.univ := by
          rw [hcandidate, hledger]
          exact ⟨congrArg (fun v : ReferenceActivePhysicalStep.Payload rate => v.sigma.val + 1)
            hpayload, rfl, rfl, rfl⟩
        exact ⟨d, L, hretained, hexpected, hsiteL, hvalid, hinput, hfields⟩
  | clockFailure failure he => simp [hlive] at hc
  | initializerFailure out hs checked he => simp [hlive] at hc
  | localFailure out hs reason => simp [hlive] at hc
  | continuingChosen out hs continuation selected => simp [hlive] at hc

section Run

variable (initial : State p rate) (rows : CompletePublicTable.CompleteRows p)
  (J : Fin (M p)) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (start count : ℕ) (span : start + count ≤ p.T)
  (mode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
  (k : ℕ) (hk : k + 1 < count) (payload : ReferenceActivePhysicalStep.Payload rate)
  (i : Fin (p.m - 1))

/-- The adjacent accepted-DOWN branch supplies the actual unoccupied collection
seed. Source: `06_interruptions.tex:41-69,164-177,327-348` and
`05_binary_transport.tex:70-88`. Both ordinary endpoints remain explicit. -/
theorem cutoff_after_down_reply_seed :
  let E := ReferenceActivePhysicalHorizon.run initial rows J rewards start count span mode
  let prev := E.records[k]'(by
    rw [ReferenceActivePhysicalHorizon.run_record_count]; omega)
  let current := E.records[k + 1]'(by
    rw [ReferenceActivePhysicalHorizon.run_record_count]; exact hk)
  ∀ (_hp : ReferenceAssignmentPayloadPersistence.storedPayload current.input.state.coordinator =
      some payload)
    (_hc : ReferenceCollectionPhaseHistory.cutoffChosen current.input = true)
    (_hd : ReferenceAcceptedUpFollowerHistory.RetainedDown prev i (payload.downRecord i))
    (next : ReferencePrelaunchFollower.State p rate.eta)
    (nextMemory : ActiveFollowerLifecycle.LocalMemory p)
    (_hf : current.output.next.followers i = .ordinary next nextMemory)
    (_ho : current.output.next.coordinator ≠ .dagger),
    ∃ s memory choice choiceMemory ledger saved,
      current.input.state.followers i = .ordinary s memory ∧
      (ReferenceFollowerFixedReply.actualChoice current i).configuration =
        .ordinary choice choiceMemory ∧
      ActiveFollowerLifecycle.startRound rate.eta current.input.time s memory =
        .ok (choice, choiceMemory) ∧
      s.lastDown = some (payload.downRecord i) ∧
      choice.status = .unoccupied ∧
      ReferenceFollowerReplyChronology.reply choice = ReferenceFollowerReplyChronology.reply s ∧
      next.status = .unoccupied ∧
      ReferenceFollowerReplyChronology.reply next = ReferenceFollowerReplyChronology.reply s ∧
      next.lastDown = some (payload.downRecord i) ∧
      ReferencePrelaunchFollower.acceptedStart next = payload.sigma.val + 1 ∧
      current.output.next.coordinator = .collection payload ledger saved := by
  classical
  dsimp only
  let E := ReferenceActivePhysicalHorizon.run initial rows J rewards start count span mode
  let prev := E.records[k]'(by
    rw [ReferenceActivePhysicalHorizon.run_record_count]; omega)
  let current := E.records[k + 1]'(by
    rw [ReferenceActivePhysicalHorizon.run_record_count]; exact hk)
  intro hp hc hd next nextMemory hf ho
  have hlength : E.records.length = count := ReferenceActivePhysicalHorizon.run_record_count
    initial rows J rewards start count span mode
  have hprev : k < E.records.length := by omega
  have hcurrent : k + 1 < E.records.length := by omega
  have hadj := connected_adjacent E.connected ⟨k, hprev⟩ hcurrent
  have htimes := ReferenceActivePhysicalHorizon.run_time_values
    initial rows J rewards start count span mode
  change E.records.map (fun r => r.input.time.val) =
    ReferenceActivePhysicalHorizon.calendar start count at htimes
  have htime (n : ℕ) (hn : n < E.records.length) :
      (E.records[n]'hn).input.time.val = start + n := by
    have hm : (E.records.map (fun r => r.input.time.val))[n]'(by simpa using hn) =
        start + n := by
      simp only [htimes, ReferenceActivePhysicalHorizon.calendar, List.getElem_range'_1]
    simpa only [List.getElem_map] using hm
  have hprevTime : prev.input.time.val + 1 = current.input.time.val := by
    rw [htime k hprev, htime (k + 1) hcurrent]; omega
  obtain ⟨s, memory, choice, choiceMemory, hs, hchoice, hstart, hlast⟩ :=
    adjacent_local_states prev current i (payload.downRecord i) next nextMemory hadj hd hf
  have hframe := ActiveFollowerLifecycle.startRound_frame rate.eta current.input.time
    s choice memory choiceMemory hstart
  have hreply : ReferenceFollowerReplyChronology.reply choice =
      ReferenceFollowerReplyChronology.reply s := by
    simp only [ReferenceFollowerReplyChronology.reply,
      hframe.1, hframe.2.1, hframe.2.2.1, hframe.2.2.2.1]
  obtain ⟨r, q, base, hstate⟩ := cutoff_input_live current.input hc
  have hpayload : r.payload = payload := by
    change ReferenceAssignmentPayloadPersistence.storedPayload current.input.state.coordinator =
      some payload at hp
    rw [hstate, ReferenceAssignmentPayloadPersistence.storedPayload_live] at hp
    exact Option.some.inj hp
  let input := ReferenceActivePhysicalStep.liveInput current.input r q base
  have hdispatch : (ReferenceActivePhysicalStep.prepare current.input).coordinator =
      .live r q base (CoordinatorRoundDispatch.dispatchLive input) := by
    rw [(ReferenceActivePhysicalStep.prepare current.input).coordinator_eq]
    simp only [ReferenceActivePhysicalStep.dispatch, hstate, CoordinatorRoundDispatch.dispatch]
    rfl
  have hcut := hc
  unfold ReferenceCollectionPhaseHistory.cutoffChosen at hcut
  rw [hdispatch] at hcut
  cases hlive : CoordinatorRoundDispatch.dispatchLive input with
  | cutoffChosen dispatched hclock ledger hinit hledger hdomain hclockFrame hpending hnone selected =>
    have hcommand := dispatchLive_cutoff_command input dispatched hclock ledger hinit hledger
      hdomain hclockFrame hpending hnone selected hlive
    dsimp only [input, ReferenceActivePhysicalStep.liveInput,
      ReferenceActivePhysicalStep.liveRegistersAt] at hclock hcommand hdomain
    obtain ⟨sigma, hsigma, hu, hcutAlternative⟩ := startRound_initializeAt_cutoff_inputs p
      rate.eta.val r.priorClock r.clockPending current.input.time dispatched.startResult
      hclock hcommand
    have hclockValid : CoordinatorPhaseClock.clockRegistersValid p rate.eta.val r.priorClock := by
      by_contra hbad
      simp [CoordinatorPhaseClock.startRound, hbad] at hclock
      split at hclock <;> contradiction
    have hboundary : FollowerCutoffScan.gridBoundary p rate.eta.val payload.sigma =
        r.priorClock.g := by
      have hgrid := hclockValid.1
      rw [hdomain.1] at hgrid
      simpa only [CoordinatorPhaseClock.boundaryFromSigma, hpayload] using hgrid.symm
    have hprior : prev.output.next.coordinator = .live r q base := by
      rw [hadj]; exact hstate
    have hproposal := record_live_savedProposal prev r q base hprior hu
    have hprevOutput : prev.output.next.followers i = .ordinary s memory := by
      rw [hadj]; exact hs
    have htargetSigma : (payload.downRecord i).val.sigma = payload.sigma.val + 1 :=
      congrArg OrdinaryMessageCodec.DownFields.sigma (payload.downRecord_fields i)
    have htargetCoordinate : ActiveFollowerLifecycle.acceptedStartCoordinate
        (payload.downRecord i) = payload.sigma := by
      apply Fin.ext
      have hv := ActiveFollowerLifecycle.accepted_start_coordinate_one_based (payload.downRecord i)
      rw [htargetSigma] at hv
      omega
    have hstatus := cutoff_choice_unoccupied prev current i (payload.downRecord i)
      s memory choice choiceMemory r hprevTime hprevOutput hlast hstart hproposal
      (by
        rcases hcutAlternative with hg | ⟨stamp, bit, hb, ht, hbit⟩
        · exact Or.inl hg
        · exact Or.inr ⟨stamp, by simpa only [hbit] using hb, ht⟩)
      (by rw [htargetCoordinate]; exact hboundary)
      (by
        rw [htargetSigma, ← hpayload]
        have ht : r.payload.sigma.val < current.input.time.val := hdomain.2.2.1
        omega)
      (by rw [htargetCoordinate, hboundary, ← hdomain.2.1]; exact hdomain.2.2.2.1)
    have hprep : current.output.preparation = ReferenceActivePhysicalStep.prepare current.input := by
      rw [current.output_eq]; rfl
    have hview : ∃ view, current.output.preparation.coordinator.downView = some view ∧
        view.payload = payload := by
      rw [hprep, hdispatch, hlive]
      simp only [ReferenceActivePhysicalStep.DispatchCut.downView,
        ReferenceActivePhysicalStep.DispatchCut.selection, ReferenceActivePhysicalStep.selectionAt,
        ↓reduceDIte, Option.map_some]
      exact ⟨_, rfl, hpayload⟩
    obtain ⟨view, hview, hviewPayload⟩ := hview
    have hnext := cutoff_tail_follower_frame current i payload choice next choiceMemory nextMemory
      hchoice hstatus (hframe.1.trans hlast) view hview hviewPayload hf
    have hobserve := ReferenceActivePhysicalStep.observeCoordinator_live_equation
      (ReferenceActivePhysicalStep.prepare current.input) r q base _ (hdispatch.trans
        (congrArg (fun o => ReferenceActivePhysicalStep.DispatchCut.live r q base o) hlive))
    simp only [ReferenceActivePhysicalStep.DispatchCut.selection,
      ReferenceActivePhysicalStep.selectionAt, ↓reduceDIte, reduceCtorEq, ↓reduceIte] at hobserve
    have hcoordinator : current.output.next.coordinator =
        (ReferenceActivePhysicalStep.collectionPostChoice
          (ReferenceActivePhysicalStep.prepare current.input) r.payload
          (ReferenceActivePhysicalStep.sharedLedger ledger) dispatched.startResult
          (ReferenceActivePhysicalStep.liveRegistersAt r current.input.time).complementWeights).configuration := by
      rw [current.output_eq, (ReferenceActivePhysicalStep.step_next_fields current.input).1, hobserve]
    obtain ⟨out, saved, hout⟩ := collection_output r.payload
      (ReferenceActivePhysicalStep.sharedLedger ledger) dispatched.startResult
      (ReferenceActivePhysicalStep.liveRegistersAt r current.input.time).complementWeights
      (by rw [← hcoordinator]; exact ho)
    have hnextReply := hnext.2.trans hreply
    have hnextLast : next.lastDown = some (payload.downRecord i) :=
      (congrArg Prod.fst hnextReply).trans hlast
    refine ⟨s, memory, choice, choiceMemory, out, saved, hs, hchoice, hstart, hlast,
      hstatus, hreply, hnext.1, hnextReply, hnextLast, ?_, ?_⟩
    · rw [ReferencePrelaunchFollower.acceptedStart, hnextLast]; exact htargetSigma
    · rw [hcoordinator, hout, hpayload]
  | clockFailure failure he => simp [hlive] at hcut
  | initializerFailure out hs checked he => simp [hlive] at hcut
  | localFailure out hs reason => simp [hlive] at hcut
  | continuingChosen out hs continuation selected => simp [hlive] at hcut

/-- A selected UP on that same cutoff constructs the checked current reply and
its actual reception-site acceptance test, before any parsed receiver effect.
Sources: `05_binary_transport.tex:36-53,70-124`, `06_interruptions.tex:164-177,277-284`,
and `appendix_a_local_protocol.tex:92-109,151-157`. -/
theorem cutoff_selected_up_offer :
  let E := ReferenceActivePhysicalHorizon.run initial rows J rewards start count span mode
  let prev := E.records[k]'(by
    rw [ReferenceActivePhysicalHorizon.run_record_count]; omega)
  let current := E.records[k + 1]'(by
    rw [ReferenceActivePhysicalHorizon.run_record_count]; exact hk)
  let x := current.input
  ∀ (_hp : ReferenceAssignmentPayloadPersistence.storedPayload x.state.coordinator = some payload)
    (_hc : ReferenceCollectionPhaseHistory.cutoffChosen x = true)
    (_hd : ReferenceAcceptedUpFollowerHistory.RetainedDown prev i (payload.downRecord i))
    (next : ReferencePrelaunchFollower.State p rate.eta)
    (nextMemory : ActiveFollowerLifecycle.LocalMemory p)
    (_hf : current.output.next.followers i = .ordinary next nextMemory)
    (_ho : current.output.next.coordinator ≠ .dagger)
    (_hu : PublicDiscreteDraws.slotDraw (x.row.2 x.time).1 = PublicDiscreteDraws.upSlot)
    (_hi : ReferenceActivePhysicalStep.upSenderIndex x = i),
    ∃ s memory choice choiceMemory M d L,
      x.state.followers i = .ordinary s memory ∧
      (ReferenceFollowerFixedReply.actualChoice current i).configuration = .ordinary choice choiceMemory ∧
      s.lastDown = some (payload.downRecord i) ∧ choice.status = .unoccupied ∧
      ReferenceFollowerReplyChronology.reply choice = ReferenceFollowerReplyChronology.reply s ∧
      M.val = ActiveFollowerQueueOperation.upOfferFields s ∧
      ActiveFollowerQueueOperation.checkedUpOffer rate.eta i x.row
        (x.state.activations i) x.time choice = .offer M ∧
      (let w := ActiveFollowerArmChoice.offeredUpWord rate.eta M
       ReferenceActiveAffinePositiveTest.upSent x = some w ∧
       ReferenceActivePhysicalStep.upExpected (ReferenceActivePhysicalStep.prepare x) = some w ∧
       CoordinatorUpReception.parseDecoderOutput (p := p) (eta := rate.eta.val) (some w) = some M ∧
       current.output.coordinator.up = some d ∧ d.expected = some w ∧
       ReferenceCoordinatorUpPhysicalCall.siteLedger? (x := x) = some L ∧
       CoordinatorUpReception.receptionInputCheck
         (ReferenceCoordinatorUpPhysicalCall.actualUpInput x L) = true ∧
       d.input = ReferenceCoordinatorUpPhysicalCall.actualUpInput x L ∧
       L.sigma = payload.sigma.val + 1 ∧ L.cutoff = x.time.val + 1 ∧
       L.cursor = x.time.val + 1 ∧ i ∈ L.pending ∧
       CoordinatorCollectionLedger.acceptUpCheck L i M = true ∧
       M.val.sigma = payload.sigma.val + 1 ∧ 0 < M.val.sigma ∧
       (ReferenceActiveAffinePositiveTest.upPositive x = true →
         AffineChannelLaw.affineHash ((x.row.2 x.time).2 (1, i)) w = 1)) := by
  classical
  dsimp only
  let E := ReferenceActivePhysicalHorizon.run initial rows J rewards start count span mode
  let current := E.records[k + 1]'(by
    rw [ReferenceActivePhysicalHorizon.run_record_count]; exact hk)
  let x := current.input
  intro hp hc hd next nextMemory hf ho hu hi
  change ReferenceActivePhysicalStep.upSenderIndex x = i at hi
  obtain ⟨s, memory, choice, choiceMemory, ledger, saved, hs, hchoice, _, hlast,
    hstatus, hreply, _, _, _, _, _⟩ := cutoff_after_down_reply_seed
      initial rows J rewards start count span mode k hk payload i hp hc hd next nextMemory hf ho
  change (ReferenceFollowerFixedReply.actualChoice current i).configuration =
    .ordinary choice choiceMemory at hchoice
  have hprep : ReferenceFollowerFixedReply.actualChoice current i = DeclaredFollowerLocalRound.prepare
      rate i x.row (x.state.activations i) x.time (x.active i) (x.state.followers i) :=
    current.output.preparation.followers.followers_eq i
  have hspec := ReferenceUpPhysicalHashRule.prepare_arm_spec i x.row
    (x.state.activations i) x.time (x.active i) (x.state.followers i)
  simp only [← hprep, hchoice] at hspec
  have hselected : ActiveFollowerQueueOperation.selectedUpRound i x.row
      (x.state.activations i) x.time ∧ choice.status = .unoccupied :=
    ⟨⟨x.active i, hu, hi⟩, hstatus⟩
  cases hoff : ActiveFollowerQueueOperation.checkedUpOffer rate.eta i x.row
      (x.state.activations i) x.time choice with
  | failure => simp only [hoff] at hspec
  | noOffer =>
      unfold ActiveFollowerQueueOperation.checkedUpOffer at hoff
      split at hoff <;> try contradiction
      split at hoff <;> contradiction
  | offer M =>
    have hfields := ActiveFollowerQueueOperation.checkedUpOffer_fields rate.eta i x.row
      (x.state.activations i) x.time choice M hoff
    have hpairs := hreply
    simp only [ReferenceFollowerReplyChronology.reply, Prod.mk.injEq] at hpairs
    have hstart := ReferenceFollowerReplyChronology.acceptedStart_eq_of_reply_eq hreply
    have hM : M.val = ActiveFollowerQueueOperation.upOfferFields s := by
      rw [hfields, ActiveFollowerQueueOperation.upOfferFields, hstart,
        hpairs.2.1, hpairs.2.2.1, hpairs.2.2.2]
      rfl
    have hconfiguration : ((ReferenceActivePhysicalStep.prepare x).followers.followers i).configuration =
        .ordinary choice choiceMemory := by
      have hactual := hchoice
      change (current.output.preparation.followers.followers i).configuration =
        .ordinary choice choiceMemory at hactual
      have heq : current.output.preparation = ReferenceActivePhysicalStep.prepare x := by
        rw [current.output_eq]; rfl
      rw [heq] at hactual
      exact hactual
    have hsent : ReferenceActiveAffinePositiveTest.upSent x =
        some (ActiveFollowerArmChoice.offeredUpWord rate.eta M) := by
      rw [ReferenceUpPhysicalHashRule.upSent_eq_configuration, hi, hconfiguration]
      simp only [hoff]
      rfl
    have hparse : CoordinatorUpReception.parseDecoderOutput (p := p) (eta := rate.eta.val)
        (some (ActiveFollowerArmChoice.offeredUpWord rate.eta M)) = some M := by
      change OrdinaryMessageCodec.parseUp (ReferencePrelaunchFollower.codecParams p rate.eta)
        (some ((OrdinaryMessageCodec.wordEquivFlat (ReferencePrelaunchFollower.codecParams p rate.eta)).symm
          ((OrdinaryMessageCodec.wordEquivFlat (ReferencePrelaunchFollower.codecParams p rate.eta))
            (OrdinaryMessageCodec.encodeUp (ReferencePrelaunchFollower.codecParams p rate.eta) M)))) = some M
      rw [Equiv.symm_apply_apply]
      exact OrdinaryMessageCodec.parseUp_encode _ M
    obtain ⟨d, L, hdiag, hexpected, hsite, hcheck, hinput, hsigma, hcutoff, hcursor, hpending⟩ :=
      cutoff_call current payload hp hc ho
    have hMsigma : M.val.sigma = payload.sigma.val + 1 := by
      rw [hM, ActiveFollowerQueueOperation.upOfferFields, ReferencePrelaunchFollower.acceptedStart, hlast]
      exact congrArg OrdinaryMessageCodec.DownFields.sigma (payload.downRecord_fields i)
    have hmember : i ∈ L.pending := by rw [hpending]; exact Finset.mem_univ i
    have haccept : CoordinatorCollectionLedger.acceptUpCheck L i M = true := by
      simp only [CoordinatorCollectionLedger.acceptUpCheck, hcutoff, hcursor, le_refl,
        decide_true, hmember, hMsigma, hsigma, Bool.and_self]
    refine ⟨s, memory, choice, choiceMemory, M, d, L, hs, hchoice, hlast, hstatus, hreply,
      hM, hoff, hsent, hsent, hparse, hdiag, hexpected.trans hsent, hsite, hcheck, hinput,
      hsigma, hcutoff, hcursor, hmember, haccept, hMsigma, by rw [hMsigma]; omega, ?_⟩
    intro hpositive
    have hh := ReferenceUpPhysicalHashRule.upPositive_hash_one x _ hsent hpositive
    rw [hi] at hh
    exact hh

end Run

end Bandits.Support.ReferenceCutoffUpOfferConstruction

end
