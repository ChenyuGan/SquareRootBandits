/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionEpochAlignment

/-!
# Actual first-collection chosen context

This module transports the checked cutoff initializer's collection context
along the original connected physical prefix and identifies every selected
choice in the literal first collection window.  Failed and dagger records stay
in that window; only an actual selected choice is concluded about.

Mathematical sources: `sources/zip4/manuscript/06_interruptions.tex:9-100,
246-295`, `sources/zip4/manuscript/04_slow_fast_learner.tex:157-174`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-64`.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceInitializationRun
open Bandits.Support.ActualReferenceInitializationBlock
open Bandits.Support.ReferenceFirstLiveConfirmationHistory
open Bandits.Support.ReferenceCollectionSegmentExtraction
open Bandits.Support.ReferenceCollectionPhaseHistory
open Bandits.Support.CollectionBufferProvenance
open Bandits.Support.ReferenceFirstCollectionEpochAlignment

namespace Bandits.Support.ReferenceFirstCollectionChosenContext

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput

variable {p : Parameters}

private theorem choice_none_of_dagger (rate : RateInput p)
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (hdagger : x.state.coordinator = .dagger) :
    ReferenceCollectionSegmentExtraction.choice x = none := by
  simp [ReferenceCollectionSegmentExtraction.choice, ReferenceActivePhysicalStep.prepare,
    ReferenceActivePhysicalStep.dispatch_dagger x hdagger,
    ReferenceActivePhysicalStep.DispatchCut.selection]

private theorem collectionChoice_congruent {rate : RateInput p}
    {x y : ReferenceActivePhysicalStep.RoundInput p rate} (hxy : x = y) :
    ReferenceCollectionSegmentExtraction.choice x =
      ReferenceCollectionSegmentExtraction.choice y := by
  cases hxy
  rfl

/-- In a carried collection state, an unselected non-later-choice step is an
actual failure.  The continuing constructor is selected; the later-choice
constructor is excluded by the literal window predicate; all remaining
dispatch constructors use the protocol's absorbing failure branch. -/
private theorem collection_choice_none_dagger (rate : RateInput p)
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (proposal : Option (Fin p.T × Bool))
    (hstate : x.state.coordinator = .collection payload ledger proposal)
    (hnotLater : ReferenceCollectionPhaseHistory.laterChosen x = false)
    (hchoice : ReferenceCollectionSegmentExtraction.choice x = none) :
    (ReferenceActivePhysicalStep.step x).next.coordinator = .dagger := by
  classical
  change (ReferenceActivePhysicalStep.prepare x).observeCoordinator.configuration = .dagger
  by_cases hcutoff : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
  · let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
    let clock := ReferenceActivePhysicalStep.collectionClock payload ledger proposal cutoff
    let input := ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff
    have hprepared : (ReferenceActivePhysicalStep.prepare x).coordinator =
        .collection payload ledger clock cutoff
          (CoordinatorRoundDispatch.dispatchCollection input) := by
      simp [ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch,
        CoordinatorRoundDispatch.dispatch, hstate, hcutoff, cutoff, clock, input]
      rfl
    cases hdispatch : CoordinatorRoundDispatch.dispatchCollection input <;>
      simp_all [ReferenceCollectionSegmentExtraction.choice,
        ReferenceCollectionSegmentExtraction.choiceOfCut,
        ReferenceCollectionPhaseHistory.laterChosen,
        ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
        ReferenceActivePhysicalStep.DispatchCut.selection,
        ReferenceActivePhysicalStep.coordinatorFailure]
  · have hprepared : (ReferenceActivePhysicalStep.prepare x).coordinator =
        .invalidCollectionCutoff := by
      simp [ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch,
        hstate, hcutoff]
    simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
      hprepared, ReferenceActivePhysicalStep.DispatchCut.selection,
      ReferenceActivePhysicalStep.coordinatorFailure]

/-- The selected choice at an incoming collection state is the actual carried
payload and ledger.  The payload identity is recovered from the literal
dispatch projection; it is not supplied as a history premise. -/
private theorem choice_collection_payload_pre (rate : RateInput p)
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (proposal : Option (Fin p.T × Bool))
    (c : ReferenceCollectionSegmentExtraction.Choice rate)
    (hstate : x.state.coordinator = .collection payload ledger proposal)
    (hchoice : ReferenceCollectionSegmentExtraction.choice x = some c) :
    c.payload = payload ∧ c.preLedger = ledger := by
  have hpre := ReferenceCollectionSegmentExtraction.choice_collection_pre
    x payload ledger proposal c hstate hchoice
  have hvalid : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T := by
    by_contra hbad
    have hnone : ReferenceCollectionSegmentExtraction.choice x = none := by
      simp [ReferenceCollectionSegmentExtraction.choice,
        ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch,
        hstate, hbad, ReferenceActivePhysicalStep.DispatchCut.selection]
    rw [hnone] at hchoice
    contradiction
  let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
  let clock := ReferenceActivePhysicalStep.collectionClock payload ledger proposal cutoff
  let input := ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff
  have hdispatch : ReferenceActivePhysicalStep.dispatch x =
      .collection payload ledger clock cutoff
        (CoordinatorRoundDispatch.dispatchCollection input) := by
    simp [ReferenceActivePhysicalStep.dispatch, CoordinatorRoundDispatch.dispatch,
      hstate, hvalid, cutoff, clock, input]
    rfl
  have hpayload : c.payload = payload := by
    have hc := hchoice
    cases hround : CoordinatorRoundDispatch.dispatchCollection input with
    | continuing core snapshot boundary scores =>
        have heq :
            ({ payload := payload, preLedger := ledger,
                started := snapshot.clockStarted,
                weights := CoordinatorCollectionInteractive.PreObservationInputs.weights
                  input snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq,
                initializer := none } : ReferenceCollectionSegmentExtraction.Choice rate) = c := by
          simpa [ReferenceCollectionSegmentExtraction.choice,
            ReferenceActivePhysicalStep.prepare, hdispatch, hround,
            ReferenceActivePhysicalStep.DispatchCut.selection,
            ReferenceCollectionSegmentExtraction.choiceOfCut,
            cutoff, clock, input] using hc
        exact (congrArg ReferenceCollectionSegmentExtraction.Choice.payload heq).symm
    | _ => simp [ReferenceCollectionSegmentExtraction.choice,
        ReferenceActivePhysicalStep.prepare, hdispatch, hround,
        ReferenceActivePhysicalStep.DispatchCut.selection,
        ReferenceCollectionSegmentExtraction.choiceOfCut,
        cutoff, clock, input] at hc
  exact ⟨hpayload, hpre.1⟩

/-- Splitting a connected run at a literal list boundary retains the actual
intermediate state. -/
private theorem connected_append_split {rate : RateInput p}
    {initial final : ReferenceActivePhysicalStep.State p rate}
    (left right : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (hchain : ReferenceActivePhysicalHorizon.Connected initial (left ++ right) final) :
    ∃ middle,
      ReferenceActivePhysicalHorizon.Connected initial left middle ∧
      ReferenceActivePhysicalHorizon.Connected middle right final := by
  induction left generalizing initial with
  | nil => exact ⟨initial, rfl, hchain⟩
  | cons record rest ih =>
      simp only [List.cons_append,
        ReferenceActivePhysicalHorizon.Connected] at hchain
      obtain ⟨middle, hleft, hright⟩ := ih hchain.2
      exact ⟨middle, ⟨hchain.1, hleft⟩, hright⟩

private theorem roundInput_getElem_eq_tail
    {rate : RateInput p}
    {whole tail : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))}
    {head : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)}
    (hwhole : whole = head :: tail) (n : Fin whole.length) (hn : n.val ≠ 0) :
    ∃ j : Fin tail.length, whole[n].input = tail[j.val].input := by
  have hnlt : n.val < tail.length + 1 := by
    simpa [hwhole] using n.isLt
  let j : Fin tail.length := ⟨n.val - 1, by omega⟩
  have hj : j.val + 1 = n.val := by
    simp only [j]
    omega
  have hlookup : whole[n.val]? = some tail[j.val] := by
    calc
      whole[n.val]? = (head :: tail)[n.val]? :=
        congrArg (fun xs : List (ReferenceActivePhysicalHorizon.RoundRecord
          (p := p) (rate := rate)) => xs[n.val]?) hwhole
      _ = some tail[j.val] := by
        calc
          (head :: tail)[n.val]? = (head :: tail)[j.val + 1]? :=
            congrArg (fun k : ℕ => (head :: tail)[k]?) hj.symm
          _ = some tail[j.val] := by simp
  have hget : whole[n.val]? = some whole[n] := by simp [n.isLt]
  have hrecord : whole[n] = tail[j.val] := Option.some.inj (hget.symm.trans hlookup)
  exact ⟨j, congrArg (fun record : ReferenceActivePhysicalHorizon.RoundRecord
    (p := p) (rate := rate) => record.input) hrecord⟩

/-- Along a genuine connected collection prefix containing no later choice,
every selected ordinary input has the same payload and literal receiver-local
context. A missing choice enters dagger, whose absorption excludes any later
selected input in this prefix. -/
private theorem connected_collection_choices_context
    (rate : RateInput p)
    (initializer : ReferenceCollectionSegmentExtraction.Initializer p)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (initial final : ReferenceActivePhysicalStep.State p rate)
    (hchain : ReferenceActivePhysicalHorizon.Connected initial records final)
    (hcontext : ∃ ledger proposal,
      initial.coordinator = .collection payload ledger proposal ∧
      CollectionBufferProvenance.collectionContext ledger =
        (initializer.assignment, initializer.sigma, initializer.cutoff,
          initializer.freezeAt, initializer.base))
    (hnoLater : ∀ record ∈ records,
      ReferenceCollectionPhaseHistory.laterChosen record.input = false) :
    ∀ record ∈ records, ∀ c : ReferenceCollectionSegmentExtraction.Choice rate,
      ReferenceCollectionSegmentExtraction.choice record.input = some c →
        c.payload = payload ∧
        CollectionBufferProvenance.collectionContext c.preLedger =
          (initializer.assignment, initializer.sigma, initializer.cutoff,
            initializer.freezeAt, initializer.base) := by
  induction records generalizing initial final with
  | nil => intro record hmem; simp at hmem
  | cons record rest ih =>
      rcases hchain with ⟨hpre, hrest⟩
      rcases hcontext with ⟨ledger, proposal, hcoord, hledgerContext⟩
      have hstate : record.input.state.coordinator = .collection payload ledger proposal := by
        rw [hpre]
        exact hcoord
      have hnoLaterHead := hnoLater record (by simp)
      cases hchoice : ReferenceCollectionSegmentExtraction.choice record.input with
      | none =>
          have hdagger := collection_choice_none_dagger rate record.input payload ledger proposal
            hstate hnoLaterHead hchoice
          have hdaggerOut : record.output.next.coordinator = .dagger := by
            calc
              record.output.next.coordinator =
                  (ReferenceActivePhysicalStep.step record.input).next.coordinator := by
                rw [record.output_eq]
              _ = .dagger := hdagger
          have hdaggerTail :=
            ReferenceActivePhysicalHorizon.Connected.coordinator_dagger hrest hdaggerOut
          intro current hmem c hc
          rcases List.mem_cons.mp hmem with heq | htail
          · subst current
            simp [hchoice] at hc
          · have hcurrentDagger := hdaggerTail.2 current htail
            have hcurrentNone := choice_none_of_dagger rate current.input hcurrentDagger
            rw [hcurrentNone] at hc
            contradiction
      | some c =>
          have hpayloadPre := choice_collection_payload_pre rate record.input payload ledger
            proposal c hstate hchoice
          have hchoiceContext :
              CollectionBufferProvenance.collectionContext c.preLedger =
                (initializer.assignment, initializer.sigma, initializer.cutoff,
                  initializer.freezeAt, initializer.base) := by
            rw [hpayloadPre.2]
            exact hledgerContext
          have hstep := ReferenceFirstCollectionEpochAlignment.actual_chosen_step_context
            rate record.input c initializer hchoice hchoiceContext
          intro current hmem d hd
          rcases List.mem_cons.mp hmem with heq | htail
          · subst current
            have hdc : d = c := Option.some.inj (hd.symm.trans hchoice)
            subst d
            exact ⟨hpayloadPre.1, hchoiceContext⟩
          · rcases hstep with hdagger | ⟨nextLedger, nextProposal, completed,
                hnext, hnextContext, _, _, _⟩
            · have hdaggerTail :=
                ReferenceActivePhysicalHorizon.Connected.coordinator_dagger hrest
                  (by rw [record.output_eq]; exact hdagger)
              have hcurrentDagger := hdaggerTail.2 current htail
              have hcurrentNone := choice_none_of_dagger rate current.input hcurrentDagger
              rw [hcurrentNone] at hd
              contradiction
            · have hnextCoord : record.output.next.coordinator =
                  .collection payload nextLedger nextProposal := by
                calc
                  record.output.next.coordinator =
                      (ReferenceActivePhysicalStep.step record.input).next.coordinator := by
                    rw [record.output_eq]
                  _ = .collection payload nextLedger nextProposal := by
                    simpa only [hpayloadPre.1] using hnext
              apply ih record.output.next final hrest
                ⟨nextLedger, nextProposal, hnextCoord, hnextContext⟩
                (fun current hm => hnoLater current (List.mem_cons_of_mem record hm))
                current htail d hd

/-- The actual first-cutoff selected choice seeds the same checked
initializer context at every selected physical input in the literal window.
The current input is restricted only by its actual `choice = some c` branch;
no current completed extraction or operation-success fact is assumed.
-/
theorem actual_first_collection_chosen_context (rate : RateInput p)
    (source : SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (count : ℕ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed + count ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count hspan).records).length < count) :
    let start := ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
    let execution := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
      rate source rewards C_star C_h hcross count hspan
    let firstWindow := ReferenceFirstLiveConfirmationHistory.firstLiveWindow execution.records
    let w := firstWindow.length
    let W := ReferenceCollectionPhaseHistory.collectionWindow execution.records w
    ∀ (n : Fin W.length) (c : ReferenceCollectionSegmentExtraction.Choice rate),
      ReferenceCollectionSegmentExtraction.choice W[n].input = some c →
      ∃ (cut : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
          (suffix : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
          (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
          (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
          (base : Fin (p.m - 1) → ℕ)
          (c0 : ReferenceCollectionSegmentExtraction.Choice rate)
          (initializer : ReferenceCollectionSegmentExtraction.Initializer p)
          (seg : ReferenceCollectionSegmentExtraction.Segment rate),
        execution.records = firstWindow ++ cut :: suffix ∧
        cut.input.time.val = start + w ∧
        c0.payload = r.payload ∧
        initializer = ReferenceCollectionSegmentExtraction.cutoffInitializer
          (ReferenceActivePhysicalStep.liveInput cut.input r q base).registers
          (ReferenceActivePhysicalStep.liveInput cut.input r q base).ownedRegisters base
          (ReferenceActivePhysicalStep.liveInput cut.input r q base).registers.time ∧
        ReferenceCollectionSegmentExtraction.segmentAt execution.records w = some seg ∧
        seg.entry = cut ∧ seg.context = c0 ∧
        ReferenceCollectionSegmentExtraction.choice cut.input = some c0 ∧
        c0.initializer = some initializer ∧
        initializer.checkedStart rate = .success c0.preLedger ∧
        initializer.sigma = start + 1 ∧
        initializer.cutoff = start + w + 1 ∧
        initializer.freezeAt = r.gridBoundary ∧
        initializer.freezeAt = FollowerCutoffScan.gridBoundary p rate.eta.val c0.payload.sigma ∧
        initializer.base = (fun _ => 0) ∧
        initializer.assignment.arm = r.payload.assignment.assigned ∧
        initializer.assignment.arm = c0.payload.assignment.assigned ∧
        0 < w ∧
        c.payload = c0.payload ∧
        CollectionBufferProvenance.collectionContext c.preLedger =
          (initializer.assignment, initializer.sigma, initializer.cutoff,
            initializer.freezeAt, initializer.base) ∧
        W[n].input.time.val = start + w + n.val := by
  let start := ReferenceInitializationRun.elapsed p
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
  let execution := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
    rate source rewards C_star C_h hcross count hspan
  let firstWindow := ReferenceFirstLiveConfirmationHistory.firstLiveWindow execution.records
  let w := firstWindow.length
  let W := ReferenceCollectionPhaseHistory.collectionWindow execution.records w
  change ∀ (n : Fin W.length) (c : ReferenceCollectionSegmentExtraction.Choice rate),
    ReferenceCollectionSegmentExtraction.choice W[n].input = some c →
      ∃ (cut : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
          (suffix : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
          (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
          (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
          (base : Fin (p.m - 1) → ℕ)
          (c0 : ReferenceCollectionSegmentExtraction.Choice rate)
          (initializer : ReferenceCollectionSegmentExtraction.Initializer p)
          (seg : ReferenceCollectionSegmentExtraction.Segment rate),
        execution.records = firstWindow ++ cut :: suffix ∧
        cut.input.time.val = start + w ∧
        c0.payload = r.payload ∧
        initializer = ReferenceCollectionSegmentExtraction.cutoffInitializer
          (ReferenceActivePhysicalStep.liveInput cut.input r q base).registers
          (ReferenceActivePhysicalStep.liveInput cut.input r q base).ownedRegisters base
          (ReferenceActivePhysicalStep.liveInput cut.input r q base).registers.time ∧
        ReferenceCollectionSegmentExtraction.segmentAt execution.records w = some seg ∧
        seg.entry = cut ∧ seg.context = c0 ∧
        ReferenceCollectionSegmentExtraction.choice cut.input = some c0 ∧
        c0.initializer = some initializer ∧
        initializer.checkedStart rate = .success c0.preLedger ∧
        initializer.sigma = start + 1 ∧
        initializer.cutoff = start + w + 1 ∧
        initializer.freezeAt = r.gridBoundary ∧
        initializer.freezeAt = FollowerCutoffScan.gridBoundary p rate.eta.val c0.payload.sigma ∧
        initializer.base = (fun _ => 0) ∧
        initializer.assignment.arm = r.payload.assignment.assigned ∧
        initializer.assignment.arm = c0.payload.assignment.assigned ∧
        0 < w ∧
        c.payload = c0.payload ∧
        CollectionBufferProvenance.collectionContext c.preLedger =
          (initializer.assignment, initializer.sigma, initializer.cutoff,
            initializer.freezeAt, initializer.base) ∧
        W[n].input.time.val = start + w + n.val
  intro n c hchoice
  rcases ReferenceFirstCollectionEpochAlignment.actual_first_collection_segment
      rate source rewards C_star C_h count hcross hspan hshort with
    ⟨cut, suffix, r, q, base, c0, initializer, seg, hsplit, htime, hcutChoice,
      hcutPayload, hinitializer, hc0init, hsigma, hcutoff, hfreeze, hfreezeGrid,
      hbase, hassignment, hchecked, hwpos, hsourceEnd, hgridLower, hgridUpper,
      hfirstCutoff, hsegmentAt, hentry, hsegmentChoice, hrecords, hremaining,
      hpartition, hwindow⟩
  have hpreFields := CollectionBufferProvenance.startCollectionChecked_success_context
    initializer.assignment initializer.sigma initializer.cutoff initializer.freezeAt
    initializer.base initializer.outside c0.preLedger (by
      simpa [ReferenceCollectionSegmentExtraction.Initializer.checkedStart] using hchecked)
  have hcutContext :
      CollectionBufferProvenance.collectionContext c0.preLedger =
        (initializer.assignment, initializer.sigma, initializer.cutoff,
          initializer.freezeAt, initializer.base) := by
    simp [CollectionBufferProvenance.collectionContext, hpreFields.1,
      hpreFields.2.1, hpreFields.2.2.2.1,
      hpreFields.2.2.2.2.1, hpreFields.2.2.2.2.2]
  have htimeWindow := ReferenceFirstCollectionEpochAlignment.actual_first_collection_window_time
    rate source rewards C_star C_h count hcross hspan hshort n
  have htimeIndex : W[n].input.time.val = start + w + n.val := by
    have htimePlus : W[n].input.time.val + 1 = start + w + 1 + n.val := by
      simpa [W, w, firstWindow, execution, start] using htimeWindow.2
    omega
  have hfreezeGridC0 : initializer.freezeAt =
      FollowerCutoffScan.gridBoundary p rate.eta.val c0.payload.sigma := by
    rw [hcutPayload]
    exact hfreezeGrid
  have hassignmentC0 : initializer.assignment.arm = c0.payload.assignment.assigned := by
    rw [hcutPayload]
    exact hassignment
  by_cases hn : n.val = 0
  · have hcurrentCut : W[n] = cut := by
      have hlookup : W[n.val]? = some cut := by
        change (ReferenceCollectionPhaseHistory.collectionWindow execution.records w)[n.val]? = some cut
        rw [hwindow]
        simp [hn]
      have hget : W[n.val]? = some W[n] := by simp [n.isLt]
      rw [hget] at hlookup
      exact Option.some.inj hlookup
    have hc0 : c = c0 := by
      apply Option.some.inj
      calc
        some c = ReferenceCollectionSegmentExtraction.choice W[n].input := hchoice.symm
        _ = ReferenceCollectionSegmentExtraction.choice cut.input := by rw [hcurrentCut]
        _ = some c0 := hcutChoice
    subst c
    refine ⟨cut, suffix, r, q, base, c0, initializer, seg, hsplit, htime,
      hcutPayload, hinitializer, hsegmentAt, hentry, hsegmentChoice, hcutChoice, hc0init, hchecked,
      hsigma, hcutoff, hfreeze, hfreezeGridC0, hbase, hassignment, hassignmentC0, hwpos, rfl, hcutContext,
      htimeIndex⟩
  · let during := suffix.takeWhile
      (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input)
    have hwindowShape : W = cut :: during := by
      simpa [W, during] using hwindow
    have hfull : ReferenceActivePhysicalHorizon.Connected
        (ReferenceFirstCollectionEpochAlignment.actualLaunchState rate source rewards C_star C_h hcross)
        execution.records execution.finalState := by
      simpa [execution, ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun] using
        ReferenceActivePhysicalHorizon.run_connected
          (ReferenceFirstCollectionEpochAlignment.actualLaunchState rate source rewards C_star C_h hcross)
          source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
          start count hspan
          (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
            rate source rewards C_star C_h hcross).1
    have hsplitChain : ReferenceActivePhysicalHorizon.Connected
        (ReferenceFirstCollectionEpochAlignment.actualLaunchState rate source rewards C_star C_h hcross)
        (firstWindow ++ (cut :: suffix)) execution.finalState := by
      rw [← hsplit]
      exact hfull
    obtain ⟨afterWindow, hfirstChain, hcutChain⟩ :=
      connected_append_split firstWindow (cut :: suffix) hsplitChain
    rcases hcutChain with ⟨hcutPre, hafterCut⟩
    have hcutOutput : ReferenceActivePhysicalHorizon.Connected
        cut.output.next suffix execution.finalState := hafterCut
    have hcutLocal := ReferenceFirstCollectionEpochAlignment.actual_chosen_step_context
      rate cut.input c0 initializer hcutChoice hcutContext
    let remainder := suffix.dropWhile
      (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input)
    have hsuffixSplit : suffix = during ++ remainder := by
      dsimp [during, remainder]
      exact List.takeWhile_append_dropWhile.symm
    rw [hsuffixSplit] at hcutOutput
    obtain ⟨afterDuring, hDuringChain, hafterDuring⟩ :=
      connected_append_split during remainder hcutOutput
    have hnoLater : ∀ record ∈ during,
        ReferenceCollectionPhaseHistory.laterChosen record.input = false := by
      intro record hmem
      have hall : (!ReferenceCollectionPhaseHistory.laterChosen record.input) = true :=
        (List.all_eq_true.mp List.all_takeWhile) record hmem
      cases hlater : ReferenceCollectionPhaseHistory.laterChosen record.input <;>
        simp [hlater] at hall ⊢
    have htimeCurrent : W[n].input.time.val = start + w + n.val := htimeIndex
    obtain ⟨j, hinputEq⟩ := roundInput_getElem_eq_tail hwindowShape n hn
    have hcurrentChoice :
        ReferenceCollectionSegmentExtraction.choice during[j.val].input = some c :=
      (collectionChoice_congruent hinputEq).symm.trans hchoice
    have hmemCurrent : during[j.val] ∈ during := List.getElem_mem j.isLt
    rcases hcutLocal with hdagger | ⟨ledger0, proposal0, _, hnext, hledgerContext,
      _, _, _⟩
    · have hdaggerOutput : cut.output.next.coordinator = .dagger := by
        rw [cut.output_eq]
        exact hdagger
      have hdaggerDuring :=
        ReferenceActivePhysicalHorizon.Connected.coordinator_dagger hDuringChain hdaggerOutput
      have hcurrentStateDagger : W[n].input.state.coordinator = .dagger := by
        calc
          W[n].input.state.coordinator = during[j.val].input.state.coordinator :=
            congrArg (fun x : ReferenceActivePhysicalStep.RoundInput p rate =>
              x.state.coordinator) hinputEq
          _ = .dagger := hdaggerDuring.2 during[j.val] hmemCurrent
      have hnone := choice_none_of_dagger rate W[n].input hcurrentStateDagger
      rw [hnone] at hchoice
      contradiction
    · have hnext' : cut.output.next.coordinator =
          .collection c0.payload ledger0 proposal0 := by
        calc
          cut.output.next.coordinator =
              (ReferenceActivePhysicalStep.step cut.input).next.coordinator := by
            rw [cut.output_eq]
          _ = .collection c0.payload ledger0 proposal0 := hnext
      have hchosenAll := connected_collection_choices_context rate initializer c0.payload
        during cut.output.next afterDuring hDuringChain
        ⟨ledger0, proposal0, hnext', hledgerContext⟩ hnoLater
      obtain ⟨hpayloadCurrent, hcontextCurrent⟩ :=
        hchosenAll during[j.val] hmemCurrent c hcurrentChoice
      refine ⟨cut, suffix, r, q, base, c0, initializer, seg, hsplit, htime,
        hcutPayload, hinitializer, hsegmentAt, hentry, hsegmentChoice, hcutChoice, hc0init, hchecked,
        hsigma, hcutoff, hfreeze, hfreezeGridC0, hbase, hassignment, hassignmentC0, hwpos,
        hpayloadCurrent, hcontextCurrent, htimeCurrent⟩

end Bandits.Support.ReferenceFirstCollectionChosenContext

end
