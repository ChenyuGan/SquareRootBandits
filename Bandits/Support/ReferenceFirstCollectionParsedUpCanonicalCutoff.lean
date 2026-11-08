/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionRejectedReadyStep
public import Bandits.Support.ReferenceFirstCollectionCanonicalArrivalSource

import Lean.Elab.Tactic.Omega

/-!
# Parsed first-collection UP fields at the canonical live cutoff

Sources: `sources/zip4/manuscript/06_interruptions.tex:16-100,246-299,391-408`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-79`, and
`sources/zip4/manuscript/04_slow_fast_learner.tex:157-174`.

For an actual first-collection input, a successful filtered UP parse and local
acceptance query identify sender fields that replay the original launch's live
queue cells through the first cutoff.  The proof preserves the retained DOWN
record and distinguishes the early-reply and late-recovery paths.  It does not
assert that the current receiver or FINISH succeeds.
-/

@[expose] public section

noncomputable section

open Bandits.Support

namespace Bandits.Support.ReferenceFirstCollectionParsedUpCanonicalCutoff

variable {p : ConstructorDimensions.Parameters}

/-- The actual parse and acceptance query supplies its retained sender and
the whole first-assignment payload that generated its DOWN record. -/
private theorem actual_first_collection_parsed_up_payload_source
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
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
    let init := ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate
    let I := ReferenceInitializationRun.output init
    let s := ReferenceInitializationRun.elapsed p I.completed
    let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
      rate source rewards C_star C_h hcross count hspan
    let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records
    let w := W.length
    let B := ReferenceCollectionPhaseHistory.collectionWindow E.records w
    ∀ (n : Fin B.length) (c : ReferenceCollectionSegmentExtraction.Choice rate),
      ReferenceCollectionSegmentExtraction.choice B[n].input = some c →
      let x := B[n].input
      let i := ReferenceActivePhysicalStep.upSenderIndex x
      let candidate := CoordinatorCollectionLedger.startRoundCandidate c.preLedger x.time
        (ReferenceActivePhysicalStep.collectionEnabled c.preLedger x.time)
        (ReferenceCollectionRawBufferHistory.rawDiagnostic B[n])
      ∀ (M : OrdinaryMessageCodec.UpRecord
        (CoordinatorCollectionLedger.codecParams p rate.eta.val)),
        ReferenceCollectionSegmentExtraction.effectiveParse x candidate = some M →
        CoordinatorCollectionLedger.acceptUpCheck candidate i M = true →
        ∃ (P0 : ReferenceActivePhysicalStep.Payload rate)
          (birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
          (d : Fin E.records.length)
          (message : ReferenceFirstAcceptedUpNumericSnapshot.DownRecord (p := p) (rate := rate)),
          birth ∈ E.records ∧
          ReferenceAssignmentPayloadPersistence.InstallationBirth birth P0 ∧
          birth.input.time.val = s ∧
          P0 = c.payload ∧
          message = P0.downRecord i ∧
          message.val.q = 0 ∧
          ReferenceAcceptedUpFollowerHistory.RetainedDown E.records[d.val] i message ∧
          d.val < w + n.val ∧
          M.val.sigma = s + 1 ∧
          M.val.S = (QueueReplay.replay (4 * rate.n) (0, 0)
            (ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords
              E.records i d.val message w)).1 ∧
          M.val.q = (QueueReplay.replay (4 * rate.n) (0, 0)
            (ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords
              E.records i d.val message w)).2 ∧
          M.val.delta =
            (QueueReplay.replay (4 * rate.n) (0, 0)
              (ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords
                E.records i d.val message w)).1 -
            (QueueReplay.replay (4 * rate.n) (0, 0)
              (ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords
                E.records i d.val message (w - 1))).1 ∧
          c.preLedger.assignment.arm i = c.payload.assignment.assigned i := by
  classical
  let init := ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate
  let boot := ReferenceInitializationRun.output init
  let s := ReferenceInitializationRun.elapsed p boot.completed
  let I := ReferenceFirstCollectionEpochAlignment.actualLaunchState
    rate source rewards C_star C_h hcross
  let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
    rate source rewards C_star C_h hcross count hspan
  let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records
  let w := W.length
  let B := ReferenceCollectionPhaseHistory.collectionWindow E.records w
  let u := s + w + 1
  let cells := ReferenceFirstWindowNumericalStream.actualLiveSourceCells
    rate source rewards C_star C_h hcross count hspan
  let qpar := ReferenceFirstLaunchNumericalCell.queueParameters rate
  change ∀ (n : Fin B.length) (c : ReferenceCollectionSegmentExtraction.Choice rate),
    ReferenceCollectionSegmentExtraction.choice B[n].input = some c → _
  intro n c hchoice
  dsimp only
  let x := B[n].input
  let i := ReferenceActivePhysicalStep.upSenderIndex x
  let a := c.preLedger.assignment.arm i
  let candidate := CoordinatorCollectionLedger.startRoundCandidate c.preLedger x.time
    (ReferenceActivePhysicalStep.collectionEnabled c.preLedger x.time)
    (ReferenceCollectionRawBufferHistory.rawDiagnostic B[n])
  let A := fun X : List (RecordedQueueRun.RoundInput p.K) =>
    X.map (fun z => (z.enabled, RecordedQueueRun.quantizedArrival qpar z a))
  let V := fun h => QueueReplay.replay (4 * rate.n) (0, 0) (A (cells.take h))
  intro M hparse haccept

  let initial := ReferenceFirstCollectionEpochAlignment.actualLaunchState
    rate source rewards C_star C_h hcross
  let rows := source.1.2
  let J := ActualInitializationPhysicalStep.selectedRowIndex p source
  let liveRun := ReferenceFirstWindowNumericalStream.actualFirstLiveRun
    rate source rewards C_star C_h hcross count hspan
  let liveWindow := ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
    rate source rewards C_star C_h hcross count hspan
  let cellAt := ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
    rate source rewards C_star C_h hcross count hspan
  let seed := ReferenceInitializationRun.ordinary init boot
    (ActualReferenceInitializationBlock.refFollower i)
  let seedMemory := ActiveFollowerLifecycle.initialMemory p

  have hlaunchSeed := ReferenceFirstLaunchNumericalCell.actual_launch_seed
    rate source rewards C_star C_h hcross
  rcases hlaunchSeed with ⟨_, hmodeSource, _, hfirstSource, _, _, _, hseedFollowersSource⟩
  have hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial s := by
    simpa [initial, ReferenceFirstCollectionEpochAlignment.actualLaunchState,
      ReferenceFirstLaunchNumericalCell.launchState] using hmodeSource
  have hfirst : initial.coordinator = .first := by
    simpa [initial, ReferenceFirstCollectionEpochAlignment.actualLaunchState,
      ReferenceFirstLaunchNumericalCell.launchState] using hfirstSource
  have hLiveRunEq : liveRun = E := by
    rfl
  have hLiveWindowEq : liveWindow = W := by
    simp [liveWindow, ReferenceFirstWindowNumericalStream.actualFirstLiveWindow,
      ReferenceFirstWindowNumericalStream.actualFirstLiveRun, E, W,
      ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun,
      ReferenceFirstCollectionEpochAlignment.actualLaunchState,
      ReferenceFirstLaunchNumericalCell.launchState]
  have hLiveWindowLength : liveWindow.length = w := by
    simp [W, w, hLiveWindowEq]
  have hshortLive : liveWindow.length < count := by
    simpa [liveWindow, liveRun, ReferenceFirstWindowNumericalStream.actualFirstLiveWindow,
      ReferenceFirstWindowNumericalStream.actualFirstLiveRun, E,
      ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun,
      ReferenceFirstCollectionEpochAlignment.actualLaunchState,
      ReferenceFirstLaunchNumericalCell.launchState] using hshort

  have hOrigin := ReferenceFirstCollectionDownPayloadOrigin.actual_first_collection_down_payload_origin
    rate source rewards C_star C_h count hcross hspan hshort
  rcases hOrigin.origin with
    ⟨originCut, originPayload, originBirth, originRegisters, originOwned, originBase,
      horiginIndex, horiginUnique, horiginState, _horiginCutoff, horiginPayload,
      _horiginSigma, _horiginQueues, _horiginFirstCutoff, horiginBirthMember,
      horiginBirthInstall, horiginBirthTime, _horiginBirthFirst, horiginWindowLookup,
      _horiginSelectedPayload, horiginPrior⟩

  have hCutoffSource := ReferenceFirstCutoffNumericalSource.actual_first_cutoff_numerical_source
    rate source rewards C_star C_h hcross count hspan hshortLive
  rcases hCutoffSource with
    ⟨cut, suffix, registers, owned, base, hcutIndex, hrecordsCut, hcutTime,
      hcutRows, hcutSelected, hcutRewards, hcutState, hcutSigma, hcutQueues,
      hdispatchData⟩
  rcases hdispatchData with
    ⟨dispatched, hstart, ledger, hinit, hcand, hdomain, hclock, hpending,
      hnoAssignment, selected, hdispatch, hdispatchTail⟩
  rcases hdispatchTail with
    ⟨hu, huT, huGrid, hledgerSigma, hledgerCutoff, hfollowersTail⟩
  rcases hfollowersTail with
    ⟨hcutFollowers, hkPositive, hpreparedFollowers, hcutFollowerTail⟩
  rcases hcutFollowerTail with
    ⟨hcutFollower, hcellPayload, _hcollectionRecorder⟩
  have hrecordsCutLive : liveRun.records = liveWindow ++ cut :: suffix := by
    simpa [liveRun, liveWindow,
      ReferenceFirstWindowNumericalStream.actualFirstLiveRun,
      ReferenceFirstWindowNumericalStream.actualFirstLiveWindow] using hrecordsCut
  have hrecordsCutE : E.records = W ++ cut :: suffix := by
    simpa only [hLiveRunEq, hLiveWindowEq] using hrecordsCutLive
  have hcutEqOrigin : cut = originCut := horiginUnique cut suffix hrecordsCutE

  have hcoordEq : cut.input.state.coordinator = originCut.input.state.coordinator :=
    congrArg (fun r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) =>
      r.input.state.coordinator) hcutEqOrigin
  have hregistersEq : registers = originRegisters := by
    have hlive :
        (ReferenceActivePhysicalStep.CoordinatorConfiguration.live registers owned base) =
          .live originRegisters originOwned originBase := by
      exact hcutState.symm.trans (hcoordEq.trans horiginState)
    injection hlive with hregisters
  have hsourcePayload : registers.payload = originPayload := by
    rw [hregistersEq, horiginPayload]

  have hSegment := ReferenceFirstCollectionEpochAlignment.actual_first_collection_segment
    rate source rewards C_star C_h count hcross hspan hshort
  rcases hSegment with
    ⟨segmentCut, segmentSuffix, segmentRegisters, segmentOwned, segmentBase,
      segmentChoice, segmentInitializer, segment, hsegmentSplit, _hsegmentTime,
      hsegmentChoiceAtCut, hsegmentPayload, _hsegmentInitializer,
      _hsegmentChoiceInitializer, _hsegmentSigma, _hsegmentCutoff,
      _hsegmentFreeze, _hsegmentFreezeGrid, _hsegmentBase, _hsegmentAssignment,
      _hsegmentChecked, _hwPositive, _hsegmentT, _hsegmentGrid, _hgridT,
      hfirstCutoff, _hsegmentAt, _hsegmentEntry, _hsegmentContext,
      _hsegmentRecords, _hsegmentRemaining, _hsegmentPartition, _hsegmentWindow⟩
  have hsegmentRecordsE : E.records = W ++ segmentCut :: segmentSuffix := by
    simpa [E, W] using hsegmentSplit
  have hsegmentCutEqOrigin : segmentCut = originCut :=
    horiginUnique segmentCut segmentSuffix hsegmentRecordsE
  have hsegmentCutEqCut : segmentCut = cut := hsegmentCutEqOrigin.trans hcutEqOrigin.symm

  have hContext := ReferenceFirstCollectionChosenContext.actual_first_collection_chosen_context
    rate source rewards C_star C_h count hcross hspan hshort
  rcases hContext n c hchoice with
    ⟨contextCut, contextSuffix, contextRegisters, contextOwned, contextBase,
      cutoffChoice, contextInitializer, contextSegment, hcontextSplit, _hcontextTime,
      hcutoffPayload, _hcontextInitializerEq, _hcontextSegmentAt, _hcontextEntry,
      _hcontextSegContext, hcontextChoiceAtCut, _hcontextChoiceInit,
      _hcontextChecked, _hcontextSigma, _hcontextCutoff, _hcontextFreeze,
      _hcontextFreezeGrid, _hcontextBase, _hcontextAssignment1,
      _hcontextAssignment2, _hcontextWPositive, hchoicePayload,
      _hcontextLedger, _hcontextWindowTime⟩
  have hcontextRecordsE : E.records = W ++ contextCut :: contextSuffix := by
    simpa [E, W] using hcontextSplit
  have hcontextCutEqOrigin : contextCut = originCut :=
    horiginUnique contextCut contextSuffix hcontextRecordsE
  have hcontextCutEqCut : contextCut = cut := hcontextCutEqOrigin.trans hcutEqOrigin.symm

  have hprepareCut :
      (ReferenceActivePhysicalStep.prepare cut.input).coordinator =
        .live registers owned base
          (.cutoffChosen dispatched hstart ledger hinit hcand hdomain hclock hpending
            hnoAssignment selected) := by
    calc
      (ReferenceActivePhysicalStep.prepare cut.input).coordinator =
          (ReferenceActivePhysicalStep.step cut.input).preparation.coordinator := rfl
      _ = cut.output.preparation.coordinator := by rw [cut.output_eq]
      _ = _ := hdispatch
  have hcontextChoiceAtCut' :
      ReferenceCollectionSegmentExtraction.choice cut.input = some cutoffChoice := by
    have hinputEq := congrArg
      (fun r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) => r.input)
      hcontextCutEqCut
    simpa only [hinputEq] using hcontextChoiceAtCut
  let canonicalCutoffChoice : ReferenceCollectionSegmentExtraction.Choice rate :=
    ⟨registers.payload, ReferenceActivePhysicalStep.sharedLedger ledger,
      dispatched.startResult,
      (ReferenceActivePhysicalStep.liveRegistersAt registers cut.input.time).complementWeights,
      some (ReferenceCollectionSegmentExtraction.cutoffInitializer
        (ReferenceActivePhysicalStep.liveRegistersAt registers cut.input.time)
        (ReferenceActivePhysicalStep.liveOwnedAt registers owned cut.input.time) base
        cut.input.time)⟩
  have hcanonicalCutoffChoice :
      ReferenceCollectionSegmentExtraction.choice cut.input =
        some canonicalCutoffChoice := by
    simp [ReferenceCollectionSegmentExtraction.choice,
      ReferenceCollectionSegmentExtraction.choiceOfCut, hprepareCut,
      ReferenceActivePhysicalStep.DispatchCut.selection,
      ReferenceActivePhysicalStep.selectionAt, canonicalCutoffChoice]
  have hcutoffChoicePayload : cutoffChoice.payload = registers.payload := by
    have heq : canonicalCutoffChoice = cutoffChoice :=
      Option.some.inj (hcanonicalCutoffChoice.symm.trans hcontextChoiceAtCut')
    exact (congrArg ReferenceCollectionSegmentExtraction.Choice.payload heq).symm
  have hsegmentChoiceAtCut' :
      ReferenceCollectionSegmentExtraction.choice cut.input = some segmentChoice := by
    have hinputEq := congrArg
      (fun r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) => r.input)
      hsegmentCutEqCut
    simpa only [hinputEq] using hsegmentChoiceAtCut
  have hsegmentChoicePayload : segmentChoice.payload = registers.payload := by
    have heq : canonicalCutoffChoice = segmentChoice :=
      Option.some.inj (hcanonicalCutoffChoice.symm.trans hsegmentChoiceAtCut')
    exact (congrArg ReferenceCollectionSegmentExtraction.Choice.payload heq).symm
  have hsegmentRegistersPayload : segmentRegisters.payload = registers.payload :=
    hsegmentPayload.symm.trans hsegmentChoicePayload
  have hcPayloadSource : c.payload = originPayload := by
    calc
      c.payload = cutoffChoice.payload := hchoicePayload
      _ = registers.payload := hcutoffChoicePayload
      _ = originPayload := hsourcePayload

  have hJoinRoot :=
    ReferenceFirstCollectionParsedUpBudgets.actual_first_collection_parsed_up_budget_calendar_replay_join
      rate source rewards C_star C_h count hcross hspan hshort
  have hJoin := hJoinRoot n c hchoice M hparse haccept
  simp only [Fin.getElem_fin] at hJoin
  rcases hJoin with
    ⟨P0, birth, state, memory, offered, j, message, _hinitializer,
      _hledgerSigma, _hledgerCutoff, hledgerAssignment, _hvalidLedger,
      _hpending, _hcurrentUnknown, _hcutoffUnknown, _hlplusSigma,
      _hlplusCutoff, hP0Sigma, _hP0Queues, hbirthMember, hbirthInstall,
      hbirthTime, _hconfiguration, _hcheckedOffer, _hOfferEq, _hword,
      _hlastDown, hjBound, _hjRange, hretained, hmessageP0, hmessageSigma,
      hmessageQ, hMSigma, hMS, hMq, hMdelta, _hbudgetJoint, _hbudgetScore,
      _hbudgetDelta, _hbudgetCap, _hcalendarEnd, _hindices, _hindexLength,
      _hreplayPrior, _hrowsBound, _hlonger, _hlongerLength,
      _hreplayCandidate, _hcandidateRowsBound⟩

  have hbirthEq : birth = originBirth := by
    apply ReferenceAssignmentPayloadChronology.run_records_time_injective
      (initial := initial) (rows := rows) (selected := J) (rewards := rewards)
      (start := s) (count := count) (hspan := hspan) (hmode := hmode)
    · simpa [E, ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun,
        ReferenceFirstCollectionEpochAlignment.actualLaunchState,
        ReferenceFirstLaunchNumericalCell.launchState, initial, rows, J, s] using hbirthMember
    · simpa [E, ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun,
        ReferenceFirstCollectionEpochAlignment.actualLaunchState,
        ReferenceFirstLaunchNumericalCell.launchState, initial, rows, J, s] using horiginBirthMember
    · calc
        birth.input.time.val = s := hbirthTime
        _ = originBirth.input.time.val := horiginBirthTime.symm
  have hOriginInstallAtBirth :
      ReferenceAssignmentPayloadPersistence.InstallationBirth birth originPayload := by
    rw [hbirthEq]
    exact horiginBirthInstall
  have hP0Origin : P0 = originPayload :=
    ReferenceAssignmentPayloadChronology.installationBirth_payload_unique
      birth P0 originPayload hbirthInstall hOriginInstallAtBirth

  have hledgerAssignmentAt :
      c.preLedger.assignment.arm i = c.payload.assignment.assigned i :=
    congrArg (fun arms : Fin (p.m - 1) → Fin p.K => arms i) hledgerAssignment
  refine ⟨P0, birth, j, message, hbirthMember, hbirthInstall, hbirthTime,
    hP0Origin.trans hcPayloadSource.symm, hmessageP0, hmessageQ, hretained,
    hjBound, hMSigma, hMS, hMq, hMdelta, hledgerAssignmentAt⟩

private theorem actual_down_recovery_no_reset
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (ConstructorDimensions.M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hfirst : initial.coordinator = .first)
    (i : Fin (p.m - 1))
    (seed : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hseed : initial.followers i = .ordinary seed memory)
    (hnone : seed.lastDown = none)
    (hunoccupied : seed.status = .unoccupied)
    (hvalid : ActiveFollowerLifecycle.localBufferValid seed)
    (hpair : seed.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound))
    (htime : ∀ saved ∈ seed.buffer, saved.calendarRound ≤ start)
    (j : Fin ((ReferenceActivePhysicalHorizon.run initial rows J rewards start count
      hspan hmode).records.length))
    (message : ReferenceFirstAcceptedUpNumericSnapshot.DownRecord (p := p) (rate := rate))
    (hretained : ReferenceAcceptedUpFollowerHistory.RetainedDown
      (ReferenceActivePhysicalHorizon.run initial rows J rewards start count
        hspan hmode).records[j.val] i message)
    (hsigma : message.val.sigma = start + 1) :
    ∀ prior ∈ (ReferenceActivePhysicalHorizon.run initial rows J rewards start count
      hspan hmode).records.take j.val,
      ¬ ReferenceFollowerBufferProvenance.acceptedDownReset i prior := by
  obtain ⟨logged, downCut, after, raw, scan, registers, lastService,
      _hlogged, _hdown, _houtcome, view, selected, _, _, _, _,
      birth, installed, firstChoice, _, _, _, _, _, _, _, _, _, hq, _, _,
      n0, _hn0, _hendpoint, _hnpos, _hnbound, hnoReset,
      _hphysical, _hchecked, _hregisters, _hlast, _hdomains, _hafter⟩ :=
    ReferenceFirstDownZeroRecovery.actual_first_down_zero_seeded_recovery
      initial rows J rewards start count hspan hmode hfirst i seed memory hseed
      hnone hunoccupied hvalid hpair htime j message hretained hsigma
  exact hnoReset

private theorem retained_prefix_start_contradiction
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (w d : ℕ) (hd : d < records.length) (hdw : d < w)
    (i : Fin (p.m - 1))
    (message : ReferenceFirstAcceptedUpNumericSnapshot.DownRecord (p := p) (rate := rate))
    (hretained : ReferenceAcceptedUpFollowerHistory.RetainedDown records[d] i message)
    (next : ReferencePrelaunchFollower.State p rate.eta)
    (nextMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hnextTake :
      ((records.take w)[d]'(by
        simp only [List.length_take]
        exact (Nat.lt_min).2 ⟨hdw, hd⟩)).output.next.followers i =
        .ordinary next nextMemory)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (hstate : state.lastDown = none)
    (hstartBoundState : ReferencePrelaunchFollower.acceptedStart next ≤
      ReferencePrelaunchFollower.acceptedStart state)
    (start : ℕ)
    (hsigma : message.val.sigma = start + 1) :
    False := by
  have hindex : records[d] = (records.take w)[d]'(by
      simp only [List.length_take]
      exact (Nat.lt_min).2 ⟨hdw, hd⟩) :=
    List.getElem_take' (hi := hd) (hj := hdw)
  have hnext :
      records[d].output.next.followers i = .ordinary next nextMemory := by
    rw [← hindex] at hnextTake
    exact hnextTake
  have happly : ReferenceFollowerReplyChronology.appliedDown records[d] i message.val.sigma :=
    ReferenceAcceptedUpFollowerHistory.retainedDown_appliedDown hretained
  obtain ⟨_, _, _, hstrict, hnextSigma⟩ :=
    ReferenceFollowerReplyChronology.record_appliedDown_strict
      records[d] i message.val.sigma happly next nextMemory hnext
  have hstartZero : ReferencePrelaunchFollower.acceptedStart state = 0 := by
    simp [ReferencePrelaunchFollower.acceptedStart, hstate]
  rw [hnextSigma, hstartZero, hsigma] at hstartBoundState
  omega

private theorem actual_first_collection_parsed_up_canonical_replay_fields
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
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
    let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
      rate source rewards C_star C_h hcross count hspan
    let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records
    let w := W.length
    let B := ReferenceCollectionPhaseHistory.collectionWindow E.records w
    let cells := ReferenceFirstWindowNumericalStream.actualLiveSourceCells
      rate source rewards C_star C_h hcross count hspan
    let qpar := ReferenceFirstLaunchNumericalCell.queueParameters rate
    ∀ (n : Fin B.length) (c : ReferenceCollectionSegmentExtraction.Choice rate),
      ReferenceCollectionSegmentExtraction.choice B[n].input = some c →
      let x := B[n].input
      let i := ReferenceActivePhysicalStep.upSenderIndex x
      let a := c.preLedger.assignment.arm i
      let candidate := CoordinatorCollectionLedger.startRoundCandidate c.preLedger x.time
        (ReferenceActivePhysicalStep.collectionEnabled c.preLedger x.time)
        (ReferenceCollectionRawBufferHistory.rawDiagnostic B[n])
      let A := fun X : List (RecordedQueueRun.RoundInput p.K) =>
        X.map (fun z => (z.enabled, RecordedQueueRun.quantizedArrival qpar z a))
      let V := fun h => QueueReplay.replay (4 * rate.n) (0, 0) (A (cells.take h))
      ∀ (M : OrdinaryMessageCodec.UpRecord
        (CoordinatorCollectionLedger.codecParams p rate.eta.val)),
        ReferenceCollectionSegmentExtraction.effectiveParse x candidate = some M →
        CoordinatorCollectionLedger.acceptUpCheck candidate i M = true →
        M.val.S = (V w).1 ∧
        M.val.q = (V w).2 ∧
        M.val.delta = (V w).1 - (V (w - 1)).1 := by
  classical
  let init := ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate
  let boot := ReferenceInitializationRun.output init
  let s := ReferenceInitializationRun.elapsed p boot.completed
  let I := ReferenceFirstCollectionEpochAlignment.actualLaunchState
    rate source rewards C_star C_h hcross
  let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
    rate source rewards C_star C_h hcross count hspan
  let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records
  let w := W.length
  let B := ReferenceCollectionPhaseHistory.collectionWindow E.records w
  let u := s + w + 1
  let cells := ReferenceFirstWindowNumericalStream.actualLiveSourceCells
    rate source rewards C_star C_h hcross count hspan
  let qpar := ReferenceFirstLaunchNumericalCell.queueParameters rate
  change ∀ (n : Fin B.length) (c : ReferenceCollectionSegmentExtraction.Choice rate),
    ReferenceCollectionSegmentExtraction.choice B[n].input = some c → _
  intro n c hchoice
  dsimp only
  let x := B[n].input
  let i := ReferenceActivePhysicalStep.upSenderIndex x
  let a := c.preLedger.assignment.arm i
  let candidate := CoordinatorCollectionLedger.startRoundCandidate c.preLedger x.time
    (ReferenceActivePhysicalStep.collectionEnabled c.preLedger x.time)
    (ReferenceCollectionRawBufferHistory.rawDiagnostic B[n])
  let A := fun X : List (RecordedQueueRun.RoundInput p.K) =>
    X.map (fun z => (z.enabled, RecordedQueueRun.quantizedArrival qpar z a))
  let V := fun h => QueueReplay.replay (4 * rate.n) (0, 0) (A (cells.take h))
  intro M hparse haccept

  have hWitness := actual_first_collection_parsed_up_payload_source
    rate source rewards C_star C_h count hcross hspan hshort n c hchoice M hparse haccept
  rcases hWitness with
    ⟨P0, birth, d, message, hbirthMember, hbirthInstall, hbirthTime,
      hP0Choice, hmessageP0, hmessageQ, hretained, hdBound, hMSigma,
      hMS, hMq, hMdelta, hledgerAssignment⟩

  let initial := ReferenceFirstCollectionEpochAlignment.actualLaunchState
    rate source rewards C_star C_h hcross
  let rows := source.1.2
  let J := ActualInitializationPhysicalStep.selectedRowIndex p source
  let liveRun := ReferenceFirstWindowNumericalStream.actualFirstLiveRun
    rate source rewards C_star C_h hcross count hspan
  let liveWindow := ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
    rate source rewards C_star C_h hcross count hspan
  let cellAt := ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
    rate source rewards C_star C_h hcross count hspan
  let seed := ReferenceInitializationRun.ordinary init boot
    (ActualReferenceInitializationBlock.refFollower i)
  let seedMemory := ActiveFollowerLifecycle.initialMemory p

  have hlaunchSeed := ReferenceFirstLaunchNumericalCell.actual_launch_seed
    rate source rewards C_star C_h hcross
  rcases hlaunchSeed with ⟨_, hmodeSource, _, hfirstSource, _, _, _, hseedFollowersSource⟩
  have hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial s := by
    simpa [initial, ReferenceFirstCollectionEpochAlignment.actualLaunchState,
      ReferenceFirstLaunchNumericalCell.launchState] using hmodeSource
  have hfirst : initial.coordinator = .first := by
    simpa [initial, ReferenceFirstCollectionEpochAlignment.actualLaunchState,
      ReferenceFirstLaunchNumericalCell.launchState] using hfirstSource
  have hLiveRunEq : liveRun = E := rfl
  have hLiveWindowEq : liveWindow = W := by
    simp [liveWindow, ReferenceFirstWindowNumericalStream.actualFirstLiveWindow,
      ReferenceFirstWindowNumericalStream.actualFirstLiveRun, E, W,
      ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun,
      ReferenceFirstCollectionEpochAlignment.actualLaunchState,
      ReferenceFirstLaunchNumericalCell.launchState]
  have hLiveWindowLength : liveWindow.length = w := by
    simp [W, w, hLiveWindowEq]
  have hshortLive : liveWindow.length < count := by
    simpa [liveWindow, liveRun, ReferenceFirstWindowNumericalStream.actualFirstLiveWindow,
      ReferenceFirstWindowNumericalStream.actualFirstLiveRun, E,
      ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun,
      ReferenceFirstCollectionEpochAlignment.actualLaunchState,
      ReferenceFirstLaunchNumericalCell.launchState] using hshort

  have hOrigin := ReferenceFirstCollectionDownPayloadOrigin.actual_first_collection_down_payload_origin
    rate source rewards C_star C_h count hcross hspan hshort
  rcases hOrigin.origin with
    ⟨originCut, originPayload, originBirth, originRegisters, originOwned, originBase,
      horiginIndex, horiginUnique, horiginState, _horiginCutoff, horiginPayload,
      horiginSigma, _horiginQueues, _horiginFirstCutoff, horiginBirthMember,
      horiginBirthInstall, horiginBirthTime, _horiginBirthFirst, _horiginWindowLookup,
      _horiginSelectedPayload, _horiginPrior⟩
  have hbirthEq : birth = originBirth := by
    apply ReferenceAssignmentPayloadChronology.run_records_time_injective
      (initial := initial) (rows := rows) (selected := J) (rewards := rewards)
      (start := s) (count := count) (hspan := hspan) (hmode := hmode)
    · simpa [E, ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun,
        ReferenceFirstCollectionEpochAlignment.actualLaunchState,
        ReferenceFirstLaunchNumericalCell.launchState, initial, rows, J, s] using hbirthMember
    · simpa [E, ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun,
        ReferenceFirstCollectionEpochAlignment.actualLaunchState,
        ReferenceFirstLaunchNumericalCell.launchState, initial, rows, J, s] using horiginBirthMember
    · calc
        birth.input.time.val = s := hbirthTime
        _ = originBirth.input.time.val := horiginBirthTime.symm
  have hOriginInstallAtBirth :
      ReferenceAssignmentPayloadPersistence.InstallationBirth birth originPayload := by
    rw [hbirthEq]
    exact horiginBirthInstall
  have hP0Origin : P0 = originPayload :=
    ReferenceAssignmentPayloadChronology.installationBirth_payload_unique
      birth P0 originPayload hbirthInstall hOriginInstallAtBirth

  have hCutoffSource := ReferenceFirstCutoffNumericalSource.actual_first_cutoff_numerical_source
    rate source rewards C_star C_h hcross count hspan hshortLive
  rcases hCutoffSource with
    ⟨cut, suffix, registers, owned, base, hcutIndex, hrecordsCut, hcutTime,
      hcutRows, hcutSelected, hcutRewards, hcutState, hcutSigma, hcutQueues,
      hdispatchData⟩
  rcases hdispatchData with
    ⟨dispatched, hstart, ledger, hinit, hcand, hdomain, hclock, hpending,
      hnoAssignment, selected, hdispatch, hdispatchTail⟩
  rcases hdispatchTail with
    ⟨hu, huT, huGrid, hledgerSigma, hledgerCutoff, hfollowersTail⟩
  rcases hfollowersTail with
    ⟨hcutFollowers, hkPositive, hpreparedFollowers, hcutFollower, hcellPayload,
      _hcollectionRecorder⟩
  have hrecordsCutLive : liveRun.records = liveWindow ++ cut :: suffix := by
    simpa [liveRun, liveWindow,
      ReferenceFirstWindowNumericalStream.actualFirstLiveRun,
      ReferenceFirstWindowNumericalStream.actualFirstLiveWindow] using hrecordsCut
  have hrecordsCutE : E.records = W ++ cut :: suffix := by
    simpa only [hLiveRunEq, hLiveWindowEq] using hrecordsCutLive
  have hcutEqOrigin : cut = originCut := horiginUnique cut suffix hrecordsCutE

  have hcoordEq : cut.input.state.coordinator = originCut.input.state.coordinator :=
    congrArg (fun r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) =>
      r.input.state.coordinator) hcutEqOrigin
  have hregistersEq : registers = originRegisters := by
    have hlive :
        (ReferenceActivePhysicalStep.CoordinatorConfiguration.live registers owned base) =
          .live originRegisters originOwned originBase := by
      exact hcutState.symm.trans (hcoordEq.trans horiginState)
    injection hlive with hregisters
  have hsourcePayload : registers.payload = originPayload := by
    rw [hregistersEq, horiginPayload]

  rcases hcutFollower i with ⟨sb, sbMemory, hsb, hsourceBranches⟩
  rcases hsourceBranches with ⟨k0, hk0, hsourceBranches⟩
  let sourcePayload := (cellAt k0).selected.view.payload
  let M0 := sourcePayload.downRecord i
  let sourceArrivals := fun h => (cells.take h).map (fun z =>
    (z.enabled, RecordedQueueRun.quantizedArrival qpar z
      (sourcePayload.assignment.assigned i)))
  let sourceReplay := fun h => QueueReplay.replay (4 * rate.n) (0, 0)
    (sourceArrivals h)
  rcases hsourceBranches with ⟨hOccupied, hUnoccupied⟩
  have hsourcePayloadCell : sourcePayload = originPayload := by
    calc
      sourcePayload = registers.payload := hcellPayload k0
      _ = originPayload := hsourcePayload
  have hM0Eq : M0 = message := by
    calc
      M0 = originPayload.downRecord i := by
        change sourcePayload.downRecord i = originPayload.downRecord i
        rw [hsourcePayloadCell]
      _ = P0.downRecord i := by rw [hP0Origin]
      _ = message := hmessageP0.symm
  have hsourceArm : a = originPayload.assignment.assigned i := by
    calc
      a = c.preLedger.assignment.arm i := rfl
      _ = c.payload.assignment.assigned i := hledgerAssignment
      _ = P0.assignment.assigned i :=
        congrArg (fun payload : ReferenceActivePhysicalStep.Payload rate =>
          payload.assignment.assigned i) hP0Choice.symm
      _ = originPayload.assignment.assigned i :=
        congrArg (fun payload : ReferenceActivePhysicalStep.Payload rate =>
          payload.assignment.assigned i) hP0Origin
  have hsourceArrivalsEq (h : ℕ) : sourceArrivals h = A (cells.take h) := by
    simp [sourceArrivals, A, hsourcePayloadCell, hsourceArm]
  have hOccupiedRetained : ∀ hstatus : sb.status ≠ .unoccupied,
      ∃ priorIndex : Fin liveWindow.length,
        priorIndex.val < liveWindow.length ∧
        ReferenceAcceptedUpFollowerHistory.RetainedDown
          liveWindow[priorIndex.val] i M0 := by
    intro hstatus
    have hfields := hOccupied hstatus
    exact hfields.2.2.2.2.2.2.2

  let F := fun h => QueueReplay.replay (4 * rate.n) (0, 0)
    (ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords E.records i d.val message h)

  have hcutFin : w < E.records.length := by
    have hlen := ReferenceActivePhysicalHorizon.run_record_count initial rows J rewards s count hspan hmode
    have hw : w < count := by
      simpa [E, W, w] using hshort
    have hlenE : E.records.length = count := by
      simpa [E, ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun,
        initial, s] using hlen
    rw [hlenE]
    exact hw
  let cutoffIndex : Fin E.records.length := ⟨w, hcutFin⟩
  have hcutRecord : E.records[w] = cut := by
    have hgetOwn : E.records[w]? = some E.records[w] :=
      List.getElem?_eq_getElem hcutFin
    have hgetCut : E.records[w]? = some cut := by
      rw [hrecordsCutE]
      simp [W, w]
    exact Option.some.inj (hgetOwn.symm.trans hgetCut)

  rcases hseedFollowersSource i with
    ⟨hseedSource, hseedNone, _hseedStart, _hseedScore, _hseedDelta,
      _hseedBacklog, hseedUnoccupied, _hseedDomain, hseedValid,
      hseedPair, hseedTime⟩
  have hseed : initial.followers i = .ordinary seed seedMemory := by
    simpa [initial, seed, seedMemory,
      ReferenceFirstCollectionEpochAlignment.actualLaunchState,
      ReferenceFirstLaunchNumericalCell.launchState] using hseedSource
  rcases hpreparedFollowers i with
    ⟨before, beforeMemory, hbefore, hstartRound, hprepared,
      hpreparedUnoccupied, _hpreparedDomain, _hpreparedScore,
      _hpreparedDelta, _hpreparedBacklog, hpreparedLastDown, _hpreparedTail⟩
  have hbeforeEq : before = sb := by
    exact (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
      (hbefore.symm.trans hsb)).1

  have hSegment := ReferenceFirstCollectionEpochAlignment.actual_first_collection_segment
    rate source rewards C_star C_h count hcross hspan hshort
  rcases hSegment with
    ⟨segmentCut, segmentSuffix, segmentRegisters, segmentOwned, segmentBase,
      segmentChoice, segmentInitializer, segment, hsegmentSplit, _hsegmentTime,
      hsegmentChoiceAtCut, hsegmentPayload, _hsegmentInitializer,
      _hsegmentChoiceInitializer, _hsegmentSigma, _hsegmentCutoff,
      _hsegmentFreeze, _hsegmentFreezeGrid, _hsegmentBase, _hsegmentAssignment,
      _hsegmentChecked, _hwPositive, _hsegmentT, _hsegmentGrid, _hgridT,
      hfirstCutoff, _hsegmentAt, _hsegmentEntry, _hsegmentContext,
      _hsegmentRecords, _hsegmentRemaining, _hsegmentPartition, _hsegmentWindow⟩
  have hsegmentRecordsE : E.records = W ++ segmentCut :: segmentSuffix := by
    simpa [E, W] using hsegmentSplit
  have hsegmentCutEqOrigin : segmentCut = originCut :=
    horiginUnique segmentCut segmentSuffix hsegmentRecordsE
  have hsegmentCutEqCut : segmentCut = cut := hsegmentCutEqOrigin.trans hcutEqOrigin.symm
  have hsegmentChoiceAtCut' :
      ReferenceCollectionSegmentExtraction.choice cut.input = some segmentChoice := by
    have hinputEq := congrArg
      (fun r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) => r.input)
      hsegmentCutEqCut
    simpa only [hinputEq] using hsegmentChoiceAtCut
  have hprepareCut :
      (ReferenceActivePhysicalStep.prepare cut.input).coordinator =
        .live registers owned base
          (.cutoffChosen dispatched hstart ledger hinit hcand hdomain hclock hpending
            hnoAssignment selected) := by
    calc
      (ReferenceActivePhysicalStep.prepare cut.input).coordinator =
          (ReferenceActivePhysicalStep.step cut.input).preparation.coordinator := rfl
      _ = cut.output.preparation.coordinator := by rw [cut.output_eq]
      _ = _ := hdispatch
  let canonicalCutoffChoice : ReferenceCollectionSegmentExtraction.Choice rate :=
    ⟨registers.payload, ReferenceActivePhysicalStep.sharedLedger ledger,
      dispatched.startResult,
      (ReferenceActivePhysicalStep.liveRegistersAt registers cut.input.time).complementWeights,
      some (ReferenceCollectionSegmentExtraction.cutoffInitializer
        (ReferenceActivePhysicalStep.liveRegistersAt registers cut.input.time)
        (ReferenceActivePhysicalStep.liveOwnedAt registers owned cut.input.time) base
        cut.input.time)⟩
  have hcanonicalCutoffChoice :
      ReferenceCollectionSegmentExtraction.choice cut.input =
        some canonicalCutoffChoice := by
    simp [ReferenceCollectionSegmentExtraction.choice,
      ReferenceCollectionSegmentExtraction.choiceOfCut, hprepareCut,
      ReferenceActivePhysicalStep.DispatchCut.selection,
      ReferenceActivePhysicalStep.selectionAt, canonicalCutoffChoice]
  have hsegmentChoicePayload : segmentChoice.payload = registers.payload := by
    have heq : canonicalCutoffChoice = segmentChoice :=
      Option.some.inj (hcanonicalCutoffChoice.symm.trans hsegmentChoiceAtCut')
    exact (congrArg ReferenceCollectionSegmentExtraction.Choice.payload heq).symm
  have hsegmentRegistersPayload : segmentRegisters.payload = registers.payload :=
    hsegmentPayload.symm.trans hsegmentChoicePayload

  have hmessageSigma : message.val.sigma = s + 1 := by
    rw [hmessageP0, hP0Origin]
    change (originPayload.downRecord i).val.sigma = s + 1
    rw [show (originPayload.downRecord i).val.sigma =
      originPayload.sigma.val + 1 by rfl, horiginSigma]
  have hcutForSegmentEndpoint :
      ∀ z : Fin (p.m - 1),
        FollowerCutoffScan.firstCutoff p rate.eta.val
          (ActiveFollowerDownAcceptance.downStart p rate message)
          (FollowerCutoffScan.completeRowProposalBit p rate.eta.val (rows J)) = s + w + 1 := by
    intro z
    have hdownStart :
        ActiveFollowerDownAcceptance.downStart p rate message = originPayload.sigma := by
      have hadd := ActiveFollowerDownAcceptance.downStart_val_add_one p rate message
      have hdownStartVal :
          (ActiveFollowerDownAcceptance.downStart p rate message).val = s := by
        apply Nat.add_right_cancel
        exact hadd.trans hmessageSigma
      apply Fin.ext
      exact hdownStartVal.trans horiginSigma.symm
    have hfirstCutoffOrigin :
        FollowerCutoffScan.firstCutoff p rate.eta.val originPayload.sigma
          (FollowerCutoffScan.completeRowProposalBit p rate.eta.val (rows J)) = s + w + 1 := by
      have hpayloadSigma := congrArg
        (fun payload : ReferenceActivePhysicalStep.Payload rate => payload.sigma)
        (hsegmentRegistersPayload.trans hsourcePayload)
      simpa only [hpayloadSigma] using hfirstCutoff z
    rw [hdownStart]
    exact hfirstCutoffOrigin

  have hRunEq :
      ReferenceActivePhysicalHorizon.run initial rows J rewards s count hspan hmode = E := by
    dsimp only [E, ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun,
      initial, ReferenceFirstCollectionEpochAlignment.actualLaunchState]

  have hcutChain :=
    ReferenceFollowerReplyChronology.connected_take_to_input E.connected w hcutFin
  have hcutChain' :
      ReferenceActivePhysicalHorizon.Connected initial (E.records.take w) cut.input.state := by
    simpa only [hcutRecord] using hcutChain

  by_cases hdEarly : d.val < w
  · have hnotUnoccupied : sb.status ≠ .unoccupied := by
      intro hsbUnoccupied
      rcases hUnoccupied hsbUnoccupied with
        ⟨hsbLastNone, _hsbZeroS, _hsbZeroDelta, _hsbZeroBacklog,
          _hsbBuffer, _hsbReplyRecords⟩
      obtain ⟨next, nextMemory, hnextTake, hstartBound⟩ :=
        ReferenceFollowerReplyChronology.connected_output_chronology
          (chain := hcutChain') (i := i) (last := sb)
          (lastMemory := sbMemory) (hf := hsb) (n := d.val) (hn := by
            simp only [List.length_take]
            exact (Nat.lt_min).2 ⟨hdEarly, d.isLt⟩)
      exact retained_prefix_start_contradiction
        rate E.records w d.val d.isLt hdEarly i message hretained next nextMemory
        hnextTake sb hsbLastNone hstartBound s hmessageSigma
    have hOccupiedData : sb.lastDown = some M0 ∧
        (sb.S, sb.backlog) = sourceReplay w ∧
        sb.delta = (sourceReplay w).1 - (sourceReplay (w - 1)).1 := by
      have hfields := hOccupied hnotUnoccupied
      exact ⟨hfields.1, hfields.2.1, hfields.2.2.1⟩
    have hsbLastDown := hOccupiedData.1
    have hsbRegisters := hOccupiedData.2.1
    have hsbDelta := hOccupiedData.2.2
    have hlastDown :
        ({ before with status := ActiveRoundActions.FollowerStatus.unoccupied }).lastDown =
          some message := by
      calc
        ({ before with status := ActiveRoundActions.FollowerStatus.unoccupied }).lastDown =
            before.lastDown := hpreparedLastDown
        _ = sb.lastDown := by rw [hbeforeEq]
        _ = some M0 := hsbLastDown
        _ = some message := congrArg some hM0Eq
    have hlastChoice :
        (ReferenceFollowerFixedReply.actualChoice E.records[w] i).configuration =
          .ordinary ({ before with status := ActiveRoundActions.FollowerStatus.unoccupied })
            beforeMemory := by
      dsimp only [ReferenceFollowerFixedReply.actualChoice]
      rw [hcutRecord]
      exact hprepared
    have hlastStatus :
        ({ before with status := ActiveRoundActions.FollowerStatus.unoccupied }).status =
          .unoccupied := by simp
    let epochReplayIndex : Fin E.records.length := cutoffIndex
    have hReplay := ReferenceFirstOfferedUpNumericalReplay.choice_replay_of_retained_first_down
      initial rows J rewards s count hspan hmode hfirst i seed seedMemory hseed
      hseedNone hseedUnoccupied hseedValid hseedPair hseedTime d epochReplayIndex
      (by dsimp [epochReplayIndex]; exact hdEarly) message hretained hmessageSigma
      ({ before with status := ActiveRoundActions.FollowerStatus.unoccupied })
      beforeMemory hlastChoice hlastDown hlastStatus
    have hReplayLength :
        FollowerCutoffScan.firstCutoff p rate.eta.val
          (ActiveFollowerDownAcceptance.downStart p rate message)
          (FollowerCutoffScan.completeRowProposalBit p rate.eta.val (rows J)) -
            (s + 1) = w := by
      rw [hcutForSegmentEndpoint i]
      omega
    rcases hReplay with
      ⟨_hcutoffPositive, _hreplayPositive, _hreplayBound,
        _hreplayIndexBound, hReplayScore, hReplayQueue, hReplayDelta⟩
    have hReplayScoreW :
        ({ before with status := ActiveRoundActions.FollowerStatus.unoccupied }).S =
          (F w).1 := by
      simpa only [F, epochReplayIndex, hReplayLength, hRunEq] using hReplayScore
    have hReplayQueueW :
        ({ before with status := ActiveRoundActions.FollowerStatus.unoccupied }).backlog =
          (F w).2 := by
      simpa only [F, epochReplayIndex, hReplayLength, hRunEq] using hReplayQueue
    have hReplayDeltaW :
        ({ before with status := ActiveRoundActions.FollowerStatus.unoccupied }).delta =
          (F w).1 - (F (w - 1)).1 := by
      simpa only [F, epochReplayIndex, hReplayLength, hRunEq] using hReplayDelta
    have hpreparedScore' :
        ({ before with status := ActiveRoundActions.FollowerStatus.unoccupied }).S = sb.S := by
      simp only [hbeforeEq]
    have hpreparedBacklog' :
        ({ before with status := ActiveRoundActions.FollowerStatus.unoccupied }).backlog =
          sb.backlog := by
      simp only [hbeforeEq]
    have hpreparedDelta' :
        ({ before with status := ActiveRoundActions.FollowerStatus.unoccupied }).delta = sb.delta := by
      simp only [hbeforeEq]
    have hsbScore : sb.S = (sourceReplay w).1 := congrArg Prod.fst hsbRegisters
    have hsbBacklog : sb.backlog = (sourceReplay w).2 := congrArg Prod.snd hsbRegisters
    have hsourceReplayW : sourceReplay w = V w := by
      simp [sourceReplay, sourceArrivals, A, V, hsourcePayloadCell, hsourceArm]
    have hsourceReplayPrevious : sourceReplay (w - 1) = V (w - 1) := by
      simp [sourceReplay, sourceArrivals, A, V, hsourcePayloadCell, hsourceArm]
    have hScoreEq : (F w).1 = (V w).1 := by
      calc
        (F w).1 = ({ before with status := ActiveRoundActions.FollowerStatus.unoccupied }).S :=
          hReplayScoreW.symm
        _ = sb.S := hpreparedScore'
        _ = (sourceReplay w).1 := hsbScore
        _ = (V w).1 := congrArg Prod.fst hsourceReplayW
    have hQueueEq : (F w).2 = (V w).2 := by
      calc
        (F w).2 = ({ before with status := ActiveRoundActions.FollowerStatus.unoccupied }).backlog :=
          hReplayQueueW.symm
        _ = sb.backlog := hpreparedBacklog'
        _ = (sourceReplay w).2 := hsbBacklog
        _ = (V w).2 := congrArg Prod.snd hsourceReplayW
    have hDeltaEq :
        (F w).1 - (F (w - 1)).1 = (V w).1 - (V (w - 1)).1 := by
      have hPreparedDeltaSource :
          ({ before with status := ActiveRoundActions.FollowerStatus.unoccupied }).delta =
            (sourceReplay w).1 - (sourceReplay (w - 1)).1 := by
        calc
          ({ before with status := ActiveRoundActions.FollowerStatus.unoccupied }).delta = sb.delta :=
            hpreparedDelta'
          _ = (sourceReplay w).1 - (sourceReplay (w - 1)).1 := hsbDelta
      have hCanonicalDelta :
          ({ before with status := ActiveRoundActions.FollowerStatus.unoccupied }).delta =
            (V w).1 - (V (w - 1)).1 := by
        calc
          ({ before with status := ActiveRoundActions.FollowerStatus.unoccupied }).delta =
              (sourceReplay w).1 - (sourceReplay (w - 1)).1 := hPreparedDeltaSource
          _ = (V w).1 - (V (w - 1)).1 := by
            rw [hsourceReplayW, hsourceReplayPrevious]
      exact hReplayDeltaW.symm.trans hCanonicalDelta
    refine ⟨?_, ?_, ?_⟩
    · exact hMS.trans hScoreEq
    · exact hMq.trans hQueueEq
    · exact hMdelta.trans hDeltaEq
  · have hlate : w ≤ d.val := by omega
    have hnoResetRun := actual_down_recovery_no_reset
      rate initial rows J rewards s count hspan hmode hfirst i seed seedMemory hseed
      hseedNone hseedUnoccupied hseedValid hseedPair hseedTime d message hretained
      hmessageSigma
    have hnoReset : ∀ prior ∈ E.records.take d.val,
        ¬ ReferenceFollowerBufferProvenance.acceptedDownReset i prior := by
      simpa only [hRunEq] using hnoResetRun
    have hnotOccupied : ¬ sb.status ≠ .unoccupied := by
      intro hsbOccupied
      rcases hOccupiedRetained hsbOccupied with ⟨priorIndex, hpriorIndex, hretainedCut⟩
      have hpriorFull : priorIndex.val < E.records.length := by
        have hwindowLe : W.length ≤ E.records.length := by
          rw [hrecordsCutE]
          simp
        have hpriorBound : priorIndex.val < W.length := by
          simpa [liveWindow, W, hLiveWindowEq] using priorIndex.isLt
        exact hpriorBound.trans_le hwindowLe
      have hpriorOwn :
          E.records[priorIndex.val]? = some E.records[priorIndex.val] :=
        List.getElem?_eq_getElem hpriorFull
      have hpriorBound : priorIndex.val < W.length := by
        simpa only [hLiveWindowEq] using priorIndex.isLt
      have hpriorWindowAppend :
          (W ++ cut :: suffix)[priorIndex.val]? = some W[priorIndex.val] := by
        rw [List.getElem?_append_left hpriorBound]
        exact List.getElem?_eq_getElem hpriorBound
      have hpriorWindow :
          E.records[priorIndex.val]? = some W[priorIndex.val] := by
        calc
          E.records[priorIndex.val]? =
              (W ++ cut :: suffix)[priorIndex.val]? :=
            congrArg (fun records : List (ReferenceActivePhysicalHorizon.RoundRecord
              (p := p) (rate := rate)) => records[priorIndex.val]?) hrecordsCutE
          _ = some W[priorIndex.val] := hpriorWindowAppend
      have hpriorElem :
          E.records[priorIndex.val] = W[priorIndex.val] :=
        Option.some.inj (hpriorOwn.symm.trans hpriorWindow)
      have hretainedW :
          ReferenceAcceptedUpFollowerHistory.RetainedDown W[priorIndex.val] i M0 := by
        simpa only [hLiveWindowEq] using hretainedCut
      have hretainedE :
          ReferenceAcceptedUpFollowerHistory.RetainedDown
            E.records[priorIndex.val] i M0 := by
        simpa only [hpriorElem] using hretainedW
      have hreset :
          ReferenceFollowerBufferProvenance.acceptedDownReset i
            E.records[priorIndex.val] := by
        rcases hretainedE with ⟨logged0, cut0, after0, raw0, scan0,
          regs0, service0, hinput0, hdown0, haccepted0⟩
        exact ⟨cut0, hdown0, logged0, after0, raw0, M0, scan0, regs0,
          service0, haccepted0⟩
      have hmemTake : E.records[priorIndex.val] ∈ E.records.take d.val :=
        List.mem_take_iff_getElem.mpr ⟨priorIndex.val,
          (Nat.lt_min).2 ⟨by omega, hpriorFull⟩, rfl⟩
      exact hnoReset (E.records[priorIndex.val]) hmemTake hreset
    have hsbUnoccupied : sb.status = .unoccupied := by
      by_cases hstatus : sb.status = .unoccupied
      · exact hstatus
      · exact (hnotOccupied hstatus).elim
    rcases hUnoccupied hsbUnoccupied with
      ⟨_hsbLastNone, _hsbZeroS, _hsbZeroDelta, _hsbZeroBacklog,
        _hsbBuffer, hReplyRecordsW⟩
    have hsourceM0 :
        (cellAt k0).selected.view.payload.downRecord i = message := by
      change M0 = message
      exact hM0Eq
    rw [hsourceM0] at hReplyRecordsW
    have hReplyRecordsW' :
        ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords
          E.records i w message w = A (cells.take w) := by
      calc
        ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords
            E.records i w message w = sourceArrivals w := by
          simpa [E, liveRun, liveWindow, W, w, cells, qpar,
            ReferenceFirstWindowNumericalStream.actualFirstLiveRun,
            ReferenceFirstWindowNumericalStream.actualFirstLiveWindow,
            ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun,
            ReferenceFirstCollectionEpochAlignment.actualLaunchState,
            ReferenceFirstLaunchNumericalCell.launchState,
            sourceArrivals, sourcePayload, hLiveWindowLength] using hReplyRecordsW
        _ = A (cells.take w) := hsourceArrivalsEq w
    have hReplyDToW :
        ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords
          E.records i d.val message w =
        ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords
          E.records i w message w := by
      rw [ReferenceFirstLiveDownNumericalRecovery.firstReplyQueueRecords_eq_emissions
        E.records i d.val w message (by omega),
        ReferenceFirstLiveDownNumericalRecovery.firstReplyQueueRecords_eq_emissions
          E.records i w w message (by omega)]
    have hSourceReplayW : F w = V w := by
      unfold F V
      exact congrArg (QueueReplay.replay (4 * rate.n) (0, 0))
        (hReplyDToW.trans hReplyRecordsW')

    have hwPositive : 0 < w := by
      simpa only [liveWindow, hLiveWindowLength] using hkPositive
    let previousIndex : Fin liveWindow.length :=
      ⟨w - 1, by rw [hLiveWindowLength]; omega⟩
    have hpreviousPayload : (cellAt previousIndex).selected.view.payload = originPayload := by
      calc
        (cellAt previousIndex).selected.view.payload = registers.payload :=
          hcellPayload previousIndex
        _ = originPayload := hsourcePayload
    have hmessagePrevious :
        message = (cellAt previousIndex).selected.view.payload.downRecord i := by
      calc
        message = P0.downRecord i := hmessageP0
        _ = originPayload.downRecord i :=
          congrArg (fun payload : ReferenceActivePhysicalStep.Payload rate => payload.downRecord i)
            hP0Origin
        _ = (cellAt previousIndex).selected.view.payload.downRecord i := by
          rw [hpreviousPayload]
    have hnoResetPrevious : ∀ prior ∈ liveRun.records.take previousIndex.val,
        ¬ ReferenceFollowerBufferProvenance.acceptedDownReset i prior := by
      intro prior hprior
      have hpriorE : prior ∈ E.records.take previousIndex.val := by
        simpa only [hLiveRunEq] using hprior
      rcases List.mem_take_iff_getElem.mp hpriorE with ⟨r, hr, hpriorEq⟩
      rcases Nat.lt_min.mp hr with ⟨hrTake, hrFull⟩
      have hrBeforeDown : r < d.val := by
        have hrBeforePrevious : r < w - 1 := by simpa [previousIndex] using hrTake
        omega
      have hmemD : prior ∈ E.records.take d.val :=
        List.mem_take_iff_getElem.mpr ⟨r,
          (Nat.lt_min).2 ⟨hrBeforeDown, hrFull⟩, hpriorEq⟩
      exact hnoReset prior hmemD
    have hReplyPrefix :=
      ReferenceFirstLiveDownNumericalRecovery.actual_reply_records_eq_source_prefix
        rate source rewards C_star C_h hcross count hspan i previousIndex message
        hmessagePrevious hnoResetPrevious
    have hReplyDPrevious :
        ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords
          E.records i d.val message (w - 1) =
        ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords
          E.records i previousIndex.val message (w - 1) := by
      rw [ReferenceFirstLiveDownNumericalRecovery.firstReplyQueueRecords_eq_emissions
        E.records i d.val (w - 1) message (by omega),
        ReferenceFirstLiveDownNumericalRecovery.firstReplyQueueRecords_eq_emissions
          E.records i previousIndex.val (w - 1) message (by simp [previousIndex])]
    have hReplyPrevious :
        ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords
          E.records i d.val message (w - 1) = A (cells.take (w - 1)) := by
      have hreply := hReplyPrefix (w - 1) (by simp [previousIndex])
      have hpreviousVal : previousIndex.val = w - 1 := rfl
      have hpreviousPayload' :
          (ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
            rate source rewards C_star C_h hcross count hspan previousIndex).selected.view.payload =
              originPayload := by
        simpa [cellAt] using hpreviousPayload
      rw [hpreviousPayload'] at hreply
      have hreply' :
          ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords
            E.records i previousIndex.val message (w - 1) = A (cells.take (w - 1)) := by
        simpa [liveRun, liveWindow, E, W, cells, qpar, A,
          ReferenceFirstWindowNumericalStream.actualFirstLiveRun,
          ReferenceFirstWindowNumericalStream.actualFirstLiveWindow,
          ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun,
          ReferenceFirstCollectionEpochAlignment.actualLaunchState,
          ReferenceFirstLaunchNumericalCell.launchState,
          hRunEq, hLiveWindowLength, hpreviousVal, hsourceArm] using hreply
      exact hReplyDPrevious.trans hreply'
    have hSourceReplayPrevious : F (w - 1) = V (w - 1) := by
      unfold F V
      exact congrArg (QueueReplay.replay (4 * rate.n) (0, 0)) hReplyPrevious
    refine ⟨?_, ?_, ?_⟩
    · exact hMS.trans (congrArg Prod.fst hSourceReplayW)
    · exact hMq.trans (congrArg Prod.snd hSourceReplayW)
    · calc
        M.val.delta = (F w).1 - (F (w - 1)).1 := hMdelta
        _ = (V w).1 - (V (w - 1)).1 := by
          rw [hSourceReplayW, hSourceReplayPrevious]

/-- A parsed and accepted first-collection UP record retains its actual DOWN
origin and has score, queue, and last-service delta equal to the original
launch-cell replay at the canonical live cutoff. -/
theorem actual_first_collection_parsed_up_canonical_cutoff
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
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
    let init := ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate
    let I := ReferenceInitializationRun.output init
    let s := ReferenceInitializationRun.elapsed p I.completed
    let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
      rate source rewards C_star C_h hcross count hspan
    let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records
    let w := W.length
    let B := ReferenceCollectionPhaseHistory.collectionWindow E.records w
    let _u := s + w + 1
    let cells := ReferenceFirstWindowNumericalStream.actualLiveSourceCells
      rate source rewards C_star C_h hcross count hspan
    let qpar := ReferenceFirstLaunchNumericalCell.queueParameters rate
    ∀ (n : Fin B.length) (c : ReferenceCollectionSegmentExtraction.Choice rate),
      ReferenceCollectionSegmentExtraction.choice B[n].input = some c →
      let x := B[n].input
      let i := ReferenceActivePhysicalStep.upSenderIndex x
      let a := c.preLedger.assignment.arm i
      let candidate := CoordinatorCollectionLedger.startRoundCandidate c.preLedger x.time
        (ReferenceActivePhysicalStep.collectionEnabled c.preLedger x.time)
        (ReferenceCollectionRawBufferHistory.rawDiagnostic B[n])
      let A := fun X : List (RecordedQueueRun.RoundInput p.K) =>
        X.map (fun z => (z.enabled, RecordedQueueRun.quantizedArrival qpar z a))
      let V := fun h => QueueReplay.replay (4 * rate.n) (0, 0) (A (cells.take h))
      ∀ (M : OrdinaryMessageCodec.UpRecord
        (CoordinatorCollectionLedger.codecParams p rate.eta.val)),
        ReferenceCollectionSegmentExtraction.effectiveParse x candidate = some M →
        CoordinatorCollectionLedger.acceptUpCheck candidate i M = true →
        ∃ (P0 : ReferenceActivePhysicalStep.Payload rate)
          (birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
          (d : Fin E.records.length)
          (message : ReferenceFirstAcceptedUpNumericSnapshot.DownRecord (p := p) (rate := rate)),
          birth ∈ E.records ∧
          ReferenceAssignmentPayloadPersistence.InstallationBirth birth P0 ∧
          birth.input.time.val = s ∧
          P0 = c.payload ∧
          message = P0.downRecord i ∧
          message.val.q = 0 ∧
          ReferenceAcceptedUpFollowerHistory.RetainedDown E.records[d.val] i message ∧
          d.val < w + n.val ∧
          M.val.sigma = s + 1 ∧
          M.val.S = (V w).1 ∧
          M.val.q = (V w).2 ∧
          M.val.delta = (V w).1 - (V (w - 1)).1 := by
  classical
  let init := ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate
  let I := ReferenceInitializationRun.output init
  let s := ReferenceInitializationRun.elapsed p I.completed
  let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
    rate source rewards C_star C_h hcross count hspan
  let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records
  let w := W.length
  let B := ReferenceCollectionPhaseHistory.collectionWindow E.records w
  let u := s + w + 1
  let cells := ReferenceFirstWindowNumericalStream.actualLiveSourceCells
    rate source rewards C_star C_h hcross count hspan
  let qpar := ReferenceFirstLaunchNumericalCell.queueParameters rate
  change ∀ (n : Fin B.length) (c : ReferenceCollectionSegmentExtraction.Choice rate),
    ReferenceCollectionSegmentExtraction.choice B[n].input = some c → _
  intro n c hchoice
  dsimp only
  let x := B[n].input
  let i := ReferenceActivePhysicalStep.upSenderIndex x
  let a := c.preLedger.assignment.arm i
  let candidate := CoordinatorCollectionLedger.startRoundCandidate c.preLedger x.time
    (ReferenceActivePhysicalStep.collectionEnabled c.preLedger x.time)
    (ReferenceCollectionRawBufferHistory.rawDiagnostic B[n])
  let A := fun X : List (RecordedQueueRun.RoundInput p.K) =>
    X.map (fun z => (z.enabled, RecordedQueueRun.quantizedArrival qpar z a))
  let V := fun h => QueueReplay.replay (4 * rate.n) (0, 0) (A (cells.take h))
  intro M hparse haccept
  have hWitness := actual_first_collection_parsed_up_payload_source
    rate source rewards C_star C_h count hcross hspan hshort n c hchoice M hparse haccept
  rcases hWitness with
    ⟨P0, birth, d, message, hbirthMember, hbirthInstall, hbirthTime,
      hP0Choice, hmessageP0, hmessageQ, hretained, hdBound, hMSigma,
      _hMS, _hMq, _hMdelta, _hledgerAssignment⟩
  have hfields := actual_first_collection_parsed_up_canonical_replay_fields
    rate source rewards C_star C_h count hcross hspan hshort n c hchoice M hparse haccept
  rcases hfields with ⟨hscore, hqueue, hdelta⟩
  exact ⟨P0, birth, d, message, hbirthMember, hbirthInstall, hbirthTime,
    hP0Choice, hmessageP0, hmessageQ, hretained, hdBound, hMSigma,
    hscore, hqueue, hdelta⟩

end Bandits.Support.ReferenceFirstCollectionParsedUpCanonicalCutoff

end
