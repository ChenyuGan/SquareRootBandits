/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstUnacceptedDownEpoch
public import Bandits.Support.ReferenceFollowerDownWindowCompletedCut

/-!
# The actual first-live second awaited DOWN batch is ambiguous on nonacceptance

Sources: `sources/zip4/manuscript/05_binary_transport.tex:36-124`,
`sources/zip4/manuscript/06_interruptions.tex:164-177,246-295`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:92-109,151-157`.

The source-root theorem joins the actual unaccepted first-live sender producer
to the actual completed-window cut. Its count equation is a branch selector
inside the conclusion. It proves neither count attainment nor a probability,
measurability, delivery, global decoding, or regret result.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceFirstDownAwaitedAmbiguity

open ConstructorDimensions ReferenceActivePhysicalStep
open ReferencePrelaunchFollower (acceptedStart)

variable {p : Parameters}

private theorem consumed_matching_accepted_down_has_lastDown
    {rate : RateInput p}
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (time : Fin p.T) (observation : ReferencePrelaunchFollower.Observation p)
    (logged post : ReferencePrelaunchFollower.State p rate.eta)
    (word : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (message : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hselected : ActiveFollowerDownAcceptance.downSelected p i row time)
    (hstatus : logged.status = .unoccupied)
    (hregisters : ActiveFollowerDownAcceptance.registerInputDomain p rate logged)
    (hbatch : ActiveFollowerDownAcceptance.decoderInputDomain p logged.downBatch)
    (hbuffer : ActiveFollowerDownAcceptance.bufferInputDomain p logged.buffer)
    (hdecoded : (ActiveFollowerDownAcceptance.currentDecodeStep
      p i row time observation rate logged).2 = some word)
    (hexpected : ReferenceDownReception.expectedDownFlatWord view i row time = some word)
    (hparse : ReferenceDownReception.ordinaryParse p rate (some word) = some message)
    (haccept : OrdinaryMessageCodec.acceptDown
      (ReferencePrelaunchFollower.codecParams p rate.eta) (acceptedStart logged)
      (time.val + 1) message)
    (hconsume : DeclaredFollowerLocalRound.consumeDownResult rate
      (ReferenceDownReception.referenceDownCut p view i row time observation rate logged).outcome =
        .ok post) :
    post.lastDown = some message := by
  classical
  let decoded := ActiveFollowerDownAcceptance.currentDecodeStep p i row time observation rate logged
  let scan := ActiveFollowerDownAcceptance.acceptedCutoffScan p rate message time
    (ActiveFollowerDownAcceptance.acceptedDownStartLE p rate message time logged haccept) row
  cases hchecked : ActiveFollowerDownAcceptance.checkedRecovery p rate message logged scan.endpoint with
  | error failure =>
      have hcut : (ReferenceDownReception.referenceDownCut p view i row time observation rate logged).outcome =
          .outputFailure logged (.replay failure) := by
        simp [ReferenceDownReception.referenceDownCut, scan, hselected, hstatus,
          hregisters, hbatch, hbuffer, hdecoded, hexpected, hparse, haccept, hchecked]
      rw [hcut, DeclaredFollowerLocalRound.consumeDownResult] at hconsume
      cases hconsume
  | ok recovered =>
      let after := { {logged with downBatch := decoded.1} with
        lastDown := some message
        S := recovered.registers.1
        delta := recovered.lastService
        backlog := recovered.registers.2
        status := if scan.endpoint = time.val + 2 then .pending else .unoccupied
        buffer := [] }
      have hcut : (ReferenceDownReception.referenceDownCut p view i row time observation rate logged).outcome =
          .accepted logged after decoded.2 message scan recovered.registers recovered.lastService := by
        simp [ReferenceDownReception.referenceDownCut, decoded, scan, after, hselected, hstatus,
          hregisters, hbatch, hbuffer, hdecoded, hexpected, hparse, haccept, hchecked]
      rw [hcut, DeclaredFollowerLocalRound.consumeDownResult] at hconsume
      injection hconsume with hpost
      subst post
      simp [after]

section ActualLaunch

/-- On the actual launched-boundary first-live branch, if its actual second
completed awaited DOWN window is selected, the transmitted word solves every
original positive sample but the actual decoder returned no word. The same
completion record retains its real logging, raw comparison, parser, and local
acceptance checks. -/
theorem ofActualLaunchedBoundary_first_down_second_awaited_ambiguity :
    ∀ {p : Parameters}
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (rate : ReferenceActivePhysicalStep.RateInput p) (C_star C_h : ℝ)
    (boundary : ReferenceInitializationRun.Boundary p)
    (hboundary : boundary.completed < BootstrapDimensions.n_boot p)
    (actual : ActualInitializationRun.BlockCarry p rate
      (ReferenceInitializationRun.nextBlock boundary hboundary))
    (past : List (ActualInitializationRun.PhysicalRoundRecord p rate source rewards))
    (hr : ActualReferenceInitializationBlock.BlockStartRelated source rewards
      C_star C_h rate (ReferenceInitializationRun.nextBlock boundary hboundary) actual boundary past)
    (hdown : ∀ i, ¬ InitializationFailureProvenance.generatedBlockDown
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
      boundary hboundary i)
    (hclean : ∀ (i : Fin (p.m - 1))
      (hi : ActualReferenceInitializationBlock.refFollower i ∈
        (ReferenceInitializationRun.physical
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
          boundary hboundary).uninformed),
      BootstrapAllCandidateController.cleanPrefix
        (ReferenceInitializationRun.physical
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
          boundary hboundary)
        source.1.2 ⟨ActualReferenceInitializationBlock.refFollower i, hi⟩
        (ActualInitializationPhysicalStep.selectedRowIndex p source) p.T)
    (hforce : ∀ i, ReferenceInitializationRun.forced
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
      boundary hboundary i = false)
    (launch : BootstrapCoordinatorLocalRound.LaunchedBlock p)
    (learnerSeed : ActualInitializationRun.CoordinatorLearnerZeroSeed p)
    (hlaunched : (ActualInitializationRun.combinedBoundaryHandoff p rate
      (ReferenceInitializationRun.nextBlock boundary hboundary) source rewards actual.C_star
      actual.C_h (ActualInitializationRun.foldBlock p rate
        (ReferenceInitializationRun.nextBlock boundary hboundary) source rewards actual)).disposition =
          .launched launch learnerSeed)
    (count : ℕ)
    (span : BootstrapObservedFollower.blockStop p
      (ReferenceInitializationRun.nextBlock boundary hboundary) + count ≤ p.T),
    let initial := ActualInitializationLaunchState.ofActualLaunchedBoundary source rewards rate C_star C_h
      boundary hboundary actual past hr hdown hclean hforce launch learnerSeed hlaunched
    let rows := source.1.2
    let J := ActualInitializationPhysicalStep.selectedRowIndex p source
    let start := BootstrapObservedFollower.blockStop p
      (ReferenceInitializationRun.nextBlock boundary hboundary)
    let mode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start :=
      fun j => ActualInitializationLaunchState.ofActualLaunchedBoundary_activation_le_blockStop
        source rewards rate C_star C_h boundary hboundary actual past hr hdown hclean hforce
        launch learnerSeed hlaunched j
    ∀ (b : ℕ) (hb : b ≤ count)
    (_hwindow : b ≤ (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceActivePhysicalHorizon.run initial rows J rewards start count span mode).records).length)
    (rB : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (qB : CoordinatorLiveServiceFinish.OwnedRegisters rB)
    (baseB : Fin (p.m - 1) → ℕ)
    (_hcoord : (ReferenceActivePhysicalHorizon.run initial rows J rewards start b ((Nat.add_le_add_left hb start).trans span) mode).finalState.coordinator =
      .live rB qB baseB)
    (i : Fin (p.m - 1))
    (sB : ReferencePrelaunchFollower.State p rate.eta)
    (memoryB : ActiveFollowerLifecycle.LocalMemory p)
    (_hfocal : (ReferenceActivePhysicalHorizon.run initial rows J rewards start b ((Nat.add_le_add_left hb start).trans span) mode).finalState.followers i =
      .ordinary sB memoryB)
    (_hnone : sB.lastDown = none),
    let Rb := ReferenceActivePhysicalHorizon.run initial rows J rewards start b ((Nat.add_le_add_left hb start).trans span) mode
    let positives := ReferenceFollowerDownDecoderReplay.actualDownPositives i Rb.records
    ∃ (seed : ReferencePrelaunchFollower.State p rate.eta)
      (seedMemory : ActiveFollowerLifecycle.LocalMemory p),
      initial.followers i = .ordinary seed seedMemory ∧
      let word : AffineChannelLaw.Word (AffineBatchDecoder.width p) :=
        CoordinatorLocalArmChoice.storedDownFlatWord rB.payload i
      let q := AffineBatchDecoder.quota p
      let needed := q - seed.downBatch.pending.length
      let window := positives.drop needed
      ∀ (_hcount : positives.length = needed + q),
        window.length = q ∧
        (∀ entry ∈ window, AffineBatchDecoder.equation entry.sample word) ∧
        (∀ entry ∈ window,
          ∃ sampleRecord : ReferenceFollowerDownDecoderReplay.Record p rate,
            sampleRecord ∈ Rb.records ∧ entry.time = sampleRecord.input.time ∧
            entry.sample = ReferenceDownPhysicalHashRule.originalDownSample sampleRecord.input ∧
            sampleRecord.input.rows = rows ∧ sampleRecord.input.selected = J ∧
            sampleRecord.input.rewards = rewards) ∧
        AffineBatchDecoder.batchOutput window = none ∧
        (∃ other, other ≠ word ∧
          AffineBatchDecoder.satisfies (AffineBatchDecoder.samples window) other) ∧
        ∃ (entry : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p))
          (record : ReferenceFollowerDownDecoderReplay.Record p rate)
          (call : ReferenceFollowerDownDecoderReplay.Call p)
          (logged : ReferencePrelaunchFollower.State p rate.eta)
          (cut : ReferenceDownReception.ReferenceDownCutOutput p rate),
          entry ∈ window ∧ entry.time = record.input.time ∧ record ∈ Rb.records ∧
          ReferenceFollowerDownDecoderReplay.actualDownCall i record = some call ∧
          call.1 = record.input.time ∧ entry.time = call.1 ∧
          0 < (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i).val.val ∧
          (record.output.preparation.observeFollower i).downInput = some logged ∧
          (record.output.preparation.observeFollower i).down = some cut ∧
          (record.output.followers i).downInput = some logged ∧
          (record.output.followers i).down = some cut ∧
          cut.rawComparison.isSome = true ∧
          cut.rawComparison = some false ∧
          cut.raw = AffineBatchDecoder.batchOutput window ∧
          cut.expectedWord = some word ∧
          (ActiveFollowerDownAcceptance.currentDecodeStep p i record.input.row record.input.time
            (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i) rate logged).1 =
              ⟨[], seed.downBatch.completed ++
                [seed.downBatch.pending ++ positives.take needed, window]⟩ ∧
          ReferenceDownReception.ordinaryParse p rate (some word) =
            some (rB.payload.downRecord i) ∧
          OrdinaryMessageCodec.acceptDown (ReferencePrelaunchFollower.codecParams p rate.eta)
            (acceptedStart logged) (record.input.time.val + 1) (rB.payload.downRecord i)

    := by
  intro p source rewards rate C_star C_h boundary hboundary actual past hr hdown hclean hforce
    launch learnerSeed hlaunched count span
  classical
  intro initial rows J start mode b hb hwindow rB qB baseB hcoord i sB memoryB hfocal hnone
    Rb positives
  let full := ReferenceActivePhysicalHorizon.run initial rows J rewards start count span mode
  let calls := ReferenceFollowerDownDecoderReplay.actualDownCalls i Rb.records

  have hEpoch := ReferenceFirstUnacceptedDownEpoch.ofActualLaunchedBoundary_first_unaccepted_down_epoch
    source rewards rate C_star C_h boundary hboundary actual past hr hdown hclean hforce
    launch learnerSeed hlaunched count span
  have hEpochBranch := hEpoch b hb hwindow rB qB baseB hcoord i sB memoryB hfocal hnone
  rcases hEpochBranch with ⟨_hpositiveB, hsender⟩

  have hspanB : start + b ≤ p.T := by
    exact (Nat.add_le_add_left hb start).trans (by simpa only [start] using span)
  have hordinaryB : (ReferenceActivePhysicalHorizon.run initial rows J rewards start b hspanB mode).finalState.followers i =
      .ordinary sB memoryB := by
    simpa only [initial, rows, J, start, mode] using hfocal
  obtain ⟨hmode, _hseed, hcutResult⟩ :=
    ReferenceFollowerDownWindowCompletedCut.run_actualLaunched_interval_down_completed_window_cut
      p source rewards rate C_star C_h boundary hboundary actual past hr hdown hclean hforce
      launch learnerSeed hlaunched 0 b (Nat.zero_le b) hspanB i sB memoryB hordinaryB
  dsimp only [ReferenceFollowerDownWindowCompletedCut.intervalDownCompletedWindowCutResult] at hcutResult
  rcases hcutResult with ⟨seed, seedMemory, hseedState, hconditional⟩
  have hseedInitial : initial.followers i = .ordinary seed seedMemory := by
    simpa only [ReferenceActivePhysicalHorizon.run_zero_final] using hseedState

  refine ⟨seed, seedMemory, hseedInitial, ?_⟩
  intro word q needed window hcount
  have hcountCut :
      (ReferenceFollowerDownDecoderReplay.actualDownPositives i
        ((ReferenceActivePhysicalHorizon.run initial rows J rewards start b (by omega) hmode).records.drop 0)).length =
        (AffineBatchDecoder.quota p - seed.downBatch.pending.length) + AffineBatchDecoder.quota p := by
    simpa only [ReferenceFollowerDownDecoderReplay.actualDownPositives, List.drop_zero,
      positives, Rb, calls, Nat.add_comm] using hcount
  rcases hconditional hcountCut with
    ⟨index, call, completionEntry, record, choice, choiceMemory, logged, postRecord,
      next, nextMemory, hindex, hsplit, hcompletionEntry, hlast, hentryTime, hrecordInterval,
      hactualCall, hcallTime, hprepared, hchoiceStatus, hdownSelected, hpositiveOwn, hown,
      hfinish, hnext, hrecordOk, hrelease, hloggingC, hchoiceBuffer, hloggedBuffer,
      hloggedBatch, hdownInputC, hcutC, hregisterC, hdecoderC, hbufferC, hrawComparisonC,
      hrawWindowC, hindexBound, trace, htrace, prefixState, prefixMemory, hprefixOrdinary,
      hbefore, hprefixBank, hchoiceBank, hchoiceWindow, hloggedWindow, hwindowLength,
      hcurrentBatch⟩

  have hwindowLength' : (positives.drop (AffineBatchDecoder.quota p - seed.downBatch.pending.length)).length =
      AffineBatchDecoder.quota p := by
    have hchoiceWindow' :
        choice.downBatch.pending ++ AffineBatchDecoder.positiveAt p trace call.1 =
          positives.drop (AffineBatchDecoder.quota p - seed.downBatch.pending.length) := by
      simpa only [ReferenceFollowerDownDecoderReplay.actualDownPositives, List.drop_zero,
        positives, Rb, calls] using hchoiceWindow
    calc
      _ = (choice.downBatch.pending ++ AffineBatchDecoder.positiveAt p trace call.1).length :=
        congrArg List.length hchoiceWindow'.symm
      _ = AffineBatchDecoder.quota p := hwindowLength

  have hprefixRecords : Rb.records = full.records.take b := by
    have hprefix : Rb.records.IsPrefix full.records := by
      obtain ⟨suffix, hrecords⟩ := ReferenceCollectionPhaseHistory.run_records_prefix
        initial rows J rewards start b (count - b) (by omega) mode
      exact ⟨suffix, by simpa only [Nat.add_sub_of_le hb] using hrecords.symm⟩
    have htake := List.prefix_iff_eq_take.mp hprefix
    rw [ReferenceActivePhysicalHorizon.run_record_count] at htake
    exact htake

  have hwordEntriesAndOrigins : ∀ entry ∈ positives.drop
      (AffineBatchDecoder.quota p - seed.downBatch.pending.length),
      AffineBatchDecoder.equation entry.sample
        word ∧
      ∃ sampleRecord : ReferenceFollowerDownDecoderReplay.Record p rate,
        sampleRecord ∈ Rb.records ∧ entry.time = sampleRecord.input.time ∧
        entry.sample = ReferenceDownPhysicalHashRule.originalDownSample sampleRecord.input ∧
        sampleRecord.input.rows = rows ∧ sampleRecord.input.selected = J ∧
        sampleRecord.input.rewards = rewards := by
    intro entry hentryWindow
    have hentryPos : entry ∈ positives := List.mem_of_mem_drop hentryWindow
    change entry ∈ ReferenceFollowerDownDecoderReplay.positiveCallEntries calls at hentryPos
    obtain ⟨entryCall, hcallPos, hpositiveAt⟩ := List.mem_flatMap.mp hentryPos
    have hcallMember : entryCall ∈ ReferenceFollowerDownDecoderReplay.actualDownCalls i Rb.records := by
      simpa only [calls] using hcallPos
    change entryCall ∈ Rb.records.filterMap (ReferenceFollowerDownDecoderReplay.actualDownCall i) at hcallMember
    obtain ⟨sourceRecord, hsourceRecord, hactualCallPos⟩ := List.mem_filterMap.mp hcallMember
    have hsourcePrefix : sourceRecord ∈ full.records.take b := by
      rw [← hprefixRecords]
      exact hsourceRecord
    obtain ⟨a, ha, selected, before, beforeMemory, sourceChoice, sourceChoiceMemory,
      sourceNext, sourceNextMemory, htime, hstate, hrows, hJ, hrewards,
      hselectedRecord, hpayload, hpending, hsigma, hbeforeConfiguration,
      hchoiceConfiguration, hnextConfiguration, hbeforeLast, hchoiceLast, hnextLast,
      hbeforeStatus, hchoiceStatus, hnextStatus, hdownFacts⟩ := hsender sourceRecord hsourcePrefix
    have hchoicePrepared :
        ReferenceFollowerDownDecoderReplay.preparedChoiceConfiguration sourceRecord i =
          .ordinary sourceChoice sourceChoiceMemory := by
      simpa only [ReferenceFollowerDownDecoderReplay.preparedChoiceConfiguration] using hchoiceConfiguration
    have hactualCallSpec := Option.some.inj
      (hactualCallPos.symm.trans
        (ReferenceFollowerDownDecoderReplay.actualDownCall_ordinary sourceRecord i
          sourceChoice sourceChoiceMemory hchoicePrepared))
    have hactualInput : entryCall.2 =
        ActiveFollowerDownAcceptance.currentRoundInput p i
          (ReferenceFollowerDownDecoderReplay.preparedChoiceRow sourceRecord i)
          (ReferenceFollowerDownDecoderReplay.preparedChoiceTime sourceRecord i)
          (ReferenceFollowerDownDecoderReplay.preparedOwnObservation sourceRecord i)
          rate sourceChoice := congrArg Prod.snd hactualCallSpec
    have hpositiveInfo : AffineBatchDecoder.eligible entryCall.2 ∧
        entry = AffineBatchDecoder.entry p
          (ActiveFollowerDownAcceptance.currentInputExtension p entryCall.2) entryCall.1 := by
      unfold AffineBatchDecoder.positiveAt at hpositiveAt
      split at hpositiveAt
      · rename_i heligible
        exact ⟨heligible, List.mem_singleton.mp hpositiveAt⟩
      · cases hpositiveAt
    have hinputEligible := hpositiveInfo.1
    have hpositiveEntry := hpositiveInfo.2
    have hsourceHashAndSample : entryCall.2.sample =
        ReferenceDownPhysicalHashRule.originalDownSample sourceRecord.input ∧
        AffineChannelLaw.affineHash
          (ReferenceDownPhysicalHashRule.originalDownSample sourceRecord.input)
          word = 1 := by
      have hrow : ReferenceFollowerDownDecoderReplay.preparedChoiceRow sourceRecord i =
          sourceRecord.input.row := (sourceRecord.output.preparation.follower_alignment i).1
      have htime' := ReferenceFollowerDownDecoderReplay.preparedChoiceTime_eq_recordTime sourceRecord i
      have hinputEligible' : AffineBatchDecoder.eligible
          (ActiveFollowerDownAcceptance.currentRoundInput p i
            (ReferenceFollowerDownDecoderReplay.preparedChoiceRow sourceRecord i)
            (ReferenceFollowerDownDecoderReplay.preparedChoiceTime sourceRecord i)
            (ReferenceFollowerDownDecoderReplay.preparedOwnObservation sourceRecord i) rate sourceChoice) := by
        rw [← hactualInput]
        exact hinputEligible
      rcases (ReferenceFollowerDownDecoderReplay.actualDownCall_eligible_iff
        sourceRecord i sourceChoice).mp hinputEligible' with
        ⟨hdownOnPrepared, _, hpositiveSourcePrepared⟩
      have hpositiveSource : 0 <
          (sourceRecord.output.preparation.feedback.observations
            (PublicDiscreteDraws.followerPlayer p.two_le_m i)).val.val := by
        simpa only [ReferenceFollowerDownDecoderReplay.preparedOwnObservation] using hpositiveSourcePrepared
      have hdownOnSource : ActiveFollowerDownAcceptance.downSelected p i sourceRecord.input.row
          sourceRecord.input.time := by
        simpa only [hrow, htime'] using hdownOnPrepared
      have hsourceFacts := hdownFacts hdownOnSource
      dsimp only at hsourceFacts
      rcases hsourceFacts with ⟨sourceLogged, hsourceLogging, hsourceDownInput,
        hsourceCut, hsourceLast, hsourceUnoccupied, hsourceBank, hsent, hexpected,
        hsourceCutExpected, hsourceParse, hsourceAccept, hsourceRegister, hsourceDecoder,
        hsourceBuffer, hsourceCompared, hsourceRaw, hsourceNext, hsourceInput,
        hsourceSample, hsourceReward, hsourcePreparedTime, hsourceOwnEntry, hhash⟩
      have hcallSample : entryCall.2.sample =
          ReferenceDownPhysicalHashRule.originalDownSample sourceRecord.input := by
        calc
          _ = (ActiveFollowerDownAcceptance.currentRoundInput p i sourceRecord.input.row
              sourceRecord.input.time
              (sourceRecord.output.preparation.feedback.observations
                (PublicDiscreteDraws.followerPlayer p.two_le_m i)) rate sourceChoice).sample := by
            simpa only [hrow, htime', ReferenceFollowerDownDecoderReplay.preparedOwnObservation]
              using congrArg AffineBatchDecoder.RoundInput.sample hactualInput
          _ = (ActiveFollowerDownAcceptance.currentRoundInput p i sourceRecord.input.row
              sourceRecord.input.time
              (sourceRecord.output.preparation.feedback.observations
                (PublicDiscreteDraws.followerPlayer p.two_le_m i)) rate sourceLogged).sample :=
            congrArg AffineBatchDecoder.RoundInput.sample hsourceInput
          _ = _ := hsourceSample
      exact ⟨hcallSample, hhash hpositiveSource⟩
    rcases hsourceHashAndSample with ⟨hinputSample, hsourceHash⟩
    have hentrySample : entry.sample = entryCall.2.sample := by
      simpa [AffineBatchDecoder.entry, ActiveFollowerDownAcceptance.currentInputExtension] using
        congrArg AffineBatchDecoder.Entry.sample hpositiveEntry
    constructor
    · rw [hentrySample, hinputSample]
      exact (AffineBatchDecoder.equation_iff_affineHash _ word).2 hsourceHash
    · refine ⟨sourceRecord, hsourceRecord, ?_, hentrySample.trans hinputSample,
        hrows, hJ, hrewards⟩
      calc
        entry.time = entryCall.1 := congrArg AffineBatchDecoder.Entry.time hpositiveEntry
        _ = ReferenceFollowerDownDecoderReplay.preparedChoiceTime sourceRecord i :=
          congrArg Prod.fst hactualCallSpec
        _ = sourceRecord.input.time :=
          ReferenceFollowerDownDecoderReplay.preparedChoiceTime_eq_recordTime sourceRecord i

  have hwordEntries : ∀ entry ∈ positives.drop
      (AffineBatchDecoder.quota p - seed.downBatch.pending.length),
      AffineBatchDecoder.equation entry.sample word :=
    fun entry hentry => (hwordEntriesAndOrigins entry hentry).1

  have hwordConsistent : AffineBatchDecoder.satisfies
      (AffineBatchDecoder.samples (positives.drop
        (AffineBatchDecoder.quota p - seed.downBatch.pending.length)))
      word :=
    (AffineBatchDecoder.satisfies_samples_iff _ _).2 hwordEntries
  have hcompletionRecord : record ∈ Rb.records := by
    simpa only [List.drop_zero, Rb, initial, rows, J, start, mode] using hrecordInterval
  have hcompletionPrefix : record ∈ full.records.take b := by
    rw [← hprefixRecords]
    exact hcompletionRecord
  obtain ⟨completionOffset, hcompletionOffset, completionSelection,
      completionBefore, completionBeforeMemory, completionSourceChoice,
      completionSourceChoiceMemory, completionSourceNext, completionSourceNextMemory,
      hcompletionSourceTime, hcompletionSourceState, hcompletionRows,
      hcompletionSelectedRow, hcompletionRewards, hcompletionSelection,
      hcompletionPayload, hcompletionPending, hcompletionSigma,
      hcompletionBeforeState, hcompletionSourceChoiceState,
      hcompletionSourceNextState, hcompletionBeforeLast, hcompletionSourceChoiceLast,
      hcompletionSourceNextLast, hcompletionBeforeUnoccupied,
      hcompletionSourceChoiceUnoccupied, hcompletionSourceNextUnoccupied,
      hcompletionDownFacts⟩ := hsender record hcompletionPrefix
  have hcompletionRow : ReferenceFollowerDownDecoderReplay.preparedChoiceRow record i =
      record.input.row := (record.output.preparation.follower_alignment i).1
  have hcompletionTime' := ReferenceFollowerDownDecoderReplay.preparedChoiceTime_eq_recordTime
    record i
  have hcompletionDown : ActiveFollowerDownAcceptance.downSelected p i record.input.row record.input.time := by
    have htmp := hdownSelected
    rw [hcompletionRow, hcompletionTime'] at htmp
    exact htmp
  have hcompletionSourceFacts := hcompletionDownFacts hcompletionDown
  dsimp only at hcompletionSourceFacts
  rcases hcompletionSourceFacts with ⟨actualLogged, hactualLogging, hactualDownInput,
    hactualDown, hactualLast, hactualUnoccupied, hactualBank,
    hactualSent, hactualExpected, hactualCutExpected, hactualParse,
    hactualAccept, hactualRegister, hactualDecoder, hactualBuffer,
    hactualCompared, hactualRaw, hactualNextUpdate, hactualInput,
    hactualSample, hactualReward, hactualPreparedTime, hactualOwnEntry,
    hactualHash⟩
  let actualCut := ReferenceDownReception.referenceDownCut p
    (dispatch record.input).downView i record.input.row record.input.time
    (record.output.preparation.feedback.observations
      (PublicDiscreteDraws.followerPlayer p.two_le_m i)) rate actualLogged
  have hactualChoice : completionSourceChoice = choice := by
    have hconfig : DeclaredFollowerLocalRound.LocalConfiguration.ordinary
        completionSourceChoice completionSourceChoiceMemory =
        .ordinary choice choiceMemory := by
      simpa only [ReferenceFollowerDownDecoderReplay.preparedChoiceConfiguration] using
        hcompletionSourceChoiceState.symm.trans hprepared
    exact (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj hconfig).1
  have hactualLogSame : actualLogged = logged := by
    have hloggingEq : ActiveFollowerLogging.checkedLogging i record.input.row
        (record.input.state.activations i) record.input.time
        ((record.output.preparation.followers.followers i).arm,
          record.output.preparation.feedback.observations
            (PublicDiscreteDraws.followerPlayer p.two_le_m i)) completionSourceChoice =
          .ok logged := by
      simpa only [hcompletionRow, hcompletionTime',
        (record.output.preparation.follower_alignment i).2.2.2,
        ReferenceFollowerDownDecoderReplay.preparedOwnObservation,
        hactualChoice] using hloggingC
    have hsame := hactualLogging.symm.trans hloggingEq
    exact Except.ok.inj hsame
  have hactualView : (dispatch record.input).downView =
      some completionSelection.view := by
    have hselected' : (prepare record.input).coordinator.selection =
        some completionSelection := by
      have hs := hcompletionSelection
      rw [record.output_eq] at hs
      exact hs
    change (prepare record.input).coordinator.selection.map Selection.view = _
    rw [hselected']
    rfl
  have hcompletionView : record.output.preparation.coordinator.downView =
      some completionSelection.view := by
    rw [record.output_eq]
    change (prepare record.input).coordinator.downView = _
    rw [(prepare record.input).coordinator_eq]
    exact hactualView
  have hcutEq : ReferenceDownReception.referenceDownCut p
      record.output.preparation.coordinator.downView i
      (ReferenceFollowerDownDecoderReplay.preparedChoiceRow record i)
      (ReferenceFollowerDownDecoderReplay.preparedChoiceTime record i)
      (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i)
      rate logged = actualCut := by
    dsimp only [actualCut]
    rw [hcompletionView, hcompletionRow, hcompletionTime',
      ReferenceFollowerDownDecoderReplay.preparedOwnObservation, hactualLogSame]
    rw [hactualView]

  have hcutRaw : actualCut.raw =
      AffineBatchDecoder.batchOutput (positives.drop
        (AffineBatchDecoder.quota p - seed.downBatch.pending.length)) := by
    have hraw := hrawWindowC
    rw [hcutEq] at hraw
    simpa only [List.drop_zero, positives, Rb, calls] using hraw
  have hcutExpected : actualCut.expectedWord =
      some word := hactualCutExpected
  have hexpected : ReferenceDownReception.expectedDownFlatWord
      (some completionSelection.view) i record.input.row record.input.time =
        some word := hactualExpected
  have hexpectedActual : ReferenceDownReception.expectedDownFlatWord
      (dispatch record.input).downView i record.input.row record.input.time =
        some word := by
    simpa only [hactualView] using hexpected
  have hparseAccept :
      ReferenceDownReception.ordinaryParse p rate
          (some word) =
        some (rB.payload.downRecord i) ∧
      OrdinaryMessageCodec.acceptDown (ReferencePrelaunchFollower.codecParams p rate.eta)
        (acceptedStart actualLogged) (record.input.time.val + 1)
        (rB.payload.downRecord i) := by
    constructor
    · exact hactualParse
    · exact hactualAccept
  have hactualCutRawCurrent :
      (ActiveFollowerDownAcceptance.currentDecodeStep p i record.input.row
        record.input.time
        (record.output.preparation.feedback.observations
          (PublicDiscreteDraws.followerPlayer p.two_le_m i)) rate actualLogged).2 =
        AffineBatchDecoder.batchOutput (positives.drop
          (AffineBatchDecoder.quota p - seed.downBatch.pending.length)) := by
    calc
      _ = actualCut.raw := hactualRaw.symm
      _ = AffineBatchDecoder.batchOutput (positives.drop
          (AffineBatchDecoder.quota p - seed.downBatch.pending.length)) := hcutRaw
  have hconsumeC : DeclaredFollowerLocalRound.consumeDownResult rate
      (ReferenceDownReception.referenceDownCut p
        record.output.preparation.coordinator.downView i
        (ReferenceFollowerDownDecoderReplay.preparedChoiceRow record i)
        (ReferenceFollowerDownDecoderReplay.preparedChoiceTime record i)
        (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i)
        rate logged).outcome = .ok postRecord := by
    simpa only [ReferenceActivePhysicalStep.recordFollower, dite_eq_left hchoiceStatus,
      hloggingC] using hrecordOk
  have hconsume : DeclaredFollowerLocalRound.consumeDownResult rate actualCut.outcome =
      .ok postRecord := by
    rw [← hcutEq]
    exact hconsumeC
  have hnextE : record.output.next.followers i =
      .ordinary completionSourceNext completionSourceNextMemory := hcompletionSourceNextState
  have hnextC : record.output.next.followers i = .ordinary next nextMemory := hnext
  have hnextEq : next = completionSourceNext := by
    have h := hnextC.symm.trans hnextE
    exact (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj h).1
  have hcompletionNextLast : next.lastDown = none := by
    simpa only [hnextEq] using hcompletionSourceNextLast
  have hreplyFrame := (ReferenceFollowerReplyChronology.releaseAndFinish_frame
    i (ReferenceFollowerDownDecoderReplay.preparedChoiceRow record i)
    (ReferenceFollowerDownDecoderReplay.preparedChoiceTime record i)
    (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i)
    choice postRecord next choiceMemory nextMemory hrelease).1
  have hpostLast : postRecord.lastDown = none := by
    have hlast := congrArg Prod.fst hreplyFrame
    change next.lastDown = postRecord.lastDown at hlast
    calc
      postRecord.lastDown = next.lastDown := hlast.symm
      _ = none := hcompletionNextLast
  have hrawNotSome : AffineBatchDecoder.batchOutput
      (positives.drop (AffineBatchDecoder.quota p - seed.downBatch.pending.length)) ≠
        some word := by
    intro hsome
    have hdecodedSome :
        (ActiveFollowerDownAcceptance.currentDecodeStep p i record.input.row record.input.time
          (record.output.preparation.feedback.observations
            (PublicDiscreteDraws.followerPlayer p.two_le_m i)) rate actualLogged).2 =
          some word := by
      exact hactualCutRawCurrent.trans hsome
    have hacceptedPost := consumed_matching_accepted_down_has_lastDown
      (dispatch record.input).downView i record.input.row record.input.time
      (record.output.preparation.feedback.observations
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)) actualLogged postRecord
      word (rB.payload.downRecord i)
      hcompletionDown hactualUnoccupied hactualRegister hactualDecoder hactualBuffer
      hdecodedSome hexpectedActual hactualParse hactualAccept hconsume
    have hcontradiction := hacceptedPost
    rw [hpostLast] at hcontradiction
    cases hcontradiction
  have hbatchNone : AffineBatchDecoder.batchOutput
      (positives.drop (AffineBatchDecoder.quota p - seed.downBatch.pending.length)) = none := by
    cases houtput : AffineBatchDecoder.batchOutput
        (positives.drop (AffineBatchDecoder.quota p - seed.downBatch.pending.length)) with
    | none => rfl
    | some output =>
        have heq := (AffineBatchDecoder.batchOutput_eq_some_iff _ output).mp houtput |>.2
          word hwordEntries
        exact False.elim (hrawNotSome
          (houtput.trans (congrArg some heq.symm)))
  have hsolutionsNone : AffineBatchDecoder.solve
      (AffineBatchDecoder.samples (positives.drop
        (AffineBatchDecoder.quota p - seed.downBatch.pending.length))) = none := by
    simpa only [AffineBatchDecoder.batchOutput] using hbatchNone
  have hdecodedNone :
      (ActiveFollowerDownAcceptance.currentDecodeStep p i record.input.row record.input.time
        (record.output.preparation.feedback.observations
          (PublicDiscreteDraws.followerPlayer p.two_le_m i)) rate actualLogged).2 = none :=
    hactualCutRawCurrent.trans hbatchNone
  have hcomparison : actualCut.rawComparison = some false := by
    simp only [actualCut, ReferenceDownReception.referenceDownCut,
      dite_eq_left hcompletionDown, dite_eq_left hactualUnoccupied,
      dite_eq_left hactualRegister, dite_eq_left hactualDecoder, dite_eq_left hactualBuffer,
      hdecodedNone, hexpectedActual, reduceCtorEq, dite_false]
  have hcompletedBank :
      (ActiveFollowerDownAcceptance.currentDecodeStep p i record.input.row record.input.time
        (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i) rate actualLogged).1 =
          ⟨[], seed.downBatch.completed ++
            [seed.downBatch.pending ++ positives.take needed, window]⟩ := by
    simpa only [hcompletionRow, hcompletionTime', hactualLogSame, List.drop_zero,
      positives, Rb, needed, q, window] using hcurrentBatch
  have hemptyOrAmbiguous :=
    (AffineBatchDecoder.solve_eq_none_iff_empty_or_ambiguous _).mp hsolutionsNone
  have hother : ∃ other, other ≠ word ∧
      AffineBatchDecoder.satisfies
        (AffineBatchDecoder.samples (positives.drop
          (AffineBatchDecoder.quota p - seed.downBatch.pending.length))) other := by
    rcases hemptyOrAmbiguous with hempty | ⟨u, v, hu, hv, huv⟩
    · exact False.elim (hempty _ hwordConsistent)
    · by_cases huword : u = word
      · exact ⟨v, (fun hvword => huv (huword.trans hvword.symm)), hv⟩
      · exact ⟨u, huword, hu⟩
  have hwindowLengthFinal := hwindowLength'
  have hpreparationDownInput : (record.output.preparation.observeFollower i).downInput =
      some actualLogged := by
    rw [hactualLogSame]
    exact hdownInputC
  have hpreparationDown : (record.output.preparation.observeFollower i).down =
      some actualCut := by
    rw [← hcutEq]
    exact hcutC
  have hactualDownInput' : (record.output.followers i).downInput = some actualLogged := by
    exact hactualDownInput
  have hactualDown' : (record.output.followers i).down = some actualCut := by
    exact hactualDown
  refine ⟨hwindowLengthFinal, hwordEntries,
    (fun entry hentry => (hwordEntriesAndOrigins entry hentry).2), hbatchNone, hother,
    completionEntry, record, call, actualLogged, actualCut,
    hcompletionEntry, hentryTime.trans hcallTime, hcompletionRecord, hactualCall, hcallTime, hentryTime,
    hpositiveOwn, hpreparationDownInput, hpreparationDown,
    hactualDownInput', hactualDown', hactualCompared, hcomparison, hcutRaw, hcutExpected,
    hcompletedBank, hparseAccept.1, hparseAccept.2⟩

end ActualLaunch

end Bandits.Support.ReferenceFirstDownAwaitedAmbiguity

end
