/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionReadyStream
public import Bandits.Support.ReferenceAllKnownCollectionSampleInstall

import Lean.Elab.Tactic.Omega

/-!
# First empty pending boundary and its actual next dispatch

The initialized stream producer consumes the actual finite first-collection
window through any finite accepted or rejected UP prefix.  At its first empty
pending ledger, this module identifies the same actual accepted FINISH, builds
the next original-prefix round input when that round is below the horizon, and
applies the admitted all-known dispatch classifier at that boundary.  A
nonempty final ledger is reported only as finite-window exhaustion.

Sources: `sources/zip4/manuscript/06_interruptions.tex:9-100,246-299`,
`sources/zip4/manuscript/04_slow_fast_learner.tex:97-174,176-215`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-79`.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions

namespace Bandits.Support.ReferenceFirstCollectionStreamEmptyDispatch

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput
abbrev RewardTable := ActualInitializationPhysicalStep.GridRewardTable
abbrev Record (p : Parameters) (rate : RateInput p) :=
  ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)
abbrev Payload {p : Parameters} (rate : RateInput p) :=
  ReferenceActivePhysicalStep.Payload rate
abbrev Ledger {p : Parameters} (rate : RateInput p) :=
  ReferenceActivePhysicalStep.Ledger rate

variable {p : Parameters} {rate : RateInput p}

private theorem connected_append_first_input
    {initial middle final : ReferenceActivePhysicalStep.State p rate}
    (pref : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (rest : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (hfull : ReferenceActivePhysicalHorizon.Connected initial
      (pref ++ record :: rest) final)
    (hprefix : ReferenceActivePhysicalHorizon.Connected initial pref middle) :
    record.input.state = middle := by
  induction pref generalizing initial middle with
  | nil =>
      have hfull' : record.input.state = initial ∧
          ReferenceActivePhysicalHorizon.Connected record.output.next rest final := by
        simpa only [List.nil_append, ReferenceActivePhysicalHorizon.Connected] using hfull
      have hprefix' : middle = initial := by
        simpa only [ReferenceActivePhysicalHorizon.Connected] using hprefix
      exact hfull'.1.trans hprefix'.symm
  | cons head tail ih =>
      have hfull' : head.input.state = initial ∧
          ReferenceActivePhysicalHorizon.Connected head.output.next
            (tail ++ record :: rest) final := by
        simpa only [List.cons_append, ReferenceActivePhysicalHorizon.Connected] using hfull
      have hprefix' : head.input.state = initial ∧
          ReferenceActivePhysicalHorizon.Connected head.output.next tail middle := by
        simpa only [ReferenceActivePhysicalHorizon.Connected] using hprefix
      exact ih hfull'.2 hprefix'.2

private theorem activeRoundInput_ext
    {left right : ReferenceActivePhysicalStep.RoundInput p rate}
    (hstate : left.state = right.state) (hrows : left.rows = right.rows)
    (hselected : left.selected = right.selected) (htime : left.time = right.time)
    (hrewards : left.rewards = right.rewards) : left = right := by
  cases left
  cases right
  simp_all

/-- The final actual round record ends at the computed state of its canonical
prefix. -/
private theorem run_last_record_output
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : RewardTable p) (start count : ℕ)
    (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hcount : 0 < count)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hget : (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count
      hspan hmode).records[count - 1]? = some record) :
    record.output.next = (ReferenceActivePhysicalHorizon.run initial rows selected rewards
      start count hspan hmode).finalState := by
  let entry : ReferenceActivePhysicalHorizon.CalendarEntry p start :=
    ⟨start + (count - 1), by omega⟩
  have hstep := ReferenceActivePhysicalHorizon.run_successor_step initial rows selected
    rewards start (count - 1) (by omega) hmode
  have hstep' : ReferenceActivePhysicalHorizon.run initial rows selected rewards start
      count hspan hmode =
      ReferenceActivePhysicalHorizon.foldRound initial rows selected rewards start hmode
        (ReferenceActivePhysicalHorizon.run initial rows selected rewards start
          (count - 1) (by omega) hmode) entry := by
    simpa only [Nat.sub_add_cancel hcount] using hstep
  have hrecords :
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count
        hspan hmode).records =
        (ReferenceActivePhysicalHorizon.run initial rows selected rewards start (count - 1)
          (by omega) hmode).records ++
          [⟨ReferenceActivePhysicalHorizon.roundInputAt initial rows selected rewards start
              hmode
              (ReferenceActivePhysicalHorizon.run initial rows selected rewards start
                (count - 1) (by omega) hmode) entry,
            ReferenceActivePhysicalStep.step
              (ReferenceActivePhysicalHorizon.roundInputAt initial rows selected rewards start
                hmode
                (ReferenceActivePhysicalHorizon.run initial rows selected rewards start
                  (count - 1) (by omega) hmode) entry), rfl⟩] := by
    rw [hstep']
    rfl
  have hprevLength := ReferenceActivePhysicalHorizon.run_record_count initial rows selected
    rewards start (count - 1) (by omega) hmode
  have hrecord : record =
      ⟨ReferenceActivePhysicalHorizon.roundInputAt initial rows selected rewards start hmode
          (ReferenceActivePhysicalHorizon.run initial rows selected rewards start
            (count - 1) (by omega) hmode) entry,
        ReferenceActivePhysicalStep.step
          (ReferenceActivePhysicalHorizon.roundInputAt initial rows selected rewards start
            hmode
            (ReferenceActivePhysicalHorizon.run initial rows selected rewards start
              (count - 1) (by omega) hmode) entry), rfl⟩ := by
    rw [hrecords] at hget
    simpa [hprevLength] using hget.symm
  rw [hrecord, hstep']
  rfl

private theorem run_record_time_at
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : RewardTable p) (start count : ℕ)
    (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (n : ℕ) (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hget : (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count
      hspan hmode).records[n]? = some record) :
    record.input.time.val = start + n := by
  obtain ⟨hn, _⟩ := List.getElem?_eq_some_iff.mp hget
  have hcount := ReferenceActivePhysicalHorizon.run_record_count initial rows selected
    rewards start count hspan hmode
  have hn' : n < count := by rw [hcount] at hn; exact hn
  have htimes := ReferenceActivePhysicalHorizon.run_time_values initial rows selected
    rewards start count hspan hmode
  have h := congrArg (fun xs : List ℕ => xs[n]?) htimes
  rw [List.getElem?_map, hget] at h
  simpa only [ReferenceActivePhysicalHorizon.calendar, List.getElem?_range' hn',
    ↓reduceIte, Nat.one_mul, Option.map_some, Option.some.injEq] using h

/-- The literal output proposition of the admitted all-known boundary
classifier, made nameable for carrying its exact alternatives in this
producer's result. -/
abbrev actualAllKnownCollectionNextDispatchCases
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : Payload rate) (l : Ledger rate)
    (saved : Option (Fin p.T × Bool)) : Prop :=
  ∃ cutoff : Fin p.T, cutoff.val + 1 = l.cutoff ∧
    let clock := ReferenceActivePhysicalStep.collectionClock payload l saved cutoff
    let input := ReferenceActivePhysicalStep.collectionInput x payload l clock cutoff
    ∃ core : CoordinatorRoundDispatch.CollectionCoreValid input,
    ∃ started : CoordinatorPhaseClock.StartRoundResult p,
    ∃ hstart : CoordinatorPhaseClock.startRound p rate.eta.val x.time clock l.pending =
      .ok started,
    ∃ instruction : CoordinatorPhaseClock.AssignmentStartInstruction p,
    ∃ hassignment : started.assignmentStart = some instruction,
    let operationLedger := CoordinatorRoundDispatch.collectionOperationLedger input
      core.payload_n_eq
    ∃ consistent : LaterAssignmentStartOperation.LocalConsistency input.payload
      operationLedger,
    instruction.time = x.time ∧
    instruction.kind = AssignmentScoreReconstruction.expectedLaterStartKind
      operationLedger.freezeAt instruction.time ∧
    (ReferenceActivePhysicalStep.prepare x).coordinator =
      .collection payload l clock cutoff (CoordinatorRoundDispatch.dispatchCollection input) ∧
    (AssignmentScoreReconstruction.reconstructLaterStart operationLedger instruction =
        .failure .previousOutputDomain ↔
      instruction.time.val + 1 < l.freezeAt ∧
        ∃ a c, l.cutoffRegisters a = some c ∧ c.score < c.lastService) ∧
    ((∃ a c, l.cutoffRegisters a = some c ∧ c.score < c.lastService ∧
        ∃ hrec : AssignmentScoreReconstruction.reconstructLaterStart operationLedger
          instruction = .failure .previousOutputDomain,
        instruction.kind = .corrected ∧
        CoordinatorRoundDispatch.dispatchCollection input =
          .laterReconstructionFailure core consistent started hstart instruction hassignment
            .previousOutputDomain
            (LaterAssignmentStartOperation.laterAssignmentStart_reconstructionFailure
              input.payload operationLedger instruction input.row consistent
              .previousOutputDomain hrec)) ∨
     ∃ out : AssignmentScoreReconstruction.ReconstructedStart operationLedger instruction,
     AssignmentScoreReconstruction.reconstructLaterStart operationLedger instruction =
        .success operationLedger instruction out ∧
     ((∃ hcutoffReached : operationLedger.cutoff ≤ instruction.time.val + 1,
        ∃ hcurrentPos : ∀ i, 0 < AssignmentScoreReconstruction.currentWeight out i,
        ∃ law : LaterAssignmentStartOperation.SelectedLaw input.payload operationLedger
          instruction out,
        ∃ arm : Fin p.K, ∃ reason : CheckedPrefixSampler.FailureReason,
        instruction.kind = .corrected ∧
        LaterAssignmentStartOperation.selectLaw? input.payload operationLedger instruction out
          hcutoffReached hcurrentPos = some law ∧
        ∃ previous, AssignmentScoreReconstruction.previousWeight out = some previous ∧
          (∀ i, 0 < previous i) ∧ law.anchor = input.payload.anchor ∧
          (∀ S, law.mass S = LaterAssignmentStartOperation.correctedRawMass
            input.payload operationLedger instruction out previous hcutoffReached S) ∧
        ∃ hlater : LaterAssignmentStartOperation.laterAssignmentStart input.payload
          operationLedger instruction input.row consistent = .prefixFailure (some arm) reason,
        CheckedAssignmentSample.checkedAssignmentSample p law.mass law.anchor
          (LaterAssignmentStartOperation.ownAssignmentVector input.row instruction.time) =
            .prefixFailure (some arm) reason ∧
        ∃ state : PrefixSetSampler.PrefixState p.K p.m,
          CheckedPrefixSampler.runCheckedPrefix law.mass
            (PrefixSamplerLaw.prefixValues
              (LaterAssignmentStartOperation.ownAssignmentVector input.row instruction.time))
            arm.val (Nat.le_of_lt arm.isLt) = .ready state ∧
          CheckedPrefixSampler.checkedStep law.mass
            ((PrefixSamplerLaw.prefixValues
              (LaterAssignmentStartOperation.ownAssignmentVector input.row instruction.time)) arm)
            state arm = .failed arm reason ∧
          0 < CheckedPrefixSampler.rawStateMass law.mass state ∧
          ((reason = .probabilityBelowZero ∧
              CheckedPrefixSampler.rawIncludedMass law.mass state arm /
                CheckedPrefixSampler.rawStateMass law.mass state < 0) ∨
           (reason = .probabilityAboveOne ∧
              1 < CheckedPrefixSampler.rawIncludedMass law.mass state arm /
                CheckedPrefixSampler.rawStateMass law.mass state)) ∧
        CoordinatorRoundDispatch.dispatchCollection input =
          .laterPrefixFailure core consistent started hstart instruction hassignment
            (some arm) reason hlater) ∨
      ∃ output : LaterAssignmentStartOperation.SuccessfulStart input.payload operationLedger
        instruction input.row,
      ∃ hlocal : output.localConsistency = consistent,
      ∃ clockData : CoordinatorAssignmentRegisterInstall.LaterStartRoundEvidence output,
      ∃ installation : CoordinatorAssignmentRegisterInstall.LaterInstallation output clockData,
      ∃ selection : CoordinatorRoundDispatch.ArmSelection installation.registers.payload
        started instruction.time installation.registers.complementWeights input.row,
        installation = CoordinatorAssignmentRegisterInstall.installLater output clockData ∧
        CoordinatorLocalArmChoice.coordinatorArmChoice installation.registers.payload
          started.pending
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
          instruction.time installation.registers.complementWeights input.row =
            some selection.arm ∧
        output.reconstruction = out ∧
        LaterAssignmentStartOperation.laterAssignmentStart input.payload operationLedger
          instruction input.row consistent = .success output hlocal ∧
        CoordinatorRoundDispatch.dispatchCollection input =
          .laterChosen core consistent started hstart instruction hassignment output hlocal
            clockData installation selection ∧
        LaterAssignmentStartOperation.selectLaw? input.payload operationLedger instruction
          output.reconstruction output.cutoffReached output.currentWeight_pos =
            some output.law ∧
        output.assignmentVector = LaterAssignmentStartOperation.ownAssignmentVector
          input.row instruction.time ∧
        CheckedAssignmentSample.checkedAssignmentSample p output.law.mass output.law.anchor
          output.assignmentVector = .sampled output.outcome ∧
        output.slowSet.1 = output.outcome.1.1.1.erase output.outcome.1.2 ∧
        Finset.univ.image output.payload.assignment.assigned = output.slowSet.1 ∧
        StrictMono output.payload.assignment.assigned ∧
        (output.payload.assignment.auxiliary ∈
          CanonicalFastSampling.fastArmFinset output.slowSet ∧
          (∀ j, j ∈ CanonicalFastSampling.fastArmFinset output.slowSet →
            output.payload.anchor output.payload.assignment.auxiliary ≤ output.payload.anchor j) ∧
          ∀ j, j ∈ CanonicalFastSampling.fastArmFinset output.slowSet →
            output.payload.anchor output.payload.assignment.auxiliary = output.payload.anchor j →
              output.payload.assignment.auxiliary ≤ j) ∧
        (∀ a, output.payload.queues a =
          AssignmentScoreReconstruction.initialQueue output.reconstruction a) ∧
        (∀ i, output.baseScore i = AssignmentScoreReconstruction.sourceScore
          output.reconstruction (output.payload.assignment.assigned i)) ∧
        (∀ i : ActiveRoundActions.Follower p.m,
          installation.retainedBaseScore i =
            AssignmentScoreReconstruction.sourceScore output.reconstruction
              (output.payload.assignment.assigned i)) ∧
        (instruction.kind = .corrected →
          instruction.time.val + 1 < output.localConsistency.oldFreezeAt ∧
          ∃ previous, AssignmentScoreReconstruction.previousWeight output.reconstruction =
            some previous ∧ (∀ i, 0 < previous i) ∧
            output.payload.anchor = input.payload.anchor ∧
            ∀ S, output.law.mass S = LaterAssignmentStartOperation.correctedRawMass
              input.payload operationLedger instruction output.reconstruction previous
                output.cutoffReached S) ∧
        (instruction.kind = .renewal →
          AssignmentScoreReconstruction.previousScore output.reconstruction = none ∧
          AssignmentScoreReconstruction.previousWeight output.reconstruction = none ∧
          output.localConsistency.oldFreezeAt ≤ instruction.time.val + 1 ∧
          output.payload.anchor = AssignmentScoreReconstruction.currentWeight
            output.reconstruction ∧
          (∀ S, output.law.mass S = LaterAssignmentStartOperation.renewalRawMass
            output.reconstruction S) ∧
          ∀ vector : CheckedAssignmentSample.AssignmentVector p,
            ∃ outcome, CheckedAssignmentSample.checkedAssignmentSample p output.law.mass
              output.law.anchor vector = .sampled outcome) ∧
        (∀ i : ActiveRoundActions.Follower p.m,
          (output.payload.downRecord i).val =
            ⟨instruction.time.val + 1,
              (output.payload.assignment.assigned i).val + 1,
              output.payload.assignment.auxiliary.val + 1,
              output.payload.exponent (output.payload.assignment.assigned i),
              AssignmentScoreReconstruction.initialQueue output.reconstruction
                (output.payload.assignment.assigned i)⟩) ∧
        (∀ i : ActiveRoundActions.Follower p.m,
          OrdinaryMessageCodec.dyadicRate (output.payload.downRecord i).val.h =
            CanonicalRecordingRates.xi p rate.eta.val output.payload.anchor
              (output.payload.assignment.assigned i))))

/-- All exact local hypotheses passed to the repeated-admission classifier,
together with its complete result and named current START/reconstruction
data. The classifier result retains its corrected-ratio failure alternative,
its later checked-sample/install alternative, and its renewal consequence. -/
structure ActualNextDispatch
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : Payload rate) (l : Ledger rate)
    (saved : Option (Fin p.T × Bool)) where
  actualState : x.state.coordinator = .collection payload l saved
  validLedger : CoordinatorCollectionLedger.validLedgerCheck l = true
  readyPhase : l.phase = CoordinatorCollectionLedger.Phase.ready
  sigma : l.sigma = payload.sigma.val + 1
  order : l.sigma < l.cutoff
  cutoffBeforeCursor : l.cutoff < l.cursor
  cursor : l.cursor = x.time.val + 1
  freeze : l.freezeAt = FollowerCutoffScan.gridBoundary p rate.eta.val payload.sigma
  assignment : l.assignment.arm = payload.assignment.assigned
  emptyPending : l.pending = ∅
  unitAnchor : ∀ a, payload.anchor a = 1
  currentMassBounds : ∀ a c q, l.cutoffRegisters a = some c →
    l.currentRegisters a = some q →
    c.score + l.increment a + q.queue ≤ (l.cursor - l.sigma) * ConstructorDimensions.D p
  currentServiceSpan : ∀ a c q, l.cutoffRegisters a = some c →
    l.currentRegisters a = some q →
    c.score + l.increment a ≤ 4 * rate.n * (min l.cursor l.freezeAt - l.sigma)
  nextBankCheck : CoordinatorUpReception.decoderBankCheck p x.state.upDecoderBank = true
  /-- The exact theorem result, including the clock start, assignment
  instruction, previous-output-domain iff, exhaustive dispatch alternatives,
  payload and operation ledger, own assignment vector, successful sample and
  installation identities, and renewal-success consequence. -/
  classification : actualAllKnownCollectionNextDispatchCases
      x payload l saved
  cutoffTime : Fin p.T
  cutoffTimeEq : cutoffTime.val + 1 = l.cutoff
  core : CoordinatorRoundDispatch.CollectionCoreValid
    (ReferenceActivePhysicalStep.collectionInput x payload l
      (ReferenceActivePhysicalStep.collectionClock payload l saved cutoffTime) cutoffTime)
  started : CoordinatorPhaseClock.StartRoundResult p
  startCheck : CoordinatorPhaseClock.startRound p rate.eta.val x.time
      (ReferenceActivePhysicalStep.collectionClock payload l saved cutoffTime) l.pending =
    .ok started
  instruction : CoordinatorPhaseClock.AssignmentStartInstruction p
  assignmentStart : started.assignmentStart = some instruction
  operationLedger : LaterAssignmentStartOperation.LocalLedger
      (ReferenceActivePhysicalStep.collectionInput x payload l
        (ReferenceActivePhysicalStep.collectionClock payload l saved cutoffTime) cutoffTime).payload :=
    CoordinatorRoundDispatch.collectionOperationLedger
      (ReferenceActivePhysicalStep.collectionInput x payload l
        (ReferenceActivePhysicalStep.collectionClock payload l saved cutoffTime) cutoffTime)
      core.payload_n_eq
  consistent : LaterAssignmentStartOperation.LocalConsistency
    (ReferenceActivePhysicalStep.collectionInput x payload l
      (ReferenceActivePhysicalStep.collectionClock payload l saved cutoffTime) cutoffTime).payload
    operationLedger
  instructionTime : instruction.time = x.time
  expectedKind : instruction.kind =
    AssignmentScoreReconstruction.expectedLaterStartKind operationLedger.freezeAt instruction.time
  preparedCoordinator : (ReferenceActivePhysicalStep.prepare x).coordinator =
    .collection payload l (ReferenceActivePhysicalStep.collectionClock payload l saved cutoffTime)
      cutoffTime (CoordinatorRoundDispatch.dispatchCollection
        (ReferenceActivePhysicalStep.collectionInput x payload l
          (ReferenceActivePhysicalStep.collectionClock payload l saved cutoffTime) cutoffTime))
  correctedFailureIff :
    (AssignmentScoreReconstruction.reconstructLaterStart operationLedger instruction =
        .failure .previousOutputDomain ↔
      instruction.time.val + 1 < l.freezeAt ∧
        ∃ a c, l.cutoffRegisters a = some c ∧ c.score < c.lastService)
  correctedFailureAbsent :
    AssignmentScoreReconstruction.reconstructLaterStart operationLedger instruction ≠
      .failure .previousOutputDomain
  reconstructed : AssignmentScoreReconstruction.ReconstructedStart operationLedger instruction
  reconstructionSuccess :
    AssignmentScoreReconstruction.reconstructLaterStart operationLedger instruction =
      .success operationLedger instruction reconstructed

/-- The physical boundary after the current FINISH either is the terminal
state at `T`, or is the actual round input constructed from the original run
prefix. -/
inductive ActualNextBoundary
    (source : SourceInput p) (rewards : RewardTable p) (C_star C_h : ℝ)
    (count : ℕ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : ReferenceFirstCollectionReadyStream.startTime (rate := rate)
      source rewards C_star C_h + count ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
        source rewards C_star C_h hcross count hspan).records).length < count)
    (out : ReferenceFirstCollectionReadyStream.ActualInitializedStreamOutput
      (p := p) (rate := rate) source rewards C_star C_h count hcross hspan
      hshort)
    (last : Fin out.ell) (ledger : Ledger rate)
    (record : Record p rate)
    (prefixRun : ReferenceActivePhysicalHorizon.Run
      (ReferenceFirstCollectionEpochAlignment.actualLaunchState rate source rewards
        C_star C_h hcross)) : Type where
  | terminal
      (timeAtHorizon : record.input.time.val + 1 = p.T)
      (cursorAtSentinel : ledger.cursor = p.T + 1) :
      ActualNextBoundary source rewards C_star C_h count hcross hspan hshort out last ledger record prefixRun
  | next
      (beforeHorizon : record.input.time.val + 1 < p.T)
      (currentAtOrAfterStart : ReferenceFirstCollectionReadyStream.startTime
        (rate := rate) source rewards C_star C_h ≤ record.input.time.val)
      (x : ReferenceActivePhysicalStep.RoundInput p rate)
      (isOriginalPrefixInput : x = ReferenceActivePhysicalHorizon.roundInputAt
        (ReferenceFirstCollectionEpochAlignment.actualLaunchState rate source rewards
          C_star C_h hcross)
        source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
        (ReferenceFirstCollectionReadyStream.startTime (rate := rate)
          source rewards C_star C_h)
        (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
          rate source rewards C_star C_h hcross).1
        prefixRun ⟨record.input.time.val + 1, by
          exact ⟨by omega, beforeHorizon⟩⟩)
      (stateIsPriorFinish : x.state = record.output.next)
      (timeIsNext : x.time.val = record.input.time.val + 1)
      (rowsAreOriginal : x.rows = source.1.2)
      (selectedIsOriginal : x.selected = ActualInitializationPhysicalStep.selectedRowIndex p source)
      (rewardsAreWhole : x.rewards = rewards)
      (equalsRetainedWindowRecord : ∀ rNext,
        out.window[out.ell]? = some rNext → x = rNext.input)
      (equalsRetainedRunRecord : ∀ rNext,
        (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
          source rewards C_star C_h hcross count hspan).records[
            (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
              (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
                source rewards C_star C_h hcross count hspan).records).length + out.ell]? =
          some rNext → x = rNext.input)
      (dispatch : ActualNextDispatch x out.payload ledger out.saved) :
      ActualNextBoundary source rewards C_star C_h count hcross hspan hshort out last ledger record prefixRun

/-- Data at the first empty-pending selected output. The produced current cell,
its incoming ready input, accepted FINISH, actual prefix state, and either the
terminal sentinel or fully classified next input all refer to the same record. -/
structure EmptyPendingBoundary
    (source : SourceInput p) (rewards : RewardTable p) (C_star C_h : ℝ)
    (count : ℕ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : ReferenceFirstCollectionReadyStream.startTime (rate := rate)
      source rewards C_star C_h + count ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
        source rewards C_star C_h hcross count hspan).records).length < count)
    (out : ReferenceFirstCollectionReadyStream.ActualInitializedStreamOutput
      (p := p) (rate := rate) source rewards C_star C_h count hcross hspan hshort)
    (last : Fin out.ell) (ledger : Ledger rate) (record : Record p rate) where
  pendingEmpty : ledger.pending = ∅
  lastPositive : 0 < last.val
  allEarlierNonempty : ∀ earlier : Fin out.ell, earlier.val + 1 < out.ell →
    (out.ledgers earlier).pending.Nonempty
  currentRecord : out.window[last.val]? = some record
  incomingLedger : Ledger rate
  cell : ReferenceFirstCollectionReadyStream.ContinuingStreamCell source rewards
    (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
      source rewards C_star C_h hcross count hspan).records
    ((ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
        source rewards C_star C_h hcross count hspan).records).length + last.val)
    count
    (ReferenceFirstCollectionReadyStream.startTime (rate := rate)
      source rewards C_star C_h)
    record out.payload incomingLedger out.saved
  cellLedger : cell.serviceLedger = ledger
  incomingIsPrevious : incomingLedger = out.ledgers
    ⟨last.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) last.isLt⟩
  readyInput : ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain
    record.input out.payload incomingLedger out.saved
  actualFailureNone : record.output.coordinator.failure = none
  actualNextCoordinator : record.output.next.coordinator =
    .collection out.payload ledger out.saved
  actualContext : cell.serviceLedger.sigma = incomingLedger.sigma ∧
    cell.serviceLedger.cutoff = incomingLedger.cutoff ∧
    cell.serviceLedger.freezeAt = incomingLedger.freezeAt ∧
    cell.serviceLedger.assignment = incomingLedger.assignment ∧
    cell.serviceLedger.baseScore = incomingLedger.baseScore
  allKnownRegisters : ∀ a,
    (∃ q, ledger.currentRegisters a = some q) ∧
    ∃ c, ledger.cutoffRegisters a = some c
  cutoffLastService : ∀ a c, ledger.cutoffRegisters a = some c →
    c.lastService ≤ c.score ∧ c.lastService ≤ 4 * rate.n
  incrementGrowth : ∀ a,
    ledger.increment a ≤ 4 * rate.n * (min ledger.cursor ledger.freezeAt - ledger.cutoff)
  actualAcceptedFinish : ∃ M : OrdinaryMessageCodec.UpRecord
      (CoordinatorCollectionLedger.codecParams p rate.eta.val),
    ∃ hparse : ReferenceCollectionSegmentExtraction.effectiveParse record.input cell.started = some M,
    ∃ haccept : CoordinatorCollectionLedger.acceptUpCheck cell.started
      (ReferenceActivePhysicalStep.upSenderIndex record.input) M = true,
    ∃ result : ReferenceFirstCollectionAcceptedReadyStep.AcceptedFinishOutput source rewards
      (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
        source rewards C_star C_h hcross count hspan).records
      ((ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
          source rewards C_star C_h hcross count hspan).records).length + last.val)
      count
      (ReferenceFirstCollectionReadyStream.startTime (rate := rate)
        source rewards C_star C_h)
      record out.payload incomingLedger out.saved cell.choice cell.recording cell.started M,
      cell.branch = .accepted hparse haccept result ∧ result.finished = ledger
  prefixRun : ReferenceActivePhysicalHorizon.Run
    (ReferenceFirstCollectionEpochAlignment.actualLaunchState rate source rewards
      C_star C_h hcross)
  prefixRunSpan : ReferenceFirstCollectionReadyStream.startTime (rate := rate)
      source rewards C_star C_h +
      ((ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
          source rewards C_star C_h hcross count hspan).records).length + out.ell) ≤ p.T
  prefixRunIsOriginal : prefixRun = ReferenceActivePhysicalHorizon.run
    (ReferenceFirstCollectionEpochAlignment.actualLaunchState rate source rewards
      C_star C_h hcross)
    source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
    (ReferenceFirstCollectionReadyStream.startTime (rate := rate)
      source rewards C_star C_h)
    ((ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
        source rewards C_star C_h hcross count hspan).records).length + out.ell)
    prefixRunSpan
    (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
      rate source rewards C_star C_h hcross).1
  prefixStateIsActual : prefixRun.finalState = record.output.next
  nextBoundary : ActualNextBoundary source rewards C_star C_h count hcross hspan hshort
    out last ledger record prefixRun

/-- Either finite-window exhaustion with the original ready boundary, or the
first empty-pending FINISH with its same-ledger numerical bounds and next
physical boundary. -/
inductive FinalBoundary
    (source : SourceInput p) (rewards : RewardTable p) (C_star C_h : ℝ)
    (count : ℕ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : ReferenceFirstCollectionReadyStream.startTime (rate := rate)
      source rewards C_star C_h + count ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
        source rewards C_star C_h hcross count hspan).records).length < count)
    (out : ReferenceFirstCollectionReadyStream.ActualInitializedStreamOutput
      (p := p) (rate := rate) source rewards C_star C_h count hcross hspan hshort)
    (last : Fin out.ell) (ledger : Ledger rate) (record : Record p rate) : Type where
  | exhausted
      (pendingNonempty : ledger.pending.Nonempty)
      (windowExhausted : out.ell = out.window.length)
      (cutoffLastService : ∀ a c, ledger.cutoffRegisters a = some c →
        c.lastService ≤ c.score ∧ c.lastService ≤ 4 * rate.n)
      (incrementGrowth : ∀ a,
        ledger.increment a ≤ 4 * rate.n * (min ledger.cursor ledger.freezeAt - ledger.cutoff))
      (boundary : ReferenceFirstCollectionReadyStream.Boundary source rewards
        (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
          source rewards C_star C_h hcross count hspan).records
        ((ReferenceFirstLiveConfirmationHistory.firstLiveWindow
          (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
            source rewards C_star C_h hcross count hspan).records).length + last.val)
        record out.payload ledger out.saved) :
      FinalBoundary source rewards C_star C_h count hcross hspan hshort out last ledger record
  | empty (data : EmptyPendingBoundary source rewards C_star C_h count hcross hspan hshort
      out last ledger record) :
      FinalBoundary source rewards C_star C_h count hcross hspan hshort out last ledger record

/-- Produced initialized stream, exact final FINISH record, and exhaustive
pending-boundary alternatives. -/
structure ActualInitializedStreamDispatch
    (source : SourceInput p) (rewards : RewardTable p) (C_star C_h : ℝ)
    (count : ℕ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : ReferenceFirstCollectionReadyStream.startTime (rate := rate)
      source rewards C_star C_h + count ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
        source rewards C_star C_h hcross count hspan).records).length < count) where
  stream : ReferenceFirstCollectionReadyStream.ActualInitializedStreamOutput
    (p := p) (rate := rate) source rewards C_star C_h count hcross hspan hshort
  last : Fin stream.ell
  lastIsLast : last.val + 1 = stream.ell
  ledger : Ledger rate
  ledgerIsLast : ledger = stream.ledgers last
  record : Record p rate
  recordAt : stream.window[last.val]? = some record
  actualFailureNone : record.output.coordinator.failure = none
  actualNextCoordinator : record.output.next.coordinator =
    .collection stream.payload ledger stream.saved
  cutoffLastService : ∀ a c, ledger.cutoffRegisters a = some c →
    c.lastService ≤ c.score ∧ c.lastService ≤ 4 * rate.n
  incrementGrowth : ∀ a,
    ledger.increment a ≤ 4 * rate.n * (min ledger.cursor ledger.freezeAt - ledger.cutoff)
  allEarlierNonempty : ∀ earlier : Fin stream.ell, earlier.val + 1 < stream.ell →
    (stream.ledgers earlier).pending.Nonempty
  outcome : FinalBoundary source rewards C_star C_h count hcross hspan hshort
    stream last ledger record

/-- The exact stream telescope, followed by an output containing its first
empty boundary and the actual next dispatch classification. -/
theorem actual_initialized_first_collection_stream_empty_dispatch
    (rate : RateInput p) (source : SourceInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (count : ℕ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : ReferenceFirstCollectionReadyStream.startTime (rate := rate)
      source rewards C_star C_h + count ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
        source rewards C_star C_h hcross count hspan).records).length < count) :
    Nonempty (ActualInitializedStreamDispatch source rewards C_star C_h count hcross hspan hshort) := by
  classical
  let out := Classical.choice
    (ReferenceFirstCollectionReadyStream.actual_initialized_first_collection_ready_stream
      (rate := rate) source rewards C_star C_h hcross count hspan hshort)
  have hout : ReferenceFirstCollectionReadyStream.ActualInitializedStreamOutput
      (p := p) (rate := rate) source rewards C_star C_h count hcross hspan hshort :=
    Classical.choice
      (ReferenceFirstCollectionReadyStream.actual_initialized_first_collection_ready_stream
        (rate := rate) source rewards C_star C_h hcross count hspan hshort)
  let last : Fin out.ell := ⟨out.ell - 1, by have h := out.positiveLength; omega⟩
  have hlast : last.val + 1 = out.ell := by
    have hpositive := out.positiveLength
    simp only [last]
    omega
  let ledger : Ledger rate := out.ledgers last
  obtain ⟨record, hrecord, hfailure, hnext, hvalid, hphase, hcursor, hgamma,
    hcut, hinc⟩ := out.output_properties last
  have hpendingCase := Finset.eq_empty_or_nonempty ledger.pending
  have hcutFinal := hcut
  have hincFinal : ∀ a,
      ledger.increment a ≤ 4 * rate.n * (min ledger.cursor ledger.freezeAt - ledger.cutoff) := by
    intro a
    exact hinc a
  have hlastEarlier : ∀ earlier : Fin out.ell, earlier.val + 1 < out.ell →
      (out.ledgers earlier).pending.Nonempty :=
    fun earlier hbefore => out.pending_before_last earlier hbefore
  rcases hpendingCase with hempty | hpending
  · have hlastPositive : 0 < last.val := by
      by_contra hnot
      have hzero : last.val = 0 := by omega
      have hlastZero : last = (⟨0, by omega⟩ : Fin out.ell) := Fin.ext hzero
      have hledgerZero : out.ledgers (⟨0, by omega⟩ : Fin out.ell) =
          out.cutoff.ledger := by
        simpa using out.ledgers_are_outputs (⟨0, by omega⟩ : Fin out.ell)
      have hfirst : ledger = out.cutoff.ledger := by
        simpa [ledger, hlastZero] using hledgerZero
      have hnonempty := out.cutoffPendingNonempty
      rw [← hfirst] at hnonempty
      exact (Finset.nonempty_iff_ne_empty.mp hnonempty) (by simpa [ledger] using hempty)
    obtain ⟨j, cellRecord, incoming, cell, hj, hcellRecord, hserviceLedger, hprevious⟩ :=
      out.cell_at last hlastPositive
    subst j
    have hrecordEq : cellRecord = record := Option.some.inj (hcellRecord.symm.trans hrecord)
    subst cellRecord
    have hcellEmpty : cell.serviceLedger.pending = ∅ := by
      rw [hserviceLedger]
      exact hempty
    have hallKnown :=
      ReferenceFirstCollectionReadyStream.cell_all_known_when_empty cell hcellEmpty
    have hcellProperties := cell.output_properties
    have hserviceValid : CoordinatorCollectionLedger.validLedgerCheck ledger = true := by
      simpa [hserviceLedger] using hcellProperties.2.1
    have hserviceReady : ledger.phase = CoordinatorCollectionLedger.Phase.ready := by
      simpa [hserviceLedger] using hcellProperties.2.2.1
    have hserviceCursor : ledger.cursor = record.input.time.val + 2 := by
      simpa [hserviceLedger] using hcellProperties.2.2.2.1
    have hready := cell.readyInput
    rcases hready with ⟨_hReadyState, _hReadyPhase, _hSigmaGe, _hSigmaLe,
      hOrder, hSigma, _hCutGe, _hCutLe, _hCutFreeze, _hFreezeLe, hFreeze,
      hIncomingCursor, hCutCursor, _hIncomingCursorLe, hAssign, _hBase, hAnchor,
      _hn, _hIncomingPending, _hRegisters, _hGamma, _hCutMass, _hCurrentMass,
      _hCurrentService, _hRaw, _hHistory, _hBankDomains⟩
    have hcontext := cell.context
    have hsigmaSame : ledger.sigma = incoming.sigma := by
      simpa [hserviceLedger] using cell.context.1
    have hcutoffSame : ledger.cutoff = incoming.cutoff := by
      simpa [hserviceLedger] using cell.context.2.1
    have hOrderFinal : ledger.sigma < ledger.cutoff := by
      rw [hsigmaSame, hcutoffSame]
      exact hOrder
    have hSigmaFinal : ledger.sigma = out.payload.sigma.val + 1 := by
      calc
        ledger.sigma = incoming.sigma := hsigmaSame
        _ = out.payload.sigma.val + 1 := hSigma
    have hcutFinalCursor : ledger.cutoff < ledger.cursor := by
      have hcutIn : ledger.cutoff < incoming.cursor := by
        rw [hcutoffSame]
        exact hCutCursor
      rw [hIncomingCursor] at hcutIn
      rw [hserviceCursor]
      rw [hcutoffSame]
      omega
    have hfreezeFinal : ledger.freezeAt = FollowerCutoffScan.gridBoundary
        p rate.eta.val out.payload.sigma := by
      calc
        ledger.freezeAt = incoming.freezeAt := by
          simpa [hserviceLedger] using cell.context.2.2.1
        _ = FollowerCutoffScan.gridBoundary p rate.eta.val out.payload.sigma := hFreeze
    have hassignmentFinal : ledger.assignment.arm = out.payload.assignment.assigned := by
      have hassignSame : ledger.assignment = incoming.assignment := by
        simpa [hserviceLedger] using cell.context.2.2.2.1
      rw [hassignSame]
      exact hAssign
    have hacceptedProof : ∃ M : OrdinaryMessageCodec.UpRecord
        (CoordinatorCollectionLedger.codecParams p rate.eta.val),
        ∃ hparse : ReferenceCollectionSegmentExtraction.effectiveParse record.input cell.started =
          some M,
        ∃ haccept : CoordinatorCollectionLedger.acceptUpCheck cell.started
          (ReferenceActivePhysicalStep.upSenderIndex record.input) M = true,
        ∃ result : ReferenceFirstCollectionAcceptedReadyStep.AcceptedFinishOutput source rewards
          (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
            source rewards C_star C_h hcross count hspan).records
          ((ReferenceFirstLiveConfirmationHistory.firstLiveWindow
            (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
              source rewards C_star C_h hcross count hspan).records).length + last.val)
          count
          (ReferenceFirstCollectionReadyStream.startTime (rate := rate)
            source rewards C_star C_h)
          record out.payload incoming out.saved cell.choice cell.recording cell.started M,
          cell.branch = .accepted hparse haccept result ∧ result.finished = ledger := by
      cases hbranch : cell.branch with
      | accepted hparse haccept result =>
          have hfinish : result.finished = ledger := by
            have hs := cell.serviceLedgerIsBranch
            rw [hbranch] at hs
            simpa [ReferenceFirstCollectionReadyStream.ContinuingBranchOutput.finished]
              using hs.symm.trans hserviceLedger
          exact ⟨_, hparse, haccept, result, rfl, hfinish⟩
      | rejected hreject result =>
          have hfinish : result.finished = ledger := by
            have hs := cell.serviceLedgerIsBranch
            rw [hbranch] at hs
            simpa [ReferenceFirstCollectionReadyStream.ContinuingBranchOutput.finished]
              using hs.symm.trans hserviceLedger
          have hnonempty := result.finished_pending_nonempty
          rw [hfinish] at hnonempty
          exact False.elim ((Finset.nonempty_iff_ne_empty.mp hnonempty) hempty)
    have hacceptedOutput := hacceptedProof
    obtain ⟨M, hparse, haccept, acceptedResult, hbranchAccepted, hfinish⟩ := hacceptedProof
    let start := ReferenceFirstCollectionReadyStream.startTime (rate := rate)
      source rewards C_star C_h
    let epoch := ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
      source rewards C_star C_h hcross count hspan
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow epoch.records).length
    let k := w + out.ell
    have hcurrentIndex : last.val < out.window.length :=
      Nat.lt_of_lt_of_le last.isLt out.withinWindow
    let currentIndex : Fin out.window.length := ⟨last.val, hcurrentIndex⟩
    have hcurrentAlignment := out.alignment currentIndex
    have hwindowValue : out.window[currentIndex.val]'currentIndex.isLt = record := by
      apply Option.some.inj
      exact (List.getElem?_eq_getElem currentIndex.isLt).symm.trans hrecord
    have htime : record.input.time.val + 1 = start + k := by
      have ht : record.input.time.val + 1 = start + w + 1 + last.val := by
        simpa [currentIndex, hwindowValue] using hcurrentAlignment.2
      have hlast' : last.val + 1 = out.ell := hlast
      dsimp [start, w, k, ReferenceFirstCollectionReadyStream.startTime] at ht ⊢
      omega
    have hprefixSpan : start + k ≤ p.T := by
      calc
        start + k = record.input.time.val + 1 := htime.symm
        _ ≤ p.T := Nat.succ_le_of_lt record.input.time.isLt
    have hcountEpoch : epoch.records.length = count := by
      dsimp [epoch, ReferenceFirstCollectionReadyStream.actualEpoch,
        ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun]
      exact ReferenceActivePhysicalHorizon.run_record_count
        (ReferenceFirstCollectionEpochAlignment.actualLaunchState rate source rewards
          C_star C_h hcross)
        source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
        start count hspan
        (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
          rate source rewards C_star C_h hcross).1
    have hgetEpoch : epoch.records[w + last.val]? = some record := by
      simpa [epoch, w] using hcurrentAlignment.1.trans (congrArg some hwindowValue)
    have hprefixCount : k ≤ count := by
      have hindex := (List.getElem?_eq_some_iff.mp hgetEpoch).1
      dsimp [k, w] at hindex
      omega
    have hmode := (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
      rate source rewards C_star C_h hcross).1
    let initial := ReferenceFirstCollectionEpochAlignment.actualLaunchState rate source rewards
      C_star C_h hcross
    let prefixRun := ReferenceActivePhysicalHorizon.run initial source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start k hprefixSpan hmode
    have hepochRecords : epoch.records =
        (ReferenceActivePhysicalHorizon.run initial source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source)
          rewards start count hspan hmode).records := by
      dsimp [epoch, initial, start, ReferenceFirstCollectionReadyStream.actualEpoch,
        ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun]
    obtain ⟨suffix, hrunPrefix⟩ := ReferenceCollectionPhaseHistory.run_records_prefix
      initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
      start k (count - k) (by omega) hmode
    have hcountSplit : k + (count - k) = count := Nat.add_sub_of_le hprefixCount
    have hrunPrefix' : epoch.records = prefixRun.records ++ suffix := by
      simpa [epoch, prefixRun, initial, start, ReferenceFirstCollectionReadyStream.actualEpoch,
        ReferenceFirstCollectionReadyStream.startTime,
        ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun, hcountSplit] using hrunPrefix
    have hprefixLength : prefixRun.records.length = k :=
      ReferenceActivePhysicalHorizon.run_record_count initial source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start k hprefixSpan hmode
    have hlastIndex : w + last.val = k - 1 := by dsimp [k, w]; omega
    have hgetPrefix : prefixRun.records[k - 1]? = some record := by
      have hgetEpoch' := hgetEpoch
      rw [hrunPrefix'] at hgetEpoch'
      rw [List.getElem?_append_left (by rw [hprefixLength]; omega)] at hgetEpoch'
      simpa [hlastIndex] using hgetEpoch'
    have hprefixState : prefixRun.finalState = record.output.next := by
      have hlastState := run_last_record_output initial source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start k
        hprefixSpan hmode (by omega) record hgetPrefix
      exact hlastState.symm
    have hcutoffBounds : ∀ a c, ledger.cutoffRegisters a = some c →
        c.lastService ≤ c.score := fun a c hc => (hcutFinal a c hc).1
    have hmass : ∀ a c q, ledger.cutoffRegisters a = some c →
        ledger.currentRegisters a = some q →
        c.score + ledger.increment a + q.queue ≤
          (ledger.cursor - ledger.sigma) * ConstructorDimensions.D p := by
      intro a c q hc hq
      have hcut' : acceptedResult.finished.cutoffRegisters a = some c := by
        simpa [hfinish] using hc
      have hcurrent' : acceptedResult.finished.currentRegisters a = some q := by
        simpa [hfinish] using hq
      have hb := acceptedResult.currentMassBounds a c q hcut' hcurrent'
      rw [hfinish] at hb
      rw [hserviceCursor, hsigmaSame]
      simpa [hfinish] using hb
    have hservice : ∀ a c q, ledger.cutoffRegisters a = some c →
        ledger.currentRegisters a = some q →
        c.score + ledger.increment a ≤
          4 * rate.n * (min ledger.cursor ledger.freezeAt - ledger.sigma) := by
      intro a c q hc hq
      have hcut' : acceptedResult.finished.cutoffRegisters a = some c := by
        simpa [hfinish] using hc
      have hcurrent' : acceptedResult.finished.currentRegisters a = some q := by
        simpa [hfinish] using hq
      have hb := acceptedResult.currentServiceSpanBound a c q hcut' hcurrent'
      rw [hfinish] at hb
      have hfreezeSame : ledger.freezeAt = incoming.freezeAt := by
        simpa [hserviceLedger] using cell.context.2.2.1
      rw [hserviceCursor, hfreezeSame, hsigmaSame]
      simpa [hfinish] using hb
    have hprefixEq : prefixRun = ReferenceActivePhysicalHorizon.run initial
        source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
        start k hprefixSpan hmode := rfl
    have hterminal : record.input.time.val + 1 = p.T ∨ record.input.time.val + 1 < p.T := by
      omega
    rcases hterminal with htimeTerminal | htimeBefore
    · have hcursorTerminal : ledger.cursor = p.T + 1 := by
        rw [hcursor]
        omega
      refine ⟨{
        stream := out
        last := last
        lastIsLast := hlast
        ledger := ledger
        ledgerIsLast := rfl
        record := record
        recordAt := hrecord
        actualFailureNone := hfailure
        actualNextCoordinator := by simpa [ledger] using hnext
        cutoffLastService := hcutFinal
        incrementGrowth := hincFinal
        allEarlierNonempty := hlastEarlier
        outcome := .empty {
          pendingEmpty := hempty
          lastPositive := hlastPositive
          allEarlierNonempty := hlastEarlier
          currentRecord := hrecord
          incomingLedger := incoming
          cell := cell
          cellLedger := hserviceLedger
          incomingIsPrevious := hprevious
          readyInput := cell.readyInput
          actualFailureNone := hfailure
          actualNextCoordinator := by simpa [ledger] using hnext
          actualContext := cell.context
          allKnownRegisters := by simpa [hserviceLedger] using hallKnown
          cutoffLastService := hcutFinal
          incrementGrowth := hincFinal
          actualAcceptedFinish := hacceptedOutput
          prefixRun := prefixRun
          prefixRunSpan := hprefixSpan
          prefixRunIsOriginal := hprefixEq
          prefixStateIsActual := hprefixState
          nextBoundary := .terminal htimeTerminal hcursorTerminal
        }
      }⟩
    · let x : ReferenceActivePhysicalStep.RoundInput p rate :=
        ReferenceActivePhysicalHorizon.roundInputAt initial source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start hmode
          prefixRun ⟨record.input.time.val + 1, by
            constructor
            · have htime' := htime
              dsimp [k, w, start, ReferenceFirstCollectionReadyStream.startTime] at htime'
              omega
            · exact htimeBefore⟩
      have hrecordAfterStart : start ≤ record.input.time.val := by
        have htime' := htime
        dsimp [k, w, start, ReferenceFirstCollectionReadyStream.startTime] at htime'
        omega
      have hstateX : x.state = record.output.next := by
        change prefixRun.finalState = record.output.next
        exact hprefixState
      have htimeX : x.time.val = record.input.time.val + 1 := rfl
      have hstateRoot : x.state.coordinator = .collection out.payload ledger out.saved := by
        rw [hstateX]
        simpa [ledger] using hnext
      have hcursorRoot : ledger.cursor = x.time.val + 1 := by
        omega
      have hbankRoot : CoordinatorUpReception.decoderBankCheck p x.state.upDecoderBank = true := by
        rw [hstateX, acceptedResult.actualNextBank]
        exact (CoordinatorUpReception.decoderBankCheck_eq_true_iff p acceptedResult.bank).2
          acceptedResult.decoderBankWellFormed
      have hclassification :=
        ReferenceAllKnownCollectionSampleInstall.all_known_collection_next_dispatch_cases
          x out.payload ledger out.saved hstateRoot hserviceValid hserviceReady hSigmaFinal
          hOrderFinal hcutFinalCursor hcursorRoot hfreezeFinal hassignmentFinal hempty hAnchor
          hmass hservice hbankRoot
      have hclassificationResult := hclassification
      rcases hclassificationResult with ⟨cutoff, hcutoffFin, core, started, hstart, instruction,
        hassignment, consistent, htimeInstruction, hkind, hprepared, hiff, hcases⟩
      let operationLedger := CoordinatorRoundDispatch.collectionOperationLedger
        (ReferenceActivePhysicalStep.collectionInput x out.payload ledger
          (ReferenceActivePhysicalStep.collectionClock out.payload ledger out.saved cutoff)
          cutoff) core.payload_n_eq
      have hcorrectedAbsent :
          AssignmentScoreReconstruction.reconstructLaterStart operationLedger instruction ≠
            .failure .previousOutputDomain := by
        intro hfailure'
        have hbad := hiff.mp hfailure'
        rcases hbad.2 with ⟨a, c, hc, hscore⟩
        have hordered := hcutoffBounds a c hc
        omega
      rcases hcases with hbad | hsuccess
      · rcases hbad with ⟨a, c, hc, hscore, _⟩
        have horderService := hcutoffBounds a c hc
        exact False.elim (by omega)
      · rcases hsuccess with ⟨reconstructed, hreconstruction, _remainingCases⟩
        have hdispatch : ActualNextDispatch x out.payload ledger out.saved := {
          actualState := hstateRoot
          validLedger := hserviceValid
          readyPhase := hserviceReady
          sigma := hSigmaFinal
          order := hOrderFinal
          cutoffBeforeCursor := hcutFinalCursor
          cursor := hcursorRoot
          freeze := hfreezeFinal
          assignment := hassignmentFinal
          emptyPending := hempty
          unitAnchor := hAnchor
          currentMassBounds := hmass
          currentServiceSpan := hservice
          nextBankCheck := hbankRoot
          classification := hclassification
          cutoffTime := cutoff
          cutoffTimeEq := hcutoffFin
          core := core
          started := started
          startCheck := hstart
          instruction := instruction
          assignmentStart := hassignment
          operationLedger := operationLedger
          consistent := consistent
          instructionTime := htimeInstruction
          expectedKind := hkind
          preparedCoordinator := hprepared
          correctedFailureIff := hiff
          correctedFailureAbsent := hcorrectedAbsent
          reconstructed := reconstructed
          reconstructionSuccess := hreconstruction
        }
        have hretainedEpoch : ∀ rNext, epoch.records[k]? = some rNext →
            x = rNext.input := by
          intro rNext hget
          have hgetSuffix : suffix[0]? = some rNext := by
            rw [hrunPrefix'] at hget
            rw [List.getElem?_append_right (by simpa [hprefixLength])] at hget
            simpa [k, hprefixLength] using hget
          have hgetRun := hget
          rw [hepochRecords] at hgetRun
          cases suffix with
          | nil => simp at hgetSuffix
          | cons first rest =>
              have hfirst : first = rNext := by simpa using hgetSuffix
              subst first
              have hfullConnected0 := ReferenceActivePhysicalHorizon.run_connected
                initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
                rewards start count hspan hmode
              have hfullConnected := hfullConnected0
              rw [← hepochRecords] at hfullConnected
              have hprefixConnected := ReferenceActivePhysicalHorizon.run_connected
                initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
                rewards start k hprefixSpan hmode
              rw [hrunPrefix'] at hfullConnected
              have hrecordState := connected_append_first_input prefixRun.records
                rNext rest hfullConnected hprefixConnected
              have hmem : rNext ∈
                  (ReferenceActivePhysicalHorizon.run initial source.1.2
                    (ActualInitializationPhysicalStep.selectedRowIndex p source)
                    rewards start count hspan hmode).records := by
                exact List.mem_iff_getElem?.mpr ⟨k, hgetRun⟩
              have hinputRows := ReferenceActivePhysicalHorizon.run_record_inputs
                initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
                rewards start count hspan hmode rNext hmem
              have hrecordTime := run_record_time_at initial source.1.2
                (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
                start count hspan hmode k rNext hgetRun
              have heq : x = rNext.input := by
                have hstateEq : x.state = rNext.input.state := by
                  calc
                    x.state = record.output.next := hstateX
                    _ = prefixRun.finalState := hprefixState.symm
                    _ = rNext.input.state := hrecordState.symm
                have hrowsEq : x.rows = rNext.input.rows := by
                  change source.1.2 = rNext.input.rows
                  exact hinputRows.1.symm
                have hselectedEq : x.selected = rNext.input.selected := by
                  change ActualInitializationPhysicalStep.selectedRowIndex p source =
                    rNext.input.selected
                  exact hinputRows.2.1.symm
                have htimeValue : x.time.val = rNext.input.time.val := by
                  calc
                    x.time.val = record.input.time.val + 1 := htimeX
                    _ = start + k := htime
                    _ = rNext.input.time.val := hrecordTime.symm
                have htimeEq : x.time = rNext.input.time := Fin.ext htimeValue
                have hrewardsEq : x.rewards = rNext.input.rewards := by
                  change rewards = rNext.input.rewards
                  exact hinputRows.2.2.symm
                exact activeRoundInput_ext hstateEq hrowsEq hselectedEq htimeEq hrewardsEq
              exact heq
        have hretainedWindow : ∀ rNext, out.window[out.ell]? = some rNext →
            x = rNext.input := by
          intro rNext hgetWindow
          have hnextFin : out.ell < out.window.length :=
            (List.getElem?_eq_some_iff.mp hgetWindow).1
          have hnextAlignment := out.alignment ⟨out.ell, hnextFin⟩
          have hwindowNext : out.window[out.ell] = rNext := by
            apply Option.some.inj
            exact (List.getElem?_eq_getElem hnextFin).symm.trans hgetWindow
          have hgetEpochNext : epoch.records[k]? = some rNext := by
            simpa only [epoch, w, k] using hnextAlignment.1.trans (congrArg some hwindowNext)
          exact hretainedEpoch rNext hgetEpochNext
        refine ⟨{
          stream := out
          last := last
          lastIsLast := hlast
          ledger := ledger
          ledgerIsLast := rfl
          record := record
          recordAt := hrecord
          actualFailureNone := hfailure
          actualNextCoordinator := by simpa [ledger] using hnext
          cutoffLastService := hcutFinal
          incrementGrowth := hincFinal
          allEarlierNonempty := hlastEarlier
          outcome := .empty {
            pendingEmpty := hempty
            lastPositive := hlastPositive
            allEarlierNonempty := hlastEarlier
            currentRecord := hrecord
            incomingLedger := incoming
            cell := cell
            cellLedger := hserviceLedger
            incomingIsPrevious := hprevious
            readyInput := cell.readyInput
            actualFailureNone := hfailure
            actualNextCoordinator := by simpa [ledger] using hnext
            actualContext := hcontext
            allKnownRegisters := by simpa [hserviceLedger] using hallKnown
            cutoffLastService := hcutFinal
            incrementGrowth := hincFinal
            actualAcceptedFinish := hacceptedOutput
            prefixRun := prefixRun
            prefixRunSpan := hprefixSpan
            prefixRunIsOriginal := hprefixEq
            prefixStateIsActual := hprefixState
            nextBoundary := .next htimeBefore hrecordAfterStart x rfl hstateX htimeX rfl rfl rfl
              hretainedWindow hretainedEpoch hdispatch
          }
        }⟩
  · have hwindowExhausted : out.ell = out.window.length := by
      by_contra hnot
      have hlt : out.ell < out.window.length :=
        Nat.lt_of_le_of_ne out.withinWindow hnot
      have hemptyLast := out.last_empty_of_not_exhausted hlt
      have hledgerEmpty : ledger.pending = ∅ := by
        simpa [ledger, last] using hemptyLast
      exact (Finset.nonempty_iff_ne_empty.mp hpending) hledgerEmpty
    obtain ⟨boundaryRecord, hboundaryRecord, boundary⟩ := out.boundary_at last
    have hboundaryEq : boundaryRecord = record := Option.some.inj (hboundaryRecord.symm.trans hrecord)
    subst boundaryRecord
    exact ⟨{
      stream := out
      last := last
      lastIsLast := hlast
      ledger := ledger
      ledgerIsLast := rfl
      record := record
      recordAt := hrecord
      actualFailureNone := hfailure
      actualNextCoordinator := by simpa [ledger] using hnext
      cutoffLastService := hcutFinal
      incrementGrowth := hincFinal
      allEarlierNonempty := hlastEarlier
      outcome := .exhausted hpending hwindowExhausted hcutFinal hincFinal boundary
    }⟩

end Bandits.Support.ReferenceFirstCollectionStreamEmptyDispatch

end
