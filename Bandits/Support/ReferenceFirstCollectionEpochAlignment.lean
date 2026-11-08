/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCutoffRecordedService
public import Bandits.Support.ReferenceGeneratedActivePrefixFactor

/-!
# Original-source first collection epoch geometry

Theorems in this file start from the original bootstrap source, the whole
reward grid, and the same unrestricted constants used by corrected launch.
They reuse the actual corrected launch and first-cutoff producers; they do
not introduce a second protocol execution.

Mathematical sources: `sources/zip4/manuscript/06_interruptions.tex:9-100,
192-233,246-295`, `sources/zip4/manuscript/appendix_a_local_protocol.tex:28-64`,
`sources/zip4/manuscript/07_public_setup.tex:127-164`, and
`sources/zip4/manuscript/04_slow_fast_learner.tex:157-174`.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceInitializationRun
open Bandits.Support.ActualReferenceInitializationBlock
open Bandits.Support.ReferenceCorrectedInitializationLaunch
open Bandits.Support.ReferenceGeneratedActivePrefixFactor
open Bandits.Support.ReferenceFirstCutoffOutsideInitialization
open Bandits.Support.ReferenceCollectionSegmentExtraction
open Bandits.Support.ReferenceFirstLiveConfirmationHistory
open Bandits.Support.ReferenceFixedTimeSourceControlCoupling
open Bandits.Support.ReferenceInitializationControlRemainder

namespace Bandits.Support.ReferenceFirstCollectionEpochAlignment

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput

variable {p : Parameters}

/-- The active state is the option payload of the existing corrected-launch
constructor on the original source input. -/
def actualLaunchState (rate : RateInput p) (source : SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true) :
    ReferenceActivePhysicalStep.State p rate :=
  ReferenceCorrectedInitializationLaunch.correctedLaunch rate source rewards C_star C_h |>.get
    ((ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
      rate source rewards C_star C_h).2 hcross)

/-- C provides the actual launch mode and first coordinator constructor. -/
theorem actualLaunchState_first_active (rate : RateInput p)
    (source : SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true) :
    allActiveAtStart (actualLaunchState rate source rewards C_star C_h hcross)
        (ReferenceInitializationRun.elapsed p
          (ReferenceInitializationRun.output
            (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed) ∧
      (actualLaunchState rate source rewards C_star C_h hcross).coordinator = .first := by
  obtain ⟨actual, hactualLaunch, hactualFirst, _, _, _⟩ :=
    ReferenceCorrectedInitializationLaunch.correctedLaunch_coordinator_provenance
      rate source rewards C_star C_h hcross
  have hactualEq : actual = actualLaunchState rate source rewards C_star C_h hcross := by
    unfold actualLaunchState
    exact (Option.get_of_eq_some
      ((ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
        rate source rewards C_star C_h).2 hcross) hactualLaunch).symm
  obtain ⟨active, hactiveLaunch, hactiveMode⟩ :=
    ReferenceCorrectedInitializationLaunch.correctedLaunch_all_active_at_start
      rate source rewards C_star C_h hcross
  have hactiveEq : active = actualLaunchState rate source rewards C_star C_h hcross := by
    exact (Option.some.inj (hactiveLaunch.symm.trans hactualLaunch)).trans hactualEq
  constructor
  · rw [← hactiveEq]
    exact hactiveMode
  · rw [← hactualEq]
    exact hactualFirst

/-- The literal horizon run on C's option payload, original rows, selected
private index, whole rewards, and computed elapsed start. -/
def actualFirstCollectionRun (rate : RateInput p) (source : SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (count : ℕ)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed + count ≤ p.T) :
    ReferenceActivePhysicalHorizon.Run (actualLaunchState rate source rewards C_star C_h hcross) :=
  ReferenceActivePhysicalHorizon.run (actualLaunchState rate source rewards C_star C_h hcross)
    source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
    (ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed)
    count hspan (actualLaunchState_first_active rate source rewards C_star C_h hcross).1

/-- On a nonterminal source boundary, G's fixed-control split constructs the
actual generated seed. The only additional input is the explicit strict
boundary inequality needed to form the source's `Fin T` split coordinate. -/
theorem actualLaunchState_generatedSeed (rate : RateInput p)
    (source : SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hstartLt : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed < p.T) :
    ∃ (t : Fin p.T),
      ∃ (ht : t.val = ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed),
      ∃ (control : ReferenceGeneratedActivePrefixFactor.TimeControl p)
        (remainder : ReferenceGeneratedActivePrefixFactor.Remainder p
          (ActualInitializationPhysicalStep.selectedRowIndex p source) t)
        (hrem : remainder ∈ ReferenceFixedTimeSourceControlCoupling.fixedControlRemainderStratum p
          (ActualInitializationPhysicalStep.selectedRowIndex p source) t)
        (hstart : remainder ∈ ReferenceInitializationControlRemainder.launchStartRemainderEvent
          rate rewards C_star C_h (ActualInitializationPhysicalStep.selectedRowIndex p source) t
          (ReferenceInitializationRun.elapsed p
            (ReferenceInitializationRun.output
              (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed)
          control),
        ReferenceGeneratedActivePrefixFactor.splitSource
            (ActualInitializationPhysicalStep.selectedRowIndex p source) t control remainder = source ∧
          ReferenceGeneratedActivePrefixFactor.generatedActiveSeed rate rewards C_star C_h
            (ActualInitializationPhysicalStep.selectedRowIndex p source) t control remainder hrem
            (ReferenceInitializationRun.elapsed p
              (ReferenceInitializationRun.output
                (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed)
            (by omega) hstart =
              actualLaunchState rate source rewards C_star C_h hcross := by
  let b := ReferenceInitializationRun.output
    (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
  let s := ReferenceInitializationRun.elapsed p b.completed
  let J := ActualInitializationPhysicalStep.selectedRowIndex p source
  let t : Fin p.T := ⟨s, hstartLt⟩
  let split := ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p J t source
  let control := split.1
  let remainder := split.2
  have hrem : remainder ∈ ReferenceFixedTimeSourceControlCoupling.fixedControlRemainderStratum p J t := by
    change PrivateSourceStreams.coordinatorIndex p
      ((ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p J t source).2.2).1.2 = J
    rw [ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_private p J t source]
    change ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p source = J
    rw [ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex]
  have hselected : ActualInitializationPhysicalStep.selectedRowIndex p source = J := rfl
  have hstart : remainder ∈ ReferenceInitializationControlRemainder.launchStartRemainderEvent
      rate rewards C_star C_h J t s control := by
    exact (ReferenceInitializationControlRemainder.launchStartRemainderEvent_iff_source
      rate rewards C_star C_h J t control source hselected s (by rfl)).mpr
      ⟨hcross, rfl⟩
  let seed := ReferenceGeneratedActivePrefixFactor.generatedActiveSeed rate rewards C_star C_h
    J t control remainder hrem s (by rfl) hstart
  have hseedSpec := ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec rate rewards
    C_star C_h J t control remainder hrem s (by rfl) hstart
  have hsplitSource : ReferenceGeneratedActivePrefixFactor.splitSource J t control remainder = source := by
    dsimp [ReferenceGeneratedActivePrefixFactor.splitSource, split, control, remainder]
    exact (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p J t).symm_apply_apply source
  have hseedLaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch rate source rewards C_star C_h =
      some seed := by
    simpa only [hsplitSource] using hseedSpec.1
  obtain ⟨actual, hactualLaunch, _, _, _, _⟩ :=
    ReferenceCorrectedInitializationLaunch.correctedLaunch_coordinator_provenance
      rate source rewards C_star C_h hcross
  have hseedEq : seed = actualLaunchState rate source rewards C_star C_h hcross := by
    have hEq : seed = actual := Option.some.inj (hseedLaunch.symm.trans hactualLaunch)
    have hActualGet : actual = actualLaunchState rate source rewards C_star C_h hcross := by
      unfold actualLaunchState
      exact (Option.get_of_eq_some
        ((ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
          rate source rewards C_star C_h).2 hcross) hactualLaunch).symm
    exact hEq.trans hActualGet
  refine ⟨t, rfl, control, remainder, hrem, hstart, hsplitSource, ?_⟩
  simpa [seed] using hseedEq

/-- The actual-source first-cutoff geometry, with no caller-supplied active
trace. The cutoff branch is selected only by the literal first-live window
length. Its conclusion is O's actual record, dispatch, initializer, checked
ledger, outside-register and first-cutoff certificate.

The conditional span and cutoff selector are the only execution-window
inputs. Terminal launch and exhausted initialization therefore do not gain a
fictitious cut or action at round `T`.
-/
theorem actual_first_collection_epoch_replay (rate : RateInput p)
    (source : SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (count : ℕ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed + count ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (actualFirstCollectionRun rate source rewards C_star C_h hcross count hspan).records).length < count) :
    let start := ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
    let active := actualLaunchState rate source rewards C_star C_h hcross
    let mode := (actualLaunchState_first_active rate source rewards C_star C_h hcross).1
    let execution := actualFirstCollectionRun rate source rewards C_star C_h hcross count hspan
    let window := ReferenceFirstLiveConfirmationHistory.firstLiveWindow execution.records
    let k := window.length
    let prefixRun := ReferenceActivePhysicalHorizon.run active source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start k (by
        have hk : k < count := by simpa [k, window, execution, actualFirstCollectionRun] using hshort
        omega) mode
    ∃ cut suffix,
      execution.records = window ++ cut :: suffix ∧
      cut.input.time.val = start + k ∧
      ∃ (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
        (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
        (base : Fin (p.m - 1) → ℕ),
        cut.input.state = prefixRun.finalState ∧
        prefixRun.finalState.coordinator = .live r q base ∧
        let callInput := ReferenceActivePhysicalStep.liveInput cut.input r q base;
        ∃ (dispatched : CoordinatorStartRoundCutoffDispatch.Output
            callInput.registers callInput.ownedRegisters base)
          (hstart : CoordinatorPhaseClock.startRound p rate.eta.val
            callInput.registers.time callInput.registers.priorClock
            callInput.registers.clockPending =
              .ok dispatched.startResult)
          (ledger : CoordinatorStartRoundCutoffDispatch.NewLedger
            callInput.registers)
          (hinit : dispatched.collectionInitialization = .success (some ledger))
          (hledger : ledger = CoordinatorStartRoundCutoffDispatch.collectionStartLedger
            callInput.registers callInput.ownedRegisters base callInput.registers.time)
          (hdomain : CoordinatorStartRoundCutoffDispatch.initializationDomainValid
            callInput.registers callInput.ownedRegisters base callInput.registers.time)
          (hclock : dispatched.startResult.clock =
            {callInput.registers.priorClock with u := some callInput.registers.time})
          (hpending : dispatched.startResult.pending = Finset.univ)
          (hnoAssignment : dispatched.startResult.assignmentStart = none)
          (selected : CoordinatorRoundDispatch.ArmSelection
            callInput.registers.payload
            dispatched.startResult
            callInput.registers.time callInput.registers.complementWeights
            cut.input.row),
          cut.output.preparation.coordinator = .live r q base
            (.cutoffChosen dispatched hstart ledger hinit hledger hdomain hclock hpending
              hnoAssignment selected) ∧
          k > 0 ∧
          r.payload.sigma.val = start ∧
          (∀ i : Fin (p.m - 1), base i = 0) ∧
          (let u := start + k + 1;
            u ≤ p.T ∧ u ≤ r.gridBoundary ∧ r.gridBoundary ≤ p.T + 1 ∧
            r.gridBoundary = FollowerCutoffScan.gridBoundary p rate.eta.val r.payload.sigma ∧
            (∀ _i : Fin (p.m - 1),
              FollowerCutoffScan.firstCutoff p rate.eta.val r.payload.sigma
                (FollowerCutoffScan.completeRowProposalBit p rate.eta.val (source.1.2
                  (ActualInitializationPhysicalStep.selectedRowIndex p source))) = u) ∧
            ledger.sigma = r.payload.sigma.val + 1 ∧ ledger.cutoff = u ∧
            ledger.freezeAt = r.gridBoundary ∧
            ∃ (initializer : ReferenceCollectionSegmentExtraction.Initializer p)
              (choice : ReferenceCollectionSegmentExtraction.Choice rate),
              initializer = ReferenceCollectionSegmentExtraction.cutoffInitializer
                callInput.registers callInput.ownedRegisters base callInput.registers.time ∧
              ReferenceCollectionSegmentExtraction.choice cut.input = some choice ∧
              choice.initializer = some initializer ∧
              initializer.checkedStart rate = .success
                (ReferenceActivePhysicalStep.sharedLedger ledger)) := by
  let start := ReferenceInitializationRun.elapsed p
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
  let active := actualLaunchState rate source rewards C_star C_h hcross
  have hstartLt : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed < p.T := by
    have hnonempty : 0 < count := by omega
    omega
  obtain ⟨t, ht, control, remainder, hrem, hlaunchStart, hsource, hseedEq⟩ :=
    actualLaunchState_generatedSeed rate source rewards C_star C_h hcross hstartLt
  let seed := ReferenceGeneratedActivePrefixFactor.generatedActiveSeed rate rewards C_star C_h
    (ActualInitializationPhysicalStep.selectedRowIndex p source) t control remainder hrem start
    (by omega) hlaunchStart
  have hseedFacts := ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec rate rewards
    C_star C_h (ActualInitializationPhysicalStep.selectedRowIndex p source) t control remainder
    hrem start (by omega) hlaunchStart
  have hmodeG : allActiveAtStart active start := by
    change allActiveAtStart (actualLaunchState rate source rewards C_star C_h hcross) start
    rw [← hseedEq]
    simpa [seed] using hseedFacts.2.1
  let mode := hmodeG
  let execution := ReferenceActivePhysicalHorizon.run active source.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start count hspan mode
  let window := ReferenceFirstLiveConfirmationHistory.firstLiveWindow execution.records
  let k := window.length
  let prefixRun := ReferenceActivePhysicalHorizon.run active source.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start k (by
      have hk : k < count := by simpa [k, window, execution, mode, actualFirstCollectionRun] using hshort
      omega) mode
  have hshortRun : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      execution.records).length < count := by
    simpa [execution, actualFirstCollectionRun] using hshort
  have hO := ReferenceFirstCutoffOutsideInitialization.run_first_cutoff_outside_initializer
    active source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
    start count hspan mode (actualLaunchState_first_active rate source rewards C_star C_h hcross).2 hshortRun
  rcases hO with ⟨cut, suffix, hsplit, hindex, htime, hactual, r, q, base, hstate, hlive,
    dispatched, hstart, ledger, hinit, hledger, hdomain, hclock, hpending, hnoAssignment,
    selected, hbranch, hrest⟩
  rcases hrest with ⟨hkpos, hsigma, hbase, hbirth, hproposal, hqueues, hrest⟩
  rcases hrest with ⟨huvalue, hsigmaPos, huT, huGrid, hgridT, hledgerSigma, hledgerCutoff,
    hledgerFreeze, hfirstCutoff, houtsideSlow, houtsideFast, hledgerFields⟩
  -- Keep the checked source initializer and the literal selected choice from O.
  rcases hledgerFields with ⟨hcutoffRegisters, hcurrentRegisters, hbaseLedger, hpendingLedger,
    hincrement, hgamma, hraw, henabled, hcursor, hphase, hsharedCutoff, hsharedCurrent,
    hsharedIncrement, hsharedGamma, hsharedRaw, hsharedEnabled, hsharedCursor, hsharedPhase,
    hinitializerData⟩
  rcases hinitializerData with ⟨initializer, choice, hinitializer, hchoice, hchoiceInitializer,
    hchecked⟩
  have hfirst := (actualLaunchState_first_active rate source rewards C_star C_h hcross).2
  have hmode := (actualLaunchState_first_active rate source rewards C_star C_h hcross).1
  have hclockSeed : ReferenceCoordinatorClockDomains.clockAt source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) start active := by
    change ReferenceCoordinatorClockDomains.clockAt source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) start
      (actualLaunchState rate source rewards C_star C_h hcross)
    unfold ReferenceCoordinatorClockDomains.clockAt
    rw [hfirst]
    trivial
  have hclockRun := ReferenceRunClockPreservation.run_clockAt active source.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start count hspan
    hmode hclockSeed
  have hcutMem : cut ∈ execution.records := by
    rw [hsplit]
    simp
  have hcutClock := (hclockRun.2.2.2 cut hcutMem).1
  rw [hstate] at hcutClock
  simp only [ReferenceCoordinatorClockDomains.clockAt, hlive] at hcutClock
  rcases hcutClock with ⟨_, hclockValid, hpriorSigma, _, hgrid, _, _, _⟩
  have hboundary : r.priorClock.g =
      FollowerCutoffScan.gridBoundary p rate.eta.val r.payload.sigma := by
    simpa only [CoordinatorPhaseClock.boundaryFromSigma, hpriorSigma] using hclockValid.1
  have hrGrid : r.gridBoundary =
      FollowerCutoffScan.gridBoundary p rate.eta.val r.payload.sigma := hgrid.trans hboundary
  have htimeStart : cut.input.time.val = start + k := by omega
  refine ⟨cut, suffix, hsplit, htimeStart, r, q, base, ?_, ?_, ?_⟩
  · simpa [prefixRun, active, mode, execution, window, k, actualFirstCollectionRun] using hstate
  · simpa [prefixRun, active, mode, execution, window, k, actualFirstCollectionRun] using hlive
  · refine ⟨dispatched, hstart, ledger, hinit, hledger, hdomain, hclock, hpending,
      hnoAssignment, selected, hbranch, hkpos, hsigma, hbase, ?_⟩
    change start + k + 1 ≤ p.T ∧ start + k + 1 ≤ r.gridBoundary ∧
      r.gridBoundary ≤ p.T + 1 ∧
      r.gridBoundary = FollowerCutoffScan.gridBoundary p rate.eta.val r.payload.sigma ∧
      (∀ i : Fin (p.m - 1), FollowerCutoffScan.firstCutoff p rate.eta.val
        r.payload.sigma (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
          (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source))) =
        start + k + 1) ∧ ledger.sigma = r.payload.sigma.val + 1 ∧
      ledger.cutoff = start + k + 1 ∧ ledger.freezeAt = r.gridBoundary ∧
      ∃ (initializer : ReferenceCollectionSegmentExtraction.Initializer p)
        (choice : ReferenceCollectionSegmentExtraction.Choice rate),
        initializer = ReferenceCollectionSegmentExtraction.cutoffInitializer
          (ReferenceActivePhysicalStep.liveInput cut.input r q base).registers
          (ReferenceActivePhysicalStep.liveInput cut.input r q base).ownedRegisters base
          (ReferenceActivePhysicalStep.liveInput cut.input r q base).registers.time ∧
        ReferenceCollectionSegmentExtraction.choice cut.input = some choice ∧
        choice.initializer = some initializer ∧
        initializer.checkedStart rate = .success (ReferenceActivePhysicalStep.sharedLedger ledger)
    exact ⟨by omega, by omega, by omega, hrGrid, fun _ => by omega,
      hledgerSigma, by omega, hledgerFreeze,
      ⟨initializer, choice, hinitializer, hchoice, hchoiceInitializer, hchecked⟩⟩

/-- The cutoff branch also constructs X's segment from the actual run suffix.
Its window is the literal collection window through the next later choice,
and X's partition keeps every failed or excluded physical record. -/
theorem actual_first_collection_segment (rate : RateInput p)
    (source : SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (count : ℕ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed + count ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (actualFirstCollectionRun rate source rewards C_star C_h hcross count hspan).records).length < count) :
    let start := ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
    let execution := actualFirstCollectionRun rate source rewards C_star C_h hcross count hspan
    let window := ReferenceFirstLiveConfirmationHistory.firstLiveWindow execution.records
    let k := window.length
    ∃ cut suffix,
      ∃ r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta,
        ∃ q : CoordinatorLiveServiceFinish.OwnedRegisters r,
          ∃ base : Fin (p.m - 1) → ℕ,
            ∃ choice : ReferenceCollectionSegmentExtraction.Choice rate,
              ∃ initializer : ReferenceCollectionSegmentExtraction.Initializer p,
                ∃ seg : ReferenceCollectionSegmentExtraction.Segment rate,
              execution.records = window ++ cut :: suffix ∧
              cut.input.time.val = start + k ∧
              ReferenceCollectionSegmentExtraction.choice cut.input = some choice ∧
              choice.payload = r.payload ∧
              initializer = ReferenceCollectionSegmentExtraction.cutoffInitializer
                (ReferenceActivePhysicalStep.liveInput cut.input r q base).registers
                (ReferenceActivePhysicalStep.liveInput cut.input r q base).ownedRegisters base
                (ReferenceActivePhysicalStep.liveInput cut.input r q base).registers.time ∧
              choice.initializer = some initializer ∧
              initializer.sigma = start + 1 ∧
              initializer.cutoff = start + k + 1 ∧
              initializer.freezeAt = r.gridBoundary ∧
              initializer.freezeAt =
                FollowerCutoffScan.gridBoundary p rate.eta.val r.payload.sigma ∧
              initializer.base = (fun _ => 0) ∧
              initializer.assignment.arm = r.payload.assignment.assigned ∧
              initializer.checkedStart rate = .success choice.preLedger ∧
              0 < k ∧ start + k + 1 ≤ p.T ∧
              start + k + 1 ≤ r.gridBoundary ∧ r.gridBoundary ≤ p.T + 1 ∧
              (∀ _i : Fin (p.m - 1),
                FollowerCutoffScan.firstCutoff p rate.eta.val r.payload.sigma
                  (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
                    (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source))) =
                start + k + 1) ∧
              ReferenceCollectionSegmentExtraction.segmentAt execution.records k = some seg ∧
              seg.entry = cut ∧
              seg.context = choice ∧
              seg.records = (if (ReferenceCollectionSegmentExtraction.extractRound cut).isSome
                then cut :: suffix.takeWhile ReferenceCollectionSegmentExtraction.continuing else []) ∧
              seg.remaining = (if (ReferenceCollectionSegmentExtraction.extractRound cut).isSome
                then suffix.dropWhile ReferenceCollectionSegmentExtraction.continuing else cut :: suffix) ∧
              seg.records ++ seg.remaining = execution.records.drop k ∧
              ReferenceCollectionPhaseHistory.collectionWindow execution.records k =
                cut :: suffix.takeWhile (fun record =>
                  !ReferenceCollectionPhaseHistory.laterChosen record.input) := by
  let start := ReferenceInitializationRun.elapsed p
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
  let execution := actualFirstCollectionRun rate source rewards C_star C_h hcross count hspan
  let window := ReferenceFirstLiveConfirmationHistory.firstLiveWindow execution.records
  let k := window.length
  obtain ⟨cut, suffix, hsplit, htime, r, q, base, hstate, hlive,
    dispatched, hstart, ledger, hinit, hledger, hdomain, hclock, hpending,
    hnoAssignment, selected, hbranch, hkpos, hsigma, hbase, hgeometry⟩ :=
      actual_first_collection_epoch_replay rate source rewards C_star C_h count
        hcross hspan hshort
  rcases hgeometry with ⟨hu, hgridLower, hgridUpper, hrGrid, hfirstCutoff, hledgerSigma,
    hledgerCutoff, hledgerFreeze, initializer, choice, hinitializer, hchoice,
    hchoiceInitializer, hchecked⟩
  have hsplit' : execution.records = window ++ cut :: suffix := by
    simpa [execution, window] using hsplit
  have hdrop : execution.records.drop k = cut :: suffix := by
    rw [hsplit']
    simp [k]
  have hdropNext : execution.records.drop (k + 1) = suffix := by
    rw [hsplit']
    simp [k]
  have hkpos' : k > 0 := by
    simpa [k, window, execution, actualFirstCollectionRun] using hkpos
  have hseg : ∃ seg : ReferenceCollectionSegmentExtraction.Segment rate,
      ReferenceCollectionSegmentExtraction.segmentAt execution.records k = some seg := by
    have hkne : k ≠ 0 := by omega
    unfold ReferenceCollectionSegmentExtraction.segmentAt
    rw [hdrop]
    cases he : ReferenceCollectionSegmentExtraction.extractRound cut with
    | none =>
        let seg : ReferenceCollectionSegmentExtraction.Segment rate :=
          ⟨cut, choice, [], cut :: suffix⟩
        have hs : ReferenceCollectionSegmentExtraction.segment (cut :: suffix) = some seg := by
          simp [ReferenceCollectionSegmentExtraction.segment, hchoice, he, seg]
        refine ⟨seg, ?_⟩
        simp only [hs, Option.bind_some]
        simp [hkne, seg, hchoiceInitializer]
    | some completed =>
        let seg : ReferenceCollectionSegmentExtraction.Segment rate :=
          ⟨cut, choice, cut :: suffix.takeWhile ReferenceCollectionSegmentExtraction.continuing,
            suffix.dropWhile ReferenceCollectionSegmentExtraction.continuing⟩
        have hs : ReferenceCollectionSegmentExtraction.segment (cut :: suffix) = some seg := by
          simp [ReferenceCollectionSegmentExtraction.segment, hchoice, he, seg]
        refine ⟨seg, ?_⟩
        simp only [hs, Option.bind_some]
        simp [hkne, seg, hchoiceInitializer]
  rcases hseg with ⟨seg, hseg⟩
  have hbranchSeg := ReferenceCollectionSegmentExtraction.segmentAt_branch
    execution.records k seg hseg
  have hpart := ReferenceCollectionSegmentExtraction.segmentAt_partition
    execution.records k seg hseg
  have hentry : seg.entry = cut := by
    have hs := hbranchSeg.1
    rw [hdrop] at hs
    unfold ReferenceCollectionSegmentExtraction.segment at hs
    simp only [hchoice, Option.map_some] at hs
    split at hs <;> cases Option.some.inj hs <;> rfl
  have hcontext : seg.context = choice := by
    have hs := hbranchSeg.1
    rw [hdrop] at hs
    unfold ReferenceCollectionSegmentExtraction.segment at hs
    simp only [hchoice, Option.map_some] at hs
    split at hs <;> cases Option.some.inj hs <;> rfl
  have hshape :
      seg.records = (if (ReferenceCollectionSegmentExtraction.extractRound cut).isSome
        then cut :: suffix.takeWhile ReferenceCollectionSegmentExtraction.continuing else []) ∧
      seg.remaining = (if (ReferenceCollectionSegmentExtraction.extractRound cut).isSome
        then suffix.dropWhile ReferenceCollectionSegmentExtraction.continuing else cut :: suffix) := by
    have hs := hbranchSeg.1
    rw [hdrop] at hs
    unfold ReferenceCollectionSegmentExtraction.segment at hs
    simp only [hchoice, Option.map_some] at hs
    cases he : ReferenceCollectionSegmentExtraction.extractRound cut with
    | none =>
        simp only [he, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hs
        cases Option.some.inj hs
        exact ⟨rfl, rfl⟩
    | some completed =>
        simp only [he, Option.isSome_some, ↓reduceIte] at hs
        cases Option.some.inj hs
        exact ⟨rfl, rfl⟩
  have hcheckedChoice := ReferenceCollectionSegmentExtraction.choice_initializer
    cut.input choice initializer hchoice hchoiceInitializer
  have htime' : cut.input.time.val = start + k := by
    simpa [start, k, window, execution] using htime
  have hsigmaI : initializer.sigma = start + 1 := by
    rw [hinitializer]
    simp [ReferenceCollectionSegmentExtraction.cutoffInitializer,
      ReferenceActivePhysicalStep.liveInput, ReferenceActivePhysicalStep.liveRegistersAt, hsigma]
    rfl
  have hcutoffI : initializer.cutoff = start + k + 1 := by
    rw [hinitializer]
    simp [ReferenceCollectionSegmentExtraction.cutoffInitializer,
      ReferenceActivePhysicalStep.liveInput, ReferenceActivePhysicalStep.liveRegistersAt, htime']
  have hfreezeI : initializer.freezeAt = r.gridBoundary := by
    rw [hinitializer]
    rfl
  have hbaseI : initializer.base = (fun _ => 0) := by
    rw [hinitializer]
    funext i
    exact hbase i
  have hassignmentI : initializer.assignment.arm = r.payload.assignment.assigned := by
    rw [hinitializer]
    simp [ReferenceCollectionSegmentExtraction.cutoffInitializer,
      CoordinatorStartRoundCutoffDispatch.ledgerAssignment,
      ReferenceActivePhysicalStep.liveInput, ReferenceActivePhysicalStep.liveRegistersAt]
    rfl
  have hprep : (ReferenceActivePhysicalStep.prepare cut.input).coordinator =
      .live r q base (.cutoffChosen dispatched hstart ledger hinit hledger hdomain
        hclock hpending hnoAssignment selected) := by
    calc
      _ = (ReferenceActivePhysicalStep.step cut.input).preparation.coordinator := rfl
      _ = cut.output.preparation.coordinator := by rw [cut.output_eq]
      _ = _ := hbranch
  have hnotLater : ReferenceCollectionPhaseHistory.laterChosen cut.input = false := by
    simp [ReferenceCollectionPhaseHistory.laterChosen, hprep]
  have hfreezeIGrid := hfreezeI.trans hrGrid
  have hwindow : ReferenceCollectionPhaseHistory.collectionWindow execution.records k =
      cut :: suffix.takeWhile (fun record =>
        !ReferenceCollectionPhaseHistory.laterChosen record.input) := by
    unfold ReferenceCollectionPhaseHistory.collectionWindow
    rw [hdrop, hdropNext]
    simp
  refine ⟨cut, suffix, r, q, base, choice, initializer, seg, hsplit, htime', hchoice,
    ?_, hinitializer, hchoiceInitializer, hsigmaI, hcutoffI, hfreezeI, hfreezeIGrid, hbaseI,
    hassignmentI, hcheckedChoice, hkpos, hu, hgridLower, hgridUpper, hfirstCutoff,
    hseg, hentry, hcontext, hshape.1, hshape.2, hpart, hwindow⟩
  have hpayload : choice.payload = r.payload := by
    let canonical : ReferenceCollectionSegmentExtraction.Choice rate :=
      ⟨r.payload, ReferenceActivePhysicalStep.sharedLedger ledger,
        dispatched.startResult, (ReferenceActivePhysicalStep.liveRegistersAt r cut.input.time).complementWeights,
        some (ReferenceCollectionSegmentExtraction.cutoffInitializer
          (ReferenceActivePhysicalStep.liveRegistersAt r cut.input.time)
          (ReferenceActivePhysicalStep.liveOwnedAt r q cut.input.time) base cut.input.time)⟩
    have hcanonical : ReferenceCollectionSegmentExtraction.choice cut.input = some canonical := by
      simp [ReferenceCollectionSegmentExtraction.choice,
        ReferenceCollectionSegmentExtraction.choiceOfCut, hprep,
        ReferenceActivePhysicalStep.DispatchCut.selection,
        ReferenceActivePhysicalStep.selectionAt, canonical]
    have hcanonicalEq : canonical = choice := Option.some.inj (hcanonical.symm.trans hchoice)
    simpa [canonical] using
      (congrArg ReferenceCollectionSegmentExtraction.Choice.payload hcanonicalEq).symm
  exact hpayload

/-- Every round in the raw first collection window is an actual consecutive
physical round of E, including the retained failure and dagger suffix. -/
theorem actual_first_collection_window_time (rate : RateInput p)
    (source : SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (count : ℕ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed + count ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (actualFirstCollectionRun rate source rewards C_star C_h hcross count hspan).records).length < count) :
    let start := ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
    let execution := actualFirstCollectionRun rate source rewards C_star C_h hcross count hspan
    let window := ReferenceFirstLiveConfirmationHistory.firstLiveWindow execution.records
    let k := window.length
    let B := ReferenceCollectionPhaseHistory.collectionWindow execution.records k
    ∀ l : Fin B.length,
      execution.records[k + l.val]? = some B[l.val] ∧
        B[l.val].input.time.val + 1 = start + k + 1 + l.val := by
  let start := ReferenceInitializationRun.elapsed p
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
  let execution := actualFirstCollectionRun rate source rewards C_star C_h hcross count hspan
  let window := ReferenceFirstLiveConfirmationHistory.firstLiveWindow execution.records
  let k := window.length
  let B := ReferenceCollectionPhaseHistory.collectionWindow execution.records k
  rcases actual_first_collection_segment rate source rewards C_star C_h count hcross hspan hshort with
    ⟨cut, suffix, r, q, base, choice, initializer, seg, hsplit, htime, hchoice,
      hpayload, hinitializer, hchoiceInitializer, hsigmaI, hcutoffI, hfreezeI, hfreezeIGrid,
      hbaseI, hassignmentI, hchecked, hkpos, hu, hgridLower, hgridUpper,
      hfirstCutoff, hsegmentAt, hentry, hcontext, hrecords, hremaining,
      hpartition, hwindow⟩
  have hsplit' : execution.records = window ++ cut :: suffix := by
    simpa [execution, window] using hsplit
  have hdrop : execution.records.drop k = cut :: suffix := by
    rw [hsplit']
    simp [k]
  have hprefix : B <+: execution.records.drop k := by
    change ReferenceCollectionPhaseHistory.collectionWindow execution.records k <+:
      execution.records.drop k
    rw [hwindow]
    refine ⟨suffix.dropWhile (fun record =>
      !ReferenceCollectionPhaseHistory.laterChosen record.input), ?_⟩
    rw [hdrop]
    simp only [List.cons_append, List.takeWhile_append_dropWhile]
  have htimes : execution.records.map (fun record => record.input.time.val) =
      ReferenceActivePhysicalHorizon.calendar start count := by
    simpa [execution, actualFirstCollectionRun, start] using
      ReferenceActivePhysicalHorizon.run_time_values
        (actualLaunchState rate source rewards C_star C_h hcross) source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start count hspan
        ((actualLaunchState_first_active rate source rewards C_star C_h hcross).1)
  change ∀ l : Fin B.length,
    execution.records[k + l.val]? = some B[l.val] ∧
      B[l.val].input.time.val + 1 = start + k + 1 + l.val
  intro l
  have hlookup := (List.prefix_iff_getElem?).mp hprefix l.val l.isLt
  have hrecordLookup : execution.records[k + l.val]? = some B[l.val] := by
    simpa [List.getElem?_drop, Nat.add_comm] using hlookup
  have htimeLookup :
      (B.map (fun record => record.input.time.val))[l.val]? =
        (execution.records.map (fun record => record.input.time.val))[k + l.val]? := by
    have hBget : B[l.val]? = some B[l.val] := by simp [l.isLt]
    calc
      (B.map (fun record => record.input.time.val))[l.val]? =
          Option.map (fun record => record.input.time.val) B[l.val]? := by simp [l.isLt]
      _ = Option.map (fun record => record.input.time.val)
          (execution.records.drop k)[l.val]? := by
        exact congrArg (Option.map (fun record => record.input.time.val))
          (hBget.trans hlookup.symm)
      _ = (execution.records.map (fun record => record.input.time.val))[k + l.val]? := by
        simp [List.getElem?_drop, Nat.add_comm]
  have hcalendarLookup := congrArg (fun records : List ℕ => records[k + l.val]?) htimes
  have hvalue : (B.map (fun record => record.input.time.val))[l.val]? =
      (ReferenceActivePhysicalHorizon.calendar start count)[k + l.val]? :=
    htimeLookup.trans hcalendarLookup
  have hmapAt : (B.map (fun record => record.input.time.val))[l.val]? =
      some B[l.val].input.time.val := by simp [l.isLt]
  have hcalendarValue : B[l.val].input.time.val = start + k + l.val := by
    have hvalue' := hmapAt.symm.trans hvalue
    by_cases hbound : k + l.val < count
    · simp [ReferenceActivePhysicalHorizon.calendar, hbound] at hvalue'
      omega
    · simp [ReferenceActivePhysicalHorizon.calendar, hbound] at hvalue'
  refine ⟨hrecordLookup, ?_⟩
  omega

/-- The constructed source segment is also the existing checked execution
from its actual initializer. Its endpoint retains that initializer's complete
receiver-local context, including assignment and base scores. -/
theorem actual_first_collection_segment_checked_context (rate : RateInput p)
    (source : SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (count : ℕ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed + count ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (actualFirstCollectionRun rate source rewards C_star C_h hcross count hspan).records).length < count) :
    let execution := actualFirstCollectionRun rate source rewards C_star C_h hcross count hspan
    let window := ReferenceFirstLiveConfirmationHistory.firstLiveWindow execution.records
    let k := window.length
    ∃ initializer : ReferenceCollectionSegmentExtraction.Initializer p,
      ∃ seg : ReferenceCollectionSegmentExtraction.Segment rate,
        ReferenceCollectionSegmentExtraction.segmentAt execution.records k = some seg ∧
        seg.context.initializer = some initializer ∧
        CollectionCheckedExecution.startAndRunChecked p rate.eta.val rate.eta.property
          (ReferenceUpReception.sourceCap_forLedger rate) rate.n rate.n_scale
          initializer.assignment initializer.sigma initializer.cutoff initializer.freezeAt
          initializer.base initializer.outside seg.inputs =
          .success ⟨seg.context.preLedger, seg.accepted, seg.final⟩ ∧
        CollectionBufferProvenance.collectionContext seg.final =
          (initializer.assignment, initializer.sigma, initializer.cutoff,
            initializer.freezeAt, initializer.base) := by
  let start := ReferenceInitializationRun.elapsed p
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
  let execution := actualFirstCollectionRun rate source rewards C_star C_h hcross count hspan
  let window := ReferenceFirstLiveConfirmationHistory.firstLiveWindow execution.records
  let k := window.length
  rcases actual_first_collection_segment rate source rewards C_star C_h count hcross hspan hshort with
    ⟨cut, suffix, r, q, base, choice, initializer, seg, hsplit, htime, hchoice,
      hpayload, hinitializer, hchoiceInitializer, hsigmaI, hcutoffI, hfreezeI,
      hfreezeIGrid, hbaseI, hassignmentI, hcheckedI, hkpos, hu, hgridLower,
      hgridUpper, hfirstCutoff, hsegmentAt, hentry, hcontext, hrecords,
      hremaining, hpartition, hwindow⟩
  have hsegInit : seg.context.initializer = some initializer := by
    simpa [hcontext] using hchoiceInitializer
  have hmode := (actualLaunchState_first_active rate source rewards C_star C_h hcross).1
  have hfirst := (actualLaunchState_first_active rate source rewards C_star C_h hcross).2
  have hsegmentAtRun :
      ReferenceCollectionSegmentExtraction.segmentAt
        (ReferenceActivePhysicalHorizon.run (actualLaunchState rate source rewards C_star C_h hcross)
          source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
          start count hspan hmode).records k = some seg := by
    simpa [execution, actualFirstCollectionRun, k, window] using hsegmentAt
  obtain ⟨a, ha, hrun⟩ := ReferenceCollectionSegmentExtraction.run_collection_initialized_segment_at
    (actualLaunchState rate source rewards C_star C_h hcross) source.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start count hspan
    hmode hfirst k seg hsegmentAtRun
  have hae : a = initializer := Option.some.inj (ha.symm.trans hsegInit)
  subst a
  let checkedExecution : CollectionCheckedExecution.Execution p rate.eta.val rate.eta.property
      (ReferenceUpReception.sourceCap_forLedger rate) rate.n rate.n_scale :=
    ⟨seg.context.preLedger, seg.accepted, seg.final⟩
  have hcomponents := CollectionBufferProvenance.startAndRunChecked_success_components
    initializer.assignment initializer.sigma initializer.cutoff initializer.freezeAt
    initializer.base initializer.outside seg.inputs checkedExecution hrun
  rcases hcomponents with ⟨accepted, hinit, hfold⟩
  have hinit' : initializer.checkedStart rate = .success seg.context.preLedger := by
    simpa [ReferenceCollectionSegmentExtraction.Initializer.checkedStart,
      checkedExecution] using hinit
  have hinitFields := CollectionBufferProvenance.startCollectionChecked_success_context
    initializer.assignment initializer.sigma initializer.cutoff initializer.freezeAt
    initializer.base initializer.outside seg.context.preLedger (by
      simpa [ReferenceCollectionSegmentExtraction.Initializer.checkedStart] using hinit')
  have hpreContext : CollectionBufferProvenance.collectionContext seg.context.preLedger =
      (initializer.assignment, initializer.sigma, initializer.cutoff,
        initializer.freezeAt, initializer.base) := by
    simp [CollectionBufferProvenance.collectionContext, hinitFields.1,
      hinitFields.2.1, hinitFields.2.2.2.1, hinitFields.2.2.2.2.1,
      hinitFields.2.2.2.2.2]
  have hfold' : CollectionCheckedExecution.checkedRounds seg.context.preLedger seg.inputs =
      some (accepted, seg.final) := by
    simpa [checkedExecution] using hfold
  have hfinalContext := CollectionBufferProvenance.checkedRounds_success_preserves_context
    seg.context.preLedger seg.final seg.inputs accepted hfold'
  refine ⟨initializer, seg, hsegmentAt, hsegInit, hrun, ?_⟩
  exact hfinalContext.trans hpreContext

/-- An actual selected collection operation either reaches dagger or keeps
the selected payload and initializer context. In the collection branch the
same physical record has an actual extracted completed round at its own
calendar time. The incoming context equality remains an explicit conditional
input for fixed-boundary consumers. -/
theorem actual_chosen_step_context (rate : RateInput p)
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (choice : ReferenceCollectionSegmentExtraction.Choice rate)
    (initializer : ReferenceCollectionSegmentExtraction.Initializer p)
    (hchoice : ReferenceCollectionSegmentExtraction.choice x = some choice)
    (hcontext : CollectionBufferProvenance.collectionContext choice.preLedger =
      (initializer.assignment, initializer.sigma, initializer.cutoff,
        initializer.freezeAt, initializer.base)) :
    (ReferenceActivePhysicalStep.step x).next.coordinator = .dagger ∨
      ∃ ledger proposal completed,
        (ReferenceActivePhysicalStep.step x).next.coordinator =
          .collection choice.payload ledger proposal ∧
        CollectionBufferProvenance.collectionContext ledger =
          (initializer.assignment, initializer.sigma, initializer.cutoff,
            initializer.freezeAt, initializer.base) ∧
        ReferenceCollectionSegmentExtraction.extractRound
          (⟨x, ReferenceActivePhysicalStep.step x, rfl⟩ :
            ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) =
          some completed ∧
        CollectionBufferProvenance.collectionContext completed.context.preLedger =
          (initializer.assignment, initializer.sigma, initializer.cutoff,
            initializer.freezeAt, initializer.base) ∧
        completed.input.round = x.time := by
  have htail := ReferenceCollectionSegmentExtraction.choice_tail x choice hchoice
  have hphase : ReferenceCollectionPhaseHistory.CollectionPhase
      (ReferenceActivePhysicalStep.step x).next.coordinator := by
    change ReferenceCollectionPhaseHistory.CollectionPhase
      (ReferenceActivePhysicalStep.prepare x).observeCoordinator.configuration
    rw [htail]
    exact ReferenceCollectionPhaseHistory.collectionPostChoice_no_installation
      (ReferenceActivePhysicalStep.prepare x) choice.payload choice.preLedger
      choice.started choice.weights
  rcases hphase with hdagger | ⟨payload, ledger, proposal, hconfig⟩
  · exact Or.inl hdagger
  · have hpost :
        (ReferenceActivePhysicalStep.collectionPostChoice
          (ReferenceActivePhysicalStep.prepare x) choice.payload choice.preLedger
          choice.started choice.weights).configuration = .collection payload ledger proposal := by
      change (ReferenceActivePhysicalStep.prepare x).observeCoordinator.configuration = _ at hconfig
      rw [htail] at hconfig
      exact hconfig
    have hpayloadFrame := ReferenceAssignmentPayloadPersistence.collectionPostChoice_payload_frame
      (ReferenceActivePhysicalStep.prepare x) choice.payload choice.preLedger choice.started choice.weights
    have hpayload : payload = choice.payload := by
      rcases hpayloadFrame with hnone | hsome
      · rw [hpost] at hnone
        simp [ReferenceAssignmentPayloadPersistence.storedPayload] at hnone
      · rw [hpost] at hsome
        exact Option.some.inj hsome
    have hnext : (ReferenceActivePhysicalStep.step x).next.coordinator =
        .collection payload ledger proposal := by
      exact hconfig
    let record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) :=
      ⟨x, ReferenceActivePhysicalStep.step x, rfl⟩
    obtain ⟨completed, hextract⟩ :=
      ReferenceCollectionSegmentExtraction.actual_collection_round_complete record choice
        payload ledger proposal hchoice hnext
    have hextractRecord : ReferenceCollectionSegmentExtraction.extractRound record = some completed := by
      simpa [record] using hextract
    obtain ⟨hchoiceCompleted, hroundCompleted, hchecked, payload', proposal', hendpoint⟩ :=
      ReferenceCollectionSegmentExtraction.actual_collection_round_checked record completed hextractRecord
    have hcompletedChoice : completed.context = choice :=
      Option.some.inj (hchoiceCompleted.symm.trans hchoice)
    have hcompletedContext : CollectionBufferProvenance.collectionContext
        completed.context.preLedger =
          (initializer.assignment, initializer.sigma, initializer.cutoff,
            initializer.freezeAt, initializer.base) := by
      rw [hcompletedChoice]
      exact hcontext
    have hfinalContext := CollectionBufferProvenance.checkedRounds_success_preserves_context
      completed.context.preLedger completed.final [completed.input] [completed.accepted] hchecked
    have hledgerEq : ledger = completed.final := by
      have heq : ReferenceActivePhysicalStep.CoordinatorConfiguration.collection
          payload ledger proposal =
          ReferenceActivePhysicalStep.CoordinatorConfiguration.collection
            payload' completed.final proposal' := by
        calc
          ReferenceActivePhysicalStep.CoordinatorConfiguration.collection
              payload ledger proposal =
              (ReferenceActivePhysicalStep.step x).next.coordinator := hnext.symm
          _ = record.output.next.coordinator := rfl
          _ = ReferenceActivePhysicalStep.CoordinatorConfiguration.collection
                payload' completed.final proposal' := hendpoint
      injection heq
    have hnextChoice : (ReferenceActivePhysicalStep.step x).next.coordinator =
        .collection choice.payload ledger proposal := by
      exact hnext.trans (congrArg
        (fun selectedPayload =>
          ReferenceActivePhysicalStep.CoordinatorConfiguration.collection
            selectedPayload ledger proposal) hpayload)
    refine Or.inr ⟨ledger, proposal, completed, hnextChoice, ?_, ?_, ?_, hroundCompleted⟩
    · rw [hledgerEq]
      exact hfinalContext.trans hcompletedContext
    · simpa [record] using hextractRecord
    · exact hcompletedContext

end Bandits.Support.ReferenceFirstCollectionEpochAlignment

end
