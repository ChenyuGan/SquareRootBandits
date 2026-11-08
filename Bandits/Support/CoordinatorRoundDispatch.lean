/-
Copyright (c) 2026 The Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.CoordinatorStartRoundCutoffDispatch
public import Bandits.Support.CoordinatorAssignmentRegisterInstall
public import Bandits.Support.CoordinatorPhaseClock
public import Bandits.Support.FirstAssignmentLaunch
public import Bandits.Support.LaterAssignmentStartOperation
public import Bandits.Support.AssignmentScoreReconstruction
public import Bandits.Support.CoordinatorLocalArmChoice
public import Bandits.Support.CoordinatorLiveInteractive
public import Bandits.Support.CoordinatorCollectionInteractive

/-!
# Coordinator pre-choice dispatch

This module consumes the accepted start-round, cutoff, first-installation,
later-start, and local arm-choice operations. Its transient input views retain
only the source row and the already-owned coordinator registers or collection
ledger; they introduce no second clock, score, weight, or queue state.

The dispatcher returns the original checked failures and the exact arm chosen
from the original start result. It does not construct physical feedback or a
reference execution.

Sources: `sources/zip4/manuscript/06_interruptions.tex:9-70,123-189,235-297`,
`sources/zip4/manuscript/05_binary_transport.tex:60-124`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:6-14`.
-/

@[expose] public section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ActiveRoundActions
open Bandits.Support.CanonicalFastSampling
open Bandits.Support.CoordinatorPhaseClock
open Bandits.Support.ReferencePrelaunchFollower

namespace Bandits.Support.CoordinatorRoundDispatch

abbrev Parameters := ConstructorDimensions.Parameters
abbrev LearningRate := ReferencePrelaunchFollower.LearningRate

variable {p : Parameters}

/-- First-start source data before applying the existing complete-row
coordinate projection. The rate and exact integer numerator are the original
ones used by the payload and launch constructors. -/
structure FirstInput (p : Parameters) where
  eta : LearningRate
  eta_le_source_cap : eta.val ≤
    1 / (1024 * (p.m : ℝ) * (p.K : ℝ) *
      (CanonicalRecordingRates.L_stab p : ℝ))
  n : ℕ
  n_eq_eta_mul_D : (n : ℝ) = eta.val * (D p : ℝ)
  time : Fin p.T
  row : CompletePublicTable.CompleteRow p

/-- Derive the first launch from the actual time slice's whole assignment
vector. No coordinate, rate, queue, or score is chosen independently. -/
noncomputable def firstLaunchInput (x : FirstInput p) :
    FirstAssignmentLaunch.Input p x.eta := {
  eta_le_source_cap := x.eta_le_source_cap
  n := x.n
  n_eq_eta_mul_D := x.n_eq_eta_mul_D
  sigma := x.time
  coordinates := LaterAssignmentStartOperation.ownAssignmentVector x.row x.time
}

/-- Every installed or carried choice uses the cutoff encoded by the exact
start result that is retained in the same value. -/
structure ArmSelection
    {eta : LearningRate}
    (payload : AssignmentStartPayload.Input p eta)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (time : Fin p.T)
    (weights : FastArm payload.slowSet → ℝ)
    (row : CompletePublicTable.CompleteRow p) where
  arm : Fin p.K
  choiceInputsValid : CoordinatorLocalArmChoice.ChoiceInputsValid payload
    (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
    time weights
  recorderBoundaryValid : started.clock.g ≤ p.T + 1
  armChoice_eq : CoordinatorLocalArmChoice.coordinatorArmChoice payload
    started.pending
    (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
    time weights row = some arm

/-- A first start either exposes a tagged local failure or the exact existing
first installation and its pre-choice arm. -/
inductive FirstOutcome (x : FirstInput p) where
  | choiceDomainFailure
      (installation : CoordinatorAssignmentRegisterInstall.FirstInstallation
        (firstLaunchInput x))
  | recorderBoundaryFailure
      (installation : CoordinatorAssignmentRegisterInstall.FirstInstallation
        (firstLaunchInput x))
  | choiceRejected
      (installation : CoordinatorAssignmentRegisterInstall.FirstInstallation
        (firstLaunchInput x))
  | chosen
      (installation : CoordinatorAssignmentRegisterInstall.FirstInstallation
        (firstLaunchInput x))
      (selection : ArmSelection installation.registers.payload
        installation.startRoundResult installation.registers.time
        installation.registers.complementWeights x.row)

/-- Local checks that distinguish malformed carried live registers from the
phase-clock and checked-collection outcomes retained in `LiveOutcome`. -/
inductive LiveFailure where
  | frameMismatch
  | payloadClockMismatch
  | gridBoundaryMismatch
  | scoreDomainFailure
  | queueDomainFailure
  | previousServiceDomainFailure
  | baseScoreDomainFailure
  | choiceDomainFailure
  | recorderBoundaryFailure
  | choiceRejected
  deriving DecidableEq

/-- The disjoint live input view uses the existing score and owned-register
carriers and the one actual complete source row. -/
structure LiveInput (p : Parameters) where
  eta : LearningRate
  registers : CoordinatorLiveChoiceRecorderStep.Registers p eta
  ownedRegisters : CoordinatorLiveServiceFinish.OwnedRegisters registers
  followerBaseScore : Fin (p.m - 1) → ℕ
  row : CompletePublicTable.CompleteRow p

/-- Every live failure retains the actual cutoff-dispatch result (or exact
outer clock failure). A chosen cutoff carries the checked new ledger; a
continuation carries the locally checked live continuation. -/
inductive LiveOutcome (x : LiveInput p) where
  | clockFailure (failure : CoordinatorPhaseClock.ClockFailure)
      (dispatch_eq : CoordinatorStartRoundCutoffDispatch.dispatch
        x.registers x.ownedRegisters x.followerBaseScore = .error failure)
  | initializerFailure
      (dispatched : CoordinatorStartRoundCutoffDispatch.Output
        x.registers x.ownedRegisters x.followerBaseScore)
      (startRound_eq : CoordinatorPhaseClock.startRound p x.eta.val
        x.registers.time x.registers.priorClock x.registers.clockPending =
          .ok dispatched.startResult)
      (checked : CoordinatorCollectionLedger.Checked
        (Option (CoordinatorStartRoundCutoffDispatch.NewLedger x.registers)))
      (checked_eq : dispatched.collectionInitialization = checked)
  | localFailure
      (dispatched : CoordinatorStartRoundCutoffDispatch.Output
        x.registers x.ownedRegisters x.followerBaseScore)
      (startRound_eq : CoordinatorPhaseClock.startRound p x.eta.val
        x.registers.time x.registers.priorClock x.registers.clockPending =
          .ok dispatched.startResult)
      (reason : LiveFailure)
  | cutoffChosen
      (dispatched : CoordinatorStartRoundCutoffDispatch.Output
        x.registers x.ownedRegisters x.followerBaseScore)
      (startRound_eq : CoordinatorPhaseClock.startRound p x.eta.val
        x.registers.time x.registers.priorClock x.registers.clockPending =
          .ok dispatched.startResult)
      (ledger : CoordinatorStartRoundCutoffDispatch.NewLedger x.registers)
      (initialization_eq : dispatched.collectionInitialization =
        .success (some ledger))
      (ledger_eq_candidate : ledger =
        CoordinatorStartRoundCutoffDispatch.collectionStartLedger
          x.registers x.ownedRegisters x.followerBaseScore x.registers.time)
      (initializationDomainValid :
        CoordinatorStartRoundCutoffDispatch.initializationDomainValid
          x.registers x.ownedRegisters x.followerBaseScore x.registers.time)
      (cutoff_clock : dispatched.startResult.clock =
        { x.registers.priorClock with u := some x.registers.time })
      (cutoff_pending : dispatched.startResult.pending = Finset.univ)
      (no_assignment : dispatched.startResult.assignmentStart = none)
      (selection : ArmSelection x.registers.payload dispatched.startResult
        x.registers.time x.registers.complementWeights x.row)
  | continuingChosen
      (dispatched : CoordinatorStartRoundCutoffDispatch.Output
        x.registers x.ownedRegisters x.followerBaseScore)
      (startRound_eq : CoordinatorPhaseClock.startRound p x.eta.val
        x.registers.time x.registers.priorClock x.registers.clockPending =
          .ok dispatched.startResult)
      (continuation : CoordinatorLiveChoiceRecorderStep.Continuation
        x.registers x.row)
      (selection : ArmSelection x.registers.payload dispatched.startResult
        x.registers.time x.registers.complementWeights x.row)

/-- Local source-state checks for a carried collection input. Pending may be
empty: that is the case in which the same clock result issues a new assignment
instruction. Choice validity is checked only after that actual call. -/
structure CollectionCoreValid
    (x : CoordinatorCollectionInteractive.PreObservationInputs p) where
  payload_n_eq : x.payload.n = x.n
  ledger_valid : CoordinatorCollectionLedger.validLedger x.ledger
  ledger_ready : x.ledger.phase = CoordinatorCollectionLedger.Phase.ready
  assignment_eq : ∀ i : Fin (p.m - 1),
    x.ledger.assignment.arm i = x.payload.assignment.assigned i
  base_score_eq : x.ledger.baseScore = x.baseScores
  clock_parameter_valid : CoordinatorPhaseClock.proposalParameterValid p x.etaReal
  clock_registers_valid :
    CoordinatorPhaseClock.clockRegistersValid p x.etaReal x.clock
  clock_start_time_valid :
    CoordinatorPhaseClock.startRoundTimeValid p x.time x.clock
  clock_sigma_eq : x.clock.sigma = some x.payload.sigma
  clock_cutoff_eq : x.clock.u = some x.cutoffIndex
  ledger_sigma_eq : x.ledger.sigma =
    CoordinatorRecorderComplementBridge.sourceStart x.payload
  ledger_cutoff_eq : x.ledger.cutoff =
    CoordinatorCollectionUpRoundStep.sourceCutoff x.cutoffIndex
  ledger_freeze_eq : x.ledger.freezeAt = x.clock.g
  ledger_cursor_eq : x.ledger.cursor =
    CoordinatorCollectionUpRoundStep.sourceRound x.time
  decoder_bank_valid :
    CoordinatorUpReception.decoderBankCheck p x.upDecoderBank = true

/-- Tagged local collection failures. The original `ClockFailure` and every
later-start failure are carried by separate constructors without translation.
-/
inductive CollectionFailure where
  | stateDomainFailure
  | currentScoreDomainFailure
  | wrongClockBranch
  | choiceDomainFailure
  | recorderBoundaryFailure
  | choiceRejected
  | assignmentInstructionMissing
  deriving DecidableEq

/-- One collection input is the already accepted observation-free interactive
carrier. It still contains the actual row, clock, ledger, base scores, and
persistent UP decoder bank. -/
abbrev CollectionInput (p : Parameters) :=
  CoordinatorCollectionInteractive.PreObservationInputs p

/-- Before forming continuing-collection weights, check each actual complement
cutoff score plus its accumulated increment. Unknown complement registers fail;
unknown pending slow arms are left untouched. Natural scores are nonnegative.
Sources: `appendix_a_local_protocol.tex:6-14`,
`06_interruptions.tex:16-30`, and `04_slow_fast_learner.tex:140-174`, all under
`sources/zip4/manuscript/`. -/
def collectionCurrentScoresCheck (x : CollectionInput p) : Bool :=
  CoordinatorCollectionLedger.allFin p.K fun a =>
    if a ∈ x.payload.slowSet.1 then true else
      match x.ledger.cutoffRegisters a with
      | none => false
      | some cutoff => decide (cutoff.score + x.ledger.increment a ≤ p.T * D p)

-- The accepted allFin characterization is private in the collection modules.
private theorem allFin_eq_true_iff {length : ℕ} (test : Fin length → Bool) :
    CoordinatorCollectionLedger.allFin length test = true ↔ ∀ i, test i = true := by
  unfold CoordinatorCollectionLedger.allFin
  rw [List.all_eq_true]
  constructor
  · intro h i
    exact h (test i) (by simp)
  · intro h b hb
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp hb
    subst b
    exact h i

/-- The score used by the accepted weight operation is the actual stored
cutoff score plus increment. The known-register theorem supplies presence;
option injectivity supplies correspondence, without a provenance premise. -/
theorem collection_complementCurrentScore_eq (x : CollectionInput p)
    (core : CollectionCoreValid x) (a : Fin p.K)
    (ha : a ∉ x.payload.slowSet.1)
    (cutoff : CoordinatorCollectionLedger.CutoffRegister)
    (hcutoff : x.ledger.cutoffRegisters a = some cutoff) :
    CoordinatorCollectionUpRoundStep.complementCurrentScore x.ledger x.payload
      core.ledger_valid core.assignment_eq a ha =
        cutoff.score + x.ledger.increment a := by
  have hknown := CoordinatorCollectionUpRoundStep.complementRegisters_known
    x.ledger x.payload core.ledger_valid core.assignment_eq a ha
  have hchosen := (Classical.choose_spec hknown).1
  have heq := Option.some.inj (hchosen.symm.trans hcutoff)
  unfold CoordinatorCollectionUpRoundStep.complementCurrentScore
  rw [heq]

/-- The finite runtime check is exactly the domain bound on the scores used
by continuing collection. Core validity provides known registers, not bounds
on their sums. No weight envelope or reachability assumption is used. -/
theorem collectionCurrentScoresCheck_iff (x : CollectionInput p)
    (core : CollectionCoreValid x) :
    collectionCurrentScoresCheck x = true ↔
      ∀ (a : Fin p.K) (ha : a ∉ x.payload.slowSet.1),
        CoordinatorCollectionUpRoundStep.complementCurrentScore x.ledger x.payload
          core.ledger_valid core.assignment_eq a ha ≤ p.T * D p := by
  classical
  unfold collectionCurrentScoresCheck
  rw [allFin_eq_true_iff]
  constructor
  · intro h a ha
    obtain ⟨cutoff, hcutoff, _⟩ :=
      CoordinatorCollectionUpRoundStep.complementRegisters_known
        x.ledger x.payload core.ledger_valid core.assignment_eq a ha
    have hentry := h a
    simp only [ite_eq_right ha, hcutoff, decide_eq_true_eq] at hentry
    rw [collection_complementCurrentScore_eq x core a ha cutoff hcutoff]
    exact hentry
  · intro h a
    by_cases ha : a ∈ x.payload.slowSet.1
    · simp only [ite_eq_left ha]
    · obtain ⟨cutoff, hcutoff, _⟩ :=
        CoordinatorCollectionUpRoundStep.complementRegisters_known
          x.ledger x.payload core.ledger_valid core.assignment_eq a ha
      simp only [ite_eq_right ha, hcutoff, decide_eq_true_eq]
      rw [← collection_complementCurrentScore_eq x core a ha cutoff hcutoff]
      exact h a ha

/-- On a checked core, failure is exactly an overflowing actual known
complement score. Missing-register cases have been ruled out by the accepted
ledger and assignment equations, not by an added bound or truthful-UP premise. -/
theorem collectionCurrentScoresCheck_eq_false_iff (x : CollectionInput p)
    (core : CollectionCoreValid x) :
    collectionCurrentScoresCheck x = false ↔
      ∃ a : Fin p.K, a ∉ x.payload.slowSet.1 ∧
        ∃ cutoff : CoordinatorCollectionLedger.CutoffRegister,
          x.ledger.cutoffRegisters a = some cutoff ∧
            p.T * D p < cutoff.score + x.ledger.increment a := by
  classical
  constructor
  · intro hfailed
    have hnot : ¬ ∀ (a : Fin p.K) (ha : a ∉ x.payload.slowSet.1),
        CoordinatorCollectionUpRoundStep.complementCurrentScore x.ledger x.payload
          core.ledger_valid core.assignment_eq a ha ≤ p.T * D p := by
      intro h
      have htrue := (collectionCurrentScoresCheck_iff x core).mpr h
      rw [hfailed] at htrue
      exact Bool.false_ne_true htrue
    obtain ⟨a, hnot⟩ := not_forall.mp hnot
    obtain ⟨ha, hover⟩ := not_forall.mp hnot
    obtain ⟨cutoff, hcutoff, _⟩ :=
      CoordinatorCollectionUpRoundStep.complementRegisters_known
        x.ledger x.payload core.ledger_valid core.assignment_eq a ha
    refine ⟨a, ha, cutoff, hcutoff, ?_⟩
    rw [collection_complementCurrentScore_eq x core a ha cutoff hcutoff] at hover
    exact Nat.lt_of_not_ge hover
  · rintro ⟨a, ha, cutoff, hcutoff, hover⟩
    apply Bool.eq_false_of_not_eq_true
    intro hcheck
    have hbound := (collectionCurrentScoresCheck_iff x core).mp hcheck a ha
    rw [collection_complementCurrentScore_eq x core a ha cutoff hcutoff] at hbound
    exact (Nat.not_le_of_lt hover) hbound

/-- A type-directed field projection of the carried collection ledger into
the later-start API's local-ledger index. Every stored value is copied
verbatim; only the proof-index presentation is adapted. -/
def collectionOperationLedger (x : CollectionInput p)
    (_payload_n_eq : x.payload.n = x.n) :
    LaterAssignmentStartOperation.LocalLedger x.payload := {
  assignment := x.ledger.assignment
  sigma := x.ledger.sigma
  cutoff := x.ledger.cutoff
  freezeAt := x.ledger.freezeAt
  baseScore := x.ledger.baseScore
  pending := x.ledger.pending
  cutoffRegisters := x.ledger.cutoffRegisters
  currentRegisters := x.ledger.currentRegisters
  increment := x.ledger.increment
  gammaLoc := x.ledger.gammaLoc
  rawBuffer := x.ledger.rawBuffer
  enabledHistory := x.ledger.enabledHistory
  cursor := x.ledger.cursor
  phase := x.ledger.phase }

/-- The local later-start ledger view retains every actual carried register. -/
theorem collectionOperationLedger_fields (x : CollectionInput p)
    (payload_n_eq : x.payload.n = x.n) :
    (collectionOperationLedger x payload_n_eq).assignment = x.ledger.assignment ∧
    (collectionOperationLedger x payload_n_eq).sigma = x.ledger.sigma ∧
    (collectionOperationLedger x payload_n_eq).cutoff = x.ledger.cutoff ∧
    (collectionOperationLedger x payload_n_eq).freezeAt = x.ledger.freezeAt ∧
    (collectionOperationLedger x payload_n_eq).baseScore = x.ledger.baseScore ∧
    (collectionOperationLedger x payload_n_eq).pending = x.ledger.pending ∧
    (collectionOperationLedger x payload_n_eq).cutoffRegisters = x.ledger.cutoffRegisters ∧
    (collectionOperationLedger x payload_n_eq).currentRegisters = x.ledger.currentRegisters ∧
    (collectionOperationLedger x payload_n_eq).increment = x.ledger.increment ∧
    (collectionOperationLedger x payload_n_eq).gammaLoc = x.ledger.gammaLoc ∧
    (collectionOperationLedger x payload_n_eq).rawBuffer = x.ledger.rawBuffer ∧
    (collectionOperationLedger x payload_n_eq).enabledHistory = x.ledger.enabledHistory ∧
    (collectionOperationLedger x payload_n_eq).cursor = x.ledger.cursor ∧
    (collectionOperationLedger x payload_n_eq).phase = x.ledger.phase := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Outcome of one collection pre-choice operation. Pending collection
retains the old interactive preparation and state. A later start retains the
actual operation result, original clock evidence, installation, and selected
arm. -/
inductive CollectionOutcome (x : CollectionInput p) where
  | clockFailure (failure : CoordinatorPhaseClock.ClockFailure)
      (startRound_eq : CoordinatorPhaseClock.startRound p x.etaReal x.time
        x.clock x.ledger.pending = .error failure)
  | localFailure (started : CoordinatorPhaseClock.StartRoundResult p)
      (startRound_eq : CoordinatorPhaseClock.startRound p x.etaReal x.time
        x.clock x.ledger.pending = .ok started)
      (core_invalid : ¬ CollectionCoreValid x)
      (reason : CollectionFailure)
  | coreFailure (core : CollectionCoreValid x)
      (started : CoordinatorPhaseClock.StartRoundResult p)
      (startRound_eq : CoordinatorPhaseClock.startRound p x.etaReal x.time
        x.clock x.ledger.pending = .ok started)
      (reason : CollectionFailure)
  | continuing
      (core : CollectionCoreValid x)
      (prepared : CoordinatorCollectionInteractive.PreparedSnapshot x)
      (recorderBoundaryValid : prepared.clockStarted.clock.g ≤ p.T + 1)
      (currentScoresChecked : collectionCurrentScoresCheck x = true)
  | laterReconstructionFailure
      (core : CollectionCoreValid x)
      (consistent : LaterAssignmentStartOperation.LocalConsistency
        x.payload (collectionOperationLedger x core.payload_n_eq))
      (started : CoordinatorPhaseClock.StartRoundResult p)
      (startRound_eq : CoordinatorPhaseClock.startRound p x.etaReal x.time
        x.clock x.ledger.pending = .ok started)
      (instruction : CoordinatorPhaseClock.AssignmentStartInstruction p)
      (assignmentStart_eq : started.assignmentStart = some instruction)
      (reason : AssignmentScoreReconstruction.Failure)
      (later_eq : LaterAssignmentStartOperation.laterAssignmentStart
        x.payload (collectionOperationLedger x core.payload_n_eq) instruction x.row consistent =
          .reconstructionFailure reason)
  | laterPrefixFailure
      (core : CollectionCoreValid x)
      (consistent : LaterAssignmentStartOperation.LocalConsistency
        x.payload (collectionOperationLedger x core.payload_n_eq))
      (started : CoordinatorPhaseClock.StartRoundResult p)
      (startRound_eq : CoordinatorPhaseClock.startRound p x.etaReal x.time
        x.clock x.ledger.pending = .ok started)
      (instruction : CoordinatorPhaseClock.AssignmentStartInstruction p)
      (assignmentStart_eq : started.assignmentStart = some instruction)
      (arm : Option (Fin p.K))
      (reason : CheckedPrefixSampler.FailureReason)
      (later_eq : LaterAssignmentStartOperation.laterAssignmentStart
        x.payload (collectionOperationLedger x core.payload_n_eq) instruction x.row consistent =
          .prefixFailure arm reason)
  | laterOrientationFailure
      (core : CollectionCoreValid x)
      (consistent : LaterAssignmentStartOperation.LocalConsistency
        x.payload (collectionOperationLedger x core.payload_n_eq))
      (started : CoordinatorPhaseClock.StartRoundResult p)
      (startRound_eq : CoordinatorPhaseClock.startRound p x.etaReal x.time
        x.clock x.ledger.pending = .ok started)
      (instruction : CoordinatorPhaseClock.AssignmentStartInstruction p)
      (assignmentStart_eq : started.assignmentStart = some instruction)
      (set : PrefixSetSampler.SetCarrier p.K p.m)
      (later_eq : LaterAssignmentStartOperation.laterAssignmentStart
        x.payload (collectionOperationLedger x core.payload_n_eq) instruction x.row consistent =
          .orientationFailure set)
  | laterChoiceFailure
      (core : CollectionCoreValid x)
      (consistent : LaterAssignmentStartOperation.LocalConsistency
        x.payload (collectionOperationLedger x core.payload_n_eq))
      (started : CoordinatorPhaseClock.StartRoundResult p)
      (startRound_eq : CoordinatorPhaseClock.startRound p x.etaReal x.time
        x.clock x.ledger.pending = .ok started)
      (instruction : CoordinatorPhaseClock.AssignmentStartInstruction p)
      (assignmentStart_eq : started.assignmentStart = some instruction)
      (output : LaterAssignmentStartOperation.SuccessfulStart
        x.payload (collectionOperationLedger x core.payload_n_eq) instruction x.row)
      (localConsistency_eq : output.localConsistency = consistent)
      (clockData : CoordinatorAssignmentRegisterInstall.LaterStartRoundEvidence
        output)
      (installation : CoordinatorAssignmentRegisterInstall.LaterInstallation
        output clockData)
      (reason : CollectionFailure)
  | laterChosen
      (core : CollectionCoreValid x)
      (consistent : LaterAssignmentStartOperation.LocalConsistency
        x.payload (collectionOperationLedger x core.payload_n_eq))
      (started : CoordinatorPhaseClock.StartRoundResult p)
      (startRound_eq : CoordinatorPhaseClock.startRound p x.etaReal x.time
        x.clock x.ledger.pending = .ok started)
      (instruction : CoordinatorPhaseClock.AssignmentStartInstruction p)
      (assignmentStart_eq : started.assignmentStart = some instruction)
      (output : LaterAssignmentStartOperation.SuccessfulStart
        x.payload (collectionOperationLedger x core.payload_n_eq) instruction x.row)
      (localConsistency_eq : output.localConsistency = consistent)
      (clockData : CoordinatorAssignmentRegisterInstall.LaterStartRoundEvidence
        output)
      (installation : CoordinatorAssignmentRegisterInstall.LaterInstallation
        output clockData)
      (selection : ArmSelection installation.registers.payload started
        instruction.time installation.registers.complementWeights x.row)

/-- The score-domain obligation on a returned continuing choice, using the
same accepted current-score formula as its weights. Other outcomes use none
of these continuing weights. -/
def CollectionOutcome.currentScoreDomain {x : CollectionInput p} :
    CollectionOutcome x → Prop
  | .continuing core _ _ _ =>
      ∀ (a : Fin p.K) (ha : a ∉ x.payload.slowSet.1),
        CoordinatorCollectionUpRoundStep.complementCurrentScore x.ledger x.payload
          core.ledger_valid core.assignment_eq a ha ≤ p.T * D p
  | _ => True

/-- The combined pre-choice input is a disjoint sum of the actual first
source data, live local registers, and collection interactive carrier. -/
inductive Input (p : Parameters) where
  | first (source : FirstInput p)
  | live (source : LiveInput p)
  | collection (source : CollectionInput p)

/-- The dependent output preserves the exact result type and evidence of its
selected input branch. -/
inductive Outcome : Input p → Type where
  | first {source : FirstInput p} : FirstOutcome source → Outcome (.first source)
  | live {source : LiveInput p} : LiveOutcome source → Outcome (.live source)
  | collection {source : CollectionInput p} :
      CollectionOutcome source → Outcome (.collection source)

/-- Perform the first assignment's actual installation and call arm choice
directly on that installation's first `StartRoundResult`. -/
noncomputable def dispatchFirst (x : FirstInput p) : FirstOutcome x := by
  classical
  let launch := firstLaunchInput x
  let installed := CoordinatorAssignmentRegisterInstall.installFirst launch
  let started := installed.startRoundResult
  let payload := installed.registers.payload
  let weights := installed.registers.complementWeights
  let cutoff := CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u
  have hpayload : payload = AssignmentStartPayload.Input.ofFirstAssignment launch :=
    CoordinatorAssignmentRegisterInstall.first_registers_payload launch
  have hstarted :
      CoordinatorLocalArmChoice.assignmentStart payload ≤
        CoordinatorLocalArmChoice.sourceRound installed.registers.time := by
    simp only [CoordinatorLocalArmChoice.assignmentStart,
      CoordinatorLocalArmChoice.sourceRound]
    rw [hpayload, CoordinatorAssignmentRegisterInstall.first_registers_time]
    rfl
  have hcutoff :
      CoordinatorLocalArmChoice.assignmentStart payload ≤
        CoordinatorLocalArmChoice.cutoffRound cutoff := by
    rw [hpayload]
    simp [cutoff, started, installed,
      CoordinatorLiveChoiceRecorderStep.cutoffFromClock,
      CoordinatorLocalArmChoice.assignmentStart,
      CoordinatorLocalArmChoice.cutoffRound,
      AssignmentStartPayload.Input.ofFirstAssignment,
      CoordinatorAssignmentRegisterInstall.installFirst,
      CoordinatorAssignmentRegisterInstall.firstStartRoundResult]
  have hweights : ∀ j, 0 < weights j ∧ payload.anchor j.1 ≤ weights j ∧
      weights j ≤ 2 * payload.anchor j.1 := by
    intro j
    have hw : weights j = 1 := by
      simpa [weights, installed] using
        CoordinatorAssignmentRegisterInstall.first_complementWeight_one launch j
    have ha : payload.anchor j.1 = 1 := by
      simpa [payload, installed] using
        CoordinatorAssignmentRegisterInstall.first_payload_anchor_one launch j.1
    rw [hw, ha]
    norm_num
  have hchoice : CoordinatorLocalArmChoice.ChoiceInputsValid payload cutoff
      installed.registers.time weights :=
    CoordinatorLocalArmChoice.choiceInputsValid_mk payload cutoff
      installed.registers.time weights hstarted hcutoff hweights
  have hboundary : started.clock.g ≤ p.T + 1 := by
    change (CoordinatorAssignmentRegisterInstall.firstStartRoundResult launch).clock.g ≤
      p.T + 1
    simpa [CoordinatorAssignmentRegisterInstall.firstStartRoundResult] using
      (CoordinatorAssignmentRegisterInstall.first_new_grid_boundary_valid launch).2
  have hnonempty := CoordinatorLiveChoiceRecorderStep.coordinatorArmChoice_ne_none
    payload started.pending cutoff installed.registers.time weights x.row hchoice
  match hselected : CoordinatorLocalArmChoice.coordinatorArmChoice payload
      started.pending cutoff installed.registers.time weights x.row with
  | none => exact False.elim (hnonempty hselected)
  | some arm =>
      exact .chosen installed {
        arm := arm
        choiceInputsValid := hchoice
        recorderBoundaryValid := hboundary
        armChoice_eq := hselected }

/-- The cutoff dispatcher returns the clock result from its one original
`StartRound` call. -/
theorem cutoffDispatch_startResult_eq
    {eta : LearningRate}
    (r : CoordinatorLiveChoiceRecorderStep.Registers p eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ)
    (out : CoordinatorStartRoundCutoffDispatch.Output r q base)
    (h : CoordinatorStartRoundCutoffDispatch.dispatch r q base = .ok out) :
    CoordinatorPhaseClock.startRound p eta.val r.time r.priorClock r.clockPending =
      .ok out.startResult := by
  classical
  unfold CoordinatorStartRoundCutoffDispatch.dispatch at h
  cases hstart : CoordinatorPhaseClock.startRound p eta.val r.time
      r.priorClock r.clockPending with
  | error failure => simp [hstart] at h
  | ok started =>
      simp only [hstart] at h
      have hstruct := Except.ok.inj h
      have hfield := congrArg
        CoordinatorStartRoundCutoffDispatch.Output.startResult hstruct
      exact congrArg
        (fun result : CoordinatorPhaseClock.StartRoundResult p =>
          (Except.ok result : Except CoordinatorPhaseClock.ClockFailure
            (CoordinatorPhaseClock.StartRoundResult p))) hfield

/-- A successful phase-clock initialization stamps the actual current round,
not an independent time coordinate. -/
theorem startRound_initializeAt_time
    {eta : LearningRate}
    (time otherTime : Fin p.T)
    (clock : CoordinatorPhaseClock.ClockRegisters p)
    (pending : Finset (Fin (p.m - 1)))
    (result : CoordinatorPhaseClock.StartRoundResult p)
    (hstart : CoordinatorPhaseClock.startRound p eta.val time clock pending =
      .ok result)
    (hcommand : result.ledgerCommand = some (.initializeAt otherTime)) :
    otherTime = time := by
  classical
  unfold CoordinatorPhaseClock.startRound at hstart
  by_cases hparameter :
      CoordinatorPhaseClock.proposalParameterValid p eta.val
  · rw [ite_eq_left hparameter] at hstart
    by_cases hclock : CoordinatorPhaseClock.clockRegistersValid p eta.val clock
    · rw [dite_eq_left hclock] at hstart
      by_cases htime : CoordinatorPhaseClock.startRoundTimeValid p time clock
      · rw [dite_eq_left htime] at hstart
        cases hdetect : CoordinatorPhaseClock.detectCutoff clock time with
        | error failure =>
            simp [hdetect] at hstart
        | ok decision =>
            rw [hdetect] at hstart
            cases decision with
            | cutoff sigma hsigma =>
                have hnoStart :=
                  CoordinatorPhaseClock.sourceStartTest_false_after_cutoff p sigma time
                have hnoStart' :
                    ¬ CoordinatorPhaseClock.sourceStartTest clock.sigma (some time)
                      time Finset.univ := by
                  simpa [hsigma] using hnoStart
                simp [hnoStart'] at hstart
                have hcommandEq := congrArg
                  CoordinatorPhaseClock.StartRoundResult.ledgerCommand
                  (Except.ok.inj hstart)
                have hcommands :
                    some (CoordinatorPhaseClock.CollectionLedgerCommand.initializeAt time) =
                      some (.initializeAt otherTime) := by
                  exact hcommandEq.trans hcommand
                have hcommandEq :
                    CoordinatorPhaseClock.CollectionLedgerCommand.initializeAt time =
                      .initializeAt otherTime := by
                  injection hcommands with hcommandEq
                injection hcommandEq with htimeEq
                exact htimeEq.symm
            | noCutoff =>
                by_cases hready :
                    CoordinatorPhaseClock.sourceStartTest clock.sigma clock.u time pending
                · by_cases hgrid : CoordinatorPhaseClock.newGridBoundaryValid p time
                      (FollowerCutoffScan.gridBoundary p eta.val time)
                  · simp [hready, hgrid] at hstart
                    have hcmd := congrArg
                      CoordinatorPhaseClock.StartRoundResult.ledgerCommand
                      (Except.ok.inj hstart)
                    simp [hcommand] at hcmd
                  · simp [hready, hgrid] at hstart
                · simp [hready] at hstart
                  have hcmd := congrArg
                    CoordinatorPhaseClock.StartRoundResult.ledgerCommand
                    (Except.ok.inj hstart)
                  simp [hcommand] at hcmd
      · simp [htime] at hstart
    · simp [hclock] at hstart
  · simp [hparameter] at hstart

/-- A checked successful collection initialization is exactly the candidate
ledger built from the pre-round owned values and retained follower bases. -/
theorem cutoffDispatch_ledger_eq_candidate
    {eta : LearningRate}
    (r : CoordinatorLiveChoiceRecorderStep.Registers p eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ)
    (out : CoordinatorStartRoundCutoffDispatch.Output r q base)
    (ledger : CoordinatorStartRoundCutoffDispatch.NewLedger r)
    (hdispatch : CoordinatorStartRoundCutoffDispatch.dispatch r q base = .ok out)
    (hinit : out.collectionInitialization = .success (some ledger)) :
    out.startResult.ledgerCommand = some (.initializeAt r.time) ∧
      CoordinatorStartRoundCutoffDispatch.initializationDomainValid r q base r.time ∧
      ledger = CoordinatorStartRoundCutoffDispatch.collectionStartLedger
        r q base r.time := by
  classical
  have hstart := cutoffDispatch_startResult_eq r q base out hdispatch
  have hfield : out.collectionInitialization =
      match out.startResult.ledgerCommand with
      | some (.initializeAt time) =>
          CoordinatorStartRoundCutoffDispatch.checkedOptionIfValid
            (decide (CoordinatorStartRoundCutoffDispatch.initializationDomainValid
              r q base time))
            (CoordinatorCollectionLedger.startCollectionChecked p eta.val eta.property
              (LaterAssignmentStartOperation.oldPayloadSourceCap r.payload)
              r.payload.n r.payload.n_eq_eta_mul_D
              (CoordinatorStartRoundCutoffDispatch.ledgerAssignment r)
              (r.payload.sigma.val + 1) (time.val + 1) r.gridBoundary base
              (CoordinatorStartRoundCutoffDispatch.outsideRegisters r q))
      | _ => .success none := by
    unfold CoordinatorStartRoundCutoffDispatch.dispatch at hdispatch
    rw [hstart] at hdispatch
    have hstruct := Except.ok.inj hdispatch
    have hstartField := congrArg
      CoordinatorStartRoundCutoffDispatch.Output.startResult hstruct
    have hinitializationField := congrArg
      CoordinatorStartRoundCutoffDispatch.Output.collectionInitialization hstruct
    rw [← hstartField]
    exact hinitializationField.symm
  have hcommandTime : out.startResult.ledgerCommand = some (.initializeAt r.time) := by
    cases hcommand : out.startResult.ledgerCommand with
    | none => simp [hfield, hcommand] at hinit
    | some command =>
        cases command with
        | accumulateLocalServiceAt time => simp [hfield, hcommand] at hinit
        | initializeAt time =>
            have htime := startRound_initializeAt_time r.time time r.priorClock
              r.clockPending out.startResult hstart hcommand
            subst time
            rfl
  have hdomain :
      CoordinatorStartRoundCutoffDispatch.initializationDomainValid r q base r.time := by
    rw [hfield, hcommandTime] at hinit
    cases hchecked : CoordinatorCollectionLedger.startCollectionChecked p eta.val
        eta.property (LaterAssignmentStartOperation.oldPayloadSourceCap r.payload)
        r.payload.n
        r.payload.n_eq_eta_mul_D
        (CoordinatorStartRoundCutoffDispatch.ledgerAssignment r)
        (r.payload.sigma.val + 1) (r.time.val + 1) r.gridBoundary base
        (CoordinatorStartRoundCutoffDispatch.outsideRegisters r q) with
    | invalid => simp [CoordinatorStartRoundCutoffDispatch.checkedOptionIfValid,
        hchecked] at hinit
    | rejected value => simp [CoordinatorStartRoundCutoffDispatch.checkedOptionIfValid,
        hchecked] at hinit
    | success value =>
        have hv : decide
            (CoordinatorStartRoundCutoffDispatch.initializationDomainValid r q base r.time) =
              true := by
          by_contra hfalse
          simp [CoordinatorStartRoundCutoffDispatch.checkedOptionIfValid,
            hchecked, hfalse] at hinit
        exact of_decide_eq_true hv
  have hsuccess := CoordinatorStartRoundCutoffDispatch.startCollectionChecked_success_of_domains
    r q base r.time hdomain
  have hcandidate : ledger =
      CoordinatorStartRoundCutoffDispatch.collectionStartLedger r q base r.time := by
    have hdomainBool : decide
        (CoordinatorStartRoundCutoffDispatch.initializationDomainValid r q base r.time) =
          true := decide_eq_true_eq.mpr hdomain
    have hinit' :
        CoordinatorCollectionLedger.Checked.success
          (some (CoordinatorStartRoundCutoffDispatch.collectionStartLedger
            r q base r.time)) =
          CoordinatorCollectionLedger.Checked.success (some ledger) := by
      simpa [hfield, hcommandTime,
        CoordinatorStartRoundCutoffDispatch.checkedOptionIfValid,
        hdomainBool, hsuccess] using hinit
    exact Option.some.inj (CoordinatorCollectionLedger.Checked.success.inj hinit').symm
  exact ⟨hcommandTime, hdomain, hcandidate⟩

/-- Consume the live start-round/cutoff dispatch once. An accepted cutoff
goes directly to arm choice on the changed cutoff frame; an unchanged live
frame is packaged with the same original clock result. -/
noncomputable def dispatchLive (x : LiveInput p) : LiveOutcome x := by
  classical
  let r := x.registers
  let q := x.ownedRegisters
  let base := x.followerBaseScore
  match hdispatch : CoordinatorStartRoundCutoffDispatch.dispatch r q base with
  | .error failure => exact .clockFailure failure hdispatch
  | .ok dispatched =>
      have hstart := cutoffDispatch_startResult_eq r q base dispatched hdispatch
      match hinitialization : dispatched.collectionInitialization with
      | .invalid =>
          exact .initializerFailure dispatched hstart .invalid hinitialization
      | .rejected value =>
          exact .initializerFailure dispatched hstart (.rejected value) hinitialization
      | .success none =>
          if hframe : CoordinatorLiveChoiceRecorderStep.unchangedLiveClockFrame
              r dispatched.startResult then
            if hpayload : r.priorClock.sigma = some r.payload.sigma then
              if hgrid : r.gridBoundary = r.priorClock.g then
                if hscore : r.scoreDomainValid then
                  if hqueue : q.queueDomainValid then
                    if hprevious : q.previousServiceDomainValid then
                      if hbase : ∀ i, base i ≤ p.T * D p then
                        if hlive : CoordinatorLocalArmChoice.assignmentIsLive
                            r.payload
                              (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
                                dispatched.startResult.clock.u) r.time then
                          let weights := r.complementWeights
                          let cutoff :=
                            CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
                              dispatched.startResult.clock.u
                          if hchoice : CoordinatorLocalArmChoice.ChoiceInputsValid
                              r.payload cutoff r.time weights then
                            if hboundary : dispatched.startResult.clock.g ≤ p.T + 1 then
                              if henvelope : r.complementEnvelopeValid then
                                let selected :=
                                  CoordinatorLocalArmChoice.coordinatorArmChoice
                                    r.payload dispatched.startResult.pending cutoff
                                    r.time weights x.row
                                have hnonempty :=
                                  CoordinatorLiveChoiceRecorderStep.coordinatorArmChoice_ne_none
                                    r.payload dispatched.startResult.pending cutoff r.time
                                    weights x.row hchoice
                                match hselected : selected with
                                | none => exact False.elim (hnonempty hselected)
                                | some arm =>
                                    have hpending :
                                        dispatched.startResult.pending =
                                          r.pendingAtChoice := by
                                      exact hframe.2.1.trans
                                        (CoordinatorLiveChoiceRecorderStep.Registers.clockPending_eq r)
                                    have hchoiceTime :
                                        CoordinatorLocalArmChoice.SourceTimeValid r.payload
                                          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
                                            r.priorClock.u) r.time := by
                                      simpa [cutoff, hframe.1] using hchoice.time
                                    have hrecorderBoundary : r.gridBoundary ≤ p.T + 1 := by
                                      calc
                                        r.gridBoundary = r.priorClock.g := hgrid
                                        _ ≤ p.T + 1 := by
                                          simpa only [hframe.1] using hboundary
                                    let continuation :
                                        CoordinatorLiveChoiceRecorderStep.Continuation
                                          r x.row := {
                                      startRoundResult := dispatched.startResult
                                      clockFrame := hframe
                                      payloadClockStart := hpayload
                                      gridBoundary_eq_clock := hgrid
                                      sourceTimeValid := by
                                        exact hchoiceTime
                                      choiceInputsValid := by
                                        simpa [cutoff, hframe.1] using hchoice
                                      scoreDomainValid := hscore
                                      recorderInputsValid := ⟨hrecorderBoundary, henvelope⟩
                                      confirmationInputsValid := by
                                        apply CoordinatorLocalArmChoice.confirmationInputsValid_mk
                                          r.payload
                                          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
                                            r.priorClock.u) r.time
                                        · exact hchoiceTime.assignment_started
                                        · exact hchoiceTime.cutoff_after_start
                                      currentControl := x.row.2 r.time
                                      currentControl_eq := rfl
                                      preChoiceMode :=
                                        .live (decide (r.pendingAtChoice = ∅))
                                      preChoiceMode_eq := rfl
                                      armChoice_ne_none := by
                                        simpa [cutoff, hframe.1, hpending] using hnonempty }
                                    exact .continuingChosen dispatched hstart continuation {
                                      arm := arm
                                      choiceInputsValid := hchoice
                                      recorderBoundaryValid := hboundary
                                      armChoice_eq := hselected }
                              else exact (.localFailure dispatched hstart
                                .recorderBoundaryFailure)
                            else exact (.localFailure dispatched hstart
                              .recorderBoundaryFailure)
                          else exact .localFailure dispatched hstart .choiceDomainFailure
                        else exact .localFailure dispatched hstart .choiceDomainFailure
                      else exact .localFailure dispatched hstart .baseScoreDomainFailure
                    else exact .localFailure dispatched hstart .previousServiceDomainFailure
                  else exact .localFailure dispatched hstart .queueDomainFailure
                else exact .localFailure dispatched hstart .scoreDomainFailure
              else exact .localFailure dispatched hstart .gridBoundaryMismatch
            else exact .localFailure dispatched hstart .payloadClockMismatch
          else exact .localFailure dispatched hstart .frameMismatch
      | .success (some ledger) =>
          have ⟨hcommand, hdomains, hledger⟩ := cutoffDispatch_ledger_eq_candidate
            r q base dispatched ledger hdispatch hinitialization
          have hshape := CoordinatorStartRoundCutoffDispatch.startRound_initializeAt_shape
            r dispatched.startResult hstart hcommand
          if hchoice : CoordinatorLocalArmChoice.ChoiceInputsValid r.payload
              (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
                dispatched.startResult.clock.u) r.time r.complementWeights then
            if hboundary : dispatched.startResult.clock.g ≤ p.T + 1 then
              if henvelope : r.complementEnvelopeValid then
                let selected := CoordinatorLocalArmChoice.coordinatorArmChoice
                  r.payload dispatched.startResult.pending
                  (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
                    dispatched.startResult.clock.u)
                  r.time r.complementWeights x.row
                have hnonempty :=
                  CoordinatorLiveChoiceRecorderStep.coordinatorArmChoice_ne_none
                    r.payload dispatched.startResult.pending
                    (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
                      dispatched.startResult.clock.u)
                    r.time r.complementWeights x.row hchoice
                match hselected : selected with
                | none => exact False.elim (hnonempty hselected)
                | some arm =>
                    exact .cutoffChosen dispatched hstart ledger hinitialization
                      hledger hdomains hshape.1 hshape.2.1 hshape.2.2 {
                        arm := arm
                        choiceInputsValid := hchoice
                        recorderBoundaryValid := hboundary
                        armChoice_eq := hselected }
              else exact .localFailure dispatched hstart .recorderBoundaryFailure
            else exact .localFailure dispatched hstart .recorderBoundaryFailure
          else exact .localFailure dispatched hstart .choiceDomainFailure

/-- Call the carried collection clock once. Pending replies retain the
original payload and prepared local carrier; an empty pending set runs the
actual reconstruction and later-start computation before installation. -/
noncomputable def dispatchCollection (x : CollectionInput p) :
    CollectionOutcome x := by
  classical
  match hstart : CoordinatorPhaseClock.startRound p x.etaReal x.time
      x.clock x.ledger.pending with
  | .error failure => exact .clockFailure failure hstart
  | .ok started =>
      if hcore : CollectionCoreValid x then
        let operationLedger := collectionOperationLedger x hcore.payload_n_eq
        if hpending : x.ledger.pending.Nonempty then
          if hscores : collectionCurrentScoresCheck x = true then
            let weights := CoordinatorCollectionInteractive.PreObservationInputs.weights
              x hcore.ledger_valid hcore.assignment_eq
            let cutoff := some (CoordinatorCollectionUpRoundStep.localCutoff x.cutoffIndex)
            have hframe :
                started.clock = x.clock ∧
                  started.pending = x.ledger.pending ∧
                  started.ledgerCommand = none ∧
                  started.assignmentStart = none := by
              have hut : x.cutoffIndex.val ≤ x.time.val := by
                have htimeParts : x.payload.sigma.val < x.time.val ∧
                    x.cutoffIndex.val ≤ x.time.val := by
                  simpa [CoordinatorPhaseClock.startRoundTimeValid,
                    hcore.clock_sigma_eq, hcore.clock_cutoff_eq] using
                    hcore.clock_start_time_valid
                exact htimeParts.2
              have hknown := CoordinatorPhaseClock.startRound_collection_pending
                p x.etaReal x.time x.payload.sigma x.cutoffIndex x.clock
                x.ledger.pending hcore.clock_parameter_valid
                hcore.clock_registers_valid hcore.clock_sigma_eq
                hcore.clock_cutoff_eq hut
                (Finset.nonempty_iff_ne_empty.mp hpending)
              have heq := Except.ok.inj (hstart.symm.trans hknown)
              rw [heq]
              exact ⟨rfl, rfl, rfl, rfl⟩
            have hcutoff :
                CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u =
                  cutoff := by
              rw [hframe.1, hcore.clock_cutoff_eq]
              rfl
            if hchoice : CoordinatorLocalArmChoice.ChoiceInputsValid x.payload cutoff
                x.time weights then
              have hchoiceActual :
                  CoordinatorLocalArmChoice.ChoiceInputsValid x.payload
                    (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
                    x.time weights := by
                simpa [hcutoff] using hchoice
              have hnonempty :=
                CoordinatorLiveChoiceRecorderStep.coordinatorArmChoice_ne_none
                  x.payload started.pending
                  (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
                  x.time weights x.row hchoiceActual
              let selected := CoordinatorLocalArmChoice.coordinatorArmChoice x.payload
                started.pending
                (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
                x.time weights x.row
              match hselected : selected with
              | none => exact False.elim (hnonempty hselected)
              | some arm =>
                  have hboundary : started.clock.g ≤ p.T + 1 := by
                    have hgrid := CoordinatorPhaseClock.clockRegistersValid_gridDomain
                      p x.etaReal x.clock hcore.clock_registers_valid
                    have hgrid' := hgrid
                    simp only [CoordinatorPhaseClock.clockGridDomain,
                      hcore.clock_sigma_eq] at hgrid'
                    simpa [hframe.1] using hgrid'.2
                  have hinputs :
                      CoordinatorCollectionInteractive.PreInputsValid x := {
                    ledger_valid := hcore.ledger_valid
                    ledger_ready := hcore.ledger_ready
                    pending_nonempty := hpending
                    assignment_eq := hcore.assignment_eq
                    base_score_eq := hcore.base_score_eq
                    clock_parameter_valid := hcore.clock_parameter_valid
                    clock_registers_valid := hcore.clock_registers_valid
                    clock_start_time_valid := hcore.clock_start_time_valid
                    clock_sigma_eq := hcore.clock_sigma_eq
                    clock_cutoff_eq := hcore.clock_cutoff_eq
                    ledger_sigma_eq := hcore.ledger_sigma_eq
                    ledger_cutoff_eq := hcore.ledger_cutoff_eq
                    ledger_freeze_eq := hcore.ledger_freeze_eq
                    ledger_cursor_eq := hcore.ledger_cursor_eq
                    decoder_bank_valid := hcore.decoder_bank_valid
                    choice_valid := hchoice }
                  let prepared : CoordinatorCollectionInteractive.PreparedSnapshot x := {
                    inputsValid := hinputs
                    clockStarted := started
                    clockStarted_eq := hstart
                    clockStarted_frame := hframe
                    arm := arm
                    armChoice_eq := by
                      change CoordinatorLocalArmChoice.coordinatorArmChoice x.payload
                        started.pending
                        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
                        x.time weights x.row = some arm at hselected
                      rw [hcutoff] at hselected
                      simpa [weights,
                        CoordinatorCollectionInteractive.PreObservationInputs.weights]
                        using hselected }
                  exact .continuing hcore prepared hboundary hscores
            else exact .coreFailure hcore started hstart .choiceDomainFailure
          else exact .coreFailure hcore started hstart .currentScoreDomainFailure
        else
          let hpendingEmpty : x.ledger.pending = ∅ :=
            Finset.not_nonempty_iff_eq_empty.mp hpending
          match hassignment : started.assignmentStart with
          | none => exact .coreFailure hcore started hstart .assignmentInstructionMissing
          | some instruction =>
              have hclockEquations :=
                CoordinatorPhaseClock.startRound_assignment_effect p x.etaReal x.time
                  x.clock x.ledger.pending started instruction
                  hcore.clock_parameter_valid hcore.clock_registers_valid
                  hcore.clock_start_time_valid hstart hassignment
              rcases hclockEquations with
                ⟨htime, _, hnewSigma, hnewCutoff, hnewGrid, _, hnewPending, _⟩
              let consistent : LaterAssignmentStartOperation.LocalConsistency
                  x.payload operationLedger := {
                oldStart_eq := by
                  simpa [CoordinatorRecorderComplementBridge.sourceStart,
                    operationLedger, collectionOperationLedger] using
                    hcore.ledger_sigma_eq.symm
                oldAssignment_eq := fun i => by
                  simpa [operationLedger, collectionOperationLedger] using
                    (hcore.assignment_eq i).symm
                oldFreezeAt := x.ledger.freezeAt
                oldFreezeAt_eq := by rfl }
              match hlater : LaterAssignmentStartOperation.laterAssignmentStart
                  x.payload operationLedger instruction x.row consistent with
              | .reconstructionFailure reason =>
                  exact .laterReconstructionFailure hcore consistent started hstart
                    instruction hassignment reason hlater
              | .prefixFailure arm reason =>
                  exact .laterPrefixFailure hcore consistent started hstart instruction
                    hassignment arm reason hlater
              | .orientationFailure set =>
                  exact .laterOrientationFailure hcore consistent started hstart
                    instruction hassignment set hlater
              | .success output hlocal =>
                  have hfreeze : x.clock.g = output.localConsistency.oldFreezeAt := by
                    calc
                      x.clock.g = x.ledger.freezeAt := hcore.ledger_freeze_eq.symm
                      _ = consistent.oldFreezeAt := consistent.oldFreezeAt_eq.symm
                      _ = output.localConsistency.oldFreezeAt := by rw [hlocal]
                  let clockData :
                      CoordinatorAssignmentRegisterInstall.LaterStartRoundEvidence
                        output := {
                    priorClock := x.clock
                    pending := x.ledger.pending
                    proposalParameterValid := hcore.clock_parameter_valid
                    priorClockValid := hcore.clock_registers_valid
                    startTimeValid := by
                      rw [htime]
                      exact hcore.clock_start_time_valid
                    result := started
                    startRound_eq := by
                      rw [htime]
                      exact hstart
                    assignmentStart_eq := hassignment
                    priorSigma_eq := hcore.clock_sigma_eq
                    priorGrid_eq_freezeAt := hfreeze }
                  let installation :=
                    CoordinatorAssignmentRegisterInstall.installLater output clockData
                  have hregisterDomains :=
                    CoordinatorAssignmentRegisterInstall.later_register_domains
                      output clockData
                  rcases hregisterDomains with ⟨hscore, hqueue, hprevious⟩
                  have hboundary : started.clock.g ≤ p.T + 1 := by
                    have hgrid :
                        CoordinatorPhaseClock.clockGridDomain p started.clock := by
                      simpa [hnewSigma] using started.gridDomain
                    have hgrid' := hgrid
                    simp only [CoordinatorPhaseClock.clockGridDomain, hnewSigma] at hgrid'
                    exact hgrid'.2
                  if hbase : ∀ i, installation.retainedBaseScore i ≤ p.T * D p then
                    if hchoice : CoordinatorLocalArmChoice.ChoiceInputsValid
                        installation.registers.payload
                        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
                          started.clock.u)
                        instruction.time installation.registers.complementWeights then
                      if hrecorder : installation.registers.complementEnvelopeValid then
                        let selected := CoordinatorLocalArmChoice.coordinatorArmChoice
                          installation.registers.payload started.pending
                          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
                            started.clock.u)
                          instruction.time installation.registers.complementWeights x.row
                        have hnonempty :=
                          CoordinatorLiveChoiceRecorderStep.coordinatorArmChoice_ne_none
                            installation.registers.payload started.pending
                            (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
                              started.clock.u)
                            instruction.time installation.registers.complementWeights x.row
                            hchoice
                        match hselected : selected with
                        | none => exact False.elim (hnonempty hselected)
                        | some arm =>
                            exact .laterChosen hcore consistent started hstart instruction
                              hassignment output hlocal clockData installation {
                                arm := arm
                                choiceInputsValid := hchoice
                                recorderBoundaryValid := hboundary
                                armChoice_eq := hselected }
                      else exact (.laterChoiceFailure hcore consistent started hstart instruction
                        hassignment output hlocal clockData installation
                        .recorderBoundaryFailure)
                    else exact (.laterChoiceFailure hcore consistent started hstart instruction
                      hassignment output hlocal clockData installation .choiceDomainFailure)
                  else exact (.laterChoiceFailure hcore consistent started hstart instruction
                    hassignment output hlocal clockData installation .stateDomainFailure)
      else exact .localFailure started hstart hcore .stateDomainFailure

/-- Every computed continuing choice satisfies the checked current-score
domain. This statement takes no score bound, valid execution, or successful
choice as an input. Clock and domain failures remain explicit outcomes. -/
theorem dispatchCollection_currentScoreDomain (x : CollectionInput p) :
    (dispatchCollection x).currentScoreDomain := by
  cases dispatchCollection x
  case continuing core prepared boundary hchecked =>
    exact (collectionCurrentScoresCheck_iff x core).mp hchecked
  all_goals trivial

/-- On the continuing branch, a failed actual numeric guard returns exactly
its distinct domain-failure tag, with the original one-call clock evidence.
The clock-success equation, checked core and nonempty pending set specify the
branch; none is a score-bound or physical reachability premise. -/
theorem dispatchCollection_rejects_currentScores (x : CollectionInput p)
    (core : CollectionCoreValid x) (hpending : x.ledger.pending.Nonempty)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (hstart : CoordinatorPhaseClock.startRound p x.etaReal x.time
      x.clock x.ledger.pending = .ok started)
    (hfailed : collectionCurrentScoresCheck x = false) :
    dispatchCollection x =
      .coreFailure core started hstart .currentScoreDomainFailure := by
  classical
  unfold dispatchCollection
  split
  · rename_i failure hfailure
    rw [hstart] at hfailure
    contradiction
  · rename_i result hresult
    have heq : result = started := Except.ok.inj (hresult.symm.trans hstart)
    subst result
    simp only [dite_eq_left core, dite_eq_left hpending,
      hfailed, Bool.false_eq_true, dite_false]

/-- In particular, any actual known complement sum above TD is rejected on
the continuing branch, regardless of its weight envelope or provenance. -/
theorem dispatchCollection_rejects_currentScore_overflow (x : CollectionInput p)
    (core : CollectionCoreValid x) (hpending : x.ledger.pending.Nonempty)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (hstart : CoordinatorPhaseClock.startRound p x.etaReal x.time
      x.clock x.ledger.pending = .ok started)
    (a : Fin p.K) (ha : a ∉ x.payload.slowSet.1)
    (cutoff : CoordinatorCollectionLedger.CutoffRegister)
    (hcutoff : x.ledger.cutoffRegisters a = some cutoff)
    (hover : p.T * D p < cutoff.score + x.ledger.increment a) :
    dispatchCollection x =
      .coreFailure core started hstart .currentScoreDomainFailure := by
  exact dispatchCollection_rejects_currentScores x core hpending started hstart
    ((collectionCurrentScoresCheck_eq_false_iff x core).mpr
      ⟨a, ha, cutoff, hcutoff, hover⟩)

/-- One public dispatch over the three disjoint pre-choice source views. -/
noncomputable def dispatch : (input : Input p) → Outcome input
  | .first source => .first (dispatchFirst source)
  | .live source => .live (dispatchLive source)
  | .collection source => .collection (dispatchCollection source)

/-- The first-launch view uses exactly the `K+1` values in the original row
slice, including the orientation coordinate. -/
theorem firstLaunchInput_coordinate
    (x : FirstInput p) (i : Fin (p.K + 1)) :
    (firstLaunchInput x).coordinates i =
      (x.row.2 x.time).1 (ContinuousControlSlice.Label.assign i) := by
  exact LaterAssignmentStartOperation.ownAssignmentVector_apply x.row x.time i

/-- The first installation retains its one original initial-clock call and
the first payload built from the derived launch input. -/
theorem firstInstallation_source_fields (x : FirstInput p) :
    let launch := firstLaunchInput x
    let installed := CoordinatorAssignmentRegisterInstall.installFirst launch
    installed.start.coordinates = (firstLaunchInput x).coordinates ∧
    installed.startRound_eq = CoordinatorAssignmentRegisterInstall.first_start_round_success
      (firstLaunchInput x) ∧
    installed.registers.payload = AssignmentStartPayload.Input.ofFirstAssignment
      (firstLaunchInput x) ∧
    installed.registers.time = x.time ∧
    installed.registers.pendingAtChoice = Finset.univ ∧
    (∀ j, installed.registers.complementScores j = 0) ∧
    (∀ j, installed.ownedRegisters.queue j = 0) ∧
    (∀ j, installed.ownedRegisters.previousService j = 0) ∧
    (∀ i, installed.followerBaseScore i = 0) := by
  dsimp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [(CoordinatorAssignmentRegisterInstall.installFirst
      (firstLaunchInput x)).start_eq]
    rfl
  · rfl
  · exact CoordinatorAssignmentRegisterInstall.first_registers_payload _
  · exact CoordinatorAssignmentRegisterInstall.first_registers_time _
  · exact CoordinatorAssignmentRegisterInstall.first_registers_pending _
  · intro j
    exact CoordinatorAssignmentRegisterInstall.first_registers_complement_scores _ j
  · intro j
    exact CoordinatorAssignmentRegisterInstall.first_owned_queue _ j
  · intro j
    exact CoordinatorAssignmentRegisterInstall.first_owned_previous_service _ j
  · intro i
    exact CoordinatorAssignmentRegisterInstall.first_follower_base_score _ i

/-- The first register payload reuses the actual sampled assignment, unit
anchor, rates, exponents, DOWN records, and encoded DOWN words. -/
theorem firstInstallation_payload_identities (x : FirstInput p) :
    let launch := firstLaunchInput x
    let installed := CoordinatorAssignmentRegisterInstall.installFirst launch
    (∀ i : Follower p.m,
      installed.registers.payload.assignment.assigned i =
        installed.start.assignment.assigned i) ∧
    (∀ a : Fin p.K, installed.registers.payload.anchor a = 1) ∧
    (∀ i : Follower p.m,
      installed.registers.payload.downRecord i = installed.start.outgoing i) ∧
    (∀ i : Follower p.m,
      installed.registers.payload.downWord i = installed.start.outgoingWords i) ∧
    (∀ a : Fin p.K,
      installed.registers.payload.rate a = installed.start.recordingRates a) ∧
    (∀ i : Follower p.m,
      installed.registers.payload.exponent
        (installed.start.assignment.assigned i) = launch.exponent i) := by
  dsimp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact congrFun (CoordinatorAssignmentRegisterInstall.first_payload_assignment_eq_start _ ) i
  · intro a
    exact CoordinatorAssignmentRegisterInstall.first_payload_anchor_one _ a
  · intro i
    exact CoordinatorAssignmentRegisterInstall.first_payload_down_record_eq_start _ i
  · intro i
    exact CoordinatorAssignmentRegisterInstall.first_payload_down_word_eq_start _ i
  · intro a
    exact CoordinatorAssignmentRegisterInstall.first_payload_rate_eq_start _ a
  · intro i
    exact CoordinatorAssignmentRegisterInstall.first_payload_exponent_eq_start _ i

/-- The old DOWN queue field remains the immutable assignment-start queue.
Collection's moving queue registers are separately constructed from the
coordinator's currently owned values. -/
theorem retained_down_queue_field
    {eta : LearningRate} (payload : AssignmentStartPayload.Input p eta)
    (i : Follower p.m) :
    (payload.downRecord i).val.q =
      payload.queues (payload.assignment.assigned i) :=
  payload.downRecord_initialQueue i

/-- A successful later-start operation retains the exact complete assignment
vector from the original row and start coordinate. -/
theorem later_successful_sample_is_original
    {eta : LearningRate}
    {old : AssignmentStartPayload.Input p eta}
    {ledger : LaterAssignmentStartOperation.LocalLedger old}
    {instruction : CoordinatorPhaseClock.AssignmentStartInstruction p}
    {row : CompletePublicTable.CompleteRow p}
    (output : LaterAssignmentStartOperation.SuccessfulStart old ledger instruction row) :
    output.assignmentVector =
      LaterAssignmentStartOperation.ownAssignmentVector row instruction.time :=
  LaterAssignmentStartOperation.successful_assignmentVector_is_original_row_projection
    output

/-- Every successful installed later start is classified as corrected or
renewal by the original clock and the reconstruction's retained freeze. -/
theorem later_success_kind_cases
    {eta : LearningRate}
    {old : AssignmentStartPayload.Input p eta}
    {ledger : LaterAssignmentStartOperation.LocalLedger old}
    {instruction : CoordinatorPhaseClock.AssignmentStartInstruction p}
    {row : CompletePublicTable.CompleteRow p}
    (output : LaterAssignmentStartOperation.SuccessfulStart old ledger instruction row)
    (clockData : CoordinatorAssignmentRegisterInstall.LaterStartRoundEvidence output) :
    instruction.kind = .corrected ∨ instruction.kind = .renewal := by
  have hcompat :=
    CoordinatorAssignmentRegisterInstall.later_start_round_compatibility output clockData
  rcases hcompat with ⟨_, _, _, _, _, _, _, _, hkind⟩
  unfold AssignmentScoreReconstruction.expectedLaterStartKind at hkind
  split at hkind <;> simp_all

/-- The corrected start installs the old frozen anchor; renewal installs the
reconstructed current weight. These equations use the successful operation's
actual result and the original clock evidence. -/
theorem later_success_anchor_branches
    {eta : LearningRate}
    {old : AssignmentStartPayload.Input p eta}
    {ledger : LaterAssignmentStartOperation.LocalLedger old}
    {instruction : CoordinatorPhaseClock.AssignmentStartInstruction p}
    {row : CompletePublicTable.CompleteRow p}
    (output : LaterAssignmentStartOperation.SuccessfulStart old ledger instruction row)
    (clockData : CoordinatorAssignmentRegisterInstall.LaterStartRoundEvidence output) :
    (instruction.kind = .corrected →
      instruction.time.val + 1 < output.localConsistency.oldFreezeAt ∧
      instruction.kind = CoordinatorPhaseClock.classifyAssignmentStart
        clockData.priorClock.sigma instruction.time clockData.priorClock.g ∧
      ((CoordinatorAssignmentRegisterInstall.installLater output clockData).registers.payload.anchor) =
        old.anchor) ∧
    (instruction.kind = .renewal →
      output.localConsistency.oldFreezeAt ≤ instruction.time.val + 1 ∧
      instruction.kind = CoordinatorPhaseClock.classifyAssignmentStart
        clockData.priorClock.sigma instruction.time clockData.priorClock.g ∧
      ((CoordinatorAssignmentRegisterInstall.installLater output clockData).registers.payload.anchor) =
          AssignmentScoreReconstruction.currentWeight output.reconstruction) := by
  constructor
  · intro hcorrected
    exact CoordinatorAssignmentRegisterInstall.later_corrected_branch output
      clockData hcorrected
  · intro hrenewal
    exact CoordinatorAssignmentRegisterInstall.later_renewal_branch output
      clockData hrenewal

/-- The later installation's payload records the reconstructed start queues;
the old immutable DOWN queue field is available separately from the original
payload through `retained_down_queue_field`. -/
theorem later_installed_queue_eq_reconstruction
    {eta : LearningRate}
    {old : AssignmentStartPayload.Input p eta}
    {ledger : LaterAssignmentStartOperation.LocalLedger old}
    {instruction : CoordinatorPhaseClock.AssignmentStartInstruction p}
    {row : CompletePublicTable.CompleteRow p}
    (output : LaterAssignmentStartOperation.SuccessfulStart old ledger instruction row)
    (clockData : CoordinatorAssignmentRegisterInstall.LaterStartRoundEvidence output)
    (a : Fin p.K) :
    ((CoordinatorAssignmentRegisterInstall.installLater output clockData).registers.payload.queues) a =
        AssignmentScoreReconstruction.initialQueue output.reconstruction a :=
  CoordinatorAssignmentRegisterInstall.later_payload_queue_eq_initial_queue
    output clockData a

end Bandits.Support.CoordinatorRoundDispatch

end
