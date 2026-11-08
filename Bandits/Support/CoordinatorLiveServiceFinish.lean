/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.CoordinatorLiveChoiceRecorderStep
public import Bandits.Support.CoordinatorRecorderComplementBridge
public import Bandits.Support.CappedService
public import Bandits.Support.QueueReplay

import Bandits.Support.CoordinatorRecordingMeasurability
import Bandits.Support.FollowerDownMeasurability
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Lean.Elab.Tactic.Omega

/-!
# Live coordinator service and round finish

Compose the accepted live coordinator choice and recorder operation with
capped service on exactly the coordinator-owned fast-arm complement, then
apply confirmation and the actual phase-clock `finishRound`.

Sources: `sources/zip4/manuscript/06_interruptions.tex:16-21,37-70,235-296`,
`sources/zip4/manuscript/04_slow_fast_learner.tex:140-174`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:8-14`.

All incoming complement scores, queues, and working prior services remain
explicit local data. This operation makes no physical-history, score-identity,
freshness, global-state, or no-dagger claim. The complete continuous row is
retained separately from the finite output code.
-/

@[expose] public section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.CanonicalFastSampling
open Bandits.Support.ActiveRoundActions
open Bandits.Support.CompletePublicTable
open Bandits.Support.CoordinatorLiveChoiceRecorderStep
open Bandits.Support.CoordinatorRecorderComplementBridge
open Bandits.Support.CoordinatorRecordingOperation
open Bandits.Support.CoordinatorPhaseClock
open Bandits.Support.FollowerCutoffScan

namespace Bandits.Support.CoordinatorLiveServiceFinish

abbrev Parameters := ConstructorDimensions.Parameters
abbrev LearningRate := CoordinatorLiveChoiceRecorderStep.LearningRate

variable {p : Parameters} {eta : LearningRate}

local instance optionRecorderOutputMeasurableSpace (p : Parameters) :
    MeasurableSpace (Option (CoordinatorRecordingOperation.Output p)) := ⊤

local instance optionPendingMeasurableSpace (m : ℕ) :
    MeasurableSpace (Option (Finset (Fin m))) := ⊤

/-- The coordinator's working queues on the actual complement of the
payload's slow set, together with its working previous services. No follower
queue or score is accepted. -/
structure OwnedRegisters (r : CoordinatorLiveChoiceRecorderStep.Registers p eta) where
  queue : FastArm r.payload.slowSet → ℕ
  previousService : FastArm r.payload.slowSet → ℕ

namespace OwnedRegisters

variable {r : CoordinatorLiveChoiceRecorderStep.Registers p eta}

/-- Appendix input domain for the coordinator-owned complement queues. -/
def queueDomainValid (q : OwnedRegisters r) : Prop :=
  ∀ j, q.queue j ≤ p.T * D p

/-- Appendix input domain for carried working last services. -/
def previousServiceDomainValid (q : OwnedRegisters r) : Prop :=
  ∀ j, q.previousService j ≤ D p

end OwnedRegisters

/-- The accepted recorder's raw integer output at its actual gate arm, and
zero on every other complement coordinate. -/
def complementArrival (s : AssignmentStartPayload.Input p eta)
    (recording : CoordinatorRecordingOperation.Output p)
    (j : FastArm s.slowSet) : ℕ :=
  if recording.gateArm = some j.1 then recording.rawArrival else 0

/-- Distinct checked results for every preparation, local-register,
recorder, service-output, confirmation, and finish-clock failure site. The
accepted prepare API exposes clock rejection as one result, retained here as
one tag. -/
inductive Failure where
  | prepareClockRejected
  | prepareClockTransition
  | preparePayloadClockMismatch
  | prepareGridBoundaryMismatch
  | prepareScoreDomainFailure
  | prepareNotLive
  | prepareChoiceDomainFailure
  | prepareRecorderBoundaryFailure
  | prepareComplementEnvelopeFailure
  | queueInputDomainFailure
  | previousServiceInputDomainFailure
  | recorderRejected
  | arrivalOutputDomainFailure
  | serviceOutputDomainFailure
  | scoreOutputDomainFailure
  | queueOutputDomainFailure
  | confirmationRejected
  | finishInvalidProposalParameter
  | finishInvalidClockRegisters
  | finishIncompatibleStartTime
  | finishMissingPriorProposal
  | finishStalePriorProposal
  | finishInvalidNewGridBoundary
  | finishNoLiveAssignment
  | finishIncompatibleFinishTime
  deriving DecidableEq

/-- Preserve each result exposed by the accepted `prepare` API. -/
def prepareFailureCode : CoordinatorLiveChoiceRecorderStep.PrepareFailure → Failure
  | .clockRejected => .prepareClockRejected
  | .clockTransition => .prepareClockTransition
  | .payloadClockMismatch => .preparePayloadClockMismatch
  | .gridBoundaryMismatch => .prepareGridBoundaryMismatch
  | .scoreDomainFailure => .prepareScoreDomainFailure
  | .notLive => .prepareNotLive
  | .choiceDomainFailure => .prepareChoiceDomainFailure
  | .recorderBoundaryFailure => .prepareRecorderBoundaryFailure
  | .complementEnvelopeFailure => .prepareComplementEnvelopeFailure

/-- Preserve the actual failure returned by the final phase-clock operation. -/
def finishFailureCode : CoordinatorPhaseClock.ClockFailure → Failure
  | .invalidProposalParameter => .finishInvalidProposalParameter
  | .invalidClockRegisters => .finishInvalidClockRegisters
  | .incompatibleStartTime => .finishIncompatibleStartTime
  | .missingPriorProposal => .finishMissingPriorProposal
  | .stalePriorProposal => .finishStalePriorProposal
  | .invalidNewGridBoundary => .finishInvalidNewGridBoundary
  | .noLiveAssignment => .finishNoLiveAssignment
  | .incompatibleFinishTime => .finishIncompatibleFinishTime

/-- The checked queue/score transition for all owned complement arms. -/
structure ServicedRegisters
    (r : CoordinatorLiveChoiceRecorderStep.Registers p eta)
    (q : OwnedRegisters r) where
  recording : CoordinatorRecordingOperation.Output p
  arrival : FastArm r.payload.slowSet → ℕ
  service : FastArm r.payload.slowSet → ℕ
  queue : FastArm r.payload.slowSet → ℕ
  score : FastArm r.payload.slowSet → ℕ
  previousService : FastArm r.payload.slowSet → ℕ
  arrivalDomain : ∀ j, arrival j ≤ D p
  serviceDomain : ∀ j, service j ≤ D p
  queueDomain : ∀ j, queue j ≤ p.T * D p
  scoreDomain : ∀ j, score j ≤ p.T * D p
  previousServiceDomain : ∀ j, previousService j ≤ D p
  arrival_eq : ∀ j, arrival j = complementArrival r.payload recording j
  service_eq : ∀ j, service j =
    CappedService.service (4 * r.payload.n) (q.queue j) (arrival j)
  queue_eq : ∀ j, queue j =
    CappedService.residual (4 * r.payload.n) (q.queue j) (arrival j)
  score_eq : ∀ j, score j = r.complementScores j + service j
  previousService_eq : ∀ j, previousService j = service j

/-- Check the two carried domains, form all actual recorder arrivals, and
serve every known complement queue with capacity `4 * payload.n`. This runs
after the one recorder call and before confirmation. -/
noncomputable def servicePass
    (r : CoordinatorLiveChoiceRecorderStep.Registers p eta)
    (q : OwnedRegisters r) (recording : CoordinatorRecordingOperation.Output p) :
    Except Failure (ServicedRegisters r q) := by
  classical
  exact if hqueue : q.queueDomainValid then
    if hprevious : q.previousServiceDomainValid then
      let arrival : FastArm r.payload.slowSet → ℕ :=
        fun j => complementArrival r.payload recording j
      if harrival : ∀ j, arrival j ≤ D p then
        let service : FastArm r.payload.slowSet → ℕ :=
          fun j => CappedService.service (4 * r.payload.n) (q.queue j) (arrival j)
        if hservice : ∀ j, service j ≤ D p then
          let score : FastArm r.payload.slowSet → ℕ :=
            fun j => r.complementScores j + service j
          if hscore : ∀ j, score j ≤ p.T * D p then
            let queue : FastArm r.payload.slowSet → ℕ :=
              fun j => CappedService.residual (4 * r.payload.n) (q.queue j) (arrival j)
            if hqueueOut : ∀ j, queue j ≤ p.T * D p then
              .ok
                { recording := recording
                  arrival := arrival
                  service := service
                  queue := queue
                  score := score
                  previousService := service
                  arrivalDomain := harrival
                  serviceDomain := hservice
                  queueDomain := hqueueOut
                  scoreDomain := hscore
                  previousServiceDomain := hservice
                  arrival_eq := fun _ => rfl
                  service_eq := fun _ => rfl
                  queue_eq := fun _ => rfl
                  score_eq := fun _ => rfl
                  previousService_eq := fun _ => rfl }
            else .error .queueOutputDomainFailure
          else .error .scoreOutputDomainFailure
        else .error .serviceOutputDomainFailure
      else .error .arrivalOutputDomainFailure
    else .error .previousServiceInputDomainFailure
  else .error .queueInputDomainFailure

/-- The full local service-contribution vector places actual capped service
on known complement queues and zero on arms outside the owned domain. -/
def gammaLoc (r : CoordinatorLiveChoiceRecorderStep.Registers p eta)
    {q : OwnedRegisters r}
    (serviced : ServicedRegisters r q) : Fin p.K → ℕ := fun arm =>
  if hslow : arm ∈ r.payload.slowSet.val then 0 else
    serviced.service ⟨arm, Finset.mem_sdiff.mpr ⟨Finset.mem_univ arm, hslow⟩⟩

theorem gammaLoc_zero_unowned
    (r : CoordinatorLiveChoiceRecorderStep.Registers p eta)
    {q : OwnedRegisters r}
    (serviced : ServicedRegisters r q) (arm : Fin p.K)
    (hslow : arm ∈ r.payload.slowSet.val) :
    gammaLoc r serviced arm = 0 := by
  simp [gammaLoc, hslow]

theorem gammaLoc_owned
    (r : CoordinatorLiveChoiceRecorderStep.Registers p eta)
    {q : OwnedRegisters r}
    (serviced : ServicedRegisters r q) (arm : Fin p.K)
    (hfast : arm ∉ r.payload.slowSet.val) :
    gammaLoc r serviced arm = serviced.service
      ⟨arm, Finset.mem_sdiff.mpr ⟨Finset.mem_univ arm, hfast⟩⟩ := by
  simp [gammaLoc, hfast]

theorem serviced_conservation
    (r : CoordinatorLiveChoiceRecorderStep.Registers p eta)
    (q : OwnedRegisters r) (serviced : ServicedRegisters r q)
    (j : FastArm r.payload.slowSet) :
    serviced.score j + serviced.queue j =
      r.complementScores j + q.queue j + serviced.arrival j := by
  rw [serviced.score_eq j, serviced.queue_eq j]
  calc
    r.complementScores j + serviced.service j +
        CappedService.residual (4 * r.payload.n) (q.queue j) (serviced.arrival j) =
      r.complementScores j +
        (CappedService.residual (4 * r.payload.n) (q.queue j)
            (serviced.arrival j) + serviced.service j) := by omega
    _ = r.complementScores j + (q.queue j + serviced.arrival j) := by
      rw [serviced.service_eq j]
      rw [CappedService.residual_add_service]
    _ = r.complementScores j + q.queue j + serviced.arrival j := by omega

theorem serviced_queueReplay_transition
    (r : CoordinatorLiveChoiceRecorderStep.Registers p eta)
    (q : OwnedRegisters r) (serviced : ServicedRegisters r q)
    (j : FastArm r.payload.slowSet) :
    QueueReplay.transition (4 * r.payload.n)
      (r.complementScores j, q.queue j) (true, serviced.arrival j) =
        (serviced.score j, serviced.queue j) := by
  simp [QueueReplay.transition, CappedService.service, CappedService.residual,
    serviced.service_eq, serviced.score_eq, serviced.queue_eq]

/-- Every successfully computed zero arrival still serves existing backlog
under the enabled live update. -/
theorem serviced_zeroArrival_drains
    (r : CoordinatorLiveChoiceRecorderStep.Registers p eta)
    (q : OwnedRegisters r) (serviced : ServicedRegisters r q)
    (j : FastArm r.payload.slowSet) (hzero : serviced.arrival j = 0) :
    serviced.service j = min (4 * r.payload.n) (q.queue j) ∧
      serviced.queue j = q.queue j - min (4 * r.payload.n) (q.queue j) := by
  rw [serviced.service_eq j, serviced.queue_eq j, hzero,
    CappedService.service, CappedService.residual]
  simp [CappedService.service]

theorem serviced_zeroArrival_service_pos
    (r : CoordinatorLiveChoiceRecorderStep.Registers p eta)
    (q : OwnedRegisters r) (serviced : ServicedRegisters r q)
    (j : FastArm r.payload.slowSet) (hzero : serviced.arrival j = 0)
    (hbacklog : 0 < q.queue j) :
    0 < serviced.service j := by
  have hcapacity : 0 < 4 * r.payload.n := by
    have hnreal : 0 < (r.payload.n : ℝ) := by
      rw [r.payload.n_eq_eta_mul_D]
      exact mul_pos eta.property (Nat.cast_pos.mpr (D_pos p))
    have hn : 0 < r.payload.n := by exact_mod_cast hnreal
    omega
  rw [(serviced_zeroArrival_drains r q serviced j hzero).1]
  exact QueueReplay.transition_zero_arrival_service_pos
    (capacity := 4 * r.payload.n) (_score := 0) (backlog := q.queue j)
    hcapacity hbacklog

/-- A successful recorder output with no gate on this complement arm gives
an actual zero arrival and therefore the preceding draining update. -/
theorem serviced_noGate_drains
    (r : CoordinatorLiveChoiceRecorderStep.Registers p eta)
    (q : OwnedRegisters r) (recording : CoordinatorRecordingOperation.Output p)
    (serviced : ServicedRegisters r q) (j : FastArm r.payload.slowSet)
    (hrecording : serviced.recording = recording)
    (hgate : recording.gateArm ≠ some j.1) :
    serviced.arrival j = 0 ∧
      serviced.service j = min (4 * r.payload.n) (q.queue j) ∧
      serviced.queue j = q.queue j - min (4 * r.payload.n) (q.queue j) := by
  have hzero : serviced.arrival j = 0 := by
    rw [serviced.arrival_eq, hrecording]
    simp [complementArrival, hgate]
  exact ⟨hzero, (serviced_zeroArrival_drains r q serviced j hzero).1,
    (serviced_zeroArrival_drains r q serviced j hzero).2⟩

/-- A finite code for every row-dependent output register. The continuous
row is not put into this carrier. An absent arm entry means the arm is outside
the coordinator's complement; it does not encode a queue or score. -/
structure ExactOutputCode
    (r : CoordinatorLiveChoiceRecorderStep.Registers p eta)
    (q : OwnedRegisters r) where
  ownArm : Fin p.K
  gateArm : Option (Fin p.K)
  rawArrival : Fin (D p + 1)
  pendingAfter : Finset (ActiveRoundActions.Follower p.m)
  arrival : Fin p.K → Option (Fin (D p + 1))
  service : Fin p.K → Option (Fin (D p + 1))
  queue : Fin p.K → Option (Fin (p.T * D p + 1))
  score : Fin p.K → Option (Fin (p.T * D p + 1))
  previousService : Fin p.K → Option (Fin (D p + 1))
  savedProposal : Option (Fin p.T × Bool)

noncomputable instance exactOutputCodeFintype
    (r : CoordinatorLiveChoiceRecorderStep.Registers p eta)
    (q : OwnedRegisters r) : Fintype (ExactOutputCode r q) := by
  classical
  let encode := fun c : ExactOutputCode r q =>
    (c.ownArm, (c.gateArm, (c.rawArrival, (c.pendingAfter,
      (c.arrival, (c.service, (c.queue, (c.score,
        (c.previousService, c.savedProposal)))))))))
  exact Fintype.ofInjective encode (by
    intro a b h
    cases a
    cases b
    simp_all [encode])

local instance exactOutputCodeMeasurableSpace
    (r : CoordinatorLiveChoiceRecorderStep.Registers p eta) (q : OwnedRegisters r) :
    MeasurableSpace (ExactOutputCode r q) := ⊤

local instance checkedCodeMeasurableSpace
    (r : CoordinatorLiveChoiceRecorderStep.Registers p eta) (q : OwnedRegisters r) :
    MeasurableSpace (Except Failure (ExactOutputCode r q)) := ⊤

/-- Convert a checked natural register into its exact finite coordinate. -/
def codeNat (bound value : ℕ) (h : value ≤ bound) : Fin (bound + 1) :=
  ⟨value, Nat.lt_succ_of_le h⟩

/-- Encode one checked service pass with exact arrival, service, score, queue,
and last-service equations. -/
def codeOfServiced
    (r : CoordinatorLiveChoiceRecorderStep.Registers p eta)
    (q : OwnedRegisters r) (ownArm : Fin p.K)
    (recording : CoordinatorRecordingOperation.Output p)
    (pendingAfter : Finset (ActiveRoundActions.Follower p.m))
    (savedProposal : Option (Fin p.T × Bool))
    (serviced : ServicedRegisters r q) : ExactOutputCode r q :=
  { ownArm := ownArm
    gateArm := recording.gateArm
    rawArrival := codeNat (D p) recording.rawArrival recording.rawArrival_le_D
    pendingAfter := pendingAfter
    arrival := fun arm => if h : arm ∈ r.payload.slowSet.val then none else
      some (codeNat (D p) (serviced.arrival
        ⟨arm, Finset.mem_sdiff.mpr ⟨Finset.mem_univ arm, h⟩⟩)
        (serviced.arrivalDomain ⟨arm,
          Finset.mem_sdiff.mpr ⟨Finset.mem_univ arm, h⟩⟩))
    service := fun arm => if h : arm ∈ r.payload.slowSet.val then none else
      some (codeNat (D p) (serviced.service
        ⟨arm, Finset.mem_sdiff.mpr ⟨Finset.mem_univ arm, h⟩⟩)
        (serviced.serviceDomain ⟨arm,
          Finset.mem_sdiff.mpr ⟨Finset.mem_univ arm, h⟩⟩))
    queue := fun arm => if h : arm ∈ r.payload.slowSet.val then none else
      some (codeNat (p.T * D p) (serviced.queue
        ⟨arm, Finset.mem_sdiff.mpr ⟨Finset.mem_univ arm, h⟩⟩)
        (serviced.queueDomain ⟨arm,
          Finset.mem_sdiff.mpr ⟨Finset.mem_univ arm, h⟩⟩))
    score := fun arm => if h : arm ∈ r.payload.slowSet.val then none else
      some (codeNat (p.T * D p) (serviced.score
        ⟨arm, Finset.mem_sdiff.mpr ⟨Finset.mem_univ arm, h⟩⟩)
        (serviced.scoreDomain ⟨arm,
          Finset.mem_sdiff.mpr ⟨Finset.mem_univ arm, h⟩⟩))
    previousService := fun arm =>
      if h : arm ∈ r.payload.slowSet.val then none else
        some (codeNat (D p) (serviced.previousService
          ⟨arm, Finset.mem_sdiff.mpr ⟨Finset.mem_univ arm, h⟩⟩)
          (serviced.previousServiceDomain ⟨arm,
            Finset.mem_sdiff.mpr ⟨Finset.mem_univ arm, h⟩⟩))
    savedProposal := savedProposal }

theorem codeOfServiced_ownedEntries
    (r : CoordinatorLiveChoiceRecorderStep.Registers p eta)
    (q : OwnedRegisters r) (ownArm : Fin p.K)
    (recording : CoordinatorRecordingOperation.Output p)
    (pendingAfter : Finset (ActiveRoundActions.Follower p.m))
    (savedProposal : Option (Fin p.T × Bool))
    (serviced : ServicedRegisters r q) (j : FastArm r.payload.slowSet) :
    (codeOfServiced r q ownArm recording pendingAfter savedProposal serviced).arrival j.1 =
        some (codeNat (D p) (serviced.arrival j) (serviced.arrivalDomain j)) ∧
    (codeOfServiced r q ownArm recording pendingAfter savedProposal serviced).service j.1 =
        some (codeNat (D p) (serviced.service j) (serviced.serviceDomain j)) ∧
    (codeOfServiced r q ownArm recording pendingAfter savedProposal serviced).queue j.1 =
        some (codeNat (p.T * D p) (serviced.queue j) (serviced.queueDomain j)) ∧
    (codeOfServiced r q ownArm recording pendingAfter savedProposal serviced).score j.1 =
        some (codeNat (p.T * D p) (serviced.score j) (serviced.scoreDomain j)) ∧
    (codeOfServiced r q ownArm recording pendingAfter savedProposal serviced).previousService j.1 =
        some (codeNat (D p) (serviced.previousService j)
          (serviced.previousServiceDomain j)) := by
  have hnot : j.1 ∉ r.payload.slowSet.val := (Finset.mem_sdiff.mp j.2).2
  simp [codeOfServiced, hnot]

@[simp] theorem codeNat_val (bound value : ℕ) (h : value ≤ bound) :
    (codeNat bound value h).val = value := rfl

/-- Run the source order on one actual row and own observation: prepare,
recorder once, service and update every complement register, confirmation,
then the actual phase-clock finish. -/
noncomputable def run
    (r : CoordinatorLiveChoiceRecorderStep.Registers p eta)
    (q : OwnedRegisters r) (row : CompleteRow p)
    (observation : Fin (D p + 1)) : Except Failure (ExactOutputCode r q) := by
  classical
  exact match CoordinatorLiveChoiceRecorderStep.prepare r row with
  | .error failure => .error (prepareFailureCode failure)
  | .ok continuation =>
      match CoordinatorRecorderComplementBridge.run
          (CoordinatorLiveChoiceRecorderStep.recorderInput continuation observation) with
      | none => .error .recorderRejected
      | some recording =>
          match servicePass r q recording with
          | .error failure => .error failure
          | .ok serviced =>
              match CoordinatorLocalArmChoice.confirmationUpdate r.payload
                  r.pendingAtChoice continuation.sourceCutoff r.time row observation with
              | none => .error .confirmationRejected
              | some pendingAfter =>
                  match CoordinatorPhaseClock.finishRound p eta.val r.time
                      continuation.startRoundResult.clock pendingAfter row with
                  | .error failure => .error (finishFailureCode failure)
                  | .ok finishResult =>
                      .ok (codeOfServiced r q continuation.ownArm recording
                        pendingAfter finishResult.clock.lastProposal serviced)

/-- Decode a finite output code while retaining the original continuous row
and actual prepared continuation outside the code. -/
structure ReconstructedOutput
    (r : CoordinatorLiveChoiceRecorderStep.Registers p eta)
    (row : CompleteRow p) where
  choice : CoordinatorLiveChoiceRecorderStep.Output p eta
  arrival : FastArm r.payload.slowSet → Option (Fin (D p + 1))
  service : FastArm r.payload.slowSet → Option (Fin (D p + 1))
  queue : FastArm r.payload.slowSet → Option (Fin (p.T * D p + 1))
  score : FastArm r.payload.slowSet → Option (Fin (p.T * D p + 1))
  previousService : FastArm r.payload.slowSet → Option (Fin (D p + 1))
  savedProposal : Option (Fin p.T × Bool)

/-- Exact reconstruction of the local choice and register output from the
original row, prepared continuation, and finite code. -/
def reconstructOutput
    {r : CoordinatorLiveChoiceRecorderStep.Registers p eta}
    {q : OwnedRegisters r} {row : CompleteRow p}
    (continuation : CoordinatorLiveChoiceRecorderStep.Continuation r row)
    (code : ExactOutputCode r q) : ReconstructedOutput r row :=
  { choice :=
      { priorClock := r.priorClock
        startRoundResult := continuation.startRoundResult
        payload := r.payload
        time := r.time
        pendingBefore := r.pendingAtChoice
        pendingAfter := code.pendingAfter
        ownArm := code.ownArm
        recorderOutput :=
          { gateArm := code.gateArm
            rawArrival := code.rawArrival.val
            rawArrival_le_D := Nat.le_of_lt_succ code.rawArrival.isLt } }
    arrival := fun j => code.arrival j.1
    service := fun j => code.service j.1
    queue := fun j => code.queue j.1
    score := fun j => code.score j.1
    previousService := fun j => code.previousService j.1
    savedProposal := code.savedProposal }

/-- Re-encoding a decoded code preserves every finite output coordinate. -/
theorem code_reconstructOutput
    {r : CoordinatorLiveChoiceRecorderStep.Registers p eta}
    {q : OwnedRegisters r} {row : CompleteRow p}
    (c : CoordinatorLiveChoiceRecorderStep.Continuation r row)
    (code : ExactOutputCode r q) :
    let decoded := reconstructOutput c code
    decoded.choice.ownArm = code.ownArm ∧
    decoded.choice.recorderOutput.gateArm = code.gateArm ∧
    decoded.choice.recorderOutput.rawArrival = code.rawArrival.val ∧
    decoded.choice.pendingAfter = code.pendingAfter ∧
    (∀ j, decoded.arrival j = code.arrival j.1) ∧
    (∀ j, decoded.service j = code.service j.1) ∧
    (∀ j, decoded.queue j = code.queue j.1) ∧
    (∀ j, decoded.score j = code.score j.1) ∧
    decoded.savedProposal = code.savedProposal := by
  simp [reconstructOutput]

/-- A successful code uses the same prepared continuation and retains all
payload data, including its assignment, anchor, and rates. -/
theorem reconstructedChoiceFrame
    {r : CoordinatorLiveChoiceRecorderStep.Registers p eta}
    {q : OwnedRegisters r} {row : CompleteRow p}
    (c : CoordinatorLiveChoiceRecorderStep.Continuation r row)
    (code : ExactOutputCode r q) :
    let decoded := reconstructOutput c code
    decoded.choice.payload = r.payload ∧
    decoded.choice.startRoundResult.assignmentStart =
      c.startRoundResult.assignmentStart ∧
    decoded.choice.payload.anchor = r.payload.anchor ∧
    (∀ arm, decoded.choice.payload.rate arm = r.payload.rate arm) ∧
    decoded.choice.time = r.time ∧
    decoded.choice.pendingBefore = r.pendingAtChoice := by
  simp [reconstructOutput]

/-- The phase-clock register checks and enabled time guard are derived from
the exact successful StartRound used by prepare. -/
theorem startRound_success_domains
    {r : CoordinatorLiveChoiceRecorderStep.Registers p eta}
    {result : CoordinatorPhaseClock.StartRoundResult p}
    (h : CoordinatorPhaseClock.startRound p eta.val r.time
      r.priorClock r.clockPending = .ok result) :
    CoordinatorPhaseClock.proposalParameterValid p eta.val ∧
      CoordinatorPhaseClock.clockRegistersValid p eta.val r.priorClock ∧
      CoordinatorPhaseClock.startRoundTimeValid p r.time r.priorClock := by
  unfold CoordinatorPhaseClock.startRound at h
  by_cases hp : CoordinatorPhaseClock.proposalParameterValid p eta.val
  · simp only [if_pos hp] at h
    by_cases hc : CoordinatorPhaseClock.clockRegistersValid p eta.val r.priorClock
    · simp only [dif_pos hc] at h
      by_cases ht : CoordinatorPhaseClock.startRoundTimeValid p r.time r.priorClock
      · exact ⟨hp, hc, ht⟩
      · simp only [dif_neg ht] at h
        cases h
    · simp only [dif_neg hc] at h
      cases h
  · simp only [if_neg hp] at h
    cases h

/-- A prepared source-live branch cannot carry a collection cutoff: the
start clock's at-or-after-cutoff guard conflicts with prepare's strict-live
guard. -/
theorem live_preparation_has_no_cutoff
    {r : CoordinatorLiveChoiceRecorderStep.Registers p eta}
    (domain : CoordinatorLiveChoiceRecorderStep.PreparationDomain r)
    (hdomains : CoordinatorPhaseClock.proposalParameterValid p eta.val ∧
      CoordinatorPhaseClock.clockRegistersValid p eta.val r.priorClock ∧
      CoordinatorPhaseClock.startRoundTimeValid p r.time r.priorClock) :
    r.priorClock.u = none := by
  cases hu : r.priorClock.u with
  | none => rfl
  | some u =>
      have htime : u.val ≤ r.time.val := by
        have ht := hdomains.2.2
        simp only [CoordinatorPhaseClock.startRoundTimeValid,
          domain.payloadClockStart, hu] at ht
        exact ht.2
      have hbefore : r.time.val < u.val := by
        have hlt := domain.assignmentLive.2
        simpa [CoordinatorLocalArmChoice.assignmentIsLive,
          CoordinatorLocalArmChoice.sourceRound,
          CoordinatorLocalArmChoice.cutoffRound,
          CoordinatorLiveChoiceRecorderStep.cutoffFromClock, hu] using hlt
      omega

/-- The accepted `FinishRound` time guard follows from the same prepared
assignment start and live `StartRound` time check. -/
theorem live_finish_time_valid
    {r : CoordinatorLiveChoiceRecorderStep.Registers p eta}
    (domain : CoordinatorLiveChoiceRecorderStep.PreparationDomain r)
    (hdomains : CoordinatorPhaseClock.proposalParameterValid p eta.val ∧
      CoordinatorPhaseClock.clockRegistersValid p eta.val r.priorClock ∧
      CoordinatorPhaseClock.startRoundTimeValid p r.time r.priorClock)
    (hu : r.priorClock.u = none) :
    CoordinatorPhaseClock.finishRoundTimeValid r.time r.priorClock := by
  have ht := hdomains.2.2
  have ht' : r.payload.sigma.val < r.time.val ∧
      FollowerCutoffScan.calendarRound r.time ≤ r.priorClock.g := by
    simpa [CoordinatorPhaseClock.startRoundTimeValid,
      domain.payloadClockStart, hu] using ht
  have hstarted := domain.choiceInputsValid.time.assignment_started
  have hround : r.payload.sigma.val ≤ r.time.val := by
    simp only [CoordinatorLocalArmChoice.assignmentStart,
      CoordinatorLocalArmChoice.sourceRound] at hstarted
    omega
  simp [CoordinatorPhaseClock.finishRoundTimeValid,
    domain.payloadClockStart, hu, hround, ht'.2]

/-- The saved proposal overwrites only the last-proposal register at the
current original coordinate. -/
noncomputable def savedProposalClock (eta : LearningRate)
    (clock : CoordinatorPhaseClock.ClockRegisters p)
    (t : Fin p.T) (row : CompleteRow p) : CoordinatorPhaseClock.ClockRegisters p := by
  let proposal : Option (Fin p.T × Bool) :=
    Option.some (t, FollowerCutoffScan.completeRowProposalBit p eta.val row t)
  exact { clock with lastProposal := proposal }

/-- The actual final clock operation succeeds on the pending set produced by
confirmation, and saves the current row's proposal coordinate and bit. -/
theorem finishRound_live_success
    {r : CoordinatorLiveChoiceRecorderStep.Registers p eta}
    {row : CompleteRow p}
    (domain : CoordinatorLiveChoiceRecorderStep.PreparationDomain r)
    (c : CoordinatorLiveChoiceRecorderStep.Continuation r row)
    (hprepare : CoordinatorLiveChoiceRecorderStep.prepare r row = .ok c)
    (pending : Finset (Fin (p.m - 1))) :
    ∃ result,
      CoordinatorPhaseClock.finishRound p eta.val r.time
        c.startRoundResult.clock pending row = .ok result ∧
      result.clock = savedProposalClock eta r.priorClock r.time row ∧
      result.pending = pending ∧ result.ledgerCommand = none := by
  have _hstage :=
    CoordinatorLiveChoiceRecorderStep.prepare_success_stage domain hprepare
  have hdomains := startRound_success_domains domain.startRound_eq
  have hu := live_preparation_has_no_cutoff domain hdomains
  have htime := live_finish_time_valid domain hdomains hu
  have hsigma : r.priorClock.sigma ≠ none := by
    rw [domain.payloadClockStart]
    exact Option.some_ne_none r.payload.sigma
  obtain ⟨result, hfinish, hclock, hpending, hledger⟩ :=
    CoordinatorPhaseClock.finishRound_live_savedProposal p eta.val r.time
      r.priorClock pending row hdomains.2.1 htime hsigma hu hdomains.1
  refine ⟨result, ?_, ?_, hpending, hledger⟩
  · simpa [c.clockFrame.1] using hfinish
  · simpa [savedProposalClock, c.clockFrame.1] using hclock

/-- The code's proposal field is the actual value written by the successful
phase-clock finish, at the original round coordinate. -/
theorem savedProposal_exact
    {r : CoordinatorLiveChoiceRecorderStep.Registers p eta}
    {q : OwnedRegisters r} {row : CompleteRow p} {observation : Fin (D p + 1)}
    {code : ExactOutputCode r q} (h : run r q row observation = .ok code)
    (domain : CoordinatorLiveChoiceRecorderStep.PreparationDomain r) :
    code.savedProposal = some
      (r.time, FollowerCutoffScan.completeRowProposalBit p eta.val row r.time) := by
  classical
  rcases CoordinatorLiveChoiceRecorderStep.prepare_success_of_domain domain row with
    ⟨c, hc, _⟩
  cases hrecording : CoordinatorRecorderComplementBridge.run
      (CoordinatorLiveChoiceRecorderStep.recorderInput c observation) with
  | none => simp [run, hc, hrecording] at h
  | some recording =>
      cases hservice : servicePass r q recording with
      | error failure => simp [run, hc, hrecording, hservice] at h
      | ok serviced =>
          cases hconfirmation : CoordinatorLocalArmChoice.confirmationUpdate
              r.payload r.pendingAtChoice c.sourceCutoff r.time row observation with
          | none => simp [run, hc, hrecording, hservice, hconfirmation] at h
          | some pendingAfter =>
              obtain ⟨finishResult, hfinish, hclock, _, _⟩ :=
                finishRound_live_success domain c hc pendingAfter
              have hcode : codeOfServiced r q c.ownArm recording pendingAfter
                  finishResult.clock.lastProposal serviced = code := by
                simpa [run, hc, hrecording, hservice, hconfirmation, hfinish]
                  using h
              rw [← hcode, hclock]
              simp [savedProposalClock, codeOfServiced]

/-- A successful live completion factors through the actual prepared
continuation, exactly one accepted recorder result, a complete complement
service pass, and confirmation from the pre-choice pending state. -/
theorem run_success_decomposition
    {r : CoordinatorLiveChoiceRecorderStep.Registers p eta}
    {q : OwnedRegisters r} {row : CompleteRow p}
    {observation : Fin (D p + 1)} {code : ExactOutputCode r q}
    (domain : CoordinatorLiveChoiceRecorderStep.PreparationDomain r)
    (h : run r q row observation = .ok code) :
    ∃ c recording serviced pendingAfter,
      CoordinatorLiveChoiceRecorderStep.prepare r row = .ok c ∧
      CoordinatorRecorderComplementBridge.run
        (CoordinatorLiveChoiceRecorderStep.recorderInput c observation) = some recording ∧
      servicePass r q recording = .ok serviced ∧
      CoordinatorLocalArmChoice.confirmationUpdate r.payload r.pendingAtChoice
        c.sourceCutoff r.time row observation = some pendingAfter ∧
      codeOfServiced r q c.ownArm recording pendingAfter
        (some (r.time, FollowerCutoffScan.completeRowProposalBit
          p eta.val row r.time)) serviced = code ∧
      (∀ arm, arm ∈ r.payload.slowSet.val → gammaLoc r serviced arm = 0) := by
  classical
  rcases CoordinatorLiveChoiceRecorderStep.prepare_success_of_domain domain row with
    ⟨c, hc, _⟩
  cases hrecording : CoordinatorRecorderComplementBridge.run
      (CoordinatorLiveChoiceRecorderStep.recorderInput c observation) with
  | none => simp [run, hc, hrecording] at h
  | some recording =>
      cases hservice : servicePass r q recording with
      | error failure => simp [run, hc, hrecording, hservice] at h
      | ok serviced =>
          cases hconfirmation : CoordinatorLocalArmChoice.confirmationUpdate
              r.payload r.pendingAtChoice c.sourceCutoff r.time row observation with
          | none => simp [run, hc, hrecording, hservice, hconfirmation] at h
          | some pendingAfter =>
              obtain ⟨finishResult, hfinish, hclock, _, _⟩ :=
                finishRound_live_success domain c hc pendingAfter
              have hcode : codeOfServiced r q c.ownArm recording pendingAfter
                  finishResult.clock.lastProposal serviced = code := by
                simpa [run, hc, hrecording, hservice, hconfirmation, hfinish]
                  using h
              have hclockProposal : finishResult.clock.lastProposal = some
                  (r.time, FollowerCutoffScan.completeRowProposalBit
                    p eta.val row r.time) := by
                rw [hclock]
                simp [savedProposalClock]
              rw [hclockProposal] at hcode
              refine ⟨c, recording, serviced, pendingAfter, hc, hrecording,
                hservice, hconfirmation, hcode, ?_⟩
              · intro arm hslow
                exact gammaLoc_zero_unowned r serviced arm hslow

/-- Every successful output coordinate is the exact checked service result;
the option map is present precisely on coordinator-owned complement arms. -/
theorem run_success_equations
    {r : CoordinatorLiveChoiceRecorderStep.Registers p eta}
    {q : OwnedRegisters r} {row : CompleteRow p}
    {observation : Fin (D p + 1)} {code : ExactOutputCode r q}
    (domain : CoordinatorLiveChoiceRecorderStep.PreparationDomain r)
    (h : run r q row observation = .ok code) :
    ∃ c recording serviced pendingAfter,
      CoordinatorLiveChoiceRecorderStep.prepare r row = .ok c ∧
      CoordinatorRecorderComplementBridge.run
        (CoordinatorLiveChoiceRecorderStep.recorderInput c observation) = some recording ∧
      servicePass r q recording = .ok serviced ∧
      CoordinatorLocalArmChoice.confirmationUpdate r.payload r.pendingAtChoice
        c.sourceCutoff r.time row observation = some pendingAfter ∧
      c.ownArm = code.ownArm ∧
      recording.gateArm = code.gateArm ∧
      recording.rawArrival = code.rawArrival.val ∧
      pendingAfter = code.pendingAfter ∧
      (∀ j : FastArm r.payload.slowSet,
        code.arrival j.1 = some
          (codeNat (D p) (serviced.arrival j) (serviced.arrivalDomain j))) ∧
      (∀ j : FastArm r.payload.slowSet,
        code.service j.1 = some
          (codeNat (D p) (serviced.service j) (serviced.serviceDomain j))) ∧
      (∀ j : FastArm r.payload.slowSet,
        code.queue j.1 = some
          (codeNat (p.T * D p) (serviced.queue j) (serviced.queueDomain j))) ∧
      (∀ j : FastArm r.payload.slowSet,
        code.score j.1 = some
          (codeNat (p.T * D p) (serviced.score j) (serviced.scoreDomain j))) ∧
      (∀ j : FastArm r.payload.slowSet,
        code.previousService j.1 = some
          (codeNat (D p) (serviced.previousService j)
            (serviced.previousServiceDomain j))) ∧
      code.savedProposal = some
        (r.time, FollowerCutoffScan.completeRowProposalBit p eta.val row r.time) := by
  rcases run_success_decomposition domain h with
    ⟨c, recording, serviced, pendingAfter, hc, hrecording, hservice, hconfirmation,
      hcode, _⟩
  have hproposal := savedProposal_exact h domain
  have hown : c.ownArm = code.ownArm := by
    simpa [codeOfServiced] using
      congrArg (fun x : ExactOutputCode r q => x.ownArm) hcode
  have hgate : recording.gateArm = code.gateArm := by
    simpa [codeOfServiced] using
      congrArg (fun x : ExactOutputCode r q => x.gateArm) hcode
  have hraw : recording.rawArrival = code.rawArrival.val := by
    simpa [codeOfServiced, codeNat] using
      congrArg (fun x : ExactOutputCode r q => x.rawArrival.val) hcode
  have hpending : pendingAfter = code.pendingAfter := by
    simpa [codeOfServiced] using
      congrArg (fun x : ExactOutputCode r q => x.pendingAfter) hcode
  refine ⟨c, recording, serviced, pendingAfter, hc, hrecording, hservice, hconfirmation,
    hown, hgate, hraw, hpending, ?_, ?_, ?_, ?_, ?_, hproposal⟩
  · intro j
    rw [← hcode]
    exact (codeOfServiced_ownedEntries r q c.ownArm recording
      pendingAfter (some (r.time,
        FollowerCutoffScan.completeRowProposalBit p eta.val row r.time))
      serviced j).1
  · intro j
    rw [← hcode]
    exact (codeOfServiced_ownedEntries r q c.ownArm recording
      pendingAfter (some (r.time,
        FollowerCutoffScan.completeRowProposalBit p eta.val row r.time))
      serviced j).2.1
  · intro j
    rw [← hcode]
    exact (codeOfServiced_ownedEntries r q c.ownArm recording
      pendingAfter (some (r.time,
        FollowerCutoffScan.completeRowProposalBit p eta.val row r.time))
      serviced j).2.2.1
  · intro j
    rw [← hcode]
    exact (codeOfServiced_ownedEntries r q c.ownArm recording
      pendingAfter (some (r.time,
        FollowerCutoffScan.completeRowProposalBit p eta.val row r.time))
      serviced j).2.2.2.1
  · intro j
    rw [← hcode]
    exact (codeOfServiced_ownedEntries r q c.ownArm recording
      pendingAfter (some (r.time,
        FollowerCutoffScan.completeRowProposalBit p eta.val row r.time))
      serviced j).2.2.2.2

/-- The accepted choice's successful recorder and confirmation projections
agree exactly with those consumed by the service composition. The accepted
choice finish is used only in this equality theorem, after the composed
operation has already respected service-before-confirmation-before-clock. -/
theorem successfulAcceptedProjections
    {r : CoordinatorLiveChoiceRecorderStep.Registers p eta}
    {q : OwnedRegisters r} {row : CompleteRow p}
    {observation : Fin (D p + 1)} {code : ExactOutputCode r q}
    (domain : CoordinatorLiveChoiceRecorderStep.PreparationDomain r)
    (h : run r q row observation = .ok code) :
    ∃ c out,
      CoordinatorLiveChoiceRecorderStep.prepare r row = .ok c ∧
      CoordinatorLiveChoiceRecorderStep.finish c observation = .ok out ∧
      CoordinatorRecorderComplementBridge.run
        (CoordinatorLiveChoiceRecorderStep.recorderInput c observation) =
          some out.recorderOutput ∧
      CoordinatorLocalArmChoice.confirmationUpdate r.payload r.pendingAtChoice
        c.sourceCutoff r.time row observation = some out.pendingAfter ∧
      out.ownArm = code.ownArm ∧
      out.recorderOutput.gateArm = code.gateArm ∧
      out.recorderOutput.rawArrival = code.rawArrival.val ∧
      out.pendingAfter = code.pendingAfter ∧
      out.payload = r.payload ∧ out.startRoundResult = c.startRoundResult ∧
      out.startRoundResult.assignmentStart = c.startRoundResult.assignmentStart ∧
      out.payload.anchor = r.payload.anchor ∧
      (∀ arm, out.payload.rate arm = r.payload.rate arm) ∧
      out.time = r.time ∧ out.pendingBefore = r.pendingAtChoice := by
  rcases run_success_equations domain h with
    ⟨c, recording, serviced, pendingAfter, hc, hrecording, hservice, hconfirmation,
      hown, hgate, hraw, hpending, _, _, _, _, _, _⟩
  let out : CoordinatorLiveChoiceRecorderStep.Output p eta :=
    { priorClock := r.priorClock
      startRoundResult := c.startRoundResult
      payload := r.payload
      time := r.time
      pendingBefore := r.pendingAtChoice
      pendingAfter := pendingAfter
      ownArm := c.ownArm
      recorderOutput := recording }
  have hfinish : CoordinatorLiveChoiceRecorderStep.finish c observation = .ok out := by
    simp [CoordinatorLiveChoiceRecorderStep.finish, hrecording, hconfirmation, out]
  have hprojections := CoordinatorLiveChoiceRecorderStep.finish_success_equations hfinish
  refine ⟨c, out, hc, hfinish, hprojections.1, hprojections.2,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [out] using hown
  · simpa [out] using hgate
  · simpa [out] using hraw
  · simpa [out] using hpending
  · rfl
  · rfl
  · rfl
  · rfl
  · intro arm
    rfl
  · rfl
  · rfl

/-- The successful proposal read remains a live finish with the same
confirmation-produced pending set and no ledger interruption command. -/
theorem successfulFinishNoInterrupt
    {r : CoordinatorLiveChoiceRecorderStep.Registers p eta}
    {q : OwnedRegisters r} {row : CompleteRow p}
    {observation : Fin (D p + 1)} {code : ExactOutputCode r q}
    (domain : CoordinatorLiveChoiceRecorderStep.PreparationDomain r)
    (h : run r q row observation = .ok code) :
    ∃ c pending finishResult,
      CoordinatorLiveChoiceRecorderStep.prepare r row = .ok c ∧
      CoordinatorLocalArmChoice.confirmationUpdate r.payload r.pendingAtChoice
        c.sourceCutoff r.time row observation = some pending ∧
      pending = code.pendingAfter ∧
      CoordinatorPhaseClock.finishRound p eta.val r.time
        c.startRoundResult.clock pending row = .ok finishResult ∧
      finishResult.clock = savedProposalClock eta r.priorClock r.time row ∧
      finishResult.clock.lastProposal = some
        (r.time, FollowerCutoffScan.completeRowProposalBit p eta.val row r.time) ∧
      finishResult.pending = pending ∧ finishResult.ledgerCommand = none := by
  rcases run_success_decomposition domain h with
    ⟨c, recording, serviced, pendingAfter, hc, _, _, hconfirmation, hcode, _⟩
  have hpending : pendingAfter = code.pendingAfter := by
    simpa [codeOfServiced] using
      (congrArg (fun x : ExactOutputCode r q => x.pendingAfter) hcode)
  obtain ⟨finishResult, hfinish, hclock, hframe, hledger⟩ :=
    finishRound_live_success domain c hc pendingAfter
  refine ⟨c, pendingAfter, finishResult, hc, hconfirmation, hpending,
    hfinish, hclock, ?_, hframe, hledger⟩
  rw [hclock]
  simp [savedProposalClock]

/-- For fixed incoming registers, the accepted recorder and confirmation
projections are jointly measurable in the complete row and typed own
observation. -/
theorem measurable_liveRecorderAt
    (r : CoordinatorLiveChoiceRecorderStep.Registers p eta) :
    Measurable (fun value : CompleteRow p × Fin (D p + 1) =>
      CoordinatorLiveChoiceRecorderStep.flowRecorderAt r value) := by
  have harm : Measurable (CoordinatorLiveChoiceRecorderStep.flowArmAt r) := by
    have hchoice := CoordinatorLocalArmChoice.measurable_coordinatorArmChoice
      r.payload r.pendingAtChoice
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p r.priorClock.u)
      r.time r.complementWeights
    have hget : Measurable (fun x : Option (Fin p.K) => x.getD ⟨0, K_pos p⟩) :=
      measurable_of_finite _
    change Measurable (fun row : CompleteRow p =>
      (CoordinatorLocalArmChoice.coordinatorArmChoice r.payload r.pendingAtChoice
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p r.priorClock.u)
        r.time r.complementWeights row).getD ⟨0, K_pos p⟩)
    exact hget.comp hchoice
  have hinput : Measurable (fun value : CompleteRow p × Fin (D p + 1) =>
      (value.1, (CoordinatorLiveChoiceRecorderStep.flowArmAt r value.1, value.2))) := by
    exact measurable_fst.prodMk
      ((harm.comp measurable_fst).prodMk measurable_snd)
  exact (CoordinatorRecordingMeasurability.measurable_run
    (CoordinatorLiveChoiceRecorderStep.flowRecorderBase r)).comp hinput

/-- Fixed-register output codes are jointly measurable in the complete row
and the coordinator's own typed observation. The proof factors through the
accepted recorder, choice, confirmation, and proposal measurability APIs. -/
theorem measurable_outputCode
    (r : CoordinatorLiveChoiceRecorderStep.Registers p eta)
    (q : OwnedRegisters r)
    (domain : CoordinatorLiveChoiceRecorderStep.PreparationDomain r) :
    Measurable (fun value : CompleteRow p × Fin (D p + 1) =>
      run r q value.1 value.2) := by
  classical
  let factor : Option (CoordinatorRecordingOperation.Output p) ×
      (Option (Finset (ActiveRoundActions.Follower p.m)) ×
        (Fin p.K × Bool)) → Except Failure (ExactOutputCode r q) := by
    intro data
    exact match data.1 with
    | none => .error .recorderRejected
    | some recording =>
        match servicePass r q recording with
        | .error failure => .error failure
        | .ok serviced =>
            match data.2.1 with
            | none => .error .confirmationRejected
            | some pendingAfter =>
                .ok (codeOfServiced r q data.2.2.1 recording pendingAfter
                  (some (r.time, data.2.2.2)) serviced)
  have hfactor : Measurable factor := measurable_of_finite _
  have hrecorder := measurable_liveRecorderAt r
  have hconfirmation :=
    CoordinatorLiveChoiceRecorderStep.measurable_flowConfirmationAt r
  have hproposal : Measurable (fun value : CompleteRow p × Fin (D p + 1) =>
      completeRowProposalBit p eta.val value.1 r.time) :=
    (FollowerDownMeasurability.measurable_completeRowProposalBit
      p eta.val r.time).comp measurable_fst
  have hchoice : Measurable (fun value : CompleteRow p × Fin (D p + 1) =>
      CoordinatorLiveChoiceRecorderStep.flowArmAt r value.1) := by
    have h := CoordinatorLocalArmChoice.measurable_coordinatorArmChoice
      r.payload r.pendingAtChoice
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p r.priorClock.u)
      r.time r.complementWeights
    have hget : Measurable (fun x : Option (Fin p.K) => x.getD ⟨0, K_pos p⟩) :=
      measurable_of_finite _
    change Measurable (fun value : CompleteRow p × Fin (D p + 1) =>
      (CoordinatorLocalArmChoice.coordinatorArmChoice r.payload
        r.pendingAtChoice
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p r.priorClock.u)
        r.time r.complementWeights value.1).getD ⟨0, K_pos p⟩)
    exact (hget.comp h).comp measurable_fst
  have htuple : Measurable (fun value : CompleteRow p × Fin (D p + 1) =>
      (CoordinatorLiveChoiceRecorderStep.flowRecorderAt r value,
        (CoordinatorLiveChoiceRecorderStep.flowConfirmationAt r value,
          (CoordinatorLiveChoiceRecorderStep.flowArmAt r value.1,
            completeRowProposalBit p eta.val value.1 r.time)))) :=
    hrecorder.prodMk (hconfirmation.prodMk (hchoice.prodMk hproposal))
  have heq : (fun value : CompleteRow p × Fin (D p + 1) =>
      run r q value.1 value.2) = fun value =>
        factor (CoordinatorLiveChoiceRecorderStep.flowRecorderAt r value,
          (CoordinatorLiveChoiceRecorderStep.flowConfirmationAt r value,
            (CoordinatorLiveChoiceRecorderStep.flowArmAt r value.1,
              completeRowProposalBit p eta.val value.1 r.time))) := by
    funext value
    rcases CoordinatorLiveChoiceRecorderStep.prepare_success_of_domain domain
        value.1 with ⟨c, hprepare, _⟩
    have harm : c.ownArm =
        CoordinatorLiveChoiceRecorderStep.flowArmAt r value.1 := by
      change c.ownArm =
        (CoordinatorLocalArmChoice.coordinatorArmChoice r.payload
          r.pendingAtChoice
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p r.priorClock.u)
          r.time r.complementWeights value.1).getD ⟨0, K_pos p⟩
      rw [c.armChoice_eq]
      rfl
    have hrecord : CoordinatorRecorderComplementBridge.run
        (CoordinatorLiveChoiceRecorderStep.recorderInput c value.2) =
        CoordinatorLiveChoiceRecorderStep.flowRecorderAt r value := by
      -- The recorder's extended weights are fixed by the same complement
      -- scores; `inputAt` changes only this row, arm, and observation.
      have hweights :
          CoordinatorRecorderComplementBridge.extendedCurrentWeights
            (CoordinatorLiveChoiceRecorderStep.flowRecorderInput r value.1
              (CoordinatorLiveChoiceRecorderStep.flowArmAt r value.1) value.2) =
          CoordinatorRecorderComplementBridge.extendedCurrentWeights
            (CoordinatorLiveChoiceRecorderStep.flowRecorderInput r
              (CoordinatorLiveChoiceRecorderStep.dummyCompleteRow p)
              ⟨0, K_pos p⟩ (CoordinatorLiveChoiceRecorderStep.zeroObservation p)) := by
        funext arm
        by_cases hslow : arm ∈ r.payload.slowSet.val
        · rw [CoordinatorRecorderComplementBridge.extendedCurrentWeights_eq_anchor
            _ arm hslow,
            CoordinatorRecorderComplementBridge.extendedCurrentWeights_eq_anchor
              _ arm hslow]
        · let fast : FastArm r.payload.slowSet :=
            ⟨arm, Finset.mem_sdiff.mpr ⟨Finset.mem_univ arm, hslow⟩⟩
          rw [CoordinatorRecorderComplementBridge.extendedCurrentWeights_eq_complement
            _ fast,
            CoordinatorRecorderComplementBridge.extendedCurrentWeights_eq_complement
              _ fast]
          rfl
      have hc : CoordinatorLiveChoiceRecorderStep.recorderInput c value.2 =
          CoordinatorLiveChoiceRecorderStep.flowRecorderInput r value.1
            c.ownArm value.2 := by
        simp only [CoordinatorLiveChoiceRecorderStep.recorderInput,
          CoordinatorLiveChoiceRecorderStep.flowRecorderInput,
          c.preChoiceMode_eq]
      have hinput : CoordinatorRecorderComplementBridge.recorderInput
          (CoordinatorLiveChoiceRecorderStep.recorderInput c value.2) =
        CoordinatorRecordingMeasurability.inputAt
          (CoordinatorLiveChoiceRecorderStep.flowRecorderBase r)
          (value.1, (CoordinatorLiveChoiceRecorderStep.flowArmAt r value.1,
            value.2)) := by
        rw [hc, harm]
        simp only [CoordinatorRecorderComplementBridge.recorderInput,
          CoordinatorRecorderComplementBridge.recorderInputWithWeights,
          CoordinatorRecordingMeasurability.inputAt,
          CoordinatorLiveChoiceRecorderStep.flowRecorderBase]
        rw [hweights]
        rfl
      rw [CoordinatorRecorderComplementBridge.run_eq_accepted, hinput]
      rfl
    cases hrecording : CoordinatorLiveChoiceRecorderStep.flowRecorderAt r value with
    | none => simp [run, hprepare, hrecord, hrecording, factor]
    | some recording =>
        cases hserviced : servicePass r q recording with
        | error failure =>
            simp [run, hprepare, hrecord, hrecording, hserviced, factor]
        | ok serviced =>
            have hconfirmation :
                CoordinatorLocalArmChoice.confirmationUpdate r.payload
                  r.pendingAtChoice c.sourceCutoff r.time value.1 value.2 =
                CoordinatorLiveChoiceRecorderStep.flowConfirmationAt r value := rfl
            cases hpending : CoordinatorLiveChoiceRecorderStep.flowConfirmationAt
                r value with
            | none =>
                simp only [run, hprepare, hrecord, hrecording, hserviced,
                  hconfirmation, hpending, factor]
            | some pendingAfter =>
                obtain ⟨finishResult, hfinish, hclock, _, _⟩ :=
                  finishRound_live_success domain c hprepare pendingAfter
                simp only [run, hprepare, hrecord, hrecording, hserviced,
                  hconfirmation, hpending, hfinish, hclock, factor,
                  codeOfServiced, savedProposalClock, harm]
  rw [heq]
  exact hfactor.comp htuple

end Bandits.Support.CoordinatorLiveServiceFinish

end
