/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ActiveFollowerLifecycle
public import Bandits.Support.DeclaredFollowerLocalRound
public import Bandits.Support.ActiveFollowerDownAcceptance
public import Bandits.Support.FollowerDownMeasurability
public import Bandits.Support.FollowerDownJointMeasurability
import Bandits.Support.ActiveFollowerQueueOperation
public import Bandits.Support.FollowerActionMeasurability
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Tactic.DeriveCountable
import Lean.Elab.Tactic.Omega

/-!
# Measurability of the actual follower lifecycle and arm preparation

This module codes the existing follower state with its accepted countable
register code and its exact timestamp/pilot buffer skeleton. The original
saved observation/thinning family remains continuous and unchanged.

Sources: `sources/zip4/manuscript/06_interruptions.tex:108-114,237-297`,
`sources/zip4/manuscript/07_public_setup.tex:52-55`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:8-14`.

The results concern the supplied local operations. They establish no physical
reachability, law, message truth, or manuscript theorem closure.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.FollowerLifecycleMeasurability

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.CompletePublicTable
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.SparseCalendarReplay
open Bandits.Support.ActiveFollowerLifecycle
open Bandits.Support.ActiveFollowerDownAcceptance
open Bandits.Support.FollowerDownMeasurability
  (SavedScalar SavedScalarFamily FollowerStateCode followerStateCode followerStateOfCode
    feedbackAtGrid feedbackAtGrid_is_quantized quantizedObservationGrid)
open Bandits.Support.FollowerDownJointMeasurability
  (BufferSkeletonCode bufferFromSkeletonAndScalars)
open Bandits.Support.DeclaredFollowerLocalRound

/-- The actual active calendar coordinates for a fixed activation. -/
abbrev ActiveCalendarTime (p : Parameters) (activation : Activation p) :=
  {t : Fin p.T // activation.val ≤ t.val + 1}

/-- The lossless code of the one-bit proposal memory. -/
abbrev LocalMemoryCode (p : Parameters) := Option (Fin p.T × Bool)

/-- Encode the actual last proposal read without adding history. -/
def localMemoryCode {p : Parameters} (memory : LocalMemory p) : LocalMemoryCode p :=
  memory.lastProposalRead.map fun token => (token.timestamp, token.bit)

/-- Decode a proposal-memory code exactly. -/
def localMemoryOfCode {p : Parameters} (code : LocalMemoryCode p) : LocalMemory p :=
  ⟨code.map fun token => ⟨token.1, token.2⟩⟩

theorem localMemoryOfCode_code {p : Parameters} (memory : LocalMemory p) :
    localMemoryOfCode (localMemoryCode memory) = memory := by
  cases memory with
  | mk token => cases token <;> rfl

theorem localMemoryCodeOfCode {p : Parameters} (code : LocalMemoryCode p) :
    localMemoryCode (localMemoryOfCode code) = code := by
  cases code with
  | none => rfl
  | some token => cases token; rfl

/-- Dagger or an ordinary configuration represented by the accepted
countable state code and lossless proposal-memory code. -/
abbrev LocalConfigurationCode (p : Parameters) (rate : RateInput p) :=
  Option (FollowerStateCode p rate × LocalMemoryCode p)

instance localConfigurationCodeCountable (p : Parameters) (rate : RateInput p) :
    Countable (LocalConfigurationCode p rate) := inferInstance

instance localConfigurationCodeMeasurableSpace (p : Parameters) (rate : RateInput p) :
    MeasurableSpace (LocalConfigurationCode p rate) := ⊤

/-- Encode the actual ordinary configuration, or the absorbing dagger tag. -/
def localConfigurationCode {p : Parameters} {rate : RateInput p}
    (configuration : LocalConfiguration p rate) : LocalConfigurationCode p rate :=
  match configuration with
  | .dagger => none
  | .ordinary state memory => some (followerStateCode rate state, localMemoryCode memory)

/-- Decode a configuration while retaining the supplied buffer literally. -/
def localConfigurationOfCode {p : Parameters} (rate : RateInput p)
    (code : LocalConfigurationCode p rate)
    (buffer : List (SparseCalendarRecord p.K)) : LocalConfiguration p rate :=
  match code with
  | none => .dagger
  | some (state, memory) =>
      .ordinary (followerStateOfCode rate state buffer) (localMemoryOfCode memory)

/-- Encoding and decoding an actual configuration reconstructs its full
state and memory when the original buffer is supplied unchanged. -/
theorem localConfigurationOfCode_code {p : Parameters} {rate : RateInput p}
    (configuration : LocalConfiguration p rate) :
    localConfigurationOfCode rate (localConfigurationCode configuration)
      (match configuration with
      | .dagger => []
      | .ordinary state _ => state.buffer) = configuration := by
  cases configuration with
  | dagger => rfl
  | ordinary state memory =>
      simp [localConfigurationOfCode, localConfigurationCode,
        FollowerDownMeasurability.followerStateOfCode_code_eq,
        localMemoryOfCode_code]

/-- A finite code retaining all six distinct lifecycle failure reasons. -/
def lifecycleFailureCode : LifecycleFailure → Fin 6
  | .invalidLocalStateDomain => 0
  | .missingAcceptedDown => 1
  | .incompatibleAcceptedDown => 2
  | .missedGridBoundary => 3
  | .missingProposalRead => 4
  | .staleProposalRead => 5

/-- Decode a lifecycle failure code. The last branch is only a total extension
for code values that are not emitted by `lifecycleFailureCode`. -/
def lifecycleFailureOfCode (code : Fin 6) : LifecycleFailure :=
  if code.val = 0 then .invalidLocalStateDomain
  else if code.val = 1 then .missingAcceptedDown
  else if code.val = 2 then .incompatibleAcceptedDown
  else if code.val = 3 then .missedGridBoundary
  else if code.val = 4 then .missingProposalRead
  else .staleProposalRead

theorem lifecycleFailureOfCode_code (reason : LifecycleFailure) :
    lifecycleFailureOfCode (lifecycleFailureCode reason) = reason := by
  cases reason <;> rfl

/-- The complete discrete output of the actual `startRound`: every failure
reason is retained, while success uses the existing follower-state code. -/
inductive StartRoundResultCode (p : Parameters) (rate : RateInput p) where
  | failure (reason : Fin 6)
  | success (state : FollowerStateCode p rate) (memory : LocalMemoryCode p)
  deriving Countable

instance startRoundResultCodeMeasurableSpace (p : Parameters) (rate : RateInput p) :
    MeasurableSpace (StartRoundResultCode p rate) := ⊤

/-- Encode the exact result of the existing `startRound`. -/
def startRoundResultCode {p : Parameters} (rate : RateInput p)
    (result : LifecycleCheck
      (ReferencePrelaunchFollower.State p rate.eta × LocalMemory p)) :
    StartRoundResultCode p rate :=
  match result with
  | .error reason => .failure (lifecycleFailureCode reason)
  | .ok (state, memory) => .success (followerStateCode rate state) (localMemoryCode memory)

/-- Reconstruct a coded `startRound` result from the unchanged input buffer. -/
def startRoundResultOfCode {p : Parameters} (rate : RateInput p)
    (buffer : List (SparseCalendarRecord p.K)) : StartRoundResultCode p rate →
      LifecycleCheck
        (ReferencePrelaunchFollower.State p rate.eta × LocalMemory p)
  | .failure reason => .error (lifecycleFailureOfCode reason)
  | .success state memory =>
      .ok (followerStateOfCode rate state buffer, localMemoryOfCode memory)

/-- The actual start result is exactly reconstructed from its code and the
unchanged original input buffer. -/
theorem startRoundResultOfCode_code {p : Parameters} (rate : RateInput p)
    (t : Fin p.T) (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : LocalMemory p) :
    startRoundResultOfCode rate state.buffer
        (startRoundResultCode rate (ActiveFollowerLifecycle.startRound
          rate.eta t state memory)) =
      ActiveFollowerLifecycle.startRound rate.eta t state memory := by
  cases hstart : ActiveFollowerLifecycle.startRound rate.eta t state memory with
  | error reason =>
      simp [startRoundResultCode, startRoundResultOfCode,
        lifecycleFailureOfCode_code]
  | ok result =>
      cases result with
      | mk output outputMemory =>
          have hframe := ActiveFollowerLifecycle.startRound_frame rate.eta t state
            output memory outputMemory hstart
          rcases hframe with ⟨_, _, _, _, _, hbuffer, _, _⟩
          simp [startRoundResultCode, startRoundResultOfCode,
            FollowerDownMeasurability.followerStateOfCode_code_eq rate output
              state.buffer hbuffer,
            localMemoryOfCode_code]

/-- The exact discrete result of the actual pending-release operation. -/
inductive ReleaseAfterServiceResultCode (p : Parameters) (rate : RateInput p) where
  | failure (reason : Fin 6)
  | success (state : FollowerStateCode p rate)
  deriving Countable

instance releaseAfterServiceResultCodeMeasurableSpace (p : Parameters)
    (rate : RateInput p) : MeasurableSpace (ReleaseAfterServiceResultCode p rate) := ⊤

/-- Encode every failure and the complete follower-state code returned by
`releaseAfterService`. -/
def releaseAfterServiceResultCode {p : Parameters} (rate : RateInput p)
    (result : LifecycleCheck (ReferencePrelaunchFollower.State p rate.eta)) :
    ReleaseAfterServiceResultCode p rate :=
  match result with
  | .error reason => .failure (lifecycleFailureCode reason)
  | .ok state => .success (followerStateCode rate state)

/-- Decode a release result with the unchanged post-service buffer. -/
def releaseAfterServiceResultOfCode {p : Parameters} (rate : RateInput p)
    (buffer : List (SparseCalendarRecord p.K)) : ReleaseAfterServiceResultCode p rate →
      LifecycleCheck (ReferencePrelaunchFollower.State p rate.eta)
  | .failure reason => .error (lifecycleFailureOfCode reason)
  | .success state => .ok (followerStateOfCode rate state buffer)

/-- Every successful release preserves the supplied post-service buffer. -/
theorem releaseAfterService_buffer_preserved {p : Parameters} (rate : RateInput p)
    (i : Fin (p.m - 1)) (t : Fin p.T) (row : FollowerPublicRow p.m p.K)
    (own : ReferencePrelaunchFollower.Observation p)
    (preChoice postService output : ReferencePrelaunchFollower.State p rate.eta)
    (h : ActiveFollowerLifecycle.releaseAfterService rate.eta i t row own
      preChoice postService = .ok output) :
    output.buffer = postService.buffer := by
  classical
  by_cases hpending : preChoice.status = .pending
  · by_cases hpre : ActiveFollowerLifecycle.localStateDomainValid preChoice
    · cases hlast : preChoice.lastDown with
      | none => simp [ActiveFollowerLifecycle.releaseAfterService, hpending, hpre, hlast] at h
      | some M =>
          by_cases htime : M.val.sigma ≤ t.val
          · by_cases hpost : ActiveFollowerLifecycle.localStateDomainValid postService
            · by_cases hcondition : ActiveFollowerLifecycle.releaseCondition rate.eta i row own M
              · let out := {postService with status := ActiveRoundActions.FollowerStatus.released}
                by_cases hrecord : out.status = .unoccupied ∨
                    (∃ M', out.lastDown = some M' ∧ M'.val.sigma ≤ t.val + 1)
                · have hresult := by
                    have hrecord' : ∃ M', postService.lastDown = some M' ∧
                        M'.val.sigma ≤ t.val + 1 := by
                      simpa [out] using hrecord
                    simpa [ActiveFollowerLifecycle.releaseAfterService, hpending, hpre,
                      hlast, htime, hpost, hcondition, hrecord'] using h
                  cases hresult
                  rfl
                · have hrecord' : ¬(∃ M', postService.lastDown = some M' ∧
                    M'.val.sigma ≤ t.val + 1) := by
                    simpa [out] using hrecord
                  simp [ActiveFollowerLifecycle.releaseAfterService, hpending, hpre,
                    hlast, htime, hpost, hcondition, hrecord'] at h
              · let out := postService
                by_cases hrecord : out.status = .unoccupied ∨
                    (∃ M', out.lastDown = some M' ∧ M'.val.sigma ≤ t.val + 1)
                · have hresult := by
                    simpa [ActiveFollowerLifecycle.releaseAfterService, hpending, hpre,
                      hlast, htime, hpost, hcondition, out, hrecord] using h
                  cases hresult
                  rfl
                · simp [ActiveFollowerLifecycle.releaseAfterService, hpending, hpre,
                    hlast, htime, hpost, hcondition, out, hrecord] at h
            · simp [ActiveFollowerLifecycle.releaseAfterService, hpending, hpre,
                hlast, htime, hpost] at h
          · simp [ActiveFollowerLifecycle.releaseAfterService, hpending, hpre,
              hlast, htime] at h
    · simp [ActiveFollowerLifecycle.releaseAfterService, hpending, hpre] at h
  · have hresult := by
      simpa [ActiveFollowerLifecycle.releaseAfterService, hpending] using h
    cases hresult
    rfl

/-- The coded actual release result reconstructs its entire returned state
from the post-service buffer and retains every failure code. -/
theorem releaseAfterServiceResultOfCode_code {p : Parameters} (rate : RateInput p)
    (i : Fin (p.m - 1)) (t : Fin p.T) (row : FollowerPublicRow p.m p.K)
    (own : ReferencePrelaunchFollower.Observation p)
    (preChoice postService : ReferencePrelaunchFollower.State p rate.eta) :
    releaseAfterServiceResultOfCode rate postService.buffer
        (releaseAfterServiceResultCode rate
          (ActiveFollowerLifecycle.releaseAfterService rate.eta i t row own
            preChoice postService)) =
      ActiveFollowerLifecycle.releaseAfterService rate.eta i t row own
        preChoice postService := by
  cases hrelease : ActiveFollowerLifecycle.releaseAfterService rate.eta i t row own
      preChoice postService with
  | error reason =>
      simp [releaseAfterServiceResultCode, releaseAfterServiceResultOfCode,
        lifecycleFailureOfCode_code]
  | ok output =>
      have hbuffer := releaseAfterService_buffer_preserved rate i t row own
        preChoice postService output hrelease
      simp [releaseAfterServiceResultCode, releaseAfterServiceResultOfCode,
        FollowerDownMeasurability.followerStateOfCode_code_eq rate output
          postService.buffer hbuffer]

/-- A zero-grid saved scalar used only as a measurable reference point for a
fixed discrete buffer skeleton. It is never substituted into an operation's
actual input or output. -/
def canonicalSavedScalar (p : Parameters) : SavedScalar :=
  ((feedbackAtGrid p ⟨0, by omega⟩).val, ⟨0, by norm_num⟩)

/-- The canonical reference family for a fixed finite buffer length. -/
def canonicalSavedFamily (p : Parameters) (n : ℕ) : SavedScalarFamily n :=
  fun _ => canonicalSavedScalar p

/-- The canonical scalar has an observation on the source finite grid. -/
theorem canonicalSavedScalar_grid (p : Parameters) :
    (canonicalSavedScalar p).1 ∈ quantizedObservationGrid p := by
  exact feedbackAtGrid_is_quantized p ⟨0, by omega⟩

/-- Build a reference buffer with the exact discrete skeleton and canonical
grid scalars. -/
def bufferSkeletonTemplate {p : Parameters} {n : ℕ}
    (skeleton : BufferSkeletonCode p n) : List (SparseCalendarRecord p.K) :=
  bufferFromSkeletonAndScalars skeleton (canonicalSavedFamily p n)

theorem bufferSkeletonTemplate_length {p : Parameters} {n : ℕ}
    (skeleton : BufferSkeletonCode p n) :
    (bufferSkeletonTemplate skeleton).length = n := by
  simp [bufferSkeletonTemplate, bufferFromSkeletonAndScalars]

/-- Reindex an original family along the template's finite-position
equivalence. -/
def templateSavedValues {p : Parameters} {n : ℕ}
    (skeleton : BufferSkeletonCode p n) (values : SavedScalarFamily n) :
    SavedScalarFamily (bufferSkeletonTemplate skeleton).length :=
  fun j => values (Fin.cast (bufferSkeletonTemplate_length skeleton) j)

/-- Replacing the reference scalars in a skeleton template gives precisely
the existing lossless skeleton/scalar reconstruction. -/
theorem replaceTemplateScalars_eq_bufferFromSkeleton {p : Parameters} {n : ℕ}
    (skeleton : BufferSkeletonCode p n) (values : SavedScalarFamily n) :
    FollowerDownMeasurability.replaceBufferScalars
        (bufferSkeletonTemplate skeleton) (templateSavedValues skeleton values) =
      bufferFromSkeletonAndScalars skeleton values := by
  simp [templateSavedValues, bufferSkeletonTemplate,
    FollowerDownMeasurability.replaceBufferScalars,
    bufferFromSkeletonAndScalars]
  funext j
  congr 1

/-- The local lifecycle validator and the accepted DOWN input validator check
the same timestamp, duplicate-key, and finite-grid observation conditions. -/
theorem localBufferValid_iff_bufferInputDomain {p : Parameters} {eta : LearningRate}
    (state : ReferencePrelaunchFollower.State p eta) :
    ActiveFollowerLifecycle.localBufferValid state ↔
      ActiveFollowerDownAcceptance.bufferInputDomain p state.buffer := by
  constructor
  · intro h
    constructor
    · intro record hrecord
      rcases h.1 record hrecord with ⟨hlo, hhi⟩
      rcases h.2.2 record hrecord with ⟨q, hq, hvalue⟩
      refine ⟨hlo, hhi, ?_⟩
      exact ⟨⟨q, by omega⟩, by simpa using hvalue⟩
    · exact h.2.1
  · intro h
    constructor
    · intro record hrecord
      rcases h.1 record hrecord with ⟨hlo, hhi, _⟩
      exact ⟨hlo, hhi⟩
    · constructor
      · exact h.2
      · intro record hrecord
        rcases (h.1 record hrecord).2.2 with ⟨q, hvalue⟩
        exact ⟨q.val, by omega, by simpa using hvalue⟩

/-- The actual start-round result code at a fixed incoming discrete state,
memory, and buffer skeleton. Its remaining inputs are the original scalar
family and calendar coordinate. -/
def startRoundResultCodeAt {p : Parameters} (rate : RateInput p) {n : ℕ}
    (stateCode : FollowerStateCode p rate) (memoryCode : LocalMemoryCode p)
    (skeleton : BufferSkeletonCode p n) (values : SavedScalarFamily n)
    (t : Fin p.T) : StartRoundResultCode p rate :=
  startRoundResultCode rate (ActiveFollowerLifecycle.startRound rate.eta t
    (followerStateOfCode rate stateCode (bufferFromSkeletonAndScalars skeleton values))
    (localMemoryOfCode memoryCode))

/-- Reconstruct the exact actual start-round result, retaining its original
buffer and all failure reasons. -/
theorem startRoundResultCodeAt_reconstruct {p : Parameters} (rate : RateInput p)
    {n : ℕ} (stateCode : FollowerStateCode p rate) (memoryCode : LocalMemoryCode p)
    (skeleton : BufferSkeletonCode p n) (values : SavedScalarFamily n) (t : Fin p.T) :
    startRoundResultOfCode rate (bufferFromSkeletonAndScalars skeleton values)
        (startRoundResultCodeAt rate stateCode memoryCode skeleton values t) =
      ActiveFollowerLifecycle.startRound rate.eta t
        (followerStateOfCode rate stateCode (bufferFromSkeletonAndScalars skeleton values))
        (localMemoryOfCode memoryCode) := by
  exact startRoundResultOfCode_code rate t
    (followerStateOfCode rate stateCode (bufferFromSkeletonAndScalars skeleton values))
    (localMemoryOfCode memoryCode)

/-- The actual pending-release result on two independently supplied local
states. Each state's original continuous buffer scalars vary over its own
finite product; the two skeletons and discrete codes remain fixed. -/
def releaseAfterServiceResultCodeAt {p : Parameters} (rate : RateInput p)
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (time : Fin p.T) (feedback : Fin (D p + 1))
    (preCode postCode : FollowerStateCode p rate)
    {n m : ℕ} (preSkeleton : BufferSkeletonCode p n)
    (postSkeleton : BufferSkeletonCode p m)
    (preValues : SavedScalarFamily n) (postValues : SavedScalarFamily m) :
    ReleaseAfterServiceResultCode p rate :=
  releaseAfterServiceResultCode rate
    (ActiveFollowerLifecycle.releaseAfterService rate.eta i time
      (ActiveFollowerLifecycle.publicRowOfCompleteRow row time)
      (feedbackAtGrid p feedback)
      (followerStateOfCode rate preCode
        (bufferFromSkeletonAndScalars preSkeleton preValues))
      (followerStateOfCode rate postCode
        (bufferFromSkeletonAndScalars postSkeleton postValues)))

/-- Exact output reconstruction for the two-state release code, using the
unchanged buffer of the supplied post-service state. -/
theorem releaseAfterServiceResultCodeAt_reconstruct {p : Parameters}
    (rate : RateInput p) (i : Fin (p.m - 1))
    (row : CompletePublicTable.CompleteRow p) (time : Fin p.T)
    (feedback : Fin (D p + 1)) (preCode postCode : FollowerStateCode p rate)
    {n m : ℕ} (preSkeleton : BufferSkeletonCode p n)
    (postSkeleton : BufferSkeletonCode p m)
    (preValues : SavedScalarFamily n) (postValues : SavedScalarFamily m) :
    releaseAfterServiceResultOfCode rate
        (bufferFromSkeletonAndScalars postSkeleton postValues)
        (releaseAfterServiceResultCodeAt rate i row time feedback preCode postCode
          preSkeleton postSkeleton preValues postValues) =
      ActiveFollowerLifecycle.releaseAfterService rate.eta i time
        (ActiveFollowerLifecycle.publicRowOfCompleteRow row time)
        (feedbackAtGrid p feedback)
        (followerStateOfCode rate preCode
          (bufferFromSkeletonAndScalars preSkeleton preValues))
        (followerStateOfCode rate postCode
          (bufferFromSkeletonAndScalars postSkeleton postValues)) := by
  exact releaseAfterServiceResultOfCode_code rate i time
    (ActiveFollowerLifecycle.publicRowOfCompleteRow row time) (feedbackAtGrid p feedback)
    (followerStateOfCode rate preCode
      (bufferFromSkeletonAndScalars preSkeleton preValues))
    (followerStateOfCode rate postCode
      (bufferFromSkeletonAndScalars postSkeleton postValues))

/-- The exact discrete result of the existing combined release and final
proposal-read operation. Its failure payload retains the source stage and
reason verbatim. -/
inductive ReleaseAndFinishResultCode (p : Parameters) (rate : RateInput p) where
  | failure (reason : RoundFailure)
  | success (state : FollowerStateCode p rate) (memory : LocalMemoryCode p)

instance releaseAndFinishResultCodeMeasurableSpace (p : Parameters)
    (rate : RateInput p) : MeasurableSpace (ReleaseAndFinishResultCode p rate) := ⊤

/-- Encode an actual combined result, preserving every failure constructor. -/
def releaseAndFinishResultCode {p : Parameters} (rate : RateInput p)
    (result : Except RoundFailure
      (ReferencePrelaunchFollower.State p rate.eta × LocalMemory p)) :
    ReleaseAndFinishResultCode p rate :=
  match result with
  | .error reason => .failure reason
  | .ok (state, memory) => .success (followerStateCode rate state) (localMemoryCode memory)

/-- Decode a combined result while retaining the post-service buffer exactly. -/
def releaseAndFinishResultOfCode {p : Parameters} (rate : RateInput p)
    (buffer : List (SparseCalendarRecord p.K)) : ReleaseAndFinishResultCode p rate →
      Except RoundFailure
        (ReferencePrelaunchFollower.State p rate.eta × LocalMemory p)
  | .failure reason => .error reason
  | .success state memory =>
      .ok (followerStateOfCode rate state buffer, localMemoryOfCode memory)

/-- The combined release and final read preserve the supplied post-state
buffer on every successful path. -/
theorem releaseAndFinish_buffer_preserved {p : Parameters} (rate : RateInput p)
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (time : Fin p.T) (own : ReferencePrelaunchFollower.Observation p)
    (choiceState postState : ReferencePrelaunchFollower.State p rate.eta)
    (memory : LocalMemory p) (output : ReferencePrelaunchFollower.State p rate.eta)
    (outputMemory : LocalMemory p)
    (h : DeclaredFollowerLocalRound.releaseAndFinish rate i row time own choiceState
      memory postState = .ok (output, outputMemory)) :
    output.buffer = postState.buffer := by
  unfold DeclaredFollowerLocalRound.releaseAndFinish at h
  cases hrelease : ActiveFollowerLifecycle.releaseAfterService rate.eta i time
      (ActiveFollowerLifecycle.publicRowOfCompleteRow row time) own choiceState postState with
  | error reason => simp [hrelease] at h
  | ok released =>
      have hreleaseBuffer := releaseAfterService_buffer_preserved rate i time
        (ActiveFollowerLifecycle.publicRowOfCompleteRow row time) own choiceState
        postState released hrelease
      cases hfinish : ActiveFollowerLifecycle.finishRound rate.eta time row released memory with
      | error reason => simp [hrelease, hfinish] at h
      | ok result =>
          rcases result with ⟨finished, finishedMemory⟩
          have hframe := ActiveFollowerLifecycle.finishRound_frame rate.eta time row
            released finished memory finishedMemory hfinish
          have hfinished : finished = output ∧ finishedMemory = outputMemory := by
            simpa [hrelease, hfinish] using h
          have hpair : (output, outputMemory) = (finished, finishedMemory) :=
            Prod.ext hfinished.1.symm hfinished.2.symm
          cases hpair
          rw [hframe, hreleaseBuffer]

/-- Reconstruct the entire successful combined state and memory from the
exact code and unchanged post-state buffer. -/
theorem releaseAndFinishResultOfCode_code {p : Parameters} (rate : RateInput p)
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (time : Fin p.T) (own : ReferencePrelaunchFollower.Observation p)
    (choiceState postState : ReferencePrelaunchFollower.State p rate.eta)
    (memory : LocalMemory p) :
    releaseAndFinishResultOfCode rate postState.buffer
        (releaseAndFinishResultCode rate
          (DeclaredFollowerLocalRound.releaseAndFinish rate i row time own choiceState
            memory postState)) =
      DeclaredFollowerLocalRound.releaseAndFinish rate i row time own choiceState
        memory postState := by
  cases hresult : DeclaredFollowerLocalRound.releaseAndFinish rate i row time own choiceState
      memory postState with
  | error reason => simp [releaseAndFinishResultCode, releaseAndFinishResultOfCode]
  | ok result =>
      rcases result with ⟨output, outputMemory⟩
      have hbuffer := releaseAndFinish_buffer_preserved rate i row time own choiceState
        postState memory output outputMemory hresult
      simp [releaseAndFinishResultCode, releaseAndFinishResultOfCode,
        FollowerDownMeasurability.followerStateOfCode_code_eq rate output
          postState.buffer hbuffer, localMemoryOfCode_code]

/-- The actual combined release/finish result on two independently supplied
states with their own unchanged buffer skeletons and original scalar families. -/
def releaseAndFinishResultCodeAt {p : Parameters} (rate : RateInput p)
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (time : Fin p.T) (feedback : Fin (D p + 1))
    (preCode postCode : FollowerStateCode p rate) (memoryCode : LocalMemoryCode p)
    {n m : ℕ} (preSkeleton : BufferSkeletonCode p n)
    (postSkeleton : BufferSkeletonCode p m)
    (preValues : SavedScalarFamily n) (postValues : SavedScalarFamily m) :
    ReleaseAndFinishResultCode p rate :=
  releaseAndFinishResultCode rate
    (DeclaredFollowerLocalRound.releaseAndFinish rate i row time
      (feedbackAtGrid p feedback)
      (followerStateOfCode rate preCode
        (bufferFromSkeletonAndScalars preSkeleton preValues))
      (localMemoryOfCode memoryCode)
      (followerStateOfCode rate postCode
        (bufferFromSkeletonAndScalars postSkeleton postValues)))

/-- Exact reconstruction for the combined code retains its complete row,
calendar time, own finite-grid feedback and unchanged post-state buffer. -/
theorem releaseAndFinishResultCodeAt_reconstruct {p : Parameters}
    (rate : RateInput p) (i : Fin (p.m - 1))
    (row : CompletePublicTable.CompleteRow p) (time : Fin p.T)
    (feedback : Fin (D p + 1)) (preCode postCode : FollowerStateCode p rate)
    (memoryCode : LocalMemoryCode p) {n m : ℕ}
    (preSkeleton : BufferSkeletonCode p n) (postSkeleton : BufferSkeletonCode p m)
    (preValues : SavedScalarFamily n) (postValues : SavedScalarFamily m) :
    releaseAndFinishResultOfCode rate
        (bufferFromSkeletonAndScalars postSkeleton postValues)
        (releaseAndFinishResultCodeAt rate i row time feedback preCode postCode memoryCode
          preSkeleton postSkeleton preValues postValues) =
      DeclaredFollowerLocalRound.releaseAndFinish rate i row time (feedbackAtGrid p feedback)
        (followerStateOfCode rate preCode
          (bufferFromSkeletonAndScalars preSkeleton preValues))
        (localMemoryOfCode memoryCode)
        (followerStateOfCode rate postCode
          (bufferFromSkeletonAndScalars postSkeleton postValues)) := by
  exact releaseAndFinishResultOfCode_code rate i row time (feedbackAtGrid p feedback)
    (followerStateOfCode rate preCode
      (bufferFromSkeletonAndScalars preSkeleton preValues))
    (followerStateOfCode rate postCode
      (bufferFromSkeletonAndScalars postSkeleton postValues))
    (localMemoryOfCode memoryCode)

private theorem localStateDomainValid_canonical_of_valid {p : Parameters}
    (rate : RateInput p) {n : ℕ} (stateCode : FollowerStateCode p rate)
    (skeleton : BufferSkeletonCode p n) (values : SavedScalarFamily n)
    (hvalid : ActiveFollowerLifecycle.localStateDomainValid
      (followerStateOfCode rate stateCode (bufferFromSkeletonAndScalars skeleton values))) :
    ActiveFollowerLifecycle.localStateDomainValid
      (followerStateOfCode rate stateCode (bufferSkeletonTemplate skeleton)) := by
  have hbuffer : ActiveFollowerDownAcceptance.bufferInputDomain p
      (bufferFromSkeletonAndScalars skeleton values) :=
    (localBufferValid_iff_bufferInputDomain
      (followerStateOfCode rate stateCode (bufferFromSkeletonAndScalars skeleton values))).mp
      hvalid.2.1
  let template := bufferSkeletonTemplate skeleton
  have htemplate : ActiveFollowerDownAcceptance.bufferInputDomain p
      (FollowerDownMeasurability.replaceBufferScalars template
        (templateSavedValues skeleton values)) := by
    rw [replaceTemplateScalars_eq_bufferFromSkeleton]
    exact hbuffer
  rcases (FollowerDownMeasurability.bufferInputDomain_replace_iff template
      (templateSavedValues skeleton values)).mp htemplate with ⟨hskeleton, _⟩
  have hcanonicalGrid : FollowerDownMeasurability.carriedBufferGridTest p
      (FollowerDownMeasurability.replaceBufferScalars template
        (templateSavedValues skeleton (canonicalSavedFamily p n))) := by
    rw [FollowerDownMeasurability.carriedBufferGridTest_replace_iff]
    intro j
    simpa [templateSavedValues, canonicalSavedFamily] using canonicalSavedScalar_grid p
  have hcanonical : ActiveFollowerDownAcceptance.bufferInputDomain p
      (FollowerDownMeasurability.replaceBufferScalars template
        (templateSavedValues skeleton (canonicalSavedFamily p n))) :=
    (FollowerDownMeasurability.bufferInputDomain_replace_iff template
      (templateSavedValues skeleton (canonicalSavedFamily p n))).mpr
      ⟨hskeleton, hcanonicalGrid⟩
  have hcanonicalBuffer : ActiveFollowerDownAcceptance.bufferInputDomain p
      (bufferSkeletonTemplate skeleton) := by
    rw [replaceTemplateScalars_eq_bufferFromSkeleton] at hcanonical
    simpa [template, bufferSkeletonTemplate] using hcanonical
  have hregisters : ActiveFollowerLifecycle.serviceRegistersValid p
      (followerStateOfCode rate stateCode (bufferSkeletonTemplate skeleton)) := by
    exact hvalid.1
  have hbatch : ActiveFollowerLifecycle.downDecoderStateValid
      (followerStateOfCode rate stateCode (bufferSkeletonTemplate skeleton)) := by
    exact hvalid.2.2
  exact ⟨hregisters,
    (localBufferValid_iff_bufferInputDomain
      (followerStateOfCode rate stateCode (bufferSkeletonTemplate skeleton))).mpr
      hcanonicalBuffer,
    hbatch⟩

private theorem startRoundResultCode_eq_of_valid_discrete_eq {p : Parameters}
    (rate : RateInput p) (t : Fin p.T)
    (state state' : ReferencePrelaunchFollower.State p rate.eta)
    (memory : LocalMemory p)
    (hvalid : ActiveFollowerLifecycle.localStateDomainValid state)
    (hvalid' : ActiveFollowerLifecycle.localStateDomainValid state')
    (hstatus : state.status = state'.status)
    (hlast : state.lastDown = state'.lastDown)
    (hstate : state' = {state with buffer := state'.buffer}) :
    startRoundResultCode rate (ActiveFollowerLifecycle.startRound rate.eta t state memory) =
      startRoundResultCode rate (ActiveFollowerLifecycle.startRound rate.eta t state' memory) := by
  have hdecision : ActiveFollowerLifecycle.interruptionDecision rate.eta t state memory =
      ActiveFollowerLifecycle.interruptionDecision rate.eta t state' memory := by
    simp [ActiveFollowerLifecycle.interruptionDecision, hvalid, hvalid', hstatus, hlast]
  unfold ActiveFollowerLifecycle.startRound
  rw [hdecision]
  cases hd : ActiveFollowerLifecycle.interruptionDecision rate.eta t state' memory with
  | error reason => simp [startRoundResultCode]
  | ok interrupted =>
      simp [startRoundResultCode]
      change FollowerDownMeasurability.followerStateCode rate
          {state with status := if interrupted then .unoccupied else state.status} =
        FollowerDownMeasurability.followerStateCode rate
          {state' with status := if interrupted then .unoccupied else state'.status}
      rw [hstate]
      simp [FollowerDownMeasurability.followerStateCode]

private theorem startRoundResultCode_eq_of_domains {p : Parameters}
    (rate : RateInput p) {n : ℕ} (stateCode : FollowerStateCode p rate)
    (skeleton : BufferSkeletonCode p n) (values values' : SavedScalarFamily n)
    (t : Fin p.T) (memoryCode : LocalMemoryCode p)
    (hvalid : ActiveFollowerLifecycle.localStateDomainValid
      (followerStateOfCode rate stateCode (bufferFromSkeletonAndScalars skeleton values)))
    (hvalid' : ActiveFollowerLifecycle.localStateDomainValid
      (followerStateOfCode rate stateCode (bufferFromSkeletonAndScalars skeleton values'))) :
    startRoundResultCodeAt rate stateCode memoryCode skeleton values t =
      startRoundResultCodeAt rate stateCode memoryCode skeleton values' t := by
  let state := followerStateOfCode rate stateCode
    (bufferFromSkeletonAndScalars skeleton values)
  let state' := followerStateOfCode rate stateCode
    (bufferFromSkeletonAndScalars skeleton values')
  have hstatus : state.status = state'.status := by
    simp [state, state', FollowerDownMeasurability.followerStateOfCode]
  have hlast : state.lastDown = state'.lastDown := by
    simp [state, state', FollowerDownMeasurability.followerStateOfCode]
  have hstate : state' = {state with buffer := state'.buffer} := by
    cases stateCode
    simp [state, state', FollowerDownMeasurability.followerStateOfCode,
      FollowerDownMeasurability.followerStatusOfCode,
      FollowerDownMeasurability.decoderBatchOfCode]
  exact startRoundResultCode_eq_of_valid_discrete_eq rate t state state'
    (localMemoryOfCode memoryCode) hvalid hvalid' hstatus hlast hstate

/-- The lifecycle-domain test for a state reconstructed from a fixed countable
code and buffer skeleton is measurable in the original saved scalar family. -/
theorem measurableSet_localStateDomainValid {p : Parameters} (rate : RateInput p)
    {n : ℕ} (stateCode : FollowerStateCode p rate)
    (skeleton : BufferSkeletonCode p n) :
    MeasurableSet {values : SavedScalarFamily n |
      ActiveFollowerLifecycle.localStateDomainValid
        (followerStateOfCode rate stateCode (bufferFromSkeletonAndScalars skeleton values))} := by
  let template := bufferSkeletonTemplate skeleton
  let reindex := templateSavedValues skeleton
  have hindex : Measurable reindex := by
    rw [measurable_pi_iff]
    intro j
    exact measurable_pi_apply (Fin.cast (bufferSkeletonTemplate_length skeleton) j)
  have hbuffer : MeasurableSet {values : SavedScalarFamily n |
      ActiveFollowerDownAcceptance.bufferInputDomain p
        (bufferFromSkeletonAndScalars skeleton values)} := by
    have htemplate : MeasurableSet {templateValues : SavedScalarFamily template.length |
        ActiveFollowerDownAcceptance.bufferInputDomain p
          (FollowerDownMeasurability.replaceBufferScalars template templateValues)} :=
      FollowerDownMeasurability.measurableSet_bufferInputDomain template
    have heq : {values : SavedScalarFamily n |
        ActiveFollowerDownAcceptance.bufferInputDomain p
          (bufferFromSkeletonAndScalars skeleton values)} =
        reindex ⁻¹' {templateValues | ActiveFollowerDownAcceptance.bufferInputDomain p
          (FollowerDownMeasurability.replaceBufferScalars template templateValues)} := by
      ext values
      simp only [Set.mem_preimage, Set.mem_ofPred_eq]
      rw [replaceTemplateScalars_eq_bufferFromSkeleton]
    have hpre := htemplate.preimage hindex
    rw [heq]
    exact hpre
  by_cases hregisters :
      stateCode.S ≤ p.T * D p ∧ stateCode.delta ≤ D p ∧ stateCode.backlog ≤ p.T * D p
  · by_cases hbatch : stateCode.downBatch.1.length < AffineBatchDecoder.quota p ∧
        ∀ batch ∈ stateCode.downBatch.2, batch.length = AffineBatchDecoder.quota p
    · have heq : {values : SavedScalarFamily n |
          ActiveFollowerLifecycle.localStateDomainValid
            (followerStateOfCode rate stateCode
              (bufferFromSkeletonAndScalars skeleton values))} =
          {values | ActiveFollowerDownAcceptance.bufferInputDomain p
            (bufferFromSkeletonAndScalars skeleton values)} := by
        have hregistersState {values : SavedScalarFamily n} :
            ActiveFollowerLifecycle.serviceRegistersValid p
              (followerStateOfCode rate stateCode
                (bufferFromSkeletonAndScalars skeleton values)) := by
          simpa [ActiveFollowerLifecycle.serviceRegistersValid,
            FollowerDownMeasurability.followerStateOfCode] using hregisters
        have hbatchState {values : SavedScalarFamily n} :
            ActiveFollowerLifecycle.downDecoderStateValid
              (followerStateOfCode rate stateCode
                (bufferFromSkeletonAndScalars skeleton values)) := by
          simpa [ActiveFollowerLifecycle.downDecoderStateValid,
            FollowerDownMeasurability.followerStateOfCode,
            FollowerDownMeasurability.decoderBatchOfCode,
            FollowerDownMeasurability.decoderEntryOfCode] using hbatch
        ext values
        constructor
        · intro hvalid
          exact (localBufferValid_iff_bufferInputDomain
            (followerStateOfCode rate stateCode
              (bufferFromSkeletonAndScalars skeleton values))).mp hvalid.2.1
        · intro hbuffer
          exact ⟨hregistersState, (localBufferValid_iff_bufferInputDomain
            (followerStateOfCode rate stateCode
              (bufferFromSkeletonAndScalars skeleton values))).mpr hbuffer, hbatchState⟩
      rw [heq]
      exact hbuffer
    · have hbatchState {values : SavedScalarFamily n} :
          ¬ ActiveFollowerLifecycle.downDecoderStateValid
            (followerStateOfCode rate stateCode
              (bufferFromSkeletonAndScalars skeleton values)) := by
        simpa [ActiveFollowerLifecycle.downDecoderStateValid,
          FollowerDownMeasurability.followerStateOfCode,
          FollowerDownMeasurability.decoderBatchOfCode,
          FollowerDownMeasurability.decoderEntryOfCode] using hbatch
      have heq : {values : SavedScalarFamily n |
          ActiveFollowerLifecycle.localStateDomainValid
            (followerStateOfCode rate stateCode
              (bufferFromSkeletonAndScalars skeleton values))} = ∅ := by
        ext values
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false]
        constructor
        · intro hvalid
          exact hbatchState hvalid.2.2
        · intro hfalse
          exact False.elim hfalse
      rw [heq]
      exact MeasurableSet.empty
  · have heq : {values : SavedScalarFamily n |
        ActiveFollowerLifecycle.localStateDomainValid
          (followerStateOfCode rate stateCode
            (bufferFromSkeletonAndScalars skeleton values))} = ∅ := by
      have hregistersState {values : SavedScalarFamily n} :
          ¬ ActiveFollowerLifecycle.serviceRegistersValid p
            (followerStateOfCode rate stateCode
              (bufferFromSkeletonAndScalars skeleton values)) := by
        simpa [ActiveFollowerLifecycle.serviceRegistersValid,
          FollowerDownMeasurability.followerStateOfCode] using hregisters
      ext values
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false]
      constructor
      · intro hvalid
        exact hregistersState hvalid.1
      · intro hfalse
        exact False.elim hfalse
    rw [heq]
    exact MeasurableSet.empty

/-- The actual start-round result code is jointly measurable in the
original saved scalars and calendar coordinate. No local-domain premise is
assumed: off-grid observations, duplicate keys, invalid timestamps, and all
other checked failures remain represented. -/
theorem measurable_startRoundResultCodeAt {p : Parameters} (rate : RateInput p)
    {n : ℕ} (stateCode : FollowerStateCode p rate) (memoryCode : LocalMemoryCode p)
    (skeleton : BufferSkeletonCode p n) :
    Measurable (fun input : SavedScalarFamily n × Fin p.T =>
      startRoundResultCodeAt rate stateCode memoryCode skeleton input.1 input.2) := by
  classical
  apply measurable_from_prod_countable_left
  intro t
  have hvalidSet := measurableSet_localStateDomainValid rate stateCode skeleton
  let reference := startRoundResultCodeAt rate stateCode memoryCode skeleton
    (canonicalSavedFamily p n) t
  have hformula :
      (fun values : SavedScalarFamily n =>
        startRoundResultCodeAt rate stateCode memoryCode skeleton values t) =
      fun values =>
        if hvalid : ActiveFollowerLifecycle.localStateDomainValid
            (followerStateOfCode rate stateCode
              (bufferFromSkeletonAndScalars skeleton values)) then reference
        else .failure (lifecycleFailureCode .invalidLocalStateDomain) := by
    funext values
    by_cases hvalid : ActiveFollowerLifecycle.localStateDomainValid
        (followerStateOfCode rate stateCode (bufferFromSkeletonAndScalars skeleton values))
    · have hcanonical := localStateDomainValid_canonical_of_valid rate stateCode
        skeleton values hvalid
      have hsame := startRoundResultCode_eq_of_domains rate stateCode skeleton values
        (canonicalSavedFamily p n) t memoryCode hvalid hcanonical
      simp [reference, hsame, hvalid]
    · simp [startRoundResultCodeAt, startRoundResultCode,
        ActiveFollowerLifecycle.startRound,
        ActiveFollowerLifecycle.interruptionDecision, hvalid,
        lifecycleFailureCode]
  rw [hformula]
  exact Measurable.ite hvalidSet measurable_const measurable_const

/-- The exact discrete arm/configuration output of the actual prepare call. -/
structure PreparedRoundCode (p : Parameters) (rate : RateInput p) where
  arm : Fin p.K
  configuration : LocalConfigurationCode p rate
  deriving Countable

instance preparedRoundCodeMeasurableSpace (p : Parameters) (rate : RateInput p) :
    MeasurableSpace (PreparedRoundCode p rate) := ⊤

/-- Encode the prepared arm and ordinary state/memory or dagger tag. -/
def preparedRoundCode {p : Parameters} {rate : RateInput p}
    (prepared : PreparedRound p rate) : PreparedRoundCode p rate :=
  ⟨prepared.arm, localConfigurationCode prepared.configuration⟩

/-- Reconstruct the full prepared round while retaining its carried row,
follower, activation, active-time proof, and original buffer. -/
def preparedRoundOfCode {p : Parameters} (rate : RateInput p)
    (follower : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (activation : Activation p) (time : ActiveCalendarTime p activation)
    (code : PreparedRoundCode p rate)
    (buffer : List (SparseCalendarRecord p.K)) : PreparedRound p rate :=
  ⟨follower, row, activation, time.1, time.2, code.arm,
    localConfigurationOfCode rate code.configuration buffer⟩

/-- Read the unchanged buffer needed to decode a prepared local
configuration; dagger carries no buffer. -/
def preparedRoundBuffer {p : Parameters} {rate : RateInput p}
    (prepared : PreparedRound p rate) : List (SparseCalendarRecord p.K) :=
  match prepared.configuration with
  | .dagger => []
  | .ordinary state _ => state.buffer

/-- Every prepared result is exactly reconstructed from its arm/configuration
code and its unchanged local buffer, with row and active-time data retained. -/
theorem preparedRoundOfCode_preparedRoundCode {p : Parameters}
    (rate : RateInput p) (prepared : PreparedRound p rate) :
    preparedRoundOfCode rate prepared.follower prepared.row prepared.activation
      ⟨prepared.time, prepared.active⟩ (preparedRoundCode prepared)
      (preparedRoundBuffer prepared) = prepared := by
  cases prepared with
  | mk follower row activation time active arm configuration =>
      cases configuration with
      | dagger => rfl
      | ordinary state memory =>
          simp [preparedRoundOfCode, preparedRoundBuffer, preparedRoundCode,
            localConfigurationOfCode, localConfigurationCode,
            FollowerDownMeasurability.followerStateOfCode_code_eq rate state
              state.buffer rfl, localMemoryOfCode_code]

/-- The fallback prepared code is the literal source fallback coordinate and
the absorbing dagger tag. -/
def fallbackPreparedRoundCode {p : Parameters} (rate : RateInput p)
    (i : Fin (p.m - 1)) : PreparedRoundCode p rate :=
  ⟨fallbackArm p i, none⟩

/-- Apply the existing accepted action operation to the state represented by
a successful start-round code. The buffer is empty only in this measurable
representative; exact output reconstruction uses the actual buffer. -/
def armChoiceFromStartCode {p : Parameters} (rate : RateInput p)
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (activation : Activation p) (time : ActiveCalendarTime p activation)
    (stateCode : FollowerStateCode p rate) : Option (Fin p.K) :=
  FollowerActionMeasurability.checkedActiveFollowerArmChoice
    (followerStateOfCode rate stateCode [])
    i row activation time.1 time.2

/-- Decode the exact prepare result from the actual start result code and the
existing checked arm-choice operation. Every failure maps to the source
fallback and dagger. -/
def preparedRoundCodeFromStartCode {p : Parameters} (rate : RateInput p)
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (activation : Activation p) (time : ActiveCalendarTime p activation)
    (startCode : StartRoundResultCode p rate) : PreparedRoundCode p rate :=
  match startCode with
  | .failure _ => fallbackPreparedRoundCode rate i
  | .success stateCode memoryCode =>
      match armChoiceFromStartCode rate i row activation time stateCode with
      | none => fallbackPreparedRoundCode rate i
      | some arm => ⟨arm, some (stateCode, memoryCode)⟩

/-- Encode the output of the actual DeclaredFollowerLocalRound.prepare on a
fixed incoming discrete configuration and buffer skeleton. -/
def prepareRoundCodeAt {p : Parameters} (rate : RateInput p)
    (i : Fin (p.m - 1)) (activation : Activation p)
    (incoming : LocalConfigurationCode p rate) {n : ℕ}
    (skeleton : BufferSkeletonCode p n)
    (row : CompletePublicTable.CompleteRow p)
    (time : ActiveCalendarTime p activation) (values : SavedScalarFamily n) :
    PreparedRoundCode p rate :=
  preparedRoundCode (DeclaredFollowerLocalRound.prepare rate i row activation
    time.1 time.2
    (localConfigurationOfCode rate incoming (bufferFromSkeletonAndScalars skeleton values)))

private theorem prepare_buffer_preserved_of_ordinary {p : Parameters}
    (rate : RateInput p) (i : Fin (p.m - 1))
    (row : CompletePublicTable.CompleteRow p) (activation : Activation p)
    (time : ActiveCalendarTime p activation)
    (input : LocalConfiguration p rate) (output : State p rate.eta)
    (outputMemory : LocalMemory p)
    (h : (DeclaredFollowerLocalRound.prepare rate i row activation time.1 time.2 input).configuration =
      .ordinary output outputMemory) :
    output.buffer =
      match input with
      | .dagger => []
      | .ordinary state _ => state.buffer := by
  cases input with
  | dagger => simp [DeclaredFollowerLocalRound.prepare] at h
  | ordinary state memory =>
      cases hstart : ActiveFollowerLifecycle.startRound rate.eta time.1 state memory with
      | error reason => simp [DeclaredFollowerLocalRound.prepare, hstart] at h
      | ok result =>
          rcases result with ⟨choiceState, choiceMemory⟩
          have hframe := ActiveFollowerLifecycle.startRound_frame rate.eta time.1
            state choiceState memory choiceMemory hstart
          rcases hframe with ⟨_, _, _, _, _, hbuffer, _, _⟩
          cases hoff : ActiveFollowerQueueOperation.checkedUpOffer rate.eta i row
              activation time.1 choiceState with
          | failure => simp [DeclaredFollowerLocalRound.prepare, hstart, hoff] at h
          | noOffer =>
              cases hchoice : ActiveFollowerArmChoice.followerArmChoice choiceState row
                  time.1 i none with
              | none => simp [DeclaredFollowerLocalRound.prepare, hstart, hoff, hchoice] at h
              | some arm =>
                  have hconfig : LocalConfiguration.ordinary choiceState choiceMemory =
                      LocalConfiguration.ordinary output outputMemory := by
                    simpa [DeclaredFollowerLocalRound.prepare, hstart, hoff, hchoice] using h
                  injection hconfig with hstate hmemory
                  subst output
                  exact hbuffer
          | offer offered =>
              cases hchoice : ActiveFollowerArmChoice.followerArmChoice choiceState row
                  time.1 i (some offered) with
              | none => simp [DeclaredFollowerLocalRound.prepare, hstart, hoff, hchoice] at h
              | some arm =>
                  have hconfig : LocalConfiguration.ordinary choiceState choiceMemory =
                      LocalConfiguration.ordinary output outputMemory := by
                    simpa [DeclaredFollowerLocalRound.prepare, hstart, hoff, hchoice] using h
                  injection hconfig with hstate hmemory
                  subst output
                  exact hbuffer

/-- The actual prepared round is exactly reconstructed from its coded arm and
configuration together with the buffer it carries. Its declared row,
follower, activation and active calendar coordinate are retained verbatim. -/
theorem prepareRoundCodeAt_reconstruct {p : Parameters} (rate : RateInput p)
    (i : Fin (p.m - 1)) (activation : Activation p)
    (incoming : LocalConfigurationCode p rate) {n : ℕ}
    (skeleton : BufferSkeletonCode p n)
    (row : CompletePublicTable.CompleteRow p)
    (time : ActiveCalendarTime p activation) (values : SavedScalarFamily n) :
    preparedRoundOfCode rate
      (DeclaredFollowerLocalRound.prepare rate i row activation time.1 time.2
        (localConfigurationOfCode rate incoming (bufferFromSkeletonAndScalars skeleton values))).follower
      (DeclaredFollowerLocalRound.prepare rate i row activation time.1 time.2
        (localConfigurationOfCode rate incoming (bufferFromSkeletonAndScalars skeleton values))).row
      (DeclaredFollowerLocalRound.prepare rate i row activation time.1 time.2
        (localConfigurationOfCode rate incoming (bufferFromSkeletonAndScalars skeleton values))).activation
      ⟨(DeclaredFollowerLocalRound.prepare rate i row activation time.1 time.2
          (localConfigurationOfCode rate incoming (bufferFromSkeletonAndScalars skeleton values))).time,
        (DeclaredFollowerLocalRound.prepare rate i row activation time.1 time.2
          (localConfigurationOfCode rate incoming (bufferFromSkeletonAndScalars skeleton values))).active⟩
      (prepareRoundCodeAt rate i activation incoming skeleton row time values)
      (bufferFromSkeletonAndScalars skeleton values) =
    DeclaredFollowerLocalRound.prepare rate i row activation time.1 time.2
      (localConfigurationOfCode rate incoming (bufferFromSkeletonAndScalars skeleton values)) := by
  cases incoming with
  | none =>
      simp [prepareRoundCodeAt, localConfigurationOfCode,
        DeclaredFollowerLocalRound.prepare, preparedRoundCode,
        preparedRoundOfCode, localConfigurationCode]
  | some incomingData =>
      rcases incomingData with ⟨stateCode, memoryCode⟩
      let inputState := followerStateOfCode rate stateCode
        (bufferFromSkeletonAndScalars skeleton values)
      let inputMemory := localMemoryOfCode memoryCode
      let prepared := DeclaredFollowerLocalRound.prepare rate i row activation
        time.1 time.2 (.ordinary inputState inputMemory)
      have hcode : prepareRoundCodeAt rate i activation (some (stateCode, memoryCode))
          skeleton row time values = preparedRoundCode prepared := by
        rfl
      cases hconfig : prepared.configuration with
      | dagger =>
          have hrec := preparedRoundOfCode_preparedRoundCode rate prepared
          have hbufferIrrelevant :
              preparedRoundOfCode rate prepared.follower prepared.row prepared.activation
                ⟨prepared.time, prepared.active⟩ (preparedRoundCode prepared)
                (bufferFromSkeletonAndScalars skeleton values) =
              preparedRoundOfCode rate prepared.follower prepared.row prepared.activation
                ⟨prepared.time, prepared.active⟩ (preparedRoundCode prepared) [] := by
            simp [preparedRoundOfCode, preparedRoundCode, localConfigurationOfCode,
              localConfigurationCode, hconfig]
          change preparedRoundOfCode rate prepared.follower prepared.row prepared.activation
              ⟨prepared.time, prepared.active⟩ (preparedRoundCode prepared)
              (bufferFromSkeletonAndScalars skeleton values) = prepared
          rw [hbufferIrrelevant]
          simpa [preparedRoundBuffer, hconfig] using hrec
      | ordinary output outputMemory =>
          have hbuffer := prepare_buffer_preserved_of_ordinary rate i row activation time
            (.ordinary inputState inputMemory) output outputMemory (by
              simpa [prepared] using hconfig)
          have hsame : preparedRoundBuffer prepared =
              bufferFromSkeletonAndScalars skeleton values := by
            simpa [preparedRoundBuffer, hconfig, inputState,
              FollowerDownMeasurability.followerStateOfCode] using hbuffer
          change preparedRoundOfCode rate prepared.follower prepared.row prepared.activation
              ⟨prepared.time, prepared.active⟩ (preparedRoundCode prepared)
              (bufferFromSkeletonAndScalars skeleton values) = prepared
          rw [← hsame]
          exact preparedRoundOfCode_preparedRoundCode rate prepared

/-- A successful start result preserves the complete local domain, including
the original buffer, while it changes only the status register. -/
private theorem startRound_success_preserves_domain {p : Parameters}
    (rate : RateInput p) (t : Fin p.T) (state output : State p rate.eta)
    (memory outputMemory : LocalMemory p)
    (hstart : ActiveFollowerLifecycle.startRound rate.eta t state memory =
      .ok (output, outputMemory)) :
    ActiveFollowerLifecycle.localStateDomainValid state →
      ActiveFollowerLifecycle.localStateDomainValid output := by
  intro hvalid
  rcases ActiveFollowerLifecycle.startRound_frame rate.eta t state output
      memory outputMemory hstart with
    ⟨_, hS, hdelta, hbacklog, hbatch, hbuffer, _, _⟩
  rcases hvalid with ⟨hregisters, hlog, hdecoder⟩
  rcases hregisters with ⟨hS0, hdelta0, hbacklog0⟩
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨hS ▸ hS0, hdelta ▸ hdelta0, hbacklog ▸ hbacklog0⟩
  · simpa [ActiveFollowerLifecycle.localBufferValid, hbuffer] using hlog
  · simpa [ActiveFollowerLifecycle.downDecoderStateValid, hbatch] using hdecoder

/-- A checked local state supplies the exact smaller offer-domain checks. -/
private theorem stateInputDomain_of_localStateDomainValid {p : Parameters}
    {eta : LearningRate} (state : State p eta)
    (hvalid : ActiveFollowerLifecycle.localStateDomainValid state) :
    ActiveFollowerQueueOperation.stateInputDomain state := by
  rcases hvalid with ⟨hregisters, hbuffer, _⟩
  rcases hregisters with ⟨hS, hdelta, hbacklog⟩
  rcases (localBufferValid_iff_bufferInputDomain state).mp hbuffer with
    ⟨hrecords, hkeys⟩
  refine ⟨hS, hdelta, hbacklog, ?_, ?_⟩
  · intro record hrecord
    exact ⟨(hrecords record hrecord).1, (hrecords record hrecord).2.1⟩
  · change (state.buffer.map
      (fun record => (record.calendarRound, record.pilot))).Nodup
    exact hkeys

/-- The empty-buffer representative is in the checked UP-offer input domain
whenever it has the same registers as a lifecycle-valid state. -/
private theorem emptyBufferStateInputDomain_of_localStateDomainValid {p : Parameters}
    (rate : RateInput p) (stateCode : FollowerStateCode p rate)
    (state : State p rate.eta)
    (hcode : stateCode = followerStateCode rate state)
    (hvalid : ActiveFollowerLifecycle.localStateDomainValid state) :
    ActiveFollowerQueueOperation.stateInputDomain
      (followerStateOfCode rate stateCode []) := by
  have hregisters := hvalid.1
  have hrep : followerStateOfCode rate stateCode [] = {state with buffer := []} := by
    rw [hcode]
    exact FollowerDownMeasurability.followerStateOfCode_code rate state []
  rcases hregisters with ⟨hS, hdelta, hbacklog⟩
  rw [hrep]
  unfold ActiveFollowerQueueOperation.stateInputDomain
  exact ⟨hS, hdelta, hbacklog, by simp, by simp⟩

/-- The actual checked offer and arm-choice result depend on the carried
countable state code, not on the continuous buffer fields. -/
private theorem checkedActiveFollowerArmChoice_bufferCode_eq {p : Parameters}
    (rate : RateInput p) (i : Fin (p.m - 1))
    (row : CompletePublicTable.CompleteRow p) (activation : Activation p)
    (time : ActiveCalendarTime p activation) (state : State p rate.eta)
    (hvalid : ActiveFollowerLifecycle.localStateDomainValid state) :
    FollowerActionMeasurability.checkedActiveFollowerArmChoice state i row activation
        time.1 time.2 =
      armChoiceFromStartCode rate i row activation time
        (followerStateCode rate state) := by
  have hdomain := stateInputDomain_of_localStateDomainValid state hvalid
  have hrepdomain := emptyBufferStateInputDomain_of_localStateDomainValid rate
    (followerStateCode rate state) state rfl hvalid
  have hrep : followerStateOfCode rate (followerStateCode rate state) [] =
      {state with buffer := []} :=
    FollowerDownMeasurability.followerStateOfCode_code rate state []
  let representative := followerStateOfCode rate (followerStateCode rate state) []
  have hstatus : state.status = representative.status := by simp [representative, hrep]
  have hlast : state.lastDown = representative.lastDown := by simp [representative, hrep]
  have hS : state.S = representative.S := by simp [representative, hrep]
  have hdelta : state.delta = representative.delta := by simp [representative, hrep]
  have hbacklog : state.backlog = representative.backlog := by
    simp [representative, hrep]
  have hfields : ActiveFollowerQueueOperation.upOfferFields state =
      ActiveFollowerQueueOperation.upOfferFields representative := by
    simp [ActiveFollowerQueueOperation.upOfferFields,
      ReferencePrelaunchFollower.acceptedStart, hlast, hS, hdelta, hbacklog]
  have hrepdomain' : ActiveFollowerQueueOperation.stateInputDomain representative := by
    simpa [representative] using hrepdomain
  have hoffer : ActiveFollowerQueueOperation.checkedUpOffer rate.eta i row activation
      time.1 state = ActiveFollowerQueueOperation.checkedUpOffer rate.eta i row activation
        time.1 representative := by
    by_cases hsel : ActiveFollowerQueueOperation.selectedUpRound i row activation time.1 ∧
        state.status = ActiveRoundActions.FollowerStatus.unoccupied
    · have hsel' : ActiveFollowerQueueOperation.selectedUpRound i row activation time.1 ∧
          representative.status = ActiveRoundActions.FollowerStatus.unoccupied := by
        simpa [hstatus] using hsel
      by_cases hadm : OrdinaryMessageCodec.upAdmissible
          (ReferencePrelaunchFollower.codecParams p rate.eta)
          (ActiveFollowerQueueOperation.upOfferFields state)
      · have hadm' : OrdinaryMessageCodec.upAdmissible
            (ReferencePrelaunchFollower.codecParams p rate.eta)
            (ActiveFollowerQueueOperation.upOfferFields representative) := by
          simpa [hfields] using hadm
        let record : OrdinaryMessageCodec.UpRecord
            (ReferencePrelaunchFollower.codecParams p rate.eta) :=
          ⟨ActiveFollowerQueueOperation.upOfferFields state, hadm⟩
        let record' : OrdinaryMessageCodec.UpRecord
            (ReferencePrelaunchFollower.codecParams p rate.eta) :=
          ⟨ActiveFollowerQueueOperation.upOfferFields representative, hadm'⟩
        have hrecord : record = record' := by
          apply Subtype.ext
          exact hfields
        have hleft : ActiveFollowerQueueOperation.checkedUpOffer rate.eta i row activation
            time.1 state = .offer record := by
          unfold ActiveFollowerQueueOperation.checkedUpOffer
          simp only [dite_eq_left hdomain, dite_eq_left hsel, dite_eq_left hadm]
          rfl
        have hright : ActiveFollowerQueueOperation.checkedUpOffer rate.eta i row activation
            time.1 representative = .offer record' := by
          unfold ActiveFollowerQueueOperation.checkedUpOffer
          simp only [dite_eq_left hrepdomain', dite_eq_left hsel', dite_eq_left hadm']
          rfl
        rw [hleft, hright, hrecord]
      · have hadm' : ¬ OrdinaryMessageCodec.upAdmissible
            (ReferencePrelaunchFollower.codecParams p rate.eta)
            (ActiveFollowerQueueOperation.upOfferFields representative) := by
          simpa [hfields] using hadm
        have hleft : ActiveFollowerQueueOperation.checkedUpOffer rate.eta i row activation
            time.1 state = .failure := by
          unfold ActiveFollowerQueueOperation.checkedUpOffer
          simp only [dite_eq_left hdomain, dite_eq_left hsel, dite_eq_right hadm]
        have hright : ActiveFollowerQueueOperation.checkedUpOffer rate.eta i row activation
            time.1 representative = .failure := by
          unfold ActiveFollowerQueueOperation.checkedUpOffer
          simp only [dite_eq_left hrepdomain', dite_eq_left hsel', dite_eq_right hadm']
        rw [hleft, hright]
    · have hsel' : ¬(ActiveFollowerQueueOperation.selectedUpRound i row activation time.1 ∧
          representative.status = ActiveRoundActions.FollowerStatus.unoccupied) := by
        simpa [hstatus] using hsel
      exact ActiveFollowerQueueOperation.checkedUpOffer_noOffer rate.eta i row activation
        time.1 state hdomain hsel |>.trans
          (ActiveFollowerQueueOperation.checkedUpOffer_noOffer rate.eta i row activation
            time.1 representative hrepdomain' hsel').symm
  have harm (offer : Option (OrdinaryMessageCodec.UpRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))) :
      ActiveFollowerArmChoice.followerArmChoice state row time.1 i offer =
      ActiveFollowerArmChoice.followerArmChoice representative row time.1 i offer := by
    change ActiveFollowerArmChoice.followerArmChoiceCore state (row.2 time.1) i offer =
      ActiveFollowerArmChoice.followerArmChoiceCore
        (followerStateOfCode rate (followerStateCode rate state) []) (row.2 time.1) i offer
    rw [hrep]
    simp [ActiveFollowerArmChoice.followerArmChoiceCore,
      hstatus, hlast, hS, hdelta, hbacklog,
      ActiveFollowerArmChoice.upStateDomain, ActiveFollowerArmChoice.offeredUpMatchesState,
      ReferencePrelaunchFollower.acceptedStart]
  unfold FollowerActionMeasurability.checkedActiveFollowerArmChoice
    armChoiceFromStartCode
  rw [hoffer]
  simp only [FollowerActionMeasurability.checkedActiveFollowerArmChoice]
  simp [harm]
  cases hchoice : ActiveFollowerQueueOperation.checkedUpOffer rate.eta i row activation
      time.1 representative <;>
    simp [representative]

private theorem prepare_code_of_successful_start {p : Parameters}
    (rate : RateInput p) (i : Fin (p.m - 1))
    (row : CompletePublicTable.CompleteRow p) (activation : Activation p)
    (time : ActiveCalendarTime p activation)
    (state choiceState : State p rate.eta)
    (memory choiceMemory : LocalMemory p)
    (hstart : ActiveFollowerLifecycle.startRound rate.eta time.1 state memory =
      .ok (choiceState, choiceMemory)) :
    preparedRoundCode
        (DeclaredFollowerLocalRound.prepare rate i row activation time.1 time.2
          (.ordinary state memory)) =
      match FollowerActionMeasurability.checkedActiveFollowerArmChoice
          choiceState i row activation time.1 time.2 with
      | none => fallbackPreparedRoundCode rate i
      | some arm =>
          ⟨arm, some (followerStateCode rate choiceState, localMemoryCode choiceMemory)⟩ := by
  simp only [DeclaredFollowerLocalRound.prepare, hstart]
  cases hoff : ActiveFollowerQueueOperation.checkedUpOffer rate.eta i row activation
      time.1 choiceState with
  | failure =>
      simp [FollowerActionMeasurability.checkedActiveFollowerArmChoice, hoff,
        preparedRoundCode, localConfigurationCode, fallbackPreparedRoundCode]
  | noOffer =>
      cases hchoice : ActiveFollowerArmChoice.followerArmChoice choiceState row time.1 i none
      <;> simp [FollowerActionMeasurability.checkedActiveFollowerArmChoice, hoff, hchoice,
        preparedRoundCode, localConfigurationCode, fallbackPreparedRoundCode]
  | offer offered =>
      cases hchoice : ActiveFollowerArmChoice.followerArmChoice choiceState row time.1 i
          (some offered)
      <;> simp [FollowerActionMeasurability.checkedActiveFollowerArmChoice, hoff, hchoice,
        preparedRoundCode, localConfigurationCode, fallbackPreparedRoundCode]

/-- On every branch, prepare is exactly the result of its actual start
operation followed by the accepted checked action operation. -/
private theorem prepare_eq_from_start_code {p : Parameters} (rate : RateInput p)
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (activation : Activation p) (time : ActiveCalendarTime p activation)
    (incoming : LocalConfigurationCode p rate) {n : ℕ}
    (skeleton : BufferSkeletonCode p n) (values : SavedScalarFamily n) :
    prepareRoundCodeAt rate i activation incoming skeleton row time values =
      match incoming with
      | none => fallbackPreparedRoundCode rate i
      | some (stateCode, memoryCode) =>
          preparedRoundCodeFromStartCode rate i row activation time
            (startRoundResultCodeAt rate stateCode memoryCode skeleton values time.1) := by
  cases incoming with
  | none =>
      simp [prepareRoundCodeAt, localConfigurationOfCode,
        DeclaredFollowerLocalRound.prepare, preparedRoundCode,
        localConfigurationCode, fallbackPreparedRoundCode]
  | some incomingData =>
      rcases incomingData with ⟨stateCode, memoryCode⟩
      let state := followerStateOfCode rate stateCode
        (bufferFromSkeletonAndScalars skeleton values)
      let memory := localMemoryOfCode memoryCode
      cases hstart : ActiveFollowerLifecycle.startRound rate.eta time.1 state memory with
      | error reason =>
          simp [prepareRoundCodeAt, localConfigurationOfCode,
            DeclaredFollowerLocalRound.prepare, preparedRoundCode,
            localConfigurationCode, state, memory, hstart,
            startRoundResultCodeAt, startRoundResultCode,
            preparedRoundCodeFromStartCode, fallbackPreparedRoundCode]
      | ok result =>
          cases result with
          | mk choiceState choiceMemory =>
              have hvalid : ActiveFollowerLifecycle.localStateDomainValid choiceState := by
                apply startRound_success_preserves_domain rate time.1 state choiceState
                  memory choiceMemory hstart
                by_contra hbad
                have herr : ActiveFollowerLifecycle.startRound rate.eta time.1 state memory =
                    .error .invalidLocalStateDomain := by
                  simp [ActiveFollowerLifecycle.startRound,
                    ActiveFollowerLifecycle.interruptionDecision, hbad]
                rw [herr] at hstart
                cases hstart
              have hchoice := checkedActiveFollowerArmChoice_bufferCode_eq rate i row
                activation time choiceState hvalid
              have hprepare := prepare_code_of_successful_start rate i row activation
                time state choiceState memory choiceMemory hstart
              have hstartCode : startRoundResultCodeAt rate stateCode memoryCode
                  skeleton values time.1 =
                .success (followerStateCode rate choiceState)
                  (localMemoryCode choiceMemory) := by
                simp [startRoundResultCodeAt, startRoundResultCode, state, memory, hstart]
              simp [prepareRoundCodeAt, localConfigurationOfCode,
                state, memory, hprepare, hchoice, hstartCode,
                preparedRoundCodeFromStartCode, fallbackPreparedRoundCode,
                armChoiceFromStartCode]

/-- Measurability of the actual checked action stage after a coded successful
start result, using the accepted row-facing arm-choice theorem. -/
private theorem measurable_preparedRoundCodeFromStartCode {p : Parameters}
    (rate : RateInput p) (i : Fin (p.m - 1)) (activation : Activation p)
    (time : ActiveCalendarTime p activation) :
    Measurable (fun input : (CompletePublicTable.CompleteRow p) ×
        (StartRoundResultCode p rate) =>
      preparedRoundCodeFromStartCode rate i input.1 activation time input.2) := by
  apply measurable_from_prod_countable_left
  intro startCode
  cases startCode with
  | failure reason => exact measurable_const
  | success stateCode memoryCode =>
      let state := followerStateOfCode rate stateCode []
      have hchoice := FollowerActionMeasurability.measurable_checkedActiveFollowerArmChoice
        state i activation time.1 time.2
      let encodeArm : Option (Fin p.K) → PreparedRoundCode p rate
        | none => fallbackPreparedRoundCode rate i
        | some arm => ⟨arm, some (stateCode, memoryCode)⟩
      have hencode : Measurable encodeArm := measurable_of_finite encodeArm
      have hEq :
          (fun row : CompletePublicTable.CompleteRow p =>
            preparedRoundCodeFromStartCode rate i row activation time
              (.success stateCode memoryCode)) =
          fun row => encodeArm
            (FollowerActionMeasurability.checkedActiveFollowerArmChoice state i row
              activation time.1 time.2) := by
        funext row
        rfl
      rw [hEq]
      exact hencode.comp hchoice

/-- Joint measurability of the actual prepare arm and prepared-configuration
code in the complete row, genuine active calendar-time subtype, and original
saved scalar family. The row and active-time data remain in the reconstructed
PreparedRound unchanged. -/
theorem measurable_prepareRoundCodeAt {p : Parameters} (rate : RateInput p)
    (i : Fin (p.m - 1)) (activation : Activation p)
    (incoming : LocalConfigurationCode p rate) {n : ℕ}
    (skeleton : BufferSkeletonCode p n) :
    Measurable (fun input :
      (CompletePublicTable.CompleteRow p × SavedScalarFamily n) ×
          ActiveCalendarTime p activation =>
      prepareRoundCodeAt rate i activation incoming skeleton
        input.1.1 input.2 input.1.2) := by
  apply measurable_from_prod_countable_left
  intro time
  cases incoming with
  | none =>
      have hEq :
          (fun input : CompletePublicTable.CompleteRow p × SavedScalarFamily n =>
            prepareRoundCodeAt rate i activation none skeleton input.1 time input.2) =
          fun _ => fallbackPreparedRoundCode rate i := by
        funext input
        simp [prepareRoundCodeAt, localConfigurationOfCode,
          DeclaredFollowerLocalRound.prepare, preparedRoundCode,
          localConfigurationCode, fallbackPreparedRoundCode]
      rw [hEq]
      exact measurable_const
  | some incomingData =>
      rcases incomingData with ⟨stateCode, memoryCode⟩
      have hstartFull := measurable_startRoundResultCodeAt rate stateCode memoryCode
        skeleton
      have hstart : Measurable (fun values : SavedScalarFamily n =>
          startRoundResultCodeAt rate stateCode memoryCode skeleton values time.1) :=
        hstartFull.comp (Measurable.prodMk measurable_id measurable_const)
      have hfrom := measurable_preparedRoundCodeFromStartCode rate i activation time
      have hpair : Measurable (fun input :
          CompletePublicTable.CompleteRow p × SavedScalarFamily n =>
          (input.1, startRoundResultCodeAt rate stateCode memoryCode skeleton
            input.2 time.1)) :=
        Measurable.prodMk measurable_fst (hstart.comp measurable_snd)
      have hEq :
          (fun input : CompletePublicTable.CompleteRow p × SavedScalarFamily n =>
            prepareRoundCodeAt rate i activation (some (stateCode, memoryCode))
              skeleton input.1 time input.2) =
          fun input => preparedRoundCodeFromStartCode rate i input.1 activation time
            (startRoundResultCodeAt rate stateCode memoryCode skeleton input.2 time.1) := by
        funext input
        exact prepare_eq_from_start_code rate i input.1 activation time
          (some (stateCode, memoryCode)) skeleton input.2
      rw [hEq]
      exact hfrom.comp hpair


end Bandits.Support.FollowerLifecycleMeasurability

end
