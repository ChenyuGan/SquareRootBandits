/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ActiveFollowerQueueOperation
public import Bandits.Support.DeclaredFollowerLocalRound
public import Bandits.Support.FollowerDownJointMeasurability

/-!
# Joint measurability of the existing occupied follower service

This module measures the existing `checkedService` and the occupied branch of
`recordOrServiceThenDown`. It consumes the actual queue operation and the
accepted follower state/buffer encodings. Its continuous inputs retain the
complete row and the original finite product of saved observation/thinning
scalars; only countable result codes receive a discrete measurable space.

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:151-174`,
`sources/zip4/manuscript/05_binary_transport.tex:352-393`,
`sources/zip4/manuscript/06_interruptions.tex:256-269`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:8-14`.
This is a local operation result only. It supplies no physical feedback
provenance, assignment ownership, history freshness, recording law, reachable
queue envelope, or source-facing regret closure.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.FollowerServiceMeasurability

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.CompletePublicTable
open Bandits.Support.ContinuousControlSlice
open Bandits.Support.ContinuousLearningRows
open Bandits.Support.PublicDiscreteDraws
open Bandits.Support.CanonicalRecordingSlice
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.OrdinaryMessageCodec
open Bandits.Support.SparseCalendarReplay
open Bandits.Support.PrelaunchBufferRecovery
open Bandits.Support.ActiveFollowerQueueOperation
open Bandits.Support.ActiveFollowerDownAcceptance
open Bandits.Support.FollowerDownMeasurability
open Bandits.Support.FollowerDownJointMeasurability
open Bandits.Support.DeclaredFollowerLocalRound

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ActiveFollowerDownAcceptance.RateInput
abbrev JointInput (p : Parameters) (n : ℕ) :=
  FollowerDownJointMeasurability.DownJointInput p n

theorem rateSourceCap_forService {p : Parameters} (rate : RateInput p) :
    ActiveFollowerQueueOperation.sourceRateCapped p rate.eta := by
  simpa only [ActiveFollowerQueueOperation.sourceRateCapped] using rate.sourceCap

/-- The countable discrete service output code records failure or every
successful value field: the exact arrival, service, and the existing discrete
follower-state code. The continuous buffer is reconstructed from its original
unchanged input. -/
inductive ServiceResultCode (p : Parameters) (rate : RateInput p) where
  | failure
  | success (arrival service : ℕ) (output : FollowerDownMeasurability.FollowerStateCode p rate)
  deriving Countable

instance serviceResultCodeMeasurableSpace (p : Parameters) (rate : RateInput p) :
    MeasurableSpace (ServiceResultCode p rate) := ⊤

/-- Forget only the proof fields of the actual checked result. -/
def encodeServiceResult {p : Parameters} (rate : RateInput p)
    {i : Fin (p.m - 1)} {row : CompleteRow p} {activation : Activation p}
    {t : Fin p.T} {observation : Observation p}
    {state : ReferencePrelaunchFollower.State p rate.eta}
    (result : ActiveFollowerQueueOperation.ServiceResult p rate.eta rate.n i row
      activation t observation state) : ServiceResultCode p rate :=
  match result with
  | .failure => .failure
  | .success success =>
      .success success.arrival success.service
        (FollowerDownMeasurability.followerStateCode rate success.output)

/-- Reconstruct all successful data from the code and the original buffer. -/
def reconstructServiceResultCode {p : Parameters} (rate : RateInput p)
    (originalBuffer : List (SparseCalendarRecord p.K))
    (code : ServiceResultCode p rate) :
    Option (ReferencePrelaunchFollower.State p rate.eta × ℕ × ℕ) :=
  match code with
  | .failure => none
  | .success arrival service output =>
      some (FollowerDownMeasurability.followerStateOfCode rate output originalBuffer,
        arrival, service)

/-- Every successful proof-carrying result is recovered exactly once its
unchanged buffer is supplied; the erased fields were propositions only. -/
theorem reconstruct_encodeServiceResult_success {p : Parameters}
    (rate : RateInput p) (originalBuffer : List (SparseCalendarRecord p.K))
    {i : Fin (p.m - 1)} {row : CompleteRow p} {activation : Activation p}
    {t : Fin p.T} {observation : Observation p}
    {state : ReferencePrelaunchFollower.State p rate.eta}
    (success : ActiveFollowerQueueOperation.ServiceSuccess p rate.eta rate.n i row
      activation t observation state)
    (hbuffer : success.output.buffer = originalBuffer) :
    reconstructServiceResultCode rate originalBuffer
        (encodeServiceResult rate (.success success)) =
      some (success.output, success.arrival, success.service) := by
  simp only [encodeServiceResult, reconstructServiceResultCode]
  rw [FollowerDownMeasurability.followerStateOfCode_code_eq rate success.output
    originalBuffer hbuffer]

theorem encodeServiceResult_failure {p : Parameters} (rate : RateInput p)
    {i : Fin (p.m - 1)} {row : CompleteRow p} {activation : Activation p}
    {t : Fin p.T} {observation : Observation p}
    {state : ReferencePrelaunchFollower.State p rate.eta} :
    encodeServiceResult rate
      (ActiveFollowerQueueOperation.ServiceResult.failure :
        ActiveFollowerQueueOperation.ServiceResult p rate.eta rate.n i row activation t
          observation state) = .failure := rfl

theorem encodeServiceResult_success_projection {p : Parameters}
    (rate : RateInput p) {i : Fin (p.m - 1)} {row : CompleteRow p}
    {activation : Activation p} {t : Fin p.T} {observation : Observation p}
    {state : ReferencePrelaunchFollower.State p rate.eta}
    (success : ActiveFollowerQueueOperation.ServiceSuccess p rate.eta rate.n i row
      activation t observation state) :
    encodeServiceResult rate (.success success) =
      .success success.arrival success.service
        (FollowerDownMeasurability.followerStateCode rate success.output) := rfl

/-- The source's literal floor on the original quantized-feedback carrier is
Borel measurable. -/
theorem measurable_sourceArrivalFloor {p : Parameters} (eta : LearningRate)
    (M : DownRecord (ReferencePrelaunchFollower.codecParams p eta)) :
    Measurable (fun y : Observation p =>
      ActiveFollowerQueueOperation.sourceArrivalFloor eta M y) := by
  have hy : Measurable (fun y : Observation p => y.val.1) :=
    measurable_subtype_coe.comp (measurable_subtype_coe.comp measurable_id)
  have hbase : Measurable (fun y : Observation p =>
      (D p : ℝ) * eta.val * y.val.1) := by
    simpa only [Pi.mul_apply, ← mul_assoc] using
      (hy.const_mul eta.val).const_mul (D p : ℝ)
  have hscaled : Measurable (fun y : Observation p =>
      ((D p : ℝ) * eta.val * y.val.1) *
        (OrdinaryMessageCodec.dyadicRate M.val.h)⁻¹) :=
    hbase.mul_const (OrdinaryMessageCodec.dyadicRate M.val.h)⁻¹
  have hfloor : Measurable (fun y : Observation p =>
      Nat.floor (((D p : ℝ) * eta.val * y.val.1) *
        (OrdinaryMessageCodec.dyadicRate M.val.h)⁻¹)) :=
    Nat.measurable_floor.comp hscaled
  simpa only [ActiveFollowerQueueOperation.sourceArrivalFloor, div_eq_mul_inv] using hfloor

/-- The finite source feedback index selects the actual quantized observation;
its source floor remains the same literal floor. -/
def feedbackObservation {p : Parameters} (q : Fin (D p + 1)) : Observation p :=
  FollowerDownMeasurability.feedbackAtGrid p q

theorem measurable_feedbackSourceFloor {p : Parameters} (eta : LearningRate)
    (M : DownRecord (ReferencePrelaunchFollower.codecParams p eta)) :
    Measurable (fun q : Fin (D p + 1) =>
      ActiveFollowerQueueOperation.sourceArrivalFloor eta M (feedbackObservation q)) :=
  measurable_sourceArrivalFloor eta M |>.comp (measurable_feedbackAtGrid p)

/-- A finite signature of the exact current source read. The gate bit is formed
from DATA, recorder source, the non-owner pilot mask, and the inclusive current
thinning test on the same original row slice. -/
structure ServiceRead (p : Parameters) where
  time : Fin p.T
  feedback : Fin (D p + 1)
  gate : Bool
  deriving DecidableEq, Fintype, Countable

instance serviceReadMeasurableSpace (p : Parameters) : MeasurableSpace (ServiceRead p) := ⊤

noncomputable def recorderGateBit {p : Parameters} (eta : LearningRate)
    (i : Fin (p.m - 1)) (row : CompleteRow p) (t : Fin p.T)
    (M : DownRecord (ReferencePrelaunchFollower.codecParams p eta)) : Bool := by
  classical
  exact decide (ActiveFollowerQueueOperation.recorderGate eta i row t M)

private theorem measurable_finIndex_eval {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] (n : ℕ) (f : Fin n → α → β)
    (hf : ∀ j, Measurable (f j)) :
    Measurable (fun z : α × Fin n => f z.2 z.1) := by
  intro s hs
  have hpre : (fun z : α × Fin n => f z.2 z.1) ⁻¹' s =
      ⋃ j : Fin n, {z | z.2 = j} ∩ {z | f j z.1 ∈ s} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff,
      Set.mem_ofPred_eq]
    constructor
    · intro hz
      exact ⟨z.2, rfl, hz⟩
    · rintro ⟨j, hj, hz⟩
      rw [hj]
      exact hz
  rw [hpre]
  apply MeasurableSet.iUnion
  intro j
  have hindex : MeasurableSet {z : α × Fin n | z.2 = j} :=
    (measurableSet_singleton j).preimage measurable_snd
  have hvalue : MeasurableSet {z : α × Fin n | f j z.1 ∈ s} :=
    ((hf j).comp measurable_fst) hs
  exact hindex.inter hvalue

/-- The actual gate is a measurable event in one complete-row time slice. -/
theorem measurableSet_recorderGateAt {p : Parameters} (eta : LearningRate)
    (i : Fin (p.m - 1)) (t : Fin p.T)
    (M : DownRecord (ReferencePrelaunchFollower.codecParams p eta)) :
    MeasurableSet {row : CompleteRow p |
      ActiveFollowerQueueOperation.recorderGate eta i row t M} := by
  have hslice : Measurable (fun row : CompleteRow p => (row.2 t).1) := by
    change Measurable
      (ContinuousLearningRows.sliceAt t ∘ CompletePublicTable.completeRowLearning p)
    exact (ContinuousLearningRows.measurable_sliceAt t).comp
      (CompletePublicTable.measurable_completeRowLearning p)
  have hcanonical := CanonicalRecordingSlice.measurableSet_deterministicOwnedRecordingGate
    p.two_le_m p.m_lt_K (K_pos p) (PublicDiscreteDraws.followerPlayer p.two_le_m i)
    (PrelaunchBufferRecovery.downArm eta M)
    (ActiveFollowerQueueOperation.thinningProbability eta M)
  have hset : {row : CompleteRow p |
      ActiveFollowerQueueOperation.recorderGate eta i row t M} =
      (fun row : CompleteRow p => (row.2 t).1) ⁻¹'
        {slice : ContinuousControlSlice.Slice p.m p.K |
          CanonicalRecordingSlice.deterministicOwnedRecordingGate p.two_le_m p.m_lt_K
            (K_pos p) (PublicDiscreteDraws.followerPlayer p.two_le_m i)
            (PrelaunchBufferRecovery.downArm eta M)
            (ActiveFollowerQueueOperation.thinningProbability eta M) slice} := by
    ext row
    simp [ActiveFollowerQueueOperation.recorderGate,
      CanonicalRecordingSlice.deterministicOwnedRecordingGate]
  rw [hset]
  exact hcanonical.preimage hslice

/-- The gate bit is the exact source predicate, not a separately supplied
arrival or threshold. -/
theorem measurable_recorderGateBitJoint {p : Parameters} (eta : LearningRate)
    (i : Fin (p.m - 1)) (M : DownRecord (ReferencePrelaunchFollower.codecParams p eta)) :
    Measurable (fun rt : CompleteRow p × Fin p.T =>
      recorderGateBit eta i rt.1 rt.2 M) := by
  classical
  have hAt : ∀ t : Fin p.T, Measurable (fun row : CompleteRow p =>
      recorderGateBit eta i row t M) := by
    intro t
    apply FollowerDownMeasurability.measurable_of_countable_fibers
    intro bit
    cases bit with
    | false =>
        have hset : {row : CompleteRow p |
            recorderGateBit eta i row t M = false} =
            {row | ActiveFollowerQueueOperation.recorderGate eta i row t M}ᶜ := by
          ext row
          simp [recorderGateBit]
        rw [hset]
        exact (measurableSet_recorderGateAt eta i t M).compl
    | true =>
        have hset : {row : CompleteRow p |
            recorderGateBit eta i row t M = true} =
            {row | ActiveFollowerQueueOperation.recorderGate eta i row t M} := by
          ext row
          simp [recorderGateBit]
        rw [hset]
        exact measurableSet_recorderGateAt eta i t M
  simpa only [Function.comp_def] using
    measurable_finIndex_eval p.T
      (fun t row => recorderGateBit eta i row t M) hAt

/-- The literal actual raw arrival, with row, time, finite feedback, mask, and
current thinning threshold all read from the same original row. -/
def rawArrivalFromServiceRead {p : Parameters} (eta : LearningRate)
    (M : DownRecord (ReferencePrelaunchFollower.codecParams p eta))
    (read : ServiceRead p) : ℕ :=
  if read.gate then
    ActiveFollowerQueueOperation.sourceArrivalFloor eta M
      (feedbackObservation read.feedback)
  else 0

/-- The buffer length is an irrelevant index here; this polymorphic variant
lets the same original product input carry the actual saved scalar family. -/
def recorderReadForDownAt {p : Parameters} {n : ℕ} (eta : LearningRate)
    (i : Fin (p.m - 1)) (M : DownRecord (ReferencePrelaunchFollower.codecParams p eta))
    (x : JointInput p n) : ServiceRead p := by
  classical
  exact ⟨FollowerDownJointMeasurability.jointTime x,
    FollowerDownJointMeasurability.jointFeedbackIndex x,
    recorderGateBit eta i
      (FollowerDownJointMeasurability.jointRow x)
      (FollowerDownJointMeasurability.jointTime x) M⟩

theorem measurable_recorderReadForDownAt {p : Parameters} {n : ℕ}
    (eta : LearningRate) (i : Fin (p.m - 1))
    (M : DownRecord (ReferencePrelaunchFollower.codecParams p eta)) :
    Measurable (recorderReadForDownAt eta i M : JointInput p n → ServiceRead p) := by
  classical
  have hrowTime : Measurable (fun x : JointInput p n =>
      (FollowerDownJointMeasurability.jointRow x,
        FollowerDownJointMeasurability.jointTime x)) :=
    (measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk
      (measurable_snd.comp (measurable_fst.comp measurable_fst))
  have htime : Measurable (FollowerDownJointMeasurability.jointTime :
      JointInput p n → Fin p.T) :=
    (measurable_snd.comp measurable_fst).comp measurable_fst
  have hfeedback : Measurable (FollowerDownJointMeasurability.jointFeedbackIndex :
      JointInput p n → Fin (D p + 1)) := measurable_snd.comp measurable_fst
  have hgate : Measurable (fun x : JointInput p n =>
      recorderGateBit eta i
        (FollowerDownJointMeasurability.jointRow x)
        (FollowerDownJointMeasurability.jointTime x) M) :=
    (measurable_recorderGateBitJoint eta i M).comp hrowTime
  apply FollowerDownMeasurability.measurable_of_countable_fibers
  intro read
  have hset : {x : JointInput p n | recorderReadForDownAt eta i M x = read} =
      {x | FollowerDownJointMeasurability.jointTime x = read.time} ∩
        ({x | FollowerDownJointMeasurability.jointFeedbackIndex x = read.feedback} ∩
          {x | recorderGateBit eta i (FollowerDownJointMeasurability.jointRow x)
            (FollowerDownJointMeasurability.jointTime x) M = read.gate}) := by
    ext x
    cases read
    simp [recorderReadForDownAt]
  rw [hset]
  exact (htime (measurableSet_singleton read.time)).inter
    ((hfeedback (measurableSet_singleton read.feedback)).inter
      (hgate (measurableSet_singleton read.gate)))

theorem rawArrivalFromServiceRead_eq_actual {p : Parameters} {n : ℕ}
    (eta : LearningRate) (i : Fin (p.m - 1))
    (M : DownRecord (ReferencePrelaunchFollower.codecParams p eta))
    (x : JointInput p n) :
    rawArrivalFromServiceRead eta M (recorderReadForDownAt eta i M x) =
      ActiveFollowerQueueOperation.rawArrival eta i
        (FollowerDownJointMeasurability.jointRow x)
        (FollowerDownJointMeasurability.jointTime x) M
        (feedbackObservation (FollowerDownJointMeasurability.jointFeedbackIndex x)) := by
  classical
  rw [ActiveFollowerQueueOperation.rawArrival_eq_sourceFormula]
  let gate := ActiveFollowerQueueOperation.recorderGate eta i
    (FollowerDownJointMeasurability.jointRow x)
    (FollowerDownJointMeasurability.jointTime x) M
  by_cases hgate : gate
  · simp [rawArrivalFromServiceRead, recorderReadForDownAt, recorderGateBit,
      gate, hgate]
  · simp [rawArrivalFromServiceRead, recorderReadForDownAt, recorderGateBit,
      gate, hgate]

/-- Joint measurability of the actual source raw arrival over the whole
complete row/time/finite-feedback/original-saved-scalar product. -/
theorem measurable_rawArrival_joint {p : Parameters} {n : ℕ}
    (eta : LearningRate) (i : Fin (p.m - 1))
    (M : DownRecord (ReferencePrelaunchFollower.codecParams p eta)) :
    Measurable (fun x : JointInput p n =>
      ActiveFollowerQueueOperation.rawArrival eta i
        (FollowerDownJointMeasurability.jointRow x)
        (FollowerDownJointMeasurability.jointTime x) M
        (feedbackObservation (FollowerDownJointMeasurability.jointFeedbackIndex x))) := by
  have hread := measurable_recorderReadForDownAt (n := n) eta i M
  have hcode : Measurable (rawArrivalFromServiceRead eta M : ServiceRead p → ℕ) :=
    measurable_of_finite _
  have hfactor :
      (fun x : JointInput p n => ActiveFollowerQueueOperation.rawArrival eta i
        (FollowerDownJointMeasurability.jointRow x)
        (FollowerDownJointMeasurability.jointTime x) M
        (feedbackObservation (FollowerDownJointMeasurability.jointFeedbackIndex x))) =
      (rawArrivalFromServiceRead eta M ∘ recorderReadForDownAt (n := n) eta i M) := by
    funext x
    exact (rawArrivalFromServiceRead_eq_actual eta i M x).symm
  rw [hfactor]
  exact hcode.comp hread

/-- The local service amount is a measurable function of its actual natural
arrival; the natural carrier has its discrete sigma algebra. -/
theorem measurable_localService (n backlog : ℕ) :
    Measurable (fun arrival : ℕ => ActiveFollowerQueueOperation.localService n backlog arrival) :=
  Measurable.of_discrete

/-- The exact output-domain decision, including invalid arrivals and failed
score/backlog bounds, is measurable as a function of the actual arrival. -/
noncomputable def outputDomainDecision {p : Parameters} (n : ℕ)
    {eta : LearningRate} (state : ReferencePrelaunchFollower.State p eta)
    (arrival : ℕ) : Bool := by
  classical
  exact decide (ActiveFollowerQueueOperation.outputDomain n state arrival
    (ActiveFollowerQueueOperation.localService n state.backlog arrival))

theorem measurable_outputDomainDecision {p : Parameters} (n : ℕ)
    {eta : LearningRate} (state : ReferencePrelaunchFollower.State p eta) :
    Measurable (outputDomainDecision n state) :=
  Measurable.of_discrete

theorem measurable_localService_joint {p : Parameters} {n : ℕ}
    (rate : RateInput p) (i : Fin (p.m - 1))
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (M : DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)) :
    Measurable (fun x : JointInput p n =>
      ActiveFollowerQueueOperation.localService rate.n state.backlog
        (ActiveFollowerQueueOperation.rawArrival rate.eta i
          (FollowerDownJointMeasurability.jointRow x)
          (FollowerDownJointMeasurability.jointTime x) M
          (feedbackObservation (FollowerDownJointMeasurability.jointFeedbackIndex x)))) :=
  (measurable_localService rate.n state.backlog).comp
    (measurable_rawArrival_joint rate.eta i M)

theorem measurable_outputDomainDecision_joint {p : Parameters} {n : ℕ}
    (rate : RateInput p) (i : Fin (p.m - 1))
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (M : DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)) :
    Measurable (fun x : JointInput p n =>
      outputDomainDecision rate.n state
        (ActiveFollowerQueueOperation.rawArrival rate.eta i
          (FollowerDownJointMeasurability.jointRow x)
          (FollowerDownJointMeasurability.jointTime x) M
          (feedbackObservation (FollowerDownJointMeasurability.jointFeedbackIndex x)))) :=
  (measurable_outputDomainDecision rate.n state).comp
    (measurable_rawArrival_joint rate.eta i M)

/-- Exact source result code obtained from the actual checked operation after
its raw arrival has been computed. Every input and output-domain check is
retained in this code-valued projection. -/
def serviceResultCodeFromArrival {p : Parameters} (rate : RateInput p)
    (_i : Fin (p.m - 1)) (activation : Activation p)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (t : Fin p.T) (arrival : ℕ) : ServiceResultCode p rate := by
  classical
  exact if ActiveFollowerQueueOperation.stateInputDomain state then
    if state.status = .unoccupied then
      .success 0 0 (FollowerDownMeasurability.followerStateCode rate state)
    else if activation.val ≤ t.val + 1 then
      match state.lastDown with
      | none => .failure
      | some M =>
          if ActiveFollowerQueueOperation.thinningProbabilityDomain rate.eta M then
            let service := ActiveFollowerQueueOperation.localService rate.n state.backlog arrival
            let output := ActiveFollowerQueueOperation.serviceOutput rate.n state arrival
            if ActiveFollowerQueueOperation.outputDomain rate.n state arrival service then
              .success arrival service (FollowerDownMeasurability.followerStateCode rate output)
            else .failure
          else .failure
    else .failure
  else .failure

theorem encode_checkedService_eq_fromArrival {p : Parameters}
    (rate : RateInput p) (i : Fin (p.m - 1)) (row : CompleteRow p)
    (activation : Activation p) (t : Fin p.T) (observation : Observation p)
    (state : ReferencePrelaunchFollower.State p rate.eta) :
    encodeServiceResult rate
        (ActiveFollowerQueueOperation.checkedService rate.eta (rateSourceCap_forService rate) rate.n
          rate.n_scale i row activation t observation state) =
      serviceResultCodeFromArrival rate i activation state t
        (match state.lastDown with
        | none => 0
        | some M => ActiveFollowerQueueOperation.rawArrival rate.eta i row t M observation) := by
  classical
  cases state with
  | mk lastDown S delta backlog status downBatch buffer initializationFailure =>
      let s : ReferencePrelaunchFollower.State p rate.eta :=
        ⟨lastDown, S, delta, backlog, status, downBatch, buffer, initializationFailure⟩
      change encodeServiceResult rate
          (ActiveFollowerQueueOperation.checkedService rate.eta (rateSourceCap_forService rate)
            rate.n rate.n_scale i row activation t observation s) =
        serviceResultCodeFromArrival rate i activation s t
          (match s.lastDown with
          | none => 0
          | some M => ActiveFollowerQueueOperation.rawArrival rate.eta i row t M observation)
      by_cases hdomain : ActiveFollowerQueueOperation.stateInputDomain s
      · cases status with
        | unoccupied =>
            simp [ActiveFollowerQueueOperation.checkedService, encodeServiceResult,
              serviceResultCodeFromArrival, s, hdomain]
        | pending =>
            cases lastDown with
            | none =>
                simp [ActiveFollowerQueueOperation.checkedService, encodeServiceResult,
                  serviceResultCodeFromArrival, s, hdomain]
            | some down =>
                simp [ActiveFollowerQueueOperation.checkedService, encodeServiceResult,
                  serviceResultCodeFromArrival, s, hdomain]
                split_ifs <;> rfl
        | released =>
            cases lastDown with
            | none =>
                simp [ActiveFollowerQueueOperation.checkedService, encodeServiceResult,
                  serviceResultCodeFromArrival, s, hdomain]
            | some down =>
                simp [ActiveFollowerQueueOperation.checkedService, encodeServiceResult,
                  serviceResultCodeFromArrival, s, hdomain]
                split_ifs <;> rfl
      · simp [ActiveFollowerQueueOperation.checkedService, encodeServiceResult,
          serviceResultCodeFromArrival, s, hdomain]

theorem replaceBufferScalars_mapBufferKey {p : Parameters}
    (buffer : List (SparseCalendarRecord p.K))
    (values : SavedScalarFamily buffer.length) :
    (FollowerDownMeasurability.replaceBufferScalars buffer values).map
        ActiveFollowerQueueOperation.bufferKey =
      buffer.map ActiveFollowerQueueOperation.bufferKey := by
  apply List.ext_get
  · simp [FollowerDownMeasurability.replaceBufferScalars]
  · intro j hj₁ hj₂
    simp [FollowerDownMeasurability.replaceBufferScalars,
      ActiveFollowerQueueOperation.bufferKey]

/-- Replacing saved continuous fields changes neither the appendix-A domain
check nor any code of an existing discrete register. -/
theorem stateInputDomain_adaptedInputState {p : Parameters} (rate : RateInput p)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (values : SavedScalarFamily state.buffer.length) :
    ActiveFollowerQueueOperation.stateInputDomain
        (FollowerDownMeasurability.adaptedInputState rate state values) =
      ActiveFollowerQueueOperation.stateInputDomain state := by
  cases state with
  | mk lastDown S delta backlog status downBatch buffer initializationFailure =>
      have hround :
          (∀ record ∈ FollowerDownMeasurability.replaceBufferScalars buffer values,
            1 ≤ record.calendarRound ∧ record.calendarRound ≤ p.T) ↔
          (∀ record ∈ buffer, 1 ≤ record.calendarRound ∧ record.calendarRound ≤ p.T) := by
        simp only [FollowerDownMeasurability.replaceBufferScalars]
        rw [List.forall_mem_ofFn_iff, List.forall_mem_iff_get]
        simp
      have hkeys := replaceBufferScalars_mapBufferKey buffer values
      apply propext
      simp only [ActiveFollowerQueueOperation.stateInputDomain,
        FollowerDownMeasurability.adaptedInputState]
      rw [hround, hkeys]

theorem followerStateCode_adaptedInputState {p : Parameters} (rate : RateInput p)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (values : SavedScalarFamily state.buffer.length) :
    FollowerDownMeasurability.followerStateCode rate
        (FollowerDownMeasurability.adaptedInputState rate state values) =
      FollowerDownMeasurability.followerStateCode rate state := by
  cases state
  rfl

theorem serviceOutput_bufferReplace {p : Parameters} {eta : LearningRate}
    (n : ℕ) (state : ReferencePrelaunchFollower.State p eta)
    (buffer : List (SparseCalendarRecord p.K)) (arrival : ℕ) :
    ActiveFollowerQueueOperation.serviceOutput n {state with buffer := buffer} arrival =
      {ActiveFollowerQueueOperation.serviceOutput n state arrival with buffer := buffer} := by
  cases state with
  | mk lastDown S delta backlog status downBatch oldBuffer initializationFailure =>
      cases status <;>
        simp [ActiveFollowerQueueOperation.serviceOutput,
          ActiveFollowerQueueOperation.serviceUpdate,
          ActiveFollowerQueueOperation.localService,
          ActiveRoundActions.FollowerStatus.occupied]

theorem followerStateCode_serviceOutput_adapted {p : Parameters} (rate : RateInput p)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (values : SavedScalarFamily state.buffer.length) (arrival : ℕ) :
    FollowerDownMeasurability.followerStateCode rate
        (ActiveFollowerQueueOperation.serviceOutput rate.n
          (FollowerDownMeasurability.adaptedInputState rate state values) arrival) =
      FollowerDownMeasurability.followerStateCode rate
        (ActiveFollowerQueueOperation.serviceOutput rate.n state arrival) := by
  change FollowerDownMeasurability.followerStateCode rate
      (ActiveFollowerQueueOperation.serviceOutput rate.n
        {state with buffer := FollowerDownMeasurability.replaceBufferScalars state.buffer values}
        arrival) = _
  rw [serviceOutput_bufferReplace rate.n state
    (FollowerDownMeasurability.replaceBufferScalars state.buffer values) arrival]
  simp [FollowerDownMeasurability.followerStateCode]

theorem serviceResultCodeFromArrival_adaptedInputState {p : Parameters}
    (rate : RateInput p) (i : Fin (p.m - 1)) (activation : Activation p)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (values : SavedScalarFamily state.buffer.length) (t : Fin p.T) (arrival : ℕ) :
    serviceResultCodeFromArrival rate i activation
        (FollowerDownMeasurability.adaptedInputState rate state values) t arrival =
      serviceResultCodeFromArrival rate i activation state t arrival := by
  classical
  unfold serviceResultCodeFromArrival
  rw [stateInputDomain_adaptedInputState]
  by_cases hdomain : ActiveFollowerQueueOperation.stateInputDomain state
  · simp only [hdomain]
    have hregs := FollowerDownMeasurability.adaptedInputState_registers rate state values
    rcases hregs with ⟨hdown, hS, hdelta, hbacklog, hstatus, hbatch, hmarker⟩
    have houtputDomain (service : ℕ) :
        ActiveFollowerQueueOperation.outputDomain rate.n
          (FollowerDownMeasurability.adaptedInputState rate state values) arrival service =
        ActiveFollowerQueueOperation.outputDomain rate.n state arrival service := by
      unfold ActiveFollowerQueueOperation.outputDomain
      rw [hS, hbacklog]
    simp only [hstatus, hdown, hbacklog, houtputDomain,
      followerStateCode_adaptedInputState,
      followerStateCode_serviceOutput_adapted]
  · simp [hdomain]

/-- Actual service input state: the original finite scalar family is installed
in the existing buffer adapter, with all discrete registers held fixed. -/
def serviceJointState {p : Parameters} (rate : RateInput p)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (x : JointInput p state.buffer.length) : ReferencePrelaunchFollower.State p rate.eta :=
  FollowerDownMeasurability.adaptedInputState rate state
    (FollowerDownJointMeasurability.jointValues x)

def serviceReadForState {p : Parameters} {n : ℕ} (rate : RateInput p)
    (i : Fin (p.m - 1)) (state : ReferencePrelaunchFollower.State p rate.eta)
    (x : JointInput p n) : ServiceRead p := by
  classical
  exact match state.lastDown with
  | none => ⟨FollowerDownJointMeasurability.jointTime x,
      FollowerDownJointMeasurability.jointFeedbackIndex x, false⟩
  | some M => recorderReadForDownAt rate.eta i M x

def serviceArrivalFromRead {p : Parameters} (rate : RateInput p)
    (state : ReferencePrelaunchFollower.State p rate.eta) (read : ServiceRead p) : ℕ :=
  match state.lastDown with
  | none => 0
  | some M => rawArrivalFromServiceRead rate.eta M read

def serviceCodeFromRead {p : Parameters} (rate : RateInput p)
    (i : Fin (p.m - 1)) (activation : Activation p)
    (state : ReferencePrelaunchFollower.State p rate.eta) (read : ServiceRead p) :
    ServiceResultCode p rate :=
  serviceResultCodeFromArrival rate i activation state read.time
    (serviceArrivalFromRead rate state read)

theorem measurable_serviceReadForState {p : Parameters} {n : ℕ}
    (rate : RateInput p) (i : Fin (p.m - 1))
    (state : ReferencePrelaunchFollower.State p rate.eta) :
    Measurable (serviceReadForState rate i state : JointInput p n → ServiceRead p) := by
  classical
  cases hlast : state.lastDown with
  | none =>
      have htime : Measurable (FollowerDownJointMeasurability.jointTime :
          JointInput p n → Fin p.T) :=
        (measurable_snd.comp measurable_fst).comp measurable_fst
      have hfeedback : Measurable (FollowerDownJointMeasurability.jointFeedbackIndex :
          JointInput p n → Fin (D p + 1)) := measurable_snd.comp measurable_fst
      apply FollowerDownMeasurability.measurable_of_countable_fibers
      intro read
      have hset : {x : JointInput p n | serviceReadForState rate i state x = read} =
          {x | FollowerDownJointMeasurability.jointTime x = read.time} ∩
            ({x | FollowerDownJointMeasurability.jointFeedbackIndex x = read.feedback} ∩
              {x | False = read.gate}) := by
        ext x
        cases read
        simp [serviceReadForState, hlast]
      rw [hset]
      exact (htime (measurableSet_singleton read.time)).inter
        ((hfeedback (measurableSet_singleton read.feedback)).inter
          (by by_cases h : read.gate <;> simp [h]))
  | some M =>
      have hread : serviceReadForState (n := n) rate i state =
          recorderReadForDownAt (n := n) rate.eta i M := by
        funext x
        simp [serviceReadForState, hlast]
      rw [hread]
      exact measurable_recorderReadForDownAt (n := n) rate.eta i M

theorem measurable_serviceCodeFromRead {p : Parameters} (rate : RateInput p)
    (i : Fin (p.m - 1)) (activation : Activation p)
    (state : ReferencePrelaunchFollower.State p rate.eta) :
    Measurable (serviceCodeFromRead rate i activation state : ServiceRead p →
      ServiceResultCode p rate) :=
  measurable_of_finite _

/-- The result code of the literal existing checked service, evaluated on the
entire row/time/feedback/saved-scalar product. -/
def checkedServiceCodeAtJoint {p : Parameters} (rate : RateInput p)
    (i : Fin (p.m - 1)) (activation : Activation p)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (x : JointInput p state.buffer.length) : ServiceResultCode p rate :=
  encodeServiceResult rate
    (ActiveFollowerQueueOperation.checkedService rate.eta (rateSourceCap_forService rate) rate.n rate.n_scale
      i (FollowerDownJointMeasurability.jointRow x) activation
      (FollowerDownJointMeasurability.jointTime x)
      (feedbackObservation (FollowerDownJointMeasurability.jointFeedbackIndex x))
      (serviceJointState rate state x))

theorem checkedServiceCodeAtJoint_eq_readFactor {p : Parameters} (rate : RateInput p)
    (i : Fin (p.m - 1)) (activation : Activation p)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (x : JointInput p state.buffer.length) :
    checkedServiceCodeAtJoint rate i activation state x =
      serviceCodeFromRead rate i activation state (serviceReadForState rate i state x) := by
  classical
  have hencode := encode_checkedService_eq_fromArrival rate i
    (FollowerDownJointMeasurability.jointRow x) activation
    (FollowerDownJointMeasurability.jointTime x)
    (feedbackObservation (FollowerDownJointMeasurability.jointFeedbackIndex x))
    (serviceJointState rate state x)
  change encodeServiceResult rate
      (ActiveFollowerQueueOperation.checkedService rate.eta (rateSourceCap_forService rate) rate.n rate.n_scale
        i (FollowerDownJointMeasurability.jointRow x) activation
        (FollowerDownJointMeasurability.jointTime x)
        (feedbackObservation (FollowerDownJointMeasurability.jointFeedbackIndex x))
        (FollowerDownMeasurability.adaptedInputState rate state
          (FollowerDownJointMeasurability.jointValues x))) = _
  dsimp [serviceJointState] at hencode
  rw [hencode]
  rw [serviceResultCodeFromArrival_adaptedInputState rate i activation state
    (FollowerDownJointMeasurability.jointValues x)]
  have hlastAdapted :=
    (FollowerDownMeasurability.adaptedInputState_registers rate state
      (FollowerDownJointMeasurability.jointValues x)).1
  rw [hlastAdapted]
  cases hlast : state.lastDown with
  | none => simp [serviceReadForState, serviceArrivalFromRead, serviceCodeFromRead, hlast]
  | some M =>
      have hread : serviceReadForState (n := state.buffer.length) rate i state x =
          recorderReadForDownAt (n := state.buffer.length) rate.eta i M x := by
        simp [serviceReadForState, hlast]
      have htime : (recorderReadForDownAt (n := state.buffer.length)
          rate.eta i M x).time = FollowerDownJointMeasurability.jointTime x := rfl
      unfold serviceCodeFromRead
      rw [hread]
      simp only [serviceArrivalFromRead, hlast]
      rw [htime, rawArrivalFromServiceRead_eq_actual rate.eta i M x]

theorem measurable_checkedServiceCodeAtJoint {p : Parameters} (rate : RateInput p)
    (i : Fin (p.m - 1)) (activation : Activation p)
    (state : ReferencePrelaunchFollower.State p rate.eta) :
    Measurable (checkedServiceCodeAtJoint rate i activation state) := by
  rw [show checkedServiceCodeAtJoint rate i activation state =
      serviceCodeFromRead rate i activation state ∘ serviceReadForState rate i state by
        funext x
        exact checkedServiceCodeAtJoint_eq_readFactor rate i activation state x]
  exact (measurable_serviceCodeFromRead rate i activation state).comp
    (measurable_serviceReadForState rate i state)

theorem measurable_checkedServiceCodeAtJoint_comp {p : Parameters}
    (rate : RateInput p) (i : Fin (p.m - 1)) (activation : Activation p)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    {Ω : Type*} [MeasurableSpace Ω] (inputs : Ω → JointInput p state.buffer.length)
    (hinputs : Measurable inputs) :
    Measurable (fun ω => checkedServiceCodeAtJoint rate i activation state (inputs ω)) :=
  (measurable_checkedServiceCodeAtJoint rate i activation state).comp hinputs

/-- Componentwise arbitrary-base form of the joint service measurability
theorem. Each map into the complete row, calendar time, finite feedback grid,
and original saved-scalar family is an explicit input. -/
theorem measurable_checkedServiceCodeAtComponents {p : Parameters}
    (rate : RateInput p) (i : Fin (p.m - 1)) (activation : Activation p)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    {Ω : Type*} [MeasurableSpace Ω]
    (row : Ω → CompleteRow p) (hrow : Measurable row)
    (time : Ω → Fin p.T) (htime : Measurable time)
    (feedback : Ω → Fin (D p + 1)) (hfeedback : Measurable feedback)
    (values : Ω → SavedScalarFamily state.buffer.length) (hvalues : Measurable values) :
    Measurable (fun ω => checkedServiceCodeAtJoint rate i activation state
      (((row ω, time ω), feedback ω), values ω)) := by
  apply measurable_checkedServiceCodeAtJoint_comp
  exact ((hrow.prodMk htime).prodMk hfeedback).prodMk hvalues

/-- The actual successful service result preserves the original continuous
buffer as well as every unrelated discrete register. -/
theorem serviceSuccess_preserves_retained_fields {p : Parameters}
    {rate : RateInput p} {i : Fin (p.m - 1)} {row : CompleteRow p}
    {activation : Activation p} {t : Fin p.T} {observation : Observation p}
    {state : ReferencePrelaunchFollower.State p rate.eta}
    (success : ActiveFollowerQueueOperation.ServiceSuccess p rate.eta rate.n i row
      activation t observation state) :
    success.output.lastDown = state.lastDown ∧
    success.output.downBatch = state.downBatch ∧
    success.output.buffer = state.buffer ∧
    success.output.status = state.status ∧
    success.output.initializationFailure = state.initializationFailure := by
  rw [success.queueUpdate]
  exact ActiveFollowerQueueOperation.serviceOutput_preserves_other_registers rate.n state
    success.arrival

theorem serviceSuccess_buffer_eq_input {p : Parameters}
    {rate : RateInput p} {i : Fin (p.m - 1)} {row : CompleteRow p}
    {activation : Activation p} {t : Fin p.T} {observation : Observation p}
    {state : ReferencePrelaunchFollower.State p rate.eta}
    (success : ActiveFollowerQueueOperation.ServiceSuccess p rate.eta rate.n i row
      activation t observation state) : success.output.buffer = state.buffer :=
  (serviceSuccess_preserves_retained_fields success).2.2.1

/-- Source-enabled unoccupied service is an exact no-op and retains its zero
arrival/service fields; invalid input domains still fail in `checkedService`. -/
theorem checkedService_unoccupied_noop {p : Parameters} (rate : RateInput p)
    (i : Fin (p.m - 1)) (row : CompleteRow p) (activation : Activation p)
    (t : Fin p.T) (observation : Observation p)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (hdomain : ActiveFollowerQueueOperation.stateInputDomain state)
    (h_unoccupied : state.status = .unoccupied) :
    ∃ success, ActiveFollowerQueueOperation.checkedService rate.eta
      (rateSourceCap_forService rate) rate.n
      rate.n_scale i row activation t observation state = .success success ∧
      success.output = state ∧ success.arrival = 0 ∧ success.service = 0 := by
  classical
  cases state with
  | mk lastDown S delta backlog status downBatch buffer initializationFailure =>
      cases status with
      | unoccupied =>
          let s : ReferencePrelaunchFollower.State p rate.eta :=
            ⟨lastDown, S, delta, backlog, .unoccupied, downBatch, buffer,
              initializationFailure⟩
          have hdomain' : ActiveFollowerQueueOperation.stateInputDomain s := by
            simpa [s] using hdomain
          let success : ActiveFollowerQueueOperation.ServiceSuccess p rate.eta rate.n i row
              activation t observation s := {
              output := s
              arrival := 0
              service := 0
              inputDomain := hdomain'
              sourceRateCap := rateSourceCap_forService rate
              naturalScale := rate.n_scale
              arrival_le_D := Nat.zero_le _
              service_le_D := Nat.zero_le _
              score_le_TD := hdomain'.1
              backlog_le_TD := hdomain'.2.2.1
              queueUpdate := by
                exact (ActiveFollowerQueueOperation.serviceOutput_unoccupied_preserves
                  rate.n s rfl 0).symm
              action := by simp [ActiveFollowerQueueOperation.serviceAction, s]
            }
          refine ⟨success, ?_, rfl, rfl, rfl⟩
          simp [ActiveFollowerQueueOperation.checkedService, hdomain', s, success]
      | pending => simp at h_unoccupied
      | released => simp at h_unoccupied

/-- A genuine typed feedback record always satisfies the literal thinning
parameter check. The checked operation still retains and executes that check. -/
theorem thinningProbabilityDomain_of_existing_record {p : Parameters}
    (eta : LearningRate) (M : DownRecord (ReferencePrelaunchFollower.codecParams p eta)) :
    ActiveFollowerQueueOperation.thinningProbabilityDomain eta M :=
  ActiveFollowerQueueOperation.thinningProbability_domain eta M

/-- The occupied local round's code keeps the actual service failure tag and,
on success, arrival, service, and every changed discrete state register. -/
inductive OccupiedRoundCode (p : Parameters) (rate : RateInput p) where
  | serviceFailure
  | success (arrival service : ℕ)
      (output : FollowerDownMeasurability.FollowerStateCode p rate)
  deriving Countable

instance occupiedRoundCodeMeasurableSpace (p : Parameters) (rate : RateInput p) :
    MeasurableSpace (OccupiedRoundCode p rate) := ⊤

def occupiedRoundCodeOfServiceCode {p : Parameters} (rate : RateInput p)
    (code : ServiceResultCode p rate) : OccupiedRoundCode p rate :=
  match code with
  | .failure => .serviceFailure
  | .success arrival service output => .success arrival service output

def occupiedRoundCodeAtJoint {p : Parameters} (rate : RateInput p)
    (i : Fin (p.m - 1)) (activation : Activation p)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (x : JointInput p state.buffer.length) : OccupiedRoundCode p rate :=
  occupiedRoundCodeOfServiceCode rate (checkedServiceCodeAtJoint rate i activation state x)

theorem measurable_occupiedRoundCodeAtJoint {p : Parameters} (rate : RateInput p)
    (i : Fin (p.m - 1)) (activation : Activation p)
    (state : ReferencePrelaunchFollower.State p rate.eta) :
    Measurable (occupiedRoundCodeAtJoint rate i activation state) :=
  (measurable_of_countable (occupiedRoundCodeOfServiceCode rate)).comp
    (measurable_checkedServiceCodeAtJoint rate i activation state)

theorem measurable_occupiedRoundCodeAtJoint_comp {p : Parameters}
    (rate : RateInput p) (i : Fin (p.m - 1)) (activation : Activation p)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    {Ω : Type*} [MeasurableSpace Ω] (inputs : Ω → JointInput p state.buffer.length)
    (hinputs : Measurable inputs) :
    Measurable (fun ω => occupiedRoundCodeAtJoint rate i activation state (inputs ω)) :=
  (measurable_occupiedRoundCodeAtJoint rate i activation state).comp hinputs

/-- Componentwise arbitrary-base form for the occupied branch code, with the
same complete-row and original-buffer scalar inputs as checked service. -/
theorem measurable_occupiedRoundCodeAtComponents {p : Parameters}
    (rate : RateInput p) (i : Fin (p.m - 1)) (activation : Activation p)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    {Ω : Type*} [MeasurableSpace Ω]
    (row : Ω → CompleteRow p) (hrow : Measurable row)
    (time : Ω → Fin p.T) (htime : Measurable time)
    (feedback : Ω → Fin (D p + 1)) (hfeedback : Measurable feedback)
    (values : Ω → SavedScalarFamily state.buffer.length) (hvalues : Measurable values) :
    Measurable (fun ω => occupiedRoundCodeAtJoint rate i activation state
      (((row ω, time ω), feedback ω), values ω)) := by
  apply measurable_occupiedRoundCodeAtJoint_comp
  exact ((hrow.prodMk htime).prodMk hfeedback).prodMk hvalues

def reconstructOccupiedRoundCode {p : Parameters} (rate : RateInput p)
    (originalBuffer : List (SparseCalendarRecord p.K)) (code : OccupiedRoundCode p rate) :
    Except RoundFailure (ReferencePrelaunchFollower.State p rate.eta) :=
  match code with
  | .serviceFailure => .error .service
  | .success _ _ output =>
      .ok (FollowerDownMeasurability.followerStateOfCode rate output originalBuffer)

theorem reconstruct_occupiedCode_success {p : Parameters} (rate : RateInput p)
    (originalBuffer : List (SparseCalendarRecord p.K))
    (arrival service : ℕ) (output : FollowerDownMeasurability.FollowerStateCode p rate) :
    reconstructOccupiedRoundCode rate originalBuffer
        (.success arrival service output) =
      .ok (FollowerDownMeasurability.followerStateOfCode rate output originalBuffer) := rfl

theorem reconstruct_occupiedCode_failure {p : Parameters} (rate : RateInput p)
    (originalBuffer : List (SparseCalendarRecord p.K)) :
    reconstructOccupiedRoundCode rate originalBuffer .serviceFailure = .error .service := rfl

/-- Under the honest occupied-at-choice guard, reconstruction of the code is
the exact actual `recordOrServiceThenDown` result, including `.service` failure. -/
theorem reconstruct_occupied_recordOrServiceThenDown {p : Parameters}
    (rate : RateInput p) (i : Fin (p.m - 1)) (row : CompleteRow p)
    (activation : Activation p) (t : Fin p.T) (hactive : activation.val ≤ t.val + 1)
    (arm : Fin p.K) (observation : Observation p)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (hoccupied : state.status ≠ .unoccupied) :
    reconstructOccupiedRoundCode rate state.buffer
        (occupiedRoundCodeOfServiceCode rate
          (encodeServiceResult rate
            (ActiveFollowerQueueOperation.checkedService rate.eta (rateSourceCap_forService rate) rate.n
              rate.n_scale i row activation t observation state))) =
      DeclaredFollowerLocalRound.recordOrServiceThenDown rate i row activation t hactive
        arm observation state := by
  rw [DeclaredFollowerLocalRound.recordOrServiceThenDown_occupied rate i row activation t
    hactive arm observation state hoccupied]
  cases hservice : ActiveFollowerQueueOperation.checkedService rate.eta (rateSourceCap_forService rate) rate.n
      rate.n_scale i row activation t observation state with
  | failure => rfl
  | success result =>
      simp only [encodeServiceResult, occupiedRoundCodeOfServiceCode,
        reconstructOccupiedRoundCode]
      exact congrArg Except.ok
        (FollowerDownMeasurability.followerStateOfCode_code_eq rate result.output
          state.buffer (serviceSuccess_buffer_eq_input result))

/-- Measurable exact reconstruction of the occupied branch for a fixed
incoming discrete register/buffer skeleton, with its original continuous
buffer scalars carried jointly in `JointInput`. -/
theorem measurable_occupiedRound_reconstruction {p : Parameters}
    (rate : RateInput p) (i : Fin (p.m - 1)) (activation : Activation p)
    (state : ReferencePrelaunchFollower.State p rate.eta) :
    Measurable (occupiedRoundCodeAtJoint rate i activation state) :=
  measurable_occupiedRoundCodeAtJoint rate i activation state

/-- A non-DATA row still performs enabled zero-arrival service for an occupied
follower; the exact zero-arrival queue update is inherited from the actual
service proof. -/
theorem occupied_nonData_service_fields {p : Parameters} (rate : RateInput p)
    (i : Fin (p.m - 1)) (row : CompleteRow p) (activation : Activation p)
    (t : Fin p.T) (observation : Observation p)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (hoccupied : state.status.occupied)
    (hslot : PublicDiscreteDraws.slotDraw (row.2 t).1 ≠ PublicDiscreteDraws.dataSlot)
    (success : ActiveFollowerQueueOperation.ServiceSuccess p rate.eta rate.n i row
      activation t observation state) :
    success.arrival = 0 ∧
    success.service = min (ActiveFollowerQueueOperation.serviceCapacity rate.n) state.backlog ∧
    success.output.S = state.S + min (ActiveFollowerQueueOperation.serviceCapacity rate.n)
      state.backlog ∧
    success.output.delta = min (ActiveFollowerQueueOperation.serviceCapacity rate.n)
      state.backlog ∧
    success.output.backlog = state.backlog -
      min (ActiveFollowerQueueOperation.serviceCapacity rate.n) state.backlog :=
  ActiveFollowerQueueOperation.serviceSuccess_nonData_update success hoccupied hslot

/-- If the actual occupied recorder gate is disabled, a successful enabled
service still applies the zero-arrival queue transition. The gate includes the
same-row DATA, source, pilot-mask, and inclusive thinning checks used by
`rawArrival`. -/
theorem occupied_sourceDisabled_service_fields {p : Parameters} (rate : RateInput p)
    (i : Fin (p.m - 1)) (row : CompleteRow p) (activation : Activation p)
    (t : Fin p.T) (observation : Observation p)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (hoccupied : state.status.occupied)
    (M : DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hlast : state.lastDown = some M)
    (hgate : ¬ ActiveFollowerQueueOperation.recorderGate rate.eta i row t M)
    (success : ActiveFollowerQueueOperation.ServiceSuccess p rate.eta rate.n i row
      activation t observation state) :
    success.arrival = 0 ∧
    success.service = min (ActiveFollowerQueueOperation.serviceCapacity rate.n) state.backlog ∧
    success.output.S = state.S + min (ActiveFollowerQueueOperation.serviceCapacity rate.n)
      state.backlog ∧
    success.output.delta = min (ActiveFollowerQueueOperation.serviceCapacity rate.n)
      state.backlog ∧
    success.output.backlog = state.backlog -
      min (ActiveFollowerQueueOperation.serviceCapacity rate.n) state.backlog := by
  cases hstatus : state.status with
  | unoccupied =>
      simp [ActiveRoundActions.FollowerStatus.occupied, hstatus] at hoccupied
  | pending =>
      have haction := success.action
      simp only [ActiveFollowerQueueOperation.serviceAction, hstatus] at haction
      rcases haction with ⟨_, M', hM', _, harrival, hservice⟩
      have hM : M' = M := Option.some.inj (hM'.symm.trans hlast)
      have hnotGate : ¬ ActiveFollowerQueueOperation.recorderGate rate.eta i row t M' := by
        simpa [hM] using hgate
      have hraw : ActiveFollowerQueueOperation.rawArrival rate.eta i row t M' observation = 0 := by
        rw [ActiveFollowerQueueOperation.rawArrival_eq_sourceFormula]
        simp [hnotGate]
      have harrivalZero : success.arrival = 0 := by
        rw [harrival, hraw]
      have hserviceZero : success.service =
          min (ActiveFollowerQueueOperation.serviceCapacity rate.n) state.backlog := by
        rw [hservice, harrivalZero]
        simp [ActiveFollowerQueueOperation.localService, CappedService.service,
          ActiveFollowerQueueOperation.serviceCapacity]
      have hqueue : success.output =
          ActiveFollowerQueueOperation.serviceUpdate rate.n state 0 := by
        calc
          success.output = ActiveFollowerQueueOperation.serviceOutput rate.n state
              success.arrival := success.queueUpdate
          _ = ActiveFollowerQueueOperation.serviceOutput rate.n state 0 := by
            rw [harrivalZero]
          _ = ActiveFollowerQueueOperation.serviceUpdate rate.n state 0 := by
            simp [ActiveFollowerQueueOperation.serviceOutput,
              ActiveRoundActions.FollowerStatus.occupied, hstatus]
      rcases ActiveFollowerQueueOperation.serviceUpdate_zero_arrival rate.n state with
        ⟨hS, hdelta, hbacklog⟩
      exact ⟨harrivalZero, hserviceZero, by rw [hqueue]; exact hS,
        by rw [hqueue]; exact hdelta, by rw [hqueue]; exact hbacklog⟩
  | released =>
      have haction := success.action
      simp only [ActiveFollowerQueueOperation.serviceAction, hstatus] at haction
      rcases haction with ⟨_, M', hM', _, harrival, hservice⟩
      have hM : M' = M := Option.some.inj (hM'.symm.trans hlast)
      have hnotGate : ¬ ActiveFollowerQueueOperation.recorderGate rate.eta i row t M' := by
        simpa [hM] using hgate
      have hraw : ActiveFollowerQueueOperation.rawArrival rate.eta i row t M' observation = 0 := by
        rw [ActiveFollowerQueueOperation.rawArrival_eq_sourceFormula]
        simp [hnotGate]
      have harrivalZero : success.arrival = 0 := by
        rw [harrival, hraw]
      have hserviceZero : success.service =
          min (ActiveFollowerQueueOperation.serviceCapacity rate.n) state.backlog := by
        rw [hservice, harrivalZero]
        simp [ActiveFollowerQueueOperation.localService, CappedService.service,
          ActiveFollowerQueueOperation.serviceCapacity]
      have hqueue : success.output =
          ActiveFollowerQueueOperation.serviceUpdate rate.n state 0 := by
        calc
          success.output = ActiveFollowerQueueOperation.serviceOutput rate.n state
              success.arrival := success.queueUpdate
          _ = ActiveFollowerQueueOperation.serviceOutput rate.n state 0 := by
            rw [harrivalZero]
          _ = ActiveFollowerQueueOperation.serviceUpdate rate.n state 0 := by
            simp [ActiveFollowerQueueOperation.serviceOutput,
              ActiveRoundActions.FollowerStatus.occupied, hstatus]
      rcases ActiveFollowerQueueOperation.serviceUpdate_zero_arrival rate.n state with
        ⟨hS, hdelta, hbacklog⟩
      exact ⟨harrivalZero, hserviceZero, by rw [hqueue]; exact hS,
        by rw [hqueue]; exact hdelta, by rw [hqueue]; exact hbacklog⟩

end Bandits.Support.FollowerServiceMeasurability

end
