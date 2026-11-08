/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.FollowerLifecycleMeasurability
public import Bandits.Support.DeclaredFollowerLocalRound
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# Joint measurability of actual follower release and proposal finish

These results measure the actual release tests and final proposal read on one
declared complete row, retaining the complete row and both original saved
scalar families. The pre-choice and post-service state codes and buffer
skeletons are independent inputs. Invalid registers and buffers remain
failures, and the successful output code reconstructs the entire returned
state and proposal memory from the unchanged post-state buffer.

Sources: `sources/zip4/manuscript/06_interruptions.tex:235-296`,
`sources/zip4/manuscript/05_binary_transport.tex:74-124`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:8-14`.
These local operation results do not provide chronological input provenance,
adaptation, a physical execution, or manuscript theorem closure.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.FollowerReleaseFinishMeasurability

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.CompletePublicTable
open Bandits.Support.ContinuousControlSlice
open Bandits.Support.ContinuousLearningRows
open Bandits.Support.PublicDiscreteDraws
open Bandits.Support.OrderedTupleSampler
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.SparseCalendarReplay
open Bandits.Support.OrdinaryMessageCodec
open Bandits.Support.ActiveRoundActions
open Bandits.Support.ActiveFollowerLifecycle
open Bandits.Support.DeclaredFollowerLocalRound
open Bandits.Support.FollowerDownMeasurability
open Bandits.Support.FollowerDownJointMeasurability
open Bandits.Support.FollowerLifecycleMeasurability

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ActiveFollowerDownAcceptance.RateInput
abbrev SavedScalarFamily (n : ℕ) := FollowerDownMeasurability.SavedScalarFamily n

/-- Inputs to the standalone final proposal-read measurability theorem. -/
abbrev FinishRoundInput (p : Parameters) (n : ℕ) :=
  (CompletePublicTable.CompleteRow p × Fin p.T) × SavedScalarFamily n

/-- Joint inputs to release retain the entire row, both discrete coordinates,
and the two independent original continuous scalar families. -/
abbrev ReleaseInput (p : Parameters) (n m : ℕ) :=
  ((CompletePublicTable.CompleteRow p × Fin p.T) × Fin (D p + 1)) ×
    (SavedScalarFamily n × SavedScalarFamily m)

/-- A countable exact code for the standalone actual `finishRound` result. -/
inductive FinishRoundResultCode (p : Parameters) (rate : RateInput p) where
  | failure (reason : Fin 6)
  | success (state : FollowerStateCode p rate) (memory : LocalMemoryCode p)
  deriving Countable

instance finishRoundResultCodeMeasurableSpace (p : Parameters) (rate : RateInput p) :
    MeasurableSpace (FinishRoundResultCode p rate) := ⊤

/-- Encode the exact result of `ActiveFollowerLifecycle.finishRound`. -/
def finishRoundResultCode {p : Parameters} (rate : RateInput p)
    (result : LifecycleCheck
      (ReferencePrelaunchFollower.State p rate.eta × LocalMemory p)) :
    FinishRoundResultCode p rate :=
  match result with
  | .error reason => .failure (lifecycleFailureCode reason)
  | .ok (state, memory) =>
      .success (followerStateCode rate state) (localMemoryCode memory)

/-- Decode a finish result with its original input buffer supplied unchanged. -/
def finishRoundResultOfCode {p : Parameters} (rate : RateInput p)
    (buffer : List (SparseCalendarRecord p.K)) : FinishRoundResultCode p rate →
      LifecycleCheck
        (ReferencePrelaunchFollower.State p rate.eta × LocalMemory p)
  | .failure reason => .error (lifecycleFailureOfCode reason)
  | .success state memory =>
      .ok (followerStateOfCode rate state buffer, localMemoryOfCode memory)

/-- The exact standalone final-read result on a fixed state code and buffer
skeleton, with the original scalar family left as a continuous input. -/
def finishRoundResultCodeAt {p : Parameters} (rate : RateInput p)
    (row : CompletePublicTable.CompleteRow p) (time : Fin p.T)
    (stateCode : FollowerStateCode p rate) (memoryCode : LocalMemoryCode p)
    {n : ℕ} (skeleton : BufferSkeletonCode p n) (values : SavedScalarFamily n) :
    FinishRoundResultCode p rate :=
  finishRoundResultCode rate
    (ActiveFollowerLifecycle.finishRound rate.eta time row
      (followerStateOfCode rate stateCode
        (bufferFromSkeletonAndScalars skeleton values))
      (localMemoryOfCode memoryCode))

/-- Decide the accepted local-domain predicate on the original scalar family.
The family itself remains on its existing continuous product carrier. -/
noncomputable def localStateDomainValidBit {p : Parameters} (rate : RateInput p)
    (stateCode : FollowerStateCode p rate) {n : ℕ}
    (skeleton : BufferSkeletonCode p n) (values : SavedScalarFamily n) : Bool := by
  classical
  exact decide (ActiveFollowerLifecycle.localStateDomainValid
    (followerStateOfCode rate stateCode (bufferFromSkeletonAndScalars skeleton values)))

private theorem followerStateCode_decode_same_buffer_irrel {p : Parameters}
    (rate : RateInput p) (code : FollowerStateCode p rate)
    (buffer buffer' : List (SparseCalendarRecord p.K)) :
    followerStateCode rate (followerStateOfCode rate code buffer) =
      followerStateCode rate (followerStateOfCode rate code buffer') := by
  cases code
  rfl

private theorem decide_eq_of_iff {p q : Prop} (dp : Decidable p)
    (dq : Decidable q) (h : p ↔ q) : @decide p dp = @decide q dq := by
  cases dp with
  | isTrue hp =>
      cases dq with
      | isTrue _ => rfl
      | isFalse hn => exact False.elim (hn (h.mp hp))
  | isFalse hn =>
      cases dq with
      | isTrue hq => exact False.elim (hn (h.mpr hq))
      | isFalse _ => rfl

/-- Decoding the standalone finish code recovers the complete actual result,
including the entire state and memory, from the unchanged buffer. -/
theorem finishRoundResultOfCode_code {p : Parameters} (rate : RateInput p)
    (time : Fin p.T) (row : CompletePublicTable.CompleteRow p)
    (state : ReferencePrelaunchFollower.State p rate.eta) (memory : LocalMemory p) :
    finishRoundResultOfCode rate state.buffer
        (finishRoundResultCode rate
          (ActiveFollowerLifecycle.finishRound rate.eta time row state memory)) =
      ActiveFollowerLifecycle.finishRound rate.eta time row state memory := by
  cases hfinish : ActiveFollowerLifecycle.finishRound rate.eta time row state memory with
  | error reason => simp [finishRoundResultCode, finishRoundResultOfCode,
      lifecycleFailureOfCode_code]
  | ok result =>
      rcases result with ⟨output, outputMemory⟩
      have hframe := ActiveFollowerLifecycle.finishRound_frame rate.eta time row
        state output memory outputMemory hfinish
      subst output
      simp [finishRoundResultCode, finishRoundResultOfCode,
        FollowerDownMeasurability.followerStateOfCode_code_eq, localMemoryOfCode_code]

/-- Exact reconstruction for the coded finish operation on its original
continuous buffer family. -/
theorem finishRoundResultCodeAt_reconstruct {p : Parameters} (rate : RateInput p)
    (row : CompletePublicTable.CompleteRow p) (time : Fin p.T)
    (stateCode : FollowerStateCode p rate) (memoryCode : LocalMemoryCode p)
    {n : ℕ} (skeleton : BufferSkeletonCode p n) (values : SavedScalarFamily n) :
    finishRoundResultOfCode rate (bufferFromSkeletonAndScalars skeleton values)
        (finishRoundResultCodeAt rate row time stateCode memoryCode skeleton values) =
      ActiveFollowerLifecycle.finishRound rate.eta time row
        (followerStateOfCode rate stateCode
          (bufferFromSkeletonAndScalars skeleton values))
        (localMemoryOfCode memoryCode) := by
  exact finishRoundResultOfCode_code rate time row
    (followerStateOfCode rate stateCode
      (bufferFromSkeletonAndScalars skeleton values))
    (localMemoryOfCode memoryCode)

/-- The measurable read signature retains exactly the finish inputs that can
affect its countable result: time, full-state domain validity, and the actual
current-row proposal bit. -/
def finishRoundReadAt {p : Parameters} (rate : RateInput p)
    (stateCode : FollowerStateCode p rate) {n : ℕ}
    (skeleton : BufferSkeletonCode p n) (input : FinishRoundInput p n) :
    Fin p.T × (Bool × Bool) :=
  (input.1.2,
    (localStateDomainValidBit rate stateCode skeleton input.2,
      FollowerCutoffScan.completeRowProposalBit p rate.eta.val input.1.1 input.1.2))

private theorem measurable_localStateDomainBit {p : Parameters} (rate : RateInput p)
    {n : ℕ} (stateCode : FollowerStateCode p rate)
    (skeleton : BufferSkeletonCode p n) :
    Measurable (fun values : SavedScalarFamily n =>
      localStateDomainValidBit rate stateCode skeleton values) := by
  apply FollowerDownMeasurability.measurable_of_countable_fibers
  intro bit
  cases bit with
  | false =>
      have hset : {values : SavedScalarFamily n |
          localStateDomainValidBit rate stateCode skeleton values = false} =
          {values | ¬ ActiveFollowerLifecycle.localStateDomainValid
            (followerStateOfCode rate stateCode
              (bufferFromSkeletonAndScalars skeleton values))} := by
        ext values
        simp [localStateDomainValidBit]
      rw [hset]
      exact (FollowerLifecycleMeasurability.measurableSet_localStateDomainValid
        rate stateCode skeleton).compl
  | true =>
      have hset : {values : SavedScalarFamily n |
          localStateDomainValidBit rate stateCode skeleton values = true} =
          {values | ActiveFollowerLifecycle.localStateDomainValid
            (followerStateOfCode rate stateCode
              (bufferFromSkeletonAndScalars skeleton values))} := by
        ext values
        simp [localStateDomainValidBit]
      rw [hset]
      exact FollowerLifecycleMeasurability.measurableSet_localStateDomainValid
        rate stateCode skeleton

/-- The actual proposal bit read from a complete row at the supplied time is
jointly measurable in that row and time. -/
theorem measurable_completeRowProposalBitAt (p : Parameters) (eta : ℝ) :
    Measurable (fun rt : CompletePublicTable.CompleteRow p × Fin p.T =>
      FollowerCutoffScan.completeRowProposalBit p eta rt.1 rt.2) := by
  apply measurable_from_prod_countable_left
  intro time
  exact FollowerDownMeasurability.measurable_completeRowProposalBit p eta time

/-- Joint measurability of the standalone actual final proposal-read result
in the entire complete row, calendar time, and original saved scalar family.
All validation branches, including invalid buffers and missing/stale state
records, are retained in the finite failure code. -/
theorem measurable_finishRoundResultCodeAt {p : Parameters} (rate : RateInput p)
    (stateCode : FollowerStateCode p rate) (memoryCode : LocalMemoryCode p)
    {n : ℕ} (skeleton : BufferSkeletonCode p n) :
    Measurable (fun input : FinishRoundInput p n =>
      finishRoundResultCodeAt rate input.1.1 input.1.2 stateCode memoryCode
        skeleton input.2) := by
  let read := finishRoundReadAt rate stateCode skeleton
  have hrowTime : Measurable (fun input : FinishRoundInput p n => input.1) :=
    measurable_fst
  have htime : Measurable (fun input : FinishRoundInput p n => input.1.2) :=
    measurable_snd.comp measurable_fst
  have hproposal : Measurable (fun input : FinishRoundInput p n =>
      FollowerCutoffScan.completeRowProposalBit p rate.eta.val input.1.1 input.1.2) :=
    measurable_completeRowProposalBitAt p rate.eta.val |>.comp hrowTime
  have hdomain : Measurable (fun input : FinishRoundInput p n =>
      localStateDomainValidBit rate stateCode skeleton input.2) :=
    (measurable_localStateDomainBit rate stateCode skeleton).comp measurable_snd
  have hread : Measurable read := by
    exact htime.prodMk (hdomain.prodMk hproposal)
  have hinvariant : ∀ x y : FinishRoundInput p n, read x = read y →
      finishRoundResultCodeAt rate x.1.1 x.1.2 stateCode memoryCode skeleton x.2 =
        finishRoundResultCodeAt rate y.1.1 y.1.2 stateCode memoryCode skeleton y.2 := by
    intro x y hreadEq
    have htimeEq := congrArg Prod.fst hreadEq
    have hdomainEq := congrArg (fun z : Fin p.T × (Bool × Bool) => z.2.1) hreadEq
    have hproposalEq := congrArg (fun z : Fin p.T × (Bool × Bool) => z.2.2) hreadEq
    dsimp [read, finishRoundReadAt] at hdomainEq
    have hvalid : ActiveFollowerLifecycle.localStateDomainValid
        (followerStateOfCode rate stateCode
          (bufferFromSkeletonAndScalars skeleton x.2)) ↔
      ActiveFollowerLifecycle.localStateDomainValid
        (followerStateOfCode rate stateCode
          (bufferFromSkeletonAndScalars skeleton y.2)) := by
      change localStateDomainValidBit rate stateCode skeleton x.2 =
        localStateDomainValidBit rate stateCode skeleton y.2 at hdomainEq
      by_cases hx : ActiveFollowerLifecycle.localStateDomainValid
          (followerStateOfCode rate stateCode (bufferFromSkeletonAndScalars skeleton x.2))
      · by_cases hy : ActiveFollowerLifecycle.localStateDomainValid
            (followerStateOfCode rate stateCode (bufferFromSkeletonAndScalars skeleton y.2))
        · exact ⟨fun _ => hy, fun _ => hx⟩
        · simp [localStateDomainValidBit, hx, hy] at hdomainEq
      · by_cases hy : ActiveFollowerLifecycle.localStateDomainValid
            (followerStateOfCode rate stateCode (bufferFromSkeletonAndScalars skeleton y.2))
        · simp [localStateDomainValidBit, hx, hy] at hdomainEq
        · exact ⟨fun h => (hx h).elim, fun h => (hy h).elim⟩
    have hproposal : FollowerCutoffScan.completeRowProposalBit p rate.eta.val
        x.1.1 x.1.2 = FollowerCutoffScan.completeRowProposalBit p rate.eta.val
          y.1.1 y.1.2 := by
      simpa [read, finishRoundReadAt] using hproposalEq
    have htime : x.1.2 = y.1.2 := htimeEq
    unfold finishRoundResultCodeAt finishRoundResultCode
    let stateX := followerStateOfCode rate stateCode
      (bufferFromSkeletonAndScalars skeleton x.2)
    let stateY := followerStateOfCode rate stateCode
      (bufferFromSkeletonAndScalars skeleton y.2)
    have hstatus : stateX.status = stateY.status := by
      simp [stateX, stateY, FollowerDownMeasurability.followerStateOfCode]
    have hlast : stateX.lastDown = stateY.lastDown := by
      simp [stateX, stateY, FollowerDownMeasurability.followerStateOfCode]
    have hstateCode : followerStateCode rate stateX = followerStateCode rate stateY := by
      exact followerStateCode_decode_same_buffer_irrel rate stateCode _ _
    change finishRoundResultCode rate
        (ActiveFollowerLifecycle.finishRound rate.eta x.1.2 x.1.1 stateX
          (localMemoryOfCode memoryCode)) =
      finishRoundResultCode rate
        (ActiveFollowerLifecycle.finishRound rate.eta y.1.2 y.1.1 stateY
          (localMemoryOfCode memoryCode))
    by_cases hvalidX : ActiveFollowerLifecycle.localStateDomainValid stateX
    · have hvalidY : ActiveFollowerLifecycle.localStateDomainValid stateY := by
        simpa [stateX, stateY] using hvalid.mp hvalidX
      by_cases hunoccupied : stateX.status = FollowerStatus.unoccupied
      · have hunoccupiedY : stateY.status = FollowerStatus.unoccupied := by
          simpa [hstatus] using hunoccupied
        rw [ActiveFollowerLifecycle.finishRound_unoccupied rate.eta x.1.2 x.1.1
              stateX (localMemoryOfCode memoryCode) hvalidX hunoccupied,
            ActiveFollowerLifecycle.finishRound_unoccupied rate.eta y.1.2 y.1.1
              stateY (localMemoryOfCode memoryCode) hvalidY hunoccupiedY]
        simp [finishRoundResultCode, hstateCode, localMemoryCodeOfCode]
      · have hunoccupiedY : stateY.status ≠ FollowerStatus.unoccupied := by
          intro h
          exact hunoccupied (hstatus.symm ▸ h)
        cases hrecord : stateX.lastDown with
        | none =>
            have hrecordY : stateY.lastDown = none := by simpa [hlast] using hrecord
            rw [ActiveFollowerLifecycle.finishRound_missing_record rate.eta x.1.2 x.1.1
                  stateX (localMemoryOfCode memoryCode) hunoccupied hvalidX hrecord,
                ActiveFollowerLifecycle.finishRound_missing_record rate.eta y.1.2 y.1.1
                  stateY (localMemoryOfCode memoryCode) hunoccupiedY hvalidY hrecordY]
        | some M =>
            have hrecordY : stateY.lastDown = some M := by simpa [hlast] using hrecord
            by_cases htimeX : M.val.sigma ≤ x.1.2.val + 1
            · have htimeY : M.val.sigma ≤ y.1.2.val + 1 := by
                simpa [htime] using htimeX
              rw [ActiveFollowerLifecycle.finishRound_occupied_read rate.eta x.1.2 x.1.1
                    stateX (localMemoryOfCode memoryCode) hunoccupied hvalidX M hrecord htimeX,
                  ActiveFollowerLifecycle.finishRound_occupied_read rate.eta y.1.2 y.1.1
                    stateY (localMemoryOfCode memoryCode) hunoccupiedY hvalidY M hrecordY htimeY]
              rw [hproposal]
              simp [finishRoundResultCode, hstateCode, htime]
            · have htimeY : ¬ M.val.sigma ≤ y.1.2.val + 1 := by
                simpa [htime] using htimeX
              have hbadX : x.1.2.val + 1 < M.val.sigma := by omega
              have hbadY : y.1.2.val + 1 < M.val.sigma := by omega
              rw [ActiveFollowerLifecycle.finishRound_incompatible_start rate.eta x.1.2 x.1.1
                    stateX (localMemoryOfCode memoryCode) hunoccupied hvalidX M hrecord hbadX,
                  ActiveFollowerLifecycle.finishRound_incompatible_start rate.eta y.1.2 y.1.1
                    stateY (localMemoryOfCode memoryCode) hunoccupiedY hvalidY M hrecordY hbadY]
    · have hvalidY : ¬ ActiveFollowerLifecycle.localStateDomainValid stateY := by
        intro h
        exact hvalidX (hvalid.mpr h)
      rw [ActiveFollowerLifecycle.finishRound_invalid_domain rate.eta x.1.2 x.1.1
            stateX (localMemoryOfCode memoryCode) hvalidX,
          ActiveFollowerLifecycle.finishRound_invalid_domain rate.eta y.1.2 y.1.1
            stateY (localMemoryOfCode memoryCode) hvalidY]
  exact FollowerDownJointMeasurability.measurable_of_countable_read_factorization
    read hread _ hinvariant

/-- A bounded helper type for the finite release observations used by the
actual release operation. -/
abbrev ReleaseObservationCode (p : Parameters) :=
  Fin p.T × (Bool × (Bool × Bool))

/-- The exact release predicate on the selected complete row. -/
noncomputable def releaseConditionBitAt {p : Parameters} (rate : RateInput p)
    (i : Fin (p.m - 1)) (M : DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (row : CompletePublicTable.CompleteRow p) (time : Fin p.T)
    (feedback : Fin (D p + 1)) : Bool := by
  classical
  exact decide (ActiveFollowerLifecycle.releaseCondition rate.eta i
    (ActiveFollowerLifecycle.publicRowOfCompleteRow row time)
    (FollowerDownMeasurability.feedbackAtGrid p feedback) M)

/-- The actual release read signature: current time, validity of each
independent input state, and the exact PRE-CHOICE record's release test. -/
def releaseReadAt {p : Parameters} (rate : RateInput p)
    (i : Fin (p.m - 1)) (preCode postCode : FollowerStateCode p rate)
    {n m : ℕ} (preSkeleton : BufferSkeletonCode p n)
    (postSkeleton : BufferSkeletonCode p m) (input : ReleaseInput p n m) :
    ReleaseObservationCode p := by
  classical
  exact (input.1.1.2,
    (localStateDomainValidBit rate preCode preSkeleton input.2.1,
      (localStateDomainValidBit rate postCode postSkeleton input.2.2,
        match preCode.lastDown with
        | none => false
        | some M => releaseConditionBitAt rate i M input.1.1.1 input.1.1.2
            input.1.2)))

private theorem measurable_releaseConditionBitAt {p : Parameters} (rate : RateInput p)
    (i : Fin (p.m - 1)) (time : Fin p.T)
    (M : DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (feedback : Fin (D p + 1)) :
    Measurable (fun row : CompletePublicTable.CompleteRow p =>
      releaseConditionBitAt rate i M row time feedback) := by
  classical
  let slice : CompletePublicTable.CompleteRow p → ContinuousControlSlice.Slice p.m p.K :=
    fun row => (row.2 time).1
  have hslice : Measurable slice := by
    exact measurable_fst.comp
      ((measurable_pi_apply time).comp measurable_snd)
  let slot : CompletePublicTable.CompleteRow p → PublicDiscreteDraws.Slot :=
    fun row => PublicDiscreteDraws.slotDraw (slice row)
  let selected : CompletePublicTable.CompleteRow p → Fin (p.m - 1) :=
    fun row => PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K (slice row)
  let tuple : CompletePublicTable.CompleteRow p → OrderedTupleSampler.Tuple p.m p.K :=
    fun row => OrderedTupleSampler.sample p.two_le_m p.m_lt_K (slice row)
  let coordinatorTuple : CompletePublicTable.CompleteRow p → Fin p.K :=
    fun row => (tuple row).val (ActiveRoundActions.coordinator p.two_le_m)
  let coordinatorPilot : CompletePublicTable.CompleteRow p → Fin p.K :=
    fun row => PublicDiscreteDraws.pilotDraw (K_pos p)
      (ActiveRoundActions.coordinator p.two_le_m) (slice row)
  have hslot : Measurable slot := PublicDiscreteDraws.measurable_slotDraw.comp hslice
  have hselected : Measurable selected :=
    (PublicDiscreteDraws.measurable_selectedFollowerDraw p.two_le_m p.m_lt_K).comp hslice
  have htuple : Measurable tuple :=
    (OrderedTupleSampler.measurable_sample p.two_le_m p.m_lt_K).comp hslice
  have hcoordinatorTuple : Measurable coordinatorTuple := by
    exact (measurable_pi_apply (ActiveRoundActions.coordinator p.two_le_m)).comp
      (measurable_subtype_coe.comp htuple)
  have hcoordinatorPilot : Measurable coordinatorPilot :=
    (PublicDiscreteDraws.measurable_pilotDraw (K_pos p)
      (ActiveRoundActions.coordinator p.two_le_m)).comp hslice
  let args : CompletePublicTable.CompleteRow p →
      PublicDiscreteDraws.Slot × (Fin (p.m - 1) × (Fin p.K × Fin p.K)) :=
    fun row => (slot row, (selected row, (coordinatorTuple row, coordinatorPilot row)))
  have hargs : Measurable args :=
    hslot.prodMk (hselected.prodMk (hcoordinatorTuple.prodMk hcoordinatorPilot))
  let condition : PublicDiscreteDraws.Slot × (Fin (p.m - 1) × (Fin p.K × Fin p.K)) → Bool :=
    fun z => decide (0 < (FollowerDownMeasurability.feedbackAtGrid p feedback).val.val ∧
      ((z.1 = PublicDiscreteDraws.upSlot ∧ z.2.1 = i ∧
          z.2.2.1 = ActiveFollowerLifecycle.acceptedEscapeArm M) ∨
        (z.1 = PublicDiscreteDraws.dataSlot ∧
          z.2.2.2 = PrelaunchBufferRecovery.downArm rate.eta M)))
  have hcondition : Measurable condition := measurable_of_finite _
  have heq : (fun row : CompletePublicTable.CompleteRow p =>
      releaseConditionBitAt rate i M row time feedback) =
      condition ∘ args := by
    funext row
    have hprop := ActiveFollowerLifecycle.releaseCondition_complete_row rate.eta i
      time row (FollowerDownMeasurability.feedbackAtGrid p feedback) M
    have hbit : releaseConditionBitAt rate i M row time feedback =
        decide (0 < (FollowerDownMeasurability.feedbackAtGrid p feedback).val.val ∧
          ((PublicDiscreteDraws.slotDraw (slice row) = PublicDiscreteDraws.upSlot ∧
              PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K (slice row) = i ∧
                (OrderedTupleSampler.sample p.two_le_m p.m_lt_K (slice row)).val
                  (ActiveRoundActions.coordinator p.two_le_m) =
                    ActiveFollowerLifecycle.acceptedEscapeArm M) ∨
            (PublicDiscreteDraws.slotDraw (slice row) = PublicDiscreteDraws.dataSlot ∧
              PublicDiscreteDraws.pilotDraw (K_pos p)
                (ActiveRoundActions.coordinator p.two_le_m) (slice row) =
                  PrelaunchBufferRecovery.downArm rate.eta M))) := by
      unfold releaseConditionBitAt
      simpa [slice] using decide_eq_of_iff (inferInstance) (inferInstance) hprop
    calc
      releaseConditionBitAt rate i M row time feedback = _ := hbit
      _ = condition (args row) := by
        simp only [condition, args, slot, selected, tuple, coordinatorTuple,
          coordinatorPilot, slice]
        exact decide_eq_of_iff _ _ Iff.rfl
  rw [heq]
  exact hcondition.comp hargs

/-- The release predicate is jointly measurable in the complete row, time,
and finite own-feedback index. -/
private theorem measurable_releaseConditionBitJoint {p : Parameters}
    (rate : RateInput p) (i : Fin (p.m - 1))
    (M : DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)) :
    Measurable (fun input :
      (CompletePublicTable.CompleteRow p × Fin p.T) × Fin (D p + 1) =>
        releaseConditionBitAt rate i M input.1.1 input.1.2 input.2) := by
  have hsection : ∀ tf : Fin p.T × Fin (D p + 1),
      Measurable (fun row : CompletePublicTable.CompleteRow p =>
        releaseConditionBitAt rate i M row tf.1 tf.2) := by
    intro tf
    exact measurable_releaseConditionBitAt rate i tf.1 M tf.2
  have hjoint : Measurable (fun x : CompletePublicTable.CompleteRow p ×
      (Fin p.T × Fin (D p + 1)) =>
        releaseConditionBitAt rate i M x.1 x.2.1 x.2.2) := by
    apply measurable_from_prod_countable_left
    intro tf
    exact hsection tf
  have hargs : Measurable (fun input :
      (CompletePublicTable.CompleteRow p × Fin p.T) × Fin (D p + 1) =>
        Prod.mk input.1.1 (Prod.mk input.1.2 input.2)) := by
    have hrow : Measurable (fun input :
        (CompletePublicTable.CompleteRow p × Fin p.T) × Fin (D p + 1) => input.1.1) :=
      measurable_fst.comp measurable_fst
    have htime : Measurable (fun input :
        (CompletePublicTable.CompleteRow p × Fin p.T) × Fin (D p + 1) => input.1.2) :=
      measurable_snd.comp measurable_fst
    have hfeedback : Measurable (fun input :
        (CompletePublicTable.CompleteRow p × Fin p.T) × Fin (D p + 1) => input.2) :=
      measurable_snd
    exact hrow.prodMk (htime.prodMk hfeedback)
  have hcomp := hjoint.comp hargs
  change Measurable (fun input :
    (CompletePublicTable.CompleteRow p × Fin p.T) × Fin (D p + 1) =>
      releaseConditionBitAt rate i M input.1.1 input.1.2 input.2) at hcomp
  exact hcomp

/-- The release read signature is measurable in the entire joint input. -/
theorem measurable_releaseReadAt {p : Parameters} (rate : RateInput p)
    (i : Fin (p.m - 1)) (preCode postCode : FollowerStateCode p rate)
    {n m : ℕ} (preSkeleton : BufferSkeletonCode p n)
    (postSkeleton : BufferSkeletonCode p m) :
    Measurable (releaseReadAt rate i preCode postCode preSkeleton postSkeleton) := by
  let validPre := fun values : SavedScalarFamily n =>
    localStateDomainValidBit rate preCode preSkeleton values
  let validPost := fun values : SavedScalarFamily m =>
    localStateDomainValidBit rate postCode postSkeleton values
  have htime : Measurable (fun input : ReleaseInput p n m => input.1.1.2) :=
    measurable_snd.comp (measurable_fst.comp measurable_fst)
  have hpre : Measurable (fun input : ReleaseInput p n m => validPre input.2.1) :=
    (measurable_localStateDomainBit rate preCode preSkeleton).comp
      (measurable_fst.comp measurable_snd)
  have hpost : Measurable (fun input : ReleaseInput p n m => validPost input.2.2) :=
    (measurable_localStateDomainBit rate postCode postSkeleton).comp
      (measurable_snd.comp measurable_snd)
  have htest : Measurable (fun input : ReleaseInput p n m =>
      match preCode.lastDown with
      | none => false
      | some M => releaseConditionBitAt rate i M
          input.1.1.1 input.1.1.2 input.1.2) := by
    cases hrecord : preCode.lastDown with
    | none => simpa [hrecord] using (measurable_const : Measurable (fun _ : ReleaseInput p n m => false))
    | some M =>
        have hbase : Measurable (fun input :
            (CompletePublicTable.CompleteRow p × Fin p.T) × Fin (D p + 1) =>
              releaseConditionBitAt rate i M input.1.1 input.1.2 input.2) :=
          measurable_releaseConditionBitJoint rate i M
        have hproj : Measurable (fun input : ReleaseInput p n m => input.1) :=
          measurable_fst
        have hcomp := hbase.comp hproj
        change Measurable (fun input : ReleaseInput p n m =>
          releaseConditionBitAt rate i M input.1.1.1 input.1.1.2 input.1.2) at hcomp
        exact hcomp
  exact htime.prodMk (hpre.prodMk (hpost.prodMk htest))

/-- The actual release result code is constant on equal time, input-domain,
and exact release-test signatures. -/
private theorem releaseAfterServiceResultCodeAt_eq_of_read_eq {p : Parameters}
    (rate : RateInput p) (i : Fin (p.m - 1))
    (preCode postCode : FollowerStateCode p rate)
    {n m : ℕ} (preSkeleton : BufferSkeletonCode p n)
    (postSkeleton : BufferSkeletonCode p m)
    (x y : ReleaseInput p n m)
    (hread : releaseReadAt rate i preCode postCode preSkeleton postSkeleton x =
      releaseReadAt rate i preCode postCode preSkeleton postSkeleton y) :
    releaseAfterServiceResultCodeAt rate i x.1.1.1 x.1.1.2 x.1.2 preCode postCode
      preSkeleton postSkeleton x.2.1 x.2.2 =
    releaseAfterServiceResultCodeAt rate i y.1.1.1 y.1.1.2 y.1.2 preCode postCode
      preSkeleton postSkeleton y.2.1 y.2.2 := by
  have htime := congrArg Prod.fst hread
  dsimp [releaseReadAt] at htime
  have hpreBit := congrArg (fun z : ReleaseObservationCode p => z.2.1) hread
  have hpostBit := congrArg (fun z : ReleaseObservationCode p => z.2.2.1) hread
  have htestBit := congrArg (fun z : ReleaseObservationCode p => z.2.2.2) hread
  let preX := followerStateOfCode rate preCode
    (bufferFromSkeletonAndScalars preSkeleton x.2.1)
  let preY := followerStateOfCode rate preCode
    (bufferFromSkeletonAndScalars preSkeleton y.2.1)
  let postX := followerStateOfCode rate postCode
    (bufferFromSkeletonAndScalars postSkeleton x.2.2)
  let postY := followerStateOfCode rate postCode
    (bufferFromSkeletonAndScalars postSkeleton y.2.2)
  have hpreValid : ActiveFollowerLifecycle.localStateDomainValid preX ↔
      ActiveFollowerLifecycle.localStateDomainValid preY := by
    dsimp [releaseReadAt] at hpreBit
    change localStateDomainValidBit rate preCode preSkeleton x.2.1 =
      localStateDomainValidBit rate preCode preSkeleton y.2.1 at hpreBit
    by_cases hx : ActiveFollowerLifecycle.localStateDomainValid preX <;>
      by_cases hy : ActiveFollowerLifecycle.localStateDomainValid preY <;>
        simp [localStateDomainValidBit, preX, preY, hx, hy] at hpreBit ⊢
  have hpostValid : ActiveFollowerLifecycle.localStateDomainValid postX ↔
      ActiveFollowerLifecycle.localStateDomainValid postY := by
    dsimp [releaseReadAt] at hpostBit
    change localStateDomainValidBit rate postCode postSkeleton x.2.2 =
      localStateDomainValidBit rate postCode postSkeleton y.2.2 at hpostBit
    by_cases hx : ActiveFollowerLifecycle.localStateDomainValid postX <;>
      by_cases hy : ActiveFollowerLifecycle.localStateDomainValid postY <;>
        simp [localStateDomainValidBit, postX, postY, hx, hy] at hpostBit ⊢
  have hpreStatus : preX.status = preY.status := rfl
  have hpreLast : preX.lastDown = preY.lastDown := rfl
  have htimeValue : x.1.1.2.val = y.1.1.2.val := congrArg Fin.val htime
  have hpostCode : followerStateCode rate postX = followerStateCode rate postY := by
    dsimp [postX, postY]
    exact followerStateCode_decode_same_buffer_irrel rate postCode _ _
  have hpostReleasedCode :
      followerStateCode rate {postX with status := FollowerStatus.released} =
        followerStateCode rate {postY with status := FollowerStatus.released} := by
    cases postCode
    rfl
  unfold releaseAfterServiceResultCodeAt releaseAfterServiceResultCode
  by_cases hpending : FollowerDownMeasurability.followerStatusOfCode preCode.status =
      FollowerStatus.pending
  · have hpendingY : FollowerDownMeasurability.followerStatusOfCode preCode.status =
        FollowerStatus.pending := hpending
    have hpendingStateX : preX.status = FollowerStatus.pending := by
      change FollowerDownMeasurability.followerStatusOfCode preCode.status = _
      exact hpending
    have hpendingStateY : preY.status = FollowerStatus.pending := by
      change FollowerDownMeasurability.followerStatusOfCode preCode.status = _
      exact hpendingY
    by_cases hpreDomain : ActiveFollowerLifecycle.localStateDomainValid preX
    · have hpreDomainY : ActiveFollowerLifecycle.localStateDomainValid preY :=
        hpreValid.mp hpreDomain
      cases hlast : preX.lastDown with
      | none =>
          have hlastY : preY.lastDown = none := hpreLast.symm.trans hlast
          have hlastStateX : preX.lastDown = none := hlast
          have hlastStateY : preY.lastDown = none := hlastY
          have hlastCode : preCode.lastDown = none := by
            simpa [preX, FollowerDownMeasurability.followerStateOfCode] using hlast
          simp [ActiveFollowerLifecycle.releaseAfterService, preX, preY, postX, postY,
            hpendingStateX, hpendingStateY, hlastStateX, hlastStateY, hlastCode,
            hpreDomain, hpreDomainY, hpostCode]
      | some M =>
          have hlastY : preY.lastDown = some M := hpreLast.symm.trans hlast
          have hlastStateX : preX.lastDown = some M := hlast
          have hlastStateY : preY.lastDown = some M := hlastY
          have hlastCode : preCode.lastDown = some M := by
            simpa [preX, FollowerDownMeasurability.followerStateOfCode] using hlast
          have htestBit' : releaseConditionBitAt rate i M x.1.1.1 x.1.1.2 x.1.2 =
              releaseConditionBitAt rate i M y.1.1.1 y.1.1.2 y.1.2 := by
            simpa [releaseReadAt, hlastCode] using htestBit
          have htest : ActiveFollowerLifecycle.releaseCondition rate.eta i
              (ActiveFollowerLifecycle.publicRowOfCompleteRow x.1.1.1 x.1.1.2)
              (FollowerDownMeasurability.feedbackAtGrid p x.1.2) M ↔
            ActiveFollowerLifecycle.releaseCondition rate.eta i
              (ActiveFollowerLifecycle.publicRowOfCompleteRow y.1.1.1 y.1.1.2)
              (FollowerDownMeasurability.feedbackAtGrid p y.1.2) M := by
            by_cases hx : ActiveFollowerLifecycle.releaseCondition rate.eta i
                (ActiveFollowerLifecycle.publicRowOfCompleteRow x.1.1.1 x.1.1.2)
                (FollowerDownMeasurability.feedbackAtGrid p x.1.2) M <;>
              by_cases hy : ActiveFollowerLifecycle.releaseCondition rate.eta i
                (ActiveFollowerLifecycle.publicRowOfCompleteRow y.1.1.1 y.1.1.2)
                (FollowerDownMeasurability.feedbackAtGrid p y.1.2) M <;>
              simp [releaseConditionBitAt, hx, hy] at htestBit' ⊢
          by_cases htimeM : M.val.sigma ≤ x.1.1.2.val
          · have htimeMY : M.val.sigma ≤ y.1.1.2.val := by
              simpa [htimeValue] using htimeM
            by_cases hpostDomain : ActiveFollowerLifecycle.localStateDomainValid postX
            · have hpostDomainY : ActiveFollowerLifecycle.localStateDomainValid postY :=
                hpostValid.mp hpostDomain
              let hasOutputRecordX : Prop := ∃ M', postX.lastDown = some M' ∧
                M'.val.sigma ≤ y.1.1.2.val + 1
              let hasOutputRecordY : Prop := ∃ M', postY.lastDown = some M' ∧
                M'.val.sigma ≤ y.1.1.2.val + 1
              have hhasOutputRecord : hasOutputRecordX ↔ hasOutputRecordY := by
                simp [hasOutputRecordX, hasOutputRecordY, postX, postY,
                  FollowerDownMeasurability.followerStateOfCode]
              have hpostStatus : postX.status = postY.status := rfl
              have hpostOutputRecord :
                  (postX.status = FollowerStatus.unoccupied ∨ hasOutputRecordX) ↔
                    (postY.status = FollowerStatus.unoccupied ∨ hasOutputRecordY) := by
                simp [hpostStatus, hhasOutputRecord]
              by_cases htestX : ActiveFollowerLifecycle.releaseCondition rate.eta i
                  (ActiveFollowerLifecycle.publicRowOfCompleteRow x.1.1.1 x.1.1.2)
                  (FollowerDownMeasurability.feedbackAtGrid p x.1.2) M
              · have htestY := htest.mp htestX
                by_cases hrecordX : hasOutputRecordX
                · have hrecordY : hasOutputRecordY := hhasOutputRecord.mp hrecordX
                  simp [ActiveFollowerLifecycle.releaseAfterService, preX, preY, postX, postY,
                    hpendingStateX, hpendingStateY, hlastStateX, hlastStateY, hlastCode,
                    hpreDomain, hpreDomainY, htimeM, htimeMY, htimeValue,
                    hpostDomain, hpostDomainY, htestX, htestY, hrecordX, hrecordY,
                    hasOutputRecordX, hasOutputRecordY, hpostCode, hpostReleasedCode]
                · have hrecordY : ¬ hasOutputRecordY := fun hy =>
                    hrecordX (hhasOutputRecord.mpr hy)
                  simp [ActiveFollowerLifecycle.releaseAfterService, preX, preY, postX, postY,
                    hpendingStateX, hpendingStateY, hlastStateX, hlastStateY, hlastCode,
                    hpreDomain, hpreDomainY, htimeM, htimeMY, htimeValue,
                    hpostDomain, hpostDomainY, htestX, htestY, hrecordX, hrecordY,
                    hasOutputRecordX, hasOutputRecordY, hpostCode, hpostReleasedCode]
              · have htestY : ¬ ActiveFollowerLifecycle.releaseCondition rate.eta i
                    (ActiveFollowerLifecycle.publicRowOfCompleteRow y.1.1.1 y.1.1.2)
                    (FollowerDownMeasurability.feedbackAtGrid p y.1.2) M :=
                  fun hy => htestX (htest.mpr hy)
                by_cases houtputX :
                    postX.status = FollowerStatus.unoccupied ∨ hasOutputRecordX
                · have houtputY :
                      postY.status = FollowerStatus.unoccupied ∨ hasOutputRecordY :=
                    hpostOutputRecord.mp houtputX
                  simp [ActiveFollowerLifecycle.releaseAfterService, preX, preY, postX, postY,
                    hpendingStateX, hpendingStateY, hlastStateX, hlastStateY, hlastCode,
                    hpreDomain, hpreDomainY, htimeM, htimeMY, htimeValue,
                    hpostDomain, hpostDomainY, htestX, htestY, houtputX, houtputY,
                    hasOutputRecordX, hasOutputRecordY, hpostCode]
                · have houtputY :
                      ¬(postY.status = FollowerStatus.unoccupied ∨ hasOutputRecordY) :=
                    fun hy => houtputX (hpostOutputRecord.mpr hy)
                  simp [ActiveFollowerLifecycle.releaseAfterService, preX, preY, postX, postY,
                    hpendingStateX, hpendingStateY, hlastStateX, hlastStateY, hlastCode,
                    hpreDomain, hpreDomainY, htimeM, htimeMY, htimeValue,
                    hpostDomain, hpostDomainY, htestX, htestY, houtputX, houtputY,
                    hasOutputRecordX, hasOutputRecordY, hpostCode]
            · have hpostDomainY : ¬ ActiveFollowerLifecycle.localStateDomainValid postY :=
                fun hy => hpostDomain ((hpostValid).mpr hy)
              simp [ActiveFollowerLifecycle.releaseAfterService, preX, preY, postX, postY,
                hpendingStateX, hpendingStateY, hlastStateX, hlastStateY, hlastCode,
                hpreDomain, hpreDomainY,
                htimeM, htimeMY, htimeValue, hpostDomain, hpostDomainY]
          · have htimeMY : ¬ M.val.sigma ≤ y.1.1.2.val := by
              simpa [htimeValue] using htimeM
            simp [ActiveFollowerLifecycle.releaseAfterService, preX, preY, postX, postY,
              hpendingStateX, hpendingStateY, hlastStateX, hlastStateY, hlastCode,
              hpreDomain, hpreDomainY,
              htimeM, htimeMY, htimeValue]
    · have hpreDomainY : ¬ ActiveFollowerLifecycle.localStateDomainValid preY :=
        fun hy => hpreDomain ((hpreValid).mpr hy)
      simp [ActiveFollowerLifecycle.releaseAfterService, preX, preY, postX, postY,
        hpendingStateX, hpendingStateY, hpreDomain, hpreDomainY]
  · have hpendingY : preY.status ≠ FollowerStatus.pending :=
    by simpa [preY, FollowerDownMeasurability.followerStateOfCode] using hpending
    have hpendingStateX : preX.status ≠ FollowerStatus.pending := by
      change ¬(FollowerDownMeasurability.followerStatusOfCode preCode.status =
        FollowerStatus.pending)
      exact hpending
    have hpendingStateY : preY.status ≠ FollowerStatus.pending := hpendingY
    simp [ActiveFollowerLifecycle.releaseAfterService, preX, preY, postX, postY,
      hpendingStateX, hpendingStateY, hpostCode]

/-- Joint measurability of the existing actual pending-release result code in
the complete row, time, own finite feedback, and both original continuous
saved-scalar families, for independently supplied codes and skeletons of any
length. -/
theorem measurable_releaseAfterServiceResultCodeAt {p : Parameters}
    (rate : RateInput p) (i : Fin (p.m - 1))
    (preCode postCode : FollowerStateCode p rate)
    {n m : ℕ} (preSkeleton : BufferSkeletonCode p n)
    (postSkeleton : BufferSkeletonCode p m) :
    Measurable (fun input : ReleaseInput p n m =>
      releaseAfterServiceResultCodeAt rate i input.1.1.1 input.1.1.2 input.1.2
        preCode postCode preSkeleton postSkeleton input.2.1 input.2.2) := by
  let read := releaseReadAt rate i preCode postCode preSkeleton postSkeleton
  have hread := measurable_releaseReadAt rate i preCode postCode preSkeleton postSkeleton
  have hinvariant : ∀ x y : ReleaseInput p n m, read x = read y →
      releaseAfterServiceResultCodeAt rate i x.1.1.1 x.1.1.2 x.1.2 preCode postCode
        preSkeleton postSkeleton x.2.1 x.2.2 =
      releaseAfterServiceResultCodeAt rate i y.1.1.1 y.1.1.2 y.1.2 preCode postCode
        preSkeleton postSkeleton y.2.1 y.2.2 := by
    intro x y h
    exact releaseAfterServiceResultCodeAt_eq_of_read_eq rate i preCode postCode
      preSkeleton postSkeleton x y h
  exact FollowerDownJointMeasurability.measurable_of_countable_read_factorization
    read hread _ hinvariant

/-- Reconstructing the release code retains every failure and the complete
returned post-service state, including all continuous post-state buffer
coordinates. -/
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
        (FollowerDownMeasurability.feedbackAtGrid p feedback)
        (followerStateOfCode rate preCode
          (bufferFromSkeletonAndScalars preSkeleton preValues))
        (followerStateOfCode rate postCode
          (bufferFromSkeletonAndScalars postSkeleton postValues)) :=
  FollowerLifecycleMeasurability.releaseAfterServiceResultCodeAt_reconstruct
    rate i row time feedback preCode postCode preSkeleton postSkeleton preValues postValues

/-- Exact composition of the measurable release code and the standalone
finish code gives the existing combined actual `releaseAndFinish` code. The
released state is reconstructed from its entire post-service buffer before
the finish operation is applied. -/
def releaseAndFinishCodeFromReleaseAndFinishCodes {p : Parameters}
    (rate : RateInput p) (row : CompletePublicTable.CompleteRow p)
    (time : Fin p.T) (memoryCode : LocalMemoryCode p) {m : ℕ}
    (postSkeleton : BufferSkeletonCode p m) (postValues : SavedScalarFamily m)
    (releaseCode : ReleaseAfterServiceResultCode p rate) :
    ReleaseAndFinishResultCode p rate := by
  classical
  cases releaseCode with
  | failure reason =>
      exact .failure (.release (lifecycleFailureOfCode reason))
  | success stateCode =>
      match finishRoundResultCodeAt rate row time stateCode memoryCode postSkeleton postValues with
      | .failure reason => exact .failure (.finish (lifecycleFailureOfCode reason))
      | .success output outputMemory => exact .success output outputMemory

/-- The result-code composition above is exactly the existing actual
`DeclaredFollowerLocalRound.releaseAndFinish` encoder, with no assumed
measurability of either operation or branch. -/
theorem releaseAndFinishResultCodeAt_eq_from_codes {p : Parameters}
    (rate : RateInput p) (i : Fin (p.m - 1))
    (row : CompletePublicTable.CompleteRow p) (time : Fin p.T)
    (feedback : Fin (D p + 1)) (preCode postCode : FollowerStateCode p rate)
    (memoryCode : LocalMemoryCode p) {n m : ℕ}
    (preSkeleton : BufferSkeletonCode p n) (postSkeleton : BufferSkeletonCode p m)
    (preValues : SavedScalarFamily n) (postValues : SavedScalarFamily m) :
    releaseAndFinishResultCodeAt rate i row time feedback preCode postCode memoryCode
      preSkeleton postSkeleton preValues postValues =
    releaseAndFinishCodeFromReleaseAndFinishCodes rate row time memoryCode
      postSkeleton postValues
      (releaseAfterServiceResultCodeAt rate i row time feedback preCode postCode
        preSkeleton postSkeleton preValues postValues) := by
  let postBuffer := bufferFromSkeletonAndScalars postSkeleton postValues
  unfold releaseAndFinishResultCodeAt
  cases hcode : releaseAfterServiceResultCodeAt rate i row time feedback preCode postCode
      preSkeleton postSkeleton preValues postValues with
  | failure reason =>
      have hrec := releaseAfterServiceResultCodeAt_reconstruct rate i row time feedback
        preCode postCode preSkeleton postSkeleton preValues postValues
      rw [hcode] at hrec
      have hrelease : ActiveFollowerLifecycle.releaseAfterService rate.eta i time
          (ActiveFollowerLifecycle.publicRowOfCompleteRow row time)
          (FollowerDownMeasurability.feedbackAtGrid p feedback)
          (followerStateOfCode rate preCode
            (bufferFromSkeletonAndScalars preSkeleton preValues))
          (followerStateOfCode rate postCode postBuffer) =
        .error (lifecycleFailureOfCode reason) := by
        simpa [releaseAfterServiceResultOfCode, postBuffer] using hrec.symm
      have hrelease' := hrelease
      simp only [postBuffer] at hrelease'
      simp [releaseAndFinishCodeFromReleaseAndFinishCodes,
        releaseAndFinishResultCode, DeclaredFollowerLocalRound.releaseAndFinish,
        hrelease']
  | success stateCode =>
      have hrec := releaseAfterServiceResultCodeAt_reconstruct rate i row time feedback
        preCode postCode preSkeleton postSkeleton preValues postValues
      rw [hcode] at hrec
      have hrelease : ActiveFollowerLifecycle.releaseAfterService rate.eta i time
          (ActiveFollowerLifecycle.publicRowOfCompleteRow row time)
          (FollowerDownMeasurability.feedbackAtGrid p feedback)
          (followerStateOfCode rate preCode
            (bufferFromSkeletonAndScalars preSkeleton preValues))
          (followerStateOfCode rate postCode postBuffer) =
        .ok (followerStateOfCode rate stateCode postBuffer) := by
        simpa [releaseAfterServiceResultOfCode, postBuffer] using hrec.symm
      have hrelease' := hrelease
      simp only [postBuffer] at hrelease'
      let releasedState := followerStateOfCode rate stateCode
        (bufferFromSkeletonAndScalars postSkeleton postValues)
      cases hfinish : ActiveFollowerLifecycle.finishRound rate.eta time row releasedState
          (localMemoryOfCode memoryCode) with
      | error reason =>
          simp [releaseAndFinishCodeFromReleaseAndFinishCodes,
            releaseAndFinishResultCode, DeclaredFollowerLocalRound.releaseAndFinish,
            hrelease', hfinish, finishRoundResultCodeAt, finishRoundResultCode,
            releasedState, lifecycleFailureOfCode_code]
      | ok result =>
          rcases result with ⟨state, memory⟩
          simp [releaseAndFinishCodeFromReleaseAndFinishCodes,
            releaseAndFinishResultCode, DeclaredFollowerLocalRound.releaseAndFinish,
            hrelease', hfinish, finishRoundResultCodeAt, finishRoundResultCode,
            releasedState, localMemoryCodeOfCode, lifecycleFailureOfCode_code]

/-- Decoding the combined result code with the original post-service buffer
recovers the complete actual state and memory on success and preserves every
failure constructor. -/
theorem releaseAndFinishResultCodeAt_reconstruct {p : Parameters}
    (rate : RateInput p) (i : Fin (p.m - 1))
    (row : CompletePublicTable.CompleteRow p) (time : Fin p.T)
    (feedback : Fin (D p + 1)) (preCode postCode : FollowerStateCode p rate)
    (memoryCode : LocalMemoryCode p) {n m : ℕ}
    (preSkeleton : BufferSkeletonCode p n) (postSkeleton : BufferSkeletonCode p m)
    (preValues : SavedScalarFamily n) (postValues : SavedScalarFamily m) :
    releaseAndFinishResultOfCode rate (bufferFromSkeletonAndScalars postSkeleton postValues)
        (releaseAndFinishResultCodeAt rate i row time feedback preCode postCode memoryCode
          preSkeleton postSkeleton preValues postValues) =
      DeclaredFollowerLocalRound.releaseAndFinish rate i row time
        (FollowerDownMeasurability.feedbackAtGrid p feedback)
        (followerStateOfCode rate preCode
          (bufferFromSkeletonAndScalars preSkeleton preValues))
        (localMemoryOfCode memoryCode)
        (followerStateOfCode rate postCode
          (bufferFromSkeletonAndScalars postSkeleton postValues)) := by
  exact FollowerLifecycleMeasurability.releaseAndFinishResultCodeAt_reconstruct
    rate i row time feedback preCode postCode memoryCode preSkeleton postSkeleton
    preValues postValues

/-- Joint measurability of the actual combined release and final proposal
read. This is derived by splitting on the countable returned release code,
then applying the independently proved standalone finish measurability. -/
theorem measurable_releaseAndFinishResultCodeAt {p : Parameters}
    (rate : RateInput p) (i : Fin (p.m - 1))
    (preCode postCode : FollowerStateCode p rate) (memoryCode : LocalMemoryCode p)
    {n m : ℕ} (preSkeleton : BufferSkeletonCode p n)
    (postSkeleton : BufferSkeletonCode p m) :
    Measurable (fun input : ReleaseInput p n m =>
      releaseAndFinishResultCodeAt rate i input.1.1.1 input.1.1.2 input.1.2
        preCode postCode memoryCode preSkeleton postSkeleton input.2.1 input.2.2) := by
  let releaseMap := fun input : ReleaseInput p n m =>
    releaseAfterServiceResultCodeAt rate i input.1.1.1 input.1.1.2 input.1.2
      preCode postCode preSkeleton postSkeleton input.2.1 input.2.2
  have hrelease : Measurable releaseMap :=
    measurable_releaseAfterServiceResultCodeAt rate i preCode postCode
      preSkeleton postSkeleton
  let finishBase : ReleaseInput p n m → FinishRoundInput p m :=
    fun (input : ReleaseInput p n m) => ((input.1.1.1, input.1.1.2), input.2.2)
  have hfinishBase : Measurable finishBase := by
    have hrow : Measurable (fun input : ReleaseInput p n m => input.1.1.1) :=
      measurable_fst.comp (measurable_fst.comp measurable_fst)
    have htime : Measurable (fun input : ReleaseInput p n m => input.1.1.2) :=
      measurable_snd.comp (measurable_fst.comp measurable_fst)
    have hpost : Measurable (fun input : ReleaseInput p n m => input.2.2) :=
      measurable_snd.comp measurable_snd
    exact (hrow.prodMk htime).prodMk hpost
  let compose : ReleaseAfterServiceResultCode p rate × ReleaseInput p n m →
      ReleaseAndFinishResultCode p rate := fun z =>
        releaseAndFinishCodeFromReleaseAndFinishCodes rate z.2.1.1.1 z.2.1.1.2
          memoryCode postSkeleton z.2.2.2 z.1
  have hcompose : Measurable compose := by
    apply measurable_from_prod_countable_right
    intro code
    cases code with
    | failure _ => exact measurable_const
    | success stateCode =>
        have hfinish : Measurable (fun input : ReleaseInput p n m =>
            finishRoundResultCodeAt rate input.1.1.1 input.1.1.2 stateCode
              memoryCode postSkeleton input.2.2) := by
          exact (measurable_finishRoundResultCodeAt rate stateCode memoryCode
            postSkeleton).comp hfinishBase
        have hmap : Measurable (fun code : FinishRoundResultCode p rate =>
            match code with
            | .failure reason =>
                ReleaseAndFinishResultCode.failure (.finish (lifecycleFailureOfCode reason))
            | .success state memory => ReleaseAndFinishResultCode.success state memory) :=
          Measurable.of_discrete
        change Measurable ((fun code : FinishRoundResultCode p rate =>
          match code with
          | .failure reason =>
              ReleaseAndFinishResultCode.failure (.finish (lifecycleFailureOfCode reason))
          | .success state memory => ReleaseAndFinishResultCode.success state memory) ∘
          (fun input : ReleaseInput p n m =>
            finishRoundResultCodeAt rate input.1.1.1 input.1.1.2 stateCode
              memoryCode postSkeleton input.2.2))
        exact (hmap.comp hfinish)
  have hpair : Measurable (fun input : ReleaseInput p n m =>
      (releaseMap input, input)) := hrelease.prodMk measurable_id
  have hderived : Measurable (compose ∘ fun input => (releaseMap input, input)) :=
    hcompose.comp hpair
  have hEq : (fun input : ReleaseInput p n m =>
      releaseAndFinishResultCodeAt rate i input.1.1.1 input.1.1.2 input.1.2
        preCode postCode memoryCode preSkeleton postSkeleton input.2.1 input.2.2) =
      compose ∘ fun input => (releaseMap input, input) := by
    funext input
    simpa [compose, releaseMap] using (releaseAndFinishResultCodeAt_eq_from_codes rate i
      input.1.1.1 input.1.1.2 input.1.2 preCode postCode memoryCode
      preSkeleton postSkeleton input.2.1 input.2.2)
  rw [hEq]
  exact hderived

/-- Arbitrary-base composition for the standalone finish producer. Every map
into the complete row, time, and original scalar family has its own explicit
measurability premise. -/
theorem measurable_finishRoundResultCodeAt_comp {p : Parameters}
    (rate : RateInput p) (stateCode : FollowerStateCode p rate)
    (memoryCode : LocalMemoryCode p) {n : ℕ}
    (skeleton : BufferSkeletonCode p n) {Ω : Type*} [MeasurableSpace Ω]
    (row : Ω → CompletePublicTable.CompleteRow p) (time : Ω → Fin p.T)
    (values : Ω → SavedScalarFamily n)
    (hrow : Measurable row) (htime : Measurable time) (hvalues : Measurable values) :
    Measurable (fun ω => finishRoundResultCodeAt rate (row ω) (time ω)
      stateCode memoryCode skeleton (values ω)) := by
  have hinputs : Measurable (fun ω => ((row ω, time ω), values ω)) :=
    (hrow.prodMk htime).prodMk hvalues
  exact (measurable_finishRoundResultCodeAt rate stateCode memoryCode skeleton).comp hinputs

/-- Arbitrary-base composition for the two-buffer actual release producer.
The row, time, finite feedback, and both scalar-family maps are all explicit. -/
theorem measurable_releaseAfterServiceResultCodeAt_comp {p : Parameters}
    (rate : RateInput p) (i : Fin (p.m - 1)) (preCode postCode : FollowerStateCode p rate)
    {n m : ℕ} (preSkeleton : BufferSkeletonCode p n)
    (postSkeleton : BufferSkeletonCode p m) {Ω : Type*} [MeasurableSpace Ω]
    (row : Ω → CompletePublicTable.CompleteRow p) (time : Ω → Fin p.T)
    (feedback : Ω → Fin (D p + 1)) (preValues : Ω → SavedScalarFamily n)
    (postValues : Ω → SavedScalarFamily m)
    (hrow : Measurable row) (htime : Measurable time)
    (hfeedback : Measurable feedback) (hpreValues : Measurable preValues)
    (hpostValues : Measurable postValues) :
    Measurable (fun ω => releaseAfterServiceResultCodeAt rate i (row ω) (time ω)
      (feedback ω) preCode postCode preSkeleton postSkeleton
      (preValues ω) (postValues ω)) := by
  have hinputs : Measurable (fun ω =>
      (((row ω, time ω), feedback ω), (preValues ω, postValues ω))) :=
    ((hrow.prodMk htime).prodMk hfeedback).prodMk (hpreValues.prodMk hpostValues)
  exact (measurable_releaseAfterServiceResultCodeAt rate i preCode postCode
    preSkeleton postSkeleton).comp hinputs

/-- Arbitrary-base composition for the actual combined release and finish
producer, with the same complete row and both independently supplied original
scalar families. -/
theorem measurable_releaseAndFinishResultCodeAt_comp {p : Parameters}
    (rate : RateInput p) (i : Fin (p.m - 1))
    (preCode postCode : FollowerStateCode p rate) (memoryCode : LocalMemoryCode p)
    {n m : ℕ} (preSkeleton : BufferSkeletonCode p n)
    (postSkeleton : BufferSkeletonCode p m) {Ω : Type*} [MeasurableSpace Ω]
    (row : Ω → CompletePublicTable.CompleteRow p) (time : Ω → Fin p.T)
    (feedback : Ω → Fin (D p + 1)) (preValues : Ω → SavedScalarFamily n)
    (postValues : Ω → SavedScalarFamily m)
    (hrow : Measurable row) (htime : Measurable time)
    (hfeedback : Measurable feedback) (hpreValues : Measurable preValues)
    (hpostValues : Measurable postValues) :
    Measurable (fun ω => releaseAndFinishResultCodeAt rate i (row ω) (time ω)
      (feedback ω) preCode postCode memoryCode preSkeleton postSkeleton
      (preValues ω) (postValues ω)) := by
  have hinputs : Measurable (fun ω =>
      (((row ω, time ω), feedback ω), (preValues ω, postValues ω))) :=
    ((hrow.prodMk htime).prodMk hfeedback).prodMk (hpreValues.prodMk hpostValues)
  exact (measurable_releaseAndFinishResultCodeAt rate i preCode postCode memoryCode
    preSkeleton postSkeleton).comp hinputs

private theorem completeRowProposalBit_eq_of_currentTimeControl_eq
    (p : Parameters) (eta : ℝ) (row row' : CompletePublicTable.CompleteRow p)
    (time : Fin p.T) (hcurrent : row.2 time = row'.2 time) :
    FollowerCutoffScan.completeRowProposalBit p eta row time =
      FollowerCutoffScan.completeRowProposalBit p eta row' time := by
  change FollowerCutoffScan.thresholdProposalBit
      ((row.2 time).1 ContinuousControlSlice.Label.prop)
      (FollowerCutoffScan.proposalHazard p eta) =
    FollowerCutoffScan.thresholdProposalBit
      ((row'.2 time).1 ContinuousControlSlice.Label.prop)
      (FollowerCutoffScan.proposalHazard p eta)
  exact congrArg (fun control : ContinuousLearningRows.TimeControl p =>
    FollowerCutoffScan.thresholdProposalBit
      (control.1 ContinuousControlSlice.Label.prop)
      (FollowerCutoffScan.proposalHazard p eta)) hcurrent

/-- Equal current `TimeControl` at the same time gives the same actual
standalone finish code. The operation reads only that row's current proposal
coordinate and never scans an older row entry. -/
theorem finishRoundResultCodeAt_eq_of_currentTimeControl_eq {p : Parameters}
    (rate : RateInput p) (stateCode : FollowerStateCode p rate)
    (memoryCode : LocalMemoryCode p) {n : ℕ}
    (skeleton : BufferSkeletonCode p n)
    (row row' : CompletePublicTable.CompleteRow p) (time : Fin p.T)
    (values : SavedScalarFamily n) (hcurrent : row.2 time = row'.2 time) :
    finishRoundResultCodeAt rate row time stateCode memoryCode skeleton values =
      finishRoundResultCodeAt rate row' time stateCode memoryCode skeleton values := by
  unfold finishRoundResultCodeAt
  have hbit := completeRowProposalBit_eq_of_currentTimeControl_eq p rate.eta.val
    row row' time hcurrent
  unfold ActiveFollowerLifecycle.finishRound
  rw [hbit]

/-- Equal current `TimeControl` at the same time gives the same pending
release code when the row, own feedback, both state codes, skeletons, and
original scalar families are otherwise fixed. -/
theorem releaseAfterServiceResultCodeAt_eq_of_currentTimeControl_eq {p : Parameters}
    (rate : RateInput p) (i : Fin (p.m - 1))
    (preCode postCode : FollowerStateCode p rate) (time : Fin p.T)
    {n m : ℕ} (preSkeleton : BufferSkeletonCode p n)
    (postSkeleton : BufferSkeletonCode p m)
    (row row' : CompletePublicTable.CompleteRow p) (feedback : Fin (D p + 1))
    (preValues : SavedScalarFamily n) (postValues : SavedScalarFamily m)
    (hcurrent : row.2 time = row'.2 time) :
    releaseAfterServiceResultCodeAt rate i row time feedback preCode postCode
      preSkeleton postSkeleton preValues postValues =
    releaseAfterServiceResultCodeAt rate i row' time feedback preCode postCode
      preSkeleton postSkeleton preValues postValues := by
  have hpublic : ActiveFollowerLifecycle.publicRowOfCompleteRow row time =
      ActiveFollowerLifecycle.publicRowOfCompleteRow row' time := by
    unfold ActiveFollowerLifecycle.publicRowOfCompleteRow
    rw [hcurrent]
  unfold releaseAfterServiceResultCodeAt
  rw [hpublic]

/-- Equal current `TimeControl` at the same time and identical local inputs
give the same combined actual release/finish code. Both operations inspect
only the supplied current time slice. -/
theorem releaseAndFinishResultCodeAt_eq_of_currentTimeControl_eq {p : Parameters}
    (rate : RateInput p) (i : Fin (p.m - 1))
    (preCode postCode : FollowerStateCode p rate) (memoryCode : LocalMemoryCode p)
    (time : Fin p.T) {n m : ℕ} (preSkeleton : BufferSkeletonCode p n)
    (postSkeleton : BufferSkeletonCode p m)
    (row row' : CompletePublicTable.CompleteRow p) (feedback : Fin (D p + 1))
    (preValues : SavedScalarFamily n) (postValues : SavedScalarFamily m)
    (hcurrent : row.2 time = row'.2 time) :
    releaseAndFinishResultCodeAt rate i row time feedback preCode postCode memoryCode
      preSkeleton postSkeleton preValues postValues =
    releaseAndFinishResultCodeAt rate i row' time feedback preCode postCode memoryCode
      preSkeleton postSkeleton preValues postValues := by
  unfold releaseAndFinishResultCodeAt
  have hpublic : ActiveFollowerLifecycle.publicRowOfCompleteRow row time =
      ActiveFollowerLifecycle.publicRowOfCompleteRow row' time := by
    unfold ActiveFollowerLifecycle.publicRowOfCompleteRow
    rw [hcurrent]
  have hbit := completeRowProposalBit_eq_of_currentTimeControl_eq p rate.eta.val
    row row' time hcurrent
  have hfinish : ∀ state,
      ActiveFollowerLifecycle.finishRound rate.eta time row state
        (localMemoryOfCode memoryCode) =
      ActiveFollowerLifecycle.finishRound rate.eta time row' state
        (localMemoryOfCode memoryCode) := by
    intro state
    unfold ActiveFollowerLifecycle.finishRound
    rw [hbit]
  have hresult : DeclaredFollowerLocalRound.releaseAndFinish rate i row time
      (FollowerDownMeasurability.feedbackAtGrid p feedback)
      (followerStateOfCode rate preCode
        (bufferFromSkeletonAndScalars preSkeleton preValues))
      (localMemoryOfCode memoryCode)
      (followerStateOfCode rate postCode
        (bufferFromSkeletonAndScalars postSkeleton postValues)) =
    DeclaredFollowerLocalRound.releaseAndFinish rate i row' time
      (FollowerDownMeasurability.feedbackAtGrid p feedback)
      (followerStateOfCode rate preCode
        (bufferFromSkeletonAndScalars preSkeleton preValues))
      (localMemoryOfCode memoryCode)
      (followerStateOfCode rate postCode
        (bufferFromSkeletonAndScalars postSkeleton postValues)) := by
    unfold DeclaredFollowerLocalRound.releaseAndFinish
    rw [hpublic]
    cases hrel : ActiveFollowerLifecycle.releaseAfterService rate.eta i time
        (ActiveFollowerLifecycle.publicRowOfCompleteRow row' time)
        (FollowerDownMeasurability.feedbackAtGrid p feedback)
        (followerStateOfCode rate preCode
          (bufferFromSkeletonAndScalars preSkeleton preValues))
        (followerStateOfCode rate postCode
          (bufferFromSkeletonAndScalars postSkeleton postValues)) with
    | error reason => simp [hrel]
    | ok released =>
        simp only [hrel]
        rw [hfinish released]
  exact congrArg (releaseAndFinishResultCode rate) hresult

end Bandits.Support.FollowerReleaseFinishMeasurability

end
