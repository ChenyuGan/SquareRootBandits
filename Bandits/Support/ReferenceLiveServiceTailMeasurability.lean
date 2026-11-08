/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceActivePhysicalStepMeasurability

/-!
# Joint coordinates for the live service, confirmation, and finish suffix

Sources: `sources/zip4/manuscript/06_interruptions.tex:256-296` and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:6-14,28-60`.

The suffix starts after the single recorder call. Its recorder result is an
independent primitive coordinate. It then performs the existing service pass,
confirmation update, and finish-round operation in source order, retaining
their actual failure branches. The unconditional joint Borel theorem uses the
original payload Borel space and the accepted canonical coordinator encoding.
Whole-observation decoding and the same-input factorization are proved on all
branches. The recorder producer, full step, horizon and manuscript theorems
remain outside this internal suffix result.

The sole direct project dependency was checked against
`private-audit-archive/turn-00134-dependency-evidence.json`,
`turn-00134-publication.json`, and `delta-verified-dependencies.json` in that
same directory. Its exact SHA-256 is
`11b431bc05c6971b331016537f4e67f457e80a9c45d76940874cb30d37c6b314`.
All 17 pinned source hashes were rechecked against `sources/manifest.json`
and the absolute `turn-00134-source-integrity.json` evidence.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.CompletePublicTable
open Bandits.Support.CoordinatorPhaseClock
open Bandits.Support.CoordinatorLiveChoiceRecorderStep
open Bandits.Support.CoordinatorLiveServiceFinish
open Bandits.Support.CoordinatorLocalArmChoice
open Bandits.Support.CoordinatorRecordingMeasurability
open Bandits.Support.CoordinatorUpReception
open Bandits.Support.LaterAssignmentStartMeasurability

namespace Bandits.Support.ReferenceLiveServiceTailMeasurability

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

local instance tailStartRoundMeasurableSpace :
    MeasurableSpace (CoordinatorPhaseClock.StartRoundResult p) := ⊤
local instance tailStartRoundDiscreteMeasurableSpace :
    DiscreteMeasurableSpace (CoordinatorPhaseClock.StartRoundResult p) :=
  ⟨fun _ => trivial⟩

/-- Total finite encoding of the existing live failure enumeration. -/
private def liveFailureCode : CoordinatorLiveServiceFinish.Failure → Fin 25
  | .prepareClockRejected => 0
  | .prepareClockTransition => 1
  | .preparePayloadClockMismatch => 2
  | .prepareGridBoundaryMismatch => 3
  | .prepareScoreDomainFailure => 4
  | .prepareNotLive => 5
  | .prepareChoiceDomainFailure => 6
  | .prepareRecorderBoundaryFailure => 7
  | .prepareComplementEnvelopeFailure => 8
  | .queueInputDomainFailure => 9
  | .previousServiceInputDomainFailure => 10
  | .recorderRejected => 11
  | .arrivalOutputDomainFailure => 12
  | .serviceOutputDomainFailure => 13
  | .scoreOutputDomainFailure => 14
  | .queueOutputDomainFailure => 15
  | .confirmationRejected => 16
  | .finishInvalidProposalParameter => 17
  | .finishInvalidClockRegisters => 18
  | .finishIncompatibleStartTime => 19
  | .finishMissingPriorProposal => 20
  | .finishStalePriorProposal => 21
  | .finishInvalidNewGridBoundary => 22
  | .finishNoLiveAssignment => 23
  | .finishIncompatibleFinishTime => 24

private theorem liveFailureCode_injective : Function.Injective liveFailureCode := by
  intro a b h
  cases a <;> cases b <;> simp [liveFailureCode] at h ⊢

private def coordinatorFailureCode : ReferenceActivePhysicalStep.CoordinatorFailure →
    Unit ⊕ (Fin 25 ⊕ (Option CoordinatorPhaseClock.ClockFailure × Fin 8))
  | .dispatchRejected => .inl ()
  | .live reason => .inr (.inl (liveFailureCode reason))
  | .collection reason => .inr (.inr
      (CoordinatorCollectionRunMeasurabilityRepair.failureCode reason))

private theorem coordinatorFailureCode_injective : Function.Injective coordinatorFailureCode := by
  intro a b h
  cases a with
  | dispatchRejected =>
    cases b <;> simp [coordinatorFailureCode] at h ⊢
  | live a =>
    cases b with
    | dispatchRejected => simp [coordinatorFailureCode] at h
    | collection b => simp [coordinatorFailureCode] at h
    | live b =>
      have hab : liveFailureCode a = liveFailureCode b := by
        simpa only [coordinatorFailureCode, Sum.inr.injEq, Sum.inl.injEq] using h
      exact congrArg ReferenceActivePhysicalStep.CoordinatorFailure.live
        (liveFailureCode_injective hab)
  | collection a =>
    cases b with
    | dispatchRejected => simp [coordinatorFailureCode] at h
    | live b => simp [coordinatorFailureCode] at h
    | collection b =>
      have hab : CoordinatorCollectionRunMeasurabilityRepair.failureCode a =
          CoordinatorCollectionRunMeasurabilityRepair.failureCode b := by
        simpa only [coordinatorFailureCode, Sum.inr.injEq] using h
      exact congrArg ReferenceActivePhysicalStep.CoordinatorFailure.collection
        (CoordinatorCollectionRunMeasurabilityRepair.failureCode_injective hab)

local instance tailCoordinatorFailureCountable :
    Countable ReferenceActivePhysicalStep.CoordinatorFailure :=
  coordinatorFailureCode_injective.countable

local instance tailCoordinatorFailureMeasurableSpace :
    MeasurableSpace ReferenceActivePhysicalStep.CoordinatorFailure := ⊤

abbrev LiveDiscrete (p : ConstructorDimensions.Parameters) :=
  ReferenceActivePhysicalStepMeasurability.LiveDiscrete p
abbrev RecorderCode (p : ConstructorDimensions.Parameters) :=
  CoordinatorRecordingMeasurability.OutputCode p
abbrev Bank (p : ConstructorDimensions.Parameters) :=
  CoordinatorUpReception.UpDecoderBank p

local instance tailBankDiscreteMeasurableSpace : DiscreteMeasurableSpace (Bank p) :=
  ⟨fun _ => trivial⟩

private theorem measurableSet_option_singleton {α : Type*}
    [MeasurableSpace α] [MeasurableSingletonClass α] (a : Option α) :
    MeasurableSet ({a} : Set (Option α)) := by
  let e := Equiv.optionEquivSumPUnit α
  have he : Measurable e := comap_measurable _
  have hset : ({a} : Set (Option α)) = e ⁻¹' {e a} := by
    ext x
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    exact ⟨congrArg e, fun h => e.injective h⟩
  rw [hset]
  apply he
  cases h : e a with
  | inl value =>
    simpa only [Set.image_singleton] using
      (measurableSet_singleton value).inl_image (β := PUnit)
  | inr value =>
    simpa only [Set.image_singleton] using
      (measurableSet_singleton value).inr_image (α := α)

local instance tailOptionLiveMeasurableSingletonClass :
    MeasurableSingletonClass (Option (LiveDiscrete p)) :=
  ⟨measurableSet_option_singleton⟩

local instance tailOptionRecorderMeasurableSingletonClass :
    MeasurableSingletonClass (Option (RecorderCode p)) :=
  ⟨measurableSet_option_singleton⟩

/-- The payload's countable state that can affect this suffix. The real anchor
remains in `Payload`; its derived exponents and auxiliary arm are measured
separately on the accepted payload carrier. -/
abbrev PayloadTailDiscreteCode (p : ConstructorDimensions.Parameters) :=
  ℕ × (Fin p.T × (Finset (Fin p.K) ×
    ((Fin p.K → ℕ) × ((Fin p.K → ℕ) × Fin p.K))))

def payloadTailDiscreteCode
    (payload : ReferenceActivePhysicalStep.Payload rate) :
    PayloadTailDiscreteCode p :=
  (payload.n, (payload.sigma, (payload.slowSet.1,
    (payload.queues,
      (AssignmentPayloadDerivedMeasurability.inputExponent payload,
        AssignmentPayloadDerivedMeasurability.inputAuxiliary payload)))))

private theorem measurable_payloadTailDiscreteCode :
    Measurable (payloadTailDiscreteCode (p := p) (rate := rate)) := by
  have hobs : Measurable
      (LaterAssignmentStartMeasurability.payloadObservation
        (p := p) (eta := rate.eta)) := comap_measurable _
  have hfields := AssignmentPayloadDerivedMeasurability.measurable_inputDerivedFields
    (p := p) (eta := rate.eta)
  have hderived : Measurable (fun payload : ReferenceActivePhysicalStep.Payload rate =>
      (AssignmentPayloadDerivedMeasurability.inputExponent payload,
        AssignmentPayloadDerivedMeasurability.inputAuxiliary payload)) := by
    exact measurable_snd.comp (measurable_snd.comp hfields)
  have hcodeObs : Measurable (fun payload : ReferenceActivePhysicalStep.Payload rate =>
      ((LaterAssignmentStartMeasurability.payloadObservation payload).1,
        ((LaterAssignmentStartMeasurability.payloadObservation payload).2.1,
          ((LaterAssignmentStartMeasurability.payloadObservation payload).2.2.1,
            ((LaterAssignmentStartMeasurability.payloadObservation payload).2.2.2.2,
              (AssignmentPayloadDerivedMeasurability.inputExponent payload,
                AssignmentPayloadDerivedMeasurability.inputAuxiliary payload)))))) :=
    (measurable_fst.comp hobs).prodMk
    ((measurable_fst.comp (measurable_snd.comp hobs)).prodMk
      ((measurable_fst.comp
          (measurable_snd.comp (measurable_snd.comp hobs))).prodMk
        ((measurable_snd.comp (measurable_snd.comp
          (measurable_snd.comp (measurable_snd.comp hobs)))).prodMk hderived)))
  have hcodeFields : Measurable (fun payload : ReferenceActivePhysicalStep.Payload rate =>
      (payload.n, (payload.sigma, (payload.slowSet.1,
        (payload.queues,
          (AssignmentPayloadDerivedMeasurability.inputExponent payload,
            AssignmentPayloadDerivedMeasurability.inputAuxiliary payload)))))) := by
    simpa [LaterAssignmentStartMeasurability.payloadObservation] using hcodeObs
  change Measurable (fun payload : ReferenceActivePhysicalStep.Payload rate =>
      (payload.n, (payload.sigma, (payload.slowSet.1,
        (payload.queues,
          (AssignmentPayloadDerivedMeasurability.inputExponent payload,
            AssignmentPayloadDerivedMeasurability.inputAuxiliary payload))))))
  exact hcodeFields

private theorem payload_downWord_eq_of_code_eq
    {payload₁ payload₂ : ReferenceActivePhysicalStep.Payload rate}
    (hcode : payloadTailDiscreteCode payload₁ = payloadTailDiscreteCode payload₂)
    (i : ActiveRoundActions.Follower p.m) :
    payload₁.downWord i = payload₂.downWord i := by
  simp only [payloadTailDiscreteCode, Prod.mk.injEq] at hcode
  rcases hcode with ⟨_, h⟩
  rcases h with ⟨hsigma, h⟩
  rcases h with ⟨hslow, h⟩
  rcases h with ⟨hqueues, h⟩
  rcases h with ⟨hexponent, haux⟩
  have hslowSet : payload₁.slowSet = payload₂.slowSet := Subtype.ext hslow
  have hassigned : payload₁.assignment.assigned i = payload₂.assignment.assigned i := by
    change CanonicalAssignmentVector.followerArm p.two_le_m payload₁.slowSet i =
      CanonicalAssignmentVector.followerArm p.two_le_m payload₂.slowSet i
    exact congrArg (fun slowSet : CanonicalOrientedSetLaw.SlowSet p.K p.m =>
      CanonicalAssignmentVector.followerArm p.two_le_m slowSet i) hslowSet
  have hauxiliary : payload₁.assignment.auxiliary = payload₂.assignment.auxiliary := haux
  have hfields : (payload₁.downRecord i).val = (payload₂.downRecord i).val := by
    rw [payload₁.downRecord_fields, payload₂.downRecord_fields]
    ext
    · simp [hsigma]
    · simp [hassigned]
    · simp [hauxiliary]
    · rw [hassigned]
      exact congrFun hexponent (payload₂.assignment.assigned i)
    · rw [hassigned]
      exact congrFun hqueues (payload₂.assignment.assigned i)
  have hrecord : payload₁.downRecord i = payload₂.downRecord i := Subtype.ext hfields
  simp [AssignmentStartPayload.Input.downWord, hrecord]

/-- A countable measurable control suffices when the output is constant on
its exact fibers. No decoding default or representative is introduced. -/
private theorem measurable_of_countable_control
    {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [Countable β] [MeasurableSingletonClass β]
    (control : α → β) (output : α → γ) (hc : Measurable control)
    (hf : ∀ x y, control x = control y → output x = output y) :
    Measurable output := by
  classical
  intro s _
  have heq : output ⁻¹' s =
      ⋃ b : {b : β // ∃ x, control x = b ∧ output x ∈ s},
        control ⁻¹' {b.val} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_singleton_iff]
    constructor
    · intro hx
      exact ⟨⟨control x, x, rfl, hx⟩, rfl⟩
    · rintro ⟨b, hb⟩
      obtain ⟨y, hy, hys⟩ := b.property
      rw [hf x y (hb.trans hy.symm)]
      exact hys
  rw [heq]
  exact MeasurableSet.iUnion fun b => hc (measurableSet_singleton b.val)

abbrev TailControlCode (p : ConstructorDimensions.Parameters) :=
  PublicDiscreteDraws.Slot ×
    (ActiveRoundActions.Follower p.m × (AffineChannelLaw.Bit × Bool))

abbrev TailRowTime (p : ConstructorDimensions.Parameters) :=
  CompletePublicTable.CompleteRow p × Fin p.T

private theorem measurable_payloadCurrentDownHash (i : ActiveRoundActions.Follower p.m) :
    Measurable (fun z : ReferenceActivePhysicalStep.Payload rate ×
        ContinuousLearningRows.TimeControl p =>
      CoordinatorLocalArmChoice.currentDownHash z.1 z.2 i) := by
  apply measurable_of_countable_control
    (fun z : ReferenceActivePhysicalStep.Payload rate × ContinuousLearningRows.TimeControl p =>
      (payloadTailDiscreteCode z.1, z.2.2 (CoordinatorLocalArmChoice.downChannel i)))
    _ ((measurable_payloadTailDiscreteCode.comp measurable_fst).prodMk
      ((measurable_pi_apply (CoordinatorLocalArmChoice.downChannel i)).comp
        (measurable_snd.comp measurable_snd)))
  intro x y h
  obtain ⟨hp, hs⟩ := Prod.mk.inj h
  have hw := payload_downWord_eq_of_code_eq hp i
  simp only [CoordinatorLocalArmChoice.currentDownHash,
    CoordinatorLocalArmChoice.storedDownFlatWord, hs, hw]

private theorem measurable_payloadSelectedDownHash :
    Measurable (fun z : ReferenceActivePhysicalStep.Payload rate ×
        ContinuousLearningRows.TimeControl p =>
      CoordinatorLocalArmChoice.currentDownHash z.1 z.2
        (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K z.2.1)) := by
  classical
  apply measurable_to_countable'
  intro b
  have hdecomp :
      {z : ReferenceActivePhysicalStep.Payload rate ×
          ContinuousLearningRows.TimeControl p |
        CoordinatorLocalArmChoice.currentDownHash z.1 z.2
          (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K z.2.1) = b} =
      ⋃ i : ActiveRoundActions.Follower p.m,
        {z | PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K z.2.1 = i ∧
          CoordinatorLocalArmChoice.currentDownHash z.1 z.2 i = b} := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · intro hb
      exact ⟨PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K z.2.1,
        rfl, hb⟩
    · rintro ⟨i, hi, hb⟩
      rw [hi]
      exact hb
  change MeasurableSet {z : ReferenceActivePhysicalStep.Payload rate ×
    ContinuousLearningRows.TimeControl p |
      CoordinatorLocalArmChoice.currentDownHash z.1 z.2
        (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K z.2.1) = b}
  rw [hdecomp]
  exact MeasurableSet.iUnion fun i => by
    have hselectedMap : Measurable (fun z : ReferenceActivePhysicalStep.Payload rate ×
        ContinuousLearningRows.TimeControl p =>
        PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K z.2.1) :=
      (PublicDiscreteDraws.measurable_selectedFollowerDraw p.two_le_m p.m_lt_K).comp
        (measurable_fst.comp measurable_snd)
    have hselected : MeasurableSet {z : ReferenceActivePhysicalStep.Payload rate ×
        ContinuousLearningRows.TimeControl p |
        PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K z.2.1 = i} :=
      hselectedMap (measurableSet_singleton i)
    have hhash : MeasurableSet {z : ReferenceActivePhysicalStep.Payload rate ×
        ContinuousLearningRows.TimeControl p |
        CoordinatorLocalArmChoice.currentDownHash z.1 z.2 i = b} :=
      (measurable_payloadCurrentDownHash (p := p) (rate := rate) i)
        (measurableSet_singleton b)
    exact hselected.inter hhash

private theorem measurable_tailRowTimeEval :
    Measurable (fun rt : TailRowTime p => rt.1.2 rt.2) := by
  have heval : Measurable (fun z : ContinuousLearningRows.LearningRow p × Fin p.T =>
      z.1 z.2) := by
    apply measurable_from_prod_countable_left
    intro t
    exact measurable_pi_apply t
  exact heval.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)

def tailControlCode
    (z : ReferenceActivePhysicalStep.Payload rate × TailRowTime p) : TailControlCode p :=
  let control := z.2.1.2 z.2.2
  (PublicDiscreteDraws.slotDraw control.1,
    (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K control.1,
      (CoordinatorLocalArmChoice.currentDownHash z.1 control
        (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K control.1),
        FollowerCutoffScan.completeRowProposalBit p rate.eta.val z.2.1 z.2.2)))

private theorem measurable_tailControlCode :
    Measurable (tailControlCode (p := p) (rate := rate)) := by
  let control := fun z : ReferenceActivePhysicalStep.Payload rate × TailRowTime p =>
    z.2.1.2 z.2.2
  have hcontrol : Measurable control := measurable_tailRowTimeEval.comp measurable_snd
  have hslice : Measurable (fun z : ReferenceActivePhysicalStep.Payload rate ×
      TailRowTime p => (control z).1) := (measurable_fst.comp hcontrol)
  have hslot := PublicDiscreteDraws.measurable_slotDraw.comp hslice
  have hselected := (PublicDiscreteDraws.measurable_selectedFollowerDraw
    p.two_le_m p.m_lt_K).comp hslice
  have hhash := measurable_payloadSelectedDownHash (p := p) (rate := rate) |>.comp
    (measurable_fst.prodMk hcontrol)
  have hproposal : Measurable (fun z : ReferenceActivePhysicalStep.Payload rate ×
      TailRowTime p =>
        FollowerCutoffScan.completeRowProposalBit p rate.eta.val z.2.1 z.2.2) :=
    (FollowerReleaseFinishMeasurability.measurable_completeRowProposalBitAt
      p rate.eta.val).comp measurable_snd
  change Measurable (fun z : ReferenceActivePhysicalStep.Payload rate × TailRowTime p =>
    (PublicDiscreteDraws.slotDraw (control z).1,
      (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K (control z).1,
        (CoordinatorLocalArmChoice.currentDownHash z.1 (control z)
          (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K (control z).1),
          FollowerCutoffScan.completeRowProposalBit p rate.eta.val z.2.1 z.2.2))))
  exact hslot.prodMk (hselected.prodMk (hhash.prodMk hproposal))

/-- Product coordinates for the actual post-recorder suffix. The payload and
the original complete row retain their existing Borel spaces; every other
runtime coordinate is explicit. -/
abbrev LiveServiceTailDiscreteCoordinates (p : ConstructorDimensions.Parameters) :=
  LiveDiscrete p ×
    (CoordinatorPhaseClock.StartRoundResult p ×
      (Bank p ×
        (Fin p.T × (Fin (D p + 1) × Option (RecorderCode p)))))

abbrev LiveServiceTailCoordinates (p : ConstructorDimensions.Parameters)
    (rate : ReferenceActivePhysicalStep.RateInput p) :=
  LiveServiceTailDiscreteCoordinates p ×
    (ReferenceActivePhysicalStep.Payload rate × CompletePublicTable.CompleteRow p)

def tailLiveCode (z : LiveServiceTailCoordinates (p := p) (rate := rate)) := z.1.1
def tailStarted (z : LiveServiceTailCoordinates (p := p) (rate := rate)) := z.1.2.1
def tailBank (z : LiveServiceTailCoordinates (p := p) (rate := rate)) := z.1.2.2.1
def tailTime (z : LiveServiceTailCoordinates (p := p) (rate := rate)) := z.1.2.2.2.1
def tailObservation (z : LiveServiceTailCoordinates (p := p) (rate := rate)) := z.1.2.2.2.2.1
def tailRecorderCode (z : LiveServiceTailCoordinates (p := p) (rate := rate)) := z.1.2.2.2.2.2
def tailPayload (z : LiveServiceTailCoordinates (p := p) (rate := rate)) := z.2.1
def tailRow (z : LiveServiceTailCoordinates (p := p) (rate := rate)) := z.2.2

/-- Apply the literal source-ordered suffix to an arbitrary lossless recorder
result. No recorder validity or success premise is supplied. -/
abbrev LiveRuntime :=
  Σ r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta,
    CoordinatorLiveServiceFinish.OwnedRegisters r × (Fin (p.m - 1) → ℕ)

def decodeLiveRuntime (payload : ReferenceActivePhysicalStep.Payload rate)
    (code : LiveDiscrete p) : LiveRuntime (p := p) (rate := rate) :=
  ⟨ReferenceActivePhysicalStepMeasurability.decodeLiveRegisters payload code,
    (ReferenceActivePhysicalStepMeasurability.decodeLiveOwned payload code,
      code.baseScores)⟩

def pendingToClockSet (pending : Finset (ActiveRoundActions.Follower p.m)) :
    Finset (Fin (p.m - 1)) := by
  simpa [ActiveRoundActions.Follower, PublicDiscreteDraws.followerCount] using pending

def pendingFromClockSet (pending : Finset (Fin (p.m - 1))) :
    Finset (ActiveRoundActions.Follower p.m) := by
  simpa [ActiveRoundActions.Follower, PublicDiscreteDraws.followerCount] using pending

private theorem decodeLiveRuntime_eq
    (payload : ReferenceActivePhysicalStep.Payload rate) (code : LiveDiscrete p) :
    decodeLiveRuntime payload code =
      ⟨{ payload := payload
         priorClock := ⟨code.clockSigma, code.clockCutoff, code.clockBoundary, code.clockProposal⟩
         pendingAtChoice := pendingFromClockSet code.pending
         time := code.time
         gridBoundary := code.gridBoundary
         complementScores := fun a => code.scores a.val },
       ({ queue := fun a => code.queues a.val
          previousService := fun a => code.previousServices a.val }, code.baseScores)⟩ := rfl

/-- Literal continuation on an actual live register bundle and an arbitrary
primitive recorder result. The checked service, confirmation, and finish
branches appear in the source order. -/
def liveServiceTailFromRuntime
    (runtime : LiveRuntime (p := p) (rate := rate))
    (bank : Bank p) (started : CoordinatorPhaseClock.StartRoundResult p)
    (time : Fin p.T) (row : CompletePublicTable.CompleteRow p)
    (observation : Fin (D p + 1)) (recorderCode : Option (RecorderCode p)) :
    ReferenceActivePhysicalStep.CoordinatorObservation p rate := by
  classical
  rcases runtime with ⟨r, ⟨q, base⟩⟩
  match CoordinatorRecordingMeasurability.decodeResult recorderCode with
  | none =>
      exact ReferenceActivePhysicalStep.coordinatorFailure bank
        (.live .recorderRejected) none none
  | some recording =>
      match CoordinatorLiveServiceFinish.servicePass r q recording with
      | .error reason =>
          exact ReferenceActivePhysicalStep.coordinatorFailure bank
            (.live reason) (some recording) none
      | .ok serviced =>
          match CoordinatorLocalArmChoice.confirmationUpdate r.payload
              started.pending
              (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
              time row observation with
          | none =>
              exact ReferenceActivePhysicalStep.coordinatorFailure bank
                (.live .confirmationRejected) (some recording) none
          | some pending =>
              match CoordinatorPhaseClock.finishRound p rate.eta.val
                  time started.clock (pendingToClockSet pending) row with
              | .error reason =>
                  exact ReferenceActivePhysicalStep.coordinatorFailure bank
                    (.live (CoordinatorLiveServiceFinish.finishFailureCode reason))
                    (some recording) none
              | .ok finished =>
                  let next : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta := {
                    payload := r.payload
                    priorClock := finished.clock
                    pendingAtChoice := pendingFromClockSet finished.pending
                    time := time
                    gridBoundary := finished.clock.g
                    complementScores := serviced.score }
                  exact ⟨.live next {
                    queue := serviced.queue
                    previousService := serviced.previousService }
                    base, bank, none, some recording, none⟩

private theorem confirmationInputsValid_iff
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (cutoff : Option (CoordinatorLocalArmChoice.Cutoff p)) (time : Fin p.T) :
    CoordinatorLocalArmChoice.ConfirmationInputsValid payload cutoff time ↔
      CoordinatorLocalArmChoice.assignmentStart payload ≤
        CoordinatorLocalArmChoice.sourceRound time ∧
      CoordinatorLocalArmChoice.assignmentStart payload ≤
        CoordinatorLocalArmChoice.cutoffRound cutoff :=
  ⟨fun h => ⟨h.time.assignment_started, h.time.cutoff_after_start⟩,
    fun h => CoordinatorLocalArmChoice.confirmationInputsValid_mk payload cutoff time h.1 h.2⟩

private theorem confirmationUpdate_eq_of_payload_control
    (payload₁ payload₂ : ReferenceActivePhysicalStep.Payload rate)
    (pending : Finset (ActiveRoundActions.Follower p.m))
    (cutoff : Option (CoordinatorLocalArmChoice.Cutoff p))
    (time : Fin p.T) (observation : Fin (D p + 1))
    (row₁ row₂ : CompletePublicTable.CompleteRow p)
    (hsigma : payload₁.sigma = payload₂.sigma)
    (hslot : PublicDiscreteDraws.slotDraw (row₁.2 time).1 =
      PublicDiscreteDraws.slotDraw (row₂.2 time).1)
    (hselected : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
      (row₁.2 time).1 = PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
        (row₂.2 time).1)
    (hhash : CoordinatorLocalArmChoice.currentDownHash payload₁ (row₁.2 time)
      (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
        (row₁.2 time).1) =
      CoordinatorLocalArmChoice.currentDownHash payload₂ (row₂.2 time)
        (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
          (row₂.2 time).1)) :
    CoordinatorLocalArmChoice.confirmationUpdate payload₁ pending cutoff time row₁ observation =
      CoordinatorLocalArmChoice.confirmationUpdate payload₂ pending cutoff time row₂ observation := by
  have hvalid : CoordinatorLocalArmChoice.ConfirmationInputsValid payload₁ cutoff time =
      CoordinatorLocalArmChoice.ConfirmationInputsValid payload₂ cutoff time := by
    apply propext
    simp only [confirmationInputsValid_iff, CoordinatorLocalArmChoice.assignmentStart, hsigma]
  have hhash' := hhash
  rw [hselected] at hhash'
  have hevent : CoordinatorLocalArmChoice.downConfirmationEvent payload₁ pending cutoff
      time (row₁.2 time) observation =
      CoordinatorLocalArmChoice.downConfirmationEvent payload₂ pending cutoff
        time (row₂.2 time) observation := by
    apply propext
    simp only [CoordinatorLocalArmChoice.downConfirmationEvent,
      CoordinatorLocalArmChoice.confirmationLive, CoordinatorLocalArmChoice.assignmentIsLive,
      CoordinatorLocalArmChoice.assignmentStart, hsigma, hslot, hselected, hhash']
  simp only [CoordinatorLocalArmChoice.confirmationUpdate,
    CoordinatorLocalArmChoice.confirmationUpdateCore]
  rw [hvalid, hevent, hselected]

private theorem finishRound_eq_of_proposalBit_eq
    (time : Fin p.T) (clock : CoordinatorPhaseClock.ClockRegisters p)
    (pending : Finset (ActiveRoundActions.Follower p.m))
    (row₁ row₂ : CompletePublicTable.CompleteRow p)
    (hproposal : FollowerCutoffScan.completeRowProposalBit p rate.eta.val row₁ time =
      FollowerCutoffScan.completeRowProposalBit p rate.eta.val row₂ time) :
    CoordinatorPhaseClock.finishRound p rate.eta.val time clock
        (pendingToClockSet pending) row₁ =
      CoordinatorPhaseClock.finishRound p rate.eta.val time clock
        (pendingToClockSet pending) row₂ := by
  unfold CoordinatorPhaseClock.finishRound
  rw [hproposal]


def liveServiceTailObservation
    (z : LiveServiceTailCoordinates (p := p) (rate := rate)) :
    ReferenceActivePhysicalStep.CoordinatorObservation p rate :=
  liveServiceTailFromRuntime (decodeLiveRuntime (tailPayload z) (tailLiveCode z))
    (tailBank z) (tailStarted z) (tailTime z) (tailRow z) (tailObservation z)
    (tailRecorderCode z)

/-- Discrete suffix data, with the unchanged continuous payload retained
separately for reconstruction. Every failure reason and recorder field stays
literal. The canonical whole code is provided below. -/
abbrev LiveServiceTailOutputCode (p : ConstructorDimensions.Parameters) :=
  Option (LiveDiscrete p) ×
    (Bank p ×
      (Option ReferenceActivePhysicalStep.CoordinatorFailure × Option (RecorderCode p)))

/-- The suffix data is countable; only the separately retained original
payload contributes a continuous output coordinate. -/
theorem liveServiceTailOutputCode_countable : Countable (LiveServiceTailOutputCode p) :=
  inferInstance

def encodeLiveServiceTailObservation
    (o : ReferenceActivePhysicalStep.CoordinatorObservation p rate) :
    LiveServiceTailOutputCode p :=
  ((match o.configuration with
    | .live registers owned base =>
        some (ReferenceActivePhysicalStepMeasurability.encodeLive registers owned base)
    | _ => none),
    (o.upDecoderBank,
      (o.failure, CoordinatorRecordingMeasurability.encodeResult o.recording)))

def decodeLiveServiceTailObservation
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (code : LiveServiceTailOutputCode p) :
    ReferenceActivePhysicalStep.CoordinatorObservation p rate :=
  ⟨(code.1.elim .dagger fun liveCode =>
      .live
        (ReferenceActivePhysicalStepMeasurability.decodeLiveRegisters payload liveCode)
        (ReferenceActivePhysicalStepMeasurability.decodeLiveOwned payload liveCode)
        liveCode.baseScores),
    code.2.1, code.2.2.1,
    CoordinatorRecordingMeasurability.decodeResult code.2.2.2, none⟩

def liveServiceTailCode
    (z : LiveServiceTailCoordinates (p := p) (rate := rate)) :
    LiveServiceTailOutputCode p :=
  encodeLiveServiceTailObservation (liveServiceTailObservation z)

private theorem liveServiceTailCode_eq_of_discrete_control
    (discrete : LiveServiceTailDiscreteCoordinates p)
    (payload₁ payload₂ : ReferenceActivePhysicalStep.Payload rate)
    (row₁ row₂ : CompletePublicTable.CompleteRow p)
    (hn : payload₁.n = payload₂.n) (hsigma : payload₁.sigma = payload₂.sigma)
    (hslow : payload₁.slowSet = payload₂.slowSet)
    (hcontrol : tailControlCode (payload₁, row₁, discrete.2.2.2.1) =
      tailControlCode (payload₂, row₂, discrete.2.2.2.1)) :
    liveServiceTailCode (discrete, payload₁, row₁) =
      liveServiceTailCode (discrete, payload₂, row₂) := by
  classical
  simp only [tailControlCode, Prod.mk.injEq] at hcontrol
  obtain ⟨hslot, hselected, hhash, hproposal⟩ := hcontrol
  have hconfirmation := confirmationUpdate_eq_of_payload_control payload₁ payload₂
    discrete.2.1.pending
    (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p discrete.2.1.clock.u)
    discrete.2.2.2.1 discrete.2.2.2.2.1 row₁ row₂ hsigma hslot hselected hhash
  cases payload₁ with
  | mk cap₁ n₁ scale₁ sigma₁ slow₁ anchor₁ pos₁ queues₁ bound₁ =>
    cases payload₂ with
    | mk cap₂ n₂ scale₂ sigma₂ slow₂ anchor₂ pos₂ queues₂ bound₂ =>
      dsimp only at hn hsigma hslow
      subst n₂
      subst sigma₂
      subst slow₂
      unfold liveServiceTailCode liveServiceTailObservation
      simp only [tailPayload, tailLiveCode, tailBank, tailStarted, tailTime, tailRow,
        tailObservation, tailRecorderCode, decodeLiveRuntime_eq, liveServiceTailFromRuntime]
      rw [hconfirmation]
      cases hrec : CoordinatorRecordingMeasurability.decodeResult discrete.2.2.2.2.2 with
      | none => rfl
      | some recording =>
        dsimp +instances only [CoordinatorLiveServiceFinish.servicePass,
          CoordinatorLiveServiceFinish.OwnedRegisters.queueDomainValid,
          CoordinatorLiveServiceFinish.OwnedRegisters.previousServiceDomainValid,
          CoordinatorLiveServiceFinish.complementArrival]
        by_cases hq : ∀ j : CanonicalFastSampling.FastArm slow₁,
            discrete.1.queues j.val ≤ p.T * D p
        · simp only [dite_eq_left hq]
          by_cases hp : ∀ j : CanonicalFastSampling.FastArm slow₁,
              discrete.1.previousServices j.val ≤ D p
          · simp only [dite_eq_left hp]
            by_cases ha : ∀ j : CanonicalFastSampling.FastArm slow₁,
                (if recording.gateArm = some j.val then recording.rawArrival else 0) ≤ D p
            · simp only [dite_eq_left ha]
              by_cases hv : ∀ j : CanonicalFastSampling.FastArm slow₁,
                  CappedService.service (4 * n₁) (discrete.1.queues j.val)
                    (if recording.gateArm = some j.val then recording.rawArrival else 0) ≤ D p
              · simp only [dite_eq_left hv]
                by_cases hs : ∀ j : CanonicalFastSampling.FastArm slow₁,
                    discrete.1.scores j.val +
                      CappedService.service (4 * n₁) (discrete.1.queues j.val)
                        (if recording.gateArm = some j.val then recording.rawArrival else 0) ≤
                      p.T * D p
                · simp only [dite_eq_left hs]
                  by_cases ho : ∀ j : CanonicalFastSampling.FastArm slow₁,
                      CappedService.residual (4 * n₁) (discrete.1.queues j.val)
                        (if recording.gateArm = some j.val then recording.rawArrival else 0) ≤
                      p.T * D p
                  · simp only [dite_eq_left ho]
                    split
                    · rfl
                    · rename_i pending hconfirm
                      have hf := finishRound_eq_of_proposalBit_eq (rate := rate)
                        discrete.2.2.2.1 discrete.2.1.clock pending row₁ row₂ hproposal
                      rw [hf]
                      split <;> rfl
                  · simp only [dite_eq_right ho]
                · simp only [dite_eq_right hs]
              · simp only [dite_eq_right hv]
            · simp only [dite_eq_right ha]
          · simp only [dite_eq_right hp]
        · simp only [dite_eq_right hq]

/-- Joint Borel measurability on the entire product of original payload,
live registers, retained start result, bank, time, complete row, grid feedback,
and an independent lossless recorder-result code. No operation-success,
reachability, or recorder-producer hypothesis is used. -/
theorem measurable_liveServiceTailCode :
    Measurable (liveServiceTailCode (p := p) (rate := rate)) := by
  have hpayload : Measurable (tailPayload (p := p) (rate := rate)) :=
    measurable_fst.comp measurable_snd
  have hrow : Measurable (tailRow (p := p) (rate := rate)) :=
    measurable_snd.comp measurable_snd
  have htime : Measurable (tailTime (p := p) (rate := rate)) :=
    measurable_fst.comp (measurable_snd.comp (measurable_snd.comp
      (measurable_snd.comp measurable_fst)))
  have hcontrol : Measurable (fun z : LiveServiceTailCoordinates p rate =>
      tailControlCode (tailPayload z, tailRow z, tailTime z)) :=
    measurable_tailControlCode.comp (hpayload.prodMk (hrow.prodMk htime))
  have hread : Measurable (fun z : LiveServiceTailCoordinates p rate =>
      (z.1, payloadTailDiscreteCode (tailPayload z),
        tailControlCode (tailPayload z, tailRow z, tailTime z))) :=
    measurable_fst.prodMk
      ((measurable_payloadTailDiscreteCode.comp hpayload).prodMk hcontrol)
  apply measurable_of_countable_control _ _ hread
  rintro ⟨dx, px, rx⟩ ⟨dy, py, ry⟩ h
  obtain ⟨hd, hp, ht⟩ := Prod.mk.inj h |>.imp_right Prod.mk.inj
  cases hd
  simp only [tailPayload, payloadTailDiscreteCode, Prod.mk.injEq] at hp
  obtain ⟨hn, hsigma, hslow, _, _, _⟩ := hp
  exact liveServiceTailCode_eq_of_discrete_control dx px py rx ry
    hn hsigma (Subtype.ext hslow) ht

/-- Assemble only separately supplied primitive maps on any measurable
parameter space. This is an input product, not a new protocol state. -/
def assembleLiveServiceTailCoordinates {Ω : Type*}
    (live : Ω → LiveDiscrete p) (started : Ω → StartRoundResult p)
    (bank : Ω → Bank p) (time : Ω → Fin p.T)
    (observation : Ω → Fin (D p + 1)) (recorder : Ω → Option (RecorderCode p))
    (payload : Ω → ReferenceActivePhysicalStep.Payload rate)
    (row : Ω → CompleteRow p) (ω : Ω) : LiveServiceTailCoordinates p rate :=
  ((live ω, started ω, bank ω, time ω, observation ω, recorder ω), (payload ω, row ω))

theorem measurable_assembleLiveServiceTailCoordinates {Ω : Type*} [MeasurableSpace Ω]
    (live : Ω → LiveDiscrete p) (started : Ω → StartRoundResult p)
    (bank : Ω → Bank p) (time : Ω → Fin p.T)
    (observation : Ω → Fin (D p + 1)) (recorder : Ω → Option (RecorderCode p))
    (payload : Ω → ReferenceActivePhysicalStep.Payload rate) (row : Ω → CompleteRow p)
    (hlive : Measurable live) (hstarted : Measurable started)
    (hbank : Measurable bank) (htime : Measurable time)
    (hobservation : Measurable observation) (hrecorder : Measurable recorder)
    (hpayload : Measurable payload) (hrow : Measurable row) :
    Measurable (assembleLiveServiceTailCoordinates live started bank time observation
      recorder payload row) :=
  (hlive.prodMk (hstarted.prodMk (hbank.prodMk
    (htime.prodMk (hobservation.prodMk hrecorder))))).prodMk (hpayload.prodMk hrow)

/-- Compose the unconditional joint theorem with separately measurable
primitive maps; `hrecorder` concerns only the supplied lossless finite code,
not the unproved physical producer. -/
theorem measurable_liveServiceTailCode_comp {Ω : Type*} [MeasurableSpace Ω]
    (live : Ω → LiveDiscrete p) (started : Ω → StartRoundResult p)
    (bank : Ω → Bank p) (time : Ω → Fin p.T)
    (observation : Ω → Fin (D p + 1)) (recorder : Ω → Option (RecorderCode p))
    (payload : Ω → ReferenceActivePhysicalStep.Payload rate) (row : Ω → CompleteRow p)
    (hlive : Measurable live) (hstarted : Measurable started)
    (hbank : Measurable bank) (htime : Measurable time)
    (hobservation : Measurable observation) (hrecorder : Measurable recorder)
    (hpayload : Measurable payload) (hrow : Measurable row) :
    Measurable (fun ω => liveServiceTailCode
      (assembleLiveServiceTailCoordinates live started bank time observation
        recorder payload row ω)) :=
  measurable_liveServiceTailCode.comp
    (measurable_assembleLiveServiceTailCoordinates live started bank time observation
      recorder payload row hlive hstarted hbank htime hobservation hrecorder hpayload hrow)

theorem liveServiceTailObservation_up_none
    (z : LiveServiceTailCoordinates (p := p) (rate := rate)) :
    (liveServiceTailObservation z).up = none := by
  classical
  unfold liveServiceTailObservation liveServiceTailFromRuntime decodeLiveRuntime
  simp only [ReferenceActivePhysicalStep.coordinatorFailure]
  split <;> rename_i hrecord
  · rfl
  · split <;> rename_i hservice
    · rfl
    · split <;> rename_i hconfirmation
      · rfl
      · split <;> rfl

private theorem decode_encode_liveServiceTailFromRuntime
    (runtime : LiveRuntime (p := p) (rate := rate))
    (bank : Bank p) (started : CoordinatorPhaseClock.StartRoundResult p)
    (time : Fin p.T) (row : CompletePublicTable.CompleteRow p)
    (observation : Fin (D p + 1)) (recorderCode : Option (RecorderCode p)) :
    decodeLiveServiceTailObservation runtime.1.payload
        (encodeLiveServiceTailObservation
          (liveServiceTailFromRuntime runtime bank started time row observation recorderCode)) =
      liveServiceTailFromRuntime runtime bank started time row observation recorderCode := by
  classical
  rcases runtime with ⟨r, q, base⟩
  unfold liveServiceTailFromRuntime
  cases hrecord : CoordinatorRecordingMeasurability.decodeResult recorderCode with
  | none =>
      simp [ReferenceActivePhysicalStep.coordinatorFailure,
        encodeLiveServiceTailObservation, decodeLiveServiceTailObservation]
      rw [CoordinatorRecordingMeasurability.decodeResult_encodeResult]
  | some recording =>
      cases hservice : CoordinatorLiveServiceFinish.servicePass r q recording with
      | error reason =>
          simp [hservice, ReferenceActivePhysicalStep.coordinatorFailure,
            encodeLiveServiceTailObservation, decodeLiveServiceTailObservation]
          rw [CoordinatorRecordingMeasurability.decodeResult_encodeResult]
      | ok serviced =>
          cases hconfirmation : CoordinatorLocalArmChoice.confirmationUpdate r.payload
              started.pending
              (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
              time row observation with
          | none =>
              simp [hservice, hconfirmation,
                ReferenceActivePhysicalStep.coordinatorFailure,
                encodeLiveServiceTailObservation, decodeLiveServiceTailObservation]
              rw [CoordinatorRecordingMeasurability.decodeResult_encodeResult]
          | some pending =>
              cases hfinish : CoordinatorPhaseClock.finishRound p rate.eta.val time
                  started.clock (pendingToClockSet pending) row with
              | error reason =>
                  simp [hservice, hconfirmation, hfinish,
                    ReferenceActivePhysicalStep.coordinatorFailure,
                    CoordinatorLiveServiceFinish.finishFailureCode,
                    encodeLiveServiceTailObservation, decodeLiveServiceTailObservation]
                  rw [CoordinatorRecordingMeasurability.decodeResult_encodeResult]
              | ok finished =>
                  let next : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta := {
                    payload := r.payload
                    priorClock := finished.clock
                    pendingAtChoice := pendingFromClockSet finished.pending
                    time := time
                    gridBoundary := finished.clock.g
                    complementScores := serviced.score }
                  have hconfig :
                      ReferenceActivePhysicalStep.CoordinatorConfiguration.live
                          (ReferenceActivePhysicalStepMeasurability.decodeLiveRegisters r.payload
                            (ReferenceActivePhysicalStepMeasurability.encodeLive next
                              { queue := serviced.queue
                                previousService := serviced.previousService } base))
                          (ReferenceActivePhysicalStepMeasurability.decodeLiveOwned r.payload
                            (ReferenceActivePhysicalStepMeasurability.encodeLive next
                              { queue := serviced.queue
                                previousService := serviced.previousService } base))
                          (ReferenceActivePhysicalStepMeasurability.encodeLive next
                            { queue := serviced.queue
                              previousService := serviced.previousService } base).baseScores =
                        .live next
                          { queue := serviced.queue
                            previousService := serviced.previousService } base := by
                    change ReferenceActivePhysicalStepMeasurability.decodeCoordinator
                        (ReferenceActivePhysicalStepMeasurability.encodeCoordinator
                          (.live next
                            { queue := serviced.queue
                              previousService := serviced.previousService } base)) = _
                    exact ReferenceActivePhysicalStepMeasurability.decodeCoordinator_encodeCoordinator _
                  simp [hservice, hconfirmation, hfinish, next,
                    encodeLiveServiceTailObservation, decodeLiveServiceTailObservation,
                    CoordinatorRecordingMeasurability.decodeResult_encodeResult,
                    hconfig]

/-- The code decodes to the exact whole observation for every input. -/
theorem decode_liveServiceTailCode
    (z : LiveServiceTailCoordinates (p := p) (rate := rate)) :
    decodeLiveServiceTailObservation (tailPayload z) (liveServiceTailCode z) =
      liveServiceTailObservation z := by
  exact decode_encode_liveServiceTailFromRuntime
    (decodeLiveRuntime (tailPayload z) (tailLiveCode z)) (tailBank z)
    (tailStarted z) (tailTime z) (tailRow z) (tailObservation z) (tailRecorderCode z)

/-- The canonical coordinator STORE code and all remaining possible suffix
observation data. UP is identically absent, as proved above. -/
abbrev LiveServiceTailWholeCode (p : ConstructorDimensions.Parameters)
    (rate : ReferenceActivePhysicalStep.RateInput p) :=
  ReferenceActivePhysicalStepMeasurability.CoordinatorCode p rate ×
    (Bank p × (Option ReferenceActivePhysicalStep.CoordinatorFailure × Option (RecorderCode p)))

def encodeLiveServiceTailWholeObservation
    (o : ReferenceActivePhysicalStep.CoordinatorObservation p rate) :
    LiveServiceTailWholeCode p rate :=
  (ReferenceActivePhysicalStepMeasurability.encodeCoordinator o.configuration,
    o.upDecoderBank, o.failure, CoordinatorRecordingMeasurability.encodeResult o.recording)

def decodeLiveServiceTailWholeObservation (code : LiveServiceTailWholeCode p rate) :
    ReferenceActivePhysicalStep.CoordinatorObservation p rate :=
  ⟨ReferenceActivePhysicalStepMeasurability.decodeCoordinator code.1,
    code.2.1, code.2.2.1, CoordinatorRecordingMeasurability.decodeResult code.2.2.2, none⟩

def liveServiceTailWholeCode (z : LiveServiceTailCoordinates p rate) :
    LiveServiceTailWholeCode p rate :=
  encodeLiveServiceTailWholeObservation (liveServiceTailObservation z)

private def coordinatorCodeFromTailData (payload : ReferenceActivePhysicalStep.Payload rate)
    (live : Option (LiveDiscrete p)) :
    ReferenceActivePhysicalStepMeasurability.CoordinatorCode p rate :=
  match live with
  | none => .inr (.inr (.inr ()))
  | some code => .inr (.inl (payload, code))

private theorem measurable_coordinatorCodeFromTailData :
    Measurable (fun z : ReferenceActivePhysicalStep.Payload rate × Option (LiveDiscrete p) =>
      coordinatorCodeFromTailData z.1 z.2) := by
  apply measurable_from_prod_countable_left
  intro code
  cases code with
  | none => exact measurable_const
  | some code =>
    exact measurable_inr.comp (measurable_inl.comp
      (measurable_id.prodMk (measurable_const (a := code))))

private theorem encodeRuntime_eq_wholeData
    (runtime : LiveRuntime (p := p) (rate := rate))
    (bank : Bank p) (started : StartRoundResult p) (time : Fin p.T) (row : CompleteRow p)
    (observation : Fin (D p + 1)) (recorder : Option (RecorderCode p)) :
    encodeLiveServiceTailWholeObservation
        (liveServiceTailFromRuntime runtime bank started time row observation recorder) =
      (coordinatorCodeFromTailData runtime.1.payload
        (encodeLiveServiceTailObservation
          (liveServiceTailFromRuntime runtime bank started time row observation recorder)).1,
       (encodeLiveServiceTailObservation
          (liveServiceTailFromRuntime runtime bank started time row observation recorder)).2) := by
  classical
  rcases runtime with ⟨r, q, base⟩
  unfold liveServiceTailFromRuntime
  dsimp only
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · split <;> rfl

private theorem liveServiceTailWholeCode_eq (z : LiveServiceTailCoordinates p rate) :
    liveServiceTailWholeCode z =
      (coordinatorCodeFromTailData (tailPayload z) (liveServiceTailCode z).1,
        (liveServiceTailCode z).2) :=
  encodeRuntime_eq_wholeData (decodeLiveRuntime (tailPayload z) (tailLiveCode z))
    (tailBank z) (tailStarted z) (tailTime z) (tailRow z) (tailObservation z) (tailRecorderCode z)

/-- Unconditional JOINT Borel result for the whole continuation observation:
the entire original payload is retained inside the accepted coordinator code,
and bank, exact failure reason, and recorder output are all retained. -/
theorem measurable_liveServiceTailWholeCode :
    Measurable (liveServiceTailWholeCode (p := p) (rate := rate)) := by
  have hpayload : Measurable (tailPayload (p := p) (rate := rate)) :=
    measurable_fst.comp measurable_snd
  have hconfig := measurable_coordinatorCodeFromTailData.comp
    (hpayload.prodMk (measurable_fst.comp measurable_liveServiceTailCode))
  have hdata := measurable_snd.comp (measurable_liveServiceTailCode (p := p) (rate := rate))
  have h := hconfig.prodMk hdata
  simpa only [Function.comp_def, ← liveServiceTailWholeCode_eq] using h

/-- The canonical whole code decodes to the very same full observation,
including every failure and the identically absent UP diagnostic. -/
theorem decode_liveServiceTailWholeCode (z : LiveServiceTailCoordinates p rate) :
    decodeLiveServiceTailWholeObservation (liveServiceTailWholeCode z) =
      liveServiceTailObservation z := by
  change decodeLiveServiceTailWholeObservation
    (encodeLiveServiceTailWholeObservation (liveServiceTailObservation z)) = _
  have hup := liveServiceTailObservation_up_none z
  generalize liveServiceTailObservation z = o at *
  cases o with
  | mk configuration bank failure recording up =>
    change up = none at hup
    subst up
    simp only [encodeLiveServiceTailWholeObservation,
      decodeLiveServiceTailWholeObservation,
      ReferenceActivePhysicalStepMeasurability.decodeCoordinator_encodeCoordinator,
      CoordinatorRecordingMeasurability.decodeResult_encodeResult]

/-- The whole-observation joint theorem composed only with independently
measurable primitive maps. No supplied suffix measurability is a premise. -/
theorem measurable_liveServiceTailWholeCode_comp {Ω : Type*} [MeasurableSpace Ω]
    (live : Ω → LiveDiscrete p) (started : Ω → StartRoundResult p)
    (bank : Ω → Bank p) (time : Ω → Fin p.T)
    (observation : Ω → Fin (D p + 1)) (recorder : Ω → Option (RecorderCode p))
    (payload : Ω → ReferenceActivePhysicalStep.Payload rate) (row : Ω → CompleteRow p)
    (hlive : Measurable live) (hstarted : Measurable started)
    (hbank : Measurable bank) (htime : Measurable time)
    (hobservation : Measurable observation) (hrecorder : Measurable recorder)
    (hpayload : Measurable payload) (hrow : Measurable row) :
    Measurable (fun ω => liveServiceTailWholeCode
      (assembleLiveServiceTailCoordinates live started bank time observation
        recorder payload row ω)) :=
  measurable_liveServiceTailWholeCode.comp
    (measurable_assembleLiveServiceTailCoordinates live started bank time observation
      recorder payload row hlive hstarted hbank htime hobservation hrecorder hpayload hrow)

/-- Independent coordinates of the canonical continuation, with the one
actual recorder output encoded losslessly. -/
def actualLiveServiceTailCoordinates
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ)
    (started : CoordinatorPhaseClock.StartRoundResult p) :
    LiveServiceTailCoordinates (p := p) (rate := rate) :=
  ((ReferenceActivePhysicalStepMeasurability.encodeLive r q base,
      (started,
        (x.state.upDecoderBank,
          (x.time,
            (prepared.coordinatorObservation,
              CoordinatorRecordingMeasurability.encodeResult
                (CoordinatorRecorderComplementBridge.run
                  (ReferenceActivePhysicalStep.liveRecordingInput prepared r started))))))),
    (r.payload, x.row))

private def liveConfigurationParts
    (configuration : ReferenceActivePhysicalStep.CoordinatorConfiguration p rate) :
    Option (Σ registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta,
      CoordinatorLiveServiceFinish.OwnedRegisters registers × (Fin (p.m - 1) → ℕ)) :=
  match configuration with
  | .live registers owned base => some ⟨registers, (owned, base)⟩
  | _ => none

/-- Factorization through the literal recorder complement result, for every
actual original continuation input. This identity makes no measurability claim
about that producer. -/
theorem liveServiceTail_reconstructs_actual
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ)
    (started : CoordinatorPhaseClock.StartRoundResult p) :
    decodeLiveServiceTailObservation (r.payload)
        (liveServiceTailCode (actualLiveServiceTailCoordinates prepared r q base started)) =
      ReferenceActivePhysicalStep.livePostChoice prepared r q base started := by
  change decodeLiveServiceTailObservation
      (tailPayload (actualLiveServiceTailCoordinates prepared r q base started))
      (liveServiceTailCode (actualLiveServiceTailCoordinates prepared r q base started)) =
    ReferenceActivePhysicalStep.livePostChoice prepared r q base started
  rw [decode_liveServiceTailCode]
  have hconfig :
      ReferenceActivePhysicalStep.CoordinatorConfiguration.live
          (ReferenceActivePhysicalStepMeasurability.decodeLiveRegisters r.payload
            (ReferenceActivePhysicalStepMeasurability.encodeLive r q base))
          (ReferenceActivePhysicalStepMeasurability.decodeLiveOwned r.payload
            (ReferenceActivePhysicalStepMeasurability.encodeLive r q base))
          (ReferenceActivePhysicalStepMeasurability.encodeLive r q base).baseScores =
        .live r q base := by
    change ReferenceActivePhysicalStepMeasurability.decodeCoordinator
        (ReferenceActivePhysicalStepMeasurability.encodeCoordinator (.live r q base)) =
      .live r q base
    exact ReferenceActivePhysicalStepMeasurability.decodeCoordinator_encodeCoordinator _
  have hparts := congrArg liveConfigurationParts hconfig
  simp only [liveConfigurationParts] at hparts
  have hdecoded :
      decodeLiveRuntime r.payload
          (ReferenceActivePhysicalStepMeasurability.encodeLive r q base) =
        (⟨r, (q, base)⟩ : LiveRuntime (p := p) (rate := rate)) := by
    apply Option.some.inj
    simpa [liveConfigurationParts, decodeLiveRuntime] using hparts
  have htail := congrArg
    (fun runtime => liveServiceTailFromRuntime runtime x.state.upDecoderBank started
      x.time x.row prepared.coordinatorObservation
      (CoordinatorRecordingMeasurability.encodeResult
        (CoordinatorRecorderComplementBridge.run
          (ReferenceActivePhysicalStep.liveRecordingInput prepared r started)))) hdecoded
  have hsource :
      liveServiceTailFromRuntime (⟨r, (q, base)⟩ : LiveRuntime (p := p) (rate := rate))
          x.state.upDecoderBank started x.time x.row prepared.coordinatorObservation
          (CoordinatorRecordingMeasurability.encodeResult
            (CoordinatorRecorderComplementBridge.run
              (ReferenceActivePhysicalStep.liveRecordingInput prepared r started))) =
        ReferenceActivePhysicalStep.livePostChoice prepared r q base started := by
    unfold liveServiceTailFromRuntime ReferenceActivePhysicalStep.livePostChoice
      ReferenceActivePhysicalStep.liveRecordingInput
    simp only [CoordinatorRecordingMeasurability.decodeResult_encodeResult]
    rfl
  change liveServiceTailFromRuntime
      (decodeLiveRuntime r.payload
        (ReferenceActivePhysicalStepMeasurability.encodeLive r q base))
      x.state.upDecoderBank started x.time x.row prepared.coordinatorObservation
      (CoordinatorRecordingMeasurability.encodeResult
        (CoordinatorRecorderComplementBridge.run
          (ReferenceActivePhysicalStep.liveRecordingInput prepared r started))) =
    ReferenceActivePhysicalStep.livePostChoice prepared r q base started
  exact htail.trans hsource

/-- Direct same-input identity at the literal physical recorder producer.
This is a factorization identity, not a measurability assertion about it. -/
theorem liveServiceTailFromRuntime_actual
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ) (started : StartRoundResult p) :
    liveServiceTailFromRuntime ⟨r, q, base⟩ x.state.upDecoderBank started
        x.time x.row prepared.coordinatorObservation
        (CoordinatorRecordingMeasurability.encodeResult
          (CoordinatorRecorderComplementBridge.run
            (ReferenceActivePhysicalStep.liveRecordingInput prepared r started))) =
      ReferenceActivePhysicalStep.livePostChoice prepared r q base started := by
  unfold liveServiceTailFromRuntime ReferenceActivePhysicalStep.livePostChoice
  rw [CoordinatorRecordingMeasurability.decodeResult_encodeResult]
  rfl

/-- Whole-observation decoder identification with the actual continuation,
for every original input and retained start result, without success assumptions. -/
theorem liveServiceTailWholeCode_reconstructs_actual
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ) (started : StartRoundResult p) :
    decodeLiveServiceTailWholeObservation
        (liveServiceTailWholeCode (actualLiveServiceTailCoordinates prepared r q base started)) =
      ReferenceActivePhysicalStep.livePostChoice prepared r q base started := by
  rw [decode_liveServiceTailWholeCode]
  exact (decode_liveServiceTailCode _).symm.trans
    (liveServiceTail_reconstructs_actual prepared r q base started)

end Bandits.Support.ReferenceLiveServiceTailMeasurability

end
