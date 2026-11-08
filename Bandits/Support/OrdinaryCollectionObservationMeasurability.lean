/-
Copyright (c) 2026 Bandits Lean regret formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bandits Lean regret formalization contributors
-/
module

public import Bandits.Support.OrdinaryCollectionPrimitiveMeasurability

/-!
# Borel code for the ordinary collection post-choice observation

The input is the product of the original bank, complete row, calendar time,
own arm, grid observation, payload, ledger, start result, and full real weight
vector. The output reuses the retained collection observation code. The
receiver is the ordinary unfiltered UP operation.

Mathematical evidence: `sources/zip4/manuscript/07_public_setup.tex:55-114`,
`sources/zip4/manuscript/06_interruptions.tex:240-296`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:6-14`,
`sources/zip4/manuscript/appendix_b_communication.tex:94-131`, and
`sources/zip4/manuscript/08_main_theorem.tex:67-75`.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Bandits.Support.OrdinaryCollectionObservationMeasurability

open OrdinaryCollectionPrimitiveMeasurability

variable {p : ConstructorDimensions.Parameters}
  {rate : ReferenceActivePhysicalStep.RateInput p}

/-- The original independent carriers for the ordinary collection tail,
including the full real weight vector. -/
abbrev CollectionPostChoiceInputs (p : ConstructorDimensions.Parameters)
    (rate : ReferenceActivePhysicalStep.RateInput p) :=
  CoordinatorUpReception.UpDecoderBank p ×
    (CompletePublicTable.CompleteRow p ×
      (Fin p.T ×
        (Fin p.K ×
          (Fin (ConstructorDimensions.D p + 1) ×
            (ReferenceActivePhysicalStep.Payload rate ×
              (ReferenceActivePhysicalStep.Ledger rate ×
                (CoordinatorPhaseClock.StartRoundResult p × (Fin p.K → ℝ))))))))

/-- Assemble the actual local continuation stages in source order. The
receiver read is total on the checked carrier; when ledger start fails its
fallback ledger is unused by `serviceObservation`. -/
def collectionServiceReadAtComponents
    (bank : CoordinatorUpReception.UpDecoderBank p)
    (row : CompletePublicTable.CompleteRow p) (time : Fin p.T)
    (arm : Fin p.K) (Y : Fin (ConstructorDimensions.D p + 1))
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (weights : Fin p.K → ℝ) :
    ReferenceCollectionServiceTailMeasurability.ServiceRead p rate := by
  let recording := collectionRecordingAtComponents row time arm Y payload started weights
  let ledgerStarted := ReferenceCollectionServiceTailMeasurability.serviceStart
    ledger time recording
  let receiverInputs : ReferenceUpReception.ReceptionLocalInputs rate :=
    (ReferenceCollectionServiceTailMeasurability.serviceReceptionLedger ledger ledgerStarted,
      (bank, (time, Y)))
  let received := CoordinatorUpMeasurability.receiveUpAtRow row receiverInputs time
  let ledgerFinished := ReferenceCollectionServiceTailMeasurability.serviceFinishLedger received
  let pending := ReferenceCollectionServiceTailMeasurability.serviceFinishPending ledgerFinished
  let clockFinished := collectionPhaseClockFinishAtComponents rate time started pending row
  exact (bank, (recording, (ledgerStarted,
    (received, (none, (ledgerFinished, clockFinished))))))

/-- Decode only the retained stage results through the established
`ServiceRead` reconstruction. No operation is rerun by this definition. -/
def collectionObservationAtComponents
    (bank : CoordinatorUpReception.UpDecoderBank p)
    (row : CompletePublicTable.CompleteRow p) (time : Fin p.T)
    (arm : Fin p.K) (Y : Fin (ConstructorDimensions.D p + 1))
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (weights : Fin p.K → ℝ) :
    ReferenceActivePhysicalStep.CoordinatorObservation p rate :=
  ReferenceCollectionServiceTailMeasurability.serviceObservation payload
    (collectionServiceReadAtComponents bank row time arm Y payload ledger started weights)

/-- The existing collection tail code applied to the retained local output. -/
def collectionObservationCodeAtComponents
    (bank : CoordinatorUpReception.UpDecoderBank p)
    (row : CompletePublicTable.CompleteRow p) (time : Fin p.T)
    (arm : Fin p.K) (Y : Fin (ConstructorDimensions.D p + 1))
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (weights : Fin p.K → ℝ) :
    ReferenceCollectionServiceTailMeasurability.CollectionTailCode p rate :=
  ReferenceCollectionServiceTailMeasurability.encodeCollectionObservation
    (collectionObservationAtComponents bank row time arm Y payload ledger started weights)

/-- The full-vector recorder is exactly the existing coordinator recorder
input restricted to the payload's actual fast complement. -/
theorem collectionRecordingAtComponents_eq_existingRun
    (row : CompletePublicTable.CompleteRow p) (time : Fin p.T)
    (arm : Fin p.K) (Y : Fin (ConstructorDimensions.D p + 1))
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (weights : Fin p.K → ℝ) :
    collectionRecordingAtComponents row time arm Y payload started weights =
      CoordinatorRecorderComplementBridge.run
        (OrdinaryCoordinatorPhysicalInterface.collectionRecordingInput
          row time arm Y payload started (fun a => weights a.val)) := by
  unfold collectionRecordingAtComponents
  rw [collectionRecordingInputAtComponents_eq_existing
    row time arm Y payload started weights (fun a => weights a.val)
      (fun _ => rfl)]

private theorem collectionPostChoice_congr_recordingInput
    (bank : CoordinatorUpReception.UpDecoderBank p)
    (row : CompletePublicTable.CompleteRow p) (time : Fin p.T)
    (arm : Fin p.K) (Y : Fin (ConstructorDimensions.D p + 1))
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (weights₁ weights₂ : CanonicalFastSampling.FastArm payload.slowSet → ℝ)
    (hinput :
      OrdinaryCoordinatorPhysicalInterface.collectionRecordingInput
        row time arm Y payload started weights₁ =
      OrdinaryCoordinatorPhysicalInterface.collectionRecordingInput
        row time arm Y payload started weights₂) :
    OrdinaryCoordinatorPhysicalInterface.collectionPostChoice bank row time arm Y
        payload ledger started weights₁ =
      OrdinaryCoordinatorPhysicalInterface.collectionPostChoice bank row time arm Y
        payload ledger started weights₂ := by
  unfold OrdinaryCoordinatorPhysicalInterface.collectionPostChoice
  rw [hinput]

private theorem collectionServiceObservation_eq_collectionFinish
    (bank : CoordinatorUpReception.UpDecoderBank p)
    (row : CompletePublicTable.CompleteRow p) (time : Fin p.T)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (recording : CoordinatorRecordingOperation.Output p)
    (ledgerStarted : ReferenceActivePhysicalStep.Ledger rate)
    (received : ReferenceCollectionServiceTailMeasurability.UpResult rate) :
    ReferenceCollectionServiceTailMeasurability.serviceObservation payload
        (bank, (some recording,
          (CoordinatorCollectionLedger.Checked.success ledgerStarted,
            (received, (none,
              (ReferenceCollectionServiceTailMeasurability.serviceFinishLedger received,
                collectionPhaseClockFinishAtComponents rate time started
                  (ReferenceCollectionServiceTailMeasurability.serviceFinishPending
                    (ReferenceCollectionServiceTailMeasurability.serviceFinishLedger received)) row)))))) =
      OrdinaryCoordinatorPhysicalInterface.collectionFinish bank row time payload started recording
        ({ result := received, diagnostic := none } : ReferenceActivePhysicalStep.UpCut p rate) := by
  cases received with
  | invalid =>
      simp [ReferenceCollectionServiceTailMeasurability.serviceObservation,
        OrdinaryCoordinatorPhysicalInterface.collectionFinish]
  | success pair | rejected pair =>
      rcases pair with ⟨receivedLedger, returnedBank⟩
      cases hfinish : CoordinatorCollectionLedger.finishRound receivedLedger with
      | invalid =>
          simp [ReferenceCollectionServiceTailMeasurability.serviceObservation,
            ReferenceCollectionServiceTailMeasurability.serviceFinishLedger,
            OrdinaryCoordinatorPhysicalInterface.collectionFinish, hfinish]
      | rejected rejectedLedger =>
          simp [ReferenceCollectionServiceTailMeasurability.serviceObservation,
            ReferenceCollectionServiceTailMeasurability.serviceFinishLedger,
            OrdinaryCoordinatorPhysicalInterface.collectionFinish, hfinish]
      | success finishedLedger =>
          cases hclock : collectionPhaseClockFinishAtComponents rate time started
              finishedLedger.pending row with
          | error reason =>
              simp [ReferenceCollectionServiceTailMeasurability.serviceObservation,
                ReferenceCollectionServiceTailMeasurability.serviceFinishLedger,
                ReferenceCollectionServiceTailMeasurability.serviceFinishPending,
                collectionPhaseClockFinishAtComponents,
                OrdinaryCoordinatorPhysicalInterface.collectionFinish, hfinish]
              rfl
          | ok clock =>
              simp [ReferenceCollectionServiceTailMeasurability.serviceObservation,
                ReferenceCollectionServiceTailMeasurability.serviceFinishLedger,
                ReferenceCollectionServiceTailMeasurability.serviceFinishPending,
                collectionPhaseClockFinishAtComponents,
                OrdinaryCoordinatorPhysicalInterface.collectionFinish, hfinish]
              rfl

/-- Exact pointwise factorization to the ordinary, unrestricted collection
post-choice operation, including every checked failure branch. -/
theorem collectionObservationAtComponents_eq_collectionPostChoice
    (bank : CoordinatorUpReception.UpDecoderBank p)
    (row : CompletePublicTable.CompleteRow p) (time : Fin p.T)
    (arm : Fin p.K) (Y : Fin (ConstructorDimensions.D p + 1))
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (weights : Fin p.K → ℝ) :
    collectionObservationAtComponents bank row time arm Y payload ledger started weights =
      OrdinaryCoordinatorPhysicalInterface.collectionPostChoice bank row time arm Y
        payload ledger started (fun a => weights a.val) := by
  classical
  have hrecording := collectionRecordingAtComponents_eq_existingRun
    row time arm Y payload started weights
  unfold collectionObservationAtComponents collectionServiceReadAtComponents
  rw [hrecording]
  unfold OrdinaryCoordinatorPhysicalInterface.collectionPostChoice
  cases hrecording' : CoordinatorRecorderComplementBridge.run
      (OrdinaryCoordinatorPhysicalInterface.collectionRecordingInput
        row time arm Y payload started (fun a => weights a.val)) with
  | none =>
      simp [ReferenceCollectionServiceTailMeasurability.serviceObservation]
  | some recorded =>
      let enabled := ReferenceActivePhysicalStep.collectionEnabled ledger time
      let raw := CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recorded
      cases hstart : CoordinatorCollectionLedger.startRound ledger (time.val + 1) enabled raw with
      | invalid =>
          simp [ReferenceCollectionServiceTailMeasurability.serviceObservation,
            ReferenceCollectionServiceTailMeasurability.serviceStart,
            enabled, raw, hstart]
      | rejected returned =>
          simp [ReferenceCollectionServiceTailMeasurability.serviceObservation,
            ReferenceCollectionServiceTailMeasurability.serviceStart,
            enabled, raw, hstart]
      | success ledgerStarted =>
          let receiverInputs : ReferenceUpReception.ReceptionLocalInputs rate :=
            (ledgerStarted, (bank, (time, Y)))
          let received := CoordinatorUpMeasurability.receiveUpAtRow row receiverInputs time
          have hobs := collectionServiceObservation_eq_collectionFinish
            bank row time payload started recorded ledgerStarted received
          simpa [ReferenceCollectionServiceTailMeasurability.serviceObservation,
            ReferenceCollectionServiceTailMeasurability.serviceStart,
            ReferenceCollectionServiceTailMeasurability.serviceReceptionLedger,
            ReferenceCollectionServiceTailMeasurability.serviceFinishLedger,
            ReferenceCollectionServiceTailMeasurability.serviceFinishPending,
            CoordinatorUpMeasurability.receiveUpAtRow,
            ReferenceUpReception.receptionInputAtRow,
            enabled, raw, hrecording', hstart, receiverInputs, received,
            OrdinaryCoordinatorPhysicalInterface.collectionFinish] using hobs

/-- The code is pointwise the existing retained encoding of the exact C
result. -/
theorem collectionObservationCodeAtComponents_eq_collectionPostChoice
    (bank : CoordinatorUpReception.UpDecoderBank p)
    (row : CompletePublicTable.CompleteRow p) (time : Fin p.T)
    (arm : Fin p.K) (Y : Fin (ConstructorDimensions.D p + 1))
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (weights : Fin p.K → ℝ) :
    collectionObservationCodeAtComponents bank row time arm Y payload ledger started weights =
      ReferenceCollectionServiceTailMeasurability.encodeCollectionObservation
        (OrdinaryCoordinatorPhysicalInterface.collectionPostChoice bank row time arm Y
          payload ledger started (fun a => weights a.val)) := by
  exact congrArg ReferenceCollectionServiceTailMeasurability.encodeCollectionObservation
    (collectionObservationAtComponents_eq_collectionPostChoice
      bank row time arm Y payload ledger started weights)

/-- Decode the retained code to the actual post-choice observation. The
decoder reads retained code fields and does not rerun any local operation. -/
theorem decode_collectionObservationCodeAtComponents
    (bank : CoordinatorUpReception.UpDecoderBank p)
    (row : CompletePublicTable.CompleteRow p) (time : Fin p.T)
    (arm : Fin p.K) (Y : Fin (ConstructorDimensions.D p + 1))
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (weights : Fin p.K → ℝ) :
    ReferenceCollectionServiceTailMeasurability.decodeCollectionObservation
        (collectionObservationCodeAtComponents bank row time arm Y payload ledger started weights) =
      OrdinaryCoordinatorPhysicalInterface.collectionPostChoice bank row time arm Y
        payload ledger started (fun a => weights a.val) := by
  calc
    _ = collectionObservationAtComponents bank row time arm Y payload ledger started weights := by
      change ReferenceCollectionServiceTailMeasurability.decodeCollectionObservation
        (ReferenceCollectionServiceTailMeasurability.encodeCollectionObservation
          (collectionObservationAtComponents bank row time arm Y payload ledger started weights)) = _
      exact ReferenceCollectionServiceTailMeasurability.decodeCollectionObservation_encodeCollectionObservation _
    _ = _ := collectionObservationAtComponents_eq_collectionPostChoice
      bank row time arm Y payload ledger started weights

/-- Exact specialization when the full vector extends an actual complement
weight function. -/
theorem collectionObservationCodeAtComponents_eq_of_complement_extension
    (bank : CoordinatorUpReception.UpDecoderBank p)
    (row : CompletePublicTable.CompleteRow p) (time : Fin p.T)
    (arm : Fin p.K) (Y : Fin (ConstructorDimensions.D p + 1))
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (weights : Fin p.K → ℝ)
    (complementWeights : CanonicalFastSampling.FastArm payload.slowSet → ℝ)
    (hextends : ∀ a, weights a.val = complementWeights a) :
    collectionObservationCodeAtComponents bank row time arm Y payload ledger started weights =
      ReferenceCollectionServiceTailMeasurability.encodeCollectionObservation
        (OrdinaryCoordinatorPhysicalInterface.collectionPostChoice bank row time arm Y
          payload ledger started complementWeights) := by
  calc
    collectionObservationCodeAtComponents bank row time arm Y payload ledger started weights =
        ReferenceCollectionServiceTailMeasurability.encodeCollectionObservation
          (OrdinaryCoordinatorPhysicalInterface.collectionPostChoice bank row time arm Y
            payload ledger started (fun a => weights a.val)) :=
      collectionObservationCodeAtComponents_eq_collectionPostChoice
        bank row time arm Y payload ledger started weights
    _ = ReferenceCollectionServiceTailMeasurability.encodeCollectionObservation
          (OrdinaryCoordinatorPhysicalInterface.collectionPostChoice bank row time arm Y
            payload ledger started complementWeights) := by
      apply congrArg ReferenceCollectionServiceTailMeasurability.encodeCollectionObservation
      apply collectionPostChoice_congr_recordingInput
      have hprojected := collectionRecordingInputAtComponents_eq_existing
        row time arm Y payload started weights (fun a => weights a.val) (fun _ => rfl)
      have hextended := collectionRecordingInputAtComponents_eq_existing
        row time arm Y payload started weights complementWeights hextends
      exact hprojected.symm.trans hextended

/-- Changing only the extension away from the actual fast complement leaves
the complete collection observation code unchanged. -/
theorem collectionObservationCodeAtComponents_eq_of_complement_agreement
    (bank : CoordinatorUpReception.UpDecoderBank p)
    (row : CompletePublicTable.CompleteRow p) (time : Fin p.T)
    (arm : Fin p.K) (Y : Fin (ConstructorDimensions.D p + 1))
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (weights₁ weights₂ : Fin p.K → ℝ)
    (hagrees : ∀ a : CanonicalFastSampling.FastArm payload.slowSet,
      weights₁ a.val = weights₂ a.val) :
    collectionObservationCodeAtComponents bank row time arm Y payload ledger started weights₁ =
      collectionObservationCodeAtComponents bank row time arm Y payload ledger started weights₂ := by
  calc
    collectionObservationCodeAtComponents bank row time arm Y payload ledger started weights₁ =
        ReferenceCollectionServiceTailMeasurability.encodeCollectionObservation
          (OrdinaryCoordinatorPhysicalInterface.collectionPostChoice bank row time arm Y
            payload ledger started (fun a => weights₁ a.val)) :=
      collectionObservationCodeAtComponents_eq_collectionPostChoice
        bank row time arm Y payload ledger started weights₁
    _ = ReferenceCollectionServiceTailMeasurability.encodeCollectionObservation
          (OrdinaryCoordinatorPhysicalInterface.collectionPostChoice bank row time arm Y
            payload ledger started (fun a => weights₂ a.val)) := by
      apply congrArg ReferenceCollectionServiceTailMeasurability.encodeCollectionObservation
      apply collectionPostChoice_congr_recordingInput
      unfold OrdinaryCoordinatorPhysicalInterface.collectionRecordingInput
      have hweights : (fun a : CanonicalFastSampling.FastArm payload.slowSet =>
          weights₁ a.val) = (fun a => weights₂ a.val) := funext hagrees
      rw [hweights]
    _ = collectionObservationCodeAtComponents bank row time arm Y payload ledger started weights₂ :=
      (collectionObservationCodeAtComponents_eq_collectionPostChoice
        bank row time arm Y payload ledger started weights₂).symm

private theorem measurable_finite_sections {Ω α β : Type*}
    [MeasurableSpace Ω] [Fintype α] [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [MeasurableSpace β]
    (index : Ω → α) (family : α → Ω → β) (hindex : Measurable index)
    (hfamily : ∀ a, Measurable (family a)) :
    Measurable (fun ω => family (index ω) ω) := by
  have hsections : Measurable (fun z : α × Ω => family z.1 z.2) :=
    measurable_from_prod_countable_right fun a => hfamily a
  exact hsections.comp (hindex.prodMk measurable_id)

/-- The literal service read is Borel from separately measurable original
primitive maps. Calendar time varies by finite measurable sections. -/
theorem measurable_collectionServiceReadAtComponents_comp {Ω : Type*}
    [MeasurableSpace Ω]
    (bank : Ω → CoordinatorUpReception.UpDecoderBank p)
    (row : Ω → CompletePublicTable.CompleteRow p) (time : Ω → Fin p.T)
    (arm : Ω → Fin p.K) (Y : Ω → Fin (ConstructorDimensions.D p + 1))
    (payload : Ω → ReferenceActivePhysicalStep.Payload rate)
    (ledger : Ω → ReferenceActivePhysicalStep.Ledger rate)
    (started : Ω → CoordinatorPhaseClock.StartRoundResult p)
    (weights : Ω → Fin p.K → ℝ)
    (hbank : Measurable bank) (hrow : Measurable row) (htime : Measurable time)
    (harm : Measurable arm) (hY : Measurable Y)
    (hpayload : Measurable payload) (hledger : Measurable ledger)
    (hstarted : Measurable started) (hweights : Measurable weights) :
    Measurable (fun ω => collectionServiceReadAtComponents (bank ω) (row ω)
      (time ω) (arm ω) (Y ω) (payload ω) (ledger ω) (started ω) (weights ω)) := by
  let recording := fun ω => collectionRecordingAtComponents (row ω) (time ω)
    (arm ω) (Y ω) (payload ω) (started ω) (weights ω)
  have hrecording := measurable_collectionRecordingAtComponents row time payload started
    weights arm Y hrow htime hpayload hstarted hweights harm hY
  let ledgerStarted := fun ω =>
    ReferenceCollectionServiceTailMeasurability.serviceStart (ledger ω) (time ω) (recording ω)
  have hledgerStarted : Measurable ledgerStarted := by
    exact (Measurable.of_discrete : Measurable
      (fun z : ReferenceActivePhysicalStep.Ledger rate ×
        (Fin p.T × Option (CoordinatorRecordingOperation.Output p)) =>
          ReferenceCollectionServiceTailMeasurability.serviceStart z.1 z.2.1 z.2.2)).comp
      (hledger.prodMk (htime.prodMk hrecording))
  let receptionLedger := fun ω =>
    ReferenceCollectionServiceTailMeasurability.serviceReceptionLedger
      (ledger ω) (ledgerStarted ω)
  have hReceptionLedger : Measurable receptionLedger := by
    exact (Measurable.of_discrete : Measurable
      (fun z : ReferenceActivePhysicalStep.Ledger rate ×
        ReferenceCollectionServiceTailMeasurability.CheckedLedger rate =>
          ReferenceCollectionServiceTailMeasurability.serviceReceptionLedger z.1 z.2)).comp
      (hledger.prodMk hledgerStarted)
  let receiverInputs (t : Fin p.T) : Ω →
      CoordinatorUpMeasurability.ReceptionLocalInputs p rate.eta.val rate.eta.property
        (ReferenceUpReception.sourceCap_forLedger rate) rate.n rate.n_scale :=
    fun ω => (receptionLedger ω, (bank ω, (t, Y ω)))
  have hreceiverInputs (t : Fin p.T) : Measurable (receiverInputs t) := by
    exact hReceptionLedger.prodMk
      (hbank.prodMk (measurable_const.prodMk hY))
  let UInput := CompletePublicTable.CompleteRow p ×
    CoordinatorUpMeasurability.ReceptionLocalInputs p rate.eta.val rate.eta.property
      (ReferenceUpReception.sourceCap_forLedger rate) rate.n rate.n_scale
  let receiverJoint (t : Fin p.T) : Ω → UInput :=
    fun ω => (row ω, receiverInputs t ω)
  have hreceiverJoint (t : Fin p.T) : Measurable (receiverJoint t) :=
    hrow.prodMk (hreceiverInputs t)
  let receiveSection (t : Fin p.T) (ω : Ω) :=
    CoordinatorUpMeasurability.receiveUpAtRow (receiverJoint t ω).1
      (receiverJoint t ω).2 t
  have hreceiveSection (t : Fin p.T) : Measurable (receiveSection t) := by
    change Measurable (fun ω =>
      CoordinatorUpMeasurability.receiveUpAtRow (receiverJoint t ω).1
        (receiverJoint t ω).2 t)
    have hU : Measurable (fun z : UInput =>
        CoordinatorUpMeasurability.receiveUpAtRow z.1 z.2 t) := by
      change Measurable (fun z : CompletePublicTable.CompleteRow p ×
          CoordinatorUpMeasurability.ReceptionLocalInputs p rate.eta.val rate.eta.property
            (ReferenceUpReception.sourceCap_forLedger rate) rate.n rate.n_scale =>
        CoordinatorUpMeasurability.receiveUpAtRow z.1 z.2 t)
      exact CoordinatorUpMeasurability.measurable_receiveUpAtRow
        (p := p) (eta := rate.eta.val) (heta := rate.eta.property)
        (hcap := ReferenceUpReception.sourceCap_forLedger rate)
        (n := rate.n) (hn := rate.n_scale) t
    exact hU.comp (hreceiverJoint t)
  let received := fun ω => receiveSection (time ω) ω
  have hreceived := measurable_finite_sections time receiveSection htime hreceiveSection
  let ledgerFinished := fun ω =>
    ReferenceCollectionServiceTailMeasurability.serviceFinishLedger (received ω)
  have hledgerFinished : Measurable ledgerFinished := by
    exact (Measurable.of_discrete : Measurable
      (fun u : ReferenceCollectionServiceTailMeasurability.UpResult rate =>
        ReferenceCollectionServiceTailMeasurability.serviceFinishLedger u)).comp hreceived
  let pending := fun ω =>
    ReferenceCollectionServiceTailMeasurability.serviceFinishPending (ledgerFinished ω)
  have hpending : Measurable pending := by
    exact (Measurable.of_discrete : Measurable
      (fun x : ReferenceCollectionServiceTailMeasurability.CheckedLedger rate =>
        ReferenceCollectionServiceTailMeasurability.serviceFinishPending x)).comp hledgerFinished
  have hclock := measurable_collectionPhaseClockFinishAtComponents (rate := rate)
    (started := started) (pending := pending) (time := time) (row := row)
    hstarted hpending htime hrow
  change Measurable (fun ω =>
    (bank ω, (recording ω, (ledgerStarted ω,
      (received ω, (none,
        (ledgerFinished ω,
          collectionPhaseClockFinishAtComponents rate (time ω) (started ω)
            (pending ω) (row ω))))))))
  exact hbank.prodMk (hrecording.prodMk (hledgerStarted.prodMk
    (hreceived.prodMk (measurable_const.prodMk (hledgerFinished.prodMk hclock)))))

/-- Borel composition of the retained observation code from separately
measurable original coordinates. -/
theorem measurable_collectionObservationCodeAtComponents_comp {Ω : Type*}
    [MeasurableSpace Ω]
    (bank : Ω → CoordinatorUpReception.UpDecoderBank p)
    (row : Ω → CompletePublicTable.CompleteRow p) (time : Ω → Fin p.T)
    (arm : Ω → Fin p.K) (Y : Ω → Fin (ConstructorDimensions.D p + 1))
    (payload : Ω → ReferenceActivePhysicalStep.Payload rate)
    (ledger : Ω → ReferenceActivePhysicalStep.Ledger rate)
    (started : Ω → CoordinatorPhaseClock.StartRoundResult p)
    (weights : Ω → Fin p.K → ℝ)
    (hbank : Measurable bank) (hrow : Measurable row) (htime : Measurable time)
    (harm : Measurable arm) (hY : Measurable Y)
    (hpayload : Measurable payload) (hledger : Measurable ledger)
    (hstarted : Measurable started) (hweights : Measurable weights) :
    Measurable (fun ω =>
      ReferenceCollectionServiceTailMeasurability.encodeCollectionObservation
        (OrdinaryCoordinatorPhysicalInterface.collectionPostChoice (bank ω) (row ω)
          (time ω) (arm ω) (Y ω) (payload ω) (ledger ω) (started ω)
          (fun a => weights ω a.val))) := by
  have hread := measurable_collectionServiceReadAtComponents_comp bank row time arm Y
    payload ledger started weights hbank hrow htime harm hY hpayload hledger hstarted hweights
  have hcode : Measurable (fun ω => collectionObservationCodeAtComponents
      (bank ω) (row ω) (time ω) (arm ω) (Y ω) (payload ω) (ledger ω)
      (started ω) (weights ω)) := by
    change Measurable (fun ω =>
      ReferenceCollectionServiceTailMeasurability.encodeCollectionObservation
        (ReferenceCollectionServiceTailMeasurability.serviceObservation (payload ω)
          (collectionServiceReadAtComponents (bank ω) (row ω) (time ω) (arm ω)
            (Y ω) (payload ω) (ledger ω) (started ω) (weights ω))))
    exact ReferenceCollectionServiceTailMeasurability.measurable_serviceObservationCode.comp
      (hpayload.prodMk hread)
  have heq : (fun ω =>
      ReferenceCollectionServiceTailMeasurability.encodeCollectionObservation
        (OrdinaryCoordinatorPhysicalInterface.collectionPostChoice (bank ω) (row ω)
          (time ω) (arm ω) (Y ω) (payload ω) (ledger ω) (started ω)
          (fun a => weights ω a.val))) =
      (fun ω => collectionObservationCodeAtComponents (bank ω) (row ω) (time ω)
        (arm ω) (Y ω) (payload ω) (ledger ω) (started ω) (weights ω)) := by
    funext ω
    exact (collectionObservationCodeAtComponents_eq_collectionPostChoice
      (bank ω) (row ω) (time ω) (arm ω) (Y ω) (payload ω) (ledger ω)
      (started ω) (weights ω)).symm
  rw [heq]
  exact hcode

/-- The retained collection code for the exact ordinary post-choice map on
the original product carrier. -/
def collectionPostChoiceCode (x : CollectionPostChoiceInputs p rate) :=
  ReferenceCollectionServiceTailMeasurability.encodeCollectionObservation
    (OrdinaryCoordinatorPhysicalInterface.collectionPostChoice x.1 x.2.1
      x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2.1
      x.2.2.2.2.2.2.1 x.2.2.2.2.2.2.2.1
      (fun a => x.2.2.2.2.2.2.2.2 a.val))

/-- The original product map is Borel. Its defining equation is the exact
ordinary post-choice code, and the proof composes the original projections. -/
theorem measurable_collectionPostChoiceCode :
    Measurable (collectionPostChoiceCode (p := p) (rate := rate)) := by
  let Input := CollectionPostChoiceInputs p rate
  let bank : Input → CoordinatorUpReception.UpDecoderBank p := fun x => x.1
  let row : Input → CompletePublicTable.CompleteRow p := fun x => x.2.1
  let time : Input → Fin p.T := fun x => x.2.2.1
  let arm : Input → Fin p.K := fun x => x.2.2.2.1
  let Y : Input → Fin (ConstructorDimensions.D p + 1) := fun x => x.2.2.2.2.1
  let payload : Input → ReferenceActivePhysicalStep.Payload rate := fun x => x.2.2.2.2.2.1
  let ledger : Input → ReferenceActivePhysicalStep.Ledger rate := fun x => x.2.2.2.2.2.2.1
  let started : Input → CoordinatorPhaseClock.StartRoundResult p := fun x => x.2.2.2.2.2.2.2.1
  let weights : Input → Fin p.K → ℝ := fun x => x.2.2.2.2.2.2.2.2
  have hbank : Measurable bank := measurable_fst
  have htail₀ : Measurable (fun x : Input => x.2) := measurable_snd
  have htail₁ : Measurable (fun x : Input => x.2.2) := measurable_snd.comp htail₀
  have htail₂ : Measurable (fun x : Input => x.2.2.2) := measurable_snd.comp htail₁
  have htail₃ : Measurable (fun x : Input => x.2.2.2.2) := measurable_snd.comp htail₂
  have htail₄ : Measurable (fun x : Input => x.2.2.2.2.2) := measurable_snd.comp htail₃
  have htail₅ : Measurable (fun x : Input => x.2.2.2.2.2.2) := measurable_snd.comp htail₄
  have htail₆ : Measurable (fun x : Input => x.2.2.2.2.2.2.2) := measurable_snd.comp htail₅
  have hrow : Measurable row := measurable_fst.comp htail₀
  have htime : Measurable time := measurable_fst.comp htail₁
  have harm : Measurable arm := measurable_fst.comp htail₂
  have hY : Measurable Y := measurable_fst.comp htail₃
  have hpayload : Measurable payload := measurable_fst.comp htail₄
  have hledger : Measurable ledger := measurable_fst.comp htail₅
  have hstarted : Measurable started := measurable_fst.comp htail₆
  have hweights : Measurable weights := measurable_snd.comp htail₆
  have hcomponents := measurable_collectionObservationCodeAtComponents_comp
    bank row time arm Y payload ledger started weights
    hbank hrow htime harm hY hpayload hledger hstarted hweights
  exact hcomponents

end Bandits.Support.OrdinaryCollectionObservationMeasurability

end
