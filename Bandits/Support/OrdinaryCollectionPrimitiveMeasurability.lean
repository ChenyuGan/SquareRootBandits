/-
Copyright (c) 2026 Bandits Lean regret formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bandits Lean regret formalization contributors
-/
module

public import Bandits.Support.OrdinaryCoordinatorLocalMeasurability

import Mathlib.MeasureTheory.Function.Floor

/-!
# Primitive Borel maps for the ordinary collection recorder and clock finish

These producers retain the original complete row and calendar time as
independent Borel coordinates. The recorder receives the existing payload,
start result, full real weight vector, own arm, and typed grid observation;
the clock finish receives the original start result, pending set, time, and
complete row. No canonical `RoundInput` or supplied measurable operation is
used.

Mathematical evidence: `sources/zip4/manuscript/07_public_setup.tex:55-114`,
`sources/zip4/manuscript/06_interruptions.tex:240-296`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:6-14`,
`sources/zip4/manuscript/appendix_b_communication.tex:94-131`, and
`sources/zip4/manuscript/08_main_theorem.tex:67-75`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.CanonicalFastSampling
open Bandits.Support.CanonicalRecordingRates
open Bandits.Support.CanonicalRecordingSlice
open Bandits.Support.ContinuousControlSlice
open Bandits.Support.ContinuousLearningRows
open Bandits.Support.PublicDiscreteDraws
open Bandits.Support.RealRewardGridCount
open Bandits.Support.ActiveRoundActions
open Bandits.Support.CoordinatorPhaseClock
open Bandits.Support.CoordinatorRecorderComplementBridge
open Bandits.Support.CoordinatorRecordingMeasurability
open Bandits.Support.ReferenceCollectionRecorderJointMeasurability

namespace Bandits.Support.OrdinaryCollectionPrimitiveMeasurability

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput

variable {p : Parameters} {rate : RateInput p}

/-- Assemble the literal checked collection-recorder input from the original
primitive arguments. `weights` keeps the full real-vector Borel carrier; the
existing bridge receives only its restriction to the payload's fast set. -/
def collectionRecordingInputAtComponents
    (row : CompletePublicTable.CompleteRow p) (time : Fin p.T)
    (arm : Fin p.K) (Y : Fin (D p + 1))
    (payload : Payload rate) (started : StartRoundResult p)
    (weights : Fin p.K → ℝ) : CoordinatorRecorderComplementBridge.Input payload := {
  currentWeights := restrictedWeights payload weights
  time := time
  gridBoundary := started.clock.g
  row := row
  ownArm := arm
  observation := Y
  mode := .collection }

/-- The actual ordinary bridge result on its original post-choice
coordinates. -/
def collectionRecordingAtComponents
    (row : CompletePublicTable.CompleteRow p) (time : Fin p.T)
    (arm : Fin p.K) (Y : Fin (D p + 1))
    (payload : Payload rate) (started : StartRoundResult p)
    (weights : Fin p.K → ℝ) : Option (CoordinatorRecordingOperation.Output p) :=
  CoordinatorRecorderComplementBridge.run
    (collectionRecordingInputAtComponents row time arm Y payload started weights)

/-- The full-vector and fast-complement input calls agree whenever the full
vector extends that actual complement. -/
theorem collectionRecordingInputAtComponents_eq_existing
    (row : CompletePublicTable.CompleteRow p) (time : Fin p.T)
    (arm : Fin p.K) (Y : Fin (D p + 1)) (payload : Payload rate)
    (started : StartRoundResult p) (weights : Fin p.K → ℝ)
    (complementWeights : FastArm payload.slowSet → ℝ)
    (hweights : ∀ a, weights a.val = complementWeights a) :
    collectionRecordingInputAtComponents row time arm Y payload started weights =
      OrdinaryCoordinatorPhysicalInterface.collectionRecordingInput
        row time arm Y payload started complementWeights := by
  have hw : restrictedWeights payload weights = complementWeights := funext hweights
  unfold collectionRecordingInputAtComponents
  rw [hw]
  rfl

/-- The recorder does not depend on a full-vector extension away from the
payload's actual fast complement. -/
theorem collectionRecordingAtComponents_eq_of_complement_agreement
    (row : CompletePublicTable.CompleteRow p) (time : Fin p.T)
    (arm : Fin p.K) (Y : Fin (D p + 1)) (payload : Payload rate)
    (started : StartRoundResult p) (weights₁ weights₂ : Fin p.K → ℝ)
    (hagrees : ∀ a : FastArm payload.slowSet,
      weights₁ a.val = weights₂ a.val) :
    collectionRecordingAtComponents row time arm Y payload started weights₁ =
      collectionRecordingAtComponents row time arm Y payload started weights₂ := by
  have hw : restrictedWeights payload weights₁ = restrictedWeights payload weights₂ :=
    funext hagrees
  simp [collectionRecordingAtComponents, collectionRecordingInputAtComponents, hw]

/-- The exact source gate, written on the original complete row and time. -/
def collectionRecorderGateAtComponents
    (row : CompletePublicTable.CompleteRow p) (time : Fin p.T)
    (payload : Payload rate) (started : StartRoundResult p)
    (_weights : Fin p.K → ℝ) (arm : Fin p.K) (_Y : Fin (D p + 1)) : Prop :=
  slotDraw (sliceAt time row.2) = dataSlot ∧
    recorderSourceDraw p.two_le_m p.m_lt_K (sliceAt time row.2) =
      coordinator p.two_le_m ∧
    time.val + 1 < started.clock.g ∧
    recordingMask (K_pos p) (coordinator p.two_le_m) arm (sliceAt time row.2) ∧
    (coordinate Label.thin (sliceAt time row.2)).val ≤
      collectionThresholdAtComponents payload arm

/-- Finite code for the checked recorder. Invalid boundary or complement
envelope data remain outer `none`; valid failed gates remain a successful
zero-arrival code. -/
def collectionRecorderCodeAtComponents
    (row : CompletePublicTable.CompleteRow p) (time : Fin p.T)
    (payload : Payload rate) (started : StartRoundResult p)
    (weights : Fin p.K → ℝ) (arm : Fin p.K) (Y : Fin (D p + 1)) :
    Option (CoordinatorRecordingMeasurability.OutputCode p) := by
  classical
  exact if hvalid : started.clock.g ≤ p.T + 1 ∧
      collectionLocalEnvelope payload weights then
    if hgate : collectionRecorderGateAtComponents row time payload started
        weights arm Y then
      some (some arm,
        ⟨min (D p) (collectionFloorAtComponents payload arm Y),
          Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩)
    else
      some (none, ⟨0, Nat.succ_pos _⟩)
  else none

private theorem measurable_choose_finite {Ω α β : Type*}
    [MeasurableSpace Ω] [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [MeasurableSpace β]
    (choice : Ω → α) (family : α → Ω → β)
    (hchoice : Measurable choice) (hfamily : ∀ a, Measurable (family a)) :
    Measurable (fun ω => family (choice ω) ω) := by
  intro s hs
  change MeasurableSet {ω | family (choice ω) ω ∈ s}
  have hpre : {ω | family (choice ω) ω ∈ s} =
      ⋃ a : α, {ω | choice ω = a} ∩ {ω | family a ω ∈ s} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro h
      exact ⟨choice ω, rfl, h⟩
    · rintro ⟨a, hchoice', hvalue⟩
      rw [hchoice']
      exact hvalue
  rw [hpre]
  exact MeasurableSet.iUnion fun a =>
    (measurableSet_eq_fun hchoice measurable_const).inter (hfamily a hs)

private theorem measurable_collectionSliceAtComponents {Ω : Type*}
    [MeasurableSpace Ω]
    (row : Ω → CompletePublicTable.CompleteRow p) (time : Ω → Fin p.T)
    (hrow : Measurable row) (htime : Measurable time) :
    Measurable (fun ω => sliceAt (time ω) (row ω).2) := by
  let family : Fin p.T → (LearningRow p × Fin p.T) → Slice p :=
    fun t z => sliceAt t z.1
  have hfamily : ∀ t, Measurable (family t) := by
    intro t
    exact (ContinuousLearningRows.measurable_sliceAt t).comp measurable_fst
  have hselected : Measurable
      (fun z : LearningRow p × Fin p.T => family z.2 z) :=
    measurable_choose_finite (fun z : LearningRow p × Fin p.T => z.2)
      family measurable_snd hfamily
  exact hselected.comp ((measurable_snd.comp hrow).prodMk htime)

private theorem measurable_collectionEnvelopeSet {Ω : Type*}
    [MeasurableSpace Ω] (payload : Ω → Payload rate)
    (weights : Ω → Fin p.K → ℝ) (hpayload : Measurable payload)
    (hweights : Measurable weights) :
    MeasurableSet {ω | collectionLocalEnvelope (payload ω) (weights ω)} := by
  have hpobs : Measurable (fun ω =>
      LaterAssignmentStartMeasurability.payloadObservation (payload ω)) :=
    (comap_measurable _ : Measurable
      LaterAssignmentStartMeasurability.payloadObservation).comp hpayload
  have hslow : Measurable (fun ω =>
      (LaterAssignmentStartMeasurability.payloadObservation (payload ω)).2.2.1) :=
    measurable_fst.comp (measurable_snd.comp (measurable_snd.comp hpobs))
  have hanchor := AssignmentPayloadDerivedMeasurability.measurable_inputAnchor.comp
    hpayload
  have hslowMem (a : Fin p.K) :
      MeasurableSet {ω | a ∈ (payload ω).slowSet.val} := by
    have hset : MeasurableSet {s : Finset (Fin p.K) | a ∈ s} := by
      rw [show {s : Finset (Fin p.K) | a ∈ s} =
        ⋃ s : Finset (Fin p.K),
          if a ∈ s then ({s} : Set (Finset (Fin p.K))) else ∅ by
        ext s
        simp]
      exact MeasurableSet.iUnion fun s => by
        by_cases hs : a ∈ s <;> simp [hs]
    exact hslow hset
  have hEq : {ω | collectionLocalEnvelope (payload ω) (weights ω)} =
      ⋂ a : Fin p.K,
        ({ω | a ∈ (payload ω).slowSet.val} ∪
          ({ω | (payload ω).anchor a ≤ weights ω a} ∩
            {ω | weights ω a ≤ 2 * (payload ω).anchor a})) := by
    ext ω
    simp [collectionLocalEnvelope]
  rw [hEq]
  apply MeasurableSet.iInter
  intro a
  have ha := (measurable_pi_apply a).comp hanchor
  have hw := (measurable_pi_apply a).comp hweights
  have htwo : Measurable (fun ω => (2 : ℝ) * (payload ω).anchor a) :=
    measurable_const.mul ha
  exact (hslowMem a).union
    ((measurableSet_le ha hw).inter (measurableSet_le hw htwo))

/-- Joint measurability of the finite recorder code from separately
measurable original primitive maps. The row and time are unrestricted and
vary independently. -/
theorem measurable_collectionRecorderCodeAtComponents {Ω : Type*}
    [MeasurableSpace Ω]
    (row : Ω → CompletePublicTable.CompleteRow p) (time : Ω → Fin p.T)
    (payload : Ω → Payload rate) (started : Ω → StartRoundResult p)
    (weights : Ω → Fin p.K → ℝ) (arm : Ω → Fin p.K)
    (Y : Ω → Fin (D p + 1))
    (hrow : Measurable row) (htime : Measurable time)
    (hpayload : Measurable payload) (hstarted : Measurable started)
    (hweights : Measurable weights) (harm : Measurable arm)
    (hY : Measurable Y) :
    Measurable (fun ω => collectionRecorderCodeAtComponents
      (row ω) (time ω) (payload ω) (started ω) (weights ω) (arm ω) (Y ω)) := by
  classical
  let boundary := fun ω => (started ω).clock.g
  have hboundary : Measurable boundary := by
    exact (Measurable.of_discrete : Measurable
      (fun s : StartRoundResult p => s.clock.g)).comp hstarted
  have hlocal : MeasurableSet {ω | boundary ω ≤ p.T + 1 ∧
      collectionLocalEnvelope (payload ω) (weights ω)} := by
    exact (measurableSet_le hboundary measurable_const).inter
      (measurable_collectionEnvelopeSet payload weights hpayload hweights)
  let slice := fun ω => sliceAt (time ω) (row ω).2
  have hslice : Measurable slice :=
    measurable_collectionSliceAtComponents row time hrow htime
  have hslot : Measurable (fun ω => slotDraw (slice ω)) :=
    PublicDiscreteDraws.measurable_slotDraw.comp hslice
  have hsource : Measurable (fun ω =>
      recorderSourceDraw p.two_le_m p.m_lt_K (slice ω)) :=
    (PublicDiscreteDraws.measurable_recorderSourceDraw
      p.two_le_m p.m_lt_K).comp hslice
  have htimeVal : Measurable (fun ω => (time ω).val) :=
    (Measurable.of_discrete : Measurable (fun t : Fin p.T => t.val)).comp htime
  have hsourceRound : Measurable (fun ω => (time ω).val + 1) :=
    htimeVal.add_const 1
  have hnotFrozen : MeasurableSet {ω | (time ω).val + 1 < boundary ω} :=
    measurableSet_lt hsourceRound hboundary
  have hmask : MeasurableSet {ω | recordingMask (K_pos p)
      (coordinator p.two_le_m) (arm ω) (slice ω)} := by
    have hEq : {ω | recordingMask (K_pos p) (coordinator p.two_le_m)
        (arm ω) (slice ω)} =
      ⋃ a : Fin p.K, {ω | arm ω = a} ∩
        {ω | recordingMask (K_pos p) (coordinator p.two_le_m) a (slice ω)} := by
      ext ω
      simp
    rw [hEq]
    apply MeasurableSet.iUnion
    intro a
    exact (measurableSet_eq_fun harm measurable_const).inter
      ((measurableSet_recordingMask p.two_le_m (K_pos p)
        (coordinator p.two_le_m) a).preimage hslice)
  have hrates := AssignmentPayloadDerivedMeasurability.measurable_inputRate.comp
    hpayload
  have hrateAt : Measurable (fun ω => (payload ω).rate (arm ω)) := by
    let family : Fin p.K → Ω → ℝ := fun a ω => (payload ω).rate a
    have hfam : ∀ a, Measurable (family a) := fun a =>
      (measurable_pi_apply a).comp hrates
    exact measurable_choose_finite arm family harm hfam
  have hthreshold : Measurable (fun ω =>
      collectionThresholdAtComponents (payload ω) (arm ω)) :=
    hrateAt.div_const (collectionRawGateMass (p := p))
  have hthin : Measurable (fun ω =>
      (coordinate Label.thin (slice ω)).val) :=
    (ContinuousControlSlice.measurable_coordinate Label.thin).subtype_val.comp hslice
  have hdataSet : MeasurableSet {ω | slotDraw (slice ω) = dataSlot} :=
    (measurableSet_singleton dataSlot).preimage hslot
  have hsourceSet : MeasurableSet {ω | recorderSourceDraw p.two_le_m p.m_lt_K
      (slice ω) = coordinator p.two_le_m} :=
    (measurableSet_singleton (coordinator p.two_le_m)).preimage hsource
  have hthinSet : MeasurableSet {ω | (coordinate Label.thin (slice ω)).val ≤
      collectionThresholdAtComponents (payload ω) (arm ω)} :=
    measurableSet_le hthin hthreshold
  have hgate : MeasurableSet {ω | collectionRecorderGateAtComponents
      (row ω) (time ω) (payload ω) (started ω) (weights ω) (arm ω) (Y ω)} := by
    change MeasurableSet ({ω | slotDraw (slice ω) = dataSlot} ∩
      ({ω | recorderSourceDraw p.two_le_m p.m_lt_K (slice ω) =
        coordinator p.two_le_m} ∩
      ({ω | (time ω).val + 1 < boundary ω} ∩
      ({ω | recordingMask (K_pos p) (coordinator p.two_le_m)
        (arm ω) (slice ω)} ∩
      {ω | (coordinate Label.thin (slice ω)).val ≤
        collectionThresholdAtComponents (payload ω) (arm ω)}))))
    exact hdataSet.inter (hsourceSet.inter
      (hnotFrozen.inter (hmask.inter hthinSet)))
  have hreward : Measurable (fun ω =>
      realRewardGridValue (D p) (D_pos p) (Y ω)) := by
    exact (Measurable.of_discrete : Measurable
      (fun y : Fin (D p + 1) => realRewardGridValue (D p) (D_pos p) y)).comp hY
  have hfloorArgument : Measurable (fun ω => ((D p : ℝ) * rate.eta.val *
      realRewardGridValue (D p) (D_pos p) (Y ω)) / (payload ω).rate (arm ω)) := by
    exact (((measurable_const : Measurable fun _ : Ω =>
      (D p : ℝ) * rate.eta.val).mul hreward).div hrateAt)
  have hfloor : Measurable (fun ω =>
      collectionFloorAtComponents (payload ω) (arm ω) (Y ω)) :=
    Nat.measurable_floor.comp hfloorArgument
  let arrivalFin : Ω → Fin (D p + 1) := fun ω =>
    ⟨min (D p) (collectionFloorAtComponents (payload ω) (arm ω) (Y ω)),
      Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩
  have harrivalFin : Measurable arrivalFin := by
    have hcast : Measurable (fun n : ℕ =>
        (⟨min (D p) n, Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩ :
          Fin (D p + 1))) := Measurable.of_discrete
    exact hcast.comp hfloor
  have hsomeArm : Measurable
      (fun ω => (some (arm ω) : Option (Fin p.K))) :=
    (Measurable.of_discrete :
      Measurable (some : Fin p.K → Option (Fin p.K))).comp harm
  have hsuccessCode : Measurable (fun ω => some
      ((some (arm ω), arrivalFin ω) :
        CoordinatorRecordingMeasurability.OutputCode p)) := by
    have hpair : Measurable (fun ω =>
        ((some (arm ω) : Option (Fin p.K)), arrivalFin ω)) :=
      hsomeArm.prodMk harrivalFin
    exact (Measurable.of_discrete : Measurable
      (some : CoordinatorRecordingMeasurability.OutputCode p →
        Option (CoordinatorRecordingMeasurability.OutputCode p))).comp hpair
  have hzeroCode : Measurable (fun _ : Ω =>
      (some (none, (⟨0, Nat.succ_pos _⟩ : Fin (D p + 1))) :
        Option (CoordinatorRecordingMeasurability.OutputCode p))) := measurable_const
  have hvalidCode : Measurable (fun ω =>
      (if collectionRecorderGateAtComponents (row ω) (time ω) (payload ω)
          (started ω) (weights ω) (arm ω) (Y ω) then
        some (some (arm ω), arrivalFin ω)
      else some (none, (⟨0, Nat.succ_pos _⟩ : Fin (D p + 1))))) :=
    Measurable.ite hgate hsuccessCode hzeroCode
  exact Measurable.ite hlocal hvalidCode measurable_const

/-- The finite primitive code reconstructs the exact checked bridge result,
including invalid-domain failure, zero-arrival rejection, and the raw floor. -/
theorem collectionRecorderCodeAtComponents_reconstructs
    (row : CompletePublicTable.CompleteRow p) (time : Fin p.T)
    (payload : Payload rate) (started : StartRoundResult p)
    (weights : Fin p.K → ℝ) (arm : Fin p.K) (Y : Fin (D p + 1)) :
    collectionRecorderCodeAtComponents row time payload started weights arm Y =
      CoordinatorRecordingMeasurability.encodeResult
        (collectionRecordingAtComponents row time arm Y payload started weights) := by
  classical
  let input := collectionRecordingInputAtComponents row time arm Y payload started weights
  let boundary := started.clock.g
  have hEnvelope : collectionLocalEnvelope payload weights ↔
      ∀ a : FastArm payload.slowSet,
        payload.anchor a.val ≤ weights a.val ∧
          weights a.val ≤ 2 * payload.anchor a.val := by
    constructor
    · intro h a
      rcases h a.val with hs | hw
      · exact False.elim ((Finset.mem_sdiff.mp a.property).2 hs)
      · exact hw
    · intro h a
      by_cases hs : a ∈ payload.slowSet.val
      · exact Or.inl hs
      · right
        let fast : FastArm payload.slowSet :=
          ⟨a, Finset.mem_sdiff.mpr ⟨Finset.mem_univ a, hs⟩⟩
        exact h fast
  have hlocalIff :
      CoordinatorRecorderComplementBridge.LocalInputsValid input ↔
        boundary ≤ p.T + 1 ∧ collectionLocalEnvelope payload weights := by
    change (boundary ≤ p.T + 1 ∧
        ∀ a : FastArm payload.slowSet,
          payload.anchor a.val ≤ weights a.val ∧
            weights a.val ≤ 2 * payload.anchor a.val) ↔ _
    rw [hEnvelope]
  have hdataEq : CoordinatorRecorderComplementBridge.selectedSlot input =
      slotDraw (sliceAt time row.2) := by
    simp [CoordinatorRecorderComplementBridge.selectedSlot, input,
      collectionRecordingInputAtComponents,
      CoordinatorRecorderComplementBridge.recorderInput,
      CoordinatorRecorderComplementBridge.recorderInputWithWeights,
      CoordinatorRecordingOperation.selectedSlot]
  have hsourceEq : CoordinatorRecorderComplementBridge.selectedRecorder input =
      recorderSourceDraw p.two_le_m p.m_lt_K (sliceAt time row.2) := by
    unfold CoordinatorRecorderComplementBridge.selectedRecorder
      CoordinatorRecordingOperation.selectedRecorder
    simp [input, collectionRecordingInputAtComponents,
      CoordinatorRecorderComplementBridge.recorderInput,
      CoordinatorRecorderComplementBridge.recorderInputWithWeights]
    rfl
  have hfreezeEq : CoordinatorRecorderComplementBridge.isFrozen input ↔
      ¬ time.val + 1 < boundary := by
    simp [CoordinatorRecorderComplementBridge.isFrozen,
      CoordinatorRecordingOperation.isFrozen,
      CoordinatorRecorderComplementBridge.recorderInput,
      CoordinatorRecorderComplementBridge.recorderInputWithWeights,
      collectionRecordingInputAtComponents, input, boundary,
      CoordinatorRecorderComplementBridge.sourceStart,
      CoordinatorRecordingOperation.sourceCalendarRound]
  have hmaskEq : CoordinatorRecorderComplementBridge.ownMaskPasses input ↔
      recordingMask (K_pos p) (coordinator p.two_le_m) arm
        (sliceAt time row.2) := by
    rfl
  have hthresholdEq (hvalid : CoordinatorRecorderComplementBridge.LocalInputsValid input) :
      CoordinatorRecorderComplementBridge.threshold input hvalid =
        collectionThresholdAtComponents payload arm := by
    have hopValid := CoordinatorRecorderComplementBridge.recorderInput_inputsValid input hvalid
    have hmode : (CoordinatorRecorderComplementBridge.recorderInput input).mode = .collection := by
      rfl
    have hraw : CoordinatorRecordingOperation.coordinatorRawGateMass
        (CoordinatorRecorderComplementBridge.recorderInput input) hopValid =
          collectionRawGateMass (p := p) := by
      simp [CoordinatorRecordingOperation.coordinatorRawGateMass,
        CoordinatorRecordingOperation.coordinatorArmProbability, hmode,
        collectionRawGateMass]
    unfold CoordinatorRecorderComplementBridge.threshold
      CoordinatorRecordingOperation.coordinatorThreshold
    rw [hraw]
    simp [collectionThresholdAtComponents, input,
      CoordinatorRecorderComplementBridge.recorderInput,
      CoordinatorRecorderComplementBridge.recorderInputWithWeights,
      collectionRecordingInputAtComponents,
      AssignmentStartPayload.Input.rate_eq_canonical]
  have hfloorEq : CoordinatorRecorderComplementBridge.floorArrival input =
      collectionFloorAtComponents payload arm Y := by
    simp only [CoordinatorRecorderComplementBridge.floorArrival,
      CoordinatorRecordingOperation.floorArrival, input,
      CoordinatorRecorderComplementBridge.recorderInput,
      CoordinatorRecorderComplementBridge.recorderInputWithWeights,
      collectionRecordingInputAtComponents]
    unfold collectionFloorAtComponents
    rw [← payload.rate_eq_canonical arm]
  by_cases hlocal : boundary ≤ p.T + 1 ∧ collectionLocalEnvelope payload weights
  · have hvalid : CoordinatorRecorderComplementBridge.LocalInputsValid input :=
      hlocalIff.mpr hlocal
    have hopValid := CoordinatorRecorderComplementBridge.recorderInput_inputsValid input hvalid
    have hfloorBound : collectionFloorAtComponents payload arm Y ≤ D p := by
      rw [← hfloorEq]
      exact CoordinatorRecordingOperation.floorArrival_le_D
        (CoordinatorRecorderComplementBridge.recorderInput input) hopValid
    have howns : CoordinatorRecorderComplementBridge.ownsArm input := by
      change CoordinatorRecordingOperation.ownsArm
        (CoordinatorRecorderComplementBridge.operationMode input.mode) arm
      simp [CoordinatorRecorderComplementBridge.operationMode, input,
        collectionRecordingInputAtComponents, CoordinatorRecordingOperation.ownsArm]
    have hdata : CoordinatorRecorderComplementBridge.selectedSlot input = dataSlot ↔
        slotDraw (sliceAt time row.2) = dataSlot := by rw [hdataEq]
    have hsource : CoordinatorRecorderComplementBridge.selectedRecorder input =
        coordinator p.two_le_m ↔ recorderSourceDraw p.two_le_m p.m_lt_K
          (sliceAt time row.2) = coordinator p.two_le_m := by rw [hsourceEq]
    have hnotFrozen : ¬ CoordinatorRecorderComplementBridge.isFrozen input ↔
        time.val + 1 < boundary := by rw [hfreezeEq]; omega
    have hmask : CoordinatorRecorderComplementBridge.ownMaskPasses input ↔
        recordingMask (K_pos p) (coordinator p.two_le_m) arm
          (sliceAt time row.2) := hmaskEq
    have hthin : CoordinatorRecorderComplementBridge.thinScalar input ≤
        CoordinatorRecorderComplementBridge.threshold input hvalid ↔
        (coordinate Label.thin (sliceAt time row.2)).val ≤
          collectionThresholdAtComponents payload arm := by
      rw [hthresholdEq hvalid]
      rfl
    by_cases hgate : collectionRecorderGateAtComponents row time payload started
        weights arm Y
    · have hgates :
          slotDraw (sliceAt time row.2) = dataSlot ∧
          recorderSourceDraw p.two_le_m p.m_lt_K (sliceAt time row.2) =
            coordinator p.two_le_m ∧
          time.val + 1 < boundary ∧
          recordingMask (K_pos p) (coordinator p.two_le_m) arm
            (sliceAt time row.2) ∧
          (coordinate Label.thin (sliceAt time row.2)).val ≤
            collectionThresholdAtComponents payload arm := by
        simpa [collectionRecorderGateAtComponents] using hgate
      rcases hgates with ⟨hd, hs, hf, hm, ht⟩
      have hrun := CoordinatorRecorderComplementBridge.run_gate_and_floor input hvalid
        (hdata.mp hd) (hsource.mp hs) (hnotFrozen.mpr hf) howns
        (hmask.mpr hm) (hthin.mpr ht)
      rcases hrun with ⟨out, hout, hgateArm, harrival⟩
      simp [collectionRecorderCodeAtComponents, boundary, input, hlocal, hgate, hout,
        CoordinatorRecordingMeasurability.encodeResult,
        CoordinatorRecordingMeasurability.encodeOutput, hfloorBound,
        collectionRecordingAtComponents]
      exact ⟨by simpa [input, collectionRecordingInputAtComponents] using hgateArm.symm,
        by simpa [collectionFloorAtComponents] using (harrival.trans hfloorEq).symm⟩
    · by_cases hd : slotDraw (sliceAt time row.2) = dataSlot
      · by_cases hs : recorderSourceDraw p.two_le_m p.m_lt_K
            (sliceAt time row.2) = coordinator p.two_le_m
        · by_cases hf : time.val + 1 < boundary
          · by_cases hm : recordingMask (K_pos p) (coordinator p.two_le_m)
                arm (sliceAt time row.2)
            · have ht : ¬ (coordinate Label.thin (sliceAt time row.2)).val ≤
                  collectionThresholdAtComponents payload arm := by
                intro ht
                exact hgate (by simp [collectionRecorderGateAtComponents,
                  boundary, hd, hs, hf, hm, ht])
              have hrun := CoordinatorRecorderComplementBridge.run_zero_of_thinning_rejected
                input hvalid (hdata.mpr hd) (hsource.mpr hs) (hnotFrozen.mpr hf)
                howns (hmask.mpr hm) (by
                  intro hthinActual
                  exact ht (hthin.mp hthinActual))
              simp [collectionRecorderCodeAtComponents, boundary, input, hlocal, hgate,
                hrun, CoordinatorRecordingMeasurability.encodeResult,
                CoordinatorRecordingMeasurability.encodeOutput,
                CoordinatorRecordingOperation.zeroOutput,
                collectionRecordingAtComponents]
            · have hrun := CoordinatorRecorderComplementBridge.run_zero_of_mask_rejected
                input hvalid (hdata.mpr hd) (hsource.mpr hs) (hnotFrozen.mpr hf)
                howns (by
                  intro hown
                  exact hm (hmask.mp hown))
              simp [collectionRecorderCodeAtComponents, boundary, input, hlocal, hgate,
                hrun, CoordinatorRecordingMeasurability.encodeResult,
                CoordinatorRecordingMeasurability.encodeOutput,
                CoordinatorRecordingOperation.zeroOutput,
                collectionRecordingAtComponents]
          · have hrun := CoordinatorRecorderComplementBridge.run_zero_of_frozen
              input hvalid (hdata.mpr hd) (hsource.mpr hs) (hfreezeEq.mpr hf)
            simp [collectionRecorderCodeAtComponents, boundary, input, hlocal, hgate,
              hrun, CoordinatorRecordingMeasurability.encodeResult,
              CoordinatorRecordingMeasurability.encodeOutput,
              CoordinatorRecordingOperation.zeroOutput,
              collectionRecordingAtComponents]
        · have hrun := CoordinatorRecorderComplementBridge.run_zero_of_other_source
            input hvalid (hdata.mpr hd) (by rw [hsourceEq]; exact hs)
          simp [collectionRecorderCodeAtComponents, boundary, input, hlocal, hgate,
            hrun, CoordinatorRecordingMeasurability.encodeResult,
            CoordinatorRecordingMeasurability.encodeOutput,
            CoordinatorRecordingOperation.zeroOutput,
            collectionRecordingAtComponents]
      · have hrun := CoordinatorRecorderComplementBridge.run_zero_of_not_data
          input hvalid (by rw [hdataEq]; exact hd)
        simp [collectionRecorderCodeAtComponents, boundary, input, hlocal, hgate,
          hrun, CoordinatorRecordingMeasurability.encodeResult,
          CoordinatorRecordingMeasurability.encodeOutput,
          CoordinatorRecordingOperation.zeroOutput,
          collectionRecordingAtComponents]
  · have hrun : CoordinatorRecorderComplementBridge.run input = none := by
      by_cases hb : boundary ≤ p.T + 1
      · have hnotEnv : ¬ collectionLocalEnvelope payload weights := by
          intro henv
          exact hlocal ⟨hb, henv⟩
        have hcounter : ∃ a : Fin p.K,
            a ∉ payload.slowSet.val ∧
              (payload.anchor a ≤ weights a →
                ¬ weights a ≤ 2 * payload.anchor a) := by
          simpa [collectionLocalEnvelope] using hnotEnv
        rcases hcounter with ⟨a, haSlow, hbad⟩
        let fast : FastArm payload.slowSet :=
          ⟨a, Finset.mem_sdiff.mpr ⟨Finset.mem_univ a, haSlow⟩⟩
        by_cases hlow : payload.anchor a ≤ weights a
        · exact CoordinatorRecorderComplementBridge.run_none_of_invalid_complement_upper
            input fast (hbad hlow)
        · exact CoordinatorRecorderComplementBridge.run_none_of_invalid_complement_lower
            input fast hlow
      · exact CoordinatorRecorderComplementBridge.run_none_of_invalid_boundary input hb
    simp [collectionRecorderCodeAtComponents, boundary, input, hlocal, hrun,
      CoordinatorRecordingMeasurability.encodeResult,
      collectionRecordingAtComponents]

/-- Pointwise code equation for arbitrary independently varying primitive
maps. -/
theorem collectionRecorderCodeAtComponents_eq_encodeResult {Ω : Type*}
    (row : Ω → CompletePublicTable.CompleteRow p) (time : Ω → Fin p.T)
    (payload : Ω → Payload rate) (started : Ω → StartRoundResult p)
    (weights : Ω → Fin p.K → ℝ) (arm : Ω → Fin p.K)
    (Y : Ω → Fin (D p + 1)) (ω : Ω) :
    collectionRecorderCodeAtComponents (row ω) (time ω) (payload ω)
      (started ω) (weights ω) (arm ω) (Y ω) =
      CoordinatorRecordingMeasurability.encodeResult
        (collectionRecordingAtComponents (row ω) (time ω) (arm ω) (Y ω)
          (payload ω) (started ω) (weights ω)) :=
  collectionRecorderCodeAtComponents_reconstructs
    (row ω) (time ω) (payload ω) (started ω) (weights ω) (arm ω) (Y ω)

/-- Joint Borel measurability of the actual `Option (Output)` recorder
result, reconstructed through the admitted countable output code. -/
theorem measurable_collectionRecordingAtComponents {Ω : Type*}
    [MeasurableSpace Ω]
    (row : Ω → CompletePublicTable.CompleteRow p) (time : Ω → Fin p.T)
    (payload : Ω → Payload rate) (started : Ω → StartRoundResult p)
    (weights : Ω → Fin p.K → ℝ) (arm : Ω → Fin p.K)
    (Y : Ω → Fin (D p + 1))
    (hrow : Measurable row) (htime : Measurable time)
    (hpayload : Measurable payload) (hstarted : Measurable started)
    (hweights : Measurable weights) (harm : Measurable arm)
    (hY : Measurable Y) :
    Measurable (fun ω => collectionRecordingAtComponents
      (row ω) (time ω) (arm ω) (Y ω) (payload ω) (started ω) (weights ω)) := by
  have hcode := measurable_collectionRecorderCodeAtComponents
    row time payload started weights arm Y hrow htime hpayload hstarted
      hweights harm hY
  have hdecode : Measurable (CoordinatorRecordingMeasurability.decodeResult :
      Option (CoordinatorRecordingMeasurability.OutputCode p) →
        Option (CoordinatorRecordingOperation.Output p)) :=
    Measurable.of_discrete
  have hrecover := collectionRecorderCodeAtComponents_eq_encodeResult
    row time payload started weights arm Y
  have heq : (fun ω => collectionRecordingAtComponents
      (row ω) (time ω) (arm ω) (Y ω) (payload ω) (started ω) (weights ω)) =
      CoordinatorRecordingMeasurability.decodeResult ∘
        (fun ω => collectionRecorderCodeAtComponents
          (row ω) (time ω) (payload ω) (started ω) (weights ω) (arm ω) (Y ω)) := by
    funext ω
    rw [Function.comp_apply, hrecover ω]
    exact (CoordinatorRecordingMeasurability.decodeResult_encodeResult _).symm
  rw [heq]
  exact hdecode.comp hcode

/-- The exact original phase-clock finish on the unrestricted primitive
coordinates, with the actual `StartRoundResult` retained. -/
def collectionPhaseClockFinishAtComponents (ρ : RateInput p) (time : Fin p.T)
    (started : StartRoundResult p) (pending : Finset (Fin (p.m - 1)))
    (row : CompletePublicTable.CompleteRow p) :
    Except CoordinatorPhaseClock.ClockFailure
      (CoordinatorPhaseClock.FinishRoundResult p) :=
  CoordinatorPhaseClock.finishRound p ρ.eta.val time started.clock pending row

/-- The named map is definitionally the existing finish operation, retaining
all original error constructors and the row proposal in its successful clock. -/
theorem collectionPhaseClockFinishAtComponents_eq_original
    (ρ : RateInput p) (time : Fin p.T) (started : StartRoundResult p)
    (pending : Finset (Fin (p.m - 1)))
    (row : CompletePublicTable.CompleteRow p) :
    collectionPhaseClockFinishAtComponents ρ time started pending row =
      CoordinatorPhaseClock.finishRound p ρ.eta.val time started.clock pending row := rfl

/-- Joint measurability of the original phase-clock finish on independently
varying start result, pending set, calendar time, and whole row. The read
signature retains the exact proposal bit and hence the final proposal record. -/
theorem measurable_collectionPhaseClockFinishAtComponents {Ω : Type*}
    [MeasurableSpace Ω]
    (started : Ω → StartRoundResult p)
    (pending : Ω → Finset (Fin (p.m - 1)))
    (time : Ω → Fin p.T)
    (row : Ω → CompletePublicTable.CompleteRow p)
    (hstarted : Measurable started) (hpending : Measurable pending)
    (htime : Measurable time) (hrow : Measurable row) :
    Measurable (fun ω => collectionPhaseClockFinishAtComponents rate
      (time ω) (started ω) (pending ω) (row ω)) := by
  let proposal := fun ω => FollowerCutoffScan.completeRowProposalBit p rate.eta.val
    (row ω) (time ω)
  let read : Ω → ReferenceCollectionServiceTailMeasurability.CollectionClockFinishRead p := fun ω =>
    Prod.mk ((started ω).clock)
      (Prod.mk (pending ω) (Prod.mk (time ω) (proposal ω)))
  have hclock : Measurable (fun ω => (started ω).clock) := by
    exact (Measurable.of_discrete :
      Measurable (fun s : StartRoundResult p => s.clock)).comp hstarted
  have hproposal : Measurable proposal := by
    exact (FollowerReleaseFinishMeasurability.measurable_completeRowProposalBitAt
      p rate.eta.val).comp (hrow.prodMk htime)
  have hread : Measurable read := by
    change Measurable (fun ω => Prod.mk ((started ω).clock)
      (Prod.mk (pending ω) (Prod.mk (time ω) (proposal ω))))
    exact hclock.prodMk (hpending.prodMk (htime.prodMk hproposal))
  apply FollowerDownJointMeasurability.measurable_of_countable_read_factorization
    read hread (fun ω => collectionPhaseClockFinishAtComponents rate
      (time ω) (started ω) (pending ω) (row ω))
  intro x y hreadEq
  rcases Prod.mk.inj hreadEq with ⟨hclockEq, hrest⟩
  rcases Prod.mk.inj hrest with ⟨hpendingEq, hrest⟩
  rcases Prod.mk.inj hrest with ⟨htimeEq, hbitEq⟩
  change proposal x = proposal y at hbitEq
  have hbit : FollowerCutoffScan.completeRowProposalBit p rate.eta.val
      (row x) (time x) = FollowerCutoffScan.completeRowProposalBit p rate.eta.val
        (row y) (time x) := by
    exact hbitEq.trans (congrArg
      (FollowerCutoffScan.completeRowProposalBit p rate.eta.val (row y)) htimeEq.symm)
  have hfinish (clock : CoordinatorPhaseClock.ClockRegisters p)
      (waiting : Finset (Fin (p.m - 1))) (t : Fin p.T)
      (row₁ row₂ : CompletePublicTable.CompleteRow p)
      (hproposal : FollowerCutoffScan.completeRowProposalBit p rate.eta.val row₁ t =
        FollowerCutoffScan.completeRowProposalBit p rate.eta.val row₂ t) :
      CoordinatorPhaseClock.finishRound p rate.eta.val t clock waiting row₁ =
        CoordinatorPhaseClock.finishRound p rate.eta.val t clock waiting row₂ := by
    unfold CoordinatorPhaseClock.finishRound
    rw [hproposal]
  change CoordinatorPhaseClock.finishRound p rate.eta.val (time x)
      (started x).clock (pending x) (row x) =
    CoordinatorPhaseClock.finishRound p rate.eta.val (time y)
      (started y).clock (pending y) (row y)
  calc
    _ = CoordinatorPhaseClock.finishRound p rate.eta.val (time x)
        (started x).clock (pending x) (row y) :=
      hfinish _ _ _ _ _ hbit
    _ = _ := by rw [hclockEq, hpendingEq, htimeEq]

end Bandits.Support.OrdinaryCollectionPrimitiveMeasurability

end
