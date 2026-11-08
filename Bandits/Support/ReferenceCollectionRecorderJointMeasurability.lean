/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceActivePhysicalStepMeasurability

import Mathlib.MeasureTheory.Function.Floor

/-!
# Joint collection-recorder output measurability

Sources: sources/zip4/manuscript/06_interruptions.tex:235-274 and
sources/zip4/manuscript/appendix_a_local_protocol.tex:6-14,69-76.

This module proves the direct Borel output code and exact reconstruction for
the existing collection recorder. The original payload, checked start result,
complete selected row and time, full real weight vector, own arm, and typed
own grid observation vary jointly. The weight vector is restricted only when
forming the existing recorder input. No collection service, UP reception,
ledger finish, or full physical step is included.

The sole direct project dependency is
Bandits.Support.ReferenceActivePhysicalStepMeasurability at SHA-256
11b431bc05c6971b331016537f4e67f457e80a9c45d76940874cb30d37c6b314,
independently reviewed PASS in review-0347 with both build/axiom/kernel gates.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions

namespace Bandits.Support.ReferenceCollectionRecorderJointMeasurability

open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalStepMeasurability
open Bandits.Support.CoordinatorPhaseClock
open Bandits.Support.CoordinatorRecorderComplementBridge
open Bandits.Support.CoordinatorRecordingOperation
open Bandits.Support.CoordinatorRecordingMeasurability
open Bandits.Support.AssignmentStartPayload
open Bandits.Support.AssignmentPayloadDerivedMeasurability
open Bandits.Support.CanonicalFastSampling
open Bandits.Support.CanonicalRecordingSlice
open Bandits.Support.CanonicalRecordingRates
open Bandits.Support.ContinuousControlSlice
open Bandits.Support.ContinuousLearningRows
open Bandits.Support.LaterAssignmentStartMeasurability
open Bandits.Support.PublicDiscreteDraws
open Bandits.Support.RealRewardGridCount
open Bandits.Support.ActiveRoundActions

abbrev Parameters := ConstructorDimensions.Parameters

variable {p : Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}

instance outputCodeOptionMeasurableSingletonClass :
    MeasurableSingletonClass
      (Option (CoordinatorRecordingMeasurability.OutputCode p)) where
  measurableSet_singleton value := by
    rw [LaterAssignmentStartMeasurability.optionMeasurableSpace,
      MeasurableSpace.measurableSet_comap]
    refine ⟨Set.singleton (Equiv.optionEquivSumPUnit
      (CoordinatorRecordingMeasurability.OutputCode p) value), ?_, ?_⟩
    · cases value with
      | none =>
          rw [Equiv.optionEquivSumPUnit_none]
          rw [measurableSet_sum_iff]
          constructor
          · have hpre :
                Sum.inl ⁻¹' ({Sum.inr PUnit.unit} :
                  Set (CoordinatorRecordingMeasurability.OutputCode p ⊕ PUnit)) = ∅ := by
              ext code
              simp
            change MeasurableSet (Sum.inl ⁻¹' ({Sum.inr PUnit.unit} :
              Set (CoordinatorRecordingMeasurability.OutputCode p ⊕ PUnit)))
            rw [hpre]
            exact MeasurableSet.empty
          · have hpre :
                Sum.inr ⁻¹' ({Sum.inr PUnit.unit} :
                  Set (CoordinatorRecordingMeasurability.OutputCode p ⊕ PUnit)) =
                    {PUnit.unit} := by
              ext u
              simp
            change MeasurableSet (Sum.inr ⁻¹' ({Sum.inr PUnit.unit} :
              Set (CoordinatorRecordingMeasurability.OutputCode p ⊕ PUnit)))
            rw [hpre]
            exact measurableSet_singleton PUnit.unit
      | some code =>
          rw [Equiv.optionEquivSumPUnit_some]
          rw [measurableSet_sum_iff]
          constructor
          · have hpre :
                Sum.inl ⁻¹' ({Sum.inl code} :
                  Set (CoordinatorRecordingMeasurability.OutputCode p ⊕ PUnit)) =
                    {code} := by
              ext other
              simp
            change MeasurableSet (Sum.inl ⁻¹' ({Sum.inl code} :
              Set (CoordinatorRecordingMeasurability.OutputCode p ⊕ PUnit)))
            rw [hpre]
            exact measurableSet_singleton code
          · have hpre :
                Sum.inr ⁻¹' ({Sum.inl code} :
                  Set (CoordinatorRecordingMeasurability.OutputCode p ⊕ PUnit)) = ∅ := by
              ext u
              simp
            change MeasurableSet (Sum.inr ⁻¹' ({Sum.inl code} :
              Set (CoordinatorRecordingMeasurability.OutputCode p ⊕ PUnit)))
            rw [hpre]
            exact MeasurableSet.empty
    · ext other
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · intro h
        exact (Equiv.optionEquivSumPUnit _).injective h
      · intro h
        subst other
        exact Set.mem_singleton_iff.mpr rfl

instance startRoundResultMeasurableSpace :
    MeasurableSpace (CoordinatorPhaseClock.StartRoundResult p) := ⊤

instance startRoundResultDiscreteMeasurableSpace :
    DiscreteMeasurableSpace (CoordinatorPhaseClock.StartRoundResult p) :=
  ⟨fun _ => trivial⟩

/-- Restrict the supplied full real vector to the payload's actual fast
complement. Every coordinate of the full vector retains its real Borel
structure. -/
def restrictedWeights (payload : Payload rate) (weights : Fin p.K → ℝ) :
    FastArm payload.slowSet → ℝ :=
  fun a => weights a.val

/-- The original local arguments assembled as the collection-mode input to
the accepted complement bridge. The complete original row and finite time are
retained verbatim. -/
def collectionRecordingInputAtComponents {x : RoundInput p rate}
    (payload : Payload rate) (started : StartRoundResult p)
    (weights : Fin p.K → ℝ) (ownArm : Fin p.K)
    (observation : Fin (D p + 1)) : CoordinatorRecorderComplementBridge.Input payload := {
  currentWeights := restrictedWeights payload weights
  time := x.time
  gridBoundary := started.clock.g
  row := x.row
  ownArm := ownArm
  observation := observation
  mode := .collection
}

/-- Exact reduction to the existing prepared collection input when the
separately supplied local primitives are the prepared call's own fields. -/
theorem collectionRecordingInputAtComponents_eq {x : RoundInput p rate}
    (prepared : PreparedRound x) (payload : Payload rate)
    (started : StartRoundResult p) (weights : Fin p.K → ℝ)
    (complementWeights : FastArm payload.slowSet → ℝ)
    (ownArm : Fin p.K) (observation : Fin (D p + 1))
    (harm : ownArm = prepared.coordinator.arm)
    (hobs : observation = prepared.coordinatorObservation)
    (hweights : ∀ a, weights a.val = complementWeights a) :
    collectionRecordingInputAtComponents (x := x) payload started weights ownArm observation =
      ReferenceActivePhysicalStep.collectionRecordingInput prepared payload started
        complementWeights := by
  subst ownArm
  subst observation
  have hw : restrictedWeights payload weights = complementWeights := funext hweights
  cases hw
  rfl

/-- The literal checked recorder on the varying original local coordinates.
This map returns the actual failure option and successful output. -/
def collectionRecordingAtComponents {Ω : Type*} {p : Parameters}
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (round : Ω → RoundInput p rate) (payload : Ω → Payload rate)
    (started : Ω → StartRoundResult p) (weights : Ω → Fin p.K → ℝ)
    (ownArm : Ω → Fin p.K) (observation : Ω → Fin (D p + 1)) :
    Ω → Option (CoordinatorRecordingOperation.Output p) :=
  fun ω => CoordinatorRecorderComplementBridge.run
    (collectionRecordingInputAtComponents (x := round ω) (payload ω) (started ω)
      (weights ω) (ownArm ω) (observation ω))

/-- The source's real fast-complement envelope, expressed over the varying
full vector while leaving retained slow coordinates unrestricted. -/
def collectionLocalEnvelope {p : Parameters}
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (payload : Payload rate) (weights : Fin p.K → ℝ) : Prop :=
  ∀ a : Fin p.K, a ∈ payload.slowSet.val ∨
    (payload.anchor a ≤ weights a ∧ weights a ≤ 2 * payload.anchor a)

/-- The collection recorder's raw gate mass, including its uniform arm and
source-mode factors. -/
def collectionRawGateMass {p : Parameters} : ℝ :=
  (1 / 2) * (1 / 2) * (1 / (p.K : ℝ)) * recordingZeta p.m p.K

/-- The source thinning threshold for this payload and actual own arm. -/
def collectionThresholdAtComponents {p : Parameters}
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (payload : Payload rate) (ownArm : Fin p.K) : ℝ :=
  payload.rate ownArm / collectionRawGateMass (p := p)

/-- The exact real floor computed from the typed own grid observation and the
payload's canonical arm rate. -/
def collectionFloorAtComponents {p : Parameters}
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (payload : Payload rate) (ownArm : Fin p.K)
    (observation : Fin (D p + 1)) : ℕ :=
  Nat.floor (((D p : ℝ) * rate.eta.val *
    realRewardGridValue (D p) (D_pos p) observation) / payload.rate ownArm)

/-- All gates of the collection recorder in source order, on the actual
selected row slice, arm, observation, and moving source boundary. -/
def collectionRecorderGateAtComponents {p : Parameters}
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (round : RoundInput p rate) (payload : Payload rate)
    (started : StartRoundResult p) (_weights : Fin p.K → ℝ)
    (ownArm : Fin p.K) (_observation : Fin (D p + 1)) : Prop :=
  slotDraw (sliceAt round.time round.row.2) = dataSlot ∧
    recorderSourceDraw p.two_le_m p.m_lt_K (sliceAt round.time round.row.2) =
      coordinator p.two_le_m ∧
    round.time.val + 1 < started.clock.g ∧
    recordingMask (K_pos p) (coordinator p.two_le_m) ownArm
      (sliceAt round.time round.row.2) ∧
    (coordinate Label.thin (sliceAt round.time round.row.2)).val ≤
      collectionThresholdAtComponents payload ownArm

/-- Total finite code for the checked bridge output. Invalid runtime boundary
or complement-envelope data map to none; valid failed gates remain a
successful zero-arrival output. The minimum only totalizes the code, and the
validity proof below shows that it does not alter a successful raw floor. -/
def collectionRecorderCodeAtComponents {Ω : Type*} {p : Parameters}
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (round : Ω → RoundInput p rate) (payload : Ω → Payload rate)
    (started : Ω → StartRoundResult p) (weights : Ω → Fin p.K → ℝ)
    (ownArm : Ω → Fin p.K) (observation : Ω → Fin (D p + 1)) :
    Ω → Option (CoordinatorRecordingMeasurability.OutputCode p) := by
  classical
  exact fun ω =>
    if hvalid : (started ω).clock.g ≤ p.T + 1 ∧
        collectionLocalEnvelope (payload ω) (weights ω) then
      if hgate : collectionRecorderGateAtComponents (round ω) (payload ω)
          (started ω) (weights ω) (ownArm ω) (observation ω) then
        some (some (ownArm ω),
          ⟨min (D p) (collectionFloorAtComponents (payload ω) (ownArm ω)
            (observation ω)), Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩)
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
    [MeasurableSpace Ω] {ρ : ReferenceActivePhysicalStep.RateInput p}
    (round : Ω → RoundInput p ρ) (hround : Measurable round) :
    Measurable (fun ω => sliceAt (round ω).time (round ω).row.2) := by
  let family : Fin p.T → (LearningRow p × Fin p.T) → Slice p :=
    fun t z => sliceAt t z.1
  have hfamily : ∀ t, Measurable (family t) := by
    intro t
    exact (ContinuousLearningRows.measurable_sliceAt t).comp measurable_fst
  have hrow := ReferenceActivePhysicalStepMeasurability.measurable_row
    (p := p) (rate := ρ)
  have hrows : Measurable (fun x : RoundInput p ρ => x.row.2) :=
    measurable_snd.comp hrow
  have htime := ReferenceActivePhysicalStepMeasurability.measurable_time
    (p := p) (rate := ρ)
  have hselected : Measurable
      (fun z : LearningRow p × Fin p.T => family z.2 z) :=
    measurable_choose_finite (fun z : LearningRow p × Fin p.T => z.2)
      family measurable_snd hfamily
  have hpair : Measurable (fun x : RoundInput p ρ => (x.row.2, x.time)) :=
    hrows.prodMk htime
  exact (hselected.comp hpair).comp hround

private theorem measurable_collectionEnvelopeSet {Ω : Type*}
    [MeasurableSpace Ω] {ρ : ReferenceActivePhysicalStep.RateInput p}
    (payload : Ω → Payload ρ) (weights : Ω → Fin p.K → ℝ)
    (hpayload : Measurable payload) (hweights : Measurable weights) :
    MeasurableSet {ω | collectionLocalEnvelope (payload ω) (weights ω)} := by
  have hpobs : Measurable (fun ω => payloadObservation (payload ω)) :=
    comap_measurable _ |>.comp hpayload
  have hslow : Measurable (fun ω => (payloadObservation (payload ω)).2.2.1) :=
    measurable_fst.comp (measurable_snd.comp (measurable_snd.comp hpobs))
  have hanchor := AssignmentPayloadDerivedMeasurability.measurable_inputAnchor.comp
    hpayload
  have hslowMem (a : Fin p.K) :
      MeasurableSet {ω | a ∈ (payload ω).slowSet.val} := by
    have hset : MeasurableSet {s : Finset (Fin p.K) | a ∈ s} := by
      rw [show {s : Finset (Fin p.K) | a ∈ s} =
        ⋃ s : Finset (Fin p.K), if a ∈ s then ({s} : Set (Finset (Fin p.K))) else ∅ by
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

/-- Joint Borel measurability of the finite code for the actual checked
collection recorder, with all original primitive coordinates varying. -/
theorem measurable_collectionRecorderCodeAtComponents {Ω : Type*}
    [MeasurableSpace Ω] {ρ : ReferenceActivePhysicalStep.RateInput p}
    (round : Ω → RoundInput p ρ) (payload : Ω → Payload ρ)
    (started : Ω → StartRoundResult p) (weights : Ω → Fin p.K → ℝ)
    (ownArm : Ω → Fin p.K) (observation : Ω → Fin (D p + 1))
    (hround : Measurable round) (hpayload : Measurable payload)
    (hstarted : Measurable started) (hweights : Measurable weights)
    (harm : Measurable ownArm) (hobs : Measurable observation) :
    Measurable (collectionRecorderCodeAtComponents round payload started
      weights ownArm observation) := by
  classical
  let boundary := fun ω => (started ω).clock.g
  have hboundary : Measurable boundary := by
    exact (Measurable.of_discrete : Measurable
      (fun s : StartRoundResult p => s.clock.g)).comp hstarted
  have hlocal : MeasurableSet {ω | boundary ω ≤ p.T + 1 ∧
      collectionLocalEnvelope (payload ω) (weights ω)} := by
    exact (measurableSet_le hboundary measurable_const).inter
      (measurable_collectionEnvelopeSet payload weights hpayload hweights)
  let slice := fun ω => sliceAt (round ω).time (round ω).row.2
  have hslice : Measurable slice :=
    measurable_collectionSliceAtComponents round hround
  have hslot : Measurable (fun ω => slotDraw (slice ω)) :=
    PublicDiscreteDraws.measurable_slotDraw.comp hslice
  have hsource : Measurable (fun ω => recorderSourceDraw p.two_le_m p.m_lt_K
      (slice ω)) :=
    (PublicDiscreteDraws.measurable_recorderSourceDraw
      p.two_le_m p.m_lt_K).comp hslice
  have htime := ReferenceActivePhysicalStepMeasurability.measurable_time.comp hround
  have htimeVal : Measurable (fun ω => (round ω).time.val) :=
    (Measurable.of_discrete : Measurable (fun t : Fin p.T => t.val)).comp htime
  have hsourceRound : Measurable (fun ω => (round ω).time.val + 1) :=
    htimeVal.add_const 1
  have hnotFrozen : MeasurableSet {ω | (round ω).time.val + 1 < boundary ω} :=
    measurableSet_lt hsourceRound hboundary
  have hmask : MeasurableSet {ω | recordingMask (K_pos p)
      (coordinator p.two_le_m) (ownArm ω) (slice ω)} := by
    have hEq : {ω | recordingMask (K_pos p) (coordinator p.two_le_m)
        (ownArm ω) (slice ω)} =
      ⋃ a : Fin p.K, {ω | ownArm ω = a} ∩
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
  have hrateAt : Measurable (fun ω => (payload ω).rate (ownArm ω)) := by
    let family : Fin p.K → Ω → ℝ := fun a ω => (payload ω).rate a
    have hfam : ∀ a, Measurable (family a) := fun a =>
      (measurable_pi_apply a).comp hrates
    exact measurable_choose_finite ownArm family harm hfam
  have hthreshold : Measurable (fun ω => collectionThresholdAtComponents
      (payload ω) (ownArm ω)) :=
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
      collectionThresholdAtComponents (payload ω) (ownArm ω)} :=
    measurableSet_le hthin hthreshold
  have hgate : MeasurableSet {ω | collectionRecorderGateAtComponents
      (round ω) (payload ω) (started ω) (weights ω) (ownArm ω) (observation ω)} := by
    change MeasurableSet ({ω | slotDraw (slice ω) = dataSlot} ∩
      ({ω | recorderSourceDraw p.two_le_m p.m_lt_K (slice ω) =
        coordinator p.two_le_m} ∩
      ({ω | (round ω).time.val + 1 < boundary ω} ∩
      ({ω | recordingMask (K_pos p) (coordinator p.two_le_m)
        (ownArm ω) (slice ω)} ∩
      {ω | (coordinate Label.thin (slice ω)).val ≤
        collectionThresholdAtComponents (payload ω) (ownArm ω)}))))
    exact hdataSet.inter (hsourceSet.inter
      (hnotFrozen.inter (hmask.inter hthinSet)))
  have hreward : Measurable (fun ω => realRewardGridValue (D p) (D_pos p)
      (observation ω)) := by
    exact (Measurable.of_discrete : Measurable
      (fun y : Fin (D p + 1) => realRewardGridValue (D p) (D_pos p) y)).comp hobs
  have hfloorArgument : Measurable (fun ω => ((D p : ℝ) * ρ.eta.val *
      realRewardGridValue (D p) (D_pos p) (observation ω)) /
      (payload ω).rate (ownArm ω)) := by
    exact (((measurable_const : Measurable fun _ : Ω =>
      (D p : ℝ) * ρ.eta.val).mul hreward).div hrateAt)
  have hfloor : Measurable (fun ω => collectionFloorAtComponents
      (payload ω) (ownArm ω) (observation ω)) :=
    Nat.measurable_floor.comp hfloorArgument
  let arrivalFin : Ω → Fin (D p + 1) := fun ω =>
    ⟨min (D p) (collectionFloorAtComponents (payload ω) (ownArm ω)
      (observation ω)), Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩
  have harrivalFin : Measurable arrivalFin := by
    have hcast : Measurable (fun n : ℕ =>
        (⟨min (D p) n, Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩ :
          Fin (D p + 1))) := Measurable.of_discrete
    exact hcast.comp hfloor
  have hsomeArm : Measurable
      (fun ω => (some (ownArm ω) : Option (Fin p.K))) :=
    (Measurable.of_discrete :
      Measurable (some : Fin p.K → Option (Fin p.K))).comp harm
  have hsuccessCode : Measurable (fun ω => some
      ((some (ownArm ω), arrivalFin ω) :
        CoordinatorRecordingMeasurability.OutputCode p)) := by
    have hpair : Measurable (fun ω => ((some (ownArm ω) : Option (Fin p.K)),
        arrivalFin ω)) := hsomeArm.prodMk harrivalFin
    exact (Measurable.of_discrete :
      Measurable (some :
        CoordinatorRecordingMeasurability.OutputCode p →
          Option (CoordinatorRecordingMeasurability.OutputCode p))).comp hpair
  have hzeroCode : Measurable (fun _ : Ω =>
      (some (none, (⟨0, Nat.succ_pos _⟩ : Fin (D p + 1))) :
        Option (CoordinatorRecordingMeasurability.OutputCode p))) := measurable_const
  have hvalidCode : Measurable (fun ω =>
      (if collectionRecorderGateAtComponents (round ω) (payload ω)
          (started ω) (weights ω) (ownArm ω) (observation ω)
      then some (some (ownArm ω), arrivalFin ω)
      else some (none, (⟨0, Nat.succ_pos _⟩ : Fin (D p + 1))))) :=
    Measurable.ite hgate hsuccessCode hzeroCode
  exact Measurable.ite hlocal hvalidCode measurable_const

/-- The same-input code equation, including invalid-domain failure, every
zero-arrival gate rejection, and the success branch with its actual floor. -/
theorem collectionRecorderCodeAtComponents_reconstructs {x : RoundInput p rate}
    (payload : Payload rate) (started : StartRoundResult p)
    (weights : Fin p.K → ℝ) (ownArm : Fin p.K)
    (observation : Fin (D p + 1)) :
    collectionRecorderCodeAtComponents (fun _ : Unit => x) (fun _ => payload)
      (fun _ => started) (fun _ => weights) (fun _ => ownArm) (fun _ => observation) () =
      CoordinatorRecordingMeasurability.encodeResult
        (CoordinatorRecorderComplementBridge.run
          (collectionRecordingInputAtComponents (x := x) payload started
            weights ownArm observation)) := by
  classical
  let input := collectionRecordingInputAtComponents (x := x) payload started
    weights ownArm observation
  let boundary := started.clock.g
  have hEnvelope : collectionLocalEnvelope payload weights ↔
      ∀ a : FastArm payload.slowSet,
        payload.anchor a.val ≤ weights a.val ∧ weights a.val ≤ 2 * payload.anchor a.val := by
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
      slotDraw (sliceAt x.time x.row.2) := by
    simp [CoordinatorRecorderComplementBridge.selectedSlot,
      input, collectionRecordingInputAtComponents,
      CoordinatorRecorderComplementBridge.recorderInput,
      CoordinatorRecorderComplementBridge.recorderInputWithWeights,
      CoordinatorRecordingOperation.selectedSlot]
  have hsourceEq : CoordinatorRecorderComplementBridge.selectedRecorder input =
      recorderSourceDraw p.two_le_m p.m_lt_K (sliceAt x.time x.row.2) := by
    unfold CoordinatorRecorderComplementBridge.selectedRecorder
      CoordinatorRecordingOperation.selectedRecorder
    simp [input, collectionRecordingInputAtComponents,
      CoordinatorRecorderComplementBridge.recorderInput,
      CoordinatorRecorderComplementBridge.recorderInputWithWeights]
    rfl
  have hfreezeEq : CoordinatorRecorderComplementBridge.isFrozen input ↔
      ¬ x.time.val + 1 < boundary := by
    simp [CoordinatorRecorderComplementBridge.isFrozen,
      CoordinatorRecordingOperation.isFrozen,
      CoordinatorRecorderComplementBridge.recorderInput,
      CoordinatorRecorderComplementBridge.recorderInputWithWeights,
      collectionRecordingInputAtComponents, input, boundary,
      CoordinatorRecorderComplementBridge.sourceStart,
      CoordinatorRecordingOperation.sourceCalendarRound]
  have hmaskEq : CoordinatorRecorderComplementBridge.ownMaskPasses input ↔
      recordingMask (K_pos p) (coordinator p.two_le_m) ownArm
        (sliceAt x.time x.row.2) := by
    rfl
  have hthresholdEq (hvalid : CoordinatorRecorderComplementBridge.LocalInputsValid input) :
      CoordinatorRecorderComplementBridge.threshold input hvalid =
        collectionThresholdAtComponents payload ownArm := by
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
      collectionFloorAtComponents payload ownArm observation := by
    simp only [CoordinatorRecorderComplementBridge.floorArrival,
      CoordinatorRecordingOperation.floorArrival, input,
      CoordinatorRecorderComplementBridge.recorderInput,
      CoordinatorRecorderComplementBridge.recorderInputWithWeights,
      collectionRecordingInputAtComponents]
    unfold collectionFloorAtComponents
    rw [← payload.rate_eq_canonical ownArm]
  by_cases hlocal : boundary ≤ p.T + 1 ∧ collectionLocalEnvelope payload weights
  · have hvalid : CoordinatorRecorderComplementBridge.LocalInputsValid input :=
      hlocalIff.mpr hlocal
    have hopValid := CoordinatorRecorderComplementBridge.recorderInput_inputsValid input hvalid
    have hfloorBound : collectionFloorAtComponents payload ownArm observation ≤ D p := by
      rw [← hfloorEq]
      exact CoordinatorRecordingOperation.floorArrival_le_D
        (CoordinatorRecorderComplementBridge.recorderInput input) hopValid
    have howns : CoordinatorRecorderComplementBridge.ownsArm input := by
      change CoordinatorRecordingOperation.ownsArm
        (CoordinatorRecorderComplementBridge.operationMode input.mode) ownArm
      simp [CoordinatorRecorderComplementBridge.operationMode, input,
        collectionRecordingInputAtComponents, CoordinatorRecordingOperation.ownsArm]
    have hdata : CoordinatorRecorderComplementBridge.selectedSlot input = dataSlot ↔
        slotDraw (sliceAt x.time x.row.2) = dataSlot := by rw [hdataEq]
    have hsource : CoordinatorRecorderComplementBridge.selectedRecorder input =
        coordinator p.two_le_m ↔ recorderSourceDraw p.two_le_m p.m_lt_K
          (sliceAt x.time x.row.2) = coordinator p.two_le_m := by rw [hsourceEq]
    have hnotFrozen : ¬ CoordinatorRecorderComplementBridge.isFrozen input ↔
        x.time.val + 1 < boundary := by rw [hfreezeEq]; omega
    have hmask : CoordinatorRecorderComplementBridge.ownMaskPasses input ↔
        recordingMask (K_pos p) (coordinator p.two_le_m) ownArm
          (sliceAt x.time x.row.2) := hmaskEq
    have hthin : CoordinatorRecorderComplementBridge.thinScalar input ≤
        CoordinatorRecorderComplementBridge.threshold input hvalid ↔
        (coordinate Label.thin (sliceAt x.time x.row.2)).val ≤
          collectionThresholdAtComponents payload ownArm := by
      rw [hthresholdEq hvalid]
      rfl
    by_cases hgate : collectionRecorderGateAtComponents x payload started
        weights ownArm observation
    · have hgates :
          slotDraw (sliceAt x.time x.row.2) = dataSlot ∧
          recorderSourceDraw p.two_le_m p.m_lt_K (sliceAt x.time x.row.2) =
            coordinator p.two_le_m ∧
          x.time.val + 1 < boundary ∧
          recordingMask (K_pos p) (coordinator p.two_le_m) ownArm
            (sliceAt x.time x.row.2) ∧
          (coordinate Label.thin (sliceAt x.time x.row.2)).val ≤
            collectionThresholdAtComponents payload ownArm := by
        simpa [collectionRecorderGateAtComponents] using hgate
      rcases hgates with ⟨hd, hs, hf, hm, ht⟩
      have hrun := CoordinatorRecorderComplementBridge.run_gate_and_floor input hvalid
        (hdata.mp hd) (hsource.mp hs) (hnotFrozen.mpr hf) howns
        (hmask.mpr hm) (hthin.mpr ht)
      rcases hrun with ⟨out, hout, hgateArm, harrival⟩
      have hencode : CoordinatorRecordingMeasurability.encodeOutput out =
          (some ownArm, ⟨collectionFloorAtComponents payload ownArm observation,
            Nat.lt_succ_of_le hfloorBound⟩) := by
        cases out with
        | mk arm arrival bound =>
            apply Prod.ext
            · exact hgateArm
            · apply Fin.ext
              have harrival' : arrival =
                  collectionFloorAtComponents payload ownArm observation :=
                harrival.trans hfloorEq
              simp [CoordinatorRecordingMeasurability.encodeOutput, harrival']
      simp [collectionRecorderCodeAtComponents, boundary, input, hlocal, hgate, hout,
        CoordinatorRecordingMeasurability.encodeResult,
        CoordinatorRecordingMeasurability.encodeOutput,
        hfloorBound]
      exact ⟨by simpa [input, collectionRecordingInputAtComponents] using hgateArm.symm,
        by simpa [collectionFloorAtComponents] using (harrival.trans hfloorEq).symm⟩
    · by_cases hd : slotDraw (sliceAt x.time x.row.2) = dataSlot
      · by_cases hs : recorderSourceDraw p.two_le_m p.m_lt_K
            (sliceAt x.time x.row.2) = coordinator p.two_le_m
        · by_cases hf : x.time.val + 1 < boundary
          · by_cases hm : recordingMask (K_pos p) (coordinator p.two_le_m)
                ownArm (sliceAt x.time x.row.2)
            · have ht : ¬ (coordinate Label.thin (sliceAt x.time x.row.2)).val ≤
                  collectionThresholdAtComponents payload ownArm := by
                intro ht
                exact hgate (by simp [collectionRecorderGateAtComponents, boundary, hd, hs, hf, hm, ht])
              have hrun := CoordinatorRecorderComplementBridge.run_zero_of_thinning_rejected
                input hvalid (hdata.mpr hd) (hsource.mpr hs) (hnotFrozen.mpr hf)
                howns (hmask.mpr hm) (by
                  intro hthinActual
                  exact ht (hthin.mp hthinActual))
              simp [collectionRecorderCodeAtComponents, boundary, input, hlocal, hgate,
                hrun, CoordinatorRecordingMeasurability.encodeResult,
                CoordinatorRecordingMeasurability.encodeOutput,
                CoordinatorRecordingOperation.zeroOutput]
            · have hrun := CoordinatorRecorderComplementBridge.run_zero_of_mask_rejected
                input hvalid (hdata.mpr hd) (hsource.mpr hs) (hnotFrozen.mpr hf)
                howns (by
                  intro hown
                  exact hm (hmask.mp hown))
              simp [collectionRecorderCodeAtComponents, boundary, input, hlocal, hgate,
                hrun, CoordinatorRecordingMeasurability.encodeResult,
                CoordinatorRecordingMeasurability.encodeOutput,
                CoordinatorRecordingOperation.zeroOutput]
          · have hrun := CoordinatorRecorderComplementBridge.run_zero_of_frozen
              input hvalid (hdata.mpr hd) (hsource.mpr hs)
              (hfreezeEq.mpr hf)
            simp [collectionRecorderCodeAtComponents, boundary, input, hlocal, hgate,
              hrun, CoordinatorRecordingMeasurability.encodeResult,
              CoordinatorRecordingMeasurability.encodeOutput,
              CoordinatorRecordingOperation.zeroOutput]
        · have hrun := CoordinatorRecorderComplementBridge.run_zero_of_other_source
            input hvalid (hdata.mpr hd) (by rw [hsourceEq]; exact hs)
          simp [collectionRecorderCodeAtComponents, boundary, input, hlocal, hgate,
            hrun, CoordinatorRecordingMeasurability.encodeResult,
            CoordinatorRecordingMeasurability.encodeOutput,
            CoordinatorRecordingOperation.zeroOutput]
      · have hrun := CoordinatorRecorderComplementBridge.run_zero_of_not_data
          input hvalid (by rw [hdataEq]; exact hd)
        simp [collectionRecorderCodeAtComponents, boundary, input, hlocal, hgate,
          hrun, CoordinatorRecordingMeasurability.encodeResult,
          CoordinatorRecordingMeasurability.encodeOutput,
          CoordinatorRecordingOperation.zeroOutput]
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
      CoordinatorRecordingMeasurability.encodeResult]

/-- The finite code is lossless for the literal checked recorder result,
including the outer none failure and the complete retained output. -/
theorem collectionRecorderCodeAtComponents_eq_encodeResult {Ω : Type*}
    {p : Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}
    (round : Ω → RoundInput p rate) (payload : Ω → Payload rate)
    (started : Ω → StartRoundResult p) (weights : Ω → Fin p.K → ℝ)
    (ownArm : Ω → Fin p.K) (observation : Ω → Fin (D p + 1)) (ω : Ω) :
    collectionRecorderCodeAtComponents round payload started weights ownArm observation ω =
      CoordinatorRecordingMeasurability.encodeResult
        (collectionRecordingAtComponents rate round payload started weights ownArm observation ω) := by
  change collectionRecorderCodeAtComponents (fun _ : Unit => round ω)
      (fun _ => payload ω) (fun _ => started ω) (fun _ => weights ω)
      (fun _ => ownArm ω) (fun _ => observation ω) () =
    CoordinatorRecordingMeasurability.encodeResult
      (CoordinatorRecorderComplementBridge.run
        (collectionRecordingInputAtComponents (x := round ω) (payload ω)
          (started ω) (weights ω) (ownArm ω) (observation ω)))
  exact collectionRecorderCodeAtComponents_reconstructs (x := round ω)
    (payload ω) (started ω) (weights ω) (ownArm ω) (observation ω)

/-- Direct joint Borel measurability of the actual Option(Output) returned by
the collection recorder on independently varying source primitives. -/
theorem measurable_collectionRecordingAtComponents {Ω : Type*}
    [MeasurableSpace Ω] {ρ : ReferenceActivePhysicalStep.RateInput p}
    (round : Ω → RoundInput p ρ) (payload : Ω → Payload ρ)
    (started : Ω → StartRoundResult p) (weights : Ω → Fin p.K → ℝ)
    (ownArm : Ω → Fin p.K) (observation : Ω → Fin (D p + 1))
    (hround : Measurable round) (hpayload : Measurable payload)
    (hstarted : Measurable started) (hweights : Measurable weights)
    (harm : Measurable ownArm) (hobs : Measurable observation) :
    Measurable (collectionRecordingAtComponents ρ round payload started
      weights ownArm observation) := by
  have hcode := measurable_collectionRecorderCodeAtComponents
    round payload started weights ownArm observation
    hround hpayload hstarted hweights harm hobs
  have hdecode : Measurable (CoordinatorRecordingMeasurability.decodeResult :
      Option (CoordinatorRecordingMeasurability.OutputCode p) →
        Option (CoordinatorRecordingOperation.Output p)) :=
    Measurable.of_discrete
  have hrecover := collectionRecorderCodeAtComponents_eq_encodeResult
    round payload started weights ownArm observation
  have heq : collectionRecordingAtComponents ρ round payload started
      weights ownArm observation =
      CoordinatorRecordingMeasurability.decodeResult ∘
        collectionRecorderCodeAtComponents round payload started weights ownArm observation := by
    funext ω
    rw [Function.comp_apply, hrecover ω]
    exact (CoordinatorRecordingMeasurability.decodeResult_encodeResult _).symm
  rw [heq]
  exact hdecode.comp hcode

/-- On every original prepared round, using its actual coordinator arm and
observation and the same full row/time, the varying-coordinate producer is
exactly the existing collectionRecordingInput call. -/
theorem collectionRecordingAtComponents_eq_existing {x : RoundInput p rate}
    (prepared : PreparedRound x) (payload : Payload rate)
    (started : StartRoundResult p) (weights : Fin p.K → ℝ)
    (complementWeights : FastArm payload.slowSet → ℝ)
    (hweights : ∀ a, weights a.val = complementWeights a) :
    collectionRecordingAtComponents rate (fun _ : Unit => x) (fun _ => payload)
      (fun _ => started) (fun _ => weights)
      (fun _ => prepared.coordinator.arm)
      (fun _ => prepared.coordinatorObservation) () =
      CoordinatorRecorderComplementBridge.run
        (ReferenceActivePhysicalStep.collectionRecordingInput prepared payload started
          complementWeights) := by
  unfold collectionRecordingAtComponents
  rw [collectionRecordingInputAtComponents_eq prepared payload started weights
    complementWeights prepared.coordinator.arm prepared.coordinatorObservation
    rfl rfl hweights]

end Bandits.Support.ReferenceCollectionRecorderJointMeasurability

end
