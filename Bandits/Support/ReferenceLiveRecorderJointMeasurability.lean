/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceActivePhysicalStepMeasurability

/-!
# Joint Borel measurability of the actual live coordinator recorder

Sources: `sources/zip4/manuscript/05_binary_transport.tex:354-423`,
`06_interruptions.tex:256-269`, and `appendix_a_local_protocol.tex:6-14`.
The local product retains the accepted payload, canonical natural live code,
original StartRound result, finite time, WHOLE continuous CompleteRow, own arm,
and own grid observation. It carries no validity or successful-run premise.

Only the recorder is treated here. Service, confirmation, clock transitions,
physical probability laws, and manuscript/regret closure remain separate.
Direct dependency SHA-256:
`11b431bc05c6971b331016537f4e67f457e80a9c45d76940874cb30d37c6b314`.
Acceptance/source evidence: campaign control `turn-00126-dependency-evidence.json`
and `turn-00126-source-integrity.json`; exact independent review `review-0347`.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceLiveRecorderJointMeasurability

open MeasureTheory
open Bandits.Support.ConstructorDimensions

variable {p : Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}

/-- The original StartRound result is countable by its accepted field code.
Its discrete space concerns only clock naturals, finite sets and finite tags. -/
instance startRoundResultMeasurableSpace :
    MeasurableSpace (CoordinatorPhaseClock.StartRoundResult p) := ⊤

instance startRoundResultDiscreteMeasurableSpace :
    DiscreteMeasurableSpace (CoordinatorPhaseClock.StartRoundResult p) :=
  ⟨fun _ => trivial⟩

/-- Literal local product of exactly the varying inputs read by the live
recorder; no new physical state or global schema is introduced. -/
abbrev RecorderCoordinates (p : Parameters)
    (rate : ReferenceActivePhysicalStep.RateInput p) :=
  ReferenceActivePhysicalStep.Payload rate ×
    ReferenceActivePhysicalStepMeasurability.LiveDiscrete p ×
      CoordinatorPhaseClock.StartRoundResult p ×
        Fin p.T ×
          CompletePublicTable.CompleteRow p × Fin p.K × Fin (D p + 1)

def recorderPayload (z : RecorderCoordinates p rate) := z.1

def recorderLiveCode (z : RecorderCoordinates p rate) := z.2.1

def recorderStarted (z : RecorderCoordinates p rate) := z.2.2.1

def recorderTime (z : RecorderCoordinates p rate) := z.2.2.2.1

def recorderRow (z : RecorderCoordinates p rate) := z.2.2.2.2.1

def recorderOwnArm (z : RecorderCoordinates p rate) := z.2.2.2.2.2.1

def recorderObservation (z : RecorderCoordinates p rate) := z.2.2.2.2.2.2

theorem measurable_recorderPayload :
    Measurable (recorderPayload (p := p) (rate := rate)) := measurable_fst

theorem measurable_recorderLiveCode :
    Measurable (recorderLiveCode (p := p) (rate := rate)) :=
  measurable_fst.comp measurable_snd

theorem measurable_recorderStarted :
    Measurable (recorderStarted (p := p) (rate := rate)) :=
  measurable_fst.comp (measurable_snd.comp measurable_snd)

theorem measurable_recorderTime :
    Measurable (recorderTime (p := p) (rate := rate)) :=
  measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))

theorem measurable_recorderOwnArm :
    Measurable (recorderOwnArm (p := p) (rate := rate)) :=
  measurable_fst.comp (measurable_snd.comp (measurable_snd.comp
    (measurable_snd.comp (measurable_snd.comp measurable_snd))))

theorem measurable_recorderObservation :
    Measurable (recorderObservation (p := p) (rate := rate)) :=
  measurable_snd.comp (measurable_snd.comp (measurable_snd.comp
    (measurable_snd.comp (measurable_snd.comp measurable_snd))))

def fullCurrentWeights (z : RecorderCoordinates p rate) :
    Fin p.K → ℝ := fun arm =>
  if arm ∈ (recorderPayload z).slowSet.val then
    (recorderPayload z).anchor arm
  else
    ScoreWeights.scoreWeight (AssignmentScoreReconstruction.sourceWeightBase p)
      ((recorderLiveCode z).scores arm)

theorem measurable_recorderPayloadSlowSet :
    Measurable (fun z : RecorderCoordinates p rate =>
      (recorderPayload z).slowSet.1) := by
  have hpayloadObservation :
      Measurable (LaterAssignmentStartMeasurability.payloadObservation
        (p := p) (eta := rate.eta)) := comap_measurable _
  change Measurable (fun z : RecorderCoordinates p rate =>
    (LaterAssignmentStartMeasurability.payloadObservation (recorderPayload z)).2.2.1)
  exact measurable_fst.comp (measurable_snd.comp
    (measurable_snd.comp (hpayloadObservation.comp measurable_recorderPayload)))

theorem measurable_fullCurrentWeights :
    Measurable (fullCurrentWeights (p := p) (rate := rate)) := by
  apply measurable_pi_iff.mpr
  intro arm
  let inSlowSet : Finset (Fin p.K) → Bool := fun slow => decide (arm ∈ slow)
  have hslowMember : Measurable (fun z : RecorderCoordinates p rate =>
      inSlowSet ((recorderPayload z).slowSet.1)) :=
    (Measurable.of_discrete : Measurable inSlowSet).comp
      measurable_recorderPayloadSlowSet
  have hmemberSet : MeasurableSet {z : RecorderCoordinates p rate |
      inSlowSet ((recorderPayload z).slowSet.1) = true} :=
    measurableSet_eq_fun hslowMember measurable_const
  have han :=
    (AssignmentPayloadDerivedMeasurability.measurable_inputAnchor
      (p := p) (eta := rate.eta)).comp measurable_recorderPayload
  have hanarm := (measurable_pi_apply arm).comp han
  let weightOfCode : ReferenceActivePhysicalStepMeasurability.LiveDiscrete p → ℝ :=
    fun code => ScoreWeights.scoreWeight (AssignmentScoreReconstruction.sourceWeightBase p)
      (code.scores arm)
  have hweightOfCode : Measurable weightOfCode := Measurable.of_discrete
  have hweight := hweightOfCode.comp
    (measurable_recorderLiveCode (p := p) (rate := rate))
  change Measurable (fun z : RecorderCoordinates p rate =>
    if arm ∈ (recorderPayload z).slowSet.val then (recorderPayload z).anchor arm
    else ScoreWeights.scoreWeight (AssignmentScoreReconstruction.sourceWeightBase p)
      ((recorderLiveCode z).scores arm))
  exact Measurable.ite (by
    simpa [inSlowSet] using hmemberSet) hanarm hweight

theorem measurable_inverseAnchorSum (U : Finset (Fin p.K)) :
    Measurable (fun anchor : Fin p.K → ℝ =>
      FiniteOrientationDisintegration.inverseAnchorSum anchor U) := by
  unfold FiniteOrientationDisintegration.inverseAnchorSum
  exact Finset.measurable_fun_sum U fun i _ =>
    measurable_const.div (measurable_pi_apply i)

theorem measurable_candidateWeight (U : Finset (Fin p.K))
    (j : Fin p.K) :
    Measurable (fun value : (Fin p.K → ℝ) × (Fin p.K → ℝ) =>
      FiniteOrientationDisintegration.candidateWeight value.2 value.1 U j) := by
  have hfst : Measurable (fun value : (Fin p.K → ℝ) × (Fin p.K → ℝ) => value.1) :=
    measurable_fst
  have hsnd : Measurable (fun value : (Fin p.K → ℝ) × (Fin p.K → ℝ) => value.2) :=
    measurable_snd
  have hinv := (measurable_inverseAnchorSum (p := p) U).comp hfst
  have hanchor := (measurable_pi_apply j).comp hfst
  have hweight := (measurable_pi_apply j).comp hsnd
  unfold FiniteOrientationDisintegration.candidateWeight
  exact hweight.div (measurable_const.add (hinv.mul hanchor))

theorem measurable_candidateNormalizer (U : Finset (Fin p.K)) :
    Measurable (fun value : (Fin p.K → ℝ) × (Fin p.K → ℝ) =>
      FiniteOrientationDisintegration.candidateNormalizer
        (Finset.univ : Finset (Fin p.K)) value.2 value.1 U) := by
  unfold FiniteOrientationDisintegration.candidateNormalizer
  exact Finset.measurable_fun_sum _ fun j _ =>
    measurable_candidateWeight (p := p) U j.1

def qGammaFormula
    (U : Finset (Fin p.K))
    (value : (Fin p.K → ℝ) × (Fin p.K → ℝ))
    (j : Fin p.K) : ℝ :=
  (1 - CanonicalRecordingRates.gamma p rate.eta.val) *
      (FiniteOrientationDisintegration.candidateWeight value.2 value.1 U j /
        FiniteOrientationDisintegration.candidateNormalizer
          (Finset.univ : Finset (Fin p.K)) value.2 value.1 U) +
    CanonicalRecordingRates.gamma p rate.eta.val /
      ((p.K - p.m + 1 : ℕ) : ℝ)

theorem measurable_qGammaFormula
    (U : Finset (Fin p.K))
    (j : Fin p.K) :
    Measurable (qGammaFormula (p := p) (rate := rate) U · j) := by
  have hweight := measurable_candidateWeight (p := p) U j
  have hnorm := measurable_candidateNormalizer (p := p) U
  unfold qGammaFormula
  fun_prop

def qGammaAtArm
    (U : Finset (Fin p.K))
    (value : (Fin p.K → ℝ) × (Fin p.K → ℝ))
    (arm : Fin p.K) : ℝ :=
  if arm ∈ (Finset.univ : Finset (Fin p.K)) \ U then
    qGammaFormula (p := p) (rate := rate) U value arm
  else 0

theorem measurable_qGammaAtArm
    (U : Finset (Fin p.K)) (arm : Fin p.K) :
    Measurable (qGammaAtArm (p := p) (rate := rate) U · arm) := by
  unfold qGammaAtArm
  split_ifs
  · exact measurable_qGammaFormula (p := p) U arm
  · exact measurable_const

private theorem measurable_of_countable_code {α β γ : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [Countable β] [MeasurableSingletonClass β]
    [MeasurableSpace γ]
    (code : α → β) (hcode : Measurable code) (fiber : β → α → γ)
    (hfiber : ∀ b, Measurable (fun x => fiber b x)) :
    Measurable (fun x => fiber (code x) x) := by
  have h : Measurable (fun z : β × α => fiber z.1 z.2) :=
    measurable_from_prod_countable_right hfiber
  exact h.comp (hcode.prodMk measurable_id)

theorem measurable_recorderQGammaAtArm :
    Measurable (fun z : RecorderCoordinates p rate =>
      qGammaAtArm (p := p) (rate := rate)
        (recorderPayload z).slowSet.1
        ((recorderPayload z).anchor, fullCurrentWeights z) (recorderOwnArm z)) := by
  refine measurable_of_countable_code
    (α := RecorderCoordinates p rate)
    (β := Finset (Fin p.K) × Fin p.K)
    (γ := ℝ)
    (code := fun z : RecorderCoordinates p rate =>
      ((recorderPayload z).slowSet.1, recorderOwnArm z))
    (fiber := fun code z => qGammaAtArm (p := p) (rate := rate)
      code.1 ((recorderPayload z).anchor, fullCurrentWeights z) code.2) ?_ ?_
  · exact measurable_recorderPayloadSlowSet.prodMk
      (measurable_recorderOwnArm (p := p) (rate := rate))
  · intro code
    have hvalue : Measurable (fun z : RecorderCoordinates p rate =>
        ((recorderPayload z).anchor, fullCurrentWeights z)) :=
      ((AssignmentPayloadDerivedMeasurability.measurable_inputAnchor
          (p := p) (eta := rate.eta)).comp measurable_recorderPayload).prodMk
        measurable_fullCurrentWeights
    exact (measurable_qGammaAtArm (p := p) (rate := rate) code.1 code.2).comp
      hvalue

def armProbability (z : RecorderCoordinates p rate) : ℝ :=
  if (recorderStarted z).pending = ∅ then
    qGammaAtArm (p := p) (rate := rate)
    (recorderPayload z).slowSet.1
    ((recorderPayload z).anchor, fullCurrentWeights z) (recorderOwnArm z)
  else 1 / (p.K : ℝ)

theorem measurable_armProbability :
    Measurable (armProbability (p := p) (rate := rate)) := by
  let pendingEmpty : CoordinatorPhaseClock.StartRoundResult p → Bool :=
    fun started => decide (started.pending = ∅)
  have hpending : Measurable (fun z : RecorderCoordinates p rate =>
      pendingEmpty (recorderStarted z)) := by
    have hdiscrete : Measurable pendingEmpty := Measurable.of_discrete
    exact hdiscrete.comp
      (measurable_fst.comp (measurable_snd.comp measurable_snd))
  have hpendingSet : MeasurableSet {z : RecorderCoordinates p rate |
      pendingEmpty (recorderStarted z) = true} :=
    measurableSet_eq_fun hpending measurable_const
  change Measurable (fun z : RecorderCoordinates p rate =>
    if (recorderStarted z).pending = ∅ then
      qGammaAtArm (p := p) (rate := rate)
      (recorderPayload z).slowSet.1
      ((recorderPayload z).anchor, fullCurrentWeights z) (recorderOwnArm z)
    else 1 / (p.K : ℝ))
  exact Measurable.ite (by
    simpa [pendingEmpty, recorderStarted] using hpendingSet)
      measurable_recorderQGammaAtArm measurable_const

def recorderXi (z : RecorderCoordinates p rate) : ℝ :=
  CanonicalRecordingRates.xi p rate.eta.val
    (recorderPayload z).anchor (recorderOwnArm z)

theorem measurable_recorderXi :
    Measurable (recorderXi (p := p) (rate := rate)) := by
  change Measurable (fun z : RecorderCoordinates p rate =>
    AssignmentPayloadDerivedMeasurability.inputRate (recorderPayload z) (recorderOwnArm z))
  refine measurable_of_countable_code
    (α := RecorderCoordinates p rate) (β := Fin p.K) (γ := ℝ)
    (code := recorderOwnArm) (fiber := fun arm z =>
      AssignmentPayloadDerivedMeasurability.inputRate (recorderPayload z) arm) ?_ ?_
  · exact measurable_recorderOwnArm (p := p) (rate := rate)
  · intro arm
    exact (measurable_pi_apply arm).comp
      ((AssignmentPayloadDerivedMeasurability.measurable_inputRate
        (p := p) (eta := rate.eta)).comp measurable_recorderPayload)

def rawGateMass (z : RecorderCoordinates p rate) : ℝ :=
  (1 / 2) * (1 / 2) * armProbability (p := p) (rate := rate) z *
    CanonicalRecordingSlice.recordingZeta p.m p.K

theorem measurable_rawGateMass :
    Measurable (rawGateMass (p := p) (rate := rate)) := by
  unfold rawGateMass
  convert (measurable_armProbability (p := p) (rate := rate)).const_mul
      ((1 / 2 : ℝ) * (1 / 2) * CanonicalRecordingSlice.recordingZeta p.m p.K)
    using 1
  funext z
  ring

def threshold (z : RecorderCoordinates p rate) : ℝ :=
  recorderXi (p := p) (rate := rate) z /
    rawGateMass (p := p) (rate := rate) z

theorem measurable_threshold :
    Measurable (threshold (p := p) (rate := rate)) := by
  exact measurable_recorderXi.div measurable_rawGateMass

def floorArrival (z : RecorderCoordinates p rate) : ℕ :=
  Nat.floor (((D p : ℝ) * rate.eta.val *
    RealRewardGridCount.realRewardGridValue (D p) (D_pos p) (recorderObservation z)) /
      recorderXi (p := p) (rate := rate) z)

theorem measurable_floorArrival :
    Measurable (floorArrival (p := p) (rate := rate)) := by
  have hvalue : Measurable (fun z : RecorderCoordinates p rate =>
      RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
        (recorderObservation z)) := by
    have hgrid : Measurable
        (RealRewardGridCount.realRewardGridValue (D p) (D_pos p) :
          Fin (D p + 1) → ℝ) := Measurable.of_discrete
    exact hgrid.comp (measurable_recorderObservation (p := p) (rate := rate))
  have hscaled : Measurable (fun z : RecorderCoordinates p rate =>
      (D p : ℝ) * rate.eta.val *
        RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
          (recorderObservation z)) := by
    exact hvalue.const_mul ((D p : ℝ) * rate.eta.val)
  have hargument : Measurable (fun z : RecorderCoordinates p rate =>
      ((D p : ℝ) * rate.eta.val *
        RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
          (recorderObservation z)) /
        recorderXi (p := p) (rate := rate) z) :=
    hscaled.div measurable_recorderXi
  exact Nat.measurable_floor.comp hargument

theorem measurable_recorderRow :
    Measurable (recorderRow (p := p) (rate := rate)) :=
  measurable_fst.comp (measurable_snd.comp (measurable_snd.comp
    (measurable_snd.comp measurable_snd)))

def recorderRegisters (z : RecorderCoordinates p rate) :=
  ReferenceActivePhysicalStepMeasurability.decodeLiveRegisters
    (recorderPayload z) (recorderLiveCode z)

/-- The exact bridge input used after the live coordinator's arm and feedback
have already been chosen. -/
def recordingInput (z : RecorderCoordinates p rate) :
    CoordinatorRecorderComplementBridge.Input (recorderPayload z) := {
  currentWeights := (recorderRegisters z).complementWeights
  time := recorderTime z
  gridBoundary := (recorderStarted z).clock.g
  row := recorderRow z
  ownArm := recorderOwnArm z
  observation := recorderObservation z
  mode := .live (decide ((recorderStarted z).pending = ∅)) }

/-- The exact accepted recorder input after extending only the complement
weights by the original payload anchor on its stored slow set. -/
def operationInput (z : RecorderCoordinates p rate) :
    CoordinatorRecordingOperation.Input p :=
  CoordinatorRecorderComplementBridge.recorderInput (recordingInput z)

theorem operationInput_currentWeights
    (z : RecorderCoordinates p rate) (arm : Fin p.K) :
    (operationInput z).currentWeights arm = fullCurrentWeights z arm := by
  change CoordinatorRecorderComplementBridge.extendedCurrentWeights
      (recordingInput z) arm = fullCurrentWeights z arm
  by_cases hmem : arm ∈ (recorderPayload z).slowSet.val
  · rw [CoordinatorRecorderComplementBridge.extendedCurrentWeights_eq_anchor _ arm hmem]
    exact (ite_eq_left (t := (recorderPayload z).anchor arm) hmem).symm
  · have hmem' : arm ∉ z.1.slowSet.val := by simpa [recorderPayload] using hmem
    simp [CoordinatorRecorderComplementBridge.extendedCurrentWeights,
      recordingInput, recorderRegisters, recorderPayload, recorderLiveCode,
      ReferenceActivePhysicalStepMeasurability.decodeLiveRegisters,
      CoordinatorLiveChoiceRecorderStep.Registers.complementWeights,
      fullCurrentWeights, hmem']

theorem armProbability_eq_actual
    (z : RecorderCoordinates p rate)
    (hvalid : CoordinatorRecordingOperation.InputsValid
      (operationInput z)) :
    CoordinatorRecordingOperation.coordinatorArmProbability
        (operationInput z) hvalid =
      armProbability z := by
  classical
  have hmode : (operationInput z).mode =
      CoordinatorRecordingOperation.LocalMode.live
        (recorderPayload z).assignment (decide ((recorderStarted z).pending = ∅)) := rfl
  have hslow :=
    CoordinatorRecorderComplementBridge.assignmentSlowSet_eq_payload
      (recorderPayload z)
  have hweights : (operationInput z).currentWeights =
      fullCurrentWeights z := by
    funext arm
    exact operationInput_currentWeights z arm
  by_cases hpending : (recorderStarted z).pending = ∅
  · have hempty : decide ((recorderStarted z).pending = ∅) = true :=
      decide_eq_true hpending
    rw [armProbability, ite_eq_left hpending]
    rw [CoordinatorRecordingOperation.coordinatorArmProbability, hmode]
    simp only [hempty]
    by_cases hfast : recorderOwnArm z ∈
        CanonicalFastSampling.fastArmFinset (recorderPayload z).slowSet
    · have hfast' : recorderOwnArm z ∈ CanonicalFastSampling.fastArmFinset
          (SnapshotRecordingKernel.assignmentSlowSet p
            (recorderPayload z).assignment) := by
        simpa [hslow] using hfast
      have hfastActual : (operationInput z).ownArm ∈
          CanonicalFastSampling.fastArmFinset
            (SnapshotRecordingKernel.assignmentSlowSet p
              (recorderPayload z).assignment) := by
        simpa [operationInput,
          CoordinatorRecorderComplementBridge.recorderInput,
          CoordinatorRecorderComplementBridge.recorderInputWithWeights,
          recordingInput, recorderOwnArm, hslow] using hfast'
      rw [dite_eq_left hfastActual]
      have hq : CanonicalFastSampling.qGamma p rate.eta.val
          hvalid.eta_pos hvalid.eta_source_cap
          (recorderPayload z).anchor (operationInput z).currentWeights
          hvalid.anchor_pos hvalid.current_pos hvalid.anchor_le_current
          hvalid.current_le_twice_anchor
          (SnapshotRecordingKernel.assignmentSlowSet p
            (recorderPayload z).assignment)
          ⟨recorderOwnArm z, hfast'⟩ =
        qGammaFormula (p := p) (rate := rate)
          (recorderPayload z).slowSet.1
          ((recorderPayload z).anchor, fullCurrentWeights z) (recorderOwnArm z) := by
        simp [CanonicalFastSampling.qGamma,
          FiniteOrientationDisintegration.conditionalFastLaw,
          qGammaFormula, hslow, hweights]
      change CanonicalFastSampling.qGamma p rate.eta.val
        hvalid.eta_pos hvalid.eta_source_cap (recorderPayload z).anchor
        (operationInput z).currentWeights hvalid.anchor_pos hvalid.current_pos
        hvalid.anchor_le_current hvalid.current_le_twice_anchor
        (SnapshotRecordingKernel.assignmentSlowSet p (recorderPayload z).assignment)
        ⟨recorderOwnArm z, hfast'⟩ = _
      rw [hq]
      simp [qGammaAtArm, hfast]
    · have hfast' : recorderOwnArm z ∉ CanonicalFastSampling.fastArmFinset
          (SnapshotRecordingKernel.assignmentSlowSet p
            (recorderPayload z).assignment) := by
        simpa [hslow] using hfast
      have hfastActual : (operationInput z).ownArm ∉
          CanonicalFastSampling.fastArmFinset
            (SnapshotRecordingKernel.assignmentSlowSet p
              (recorderPayload z).assignment) := by
        simpa [operationInput,
          CoordinatorRecorderComplementBridge.recorderInput,
          CoordinatorRecorderComplementBridge.recorderInputWithWeights,
          recordingInput, recorderOwnArm, hslow] using hfast'
      rw [dite_eq_right hfastActual]
      simp [qGammaAtArm, hfast]
  · have hnotempty : decide ((recorderStarted z).pending = ∅) = false :=
      decide_eq_false hpending
    rw [armProbability, ite_eq_right hpending]
    rw [CoordinatorRecordingOperation.coordinatorArmProbability, hmode]
    simp [hnotempty]

theorem measurable_recorderValidity :
    MeasurableSet {z : RecorderCoordinates p rate |
      CoordinatorRecorderComplementBridge.LocalInputsValid
        (recordingInput z)} := by
  let slow := fun z : RecorderCoordinates p rate =>
    (recorderPayload z).slowSet.1
  let weights := fullCurrentWeights (p := p) (rate := rate)
  let anchor := fun z : RecorderCoordinates p rate => (recorderPayload z).anchor
  have hslow : Measurable slow := measurable_recorderPayloadSlowSet
  have hanchor : Measurable anchor :=
    (AssignmentPayloadDerivedMeasurability.measurable_inputAnchor
      (p := p) (eta := rate.eta)).comp measurable_recorderPayload
  have hboundaryValue : Measurable (fun z : RecorderCoordinates p rate =>
      (recorderStarted z).clock.g) := by
    have hcode : Measurable (fun s : CoordinatorPhaseClock.StartRoundResult p =>
        s.clock.g) := Measurable.of_discrete
    exact hcode.comp (measurable_recorderStarted (p := p) (rate := rate))
  have hboundary : MeasurableSet {z : RecorderCoordinates p rate |
      (recorderStarted z).clock.g ≤ p.T + 1} :=
    measurableSet_le hboundaryValue measurable_const
  have henv : MeasurableSet {z : RecorderCoordinates p rate |
      ∀ j : CanonicalFastSampling.FastArm (recorderPayload z).slowSet,
        (recorderPayload z).anchor j.1 ≤
            (recordingInput z).currentWeights j ∧
          (recordingInput z).currentWeights j ≤
            2 * (recorderPayload z).anchor j.1} := by
    have henvArm : ∀ arm : Fin p.K, MeasurableSet
        {z : RecorderCoordinates p rate |
          arm ∈ slow z ∨ anchor z arm ≤ weights z arm ∧
            weights z arm ≤ 2 * anchor z arm} := by
      intro arm
      let member : Finset (Fin p.K) → Bool := fun s => decide (arm ∈ s)
      have hmember0 : Measurable member := Measurable.of_discrete
      have hmember : Measurable (fun z : RecorderCoordinates p rate =>
          member (slow z)) := hmember0.comp hslow
      have hmemberSet : MeasurableSet {z : RecorderCoordinates p rate |
          member (slow z) = true} := measurableSet_eq_fun hmember measurable_const
      have han := (measurable_pi_apply arm).comp hanchor
      have hw := (measurable_pi_apply arm).comp
        (measurable_fullCurrentWeights (p := p) (rate := rate))
      have hlower := measurableSet_le han hw
      have hupper := measurableSet_le hw (han.const_mul (2 : ℝ))
      have hshape : {z : RecorderCoordinates p rate |
          arm ∈ slow z ∨ anchor z arm ≤ weights z arm ∧
            weights z arm ≤ 2 * anchor z arm} =
          {z | member (slow z) = true} ∪
            ({z | anchor z arm ≤ weights z arm} ∩
              {z | weights z arm ≤ 2 * anchor z arm}) := by
        ext z
        simp [member]
      rw [hshape]
      exact hmemberSet.union (hlower.inter hupper)
    have heq : {z : RecorderCoordinates p rate |
        ∀ j : CanonicalFastSampling.FastArm (recorderPayload z).slowSet,
          (recorderPayload z).anchor j.1 ≤
              (recordingInput z).currentWeights j ∧
            (recordingInput z).currentWeights j ≤
              2 * (recorderPayload z).anchor j.1} =
        {z | ∀ arm : Fin p.K, arm ∈ slow z ∨
          anchor z arm ≤ weights z arm ∧ weights z arm ≤ 2 * anchor z arm} := by
      ext z
      constructor
      · intro h arm
        by_cases hslowArm : arm ∈ slow z
        · exact Or.inl hslowArm
        · right
          let j : CanonicalFastSampling.FastArm (recorderPayload z).slowSet :=
            ⟨arm, Finset.mem_sdiff.mpr ⟨Finset.mem_univ arm, hslowArm⟩⟩
          have hj := h j
          have hw : (recordingInput z).currentWeights j = weights z arm := by
            calc
              (recordingInput z).currentWeights j =
                  CoordinatorRecorderComplementBridge.extendedCurrentWeights
                    (recordingInput z) j.1 :=
                (CoordinatorRecorderComplementBridge.extendedCurrentWeights_eq_complement
                  (recordingInput z) j).symm
              _ = (operationInput z).currentWeights j.1 := rfl
              _ = weights z arm := by
                simpa [weights, fullCurrentWeights, hslowArm] using
                  operationInput_currentWeights z arm
          simpa [anchor, j, hw] using hj
      · intro h j
        have hnot : j.1 ∉ slow z := (Finset.mem_sdiff.mp j.2).2
        rcases h j.1 with hslowArm | hbound
        · exact False.elim (hnot hslowArm)
        · have hw : (recordingInput z).currentWeights j = weights z j.1 := by
            calc
              (recordingInput z).currentWeights j =
                  CoordinatorRecorderComplementBridge.extendedCurrentWeights
                    (recordingInput z) j.1 :=
                (CoordinatorRecorderComplementBridge.extendedCurrentWeights_eq_complement
                  (recordingInput z) j).symm
              _ = (operationInput z).currentWeights j.1 := rfl
              _ = weights z j.1 := by
                simpa [weights, fullCurrentWeights, hnot] using
                  operationInput_currentWeights z j.1
          simpa [anchor, hw] using hbound
    rw [heq]
    have hset : {z : RecorderCoordinates p rate |
        ∀ arm : Fin p.K, arm ∈ slow z ∨
          anchor z arm ≤ weights z arm ∧ weights z arm ≤ 2 * anchor z arm} =
        ⋂ arm : Fin p.K, {z : RecorderCoordinates p rate |
          arm ∈ slow z ∨ anchor z arm ≤ weights z arm ∧
            weights z arm ≤ 2 * anchor z arm} := by
      ext z
      simp
    rw [hset]
    exact MeasurableSet.iInter henvArm
  change MeasurableSet {z : RecorderCoordinates p rate |
    (recorderStarted z).clock.g ≤ p.T + 1 ∧
      ∀ j : CanonicalFastSampling.FastArm (recorderPayload z).slowSet,
        (recorderPayload z).anchor j.1 ≤
            (recordingInput z).currentWeights j ∧
          (recordingInput z).currentWeights j ≤
            2 * (recorderPayload z).anchor j.1}
  exact hboundary.inter henv

def rowSlice (z : RecorderCoordinates p rate) :
    ContinuousLearningRows.Slice p :=
  ContinuousLearningRows.sliceAt (recorderTime z) (recorderRow z).2

theorem measurable_rowSlice :
    Measurable (rowSlice (p := p) (rate := rate)) := by
  refine measurable_of_countable_code
    (α := RecorderCoordinates p rate) (β := Fin p.T)
    (γ := ContinuousLearningRows.Slice p)
    (code := recorderTime) (fiber := fun t z =>
      ContinuousLearningRows.sliceAt t (recorderRow z).2) ?_ ?_
  · exact measurable_recorderTime (p := p) (rate := rate)
  · intro t
    exact (ContinuousLearningRows.measurable_sliceAt t).comp
      (measurable_snd.comp (measurable_recorderRow (p := p) (rate := rate)))


/-- The literal canonical rate is the payload's actual derived rate. -/
theorem recorderXi_eq_payload_rate (z : RecorderCoordinates p rate) :
    recorderXi z = (recorderPayload z).rate (recorderOwnArm z) := rfl

theorem rawGateMass_eq_actual (z : RecorderCoordinates p rate)
    (hvalid : CoordinatorRecordingOperation.InputsValid (operationInput z)) :
    CoordinatorRecordingOperation.coordinatorRawGateMass (operationInput z) hvalid =
      rawGateMass z := by
  unfold CoordinatorRecordingOperation.coordinatorRawGateMass rawGateMass
  rw [armProbability_eq_actual z hvalid]

theorem threshold_eq_actual (z : RecorderCoordinates p rate)
    (hvalid : CoordinatorRecordingOperation.InputsValid (operationInput z)) :
    CoordinatorRecordingOperation.coordinatorThreshold (operationInput z) hvalid =
      threshold z := by
  unfold CoordinatorRecordingOperation.coordinatorThreshold threshold
  rw [rawGateMass_eq_actual z hvalid]
  rfl

theorem floorArrival_eq_actual (z : RecorderCoordinates p rate) :
    CoordinatorRecordingOperation.floorArrival (operationInput z) = floorArrival z := rfl

theorem measurableSet_inputsValid :
    MeasurableSet {z : RecorderCoordinates p rate |
      CoordinatorRecordingOperation.InputsValid (operationInput z)} := by
  have heq : {z : RecorderCoordinates p rate |
      CoordinatorRecordingOperation.InputsValid (operationInput z)} =
      {z | CoordinatorRecorderComplementBridge.LocalInputsValid (recordingInput z)} := by
    ext z
    exact CoordinatorRecorderComplementBridge.recorderInput_inputsValid_iff _
  rw [heq]
  exact measurable_recorderValidity

theorem measurable_selectedSlot :
    Measurable (fun z : RecorderCoordinates p rate =>
      CoordinatorRecordingOperation.selectedSlot (operationInput z)) := by
  exact (PublicDiscreteDraws.measurable_slotDraw (m := p.m) (K := p.K)).comp
    measurable_rowSlice

theorem measurable_selectedRecorder :
    Measurable (fun z : RecorderCoordinates p rate =>
      CoordinatorRecordingOperation.selectedRecorder (operationInput z)) := by
  exact (PublicDiscreteDraws.measurable_recorderSourceDraw p.two_le_m p.m_lt_K).comp
    measurable_rowSlice

theorem measurableSet_isFrozen :
    MeasurableSet {z : RecorderCoordinates p rate |
      CoordinatorRecordingOperation.isFrozen (operationInput z)} := by
  have hround : Measurable (fun z : RecorderCoordinates p rate =>
      (recorderTime z).val + 1) :=
    (Measurable.of_discrete : Measurable (fun t : Fin p.T => t.val + 1)).comp
      measurable_recorderTime
  have hboundary : Measurable (fun z : RecorderCoordinates p rate =>
      (recorderStarted z).clock.g) :=
    (Measurable.of_discrete : Measurable (fun s : CoordinatorPhaseClock.StartRoundResult p =>
      s.clock.g)).comp measurable_recorderStarted
  have heq : {z : RecorderCoordinates p rate |
      CoordinatorRecordingOperation.isFrozen (operationInput z)} =
      {z | (recorderStarted z).clock.g ≤ (recorderTime z).val + 1} := by
    ext z
    change (0 < (recorderPayload z).sigma.val + 1 ∧
      (recorderTime z).val + 1 ≥ (recorderStarted z).clock.g) ↔ _
    exact and_iff_right (Nat.zero_lt_succ _)
  rw [heq]
  exact measurableSet_le hboundary hround

theorem measurableSet_ownsArm :
    MeasurableSet {z : RecorderCoordinates p rate |
      CoordinatorRecordingOperation.ownsArm (operationInput z).mode (recorderOwnArm z)} := by
  let owns : Finset (Fin p.K) × Fin p.K → Bool := fun c => decide (c.2 ∉ c.1)
  have howns : Measurable (fun z : RecorderCoordinates p rate =>
      owns ((recorderPayload z).slowSet.1, recorderOwnArm z)) :=
    (Measurable.of_discrete : Measurable owns).comp
      (measurable_recorderPayloadSlowSet.prodMk measurable_recorderOwnArm)
  have heq : {z : RecorderCoordinates p rate |
      CoordinatorRecordingOperation.ownsArm (operationInput z).mode (recorderOwnArm z)} =
      {z | owns ((recorderPayload z).slowSet.1, recorderOwnArm z) = true} := by
    ext z
    change (recorderOwnArm z ∉ (SnapshotRecordingKernel.assignmentSlowSet p
      (recorderPayload z).assignment).val) ↔ _
    rw [CoordinatorRecorderComplementBridge.assignmentSlowSet_eq_payload]
    simp only [owns, decide_eq_true_eq, Set.mem_ofPred_eq]
  rw [heq]
  exact measurableSet_eq_fun howns measurable_const

theorem measurableSet_ownMaskPasses :
    MeasurableSet {z : RecorderCoordinates p rate |
      CoordinatorRecordingOperation.ownMaskPasses (operationInput z)} := by
  have heq : {z : RecorderCoordinates p rate |
      CoordinatorRecordingOperation.ownMaskPasses (operationInput z)} =
      ⋃ arm : Fin p.K, {z | recorderOwnArm z = arm} ∩
        {z | CanonicalRecordingSlice.recordingMask (K_pos p)
          (ActiveRoundActions.coordinator p.two_le_m) arm (rowSlice z)} := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff,
      CoordinatorRecordingOperation.ownMaskPasses]
    constructor
    · intro h
      exact ⟨recorderOwnArm z, rfl, h⟩
    · rintro ⟨arm, harm, hmask⟩
      change CanonicalRecordingSlice.recordingMask (K_pos p)
        (ActiveRoundActions.coordinator p.two_le_m) (recorderOwnArm z) (rowSlice z)
      rw [harm]
      exact hmask
  rw [heq]
  exact MeasurableSet.iUnion fun arm =>
    (measurableSet_eq_fun measurable_recorderOwnArm measurable_const).inter
      ((CanonicalRecordingSlice.measurableSet_recordingMask p.two_le_m (K_pos p)
        (ActiveRoundActions.coordinator p.two_le_m) arm).preimage measurable_rowSlice)

/-- The actual output-domain check, with both output fields retained. This is
only the final branch of the recorder, not a supplied successful-output law. -/
def checkedArrival (c : Fin p.K × ℕ) : Option (CoordinatorRecordingOperation.Output p) :=
  if h : c.2 ≤ D p then some ⟨some c.1, c.2, h⟩ else none

/-- Literal source-ordered checks, with the actual conditional qGamma
unfolded into its Borel formula. Ordinary no-arrival branches remain successful
zero outputs. Failed input, denominator, parameter and output checks reject. -/
def checkedRun (z : RecorderCoordinates p rate) :
    Option (CoordinatorRecordingOperation.Output p) := by
  classical
  exact
    if CoordinatorRecorderComplementBridge.LocalInputsValid (recordingInput z) then
      if CoordinatorRecordingOperation.selectedSlot (operationInput z) =
          PublicDiscreteDraws.dataSlot then
        if CoordinatorRecordingOperation.selectedRecorder (operationInput z) =
            ActiveRoundActions.coordinator p.two_le_m then
          if CoordinatorRecordingOperation.isFrozen (operationInput z) then
            some (CoordinatorRecordingOperation.zeroOutput p)
          else if CoordinatorRecordingOperation.ownsArm (operationInput z).mode
              (recorderOwnArm z) then
            if CoordinatorRecordingOperation.ownMaskPasses (operationInput z) then
              if 0 < rawGateMass z then
                if threshold z ∈ Set.Icc (0 : ℝ) 1 then
                  if (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.thin
                      (rowSlice z)).val ≤ threshold z then
                    checkedArrival (recorderOwnArm z, floorArrival z)
                  else some (CoordinatorRecordingOperation.zeroOutput p)
                else none
              else none
            else some (CoordinatorRecordingOperation.zeroOutput p)
          else some (CoordinatorRecordingOperation.zeroOutput p)
        else some (CoordinatorRecordingOperation.zeroOutput p)
      else some (CoordinatorRecordingOperation.zeroOutput p)
    else none

/-- Exact whole-result comparison on every local input, including all rejected
and zero-arrival paths. The validity proof is constructed only inside the
accepted runtime branch. -/
theorem checkedRun_eq_run (z : RecorderCoordinates p rate) :
    checkedRun z = CoordinatorRecorderComplementBridge.run (recordingInput z) := by
  classical
  change checkedRun z = CoordinatorRecordingOperation.run (operationInput z)
  by_cases hv : CoordinatorRecordingOperation.InputsValid (operationInput z)
  · have hl := (CoordinatorRecorderComplementBridge.recorderInput_inputsValid_iff
      (recordingInput z)).mp hv
    rw [checkedRun, ite_eq_left hl, CoordinatorRecordingOperation.run, dite_eq_left hv]
    unfold CoordinatorRecordingOperation.executeValid
    simp only [rawGateMass_eq_actual z hv, floorArrival_eq_actual, checkedArrival]
    rfl
  · have hl : ¬ CoordinatorRecorderComplementBridge.LocalInputsValid (recordingInput z) :=
      fun h => hv ((CoordinatorRecorderComplementBridge.recorderInput_inputsValid_iff _).mpr h)
    rw [checkedRun, ite_eq_right hl, CoordinatorRecordingOperation.run, dite_eq_right hv]

theorem measurable_checkedRun :
    Measurable (checkedRun (p := p) (rate := rate)) := by
  classical
  have hdata := measurableSet_eq_fun
    (measurable_selectedSlot (p := p) (rate := rate))
    (measurable_const (a := PublicDiscreteDraws.dataSlot))
  have hsource := measurableSet_eq_fun
    (measurable_selectedRecorder (p := p) (rate := rate))
    (measurable_const (a := ActiveRoundActions.coordinator p.two_le_m))
  have hden := measurableSet_lt (measurable_const (a := (0 : ℝ)))
    (measurable_rawGateMass (p := p) (rate := rate))
  have hparameter := (measurableSet_Icc : MeasurableSet (Set.Icc (0 : ℝ) 1)).preimage
    (measurable_threshold (p := p) (rate := rate))
  have hthinValue : Measurable (fun z : RecorderCoordinates p rate =>
      (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.thin (rowSlice z)).val) :=
    measurable_subtype_coe.comp
      ((ContinuousControlSlice.measurable_coordinate _).comp measurable_rowSlice)
  have hthin := measurableSet_le hthinValue (measurable_threshold (p := p) (rate := rate))
  unfold checkedRun
  apply Measurable.ite measurable_recorderValidity ?_ measurable_const
  apply Measurable.ite hdata ?_ measurable_const
  apply Measurable.ite hsource ?_ measurable_const
  apply Measurable.ite measurableSet_isFrozen measurable_const
  apply Measurable.ite measurableSet_ownsArm ?_ measurable_const
  apply Measurable.ite measurableSet_ownMaskPasses ?_ measurable_const
  apply Measurable.ite hden ?_ measurable_const
  apply Measurable.ite hparameter ?_ measurable_const
  apply Measurable.ite hthin ?_ measurable_const
  exact (Measurable.of_discrete : Measurable (checkedArrival (p := p))).comp
    (measurable_recorderOwnArm.prodMk measurable_floorArrival)

/-- Joint measurability of the actual recorder, with no input-validity,
no-cutoff, true-score, no-overflow or successful-recording assumption. -/
theorem measurable_run : Measurable (fun z : RecorderCoordinates p rate =>
    CoordinatorRecorderComplementBridge.run (recordingInput z)) := by
  have heq : (fun z : RecorderCoordinates p rate =>
      CoordinatorRecorderComplementBridge.run (recordingInput z)) = checkedRun :=
    funext fun z => (checkedRun_eq_run z).symm
  rw [heq]
  exact measurable_checkedRun

/-- The existing lossless code of the WHOLE option, rather than a gate or
arrival projection. -/
def runCode (z : RecorderCoordinates p rate) :
    Option (CoordinatorRecordingMeasurability.OutputCode p) :=
  CoordinatorRecordingMeasurability.encodeResult
    (CoordinatorRecorderComplementBridge.run (recordingInput z))

theorem measurable_runCode : Measurable (runCode (p := p) (rate := rate)) :=
  (measurable_from_top : Measurable
    (CoordinatorRecordingMeasurability.encodeResult (p := p))).comp measurable_run

/-- Decoding recovers the same actual run at the same complete local input. -/
theorem decodeResult_runCode (z : RecorderCoordinates p rate) :
    CoordinatorRecordingMeasurability.decodeResult (runCode z) =
      CoordinatorRecorderComplementBridge.run (recordingInput z) :=
  CoordinatorRecordingMeasurability.decodeResult_encodeResult _

/-- Composition needs only separately measurable primitive local maps. In
particular, no recorder probability or recorder-measurability input is supplied. -/
theorem measurable_runCode_comp {α : Type*} [MeasurableSpace α]
    (payload : α → ReferenceActivePhysicalStep.Payload rate)
    (code : α → ReferenceActivePhysicalStepMeasurability.LiveDiscrete p)
    (started : α → CoordinatorPhaseClock.StartRoundResult p)
    (time : α → Fin p.T) (row : α → CompletePublicTable.CompleteRow p)
    (arm : α → Fin p.K) (observation : α → Fin (D p + 1))
    (hpayload : Measurable payload) (hcode : Measurable code)
    (hstarted : Measurable started) (htime : Measurable time) (hrow : Measurable row)
    (harm : Measurable arm) (hobs : Measurable observation) :
    Measurable (fun a => runCode
      (payload a, code a, started a, time a, row a, arm a, observation a)) :=
  measurable_runCode.comp (hpayload.prodMk (hcode.prodMk (hstarted.prodMk
    (htime.prodMk (hrow.prodMk (harm.prodMk hobs))))))

/-- Coordinates extracted at the ORIGINAL physical input and its prepared
observation. The original start result and whole row are retained literally. -/
def coordinatesOf {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ) (started : CoordinatorPhaseClock.StartRoundResult p) :
    RecorderCoordinates p rate :=
  (r.payload, ReferenceActivePhysicalStepMeasurability.encodeLive r owned base,
    started, x.time, x.row, prepared.coordinator.arm, prepared.coordinatorObservation)

/-- The accepted live-code decode preserves the actual score-derived weights.
Queues and base scores are retained in the code but never read by this call. -/
theorem complementWeights_decodeLive_encodeLive
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ) :
    (ReferenceActivePhysicalStepMeasurability.decodeLiveRegisters r.payload
      (ReferenceActivePhysicalStepMeasurability.encodeLive r owned base)).complementWeights =
      r.complementWeights := by
  exact funext fun (j : CanonicalFastSampling.FastArm r.payload.slowSet) =>
    congrArg (ScoreWeights.scoreWeight (AssignmentScoreReconstruction.sourceWeightBase p))
      (ReferenceActivePhysicalStepMeasurability.extendComplement_apply r.payload r.complementScores j)

/-- Pointwise equality to the exact canonical physical recorder input, without
changing the physical input, supplying a dummy state, or replacing any row. -/
theorem recordingInput_coordinatesOf {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ) (started : CoordinatorPhaseClock.StartRoundResult p) :
    recordingInput (coordinatesOf prepared r owned base started) =
      ReferenceActivePhysicalStep.liveRecordingInput prepared r started := by
  unfold recordingInput recorderRegisters coordinatesOf recorderPayload recorderLiveCode
  rw [complementWeights_decodeLive_encodeLive]
  rfl

/-- WHOLE decoded output equals the actual live call on the SAME original x.
No producer, service, confirmation or clock-transition conclusion is assumed. -/
theorem decodeResult_runCode_coordinatesOf {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ) (started : CoordinatorPhaseClock.StartRoundResult p) :
    CoordinatorRecordingMeasurability.decodeResult
        (runCode (coordinatesOf prepared r owned base started)) =
      CoordinatorRecorderComplementBridge.run
        (ReferenceActivePhysicalStep.liveRecordingInput prepared r started) := by
  rw [decodeResult_runCode, recordingInput_coordinatesOf]
  rfl

end Bandits.Support.ReferenceLiveRecorderJointMeasurability
