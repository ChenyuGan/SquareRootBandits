/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.CoordinatorRecordingOperation
public import Bandits.Support.CompletePublicTable
public import Bandits.Support.ContinuousLearningRows
public import Bandits.Support.ContinuousControlSlice
public import Bandits.Support.PublicDiscreteDraws
public import Bandits.Support.CanonicalRecordingSlice
public import Bandits.Support.CanonicalRecordingRates
public import Bandits.Support.RealRewardGridCount
public import Bandits.Support.ActiveRoundActions

import Mathlib.MeasureTheory.Function.Floor

/-!
# Measurability of the actual coordinator-local recorder

This module proves joint measurability of the existing
`CoordinatorRecordingOperation.run`, on one complete public row and the
coordinator's actual arm and typed grid observation. It retains the full
continuous row carrier. The only continuous coordinates read are the current
time slice's DATA slot, recorder source, other-player pilots, and own thinning
coordinate.

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:140-165`,
`sources/zip4/manuscript/05_binary_transport.tex:352-426`,
`sources/zip4/manuscript/06_interruptions.tex:257-269`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:8-14`.

This is a fixed-retained-data measurability result. It does not assert an
adaptive conditional recording law, physical provenance of arbitrary supplied
rows, or a complete active-run theorem.

The later countable decomposition can fix each actual integer score/queue
tuple and its derived weights as retained data, then apply this result on that
fiber. This module supplies the fiberwise measurability step; it does not prove
the decomposition's law or adaptation.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.CoordinatorRecordingMeasurability

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.CompletePublicTable
open Bandits.Support.ContinuousLearningRows
open Bandits.Support.ContinuousControlSlice
open Bandits.Support.PublicDiscreteDraws
open Bandits.Support.CanonicalRecordingSlice
open Bandits.Support.CanonicalRecordingRates
open Bandits.Support.ActiveRoundActions
open Bandits.Support.CoordinatorRecordingOperation
open Bandits.Support.RealRewardGridCount

abbrev Parameters := ConstructorDimensions.Parameters

/-- A finite code records both fields of the actual local output. -/
abbrev OutputCode (p : Parameters) :=
  Option (Fin p.K) × Fin (D p + 1)

/-- Encode the gate arm and the raw arrival without identifying gate failure
with a successful zero-floor observation. -/
def encodeOutput {p : Parameters} (output : Output p) : OutputCode p :=
  (output.gateArm, ⟨output.rawArrival, Nat.lt_succ_of_le output.rawArrival_le_D⟩)

/-- Reconstruct the exact gate arm and raw arrival from the finite code. -/
def decodeOutput {p : Parameters} (code : OutputCode p) : Output p :=
  ⟨code.1, code.2.val, Nat.le_of_lt_succ code.2.isLt⟩

theorem decodeOutput_encodeOutput {p : Parameters} (output : Output p) :
    decodeOutput (encodeOutput output) = output := by
  cases output
  rfl

theorem encodeOutput_decodeOutput {p : Parameters} (code : OutputCode p) :
    encodeOutput (decodeOutput code) = code := by
  rcases code with ⟨gate, arrival⟩
  apply Prod.ext
  · rfl
  · apply Fin.ext
    rfl

/-- The output carrier is equivalent to its proved finite code. -/
def outputCodeEquiv (p : Parameters) : Output p ≃ OutputCode p where
  toFun := encodeOutput
  invFun := decodeOutput
  left_inv := decodeOutput_encodeOutput
  right_inv := encodeOutput_decodeOutput

instance outputFintype (p : Parameters) : Fintype (Output p) :=
  Fintype.ofEquiv (OutputCode p) (outputCodeEquiv p).symm

/-- Encode the outer failure option separately from a successful output. -/
def encodeResult {p : Parameters} :
    Option (Output p) → Option (OutputCode p) :=
  Option.map encodeOutput

/-- Reconstruct failure or the exact successful output code. -/
def decodeResult {p : Parameters} :
    Option (OutputCode p) → Option (Output p) :=
  Option.map decodeOutput

theorem decodeResult_encodeResult {p : Parameters} (result : Option (Output p)) :
    decodeResult (encodeResult result) = result := by
  cases result with
  | none => rfl
  | some output => simp [encodeResult, decodeResult, decodeOutput_encodeOutput]

theorem encodeResult_decodeResult {p : Parameters} (code : Option (OutputCode p)) :
    encodeResult (decodeResult code) = code := by
  cases code with
  | none => rfl
  | some output => simp [encodeResult, decodeResult, encodeOutput_decodeOutput]

/-- The operation's output has the discrete measurable space justified by its
finite encoding above. -/
instance outputMeasurableSpace (p : Parameters) : MeasurableSpace (Output p) := ⊤

/-- Failure and successful outputs form a countable discrete result carrier. -/
instance resultMeasurableSpace (p : Parameters) :
    MeasurableSpace (Option (Output p)) := ⊤

/-- The actual joint input for one coordinator call: the complete row and the
coordinator's own arm and denominator-`D` grid observation. -/
abbrev RecorderDomain (p : Parameters) :=
  CompleteRow p × (Fin p.K × Fin (D p + 1))

/-- Literal adapter to the accepted operation input. The retained local data
come from `base`; only its complete row, own arm, and typed own observation
are replaced by the jointly varying values. -/
def inputAt {p : Parameters} (base : Input p) (value : RecorderDomain p) :
    Input p :=
  { base with row := value.1, ownArm := value.2.1, observation := value.2.2 }

theorem inputAt_row {p : Parameters} (base : Input p) (value : RecorderDomain p) :
    (inputAt base value).row = value.1 := rfl

theorem inputAt_ownArm {p : Parameters} (base : Input p) (value : RecorderDomain p) :
    (inputAt base value).ownArm = value.2.1 := rfl

theorem inputAt_observation {p : Parameters} (base : Input p) (value : RecorderDomain p) :
    (inputAt base value).observation = value.2.2 := rfl

theorem inputAt_fixedFields {p : Parameters} (base : Input p) (value : RecorderDomain p) :
    (inputAt base value).eta = base.eta ∧
    (inputAt base value).anchor = base.anchor ∧
    (inputAt base value).currentWeights = base.currentWeights ∧
    (inputAt base value).sigma = base.sigma ∧
    (inputAt base value).time = base.time ∧
    (inputAt base value).gridBoundary = base.gridBoundary ∧
    (inputAt base value).mode = base.mode := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Input validity is exactly the validity of the fixed retained numerical
data; it makes no assumption about the row, arm, or observation. -/
theorem inputAt_inputsValid_iff {p : Parameters} (base : Input p)
    (value : RecorderDomain p) :
    InputsValid (inputAt base value) ↔ InputsValid base := by
  constructor
  · intro hvalid
    exact ⟨hvalid.sigma_le_terminal, hvalid.boundary_le_terminal,
      hvalid.eta_pos, hvalid.eta_source_cap, hvalid.anchor_pos,
      hvalid.current_pos, hvalid.anchor_le_current,
      hvalid.current_le_twice_anchor⟩
  · intro hvalid
    exact ⟨hvalid.sigma_le_terminal, hvalid.boundary_le_terminal,
      hvalid.eta_pos, hvalid.eta_source_cap, hvalid.anchor_pos,
      hvalid.current_pos, hvalid.anchor_le_current,
      hvalid.current_le_twice_anchor⟩

theorem inputAt_inputsValid {p : Parameters} (base : Input p)
    (value : RecorderDomain p) (hvalid : InputsValid base) :
    InputsValid (inputAt base value) :=
  (inputAt_inputsValid_iff base value).2 hvalid

private def rowSlice {p : Parameters} (base : Input p) (value : RecorderDomain p) :
    Slice p :=
  sliceAt base.time value.1.2

private def armAt {p : Parameters} (_base : Input p) (value : RecorderDomain p) : Fin p.K :=
  value.2.1

private def observationAt {p : Parameters} (_base : Input p)
    (value : RecorderDomain p) : Fin (D p + 1) := value.2.2

private theorem measurable_rowSlice {p : Parameters} (base : Input p) :
    Measurable (rowSlice base : RecorderDomain p → Slice p) := by
  exact (ContinuousLearningRows.measurable_sliceAt base.time).comp
    (measurable_snd.comp measurable_fst)

/-- The actual operation call is measurable jointly in the complete row,
finite own arm, and finite grid observation. No validity or good-run input is
assumed: invalid retained numerical data take the accepted `run` failure path. -/
theorem measurable_run {p : Parameters} (base : Input p) :
    Measurable (fun value : RecorderDomain p => run (inputAt base value)) := by
  classical
  by_cases hvalidBase : InputsValid base
  · let hvalidAt : ∀ value : RecorderDomain p, InputsValid (inputAt base value) :=
      fun value => inputAt_inputsValid base value hvalidBase
    have hslot : Measurable (fun value : RecorderDomain p =>
        selectedSlot (inputAt base value)) := by
      change Measurable (fun value : RecorderDomain p =>
        slotDraw (rowSlice base value))
      exact (PublicDiscreteDraws.measurable_slotDraw (m := p.m) (K := p.K)).comp
        (measurable_rowSlice base)
    have hsource : Measurable (fun value : RecorderDomain p =>
        selectedRecorder (inputAt base value)) := by
      change Measurable (fun value : RecorderDomain p =>
        recorderSourceDraw p.two_le_m p.m_lt_K (rowSlice base value))
      exact (PublicDiscreteDraws.measurable_recorderSourceDraw
        p.two_le_m p.m_lt_K).comp (measurable_rowSlice base)
    have harm : Measurable (armAt base : RecorderDomain p → Fin p.K) :=
      measurable_fst.comp measurable_snd
    have hobs : Measurable (observationAt base : RecorderDomain p → Fin (D p + 1)) :=
      measurable_snd.comp measurable_snd
    have hdataSet : MeasurableSet {value : RecorderDomain p |
        selectedSlot (inputAt base value) = dataSlot} :=
      measurableSet_eq_fun hslot measurable_const
    have hsourceSet : MeasurableSet {value : RecorderDomain p |
        selectedRecorder (inputAt base value) = coordinator p.two_le_m} :=
      measurableSet_eq_fun hsource measurable_const
    have hfrozenSet : MeasurableSet {value : RecorderDomain p |
        isFrozen (inputAt base value)} := by
      have heq : {value : RecorderDomain p | isFrozen (inputAt base value)} =
          {value | isFrozen base} := by
        ext value
        rfl
      rw [heq]
      by_cases hfrozen : isFrozen base <;> simp [hfrozen]
    have hownsSet : MeasurableSet {value : RecorderDomain p |
        ownsArm (base.mode) (armAt base value)} := by
      rw [show {value : RecorderDomain p |
          ownsArm base.mode (armAt base value)} =
        ⋃ arm : Fin p.K, {value : RecorderDomain p |
          armAt base value = arm ∧ ownsArm base.mode arm} by
        ext value
        simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
        constructor
        · intro h
          exact ⟨armAt base value, rfl, h⟩
        · rintro ⟨arm, har, hown⟩
          simpa [har] using hown]
      refine MeasurableSet.iUnion fun arm => ?_
      have harmSet : MeasurableSet {value : RecorderDomain p |
          armAt base value = arm} := measurableSet_eq_fun harm measurable_const
      have hownSet : MeasurableSet {value : RecorderDomain p |
          ownsArm base.mode arm} := by
        by_cases hown : ownsArm base.mode arm <;> simp [hown]
      exact harmSet.inter hownSet
    have hmaskSet : MeasurableSet {value : RecorderDomain p |
        ownMaskPasses (inputAt base value)} := by
      rw [show {value : RecorderDomain p | ownMaskPasses (inputAt base value)} =
        ⋃ arm : Fin p.K, {value : RecorderDomain p |
          armAt base value = arm ∧
            recordingMask (K_pos p) (coordinator p.two_le_m) arm
              (rowSlice base value)} by
        ext value
        simp only [Set.mem_ofPred_eq, Set.mem_iUnion,
          CoordinatorRecordingOperation.ownMaskPasses, inputAt, rowSlice, armAt]
        constructor
        · intro h
          exact ⟨value.2.1, rfl, h⟩
        · rintro ⟨arm, har, hmask⟩
          simpa [har] using hmask]
      refine MeasurableSet.iUnion fun arm => ?_
      have harmSet : MeasurableSet {value : RecorderDomain p |
          armAt base value = arm} := measurableSet_eq_fun harm measurable_const
      have hrecordingMask : MeasurableSet {slice : Slice p |
          recordingMask (K_pos p) (coordinator p.two_le_m) arm slice} :=
        CanonicalRecordingSlice.measurableSet_recordingMask p.two_le_m
          (K_pos p) (coordinator p.two_le_m) arm
      exact harmSet.inter (hrecordingMask.preimage (measurable_rowSlice base))
    let armInput : Fin p.K → Input p := fun arm =>
      inputAt base (base.row, (arm, base.observation))
    have hvalidArm : ∀ arm, InputsValid (armInput arm) := by
      intro arm
      exact inputAt_inputsValid base _ hvalidBase
    let rawArm : Fin p.K → ℝ := fun arm =>
      coordinatorRawGateMass (armInput arm) (hvalidArm arm)
    have hrawArm : Measurable rawArm := Measurable.of_discrete
    have hprob : ∀ value : RecorderDomain p,
        coordinatorArmProbability (inputAt base value) (hvalidAt value) =
          coordinatorArmProbability (armInput (armAt base value))
            (hvalidArm (armAt base value)) := by
      intro value
      cases hmode : base.mode with
      | collection =>
          simp [CoordinatorRecordingOperation.coordinatorArmProbability,
            hmode, armInput, inputAt, armAt]
      | live assignment confirmationsEmpty =>
          cases confirmationsEmpty <;>
            simp [CoordinatorRecordingOperation.coordinatorArmProbability,
              hmode, armInput, inputAt, armAt]
    have hrawEq : ∀ value : RecorderDomain p,
        coordinatorRawGateMass (inputAt base value) (hvalidAt value) =
          rawArm (armAt base value) := by
      intro value
      change (1 / 2) * (1 / 2) *
          coordinatorArmProbability (inputAt base value) (hvalidAt value) *
            recordingZeta p.m p.K =
        (1 / 2) * (1 / 2) *
          coordinatorArmProbability (armInput (armAt base value))
            (hvalidArm (armAt base value)) * recordingZeta p.m p.K
      rw [hprob value]
    have hraw : Measurable (fun value : RecorderDomain p =>
        coordinatorRawGateMass (inputAt base value) (hvalidAt value)) := by
      have hrawEqFun : (fun value : RecorderDomain p =>
          coordinatorRawGateMass (inputAt base value) (hvalidAt value)) =
          rawArm ∘ armAt base := by
        funext value
        exact hrawEq value
      rw [hrawEqFun]
      exact hrawArm.comp harm
    let xiArm : Fin p.K → ℝ := fun arm => xi p base.eta base.anchor arm
    have hxiArm : Measurable xiArm := Measurable.of_discrete
    let thresholdArm : Fin p.K → ℝ := fun arm => xiArm arm / rawArm arm
    have hthresholdArm : Measurable thresholdArm := hxiArm.div hrawArm
    have hthreshold : Measurable (fun value : RecorderDomain p =>
        coordinatorThreshold (inputAt base value) (hvalidAt value)) := by
      have hthresholdEq : (fun value : RecorderDomain p =>
          coordinatorThreshold (inputAt base value) (hvalidAt value)) =
          thresholdArm ∘ armAt base := by
        funext value
        change xi p base.eta base.anchor (armAt base value) /
            coordinatorRawGateMass (inputAt base value) (hvalidAt value) =
          xi p base.eta base.anchor (armAt base value) /
            rawArm (armAt base value)
        rw [hrawEq value]
      rw [hthresholdEq]
      exact hthresholdArm.comp harm
    have hdenSet : MeasurableSet {value : RecorderDomain p |
        0 < coordinatorRawGateMass (inputAt base value) (hvalidAt value)} :=
      measurableSet_lt measurable_const hraw
    have hparameterSet : MeasurableSet {value : RecorderDomain p |
        coordinatorThreshold (inputAt base value) (hvalidAt value) ∈
          Set.Icc (0 : ℝ) 1} :=
      (measurableSet_Icc : MeasurableSet (Set.Icc (0 : ℝ) 1)).preimage hthreshold
    have hthin : Measurable (fun value : RecorderDomain p =>
        (coordinate Label.thin (rowSlice base value)).val) :=
      measurable_subtype_coe.comp
        ((ContinuousControlSlice.measurable_coordinate Label.thin).comp
          (measurable_rowSlice base))
    have hthinSet : MeasurableSet {value : RecorderDomain p |
        (coordinate Label.thin (rowSlice base value)).val ≤
          coordinatorThreshold (inputAt base value) (hvalidAt value)} :=
      measurableSet_le hthin hthreshold
    let floorArgument : Fin p.K × Fin (D p + 1) → ℝ := fun code =>
      (D p : ℝ) * base.eta * realRewardGridValue (D p) (D_pos p) code.2 /
        xi p base.eta base.anchor code.1
    have hfloorArgument : Measurable floorArgument := Measurable.of_discrete
    have hfloorInput : Measurable (fun value : RecorderDomain p =>
        (armAt base value, observationAt base value)) := harm.prodMk hobs
    have hfloor : Measurable (fun value : RecorderDomain p =>
        floorArrival (inputAt base value)) := by
      have hfloorFormula : (fun value : RecorderDomain p =>
          floorArrival (inputAt base value)) =
          fun value => Nat.floor (floorArgument
            (armAt base value, observationAt base value)) := by
        funext value
        simp [floorArgument, CoordinatorRecordingOperation.floorArrival,
          inputAt, armAt, observationAt]
      rw [hfloorFormula]
      exact Nat.measurable_floor.comp (hfloorArgument.comp hfloorInput)
    have hfloorSet : MeasurableSet {value : RecorderDomain p |
        floorArrival (inputAt base value) ≤ D p} :=
      measurableSet_le hfloor measurable_const
    let checkedOutput : Fin p.K × ℕ → Option (Output p) := fun code =>
      if houtput : code.2 ≤ D p then
        some ⟨some code.1, code.2, houtput⟩
      else none
    have hcheckedOutput : Measurable checkedOutput := Measurable.of_discrete
    have hchecked : Measurable (fun value : RecorderDomain p =>
        if houtput : floorArrival (inputAt base value) ≤ D p then
          some (⟨some (inputAt base value).ownArm,
            floorArrival (inputAt base value), houtput⟩ : Output p)
        else none) := by
      have hcheckedEq : (fun value : RecorderDomain p =>
          if houtput : floorArrival (inputAt base value) ≤ D p then
            some (⟨some (inputAt base value).ownArm,
              floorArrival (inputAt base value), houtput⟩ : Output p)
          else none) = checkedOutput ∘ (fun value =>
            (armAt base value, floorArrival (inputAt base value))) := by
        funext value
        change (if houtput : floorArrival (inputAt base value) ≤ D p then
          some (⟨some (inputAt base value).ownArm,
            floorArrival (inputAt base value), houtput⟩ : Output p)
        else none) =
          (if houtput : floorArrival (inputAt base value) ≤ D p then
            some (⟨some (inputAt base value).ownArm,
              floorArrival (inputAt base value), houtput⟩ : Output p)
          else none)
        rfl
      rw [hcheckedEq]
      exact hcheckedOutput.comp (harm.prodMk hfloor)
    let zeroResult : Option (Output p) := some (zeroOutput p)
    have hafterThin : Measurable (fun value : RecorderDomain p =>
        if (coordinate Label.thin (rowSlice base value)).val ≤
            coordinatorThreshold (inputAt base value) (hvalidAt value)
        then (if houtput : floorArrival (inputAt base value) ≤ D p then
          some ⟨some (inputAt base value).ownArm,
            floorArrival (inputAt base value), houtput⟩ else none)
        else zeroResult) :=
      Measurable.ite hthinSet hchecked measurable_const
    have hafterParameter : Measurable (fun value : RecorderDomain p =>
        if coordinatorThreshold (inputAt base value) (hvalidAt value) ∈
            Set.Icc (0 : ℝ) 1
        then (if (coordinate Label.thin (rowSlice base value)).val ≤
            coordinatorThreshold (inputAt base value) (hvalidAt value)
          then (if houtput : floorArrival (inputAt base value) ≤ D p then
            some ⟨some (inputAt base value).ownArm,
              floorArrival (inputAt base value), houtput⟩ else none)
          else zeroResult)
        else none) :=
      Measurable.ite hparameterSet hafterThin measurable_const
    have hafterDenominator : Measurable (fun value : RecorderDomain p =>
        if 0 < coordinatorRawGateMass (inputAt base value) (hvalidAt value)
        then (if coordinatorThreshold (inputAt base value) (hvalidAt value) ∈
            Set.Icc (0 : ℝ) 1
          then (if (coordinate Label.thin (rowSlice base value)).val ≤
              coordinatorThreshold (inputAt base value) (hvalidAt value)
            then (if houtput : floorArrival (inputAt base value) ≤ D p then
              some ⟨some (inputAt base value).ownArm,
                floorArrival (inputAt base value), houtput⟩ else none)
            else zeroResult)
          else none)
        else none) :=
      Measurable.ite hdenSet hafterParameter measurable_const
    have hafterMask : Measurable (fun value : RecorderDomain p =>
        if ownMaskPasses (inputAt base value)
        then (if 0 < coordinatorRawGateMass (inputAt base value) (hvalidAt value)
          then (if coordinatorThreshold (inputAt base value) (hvalidAt value) ∈
              Set.Icc (0 : ℝ) 1
            then (if (coordinate Label.thin (rowSlice base value)).val ≤
                coordinatorThreshold (inputAt base value) (hvalidAt value)
              then (if houtput : floorArrival (inputAt base value) ≤ D p then
                some ⟨some (inputAt base value).ownArm,
                  floorArrival (inputAt base value), houtput⟩ else none)
              else zeroResult)
            else none)
          else none)
        else zeroResult) :=
      Measurable.ite hmaskSet hafterDenominator measurable_const
    have hafterOwns : Measurable (fun value : RecorderDomain p =>
        if ownsArm base.mode (armAt base value)
        then (if ownMaskPasses (inputAt base value)
          then (if 0 < coordinatorRawGateMass (inputAt base value) (hvalidAt value)
            then (if coordinatorThreshold (inputAt base value) (hvalidAt value) ∈
                Set.Icc (0 : ℝ) 1
              then (if (coordinate Label.thin (rowSlice base value)).val ≤
                  coordinatorThreshold (inputAt base value) (hvalidAt value)
                then (if houtput : floorArrival (inputAt base value) ≤ D p then
                  some ⟨some (inputAt base value).ownArm,
                    floorArrival (inputAt base value), houtput⟩ else none)
                else zeroResult)
              else none)
            else none)
          else zeroResult)
        else zeroResult) :=
      Measurable.ite hownsSet hafterMask measurable_const
    have hafterFreeze : Measurable (fun value : RecorderDomain p =>
        if isFrozen (inputAt base value)
        then zeroResult
        else (if ownsArm base.mode (armAt base value)
          then (if ownMaskPasses (inputAt base value)
            then (if 0 < coordinatorRawGateMass (inputAt base value) (hvalidAt value)
              then (if coordinatorThreshold (inputAt base value) (hvalidAt value) ∈
                  Set.Icc (0 : ℝ) 1
                then (if (coordinate Label.thin (rowSlice base value)).val ≤
                    coordinatorThreshold (inputAt base value) (hvalidAt value)
                  then (if houtput : floorArrival (inputAt base value) ≤ D p then
                    some ⟨some (inputAt base value).ownArm,
                      floorArrival (inputAt base value), houtput⟩ else none)
                  else zeroResult)
                else none)
              else none)
            else zeroResult)
          else zeroResult)) :=
      Measurable.ite hfrozenSet measurable_const hafterOwns
    have hafterSource : Measurable (fun value : RecorderDomain p =>
        if selectedRecorder (inputAt base value) = coordinator p.two_le_m
        then (if isFrozen (inputAt base value)
          then zeroResult
          else (if ownsArm base.mode (armAt base value)
            then (if ownMaskPasses (inputAt base value)
              then (if 0 < coordinatorRawGateMass (inputAt base value) (hvalidAt value)
                then (if coordinatorThreshold (inputAt base value) (hvalidAt value) ∈
                    Set.Icc (0 : ℝ) 1
                  then (if (coordinate Label.thin (rowSlice base value)).val ≤
                      coordinatorThreshold (inputAt base value) (hvalidAt value)
                    then (if houtput : floorArrival (inputAt base value) ≤ D p then
                      some ⟨some (inputAt base value).ownArm,
                        floorArrival (inputAt base value), houtput⟩ else none)
                    else zeroResult)
                  else none)
                else none)
              else zeroResult)
            else zeroResult))
        else zeroResult) :=
      Measurable.ite hsourceSet hafterFreeze measurable_const
    have hafterData : Measurable (fun value : RecorderDomain p =>
        if selectedSlot (inputAt base value) = dataSlot
        then (if selectedRecorder (inputAt base value) = coordinator p.two_le_m
          then (if isFrozen (inputAt base value)
            then zeroResult
            else (if ownsArm base.mode (armAt base value)
              then (if ownMaskPasses (inputAt base value)
                then (if 0 < coordinatorRawGateMass (inputAt base value) (hvalidAt value)
                  then (if coordinatorThreshold (inputAt base value) (hvalidAt value) ∈
                      Set.Icc (0 : ℝ) 1
                    then (if (coordinate Label.thin (rowSlice base value)).val ≤
                        coordinatorThreshold (inputAt base value) (hvalidAt value)
                      then (if houtput : floorArrival (inputAt base value) ≤ D p then
                        some ⟨some (inputAt base value).ownArm,
                          floorArrival (inputAt base value), houtput⟩ else none)
                      else zeroResult)
                    else none)
                  else none)
                else zeroResult)
              else zeroResult))
          else zeroResult)
        else zeroResult) :=
      Measurable.ite hdataSet hafterSource measurable_const
    have hexecute : (fun value : RecorderDomain p =>
        executeValid (inputAt base value) (hvalidAt value)) =
        (fun value => if selectedSlot (inputAt base value) = dataSlot then
          if selectedRecorder (inputAt base value) = coordinator p.two_le_m then
            if isFrozen (inputAt base value) then zeroResult else
              if ownsArm base.mode (armAt base value) then
                if ownMaskPasses (inputAt base value) then
                  let raw := coordinatorRawGateMass (inputAt base value) (hvalidAt value)
                  if hden : 0 < raw then
                    let threshold := xi p (inputAt base value).eta
                      (inputAt base value).anchor (inputAt base value).ownArm / raw
                    if hparameter : threshold ∈ Set.Icc (0 : ℝ) 1 then
                      if hthin : (coordinate Label.thin
                          (rowSlice base value)).val ≤ threshold then
                        let arrival := floorArrival (inputAt base value)
                        if houtput : arrival ≤ D p then
                          some ⟨some (inputAt base value).ownArm, arrival, houtput⟩
                        else none
                      else zeroResult
                    else none
                  else none
                else zeroResult
              else zeroResult
          else zeroResult
        else zeroResult) := by
      funext value
      simp only [executeValid, zeroResult]
      rfl
    rw [show (fun value : RecorderDomain p => run (inputAt base value)) =
        (fun value => executeValid (inputAt base value) (hvalidAt value)) by
      funext value
      simp [run, hvalidAt]]
    rw [hexecute]
    exact hafterData
  · have hnone : (fun value : RecorderDomain p => run (inputAt base value)) =
        fun _ => (none : Option (Output p)) := by
      funext value
      apply run_none_of_invalid
      rw [inputAt_inputsValid_iff]
      exact hvalidBase
    rw [hnone]
    exact measurable_const

/-- The operation reads its complete row only through the current scalar
slice. Equality of that slice and the actual arm/grid observation determines
the result, even when forward bits, affine samples, and all other times vary. -/
theorem run_eq_of_current_slice_eq {p : Parameters} (base : Input p)
    (left right : RecorderDomain p)
    (hslice : sliceAt base.time left.1.2 = sliceAt base.time right.1.2)
    (harm : left.2.1 = right.2.1)
    (hobs : left.2.2 = right.2.2) :
    run (inputAt base left) = run (inputAt base right) := by
  classical
  let right' : RecorderDomain p := (right.1, (left.2.1, left.2.2))
  have hright : right = right' := by
    dsimp [right']
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · exact harm.symm
      · exact hobs.symm
  have hslice' : sliceAt base.time left.1.2 = sliceAt base.time right'.1.2 := by
    simpa [right'] using hslice
  have hresult : run (inputAt base left) = run (inputAt base right') := by
    by_cases hvalidBase : InputsValid base
    · have hvalidLeft := inputAt_inputsValid base left hvalidBase
      have hvalidRight := inputAt_inputsValid base right' hvalidBase
      have hslot : selectedSlot (inputAt base left) =
          selectedSlot (inputAt base right') := by
        simp only [selectedSlot, inputAt]
        rw [hslice']
      have hsource : selectedRecorder (inputAt base left) =
          selectedRecorder (inputAt base right') := by
        simp only [selectedRecorder, inputAt]
        rw [hslice']
      have hfrozen : isFrozen (inputAt base left) =
          isFrozen (inputAt base right') := rfl
      have hmask : ownMaskPasses (inputAt base left) =
          ownMaskPasses (inputAt base right') := by
        simp only [CoordinatorRecordingOperation.ownMaskPasses, inputAt]
        rw [hslice']
      have hthin :
          (coordinate Label.thin
            (sliceAt (inputAt base left).time (inputAt base left).row.2)).val =
          (coordinate Label.thin
            (sliceAt (inputAt base right').time (inputAt base right').row.2)).val := by
        change (coordinate Label.thin (sliceAt base.time left.1.2)).val =
          (coordinate Label.thin (sliceAt base.time right'.1.2)).val
        exact congrArg (fun slice => (coordinate Label.thin slice).val) hslice'
      have hownArm : (inputAt base left).ownArm =
          (inputAt base right').ownArm := rfl
      have hraw : coordinatorRawGateMass (inputAt base left) hvalidLeft =
          coordinatorRawGateMass (inputAt base right') hvalidRight := by
        have hprob : coordinatorArmProbability (inputAt base left) hvalidLeft =
            coordinatorArmProbability (inputAt base right') hvalidRight := by
          cases hmode : base.mode with
          | collection =>
              simp [CoordinatorRecordingOperation.coordinatorArmProbability,
                hmode, inputAt, right']
          | live assignment confirmationsEmpty =>
              cases confirmationsEmpty <;>
                simp [CoordinatorRecordingOperation.coordinatorArmProbability,
                  hmode, inputAt, right']
        change (1 / 2) * (1 / 2) *
            coordinatorArmProbability (inputAt base left) hvalidLeft *
              recordingZeta p.m p.K =
          (1 / 2) * (1 / 2) *
            coordinatorArmProbability (inputAt base right') hvalidRight *
              recordingZeta p.m p.K
        rw [hprob]
      have hfloor : floorArrival (inputAt base left) =
          floorArrival (inputAt base right') := by
        simp only [CoordinatorRecordingOperation.floorArrival, inputAt, right']
      have hrunLeft : run (inputAt base left) =
          executeValid (inputAt base left) hvalidLeft := by
        simp [run, hvalidLeft]
      have hrunRight : run (inputAt base right') =
          executeValid (inputAt base right') hvalidRight := by
        simp [run, hvalidRight]
      have howns' : ownsArm (inputAt base left).mode
          (inputAt base right').ownArm =
          ownsArm (inputAt base right').mode (inputAt base right').ownArm := rfl
      have hthreshold' :
          xi p (inputAt base left).eta (inputAt base left).anchor
              (inputAt base right').ownArm /
                coordinatorRawGateMass (inputAt base right') hvalidRight =
            xi p (inputAt base right').eta (inputAt base right').anchor
              (inputAt base right').ownArm /
                coordinatorRawGateMass (inputAt base right') hvalidRight := rfl
      rw [hrunLeft, hrunRight]
      simp only [CoordinatorRecordingOperation.executeValid, hslot, hsource,
        hfrozen, howns', hmask, hraw, hthreshold', hthin, hfloor, hownArm]
    · have hleft : ¬ InputsValid (inputAt base left) := by
        rw [inputAt_inputsValid_iff]
        exact hvalidBase
      have hright' : ¬ InputsValid (inputAt base right') := by
        rw [inputAt_inputsValid_iff]
        exact hvalidBase
      simp [run, hleft, hright']
  calc
    run (inputAt base left) = run (inputAt base right') := hresult
    _ = run (inputAt base right) := by rw [hright]

/-- The one-based manuscript source time is retained exactly by the adapter.
For `time : Fin T` it is at most `T`, so the initial boundary `T+1` is outside
the represented calendar. -/
theorem inputAt_sourceCalendarRound {p : Parameters} (base : Input p)
    (value : RecorderDomain p) :
    sourceCalendarRound (inputAt base value) = base.time.val + 1 := rfl

theorem inputAt_sourceCalendarRound_le_horizon {p : Parameters} (base : Input p)
    (value : RecorderDomain p) :
    sourceCalendarRound (inputAt base value) ≤ p.T :=
  sourceCalendarRound_le_horizon (inputAt base value)

theorem inputAt_sourceCalendarRound_ne_terminal {p : Parameters} (base : Input p)
    (value : RecorderDomain p) :
    sourceCalendarRound (inputAt base value) ≠ p.T + 1 :=
  sourceCalendarRound_ne_terminal (inputAt base value)

/-- The fixed complete-row operation lifted to a complete-row family at its
supplied coordinator row index. -/
theorem measurable_completeRows_run {p : Parameters} (base : Input p)
    (q : Fin (ConstructorDimensions.M p)) :
    Measurable (fun value : CompleteRows p × (Fin p.K × Fin (D p + 1)) =>
      run (inputAt base (value.1 q, value.2))) := by
  have hrow : Measurable (fun value : CompleteRows p ×
      (Fin p.K × Fin (D p + 1)) => value.1 q) :=
    (CompletePublicTable.measurable_completeRowProjection p q).comp measurable_fst
  have hdata : Measurable (fun value : CompleteRows p ×
      (Fin p.K × Fin (D p + 1)) => value.2) := measurable_snd
  exact (measurable_run base).comp (hrow.prodMk hdata)

/-- Complete-row families agreeing at the selected coordinator row give the
same actual operation result, regardless of every nonselected row. -/
theorem completeRows_run_eq_of_selected_row_eq {p : Parameters}
    (base : Input p) (rows rows' : CompleteRows p)
    (q : Fin (ConstructorDimensions.M p))
    (recordData : Fin p.K × Fin (D p + 1))
    (hrow : rows q = rows' q) :
    run (inputAt base (rows q, recordData)) =
      run (inputAt base (rows' q, recordData)) := by
  rw [hrow]

end Bandits.Support.CoordinatorRecordingMeasurability

end
