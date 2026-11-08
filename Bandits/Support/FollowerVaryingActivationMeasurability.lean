/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.FollowerPrepareJointMeasurability
public import Bandits.Support.FollowerObservationStageMeasurabilityRepair
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Prod

/-!
# Follower prepare and observation with varying activation

The local prepare and observation operations are assembled over the genuine
countable activation label and its dependent active-calendar-time subtype.
Incoming carry and proposal memory use the accepted lossless representations;
the complete row, saved buffer scalars, feedback grid index, and played arm
retain their existing measurable structures. The only time condition is the
source active-time validity predicate.

These are local input-composition results. They make no physical-history,
source-law, full-policy, or manuscript-closure claim.

Sources: `sources/zip4/manuscript/06_interruptions.tex:235-275`,
`sources/zip4/manuscript/05_binary_transport.tex:74-124`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:6-14`.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.FollowerVaryingActivationMeasurability

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.CompletePublicTable
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.ActiveFollowerDownAcceptance
open Bandits.Support.FollowerDownMeasurability
open Bandits.Support.FollowerLifecycleMeasurability
open Bandits.Support.FollowerPrepareJointMeasurability
open Bandits.Support.FollowerObservationStageMeasurabilityRepair
open Bandits.Support.DeclaredFollowerLocalRound

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ActiveFollowerDownAcceptance.RateInput
abbrev CarriedState (p : Parameters) (rate : RateInput p) :=
  FollowerObservationStageMeasurabilityRepair.CarriedState p rate
abbrev ActiveCalendarTime (p : Parameters) (activation : Activation p) :=
  FollowerLifecycleMeasurability.ActiveCalendarTime p activation

instance observationInputFiberMeasurableSpace {p : Parameters} {rate : RateInput p}
    (activation : Activation p)
    (index : FollowerObservationStageMeasurabilityRepair.FollowerCarryIndex p rate) :
    MeasurableSpace (ObservationFiber p rate activation index) := by
  unfold ObservationFiber ActiveTime FollowerLoggingDownMeasurability.ActiveTime
  infer_instance

instance observationInputMeasurableSpace {p : Parameters} (rate : RateInput p)
    (activation : Activation p) : MeasurableSpace (ObservationInput p rate activation) := by
  letI : ∀ index : FollowerObservationStageMeasurabilityRepair.FollowerCarryIndex p rate,
      MeasurableSpace (ObservationFiber p rate activation index) := fun _ => inferInstance
  exact Sigma.instMeasurableSpace

/-- The measurable disjoint union of the accepted prepare fibers over every
genuine activation label. -/
abbrev VaryingPrepareInput (p : Parameters) (rate : RateInput p) :=
  Sigma fun activation : Activation p => PrepareInput p rate activation

/-- The measurable disjoint union of the accepted observation fibers over
every genuine activation label. -/
abbrev VaryingObservationInput (p : Parameters) (rate : RateInput p) :=
  Sigma fun activation : Activation p => ObservationInput p rate activation

/-- Full prepared output on the same dependent activation carrier. -/
abbrev VaryingPreparedOutput (p : Parameters) (rate : RateInput p) :=
  Sigma fun activation : Activation p => PrepareOutput p rate activation

/-- Prepared round-code output on the same dependent activation carrier. -/
abbrev VaryingPreparedRoundCode (p : Parameters) (rate : RateInput p) :=
  Sigma fun _activation : Activation p => PreparedRoundCode p rate

/-- Observation result-code output on the same dependent activation carrier. -/
abbrev VaryingObservationResultCode (p : Parameters) (rate : RateInput p) :=
  Sigma fun _activation : Activation p => ObservationResultCode p rate

private theorem measurable_sigmaMk {α : Type*} {β : α → Type*}
    [∀ a, MeasurableSpace (β a)] (a : α) :
    Measurable (Sigma.mk a : β a → Sigma β) := by
  rw [measurable_iff_le_map]
  change (⨅ i, (inferInstance : MeasurableSpace (β i)).map (Sigma.mk i)) ≤ _
  exact iInf_le _ a

private theorem measurable_of_sigma_sections {α : Type*} {β : α → Type*}
    [∀ a, MeasurableSpace (β a)] {γ : Type*} [MeasurableSpace γ]
    (f : Sigma β → γ)
    (hf : ∀ a, Measurable (fun x : β a => f ⟨a, x⟩)) : Measurable f := by
  intro s hs
  change MeasurableSet[
    (⨅ a, (inferInstance : MeasurableSpace (β a)).map (Sigma.mk a))]
    {x | f x ∈ s}
  rw [MeasurableSpace.measurableSet_iInf]
  intro a
  rw [MeasurableSpace.map_def]
  exact hf a hs

private abbrev ActivationFiber {p : Parameters} {Ω : Type*}
    (activation : Ω → Activation p) (label : Activation p) :=
  {ω : Ω // activation ω = label}

/-- Restrict the separately supplied calendar index to the genuine active-time
subtype on one activation fiber. -/
private def activeCalendarTimeOnFiber {p : Parameters} {Ω : Type*}
    (activation : Ω → Activation p) (calendarIndex : Ω → Fin p.T)
    (valid : ∀ ω, (activation ω).val ≤ (calendarIndex ω).val + 1)
    (label : Activation p) (ω : ActivationFiber activation label) :
    ActiveCalendarTime p label :=
  ⟨calendarIndex ω.1, by simpa only [ω.2] using valid ω.1⟩

private theorem measurable_activeCalendarTimeOnFiber {p : Parameters}
    {Ω : Type*} [MeasurableSpace Ω]
    (activation : Ω → Activation p) (calendarIndex : Ω → Fin p.T)
    (valid : ∀ ω, (activation ω).val ≤ (calendarIndex ω).val + 1)
    (label : Activation p) (hcalendar : Measurable calendarIndex) :
    Measurable (activeCalendarTimeOnFiber activation calendarIndex valid label) :=
  (hcalendar.comp (measurable_subtype_coe : Measurable
    (fun ω : ActivationFiber activation label => (ω.1 : Ω)))).subtype_mk

/-- A measurable map into a dependent Sigma carrier, assembled from a
measurable countable label and maps measurable on each label fiber. The target
Sigma structure is its standard dependent-union structure. -/
private theorem measurable_activationDependentAssembly
    {α : Type*} [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
    {β : α → Type*} [∀ a, MeasurableSpace (β a)]
    {Ω : Type*} [MeasurableSpace Ω]
    (label : Ω → α) (hlabel : Measurable label)
    (fiber : ∀ a, {ω : Ω // label ω = a} → β a)
    (hfiber : ∀ a, Measurable (fiber a)) :
    Measurable (fun ω => (⟨label ω, fiber (label ω) ⟨ω, rfl⟩⟩ : Sigma β)) := by
  intro s hs
  have hdecomp :
      (fun ω => (⟨label ω, fiber (label ω) ⟨ω, rfl⟩⟩ : Sigma β)) ⁻¹' s =
        ⋃ a, (Subtype.val : {ω : Ω // label ω = a} → Ω) ''
          {x | fiber a x ∈ (Sigma.mk a) ⁻¹' s} := by
    ext ω
    constructor
    · intro hω
      refine Set.mem_iUnion.mpr ⟨label ω, ?_⟩
      refine (Set.mem_image Subtype.val _ ω).mpr ⟨⟨ω, rfl⟩, ?_, rfl⟩
      simpa using hω
    · intro hω
      obtain ⟨a, hω⟩ := Set.mem_iUnion.mp hω
      obtain ⟨x, hx, hxω⟩ := (Set.mem_image Subtype.val _ ω).mp hω
      have hlabelω : label ω = a := by
        rw [← hxω]
        exact x.2
      subst a
      have hx' : x = ⟨ω, rfl⟩ := Subtype.ext hxω
      subst x
      simpa using hx
  rw [hdecomp]
  exact MeasurableSet.iUnion fun a => by
    have hbase : MeasurableSet {ω : Ω | label ω = a} :=
      (measurableSet_singleton a).preimage hlabel
    have hsection : MeasurableSet ((Sigma.mk a) ⁻¹' s) :=
      (measurable_sigmaMk a) hs
    exact hbase.subtype_image (hfiber a hsection)

/-- Assemble a fixed-activation prepare input while retaining its original
active-calendar-time subtype. -/
def assembleVaryingPrepareInput {p : Parameters} {rate : RateInput p}
    (activation : Activation p) (incoming : IncomingConfiguration p rate)
    (row : CompleteRow p) (calendarIndex : Fin p.T)
    (hvalid : activation.val ≤ calendarIndex.val + 1) :
    VaryingPrepareInput p rate :=
  ⟨activation, assemblePrepareInput incoming row ⟨calendarIndex, hvalid⟩⟩

/-- Assemble a fixed-activation observation input with the original lossless
carried state, full row, valid active time, grid feedback index, and played arm. -/
def assembleVaryingObservationInput {p : Parameters} {rate : RateInput p}
    (activation : Activation p) (carry : CarriedState p rate)
    (row : CompleteRow p) (calendarIndex : Fin p.T)
    (hvalid : activation.val ≤ calendarIndex.val + 1)
    (feedback : Fin (D p + 1)) (arm : Fin p.K) :
    VaryingObservationInput p rate :=
  ⟨activation, assembleObservationInput carry row ⟨calendarIndex, hvalid⟩ feedback arm⟩

theorem assembleVaryingPrepareInput_fixedFiber {p : Parameters} {rate : RateInput p}
    (activation : Activation p) (incoming : IncomingConfiguration p rate)
    (row : CompleteRow p) (calendarIndex : Fin p.T)
    (hvalid : activation.val ≤ calendarIndex.val + 1) :
    assembleVaryingPrepareInput activation incoming row calendarIndex hvalid =
      ⟨activation, assemblePrepareInput incoming row ⟨calendarIndex, hvalid⟩⟩ := rfl

theorem assembleVaryingObservationInput_fixedFiber {p : Parameters}
    {rate : RateInput p} (activation : Activation p) (carry : CarriedState p rate)
    (row : CompleteRow p) (calendarIndex : Fin p.T)
    (hvalid : activation.val ≤ calendarIndex.val + 1)
    (feedback : Fin (D p + 1)) (arm : Fin p.K) :
    assembleVaryingObservationInput activation carry row calendarIndex hvalid feedback arm =
      ⟨activation,
        assembleObservationInput carry row ⟨calendarIndex, hvalid⟩ feedback arm⟩ := rfl

/-- Measurability of prepare-input assembly from the separate activation,
lossless incoming carry/memory, full row, and calendar index maps. The sole
non-measurability premise is the source active-time validity predicate needed
to form the dependent subtype. -/
theorem measurable_assembleVaryingPrepareInput {p : Parameters}
    {Ω : Type*} [MeasurableSpace Ω] (rate : RateInput p)
    (activation : Ω → Activation p)
    (incoming : Ω → IncomingConfiguration p rate)
    (row : Ω → CompleteRow p) (calendarIndex : Ω → Fin p.T)
    (hactivation : Measurable activation) (hincoming : Measurable incoming)
    (hrow : Measurable row) (hcalendar : Measurable calendarIndex)
    (hvalid : ∀ ω, (activation ω).val ≤ (calendarIndex ω).val + 1) :
    Measurable (fun ω => assembleVaryingPrepareInput (activation ω)
      (incoming ω) (row ω) (calendarIndex ω) (hvalid ω)) := by
  let fiber : ∀ a : Activation p, ActivationFiber activation a →
      PrepareInput p rate a := fun a ω =>
    assemblePrepareInput (incoming ω.1) (row ω.1)
      (activeCalendarTimeOnFiber activation calendarIndex hvalid a ω)
  have hfiber (a : Activation p) : Measurable (fiber a) := by
    have hcoe : Measurable (fun ω : ActivationFiber activation a => (ω.1 : Ω)) :=
      measurable_subtype_coe
    have hincomingFiber : Measurable
        (fun ω : ActivationFiber activation a => incoming ω.1) := by
      change Measurable (incoming ∘ fun ω : ActivationFiber activation a => (ω.1 : Ω))
      exact hincoming.comp hcoe
    have hrowFiber : Measurable
        (fun ω : ActivationFiber activation a => row ω.1) := by
      change Measurable (row ∘ fun ω : ActivationFiber activation a => (ω.1 : Ω))
      exact hrow.comp hcoe
    exact measurable_assemblePrepareInput a
      (fun ω => incoming ω.1) (fun ω => row ω.1)
      (activeCalendarTimeOnFiber activation calendarIndex hvalid a)
      hincomingFiber
      hrowFiber
      (measurable_activeCalendarTimeOnFiber activation calendarIndex hvalid a hcalendar)
  have hassembled := measurable_activationDependentAssembly activation hactivation fiber hfiber
  simpa [assembleVaryingPrepareInput, fiber, activeCalendarTimeOnFiber] using hassembled

/-- Measurability of observation-input assembly from the separate activation,
lossless carried state, complete row, calendar index, denominator-D feedback
index, and played-arm maps. The only validity premise types the active time. -/
theorem measurable_assembleVaryingObservationInput {p : Parameters}
    {Ω : Type*} [MeasurableSpace Ω] (rate : RateInput p)
    (activation : Ω → Activation p)
    (carry : Ω → CarriedState p rate) (row : Ω → CompleteRow p)
    (calendarIndex : Ω → Fin p.T) (feedback : Ω → Fin (D p + 1))
    (arm : Ω → Fin p.K)
    (hactivation : Measurable activation) (hcarry : Measurable carry)
    (hrow : Measurable row) (hcalendar : Measurable calendarIndex)
    (hfeedback : Measurable feedback) (harm : Measurable arm)
    (hvalid : ∀ ω, (activation ω).val ≤ (calendarIndex ω).val + 1) :
    Measurable (fun ω => assembleVaryingObservationInput (activation ω)
      (carry ω) (row ω) (calendarIndex ω) (hvalid ω) (feedback ω) (arm ω)) := by
  let fiber : ∀ a : Activation p, ActivationFiber activation a →
      ObservationInput p rate a := fun a ω =>
    assembleObservationInput (carry ω.1) (row ω.1)
      (activeCalendarTimeOnFiber activation calendarIndex hvalid a ω)
      (feedback ω.1) (arm ω.1)
  have hfiber (a : Activation p) : Measurable (fiber a) := by
    have hcoe : Measurable (fun ω : ActivationFiber activation a => (ω.1 : Ω)) :=
      measurable_subtype_coe
    have hcarryFiber : Measurable
        (fun ω : ActivationFiber activation a => carry ω.1) := by
      change Measurable (carry ∘ fun ω : ActivationFiber activation a => (ω.1 : Ω))
      exact hcarry.comp hcoe
    have hrowFiber : Measurable
        (fun ω : ActivationFiber activation a => row ω.1) := by
      change Measurable (row ∘ fun ω : ActivationFiber activation a => (ω.1 : Ω))
      exact hrow.comp hcoe
    have hfeedbackFiber : Measurable
        (fun ω : ActivationFiber activation a => feedback ω.1) := by
      change Measurable (feedback ∘ fun ω : ActivationFiber activation a => (ω.1 : Ω))
      exact hfeedback.comp hcoe
    have harmFiber : Measurable
        (fun ω : ActivationFiber activation a => arm ω.1) := by
      change Measurable (arm ∘ fun ω : ActivationFiber activation a => (ω.1 : Ω))
      exact harm.comp hcoe
    exact measurable_assembleObservationInput
      (fun ω => carry ω.1) (fun ω => row ω.1)
      (activeCalendarTimeOnFiber activation calendarIndex hvalid a)
      (fun ω => feedback ω.1) (fun ω => arm ω.1)
      hcarryFiber
      hrowFiber
      (measurable_activeCalendarTimeOnFiber activation calendarIndex hvalid a hcalendar)
      hfeedbackFiber
      harmFiber
  have hassembled := measurable_activationDependentAssembly activation hactivation fiber hfiber
  simpa [assembleVaryingObservationInput, fiber, activeCalendarTimeOnFiber] using hassembled

/-- The fixed-activation prepare operation over the dependent input carrier.
Its code retains the checked error and absorbing-dagger branches. -/
def varyingPrepareRoundCode {p : Parameters} (rate : RateInput p)
    (i : Fin (p.m - 1)) (x : VaryingPrepareInput p rate) :
    VaryingPreparedRoundCode p rate :=
  ⟨x.1, prepareRoundCodeOnInput rate i (activation := x.1) x.2⟩

/-- Full lossless prepared output over the varying activation carrier. -/
def varyingPreparedOutput {p : Parameters} (rate : RateInput p)
    (i : Fin (p.m - 1)) (x : VaryingPrepareInput p rate) :
    VaryingPreparedOutput p rate :=
  ⟨x.1, prepareOutputOnInput rate i x.1 x.2⟩

/-- The prepared arm projection, with activation forgotten only after the
dependent input has been assembled. -/
def varyingPreparedArm {p : Parameters} {rate : RateInput p}
    (i : Fin (p.m - 1)) (x : VaryingPrepareInput p rate) : Fin p.K :=
  (prepareOutputOnInput rate i x.1 x.2).2.1

/-- The next losslessly carried ordinary/dagger configuration projection. -/
def varyingPreparedConfiguration {p : Parameters} {rate : RateInput p}
    (i : Fin (p.m - 1)) (x : VaryingPrepareInput p rate) :
    IncomingConfiguration p rate :=
  (prepareOutputOnInput rate i x.1 x.2).2.2

/-- The observation code map, retaining the unoccupied logging/DOWN and
occupied service branches and all of their checked outcomes. -/
def varyingObservationResultCodeValue {p : Parameters} (rate : RateInput p)
    (i : Fin (p.m - 1)) (x : VaryingObservationInput p rate) :
    ObservationResultCode p rate :=
  observationResultCode rate i x.1 x.2

/-- Observation result code with its activation label retained in the
dependent-union output. -/
def varyingObservationResultCode {p : Parameters} (rate : RateInput p)
    (i : Fin (p.m - 1)) (x : VaryingObservationInput p rate) :
    VaryingObservationResultCode p rate :=
  ⟨x.1, varyingObservationResultCodeValue rate i x⟩

theorem measurable_varyingPrepareRoundCode {p : Parameters}
    (rate : RateInput p) (i : Fin (p.m - 1)) :
    Measurable (varyingPrepareRoundCode rate i) := by
  apply measurable_of_sigma_sections
  intro activation
  exact (measurable_sigmaMk activation).comp
    (measurable_prepareRoundCode rate i activation)

theorem measurable_varyingPreparedOutput {p : Parameters}
    (rate : RateInput p) (i : Fin (p.m - 1)) :
    Measurable (varyingPreparedOutput rate i) := by
  apply measurable_of_sigma_sections
  intro activation
  exact (measurable_sigmaMk activation).comp
    (measurable_prepareOutput rate i activation)

theorem measurable_varyingPreparedArm {p : Parameters} {rate : RateInput p}
    (i : Fin (p.m - 1)) : Measurable (varyingPreparedArm (rate := rate) i) := by
  apply measurable_of_sigma_sections
  intro activation
  exact ((measurable_fst.comp measurable_snd).comp
    (measurable_prepareOutput rate i activation))

theorem measurable_varyingPreparedConfiguration {p : Parameters}
    {rate : RateInput p} (i : Fin (p.m - 1)) :
    Measurable (varyingPreparedConfiguration (rate := rate) i) := by
  apply measurable_of_sigma_sections
  intro activation
  exact ((measurable_snd.comp measurable_snd).comp
    (measurable_prepareOutput rate i activation))

theorem measurable_varyingObservationResultCodeValue {p : Parameters}
    (rate : RateInput p) (i : Fin (p.m - 1)) :
    Measurable (varyingObservationResultCodeValue rate i) := by
  apply measurable_of_sigma_sections
  intro activation
  exact measurable_observationResultCode rate i activation

theorem measurable_varyingObservationResultCode {p : Parameters}
    (rate : RateInput p) (i : Fin (p.m - 1)) :
    Measurable (varyingObservationResultCode rate i) := by
  apply measurable_of_sigma_sections
  intro activation
  exact (measurable_sigmaMk activation).comp
    (measurable_observationResultCode rate i activation)

/-- The fixed-activation input fiber is the canonical measurable Sigma
injection and does not alter any row, time, state, memory, or scalar value. -/
def fixedPrepareInputFiber {p : Parameters} {rate : RateInput p}
    (activation : Activation p) : PrepareInput p rate activation →
      VaryingPrepareInput p rate := Sigma.mk activation

theorem measurable_fixedPrepareInputFiber {p : Parameters} {rate : RateInput p}
    (activation : Activation p) : Measurable (fixedPrepareInputFiber (rate := rate) activation) :=
  measurable_sigmaMk activation

/-- The fixed-activation observation fiber is the canonical measurable Sigma
injection and preserves the original continuous saved-scalar family. -/
def fixedObservationInputFiber {p : Parameters} {rate : RateInput p}
    (activation : Activation p) : ObservationInput p rate activation →
      VaryingObservationInput p rate := Sigma.mk activation

theorem measurable_fixedObservationInputFiber {p : Parameters} {rate : RateInput p}
    (activation : Activation p) :
    Measurable (fixedObservationInputFiber (rate := rate) activation) :=
  measurable_sigmaMk activation

theorem varyingPreparedOutput_fixedFiber {p : Parameters} (rate : RateInput p)
    (i : Fin (p.m - 1)) (activation : Activation p)
    (x : PrepareInput p rate activation) :
    varyingPreparedOutput rate i (fixedPrepareInputFiber activation x) =
      ⟨activation, prepareOutputOnInput rate i activation x⟩ := rfl

theorem varyingPrepareRoundCode_fixedFiber {p : Parameters} (rate : RateInput p)
    (i : Fin (p.m - 1)) (activation : Activation p)
    (x : PrepareInput p rate activation) :
    varyingPrepareRoundCode rate i (fixedPrepareInputFiber activation x) =
      ⟨activation, prepareRoundCodeOnInput rate i (activation := activation) x⟩ := rfl

theorem varyingPreparedArm_fixedFiber {p : Parameters} {rate : RateInput p}
    (i : Fin (p.m - 1)) (activation : Activation p)
    (x : PrepareInput p rate activation) :
    varyingPreparedArm (rate := rate) i (fixedPrepareInputFiber activation x) =
      (prepareOutputOnInput rate i activation x).2.1 := rfl

theorem varyingPreparedConfiguration_fixedFiber {p : Parameters}
    {rate : RateInput p} (i : Fin (p.m - 1)) (activation : Activation p)
    (x : PrepareInput p rate activation) :
    varyingPreparedConfiguration (rate := rate) i (fixedPrepareInputFiber activation x) =
      (prepareOutputOnInput rate i activation x).2.2 := rfl

theorem varyingObservationResultCodeValue_fixedFiber {p : Parameters}
    (rate : RateInput p) (i : Fin (p.m - 1)) (activation : Activation p)
    (x : ObservationInput p rate activation) :
    varyingObservationResultCodeValue rate i (fixedObservationInputFiber activation x) =
      observationResultCode rate i activation x := rfl

theorem varyingObservationResultCode_fixedFiber {p : Parameters}
    (rate : RateInput p) (i : Fin (p.m - 1)) (activation : Activation p)
    (x : ObservationInput p rate activation) :
    varyingObservationResultCode rate i (fixedObservationInputFiber activation x) =
      ⟨activation, observationResultCode rate i activation x⟩ := rfl

/-- Decoding the varying prepared output is exactly the existing declared
`prepare` operation on the original row, valid active time, and reconstructed
incoming configuration. -/
theorem varyingPreparedRound_reconstructs_prepare {p : Parameters}
    (rate : RateInput p) (i : Fin (p.m - 1))
    (x : VaryingPrepareInput p rate) :
    preparedRoundOfOutput rate i x.1
      (prepareOutputOnInput rate i x.1 x.2) =
      DeclaredFollowerLocalRound.prepare rate i (prepareInputRow x.2) x.1
        (prepareInputTime x.2).1 (prepareInputTime x.2).2
        (prepareInputConfiguration rate x.2) :=
  preparedRoundOfOutput_prepare rate i x.1 x.2

/-- On a separately assembled fixed-activation input, the full output
reconstructs the declared operation on the exact lossless incoming
configuration. -/
theorem assembledPrepare_reconstructs_prepare {p : Parameters}
    (rate : RateInput p) (i : Fin (p.m - 1))
    (activation : Activation p) (incoming : IncomingConfiguration p rate)
    (row : CompleteRow p) (calendarIndex : Fin p.T)
    (hvalid : activation.val ≤ calendarIndex.val + 1) :
    preparedRoundOfOutput rate i activation
      (prepareOutputOnInput rate i activation
        (assemblePrepareInput incoming row ⟨calendarIndex, hvalid⟩)) =
      DeclaredFollowerLocalRound.prepare rate i row activation calendarIndex hvalid
        (localConfigurationOfIncoming rate incoming) := by
  rw [preparedRoundOfOutput_prepare]
  cases incoming with
  | none => rfl
  | some data => rcases data with ⟨state, memory⟩; rfl

/-- The observation result-code decoder reconstructs the exact existing local
`recordOrServiceThenDown` operation, including all failure, rejection, and
acceptance distinctions and every carried scalar coordinate. -/
theorem varyingObservationResultCode_reconstructs_recordOrServiceThenDown
    {p : Parameters} (rate : RateInput p) (i : Fin (p.m - 1))
    (x : VaryingObservationInput p rate) :
    decodeObservationResultCode rate i x.1 x.2
        (varyingObservationResultCode rate i x).2 =
      DeclaredFollowerLocalRound.recordOrServiceThenDown rate i
        (fiberRow x.2.2) x.1 (fiberTime x.2.2).1 (fiberTime x.2.2).2
        (fiberPlayedArm x.2.2)
        (FollowerDownMeasurability.feedbackAtGrid p (fiberFeedbackIndex x.2.2))
        (reconstructCarriedState x.2.1 (fiberValues x.2.2)) :=
  decode_observationResultCode_eq_actual rate i x.1 x.2

/-- Separate measurable input maps suffice to make the varying prepared code
measurable; no assembled-output premise is supplied. -/
theorem measurable_varyingPrepareRoundCode_atComponents {p : Parameters}
    {Ω : Type*} [MeasurableSpace Ω] (rate : RateInput p)
    (i : Fin (p.m - 1)) (activation : Ω → Activation p)
    (incoming : Ω → IncomingConfiguration p rate)
    (row : Ω → CompleteRow p) (calendarIndex : Ω → Fin p.T)
    (hactivation : Measurable activation) (hincoming : Measurable incoming)
    (hrow : Measurable row) (hcalendar : Measurable calendarIndex)
    (hvalid : ∀ ω, (activation ω).val ≤ (calendarIndex ω).val + 1) :
    Measurable (fun ω => varyingPrepareRoundCode rate i
      (assembleVaryingPrepareInput (activation ω) (incoming ω) (row ω)
        (calendarIndex ω) (hvalid ω))) :=
  (measurable_varyingPrepareRoundCode rate i).comp
    (measurable_assembleVaryingPrepareInput rate activation incoming row calendarIndex
      hactivation hincoming hrow hcalendar hvalid)

/-- Separate measurable input maps suffice to make the full varying prepared
output measurable, retaining row, active time, arm, and next carry. -/
theorem measurable_varyingPreparedOutput_atComponents {p : Parameters}
    {Ω : Type*} [MeasurableSpace Ω] (rate : RateInput p)
    (i : Fin (p.m - 1)) (activation : Ω → Activation p)
    (incoming : Ω → IncomingConfiguration p rate)
    (row : Ω → CompleteRow p) (calendarIndex : Ω → Fin p.T)
    (hactivation : Measurable activation) (hincoming : Measurable incoming)
    (hrow : Measurable row) (hcalendar : Measurable calendarIndex)
    (hvalid : ∀ ω, (activation ω).val ≤ (calendarIndex ω).val + 1) :
    Measurable (fun ω => varyingPreparedOutput rate i
      (assembleVaryingPrepareInput (activation ω) (incoming ω) (row ω)
        (calendarIndex ω) (hvalid ω))) :=
  (measurable_varyingPreparedOutput rate i).comp
    (measurable_assembleVaryingPrepareInput rate activation incoming row calendarIndex
      hactivation hincoming hrow hcalendar hvalid)

/-- Separate measurable input maps suffice for the prepared-arm projection. -/
theorem measurable_varyingPreparedArm_atComponents {p : Parameters}
    {Ω : Type*} [MeasurableSpace Ω] (rate : RateInput p)
    (i : Fin (p.m - 1)) (activation : Ω → Activation p)
    (incoming : Ω → IncomingConfiguration p rate)
    (row : Ω → CompleteRow p) (calendarIndex : Ω → Fin p.T)
    (hactivation : Measurable activation) (hincoming : Measurable incoming)
    (hrow : Measurable row) (hcalendar : Measurable calendarIndex)
    (hvalid : ∀ ω, (activation ω).val ≤ (calendarIndex ω).val + 1) :
    Measurable (fun ω => varyingPreparedArm (rate := rate) i
      (assembleVaryingPrepareInput (activation ω) (incoming ω) (row ω)
        (calendarIndex ω) (hvalid ω))) :=
  (measurable_varyingPreparedArm (rate := rate) i).comp
    (measurable_assembleVaryingPrepareInput rate activation incoming row calendarIndex
      hactivation hincoming hrow hcalendar hvalid)

/-- Separate measurable input maps suffice for the next carried
ordinary/dagger configuration projection. -/
theorem measurable_varyingPreparedConfiguration_atComponents {p : Parameters}
    {Ω : Type*} [MeasurableSpace Ω] (rate : RateInput p)
    (i : Fin (p.m - 1)) (activation : Ω → Activation p)
    (incoming : Ω → IncomingConfiguration p rate)
    (row : Ω → CompleteRow p) (calendarIndex : Ω → Fin p.T)
    (hactivation : Measurable activation) (hincoming : Measurable incoming)
    (hrow : Measurable row) (hcalendar : Measurable calendarIndex)
    (hvalid : ∀ ω, (activation ω).val ≤ (calendarIndex ω).val + 1) :
    Measurable (fun ω => varyingPreparedConfiguration (rate := rate) i
      (assembleVaryingPrepareInput (activation ω) (incoming ω) (row ω)
        (calendarIndex ω) (hvalid ω))) :=
  (measurable_varyingPreparedConfiguration (rate := rate) i).comp
    (measurable_assembleVaryingPrepareInput rate activation incoming row calendarIndex
      hactivation hincoming hrow hcalendar hvalid)

/-- Separate measurable maps, plus only active-time validity, make the
varying observation result code measurable. -/
theorem measurable_varyingObservationResultCode_atComponents {p : Parameters}
    {Ω : Type*} [MeasurableSpace Ω] (rate : RateInput p)
    (i : Fin (p.m - 1)) (activation : Ω → Activation p)
    (carry : Ω → CarriedState p rate) (row : Ω → CompleteRow p)
    (calendarIndex : Ω → Fin p.T) (feedback : Ω → Fin (D p + 1))
    (arm : Ω → Fin p.K)
    (hactivation : Measurable activation) (hcarry : Measurable carry)
    (hrow : Measurable row) (hcalendar : Measurable calendarIndex)
    (hfeedback : Measurable feedback) (harm : Measurable arm)
    (hvalid : ∀ ω, (activation ω).val ≤ (calendarIndex ω).val + 1) :
    Measurable (fun ω => varyingObservationResultCode rate i
      (assembleVaryingObservationInput (activation ω) (carry ω) (row ω)
        (calendarIndex ω) (hvalid ω) (feedback ω) (arm ω))) :=
  (measurable_varyingObservationResultCode rate i).comp
    (measurable_assembleVaryingObservationInput rate activation carry row calendarIndex
      feedback arm hactivation hcarry hrow hcalendar hfeedback harm hvalid)

/-- The varying assembled observation result reconstructs the exact source
local operation on the supplied carry, row, valid time, feedback grid point,
and played arm. -/
theorem assembledObservation_reconstructs_recordOrServiceThenDown {p : Parameters}
    (rate : RateInput p) (i : Fin (p.m - 1)) (activation : Activation p)
    (carry : CarriedState p rate) (row : CompleteRow p) (calendarIndex : Fin p.T)
    (hvalid : activation.val ≤ calendarIndex.val + 1)
    (feedback : Fin (D p + 1)) (arm : Fin p.K) :
    decodeObservationResultCode rate i activation
        (assembleObservationInput carry row ⟨calendarIndex, hvalid⟩ feedback arm)
        (observationResultCode rate i activation
          (assembleObservationInput carry row ⟨calendarIndex, hvalid⟩ feedback arm)) =
      DeclaredFollowerLocalRound.recordOrServiceThenDown rate i row activation
        calendarIndex hvalid arm (FollowerDownMeasurability.feedbackAtGrid p feedback)
        (reconstructCarriedState carry.1 carry.2) :=
  decode_observationResultCode_atComponents_eq_actual rate i activation carry row
    ⟨calendarIndex, hvalid⟩ feedback arm

end Bandits.Support.FollowerVaryingActivationMeasurability

end
