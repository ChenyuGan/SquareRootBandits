/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.FollowerLifecycleMeasurability
public import Bandits.Support.FollowerObservationStageMeasurabilityRepair
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# Varying-carry measurability of follower start and arm preparation

The actual start/interruption result and `prepare` operation are lifted over
the accepted lossless carried state, ordinary proposal memory, complete row,
and active calendar time.  Saved buffer observations and thinning scalars keep
their original finite real product structures.  The operation code retains
all checked failures and fallback branches; the full carried output updates
only the countable state register and keeps the original scalar family.

Sources: `sources/zip4/manuscript/06_interruptions.tex:235-255`,
`sources/zip4/manuscript/05_binary_transport.tex:74-124`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:8-14`.

These results concern the supplied pre-choice local operation only. They
establish no physical feedback law, input provenance, history adaptation,
whole-run claim, or manuscript theorem closure.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.FollowerPrepareJointMeasurability

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.CompletePublicTable
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.FollowerDownMeasurability
open Bandits.Support.FollowerDownJointMeasurability
open Bandits.Support.SparseCalendarReplay
open Bandits.Support.FollowerLifecycleMeasurability
open Bandits.Support.FollowerObservationStageMeasurabilityRepair
open Bandits.Support.DeclaredFollowerLocalRound

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ActiveFollowerDownAcceptance.RateInput
abbrev ActiveCalendarTime (p : Parameters) (activation : Activation p) :=
  FollowerLifecycleMeasurability.ActiveCalendarTime p activation
abbrev CarriedState (p : Parameters) (rate : RateInput p) :=
  FollowerObservationStageMeasurabilityRepair.CarriedState p rate
abbrev FollowerCarryIndex (p : Parameters) (rate : RateInput p) :=
  FollowerObservationStageMeasurabilityRepair.FollowerCarryIndex p rate
abbrev LocalMemoryCode (p : Parameters) :=
  FollowerLifecycleMeasurability.LocalMemoryCode p

instance localMemoryCodeMeasurableSpace (p : Parameters) :
    MeasurableSpace (LocalMemoryCode p) := ⊤

instance localMemoryCodeMeasurableSingletonClass (p : Parameters) :
    MeasurableSingletonClass (LocalMemoryCode p) := ⟨fun _ => trivial⟩

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

private theorem measurableEmbedding_sigmaMk {α : Type*} {β : α → Type*}
    [∀ a, MeasurableSpace (β a)] (a : α) :
    MeasurableEmbedding (Sigma.mk a : β a → Sigma β) := by
  classical
  refine ⟨?_, measurable_sigmaMk a, ?_⟩
  · intro x y h
    cases h
    rfl
  · intro s hs
    change MeasurableSet[
      (⨅ b, (inferInstance : MeasurableSpace (β b)).map (Sigma.mk b))]
      (Sigma.mk a '' s)
    rw [MeasurableSpace.measurableSet_iInf]
    intro b
    rw [MeasurableSpace.map_def]
    by_cases h : b = a
    · subst b
      have hinj : Function.Injective (Sigma.mk a : β a → Sigma β) := by
        intro x y hxy
        cases hxy
        rfl
      simpa only [hinj.preimage_image] using hs
    · have hempty : (Sigma.mk b) ⁻¹' (Sigma.mk a '' s) = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        rintro x ⟨y, _, hxy⟩
        exact h (congrArg Sigma.fst hxy).symm
      rw [hempty]
      exact MeasurableSet.empty

/-- The canonical measurable assembly from a countable disjoint union and a
separate Borel input. The continuous fiber is carried without coding it. -/
private theorem measurable_assembleSigmaProduct {α : Type*} [Countable α]
    {β : α → Type*} [∀ a, MeasurableSpace (β a)]
    {γ : Type*} [MeasurableSpace γ] :
    Measurable (fun x : (Sigma β) × γ =>
      (⟨x.1.1, (x.1.2, x.2)⟩ : Sigma fun a => β a × γ)) := by
  intro s hs
  have hsections (a : α) :
      MeasurableSet ((@Sigma.mk α (fun b => β b × γ) a) ⁻¹' s) := by
    exact (measurable_sigmaMk (β := fun b => β b × γ) a) hs
  have himages (a : α) : MeasurableSet
      ((Prod.map (Sigma.mk a) id) ''
        ((@Sigma.mk α (fun b => β b × γ) a) ⁻¹' s)) :=
    ((measurableEmbedding_sigmaMk a).prodMap MeasurableEmbedding.id).measurableSet_image'
      (hsections a)
  have hdecomp :
      (fun x : (Sigma β) × γ =>
        (⟨x.1.1, (x.1.2, x.2)⟩ : Sigma fun a => β a × γ)) ⁻¹' s =
      ⋃ a : α, (Prod.map (Sigma.mk a) id) ''
        ((@Sigma.mk α (fun b => β b × γ) a) ⁻¹' s) := by
    ext x
    constructor
    · intro hx
      exact Set.mem_iUnion.mpr ⟨x.1.1, (x.1.2, x.2), hx, rfl⟩
    · intro hx
      obtain ⟨a, y, hy, hxy⟩ := Set.mem_iUnion.mp hx
      subst x
      exact hy
  rw [hdecomp]
  exact MeasurableSet.iUnion himages

/-! ## Lossless ordinary/dagger input representation -/

/-- Observable representation of the existing ordinary local configuration
or its actual absorbing dagger case. Its `Option` measurable space is
transported from the measurable disjoint union, preserving the original
continuous scalar fibers of `CarriedState`. -/
abbrev IncomingConfiguration (p : Parameters) (rate : RateInput p) :=
  Option (CarriedState p rate × LocalMemoryCode p)

/-- The measurable disjoint-union view used only to give the `Option` its
ordinary/dagger observable structure. -/
def incomingConfigurationToSum {p : Parameters} {rate : RateInput p}
    (x : IncomingConfiguration p rate) :
    Unit ⊕ (CarriedState p rate × LocalMemoryCode p) :=
  match x with
  | none => Sum.inl ()
  | some data => Sum.inr data

instance incomingConfigurationMeasurableSpace (p : Parameters)
    (rate : RateInput p) : MeasurableSpace (IncomingConfiguration p rate) :=
  (inferInstance : MeasurableSpace
    (Unit ⊕ (CarriedState p rate × LocalMemoryCode p))).comap
      (incomingConfigurationToSum (p := p) (rate := rate))

theorem measurable_incomingConfigurationToSum {p : Parameters}
    (rate : RateInput p) :
    Measurable (incomingConfigurationToSum (p := p) (rate := rate)) :=
  comap_measurable _

/-- Decode the observable option as exactly the existing `LocalConfiguration`.
The ordinary case reconstructs the full original state and memory. -/
def localConfigurationOfIncoming {p : Parameters} (rate : RateInput p)
    (x : IncomingConfiguration p rate) : LocalConfiguration p rate :=
  match x with
  | none => .dagger
  | some (state, memory) =>
      .ordinary (reconstructCarriedState state.1 state.2)
        (FollowerLifecycleMeasurability.localMemoryOfCode memory)

/-- Encode an existing local configuration without replacing its buffer
coordinates or changing its ordinary/dagger status. -/
def incomingOfLocalConfiguration {p : Parameters} (rate : RateInput p)
    (x : LocalConfiguration p rate) : IncomingConfiguration p rate :=
  match x with
  | .dagger => none
  | .ordinary state memory =>
      some (carriedStateOfState rate state,
        FollowerLifecycleMeasurability.localMemoryCode memory)

/-- Encoding and decoding recover the entire existing configuration, including
dagger and both saved real scalars at every original buffer position. -/
theorem localConfigurationOfIncoming_incomingOfLocalConfiguration
    {p : Parameters} (rate : RateInput p) (x : LocalConfiguration p rate) :
    localConfigurationOfIncoming rate (incomingOfLocalConfiguration rate x) = x := by
  cases x with
  | dagger => rfl
  | ordinary state memory =>
      have hstate : reconstructCarriedState
          (carriedStateOfState rate state).1
          (carriedStateOfState rate state).2 = state := by
        simpa [reconstructCarriedState, carriedStateBuffer] using
          FollowerObservationStageMeasurabilityRepair.carriedStateOfState_reconstruct
            rate state
      simp only [localConfigurationOfIncoming, incomingOfLocalConfiguration]
      rw [hstate, FollowerLifecycleMeasurability.localMemoryOfCode_code]

/-! ## The actual start/interruption result with varying carry -/

/-- A separate-input Sigma carrier for the actual start-round code. Its only
uncountable coordinates are the original saved scalar family. -/
abbrev StartInput (p : Parameters) (rate : RateInput p) :=
  Sigma fun index : FollowerCarryIndex p rate =>
    SavedScalarFamily index.2.1 × (LocalMemoryCode p × Fin p.T)

/-- Assemble the existing carry, ordinary proposal memory, and calendar time
as separate inputs. -/
def assembleStartInput {p : Parameters} {rate : RateInput p}
    (state : CarriedState p rate) (memory : LocalMemoryCode p) (t : Fin p.T) :
    StartInput p rate :=
  ⟨state.1, (state.2, (memory, t))⟩

/-- The existing checked start/interruption result code on the full varying
carry input. -/
def startRoundResultCode {p : Parameters} (rate : RateInput p)
    (x : StartInput p rate) : StartRoundResultCode p rate :=
  FollowerLifecycleMeasurability.startRoundResultCodeAt rate x.1.1
    x.2.2.1 x.1.2.2 x.2.1 x.2.2.2

private theorem measurable_startRoundResultCodeOnFiber {p : Parameters}
    (rate : RateInput p) (index : FollowerCarryIndex p rate) :
    Measurable (fun x : SavedScalarFamily index.2.1 ×
      (LocalMemoryCode p × Fin p.T) =>
        FollowerLifecycleMeasurability.startRoundResultCodeAt rate index.1
          x.2.1 index.2.2 x.1 x.2.2) := by
  apply measurable_from_prod_countable_left
  intro memoryTime
  have hfixed := FollowerLifecycleMeasurability.measurable_startRoundResultCodeAt
    rate index.1 memoryTime.1 index.2.2
  have hpair : Measurable (fun values : SavedScalarFamily index.2.1 =>
      (values, memoryTime.2)) := measurable_id.prodMk measurable_const
  exact hfixed.comp hpair

/-- Measurability of the actual start-round result over all registers,
proposal memory, saved scalars, and `Fin p.T` calendar times. -/
theorem measurable_startRoundResultCode {p : Parameters} (rate : RateInput p) :
    Measurable (startRoundResultCode rate : StartInput p rate →
      StartRoundResultCode p rate) := by
  apply measurable_of_sigma_sections
  intro index
  exact measurable_startRoundResultCodeOnFiber rate index

/-- The literal start-input assembler is measurable from its three separate
component maps. -/
theorem measurable_assembleStartInput {p : Parameters} {rate : RateInput p}
    {Ω : Type*} [MeasurableSpace Ω]
    (state : Ω → CarriedState p rate) (memory : Ω → LocalMemoryCode p)
    (t : Ω → Fin p.T) (hstate : Measurable state)
    (hmemory : Measurable memory) (ht : Measurable t) :
    Measurable (fun ω => assembleStartInput (state ω) (memory ω) (t ω)) := by
  exact measurable_assembleSigmaProduct.comp
    (hstate.prodMk (hmemory.prodMk ht))

/-- Arbitrary-base start-result measurability with only the actual separate
carry, memory, and time map premises. -/
theorem measurable_startRoundResultCode_atComponents {p : Parameters}
    (rate : RateInput p) {Ω : Type*} [MeasurableSpace Ω]
    (state : Ω → CarriedState p rate) (memory : Ω → LocalMemoryCode p)
    (t : Ω → Fin p.T) (hstate : Measurable state)
    (hmemory : Measurable memory) (ht : Measurable t) :
    Measurable (fun ω => startRoundResultCode rate
      (assembleStartInput (state ω) (memory ω) (t ω))) :=
  (measurable_startRoundResultCode rate).comp
    (measurable_assembleStartInput state memory t hstate hmemory ht)

/-- Exact reconstruction of the existing start operation, including every
local-domain failure and the original unmodified buffer. -/
theorem startRoundResultCode_atComponents_reconstruct {p : Parameters}
    (rate : RateInput p) (state : CarriedState p rate)
    (memory : LocalMemoryCode p) (t : Fin p.T) :
    FollowerLifecycleMeasurability.startRoundResultOfCode rate
        (carriedStateBuffer state)
        (startRoundResultCode rate (assembleStartInput state memory t)) =
      ActiveFollowerLifecycle.startRound rate.eta t
        (reconstructCarriedState state.1 state.2)
        (FollowerLifecycleMeasurability.localMemoryOfCode memory) := by
  exact FollowerLifecycleMeasurability.startRoundResultCodeAt_reconstruct rate
    state.1.1 memory state.1.2.2 state.2 t

/-! ## Fixed-activation joint prepare input -/

/-- The countable index joins only the existing countable register/skeleton
index and ordinary proposal-memory code. Its fiber retains the original saved
real scalar family. -/
abbrev PrepareCarryMemoryIndex (p : Parameters) (rate : RateInput p) :=
  FollowerCarryIndex p rate × LocalMemoryCode p

/-- The prepare-input carrier at one genuine activation. Time still varies
over its original active-calendar subtype. The dagger summand has no buffer;
the ordinary summand retains the accepted carried state and scalar family. -/
abbrev PrepareInput (p : Parameters) (rate : RateInput p)
    (activation : Activation p) :=
  (CompleteRow p × ActiveCalendarTime p activation) ⊕
    Sigma fun index : PrepareCarryMemoryIndex p rate =>
      (CompleteRow p × SavedScalarFamily index.1.2.1) ×
        ActiveCalendarTime p activation

instance prepareInputMeasurableSpace {p : Parameters} {rate : RateInput p}
    {activation : Activation p} : MeasurableSpace (PrepareInput p rate activation) := by
  letI : ∀ index : PrepareCarryMemoryIndex p rate,
      MeasurableSpace ((CompleteRow p × SavedScalarFamily index.1.2.1) ×
        ActiveCalendarTime p activation) := fun _ => inferInstance
  infer_instance

abbrev PreparedCarryScalarSigma (p : Parameters) (rate : RateInput p) :=
  Sigma fun index : PrepareCarryMemoryIndex p rate =>
    SavedScalarFamily index.1.2.1

instance preparedCarryScalarSigmaMeasurableSpace {p : Parameters}
    {rate : RateInput p} :
    MeasurableSpace (PreparedCarryScalarSigma p rate) := by
  letI : ∀ index : PrepareCarryMemoryIndex p rate,
      MeasurableSpace (SavedScalarFamily index.1.2.1) := fun _ => inferInstance
  exact Sigma.instMeasurableSpace

private def encodePrepareCarryMemory {p : Parameters} {rate : RateInput p}
    (x : CarriedState p rate × LocalMemoryCode p) : PreparedCarryScalarSigma p rate :=
  ⟨(x.1.1, x.2), x.1.2⟩

private theorem measurable_encodePrepareCarryMemory {p : Parameters}
    (rate : RateInput p) :
    Measurable (encodePrepareCarryMemory (p := p) (rate := rate)) := by
  apply measurable_from_prod_countable_left
  intro memory
  apply measurable_of_sigma_sections
  intro index
  exact measurable_sigmaMk (index, memory)

private def reorderPrepareCarrySigma {p : Parameters} {rate : RateInput p}
    {activation : Activation p}
    (x : Sigma fun index : PrepareCarryMemoryIndex p rate =>
      SavedScalarFamily index.1.2.1 ×
        (CompleteRow p × ActiveCalendarTime p activation)) :
    Sigma fun index : PrepareCarryMemoryIndex p rate =>
      (CompleteRow p × SavedScalarFamily index.1.2.1) ×
        ActiveCalendarTime p activation :=
  ⟨x.1, ((x.2.2.1, x.2.1), x.2.2.2)⟩

private theorem measurable_reorderPrepareCarrySigma {p : Parameters}
    {rate : RateInput p} {activation : Activation p} :
    Measurable (reorderPrepareCarrySigma (p := p) (rate := rate)
      (activation := activation)) := by
  apply measurable_of_sigma_sections
  intro index
  have hreorder : Measurable (fun x : SavedScalarFamily index.1.2.1 ×
      (CompleteRow p × ActiveCalendarTime p activation) =>
      ((x.2.1, x.1), x.2.2)) := by
    exact ((measurable_fst.comp measurable_snd).prodMk measurable_fst).prodMk
      (measurable_snd.comp measurable_snd)
  exact (measurable_sigmaMk index).comp hreorder

private def assemblePrepareOrdinarySigma {p : Parameters} {rate : RateInput p}
    {activation : Activation p}
    (x : PreparedCarryScalarSigma p rate ×
      (CompleteRow p × ActiveCalendarTime p activation)) :
    Sigma fun index : PrepareCarryMemoryIndex p rate =>
      (CompleteRow p × SavedScalarFamily index.1.2.1) ×
        ActiveCalendarTime p activation :=
  reorderPrepareCarrySigma
    (⟨x.1.1, (x.1.2, x.2)⟩ : Sigma fun index : PrepareCarryMemoryIndex p rate =>
      SavedScalarFamily index.1.2.1 ×
        (CompleteRow p × ActiveCalendarTime p activation))

/-- Assemble separate ordinary/dagger, row, and active-calendar-time inputs. -/
def assemblePrepareInput {p : Parameters} {rate : RateInput p}
    {activation : Activation p} (incoming : IncomingConfiguration p rate)
    (row : CompleteRow p) (time : ActiveCalendarTime p activation) :
    PrepareInput p rate activation :=
  match incoming with
  | none => Sum.inl (row, time)
  | some (state, memory) =>
      Sum.inr ⟨(state.1, memory), ((row, state.2), time)⟩

private def assemblePrepareInputFromDistributed {p : Parameters}
    {rate : RateInput p} {activation : Activation p}
    (x : (Unit × (CompleteRow p × ActiveCalendarTime p activation)) ⊕
      ((CarriedState p rate × LocalMemoryCode p) ×
        (CompleteRow p × ActiveCalendarTime p activation))) :
    PrepareInput p rate activation :=
  Sum.elim
    (fun (_, rowTime) => Sum.inl rowTime)
    (fun ((state, memory), rowTime) =>
      Sum.inr (assemblePrepareOrdinarySigma
        (encodePrepareCarryMemory (state, memory), rowTime))) x

private theorem measurable_assemblePrepareInputFromDistributed {p : Parameters}
    {rate : RateInput p} {activation : Activation p} :
    Measurable (assemblePrepareInputFromDistributed
      (p := p) (rate := rate) (activation := activation)) := by
  have hleft : Measurable (fun x : Unit ×
      (CompleteRow p × ActiveCalendarTime p activation) =>
      Sum.inl x.2 : Unit × (CompleteRow p × ActiveCalendarTime p activation) →
        PrepareInput p rate activation) :=
    measurable_inl.comp measurable_snd
  have hassembleSigma : Measurable (fun y : PreparedCarryScalarSigma p rate ×
      (CompleteRow p × ActiveCalendarTime p activation) =>
      (⟨y.1.1, (y.1.2, y.2)⟩ : Sigma fun index : PrepareCarryMemoryIndex p rate =>
        SavedScalarFamily index.1.2.1 ×
          (CompleteRow p × ActiveCalendarTime p activation))) :=
    measurable_assembleSigmaProduct
  have hSigma : Measurable (assemblePrepareOrdinarySigma
      (p := p) (rate := rate) (activation := activation)) :=
    (measurable_reorderPrepareCarrySigma (p := p) (rate := rate)
      (activation := activation)).comp hassembleSigma
  have hright : Measurable (fun x :
      (CarriedState p rate × LocalMemoryCode p) ×
        (CompleteRow p × ActiveCalendarTime p activation) =>
      Sum.inr (assemblePrepareOrdinarySigma
        (encodePrepareCarryMemory (x.1.1, x.1.2), x.2)) :
      (CarriedState p rate × LocalMemoryCode p) ×
        (CompleteRow p × ActiveCalendarTime p activation) →
          PrepareInput p rate activation) :=
    measurable_inr.comp
      (hSigma.comp
        (((measurable_encodePrepareCarryMemory rate).comp measurable_fst).prodMk
          measurable_snd))
  exact Measurable.sumElim hleft hright

/-- The prepare assembler is measurable from only the separate actual input
maps. The complete row and active-time subtype keep their Borel structures. -/
theorem measurable_assemblePrepareInput {p : Parameters}
    {rate : RateInput p} (activation : Activation p)
    {Ω : Type*} [MeasurableSpace Ω]
    (incoming : Ω → IncomingConfiguration p rate)
    (row : Ω → CompleteRow p)
    (time : Ω → ActiveCalendarTime p activation)
    (hincoming : Measurable incoming) (hrow : Measurable row)
    (htime : Measurable time) :
    Measurable (fun ω => assemblePrepareInput (incoming ω) (row ω) (time ω)) := by
  have hbase : Measurable (fun ω =>
      (incomingConfigurationToSum (incoming ω), (row ω, time ω))) := by
    exact ((measurable_incomingConfigurationToSum rate).comp hincoming).prodMk
      (hrow.prodMk htime)
  let distrib := MeasurableEquiv.sumProdDistrib Unit
    (CarriedState p rate × LocalMemoryCode p)
    (CompleteRow p × ActiveCalendarTime p activation)
  have hEq :
      (fun ω => assemblePrepareInput (incoming ω) (row ω) (time ω)) =
        (fun ω => assemblePrepareInputFromDistributed
          (distrib (incomingConfigurationToSum (incoming ω), (row ω, time ω)))) := by
    funext ω
    cases hin : incoming ω <;> rfl
  rw [hEq]
  exact (measurable_assemblePrepareInputFromDistributed
    (p := p) (rate := rate) (activation := activation)).comp
      (distrib.measurable_toFun.comp hbase)

def prepareInputRow {p : Parameters} {rate : RateInput p}
    {activation : Activation p} (x : PrepareInput p rate activation) :
    CompleteRow p :=
  match x with
  | .inl data => data.1
  | .inr ⟨_, ((row, _), _)⟩ => row

def prepareInputTime {p : Parameters} {rate : RateInput p}
    {activation : Activation p} (x : PrepareInput p rate activation) :
    ActiveCalendarTime p activation :=
  match x with
  | .inl data => data.2
  | .inr ⟨_, (_, time)⟩ => time

def prepareInputBuffer {p : Parameters} {rate : RateInput p}
    {activation : Activation p} (x : PrepareInput p rate activation) :
    List (SparseCalendarRecord p.K) :=
  match x with
  | .inl _ => []
  | .inr ⟨index, ((_, values), _)⟩ =>
      bufferFromSkeletonAndScalars index.1.2.2 values

def prepareInputConfiguration {p : Parameters} (rate : RateInput p)
    {activation : Activation p} (x : PrepareInput p rate activation) :
    LocalConfiguration p rate :=
  match x with
  | .inl _ => .dagger
  | .inr ⟨index, ((_, values), _)⟩ =>
      .ordinary (followerStateOfCode rate index.1.1
        (bufferFromSkeletonAndScalars index.1.2.2 values))
        (FollowerLifecycleMeasurability.localMemoryOfCode index.2)

def prepareRoundCodeOnInput {p : Parameters} (rate : RateInput p)
    (i : Fin (p.m - 1)) {activation : Activation p}
    (x : PrepareInput p rate activation) : PreparedRoundCode p rate :=
  match x with
  | .inl _ => fallbackPreparedRoundCode rate i
  | .inr ⟨index, ((row, values), time)⟩ =>
      FollowerLifecycleMeasurability.prepareRoundCodeAt rate i activation
        (some (index.1.1, index.2)) index.1.2.2 row time values

/-- The actual prepare arm/configuration code is jointly measurable over the
varying carry, ordinary memory, complete row, and genuine active time. -/
theorem measurable_prepareRoundCode {p : Parameters} (rate : RateInput p)
    (i : Fin (p.m - 1)) (activation : Activation p) :
    Measurable (prepareRoundCodeOnInput rate i (activation := activation) :
      PrepareInput p rate activation → PreparedRoundCode p rate) := by
  apply Measurable.sumElim
  · exact measurable_const
  · apply measurable_of_sigma_sections
    intro index
    rcases index with ⟨carry, memory⟩
    rcases carry with ⟨stateCode, skeletonData⟩
    cases skeletonData with
    | mk n skeleton =>
        exact FollowerLifecycleMeasurability.measurable_prepareRoundCodeAt
          rate i activation (some (stateCode, memory)) skeleton

/-- Arbitrary-base prepare-code measurability with only separate incoming,
complete-row, and genuine active-time measurability premises. -/
theorem measurable_prepareRoundCode_atComponents {p : Parameters}
    (rate : RateInput p) (i : Fin (p.m - 1)) (activation : Activation p)
    {Ω : Type*} [MeasurableSpace Ω]
    (incoming : Ω → IncomingConfiguration p rate)
    (row : Ω → CompleteRow p)
    (time : Ω → ActiveCalendarTime p activation)
    (hincoming : Measurable incoming) (hrow : Measurable row)
    (htime : Measurable time) :
    Measurable (fun ω => prepareRoundCodeOnInput rate i (activation := activation)
      (assemblePrepareInput (incoming ω) (row ω) (time ω))) :=
  (measurable_prepareRoundCode rate i activation).comp
    (measurable_assemblePrepareInput activation incoming row time
      hincoming hrow htime)

private theorem measurable_carriedConfigurationFromCode {p : Parameters}
    (rate : RateInput p) (index : FollowerCarryIndex p rate) :
    Measurable (fun x : SavedScalarFamily index.2.1 × PreparedRoundCode p rate =>
      match x.2.configuration with
      | none => (none : IncomingConfiguration p rate)
      | some (stateCode, memory) =>
          some (⟨(stateCode, index.2), x.1⟩, memory)) := by
  apply measurable_from_prod_countable_left
  intro code
  cases hconfig : code.configuration with
  | none =>
      simpa [hconfig] using
        (measurable_const : Measurable (fun _ : SavedScalarFamily index.2.1 =>
          (none : IncomingConfiguration p rate)))
  | some config =>
      rcases config with ⟨stateCode, memory⟩
      have hEq : (fun values : SavedScalarFamily index.2.1 =>
          match code.configuration with
          | none => (none : IncomingConfiguration p rate)
          | some (stateCode, memory) =>
              some (⟨(stateCode, index.2), values⟩, memory)) =
          fun values => some (⟨(stateCode, index.2), values⟩, memory) := by
        funext values
        simp [hconfig]
      rw [hEq]
      apply (measurable_comap_iff).2
      change Measurable (fun values : SavedScalarFamily index.2.1 =>
        incomingConfigurationToSum
          (some (⟨(stateCode, index.2), values⟩, memory)))
      simp only [incomingConfigurationToSum]
      exact measurable_inr.comp
        (((measurable_sigmaMk (⟨stateCode, index.2⟩ : FollowerCarryIndex p rate)).comp
          measurable_id).prodMk measurable_const)

def prepareOutputConfiguration {p : Parameters} (rate : RateInput p)
    (i : Fin (p.m - 1)) {activation : Activation p}
    (x : PrepareInput p rate activation) : IncomingConfiguration p rate :=
  match x with
  | .inl _ => none
  | .inr ⟨index, ((_, values), _)⟩ =>
      match (prepareRoundCodeOnInput rate i x).configuration with
      | none => none
      | some (stateCode, memory) =>
          some (⟨(stateCode, index.1.2), values⟩, memory)

/-- Ordinary prepared output changes only the countable state register and
proposal-memory code. Its full carried state retains every original saved
scalar and therefore reconstructs the exact input buffer; dagger carries no
buffer. -/
theorem prepareOutputConfiguration_buffer_or_dagger {p : Parameters}
    (rate : RateInput p) (i : Fin (p.m - 1)) (activation : Activation p)
    (x : PrepareInput p rate activation) :
    prepareOutputConfiguration rate i (activation := activation) x = none ∨
      ∃ state memory,
        prepareOutputConfiguration rate i (activation := activation) x =
          some (state, memory) ∧ carriedStateBuffer state = prepareInputBuffer x := by
  cases x with
  | inl data => exact Or.inl rfl
  | inr data =>
      cases data with
      | mk index rest =>
          rcases rest with ⟨⟨row, values⟩, time⟩
          cases hconfig : (prepareRoundCodeOnInput rate i
              (activation := activation)
              (Sum.inr ⟨index, ((row, values), time)⟩)).configuration with
          | none =>
              exact Or.inl (by simp [prepareOutputConfiguration, hconfig])
          | some config =>
              rcases config with ⟨stateCode, memory⟩
              refine Or.inr ⟨⟨(stateCode, index.1.2), values⟩, memory, ?_, ?_⟩
              · simp [prepareOutputConfiguration, hconfig]
              · simp [carriedStateBuffer, prepareInputBuffer,
                  bufferFromSkeletonAndScalars]

private theorem measurable_prepareOutputConfiguration {p : Parameters}
    (rate : RateInput p) (i : Fin (p.m - 1)) (activation : Activation p) :
    Measurable (prepareOutputConfiguration rate i (activation := activation) :
      PrepareInput p rate activation → IncomingConfiguration p rate) := by
  apply Measurable.sumElim
  · exact measurable_const
  · apply measurable_of_sigma_sections
    intro index
    have hcode : Measurable (fun x :
        (CompleteRow p × SavedScalarFamily index.1.2.1) ×
          ActiveCalendarTime p activation =>
        prepareRoundCodeOnInput rate i (activation := activation)
          (Sum.inr ⟨index, x⟩)) :=
      (measurable_prepareRoundCode rate i activation).comp
        (measurable_inr.comp (measurable_sigmaMk index))
    exact (measurable_carriedConfigurationFromCode rate index.1).comp
      ((measurable_snd.comp measurable_fst).prodMk hcode)

/-! ## Full carried prepared output -/

/-- Full output data: complete row, genuine active-time coordinate, arm, and
the losslessly carried ordinary result or dagger. The follower and activation
are fixed parameters of this operation. -/
abbrev PrepareOutput (p : Parameters) (rate : RateInput p)
    (activation : Activation p) :=
  (CompleteRow p × ActiveCalendarTime p activation) ×
    (Fin p.K × IncomingConfiguration p rate)

def prepareOutputOnInput {p : Parameters} (rate : RateInput p)
    (i : Fin (p.m - 1)) (activation : Activation p)
    (x : PrepareInput p rate activation) : PrepareOutput p rate activation :=
  ((prepareInputRow x, prepareInputTime x),
    ((prepareRoundCodeOnInput rate i (activation := activation) x).arm,
      prepareOutputConfiguration rate i (activation := activation) x))

theorem measurable_prepareOutput {p : Parameters} (rate : RateInput p)
    (i : Fin (p.m - 1)) (activation : Activation p) :
    Measurable (prepareOutputOnInput rate i activation :
      PrepareInput p rate activation → PrepareOutput p rate activation) := by
  have hrow : Measurable (prepareInputRow (p := p) (rate := rate)
      (activation := activation) : PrepareInput p rate activation → CompleteRow p) := by
    apply Measurable.sumElim
    · exact measurable_fst
    · apply measurable_of_sigma_sections
      intro index
      exact measurable_fst.comp measurable_fst
  have htime : Measurable (prepareInputTime (p := p) (rate := rate)
      (activation := activation) :
        PrepareInput p rate activation → ActiveCalendarTime p activation) := by
    apply Measurable.sumElim
    · exact measurable_snd
    · apply measurable_of_sigma_sections
      intro index
      exact measurable_snd
  have hcode := measurable_prepareRoundCode rate i activation
  have harm : Measurable (fun x : PrepareInput p rate activation =>
      (prepareRoundCodeOnInput rate i (activation := activation) x).arm) :=
    (measurable_of_countable fun code : PreparedRoundCode p rate => code.arm).comp hcode
  exact ((hrow.prodMk htime).prodMk
    (harm.prodMk (measurable_prepareOutputConfiguration rate i activation)))

/-- Arbitrary-base full output measurability from only the separate actual
incoming configuration, complete row, and active-calendar-time maps. -/
theorem measurable_prepareOutput_atComponents {p : Parameters}
    (rate : RateInput p) (i : Fin (p.m - 1)) (activation : Activation p)
    {Ω : Type*} [MeasurableSpace Ω]
    (incoming : Ω → IncomingConfiguration p rate)
    (row : Ω → CompleteRow p)
    (time : Ω → ActiveCalendarTime p activation)
    (hincoming : Measurable incoming) (hrow : Measurable row)
    (htime : Measurable time) :
    Measurable (fun ω => prepareOutputOnInput rate i activation
      (assemblePrepareInput (incoming ω) (row ω) (time ω))) :=
  (measurable_prepareOutput rate i activation).comp
    (measurable_assemblePrepareInput activation incoming row time
      hincoming hrow htime)

/-- Decode a full output as the existing prepared round, retaining the fixed
follower and activation and every varying row, time, arm, state, and memory. -/
def preparedRoundOfOutput {p : Parameters} (rate : RateInput p)
    (i : Fin (p.m - 1)) (activation : Activation p)
    (x : PrepareOutput p rate activation) : PreparedRound p rate :=
  ⟨i, x.1.1, activation, x.1.2.1, x.1.2.2, x.2.1,
    localConfigurationOfIncoming rate x.2.2⟩

private theorem preparedRound_extFields {p : Parameters} {rate : RateInput p}
    {x y : PreparedRound p rate}
    (hfollower : x.follower = y.follower) (hrow : x.row = y.row)
    (hactivation : x.activation = y.activation) (htime : x.time = y.time)
    (harm : x.arm = y.arm) (hconfiguration : x.configuration = y.configuration) :
    x = y := by
  cases x with
  | mk xfollower xrow xactivation xtime xactive xarm xconfiguration =>
      cases y with
      | mk yfollower yrow yactivation ytime yactive yarm yconfiguration =>
          cases hfollower
          cases hrow
          cases hactivation
          cases htime
          cases harm
          cases hconfiguration
          have hactive : xactive = yactive := Subsingleton.elim _ _
          cases hactive
          rfl

theorem prepareOutputConfiguration_eq_coded {p : Parameters}
    (rate : RateInput p) (i : Fin (p.m - 1)) (activation : Activation p)
    (x : PrepareInput p rate activation) :
    localConfigurationOfIncoming rate
        (prepareOutputConfiguration rate i (activation := activation) x) =
      localConfigurationOfCode rate
        (prepareRoundCodeOnInput rate i (activation := activation) x).configuration
        (prepareInputBuffer x) := by
  cases x with
  | inl data => rfl
  | inr data =>
      cases data with
      | mk index rest =>
          rcases rest with ⟨⟨row, values⟩, time⟩
          cases hconfig : (prepareRoundCodeOnInput rate i
              (activation := activation)
              (Sum.inr ⟨index, ((row, values), time)⟩)).configuration with
          | none => simp [prepareOutputConfiguration, prepareInputBuffer,
              localConfigurationOfIncoming, localConfigurationOfCode, hconfig]
          | some config =>
              rcases config with ⟨stateCode, outputMemory⟩
              simp [prepareOutputConfiguration, prepareInputBuffer,
                localConfigurationOfIncoming, localConfigurationOfCode, hconfig,
                reconstructCarriedState]

/-- The full carried output reconstructs the actual prepare result exactly.
Ordinary success changes only the countable register index and retains the
input scalar family; dagger has no buffer. -/
theorem preparedRoundOfOutput_prepare {p : Parameters} (rate : RateInput p)
    (i : Fin (p.m - 1)) (activation : Activation p)
    (x : PrepareInput p rate activation) :
    preparedRoundOfOutput rate i activation
      (prepareOutputOnInput rate i activation x) =
      DeclaredFollowerLocalRound.prepare rate i (prepareInputRow x) activation
        (prepareInputTime x).1 (prepareInputTime x).2
        (prepareInputConfiguration rate x) := by
  cases x with
  | inl data =>
      rcases data with ⟨row, time⟩
      rfl
  | inr data =>
      cases data with
      | mk index rest =>
          rcases rest with ⟨⟨row, values⟩, time⟩
          let incoming : LocalConfigurationCode p rate := some (index.1.1, index.2)
          let code := FollowerLifecycleMeasurability.prepareRoundCodeAt rate i
            activation incoming index.1.2.2 row time values
          let buffer := bufferFromSkeletonAndScalars index.1.2.2 values
          let actual := DeclaredFollowerLocalRound.prepare rate i row activation
            time.1 time.2 (localConfigurationOfCode rate incoming buffer)
          have hfields : actual.follower = i ∧ actual.row = row ∧
              actual.activation = activation ∧ actual.time = time.1 := by
            cases hin : localConfigurationOfCode rate incoming buffer with
            | dagger => simp [actual, hin, DeclaredFollowerLocalRound.prepare]
            | ordinary state memory =>
                cases hstart : ActiveFollowerLifecycle.startRound
                    rate.eta time.1 state memory with
                | error reason =>
                    simp [actual, hin, hstart, DeclaredFollowerLocalRound.prepare]
                | ok result =>
                    rcases result with ⟨choiceState, choiceMemory⟩
                    cases hoff : ActiveFollowerQueueOperation.checkedUpOffer
                        rate.eta i row activation time.1 choiceState with
                    | failure =>
                        simp [actual, hin, hstart, hoff,
                          DeclaredFollowerLocalRound.prepare]
                    | noOffer =>
                        cases hchoice : ActiveFollowerArmChoice.followerArmChoice
                            choiceState row time.1 i none with
                        | none =>
                            simp [actual, hin, hstart, hoff, hchoice,
                              DeclaredFollowerLocalRound.prepare]
                        | some arm =>
                            simp [actual, hin, hstart, hoff, hchoice,
                              DeclaredFollowerLocalRound.prepare]
                    | offer offered =>
                        cases hchoice : ActiveFollowerArmChoice.followerArmChoice
                            choiceState row time.1 i (some offered) with
                        | none =>
                            simp [actual, hin, hstart, hoff, hchoice,
                              DeclaredFollowerLocalRound.prepare]
                        | some arm =>
                            simp [actual, hin, hstart, hoff, hchoice,
                              DeclaredFollowerLocalRound.prepare]
          rcases hfields with ⟨hfollower, hrow, hactivation, htime⟩
          have hrec := FollowerLifecycleMeasurability.prepareRoundCodeAt_reconstruct
            rate i activation (some (index.1.1, index.2))
            index.1.2.2 row time values
          have hsame : preparedRoundOfOutput rate i activation
              (prepareOutputOnInput rate i activation
                (Sum.inr ⟨index, ((row, values), time)⟩)) =
              preparedRoundOfCode rate actual.follower actual.row
                actual.activation ⟨actual.time, actual.active⟩ code buffer := by
            unfold preparedRoundOfOutput prepareOutputOnInput preparedRoundOfCode
            rw [prepareOutputConfiguration_eq_coded rate i activation
              (Sum.inr ⟨index, ((row, values), time)⟩)]
            apply preparedRound_extFields
            · exact hfollower.symm
            · exact hrow.symm
            · exact hactivation.symm
            · exact htime.symm
            · rfl
            · rfl
          change preparedRoundOfOutput rate i activation
              (prepareOutputOnInput rate i activation
                (Sum.inr ⟨index, ((row, values), time)⟩)) = actual
          rw [hsame]
          exact hrec

/-! ## Measurable ordinary, dagger, fallback, and arm projections -/

def preparedOutputIsOrdinary {p : Parameters} {rate : RateInput p}
    {activation : Activation p} (x : PrepareOutput p rate activation) : Bool :=
  decide x.2.2.isSome

def preparedOutputArm {p : Parameters} {rate : RateInput p}
    {activation : Activation p} (x : PrepareOutput p rate activation) :
    Fin p.K := x.2.1

def preparedOutputIsDagger {p : Parameters} {rate : RateInput p}
    {activation : Activation p} (x : PrepareOutput p rate activation) : Bool :=
  !preparedOutputIsOrdinary x

def preparedOutputIsFallback {p : Parameters} {rate : RateInput p}
    {activation : Activation p} (i : Fin (p.m - 1))
    (x : PrepareOutput p rate activation) : Bool :=
  preparedOutputIsDagger x && decide (preparedOutputArm x = fallbackArm p i)

theorem measurable_preparedOutputIsOrdinary {p : Parameters}
    (rate : RateInput p) (activation : Activation p) :
    Measurable (preparedOutputIsOrdinary :
      PrepareOutput p rate activation → Bool) := by
  have hsum : Measurable (fun x : Unit ⊕
      (CarriedState p rate × LocalMemoryCode p) =>
        decide (Sum.isRight x)) := by
    apply Measurable.sumElim
    · exact measurable_const
    · exact measurable_const
  have hoption : Measurable (fun x : IncomingConfiguration p rate =>
      decide x.isSome) := by
    have heq : (fun x : IncomingConfiguration p rate => decide x.isSome) =
        (fun x => decide (Sum.isRight (incomingConfigurationToSum x))) := by
      funext x
      cases x <;> rfl
    rw [heq]
    exact hsum.comp (measurable_incomingConfigurationToSum rate)
  exact hoption.comp (measurable_snd.comp measurable_snd)

theorem measurable_preparedOutputIsDagger {p : Parameters}
    (rate : RateInput p) (activation : Activation p) :
    Measurable (preparedOutputIsDagger :
      PrepareOutput p rate activation → Bool) := by
  exact (measurable_of_countable fun b : Bool => !b).comp
    (measurable_preparedOutputIsOrdinary rate activation)

theorem measurable_preparedOutputArm {p : Parameters} {rate : RateInput p}
    (activation : Activation p) :
    Measurable (preparedOutputArm :
      PrepareOutput p rate activation → Fin p.K) :=
  measurable_fst.comp measurable_snd

theorem measurable_preparedOutputIsFallback {p : Parameters}
    (rate : RateInput p) (i : Fin (p.m - 1)) (activation : Activation p) :
    Measurable (preparedOutputIsFallback i :
      PrepareOutput p rate activation → Bool) := by
  have harmBit : Measurable (fun x : PrepareOutput p rate activation =>
      decide (preparedOutputArm x = fallbackArm p i)) := by
    apply measurable_of_countable_fibers
    intro b
    cases b
    · have hset : {x : PrepareOutput p rate activation |
          decide (preparedOutputArm x = fallbackArm p i) = false} =
          (preparedOutputArm ⁻¹' {fallbackArm p i})ᶜ := by
        ext x
        simp
      rw [hset]
      exact ((measurableSet_singleton (fallbackArm p i)).preimage
        (measurable_preparedOutputArm activation)).compl
    · have hset : {x : PrepareOutput p rate activation |
          decide (preparedOutputArm x = fallbackArm p i) = true} =
          preparedOutputArm ⁻¹' {fallbackArm p i} := by
        ext x
        simp
      rw [hset]
      exact (measurableSet_singleton (fallbackArm p i)).preimage
        (measurable_preparedOutputArm activation)
  have hdagger := measurable_preparedOutputIsDagger rate activation
  have hpair := hdagger.prodMk harmBit
  exact (measurable_of_countable fun b : Bool × Bool => b.1 && b.2).comp hpair

end Bandits.Support.FollowerPrepareJointMeasurability

end
