/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.FollowerLoggingDownMeasurability
public import Bandits.Support.FollowerServiceMeasurability
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Prod

/-!
# Separate-input observation-stage measurability for a declared follower

This module lifts the existing `recordOrServiceThenDown` operation over the
follower's full discrete registers, ordered timestamp/pilot buffer skeleton,
original saved scalar product, complete row, active time, feedback index, and
played arm.  It uses only the accepted fixed-skeleton logging/DOWN and service
codes. The literal assembler is proved measurable from five separate maps,
using the countable disjoint-union structure, without a measurable assembled-input
premise. This is internal composition, with no physical-history or manuscript
theorem claim.

Sources: `sources/zip4/manuscript/06_interruptions.tex:192-209,235-276` and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:8-14`.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.FollowerObservationStageMeasurabilityRepair

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.CompletePublicTable
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.SparseCalendarReplay
open Bandits.Support.DeclaredFollowerLocalRound
open Bandits.Support.FollowerDownMeasurability
open Bandits.Support.FollowerDownJointMeasurability
open Bandits.Support.FollowerLoggingDownMeasurability
open Bandits.Support.FollowerServiceMeasurability

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ActiveFollowerDownAcceptance.RateInput
abbrev ActiveTime (p : Parameters) (activation : Activation p) :=
  FollowerLoggingDownMeasurability.ActiveTime p activation

/-- A countable index for every discrete register and the ordered buffer
timestamp/pilot skeleton. The skeleton fiber carries its original length. -/
abbrev FollowerCarryIndex (p : Parameters) (rate : RateInput p) :=
  FollowerStateCode p rate × Sigma (FollowerDownJointMeasurability.BufferSkeletonCode p)

theorem countableFollowerCarryIndex (p : Parameters) (rate : RateInput p) :
    Countable (FollowerCarryIndex p rate) := inferInstance

/-- The explicit lossless carried-state representation: countable registers
and skeleton index, followed by exactly the original finite scalar product. -/
abbrev CarriedState (p : Parameters) (rate : RateInput p) :=
  Sigma fun index : FollowerCarryIndex p rate =>
    SavedScalarFamily index.2.1

def carriedStateBuffer {p : Parameters} {rate : RateInput p}
    (x : CarriedState p rate) : List (SparseCalendarRecord p.K) :=
  FollowerDownJointMeasurability.bufferFromSkeletonAndScalars
    x.1.2.2 x.2

def carriedStateOfState {p : Parameters} (rate : RateInput p)
    (state : State p rate.eta) : CarriedState p rate :=
  ⟨(followerStateCode rate state,
      ⟨state.buffer.length,
        FollowerDownJointMeasurability.bufferSkeletonCode state.buffer⟩),
    FollowerDownJointMeasurability.bufferScalarsCode state.buffer⟩

/-- The explicit reconstruction recovers all registers and every continuous
buffer coordinate of any existing follower state. -/
theorem carriedStateOfState_reconstruct {p : Parameters} (rate : RateInput p)
    (state : State p rate.eta) :
    followerStateOfCode rate (carriedStateOfState rate state).1.1
      (carriedStateBuffer (carriedStateOfState rate state)) = state := by
  change followerStateOfCode rate (followerStateCode rate state)
      (FollowerDownJointMeasurability.bufferFromSkeletonAndScalars
        (FollowerDownJointMeasurability.bufferSkeletonCode state.buffer)
        (FollowerDownJointMeasurability.bufferScalarsCode state.buffer)) = state
  exact FollowerDownJointMeasurability.carriedState_countable_decomposition rate state

/-- The administrative representative of a fixed countable skeleton. Its
zero scalar coordinates are replaced immediately by the original values. -/
def sparseSkeletonBuffer {p : Parameters} {n : ℕ}
    (skeleton : FollowerDownJointMeasurability.BufferSkeletonCode p n) :
    List (SparseCalendarRecord p.K) :=
  FollowerDownJointMeasurability.bufferFromSkeletonAndScalars skeleton
    (fun _ => (⟨0, ⟨le_rfl, by norm_num⟩⟩,
      ⟨0, ⟨le_rfl, by norm_num⟩⟩))

def representativeState {p : Parameters} (rate : RateInput p)
    (index : FollowerCarryIndex p rate) : State p rate.eta :=
  followerStateOfCode rate index.1 (sparseSkeletonBuffer index.2.2)

theorem sparseSkeletonBuffer_length {p : Parameters} {n : ℕ}
    (skeleton : FollowerDownJointMeasurability.BufferSkeletonCode p n) :
    (sparseSkeletonBuffer skeleton).length = n := by
  simp [sparseSkeletonBuffer, FollowerDownJointMeasurability.bufferFromSkeletonAndScalars]

/-- Transport the original length-indexed scalar family to the representative
buffer's propositionally equal length. -/
def representativeValues {p : Parameters} {rate : RateInput p}
    (index : FollowerCarryIndex p rate) (values : SavedScalarFamily index.2.1) :
    SavedScalarFamily (representativeState rate index).buffer.length :=
  fun j => values (Fin.cast (sparseSkeletonBuffer_length index.2.2) j)

/-- Exact adapter equality from the administrative representative to the
original continuous coordinates on the carried skeleton. -/
theorem replaceRepresentativeBuffer {p : Parameters} {rate : RateInput p}
    (index : FollowerCarryIndex p rate)
    (values : SavedScalarFamily index.2.1) :
    replaceBufferScalars (sparseSkeletonBuffer index.2.2)
        (representativeValues index values) =
      FollowerDownJointMeasurability.bufferFromSkeletonAndScalars index.2.2 values := by
  classical
  apply List.ext_get
  · simp [sparseSkeletonBuffer, FollowerDownJointMeasurability.bufferFromSkeletonAndScalars,
      replaceBufferScalars]
  · intro j hj₁ hj₂
    have hj₁' : j < (sparseSkeletonBuffer index.2.2).length := by
      simpa [replaceBufferScalars] using hj₁
    have hj₂' : j < index.2.1 := by
      simpa [FollowerDownJointMeasurability.bufferFromSkeletonAndScalars] using hj₂
    have hindex : Fin.cast (sparseSkeletonBuffer_length index.2.2)
        (⟨j, hj₁'⟩ : Fin (sparseSkeletonBuffer index.2.2).length) =
          (⟨j, hj₂'⟩ : Fin index.2.1) := by
      apply Fin.ext
      rfl
    have hvalues := congrArg values hindex
    have hcomponents :
        (values (Fin.cast (sparseSkeletonBuffer_length index.2.2)
          (⟨j, hj₁'⟩ : Fin (sparseSkeletonBuffer index.2.2).length))).1 =
            (values (⟨j, hj₂'⟩ : Fin index.2.1)).1 ∧
          (values (Fin.cast (sparseSkeletonBuffer_length index.2.2)
            (⟨j, hj₁'⟩ : Fin (sparseSkeletonBuffer index.2.2).length))).2 =
            (values (⟨j, hj₂'⟩ : Fin index.2.1)).2 :=
      ⟨congrArg Prod.fst hvalues, congrArg Prod.snd hvalues⟩
    simpa [sparseSkeletonBuffer,
      FollowerDownJointMeasurability.bufferFromSkeletonAndScalars,
      replaceBufferScalars, representativeValues] using hcomponents

/-- Reconstruct a state at an arbitrary index and its original scalar family. -/
def reconstructCarriedState {p : Parameters} {rate : RateInput p}
    (index : FollowerCarryIndex p rate) (values : SavedScalarFamily index.2.1) :
    State p rate.eta :=
  followerStateOfCode rate index.1
    (FollowerDownJointMeasurability.bufferFromSkeletonAndScalars index.2.2 values)

/-- Fixed-index input coordinates. The active-time subtype is genuine, and
row, feedback index, and played arm remain independent inputs. -/
abbrev ObservationFiber (p : Parameters) (rate : RateInput p)
    (activation : Activation p) (index : FollowerCarryIndex p rate) :=
  SavedScalarFamily index.2.1 ×
    (((CompleteRow p × ActiveTime p activation) × Fin (D p + 1)) × Fin p.K)

/-- Countable measurable disjoint union of all register/skeleton fibers and
their exact finite saved-scalar products with the entire observation inputs. -/
abbrev ObservationInput (p : Parameters) (rate : RateInput p)
    (activation : Activation p) :=
  Sigma fun index : FollowerCarryIndex p rate => ObservationFiber p rate activation index

/-- The countable code retains which accepted component handled this status
branch and every component failure or successful discrete output. -/
inductive ObservationResultCode (p : Parameters) (rate : RateInput p) where
  | unoccupied (code : FollowerLoggingDownMeasurability.LoggingDownResultCode p rate)
  | occupied (code : FollowerServiceMeasurability.OccupiedRoundCode p rate)
  deriving Countable

instance observationResultCodeMeasurableSpace (p : Parameters) (rate : RateInput p) :
    MeasurableSpace (ObservationResultCode p rate) := ⊤

def fiberValues {p : Parameters} {rate : RateInput p} {activation : Activation p}
    {index : FollowerCarryIndex p rate} (x : ObservationFiber p rate activation index) := x.1

def fiberRow {p : Parameters} {rate : RateInput p} {activation : Activation p}
    {index : FollowerCarryIndex p rate} (x : ObservationFiber p rate activation index) :=
  x.2.1.1.1

def fiberTime {p : Parameters} {rate : RateInput p} {activation : Activation p}
    {index : FollowerCarryIndex p rate} (x : ObservationFiber p rate activation index) :=
  x.2.1.1.2

def fiberFeedbackIndex {p : Parameters} {rate : RateInput p} {activation : Activation p}
    {index : FollowerCarryIndex p rate} (x : ObservationFiber p rate activation index) :=
  x.2.1.2

def fiberPlayedArm {p : Parameters} {rate : RateInput p} {activation : Activation p}
    {index : FollowerCarryIndex p rate} (x : ObservationFiber p rate activation index) := x.2.2

/-- The carried-state component of the full disjoint-union observation input. -/
def observationInputCarriedState {p : Parameters} {rate : RateInput p}
    {activation : Activation p} (x : ObservationInput p rate activation) :
    CarriedState p rate := ⟨x.1, fiberValues x.2⟩

def observationInputRow {p : Parameters} {rate : RateInput p} {activation : Activation p}
    (x : ObservationInput p rate activation) : CompleteRow p := fiberRow x.2

def observationInputTime {p : Parameters} {rate : RateInput p} {activation : Activation p}
    (x : ObservationInput p rate activation) : ActiveTime p activation := fiberTime x.2

def observationInputFeedbackIndex {p : Parameters} {rate : RateInput p}
    {activation : Activation p} (x : ObservationInput p rate activation) : Fin (D p + 1) :=
  fiberFeedbackIndex x.2

def observationInputPlayedArm {p : Parameters} {rate : RateInput p}
    {activation : Activation p} (x : ObservationInput p rate activation) : Fin p.K :=
  fiberPlayedArm x.2

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

/-- Each summand has its original measurable structure, including its images.
No discreteness of the continuous summand is used. -/
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

/-- Distributing a product into a countable measurable disjoint union is
measurable. Countability is used for the union of the measurable fiber images. -/
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

/-- Literal input assembly: use the carried state's own Sigma index, its
original scalar family, and the four separately supplied observation values. -/
def assembleObservationInput {p : Parameters} {rate : RateInput p}
    {activation : Activation p} (c : CarriedState p rate)
    (row : CompleteRow p) (time : ActiveTime p activation)
    (feedback : Fin (D p + 1)) (arm : Fin p.K) : ObservationInput p rate activation :=
  ⟨c.1, (c.2, (((row, time), feedback), arm))⟩

@[simp] theorem observationInputCarriedState_assemble {p : Parameters} {rate : RateInput p}
    {activation : Activation p} (c : CarriedState p rate)
    (row : CompleteRow p) (time : ActiveTime p activation)
    (feedback : Fin (D p + 1)) (arm : Fin p.K) :
    observationInputCarriedState (assembleObservationInput c row time feedback arm) = c := rfl

@[simp] theorem observationInputRow_assemble {p : Parameters} {rate : RateInput p}
    {activation : Activation p} (c : CarriedState p rate)
    (row : CompleteRow p) (time : ActiveTime p activation)
    (feedback : Fin (D p + 1)) (arm : Fin p.K) :
    observationInputRow (assembleObservationInput c row time feedback arm) = row := rfl

@[simp] theorem observationInputTime_assemble {p : Parameters} {rate : RateInput p}
    {activation : Activation p} (c : CarriedState p rate)
    (row : CompleteRow p) (time : ActiveTime p activation)
    (feedback : Fin (D p + 1)) (arm : Fin p.K) :
    observationInputTime (assembleObservationInput c row time feedback arm) = time := rfl

@[simp] theorem observationInputFeedbackIndex_assemble {p : Parameters} {rate : RateInput p}
    {activation : Activation p} (c : CarriedState p rate)
    (row : CompleteRow p) (time : ActiveTime p activation)
    (feedback : Fin (D p + 1)) (arm : Fin p.K) :
    observationInputFeedbackIndex (assembleObservationInput c row time feedback arm) =
      feedback := rfl

@[simp] theorem observationInputPlayedArm_assemble {p : Parameters} {rate : RateInput p}
    {activation : Activation p} (c : CarriedState p rate)
    (row : CompleteRow p) (time : ActiveTime p activation)
    (feedback : Fin (D p + 1)) (arm : Fin p.K) :
    observationInputPlayedArm (assembleObservationInput c row time feedback arm) = arm := rfl

@[simp] theorem assembleObservationInput_components {p : Parameters} {rate : RateInput p}
    {activation : Activation p} (x : ObservationInput p rate activation) :
    assembleObservationInput (observationInputCarriedState x) (observationInputRow x)
      (observationInputTime x) (observationInputFeedbackIndex x)
      (observationInputPlayedArm x) = x := rfl

/-- The missing arbitrary-base lift, with exactly five separate measurability
premises. The carried scalar fibers and complete rows retain their original
measurable structures. -/
theorem measurable_assembleObservationInput {p : Parameters}
    {rate : RateInput p} {activation : Activation p}
    {Ω : Type*} [MeasurableSpace Ω]
    (c : Ω → CarriedState p rate) (row : Ω → CompleteRow p)
    (time : Ω → ActiveTime p activation) (feedback : Ω → Fin (D p + 1))
    (arm : Ω → Fin p.K)
    (hc : Measurable c) (hrow : Measurable row) (htime : Measurable time)
    (hfeedback : Measurable feedback) (harm : Measurable arm) :
    Measurable (fun ω => assembleObservationInput (c ω) (row ω) (time ω)
      (feedback ω) (arm ω)) :=
  measurable_assembleSigmaProduct.comp
    (hc.prodMk (((hrow.prodMk htime).prodMk hfeedback).prodMk harm))

theorem measurable_observationInputCarriedState {p : Parameters} (rate : RateInput p)
    (activation : Activation p) :
    Measurable (observationInputCarriedState : ObservationInput p rate activation →
      CarriedState p rate) := by
  apply measurable_of_sigma_sections
  intro index
  change Measurable (fun x : ObservationFiber p rate activation index =>
    (⟨index, fiberValues x⟩ : CarriedState p rate))
  exact (measurable_sigmaMk index).comp measurable_fst

theorem measurable_observationInputRow {p : Parameters} (rate : RateInput p)
    (activation : Activation p) :
    Measurable (observationInputRow : ObservationInput p rate activation → CompleteRow p) := by
  apply measurable_of_sigma_sections
  intro index
  exact measurable_fst.comp (measurable_fst.comp (measurable_fst.comp measurable_snd))

theorem measurable_observationInputTime {p : Parameters} (rate : RateInput p)
    (activation : Activation p) :
    Measurable (observationInputTime : ObservationInput p rate activation →
      ActiveTime p activation) := by
  apply measurable_of_sigma_sections
  intro index
  exact measurable_snd.comp (measurable_fst.comp (measurable_fst.comp measurable_snd))

theorem measurable_observationInputFeedbackIndex {p : Parameters} (rate : RateInput p)
    (activation : Activation p) :
    Measurable (observationInputFeedbackIndex : ObservationInput p rate activation →
      Fin (D p + 1)) := by
  apply measurable_of_sigma_sections
  intro index
  change Measurable (fun x : ObservationFiber p rate activation index => x.2.1.2)
  exact measurable_snd.comp (measurable_fst.comp measurable_snd)

theorem measurable_observationInputPlayedArm {p : Parameters} (rate : RateInput p)
    (activation : Activation p) :
    Measurable (observationInputPlayedArm : ObservationInput p rate activation → Fin p.K) := by
  apply measurable_of_sigma_sections
  intro index
  change Measurable (fun x : ObservationFiber p rate activation index => x.2.2)
  exact measurable_snd.comp measurable_snd

theorem measurable_observationInputComponents {p : Parameters} (rate : RateInput p)
    (activation : Activation p) :
    Measurable (fun x : ObservationInput p rate activation =>
      (observationInputCarriedState x,
        (((observationInputRow x, observationInputTime x),
          observationInputFeedbackIndex x), observationInputPlayedArm x))) := by
  exact (measurable_observationInputCarriedState rate activation).prodMk
    ((((measurable_observationInputRow rate activation).prodMk
      (measurable_observationInputTime rate activation)).prodMk
      (measurable_observationInputFeedbackIndex rate activation)).prodMk
        (measurable_observationInputPlayedArm rate activation))

theorem measurable_observationInputComponents_comp {p : Parameters}
    (rate : RateInput p) (activation : Activation p)
    {Ω : Type*} [MeasurableSpace Ω]
    (inputs : Ω → ObservationInput p rate activation) (hinputs : Measurable inputs) :
    Measurable (fun ω =>
      (observationInputCarriedState (inputs ω),
        (((observationInputRow (inputs ω), observationInputTime (inputs ω)),
          observationInputFeedbackIndex (inputs ω)), observationInputPlayedArm (inputs ω)))) :=
  (measurable_observationInputComponents rate activation).comp hinputs

/-- Exact measurable equivalence with the separate carried and observation
components; both inverse laws hold on the entire carrier. -/
def observationInputComponentsEquiv {p : Parameters} (rate : RateInput p)
    (activation : Activation p) :
    ObservationInput p rate activation ≃ᵐ
      CarriedState p rate ×
        (((CompleteRow p × ActiveTime p activation) × Fin (D p + 1)) × Fin p.K) where
  toFun x := (observationInputCarriedState x,
    (((observationInputRow x, observationInputTime x),
      observationInputFeedbackIndex x), observationInputPlayedArm x))
  invFun x := assembleObservationInput x.1 x.2.1.1.1 x.2.1.1.2 x.2.1.2 x.2.2
  left_inv := assembleObservationInput_components
  right_inv _ := rfl
  measurable_toFun := measurable_observationInputComponents rate activation
  measurable_invFun := measurable_assembleObservationInput _ _ _ _ _ measurable_fst
    (measurable_fst.comp (measurable_fst.comp (measurable_fst.comp measurable_snd)))
    (measurable_snd.comp (measurable_fst.comp (measurable_fst.comp measurable_snd)))
    (measurable_snd.comp (measurable_fst.comp measurable_snd))
    (measurable_snd.comp measurable_snd)

def loggingInputOfFiber {p : Parameters} {rate : RateInput p}
    {activation : Activation p} {index : FollowerCarryIndex p rate}
    (x : ObservationFiber p rate activation index) :
    FollowerLoggingDownMeasurability.LoggingDownInput p rate activation
      (representativeState rate index) :=
  ((((fiberRow x, fiberTime x), (fiberFeedbackIndex x, fiberPlayedArm x)),
    representativeValues index (fiberValues x)))

def serviceInputOfFiber {p : Parameters} {rate : RateInput p}
    {activation : Activation p} {index : FollowerCarryIndex p rate}
    (x : ObservationFiber p rate activation index) :
    FollowerServiceMeasurability.JointInput p (representativeState rate index).buffer.length :=
  (((fiberRow x, (fiberTime x).1), fiberFeedbackIndex x),
    representativeValues index (fiberValues x))

def observationResultCodeOnFiber {p : Parameters} (rate : RateInput p)
    (i : Fin (p.m - 1)) (activation : Activation p)
    (index : FollowerCarryIndex p rate)
    (x : ObservationFiber p rate activation index) : ObservationResultCode p rate := by
  classical
  let state := representativeState rate index
  if hstatus : state.status = .unoccupied then
    exact .unoccupied
      (FollowerLoggingDownMeasurability.recordOrServiceThenDownCode i rate activation
        state hstatus (loggingInputOfFiber x))
  else
    exact .occupied
      (FollowerServiceMeasurability.occupiedRoundCodeOfServiceCode rate
        (FollowerServiceMeasurability.checkedServiceCodeAtJoint rate i activation state
          (serviceInputOfFiber x)))

def observationResultCode {p : Parameters} (rate : RateInput p)
    (i : Fin (p.m - 1)) (activation : Activation p)
    (x : ObservationInput p rate activation) : ObservationResultCode p rate :=
  observationResultCodeOnFiber rate i activation x.1 x.2

def decodeObservationResultCode {p : Parameters} (rate : RateInput p)
    (i : Fin (p.m - 1)) (activation : Activation p)
    (x : ObservationInput p rate activation) (code : ObservationResultCode p rate) :
    Except RoundFailure (State p rate.eta) :=
  match code with
  | .unoccupied code =>
      FollowerLoggingDownMeasurability.reconstructLoggingDownResult i rate activation
        (representativeState rate x.1) (loggingInputOfFiber x.2) code
  | .occupied code =>
      FollowerServiceMeasurability.reconstructOccupiedRoundCode rate
        (FollowerDownJointMeasurability.bufferFromSkeletonAndScalars x.1.2.2
          (fiberValues x.2)) code

theorem adaptedRepresentativeState_eq_reconstruct {p : Parameters} {rate : RateInput p}
    (index : FollowerCarryIndex p rate) (values : SavedScalarFamily index.2.1) :
    FollowerDownMeasurability.adaptedInputState rate (representativeState rate index)
      (representativeValues index values) =
      reconstructCarriedState index values := by
  have hb := replaceRepresentativeBuffer index values
  cases index with
  | mk registers skeleton =>
    cases skeleton with
    | mk n entries =>
      simp [representativeState, reconstructCarriedState,
        FollowerDownMeasurability.adaptedInputState, hb,
        FollowerDownMeasurability.followerStateOfCode]

theorem decode_observationResultCode_eq_actual {p : Parameters}
    (rate : RateInput p) (i : Fin (p.m - 1)) (activation : Activation p)
    (x : ObservationInput p rate activation) :
    decodeObservationResultCode rate i activation x (observationResultCode rate i activation x) =
      DeclaredFollowerLocalRound.recordOrServiceThenDown rate i
        (fiberRow x.2) activation (fiberTime x.2).1 (fiberTime x.2).2
        (fiberPlayedArm x.2)
        (FollowerDownMeasurability.feedbackAtGrid p (fiberFeedbackIndex x.2))
        (reconstructCarriedState x.1 (fiberValues x.2)) := by
  cases x with
  | mk index fiber =>
    let state := representativeState rate index
    by_cases hstatus : (representativeState rate index).status = .unoccupied
    · have hadapter := adaptedRepresentativeState_eq_reconstruct index (fiberValues fiber)
      simp only [observationResultCode, observationResultCodeOnFiber,
        dite_eq_left hstatus, decodeObservationResultCode]
      calc
        FollowerLoggingDownMeasurability.reconstructLoggingDownResult i rate activation state
            (loggingInputOfFiber fiber)
            (FollowerLoggingDownMeasurability.recordOrServiceThenDownCode i rate activation
              state hstatus (loggingInputOfFiber fiber)) =
          DeclaredFollowerLocalRound.recordOrServiceThenDown rate i (fiberRow fiber)
            activation (fiberTime fiber).1 (fiberTime fiber).2 (fiberPlayedArm fiber)
            (FollowerDownMeasurability.feedbackAtGrid p (fiberFeedbackIndex fiber))
            (FollowerDownMeasurability.adaptedInputState rate state
              (representativeValues index (fiberValues fiber))) :=
          FollowerLoggingDownMeasurability.reconstruct_recordOrServiceThenDownCode
            i rate activation state hstatus (loggingInputOfFiber fiber)
        _ = _ := by rw [hadapter]
    · let adapted := FollowerDownMeasurability.adaptedInputState rate state
        (representativeValues index (fiberValues fiber))
      have hadapter : adapted = reconstructCarriedState index (fiberValues fiber) :=
        adaptedRepresentativeState_eq_reconstruct index (fiberValues fiber)
      have hbuffer : adapted.buffer =
          FollowerDownJointMeasurability.bufferFromSkeletonAndScalars index.2.2
            (fiberValues fiber) := by
        rw [hadapter]
        rfl
      simp only [observationResultCode, observationResultCodeOnFiber, dite_eq_right hstatus,
        decodeObservationResultCode]
      have hservice := FollowerServiceMeasurability.reconstruct_occupied_recordOrServiceThenDown
        rate i (fiberRow fiber) activation (fiberTime fiber).1 (fiberTime fiber).2
        (fiberPlayedArm fiber)
        (FollowerDownMeasurability.feedbackAtGrid p (fiberFeedbackIndex fiber)) adapted
        (by simpa [adapted, FollowerDownMeasurability.adaptedInputState] using hstatus)
      have hcode :
          FollowerServiceMeasurability.occupiedRoundCodeOfServiceCode rate
              (FollowerServiceMeasurability.checkedServiceCodeAtJoint rate i activation state
                (serviceInputOfFiber fiber)) =
            FollowerServiceMeasurability.occupiedRoundCodeOfServiceCode rate
              (FollowerServiceMeasurability.encodeServiceResult rate
                (ActiveFollowerQueueOperation.checkedService rate.eta
                  (FollowerServiceMeasurability.rateSourceCap_forService rate) rate.n rate.n_scale
                  i (fiberRow fiber) activation (fiberTime fiber).1
                  (FollowerDownMeasurability.feedbackAtGrid p (fiberFeedbackIndex fiber)) adapted)) := by
        rfl
      calc
        FollowerServiceMeasurability.reconstructOccupiedRoundCode rate
            (FollowerDownJointMeasurability.bufferFromSkeletonAndScalars index.2.2
              (fiberValues fiber))
            (FollowerServiceMeasurability.occupiedRoundCodeOfServiceCode rate
              (FollowerServiceMeasurability.checkedServiceCodeAtJoint rate i activation state
                (serviceInputOfFiber fiber))) =
          FollowerServiceMeasurability.reconstructOccupiedRoundCode rate adapted.buffer
            (FollowerServiceMeasurability.occupiedRoundCodeOfServiceCode rate
              (FollowerServiceMeasurability.encodeServiceResult rate
                (ActiveFollowerQueueOperation.checkedService rate.eta
                  (FollowerServiceMeasurability.rateSourceCap_forService rate) rate.n
                  rate.n_scale i (fiberRow fiber) activation (fiberTime fiber).1
                  (FollowerDownMeasurability.feedbackAtGrid p (fiberFeedbackIndex fiber))
                  adapted))) := by rw [hcode, hbuffer]
        _ = DeclaredFollowerLocalRound.recordOrServiceThenDown rate i (fiberRow fiber)
            activation (fiberTime fiber).1 (fiberTime fiber).2 (fiberPlayedArm fiber)
            (FollowerDownMeasurability.feedbackAtGrid p (fiberFeedbackIndex fiber)) adapted :=
          hservice
        _ = _ := by rw [hadapter]

private theorem measurable_loggingInputOfFiber {p : Parameters} {rate : RateInput p}
    {activation : Activation p} {index : FollowerCarryIndex p rate} :
    Measurable (loggingInputOfFiber (p := p) (rate := rate)
      (activation := activation) (index := index)) := by
  have hvalues : Measurable (fun x : ObservationFiber p rate activation index =>
      representativeValues index (fiberValues x)) := by
    apply measurable_pi_iff.mpr
    intro j
    change Measurable (fun x : ObservationFiber p rate activation index =>
      fiberValues x (Fin.cast (sparseSkeletonBuffer_length index.2.2) j))
    exact (measurable_pi_apply (Fin.cast (sparseSkeletonBuffer_length index.2.2) j)).comp
      measurable_fst
  have hrow : Measurable (fiberRow (p := p) (rate := rate)
      (activation := activation) (index := index)) :=
    measurable_fst.comp (measurable_fst.comp (measurable_fst.comp measurable_snd))
  have hactive : Measurable (fiberTime (p := p) (rate := rate)
      (activation := activation) (index := index)) :=
    measurable_snd.comp (measurable_fst.comp (measurable_fst.comp measurable_snd))
  have htime : Measurable (fun x : ObservationFiber p rate activation index =>
      (fiberTime x).1) := measurable_subtype_coe.comp hactive
  have hfeedback : Measurable (fiberFeedbackIndex (p := p) (rate := rate)
      (activation := activation) (index := index)) := by
    change Measurable (fun x : ObservationFiber p rate activation index => x.2.1.2)
    exact measurable_snd.comp (measurable_fst.comp measurable_snd)
  have harm : Measurable (fiberPlayedArm (p := p) (rate := rate)
      (activation := activation) (index := index)) := by
    change Measurable (fun x : ObservationFiber p rate activation index => x.2.2)
    exact measurable_snd.comp measurable_snd
  have hround : Measurable (fun x : ObservationFiber p rate activation index =>
      (((fiberRow x, fiberTime x), (fiberFeedbackIndex x, fiberPlayedArm x)))) := by
    exact (hrow.prodMk hactive).prodMk (hfeedback.prodMk harm)
  exact hround.prodMk hvalues

private theorem measurable_representativeValues {p : Parameters} {rate : RateInput p}
    {activation : Activation p} {index : FollowerCarryIndex p rate} :
    Measurable (fun x : ObservationFiber p rate activation index =>
      representativeValues index (fiberValues x)) := by
  apply measurable_pi_iff.mpr
  intro j
  change Measurable (fun x : ObservationFiber p rate activation index =>
      fiberValues x (Fin.cast (sparseSkeletonBuffer_length index.2.2) j))
  exact (measurable_pi_apply (Fin.cast (sparseSkeletonBuffer_length index.2.2) j)).comp
    measurable_fst

private theorem measurable_serviceInputOfFiber {p : Parameters} {rate : RateInput p}
    {activation : Activation p} {index : FollowerCarryIndex p rate} :
    Measurable (serviceInputOfFiber (p := p) (rate := rate)
      (activation := activation) (index := index)) := by
  have hvalues := measurable_representativeValues (p := p) (rate := rate)
    (activation := activation) (index := index)
  have hrow : Measurable (fiberRow (p := p) (rate := rate)
      (activation := activation) (index := index)) :=
    measurable_fst.comp (measurable_fst.comp (measurable_fst.comp measurable_snd))
  have hactive : Measurable (fiberTime (p := p) (rate := rate)
      (activation := activation) (index := index)) :=
    measurable_snd.comp (measurable_fst.comp (measurable_fst.comp measurable_snd))
  have htime : Measurable (fun x : ObservationFiber p rate activation index =>
      (fiberTime x).1) := measurable_subtype_coe.comp hactive
  have hfeedback : Measurable (fiberFeedbackIndex (p := p) (rate := rate)
      (activation := activation) (index := index)) := by
    change Measurable (fun x : ObservationFiber p rate activation index => x.2.1.2)
    exact measurable_snd.comp (measurable_fst.comp measurable_snd)
  exact ((hrow.prodMk htime).prodMk hfeedback).prodMk hvalues

theorem measurable_observationResultCodeOnFiber {p : Parameters} (rate : RateInput p)
    (i : Fin (p.m - 1)) (activation : Activation p)
    (index : FollowerCarryIndex p rate) :
    Measurable (observationResultCodeOnFiber rate i activation index) := by
  classical
  by_cases hstatus : (representativeState rate index).status = .unoccupied
  · have hbranch : observationResultCodeOnFiber rate i activation index =
        fun x => ObservationResultCode.unoccupied
          (FollowerLoggingDownMeasurability.recordOrServiceThenDownCode i rate activation
            (representativeState rate index) hstatus (loggingInputOfFiber x)) := by
      funext x
      simp [observationResultCodeOnFiber, hstatus]
    rw [hbranch]
    have htag : Measurable (fun code : FollowerLoggingDownMeasurability.LoggingDownResultCode p rate =>
        ObservationResultCode.unoccupied code) := measurable_of_countable _
    exact htag.comp ((FollowerLoggingDownMeasurability.measurable_recordOrServiceThenDownCode
      i rate activation (representativeState rate index) hstatus).comp
        measurable_loggingInputOfFiber)
  · have hbranch : observationResultCodeOnFiber rate i activation index =
        fun x => ObservationResultCode.occupied
          (FollowerServiceMeasurability.occupiedRoundCodeOfServiceCode rate
            (FollowerServiceMeasurability.checkedServiceCodeAtJoint rate i activation
              (representativeState rate index) (serviceInputOfFiber x))) := by
      funext x
      simp [observationResultCodeOnFiber, hstatus]
    rw [hbranch]
    have htag : Measurable (fun code : FollowerServiceMeasurability.OccupiedRoundCode p rate =>
        ObservationResultCode.occupied code) := measurable_of_countable _
    have hfactor : Measurable (fun x : ObservationFiber p rate activation index =>
        FollowerServiceMeasurability.occupiedRoundCodeOfServiceCode rate
          (FollowerServiceMeasurability.checkedServiceCodeAtJoint rate i activation
            (representativeState rate index)
            (serviceInputOfFiber x))) := by
      exact (FollowerServiceMeasurability.measurable_occupiedRoundCodeAtJoint
        rate i activation (representativeState rate index)).comp measurable_serviceInputOfFiber
    exact htag.comp hfactor

theorem measurable_observationResultCode {p : Parameters} (rate : RateInput p)
    (i : Fin (p.m - 1)) (activation : Activation p) :
    Measurable (observationResultCode rate i activation) := by
  classical
  apply FollowerDownMeasurability.measurable_of_countable_fibers
  intro target
  change MeasurableSet[
    (⨅ index, (inferInstance : MeasurableSpace
      (ObservationFiber p rate activation index)).map (Sigma.mk index))]
    {x : ObservationInput p rate activation | observationResultCode rate i activation x = target}
  rw [MeasurableSpace.measurableSet_iInf]
  intro index
  rw [MeasurableSpace.map_def]
  change MeasurableSet
    {x : ObservationFiber p rate activation index |
      observationResultCodeOnFiber rate i activation index x = target}
  exact (measurable_observationResultCodeOnFiber rate i activation index)
    (measurableSet_singleton target)

theorem measurable_observationResultCode_comp {p : Parameters} (rate : RateInput p)
    (i : Fin (p.m - 1)) (activation : Activation p)
    {Ω : Type*} [MeasurableSpace Ω]
    (inputs : Ω → ObservationInput p rate activation) (hinputs : Measurable inputs) :
    Measurable (fun ω => observationResultCode rate i activation (inputs ω)) :=
  (measurable_observationResultCode rate i activation).comp hinputs

/-- Arbitrary-base observation code from the five separate maps alone. -/
theorem measurable_observationResultCode_atComponents {p : Parameters}
    (rate : RateInput p) (i : Fin (p.m - 1)) (activation : Activation p)
    {Ω : Type*} [MeasurableSpace Ω]
    (c : Ω → CarriedState p rate) (row : Ω → CompleteRow p)
    (time : Ω → ActiveTime p activation) (feedback : Ω → Fin (D p + 1))
    (arm : Ω → Fin p.K)
    (hc : Measurable c) (hrow : Measurable row) (htime : Measurable time)
    (hfeedback : Measurable feedback) (harm : Measurable arm) :
    Measurable (fun ω => observationResultCode rate i activation
      (assembleObservationInput (c ω) (row ω) (time ω) (feedback ω) (arm ω))) :=
  (measurable_observationResultCode rate i activation).comp
    (measurable_assembleObservationInput c row time feedback arm hc hrow htime hfeedback harm)

/-- Decoding the separately assembled inputs is the entire existing operation,
including every failure and every continuous output coordinate. -/
theorem decode_observationResultCode_atComponents_eq_actual {p : Parameters}
    (rate : RateInput p) (i : Fin (p.m - 1)) (activation : Activation p)
    (c : CarriedState p rate) (row : CompleteRow p) (time : ActiveTime p activation)
    (feedback : Fin (D p + 1)) (arm : Fin p.K) :
    decodeObservationResultCode rate i activation
        (assembleObservationInput c row time feedback arm)
        (observationResultCode rate i activation
          (assembleObservationInput c row time feedback arm)) =
      DeclaredFollowerLocalRound.recordOrServiceThenDown rate i row activation
        time.1 time.2 arm (FollowerDownMeasurability.feedbackAtGrid p feedback)
        (reconstructCarriedState c.1 c.2) :=
  decode_observationResultCode_eq_actual rate i activation
    (assembleObservationInput c row time feedback arm)

/-- Discrete output-state projection for the complete DOWN result code. -/
def downOutputStateCode {p : Parameters} {rate : RateInput p}
    (code : FollowerDownMeasurability.LocalDownResultCode p rate) :
    Option (FollowerDownMeasurability.FollowerStateCode p rate) :=
  match code with
  | .skipped before _ => some before
  | .inputFailure _ _ => none
  | .decodeOrParseRejected _ after _ => some after
  | .parsedButUnaccepted _ after _ _ => some after
  | .outputFailure _ _ => none
  | .accepted _ after _ _ _ _ _ => some after

/-- Discrete output-state projection for both actual observation branches. -/
def observationOutputStateCode {p : Parameters} {rate : RateInput p}
    (code : ObservationResultCode p rate) :
    Option (FollowerDownMeasurability.FollowerStateCode p rate) :=
  match code with
  | .unoccupied (.loggingFailure _) => none
  | .unoccupied (.down result) => downOutputStateCode result
  | .unoccupied (.logged state _) => some state
  | .occupied .serviceFailure => none
  | .occupied (.success _ _ state) => some state

instance observationOutputStateCodeMeasurableSpace {p : Parameters}
    {rate : RateInput p} : MeasurableSpace
      (Option (FollowerDownMeasurability.FollowerStateCode p rate)) := ⊤

/-- A code is a failure exactly when its discrete successful-state projection
is absent. Failure tags and reasons remain in `ObservationResultCode`. -/
def observationFailed {p : Parameters} {rate : RateInput p}
    (code : ObservationResultCode p rate) : Bool :=
  decide (observationOutputStateCode code = none)

def observationSucceeded {p : Parameters} {rate : RateInput p}
    (code : ObservationResultCode p rate) : Bool := !observationFailed code

/-- Lossless output-buffer recipe, retaining every original scalar field and
the exact current append or accepted-DOWN clear action. -/
def observationOutputBuffer {p : Parameters} (rate : RateInput p)
    (i : Fin (p.m - 1)) (activation : Activation p)
    (x : ObservationInput p rate activation) (code : ObservationResultCode p rate) :
    Option (List (SparseCalendarRecord p.K)) :=
  (decodeObservationResultCode rate i activation x code).toOption.map
    (fun state => state.buffer)

theorem decode_observationOutputBuffer {p : Parameters} (rate : RateInput p)
    (i : Fin (p.m - 1)) (activation : Activation p)
    (x : ObservationInput p rate activation) (code : ObservationResultCode p rate) :
    (decodeObservationResultCode rate i activation x code).toOption.map
      (fun state => state.buffer) = observationOutputBuffer rate i activation x code := rfl

theorem observationOutputBuffer_eq_actual {p : Parameters} (rate : RateInput p)
    (i : Fin (p.m - 1)) (activation : Activation p)
    (x : ObservationInput p rate activation) :
    observationOutputBuffer rate i activation x
        (observationResultCode rate i activation x) =
      (DeclaredFollowerLocalRound.recordOrServiceThenDown rate i
        (fiberRow x.2) activation (fiberTime x.2).1 (fiberTime x.2).2
        (fiberPlayedArm x.2)
        (FollowerDownMeasurability.feedbackAtGrid p (fiberFeedbackIndex x.2))
        (reconstructCarriedState x.1 (fiberValues x.2))).toOption.map
          (fun state => state.buffer) := by
  rw [← decode_observationOutputBuffer, decode_observationResultCode_eq_actual]

theorem measurable_observationOutputStateCode {p : Parameters} (rate : RateInput p) :
    Measurable (observationOutputStateCode : ObservationResultCode p rate →
      Option (FollowerDownMeasurability.FollowerStateCode p rate)) :=
  measurable_of_countable _

theorem measurable_observationFailed {p : Parameters} (rate : RateInput p) :
    Measurable (observationFailed : ObservationResultCode p rate → Bool) :=
  measurable_of_countable _

theorem measurable_observationSucceeded {p : Parameters} (rate : RateInput p) :
    Measurable (observationSucceeded : ObservationResultCode p rate → Bool) :=
  measurable_of_countable _

theorem measurable_observationOutputStateCode_comp {p : Parameters}
    (rate : RateInput p) (i : Fin (p.m - 1)) (activation : Activation p)
    {Ω : Type*} [MeasurableSpace Ω]
    (inputs : Ω → ObservationInput p rate activation) (hinputs : Measurable inputs) :
    Measurable (fun ω => observationOutputStateCode
      (observationResultCode rate i activation (inputs ω))) :=
  (measurable_observationOutputStateCode rate).comp
    (measurable_observationResultCode_comp rate i activation inputs hinputs)

theorem measurable_observationFailed_comp {p : Parameters}
    (rate : RateInput p) (i : Fin (p.m - 1)) (activation : Activation p)
    {Ω : Type*} [MeasurableSpace Ω]
    (inputs : Ω → ObservationInput p rate activation) (hinputs : Measurable inputs) :
    Measurable (fun ω => observationFailed
      (observationResultCode rate i activation (inputs ω))) :=
  (measurable_observationFailed rate).comp
    (measurable_observationResultCode_comp rate i activation inputs hinputs)

theorem measurable_observationSucceeded_comp {p : Parameters}
    (rate : RateInput p) (i : Fin (p.m - 1)) (activation : Activation p)
    {Ω : Type*} [MeasurableSpace Ω]
    (inputs : Ω → ObservationInput p rate activation) (hinputs : Measurable inputs) :
    Measurable (fun ω => observationSucceeded
      (observationResultCode rate i activation (inputs ω))) :=
  (measurable_observationSucceeded rate).comp
    (measurable_observationResultCode_comp rate i activation inputs hinputs)

/-- Separate-input version of the full successful discrete state projection. -/
theorem measurable_observationOutputStateCode_atComponents {p : Parameters}
    (rate : RateInput p) (i : Fin (p.m - 1)) (activation : Activation p)
    {Ω : Type*} [MeasurableSpace Ω]
    (c : Ω → CarriedState p rate) (row : Ω → CompleteRow p)
    (time : Ω → ActiveTime p activation) (feedback : Ω → Fin (D p + 1))
    (arm : Ω → Fin p.K)
    (hc : Measurable c) (hrow : Measurable row) (htime : Measurable time)
    (hfeedback : Measurable feedback) (harm : Measurable arm) :
    Measurable (fun ω => observationOutputStateCode
      (observationResultCode rate i activation
        (assembleObservationInput (c ω) (row ω) (time ω) (feedback ω) (arm ω)))) :=
  (measurable_observationOutputStateCode rate).comp
    (measurable_observationResultCode_atComponents rate i activation
      c row time feedback arm hc hrow htime hfeedback harm)

theorem measurable_observationFailed_atComponents {p : Parameters}
    (rate : RateInput p) (i : Fin (p.m - 1)) (activation : Activation p)
    {Ω : Type*} [MeasurableSpace Ω]
    (c : Ω → CarriedState p rate) (row : Ω → CompleteRow p)
    (time : Ω → ActiveTime p activation) (feedback : Ω → Fin (D p + 1))
    (arm : Ω → Fin p.K)
    (hc : Measurable c) (hrow : Measurable row) (htime : Measurable time)
    (hfeedback : Measurable feedback) (harm : Measurable arm) :
    Measurable (fun ω => observationFailed
      (observationResultCode rate i activation
        (assembleObservationInput (c ω) (row ω) (time ω) (feedback ω) (arm ω)))) :=
  (measurable_observationFailed rate).comp
    (measurable_observationResultCode_atComponents rate i activation
      c row time feedback arm hc hrow htime hfeedback harm)

theorem measurable_observationSucceeded_atComponents {p : Parameters}
    (rate : RateInput p) (i : Fin (p.m - 1)) (activation : Activation p)
    {Ω : Type*} [MeasurableSpace Ω]
    (c : Ω → CarriedState p rate) (row : Ω → CompleteRow p)
    (time : Ω → ActiveTime p activation) (feedback : Ω → Fin (D p + 1))
    (arm : Ω → Fin p.K)
    (hc : Measurable c) (hrow : Measurable row) (htime : Measurable time)
    (hfeedback : Measurable feedback) (harm : Measurable arm) :
    Measurable (fun ω => observationSucceeded
      (observationResultCode rate i activation
        (assembleObservationInput (c ω) (row ω) (time ω) (feedback ω) (arm ω)))) :=
  (measurable_observationSucceeded rate).comp
    (measurable_observationResultCode_atComponents rate i activation
      c row time feedback arm hc hrow htime hfeedback harm)

theorem observationOutputBuffer_atComponents_eq_actual {p : Parameters}
    (rate : RateInput p) (i : Fin (p.m - 1)) (activation : Activation p)
    (c : CarriedState p rate) (row : CompleteRow p) (time : ActiveTime p activation)
    (feedback : Fin (D p + 1)) (arm : Fin p.K) :
    observationOutputBuffer rate i activation
        (assembleObservationInput c row time feedback arm)
        (observationResultCode rate i activation
          (assembleObservationInput c row time feedback arm)) =
      (DeclaredFollowerLocalRound.recordOrServiceThenDown rate i row activation
        time.1 time.2 arm (FollowerDownMeasurability.feedbackAtGrid p feedback)
        (reconstructCarriedState c.1 c.2)).toOption.map (fun state => state.buffer) :=
  observationOutputBuffer_eq_actual rate i activation
    (assembleObservationInput c row time feedback arm)

end Bandits.Support.FollowerObservationStageMeasurabilityRepair

end
