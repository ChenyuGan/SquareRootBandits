/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.FollowerReleaseFinishMeasurability
public import Bandits.Support.FollowerObservationStageMeasurabilityRepair
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Prod

/-!
# Varying-carried-state measurability for follower release and finish

This module lifts the existing finish, pending-release, and combined
release-and-finish operations over separately varying accepted carried states.
It preserves each register code, each ordered timestamp/pilot skeleton, and
each original length-indexed continuous scalar family.

Sources: sources/zip4/manuscript/06_interruptions.tex:235-296,
sources/zip4/manuscript/05_binary_transport.tex:74-124, and
sources/zip4/manuscript/appendix_a_local_protocol.tex:8-14.
These pure local operation adapters assert no physical state, input
provenance, feedback law, run, or manuscript theorem closure.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.FollowerReleaseFinishJointMeasurability

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.CompletePublicTable
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.SparseCalendarReplay
open Bandits.Support.ActiveFollowerLifecycle
open Bandits.Support.DeclaredFollowerLocalRound
open Bandits.Support.FollowerDownMeasurability
open Bandits.Support.FollowerDownJointMeasurability
open Bandits.Support.FollowerLifecycleMeasurability
open Bandits.Support.FollowerObservationStageMeasurabilityRepair
open Bandits.Support.FollowerReleaseFinishMeasurability

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ActiveFollowerDownAcceptance.RateInput
abbrev SavedScalarFamily (n : ℕ) := FollowerDownMeasurability.SavedScalarFamily n
abbrev CarriedState (p : Parameters) (rate : RateInput p) :=
  FollowerObservationStageMeasurabilityRepair.CarriedState p rate
abbrev LocalMemoryCode (p : Parameters) := FollowerLifecycleMeasurability.LocalMemoryCode p

abbrev ReleaseFinishLocalInputs (p : Parameters) :=
  LocalMemoryCode p ×
    ((CompletePublicTable.CompleteRow p × Fin p.T) × Fin (D p + 1))

abbrev ReleaseFinishFiberCoordinates (p : Parameters) (n m : ℕ) :=
  SavedScalarFamily n × (SavedScalarFamily m × ReleaseFinishLocalInputs p)

abbrev FinishRoundFiberCoordinates (p : Parameters) (n : ℕ) :=
  SavedScalarFamily n ×
    (LocalMemoryCode p × (CompletePublicTable.CompleteRow p × Fin p.T))

instance localMemoryCodeMeasurableSpace (p : Parameters) :
    MeasurableSpace (LocalMemoryCode p) := ⊤

instance localMemoryCodeMeasurableSingletonClass (p : Parameters) :
    MeasurableSingletonClass (LocalMemoryCode p) where
  measurableSet_singleton _ := MeasurableSpace.measurableSet_top

instance lifecycleFailureMeasurableSpace :
    MeasurableSpace ActiveFollowerLifecycle.LifecycleFailure := ⊤

instance lifecycleFailureMeasurableSingletonClass :
    MeasurableSingletonClass ActiveFollowerLifecycle.LifecycleFailure where
  measurableSet_singleton _ := MeasurableSpace.measurableSet_top

instance roundFailureMeasurableSpace :
    MeasurableSpace DeclaredFollowerLocalRound.RoundFailure := ⊤

instance roundFailureMeasurableSingletonClass :
    MeasurableSingletonClass DeclaredFollowerLocalRound.RoundFailure where
  measurableSet_singleton _ := MeasurableSpace.measurableSet_top

instance localMemoryMeasurableSpace (p : Parameters) :
    MeasurableSpace (ActiveFollowerLifecycle.LocalMemory p) := ⊤

instance localMemoryMeasurableSingletonClass (p : Parameters) :
    MeasurableSingletonClass (ActiveFollowerLifecycle.LocalMemory p) where
  measurableSet_singleton _ := MeasurableSpace.measurableSet_top

instance followerStatusMeasurableSpace :
    MeasurableSpace ActiveRoundActions.FollowerStatus := ⊤

private abbrev RoundFailureCode : Type :=
  Fin 2 ⊕ (PUnit ⊕ (Fin 3 ⊕
    (FollowerDownMeasurability.OutputFailureCode ⊕ (Fin 6 ⊕ Fin 6))))

private def roundFailureCode (reason : DeclaredFollowerLocalRound.RoundFailure) :
    RoundFailureCode :=
  match reason with
  | .logging reason => Sum.inl (FollowerLoggingDownMeasurability.loggingFailureCode reason)
  | .service => Sum.inr (Sum.inl PUnit.unit)
  | .downInput reason => Sum.inr (Sum.inr (Sum.inl
      (FollowerDownMeasurability.inputFailureCode reason)))
  | .downOutput reason => Sum.inr (Sum.inr (Sum.inr (Sum.inl
      (FollowerDownMeasurability.outputFailureCode reason))))
  | .release reason => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl
      (FollowerLifecycleMeasurability.lifecycleFailureCode reason)))))
  | .finish reason =>
      let code := FollowerLifecycleMeasurability.lifecycleFailureCode reason
      Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr code))))

private def roundFailureOfCode : RoundFailureCode →
    DeclaredFollowerLocalRound.RoundFailure
  | Sum.inl reason => .logging (FollowerLoggingDownMeasurability.loggingFailureOfCode reason)
  | Sum.inr (Sum.inl _) => .service
  | Sum.inr (Sum.inr (Sum.inl reason)) =>
      .downInput (FollowerDownMeasurability.inputFailureOfCode reason)
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl reason))) =>
      .downOutput (FollowerDownMeasurability.outputFailureOfCode reason)
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl reason)))) =>
      .release (FollowerLifecycleMeasurability.lifecycleFailureOfCode reason)
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr reason)))) =>
      .finish (FollowerLifecycleMeasurability.lifecycleFailureOfCode reason)

private theorem roundFailureOfCode_roundFailure (reason : DeclaredFollowerLocalRound.RoundFailure) :
    roundFailureOfCode (roundFailureCode reason) = reason := by
  cases reason <;> simp [roundFailureOfCode, roundFailureCode,
    FollowerLoggingDownMeasurability.loggingFailureOfCode_code,
    FollowerDownMeasurability.inputFailureOfCode_code,
    FollowerDownMeasurability.outputFailureOfCode_code,
    FollowerLifecycleMeasurability.lifecycleFailureOfCode_code]

private theorem roundFailureCode_injective :
    Function.Injective roundFailureCode := by
  intro x y h
  have h' := congrArg roundFailureOfCode h
  simpa only [roundFailureOfCode_roundFailure] using h'

instance roundFailureCountable : Countable DeclaredFollowerLocalRound.RoundFailure :=
  roundFailureCode_injective.countable

private def releaseAndFinishCodeAsSum {p : Parameters} {rate : RateInput p}
    (code : ReleaseAndFinishResultCode p rate) :
    DeclaredFollowerLocalRound.RoundFailure ⊕
      (FollowerDownMeasurability.FollowerStateCode p rate × LocalMemoryCode p) :=
  match code with
  | .failure reason => Sum.inl reason
  | .success state memory => Sum.inr (state, memory)

private theorem releaseAndFinishCodeAsSum_injective {p : Parameters} {rate : RateInput p} :
    Function.Injective (releaseAndFinishCodeAsSum (p := p) (rate := rate)) := by
  intro x y h
  cases x <;> cases y <;> simp_all [releaseAndFinishCodeAsSum]

instance releaseAndFinishResultCodeCountable {p : Parameters} (rate : RateInput p) :
    Countable (ReleaseAndFinishResultCode p rate) :=
  releaseAndFinishCodeAsSum_injective.countable

/-- One finish input uses the exact accepted carried state. -/
abbrev FinishRoundJointInput (p : Parameters) (rate : RateInput p) :=
  CarriedState p rate ×
    (LocalMemoryCode p × (CompletePublicTable.CompleteRow p × Fin p.T))

/-- The two-state release input keeps the choice and post-service states
independent. The memory coordinate is included for a shared local adapter;
pending release itself does not inspect it. -/
abbrev ReleaseFinishJointInput (p : Parameters) (rate : RateInput p) :=
  CarriedState p rate ×
    (CarriedState p rate ×
      (LocalMemoryCode p ×
        ((CompletePublicTable.CompleteRow p × Fin p.T) × Fin (D p + 1))))

/-- Assemble the four separately supplied finish inputs. -/
def assembleFinishRoundJointInput {p : Parameters} {rate : RateInput p}
    (state : CarriedState p rate) (memory : LocalMemoryCode p)
    (row : CompletePublicTable.CompleteRow p) (time : Fin p.T) :
    FinishRoundJointInput p rate :=
  (state, (memory, (row, time)))

/-- Assemble the independently supplied choice and post-service states and
the exact local inputs used by release or combined release and finish. -/
def assembleReleaseFinishJointInput {p : Parameters} {rate : RateInput p}
    (preChoice postService : CarriedState p rate) (memory : LocalMemoryCode p)
    (row : CompletePublicTable.CompleteRow p) (time : Fin p.T)
    (feedback : Fin (D p + 1)) : ReleaseFinishJointInput p rate :=
  (preChoice, (postService, (memory, ((row, time), feedback))))

/-- The component assembler is measurable from its separately measurable
state, memory, row, and time maps. -/
theorem measurable_assembleFinishRoundJointInput {p : Parameters}
    (rate : RateInput p) {Ω : Type*} [MeasurableSpace Ω]
    (state : Ω → CarriedState p rate) (memory : Ω → LocalMemoryCode p)
    (row : Ω → CompletePublicTable.CompleteRow p) (time : Ω → Fin p.T)
    (hstate : Measurable state) (hmemory : Measurable memory)
    (hrow : Measurable row) (htime : Measurable time) :
    Measurable (fun ω => assembleFinishRoundJointInput
      (state ω) (memory ω) (row ω) (time ω)) :=
  hstate.prodMk (hmemory.prodMk (hrow.prodMk htime))

/-- The release assembler is measurable from the independent component maps. -/
theorem measurable_assembleReleaseFinishJointInput {p : Parameters}
    (rate : RateInput p) {Ω : Type*} [MeasurableSpace Ω]
    (preChoice postService : Ω → CarriedState p rate)
    (memory : Ω → LocalMemoryCode p) (row : Ω → CompletePublicTable.CompleteRow p)
    (time : Ω → Fin p.T) (feedback : Ω → Fin (D p + 1))
    (hpreChoice : Measurable preChoice) (hpostService : Measurable postService)
    (hmemory : Measurable memory) (hrow : Measurable row) (htime : Measurable time)
    (hfeedback : Measurable feedback) :
    Measurable (fun ω => assembleReleaseFinishJointInput
      (preChoice ω) (postService ω) (memory ω) (row ω) (time ω) (feedback ω)) :=
  hpreChoice.prodMk
    (hpostService.prodMk (hmemory.prodMk ((hrow.prodMk htime).prodMk hfeedback)))

/-- The existing finishRound result code on an arbitrary carried state. -/
def finishRoundResultCodeAtComponents {p : Parameters} (rate : RateInput p)
    (state : CarriedState p rate) (memory : LocalMemoryCode p)
    (row : CompletePublicTable.CompleteRow p) (time : Fin p.T) :
    FinishRoundResultCode p rate :=
  FollowerReleaseFinishMeasurability.finishRoundResultCodeAt rate row time
    state.1.1 memory state.1.2.2 state.2

/-- The existing pending-release result code on two independently varying
carried states. -/
def releaseAfterServiceResultCodeAtComponents {p : Parameters} (rate : RateInput p)
    (i : Fin (p.m - 1)) (preChoice postService : CarriedState p rate)
    (_memory : LocalMemoryCode p) (row : CompletePublicTable.CompleteRow p)
    (time : Fin p.T) (feedback : Fin (D p + 1)) :
    ReleaseAfterServiceResultCode p rate :=
  FollowerLifecycleMeasurability.releaseAfterServiceResultCodeAt rate i
    row time feedback preChoice.1.1 postService.1.1 preChoice.1.2.2
    postService.1.2.2 preChoice.2 postService.2

/-- The existing combined releaseAndFinish result code on two independently
varying carried states. -/
def releaseAndFinishResultCodeAtComponents {p : Parameters} (rate : RateInput p)
    (i : Fin (p.m - 1)) (preChoice postService : CarriedState p rate)
    (memory : LocalMemoryCode p) (row : CompletePublicTable.CompleteRow p)
    (time : Fin p.T) (feedback : Fin (D p + 1)) :
    ReleaseAndFinishResultCode p rate :=
  FollowerLifecycleMeasurability.releaseAndFinishResultCodeAt rate i
    row time feedback preChoice.1.1 postService.1.1 memory
    preChoice.1.2.2 postService.1.2.2 preChoice.2 postService.2

/-- Replace only a carried state's countable registers. Its exact skeleton
index and original length-indexed scalar family remain unchanged. -/
def carriedStateWithStateCode {p : Parameters} {rate : RateInput p}
    (state : CarriedState p rate)
    (stateCode : FollowerDownMeasurability.FollowerStateCode p rate) :
    CarriedState p rate :=
  ⟨(stateCode, state.1.2), state.2⟩

theorem carriedStateBuffer_withStateCode {p : Parameters} {rate : RateInput p}
    (state : CarriedState p rate)
    (stateCode : FollowerDownMeasurability.FollowerStateCode p rate) :
    carriedStateBuffer (carriedStateWithStateCode state stateCode) =
      carriedStateBuffer state := rfl

abbrev FinishRoundCarriedOutput (p : Parameters) (rate : RateInput p) :=
  ActiveFollowerLifecycle.LifecycleFailure ⊕
    (CarriedState p rate × LocalMemoryCode p)

abbrev ReleaseAfterServiceCarriedOutput (p : Parameters) (rate : RateInput p) :=
  ActiveFollowerLifecycle.LifecycleFailure ⊕ CarriedState p rate

abbrev ReleaseAndFinishCarriedOutput (p : Parameters) (rate : RateInput p) :=
  DeclaredFollowerLocalRound.RoundFailure ⊕
    (CarriedState p rate × LocalMemoryCode p)

/-- The full finish output pairs the actual failure with every output register,
memory bit, and original continuous buffer coordinate on success. -/
def finishRoundCarriedOutput {p : Parameters} {rate : RateInput p}
    (inputState : CarriedState p rate)
    (code : FinishRoundResultCode p rate) : FinishRoundCarriedOutput p rate :=
  match code with
  | .failure reason => Sum.inl (lifecycleFailureOfCode reason)
  | .success stateCode memoryCode =>
      Sum.inr (carriedStateWithStateCode inputState stateCode, memoryCode)

/-- The full release output retains the exact post-service buffer on success. -/
def releaseAfterServiceCarriedOutput {p : Parameters} {rate : RateInput p}
    (postService : CarriedState p rate)
    (code : ReleaseAfterServiceResultCode p rate) : ReleaseAfterServiceCarriedOutput p rate :=
  match code with
  | .failure reason => Sum.inl (lifecycleFailureOfCode reason)
  | .success stateCode => Sum.inr (carriedStateWithStateCode postService stateCode)

/-- The full combined output retains every stage-specific error and the
post-service buffer alongside the changed registers and actual memory. -/
def releaseAndFinishCarriedOutput {p : Parameters} {rate : RateInput p}
    (postService : CarriedState p rate)
    (code : ReleaseAndFinishResultCode p rate) : ReleaseAndFinishCarriedOutput p rate :=
  match code with
  | .failure reason => Sum.inl reason
  | .success stateCode memoryCode =>
      Sum.inr (carriedStateWithStateCode postService stateCode, memoryCode)

/-- Decode a full finish output to the exact existing lifecycle result. -/
def reconstructFinishRoundCarriedOutput {p : Parameters} {rate : RateInput p}
    (output : FinishRoundCarriedOutput p rate) :
    ActiveFollowerLifecycle.LifecycleCheck
      (ReferencePrelaunchFollower.State p rate.eta × LocalMemory p) :=
  Sum.elim (fun reason => .error reason)
    (fun result => .ok
      (reconstructCarriedState result.1.1 result.1.2,
        localMemoryOfCode result.2)) output

/-- Decode a full pending-release output to the exact existing lifecycle result. -/
def reconstructReleaseAfterServiceCarriedOutput {p : Parameters} {rate : RateInput p}
    (output : ReleaseAfterServiceCarriedOutput p rate) :
    ActiveFollowerLifecycle.LifecycleCheck
      (ReferencePrelaunchFollower.State p rate.eta) :=
  Sum.elim (fun reason => .error reason)
    (fun state => .ok (reconstructCarriedState state.1 state.2)) output

/-- Decode a full combined output to the exact existing checked round result. -/
def reconstructReleaseAndFinishCarriedOutput {p : Parameters} {rate : RateInput p}
    (output : ReleaseAndFinishCarriedOutput p rate) :
    Except DeclaredFollowerLocalRound.RoundFailure
      (ReferencePrelaunchFollower.State p rate.eta × LocalMemory p) :=
  Sum.elim (fun reason => .error reason)
    (fun result => .ok
      (reconstructCarriedState result.1.1 result.1.2,
        localMemoryOfCode result.2)) output

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

/-- Distribute a product into a countable measurable disjoint union, proving
measurability from each original fiber. -/
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
  have hpre :
      (fun x : (Sigma β) × γ => (⟨x.1.1, (x.1.2, x.2)⟩ : Sigma fun a => β a × γ)) ⁻¹' s =
      ⋃ a, (Prod.map (Sigma.mk a) id) ''
        ((@Sigma.mk α (fun b => β b × γ) a) ⁻¹' s) := by
    ext x
    constructor
    · intro hx
      exact Set.mem_iUnion.mpr ⟨x.1.1, (x.1.2, x.2), hx, rfl⟩
    · intro hx
      obtain ⟨a, y, hy, hxy⟩ := Set.mem_iUnion.mp hx
      subst x
      exact hy
  rw [hpre]
  exact MeasurableSet.iUnion himages

private theorem measurable_of_sigma_sections_left {α : Type*} [Countable α]
    {β : α → Type*} [∀ a, MeasurableSpace (β a)]
    {γ δ : Type*} [MeasurableSpace γ] [MeasurableSpace δ]
    (f : Sigma β × γ → δ)
    (hf : ∀ a, Measurable (fun x : β a × γ => f (⟨a, x.1⟩, x.2))) :
    Measurable f := by
  let g : Sigma (fun a => β a × γ) → δ :=
    fun x => f (⟨x.1, x.2.1⟩, x.2.2)
  have hg : Measurable g := measurable_of_sigma_sections g hf
  have hassemble : Measurable
      (fun x : Sigma β × γ => (⟨x.1.1, (x.1.2, x.2)⟩ : Sigma fun a => β a × γ)) :=
    measurable_assembleSigmaProduct
  have heq : f = g ∘
      (fun x : Sigma β × γ => (⟨x.1.1, (x.1.2, x.2)⟩ : Sigma fun a => β a × γ)) := by
    funext x
    rfl
  rw [heq]
  exact hg.comp hassemble

private theorem measurable_of_sigma_sections_right {α : Type*} [Countable α]
    {β : α → Type*} [∀ a, MeasurableSpace (β a)]
    {γ δ : Type*} [MeasurableSpace γ] [MeasurableSpace δ]
    (f : γ × Sigma β → δ)
    (hf : ∀ a, Measurable (fun x : γ × β a => f (x.1, ⟨a, x.2⟩))) :
    Measurable f := by
  let g : Sigma β × γ → δ := fun x => f (x.2, x.1)
  have hg : Measurable g := measurable_of_sigma_sections_left g (fun a => by
    change Measurable (fun x : β a × γ => f (x.2, ⟨a, x.1⟩))
    exact (hf a).comp measurable_swap)
  have heq : f = g ∘ Prod.swap := by
    funext x
    rfl
  rw [heq]
  exact hg.comp measurable_swap

private theorem measurable_of_two_sigma_sections {α β : Type*}
    [Countable α] [Countable β]
    {A : α → Type*} [∀ a, MeasurableSpace (A a)]
    {B : β → Type*} [∀ b, MeasurableSpace (B b)]
    {γ δ : Type*} [MeasurableSpace γ] [MeasurableSpace δ]
    (f : Sigma A × (Sigma B × γ) → δ)
    (hf : ∀ a b, Measurable (fun x : A a × (B b × γ) =>
      f (⟨a, x.1⟩, (⟨b, x.2.1⟩, x.2.2)))) :
    Measurable f := by
  apply measurable_of_sigma_sections_left
  intro a
  let g : (A a × γ) × Sigma B → δ :=
    fun z => f (⟨a, z.1.1⟩, (z.2, z.1.2))
  have hg : Measurable g := measurable_of_sigma_sections_right g (fun b => by
    have hsectionReorder : Measurable (fun x : (A a × γ) × B b =>
        (x.1.1, (x.2, x.1.2))) :=
      (measurable_fst.comp measurable_fst).prodMk
        (measurable_snd.prodMk (measurable_snd.comp measurable_fst))
    exact (hf a b).comp hsectionReorder)
  have hreorder : Measurable (fun x : A a × (Sigma B × γ) =>
      ((x.1, x.2.2), x.2.1)) :=
    (measurable_fst.prodMk (measurable_snd.comp measurable_snd)).prodMk
      (measurable_fst.comp measurable_snd)
  have heq : (fun x : A a × (Sigma B × γ) =>
      f (⟨a, x.1⟩, (x.2.1, x.2.2))) =
        g ∘ (fun x => ((x.1, x.2.2), x.2.1)) := by
    funext x
    rfl
  rw [heq]
  exact hg.comp hreorder

/-- The exact varying-input finish result code. -/
def finishRoundResultCodeAtInput {p : Parameters} (rate : RateInput p)
    (input : FinishRoundJointInput p rate) : FinishRoundResultCode p rate :=
  finishRoundResultCodeAtComponents rate input.1 input.2.1 input.2.2.1 input.2.2.2

/-- Measurability on the full product carrier is proved by countable state
fibers, the accepted fixed-fiber theorem, and the countable memory code. -/
theorem measurable_finishRoundResultCodeAtInput {p : Parameters}
    (rate : RateInput p) :
    Measurable (finishRoundResultCodeAtInput rate) := by
  apply measurable_of_sigma_sections_left
  intro index
  let n := index.2.1
  let stateCode := index.1
  let skeleton := index.2.2
  have hfixed : Measurable (fun z :
      FollowerReleaseFinishMeasurability.FinishRoundInput p n × LocalMemoryCode p =>
        FollowerReleaseFinishMeasurability.finishRoundResultCodeAt rate
          z.1.1.1 z.1.1.2 stateCode z.2 skeleton z.1.2) := by
    apply measurable_from_prod_countable_left
    intro memoryCode
    exact FollowerReleaseFinishMeasurability.measurable_finishRoundResultCodeAt
      rate stateCode memoryCode skeleton
  have hcoordinates : Measurable (fun x :
      SavedScalarFamily n ×
        (LocalMemoryCode p × (CompletePublicTable.CompleteRow p × Fin p.T)) =>
          ((((x.2.2.1, x.2.2.2), x.1), x.2.1) :
            FollowerReleaseFinishMeasurability.FinishRoundInput p n ×
              LocalMemoryCode p)) := by
    have hrow : Measurable (fun x : SavedScalarFamily n ×
        (LocalMemoryCode p × (CompletePublicTable.CompleteRow p × Fin p.T)) =>
          x.2.2.1) :=
      measurable_fst.comp (measurable_snd.comp measurable_snd)
    have htime : Measurable (fun x : SavedScalarFamily n ×
        (LocalMemoryCode p × (CompletePublicTable.CompleteRow p × Fin p.T)) =>
          x.2.2.2) :=
      measurable_snd.comp (measurable_snd.comp measurable_snd)
    have hvalues : Measurable (fun x : SavedScalarFamily n ×
        (LocalMemoryCode p × (CompletePublicTable.CompleteRow p × Fin p.T)) => x.1) :=
      measurable_fst
    have hmemory : Measurable (fun x : SavedScalarFamily n ×
        (LocalMemoryCode p × (CompletePublicTable.CompleteRow p × Fin p.T)) =>
          x.2.1) :=
      measurable_fst.comp measurable_snd
    exact (((hrow.prodMk htime).prodMk hvalues).prodMk hmemory)
  have hsection : Measurable (fun x :
      SavedScalarFamily n ×
        (LocalMemoryCode p × (CompletePublicTable.CompleteRow p × Fin p.T)) =>
      finishRoundResultCodeAtInput rate
        (⟨index, x.1⟩, x.2)) := by
    exact hfixed.comp hcoordinates
  exact hsection

/-- Joint measurability of the existing finishRound result code over the
entire accepted carried-state domain, memory, complete row, and calendar time. -/
theorem measurable_finishRoundResultCodeAtComponents {p : Parameters}
    (rate : RateInput p) {Ω : Type*} [MeasurableSpace Ω]
    (state : Ω → CarriedState p rate) (memory : Ω → LocalMemoryCode p)
    (row : Ω → CompletePublicTable.CompleteRow p) (time : Ω → Fin p.T)
    (hstate : Measurable state) (hmemory : Measurable memory)
    (hrow : Measurable row) (htime : Measurable time) :
    Measurable (fun ω => finishRoundResultCodeAtComponents rate
      (state ω) (memory ω) (row ω) (time ω)) := by
  have hinput := measurable_assembleFinishRoundJointInput rate
    state memory row time hstate hmemory hrow htime
  exact (measurable_finishRoundResultCodeAtInput rate).comp hinput

/-- The exact varying-input pending-release result code. -/
def releaseAfterServiceResultCodeAtInput {p : Parameters} (rate : RateInput p)
    (i : Fin (p.m - 1)) (input : ReleaseFinishJointInput p rate) :
    ReleaseAfterServiceResultCode p rate :=
  releaseAfterServiceResultCodeAtComponents rate i
    input.1 input.2.1 input.2.2.1
    input.2.2.2.1.1 input.2.2.2.1.2 input.2.2.2.2

/-- Measurability is assembled from the independent pre-choice and
post-service countable fibers and the fixed-fiber release theorem. -/
theorem measurable_releaseAfterServiceResultCodeAtInput {p : Parameters}
    (rate : RateInput p) (i : Fin (p.m - 1)) :
    Measurable (releaseAfterServiceResultCodeAtInput rate i) := by
  apply measurable_of_two_sigma_sections
  intro preIndex postIndex
  let n := preIndex.2.1
  let m := postIndex.2.1
  let preCode := preIndex.1
  let postCode := postIndex.1
  let preSkeleton := preIndex.2.2
  let postSkeleton := postIndex.2.2
  have hcoordinates : Measurable (fun x :
      ReleaseFinishFiberCoordinates p n m =>
        ((x.2.2.2, (x.1, x.2.1)) : ReleaseInput p n m)) := by
    have hrow : Measurable (fun x : SavedScalarFamily n ×
        (SavedScalarFamily m × (LocalMemoryCode p ×
          ((CompletePublicTable.CompleteRow p × Fin p.T) × Fin (D p + 1)))) =>
          x.2.2.2.1.1) :=
      measurable_fst.comp (measurable_fst.comp
      (measurable_snd.comp (measurable_snd.comp measurable_snd)))
    have htime : Measurable (fun x : SavedScalarFamily n ×
        (SavedScalarFamily m × (LocalMemoryCode p ×
          ((CompletePublicTable.CompleteRow p × Fin p.T) × Fin (D p + 1)))) =>
          x.2.2.2.1.2) :=
      measurable_snd.comp (measurable_fst.comp
      (measurable_snd.comp (measurable_snd.comp measurable_snd)))
    have hfeedback : Measurable (fun x : SavedScalarFamily n ×
        (SavedScalarFamily m × (LocalMemoryCode p ×
          ((CompletePublicTable.CompleteRow p × Fin p.T) × Fin (D p + 1)))) =>
          x.2.2.2.2) :=
      measurable_snd.comp
      (measurable_snd.comp (measurable_snd.comp measurable_snd))
    have hpre : Measurable (fun x : SavedScalarFamily n ×
        (SavedScalarFamily m × (LocalMemoryCode p ×
          ((CompletePublicTable.CompleteRow p × Fin p.T) × Fin (D p + 1)))) =>
          x.1) := measurable_fst
    have hpost : Measurable (fun x : SavedScalarFamily n ×
        (SavedScalarFamily m × (LocalMemoryCode p ×
          ((CompletePublicTable.CompleteRow p × Fin p.T) × Fin (D p + 1)))) =>
          x.2.1) := measurable_fst.comp measurable_snd
    exact (((hrow.prodMk htime).prodMk hfeedback).prodMk (hpre.prodMk hpost))
  have hfixed : Measurable (fun x : ReleaseInput p n m =>
      FollowerLifecycleMeasurability.releaseAfterServiceResultCodeAt
        rate i x.1.1.1 x.1.1.2 x.1.2 preCode postCode
          preSkeleton postSkeleton x.2.1 x.2.2) :=
    FollowerReleaseFinishMeasurability.measurable_releaseAfterServiceResultCodeAt
      rate i preCode postCode preSkeleton postSkeleton
  have hsection : Measurable (fun x :
      ReleaseFinishFiberCoordinates p n m =>
      releaseAfterServiceResultCodeAtInput rate i
        (⟨preIndex, x.1⟩, (⟨postIndex, x.2.1⟩, x.2.2))) := by
    exact hfixed.comp hcoordinates
  exact hsection

/-- Joint measurability of the actual pending-release result code when both
independent carried states, memory, row, time, and own finite feedback vary. -/
theorem measurable_releaseAfterServiceResultCodeAtComponents {p : Parameters}
    (rate : RateInput p) (i : Fin (p.m - 1)) {Ω : Type*} [MeasurableSpace Ω]
    (preChoice postService : Ω → CarriedState p rate)
    (memory : Ω → LocalMemoryCode p) (row : Ω → CompletePublicTable.CompleteRow p)
    (time : Ω → Fin p.T) (feedback : Ω → Fin (D p + 1))
    (hpreChoice : Measurable preChoice) (hpostService : Measurable postService)
    (hmemory : Measurable memory) (hrow : Measurable row) (htime : Measurable time)
    (hfeedback : Measurable feedback) :
    Measurable (fun ω => releaseAfterServiceResultCodeAtComponents rate i
      (preChoice ω) (postService ω) (memory ω) (row ω) (time ω) (feedback ω)) := by
  have hinput := measurable_assembleReleaseFinishJointInput rate
    preChoice postService memory row time feedback
    hpreChoice hpostService hmemory hrow htime hfeedback
  exact (measurable_releaseAfterServiceResultCodeAtInput rate i).comp hinput

/-- The exact varying-input combined releaseAndFinish result code. -/
def releaseAndFinishResultCodeAtInput {p : Parameters} (rate : RateInput p)
    (i : Fin (p.m - 1)) (input : ReleaseFinishJointInput p rate) :
    ReleaseAndFinishResultCode p rate :=
  releaseAndFinishResultCodeAtComponents rate i
    input.1 input.2.1 input.2.2.1
    input.2.2.2.1.1 input.2.2.2.1.2 input.2.2.2.2

/-- The fixed-fiber combined theorem is lifted across both independently
varying state indices and the countable local-memory code. -/
theorem measurable_releaseAndFinishResultCodeAtInput {p : Parameters}
    (rate : RateInput p) (i : Fin (p.m - 1)) :
    Measurable (releaseAndFinishResultCodeAtInput rate i) := by
  apply measurable_of_two_sigma_sections
  intro preIndex postIndex
  let n := preIndex.2.1
  let m := postIndex.2.1
  let preCode := preIndex.1
  let postCode := postIndex.1
  let preSkeleton := preIndex.2.2
  let postSkeleton := postIndex.2.2
  have hfixed : Measurable (fun x : ReleaseInput p n m × LocalMemoryCode p =>
      FollowerLifecycleMeasurability.releaseAndFinishResultCodeAt rate i
        x.1.1.1.1 x.1.1.1.2 x.1.1.2 preCode postCode x.2
          preSkeleton postSkeleton x.1.2.1 x.1.2.2) := by
    apply measurable_from_prod_countable_left
    intro memoryCode
    exact FollowerReleaseFinishMeasurability.measurable_releaseAndFinishResultCodeAt
      rate i preCode postCode memoryCode preSkeleton postSkeleton
  have hcoordinates : Measurable (fun x :
      ReleaseFinishFiberCoordinates p n m =>
        (((x.2.2.2, (x.1, x.2.1)) : ReleaseInput p n m), x.2.2.1)) := by
    have hrow : Measurable (fun x : SavedScalarFamily n ×
        (SavedScalarFamily m × (LocalMemoryCode p ×
          ((CompletePublicTable.CompleteRow p × Fin p.T) × Fin (D p + 1)))) =>
          x.2.2.2.1.1) :=
      measurable_fst.comp (measurable_fst.comp
      (measurable_snd.comp (measurable_snd.comp measurable_snd)))
    have htime : Measurable (fun x : SavedScalarFamily n ×
        (SavedScalarFamily m × (LocalMemoryCode p ×
          ((CompletePublicTable.CompleteRow p × Fin p.T) × Fin (D p + 1)))) =>
          x.2.2.2.1.2) :=
      measurable_snd.comp (measurable_fst.comp
      (measurable_snd.comp (measurable_snd.comp measurable_snd)))
    have hfeedback : Measurable (fun x : SavedScalarFamily n ×
        (SavedScalarFamily m × (LocalMemoryCode p ×
          ((CompletePublicTable.CompleteRow p × Fin p.T) × Fin (D p + 1)))) =>
          x.2.2.2.2) :=
      measurable_snd.comp
      (measurable_snd.comp (measurable_snd.comp measurable_snd))
    have hpre : Measurable (fun x : SavedScalarFamily n ×
        (SavedScalarFamily m × (LocalMemoryCode p ×
          ((CompletePublicTable.CompleteRow p × Fin p.T) × Fin (D p + 1)))) =>
          x.1) := measurable_fst
    have hpost : Measurable (fun x : SavedScalarFamily n ×
        (SavedScalarFamily m × (LocalMemoryCode p ×
          ((CompletePublicTable.CompleteRow p × Fin p.T) × Fin (D p + 1)))) =>
          x.2.1) := measurable_fst.comp measurable_snd
    have hmemory : Measurable (fun x : SavedScalarFamily n ×
        (SavedScalarFamily m × (LocalMemoryCode p ×
          ((CompletePublicTable.CompleteRow p × Fin p.T) × Fin (D p + 1)))) =>
          x.2.2.1) :=
      measurable_fst.comp (measurable_snd.comp measurable_snd)
    exact ((((hrow.prodMk htime).prodMk hfeedback).prodMk (hpre.prodMk hpost)).prodMk
      hmemory)
  have hsection : Measurable (fun x :
      ReleaseFinishFiberCoordinates p n m =>
      releaseAndFinishResultCodeAtInput rate i
        (⟨preIndex, x.1⟩, (⟨postIndex, x.2.1⟩, x.2.2))) := by
    exact hfixed.comp hcoordinates
  exact hsection

/-- Joint measurability of the actual combined releaseAndFinish result code
on independent carried states and all supplied local input coordinates. -/
theorem measurable_releaseAndFinishResultCodeAtComponents {p : Parameters}
    (rate : RateInput p) (i : Fin (p.m - 1)) {Ω : Type*} [MeasurableSpace Ω]
    (preChoice postService : Ω → CarriedState p rate)
    (memory : Ω → LocalMemoryCode p) (row : Ω → CompletePublicTable.CompleteRow p)
    (time : Ω → Fin p.T) (feedback : Ω → Fin (D p + 1))
    (hpreChoice : Measurable preChoice) (hpostService : Measurable postService)
    (hmemory : Measurable memory) (hrow : Measurable row) (htime : Measurable time)
    (hfeedback : Measurable feedback) :
    Measurable (fun ω => releaseAndFinishResultCodeAtComponents rate i
      (preChoice ω) (postService ω) (memory ω) (row ω) (time ω) (feedback ω)) := by
  have hinput := measurable_assembleReleaseFinishJointInput rate
    preChoice postService memory row time feedback
    hpreChoice hpostService hmemory hrow htime hfeedback
  exact (measurable_releaseAndFinishResultCodeAtInput rate i).comp hinput

/-- Full finish success measurability retains the original carried buffer
while installing the changed result registers and memory code. -/
theorem measurable_finishRoundCarriedOutputAtInput {p : Parameters}
    (rate : RateInput p) :
    Measurable (fun input : FinishRoundJointInput p rate =>
      finishRoundCarriedOutput input.1 (finishRoundResultCodeAtInput rate input)) := by
  apply measurable_of_sigma_sections_left
  intro index
  let n := index.2.1
  let stateCode := index.1
  let skeleton := index.2.2
  have hfixed : Measurable (fun z :
      FollowerReleaseFinishMeasurability.FinishRoundInput p n × LocalMemoryCode p =>
        FollowerReleaseFinishMeasurability.finishRoundResultCodeAt rate
          z.1.1.1 z.1.1.2 stateCode z.2 skeleton z.1.2) := by
    apply measurable_from_prod_countable_left
    intro memoryCode
    exact FollowerReleaseFinishMeasurability.measurable_finishRoundResultCodeAt
      rate stateCode memoryCode skeleton
  have hcoordinates : Measurable (fun x : FinishRoundFiberCoordinates p n =>
      ((((x.2.2.1, x.2.2.2), x.1) :
        FollowerReleaseFinishMeasurability.FinishRoundInput p n), x.2.1)) := by
    have hrow : Measurable (fun x : FinishRoundFiberCoordinates p n => x.2.2.1) :=
      measurable_fst.comp (measurable_snd.comp measurable_snd)
    have htime : Measurable (fun x : FinishRoundFiberCoordinates p n => x.2.2.2) :=
      measurable_snd.comp (measurable_snd.comp measurable_snd)
    have hvalues : Measurable (fun x : FinishRoundFiberCoordinates p n => x.1) :=
      measurable_fst
    have hmemory : Measurable (fun x : FinishRoundFiberCoordinates p n => x.2.1) :=
      measurable_fst.comp measurable_snd
    exact ((hrow.prodMk htime).prodMk hvalues).prodMk hmemory
  have hcode : Measurable (fun x : FinishRoundFiberCoordinates p n =>
      finishRoundResultCodeAtInput rate (⟨index, x.1⟩, x.2)) := by
    exact hfixed.comp hcoordinates
  have hfullFiber : Measurable (fun z :
      FinishRoundResultCode p rate × SavedScalarFamily n =>
        finishRoundCarriedOutput (⟨index, z.2⟩) z.1) := by
    apply measurable_from_prod_countable_right
    intro resultCode
    cases resultCode with
    | failure _ => exact measurable_const
    | success outputCode memoryCode =>
        have hstate : Measurable (fun values : SavedScalarFamily n =>
            (⟨(outputCode, index.2), values⟩ : CarriedState p rate)) :=
          measurable_sigmaMk (β := fun a : FollowerCarryIndex p rate =>
            SavedScalarFamily a.2.1) (outputCode, index.2)
        exact measurable_inr.comp (hstate.prodMk measurable_const)
  have hsection : Measurable (fun x : FinishRoundFiberCoordinates p n =>
      finishRoundCarriedOutput (⟨index, x.1⟩)
        (finishRoundResultCodeAtInput rate (⟨index, x.1⟩, x.2))) := by
    exact hfullFiber.comp (hcode.prodMk measurable_fst)
  exact hsection

/-- Arbitrary-base full finish output measurability follows from its
separately measurable accepted components and the explicit input assembler. -/
theorem measurable_finishRoundCarriedOutputAtComponents {p : Parameters}
    (rate : RateInput p) {Ω : Type*} [MeasurableSpace Ω]
    (state : Ω → CarriedState p rate) (memory : Ω → LocalMemoryCode p)
    (row : Ω → CompletePublicTable.CompleteRow p) (time : Ω → Fin p.T)
    (hstate : Measurable state) (hmemory : Measurable memory)
    (hrow : Measurable row) (htime : Measurable time) :
    Measurable (fun ω => finishRoundCarriedOutput (state ω)
      (finishRoundResultCodeAtComponents rate (state ω) (memory ω) (row ω) (time ω))) := by
  have hinput := measurable_assembleFinishRoundJointInput rate
    state memory row time hstate hmemory hrow htime
  exact (measurable_finishRoundCarriedOutputAtInput rate).comp hinput

/-- Full pending-release output measurability retains the unchanged
post-service skeleton and original scalar family on every successful branch. -/
theorem measurable_releaseAfterServiceCarriedOutputAtInput {p : Parameters}
    (rate : RateInput p) (i : Fin (p.m - 1)) :
    Measurable (fun input : ReleaseFinishJointInput p rate =>
      releaseAfterServiceCarriedOutput input.2.1
        (releaseAfterServiceResultCodeAtInput rate i input)) := by
  apply measurable_of_two_sigma_sections
  intro preIndex postIndex
  let n := preIndex.2.1
  let m := postIndex.2.1
  let preCode := preIndex.1
  let postCode := postIndex.1
  let preSkeleton := preIndex.2.2
  let postSkeleton := postIndex.2.2
  have hfixed : Measurable (fun x : ReleaseInput p n m =>
      FollowerLifecycleMeasurability.releaseAfterServiceResultCodeAt
        rate i x.1.1.1 x.1.1.2 x.1.2 preCode postCode
          preSkeleton postSkeleton x.2.1 x.2.2) :=
    FollowerReleaseFinishMeasurability.measurable_releaseAfterServiceResultCodeAt
      rate i preCode postCode preSkeleton postSkeleton
  have hcoordinates : Measurable (fun x : ReleaseFinishFiberCoordinates p n m =>
      ((x.2.2.2, (x.1, x.2.1)) : ReleaseInput p n m)) := by
    have hrow : Measurable (fun x : ReleaseFinishFiberCoordinates p n m =>
        x.2.2.2.1.1) :=
      measurable_fst.comp (measurable_fst.comp
        (measurable_snd.comp (measurable_snd.comp measurable_snd)))
    have htime : Measurable (fun x : ReleaseFinishFiberCoordinates p n m =>
        x.2.2.2.1.2) :=
      measurable_snd.comp (measurable_fst.comp
        (measurable_snd.comp (measurable_snd.comp measurable_snd)))
    have hfeedback : Measurable (fun x : ReleaseFinishFiberCoordinates p n m =>
        x.2.2.2.2) :=
      measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))
    have hpre : Measurable (fun x : ReleaseFinishFiberCoordinates p n m => x.1) :=
      measurable_fst
    have hpost : Measurable (fun x : ReleaseFinishFiberCoordinates p n m => x.2.1) :=
      measurable_fst.comp measurable_snd
    exact ((hrow.prodMk htime).prodMk hfeedback).prodMk (hpre.prodMk hpost)
  have hcode : Measurable (fun x : ReleaseFinishFiberCoordinates p n m =>
      releaseAfterServiceResultCodeAtInput rate i
        (⟨preIndex, x.1⟩, (⟨postIndex, x.2.1⟩, x.2.2))) := by
    exact hfixed.comp hcoordinates
  have hpostValues : Measurable (fun x : ReleaseFinishFiberCoordinates p n m => x.2.1) :=
    measurable_fst.comp measurable_snd
  have hfullFiber : Measurable (fun z :
      ReleaseAfterServiceResultCode p rate × SavedScalarFamily m =>
        releaseAfterServiceCarriedOutput (⟨postIndex, z.2⟩) z.1) := by
    apply measurable_from_prod_countable_right
    intro resultCode
    cases resultCode with
    | failure _ => exact measurable_const
    | success outputCode =>
        exact measurable_inr.comp
          (measurable_sigmaMk (β := fun a : FollowerCarryIndex p rate =>
            SavedScalarFamily a.2.1) (outputCode, postIndex.2))
  have hsection : Measurable (fun x : ReleaseFinishFiberCoordinates p n m =>
      releaseAfterServiceCarriedOutput (⟨postIndex, x.2.1⟩)
        (releaseAfterServiceResultCodeAtInput rate i
          (⟨preIndex, x.1⟩, (⟨postIndex, x.2.1⟩, x.2.2)))) := by
    exact hfullFiber.comp (hcode.prodMk hpostValues)
  change Measurable (fun x : ReleaseFinishFiberCoordinates p n m =>
    releaseAfterServiceCarriedOutput (⟨postIndex, x.2.1⟩)
      (releaseAfterServiceResultCodeAtInput rate i
        (⟨preIndex, x.1⟩, (⟨postIndex, x.2.1⟩, x.2.2))))
  simpa only [Prod.fst, Prod.snd] using hsection

/-- Arbitrary-base full release output measurability is derived from the
component maps through the explicit independent-state assembler. -/
theorem measurable_releaseAfterServiceCarriedOutputAtComponents {p : Parameters}
    (rate : RateInput p) (i : Fin (p.m - 1)) {Ω : Type*} [MeasurableSpace Ω]
    (preChoice postService : Ω → CarriedState p rate)
    (memory : Ω → LocalMemoryCode p) (row : Ω → CompletePublicTable.CompleteRow p)
    (time : Ω → Fin p.T) (feedback : Ω → Fin (D p + 1))
    (hpreChoice : Measurable preChoice) (hpostService : Measurable postService)
    (hmemory : Measurable memory) (hrow : Measurable row) (htime : Measurable time)
    (hfeedback : Measurable feedback) :
    Measurable (fun ω => releaseAfterServiceCarriedOutput (postService ω)
      (releaseAfterServiceResultCodeAtComponents rate i (preChoice ω) (postService ω)
        (memory ω) (row ω) (time ω) (feedback ω))) := by
  have hinput := measurable_assembleReleaseFinishJointInput rate
    preChoice postService memory row time feedback
    hpreChoice hpostService hmemory hrow htime hfeedback
  exact (measurable_releaseAfterServiceCarriedOutputAtInput rate i).comp hinput

/-- Full combined output measurability retains all source-stage failures,
the changed registers, actual memory code, and the original post-state buffer. -/
theorem measurable_releaseAndFinishCarriedOutputAtInput {p : Parameters}
    (rate : RateInput p) (i : Fin (p.m - 1)) :
    Measurable (fun input : ReleaseFinishJointInput p rate =>
      releaseAndFinishCarriedOutput input.2.1
        (releaseAndFinishResultCodeAtInput rate i input)) := by
  apply measurable_of_two_sigma_sections
  intro preIndex postIndex
  let n := preIndex.2.1
  let m := postIndex.2.1
  let preCode := preIndex.1
  let postCode := postIndex.1
  let preSkeleton := preIndex.2.2
  let postSkeleton := postIndex.2.2
  have hfixed : Measurable (fun x : ReleaseInput p n m × LocalMemoryCode p =>
      FollowerLifecycleMeasurability.releaseAndFinishResultCodeAt rate i
        x.1.1.1.1 x.1.1.1.2 x.1.1.2 preCode postCode x.2
          preSkeleton postSkeleton x.1.2.1 x.1.2.2) := by
    apply measurable_from_prod_countable_left
    intro memoryCode
    exact FollowerReleaseFinishMeasurability.measurable_releaseAndFinishResultCodeAt
      rate i preCode postCode memoryCode preSkeleton postSkeleton
  have hcoordinates : Measurable (fun x : ReleaseFinishFiberCoordinates p n m =>
      (((x.2.2.2, (x.1, x.2.1)) : ReleaseInput p n m), x.2.2.1)) := by
    have hrow : Measurable (fun x : ReleaseFinishFiberCoordinates p n m =>
        x.2.2.2.1.1) :=
      measurable_fst.comp (measurable_fst.comp
        (measurable_snd.comp (measurable_snd.comp measurable_snd)))
    have htime : Measurable (fun x : ReleaseFinishFiberCoordinates p n m =>
        x.2.2.2.1.2) :=
      measurable_snd.comp (measurable_fst.comp
        (measurable_snd.comp (measurable_snd.comp measurable_snd)))
    have hfeedback : Measurable (fun x : ReleaseFinishFiberCoordinates p n m =>
        x.2.2.2.2) :=
      measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))
    have hpre : Measurable (fun x : ReleaseFinishFiberCoordinates p n m => x.1) :=
      measurable_fst
    have hpost : Measurable (fun x : ReleaseFinishFiberCoordinates p n m => x.2.1) :=
      measurable_fst.comp measurable_snd
    have hmemory : Measurable (fun x : ReleaseFinishFiberCoordinates p n m => x.2.2.1) :=
      measurable_fst.comp (measurable_snd.comp measurable_snd)
    exact ((((hrow.prodMk htime).prodMk hfeedback).prodMk (hpre.prodMk hpost)).prodMk
      hmemory)
  have hcode : Measurable (fun x : ReleaseFinishFiberCoordinates p n m =>
      releaseAndFinishResultCodeAtInput rate i
        (⟨preIndex, x.1⟩, (⟨postIndex, x.2.1⟩, x.2.2))) := by
    exact hfixed.comp hcoordinates
  have hpostValues : Measurable (fun x : ReleaseFinishFiberCoordinates p n m => x.2.1) :=
    measurable_fst.comp measurable_snd
  have hfullFiber : Measurable (fun z :
      ReleaseAndFinishResultCode p rate × SavedScalarFamily m =>
        releaseAndFinishCarriedOutput (⟨postIndex, z.2⟩) z.1) := by
    apply measurable_from_prod_countable_right
    intro resultCode
    cases resultCode with
    | failure _ => exact measurable_const
    | success outputCode memoryCode =>
        have hstate : Measurable (fun values : SavedScalarFamily m =>
            (⟨(outputCode, postIndex.2), values⟩ : CarriedState p rate)) :=
          measurable_sigmaMk (β := fun a : FollowerCarryIndex p rate =>
            SavedScalarFamily a.2.1) (outputCode, postIndex.2)
        exact measurable_inr.comp (hstate.prodMk measurable_const)
  have hsection : Measurable (fun x : ReleaseFinishFiberCoordinates p n m =>
      releaseAndFinishCarriedOutput (⟨postIndex, x.2.1⟩)
        (releaseAndFinishResultCodeAtInput rate i
          (⟨preIndex, x.1⟩, (⟨postIndex, x.2.1⟩, x.2.2)))) := by
    exact hfullFiber.comp (hcode.prodMk hpostValues)
  change Measurable (fun x : ReleaseFinishFiberCoordinates p n m =>
    releaseAndFinishCarriedOutput (⟨postIndex, x.2.1⟩)
      (releaseAndFinishResultCodeAtInput rate i
        (⟨preIndex, x.1⟩, (⟨postIndex, x.2.1⟩, x.2.2))))
  simpa only [Prod.fst, Prod.snd] using hsection

/-- Arbitrary-base full combined output measurability follows from the
explicitly assembled independent state and local input maps. -/
theorem measurable_releaseAndFinishCarriedOutputAtComponents {p : Parameters}
    (rate : RateInput p) (i : Fin (p.m - 1)) {Ω : Type*} [MeasurableSpace Ω]
    (preChoice postService : Ω → CarriedState p rate)
    (memory : Ω → LocalMemoryCode p) (row : Ω → CompletePublicTable.CompleteRow p)
    (time : Ω → Fin p.T) (feedback : Ω → Fin (D p + 1))
    (hpreChoice : Measurable preChoice) (hpostService : Measurable postService)
    (hmemory : Measurable memory) (hrow : Measurable row) (htime : Measurable time)
    (hfeedback : Measurable feedback) :
    Measurable (fun ω => releaseAndFinishCarriedOutput (postService ω)
      (releaseAndFinishResultCodeAtComponents rate i (preChoice ω) (postService ω)
        (memory ω) (row ω) (time ω) (feedback ω))) := by
  have hinput := measurable_assembleReleaseFinishJointInput rate
    preChoice postService memory row time feedback
    hpreChoice hpostService hmemory hrow htime hfeedback
  exact (measurable_releaseAndFinishCarriedOutputAtInput rate i).comp hinput

/-- The actual decoded follower status carried by the accepted state code. -/
def carriedStateStatus {p : Parameters} {rate : RateInput p}
    (state : CarriedState p rate) : ActiveRoundActions.FollowerStatus :=
  FollowerDownMeasurability.followerStatusOfCode state.1.1.status

theorem measurable_carriedStateStatus {p : Parameters} (rate : RateInput p) :
    Measurable (carriedStateStatus : CarriedState p rate →
      ActiveRoundActions.FollowerStatus) := by
  apply measurable_of_sigma_sections
  intro index
  change Measurable (fun _ : SavedScalarFamily index.2.1 =>
    FollowerDownMeasurability.followerStatusOfCode index.1.status)
  exact measurable_const

/-- Exact error projection with a tagged success case for full finish output. -/
def finishRoundCarriedOutputError {p : Parameters} {rate : RateInput p}
    (output : FinishRoundCarriedOutput p rate) : ActiveFollowerLifecycle.LifecycleFailure ⊕ PUnit :=
  match output with
  | Sum.inl reason => Sum.inl reason
  | Sum.inr _ => Sum.inr PUnit.unit

/-- Exact decoded local memory projection with a tagged failure case. -/
def finishRoundCarriedOutputMemory {p : Parameters} {rate : RateInput p}
    (output : FinishRoundCarriedOutput p rate) : LocalMemory p ⊕ PUnit :=
  match output with
  | Sum.inl _ => Sum.inr PUnit.unit
  | Sum.inr (_, memoryCode) => Sum.inl (localMemoryOfCode memoryCode)

/-- The output's actual follower status, decoded from its changed state code. -/
def finishRoundCarriedOutputStatus {p : Parameters} {rate : RateInput p}
    (output : FinishRoundCarriedOutput p rate) : ActiveRoundActions.FollowerStatus ⊕ PUnit :=
  match output with
  | Sum.inl _ => Sum.inr PUnit.unit
  | Sum.inr (state, _) => Sum.inl (carriedStateStatus state)

def releaseAfterServiceCarriedOutputError {p : Parameters} {rate : RateInput p}
    (output : ReleaseAfterServiceCarriedOutput p rate) :
    ActiveFollowerLifecycle.LifecycleFailure ⊕ PUnit :=
  match output with
  | Sum.inl reason => Sum.inl reason
  | Sum.inr _ => Sum.inr PUnit.unit

def releaseAfterServiceCarriedOutputStatus {p : Parameters} {rate : RateInput p}
    (output : ReleaseAfterServiceCarriedOutput p rate) :
    ActiveRoundActions.FollowerStatus ⊕ PUnit :=
  match output with
  | Sum.inl _ => Sum.inr PUnit.unit
  | Sum.inr state => Sum.inl (carriedStateStatus state)

def releaseAndFinishCarriedOutputError {p : Parameters} {rate : RateInput p}
    (output : ReleaseAndFinishCarriedOutput p rate) :
    DeclaredFollowerLocalRound.RoundFailure ⊕ PUnit :=
  match output with
  | Sum.inl reason => Sum.inl reason
  | Sum.inr _ => Sum.inr PUnit.unit

def releaseAndFinishCarriedOutputMemory {p : Parameters} {rate : RateInput p}
    (output : ReleaseAndFinishCarriedOutput p rate) : LocalMemory p ⊕ PUnit :=
  match output with
  | Sum.inl _ => Sum.inr PUnit.unit
  | Sum.inr (_, memoryCode) => Sum.inl (localMemoryOfCode memoryCode)

def releaseAndFinishCarriedOutputStatus {p : Parameters} {rate : RateInput p}
    (output : ReleaseAndFinishCarriedOutput p rate) :
    ActiveRoundActions.FollowerStatus ⊕ PUnit :=
  match output with
  | Sum.inl _ => Sum.inr PUnit.unit
  | Sum.inr (state, _) => Sum.inl (carriedStateStatus state)

theorem measurable_finishRoundCarriedOutputError {p : Parameters} (rate : RateInput p) :
    Measurable (finishRoundCarriedOutputError : FinishRoundCarriedOutput p rate →
      ActiveFollowerLifecycle.LifecycleFailure ⊕ PUnit) := by
  unfold finishRoundCarriedOutputError
  exact measurable_fun_sum measurable_inl measurable_const

theorem measurable_finishRoundCarriedOutputMemory {p : Parameters} (rate : RateInput p) :
    Measurable (finishRoundCarriedOutputMemory : FinishRoundCarriedOutput p rate →
      LocalMemory p ⊕ PUnit) := by
  have hmemory : Measurable (localMemoryOfCode : LocalMemoryCode p → LocalMemory p) :=
    measurable_of_countable _
  change Measurable (Sum.elim
    (fun _ : ActiveFollowerLifecycle.LifecycleFailure => (Sum.inr PUnit.unit : LocalMemory p ⊕ PUnit))
    (fun result : CarriedState p rate × LocalMemoryCode p =>
      (Sum.inl (localMemoryOfCode result.2) : LocalMemory p ⊕ PUnit)))
  exact measurable_fun_sum measurable_const
    (measurable_inl.comp (hmemory.comp measurable_snd))

theorem measurable_finishRoundCarriedOutputStatus {p : Parameters}
    (rate : RateInput p) :
    Measurable (finishRoundCarriedOutputStatus : FinishRoundCarriedOutput p rate →
      ActiveRoundActions.FollowerStatus ⊕ PUnit) := by
  change Measurable (Sum.elim
    (fun _ : ActiveFollowerLifecycle.LifecycleFailure =>
      (Sum.inr PUnit.unit : ActiveRoundActions.FollowerStatus ⊕ PUnit))
    (fun result : CarriedState p rate × LocalMemoryCode p =>
      (Sum.inl (carriedStateStatus result.1) : ActiveRoundActions.FollowerStatus ⊕ PUnit)))
  exact measurable_fun_sum measurable_const
    (measurable_inl.comp ((measurable_carriedStateStatus rate).comp measurable_fst))

theorem measurable_releaseAfterServiceCarriedOutputError {p : Parameters}
    (rate : RateInput p) :
    Measurable (releaseAfterServiceCarriedOutputError :
      ReleaseAfterServiceCarriedOutput p rate →
        ActiveFollowerLifecycle.LifecycleFailure ⊕ PUnit) := by
  change Measurable (Sum.elim
    (fun reason : ActiveFollowerLifecycle.LifecycleFailure =>
      (Sum.inl reason : ActiveFollowerLifecycle.LifecycleFailure ⊕ PUnit))
    (fun _ : CarriedState p rate =>
      (Sum.inr PUnit.unit : ActiveFollowerLifecycle.LifecycleFailure ⊕ PUnit)))
  exact measurable_fun_sum measurable_inl measurable_const

theorem measurable_releaseAfterServiceCarriedOutputStatus {p : Parameters}
    (rate : RateInput p) :
    Measurable (releaseAfterServiceCarriedOutputStatus :
      ReleaseAfterServiceCarriedOutput p rate →
        ActiveRoundActions.FollowerStatus ⊕ PUnit) := by
  change Measurable (Sum.elim
    (fun _ : ActiveFollowerLifecycle.LifecycleFailure =>
      (Sum.inr PUnit.unit : ActiveRoundActions.FollowerStatus ⊕ PUnit))
    (fun state : CarriedState p rate =>
      (Sum.inl (carriedStateStatus state) : ActiveRoundActions.FollowerStatus ⊕ PUnit)))
  exact measurable_fun_sum measurable_const
    (measurable_inl.comp (measurable_carriedStateStatus rate))

theorem measurable_releaseAndFinishCarriedOutputError {p : Parameters}
    (rate : RateInput p) :
    Measurable (releaseAndFinishCarriedOutputError :
      ReleaseAndFinishCarriedOutput p rate →
        DeclaredFollowerLocalRound.RoundFailure ⊕ PUnit) := by
  change Measurable (Sum.elim
    (fun reason : DeclaredFollowerLocalRound.RoundFailure =>
      (Sum.inl reason : DeclaredFollowerLocalRound.RoundFailure ⊕ PUnit))
    (fun _ : CarriedState p rate × LocalMemoryCode p =>
      (Sum.inr PUnit.unit : DeclaredFollowerLocalRound.RoundFailure ⊕ PUnit)))
  exact measurable_fun_sum measurable_inl measurable_const

theorem measurable_releaseAndFinishCarriedOutputMemory {p : Parameters}
    (rate : RateInput p) :
    Measurable (releaseAndFinishCarriedOutputMemory :
      ReleaseAndFinishCarriedOutput p rate → LocalMemory p ⊕ PUnit) := by
  have hmemory : Measurable (localMemoryOfCode : LocalMemoryCode p → LocalMemory p) :=
    measurable_of_countable _
  change Measurable (Sum.elim
    (fun _ : DeclaredFollowerLocalRound.RoundFailure => (Sum.inr PUnit.unit : LocalMemory p ⊕ PUnit))
    (fun result : CarriedState p rate × LocalMemoryCode p =>
      (Sum.inl (localMemoryOfCode result.2) : LocalMemory p ⊕ PUnit)))
  exact measurable_fun_sum measurable_const
    (measurable_inl.comp (hmemory.comp measurable_snd))

theorem measurable_releaseAndFinishCarriedOutputStatus {p : Parameters}
    (rate : RateInput p) :
    Measurable (releaseAndFinishCarriedOutputStatus :
      ReleaseAndFinishCarriedOutput p rate →
        ActiveRoundActions.FollowerStatus ⊕ PUnit) := by
  change Measurable (Sum.elim
    (fun _ : DeclaredFollowerLocalRound.RoundFailure =>
      (Sum.inr PUnit.unit : ActiveRoundActions.FollowerStatus ⊕ PUnit))
    (fun result : CarriedState p rate × LocalMemoryCode p =>
      (Sum.inl (carriedStateStatus result.1) : ActiveRoundActions.FollowerStatus ⊕ PUnit)))
  exact measurable_fun_sum measurable_const
    (measurable_inl.comp ((measurable_carriedStateStatus rate).comp measurable_fst))

/-- Exact finish reconstruction on an arbitrary accepted carried state. -/
theorem finishRoundResultCodeAtComponents_reconstruct {p : Parameters}
    (rate : RateInput p) (state : CarriedState p rate)
    (memory : LocalMemoryCode p) (row : CompletePublicTable.CompleteRow p)
    (time : Fin p.T) :
    FollowerReleaseFinishMeasurability.finishRoundResultOfCode rate
        (carriedStateBuffer state)
        (finishRoundResultCodeAtComponents rate state memory row time) =
      ActiveFollowerLifecycle.finishRound rate.eta time row
        (reconstructCarriedState state.1 state.2) (localMemoryOfCode memory) := by
  cases state with
  | mk index values =>
      exact FollowerReleaseFinishMeasurability.finishRoundResultCodeAt_reconstruct
        rate row time index.1 memory index.2.2 values

/-- Exact pending-release reconstruction uses both independently supplied
carried states, including their separate original scalar families. -/
theorem releaseAfterServiceResultCodeAtComponents_reconstruct {p : Parameters}
    (rate : RateInput p) (i : Fin (p.m - 1))
    (preChoice postService : CarriedState p rate)
    (memory : LocalMemoryCode p) (row : CompletePublicTable.CompleteRow p)
    (time : Fin p.T) (feedback : Fin (D p + 1)) :
    FollowerLifecycleMeasurability.releaseAfterServiceResultOfCode rate
        (carriedStateBuffer postService)
        (releaseAfterServiceResultCodeAtComponents rate i preChoice postService memory
          row time feedback) =
      ActiveFollowerLifecycle.releaseAfterService rate.eta i time
        (ActiveFollowerLifecycle.publicRowOfCompleteRow row time)
        (FollowerDownMeasurability.feedbackAtGrid p feedback)
        (reconstructCarriedState preChoice.1 preChoice.2)
        (reconstructCarriedState postService.1 postService.2) := by
  cases preChoice with
  | mk preIndex preValues =>
    cases postService with
    | mk postIndex postValues =>
      exact FollowerReleaseFinishMeasurability.releaseAfterServiceResultCodeAt_reconstruct
        rate i row time feedback preIndex.1 postIndex.1 preIndex.2.2 postIndex.2.2
        preValues postValues

/-- Exact combined reconstruction retains both distinct input buffers and
decodes the complete original post-service buffer on every success path. -/
theorem releaseAndFinishResultCodeAtComponents_reconstruct {p : Parameters}
    (rate : RateInput p) (i : Fin (p.m - 1))
    (preChoice postService : CarriedState p rate)
    (memory : LocalMemoryCode p) (row : CompletePublicTable.CompleteRow p)
    (time : Fin p.T) (feedback : Fin (D p + 1)) :
    FollowerLifecycleMeasurability.releaseAndFinishResultOfCode rate
        (carriedStateBuffer postService)
        (releaseAndFinishResultCodeAtComponents rate i preChoice postService memory
          row time feedback) =
      DeclaredFollowerLocalRound.releaseAndFinish rate i row time
        (FollowerDownMeasurability.feedbackAtGrid p feedback)
        (reconstructCarriedState preChoice.1 preChoice.2)
        (localMemoryOfCode memory)
        (reconstructCarriedState postService.1 postService.2) := by
  cases preChoice with
  | mk preIndex preValues =>
    cases postService with
    | mk postIndex postValues =>
      exact FollowerReleaseFinishMeasurability.releaseAndFinishResultCodeAt_reconstruct
        rate i row time feedback preIndex.1 postIndex.1 memory preIndex.2.2
        postIndex.2.2 preValues postValues

/-- The full carried finish decoder agrees with the accepted result-code
decoder, including every one of the six lifecycle failures. -/
theorem reconstructFinishRoundCarriedOutput_eq_codeDecoder {p : Parameters}
    (rate : RateInput p) (state : CarriedState p rate)
    (code : FinishRoundResultCode p rate) :
    reconstructFinishRoundCarriedOutput (finishRoundCarriedOutput state code) =
      FollowerReleaseFinishMeasurability.finishRoundResultOfCode rate
        (carriedStateBuffer state) code := by
  cases code with
  | failure reason => simp [finishRoundCarriedOutput, reconstructFinishRoundCarriedOutput,
      FollowerReleaseFinishMeasurability.finishRoundResultOfCode]
  | success stateCode memoryCode =>
      simp [finishRoundCarriedOutput, reconstructFinishRoundCarriedOutput,
        carriedStateWithStateCode, carriedStateBuffer, reconstructCarriedState,
        FollowerReleaseFinishMeasurability.finishRoundResultOfCode,
        FollowerDownJointMeasurability.bufferFromSkeletonAndScalars]

/-- The full release decoder agrees with the accepted result-code decoder,
preserving the unchanged post-service buffer and every failure. -/
theorem reconstructReleaseAfterServiceCarriedOutput_eq_codeDecoder {p : Parameters}
    (rate : RateInput p) (postService : CarriedState p rate)
    (code : ReleaseAfterServiceResultCode p rate) :
    reconstructReleaseAfterServiceCarriedOutput
        (releaseAfterServiceCarriedOutput postService code) =
      FollowerLifecycleMeasurability.releaseAfterServiceResultOfCode rate
        (carriedStateBuffer postService) code := by
  cases code with
  | failure reason => simp [releaseAfterServiceCarriedOutput,
      reconstructReleaseAfterServiceCarriedOutput,
      FollowerLifecycleMeasurability.releaseAfterServiceResultOfCode]
  | success stateCode =>
      simp [releaseAfterServiceCarriedOutput, reconstructReleaseAfterServiceCarriedOutput,
        carriedStateWithStateCode, carriedStateBuffer, reconstructCarriedState,
        FollowerLifecycleMeasurability.releaseAfterServiceResultOfCode,
        FollowerDownJointMeasurability.bufferFromSkeletonAndScalars]

/-- The full combined decoder agrees with the accepted result-code decoder,
including source-stage failure tags and all output buffer coordinates. -/
theorem reconstructReleaseAndFinishCarriedOutput_eq_codeDecoder {p : Parameters}
    (rate : RateInput p) (postService : CarriedState p rate)
    (code : ReleaseAndFinishResultCode p rate) :
    reconstructReleaseAndFinishCarriedOutput
        (releaseAndFinishCarriedOutput postService code) =
      FollowerLifecycleMeasurability.releaseAndFinishResultOfCode rate
        (carriedStateBuffer postService) code := by
  cases code with
  | failure reason => simp [releaseAndFinishCarriedOutput,
      reconstructReleaseAndFinishCarriedOutput,
      FollowerLifecycleMeasurability.releaseAndFinishResultOfCode]
  | success stateCode memoryCode =>
      simp [releaseAndFinishCarriedOutput, reconstructReleaseAndFinishCarriedOutput,
        carriedStateWithStateCode, carriedStateBuffer, reconstructCarriedState,
        FollowerLifecycleMeasurability.releaseAndFinishResultOfCode,
        FollowerDownJointMeasurability.bufferFromSkeletonAndScalars]

/-- Full finish output reconstruction gives the existing operation itself,
with no deletion of invalid-domain or proposal-read error branches. -/
theorem finishRoundCarriedOutputAtComponents_reconstruct {p : Parameters}
    (rate : RateInput p) (state : CarriedState p rate)
    (memory : LocalMemoryCode p) (row : CompletePublicTable.CompleteRow p)
    (time : Fin p.T) :
    reconstructFinishRoundCarriedOutput
        (finishRoundCarriedOutput state
          (finishRoundResultCodeAtComponents rate state memory row time)) =
      ActiveFollowerLifecycle.finishRound rate.eta time row
        (reconstructCarriedState state.1 state.2) (localMemoryOfCode memory) := by
  rw [reconstructFinishRoundCarriedOutput_eq_codeDecoder]
  exact finishRoundResultCodeAtComponents_reconstruct rate state memory row time

/-- Full pending-release output reconstructs the existing operation and
retains its literal missing, stale, and all other release checks. -/
theorem releaseAfterServiceCarriedOutputAtComponents_reconstruct {p : Parameters}
    (rate : RateInput p) (i : Fin (p.m - 1))
    (preChoice postService : CarriedState p rate)
    (memory : LocalMemoryCode p) (row : CompletePublicTable.CompleteRow p)
    (time : Fin p.T) (feedback : Fin (D p + 1)) :
    reconstructReleaseAfterServiceCarriedOutput
        (releaseAfterServiceCarriedOutput postService
          (releaseAfterServiceResultCodeAtComponents rate i preChoice postService memory
            row time feedback)) =
      ActiveFollowerLifecycle.releaseAfterService rate.eta i time
        (ActiveFollowerLifecycle.publicRowOfCompleteRow row time)
        (FollowerDownMeasurability.feedbackAtGrid p feedback)
        (reconstructCarriedState preChoice.1 preChoice.2)
        (reconstructCarriedState postService.1 postService.2) := by
  rw [reconstructReleaseAfterServiceCarriedOutput_eq_codeDecoder]
  exact releaseAfterServiceResultCodeAtComponents_reconstruct rate i preChoice postService
    memory row time feedback

/-- Full combined output reconstructs the exact checked local round and
preserves every continuous coordinate of each independent input buffer. -/
theorem releaseAndFinishCarriedOutputAtComponents_reconstruct {p : Parameters}
    (rate : RateInput p) (i : Fin (p.m - 1))
    (preChoice postService : CarriedState p rate)
    (memory : LocalMemoryCode p) (row : CompletePublicTable.CompleteRow p)
    (time : Fin p.T) (feedback : Fin (D p + 1)) :
    reconstructReleaseAndFinishCarriedOutput
        (releaseAndFinishCarriedOutput postService
          (releaseAndFinishResultCodeAtComponents rate i preChoice postService memory
            row time feedback)) =
      DeclaredFollowerLocalRound.releaseAndFinish rate i row time
        (FollowerDownMeasurability.feedbackAtGrid p feedback)
        (reconstructCarriedState preChoice.1 preChoice.2)
        (localMemoryOfCode memory)
        (reconstructCarriedState postService.1 postService.2) := by
  rw [reconstructReleaseAndFinishCarriedOutput_eq_codeDecoder]
  exact releaseAndFinishResultCodeAtComponents_reconstruct rate i preChoice postService
    memory row time feedback

/-- Same current `TimeControl`, equal local finish inputs, and equal time give
the same faithful varying-carried-state finish adapter. -/
theorem finishRoundResultCodeAtComponents_eq_of_currentTimeControl_eq {p : Parameters}
    (rate : RateInput p) (state : CarriedState p rate)
    (memory : LocalMemoryCode p) (row row' : CompletePublicTable.CompleteRow p)
    (time : Fin p.T) (hcurrent : row.2 time = row'.2 time) :
    finishRoundResultCodeAtComponents rate state memory row time =
      finishRoundResultCodeAtComponents rate state memory row' time := by
  cases state with
  | mk index values =>
      exact FollowerReleaseFinishMeasurability.finishRoundResultCodeAt_eq_of_currentTimeControl_eq
        rate index.1 memory index.2.2 row row' time values hcurrent

/-- Same current `TimeControl`, equal two-state local inputs, and equal time
give the same faithful varying-carried-state pending-release adapter. -/
theorem releaseAfterServiceResultCodeAtComponents_eq_of_currentTimeControl_eq
    {p : Parameters} (rate : RateInput p) (i : Fin (p.m - 1))
    (preChoice postService : CarriedState p rate) (memory : LocalMemoryCode p)
    (row row' : CompletePublicTable.CompleteRow p) (time : Fin p.T)
    (feedback : Fin (D p + 1)) (hcurrent : row.2 time = row'.2 time) :
    releaseAfterServiceResultCodeAtComponents rate i preChoice postService memory
      row time feedback =
    releaseAfterServiceResultCodeAtComponents rate i preChoice postService memory
      row' time feedback := by
  cases preChoice with
  | mk preIndex preValues =>
    cases postService with
    | mk postIndex postValues =>
      exact FollowerReleaseFinishMeasurability.releaseAfterServiceResultCodeAt_eq_of_currentTimeControl_eq
        rate i preIndex.1 postIndex.1 time preIndex.2.2 postIndex.2.2 row row'
        feedback preValues postValues hcurrent

/-- Same current `TimeControl`, equal local state/memory/feedback inputs,
and equal time give the same faithful varying-state combined adapter. -/
theorem releaseAndFinishResultCodeAtComponents_eq_of_currentTimeControl_eq
    {p : Parameters} (rate : RateInput p) (i : Fin (p.m - 1))
    (preChoice postService : CarriedState p rate) (memory : LocalMemoryCode p)
    (row row' : CompletePublicTable.CompleteRow p) (time : Fin p.T)
    (feedback : Fin (D p + 1)) (hcurrent : row.2 time = row'.2 time) :
    releaseAndFinishResultCodeAtComponents rate i preChoice postService memory
      row time feedback =
    releaseAndFinishResultCodeAtComponents rate i preChoice postService memory
      row' time feedback := by
  cases preChoice with
  | mk preIndex preValues =>
    cases postService with
    | mk postIndex postValues =>
      exact FollowerReleaseFinishMeasurability.releaseAndFinishResultCodeAt_eq_of_currentTimeControl_eq
        rate i preIndex.1 postIndex.1 memory time preIndex.2.2 postIndex.2.2
        row row' feedback preValues postValues hcurrent

/-- The full finish output inherits the accepted current-time dependence
with the identical original buffer retained. -/
theorem finishRoundCarriedOutputAtComponents_eq_of_currentTimeControl_eq
    {p : Parameters} (rate : RateInput p) (state : CarriedState p rate)
    (memory : LocalMemoryCode p) (row row' : CompletePublicTable.CompleteRow p)
    (time : Fin p.T) (hcurrent : row.2 time = row'.2 time) :
    finishRoundCarriedOutput state (finishRoundResultCodeAtComponents rate state memory row time) =
      finishRoundCarriedOutput state (finishRoundResultCodeAtComponents rate state memory row' time) := by
  exact congrArg (finishRoundCarriedOutput state)
    (finishRoundResultCodeAtComponents_eq_of_currentTimeControl_eq rate state memory
      row row' time hcurrent)

/-- The full release output inherits same-current-`TimeControl` dependence
without restricting or replacing either carried input state. -/
theorem releaseAfterServiceCarriedOutputAtComponents_eq_of_currentTimeControl_eq
    {p : Parameters} (rate : RateInput p) (i : Fin (p.m - 1))
    (preChoice postService : CarriedState p rate) (memory : LocalMemoryCode p)
    (row row' : CompletePublicTable.CompleteRow p) (time : Fin p.T)
    (feedback : Fin (D p + 1)) (hcurrent : row.2 time = row'.2 time) :
    releaseAfterServiceCarriedOutput postService
        (releaseAfterServiceResultCodeAtComponents rate i preChoice postService memory
          row time feedback) =
      releaseAfterServiceCarriedOutput postService
        (releaseAfterServiceResultCodeAtComponents rate i preChoice postService memory
          row' time feedback) := by
  exact congrArg (releaseAfterServiceCarriedOutput postService)
    (releaseAfterServiceResultCodeAtComponents_eq_of_currentTimeControl_eq
      rate i preChoice postService memory row row' time feedback hcurrent)

/-- The full combined output inherits same-current-`TimeControl` dependence
for identical local inputs and retains the original post-service buffer. -/
theorem releaseAndFinishCarriedOutputAtComponents_eq_of_currentTimeControl_eq
    {p : Parameters} (rate : RateInput p) (i : Fin (p.m - 1))
    (preChoice postService : CarriedState p rate) (memory : LocalMemoryCode p)
    (row row' : CompletePublicTable.CompleteRow p) (time : Fin p.T)
    (feedback : Fin (D p + 1)) (hcurrent : row.2 time = row'.2 time) :
    releaseAndFinishCarriedOutput postService
        (releaseAndFinishResultCodeAtComponents rate i preChoice postService memory
          row time feedback) =
      releaseAndFinishCarriedOutput postService
        (releaseAndFinishResultCodeAtComponents rate i preChoice postService memory
          row' time feedback) := by
  exact congrArg (releaseAndFinishCarriedOutput postService)
    (releaseAndFinishResultCodeAtComponents_eq_of_currentTimeControl_eq
      rate i preChoice postService memory row row' time feedback hcurrent)

end Bandits.Support.FollowerReleaseFinishJointMeasurability
