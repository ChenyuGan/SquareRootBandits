/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.DeclaredFollowerLocalRound
public import Bandits.Support.FollowerVaryingActivationMeasurability
public import Bandits.Support.FollowerReleaseFinishJointMeasurability

/-!
# Measurable composition of a declared follower's observation

This module composes the accepted logging/service/DOWN observation decoder
with the accepted joint release/finish decoder. It retains the input
choice-state snapshot separately from the returned post-service/DOWN state,
uses the original bounded feedback grid and complete row, and carries the
entire ordered buffer skeleton and its continuous scalar family.

Sources: `sources/zip4/manuscript/appendix_a_local_protocol.tex:6-14`,
`sources/zip4/manuscript/07_public_setup.tex:55-114`, and
`sources/zip4/manuscript/06_interruptions.tex:235-296`.
These are internal local-input results. They assert no physical feedback
provenance, history condition, whole-round/run measurability, or manuscript
theorem closure.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.DeclaredFollowerObservationMeasurability

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.CompletePublicTable
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.FollowerDownMeasurability
open Bandits.Support.FollowerDownJointMeasurability
open Bandits.Support.FollowerLoggingDownMeasurability
open Bandits.Support.FollowerServiceMeasurability
open Bandits.Support.ActiveFollowerLogging
open Bandits.Support.FollowerObservationStageMeasurabilityRepair
open Bandits.Support.FollowerVaryingActivationMeasurability
open Bandits.Support.FollowerReleaseFinishJointMeasurability
open Bandits.Support.FollowerLifecycleMeasurability
open Bandits.Support.DeclaredFollowerLocalRound
open Bandits.Support.SparseCalendarReplay

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ActiveFollowerDownAcceptance.RateInput
abbrev CarriedState (p : Parameters) (rate : RateInput p) :=
  FollowerObservationStageMeasurabilityRepair.CarriedState p rate
abbrev SavedScalarFamily (n : ℕ) := FollowerDownMeasurability.SavedScalarFamily n
abbrev LocalMemoryCode (p : Parameters) :=
  FollowerLifecycleMeasurability.LocalMemoryCode p
abbrev IncomingConfiguration (p : Parameters) (rate : RateInput p) :=
  FollowerPrepareJointMeasurability.IncomingConfiguration p rate
abbrev ObserveOrdinaryCarriedOutput (p : Parameters) (rate : RateInput p) :=
  FollowerReleaseFinishJointMeasurability.ReleaseAndFinishCarriedOutput p rate

private abbrev CarryIndex (p : Parameters) (rate : RateInput p) :=
  FollowerObservationStageMeasurabilityRepair.FollowerCarryIndex p rate
private abbrev ObservationFiber (p : Parameters) (rate : RateInput p)
    (activation : Activation p) :=
  FollowerObservationStageMeasurabilityRepair.ObservationInput p rate activation
abbrev FollowerActiveCalendarTime (p : Parameters) (activation : Activation p) :=
  FollowerLifecycleMeasurability.ActiveCalendarTime p activation

def activeCalendarTimeOnFiberLocal {p : Parameters} {Ω : Type*}
    (activation : Ω → Activation p) (calendarIndex : Ω → Fin p.T)
    (valid : ∀ ω, (activation ω).val ≤ (calendarIndex ω).val + 1)
    (label : Activation p) (ω : {ω : Ω // activation ω = label}) :
    FollowerActiveCalendarTime p label :=
  ⟨calendarIndex ω.1, by simpa only [ω.2] using valid ω.1⟩

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

private theorem measurable_from_countable_left {α β γ : Type*}
    [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace β] [MeasurableSpace γ]
    (f : α × β → γ)
    (hf : ∀ a, Measurable (fun b => f (a, b))) : Measurable f := by
  intro s hs
  have hdecomp : f ⁻¹' s =
      ⋃ a : α, ({a} ×ˢ ((fun b => f (a, b)) ⁻¹' s)) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_prod, Set.mem_singleton_iff]
    constructor
    · intro hx
      exact ⟨x.1, rfl, hx⟩
    · rintro ⟨a, rfl, hx⟩
      exact hx
  rw [hdecomp]
  exact MeasurableSet.iUnion fun a =>
    (measurableSet_singleton a).prod (hf a hs)

abbrev ObservationKey (p : Parameters) := ℕ × Fin p.K
abbrev SavedScalar := FollowerDownMeasurability.SavedScalar

def appendSavedScalarFamily {n : ℕ}
    (values : SavedScalarFamily n) (last : SavedScalar) : SavedScalarFamily (n + 1) :=
  Fin.lastCases last values

private theorem measurable_appendSavedScalarFamily {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (values : Ω → SavedScalarFamily n) (last : Ω → SavedScalar)
    (hvalues : Measurable values) (hlast : Measurable last) :
    Measurable (fun ω => appendSavedScalarFamily (values ω) (last ω)) := by
  apply measurable_pi_iff.mpr
  intro j
  induction j using Fin.lastCases with
  | cast j =>
      have hvalue : Measurable (fun ω => values ω j) := by
        convert (measurable_pi_apply j).comp hvalues using 1; rfl
      simpa only [appendSavedScalarFamily, Fin.lastCases_castSucc] using hvalue
  | last =>
      simpa [appendSavedScalarFamily] using hlast

def appendCarriedState {p : Parameters} {rate : RateInput p}
    (state : CarriedState p rate)
    (stateCode : FollowerDownMeasurability.FollowerStateCode p rate)
    (key : ObservationKey p) (saved : SavedScalar) : CarriedState p rate :=
  ⟨(stateCode,
      ⟨state.1.2.1 + 1, Fin.lastCases key (fun j => state.1.2.2 j)⟩),
    appendSavedScalarFamily state.2 saved⟩

def emptyCarriedState {p : Parameters} {rate : RateInput p}
    (stateCode : FollowerDownMeasurability.FollowerStateCode p rate) :
    CarriedState p rate :=
  ⟨(stateCode, ⟨0, fun j => Fin.elim0 j⟩), fun j => Fin.elim0 j⟩

private theorem measurable_carriedStateWithStateCode {p : Parameters}
    {rate : RateInput p} (stateCode : FollowerDownMeasurability.FollowerStateCode p rate) :
    Measurable (fun state : CarriedState p rate =>
      FollowerReleaseFinishJointMeasurability.carriedStateWithStateCode state stateCode) := by
  apply measurable_of_sigma_sections
  intro index
  exact (measurable_sigmaMk (stateCode, index.2)).comp measurable_id

private def appendPayloadToCarriedState {p : Parameters} {rate : RateInput p}
    (index : CarryIndex p rate)
    (stateCode : FollowerDownMeasurability.FollowerStateCode p rate)
    (x : Sigma fun _key : ObservationKey p => SavedScalarFamily (index.2.1 + 1)) :
    CarriedState p rate :=
  ⟨(stateCode,
      ⟨index.2.1 + 1, Fin.lastCases x.1 (fun j => index.2.2 j)⟩), x.2⟩

private theorem measurable_appendPayloadToCarriedState {p : Parameters}
    {rate : RateInput p} (index : CarryIndex p rate)
    (stateCode : FollowerDownMeasurability.FollowerStateCode p rate) :
    Measurable (appendPayloadToCarriedState index stateCode) := by
  apply measurable_of_sigma_sections
  intro key
  let extended : CarryIndex p rate :=
    (stateCode, ⟨index.2.1 + 1, Fin.lastCases key (fun j => index.2.2 j)⟩)
  exact measurable_sigmaMk (α := CarryIndex p rate)
    (β := fun x : CarryIndex p rate => SavedScalarFamily x.2.1)
    extended

private theorem measurable_appendCarriedState {p : Parameters}
    {rate : RateInput p} {Ω : Type*} [MeasurableSpace Ω]
    (state : Ω → CarriedState p rate)
    (stateCode : FollowerDownMeasurability.FollowerStateCode p rate)
    (key : Ω → ObservationKey p) (saved : Ω → SavedScalar)
    (hstate : Measurable state) (hkey : Measurable key) (hsaved : Measurable saved) :
    Measurable (fun ω => appendCarriedState (state ω) stateCode (key ω) (saved ω)) := by
  let rest := (ObservationKey p) × SavedScalar
  have hassemble : Measurable (fun ω =>
      (⟨(state ω).1, ((state ω).2, (key ω, saved ω))⟩ :
        Sigma fun index : CarryIndex p rate =>
          SavedScalarFamily index.2.1 × rest)) := by
    exact measurable_assembleSigmaProduct.comp
      (hstate.prodMk (hkey.prodMk hsaved))
  have hfiber (index : CarryIndex p rate) :
      Measurable (fun x : SavedScalarFamily index.2.1 × rest =>
        appendCarriedState (⟨index, x.1⟩ : CarriedState p rate)
          stateCode x.2.1 x.2.2) := by
    let label : SavedScalarFamily index.2.1 × rest → ObservationKey p :=
      fun x => x.2.1
    have hlabel : Measurable label := measurable_fst.comp (measurable_snd.comp measurable_id)
    let fiber : ∀ a : ObservationKey p,
        {x : SavedScalarFamily index.2.1 × rest // label x = a} →
          SavedScalarFamily (index.2.1 + 1) :=
      fun _ x => appendSavedScalarFamily x.1.1 x.1.2.2
    have hfiber (a : ObservationKey p) : Measurable (fiber a) := by
      have hvalues : Measurable (fun x : {x : SavedScalarFamily index.2.1 × rest //
          label x = a} => x.1.1) :=
        (measurable_fst.comp measurable_subtype_coe)
      have hlast : Measurable (fun x : {x : SavedScalarFamily index.2.1 × rest //
          label x = a} => x.1.2.2) :=
        (measurable_snd.comp (measurable_snd.comp measurable_subtype_coe))
      exact measurable_appendSavedScalarFamily _ _ hvalues hlast
    have hpayload := measurable_activationDependentAssembly label hlabel fiber hfiber
    have hmap := (measurable_appendPayloadToCarriedState index stateCode).comp hpayload
    have hfactor :
        (fun x : SavedScalarFamily index.2.1 × rest =>
          appendCarriedState (⟨index, x.1⟩ : CarriedState p rate)
            stateCode x.2.1 x.2.2) =
        appendPayloadToCarriedState index stateCode ∘
          (fun x : SavedScalarFamily index.2.1 × rest =>
            (⟨x.2.1, appendSavedScalarFamily x.1 x.2.2⟩ :
              Sigma fun a : ObservationKey p => SavedScalarFamily (index.2.1 + 1))) := by
      funext x
      rcases x with ⟨values, key, saved⟩
      simp [Function.comp, appendCarriedState, appendPayloadToCarriedState]
    rw [hfactor]
    exact hmap
  have hsection := measurable_of_sigma_sections
    (f := fun x : Sigma fun index : CarryIndex p rate =>
        SavedScalarFamily index.2.1 × rest =>
      appendCarriedState (⟨x.1, x.2.1⟩ : CarriedState p rate)
        stateCode x.2.2.1 x.2.2.2) hfiber
  have htarget : (fun ω =>
      appendCarriedState (state ω) stateCode (key ω) (saved ω)) =
    (fun x : Sigma fun index : CarryIndex p rate =>
        SavedScalarFamily index.2.1 × rest =>
      appendCarriedState (⟨x.1, x.2.1⟩ : CarriedState p rate)
        stateCode x.2.2.1 x.2.2.2) ∘
      (fun ω => (⟨(state ω).1, ((state ω).2, (key ω, saved ω))⟩ :
        Sigma fun index : CarryIndex p rate => SavedScalarFamily index.2.1 × rest)) := by
    funext ω
    rfl
  rw [htarget]
  exact hsection.comp hassemble

def currentSavedScalar {p : Parameters} (row : CompleteRow p)
    (time : Fin p.T) (feedback : Fin (D p + 1)) : SavedScalar :=
  ((FollowerDownMeasurability.feedbackAtGrid p feedback).val,
    (row.2 time).1 ContinuousControlSlice.Label.thin)

private theorem measurable_finIndex_eval {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] (n : ℕ) (f : Fin n → α → β)
    (hf : ∀ j, Measurable (f j)) :
    Measurable (fun z : α × Fin n => f z.2 z.1) := by
  intro s hs
  have hpre : (fun z : α × Fin n => f z.2 z.1) ⁻¹' s =
      ⋃ j : Fin n, {z | z.2 = j} ∩ {z | f j z.1 ∈ s} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff,
      Set.mem_ofPred_eq]
    constructor
    · intro hz
      exact ⟨z.2, rfl, hz⟩
    · rintro ⟨j, hj, hz⟩
      rw [hj]
      exact hz
  rw [hpre]
  exact MeasurableSet.iUnion fun j => by
    have hindex : MeasurableSet {z : α × Fin n | z.2 = j} :=
      (measurableSet_singleton j).preimage measurable_snd
    have hvalue : MeasurableSet {z : α × Fin n | f j z.1 ∈ s} :=
      ((hf j).comp measurable_fst) hs
    exact hindex.inter hvalue

private theorem measurable_currentSavedScalar {p : Parameters}
    {Ω : Type*} [MeasurableSpace Ω]
    (row : Ω → CompleteRow p) (time : Ω → Fin p.T)
    (feedback : Ω → Fin (D p + 1))
    (hrow : Measurable row) (htime : Measurable time)
    (hfeedback : Measurable feedback) :
    Measurable (fun ω => currentSavedScalar (row ω) (time ω) (feedback ω)) := by
  have hlearning : Measurable (fun ω => CompletePublicTable.completeRowLearning p (row ω)) :=
    (CompletePublicTable.measurable_completeRowLearning p).comp hrow
  have hthinAt (t : Fin p.T) : Measurable (fun learning : ContinuousLearningRows.LearningRow p =>
      ContinuousLearningRows.scalarAt t ContinuousControlSlice.Label.thin learning) :=
    ContinuousLearningRows.measurable_scalarAt t ContinuousControlSlice.Label.thin
  have hthin : Measurable (fun ω =>
      ContinuousLearningRows.scalarAt (time ω) ContinuousControlSlice.Label.thin
        (CompletePublicTable.completeRowLearning p (row ω))) := by
    exact (measurable_finIndex_eval
      (α := ContinuousLearningRows.LearningRow p) p.T
      (fun t learning => ContinuousLearningRows.scalarAt t
        ContinuousControlSlice.Label.thin learning) hthinAt).comp
        (hlearning.prodMk htime)
  have hfeedbackValue : Measurable (fun ω =>
      (FollowerDownMeasurability.feedbackAtGrid p (feedback ω)).val) :=
    (measurable_subtype_coe.comp
      (FollowerDownMeasurability.measurable_feedbackAtGrid p)).comp hfeedback
  exact hfeedbackValue.prodMk hthin

private theorem measurable_currentObservationKey {p : Parameters}
    {Ω : Type*} [MeasurableSpace Ω]
    (time : Ω → Fin p.T) (arm : Ω → Fin p.K)
    (htime : Measurable time) (harm : Measurable arm) :
    Measurable (fun ω => ((time ω).val + 1, arm ω) : Ω → ObservationKey p) := by
  have hround : Measurable (fun ω => (time ω).val + 1) :=
    (measurable_of_countable (fun t : Fin p.T => t.val + 1)).comp htime
  exact hround.prodMk harm

def firstStageCarriedResult {p : Parameters} {rate : RateInput p}
    (code : ObservationResultCode p rate)
    (carry : CarriedState p rate) (key : ObservationKey p) (saved : SavedScalar) :
    RoundFailure ⊕ CarriedState p rate := by
  match code with
  | .unoccupied (.loggingFailure reason) =>
      exact .inl (.logging (FollowerLoggingDownMeasurability.loggingFailureOfCode reason))
  | .unoccupied (.down result) =>
      match result with
      | .skipped before _ =>
          exact .inr (FollowerReleaseFinishJointMeasurability.carriedStateWithStateCode
            carry before)
      | .inputFailure _ reason =>
          exact .inl (.downInput (FollowerDownMeasurability.inputFailureOfCode reason))
      | .decodeOrParseRejected _ after _ =>
          exact .inr (FollowerReleaseFinishJointMeasurability.carriedStateWithStateCode
            carry after)
      | .parsedButUnaccepted _ after _ _ =>
          exact .inr (FollowerReleaseFinishJointMeasurability.carriedStateWithStateCode
            carry after)
      | .outputFailure _ reason =>
          exact .inl (.downOutput (FollowerDownMeasurability.outputFailureOfCode reason))
      | .accepted _ after _ _ _ _ _ => exact .inr (emptyCarriedState after)
  | .unoccupied (.logged state recipe) =>
      match recipe with
      | .retained =>
          exact .inr (FollowerReleaseFinishJointMeasurability.carriedStateWithStateCode
            carry state)
      | .appendedCurrent => exact .inr (appendCarriedState carry state key saved)
      | .cleared => exact .inr (emptyCarriedState state)
  | .occupied .serviceFailure => exact .inl .service
  | .occupied (.success _ _ state) =>
      exact .inr (FollowerReleaseFinishJointMeasurability.carriedStateWithStateCode
        carry state)

private theorem measurable_firstStageCarriedResult {p : Parameters}
    {rate : RateInput p} {Ω : Type*} [MeasurableSpace Ω]
    (code : Ω → ObservationResultCode p rate)
    (carry : Ω → CarriedState p rate) (key : Ω → ObservationKey p)
    (saved : Ω → SavedScalar)
    (hcode : Measurable code) (hcarry : Measurable carry)
    (hkey : Measurable key) (hsaved : Measurable saved) :
    Measurable (fun ω => firstStageCarriedResult (code ω)
      (carry ω) (key ω) (saved ω)) := by
  have hsections (c : ObservationResultCode p rate) :
      Measurable (fun z : CarriedState p rate ×
          (ObservationKey p × SavedScalar) =>
        firstStageCarriedResult c z.1 z.2.1 z.2.2) := by
    cases c with
    | unoccupied code =>
      cases code with
      | loggingFailure reason => exact measurable_const
      | down result =>
        cases result with
        | skipped before reason =>
          exact measurable_inr.comp
            ((measurable_carriedStateWithStateCode (rate := rate) before).comp measurable_fst)
        | inputFailure before reason => exact measurable_const
        | decodeOrParseRejected before after raw =>
          exact measurable_inr.comp
            ((measurable_carriedStateWithStateCode (rate := rate) after).comp measurable_fst)
        | parsedButUnaccepted before after raw reply =>
          exact measurable_inr.comp
            ((measurable_carriedStateWithStateCode (rate := rate) after).comp measurable_fst)
        | outputFailure before reason => exact measurable_const
        | accepted before after raw reply scan registers service => exact measurable_const
      | logged state recipe =>
        cases recipe with
        | retained =>
          exact measurable_inr.comp
            ((measurable_carriedStateWithStateCode (rate := rate) state).comp measurable_fst)
        | appendedCurrent =>
          exact measurable_inr.comp
            (measurable_appendCarriedState (fun z : CarriedState p rate ×
                (ObservationKey p × SavedScalar) => z.1) state
              (fun z => z.2.1) (fun z => z.2.2)
              measurable_fst (measurable_fst.comp measurable_snd)
              (measurable_snd.comp measurable_snd))
        | cleared => exact measurable_const
    | occupied code =>
      cases code with
      | serviceFailure => exact measurable_const
      | success arrival service state =>
        exact measurable_inr.comp
          ((measurable_carriedStateWithStateCode (rate := rate) state).comp measurable_fst)
  have hcodeSections : Measurable (fun z : ObservationResultCode p rate ×
      (CarriedState p rate × (ObservationKey p × SavedScalar)) =>
      firstStageCarriedResult z.1 z.2.1 z.2.2.1 z.2.2.2) :=
    measurable_from_countable_left
      (fun z : ObservationResultCode p rate ×
          (CarriedState p rate × (ObservationKey p × SavedScalar)) =>
        firstStageCarriedResult z.1 z.2.1 z.2.2.1 z.2.2.2) hsections
  exact hcodeSections.comp (hcode.prodMk (hcarry.prodMk (hkey.prodMk hsaved)))

private def reconstructFirstStageCarriedResult {p : Parameters} {rate : RateInput p}
    (result : RoundFailure ⊕ CarriedState p rate) :
    Except RoundFailure (ReferencePrelaunchFollower.State p rate.eta) :=
  Sum.elim Except.error
    (fun state => Except.ok
      (FollowerObservationStageMeasurabilityRepair.reconstructCarriedState
        state.1 state.2)) result

private theorem reconstruct_carriedStateWithStateCode {p : Parameters}
    {rate : RateInput p} (carry : CarriedState p rate)
    (stateCode : FollowerDownMeasurability.FollowerStateCode p rate) :
    FollowerObservationStageMeasurabilityRepair.reconstructCarriedState
        (FollowerReleaseFinishJointMeasurability.carriedStateWithStateCode carry stateCode).1
        (FollowerReleaseFinishJointMeasurability.carriedStateWithStateCode carry stateCode).2 =
      FollowerDownMeasurability.followerStateOfCode rate stateCode
        (FollowerObservationStageMeasurabilityRepair.carriedStateBuffer carry) := by
  cases carry with
  | mk index values => rfl

private theorem reconstruct_emptyCarriedState {p : Parameters}
    {rate : RateInput p} (stateCode : FollowerDownMeasurability.FollowerStateCode p rate) :
    FollowerObservationStageMeasurabilityRepair.reconstructCarriedState
        (emptyCarriedState stateCode).1 (emptyCarriedState stateCode).2 =
      FollowerDownMeasurability.followerStateOfCode rate stateCode [] := by
  simp [emptyCarriedState,
    FollowerObservationStageMeasurabilityRepair.reconstructCarriedState,
    FollowerDownJointMeasurability.bufferFromSkeletonAndScalars]

private theorem reconstruct_appendCarriedState {p : Parameters}
    {rate : RateInput p} (carry : CarriedState p rate)
    (stateCode : FollowerDownMeasurability.FollowerStateCode p rate)
    (key : ObservationKey p) (saved : SavedScalar) :
    FollowerObservationStageMeasurabilityRepair.reconstructCarriedState
        (appendCarriedState carry stateCode key saved).1
        (appendCarriedState carry stateCode key saved).2 =
      FollowerDownMeasurability.followerStateOfCode rate stateCode
        (FollowerObservationStageMeasurabilityRepair.carriedStateBuffer carry ++
          [⟨key.1, key.2, saved.1, saved.2⟩]) := by
  rcases carry with ⟨⟨stateCode₀, ⟨n, skeleton⟩⟩, values⟩
  simp only [FollowerObservationStageMeasurabilityRepair.reconstructCarriedState,
    appendCarriedState,
    FollowerObservationStageMeasurabilityRepair.carriedStateBuffer]
  congr 1
  change FollowerDownJointMeasurability.bufferFromSkeletonAndScalars
      (Fin.lastCases key skeleton)
      (Fin.lastCases saved values) =
    FollowerDownJointMeasurability.bufferFromSkeletonAndScalars skeleton values ++
      [⟨key.1, key.2, saved.1, saved.2⟩]
  simp only [FollowerDownJointMeasurability.bufferFromSkeletonAndScalars]
  rw [List.ofFn_succ']
  simp_rw [Fin.lastCases_castSucc, Fin.lastCases_last]
  simp only [List.concat_eq_append]

/-! Decoding the retained first-stage code reconstructs its exact carried
state or tagged failure. Rejected and parsed-but-unaccepted DOWN branches use
their decoded returned state, while accepted DOWN carries the cleared buffer. -/
private theorem firstStageCarriedResult_reconstructs
    {p : Parameters} (rate : RateInput p) (i : Fin (p.m - 1))
    (activation : Activation p) (carry : CarriedState p rate)
    (row : CompleteRow p) (time : FollowerActiveCalendarTime p activation)
    (feedback : Fin (D p + 1)) (arm : Fin p.K)
    (code : ObservationResultCode p rate) :
    reconstructFirstStageCarriedResult
        (firstStageCarriedResult code carry
          ((time.1.val + 1, arm)) (currentSavedScalar row time.1 feedback)) =
      decodeObservationResultCode rate i activation
        (assembleObservationInput carry row time feedback arm) code := by
  have hbuffer :
      FollowerDownMeasurability.replaceBufferScalars
        (FollowerObservationStageMeasurabilityRepair.representativeState rate
          (assembleObservationInput carry row time feedback arm).1).buffer
        (FollowerLoggingDownMeasurability.inputSavedScalars
          (FollowerObservationStageMeasurabilityRepair.loggingInputOfFiber
            (assembleObservationInput carry row time feedback arm).2)) =
        FollowerObservationStageMeasurabilityRepair.carriedStateBuffer carry := by
    change FollowerDownMeasurability.replaceBufferScalars
        (FollowerObservationStageMeasurabilityRepair.sparseSkeletonBuffer carry.1.2.2)
        (FollowerObservationStageMeasurabilityRepair.representativeValues carry.1 carry.2) =
      FollowerDownJointMeasurability.bufferFromSkeletonAndScalars carry.1.2.2 carry.2
    exact FollowerObservationStageMeasurabilityRepair.replaceRepresentativeBuffer carry.1 carry.2
  have hcarryBuffer :
      FollowerDownJointMeasurability.bufferFromSkeletonAndScalars
          (assembleObservationInput carry row time feedback arm).1.2.2
          (FollowerObservationStageMeasurabilityRepair.fiberValues
            (assembleObservationInput carry row time feedback arm).2) =
        FollowerObservationStageMeasurabilityRepair.carriedStateBuffer carry := by
    rfl
  have hrecord :
      FollowerLoggingDownMeasurability.currentLoggingRecord i activation
          (FollowerObservationStageMeasurabilityRepair.loggingInputOfFiber
            (assembleObservationInput carry row time feedback arm).2) =
        ⟨time.1.val + 1, arm,
          (currentSavedScalar row time.1 feedback).1,
          (currentSavedScalar row time.1 feedback).2⟩ := by
    rfl
  cases code with
  | unoccupied loggingCode =>
    cases loggingCode with
    | loggingFailure reason => rfl
    | down downCode =>
      cases downCode with
      | skipped before reason =>
        simp [firstStageCarriedResult, reconstructFirstStageCarriedResult,
          decodeObservationResultCode, reconstructLoggingDownResult,
          reconstructLocalDownResult, DeclaredFollowerLocalRound.consumeDownResult,
          reconstruct_carriedStateWithStateCode, hbuffer]
      | inputFailure before reason =>
        simp [firstStageCarriedResult, reconstructFirstStageCarriedResult,
          decodeObservationResultCode, reconstructLoggingDownResult,
          reconstructLocalDownResult, DeclaredFollowerLocalRound.consumeDownResult]
      | decodeOrParseRejected before after raw =>
        simp [firstStageCarriedResult, reconstructFirstStageCarriedResult,
          decodeObservationResultCode, reconstructLoggingDownResult,
          reconstructLocalDownResult, DeclaredFollowerLocalRound.consumeDownResult,
          reconstruct_carriedStateWithStateCode, hbuffer]
      | parsedButUnaccepted before after raw reply =>
        simp [firstStageCarriedResult, reconstructFirstStageCarriedResult,
          decodeObservationResultCode, reconstructLoggingDownResult,
          reconstructLocalDownResult, DeclaredFollowerLocalRound.consumeDownResult,
          reconstruct_carriedStateWithStateCode, hbuffer]
      | outputFailure before reason =>
        simp [firstStageCarriedResult, reconstructFirstStageCarriedResult,
          decodeObservationResultCode, reconstructLoggingDownResult,
          reconstructLocalDownResult, DeclaredFollowerLocalRound.consumeDownResult]
      | accepted before after raw reply scan registers service =>
        simp [firstStageCarriedResult, reconstructFirstStageCarriedResult,
          decodeObservationResultCode, reconstructLoggingDownResult,
          reconstructLocalDownResult, DeclaredFollowerLocalRound.consumeDownResult,
          reconstruct_emptyCarriedState]
    | logged state recipe =>
      cases recipe with
      | retained =>
        simp [firstStageCarriedResult, reconstructFirstStageCarriedResult,
          decodeObservationResultCode, reconstructLoggingDownResult,
          reconstructedBuffer, reconstruct_carriedStateWithStateCode,
          hbuffer]
      | appendedCurrent =>
        simp [firstStageCarriedResult, reconstructFirstStageCarriedResult,
          decodeObservationResultCode, reconstructLoggingDownResult,
          reconstructedBuffer, reconstruct_appendCarriedState]
        rw [← hbuffer]
        rw [hrecord]
      | cleared =>
        simp [firstStageCarriedResult, reconstructFirstStageCarriedResult,
          decodeObservationResultCode, reconstructLoggingDownResult,
          reconstructedBuffer, reconstruct_emptyCarriedState]
  | occupied serviceCode =>
    cases serviceCode with
    | serviceFailure => rfl
    | success arrival service stateCode =>
      simp [firstStageCarriedResult, reconstructFirstStageCarriedResult,
        decodeObservationResultCode, reconstructOccupiedRoundCode,
        reconstruct_carriedStateWithStateCode, hcarryBuffer]

abbrev ObserveOrdinaryRest (p : Parameters) (rate : RateInput p) :=
  CarriedState p rate ×
    (LocalMemoryCode p ×
      (CompleteRow p × (Fin p.T × Fin (D p + 1))))

def releaseAfterFirstStage {p : Parameters} (rate : RateInput p)
    (i : Fin (p.m - 1)) (stage : RoundFailure ⊕ CarriedState p rate)
    (rest : ObserveOrdinaryRest p rate) : ObserveOrdinaryCarriedOutput p rate :=
  Sum.elim (fun reason => Sum.inl reason)
    (fun postService =>
      FollowerReleaseFinishJointMeasurability.releaseAndFinishCarriedOutput postService
        (FollowerReleaseFinishJointMeasurability.releaseAndFinishResultCodeAtComponents
          rate i rest.1 postService rest.2.1 rest.2.2.1 rest.2.2.2.1
            rest.2.2.2.2)) stage

private theorem measurable_releaseAfterFirstStage {p : Parameters}
    (rate : RateInput p) (i : Fin (p.m - 1)) :
    Measurable (fun z : (RoundFailure ⊕ CarriedState p rate) ×
        ObserveOrdinaryRest p rate => releaseAfterFirstStage rate i z.1 z.2) := by
  let distribute := MeasurableEquiv.sumProdDistrib RoundFailure
    (CarriedState p rate) (ObserveOrdinaryRest p rate)
  have hleft : Measurable (fun x : RoundFailure × ObserveOrdinaryRest p rate =>
      (Sum.inl x.1 : ObserveOrdinaryCarriedOutput p rate)) :=
    measurable_inl.comp measurable_fst
  let preChoice : (CarriedState p rate × ObserveOrdinaryRest p rate) → CarriedState p rate :=
    fun x => x.2.1
  let postService : (CarriedState p rate × ObserveOrdinaryRest p rate) → CarriedState p rate :=
    fun x => x.1
  let memory : (CarriedState p rate × ObserveOrdinaryRest p rate) → LocalMemoryCode p :=
    fun x => x.2.2.1
  let row : (CarriedState p rate × ObserveOrdinaryRest p rate) → CompleteRow p :=
    fun x => x.2.2.2.1
  let time : (CarriedState p rate × ObserveOrdinaryRest p rate) → Fin p.T :=
    fun x => x.2.2.2.2.1
  let feedback : (CarriedState p rate × ObserveOrdinaryRest p rate) → Fin (D p + 1) :=
    fun x => x.2.2.2.2.2
  have hpreChoice : Measurable preChoice := measurable_fst.comp measurable_snd
  have hpostService : Measurable postService := measurable_fst
  have hmemory : Measurable memory :=
    measurable_fst.comp (measurable_snd.comp measurable_snd)
  have hrow : Measurable row :=
    measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))
  have htime : Measurable time := measurable_fst.comp (measurable_snd.comp
    (measurable_snd.comp (measurable_snd.comp measurable_snd)))
  have hfeedback : Measurable feedback := measurable_snd.comp (measurable_snd.comp
    (measurable_snd.comp (measurable_snd.comp measurable_snd)))
  have hright : Measurable (fun x : CarriedState p rate × ObserveOrdinaryRest p rate =>
      FollowerReleaseFinishJointMeasurability.releaseAndFinishCarriedOutput x.1
        (FollowerReleaseFinishJointMeasurability.releaseAndFinishResultCodeAtComponents
          rate i x.2.1 x.1 x.2.2.1 x.2.2.2.1
            x.2.2.2.2.1 x.2.2.2.2.2)) := by
    change Measurable (fun x =>
      FollowerReleaseFinishJointMeasurability.releaseAndFinishCarriedOutput (postService x)
        (FollowerReleaseFinishJointMeasurability.releaseAndFinishResultCodeAtComponents
          rate i (preChoice x) (postService x) (memory x) (row x) (time x) (feedback x)))
    exact FollowerReleaseFinishJointMeasurability.measurable_releaseAndFinishCarriedOutputAtComponents
      rate i preChoice postService memory row time feedback hpreChoice hpostService
      hmemory hrow htime hfeedback
  have hsum := Measurable.sumElim hleft hright
  let combined :
      (RoundFailure × ObserveOrdinaryRest p rate ⊕
        CarriedState p rate × ObserveOrdinaryRest p rate) →
          ObserveOrdinaryCarriedOutput p rate :=
    Sum.elim (fun x => (Sum.inl x.1 : ObserveOrdinaryCarriedOutput p rate))
      (fun x => FollowerReleaseFinishJointMeasurability.releaseAndFinishCarriedOutput
        x.1 (FollowerReleaseFinishJointMeasurability.releaseAndFinishResultCodeAtComponents
          rate i x.2.1 x.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2))
  have hcombined : Measurable combined := hsum
  have hfactor :
      (fun z : (RoundFailure ⊕ CarriedState p rate) × ObserveOrdinaryRest p rate =>
        releaseAfterFirstStage rate i z.1 z.2) = combined ∘ distribute := by
    funext z
    rcases z with ⟨stage, rest⟩
    cases stage <;> rfl
  rw [hfactor]
  exact hcombined.comp distribute.measurable_toFun

/-- Complete ordinary observation on independently supplied local inputs.
The `carry` is the original choice snapshot; the first-stage decoder supplies
the actual post-service/DOWN carry used by release and finish. -/
def observeOrdinaryCarriedOutputAtComponents {p : Parameters}
    (rate : RateInput p) (i : Fin (p.m - 1)) (activation : Activation p)
    {Ω : Type*} [MeasurableSpace Ω]
    (carry : Ω → CarriedState p rate) (memory : Ω → LocalMemoryCode p)
    (row : Ω → CompleteRow p) (time : Ω → FollowerActiveCalendarTime p activation)
    (feedback : Ω → Fin (D p + 1)) (arm : Ω → Fin p.K) :
    Ω → ObserveOrdinaryCarriedOutput p rate :=
  fun ω =>
    let code := observationResultCode rate i activation
      (assembleObservationInput (carry ω) (row ω) (time ω) (feedback ω) (arm ω))
    let stage := firstStageCarriedResult code (carry ω)
      ((time ω).1.val + 1, arm ω)
      (currentSavedScalar (row ω) (time ω).1 (feedback ω))
    releaseAfterFirstStage rate i stage
      (carry ω, (memory ω, (row ω, ((time ω).1, feedback ω))))

/-- The ordinary composition is measurable from separate original choice
carry, memory, full row, genuine active time, grid feedback index, and arm. -/
theorem measurable_observeOrdinaryCarriedOutputAtComponents {p : Parameters}
    (rate : RateInput p) (i : Fin (p.m - 1)) (activation : Activation p)
    {Ω : Type*} [MeasurableSpace Ω]
    (carry : Ω → CarriedState p rate) (memory : Ω → LocalMemoryCode p)
    (row : Ω → CompleteRow p) (time : Ω → FollowerActiveCalendarTime p activation)
    (feedback : Ω → Fin (D p + 1)) (arm : Ω → Fin p.K)
    (hcarry : Measurable carry) (hmemory : Measurable memory)
    (hrow : Measurable row) (htime : Measurable time)
    (hfeedback : Measurable feedback) (harm : Measurable arm) :
    Measurable (observeOrdinaryCarriedOutputAtComponents rate i activation
      carry memory row time feedback arm) := by
  have hcalendar : Measurable (fun ω => (time ω).1) :=
    measurable_subtype_coe.comp htime
  have hcode : Measurable (fun ω => observationResultCode rate i activation
      (assembleObservationInput (carry ω) (row ω) (time ω)
        (feedback ω) (arm ω))) :=
    measurable_observationResultCode_atComponents rate i activation carry row time
      feedback arm hcarry hrow htime hfeedback harm
  have hkey := measurable_currentObservationKey (fun ω => (time ω).1) arm hcalendar harm
  have hsaved := measurable_currentSavedScalar row
    (fun ω => (time ω).1) feedback hrow hcalendar hfeedback
  have hstage : Measurable (fun ω => firstStageCarriedResult
      (observationResultCode rate i activation
        (assembleObservationInput (carry ω) (row ω) (time ω)
          (feedback ω) (arm ω))) (carry ω)
      ((time ω).1.val + 1, arm ω)
      (currentSavedScalar (row ω) (time ω).1 (feedback ω))) := by
    exact measurable_firstStageCarriedResult
      (fun ω => observationResultCode rate i activation
        (assembleObservationInput (carry ω) (row ω) (time ω)
          (feedback ω) (arm ω))) carry
      (fun ω => ((time ω).1.val + 1, arm ω))
      (fun ω => currentSavedScalar (row ω) (time ω).1 (feedback ω))
      hcode hcarry hkey hsaved
  have hrest : Measurable (fun ω : Ω =>
      (carry ω, (memory ω, (row ω, ((time ω).1, feedback ω)))) :
      Ω → ObserveOrdinaryRest p rate) :=
    hcarry.prodMk (hmemory.prodMk (hrow.prodMk (hcalendar.prodMk hfeedback)))
  have hpair := hstage.prodMk hrest
  have hcomp := (measurable_releaseAfterFirstStage rate i).comp hpair
  change Measurable (observeOrdinaryCarriedOutputAtComponents rate i activation
    carry memory row time feedback arm)
  exact hcomp

/-- Reconstructing the complete carried output gives the exact existing
ordinary observation operation, with the original choice snapshot supplied
to release while its actual first-stage output supplies the post-service
snapshot. -/
theorem observeOrdinaryCarriedOutputAtComponents_reconstructs
    {p : Parameters} (rate : RateInput p) (i : Fin (p.m - 1))
    (activation : Activation p) (carry : CarriedState p rate)
    (memory : LocalMemoryCode p) (row : CompleteRow p)
    (time : FollowerActiveCalendarTime p activation) (feedback : Fin (D p + 1))
    (arm : Fin p.K) :
    FollowerReleaseFinishJointMeasurability.reconstructReleaseAndFinishCarriedOutput
        (observeOrdinaryCarriedOutputAtComponents rate i activation
          (fun _ => carry) (fun _ => memory) (fun _ => row)
          (fun _ => time) (fun _ => feedback) (fun _ => arm) ()) =
      DeclaredFollowerLocalRound.observeOrdinary rate i row activation time.1 time.2
        arm (FollowerDownMeasurability.feedbackAtGrid p feedback)
        (FollowerObservationStageMeasurabilityRepair.reconstructCarriedState
          carry.1 carry.2)
        (FollowerLifecycleMeasurability.localMemoryOfCode memory) := by
  classical
  let code := observationResultCode rate i activation
    (assembleObservationInput carry row time feedback arm)
  let stage := firstStageCarriedResult code carry
    (time.1.val + 1, arm) (currentSavedScalar row time.1 feedback)
  have hstage := firstStageCarriedResult_reconstructs rate i activation carry row
    time feedback arm code
  have hdecode : decodeObservationResultCode rate i activation
      (assembleObservationInput carry row time feedback arm) code =
      DeclaredFollowerLocalRound.recordOrServiceThenDown rate i row activation
        time.1 time.2 arm (FollowerDownMeasurability.feedbackAtGrid p feedback)
        (FollowerObservationStageMeasurabilityRepair.reconstructCarriedState
          carry.1 carry.2) := by
    simpa [code, FollowerObservationStageMeasurabilityRepair.assembleObservationInput,
      FollowerObservationStageMeasurabilityRepair.fiberRow,
      FollowerObservationStageMeasurabilityRepair.fiberTime,
      FollowerObservationStageMeasurabilityRepair.fiberFeedbackIndex,
      FollowerObservationStageMeasurabilityRepair.fiberPlayedArm,
      FollowerObservationStageMeasurabilityRepair.fiberValues] using
      FollowerObservationStageMeasurabilityRepair.decode_observationResultCode_eq_actual
        rate i activation (assembleObservationInput carry row time feedback arm)
  have hstage' : reconstructFirstStageCarriedResult stage =
      decodeObservationResultCode rate i activation
        (assembleObservationInput carry row time feedback arm) code := by
    simpa [stage] using hstage
  unfold observeOrdinaryCarriedOutputAtComponents
  dsimp only
  rw [show (firstStageCarriedResult code carry (time.1.val + 1, arm)
      (currentSavedScalar row time.1 feedback)) = stage by rfl]
  cases hfirst : stage with
  | inl reason =>
      have hactual : DeclaredFollowerLocalRound.recordOrServiceThenDown rate i row
          activation time.1 time.2 arm
          (FollowerDownMeasurability.feedbackAtGrid p feedback)
          (FollowerObservationStageMeasurabilityRepair.reconstructCarriedState
            carry.1 carry.2) = .error reason := by
        have hdecoded := hstage'
        simp [hfirst, reconstructFirstStageCarriedResult] at hdecoded
        exact (hdecoded.trans hdecode).symm
      simp [releaseAfterFirstStage, hactual,
        DeclaredFollowerLocalRound.observeOrdinary,
        FollowerReleaseFinishJointMeasurability.reconstructReleaseAndFinishCarriedOutput]
  | inr postService =>
      have hactual : DeclaredFollowerLocalRound.recordOrServiceThenDown rate i row
          activation time.1 time.2 arm
          (FollowerDownMeasurability.feedbackAtGrid p feedback)
          (FollowerObservationStageMeasurabilityRepair.reconstructCarriedState
            carry.1 carry.2) = .ok
            (FollowerObservationStageMeasurabilityRepair.reconstructCarriedState
              postService.1 postService.2) := by
        have hdecoded := hstage'
        simp [hfirst, reconstructFirstStageCarriedResult] at hdecoded
        exact (hdecoded.trans hdecode).symm
      rw [DeclaredFollowerLocalRound.observeOrdinary, hactual]
      simp only [releaseAfterFirstStage]
      exact FollowerReleaseFinishJointMeasurability.releaseAndFinishCarriedOutputAtComponents_reconstruct
        rate i carry postService memory row time.1 feedback

/-! ## Activation-retaining ordinary observation -/

abbrev VaryingOrdinaryObservationInput (p : Parameters) (rate : RateInput p) :=
  Sigma fun activation : Activation p =>
    FollowerObservationStageMeasurabilityRepair.ObservationInput p rate activation ×
      LocalMemoryCode p

abbrev VaryingOrdinaryObservationOutput (p : Parameters) (rate : RateInput p) :=
  Sigma fun _activation : Activation p => ObserveOrdinaryCarriedOutput p rate

/-- Assemble the existing varying observation input together with this
follower's independently supplied local proposal memory. -/
def assembleVaryingOrdinaryObservationInput {p : Parameters}
    {rate : RateInput p} (activation : Activation p)
    (carry : CarriedState p rate) (memory : LocalMemoryCode p)
    (row : CompleteRow p) (calendarIndex : Fin p.T)
    (hvalid : activation.val ≤ calendarIndex.val + 1)
    (feedback : Fin (D p + 1)) (arm : Fin p.K) :
    VaryingOrdinaryObservationInput p rate :=
  ⟨activation,
    (assembleObservationInput carry row ⟨calendarIndex, hvalid⟩ feedback arm,
      memory)⟩

theorem measurable_assembleVaryingOrdinaryObservationInput {p : Parameters}
    (rate : RateInput p) {Ω : Type*} [MeasurableSpace Ω]
    (activation : Ω → Activation p) (carry : Ω → CarriedState p rate)
    (memory : Ω → LocalMemoryCode p) (row : Ω → CompleteRow p)
    (calendarIndex : Ω → Fin p.T) (feedback : Ω → Fin (D p + 1))
    (arm : Ω → Fin p.K) (hactivation : Measurable activation)
    (hcarry : Measurable carry) (hmemory : Measurable memory)
    (hrow : Measurable row) (hcalendar : Measurable calendarIndex)
    (hfeedback : Measurable feedback) (harm : Measurable arm)
    (hvalid : ∀ ω, (activation ω).val ≤ (calendarIndex ω).val + 1) :
    Measurable (fun ω => assembleVaryingOrdinaryObservationInput
      (activation ω) (carry ω) (memory ω) (row ω) (calendarIndex ω)
      (hvalid ω) (feedback ω) (arm ω)) := by
  have hobs := measurable_assembleVaryingObservationInput rate activation carry row
    calendarIndex feedback arm hactivation hcarry hrow hcalendar hfeedback harm hvalid
  have hpaired := hobs.prodMk hmemory
  exact measurable_assembleSigmaProduct.comp hpaired

/-- Run the already assembled activation-dependent ordinary observation and
retain the same activation in its output. -/
def varyingObserveOrdinaryCarriedOutput {p : Parameters} (rate : RateInput p)
    (i : Fin (p.m - 1)) (x : VaryingOrdinaryObservationInput p rate) :
    VaryingOrdinaryObservationOutput p rate := by
  let observation := x.2.1
  exact ⟨x.1,
    observeOrdinaryCarriedOutputAtComponents rate i x.1
      (fun _ => observationInputCarriedState observation)
      (fun _ => x.2.2)
      (fun _ => observationInputRow observation)
      (fun _ => observationInputTime observation)
      (fun _ => observationInputFeedbackIndex observation)
      (fun _ => observationInputPlayedArm observation) ()⟩

/-- The activation-dependent ordinary output decodes to the exact source
`observeOrdinary` call on its supplied carried state, row, valid time,
feedback-grid point, arm, and memory. -/
theorem varyingObserveOrdinaryCarriedOutput_reconstructs {p : Parameters}
    (rate : RateInput p) (i : Fin (p.m - 1))
    (x : VaryingOrdinaryObservationInput p rate) :
    FollowerReleaseFinishJointMeasurability.reconstructReleaseAndFinishCarriedOutput
      (varyingObserveOrdinaryCarriedOutput rate i x).2 =
      DeclaredFollowerLocalRound.observeOrdinary rate i
        (observationInputRow x.2.1) x.1
        (observationInputTime x.2.1).1 (observationInputTime x.2.1).2
        (observationInputPlayedArm x.2.1)
        (FollowerDownMeasurability.feedbackAtGrid p
          (observationInputFeedbackIndex x.2.1))
        (FollowerObservationStageMeasurabilityRepair.reconstructCarriedState
          (observationInputCarriedState x.2.1).1
          (observationInputCarriedState x.2.1).2)
        (FollowerLifecycleMeasurability.localMemoryOfCode x.2.2) := by
  cases x with
  | mk activation data =>
      rcases data with ⟨observation, memory⟩
      exact observeOrdinaryCarriedOutputAtComponents_reconstructs rate i activation
        (observationInputCarriedState observation) memory
        (observationInputRow observation) (observationInputTime observation)
        (observationInputFeedbackIndex observation) (observationInputPlayedArm observation)

/-- Arbitrary-base varying-activation ordinary composition. Its only domain
condition is the genuine source validity `activation ≤ calendarIndex + 1`;
the returned dependent-union label is the same supplied activation. -/
def varyingObserveOrdinaryCarriedOutputAtComponents {p : Parameters}
    (rate : RateInput p) (i : Fin (p.m - 1))
    {Ω : Type*} (activation : Ω → Activation p)
    (carry : Ω → CarriedState p rate) (memory : Ω → LocalMemoryCode p)
    (row : Ω → CompleteRow p) (calendarIndex : Ω → Fin p.T)
    (feedback : Ω → Fin (D p + 1)) (arm : Ω → Fin p.K)
    (hvalid : ∀ ω, (activation ω).val ≤ (calendarIndex ω).val + 1) :
    Ω → VaryingOrdinaryObservationOutput p rate :=
  fun ω => by
    let label := activation ω
    let x : {x : Ω // activation x = label} := ⟨ω, rfl⟩
    letI : MeasurableSpace {x : Ω // activation x = label} := ⊤
    exact ⟨label,
      observeOrdinaryCarriedOutputAtComponents rate i label
        (fun y => carry y.1) (fun y => memory y.1) (fun y => row y.1)
        (activeCalendarTimeOnFiberLocal activation calendarIndex hvalid label)
        (fun y => feedback y.1) (fun y => arm y.1) x⟩

theorem measurable_varyingObserveOrdinaryCarriedOutputAtComponents
    {p : Parameters} (rate : RateInput p) (i : Fin (p.m - 1))
    {Ω : Type*} [MeasurableSpace Ω]
    (activation : Ω → Activation p) (carry : Ω → CarriedState p rate)
    (memory : Ω → LocalMemoryCode p) (row : Ω → CompleteRow p)
    (calendarIndex : Ω → Fin p.T) (feedback : Ω → Fin (D p + 1))
    (arm : Ω → Fin p.K)
    (hactivation : Measurable activation) (hcarry : Measurable carry)
    (hmemory : Measurable memory) (hrow : Measurable row)
    (hcalendar : Measurable calendarIndex) (hfeedback : Measurable feedback)
    (harm : Measurable arm)
    (hvalid : ∀ ω, (activation ω).val ≤ (calendarIndex ω).val + 1) :
    Measurable (varyingObserveOrdinaryCarriedOutputAtComponents rate i
      activation carry memory row calendarIndex feedback arm hvalid) := by
  let base (a : Activation p) : {ω : Ω // activation ω = a} → Ω := fun x => x.1
  let timeOnFiber (a : Activation p) (x : {ω : Ω // activation ω = a}) :
      FollowerActiveCalendarTime p a :=
    ⟨calendarIndex (base a x), by simpa [base, x.2] using hvalid (base a x)⟩
  let fiber (a : Activation p) (x : {ω : Ω // activation ω = a}) :
      ObserveOrdinaryCarriedOutput p rate :=
    observeOrdinaryCarriedOutputAtComponents rate i a
      (carry ∘ base a) (memory ∘ base a) (row ∘ base a)
      (timeOnFiber a) (feedback ∘ base a) (arm ∘ base a) x
  have hfiber (a : Activation p) : Measurable (fiber a) := by
    have hbase : Measurable (base a) :=
      measurable_subtype_coe
    exact measurable_observeOrdinaryCarriedOutputAtComponents rate i a
      (carry ∘ base a) (memory ∘ base a) (row ∘ base a)
      (timeOnFiber a) (feedback ∘ base a) (arm ∘ base a)
      (hcarry.comp hbase) (hmemory.comp hbase) (hrow.comp hbase)
      ((hcalendar.comp hbase).subtype_mk)
      (hfeedback.comp hbase) (harm.comp hbase)
  have hassembled := measurable_activationDependentAssembly activation hactivation
    fiber hfiber
  change Measurable (fun ω =>
    (⟨activation ω, fiber (activation ω) ⟨ω, rfl⟩⟩ :
      VaryingOrdinaryObservationOutput p rate))
  exact hassembled

/-- Pointwise exact decoder for the arbitrary-base varying ordinary
composition. The sole side condition is valid activation time. -/
theorem varyingObserveOrdinaryCarriedOutputAtComponents_reconstructs
    {p : Parameters} (rate : RateInput p) (i : Fin (p.m - 1))
    {Ω : Type*} (activation : Ω → Activation p)
    (carry : Ω → CarriedState p rate) (memory : Ω → LocalMemoryCode p)
    (row : Ω → CompleteRow p) (calendarIndex : Ω → Fin p.T)
    (feedback : Ω → Fin (D p + 1)) (arm : Ω → Fin p.K)
    (hvalid : ∀ ω, (activation ω).val ≤ (calendarIndex ω).val + 1)
    (ω : Ω) :
    FollowerReleaseFinishJointMeasurability.reconstructReleaseAndFinishCarriedOutput
        (varyingObserveOrdinaryCarriedOutputAtComponents rate i activation carry memory
          row calendarIndex feedback arm hvalid ω).2 =
      DeclaredFollowerLocalRound.observeOrdinary rate i (row ω) (activation ω)
        (calendarIndex ω) (hvalid ω) (arm ω)
        (FollowerDownMeasurability.feedbackAtGrid p (feedback ω))
        (FollowerObservationStageMeasurabilityRepair.reconstructCarriedState
          (carry ω).1 (carry ω).2)
        (FollowerLifecycleMeasurability.localMemoryOfCode (memory ω)) := by
  have hcomponent :
      (varyingObserveOrdinaryCarriedOutputAtComponents rate i activation carry memory
        row calendarIndex feedback arm hvalid ω).2 =
        observeOrdinaryCarriedOutputAtComponents rate i (activation ω)
          (fun _ => carry ω) (fun _ => memory ω) (fun _ => row ω)
          (fun _ => (⟨calendarIndex ω, hvalid ω⟩ : FollowerActiveCalendarTime p (activation ω)))
          (fun _ => feedback ω) (fun _ => arm ω) () := by
    rfl
  rw [hcomponent]
  exact observeOrdinaryCarriedOutputAtComponents_reconstructs rate i (activation ω)
    (carry ω) (memory ω) (row ω) ⟨calendarIndex ω, hvalid ω⟩
    (feedback ω) (arm ω)

/-! ## Whole ordinary/dagger observation and the exact local encoding -/

abbrev ObserveRest (p : Parameters) (activation : Activation p) :=
  CompleteRow p ×
    (FollowerActiveCalendarTime p activation × (Fin p.K × Fin (D p + 1)))

abbrev VaryingObserveInput (p : Parameters) (rate : RateInput p) :=
  Sigma fun activation : Activation p =>
    IncomingConfiguration p rate × ObserveRest p activation

abbrev VaryingObserveCarriedOutput (p : Parameters) (rate : RateInput p) :=
  Sigma fun _activation : Activation p => Fin p.K × IncomingConfiguration p rate

instance varyingObserveInputMeasurableSpace (p : Parameters) (rate : RateInput p) :
    MeasurableSpace (VaryingObserveInput p rate) := by
  letI : ∀ activation : Activation p,
      MeasurableSpace (IncomingConfiguration p rate × ObserveRest p activation) :=
    fun _ => inferInstance
  exact Sigma.instMeasurableSpace

instance varyingObserveOutputMeasurableSpace (p : Parameters) (rate : RateInput p) :
    MeasurableSpace (VaryingObserveCarriedOutput p rate) := by
  letI : ∀ _activation : Activation p,
      MeasurableSpace (Fin p.K × IncomingConfiguration p rate) :=
    fun _ => inferInstance
  exact Sigma.instMeasurableSpace

/-- Separate-input dependent-union carrier for the exact observable portion
of an already prepared follower round. -/
def assembleVaryingObserveInput {p : Parameters} {rate : RateInput p}
    (activation : Activation p) (incoming : IncomingConfiguration p rate)
    (row : CompleteRow p) (calendarIndex : Fin p.T)
    (hvalid : activation.val ≤ calendarIndex.val + 1)
    (arm : Fin p.K) (feedback : Fin (D p + 1)) : VaryingObserveInput p rate :=
  ⟨activation,
    (incoming, (row, (⟨calendarIndex, hvalid⟩, (arm, feedback))))⟩

/-- Measurable assembly of the actual incoming ordinary/dagger carrier, row,
valid time, prepared arm, and bounded-grid feedback while retaining activation. -/
theorem measurable_assembleVaryingObserveInput {p : Parameters}
    (rate : RateInput p) {Ω : Type*} [MeasurableSpace Ω]
    (activation : Ω → Activation p) (incoming : Ω → IncomingConfiguration p rate)
    (row : Ω → CompleteRow p) (calendarIndex : Ω → Fin p.T)
    (arm : Ω → Fin p.K) (feedback : Ω → Fin (D p + 1))
    (hactivation : Measurable activation) (hincoming : Measurable incoming)
    (hrow : Measurable row) (hcalendar : Measurable calendarIndex)
    (harm : Measurable arm) (hfeedback : Measurable feedback)
    (hvalid : ∀ ω, (activation ω).val ≤ (calendarIndex ω).val + 1) :
    Measurable (fun ω => assembleVaryingObserveInput (activation ω)
      (incoming ω) (row ω) (calendarIndex ω) (hvalid ω) (arm ω) (feedback ω)) := by
  let ActivationFiber (a : Activation p) := {ω : Ω // activation ω = a}
  let : ∀ a : Activation p, MeasurableSpace (ActivationFiber a) := fun a => by
    change MeasurableSpace {ω : Ω // activation ω = a}
    infer_instance
  let fiber (a : Activation p) (x : ActivationFiber a) :
      IncomingConfiguration p rate × ObserveRest p a :=
    (incoming x.1, (row x.1,
      (activeCalendarTimeOnFiberLocal activation calendarIndex hvalid a x,
        (arm x.1, feedback x.1))))
  have hfiber (a : Activation p) : Measurable (fiber a) := by
    have hcoe : Measurable (fun x : ActivationFiber a => (x.1 : Ω)) :=
      measurable_subtype_coe
    exact (hincoming.comp hcoe).prodMk ((hrow.comp hcoe).prodMk
      (((hcalendar.comp hcoe).subtype_mk).prodMk
        ((harm.comp hcoe).prodMk (hfeedback.comp hcoe))))
  simpa [assembleVaryingObserveInput, fiber, ActivationFiber,
    activeCalendarTimeOnFiberLocal] using
      measurable_activationDependentAssembly activation hactivation fiber hfiber

def ordinaryOutputToIncoming {p : Parameters} {rate : RateInput p}
    (output : ObserveOrdinaryCarriedOutput p rate) : IncomingConfiguration p rate :=
  Sum.elim (fun _ => none) (fun result => some result) output

private theorem measurable_ordinaryOutputToIncoming {p : Parameters}
    (rate : RateInput p) :
    Measurable (ordinaryOutputToIncoming (p := p) (rate := rate)) := by
  apply (measurable_comap_iff).2
  change Measurable (Sum.elim (fun _ : RoundFailure =>
    (Sum.inl () : Unit ⊕ (CarriedState p rate × LocalMemoryCode p)))
    (fun result : CarriedState p rate × LocalMemoryCode p => Sum.inr result))
  exact Measurable.sumElim measurable_const measurable_inr

/-- Whole local observe after carrying the already prepared state. An ordinary
failure becomes dagger, while the prepared arm is copied unchanged. -/
def observeCarriedOutputAtComponents {p : Parameters}
    (rate : RateInput p) (i : Fin (p.m - 1)) (activation : Activation p)
    {Ω : Type*} [MeasurableSpace Ω]
    (incoming : Ω → IncomingConfiguration p rate)
    (row : Ω → CompleteRow p) (time : Ω → FollowerActiveCalendarTime p activation)
    (arm : Ω → Fin p.K) (feedback : Ω → Fin (D p + 1)) :
    Ω → Fin p.K × IncomingConfiguration p rate := by
  let rest := fun ω : Ω => (row ω, (time ω, (arm ω, feedback ω)))
  let coded := fun ω : Ω =>
    FollowerPrepareJointMeasurability.incomingConfigurationToSum (incoming ω)
  let distribute := MeasurableEquiv.sumProdDistrib Unit
    (CarriedState p rate × LocalMemoryCode p) (ObserveRest p activation)
  exact fun ω => Sum.elim
    (fun x : Unit × ObserveRest p activation => (x.2.2.2.1, none))
    (fun x : (CarriedState p rate × LocalMemoryCode p) × ObserveRest p activation =>
      (x.2.2.2.1, ordinaryOutputToIncoming
        (observeOrdinaryCarriedOutputAtComponents rate i activation
          (fun _ => x.1.1) (fun _ => x.1.2)
          (fun _ => x.2.1) (fun _ => x.2.2.1)
          (fun _ => x.2.2.2.2) (fun _ => x.2.2.2.1) ())))
      (distribute (coded ω, rest ω))

/-- The observation-level adapter is measurable from the lossless incoming
ordinary/dagger carrier and separate row, valid time, arm, and grid feedback. -/
theorem measurable_observeCarriedOutputAtComponents {p : Parameters}
    (rate : RateInput p) (i : Fin (p.m - 1)) (activation : Activation p)
    {Ω : Type*} [MeasurableSpace Ω]
    (incoming : Ω → IncomingConfiguration p rate)
    (row : Ω → CompleteRow p) (time : Ω → FollowerActiveCalendarTime p activation)
    (arm : Ω → Fin p.K) (feedback : Ω → Fin (D p + 1))
    (hincoming : Measurable incoming) (hrow : Measurable row)
    (htime : Measurable time) (harm : Measurable arm)
    (hfeedback : Measurable feedback) :
    Measurable (observeCarriedOutputAtComponents rate i activation
      incoming row time arm feedback) := by
  let rest := fun ω : Ω => (row ω, (time ω, (arm ω, feedback ω)))
  let coded := fun ω : Ω =>
    FollowerPrepareJointMeasurability.incomingConfigurationToSum (incoming ω)
  let distribute := MeasurableEquiv.sumProdDistrib Unit
    (CarriedState p rate × LocalMemoryCode p) (ObserveRest p activation)
  have hbase : Measurable (fun ω => (coded ω, rest ω)) :=
    ((FollowerPrepareJointMeasurability.measurable_incomingConfigurationToSum rate).comp
      hincoming).prodMk
      (hrow.prodMk (htime.prodMk (harm.prodMk hfeedback)))
  have hleft : Measurable (fun x : Unit × ObserveRest p activation =>
      (x.2.2.2.1, (none : IncomingConfiguration p rate))) :=
    (measurable_fst.comp (measurable_snd.comp
      (measurable_snd.comp (measurable_snd.comp measurable_id)))).prodMk measurable_const
  have hright : Measurable (fun x :
      (CarriedState p rate × LocalMemoryCode p) × ObserveRest p activation =>
      (x.2.2.2.1, ordinaryOutputToIncoming
        (observeOrdinaryCarriedOutputAtComponents rate i activation
          (fun _ => x.1.1) (fun _ => x.1.2)
          (fun _ => x.2.1) (fun _ => x.2.2.1)
          (fun _ => x.2.2.2.2) (fun _ => x.2.2.2.1) ()))) := by
    have hordinary : Measurable (observeOrdinaryCarriedOutputAtComponents rate i activation
        (fun x : (CarriedState p rate × LocalMemoryCode p) × ObserveRest p activation => x.1.1)
        (fun x : (CarriedState p rate × LocalMemoryCode p) × ObserveRest p activation => x.1.2)
        (fun x => x.2.1) (fun x => x.2.2.1)
        (fun x => x.2.2.2.2) (fun x => x.2.2.2.1)) := by
      apply measurable_observeOrdinaryCarriedOutputAtComponents
      exact measurable_fst.comp measurable_fst
      exact measurable_snd.comp measurable_fst
      exact measurable_fst.comp measurable_snd
      exact measurable_fst.comp (measurable_snd.comp measurable_snd)
      exact measurable_snd.comp (measurable_snd.comp
        (measurable_snd.comp measurable_snd))
      exact measurable_fst.comp (measurable_snd.comp
        (measurable_snd.comp measurable_snd))
    exact ((measurable_fst.comp (measurable_snd.comp
      (measurable_snd.comp (measurable_snd.comp measurable_id)))).prodMk
      ((measurable_ordinaryOutputToIncoming rate).comp hordinary))
  have hsum := Measurable.sumElim hleft hright
  change Measurable
    ((Sum.elim
      (fun x : Unit × ObserveRest p activation =>
        (x.2.2.2.1, (none : IncomingConfiguration p rate)))
      (fun x : (CarriedState p rate × LocalMemoryCode p) × ObserveRest p activation =>
        (x.2.2.2.1, ordinaryOutputToIncoming
          (observeOrdinaryCarriedOutputAtComponents rate i activation
            (fun _ => x.1.1) (fun _ => x.1.2)
            (fun _ => x.2.1) (fun _ => x.2.2.1)
            (fun _ => x.2.2.2.2) (fun _ => x.2.2.2.1) ()))) ∘ distribute) ∘
      (fun ω => (coded ω, rest ω)))
  exact hsum.comp (distribute.measurable_toFun.comp hbase)

/-- Decode a carried arm/configuration pair to the existing declared local
observed-round structure. -/
def observedRoundOfCarriedOutput {p : Parameters} {rate : RateInput p}
    (output : Fin p.K × IncomingConfiguration p rate) :
    DeclaredFollowerLocalRound.ObservedRound p rate :=
  ⟨output.1,
    FollowerPrepareJointMeasurability.localConfigurationOfIncoming rate output.2⟩

/-- The whole ordinary/dagger output decodes to the exact existing `observe`
operation. The incoming option retains arbitrary ordinary, pending, occupied,
released, and dagger states without any coordinator-state premise. -/
theorem observeCarriedOutputAtComponents_reconstructs {p : Parameters}
    (rate : RateInput p) (i : Fin (p.m - 1)) (activation : Activation p)
    (incoming : IncomingConfiguration p rate) (row : CompleteRow p)
    (time : FollowerActiveCalendarTime p activation) (arm : Fin p.K)
    (feedback : Fin (D p + 1)) :
    observedRoundOfCarriedOutput
        (observeCarriedOutputAtComponents rate i activation
          (fun _ => incoming) (fun _ => row) (fun _ => time)
          (fun _ => arm) (fun _ => feedback) ()) =
      DeclaredFollowerLocalRound.observe
        ⟨i, row, activation, time.1, time.2, arm,
          FollowerPrepareJointMeasurability.localConfigurationOfIncoming rate incoming⟩
        (FollowerDownMeasurability.feedbackAtGrid p feedback) := by
  cases incoming with
  | none => rfl
  | some data =>
      rcases data with ⟨carry, memory⟩
      let result := observeOrdinaryCarriedOutputAtComponents rate i activation
        (fun _ => carry) (fun _ => memory) (fun _ => row)
        (fun _ => time) (fun _ => feedback) (fun _ => arm) ()
      have hresult := observeOrdinaryCarriedOutputAtComponents_reconstructs rate i
        activation carry memory row time feedback arm
      have hconfiguration :
          FollowerPrepareJointMeasurability.localConfigurationOfIncoming rate
              (ordinaryOutputToIncoming result) =
            (match FollowerReleaseFinishJointMeasurability.reconstructReleaseAndFinishCarriedOutput
                result with
              | .error _ => LocalConfiguration.dagger
              | .ok output => LocalConfiguration.ordinary output.1 output.2) := by
        cases result <;> rfl
      change (⟨arm, FollowerPrepareJointMeasurability.localConfigurationOfIncoming
          rate (ordinaryOutputToIncoming result)⟩ : DeclaredFollowerLocalRound.ObservedRound p rate) =
        DeclaredFollowerLocalRound.observe
          ⟨i, row, activation, time.1, time.2, arm,
            LocalConfiguration.ordinary
              (FollowerObservationStageMeasurabilityRepair.reconstructCarriedState
                carry.1 carry.2)
              (FollowerLifecycleMeasurability.localMemoryOfCode memory)⟩
          (FollowerDownMeasurability.feedbackAtGrid p feedback)
      rw [hconfiguration, hresult]
      simp only [DeclaredFollowerLocalRound.observe]
      cases DeclaredFollowerLocalRound.observeOrdinary rate i row activation time.1
          time.2 arm (FollowerDownMeasurability.feedbackAtGrid p feedback)
          (FollowerObservationStageMeasurabilityRepair.reconstructCarriedState
            carry.1 carry.2)
          (FollowerLifecycleMeasurability.localMemoryOfCode memory) <;> rfl

/-- The varying whole-round input operation on its dependent-union carrier. -/
def varyingObserveCarriedOutput {p : Parameters} (rate : RateInput p)
    (i : Fin (p.m - 1)) (input : VaryingObserveInput p rate) :
    VaryingObserveCarriedOutput p rate := by
  let rest := input.2.2
  exact ⟨input.1,
    observeCarriedOutputAtComponents rate i input.1
      (fun _ => input.2.1) (fun _ => rest.1)
      (fun _ => rest.2.1) (fun _ => rest.2.2.1)
      (fun _ => rest.2.2.2) ()⟩

/-- The varying whole-round decoder is exactly the source `observe` operation
and retains its activation label. -/
theorem varyingObserveCarriedOutput_reconstructs {p : Parameters}
    (rate : RateInput p) (i : Fin (p.m - 1)) (input : VaryingObserveInput p rate) :
    observedRoundOfCarriedOutput (varyingObserveCarriedOutput rate i input).2 =
      DeclaredFollowerLocalRound.observe
        ⟨i, input.2.2.1, input.1, input.2.2.2.1.1,
          input.2.2.2.1.2, input.2.2.2.2.1,
          FollowerPrepareJointMeasurability.localConfigurationOfIncoming rate input.2.1⟩
        (FollowerDownMeasurability.feedbackAtGrid p input.2.2.2.2.2) := by
  rcases input with ⟨activation, ⟨incoming, ⟨row, ⟨time, ⟨arm, feedback⟩⟩⟩⟩⟩
  simpa [varyingObserveCarriedOutput] using
    observeCarriedOutputAtComponents_reconstructs rate i activation
      incoming row time arm feedback

/-- Arbitrary-base varying whole observation, with activation retained in the
dependent-union result and validity exposed only as `activation ≤ t + 1`. -/
def observeVaryingCarriedOutputAtComponents {p : Parameters}
    (rate : RateInput p) (i : Fin (p.m - 1))
    {Ω : Type*} [MeasurableSpace Ω]
    (activation : Ω → Activation p) (incoming : Ω → IncomingConfiguration p rate)
    (row : Ω → CompleteRow p) (calendarIndex : Ω → Fin p.T)
    (arm : Ω → Fin p.K) (feedback : Ω → Fin (D p + 1))
    (hvalid : ∀ ω, (activation ω).val ≤ (calendarIndex ω).val + 1) :
    Ω → VaryingObserveCarriedOutput p rate :=
  fun ω => by
    let label := activation ω
    let x : {x : Ω // activation x = label} := ⟨ω, rfl⟩
    letI : MeasurableSpace {x : Ω // activation x = label} := ⊤
    exact ⟨label,
      observeCarriedOutputAtComponents rate i label
        (fun y => incoming y.1) (fun y => row y.1)
        (activeCalendarTimeOnFiberLocal activation calendarIndex hvalid label)
        (fun y => arm y.1) (fun y => feedback y.1) x⟩

/-- Measurability of whole ordinary/dagger observation from its separate
activation, incoming configuration, complete row, calendar time, arm, and
bounded-grid feedback maps. -/
theorem measurable_observeVaryingCarriedOutputAtComponents {p : Parameters}
    (rate : RateInput p) (i : Fin (p.m - 1))
    {Ω : Type*} [MeasurableSpace Ω]
    (activation : Ω → Activation p) (incoming : Ω → IncomingConfiguration p rate)
    (row : Ω → CompleteRow p) (calendarIndex : Ω → Fin p.T)
    (arm : Ω → Fin p.K) (feedback : Ω → Fin (D p + 1))
    (hactivation : Measurable activation) (hincoming : Measurable incoming)
    (hrow : Measurable row) (hcalendar : Measurable calendarIndex)
    (harm : Measurable arm) (hfeedback : Measurable feedback)
    (hvalid : ∀ ω, (activation ω).val ≤ (calendarIndex ω).val + 1) :
    Measurable (observeVaryingCarriedOutputAtComponents rate i activation incoming
      row calendarIndex arm feedback hvalid) := by
  let base (a : Activation p) : {ω : Ω // activation ω = a} → Ω := fun x => x.1
  let timeOnFiber (a : Activation p) (x : {ω : Ω // activation ω = a}) :
      FollowerActiveCalendarTime p a :=
    ⟨calendarIndex (base a x), by simpa [base, x.2] using hvalid (base a x)⟩
  let fiber (a : Activation p) (x : {ω : Ω // activation ω = a}) :
      Fin p.K × IncomingConfiguration p rate :=
    observeCarriedOutputAtComponents rate i a (incoming ∘ base a)
      (row ∘ base a) (timeOnFiber a) (arm ∘ base a)
      (feedback ∘ base a) x
  have hfiber (a : Activation p) : Measurable (fiber a) := by
    have hbase : Measurable (base a) :=
      measurable_subtype_coe
    have htime : Measurable (timeOnFiber a) := (hcalendar.comp hbase).subtype_mk
    exact measurable_observeCarriedOutputAtComponents rate i a
      (incoming ∘ base a) (row ∘ base a) (timeOnFiber a)
      (arm ∘ base a) (feedback ∘ base a)
      (hincoming.comp hbase) (hrow.comp hbase) htime
      (harm.comp hbase) (hfeedback.comp hbase)
  have hassembled := measurable_activationDependentAssembly activation hactivation
    fiber hfiber
  change Measurable (fun ω =>
    (⟨activation ω, fiber (activation ω) ⟨ω, rfl⟩⟩ :
      VaryingObserveCarriedOutput p rate))
  exact hassembled

/-- On assembled separate maps, decoding the varying output recovers the
exact declared observe operation at every supplied activation. -/
theorem observeVaryingCarriedOutputAtComponents_reconstructs
    {p : Parameters} (rate : RateInput p) (i : Fin (p.m - 1))
    {Ω : Type*} [MeasurableSpace Ω] (activation : Ω → Activation p)
    (incoming : Ω → IncomingConfiguration p rate) (row : Ω → CompleteRow p)
    (calendarIndex : Ω → Fin p.T) (arm : Ω → Fin p.K)
    (feedback : Ω → Fin (D p + 1))
    (hvalid : ∀ ω, (activation ω).val ≤ (calendarIndex ω).val + 1)
    (ω : Ω) :
    observedRoundOfCarriedOutput
        (observeVaryingCarriedOutputAtComponents rate i activation incoming row
          calendarIndex arm feedback hvalid ω).2 =
      DeclaredFollowerLocalRound.observe
        ⟨i, row ω, activation ω, calendarIndex ω, hvalid ω, arm ω,
          FollowerPrepareJointMeasurability.localConfigurationOfIncoming rate
            (incoming ω)⟩
        (FollowerDownMeasurability.feedbackAtGrid p (feedback ω)) := by
  exact observeCarriedOutputAtComponents_reconstructs rate i (activation ω)
    (incoming ω) (row ω) ⟨calendarIndex ω, hvalid ω⟩ (arm ω) (feedback ω)

end Bandits.Support.DeclaredFollowerObservationMeasurability

end
