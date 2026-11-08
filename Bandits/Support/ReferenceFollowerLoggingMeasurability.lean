/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.FollowerPrepareJointMeasurability
public import Bandits.Support.FollowerReleaseFinishJointMeasurability

/-!
# Lossless measurable checked logging on the ordinary unoccupied branch

The branch is a measurable subtype of the existing `ObservationInput`. All
registers, ordered buffer keys, original continuous saved scalars, the whole
current row, active calendar time, played arm and grid feedback vary. No buffer
validity, freshness, positive feedback or successful logging premise is imposed.
The observable returns the actual logging failure or the accepted carried state.
Its decoder only reconstructs that returned carry; it never calls logging.

Sources: `sources/zip4/manuscript/05_binary_transport.tex:354-389`,
`sources/zip4/manuscript/06_interruptions.tex:235-276`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:6-14`.
This internal local branch result does not implement reference DOWN, service,
release, finish, a follower tail, a physical run, or a manuscript theorem.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped Classical
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.SparseCalendarReplay
open Bandits.Support.FollowerDownMeasurability
open Bandits.Support.FollowerDownJointMeasurability
open Bandits.Support.FollowerLoggingDownMeasurability
open Bandits.Support.FollowerObservationStageMeasurabilityRepair

namespace Bandits.Support.ReferenceFollowerLoggingMeasurability

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ActiveFollowerDownAcceptance.RateInput
abbrev CarriedState (p : Parameters) (rate : RateInput p) :=
  FollowerObservationStageMeasurabilityRepair.CarriedState p rate


/-- Checked logging either fails, leaves the original buffer, or appends the
literal current record.  It is an auxiliary code, not protocol state. -/
private inductive CheckedLoggingCode where
  | failure (reason : Fin 2)
  | retained
  | appended
  deriving DecidableEq, Countable

private instance checkedLoggingCodeMeasurableSpace : MeasurableSpace CheckedLoggingCode := ⊤

private inductive LoggingBufferChange where
  | retained
  | appendedCurrent
  deriving DecidableEq, Countable

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
  · intro x y hxy
    cases hxy
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

private abbrev SavedScalar := FollowerDownMeasurability.SavedScalar
private abbrev SavedScalarFamily (n : ℕ) := FollowerDownMeasurability.SavedScalarFamily n
private abbrev ObservationKey (p : Parameters) := ℕ × Fin p.K

private def appendSavedScalarFamily {n : ℕ}
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
        exact (measurable_pi_apply j).comp hvalues
      simpa only [appendSavedScalarFamily, Fin.lastCases_castSucc] using hvalue
  | last =>
      simpa [appendSavedScalarFamily] using hlast

private def appendCarriedState {p : Parameters} {rate : RateInput p}
    (state : CarriedState p rate)
    (stateCode : FollowerDownMeasurability.FollowerStateCode p rate)
    (key : ObservationKey p) (saved : SavedScalar) : CarriedState p rate :=
  ⟨(stateCode,
      ⟨state.1.2.1 + 1, Fin.lastCases key (fun j => state.1.2.2 j)⟩),
    appendSavedScalarFamily state.2 saved⟩


private def appendPayloadToCarriedState {p : Parameters} {rate : RateInput p}
    (index : FollowerObservationStageMeasurabilityRepair.FollowerCarryIndex p rate)
    (stateCode : FollowerDownMeasurability.FollowerStateCode p rate)
    (x : Sigma fun _key : ObservationKey p => SavedScalarFamily (index.2.1 + 1)) :
    CarriedState p rate :=
  ⟨(stateCode,
      ⟨index.2.1 + 1, Fin.lastCases x.1 (fun j => index.2.2 j)⟩), x.2⟩

private theorem measurable_appendPayloadToCarriedState {p : Parameters}
    {rate : RateInput p}
    (index : FollowerObservationStageMeasurabilityRepair.FollowerCarryIndex p rate)
    (stateCode : FollowerDownMeasurability.FollowerStateCode p rate) :
    Measurable (appendPayloadToCarriedState index stateCode) := by
  apply measurable_of_sigma_sections
  intro key
  let extended : FollowerObservationStageMeasurabilityRepair.FollowerCarryIndex p rate :=
    (stateCode, ⟨index.2.1 + 1, Fin.lastCases key (fun j => index.2.2 j)⟩)
  exact measurable_sigmaMk (α := FollowerObservationStageMeasurabilityRepair.FollowerCarryIndex p rate)
    (β := fun x : FollowerObservationStageMeasurabilityRepair.FollowerCarryIndex p rate =>
      SavedScalarFamily x.2.1) extended

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
        Sigma fun index : FollowerObservationStageMeasurabilityRepair.FollowerCarryIndex p rate =>
          SavedScalarFamily index.2.1 × rest)) := by
    exact measurable_assembleSigmaProduct.comp
      (hstate.prodMk (hkey.prodMk hsaved))
  have hfiber (index : FollowerObservationStageMeasurabilityRepair.FollowerCarryIndex p rate) :
      Measurable (fun x : SavedScalarFamily index.2.1 × rest =>
        appendCarriedState (⟨index, x.1⟩ : CarriedState p rate)
          stateCode x.2.1 x.2.2) := by
    let label : SavedScalarFamily index.2.1 × rest → ObservationKey p :=
      fun x => x.2.1
    have hlabel : Measurable label :=
      measurable_fst.comp (measurable_snd.comp measurable_id)
    let fiber : ∀ a : ObservationKey p,
        {x : SavedScalarFamily index.2.1 × rest // label x = a} →
          SavedScalarFamily (index.2.1 + 1) :=
      fun _ x => appendSavedScalarFamily x.1.1 x.1.2.2
    have hfiber (a : ObservationKey p) : Measurable (fiber a) := by
      have hvalues : Measurable (fun x : {x : SavedScalarFamily index.2.1 × rest //
          label x = a} => x.1.1) :=
        measurable_fst.comp measurable_subtype_coe
      have hlast : Measurable (fun x : {x : SavedScalarFamily index.2.1 × rest //
          label x = a} => x.1.2.2) :=
        measurable_snd.comp (measurable_snd.comp measurable_subtype_coe)
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
    (f := fun x : Sigma fun index :
        FollowerObservationStageMeasurabilityRepair.FollowerCarryIndex p rate =>
        SavedScalarFamily index.2.1 × rest =>
      appendCarriedState (⟨x.1, x.2.1⟩ : CarriedState p rate)
        stateCode x.2.2.1 x.2.2.2) hfiber
  have htarget : (fun ω =>
      appendCarriedState (state ω) stateCode (key ω) (saved ω)) =
    (fun x : Sigma fun index :
        FollowerObservationStageMeasurabilityRepair.FollowerCarryIndex p rate =>
        SavedScalarFamily index.2.1 × rest =>
      appendCarriedState (⟨x.1, x.2.1⟩ : CarriedState p rate)
        stateCode x.2.2.1 x.2.2.2) ∘
      (fun ω => (⟨(state ω).1, ((state ω).2, (key ω, saved ω))⟩ :
        Sigma fun index : FollowerObservationStageMeasurabilityRepair.FollowerCarryIndex p rate =>
          SavedScalarFamily index.2.1 × rest)) := by
    funext ω
    rfl
  rw [htarget]
  exact hsection.comp hassemble

private def currentSavedScalar {p : Parameters} (row : CompletePublicTable.CompleteRow p)
    (time : Fin p.T) (feedback : Fin (D p + 1)) : SavedScalar :=
  ((FollowerDownMeasurability.feedbackAtGrid p feedback).val,
    (row.2 time).1 ContinuousControlSlice.Label.thin)

private theorem measurable_finIndex_eval {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] (n : ℕ) (f : Fin n → α → β)
    (hf : ∀ j, Measurable (f j)) : Measurable (fun z : α × Fin n => f z.2 z.1) := by
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
    exact (measurableSet_singleton j).preimage measurable_snd |>.inter
      (((hf j).comp measurable_fst) hs)

private theorem measurable_currentSavedScalar {p : Parameters}
    {Ω : Type*} [MeasurableSpace Ω]
    (row : Ω → CompletePublicTable.CompleteRow p) (time : Ω → Fin p.T)
    (feedback : Ω → Fin (D p + 1))
    (hrow : Measurable row) (htime : Measurable time)
    (hfeedback : Measurable feedback) :
    Measurable (fun ω => currentSavedScalar (row ω) (time ω) (feedback ω)) := by
  have hlearning : Measurable
      (fun ω => CompletePublicTable.completeRowLearning p (row ω)) :=
    (CompletePublicTable.measurable_completeRowLearning p).comp hrow
  have hthinAt (t : Fin p.T) : Measurable
      (fun learning : ContinuousLearningRows.LearningRow p =>
        ContinuousLearningRows.scalarAt t ContinuousControlSlice.Label.thin learning) :=
    ContinuousLearningRows.measurable_scalarAt t ContinuousControlSlice.Label.thin
  have hthin : Measurable (fun ω =>
      ContinuousLearningRows.scalarAt (time ω) ContinuousControlSlice.Label.thin
        (CompletePublicTable.completeRowLearning p (row ω))) :=
    (measurable_finIndex_eval p.T
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

private theorem measurable_decideOfSet {Ω : Type*} [MeasurableSpace Ω]
    (P : Ω → Prop) (hP : MeasurableSet {ω | P ω}) :
    Measurable (fun ω => @decide (P ω) (Classical.propDecidable (P ω))) := by
  classical
  apply FollowerDownMeasurability.measurable_of_countable_fibers
  intro b
  cases b with
  | false =>
      have hset : {ω | decide (P ω) = false} = {ω | P ω}ᶜ := by
        ext ω
        simp
      rw [hset]
      exact hP.compl
  | true =>
      have hset : {ω | decide (P ω) = true} = {ω | P ω} := by
        ext ω
        simp
      rw [hset]
      exact hP

private theorem measurable_loggingInputOfFiber {p : Parameters}
    {rate : RateInput p} {activation : Activation p}
    (index : FollowerObservationStageMeasurabilityRepair.FollowerCarryIndex p rate) :
    Measurable (FollowerObservationStageMeasurabilityRepair.loggingInputOfFiber
      (p := p) (rate := rate) (activation := activation) (index := index)) := by
  let values : SavedScalarFamily index.2.1 → SavedScalarFamily
      (FollowerObservationStageMeasurabilityRepair.representativeState rate index).buffer.length :=
    FollowerObservationStageMeasurabilityRepair.representativeValues index
  have hvalues : Measurable values := by
    apply measurable_pi_iff.mpr
    intro j
    exact measurable_pi_apply
      (Fin.cast (FollowerObservationStageMeasurabilityRepair.sparseSkeletonBuffer_length
        index.2.2) j)
  change Measurable (fun x : FollowerObservationStageMeasurabilityRepair.ObservationFiber
      p rate activation index =>
    ((((x.2.1.1.1, x.2.1.1.2), (x.2.1.2, x.2.2)), values x.1)))
  have hrow : Measurable (fun x : FollowerObservationStageMeasurabilityRepair.ObservationFiber
      p rate activation index => x.2.1.1.1) :=
    measurable_fst.comp (measurable_fst.comp (measurable_fst.comp
      (measurable_snd.comp measurable_id)))
  have htime : Measurable (fun x : FollowerObservationStageMeasurabilityRepair.ObservationFiber
      p rate activation index => x.2.1.1.2) :=
    measurable_snd.comp (measurable_fst.comp (measurable_fst.comp
      (measurable_snd.comp measurable_id)))
  have hfeedback : Measurable (fun x : FollowerObservationStageMeasurabilityRepair.ObservationFiber
      p rate activation index => x.2.1.2) :=
    measurable_snd.comp (measurable_fst.comp (measurable_snd.comp measurable_id))
  have harm : Measurable (fun x : FollowerObservationStageMeasurabilityRepair.ObservationFiber
      p rate activation index => x.2.2) :=
    measurable_snd.comp (measurable_snd.comp measurable_id)
  exact ((((hrow.prodMk htime).prodMk (hfeedback.prodMk harm)).prodMk
    (hvalues.comp measurable_fst)))

/-- Finite code for the checked logger on one fixed original carry fiber.
The append bit retains the row's own thin scalar through `currentSavedScalar`.
-/
private def checkedLoggingCodeOnFiber {p : Parameters} (rate : RateInput p)
    (i : Fin (p.m - 1)) (activation : Activation p)
    (index : FollowerObservationStageMeasurabilityRepair.FollowerCarryIndex p rate)
    (x : FollowerObservationStageMeasurabilityRepair.ObservationFiber p rate activation index) :
    CheckedLoggingCode := by
  classical
  let state := FollowerObservationStageMeasurabilityRepair.representativeState rate index
  let input := FollowerObservationStageMeasurabilityRepair.loggingInputOfFiber x
  if state.status = .unoccupied then
    if ActiveFollowerLifecycle.localBufferValid
        (FollowerDownMeasurability.adaptedInputState rate state
          (FollowerLoggingDownMeasurability.inputSavedScalars input)) then
      if FollowerLoggingDownMeasurability.loggingGateBit i input then
        if FollowerLoggingDownMeasurability.currentKeyFresh input then
          exact .appended
        else exact .failure 1
      else exact .retained
    else exact .failure 0
  else exact .retained

private theorem measurable_checkedLoggingCodeOnFiber {p : Parameters}
    (rate : RateInput p) (i : Fin (p.m - 1)) (activation : Activation p)
    (index : FollowerObservationStageMeasurabilityRepair.FollowerCarryIndex p rate) :
    Measurable (checkedLoggingCodeOnFiber rate i activation index) := by
  classical
  let state := FollowerObservationStageMeasurabilityRepair.representativeState rate index
  let input := FollowerObservationStageMeasurabilityRepair.loggingInputOfFiber
    (p := p) (rate := rate) (activation := activation) (index := index)
  have hinput := measurable_loggingInputOfFiber (p := p) (rate := rate)
    (activation := activation) index
  by_cases hstatus : state.status = .unoccupied
  · let valid : FollowerObservationStageMeasurabilityRepair.ObservationFiber
        p rate activation index → Bool := fun x => decide
          (ActiveFollowerLifecycle.localBufferValid
            (FollowerDownMeasurability.adaptedInputState rate state
              (FollowerLoggingDownMeasurability.inputSavedScalars (input x))))
    have hvalid : Measurable valid := by
      apply measurable_decideOfSet
      exact FollowerLoggingDownMeasurability.measurableSet_adaptedState_localBufferValid
        rate activation state |>.preimage hinput
    have hgate : Measurable (fun x => FollowerLoggingDownMeasurability.loggingGateBit i
        (input x)) :=
      (FollowerLoggingDownMeasurability.measurable_loggingGateBit i rate activation state).comp
        hinput
    let fresh : FollowerObservationStageMeasurabilityRepair.ObservationFiber
        p rate activation index → Bool := fun x => decide
          (FollowerLoggingDownMeasurability.currentKeyFresh (input x))
    have hfresh : Measurable fresh := by
      apply measurable_decideOfSet
      exact FollowerLoggingDownMeasurability.measurableSet_currentKeyFresh
        rate activation state |>.preimage hinput
    let bits : FollowerObservationStageMeasurabilityRepair.ObservationFiber
        p rate activation index → Bool × (Bool × Bool) :=
      fun x => (valid x, (FollowerLoggingDownMeasurability.loggingGateBit i (input x), fresh x))
    have hbits : Measurable bits := hvalid.prodMk (hgate.prodMk hfresh)
    let fromBits : Bool × (Bool × Bool) → CheckedLoggingCode := fun b =>
      if b.1 then
        if b.2.1 then
          if b.2.2 then .appended else .failure 1
        else .retained
      else .failure 0
    have hfromBits : Measurable fromBits := measurable_of_finite fromBits
    have heq : checkedLoggingCodeOnFiber rate i activation index = fromBits ∘ bits := by
      funext x
      simp [checkedLoggingCodeOnFiber, state, input, valid, fresh, bits, fromBits,
        hstatus, decide_eq_true_eq]
    rw [heq]
    exact hfromBits.comp hbits
  · have heq : checkedLoggingCodeOnFiber rate i activation index = fun _ => .retained := by
      funext x
      simp [checkedLoggingCodeOnFiber, state, hstatus]
    rw [heq]
    exact measurable_const

private def checkedLoggingCode {p : Parameters} (rate : RateInput p)
    (i : Fin (p.m - 1)) (activation : Activation p)
    (x : FollowerObservationStageMeasurabilityRepair.ObservationInput p rate activation) :
    CheckedLoggingCode :=
  checkedLoggingCodeOnFiber rate i activation x.1 x.2

private theorem measurable_checkedLoggingCode {p : Parameters} (rate : RateInput p)
    (i : Fin (p.m - 1)) (activation : Activation p) :
    Measurable (checkedLoggingCode rate i activation) := by
  apply measurable_of_sigma_sections
  intro index
  exact measurable_checkedLoggingCodeOnFiber rate i activation index

private def loggedCarriedState {p : Parameters} {rate : RateInput p}
    (carry : CarriedState p rate) (change : LoggingBufferChange)
    (row : CompletePublicTable.CompleteRow p) (time : Fin p.T)
    (feedback : Fin (D p + 1)) (arm : Fin p.K) : CarriedState p rate :=
  match change with
  | .retained => carry
  | .appendedCurrent =>
      appendCarriedState carry carry.1.1 ((time.val + 1, arm))
        (currentSavedScalar row time feedback)

private def loggedCarriedStateOnObservationFiber {p : Parameters} {rate : RateInput p}
    {activation : Activation p}
    (index : FollowerObservationStageMeasurabilityRepair.FollowerCarryIndex p rate)
    (change : LoggingBufferChange)
    (x : FollowerObservationStageMeasurabilityRepair.ObservationFiber p rate activation index) :
    CarriedState p rate :=
  loggedCarriedState ⟨index, x.1⟩ change
    (FollowerObservationStageMeasurabilityRepair.fiberRow x)
    (FollowerObservationStageMeasurabilityRepair.fiberTime x).1
    (FollowerObservationStageMeasurabilityRepair.fiberFeedbackIndex x)
    (FollowerObservationStageMeasurabilityRepair.fiberPlayedArm x)

private theorem measurable_loggedCarriedStateOnFiber {p : Parameters}
    (rate : RateInput p) (activation : Activation p)
    (index : FollowerObservationStageMeasurabilityRepair.FollowerCarryIndex p rate)
    (change : LoggingBufferChange) :
    Measurable (fun x : FollowerObservationStageMeasurabilityRepair.ObservationFiber
        p rate activation index =>
      loggedCarriedState (⟨index, x.1⟩ : CarriedState p rate) change
        (FollowerObservationStageMeasurabilityRepair.fiberRow x)
        (FollowerObservationStageMeasurabilityRepair.fiberTime x).1
        (FollowerObservationStageMeasurabilityRepair.fiberFeedbackIndex x)
        (FollowerObservationStageMeasurabilityRepair.fiberPlayedArm x)) := by
  cases change with
  | retained =>
      exact (measurable_sigmaMk index).comp measurable_fst
  | appendedCurrent =>
      let carry : FollowerObservationStageMeasurabilityRepair.ObservationFiber
          p rate activation index → CarriedState p rate := fun x => ⟨index, x.1⟩
      let time : FollowerObservationStageMeasurabilityRepair.ObservationFiber
          p rate activation index → Fin p.T := fun x =>
        (FollowerObservationStageMeasurabilityRepair.fiberTime x).1
      let timeSubtype : FollowerObservationStageMeasurabilityRepair.ObservationFiber
          p rate activation index → FollowerObservationStageMeasurabilityRepair.ActiveTime
            p activation := FollowerObservationStageMeasurabilityRepair.fiberTime
      let row : FollowerObservationStageMeasurabilityRepair.ObservationFiber
          p rate activation index → CompletePublicTable.CompleteRow p :=
        FollowerObservationStageMeasurabilityRepair.fiberRow
      let feedback : FollowerObservationStageMeasurabilityRepair.ObservationFiber
          p rate activation index → Fin (D p + 1) :=
        FollowerObservationStageMeasurabilityRepair.fiberFeedbackIndex
      let arm : FollowerObservationStageMeasurabilityRepair.ObservationFiber
          p rate activation index → Fin p.K :=
        FollowerObservationStageMeasurabilityRepair.fiberPlayedArm
      have hcarry : Measurable carry :=
        (measurable_sigmaMk index).comp measurable_fst
      have hrow : Measurable row :=
        measurable_fst.comp (measurable_fst.comp (measurable_fst.comp
          (measurable_snd.comp measurable_id)))
      have htimeSubtype : Measurable timeSubtype :=
        measurable_snd.comp (measurable_fst.comp (measurable_fst.comp
          (measurable_snd.comp measurable_id)))
      have htime : Measurable time := measurable_subtype_coe.comp htimeSubtype
      have hfeedback : Measurable feedback :=
        measurable_snd.comp (measurable_fst.comp (measurable_snd.comp measurable_id))
      have harm : Measurable arm := measurable_snd.comp (measurable_snd.comp measurable_id)
      let key : FollowerObservationStageMeasurabilityRepair.ObservationFiber
          p rate activation index → ObservationKey p :=
        fun x => ((time x).val + 1, arm x)
      have hkey : Measurable key := measurable_currentObservationKey time arm htime harm
      let saved : FollowerObservationStageMeasurabilityRepair.ObservationFiber
          p rate activation index → SavedScalar :=
        fun x => currentSavedScalar (row x) (time x) (feedback x)
      have hsaved : Measurable saved :=
        measurable_currentSavedScalar row time feedback hrow htime hfeedback
      have happend := measurable_appendCarriedState carry index.1 key saved
        hcarry hkey hsaved
      simpa [carry, time, row, feedback, arm, key, saved, loggedCarriedState,
        FollowerObservationStageMeasurabilityRepair.fiberTime] using happend

private theorem reconstruct_appendCarriedState {p : Parameters} {rate : RateInput p}
    (carry : CarriedState p rate)
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


private theorem decoderBatchCode_ofCode {p : Parameters}
    (batch : FollowerDownMeasurability.DecoderBatchCode p) :
    FollowerDownMeasurability.decoderBatchCode
        (FollowerDownMeasurability.decoderBatchOfCode batch) = batch := by
  rcases batch with ⟨pending, completed⟩
  have hentry (e : FollowerDownMeasurability.DecoderEntryCode p) :
      FollowerDownMeasurability.decoderEntryCode
          (FollowerDownMeasurability.decoderEntryOfCode e) = e := by
    rcases e with ⟨time, sample⟩
    rfl
  have hmap (entries : List (FollowerDownMeasurability.DecoderEntryCode p)) :
      List.map (FollowerDownMeasurability.decoderEntryCode ∘
        FollowerDownMeasurability.decoderEntryOfCode) entries = entries := by
    induction entries with
    | nil => rfl
    | cons entry entries ih => simp [Function.comp, hentry, ih]
  have hmap2 (entries : List (List (FollowerDownMeasurability.DecoderEntryCode p))) :
      List.map (List.map (FollowerDownMeasurability.decoderEntryCode ∘
        FollowerDownMeasurability.decoderEntryOfCode)) entries = entries := by
    induction entries with
    | nil => rfl
    | cons entry entries ih => simp [hmap, ih]
  simp [FollowerDownMeasurability.decoderBatchCode,
    FollowerDownMeasurability.decoderBatchOfCode, hmap, hmap2]

private theorem followerStateCode_ofCode {p : Parameters} {rate : RateInput p}
    (code : FollowerDownMeasurability.FollowerStateCode p rate)
    (buffer : List (SparseCalendarRecord p.K)) :
    FollowerDownMeasurability.followerStateCode rate
      (FollowerDownMeasurability.followerStateOfCode rate code buffer) = code := by
  cases code with
  | mk lastDown S delta backlog status downBatch initializationFailure =>
    have hstatus : FollowerDownMeasurability.followerStatusCode
        (FollowerDownMeasurability.followerStatusOfCode status) = status := by
      fin_cases status <;> rfl
    simp [FollowerDownMeasurability.followerStateCode,
      FollowerDownMeasurability.followerStateOfCode, hstatus,
      decoderBatchCode_ofCode]


private def reconstructCheckedLoggingCode {p : Parameters} {rate : RateInput p}
    {activation : Activation p}
    (index : FollowerObservationStageMeasurabilityRepair.FollowerCarryIndex p rate)
    (x : FollowerObservationStageMeasurabilityRepair.ObservationFiber p rate activation index)
    (code : CheckedLoggingCode) : Except ActiveFollowerLogging.LoggingFailure
      (ReferencePrelaunchFollower.State p rate.eta) :=
  match code with
  | .failure reason => .error
      (FollowerLoggingDownMeasurability.loggingFailureOfCode reason)
  | .retained => .ok
      (FollowerObservationStageMeasurabilityRepair.reconstructCarriedState index x.1)
  | .appended => .ok
      (FollowerObservationStageMeasurabilityRepair.reconstructCarriedState
        (loggedCarriedState ⟨index, x.1⟩ .appendedCurrent
          (FollowerObservationStageMeasurabilityRepair.fiberRow x)
          (FollowerObservationStageMeasurabilityRepair.fiberTime x).1
          (FollowerObservationStageMeasurabilityRepair.fiberFeedbackIndex x)
          (FollowerObservationStageMeasurabilityRepair.fiberPlayedArm x)).1
        (loggedCarriedState ⟨index, x.1⟩ .appendedCurrent
          (FollowerObservationStageMeasurabilityRepair.fiberRow x)
          (FollowerObservationStageMeasurabilityRepair.fiberTime x).1
          (FollowerObservationStageMeasurabilityRepair.fiberFeedbackIndex x)
          (FollowerObservationStageMeasurabilityRepair.fiberPlayedArm x)).2)

private theorem localBufferValid_loggingAppend_iff {p : Parameters}
    {rate : RateInput p} {activation : Activation p}
    (i : Fin (p.m - 1)) (state : ReferencePrelaunchFollower.State p rate.eta)
    (x : FollowerLoggingDownMeasurability.LoggingDownInput p rate activation state) :
    ActiveFollowerLifecycle.localBufferValid
        {FollowerDownMeasurability.adaptedInputState rate state
          (FollowerLoggingDownMeasurability.inputSavedScalars x) with
          buffer := (FollowerDownMeasurability.adaptedInputState rate state
            (FollowerLoggingDownMeasurability.inputSavedScalars x)).buffer ++
            [FollowerLoggingDownMeasurability.currentLoggingRecord i activation x]} ↔
      ActiveFollowerLifecycle.localBufferValid
        (FollowerDownMeasurability.adaptedInputState rate state
          (FollowerLoggingDownMeasurability.inputSavedScalars x)) ∧
        FollowerLoggingDownMeasurability.currentKeyFresh x := by
  classical
  let localState := FollowerDownMeasurability.adaptedInputState rate state
    (FollowerLoggingDownMeasurability.inputSavedScalars x)
  let record := FollowerLoggingDownMeasurability.currentLoggingRecord i activation x
  have hrange : 1 ≤ record.calendarRound ∧ record.calendarRound ≤ p.T := by
    simp [record, FollowerLoggingDownMeasurability.currentLoggingRecord,
      SparseCalendarReplay.recordAt, FollowerLoggingDownMeasurability.inputTime]
  have hgrid : ∃ q : ℕ, q ≤ D p ∧ record.observation.val = (q : ℝ) / (D p : ℝ) := by
    exact ActiveFollowerLogging.recordAt_observation_grid i
      (FollowerLoggingDownMeasurability.inputRow x) activation
      (FollowerLoggingDownMeasurability.inputTime x)
      (FollowerLoggingDownMeasurability.inputPlayedArm x,
        FollowerDownMeasurability.feedbackAtGrid p
          (FollowerLoggingDownMeasurability.inputFeedbackIndex x))
  have hkeys : localState.buffer.map ActiveFollowerQueueOperation.bufferKey =
      state.buffer.map ActiveFollowerQueueOperation.bufferKey := by
    simp only [localState, FollowerDownMeasurability.adaptedInputState]
    exact FollowerServiceMeasurability.replaceBufferScalars_mapBufferKey
      state.buffer (FollowerLoggingDownMeasurability.inputSavedScalars x)
  rw [FollowerLoggingDownMeasurability.localBufferValid_append_iff
    localState record hrange hgrid]
  change ActiveFollowerLifecycle.localBufferValid localState ∧
      (∀ old ∈ localState.buffer,
        (old.calendarRound, old.pilot) ≠ (record.calendarRound, record.pilot)) ↔
    ActiveFollowerLifecycle.localBufferValid localState ∧
      FollowerLoggingDownMeasurability.currentKeyFresh x
  have hrecordKey : ActiveFollowerQueueOperation.bufferKey record =
      ((FollowerLoggingDownMeasurability.inputTime x).val + 1,
        FollowerLoggingDownMeasurability.inputPlayedArm x) := by
    simp [ActiveFollowerQueueOperation.bufferKey, record,
      FollowerLoggingDownMeasurability.currentLoggingRecord,
      SparseCalendarReplay.recordAt, FollowerLoggingDownMeasurability.inputTime,
      FollowerLoggingDownMeasurability.inputPlayedArm,
      ReferencePrelaunchFollower.loggingRound]
  constructor
  · rintro ⟨hvalid, hfresh⟩
    refine ⟨hvalid, ?_⟩
    intro old hold heq
    have hmem : ActiveFollowerQueueOperation.bufferKey old ∈
        state.buffer.map ActiveFollowerQueueOperation.bufferKey := by
      exact List.mem_map.mpr ⟨old, hold, rfl⟩
    rw [← hkeys] at hmem
    obtain ⟨original, horiginal, hkey⟩ := List.mem_map.mp hmem
    have heqOld : ActiveFollowerQueueOperation.bufferKey old =
        ((FollowerLoggingDownMeasurability.inputTime x).val + 1,
          FollowerLoggingDownMeasurability.inputPlayedArm x) := by
      simpa [ActiveFollowerQueueOperation.bufferKey] using heq
    have heqRecord : ActiveFollowerQueueOperation.bufferKey original =
        ActiveFollowerQueueOperation.bufferKey record := by
      exact hkey.trans (heqOld.trans hrecordKey.symm)
    exact (hfresh original horiginal) heqRecord
  · rintro ⟨hvalid, hfresh⟩
    refine ⟨hvalid, ?_⟩
    intro old hold heq
    have hmemLocal : ActiveFollowerQueueOperation.bufferKey old ∈
        localState.buffer.map ActiveFollowerQueueOperation.bufferKey :=
      List.mem_map.mpr ⟨old, hold, rfl⟩
    have hmem : ActiveFollowerQueueOperation.bufferKey old ∈
        state.buffer.map ActiveFollowerQueueOperation.bufferKey := by
      rw [hkeys] at hmemLocal
      exact hmemLocal
    obtain ⟨original, horiginal, hkey⟩ := List.mem_map.mp hmem
    have heqOld : ActiveFollowerQueueOperation.bufferKey old =
        ActiveFollowerQueueOperation.bufferKey record := by
      simpa [ActiveFollowerQueueOperation.bufferKey] using heq
    have heqInput : ActiveFollowerQueueOperation.bufferKey original =
        ((FollowerLoggingDownMeasurability.inputTime x).val + 1,
          FollowerLoggingDownMeasurability.inputPlayedArm x) := by
      exact hkey.trans (heqOld.trans hrecordKey)
    exact (hfresh original horiginal) (by
      simpa [ActiveFollowerQueueOperation.bufferKey] using heqInput)

private theorem checkedLoggingCodeOnFiber_reconstruct {p : Parameters}
    (rate : RateInput p) (i : Fin (p.m - 1)) (activation : Activation p)
    (index : FollowerObservationStageMeasurabilityRepair.FollowerCarryIndex p rate)
    (x : FollowerObservationStageMeasurabilityRepair.ObservationFiber p rate activation index)
    (hstatus : (FollowerObservationStageMeasurabilityRepair.reconstructCarriedState
      index x.1).status = .unoccupied) :
    reconstructCheckedLoggingCode index x
        (checkedLoggingCodeOnFiber rate i activation index x) =
      ActiveFollowerLogging.checkedLogging i
        (FollowerObservationStageMeasurabilityRepair.fiberRow x) activation
        (FollowerObservationStageMeasurabilityRepair.fiberTime x).1
        (FollowerObservationStageMeasurabilityRepair.fiberPlayedArm x,
          FollowerDownMeasurability.feedbackAtGrid p
            (FollowerObservationStageMeasurabilityRepair.fiberFeedbackIndex x))
        (FollowerObservationStageMeasurabilityRepair.reconstructCarriedState index x.1) := by
  classical
  let state := FollowerObservationStageMeasurabilityRepair.representativeState rate index
  let input := FollowerObservationStageMeasurabilityRepair.loggingInputOfFiber x
  let actual := FollowerObservationStageMeasurabilityRepair.reconstructCarriedState index x.1
  let localState := FollowerDownMeasurability.adaptedInputState rate state
    (FollowerLoggingDownMeasurability.inputSavedScalars input)
  have hstate : localState = actual :=
    FollowerObservationStageMeasurabilityRepair.adaptedRepresentativeState_eq_reconstruct
      index x.1
  have hstatus' : state.status = .unoccupied := by
    calc
      state.status = localState.status := by
        simp [localState, FollowerDownMeasurability.adaptedInputState]
      _ = actual.status := congrArg ReferencePrelaunchFollower.State.status hstate
      _ = .unoccupied := hstatus
  have hlocalStatus : localState.status = .unoccupied := by
    simpa [localState, FollowerDownMeasurability.adaptedInputState] using hstatus'
  have hactive : activation.val ≤
      (FollowerObservationStageMeasurabilityRepair.fiberTime x).1.val + 1 :=
    (FollowerObservationStageMeasurabilityRepair.fiberTime x).2
  have hgate : FollowerLoggingDownMeasurability.loggingGateBit i input = true ↔
      SparseCalendarReplay.loggingTestsPass
        (ReferencePrelaunchFollower.loggingRound i
          (FollowerObservationStageMeasurabilityRepair.fiberRow x) activation
          (FollowerObservationStageMeasurabilityRepair.fiberTime x).1
          (FollowerObservationStageMeasurabilityRepair.fiberPlayedArm x,
            FollowerDownMeasurability.feedbackAtGrid p
              (FollowerObservationStageMeasurabilityRepair.fiberFeedbackIndex x))) := by
    exact FollowerLoggingDownMeasurability.loggingGateBit_true_iff_testsPass
      i rate activation state input
  let localBufferValid' := ActiveFollowerLifecycle.localBufferValid localState
  let currentFresh := FollowerLoggingDownMeasurability.currentKeyFresh input
  let currentRecord := FollowerLoggingDownMeasurability.currentLoggingRecord i activation input
  have hrecord : currentRecord = SparseCalendarReplay.recordAt
      ((FollowerObservationStageMeasurabilityRepair.fiberTime x).1.val + 1)
        (ReferencePrelaunchFollower.loggingRound i
          (FollowerObservationStageMeasurabilityRepair.fiberRow x) activation
          (FollowerObservationStageMeasurabilityRepair.fiberTime x).1
          (FollowerObservationStageMeasurabilityRepair.fiberPlayedArm x,
            FollowerDownMeasurability.feedbackAtGrid p
              (FollowerObservationStageMeasurabilityRepair.fiberFeedbackIndex x))) := rfl
  have hupdateKeep (htests : ¬ SparseCalendarReplay.loggingTestsPass
      (ReferencePrelaunchFollower.loggingRound i
        (FollowerObservationStageMeasurabilityRepair.fiberRow x) activation
        (FollowerObservationStageMeasurabilityRepair.fiberTime x).1
        (FollowerObservationStageMeasurabilityRepair.fiberPlayedArm x,
          FollowerDownMeasurability.feedbackAtGrid p
            (FollowerObservationStageMeasurabilityRepair.fiberFeedbackIndex x)))) :
      ActiveFollowerLogging.loggingUpdate i
        (FollowerObservationStageMeasurabilityRepair.fiberRow x) activation
        (FollowerObservationStageMeasurabilityRepair.fiberTime x).1
        (FollowerObservationStageMeasurabilityRepair.fiberPlayedArm x,
          FollowerDownMeasurability.feedbackAtGrid p
            (FollowerObservationStageMeasurabilityRepair.fiberFeedbackIndex x)) localState =
        localState := by
    unfold ActiveFollowerLogging.loggingUpdate
    rw [ite_eq_left ⟨hactive, hlocalStatus⟩]
    rw [ActiveFollowerLogging.logAt_eq_nil_of_not_tests i
      (FollowerObservationStageMeasurabilityRepair.fiberRow x) activation
      (FollowerObservationStageMeasurabilityRepair.fiberTime x).1
      (FollowerObservationStageMeasurabilityRepair.fiberPlayedArm x,
        FollowerDownMeasurability.feedbackAtGrid p
          (FollowerObservationStageMeasurabilityRepair.fiberFeedbackIndex x)) htests]
    cases localState
    simp
  have hupdateAppend (htests : SparseCalendarReplay.loggingTestsPass
      (ReferencePrelaunchFollower.loggingRound i
        (FollowerObservationStageMeasurabilityRepair.fiberRow x) activation
        (FollowerObservationStageMeasurabilityRepair.fiberTime x).1
        (FollowerObservationStageMeasurabilityRepair.fiberPlayedArm x,
          FollowerDownMeasurability.feedbackAtGrid p
            (FollowerObservationStageMeasurabilityRepair.fiberFeedbackIndex x)))) :
      ActiveFollowerLogging.loggingUpdate i
      (FollowerObservationStageMeasurabilityRepair.fiberRow x) activation
      (FollowerObservationStageMeasurabilityRepair.fiberTime x).1
      (FollowerObservationStageMeasurabilityRepair.fiberPlayedArm x,
        FollowerDownMeasurability.feedbackAtGrid p
          (FollowerObservationStageMeasurabilityRepair.fiberFeedbackIndex x)) localState =
      {localState with buffer := localState.buffer ++ [currentRecord]} := by
    unfold ActiveFollowerLogging.loggingUpdate
    rw [ite_eq_left ⟨hactive, hlocalStatus⟩]
    rw [ActiveFollowerLogging.logAt_eq_singleton_of_tests i
      (FollowerObservationStageMeasurabilityRepair.fiberRow x) activation
      (FollowerObservationStageMeasurabilityRepair.fiberTime x).1
      (FollowerObservationStageMeasurabilityRepair.fiberPlayedArm x,
        FollowerDownMeasurability.feedbackAtGrid p
          (FollowerObservationStageMeasurabilityRepair.fiberFeedbackIndex x)) htests]
    rw [hrecord]
  have hloggedAppend (htests : SparseCalendarReplay.loggingTestsPass
      (ReferencePrelaunchFollower.loggingRound i
        (FollowerObservationStageMeasurabilityRepair.fiberRow x) activation
        (FollowerObservationStageMeasurabilityRepair.fiberTime x).1
        (FollowerObservationStageMeasurabilityRepair.fiberPlayedArm x,
          FollowerDownMeasurability.feedbackAtGrid p
            (FollowerObservationStageMeasurabilityRepair.fiberFeedbackIndex x)))) :
      FollowerObservationStageMeasurabilityRepair.reconstructCarriedState
        (loggedCarriedState ⟨index, x.1⟩ .appendedCurrent
          (FollowerObservationStageMeasurabilityRepair.fiberRow x)
          (FollowerObservationStageMeasurabilityRepair.fiberTime x).1
          (FollowerObservationStageMeasurabilityRepair.fiberFeedbackIndex x)
          (FollowerObservationStageMeasurabilityRepair.fiberPlayedArm x)).1
        (loggedCarriedState ⟨index, x.1⟩ .appendedCurrent
          (FollowerObservationStageMeasurabilityRepair.fiberRow x)
          (FollowerObservationStageMeasurabilityRepair.fiberTime x).1
          (FollowerObservationStageMeasurabilityRepair.fiberFeedbackIndex x)
          (FollowerObservationStageMeasurabilityRepair.fiberPlayedArm x)).2 =
      ActiveFollowerLogging.loggingUpdate i
        (FollowerObservationStageMeasurabilityRepair.fiberRow x) activation
        (FollowerObservationStageMeasurabilityRepair.fiberTime x).1
        (FollowerObservationStageMeasurabilityRepair.fiberPlayedArm x,
          FollowerDownMeasurability.feedbackAtGrid p
            (FollowerObservationStageMeasurabilityRepair.fiberFeedbackIndex x)) localState := by
    simp only [loggedCarriedState]
    rw [reconstruct_appendCarriedState, hupdateAppend htests]
    have hcode : FollowerDownMeasurability.followerStateCode rate actual = index.1 := by
      simpa [actual, FollowerObservationStageMeasurabilityRepair.reconstructCarriedState] using
        followerStateCode_ofCode index.1
          (FollowerDownJointMeasurability.bufferFromSkeletonAndScalars index.2.2 x.1)
    rw [← hcode, FollowerDownMeasurability.followerStateOfCode_code, hstate]
    simp [actual, FollowerObservationStageMeasurabilityRepair.reconstructCarriedState,
      FollowerDownMeasurability.followerStateOfCode,
      FollowerDownJointMeasurability.bufferFromSkeletonAndScalars,
      FollowerObservationStageMeasurabilityRepair.carriedStateBuffer,
      currentSavedScalar,
      SparseCalendarReplay.recordAt, ReferencePrelaunchFollower.loggingRound, hrecord]
  have hloggedKeep :
      FollowerObservationStageMeasurabilityRepair.reconstructCarriedState
        (⟨index, x.1⟩ : CarriedState p rate).1
        (⟨index, x.1⟩ : CarriedState p rate).2 = actual := rfl
  by_cases hin : localBufferValid'
  · have hinLocal : ActiveFollowerLifecycle.localBufferValid localState := hin
    have hinInput : ActiveFollowerLifecycle.localBufferValid
        (FollowerDownMeasurability.adaptedInputState rate state
          (FollowerLoggingDownMeasurability.inputSavedScalars input)) := by
      simpa [localState] using hinLocal
    have hinActual : ActiveFollowerLifecycle.localBufferValid actual := by
      rw [← hstate]
      exact hinLocal
    by_cases htests : SparseCalendarReplay.loggingTestsPass
        (ReferencePrelaunchFollower.loggingRound i
          (FollowerObservationStageMeasurabilityRepair.fiberRow x) activation
          (FollowerObservationStageMeasurabilityRepair.fiberTime x).1
          (FollowerObservationStageMeasurabilityRepair.fiberPlayedArm x,
            FollowerDownMeasurability.feedbackAtGrid p
              (FollowerObservationStageMeasurabilityRepair.fiberFeedbackIndex x)))
    · by_cases hfresh : currentFresh
      · have hout : ActiveFollowerLifecycle.localBufferValid
          {localState with buffer := localState.buffer ++ [currentRecord]} :=
          (localBufferValid_loggingAppend_iff i state input).2 ⟨hinLocal, hfresh⟩
        have hsuccess : ActiveFollowerLogging.checkedLogging i
            (FollowerObservationStageMeasurabilityRepair.fiberRow x) activation
            (FollowerObservationStageMeasurabilityRepair.fiberTime x).1
            (FollowerObservationStageMeasurabilityRepair.fiberPlayedArm x,
              FollowerDownMeasurability.feedbackAtGrid p
                (FollowerObservationStageMeasurabilityRepair.fiberFeedbackIndex x)) actual =
            .ok (ActiveFollowerLogging.loggingUpdate i
              (FollowerObservationStageMeasurabilityRepair.fiberRow x) activation
              (FollowerObservationStageMeasurabilityRepair.fiberTime x).1
              (FollowerObservationStageMeasurabilityRepair.fiberPlayedArm x,
                FollowerDownMeasurability.feedbackAtGrid p
                  (FollowerObservationStageMeasurabilityRepair.fiberFeedbackIndex x)) localState) := by
          apply (ActiveFollowerLogging.checkedLogging_success_iff i
            (FollowerObservationStageMeasurabilityRepair.fiberRow x) activation
            (FollowerObservationStageMeasurabilityRepair.fiberTime x).1
            (FollowerObservationStageMeasurabilityRepair.fiberPlayedArm x,
              FollowerDownMeasurability.feedbackAtGrid p
                (FollowerObservationStageMeasurabilityRepair.fiberFeedbackIndex x)) actual _).2
          refine ⟨hinActual, ?_, ?_⟩
          · rw [← hstate]
          · simpa only [hupdateAppend htests] using hout
        have hcode : checkedLoggingCodeOnFiber rate i activation index x = .appended := by
          simp [checkedLoggingCodeOnFiber, state, input, hstatus', hinInput,
            hgate, htests, currentFresh, hfresh]
        rw [hcode]
        simpa [reconstructCheckedLoggingCode] using
          (congrArg (Except.ok) (hloggedAppend htests)).trans hsuccess.symm
      · have hout : ¬ ActiveFollowerLifecycle.localBufferValid
          {localState with buffer := localState.buffer ++ [currentRecord]} := by
          intro hv
          exact hfresh ((localBufferValid_loggingAppend_iff i state input).mp hv).2
        have hbad : ¬ ActiveFollowerLifecycle.localBufferValid
            (ActiveFollowerLogging.loggingUpdate i
              (FollowerObservationStageMeasurabilityRepair.fiberRow x) activation
              (FollowerObservationStageMeasurabilityRepair.fiberTime x).1
              (FollowerObservationStageMeasurabilityRepair.fiberPlayedArm x,
                FollowerDownMeasurability.feedbackAtGrid p
                  (FollowerObservationStageMeasurabilityRepair.fiberFeedbackIndex x)) actual) := by
          intro hv
          have hvLocal : ActiveFollowerLifecycle.localBufferValid
              (ActiveFollowerLogging.loggingUpdate i
                (FollowerObservationStageMeasurabilityRepair.fiberRow x) activation
                (FollowerObservationStageMeasurabilityRepair.fiberTime x).1
                (FollowerObservationStageMeasurabilityRepair.fiberPlayedArm x,
                  FollowerDownMeasurability.feedbackAtGrid p
                    (FollowerObservationStageMeasurabilityRepair.fiberFeedbackIndex x)) localState) := by
            simpa only [hstate] using hv
          rw [hupdateAppend htests] at hvLocal
          exact hout hvLocal
        have hfailure := ActiveFollowerLogging.checkedLogging_invalid_output i
          (FollowerObservationStageMeasurabilityRepair.fiberRow x) activation
          (FollowerObservationStageMeasurabilityRepair.fiberTime x).1
          (FollowerObservationStageMeasurabilityRepair.fiberPlayedArm x,
            FollowerDownMeasurability.feedbackAtGrid p
              (FollowerObservationStageMeasurabilityRepair.fiberFeedbackIndex x)) actual
          hinActual hbad
        have hcode : checkedLoggingCodeOnFiber rate i activation index x = .failure 1 := by
          simp [checkedLoggingCodeOnFiber, state, input, hstatus', hinInput,
            hgate, htests, currentFresh, hfresh]
        rw [hcode]
        simpa [reconstructCheckedLoggingCode,
          FollowerLoggingDownMeasurability.loggingFailureOfCode] using hfailure.symm
    · have hsuccess : ActiveFollowerLogging.checkedLogging i
          (FollowerObservationStageMeasurabilityRepair.fiberRow x) activation
          (FollowerObservationStageMeasurabilityRepair.fiberTime x).1
          (FollowerObservationStageMeasurabilityRepair.fiberPlayedArm x,
            FollowerDownMeasurability.feedbackAtGrid p
              (FollowerObservationStageMeasurabilityRepair.fiberFeedbackIndex x)) actual =
          .ok actual := by
        apply (ActiveFollowerLogging.checkedLogging_success_iff i
          (FollowerObservationStageMeasurabilityRepair.fiberRow x) activation
          (FollowerObservationStageMeasurabilityRepair.fiberTime x).1
          (FollowerObservationStageMeasurabilityRepair.fiberPlayedArm x,
            FollowerDownMeasurability.feedbackAtGrid p
              (FollowerObservationStageMeasurabilityRepair.fiberFeedbackIndex x)) actual actual).2
        refine ⟨hinActual, ?_, hinActual⟩
        calc
          actual = localState := hstate.symm
          _ = ActiveFollowerLogging.loggingUpdate i
              (FollowerObservationStageMeasurabilityRepair.fiberRow x) activation
              (FollowerObservationStageMeasurabilityRepair.fiberTime x).1
              (FollowerObservationStageMeasurabilityRepair.fiberPlayedArm x,
                FollowerDownMeasurability.feedbackAtGrid p
                  (FollowerObservationStageMeasurabilityRepair.fiberFeedbackIndex x)) localState :=
            (hupdateKeep htests).symm
          _ = ActiveFollowerLogging.loggingUpdate i
              (FollowerObservationStageMeasurabilityRepair.fiberRow x) activation
              (FollowerObservationStageMeasurabilityRepair.fiberTime x).1
              (FollowerObservationStageMeasurabilityRepair.fiberPlayedArm x,
                FollowerDownMeasurability.feedbackAtGrid p
                  (FollowerObservationStageMeasurabilityRepair.fiberFeedbackIndex x)) actual := by
            rw [hstate]
      have hcode : checkedLoggingCodeOnFiber rate i activation index x = .retained := by
        simp [checkedLoggingCodeOnFiber, state, input, hstatus', hinInput,
          hgate, htests]
      rw [hcode]
      simpa [reconstructCheckedLoggingCode] using hsuccess.symm
  · have hinLocal : ¬ ActiveFollowerLifecycle.localBufferValid localState := hin
    have hinInput : ¬ ActiveFollowerLifecycle.localBufferValid
        (FollowerDownMeasurability.adaptedInputState rate state
          (FollowerLoggingDownMeasurability.inputSavedScalars input)) := by
      simpa [localState] using hinLocal
    have hbad : ¬ ActiveFollowerLifecycle.localBufferValid actual := by
      intro hv
      apply hinLocal
      simpa only [← hstate] using hv
    have hfailure := ActiveFollowerLogging.checkedLogging_invalid_input i
      (FollowerObservationStageMeasurabilityRepair.fiberRow x) activation
      (FollowerObservationStageMeasurabilityRepair.fiberTime x).1
      (FollowerObservationStageMeasurabilityRepair.fiberPlayedArm x,
        FollowerDownMeasurability.feedbackAtGrid p
          (FollowerObservationStageMeasurabilityRepair.fiberFeedbackIndex x)) actual hbad
    have hcode : checkedLoggingCodeOnFiber rate i activation index x = .failure 0 := by
      simp [checkedLoggingCodeOnFiber, state, input, hstatus', hinInput]
    rw [hcode]
    simpa [reconstructCheckedLoggingCode,
      FollowerLoggingDownMeasurability.loggingFailureOfCode] using hfailure.symm

/-- Exactly the unoccupied branch of the existing observation input. Activation
is already part of its active-calendar-time subtype. No domain check is assumed. -/
def unoccupiedLoggingInputs {p : Parameters} (rate : RateInput p)
    (activation : Activation p) : Set (ObservationInput p rate activation) :=
  {x | (reconstructCarriedState x.1 (fiberValues x.2)).status = .unoccupied}

/-- The branch is determined by the existing countable status register alone. -/
theorem mem_unoccupiedLoggingInputs_iff {p : Parameters} (rate : RateInput p)
    (activation : Activation p) (x : ObservationInput p rate activation) :
    x ∈ unoccupiedLoggingInputs rate activation ↔
      followerStatusOfCode x.1.1.status = .unoccupied := Iff.rfl

/-- On the existing active-time carrier this subtype is precisely the actual
logging branch, with no assumption about successful domain checks. -/
theorem mem_unoccupiedLoggingInputs_iff_loggingBranch {p : Parameters}
    (rate : RateInput p) (activation : Activation p)
    (x : ObservationInput p rate activation) :
    x ∈ unoccupiedLoggingInputs rate activation ↔
      ActiveFollowerLogging.loggingBranch activation (observationInputTime x).val
        (reconstructCarriedState x.1 (fiberValues x.2)) :=
  ⟨fun h => ⟨(observationInputTime x).property, h⟩, fun h => h.2⟩

theorem measurableSet_unoccupiedLoggingInputs {p : Parameters} (rate : RateInput p)
    (activation : Activation p) : MeasurableSet (unoccupiedLoggingInputs rate activation) := by
  have hstatus : Measurable (fun x : ObservationInput p rate activation =>
      (reconstructCarriedState x.1 (fiberValues x.2)).status) := by
    apply measurable_of_sigma_sections
    intro index
    change Measurable (fun _ : ObservationFiber p rate activation index =>
      followerStatusOfCode index.1.status)
    exact measurable_const
  exact (measurableSet_singleton ActiveRoundActions.FollowerStatus.unoccupied).preimage hstatus

/-- Literal measurable subtype of the accepted carrier on the local source branch. -/
abbrev LoggingInput (p : Parameters) (rate : RateInput p) (activation : Activation p) :=
  ↥(unoccupiedLoggingInputs rate activation)

/-- Inclusion into the original input; no field or continuous coordinate changes. -/
def loggingInputInclusion {p : Parameters} {rate : RateInput p}
    {activation : Activation p} (x : LoggingInput p rate activation) :
    ObservationInput p rate activation := x.val

theorem measurable_loggingInputInclusion {p : Parameters} (rate : RateInput p)
    (activation : Activation p) :
    Measurable (loggingInputInclusion : LoggingInput p rate activation →
      ObservationInput p rate activation) := measurable_subtype_coe

theorem measurable_loggingInputCarriedState {p : Parameters} (rate : RateInput p)
    (activation : Activation p) : Measurable (fun x : LoggingInput p rate activation =>
      observationInputCarriedState x.val) :=
  (measurable_observationInputCarriedState rate activation).comp measurable_subtype_coe

theorem measurable_loggingInputRow {p : Parameters} (rate : RateInput p)
    (activation : Activation p) : Measurable (fun x : LoggingInput p rate activation =>
      observationInputRow x.val) :=
  (measurable_observationInputRow rate activation).comp measurable_subtype_coe

theorem measurable_loggingInputTime {p : Parameters} (rate : RateInput p)
    (activation : Activation p) : Measurable (fun x : LoggingInput p rate activation =>
      observationInputTime x.val) :=
  (measurable_observationInputTime rate activation).comp measurable_subtype_coe

theorem measurable_loggingInputFeedbackIndex {p : Parameters} (rate : RateInput p)
    (activation : Activation p) : Measurable (fun x : LoggingInput p rate activation =>
      observationInputFeedbackIndex x.val) :=
  (measurable_observationInputFeedbackIndex rate activation).comp measurable_subtype_coe

theorem measurable_loggingInputPlayedArm {p : Parameters} (rate : RateInput p)
    (activation : Activation p) : Measurable (fun x : LoggingInput p rate activation =>
      observationInputPlayedArm x.val) :=
  (measurable_observationInputPlayedArm rate activation).comp measurable_subtype_coe

instance loggingFailureMeasurableSpace : MeasurableSpace ActiveFollowerLogging.LoggingFailure := ⊤

/-- Actual failure diagnostic or the full existing continuous carried output. -/
abbrev LoggingObservable (p : Parameters) (rate : RateInput p) :=
  ActiveFollowerLogging.LoggingFailure ⊕ CarriedState p rate

private def loggingObservableOfCode {p : Parameters} {rate : RateInput p}
    {activation : Activation p} (x : ObservationInput p rate activation)
    (code : CheckedLoggingCode) : LoggingObservable p rate :=
  match code with
  | .failure reason => .inl (loggingFailureOfCode reason)
  | .retained => .inr (observationInputCarriedState x)
  | .appended => .inr (loggedCarriedStateOnObservationFiber x.1 .appendedCurrent x.2)

private theorem measurable_loggingObservableOfCode {p : Parameters} (rate : RateInput p)
    (activation : Activation p) : Measurable
      (fun x : ObservationInput p rate activation × CheckedLoggingCode =>
        loggingObservableOfCode x.1 x.2) := by
  apply measurable_from_prod_countable_left
  intro code
  apply measurable_of_sigma_sections
  intro index
  cases code with
  | failure reason => exact measurable_const
  | retained => exact measurable_inr.comp ((measurable_sigmaMk index).comp measurable_fst)
  | appended =>
      exact measurable_inr.comp
        (measurable_loggedCarriedStateOnFiber rate activation index .appendedCurrent)

/-- Lossless checked logging on the actual active unoccupied source branch.
Failure tests precede storage, retained buffers keep all original scalars, and
append uses the current row's original thin scalar, including for zero feedback. -/
def checkedLoggingObservable {p : Parameters} (rate : RateInput p)
    (i : Fin (p.m - 1)) (activation : Activation p)
    (x : LoggingInput p rate activation) : LoggingObservable p rate := by
  classical
  let carry := observationInputCarriedState x.val
  let input := loggingInputOfFiber x.val.2
  if ActiveFollowerLifecycle.localBufferValid
      (reconstructCarriedState x.val.1 (fiberValues x.val.2)) then
    if loggingGateBit i input then
      if currentKeyFresh input then
        exact .inr
          ⟨(carry.1.1, ⟨carry.1.2.1 + 1,
              Fin.lastCases ((observationInputTime x.val).val.val + 1,
                observationInputPlayedArm x.val) carry.1.2.2⟩),
            Fin.lastCases
              ((feedbackAtGrid p (observationInputFeedbackIndex x.val)).val,
                ((observationInputRow x.val).2 (observationInputTime x.val).val).1
                  ContinuousControlSlice.Label.thin) carry.2⟩
      else exact .inl .invalidOutputBuffer
    else exact .inr carry
  else exact .inl .invalidInputBuffer

private theorem checkedLoggingObservable_eq_code {p : Parameters} (rate : RateInput p)
    (i : Fin (p.m - 1)) (activation : Activation p)
    (x : LoggingInput p rate activation) :
    checkedLoggingObservable rate i activation x =
      loggingObservableOfCode x.val (checkedLoggingCode rate i activation x.val) := by
  classical
  have hstatus : (representativeState rate x.val.1).status = .unoccupied := x.property
  have hstate : adaptedInputState rate (representativeState rate x.val.1)
      (inputSavedScalars (loggingInputOfFiber x.val.2)) =
        reconstructCarriedState x.val.1 (fiberValues x.val.2) :=
    adaptedRepresentativeState_eq_reconstruct x.val.1 (fiberValues x.val.2)
  simp only [checkedLoggingObservable, checkedLoggingCode, checkedLoggingCodeOnFiber,
    hstatus, hstate]
  split_ifs <;>
    rfl

theorem measurable_checkedLoggingObservable {p : Parameters} (rate : RateInput p)
    (i : Fin (p.m - 1)) (activation : Activation p) :
    Measurable (checkedLoggingObservable rate i activation) := by
  have hmeas : Measurable (fun x : LoggingInput p rate activation =>
      loggingObservableOfCode x.val (checkedLoggingCode rate i activation x.val)) :=
    ((measurable_loggingObservableOfCode rate activation).comp
    (measurable_id.prodMk (measurable_checkedLoggingCode rate i activation))).comp
      (measurable_subtype_coe (p := fun x => x ∈ unoccupiedLoggingInputs rate activation))
  convert hmeas using 1
  funext x
  exact checkedLoggingObservable_eq_code rate i activation x

/-- Literal decoder: retain the diagnostic or reconstruct the returned existing
carry from its original scalar family. It does not reevaluate the operation. -/
def reconstructLoggingObservable {p : Parameters} {rate : RateInput p}
    (out : LoggingObservable p rate) :
    Except ActiveFollowerLogging.LoggingFailure (State p rate.eta) :=
  match out with
  | .inl reason => .error reason
  | .inr carry => .ok (reconstructCarriedState carry.1 carry.2)

/-- Full same-input Except equality, including both input and output failures. -/
theorem checkedLoggingObservable_reconstruct {p : Parameters} (rate : RateInput p)
    (i : Fin (p.m - 1)) (activation : Activation p)
    (x : LoggingInput p rate activation) :
    reconstructLoggingObservable (checkedLoggingObservable rate i activation x) =
      ActiveFollowerLogging.checkedLogging i (observationInputRow x.val) activation
        (observationInputTime x.val).val
        (observationInputPlayedArm x.val,
          feedbackAtGrid p (observationInputFeedbackIndex x.val))
        (reconstructCarriedState x.val.1 (fiberValues x.val.2)) := by
  have hdecode : reconstructLoggingObservable (checkedLoggingObservable rate i activation x) =
      reconstructCheckedLoggingCode x.val.1 x.val.2
        (checkedLoggingCodeOnFiber rate i activation x.val.1 x.val.2) := by
    rw [checkedLoggingObservable_eq_code]
    unfold checkedLoggingCode
    cases checkedLoggingCodeOnFiber rate i activation x.val.1 x.val.2 <;>
      rfl
  exact hdecode.trans (checkedLoggingCodeOnFiber_reconstruct rate i activation
    x.val.1 x.val.2 x.property)

/-- Every diagnostic is equivalent pointwise to the actual checked-operation error. -/
theorem checkedLoggingObservable_error_iff {p : Parameters} (rate : RateInput p)
    (i : Fin (p.m - 1)) (activation : Activation p)
    (x : LoggingInput p rate activation) (reason : ActiveFollowerLogging.LoggingFailure) :
    checkedLoggingObservable rate i activation x = .inl reason ↔
      ActiveFollowerLogging.checkedLogging i (observationInputRow x.val) activation
        (observationInputTime x.val).val
        (observationInputPlayedArm x.val,
          feedbackAtGrid p (observationInputFeedbackIndex x.val))
        (reconstructCarriedState x.val.1 (fiberValues x.val.2)) = .error reason := by
  rw [← checkedLoggingObservable_reconstruct rate i activation x]
  cases checkedLoggingObservable rate i activation x <;> simp [reconstructLoggingObservable]

/-- A success of the actual operation is exactly a returned full carry whose
literal reconstruction is that successful state. -/
theorem checkedLoggingObservable_success_iff {p : Parameters} (rate : RateInput p)
    (i : Fin (p.m - 1)) (activation : Activation p)
    (x : LoggingInput p rate activation) (out : State p rate.eta) :
    ActiveFollowerLogging.checkedLogging i (observationInputRow x.val) activation
        (observationInputTime x.val).val
        (observationInputPlayedArm x.val,
          feedbackAtGrid p (observationInputFeedbackIndex x.val))
        (reconstructCarriedState x.val.1 (fiberValues x.val.2)) = .ok out ↔
      ∃ carry : CarriedState p rate,
        checkedLoggingObservable rate i activation x = .inr carry ∧
          reconstructCarriedState carry.1 carry.2 = out := by
  rw [← checkedLoggingObservable_reconstruct rate i activation x]
  cases checkedLoggingObservable rate i activation x <;> simp [reconstructLoggingObservable]

/-- Accepted outputs preserve the entire original discrete register/decoder code. -/
theorem checkedLoggingObservable_success_registers {p : Parameters} (rate : RateInput p)
    (i : Fin (p.m - 1)) (activation : Activation p)
    (x : LoggingInput p rate activation) (carry : CarriedState p rate)
    (h : checkedLoggingObservable rate i activation x = .inr carry) :
    carry.1.1 = x.val.1.1 := by
  rw [checkedLoggingObservable_eq_code] at h
  unfold loggingObservableOfCode at h
  cases hcode : checkedLoggingCode rate i activation x.val <;> rw [hcode] at h
  · cases h
  · cases h
    rfl
  · cases h
    rfl

/-- When the source/slot/mask tests reject recording, a successful output
is the exact original carry, including its ordered original scalar family. -/
theorem checkedLoggingObservable_retained {p : Parameters} (rate : RateInput p)
    (i : Fin (p.m - 1)) (activation : Activation p)
    (x : LoggingInput p rate activation) (carry : CarriedState p rate)
    (h : checkedLoggingObservable rate i activation x = .inr carry)
    (htests : ¬ loggingTestsPass (loggingRound i (observationInputRow x.val) activation
      (observationInputTime x.val).val (observationInputPlayedArm x.val,
        feedbackAtGrid p (observationInputFeedbackIndex x.val)))) :
    carry = observationInputCarriedState x.val := by
  have hgate : loggingGateBit i (loggingInputOfFiber x.val.2) ≠ true := by
    intro hg
    exact htests ((loggingGateBit_true_iff_testsPass i rate activation
      (representativeState rate x.val.1) (loggingInputOfFiber x.val.2)).mp hg)
  by_cases hin : ActiveFollowerLifecycle.localBufferValid
      (reconstructCarriedState x.val.1 (fiberValues x.val.2))
  · have hcarry : observationInputCarriedState x.val = carry := by
      simpa [checkedLoggingObservable, hin, hgate] using h
    exact hcarry.symm
  · simp [checkedLoggingObservable, hin] at h

/-- The exact output buffer: either the entire original buffer is retained or
one literal current record is appended at the end, with the original thin scalar. -/
theorem checkedLoggingObservable_success_buffer {p : Parameters} (rate : RateInput p)
    (i : Fin (p.m - 1)) (activation : Activation p)
    (x : LoggingInput p rate activation) (carry : CarriedState p rate)
    (h : checkedLoggingObservable rate i activation x = .inr carry) :
    carriedStateBuffer carry =
      if loggingTestsPass (loggingRound i (observationInputRow x.val) activation
          (observationInputTime x.val).val
          (observationInputPlayedArm x.val,
            feedbackAtGrid p (observationInputFeedbackIndex x.val))) then
        carriedStateBuffer (observationInputCarriedState x.val) ++
          [⟨(observationInputTime x.val).val.val + 1,
            observationInputPlayedArm x.val,
            (feedbackAtGrid p (observationInputFeedbackIndex x.val)).val,
            ((observationInputRow x.val).2 (observationInputTime x.val).val).1
              ContinuousControlSlice.Label.thin⟩]
      else carriedStateBuffer (observationInputCarriedState x.val) := by
  classical
  have hactual := (checkedLoggingObservable_success_iff rate i activation x
    (reconstructCarriedState carry.1 carry.2)).mpr ⟨carry, h, rfl⟩
  have hbuf := ActiveFollowerLogging.checkedLogging_success_buffer i
    (observationInputRow x.val) activation (observationInputTime x.val).val
    (observationInputPlayedArm x.val,
      feedbackAtGrid p (observationInputFeedbackIndex x.val))
    (reconstructCarriedState x.val.1 (fiberValues x.val.2))
    (reconstructCarriedState carry.1 carry.2) hactual
  have hbranch : ActiveFollowerLogging.loggingBranch activation
      (observationInputTime x.val).val
      (reconstructCarriedState x.val.1 (fiberValues x.val.2)) :=
    ⟨(observationInputTime x.val).property, x.property⟩
  rw [ite_eq_left hbranch] at hbuf
  by_cases htests : loggingTestsPass (loggingRound i (observationInputRow x.val) activation
      (observationInputTime x.val).val (observationInputPlayedArm x.val,
        feedbackAtGrid p (observationInputFeedbackIndex x.val)))
  · rw [ite_eq_left htests]
    rw [ActiveFollowerLogging.logAt_eq_singleton_of_tests i _ _ _ _ htests] at hbuf
    exact hbuf
  · rw [ite_eq_right htests]
    rw [ActiveFollowerLogging.logAt_eq_nil_of_not_tests i _ _ _ _ htests] at hbuf
    change carriedStateBuffer carry =
      carriedStateBuffer (observationInputCarriedState x.val) ++ [] at hbuf
    simpa only [List.append_nil] using hbuf

end Bandits.Support.ReferenceFollowerLoggingMeasurability

end
