/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCalendarLaterSamplerPredictability
public import Bandits.Support.ReferenceFirstCollectionSamplerCall

/-!
# Prefix and current-control laws for the actual collection call

The observations below are projections of the existing complete physical
suffix and its first-call observer. They preserve absent calls and use the
original source measure and complete control/vector coordinates.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open scoped Classical

namespace Bandits.Support.ReferenceCalendarCollectionCallControlLaw

variable {p : ConstructorDimensions.Parameters}
  (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ)

abbrev SourceInput (p : ConstructorDimensions.Parameters) :=
  BootstrapPrivateRoundStreams.SourceInput p
abbrev Theta (p : ConstructorDimensions.Parameters) :=
  AssignmentParameterFibreKernel.Theta p
abbrev Call (p : ConstructorDimensions.Parameters) :=
  Fin p.T × (Fin p.T × Theta p)
abbrev CallAt (p : ConstructorDimensions.Parameters) :=
  Option (Fin p.T × Theta p)
abbrev TimeControl (p : ConstructorDimensions.Parameters) :=
  ContinuousLearningRows.TimeControl p
abbrev AssignmentVector (p : ConstructorDimensions.Parameters) :=
  Fin (p.K + 1) → ContinuousControlSlice.Scalar

local instance optionFinMeasurableSpace : MeasurableSpace (Option (Fin p.T)) :=
  LaterAssignmentStartMeasurability.optionMeasurableSpace

/-- The existing pre-choice call on the actual round record at calendar `t`.
-/
def callAt (t : Fin p.T) (z : SourceInput p) : CallAt p :=
  (ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z).bind
    ReferenceFirstCollectionSamplerCall.collectionCallAt

/-- Date projection of the already defined first actual invocation.
-/
def firstAt (t : Fin p.T) (z : SourceInput p) : CallAt p :=
  (ReferenceFirstCollectionSamplerCall.firstCollectionCall rate rewards C_star C_h z).bind
    (fun c => if c.2.1 = t then some (c.1, c.2.2) else none)

/-- The original first-invocation cell, retaining its cutoff and date tags.
-/
def firstCell (u t : Fin p.T) : Set (SourceInput p) :=
  {z | (ReferenceFirstCollectionSamplerCall.firstCollectionCall rate rewards C_star C_h z).map
    (fun c => (c.1, c.2.1)) = some (u, t)}

private theorem actualRecord_input_time (t : Fin p.T) (z : SourceInput p)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r) :
    r.input.time = t := by
  unfold ReferenceSourcePrefixHistoryFiltration.actualRecord at hr
  split_ifs at hr with hs
  · obtain ⟨hk, hrecord⟩ := List.getElem?_eq_some_iff.mp hr
    have hf := ReferenceCompleteSuffixInputMeasurability.actualRoundInputAt_fields
      rate rewards C_star C_h _ ⟨z, hk⟩
    dsimp only [ReferenceCompleteSuffixInputMeasurability.actualRoundInputAt,
      ReferenceCompleteSuffixInputMeasurability.actualRecordCodeAt,
      List.get_eq_getElem] at hf
    rw [hrecord] at hf
    have ht := ReferenceCompletePhysicalHistory.completeSuffixRecords_time_values
      rate z rewards C_star C_h
    have hk' : t.val - ReferenceCompletePhysicalHistory.physicalStart
        rate z rewards C_star C_h < p.T - ReferenceCompletePhysicalHistory.physicalStart
          rate z rewards C_star C_h := by
      simpa only [ReferenceCompletePhysicalHistory.completeSuffixRecords_length] using hk
    have hget := congrArg (fun l : List ℕ => l[t.val -
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h]?) ht
    simp only [ReferenceActivePhysicalHorizon.calendar, List.getElem?_map,
      List.getElem?_range' hk', Nat.one_mul] at hget
    rw [List.getElem?_eq_getElem hk, hrecord] at hget
    apply Fin.ext
    have hv := Option.some.inj hget
    simpa only [Nat.add_sub_of_le hs] using hv

/-- The call depends only on the pre-choice state and its actual calendar date.
-/
theorem callAt_factor (control0 : TimeControl p) (t : Fin p.T) (z : SourceInput p) :
    callAt rate rewards C_star C_h t z =
      callAt rate rewards C_star C_h t
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z) := by
  let z' := ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z
  have hinc := ReferenceSourcePrefixHistoryFiltration.incoming_factor
    rate rewards C_star C_h control0 t z
  change Option.map (fun r => ReferenceActivePhysicalStepMeasurability.encodeState r.input.state)
      (ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z) =
    Option.map (fun r => ReferenceActivePhysicalStepMeasurability.encodeState r.input.state)
      (ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z') at hinc
  unfold callAt
  cases h₁ : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z with
  | none =>
      cases h₂ : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z' with
      | none => rfl
      | some r₂ =>
          rw [h₁, h₂] at hinc
          simp at hinc
  | some r₁ =>
      cases h₂ : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z' with
      | none =>
          rw [h₁, h₂] at hinc
          simp at hinc
      | some r₂ =>
          rw [h₁, h₂] at hinc
          have hcode : ReferenceActivePhysicalStepMeasurability.encodeState r₁.input.state =
              ReferenceActivePhysicalStepMeasurability.encodeState r₂.input.state := by
            exact Option.some.inj hinc
          have hs : r₁.input.state = r₂.input.state :=
            ReferenceActivePhysicalStepMeasurability.encodeState_injective hcode
          have ht₁ := actualRecord_input_time rate rewards C_star C_h t z r₁ h₁
          have ht₂ := actualRecord_input_time rate rewards C_star C_h t z' r₂ h₂
          have hc := ReferenceFirstCollectionSamplerCall.collectionCallOnInput_eq_of_state_eq_time_eq
            r₁.input r₂.input hs (ht₁.trans ht₂.symm)
          change ReferenceFirstCollectionSamplerCall.collectionCallAt r₁ =
            ReferenceFirstCollectionSamplerCall.collectionCallAt r₂
          exact hc

private theorem firstCall_least_date (u s : Fin p.T) (theta : Theta p)
    (z : SourceInput p)
    (hfirst : ReferenceFirstCollectionSamplerCall.firstCollectionCall
      rate rewards C_star C_h z = some (u, (s, theta))) :
    callAt rate rewards C_star C_h s z = some (u, theta) ∧
      ∀ v : Fin p.T, v.val < s.val → callAt rate rewards C_star C_h v z = none := by
  let records := ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate z rewards C_star C_h
  let start := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  rcases (ReferenceFirstCollectionSamplerCall.firstCollectionCall_spec
      (rate := rate) rewards C_star C_h z u s theta).mp hfirst with
    ⟨n, r, hr, htime, hcall, hprevious⟩
  have hn : n < records.length := (List.getElem?_eq_some_iff.mp hr).1
  have hn' : n < p.T - ReferenceCompletePhysicalHistory.physicalStart
      rate z rewards C_star C_h := by
    change n < (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length at hn
    simpa only [ReferenceCompletePhysicalHistory.completeSuffixRecords_length] using hn
  have htimes := ReferenceCompletePhysicalHistory.completeSuffixRecords_time_values
    rate z rewards C_star C_h
  have htimeIndex := congrArg (fun xs : List ℕ => xs[n]?) htimes
  simp only [ReferenceActivePhysicalHorizon.calendar, List.getElem?_map,
    List.getElem?_range' hn', Nat.one_mul] at htimeIndex
  rw [hr] at htimeIndex
  simp only [Option.map_some] at htimeIndex
  have hs_eq : s.val = start + n := by
    have h := Option.some.inj htimeIndex
    simpa only [htime] using h
  have hs_start : start ≤ s.val := by omega
  have hindex_s : s.val - start = n := by omega
  have hrecord_s :
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h s z = some r := by
    simp [ReferenceSourcePrefixHistoryFiltration.actualRecord, start, hs_start, hindex_s, hr]
  have hcall_s : callAt rate rewards C_star C_h s z = some (u, theta) := by
    simp [callAt, hrecord_s, hcall]
  refine ⟨hcall_s, ?_⟩
  intro v hvis
  by_cases hvstart : start ≤ v.val
  · cases hrecord_v : records[v.val - start]? with
    | none =>
        have hactual : ReferenceSourcePrefixHistoryFiltration.actualRecord
            rate rewards C_star C_h v z = none := by
          change (if ReferenceCompletePhysicalHistory.physicalStart
            rate z rewards C_star C_h ≤ v.val then
            (ReferenceCompletePhysicalHistory.completeSuffixRecords
              rate z rewards C_star C_h)[v.val -
                ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h]?
            else none) = none
          rw [ite_eq_left hvstart]
          simpa [records, start] using hrecord_v
        simp [callAt, hactual]
    | some rv =>
      have hjn : v.val - start < n := by omega
      have hnone := hprevious (v.val - start) hjn rv hrecord_v
      have hcallnone :
          ReferenceFirstCollectionSamplerCall.collectionCallAt rv = none :=
        (ReferenceFirstCollectionSamplerCall.collectionCallAt_none_iff rv).2 hnone
      have hactual : ReferenceSourcePrefixHistoryFiltration.actualRecord
          rate rewards C_star C_h v z = some rv := by
        change (if ReferenceCompletePhysicalHistory.physicalStart
          rate z rewards C_star C_h ≤ v.val then
          (ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate z rewards C_star C_h)[v.val -
              ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h]?
          else none) = some rv
        rw [ite_eq_left hvstart]
        simpa [records, start] using hrecord_v
      simp [callAt, hactual, hcallnone]
  · have hactual : ReferenceSourcePrefixHistoryFiltration.actualRecord
        rate rewards C_star C_h v z = none := by
      change (if ReferenceCompletePhysicalHistory.physicalStart
        rate z rewards C_star C_h ≤ v.val then
        (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)[v.val -
            ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h]?
        else none) = none
      rw [ite_eq_right hvstart]
    simp [callAt, hactual]

/-- The date projection of the actual first call is the first nonempty
per-date call in the finite physical calendar.
-/
theorem firstAt_eq (t : Fin p.T) (z : SourceInput p) :
    firstAt rate rewards C_star C_h t z =
      if (∀ v : Fin p.T, v.val < t.val → callAt rate rewards C_star C_h v z = none)
      then callAt rate rewards C_star C_h t z else none := by
  unfold firstAt
  cases hfirst : ReferenceFirstCollectionSamplerCall.firstCollectionCall
      rate rewards C_star C_h z with
  | none =>
      have hnone := (ReferenceFirstCollectionSamplerCall.firstCollectionCall_none_iff
        (rate := rate) rewards C_star C_h z).mp hfirst
      have hcallNone : ∀ v : Fin p.T, callAt rate rewards C_star C_h v z = none := by
        intro v
        unfold callAt
        by_cases hstart : ReferenceCompletePhysicalHistory.physicalStart
            rate z rewards C_star C_h ≤ v.val
        · cases hrecord : (ReferenceCompletePhysicalHistory.completeSuffixRecords
              rate z rewards C_star C_h)[v.val -
                ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h]? with
          | none =>
              simp [ReferenceSourcePrefixHistoryFiltration.actualRecord, hstart, hrecord]
          | some r =>
            have hmem : r ∈ ReferenceCompletePhysicalHistory.completeSuffixRecords
                rate z rewards C_star C_h := List.mem_of_getElem? hrecord
            have hparam := hnone r hmem
            have hcallnone :=
              (ReferenceFirstCollectionSamplerCall.collectionCallAt_none_iff r).2 hparam
            simp [ReferenceSourcePrefixHistoryFiltration.actualRecord, hstart,
              hrecord, hcallnone]
        · simp [ReferenceSourcePrefixHistoryFiltration.actualRecord, hstart]
      simp [hcallNone]
  | some c =>
      rcases c with ⟨u, s, theta⟩
      obtain ⟨hcallS, hpast⟩ :=
        firstCall_least_date rate rewards C_star C_h u s theta z hfirst
      simp only [Option.bind_some]
      by_cases hst : s = t
      · subst t
        rw [ite_eq_left hpast]
        simp [hcallS]
      · by_cases hts : t.val < s.val
        · have hcallT : callAt rate rewards C_star C_h t z = none := hpast t hts
          have hearlier : ∀ v : Fin p.T, v.val < t.val →
              callAt rate rewards C_star C_h v z = none := by
            intro v hv
            exact hpast v (by omega)
          rw [ite_eq_right hst, ite_eq_left hearlier]
          simp only [hcallT]
        · have hst' : s.val < t.val := by omega
          have hnot : ¬ (∀ v : Fin p.T, v.val < t.val →
              callAt rate rewards C_star C_h v z = none) := by
            intro hall
            have hsnone := hall s hst'
            rw [hcallS] at hsnone
            cases hsnone
          rw [ite_eq_right hst, ite_eq_right hnot]

/-- The first actual call is determined by its date and strict past prefix. -/
theorem firstAt_factor (control0 : TimeControl p) (t : Fin p.T)
    (z : SourceInput p) :
    firstAt rate rewards C_star C_h t z =
      firstAt rate rewards C_star C_h t
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z) := by
  rw [firstAt_eq rate rewards C_star C_h t z,
    firstAt_eq rate rewards C_star C_h t
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z)]
  have hcall (v : Fin p.T) (hv : v.val < t.val) :
      callAt rate rewards C_star C_h v z =
        callAt rate rewards C_star C_h v
          (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z) := by
    calc
      callAt rate rewards C_star C_h v z =
          callAt rate rewards C_star C_h v
            (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 v.val z) :=
              callAt_factor rate rewards C_star C_h control0 v z
      _ = callAt rate rewards C_star C_h v
            (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 v.val
              (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z)) :=
          congrArg (callAt rate rewards C_star C_h v)
            (ReferenceSourcePrefixHistoryFiltration.sourcePrefix_sourcePrefix control0
              v.val t.val (Nat.le_of_lt hv) z).symm
      _ = callAt rate rewards C_star C_h v
            (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z) :=
          (callAt_factor rate rewards C_star C_h control0 v
            (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z)).symm
  have hpast :
      (∀ v : Fin p.T, v.val < t.val → callAt rate rewards C_star C_h v z = none) ↔
        (∀ v : Fin p.T, v.val < t.val →
          callAt rate rewards C_star C_h v
            (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z) = none) := by
    constructor
    · intro h v hv
      rw [← hcall v hv]
      exact h v hv
    · intro h v hv
      rw [hcall v hv]
      exact h v hv
  by_cases h : ∀ v : Fin p.T, v.val < t.val →
      callAt rate rewards C_star C_h v z = none
  · have h' := hpast.mp h
    rw [ite_eq_left h, ite_eq_left h']
    exact callAt_factor rate rewards C_star C_h control0 t z
  · have h' : ¬ (∀ v : Fin p.T, v.val < t.val →
        callAt rate rewards C_star C_h v
          (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z) = none) := by
      intro h'
      exact h (hpast.mpr h')
    rw [ite_eq_right h, ite_eq_right h']

private theorem measurableSet_optionNone {A : Type*} [MeasurableSpace A] :
    MeasurableSet ({none} : Set (Option A)) := by
  change MeasurableSet[(inferInstance : MeasurableSpace (A ⊕ PUnit)).comap
    (Equiv.optionEquivSumPUnit A)] {none}
  rw [MeasurableSpace.measurableSet_comap]
  refine ⟨Set.range (Sum.inr : PUnit → A ⊕ PUnit), measurableSet_range_inr, ?_⟩
  ext value
  cases value <;> simp

private theorem measurableSet_optionSome {A : Type*} [MeasurableSpace A]
    (s : Set A) (hs : MeasurableSet s) :
    MeasurableSet (some '' s : Set (Option A)) := by
  change MeasurableSet[(inferInstance : MeasurableSpace (A ⊕ PUnit)).comap
    (Equiv.optionEquivSumPUnit A)] (some '' s)
  rw [MeasurableSpace.measurableSet_comap]
  refine ⟨Sum.inl '' s, measurableSet_inl_image.mpr hs, ?_⟩
  ext value
  cases value <;> simp

private def cutoffFromLedger? (ledger : ReferenceActivePhysicalStep.Ledger rate) :
    Option (Fin p.T) :=
  if hc : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T then
    some ⟨ledger.cutoff - 1, by omega⟩ else none

private def cutoffFromCoordinatorCode?
    (code : ReferenceActivePhysicalStepMeasurability.CoordinatorCode p rate) :
    Option (Fin p.T) :=
  match code with
  | .inr (.inr (.inl (_, ledger, _))) => cutoffFromLedger? rate ledger
  | _ => none

private theorem measurable_cutoffFromCoordinatorCode? :
    Measurable (cutoffFromCoordinatorCode? rate) := by
  apply measurable_fun_sum measurable_const
  apply measurable_fun_sum measurable_const
  exact measurable_fun_sum
    ((measurable_of_countable (cutoffFromLedger? rate)).comp
      (measurable_fst.comp measurable_snd)) measurable_const

private theorem measurable_optionBind {X Y Z : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (input : X → Option Y) (hinput : Measurable input)
    (f : Y → Option Z) (hf : Measurable f) :
    Measurable (fun x => (input x).bind f) := by
  classical
  intro s hs
  let someImage : Set (Option Y) := some '' (f ⁻¹' s)
  have hsome : MeasurableSet someImage := by
    change MeasurableSet[
      (inferInstance : MeasurableSpace (Y ⊕ PUnit)).comap
        (Equiv.optionEquivSumPUnit Y)] someImage
    rw [MeasurableSpace.measurableSet_comap]
    refine ⟨Sum.inl '' (f ⁻¹' s), measurableSet_inl_image.mpr (hf hs), ?_⟩
    ext value
    cases value <;> simp [someImage]
  have hnone : MeasurableSet ({none} : Set (Option Y)) := by
    change MeasurableSet[
      (inferInstance : MeasurableSpace (Y ⊕ PUnit)).comap
        (Equiv.optionEquivSumPUnit Y)] {none}
    rw [MeasurableSpace.measurableSet_comap]
    refine ⟨{Sum.inr PUnit.unit}, ?_, ?_⟩
    · convert measurableSet_inr_image.mpr (measurableSet_singleton PUnit.unit) using 1
      ext value
      simp
    ext value
    cases value <;> simp
  have hpre :
      (fun x => (input x).bind f) ⁻¹' s = input ⁻¹'
        (someImage ∪ if (none : Option Z) ∈ s then
          ({(none : Option Y)} : Set (Option Y)) else ∅) := by
    ext x
    cases h : input x <;> simp [h, someImage]
  have hrest : MeasurableSet (if (none : Option Z) ∈ s then
      ({(none : Option Y)} : Set (Option Y)) else ∅) := by
    by_cases h : (none : Option Z) ∈ s
    · simpa [h] using hnone
    · simp [h]
  have hmeas := hinput (hsome.union hrest)
  rw [← hpre] at hmeas
  exact hmeas

private def pairOptions {A B : Type*} (z : Option A × Option B) : Option (A × B) :=
  z.1.bind (fun a => z.2.map (fun b => (a, b)))

private theorem measurable_optionMapWith {X A B C : Type*}
    [MeasurableSpace X] [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    (a : X → A) (ha : Measurable a) (o : X → Option B) (ho : Measurable o)
    (f : A × B → C) (hf : Measurable f) :
    Measurable (fun x => (o x).map (fun b => f (a x, b))) := by
  let e := ReferenceCollectionDispatchMeasurability.optionPairEquiv B A
  have hleft : Measurable (fun z : B × A => (some (f (z.2, z.1)) : Option C)) :=
    LaterAssignmentFullOutputMeasurability.measurable_some_of_measurable _
      (hf.comp measurable_swap)
  have h := (hleft.sumElim (measurable_const :
    Measurable (fun _ : PUnit × A => (none : Option C)))).comp
      (e.measurable.comp (ho.prodMk ha))
  convert h using 1
  funext x
  dsimp only [Function.comp_apply]
  cases ho' : o x <;> rfl

private theorem measurable_pairOptions {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B] :
    Measurable (pairOptions (A := A) (B := B)) := by
  let e := ReferenceCollectionDispatchMeasurability.optionPairEquiv A (Option B)
  have hleft : Measurable (fun z : A × Option B => z.2.map (fun b => (z.1, b))) :=
    measurable_optionMapWith Prod.fst measurable_fst Prod.snd measurable_snd
      id measurable_id
  let f : (A × Option B) ⊕ (PUnit × Option B) → Option (A × B) :=
    Sum.elim (fun z => z.2.map (fun b => (z.1, b))) (fun _ => none)
  have hf : Measurable f := hleft.sumElim
      (measurable_const : Measurable (fun _ : PUnit × Option B => (none : Option (A × B))))
  have heq : pairOptions (A := A) (B := B) = fun z => f (e z) := by
    funext z
    rcases z with ⟨oa, ob⟩
    cases oa <;> rfl
  rw [heq]
  exact hf.comp e.measurable

private def callAtView (incoming : Option
    (ReferenceActivePhysicalStepMeasurability.StateCode p rate))
    (theta : Option (Theta p)) : CallAt p :=
  pairOptions (incoming.bind (fun code => cutoffFromCoordinatorCode? rate code.1), theta)

private theorem measurable_callAtView :
    Measurable (fun x : Option (ReferenceActivePhysicalStepMeasurability.StateCode p rate) ×
      Option (Theta p) => callAtView rate x.1 x.2) := by
  have hcut : Measurable (fun code : ReferenceActivePhysicalStepMeasurability.StateCode p rate =>
      cutoffFromCoordinatorCode? rate code.1) :=
    (measurable_cutoffFromCoordinatorCode? rate).comp measurable_fst
  have hopt : Measurable (fun incoming : Option
      (ReferenceActivePhysicalStepMeasurability.StateCode p rate) =>
        incoming.bind (fun code => cutoffFromCoordinatorCode? rate code.1)) :=
    measurable_optionBind id measurable_id
      (fun code : ReferenceActivePhysicalStepMeasurability.StateCode p rate =>
        cutoffFromCoordinatorCode? rate code.1) hcut
  exact measurable_pairOptions.comp ((hopt.comp measurable_fst).prodMk measurable_snd)

private theorem callAt_eq_view (t : Fin p.T) (z : SourceInput p) :
    callAt rate rewards C_star C_h t z = callAtView rate
      (ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t z)
      (ReferenceCalendarLaterSamplerPredictability.calendarParameters
        rate rewards C_star C_h t z) := by
  classical
  unfold callAt callAtView pairOptions
  cases hrecord : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z with
  | none => simp [ReferenceSourcePrefixHistoryFiltration.incoming,
      ReferenceCalendarLaterSamplerPredictability.calendarParameters, hrecord]
  | some r =>
      cases hcoord : r.input.state.coordinator with
      | first =>
          simp [ReferenceSourcePrefixHistoryFiltration.incoming,
          ReferenceCalendarLaterSamplerPredictability.calendarParameters, hrecord,
          ReferenceActivePhysicalStepMeasurability.encodeState,
          ReferenceActivePhysicalStepMeasurability.encodeCoordinator,
          ReferenceFirstCollectionSamplerCall.collectionCallAt,
          ReferenceFirstCollectionSamplerCall.collectionCallOnInput,
          ReferenceLaterSamplerParameterMeasurability.parameters?,
          ReferenceLaterAssignmentFibreStep.parameters?, hcoord]
      | live registers owned base =>
          simp [ReferenceSourcePrefixHistoryFiltration.incoming,
            ReferenceCalendarLaterSamplerPredictability.calendarParameters, hrecord,
            ReferenceActivePhysicalStepMeasurability.encodeState,
            ReferenceActivePhysicalStepMeasurability.encodeCoordinator,
            ReferenceFirstCollectionSamplerCall.collectionCallAt,
            ReferenceFirstCollectionSamplerCall.collectionCallOnInput,
            ReferenceLaterSamplerParameterMeasurability.parameters?,
            ReferenceLaterAssignmentFibreStep.parameters?, hcoord]
      | dagger =>
          simp [ReferenceSourcePrefixHistoryFiltration.incoming,
            ReferenceCalendarLaterSamplerPredictability.calendarParameters, hrecord,
            ReferenceActivePhysicalStepMeasurability.encodeState,
            ReferenceActivePhysicalStepMeasurability.encodeCoordinator,
            ReferenceFirstCollectionSamplerCall.collectionCallAt,
            ReferenceFirstCollectionSamplerCall.collectionCallOnInput,
            ReferenceLaterSamplerParameterMeasurability.parameters?,
            ReferenceLaterAssignmentFibreStep.parameters?, hcoord]
      | collection payload ledger proposal =>
          by_cases hc : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T <;>
            simp [ReferenceSourcePrefixHistoryFiltration.incoming,
              ReferenceCalendarLaterSamplerPredictability.calendarParameters, hrecord,
              ReferenceActivePhysicalStepMeasurability.encodeState,
              ReferenceActivePhysicalStepMeasurability.encodeCoordinator,
              ReferenceFirstCollectionSamplerCall.collectionCallAt,
              ReferenceFirstCollectionSamplerCall.collectionCallOnInput,
              ReferenceLaterSamplerParameterMeasurability.parameters?,
              ReferenceLaterAssignmentFibreStep.parameters?, cutoffFromLedger?,
              cutoffFromCoordinatorCode?, hcoord, hc]

/-- The actual pre-choice call is measurable in the exact successor field.
-/
theorem callAt_measurable (control0 : TimeControl p) (t : Fin p.T) :
    Measurable[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
      control0 (t.val + 1)] (callAt rate rewards C_star C_h t) := by
  have heq : callAt rate rewards C_star C_h t = fun z => callAtView rate
      (ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t z)
      (ReferenceCalendarLaterSamplerPredictability.calendarParameters
        rate rewards C_star C_h t z) := by
    funext z
    exact callAt_eq_view rate rewards C_star C_h t z
  rw [heq]
  exact (measurable_callAtView rate).comp
    ((ReferenceSourcePrefixHistoryFiltration.incoming_measurable
        rate rewards C_star C_h control0 t).prodMk
      (ReferenceCalendarLaterSamplerPredictability.calendarParameters_measurable
        rate rewards C_star C_h control0 t))

/-- The first-call date projection is measurable in the exact successor field. -/
theorem firstAt_measurable (control0 : TimeControl p) (t : Fin p.T) :
    Measurable[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
      control0 (t.val + 1)] (firstAt rate rewards C_star C_h t) := by
  classical
  let past : Set (SourceInput p) :=
    {z | ∀ v : Fin p.T, v.val < t.val → callAt rate rewards C_star C_h v z = none}
  have hPast : MeasurableSet[
      ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (t.val + 1)] past := by
    have hset : past = ⋂ v : Fin p.T,
        if v.val < t.val then
          {z : SourceInput p | callAt rate rewards C_star C_h v z = none}
        else Set.univ := by
      ext z
      simp [past]
    rw [hset]
    exact MeasurableSet.iInter fun v => by
      by_cases hv : v.val < t.val
      · rw [ite_eq_left hv]
        have hcall : Measurable[
            ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (t.val + 1)]
            (callAt rate rewards C_star C_h v) :=
          (callAt_measurable rate rewards C_star C_h control0 v).mono
            ((ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).mono'
              (Nat.succ_le_succ (Nat.le_of_lt hv))) le_rfl
        exact hcall measurableSet_optionNone
      · rw [ite_eq_right hv]
        exact MeasurableSet.univ
  have hcurrent : Measurable[
      ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (t.val + 1)]
      (callAt rate rewards C_star C_h t) :=
    callAt_measurable rate rewards C_star C_h control0 t
  have hfirst : firstAt rate rewards C_star C_h t =
      fun z => if z ∈ past then callAt rate rewards C_star C_h t z else none := by
    funext z
    rw [firstAt_eq]
    rfl
  rw [hfirst]
  intro s hs
  have hpre : (fun z => if z ∈ past then callAt rate rewards C_star C_h t z
      else (none : CallAt p)) ⁻¹' s =
      (past ∩ (callAt rate rewards C_star C_h t) ⁻¹' s) ∪
        (pastᶜ ∩ if (none : CallAt p) ∈ s then Set.univ else ∅) := by
    ext z
    by_cases hz : z ∈ past <;> simp [hz]
  rw [hpre]
  have hrest : MeasurableSet[
      ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (t.val + 1)]
      (pastᶜ ∩ if (none : CallAt p) ∈ s then Set.univ else ∅) := by
    by_cases hn : (none : CallAt p) ∈ s
    · simpa [hn] using hPast.compl
    · simp [hn]
  exact (hPast.inter (hcurrent hs)).union hrest

private theorem firstCell_iff_firstAt (u t : Fin p.T) (z : SourceInput p) :
    z ∈ firstCell rate rewards C_star C_h u t ↔
      (firstAt rate rewards C_star C_h t z).map Prod.fst = some u := by
  unfold firstCell firstAt
  cases hfirst : ReferenceFirstCollectionSamplerCall.firstCollectionCall
      rate rewards C_star C_h z with
  | none => simp [hfirst]
  | some c =>
      rcases c with ⟨cutoff, time, theta⟩
      rcases theta with ⟨theta₁, theta₂⟩
      by_cases htime : time = t
      · subst time
        simp [hfirst]
      · simp [hfirst, htime]

private theorem firstCell_factor_iff (control0 : TimeControl p) (u t : Fin p.T)
    (z : SourceInput p) :
    z ∈ firstCell rate rewards C_star C_h u t ↔
      ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z ∈
        firstCell rate rewards C_star C_h u t := by
  rw [firstCell_iff_firstAt rate rewards C_star C_h u t z,
    firstCell_iff_firstAt rate rewards C_star C_h u t
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z),
    firstAt_factor rate rewards C_star C_h control0 t z]

/-- Each original cutoff/date cell is measurable in its exact successor field. -/
theorem firstCell_measurable (control0 : TimeControl p) (u t : Fin p.T) :
    MeasurableSet[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
      control0 (t.val + 1)] (firstCell rate rewards C_star C_h u t) := by
  have hglobal : MeasurableSet (firstCell rate rewards C_star C_h u t) := by
    simpa only [firstCell] using
      ReferenceFirstCollectionSamplerCall.measurableSet_firstCollectionCall_cell
        rate rewards C_star C_h u t
  rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration_succ control0 t.val]
  rw [MeasurableSpace.measurableSet_comap]
  refine ⟨firstCell rate rewards C_star C_h u t, hglobal, ?_⟩
  ext z
  exact (firstCell_factor_iff rate rewards C_star C_h control0 u t z).symm

/-- Independence of this pre-choice call from the complete current control. -/
theorem callAt_currentControl_joint (control0 : TimeControl p) (t : Fin p.T) :
    (BootstrapPrivateRoundStreams.sourceInputLaw p).map
        (fun z => (callAt rate rewards C_star C_h t z,
          ReferenceSourceCurrentControlFreshness.u_t p t z)) =
      ((BootstrapPrivateRoundStreams.sourceInputLaw p).map
        (callAt rate rewards C_star C_h t)).prod
        (ContinuousLearningRows.timeControlLaw p) := by
  let μ := BootstrapPrivateRoundStreams.sourceInputLaw p
  let c := ReferenceSourceCurrentControlFreshness.c_t p control0 t
  let u := ReferenceSourceCurrentControlFreshness.u_t p t
  let observe := fun x : SourceInput p × TimeControl p =>
    (callAt rate rewards C_star C_h t x.1, x.2)
  have hc : Measurable c :=
    ReferenceSourceCurrentControlFreshness.measurable_c_t control0 t
  have hu : Measurable u := ReferenceSourceCurrentControlFreshness.measurable_u_t t
  have hcallBorel : Measurable (callAt rate rewards C_star C_h t) :=
    (callAt_measurable rate rewards C_star C_h control0 t).mono
      ((ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le'
        (t.val + 1)) le_rfl
  have hprefixPair : Measurable (fun z : SourceInput p => (c z, u z)) := hc.prodMk hu
  have hobserve : Measurable observe := (hcallBorel.comp measurable_fst).prodMk measurable_snd
  have hpair :
      (fun z : SourceInput p => (callAt rate rewards C_star C_h t z, u z)) =
        (fun z => observe (c z, u z)) := by
    funext z
    apply Prod.ext
    · calc
        callAt rate rewards C_star C_h t z =
            callAt rate rewards C_star C_h t
              (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z) :=
                callAt_factor rate rewards C_star C_h control0 t z
        _ = callAt rate rewards C_star C_h t (c z) := by
          rw [← ReferenceSourcePhysicalFlagConditionalLaw.c_t_eq_sourcePrefix control0 t z]
    · rfl
  have hfactor : (fun z : SourceInput p => callAt rate rewards C_star C_h t (c z)) =
      callAt rate rewards C_star C_h t := by
    funext z
    change callAt rate rewards C_star C_h t
      (ReferenceSourceCurrentControlFreshness.c_t p control0 t z) = _
    rw [ReferenceSourcePhysicalFlagConditionalLaw.c_t_eq_sourcePrefix control0 t z]
    exact (callAt_factor rate rewards C_star C_h control0 t z).symm
  calc
    μ.map (fun z => (callAt rate rewards C_star C_h t z, u z)) =
        μ.map (fun z => observe (c z, u z)) :=
          congrArg (fun f : SourceInput p → CallAt p × TimeControl p => μ.map f) hpair
    _ = μ.map (observe ∘ fun z => (c z, u z)) := rfl
    _ = (μ.map (fun z => (c z, u z))).map observe := by
      symm
      exact Measure.map_map hobserve hprefixPair
    _ = ((μ.map c).prod (ContinuousLearningRows.timeControlLaw p)).map observe := by
      rw [ReferenceSourceCurrentControlFreshness.source_joint_prefix_control control0 t]
    _ = ((μ.map c).map (callAt rate rewards C_star C_h t)).prod
        ((ContinuousLearningRows.timeControlLaw p).map id) := by
      symm
      exact Measure.map_prod_map (μ.map c) (ContinuousLearningRows.timeControlLaw p)
        hcallBorel measurable_id
    _ = (μ.map (callAt rate rewards C_star C_h t)).prod
        (ContinuousLearningRows.timeControlLaw p) := by
      rw [Measure.map_id]
      congr 1
      calc
        (μ.map c).map (callAt rate rewards C_star C_h t) =
            μ.map (fun z => callAt rate rewards C_star C_h t (c z)) :=
              Measure.map_map hcallBorel hc
        _ = μ.map (callAt rate rewards C_star C_h t) := by
          exact congrArg (fun f : SourceInput p → CallAt p => μ.map f) hfactor

/-- Independence for the entire current assignment-coordinate vector. -/
theorem callAt_currentVector_joint (control0 : TimeControl p) (t : Fin p.T) :
    (BootstrapPrivateRoundStreams.sourceInputLaw p).map (fun z =>
        (callAt rate rewards C_star C_h t z,
          ContinuousControlSlice.assignmentVector
            ((ReferenceSourceCurrentControlFreshness.u_t p t z).1))) =
      ((BootstrapPrivateRoundStreams.sourceInputLaw p).map
        (callAt rate rewards C_star C_h t)).prod
        (ContinuousControlSlice.assignmentLaw p.K) := by
  let vector : TimeControl p → AssignmentVector p :=
    fun control => ContinuousControlSlice.assignmentVector control.1
  have hvector : Measurable vector :=
    ContinuousControlSlice.measurable_assignmentVector p.m p.K |>.comp measurable_fst
  have hvectorLaw :
      (ContinuousLearningRows.timeControlLaw p).map vector =
        ContinuousControlSlice.assignmentLaw p.K := by
    rw [ContinuousLearningRows.timeControlLaw]
    calc
      _ = (((ContinuousControlSlice.sliceLaw p.m p.K).prod
            (ContinuousLearningRows.affineSamplesLaw p)).map Prod.fst).map
              ContinuousControlSlice.assignmentVector := by
            symm
            exact Measure.map_map
              (ContinuousControlSlice.measurable_assignmentVector p.m p.K) measurable_fst
      _ = (ContinuousControlSlice.sliceLaw p.m p.K).map
            ContinuousControlSlice.assignmentVector := by
            simp [Measure.map_fst_prod]
      _ = ContinuousControlSlice.assignmentLaw p.K :=
            ContinuousControlSlice.map_assignmentVector p.m p.K
  let transform : CallAt p × TimeControl p → CallAt p × AssignmentVector p :=
    Prod.map id vector
  have htransform : Measurable transform := measurable_fst.prodMk (hvector.comp measurable_snd)
  have hcall : Measurable (callAt rate rewards C_star C_h t) :=
    (callAt_measurable rate rewards C_star C_h control0 t).mono
      ((ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le'
        (t.val + 1)) le_rfl
  calc
    (BootstrapPrivateRoundStreams.sourceInputLaw p).map
        (fun z => (callAt rate rewards C_star C_h t z,
          vector (ReferenceSourceCurrentControlFreshness.u_t p t z))) =
      ((BootstrapPrivateRoundStreams.sourceInputLaw p).map
        (fun z => (callAt rate rewards C_star C_h t z,
          ReferenceSourceCurrentControlFreshness.u_t p t z))).map transform := by
            symm
            exact Measure.map_map htransform
              ((hcall.prodMk
                (ReferenceSourceCurrentControlFreshness.measurable_u_t t)))
    _ = (((BootstrapPrivateRoundStreams.sourceInputLaw p).map
        (callAt rate rewards C_star C_h t)).prod
          (ContinuousLearningRows.timeControlLaw p)).map transform := by
            rw [callAt_currentControl_joint rate rewards C_star C_h control0 t]
    _ = ((BootstrapPrivateRoundStreams.sourceInputLaw p).map
        (callAt rate rewards C_star C_h t)).prod
          ((ContinuousLearningRows.timeControlLaw p).map vector) := by
            rw [← Measure.map_prod_map
              ((BootstrapPrivateRoundStreams.sourceInputLaw p).map
                (callAt rate rewards C_star C_h t))
              (ContinuousLearningRows.timeControlLaw p) measurable_id hvector]
            simp
    _ = _ := by rw [hvectorLaw]

private theorem prefixObservable_currentControl_joint {X : Type*} [MeasurableSpace X]
    (control0 : TimeControl p) (t : Fin p.T) (f : SourceInput p → X)
    (hf : Measurable[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
      control0 (t.val + 1)] f)
    (hfactor : ∀ z, f z = f
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z)) :
    (BootstrapPrivateRoundStreams.sourceInputLaw p).map (fun z =>
        (f z, ReferenceSourceCurrentControlFreshness.u_t p t z)) =
      ((BootstrapPrivateRoundStreams.sourceInputLaw p).map f).prod
        (ContinuousLearningRows.timeControlLaw p) := by
  let μ := BootstrapPrivateRoundStreams.sourceInputLaw p
  let c := ReferenceSourceCurrentControlFreshness.c_t p control0 t
  let u := ReferenceSourceCurrentControlFreshness.u_t p t
  let output := fun x : SourceInput p × TimeControl p => (f x.1, x.2)
  have hc : Measurable c :=
    ReferenceSourceCurrentControlFreshness.measurable_c_t control0 t
  have hu : Measurable u := ReferenceSourceCurrentControlFreshness.measurable_u_t t
  have hfBorel : Measurable f := hf.mono
    ((ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le'
      (t.val + 1)) le_rfl
  have hprefixPair : Measurable (fun z : SourceInput p => (c z, u z)) := hc.prodMk hu
  have houtput : Measurable output := (hfBorel.comp measurable_fst).prodMk measurable_snd
  have hpair :
      (fun z : SourceInput p => (f z, u z)) = fun z => output (c z, u z) := by
    funext z
    apply Prod.ext
    · calc
        f z = f (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z) :=
          hfactor z
        _ = f (c z) := by
          rw [← ReferenceSourcePhysicalFlagConditionalLaw.c_t_eq_sourcePrefix control0 t z]
    · rfl
  have hfactorC : (fun z : SourceInput p => f (c z)) = f := by
    funext z
    change f (ReferenceSourceCurrentControlFreshness.c_t p control0 t z) = f z
    rw [ReferenceSourcePhysicalFlagConditionalLaw.c_t_eq_sourcePrefix control0 t z]
    exact (hfactor z).symm
  calc
    μ.map (fun z => (f z, u z)) = μ.map (fun z => output (c z, u z)) :=
      congrArg (fun g : SourceInput p → X × TimeControl p => μ.map g) hpair
    _ = μ.map (output ∘ fun z => (c z, u z)) := rfl
    _ = (μ.map (fun z => (c z, u z))).map output := by
      symm
      exact Measure.map_map houtput hprefixPair
    _ = ((μ.map c).prod (ContinuousLearningRows.timeControlLaw p)).map output := by
      rw [ReferenceSourceCurrentControlFreshness.source_joint_prefix_control control0 t]
    _ = ((μ.map c).map f).prod ((ContinuousLearningRows.timeControlLaw p).map id) := by
      symm
      exact Measure.map_prod_map (μ.map c) (ContinuousLearningRows.timeControlLaw p)
        hfBorel measurable_id
    _ = (μ.map f).prod (ContinuousLearningRows.timeControlLaw p) := by
      rw [Measure.map_id]
      congr 1
      calc
        (μ.map c).map f = μ.map (fun z => f (c z)) := Measure.map_map hfBorel hc
        _ = μ.map f := congrArg (fun g : SourceInput p → X => μ.map g) hfactorC

private theorem prefixObservable_currentVector_joint {X : Type*} [MeasurableSpace X]
    (control0 : TimeControl p) (t : Fin p.T) (f : SourceInput p → X)
    (hf : Measurable[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
      control0 (t.val + 1)] f)
    (hfactor : ∀ z, f z = f
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z)) :
    (BootstrapPrivateRoundStreams.sourceInputLaw p).map (fun z =>
        (f z, ContinuousControlSlice.assignmentVector
          ((ReferenceSourceCurrentControlFreshness.u_t p t z).1))) =
      ((BootstrapPrivateRoundStreams.sourceInputLaw p).map f).prod
        (ContinuousControlSlice.assignmentLaw p.K) := by
  let vector : TimeControl p → AssignmentVector p :=
    fun control => ContinuousControlSlice.assignmentVector control.1
  have hvector : Measurable vector :=
    (ContinuousControlSlice.measurable_assignmentVector p.m p.K).comp measurable_fst
  have hvectorLaw :
      (ContinuousLearningRows.timeControlLaw p).map vector =
        ContinuousControlSlice.assignmentLaw p.K := by
    rw [ContinuousLearningRows.timeControlLaw]
    calc
      _ = (((ContinuousControlSlice.sliceLaw p.m p.K).prod
            (ContinuousLearningRows.affineSamplesLaw p)).map Prod.fst).map
              ContinuousControlSlice.assignmentVector := by
            symm
            exact Measure.map_map
              (ContinuousControlSlice.measurable_assignmentVector p.m p.K) measurable_fst
      _ = (ContinuousControlSlice.sliceLaw p.m p.K).map
            ContinuousControlSlice.assignmentVector := by
            simp [Measure.map_fst_prod]
      _ = ContinuousControlSlice.assignmentLaw p.K :=
            ContinuousControlSlice.map_assignmentVector p.m p.K
  let transform : X × TimeControl p → X × AssignmentVector p := Prod.map id vector
  have htransform : Measurable transform := measurable_fst.prodMk
    (hvector.comp measurable_snd)
  have hfBorel : Measurable f := hf.mono
    ((ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le'
      (t.val + 1)) le_rfl
  have hu : Measurable (ReferenceSourceCurrentControlFreshness.u_t p t) :=
    ReferenceSourceCurrentControlFreshness.measurable_u_t t
  calc
    (BootstrapPrivateRoundStreams.sourceInputLaw p).map
        (fun z => (f z, vector (ReferenceSourceCurrentControlFreshness.u_t p t z))) =
      ((BootstrapPrivateRoundStreams.sourceInputLaw p).map
        (fun z => (f z, ReferenceSourceCurrentControlFreshness.u_t p t z))).map transform := by
            symm
            exact Measure.map_map htransform (hfBorel.prodMk hu)
    _ = (((BootstrapPrivateRoundStreams.sourceInputLaw p).map f).prod
        (ContinuousLearningRows.timeControlLaw p)).map transform := by
            rw [prefixObservable_currentControl_joint control0 t f hf hfactor]
    _ = ((BootstrapPrivateRoundStreams.sourceInputLaw p).map f).prod
        ((ContinuousLearningRows.timeControlLaw p).map vector) := by
            rw [← Measure.map_prod_map
              ((BootstrapPrivateRoundStreams.sourceInputLaw p).map f)
              (ContinuousLearningRows.timeControlLaw p) measurable_id hvector]
            simp
    _ = _ := by rw [hvectorLaw]

/-- Independence of the first actual-call observation and the whole current
assignment vector, with its original continuous law. -/
theorem firstAt_currentVector_joint (control0 : TimeControl p) (t : Fin p.T) :
    (BootstrapPrivateRoundStreams.sourceInputLaw p).map (fun z =>
        (firstAt rate rewards C_star C_h t z,
          ContinuousControlSlice.assignmentVector
            ((ReferenceSourceCurrentControlFreshness.u_t p t z).1))) =
      ((BootstrapPrivateRoundStreams.sourceInputLaw p).map
        (firstAt rate rewards C_star C_h t)).prod
        (ContinuousControlSlice.assignmentLaw p.K) :=
  prefixObservable_currentVector_joint control0 t
    (firstAt rate rewards C_star C_h t)
    (firstAt_measurable rate rewards C_star C_h control0 t)
    (firstAt_factor rate rewards C_star C_h control0 t)

/-- Restricting to an actual first-call cell preserves its unnormalized mass
and the complete independent current assignment vector. -/
theorem firstCell_currentVector_joint (control0 : TimeControl p) (u t : Fin p.T) :
    ((BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
      (firstCell rate rewards C_star C_h u t)).map (fun z =>
        (callAt rate rewards C_star C_h t z,
          ContinuousControlSlice.assignmentVector
            ((ReferenceSourceCurrentControlFreshness.u_t p t z).1))) =
      (((BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
        (firstCell rate rewards C_star C_h u t)).map
          (callAt rate rewards C_star C_h t)).prod
        (ContinuousControlSlice.assignmentLaw p.K) := by
  let μ := BootstrapPrivateRoundStreams.sourceInputLaw p
  let vector : TimeControl p → AssignmentVector p :=
    fun control => ContinuousControlSlice.assignmentVector control.1
  let obs : SourceInput p → CallAt p × CallAt p := fun z =>
    (firstAt rate rewards C_star C_h t z, callAt rate rewards C_star C_h t z)
  let joint : SourceInput p → (CallAt p × CallAt p) × AssignmentVector p :=
    fun z => (obs z, vector (ReferenceSourceCurrentControlFreshness.u_t p t z))
  let cell : Set (SourceInput p) := firstCell rate rewards C_star C_h u t
  let cellCode : Set (CallAt p × CallAt p) :=
    {x | (x.1).map (Prod.fst : Fin p.T × Theta p → Fin p.T) = some u}
  let drop : (CallAt p × CallAt p) × AssignmentVector p → CallAt p × AssignmentVector p :=
    fun x => (x.1.2, x.2)
  have hfirstField := firstAt_measurable rate rewards C_star C_h control0 t
  have hcallField := callAt_measurable rate rewards C_star C_h control0 t
  have hobsField : Measurable[
      ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (t.val + 1)] obs :=
    hfirstField.prodMk hcallField
  have hobsFactor (z : SourceInput p) :
      obs z = obs (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z) := by
    apply Prod.ext
    · exact firstAt_factor rate rewards C_star C_h control0 t z
    · exact callAt_factor rate rewards C_star C_h control0 t z
  have hobsBorel : Measurable obs := hobsField.mono
    ((ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le'
      (t.val + 1)) le_rfl
  have hvector : Measurable vector :=
    (ContinuousControlSlice.measurable_assignmentVector p.m p.K).comp measurable_fst
  have hu : Measurable (ReferenceSourceCurrentControlFreshness.u_t p t) :=
    ReferenceSourceCurrentControlFreshness.measurable_u_t t
  have hjointMeas : Measurable joint := hobsBorel.prodMk (hvector.comp hu)
  have hjointLaw := prefixObservable_currentVector_joint control0 t obs hobsField hobsFactor
  have hcellCodeMeasMap : Measurable (fun x : CallAt p × CallAt p =>
      (x.1).map (Prod.fst : Fin p.T × Theta p → Fin p.T)) :=
    LaterAssignmentFullOutputMeasurability.measurable_optionMap
      Prod.fst measurable_fst Prod.fst measurable_fst
  have hcellCodeMeas : MeasurableSet cellCode := by
    change MeasurableSet ((fun x : CallAt p × CallAt p =>
      (x.1).map (Prod.fst : Fin p.T × Theta p → Fin p.T)) ⁻¹'
        ({some u} : Set (Option (Fin p.T))))
    have hsome : MeasurableSet ({some u} : Set (Option (Fin p.T))) := by
      have h := measurableSet_optionSome ({u} : Set (Fin p.T))
        (measurableSet_singleton u)
      simpa only [Set.image_singleton] using h
    exact hcellCodeMeasMap hsome
  have hpreObs : obs ⁻¹' cellCode = cell := by
    ext z
    change (firstAt rate rewards C_star C_h t z).map Prod.fst = some u ↔
      z ∈ firstCell rate rewards C_star C_h u t
    exact (firstCell_iff_firstAt rate rewards C_star C_h u t z).symm
  have hobsMem (z : SourceInput p) : obs z ∈ cellCode ↔ z ∈ cell := by
    have h := congrArg (fun s : Set (SourceInput p) => z ∈ s) hpreObs
    exact Iff.of_eq (by simpa only [Set.mem_preimage] using h)
  have hpreJoint : joint ⁻¹' (cellCode ×ˢ (Set.univ : Set (AssignmentVector p))) = cell := by
    ext z
    change (obs z ∈ cellCode ∧ vector
      (ReferenceSourceCurrentControlFreshness.u_t p t z) ∈ Set.univ) ↔ z ∈ cell
    simp only [Set.mem_univ, and_true]
    exact hobsMem z
  have hrestrictJoint : (μ.restrict cell).map joint =
      (μ.map joint).restrict (cellCode ×ˢ (Set.univ : Set (AssignmentVector p))) := by
    rw [← hpreJoint]
    exact (Measure.restrict_map hjointMeas
      (hcellCodeMeas.prod MeasurableSet.univ)).symm
  have hrestrictedProduct : (μ.restrict cell).map joint =
      ((μ.map obs).restrict cellCode).prod (ContinuousControlSlice.assignmentLaw p.K) := by
    calc
      _ = (μ.map joint).restrict
          (cellCode ×ˢ (Set.univ : Set (AssignmentVector p))) := hrestrictJoint
      _ = ((μ.map obs).prod (ContinuousControlSlice.assignmentLaw p.K)).restrict
          (cellCode ×ˢ (Set.univ : Set (AssignmentVector p))) := by rw [hjointLaw]
      _ = ((μ.map obs).restrict cellCode).prod
          (ContinuousControlSlice.assignmentLaw p.K) := by
        rw [← Measure.restrict_prod_eq_prod_univ]
  have hdropMeas : Measurable drop :=
    (measurable_snd.comp measurable_fst).prodMk measurable_snd
  have hmapDrop : (μ.restrict cell).map
      (fun z => (callAt rate rewards C_star C_h t z,
        vector (ReferenceSourceCurrentControlFreshness.u_t p t z))) =
      ((μ.restrict cell).map joint).map drop := by
    calc
      _ = (μ.restrict cell).map (drop ∘ joint) := rfl
      _ = ((μ.restrict cell).map joint).map drop :=
        (Measure.map_map hdropMeas hjointMeas).symm
  have hfirstMarg : ((μ.map obs).restrict cellCode).map Prod.snd =
      (μ.restrict cell).map (callAt rate rewards C_star C_h t) := by
    calc
      _ = ((μ.restrict (obs ⁻¹' cellCode)).map obs).map Prod.snd := by
        rw [Measure.restrict_map hobsBorel hcellCodeMeas]
      _ = (μ.restrict cell).map (callAt rate rewards C_star C_h t) := by
        rw [hpreObs]
        rw [Measure.map_map measurable_snd hobsBorel]
        rfl
  calc
    _ = ((μ.restrict cell).map joint).map drop := hmapDrop
    _ = (((μ.map obs).restrict cellCode).prod
        (ContinuousControlSlice.assignmentLaw p.K)).map drop := by
          rw [hrestrictedProduct]
    _ = (((μ.map obs).restrict cellCode).map Prod.snd).prod
        (ContinuousControlSlice.assignmentLaw p.K) := by
          rw [show drop = Prod.map Prod.snd id from rfl]
          rw [← Measure.map_prod_map ((μ.map obs).restrict cellCode)
            (ContinuousControlSlice.assignmentLaw p.K) measurable_snd measurable_id]
          rw [Measure.map_id]
    _ = _ := by rw [hfirstMarg]

/-- The full current-control Borel tests have the literal section conditional
expectation on the exact original successor field.
-/
theorem callAt_currentControl_condExp (control0 : TimeControl p) (t : Fin p.T)
    (B : Set (CallAt p × TimeControl p)) (hB : MeasurableSet B) :
    (BootstrapPrivateRoundStreams.sourceInputLaw p)[
      (fun z => B.indicator (fun _ => (1 : ℝ))
        (callAt rate rewards C_star C_h t z,
          ReferenceSourceCurrentControlFreshness.u_t p t z)) |
      ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (t.val + 1)] =ᵐ[
        BootstrapPrivateRoundStreams.sourceInputLaw p]
      fun z => ∫ control, B.indicator (fun _ => (1 : ℝ))
        (callAt rate rewards C_star C_h t z, control)
          ∂ContinuousLearningRows.timeControlLaw p := by
  let μ := BootstrapPrivateRoundStreams.sourceInputLaw p
  let c := ReferenceSourceCurrentControlFreshness.c_t p control0 t
  let u := ReferenceSourceCurrentControlFreshness.u_t p t
  let E : Set (SourceInput p × TimeControl p) :=
    {x | (callAt rate rewards C_star C_h t x.1, x.2) ∈ B}
  have hcall : Measurable (callAt rate rewards C_star C_h t) :=
    (callAt_measurable rate rewards C_star C_h control0 t).mono
      ((ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le'
        (t.val + 1)) le_rfl
  have hE : MeasurableSet E := by
    apply hB.preimage
    exact (hcall.comp measurable_fst).prodMk measurable_snd
  have hcond := ReferenceSourceCurrentControlFreshness.source_control_test_condExp
    control0 t E hE
  have hcallPrefix (z : SourceInput p) : callAt rate rewards C_star C_h t (c z) =
      callAt rate rewards C_star C_h t z := by
    change callAt rate rewards C_star C_h t
      (ReferenceSourceCurrentControlFreshness.c_t p control0 t z) = _
    rw [ReferenceSourcePhysicalFlagConditionalLaw.c_t_eq_sourcePrefix control0 t z]
    exact (callAt_factor rate rewards C_star C_h control0 t z).symm
  have htest : ReferenceSourceCurrentControlFreshness.sourceControlTest p control0 t E =ᵐ[μ]
      (fun z => B.indicator (fun _ => (1 : ℝ))
        (callAt rate rewards C_star C_h t z, u z)) := by
    apply Filter.Eventually.of_forall
    intro z
    change (if (callAt rate rewards C_star C_h t (c z), u z) ∈ B then (1 : ℝ) else 0) =
      (if (callAt rate rewards C_star C_h t z, u z) ∈ B then (1 : ℝ) else 0)
    rw [hcallPrefix z]
  have hleft : μ[(fun z => B.indicator (fun _ => (1 : ℝ))
        (callAt rate rewards C_star C_h t z, u z)) |
      ReferenceSourceCurrentControlFreshness.m_t p control0 t] =ᵐ[μ]
      μ[ReferenceSourceCurrentControlFreshness.sourceControlTest p control0 t E |
        ReferenceSourceCurrentControlFreshness.m_t p control0 t] :=
    MeasureTheory.condExp_congr_ae htest.symm
  have hright : (fun z => ∫ control,
      E.indicator (fun _ => (1 : ℝ)) (c z, control)
        ∂ContinuousLearningRows.timeControlLaw p) =ᵐ[μ]
      (fun z => ∫ control, B.indicator (fun _ => (1 : ℝ))
        (callAt rate rewards C_star C_h t z, control)
          ∂ContinuousLearningRows.timeControlLaw p) := by
    apply Filter.Eventually.of_forall
    intro z
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun control => by
      change (if (callAt rate rewards C_star C_h t (c z), control) ∈ B then (1 : ℝ) else 0) =
        (if (callAt rate rewards C_star C_h t z, control) ∈ B then (1 : ℝ) else 0)
      rw [hcallPrefix z]
  have hfull := hleft.trans (hcond.trans hright)
  simpa only [ReferenceSourcePhysicalFlagConditionalLaw.sourcePrefixField_eq_m_t
    control0 t] using hfull

/-- The same bounded Borel-test identity holds for the concrete first-date
projection, using its finite-past formula. -/
theorem firstAt_currentControl_condExp (control0 : TimeControl p) (t : Fin p.T)
    (B : Set (CallAt p × TimeControl p)) (hB : MeasurableSet B) :
    (BootstrapPrivateRoundStreams.sourceInputLaw p)[
      (fun z => B.indicator (fun _ => (1 : ℝ))
        (firstAt rate rewards C_star C_h t z,
          ReferenceSourceCurrentControlFreshness.u_t p t z)) |
      ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (t.val + 1)] =ᵐ[
        BootstrapPrivateRoundStreams.sourceInputLaw p]
      fun z => ∫ control, B.indicator (fun _ => (1 : ℝ))
        (firstAt rate rewards C_star C_h t z, control)
          ∂ContinuousLearningRows.timeControlLaw p := by
  let μ := BootstrapPrivateRoundStreams.sourceInputLaw p
  let c := ReferenceSourceCurrentControlFreshness.c_t p control0 t
  let u := ReferenceSourceCurrentControlFreshness.u_t p t
  let E : Set (SourceInput p × TimeControl p) :=
    {x | (firstAt rate rewards C_star C_h t x.1, x.2) ∈ B}
  have hfirst : Measurable (firstAt rate rewards C_star C_h t) :=
    (firstAt_measurable rate rewards C_star C_h control0 t).mono
      ((ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le'
        (t.val + 1)) le_rfl
  have hE : MeasurableSet E := by
    apply hB.preimage
    exact (hfirst.comp measurable_fst).prodMk measurable_snd
  have hcond := ReferenceSourceCurrentControlFreshness.source_control_test_condExp
    control0 t E hE
  have hfirstPrefix (z : SourceInput p) :
      firstAt rate rewards C_star C_h t (c z) = firstAt rate rewards C_star C_h t z := by
    change firstAt rate rewards C_star C_h t
      (ReferenceSourceCurrentControlFreshness.c_t p control0 t z) = _
    rw [ReferenceSourcePhysicalFlagConditionalLaw.c_t_eq_sourcePrefix control0 t z]
    exact (firstAt_factor rate rewards C_star C_h control0 t z).symm
  have htest : ReferenceSourceCurrentControlFreshness.sourceControlTest p control0 t E =ᵐ[μ]
      (fun z => B.indicator (fun _ => (1 : ℝ))
        (firstAt rate rewards C_star C_h t z, u z)) := by
    apply Filter.Eventually.of_forall
    intro z
    change (if (firstAt rate rewards C_star C_h t (c z), u z) ∈ B then (1 : ℝ) else 0) =
      (if (firstAt rate rewards C_star C_h t z, u z) ∈ B then (1 : ℝ) else 0)
    rw [hfirstPrefix z]
  have hleft : μ[(fun z => B.indicator (fun _ => (1 : ℝ))
        (firstAt rate rewards C_star C_h t z, u z)) |
      ReferenceSourceCurrentControlFreshness.m_t p control0 t] =ᵐ[μ]
      μ[ReferenceSourceCurrentControlFreshness.sourceControlTest p control0 t E |
        ReferenceSourceCurrentControlFreshness.m_t p control0 t] :=
    MeasureTheory.condExp_congr_ae htest.symm
  have hright : (fun z => ∫ control,
      E.indicator (fun _ => (1 : ℝ)) (c z, control)
        ∂ContinuousLearningRows.timeControlLaw p) =ᵐ[μ]
      (fun z => ∫ control, B.indicator (fun _ => (1 : ℝ))
        (firstAt rate rewards C_star C_h t z, control)
          ∂ContinuousLearningRows.timeControlLaw p) := by
    apply Filter.Eventually.of_forall
    intro z
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun control => by
      change (if (firstAt rate rewards C_star C_h t (c z), control) ∈ B then
          (1 : ℝ) else 0) =
        (if (firstAt rate rewards C_star C_h t z, control) ∈ B then (1 : ℝ) else 0)
      rw [hfirstPrefix z]
  have hfull := hleft.trans (hcond.trans hright)
  simpa only [ReferenceSourcePhysicalFlagConditionalLaw.sourcePrefixField_eq_m_t
    control0 t] using hfull

end Bandits.Support.ReferenceCalendarCollectionCallControlLaw

end
