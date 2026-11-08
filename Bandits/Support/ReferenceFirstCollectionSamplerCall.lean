/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFiniteSourcePath
public import Bandits.Support.ReferenceGeneratedCompleteCalendarObservation

/-!
# The first actual later-sampler invocation

Sources: `sources/zip4/manuscript/06_interruptions.tex:399-423`,
`sources/zip4/manuscript/04_slow_fast_learner.tex:176-180,206-208`,
`sources/zip4/manuscript/07_public_setup.tex:121-164`, and
`sources/zip4/manuscript/appendix_b_communication.tex:25-58`.

The observer reads the incoming collection phase and the existing prechoice
parameter selector, including calls whose subsequent prefix or orientation
fails. It keeps every actual suffix calendar entry. Measurability uses the
original product Borel spaces and the genuine generated launch fibres;
preservation uses the joint chronological evidence equality of the admitted
finite source path. No auxiliary randomness or logical slow-set law is defined.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions

namespace Bandits.Support.ReferenceFirstCollectionSamplerCall

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev SourceInput (p : Parameters) := BootstrapPrivateRoundStreams.SourceInput p
abbrev Rewards (p : Parameters) := ActualInitializationPhysicalStep.GridRewardTable p
abbrev Theta (p : Parameters) := AssignmentParameterFibreKernel.Theta p
abbrev RoundRecord (p : Parameters) (rate : RateInput p) :=
  ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)
abbrev CalendarCell (p : Parameters) := Fin p.T × Option (Fin p.T × Theta p)
abbrev Call (p : Parameters) := Fin p.T × (Fin p.T × Theta p)

variable {p : Parameters} {rate : RateInput p}

local instance optionFinMeasurableSpace : MeasurableSpace (Option (Fin p.T)) :=
  LaterAssignmentStartMeasurability.optionMeasurableSpace

/-- The literal incoming-phase/cutoff check followed by the actual prechoice
selector. No successful-assignment test is imposed. -/
def collectionCallOnInput (x : ReferenceActivePhysicalStep.RoundInput p rate) :
    Option (Fin p.T × Theta p) :=
  match x.state.coordinator with
  | .collection _ ledger _ =>
      if hc : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T then
        let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
        (ReferenceLaterSamplerParameterMeasurability.parameters? x).map
          (fun theta => (cutoff, theta))
      else none
  | _ => none

/-- Observe an existing actual record, before assignment choice. -/
def collectionCallAt (r : RoundRecord p rate) : Option (Fin p.T × Theta p) :=
  collectionCallOnInput r.input

/-- Exact characterization on the original input. The existential constructor
data are fields of its incoming coordinator, not supplied request data. -/
theorem collectionCallOnInput_spec (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (u : Fin p.T) (theta : Theta p) :
    collectionCallOnInput x = some (u, theta) ↔
      ∃ payload ledger proposal,
        x.state.coordinator = .collection payload ledger proposal ∧
        ledger.cutoff = u.val + 1 ∧
        ReferenceLaterSamplerParameterMeasurability.parameters? x = some theta := by
  cases hcoord : x.state.coordinator with
  | first => simp [collectionCallOnInput, hcoord]
  | live registers owned base => simp [collectionCallOnInput, hcoord]
  | dagger => simp [collectionCallOnInput, hcoord]
  | collection payload ledger proposal =>
      by_cases hc : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
      · simp only [collectionCallOnInput, hcoord, dite_eq_left hc, Option.map_eq_some_iff,
          Prod.mk.injEq]
        constructor
        · rintro ⟨theta', hp, hu, rfl⟩
          refine ⟨payload, ledger, proposal, rfl, ?_, hp⟩
          have hv := congrArg Fin.val hu
          dsimp at hv
          omega
        · rintro ⟨payload', ledger', proposal', heq, hcut, hp⟩
          cases heq
          refine ⟨theta, hp, ?_, rfl⟩
          apply Fin.ext
          dsimp
          omega
      · have hn (hcut : ledger.cutoff = u.val + 1) : False := by
          apply hc
          have hu := u.isLt
          omega
        simp only [collectionCallOnInput, hcoord, dite_eq_right hc]
        constructor
        · intro h
          cases h
        · rintro ⟨payload', ledger', proposal', heq, hcut, _⟩
          cases heq
          exact (hn hcut).elim

/-- Exact invocation characterization for each actual record. -/
theorem collectionCallAt_spec (r : RoundRecord p rate) (u : Fin p.T) (theta : Theta p) :
    collectionCallAt r = some (u, theta) ↔
      ∃ payload ledger proposal,
        r.input.state.coordinator = .collection payload ledger proposal ∧
        ledger.cutoff = u.val + 1 ∧
        ReferenceLaterSamplerParameterMeasurability.parameters? r.input = some theta :=
  collectionCallOnInput_spec r.input u theta

/-- Malformed cutoffs and other phases are absent exactly as in the physical
selector. Reconstruction failures are absent, but later sampling failures need
not be absent. This statement holds on every existing input. -/
theorem collectionCallOnInput_isSome (x : ReferenceActivePhysicalStep.RoundInput p rate) :
    (collectionCallOnInput x).isSome =
      (ReferenceLaterSamplerParameterMeasurability.parameters? x).isSome := by
  cases hcoord : x.state.coordinator with
  | first => simp [collectionCallOnInput, ReferenceLaterSamplerParameterMeasurability.parameters?,
      ReferenceLaterAssignmentFibreStep.parameters?, hcoord]
  | live registers owned base =>
      simp [collectionCallOnInput, ReferenceLaterSamplerParameterMeasurability.parameters?,
        ReferenceLaterAssignmentFibreStep.parameters?, hcoord]
  | dagger => simp [collectionCallOnInput, ReferenceLaterSamplerParameterMeasurability.parameters?,
      ReferenceLaterAssignmentFibreStep.parameters?, hcoord]
  | collection payload ledger proposal =>
      by_cases hc : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
      · simp only [collectionCallOnInput, hcoord, dite_eq_left hc, Option.isSome_map]
      · simp [collectionCallOnInput, ReferenceLaterSamplerParameterMeasurability.parameters?,
          ReferenceLaterAssignmentFibreStep.parameters?, hcoord, hc]

theorem collectionCallAt_isSome (r : RoundRecord p rate) :
    (collectionCallAt r).isSome =
      (ReferenceLaterSamplerParameterMeasurability.parameters? r.input).isSome :=
  collectionCallOnInput_isSome r.input

theorem collectionCallAt_none_iff (r : RoundRecord p rate) :
    collectionCallAt r = none ↔
      ReferenceLaterSamplerParameterMeasurability.parameters? r.input = none := by
  exact Option.isSome_eq_isSome.mp (collectionCallAt_isSome r)

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
  cases ho : o x <;> rfl

private def pairOptions {A B : Type*} (z : Option A × Option B) : Option (A × B) :=
  z.1.bind (fun a => z.2.map (fun b => (a, b)))

private theorem measurable_pairOptions {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B] :
    Measurable (pairOptions (A := A) (B := B)) := by
  let e := ReferenceCollectionDispatchMeasurability.optionPairEquiv A (Option B)
  have hleft : Measurable (fun z : A × Option B => z.2.map (fun b => (z.1, b))) :=
    measurable_optionMapWith Prod.fst measurable_fst Prod.snd measurable_snd id measurable_id
  have h := (hleft.sumElim (measurable_const :
    Measurable (fun _ : PUnit × Option B => (none : Option (A × B))))).comp e.measurable
  convert h using 1
  funext z
  rcases z with ⟨o, value⟩
  cases o <;> rfl

private def cutoffFromLedger? (ledger : ReferenceActivePhysicalStep.Ledger rate) :
    Option (Fin p.T) :=
  if hc : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T then
    some ⟨ledger.cutoff - 1, by omega⟩
  else none

private def cutoffFromCoordinatorCode? :
    ReferenceActivePhysicalStepMeasurability.CoordinatorCode p rate → Option (Fin p.T)
  | .inr (.inr (.inl (_, ledger, _))) => cutoffFromLedger? ledger
  | _ => none

private theorem measurable_cutoffFromCoordinatorCode? :
    Measurable (cutoffFromCoordinatorCode? (p := p) (rate := rate)) := by
  apply measurable_fun_sum measurable_const
  apply measurable_fun_sum measurable_const
  exact measurable_fun_sum
    ((measurable_of_countable cutoffFromLedger?).comp
      (measurable_fst.comp measurable_snd)) measurable_const

/-- Joint Borel measurability on the original active RoundInput schema.
Only the ledger's already countable cutoff field is used for the finite index;
payloads, rows and the parameter retain their existing Borel structures. -/
theorem measurable_collectionCallOnInput :
    Measurable (collectionCallOnInput (p := p) (rate := rate)) := by
  have heq : collectionCallOnInput (p := p) (rate := rate) = fun x =>
      pairOptions
        (cutoffFromCoordinatorCode?
          (ReferenceActivePhysicalStepMeasurability.encodeCoordinator x.state.coordinator),
        ReferenceLaterSamplerParameterMeasurability.parameters? x) := by
    funext x
    cases hcoord : x.state.coordinator with
    | first => simp only [collectionCallOnInput, hcoord, pairOptions,
        ReferenceActivePhysicalStepMeasurability.encodeCoordinator,
        cutoffFromCoordinatorCode?, Option.bind_none]
    | live registers owned base => simp only [collectionCallOnInput, hcoord, pairOptions,
        ReferenceActivePhysicalStepMeasurability.encodeCoordinator,
        cutoffFromCoordinatorCode?, Option.bind_none]
    | dagger => simp only [collectionCallOnInput, hcoord, pairOptions,
        ReferenceActivePhysicalStepMeasurability.encodeCoordinator,
        cutoffFromCoordinatorCode?, Option.bind_none]
    | collection payload ledger proposal =>
        by_cases hc : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T <;>
          simp [collectionCallOnInput, hcoord, pairOptions, cutoffFromCoordinatorCode?,
            cutoffFromLedger?, ReferenceActivePhysicalStepMeasurability.encodeCoordinator, hc]
  rw [heq]
  exact measurable_pairOptions.comp
    ((measurable_cutoffFromCoordinatorCode?.comp
      (ReferenceActivePhysicalStepMeasurability.measurable_coordinatorCode.comp
        ReferenceActivePhysicalStepMeasurability.measurable_state)).prodMk
      ReferenceLaterSamplerParameterMeasurability.measurable_parameters?)

/-- Every actual suffix entry, including an absent call. -/
def collectionCallCalendar (rate : RateInput p) (rewards : Rewards p) (C_star C_h : ℝ)
    (source : SourceInput p) : List (CalendarCell p) :=
  (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h).map
    (fun r => (r.input.time, collectionCallAt r))

/-- The present call in a calendar cell, ordered as cutoff, physical time,
parameter. Absence remains absence. -/
def callInCell (cell : CalendarCell p) : Option (Call p) :=
  cell.2.map (fun call => (call.1, (cell.1, call.2)))

/-- Literal ordered search in the complete actual calendar. -/
def firstCollectionCall (rate : RateInput p) (rewards : Rewards p) (C_star C_h : ℝ)
    (source : SourceInput p) : Option (Call p) :=
  (collectionCallCalendar rate rewards C_star C_h source).findSome? callInCell

/-- Calendar length is exactly the actual suffix length. -/
theorem collectionCallCalendar_length (rewards : Rewards p) (C_star C_h : ℝ)
    (source : SourceInput p) :
    (collectionCallCalendar rate rewards C_star C_h source).length =
      p.T - ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h := by
  simp only [collectionCallCalendar, List.length_map]
  exact ReferenceCompletePhysicalHistory.completeSuffixRecords_length
    rate source rewards C_star C_h

/-- Exact chronological physical timestamps, with no terminal action. -/
theorem collectionCallCalendar_times (rewards : Rewards p) (C_star C_h : ℝ)
    (source : SourceInput p) :
    (collectionCallCalendar rate rewards C_star C_h source).map (fun cell => cell.1.val) =
      List.range' (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
        (p.T - ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h) 1 := by
  simpa only [collectionCallCalendar, List.map_map, Function.comp_def,
    ReferenceActivePhysicalHorizon.calendar] using
    ReferenceCompletePhysicalHistory.completeSuffixRecords_time_values
      rate source rewards C_star C_h

private theorem findSome?_eq_some_index {α β : Type*} (f : α → Option β)
    (l : List α) (b : β) :
    l.findSome? f = some b ↔
      ∃ n : ℕ, l[n]?.bind f = some b ∧ ∀ j < n, l[j]?.bind f = none := by
  induction l with
  | nil => simp
  | cons a l ih =>
      cases hfa : f a with
      | none =>
          simp only [List.findSome?_cons, hfa]
          rw [ih]
          constructor
          · rintro ⟨n, hn, hearlier⟩
            refine ⟨n + 1, hn, ?_⟩
            intro j hj
            cases j with
            | zero => simpa using hfa
            | succ j => exact hearlier j (by omega)
          · rintro ⟨n, hn, hearlier⟩
            cases n with
            | zero => simp [hfa] at hn
            | succ n =>
                exact ⟨n, hn, fun j hj => hearlier (j + 1) (by omega)⟩
      | some value =>
          simp only [List.findSome?_cons, hfa]
          constructor
          · intro h
            exact ⟨0, by simpa [hfa] using h, by simp⟩
          · rintro ⟨n, hn, hearlier⟩
            cases n with
            | zero => simpa [hfa] using hn
            | succ n => simpa [hfa] using hearlier 0 (by omega)

private theorem bind_getElem?_none_iff {α β : Type*} (l : List α) (f : α → Option β) :
    (∀ n : ℕ, l[n]?.bind f = none) ↔ ∀ a ∈ l, f a = none := by
  constructor
  · intro h a ha
    obtain ⟨n, hn⟩ := List.mem_iff_getElem?.mp ha
    simpa only [hn, Option.bind_some] using h n
  · intro h n
    cases hn : l[n]? with
    | none => rfl
    | some a => exact h a (List.mem_of_getElem? hn)

/-- A returned first call is an indexed actual record; every earlier actual
record has an absent parameter selector. No matching/success premise occurs. -/
theorem firstCollectionCall_spec (rewards : Rewards p) (C_star C_h : ℝ)
    (source : SourceInput p) (u t : Fin p.T) (theta : Theta p) :
    firstCollectionCall rate rewards C_star C_h source = some (u, (t, theta)) ↔
      ∃ (n : ℕ) (r : RoundRecord p rate),
        (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h)[n]? = some r ∧
        r.input.time = t ∧ collectionCallAt r = some (u, theta) ∧
        ∀ j < n, ∀ earlier : RoundRecord p rate,
          (ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate source rewards C_star C_h)[j]? = some earlier →
          ReferenceLaterSamplerParameterMeasurability.parameters? earlier.input = none := by
  let records := ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h
  have hfirst : firstCollectionCall rate rewards C_star C_h source =
      records.findSome? (fun r => callInCell (r.input.time, collectionCallAt r)) := by
    simp only [firstCollectionCall, collectionCallCalendar, List.findSome?_map,
      Function.comp_def, records]
  rw [hfirst, findSome?_eq_some_index]
  constructor
  · rintro ⟨n, hn, hearlier⟩
    cases hr : records[n]? with
    | none => simp [hr] at hn
    | some r =>
        simp only [hr, Option.bind_some, callInCell, Option.map_eq_some_iff] at hn
        obtain ⟨⟨u', theta'⟩, hcall, heq⟩ := hn
        cases heq
        refine ⟨n, r, hr, rfl, hcall, ?_⟩
        intro j hj earlier hrecord
        have h := hearlier j hj
        rw [hrecord] at h
        simp only [Option.bind_some, callInCell, Option.map_eq_none_iff] at h
        exact (collectionCallAt_none_iff earlier).1 h
  · rintro ⟨n, r, hr, htime, hcall, hearlier⟩
    refine ⟨n, ?_, ?_⟩
    · simp only [records, hr, Option.bind_some, callInCell, hcall, Option.map_some, htime]
    · intro j hj
      cases hrecord : records[j]? with
      | none => rfl
      | some earlier =>
          have hnone := (collectionCallAt_none_iff earlier).2
            (hearlier j hj earlier hrecord)
          simp only [Option.bind_some, callInCell, hnone, Option.map_none]

/-- No call is equivalent to absence of the actual selector in every suffix
record, including an empty no-launch or terminal suffix. -/
theorem firstCollectionCall_none_iff (rewards : Rewards p) (C_star C_h : ℝ)
    (source : SourceInput p) :
    firstCollectionCall rate rewards C_star C_h source = none ↔
      ∀ r ∈ ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h,
        ReferenceLaterSamplerParameterMeasurability.parameters? r.input = none := by
  simp only [firstCollectionCall, collectionCallCalendar, List.findSome?_map,
    List.findSome?_eq_none_iff, Function.comp_def, callInCell, Option.map_eq_none_iff,
    collectionCallAt_none_iff]

/-- The actual empty suffix at the physical horizon has no call. -/
theorem firstCollectionCall_none_of_terminal (rewards : Rewards p) (C_star C_h : ℝ)
    (source : SourceInput p)
    (hterminal : ReferenceCompletePhysicalHistory.physicalStart
      rate source rewards C_star C_h = p.T) :
    collectionCallCalendar rate rewards C_star C_h source = [] ∧
      firstCollectionCall rate rewards C_star C_h source = none := by
  have hlen := collectionCallCalendar_length (rate := rate) rewards C_star C_h source
  rw [hterminal, Nat.sub_self] at hlen
  have hnil := List.length_eq_zero_iff.mp hlen
  exact ⟨hnil, by simp only [firstCollectionCall, hnil, List.findSome?_nil]⟩

private theorem measurable_list_append_singleton {X A : Type*}
    [MeasurableSpace X] [MeasurableSpace A] (records : X → List A)
    (hrecords : Measurable records) (n : ℕ) (hlen : ∀ x, (records x).length = n)
    (last : X → A) (hlast : Measurable last) :
    Measurable (fun x => records x ++ [last x]) := by
  apply measurable_comap_iff.mpr
  have hcoordinates := ReferenceActiveHorizonMeasurability.measurable_listObservationCoordinates.comp
    hrecords
  have hlength : Measurable (fun x => (records x ++ [last x]).length) := by
    have heq : (fun x => (records x ++ [last x]).length) = fun _ => n + 1 := by
      funext x
      simp only [List.length_append, List.length_singleton, hlen x]
    rw [heq]
    exact measurable_const
  have hstream : Measurable (fun x => fun k =>
      ReferenceActiveHorizonMeasurability.listObservationAt (records x ++ [last x]) k) := by
    apply measurable_pi_iff.mpr
    intro k
    by_cases hkn : k < n
    · have heq (x) :
          ReferenceActiveHorizonMeasurability.listObservationAt (records x ++ [last x]) k =
            ReferenceActiveHorizonMeasurability.listObservationAt (records x) k := by
        unfold ReferenceActiveHorizonMeasurability.listObservationAt
        rw [List.getElem?_append_left (by simpa only [hlen x] using hkn)]
      simp_rw [heq]
      exact (measurable_pi_apply k).comp (measurable_snd.comp hcoordinates)
    · by_cases hkeq : k = n
      · subst k
        have heq (x) :
            ReferenceActiveHorizonMeasurability.listObservationAt (records x ++ [last x]) n =
              Sum.inr (last x) := by
          unfold ReferenceActiveHorizonMeasurability.listObservationAt
          rw [List.getElem?_append_right (by simp only [hlen x, le_refl])]
          simp only [hlen x, Nat.sub_self, List.getElem?_cons_zero]
        simp_rw [heq]
        exact measurable_inr.comp hlast
      · have heq (x) :
            ReferenceActiveHorizonMeasurability.listObservationAt (records x ++ [last x]) k =
              Sum.inl () := by
          unfold ReferenceActiveHorizonMeasurability.listObservationAt
          rw [List.getElem?_eq_none (by simp only [List.length_append,
            List.length_singleton, hlen x]; omega)]
        simp_rw [heq]
        exact measurable_const
  exact hlength.prodMk hstream

private def runCalendar (start count : ℕ) (hspan : start + count ≤ p.T)
    (input : ReferenceActiveHorizonMeasurability.ActiveRunInput (p := p) (rate := rate) start) :
    List (CalendarCell p) :=
  (ReferenceActiveHorizonMeasurability.runOfInput start count hspan input).records.map
    (fun r => (r.input.time, collectionCallAt r))

-- This is the actual next input of the already computed prefix run. No
-- operational state is decoded or fabricated to prove its measurability.
private def nextRoundInput (start count : ℕ) (hspan : start + (count + 1) ≤ p.T)
    (input : ReferenceActiveHorizonMeasurability.ActiveRunInput (p := p) (rate := rate) start) :=
  ReferenceActivePhysicalHorizon.roundInputAt input.val.1 input.val.2.1
    input.val.2.2.1 input.val.2.2.2 start input.property
    (ReferenceActiveHorizonMeasurability.runOfInput start count (by omega) input)
    ⟨start + count, by omega, by omega⟩

private theorem measurable_nextRoundInput (start count : ℕ)
    (hspan : start + (count + 1) ≤ p.T) :
    Measurable (nextRoundInput (p := p) (rate := rate) start count hspan) := by
  have hdata : Measurable (fun input :
      ReferenceActiveHorizonMeasurability.ActiveRunInput (p := p) (rate := rate) start =>
        input.val) := measurable_subtype_coe
  have hstate := ReferenceActiveHorizonMeasurability.measurable_runFinalState
    (p := p) (rate := rate) start count (by omega)
  have hrows := measurable_fst.comp (measurable_snd.comp hdata)
  have hselected := measurable_fst.comp (measurable_snd.comp (measurable_snd.comp hdata))
  have hrewards := measurable_snd.comp (measurable_snd.comp (measurable_snd.comp hdata))
  have hcoordinates := hstate.prodMk (hrows.prodMk (hselected.prodMk
    ((measurable_const : Measurable (fun _ :
      ReferenceActiveHorizonMeasurability.ActiveRunInput (p := p) (rate := rate) start =>
        (⟨start + count, by omega⟩ : Fin p.T))).prodMk hrewards)))
  apply measurable_comap_iff.mpr
  exact hcoordinates.subtype_mk (h := fun input =>
    (nextRoundInput start count hspan input).active)

private theorem runCalendar_succ (start count : ℕ) (hspan : start + (count + 1) ≤ p.T)
    (input : ReferenceActiveHorizonMeasurability.ActiveRunInput (p := p) (rate := rate) start) :
    runCalendar start (count + 1) hspan input =
      runCalendar start count (by omega) input ++
        [((nextRoundInput start count hspan input).time,
          collectionCallOnInput (nextRoundInput start count hspan input))] := by
  have hrun := ReferenceActivePhysicalHorizon.run_successor_step input.val.1 input.val.2.1
    input.val.2.2.1 input.val.2.2.2 start count hspan input.property
  have hfold := ReferenceActivePhysicalHorizon.foldRound_equations input.val.1 input.val.2.1
    input.val.2.2.1 input.val.2.2.2 start input.property
    (ReferenceActiveHorizonMeasurability.runOfInput start count (by omega) input)
    ⟨start + count, by omega, by omega⟩
  unfold runCalendar
  change (ReferenceActivePhysicalHorizon.run input.val.1 input.val.2.1 input.val.2.2.1
    input.val.2.2.2 start (count + 1) hspan input.property).records.map _ = _
  simp only [ReferenceActiveHorizonMeasurability.runOfInput] at hfold
  rw [hrun, hfold.2, List.map_append, List.map_singleton]
  rfl

private theorem measurable_runCalendar (start count : ℕ) (hspan : start + count ≤ p.T) :
    Measurable (runCalendar (p := p) (rate := rate) start count hspan) := by
  induction count with
  | zero =>
      have heq : runCalendar (p := p) (rate := rate) start 0 hspan = fun _ => [] := by
        funext input
        simp only [runCalendar, ReferenceActiveHorizonMeasurability.runOfInput,
          ReferenceActivePhysicalHorizon.run_zero_records, List.map_nil]
      rw [heq]
      exact measurable_const
  | succ count ih =>
      have hinput := measurable_nextRoundInput (p := p) (rate := rate) start count hspan
      have hlast := (ReferenceActivePhysicalStepMeasurability.measurable_time.comp hinput).prodMk
        (measurable_collectionCallOnInput.comp hinput)
      have hlen (input :
          ReferenceActiveHorizonMeasurability.ActiveRunInput (p := p) (rate := rate) start) :
          (runCalendar start count (by omega) input).length = count := by
        simp only [runCalendar, List.length_map, ReferenceActiveHorizonMeasurability.runOfInput]
        exact ReferenceActivePhysicalHorizon.run_record_count input.val.1 input.val.2.1
          input.val.2.2.1 input.val.2.2.2 start count (by omega) input.property
      have h := measurable_list_append_singleton (runCalendar start count (by omega))
        (ih (by omega)) count hlen _ hlast
      convert h using 1
      funext input
      exact runCalendar_succ start count hspan input

private theorem calendar_on_launch_fiber (rewards : Rewards p) (C_star C_h : ℝ)
    (s : Fin (p.T + 1))
    (source : ReferenceGeneratedDownAmbiguityMeasurability.GeneratedLaunchFiber
      (rate := rate) rewards C_star C_h s.val) :
    collectionCallCalendar rate rewards C_star C_h source.val =
      runCalendar s.val (p.T - s.val) (by omega)
        (ReferenceGeneratedDownAmbiguityMeasurability.generatedActiveRunInput
          (rate := rate) rewards C_star C_h s.val source) := by
  have hstart : ReferenceCompletePhysicalHistory.physicalStart
      rate source.val rewards C_star C_h = s.val := source.property.2
  have hlen : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source.val rewards C_star C_h).length ≤ p.T - s.val := by
    rw [ReferenceCompletePhysicalHistory.completeSuffixRecords_length, hstart]
  unfold runCalendar
  rw [ReferenceGeneratedDownAmbiguityMeasurability.generatedRun_records_eq_completeSuffixRecords_take,
    List.take_of_length_le hlen]
  rfl

/-- Borel measurability of the whole literal calendar on the original source.
The cover includes no launch and the zero-round terminal launch. All genuine
launch fibres are glued using their actual generated run inputs. -/
theorem measurable_collectionCallCalendar
    (rate : RateInput p) (rewards : Rewards p) (C_star C_h : ℝ) :
    Measurable (collectionCallCalendar rate rewards C_star C_h) := by
  let code := ReferenceGeneratedCompleteCalendarObservation.completeSuffixCode
    (rate := rate) rewards C_star C_h
  let emptySet : Set (SourceInput p) := {source | (code source).length = 0}
  have hemptySet : MeasurableSet emptySet := by
    exact measurableSet_eq_fun
      (measurable_fst.comp
        (ReferenceActiveHorizonMeasurability.measurable_listObservationCoordinates.comp
          (ReferenceGeneratedCompleteCalendarObservation.measurable_completeSuffixCode
            (rate := rate) rewards C_star C_h))) measurable_const
  have hempty (source : SourceInput p) (h : source ∈ emptySet) :
      collectionCallCalendar rate rewards C_star C_h source = [] := by
    apply List.length_eq_zero_iff.mp
    change (code source).length = 0 at h
    simpa only [collectionCallCalendar, code,
      ReferenceGeneratedCompleteCalendarObservation.completeSuffixCode, List.length_map] using h
  have hcover (source : SourceInput p) : source ∈ emptySet ∨
      ∃ s : Fin (p.T + 1), source ∈
        ReferenceGeneratedDownAmbiguityMeasurability.generatedLaunchFiberSet
          (rate := rate) rewards C_star C_h s.val := by
    by_cases hn : ReferenceCorrectedInitializationLaunch.correctedLaunch
        rate source rewards C_star C_h = none
    · left
      change (code source).length = 0
      simp only [code,
        ReferenceGeneratedCompleteCalendarObservation.completeSuffixCode,
        ReferenceCompletePhysicalHistory.completeSuffixRecords, dite_eq_left hn,
        List.map_nil, List.length_nil]
    · right
      refine ⟨⟨ReferenceCompletePhysicalHistory.physicalStart
        rate source rewards C_star C_h, ?_⟩, ?_⟩
      · have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T
          rate source rewards C_star C_h
        omega
      · refine ⟨?_, rfl⟩
        have hsome := Option.ne_none_iff_isSome.mp hn
        have hcross := (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
          rate source rewards C_star C_h).mp hsome
        simpa only [ReferenceCompletePhysicalHistory.generatedBoundary,
          ReferenceCompletePhysicalHistory.generatedInput] using hcross
  have hfiber (s : Fin (p.T + 1)) :
      Measurable (fun source : ReferenceGeneratedDownAmbiguityMeasurability.GeneratedLaunchFiber
        (rate := rate) rewards C_star C_h s.val =>
        collectionCallCalendar rate rewards C_star C_h source.val) := by
    simp_rw [calendar_on_launch_fiber rewards C_star C_h s]
    exact (measurable_runCalendar s.val (p.T - s.val) (by omega)).comp
      (ReferenceGeneratedDownAmbiguityMeasurability.measurable_generatedActiveRunInput
        (rate := rate) rewards C_star C_h s.val)
  intro target htarget
  have heq : collectionCallCalendar rate rewards C_star C_h ⁻¹' target =
      (Subtype.val '' ((fun source : emptySet =>
        collectionCallCalendar rate rewards C_star C_h source.val) ⁻¹' target)) ∪
      ⋃ s : Fin (p.T + 1), Subtype.val ''
        ((fun source : ReferenceGeneratedDownAmbiguityMeasurability.GeneratedLaunchFiber
          (rate := rate) rewards C_star C_h s.val =>
          collectionCallCalendar rate rewards C_star C_h source.val) ⁻¹' target) := by
    ext source
    constructor
    · intro h
      rcases hcover source with hzero | ⟨s, hs⟩
      · exact Or.inl ⟨⟨source, hzero⟩, h, rfl⟩
      · exact Or.inr (Set.mem_iUnion.mpr ⟨s, ⟨⟨source, hs⟩, h, rfl⟩⟩)
    · rintro (⟨source, hs, rfl⟩ | h)
      · exact hs
      · obtain ⟨s, source, hs, rfl⟩ := Set.mem_iUnion.mp h
        exact hs
  rw [heq]
  have hz : Measurable (fun source : emptySet =>
      collectionCallCalendar rate rewards C_star C_h source.val) := by
    have heq : (fun source : emptySet =>
        collectionCallCalendar rate rewards C_star C_h source.val) = fun _ => [] :=
      funext (fun source => hempty source.val source.property)
    rw [heq]
    exact measurable_const
  exact (MeasurableSet.subtype_image hemptySet (hz htarget)).union
    (MeasurableSet.iUnion (fun s => MeasurableSet.subtype_image
      (ReferenceGeneratedDownAmbiguityMeasurability.measurableSet_generatedLaunchFiberSet
        (rate := rate) rewards C_star C_h s.val) (hfiber s htarget)))

private theorem measurableSet_option_none {A : Type*} [MeasurableSpace A] :
    MeasurableSet ({none} : Set (Option A)) := by
  change MeasurableSet[
    (inferInstance : MeasurableSpace (A ⊕ PUnit)).comap
      (Equiv.optionEquivSumPUnit A)] {none}
  rw [MeasurableSpace.measurableSet_comap]
  refine ⟨Set.range (Sum.inr : PUnit → A ⊕ PUnit), measurableSet_range_inr, ?_⟩
  ext o
  cases o <;> simp

private theorem measurableSet_option_some {A : Type*} [MeasurableSpace A]
    (s : Set A) (hs : MeasurableSet s) : MeasurableSet (some '' s : Set (Option A)) := by
  change MeasurableSet[
    (inferInstance : MeasurableSpace (A ⊕ PUnit)).comap
      (Equiv.optionEquivSumPUnit A)] (some '' s)
  rw [MeasurableSpace.measurableSet_comap]
  refine ⟨Sum.inl '' s, measurableSet_inl_image.mpr hs, ?_⟩
  ext o
  cases o <;> simp

private def indexedCall {A B : Type*} (f : A → Option B) (l : List A) (n : ℕ) : Option B :=
  l[n]?.bind f

private theorem measurable_indexedCall {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (f : A → Option B) (hf : Measurable f) (n : ℕ) :
    Measurable (fun l : List A => indexedCall f l n) := by
  have heq : (fun l : List A => indexedCall f l n) = fun l =>
      Sum.elim (fun _ : Unit => (none : Option B)) f
        (ReferenceActiveHorizonMeasurability.listObservationAt l n) := by
    funext l
    unfold indexedCall ReferenceActiveHorizonMeasurability.listObservationAt
    cases l[n]? <;> rfl
  rw [heq]
  exact ((measurable_const : Measurable (fun _ : Unit => (none : Option B))).sumElim hf).comp
    ((measurable_pi_apply n).comp
      (measurable_snd.comp ReferenceActiveHorizonMeasurability.measurable_listObservationCoordinates))

-- The existing list sigma algebra keeps length and every indexed sum-tagged
-- entry. First-present search is Borel in this space; no element space is
-- replaced by a discrete sigma algebra.
private theorem measurable_list_findSome? {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B] (f : A → Option B) (hf : Measurable f) :
    Measurable (fun l : List A => l.findSome? f) := by
  have hzero (n : ℕ) : MeasurableSet {l : List A | indexedCall f l n = none} :=
    (measurable_indexedCall f hf n) measurableSet_option_none
  have hall : MeasurableSet {l : List A | ∀ n, indexedCall f l n = none} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter hzero
  have hbefore (n : ℕ) :
      MeasurableSet {l : List A | ∀ j < n, indexedCall f l j = none} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter (fun j => MeasurableSet.iInter (fun _ => hzero j))
  have hnone (l : List A) :
      l.findSome? f = none ↔ ∀ n, indexedCall f l n = none := by
    rw [List.findSome?_eq_none_iff]
    exact (bind_getElem?_none_iff l f).symm
  intro target htarget
  have heq : (fun l : List A => l.findSome? f) ⁻¹' target =
      {l | (none : Option B) ∈ target ∧ ∀ n, indexedCall f l n = none} ∪
      ⋃ n : ℕ, {l | indexedCall f l n ∈ target ∧ indexedCall f l n ≠ none ∧
        ∀ j < n, indexedCall f l j = none} := by
    ext l
    simp only [Set.mem_preimage, Set.mem_union, Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · intro hmem
      cases hfind : l.findSome? f with
      | none => exact Or.inl ⟨hfind ▸ hmem, (hnone l).1 hfind⟩
      | some b =>
          obtain ⟨n, hn, hearlier⟩ := (findSome?_eq_some_index f l b).1 hfind
          refine Or.inr ⟨n, ?_, ?_, hearlier⟩
          · simpa only [indexedCall, hn, hfind] using hmem
          · simp only [indexedCall, hn, ne_eq, reduceCtorEq, not_false_eq_true]
    · rintro (⟨hmem, hnone'⟩ | ⟨n, hmem, hsome, hearlier⟩)
      · simpa only [(hnone l).2 hnone'] using hmem
      · cases hcurrent : indexedCall f l n with
        | none => exact (hsome hcurrent).elim
        | some b =>
            have hfind := (findSome?_eq_some_index f l b).2 ⟨n, hcurrent, hearlier⟩
            simpa only [hfind, hcurrent] using hmem
  rw [heq]
  exact ((MeasurableSet.const _).inter hall).union
    (MeasurableSet.iUnion (fun n =>
      (measurable_indexedCall f hf n htarget).inter ((hzero n).compl.inter (hbefore n))))

/-- The cell permutation retains the continuous parameter and is Borel. -/
theorem measurable_callInCell : Measurable (callInCell (p := p)) := by
  exact measurable_optionMapWith Prod.fst measurable_fst Prod.snd measurable_snd
    (fun z : Fin p.T × (Fin p.T × Theta p) => (z.2.1, (z.1, z.2.2)))
    ((measurable_fst.comp measurable_snd).prodMk
      (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))

/-- Joint Borel measurability of the first actual later-sampler call on the
whole original source, including all empty and failure paths. -/
theorem measurable_firstCollectionCall
    (rate : RateInput p) (rewards : Rewards p) (C_star C_h : ℝ) :
    Measurable (firstCollectionCall rate rewards C_star C_h) :=
  (measurable_list_findSome? callInCell measurable_callInCell).comp
    (measurable_collectionCallCalendar rate rewards C_star C_h)

/-- Each actual cutoff/time cell is Borel, with the continuous parameter
projected only after selecting the first actual invocation. -/
theorem measurableSet_firstCollectionCall_cell
    (rate : RateInput p) (rewards : Rewards p) (C_star C_h : ℝ) (u t : Fin p.T) :
    MeasurableSet {source : SourceInput p |
      (firstCollectionCall rate rewards C_star C_h source).map (fun c => (c.1, c.2.1)) =
        some (u, t)} := by
  have hmap := LaterAssignmentFullOutputMeasurability.measurable_optionMap
    (fun c : Call p => (c.1, c.2.1))
    (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
    (firstCollectionCall rate rewards C_star C_h)
    (measurable_firstCollectionCall rate rewards C_star C_h)
  have hs := measurableSet_option_some ({(u, t)} : Set (Fin p.T × Fin p.T))
    (measurableSet_singleton _)
  simpa only [Set.image_singleton, Set.preimage_singleton] using hmap hs

/-- The actual no-invocation event is Borel. -/
theorem measurableSet_firstCollectionCall_none
    (rate : RateInput p) (rewards : Rewards p) (C_star C_h : ℝ) :
    MeasurableSet {source : SourceInput p |
      firstCollectionCall rate rewards C_star C_h source = none} :=
  (measurable_firstCollectionCall rate rewards C_star C_h) measurableSet_option_none

/-- Input equality is only required for the actual pre-state and timestamp;
whole row-bearing records are not asserted equal. -/
theorem collectionCallOnInput_eq_of_state_eq_time_eq
    (x y : ReferenceActivePhysicalStep.RoundInput p rate)
    (hstate : x.state = y.state) (htime : x.time = y.time) :
    collectionCallOnInput x = collectionCallOnInput y := by
  have hp := ReferenceLaterSamplerParameterMeasurability.parameters?_eq_of_state_eq_time_eq
    x y hstate htime
  unfold collectionCallOnInput
  rw [hstate, hp]

private theorem calendar_eq_of_records_evidence_eq
    (left right : List (RoundRecord p rate))
    (hevidence : left.map ReferenceActivePhysicalHorizon.RoundRecord.evidence =
      right.map ReferenceActivePhysicalHorizon.RoundRecord.evidence) :
    left.map (fun r => (r.input.time, collectionCallAt r)) =
      right.map (fun r => (r.input.time, collectionCallAt r)) := by
  induction left generalizing right with
  | nil =>
      cases right <;> simp_all
  | cons a left ih =>
      cases right with
      | nil => simp at hevidence
      | cons b right =>
          simp only [List.map_cons, List.cons.injEq] at hevidence
          have hstate := congrArg ReferenceActivePhysicalHorizon.RoundEvidence.before hevidence.1
          have htime := congrArg ReferenceActivePhysicalHorizon.RoundEvidence.time hevidence.1
          have hcall := collectionCallOnInput_eq_of_state_eq_time_eq a.input b.input hstate htime
          exact congrArg₂ List.cons (Prod.ext htime hcall) (ih right hevidence.2)

/-- Conditional comparison helper: equality of the actual complete evidence
implies equality of this observation. The AE theorem below produces its input
from F on the same source path. -/
theorem collectionCallCalendar_eq_of_evidence_eq (rewards : Rewards p) (C_star C_h : ℝ)
    (source source' : SourceInput p)
    (hevidence : ReferenceCompletePhysicalHistory.completeSuffixEvidence
      rate source rewards C_star C_h = ReferenceCompletePhysicalHistory.completeSuffixEvidence
        rate source' rewards C_star C_h) :
    collectionCallCalendar rate rewards C_star C_h source =
      collectionCallCalendar rate rewards C_star C_h source' :=
  calendar_eq_of_records_evidence_eq _ _ hevidence

/-- Joint preservation along the admitted finite source path, using complete
physical evidence rather than two marginal-law identities. -/
theorem ae_finiteSourcePathLaw_collectionCallCalendar
    (rate : RateInput p) (rewards : Rewards p) (C_star C_h : ℝ)
    (control0 : ContinuousLearningRows.TimeControl p) (k : ℕ) (hk : k ≤ p.T) :
    ∀ᵐ path ∂ReferenceFiniteSourcePath.finiteSourcePathLaw
      rate rewards C_star C_h control0 k hk,
      ∀ a b : Fin (k + 1), a.val ≤ b.val →
        collectionCallCalendar rate rewards C_star C_h (path a) =
          collectionCallCalendar rate rewards C_star C_h (path b) := by
  filter_upwards [ReferenceFiniteSourcePath.ae_finiteSourcePathLaw_complete
    rate rewards C_star C_h control0 k hk] with path hpath
  intro a b hab
  exact collectionCallCalendar_eq_of_evidence_eq rewards C_star C_h
    (path a) (path b) (hpath a b hab).2.1

/-- The first actual invocation is preserved on the same joint AE path. -/
theorem ae_finiteSourcePathLaw_firstCollectionCall
    (rate : RateInput p) (rewards : Rewards p) (C_star C_h : ℝ)
    (control0 : ContinuousLearningRows.TimeControl p) (k : ℕ) (hk : k ≤ p.T) :
    ∀ᵐ path ∂ReferenceFiniteSourcePath.finiteSourcePathLaw
      rate rewards C_star C_h control0 k hk,
      ∀ a b : Fin (k + 1), a.val ≤ b.val →
        firstCollectionCall rate rewards C_star C_h (path a) =
          firstCollectionCall rate rewards C_star C_h (path b) := by
  filter_upwards [ae_finiteSourcePathLaw_collectionCallCalendar
    rate rewards C_star C_h control0 k hk] with path hpath
  intro a b hab
  exact congrArg (fun calendar => calendar.findSome? callInCell) (hpath a b hab)

end Bandits.Support.ReferenceFirstCollectionSamplerCall

end
