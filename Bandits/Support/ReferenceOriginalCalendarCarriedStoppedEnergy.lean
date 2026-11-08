/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceOriginalNumericalFirstOverflowLocator

import Mathlib.Tactic

/-!
# Calendar energy from the latest actual optional readout

This internal observation construction carries the last genuinely observed
original-prefix queue across absent readouts. It does not identify the
observation event with a physical event or add a recorder law.
-/

@[expose] public section

noncomputable section

open MeasureTheory Bandits.Support ConstructorDimensions
open BootstrapPrivateRoundStreams (SourceInput sourceInputLaw)
open ReferenceSourcePrefixHistoryFiltration (actualLaunchBy actualRecord)
open ReferenceFirstCollectionRenewalIncomingQueueMeasurability (stateReadout)
open scoped Classical

namespace Bandits.Support.ReferenceOriginalCalendarCarriedStoppedEnergy

variable {p : Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ)

local notation "X" => SourceInput p
local notation "Q" => ReferenceFirstLaunchNumericalCell.queueParameters rate
local notation "Input" => RecordedQueueRun.RoundInput p.K
local notation "Readout" => ReferenceFirstCollectionCurrentQueueReadout.QueueReadout p.K
local notation "P" => ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout
  rate rewards C_star C_h
local notation "PI" => ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
  rate rewards C_star C_h

private instance sourceSumMeasurableSingleton {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β] :
    MeasurableSingletonClass (α ⊕ β) where
  measurableSet_singleton x := by
    cases x with
    | inl a =>
        simpa only [Set.image_singleton] using
          (MeasurableSet.singleton a).inl_image
    | inr b =>
        simpa only [Set.image_singleton] using
          (MeasurableSet.singleton b).inr_image

private instance sourceRecordListMeasurableSingleton :
    MeasurableSingletonClass (List (Bool × ℕ)) where
  measurableSet_singleton l := by
    let : MeasurableSingletonClass (Unit ⊕ (Bool × ℕ)) := ⟨fun x => by
      cases x with
      | inl a =>
          simpa only [Set.image_singleton] using
            (MeasurableSet.singleton a).inl_image
      | inr a =>
          simpa only [Set.image_singleton] using
            (MeasurableSet.singleton a).inr_image⟩
    have hinj : Function.Injective
        (ReferenceActiveHorizonMeasurability.listObservationCoordinates
          (α := Bool × ℕ)) := by
      intro a b h
      have hlen : a.length = b.length := congrArg Prod.fst h
      apply List.ext_getElem hlen
      intro i hi hj
      have he := congrFun (congrArg Prod.snd h) i
      simpa only [ReferenceActiveHorizonMeasurability.listObservationCoordinates,
        ReferenceActiveHorizonMeasurability.listObservationAt,
        List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj,
        Sum.inr.injEq] using he
    have hm := ReferenceActiveHorizonMeasurability.measurable_listObservationCoordinates
      (α := Bool × ℕ)
    have hh := hm (MeasurableSet.singleton
      (ReferenceActiveHorizonMeasurability.listObservationCoordinates l))
    convert hh using 1
    ext x
    simp only [Set.mem_singleton_iff, Set.mem_preimage, hinj.eq_iff]

private instance finitePiMeasurableSingleton {ι α : Type*} [Finite ι]
    [MeasurableSpace α] [MeasurableSingletonClass α] :
    MeasurableSingletonClass (ι → α) := by
  refine ⟨fun x => ?_⟩
  have heq : Set.univ.pi (fun i : ι => {x i}) = {x} := by
    ext y
    simp only [Set.mem_pi, Set.mem_univ, Set.mem_singleton_iff]
    constructor
    · intro hy
      exact funext (fun i => hy i trivial)
    · intro h i _
      exact congrFun h i
  rw [← heq]
  exact MeasurableSet.univ_pi (fun i => MeasurableSet.singleton (x i))

/-- Carry the last actual optional readout; absence preserves the observation. -/
public def carriedPrefixReadout : ℕ → X → Option Readout
  | 0, z => P 0 z
  | n + 1, z =>
      (P (n + 1) z).or
        (carriedPrefixReadout n z)

/-- The recursion retains a present current readout verbatim. -/
@[simp] public theorem carriedPrefixReadout_succ_present (n : ℕ) (z : X)
    (o : Readout)
    (h : P (n + 1) z = some o) :
    carriedPrefixReadout rate rewards C_star C_h (n + 1) z = some o := by
  simp [carriedPrefixReadout, h]

/-- The recursion carries its previous value across a missing readout. -/
@[simp] public theorem carriedPrefixReadout_succ_absent (n : ℕ) (z : X)
    (h : P (n + 1) z = none) :
    carriedPrefixReadout rate rewards C_star C_h (n + 1) z =
      carriedPrefixReadout rate rewards C_star C_h n z := by
  simp [carriedPrefixReadout, h]

/-- A carried value is the last present original-prefix readout through its
date. The quantified absence condition makes the witness date the latest one. -/
public theorem carriedPrefixReadout_eq_some_iff (n : ℕ) (z : X) (o : Readout) :
    carriedPrefixReadout rate rewards C_star C_h n z = some o ↔
      ∃ k ≤ n,
        P k z = some o ∧
        ∀ j, k < j → j ≤ n → P j z = none := by
  induction n with
  | zero =>
      constructor
      · intro h
        refine ⟨0, le_rfl, h, ?_⟩
        intro j hj hj0
        omega
      · rintro ⟨k, hk, hread, _⟩
        have hk0 : k = 0 := by omega
        simpa [carriedPrefixReadout, hk0] using hread
  | succ n ih =>
      by_cases hp : P (n + 1) z = none
      · rw [carriedPrefixReadout_succ_absent rate rewards C_star C_h n z hp, ih]
        constructor
        · rintro ⟨k, hk, hread, hlast⟩
          refine ⟨k, Nat.le_succ_of_le hk, hread, ?_⟩
          intro j hkj hj
          by_cases hjs : j = n + 1
          · simpa [hjs] using hp
          · exact hlast j hkj (by omega)
        · rintro ⟨k, hk, hread, hlast⟩
          have hk' : k ≤ n := by
            by_contra hkn
            have hkeq : k = n + 1 := by omega
            subst k
            rw [hp] at hread
            cases hread
          refine ⟨k, hk', hread, ?_⟩
          intro j hkj hj
          by_cases hjs : j = n + 1
          · simpa [hjs] using hp
          · exact hlast j hkj (by omega)
      · cases hcur : P (n + 1) z with
        | none => exact (hp hcur).elim
        | some o' =>
          simp only [carriedPrefixReadout, hcur, Option.some_or]
          constructor
          · intro heq
            have hoo : o' = o := Option.some.inj heq
            subst o'
            refine ⟨n + 1, le_rfl, hcur, ?_⟩
            intro j hkj hj
            have : False := by omega
            exact this.elim
          · rintro ⟨k, hk, hread, hlast⟩
            have hkn : k = n + 1 := by
              by_contra hne
              have hknle : k ≤ n := by omega
              have hnone := hlast (n + 1) (by omega) le_rfl
              rw [hcur] at hnone
              cases hnone
            subst k
            have hoo : o' = o := Option.some.inj (hcur.symm.trans hread)
            subst o'
            rfl

/-- Every carried observation has genuine original-prefix provenance. -/
public theorem carriedPrefixReadout_provenance (n : ℕ) (z : X) (o : Readout)
    (h : carriedPrefixReadout rate rewards C_star C_h n z = some o) :
    ∃ k ≤ n, P k z = some o := by
  obtain ⟨k, hk, hread, _⟩ :=
    (carriedPrefixReadout_eq_some_iff rate rewards C_star C_h n z o).mp h
  exact ⟨k, hk, hread⟩

private theorem mapM_id_eq_map_some {α : Type*} :
    ∀ {slots : List (Option α)} {cells : List α},
      slots.mapM id = some cells → slots = cells.map some := by
  intro slots
  induction slots with
  | nil =>
      intro cells h
      cases cells <;> simp [List.mapM_nil] at h ⊢
  | cons slot slots ih =>
      intro cells h
      cases slot with
      | none => simp [List.mapM_cons] at h
      | some cell =>
          cases ht : slots.mapM id with
          | none => simp [List.mapM_cons, ht] at h
          | some tail =>
              have hc : cell :: tail = cells := by
                simpa [List.mapM_cons, ht] using h
              cases hc
              have htail := ih ht
              simp [htail]

private theorem mapM_id_map_some {α : Type*} (cells : List α) :
    (cells.map some).mapM id = some cells := by
  induction cells with
  | nil => rfl
  | cons cell cells ih => simp [List.mapM_cons, ih]

/-- The one actual optional current cell in the original source at date `q`. -/
public def actualCellAt (q : Fin p.T) (z : X) : Option Input :=
  (actualRecord rate rewards C_star C_h q z).bind
    (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate)

/-- A successful optional prefix contains the mapped source slots with no
absence erased. -/
private theorem prefixInputs_slots (n : ℕ) (z : X) (L : List Input)
    (hnT : n ≤ p.T)
    (hL : PI n z = some L) :
    ((ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords
      rate rewards C_star C_h z).take
      (n - ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart
        rate rewards C_star C_h z)).map
      (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate) = L.map some := by
  have hlaunch :=
    ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs_launch
      rate rewards C_star C_h n z L hL
  have hlenR := ReferenceCompletePhysicalHistory.completeSuffixRecords_length
    rate z rewards C_star C_h
  have hlenR' :
      (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords
        rate rewards C_star C_h z).length =
        p.T - ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart
          rate rewards C_star C_h z := by
    simpa only [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords,
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart] using hlenR
  have htakeN : n - ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart
      rate rewards C_star C_h z ≤
      (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords
        rate rewards C_star C_h z).length := by
    rw [hlenR']
    omega
  have hmap : ((((ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords
      rate rewards C_star C_h z).take
      (n - ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart
        rate rewards C_star C_h z)).map
      (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate)).mapM id) = some L := by
    simpa only [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs,
      ite_eq_left hlaunch] using hL
  exact mapM_id_eq_map_some hmap

private theorem take_map_eq_rangeLookup {α β : Type*} (f : α → Option β)
    (R : List α) (n : ℕ) (hn : n ≤ R.length) :
    (R.take n).map f = (List.range n).map
      (fun i => (R[i]?).bind f) := by
  induction n generalizing R with
  | zero => simp
  | succ n ih =>
      cases R with
      | nil => simp at hn
      | cons x xs =>
          have hn' : n ≤ xs.length := by simp at hn; omega
          simp [List.range_succ_eq_map, ih xs hn']

/-- The original numerical prefix is the existing strict-past retained-gate
readout at the same literal date. This is established from source-list lookup
and complete-suffix lengths. -/
private theorem prefixReadout_eq_currentRetainedGate (t : Fin p.T) (z : X) :
    P t.val z = ReferenceFirstCollectionCurrentRetainedGate.prefixReadout?
      rate rewards C_star C_h t z := by
  by_cases hlaunch : actualLaunchBy rate rewards C_star C_h t.val z
  · have hs : ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart
        rate rewards C_star C_h z ≤ t.val := hlaunch.2
    let R := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords
      rate rewards C_star C_h z
    let n := t.val - ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart
      rate rewards C_star C_h z
    have hlenR : R.length = p.T -
        ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart
          rate rewards C_star C_h z := by
      simpa only [R, ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords,
        ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart] using
        ReferenceCompletePhysicalHistory.completeSuffixRecords_length
          rate z rewards C_star C_h
    have hnR : n ≤ R.length := by rw [hlenR]; dsimp [n]; omega
    have hslots : (R.take n).map
        (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate) =
        ReferenceFirstCollectionCurrentRetainedGate.pastSlots
          rate rewards C_star C_h t z := by
      dsimp [ReferenceFirstCollectionCurrentRetainedGate.pastSlots, R, n,
        ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords,
        ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart]
      exact take_map_eq_rangeLookup
        (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate)
        (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)
        (t.val - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
        (by rw [ReferenceCompletePhysicalHistory.completeSuffixRecords_length]; omega)
    have hinputs : PI t.val z =
        ReferenceFirstCollectionCurrentRetainedGate.pastCells?
          rate rewards C_star C_h t z := by
      simp only [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs,
        ReferenceFirstCollectionCurrentRetainedGate.pastCells?, ite_eq_left hlaunch,
        ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords,
        ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart]
      change (((R.take n).map (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate)).mapM id) =
        ((ReferenceFirstCollectionCurrentRetainedGate.pastSlots
          rate rewards C_star C_h t z).mapM id)
      rw [hslots]
    simp only [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout,
      ReferenceFirstCollectionCurrentRetainedGate.prefixReadout?, hinputs]
  · simp [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout,
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs,
      ReferenceFirstCollectionCurrentRetainedGate.prefixReadout?,
      ReferenceFirstCollectionCurrentRetainedGate.pastCells?, hlaunch]

/-- Every shorter date at or after launch is a true prefix of a present later
readout. This reconstructs the public consequence here instead of calling the
locator's private helper. -/
private theorem prefixInputs_from_present_full (n k : ℕ) (z : X)
    (hnT : n ≤ p.T)
    (hsk : ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart
      rate rewards C_star C_h z ≤ k)
    (hkn : k ≤ n) (L : List Input) (hL : PI n z = some L) :
    ∃ Lk : List Input,
      PI k z = some Lk ∧
      Lk = L.take (k - ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart
        rate rewards C_star C_h z) ∧
      Lk.length = k - ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart
        rate rewards C_star C_h z := by
  let s := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart
    rate rewards C_star C_h z
  let R := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords
    rate rewards C_star C_h z
  have hlaunch :=
    ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs_launch
      rate rewards C_star C_h n z L hL
  have hslots := prefixInputs_slots rate rewards C_star C_h n z L hnT hL
  have hlenR := ReferenceCompletePhysicalHistory.completeSuffixRecords_length
    rate z rewards C_star C_h
  have hlenR' : R.length = p.T - s := by
    simpa only [R, s, ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords,
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart] using hlenR
  have htakeN : n - s ≤ R.length := by rw [hlenR']; omega
  have hLlength : L.length = n - s := by
    have hlen := congrArg List.length hslots
    simp only [List.length_map] at hlen
    rw [List.length_take, Nat.min_eq_left htakeN] at hlen
    exact hlen.symm
  have hkslot : (R.take (k - s)).map
      (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate) =
        ((R.take (n - s)).map
          (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate)).take (k - s) := by
    let f := ReferenceFirstCollectionCurrentRetainedGate.cell0 rate
    calc
      (R.take (k - s)).map f = (R.take (min (k - s) (n - s))).map f := by
        rw [Nat.min_eq_left (by omega)]
      _ = ((R.take (n - s)).map f).take (k - s) := by
        rw [← List.map_take, List.take_take]
  have hmapK : ((R.take (k - s)).map
      (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate)).mapM id =
        some (L.take (k - s)) := by
    rw [hkslot, hslots]
    simpa only [List.map_take] using mapM_id_map_some (L.take (k - s))
  have hlaunchK : actualLaunchBy rate rewards C_star C_h k z :=
    ⟨hlaunch.1, hsk⟩
  have hprefixK : PI k z = some (L.take (k - s)) := by
    simpa only [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs,
      ite_eq_left hlaunchK, R, s, ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords,
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart] using hmapK
  refine ⟨L.take (k - s), hprefixK, rfl, ?_⟩
  rw [List.length_take, Nat.min_eq_left (by rw [hLlength]; omega)]

/-- Once the actual launch has occurred, an absent original prefix cannot
reappear at a later date: any later present `mapM` prefix has the earlier
literal input list as a prefix. -/
public theorem prefixReadout_none_persists_after_launch (q m : ℕ) (z : X)
    (hqm : q ≤ m) (hmT : m ≤ p.T)
    (hlaunch : actualLaunchBy rate rewards C_star C_h q z)
    (hnone : P q z = none) : P m z = none := by
  by_contra hnot
  cases hmread : P m z with
  | none => exact hnot hmread
  | some o =>
      have hinputsM : ∃ L, PI m z = some L := by
        unfold ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout at hmread
        cases h : PI m z with
        | none => simp [h] at hmread
        | some L => exact ⟨L, rfl⟩
      obtain ⟨L, hL⟩ := hinputsM
      obtain ⟨Lq, hLq, _, _⟩ := prefixInputs_from_present_full
        rate rewards C_star C_h m q z hmT hlaunch.2 hqm L hL
      have hPq : P q z = some (stateReadout (RecordedQueueRun.run Q Lq)) := by
        simp [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout, hLq]
      rw [hnone] at hPq
      cases hPq

/-- An absence from a post-launch date onward leaves the last real
observation carried unchanged, including through the terminal date. -/
public theorem carriedPrefixReadout_preserved_after_absence (q m : ℕ) (z : X)
    (hqm : q ≤ m) (hmT : m ≤ p.T)
    (hlaunch : actualLaunchBy rate rewards C_star C_h q z)
    (hnone : P q z = none) :
    carriedPrefixReadout rate rewards C_star C_h m z =
      carriedPrefixReadout rate rewards C_star C_h q z := by
  have hstep : ∀ d, q + d ≤ p.T →
      carriedPrefixReadout rate rewards C_star C_h (q + d) z =
        carriedPrefixReadout rate rewards C_star C_h q z := by
    intro d
    induction d with
    | zero => simp
    | succ d ih =>
        intro hd
        have hprev : q + d ≤ p.T := by omega
        have hp : P (q + d + 1) z = none := by
          apply prefixReadout_none_persists_after_launch rate rewards C_star C_h
            q (q + d + 1) z (by omega) hd hlaunch hnone
        rw [show q + (d + 1) = q + d + 1 by omega]
        rw [carriedPrefixReadout_succ_absent rate rewards C_star C_h (q + d) z
          (by simpa [Nat.add_assoc] using hp)]
        exact ih hprev
  have := hstep (m - q) (by omega)
  simpa [Nat.add_sub_of_le hqm] using this

/-- Literal full-calendar lookup of the physical record occupying a source
date, with its actual time recovered from the complete suffix list. -/
private theorem sourceRecord_at_date (z : X) (s t : ℕ)
    (hs : s = ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart
      rate rewards C_star C_h z)
    (hst : s ≤ t) (htT : t < p.T) :
    ∃ r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate),
      (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords
        rate rewards C_star C_h z)[t - s]? = some r ∧ r.input.time.val = t := by
  let R := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords
    rate rewards C_star C_h z
  have hlen := ReferenceCompletePhysicalHistory.completeSuffixRecords_length
    rate z rewards C_star C_h
  have hlenR : R.length = p.T - s := by
    simpa only [R, ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords,
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart, hs] using hlen
  have hi : t - s < R.length := by rw [hlenR]; omega
  have htimeMap := ReferenceCompletePhysicalHistory.completeSuffixRecords_time_values
    rate z rewards C_star C_h
  have htime : R.map (fun r => r.input.time.val) =
      ReferenceActivePhysicalHorizon.calendar s (p.T - s) := by
    simpa only [R, ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords,
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart, hs] using htimeMap
  let r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) :=
    R[t - s]
  have hr : R[t - s]? = some r := List.getElem?_eq_getElem hi
  have hiCal : t - s < (ReferenceActivePhysicalHorizon.calendar s (p.T - s)).length := by
    rw [ReferenceActivePhysicalHorizon.calendar, List.length_range']
    omega
  have htimeLookup := congrArg (fun xs : List ℕ => xs[t - s]?) htime
  rw [List.getElem?_map, hr] at htimeLookup
  rw [List.getElem?_eq_getElem hiCal] at htimeLookup
  have htimeRange :
      (ReferenceActivePhysicalHorizon.calendar s (p.T - s))[t - s] = s + (t - s) := by
    simp only [ReferenceActivePhysicalHorizon.calendar,
      List.getElem_range'_1]
  rw [htimeRange] at htimeLookup
  have htimeValue : r.input.time.val = s + (t - s) :=
    Option.some.inj htimeLookup
  refine ⟨r, ?_, ?_⟩
  · simpa only [R, r] using hr
  · omega

/-- A present original cell appends the same actual cell to the existing
optional prefix and runs the same initialized queue. -/
private theorem prefixInputs_append_actualCell (q : Fin p.T) (z : X)
    (L : List Input) (hL : PI q.val z = some L) (c : Input)
    (hc : actualCellAt rate rewards C_star C_h q z = some c) :
    PI (q.val + 1) z = some (L ++ [c]) := by
  obtain ⟨r, hr, hcell⟩ := Option.bind_eq_some_iff.mp hc
  have hlaunch :=
    ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs_launch
      rate rewards C_star C_h q.val z L hL
  have hstart : ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart
      rate rewards C_star C_h z ≤ q.val := hlaunch.2
  have hphysical : ReferenceCompletePhysicalHistory.physicalStart
      rate z rewards C_star C_h ≤ q.val := by
    simpa only [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart] using hstart
  have hlookup :
      (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords
        rate rewards C_star C_h z)[q.val -
          ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart
            rate rewards C_star C_h z]? = some r := by
    rw [ReferenceSourcePrefixHistoryFiltration.actualRecord, ite_eq_left hphysical] at hr
    simpa only [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords,
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart] using hr
  exact ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs_append_one
    rate rewards C_star C_h q.val z L hL r c hlookup hcell

/-- If both adjacent optional prefixes are present, the later one contains
the actual current cell at its literal calendar index. -/
private theorem present_successor_has_actual_cell (q : Fin p.T) (z : X)
    (L N : List Input) (hL : PI q.val z = some L)
    (hN : PI (q.val + 1) z = some N) :
    ∃ c, actualCellAt rate rewards C_star C_h q z = some c ∧
      PI (q.val + 1) z = some (L ++ [c]) := by
  have hlaunch :=
    ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs_launch
      rate rewards C_star C_h q.val z L hL
  have hs : ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart
      rate rewards C_star C_h z ≤ q.val := hlaunch.2
  let s := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart
    rate rewards C_star C_h z
  let R := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords
    rate rewards C_star C_h z
  obtain ⟨r, hr, htime⟩ := sourceRecord_at_date rate rewards C_star C_h z s q.val rfl hs q.isLt
  have hslots := prefixInputs_slots rate rewards C_star C_h (q.val + 1) z N
    (by omega) hN
  have hlen := ReferenceCompletePhysicalHistory.completeSuffixRecords_length
    rate z rewards C_star C_h
  have hlenR : R.length = p.T - s := by
    simpa only [R, s, ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords,
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart] using hlen
  have htake : q.val + 1 - s ≤ R.length := by rw [hlenR]; omega
  have hi : q.val - s < (R.take (q.val + 1 - s)).length := by
    rw [List.length_take, Nat.min_eq_left htake]
    omega
  have hri : R[q.val - s]? = some r := by simpa only [R, s] using hr
  have hrval : R[q.val - s] = r := (List.getElem?_eq_some_iff.mp hri).2
  have hrTake : (R.take (q.val + 1 - s))[q.val - s] = r := by
    simpa only [List.getElem_take] using hrval
  have hslot : ((R.take (q.val + 1 - s)).map
      (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate))[q.val - s]? =
        some (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r) := by
    rw [List.getElem?_map]
    have hrTake? : (R.take (q.val + 1 - s))[q.val - s]? = some r :=
      (List.getElem?_eq_getElem hi).trans (congrArg some hrTake)
    rw [hrTake?]
    rfl
  have hslotN := congrArg (fun xs : List (Option Input) => xs[q.val - s]?) hslots
  rw [hslot] at hslotN
  have hslotN' : some (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r) =
      Option.map some (N[q.val - s]?) := by
    simpa only [List.getElem?_map] using hslotN
  cases hNi : N[q.val - s]? with
  | none => simp [hNi] at hslotN'
  | some c =>
      have hcell : ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r = some c := by
        rw [hNi, Option.map_some] at hslotN'
        exact Option.some.inj hslotN'
      have hphysical : ReferenceCompletePhysicalHistory.physicalStart
          rate z rewards C_star C_h ≤ q.val := by
        simpa only [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart] using hs
      have hrecord : actualRecord rate rewards C_star C_h q z = some r := by
        rw [ReferenceSourcePrefixHistoryFiltration.actualRecord, ite_eq_left hphysical]
        simpa only [R, s,
          ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords,
          ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart] using hr
      have hc : actualCellAt rate rewards C_star C_h q z = some c := by
        simp [actualCellAt, hrecord, hcell]
      have happ := prefixInputs_append_actualCell rate rewards C_star C_h q z L hL c hc
      refine ⟨c, hc, happ⟩

/-- The carried observation is absent before the actual initialization launch. -/
public theorem carriedPrefixReadout_none_before_launch (n : ℕ) (z : X)
    (hn : n ≤ p.T)
    (hno : ¬ actualLaunchBy rate rewards C_star C_h n z) :
    carriedPrefixReadout rate rewards C_star C_h n z = none := by
  induction n with
  | zero =>
      change P 0 z = none
      unfold ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout
        ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
      simp [hno]
  | succ n ih =>
      have hno' : ¬ actualLaunchBy rate rewards C_star C_h n z := by
        intro h
        exact hno ⟨h.1, h.2.trans (Nat.le_succ _)⟩
      have hn' : n ≤ p.T := by omega
      have hp : P (n + 1) z = none := by
        unfold ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout
          ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
        simp [hno]
      rw [carriedPrefixReadout_succ_absent rate rewards C_star C_h n z hp]
      exact ih hn' hno'

/-- The dormant scalar is one and is not represented as a queue observation. -/
public def carriedStoppedEnergy (n : ℕ) (a : Fin p.K) (z : X) : ℝ :=
  match carriedPrefixReadout rate rewards C_star C_h n z with
  | none => 1
  | some o => Real.exp (CanonicalRecordingRates.beta p rate.eta.val *
      ((o.1 a).2 : ℝ) /
      ((ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ))

/-- The source threshold in normalized backlog units. -/
public def backlogCap : ℝ := 1 / (32 * rate.eta.val)

/-- The deterministic exponential envelope from the stopped-run backlog bound. -/
public def energyCeiling : ℝ :=
  Real.exp (CanonicalRecordingRates.beta p rate.eta.val * (2 * backlogCap rate))

/-- A retained, enabled non-overflow update of the literal original prefix. -/
public def activeUpdateAt (q : Fin p.T) (z : X) : Prop :=
  ∃ o c, P q.val z = some o ∧ actualCellAt rate rewards C_star C_h q z = some c ∧
    o.2.1 = false ∧ c.enabled = true

/-- The actual normalized quantized arrival minus service, extended by zero
off the active-update event. -/
public def normalizedArrivalIncrementAt (q : Fin p.T) (a : Fin p.K) (z : X) : ℝ :=
  if activeUpdateAt rate rewards C_star C_h q z then
    match actualCellAt rate rewards C_star C_h q z with
    | none => 0
    | some c => RecordedRoundMoments.normalizedQuantizedArrival Q c a - 4
  else 0

public theorem normalizedArrivalIncrementAt_eq (q : Fin p.T) (a : Fin p.K)
    (z : X) (c : Input) (hA : activeUpdateAt rate rewards C_star C_h q z)
    (hc : actualCellAt rate rewards C_star C_h q z = some c) :
    normalizedArrivalIncrementAt rate rewards C_star C_h q a z =
      RecordedRoundMoments.normalizedQuantizedArrival Q c a - 4 := by
  simp [normalizedArrivalIncrementAt, hA, hc]

@[simp] public theorem carriedStoppedEnergy_eq_one_of_none (n : ℕ)
    (a : Fin p.K) (z : X)
    (h : carriedPrefixReadout rate rewards C_star C_h n z = none) :
    carriedStoppedEnergy rate rewards C_star C_h n a z = 1 := by
  simp [carriedStoppedEnergy, h]

/-- At time zero the actual queue is empty, so the scalar energy starts at one. -/
public theorem carriedStoppedEnergy_zero (a : Fin p.K) (z : X) :
    carriedStoppedEnergy rate rewards C_star C_h 0 a z = 1 := by
  by_cases hp : P 0 z = none
  · simp [carriedStoppedEnergy, carriedPrefixReadout, hp]
  · cases hread : P 0 z with
    | none => exact (hp hread).elim
    | some o =>
        have hinputs : ∃ L, PI 0 z = some L := by
          unfold ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout at hread
          cases h : PI 0 z with
          | none => simp [h] at hread
          | some L => exact ⟨L, rfl⟩
        obtain ⟨L, hL⟩ := hinputs
        have hlaunch :=
          ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs_launch
            rate rewards C_star C_h 0 z L hL
        have hs : ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart
            rate rewards C_star C_h z = 0 := by
          unfold actualLaunchBy at hlaunch
          exact Nat.eq_zero_of_le_zero hlaunch.2
        have hinputs0 : PI 0 z = some [] := by
          change (if actualLaunchBy rate rewards C_star C_h 0 z then
            (((ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords
              rate rewards C_star C_h z).take
              (0 - ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart
                rate rewards C_star C_h z)).map
              (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate)).mapM id else none) =
                some []
          rw [ite_eq_left hlaunch]
          simp [hs]
        unfold carriedStoppedEnergy carriedPrefixReadout
        rw [hread]
        have ho : o = stateReadout (RecordedQueueRun.run Q []) := by
          unfold ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout at hread
          rw [hinputs0] at hread
          simp only [Option.map_some, Option.some.injEq] at hread
          exact hread.symm
        rw [ho]
        simp [stateReadout, RecordedQueueRun.run, RecordedQueueRun.execute,
          RecordedQueueRun.initialState]

/-- Before an actual launch the carried optional observation is absent and
the scalar remains the dormant energy one. -/
public theorem carriedStoppedEnergy_one_before_launch (n : ℕ) (z : X)
    (hn : n ≤ p.T)
    (hno : ¬ actualLaunchBy rate rewards C_star C_h n z) (a : Fin p.K) :
    carriedStoppedEnergy rate rewards C_star C_h n a z = 1 := by
  exact carriedStoppedEnergy_eq_one_of_none rate rewards C_star C_h n a z
    (carriedPrefixReadout_none_before_launch rate rewards C_star C_h n z hn hno)

/-- The actual launch boundary initializes the carried queue once from the
source's genuine zero-length prefix. -/
public theorem carriedStoppedEnergy_sourceStart (z : X) (a : Fin p.K)
    (hcross : (ReferenceCompletePhysicalHistory.generatedBoundary rate z rewards
      C_star C_h).crossing.isSome = true) :
    carriedStoppedEnergy rate rewards C_star C_h
      (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart
        rate rewards C_star C_h z) a z = 1 := by
  let s := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart
    rate rewards C_star C_h z
  have hlaunch : actualLaunchBy rate rewards C_star C_h s z := by
    exact ⟨hcross, by simp [s,
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart]⟩
  have hinputs : PI s z = some [] := by
    unfold ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
    rw [ite_eq_left hlaunch]
    simp [s]
  have hP : P s z = some (stateReadout (RecordedQueueRun.run Q [])) := by
    simp [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout, hinputs]
  have hcarry : carriedPrefixReadout rate rewards C_star C_h s z =
      some (stateReadout (RecordedQueueRun.run Q [])) := by
    dsimp only [s]
    have hP' := hP
    dsimp only [s] at hP'
    cases hs : ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart
        rate rewards C_star C_h z with
    | zero =>
        have hP0 : P 0 z = some (stateReadout (RecordedQueueRun.run Q [])) := by
          simpa only [hs] using hP'
        simpa [carriedPrefixReadout, hs] using hP0
    | succ n =>
        have hPn : P (n + 1) z = some (stateReadout (RecordedQueueRun.run Q [])) := by
          simpa only [hs, Nat.succ_eq_add_one] using hP'
        exact carriedPrefixReadout_succ_present rate rewards C_star C_h n z _ hPn
  simp [s, carriedStoppedEnergy, hcarry, stateReadout, RecordedQueueRun.run,
    RecordedQueueRun.execute, RecordedQueueRun.initialState]

/-- A present current readout initializes the carry at that exact readout. -/
public theorem carriedPrefixReadout_of_present (n : ℕ) (z : X) (o : Readout)
    (h : P n z = some o) :
    carriedPrefixReadout rate rewards C_star C_h n z = some o := by
  induction n with
  | zero => simpa [carriedPrefixReadout] using h
  | succ n ih => exact carriedPrefixReadout_succ_present rate rewards C_star C_h n z o h

/-- The actual readout of a present prefix is its unchanged initialized run
state projection. -/
private theorem prefixReadout_of_inputs (n : ℕ) (z : X) (L : List Input)
    (hL : PI n z = some L) :
    P n z = some (stateReadout (RecordedQueueRun.run Q L)) := by
  simp [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout, hL]

/-- A current-record append changes the readout by exactly one retained queue
step. The accepted-history coordinate may grow and is not equated separately. -/
private theorem prefixReadout_append_actualCell (q : Fin p.T) (z : X)
    (L : List Input) (hL : PI q.val z = some L) (c : Input)
    (hc : actualCellAt rate rewards C_star C_h q z = some c) :
    P (q.val + 1) z = some
      (stateReadout (RecordedQueueRun.step Q (RecordedQueueRun.run Q L) c)) := by
  have hinputs := prefixInputs_append_actualCell rate rewards C_star C_h q z L hL c hc
  simp only [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout,
    hinputs, Option.map_some]
  rw [ReferenceFirstCollectionRenewalFutureNumericalPrefix.run_append_one]

private theorem carriedStoppedEnergy_freeze_of_present_successor
    (q : Fin p.T) (a : Fin p.K) (z : X) (o onext : Readout)
    (hP : P q.val z = some o) (hPnext : P (q.val + 1) z = some onext)
    (hnotA : ¬ activeUpdateAt rate rewards C_star C_h q z) :
    carriedStoppedEnergy rate rewards C_star C_h (q.val + 1) a z =
      carriedStoppedEnergy rate rewards C_star C_h q.val a z := by
  obtain ⟨L, hL⟩ : ∃ L, PI q.val z = some L := by
    unfold ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout at hP
    cases h : PI q.val z with
    | none => simp [h] at hP
    | some L => exact ⟨L, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N, PI (q.val + 1) z = some N := by
    unfold ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout at hPnext
    cases h : PI (q.val + 1) z with
    | none => simp [h] at hPnext
    | some N => exact ⟨N, rfl⟩
  obtain ⟨c, hc, _happend⟩ := present_successor_has_actual_cell
    rate rewards C_star C_h q z L N hL hN
  have hstate : stateReadout (RecordedQueueRun.run Q L) = o := by
    exact Option.some.inj ((prefixReadout_of_inputs rate rewards C_star C_h
      q.val z L hL).symm.trans hP)
  have hstateFlag : (RecordedQueueRun.run Q L).overflow = o.2.1 := by
    exact congrArg (fun v : Readout => v.2.1) hstate
  have hdisableOrOverflow : c.enabled = false ∨
      (RecordedQueueRun.run Q L).overflow = true := by
    by_cases ho : o.2.1 = true
    · exact Or.inr (by rw [hstateFlag, ho])
    · have hoFalse : o.2.1 = false := by cases h : o.2.1 <;> simp_all
      by_cases hcEnabled : c.enabled = true
      · exact (hnotA ⟨o, c, hP, hc, hoFalse, hcEnabled⟩).elim
      · cases he : c.enabled with
        | false => exact Or.inl rfl
        | true => exact False.elim (hcEnabled he)
  have hreg : (RecordedQueueRun.step Q (RecordedQueueRun.run Q L) c).registers a =
      (RecordedQueueRun.run Q L).registers a := by
    rcases hdisableOrOverflow with hdisabled | hoverflow
    · exact (RecordedQueueRun.step_disabled_preserves Q (RecordedQueueRun.run Q L)
        c hdisabled a).1
    · exact (RecordedQueueRun.step_after_overflow_preserves Q (RecordedQueueRun.run Q L)
        c hoverflow a).1
  have hPstep := prefixReadout_append_actualCell rate rewards C_star C_h q z L hL c hc
  have hoNext : onext =
      stateReadout (RecordedQueueRun.step Q (RecordedQueueRun.run Q L) c) :=
    Option.some.inj (hPnext.symm.trans hPstep)
  have hcarry := carriedPrefixReadout_of_present rate rewards C_star C_h q.val z o hP
  have hcarryNext := carriedPrefixReadout_of_present rate rewards C_star C_h
    (q.val + 1) z onext hPnext
  have hregReadout : ((onext.1 a).2 : ℝ) = ((o.1 a).2 : ℝ) := by
    rw [hoNext, ← hstate]
    change (((RecordedQueueRun.step Q (RecordedQueueRun.run Q L) c).registers a).2 : ℝ) =
      (((RecordedQueueRun.run Q L).registers a).2 : ℝ)
    exact congrArg (fun n : ℕ => (n : ℝ)) (congrArg Prod.snd hreg)
  simp [carriedStoppedEnergy, hcarry, hcarryNext, hregReadout]

local instance sourceInputMeasurableSpace : MeasurableSpace X := by
  change MeasurableSpace (CompletePublicTable.PublishedOutput p ×
    BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

/-- Finite optional recursion preserves ambient Borel measurability. -/
private theorem measurable_carriedPrefixReadout (n : ℕ) :
    Measurable (carriedPrefixReadout rate rewards C_star C_h n) := by
  induction n with
  | zero =>
      exact ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.measurable_prefixReadout
        rate rewards C_star C_h 0
  | succ n ih =>
      have hp :=
        ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.measurable_prefixReadout
          rate rewards C_star C_h (n + 1)
      exact (measurable_of_countable
        (fun v : Option Readout × Option Readout => v.1.or v.2)).comp (hp.prodMk ih)

private theorem measurable_prefixReadout_at_prior_filtration
    (control0 : ContinuousLearningRows.TimeControl p) (q : Fin p.T)
    (n : ℕ) (hnq : n ≤ q.val) :
    Measurable[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
      control0 (q.val + 1)] (P n) := by
  let t : Fin p.T := ⟨n, lt_of_le_of_lt hnq q.isLt⟩
  have hEq : P n = ReferenceFirstCollectionCurrentRetainedGate.prefixReadout?
      rate rewards C_star C_h t := by
    funext z
    exact prefixReadout_eq_currentRetainedGate rate rewards C_star C_h t z
  rw [hEq]
  have hmeas := ReferenceFirstCollectionCurrentRetainedGate.prefixReadout_measurable
    rate rewards C_star C_h control0 t
  have hmono := (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
    control0).mono (Nat.add_le_add_right hnq 1)
  have hreadoutTop : (inferInstance : MeasurableSpace Readout) = ⊤ := by
    apply le_antisymm le_top
    intro s _
    exact (Set.to_countable s).measurableSet
  have hsumTop : (inferInstance : MeasurableSpace (Readout ⊕ PUnit)) = ⊤ := by
    apply le_antisymm le_top
    intro s _
    exact (Set.to_countable s).measurableSet
  have hcodEq : LaterAssignmentStartMeasurability.optionMeasurableSpace =
      (⊤ : MeasurableSpace (Option Readout)) := by
    rw [LaterAssignmentStartMeasurability.optionMeasurableSpace, hsumTop]
    apply MeasurableSpace.ext
    intro s
    constructor
    · intro _
      trivial
    · intro _
      refine ⟨Equiv.optionEquivSumPUnit Readout '' s, trivial, ?_⟩
      ext x
      simp
  have hcod : (⊤ : MeasurableSpace (Option Readout)) ≤
      LaterAssignmentStartMeasurability.optionMeasurableSpace := by
    rw [hcodEq]
  exact Measurable.mono hmeas hmono hcod

private theorem measurable_carriedPrefixReadout_at_prior_filtration
    (control0 : ContinuousLearningRows.TimeControl p) (q : Fin p.T)
    (n : ℕ) (hnq : n ≤ q.val) :
    Measurable[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
      control0 (q.val + 1)] (carriedPrefixReadout rate rewards C_star C_h n) := by
  induction n with
  | zero =>
      simpa [carriedPrefixReadout] using
        measurable_prefixReadout_at_prior_filtration rate rewards C_star C_h
          control0 q 0 (Nat.zero_le _)
  | succ n ih =>
      have hp := measurable_prefixReadout_at_prior_filtration rate rewards C_star C_h
        control0 q (n + 1) hnq
      have hi := ih (by omega)
      exact (measurable_of_countable
        (fun v : Option Readout × Option Readout => v.1.or v.2)).comp (hp.prodMk hi)

/-- The current scalar is predictable in the original source filtration:
every prefix used by the finite carry is an actual strict-past retained-gate
readout at its literal date. -/
public theorem measurable_carriedStoppedEnergy_predictable
    (control0 : ContinuousLearningRows.TimeControl p) (q : Fin p.T)
    (a : Fin p.K) :
    Measurable[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
      control0 (q.val + 1)] (carriedStoppedEnergy rate rewards C_star C_h q.val a) := by
  let : MeasurableSpace X :=
    ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (q.val + 1)
  have hm := measurable_carriedPrefixReadout_at_prior_filtration
    rate rewards C_star C_h control0 q q.val le_rfl
  have hg : Measurable (fun o : Option Readout =>
      match o with
      | none => (1 : ℝ)
      | some v => Real.exp (CanonicalRecordingRates.beta p rate.eta.val *
          ((v.1 a).2 : ℝ) /
          ((ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ))) :=
    measurable_of_countable _
  exact hg.comp hm

/-- Ambient Borelness of the scalar carried energy. -/
public theorem measurable_carriedStoppedEnergy (n : ℕ) (a : Fin p.K) :
    Measurable (carriedStoppedEnergy rate rewards C_star C_h n a) := by
  have hm : Measurable (fun o : Option Readout =>
      match o with
      | none => (1 : ℝ)
      | some v => Real.exp (CanonicalRecordingRates.beta p rate.eta.val *
          ((v.1 a).2 : ℝ) /
          ((ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ))) :=
    measurable_of_countable _
  exact hm.comp (measurable_carriedPrefixReadout rate rewards C_star C_h n)

/-- Provenance transfers the normalized prefix backlog bound to every carried
observation; absence remains the literal scalar one. -/
public theorem carriedStoppedEnergy_bounds (n : ℕ) (_hn : n ≤ p.T)
    (a : Fin p.K) (z : X) :
    1 ≤ carriedStoppedEnergy rate rewards C_star C_h n a z ∧
      carriedStoppedEnergy rate rewards C_star C_h n a z ≤
        energyCeiling rate := by
  by_cases hnone : carriedPrefixReadout rate rewards C_star C_h n z = none
  · rw [carriedStoppedEnergy_eq_one_of_none rate rewards C_star C_h n a z hnone]
    have hcap : 0 < backlogCap rate := by
      rw [backlogCap]
      exact one_div_pos.mpr (mul_pos (by norm_num) rate.eta.property)
    constructor
    · norm_num
    · apply Real.one_le_exp_iff.mpr
      apply mul_nonneg (CanonicalRecordingRates.beta_pos p rate.eta.property).le
      exact mul_nonneg (by norm_num) hcap.le
  · cases hread : carriedPrefixReadout rate rewards C_star C_h n z with
    | none => exact (hnone hread).elim
    | some o =>
        have hprov := carriedPrefixReadout_provenance rate rewards C_star C_h n z o hread
        obtain ⟨k, hkn, hprefix⟩ := hprov
        have hb :=
          ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.prefixReadout_backlog_bounds
            rate rewards C_star C_h k z o hprefix a
        have hqpos : 0 <
            ((ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ) :=
          Nat.cast_pos.mpr (ReferenceFirstLaunchNumericalCell.queueParameters rate).n_pos
        have hbeta : 0 < CanonicalRecordingRates.beta p rate.eta.val :=
          CanonicalRecordingRates.beta_pos p rate.eta.property
        have hnorm : 0 ≤ ((o.1 a).2 : ℝ) /
            ((ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ) := hb.1
        have hexp :
            CanonicalRecordingRates.beta p rate.eta.val * ((o.1 a).2 : ℝ) /
                ((ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ) =
              CanonicalRecordingRates.beta p rate.eta.val *
                (((o.1 a).2 : ℝ) /
                  ((ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ)) := by
          ring
        have henergy : carriedStoppedEnergy rate rewards C_star C_h n a z =
            Real.exp (CanonicalRecordingRates.beta p rate.eta.val *
              (((o.1 a).2 : ℝ) /
                ((ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ))) := by
          simp [carriedStoppedEnergy, hread, hexp]
        rw [henergy]
        constructor
        · apply Real.one_le_exp_iff.mpr
          exact mul_nonneg hbeta.le hnorm
        · apply Real.exp_le_exp.mpr
          exact mul_le_mul_of_nonneg_left hb.2 hbeta.le

/-- Uniform deterministic domination makes every calendar energy integrable
under the original source-input law. -/
public theorem integrable_carriedStoppedEnergy (n : ℕ) (hn : n ≤ p.T)
    (a : Fin p.K) :
    Integrable (carriedStoppedEnergy rate rewards C_star C_h n a) (sourceInputLaw p) := by
  have hconst : Integrable (fun _ : X => energyCeiling rate) (sourceInputLaw p) :=
    integrable_const _
  refine hconst.mono'
    (measurable_carriedStoppedEnergy rate rewards C_star C_h n a).aestronglyMeasurable ?_
  filter_upwards [] with z
  have hb := carriedStoppedEnergy_bounds rate rewards C_star C_h n hn a z
  simpa only [Real.norm_eq_abs, abs_of_nonneg (le_trans (by norm_num) hb.1)] using hb.2

/-- Internal event identity: the locator's actual numerical detector is
exactly terminal overflow of the carried genuine readout. This concerns only
the observation construction, not a physical queue event. -/
private theorem execute_append (left right : List Input)
    (s : RecordedQueueRun.RunState p.K) :
    RecordedQueueRun.execute Q (left ++ right) s =
      RecordedQueueRun.execute Q right (RecordedQueueRun.execute Q left s) := by
  induction left generalizing s with
  | nil => simp [RecordedQueueRun.execute]
  | cons c left ih =>
      simp only [List.cons_append, RecordedQueueRun.execute]
      exact ih _

/-- A later present prefix extending an already overflowing original prefix
has exactly the same queue registers. The accepted-record history is allowed
to grow over the suffix. -/
private theorem queueRegisters_equal_after_overflow (q : Fin p.T) (k : ℕ) (z : X)
    (hs : ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart
      rate rewards C_star C_h z ≤ q.val)
    (hk : q.val + 1 ≤ k) (hkT : k ≤ p.T)
    (L : List Input) (c : Input) (N : List Input)
    (hPInext : PI (q.val + 1) z = some (L ++ [c]))
    (hPIk : PI k z = some N)
    (hflag : (RecordedQueueRun.step Q (RecordedQueueRun.run Q L) c).overflow = true) :
    ∀ a, (RecordedQueueRun.run Q N).registers a =
      (RecordedQueueRun.step Q (RecordedQueueRun.run Q L) c).registers a := by
  obtain ⟨Ld, hPId, hLd, _⟩ := prefixInputs_from_present_full
    rate rewards C_star C_h k (q.val + 1) z hkT (by omega) (by omega) N hPIk
  have htake : N.take (q.val + 1 -
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart
        rate rewards C_star C_h z) = L ++ [c] := by
    have heq : Ld = L ++ [c] := Option.some.inj (hPId.symm.trans hPInext)
    calc
      N.take (q.val + 1 -
          ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart
            rate rewards C_star C_h z) = Ld := hLd.symm
      _ = L ++ [c] := heq
  have hNsplit : N = (L ++ [c]) ++ N.drop (q.val + 1 -
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart
        rate rewards C_star C_h z) := by
    have hsplit := List.take_append_drop (q.val + 1 -
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart
        rate rewards C_star C_h z) N
    rw [htake] at hsplit
    exact hsplit.symm
  have hrun : RecordedQueueRun.run Q N =
      RecordedQueueRun.execute Q (N.drop (q.val + 1 -
        ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart
          rate rewards C_star C_h z))
        (RecordedQueueRun.run Q (L ++ [c])) := by
    calc
      RecordedQueueRun.run Q N =
          RecordedQueueRun.run Q ((L ++ [c]) ++ N.drop (q.val + 1 -
            ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart
              rate rewards C_star C_h z)) :=
        congrArg (RecordedQueueRun.run Q) hNsplit
      _ = RecordedQueueRun.execute Q (N.drop (q.val + 1 -
          ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart
            rate rewards C_star C_h z)) (RecordedQueueRun.run Q (L ++ [c])) := by
        unfold RecordedQueueRun.run
        exact execute_append rate (L ++ [c]) (N.drop (q.val + 1 -
          ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart
            rate rewards C_star C_h z)) (RecordedQueueRun.initialState p.K)
  have hone := ReferenceFirstCollectionRenewalFutureNumericalPrefix.run_append_one
    rate L c
  have hpres := RecordedQueueRun.execute_after_overflow_preserves Q
    (N.drop (q.val + 1 -
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart
        rate rewards C_star C_h z))
    (RecordedQueueRun.step Q (RecordedQueueRun.run Q L) c) hflag
  intro a
  rw [hrun, hone]
  exact hpres.2 a

private theorem carried_some_at_later (n m : ℕ) (z : X) (hnm : n ≤ m)
    (o : Readout)
    (h : carriedPrefixReadout rate rewards C_star C_h n z = some o) :
    ∃ v, carriedPrefixReadout rate rewards C_star C_h m z = some v := by
  have hrec : ∀ d, ∃ v, carriedPrefixReadout rate rewards C_star C_h (n + d) z = some v := by
    intro d
    induction d with
    | zero => exact ⟨o, by simpa using h⟩
    | succ d ih =>
        by_cases hp : P (n + d + 1) z = none
        · obtain ⟨v, hv⟩ := ih
          refine ⟨v, ?_⟩
          rw [show n + (d + 1) = n + d + 1 by omega]
          rw [carriedPrefixReadout_succ_absent rate rewards C_star C_h (n + d) z
            (by simpa [Nat.add_assoc] using hp)]
          exact hv
        · cases hcur : P (n + d + 1) z with
          | none => exact (hp hcur).elim
          | some v => exact ⟨v, carriedPrefixReadout_succ_present
              rate rewards C_star C_h (n + d) z v
              (by simpa [Nat.add_assoc] using hcur)⟩
  obtain ⟨v, hv⟩ := hrec (m - n)
  exact ⟨v, by simpa [Nat.add_sub_of_le hnm] using hv⟩

public theorem observedNumericalOverflowEvent_eq_terminalCarriedEnergy :
    ReferenceOriginalNumericalFirstOverflowLocator.observedNumericalOverflowEvent
        rate rewards C_star C_h =
      {z | ∃ a : Fin p.K,
        Real.exp (CanonicalRecordingRates.beta p rate.eta.val * backlogCap rate) <
          carriedStoppedEnergy rate rewards C_star C_h p.T a z} := by
  classical
  ext z
  constructor
  · intro hz
    rw [ReferenceOriginalNumericalFirstOverflowLocator.observedNumericalOverflowEvent_eq_firstOverflowUpdateUnion]
      at hz
    rw [Set.mem_iUnion] at hz
    obtain ⟨q, hq⟩ := hz
    simp only [ReferenceOriginalNumericalFirstOverflowLocator.firstOverflowUpdateAt,
      Set.mem_ofPred_eq] at hq
    rcases hq with ⟨L, r, c, a, hL, hs, _hslt, _hlen, hinputsNext,
      _hlookup, _htime, _hrecord, _hcell, _hphase, _hread, hreadNext,
      _hpriorFlag, _henabled, hflag, hthreshold, _hprior, _hpresent,
      _hleast, _htransition⟩
    let od := stateReadout (RecordedQueueRun.step Q (RecordedQueueRun.run Q L) c)
    have hcarryD := carriedPrefixReadout_of_present rate rewards C_star C_h
      (q.val + 1) z od hreadNext
    obtain ⟨ot, hcarryT⟩ := carried_some_at_later rate rewards C_star C_h
      (q.val + 1) p.T z (by omega) od hcarryD
    obtain ⟨k, hkT, hreadK, hlast⟩ :=
      (carriedPrefixReadout_eq_some_iff rate rewards C_star C_h
        p.T z ot).mp hcarryT
    have hdetle : q.val + 1 ≤ k := by
      by_contra h
      have hkdet : k < q.val + 1 := Nat.lt_of_not_ge h
      have hnone := hlast (q.val + 1) hkdet (by omega)
      rw [hreadNext] at hnone
      cases hnone
    have hPIk : ∃ N : List Input, PI k z = some N := by
      unfold ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout at hreadK
      cases h : PI k z with
      | none => simp [h] at hreadK
      | some N => exact ⟨N, rfl⟩
    obtain ⟨N, hPIk⟩ := hPIk
    have hrunK := prefixReadout_of_inputs rate rewards C_star C_h k z N hPIk
    have hstateK : stateReadout (RecordedQueueRun.run Q N) = ot := by
      exact Option.some.inj (hrunK.symm.trans hreadK)
    have hbeta : 0 < CanonicalRecordingRates.beta p rate.eta.val :=
      CanonicalRecordingRates.beta_pos p rate.eta.property
    have hden : 0 <
        ((ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ) :=
      Nat.cast_pos.mpr
        (ReferenceFirstLaunchNumericalCell.queueParameters rate).n_pos
    have hnorm :
        ((stateReadout (RecordedQueueRun.step Q (RecordedQueueRun.run Q L) c)).1 a).2 /
          ((ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ) >
          backlogCap rate := by
      simpa [backlogCap] using hthreshold
    have harg :
        CanonicalRecordingRates.beta p rate.eta.val * backlogCap rate <
          CanonicalRecordingRates.beta p rate.eta.val *
            (((stateReadout (RecordedQueueRun.step Q (RecordedQueueRun.run Q L) c)).1 a).2 /
              ((ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ)) :=
      mul_lt_mul_of_pos_left hnorm hbeta
    have harg' :
        CanonicalRecordingRates.beta p rate.eta.val * backlogCap rate <
          CanonicalRecordingRates.beta p rate.eta.val *
            (((stateReadout (RecordedQueueRun.step Q (RecordedQueueRun.run Q L) c)).1 a).2 : ℝ) /
              ((ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ) := by
      simpa only [div_eq_mul_inv, mul_assoc] using harg
    have hexp := (Real.exp_lt_exp).2 harg'
    have hregs := queueRegisters_equal_after_overflow rate rewards C_star C_h
      q k z hs hdetle hkT L c N hinputsNext hPIk hflag a
    refine ⟨a, ?_⟩
    simp only [carriedStoppedEnergy, hcarryT]
    have hregEq : (ot.1 a).2 =
        ((stateReadout (RecordedQueueRun.step Q (RecordedQueueRun.run Q L) c)).1 a).2 := by
      have hregReadout := congrArg (fun v : Readout => (v.1 a).2) hstateK
      have hregReadout' : (ot.1 a).2 = ((RecordedQueueRun.run Q N).registers a).2 := by
        simpa [stateReadout] using hregReadout.symm
      exact hregReadout'.trans (congrArg Prod.snd hregs)
    rw [hregEq]
    simpa only [div_eq_mul_inv, mul_assoc] using hexp
  · rintro ⟨a, henergy⟩
    have hbeta : 0 < CanonicalRecordingRates.beta p rate.eta.val :=
      CanonicalRecordingRates.beta_pos p rate.eta.property
    have hden : 0 <
        ((ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ) :=
      Nat.cast_pos.mpr
        (ReferenceFirstLaunchNumericalCell.queueParameters rate).n_pos
    by_cases hnone : carriedPrefixReadout rate rewards C_star C_h p.T z = none
    · rw [carriedStoppedEnergy_eq_one_of_none rate rewards C_star C_h p.T a z hnone] at henergy
      have hcap : 0 < backlogCap rate := by
        rw [backlogCap]
        exact one_div_pos.mpr (mul_pos (by norm_num) rate.eta.property)
      have hthreshold : 1 <
          Real.exp (CanonicalRecordingRates.beta p rate.eta.val * backlogCap rate) := by
        apply Real.one_lt_exp_iff.mpr
        exact mul_pos hbeta hcap
      linarith
    · cases hcarry : carriedPrefixReadout rate rewards C_star C_h p.T z with
      | none => exact (hnone hcarry).elim
      | some o =>
          have hprov := carriedPrefixReadout_provenance rate rewards C_star C_h
            p.T z o hcarry
          obtain ⟨k, hkT, hread⟩ := hprov
          have henergy' : Real.exp
              (CanonicalRecordingRates.beta p rate.eta.val *
                ((o.1 a).2 : ℝ) /
                  ((ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ)) >
                Real.exp (CanonicalRecordingRates.beta p rate.eta.val * backlogCap rate) := by
            simpa [carriedStoppedEnergy, hcarry] using henergy
          have harg := (Real.exp_lt_exp).mp (by simpa only [gt_iff_lt] using henergy')
          have harg' : CanonicalRecordingRates.beta p rate.eta.val * backlogCap rate <
              CanonicalRecordingRates.beta p rate.eta.val *
                (((o.1 a).2 : ℝ) /
                  ((ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ)) := by
            simpa only [div_eq_mul_inv, mul_assoc] using harg
          have hratio : backlogCap rate <
              ((o.1 a).2 : ℝ) /
                ((ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ) := by
            by_contra hnot
            have hle : ((o.1 a).2 : ℝ) /
                ((ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ) ≤
                  backlogCap rate := le_of_not_gt hnot
            have hmul := mul_le_mul_of_nonneg_left hle hbeta.le
            linarith
          have hthreshold : ((o.1 a).2 : ℝ) /
              ((ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ) >
                1 / (32 * rate.eta.val) := by
            simpa [backlogCap] using hratio
          exact ⟨k, hkT, o, hread, a, hthreshold⟩

/-- On the active branch the outgoing energy obeys the exact deterministic
exponential queue inequality, retaining the first detecting successor. -/
public theorem activeUpdate_energy_increment_bound (q : Fin p.T) (a : Fin p.K)
    (z : X) (hA : activeUpdateAt rate rewards C_star C_h q z) :
    carriedStoppedEnergy rate rewards C_star C_h (q.val + 1) a z -
        carriedStoppedEnergy rate rewards C_star C_h q.val a z ≤
      1 + carriedStoppedEnergy rate rewards C_star C_h q.val a z *
        (Real.exp (CanonicalRecordingRates.beta p rate.eta.val *
          normalizedArrivalIncrementAt rate rewards C_star C_h q a z) - 1) := by
  have hA' := hA
  obtain ⟨o, c, hP, hc, hflag, henabled⟩ := hA
  have hLexists : ∃ L : List Input, PI q.val z = some L := by
    have hread := hP
    unfold ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout at hread
    cases h : PI q.val z with
    | none => simp [h] at hread
    | some L => exact ⟨L, rfl⟩
  obtain ⟨L, hL⟩ := hLexists
  have hread := prefixReadout_of_inputs rate rewards C_star C_h q.val z L hL
  have hstate : stateReadout (RecordedQueueRun.run Q L) = o :=
    Option.some.inj (hread.symm.trans hP)
  have hsflag : (RecordedQueueRun.run Q L).overflow = false := by
    have hf := congrArg (fun v : Readout => v.2.1) hstate
    exact hf.trans hflag
  have hnext := prefixReadout_append_actualCell rate rewards C_star C_h q z L hL c hc
  have hcarried : carriedPrefixReadout rate rewards C_star C_h q.val z = some o :=
    carriedPrefixReadout_of_present rate rewards C_star C_h q.val z o hP
  have hcarriedNext :
      carriedPrefixReadout rate rewards C_star C_h (q.val + 1) z =
        some (stateReadout (RecordedQueueRun.step Q (RecordedQueueRun.run Q L) c)) :=
    carriedPrefixReadout_of_present rate rewards C_star C_h (q.val + 1) z _ hnext
  have hE : carriedStoppedEnergy rate rewards C_star C_h q.val a z =
      Real.exp (CanonicalRecordingRates.beta p rate.eta.val *
        ((o.1 a).2 : ℝ) /
          ((ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ)) := by
    simp [carriedStoppedEnergy, hcarried]
  have hEnext : carriedStoppedEnergy rate rewards C_star C_h (q.val + 1) a z =
      Real.exp (CanonicalRecordingRates.beta p rate.eta.val *
        (((stateReadout (RecordedQueueRun.step Q (RecordedQueueRun.run Q L) c)).1 a).2 : ℝ) /
        ((ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ)) := by
    simp [carriedStoppedEnergy, hcarriedNext]
  let b := StoppedQueueBound.normalizedBacklog Q (RecordedQueueRun.run Q L) a
  let x := RecordedRoundMoments.normalizedQuantizedArrival Q c a - 4
  have hb : b = ((o.1 a).2 : ℝ) /
      ((ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ) := by
    dsimp [b]
    rw [← hstate]
    simp [StoppedQueueBound.normalizedBacklog, stateReadout]
  have hx : normalizedArrivalIncrementAt rate rewards C_star C_h q a z = x := by
    exact normalizedArrivalIncrementAt_eq rate rewards C_star C_h q a z c hA' hc
  have hraw := RecordedRoundMoments.rawEstimate_eq_normalizedQuantizedArrival_of_enabled
    Q (RecordedQueueRun.run Q L) c a henabled hsflag
  have hstep := CanonicalQueueProcess.normalizedBacklog_step_of_retained
    Q (RecordedQueueRun.run Q L) c a hsflag henabled
  have hstep' :
      StoppedQueueBound.normalizedBacklog Q
        (RecordedQueueRun.step Q (RecordedQueueRun.run Q L) c) a = max (b + x) 0 := by
    rw [hstep, hraw]
    dsimp [b, x]
    congr 1
    ring
  have hE0 : carriedStoppedEnergy rate rewards C_star C_h q.val a z =
      Real.exp (CanonicalRecordingRates.beta p rate.eta.val * b) := by
    rw [hE]
    rw [show CanonicalRecordingRates.beta p rate.eta.val * ((o.1 a).2 : ℝ) /
        ((ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ) =
          CanonicalRecordingRates.beta p rate.eta.val * (((o.1 a).2 : ℝ) /
            ((ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ)) by ring]
    rw [← hb]
  have hE1 : carriedStoppedEnergy rate rewards C_star C_h (q.val + 1) a z =
      Real.exp (CanonicalRecordingRates.beta p rate.eta.val *
        StoppedQueueBound.normalizedBacklog Q
          (RecordedQueueRun.step Q (RecordedQueueRun.run Q L) c) a) := by
    rw [hEnext]
    rw [show CanonicalRecordingRates.beta p rate.eta.val *
        (((stateReadout (RecordedQueueRun.step Q (RecordedQueueRun.run Q L) c)).1 a).2 : ℝ) /
          ((ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ) =
            CanonicalRecordingRates.beta p rate.eta.val *
            ((((stateReadout (RecordedQueueRun.step Q (RecordedQueueRun.run Q L) c)).1 a).2 : ℝ) /
              ((ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ)) by ring]
    congr 1
  have hmax := CanonicalQueueProcess.exp_mul_max_le b x
    (CanonicalRecordingRates.beta p rate.eta.val)
  have hupper : carriedStoppedEnergy rate rewards C_star C_h (q.val + 1) a z ≤
      1 + carriedStoppedEnergy rate rewards C_star C_h q.val a z *
        Real.exp (CanonicalRecordingRates.beta p rate.eta.val * x) := by
    calc
      carriedStoppedEnergy rate rewards C_star C_h (q.val + 1) a z =
          Real.exp (CanonicalRecordingRates.beta p rate.eta.val * max (b + x) 0) := by
        rw [hE1, hstep']
      _ ≤ 1 + Real.exp (CanonicalRecordingRates.beta p rate.eta.val * b) *
            Real.exp (CanonicalRecordingRates.beta p rate.eta.val * x) := hmax
      _ = 1 + carriedStoppedEnergy rate rewards C_star C_h q.val a z *
            Real.exp (CanonicalRecordingRates.beta p rate.eta.val * x) := by rw [← hE0]
  rw [hx]
  have hsub :
      carriedStoppedEnergy rate rewards C_star C_h (q.val + 1) a z -
          carriedStoppedEnergy rate rewards C_star C_h q.val a z ≤
        1 + carriedStoppedEnergy rate rewards C_star C_h q.val a z *
          Real.exp (CanonicalRecordingRates.beta p rate.eta.val * x) -
          carriedStoppedEnergy rate rewards C_star C_h q.val a z := by
    linarith
  calc
    carriedStoppedEnergy rate rewards C_star C_h (q.val + 1) a z -
        carriedStoppedEnergy rate rewards C_star C_h q.val a z ≤
      1 + carriedStoppedEnergy rate rewards C_star C_h q.val a z *
        Real.exp (CanonicalRecordingRates.beta p rate.eta.val * x) -
        carriedStoppedEnergy rate rewards C_star C_h q.val a z := hsub
    _ = 1 + carriedStoppedEnergy rate rewards C_star C_h q.val a z *
          (Real.exp (CanonicalRecordingRates.beta p rate.eta.val * x) - 1) := by ring

private theorem carriedStoppedEnergy_eq_of_inactive_update (q : Fin p.T)
    (a : Fin p.K) (z : X)
    (hnotA : ¬ activeUpdateAt rate rewards C_star C_h q z) :
    carriedStoppedEnergy rate rewards C_star C_h (q.val + 1) a z =
      carriedStoppedEnergy rate rewards C_star C_h q.val a z := by
  by_cases hPnone : P q.val z = none
  · by_cases hcarryNone :
        carriedPrefixReadout rate rewards C_star C_h q.val z = none
    · by_cases hnextNone : P (q.val + 1) z = none
      · have hcarryNext :
            carriedPrefixReadout rate rewards C_star C_h (q.val + 1) z = none := by
          simp [carriedPrefixReadout, hnextNone, hcarryNone]
        simp [carriedStoppedEnergy, hcarryNone, hcarryNext]
      · cases hnext : P (q.val + 1) z with
        | none => exact (hnextNone hnext).elim
        | some o =>
            have hinputs : ∃ L, PI (q.val + 1) z = some L := by
              unfold ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout at hnext
              cases h : PI (q.val + 1) z with
              | none => simp [h] at hnext
              | some L => exact ⟨L, rfl⟩
            obtain ⟨L, hL⟩ := hinputs
            have hlaunch :=
              ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs_launch
                rate rewards C_star C_h (q.val + 1) z L hL
            have hstart : ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart
                rate rewards C_star C_h z = q.val + 1 := by
              have hnotStart : ¬ ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart
                  rate rewards C_star C_h z ≤ q.val := by
                intro hs
                obtain ⟨Lq, hLq, _, _⟩ := prefixInputs_from_present_full
                  rate rewards C_star C_h (q.val + 1) q.val z (by omega) hs (by omega) L hL
                have hPq : P q.val z = some
                    (stateReadout (RecordedQueueRun.run Q Lq)) := by
                  simp [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout,
                    hLq]
                rw [hPnone] at hPq
                cases hPq
              have hsle : ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart
                  rate rewards C_star C_h z ≤ q.val + 1 := by
                simpa only [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart]
                  using hlaunch.2
              omega
            have hslots := prefixInputs_slots rate rewards C_star C_h
              (q.val + 1) z L (by omega) hL
            have hLnil : L = [] := by
              rw [hstart] at hslots
              simp only [Nat.sub_self, List.take_zero, List.map_nil] at hslots
              cases L with
              | nil => rfl
              | cons x xs => simp at hslots
            subst L
            have hcarryNext := carriedPrefixReadout_of_present rate rewards C_star C_h
              (q.val + 1) z (stateReadout (RecordedQueueRun.run Q [])) (by
                have hrun : P (q.val + 1) z =
                    some (stateReadout (RecordedQueueRun.run Q [])) :=
                  prefixReadout_of_inputs rate rewards C_star C_h (q.val + 1) z [] hL
                exact hrun)
            have hnextEnergy :
                carriedStoppedEnergy rate rewards C_star C_h (q.val + 1) a z = 1 := by
              simp [carriedStoppedEnergy, hcarryNext, stateReadout,
                RecordedQueueRun.run, RecordedQueueRun.execute,
                RecordedQueueRun.initialState]
            rw [hnextEnergy, carriedStoppedEnergy_eq_one_of_none
              rate rewards C_star C_h q.val a z hcarryNone]
    · cases hcarry : carriedPrefixReadout rate rewards C_star C_h q.val z with
      | none => exact (hcarryNone hcarry).elim
      | some o =>
          obtain ⟨k, hkq, hPk⟩ := carriedPrefixReadout_provenance
            rate rewards C_star C_h q.val z o hcarry
          have hPIk : ∃ L, PI k z = some L := by
            unfold ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout at hPk
            cases h : PI k z with
            | none => simp [h] at hPk
            | some L => exact ⟨L, rfl⟩
          obtain ⟨L, hL⟩ := hPIk
          have hlaunch :=
            ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs_launch
              rate rewards C_star C_h k z L hL
          have hlaunchQ : actualLaunchBy rate rewards C_star C_h q.val z :=
            ⟨hlaunch.1, hlaunch.2.trans hkq⟩
          have hnextNone := prefixReadout_none_persists_after_launch
            rate rewards C_star C_h q.val (q.val + 1) z (by omega) (by omega)
            hlaunchQ hPnone
          have hcarryNext :
              carriedPrefixReadout rate rewards C_star C_h (q.val + 1) z = some o := by
            rw [carriedPrefixReadout_succ_absent rate rewards C_star C_h q.val z hnextNone,
              hcarry]
          simp [carriedStoppedEnergy, hcarry, hcarryNext]
  · cases hP : P q.val z with
    | none => exact (hPnone hP).elim
    | some o =>
        by_cases hnextNone : P (q.val + 1) z = none
        · have hcarry := carriedPrefixReadout_of_present
            rate rewards C_star C_h q.val z o hP
          have hcarryNext :
              carriedPrefixReadout rate rewards C_star C_h (q.val + 1) z = some o := by
            rw [carriedPrefixReadout_succ_absent rate rewards C_star C_h q.val z hnextNone,
              hcarry]
          simp [carriedStoppedEnergy, hcarry, hcarryNext]
        · cases hnext : P (q.val + 1) z with
          | none => exact (hnextNone hnext).elim
          | some onext =>
              exact carriedStoppedEnergy_freeze_of_present_successor
                rate rewards C_star C_h q a z o onext hP hnext hnotA

/-- Exact deterministic update over every branch: a fresh launch preserves
the scalar one, absent readouts carry their old energy, and only the active
retained update contributes the exponential arrival term. -/
public theorem carriedStoppedEnergy_update_bound (q : Fin p.T) (a : Fin p.K) (z : X) :
    carriedStoppedEnergy rate rewards C_star C_h (q.val + 1) a z -
        carriedStoppedEnergy rate rewards C_star C_h q.val a z ≤
      (if activeUpdateAt rate rewards C_star C_h q z then 1 else 0) +
        carriedStoppedEnergy rate rewards C_star C_h q.val a z *
          (Real.exp (CanonicalRecordingRates.beta p rate.eta.val *
            normalizedArrivalIncrementAt rate rewards C_star C_h q a z) - 1) := by
  by_cases hA : activeUpdateAt rate rewards C_star C_h q z
  · simpa [hA] using activeUpdate_energy_increment_bound
      rate rewards C_star C_h q a z hA
  · have heq := carriedStoppedEnergy_eq_of_inactive_update
      rate rewards C_star C_h q a z hA
    simp [hA, normalizedArrivalIncrementAt, heq]

end Bandits.Support.ReferenceOriginalCalendarCarriedStoppedEnergy

end
