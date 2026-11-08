/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionCorrectedSliceNumericalPrefix

import Mathlib.Tactic
import Mathlib.MeasureTheory.Function.FactorsThrough

/-!
# Strict-future observations of the original corrected slice

Sources: `04_slow_fast_learner.tex:140-188,245-290`,
`05_binary_transport.tex:354-431`, and `06_interruptions.tex:9-14,31-100,355-426`
in `sources/zip4/manuscript/`.

The gate includes the actual first selected cutoff, but excludes any other
first noncontinuing constructor. All observations retain the original source.
These are deterministic internal results, with no conditional-law assertion.
-/

@[expose] public section
noncomputable section

open MeasureTheory
open Bandits.Support ConstructorDimensions
open ReferenceActivePhysicalStep ReferenceActivePhysicalHorizon
open ReferenceSourcePrefixHistoryFiltration
open scoped Classical

namespace Bandits.Support.ReferenceFirstCollectionCorrectedFutureRecordingView


variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ)

local notation "X" => BootstrapPrivateRoundStreams.SourceInput p
local notation "Record" => RoundRecord (p := p) (rate := rate)

/-- Strict-past actual observations; absent records do not continue. -/
def pastFlags (q : Fin p.T) (x : X) : Fin q.val → Bool := fun j =>
  (ReferenceInspectedPastRoundObservations.pastRoundObservations
    rate rewards C_star C_h q.val (Nat.le_of_lt q.isLt) x j).elim false
      (ReferenceFirstCollectionRenewalFutureFirstReplacementView.continuingCode rate)

/-- Every actual post-birth round strictly before the queried round continues. -/
def priorSlice (t q : Fin p.T) (x : X) : Bool :=
  decide (∀ j : Fin q.val, t.val + 1 ≤ j.val →
    pastFlags rate rewards C_star C_h q x j = true)

/-- Current live dispatcher tag, erasing only the chosen arm. -/
def rawTag (q : Fin p.T) (x : X) : Option (ReferenceFirstCollectionRenewalNextRecordingPriorView.LiveTag p) :=
  (actualRecord rate rewards C_star C_h q x).bind (fun r => ReferenceFirstCollectionRenewalNextRecordingPriorView.dispatchTag r.input)

/-- A chosen tag contributes its actual cutoff bit, after the strict-past test. -/
def sliceBranch (u t q : Fin p.T) (x : X) : Option Bool :=
  if x ∈ ReferenceFirstCollectionCorrectedSliceNumericalPrefix.correctedCell rate rewards C_star C_h u t ∧
      priorSlice rate rewards C_star C_h t q x = true then
    match rawTag rate rewards C_star C_h q x with
    | some (.inr (.inr (.inr (_, cutoff)))) => some cutoff
    | _ => none
  else none

/-- The literal finite-slice update gate, on the original source. -/
def futureGate (u t q : Fin p.T) : Set X :=
  {x | x ∈ ReferenceFirstCollectionCorrectedSliceNumericalPrefix.correctedCell rate rewards C_star C_h u t ∧
    q.val < ReferenceFirstCollectionCorrectedSliceNumericalPrefix.endDate rate rewards C_star C_h t x}

/-- The actual optional numerical cell, localized only by the literal gate. -/
def futureCell (u t q : Fin p.T) (x : X) :
    Option (RecordedQueueRun.RoundInput p.K) :=
  if x ∈ futureGate rate rewards C_star C_h u t q then
    (actualRecord rate rewards C_star C_h q x).bind (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate)
  else none

/-- Parameters are projections of the actual cell. -/
def futureParameters (u t q : Fin p.T) (x : X) :=
  (futureCell rate rewards C_star C_h u t q x).map fun c => (c.enabled, c.rate)

/-- Outer absence and a present bottom marker remain distinct. -/
def futureMarker (u t q : Fin p.T) (x : X) :=
  (futureCell rate rewards C_star C_h u t q x).map fun c => c.recordedArm

/-- The existing complete recording view, including its actual prepared code. -/
def futureRecordingView (u t q : Fin p.T) (x : X) : Option (ReferenceFirstCollectionRenewalFutureFirstReplacementView.ViewData rate) :=
  if x ∈ futureGate rate rewards C_star C_h u t q then
    (actualRecord rate rewards C_star C_h q x).bind (ReferenceFirstCollectionCorrectedNextPhysicalReadout.recordRecordingView rate)
  else none

/-- The corresponding public recording code. -/
def futureRecordingCode (u t q : Fin p.T) (x : X) :=
  (futureRecordingView rate rewards C_star C_h u t q x).map fun v =>
    (v.1, ReferenceFirstCollectionRenewalNextRecordingPriorView.recordingViewCode rate v.2.1, v.2.2)

private theorem le_takeWhile_length_iff {A : Type*} (f : A → Bool)
    (xs : List A) (n : ℕ) (hn : n ≤ xs.length) :
    n ≤ (xs.takeWhile f).length ↔ ∀ k < n, (xs[k]?).any f = true := by
  induction xs generalizing n with
  | nil =>
    have hz : n = 0 := by simpa using hn
    subst n
    simp
  | cons a xs ih =>
    cases n with
    | zero => simp
    | succ n =>
      have hn' : n ≤ xs.length := by simpa using hn
      cases ha : f a with
      | false =>
        simp only [List.takeWhile, ha, List.length_nil]
        constructor
        · omega
        · intro h
          have h0 := h 0 (Nat.zero_lt_succ n)
          simp only [List.getElem?_cons_zero, Option.any_some, ha, Bool.false_eq_true] at h0
      | true =>
        simp only [List.takeWhile, ha, List.length_cons, Nat.succ_le_succ_iff]
        rw [ih n hn']
        constructor
        · intro h k hk
          cases k with
          | zero => simpa only [List.getElem?_cons_zero, Option.any_some] using ha
          | succ k => simpa only [List.getElem?_cons_succ] using h k (by omega)
        · intro h k hk
          simpa only [List.getElem?_cons_succ] using h (k + 1) (by omega)

private theorem takeWhile_endpoint_false {A : Type*} (f : A → Bool)
    (xs : List A) (n : ℕ) (a : A) (hget : xs[n]? = some a)
    (hlen : (xs.takeWhile f).length = n) : f a = false := by
  induction xs generalizing n with
  | nil => simp at hget
  | cons head tail ih =>
    cases hh : f head with
    | false =>
      have hz : n = 0 := by simpa [List.takeWhile, hh] using hlen.symm
      rw [hz] at hget
      have heq : head = a := by simpa using hget
      simpa only [heq] using hh
    | true =>
      cases n with
      | zero => simp [List.takeWhile, hh] at hlen
      | succ n =>
        exact ih n (by simpa using hget) (by simpa [List.takeWhile, hh] using hlen)

/-- The causal strict-past test is exactly the takeWhile prefix test on E. -/
theorem priorSlice_eq (u t q : Fin p.T) (hfuture : t.val + 1 < q.val) (x : X)
    (hx : x ∈ ReferenceFirstCollectionCorrectedSliceNumericalPrefix.correctedCell rate rewards C_star C_h u t) :
    priorSlice rate rewards C_star C_h t q x =
      decide (q.val - (t.val + 1) ≤ (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail rate rewards C_star C_h x).length) := by
  let R := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords rate rewards C_star C_h x
  let s := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart rate rewards C_star C_h x
  let v := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex rate rewards C_star C_h x
  let n := q.val - (t.val + 1)
  have htime : s + v = t.val := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.firstCell_birth_time rate rewards C_star C_h u t x hx
  have hlen : R.length = p.T - s :=
    ReferenceCompletePhysicalHistory.completeSuffixRecords_length rate x rewards C_star C_h
  have hspan : n ≤ (R.drop (v + 1)).length := by
    simp only [List.length_drop]
    have hq := q.isLt
    dsimp only [n]
    omega
  have hequiv := le_takeWhile_length_iff ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen (R.drop (v + 1)) n hspan
  apply Bool.eq_iff_iff.mpr
  simp only [priorSlice, decide_eq_true_eq]
  change (∀ j : Fin q.val, t.val + 1 ≤ j.val →
    pastFlags rate rewards C_star C_h q x j = true) ↔
      n ≤ ((R.drop (v + 1)).takeWhile ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen).length
  rw [hequiv]
  have hrecord (j : Fin q.val) (hj : t.val + 1 ≤ j.val) :
      pastFlags rate rewards C_star C_h q x j =
        (R[j.val - s]?).any ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen := by
    have hjs : ReferenceCompletePhysicalHistory.physicalStart rate x rewards C_star C_h ≤ j.val := by
      change s ≤ j.val
      omega
    have hr : actualRecord rate rewards C_star C_h
        (Fin.castLE (Nat.le_of_lt q.isLt) j) x = R[j.val - s]? := by
      simp only [actualRecord, Fin.val_castLE, ite_eq_left hjs]
      rfl
    simp only [pastFlags, ReferenceInspectedPastRoundObservations.pastRoundObservations, hr]
    cases hh : R[j.val - s]? with
    | none => rfl
    | some r => simpa only [Option.map_some, Option.elim_some, Option.any_some] using
        ReferenceFirstCollectionRenewalFutureFirstReplacementView.continuingCode_actual rate r
  constructor
  · intro h k hk
    let j : Fin q.val := ⟨t.val + 1 + k, by dsimp only [n] at hk; omega⟩
    have hj : t.val + 1 ≤ j.val := by dsimp only [j]; omega
    have he := hrecord j hj
    have hi : j.val - s = v + 1 + k := by dsimp only [j]; omega
    rw [List.getElem?_drop, ← hi, ← he]
    exact h j hj
  · intro h j hj
    have hk : j.val - (t.val + 1) < n := by dsimp only [n]; omega
    have hh := h (j.val - (t.val + 1)) hk
    rw [List.getElem?_drop] at hh
    have hi : v + 1 + (j.val - (t.val + 1)) = j.val - s := by omega
    rw [hi, ← hrecord j hj] at hh
    exact hh

/-- The actual future record exists on E, with the literal original suffix index. -/
theorem future_record_exists (u t q : Fin p.T) (hfuture : t.val + 1 < q.val) (x : X)
    (hx : x ∈ ReferenceFirstCollectionCorrectedSliceNumericalPrefix.correctedCell rate rewards C_star C_h u t) :
    ∃ r : Record, actualRecord rate rewards C_star C_h q x = some r ∧
      (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords rate rewards C_star C_h x)[ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex rate rewards C_star C_h x +
        1 + (q.val - (t.val + 1))]? = some r := by
  have ht := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.firstCell_birth_time rate rewards C_star C_h u t x hx
  have hlen := ReferenceCompletePhysicalHistory.completeSuffixRecords_length rate x rewards C_star C_h
  change (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords rate rewards C_star C_h x).length =
    p.T - ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart rate rewards C_star C_h x at hlen
  have hs : ReferenceCompletePhysicalHistory.physicalStart rate x rewards C_star C_h ≤ q.val := by
    change ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart rate rewards C_star C_h x ≤ q.val
    omega
  have hi : ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex rate rewards C_star C_h x + 1 + (q.val - (t.val + 1)) =
      q.val - ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart rate rewards C_star C_h x := by omega
  have hlt : q.val - ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart rate rewards C_star C_h x <
      (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords rate rewards C_star C_h x).length := by
    have hq := q.isLt
    change ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart rate rewards C_star C_h x ≤ q.val at hs
    omega
  refine ⟨(ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords rate rewards C_star C_h x)[q.val - ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart rate rewards C_star C_h x],
    ?_, ?_⟩
  · simp only [actualRecord, ite_eq_left hs]
    exact List.getElem?_eq_getElem hlt
  · rw [hi]
    exact List.getElem?_eq_getElem hlt

private theorem rawTag_record (q : Fin p.T) (x : X) (r : Record)
    (hr : actualRecord rate rewards C_star C_h q x = some r) :
    rawTag rate rewards C_star C_h q x =
      match r.output.preparation.coordinator with
      | .live _ _ _ out => some (ReferenceFirstCollectionRenewalNextRecordingPriorView.eraseArm
          (ReferenceLiveDispatchOutputMeasurability.outcomeData out))
      | _ => none := by
  simp only [rawTag, hr, Option.bind_some, ReferenceFirstCollectionRenewalNextRecordingPriorView.dispatchTag]
  have hd : dispatch r.input = r.output.preparation.coordinator := by
    rw [r.output_eq]
    rfl
  rw [hd]
  cases r.output.preparation.coordinator <;> rfl


private theorem continuing_at_future (u t q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (x : X) (hx : x ∈ ReferenceFirstCollectionCorrectedSliceNumericalPrefix.correctedCell rate rewards C_star C_h u t)
    (r : Record) (hr : actualRecord rate rewards C_star C_h q x = some r)
    (hk : q.val - (t.val + 1) < (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail rate rewards C_star C_h x).length) :
    ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen r = true := by
  obtain ⟨r', har, hlookup⟩ := future_record_exists rate rewards C_star C_h u t q hfuture x hx
  have he : r' = r := Option.some.inj (har.symm.trans hr)
  subst r'
  have ht := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail_get (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords rate rewards C_star C_h x)
    (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex rate rewards C_star C_h x) ⟨q.val - (t.val + 1), hk⟩
  have he : r = (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail rate rewards C_star C_h x).get ⟨q.val - (t.val + 1), hk⟩ :=
    Option.some.inj (hlookup.symm.trans ht)
  rw [he]
  exact ReferenceFirstReplacementLiveFollowerPrefix.continuingTail_mem _ _ _ (List.get_mem _ _)

private theorem noncontinuing_at_endpoint (u t q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (x : X) (hx : x ∈ ReferenceFirstCollectionCorrectedSliceNumericalPrefix.correctedCell rate rewards C_star C_h u t)
    (r : Record) (hr : actualRecord rate rewards C_star C_h q x = some r)
    (hend : q.val - (t.val + 1) = (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail rate rewards C_star C_h x).length) :
    ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen r = false := by
  obtain ⟨r', har, hlookup⟩ := future_record_exists rate rewards C_star C_h u t q hfuture x hx
  have he : r' = r := Option.some.inj (har.symm.trans hr)
  subst r'
  apply takeWhile_endpoint_false ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen
    ((ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords rate rewards C_star C_h x).drop (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex rate rewards C_star C_h x + 1))
    (q.val - (t.val + 1)) r
  · simpa only [List.getElem?_drop] using hlookup
  · exact hend.symm

/-- Continuing chosen tags occur exactly inside the actual LIVE tail. -/
theorem sliceBranch_false_iff (u t q : Fin p.T) (hfuture : t.val + 1 < q.val) (x : X) :
    sliceBranch rate rewards C_star C_h u t q x = some false ↔
      x ∈ ReferenceFirstCollectionCorrectedSliceNumericalPrefix.correctedCell rate rewards C_star C_h u t ∧
        q.val - (t.val + 1) < (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail rate rewards C_star C_h x).length := by
  by_cases hx : x ∈ ReferenceFirstCollectionCorrectedSliceNumericalPrefix.correctedCell rate rewards C_star C_h u t
  · rw [sliceBranch, priorSlice_eq rate rewards C_star C_h u t q hfuture x hx]
    obtain ⟨r, har, _⟩ := future_record_exists rate rewards C_star C_h u t q hfuture x hx
    rw [rawTag_record rate rewards C_star C_h q x r har]
    by_cases hn : q.val - (t.val + 1) ≤ (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail rate rewards C_star C_h x).length
    · simp only [hx, decide_eq_true_eq, hn, and_self, ite_true, true_and]
      constructor
      · intro hb
        by_contra hlt
        have hend : q.val - (t.val + 1) = (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail rate rewards C_star C_h x).length := by omega
        have hf := noncontinuing_at_endpoint rate rewards C_star C_h u t q hfuture x hx r har hend
        cases hc : r.output.preparation.coordinator <;> simp only [hc] at hb <;> try contradiction
        rename_i out
        cases out <;> simp only [ReferenceFirstCollectionRenewalNextRecordingPriorView.eraseArm,
          ReferenceLiveDispatchOutputMeasurability.outcomeData, Option.some.injEq, Bool.true_eq_false, reduceCtorEq] at hb
        simp only [ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen, hc] at hf
        cases hf
      · intro hlt
        have hf := continuing_at_future rate rewards C_star C_h u t q hfuture x hx r har hlt
        cases hc : r.output.preparation.coordinator <;> simp only [ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen, hc, Bool.false_eq_true] at hf
        rename_i out
        cases out <;> simp_all [ReferenceFirstCollectionRenewalNextRecordingPriorView.eraseArm, ReferenceLiveDispatchOutputMeasurability.outcomeData]
    · simp [hx, hn, show ¬ q.val - (t.val + 1) <
        (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail rate rewards C_star C_h x).length by omega]
  · simp only [sliceBranch, hx, false_and, ite_false, reduceCtorEq]

/-- The first excluded record contributes only when its actual constructor is cutoffChosen. -/
theorem sliceBranch_true_iff (u t q : Fin p.T) (hfuture : t.val + 1 < q.val) (x : X) :
    sliceBranch rate rewards C_star C_h u t q x = some true ↔
      x ∈ ReferenceFirstCollectionCorrectedSliceNumericalPrefix.correctedCell rate rewards C_star C_h u t ∧
        q.val - (t.val + 1) = (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail rate rewards C_star C_h x).length ∧
        ReferenceFirstCollectionCorrectedSliceNumericalPrefix.cutoffDelta rate rewards C_star C_h x = 1 := by
  by_cases hx : x ∈ ReferenceFirstCollectionCorrectedSliceNumericalPrefix.correctedCell rate rewards C_star C_h u t
  · rw [sliceBranch, priorSlice_eq rate rewards C_star C_h u t q hfuture x hx]
    obtain ⟨r, har, hlookup⟩ := future_record_exists rate rewards C_star C_h u t q hfuture x hx
    rw [rawTag_record rate rewards C_star C_h q x r har]
    by_cases hn : q.val - (t.val + 1) ≤ (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail rate rewards C_star C_h x).length
    · simp only [hx, decide_eq_true_eq, hn, and_self, ite_true, true_and]
      by_cases hend : q.val - (t.val + 1) = (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail rate rewards C_star C_h x).length
      · rw [hend] at hlookup
        simp only [hend, true_and, ReferenceFirstCollectionCorrectedSliceNumericalPrefix.cutoffDelta, hlookup]
        cases r.output.preparation.coordinator <;> simp only [reduceCtorEq]
        rename_i out
        cases out <;> simp [ReferenceFirstCollectionRenewalNextRecordingPriorView.eraseArm, ReferenceLiveDispatchOutputMeasurability.outcomeData]
      · have hlt : q.val - (t.val + 1) < (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail rate rewards C_star C_h x).length := by omega
        have hf := continuing_at_future rate rewards C_star C_h u t q hfuture x hx r har hlt
        simp only [hend, false_and]
        cases hc : r.output.preparation.coordinator <;>
          simp only [ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen, hc, Bool.false_eq_true] at hf
        rename_i out
        cases out <;> simp_all [ReferenceFirstCollectionRenewalNextRecordingPriorView.eraseArm, ReferenceLiveDispatchOutputMeasurability.outcomeData]
    · simp [hx, hn, show ¬ q.val - (t.val + 1) =
        (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail rate rewards C_star C_h x).length by omega]
  · simp only [sliceBranch, hx, false_and, ite_false, reduceCtorEq]

private theorem cutoffDelta_le_one (x : X) : ReferenceFirstCollectionCorrectedSliceNumericalPrefix.cutoffDelta rate rewards C_star C_h x ≤ 1 := by
  unfold ReferenceFirstCollectionCorrectedSliceNumericalPrefix.cutoffDelta
  split
  · split <;> omega
  · omega

/-- Literal original-source chronology: no failure tag is counted as a cutoff. -/
theorem corrected_future_sliceBranch_eq_literalGate
    (u t q : Fin p.T) (hfuture : t.val + 1 < q.val) (x : X) :
    (x ∈ futureGate rate rewards C_star C_h u t q ↔
      (sliceBranch rate rewards C_star C_h u t q x).isSome = true) ∧
    (sliceBranch rate rewards C_star C_h u t q x = some false ↔
      x ∈ ReferenceFirstCollectionCorrectedSliceNumericalPrefix.correctedCell rate rewards C_star C_h u t ∧
        q.val - (t.val + 1) < (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail rate rewards C_star C_h x).length) ∧
    (sliceBranch rate rewards C_star C_h u t q x = some true ↔
      x ∈ ReferenceFirstCollectionCorrectedSliceNumericalPrefix.correctedCell rate rewards C_star C_h u t ∧
        q.val - (t.val + 1) = (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail rate rewards C_star C_h x).length ∧
        ReferenceFirstCollectionCorrectedSliceNumericalPrefix.cutoffDelta rate rewards C_star C_h x = 1) := by
  have hf := sliceBranch_false_iff rate rewards C_star C_h u t q hfuture x
  have ht := sliceBranch_true_iff rate rewards C_star C_h u t q hfuture x
  refine ⟨?_, hf, ht⟩
  have hp : (sliceBranch rate rewards C_star C_h u t q x).isSome = true ↔
      sliceBranch rate rewards C_star C_h u t q x = some false ∨
      sliceBranch rate rewards C_star C_h u t q x = some true := by
    cases sliceBranch rate rewards C_star C_h u t q x with
    | none => simp
    | some b => cases b <;> simp
  rw [hp, hf, ht]
  have hd := cutoffDelta_le_one rate rewards C_star C_h x
  change (x ∈ ReferenceFirstCollectionCorrectedSliceNumericalPrefix.correctedCell rate rewards C_star C_h u t ∧
    q.val < t.val + 1 + (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail rate rewards C_star C_h x).length +
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.cutoffDelta rate rewards C_star C_h x) ↔ _
  constructor
  · rintro ⟨hx, hq⟩
    by_cases hlt : q.val - (t.val + 1) < (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail rate rewards C_star C_h x).length
    · exact Or.inl ⟨hx, hlt⟩
    · exact Or.inr ⟨hx, by omega, by omega⟩
  · rintro (⟨hx, hlt⟩ | ⟨hx, he, hd⟩) <;> exact ⟨hx, by omega⟩


private theorem measurable_option_elim {A B : Type*} [MeasurableSpace A]
    [MeasurableSpace B] (f : A → B) (hf : Measurable f) (b : B) :
    Measurable (fun o : Option A => o.elim b f) := by
  have h : Measurable (Sum.elim f (fun _ : PUnit => b)) :=
    measurable_fun_sum hf measurable_const
  convert h.comp (comap_measurable (Equiv.optionEquivSumPUnit A)) using 1
  funext o
  cases o <;> rfl

private theorem measurable_optionBind {A B D : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace (Option D)]
    (f : A → Option B) (hf : Measurable f) (g : B → Option D) (hg : Measurable g) :
    Measurable (fun x => (f x).bind g) := by
  have he : Measurable (Equiv.optionEquivSumPUnit B) := comap_measurable _
  have hl : Measurable (Sum.elim g (fun _ : PUnit => (none : Option D))) :=
    measurable_fun_sum hg measurable_const
  convert hl.comp (he.comp hf) using 1
  funext x
  dsimp only [Function.comp_def]
  cases f x <;> rfl

/-- All strict-past flags are measurable in the existing original-source field. -/
theorem pastFlags_measurable (control0 : ContinuousLearningRows.TimeControl p) (q : Fin p.T) :
    Measurable[sourcePrefixFiltration control0 (q.val + 1)]
      (pastFlags rate rewards C_star C_h q) := by
  let : MeasurableSpace X := sourcePrefixFiltration control0 (q.val + 1)
  have hp := (ReferenceInspectedPastRoundObservations.pastRoundObservations_measurable_in_inspectedHistorySpace
    rate rewards C_star C_h q.val (Nat.le_of_lt q.isLt)).mono
      (ReferenceSourceOwnHistoryContainment.inspectedHistorySpace_le_sourcePrefixFiltration
        rate rewards C_star C_h control0 q.val (Nat.le_of_lt q.isLt)) le_rfl
  apply measurable_pi_iff.mpr
  intro j
  exact (measurable_option_elim _ (ReferenceFirstCollectionRenewalFutureFirstReplacementView.measurable_continuingCode rate) false).comp
    ((measurable_pi_apply j).comp hp)

/-- The finite universal test uses only strict-past observations. -/
theorem priorSlice_measurable (control0 : ContinuousLearningRows.TimeControl p) (t q : Fin p.T) :
    Measurable[sourcePrefixFiltration control0 (q.val + 1)]
      (priorSlice rate rewards C_star C_h t q) :=
  (measurable_of_countable (fun flags : Fin q.val → Bool =>
    decide (∀ j : Fin q.val, t.val + 1 ≤ j.val → flags j = true))).comp
      (pastFlags_measurable rate rewards C_star C_h control0 q)

/-- Equal strict prefixes preserve the complete strict-past test. -/
theorem priorSlice_congr (control0 : ContinuousLearningRows.TimeControl p)
    (t q : Fin p.T) (x y : X)
    (hprefix : sourcePrefix control0 q.val x = sourcePrefix control0 q.val y) :
    priorSlice rate rewards C_star C_h t q x = priorSlice rate rewards C_star C_h t q y := by
  have hm := priorSlice_measurable rate rewards C_star C_h control0 t q
  rw [sourcePrefixFiltration_succ] at hm
  exact hm.factorsThrough hprefix

private theorem dispatchTag_congr_all (left right : RoundInput p rate)
    (hstate : left.state = right.state) (htime : left.time = right.time) :
    ReferenceFirstCollectionRenewalNextRecordingPriorView.dispatchTag left = ReferenceFirstCollectionRenewalNextRecordingPriorView.dispatchTag right := by
  cases hs : left.state.coordinator with
  | live registers owned base =>
    exact ReferenceFirstCollectionRenewalNextRecordingPriorView.dispatchTag_congr left right hstate htime (by rw [hs]; trivial)
  | dagger =>
    exact ReferenceFirstCollectionRenewalNextRecordingPriorView.dispatchTag_congr left right hstate htime (by rw [hs]; trivial)
  | first =>
    simp only [ReferenceFirstCollectionRenewalNextRecordingPriorView.dispatchTag, dispatch, hs, ← hstate, CoordinatorRoundDispatch.dispatch]
    rfl
  | collection payload ledger saved =>
    by_cases hd : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
    · simp only [ReferenceFirstCollectionRenewalNextRecordingPriorView.dispatchTag, dispatch, hs, ← hstate, dite_eq_left hd,
        CoordinatorRoundDispatch.dispatch]
      rfl
    · simp only [ReferenceFirstCollectionRenewalNextRecordingPriorView.dispatchTag, dispatch, hs, ← hstate, dite_eq_right hd]

/-- The actual arm-erased current tag is fixed by the strict source prefix. -/
theorem rawTag_congr (control0 : ContinuousLearningRows.TimeControl p)
    (q : Fin p.T) (x y : X)
    (hprefix : sourcePrefix control0 q.val x = sourcePrefix control0 q.val y) :
    rawTag rate rewards C_star C_h q x = rawTag rate rewards C_star C_h q y := by
  have hi : incoming rate rewards C_star C_h q x = incoming rate rewards C_star C_h q y := by
    rw [incoming_factor rate rewards C_star C_h control0 q x,
      incoming_factor rate rewards C_star C_h control0 q y, hprefix]
  unfold incoming at hi
  cases hx : actualRecord rate rewards C_star C_h q x <;>
    cases hy : actualRecord rate rewards C_star C_h q y <;>
    simp only [hx, hy, Option.map_none, Option.map_some, reduceCtorEq] at hi
  · simp only [rawTag, hx, hy, Option.bind_none]
  · rename_i rx ry
    have hs : rx.input.state = ry.input.state :=
      ReferenceActivePhysicalStepMeasurability.encodeState_injective (Option.some.inj hi)
    have hfx := ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields
      rate rewards C_star C_h q x rx hx
    have hfy := ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields
      rate rewards C_star C_h q y ry hy
    simp only [rawTag, hx, hy, Option.bind_some]
    exact dispatchTag_congr_all rate rx.input ry.input hs (hfx.2.2.1.trans hfy.2.2.1.symm)

/-- Strict-prefix factorization of the actual tag on the whole original source. -/
theorem rawTag_factor (control0 : ContinuousLearningRows.TimeControl p) (q : Fin p.T) (x : X) :
    rawTag rate rewards C_star C_h q x =
      rawTag rate rewards C_star C_h q (sourcePrefix control0 q.val x) :=
  rawTag_congr rate rewards C_star C_h control0 q x _
    (sourcePrefix_sourcePrefix control0 q.val q.val le_rfl x).symm

/-- Ambient Borelness of the actual tag uses the existing continuous input code. -/
theorem rawTag_measurable (q : Fin p.T) : Measurable (rawTag rate rewards C_star C_h q) := by
  have h := measurable_optionBind (ReferenceFirstCollectionCorrectedNextPhysicalReadout.actualInput? rate rewards C_star C_h q)
    (ReferenceFirstCollectionCorrectedNextPhysicalReadout.measurable_actualInput? rate rewards C_star C_h q)
    ReferenceFirstCollectionRenewalNextRecordingPriorView.dispatchTag ReferenceFirstCollectionRenewalNextRecordingPriorView.measurable_dispatchTag
  convert h using 1
  funext x
  simp only [rawTag, ReferenceFirstCollectionCorrectedNextPhysicalReadout.actualInput?, Option.bind_map, Function.comp_def]

/-- The current tag is measurable before the whole current control is exposed. -/
theorem rawTag_prior_measurable (control0 : ContinuousLearningRows.TimeControl p) (q : Fin p.T) :
    Measurable[sourcePrefixFiltration control0 (q.val + 1)] (rawTag rate rewards C_star C_h q) := by
  rw [sourcePrefixFiltration_succ]
  have hm := (rawTag_measurable rate rewards C_star C_h q).comp
    (comap_measurable (sourcePrefix control0 q.val))
  convert hm using 1
  funext x
  exact rawTag_factor rate rewards C_star C_h control0 q x

/-- The corrected birth event is already in every later strict-prior field. -/
theorem correctedCell_prior_measurable (control0 : ContinuousLearningRows.TimeControl p)
    (u t q : Fin p.T) (hfuture : t.val + 1 < q.val) :
    MeasurableSet[sourcePrefixFiltration control0 (q.val + 1)]
      (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.correctedCell rate rewards C_star C_h u t) :=
  (sourcePrefixFiltration control0).mono (by omega : t.val + 2 ≤ q.val + 1) _
    (ReferenceFirstCollectionCorrectedNextRetainedGate.firstCell_successorBranch_measurable
      rate rewards C_star C_h control0 u t)

/-- The chosen branch, including every actual failure alternative, is predictable. -/
theorem sliceBranch_measurable (control0 : ContinuousLearningRows.TimeControl p)
    (u t q : Fin p.T) (hfuture : t.val + 1 < q.val) :
    Measurable[sourcePrefixFiltration control0 (q.val + 1)]
      (sliceBranch rate rewards C_star C_h u t q) := by
  let : MeasurableSpace X := sourcePrefixFiltration control0 (q.val + 1)
  have hE := correctedCell_prior_measurable rate rewards C_star C_h control0 u t q hfuture
  have hprior := measurableSet_eq_fun
    (priorSlice_measurable rate rewards C_star C_h control0 t q) (measurable_const (a := true))
  have htag := (measurable_of_countable (fun tag : Option (ReferenceFirstCollectionRenewalNextRecordingPriorView.LiveTag p) =>
    match tag with
    | some (.inr (.inr (.inr (_, cutoff)))) => some cutoff
    | _ => none)).comp (rawTag_prior_measurable rate rewards C_star C_h control0 q)
  exact htag.ite (hE.inter hprior) measurable_const

/-- Literal membership is predictable by chronology, without any endDate invariance claim. -/
theorem futureGate_measurable (control0 : ContinuousLearningRows.TimeControl p)
    (u t q : Fin p.T) (hfuture : t.val + 1 < q.val) :
    MeasurableSet[sourcePrefixFiltration control0 (q.val + 1)]
      (futureGate rate rewards C_star C_h u t q) := by
  have hm := sliceBranch_measurable rate rewards C_star C_h control0 u t q hfuture
  have hs := hm (MeasurableSet.of_discrete : MeasurableSet {b : Option Bool | b.isSome = true})
  convert hs using 1
  ext x
  exact (corrected_future_sliceBranch_eq_literalGate rate rewards C_star C_h u t q hfuture x).1

/-- The complete branch factors through the existing strict prefix. -/
theorem sliceBranch_congr (control0 : ContinuousLearningRows.TimeControl p)
    (u t q : Fin p.T) (hfuture : t.val + 1 < q.val) (x y : X)
    (hprefix : sourcePrefix control0 q.val x = sourcePrefix control0 q.val y) :
    sliceBranch rate rewards C_star C_h u t q x = sliceBranch rate rewards C_star C_h u t q y := by
  have hm := sliceBranch_measurable rate rewards C_star C_h control0 u t q hfuture
  rw [sourcePrefixFiltration_succ] at hm
  exact hm.factorsThrough hprefix

/-- The literal update gate factors through the strict prefix. -/
theorem futureGate_congr (control0 : ContinuousLearningRows.TimeControl p)
    (u t q : Fin p.T) (hfuture : t.val + 1 < q.val) (x y : X)
    (hprefix : sourcePrefix control0 q.val x = sourcePrefix control0 q.val y) :
    x ∈ futureGate rate rewards C_star C_h u t q ↔
      y ∈ futureGate rate rewards C_star C_h u t q := by
  rw [(corrected_future_sliceBranch_eq_literalGate rate rewards C_star C_h u t q hfuture x).1,
    (corrected_future_sliceBranch_eq_literalGate rate rewards C_star C_h u t q hfuture y).1,
    sliceBranch_congr rate rewards C_star C_h control0 u t q hfuture x y hprefix]


private theorem live_cell (u t q : Fin p.T) (hfuture : t.val + 1 < q.val) (x : X)
    (hx : x ∈ ReferenceFirstCollectionCorrectedSliceNumericalPrefix.correctedCell rate rewards C_star C_h u t)
    (r : Record) (har : actualRecord rate rewards C_star C_h q x = some r)
    (hk : q.val - (t.val + 1) < (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail rate rewards C_star C_h x).length) :
    ∃ cell : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell r,
      ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r = some cell.input ∧ cell.input.enabled = true ∧
      cell.selected.view.payload.sigma = t ∧
      cell.input.reward = (fun a => ((rewards q a).val : ℝ) / (D p : ℝ)) := by
  have h := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.firstCell_continuing_cells rate rewards C_star C_h u t x hx
    ⟨q.val - (t.val + 1), hk⟩
  obtain ⟨r', har', hlookup⟩ := future_record_exists rate rewards C_star C_h u t q hfuture x hx
  have he : r' = r := Option.some.inj (har'.symm.trans har)
  subst r'
  have heq : (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail rate rewards C_star C_h x).get ⟨q.val - (t.val + 1), hk⟩ = r :=
    Option.some.inj (h.1.symm.trans hlookup)
  rw [heq] at h
  obtain ⟨_, _, _, _, _, _, cell, hc, hen, hsig, hrew⟩ := h
  have hf := ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields
    rate rewards C_star C_h q x r har
  exact ⟨cell, hc, hen, hsig, by simpa only [hf.2.2.1] using hrew⟩

private theorem cutoff_prepared (u t q : Fin p.T) (hfuture : t.val + 1 < q.val) (x : X)
    (hx : x ∈ ReferenceFirstCollectionCorrectedSliceNumericalPrefix.correctedCell rate rewards C_star C_h u t)
    (r : Record) (har : actualRecord rate rewards C_star C_h q x = some r)
    (hend : q.val - (t.val + 1) = (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail rate rewards C_star C_h x).length) :
    match r.output.preparation.coordinator with
    | .live registers _ _ (.cutoffChosen ..) =>
      0 < registers.payload.sigma.val ∧ registers.payload.sigma = t ∧
      ∀ i : Fin (p.m - 1), ∃ state memory,
        (r.output.preparation.followers.followers i).configuration = .ordinary state memory ∧
        state.status = .unoccupied
    | _ => True := by
  obtain ⟨birth, hb, _hbactual, ht, hchosen⟩ :=
    ReferenceFirstCollectionCorrectedNextPhysicalReadout.firstCell_firstReplacement_record rate rewards C_star C_h u t x hx.1
  have hcut := ReferenceFirstReplacementCutoffPreparedBoundary.complete_first_replacement_cutoff_follower_boundary
    rate x rewards C_star C_h
  dsimp only at hcut
  simp only [hb] at hcut
  have hp : birth.output.preparation = prepare birth.input := by rw [birth.output_eq]; rfl
  unfold ReferenceCollectionPhaseHistory.laterChosen at hchosen
  rw [← hp] at hchosen
  cases hc : birth.output.preparation.coordinator <;> simp only [hc, Bool.false_eq_true] at hchosen
  rename_i out
  cases out <;> simp only at hchosen <;> try contradiction
  rw [hc] at hcut
  dsimp only at hcut
  obtain ⟨r', har', hlookup⟩ := future_record_exists rate rewards C_star C_h u t q hfuture x hx
  have he : r' = r := Option.some.inj (har'.symm.trans har)
  subst r'
  rw [hend] at hlookup
  change (match (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords rate rewards C_star C_h x)[ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex rate rewards C_star C_h x +
    1 + (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail rate rewards C_star C_h x).length]? with
    | none => True | some r => _) at hcut
  rw [hlookup] at hcut
  dsimp only at hcut
  cases hr : r.output.preparation.coordinator <;> try trivial
  rename_i registers owned base out
  cases out <;> try trivial
  rw [hr] at hcut
  obtain ⟨_, hpay, _, _, _, _, _, hsigma, hbase, _, _, _, selected, _, _, _, _, hf⟩ := hcut
  refine ⟨?_, ?_, ?_⟩
  · rw [hpay]
    omega
  · apply Fin.ext
    rw [hpay, hsigma, ht]
  · intro i
    obtain ⟨old, memory, _, _, _, _, _, _, _, _, hconfig, _⟩ := hf i
    exact ⟨{ old with status := .unoccupied }, memory, hconfig, rfl⟩

private theorem selected_ordinary (u t q : Fin p.T) (hfuture : t.val + 1 < q.val) (x : X)
    (hx : x ∈ futureGate rate rewards C_star C_h u t q)
    (r : Record) (har : actualRecord rate rewards C_star C_h q x = some r) :
    ∃ (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
      (memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p),
      ∀ i, (r.output.preparation.followers.followers i).configuration = .ordinary (states i) (memories i) := by
  have hb := (corrected_future_sliceBranch_eq_literalGate rate rewards C_star C_h u t q hfuture x).1.mp hx
  cases hbranch : sliceBranch rate rewards C_star C_h u t q x with
  | none => simp only [hbranch, Option.isSome_none, Bool.false_eq_true] at hb
  | some b =>
    cases b with
    | false =>
      have hk := ((sliceBranch_false_iff rate rewards C_star C_h u t q hfuture x).mp hbranch).2
      obtain ⟨cell, _⟩ := live_cell rate rewards C_star C_h u t q hfuture x hx.1 r har hk
      exact ⟨cell.states, cell.memories, cell.ordinary⟩
    | true =>
      have hend := ((sliceBranch_true_iff rate rewards C_star C_h u t q hfuture x).mp hbranch).2.1
      have hf := cutoff_prepared rate rewards C_star C_h u t q hfuture x hx.1 r har hend
      have htag := hbranch
      rw [sliceBranch, ite_eq_left ⟨hx.1, by
        rw [priorSlice_eq rate rewards C_star C_h u t q hfuture x hx.1, hend]
        simp⟩, rawTag_record rate rewards C_star C_h q x r har] at htag
      cases hc : r.output.preparation.coordinator <;> simp only [hc] at htag <;> try contradiction
      rename_i out
      cases out <;> simp only [ReferenceFirstCollectionRenewalNextRecordingPriorView.eraseArm, ReferenceLiveDispatchOutputMeasurability.outcomeData,
        Option.some.injEq, Bool.false_eq_true, reduceCtorEq] at htag
      rw [hc] at hf
      choose states memories hconfig hstatus using hf.2.2
      exact ⟨states, memories, hconfig⟩


private theorem gate_branch (u t q : Fin p.T) (hfuture : t.val + 1 < q.val) (x : X)
    (hx : x ∈ futureGate rate rewards C_star C_h u t q)
    (r : Record) (har : actualRecord rate rewards C_star C_h q x = some r) :
    sliceBranch rate rewards C_star C_h u t q x =
      match r.output.preparation.coordinator with
      | .live _ _ _ (.continuingChosen ..) => some false
      | .live _ _ _ (.cutoffChosen ..) => some true
      | _ => none := by
  have hd := cutoffDelta_le_one rate rewards C_star C_h x
  have hn : q.val - (t.val + 1) ≤ (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail rate rewards C_star C_h x).length := by
    have he := hx.2
    change q.val < t.val + 1 + (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail rate rewards C_star C_h x).length +
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.cutoffDelta rate rewards C_star C_h x at he
    omega
  have hp : priorSlice rate rewards C_star C_h t q x = true := by
    rw [priorSlice_eq rate rewards C_star C_h u t q hfuture x hx.1]
    exact decide_eq_true hn
  rw [sliceBranch, ite_eq_left ⟨hx.1, hp⟩, rawTag_record rate rewards C_star C_h q x r har]
  cases r.output.preparation.coordinator <;> try rfl
  rename_i out
  cases out <;> rfl

private theorem record_shape (u t q : Fin p.T) (hfuture : t.val + 1 < q.val) (x : X)
    (hx : x ∈ futureGate rate rewards C_star C_h u t q)
    (r : Record) (har : actualRecord rate rewards C_star C_h q x = some r) :
    match r.output.preparation.coordinator with
    | .live _ _ _ (.continuingChosen ..) => True
    | .live _ _ _ (.cutoffChosen ..) => True
    | _ => False := by
  have hb := (corrected_future_sliceBranch_eq_literalGate rate rewards C_star C_h u t q hfuture x).1.mp hx
  rw [gate_branch rate rewards C_star C_h u t q hfuture x hx r har] at hb
  cases hc : r.output.preparation.coordinator <;> simp only [hc, Option.isSome_none, Bool.false_eq_true] at hb
  rename_i out
  cases out <;> simp_all only [Option.isSome_none, Bool.false_eq_true]

private theorem cutoff_cell (u t q : Fin p.T) (hfuture : t.val + 1 < q.val) (x : X)
    (hx : x ∈ futureGate rate rewards C_star C_h u t q)
    (r : Record) (har : actualRecord rate rewards C_star C_h q x = some r) :
    match r.output.preparation.coordinator with
    | .live registers owned base (.cutoffChosen dispatched _ _ _ _ _ _ _ _ selected) =>
      ∃ c : RecordedQueueRun.RoundInput p.K,
        ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r = some c ∧
        c = ReferenceLaterCollectionArrivalReadout.laterCutoffCollectionInput r registers owned base dispatched selected ∧
        c.enabled = decide (q.val + 1 < FollowerCutoffScan.gridBoundary p rate.eta.val t) ∧
        c.reward = (fun a => ((rewards q a).val : ℝ) / (D p : ℝ))
    | _ => True := by
  cases hc : r.output.preparation.coordinator <;> try trivial
  rename_i registers owned base out
  cases out <;> try trivial
  rename_i dispatched hs ledger hi hledger hdomain hclock hpending hstart selected
  have hbranch := gate_branch rate rewards C_star C_h u t q hfuture x hx r har
  rw [hc] at hbranch
  have hend := ((sliceBranch_true_iff rate rewards C_star C_h u t q hfuture x).mp hbranch).2.1
  have hprep := cutoff_prepared rate rewards C_star C_h u t q hfuture x hx.1 r har hend
  rw [hc] at hprep
  have ho : ReferenceLaterCollectionArrivalReadout.preparedFollowersUnoccupied r := by
    intro i
    obtain ⟨state, memory, hp, hu⟩ := hprep.2.2 i
    simp only [hp, hu]
  have hread : ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 r =
      some (ReferenceLaterCollectionArrivalReadout.laterCutoffCollectionInput r registers owned base dispatched selected) := by
    simp only [ReferenceLaterCollectionArrivalReadout.laterCollectionReadout,
      dite_eq_left ho, hc, dite_eq_left hprep.1]
  have hcut := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.firstCell_cutoff_cell rate rewards C_star C_h u t x hx.1
  obtain ⟨r', har', hlookup⟩ := future_record_exists rate rewards C_star C_h u t q hfuture x hx.1
  have he : r' = r := Option.some.inj (har'.symm.trans har)
  subst r'
  rw [hend] at hlookup
  rw [hlookup] at hcut
  dsimp only at hcut
  rw [hc] at hcut
  obtain ⟨_, _, _, _, _, _, c, hcell, henabled, hreward⟩ := hcut
  have hL : ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r = none := by
    simp [ReferenceLaterLiveNumericalReadout.laterLiveReadout, hc, DispatchCut.selection,
      selectionAt, liveInput, liveRegistersAt, CoordinatorLocalArmChoice.assignmentIsLive, hclock,
      CoordinatorLiveChoiceRecorderStep.cutoffFromClock, CoordinatorLocalArmChoice.cutoffRound,
      CoordinatorLocalArmChoice.sourceRound]
  have heq : c = ReferenceLaterCollectionArrivalReadout.laterCutoffCollectionInput r registers owned base dispatched selected := by
    simp only [ReferenceFirstCollectionCurrentRetainedGate.cell0, hL, Option.none_or, hread, Option.some.injEq] at hcell
    exact hcell.symm
  have hf := ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields rate rewards C_star C_h q x r har
  exact ⟨c, hcell, heq, by simpa only [hf.2.2.1] using henabled,
    by simpa only [hf.2.2.1] using hreward⟩


private theorem record_parameters (u t q : Fin p.T) (hfuture : t.val + 1 < q.val) (x : X)
    (hx : x ∈ futureGate rate rewards C_star C_h u t q)
    (r : Record) (har : actualRecord rate rewards C_star C_h q x = some r) :
    (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r).map (fun c => (c.enabled, c.rate)) =
      ReferenceFirstCollectionRenewalNextRecordingPriorView.parametersOfTag rate r.input.time (ReferenceFirstCollectionRenewalNextRecordingPriorView.dispatchTag r.input) r.output.preparation.coordinator.downView := by
  have hshape := record_shape rate rewards C_star C_h u t q hfuture x hx r har
  have htag := rawTag_record rate rewards C_star C_h q x r har
  simp only [rawTag, har, Option.bind_some] at htag
  rw [htag]
  cases hd : r.output.preparation.coordinator <;> simp only [hd] at hshape
  rename_i registers owned base out
  cases out <;> simp only at hshape
  case cutoffChosen dispatched hs ledger hi hledger hdomain hclock hpending hstart selected =>
    have hcut := cutoff_cell rate rewards C_star C_h u t q hfuture x hx r har
    rw [hd] at hcut
    obtain ⟨c, hcell, hvalue, _, _⟩ := hcut
    simp only [hcell, Option.map_some]
    rw [hvalue]
    simp only [ReferenceFirstCollectionRenewalNextRecordingPriorView.parametersOfTag, Option.bind_some, ReferenceFirstCollectionRenewalNextRecordingPriorView.eraseArm,
      ReferenceLiveDispatchOutputMeasurability.outcomeData, DispatchCut.downView,
      DispatchCut.selection, selectionAt, dite_true, Option.map_some]
    simp [ReferenceLaterCollectionArrivalReadout.laterCutoffCollectionInput,
      CoordinatorRecordingOperation.isFrozen, CoordinatorRecordingOperation.sourceCalendarRound,
      CoordinatorRecorderComplementBridge.recorderInput, CoordinatorRecorderComplementBridge.recorderInputWithWeights,
      CoordinatorRecorderComplementBridge.sourceStart, collectionRecordingInput,
      ReferenceLiveDispatchOutputMeasurability.dispatchData]
    rfl
  case continuingChosen dispatched hs continuation selected =>
    have hbranch := gate_branch rate rewards C_star C_h u t q hfuture x hx r har
    rw [hd] at hbranch
    have hk := ((sliceBranch_false_iff rate rewards C_star C_h u t q hfuture x).mp hbranch).2
    obtain ⟨cell, hcell, _, _, _⟩ := live_cell rate rewards C_star C_h u t q hfuture x hx.1 r har hk
    have hsel := cell.selection_actual
    rw [hd] at hsel
    simp only [DispatchCut.selection, selectionAt, dite_true, Option.some.injEq] at hsel
    have hp := congrArg (fun selected => selected.view.payload) hsel
    have hrate : cell.input.rate = cell.selected.view.payload.rate := by rw [cell.input_eq]; rfl
    simp only [hcell, Option.map_some, ReferenceFirstCollectionRenewalNextRecordingPriorView.parametersOfTag, Option.bind_some,
      ReferenceFirstCollectionRenewalNextRecordingPriorView.eraseArm, ReferenceLiveDispatchOutputMeasurability.outcomeData,
      DispatchCut.downView, DispatchCut.selection, selectionAt, dite_true,
      cell.enabled, hrate, ← hp]
    rfl

/-- Actual LIVE and first-cutoff recording kernels, with every physical witness produced. -/
theorem corrected_future_physical_kernel (u t q : Fin p.T) (hfuture : t.val + 1 < q.val) (x : X) :
    match futureRecordingView rate rewards C_star C_h u t q x with
    | none => futureCell rate rewards C_star C_h u t q x = none ∧
        futureMarker rate rewards C_star C_h u t q x = none
    | some (parameters, view, code) =>
      ∃ (r : Record) (c : RecordedQueueRun.RoundInput p.K) (selected : Selection r.input)
        (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
        (memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p)
        (snapshot : Option (ActiveRoundActions.Snapshot view.payload.assignment))
        (valid : CoordinatorLocalArmChoice.ChoiceInputsValid view.payload view.cutoff q view.complementWeights),
        actualRecord rate rewards C_star C_h q x = some r ∧ r.input.time = q ∧
        r.input.rows = x.1.2 ∧ r.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p x ∧
        r.input.rewards = rewards ∧ ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r = some c ∧
        r.output.preparation.coordinator.selection = some selected ∧ selected.view = view ∧
        (∀ i, (r.output.preparation.followers.followers i).configuration = .ordinary (states i) (memories i)) ∧
        (sliceBranch rate rewards C_star C_h u t q x = some false → snapshot = some
          {missing := view.pendingAtChoice, status := fun i => (states i).status} ∧ c.enabled = true) ∧
        (sliceBranch rate rewards C_star C_h u t q x = some true → snapshot = none ∧
          (∀ i, (states i).status = .unoccupied) ∧
          c.enabled = decide (q.val + 1 < FollowerCutoffScan.gridBoundary p rate.eta.val t)) ∧
        futureCell rate rewards C_star C_h u t q x = some c ∧ parameters = some (c.enabled, c.rate) ∧
        c.rate = view.payload.rate ∧ c.reward = (fun a => ((rewards q a).val : ℝ) / (D p : ℝ)) ∧
        code = snapshot.map (fun z => (z.missing, fun i => some
          (FollowerDownMeasurability.followerStatusCode (z.status i)))) ∧
        c.recordedArm = SnapshotRecordingKernel.recordingMap p
          (snapshot.elim .collection (fun z => .live view.payload.assignment z)) c.enabled
          rate.eta.val rate.eta.property rate.sourceCap view.payload.anchor
          (ReferenceFirstWindowNumericalStream.sourceWeights view.payload view.complementWeights)
          view.payload.anchor_pos
          (ReferenceFirstWindowNumericalStream.sourceWeights_pos _ _ _ _ valid)
          (ReferenceFirstWindowNumericalStream.sourceWeights_lower _ _ _ _ valid)
          (ReferenceFirstWindowNumericalStream.sourceWeights_upper _ _ _ _ valid)
          (ContinuousLearningRows.sliceAt q (x.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p x)).2) := by
  by_cases hg : x ∈ futureGate rate rewards C_star C_h u t q
  · obtain ⟨r, har, _⟩ := future_record_exists rate rewards C_star C_h u t q hfuture x hg.1
    have hf := ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields rate rewards C_star C_h q x r har
    have ht := hf.2.2.1
    subst q
    have hrow : r.input.row = x.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p x) := by
      simp only [RoundInput.row, hf.1, hf.2.1]
    have hshape := record_shape rate rewards C_star C_h u t r.input.time hfuture x hg r har
    have hb := gate_branch rate rewards C_star C_h u t r.input.time hfuture x hg r har
    have htag := rawTag_record rate rewards C_star C_h r.input.time x r har
    simp only [rawTag, har, Option.bind_some] at htag
    simp only [futureRecordingView, ite_eq_left hg, har, Option.bind_some]
    cases hd : r.output.preparation.coordinator <;> simp only [hd] at hshape
    rename_i registers owned base out
    cases out <;> simp only at hshape
    case cutoffChosen dispatched hs ledger hi hledger hdomain hclock hpending hstart arm =>
      have hc := cutoff_cell rate rewards C_star C_h u t r.input.time hfuture x hg r har
      have hp := cutoff_prepared rate rewards C_star C_h u t r.input.time hfuture x hg.1 r har
        ((sliceBranch_true_iff rate rewards C_star C_h u t r.input.time hfuture x).mp (by simpa only [hd] using hb)).2.1
      rw [hd] at hc hp htag hb
      obtain ⟨c, hcell, hvalue, hen, hrew⟩ := hc
      choose states memories hconfig hstatus using hp.2.2
      simp only [ReferenceFirstCollectionCorrectedNextPhysicalReadout.recordRecordingView, hd, DispatchCut.downView, DispatchCut.selection,
        selectionAt, dite_true, Option.map_some, htag, ReferenceFirstCollectionRenewalNextRecordingPriorView.eraseArm,
        ReferenceLiveDispatchOutputMeasurability.outcomeData, ReferenceFirstCollectionRenewalNextRecordingPriorView.isCutoffTag, ite_true, hcell]
      let chosen : Selection r.input := {
        view := {
          payload := registers.payload
          pendingAtChoice := dispatched.startResult.pending
          cutoff := CoordinatorLiveChoiceRecorderStep.cutoffFromClock p dispatched.startResult.clock.u
          complementWeights := (liveRegistersAt registers r.input.time).complementWeights }
        started := dispatched.startResult
        pending_eq := rfl
        cutoff_eq := rfl
        arm := arm.arm
        choice_eq := arm.armChoice_eq }
      refine ⟨r, c, chosen, states, memories, none, arm.choiceInputsValid, rfl, rfl, hf.1, hf.2.1,
        hf.2.2.2, hcell, ?_, rfl, hconfig, ?_, ?_, ?_, rfl, ?_, hrew, rfl, ?_⟩
      · simp only [hd]
        rfl
      · intro hfalse
        rw [hb] at hfalse
        cases hfalse
      · exact fun _ => ⟨rfl, hstatus, hen⟩
      · simp only [futureCell, ite_eq_left hg, har, Option.bind_some, hcell]
      · rw [hvalue]
        rfl
      · rw [hvalue, ← hrow]
        rfl
    case continuingChosen dispatched hs continuation arm =>
      rw [hd] at hb htag
      have hk := ((sliceBranch_false_iff rate rewards C_star C_h u t r.input.time hfuture x).mp hb).2
      obtain ⟨cell, hcell, hen, _hsigma, hrew⟩ := live_cell rate rewards C_star C_h u t r.input.time hfuture x hg.1 r har hk
      have hv : r.output.preparation.coordinator.downView = some cell.selected.view := by
        simp only [DispatchCut.downView, cell.selection_actual, Option.map_some]
      have hrate : cell.input.rate = cell.selected.view.payload.rate := by rw [cell.input_eq]; rfl
      simp only [ReferenceFirstCollectionCorrectedNextPhysicalReadout.recordRecordingView, hv, Option.map_some, hcell, htag,
        ReferenceFirstCollectionRenewalNextRecordingPriorView.eraseArm, ReferenceLiveDispatchOutputMeasurability.outcomeData, ReferenceFirstCollectionRenewalNextRecordingPriorView.isCutoffTag,
        Bool.false_eq_true, ite_false]
      refine ⟨r, cell.input, cell.selected, cell.states, cell.memories,
        some (ReferenceActiveDataOwnership.choiceSnapshot cell.selected cell.states),
        cell.choiceInputsValid, rfl, rfl, hf.1, hf.2.1, hf.2.2.2, hcell, cell.selection_actual,
        rfl, cell.ordinary, ?_, ?_, ?_, rfl, hrate, hrew, ?_, ?_⟩
      · intro _
        refine ⟨?_, hen⟩
        simp only [ReferenceActiveDataOwnership.choiceSnapshot, cell.selected.pending_eq]
      · intro htrue
        rw [hb] at htrue
        cases htrue
      · simp only [futureCell, ite_eq_left hg, har, Option.bind_some, hcell]
      · simp only [Option.map_some, cell.selected.pending_eq]
        congr 2
        funext i
        simp only [ReferenceFirstCollectionCorrectedNextPhysicalReadout.recordStatuses, cell.ordinary i, ReferenceFirstCollectionRenewalNextRecordingPriorView.configurationStatus,
          ReferenceActiveDataOwnership.choiceSnapshot]
      · rw [cell.recordedArm_eq]
        unfold ReferenceFirstWindowNumericalStream.sourceArm
        simp only [hen, Option.elim_some, ReferenceActiveDataOwnership.choiceSnapshot,
          cell.selected.pending_eq, ← hrow, ContinuousLearningRows.sliceAt]
  · simp only [futureRecordingView, futureCell, futureMarker, ite_eq_right hg, Option.map_none, and_self]


private theorem dispatch_live_origin (input : RoundInput p rate) :
    match dispatch input with
    | .live r owned base _ => input.state.coordinator = .live r owned base
    | _ => True := by
  unfold dispatch
  cases hs : input.state.coordinator with
  | first => trivial
  | live r owned base =>
    simp only [CoordinatorRoundDispatch.dispatch]
    cases CoordinatorRoundDispatch.dispatchLive (liveInput input r owned base) <;> rfl
  | collection payload ledger saved =>
    by_cases hc : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
    · simp only [dite_eq_left hc, CoordinatorRoundDispatch.dispatch]
      cases CoordinatorRoundDispatch.dispatchCollection
        (collectionInput input payload ledger
          (collectionClock payload ledger saved ⟨ledger.cutoff - 1, by omega⟩)
          ⟨ledger.cutoff - 1, by omega⟩) <;> trivial
    · simp only [dite_eq_right hc]
  | dagger => trivial

private theorem record_input_phase (u t q : Fin p.T) (hfuture : t.val + 1 < q.val) (x : X)
    (hx : x ∈ futureGate rate rewards C_star C_h u t q)
    (r : Record) (har : actualRecord rate rewards C_star C_h q x = some r) :
    match r.input.state.coordinator with | .live .. => True | .dagger => True | _ => False := by
  have hs := record_shape rate rewards C_star C_h u t q hfuture x hx r har
  have ho := dispatch_live_origin rate r.input
  have hd : dispatch r.input = r.output.preparation.coordinator := by rw [r.output_eq]; rfl
  rw [hd] at ho
  cases hc : r.output.preparation.coordinator <;> simp only [hc] at hs ho
  rw [ho]
  trivial

private theorem record_view_congr (control0 : ContinuousLearningRows.TimeControl p)
    (u t q : Fin p.T) (hfuture : t.val + 1 < q.val) (x y : X)
    (hx : x ∈ futureGate rate rewards C_star C_h u t q)
    (hy : y ∈ futureGate rate rewards C_star C_h u t q)
    (hprefix : sourcePrefix control0 q.val x = sourcePrefix control0 q.val y)
    (r r' : Record) (hr : actualRecord rate rewards C_star C_h q x = some r)
    (hr' : actualRecord rate rewards C_star C_h q y = some r') :
    ReferenceFirstCollectionCorrectedNextPhysicalReadout.recordRecordingView rate r = ReferenceFirstCollectionCorrectedNextPhysicalReadout.recordRecordingView rate r' := by
  have hi : incoming rate rewards C_star C_h q x = incoming rate rewards C_star C_h q y := by
    rw [incoming_factor rate rewards C_star C_h control0 q x,
      incoming_factor rate rewards C_star C_h control0 q y, hprefix]
  simp only [incoming, hr, hr', Option.map_some, Option.some.injEq] at hi
  have hs := ReferenceActivePhysicalStepMeasurability.encodeState_injective hi
  have hf := ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields rate rewards C_star C_h q x r hr
  have hf' := ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields rate rewards C_star C_h q y r' hr'
  have htime : r.input.time = r'.input.time := hf.2.2.1.trans hf'.2.2.1.symm
  have hphase := record_input_phase rate rewards C_star C_h u t q hfuture x hx r hr
  have htag := ReferenceFirstCollectionRenewalNextRecordingPriorView.dispatchTag_congr r.input r'.input hs htime hphase
  have hv : r.output.preparation.coordinator.downView = r'.output.preparation.coordinator.downView := by
    rw [r.output_eq, r'.output_eq]
    exact ReferenceFirstCollectionRenewalNextRecordingPriorView.downView_congr r.input r'.input hs htime hphase
  have hp : (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r).map (fun c => (c.enabled, c.rate)) =
      (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r').map (fun c => (c.enabled, c.rate)) := by
    rw [record_parameters rate rewards C_star C_h u t q hfuture x hx r hr,
      record_parameters rate rewards C_star C_h u t q hfuture y hy r' hr', htime, htag, hv]
  obtain ⟨sl, ml, hol⟩ := selected_ordinary rate rewards C_star C_h u t q hfuture x hx r hr
  obtain ⟨sr, mr, hor⟩ := selected_ordinary rate rewards C_star C_h u t q hfuture y hy r' hr'
  have hstatuses : ReferenceFirstCollectionCorrectedNextPhysicalReadout.recordStatuses rate r = ReferenceFirstCollectionCorrectedNextPhysicalReadout.recordStatuses rate r' := by
    funext i
    have hol' : ((prepare r.input).followers.followers i).configuration = .ordinary (sl i) (ml i) := by
      rw [← show r.output.preparation = prepare r.input by rw [r.output_eq]; rfl]
      exact hol i
    have hor' : ((prepare r'.input).followers.followers i).configuration = .ordinary (sr i) (mr i) := by
      rw [← show r'.output.preparation = prepare r'.input by rw [r'.output_eq]; rfl]
      exact hor i
    have he := ReferenceFirstCollectionRenewalNextRecordingPriorView.ordinary_preparation_congr r.input r'.input hs htime i (sl i) (sr i) (ml i) (mr i) hol' hor'
    simp only [ReferenceFirstCollectionCorrectedNextPhysicalReadout.recordStatuses, hol i, hor i, ReferenceFirstCollectionRenewalNextRecordingPriorView.configurationStatus, he.1]
  simp only [ReferenceFirstCollectionCorrectedNextPhysicalReadout.recordRecordingView, hp, hv, htag, hstatuses]

/-- The actual complete optional view depends only on the strict source prefix. -/
theorem corrected_future_recordingView_congr (control0 : ContinuousLearningRows.TimeControl p)
    (u t q : Fin p.T) (hfuture : t.val + 1 < q.val) (x y : X)
    (hprefix : sourcePrefix control0 q.val x = sourcePrefix control0 q.val y) :
    futureRecordingView rate rewards C_star C_h u t q x =
      futureRecordingView rate rewards C_star C_h u t q y := by
  have hgate := futureGate_congr rate rewards C_star C_h control0 u t q hfuture x y hprefix
  by_cases hx : x ∈ futureGate rate rewards C_star C_h u t q
  · have hy := hgate.mp hx
    obtain ⟨r, hr, _⟩ := future_record_exists rate rewards C_star C_h u t q hfuture x hx.1
    obtain ⟨r', hr', _⟩ := future_record_exists rate rewards C_star C_h u t q hfuture y hy.1
    simp only [futureRecordingView, ite_eq_left hx, ite_eq_left hy, hr, hr', Option.bind_some]
    exact record_view_congr rate rewards C_star C_h control0 u t q hfuture x y hx hy hprefix r r' hr hr'
  · have hy := mt hgate.mpr hx
    simp only [futureRecordingView, ite_eq_right hx, ite_eq_right hy]

/-- Strict sourcePrefix factorization, preserving the entire sender view and prepared code. -/
theorem corrected_future_recordingView_factor (control0 : ContinuousLearningRows.TimeControl p)
    (u t q : Fin p.T) (hfuture : t.val + 1 < q.val) (x : X) :
    futureRecordingView rate rewards C_star C_h u t q x =
      futureRecordingView rate rewards C_star C_h u t q (sourcePrefix control0 q.val x) :=
  corrected_future_recordingView_congr rate rewards C_star C_h control0 u t q hfuture x _
    (sourcePrefix_sourcePrefix control0 q.val q.val le_rfl x).symm


/-- Presence and parameters retain outer absence and present bottom markers separately. -/
theorem corrected_future_recordingView_presence (u t q : Fin p.T)
    (hfuture : t.val + 1 < q.val) (x : X) :
    (futureRecordingView rate rewards C_star C_h u t q x).isSome =
        (sliceBranch rate rewards C_star C_h u t q x).isSome ∧
    (futureCell rate rewards C_star C_h u t q x).isSome =
        (sliceBranch rate rewards C_star C_h u t q x).isSome ∧
    futureParameters rate rewards C_star C_h u t q x =
      (futureRecordingView rate rewards C_star C_h u t q x).bind Prod.fst := by
  have hv : (futureRecordingView rate rewards C_star C_h u t q x).isSome =
      (sliceBranch rate rewards C_star C_h u t q x).isSome := by
    apply Bool.eq_iff_iff.mpr
    rw [← (corrected_future_sliceBranch_eq_literalGate rate rewards C_star C_h u t q hfuture x).1]
    by_cases hg : x ∈ futureGate rate rewards C_star C_h u t q
    · obtain ⟨r, har, _⟩ := future_record_exists rate rewards C_star C_h u t q hfuture x hg.1
      have hs := record_shape rate rewards C_star C_h u t q hfuture x hg r har
      simp only [futureRecordingView, ite_eq_left hg, har, Option.bind_some]
      cases hd : r.output.preparation.coordinator <;> simp only [hd] at hs
      rename_i out
      cases out <;> simp only at hs
      all_goals simp only [ReferenceFirstCollectionCorrectedNextPhysicalReadout.recordRecordingView, hd, DispatchCut.downView,
        DispatchCut.selection, selectionAt, dite_true, Option.map_some, Option.isSome_some, hg]
    · simp [futureRecordingView, hg]
  have hk := corrected_future_physical_kernel rate rewards C_star C_h u t q hfuture x
  refine ⟨hv, ?_⟩
  cases hview : futureRecordingView rate rewards C_star C_h u t q x with
  | none =>
    simp only [hview] at hk hv
    simp only [hk.1, futureParameters, Option.isSome_none, Option.map_none, Option.bind_none, hv.symm, and_self]
  | some v =>
    rcases v with ⟨parameters, view, code⟩
    simp only [hview] at hk hv
    obtain ⟨r, c, selected, states, memories, snapshot, valid, h⟩ := hk
    rcases h with ⟨_har, _ht, _hr, _hj, _hw, _hc, _hsel, _hv, _ho, _hfalse, _htrue,
      hcell, hparameters, _hrest⟩
    simp only [hcell, futureParameters, Option.isSome_some, Option.map_some, Option.bind_some, hv.symm,
      hparameters, and_self]

/-- The actual optional parameter pair factors together with the complete recording view. -/
theorem corrected_future_parameters_factor (control0 : ContinuousLearningRows.TimeControl p)
    (u t q : Fin p.T) (hfuture : t.val + 1 < q.val) (x : X) :
    futureParameters rate rewards C_star C_h u t q x =
      futureParameters rate rewards C_star C_h u t q (sourcePrefix control0 q.val x) := by
  rw [(corrected_future_recordingView_presence rate rewards C_star C_h u t q hfuture x).2.2,
    (corrected_future_recordingView_presence rate rewards C_star C_h u t q hfuture
      (sourcePrefix control0 q.val x)).2.2,
    corrected_future_recordingView_factor rate rewards C_star C_h control0 u t q hfuture x]

private theorem prefix_replaceControl (control0 : ContinuousLearningRows.TimeControl p)
    (q : Fin p.T) (hpos : 0 < q.val) (x : X) (control : ContinuousLearningRows.TimeControl p) :
    sourcePrefix control0 q.val (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p q x control) =
      sourcePrefix control0 q.val x := by
  let b : Fin p.T := ⟨q.val - 1, by have hq := q.isLt; omega⟩
  have hb : b.val + 1 = q.val := by dsimp only [b]; omega
  have hlt : b.val + 1 < p.T := by rw [hb]; exact q.isLt
  have he : (⟨b.val + 1, hlt⟩ : Fin p.T) = q := Fin.ext hb
  simpa only [hb, he] using ReferenceFirstCollectionCorrectedNextPhysicalReadout.sourcePrefix_replaceControl control0 b hlt x control

/-- Replacing the WHOLE current control preserves the gate and every prior view coordinate. -/
theorem corrected_future_recordingView_replaceControl (control0 : ContinuousLearningRows.TimeControl p)
    (u t q : Fin p.T) (hfuture : t.val + 1 < q.val) (x : X)
    (control : ContinuousLearningRows.TimeControl p) :
    let y := ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p q x control
    futureRecordingView rate rewards C_star C_h u t q y = futureRecordingView rate rewards C_star C_h u t q x ∧
    rawTag rate rewards C_star C_h q y = rawTag rate rewards C_star C_h q x ∧
    sliceBranch rate rewards C_star C_h u t q y = sliceBranch rate rewards C_star C_h u t q x ∧
    futureParameters rate rewards C_star C_h u t q y = futureParameters rate rewards C_star C_h u t q x ∧
    futureRecordingCode rate rewards C_star C_h u t q y = futureRecordingCode rate rewards C_star C_h u t q x ∧
    (y ∈ futureGate rate rewards C_star C_h u t q ↔ x ∈ futureGate rate rewards C_star C_h u t q) := by
  dsimp only
  have hp := prefix_replaceControl control0 q (by omega) x control
  have hv := corrected_future_recordingView_congr rate rewards C_star C_h control0 u t q hfuture _ x hp
  refine ⟨hv, rawTag_congr rate rewards C_star C_h control0 q _ x hp,
    sliceBranch_congr rate rewards C_star C_h control0 u t q hfuture _ x hp, ?_, ?_,
    futureGate_congr rate rewards C_star C_h control0 u t q hfuture _ x hp⟩
  · rw [(corrected_future_recordingView_presence rate rewards C_star C_h u t q hfuture _).2.2,
      (corrected_future_recordingView_presence rate rewards C_star C_h u t q hfuture x).2.2, hv]
  · simp only [futureRecordingCode, hv]


private theorem snapshot_code_injective (assignment : ActiveRoundActions.Assignment p.m p.K) :
    Function.Injective (fun snapshot : Option (ActiveRoundActions.Snapshot assignment) =>
      snapshot.map (fun s => (s.missing, fun i => some
        (FollowerDownMeasurability.followerStatusCode (s.status i))))) := by
  intro a b h
  cases a with
  | none => cases b with
    | none => rfl
    | some b => cases h
  | some a => cases b with
    | none => cases h
    | some b =>
      have he := Option.some.inj h
      have hm := congrArg Prod.fst he
      have hs : a.status = b.status := by
        funext i
        have hi := Option.some.inj (congrFun (congrArg Prod.snd he) i)
        have hd := congrArg FollowerDownMeasurability.followerStatusOfCode hi
        simpa only [FollowerDownMeasurability.followerStatusOfCode_code] using hd
      cases a
      cases b
      cases hm
      cases hs
      rfl

private theorem replacement_slice (q : Fin p.T) (x : X) (control : ContinuousLearningRows.TimeControl p) :
    let y := ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p q x control
    ContinuousLearningRows.sliceAt q (y.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p y)).2 = control.1 := by
  simp only [ReferenceFixedTimeSourceControlCoupling.replaceSourceControl,
    ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex,
    ActualInitializationPhysicalStep.selectedRowIndex, Function.update_self, ContinuousLearningRows.sliceAt]

/-- Fixed-argument recording section under WHOLE current-control replacement. -/
theorem corrected_future_marker_section (control0 : ContinuousLearningRows.TimeControl p)
    (u t q : Fin p.T) (hfuture : t.val + 1 < q.val) (x : X) :
    match futureRecordingView rate rewards C_star C_h u t q x with
    | none => ∀ control : ContinuousLearningRows.TimeControl p,
      futureMarker rate rewards C_star C_h u t q
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p q x control) = none
    | some (parameters, view, code) =>
      ∃ (enabled : Bool) (snapshot : Option (ActiveRoundActions.Snapshot view.payload.assignment))
        (valid : CoordinatorLocalArmChoice.ChoiceInputsValid view.payload view.cutoff q view.complementWeights),
        parameters = some (enabled, view.payload.rate) ∧
        code = snapshot.map (fun z => (z.missing, fun i => some
          (FollowerDownMeasurability.followerStatusCode (z.status i)))) ∧
        ∀ control : ContinuousLearningRows.TimeControl p,
          futureMarker rate rewards C_star C_h u t q
            (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p q x control) =
          some (SnapshotRecordingKernel.recordingMap p
            (snapshot.elim .collection (fun z => .live view.payload.assignment z)) enabled
            rate.eta.val rate.eta.property rate.sourceCap view.payload.anchor
            (ReferenceFirstWindowNumericalStream.sourceWeights view.payload view.complementWeights)
            view.payload.anchor_pos
            (ReferenceFirstWindowNumericalStream.sourceWeights_pos _ _ _ _ valid)
            (ReferenceFirstWindowNumericalStream.sourceWeights_lower _ _ _ _ valid)
            (ReferenceFirstWindowNumericalStream.sourceWeights_upper _ _ _ _ valid) control.1) := by
  have hactual := corrected_future_physical_kernel rate rewards C_star C_h u t q hfuture x
  cases hv : futureRecordingView rate rewards C_star C_h u t q x with
  | none =>
    intro control
    have h := corrected_future_physical_kernel rate rewards C_star C_h u t q hfuture
      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p q x control)
    rw [(corrected_future_recordingView_replaceControl rate rewards C_star C_h control0 u t q hfuture x control).1, hv] at h
    exact h.2
  | some v =>
    rcases v with ⟨parameters, view, code⟩
    rw [hv] at hactual
    obtain ⟨r, c, selected, states, memories, snapshot, valid, h⟩ := hactual
    rcases h with ⟨_har, _ht, _hr, _hj, _hw, _hc, _hsel, _hv, _ho, _hfalse, _htrue,
      _hcell, hp, hr, _hrew, hs, _hmarker⟩
    refine ⟨c.enabled, snapshot, valid, by rw [← hr]; exact hp, hs, ?_⟩
    intro control
    have h := corrected_future_physical_kernel rate rewards C_star C_h u t q hfuture
      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p q x control)
    rw [(corrected_future_recordingView_replaceControl rate rewards C_star C_h control0 u t q hfuture x control).1, hv] at h
    obtain ⟨r', c', selected', states', memories', snapshot', valid', h⟩ := h
    rcases h with ⟨_har', _ht', _hr', _hj', _hw', _hc', _hsel', _hv', _ho', _hf', _htrue',
      hc', hp', _hrate', _hreward', hs', hy⟩
    have he : c'.enabled = c.enabled := congrArg Prod.fst (Option.some.inj (hp'.symm.trans hp))
    have hsn : snapshot' = snapshot := snapshot_code_injective _ (hs'.symm.trans hs)
    subst snapshot'
    rw [replacement_slice, he] at hy
    simp only [futureMarker, hc', Option.map_some, hy]

private theorem measurable_inputRecordingView (q : Fin p.T) :
    Measurable (ReferenceFirstCollectionCorrectedNextPhysicalReadout.inputRecordingView rate q) := by
  have ht : Measurable (ReferenceFirstCollectionRenewalNextRecordingPriorView.dispatchTag (p := p) (rate := rate)) := ReferenceFirstCollectionRenewalNextRecordingPriorView.measurable_dispatchTag
  have hv := ReferenceActiveStepCompositionMeasurability.measurable_downView (p := p) (rate := rate)
  have hp := (ReferenceFirstCollectionRenewalNextRecordingPriorView.measurable_parametersOfTag rate q).comp (ht.prodMk hv)
  have hs : Measurable (fun input : RoundInput p rate => fun i : Fin (p.m - 1) =>
      ReferenceFirstCollectionRenewalNextRecordingPriorView.configurationStatus rate ((prepare input).followers.followers i).configuration) := by
    apply measurable_pi_iff.mpr
    intro i
    have h := (ReferenceFirstCollectionRenewalNextRecordingPriorView.measurable_preparedStatusCode rate).comp
      (ReferenceActivePhysicalStepMeasurability.measurable_preparedFollowerCode i)
    convert h using 1
    funext input
    exact (ReferenceFirstCollectionRenewalNextRecordingPriorView.preparedStatusCode_eq rate input i).symm
  have hm : Measurable (fun view : ReferenceDownReception.ChoiceTimeView p rate.eta => view.pendingAtChoice) :=
    measurable_fst.comp (measurable_snd.comp (comap_measurable
      (ReferenceDownReceptionMeasurability.choiceTimeViewObservation (p := p) (rate := rate))))
  have hc : Measurable (fun v : ReferenceDownReception.ChoiceTimeView p rate.eta × RoundInput p rate =>
      if ReferenceFirstCollectionRenewalNextRecordingPriorView.isCutoffTag (ReferenceFirstCollectionRenewalNextRecordingPriorView.dispatchTag v.2) then
        (none : Option (Finset (Fin (p.m - 1)) × (Fin (p.m - 1) → Option (Fin 3))))
      else some (v.1.pendingAtChoice, fun i =>
        ReferenceFirstCollectionRenewalNextRecordingPriorView.configurationStatus rate ((prepare v.2).followers.followers i).configuration)) :=
    (measurable_of_countable (fun key : Bool ×
      (Finset (Fin (p.m - 1)) × (Fin (p.m - 1) → Option (Fin 3))) =>
        if key.1 then none else some key.2)).comp
      ((((measurable_of_countable ReferenceFirstCollectionRenewalNextRecordingPriorView.isCutoffTag).comp ht).comp measurable_snd).prodMk
        ((hm.comp measurable_fst).prodMk (hs.comp measurable_snd)))
  exact ReferenceCollectionInstallOutputMeasurability.measurable_optionMapDependent _
    ((hp.comp measurable_snd).prodMk (measurable_fst.prodMk hc)) _ hv

/-- Literal Borel input formula on all X; the off-slice observation is absent. -/
theorem futureRecordingView_input_formula (u t q : Fin p.T) (hfuture : t.val + 1 < q.val) (x : X) :
    futureRecordingView rate rewards C_star C_h u t q x =
      if x ∈ futureGate rate rewards C_star C_h u t q then
        (ReferenceFirstCollectionCorrectedNextPhysicalReadout.actualInput? rate rewards C_star C_h q x).bind (ReferenceFirstCollectionCorrectedNextPhysicalReadout.inputRecordingView rate q)
      else none := by
  by_cases hg : x ∈ futureGate rate rewards C_star C_h u t q
  · obtain ⟨r, har, _⟩ := future_record_exists rate rewards C_star C_h u t q hfuture x hg.1
    simp only [futureRecordingView, ite_eq_left hg, ReferenceFirstCollectionCorrectedNextPhysicalReadout.actualInput?, har, Option.map_some, Option.bind_some]
    have hp := record_parameters rate rewards C_star C_h u t q hfuture x hg r har
    have ht := (ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields rate rewards C_star C_h q x r har).2.2.1
    have hprep : r.output.preparation = prepare r.input := by rw [r.output_eq]; rfl
    unfold ReferenceFirstCollectionCorrectedNextPhysicalReadout.recordRecordingView ReferenceFirstCollectionCorrectedNextPhysicalReadout.inputRecordingView ReferenceFirstCollectionCorrectedNextPhysicalReadout.recordStatuses
    rw [hp, ht, hprep]
    rfl
  · simp only [futureRecordingView, ite_eq_right hg]

/-- Ambient Borelness on the whole original continuous source carrier. -/
theorem futureRecordingView_measurable (control0 : ContinuousLearningRows.TimeControl p)
    (u t q : Fin p.T) (hfuture : t.val + 1 < q.val) :
    Measurable (futureRecordingView rate rewards C_star C_h u t q) := by
  have hG : MeasurableSet (futureGate rate rewards C_star C_h u t q) :=
    (sourcePrefixFiltration control0).le' (q.val + 1) _
      (futureGate_measurable rate rewards C_star C_h control0 u t q hfuture)
  have hm := measurable_optionBind (ReferenceFirstCollectionCorrectedNextPhysicalReadout.actualInput? rate rewards C_star C_h q)
    (ReferenceFirstCollectionCorrectedNextPhysicalReadout.measurable_actualInput? rate rewards C_star C_h q)
    (ReferenceFirstCollectionCorrectedNextPhysicalReadout.inputRecordingView rate q) (measurable_inputRecordingView rate q)
  convert hm.ite hG measurable_const using 1
  funext x
  exact futureRecordingView_input_formula rate rewards C_star C_h u t q hfuture x

/-- Borelness in the exact existing strict-prior field. -/
theorem futureRecordingView_prior_measurable (control0 : ContinuousLearningRows.TimeControl p)
    (u t q : Fin p.T) (hfuture : t.val + 1 < q.val) :
    Measurable[sourcePrefixFiltration control0 (q.val + 1)]
      (futureRecordingView rate rewards C_star C_h u t q) := by
  rw [sourcePrefixFiltration_succ]
  have hm := (futureRecordingView_measurable rate rewards C_star C_h control0 u t q hfuture).comp
    (comap_measurable (sourcePrefix control0 q.val))
  convert hm using 1
  funext x
  exact corrected_future_recordingView_factor rate rewards C_star C_h control0 u t q hfuture x

/-- Actual optional parameters are measurable in the same strict-prior field. -/
theorem futureParameters_prior_measurable (control0 : ContinuousLearningRows.TimeControl p)
    (u t q : Fin p.T) (hfuture : t.val + 1 < q.val) :
    Measurable[sourcePrefixFiltration control0 (q.val + 1)]
      (futureParameters rate rewards C_star C_h u t q) := by
  let : MeasurableSpace X := sourcePrefixFiltration control0 (q.val + 1)
  have hm := measurable_optionBind _
    (futureRecordingView_prior_measurable rate rewards C_star C_h control0 u t q hfuture)
    Prod.fst measurable_fst
  convert hm using 1
  funext x
  exact (corrected_future_recordingView_presence rate rewards C_star C_h u t q hfuture x).2.2

/-- The complete code is measurable before the entire current control. -/
theorem futureRecordingCode_prior_measurable (control0 : ContinuousLearningRows.TimeControl p)
    (u t q : Fin p.T) (hfuture : t.val + 1 < q.val) :
    Measurable[sourcePrefixFiltration control0 (q.val + 1)]
      (futureRecordingCode rate rewards C_star C_h u t q) := by
  exact @LaterAssignmentFullOutputMeasurability.measurable_optionMap
    X (sourcePrefixFiltration control0 (q.val + 1)) _ _ _ _ _
    (measurable_fst.prodMk (((ReferenceFirstCollectionRenewalNextRecordingPriorView.measurable_recordingViewCode rate).comp
      (measurable_fst.comp measurable_snd)).prodMk (measurable_snd.comp measurable_snd))) _
    (futureRecordingView_prior_measurable rate rewards C_star C_h control0 u t q hfuture)

/-- Ambient Borelness of the actual marker, using only the generic adjacent-index Borel API. -/
theorem futureMarker_measurable (control0 : ContinuousLearningRows.TimeControl p)
    (u t q : Fin p.T) (hfuture : t.val + 1 < q.val) :
    Measurable (futureMarker rate rewards C_star C_h u t q) := by
  classical
  let b : Fin p.T := ⟨q.val - 1, by have hq := q.isLt; omega⟩
  have hb : b.val + 1 = q.val := by dsimp only [b]; omega
  have hlt : b.val + 1 < p.T := by rw [hb]; exact q.isLt
  have he : (⟨b.val + 1, hlt⟩ : Fin p.T) = q := Fin.ext hb
  have hm := ReferenceFirstCollectionCorrectedNextRecordingLaw.corrected_nextMarker_measurable
    rate rewards C_star C_h b hlt
  have hG : MeasurableSet (futureGate rate rewards C_star C_h u t q) :=
    (sourcePrefixFiltration control0).le' (q.val + 1) _
      (futureGate_measurable rate rewards C_star C_h control0 u t q hfuture)
  have hmask : Measurable (fun x : X =>
      if x ∈ futureGate rate rewards C_star C_h u t q then
        ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextMarker rate rewards C_star C_h b hlt x
      else (none : Option (Option (Fin p.K)))) := hm.ite hG measurable_const
  convert hmask using 1
  funext x
  by_cases hg : x ∈ futureGate rate rewards C_star C_h u t q <;>
    simp [futureMarker, futureCell, hg, ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextMarker,
      ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextCell, he]

/-- Joint Borelness under replacement of the complete continuous current control. -/
theorem futureMarker_replaceControl_measurable (control0 : ContinuousLearningRows.TimeControl p)
    (u t q : Fin p.T) (hfuture : t.val + 1 < q.val) :
    Measurable (fun v : X × ContinuousLearningRows.TimeControl p =>
      futureMarker rate rewards C_star C_h u t q
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p q v.1 v.2)) :=
  (futureMarker_measurable rate rewards C_star C_h control0 u t q hfuture).comp
    (ReferenceSourcePhysicalFlagConditionalLaw.measurable_replaceSourceControl p q)


/-- The selected sender carries the SAME payload installed at the original birth. -/
theorem corrected_future_installed_payload (u t q : Fin p.T) (hfuture : t.val + 1 < q.val) (x : X) :
    match (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords rate rewards C_star C_h x)[ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex rate rewards C_star C_h x]? with
    | none => futureRecordingView rate rewards C_star C_h u t q x = none
    | some birth => match birth.output.preparation.coordinator with
      | .collection _ _ _ _ (.laterChosen _ _ _ _ _ _ _ _ _ installed _) =>
        match futureRecordingView rate rewards C_star C_h u t q x with
        | none => True
        | some (_, view, _) => view.payload = installed.registers.payload
      | _ => futureRecordingView rate rewards C_star C_h u t q x = none := by
  simp only [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords,
    ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex]
  by_cases hg : x ∈ futureGate rate rewards C_star C_h u t q
  · obtain ⟨birth, hb, _har, ht, hchosen⟩ := ReferenceFirstCollectionCorrectedNextPhysicalReadout.firstCell_firstReplacement_record
      rate rewards C_star C_h u t x hg.1.1
    have hread := ReferenceFirstReplacementFollowerBoundary.complete_first_replacement_continuing_live_readout
      rate x rewards C_star C_h
    have hcut := ReferenceFirstReplacementCutoffPreparedBoundary.complete_first_replacement_cutoff_follower_boundary
      rate x rewards C_star C_h
    dsimp only at hread hcut
    simp only [hb] at hread hcut ⊢
    have hprep : birth.output.preparation = prepare birth.input := by rw [birth.output_eq]; rfl
    unfold ReferenceCollectionPhaseHistory.laterChosen at hchosen
    rw [← hprep] at hchosen
    cases hc : birth.output.preparation.coordinator <;> simp only [hc, Bool.false_eq_true] at hchosen
    rename_i out
    cases out <;> simp only at hchosen <;> try contradiction
    rw [hc] at hread hcut
    dsimp only at hread hcut ⊢
    obtain ⟨r, har, hlookup⟩ := future_record_exists rate rewards C_star C_h u t q hfuture x hg.1
    have hshape := record_shape rate rewards C_star C_h u t q hfuture x hg r har
    have hbranch := gate_branch rate rewards C_star C_h u t q hfuture x hg r har
    simp only [futureRecordingView, ite_eq_left hg, har, Option.bind_some]
    cases hd : r.output.preparation.coordinator <;> simp only [hd] at hshape
    rename_i registers owned base out
    cases out <;> simp only at hshape
    case cutoffChosen dispatched hs ledger hi hledger hdomain hclock hpending hstart selected =>
      rw [hd] at hbranch
      have hend := ((sliceBranch_true_iff rate rewards C_star C_h u t q hfuture x).mp hbranch).2.1
      rw [hend] at hlookup
      change (match (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords rate rewards C_star C_h x)[ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex rate rewards C_star C_h x +
        1 + (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail rate rewards C_star C_h x).length]? with
        | none => True | some r => _) at hcut
      rw [hlookup] at hcut
      dsimp only at hcut
      rw [hd] at hcut
      have hpay := hcut.2.1
      simpa only [ReferenceFirstCollectionCorrectedNextPhysicalReadout.recordRecordingView, hd, DispatchCut.downView, DispatchCut.selection,
        selectionAt, dite_true, Option.map_some] using hpay
    case continuingChosen dispatched hs continuation selected =>
      rw [hd] at hbranch
      have hk := ((sliceBranch_false_iff rate rewards C_star C_h u t q hfuture x).mp hbranch).2
      have h := hread ⟨q.val - (t.val + 1), hk⟩
      dsimp only at h
      have heq : (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail rate rewards C_star C_h x).get ⟨q.val - (t.val + 1), hk⟩ = r :=
        Option.some.inj (h.1.symm.trans hlookup)
      obtain ⟨cell, hpay, _⟩ := h.2
      have hsel : ((ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail rate rewards C_star C_h x).get
          ⟨q.val - (t.val + 1), hk⟩).output.preparation.coordinator.selection = some cell.selected := cell.selection_actual
      have hv : ((ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail rate rewards C_star C_h x).get
          ⟨q.val - (t.val + 1), hk⟩).output.preparation.coordinator.downView = some cell.selected.view := by
        rw [DispatchCut.downView, hsel]
        rfl
      have hresult : (ReferenceFirstCollectionCorrectedNextPhysicalReadout.recordRecordingView rate
          ((ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail rate rewards C_star C_h x).get
            ⟨q.val - (t.val + 1), hk⟩)).map (fun v => v.2.1.payload) = some cell.selected.view.payload := by
        simp only [ReferenceFirstCollectionCorrectedNextPhysicalReadout.recordRecordingView, hv, Option.map_some]
      have hout := hresult.trans (congrArg some hpay)
      rw [heq] at hout
      cases hview : ReferenceFirstCollectionCorrectedNextPhysicalReadout.recordRecordingView rate r with
      | none => trivial
      | some v =>
        rcases v with ⟨parameters, view, code⟩
        simp only [hview, Option.map_some] at hout
        exact Option.some.inj hout
  · have hv : futureRecordingView rate rewards C_star C_h u t q x = none := by
      simp only [futureRecordingView, ite_eq_right hg]
    rw [hv]
    split
    · rfl
    · rename_i birth _
      cases birth.output.preparation.coordinator <;> try trivial
      rename_i out
      cases out <;> trivial

/-- Restoring the current control reconstructs this marker observation, not the whole source. -/
theorem corrected_future_marker_reconstruct (control0 : ContinuousLearningRows.TimeControl p)
    (u t q : Fin p.T) (hfuture : t.val + 1 < q.val) (x : X) :
    futureMarker rate rewards C_star C_h u t q x =
      futureMarker rate rewards C_star C_h u t q
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p q
          (sourcePrefix control0 q.val x)
          ((x.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p x)).2 q)) := by
  let y := ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p q
    (sourcePrefix control0 q.val x) ((x.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p x)).2 q)
  change futureMarker rate rewards C_star C_h u t q x = futureMarker rate rewards C_star C_h u t q y
  have hprefix : sourcePrefix control0 q.val y = sourcePrefix control0 q.val x := by
    rw [prefix_replaceControl control0 q (by omega), sourcePrefix_sourcePrefix control0 _ _ le_rfl]
  have hv := corrected_future_recordingView_congr rate rewards C_star C_h control0 u t q hfuture y x hprefix
  have h := corrected_future_physical_kernel rate rewards C_star C_h u t q hfuture x
  have h' := corrected_future_physical_kernel rate rewards C_star C_h u t q hfuture y
  rw [hv] at h'
  cases hview : futureRecordingView rate rewards C_star C_h u t q x with
  | none =>
    rw [hview] at h h'
    exact h.2.trans h'.2.symm
  | some v =>
    rcases v with ⟨parameters, view, code⟩
    rw [hview] at h h'
    obtain ⟨r, c, selected, states, memories, snapshot, valid, h⟩ := h
    obtain ⟨r', c', selected', states', memories', snapshot', valid', h'⟩ := h'
    rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, hc, hp, _, _, hs, hm⟩
    rcases h' with ⟨_, _, _, _, _, _, _, _, _, _, _, hc', hp', _, _, hs', hm'⟩
    have he : c'.enabled = c.enabled := congrArg Prod.fst (Option.some.inj (hp'.symm.trans hp))
    have hsn : snapshot' = snapshot := snapshot_code_injective _ (hs'.symm.trans hs)
    subst snapshot'
    have hslice : ContinuousLearningRows.sliceAt q (y.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p y)).2 =
        ContinuousLearningRows.sliceAt q (x.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p x)).2 :=
      replacement_slice q _ _
    simp only [futureMarker, hc, hc', Option.map_some, hm, hm', he, hslice]


/-- Literal gate factorization follows from its causal branch characterization. -/
theorem corrected_future_gate_factor (control0 : ContinuousLearningRows.TimeControl p)
    (u t q : Fin p.T) (hfuture : t.val + 1 < q.val) (x : X) :
    x ∈ futureGate rate rewards C_star C_h u t q ↔
      sourcePrefix control0 q.val x ∈ futureGate rate rewards C_star C_h u t q :=
  futureGate_congr rate rewards C_star C_h control0 u t q hfuture x _
    (sourcePrefix_sourcePrefix control0 q.val q.val le_rfl x).symm

/-- The branch, actual parameters and complete status/view code factor together. -/
theorem corrected_future_observations_factor (control0 : ContinuousLearningRows.TimeControl p)
    (u t q : Fin p.T) (hfuture : t.val + 1 < q.val) (x : X) :
    (sliceBranch rate rewards C_star C_h u t q x, futureParameters rate rewards C_star C_h u t q x,
      futureRecordingCode rate rewards C_star C_h u t q x) =
    (sliceBranch rate rewards C_star C_h u t q (sourcePrefix control0 q.val x),
      futureParameters rate rewards C_star C_h u t q (sourcePrefix control0 q.val x),
      futureRecordingCode rate rewards C_star C_h u t q (sourcePrefix control0 q.val x)) := by
  have hb := sliceBranch_congr rate rewards C_star C_h control0 u t q hfuture x _
    (sourcePrefix_sourcePrefix control0 q.val q.val le_rfl x).symm
  rw [hb, corrected_future_parameters_factor rate rewards C_star C_h control0 u t q hfuture x,
    futureRecordingCode, corrected_future_recordingView_factor rate rewards C_star C_h control0 u t q hfuture x]
  rfl

/-- The actual parameter projection is Borel on all original sources. -/
theorem futureParameters_measurable (control0 : ContinuousLearningRows.TimeControl p)
    (u t q : Fin p.T) (hfuture : t.val + 1 < q.val) :
    Measurable (futureParameters rate rewards C_star C_h u t q) :=
  (futureParameters_prior_measurable rate rewards C_star C_h control0 u t q hfuture).mono
    ((sourcePrefixFiltration control0).le' (q.val + 1)) le_rfl

/-- The complete actual recording code is Borel on all original sources. -/
theorem futureRecordingCode_measurable (control0 : ContinuousLearningRows.TimeControl p)
    (u t q : Fin p.T) (hfuture : t.val + 1 < q.val) :
    Measurable (futureRecordingCode rate rewards C_star C_h u t q) :=
  (futureRecordingCode_prior_measurable rate rewards C_star C_h control0 u t q hfuture).mono
    ((sourcePrefixFiltration control0).le' (q.val + 1)) le_rfl

/-- The literal gate is Borel on the whole original source carrier. -/
theorem futureGate_ambient_measurable (control0 : ContinuousLearningRows.TimeControl p)
    (u t q : Fin p.T) (hfuture : t.val + 1 < q.val) :
    MeasurableSet (futureGate rate rewards C_star C_h u t q) :=
  (sourcePrefixFiltration control0).le' (q.val + 1) _
    (futureGate_measurable rate rewards C_star C_h control0 u t q hfuture)

/-- A present observation joins C's SAME incoming run to its actual next update. -/
theorem corrected_future_step_inputs (u t q : Fin p.T) (hfuture : t.val + 1 < q.val) (x : X) :
    match futureCell rate rewards C_star C_h u t q x with
    | none => True
    | some c => ∃ L,
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs rate rewards C_star C_h q.val x = some L ∧
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs rate rewards C_star C_h (q.val + 1) x = some (L ++ [c]) ∧
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout rate rewards C_star C_h (q.val + 1) x = some
        (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
          (RecordedQueueRun.step (ReferenceFirstLaunchNumericalCell.queueParameters rate)
            (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate) L) c)) := by
  by_cases hg : x ∈ futureGate rate rewards C_star C_h u t q
  · obtain ⟨L, r, c, hL, hr, hc, hnext, hread⟩ := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.firstCell_step_inputs
      rate rewards C_star C_h u t x hg.1 q.val (by omega) hg.2
    have hbirth := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.firstCell_birth_time rate rewards C_star C_h u t x hg.1
    have hstart : ReferenceCompletePhysicalHistory.physicalStart rate x rewards C_star C_h ≤ q.val := by
      change ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart rate rewards C_star C_h x ≤ q.val
      omega
    have har : actualRecord rate rewards C_star C_h q x = some r := by
      simpa only [actualRecord, ite_eq_left hstart,
        ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords,
        ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart] using hr
    simp only [futureCell, ite_eq_left hg, har, Option.bind_some, hc]
    exact ⟨L, hL, hnext, hread⟩
  · simp only [futureCell, ite_eq_right hg]

end Bandits.Support.ReferenceFirstCollectionCorrectedFutureRecordingView
