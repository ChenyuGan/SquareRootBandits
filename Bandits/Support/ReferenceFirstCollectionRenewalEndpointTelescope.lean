/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionRenewalFutureSliceEndpoint
public import Bandits.Support.ReferenceFirstCollectionRenewalCalendarOverflowRetention

import Mathlib.Tactic

/-!
# Inclusive actual-source endpoint telescope

The queue readouts below are the original, whole-prefix optional run.  Every
date accessor requires endpoint bounds and uses the proved presence of that
readout.  The inclusive endpoint retains a selected detecting cutoff update.
-/

@[expose] public section
noncomputable section

open Bandits.Support ConstructorDimensions
open scoped Classical

namespace Bandits.Support.ReferenceFirstCollectionRenewalEndpointTelescope

open ReferenceFirstCollectionRenewalFutureSliceEndpoint
open ReferenceFirstCollectionRenewalCalendarOverflowRetention
open ReferenceFirstCollectionRenewalFutureNumericalPrefix
open ReferenceFirstCollectionRenewalFutureRetainedMoments
open ReferenceFirstCollectionRenewalFutureFirstReplacementView

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ) (u t : Fin p.T)

local notation "Z" => _root_.Bandits.Support.ReferenceFirstCollectionRenewalFutureControlLaw.Source
  rate rewards C_star C_h u t
abbrev actualPrefixReadout (n : ℕ) (z : Z) :=
  ReferenceFirstCollectionRenewalFutureNumericalPrefix.futurePrefixReadout
    rate rewards C_star C_h u t n z

abbrev endpointBegin : ℕ :=
  ReferenceFirstCollectionRenewalFutureSliceEndpoint.beginning t

abbrev endpointEnd (z : Z) : ℕ :=
  ReferenceFirstCollectionRenewalFutureSliceEndpoint.endpointIndex
    rate rewards C_star C_h u t z

/-- The inclusive actual calendar dates on which the original whole-prefix
readout is present. -/
def EndpointDate (z : Z) := {n : ℕ // endpointBegin t ≤ n ∧
  n ≤ endpointEnd rate rewards C_star C_h u t z}

/-- The unique actual full-prefix readout at an endpoint date. -/
def actualReadoutAt (z : Z) (n : EndpointDate rate rewards C_star C_h u t z) :=
  (actualPrefixReadout rate rewards C_star C_h u t n.val z).get (by
    exact ReferenceFirstCollectionRenewalFutureSliceEndpoint.futurePrefixReadout_present_through_endpoint
      rate rewards C_star C_h u t z n.val n.property.1 n.property.2)

/-- The endpoint exponential uses the actual integer backlog register in the
whole readout, divided by the existing queue scale. -/
def actualBacklogExpAt (z : Z) (a : Fin p.K)
    (n : EndpointDate rate rewards C_star C_h u t z) : ℝ :=
  Real.exp (CanonicalRecordingRates.beta p rate.eta.val *
    (((actualReadoutAt rate rewards C_star C_h u t z n).1 a).2 : ℝ) /
      ((_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ))

/-- The first summation date absorbs the immediate future date, as supplied by
the endpoint support theorem. -/
def endpointTelescopeStart (z : Z) : ℕ := min
  (ReferenceFirstCollectionRenewalFutureSliceEndpoint.beginning t + 1)
  (ReferenceFirstCollectionRenewalFutureSliceEndpoint.endpointIndex
    rate rewards C_star C_h u t z)

/-- Read the endpoint exponential at an offset from `j`, with the offset
bounded by the actual half-open interval length. -/
def endpointOffsetExp (z : Z) (a : Fin p.K)
    (i : Fin (endpointEnd rate rewards C_star C_h u t z -
      endpointTelescopeStart rate rewards C_star C_h u t z + 1)) : ℝ :=
  actualBacklogExpAt rate rewards C_star C_h u t z a
    ⟨endpointTelescopeStart rate rewards C_star C_h u t z + i.val,
      (by
        have h := ReferenceFirstCollectionRenewalFutureSliceEndpoint.endpoint_bounds
          rate rewards C_star C_h u t z
        exact (Nat.le_min.mpr ⟨Nat.le_add_right _ _, h.1.trans h.2.1⟩).trans
          (Nat.le_add_right _ _)),
      (by
        have h := ReferenceFirstCollectionRenewalFutureSliceEndpoint.endpoint_bounds
          rate rewards C_star C_h u t z
        have hj : endpointTelescopeStart rate rewards C_star C_h u t z ≤
            endpointEnd rate rewards C_star C_h u t z := min_le_right _ _
        have hi : i.val ≤ endpointEnd rate rewards C_star C_h u t z -
            endpointTelescopeStart rate rewards C_star C_h u t z := by omega
        omega)⟩

/-- A genuine future support date in the first-replacement slice, retaining
its actual `Fin T` date and the exact support-test witness. -/
def EndpointSupportDate (z : Z) :=
  {q : Fin p.T // ∃ hfuture : t.val + 1 < q.val,
    ReferenceFirstCollectionRenewalFutureSliceEndpoint.supportTest
      rate rewards C_star C_h u t q hfuture z}

noncomputable local instance endpointSupportDateFintype (z : Z) :
    Fintype (EndpointSupportDate rate rewards C_star C_h u t z) := by
  letI : Finite (EndpointSupportDate rate rewards C_star C_h u t z) := by
    classical
    exact Finite.of_injective
      (fun d : EndpointSupportDate rate rewards C_star C_h u t z => d.1)
      (by intro x y h; exact Subtype.ext h)
  exact Fintype.ofFinite _

/-- The increment at a supported date is formed from its two actual present
whole-prefix readouts. -/
def endpointSupportIncrement (z : Z) (a : Fin p.K)
    (d : EndpointSupportDate rate rewards C_star C_h u t z) : ℝ :=
  let q := d.1
  let hfuture := Classical.choose d.2
  let hsupport := Classical.choose_spec d.2
  let hqk := (ReferenceFirstCollectionRenewalFutureSliceEndpoint.supportTest_iff_before_endpoint
    rate rewards C_star C_h u t z q hfuture).mp hsupport
  have hbegin : endpointBegin t ≤ q.val := by
    change t.val + 1 ≤ q.val
    exact Nat.le_of_lt hfuture
  have hqend : q.val < endpointEnd rate rewards C_star C_h u t z := by
    change q.val < ReferenceFirstCollectionRenewalFutureSliceEndpoint.endpointIndex
      rate rewards C_star C_h u t z
    exact hqk
  have hbeginAfter : endpointBegin t ≤ q.val + 1 := by omega
  have hqendAfter : q.val + 1 ≤ endpointEnd rate rewards C_star C_h u t z := by omega
  have hqendBefore : q.val ≤ endpointEnd rate rewards C_star C_h u t z := Nat.le_of_lt hqend
  actualBacklogExpAt rate rewards C_star C_h u t z a
      ⟨q.val + 1, ⟨hbeginAfter, hqendAfter⟩⟩ -
    actualBacklogExpAt rate rewards C_star C_h u t z a
      ⟨q.val, ⟨hbegin, hqendBefore⟩⟩

/-- A supported first-slice date has a present actual slice cell.  Below the
continuing boundary this is the continuing readout; at the boundary it is
the selected cutoff cell after its detecting update. All other first
noncontinuing constructors are excluded by the inclusive endpoint. -/
theorem endpointSliceCell_present (z : Z) (q : Fin p.T)
    (hfuture : t.val + 1 < q.val)
    (hqk : q.val < ReferenceFirstCollectionRenewalFutureSliceEndpoint.endpointIndex
      rate rewards C_star C_h u t z) :
    (ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureCell
      rate rewards C_star C_h u t z q hfuture).isSome = true := by
  by_cases hcontinuing : q.val <
      ReferenceFirstCollectionRenewalFutureSliceEndpoint.continuingEnd
        rate rewards C_star C_h u t z
  · have hpos : q.val - (t.val + 1) <
        ReferenceFirstCollectionRenewalFutureSliceEndpoint.continuingLength
          rate rewards C_star C_h u t z := by
      dsimp [ReferenceFirstCollectionRenewalFutureSliceEndpoint.continuingEnd,
        ReferenceFirstCollectionRenewalFutureSliceEndpoint.beginning] at hcontinuing ⊢
      omega
    exact ReferenceFirstCollectionRenewalFutureSliceEndpoint.continuing_futureCell_present
      rate rewards C_star C_h u t z q hfuture hpos
  · have hdelta_le :
        ReferenceFirstCollectionRenewalFutureSliceEndpoint.cutoffEndpointDelta
          rate rewards C_star C_h u t z ≤ 1 := by
      unfold ReferenceFirstCollectionRenewalFutureSliceEndpoint.cutoffEndpointDelta
      cases hr : ReferenceFirstCollectionRenewalFutureSliceEndpoint.firstNoncontinuingRecord
          rate rewards C_star C_h u t z with
      | none => simp
      | some r =>
          cases hc : r.output.preparation.coordinator with
          | live registers owned base outcome => cases outcome <;> simp [hc]
          | first outcome => simp [hc]
          | collection payload ledger clock cutoff outcome => simp [hc]
          | invalidCollectionCutoff => simp [hc]
          | dagger => simp [hc]
    have hboundary :
        q.val = ReferenceFirstCollectionRenewalFutureSliceEndpoint.continuingEnd
          rate rewards C_star C_h u t z ∧
        ReferenceFirstCollectionRenewalFutureSliceEndpoint.cutoffEndpointDelta
          rate rewards C_star C_h u t z = 1 := by
      have hqk' := hqk
      change q.val <
        ReferenceFirstCollectionRenewalFutureSliceEndpoint.continuingEnd
          rate rewards C_star C_h u t z +
        ReferenceFirstCollectionRenewalFutureSliceEndpoint.cutoffEndpointDelta
          rate rewards C_star C_h u t z at hqk'
      have hnot := Nat.le_of_not_gt hcontinuing
      omega
    rcases hboundary with ⟨hcalendar, hdelta⟩
    have hpos : q.val - (t.val + 1) =
        ReferenceFirstCollectionRenewalFutureSliceEndpoint.continuingLength
          rate rewards C_star C_h u t z := by
      rw [hcalendar]
      dsimp [ReferenceFirstCollectionRenewalFutureSliceEndpoint.continuingEnd,
        ReferenceFirstCollectionRenewalFutureSliceEndpoint.beginning]
      omega
    exact ReferenceFirstCollectionRenewalFutureSliceEndpoint.cutoff_futureCell_present
      rate rewards C_star C_h u t z q hfuture hpos hdelta

/-- Reindex a half-open telescope offset as its genuine supported `Fin T`
calendar date. -/
def endpointSupportDateAtOffset (z : Z)
    (i : Fin (endpointEnd rate rewards C_star C_h u t z -
      endpointTelescopeStart rate rewards C_star C_h u t z)) :
    EndpointSupportDate rate rewards C_star C_h u t z := by
  let j := endpointTelescopeStart rate rewards C_star C_h u t z
  let e := endpointEnd rate rewards C_star C_h u t z
  have hbounds := ReferenceFirstCollectionRenewalFutureSliceEndpoint.endpoint_bounds
    rate rewards C_star C_h u t z
  have hje : j ≤ e := min_le_right _ _
  have hi := i.isLt
  have hjeStrict : j < e := by omega
  have hj : j = ReferenceFirstCollectionRenewalFutureSliceEndpoint.beginning t + 1 := by
    dsimp [j, endpointTelescopeStart]
    by_cases he : e ≤ ReferenceFirstCollectionRenewalFutureSliceEndpoint.beginning t + 1
    · change min (ReferenceFirstCollectionRenewalFutureSliceEndpoint.beginning t + 1) e = _
      have hstrict : j < e := hjeStrict
      have heq : j = e := by
        dsimp [j, endpointTelescopeStart]
        exact Nat.min_eq_right he
      rw [heq] at hstrict
      exact (Nat.lt_irrefl e hstrict).elim
    · change min (ReferenceFirstCollectionRenewalFutureSliceEndpoint.beginning t + 1) e = _
      exact Nat.min_eq_left (by omega)
  have hj' : j = t.val + 2 := by
    simpa [ReferenceFirstCollectionRenewalFutureSliceEndpoint.beginning] using hj
  change ↑i < e - j at hi
  have hqi : j + ↑i < e := by omega
  let q : Fin p.T := ⟨j + i.val, by
    have heT := hbounds.2.2
    exact Nat.lt_of_lt_of_le hqi heT⟩
  have hfuture : t.val + 1 < q.val := by
    dsimp [q]
    rw [hj']
    omega
  have hqend : q.val < e := by
    dsimp [q]
    exact hqi
  have hsupport := ReferenceFirstCollectionRenewalFutureSliceEndpoint.supportTest_iff_before_endpoint
    rate rewards C_star C_h u t z q hfuture |>.mpr hqend
  exact ⟨q, ⟨hfuture, hsupport⟩⟩

private theorem endpointSupportDateAtOffset_val (z : Z)
    (i : Fin (endpointEnd rate rewards C_star C_h u t z -
      endpointTelescopeStart rate rewards C_star C_h u t z)) :
    (endpointSupportDateAtOffset rate rewards C_star C_h u t z i).1.val =
      endpointTelescopeStart rate rewards C_star C_h u t z + i.val := by
  change endpointTelescopeStart rate rewards C_star C_h u t z + i.val = _
  rfl

private theorem endpointOffset_increment_eq_support (a : Fin p.K) (z : Z)
    (i : Fin (endpointEnd rate rewards C_star C_h u t z -
      endpointTelescopeStart rate rewards C_star C_h u t z)) :
    endpointOffsetExp rate rewards C_star C_h u t z a i.succ -
        endpointOffsetExp rate rewards C_star C_h u t z a i.castSucc =
      endpointSupportIncrement rate rewards C_star C_h u t z a
        (endpointSupportDateAtOffset rate rewards C_star C_h u t z i) := by
  simp only [endpointOffsetExp, endpointSupportIncrement,
    endpointSupportDateAtOffset_val, Fin.val_succ, Fin.val_castSucc,
    Nat.add_assoc]

private theorem endpoint_telescope_sum_reindex (a : Fin p.K) (z : Z) :
    (∑ i : Fin (endpointEnd rate rewards C_star C_h u t z -
      endpointTelescopeStart rate rewards C_star C_h u t z),
        (endpointOffsetExp rate rewards C_star C_h u t z a i.succ -
          endpointOffsetExp rate rewards C_star C_h u t z a i.castSucc)) =
      ∑ d : EndpointSupportDate rate rewards C_star C_h u t z,
        endpointSupportIncrement rate rewards C_star C_h u t z a d := by
  classical
  let j := endpointTelescopeStart rate rewards C_star C_h u t z
  let e := endpointEnd rate rewards C_star C_h u t z
  apply Finset.sum_bij (s := Finset.univ) (t := Finset.univ)
    (fun i _ => endpointSupportDateAtOffset rate rewards C_star C_h u t z i)
  · intro i hi
    exact Finset.mem_univ _
  · intro i hi i' hi' heq
    apply Fin.ext
    have hval := congrArg (fun d : EndpointSupportDate rate rewards C_star C_h u t z => d.1.val) heq
    rw [endpointSupportDateAtOffset_val rate rewards C_star C_h u t z i,
      endpointSupportDateAtOffset_val rate rewards C_star C_h u t z i'] at hval
    exact Nat.add_left_cancel hval
  · intro d hd
    rcases d with ⟨q, hdate⟩
    rcases hdate with ⟨hfuture, hsupport⟩
    have hqk := (ReferenceFirstCollectionRenewalFutureSliceEndpoint.supportTest_iff_before_endpoint
      rate rewards C_star C_h u t z q hfuture).mp hsupport
    change q.val < e at hqk
    have hfuture' : t.val + 1 < q.val := hfuture
    have hj : j = t.val + 2 := by
      change min (t.val + 2) e = t.val + 2
      apply Nat.min_eq_left
      omega
    have hqj : j ≤ q.val := by rw [hj]; omega
    let i : Fin (e - j) := ⟨q.val - j, by omega⟩
    have hmap : endpointSupportDateAtOffset rate rewards C_star C_h u t z i =
        ⟨q, ⟨hfuture, hsupport⟩⟩ := by
      apply Subtype.ext
      apply Fin.ext
      rw [endpointSupportDateAtOffset_val]
      change j + (q.val - j) = q.val
      exact Nat.add_sub_of_le hqj
    exact ⟨i, Finset.mem_univ _, hmap⟩
  · intro i hi
    exact endpointOffset_increment_eq_support rate rewards C_star C_h u t a z i

/-- Every supported increment is the change from the actual original-prefix
run before date `q` to that same run after appending its actual cell. The
successor API and the one-cell run law agree on the full readout. -/
theorem endpointSupportIncrement_actual_append (a : Fin p.K) (z : Z)
    (d : EndpointSupportDate rate rewards C_star C_h u t z) :
    ∃ inputs cell,
      ReferenceFirstCollectionRenewalFutureNumericalPrefix.optionalPrefixCells
        (ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells
          rate rewards C_star C_h u t d.1.val z) = some inputs ∧
      ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureCell
        rate rewards C_star C_h u t z d.1 (Classical.choose d.2) = some cell ∧
      ReferenceFirstCollectionRenewalFutureNumericalPrefix.futureCell
        rate rewards C_star C_h u t d.1 z = some cell ∧
      actualPrefixReadout rate rewards C_star C_h u t d.1.val z =
        some (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
          (RecordedQueueRun.run
            (_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate)
            inputs)) ∧
      actualPrefixReadout rate rewards C_star C_h u t (d.1.val + 1) z =
        some (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
          (RecordedQueueRun.run
            (_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate)
            (inputs ++ [cell]))) ∧
      actualPrefixReadout rate rewards C_star C_h u t (d.1.val + 1) z =
        some (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
          (RecordedQueueRun.step
            (_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate)
            (RecordedQueueRun.run
              (_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate)
              inputs) cell)) ∧
      endpointSupportIncrement rate rewards C_star C_h u t z a d =
        Real.exp (CanonicalRecordingRates.beta p rate.eta.val *
          (((ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
            (RecordedQueueRun.run
              (_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate)
              (inputs ++ [cell]))).1 a).2 : ℝ) /
            ((_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ)) -
        Real.exp (CanonicalRecordingRates.beta p rate.eta.val *
          (((ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
            (RecordedQueueRun.run
              (_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate)
              inputs)).1 a).2 : ℝ) /
            ((_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ)) ∧
      ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
          (RecordedQueueRun.run
            (_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate)
            (inputs ++ [cell])) =
        ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
          (RecordedQueueRun.step
            (_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate)
            (RecordedQueueRun.run
              (_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate)
              inputs) cell) ∧
      RecordedQueueRun.run
          (_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate)
          (inputs ++ [cell]) =
        RecordedQueueRun.step
          (_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate)
          (RecordedQueueRun.run
            (_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate)
            inputs) cell := by
  rcases d with ⟨q, hdate⟩
  let hfuture := Classical.choose hdate
  let hsupport := Classical.choose_spec hdate
  have hqend := (ReferenceFirstCollectionRenewalFutureSliceEndpoint.supportTest_iff_before_endpoint
    rate rewards C_star C_h u t z q hfuture).mp hsupport
  have hcellPresent := endpointSliceCell_present rate rewards C_star C_h u t z q hfuture hqend
  obtain ⟨cell, hcell⟩ := Option.isSome_iff_exists.mp hcellPresent
  have hcellActual := ReferenceFirstCollectionRenewalFutureRetainedMoments.futureSliceCell_eq_unmasked
    rate rewards C_star C_h u t q hfuture z cell hcell
  have hpriorPresent :=
    ReferenceFirstCollectionRenewalFutureSliceEndpoint.futurePrefixReadout_present_through_endpoint
      rate rewards C_star C_h u t z q.val (by
        change t.val + 1 ≤ q.val
        exact Nat.le_of_lt hfuture) (Nat.le_of_lt hqend)
  have hpriorInputsPresent :
      (ReferenceFirstCollectionRenewalFutureNumericalPrefix.optionalPrefixCells
        (ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells
          rate rewards C_star C_h u t q.val z)).isSome = true := by
    simpa [actualPrefixReadout,
      ReferenceFirstCollectionRenewalFutureNumericalPrefix.futurePrefixReadout,
      ReferenceFirstCollectionRenewalFutureNumericalPrefix.optionalPrefixReadout] using hpriorPresent
  obtain ⟨inputs, hinputs⟩ := Option.isSome_iff_exists.mp hpriorInputsPresent
  have hqbegin : endpointBegin t ≤ q.val := by
    change t.val + 1 ≤ q.val
    omega
  have hqafterBegin : endpointBegin t ≤ q.val + 1 := by
    change t.val + 1 ≤ q.val + 1
    omega
  have hqafterEnd : q.val + 1 ≤ endpointEnd rate rewards C_star C_h u t z := by
    exact Nat.succ_le_of_lt hqend
  have hinputs' : List.mapM id
      (ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells
        rate rewards C_star C_h u t q.val z) = some inputs := hinputs
  change List.mapM id
      (ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells
        rate rewards C_star C_h u t q.val z) = some inputs at hinputs'
  have hpriorReadout :
      actualReadoutAt rate rewards C_star C_h u t z
        ⟨q.val, ⟨hqbegin, Nat.le_of_lt hqend⟩⟩ =
      ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
        (RecordedQueueRun.run
          (_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate) inputs) := by
    simp [actualReadoutAt, actualPrefixReadout,
      ReferenceFirstCollectionRenewalFutureNumericalPrefix.futurePrefixReadout,
      ReferenceFirstCollectionRenewalFutureNumericalPrefix.optionalPrefixReadout, hinputs]
  have hcalendarSucc :=
    ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells_succ
      rate rewards C_star C_h u t q z hfuture
  have happendInputs :
      ReferenceFirstCollectionRenewalFutureNumericalPrefix.optionalPrefixCells
        (ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells
          rate rewards C_star C_h u t (q.val + 1) z) = some (inputs ++ [cell]) := by
    rw [hcalendarSucc, hcellActual]
    change List.mapM id
      (ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells
          rate rewards C_star C_h u t q.val z ++ [some cell]) = _
    rw [List.mapM_append, hinputs']
    simp
  have hafterPresent :=
    ReferenceFirstCollectionRenewalFutureSliceEndpoint.futurePrefixReadout_present_through_endpoint
      rate rewards C_star C_h u t z (q.val + 1) (by
        change t.val + 1 ≤ q.val + 1
        omega) hqafterEnd
  have hafterRun :
      actualReadoutAt rate rewards C_star C_h u t z
        ⟨q.val + 1, ⟨hqafterBegin, hqafterEnd⟩⟩ =
      ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
        (RecordedQueueRun.run
          (_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate)
          (inputs ++ [cell])) := by
    simp [actualReadoutAt, actualPrefixReadout,
      ReferenceFirstCollectionRenewalFutureNumericalPrefix.futurePrefixReadout,
      ReferenceFirstCollectionRenewalFutureNumericalPrefix.optionalPrefixReadout, happendInputs]
  have hafterStep :
      actualPrefixReadout rate rewards C_star C_h u t (q.val + 1) z =
        some (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
          (RecordedQueueRun.step
            (_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate)
            (RecordedQueueRun.run
              (_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate)
              inputs) cell)) := by
    change ReferenceFirstCollectionRenewalFutureNumericalPrefix.futurePrefixReadout
      rate rewards C_star C_h u t (q.val + 1) z = _
    rw [ReferenceFirstCollectionRenewalFutureNumericalPrefix.futurePrefixReadout_succ
      rate rewards C_star C_h u t q z hfuture]
    simp [hinputs, hcellActual]
  have hpriorOption :
      actualPrefixReadout rate rewards C_star C_h u t q.val z =
        some (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
          (RecordedQueueRun.run
            (_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate)
            inputs)) := by
    simp [actualPrefixReadout,
      ReferenceFirstCollectionRenewalFutureNumericalPrefix.futurePrefixReadout,
      ReferenceFirstCollectionRenewalFutureNumericalPrefix.optionalPrefixReadout, hinputs]
  have hafterOption :
      actualPrefixReadout rate rewards C_star C_h u t (q.val + 1) z =
        some (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
          (RecordedQueueRun.run
            (_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate)
            (inputs ++ [cell]))) := by
    simp [actualPrefixReadout,
      ReferenceFirstCollectionRenewalFutureNumericalPrefix.futurePrefixReadout,
      ReferenceFirstCollectionRenewalFutureNumericalPrefix.optionalPrefixReadout,
      happendInputs]
  have hrun := ReferenceFirstCollectionRenewalFutureNumericalPrefix.run_append_one rate inputs cell
  have hafterStepReadout :
      actualReadoutAt rate rewards C_star C_h u t z
        ⟨q.val + 1, ⟨hqafterBegin, hqafterEnd⟩⟩ =
      ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
        (RecordedQueueRun.step
          (_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate)
          (RecordedQueueRun.run
            (_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate)
            inputs) cell) := by
    simp [actualReadoutAt, hafterStep]
  have hreadoutAppendStep := hafterRun.symm.trans hafterStepReadout
  have hincrement : endpointSupportIncrement rate rewards C_star C_h u t z a
      ⟨q, ⟨hfuture, hsupport⟩⟩ =
      Real.exp (CanonicalRecordingRates.beta p rate.eta.val *
        (((ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
          (RecordedQueueRun.run
            (_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate)
            (inputs ++ [cell]))).1 a).2 : ℝ) /
          ((_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ)) -
      Real.exp (CanonicalRecordingRates.beta p rate.eta.val *
        (((ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
          (RecordedQueueRun.run
            (_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate)
            inputs)).1 a).2 : ℝ) /
          ((_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ)) := by
    change actualBacklogExpAt rate rewards C_star C_h u t z a
        ⟨q.val + 1, ⟨hqafterBegin, hqafterEnd⟩⟩ -
      actualBacklogExpAt rate rewards C_star C_h u t z a
        ⟨q.val, ⟨hqbegin, Nat.le_of_lt hqend⟩⟩ = _
    unfold actualBacklogExpAt
    rw [hafterRun, hpriorReadout]
  refine ⟨inputs, cell, hinputs, hcell, hcellActual, hpriorOption, hafterOption,
    hafterStep, hincrement, hreadoutAppendStep, hrun⟩

/-- Threshold retention on the inclusive actual endpoint, with its local
presence input discharged from endpoint geometry. -/
theorem actual_endpoint_threshold_iff (a : Fin p.K) (z : Z) :
    (∃ n, endpointBegin t ≤ n ∧
      n ≤ endpointEnd rate rewards C_star C_h u t z ∧
      ∃ on, actualPrefixReadout rate rewards C_star C_h u t n z = some on ∧
      ((on.1 a).2 : ℝ) /
        ((_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ) >
          1 / (32 * rate.eta.val)) ↔
    ∃ ok, actualPrefixReadout rate rewards C_star C_h u t
        (endpointEnd rate rewards C_star C_h u t z) z = some ok ∧
      ((ok.1 a).2 : ℝ) /
        ((_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ) >
          1 / (32 * rate.eta.val) := by
  have hbounds := ReferenceFirstCollectionRenewalFutureSliceEndpoint.endpoint_bounds
    rate rewards C_star C_h u t z
  rcases hbounds with ⟨hbEnd, hEndK, hkT⟩
  have hsource :
      ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceStart
    rate rewards C_star C_h u t z ≤ endpointBegin t := by
    have hs := ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceStart_le_call
      rate rewards C_star C_h u t z
    change ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceStart
      rate rewards C_star C_h u t z ≤ t.val + 1
    omega
  have hpresent :
      (actualPrefixReadout rate rewards C_star C_h u t
        (endpointEnd rate rewards C_star C_h u t z) z).isSome = true := by
    change (ReferenceFirstCollectionRenewalFutureSliceEndpoint.endpointReadout
      rate rewards C_star C_h u t z).isSome = true
    exact
      ReferenceFirstCollectionRenewalFutureSliceEndpoint.endpointReadout_present
        rate rewards C_star C_h u t z
  have hbk : endpointBegin t ≤
      endpointEnd rate rewards C_star C_h u t z := hbEnd.trans hEndK
  exact ReferenceFirstCollectionRenewalCalendarOverflowRetention.actual_calendar_threshold_iff
    rate rewards C_star C_h u t a (endpointBegin t)
    (endpointEnd rate rewards C_star C_h u t z) z hsource hbk hkT hpresent

/-- Once an actual prefix date has detected overflow, all later dates through
the inclusive endpoint retain every score/backlog pair and append exactly the
disabled zero histories. -/
theorem actual_endpoint_overflow_suffix_retention (n : ℕ) (z : Z)
    (hbn : endpointBegin t ≤ n)
    (hnk : n ≤ endpointEnd rate rewards C_star C_h u t z)
    (on : (Fin p.K → ℕ × ℕ) × (Bool × (Fin p.K → List (Bool × ℕ))))
    (hon : actualPrefixReadout rate rewards C_star C_h u t n z = some on)
    (hoverflow : on.2.1 = true) :
    ∃ ok, actualPrefixReadout rate rewards C_star C_h u t
      (endpointEnd rate rewards C_star C_h u t z) z = some ok ∧ ok.2.1 = true ∧
      (∀ a, ok.1 a = on.1 a) ∧
      (∀ a, ok.2.2 a = on.2.2 a ++ List.replicate
        (endpointEnd rate rewards C_star C_h u t z - n) (false, 0)) := by
  have hbounds := ReferenceFirstCollectionRenewalFutureSliceEndpoint.endpoint_bounds
    rate rewards C_star C_h u t z
  rcases hbounds with ⟨hbEnd, hEndK, hkT⟩
  have hsource :
      ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceStart
        rate rewards C_star C_h u t z ≤ n := by
    have hs := ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceStart_le_call
      rate rewards C_star C_h u t z
    change t.val + 1 ≤ n at hbn
    omega
  have hpresent :
      (actualPrefixReadout rate rewards C_star C_h u t
        (endpointEnd rate rewards C_star C_h u t z) z).isSome = true := by
    change (ReferenceFirstCollectionRenewalFutureSliceEndpoint.endpointReadout
      rate rewards C_star C_h u t z).isSome = true
    exact
      ReferenceFirstCollectionRenewalFutureSliceEndpoint.endpointReadout_present
        rate rewards C_star C_h u t z
  exact ReferenceFirstCollectionRenewalCalendarOverflowRetention.actual_calendar_overflow_suffix_retention
    rate rewards C_star C_h u t n
      (endpointEnd rate rewards C_star C_h u t z) z hsource hnk hkT hpresent on hon hoverflow

/-- A finite sequence telescopes by cancelling adjacent differences. -/
private theorem fin_telescope {n : ℕ} (f : Fin (n + 1) → ℝ) :
    f (Fin.last n) = f 0 + ∑ i : Fin n, (f i.succ - f i.castSucc) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hih := ih (fun i => f i.castSucc)
      have hzero : Fin.castSucc (0 : Fin (n + 1)) = (0 : Fin (n + 2)) := by
        apply Fin.ext
        simp
      rw [hzero] at hih
      have hfirst :
          (∑ i : Fin n, (f (Fin.castSucc i).succ - f (Fin.castSucc i).castSucc)) =
            ∑ i : Fin n, (f i.succ.castSucc - f i.castSucc.castSucc) := by
        apply Finset.sum_congr rfl
        intro i hi
        congr 1
      rw [Fin.sum_univ_castSucc]
      rw [hfirst]
      have hnext : (Fin.last n).succ = Fin.last (n + 1) := by
        apply Fin.ext
        simp
      rw [← hnext]
      linear_combination hih

/-- Endpoint values expressed over the half-open interval `[j,k)`.  The index
`i : Fin (k-j)` names the actual date `j+i`; no action at the terminal prefix
`k=T` is introduced. -/
private theorem endpoint_offset_exp_telescope (a : Fin p.K) (z : Z) :
    endpointOffsetExp rate rewards C_star C_h u t z a
        (Fin.last (endpointEnd rate rewards C_star C_h u t z -
          endpointTelescopeStart rate rewards C_star C_h u t z)) =
      endpointOffsetExp rate rewards C_star C_h u t z a 0 +
        ∑ i : Fin (endpointEnd rate rewards C_star C_h u t z -
          endpointTelescopeStart rate rewards C_star C_h u t z),
          (endpointOffsetExp rate rewards C_star C_h u t z a i.succ -
            endpointOffsetExp rate rewards C_star C_h u t z a i.castSucc) := by
  exact fin_telescope (endpointOffsetExp rate rewards C_star C_h u t z a)

/-- The full actual exponential at the inclusive endpoint equals its value at
`j=min(b+1,k)` plus the increments over exactly the genuine future dates
selected by the source support test. The endpoint readout itself remains
present in the identity even when the next-date support exits. -/
theorem actual_endpoint_exp_telescope (a : Fin p.K) (z : Z) :
    actualBacklogExpAt rate rewards C_star C_h u t z a
        ⟨endpointEnd rate rewards C_star C_h u t z,
          ⟨by
            have h := ReferenceFirstCollectionRenewalFutureSliceEndpoint.endpoint_bounds
              rate rewards C_star C_h u t z
            exact h.1.trans h.2.1,
            le_rfl⟩⟩ =
      actualBacklogExpAt rate rewards C_star C_h u t z a
          ⟨endpointTelescopeStart rate rewards C_star C_h u t z,
            ⟨by
              have h := ReferenceFirstCollectionRenewalFutureSliceEndpoint.endpoint_bounds
                rate rewards C_star C_h u t z
              change ReferenceFirstCollectionRenewalFutureSliceEndpoint.beginning t ≤
                min (ReferenceFirstCollectionRenewalFutureSliceEndpoint.beginning t + 1)
                  (endpointEnd rate rewards C_star C_h u t z)
              exact Nat.le_min.mpr ⟨by omega, h.1.trans h.2.1⟩,
              min_le_right _ _⟩⟩ +
        ∑ d : EndpointSupportDate rate rewards C_star C_h u t z,
          endpointSupportIncrement rate rewards C_star C_h u t z a d := by
  let k := endpointEnd rate rewards C_star C_h u t z
  let j := endpointTelescopeStart rate rewards C_star C_h u t z
  have hbounds := ReferenceFirstCollectionRenewalFutureSliceEndpoint.endpoint_bounds
    rate rewards C_star C_h u t z
  have hbk : endpointBegin t ≤ k := by
    change ReferenceFirstCollectionRenewalFutureSliceEndpoint.beginning t ≤
      ReferenceFirstCollectionRenewalFutureSliceEndpoint.endpointIndex
        rate rewards C_star C_h u t z
    exact hbounds.1.trans hbounds.2.1
  have hbj : endpointBegin t ≤ j := by
    change ReferenceFirstCollectionRenewalFutureSliceEndpoint.beginning t ≤
      min (ReferenceFirstCollectionRenewalFutureSliceEndpoint.beginning t + 1) k
    exact Nat.le_min.mpr ⟨by omega, hbk⟩
  have hjk : j ≤ k := by
    change min _ k ≤ k
    exact min_le_right _ _
  let endDate : EndpointDate rate rewards C_star C_h u t z :=
    ⟨k, ⟨hbk, le_rfl⟩⟩
  let startDate : EndpointDate rate rewards C_star C_h u t z :=
    ⟨j, ⟨hbj, hjk⟩⟩
  have hlast : endpointOffsetExp rate rewards C_star C_h u t z a
      (Fin.last (k - j)) =
      actualBacklogExpAt rate rewards C_star C_h u t z a endDate := by
    simp [endpointOffsetExp, actualBacklogExpAt, endDate, k, j,
      Nat.add_sub_of_le hjk]
  have hfirst : endpointOffsetExp rate rewards C_star C_h u t z a 0 =
      actualBacklogExpAt rate rewards C_star C_h u t z a startDate := by
    simp [endpointOffsetExp, actualBacklogExpAt, startDate, j]
  have htelescope := endpoint_offset_exp_telescope rate rewards C_star C_h u t a z
  have hsum := endpoint_telescope_sum_reindex rate rewards C_star C_h u t a z
  rw [hlast, hfirst, hsum] at htelescope
  exact htelescope

end Bandits.Support.ReferenceFirstCollectionRenewalEndpointTelescope

end
