/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionRenewalEndpointOverflowBound
public import Bandits.Support.ReferenceFirstCollectionActualCallExponentialQueueEstimate
public import Bandits.Support.ReferenceFirstCollectionRenewalNextDateExponentialStep

import Mathlib.Tactic

/-!
# Original-source renewal entry energy

Identify the current first-call exponential and the immediate entry energy
on the same original renewal source. Every optional calendar slot is retained.
An absent immediate cell preserves the inherited scalar energy; it does not
produce a present successor prefix. The stopped numerical run retains the
first overflow update and all accepted histories.

Sources: `04_slow_fast_learner.tex:140-188,245-290`,
`06_interruptions.tex:355-426`, and `05_binary_transport.tex:352-431` in the
pinned ZIP4 manuscript. These are internal numerical identities for the
first-call renewal slice, for use by `RenewalEntryEnergySum`.
-/

@[expose] public section

noncomputable section

open Bandits.Support ConstructorDimensions
open scoped Classical

namespace Bandits.Support.ReferenceFirstCollectionRenewalEntryEnergyBridge

open _root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix
  (start sourceRecords pastCells incoming callRecord)
open _root_.Bandits.Support.ReferenceFirstCollectionRenewalSourceCurrentPrefix
  (wholeCell wholePostReadout completeObservation)
open _root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueueMeasurability (stateReadout)
open _root_.Bandits.Support.ReferenceFirstCollectionRenewalFutureNumericalPrefix
  (calendarCells calendarCell sourceStart optionalPrefixCells
    optionalPrefixReadout futurePrefixReadout)
open _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix
  (currentCells currentState nextRecord nextCell)
open _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateExponentialStep
  (expBacklogBefore expBacklogAfter backlogBefore)
open _root_.Bandits.Support.ReferenceFirstCollectionRenewalEndpointExponentialMoment
  (entryEnergy entryIndex endpointIndex)
open _root_.Bandits.Support.ReferenceFirstCollectionCurrentRetainedGate (pastSlots pastCells?)
open _root_.Bandits.Support.ReferenceFirstCollectionCurrentNumericalCell (currentCell)
open _root_.Bandits.Support.ReferenceFirstCollectionCurrentQueueReadout (after?)
open _root_.Bandits.Support.ReferenceCompleteFirstPhaseObservationRecovery
  (rawLiveNumericalDecoder rawCollectionNumericalDecoder)
open _root_.Bandits.Support.ReferenceCompleteObservationPrefixInformation (datePrefix)
open _root_.Bandits.Support.ReferenceCompleteNumericalBranchObservation (encodeNumerical)

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ) (u t : Fin p.T)

local notation "Z" => ReferenceFirstCollectionRenewalFutureControlLaw.Source
  rate rewards C_star C_h u t
local notation "Q" => ReferenceFirstLaunchNumericalCell.queueParameters rate
local notation "β" => CanonicalRecordingRates.beta p rate.eta.val
local notation "b" => t.val + 1

private theorem start_le_call (z : Z) :
    start rate rewards C_star C_h u t z ≤ t.val := by
  have hb := ReferenceFirstCollectionRenewalIncomingQueuePrefix.actual_boundaries
    rate rewards C_star C_h u t z
  omega

private theorem launchBy_call (z : Z) :
    ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
      rate rewards C_star C_h t.val z.val := by
  refine ⟨?_, ?_⟩
  · exact ReferenceFirstCollectionRenewalIncomingQueuePrefix.crossing
      rate rewards C_star C_h u t z
  · exact start_le_call rate rewards C_star C_h u t z

private theorem slots_take {A B : Type*} (records : List A)
    (f : A → Option B) (n : ℕ) (hn : n ≤ records.length) :
    (List.range n).map (fun k => records[k]?.bind f) =
      (records.take n).map f := by
  apply List.ext_getElem?
  intro k
  by_cases hk : k < n
  · rw [List.getElem?_map, List.getElem?_range hk, Option.map_some,
      List.getElem?_map, List.getElem?_take_of_lt hk,
      List.getElem?_eq_getElem (hk.trans_le hn)]
    rfl
  · have hleft : (List.range n).length ≤ k := by
      rw [List.length_range]
      omega
    have hright : (records.take n).length ≤ k := by
      rw [List.length_take]
      omega
    rw [List.getElem?_map, List.getElem?_eq_none hleft,
      List.getElem?_map, List.getElem?_eq_none hright]
    rfl

private theorem pastSlots_eq_calendarCells (z : Z) :
    pastSlots rate rewards C_star C_h t z.val =
      calendarCells rate rewards C_star C_h u t t.val z := by
  have hlen := ReferenceFirstCollectionRenewalIncomingQueuePrefix.sourceRecords_length
    rate rewards C_star C_h u t z
  have hs := start_le_call rate rewards C_star C_h u t z
  have ht := t.isLt
  have hn : t.val - start rate rewards C_star C_h u t z ≤
      (sourceRecords rate rewards C_star C_h u t z).length := by
    rw [hlen]
    omega
  exact slots_take (sourceRecords rate rewards C_star C_h u t z)
    (calendarCell rate) (t.val - start rate rewards C_star C_h u t z) hn

private theorem rawLive_past_take (z : Z) :
    rawLiveNumericalDecoder rate (datePrefix rate t.val
        (completeObservation rate rewards C_star C_h u t z)) =
      (rawLiveNumericalDecoder rate
        (completeObservation rate rewards C_star C_h u t z)).take
          (t.val - start rate rewards C_star C_h u t z) := by
  unfold completeObservation
  rw [ReferenceCompleteObservationPrefixInformation.datePrefix_eq_take
    rate rewards C_star C_h t.val t.isLt.le z.val]
  exact List.map_take

private theorem rawCollection_past_take (z : Z) :
    rawCollectionNumericalDecoder rate (datePrefix rate t.val
        (completeObservation rate rewards C_star C_h u t z)) =
      (rawCollectionNumericalDecoder rate
        (completeObservation rate rewards C_star C_h u t z)).take
          (t.val - start rate rewards C_star C_h u t z) := by
  unfold completeObservation
  rw [ReferenceCompleteObservationPrefixInformation.datePrefix_eq_take
    rate rewards C_star C_h t.val t.isLt.le z.val]
  exact List.map_take

private theorem zipWith_map_same {A B C D : Type*} (xs : List A)
    (f : B → C → D) (g : A → B) (h : A → C) :
    List.zipWith f (xs.map g) (xs.map h) =
      xs.map (fun x => f (g x) (h x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.map_cons, List.zipWith_cons_cons]
      exact congrArg (List.cons (f (g x) (h x))) ih

private theorem map_option_or {A B : Type*} (f : A → B)
    (left right : Option A) :
    (left.map f).or (right.map f) = (left.or right).map f := by
  cases left <;> rfl

/-- The original dated decoder join retains every past optional slot. -/
private theorem encoded_past_calendar (z : Z) :
    (calendarCells rate rewards C_star C_h u t t.val z).map
        (Option.map encodeNumerical) =
      (pastCells rate rewards C_star C_h u t z).map
        (fun c => some (encodeNumerical c)) := by
  have hjoin := ReferenceFirstCollectionRenewalSourceCurrentPrefix.pastCells_rawPrefix_join
    rate rewards C_star C_h u t z
  rw [rawLive_past_take rate rewards C_star C_h u t z,
    rawCollection_past_take rate rewards C_star C_h u t z] at hjoin
  unfold completeObservation at hjoin
  rw [
    ReferenceCompleteFirstPhaseObservationRecovery.rawLiveNumericalDecoder_completeSuffixRecords
      rate rewards C_star C_h z.val,
    ReferenceCompleteFirstPhaseObservationRecovery.rawCollectionNumericalDecoder_completeSuffixRecords
      rate rewards C_star C_h z.val,
    ← List.map_take, ← List.map_take] at hjoin
  rw [zipWith_map_same] at hjoin
  calc
    _ = ((sourceRecords rate rewards C_star C_h u t z).take
        (t.val - start rate rewards C_star C_h u t z)).map
          (fun r =>
            ((ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r).map encodeNumerical).or
              ((ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 r).map
                encodeNumerical)) := by
      simp only [calendarCells, calendarCell, List.map_map, Function.comp_def]
      apply List.map_congr_left
      intro r _
      exact (map_option_or encodeNumerical _ _).symm
    _ = _ := hjoin

private theorem numerical_encoding_injective :
    Function.Injective (encodeNumerical (p := p)) := by
  intro left right h
  cases left with
  | mk le la lr lx lxp lxl lrp =>
    cases right with
    | mk re ra rr rx rxp rxl rrp =>
      simp only [encodeNumerical,
        ReferenceLaterLiveReadoutValuesMeasurability.numericalCoordinates] at h
      cases h
      rfl

private theorem optional_encoding_injective :
    Function.Injective (Option.map (encodeNumerical (p := p))) := by
  intro left right h
  cases left with
  | none => cases right <;> simp_all
  | some left =>
      cases right with
      | none => simp at h
      | some right =>
          have he := numerical_encoding_injective (Option.some.inj h)
          exact congrArg some he

private theorem mapM_present {A : Type*} (cells : List A) :
    (cells.map some).mapM id = some cells := by
  induction cells with
  | nil => rfl
  | cons c cells ih =>
      rw [List.map_cons, List.mapM_cons]
      simp [ih]

/-- Every original pre-call slot is the corresponding canonical incoming
cell, with no filtering, queue-truth premise, or reset at the renewal call. -/
theorem pastCells_eq_original (z : Z) :
    pastCells? rate rewards C_star C_h t z.val =
      some (pastCells rate rewards C_star C_h u t z) := by
  have hencoded := encoded_past_calendar rate rewards C_star C_h u t z
  have hslots : pastSlots rate rewards C_star C_h t z.val =
      (pastCells rate rewards C_star C_h u t z).map some := by
    rw [pastSlots_eq_calendarCells rate rewards C_star C_h u t z]
    apply optional_encoding_injective.list_map
    simpa only [List.map_map, Function.comp_def, Option.map_some] using hencoded
  rw [pastCells?, ite_eq_left (launchBy_call rate rewards C_star C_h u t z), hslots]
  exact mapM_present _

/-- The current calendar lookup is the actual renewal record on `z.val`. -/
theorem currentCell_eq_original (z : Z) :
    currentCell rate rewards C_star C_h t z.val =
      some (wholeCell rate rewards C_star C_h u t z) := by
  have hs := start_le_call rate rewards C_star C_h u t z
  have hstart := ReferenceFirstCollectionRenewalIncomingQueuePrefix.start_eq_physicalStart
    rate rewards C_star C_h u t z
  have hrecord : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z.val =
        some (callRecord rate rewards C_star C_h u t z) := by
    rw [ReferenceSourcePrefixHistoryFiltration.actualRecord, ← hstart, ite_eq_left hs]
    exact List.getElem?_eq_getElem
      (ReferenceFirstCollectionRenewalIncomingQueuePrefix.call_index_lt
        rate rewards C_star C_h u t z)
  rw [currentCell, hrecord, Option.bind_some, ← hstart]
  exact ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholeCell_readout
    rate rewards C_star C_h u t z

/-- The entire current optional readout equals the same whole post-readout,
including its overflow flag and every accepted history. -/
theorem after_eq_wholePostReadout (z : Z) :
    after? rate rewards C_star C_h t z.val =
      some (wholePostReadout rate rewards C_star C_h u t z) := by
  rw [after?, pastCells_eq_original rate rewards C_star C_h u t z,
    Option.bind_some, currentCell_eq_original rate rewards C_star C_h u t z,
    Option.map_some]
  rfl

/-- The incoming next-date energy is the sharp original first-call
post-update exponential at exactly the same original source `z.val`. -/
theorem expBacklogBefore_eq_callXPlus (a : Fin p.K) (z : Z) :
    expBacklogBefore rate rewards C_star C_h u t a z =
      ReferenceFirstCollectionActualCallExponentialQueueEstimate.callXPlus
        rate rewards C_star C_h a z.val := by
  obtain ⟨L, c, hL, hc, _, hplus⟩ :=
    ReferenceFirstCollectionActualCallExponentialQueueEstimate.callXMinus_callXPlus_eq_actualReadouts_of_firstCollectionCall
      rate rewards C_star C_h u t a z.val
      (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallParameter
        rate rewards C_star C_h u t z)
      (ReferenceFirstCollectionRenewalAuxiliaryLaw.firstCollectionCall_eq
        rate rewards C_star C_h u t z)
  have hLeq : L = pastCells rate rewards C_star C_h u t z :=
    Option.some.inj (hL.symm.trans (pastCells_eq_original rate rewards C_star C_h u t z))
  have hceq : c = wholeCell rate rewards C_star C_h u t z :=
    Option.some.inj (hc.symm.trans (currentCell_eq_original rate rewards C_star C_h u t z))
  subst L
  subst c
  rw [hplus]
  have hread := ReferenceFirstCollectionRenewalNextDateExponentialStep.incomingReadout_eq_currentState
    rate rewards C_star C_h u t z
  change Real.exp (β *
      ((((currentState rate rewards C_star C_h u t z).registers a).2 : ℝ) /
        ((Q).n : ℝ))) =
    Real.exp (β *
      ((((wholePostReadout rate rewards C_star C_h u t z).1 a).2 : ℝ) /
        ((Q).n : ℝ)))
  rw [← hread]
  rfl

/-- The immediate calendar append uses the next original physical record.
It does not search forward for a successful numerical cell. -/
theorem calendarCells_immediate_append (z : Z) (hq : b < p.T) :
    calendarCells rate rewards C_star C_h u t (b + 1) z =
      calendarCells rate rewards C_star C_h u t b z ++
        [calendarCell rate (nextRecord rate rewards C_star C_h u t z hq)] := by
  have hs := start_le_call rate rewards C_star C_h u t z
  have hstart := ReferenceFirstCollectionRenewalIncomingQueuePrefix.start_eq_physicalStart
    rate rewards C_star C_h u t z
  have hindex : b - sourceStart rate rewards C_star C_h u t z =
      t.val - start rate rewards C_star C_h u t z + 1 := by
    change t.val + 1 - ReferenceCompletePhysicalHistory.physicalStart
      rate z.val rewards C_star C_h = _
    rw [← hstart]
    omega
  have hlookup :
      (ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceRecords
        rate rewards C_star C_h u t z)[b -
          sourceStart rate rewards C_star C_h u t z]? =
        some (nextRecord rate rewards C_star C_h u t z hq) := by
    rw [hindex]
    exact ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextRecord_lookup
      rate rewards C_star C_h u t z hq
  have hadd : b + 1 - sourceStart rate rewards C_star C_h u t z =
      (b - sourceStart rate rewards C_star C_h u t z) + 1 := by
    change t.val + 1 + 1 - start rate rewards C_star C_h u t z =
      (t.val + 1 - start rate rewards C_star C_h u t z) + 1
    omega
  rw [calendarCells, calendarCells, hadd, List.take_add_one, hlookup,
    List.map_append]
  rfl

/-- Both next-date baselines identify the actual LIVE/collection join,
including the immediate cutoff constructor and its genuine enabled bit. -/
theorem immediate_calendarCell_eq_nextCell (z : Z) (hq : b < p.T) :
    calendarCell rate (nextRecord rate rewards C_star C_h u t z hq) =
      nextCell rate rewards C_star C_h u t z hq := by
  have hread := ReferenceFirstCollectionRenewalNextPhysicalPrefix.next_baseline_readouts
    rate rewards C_star C_h u t z hq
  unfold calendarCell ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextCell
  rw [hread.1, hread.2]

/-- The immediate whole-prefix readout is present exactly when the actual
next optional cell is present. Missing cells retain their calendar position. -/
theorem immediate_prefix_readout (z : Z) (hq : b < p.T) :
    futurePrefixReadout rate rewards C_star C_h u t (b + 1) z =
      match nextCell rate rewards C_star C_h u t z hq with
      | none => none
      | some c => some (stateReadout
          (RecordedQueueRun.step Q (currentState rate rewards C_star C_h u t z) c)) := by
  unfold futurePrefixReadout
  rw [calendarCells_immediate_append rate rewards C_star C_h u t z hq,
    immediate_calendarCell_eq_nextCell rate rewards C_star C_h u t z hq,
    ReferenceFirstCollectionRenewalFutureNumericalPrefix.optionalPrefixReadout_append,
    ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells_current_mapM
      rate rewards C_star C_h u t z]
  cases nextCell rate rewards C_star C_h u t z hq <;> rfl

/-- The selected successor is inside the inclusive endpoint precisely on
the present-cell branch. No present successor is asserted on failure. -/
theorem nextCell_present_iff_before_endpoint (z : Z) (hq : b < p.T) :
    (nextCell rate rewards C_star C_h u t z hq).isSome = true ↔
      b < endpointIndex rate rewards C_star C_h u t z := by
  have hiff := ReferenceFirstCollectionRenewalEndpointExponentialMoment.immediate_prefix_present_iff
    rate rewards C_star C_h u t z hq
  rw [immediate_prefix_readout rate rewards C_star C_h u t z hq] at hiff
  cases hc : nextCell rate rewards C_star C_h u t z hq <;>
    simpa only [hc, Option.isSome_none, Option.isSome_some] using hiff

/-- At a present immediate cell, the actual entry date is `b + 1`. -/
theorem entryIndex_of_nextCell_some (z : Z) (hq : b < p.T)
    (c : RecordedQueueRun.RoundInput p.K)
    (hc : nextCell rate rewards C_star C_h u t z hq = some c) :
    entryIndex rate rewards C_star C_h u t z = b + 1 := by
  have hk := (nextCell_present_iff_before_endpoint rate rewards C_star C_h u t z hq).mp
    (by rw [hc]; rfl)
  exact min_eq_left (by omega)

/-- A missing immediate cell makes the actual endpoint and entry date equal
to the current boundary. The inherited readout remains the current one. -/
theorem entryIndex_of_nextCell_none (z : Z) (hq : b < p.T)
    (hc : nextCell rate rewards C_star C_h u t z hq = none) :
    endpointIndex rate rewards C_star C_h u t z = b ∧
      entryIndex rate rewards C_star C_h u t z = b := by
  have hnot : ¬ b < endpointIndex rate rewards C_star C_h u t z := by
    intro hk
    have hp := (nextCell_present_iff_before_endpoint rate rewards C_star C_h u t z hq).mpr hk
    rw [hc] at hp
    contradiction
  have hb := ReferenceFirstCollectionRenewalFutureSliceEndpoint.endpoint_bounds
    rate rewards C_star C_h u t z
  have hle : b ≤ endpointIndex rate rewards C_star C_h u t z := hb.1.trans hb.2.1
  have he : endpointIndex rate rewards C_star C_h u t z = b := by omega
  exact ⟨he, by simp only [entryIndex, he, min_eq_right (Nat.le_succ b)]⟩

/-- The entry readout uses the same present immediate update or the same
inherited readout. The option-or rule preserves the original overflow bit. -/
theorem entry_prefix_readout (z : Z) (hq : b < p.T) :
    futurePrefixReadout rate rewards C_star C_h u t
        (entryIndex rate rewards C_star C_h u t z) z =
      some (match nextCell rate rewards C_star C_h u t z hq with
        | none => wholePostReadout rate rewards C_star C_h u t z
        | some c => stateReadout
            (RecordedQueueRun.step Q (currentState rate rewards C_star C_h u t z) c)) := by
  rw [ReferenceFirstCollectionRenewalEndpointExponentialMoment.entry_prefix_eq_option_or
    rate rewards C_star C_h u t z hq,
    immediate_prefix_readout rate rewards C_star C_h u t z hq]
  have hcurrent := ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells_current_readout
    rate rewards C_star C_h u t z
  change futurePrefixReadout rate rewards C_star C_h u t b z = _ at hcurrent
  rw [hcurrent]
  cases nextCell rate rewards C_star C_h u t z hq <;> rfl

private theorem actual_entry_readout (z : Z) (hq : b < p.T) :
    ReferenceFirstCollectionRenewalEndpointTelescope.actualReadoutAt
        rate rewards C_star C_h u t z
        ⟨entryIndex rate rewards C_star C_h u t z,
          ⟨by
            have hb := ReferenceFirstCollectionRenewalFutureSliceEndpoint.endpoint_bounds
              rate rewards C_star C_h u t z
            change b ≤ min (b + 1) (endpointIndex rate rewards C_star C_h u t z)
            exact Nat.le_min.mpr ⟨Nat.le_succ b, hb.1.trans hb.2.1⟩,
            min_le_right _ _⟩⟩ =
      match nextCell rate rewards C_star C_h u t z hq with
      | none => wholePostReadout rate rewards C_star C_h u t z
      | some c => stateReadout
          (RecordedQueueRun.step Q (currentState rate rewards C_star C_h u t z) c) := by
  unfold ReferenceFirstCollectionRenewalEndpointTelescope.actualReadoutAt
  simp only [ReferenceFirstCollectionRenewalEndpointTelescope.actualPrefixReadout,
    entry_prefix_readout rate rewards C_star C_h u t z hq, Option.get_some]

/-- The actual immediate entry energy is the next-date exponential of the
same stopped physical-record numerical run. Successful LIVE and immediate
cutoff cells both retain their real update, including disabled cutoffs.
Failure, dagger, and absent cells preserve the inherited energy. -/
theorem entryEnergy_eq_expBacklogAfter (hq : b < p.T) (a : Fin p.K) (z : Z) :
    entryEnergy rate rewards C_star C_h u t a z =
      expBacklogAfter rate rewards C_star C_h u t hq a z := by
  have hread := actual_entry_readout rate rewards C_star C_h u t z hq
  unfold entryEnergy ReferenceFirstCollectionRenewalEndpointTelescope.actualBacklogExpAt
  rw [hread]
  cases hc : nextCell rate rewards C_star C_h u t z hq with
  | none =>
      have hpreserve := ReferenceFirstCollectionRenewalNextDateExponentialStep.nextCell_none_preserves_physical_prefix
        rate rewards C_star C_h u t hq a z hc
      rw [hpreserve.2.1]
      have hcurrent := ReferenceFirstCollectionRenewalNextDateExponentialStep.incomingReadout_eq_currentState
        rate rewards C_star C_h u t z
      rw [← hcurrent]
      simp only [expBacklogBefore, backlogBefore, stateReadout, mul_div_assoc]
  | some c =>
      have hphysical := ReferenceFirstCollectionRenewalNextDateExponentialStep.nextCell_some_physical_run
        rate rewards C_star C_h u t hq a z c hc
      rw [hphysical.2.1]
      simp only [stateReadout, mul_div_assoc]

/-- At the terminal boundary the inclusive endpoint and actual entry are
both `T`. No successor action or numerical input at `T` is constructed. -/
theorem terminal_entryIndex (z : Z) (ht : b = p.T) :
    endpointIndex rate rewards C_star C_h u t z = b ∧
      entryIndex rate rewards C_star C_h u t z = b := by
  have hb := ReferenceFirstCollectionRenewalFutureSliceEndpoint.endpoint_bounds
    rate rewards C_star C_h u t z
  have hle : b ≤ endpointIndex rate rewards C_star C_h u t z := hb.1.trans hb.2.1
  have he : endpointIndex rate rewards C_star C_h u t z = b := by
    have hT : endpointIndex rate rewards C_star C_h u t z ≤ p.T := hb.2.2
    omega
  exact ⟨he, by simp only [entryIndex, he, min_eq_right (Nat.le_succ b)]⟩

/-- At a terminal renewal call, the entry energy is the whole current
exponential, retaining any inherited overflow energy without a reset. -/
theorem entryEnergy_eq_expBacklogBefore_of_terminal (ht : b = p.T)
    (a : Fin p.K) (z : Z) :
    entryEnergy rate rewards C_star C_h u t a z =
      expBacklogBefore rate rewards C_star C_h u t a z := by
  have hj := (terminal_entryIndex rate rewards C_star C_h u t z ht).2
  have hcurrent := ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells_current_readout
    rate rewards C_star C_h u t z
  have hread : futurePrefixReadout rate rewards C_star C_h u t
      (entryIndex rate rewards C_star C_h u t z) z =
        some (wholePostReadout rate rewards C_star C_h u t z) := by
    rw [hj]
    exact hcurrent
  unfold entryEnergy ReferenceFirstCollectionRenewalEndpointTelescope.actualBacklogExpAt
    ReferenceFirstCollectionRenewalEndpointTelescope.actualReadoutAt
  simp only [ReferenceFirstCollectionRenewalEndpointTelescope.actualPrefixReadout,
    hread, Option.get_some]
  have hstate := ReferenceFirstCollectionRenewalNextDateExponentialStep.incomingReadout_eq_currentState
    rate rewards C_star C_h u t z
  rw [← hstate]
  simp only [expBacklogBefore, backlogBefore, stateReadout, mul_div_assoc]

end Bandits.Support.ReferenceFirstCollectionRenewalEntryEnergyBridge

end
