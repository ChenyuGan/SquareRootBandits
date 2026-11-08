/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSReferenceFirstCollectionRenewalFutureSliceEndpoint.
Authors: The Bandits Lean Project contributors
-/
module

public import Bandits.Support.ReferenceFirstCollectionOriginalPrefixLearning
public import Bandits.Support.ReferenceFirstCollectionRenewalWeightedCalendarAccounting
public import Bandits.Support.ReferenceFirstCollectionRenewalFutureSliceEndpoint

import Mathlib.Tactic

/-!
# Literal original first-invocation word at a renewal call

The first-invocation word is the existing zero-origin queue word through the
actual whole current cell. Its strict-past slots and call cell come from the
same original physical source and retain every numerical field.

The direct public endpoint input was additionally admitted as
`Bandits.Support.ReferenceFirstCollectionRenewalFutureSliceEndpoint` at hash
`14b14ef00b86a677d2aeeead883db061cb069bf36f7428c5fc60dc339ccb79e1`; the
current dependency-admission receipt is
`private-audit-archive/turn-00984-prefix-dependency-admission.json`.
This records input authorization only.
-/

@[expose] public section

noncomputable section

open Bandits.Support ConstructorDimensions
open scoped Classical

namespace Bandits.Support.ReferenceFirstCollectionRenewalRawPrefixJoin


variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ) (u t : Fin p.T)

local notation "Z" =>
  ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource
    rate rewards C_star C_h u t
local notation "Q" => ReferenceFirstLaunchNumericalCell.queueParameters rate

private theorem start_le_call (z : Z) :
    ReferenceFirstCollectionRenewalIncomingQueuePrefix.start rate rewards C_star C_h u t z ≤ t.val := by
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
    ReferenceFirstCollectionCurrentRetainedGate.pastSlots rate rewards C_star C_h t z.val =
      ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells rate rewards C_star C_h u t t.val z := by
  have hlen := ReferenceFirstCollectionRenewalIncomingQueuePrefix.sourceRecords_length
    rate rewards C_star C_h u t z
  have hs := start_le_call rate rewards C_star C_h u t z
  have ht := t.isLt
  have hn : t.val - ReferenceFirstCollectionRenewalIncomingQueuePrefix.start rate rewards C_star C_h u t z ≤
      (ReferenceFirstCollectionRenewalIncomingQueuePrefix.sourceRecords rate rewards C_star C_h u t z).length := by
    rw [hlen]
    omega
  exact slots_take (ReferenceFirstCollectionRenewalIncomingQueuePrefix.sourceRecords rate rewards C_star C_h u t z)
    (ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCell rate) (t.val - ReferenceFirstCollectionRenewalIncomingQueuePrefix.start rate rewards C_star C_h u t z) hn

private theorem rawLive_past_take (z : Z) :
    ReferenceCompleteFirstPhaseObservationRecovery.rawLiveNumericalDecoder rate (ReferenceCompleteObservationPrefixInformation.datePrefix rate t.val
        (ReferenceFirstCollectionRenewalSourceCurrentPrefix.completeObservation
          rate rewards C_star C_h u t z)) =
      (ReferenceCompleteFirstPhaseObservationRecovery.rawLiveNumericalDecoder rate
        (ReferenceFirstCollectionRenewalSourceCurrentPrefix.completeObservation
          rate rewards C_star C_h u t z)).take
          (t.val - ReferenceFirstCollectionRenewalIncomingQueuePrefix.start rate rewards C_star C_h u t z) := by
  unfold ReferenceFirstCollectionRenewalSourceCurrentPrefix.completeObservation
  rw [ReferenceCompleteObservationPrefixInformation.datePrefix_eq_take
    rate rewards C_star C_h t.val t.isLt.le z.val]
  exact List.map_take

private theorem rawCollection_past_take (z : Z) :
    ReferenceCompleteFirstPhaseObservationRecovery.rawCollectionNumericalDecoder rate (ReferenceCompleteObservationPrefixInformation.datePrefix rate t.val
        (ReferenceFirstCollectionRenewalSourceCurrentPrefix.completeObservation
          rate rewards C_star C_h u t z)) =
      (ReferenceCompleteFirstPhaseObservationRecovery.rawCollectionNumericalDecoder rate
        (ReferenceFirstCollectionRenewalSourceCurrentPrefix.completeObservation
          rate rewards C_star C_h u t z)).take
          (t.val - ReferenceFirstCollectionRenewalIncomingQueuePrefix.start rate rewards C_star C_h u t z) := by
  unfold ReferenceFirstCollectionRenewalSourceCurrentPrefix.completeObservation
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

private theorem encoded_past_calendar (z : Z) :
    (ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells rate rewards C_star C_h u t t.val z).map
        (Option.map ReferenceCompleteNumericalBranchObservation.encodeNumerical) =
      (ReferenceFirstCollectionRenewalIncomingQueuePrefix.pastCells
        rate rewards C_star C_h u t z).map
        (fun c => some (ReferenceCompleteNumericalBranchObservation.encodeNumerical c)) := by
  have hjoin := ReferenceFirstCollectionRenewalSourceCurrentPrefix.pastCells_rawPrefix_join
    rate rewards C_star C_h u t z
  rw [rawLive_past_take rate rewards C_star C_h u t z,
    rawCollection_past_take rate rewards C_star C_h u t z] at hjoin
  unfold ReferenceFirstCollectionRenewalSourceCurrentPrefix.completeObservation at hjoin
  rw [ReferenceCompleteFirstPhaseObservationRecovery.rawLiveNumericalDecoder_completeSuffixRecords
      rate rewards C_star C_h z.val,
    ReferenceCompleteFirstPhaseObservationRecovery.rawCollectionNumericalDecoder_completeSuffixRecords
      rate rewards C_star C_h z.val,
    ← List.map_take, ← List.map_take] at hjoin
  rw [zipWith_map_same] at hjoin
  calc
    _ = ((ReferenceFirstCollectionRenewalIncomingQueuePrefix.sourceRecords rate rewards C_star C_h u t z).take
        (t.val - ReferenceFirstCollectionRenewalIncomingQueuePrefix.start rate rewards C_star C_h u t z)).map
          (fun r =>
            ((ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r).map ReferenceCompleteNumericalBranchObservation.encodeNumerical).or
              ((ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 r).map
                ReferenceCompleteNumericalBranchObservation.encodeNumerical)) := by
      simp only [ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells, ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCell, List.map_map, Function.comp_def]
      apply List.map_congr_left
      intro r _
      exact (map_option_or ReferenceCompleteNumericalBranchObservation.encodeNumerical _ _).symm
    _ = _ := hjoin

private theorem numerical_encoding_injective :
    Function.Injective (ReferenceCompleteNumericalBranchObservation.encodeNumerical (p := p)) := by
  intro left right h
  cases left with
  | mk le la lr lx lxp lxl lrp =>
    cases right with
    | mk re ra rr rx rxp rxl rrp =>
      simp only [ReferenceCompleteNumericalBranchObservation.encodeNumerical,
        ReferenceLaterLiveReadoutValuesMeasurability.numericalCoordinates] at h
      cases h
      rfl

private theorem optional_encoding_injective :
    Function.Injective (Option.map (ReferenceCompleteNumericalBranchObservation.encodeNumerical (p := p))) := by
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

private theorem pastCells_eq_original (z : Z) :
    ReferenceFirstCollectionCurrentRetainedGate.pastCells?
        rate rewards C_star C_h t z.val =
      some (ReferenceFirstCollectionRenewalIncomingQueuePrefix.pastCells
        rate rewards C_star C_h u t z) := by
  have hencoded := encoded_past_calendar rate rewards C_star C_h u t z
  have hslots : ReferenceFirstCollectionCurrentRetainedGate.pastSlots rate rewards C_star C_h t z.val =
      (ReferenceFirstCollectionRenewalIncomingQueuePrefix.pastCells
        rate rewards C_star C_h u t z).map some := by
    rw [pastSlots_eq_calendarCells rate rewards C_star C_h u t z]
    apply optional_encoding_injective.list_map
    simpa only [List.map_map, Function.comp_def, Option.map_some] using hencoded
  rw [ReferenceFirstCollectionCurrentRetainedGate.pastCells?,
    ite_eq_left (launchBy_call rate rewards C_star C_h u t z), hslots]
  exact mapM_present _

private theorem currentCell_eq_original (z : Z) :
    ReferenceFirstCollectionCurrentNumericalCell.currentCell rate rewards C_star C_h t z.val =
      some (ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholeCell
        rate rewards C_star C_h u t z) := by
  have hs := start_le_call rate rewards C_star C_h u t z
  have hstart := ReferenceFirstCollectionRenewalIncomingQueuePrefix.start_eq_physicalStart
    rate rewards C_star C_h u t z
  have hrecord : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z.val =
        some (ReferenceFirstCollectionRenewalIncomingQueuePrefix.callRecord
          rate rewards C_star C_h u t z) := by
    rw [ReferenceSourcePrefixHistoryFiltration.actualRecord, ← hstart, ite_eq_left hs]
    exact List.getElem?_eq_getElem
      (ReferenceFirstCollectionRenewalIncomingQueuePrefix.call_index_lt
        rate rewards C_star C_h u t z)
  rw [ReferenceFirstCollectionCurrentNumericalCell.currentCell, hrecord,
    Option.bind_some, ← hstart]
  exact ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholeCell_readout
    rate rewards C_star C_h u t z

private theorem firstInvocationCells_current (z : Z) :
    ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationCells?
      rate rewards C_star C_h z.val =
      some (ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentCells
        rate rewards C_star C_h u t z) := by
  have hfirst : z.val ∈ ReferenceCalendarCollectionCallControlLaw.firstCell
      rate rewards C_star C_h u t := by
    change (ReferenceFirstCollectionSamplerCall.firstCollectionCall
      rate rewards C_star C_h z.val).map (fun c => (c.1, c.2.1)) = some (u, t)
    rw [ReferenceFirstCollectionRenewalAuxiliaryLaw.firstCollectionCall_eq
      rate rewards C_star C_h u t z]
    rfl
  obtain ⟨L, c, hL, hc, henabled, hword, _hrun⟩ :=
    ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationCells?_firstCell_append
      rate rewards C_star C_h u t z.val hfirst
  have hpast := pastCells_eq_original rate rewards C_star C_h u t z
  have hcurrent := currentCell_eq_original rate rewards C_star C_h u t z
  have hLeq : L = ReferenceFirstCollectionRenewalIncomingQueuePrefix.pastCells
      rate rewards C_star C_h u t z := Option.some.inj (hL.symm.trans hpast)
  have hceq : c = ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholeCell
      rate rewards C_star C_h u t z := Option.some.inj (hc.symm.trans hcurrent)
  subst L
  subst c
  simpa only [ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentCells] using hword

/-- The original first-invocation word is exactly the existing full current
renewal prefix, including the actual call cell and every inherited register. -/
public theorem renewalCells_firstInvocation_eq_current (z : Z) :
    ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationCells?
      rate rewards C_star C_h z.val =
      some (ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentCells
        rate rewards C_star C_h u t z) :=
  firstInvocationCells_current rate rewards C_star C_h u t z

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
              subst cells
              have htail := ih ht
              simp [htail]

private theorem mapM_id_take {α : Type*} (slots : List (Option α))
    (cells : List α) (h : slots.mapM id = some cells) (n : ℕ) :
    (slots.take n).mapM id = some (cells.take n) := by
  induction slots generalizing cells n with
  | nil =>
      have hc : cells = [] := (Option.some.inj h).symm
      subst cells
      simp
  | cons slot slots ih =>
      cases slot with
      | none => simp [List.mapM_cons] at h
      | some a =>
          cases ht : slots.mapM id with
          | none => simp [List.mapM_cons, ht] at h
          | some tail =>
              have hc : a :: tail = cells := by
                simpa [List.mapM_cons, ht] using h
              subst cells
              cases n with
              | zero => rfl
              | succ n => simp [List.mapM_cons, ih tail ht n]

private theorem endpoint_prefix_take (z : Z)
    (L : List (RecordedQueueRun.RoundInput p.K))
    (hendpoint : ReferenceFirstCollectionRenewalFutureNumericalPrefix.optionalPrefixCells
      (ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells rate rewards C_star C_h u t
        (ReferenceFirstCollectionRenewalFutureSliceEndpoint.endpointIndex rate rewards C_star C_h u t z) z) = some L)
    (n : ℕ)
    (hnStart : ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceStart rate rewards C_star C_h u t z ≤ n)
    (hnEnd : n ≤ ReferenceFirstCollectionRenewalFutureSliceEndpoint.endpointIndex rate rewards C_star C_h u t z) :
    ReferenceFirstCollectionRenewalFutureNumericalPrefix.optionalPrefixCells (ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells rate rewards C_star C_h u t n z) =
        some (L.take (n - ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceStart rate rewards C_star C_h u t z)) ∧
      (L.take (n - ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceStart rate rewards C_star C_h u t z)).length =
        n - ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceStart rate rewards C_star C_h u t z := by
  let s := ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceStart rate rewards C_star C_h u t z
  let κ := ReferenceFirstCollectionRenewalFutureSliceEndpoint.endpointIndex rate rewards C_star C_h u t z
  have hsourceLength :
      (ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceRecords rate rewards C_star C_h u t z).length = p.T - s := by
    change (ReferenceFirstCollectionRenewalIncomingQueuePrefix.sourceRecords
        rate rewards C_star C_h u t z).length =
      p.T - ReferenceCompletePhysicalHistory.physicalStart
        rate z.val rewards C_star C_h
    rw [← ReferenceFirstCollectionRenewalIncomingQueuePrefix.start_eq_physicalStart
      rate rewards C_star C_h u t z]
    exact ReferenceFirstCollectionRenewalIncomingQueuePrefix.sourceRecords_length
      rate rewards C_star C_h u t z
  have hκT : κ ≤ p.T :=
    (ReferenceFirstCollectionRenewalFutureSliceEndpoint.endpoint_bounds rate rewards C_star C_h u t z).2.2
  have hsourceBound : κ - s ≤
      (ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceRecords rate rewards C_star C_h u t z).length := by
    rw [hsourceLength]
    omega
  have hcalendarLength :
      (ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells rate rewards C_star C_h u t κ z).length = κ - s := by
    change (List.map (ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCell rate)
      ((ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceRecords
        rate rewards C_star C_h u t z).take (κ - s))).length = κ - s
    simp only [List.length_map, List.length_take, Nat.min_eq_left hsourceBound]
  have hmapEndpoint :
      (ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells rate rewards C_star C_h u t κ z).mapM id = some L := by
    exact hendpoint
  have hslotsEndpoint :
      ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells rate rewards C_star C_h u t κ z = L.map some :=
    mapM_id_eq_map_some hmapEndpoint
  have hlength : L.length = κ - s := by
    calc
      L.length = (ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells rate rewards C_star C_h u t κ z).length := by
        rw [hslotsEndpoint]
        simp
      _ = κ - s := hcalendarLength
  have hslotsTake :
      ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells rate rewards C_star C_h u t n z =
        (ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells rate rewards C_star C_h u t κ z).take (n - s) := by
    change List.map (ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCell rate)
        ((ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceRecords rate rewards C_star C_h u t z).take (n - s)) =
      List.take (n - s) (List.map (ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCell rate)
        ((ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceRecords rate rewards C_star C_h u t z).take (κ - s)))
    rw [← List.map_take, List.take_take,
      Nat.min_eq_left (show n - s ≤ κ - s by omega)]
  have htake := mapM_id_take
    (ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells rate rewards C_star C_h u t κ z) L hmapEndpoint (n - s)
  rw [← hslotsTake] at htake
  have htakeLength :
      (L.take (n - s)).length = n - s := by
    rw [List.length_take, Nat.min_eq_left (show n - s ≤ L.length by omega)]
  exact ⟨htake, htakeLength⟩

/-- One actual endpoint word contains every literal optional calendar prefix.
The first-call and current words are the same take of this word; each prefix
retains every original source position, including absent cells before the
endpoint. -/
public theorem renewalCells_endpoint_and_takes (z : Z) :
    ∃ L : List (RecordedQueueRun.RoundInput p.K),
      ReferenceFirstCollectionRenewalFutureNumericalPrefix.optionalPrefixCells
          (ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells rate rewards C_star C_h u t
            (ReferenceFirstCollectionRenewalFutureSliceEndpoint.endpointIndex rate rewards C_star C_h u t z) z) = some L ∧
        L.length = ReferenceFirstCollectionRenewalFutureSliceEndpoint.endpointIndex rate rewards C_star C_h u t z -
          ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceStart rate rewards C_star C_h u t z ∧
        ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentCells rate rewards C_star C_h u t z =
          L.take (t.val + 1 - ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceStart rate rewards C_star C_h u t z) ∧
        ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationCells? rate rewards C_star C_h z.val =
          some (L.take (t.val + 1 - ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceStart rate rewards C_star C_h u t z)) ∧
        ∀ n, ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceStart rate rewards C_star C_h u t z ≤ n →
          n ≤ ReferenceFirstCollectionRenewalFutureSliceEndpoint.endpointIndex rate rewards C_star C_h u t z →
          ReferenceFirstCollectionRenewalFutureNumericalPrefix.optionalPrefixCells (ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells rate rewards C_star C_h u t n z) =
              some (L.take (n - ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceStart rate rewards C_star C_h u t z)) ∧
            (L.take (n - ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceStart rate rewards C_star C_h u t z)).length =
              n - ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceStart rate rewards C_star C_h u t z := by
  let s := ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceStart rate rewards C_star C_h u t z
  let κ := ReferenceFirstCollectionRenewalFutureSliceEndpoint.endpointIndex rate rewards C_star C_h u t z
  have hsCall : s ≤ t.val :=
    ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceStart_le_call rate rewards C_star C_h u t z
  have hbounds := ReferenceFirstCollectionRenewalFutureSliceEndpoint.endpoint_bounds rate rewards C_star C_h u t z
  have hsBoundary : s ≤ t.val + 1 := by omega
  have hboundaryEnd : t.val + 1 ≤ κ := by
    have h := hbounds.1.trans hbounds.2.1
    change t.val + 1 ≤ ReferenceFirstCollectionRenewalFutureSliceEndpoint.endpointIndex
      rate rewards C_star C_h u t z at h
    exact h
  have hstartEnd : s ≤ κ := le_trans hsBoundary hboundaryEnd
  have hpresent :
      (ReferenceFirstCollectionRenewalFutureNumericalPrefix.optionalPrefixReadout rate
        (ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells rate rewards C_star C_h u t κ z)).isSome = true := by
    exact ReferenceFirstCollectionRenewalFutureSliceEndpoint.endpointReadout_present rate rewards C_star C_h u t z
  have hexists : ∃ L : List (RecordedQueueRun.RoundInput p.K),
      ReferenceFirstCollectionRenewalFutureNumericalPrefix.optionalPrefixCells
        (ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells rate rewards C_star C_h u t κ z) = some L := by
    cases hc : ReferenceFirstCollectionRenewalFutureNumericalPrefix.optionalPrefixCells
        (ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells rate rewards C_star C_h u t κ z) with
    | none => simp [ReferenceFirstCollectionRenewalFutureNumericalPrefix.optionalPrefixReadout, hc] at hpresent
    | some L => exact ⟨L, rfl⟩
  obtain ⟨L, hL⟩ := hexists
  have hsourceLength :
      (ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceRecords
        rate rewards C_star C_h u t z).length = p.T - s := by
    change (ReferenceFirstCollectionRenewalIncomingQueuePrefix.sourceRecords
        rate rewards C_star C_h u t z).length =
      p.T - ReferenceCompletePhysicalHistory.physicalStart
        rate z.val rewards C_star C_h
    rw [← ReferenceFirstCollectionRenewalIncomingQueuePrefix.start_eq_physicalStart
      rate rewards C_star C_h u t z]
    exact ReferenceFirstCollectionRenewalIncomingQueuePrefix.sourceRecords_length
      rate rewards C_star C_h u t z
  have hsourceBound : κ - s ≤
      (ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceRecords
        rate rewards C_star C_h u t z).length := by
    rw [hsourceLength]
    omega
  have hcalendarLength :
      (ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells
        rate rewards C_star C_h u t κ z).length = κ - s := by
    change (List.map (ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCell rate)
      ((ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceRecords
        rate rewards C_star C_h u t z).take (κ - s))).length = κ - s
    simp only [List.length_map, List.length_take, Nat.min_eq_left hsourceBound]
  have hslots :
      ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells
        rate rewards C_star C_h u t κ z = L.map some :=
    mapM_id_eq_map_some hL
  have hlength : L.length = κ - s := by
    calc
      L.length = (ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells
          rate rewards C_star C_h u t κ z).length := by
        rw [hslots]
        simp
      _ = κ - s := hcalendarLength
  have hprefixes : ∀ n, s ≤ n → n ≤ κ →
      ReferenceFirstCollectionRenewalFutureNumericalPrefix.optionalPrefixCells (ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells rate rewards C_star C_h u t n z) =
          some (L.take (n - s)) ∧
        (L.take (n - s)).length = n - s := by
    intro n hsn hnκ
    exact endpoint_prefix_take rate rewards C_star C_h u t z L hL n hsn hnκ
  have hcurrentPrefix := (hprefixes (t.val + 1) hsBoundary hboundaryEnd).1
  have hcurrent := ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells_current_mapM rate rewards C_star C_h u t z
  have hcurrentEq : ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentCells rate rewards C_star C_h u t z =
      L.take (t.val + 1 - s) := by
    exact Option.some.inj (hcurrent.symm.trans hcurrentPrefix)
  have hfirst := renewalCells_firstInvocation_eq_current
    rate rewards C_star C_h u t z
  rw [hcurrentEq] at hfirst
  exact ⟨L, hL, hlength, hcurrentEq, hfirst, hprefixes⟩

/-- Each endpoint successor is the original record at its unchanged calendar
offset. Its present cell appends to that same endpoint-word prefix, and the
existing queue run advances by the actual recorded transition. -/
public theorem renewalCells_endpoint_successor
    (z : Z) (q : ℕ)
    (hqStart : ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceStart rate rewards C_star C_h u t z ≤ q)
    (hqEnd : q < ReferenceFirstCollectionRenewalFutureSliceEndpoint.endpointIndex
      rate rewards C_star C_h u t z) :
    ∃ L : List (RecordedQueueRun.RoundInput p.K),
      ∃ r : ReferenceFirstCollectionSamplerCall.RoundRecord p rate,
        ∃ c : RecordedQueueRun.RoundInput p.K,
        ReferenceFirstCollectionRenewalFutureNumericalPrefix.optionalPrefixCells
          (ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells rate rewards C_star C_h u t
            (ReferenceFirstCollectionRenewalFutureSliceEndpoint.endpointIndex rate rewards C_star C_h u t z) z) = some L ∧
        (ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceRecords
          rate rewards C_star C_h u t z)[
            q - ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceStart
              rate rewards C_star C_h u t z]? = some r ∧
        r.input.time.val = q ∧
        ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCell rate r = some c ∧
        ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells rate rewards C_star C_h u t (q + 1) z =
          ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells rate rewards C_star C_h u t q z ++ [some c] ∧
        L[q - ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceStart
          rate rewards C_star C_h u t z]? = some c ∧
        RecordedQueueRun.run Q
            (L.take (q + 1 - ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceStart
              rate rewards C_star C_h u t z)) =
          RecordedQueueRun.step Q
            (RecordedQueueRun.run Q
              (L.take (q - ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceStart
                rate rewards C_star C_h u t z))) c ∧
        ReferenceFirstCollectionRenewalFutureNumericalPrefix.futurePrefixReadout
            rate rewards C_star C_h u t (q + 1) z =
          some (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
            (RecordedQueueRun.step Q
              (RecordedQueueRun.run Q
                (L.take (q - ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceStart
                  rate rewards C_star C_h u t z))) c)) := by
  obtain ⟨L, hendpoint, _, _, _, _⟩ :=
    renewalCells_endpoint_and_takes rate rewards C_star C_h u t z
  let s := ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceStart
    rate rewards C_star C_h u t z
  let κ := ReferenceFirstCollectionRenewalFutureSliceEndpoint.endpointIndex
    rate rewards C_star C_h u t z
  let i := q - s
  have hsourceLength :
      (ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceRecords
        rate rewards C_star C_h u t z).length = p.T - s := by
    change (ReferenceFirstCollectionRenewalIncomingQueuePrefix.sourceRecords
        rate rewards C_star C_h u t z).length =
      p.T - ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h
    rw [← ReferenceFirstCollectionRenewalIncomingQueuePrefix.start_eq_physicalStart
      rate rewards C_star C_h u t z]
    exact ReferenceFirstCollectionRenewalIncomingQueuePrefix.sourceRecords_length
      rate rewards C_star C_h u t z
  have hbounds := ReferenceFirstCollectionRenewalFutureSliceEndpoint.endpoint_bounds
    rate rewards C_star C_h u t z
  have hκT : κ ≤ p.T := hbounds.2.2
  have hi : i <
      (ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceRecords
        rate rewards C_star C_h u t z).length := by
    rw [hsourceLength]
    omega
  have hiκ : i < κ - s := by omega
  have hprefixSucc := endpoint_prefix_take rate rewards C_star C_h u t z L
    hendpoint (q + 1) (by omega) (by omega)
  have hcalendarLength :
      (ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells
        rate rewards C_star C_h u t κ z).length = κ - s := by
    have hsourceBound : κ - s ≤
        (ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceRecords
          rate rewards C_star C_h u t z).length := by
      rw [hsourceLength]
      omega
    change (List.map (ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCell rate)
      ((ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceRecords
        rate rewards C_star C_h u t z).take (κ - s))).length = κ - s
    simp only [List.length_map, List.length_take, Nat.min_eq_left hsourceBound]
  have hslotsEndpoint :
      ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells
        rate rewards C_star C_h u t κ z = L.map some :=
    mapM_id_eq_map_some hendpoint
  have hlength : L.length = κ - s := by
    calc
      L.length = (ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells
          rate rewards C_star C_h u t κ z).length := by
        rw [hslotsEndpoint]
        simp
      _ = κ - s := hcalendarLength
  have hiL : i < L.length := by omega
  let r := (ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceRecords
    rate rewards C_star C_h u t z).get ⟨i, hi⟩
  have hr : (ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceRecords
      rate rewards C_star C_h u t z)[i]? = some r :=
    List.getElem?_eq_getElem hi
  have hrdate : r.input.time.val = q := by
    obtain ⟨_, _, hactual⟩ :=
      ReferenceLaterLiveNumericalReadout.source_record_prefix
        rate rewards C_star C_h z.val ⟨i, hi⟩
    change r = _ at hactual
    rw [hactual]
    change ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h +
      (q - s) = q
    have hstartQ : ReferenceCompletePhysicalHistory.physicalStart
        rate z.val rewards C_star C_h ≤ q := by
      change s ≤ q at hqStart
      exact hqStart
    have hsEq : s = ReferenceCompletePhysicalHistory.physicalStart
        rate z.val rewards C_star C_h := rfl
    rw [hsEq]
    omega
  have hcellAt :
      (ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells
        rate rewards C_star C_h u t κ z)[i]? =
        some (ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCell rate r) := by
    change (List.map (ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCell rate)
      ((ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceRecords
        rate rewards C_star C_h u t z).take (κ - s)))[i]? =
        some (ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCell rate r)
    rw [List.getElem?_map, List.getElem?_take_of_lt hiκ, hr]
    rfl
  have hcellPoint :
      some (L.get ⟨i, hiL⟩) =
        ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCell rate r := by
    rw [hslotsEndpoint, List.getElem?_map, List.getElem?_eq_getElem hiL] at hcellAt
    simp only [Option.map_some] at hcellAt
    exact Option.some.inj hcellAt
  let c := L.get ⟨i, hiL⟩
  have hcalendarCell :
      ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCell rate r = some c := by
    simpa only [c] using hcellPoint.symm
  have hrvalue : (ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceRecords
      rate rewards C_star C_h u t z)[i] = r := by
    have h := hr
    rw [List.getElem?_eq_getElem hi] at h
    exact Option.some.inj h
  have htakeSource :
      (ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceRecords
        rate rewards C_star C_h u t z).take (i + 1) =
        (ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceRecords
          rate rewards C_star C_h u t z).take i ++ [r] := by
    rw [List.take_succ_eq_append_getElem hi, hrvalue]
  have hdateSub : q + 1 - s = i + 1 := by
    dsimp [i]
    omega
  have happend :
      ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells
          rate rewards C_star C_h u t (q + 1) z =
        ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells
          rate rewards C_star C_h u t q z ++ [some c] := by
    change List.map (ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCell rate)
        ((ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceRecords
          rate rewards C_star C_h u t z).take (q + 1 - s)) =
      List.map (ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCell rate)
          ((ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceRecords
            rate rewards C_star C_h u t z).take (q - s)) ++ [some c]
    rw [hdateSub, htakeSource]
    simp only [List.map_append, List.map_cons, List.map_nil, hcalendarCell, i]
  have hLcell : L[q - s]? = some c := by
    change L[i]? = some c
    rw [List.getElem?_eq_getElem hiL]
    rfl
  have htakeL : L.take (i + 1) = L.take i ++ [c] := by
    rw [List.take_succ_eq_append_getElem hiL]
    rfl
  have hrun : RecordedQueueRun.run Q (L.take (i + 1)) =
      RecordedQueueRun.step Q (RecordedQueueRun.run Q (L.take i)) c := by
    rw [htakeL]
    exact ReferenceFirstCollectionRenewalFutureNumericalPrefix.run_append_one
      rate (L.take i) c
  have hreadout :
      ReferenceFirstCollectionRenewalFutureNumericalPrefix.futurePrefixReadout
          rate rewards C_star C_h u t (q + 1) z =
        some (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
          (RecordedQueueRun.run Q (L.take (i + 1)))) := by
    change ReferenceFirstCollectionRenewalFutureNumericalPrefix.optionalPrefixReadout rate
      (ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells
        rate rewards C_star C_h u t (q + 1) z) = _
    rw [ReferenceFirstCollectionRenewalFutureNumericalPrefix.optionalPrefixReadout,
      hprefixSucc.1, hdateSub]
    rfl
  refine ⟨L, r, c, hendpoint, hr, hrdate, hcalendarCell, happend, hLcell, ?_, ?_⟩
  · change RecordedQueueRun.run Q (L.take (q + 1 - s)) =
      RecordedQueueRun.step Q (RecordedQueueRun.run Q (L.take (q - s))) c
    rw [hdateSub]
    exact hrun
  · rw [hreadout, hrun]

end Bandits.Support.ReferenceFirstCollectionRenewalRawPrefixJoin
