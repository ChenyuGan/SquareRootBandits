/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCorrectedNextCalendarWordJoin
public import Bandits.Support.ReferenceFirstCorrectedNextAssignedCalendarReplay

import Mathlib.Tactic

/-!
# Complete accepted-UP assigned calendar word alignment

This internal conditional result keeps the actual accepted-UP witnesses and
aligns their assigned-arm word with literal slots in the original calendar.
The score and queue equations remain explicit local
induction inputs; they are not a source theorem or a history package.

Sources: ZIP4 appendix_a_local_protocol.tex:28-64,
06_interruptions.tex:40-100,192-233,246-299, and
04_slow_fast_learner.tex:157-174.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions ReferenceActivePhysicalStep ReferenceActivePhysicalHorizon
open CoordinatorPhaseClock CoordinatorRoundDispatch CoordinatorAssignmentRegisterInstall
open LaterAssignmentStartOperation CanonicalFastSampling RecordedQueueRun
open ReferenceCollectionSegmentExtraction ReferenceLaterCollectionArrivalReadout
open ReferenceCollectionRawBufferHistory

namespace Bandits.Support.ReferenceCompleteAssignedCalendarWordAlignment

variable {p : ConstructorDimensions.Parameters}

private theorem mapM_id_length_eq {α : Type*} (slots : List (Option α))
    (cells : List α) (h : List.mapM id slots = some cells) :
    cells.length = slots.length := by
  induction slots generalizing cells with
  | nil =>
      rw [List.mapM_nil] at h
      cases h
      rfl
  | cons head tail ih =>
      cases head with
      | none => simp [List.mapM_cons] at h
      | some value =>
          cases htail : List.mapM id tail with
          | none => simp [List.mapM_cons, htail] at h
          | some rest =>
              simp only [List.mapM_cons, htail] at h
              cases h
              simp only [List.length_cons, ih rest htail]

private theorem prefixInputs_append_slots
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (n : ℕ) (prior cells : List (RecordedQueueRun.RoundInput p.K))
    (hprefix : ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
      rate rewards C_star C_h
        (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + n)
        z = some prior)
    (hslots : ∀ x : Fin cells.length,
      let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h
      ∃ r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate),
        R[n + x.val]? = some r ∧
        ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r = some cells[x.val]) :
    ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
      rate rewards C_star C_h
        (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h +
        (n + cells.length)) z = some (prior ++ cells) := by
  induction cells generalizing n prior with
  | nil => simpa using hprefix
  | cons c cs ih =>
      have hslot0 := hslots ⟨0, by simp⟩
      rcases hslot0 with ⟨r, hr, hc⟩
      have hr' : (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)[(ReferenceCompletePhysicalHistory.physicalStart
            rate z rewards C_star C_h + n) -
            ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h]? = some r := by
        simpa only [Nat.add_sub_cancel_left, Nat.add_zero] using hr
      have hone := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs_append_one
        rate rewards C_star C_h
          (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + n)
          z prior hprefix r c hr' hc
      have htail : ∀ x : Fin cs.length,
          let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate z rewards C_star C_h
          ∃ r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate),
            R[(n + 1) + x.val]? = some r ∧
            ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r = some cs[x.val] := by
        intro x
        have hslot := hslots ⟨x.val + 1, by simpa only [List.length_cons] using Nat.succ_lt_succ x.isLt⟩
        dsimp only at hslot
        obtain ⟨r, hr, hc⟩ := hslot
        refine ⟨r, ?_, ?_⟩
        · simpa only [show n + (x.val + 1) = (n + 1) + x.val by omega] using hr
        · simpa only [List.getElem_cons_succ] using hc
      have hrec := ih (n + 1) (prior ++ [c]) hone htail
      have htime :
          ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h +
              (n + (c :: cs).length) =
            ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h +
              (n + 1 + cs.length) := by simp only [List.length_cons]; omega
      rw [htime]
      simpa only [List.append_assoc, List.cons_append, List.nil_append] using hrec

private theorem complete_record_time
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length) :
    ((ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[b.val]'b.isLt).input.time.val =
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + b.val := by
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  have htimes := ReferenceCompletePhysicalHistory.completeSuffixRecords_time_values
    rate z rewards C_star C_h
  have hget := congrArg (fun xs : List ℕ => xs[b.val]?) htimes
  have hRget : R[b.val]? = some (R[b.val]'b.isLt) :=
    List.getElem?_eq_some_iff.mpr ⟨b.isLt, rfl⟩
  have hleft : (R.map fun r => r.input.time.val)[b.val]? =
      some (R[b.val]'b.isLt).input.time.val := by
    rw [List.getElem?_map, hRget]
    rfl
  have hlen := congrArg List.length htimes
  have hRangeLen : (ReferenceActivePhysicalHorizon.calendar s (p.T - s)).length = R.length := by
    simpa only [List.length_map] using hlen.symm
  have hbRange : b.val < (ReferenceActivePhysicalHorizon.calendar s (p.T - s)).length := by
    rw [hRangeLen]
    exact b.isLt
  have hright : (ReferenceActivePhysicalHorizon.calendar s (p.T - s))[b.val]? =
      some (s + b.val) := by
    apply List.getElem?_eq_some_iff.mpr
    refine ⟨hbRange, ?_⟩
    exact List.getElem_range'_1 b.val hbRange
  rw [hleft, hright] at hget
  exact Option.some.inj hget

private theorem prefixInputs_length_at_index
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (P0 : List (RecordedQueueRun.RoundInput p.K))
    (hP0 : ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
      rate rewards C_star C_h
        (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + b.val)
        z = some P0) : P0.length = b.val := by
  classical
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  have hlaunch := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs_launch
    rate rewards C_star C_h (s + b.val) z P0 hP0
  have hslots : ((R.take b.val).map
      (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate)).mapM id = some P0 := by
    change (if ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
        rate rewards C_star C_h (s + b.val) z then
      ((((ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).take
        ((s + b.val) - ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart
          rate rewards C_star C_h z)).map
          (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate)).mapM id)
      else none) = some P0 at hP0
    rw [ite_eq_left hlaunch] at hP0
    simpa only [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart,
      ReferenceCompletePhysicalHistory.physicalStart, s, Nat.add_sub_cancel_left] using hP0
  have hlength := mapM_id_length_eq _ _ hslots
  have ht : (R.take b.val).length = b.val := by
    rw [List.length_take]
    exact Nat.min_eq_left (Nat.le_of_lt b.isLt)
  simpa only [List.length_map, ht] using hlength

private theorem segment_cells_original_slots
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (R : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (e : ℕ) (seg : ReferenceCollectionSegmentExtraction.Segment rate)
    (hseg : ReferenceCollectionSegmentExtraction.segmentAt R e = some seg)
    (Dword : List (RecordedQueueRun.RoundInput p.K))
    (hDlen : Dword.length = seg.records.length)
    (hslots : ∀ x : Fin seg.records.length,
      ReferenceFirstCollectionCurrentRetainedGate.cell0 rate seg.records[x.val] =
        some (Dword[x.val]'(Nat.lt_of_lt_of_eq x.isLt hDlen.symm))) :
    ∀ x : Fin Dword.length, ∃ r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate),
      R[e + x.val]? = some r ∧
      ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r = some Dword[x.val] := by
  have hpartition := ReferenceCollectionSegmentExtraction.segmentAt_partition R e seg hseg
  intro x
  have hxseg : x.val < seg.records.length := by rw [← hDlen]; exact x.isLt
  have hrecord : (R.drop e)[x.val]? = some seg.records[x.val] := by
    rw [← hpartition, List.getElem?_append_left hxseg]
    exact List.getElem?_eq_some_iff.mpr ⟨hxseg, rfl⟩
  refine ⟨seg.records[x.val], ?_, hslots ⟨x.val, hxseg⟩⟩
  simpa only [List.getElem?_drop] using hrecord

private theorem split_of_positive_length (b e length : ℕ)
    (hlen : length = e - b) (hpos : 0 < length) : b + length = e := by omega

private theorem native_cell_eq_of_gate
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (selected : Selection r.input)
    (ho : ReferenceLaterLiveNumericalReadout.preparedOrdinary r)
    (hselection : r.output.preparation.coordinator.selection = some selected)
    (hpositive : 0 < selected.view.payload.sigma.val)
    (hlive : CoordinatorLocalArmChoice.assignmentIsLive selected.view.payload
      selected.view.cutoff r.input.time)
    (cell : RecordedQueueRun.RoundInput p.K)
    (hgate : ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r = some cell) :
    ReferenceFirstWindowNumericalStream.sourceCell r selected.view.payload
      selected.view.pendingAtChoice
      (ReferenceLaterLiveNumericalReadout.preparedStates r ho)
      selected.view.complementWeights selected.view.cutoff
      (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected) = cell := by
  classical
  have hread : ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r =
      some (ReferenceFirstWindowNumericalStream.sourceCell r selected.view.payload
        selected.view.pendingAtChoice
        (ReferenceLaterLiveNumericalReadout.preparedStates r ho)
        selected.view.complementWeights selected.view.cutoff
        (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected)) := by
    simp only [ReferenceLaterLiveNumericalReadout.laterLiveReadout, hselection,
      hpositive, hlive, ho, and_self, dite_true, ite_true]
  change (ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r).or _ = some cell at hgate
  rw [hread] at hgate
  exact Option.some.inj hgate

private theorem native_word_eq_of_slots
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (R : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (b N : ℕ) (C : List (RecordedQueueRun.RoundInput p.K)) (a : Fin p.K)
    (hlen : N = C.length)
    (hslots : ∀ x : Fin C.length,
      ∃ r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate),
        R[b + x.val]? = some r ∧
        ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r = some C[x.val]) :
    let L := (R.drop b).take N
    ∀ (hLlen : L.length = N)
      (v : ∀ x : Fin N, Selection (L[x.val]'(Nat.lt_of_lt_of_eq x.isLt hLlen.symm)).input)
      (ho : ∀ x : Fin N, ReferenceLaterLiveNumericalReadout.preparedOrdinary
        (L[x.val]'(Nat.lt_of_lt_of_eq x.isLt hLlen.symm))),
      (∀ x, (L[x.val]'(Nat.lt_of_lt_of_eq x.isLt hLlen.symm)).output.preparation.coordinator.selection =
        some (v x)) →
      (∀ x, 0 < (v x).view.payload.sigma.val) →
      (∀ x, CoordinatorLocalArmChoice.assignmentIsLive (v x).view.payload
        (v x).view.cutoff (L[x.val]'(Nat.lt_of_lt_of_eq x.isLt hLlen.symm)).input.time) →
      let Cells : Fin N → RecordedQueueRun.RoundInput p.K := fun x =>
        ReferenceFirstWindowNumericalStream.sourceCell
          (L[x.val]'(Nat.lt_of_lt_of_eq x.isLt hLlen.symm)) (v x).view.payload
          (v x).view.pendingAtChoice
          (ReferenceLaterLiveNumericalReadout.preparedStates
            (L[x.val]'(Nat.lt_of_lt_of_eq x.isLt hLlen.symm)) (ho x))
          (v x).view.complementWeights (v x).view.cutoff
          (ReferenceLaterLiveNumericalReadout.selection_choiceValid (v x))
      List.ofFn (fun x : Fin N => ((Cells x).enabled,
        RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate)
          (Cells x) a)) = ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar rate a C := by
  intro L hLlen v ho hselected hpositive hlive Cells
  apply List.ext_getElem
  · simp only [List.length_ofFn, ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar,
      List.length_map, hlen]
  · intro x hx hx'
    have hxN : x < N := by simpa only [List.length_ofFn] using hx
    have hxC : x < C.length := by simpa only [hlen] using hxN
    have hxL : x < L.length := Nat.lt_of_lt_of_eq hxN hLlen.symm
    obtain ⟨r, hr, hgate⟩ := hslots ⟨x, hxC⟩
    have hrecord : L[x]'hxL = r := by
      have hdrop : (R.drop b)[x]? = some r := by
        simpa only [List.getElem?_drop] using hr
      have ht : L[x]? = some r := by
        simpa only [L, List.getElem?_take, ite_eq_left hxN] using hdrop
      exact (List.getElem?_eq_some_iff.mp ht).2
    have hgate' : ReferenceFirstCollectionCurrentRetainedGate.cell0 rate (L[x]'hxL) =
        some (C[x]'hxC) := by rw [hrecord]; exact hgate
    have hwhole : Cells ⟨x, hxN⟩ = C[x]'hxC :=
      native_cell_eq_of_gate rate (L[x]'hxL) (v ⟨x, hxN⟩) (ho ⟨x, hxN⟩)
        (hselected ⟨x, hxN⟩) (hpositive ⟨x, hxN⟩) (hlive ⟨x, hxN⟩) (C[x]'hxC) hgate'
    simp only [List.getElem_ofFn, ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar,
      List.getElem_map]
    rw [hwhole]

private theorem collection_word_eq_of_slots
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (seg : ReferenceCollectionSegmentExtraction.Segment rate)
    (Dword : List (RecordedQueueRun.RoundInput p.K)) (a : Fin p.K)
    (hDlen : Dword.length = seg.records.length)
    (hslots : ∀ x : Fin seg.records.length,
      let cell := Dword[x.val]'(Nat.lt_of_lt_of_eq x.isLt hDlen.symm)
      ReferenceCollectionRawBufferHistory.physicalQueueRecord seg.context.preLedger a
        seg.records[x.val] = (cell.enabled, RecordedQueueRun.quantizedArrival
          (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell a)) :
    ∀ count, (seg.records.take count).map
      (ReferenceCollectionRawBufferHistory.physicalQueueRecord seg.context.preLedger a) =
      ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar rate a (Dword.take count) := by
  have hmap : seg.records.map
      (ReferenceCollectionRawBufferHistory.physicalQueueRecord seg.context.preLedger a) =
      ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar rate a Dword := by
    apply List.ext_getElem
    · simp only [List.length_map, ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar, hDlen]
    · intro x hx hx'
      simpa only [List.getElem_map, ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar]
        using hslots ⟨x, by simpa only [List.length_map] using hx⟩
  intro count
  rw [List.map_take, hmap]
  simp only [ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar, List.map_take]

private theorem offset_of_time (s e u : ℕ) (hu : u = s + e + 1) :
    u - (s + 1) = e := by omega

private theorem window_length_of_times (s e b : ℕ) :
    (s + e + 1) - (s + b + 1) = e - b := by omega

private theorem take_calendar_cut {α : Type*} (P C D : List α) :
    (P ++ C ++ D).take (P.length + C.length) = P ++ C := by
  rw [← List.length_append, List.take_append_length]

private theorem take_calendar_prev {α : Type*} (P C D : List α)
    (hpos : 0 < C.length) :
    (P ++ C ++ D).take (P.length + C.length - 1) = P ++ C.take (C.length - 1) := by
  have hindex : P.length + C.length - 1 = P.length + (C.length - 1) := by omega
  rw [hindex, List.append_assoc, List.take_length_add_append,
    List.take_append_of_le_length (Nat.sub_le _ _)]

private theorem take_calendar_continuation {α : Type*} (P C D : List α) (j : ℕ) :
    (P ++ C ++ D).take (P.length + C.length + j) = P ++ C ++ D.take j := by
  rw [← List.length_append, List.take_length_add_append]

private theorem calendar_replay_word_alignment
    (rate : ReferenceActivePhysicalStep.RateInput p) (a : Fin p.K)
    (P C D : List (RecordedQueueRun.RoundInput p.K)) (e N : ℕ)
    (A : List (Bool × ℕ)) (H : ℕ → List (Bool × ℕ))
    (he : P.length + C.length = e) (hN : N = C.length) (hpos : 0 < C.length)
    (hA : A = ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar rate a C)
    (hH : ∀ j, H j = ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar rate a (D.take j)) :
    QueueReplay.replay (4 * rate.n) (0, 0)
        (ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar rate a P ++ A) =
      ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate (P ++ C ++ D) a e ∧
    QueueReplay.replay (4 * rate.n) (0, 0)
        (ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar rate a P ++ A.take (N - 1)) =
      ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate (P ++ C ++ D) a (e - 1) ∧
    ∀ j, QueueReplay.replay (4 * rate.n) (0, 0)
        (ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar rate a P ++ (A ++ H j)) =
      ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate (P ++ C ++ D) a (e + j) := by
  subst e
  subst N
  refine ⟨?_, ?_, ?_⟩
  · rw [hA, ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay,
      take_calendar_cut]
    simp only [ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar, List.map_append]
  · rw [hA, ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay,
      take_calendar_prev P C D hpos]
    simp only [ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar, List.map_append,
      List.map_take]
  · intro j
    rw [hA, hH j, ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay,
      take_calendar_continuation]
    simp only [ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar, List.map_append,
      List.append_assoc]

local notation "Record" => ReferenceActivePhysicalHorizon.RoundRecord (p := p)
local notation "Cell" => RecordedQueueRun.RoundInput p.K

/-- The accepted-UP output, with its source-calendar word alignment on the same
birth, payload, recovery, initializer, and segment witnesses. -/
theorem complete_accepted_up_literal_calendar_replay
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (k b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (i : Fin (p.m - 1)) (reply : ReferenceCollectionPhaseHistory.UpRecord p rate)
    (hacc : ReferenceCollectionPhaseHistory.AcceptedUp
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[k.val].input i reply)
    (P : AssignmentStartPayload.Input p rate.eta)
    (base : Fin (p.m - 1) → ℕ)
    (hbirth : ReferenceAssignmentPayloadPersistence.InstallationBirth
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[b.val] P)
    (hbase : (match ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[b.val]'b.isLt).output.preparation.coordinator with
      | .first (.chosen installation _) => some installation.followerBaseScore
      | .collection _ _ _ _ (.laterChosen _ _ _ _ _ _ _ _ _ installation _) =>
          some installation.retainedBaseScore
      | _ => none) = some base)
    (hselector : reply.val.sigma = P.sigma.val + 1)
    (hlater : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h <
      P.sigma.val)
    (P0 C Dword : List Cell) (e : ℕ)
    (seg : ReferenceCollectionSegmentExtraction.Segment rate)
    (hP0 : ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
      rate rewards C_star C_h
        (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + b.val)
        z = some P0)
    (hscan : FollowerCutoffScan.firstCutoff p rate.eta.val P.sigma
      (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
        (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z))) =
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + e + 1)
    (hseg : ReferenceCollectionSegmentExtraction.segmentAt
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h) e =
        some seg)
    (hClen : C.length = e - b.val)
    (hDlen : Dword.length = seg.records.length)
    (hCslot : ∀ x : Fin C.length,
      let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h
      ∃ r : Record, R[b.val + x.val]? = some r ∧
        ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r = some C[x.val])
    (hDslot : ∀ x : Fin seg.records.length,
      let c := Dword[x.val]'(Nat.lt_of_lt_of_eq x.isLt hDlen.symm)
      ReferenceFirstCollectionCurrentRetainedGate.cell0 rate seg.records[x.val] = some c ∧
      ReferenceCollectionRawBufferHistory.physicalQueueRecord seg.context.preLedger
        (P.assignment.assigned i) seg.records[x.val] =
        (c.enabled, RecordedQueueRun.quantizedArrival
          (ReferenceFirstLaunchNumericalCell.queueParameters rate) c
          (P.assignment.assigned i)))
    (hqueue : (P.downRecord i).val.q =
      (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate P0
        (P.assignment.assigned i) P0.length).2)
    (hscore : base i =
      (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate P0
        (P.assignment.assigned i) P0.length).1) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    ∃ (c : ReferenceCollectionSegmentExtraction.Choice rate)
      (bN j : Fin R.length)
      (logged after : ReferencePrelaunchFollower.State p rate.eta)
      (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
      (raw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)))
      (scan : FollowerCutoffScan.ScanResult p.T)
      (registers : ℕ × ℕ) (lastService : ℕ),
      ReferenceCollectionSegmentExtraction.choice (R[k.val]'k.isLt).input = some c ∧
      bN.val ≤ j.val ∧ j.val < k.val ∧
      ReferenceAssignmentPayloadPersistence.InstallationBirth
        (R[bN.val]'bN.isLt) c.payload ∧
      ReferenceAcceptedUpFollowerHistory.RetainedDown R[j.val] i (c.payload.downRecord i) ∧
      (R[j.val].output.followers i).downInput = some logged ∧
      (R[j.val].output.followers i).down = some cut ∧
      cut.outcome = .accepted logged after raw (c.payload.downRecord i) scan registers lastService ∧
      let Pn := c.payload
      let M := Pn.downRecord i
      let a := Pn.assignment.assigned i
      let sigma := Pn.sigma.val + 1
      let cap := 4 * rate.n
      let bits := FollowerCutoffScan.completeRowProposalBit p rate.eta.val
        (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z))
      let u := FollowerCutoffScan.firstCutoff p rate.eta.val Pn.sigma bits
      let ell := min u (R[j.val].input.time.val + 2)
      let N := u - sigma
      let d := ell - sigma
      let o := u - (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + 1)
      let n := k.val - o
      let L := (R.drop bN.val).take N
      let qp := ReferenceFirstLaunchNumericalCell.queueParameters rate
      ell = scan.endpoint ∧
      ActiveFollowerDownAcceptance.checkedRecovery p rate M logged ell =
        .ok ⟨registers, lastService⟩ ∧
      M.val.q = Pn.queues a ∧ reply.val.sigma = sigma ∧ 0 < d ∧ d ≤ N ∧
      L.map (fun r : Record => r.input.time.val + 1) = List.range' sigma N ∧
      ∃ (hLlen : L.length = N)
        (v : ∀ x : Fin N, Selection (L[x.val]'(Nat.lt_of_lt_of_eq x.isLt hLlen.symm)).input)
        (ho : ∀ x : Fin N, ReferenceLaterLiveNumericalReadout.preparedOrdinary
          (L[x.val]'(Nat.lt_of_lt_of_eq x.isLt hLlen.symm))),
        (∀ x, (L[x.val]'(Nat.lt_of_lt_of_eq x.isLt hLlen.symm)).output.preparation.coordinator.selection =
            some (v x) ∧ (v x).view.payload = Pn ∧ (v x).view.cutoff = none ∧
          CoordinatorLocalArmChoice.assignmentIsLive (v x).view.payload
            (v x).view.cutoff (L[x.val]'(Nat.lt_of_lt_of_eq x.isLt hLlen.symm)).input.time) ∧
        (∀ x f, (ReferenceFollowerFixedReply.actualChoice
          (L[x.val]'(Nat.lt_of_lt_of_eq x.isLt hLlen.symm)) f).configuration =
            .ordinary
              (ReferenceLaterLiveNumericalReadout.preparedStates
                (L[x.val]'(Nat.lt_of_lt_of_eq x.isLt hLlen.symm)) (ho x) f)
              (ReferenceLaterLiveNumericalReadout.preparedMemories
                (L[x.val]'(Nat.lt_of_lt_of_eq x.isLt hLlen.symm)) (ho x) f)) ∧
        let Cells : Fin N → Cell := fun x =>
          ReferenceFirstWindowNumericalStream.sourceCell
            (L[x.val]'(Nat.lt_of_lt_of_eq x.isLt hLlen.symm)) (v x).view.payload
            (v x).view.pendingAtChoice
            (ReferenceLaterLiveNumericalReadout.preparedStates
              (L[x.val]'(Nat.lt_of_lt_of_eq x.isLt hLlen.symm)) (ho x))
            (v x).view.complementWeights (v x).view.cutoff
            (ReferenceLaterLiveNumericalReadout.selection_choiceValid (v x))
        let A := List.ofFn (fun x : Fin N =>
          ((Cells x).enabled, RecordedQueueRun.quantizedArrival qp (Cells x) a))
        let V := fun count => QueueReplay.replay cap (0, M.val.q) (A.take count)
        let Ed := ((R.drop bN.val).take d).map
          (fun r => (true, ReferenceFollowerSparseEmissionRecovery.emissionContribution M i r))
        let Q := ActiveFollowerDownAcceptance.recoveryQueueRecords p rate M logged ell
        Q = Ed ∧ Ed = A.take d ∧ A.length = N ∧
        (∀ x ∈ A, x.1 = true) ∧ registers = V d ∧
        lastService = (V d).1 - (V (d - 1)).1 ∧
        ∃ (segN : ReferenceCollectionSegmentExtraction.Segment rate)
          (done : ReferenceCollectionSegmentExtraction.CompletedRound rate)
          (c0 : ReferenceCollectionSegmentExtraction.Choice rate)
          (I : ReferenceCollectionSegmentExtraction.Initializer p),
          o ≤ k.val ∧ o < R.length ∧ n < segN.records.length ∧
          ReferenceCollectionSegmentExtraction.segmentAt R o = some segN ∧
          (∀ ho : o < R.length, segN.entry = R[o]'ho) ∧
          segN.context = c0 ∧ c0.payload = Pn ∧ c0.initializer = some I ∧
          ReferenceCollectionSegmentExtraction.choice segN.entry.input = some c0 ∧
          I.checkedStart rate = .success segN.context.preLedger ∧
          I.assignment.arm = Pn.assignment.assigned ∧ I.sigma = sigma ∧ I.cutoff = u ∧
          I.base = c.preLedger.baseScore ∧
          (match (R[bN.val]'bN.isLt).output.preparation.coordinator with
          | .first (.chosen installed _) => c.preLedger.baseScore = installed.followerBaseScore
          | .collection _ _ _ _ (.laterChosen _ _ _ _ _ _ _ _ _ installed _) =>
              c.preLedger.baseScore = installed.retainedBaseScore
          | _ => False) ∧
          (∀ hn : n < segN.records.length, segN.records[n]'hn = R[k.val]'k.isLt) ∧
          ReferenceCollectionSegmentExtraction.extractRound (R[k.val]'k.isLt) = some done ∧
          done.context = c ∧ done.accepted = true ∧ done.input.parsed = some reply ∧
          done.input.selectedFollower = i ∧
          let H := fun count => (segN.records.take count).map
            (ReferenceCollectionRawBufferHistory.physicalQueueRecord segN.context.preLedger a)
          let Ledge := fun count => ReferenceCollectionSegmentExtraction.endpointLedger
            segN.context.preLedger (segN.records.take count)
          done.final = Ledge (n + 1) ∧
          ∃ (recording : CoordinatorRecordingOperation.Output p)
            (started decoded : ReferenceActivePhysicalStep.Ledger rate)
            (bank : CoordinatorUpReception.UpDecoderBank p),
            (R[k.val]'k.isLt).output.coordinator.recording = some recording ∧
            CoordinatorCollectionLedger.startRound done.context.preLedger
              ((R[k.val]'k.isLt).input.time.val + 1)
              (ReferenceActivePhysicalStep.collectionEnabled done.context.preLedger
                (R[k.val]'k.isLt).input.time)
              (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) =
                .success started ∧
            (ReferenceActivePhysicalStep.receiveUp
              (ReferenceActivePhysicalStep.prepare (R[k.val]'k.isLt).input) started).result =
                .success (decoded, bank) ∧
            CoordinatorCollectionLedger.decodeUp started i (some reply) = .success decoded ∧
            CoordinatorCollectionLedger.finishRound decoded = .success done.final ∧
            started.assignment = I.assignment ∧ started.currentRegisters a = none ∧
            started.gammaLoc a = 0 ∧ decoded.gammaLoc a = 0 ∧
            done.final.increment a = decoded.increment a ∧
            (∃ saved, (R[k.val]'k.isLt).output.next.coordinator =
              .collection Pn done.final saved) ∧
          (∀ E : List (Bool × ℕ),
            M.val.q = (QueueReplay.replay cap (0, 0) E).2 →
            I.base i = (QueueReplay.replay cap (0, 0) E).1 →
            let Full := fun count => QueueReplay.replay cap (0, 0) (E ++ (A ++ H count))
            let Cut := QueueReplay.replay cap (0, 0) (E ++ A)
            let Prev := QueueReplay.replay cap (0, 0) (E ++ A.take (N - 1))
            (I.base i + registers.1, registers.2) =
              QueueReplay.replay cap (0, 0) (E ++ A.take d) ∧
            lastService =
              (QueueReplay.replay cap (0, 0) (E ++ A.take d)).1 -
                (QueueReplay.replay cap (0, 0) (E ++ A.take (d - 1))).1 ∧
            H (n + 1) = H n ++
              [ReferenceCollectionRawBufferHistory.physicalQueueRecord
                segN.context.preLedger a (R[k.val]'k.isLt)] ∧
            Cut = (I.base i + reply.val.S, reply.val.q) ∧
            reply.val.delta = Cut.1 - Prev.1 ∧
            ∀ count, n + 1 ≤ count → count ≤ segN.records.length →
              ∃ suffixAccepted,
                CollectionCheckedExecution.checkedRounds done.final
                  ((segN.inputs.drop (n + 1)).take (count - (n + 1))) =
                    some (suffixAccepted, Ledge count) ∧
                (segN.records.take count).map
                  (fun r : Record => r.input.time.val + 1) = List.range' u count ∧
                (Ledge count).cutoffRegisters a = some ⟨Cut.1, Cut.2, Cut.1 - Prev.1⟩ ∧
                (Ledge count).currentRegisters a =
                  some ⟨(Full count).2, (Full count).1 - (Full (count - 1)).1⟩ ∧
                (Ledge count).increment a = (Full count).1 - Cut.1 ∧
                Cut.1 + (Ledge count).increment a = (Full count).1 ∧
                (Ledge count).assignment = I.assignment ∧
                (Ledge count).sigma = sigma ∧ (Ledge count).cutoff = u ∧
                (Ledge count).freezeAt = I.freezeAt) ∧
          bN = b ∧ c.payload = P ∧ o = e ∧ segN = seg ∧ N = e - b.val ∧
          A = ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar rate a C ∧
          (∀ count, H count = ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar
            rate a (Dword.take count)) ∧
          let G := P0 ++ C ++ Dword
          let q := e + seg.records.length
          G.length = q ∧
          ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
            rate rewards C_star C_h
            (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + q) z =
              some G ∧
          Ledge seg.records.length = seg.final ∧
          ∀ count, n + 1 ≤ count → count ≤ seg.records.length →
            (Ledge count).cutoffRegisters a = some ⟨
              (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate G a e).1,
              (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate G a e).2,
              (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate G a e).1 -
                (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate G a (e - 1)).1⟩ ∧
            (Ledge count).currentRegisters a = some ⟨
              (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate G a (e + count)).2,
              (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate G a (e + count)).1 -
                (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate G a
                  (e + count - 1)).1⟩ ∧
            (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate G a e).1 +
              (Ledge count).increment a =
                (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate G a
                  (e + count)).1 := by
  classical
  intro R
  obtain ⟨c, bN, j, logged, after, cut, raw, scan, registers, lastService,
    hc, hbj, hjk, hbirthN, hretained, hlogged, hdown, houtcome,
    hscanN, hchecked, hqN, hUsigma, hdpos, hdle, htimes, hLlen, v, ho,
    hselected, hprepared, hQ, hEd, hAlen, hAenabled, hregisters, hlastService,
    segN, done, c0, I, hok, hoR, hn, hsegmentN, hentry, hsegContext,
    hentryChoice, hc0, hI, hIchecked, hIarm, hIsigma, hIcutoff, hIbase,
    hbaseProv, hrecord, hdone, hcontext, haccepted, hparsed, hsender, hfinal,
    recording, started, decoded, bank, hrecording, hstart, hreceive, hdecode,
    hfinish, hassignment, hstartedNone, hgammaStarted, hgammaDecoded,
    hfinishIncrement, hnext, hcontinuation⟩ :=
    ReferenceCorrectedSuccessorAssignedNumericalStep.internal_complete_accepted_up_original_prefix_replay_of_initial_replay
      rewards C_star C_h z k i reply hacc
  let Pn := c.payload
  let M := Pn.downRecord i
  let a := Pn.assignment.assigned i
  let sigma := Pn.sigma.val + 1
  let cap := 4 * rate.n
  let bits := FollowerCutoffScan.completeRowProposalBit p rate.eta.val
    (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z))
  let u := FollowerCutoffScan.firstCutoff p rate.eta.val Pn.sigma bits
  let ell := min u (R[j.val].input.time.val + 2)
  let N := u - sigma
  let d := ell - sigma
  let L := (R.drop bN.val).take N
  let qp := ReferenceFirstLaunchNumericalCell.queueParameters rate
  let Cells : Fin N → Cell := fun x =>
    ReferenceFirstWindowNumericalStream.sourceCell
      (L[x.val]'(Nat.lt_of_lt_of_eq x.isLt hLlen.symm)) (v x).view.payload
      (v x).view.pendingAtChoice
      (ReferenceLaterLiveNumericalReadout.preparedStates
        (L[x.val]'(Nat.lt_of_lt_of_eq x.isLt hLlen.symm)) (ho x))
      (v x).view.complementWeights (v x).view.cutoff
      (ReferenceLaterLiveNumericalReadout.selection_choiceValid (v x))
  let A := List.ofFn (fun x : Fin N =>
    ((Cells x).enabled, RecordedQueueRun.quantizedArrival qp (Cells x) a))
  let V := fun count => QueueReplay.replay cap (0, M.val.q) (A.take count)
  let Ed := ((R.drop bN.val).take d).map
    (fun r => (true, ReferenceFollowerSparseEmissionRecovery.emissionContribution M i r))
  let Q := ActiveFollowerDownAcceptance.recoveryQueueRecords p rate M logged ell
  let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  let o := u - (s + 1)
  let n := k.val - o
  let H := fun count => (segN.records.take count).map
    (ReferenceCollectionRawBufferHistory.physicalQueueRecord segN.context.preLedger a)
  let Ledge := fun count => ReferenceCollectionSegmentExtraction.endpointLedger
    segN.context.preLedger (segN.records.take count)
  have htimeBirth := ReferenceAssignmentPayloadChronology.installationBirth_time_eq
    (R[bN.val]'bN.isLt) c.payload hbirthN
  have htimeGiven := ReferenceAssignmentPayloadChronology.installationBirth_time_eq
    (R[b.val]'b.isLt) P hbirth
  have hpayloadSigma : c.payload.sigma.val = P.sigma.val := by
    exact Nat.add_right_cancel (hUsigma.symm.trans hselector)
  have htimeN := complete_record_time rate rewards C_star C_h z bN
  have htimeB := complete_record_time rate rewards C_star C_h z b
  have hbEq : bN = b := by
    apply Fin.ext
    apply Nat.add_left_cancel (n := s)
    calc
      s + bN.val = (R[bN.val]'bN.isLt).input.time.val := htimeN.symm
      _ = c.payload.sigma.val := htimeBirth.symm
      _ = P.sigma.val := hpayloadSigma
      _ = (R[b.val]'b.isLt).input.time.val := htimeGiven
      _ = s + b.val := htimeB
  have hpayload : c.payload = P :=
    ReferenceAssignmentPayloadChronology.installationBirth_payload_unique
      (R[b.val]'b.isLt) c.payload P (by simpa only [hbEq] using hbirthN) hbirth
  have hsigmaTime : P.sigma.val = s + b.val := htimeGiven.trans htimeB
  have hu : u = s + e + 1 := by
    dsimp only [u, bits, Pn]
    rw [hpayload]
    simpa only [Nat.add_assoc] using hscan
  have hoffset : o = e := offset_of_time s e u hu
  have hsegEq : segN = seg := by
    have hsame : ReferenceCollectionSegmentExtraction.segmentAt R e = some segN := by
      rw [← hoffset]
      exact hsegmentN
    exact Option.some.inj (hsame.symm.trans hseg)
  have hNlen : N = C.length := by
    dsimp only [N, sigma, Pn]
    rw [hpayloadSigma, hsigmaTime, hu, window_length_of_times]
    exact hClen.symm

  have hP0length : P0.length = b.val :=
    prefixInputs_length_at_index rate rewards C_star C_h z b P0 hP0

  have hCslots : ∀ x : Fin C.length, ∃ r : Record,
      R[b.val + x.val]? = some r ∧
      ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r = some C[x.val] := hCslot
  have hPC := prefixInputs_append_slots rate rewards C_star C_h z b.val P0 C hP0 hCslots
  have hCpos : 0 < C.length := by rw [← hNlen]; exact lt_of_lt_of_le hdpos hdle
  have heSplit : b.val + C.length = e := split_of_positive_length b.val e C.length hClen hCpos
  have hDrecords := segment_cells_original_slots rate R e seg hseg Dword hDlen
    (fun x => (hDslot x).1)
  have hPCprefix : ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
      rate rewards C_star C_h (s + (b.val + C.length)) z = some (P0 ++ C) := by
    exact hPC
  have hPD := prefixInputs_append_slots rate rewards C_star C_h z e (P0 ++ C)
    Dword (by simpa only [heSplit] using hPCprefix) hDrecords
  let G := P0 ++ C ++ Dword
  let q := e + seg.records.length
  have hGlen : G.length = q := by
    dsimp only [G, q]
    rw [List.length_append, List.length_append, hP0length, hDlen, heSplit]
  have hGprefix : ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
      rate rewards C_star C_h (s + q) z = some G := by
    dsimp only [q, G] at hPD ⊢
    simpa only [hDlen] using hPD

  have hCword : A = ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar rate a C := by
    exact native_word_eq_of_slots rate R bN.val N C a hNlen
      (by simpa only [hbEq] using hCslot) hLlen v ho
      (fun x => (hselected x).1)
      (by
        intro x
        rw [(hselected x).2.1, hpayload]
        exact Nat.lt_of_le_of_lt (Nat.zero_le s) hlater)
      (fun x => (hselected x).2.2.2)
  have hDword := collection_word_eq_of_slots rate seg Dword a hDlen (by
    intro x
    simpa only [a, Pn, hpayload] using (hDslot x).2)
  have hbaseProvB := hbaseProv
  rw [hbEq] at hbaseProvB
  have hbaseFunction : c.preLedger.baseScore = base := by
    split at hbaseProvB
    · rename_i hcoord
      have hread := hbase
      simp only [hcoord] at hread
      exact hbaseProvB.trans (Option.some.inj hread)
    · rename_i hcoord
      have hread := hbase
      simp only [hcoord] at hread
      exact hbaseProvB.trans (Option.some.inj hread)
    · exact False.elim hbaseProvB
  have hbaseScore : c.preLedger.baseScore i = base i := congrArg (fun f => f i) hbaseFunction
  have hIbaseScore : I.base i =
      (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate P0 a P0.length).1 := by
    calc
      I.base i = c.preLedger.baseScore i := by
        have h := hIbase
        exact congrArg (fun f => f i) h
      _ = base i := hbaseScore
      _ = _ := by simpa only [a, Pn, hpayload] using hscore
  have hqueue0 : M.val.q =
      (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate P0 a P0.length).2 := by
    dsimp only [M, Pn, a]
    rw [hpayload]
    exact hqueue

  refine ⟨c, bN, j, logged, after, cut, raw, scan, registers, lastService,
    hc, hbj, hjk, hbirthN, hretained, hlogged, hdown, houtcome, ?_⟩
  dsimp only [Pn, M, a, sigma, cap, bits, u, ell, N, d, o, n, L, qp]
  refine ⟨hscanN, hchecked, hqN, hUsigma, hdpos, hdle, htimes, hLlen, v, ho,
    hselected, hprepared, ?_⟩
  refine ⟨hQ, hEd, hAlen, hAenabled, hregisters, hlastService, ?_⟩
  refine ⟨segN, done, c0, I, hok, hoR, hn, hsegmentN, hentry, hsegContext,
    hc0, hI, hentryChoice, hIchecked, hIarm, hIsigma,
    hIcutoff, hIbase, hbaseProv, hrecord, hdone, hcontext, haccepted,
    hparsed, hsender, ?_⟩
  refine ⟨hfinal, ?_⟩
  refine ⟨recording, started, decoded, bank, hrecording, hstart, hreceive,
    hdecode, hfinish, hassignment, hstartedNone, hgammaStarted,
    hgammaDecoded, hfinishIncrement, hnext, hcontinuation, ?_⟩
  refine ⟨hbEq, hpayload, hoffset, hsegEq, hNlen.trans hClen, hCword,
    ?_, ?_, hGprefix, ?_, ?_⟩
  · intro count
    rw [hsegEq]
    exact hDword count
  · exact hGlen
  · rw [hsegEq, List.take_length]
    rfl
  · intro count hcountLower hcountUpper
    have hqueueE : M.val.q = (QueueReplay.replay cap (0, 0)
        (ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar rate a P0)).2 := by
      simpa only [ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay,
        List.take_length] using hqueue0
    have hscoreE : I.base i = (QueueReplay.replay cap (0, 0)
        (ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar rate a P0)).1 := by
      simpa only [ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay,
        List.take_length] using hIbaseScore
    have hcont := hcontinuation
      (ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar rate a P0)
      hqueueE hscoreE
    obtain ⟨hdownReg, hserviceReg, hHappend, hCutVal, hdelta, hcontinue⟩ := hcont
    obtain ⟨suffixAccepted, hcheckedRounds, htimesCount, hcutreg, hcurrentreg,
      hincrement, hpair, hassignmentCount, hsigmaCount, hcutoffCount, hfreezeCount⟩ :=
      hcontinue count hcountLower (by simpa only [hsegEq] using hcountUpper)
    let Full := fun j => QueueReplay.replay cap (0, 0)
      ((ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar rate a P0) ++
        (A ++ H j))
    let Cut := QueueReplay.replay cap (0, 0)
      ((ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar rate a P0) ++ A)
    let Prev := QueueReplay.replay cap (0, 0)
      ((ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar rate a P0) ++ A.take (N - 1))
    have hprefixCells : P0.length + C.length = e := by
      rw [hP0length]
      exact heSplit
    have hCpos : 0 < C.length := by rw [← hNlen]; exact lt_of_lt_of_le hdpos hdle
    obtain ⟨hCut, hPrev, hFull⟩ := calendar_replay_word_alignment rate a P0 C Dword e N A H
      hprefixCells hNlen hCpos hCword (by
        intro count
        dsimp only [H]
        rw [hsegEq]
        exact hDword count)
    have hfullEq := hFull count
    have hfullPrev := hFull (count - 1)
    change Cut = ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate G a e at hCut
    change Prev = ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate G a (e - 1) at hPrev
    change Full count =
      ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate G a (e + count) at hfullEq
    change Full (count - 1) =
      ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate G a (e + (count - 1)) at hfullPrev
    have hcutreg' : (Ledge count).cutoffRegisters a = some ⟨
        (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate G a e).1,
        (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate G a e).2,
        (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate G a e).1 -
          (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate G a (e - 1)).1⟩ := by
      change (Ledge count).cutoffRegisters a = some ⟨Cut.1, Cut.2, Cut.1 - Prev.1⟩ at hcutreg
      rw [hCut, hPrev] at hcutreg
      exact hcutreg
    have hcurrentreg' : (Ledge count).currentRegisters a = some ⟨
        (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate G a (e + count)).2,
        (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate G a (e + count)).1 -
          (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate G a (e + count - 1)).1⟩ := by
      change (Ledge count).currentRegisters a =
        some ⟨(Full count).2, (Full count).1 - (Full (count - 1)).1⟩ at hcurrentreg
      rw [hfullEq, hfullPrev] at hcurrentreg
      have hcountPos : 1 ≤ count :=
        le_trans (Nat.succ_le_succ (Nat.zero_le n)) hcountLower
      have hindex : e + (count - 1) = e + count - 1 := (Nat.add_sub_assoc hcountPos e).symm
      rw [hindex] at hcurrentreg
      exact hcurrentreg
    have hinc : (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate G a e).1 +
        (Ledge count).increment a =
        (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate G a (e + count)).1 := by
      change Cut.1 + (Ledge count).increment a = (Full count).1 at hpair
      rw [hCut, hfullEq] at hpair
      exact hpair
    exact ⟨hcutreg', hcurrentreg', hinc⟩

end Bandits.Support.ReferenceCompleteAssignedCalendarWordAlignment

end
