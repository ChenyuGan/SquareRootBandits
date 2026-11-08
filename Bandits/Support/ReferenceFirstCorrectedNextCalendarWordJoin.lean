/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteLaterLiveCollectionPrefixExtension
public import Bandits.Support.ReferenceFirstCorrectedNextOutsideCalendarReplay

import Mathlib.Tactic

/-!
# First corrected NEXT initialized calendar word

Sources: ZIP4 `appendix_a_local_protocol.tex:28-64`,
`06_interruptions.tex:192-233,246-299`, and
`04_slow_fast_learner.tex:157-174`.

The internal joins below preserve the original optional numerical prefix,
the actual NEXT birth, and the first retained collection on that same run.
-/

@[expose] public section
noncomputable section

open Bandits.Support
open ConstructorDimensions ReferenceActivePhysicalStep ReferenceActivePhysicalHorizon
open CoordinatorPhaseClock CoordinatorRoundDispatch CoordinatorAssignmentRegisterInstall
open LaterAssignmentStartOperation CanonicalFastSampling RecordedQueueRun
open ReferenceCollectionSegmentExtraction
open ReferenceLaterCollectionArrivalReadout ReferenceCollectionRawBufferHistory

namespace Bandits.Support.ReferenceFirstCorrectedNextCalendarWordJoin

variable {p : ConstructorDimensions.Parameters}

/-- The complete numerical calendar record for one arm, retaining enabled
zero-arrival rounds exactly as the physical queue replay does. -/
def rawCalendar (rate : ReferenceActivePhysicalStep.RateInput p)
    (a : Fin p.K) (cells : List (RecordedQueueRun.RoundInput p.K)) :
    List (Bool × ℕ) :=
  cells.map fun cell =>
    (cell.enabled, RecordedQueueRun.quantizedArrival
      (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell a)

/-- Zero-origin, unstopped mathematical replay of a finite numerical calendar prefix. -/
def calendarReplay (rate : ReferenceActivePhysicalStep.RateInput p)
    (C : List (RecordedQueueRun.RoundInput p.K)) (a : Fin p.K) (h : ℕ) : ℕ × ℕ :=
  QueueReplay.replay (4 * rate.n) (0, 0) (rawCalendar rate a (C.take h))

/-- The raw all-arm calendar splits at a recorded cell without dropping its
enabled marker or its quantized arrival. -/
private theorem rawCalendar_append_birth
    (rate : ReferenceActivePhysicalStep.RateInput p) (a : Fin p.K)
    (first : List (RecordedQueueRun.RoundInput p.K))
    (birth : RecordedQueueRun.RoundInput p.K)
    (tail : List (RecordedQueueRun.RoundInput p.K))
    (henabled : birth.enabled = true) :
    rawCalendar rate a (first ++ [birth] ++ tail) =
      rawCalendar rate a first ++
        [(true, RecordedQueueRun.quantizedArrival
          (ReferenceFirstLaunchNumericalCell.queueParameters rate) birth a)] ++
        rawCalendar rate a tail := by
  simp only [rawCalendar, List.map_append, List.map_cons, List.map_nil, henabled]

/-- A queue replay translates its score register by the same constant while
leaving its backlog unchanged. -/
private theorem transition_score_shift (capacity offset score queue : ℕ)
    (record : Bool × ℕ) :
    QueueReplay.transition capacity (offset + score, queue) record =
      (offset + (QueueReplay.transition capacity (score, queue) record).1,
        (QueueReplay.transition capacity (score, queue) record).2) := by
  cases record with
  | mk enabled arrival =>
      cases enabled
      · simp [QueueReplay.transition]
      · simp [QueueReplay.transition, Nat.add_assoc]

private theorem replay_score_shift (capacity offset score queue : ℕ)
    (records : List (Bool × ℕ)) :
    QueueReplay.replay capacity (offset + score, queue) records =
      (offset + (QueueReplay.replay capacity (score, queue) records).1,
        (QueueReplay.replay capacity (score, queue) records).2) := by
  induction records generalizing score queue with
  | nil => rfl
  | cons record rest ih =>
      change QueueReplay.replay capacity
        (QueueReplay.transition capacity (offset + score, queue) record) rest =
        (offset + (QueueReplay.replay capacity
          (QueueReplay.transition capacity (score, queue) record) rest).1,
          (QueueReplay.replay capacity
            (QueueReplay.transition capacity (score, queue) record) rest).2)
      rw [transition_score_shift, ih]

private theorem live_cell0
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (s : ℕ)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (c : RecordedQueueRun.RoundInput p.K)
    (hread : ReferenceLaterLiveNumericalReadout.laterLiveReadout s r = some c) :
    ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r = some c := by
  classical
  obtain ⟨selected, ho, hselection, hbase, hliveState, hcell⟩ :=
    ReferenceLaterLiveNumericalReadout.laterLiveReadout_some s r c hread
  have hz : 0 < selected.view.payload.sigma.val := by omega
  have hzero : ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r = some c := by
    unfold ReferenceLaterLiveNumericalReadout.laterLiveReadout
    simp only [hselection, hz, hliveState, and_self, ite_true, dite_eq_left ho]
    exact congrArg some hcell.symm
  have hcollection : ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 r = none := by
    cases hc : ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 r with
    | none => rfl
    | some d =>
        exact False.elim (ReferenceCompleteNumericalBranchObservation.readouts_disjoint
          rate 0 r ⟨by rw [hzero]; rfl, by rw [hc]; rfl⟩)
  simp [ReferenceFirstCollectionCurrentRetainedGate.cell0, hcollection, hzero]

private theorem replayLastService_difference (capacity : ℕ) (initial : ℕ × ℕ)
    (retained : ℕ) (records : List (Bool × ℕ)) (hne : records ≠ []) :
    CollectionKnownQueueContinuation.replayLastService capacity initial retained records =
      (QueueReplay.replay capacity initial records).1 -
        (QueueReplay.replay capacity initial (records.take (records.length - 1))).1 := by
  rw [CollectionKnownQueueContinuation.replayLastService,
    List.getLast?_eq_getLast_of_ne_nil hne]
  have hsplit := List.dropLast_append_getLast hne
  have hfull : QueueReplay.replay capacity initial records =
      QueueReplay.transition capacity
        (QueueReplay.replay capacity initial records.dropLast) (records.getLast hne) := by
    conv_lhs => rw [← hsplit, QueueReplay.replay_append]
    rfl
  rw [hfull, List.dropLast_eq_take]

private theorem take_before_append {α : Type*} (A B : List α) (n : ℕ)
    (hn : n ≤ A.length) : (A ++ B).take n = A.take n := by
  simp only [List.take_append, Nat.sub_eq_zero_of_le hn, List.take_zero, List.append_nil]

private theorem take_through_append {α : Type*} (A B : List α) (n : ℕ) :
    (A ++ B).take (A.length + n) = A ++ B.take n := by
  simp only [List.take_append, Nat.add_sub_cancel_left,
    List.take_of_length_le (Nat.le_add_right _ _)]

section

variable {rate : ReferenceActivePhysicalStep.RateInput p}

private theorem collection_readout_disabled (s : ℕ) (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (c : RecordedQueueRun.RoundInput p.K)
    (hread : laterCollectionReadout s r = some c) (hdisabled : c.enabled = false) :
    c.recordedArm = none ∧ ∀ a, RecordedQueueRun.quantizedArrival
      (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a = 0 := by
  classical
  have hmarker : c.recordedArm = none := by
    unfold laterCollectionReadout at hread
    split at hread
    next =>
      cases hc : r.output.preparation.coordinator with
      | first outcome => cases outcome <;> simp [hc] at hread
      | invalidCollectionCutoff => simp [hc] at hread
      | dagger => simp [hc] at hread
      | collection payload ledger clock cutoff outcome =>
        cases outcome <;> simp only [hc] at hread
        all_goals try contradiction
        next core snapshot hcontinue selected =>
          cases Option.some.inj hread
          change (SnapshotRecordingKernel.recordingMap p .collection _ _ _ _ _ _ _ _ _ _ _) = none
          change (continuingCollectionInput r payload ledger clock cutoff snapshot).enabled = false at hdisabled
          dsimp only [continuingCollectionInput] at hdisabled
          rw [hdisabled]
          exact SnapshotRecordingKernel.recordingMap_disabled ..
      | live registers owned base outcome =>
        cases outcome <;> simp only [hc] at hread
        all_goals try contradiction
        next dispatched hs ledger hi he hd hclock hp hn selected =>
          split at hread
          next =>
            cases Option.some.inj hread
            change (SnapshotRecordingKernel.recordingMap p .collection _ _ _ _ _ _ _ _ _ _ _) = none
            change (laterCutoffCollectionInput r registers owned base dispatched selected).enabled = false at hdisabled
            dsimp only [laterCutoffCollectionInput] at hdisabled
            rw [hdisabled]
            exact SnapshotRecordingKernel.recordingMap_disabled ..
          next => contradiction
    next => contradiction
  refine ⟨hmarker, ?_⟩
  intro a
  simp only [RecordedQueueRun.quantizedArrival, hmarker, reduceCtorEq, ite_false]

private theorem cell0_disabled
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) (c : RoundInput p.K)
    (hc : ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r = some c)
    (hdisabled : c.enabled = false) :
    c.recordedArm = none ∧ ∀ a, quantizedArrival
      (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a = 0 := by
  cases hl : ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r with
  | none =>
    have hr : laterCollectionReadout 0 r = some c := by
      simpa only [ReferenceFirstCollectionCurrentRetainedGate.cell0, hl, Option.none_or] using hc
    exact collection_readout_disabled 0 r c hr hdisabled
  | some d =>
    have heq : d = c := Option.some.inj (by
      simpa only [ReferenceFirstCollectionCurrentRetainedGate.cell0, hl, Option.some_or] using hc)
    subst d
    have he := (ReferenceLaterLiveNumericalReadout.laterLiveReadout_numerical 0 r c hl).1
    rw [hdisabled] at he
    contradiction

private theorem tagged_readout_of_cell0
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) (c : RoundInput p.K)
    (hc : ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r = some c) :
    (ReferenceCompleteNumericalBranchObservation.branchReadout rate 0 r).map (Sum.elim id id) =
      some (ReferenceCompleteNumericalBranchObservation.encodeNumerical c) := by
  have hp := ReferenceCompleteNumericalBranchObservation.branch_readout_projections rate 0 r
  cases ht : ReferenceCompleteNumericalBranchObservation.branchReadout rate 0 r with
  | none =>
    cases hl : ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r <;>
      cases hr : laterCollectionReadout 0 r <;>
      simp_all [ReferenceCompleteNumericalBranchObservation.leftProjection,
        ReferenceCompleteNumericalBranchObservation.rightProjection,
        ReferenceFirstCollectionCurrentRetainedGate.cell0]
  | some tag =>
    cases tag <;>
      cases hl : ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r <;>
      cases hr : laterCollectionReadout 0 r <;>
      simp_all [ReferenceCompleteNumericalBranchObservation.leftProjection,
        ReferenceCompleteNumericalBranchObservation.rightProjection,
        ReferenceFirstCollectionCurrentRetainedGate.cell0]

private theorem mapM_id_some {α : Type*} (slots : List (Option α)) (cells : List α)
    (h : slots.mapM id = some cells) : slots = cells.map some := by
  induction slots generalizing cells with
  | nil =>
    have he : cells = [] := (Option.some.inj h).symm
    subst cells
    rfl
  | cons slot slots ih =>
    cases slot with
    | none => simp [List.mapM_cons] at h
    | some a =>
      cases ht : slots.mapM id with
      | none => simp [List.mapM_cons, ht] at h
      | some tail =>
        have he : a :: tail = cells := by simpa [List.mapM_cons, ht] using h
        rw [← he, List.map_cons, ← ih tail ht]

/-- Successful optional coverage identifies every chronological slot, rather
than merely the number of retained cells. -/
private theorem prefixInputs_readout
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (q : ℕ) (G : List (RoundInput p.K))
    (hlen : G.length = q)
    (hq : q ≤ (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).length)
    (hprefix : ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
      rate rewards C_star C_h
        (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + q) z = some G) :
    ∀ k : Fin q,
      ReferenceFirstCollectionCurrentRetainedGate.cell0 rate
        ((ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val]'(by omega)) =
          some (G[k.val]'(by omega)) := by
  have hs := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs_launch
    rate rewards C_star C_h _ z G hprefix
  simp only [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs,
    ite_eq_left hs, ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart,
    Nat.add_sub_cancel_left] at hprefix
  have hmap := mapM_id_some _ G hprefix
  intro k
  have he := congrArg (fun L => L[k.val]?) hmap
  simpa only [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords,
    List.getElem?_map, List.getElem?_take, show k.val < q from k.isLt, ite_true,
    List.getElem?_eq_getElem (show k.val <
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).length by omega),
    List.getElem?_eq_getElem (show k.val < G.length by omega), Option.map_some, Option.some.injEq] using he

private theorem calendar_coordinates
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (q : ℕ) (G : List (RoundInput p.K))
    (hlen : G.length = q)
    (hq : q ≤ (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).length)
    (hprefix : ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
      rate rewards C_star C_h
        (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + q) z = some G) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    let Omega := ReferenceCompleteNumericalBranchObservation.completeBranchObservation
      rate rewards C_star C_h z
    (∀ k : Fin q,
      let r := R[k.val]'(Nat.lt_of_lt_of_le k.isLt hq)
      let c := G[k.val]'(by omega)
      ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r = some c ∧
      r.input.time.val = s + k.val ∧
      (Omega[k.val]'(by
        simpa only [Omega, ReferenceCompleteNumericalBranchObservation.completeBranchObservation,
          ReferenceCompleteNumericalBranchObservation.branchCalendar, List.length_map, R] using
            (Nat.lt_of_lt_of_le k.isLt hq))).1 = r.input.time ∧
      ((Omega[k.val]'(by
        simpa only [Omega, ReferenceCompleteNumericalBranchObservation.completeBranchObservation,
          ReferenceCompleteNumericalBranchObservation.branchCalendar, List.length_map, R] using
            (Nat.lt_of_lt_of_le k.isLt hq))).2.2).map (Sum.elim id id) =
        some (ReferenceCompleteNumericalBranchObservation.encodeNumerical c)) ∧
    (∀ c ∈ G, c.enabled = false → c.recordedArm = none ∧ ∀ a,
      quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a = 0) := by
  intro R s Omega
  change q ≤ R.length at hq
  have hc := prefixInputs_readout rewards C_star C_h z q G hlen hq hprefix
  constructor
  · intro k
    have htimes : R.map (fun r => r.input.time.val) = List.range' s (p.T - s) :=
      ReferenceCompletePhysicalHistory.completeSuffixRecords_time_values rate z rewards C_star C_h
    have hlenR : R.length = p.T - s :=
      ReferenceCompletePhysicalHistory.completeSuffixRecords_length rate z rewards C_star C_h
    have hindex : k.val < R.length := Nat.lt_of_lt_of_le k.isLt hq
    have hcal : k.val < (List.range' s (p.T - s)).length := by
      simp only [List.length_range']
      omega
    have ht : (R[k.val]'hindex).input.time.val = s + k.val := by
      have hget : (R.map (fun r => r.input.time.val))[k.val]'(by simpa only [List.length_map] using hindex) =
          (List.range' s (p.T - s))[k.val]'hcal := by simp only [htimes]
      simpa only [List.getElem_map, List.getElem_range', Nat.one_mul] using hget
    refine ⟨hc k, ht, ?_, ?_⟩
    · simp only [Omega, ReferenceCompleteNumericalBranchObservation.completeBranchObservation,
        ReferenceCompleteNumericalBranchObservation.branchCalendar, List.getElem_map, R]
    · simpa only [Omega, ReferenceCompleteNumericalBranchObservation.completeBranchObservation,
        ReferenceCompleteNumericalBranchObservation.branchCalendar, List.getElem_map] using
        tagged_readout_of_cell0 _ _ (hc k)
  · intro c hmem hdisabled
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hmem
    have hkq : k < q := by omega
    exact cell0_disabled _ _ (hc ⟨k, hkq⟩) hdisabled

end

private theorem replay_collection_transport (capacity : ℕ)
    (before records : List (Bool × ℕ)) (retained : ℕ) (hne : records ≠ []) :
    let V := QueueReplay.replay capacity (0, 0) before
    let Y := QueueReplay.replay capacity (0, V.2) records
    Y.2 = (QueueReplay.replay capacity (0, 0) (before ++ records)).2 ∧
    CollectionKnownQueueContinuation.replayLastService capacity (0, V.2) retained records =
      (QueueReplay.replay capacity (0, 0) (before ++ records)).1 -
        (QueueReplay.replay capacity (0, 0)
          (before ++ records.take (records.length - 1))).1 ∧
    V.1 + Y.1 = (QueueReplay.replay capacity (0, 0) (before ++ records)).1 := by
  intro V Y
  have hshift (C : List (Bool × ℕ)) :
      QueueReplay.replay capacity V C =
        (V.1 + (QueueReplay.replay capacity (0, V.2) C).1,
          (QueueReplay.replay capacity (0, V.2) C).2) := by
    simpa only [Nat.add_zero] using replay_score_shift capacity V.1 0 V.2 C
  have hfull : QueueReplay.replay capacity (0, 0) (before ++ records) =
      (V.1 + Y.1, Y.2) := by
    rw [QueueReplay.replay_append]
    exact hshift records
  refine ⟨(congrArg Prod.snd hfull).symm, ?_, (congrArg Prod.fst hfull).symm⟩
  rw [replayLastService_difference capacity (0, V.2) retained records hne,
    hfull, QueueReplay.replay_append, hshift]
  exact (Nat.add_sub_add_left _ _ _).symm

private theorem take_birth_prefix {α : Type*} (C G : List α) (c : α) (q : ℕ)
    (hG : G.length = q) (htake : C.take (q + 1) = G ++ [c]) :
    C.take q = G := by
  calc
    C.take q = (C.take (q + 1)).take q := by simp only [List.take_take, Nat.min_eq_left (show q ≤ q + 1 by omega)]
    _ = (G ++ [c]).take q := congrArg (fun xs => xs.take q) htake
    _ = G := by rw [take_before_append _ _ _ (by omega), ← hG, List.take_length]

private theorem include_birth_boundary
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (s q v : ℕ) (C G : List (RecordedQueueRun.RoundInput p.K))
    (htake : C.take q = G)
    (hold : ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
      rate rewards C_star C_h (s + q) z = some G)
    (hnext : ∀ h, q + 1 ≤ h → h ≤ v →
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
        rate rewards C_star C_h (s + h) z = some (C.take h)) :
    ∀ h, q ≤ h → h ≤ v →
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
        rate rewards C_star C_h (s + h) z = some (C.take h) := by
  intro h hq hv
  by_cases heq : h = q
  · subst h
    rw [htake]
    exact hold
  · exact hnext h (by omega) hv

/-- A local initialized LIVE word. Its prefix and numerical seeds are explicit
local inputs; the original corrected-cell application below constructs them. -/
private theorem initialized_live_word
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (r0 : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q0 : CoordinatorLiveServiceFinish.OwnedRegisters r0)
    (beta : Fin (p.m - 1) → ℕ)
    (hstate : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[b.val].input.state.coordinator = .live r0 q0 beta)
    (hlater : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h <
      r0.payload.sigma.val)
    (P : List (RecordedQueueRun.RoundInput p.K))
    (hP : ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
      rate rewards C_star C_h
        (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + b.val) z = some P)
    (hseed : ∀ j : FastArm r0.payload.slowSet,
      (r0.complementScores j, q0.queue j) =
        QueueReplay.replay (4 * rate.n) (0, 0) (rawCalendar rate j.val P))
    (hprevious : ∀ j : FastArm r0.payload.slowSet,
      q0.previousService j =
        (QueueReplay.replay (4 * rate.n) (0, 0) (rawCalendar rate j.val P)).1 -
        (QueueReplay.replay (4 * rate.n) (0, 0)
          (rawCalendar rate j.val (P.take (b.val - 1)))).1) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
      rate rewards C_star C_h z b.val
    let B := ReferenceCompleteLaterLiveComplementPrefixReplay.prefixCells
      rewards C_star C_h z b r0 q0 beta hstate hlater
    let e := b.val + W.length
    let H := P ++ B
    P.length = b.val ∧ B.length = W.length ∧ e ≤ R.length ∧ s + e ≤ p.T ∧
    H.length = e ∧ H.take b.val = P ∧
    (∀ h, b.val ≤ h → h ≤ e →
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
        rate rewards C_star C_h (s + h) z = some (H.take h)) ∧
    (∀ i : Fin W.length,
      let k : Fin R.length := ⟨b.val + i.val, by
        have hbound := ReferenceCompleteLaterLiveComplementPrefixReplay.prefix_length_le
          rewards C_star C_h z b
        change b.val + W.length ≤ R.length at hbound
        exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt b.val) hbound⟩
      let r := R.get k
      let c := B[i.val]'(by
        rw [ReferenceCompleteLaterLiveComplementPrefixReplay.prefixCells_length
          rewards C_star C_h z b r0 q0 beta hstate hlater]
        exact i.isLt)
      ∀ a : Fin p.K,
      ∃ cell : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell r,
        cell.input = c ∧
        (∃! owner : Fin p.m, SnapshotRecordingKernel.owns p (.live cell.selected.view.payload.assignment
          (ReferenceActiveDataOwnership.choiceSnapshot cell.selected cell.states)) owner a) ∧
        ((a ∉ cell.selected.view.payload.slowSet.1 ∧
          ∃ out, r.output.coordinator.recording = some out ∧
            ReferenceCoordinatorRecorderCallTrace.coordinatorRaw
                (ReferenceActiveHorizonMeasurability.roundRecordCode r) a =
              some (RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a)) ∨
          ∃ i : Fin (p.m - 1), cell.selected.view.payload.assignment.assigned i = a ∧
            (∀ j, cell.selected.view.payload.assignment.assigned j = a → j = i) ∧
            (if (cell.states i).status = .unoccupied then
              ReferenceContinuingRecordingPhysicalReward.actualCurrentSavedContribution r cell.selected.view.payload i
            else ActiveFollowerQueueOperation.rawArrival rate.eta i r.input.row r.input.time
              (cell.selected.view.payload.downRecord i) (r.output.ownEntries (PublicDiscreteDraws.followerPlayer p.two_le_m i)).2) =
              RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a)) ∧
    (∀ (hV : e ≤ R.length) (hE : H.length = e) (k : Fin e),
      let r := R[k.val]'(Nat.lt_of_lt_of_le k.isLt hV)
      let c := H[k.val]'(by simpa only [hE] using k.isLt)
      let Omega := ReferenceCompleteNumericalBranchObservation.completeBranchObservation
        rate rewards C_star C_h z
      ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r = some c ∧
      r.input.time.val = s + k.val ∧
      (Omega[k.val]'(by
        simpa [Omega, ReferenceCompleteNumericalBranchObservation.completeBranchObservation,
          ReferenceCompleteNumericalBranchObservation.branchCalendar] using
          (Nat.lt_of_lt_of_le k.isLt hV))).1 = r.input.time ∧
      ((Omega[k.val]'(by
        simpa [Omega, ReferenceCompleteNumericalBranchObservation.completeBranchObservation,
          ReferenceCompleteNumericalBranchObservation.branchCalendar] using
          (Nat.lt_of_lt_of_le k.isLt hV))).2.2).map (Sum.elim id id) =
        some (ReferenceCompleteNumericalBranchObservation.encodeNumerical c)) ∧
    (∀ c ∈ H, c.enabled = false → c.recordedArm = none ∧ ∀ a,
      quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a = 0) ∧
    (e = R.length ∨
      ∃ (he : e < R.length)
        (rE : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
        (qE : CoordinatorLiveServiceFinish.OwnedRegisters rE)
        (seg : Segment rate) (I : Initializer p) (l0 : Ledger rate)
        (Dword : List (RecordedQueueRun.RoundInput p.K)),
        rE.payload = r0.payload ∧ R[e].input.state.coordinator = .live rE qE beta ∧
        segmentAt R e = some seg ∧ seg.entry = R[e] ∧
        seg.context.payload = r0.payload ∧ seg.context.preLedger = l0 ∧
        seg.context.initializer = some I ∧
        I = cutoffInitializer (liveRegistersAt rE R[e].input.time)
          (liveOwnedAt rE qE R[e].input.time) beta R[e].input.time ∧
        I.checkedStart rate = .success l0 ∧
        I.assignment.arm = r0.payload.assignment.assigned ∧
        I.sigma = r0.payload.sigma.val + 1 ∧ I.cutoff = s + e + 1 ∧
        I.cutoff = FollowerCutoffScan.firstCutoff p rate.eta.val r0.payload.sigma
          (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
            (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z))) ∧
        I.freezeAt = rE.gridBoundary ∧ I.base = beta ∧
        ReferenceCollectionPhaseHistory.cutoffChosen seg.entry.input = true ∧
        (∃ tail, seg.records = seg.entry :: tail) ∧
        seg.records ++ seg.remaining = R.drop e ∧ seg.exit = exitOf seg.remaining ∧
        CollectionCheckedExecution.startAndRunChecked p rate.eta.val rate.eta.property
          (ReferenceUpReception.sourceCap_forLedger rate) rate.n rate.n_scale
          I.assignment I.sigma I.cutoff I.freezeAt I.base I.outside seg.inputs =
            .success ⟨l0, seg.accepted, seg.final⟩ ∧
        Dword.length = seg.records.length ∧
        seg.records.map (laterCollectionReadout s) = Dword.map some ∧
        (∀ a, CollectionKnownQueueContinuation.inputQueueRecords l0 a seg.inputs =
            seg.records.map (physicalQueueRecord l0 a) ∧
          seg.records.map (physicalQueueRecord l0 a) = rawCalendar rate a Dword) ∧
        let E := H ++ Dword
        let v := e + seg.records.length
        E.length = v ∧ E.take e = H ∧ E.take b.val = P ∧
        v ≤ R.length ∧ s + v ≤ p.T ∧ R.take v = R.take e ++ seg.records ∧
        (∀ h, b.val ≤ h → h ≤ v →
          ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
            rate rewards C_star C_h (s + h) z = some (E.take h)) ∧
        (∀ (hV : v ≤ R.length) (hE : E.length = v) (k : Fin v),
          let r := R[k.val]'(Nat.lt_of_lt_of_le k.isLt hV)
          let c := E[k.val]'(by simpa only [hE] using k.isLt)
          let Omega := ReferenceCompleteNumericalBranchObservation.completeBranchObservation
            rate rewards C_star C_h z
          ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r = some c ∧
          r.input.time.val = s + k.val ∧
          (Omega[k.val]'(by
            simpa [Omega, ReferenceCompleteNumericalBranchObservation.completeBranchObservation,
              ReferenceCompleteNumericalBranchObservation.branchCalendar] using
              (Nat.lt_of_lt_of_le k.isLt hV))).1 = r.input.time ∧
          ((Omega[k.val]'(by
            simpa [Omega, ReferenceCompleteNumericalBranchObservation.completeBranchObservation,
              ReferenceCompleteNumericalBranchObservation.branchCalendar] using
              (Nat.lt_of_lt_of_le k.isLt hV))).2.2).map (Sum.elim id id) =
            some (ReferenceCompleteNumericalBranchObservation.encodeNumerical c)) ∧
        (∀ i : Fin B.length, B[i.val].enabled = true) ∧
        (∀ j : Fin Dword.length,
          Dword[j.val].enabled = false → Dword[j.val].recordedArm = none ∧ ∀ a,
            RecordedQueueRun.quantizedArrival
              (ReferenceFirstLaunchNumericalCell.queueParameters rate) Dword[j.val] a = 0) ∧
        (∀ c ∈ E, c.enabled = false → c.recordedArm = none ∧ ∀ a,
          quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a = 0) ∧
        let U := fun (a : Fin p.K) (h : ℕ) =>
          QueueReplay.replay (4 * rate.n) (0, 0) (rawCalendar rate a (E.take h))
        ∀ j : FastArm r0.payload.slowSet,
          seg.final.cutoffRegisters j.val =
            some ⟨(U j.val e).1, (U j.val e).2, (U j.val e).1 - (U j.val (e - 1)).1⟩ ∧
          seg.final.currentRegisters j.val =
            some ⟨(U j.val v).2, (U j.val v).1 - (U j.val (v - 1)).1⟩ ∧
          (U j.val e).1 + seg.final.increment j.val = (U j.val v).1) := by
  classical
  intro R s W B e H
  obtain ⟨hPlen, heR, heT, hHlen, hHtake, hprefix, hslots,
    rE, qE, hp, _hlast, hin, _hvalues, halt⟩ :=
    ReferenceCompleteLaterLiveCollectionPrefixExtension.complete_later_live_collection_prefix_extension
      rate rewards C_star C_h z b r0 q0 beta hstate hlater P hP
  have hBlen : B.length = W.length :=
    ReferenceCompleteLaterLiveComplementPrefixReplay.prefixCells_length
      rewards C_star C_h z b r0 q0 beta hstate hlater
  have hrawSlots := fun (i : Fin W.length) (a : Fin p.K) =>
    ReferenceLaterLiveNumericalReadout.laterLiveReadout_all_arm_numerical
      rate rewards C_star C_h z
      ⟨b.val + i.val, by
        have hbound := ReferenceCompleteLaterLiveComplementPrefixReplay.prefix_length_le
          rewards C_star C_h z b
        change b.val + W.length ≤ R.length at hbound
        exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt b.val) hbound⟩
      (B[i.val]'(by rw [ReferenceCompleteLaterLiveComplementPrefixReplay.prefixCells_length
        rewards C_star C_h z b r0 q0 beta hstate hlater]; exact i.isLt))
      (by simpa only [List.get_eq_getElem] using (hslots i).2.2.2.2.1) a
  have hHlenLocal : H.length = e := hHlen
  have heRLocal : e ≤ R.length := heR
  have hprefixH : ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
      rate rewards C_star C_h (s + e) z = some H := by
    have h : ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
        rate rewards C_star C_h (s + e) z = some (H.take e) :=
      hprefix e (by omega) le_rfl
    rw [List.take_of_length_le (by omega : H.length ≤ e)] at h
    exact h
  have hcoverageH := calendar_coordinates (rate := rate) rewards C_star C_h z
    e H hHlenLocal heRLocal hprefixH
  refine ⟨hPlen, hBlen, heR, heT, hHlen, hHtake, hprefix, hrawSlots,
    (fun _ _ => hcoverageH.1), hcoverageH.2, ?_⟩
  rcases halt with hterminal | ⟨he, chosen, _hdispatch, _hprep, hcut⟩
  · exact Or.inl hterminal
  · cases chosen with
    | cutoffChosen dispatched hstart ledger hinit hcand hdomain hclock hpending hnone selected =>
      obtain ⟨_hdate, _hscan, seg, I, Dword, hD, hat, hentry, hpay, hledger,
        hI, hIeq, hchecked, harm, hsigma, hcutoff, hscanI, hfreeze, hbaseI,
        hchosen, hne, hpart, hexit, hfold, _hv, _ht, _hcover, hmap, hsync,
        _hunique, hElen, hEtake, hEtakeP, hV, hVtime, hRtake, hprefixAll,
        hcoords, henabled, hdisabled⟩ := hcut
      let l0 := sharedLedger ledger
      let E := H ++ Dword
      let v := e + seg.records.length
      have hElenLocal : E.length = v := hElen
      have hprefixE : ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
          rate rewards C_star C_h (s + v) z = some E := by
        have h : ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
            rate rewards C_star C_h (s + v) z = some (E.take v) :=
          hprefixAll v (by dsimp [v, e]; omega) le_rfl
        rw [List.take_of_length_le (by omega : E.length ≤ v)] at h
        exact h
      have hcoverageE := calendar_coordinates (rate := rate) rewards C_star C_h z
        v E hElenLocal hV hprefixE
      refine Or.inr ⟨he, rE, qE, seg, I, l0, Dword, hp, hin he, hat,
        hentry, hpay, hledger, hI, hIeq, hchecked, harm, hsigma, hcutoff,
        hscanI, hfreeze, hbaseI, hchosen, ?_, hpart, hexit, hfold, hD,
        hmap, hsync, hElen, hEtake, hEtakeP, hV, hVtime, hRtake,
        hprefixAll, hcoords, henabled, hdisabled, hcoverageE.2, ?_⟩
      · simpa only [hentry] using hne
      · have hboundary :=
          ReferenceCompleteLaterLiveOutsideCutoffBoundary.complete_later_live_outside_cutoff_boundary
            rate rewards C_star C_h z b
        dsimp only at hboundary
        split at hboundary
        next rB qB betaB hBstate =>
          have hfields := CoordinatorConfiguration.live.inj (hBstate.symm.trans hstate)
          have hrB := hfields.1
          have hqB := hfields.2.1
          have hbetaB := hfields.2.2
          subst rB
          cases hqB
          subst betaB
          obtain ⟨rF, qF, _hpF, _houtF, hinF, _hvaluesF, hboundaryExit⟩ := hboundary hlater
          have hendpointFields := CoordinatorConfiguration.live.inj
            ((hinF he).symm.trans (hin he))
          have hrFE := hendpointFields.1
          have hqFE := hendpointFields.2.1
          subst rF
          cases hqFE
          rcases hboundaryExit with hterminal | ⟨heF, chosenF, _hdF, _hpF, hcutF⟩
          · exact False.elim ((Nat.ne_of_lt he) hterminal)
          · cases chosenF with
            | cutoffChosen dispatchedF hsF ledgerF hiF hcF hdomF hclockF hpendF hnF selF =>
              obtain ⟨_hdateF, _hscanF, segF, IF, hatF, _hentryF, _hpayF, hledgerF,
                _hIF, _hIdefF, _hcheckedF, _harmF, _hsigmaF, _hcutoffF, _hfreezeF,
                _hbaseF, _hneF, _hpartF, _hexitF, _hfoldF, _hknownF, _hunknownF,
                recordingF, startedF, decodedF, bankF, lfF, clockF, _hrecordF,
                _hbridgeF, _hstartF, _hreceiveF, _hdecodedF, _hfinishF, _hclockFinishF,
                _hnextF, _hfailureF, _hbaseScoreF, _hgammaF, _hfirstF, hfinalF⟩ := hcutF
              have hsegEq : segF = seg := Option.some.inj (hatF.symm.trans hat)
              subst segF
              have hledgerEq : sharedLedger ledgerF = l0 := hledgerF.symm.trans hledger
              rw [hledgerEq] at hfinalF
              intro U j
              -- Transport the actual known-arm fields onto the same complete word.
              have hfinal := hfinalF j
              have hsyncJ := (hsync j.val).1.trans (hsync j.val).2
              change CollectionKnownQueueContinuation.inputQueueRecords l0 j.val seg.inputs =
                rawCalendar rate j.val Dword at hsyncJ
              rw [hsyncJ] at hfinal
              let V := fun n => QueueReplay.replay (4 * rate.n)
                (r0.complementScores j, q0.queue j) (rawCalendar rate j.val (B.take n))
              let d := if W.length = 0 then q0.previousService j
                else (V W.length).1 - (V (W.length - 1)).1
              change seg.final.cutoffRegisters j.val =
                  some ⟨(V W.length).1, (V W.length).2, d⟩ ∧
                seg.final.currentRegisters j.val = some
                  ⟨(QueueReplay.replay (4 * rate.n) (0, (V W.length).2)
                    (rawCalendar rate j.val Dword)).2,
                    CollectionKnownQueueContinuation.replayLastService (4 * rate.n)
                      (0, (V W.length).2) d (rawCalendar rate j.val Dword)⟩ ∧
                seg.final.increment j.val =
                  (QueueReplay.replay (4 * rate.n) (0, (V W.length).2)
                    (rawCalendar rate j.val Dword)).1 ∧ _ at hfinal
              have hVglobal (n : ℕ) (hn : n ≤ W.length) :
                  V n = U j.val (b.val + n) := by
                change QueueReplay.replay (4 * rate.n)
                    (r0.complementScores j, q0.queue j)
                    (rawCalendar rate j.val (B.take n)) = _
                rw [hseed j]
                rw [← QueueReplay.replay_append]
                change _ = QueueReplay.replay (4 * rate.n) (0, 0)
                  (rawCalendar rate j.val (E.take (b.val + n)))
                have htake : E.take (b.val + n) = P ++ B.take n := by
                  change ((P ++ B) ++ Dword).take (b.val + n) = _
                  rw [take_before_append _ _ _ (by simp only [List.length_append]; omega)]
                  rw [← hPlen, take_through_append]
                rw [htake]
                simp only [rawCalendar, List.map_append]
              have hVe : V W.length = U j.val e := hVglobal _ le_rfl
              have hd : d = (U j.val e).1 - (U j.val (e - 1)).1 := by
                dsimp only [d]
                split_ifs with hz
                · have h0 : W.length = 0 := hz
                  have hBnil : B = [] := List.length_eq_zero_iff.mp (hBlen.trans hz)
                  have hprev := hprevious j
                  have htakeP : E.take (e - 1) = P.take (b.val - 1) := by
                    simp only [E, H, hBnil, List.append_nil]
                    have heq : e = b.val := by dsimp [e]; omega
                    rw [heq, take_before_append _ _ _ (by omega)]
                  have hscore : (V W.length).1 =
                      (QueueReplay.replay (4 * rate.n) (0, 0) (rawCalendar rate j.val P)).1 := by
                    simpa only [V, hz, List.take_zero, rawCalendar, List.map_nil,
                      QueueReplay.replay, List.foldl_nil] using congrArg Prod.fst (hseed j)
                  rw [← hVe, hscore]
                  change _ = _ - (QueueReplay.replay (4 * rate.n) (0, 0)
                    (rawCalendar rate j.val (E.take (e - 1)))).1
                  rw [htakeP]
                  exact hprev
                · rw [hVe, hVglobal (W.length - 1) (by omega)]
                  have heq : b.val + (W.length - 1) = e - 1 := by dsimp [e]; omega
                  rw [heq]
              have hElenLocal : E.length = v := hElen
              have hHlenLocal : H.length = e := hHlen
              have hvLocal : v = H.length + Dword.length := by
                change e + seg.records.length = H.length + Dword.length
                omega
              have hDpos : 0 < Dword.length := by
                obtain ⟨tail, htail⟩ := hne
                rw [hD, htail, List.length_cons]
                omega
              have hrawNe : rawCalendar rate j.val Dword ≠ [] := by
                intro hnil
                have hlen := congrArg List.length hnil
                simp only [rawCalendar, List.length_map, List.length_nil] at hlen
                omega
              have htransport := replay_collection_transport (4 * rate.n)
                (rawCalendar rate j.val H) (rawCalendar rate j.val Dword) d hrawNe
              have hUe : U j.val e = QueueReplay.replay (4 * rate.n) (0, 0)
                  (rawCalendar rate j.val H) := by
                change QueueReplay.replay _ _ (rawCalendar rate j.val (E.take e)) = _
                rw [hEtake]
              rw [← hUe, ← hVe] at htransport
              have hUv : U j.val v = QueueReplay.replay (4 * rate.n) (0, 0)
                  (rawCalendar rate j.val H ++ rawCalendar rate j.val Dword) := by
                change QueueReplay.replay _ _ (rawCalendar rate j.val (E.take v)) = _
                rw [← hElenLocal, List.take_length]
                simp only [E, rawCalendar, List.map_append]
              have hprevWord : rawCalendar rate j.val (E.take (v - 1)) =
                  rawCalendar rate j.val H ++
                    (rawCalendar rate j.val Dword).take
                      ((rawCalendar rate j.val Dword).length - 1) := by
                have hvEq : v - 1 = H.length + (Dword.length - 1) := by omega
                change rawCalendar rate j.val ((H ++ Dword).take (v - 1)) = _
                rw [hvEq, take_through_append]
                simp only [rawCalendar, List.map_append, List.map_take, List.length_map]
              rcases htransport with ⟨hqueue, hlast, hscore⟩
              rw [← hUv] at hqueue hlast hscore
              have hlast' : CollectionKnownQueueContinuation.replayLastService
                  (4 * rate.n) (0, (V W.length).2) d (rawCalendar rate j.val Dword) =
                    (U j.val v).1 - (U j.val (v - 1)).1 := by
                change _ = _ - (QueueReplay.replay _ _
                  (rawCalendar rate j.val (E.take (v - 1)))).1
                rw [hprevWord]
                exact hlast
              exact ⟨by rw [hfinal.1, hVe, hd],
                by rw [hfinal.2.1, hqueue, hlast'],
                by rw [hfinal.2.2.1, ← hVe]; exact hscore⟩
            | _ => exact False.elim hcutF
        next hother => exact False.elim (hother r0 q0 beta hstate)
    | _ => exact False.elim hcut

/-- Every retained physical index is an index of the complete observation calendar. -/
theorem observation_bound
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (v : ℕ) (k : Fin v)
    (hv : v ≤ (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length) :
    k.val < (ReferenceCompleteNumericalBranchObservation.completeBranchObservation
      rate rewards C_star C_h z).length := by
  simpa only [ReferenceCompleteNumericalBranchObservation.completeBranchObservation,
    ReferenceCompleteNumericalBranchObservation.branchCalendar, List.length_map] using
      Nat.lt_of_lt_of_le k.isLt hv

/-- Extend the original corrected cell through its FIRST actual NEXT birth,
LIVE word and first retained collection, with known outside registers on that
same zero-origin calendar. Horizon, dagger and non-later branches remain explicit. -/
theorem firstCell_next_calendar_word_join
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : z ∈ ReferenceFirstCollectionCorrectedSliceNumericalPrefix.correctedCell
      rate rewards C_star C_h u t) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    let b := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex rate rewards C_star C_h z
    let Omega := ReferenceCompleteNumericalBranchObservation.completeBranchObservation
      rate rewards C_star C_h z
    ∃ (L : List (RecordedQueueRun.RoundInput p.K)) (c : RecordedQueueRun.RoundInput p.K)
      (birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)),
      (ReferenceFirstCollectionCurrentRetainedGate.pastCells? rate rewards C_star C_h t z = some L ∧
      ReferenceFirstCollectionCurrentNumericalCell.currentCell rate rewards C_star C_h t z = some c ∧
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
        rate rewards C_star C_h (t.val + 1) z = some (L ++ [c]) ∧
      L.length = b ∧ s + b = t.val ∧ R[b]? = some birth ∧
      birth.input.time = t ∧ birth.input.rows = z.1.2 ∧
      birth.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p z ∧
      birth.input.rewards = rewards ∧ c.enabled = true ∧
      ReferenceLaterLiveNumericalReadout.laterLiveReadout s birth = some c ∧
      ReferenceFirstCollectionCurrentRetainedGate.cell0 rate birth = some c) ∧
      (birth.output.next.coordinator = .dagger ∨
        ∃ (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
          (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
          (base : Fin (p.m - 1) → ℕ), birth.output.next.coordinator = .live r q base) ∧
      ∀ (rout : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
        (qout : CoordinatorLiveServiceFinish.OwnedRegisters rout)
        (beta : Fin (p.m - 1) → ℕ),
        birth.output.next.coordinator = .live rout qout beta →
        rout.payload.sigma = t ∧
        ∀ _hq : t.val + 1 < p.T,
        ∃ (hk : b + 1 < R.length)
          (hstate : R[b + 1].input.state.coordinator = .live rout qout beta)
          (hlater : s < rout.payload.sigma.val),
          let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
            rate rewards C_star C_h z (b + 1)
          let B := ReferenceCompleteLaterLiveComplementPrefixReplay.prefixCells
            rewards C_star C_h z ⟨b + 1, hk⟩ rout qout beta hstate hlater
          let e := b + 1 + W.length
          let A := (L ++ [c]) ++ B
          (B.length = W.length ∧ e ≤ R.length ∧
          t.val + 1 + W.length ≤ p.T ∧ A.length = e ∧
          s + e = t.val + 1 + W.length ∧
          ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
            rate rewards C_star C_h (s + e) z = some A) ∧
          ∃ (rE : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
            (qE : CoordinatorLiveServiceFinish.OwnedRegisters rE),
            rE.payload = rout.payload ∧
            (∀ he : e < R.length, R[e].input.state.coordinator = .live rE qE beta) ∧
            (e = R.length ∨
              ∃ (he : e < R.length) (seg : Segment rate) (I : Initializer p)
                (l0 : Ledger rate),
                (segmentAt R e = some seg ∧ seg.entry = R[e] ∧
                seg.context.payload = rout.payload ∧ seg.context.preLedger = l0 ∧
                seg.context.initializer = some I ∧
                I = cutoffInitializer (liveRegistersAt rE R[e].input.time)
                  (liveOwnedAt rE qE R[e].input.time) beta R[e].input.time ∧
                I.checkedStart rate = .success l0 ∧
                I.assignment.arm = rout.payload.assignment.assigned ∧
                I.sigma = t.val + 1 ∧ I.cutoff = s + e + 1 ∧
                I.cutoff = FollowerCutoffScan.firstCutoff p rate.eta.val rout.payload.sigma
                  (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
                    (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z))) ∧
                I.freezeAt = rE.gridBoundary ∧ I.base = beta ∧
                ReferenceCollectionPhaseHistory.cutoffChosen seg.entry.input = true ∧
                (∃ during, seg.records = seg.entry :: during) ∧
                seg.records ++ seg.remaining = R.drop e) ∧
                let q := e + seg.records.length
                ∃ (dCells : List (RecordedQueueRun.RoundInput p.K)),
                  dCells.length = seg.records.length ∧
                  let G := ((L ++ [c]) ++ B) ++ dCells
                  ∃ (hG : G.length = q) (hq : q ≤ R.length),
                    s + q ≤ p.T ∧
                    ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
                      rate rewards C_star C_h (s + q) z = some G ∧
                        (∀ k : Fin q,
                          let r := R[k.val]'(Nat.lt_of_lt_of_le k.isLt hq)
                          let cell := G[k.val]'(by omega)
                          ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r = some cell ∧
                          r.input.time.val = s + k.val ∧
                          (Omega[k.val]'(by
                            simpa only [Omega, ReferenceCompleteNumericalBranchObservation.completeBranchObservation,
                              ReferenceCompleteNumericalBranchObservation.branchCalendar,
                              List.length_map, R] using
                                (Nat.lt_of_lt_of_le k.isLt hq))).1 = r.input.time ∧
                          ((Omega[k.val]'(by
                            simpa only [Omega, ReferenceCompleteNumericalBranchObservation.completeBranchObservation,
                              ReferenceCompleteNumericalBranchObservation.branchCalendar,
                              List.length_map, R] using
                                (Nat.lt_of_lt_of_le k.isLt hq))).2.2).map (Sum.elim id id) =
                            some (ReferenceCompleteNumericalBranchObservation.encodeNumerical cell)) ∧
                    let raw := fun (a : Fin p.K)
                        (C : List (RecordedQueueRun.RoundInput p.K)) =>
                      C.map (fun cell => (cell.enabled,
                        quantizedArrival
                          (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell a))
                    let U := fun (a : Fin p.K) (h : ℕ) =>
                      QueueReplay.replay (4 * rate.n) (0, 0) (raw a (G.take h))
                    ∃ saved,
                      (endpointState seg.entry.input.state seg.records).coordinator =
                        .collection seg.context.payload seg.final saved ∧
                      seg.final.cursor = s + q + 1 ∧
                      (q = R.length ∨
                        ∃ (hv : q < R.length),
                          R[q].input.state = endpointState seg.entry.input.state seg.records ∧
                          R[q].input.state.coordinator =
                            .collection seg.context.payload seg.final saved ∧
                          R[q].input.time.val = s + q ∧ R.drop q = seg.remaining ∧
                          (ReferenceCollectionPhaseHistory.laterChosen R[q].input = false ∨
                            ReferenceCollectionPhaseHistory.laterChosen R[q].input = true ∧
                            seg.final.pending = ∅ ∧
                            (∀ i : Fin (p.m - 1),
                              ∃ (ki : Fin R.length)
                                (V : ReferenceCollectionPhaseHistory.UpRecord p rate),
                                e ≤ ki.val ∧ ki.val < q ∧ R[ki.val] ∈ seg.records ∧
                                ReferenceCollectionPhaseHistory.AcceptedUp R[ki.val].input i V ∧
                                V.val.sigma = seg.final.sigma) ∧
                            let x := R[q].input
                            ∃ (uNext : Fin p.T), uNext.val + 1 = seg.final.cutoff ∧
                              let clock := collectionClock seg.context.payload seg.final saved uNext
                              let input := collectionInput x seg.context.payload seg.final clock uNext
                              ∃ (core : CollectionCoreValid input)
                                (started : StartRoundResult p)
                                (hstart : startRound p rate.eta.val x.time input.clock
                                  seg.final.pending = .ok started)
                                (instruction : AssignmentStartInstruction p)
                                (hassignment : started.assignmentStart = some instruction),
                                instruction.time = x.time ∧
                                instruction.kind =
                                  (if x.time.val + 1 < seg.final.freezeAt then .corrected else .renewal) ∧
                                let operation := collectionOperationLedger input core.payload_n_eq
                                ∃ (consistent : LocalConsistency seg.context.payload operation)
                                  (output : SuccessfulStart seg.context.payload operation instruction x.row)
                                  (hlocal : output.localConsistency = consistent),
                                  laterAssignmentStart seg.context.payload operation instruction x.row
                                    consistent = LaterAssignmentStartOperation.Result.success
                                      output hlocal ∧
                                  ∃ (clockData : LaterStartRoundEvidence output)
                                    (installation : LaterInstallation output clockData)
                                    (selected : ArmSelection installation.registers.payload started
                                      instruction.time installation.registers.complementWeights x.row),
                                    (installation = installLater output clockData ∧
                                    clockData.result = started ∧
                                    dispatchCollection input = .laterChosen core consistent started
                                      hstart instruction hassignment output hlocal clockData
                                      installation selected ∧
                                    R[q].output.preparation.coordinator =
                                      .collection seg.context.payload seg.final clock uNext
                                        (.laterChosen core consistent started hstart instruction
                                          hassignment output hlocal clockData installation selected) ∧
                                    x.rows = z.1.2 ∧
                                    x.selected = ActualInitializationPhysicalStep.selectedRowIndex p z ∧
                                    x.rewards = rewards ∧
                                    installation.registers.payload = output.payload ∧
                                    installation.assignmentVector = output.assignmentVector ∧
                                    output.assignmentVector = ownAssignmentVector x.row x.time ∧
                                    installation.reconstruction = output.reconstruction ∧
                                    (∀ a, AssignmentScoreReconstruction.currentWeight
                                        output.reconstruction a =
                                          (1 + 1 / (D p : ℝ)) ^
                                            AssignmentScoreReconstruction.sourceScore
                                              output.reconstruction a ∧
                                      AssignmentScoreReconstruction.cutoffWeight
                                        output.reconstruction a =
                                          (1 + 1 / (D p : ℝ)) ^
                                            (output.reconstruction.registers.cutoff a).score) ∧
                                    (∃ selection : Selection x,
                                      R[q].output.preparation.coordinator.selection = some selection ∧
                                      selection.view.payload = installation.registers.payload ∧
                                      selection.view.cutoff = none ∧
                                      CoordinatorLocalArmChoice.assignmentIsLive
                                        selection.view.payload selection.view.cutoff x.time) ∧
                                    (∀ a : Fin p.K,
                                      AssignmentScoreReconstruction.sourceScore
                                        output.reconstruction a =
                                          (QueueReplay.replay (4 * rate.n) (0, 0)
                                            (raw a G)).1 ∧
                                      AssignmentScoreReconstruction.initialQueue
                                        output.reconstruction a =
                                          (QueueReplay.replay (4 * rate.n) (0, 0)
                                            (raw a G)).2 ∧
                                      installation.registers.payload.queues a =
                                        (QueueReplay.replay (4 * rate.n) (0, 0)
                                          (raw a G)).2 ∧
                                      (∀ i, installation.registers.payload.assignment.assigned i = a →
                                        installation.retainedBaseScore i =
                                            (QueueReplay.replay (4 * rate.n) (0, 0)
                                              (raw a G)).1 ∧
                                          (installation.registers.payload.downRecord i).val.q =
                                            (QueueReplay.replay (4 * rate.n) (0, 0)
                                              (raw a G)).2) ∧
                                      (∀ j : FastArm installation.registers.payload.slowSet,
                                        j.val = a →
                                          installation.registers.complementScores j =
                                              (QueueReplay.replay (4 * rate.n) (0, 0)
                                                (raw a G)).1 ∧
                                            installation.ownedRegisters.queue j =
                                              (QueueReplay.replay (4 * rate.n) (0, 0)
                                                (raw a G)).2 ∧
                                            installation.ownedRegisters.previousService j =
                                              (U a q).1 - (U a (q - 1)).1))) ∧
                                    let x := R[q].input
                                    ∃ (birthSelection : Selection x)
                                      (cNext : RecordedQueueRun.RoundInput p.K)
                                      (_ho : ReferenceLaterLiveNumericalReadout.preparedOrdinary
                                        (R[q]))
                                      (cell : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell
                                        (R[q])),
                                      (R[q].output.preparation.coordinator.selection =
                                        some birthSelection ∧
                                      birthSelection.view.payload = installation.registers.payload ∧
                                      birthSelection.view.cutoff = none ∧
                                      CoordinatorLocalArmChoice.assignmentIsLive
                                        birthSelection.view.payload birthSelection.view.cutoff x.time ∧
                                      ReferenceLaterLiveNumericalReadout.laterLiveReadout s (R[q]) =
                                        some cNext ∧
                                      cell.input = cNext ∧ cell.selected = birthSelection ∧
                                      cNext.enabled = true ∧
                                      cNext.rate = installation.registers.payload.rate ∧
                                      cNext.reward =
                                        (fun arm => ((rewards x.time arm).val : ℝ) / (D p : ℝ)) ∧
                                      x.rows = z.1.2 ∧
                                      x.selected = ActualInitializationPhysicalStep.selectedRowIndex p z ∧
                                      x.rewards = rewards) ∧
                                      ∃ (o : CoordinatorRecordingOperation.Output p)
                                        (serviced : CoordinatorLiveServiceFinish.ServicedRegisters
                                          installation.registers installation.ownedRegisters)
                                        (pending : Finset (Fin (p.m - 1)))
                                        (finished : FinishRoundResult p),
                                        R[q].output.coordinator.recording = some o ∧
                                        serviced.recording = o ∧
                                        (∀ j : FastArm installation.registers.payload.slowSet,
                                          serviced.arrival j =
                                            RecordedQueueRun.quantizedArrival
                                              (ReferenceFirstLaunchNumericalCell.queueParameters rate)
                                              cNext j.val ∧
                                          (serviced.score j, serviced.queue j) =
                                            QueueReplay.transition (4 * rate.n)
                                              (AssignmentScoreReconstruction.sourceScore
                                                output.reconstruction j.val,
                                               AssignmentScoreReconstruction.initialQueue
                                                output.reconstruction j.val)
                                              (true, RecordedQueueRun.quantizedArrival
                                                (ReferenceFirstLaunchNumericalCell.queueParameters rate)
                                                cNext j.val) ∧
                                          serviced.previousService j = serviced.score j -
                                            AssignmentScoreReconstruction.sourceScore
                                              output.reconstruction j.val) ∧
                                        finishRound p rate.eta.val x.time started.clock pending x.row =
                                          .ok finished ∧
                                        let birthRegisters :
                                            CoordinatorLiveChoiceRecorderStep.Registers p rate.eta :=
                                          { payload := installation.registers.payload
                                            priorClock := finished.clock
                                            pendingAtChoice := finished.pending
                                            time := x.time
                                            gridBoundary := finished.clock.g
                                            complementScores := serviced.score }
                                        let birthOwned :
                                            CoordinatorLiveServiceFinish.OwnedRegisters birthRegisters :=
                                          { queue := serviced.queue
                                            previousService := serviced.previousService }
                                        R[q].output.next.coordinator =
                                          .live birthRegisters birthOwned installation.retainedBaseScore ∧
                                        (∀ j : FastArm installation.registers.payload.slowSet,
                                          (serviced.score j, serviced.queue j) =
                                            QueueReplay.replay (4 * rate.n) (0, 0)
                                              (raw j.val G ++ [(true,
                                                RecordedQueueRun.quantizedArrival
                                                  (ReferenceFirstLaunchNumericalCell.queueParameters rate)
                                                  cNext j.val)]) ∧
                                          serviced.previousService j = serviced.score j -
                                            (QueueReplay.replay (4 * rate.n) (0, 0)
                                              (raw j.val G)).1) ∧
                                        let P := G ++ [cNext]
                                        ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
                                          rate rewards C_star C_h (s + (q + 1)) z = some P ∧
                                          P.length = q + 1 ∧ P.take q = G ∧
                                          (∀ (hV : (q + 1) ≤ R.length) (hE : P.length = (q + 1)) (k : Fin (q + 1)),
                                            let r := R[k.val]'(Nat.lt_of_lt_of_le k.isLt hV)
                                            let c := P[k.val]'(Nat.lt_of_lt_of_le k.isLt (Nat.le_of_eq hE.symm))
                                            ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r = some c ∧
                                            r.input.time.val = s + k.val ∧
                                            (Omega[k.val]'(observation_bound rate rewards C_star C_h z _ k hV)).1 = r.input.time ∧
                                            ((Omega[k.val]'(observation_bound rate rewards C_star C_h z _ k hV)).2.2).map (Sum.elim id id) =
                                              some (ReferenceCompleteNumericalBranchObservation.encodeNumerical c)) ∧
                                          (∀ c ∈ P, c.enabled = false → c.recordedArm = none ∧ ∀ a,
                                            quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a = 0) ∧
                                          (∀ a : Fin p.K,
                                            let r := R[q]
                                              ∃ cell : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell r,
                                                cell.input = cNext ∧ cell.selected = birthSelection ∧
                                                (∃! owner : Fin p.m, SnapshotRecordingKernel.owns p (.live cell.selected.view.payload.assignment
                                                  (ReferenceActiveDataOwnership.choiceSnapshot cell.selected cell.states)) owner a) ∧
                                                ((a ∉ cell.selected.view.payload.slowSet.1 ∧
                                                  ∃ out, r.output.coordinator.recording = some out ∧
                                                    ReferenceCoordinatorRecorderCallTrace.coordinatorRaw
                                                        (ReferenceActiveHorizonMeasurability.roundRecordCode r) a =
                                                      some (RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) cNext a)) ∨
                                                  ∃ i : Fin (p.m - 1), cell.selected.view.payload.assignment.assigned i = a ∧
                                                    (∀ j, cell.selected.view.payload.assignment.assigned j = a → j = i) ∧
                                                    (if (cell.states i).status = .unoccupied then
                                                      ReferenceContinuingRecordingPhysicalReward.actualCurrentSavedContribution r cell.selected.view.payload i
                                                    else ActiveFollowerQueueOperation.rawArrival rate.eta i r.input.row r.input.time
                                                      (cell.selected.view.payload.downRecord i) (r.output.ownEntries (PublicDiscreteDraws.followerPlayer p.two_le_m i)).2) =
                                                      RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) cNext a)) ∧
                                          (q + 1 = R.length ∨
                                            ∃ (hnext : q + 1 < R.length)
                                              (hstateNext : R[q + 1].input.state.coordinator =
                                                .live birthRegisters birthOwned installation.retainedBaseScore)
                                              (hlaterNext : s < birthRegisters.payload.sigma.val),
                                              let WNext := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
                                                rate rewards C_star C_h z (q + 1)
                                              let BNext := ReferenceCompleteLaterLiveComplementPrefixReplay.prefixCells
                                                rewards C_star C_h z ⟨q + 1, hnext⟩ birthRegisters birthOwned installation.retainedBaseScore hstateNext hlaterNext
                                              let e2 := (q + 1) + WNext.length
                                              let A2 := P ++ BNext
                                              (∀ a : Fin p.K,
                                                rawCalendar rate a A2 = rawCalendar rate a G ++
                                                  [(true, quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) cNext a)] ++
                                                    rawCalendar rate a BNext) ∧
                                              P.length = (q + 1) ∧ BNext.length = WNext.length ∧ e2 ≤ R.length ∧ s + e2 ≤ p.T ∧
                                              A2.length = e2 ∧ A2.take q = G ∧
                                              (∀ h, q ≤ h → h ≤ e2 →
                                                ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
                                                  rate rewards C_star C_h (s + h) z = some (A2.take h)) ∧
                                              (∀ i : Fin WNext.length,
                                                let k : Fin R.length := ⟨(q + 1) + i.val, by
                                                  have hbound := ReferenceCompleteLaterLiveComplementPrefixReplay.prefix_length_le
                                                    rewards C_star C_h z ⟨q + 1, hnext⟩
                                                  change (q + 1) + WNext.length ≤ R.length at hbound
                                                  omega⟩
                                                let r := R.get k
                                                let c := BNext[i.val]'(by
                                                  rw [ReferenceCompleteLaterLiveComplementPrefixReplay.prefixCells_length
                                                    rewards C_star C_h z ⟨q + 1, hnext⟩ birthRegisters birthOwned installation.retainedBaseScore hstateNext hlaterNext]
                                                  exact i.isLt)
                                                ∀ a : Fin p.K,
                                                ∃ cell : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell r,
                                                  cell.input = c ∧
                                                  (∃! owner : Fin p.m, SnapshotRecordingKernel.owns p (.live cell.selected.view.payload.assignment
                                                    (ReferenceActiveDataOwnership.choiceSnapshot cell.selected cell.states)) owner a) ∧
                                                  ((a ∉ cell.selected.view.payload.slowSet.1 ∧
                                                    ∃ out, r.output.coordinator.recording = some out ∧
                                                      ReferenceCoordinatorRecorderCallTrace.coordinatorRaw
                                                          (ReferenceActiveHorizonMeasurability.roundRecordCode r) a =
                                                        some (RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a)) ∨
                                                    ∃ i : Fin (p.m - 1), cell.selected.view.payload.assignment.assigned i = a ∧
                                                      (∀ j, cell.selected.view.payload.assignment.assigned j = a → j = i) ∧
                                                      (if (cell.states i).status = .unoccupied then
                                                        ReferenceContinuingRecordingPhysicalReward.actualCurrentSavedContribution r cell.selected.view.payload i
                                                      else ActiveFollowerQueueOperation.rawArrival rate.eta i r.input.row r.input.time
                                                        (cell.selected.view.payload.downRecord i) (r.output.ownEntries (PublicDiscreteDraws.followerPlayer p.two_le_m i)).2) =
                                                        RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a)) ∧
                                              (∀ (hV : e2 ≤ R.length) (hE : A2.length = e2) (k : Fin e2),
                                                let r := R[k.val]'(Nat.lt_of_lt_of_le k.isLt hV)
                                                let c := A2[k.val]'(Nat.lt_of_lt_of_le k.isLt (Nat.le_of_eq hE.symm))
                                                ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r = some c ∧
                                                r.input.time.val = s + k.val ∧
                                                (Omega[k.val]'(observation_bound rate rewards C_star C_h z _ k hV)).1 = r.input.time ∧
                                                ((Omega[k.val]'(observation_bound rate rewards C_star C_h z _ k hV)).2.2).map (Sum.elim id id) =
                                                  some (ReferenceCompleteNumericalBranchObservation.encodeNumerical c)) ∧
                                              (∀ c ∈ A2, c.enabled = false → c.recordedArm = none ∧ ∀ a,
                                                quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a = 0) ∧
                                              (e2 = R.length ∨
                                                ∃ (he2 : e2 < R.length)
                                                  (rE2 : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
                                                  (qE2 : CoordinatorLiveServiceFinish.OwnedRegisters rE2)
                                                  (seg2 : Segment rate) (I2 : Initializer p) (l02 : Ledger rate)
                                                  (DNext : List (RecordedQueueRun.RoundInput p.K)),
                                                  rE2.payload = birthRegisters.payload ∧ R[e2].input.state.coordinator = .live rE2 qE2 installation.retainedBaseScore ∧
                                                  segmentAt R e2 = some seg2 ∧ seg2.entry = R[e2] ∧
                                                  seg2.context.payload = birthRegisters.payload ∧ seg2.context.preLedger = l02 ∧
                                                  seg2.context.initializer = some I2 ∧
                                                  I2 = cutoffInitializer (liveRegistersAt rE2 R[e2].input.time)
                                                    (liveOwnedAt rE2 qE2 R[e2].input.time) installation.retainedBaseScore R[e2].input.time ∧
                                                  I2.checkedStart rate = .success l02 ∧
                                                  I2.assignment.arm = birthRegisters.payload.assignment.assigned ∧
                                                  I2.sigma = birthRegisters.payload.sigma.val + 1 ∧ I2.cutoff = s + e2 + 1 ∧
                                                  I2.cutoff = FollowerCutoffScan.firstCutoff p rate.eta.val birthRegisters.payload.sigma
                                                    (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
                                                      (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z))) ∧
                                                  I2.freezeAt = rE2.gridBoundary ∧ I2.base = installation.retainedBaseScore ∧
                                                  ReferenceCollectionPhaseHistory.cutoffChosen seg2.entry.input = true ∧
                                                  (∃ tail, seg2.records = seg2.entry :: tail) ∧
                                                  seg2.records ++ seg2.remaining = R.drop e2 ∧ seg2.exit = exitOf seg2.remaining ∧
                                                  CollectionCheckedExecution.startAndRunChecked p rate.eta.val rate.eta.property
                                                    (ReferenceUpReception.sourceCap_forLedger rate) rate.n rate.n_scale
                                                    I2.assignment I2.sigma I2.cutoff I2.freezeAt I2.base I2.outside seg2.inputs =
                                                      .success ⟨l02, seg2.accepted, seg2.final⟩ ∧
                                                  DNext.length = seg2.records.length ∧
                                                  seg2.records.map (laterCollectionReadout s) = DNext.map some ∧
                                                  (∀ a, CollectionKnownQueueContinuation.inputQueueRecords l02 a seg2.inputs =
                                                      seg2.records.map (physicalQueueRecord l02 a) ∧
                                                    seg2.records.map (physicalQueueRecord l02 a) = rawCalendar rate a DNext) ∧
                                                  let G2 := A2 ++ DNext
                                                  let v2 := e2 + seg2.records.length
                                                  G2.length = v2 ∧ G2.take e2 = A2 ∧ G2.take q = G ∧
                                                  v2 ≤ R.length ∧ s + v2 ≤ p.T ∧ R.take v2 = R.take e2 ++ seg2.records ∧
                                                  (∀ h, q ≤ h → h ≤ v2 →
                                                    ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
                                                      rate rewards C_star C_h (s + h) z = some (G2.take h)) ∧
                                                  (∀ (hV : v2 ≤ R.length) (hE : G2.length = v2) (k : Fin v2),
                                                    let r := R[k.val]'(Nat.lt_of_lt_of_le k.isLt hV)
                                                    let c := G2[k.val]'(Nat.lt_of_lt_of_le k.isLt (Nat.le_of_eq hE.symm))
                                                    ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r = some c ∧
                                                    r.input.time.val = s + k.val ∧
                                                    (Omega[k.val]'(observation_bound rate rewards C_star C_h z _ k hV)).1 = r.input.time ∧
                                                    ((Omega[k.val]'(observation_bound rate rewards C_star C_h z _ k hV)).2.2).map (Sum.elim id id) =
                                                      some (ReferenceCompleteNumericalBranchObservation.encodeNumerical c)) ∧
                                                  (∀ i : Fin BNext.length, BNext[i.val].enabled = true) ∧
                                                  (∀ j : Fin DNext.length,
                                                    DNext[j.val].enabled = false → DNext[j.val].recordedArm = none ∧ ∀ a,
                                                      RecordedQueueRun.quantizedArrival
                                                        (ReferenceFirstLaunchNumericalCell.queueParameters rate) DNext[j.val] a = 0) ∧
                                                  (∀ c ∈ G2, c.enabled = false → c.recordedArm = none ∧ ∀ a,
                                                    quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a = 0) ∧
                                                  ∀ j : FastArm birthRegisters.payload.slowSet,
                                                    seg2.final.cutoffRegisters j.val =
                                                      some ⟨(calendarReplay rate G2 j.val e2).1, (calendarReplay rate G2 j.val e2).2, (calendarReplay rate G2 j.val e2).1 - (calendarReplay rate G2 j.val (e2 - 1)).1⟩ ∧
                                                    seg2.final.currentRegisters j.val =
                                                      some ⟨(calendarReplay rate G2 j.val v2).2, (calendarReplay rate G2 j.val v2).1 - (calendarReplay rate G2 j.val (v2 - 1)).1⟩ ∧
                                                    (calendarReplay rate G2 j.val e2).1 + seg2.final.increment j.val = (calendarReplay rate G2 j.val v2).1))))) := by
  classical
  intro R s b Omega
  obtain ⟨L, c, birth, hL, hc, hprefix, hLb, hdate, hb, hbirthTime,
    hbirthRows, hbirthSelected, hbirthRewards, henabled, hread, hcell0,
    hmode, hcont⟩ :=
    ReferenceFirstCorrectedNextOutsideCalendarReplay.firstCell_next_outside_calendar_seed
      rate rewards C_star C_h u t z hz
  refine ⟨L, c, birth, ⟨hL, hc, hprefix, hLb, hdate, hb, hbirthTime,
    hbirthRows, hbirthSelected, hbirthRewards, henabled, hread, hcell0⟩,
    hmode, ?_⟩
  intro rout qout beta hlive
  obtain ⟨hsigma, hcont⟩ := hcont rout qout beta hlive
  refine ⟨hsigma, ?_⟩
  intro hq
  obtain ⟨hk, hstate, hlater, hBlen, heR, heT, hAlen, hAdate, hprefixA,
    rE, qE, hp, hstateE, hexit⟩ := hcont hq
  let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
    rate rewards C_star C_h z (b + 1)
  let B := ReferenceCompleteLaterLiveComplementPrefixReplay.prefixCells
    rewards C_star C_h z ⟨b + 1, hk⟩ rout qout beta hstate hlater
  let e := b + 1 + W.length
  let A := (L ++ [c]) ++ B
  refine ⟨hk, hstate, hlater, ⟨hBlen, heR, heT, hAlen, hAdate, hprefixA⟩,
    rE, qE, hp, hstateE, ?_⟩
  rcases hexit with hhor | ⟨he, seg, I, l0, hsegment, hentry, hpay, hpre,
    hI, hIdef, hchecked, harm, hIsigma, hIcut, hIscan, hfreeze, hbase,
    hcutchosen, hDuring, hpartition, dCells, hD, hG, hqR, hT,
    hprefixG, hcoordinates, saved, hend, hcursor, hboundary⟩
  · exact Or.inl hhor
  · let q := e + seg.records.length
    let G := A ++ dCells
    refine Or.inr ⟨he, seg, I, l0, ⟨hsegment, hentry, hpay, hpre, hI,
      hIdef, hchecked, harm, hIsigma, hIcut, hIscan, hfreeze, hbase,
      hcutchosen, hDuring, hpartition⟩, dCells, hD, hG, hqR, hT,
      hprefixG, hcoordinates, saved, hend, hcursor, ?_⟩
    rcases hboundary with hterminal | ⟨hv, hstateQ, hcoordQ, htimeQ, hdropQ, hchoiceQ⟩
    · exact Or.inl hterminal
    · refine Or.inr ⟨hv, hstateQ, hcoordQ, htimeQ, hdropQ, ?_⟩
      rcases hchoiceQ with hnotLater | ⟨hlaterQ, hempty, haccepted,
        uNext, huNext, core, started, hstartNext, instruction, hassignment,
        htimeNext, hkind, consistent, output, hlocal, hcall, clockData,
        installation, selectedNext, hinstall, hresult, hdispatch,
        hpreparedNext, hrows, hselected, hrewards, hpayload, hvector,
        hownVector, hreconstruction, hweights, hselection, hvalues,
        birthSelection, cNext, ho, cell, hselectionS, hvpayloadS, hvcutoffS,
        hliveS, hreadout, hcell, hcellSelected, henabledN, hrate, hreward,
        hrowsS, hselectedS, hrewardsS, o, serviced, pending, finished,
        hrecord, hserviceRecord, hservice, hfinish, hnextLive, hbirthAll, hnext⟩
      · exact Or.inl hnotLater
      · refine Or.inr ⟨hlaterQ, hempty, haccepted, uNext, huNext, core,
          started, hstartNext, instruction, hassignment, htimeNext, hkind,
          consistent, output, hlocal, hcall, clockData, installation,
          selectedNext, ⟨hinstall, hresult, hdispatch, hpreparedNext, hrows,
          hselected, hrewards, hpayload, hvector, hownVector, hreconstruction,
          hweights, hselection, hvalues⟩, birthSelection, cNext, ho, cell,
          ⟨hselectionS, hvpayloadS, hvcutoffS, hliveS, hreadout, hcell,
          hcellSelected, henabledN, hrate, hreward, hrowsS, hselectedS,
          hrewardsS⟩, o, serviced, pending, finished, hrecord, hserviceRecord,
          hservice, hfinish, hnextLive, hbirthAll, ?_⟩
        let P := G ++ [cNext]
        have hGlen : G.length = q := hG
        have hPlen : P.length = q + 1 := by simp only [P, List.length_append,
          List.length_singleton, hGlen]
        have hPtake : P.take q = G := by
          change (G ++ [cNext]).take q = G
          rw [take_before_append _ _ _ (by omega), ← hGlen, List.take_length]
        have hcellNext : ReferenceFirstCollectionCurrentRetainedGate.cell0 rate R[q] =
            some cNext := live_cell0 rate s R[q] cNext hreadout
        have happ := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs_append_one
          rate rewards C_star C_h (s + q) z G hprefixG R[q] cNext
          (by change R[(s + q) - s]? = some R[q]
              rw [Nat.add_sub_cancel_left]
              exact List.getElem?_eq_getElem hv) hcellNext
        have hP : ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
            rate rewards C_star C_h (s + (q + 1)) z = some P := by
          simpa only [Nat.add_assoc] using happ
        have hPcoverage := calendar_coordinates (rate := rate) rewards C_star C_h z
          (q + 1) P hPlen (Nat.succ_le_of_lt hv) hP
        have hbirthRaw (a : Fin p.K) :=
          ReferenceLaterLiveNumericalReadout.laterLiveReadout_all_arm_numerical
            rate rewards C_star C_h z ⟨q, hv⟩ cNext
            (by simpa only [List.get_eq_getElem] using hreadout) a
        refine ⟨hP, hPlen, hPtake, (fun _ _ => hPcoverage.1), hPcoverage.2, ?_, ?_⟩
        · intro a
          obtain ⟨cellA, hinputA, hownerA, hrawA⟩ := hbirthRaw a
          exact ⟨cellA, hinputA,
            Option.some.inj (cellA.selection_actual.symm.trans hselectionS), hownerA, hrawA⟩
        · rcases hnext with hterminal | ⟨hnext, hstateNext, hlaterNext, _hrestNext⟩
          · exact Or.inl hterminal
          · let birthRegisters : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta :=
              { payload := installation.registers.payload
                priorClock := finished.clock
                pendingAtChoice := finished.pending
                time := R[q].input.time
                gridBoundary := finished.clock.g
                complementScores := serviced.score }
            let birthOwned : CoordinatorLiveServiceFinish.OwnedRegisters birthRegisters :=
              { queue := serviced.queue, previousService := serviced.previousService }
            have hseed (j : FastArm birthRegisters.payload.slowSet) :
                (birthRegisters.complementScores j, birthOwned.queue j) =
                  QueueReplay.replay (4 * rate.n) (0, 0) (rawCalendar rate j.val P) := by
              have hrawP : rawCalendar rate j.val P = rawCalendar rate j.val G ++
                  [(true, quantizedArrival
                    (ReferenceFirstLaunchNumericalCell.queueParameters rate) cNext j.val)] := by
                simp only [P, rawCalendar, List.map_append, List.map_cons, List.map_nil, henabledN]
              rw [hrawP]
              exact (hbirthAll j).1
            have hprevious (j : FastArm birthRegisters.payload.slowSet) :
                birthOwned.previousService j =
                  (QueueReplay.replay (4 * rate.n) (0, 0) (rawCalendar rate j.val P)).1 -
                  (QueueReplay.replay (4 * rate.n) (0, 0)
                    (rawCalendar rate j.val (P.take ((q + 1) - 1)))).1 := by
              rw [Nat.add_sub_cancel, hPtake]
              exact (hbirthAll j).2.trans
                (congrArg (fun score => score -
                  (QueueReplay.replay (4 * rate.n) (0, 0) (rawCalendar rate j.val G)).1)
                  (congrArg Prod.fst (hseed j)))
            obtain ⟨hPlenN, hBlenN, heRN, heTN, hAlenN, hAtakeN, hprefixN, hrawSlotsN,
              hcoordsN, hdisabledN, hexitN⟩ := initialized_live_word rate rewards C_star C_h z
                ⟨q + 1, hnext⟩ birthRegisters birthOwned installation.retainedBaseScore
                hstateNext hlaterNext P hP hseed hprevious
            let WNext := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
              rate rewards C_star C_h z (q + 1)
            let BNext := ReferenceCompleteLaterLiveComplementPrefixReplay.prefixCells
              rewards C_star C_h z ⟨q + 1, hnext⟩ birthRegisters birthOwned
                installation.retainedBaseScore hstateNext hlaterNext
            let e2 := q + 1 + WNext.length
            let A2 := P ++ BNext
            have hAtake : A2.take q = G := take_birth_prefix A2 G cNext q hGlen hAtakeN
            have hprefixA2 := include_birth_boundary rate rewards C_star C_h z s q e2
              A2 G hAtake hprefixG hprefixN
            refine Or.inr ⟨hnext, hstateNext, hlaterNext, ?_, hPlenN, hBlenN,
              heRN, heTN, hAlenN, hAtake, hprefixA2, hrawSlotsN, hcoordsN, hdisabledN, ?_⟩
            · intro a
              change rawCalendar rate a ((G ++ [cNext]) ++ BNext) =
                (rawCalendar rate a G ++ [(true, quantizedArrival
                  (ReferenceFirstLaunchNumericalCell.queueParameters rate) cNext a)]) ++
                    rawCalendar rate a BNext
              simpa only [List.append_assoc] using
                rawCalendar_append_birth rate a G cNext BNext henabledN
            · rcases hexitN with hterminal | ⟨he2, rE2, qE2, seg2, I2, l02,
                DNext, hp2, hin2, hat2, hentry2, hpay2, hledger2, hI2, hIeq2,
                hchecked2, harm2, hsigma2, hcutoff2, hscan2, hfreeze2, hbase2,
                hchosen2, hne2, hpart2, hexit2, hfold2, hD2, hmap2, hsync2,
                hElen2, hEtake2, hEtakeP2, hV2, hVtime2, hRtake2, hprefixAll2,
                hcoords2, henabled2, hdisabled2, hcanonical2, hknown2⟩
              · exact Or.inl hterminal
              · let G2 := A2 ++ DNext
                let v2 := e2 + seg2.records.length
                have hG2take : G2.take q = G :=
                  take_birth_prefix G2 G cNext q hGlen hEtakeP2
                have hprefixG2 := include_birth_boundary rate rewards C_star C_h z s q v2
                  G2 G hG2take hprefixG hprefixAll2
                exact Or.inr ⟨he2, rE2, qE2, seg2, I2, l02, DNext, hp2,
                  hin2, hat2, hentry2, hpay2, hledger2, hI2, hIeq2, hchecked2,
                  harm2, hsigma2, hcutoff2, hscan2, hfreeze2, hbase2, hchosen2,
                  hne2, hpart2, hexit2, hfold2, hD2, hmap2, hsync2, hElen2,
                  hEtake2, hG2take, hV2, hVtime2, hRtake2, hprefixG2, hcoords2,
                  henabled2, hdisabled2, hcanonical2, hknown2⟩
end Bandits.Support.ReferenceFirstCorrectedNextCalendarWordJoin

end
