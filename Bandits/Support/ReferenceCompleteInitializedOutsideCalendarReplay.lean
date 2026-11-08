/-
Copyright (c) 2026 The Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCorrectedNextCalendarWordJoin

import Mathlib.Tactic

/-!
# Initialized outside calendar replay through the actual cutoff

Sources: ZIP4 `appendix_a_local_protocol.tex:28-64`,
`06_interruptions.tex:40-100,192-233,246-299`, and
`04_slow_fast_learner.tex:157-174`.

This internal conditional alignment theorem keeps the original complete run,
its canonical later-LIVE word, and the same first retained collection segment.
The only numerical inputs are literal score, queue, and zero-live-length
previous-service equations on the outside fast arms.
-/

@[expose] public section
noncomputable section

open Bandits.Support
open ConstructorDimensions ReferenceActivePhysicalStep ReferenceActivePhysicalHorizon
open CoordinatorRoundDispatch CanonicalFastSampling RecordedQueueRun
open ReferenceCollectionSegmentExtraction
open ReferenceLaterCollectionArrivalReadout ReferenceCollectionRawBufferHistory
open ReferenceFirstCorrectedNextCalendarWordJoin

namespace Bandits.Support.ReferenceCompleteInitializedOutsideCalendarReplay

variable {p : ConstructorDimensions.Parameters}

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

/-- Align the initialized outside-arm registers with the same complete
original-calendar word through the actual later-LIVE cutoff segment. The
previous-service input is required only when the actual later-LIVE prefix is
empty. -/
public theorem complete_later_live_initialized_outside_calendar_replay
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
        ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay
          rate P j.val P.length)
    (hprevious :
      (ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
        rate rewards C_star C_h z b.val).length = 0 →
      ∀ j : FastArm r0.payload.slowSet,
        q0.previousService j =
          (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay
            rate P j.val P.length).1 -
          (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay
            rate P j.val (b.val - 1)).1) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
      rate rewards C_star C_h z b.val
    let B := ReferenceCompleteLaterLiveComplementPrefixReplay.prefixCells
      rewards C_star C_h z b r0 q0 beta hstate hlater
    let e := b.val + W.length
    let H := P ++ B
    let U0 := fun (a : Fin p.K) (h : ℕ) =>
      QueueReplay.replay (4 * rate.n) (0, 0) (rawCalendar rate a (H.take h))
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
    ∃ (rE : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
      (qE : CoordinatorLiveServiceFinish.OwnedRegisters rE),
      ∃ (hp : rE.payload = r0.payload),
      (∀ hpos : 0 < W.length,
        (W[W.length - 1]'(by omega)).output.next.coordinator = .live rE qE beta) ∧
      (∀ he : e < R.length, (R[e]'he).input.state.coordinator = .live rE qE beta) ∧
      (∀ j : FastArm r0.payload.slowSet,
        let jE : FastArm rE.payload.slowSet :=
          ⟨j.val, by simpa only [hp] using j.property⟩
        (rE.complementScores jE, qE.queue jE) = U0 j.val e ∧
        qE.previousService jE = (U0 j.val e).1 - (U0 j.val (e - 1)).1) ∧
      (e = R.length ∨
      ∃ (he : e < R.length)
        (seg : Segment rate) (I : Initializer p) (l0 : Ledger rate)
        (Dword : List (RecordedQueueRun.RoundInput p.K)),
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
  intro R s W B e H U0
  obtain ⟨hPlen, heR, heT, hHlen, hHtake, hprefix, hslots,
    rE, qE, hp, hlast, hin, hvalues, halt⟩ :=
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
  let V := fun (j : FastArm r0.payload.slowSet) (n : ℕ) =>
    QueueReplay.replay (4 * rate.n) (r0.complementScores j, q0.queue j)
      (rawCalendar rate j.val (B.take n))
  have hVglobal (j : FastArm r0.payload.slowSet) (n : ℕ) (hn : n ≤ W.length) :
      V j n = U0 j.val (b.val + n) := by
    change QueueReplay.replay (4 * rate.n) (r0.complementScores j, q0.queue j)
        (rawCalendar rate j.val (B.take n)) =
      QueueReplay.replay (4 * rate.n) (0, 0)
        (rawCalendar rate j.val (H.take (b.val + n)))
    have hseed' : (r0.complementScores j, q0.queue j) =
        QueueReplay.replay (4 * rate.n) (0, 0) (rawCalendar rate j.val P) := by
      simpa only [ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay,
        List.take_length] using hseed j
    rw [hseed', ← QueueReplay.replay_append]
    have htake : H.take (b.val + n) = P ++ B.take n := by
      change (P ++ B).take (b.val + n) = _
      rw [← hPlen]
      exact take_through_append P B n
    rw [htake]
    simp only [rawCalendar, List.map_append]
  have hEndpointValues : ∀ j : FastArm r0.payload.slowSet,
      let jE : FastArm rE.payload.slowSet :=
        ⟨j.val, by simpa only [hp] using j.property⟩
      (rE.complementScores jE, qE.queue jE) = U0 j.val e ∧
      qE.previousService jE = (U0 j.val e).1 - (U0 j.val (e - 1)).1 := by
    intro j
    let jE : FastArm rE.payload.slowSet := ⟨j.val, by simpa only [hp] using j.property⟩
    have hvaluesJ := hvalues j
    have hvaluesJ' :
        (rE.complementScores jE, qE.queue jE) = V j W.length ∧
        qE.previousService jE =
          if W.length = 0 then q0.previousService j
          else (V j W.length).1 - (V j (W.length - 1)).1 := by
      simpa only [V, ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar,
        ReferenceCompleteLaterLiveComplementPrefixReplay.prefixCells_length,
        List.take_length] using hvaluesJ
    refine ⟨?_, ?_⟩
    · calc
        (rE.complementScores jE, qE.queue jE) = V j W.length := hvaluesJ'.1
        _ = U0 j.val e := by simpa only [e] using hVglobal j W.length le_rfl
    · by_cases hzero : W.length = 0
      · have hBnil : B = [] := List.length_eq_zero_iff.mp (hBlen.trans hzero)
        have heq : e = b.val := by dsimp [e]; omega
        have hprevInput := hprevious (by simpa only [W] using hzero) j
        have hprevP : q0.previousService j =
            (QueueReplay.replay (4 * rate.n) (0, 0) (rawCalendar rate j.val P)).1 -
              (QueueReplay.replay (4 * rate.n) (0, 0)
                (rawCalendar rate j.val (P.take (b.val - 1)))).1 := by
          simpa only [ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay,
            List.take_length] using hprevInput
        have htakeP : H.take (e - 1) = P.take (b.val - 1) := by
          change (P ++ B).take (e - 1) = _
          rw [hBnil, heq]
          exact take_before_append P [] (b.val - 1) (by rw [hPlen]; omega)
        have hscoreEnd : (U0 j.val e).1 =
            (QueueReplay.replay (4 * rate.n) (0, 0) (rawCalendar rate j.val P)).1 := by
          have h := hVglobal j 0 (by omega)
          have hV0 : V j 0 = (r0.complementScores j, q0.queue j) := by
            simp [V, rawCalendar, QueueReplay.replay]
          have hseed' : (r0.complementScores j, q0.queue j) =
              QueueReplay.replay (4 * rate.n) (0, 0) (rawCalendar rate j.val P) := by
            simpa only [ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay,
              List.take_length] using hseed j
          calc
            (U0 j.val e).1 = (V j 0).1 := by simpa [heq, hzero] using congrArg Prod.fst h.symm
            _ = (r0.complementScores j, q0.queue j).1 := by rw [hV0]
            _ = (QueueReplay.replay (4 * rate.n) (0, 0)
                (rawCalendar rate j.val P)).1 := congrArg Prod.fst hseed'
        have hscoreBefore : (U0 j.val (e - 1)).1 =
            (QueueReplay.replay (4 * rate.n) (0, 0)
              (rawCalendar rate j.val (P.take (b.val - 1)))).1 := by
          change (QueueReplay.replay (4 * rate.n) (0, 0)
            (rawCalendar rate j.val (H.take (e - 1)))).1 = _
          rw [htakeP]
        have hqprev : qE.previousService jE = q0.previousService j := by
          have hq := hvaluesJ'.2
          rw [if_pos hzero] at hq
          exact hq
        calc
          qE.previousService jE = q0.previousService j := hqprev
          _ = (QueueReplay.replay (4 * rate.n) (0, 0)
                (rawCalendar rate j.val P)).1 -
              (QueueReplay.replay (4 * rate.n) (0, 0)
                (rawCalendar rate j.val (P.take (b.val - 1)))).1 := hprevP
          _ = (U0 j.val e).1 - (U0 j.val (e - 1)).1 := by rw [← hscoreEnd, ← hscoreBefore]
      · have hprevV : qE.previousService jE =
            (V j W.length).1 - (V j (W.length - 1)).1 := by
          have hq := hvaluesJ'.2
          rw [if_neg hzero] at hq
          exact hq
        have hindex : b.val + (W.length - 1) = e - 1 := by dsimp [e]; omega
        rw [hprevV, hVglobal j W.length le_rfl,
          hVglobal j (W.length - 1) (by omega), hindex]
  refine ⟨hPlen, hBlen, heR, heT, hHlen, hHtake, hprefix, hrawSlots,
    (fun _ _ => hcoverageH.1), hcoverageH.2, ?_⟩
  refine ⟨rE, qE, hp, hlast, hin, hEndpointValues, ?_⟩
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
      refine Or.inr ⟨he, seg, I, l0, Dword, hat,
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
          obtain ⟨rF, qF, _hpF, _houtF, hinF, hvaluesF, hboundaryExit⟩ := hboundary hlater
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
              let jE : FastArm rE.payload.slowSet :=
                ⟨j.val, by simpa only [hp] using j.property⟩
              have hvaluesF' :
                  (rE.complementScores jE, qE.queue jE) = V W.length ∧
                  qE.previousService jE = d := by
                simpa only [V, d, ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar,
                  ReferenceCompleteLaterLiveComplementPrefixReplay.prefixCells_length,
                  List.take_length] using hvaluesF j
              have hendpointJ := hEndpointValues j
              have hVEndpoint0 : V W.length = U0 j.val e := by
                calc
                  V W.length = (rE.complementScores jE, qE.queue jE) := hvaluesF'.1.symm
                  _ = U0 j.val e := hendpointJ.1
              have hVe : V W.length = U j.val e := by
                rw [hVEndpoint0]
                dsimp only [U0, U]
                rw [hEtake, List.take_of_length_le (by omega : H.length ≤ e)]
              have hUprior : U j.val (e - 1) = U0 j.val (e - 1) := by
                dsimp only [U, U0]
                change QueueReplay.replay (4 * rate.n) (0, 0)
                    (rawCalendar rate j.val (E.take (e - 1))) =
                  QueueReplay.replay (4 * rate.n) (0, 0)
                    (rawCalendar rate j.val (H.take (e - 1)))
                change QueueReplay.replay (4 * rate.n) (0, 0)
                    (rawCalendar rate j.val ((H ++ Dword).take (e - 1))) = _
                rw [take_before_append H Dword (e - 1)
                  (by rw [hHlen]; exact Nat.sub_le e 1)]
              have hd : d = (U j.val e).1 - (U j.val (e - 1)).1 := by
                calc
                  d = qE.previousService jE := hvaluesF'.2.symm
                  _ = (U0 j.val e).1 - (U0 j.val (e - 1)).1 := hendpointJ.2
                  _ = (U j.val e).1 - (U j.val (e - 1)).1 := by
                    rw [← hVe, ← hUprior, hVEndpoint0]
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

end Bandits.Support.ReferenceCompleteInitializedOutsideCalendarReplay
