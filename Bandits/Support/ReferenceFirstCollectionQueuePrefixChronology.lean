/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionActiveBoundaryQueueQuery
public import Bandits.Support.ReferenceFirstLiveSourceStoppedReleaseEndpoint

/-!
# First-collection queue prefix chronology

Sources: `sources/zip4/manuscript/06_interruptions.tex:355-361,391-408,425-431`,
`sources/zip4/manuscript/04_slow_fast_learner.tex:157-187,245-290`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:44-64,100-108`, and
`sources/zip4/manuscript/05_binary_transport.tex:180-188`.

These internal results relate actual incoming collection records at different
dates and preserve the first overflow update in a local source-date endpoint.
They do not assert a future active date or a full phase endpoint.
-/

@[expose] public section

open Bandits.Support
open ConstructorDimensions
open scoped Classical

namespace Bandits.Support.ReferenceFirstCollectionQueuePrefixChronology

open ReferenceFirstCollectionActiveBoundaryQueueQuery
open ReferenceFirstCollectionPendingObservation
open ReferenceCompleteFirstPhaseObservationRecovery

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)

abbrev Cell := RecordedQueueRun.RoundInput p.K
abbrev Source := BootstrapPrivateRoundStreams.SourceInput p
abbrev OBS := ReferenceCompleteFirstPhaseObservationRecovery.OBS rate

/-- The local first excluded source date for a finite actual matching list.
The horizon sentinel means that no crossing was found in this list. -/
noncomputable def prefixOverflowExcluded (s : ℕ) (L : List (Cell (p := p))) : ℕ :=
  let k := UnstoppedRecordedQueueComparison.firstOverflowPrefix
    (ReferenceFirstLaunchNumericalCell.queueParameters rate) L
  if k ≤ L.length then min (p.T + 1) (s + k + 1) else p.T + 1

variable {rate rewards C_star C_h}

/-- Whole numerical matching at a later date restricts to exactly the earlier
whole matching prefix, including the cell at the earlier current date. -/
theorem whole_matches_prefix {p : ConstructorDimensions.Parameters}
    (rate : ReferenceActivePhysicalStep.RateInput p)
    {s u : ℕ} (t0 t1 : Fin p.T)
    (hs : s ≤ u) (hu : u ≤ t0.val) (ht : t0.val ≤ t1.val)
    (omega : ReferenceCompleteFirstPhaseObservationRecovery.OBS rate)
    (N0 N1 : List (RecordedQueueRun.RoundInput p.K))
    (c0 c1 : RecordedQueueRun.RoundInput p.K)
    (hm0 : ReferenceFirstCollectionActiveBoundaryQueueQuery.Matches rate s u t0 omega N0 c0)
    (hm1 : ReferenceFirstCollectionActiveBoundaryQueueQuery.Matches rate s u t1 omega N1 c1) :
    N0 ++ [c0] = (N1 ++ [c1]).take (N0.length + 1) := by
  have hlen0 : N0.length = t0.val - s := hm0.1
  have hlen1 : N1.length = t1.val - s := hm1.1
  by_cases hdates : t0.val = t1.val
  · have ht01 : t0 = t1 := Fin.ext hdates
    subst t1
    have hp := ReferenceFirstCollectionActiveBoundaryQueueQuery.matches_unique
      s u t0 omega hm0 hm1
    have hlist := congrArg (fun z : List (RecordedQueueRun.RoundInput p.K) ×
      RecordedQueueRun.RoundInput p.K => z.1 ++ [z.2]) hp
    calc
      N0 ++ [c0] = N1 ++ [c1] := hlist
      _ = (N1 ++ [c1]).take (N0.length + 1) := by simp [hlen0, hlen1]
  · have hlt : N0.length < N1.length := by omega
    let c := N1[N0.length]'(by omega)
    have hnew : ReferenceFirstCollectionActiveBoundaryQueueQuery.Matches
        rate s u t0 omega (N1.take N0.length) c := by
      constructor
      · rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hlt), hlen0]
      · intro j hj
        have hjlen : j < N0.length + 1 := by
          simpa [List.length_take, Nat.min_eq_left (Nat.le_of_lt hlt),
            List.length_append, List.length_singleton] using hj
        by_cases hjpast : j < N0.length
        · have hfull : j < (N1 ++ [c1]).length := by
            simp only [List.length_append, List.length_singleton]
            omega
          have hnum := hm1.2 j hfull
          have htake : ((N1.take N0.length) ++ [c])[j] = N1[j] := by
            rw [List.getElem_append_left (by
              simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hlt)]
              omega)]
            simp only [List.getElem_take]
          have hget : (N1 ++ [c1])[j] = N1[j] :=
            List.getElem_append_left (by omega)
          rw [hget] at hnum
          rw [htake]
          exact hnum
        · have hjEq : j = N0.length := by omega
          subst j
          have hfull : N0.length < (N1 ++ [c1]).length := by
            simp only [List.length_append, List.length_singleton]
            omega
          have hnum := hm1.2 N0.length hfull
          have htake : ((N1.take N0.length) ++ [c])[N0.length] = c := by
            have htlen : (N1.take N0.length).length = N0.length := by
              simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hlt)]
            have happend := List.getElem_append_right
              (as := N1.take N0.length) (bs := [c]) (i := N0.length)
              (by rw [htlen]) (h₂ := hj)
            simpa only [htlen, Nat.sub_self, List.getElem_cons_zero] using happend
          have hget : (N1 ++ [c1])[N0.length] = N1[N0.length] :=
            List.getElem_append_left (by omega)
          rw [hget] at hnum
          rw [htake]
          exact hnum
    have hp := ReferenceFirstCollectionActiveBoundaryQueueQuery.matches_unique
      s u t0 omega hm0 hnew
    have hlist := congrArg (fun z : List (RecordedQueueRun.RoundInput p.K) ×
      RecordedQueueRun.RoundInput p.K => z.1 ++ [z.2]) hp
    have htake : (N1 ++ [c1]).take (N0.length + 1) =
        (N1.take N0.length) ++ [c] := by
      rw [List.take_succ_eq_append_getElem (by
        simp only [List.length_append, List.length_singleton]
        omega)]
      simp [c, List.getElem_append_left (by omega),
        List.take_append_of_le_length (show N0.length ≤ N1.length by omega)]
    exact hlist.trans htake.symm

/-- A present first crossing remains the same under extension of a list that
preserves its entire prefix. -/
theorem first_crossing_date_stable {p : ConstructorDimensions.Parameters}
    (rate : ReferenceActivePhysicalStep.RateInput p) (s : ℕ)
    (L0 L1 : List (RecordedQueueRun.RoundInput p.K))
    (hprefix : L0 = L1.take L0.length)
    (hk : UnstoppedRecordedQueueComparison.firstOverflowPrefix
      (ReferenceFirstLaunchNumericalCell.queueParameters rate) L0 ≤ L0.length) :
    UnstoppedRecordedQueueComparison.firstOverflowPrefix
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) L1 =
      UnstoppedRecordedQueueComparison.firstOverflowPrefix
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) L0 ∧
    prefixOverflowExcluded (p := p) rate s L1 =
      prefixOverflowExcluded (p := p) rate s L0 := by
  let q := ReferenceFirstLaunchNumericalCell.queueParameters rate
  let k0 := UnstoppedRecordedQueueComparison.firstOverflowPrefix q L0
  let k1 := UnstoppedRecordedQueueComparison.firstOverflowPrefix q L1
  have hlen : L0.length ≤ L1.length := by
    by_contra hnot
    have hlt : L1.length < L0.length := by omega
    have h := congrArg List.length hprefix
    simp [List.length_take, Nat.min_eq_right (Nat.le_of_lt hlt)] at h
    omega
  have htake (n : ℕ) (hn : n ≤ L0.length) : L0.take n = L1.take n := by
    rw [hprefix, List.take_take]
    simp only [Nat.min_eq_left hn]
  have hcross0 : UnstoppedRecordedQueueComparison.replay_crosses_overflow q L0 k0 := by
    exact UnstoppedRecordedQueueComparison.replay_crosses_overflow_at_first q L0 hk
  have hcross1 : UnstoppedRecordedQueueComparison.replay_crosses_overflow q L1 k0 := by
    have hsame := htake k0 hk
    have hregs : UnstoppedRecordedQueueComparison.unstoppedReplay q L0 k0 =
        UnstoppedRecordedQueueComparison.unstoppedReplay q L1 k0 := by
      funext i
      change QueueReplay.replay (4 * q.n) (0, 0)
          ((L0.take k0).map fun v => UnstoppedRecordedQueueComparison.unstoppedRecord q v i)
        = QueueReplay.replay (4 * q.n) (0, 0)
          ((L1.take k0).map fun v => UnstoppedRecordedQueueComparison.unstoppedRecord q v i)
      rw [hsame]
    rcases hcross0 with ⟨i, hi⟩
    refine ⟨i, ?_⟩
    rw [← hregs]
    exact hi
  have hk1le : k1 ≤ k0 := by
    by_contra hnot
    have hlt : k0 < k1 := by omega
    have hk0pos : 1 ≤ k0 := by
      have hpos := UnstoppedRecordedQueueComparison.first_overflow_prefix_pos q L0
      change 0 < k0 at hpos
      omega
    have hk0L1 : k0 ≤ L1.length := le_trans hk hlen
    have hnotcross := UnstoppedRecordedQueueComparison.not_replay_crosses_overflow_before_first
      q L1 k0 hk0pos hk0L1 hlt
    exact hnotcross hcross1
  have hk0le : k0 ≤ k1 := by
    by_contra hnot
    have hlt : k1 < k0 := by omega
    have hk1bound : k1 ≤ L1.length := le_trans (Nat.le_of_lt hlt) hk
      |>.trans hlen
    have hcross1first := UnstoppedRecordedQueueComparison.replay_crosses_overflow_at_first
      q L1 hk1bound
    have hsame := htake k1 ((Nat.le_of_lt hlt).trans hk)
    have hregs : UnstoppedRecordedQueueComparison.unstoppedReplay q L1 k1 =
        UnstoppedRecordedQueueComparison.unstoppedReplay q L0 k1 := by
      funext i
      change QueueReplay.replay (4 * q.n) (0, 0)
          ((L1.take k1).map fun v => UnstoppedRecordedQueueComparison.unstoppedRecord q v i)
        = QueueReplay.replay (4 * q.n) (0, 0)
          ((L0.take k1).map fun v => UnstoppedRecordedQueueComparison.unstoppedRecord q v i)
      rw [hsame]
    have hcross0early : UnstoppedRecordedQueueComparison.replay_crosses_overflow q L0 k1 := by
      rcases hcross1first with ⟨i, hi⟩
      refine ⟨i, ?_⟩
      rw [hregs] at hi
      exact hi
    have hk1pos : 1 ≤ k1 := by
      have hpos := UnstoppedRecordedQueueComparison.first_overflow_prefix_pos q L1
      change 0 < k1 at hpos
      omega
    have hk1L0 : k1 ≤ L0.length := Nat.le_trans (Nat.le_of_lt hlt) hk
    have hnotcross := UnstoppedRecordedQueueComparison.not_replay_crosses_overflow_before_first
      q L0 k1 hk1pos hk1L0 hlt
    exact hnotcross hcross0early
  have heq : k1 = k0 := Nat.le_antisymm hk1le hk0le
  constructor
  · exact heq
  · unfold prefixOverflowExcluded
    change (if k1 ≤ L1.length then min (p.T + 1) (s + k1 + 1) else p.T + 1) =
      (if k0 ≤ L0.length then min (p.T + 1) (s + k0 + 1) else p.T + 1)
    have hbranch1 : k1 ≤ L1.length := by rw [heq]; exact le_trans hk hlen
    rw [ite_eq_left hbranch1, ite_eq_left hk, heq]

/-- The actual queue event at a matched collection date is exactly the
source-date comparison with this finite local prefix endpoint. -/
theorem actual_local_overflow_date
    {s u : ℕ} {t : Fin p.T} (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hs : s ≤ u) (hu : u ≤ t.val)
    (hC : z ∈ ReferenceFirstCollectionActiveBoundaryQueueQuery.C
      rate rewards C_star C_h s u t)
    (N : List (RecordedQueueRun.RoundInput p.K)) (c : RecordedQueueRun.RoundInput p.K)
    (hm : ReferenceFirstCollectionActiveBoundaryQueueQuery.Matches rate s u t
      (ReferenceCompleteNumericalBranchObservation.completeBranchObservation
        rate rewards C_star C_h z) N c) :
    z ∈ ReferenceFirstCollectionActiveBoundaryQueueQuery.queueEvent
        (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) s u t ↔
      t.val + 1 < prefixOverflowExcluded (p := p) rate s (N ++ [c]) := by
  let q := ReferenceFirstLaunchNumericalCell.queueParameters rate
  let L := N ++ [c]
  let k := UnstoppedRecordedQueueComparison.firstOverflowPrefix q L
  have htime : t.val = s + N.length := by
    have hlen := hm.1
    have hsu : s ≤ t.val := hs.trans hu
    omega
  have hqueue := ReferenceFirstCollectionActiveBoundaryQueueQuery.queueEvent_iff_before_current_firstOverflow
    s u t hs hu z hC N c hm
  have hqueue' : z ∈ ReferenceFirstCollectionActiveBoundaryQueueQuery.queueEvent
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) s u t ↔
      N.length < k := by
    simpa [q, k] using hqueue
  have hlocal : N.length < k ↔
      t.val + 1 < (if k ≤ L.length then min (p.T + 1) (s + k + 1) else p.T + 1) := by
    have hL : L.length = N.length + 1 := by simp [L]
    by_cases hk : k ≤ L.length
    · by_cases hnow : N.length < k
      · have heq : k = N.length + 1 := by omega
        rw [ite_eq_left hk, heq]
        have htbound : t.val + 1 < p.T + 1 := by omega
        have hright : t.val + 1 < s + (N.length + 1) + 1 := by omega
        have hnow' : N.length < N.length + 1 := by omega
        exact iff_of_true hnow' (Nat.lt_min.mpr ⟨htbound, by omega⟩)
      · have hkprev : k ≤ N.length := by omega
        rw [ite_eq_left hk]
        have hfalse : ¬ t.val + 1 < min (p.T + 1) (s + k + 1) := by
          apply not_lt_of_ge
          calc
            min (p.T + 1) (s + k + 1) ≤ s + k + 1 := Nat.min_le_right _ _
            _ ≤ s + N.length + 1 := by omega
            _ = t.val + 1 := by omega
        exact iff_of_false (by omega) hfalse
    · rw [ite_eq_right hk]
      have htrue : t.val + 1 < p.T + 1 := by omega
      have hktrue : N.length < k := by omega
      exact iff_of_true hktrue htrue
  simpa [prefixOverflowExcluded, q, L, k] using hqueue'.trans hlocal

private theorem firstLiveWindow_cutoff
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow records).length < records.length) :
    ReferenceCollectionPhaseHistory.cutoffChosen
      (records[(ReferenceFirstLiveConfirmationHistory.firstLiveWindow records).length]).input = true := by
  induction records with
  | nil => simp [ReferenceFirstLiveConfirmationHistory.firstLiveWindow] at hshort
  | cons r rs ih =>
      cases hc : ReferenceCollectionPhaseHistory.cutoffChosen r.input with
      | false =>
          simpa [ReferenceFirstLiveConfirmationHistory.firstLiveWindow, hc] using
            ih (by simpa [ReferenceFirstLiveConfirmationHistory.firstLiveWindow, hc] using hshort)
      | true => simp [ReferenceFirstLiveConfirmationHistory.firstLiveWindow, hc]

section ActualWindow

variable (z : BootstrapPrivateRoundStreams.SourceInput p)
variable (hcross : (ReferenceInitializationRun.output
  (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)

local notation "start" => ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
local notation "count" => p.T - start
local notation "span" => firstPhaseReadySpan rate rewards C_star C_h z
local notation "w" =>
  (List.length (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
    (ReferenceActivePhysicalHorizon.Run.records
      (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
        z rewards C_star C_h hcross
        (p.T - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
        (firstPhaseReadySpan rate rewards C_star C_h z)))))
local notation "B" =>
  (ReferenceCollectionPhaseHistory.collectionWindow
    (ReferenceActivePhysicalHorizon.Run.records
      (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
        z rewards C_star C_h hcross
        (p.T - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
        (firstPhaseReadySpan rate rewards C_star C_h z)))
    (List.length (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceActivePhysicalHorizon.Run.records
        (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
          z rewards C_star C_h hcross
          (p.T - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
          (firstPhaseReadySpan rate rewards C_star C_h z))))))

variable (hshort :
  (List.length (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
    (ReferenceActivePhysicalHorizon.Run.records
      (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
        z rewards C_star C_h hcross
        (p.T - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
        (firstPhaseReadySpan rate rewards C_star C_h z))))) <
    (p.T - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h))
variable (d : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
  (rate := rate) z rewards C_star C_h
  (p.T - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
  hcross (firstPhaseReadySpan rate rewards C_star C_h z) hshort)

private theorem active_window_boundary (s u : ℕ) (t : Fin p.T)
    (hs : s ≤ u) (hu : u ≤ t.val) (hz : z ∈ C rate rewards C_star C_h s u t)
    (k : Fin (B).length) (ht : B[k.val].input.time = t) :
    k.val < d.stream.ell ∧ u = start + w ∧ t.val = start + w + k.val := by
  let out := d.stream
  have hwindow : out.window = B := out.windowIsActual
  have htime : t.val = start + w + k.val := by
    have hh := (out.alignment ⟨k.val, by rw [hwindow]; exact k.isLt⟩).2
    simp only [hwindow, ht] at hh
    change t.val + 1 = start + w + 1 + k.val at hh
    omega
  have hstart : start = s := hz.1
  have hP := C_subset_Praw s u t hz
  change (ReferenceFirstCollectionPendingObservation.Praw rate rewards C_star C_h t.val z).Nonempty at hP
  have hQ : (ReferenceFirstCollectionPendingObservation.Q rate rewards C_star C_h start
      B[k.val].input.time z).Nonempty := by
    simpa only [ReferenceFirstCollectionPendingObservation.Praw_at, ht] using hP
  have hqw := ReferenceFirstCollectionPendingObservation.Q_window
    (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
    z count hcross span hshort d k
  change ReferenceFirstCollectionPendingObservation.Q rate rewards C_star C_h start
    B[k.val].input.time z = _ at hqw
  rw [hqw] at hQ
  have hkell : k.val < out.ell := by
    by_cases hk0 : k.val = 0
    · have hpos := out.positiveLength
      omega
    · rw [ite_eq_right hk0] at hQ
      by_contra hnot
      rw [dite_eq_right (Nat.not_lt.mpr (Nat.le_of_not_gt hnot))] at hQ
      exact Finset.not_nonempty_empty hQ
  have hcurr : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z = some B[k.val] := by
    unfold ReferenceSourcePrefixHistoryFiltration.actualRecord
    rw [ite_eq_left (show start ≤ t.val by rw [hstart]; exact hs.trans hu),
      completeSuffixRecords_eq_actualFirstEpoch rate rewards C_star C_h z hcross]
    have hi : t.val - start = w + k.val := by omega
    rw [hi]
    simpa only [hwindow] using
      (out.alignment ⟨k.val, by rw [hwindow]; exact k.isLt⟩).1
  obtain ⟨_, r, hr, hb⟩ := hz
  have heq : r = B[k.val] := Option.some.inj (hr.symm.trans hcurr)
  rw [heq] at hb
  refine ⟨hkell, ?_, htime⟩
  by_cases hk0 : k.val = 0
  · have hhead : B[k.val] = out.cutoff.cut := by
      simpa only [hwindow, hk0] using out.cutoffIsHead
    obtain ⟨execution⟩ := out.cutoffExecution
    rw [hhead, execution.actualLive] at hb
    have hu' : t.val = u := hb.1
    omega
  · obtain ⟨j, r', incoming, cell, _, hr', _, hprevious⟩ :=
      out.cell_at ⟨k.val, hkell⟩ (Nat.pos_of_ne_zero hk0)
    have hrEq : r' = B[k.val] := by
      simp only [hwindow] at hr'
      exact (List.getElem?_eq_some_iff.mp hr').2.symm
    have hcoord := cell.readyInput.1
    rw [hrEq] at hcoord
    rw [hcoord] at hb
    have hcut : incoming.cutoff = start + w + 1 := by
      rw [hprevious, (out.context ⟨k.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) hkell⟩).2.1]
      exact out.cutoff.ledgerCutoff
    have hu' : incoming.cutoff = u + 1 := hb.2.2.1
    omega

private theorem active_stream_cell_at (n : Fin d.stream.ell) (hn : 0 < n.val) :
    ∃ j r incoming,
      ∃ cell : ReferenceFirstCollectionReadyStream.ContinuingStreamCell z rewards
          (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
            z rewards C_star C_h hcross count span).records
          j count (ReferenceFirstCollectionReadyStream.startTime (rate := rate)
            z rewards C_star C_h) r d.stream.payload incoming d.stream.saved,
        j = (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
          (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
            z rewards C_star C_h hcross count span).records).length + n.val ∧
        d.stream.window[n.val]? = some r ∧
        cell.serviceLedger = d.stream.ledgers n ∧
        incoming = d.stream.ledgers ⟨n.val - 1, by omega⟩ :=
  d.stream.cell_at n hn

private theorem active_window_membership (s u : ℕ) (t : Fin p.T)
    (hstart : start = s) (huwindow : u = start + w)
    (k : Fin (B).length) (hkell : k.val < d.stream.ell)
    (ht : B[k.val].input.time = t)
    (hrecord : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z = some B[k.val])
    (hQ : (ReferenceFirstCollectionPendingObservation.Q rate rewards C_star C_h
      s B[k.val].input.time z).Nonempty) :
    z ∈ C rate rewards C_star C_h s u t := by
  refine ⟨hstart, B[k.val], hrecord, ?_⟩
  have hwindow : d.stream.window = B := d.stream.windowIsActual
  have huwindow' : u = start + w := by
    exact huwindow
  by_cases hk0 : k.val = 0
  · have hhead : B[k.val] = d.stream.cutoff.cut := by
      simpa only [hwindow, hk0] using d.stream.cutoffIsHead
    obtain ⟨execution⟩ := d.stream.cutoffExecution
    have hcount : (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
        z rewards C_star C_h hcross count span).records.length = count :=
      ReferenceActivePhysicalHorizon.run_record_count _ _ _ _ _ _ _ _
    have hshortRecords :
        (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
          (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
            z rewards C_star C_h hcross count span).records).length <
          (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
            z rewards C_star C_h hcross count span).records.length := by
      rw [hcount]
      exact hshort
    have hcut : ReferenceCollectionPhaseHistory.cutoffChosen
        d.stream.cutoff.cut.input = true := by
      have hidx := d.stream.cutoff.cutIndex
      have heq :
          (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
            z rewards C_star C_h hcross count span).records[
              (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
                (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
                  z rewards C_star C_h hcross count span).records).length] =
            d.stream.cutoff.cut :=
        (List.getElem?_eq_some_iff.mp hidx).2
      rw [← heq]
      exact firstLiveWindow_cutoff _ hshortRecords
    have htime0 : t.val = u := by
      have hi := (d.stream.alignment
        ⟨k.val, by rw [hwindow]; exact k.isLt⟩).2
      simp only [hwindow, ht] at hi
      change t.val + 1 = start + w + 1 + k.val at hi
      rw [hk0] at hi
      have hi' : t.val = start + w := by omega
      exact hi'.trans huwindow'.symm
    have hstate : B[k.val].input.state.coordinator =
        .live execution.live execution.owned execution.base := by
      rw [hhead]
      exact execution.actualLive
    rw [hstate, hhead]
    refine ⟨htime0, ?_, ?_⟩
    · calc
        execution.live.payload.sigma.val = d.stream.cutoff.payload.sigma.val := by
          exact congrArg (fun payload => payload.sigma.val) execution.payloadIsLive.symm
        _ = start := d.stream.cutoffContext.2.1
        _ = s := hstart
    · exact hcut
  · obtain ⟨j, r, incoming, cell, _, hr, _, hprevious⟩ :=
      @active_stream_cell_at p rate rewards C_star C_h z hcross hshort d
        ⟨k.val, hkell⟩ (Nat.pos_of_ne_zero hk0)
    have hr' : r = B[k.val] := by
      simp only [hwindow] at hr
      exact (List.getElem?_eq_some_iff.mp hr).2.symm
    have hcoord := cell.readyInput.1
    rw [hr'] at hcoord
    cases hc : B[k.val].input.state.coordinator with
    | live registers owned base =>
        rw [hc] at hcoord
        cases hcoord
    | collection payload ledger saved =>
        rw [hc] at hcoord
        injection hcoord with hpayload hledger hsaved
        have hsig : payload.sigma.val = s := by
          by_contra hneq
          have hq := hQ
          rw [ht] at hq
          simp [ReferenceFirstCollectionPendingObservation.Q, hrecord, hc, hneq] at hq
        have hpending : ledger.pending.Nonempty := by
          have hq := hQ
          rw [ht] at hq
          rw [show ReferenceFirstCollectionPendingObservation.Q rate rewards C_star C_h
              s t z = ledger.pending by
            simp [ReferenceFirstCollectionPendingObservation.Q, hrecord, hc, hsig]] at hq
          exact hq
        have hcut : ledger.cutoff = u + 1 := by
          have hcut' : incoming.cutoff = start + w + 1 := by
            rw [hprevious,
              (d.stream.context ⟨k.val - 1,
                Nat.lt_of_le_of_lt (Nat.sub_le _ _) hkell⟩).2.1]
            exact d.stream.cutoff.ledgerCutoff
          have hledgerCut : ledger.cutoff = incoming.cutoff :=
            congrArg (fun q : ReferenceActivePhysicalStep.Ledger rate => q.cutoff) hledger
          omega
        have htimegt : u < t.val := by
          have hdate := (d.stream.alignment
            ⟨k.val, by rw [hwindow]; exact k.isLt⟩).2
          simp only [hwindow, ht] at hdate
          change t.val + 1 = start + w + 1 + k.val at hdate
          have hdate' : t.val = start + w + k.val := by omega
          have hkpos : 0 < k.val := Nat.pos_of_ne_zero hk0
          have hlt : start + w < start + w + k.val :=
            Nat.lt_add_of_pos_right hkpos
          rw [huwindow', hdate']
          exact hlt
        exact ⟨htimegt, hsig, hcut, hpending⟩
    | first =>
        rw [ht] at hQ
        simp [ReferenceFirstCollectionPendingObservation.Q, hrecord, hc] at hQ
    | dagger =>
        rw [ht] at hQ
        simp [ReferenceFirstCollectionPendingObservation.Q, hrecord, hc] at hQ

end ActualWindow

private theorem Praw_nonempty_implies_Q
    (z : BootstrapPrivateRoundStreams.SourceInput p) (s : ℕ) (t : Fin p.T)
    (hstart : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h = s)
    (hP : (ReferenceFirstCollectionPendingObservation.Praw
      rate rewards C_star C_h t.val z).Nonempty) :
    (ReferenceFirstCollectionPendingObservation.Q rate rewards C_star C_h s t z).Nonempty := by
  simpa only [ReferenceFirstCollectionPendingObservation.Praw_at, hstart] using hP

/-- An active incoming record remains active at every earlier date after
its actual cutoff; the original pending observation is nested backward. -/
theorem active_boundary_backward
    {s u : ℕ} {t0 t1 : Fin p.T} (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hs : s ≤ u) (hu : u ≤ t0.val) (ht : t0.val ≤ t1.val)
    (h1 : z ∈ C rate rewards C_star C_h s u t1) :
    z ∈ C rate rewards C_star C_h s u t0 ∧
      ReferenceFirstCollectionPendingObservation.Praw rate rewards C_star C_h t1.val z ⊆
        ReferenceFirstCollectionPendingObservation.Praw rate rewards C_star C_h t0.val z := by
  have hP1 := C_subset_Praw s u t1 h1
  change (ReferenceFirstCollectionPendingObservation.Praw rate rewards C_star C_h t1.val z).Nonempty at hP1
  let start := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  have hstart : start = s := h1.1
  rcases h1 with ⟨hstart0, r1, hr1, hb1⟩
  have h1' : z ∈ C rate rewards C_star C_h s u t1 := ⟨hstart0, r1, hr1, hb1⟩
  have hlaunch : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
      rate rewards C_star C_h t1.val z := by
    by_contra hnot
    rw [ReferenceSourcePrefixHistoryFiltration.actualRecord_eq_none_of_not_launchBy
      rate rewards C_star C_h t1 z hnot] at hr1
    cases hr1
  have hcross := hlaunch.1
  let count := p.T - start
  let span := firstPhaseReadySpan rate rewards C_star C_h z
  let E := ReferenceFirstCollectionReadyStream.actualEpoch
    (rate := rate) z rewards C_star C_h hcross count span
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length
  let B := ReferenceCollectionPhaseHistory.collectionWindow E.records w
  have hrecords : ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h = E.records :=
    completeSuffixRecords_eq_actualFirstEpoch rate rewards C_star C_h z hcross
  let observed := fun records : List (ReferenceActivePhysicalHorizon.RoundRecord
      (p := p) (rate := rate)) =>
    ∃ k : Fin (ReferenceCollectionPhaseHistory.collectionWindow records
        (ReferenceFirstLiveConfirmationHistory.firstLiveWindow records).length).length,
      (ReferenceCollectionPhaseHistory.collectionWindow records
        (ReferenceFirstLiveConfirmationHistory.firstLiveWindow records).length)[k.val].input.time = t1
  have hloc : ∃ k : Fin B.length, B[k.val].input.time = t1 :=
    Eq.mp (congrArg observed hrecords)
      (ReferenceFirstCollectionPendingObservation.Praw_localization t1 z hP1)
  obtain ⟨k1, ht1⟩ := hloc
  have hcount : E.records.length = count :=
    ReferenceActivePhysicalHorizon.run_record_count _ _ _ _ _ _ _ _
  have hshort : w < count := by
    by_contra hnot
    have hB : B = [] := by
      simp only [B, ReferenceCollectionPhaseHistory.collectionWindow,
        List.drop_eq_nil_iff.mpr (show E.records.length ≤ w by omega),
        List.drop_eq_nil_iff.mpr (show E.records.length ≤ w + 1 by omega),
        List.take_nil, List.takeWhile_nil, List.append_nil]
    have hlen : B.length = 0 := congrArg List.length hB
    have hk := k1.isLt
    omega
  obtain ⟨d⟩ := ReferenceFirstCollectionStreamEmptyDispatch.actual_initialized_first_collection_stream_empty_dispatch
    rate z rewards C_star C_h count hcross span hshort
  have hbound := active_window_boundary z hcross hshort d
    s u t1 hs (hu.trans ht) h1' k1 ht1
  obtain ⟨hkell, huwindow, ht1index⟩ := hbound
  have hwindow : d.stream.window = B := d.stream.windowIsActual
  let i0 := t0.val - (start + w)
  have hbase : start + w ≤ t0.val := by
    calc
      start + w = u := huwindow.symm
      _ ≤ t0.val := hu
  have hi0le : i0 ≤ k1.val := by
    calc
      i0 ≤ t1.val - (start + w) := by
        dsimp [i0]
        exact Nat.sub_le_sub_right ht (start + w)
      _ = k1.val := by
        rw [ht1index]
        exact Nat.add_sub_cancel_left _ _
  have hi0 : i0 < B.length := lt_of_le_of_lt hi0le k1.isLt
  let k0 : Fin B.length := ⟨i0, hi0⟩
  have hk0ell : k0.val < d.stream.ell :=
    Nat.lt_of_le_of_lt hi0le hkell
  have ht0 : B[k0.val].input.time = t0 := by
    apply Fin.ext
    have htime' := (d.stream.alignment
      ⟨k0.val, by rw [hwindow]; exact k0.isLt⟩).2
    simp only [hwindow] at htime'
    change B[k0.val].input.time.val + 1 = start + w + 1 + k0.val at htime'
    have hi : start + w + k0.val = t0.val := by
      have hk0val : k0.val = i0 := rfl
      rw [hk0val]
      change start + w + i0 = t0.val
      exact Nat.add_sub_of_le hbase
    omega
  have hnested := ReferenceFirstCollectionPendingObservation.Q_window_nested
    (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
    z count hcross span hshort d k0 k1 hi0le
  have hnestedS :
      ReferenceFirstCollectionPendingObservation.Q rate rewards C_star C_h s
        B[k1.val].input.time z ⊆
      ReferenceFirstCollectionPendingObservation.Q rate rewards C_star C_h s
        B[k0.val].input.time z := by
    simpa only [B, w, E, ReferenceFirstCollectionReadyStream.actualEpoch, hstart0] using hnested
  have hQ1s := Praw_nonempty_implies_Q z s t1 hstart0 hP1
  have hQ1non :
      (ReferenceFirstCollectionPendingObservation.Q rate rewards C_star C_h s
        B[k1.val].input.time z).Nonempty := by
    rw [ht1]
    exact hQ1s
  have hQ0non :
      (ReferenceFirstCollectionPendingObservation.Q rate rewards C_star C_h s
        B[k0.val].input.time z).Nonempty := by
    obtain ⟨a, ha⟩ := hQ1non
    exact ⟨a, hnestedS ha⟩
  have hrecord0 : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t0 z = some B[k0.val] := by
    unfold ReferenceSourcePrefixHistoryFiltration.actualRecord
    rw [ite_eq_left (show start ≤ t0.val by rw [hstart]; exact hs.trans hu),
      completeSuffixRecords_eq_actualFirstEpoch rate rewards C_star C_h z hcross]
    have hiT : start + w + k0.val = t0.val := by
      have hk0val : k0.val = i0 := rfl
      rw [hk0val]
      dsimp [i0]
      exact Nat.add_sub_of_le hbase
    have hi : t0.val - start = w + k0.val := by omega
    rw [hi]
    have hlookup := (d.stream.alignment
      ⟨k0.val, by rw [hwindow]; exact k0.isLt⟩).1
    simpa only [hwindow] using hlookup
  have hmember0 := active_window_membership z hcross hshort d
    s u t0 hstart huwindow k0 hk0ell ht0 hrecord0 hQ0non
  constructor
  · exact hmember0
  · intro a ha
    have hmem : a ∈ ReferenceFirstCollectionPendingObservation.Q rate rewards C_star C_h s t1 z := by
      simpa only [ReferenceFirstCollectionPendingObservation.Praw_at, hstart0] using ha
    have hb := hnestedS (by simpa only [ht1] using hmem)
    have hb' : a ∈ ReferenceFirstCollectionPendingObservation.Q rate rewards C_star C_h s t0 z := by
      rw [← ht0]
      exact hb
    simpa only [ReferenceFirstCollectionPendingObservation.Praw_at, hstart0] using hb'

section ActualWindowCutoff

variable (z : Source (p := p))
variable (hcross : (ReferenceInitializationRun.output
  (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)

local notation "start" => ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
local notation "count" => p.T - start
local notation "span" => firstPhaseReadySpan rate rewards C_star C_h z
local notation "w" =>
  (List.length (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
    (ReferenceActivePhysicalHorizon.Run.records
      (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
        z rewards C_star C_h hcross count span))))
local notation "B" =>
  (ReferenceCollectionPhaseHistory.collectionWindow
    (ReferenceActivePhysicalHorizon.Run.records
      (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
        z rewards C_star C_h hcross count span)) w)

variable (hshort :
  (List.length (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
    (ReferenceActivePhysicalHorizon.Run.records
      (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
        z rewards C_star C_h hcross
        (p.T - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
        (firstPhaseReadySpan rate rewards C_star C_h z))))) <
    (p.T - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h))
variable (d : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
  (rate := rate) z rewards C_star C_h
  (p.T - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
  hcross (firstPhaseReadySpan rate rewards C_star C_h z) hshort)

/-- Comparing an actual boundary with the same dispatched collection stream
fixes its cutoff to that stream's first collection date. -/
private theorem active_window_cutoff {s u : ℕ} (t : Fin p.T)
    (d' : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
      (rate := rate) z rewards C_star C_h count hcross span hshort)
    (hs : s ≤ u) (hu : u ≤ t.val) (hz : z ∈ C rate rewards C_star C_h s u t)
    (k : Fin (B).length) (ht : (B)[k.val].input.time = t) :
    u = start + w := by
  let out := d'.stream
  have hwindow : out.window = B := out.windowIsActual
  have htime : t.val = start + w + k.val := by
    have hh := (out.alignment ⟨k.val, by rw [hwindow]; exact k.isLt⟩).2
    simp only [hwindow, ht] at hh
    change t.val + 1 = start + w + 1 + k.val at hh
    omega
  have hstart : start = s := hz.1
  have hP := C_subset_Praw s u t hz
  change (ReferenceFirstCollectionPendingObservation.Praw rate rewards C_star C_h t.val z).Nonempty at hP
  have hQ : (ReferenceFirstCollectionPendingObservation.Q
      rate rewards C_star C_h start B[k.val].input.time z).Nonempty := by
    simpa only [ReferenceFirstCollectionPendingObservation.Praw_at, ht] using hP
  have hqw := ReferenceFirstCollectionPendingObservation.Q_window
    (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
    z count hcross span hshort d' k
  change ReferenceFirstCollectionPendingObservation.Q
    rate rewards C_star C_h start B[k.val].input.time z = _ at hqw
  rw [hqw] at hQ
  have hkell : k.val < out.ell := by
    by_cases hk0 : k.val = 0
    · have hpos := out.positiveLength
      omega
    · rw [ite_eq_right hk0] at hQ
      by_contra hnot
      rw [dite_eq_right (Nat.not_lt.mpr (Nat.le_of_not_gt hnot))] at hQ
      exact Finset.not_nonempty_empty hQ
  have hcurr : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z = some B[k.val] := by
    unfold ReferenceSourcePrefixHistoryFiltration.actualRecord
    rw [ite_eq_left (show start ≤ t.val by rw [hstart]; exact hs.trans hu),
      completeSuffixRecords_eq_actualFirstEpoch rate rewards C_star C_h z hcross]
    have hi : t.val - start = w + k.val := by omega
    rw [hi]
    simpa only [hwindow] using
      (out.alignment ⟨k.val, by rw [hwindow]; exact k.isLt⟩).1
  obtain ⟨_, r, hr, hb⟩ := hz
  have heq : r = B[k.val] := Option.some.inj (hr.symm.trans hcurr)
  rw [heq] at hb
  by_cases hk0 : k.val = 0
  · have hhead : B[k.val] = out.cutoff.cut := by
      simpa only [hwindow, hk0] using out.cutoffIsHead
    obtain ⟨execution⟩ := out.cutoffExecution
    rw [hhead, execution.actualLive] at hb
    have hu' : t.val = u := hb.1
    omega
  · obtain ⟨j, r', incoming, cell, _, hr', _, hprevious⟩ :=
      out.cell_at ⟨k.val, hkell⟩ (Nat.pos_of_ne_zero hk0)
    have hrEq : r' = B[k.val] := by
      simp only [hwindow] at hr'
      exact (List.getElem?_eq_some_iff.mp hr').2.symm
    have hcoord := cell.readyInput.1
    rw [hrEq] at hcoord
    rw [hcoord] at hb
    have hcut : incoming.cutoff = start + w + 1 := by
      rw [hprevious,
        (out.context ⟨k.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) hkell⟩).2.1]
      exact out.cutoff.ledgerCutoff
    have hu' : incoming.cutoff = u + 1 := hb.2.2.1
    omega

end ActualWindowCutoff

/-- At one original date, the actual incoming record fixes both the physical
start and its collection cutoff. -/
private theorem active_cutoff_unique_at_date
    {s0 s1 u0 u1 : ℕ} {t : Fin p.T} {z : Source (p := p)}
    (h0 : z ∈ C rate rewards C_star C_h s0 u0 t)
    (h1 : z ∈ C rate rewards C_star C_h s1 u1 t) :
    s0 = s1 ∧ u0 = u1 := by
  rcases h0 with ⟨hs0, r0, hr0, hb0⟩
  rcases h1 with ⟨hs1, r1, hr1, hb1⟩
  have hs : s0 = s1 := hs0.symm.trans hs1
  have hr : r0 = r1 := Option.some.inj (hr0.symm.trans hr1)
  subst r1
  constructor
  · exact hs
  · cases hc : r0.input.state.coordinator with
    | live registers owned base =>
        rw [hc] at hb0 hb1
        obtain ⟨hu0, _, _⟩ := hb0
        obtain ⟨hu1, _, _⟩ := hb1
        omega
    | collection payload ledger saved =>
        rw [hc] at hb0 hb1
        obtain ⟨_, _, hcut0, _⟩ := hb0
        obtain ⟨_, _, hcut1, _⟩ := hb1
        omega
    | first =>
        rw [hc] at hb0
        cases hb0
    | dagger =>
        rw [hc] at hb0
        cases hb0

/-- Actual boundary witnesses at any two dates use the same physical start
and the same cutoff selected by their common dispatched collection stream. -/
theorem active_cutoff_unique_across_dates
    {s0 s1 u0 u1 : ℕ} {t0 t1 : Fin p.T} {z : Source (p := p)}
    (hs0 : s0 ≤ u0) (hu0 : u0 ≤ t0.val)
    (hs1 : s1 ≤ u1) (hu1 : u1 ≤ t1.val)
    (h0 : z ∈ C rate rewards C_star C_h s0 u0 t0)
    (h1 : z ∈ C rate rewards C_star C_h s1 u1 t1) :
    s0 = s1 ∧ u0 = u1 := by
  have hP0 := C_subset_Praw s0 u0 t0 h0
  have hP1 := C_subset_Praw s1 u1 t1 h1
  change (ReferenceFirstCollectionPendingObservation.Praw rate rewards C_star C_h
    t0.val z).Nonempty at hP0
  change (ReferenceFirstCollectionPendingObservation.Praw rate rewards C_star C_h
    t1.val z).Nonempty at hP1
  have hstart1 : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h = s1 := h1.1
  have hQ1 := Praw_nonempty_implies_Q z s1 t1 hstart1 hP1
  have hlaunch : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
      rate rewards C_star C_h t1.val z := by
    by_contra hnot
    rw [ReferenceFirstCollectionPendingObservation.Q_eq_empty_of_not_launchBy _ t1 z hnot] at hQ1
    exact Finset.not_nonempty_empty hQ1
  have hcross := hlaunch.1
  let start := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  let count := p.T - start
  let span := firstPhaseReadySpan rate rewards C_star C_h z
  let E := ReferenceFirstCollectionReadyStream.actualEpoch
    (rate := rate) z rewards C_star C_h hcross count span
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length
  let B := ReferenceCollectionPhaseHistory.collectionWindow E.records w
  have hrecords : ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h = E.records :=
    completeSuffixRecords_eq_actualFirstEpoch rate rewards C_star C_h z hcross
  let observed := fun (t : Fin p.T) (records : List
      (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))) =>
    ∃ k : Fin (ReferenceCollectionPhaseHistory.collectionWindow records
        (ReferenceFirstLiveConfirmationHistory.firstLiveWindow records).length).length,
      (ReferenceCollectionPhaseHistory.collectionWindow records
        (ReferenceFirstLiveConfirmationHistory.firstLiveWindow records).length)[k.val].input.time = t
  have hloc0 : ∃ k : Fin B.length, B[k.val].input.time = t0 :=
    Eq.mp (congrArg (observed t0) hrecords)
      (ReferenceFirstCollectionPendingObservation.Praw_localization t0 z hP0)
  have hloc1 : ∃ k : Fin B.length, B[k.val].input.time = t1 :=
    Eq.mp (congrArg (observed t1) hrecords)
      (ReferenceFirstCollectionPendingObservation.Praw_localization t1 z hP1)
  obtain ⟨k1, ht1⟩ := hloc1
  have hcount : E.records.length = count :=
    ReferenceActivePhysicalHorizon.run_record_count _ _ _ _ _ _ _ _
  have hshort : w < count := by
    by_contra hnot
    have hB : B = [] := by
      simp only [B, ReferenceCollectionPhaseHistory.collectionWindow,
        List.drop_eq_nil_iff.mpr (show E.records.length ≤ w by omega),
        List.drop_eq_nil_iff.mpr (show E.records.length ≤ w + 1 by omega),
        List.take_nil, List.takeWhile_nil, List.append_nil]
    have hlen : B.length = 0 := congrArg List.length hB
    have hk1 := k1.isLt
    omega
  obtain ⟨d⟩ := ReferenceFirstCollectionStreamEmptyDispatch.actual_initialized_first_collection_stream_empty_dispatch
    rate z rewards C_star C_h count hcross span hshort
  obtain ⟨k0, ht0⟩ := hloc0
  have hu0' := active_window_cutoff (z := z) (hcross := hcross)
    (hshort := hshort) (d' := d) t0 hs0 hu0 h0 k0 ht0
  have hu1' := active_window_cutoff (z := z) (hcross := hcross)
    (hshort := hshort) (d' := d) t1 hs1 hu1 h1 k1 ht1
  exact ⟨h0.1.symm.trans h1.1, hu0'.trans hu1'.symm⟩

/-- The actual whole-cell queue event persists to every earlier active date.
Both numerical matches are obtained from the same source input's actual
boundary witnesses. -/
theorem active_queue_backward
    {s u : ℕ} {t0 t1 : Fin p.T} {z : Source (p := p)}
    (hs : s ≤ u) (hu : u ≤ t0.val) (ht : t0.val ≤ t1.val)
    (h1 : z ∈ C rate rewards C_star C_h s u t1)
    (hq1 : z ∈ ReferenceFirstCollectionActiveBoundaryQueueQuery.queueEvent
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) s u t1) :
    z ∈ ReferenceFirstCollectionActiveBoundaryQueueQuery.queueEvent
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) s u t0 := by
  have h0 := (active_boundary_backward
    (s := s) (u := u) (t0 := t0) (t1 := t1) z hs hu ht h1).1
  obtain ⟨pair0, hm0, _⟩ := ReferenceFirstCollectionActiveBoundaryQueueQuery.existsUnique_matching
    (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
    s u t0 hs hu z h0
  obtain ⟨pair1, hm1, _⟩ := ReferenceFirstCollectionActiveBoundaryQueueQuery.existsUnique_matching
    (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
    s u t1 hs (hu.trans ht) z h1
  rcases hq1 with ⟨_, N, c, hmevent, hall⟩
  have hsame := ReferenceFirstCollectionActiveBoundaryQueueQuery.matches_unique
    s u t1 (ReferenceCompleteNumericalBranchObservation.completeBranchObservation
      rate rewards C_star C_h z) hmevent hm1
  have hN : N = pair1.1 := congrArg Prod.fst hsame
  have hall1 : ReferenceFirstCollectionActiveBoundaryQueueQuery.allPrefixes rate
      (ReferenceFirstCollectionActiveBoundaryQueueQuery.numericalArrivals rate pair1.1) := by
    simpa only [hN] using hall
  have hwhole := whole_matches_prefix rate t0 t1 hs hu ht
    (ReferenceCompleteNumericalBranchObservation.completeBranchObservation
      rate rewards C_star C_h z) pair0.1 pair1.1 pair0.2 pair1.2 hm0 hm1
  have hlen : pair0.1.length ≤ pair1.1.length := by
    rw [hm0.1, hm1.1]
    omega
  have hlist : pair0.1 = pair1.1.take pair0.1.length := by
    have htake := congrArg (List.take pair0.1.length) hwhole
    simpa [List.take_take, List.take_append_of_le_length hlen] using htake
  have hnum : ReferenceFirstCollectionActiveBoundaryQueueQuery.numericalArrivals
      rate pair0.1 =
        (ReferenceFirstCollectionActiveBoundaryQueueQuery.numericalArrivals
          rate pair1.1).take pair0.1.length := by
    rw [hlist]
    unfold ReferenceFirstCollectionActiveBoundaryQueueQuery.numericalArrivals
    rw [List.map_take]
    simp [List.length_take, Nat.min_eq_left hlen]
  have hall0 : ReferenceFirstCollectionActiveBoundaryQueueQuery.allPrefixes rate
      (ReferenceFirstCollectionActiveBoundaryQueueQuery.numericalArrivals rate pair0.1) := by
    intro n hn a
    have htake : (ReferenceFirstCollectionActiveBoundaryQueueQuery.numericalArrivals
        rate pair0.1).take n =
      (ReferenceFirstCollectionActiveBoundaryQueueQuery.numericalArrivals
        rate pair1.1).take n := by
      rw [hnum, List.take_take]
      rw [Nat.min_eq_left (by
        simpa only [ReferenceFirstCollectionActiveBoundaryQueueQuery.numericalArrivals,
          List.length_map] using hn)]
    have hn1 : n ≤ (ReferenceFirstCollectionActiveBoundaryQueueQuery.numericalArrivals
        rate pair1.1).length := by
      have hn' : n ≤ pair0.1.length := by
        simpa only [ReferenceFirstCollectionActiveBoundaryQueueQuery.numericalArrivals,
          List.length_map] using hn
      simpa only [ReferenceFirstCollectionActiveBoundaryQueueQuery.numericalArrivals,
        List.length_map] using le_trans hn' hlen
    have hsafe := hall1 n hn1 a
    simpa only [ReferenceFirstCollectionActiveBoundaryQueueQuery.allPrefixes, htake] using hsafe
  exact ⟨h0, pair0.1, pair0.2, hm0, hall0⟩

/-- If the first overflow is exactly the current earlier cell, the actual
queue event holds there and fails at every later active date. -/
theorem actual_current_first_crossing
    {s u : ℕ} {t0 t1 : Fin p.T} {z : Source (p := p)}
    (hs : s ≤ u) (hu : u ≤ t0.val) (ht : t0.val < t1.val)
    (h1 : z ∈ C rate rewards C_star C_h s u t1)
    (N0 : List (Cell (p := p))) (c0 : Cell (p := p))
    (hm0 : ReferenceFirstCollectionActiveBoundaryQueueQuery.Matches rate s u t0
      (ReferenceCompleteNumericalBranchObservation.completeBranchObservation
        rate rewards C_star C_h z) N0 c0)
    (hcross0 : UnstoppedRecordedQueueComparison.firstOverflowPrefix
      (ReferenceFirstLaunchNumericalCell.queueParameters rate) (N0 ++ [c0]) =
        N0.length + 1) :
    z ∈ ReferenceFirstCollectionActiveBoundaryQueueQuery.queueEvent
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) s u t0 ∧
    z ∉ ReferenceFirstCollectionActiveBoundaryQueueQuery.queueEvent
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) s u t1 := by
  have h0 := (active_boundary_backward
    (s := s) (u := u) (t0 := t0) (t1 := t1) z hs hu (Nat.le_of_lt ht) h1).1
  obtain ⟨pair1, hm1, _⟩ := ReferenceFirstCollectionActiveBoundaryQueueQuery.existsUnique_matching
    (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
    s u t1 hs (hu.trans (Nat.le_of_lt ht)) z h1
  have hwhole := whole_matches_prefix rate t0 t1 hs hu
    (Nat.le_of_lt ht)
    (ReferenceCompleteNumericalBranchObservation.completeBranchObservation
      rate rewards C_star C_h z) N0 pair1.1 c0 pair1.2 hm0 hm1
  have hprefix : N0 ++ [c0] =
      (pair1.1 ++ [pair1.2]).take (N0 ++ [c0]).length := by
    simpa only [List.length_append, List.length_singleton] using hwhole
  have hstable := first_crossing_date_stable rate s (N0 ++ [c0])
      (pair1.1 ++ [pair1.2]) hprefix (by
        rw [hcross0]
        simp only [List.length_append, List.length_singleton]
        omega)
  have hq0 := ReferenceFirstCollectionActiveBoundaryQueueQuery.queueEvent_iff_before_current_firstOverflow
    (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
    s u t0 hs hu z h0 N0 c0 hm0
  have hq1 := ReferenceFirstCollectionActiveBoundaryQueueQuery.queueEvent_iff_before_current_firstOverflow
    (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
    s u t1 hs (hu.trans (Nat.le_of_lt ht)) z h1 pair1.1 pair1.2 hm1
  have hlen : N0.length < pair1.1.length := by
    rw [hm0.1, hm1.1]
    omega
  constructor
  · apply hq0.mpr
    rw [hcross0]
    omega
  · intro hq
    have hbefore := hq1.mp hq
    rw [hstable.1, hcross0] at hbefore
    omega

end Bandits.Support.ReferenceFirstCollectionQueuePrefixChronology

end
