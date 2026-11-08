/-
Copyright (c) 2026 The Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.HandoverStoppedDecoderReplay
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Lean.Elab.Tactic.Omega

/-!
# Calendar quota for the literal stopped DOWN handover replay

This module proves the deterministic receiver and service quotas for the exact
stopped replay in `HandoverStoppedDecoderReplay`. Physical live-round data,
cutoff flags, overflow flags, and the relation of those inputs to the replay
remain explicit. Source inputs are
`sources/zip4/manuscript/05_binary_transport.tex:244-281`,
`sources/zip4/manuscript/06_interruptions.tex:164-175`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:141-157`.

The receiver calendar count is uncapped. Its proof follows the actual
`roundStep` chronology: at most one mixed batch can clear while the receiver
continues awaiting, and a full fresh batch accepts the current record or stops
for the decoder's literal ambiguity failure. Confirmation is counted only
from the incoming accepted-unconfirmed phase. This is an internal conditional
quota result; it does not assert physical reachability or manuscript closure.
-/

@[expose] public section

namespace Bandits.Support.HandoverStoppedServiceQuota

open ConstructorDimensions
open AffineChannelLaw
open OrdinaryMessageCodec
open ActiveRoundActions
open ActiveObservationBridge
open HandoverStoppedDecoderReplay
open scoped BigOperators

/-- The receiver summand, classified by the incoming replay phase. -/
noncomputable def receiverTermAt (p : Parameters) (beta : ℝ)
    (a : Assignment p.m p.K)
    (live : Fin p.T → LiveRoundData a (AffineBatchDecoder.width p))
    (cutoffBefore overflowAfter : Fin p.T → Bool) (i : Follower p.m)
    (fixing : Fin p.T) (M : Down p beta) (s : LocalState p) (t : Fin p.T) : ℕ :=
  let data := fromLive p a live cutoffBefore overflowAfter
  let incoming := snapshotBefore p beta a data i fixing M s t.val
  if incoming.phase = .awaitingDown then J p a data fixing incoming t * X p a data i incoming t
  else 0

/-- The confirmation summand, classified by the incoming replay phase. -/
noncomputable def confirmationTermAt (p : Parameters) (beta : ℝ)
    (a : Assignment p.m p.K)
    (live : Fin p.T → LiveRoundData a (AffineBatchDecoder.width p))
    (cutoffBefore overflowAfter : Fin p.T → Bool) (i : Follower p.m)
    (fixing : Fin p.T) (M : Down p beta) (s : LocalState p) (t : Fin p.T) : ℕ :=
  let data := fromLive p a live cutoffBefore overflowAfter
  let incoming := snapshotBefore p beta a data i fixing M s t.val
  if incoming.phase = .acceptedUnconfirmed then
    J p a data fixing incoming t * X p a data i incoming t
  else 0

/-- Uncapped receiver subcount of the existing literal `J * X` calendar sum.
Indices beyond the finite horizon contribute zero. -/
noncomputable def receiverCalendarCount (p : Parameters) (beta : ℝ)
    (a : Assignment p.m p.K)
    (live : Fin p.T → LiveRoundData a (AffineBatchDecoder.width p))
    (cutoffBefore overflowAfter : Fin p.T → Bool) (i : Follower p.m)
    (fixing : Fin p.T) (M : Down p beta) (s : LocalState p) (n : ℕ) : ℕ :=
  ∑ r ∈ Finset.range n, if hr : r < p.T then
    receiverTermAt p beta a live cutoffBefore overflowAfter i fixing M s ⟨r, hr⟩ else 0

/-- Uncapped confirmation subcount of the same literal `J * X` calendar sum.
It uses the incoming accepted-unconfirmed phase. -/
noncomputable def confirmationCalendarCount (p : Parameters) (beta : ℝ)
    (a : Assignment p.m p.K)
    (live : Fin p.T → LiveRoundData a (AffineBatchDecoder.width p))
    (cutoffBefore overflowAfter : Fin p.T → Bool) (i : Follower p.m)
    (fixing : Fin p.T) (M : Down p beta) (s : LocalState p) (n : ℕ) : ℕ :=
  ∑ r ∈ Finset.range n, if hr : r < p.T then
    confirmationTermAt p beta a live cutoffBefore overflowAfter i fixing M s ⟨r, hr⟩ else 0

private theorem roundPrefix_map_val (p : Parameters) (n : ℕ) :
    (AffineBatchDecoder.roundPrefix p n).map Fin.val = List.range (min n p.T) := by
  classical
  have hfull : (List.ofFn (fun t : Fin p.T => t)).map Fin.val = List.range p.T := by
    rw [← List.ofFn_comp' (f := fun t : Fin p.T => t) (g := Fin.val)]
    simp [List.ofFn_eq_pmap]
  calc
    (AffineBatchDecoder.roundPrefix p n).map Fin.val =
        ((List.ofFn (fun t : Fin p.T => t)).filter
          (fun t => decide (t.val < n))).map Fin.val := rfl
    _ = (List.range p.T).filter (fun r => decide (r < n)) := by
      have hm := List.map_filter (p := fun t : Fin p.T => decide (t.val < n))
        Fin.val_injective (List.ofFn (fun t : Fin p.T => t))
      rw [hm, hfull]
      apply List.filter_congr
      intro r hr
      have hrT : r < p.T := List.mem_range.mp hr
      rw [Bool.eq_iff_iff]
      simp only [decide_eq_true_eq]
      constructor
      · rintro ⟨t, ht, htr⟩
        simpa [htr] using ht
      · intro hrn
        exact ⟨⟨r, hrT⟩, hrn, rfl⟩
    _ = List.range (min n p.T) := by
      induction p.T with
      | zero => simp
      | succ T ih =>
          rw [List.range_succ, List.filter_append]
          by_cases h : T < n
          · simp [h, ih, min_eq_right (Nat.le_of_lt h), List.range_succ]
          · have hn : n ≤ T := by omega
            rw [ih]
            simp [h, min_eq_left hn]
            rw [min_eq_left (Nat.le_trans hn (Nat.le_succ T))]

private theorem roundPrefix_succ (p : Parameters) (n : ℕ) (hn : n < p.T) :
    AffineBatchDecoder.roundPrefix p (n + 1) =
      AffineBatchDecoder.roundPrefix p n ++ [⟨n, hn⟩] := by
  have hmap :
      (AffineBatchDecoder.roundPrefix p (n + 1)).map Fin.val =
      (AffineBatchDecoder.roundPrefix p n ++ [(⟨n, hn⟩ : Fin p.T)]).map Fin.val := by
    rw [List.map_append, List.map_singleton, roundPrefix_map_val, roundPrefix_map_val,
      min_eq_left (Nat.succ_le_of_lt hn), min_eq_left (Nat.le_of_lt hn), List.range_succ]
  exact (List.map_injective_iff.mpr Fin.val_injective) hmap

private theorem snapshotBefore_zero (p : Parameters) (beta : ℝ)
    (a : Assignment p.m p.K)
    (data : Fin p.T → RoundData p a) (i : Follower p.m) (fixing : Fin p.T)
    (M : Down p beta) (s : LocalState p) :
    snapshotBefore p beta a data i fixing M s 0 = s := by
  have hprefix : AffineBatchDecoder.roundPrefix p 0 = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro t ht
    have h := (AffineBatchDecoder.mem_roundPrefix p 0 t).mp ht
    omega
  rw [snapshotBefore, hprefix, run]

private theorem snapshotBefore_succ (p : Parameters) (beta : ℝ)
    (a : Assignment p.m p.K) (data : Fin p.T → RoundData p a)
    (i : Follower p.m) (fixing : Fin p.T) (M : Down p beta)
    (s : LocalState p) (n : ℕ) (hn : n < p.T) :
    snapshotBefore p beta a data i fixing M s (n + 1) =
      roundStep p beta a data i fixing M
        (snapshotBefore p beta a data i fixing M s n) ⟨n, hn⟩ := by
  unfold snapshotBefore
  rw [roundPrefix_succ p n hn, run_append]
  rfl

private theorem range_fin_sum (T n : ℕ) (f : Fin T → ℕ) :
    (∑ r ∈ Finset.range n, if hr : r < T then f ⟨r, hr⟩ else 0) =
      ∑ t : Fin T, if t.val < n then f t else 0 := by
  classical
  let g : ℕ → ℕ := fun r => if hr : r < T then if r < n then f ⟨r, hr⟩ else 0 else 0
  have hleft :
      (∑ r ∈ Finset.range n, if hr : r < T then f ⟨r, hr⟩ else 0) =
        ∑ r ∈ Finset.range n, g r := by
    apply Finset.sum_congr rfl
    intro r hr
    have hrn : r < n := Finset.mem_range.mp hr
    by_cases hrT : r < T <;> simp [g, hrn, hrT]
  have hright :
      (∑ t : Fin T, if t.val < n then f t else 0) =
        ∑ r ∈ Finset.range T, g r := by
    calc
      (∑ t : Fin T, if t.val < n then f t else 0) =
          ∑ t : Fin T, g t.val := by
            apply Finset.sum_congr rfl
            intro t ht
            have htT : t.val < T := t.isLt
            by_cases htn : t.val < n <;> simp [g, htT, htn]
      _ = ∑ r ∈ Finset.range T, g r := Fin.sum_univ_eq_sum_range g T
  by_cases h : n ≤ T
  · have hsub : Finset.range n ⊆ Finset.range T := Finset.range_subset_range.mpr h
    have hzero : ∀ r ∈ Finset.range T, r ∉ Finset.range n → g r = 0 := by
      intro r hrT hrn
      have hn : n ≤ r := Nat.le_of_not_gt (fun hlt => hrn (Finset.mem_range.mpr hlt))
      simp [g, not_lt.mpr hn]
    calc
      (∑ r ∈ Finset.range n, if hr : r < T then f ⟨r, hr⟩ else 0) =
          ∑ r ∈ Finset.range n, g r := hleft
      _ = ∑ r ∈ Finset.range T, g r := Finset.sum_subset hsub hzero
      _ = ∑ t : Fin T, if t.val < n then f t else 0 := hright.symm
  · have h : T ≤ n := Nat.le_of_not_ge h
    have hsub : Finset.range T ⊆ Finset.range n := Finset.range_subset_range.mpr h
    have hzero : ∀ r ∈ Finset.range n, r ∉ Finset.range T → g r = 0 := by
      intro r hrn hrT
      have hT : T ≤ r := Nat.le_of_not_gt (fun hlt => hrT (Finset.mem_range.mpr hlt))
      simp [g, not_lt.mpr hT]
    calc
      (∑ r ∈ Finset.range n, if hr : r < T then f ⟨r, hr⟩ else 0) =
          ∑ r ∈ Finset.range n, g r := hleft
      _ = ∑ r ∈ Finset.range T, g r := (Finset.sum_subset hsub hzero).symm
      _ = ∑ t : Fin T, if t.val < n then f t else 0 := hright.symm

private theorem receiverCalendarCount_succ (p : Parameters) (beta : ℝ)
    (a : Assignment p.m p.K)
    (live : Fin p.T → LiveRoundData a (AffineBatchDecoder.width p))
    (cutoffBefore overflowAfter : Fin p.T → Bool) (i : Follower p.m)
    (fixing : Fin p.T) (M : Down p beta) (s : LocalState p)
    (n : ℕ) (hn : n < p.T) :
    receiverCalendarCount p beta a live cutoffBefore overflowAfter i fixing M s (n + 1) =
      receiverCalendarCount p beta a live cutoffBefore overflowAfter i fixing M s n +
        receiverTermAt p beta a live cutoffBefore overflowAfter i fixing M s ⟨n, hn⟩ := by
  unfold receiverCalendarCount
  rw [Finset.sum_range_succ]
  simp only [dite_eq_left hn]

private theorem confirmationCalendarCount_succ (p : Parameters) (beta : ℝ)
    (a : Assignment p.m p.K)
    (live : Fin p.T → LiveRoundData a (AffineBatchDecoder.width p))
    (cutoffBefore overflowAfter : Fin p.T → Bool) (i : Follower p.m)
    (fixing : Fin p.T) (M : Down p beta) (s : LocalState p)
    (n : ℕ) (hn : n < p.T) :
    confirmationCalendarCount p beta a live cutoffBefore overflowAfter i fixing M s (n + 1) =
      confirmationCalendarCount p beta a live cutoffBefore overflowAfter i fixing M s n +
        confirmationTermAt p beta a live cutoffBefore overflowAfter i fixing M s ⟨n, hn⟩ := by
  unfold confirmationCalendarCount
  rw [Finset.sum_range_succ]
  simp only [dite_eq_left hn]

private theorem receiverCalendarCount_stable (p : Parameters) (beta : ℝ)
    (a : Assignment p.m p.K)
    (live : Fin p.T → LiveRoundData a (AffineBatchDecoder.width p))
    (cutoffBefore overflowAfter : Fin p.T → Bool) (i : Follower p.m)
    (fixing : Fin p.T) (M : Down p beta) (s : LocalState p)
    (n : ℕ) (hn : p.T ≤ n) :
    receiverCalendarCount p beta a live cutoffBefore overflowAfter i fixing M s n =
      receiverCalendarCount p beta a live cutoffBefore overflowAfter i fixing M s p.T := by
  unfold receiverCalendarCount
  symm
  apply Finset.sum_subset (Finset.range_subset_range.mpr hn)
  intro r hr hnot
  have hrT : ¬ r < p.T := by
    intro hrt
    exact hnot (Finset.mem_range.mpr hrt)
  simp [hrT]

private theorem confirmationCalendarCount_stable (p : Parameters) (beta : ℝ)
    (a : Assignment p.m p.K)
    (live : Fin p.T → LiveRoundData a (AffineBatchDecoder.width p))
    (cutoffBefore overflowAfter : Fin p.T → Bool) (i : Follower p.m)
    (fixing : Fin p.T) (M : Down p beta) (s : LocalState p)
    (n : ℕ) (hn : p.T ≤ n) :
    confirmationCalendarCount p beta a live cutoffBefore overflowAfter i fixing M s n =
      confirmationCalendarCount p beta a live cutoffBefore overflowAfter i fixing M s p.T := by
  unfold confirmationCalendarCount
  symm
  apply Finset.sum_subset (Finset.range_subset_range.mpr hn)
  intro r hr hnot
  have hrT : ¬ r < p.T := by
    intro hrt
    exact hnot (Finset.mem_range.mpr hrt)
  simp [hrT]

private theorem receiverCalendarCount_finSum (p : Parameters) (beta : ℝ)
    (a : Assignment p.m p.K)
    (live : Fin p.T → LiveRoundData a (AffineBatchDecoder.width p))
    (cutoffBefore overflowAfter : Fin p.T → Bool) (i : Follower p.m)
    (fixing : Fin p.T) (M : Down p beta) (s : LocalState p) (n : ℕ) :
    receiverCalendarCount p beta a live cutoffBefore overflowAfter i fixing M s n =
      ∑ t : Fin p.T, if t.val < n then
        let data := fromLive p a live cutoffBefore overflowAfter
        let incoming := snapshotBefore p beta a data i fixing M s t.val
        if incoming.phase = .awaitingDown then J p a data fixing incoming t *
          X p a data i incoming t else 0 else 0 := by
  simpa only [receiverCalendarCount, receiverTermAt] using
    range_fin_sum p.T n (receiverTermAt p beta a live cutoffBefore overflowAfter i fixing M s)

private theorem confirmationCalendarCount_finSum (p : Parameters) (beta : ℝ)
    (a : Assignment p.m p.K)
    (live : Fin p.T → LiveRoundData a (AffineBatchDecoder.width p))
    (cutoffBefore overflowAfter : Fin p.T → Bool) (i : Follower p.m)
    (fixing : Fin p.T) (M : Down p beta) (s : LocalState p) (n : ℕ) :
    confirmationCalendarCount p beta a live cutoffBefore overflowAfter i fixing M s n =
      ∑ t : Fin p.T, if t.val < n then
        let data := fromLive p a live cutoffBefore overflowAfter
        let incoming := snapshotBefore p beta a data i fixing M s t.val
        if incoming.phase = .acceptedUnconfirmed then J p a data fixing incoming t *
          X p a data i incoming t else 0 else 0 := by
  simpa only [confirmationCalendarCount, confirmationTermAt] using
    range_fin_sum p.T n
      (confirmationTermAt p beta a live cutoffBefore overflowAfter i fixing M s)

/-- Exact decomposition of the existing stopped replay service sum into its
incoming receiver and genuine confirmation subcounts. -/
theorem N_before_decomposition (p : Parameters) (beta : ℝ)
    (a : Assignment p.m p.K)
    (live : Fin p.T → LiveRoundData a (AffineBatchDecoder.width p))
    (cutoffBefore overflowAfter : Fin p.T → Bool) (i : Follower p.m)
    (fixing : Fin p.T) (M : Down p beta) (s : LocalState p) (n : ℕ) :
    N_before p beta a (fromLive p a live cutoffBefore overflowAfter) i fixing M s n =
      receiverCalendarCount p beta a live cutoffBefore overflowAfter i fixing M s n +
        confirmationCalendarCount p beta a live cutoffBefore overflowAfter i fixing M s n := by
  classical
  rw [N_before, receiverCalendarCount_finSum, confirmationCalendarCount_finSum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  by_cases htn : t.val < n
  · simp only [ite_eq_left htn]
    let data := fromLive p a live cutoffBefore overflowAfter
    let incoming := snapshotBefore p beta a data i fixing M s t.val
    cases hp : incoming.phase <;> simp [receiverTermAt, confirmationTermAt, incoming, data, hp, X]
  · simp only [ite_eq_right htn]

private theorem roundPrefix_stable (p : Parameters) (n : ℕ) (hn : p.T ≤ n) :
    AffineBatchDecoder.roundPrefix p n = AffineBatchDecoder.roundPrefix p p.T := by
  have hmap :
      (AffineBatchDecoder.roundPrefix p n).map Fin.val =
        (AffineBatchDecoder.roundPrefix p p.T).map Fin.val := by
    rw [roundPrefix_map_val, roundPrefix_map_val, min_eq_right hn, min_eq_left le_rfl]
  exact (List.map_injective_iff.mpr Fin.val_injective) hmap

private theorem confirmationTermAt_eq_tick (p : Parameters) (beta : ℝ)
    (a : Assignment p.m p.K)
    (live : Fin p.T → LiveRoundData a (AffineBatchDecoder.width p))
    (cutoffBefore overflowAfter : Fin p.T → Bool) (i : Follower p.m)
    (fixing : Fin p.T) (M : Down p beta) (s : LocalState p) (t : Fin p.T) :
    confirmationTermAt p beta a live cutoffBefore overflowAfter i fixing M s t =
      confirmationTick p a (fromLive p a live cutoffBefore overflowAfter) i fixing
        (snapshotBefore p beta a (fromLive p a live cutoffBefore overflowAfter) i fixing M s t.val) t := by
  classical
  let data := fromLive p a live cutoffBefore overflowAfter
  let incoming := snapshotBefore p beta a data i fixing M s t.val
  cases hphase : incoming.phase with
  | awaitingDown => simp [confirmationTermAt, confirmationTick, incoming, data, hphase]
  | acceptedUnconfirmed =>
      by_cases hphys : physicalConfirmation p a data i t
      · simp [confirmationTermAt, confirmationTick, J, X, incoming, data, hphase,
          hphys, Phase.unresolved]
      · simp [confirmationTermAt, confirmationTick, J, X, incoming, data, hphase,
          hphys, Phase.unresolved]
  | confirmed => simp [confirmationTermAt, confirmationTick, incoming, data, hphase]
  | failedFalse => simp [confirmationTermAt, confirmationTick, incoming, data, hphase]
  | failedAmbiguous => simp [confirmationTermAt, confirmationTick, incoming, data, hphase]
  | cutoffOrHorizon => simp [confirmationTermAt, confirmationTick, incoming, data, hphase]
  | overflow => simp [confirmationTermAt, confirmationTick, incoming, data, hphase]

private theorem confirmationCount_append_singleton (p : Parameters) (beta : ℝ)
    (a : Assignment p.m p.K) (data : Fin p.T → RoundData p a)
    (i : Follower p.m) (fixing : Fin p.T) (M : Down p beta)
    (ts : List (Fin p.T)) (t : Fin p.T) (s : LocalState p) :
    confirmationCount p beta a data i fixing M (ts ++ [t]) s =
      confirmationCount p beta a data i fixing M ts s +
        confirmationTick p a data i fixing (run p beta a data i fixing M ts s) t := by
  induction ts generalizing s with
  | nil => simp [confirmationCount, run]
  | cons u ts ih =>
      simp [confirmationCount, run, ih, Nat.add_assoc]

private theorem confirmationCalendarCount_eq_replay (p : Parameters) (beta : ℝ)
    (a : Assignment p.m p.K)
    (live : Fin p.T → LiveRoundData a (AffineBatchDecoder.width p))
    (cutoffBefore overflowAfter : Fin p.T → Bool) (i : Follower p.m)
    (fixing : Fin p.T) (M : Down p beta) (s : LocalState p) (n : ℕ) :
    confirmationCalendarCount p beta a live cutoffBefore overflowAfter i fixing M s n =
      confirmationCount p beta a (fromLive p a live cutoffBefore overflowAfter) i fixing M
        (AffineBatchDecoder.roundPrefix p n) s := by
  by_cases hn : n ≤ p.T
  · induction n with
    | zero =>
        have hprefix : AffineBatchDecoder.roundPrefix p 0 = [] := by
          apply List.eq_nil_iff_forall_not_mem.mpr
          intro t ht
          have h := (AffineBatchDecoder.mem_roundPrefix p 0 t).mp ht
          omega
        simp [confirmationCalendarCount, hprefix, confirmationCount]
    | succ n ih =>
        have hn' : n < p.T := Nat.lt_of_succ_le hn
        rw [confirmationCalendarCount_succ p beta a live cutoffBefore overflowAfter i fixing M s n hn']
        rw [roundPrefix_succ p n hn']
        rw [confirmationCount_append_singleton]
        rw [ih (Nat.le_of_lt hn')]
        rw [confirmationTermAt_eq_tick]
        rfl
  · have hT : p.T ≤ n := Nat.le_of_not_ge hn
    rw [confirmationCalendarCount_stable p beta a live cutoffBefore overflowAfter i fixing M s n hT]
    rw [roundPrefix_stable p n hT]
    rw [← confirmationCalendarCount_eq_replay p beta a live cutoffBefore overflowAfter i fixing M s p.T]

private theorem confirmationCalendarCount_le_one (p : Parameters) (beta : ℝ)
    (a : Assignment p.m p.K)
    (live : Fin p.T → LiveRoundData a (AffineBatchDecoder.width p))
    (cutoffBefore overflowAfter : Fin p.T → Bool) (i : Follower p.m)
    (fixing : Fin p.T) (M : Down p beta) (s : LocalState p) (n : ℕ) :
    confirmationCalendarCount p beta a live cutoffBefore overflowAfter i fixing M s n ≤ 1 := by
  rw [confirmationCalendarCount_eq_replay]
  exact confirmationCount_le_one p beta a
    (fromLive p a live cutoffBefore overflowAfter) i fixing M
    (AffineBatchDecoder.roundPrefix p n) s

private theorem confirmationCount_zero_of_run_unresolved (p : Parameters) (beta : ℝ)
    (a : Assignment p.m p.K) (data : Fin p.T → RoundData p a)
    (i : Follower p.m) (fixing : Fin p.T) (M : Down p beta)
    (ts : List (Fin p.T)) (s : LocalState p)
    (h : (run p beta a data i fixing M ts s).phase.unresolved) :
    confirmationCount p beta a data i fixing M ts s = 0 := by
  induction ts generalizing s with
  | nil => rfl
  | cons t ts ih =>
      by_cases hg : fixing.val ≤ t.val ∧ (data t).cutoffBefore = false ∧
          s.phase = .acceptedUnconfirmed ∧ physicalConfirmation p a data i t
      · have hstep := roundStep_confirmation p beta a data i fixing M s t
          hg.1 hg.2.2.1 hg.2.1 hg.2.2.2
        have hterminal : ¬ ({ s with phase := Phase.confirmed } : LocalState p).phase.unresolved := by
          simp [Phase.unresolved]
        have hrun := run_terminal p beta a data i fixing M
          { s with phase := Phase.confirmed } ts hterminal
        rw [run, hstep, hrun] at h
        simp [Phase.unresolved] at h
      · have htick : confirmationTick p a data i fixing s t = 0 := by
          unfold confirmationTick
          by_cases hcond : fixing.val ≤ t.val ∧ (data t).cutoffBefore = false ∧
              s.phase = .acceptedUnconfirmed ∧ physicalConfirmation p a data i t
          · exact False.elim (hg hcond)
          · simp only [ite_eq_right hcond]
        rw [confirmationCount, htick, Nat.zero_add]
        exact ih (roundStep p beta a data i fixing M s t) h

/-- Provenance retained for a positive equation in the fresh batch. -/
private def CurrentEntry (p : Parameters) (beta : ℝ) (a : Assignment p.m p.K)
    (live : Fin p.T → LiveRoundData a (AffineBatchDecoder.width p))
    (i : Follower p.m) (fixing : Fin p.T) (M : Down p beta)
    (e : DecoderEntry p) : Prop :=
  fixing.val ≤ e.time.val ∧
    AffineBatchDecoder.eligible (ActiveObservationBridge.downObservationTrace p a live i e.time) ∧
    e.sample = (live e.time).input.down.sample ∧
    (live e.time).input.down.word = currentWord p beta M

private theorem currentEntry_of_eligible (p : Parameters) (beta : ℝ)
    (a : Assignment p.m p.K)
    (live : Fin p.T → LiveRoundData a (AffineBatchDecoder.width p))
    (i : Follower p.m) (fixing : Fin p.T) (M : Down p beta)
    (hfixed : ∀ t, fixing.val ≤ t.val →
      AffineBatchDecoder.eligible (ActiveObservationBridge.downObservationTrace p a live i t) →
      (live t).input.down.word = currentWord p beta M)
    (t : Fin p.T) (ht : fixing.val ≤ t.val)
    (he : AffineBatchDecoder.eligible (ActiveObservationBridge.downObservationTrace p a live i t)) :
    CurrentEntry p beta a live i fixing M
      (AffineBatchDecoder.entry p (ActiveObservationBridge.downObservationTrace p a live i) t) := by
  refine ⟨ht, he, ?_, hfixed t ht he⟩
  simp [AffineBatchDecoder.entry, ActiveObservationBridge.downObservationTrace]

private theorem currentEntries_wholeCurrentBatch (p : Parameters) (beta : ℝ)
    (a : Assignment p.m p.K)
    (live : Fin p.T → LiveRoundData a (AffineBatchDecoder.width p))
    (cutoffBefore overflowAfter : Fin p.T → Bool) (i : Follower p.m)
    (fixing : Fin p.T) (M : Down p beta)
    (batch : List (DecoderEntry p))
    (hgood : ∀ e ∈ batch, CurrentEntry p beta a live i fixing M e) :
    wholeCurrentBatch p beta a (fromLive p a live cutoffBefore overflowAfter)
      i fixing M batch := by
  intro e he
  obtain ⟨ht, hel, hsamp, hword⟩ := hgood e he
  refine ⟨ht, ?_, ?_, hword⟩
  · rw [observationTrace_fromLive]
    exact hel
  · simpa only [fromLive] using hsamp

private theorem wholeCurrentBatch_satisfies_live (p : Parameters) (beta : ℝ)
    (a : Assignment p.m p.K)
    (live : Fin p.T → LiveRoundData a (AffineBatchDecoder.width p))
    (cutoffBefore overflowAfter : Fin p.T → Bool) (i : Follower p.m)
    (fixing : Fin p.T) (M : Down p beta) (batch : List (DecoderEntry p))
    (hgood : ∀ e ∈ batch, CurrentEntry p beta a live i fixing M e) :
    AffineBatchDecoder.satisfies (AffineBatchDecoder.samples batch) (currentWord p beta M) := by
  exact wholeCurrentBatch_live_satisfies p beta a live cutoffBefore overflowAfter i fixing M batch
    (currentEntries_wholeCurrentBatch p beta a live cutoffBefore overflowAfter i fixing M batch hgood)

/-- Proof invariant for the literal receiver replay. The first alternative
tracks the original partial batch; the second tracks a cleared first batch
followed only by post-fix current-word equations. -/
private def ReceiverInvariant (p : Parameters) (beta : ℝ)
    (a : Assignment p.m p.K)
    (live : Fin p.T → LiveRoundData a (AffineBatchDecoder.width p))
    (cutoffBefore overflowAfter : Fin p.T → Bool) (i : Follower p.m)
    (fixing : Fin p.T) (M : Down p beta)
    (initialDecoder : DecoderState p) (olderStart n : ℕ) (s : LocalState p) : Prop :=
  let q := AffineBatchDecoder.quota p
  let initialLength := initialDecoder.pending.length
  let count := receiverCalendarCount p beta a live cutoffBefore overflowAfter i fixing M
    (initial p initialDecoder olderStart) n
  s.decoder.pending.length < q ∧
    (s.phase = .awaitingDown →
      (∀ e ∈ s.decoder.pending, e ∈ initialDecoder.pending →
        e.time.val < fixing.val) ∧
      (∀ e ∈ s.decoder.pending, e ∈ initialDecoder.pending ∨
        CurrentEntry p beta a live i fixing M e)) ∧
    count ≤ q - initialLength + q ∧
    (s.phase = .awaitingDown →
      s.acceptedStart = olderStart ∧
        (count + initialLength = s.decoder.pending.length ∨
          (count + initialLength = q + s.decoder.pending.length ∧
            ∀ e ∈ s.decoder.pending, CurrentEntry p beta a live i fixing M e)))

private theorem receiverTermAt_eq_one_iff (p : Parameters) (beta : ℝ)
    (a : Assignment p.m p.K)
    (live : Fin p.T → LiveRoundData a (AffineBatchDecoder.width p))
    (cutoffBefore overflowAfter : Fin p.T → Bool) (i : Follower p.m)
    (fixing : Fin p.T) (M : Down p beta) (s : LocalState p) (t : Fin p.T) :
    receiverTermAt p beta a live cutoffBefore overflowAfter i fixing M s t = 1 ↔
      fixing.val ≤ t.val ∧
        (snapshotBefore p beta a (fromLive p a live cutoffBefore overflowAfter)
          i fixing M s t.val).phase = .awaitingDown ∧
        cutoffBefore t = false ∧
        AffineBatchDecoder.eligible
          (observationTrace p a (fromLive p a live cutoffBefore overflowAfter) i t) := by
  classical
  let data := fromLive p a live cutoffBefore overflowAfter
  let incoming := snapshotBefore p beta a data i fixing M s t.val
  cases hp : incoming.phase <;>
    simp [receiverTermAt, J, X, data, incoming, hp, observationTrace_fromLive,
      Phase.unresolved, fromLive, and_left_comm, and_comm]
  all_goals
    by_cases he : AffineBatchDecoder.eligible
        (ActiveObservationBridge.downObservationTrace p a live i t) <;>
      by_cases hf : fixing.val ≤ t.val <;>
      by_cases hc : cutoffBefore t = false <;>
        simp_all

private theorem receiverInvariant_initial (p : Parameters) (beta : ℝ)
    (a : Assignment p.m p.K)
    (live : Fin p.T → LiveRoundData a (AffineBatchDecoder.width p))
    (cutoffBefore overflowAfter : Fin p.T → Bool) (i : Follower p.m)
    (fixing : Fin p.T) (M : Down p beta) (decoder : DecoderState p)
    (olderStart : ℕ) (hquota : decoder.pending.length < AffineBatchDecoder.quota p)
    (_hpending : ∀ e ∈ decoder.pending, e.time.val < fixing.val) :
    ReceiverInvariant p beta a live cutoffBefore overflowAfter i fixing M decoder olderStart 0
      (initial p decoder olderStart) := by
  simp only [ReceiverInvariant, receiverCalendarCount, Finset.range_zero, Finset.sum_empty,
    initial, AffineBatchDecoder.quota]
  refine ⟨hquota, ?_, ?_, ?_⟩
  · intro _
    constructor
    · intro e he _
      exact _hpending e he
    · intro e he
      exact Or.inl he
  · omega
  · intro _
    constructor
    · trivial
    · left
      simp

private theorem receiverTermAt_le_one (p : Parameters) (beta : ℝ)
    (a : Assignment p.m p.K)
    (live : Fin p.T → LiveRoundData a (AffineBatchDecoder.width p))
    (cutoffBefore overflowAfter : Fin p.T → Bool) (i : Follower p.m)
    (fixing : Fin p.T) (M : Down p beta) (s : LocalState p) (t : Fin p.T) :
    receiverTermAt p beta a live cutoffBefore overflowAfter i fixing M s t ≤ 1 := by
  classical
  let data := fromLive p a live cutoffBefore overflowAfter
  let incoming := snapshotBefore p beta a data i fixing M s t.val
  change (if incoming.phase = .awaitingDown then
      J p a data fixing incoming t * X p a data i incoming t else 0) ≤ 1
  by_cases hp : incoming.phase = .awaitingDown
  · simp [hp, J, X, Phase.unresolved]
    split_ifs <;> omega
  · simp [hp]

private theorem roundStep_awaiting_run_prefix (p : Parameters) (beta : ℝ)
    (a : Assignment p.m p.K) (data : Fin p.T → RoundData p a)
    (i : Follower p.m) (fixing : Fin p.T) (M : Down p beta)
    (s : LocalState p) (t : Fin p.T) (ht : fixing.val ≤ t.val)
    (hk : s.decoder.pending.length < AffineBatchDecoder.quota p)
    (h : (roundStep p beta a data i fixing M s t).phase = .awaitingDown) :
    s.phase = .awaitingDown ∧
      (roundStep p beta a data i fixing M s t).acceptedStart = s.acceptedStart ∧
      (roundStep p beta a data i fixing M s t).decoder =
        AffineBatchDecoder.step p (observationTrace p a data i) s.decoder t ∧
      (data t).cutoffBefore = false := by
  have hpref := run_awaiting_prefix p beta a data i fixing M [t] s
    (by intro u hu; simp only [List.mem_singleton] at hu; subst u; exact ht) hk h
  have hdecoder : (roundStep p beta a data i fixing M s t).decoder =
      AffineBatchDecoder.step p (observationTrace p a data i) s.decoder t := by
    simpa only [run, AffineBatchDecoder.run] using hpref.2.2
  have hcut : (data t).cutoffBefore ≠ true := by
    intro hc
    rw [roundStep_cutoff p beta a data i fixing M s t ht (Or.inl hpref.1) hc] at h
    simp at h
  have hcut' : (data t).cutoffBefore = false := by
    cases hb : (data t).cutoffBefore with
    | false => rfl
    | true => exact (hcut hb).elim
  exact ⟨hpref.1, hpref.2.1, hdecoder, hcut'⟩

private theorem receiverInvariant_carry (p : Parameters) (beta : ℝ)
    (a : Assignment p.m p.K)
    (live : Fin p.T → LiveRoundData a (AffineBatchDecoder.width p))
    (cutoffBefore overflowAfter : Fin p.T → Bool) (i : Follower p.m)
    (fixing : Fin p.T) (M : Down p beta) (initialDecoder : DecoderState p)
    (olderStart n : ℕ) (s : LocalState p)
    (hinv : ReceiverInvariant p beta a live cutoffBefore overflowAfter i fixing M
      initialDecoder olderStart n s)
    (hcount : receiverCalendarCount p beta a live cutoffBefore overflowAfter i fixing M
      (initial p initialDecoder olderStart) (n + 1) =
        receiverCalendarCount p beta a live cutoffBefore overflowAfter i fixing M
          (initial p initialDecoder olderStart) n) :
    ReceiverInvariant p beta a live cutoffBefore overflowAfter i fixing M
      initialDecoder olderStart (n + 1) s := by
  simpa only [ReceiverInvariant, hcount] using hinv

private theorem roundStep_no_await_after_fresh_batch (p : Parameters) (beta : ℝ)
    (a : Assignment p.m p.K) (data : Fin p.T → RoundData p a)
    (i : Follower p.m) (fixing : Fin p.T) (M : Down p beta)
    (s : LocalState p) (t : Fin p.T) (ht : fixing.val ≤ t.val)
    (hphase : s.phase = .awaitingDown) (hcut : (data t).cutoffBefore = false)
    (hpos : AffineBatchDecoder.eligible (observationTrace p a data i t))
    (hboundary : s.decoder.pending.length + 1 = AffineBatchDecoder.quota p)
    (hw : wholeCurrentBatch p beta a data i fixing M
      (s.decoder.pending ++ [AffineBatchDecoder.entry p (observationTrace p a data i) t]))
    (hlocal : acceptDown (AffineBatchDecoder.codecParams p beta) s.acceptedStart
      (WaitedWordWindow.sourceRound t) M)
    (hsat : AffineBatchDecoder.satisfies (AffineBatchDecoder.samples
      (s.decoder.pending ++ [AffineBatchDecoder.entry p (observationTrace p a data i) t]))
      (currentWord p beta M)) :
    (roundStep p beta a data i fixing M s t).phase ≠ .awaitingDown := by
  classical
  have hprogress := receiverStep_current_progress p beta a data i fixing M s t
    hpos hboundary hw hlocal hsat
  have hguard : ¬ (t.val < fixing.val ∨ ¬ s.phase.unresolved) :=
    not_or.mpr ⟨Nat.not_lt.mpr ht, not_not.mpr (Or.inl hphase)⟩
  have hcutguard : ¬ (data t).cutoffBefore = true := by
    rw [hcut]
    exact Bool.noConfusion
  have hround : roundStep p beta a data i fixing M s t =
      if (data t).overflowAfter = true ∧
          (receiverStep p beta a data i fixing M s t).phase.unresolved then
        {receiverStep p beta a data i fixing M s t with phase := .overflow}
      else receiverStep p beta a data i fixing M s t := by
    rw [roundStep, ite_eq_right hguard, ite_eq_right hcutguard]
    simp [serviceStep, hphase, hpos]
  intro hawait
  rw [hround] at hawait
  rcases hprogress.2 with haccept | hambiguous
  · cases hover : (data t).overflowAfter <;>
      simp [hover, haccept, Phase.unresolved] at hawait
  · simp [hambiguous, Phase.unresolved] at hawait

private theorem receiverInvariant_succ (p : Parameters) (beta : ℝ)
    (a : Assignment p.m p.K)
    (live : Fin p.T → LiveRoundData a (AffineBatchDecoder.width p))
    (cutoffBefore overflowAfter : Fin p.T → Bool) (i : Follower p.m)
    (fixing : Fin p.T) (M : Down p beta) (initialDecoder : DecoderState p)
    (olderStart : ℕ)
    (hquota : initialDecoder.pending.length < AffineBatchDecoder.quota p)
    (hpending : ∀ e ∈ initialDecoder.pending, e.time.val < fixing.val)
    (hsource : WaitedWordWindow.sourceRound fixing = M.val.sigma)
    (holder : olderStart < M.val.sigma)
    (hfixed : ∀ t, fixing.val ≤ t.val →
      AffineBatchDecoder.eligible (ActiveObservationBridge.downObservationTrace p a live i t) →
      (live t).input.down.word = currentWord p beta M)
    (n : ℕ) (hn : n < p.T)
    (hinv : ReceiverInvariant p beta a live cutoffBefore overflowAfter i fixing M
      initialDecoder olderStart n
      (snapshotBefore p beta a (fromLive p a live cutoffBefore overflowAfter)
        i fixing M (initial p initialDecoder olderStart) n)) :
    ReceiverInvariant p beta a live cutoffBefore overflowAfter i fixing M initialDecoder
      olderStart (n + 1)
      (roundStep p beta a (fromLive p a live cutoffBefore overflowAfter) i fixing M
        (snapshotBefore p beta a (fromLive p a live cutoffBefore overflowAfter)
          i fixing M (initial p initialDecoder olderStart) n) ⟨n, hn⟩) := by
  let data := fromLive p a live cutoffBefore overflowAfter
  let initialState := initial p initialDecoder olderStart
  let s := snapshotBefore p beta a data i fixing M (initial p initialDecoder olderStart) n
  let t : Fin p.T := ⟨n, hn⟩
  let out := roundStep p beta a data i fixing M s t
  have hparts := hinv
  rcases hparts with ⟨hplen, horigin, hbound, hpotential⟩
  have hplenS : s.decoder.pending.length < AffineBatchDecoder.quota p := by
    simpa only [s] using hplen
  have horiginS := fun hs : s.phase = .awaitingDown => by
    have hs' :
        (snapshotBefore p beta a (fromLive p a live cutoffBefore overflowAfter)
          i fixing M (initial p initialDecoder olderStart) n).phase = .awaitingDown := by
      simpa only [s] using hs
    simpa only [s] using horigin hs'
  have hpotentialS := fun hs : s.phase = .awaitingDown => by
    have hs' :
        (snapshotBefore p beta a (fromLive p a live cutoffBefore overflowAfter)
          i fixing M (initial p initialDecoder olderStart) n).phase = .awaitingDown := by
      simpa only [s] using hs
    simpa only [s] using hpotential hs'
  have htermiff :
      receiverTermAt p beta a live cutoffBefore overflowAfter i fixing M (initial p initialDecoder olderStart) t = 1 ↔
        fixing.val ≤ t.val ∧ s.phase = .awaitingDown ∧
          (data t).cutoffBefore = false ∧
          AffineBatchDecoder.eligible (observationTrace p a data i t) := by
    simpa only [s, t, data, fromLive] using
      receiverTermAt_eq_one_iff p beta a live cutoffBefore overflowAfter i fixing M (initial p initialDecoder olderStart) t
  have htermle := receiverTermAt_le_one p beta a live cutoffBefore overflowAfter i fixing M (initial p initialDecoder olderStart) t
  have hcal := receiverCalendarCount_succ p beta a live cutoffBefore overflowAfter i fixing M (initial p initialDecoder olderStart) n hn
  have hcalT : receiverCalendarCount p beta a live cutoffBefore overflowAfter i fixing M
      (initial p initialDecoder olderStart) (n + 1) =
        receiverCalendarCount p beta a live cutoffBefore overflowAfter i fixing M
          (initial p initialDecoder olderStart) n +
          receiverTermAt p beta a live cutoffBefore overflowAfter i fixing M
            (initial p initialDecoder olderStart) t := by
    simpa only [t] using hcal
  have hboundNext :
      receiverCalendarCount p beta a live cutoffBefore overflowAfter i fixing M (initial p initialDecoder olderStart)
        (n + 1) ≤ AffineBatchDecoder.quota p - initialDecoder.pending.length +
          AffineBatchDecoder.quota p := by
    rw [hcalT]
    by_cases hone : receiverTermAt p beta a live cutoffBefore overflowAfter i fixing M (initial p initialDecoder olderStart) t = 1
    · have hEvent := htermiff.mp hone
      rcases hEvent with ⟨_, hphase, _, _⟩
      have hphaseS : s.phase = .awaitingDown := by simpa only [s] using hphase
      rcases hpotentialS hphaseS with ⟨_, hpot⟩
      rcases hpot with hfirst | ⟨hsecond, _⟩ <;> omega
    · have hzero : receiverTermAt p beta a live cutoffBefore overflowAfter i fixing M (initial p initialDecoder olderStart) t = 0 := by omega
      rw [hzero]
      exact hbound
  have hpendingOut := roundStep_pending_lt p beta a data i fixing M s t hplenS
  have hpreserve : out.phase = .awaitingDown →
      out.acceptedStart = olderStart ∧
        (∀ e ∈ out.decoder.pending, e ∈ initialDecoder.pending →
          e.time.val < fixing.val) ∧
        (∀ e ∈ out.decoder.pending, e ∈ initialDecoder.pending ∨
          CurrentEntry p beta a live i fixing M e) ∧
        (receiverCalendarCount p beta a live cutoffBefore overflowAfter i fixing M (initial p initialDecoder olderStart) (n + 1) + initialDecoder.pending.length = out.decoder.pending.length ∨
          (receiverCalendarCount p beta a live cutoffBefore overflowAfter i fixing M (initial p initialDecoder olderStart) (n + 1) + initialDecoder.pending.length =
                AffineBatchDecoder.quota p + out.decoder.pending.length ∧
            ∀ e ∈ out.decoder.pending, CurrentEntry p beta a live i fixing M e)) := by
    intro hout
    by_cases hfix : fixing.val ≤ t.val
    · have ⟨hsphase, hstart, hdecoder, hcut⟩ :=
        roundStep_awaiting_run_prefix p beta a data i fixing M s t hfix hplenS hout
      have hstartOut : out.acceptedStart = s.acceptedStart := by simpa only [out] using hstart
      have hdecoderOut : out.decoder = AffineBatchDecoder.step p
          (observationTrace p a data i) s.decoder t := by simpa only [out] using hdecoder
      have hstartOld := (hpotentialS hsphase).1
      have hstartOldS : s.acceptedStart = olderStart := by
        exact hstartOld
      have hpotOld := (hpotentialS hsphase).2
      by_cases he : AffineBatchDecoder.eligible (observationTrace p a data i t)
      · have hterm : receiverTermAt p beta a live cutoffBefore overflowAfter i fixing M (initial p initialDecoder olderStart) t = 1 := htermiff.mpr ⟨hfix, hsphase, hcut, he⟩
        have hcount : receiverCalendarCount p beta a live cutoffBefore overflowAfter i fixing M (initial p initialDecoder olderStart) (n + 1) =
              receiverCalendarCount p beta a live cutoffBefore overflowAfter i fixing M (initial p initialDecoder olderStart) n + 1 := by rw [hcalT, hterm]
        have hentry : CurrentEntry p beta a live i fixing M
            (AffineBatchDecoder.entry p (observationTrace p a data i) t) := by
          have heLive : AffineBatchDecoder.eligible
              (ActiveObservationBridge.downObservationTrace p a live i t) := by
            rw [← observationTrace_fromLive]
            exact he
          exact currentEntry_of_eligible p beta a live i fixing M hfixed t hfix heLive
        by_cases hsmall : s.decoder.pending.length + 1 < AffineBatchDecoder.quota p
        · have hstepAppend : AffineBatchDecoder.step p (observationTrace p a data i)
              s.decoder t =
              ⟨s.decoder.pending ++ [AffineBatchDecoder.entry p
                (observationTrace p a data i) t], s.decoder.completed⟩ := by
            simp [AffineBatchDecoder.step, AffineBatchDecoder.positiveAt, he, hsmall]
          have hdecoderAppend : out.decoder =
              ⟨s.decoder.pending ++ [AffineBatchDecoder.entry p
                (observationTrace p a data i) t], s.decoder.completed⟩ := by
            rw [hdecoderOut, hstepAppend]
          have hlenAppend : out.decoder.pending.length = s.decoder.pending.length + 1 := by
            simp [hdecoderAppend]
          refine ⟨hstartOut.trans hstartOldS, ?_, ?_, ?_⟩
          · intro e heOut heInitial
            rw [hdecoderAppend] at heOut
            rcases List.mem_append.mp heOut with heOld | heNew
            · exact (horiginS hsphase).1 e heOld heInitial
            · have heNew' := List.mem_singleton.mp heNew
              subst e
              have htimeOld := hpending _ heInitial
              have htimeEntry :
                  (AffineBatchDecoder.entry p (observationTrace p a data i) t).time.val =
                    t.val := rfl
              omega
          · intro e heOut
            rw [hdecoderAppend] at heOut
            rcases List.mem_append.mp heOut with heOld | heNew
            · exact (horiginS hsphase).2 e heOld
            · exact Or.inr (by
                have heNew' := List.mem_singleton.mp heNew
                simpa only [heNew'] using hentry)
          · rcases hpotOld with hfirst | ⟨hsecond, hall⟩
            · left
              rw [hcount, hlenAppend]
              calc
                _ = (receiverCalendarCount p beta a live cutoffBefore overflowAfter i fixing M
                    (initial p initialDecoder olderStart) n + initialDecoder.pending.length) + 1 := by
                      omega
                _ = s.decoder.pending.length + 1 := by rw [hfirst]
            · right
              constructor
              · rw [hcount, hlenAppend]
                calc
                  _ = (receiverCalendarCount p beta a live cutoffBefore overflowAfter i fixing M
                      (initial p initialDecoder olderStart) n + initialDecoder.pending.length) + 1 := by
                        omega
                  _ = (AffineBatchDecoder.quota p + s.decoder.pending.length) + 1 := by rw [hsecond]
                  _ = AffineBatchDecoder.quota p + (s.decoder.pending.length + 1) := by omega
              · intro e heOut
                rw [hdecoderAppend] at heOut
                rcases List.mem_append.mp heOut with heOld | heNew
                · exact hall e heOld
                · have heNew' := List.mem_singleton.mp heNew
                  subst e
                  exact hentry
        · have hboundary : s.decoder.pending.length + 1 =
              AffineBatchDecoder.quota p := by omega
          rcases hpotOld with hfirst | ⟨hsecond, hall⟩
          · have hpositives :
                (AffineBatchDecoder.positives p (observationTrace p a data i) [t]).length =
                  AffineBatchDecoder.quota p - s.decoder.pending.length := by
              simp [AffineBatchDecoder.positives, he]
              omega
            have hclear := awaiting_first_batch_clears p beta a data i fixing M [t] s
              (by intro u hu; simp only [List.mem_singleton] at hu; subst u; exact hfix)
              hplenS hpositives hout
            have hclearOut : out.decoder =
                { pending := [], completed := s.decoder.completed ++
                  [s.decoder.pending ++ AffineBatchDecoder.positives p
                    (observationTrace p a data i) [t]] } := by
              simpa only [out, run] using hclear
            have hpendingEmpty : out.decoder.pending = [] := by simp [hclearOut]
            refine ⟨hstartOut.trans hstartOldS, ?_, ?_, ?_⟩
            · intro e heOut _
              rw [hpendingEmpty] at heOut
              cases heOut
            · intro e heOut
              rw [hpendingEmpty] at heOut
              cases heOut
            · right
              constructor
              · rw [hcount, hpendingEmpty]
                simp only [List.length_nil, Nat.add_zero]
                calc
                  _ = (receiverCalendarCount p beta a live cutoffBefore overflowAfter i fixing M
                      (initial p initialDecoder olderStart) n + initialDecoder.pending.length) + 1 := by
                        omega
                  _ = s.decoder.pending.length + 1 := by rw [hfirst]
                  _ = AffineBatchDecoder.quota p := hboundary
              · intro e heOut
                rw [hpendingEmpty] at heOut
                cases heOut
          · have hcurrent : ∀ e ∈ s.decoder.pending,
                CurrentEntry p beta a live i fixing M e := fun e he => hall e he
            have hbatchCurrent : ∀ e ∈ s.decoder.pending ++
                [AffineBatchDecoder.entry p (observationTrace p a data i) t],
                CurrentEntry p beta a live i fixing M e := by
              intro e heBatch
              rcases List.mem_append.mp heBatch with heOld | heNew
              · exact hcurrent e heOld
              · have heNew' := List.mem_singleton.mp heNew
                subst e
                exact hentry
            have hwhole := currentEntries_wholeCurrentBatch p beta a live cutoffBefore
              overflowAfter i fixing M _ hbatchCurrent
            have hsat := wholeCurrentBatch_satisfies_live p beta a live cutoffBefore
              overflowAfter i fixing M _ hbatchCurrent
            have hlocal : acceptDown (AffineBatchDecoder.codecParams p beta) s.acceptedStart
                (WaitedWordWindow.sourceRound t) M := by
              refine ⟨by rw [hstartOldS]; exact holder, ?_⟩
              unfold WaitedWordWindow.sourceRound at hsource ⊢
              rw [← hsource]
              exact Nat.add_le_add_right hfix 1
            have hnoawait := roundStep_no_await_after_fresh_batch p beta a data i fixing M s t
              hfix hsphase hcut he hboundary hwhole hlocal hsat
            exact (hnoawait hout).elim
      · have hnotEvent : ¬
            (fixing.val ≤ t.val ∧ s.phase = .awaitingDown ∧
              (data t).cutoffBefore = false ∧
              AffineBatchDecoder.eligible (observationTrace p a data i t)) := by
          rintro ⟨_, _, _, hevent⟩
          exact he hevent
        have htermZero : receiverTermAt p beta a live cutoffBefore overflowAfter i fixing M (initial p initialDecoder olderStart) t = 0 := by
          have hne : receiverTermAt p beta a live cutoffBefore overflowAfter i fixing M (initial p initialDecoder olderStart) t ≠ 1 := fun hone => hnotEvent (htermiff.mp hone)
          omega
        have hcountZero : receiverCalendarCount p beta a live cutoffBefore overflowAfter i fixing M (initial p initialDecoder olderStart) (n + 1) =
              receiverCalendarCount p beta a live cutoffBefore overflowAfter i fixing M (initial p initialDecoder olderStart) n := by rw [hcalT, htermZero]; omega
        have hstepIneligible := AffineBatchDecoder.step_ineligible p
          (observationTrace p a data i) s.decoder t hplenS he
        have hdecoderSame : out.decoder = s.decoder := by
          rw [hdecoderOut, hstepIneligible]
        refine ⟨hstartOut.trans hstartOldS, ?_, ?_, ?_⟩
        · intro e heOut heInitial
          rw [hdecoderSame] at heOut
          exact (horiginS hsphase).1 e heOut heInitial
        · intro e heOut
          rw [hdecoderSame] at heOut
          exact (horiginS hsphase).2 e heOut
        · simpa [hdecoderSame, hcountZero] using hpotOld
    · have hpre : t.val < fixing.val := by omega
      have houtSame : out = s := by
        simp [out, roundStep, t, hpre]
      have htermZero : receiverTermAt p beta a live cutoffBefore overflowAfter i fixing M (initial p initialDecoder olderStart) t = 0 := by
        have hne : receiverTermAt p beta a live cutoffBefore overflowAfter i fixing M (initial p initialDecoder olderStart) t ≠ 1 := by
          intro hone
          have hev := htermiff.mp hone
          exact (Nat.not_le_of_gt hpre) hev.1
        omega
      have hcountSame : receiverCalendarCount p beta a live cutoffBefore overflowAfter i fixing M (initial p initialDecoder olderStart) (n + 1) =
            receiverCalendarCount p beta a live cutoffBefore overflowAfter i fixing M (initial p initialDecoder olderStart) n := by
        rw [hcalT, htermZero]
        omega
      rw [houtSame]
      have hcarry := receiverInvariant_carry p beta a live cutoffBefore overflowAfter i fixing M
        initialDecoder olderStart n s hinv hcountSame
      rcases hcarry with ⟨_, hcarryOrigin, _, hcarryPotential⟩
      have hstateAwait : s.phase = .awaitingDown := by
        simpa [houtSame] using hout
      rcases hcarryOrigin hstateAwait with ⟨htime, horigin'⟩
      rcases hcarryPotential hstateAwait with ⟨hstart, hpotential'⟩
      exact ⟨hstart, htime, horigin', hpotential'⟩
  change out.decoder.pending.length < AffineBatchDecoder.quota p ∧
    (out.phase = .awaitingDown →
      (∀ e ∈ out.decoder.pending, e ∈ initialDecoder.pending → e.time.val < fixing.val) ∧
      (∀ e ∈ out.decoder.pending, e ∈ initialDecoder.pending ∨
        CurrentEntry p beta a live i fixing M e)) ∧
    receiverCalendarCount p beta a live cutoffBefore overflowAfter i fixing M (initial p initialDecoder olderStart)
        (n + 1) ≤ AffineBatchDecoder.quota p - initialDecoder.pending.length +
          AffineBatchDecoder.quota p ∧
    (out.phase = .awaitingDown →
      out.acceptedStart = olderStart ∧
        (receiverCalendarCount p beta a live cutoffBefore overflowAfter i fixing M (initial p initialDecoder olderStart)
            (n + 1) + initialDecoder.pending.length = out.decoder.pending.length ∨
          (receiverCalendarCount p beta a live cutoffBefore overflowAfter i fixing M (initial p initialDecoder olderStart)
              (n + 1) + initialDecoder.pending.length =
                AffineBatchDecoder.quota p + out.decoder.pending.length ∧
            ∀ e ∈ out.decoder.pending, CurrentEntry p beta a live i fixing M e)))
  refine ⟨hpendingOut, ?_, hboundNext, ?_⟩
  · intro hout
    rcases hpreserve hout with ⟨_, htime, horigin', _⟩
    exact ⟨htime, horigin'⟩
  · intro hout
    rcases hpreserve hout with ⟨hstart, _, _, hpotential'⟩
    exact ⟨hstart, hpotential'⟩

/-- The uncapped receiver subcount of the existing stopped replay calendar is
at most two actual decoder batches at every natural prefix. The physical
positive-word persistence, original partial-batch length and timestamps,
source-start equality, and strict older-start condition remain explicit. -/
theorem receiverCalendarCount_le_twoQ (p : Parameters) (beta : ℝ)
    (a : Assignment p.m p.K)
    (live : Fin p.T → LiveRoundData a (AffineBatchDecoder.width p))
    (cutoffBefore overflowAfter : Fin p.T → Bool) (i : Follower p.m)
    (fixing : Fin p.T) (M : Down p beta) (olderStart : ℕ)
    (decoder : DecoderState p)
    (hsource : WaitedWordWindow.sourceRound fixing = M.val.sigma)
    (holder : olderStart < M.val.sigma)
    (hquota : decoder.pending.length < AffineBatchDecoder.quota p)
    (hpending : ∀ e ∈ decoder.pending, e.time.val < fixing.val)
    (hfixed : ∀ t, fixing.val ≤ t.val →
      AffineBatchDecoder.eligible (ActiveObservationBridge.downObservationTrace p a live i t) →
      (live t).input.down.word = currentWord p beta M)
    (n : ℕ) :
    receiverCalendarCount p beta a live cutoffBefore overflowAfter i fixing M
      (initial p decoder olderStart) n ≤ 2 * AffineBatchDecoder.quota p := by
  have hprefix : ∀ k, k ≤ p.T →
      ReceiverInvariant p beta a live cutoffBefore overflowAfter i fixing M decoder olderStart k
        (snapshotBefore p beta a (fromLive p a live cutoffBefore overflowAfter)
          i fixing M (initial p decoder olderStart) k) := by
    intro k hk
    induction k with
    | zero =>
        have hinit := receiverInvariant_initial p beta a live cutoffBefore overflowAfter i fixing
          M decoder olderStart hquota hpending
        simpa only [snapshotBefore_zero] using hinit
    | succ k ih =>
        have hklt : k < p.T := by omega
        have hprev := ih (by omega)
        have hstep := receiverInvariant_succ p beta a live cutoffBefore overflowAfter i fixing M
          decoder olderStart hquota hpending hsource holder hfixed k hklt hprev
        simpa only [snapshotBefore_succ p beta a (fromLive p a live cutoffBefore overflowAfter)
          i fixing M (initial p decoder olderStart) k hklt] using hstep
  by_cases hn : n ≤ p.T
  · rcases hprefix n hn with ⟨_, _, hbound, _⟩
    omega
  · have hTn : p.T ≤ n := Nat.le_of_not_ge hn
    rw [receiverCalendarCount_stable p beta a live cutoffBefore overflowAfter i fixing M
      (initial p decoder olderStart) n hTn]
    rcases hprefix p.T le_rfl with ⟨_, _, hbound, _⟩
    omega

/-- The literal stopped service count is bounded by two receiver batches and
one genuine confirmation for every natural prefix, including prefixes past
the finite calendar horizon. -/
theorem N_before_le_twoQ_add_one (p : Parameters) (beta : ℝ)
    (a : Assignment p.m p.K)
    (live : Fin p.T → LiveRoundData a (AffineBatchDecoder.width p))
    (cutoffBefore overflowAfter : Fin p.T → Bool) (i : Follower p.m)
    (fixing : Fin p.T) (M : Down p beta) (olderStart : ℕ)
    (decoder : DecoderState p)
    (hsource : WaitedWordWindow.sourceRound fixing = M.val.sigma)
    (holder : olderStart < M.val.sigma)
    (hquota : decoder.pending.length < AffineBatchDecoder.quota p)
    (hpending : ∀ e ∈ decoder.pending, e.time.val < fixing.val)
    (hfixed : ∀ t, fixing.val ≤ t.val →
      AffineBatchDecoder.eligible (ActiveObservationBridge.downObservationTrace p a live i t) →
      (live t).input.down.word = currentWord p beta M)
    (n : ℕ) :
    N_before p beta a (fromLive p a live cutoffBefore overflowAfter) i fixing M
      (initial p decoder olderStart) n ≤ 2 * AffineBatchDecoder.quota p + 1 := by
  rw [N_before_decomposition]
  have hreceiver := receiverCalendarCount_le_twoQ p beta a live cutoffBefore overflowAfter i
    fixing M olderStart decoder hsource holder hquota hpending hfixed n
  have hconfirmation := confirmationCalendarCount_le_one p beta a live cutoffBefore
    overflowAfter i fixing M (initial p decoder olderStart) n
  omega

/-- If the literal incoming source-calendar indicator is one, the incoming
phase is still unresolved, so the confirmation summand is zero before that
round. This gives the strict terminal-prefix bound. -/
theorem N_before_lt_twoQ_add_one_of_J (p : Parameters) (beta : ℝ)
    (a : Assignment p.m p.K)
    (live : Fin p.T → LiveRoundData a (AffineBatchDecoder.width p))
    (cutoffBefore overflowAfter : Fin p.T → Bool) (i : Follower p.m)
    (fixing : Fin p.T) (M : Down p beta) (olderStart : ℕ)
    (decoder : DecoderState p)
    (hsource : WaitedWordWindow.sourceRound fixing = M.val.sigma)
    (holder : olderStart < M.val.sigma)
    (hquota : decoder.pending.length < AffineBatchDecoder.quota p)
    (hpending : ∀ e ∈ decoder.pending, e.time.val < fixing.val)
    (hfixed : ∀ t, fixing.val ≤ t.val →
      AffineBatchDecoder.eligible (ActiveObservationBridge.downObservationTrace p a live i t) →
      (live t).input.down.word = currentWord p beta M)
    (t : Fin p.T)
    (hJ : J p a (fromLive p a live cutoffBefore overflowAfter) fixing
      (snapshotBefore p beta a (fromLive p a live cutoffBefore overflowAfter)
        i fixing M (initial p decoder olderStart) t.val) t = 1) :
    N_before p beta a (fromLive p a live cutoffBefore overflowAfter) i fixing M
      (initial p decoder olderStart) t.val < 2 * AffineBatchDecoder.quota p + 1 := by
  classical
  let data := fromLive p a live cutoffBefore overflowAfter
  let initialState := initial p decoder olderStart
  let incoming := snapshotBefore p beta a data i fixing M initialState t.val
  have hUnresolved : incoming.phase.unresolved := by
    unfold J at hJ
    split_ifs at hJ with hcondition
    · exact hcondition.2.1
  have hrunUnresolved :
      (run p beta a data i fixing M (AffineBatchDecoder.roundPrefix p t.val) initialState).phase.unresolved := by
    simpa only [incoming, snapshotBefore, data, initialState] using hUnresolved
  have hconfirmationZero : confirmationCalendarCount p beta a live cutoffBefore
      overflowAfter i fixing M initialState t.val = 0 := by
    rw [confirmationCalendarCount_eq_replay]
    exact confirmationCount_zero_of_run_unresolved p beta a data i fixing M
      (AffineBatchDecoder.roundPrefix p t.val) initialState hrunUnresolved
  have hreceiver := receiverCalendarCount_le_twoQ p beta a live cutoffBefore overflowAfter i
    fixing M olderStart decoder hsource holder hquota hpending hfixed t.val
  rw [N_before_decomposition, hconfirmationZero]
  omega

end Bandits.Support.HandoverStoppedServiceQuota

end
