/-
Copyright (c) 2026 The Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteLaterCollectionCalendarWord

import Mathlib.Tactic

/-!
# Original numerical prefix through a later LIVE collection

This internal conditional splice extends an already present original numerical
prefix through the actual later LIVE interval and, when the actual first cutoff
is retained, through that first collection segment.  It preserves the literal
optional-cell construction, the original execution, and the existing calendar
readout APIs.  It assumes no incoming queue, history, collection success, or
future coverage.

Sources: ZIP4 `appendix_a_local_protocol.tex:28-64`,
`06_interruptions.tex:192-233,246-299`, and
`04_slow_fast_learner.tex:157-174`.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions
open ReferenceActivePhysicalStep
open ReferenceActivePhysicalHorizon
open RecordedQueueRun
open CoordinatorRoundDispatch
open ReferenceCollectionSegmentExtraction
open ReferenceCompleteLaterLiveComplementPrefixReplay
open ReferenceCompleteLaterCollectionCalendarWord
open ReferenceFirstCollectionCorrectedSliceNumericalPrefix
open ReferenceFirstCollectionCurrentRetainedGate
open ReferenceLaterLiveNumericalReadout
open ReferenceLaterCollectionArrivalReadout
open CollectionBufferProvenance
open CollectionKnownQueueContinuation
open CoordinatorCollectionLedger
open CoordinatorRecorderComplementBridge
open ReferenceCollectionRawBufferHistory

namespace Bandits.Support.ReferenceCompleteLaterLiveCollectionPrefixExtension

variable {p : ConstructorDimensions.Parameters}

private theorem mapM_id_eq_map_some {α : Type*} :
    ∀ {xs : List (Option α)} {ys : List α},
      xs.mapM id = some ys → xs = ys.map some := by
  intro xs
  induction xs with
  | nil =>
      intro ys h
      cases ys with
      | nil => rfl
      | cons y ys => simp [List.mapM_nil] at h
  | cons x xs ih =>
      intro ys h
      cases hx : x with
      | none =>
          simp [List.mapM_cons, hx] at h
      | some a =>
          cases ht : xs.mapM id with
          | none => simp [List.mapM_cons, hx, ht] at h
          | some tail =>
              have hys : a :: tail = ys := by
                simpa [List.mapM_cons, hx, ht] using h
              cases hys
              have htail := ih ht
              simp [htail]

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

private theorem cell0_complete_observation
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (c : RecordedQueueRun.RoundInput p.K)
    (hc : ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r = some c) :
    (ReferenceCompleteNumericalBranchObservation.branchReadout rate 0 r).map
      (Sum.elim id id) = some (ReferenceCompleteNumericalBranchObservation.encodeNumerical c) := by
  have hproj := ReferenceCompleteNumericalBranchObservation.branch_readout_projections
    rate 0 r
  cases hl : ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r with
  | some live =>
      have hlive : live = c := by
        simp [ReferenceFirstCollectionCurrentRetainedGate.cell0, hl] at hc
        exact hc
      have hleft : ReferenceCompleteNumericalBranchObservation.leftProjection
          (ReferenceCompleteNumericalBranchObservation.branchReadout rate 0 r) =
          some (ReferenceCompleteNumericalBranchObservation.encodeNumerical c) := by
        have h := congrArg Prod.fst hproj
        simpa only [hl, Option.map_some, Function.comp_apply, hlive] using h
      cases hb : ReferenceCompleteNumericalBranchObservation.branchReadout rate 0 r with
      | none => simp [hb, ReferenceCompleteNumericalBranchObservation.leftProjection] at hleft
      | some branch =>
          cases branch with
          | inl value =>
              have hv : value = ReferenceCompleteNumericalBranchObservation.encodeNumerical c := by
                simpa [hb, ReferenceCompleteNumericalBranchObservation.leftProjection] using hleft
              simp [hv]
          | inr value =>
              simp [hb, ReferenceCompleteNumericalBranchObservation.leftProjection] at hleft
  | none =>
      have hcollection : ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 r =
          some c := by
        simpa [ReferenceFirstCollectionCurrentRetainedGate.cell0, hl] using hc
      have hright : ReferenceCompleteNumericalBranchObservation.rightProjection
          (ReferenceCompleteNumericalBranchObservation.branchReadout rate 0 r) =
          some (ReferenceCompleteNumericalBranchObservation.encodeNumerical c) := by
        have h := congrArg Prod.snd hproj
        simpa only [hl, hcollection, Option.map_some, Function.comp_apply] using h
      cases hb : ReferenceCompleteNumericalBranchObservation.branchReadout rate 0 r with
      | none => simp [hb, ReferenceCompleteNumericalBranchObservation.rightProjection] at hright
      | some branch =>
          cases branch with
          | inl value =>
              simp [hb, ReferenceCompleteNumericalBranchObservation.rightProjection] at hright
          | inr value =>
              have hv : value = ReferenceCompleteNumericalBranchObservation.encodeNumerical c := by
                simpa [hb, ReferenceCompleteNumericalBranchObservation.rightProjection] using hright
              simp [hv]

private theorem complete_observation_slot
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (c : RecordedQueueRun.RoundInput p.K)
    (hc : ReferenceFirstCollectionCurrentRetainedGate.cell0 rate
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val] =
        some c) :
    let Omega := ReferenceCompleteNumericalBranchObservation.completeBranchObservation
      rate rewards C_star C_h z
    (Omega[k.val]'(by simp [Omega,
      ReferenceCompleteNumericalBranchObservation.completeBranchObservation,
      ReferenceCompleteNumericalBranchObservation.branchCalendar])).1 =
        (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val].input.time ∧
    ((Omega[k.val]'(by simp [Omega,
      ReferenceCompleteNumericalBranchObservation.completeBranchObservation,
      ReferenceCompleteNumericalBranchObservation.branchCalendar])).2.2).map
        (Sum.elim id id) = some (ReferenceCompleteNumericalBranchObservation.encodeNumerical c) := by
  dsimp only
  constructor
  · simp only [ReferenceCompleteNumericalBranchObservation.completeBranchObservation,
      ReferenceCompleteNumericalBranchObservation.branchCalendar, List.getElem_map]
  · simpa only [ReferenceCompleteNumericalBranchObservation.completeBranchObservation,
      ReferenceCompleteNumericalBranchObservation.branchCalendar, List.getElem_map] using
        (cell0_complete_observation rate _ c hc)

private theorem take_append_prefix {α : Type*} (P A : List α) (b i : ℕ)
    (hP : P.length = b) :
    (P ++ A).take (b + i) = P ++ A.take i := by
  simp [List.take_append, hP]

private theorem present_prefix_length
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (P : List (RecordedQueueRun.RoundInput p.K))
    (hP : ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
      rate rewards C_star C_h
        (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + b.val) z = some P) :
    P.length = b.val := by
  have hlaunch := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs_launch
    rate rewards C_star C_h
      (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + b.val) z P hP
  have hP' := hP
  rw [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs,
    ite_eq_left hlaunch] at hP'
  change (((ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate z rewards C_star C_h).take ((ReferenceCompletePhysicalHistory.physicalStart
      rate z rewards C_star C_h + b.val) -
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)).map
        (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate)).mapM id = some P at hP'
  have hsub : (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + b.val) -
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h = b.val := by
    omega
  rw [hsub] at hP'
  have hmap : ((ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).take b.val).map
        (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate) = P.map some :=
    mapM_id_eq_map_some hP'
  have hlen := congrArg List.length hmap
  have hb : b.val ≤ (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length := Nat.le_of_lt b.isLt
  simp only [List.length_map, List.length_take, Nat.min_eq_left hb] at hlen
  omega

private theorem present_prefix_append_live
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
        (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + b.val) z = some P) :
    let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
      rate rewards C_star C_h z b.val
    let A := ReferenceCompleteLaterLiveComplementPrefixReplay.prefixCells
      rewards C_star C_h z b r0 q0 beta hstate hlater
    let e := b.val + W.length
    let H := P ++ A
    P.length = b.val ∧
    e ≤ (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).length ∧
    ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + e ≤ p.T ∧
    H.length = e ∧ H.take b.val = P ∧
    (∀ h, b.val ≤ h → h ≤ e →
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
        rate rewards C_star C_h
          (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + h) z =
            some (H.take h)) := by
  dsimp only
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
    rate rewards C_star C_h z b.val
  let A := ReferenceCompleteLaterLiveComplementPrefixReplay.prefixCells
    rewards C_star C_h z b r0 q0 beta hstate hlater
  let e := b.val + W.length
  let H := P ++ A
  have hPlen : P.length = b.val :=
    present_prefix_length rate rewards C_star C_h z b P hP
  have hWlen : W.length = A.length :=
    (ReferenceCompleteLaterLiveComplementPrefixReplay.prefixCells_length
      rewards C_star C_h z b r0 q0 beta hstate hlater).symm
  have hbound : e ≤ R.length := by
    dsimp [e, W, R]
    exact ReferenceCompleteLaterLiveComplementPrefixReplay.prefix_length_le
      rewards C_star C_h z b
  have htime : s + e ≤ p.T := by
    have hlen := ReferenceCompletePhysicalHistory.completeSuffixRecords_length rate z rewards C_star C_h
    have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T rate z rewards C_star C_h
    dsimp [e, R] at hbound ⊢
    omega
  have hlength : H.length = e := by
    simp [H, hPlen, hWlen, e]
  have htake : H.take b.val = P := by
    simp [H, hPlen]
  have hprefix : ∀ i, i ≤ W.length →
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
        rate rewards C_star C_h (s + b.val + i) z = some (P ++ A.take i) := by
    intro i
    induction i with
    | zero =>
        intro _
        simpa only [Nat.add_zero, List.take_zero, List.append_nil, s] using hP
    | succ i ih =>
        intro hi
        have hilt : i < W.length := by omega
        have hindex : b.val + i < R.length := by
          have hlin : b.val + i < b.val + W.length := by omega
          omega
        have hAidx : i < A.length := by omega
        have hread := ReferenceCompleteLaterLiveComplementPrefixReplay.prefixCells_readout
          rewards C_star C_h z b r0 q0 beta hstate hlater ⟨i, by simpa [W] using hilt⟩
        have hrecord : W[i]'(by simpa [W] using hilt) = R[b.val + i]'hindex :=
          ReferenceCompleteLaterLiveComplementPrefixReplay.prefix_index
            rewards C_star C_h z b i (by simpa [W] using hilt)
        rw [hrecord] at hread
        have hcell := live_cell0 rate s (R[b.val + i]'hindex)
          (A[i]'(by simpa [A] using hAidx)) hread
        have hlookupR : R[b.val + i]? = some (R[b.val + i]'hindex) :=
          List.getElem?_eq_getElem hindex
        have hsub : (s + b.val + i) -
            ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h =
              b.val + i := by
          dsimp only [s]
          omega
        have hlookup :
            (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords
                rate rewards C_star C_h z)[(s + b.val + i) -
                ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart
                  rate rewards C_star C_h z]? = some (R[b.val + i]'hindex) := by
          simp [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords,
            ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart, hsub, R, hlookupR]
        have happ := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs_append_one
          rate rewards C_star C_h (s + b.val + i) z (P ++ A.take i)
          (ih (by omega)) (R[b.val + i]'hindex)
          (A[i]'(by simpa [A] using hAidx)) hlookup hcell
        have htakeA : A.take i ++ [A[i]'(by simpa [A] using hAidx)] = A.take (i + 1) :=
          List.take_concat_get' A i (by simpa [A] using hAidx)
        have hlist : (P ++ A.take i) ++ [A[i]'(by simpa [A] using hAidx)] =
            P ++ A.take (i + 1) := by
          rw [List.append_assoc, htakeA]
        have hdate : (s + b.val + i) + 1 = s + b.val + (i + 1) := by omega
        simpa only [hdate, hlist] using happ
  refine ⟨hPlen, hbound, htime, hlength, htake, ?_⟩
  intro h hb he
  have hi : h = b.val + (h - b.val) := by omega
  rw [hi]
  have he' : h ≤ b.val + W.length := by simpa [e] using he
  have hslice := hprefix (h - b.val) (by omega)
  rw [take_append_prefix P A b.val (h - b.val) hPlen]
  have hdate : s + b.val + (h - b.val) =
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h +
        (b.val + (h - b.val)) := by
    dsimp [s]
    omega
  rw [hdate] at hslice
  exact hslice

private theorem present_prefix_map_some
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (n : ℕ) (L : List (RecordedQueueRun.RoundInput p.K))
    (hL : ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
      rate rewards C_star C_h n z = some L) :
    ((ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).take
      (n - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)).map
        (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate) = L.map some := by
  have hlaunch := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs_launch
    rate rewards C_star C_h n z L hL
  have hL' := hL
  rw [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs,
    ite_eq_left hlaunch] at hL'
  change (((ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate z rewards C_star C_h).take (n -
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)).map
        (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate)).mapM id = some L at hL'
  exact mapM_id_eq_map_some hL'

private theorem take_before_append {α : Type*} (L M : List α) (n : ℕ)
    (hn : n ≤ L.length) : (L ++ M).take n = L.take n := by
  simp [List.take_append, Nat.sub_eq_zero_of_le hn]

private theorem take_through_segment {α : Type*} (R seg tail : List α) (e : ℕ)
    (hpart : seg ++ tail = R.drop e) (he : e ≤ R.length) :
    R.take (e + seg.length) = R.take e ++ seg := by
  calc
    R.take (e + seg.length) = (R.take e ++ R.drop e).take (e + seg.length) := by
      rw [List.take_append_drop]
    _ = R.take e ++ (R.drop e).take seg.length := by
      rw [List.take_append]
      simp [List.length_take, Nat.min_eq_left he]
    _ = R.take e ++ seg := by
      congr 1
      rw [← hpart]
      simp

/-- Extend the literal initialized numerical prefix through the actual
later-LIVE interval and through its first retained collection segment.  The
incoming numerical prefix is the only prefix invariant: its cells are still
the original optional cells from the same complete suffix.  The full accepted
calendar-word result is returned unchanged, and the cutoff branch appends its
actual `Dword` to the same `H`. -/
theorem complete_later_live_collection_prefix_extension
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
        (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + b.val) z = some P) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
      rate rewards C_star C_h z b.val
    let A := ReferenceCompleteLaterLiveComplementPrefixReplay.prefixCells
      rewards C_star C_h z b r0 q0 beta hstate hlater
    let e := b.val + W.length
    let H := P ++ A
    P.length = b.val ∧ e ≤ R.length ∧ s + e ≤ p.T ∧ H.length = e ∧ H.take b.val = P ∧
    (∀ h, b.val ≤ h → h ≤ e →
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
        rate rewards C_star C_h (s + h) z = some (H.take h)) ∧
    (∀ i : Fin W.length,
      let r := R[b.val + i.val]'(by
        have hlen := ReferenceCompleteLaterLiveComplementPrefixReplay.prefix_length_le
          rewards C_star C_h z b
        change b.val + W.length ≤ R.length at hlen
        omega)
      let c := A[i.val]'(by
        rw [ReferenceCompleteLaterLiveComplementPrefixReplay.prefixCells_length
          rewards C_star C_h z b r0 q0 beta hstate hlater]
        exact i.isLt)
      r.input.time.val = s + b.val + i.val ∧
      r.input.rows = z.1.2 ∧
      r.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p z ∧
      r.input.rewards = rewards ∧
      ReferenceLaterLiveNumericalReadout.laterLiveReadout s r = some c ∧
      ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r = some c ∧
      c.enabled = true) ∧
    (∃ (rE : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
      (qE : CoordinatorLiveServiceFinish.OwnedRegisters rE)
      (hp : rE.payload = r0.payload),
      (∀ hpos : 0 < W.length,
        (W[W.length - 1]'(by omega)).output.next.coordinator = .live rE qE beta) ∧
      (∀ he : e < R.length, (R[e]'he).input.state.coordinator = .live rE qE beta) ∧
      (∀ j : CanonicalFastSampling.FastArm r0.payload.slowSet,
        let jE : CanonicalFastSampling.FastArm rE.payload.slowSet :=
          ⟨j.val, by simpa only [hp] using j.property⟩
        (rE.complementScores jE, qE.queue jE) =
          QueueReplay.replay (4 * rate.n) (r0.complementScores j, q0.queue j)
            ((A.take W.length).map fun c => (c.enabled,
              RecordedQueueRun.quantizedArrival
                (ReferenceFirstLaunchNumericalCell.queueParameters rate) c j.val)) ∧
        qE.previousService jE =
          if W.length = 0 then q0.previousService j
          else
            (QueueReplay.replay (4 * rate.n) (r0.complementScores j, q0.queue j)
              ((A.take W.length).map fun c => (c.enabled,
                RecordedQueueRun.quantizedArrival
                  (ReferenceFirstLaunchNumericalCell.queueParameters rate) c j.val))).1 -
            (QueueReplay.replay (4 * rate.n) (r0.complementScores j, q0.queue j)
              ((A.take (W.length - 1)).map fun c => (c.enabled,
                RecordedQueueRun.quantizedArrival
                  (ReferenceFirstLaunchNumericalCell.queueParameters rate) c j.val))).1) ∧
      (e = R.length ∨
        ∃ (he : e < R.length)
          (chosen : CoordinatorRoundDispatch.LiveOutcome (liveInput (R[e]'he).input rE qE beta)),
          chosen = CoordinatorRoundDispatch.dispatchLive (liveInput (R[e]'he).input rE qE beta) ∧
          (R[e]'he).output.preparation.coordinator = .live rE qE beta chosen ∧
          match chosen with
          | .cutoffChosen _dispatched _ledgerProof ledger _ _ _ _ _ _ _ =>
            let cut := R[e]'he
            let t := cut.input.time
            let l0 := sharedLedger ledger
            t.val + 1 = s + e + 1 ∧
            t.val + 1 = FollowerCutoffScan.firstCutoff p rate.eta.val r0.payload.sigma
              (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
                (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z))) ∧
            ∃ (seg : Segment rate) (I : Initializer p)
              (Dword : List (RecordedQueueRun.RoundInput p.K)) (hD : Dword.length = seg.records.length),
              segmentAt R e = some seg ∧ seg.entry = cut ∧
              seg.context.payload = r0.payload ∧ seg.context.preLedger = l0 ∧
              seg.context.initializer = some I ∧
              I = cutoffInitializer (liveRegistersAt rE t) (liveOwnedAt rE qE t) beta t ∧
              I.checkedStart rate = .success l0 ∧
              I.assignment.arm = r0.payload.assignment.assigned ∧
              I.sigma = r0.payload.sigma.val + 1 ∧ I.cutoff = s + e + 1 ∧
              I.cutoff = FollowerCutoffScan.firstCutoff p rate.eta.val r0.payload.sigma
                (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
                  (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z))) ∧
              I.freezeAt = rE.gridBoundary ∧ I.base = beta ∧
              ReferenceCollectionPhaseHistory.cutoffChosen seg.entry.input = true ∧
              (∃ tail, seg.records = cut :: tail) ∧
              seg.records ++ seg.remaining = R.drop e ∧ seg.exit = exitOf seg.remaining ∧
              CollectionCheckedExecution.startAndRunChecked p rate.eta.val rate.eta.property
                (ReferenceUpReception.sourceCap_forLedger rate) rate.n rate.n_scale
                I.assignment I.sigma I.cutoff I.freezeAt I.base I.outside seg.inputs =
                  .success ⟨l0, seg.accepted, seg.final⟩ ∧
              e + seg.records.length ≤ R.length ∧ s + (e + seg.records.length) ≤ p.T ∧
              (∀ j : Fin seg.records.length,
                let r := seg.records[j.val]
                let c := Dword[j.val]'(by omega)
                R[e + j.val]? = some r ∧
                r.input.time.val = s + (e + j.val) ∧
                r.input.rows = z.1.2 ∧
                r.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p z ∧
                r.input.rewards = rewards ∧
                ∃ done : CompletedRound rate,
                  extractRound r = some done ∧
                  laterCollectionReadout s r = some c ∧
                  ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r = some c ∧
                  done.context.payload = r0.payload ∧
                    CollectionBufferProvenance.collectionContext done.context.preLedger =
                      CollectionBufferProvenance.collectionContext l0 ∧
                  c.enabled = collectionEnabled l0 r.input.time ∧
                  c.enabled = decide (r.input.time.val + 1 < l0.freezeAt) ∧
                  c.rate = r0.payload.rate ∧
                  c.reward = (fun a => ((rewards r.input.time a).val : ℝ) / (D p : ℝ)) ∧
                  (c.enabled = false → c.recordedArm = none ∧ ∀ a,
                    RecordedQueueRun.quantizedArrival
                      (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a = 0) ∧
                  ∃ out : CoordinatorRecordingOperation.Output p,
                    laterCollectionCall s r =
                      some ⟨done.context.payload, done.context.preLedger,
                        done.context.started, done.context.weights⟩ ∧
                    CoordinatorRecorderComplementBridge.run
                      (collectionRecordingInput r.output.preparation done.context.payload
                        done.context.started done.context.weights) = some out ∧
                    r.output.coordinator.recording = some out ∧ out.gateArm = c.recordedArm ∧
                    (∀ a, CoordinatorCollectionLedger.localArrival (rawDiagnostic r) a =
                      RecordedQueueRun.quantizedArrival
                        (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a) ∧
                  (∀ a, Bandits.Support.ReferenceCollectionRawBufferHistory.physicalQueueRecord l0 a r = (c.enabled,
                      RecordedQueueRun.quantizedArrival
                        (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a)) ∧
                    (∀ a, CoordinatorCollectionLedger.localQueueRecord l0 done.input.round
                      done.input.enabled done.input.raw a =
                        Bandits.Support.ReferenceCollectionRawBufferHistory.physicalQueueRecord l0 a r) ∧
                    done.context.started.clock.g = l0.freezeAt) ∧
              seg.records.map (laterCollectionReadout s) = Dword.map some ∧
              (∀ a, CollectionKnownQueueContinuation.inputQueueRecords l0 a seg.inputs =
                  seg.records.map (Bandits.Support.ReferenceCollectionRawBufferHistory.physicalQueueRecord l0 a) ∧
                seg.records.map (Bandits.Support.ReferenceCollectionRawBufferHistory.physicalQueueRecord l0 a) =
                  Dword.map (fun c => (c.enabled,
                    RecordedQueueRun.quantizedArrival
                      (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a))) ∧
              (∀ (Dother : List (RecordedQueueRun.RoundInput p.K))
                (hlen : Dother.length = seg.records.length),
                (∀ j : Fin seg.records.length,
                  laterCollectionReadout s seg.records[j.val] =
                    some (Dother[j.val]'(by omega))) → Dother = Dword) ∧
              (let E := H ++ Dword
               let v := e + seg.records.length
               E.length = v ∧ E.take e = H ∧ E.take b.val = P ∧
               v ≤ R.length ∧ s + v ≤ p.T ∧
               R.take v = R.take e ++ seg.records ∧
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
               (∀ i : Fin A.length, A[i.val].enabled = true) ∧
               (∀ j : Fin Dword.length,
                 Dword[j.val].enabled = false → Dword[j.val].recordedArm = none ∧ ∀ a,
                   RecordedQueueRun.quantizedArrival
                     (ReferenceFirstLaunchNumericalCell.queueParameters rate)
                     Dword[j.val] a = 0))
          | _ => False)) := by
  classical
  intro R s W A e H
  have hbase := present_prefix_append_live rate rewards C_star C_h z b r0 q0 beta
    hstate hlater P hP
  dsimp only at hbase
  rcases hbase with ⟨hPlen, hbound, htime, hHlen, hHtake, hprefix⟩
  have hWbound : b.val + W.length ≤ R.length := by
    simpa [e] using hbound
  have hLiveSlots : ∀ i : Fin W.length,
      let r := R[b.val + i.val]'(by omega)
      let c := A[i.val]'(by
        rw [ReferenceCompleteLaterLiveComplementPrefixReplay.prefixCells_length
          rewards C_star C_h z b r0 q0 beta hstate hlater]
        exact i.isLt)
      r.input.time.val = s + b.val + i.val ∧
      r.input.rows = z.1.2 ∧
      r.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p z ∧
      r.input.rewards = rewards ∧
      ReferenceLaterLiveNumericalReadout.laterLiveReadout s r = some c ∧
      ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r = some c ∧
      c.enabled = true := by
    intro i
    dsimp only
    have hindex : b.val + i.val < R.length := by omega
    have hAindex : i.val < A.length := by
      rw [ReferenceCompleteLaterLiveComplementPrefixReplay.prefixCells_length
        rewards C_star C_h z b r0 q0 beta hstate hlater]
      exact i.isLt
    have hread := ReferenceCompleteLaterLiveComplementPrefixReplay.prefixCells_readout
      rewards C_star C_h z b r0 q0 beta hstate hlater i
    have hrecord := ReferenceCompleteLaterLiveComplementPrefixReplay.prefix_index
      rewards C_star C_h z b i.val i.isLt
    rw [hrecord] at hread
    have hc := live_cell0 rate s (R[b.val + i.val]'hindex)
      (A[i.val]'hAindex) hread
    have hsource := ReferenceLaterCollectionArrivalReadout.sourceIndexedReadout_inputs
      rate rewards C_star C_h z ⟨b.val + i.val, hindex⟩
    have hdate := ReferenceLaterCollectionArrivalReadout.sourceIndexedReadout_time
      rate rewards C_star C_h z ⟨b.val + i.val, hindex⟩
    have henabled := (ReferenceLaterLiveNumericalReadout.laterLiveReadout_numerical
      s (R[b.val + i.val]'hindex) (A[i.val]'hAindex) hread).1
    refine ⟨?_, ?_, ?_, ?_, hread, hc, henabled⟩
    · simpa [s, Nat.add_assoc] using hdate
    · simpa using hsource.1
    · simpa using hsource.2.1
    · simpa using hsource.2.2
  have hrootAll := ReferenceCompleteLaterCollectionCalendarWord.complete_later_live_collection_calendar_word
    rate rewards C_star C_h z b
  have hroot := hrootAll
  dsimp only at hroot
  split at hroot
  next rB qB betaB hBstate =>
    have hfields := CoordinatorConfiguration.live.inj (hBstate.symm.trans hstate)
    have hrB : rB = r0 := hfields.1
    have hqB := hfields.2.1
    have hbetaB := hfields.2.2
    subst rB
    cases hqB
    subst betaB
    have hrootLive := hroot hlater
    rcases hrootLive with
      ⟨_hrootBound, _hrootTime, rE, qE, hp, hlast, hin, hvalues, halt⟩
    refine ⟨hPlen, hbound, htime, hHlen, hHtake, hprefix, hLiveSlots,
      rE, qE, hp, hlast, hin, hvalues, ?_⟩
    rcases halt with hterminal | ⟨he, chosen, hdispatch, hprep, hcut⟩
    · exact Or.inl hterminal
    · refine Or.inr ⟨he, chosen, hdispatch, hprep, ?_⟩
      cases chosen with
      | cutoffChosen dispatched hstart ledger hinit hcand hdomain hclock hpending hnone selected =>
          obtain ⟨hdate, hscan, seg, I, Dword, hD, hat, hentry, hpay, hledger,
            hI, hIeq, hchecked, harm, hsigma, hcutoff, hscanI, hfreeze, hbaseI,
            hchosen, hne, hpart, hexit, hfold, hv, ht, hcover, hmap, hsync, hunique⟩ := hcut
          let cut := R[e]'he
          let t := cut.input.time
          let l0 := sharedLedger ledger
          have hentry' : seg.entry = cut := by simpa [cut, hpay] using hentry
          have hledger' : seg.context.preLedger = l0 := by simpa [l0] using hledger
          have hIeq' : I = cutoffInitializer (liveRegistersAt rE t) (liveOwnedAt rE qE t) beta t :=
            by simpa [cut, t, hpay] using hIeq
          have hchecked' : I.checkedStart rate = .success l0 := by simpa [l0] using hchecked
          refine ⟨hdate, hscan, seg, I, Dword, hD, hat, ?_⟩
          refine ⟨hentry', ?_⟩
          refine ⟨hpay, ?_⟩
          refine ⟨hledger', ?_⟩
          refine ⟨hI, ?_⟩
          refine ⟨hIeq', ?_⟩
          refine ⟨hchecked', ?_⟩
          refine ⟨harm, ?_⟩
          refine ⟨hsigma, ?_⟩
          refine ⟨hcutoff, ?_⟩
          refine ⟨hscanI, ?_⟩
          refine ⟨hfreeze, ?_⟩
          refine ⟨hbaseI, ?_⟩
          refine ⟨hchosen, ?_⟩
          refine ⟨hne, ?_⟩
          refine ⟨hpart, ?_⟩
          refine ⟨hexit, ?_⟩
          refine ⟨hfold, ?_⟩
          refine ⟨hv, ?_⟩
          refine ⟨ht, ?_⟩
          refine ⟨hcover, ?_⟩
          refine ⟨hmap, ?_⟩
          refine ⟨hsync, ?_⟩
          refine ⟨hunique, ?_⟩
          let E := H ++ Dword
          let v := e + seg.records.length
          have hHlen' : H.length = e := by
            simpa [H, e, A, W] using hHlen
          have hsegPrefix : ∀ j, j ≤ seg.records.length →
              ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
                rate rewards C_star C_h (s + e + j) z = some (H ++ Dword.take j) := by
            intro j hj
            induction j with
            | zero =>
                have hbaseEnd := hprefix e (by omega) (by rfl)
                have hHfull : H.take e = H := List.take_of_length_le (by omega)
                change ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
                  rate rewards C_star C_h (s + e) z = some (H.take e) at hbaseEnd
                rw [hHfull] at hbaseEnd
                simpa [s] using hbaseEnd
            | succ j ih =>
                have hjlt : j < seg.records.length := by omega
                have hjFin : j < seg.records.length := hjlt
                let r := seg.records[j]'hjFin
                let c := Dword[j]'(by omega)
                have hslot := hcover ⟨j, hjFin⟩
                have hRlookup : R[e + j]? = some r := by
                  simpa only [r] using hslot.1
                have hcell : ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r = some c := by
                  have htail := hslot.2.2.2.2.2
                  rcases htail with ⟨done, _hext, _hread, hcell, _hmore⟩
                  simpa only [c] using hcell
                have hsub : (s + e + j) -
                    ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h =
                      e + j := by
                  dsimp [s]
                  omega
                have hlookup :
                    (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords
                      rate rewards C_star C_h z)[(s + e + j) -
                      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart
                        rate rewards C_star C_h z]? = some r := by
                  simpa [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords,
                    ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart,
                    hsub, R] using hRlookup
                have happ := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs_append_one
                  rate rewards C_star C_h (s + e + j) z (H ++ Dword.take j)
                  (ih (by omega)) r c hlookup hcell
                have htakeD : Dword.take j ++ [Dword[j]'(by omega)] =
                    Dword.take (j + 1) := by
                  exact List.take_concat_get' Dword j (by omega)
                have hlist : (H ++ Dword.take j) ++ [Dword[j]'(by omega)] =
                    H ++ Dword.take (j + 1) := by
                  calc
                    (H ++ Dword.take j) ++ [Dword[j]'(by omega)] =
                        H ++ (Dword.take j ++ [Dword[j]'(by omega)]) := List.append_assoc ..
                    _ = H ++ Dword.take (j + 1) := by rw [htakeD]
                have hdate' : (s + e + j) + 1 = s + e + (j + 1) := by omega
                rw [← hdate']
                rw [← hlist]
                exact happ
          have hElen : E.length = v := by
            change (H ++ Dword).length = e + seg.records.length
            simp only [List.length_append]
            omega
          have hEtake : E.take e = H := by
            change (H ++ Dword).take e = H
            calc
              (H ++ Dword).take e = H.take e :=
                List.take_append_of_le_length (by omega)
              _ = H := List.take_of_length_le (by omega)
          have hEtakeP : E.take b.val = P := by
            calc
              E.take b.val = H.take b.val := take_before_append H Dword b.val (by
                rw [hHlen']
                omega)
              _ = P := hHtake
          have hVbound : v ≤ R.length := by omega
          have hVtime : s + v ≤ p.T := by omega
          have hRtake : R.take v = R.take e ++ seg.records :=
            take_through_segment R seg.records seg.remaining e hpart (by omega)
          have hprefixAll : ∀ h, b.val ≤ h → h ≤ v →
              ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
                rate rewards C_star C_h (s + h) z = some (E.take h) := by
            intro h hb hvh
            by_cases hle : h ≤ e
            · have hsmall := hprefix h hb hle
              have hEtakeSmall : E.take h = H.take h :=
                take_before_append H Dword h (by rw [hHlen']; exact hle)
              rw [hEtakeSmall]
              exact hsmall
            · have heh : e ≤ h := Nat.le_of_not_ge hle
              let j := h - e
              have hj : j ≤ seg.records.length := by dsimp [j, v] at hvh; omega
              have hsp := hsegPrefix j hj
              have hdate' : s + e + j = s + h := by dsimp [j]; omega
              rw [hdate'] at hsp
              have htakeE : E.take h = H ++ Dword.take j := by
                have hEq : h = e + j := by dsimp [j]; omega
                change (H ++ Dword).take h = H ++ Dword.take j
                rw [hEq]
                exact take_append_prefix H Dword e j hHlen'
              rw [htakeE]
              exact hsp
          have hfull0 := hsegPrefix seg.records.length (by omega)
          rw [Nat.add_assoc] at hfull0
          have hfull : ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
              rate rewards C_star C_h (s + v) z = some E := by
            simpa [E, v, List.take_of_length_le, hD] using hfull0
          have hsub : (s + v) -
              ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h = v := by
            dsimp [s]
            omega
          have hmapFull0 := present_prefix_map_some rate rewards C_star C_h z (s + v) E hfull
          have hmapFull : (R.take v).map
              (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate) = E.map some := by
            simpa [R, hsub] using hmapFull0
          refine ⟨hElen, ?_⟩
          refine ⟨hEtake, ?_⟩
          refine ⟨hEtakeP, ?_⟩
          refine ⟨hVbound, ?_⟩
          refine ⟨hVtime, ?_⟩
          refine ⟨hRtake, ?_⟩
          refine ⟨hprefixAll, ?_⟩
          refine ⟨?_, ?_⟩
          · intro hV hE k
            let r := R[k.val]'(Nat.lt_of_lt_of_le k.isLt hV)
            have hcIndex : k.val < E.length := by rw [hE]; exact k.isLt
            let c := E[k.val]'hcIndex
            have hidxMap : k.val < ((R.take v).map
                (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate)).length := by
              simp only [List.length_map, List.length_take]
              change k.val < min v R.length
              rw [Nat.min_eq_left hV]
              exact k.isLt
            have hidxE : k.val < (E.map some).length := by
              simp only [List.length_map]
              exact hcIndex
            have hget := congrArg
              (fun xs : List (Option (RecordedQueueRun.RoundInput p.K)) => xs[k.val]?) hmapFull
            have hgetR : R[k.val]? = some r := by simp [r]
            have hgetE : E[k.val]? = some c := by simp [c]
            simp only [List.getElem?_map] at hget
            rw [List.getElem?_take_of_lt k.isLt, hgetR, hgetE, Option.map_some] at hget
            have hcell : ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r = some c := by
              exact Option.some.inj hget
            have hdate : r.input.time.val = s + k.val := by
              simpa [r] using ReferenceLaterCollectionArrivalReadout.sourceIndexedReadout_time
                rate rewards C_star C_h z ⟨k.val, Nat.lt_of_lt_of_le k.isLt hV⟩
            have hobs := complete_observation_slot rate rewards C_star C_h z
              ⟨k.val, Nat.lt_of_lt_of_le k.isLt hV⟩ c hcell
            exact ⟨hcell, hdate, hobs.1, hobs.2⟩
          · refine ⟨?_, ?_⟩
            · intro i
              have hAlen : A.length = W.length :=
                ReferenceCompleteLaterLiveComplementPrefixReplay.prefixCells_length
                  rewards C_star C_h z b r0 q0 beta hstate hlater
              have hiW : i.val < W.length := by
                rw [← hAlen]
                exact i.isLt
              let iW : Fin W.length := ⟨i.val, hiW⟩
              rcases hLiveSlots iW with ⟨_, _, _, _, _, _, henabled⟩
              exact henabled
            · intro j
              have hjSeg : j.val < seg.records.length := by rw [← hD]; exact j.isLt
              have hslot := hcover ⟨j.val, hjSeg⟩
              have htail := hslot.2.2.2.2.2
              rcases htail with ⟨done, _hext, _hread, _hcell, _hpayload, _hbuffer,
                _henabled, _hdate, _hrate, _hreward, hdisabled, _hout⟩
              simpa only using hdisabled
      | _ => exact hcut
  next hother =>
    exact False.elim (hother r0 q0 beta hstate)

end Bandits.Support.ReferenceCompleteLaterLiveCollectionPrefixExtension

end
