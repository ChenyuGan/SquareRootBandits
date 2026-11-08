/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bandits Lean regret formalization contributors.
-/
module

public import Bandits.Support.ReferenceFirstCollectionFormedUpSourceDetectingCut

/-!
# Actual first-collection UP prefix threshold

A finite collection prefix whose retained UP-positive count reaches the
actual decoder threshold has a first exact attaining record. No stopped quota
or source-level service claim is made.

Sources: `sources/zip4/manuscript/05_binary_transport.tex:27-45`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:151-157`, and
`sources/zip4/manuscript/06_interruptions.tex:476-481`.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support

namespace Bandits.Support.ReferenceFirstCollectionUpPrefixThreshold

variable {p : ConstructorDimensions.Parameters}

private theorem recordUpPositiveEntries_length_le_one
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1)) :
    (ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries record i).length ≤ 1 := by
  classical
  cases hdiagnostic : record.output.coordinator.up with
  | none => simp [ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries, hdiagnostic]
  | some diagnostic =>
      by_cases hselected :
          ReferenceCoordinatorUpDecoderReplay.retainedUpFollower diagnostic = i
      · simp only [ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries,
          hdiagnostic, ite_eq_left hselected]
        unfold AffineBatchDecoder.positiveAt
        split <;> simp
      · simp [ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries,
          hdiagnostic, hselected]

private theorem recordUpPositiveEntries_eq_nil_or_singleton
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1)) :
    ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries record i = [] ∨
      ∃ e, ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries record i = [e] := by
  have hlen := recordUpPositiveEntries_length_le_one record i
  cases hentries : ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries record i with
  | nil => exact Or.inl rfl
  | cons e tail =>
      cases tail with
      | nil => exact Or.inr ⟨e, rfl⟩
      | cons e' tail' =>
          simp [hentries] at hlen

private theorem retainedUpPositiveEntries_take_succ
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (B : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (i : Fin (p.m - 1)) (f a : ℕ) (hfa : f ≤ a) (ha : a < B.length) :
    ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries
        ((B.drop f).take (a + 1 - f)) i =
      ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries
        ((B.drop f).take (a - f)) i ++
        ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries B[a] i := by
  have hindex : a - f < (B.drop f).length := by simp; omega
  have hrecord : (B.drop f)[a - f] = B[a] := by
    simp only [List.getElem_drop]
    congr 1
    omega
  have htake : (B.drop f).take (a + 1 - f) =
      (B.drop f).take (a - f) ++ [B[a]] := by
    rw [show a + 1 - f = (a - f) + 1 by omega,
      List.take_succ_eq_append_getElem hindex, hrecord]
  unfold ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries
  rw [htake, List.flatMap_append]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]

private theorem first_exact_singleton_prefix
    {α : Type}
    (f n H len : ℕ) (P : ℕ → List α)
    (record : (a : ℕ) → a < len → List α)
    (hfn : f ≤ n) (hzero : P f = []) (hpositive : 0 < H)
    (hreached : H ≤ (P n).length) (hlen : n ≤ len)
    (hstep : ∀ a, f ≤ a → (ha : a < n) →
      P (a + 1) = P a ∨
        ∃ e, record a (lt_of_lt_of_le ha hlen) = [e] ∧
          P (a + 1) = P a ++ [e]) :
    ∃ b, f < b ∧ b ≤ n ∧ ∃ q : Fin len,
      q.val + 1 = b ∧ (P b).length = H ∧
      (P q.val).length + 1 = H ∧
      (∀ a : ℕ, f ≤ a → a < b → (P a).length < H) ∧
      ∃ e, record q.val q.isLt = [e] ∧ P b = P q.val ++ [e] := by
  classical
  have hterminalIndex : f + (n - f) = n := by omega
  have hterminal : H ≤ (P (f + (n - f))).length := by
    rw [hterminalIndex]
    exact hreached
  let witness : ∃ k, H ≤ (P (f + k)).length := ⟨n - f, hterminal⟩
  let r := Nat.find witness
  have hr : H ≤ (P (f + r)).length := Nat.find_spec witness
  have hrmin (k : ℕ) (hk : k < r) : (P (f + k)).length < H := by
    have hnot := Nat.find_min witness hk
    omega
  have hrle : r ≤ n - f := Nat.find_min' witness hterminal
  have hrpos : 0 < r := by
    by_contra h
    have hrzero : r = 0 := by omega
    rw [hrzero] at hr
    simp only [Nat.add_zero, hzero, List.length_nil] at hr
    omega
  let b := f + r
  have hfb : f < b := by dsimp [b]; omega
  have hbn : b ≤ n := by dsimp [b]; omega
  have hreachB : H ≤ (P b).length := by simpa only [b] using hr
  have hprev : (P (b - 1)).length < H := by
    have hindex : b - 1 = f + (r - 1) := by dsimp [b]; omega
    rw [hindex]
    exact hrmin (r - 1) (by omega)
  have hstepPrev := hstep (b - 1) (by omega) (by omega)
  have hsuccessor : (b - 1) + 1 = b := by omega
  let q : Fin len := ⟨b - 1, by omega⟩
  have hqsuccessor : q.val + 1 = b := by simp [q]; omega
  have hboundary := hstepPrev
  rcases hboundary with hsame | ⟨e, hrecord, happend⟩
  · have hsame' : P b = P (b - 1) := by simpa only [hsuccessor] using hsame
    rw [hsame'] at hreachB
    omega
  · have happend' : P b = P (b - 1) ++ [e] := by
      simpa only [hsuccessor] using happend
    have hlength : (P b).length = (P (b - 1)).length + 1 := by
      rw [happend']
      simp only [List.length_append, List.length_singleton]
    have hcount : (P b).length = H := by omega
    have hpreviousCount' : (P (b - 1)).length + 1 = H := by omega
    have hpreviousCount : (P q.val).length + 1 = H := by
      simpa only [q, Fin.val_mk] using hpreviousCount'
    have hearliest : ∀ a : ℕ, f ≤ a → a < b → (P a).length < H := by
      intro a haf hab
      have hindex : a - f < r := by dsimp [b] at hab; omega
      have hminimal := hrmin (a - f) hindex
      have hsum : f + (a - f) = a := by omega
      simpa only [hsum] using hminimal
    have hrecordQ : record q.val q.isLt = [e] := by
      simpa only [q, Fin.val_mk] using hrecord
    have happendQ : P b = P q.val ++ [e] := by
      simpa only [q, Fin.val_mk] using happend'
    exact ⟨b, hfb, hbn, q, hqsuccessor, hcount, hpreviousCount,
      hearliest, e, hrecordQ, happendQ⟩

/-- The actual first collection UP-positive prefix reaches its quota-plus-
remainder threshold at one exact retained record. The witness retains the
original full collection window and starts after the physical launch bank. -/
public theorem actual_first_collection_up_first_threshold
    {p : ConstructorDimensions.Parameters}
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (count : ℕ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed + count ≤ p.T) :
    let I := ReferenceFirstCollectionEpochAlignment.actualLaunchState rate z rewards C_star C_h hcross
    let s := ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed
    let active := (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
      rate z rewards C_star C_h hcross).1
    let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
      rate z rewards C_star C_h hcross count hspan
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length
    let B := ReferenceCollectionPhaseHistory.collectionWindow E.records w
    ∀ (i : Fin (p.m - 1)) (f n : ℕ) (hfn : f ≤ n)
      (_hnB : n ≤ B.length) (hncount : w + n ≤ count),
    let hfspan : s + (w + f) ≤ p.T := Nat.le_trans
      (Nat.add_le_add_left (Nat.add_le_add_left hfn w) s)
      (Nat.le_trans (Nat.add_le_add_left hncount s) hspan)
    let ch := (ReferenceActivePhysicalHorizon.run I z.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s (w + f) hfspan active).finalState.upDecoderBank i
    let H := AffineBatchDecoder.quota p - ch.pending.length + AffineBatchDecoder.quota p
    let P := fun b : ℕ => ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries
      ((B.drop f).take (b - f)) i
    H ≤ (P n).length → ∃ (b : ℕ) (_hfb : f < b) (_hbn : b ≤ n) (q : Fin B.length),
      q.val + 1 = b ∧ (P b).length = H ∧ (P q.val).length + 1 = H ∧
      (∀ a : ℕ, f ≤ a → a < b → (P a).length < H) ∧
      ∃ e : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p),
        ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries B[q.val] i = [e] ∧
        P b = P q.val ++ [e] := by
  classical
  intro I s active E w B i f n hfn _hnB hncount hfspan ch H P hreach
  change H ≤ (P n).length at hreach
  have hbound : n ≤ B.length := _hnB
  have hquota : 0 < AffineBatchDecoder.quota p := AffineBatchDecoder.quota_pos p
  have hIbank : ReferenceUpDecoderBankInvariant.upBankInvariant I := by
    obtain ⟨launch, hlaunch, hcoord, hbank, _, _, _⟩ :=
      ReferenceCorrectedInitializationLaunch.correctedLaunch_coordinator_provenance
        rate z rewards C_star C_h hcross
    have hlaunchEq : launch = I := by
      change launch = ReferenceFirstCollectionEpochAlignment.actualLaunchState
        rate z rewards C_star C_h hcross
      exact (Option.get_of_eq_some
        ((ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
          rate z rewards C_star C_h).2 hcross) hlaunch).symm
    rw [← hlaunchEq]
    simp only [ReferenceUpDecoderBankInvariant.upBankInvariant,
      ReferenceUpDecoderBankInvariant.coordinatorBankInvariant, hcoord, hbank]
    exact ⟨CoordinatorUpReception.initialUpDecoderBank_wellFormed p, fun _ => rfl⟩
  have hrunBank := ReferenceUpDecoderBankInvariant.run_upBankInvariant I z.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s (w + f) hfspan
    active hIbank
  have hpending : ch.pending.length < AffineBatchDecoder.quota p := by
    have hi := hrunBank.1 i
    exact hi.1
  have hremaining : 0 < AffineBatchDecoder.quota p - ch.pending.length := by
    omega
  have hposH : 0 < H := by
    dsimp only [H]
    omega
  have hPzero : P f = [] := by
    simp only [P, Nat.sub_self, List.take_zero,
      ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries]
    rfl
  have hPstep : ∀ a, f ≤ a → (han : a < n) →
      P (a + 1) = P a ∨
        ∃ e, ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries
          (B[a]'(lt_of_lt_of_le han hbound)) i = [e] ∧
          P (a + 1) = P a ++ [e] := by
    intro a hfa han
    have haB : a < B.length := lt_of_lt_of_le han _hnB
    have htake := retainedUpPositiveEntries_take_succ B i f a hfa haB
    rcases recordUpPositiveEntries_eq_nil_or_singleton (B[a]'haB) i with hempty | ⟨e, hentry⟩
    · left
      simpa only [P, hempty, List.append_nil] using htake
    · right
      refine ⟨e, hentry, ?_⟩
      simpa only [P, hentry] using htake
  have hPgoal : H ≤ (P n).length := hreach
  obtain ⟨b, hfb, hbn, q, hqb, hPb, hPq, hearliest, e, hentry, happend⟩ :=
    first_exact_singleton_prefix f n H B.length P
      (fun a ha => ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries (B[a]'ha) i)
      hfn hPzero hposH hPgoal hbound hPstep
  refine ⟨b, hfb, hbn, q, hqb, hPb, hPq, hearliest, e, hentry, ?_⟩
  exact happend

end Bandits.Support.ReferenceFirstCollectionUpPrefixThreshold

end
