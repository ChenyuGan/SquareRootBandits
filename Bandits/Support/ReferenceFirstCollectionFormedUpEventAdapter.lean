/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bandits Lean regret formalization contributors.
-/
module

public import Bandits.Support.ReferenceFirstCollectionFormedUpSourceDetectingCut
public import Bandits.Support.ReferenceFirstCollectionEarlyUpAmbiguityBound
public import Bandits.Support.ReferenceFirstCollectionLateUpAmbiguityBound

import Lean.Elab.Tactic.Omega

/-!
# Actual formed-UP detecting cut into the literal source events

The local exact-count cut is projected from the same initialized source
dispatch. A successful receiver keeps its actual filtered parse and physical
UP acceptance; an ambiguous second batch is placed in the literal early or
late event on that same source.

Sources: `sources/zip4/manuscript/06_interruptions.tex:476-481`,
`05_binary_transport.tex:20-55,70-124`, and
`appendix_a_local_protocol.tex:139-157`.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions
open ReferenceActivePhysicalHorizon
open ReferenceFirstCollectionEpochAlignment
open ReferenceFirstLiveConfirmationHistory
open ReferenceCollectionPhaseHistory
open ReferenceCoordinatorUpIntervalWindow
open ReferenceActivePhysicalStep
open ReferencePrelaunchFollower
open ReferenceFirstCollectionFormedUpOfferReceiver
open ReferenceFirstCollectionFormedUpSourceDetectingCut
open ReferenceFirstCollectionEarlyUpAmbiguityBound
open ReferenceFirstCollectionLateUpAmbiguityBound

namespace Bandits.Support.ReferenceFirstCollectionFormedUpEventAdapter

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

private theorem collectionWindow_prefix_drop
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (w : ℕ) :
    ReferenceCollectionPhaseHistory.collectionWindow records w <+: records.drop w := by
  unfold ReferenceCollectionPhaseHistory.collectionWindow
  obtain ⟨suffix, hsuffix⟩ := List.takeWhile_prefix
    (l := records.drop (w + 1))
    (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
  refine ⟨suffix, ?_⟩
  rw [List.append_assoc, hsuffix]
  simp

private theorem run_records_prefix_take
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start total : ℕ) (hspan : start + total ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (n : ℕ) (hn : n ≤ total) :
    (ReferenceActivePhysicalHorizon.run initial rows selected rewards start n
      (by omega) hmode).records =
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start total
        hspan hmode).records.take n := by
  obtain ⟨suffix, hprefix⟩ := ReferenceCollectionPhaseHistory.run_records_prefix
    initial rows selected rewards start n (total - n) (by omega) hmode
  have hadd : n + (total - n) = total := Nat.add_sub_of_le hn
  simp only [hadd] at hprefix
  rw [hprefix, List.take_append_of_le_length (by
    rw [ReferenceActivePhysicalHorizon.run_record_count])]
  symm
  apply List.take_of_length_le
  rw [ReferenceActivePhysicalHorizon.run_record_count]

private theorem run_eq_of_count_eq
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start n m : ℕ) (hn : start + n ≤ p.T) (hm : start + m ≤ p.T)
    (hcount : n = m)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start) :
    ReferenceActivePhysicalHorizon.run initial rows selected rewards start n hn hmode =
      ReferenceActivePhysicalHorizon.run initial rows selected rewards start m hm hmode := by
  cases hcount
  have hproof : hn = hm := Subsingleton.elim _ _
  cases hproof
  rfl

private theorem prefix_take_eq {α : Type} (xs ys : List α) (n : ℕ)
    (hprefix : xs <+: ys) (hn : n ≤ xs.length) : xs.take n = ys.take n := by
  obtain ⟨suffix, rfl⟩ := hprefix
  exact (List.take_append_of_le_length hn).symm

private theorem prefix_slice_eq {α : Type} (xs ys : List α)
    (w f b : ℕ) (hprefix : xs <+: ys.drop w)
    (hfb : f ≤ b) (hb : b ≤ xs.length) :
    (xs.drop f).take (b - f) = (ys.take (w + b)).drop (w + f) := by
  have htake : xs.take b = (ys.drop w).take b :=
    prefix_take_eq xs (ys.drop w) b hprefix hb
  calc
    (xs.drop f).take (b - f) = (xs.take b).drop f := by
      rw [List.take_drop, Nat.add_sub_of_le hfb]
    _ = ((ys.drop w).take b).drop f := congrArg (fun zs => zs.drop f) htake
    _ = (ys.take (w + b)).drop (w + f) := by
      rw [List.take_drop, List.drop_drop]

private theorem getElem_prefix_drop {α : Type} (ys xs : List α) (w : ℕ)
    (hprefix : xs <+: ys.drop w) (k : Fin xs.length)
    (hindex : w + k.val < ys.length) :
    ys[w + k.val]'hindex = xs[k.val]'k.isLt := by
  have hprefixGet : (ys.drop w)[k.val]? = some xs[k.val] :=
    (List.prefix_iff_getElem?).mp hprefix k.val k.isLt
  have hkDrop : k.val < (ys.drop w).length :=
    Nat.lt_of_lt_of_le k.isLt hprefix.length_le
  have hdrop : (ys.drop w)[k.val]? = some (ys.drop w)[k.val] :=
    List.getElem?_eq_getElem hkDrop
  have hopt : some xs[k.val] = some (ys.drop w)[k.val] :=
    hprefixGet.symm.trans hdrop
  have hvalue : xs[k.val] = (ys.drop w)[k.val] := Option.some.inj hopt
  calc
    ys[w + k.val]'hindex = (ys.drop w)[k.val] := List.getElem_drop' hindex
    _ = xs[k.val]'k.isLt := hvalue.symm

private theorem takeWhile_drop_inside {α : Type} (p : α → Bool)
    (xs : List α) (n : ℕ) (hn : n ≤ (xs.takeWhile p).length) :
    (xs.drop n).takeWhile p = (xs.takeWhile p).drop n := by
  induction n generalizing xs with
  | zero => simp
  | succ n ih =>
      cases xs with
      | nil => simp at hn
      | cons a xs =>
          cases hp : p a with
          | false => simp [hp] at hn
          | true =>
              have hn' : n ≤ (xs.takeWhile p).length := by
                simpa [List.takeWhile_cons, hp] using hn
              simp [hp, ih xs hn']

private theorem collectionWindow_drop_late
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (w f : ℕ) (hf : 1 ≤ f)
    (hbound : f ≤ (ReferenceCollectionPhaseHistory.collectionWindow records w).length) :
    (records.drop (w + f)).takeWhile
        (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input) =
      (ReferenceCollectionPhaseHistory.collectionWindow records w).drop f := by
  let head := (records.drop w).take 1
  let tail := (records.drop (w + 1)).takeWhile
    (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
  have hwindow : ReferenceCollectionPhaseHistory.collectionWindow records w = head ++ tail := rfl
  have hheadSingleton : ∃ a, head = [a] := by
    cases hxs : records.drop w with
    | nil =>
        have hnext : records.drop (w + 1) = [] := by
          rw [← List.drop_drop, hxs]
          rfl
        have hzero : ReferenceCollectionPhaseHistory.collectionWindow records w = [] := by
          simp [ReferenceCollectionPhaseHistory.collectionWindow, hxs, hnext]
        rw [hzero] at hbound
        simp at hbound
        omega
    | cons a xs => exact ⟨a, by simp [head, hxs]⟩
  have hheadLen : head.length = 1 := by
    obtain ⟨a, ha⟩ := hheadSingleton
    simp [ha]
  have htailBound : f - 1 ≤ tail.length := by
    rw [hwindow, List.length_append, hheadLen] at hbound
    omega
  have hwindowDrop :
      (ReferenceCollectionPhaseHistory.collectionWindow records w).drop f =
        tail.drop (f - 1) := by
    obtain ⟨a, ha⟩ := hheadSingleton
    rw [hwindow, ha]
    have hdropHead : ([a] ++ tail).drop f = tail.drop (f - 1) := by
      cases f with
      | zero => omega
      | succ f => simp
    exact hdropHead
  have hrecordDrop : records.drop (w + f) =
      (records.drop (w + 1)).drop (f - 1) := by
    rw [show w + f = (w + 1) + (f - 1) by omega, List.drop_drop]
  calc
    (records.drop (w + f)).takeWhile
        (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input) =
      ((records.drop (w + 1)).drop (f - 1)).takeWhile
        (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input) :=
          congrArg (fun xs => xs.takeWhile
            (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)) hrecordDrop
    _ = tail.drop (f - 1) := by
      exact (takeWhile_drop_inside
        (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
        (records.drop (w + 1)) (f - 1) (by simpa [tail] using htailBound))
    _ = (ReferenceCollectionPhaseHistory.collectionWindow records w).drop f :=
      hwindowDrop.symm

private theorem connected_split
    {initial final : ReferenceActivePhysicalStep.State p rate}
    {xs ys : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))}
    (h : ReferenceActivePhysicalHorizon.Connected initial (xs ++ ys) final) :
    ∃ middle, ReferenceActivePhysicalHorizon.Connected initial xs middle ∧
      ReferenceActivePhysicalHorizon.Connected middle ys final := by
  induction xs generalizing initial with
  | nil => exact ⟨initial, by simp [ReferenceActivePhysicalHorizon.Connected], h⟩
  | cons record xs ih =>
      simp only [List.cons_append, ReferenceActivePhysicalHorizon.Connected] at h
      obtain ⟨middle, hleft, hright⟩ := ih h.2
      exact ⟨middle, ⟨h.1, hleft⟩, hright⟩

private theorem connected_final_of_last_record
    {initial final : ReferenceActivePhysicalStep.State p rate}
    {xs : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))}
    {record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)}
    (h : ReferenceActivePhysicalHorizon.Connected initial (xs ++ [record]) final) :
    final = record.output.next := by
  induction xs generalizing initial with
  | nil =>
      simpa only [List.nil_append, ReferenceActivePhysicalHorizon.Connected] using h.2
  | cons head xs ih =>
      simp only [List.cons_append, ReferenceActivePhysicalHorizon.Connected] at h
      exact ih h.2

private theorem connected_final_unique
    {initial final₁ final₂ : ReferenceActivePhysicalStep.State p rate}
    {records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))}
    (h₁ : ReferenceActivePhysicalHorizon.Connected initial records final₁)
    (h₂ : ReferenceActivePhysicalHorizon.Connected initial records final₂) :
    final₁ = final₂ := by
  induction records generalizing initial final₁ final₂ with
  | nil =>
      simpa only [ReferenceActivePhysicalHorizon.Connected] using h₁.trans h₂.symm
  | cons record rest ih =>
      simp only [ReferenceActivePhysicalHorizon.Connected] at h₁ h₂
      exact ih h₁.2 h₂.2

private theorem run_last_record_output
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start total : ℕ) (hspan : start + total ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (index : ℕ) (hindex : index < total)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hrecord :
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start total
        hspan hmode).records[index]? = some record) :
    (ReferenceActivePhysicalHorizon.run initial rows selected rewards start (index + 1)
      (by omega) hmode).finalState = record.output.next := by
  have hprefix := run_records_prefix_take initial rows selected rewards start total hspan hmode
    (index + 1) (by omega)
  have hget :
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start total
        hspan hmode).records[index]'(List.getElem?_eq_some_iff.mp hrecord).1 = record :=
    (List.getElem?_eq_some_iff.mp hrecord).2
  have hindexValid : index <
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start total
        hspan hmode).records.length := (List.getElem?_eq_some_iff.mp hrecord).1
  have hlast :
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start total
        hspan hmode).records.take (index + 1) =
        (ReferenceActivePhysicalHorizon.run initial rows selected rewards start total
          hspan hmode).records.take index ++ [record] := by
    rw [List.take_succ_eq_append_getElem hindexValid, hget]
  have hconn :=
    (ReferenceActivePhysicalHorizon.run initial rows selected rewards start (index + 1)
      (by omega) hmode).connected
  rw [hprefix, hlast] at hconn
  exact connected_final_of_last_record hconn

private theorem earlier_record_output_not_dagger
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start total : ℕ) (hspan : start + total ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (i : Fin (p.m - 1)) (seedIndex detectingIndex : ℕ)
    (hseedIndex : seedIndex < total) (hdetectingIndex : detectingIndex < total)
    (horder : seedIndex < detectingIndex)
    (seed detecting : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hseed :
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start total
        hspan hmode).records[seedIndex]? = some seed)
    (hdetecting :
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start total
        hspan hmode).records[detectingIndex]? = some detecting)
    (hcoord : detecting.output.next.coordinator ≠ .dagger)
    (hfollower : detecting.output.next.followers i ≠ .dagger) :
    seed.output.next.coordinator ≠ .dagger ∧ seed.output.next.followers i ≠ .dagger := by
  let detectingRun := ReferenceActivePhysicalHorizon.run initial rows selected rewards start
    (detectingIndex + 1) (by omega) hmode
  let seedRun := ReferenceActivePhysicalHorizon.run initial rows selected rewards start
    (seedIndex + 1) (by omega) hmode
  have hdetectFinal : detectingRun.finalState = detecting.output.next := by
    exact run_last_record_output initial rows selected rewards start total hspan hmode
      detectingIndex hdetectingIndex detecting hdetecting
  have hseedRecords : seedRun.records = detectingRun.records.take (seedIndex + 1) := by
    have hseedFull := run_records_prefix_take initial rows selected rewards start total hspan hmode
      (seedIndex + 1) (by omega)
    have hdetectFull := run_records_prefix_take initial rows selected rewards start total hspan hmode
      (detectingIndex + 1) (by omega)
    calc
      seedRun.records =
          (ReferenceActivePhysicalHorizon.run initial rows selected rewards start total
            hspan hmode).records.take (seedIndex + 1) := hseedFull
      _ = ((ReferenceActivePhysicalHorizon.run initial rows selected rewards start total
            hspan hmode).records.take (detectingIndex + 1)).take (seedIndex + 1) := by
              rw [List.take_take]
              simp [Nat.min_eq_left (by omega : seedIndex + 1 ≤ detectingIndex + 1)]
      _ = detectingRun.records.take (seedIndex + 1) := by rw [← hdetectFull]
  have hsplit := List.take_append_drop (seedIndex + 1) detectingRun.records
  have hchain : ReferenceActivePhysicalHorizon.Connected initial
      (detectingRun.records.take (seedIndex + 1) ++ detectingRun.records.drop (seedIndex + 1))
      detectingRun.finalState := by simpa [hsplit] using detectingRun.connected
  obtain ⟨middle, hleft, hright⟩ := connected_split hchain
  have hmiddle : middle = seedRun.finalState := by
    apply connected_final_unique hleft
    simpa [hseedRecords] using seedRun.connected
  have hseedFinal := run_last_record_output initial rows selected rewards start total hspan hmode
    seedIndex hseedIndex seed hseed
  constructor
  · intro hbad
    have hmid : middle.coordinator = .dagger := by
      rw [hmiddle, hseedFinal]
      exact hbad
    have hbadFinal := (ReferenceActivePhysicalHorizon.Connected.coordinator_dagger hright hmid).1
    rw [hdetectFinal] at hbadFinal
    exact hcoord hbadFinal
  · intro hbad
    have hmid : middle.followers i = .dagger := by
      rw [hmiddle, hseedFinal]
      exact hbad
    have hbadFinal :=
      (ReferenceActivePhysicalHorizon.Connected.follower_dagger hright i hmid).1
    rw [hdetectFinal] at hbadFinal
    exact hfollower hbadFinal

/-- For every literal local count from the actual formed-UP detecting cut,
the same deciding record either yields the checked actual UP acceptance or
places its two distinct solvers in the corresponding early/late source event.
The dispatch, offered word, retained DOWN record, and formation index are
shared across all endpoints `b`. -/
public theorem actual_initialized_first_collection_formed_up_event_cut
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (count : ℕ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed + count ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count hspan).records).length < count) :
    ∃ d : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
        source rewards C_star C_h count hcross hspan hshort,
      let out := d.stream
      let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count hspan
      let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length
      let s := ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
      let B := ReferenceCollectionPhaseHistory.collectionWindow E.records w
      ∃ hlen : w + out.ell ≤ count,
        ∃ hBlength : out.ell ≤ B.length,
        let initial := ReferenceFirstCollectionEpochAlignment.actualLaunchState
          rate source rewards C_star C_h hcross
        let active := (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
          rate source rewards C_star C_h hcross).1
        let J := ActualInitializationPhysicalStep.selectedRowIndex p source
        let X (t : ℕ) (hwt : w + t ≤ count) :=
          (ReferenceActivePhysicalHorizon.run initial source.1.2 J rewards s (w + t)
            (Nat.le_trans (Nat.add_le_add_left hwt s) hspan) active).finalState
        out.window = B ∧
        ∀ (n : Fin out.ell) (_hn : 0 < n.val) (i : Fin (p.m - 1)),
          i ∈ (out.ledgers ⟨n.val - 1,
            Nat.lt_of_le_of_lt (Nat.sub_le n.val 1) n.isLt⟩).pending →
          ∃ (state : ReferencePrelaunchFollower.State p rate.eta)
            (memory : ActiveFollowerLifecycle.LocalMemory p),
            (B[n.val]'(Nat.lt_of_lt_of_le n.isLt hBlength)).input.state.followers i =
                .ordinary state memory ∧
            state.status = .unoccupied ∧ ActiveFollowerLifecycle.localStateDomainValid state ∧
            (state.lastDown = some (out.payload.downRecord i) →
              ∃ (U : OrdinaryMessageCodec.UpRecord
                  (ReferencePrelaunchFollower.codecParams p rate.eta))
                (j : Fin E.records.length),
                U.val = ActiveFollowerQueueOperation.upOfferFields state ∧
                U.val.sigma = s + 1 ∧ 1 ≤ U.val.sigma ∧
                j.val < w + n.val ∧
                ReferenceAcceptedUpFollowerHistory.RetainedDown E.records[j.val] i
                  (out.payload.downRecord i) ∧
                (∀ j' : Fin E.records.length, j'.val < w + n.val →
                  ReferenceAcceptedUpFollowerHistory.RetainedDown E.records[j'.val] i
                    (out.payload.downRecord i) → j' = j) ∧
                let f := if j.val < w then 0 else j.val - w + 1
                ∃ hf : f < B.length,
                  f ≤ n.val ∧
                  B[f].input.time.val + 1 = max (s + w + 1) (s + j.val + 2) ∧
                  (j.val < w → f = 0) ∧ (j.val = w → f = 1) ∧
                  ∀ (b : ℕ) (hfb : f ≤ b) (hbn : b ≤ n.val + 1),
                    let S := (B.drop f).take (b - f)
                    let times := S.map (fun r => r.input.time)
                    let tr := ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace S i
                    let P := AffineBatchDecoder.positives p tr times
                    let ch := (X f (by omega)).upDecoderBank i
                    let Q := AffineBatchDecoder.quota p
                    let _window := P.drop (Q - ch.pending.length)
                    let uword :=
                      ReferenceFirstCollectionFormedUpOfferReceiver.encodedUpOfferWord U
                    P.length = Q - ch.pending.length + Q →
                    (∃ (q : Fin B.length),
                      0 < q.val ∧ f ≤ q.val ∧ q.val < b ∧ q.val ≤ n.val ∧
                      E.records[w + q.val]? = some B[q.val] ∧
                      let r := B[q.val]
                      r.input.rows = source.1.2 ∧ r.input.selected = J ∧
                      r.input.rewards = rewards ∧
                      r.output.next.coordinator ≠ .dagger ∧
                      r.output.next.followers i ≠ .dagger ∧
                      ReferenceSelectedAffinePairLaw.selectedChannel p
                        ((source.1.2 J).2 r.input.time).1 = some (1, i) ∧
                      ReferenceActiveAffinePositiveTest.upPositive r.input = true ∧
                      ∃ (diagnostic : ReferenceActivePhysicalStep.UpDiagnostic p rate)
                        (tail : ReferenceCollectionPhaseHistory.Tail r.input)
                        (recording : CoordinatorRecordingOperation.Output p)
                        (L : ReferenceActivePhysicalStep.Ledger rate),
                        r.output.coordinator.up = some diagnostic ∧
                        diagnostic.input.selectedFollower = i ∧
                        ReferenceCollectionPhaseHistory.executedTail r.input = some tail ∧
                        CoordinatorRecorderComplementBridge.run
                          (ReferenceActivePhysicalStep.collectionRecordingInput
                            (ReferenceActivePhysicalStep.prepare r.input)
                            tail.payload tail.started tail.weights) = some recording ∧
                        CoordinatorCollectionLedger.startRound tail.ledger
                          (r.input.time.val + 1)
                          (ReferenceActivePhysicalStep.collectionEnabled tail.ledger r.input.time)
                          (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) =
                            .success L ∧
                        ReferenceCoordinatorUpPhysicalCall.siteLedger? (x := r.input) = some L ∧
                        diagnostic.input =
                          ReferenceCoordinatorUpPhysicalCall.actualUpInput r.input L ∧
                        CoordinatorUpReception.receptionInputCheck diagnostic.input = true ∧
                        tail.reception = some (L,
                          ReferenceActivePhysicalStep.receiveUp
                            (ReferenceActivePhysicalStep.prepare r.input) L) ∧
                        (ReferenceActivePhysicalStep.receiveUp
                          (ReferenceActivePhysicalStep.prepare r.input) L).result ≠ .invalid ∧
                        i ∈ L.pending ∧
                        CoordinatorCollectionLedger.acceptUpCheck L i U = true ∧
                        ReferenceActivePhysicalStep.upExpected
                          (ReferenceActivePhysicalStep.prepare r.input) = some uword ∧
                        diagnostic.expected = some uword ∧
                        diagnostic.raw = some uword ∧
                        ReferenceCollectionPhaseHistory.filteredParsed r.input L = some U ∧
                        ∃ (decoded : ReferenceActivePhysicalStep.Ledger rate)
                          (bank : CoordinatorUpReception.UpDecoderBank p),
                          (ReferenceActivePhysicalStep.receiveUp
                            (ReferenceActivePhysicalStep.prepare r.input) L).result =
                              .success (decoded, bank) ∧
                          ReferenceCollectionPhaseHistory.AcceptedUp r.input i U)
                    ∨ ((j.val < w ∧
                      source ∈ earlySecondBatchAmbiguityEvent
                            (rate := rate) rewards C_star C_h) ∨
                        (w ≤ j.val ∧
                          source ∈ lateSecondBatchAmbiguityEvent
                            (rate := rate) rewards C_star C_h))) := by
  obtain ⟨d, hcut⟩ :=
    actual_initialized_first_collection_formed_up_detecting_cut
      rate source rewards C_star C_h count hcross hspan hshort
  refine ⟨d, ?_⟩
  intro out E w s B
  rcases hcut with ⟨hlen, hBlength, hwindow⟩
  let initial := ReferenceFirstCollectionEpochAlignment.actualLaunchState
    rate source rewards C_star C_h hcross
  let active := (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
    rate source rewards C_star C_h hcross).1
  let J := ActualInitializationPhysicalStep.selectedRowIndex p source
  let X (t : ℕ) (hwt : w + t ≤ count) :=
    (ReferenceActivePhysicalHorizon.run initial source.1.2 J rewards s (w + t)
      (Nat.le_trans (Nat.add_le_add_left hwt s) hspan) active).finalState
  rcases hwindow with ⟨hWindow, hqueries⟩
  refine ⟨hlen, hBlength, ?_⟩
  refine ⟨hWindow, ?_⟩
  intro n hn i hi
  obtain ⟨state, memory, hstate, hstatus, hvalid, hformed⟩ := hqueries n hn i hi
  refine ⟨state, memory, hstate, hstatus, hvalid, ?_⟩
  intro hlastDown
  obtain ⟨U, j, hU, hUsigma, hUsigmaPos, hj, hretained, hunique, hformation⟩ :=
    hformed hlastDown
  dsimp only at hformation
  let f : ℕ := if j.val < w then 0 else j.val - w + 1
  obtain ⟨hf, hfn, hftime, hfzero, hfone, hlocal⟩ := hformation
  refine ⟨U, j, hU, hUsigma, hUsigmaPos, hj, hretained, ?_, ?_⟩
  · intro j' hj' hr'
    exact hunique j' hj' hr'
  · dsimp only
    refine ⟨hf, hfn, hftime, hfzero, hfone, ?_⟩
    intro b hfb hbn
    let S := (B.drop f).take (b - f)
    let times := S.map (fun r => r.input.time)
    let tr := ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace S i
    let P := AffineBatchDecoder.positives p tr times
    have hOutLength : w + out.ell ≤ count := hlen
    have hXBound : w + f ≤ count := by omega
    let ch := (X f hXBound).upDecoderBank i
    let Q := AffineBatchDecoder.quota p
    let window := P.drop (Q - ch.pending.length)
    intro hcount
    obtain ⟨q, hqn, last, diagnostic, tail, recording, L, hdata⟩ :=
      hlocal b hfb hbn hcount
    rcases hdata with ⟨hqpos, hfq, hqb, hqle, hget, htimeq, hrows, hselected,
      hrewards, hfirstLen, hwindowLen, hpendingLt, hPbound, hpairwise,
      hpendDisjoint, hlastIn, hdecision, htimeLast, houtDiag, hdiagFollower,
      hsel, hupPositive, hrounded, hexecuted, hrecording, hstart, hsite,
      hdiagInput, hcheck, htailReception, hnotInvalid, hpending, hacceptCheck,
      hexpected, hdiagExpected, hdiagTime, hsample, hownObservation, hbank,
      hdiagPending, htransition, hafter, hraw, hbankq, hbankb, hcompleted,
      hwindowEqns, hPcrop, hcoordOrd, hfollowerOrd, hbranch⟩
    have hqOne : q.val + 1 ≤ B.length := Nat.succ_le_of_lt q.isLt
    have hqOut : q.val < out.ell := Nat.lt_of_le_of_lt hqn n.isLt
    have hEventLength : w + (q.val + 1) ≤ count := by
      have hqOut' : q.val + 1 ≤ out.ell := Nat.succ_le_of_lt hqOut
      omega
    have hEventSpan : s + (w + (q.val + 1)) ≤ p.T :=
      Nat.le_trans (Nat.add_le_add_left hEventLength s) hspan
    have hXSpan : s + (w + f) ≤ p.T :=
      Nat.le_trans (Nat.add_le_add_left hXBound s) hspan
    have hfullIndex : w + q.val < count := by omega
    have hfullGet :
        (ReferenceActivePhysicalHorizon.run initial source.1.2 J rewards s count
          hspan active).records[w + q.val]? = some (B[q.val]) := by
      simpa only [initial, J, s, w, B, E,
        ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun] using hget
    have hdetectFinal :
        (ReferenceActivePhysicalHorizon.run initial source.1.2 J rewards s (w + (q.val + 1))
          hEventSpan active).finalState = (B[q.val]).output.next := by
      have hlast := run_last_record_output initial source.1.2 J rewards s count hspan active
        (w + q.val) hfullIndex (B[q.val]) hfullGet
      simpa [Nat.add_assoc] using hlast
    have hBprefix : B <+:
        (ReferenceActivePhysicalHorizon.run initial source.1.2 J rewards s count hspan active).records.drop w := by
      simpa only [B, E, ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun] using
        collectionWindow_prefix_drop E.records w
    have hinterval :
        (B.drop f).take (q.val + 1 - f) =
          (ReferenceActivePhysicalHorizon.run initial source.1.2 J rewards s
            (w + (q.val + 1)) hEventSpan active).records.drop (w + f) := by
      calc
        (B.drop f).take (q.val + 1 - f) =
            (List.take (w + (q.val + 1))
              (ReferenceActivePhysicalHorizon.run initial source.1.2 J rewards s count hspan active).records).drop
                (w + f) :=
          prefix_slice_eq B
            (ReferenceActivePhysicalHorizon.run initial source.1.2 J rewards s count hspan active).records
            w f (q.val + 1) hBprefix (Nat.le_trans hfq (Nat.le_succ q.val)) hqOne
        _ = (ReferenceActivePhysicalHorizon.run initial source.1.2 J rewards s
            (w + (q.val + 1)) hEventSpan active).records.drop (w + f) := by
              rw [run_records_prefix_take initial source.1.2 J rewards s count hspan active
                (w + (q.val + 1)) hEventLength]
    have hPevent :
        AffineBatchDecoder.positives p
          (ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace
            ((ReferenceActivePhysicalHorizon.run initial source.1.2 J rewards s
              (w + (q.val + 1)) hEventSpan active).records.drop (w + f)) i)
          (ReferenceCoordinatorUpIntervalWindow.intervalRounds initial source.1.2 J rewards s
            (w + f) (w + (q.val + 1)) hEventSpan active) = P := by
      change AffineBatchDecoder.positives p
        (ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace
          (ReferenceCoordinatorUpIntervalWindow.intervalRecords initial source.1.2 J rewards s
            (w + f) (w + (q.val + 1)) hEventSpan active) i)
        ((ReferenceCoordinatorUpIntervalWindow.intervalRecords initial source.1.2 J rewards s
          (w + f) (w + (q.val + 1)) hEventSpan active).map (fun r => r.input.time)) = P
      rw [ReferenceCoordinatorUpIntervalWindow.intervalRecords, ← hinterval]
      exact hPcrop
    have hchannel :
        (ReferenceActivePhysicalHorizon.run initial source.1.2 J rewards s (w + f)
          hXSpan active).finalState.upDecoderBank i = ch := by
      rfl
    have hwindowEvent :
        (AffineBatchDecoder.positives p
          (ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace
            ((ReferenceActivePhysicalHorizon.run initial source.1.2 J rewards s
              (w + (q.val + 1)) hEventSpan active).records.drop (w + f)) i)
          (ReferenceCoordinatorUpIntervalWindow.intervalRounds initial source.1.2 J rewards s
            (w + f) (w + (q.val + 1)) hEventSpan active)).drop
          (AffineBatchDecoder.quota p -
            ((ReferenceActivePhysicalHorizon.run initial source.1.2 J rewards s (w + f)
              hXSpan active).finalState.upDecoderBank i).pending.length) = window := by
      rw [hPevent, hchannel]
    rcases hbranch with haccepted | hambiguous
    · have hget' : E.records[w + q.val]? = some B[q.val] := by
        simpa only [B] using hget
      refine Or.inl ⟨q, hqpos, hfq, hqb, hqle, hget', ?_⟩
      rcases haccepted with ⟨hraw, hparsed, decoded, bank, hsuccess, haccepted⟩
      exact ⟨hrows, hselected, hrewards, hcoordOrd, hfollowerOrd, hsel,
        hupPositive, diagnostic, tail, recording, L, houtDiag, hdiagFollower,
        hexecuted, hrecording, hstart, hsite, hdiagInput, hcheck,
        htailReception, hnotInvalid, hpending, hacceptCheck, hexpected,
        hdiagExpected, hraw, hparsed, decoded, bank, hsuccess, haccepted⟩
    · rcases hambiguous with ⟨hnone, left, right, hneq, hleft, hright⟩
      by_cases hjEarly : j.val < w
      · right
        left
        refine ⟨hjEarly, ?_⟩
        have hsourceEvent : source ∈
            earlySecondBatchAmbiguityEvent (rate := rate) rewards C_star C_h := by
          simp only [earlySecondBatchAmbiguityEvent, Set.mem_ofPred_eq]
          refine ⟨count, hcross, hspan, hshort, i, j, out.payload.downRecord i,
            hjEarly, hretained, q.val + 1, ?_, ?_, ?_⟩
          · omega
          · omega
          · refine ⟨hEventSpan, ?_⟩
            have hfinalEq :
              (ReferenceActivePhysicalHorizon.run initial source.1.2 J rewards s
                (w + (q.val + 1)) hEventSpan active).finalState = (B[q.val]).output.next :=
                hdetectFinal
            have hchannelEarly :
                (ReferenceActivePhysicalHorizon.run initial source.1.2 J rewards s w
                  (by omega) active).finalState.upDecoderBank i = ch := by
              have hf0 : f = 0 := hfzero hjEarly
              simpa only [f, hf0, initial, J, s, w, E,
                ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun,
                Nat.add_zero] using hchannel
            have hPeventEarly :
                AffineBatchDecoder.positives p
                  (ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace
                    ((ReferenceActivePhysicalHorizon.run initial source.1.2 J rewards s
                      (w + (q.val + 1)) hEventSpan active).records.drop w) i)
                  (ReferenceCoordinatorUpIntervalWindow.intervalRounds initial source.1.2 J rewards s
                    w (w + (q.val + 1)) hEventSpan active) = P := by
              have hf0 : f = 0 := hfzero hjEarly
              simpa only [f, hf0, initial, J, s, w, B, E,
                ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun,
                ReferenceCoordinatorUpIntervalWindow.intervalRounds,
                ReferenceCoordinatorUpIntervalWindow.intervalRecords,
                Nat.add_zero] using hPevent
            have hwindowEventEarly :
                (AffineBatchDecoder.positives p
                  (ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace
                    ((ReferenceActivePhysicalHorizon.run initial source.1.2 J rewards s
                      (w + (q.val + 1)) hEventSpan active).records.drop w) i)
                  (ReferenceCoordinatorUpIntervalWindow.intervalRounds initial source.1.2 J rewards s
                    w (w + (q.val + 1)) hEventSpan active)).drop
                  (AffineBatchDecoder.quota p -
                    ((ReferenceActivePhysicalHorizon.run initial source.1.2 J rewards s w
                      (by omega) active).finalState.upDecoderBank i).pending.length) = window := by
              have hf0 : f = 0 := hfzero hjEarly
              simpa only [f, hf0, initial, J, s, w, B, E,
                ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun,
                ReferenceCoordinatorUpIntervalWindow.intervalRounds,
                ReferenceCoordinatorUpIntervalWindow.intervalRecords,
                Nat.add_zero] using hwindowEvent
            refine ⟨?_, ?_, ?_, ⟨left, right, hneq, ?_, ?_⟩⟩
            · rw [hfinalEq]
              exact hcoordOrd
            · rw [hfinalEq]
              exact hfollowerOrd
            · rw [hPeventEarly, hchannelEarly]
              exact hcount
            · rw [hwindowEventEarly]
              exact hleft
            · rw [hwindowEventEarly]
              exact hright
        exact hsourceEvent
      · right
        right
        refine ⟨by omega, ?_⟩
        have hBprefix' : B <+: E.records.drop w := by
          simpa only [B] using collectionWindow_prefix_drop E.records w
        have hOutB : out.ell ≤ B.length := hBlength
        have hj' : j.val < w + n.val := hj
        have hdiff : j.val - w < n.val := by omega
        have hdiffBound : j.val - w < B.length :=
          Nat.lt_of_lt_of_le hdiff (Nat.le_trans (Nat.le_of_lt n.isLt) hOutB)
        let k : Fin B.length := ⟨j.val - w, hdiffBound⟩
        have hkf : k.val + 1 = f := by
          dsimp only [f]
          have hnotEarly : ¬j.val < w := by omega
          change (j.val - w) + 1 = if j.val < w then 0 else j.val - w + 1
          simp [hnotEarly]
        have hjEq : w + k.val = j.val := by
          dsimp [k]
          omega
        have hseedEq : E.records[j.val]'j.isLt = B[k.val]'k.isLt := by
          have hindex : w + k.val < E.records.length := by
            simpa only [hjEq] using j.isLt
          have hEq := getElem_prefix_drop E.records B w hBprefix' k hindex
          simpa only [hjEq] using hEq
        have hseedGet : E.records[j.val]? = some (B[k.val]'k.isLt) := by
          calc
            E.records[j.val]? = some (E.records[j.val]'j.isLt) :=
              List.getElem?_eq_getElem j.isLt
            _ = some (B[k.val]'k.isLt) := congrArg some hseedEq
        have hseedRetained :
            ReferenceAcceptedUpFollowerHistory.RetainedDown (B[k.val]'k.isLt) i
              (out.payload.downRecord i) := by
          rw [← hseedEq]
          exact hretained
        have hkqBound : k.val + 1 ≤ q.val := by
          calc
            k.val + 1 = f := hkf
            _ ≤ q.val := hfq
        have hkq : k.val < q.val := Nat.lt_of_succ_le hkqBound
        have horder : j.val < w + q.val := by
          calc
            j.val = w + k.val := hjEq.symm
            _ < w + q.val := Nat.add_lt_add_left hkq w
        have hseedIndexBound : j.val < count := Nat.lt_trans horder hfullIndex
        have hseedGuards := earlier_record_output_not_dagger
          initial source.1.2 J rewards s count hspan active i j.val (w + q.val)
          hseedIndexBound hfullIndex horder
          (B[k.val]) (B[q.val]) hseedGet hfullGet hcoordOrd hfollowerOrd
        have hseedStart : j.val + 1 = w + f := by omega
        have hWlate :
            (E.records.drop (j.val + 1)).takeWhile
                (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input) =
              B.drop f := by
          calc
            (E.records.drop (j.val + 1)).takeWhile
                (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input) =
              (E.records.drop (w + (k.val + 1))).takeWhile
                (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input) := by
                  rw [show j.val + 1 = w + (k.val + 1) by omega]
            _ = B.drop (k.val + 1) :=
              collectionWindow_drop_late E.records w (k.val + 1) (by omega)
                (Nat.succ_le_of_lt k.isLt)
            _ = B.drop f := by rw [← hkf]
        have hEventNpos : 0 < q.val + 1 - f := by omega
        have hEventNbound : q.val + 1 - f ≤ (B.drop f).length := by
          simpa only [List.length_drop] using Nat.sub_le_sub_right hqOne f
        have hLateEnd : (j.val + 1) + (q.val + 1 - f) = w + (q.val + 1) := by
          rw [hseedStart]
          omega
        have hLateSpan : s + ((j.val + 1) + (q.val + 1 - f)) ≤ p.T := by
          rw [hLateEnd]
          exact hEventSpan
        have hLateBaseSpan : s + (j.val + 1) ≤ p.T := by omega
        have hEventNboundLate : q.val + 1 - f ≤
            ((E.records.drop (j.val + 1)).takeWhile
              (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input)).length := by
          rw [hWlate]
          exact hEventNbound
        have hLateStart : w + k.val + 1 = w + f := by omega
        have hLateEventBound : q.val + 1 - f ≤
            ((E.records.drop (w + k.val + 1)).takeWhile
              (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input)).length := by
          have hindex : j.val + 1 = w + k.val + 1 := by omega
          rw [← hindex]
          exact hEventNboundLate
        have hLateBaseSpan' : s + (w + k.val + 1) ≤ p.T := by
          rw [hLateStart]
          rw [← hseedStart]
          exact hLateBaseSpan
        have hLateSpan' : s + ((w + k.val + 1) + (q.val + 1 - f)) ≤ p.T := by
          rw [hLateStart]
          rw [← hseedStart]
          exact hLateSpan
        have hLateRunLength : (w + k.val + 1) + (q.val + 1 - f) =
            w + (q.val + 1) := by omega
        have hLatePhysicalRun :
            ReferenceActivePhysicalHorizon.run initial source.1.2 J rewards s
              ((w + k.val + 1) + (q.val + 1 - f)) hLateSpan' active =
            ReferenceActivePhysicalHorizon.run initial source.1.2 J rewards s
              (w + (q.val + 1)) hEventSpan active := by
          exact run_eq_of_count_eq initial source.1.2 J rewards s
            ((w + k.val + 1) + (q.val + 1 - f)) (w + (q.val + 1))
            hLateSpan' hEventSpan hLateRunLength active
        have hLateChannelRun :
            ReferenceActivePhysicalHorizon.run initial source.1.2 J rewards s
              (w + k.val + 1) hLateBaseSpan' active =
            ReferenceActivePhysicalHorizon.run initial source.1.2 J rewards s
              (w + f) hXSpan active := by
          exact run_eq_of_count_eq initial source.1.2 J rewards s
            (w + k.val + 1) (w + f) hLateBaseSpan' hXSpan hLateStart active
        have hLateRecordSlice :
            (ReferenceActivePhysicalHorizon.run initial source.1.2 J rewards s
              ((w + k.val + 1) + (q.val + 1 - f)) hLateSpan' active).records.drop
                (w + k.val + 1) =
            (ReferenceActivePhysicalHorizon.run initial source.1.2 J rewards s
              (w + (q.val + 1)) hEventSpan active).records.drop (w + f) := by
          rw [hLatePhysicalRun, hLateStart]
        have hLateRounds :
            ReferenceCoordinatorUpIntervalWindow.intervalRounds initial source.1.2 J rewards s
              (w + k.val + 1) ((w + k.val + 1) + (q.val + 1 - f)) hLateSpan' active =
            ReferenceCoordinatorUpIntervalWindow.intervalRounds initial source.1.2 J rewards s
              (w + f) (w + (q.val + 1)) hEventSpan active := by
          simp only [ReferenceCoordinatorUpIntervalWindow.intervalRounds,
            ReferenceCoordinatorUpIntervalWindow.intervalRecords]
          rw [hLatePhysicalRun, hLateStart]
        have hLatePevent :
            AffineBatchDecoder.positives p
              (ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace
                ((ReferenceActivePhysicalHorizon.run initial source.1.2 J rewards s
                  ((w + k.val + 1) + (q.val + 1 - f)) hLateSpan' active).records.drop
                    (w + k.val + 1)) i)
              (ReferenceCoordinatorUpIntervalWindow.intervalRounds initial source.1.2 J rewards s
                (w + k.val + 1) ((w + k.val + 1) + (q.val + 1 - f)) hLateSpan' active) = P := by
          rw [hLateRecordSlice, hLateRounds]
          exact hPevent
        have hLateChannel :
            (ReferenceActivePhysicalHorizon.run initial source.1.2 J rewards s
              (w + k.val + 1) hLateBaseSpan' active).finalState.upDecoderBank i = ch := by
          rw [hLateChannelRun]
        have hLateWindowEvent :
            (AffineBatchDecoder.positives p
              (ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace
                ((ReferenceActivePhysicalHorizon.run initial source.1.2 J rewards s
                  ((w + k.val + 1) + (q.val + 1 - f)) hLateSpan' active).records.drop
                    (w + k.val + 1)) i)
              (ReferenceCoordinatorUpIntervalWindow.intervalRounds initial source.1.2 J rewards s
                (w + k.val + 1) ((w + k.val + 1) + (q.val + 1 - f)) hLateSpan' active)).drop
              (AffineBatchDecoder.quota p -
                ((ReferenceActivePhysicalHorizon.run initial source.1.2 J rewards s
                  (w + k.val + 1) hLateBaseSpan' active).finalState.upDecoderBank i).pending.length) =
              window := by
          rw [hLatePevent, hLateChannel]
        simp only [lateSecondBatchAmbiguityEvent, Set.mem_ofPred_eq]
        refine ⟨count, hcross, hspan, hshort, k, i, out.payload.downRecord i,
          hseedRetained, ?_, ?_, ?_⟩
        · exact hseedGuards.2
        · exact hseedGuards.1
        · refine ⟨q.val + 1 - f, hEventNpos,
            (by simpa only [E, w, B,
              ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun] using hLateEventBound),
            (by simpa only [initial, J, s, w, E,
              ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun] using hLateBaseSpan'),
            (by simpa only [initial, J, s, w, E,
              ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun] using hLateSpan'), ?_⟩
          · refine ⟨?_, ?_, ?_, ?_⟩
            · have hLateFinalEq :
                (ReferenceActivePhysicalHorizon.run initial source.1.2 J rewards s
                  ((w + k.val + 1) + (q.val + 1 - f)) hLateSpan' active).finalState =
                    (B[q.val]).output.next := by
                rw [hLatePhysicalRun]
                exact hdetectFinal
              rw [hLateFinalEq]
              exact hcoordOrd
            · rw [hLatePevent, hLateChannel]
              exact hcount
            · refine ⟨left, right, hneq, ?_, ?_⟩
              · rw [hLateWindowEvent]
                exact hleft
              · rw [hLateWindowEvent]
                exact hright
            · refine ⟨B[q.val], ?_, hsel, hupPositive⟩
              have hcurrentIndex :
                  (w + k.val + 1) + (q.val + 1 - f) - 1 = w + q.val := by
                rw [hLateRunLength]
                omega
              have hcurrentGet :
                  (ReferenceActivePhysicalHorizon.run initial source.1.2 J rewards s
                    ((w + k.val + 1) + (q.val + 1 - f)) hLateSpan' active).records[
                      (w + k.val + 1) + (q.val + 1 - f) - 1]? = some B[q.val] := by
                rw [hLatePhysicalRun, hcurrentIndex,
                  run_records_prefix_take initial source.1.2 J rewards s count hspan active
                    (w + (q.val + 1)) hEventLength]
                rw [List.getElem?_take_of_lt (by omega)]
                exact hfullGet
              simpa only [initial, J, s, w, E,
                ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun,
                hLateRunLength] using hcurrentGet

/-- The event branches of the actual formed-UP cut lie in the existing
all-J awaited-UP ambiguity envelope for each supplied control slice. -/
public theorem actual_formed_up_ambiguity_events_subset_envelope
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p) :
    earlySecondBatchAmbiguityEvent (rate := rate) rewards C_star C_h ∪
        lateSecondBatchAmbiguityEvent (rate := rate) rewards C_star C_h ⊆
      ReferenceGeneratedUpAwaitedAmbiguityTail.upAwaitedAmbiguityEnvelope
        (rate := rate) rewards C_star C_h control0 := by
  intro source hsource
  rcases Set.mem_or_mem_of_mem_union hsource with hearly | hlate
  · exact earlySecondBatchAmbiguityEvent_subset_envelope
      (rate := rate) rewards C_star C_h control0 hearly
  · exact lateSecondBatchAmbiguityEvent_subset_envelope
      (rate := rate) rewards C_star C_h control0 hlate

end Bandits.Support.ReferenceFirstCollectionFormedUpEventAdapter

end
