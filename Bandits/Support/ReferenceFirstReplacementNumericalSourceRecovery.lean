/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstReplacementAcceptedSparseEmissions
public import Bandits.Support.ReferenceFirstReplacementFollowerBoundary

import Lean.Elab.Tactic.Omega
import Mathlib.Data.List.TakeDrop

/-!
# The numerical source stream after the first replacement

Sources: `sources/zip4/manuscript/05_binary_transport.tex:354-431`,
`sources/zip4/manuscript/06_interruptions.tex:9-70,193-233,246-295`,
`sources/zip4/manuscript/04_slow_fast_learner.tex:157-188`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-79`.

The stream keeps the actual birth record and every retained continuing record
in original calendar order. Accepted DOWN recovery is replayed on that same
stream from the transmitted queue, including every enabled zero-arrival date.
This is an internal numerical-source result; it does not assert a true global
initial queue, cutoff truth, accepted-UP truth, or regret closure.
-/

@[expose] public section
noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceFirstWindowNumericalStream
open Bandits.Support.ReferenceLaterLiveNumericalReadout
open Bandits.Support.ReferenceFirstReplacementLiveFollowerPrefix
open Bandits.Support.ActiveFollowerDownAcceptance
open Bandits.Support.SparseCalendarReplay
open Bandits.Support.RecordedQueueRun
open Bandits.Support

namespace Bandits.Support.ReferenceFirstReplacementNumericalSourceRecovery

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

private theorem filterMap_length_of_indexed_some {α β : Type}
    (f : α → Option β) (xs : List α)
    (h : ∀ j : Fin xs.length, ∃ y, f (xs.get j) = some y) :
    (xs.filterMap f).length = xs.length := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      have htail : ∀ j : Fin xs.length, ∃ z, f (xs.get j) = some z := by
        intro j
        simpa using h j.succ
      cases hfa : f a with
      | none =>
          obtain ⟨y, hy⟩ := h ⟨0, by simp⟩
          have : f a = some y := by simpa using hy
          rw [hfa] at this
          cases this
      | some b =>
          simp [hfa, ih htail]

private theorem filterMap_getElem?_of_indexed_some {α β : Type}
    (f : α → Option β) (xs : List α)
    (h : ∀ j : Fin xs.length, ∃ y, f (xs.get j) = some y)
    (j : Fin xs.length) :
    ∃ y, (xs.filterMap f)[j.val]? = some y ∧ f (xs.get j) = some y := by
  induction xs with
  | nil => exact Fin.elim0 j
  | cons a xs ih =>
      cases j using Fin.cases with
      | zero =>
          obtain ⟨y, hy⟩ := h ⟨0, by simp⟩
          have hy' : f a = some y := by simpa using hy
          refine ⟨y, ?_, by simpa using hy⟩
          rw [List.filterMap_cons, hy']
          simp
      | succ j =>
          obtain ⟨head, hhead⟩ := h ⟨0, by simp⟩
          have hhead' : f a = some head := by simpa using hhead
          have htail : ∀ n : Fin xs.length, ∃ y, f (xs.get n) = some y := by
            intro n
            simpa using h n.succ
          obtain ⟨y, hget, hval⟩ := ih htail j
          refine ⟨y, ?_, hval⟩
          rw [List.filterMap_cons, hhead']
          change (head :: xs.filterMap f)[j.val + 1]? = some y
          rw [List.getElem?_cons_succ]
          exact hget

private theorem backward_prefix_of_step {P : ℕ → Prop} (k : ℕ)
    (hstep : ∀ n, n < k → P (n + 1) → P n) (hk : P k) :
    ∀ n, n ≤ k → P n := by
  intro n hn
  let distance := k - n
  have hdistance : distance ≤ k := by dsimp [distance]; omega
  have hvalue : ∀ d, d ≤ k → P (k - d) := by
    intro d
    induction d with
    | zero => intro _; simpa using hk
    | succ d ih =>
        intro hle
        have hprev := ih (by omega)
        have hstep' := hstep (k - (d + 1)) (by omega)
        have hindex : k - d = (k - (d + 1)) + 1 := by omega
        rw [hindex] at hprev
        exact hstep' hprev
  have hresult := hvalue distance hdistance
  have hindex : k - distance = n := by dsimp [distance]; omega
  simpa [hindex] using hresult

/-- The first-replacement slice is literally the birth followed by the
existing continuing tail. -/
private theorem first_replacement_stream_eq_cons
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))) (v : ℕ)
    (birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hbirth : records[v]? = some birth) :
    (records.drop v).take
        (1 + (ReferenceFirstReplacementLiveFollowerPrefix.continuingTail records v).length) =
      birth :: ReferenceFirstReplacementLiveFollowerPrefix.continuingTail records v := by
  have hv : v < records.length := (List.getElem?_eq_some_iff.mp hbirth).1
  have hvalue : records[v] = birth := (List.getElem?_eq_some_iff.mp hbirth).2
  have hdrop : records.drop v = birth :: records.drop (v + 1) := by
    rw [List.drop_eq_getElem_cons hv, hvalue]
  have htailPrefix :
      ReferenceFirstReplacementLiveFollowerPrefix.continuingTail records v <+:
        records.drop (v + 1) := by
    exact List.takeWhile_prefix _
  have htail :
      (records.drop (v + 1)).take
          (ReferenceFirstReplacementLiveFollowerPrefix.continuingTail records v).length =
        ReferenceFirstReplacementLiveFollowerPrefix.continuingTail records v :=
    (List.prefix_iff_eq_take.mp htailPrefix).symm
  rw [hdrop]
  rw [Nat.one_add, List.take_succ_cons, htail]

private theorem complete_suffix_adjacent
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (k : ℕ)
    (hk : k + 1 <
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h).length) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h
    (R.get ⟨k + 1, hk⟩).input.state =
      (R.get ⟨k, (Nat.lt_succ_self k).trans hk⟩).output.next ∧
    (R.get ⟨k + 1, hk⟩).input.time.val =
      (R.get ⟨k, (Nat.lt_succ_self k).trans hk⟩).input.time.val + 1 := by
  dsimp only
  obtain ⟨_, _, h0⟩ := ReferenceLaterLiveNumericalReadout.source_record_prefix
    rate rewards C_star C_h source ⟨k, by omega⟩
  obtain ⟨_, _, h1⟩ := ReferenceLaterLiveNumericalReadout.source_record_prefix
    rate rewards C_star C_h source ⟨k + 1, hk⟩
  rw [h0, h1]
  exact ⟨ReferenceAssignmentPayloadChronology.run_successor_finalState_eq_actualRunRecordAt
    _ source.1.2 _ rewards _ k _ _, rfl⟩

private theorem complete_suffix_record_time
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length) :
    ((ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).get k).input.time.val =
        ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h + k.val := by
  obtain ⟨_, _, hrecord⟩ := ReferenceLaterLiveNumericalReadout.source_record_prefix
    rate rewards C_star C_h source k
  rw [hrecord]
  rfl

private theorem continuing_tail_adjacent
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (v n : ℕ)
    (hn : n + 1 < (ReferenceFirstReplacementLiveFollowerPrefix.continuingTail
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h) v).length) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h
    let previous := (ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v).get
      ⟨n, Nat.lt_trans (Nat.lt_succ_self n) hn⟩
    let current := (ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v).get
      ⟨n + 1, hn⟩
    current.input.state = previous.output.next ∧
      current.input.time.val = previous.input.time.val + 1 := by
  dsimp only
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h
  change n + 1 < (ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v).length at hn
  have hprev := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail_get
    R v ⟨n, Nat.lt_trans (Nat.lt_succ_self n) hn⟩
  have hcurr := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail_get
    R v ⟨n + 1, hn⟩
  have hbound : n < (ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v).length :=
    Nat.lt_trans (Nat.lt_succ_self n) hn
  have hidxPrev : v + 1 + n < R.length :=
    (List.getElem?_eq_some_iff.mp hprev).1
  have hidxCurr : v + 1 + (n + 1) < R.length := by
    have h := (List.getElem?_eq_some_iff.mp hcurr).1
    omega
  have hgetPrev : R.get ⟨v + 1 + n, hidxPrev⟩ =
      (ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v).get ⟨n, hbound⟩ :=
    (List.getElem?_eq_some_iff.mp hprev).2
  have hgetCurr : R.get ⟨v + 1 + (n + 1), hidxCurr⟩ =
      (ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v).get ⟨n + 1, hn⟩ :=
    (List.getElem?_eq_some_iff.mp hcurr).2
  have hstep := complete_suffix_adjacent rate source rewards C_star C_h (v + 1 + n) (by omega)
  dsimp only at hstep
  have hcurrFin : (⟨v + 1 + (n + 1), hidxCurr⟩ : Fin R.length) =
      ⟨v + 1 + n + 1, by omega⟩ := by
    exact Fin.ext (Nat.add_assoc (v + 1) n 1).symm
  rw [hcurrFin] at hgetCurr
  rw [hgetPrev, hgetCurr] at hstep
  exact hstep

private theorem physical_cell_of_readout
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (c : RecordedQueueRun.RoundInput p.K)
    (hc : ReferenceLaterLiveNumericalReadout.laterLiveReadout
      (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h).get k) = some c) :
    ∃ cell : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell
        ((ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h).get k),
      cell.input = c ∧ c.enabled = true ∧
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h).get k).input.rewards = rewards ∧
      c.recordedArm = ReferenceContinuingRecordingFastPair.physicalMarkerOnRecord
        ((ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h).get k) cell.selected.view.payload true ∧
      (∀ a, c.recordedArm = some a → ∃ owner : Fin p.m,
        SnapshotRecordingKernel.owns p
          (.live cell.selected.view.payload.assignment
            (ReferenceActiveDataOwnership.choiceSnapshot cell.selected cell.states)) owner a ∧
        (∀ other, SnapshotRecordingKernel.owns p
          (.live cell.selected.view.payload.assignment
            (ReferenceActiveDataOwnership.choiceSnapshot cell.selected cell.states)) other a →
          other = owner) ∧
        ((ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h).get k).output.preparation.arms.actions owner = a ∧
        ((ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h).get k).gridFeedback owner =
          rewards ((ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate source rewards C_star C_h).get k).input.time a) ∧
      (∀ i, (cell.states i).status ≠ ActiveRoundActions.FollowerStatus.unoccupied →
        (cell.states i).lastDown = some (cell.selected.view.payload.downRecord i)) := by
  classical
  obtain ⟨cell, hcell, henabled, _, _, _, _, hrewards, hmarker, hfields, howners,
    _, _, _, _⟩ :=
      ReferenceLaterLiveNumericalReadout.laterLiveReadout_physical
        rate rewards C_star C_h source k c hc
  refine ⟨cell, hcell, henabled, hrewards, hmarker, ?_, hfields⟩
  intro a ha
  obtain ⟨owner, howns, hunique, haction, hfeedback, _⟩ := howners a ha
  exact ⟨owner, howns, hunique, haction, hfeedback⟩

private theorem physical_cell_contract
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (c : RecordedQueueRun.RoundInput p.K)
    (hc : ReferenceLaterLiveNumericalReadout.laterLiveReadout
      (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h).get k) = some c) :
    ∃ cell : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell
        ((ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h).get k),
      cell.input = c ∧ c.enabled = true ∧
      c.reward = (fun a => ((rewards
        ((ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h).get k).input.time a).val : ℝ) / (D p : ℝ)) ∧
      c.rate = cell.selected.view.payload.rate ∧
      c.recordedArm = ReferenceContinuingRecordingFastPair.physicalMarkerOnRecord
        ((ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h).get k) cell.selected.view.payload true ∧
      ∀ a, c.recordedArm = some a → ∃ owner : Fin p.m,
        SnapshotRecordingKernel.owns p
          (.live cell.selected.view.payload.assignment
            (ReferenceActiveDataOwnership.choiceSnapshot cell.selected cell.states)) owner a ∧
        (∀ other, SnapshotRecordingKernel.owns p
          (.live cell.selected.view.payload.assignment
            (ReferenceActiveDataOwnership.choiceSnapshot cell.selected cell.states)) other a →
          other = owner) ∧
        ((ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h).get k).output.preparation.arms.actions owner = a ∧
        ((ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h).get k).gridFeedback owner =
          rewards ((ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate source rewards C_star C_h).get k).input.time a := by
  obtain ⟨_, selectedNum, hselectionNum, hreward, hrate, _⟩ :=
    ReferenceLaterLiveNumericalReadout.laterLiveReadout_numerical
      (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h).get k) c hc
  obtain ⟨cell, hcell, henabled, hrewards, hmarker, howners, _⟩ :=
    physical_cell_of_readout rate source rewards C_star C_h k c hc
  have hsameNum : selectedNum = cell.selected :=
    Option.some.inj (hselectionNum.symm.trans cell.selection_actual)
  have hrate' : c.rate = cell.selected.view.payload.rate := by
    rw [hsameNum] at hrate
    exact hrate
  have hreward' : c.reward = (fun a => ((rewards
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h).get k).input.time a).val : ℝ) / (D p : ℝ)) := by
    rw [hrewards] at hreward
    exact hreward
  refine ⟨cell, hcell, henabled, hreward', hrate', hmarker, ?_⟩
  intro a ha
  obtain ⟨owner, howns, hunique, haction, hfeedback⟩ := howners a ha
  exact ⟨owner, howns, hunique, haction, hfeedback⟩

/-- For the first replacement's actual birth and every continuing record, the
full numerical input is present at its original index and carries the actual
selected assignment and physical feedback. Accepted DOWN recovery agrees with
the enabled numerical arrivals on the corresponding source prefix. -/
theorem complete_first_replacement_numerical_source_stream
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
    let s := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
    let v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
    match R[v]? with
    | none => True
    | some birth => match birth.output.preparation.coordinator with
      | .collection _ _ _ _ (.laterChosen _ _ _ _ _ _ _ _ _ installed _) =>
        let payload := installed.registers.payload
        let X := (R.drop v).take (1 + (ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v).length)
        let C := X.filterMap (ReferenceLaterLiveNumericalReadout.laterLiveReadout s)
        C.length = X.length ∧
        (∀ j : Fin X.length, let x := X.get j; ∃ cell : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell x,
          C[j.val]? = some cell.input ∧
          ReferenceLaterLiveNumericalReadout.laterLiveReadout s x = some cell.input ∧
          cell.selected.view.payload = payload ∧ cell.input.enabled = true ∧
          cell.input.reward = (fun a => ((rewards x.input.time a).val : ℝ)/(D p : ℝ)) ∧
          cell.input.rate = payload.rate ∧
          cell.input.recordedArm = ReferenceContinuingRecordingFastPair.physicalMarkerOnRecord x payload true ∧
          ∀ a, cell.input.recordedArm = some a → ∃ owner : Fin p.m,
            SnapshotRecordingKernel.owns p (.live cell.selected.view.payload.assignment
              (ReferenceActiveDataOwnership.choiceSnapshot cell.selected cell.states)) owner a ∧
            (∀ other, SnapshotRecordingKernel.owns p (.live cell.selected.view.payload.assignment
              (ReferenceActiveDataOwnership.choiceSnapshot cell.selected cell.states)) other a → other=owner) ∧
            x.output.preparation.arms.actions owner = a ∧ x.gridFeedback owner = rewards x.input.time a) ∧
        (∀ k : Fin (ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v).length,
          let r := (ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v).get k
          ∀ i : Fin (p.m-1), match (r.output.followers i).down with
          | none => True
          | some cut => match cut.outcome with
            | .accepted before _after _raw msg scan _registers _lastService =>
              msg = payload.downRecord i ∧
              ActiveFollowerDownAcceptance.recoveryQueueRecords p rate msg before scan.endpoint =
                (C.take (scan.endpoint-msg.val.sigma)).map (fun c =>
                  (true, RecordedQueueRun.quantizedArrival
                    (ReferenceFirstLaunchNumericalCell.queueParameters rate) c
                    (payload.assignment.assigned i)))
            | _ => True)
      | _ => True := by
  classical
  have hBirth :=
    ReferenceFirstReplacementNextFollowerStep.complete_first_replacement_birth_live_readout
      rate source rewards C_star C_h
  have hTail :=
    ReferenceFirstReplacementFollowerBoundary.complete_first_replacement_continuing_live_readout
      rate source rewards C_star C_h
  have hBoundary :=
    ReferenceFirstReplacementFollowerBoundary.complete_first_replacement_follower_boundary
      rate source rewards C_star C_h
  have hBudgets :=
    ReferenceFirstReplacementLiveFollowerPrefix.complete_first_replacement_logged_recovery_budgets
      rate source rewards C_star C_h
  have hEmissions :=
    ReferenceFirstReplacementAcceptedSparseEmissions.complete_first_replacement_accepted_sparse_emissions
      rate source rewards C_star C_h
  have hGeometry :=
    ReferenceFirstReplacementLiveFollowerPrefix.complete_first_replacement_continuing_geometry
      rate source rewards C_star C_h
  have hBirthFinish :=
    ReferenceFirstReplacementDownRecovery.complete_first_replacement_down_recovery_and_finish
      rate source rewards C_star C_h
  dsimp only at hBirth hTail hBoundary hBudgets hEmissions hGeometry hBirthFinish ⊢
  set R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
  set s := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
  set w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  set v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
  cases hb : R[v]? with
  | none => trivial
  | some birth =>
      simp only [hb] at hBirth hTail hBoundary hBudgets hEmissions hGeometry hBirthFinish ⊢
      cases hc : birth.output.preparation.coordinator with
      | first _ => trivial
      | live _ _ _ _ => trivial
      | dagger => trivial
      | invalidCollectionCutoff => trivial
      | collection old ledger clock cutoff outcome =>
          rw [hc] at hBirth hTail hBoundary hBudgets hEmissions hGeometry hBirthFinish
          cases outcome <;> try trivial
          rename_i core consistent started hs instruction hinstruction output hcons clockData installed arm
          dsimp only [ReferenceActivePhysicalStep.collectionInput]
            at hBirth hTail hBoundary hBudgets hEmissions hGeometry hBirthFinish ⊢
          let tail := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v
          let X := (R.drop v).take (1 + tail.length)
          let C := X.filterMap (ReferenceLaterLiveNumericalReadout.laterLiveReadout s)
          change C.length = X.length ∧ _ ∧ _
          have hstream : X = birth :: tail := by
            dsimp only [X, tail]
            exact first_replacement_stream_eq_cons R v birth hb
          obtain ⟨kBirth, _hkBirth, hrecordBirth, selectedBirth, hselectBirth,
            hpayloadBirth, _hstartedBirth, _hliveBirth, cBirth, hreadBirth,
            _hnumBirth, hreadBirthAt, _hcellBirth⟩ := hBirth
          have htailRead : ∀ k : Fin tail.length,
              ∃ c, ReferenceLaterLiveNumericalReadout.laterLiveReadout s
                (tail.get k) = some c := by
            intro k
            obtain ⟨_, cell, _, hread, _, _, _, _⟩ := hTail k
            exact ⟨cell.input, hread⟩
          have hindexed : ∀ j : Fin X.length,
              ∃ c, ReferenceLaterLiveNumericalReadout.laterLiveReadout s
                (X.get j) = some c := by
            rw [hstream]
            intro j
            cases j using Fin.cases with
            | zero => exact ⟨cBirth, by simpa using hreadBirth⟩
            | succ j =>
                obtain ⟨c, hc⟩ := htailRead j
                exact ⟨c, by simpa using hc⟩
          have hcellSpec : ∀ j : Fin X.length, let x := X.get j;
              ∃ cell : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell x,
                C[j.val]? = some cell.input ∧
                ReferenceLaterLiveNumericalReadout.laterLiveReadout s x = some cell.input ∧
                cell.selected.view.payload = installed.registers.payload ∧
                cell.input.enabled = true ∧
                cell.input.reward = (fun a => ((rewards x.input.time a).val : ℝ)/(D p : ℝ)) ∧
                cell.input.rate = installed.registers.payload.rate ∧
                cell.input.recordedArm = ReferenceContinuingRecordingFastPair.physicalMarkerOnRecord
                  x installed.registers.payload true ∧
                ∀ a, cell.input.recordedArm = some a → ∃ owner : Fin p.m,
                  SnapshotRecordingKernel.owns p
                    (.live cell.selected.view.payload.assignment
                      (ReferenceActiveDataOwnership.choiceSnapshot cell.selected cell.states)) owner a ∧
                  (∀ other, SnapshotRecordingKernel.owns p
                    (.live cell.selected.view.payload.assignment
                      (ReferenceActiveDataOwnership.choiceSnapshot cell.selected cell.states)) other a →
                    other = owner) ∧
                  x.output.preparation.arms.actions owner = a ∧
                  x.gridFeedback owner = rewards x.input.time a := by
            intro j
            dsimp only
            obtain ⟨y, hyIndex, hyRead⟩ :=
              filterMap_getElem?_of_indexed_some
                (ReferenceLaterLiveNumericalReadout.laterLiveReadout s) X hindexed j
            by_cases hj0 : j.val = 0
            · have hlookup : X[j.val]? = some birth := by
                simp [hstream, hj0]
              have hget : X.get j = birth := by
                have hself : X[j.val]? = some (X.get j) :=
                  List.getElem?_eq_some_iff.mpr ⟨j.isLt, rfl⟩
                exact Option.some.inj (hself.symm.trans hlookup)
              have hread : ReferenceLaterLiveNumericalReadout.laterLiveReadout s
                  (X.get j) = some cBirth := by rw [hget]; exact hreadBirth
              have hy : y = cBirth := Option.some.inj (hyRead.symm.trans hread)
              have hmap : C[j.val]? = some cBirth := by simpa [hy] using hyIndex
              rw [hget] at ⊢
              have hphysical := physical_cell_contract rate source rewards C_star C_h
                kBirth cBirth hreadBirthAt
              rw [hrecordBirth] at hphysical
              obtain ⟨cell, hinput, henabled, hreward, hrate, hmarker, howners⟩ := hphysical
              have hpayload : cell.selected.view.payload = installed.registers.payload := by
                have hselectionCell : birth.output.preparation.coordinator.selection =
                    some cell.selected := cell.selection_actual
                rw [hc] at hselectionCell
                have hsame := Option.some.inj (hselectionCell.symm.trans hselectBirth)
                rw [hsame]
                exact hpayloadBirth
              have hreadCell : ReferenceLaterLiveNumericalReadout.laterLiveReadout s birth =
                  some cell.input := by rw [hinput]; exact hreadBirth
              have henabledCell : cell.input.enabled = true := by rw [hinput]; exact henabled
              have hrewardCell : cell.input.reward =
                  (fun a => ((rewards birth.input.time a).val : ℝ)/(D p : ℝ)) := by
                rw [hinput]
                exact hreward
              have hratePayload : cBirth.rate = installed.registers.payload.rate := by
                rw [hpayload] at hrate
                exact hrate
              have hrateCell : cell.input.rate = installed.registers.payload.rate := by
                rw [hinput]
                exact hratePayload
              have hmarkerPayload : cBirth.recordedArm =
                  ReferenceContinuingRecordingFastPair.physicalMarkerOnRecord
                    birth installed.registers.payload true := by
                rw [hpayload] at hmarker
                exact hmarker
              have hmarkerCell : cell.input.recordedArm =
                  ReferenceContinuingRecordingFastPair.physicalMarkerOnRecord
                    birth installed.registers.payload true := by
                rw [hinput]
                exact hmarkerPayload
              have hownersCell : ∀ a, cell.input.recordedArm = some a →
                  ∃ owner : Fin p.m,
                    SnapshotRecordingKernel.owns p
                      (.live cell.selected.view.payload.assignment
                        (ReferenceActiveDataOwnership.choiceSnapshot cell.selected cell.states)) owner a ∧
                    (∀ other, SnapshotRecordingKernel.owns p
                      (.live cell.selected.view.payload.assignment
                        (ReferenceActiveDataOwnership.choiceSnapshot cell.selected cell.states)) other a →
                      other = owner) ∧
                    birth.output.preparation.arms.actions owner = a ∧ birth.gridFeedback owner = rewards birth.input.time a := by
                intro a ha
                apply howners a
                rw [hinput] at ha
                exact ha
              refine ⟨cell, ?_, hreadCell, hpayload, henabledCell, hrewardCell, hrateCell,
                hmarkerCell, hownersCell⟩
              simpa [hinput] using hmap
            · have hjpos : 0 < j.val := Nat.pos_of_ne_zero hj0
              let ktail : Fin tail.length := ⟨j.val - 1, by
                have hjlen : j.val < tail.length + 1 := by
                  simpa [hstream] using j.isLt
                omega⟩
              have hjval : j.val = ktail.val + 1 := by
                simp only [ktail]
                omega
              have hlookup : X[j.val]? = some (tail.get ktail) := by
                calc
                  X[j.val]? = (birth :: tail)[j.val]? := by simp [hstream]
                  _ = tail[ktail.val]? := by simp [hjval]
                  _ = some (tail.get ktail) :=
                    List.getElem?_eq_some_iff.mpr ⟨ktail.isLt, rfl⟩
              have hget : X.get j = tail.get ktail := by
                have hself : X[j.val]? = some (X.get j) :=
                  List.getElem?_eq_some_iff.mpr ⟨j.isLt, rfl⟩
                exact Option.some.inj (hself.symm.trans hlookup)
              obtain ⟨hindex, cellTail, hpayloadTail, hreadTail, _henabledTail,
                _hrowsTail, _hselectedTail, _hrewardsTail⟩ := hTail ktail
              have hread : ReferenceLaterLiveNumericalReadout.laterLiveReadout s
                  (X.get j) = some cellTail.input := by rw [hget]; exact hreadTail
              have hy : y = cellTail.input := Option.some.inj (hyRead.symm.trans hread)
              have hmap : C[j.val]? = some cellTail.input := by simpa [hy] using hyIndex
              let kRecord : Fin R.length := ⟨v + 1 + ktail.val,
                (List.getElem?_eq_some_iff.mp hindex).1⟩
              have hrecord : R.get kRecord = tail.get ktail :=
                (List.getElem?_eq_some_iff.mp hindex).2
              have hreadAt : ReferenceLaterLiveNumericalReadout.laterLiveReadout s
                  (R.get kRecord) = some cellTail.input := by
                rw [hrecord]
                exact hreadTail
              have hselectedTail : (tail.get ktail).output.preparation.coordinator.selection =
                  some cellTail.selected := cellTail.selection_actual
              have hphysical := physical_cell_contract rate source rewards C_star C_h
                kRecord cellTail.input hreadAt
              rw [hrecord] at hphysical
              obtain ⟨cell, hinput, henabled, hreward, hrate, hmarker, howners⟩ := hphysical
              have hsame : cell.selected = cellTail.selected :=
                Option.some.inj (cell.selection_actual.symm.trans hselectedTail)
              have hpayload : cell.selected.view.payload = installed.registers.payload := by
                rw [hsame]
                exact hpayloadTail
              have hreadCell : ReferenceLaterLiveNumericalReadout.laterLiveReadout s
                  (tail.get ktail) = some cell.input := by
                rw [hinput]
                exact hreadTail
              have henabledCell : cell.input.enabled = true := by rw [hinput]; exact henabled
              have hrewardCell : cell.input.reward =
                  (fun a => ((rewards (tail.get ktail).input.time a).val : ℝ)/(D p : ℝ)) := by
                rw [hinput]
                exact hreward
              have hratePayload : cellTail.input.rate = installed.registers.payload.rate := by
                rw [hpayload] at hrate
                exact hrate
              have hrateCell : cell.input.rate = installed.registers.payload.rate := by
                rw [hinput]
                exact hratePayload
              have hmarkerPayload : cellTail.input.recordedArm =
                  ReferenceContinuingRecordingFastPair.physicalMarkerOnRecord
                    (tail.get ktail) installed.registers.payload true := by
                rw [hpayload] at hmarker
                exact hmarker
              have hmarkerCell : cell.input.recordedArm =
                  ReferenceContinuingRecordingFastPair.physicalMarkerOnRecord
                    (tail.get ktail) installed.registers.payload true := by
                rw [hinput]
                exact hmarkerPayload
              have hownersCell : ∀ a, cell.input.recordedArm = some a →
                  ∃ owner : Fin p.m,
                    SnapshotRecordingKernel.owns p
                      (.live cell.selected.view.payload.assignment
                        (ReferenceActiveDataOwnership.choiceSnapshot cell.selected cell.states)) owner a ∧
                    (∀ other, SnapshotRecordingKernel.owns p
                      (.live cell.selected.view.payload.assignment
                        (ReferenceActiveDataOwnership.choiceSnapshot cell.selected cell.states)) other a →
                      other = owner) ∧
                    (tail.get ktail).output.preparation.arms.actions owner = a ∧
                    (tail.get ktail).gridFeedback owner = rewards (tail.get ktail).input.time a := by
                intro a ha
                apply howners a
                rw [hinput] at ha
                exact ha
              rw [hget] at ⊢
              refine ⟨cell, ?_, hreadCell, hpayload, henabledCell, hrewardCell, hrateCell,
                hmarkerCell, hownersCell⟩
              simpa [hinput] using hmap
          have hlength := filterMap_length_of_indexed_some
            (ReferenceLaterLiveNumericalReadout.laterLiveReadout s) X hindexed
          refine ⟨hlength, hcellSpec, ?_⟩
          intro k i
          let r := (ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v).get k
          cases hdown : (r.output.followers i).down with
          | none => trivial
          | some cut =>
            cases houtcome : cut.outcome with
            | skipped _ _ => simp [houtcome]
            | inputFailure _ _ => simp [houtcome]
            | decodeOrParseRejected _ _ _ => simp [houtcome]
            | parsedButUnaccepted _ _ _ _ => simp [houtcome]
            | outputFailure _ _ => simp [houtcome]
            | accepted before after raw msg scan registers lastService =>
                simp only [houtcome] at ⊢
                have hbudget := hBudgets k i
                simp only [r, hdown] at hbudget
                obtain ⟨budgetState, budgetMemory, logged, hbudgetPrepared,
                  hbudgetUnoccupied, _hlogging, hbudgetInput, _hcut, _hvalid,
                  hbudgetSigma, _hq, _hbudgetChecked, _hmass, _hdomain, _hreplay,
                  _hprefix⟩ := hbudget
                obtain ⟨_hindex, _hrows, _hselectedIndex, _hrewards, selected,
                  _hselection, _hselectionPayload, _hlive, _hgrid, _hproposalBits,
                  hfollowers⟩ := hBoundary k
                obtain ⟨currentState, currentMemory, _currentNext, _currentNextMemory,
                  hcurrentInput, _hcurrentDomain, _hcurrentMass, _hcurrentZero,
                  _hcurrentStrict, _hcurrentBusy, _hcurrentPair, _hcurrentChronology,
                  _hcurrentSigma, _hcurrentSigmaTime, _hcurrentCredit,
                  _hcurrentInterruption, hcurrentPrepared, _hcurrentOutput,
                  _hcurrentFailure, _hcurrentInitializationFailure,
                  _hcurrentNextDomain, _hcurrentNextMass, _hcurrentNextDelta,
                  _hcurrentNextZero, _hcurrentNextStrict, _hcurrentNextBusy,
                  _hcurrentBusyForward⟩ := hfollowers i
                have hpreparedStates : currentState = budgetState := by
                  have hconfig := hcurrentPrepared.symm.trans hbudgetPrepared
                  simp only [DeclaredFollowerLocalRound.LocalConfiguration.ordinary.injEq]
                    at hconfig
                  exact hconfig.1
                have hcurrentStatus : currentState.status = .unoccupied := by
                  rw [hpreparedStates]
                  exact hbudgetUnoccupied
                let P : ℕ → Prop := fun n => ∀ hn : n < tail.length,
                  ∃ st memory,
                    (tail.get ⟨n, hn⟩).input.state.followers i = .ordinary st memory ∧
                    st.status = .unoccupied
                have hPk : P k.val := by
                  intro hk
                  exact ⟨currentState, currentMemory, hcurrentInput, hcurrentStatus⟩
                have hPstep : ∀ n, n < k.val → P (n + 1) → P n := by
                  intro n hnk hafter
                  have hklt := k.isLt
                  have hnextBound : n + 1 < (ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v).length := by
                    omega
                  obtain ⟨nextState, nextMemory, hnextInput, hnextStatus⟩ :=
                    hafter (by simpa [tail] using hnextBound)
                  have hpreviousBound : n <
                      (ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v).length := by
                    omega
                  obtain ⟨_hindex, _hrows, _hselectedIndex, _hrewards,
                    _selected, _hselection, _hselectionPayload, _hlive, _hgrid,
                    _hproposalBits, previousFollowers⟩ := hBoundary ⟨n, hpreviousBound⟩
                  obtain ⟨previousState, previousMemory, previousNext, previousNextMemory,
                    hpreviousInput, _hpreviousDomain, _hpreviousMass, _hpreviousZero,
                    _hpreviousStrict, _hpreviousBusy, _hpreviousPair,
                    _hpreviousChronology, _hpreviousSigma, _hpreviousSigmaTime,
                    _hpreviousCredit, _hpreviousInterruption, _hpreviousPrepared,
                    hpreviousOutput, _hpreviousFailure,
                    _hpreviousInitializationFailure, _hpreviousNextDomain,
                    _hpreviousNextMass, _hpreviousNextDelta, _hpreviousNextZero,
                    _hpreviousNextStrict, _hpreviousNextBusy, hpreviousBusyForward⟩ :=
                    previousFollowers i
                  have hadjacent := continuing_tail_adjacent rate source rewards C_star C_h
                    v n hnextBound
                  dsimp only at hadjacent
                  have hstateConfig := congrArg (fun st => st.followers i) hadjacent.1
                  have hpreviousNextConfig :
                      ((tail.get ⟨n, by omega⟩).output.next.followers i) =
                        DeclaredFollowerLocalRound.LocalConfiguration.ordinary
                          previousNext previousNextMemory := by
                    calc
                      _ = ((tail.get ⟨n, by omega⟩).output.followers i).configuration := by
                        rw [(tail.get ⟨n, by omega⟩).output_eq]
                        rfl
                      _ = .ordinary previousNext previousNextMemory := hpreviousOutput
                  have hnextStates : nextState = previousNext := by
                    have hconfig :
                        DeclaredFollowerLocalRound.LocalConfiguration.ordinary nextState nextMemory =
                        DeclaredFollowerLocalRound.LocalConfiguration.ordinary
                          previousNext previousNextMemory := by
                      calc
                        DeclaredFollowerLocalRound.LocalConfiguration.ordinary nextState nextMemory =
                            (tail.get ⟨n + 1, by omega⟩).input.state.followers i :=
                              hnextInput.symm
                        _ = (tail.get ⟨n, by omega⟩).output.next.followers i := hstateConfig
                        _ = .ordinary previousNext previousNextMemory := hpreviousNextConfig
                    simp only [DeclaredFollowerLocalRound.LocalConfiguration.ordinary.injEq]
                      at hconfig
                    exact hconfig.1
                  have hpreviousStatus : previousState.status = .unoccupied := by
                    by_contra hnot
                    have hbusy : previousState.status ≠ .unoccupied := by
                      intro heq
                      exact hnot heq
                    have hnextBusy := hpreviousBusyForward hbusy
                    rw [← hnextStates] at hnextBusy
                    exact hnextBusy hnextStatus
                  intro hn
                  exact ⟨previousState, previousMemory, hpreviousInput, hpreviousStatus⟩
                have hprefix := backward_prefix_of_step k.val hPstep hPk
                have hcurrentBoundary := hBoundary k
                have hcurrentCell := hTail k
                obtain ⟨_hcellIndex, cellTail, _hcellPayload, _hcellRead,
                  _hcellEnabled, _hcellRows, _hcellSelected, _hcellReward⟩ := hcurrentCell
                have htailCellUnoccupied : (cellTail.states i).status = .unoccupied := by
                  have hprepared := cellTail.ordinary i
                  have hprep := hcurrentPrepared
                  have hconfig := hprepared.symm.trans hprep
                  simp only [DeclaredFollowerLocalRound.LocalConfiguration.ordinary.injEq]
                    at hconfig
                  rw [hconfig.1]
                  exact hcurrentStatus
                have hEm := hEmissions k i
                simp only [r, hdown, houtcome] at hEm
                obtain ⟨hmessage, hEmInput, _hnoReset, hdateEmission⟩ := hEm
                refine ⟨hmessage, ?_⟩
                have hbefore : before = logged :=
                  Option.some.inj (hEmInput.symm.trans hbudgetInput)
                have houtcomeLogged : cut.outcome =
                    .accepted logged after raw msg scan registers lastService := by
                  simpa only [hbefore] using houtcome
                have hactualAccepted :=
                  ReferenceFollowerSparseEmissionRecovery.actualAcceptedCut_downTransition
                    r i logged cut after raw msg scan registers lastService
                    hbudgetInput hdown houtcomeLogged
                have hchecked := ActiveFollowerDownAcceptance.downTransition_accepted_checked p
                  (r.output.preparation.followers.followers i).follower
                  (r.output.preparation.followers.followers i).row
                  (r.output.preparation.followers.followers i).time
                  (r.output.preparation.feedback.observations
                    (PublicDiscreteDraws.followerPlayer p.two_le_m i))
                  rate logged after raw msg scan registers lastService hactualAccepted
                have hpreparedTime := r.output.preparation.follower_alignment i
                have hlocalTime :
                    (r.output.preparation.followers.followers i).time = r.input.time :=
                  hpreparedTime.2.2.1
                have hendpoint : scan.endpoint ≤ r.input.time.val + 2 := by
                  rw [← hlocalTime]
                  exact hchecked.2.2.2.1
                have hgeometryK := hGeometry.2 k
                obtain ⟨_, hcurrentTime, _, _, _, _⟩ := hgeometryK
                have hbirthTime : birth.input.time.val = s + v := by
                  have htime := complete_suffix_record_time rate source rewards C_star C_h
                    kBirth
                  rw [hrecordBirth] at htime
                  simpa only [_hkBirth] using htime
                have hmessageSigma : msg.val.sigma = s + v + 1 := by
                  rw [hmessage, hbudgetSigma, hGeometry.1, hbirthTime]
                let count := scan.endpoint - msg.val.sigma
                have hcountBound : count ≤ k.val + 2 := by
                  dsimp [count]
                  rw [hcurrentTime, hbirthTime] at hendpoint
                  omega
                have hXLength : X.length = tail.length + 1 := by
                  rw [hstream]
                  simp
                have hcountWithin : count ≤ X.length := by
                  rw [hXLength]
                  dsimp [tail]
                  omega
                have hcountC : count ≤ C.length := by
                  rw [hlength]
                  exact hcountWithin
                have hqueueLength :
                    (ActiveFollowerDownAcceptance.recoveryQueueRecords p rate msg before
                        scan.endpoint).length = count := by
                  simp [count, ActiveFollowerDownAcceptance.recoveryQueueRecords,
                    ActiveFollowerDownAcceptance.recoveryArrivals,
                    ActiveFollowerDownAcceptance.recoveryRounds,
                    SparseCalendarReplay.sparseCalendarRounds]
                let physicalQueue := (C.take count).map (fun c =>
                  (true, RecordedQueueRun.quantizedArrival
                    (ReferenceFirstLaunchNumericalCell.queueParameters rate) c
                    (installed.registers.payload.assignment.assigned i)))
                have hphysicalLength : physicalQueue.length = count := by
                  simp [physicalQueue, List.length_take, Nat.min_eq_left hcountC]
                change ActiveFollowerDownAcceptance.recoveryQueueRecords p rate msg before
                    scan.endpoint = physicalQueue
                apply List.ext_getElem
                · rw [hqueueLength, hphysicalLength]
                · intro q hqQueue hqPhysical
                  have hqCount : q < count := by
                    rw [← hqueueLength]
                    exact hqQueue
                  have hqX : q < X.length := lt_of_lt_of_le hqCount hcountWithin
                  have hqC : q < C.length := by rw [hlength]; exact hqX
                  let streamIndex : Fin X.length := ⟨q, hqX⟩
                  obtain ⟨cell, hmap, hread, hpayloadCell, _henabled,
                    _hreward, _hrate, _hmarker, _howners⟩ := hcellSpec streamIndex
                  have hCcell : C.get ⟨q, hqC⟩ = cell.input := by
                    have hself := List.getElem?_eq_some_iff.mpr ⟨hqC, rfl⟩
                    exact Option.some.inj (hself.symm.trans hmap)
                  have hleft :
                      (ActiveFollowerDownAcceptance.recoveryQueueRecords p rate msg before
                        scan.endpoint)[q]'hqQueue =
                        (true, ActiveFollowerDownAcceptance.bufferArrivalAt p rate msg before
                          (msg.val.sigma + q)) := by
                    simp [ActiveFollowerDownAcceptance.recoveryQueueRecords,
                      ActiveFollowerDownAcceptance.recoveryArrivals,
                      ActiveFollowerDownAcceptance.recoveryRounds,
                      SparseCalendarReplay.sparseCalendarRounds]
                  have hright : physicalQueue[q]'hqPhysical =
                      (true, RecordedQueueRun.quantizedArrival
                        (ReferenceFirstLaunchNumericalCell.queueParameters rate)
                        (C.get ⟨q, hqC⟩)
                        (installed.registers.payload.assignment.assigned i)) := by
                    simp [physicalQueue, List.getElem_map, List.getElem_take]
                  have hdateLower : msg.val.sigma ≤ msg.val.sigma + q := by omega
                  have hdateUpper : msg.val.sigma + q < scan.endpoint := by
                    have hstart : msg.val.sigma ≤ scan.endpoint := by
                      have := hchecked.2.2.1
                      omega
                    dsimp [count] at hqCount
                    omega
                  obtain ⟨_hbufferEmission, sourceIndex, hsourceIndex, hsourceAtDate⟩ :=
                    hdateEmission (msg.val.sigma + q) hdateLower hdateUpper
                  have hsourceIndexVal : sourceIndex.val = v + q := by
                    rw [hmessageSigma] at hsourceIndex
                    omega
                  have hqBound : q ≤ k.val + 1 := by
                    dsimp [count] at hqCount
                    omega
                  have hsourceEq : R.get sourceIndex = X.get streamIndex := by
                    by_cases hqzero : q = 0
                    · have hsourceV : sourceIndex.val = v := by omega
                      have hsourceFin : sourceIndex = kBirth :=
                        Fin.ext (by rw [_hkBirth]; exact hsourceV)
                      have hzeroLt : 0 < X.length := by rw [hXLength]; simp
                      have hlookupZero : X[0]? = some birth := by
                        rw [hstream]
                        simp
                      have hselfZero : X[0]? = some (X.get ⟨0, hzeroLt⟩) :=
                        List.getElem?_eq_some_iff.mpr ⟨hzeroLt, rfl⟩
                      have hgetZero : X.get ⟨0, hzeroLt⟩ = birth :=
                        Option.some.inj (hselfZero.symm.trans hlookupZero)
                      have hstreamZero : streamIndex = ⟨0, hzeroLt⟩ := Fin.ext hqzero
                      have hgetBirth : X.get streamIndex = birth := by
                        rw [hstreamZero]
                        exact hgetZero
                      calc
                        R.get sourceIndex = R.get kBirth := by rw [hsourceFin]
                        _ = birth := hrecordBirth
                        _ = X.get streamIndex := hgetBirth.symm
                    · have hqpos : 0 < q := Nat.pos_of_ne_zero hqzero
                      let n := q - 1
                      have hqeq : q = n + 1 := by dsimp [n]; omega
                      have hnle : n ≤ k.val := by dsimp [n]; omega
                      have hnBound : n < tail.length := by
                        dsimp [tail, n]
                        omega
                      let tailIndex : Fin tail.length := ⟨n, hnBound⟩
                      obtain ⟨hindexTail, cellTailAt, hpayloadTail, hreadTail,
                        _henabledTail, _hrowsTail, _hselectedTail, _hrewardsTail⟩ :=
                        hTail tailIndex
                      have hstreamIndexBound : n + 1 < X.length := by
                        rw [hXLength]
                        omega
                      have hstreamTail : streamIndex =
                          (⟨n + 1, hstreamIndexBound⟩ : Fin X.length) :=
                        Fin.ext hqeq
                      have hgetTail : X.get streamIndex = tail.get tailIndex := by
                        rw [hstreamTail]
                        have hlookupTail : X[n + 1]? = some (tail.get tailIndex) := by
                          rw [hstream]
                          simp [tailIndex]
                        have hselfTail : X[n + 1]? =
                            some (X.get ⟨n + 1, hstreamIndexBound⟩) :=
                          List.getElem?_eq_some_iff.mpr ⟨hstreamIndexBound, rfl⟩
                        exact Option.some.inj (hselfTail.symm.trans hlookupTail)
                      have htailBound := (List.getElem?_eq_some_iff.mp hindexTail).1
                      have hsourceCoordinate : sourceIndex.val = v + 1 + n := by
                        rw [hsourceIndexVal, hqeq]
                        omega
                      have hsourceFin : sourceIndex = ⟨v + 1 + n, htailBound⟩ :=
                        Fin.ext hsourceCoordinate
                      have htailGet :
                          R.get ⟨v + 1 + n, htailBound⟩ = tail.get tailIndex :=
                        (List.getElem?_eq_some_iff.mp hindexTail).2
                      calc
                        R.get sourceIndex = R.get ⟨v + 1 + n, htailBound⟩ := by
                          rw [hsourceFin]
                        _ = tail.get tailIndex := htailGet
                        _ = X.get streamIndex := hgetTail.symm
                  rw [hsourceEq] at hsourceAtDate
                  by_cases hqzero : q = 0
                  · have hzeroLt : 0 < X.length := by rw [hXLength]; simp
                    have hlookupZero : X[0]? = some birth := by
                      rw [hstream]
                      simp
                    have hselfZero : X[0]? = some (X.get ⟨0, hzeroLt⟩) :=
                      List.getElem?_eq_some_iff.mpr ⟨hzeroLt, rfl⟩
                    have hgetZero : X.get ⟨0, hzeroLt⟩ = birth :=
                      Option.some.inj (hselfZero.symm.trans hlookupZero)
                    have hstreamZero : streamIndex = ⟨0, hzeroLt⟩ := Fin.ext hqzero
                    have hgetBirth : X.get streamIndex = birth := by
                      rw [hstreamZero]
                      exact hgetZero
                    cases hgetBirth
                    obtain ⟨birthState, birthMemory, _birthLogged, _hbirthInput,
                      hbirthUnoccupied, hbirthPrepared, _hbirthRest⟩ := hBirthFinish.2 i
                    have hunoccupied : (cell.states i).status = .unoccupied := by
                      have hordinary := cell.ordinary i
                      have hconfig := hordinary.symm.trans hbirthPrepared
                      simp only [DeclaredFollowerLocalRound.LocalConfiguration.ordinary.injEq]
                        at hconfig
                      rw [hconfig.1]
                      exact hbirthUnoccupied
                    have hfields : ∀ j,
                        (cell.states j).status ≠ .unoccupied →
                          (cell.states j).lastDown =
                            some (cell.selected.view.payload.downRecord j) := by
                      intro j hbusy
                      obtain ⟨birthStateJ, birthMemoryJ, _birthLoggedJ, _hinputJ,
                        hbirthUnoccupiedJ, hbirthPreparedJ, _hbirthRestJ⟩ :=
                        hBirthFinish.2 j
                      have hordinary := cell.ordinary j
                      have hconfig := hordinary.symm.trans hbirthPreparedJ
                      simp only [DeclaredFollowerLocalRound.LocalConfiguration.ordinary.injEq]
                        at hconfig
                      have hstateEq : cell.states j = birthStateJ := hconfig.1
                      have hfalse : False := hbusy (by rw [hstateEq, hbirthUnoccupiedJ])
                      exact False.elim hfalse
                    have harrival :=
                      ReferenceFirstLiveUnoccupiedEmission.emissionContribution_eq_quantizedArrival
                        (X.get streamIndex) cell hfields i hunoccupied
                    rw [hpayloadCell, ← hmessage] at harrival
                    have hbufferArrival :
                        ActiveFollowerDownAcceptance.bufferArrivalAt p rate msg before
                          (msg.val.sigma + q) =
                          RecordedQueueRun.quantizedArrival
                            (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell.input
                            (installed.registers.payload.assignment.assigned i) :=
                      hsourceAtDate.trans harrival
                    have hCcell' : C.get ⟨q, hqC⟩ = cell.input := by
                      rw [hCcell]
                    rw [hleft, hright, hCcell']
                    exact congrArg (Prod.mk true) hbufferArrival
                  · have hqpos : 0 < q := Nat.pos_of_ne_zero hqzero
                    let n := q - 1
                    have hqeq : q = n + 1 := by dsimp [n]; omega
                    have hnle : n ≤ k.val := by dsimp [n]; omega
                    have hnBound : n < tail.length := by
                      dsimp [tail, n]
                      omega
                    let tailIndex : Fin tail.length := ⟨n, hnBound⟩
                    obtain ⟨_hindexTail, cellTailAt, hpayloadTail, hreadTail,
                      _henabledTail, _hrowsTail, _hselectedTail, _hrewardsTail⟩ :=
                      hTail tailIndex
                    have hstreamIndexBound : n + 1 < X.length := by
                      rw [hXLength]
                      omega
                    have hstreamTail : streamIndex =
                        (⟨n + 1, hstreamIndexBound⟩ : Fin X.length) :=
                      Fin.ext hqeq
                    have hgetTail : X.get streamIndex = tail.get tailIndex := by
                      rw [hstreamTail]
                      have hlookupTail : X[n + 1]? = some (tail.get tailIndex) := by
                        rw [hstream]
                        simp [tailIndex]
                      have hselfTail : X[n + 1]? =
                          some (X.get ⟨n + 1, hstreamIndexBound⟩) :=
                        List.getElem?_eq_some_iff.mpr ⟨hstreamIndexBound, rfl⟩
                      exact Option.some.inj (hselfTail.symm.trans hlookupTail)
                    have hreadEq := congrArg
                      (fun x => ReferenceLaterLiveNumericalReadout.laterLiveReadout s x)
                      hgetTail
                    rw [hread, hreadTail] at hreadEq
                    have hinputEq : cell.input = cellTailAt.input :=
                      Option.some.inj hreadEq
                    have hCtail : C.get ⟨q, hqC⟩ = cellTailAt.input := by
                      rw [hCcell, hinputEq]
                    have hPn := hprefix n hnle
                    have hprefixBound : n < tail.length := by exact hnBound
                    obtain ⟨prefixState, prefixMemory, hprefixInput,
                      hprefixUnoccupied⟩ := hPn hprefixBound
                    obtain ⟨_hindexBoundary, _hrowsBoundary, _hselectedBoundary,
                      _hrewardsBoundary, _selectedBoundary, _hselectionBoundary,
                      _hselectionPayloadBoundary, _hliveBoundary, _hgridBoundary,
                      _hproposalBoundary, hfollowersAt⟩ := hBoundary tailIndex
                    obtain ⟨stateAt, memoryAt, _nextAt, _nextMemoryAt, hinputAt,
                      _hdomainAt, _hmassAt, _hzeroAt, _hstrictAt, hbusyAt,
                      _hpairAt, _hchronologyAt, _hsigmaAt, _hsigmaTimeAt, _hcreditAt,
                      _hinterruptionAt, hpreparedAt, _houtputAt, _hfailureAt,
                      _hinitializationAt, _hnextDomainAt, _hnextMassAt, _hnextDeltaAt,
                      _hnextZeroAt, _hnextStrictAt, _hnextBusyAt, _hbusyForwardAt⟩ :=
                      hfollowersAt i
                    have hcellInputState : cellTailAt.states i = stateAt := by
                      have hconfig := (cellTailAt.ordinary i).symm.trans hpreparedAt
                      simp only [DeclaredFollowerLocalRound.LocalConfiguration.ordinary.injEq]
                        at hconfig
                      exact hconfig.1
                    have hprefixState : prefixState = stateAt := by
                      have hconfig := hprefixInput.symm.trans hinputAt
                      simp only [DeclaredFollowerLocalRound.LocalConfiguration.ordinary.injEq]
                        at hconfig
                      exact hconfig.1
                    have hunoccupied :
                        (cellTailAt.states i).status = .unoccupied := by
                      rw [hcellInputState, ← hprefixState]
                      exact hprefixUnoccupied
                    have hfields : ∀ j,
                        (cellTailAt.states j).status ≠ .unoccupied →
                          (cellTailAt.states j).lastDown =
                            some (cellTailAt.selected.view.payload.downRecord j) := by
                      intro j hbusy
                      obtain ⟨stateJ, memoryJ, _nextJ, _nextMemoryJ, _hinputJ,
                        _hdomainJ, _hmassJ, _hzeroJ, _hstrictJ, hbusyJ, _hpairJ,
                        _hchronologyJ, _hsigmaJ, _hsigmaTimeJ, _hcreditJ,
                        _hinterruptionJ, hpreparedJ, _houtputJ, _hfailureJ,
                        _hinitializationJ, _hnextDomainJ, _hnextMassJ, _hnextDeltaJ,
                        _hnextZeroJ, _hnextStrictJ, _hnextBusyJ, _hbusyForwardJ⟩ :=
                        hfollowersAt j
                      have hconfig := (cellTailAt.ordinary j).symm.trans hpreparedJ
                      simp only [DeclaredFollowerLocalRound.LocalConfiguration.ordinary.injEq]
                        at hconfig
                      have hstateEq : cellTailAt.states j = stateJ := hconfig.1
                      have hstateBusy : stateJ.status ≠ .unoccupied := by
                        intro heq
                        apply hbusy
                        rw [hstateEq, heq]
                      have hlast := (hbusyJ hstateBusy).1
                      rw [← hstateEq, ← hpayloadTail] at hlast
                      exact hlast
                    have harrival :=
                      ReferenceFirstLiveUnoccupiedEmission.emissionContribution_eq_quantizedArrival
                        (tail.get tailIndex) cellTailAt hfields i hunoccupied
                    rw [hpayloadTail, ← hmessage] at harrival
                    have hcontributionEq := congrArg
                      (fun record => ReferenceFollowerSparseEmissionRecovery.emissionContribution
                        msg i record) hgetTail
                    have harrivalAtCell := hcontributionEq.trans harrival
                    have hbufferArrival :
                        ActiveFollowerDownAcceptance.bufferArrivalAt p rate msg before
                          (msg.val.sigma + q) =
                          RecordedQueueRun.quantizedArrival
                            (ReferenceFirstLaunchNumericalCell.queueParameters rate)
                            cellTailAt.input
                            (installed.registers.payload.assignment.assigned i) :=
                      hsourceAtDate.trans harrivalAtCell
                    rw [hleft, hright, hCtail]
                    exact congrArg (Prod.mk true) hbufferArrival

end Bandits.Support.ReferenceFirstReplacementNumericalSourceRecovery
end
