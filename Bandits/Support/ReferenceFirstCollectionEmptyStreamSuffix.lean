/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionFormationOrigin

import Lean.Elab.Tactic.Omega

/-!
# Physical suffix after the first empty collection stream

Sources: `sources/zip4/manuscript/06_interruptions.tex:425-431,477-481`,
`sources/zip4/manuscript/05_binary_transport.tex:70-124`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:44-64,100-108`.

This module identifies the actual finite collection window and its physical
continuation inside the same computed execution. Failed records remain in the
continuation, and phase and pending conclusions are restricted to the
collection window.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open Bandits.Support.ConstructorDimensions

namespace Bandits.Support.ReferenceFirstCollectionEmptyStreamSuffix

variable {p : ConstructorDimensions.Parameters}

private theorem roundInput_eq_of_fields
    {rate : ReferenceActivePhysicalStep.RateInput p}
    {x y : ReferenceActivePhysicalStep.RoundInput p rate}
    (hstate : x.state = y.state) (hrows : x.rows = y.rows)
    (hselected : x.selected = y.selected) (htime : x.time.val = y.time.val)
    (hrewards : x.rewards = y.rewards) : x = y := by
  cases x with
  | mk xs xr xselected xt xactive xrewards =>
    cases y with
    | mk ys yr yselected yt yactive yrewards =>
      dsimp at hstate hrows hselected htime hrewards
      subst ys
      subst yr
      subst yselected
      subst yrewards
      have htime' : xt = yt := Fin.ext htime
      subst yt
      have hactive : xactive = yactive := Subsingleton.elim _ _
      subst yactive
      rfl

private theorem actual_run_suffix_split
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start left right : ℕ)
    (hspan : start + (left + right) ≤ p.T)
    (mode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start) :
    let P := ReferenceActivePhysicalHorizon.run initial rows selected rewards start left
      (by omega) mode
    let modeP := (ReferenceActivePhysicalHorizon.run_allActiveAtEnd initial rows selected
      rewards start left (by omega) mode)
    let S := ReferenceActivePhysicalHorizon.run P.finalState rows selected rewards
      (start + left) right (by omega) modeP
    (ReferenceActivePhysicalHorizon.run initial rows selected rewards start
      (left + right) hspan mode).finalState = S.finalState ∧
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start
        (left + right) hspan mode).records = P.records ++ S.records := by
  dsimp only
  let P := ReferenceActivePhysicalHorizon.run initial rows selected rewards start left
    (by omega) mode
  let modeP := (ReferenceActivePhysicalHorizon.run_allActiveAtEnd initial rows selected
    rewards start left (by omega) mode)
  let S := ReferenceActivePhysicalHorizon.run P.finalState rows selected rewards
    (start + left) right (by omega) modeP
  have hsplit : ∀ (j : ℕ) (hj : j ≤ right)
      (hfull : start + (left + j) ≤ p.T)
      (hsuffix : start + left + j ≤ p.T),
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start
        (left + j) hfull mode).finalState =
          (ReferenceActivePhysicalHorizon.run P.finalState rows selected rewards
            (start + left) j hsuffix modeP).finalState ∧
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start
        (left + j) hfull mode).records =
          P.records ++ (ReferenceActivePhysicalHorizon.run P.finalState rows selected
            rewards (start + left) j hsuffix modeP).records := by
    intro j
    induction j with
    | zero =>
        intro hj hfull hsuffix
        constructor
        · change P.finalState =
            (ReferenceActivePhysicalHorizon.run P.finalState rows selected rewards
              (start + left) 0 hsuffix modeP).finalState
          rw [ReferenceActivePhysicalHorizon.run_zero_final]
        · change P.records = P.records ++
            (ReferenceActivePhysicalHorizon.run P.finalState rows selected rewards
              (start + left) 0 hsuffix modeP).records
          rw [ReferenceActivePhysicalHorizon.run_zero_records]
          simp
    | succ j ih =>
        intro hj hfull hsuffix
        have hprev := ih (by omega) (by omega) (by omega)
        let x := ReferenceActivePhysicalHorizon.roundInputAt initial rows selected
          rewards start mode
          (ReferenceActivePhysicalHorizon.run initial rows selected rewards start
            (left + j) (by omega) mode)
          ⟨start + (left + j), by omega, by omega⟩
        let y := ReferenceActivePhysicalHorizon.roundInputAt P.finalState rows selected
          rewards (start + left) modeP
          (ReferenceActivePhysicalHorizon.run P.finalState rows selected rewards
            (start + left) j (by omega) modeP)
          ⟨start + left + j, by omega, by omega⟩
        have hinput : x = y := by
          exact roundInput_eq_of_fields hprev.1 rfl rfl (by
            dsimp [x, y, ReferenceActivePhysicalHorizon.roundInputAt]
            omega) rfl
        have hfullStep := ReferenceActivePhysicalHorizon.run_successor_step initial rows
          selected rewards start (left + j) hfull mode
        have hsuffixStep := ReferenceActivePhysicalHorizon.run_successor_step P.finalState
          rows selected rewards (start + left) j hsuffix modeP
        have hfullStep' :
            ReferenceActivePhysicalHorizon.run initial rows selected rewards start
              (left + (j + 1)) hfull mode =
              ReferenceActivePhysicalHorizon.foldRound initial rows selected rewards start mode
                (ReferenceActivePhysicalHorizon.run initial rows selected rewards start
                  (left + j) (by omega) mode) ⟨start + (left + j), by omega, by omega⟩ := by
          simpa only [Nat.add_succ] using hfullStep
        have hfullEquations := ReferenceActivePhysicalHorizon.foldRound_equations
          initial rows selected rewards start mode
          (ReferenceActivePhysicalHorizon.run initial rows selected rewards start
            (left + j) (by omega) mode) ⟨start + (left + j), by omega, by omega⟩
        have hsuffixEquations := ReferenceActivePhysicalHorizon.foldRound_equations
          P.finalState rows selected rewards (start + left) modeP
          (ReferenceActivePhysicalHorizon.run P.finalState rows selected rewards
            (start + left) j (by omega) modeP) ⟨start + left + j, by omega, by omega⟩
        rw [hfullStep', hsuffixStep]
        constructor
        · have hfullFinal :
              (ReferenceActivePhysicalHorizon.foldRound initial rows selected rewards start
                mode (ReferenceActivePhysicalHorizon.run initial rows selected rewards start
                  (left + j) (by omega) mode)
                ⟨start + (left + j), by omega, by omega⟩).finalState =
                (ReferenceActivePhysicalStep.step x).next := by
            simpa [x] using hfullEquations.1
          have hsuffixFinal :
              (ReferenceActivePhysicalHorizon.foldRound P.finalState rows selected rewards
                (start + left) modeP
                (ReferenceActivePhysicalHorizon.run P.finalState rows selected rewards
                  (start + left) j (by omega) modeP)
                ⟨start + left + j, by omega, by omega⟩).finalState =
                (ReferenceActivePhysicalStep.step y).next := by
            simpa [y] using hsuffixEquations.1
          rw [hfullFinal, hsuffixFinal]
          exact congrArg (fun input => (ReferenceActivePhysicalStep.step input).next) hinput
        · have hfullRecords :
              (ReferenceActivePhysicalHorizon.foldRound initial rows selected rewards start
                mode (ReferenceActivePhysicalHorizon.run initial rows selected rewards start
                  (left + j) (by omega) mode)
                ⟨start + (left + j), by omega, by omega⟩).records =
                (ReferenceActivePhysicalHorizon.run initial rows selected rewards start
                  (left + j) (by omega) mode).records ++
                  [⟨x, ReferenceActivePhysicalStep.step x, rfl⟩] := by
            simpa [x] using hfullEquations.2
          have hsuffixRecords :
              (ReferenceActivePhysicalHorizon.foldRound P.finalState rows selected rewards
                (start + left) modeP
                (ReferenceActivePhysicalHorizon.run P.finalState rows selected rewards
                  (start + left) j (by omega) modeP)
                ⟨start + left + j, by omega, by omega⟩).records =
                (ReferenceActivePhysicalHorizon.run P.finalState rows selected rewards
                  (start + left) j (by omega) modeP).records ++
                  [⟨y, ReferenceActivePhysicalStep.step y, rfl⟩] := by
            simpa [y] using hsuffixEquations.2
          rw [hfullRecords, hsuffixRecords, hprev.2, List.append_assoc]
          have hrecord :
              (⟨x, ReferenceActivePhysicalStep.step x, rfl⟩ :
                ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) =
              ⟨y, ReferenceActivePhysicalStep.step y, rfl⟩ := by
            exact congrArg (fun input =>
              (⟨input, ReferenceActivePhysicalStep.step input, rfl⟩ :
                ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))) hinput
          exact congrArg (fun record =>
            P.records ++
              ((ReferenceActivePhysicalHorizon.run P.finalState rows selected rewards
                (start + left) j (by omega) modeP).records ++ [record])) hrecord
  have hlast := hsplit right le_rfl hspan (by omega)
  exact hlast

private theorem mem_takeWhile_pred {α : Type*} (pred : α → Bool) (xs : List α)
    {x : α} (hx : x ∈ xs.takeWhile pred) : pred x := by
  induction xs with
  | nil => simp at hx
  | cons head tail ih =>
      by_cases hpred : pred head
      · simp [List.takeWhile, hpred] at hx
        rcases hx with rfl | hx
        · exact hpred
        · exact ih hx
      · simp [List.takeWhile, hpred] at hx

private theorem collection_window_tail_no_later
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (w ell : ℕ) (hw : w < records.length) (hell : 1 ≤ ell) :
    ∀ r ∈ (ReferenceCollectionPhaseHistory.collectionWindow records w).drop ell,
      ReferenceCollectionPhaseHistory.laterChosen r.input = false := by
  have hdropLength : 0 < (records.drop w).length := by
    simp only [List.length_drop]
    omega
  obtain ⟨head, tail, hdrop⟩ := List.exists_cons_of_ne_nil
    (List.ne_nil_of_length_pos hdropLength)
  have htail : records.drop (w + 1) = tail := by
    rw [List.drop_add_one_eq_tail_drop, hdrop]
    rfl
  have hwindow : ReferenceCollectionPhaseHistory.collectionWindow records w =
      head :: tail.takeWhile (fun record =>
        !ReferenceCollectionPhaseHistory.laterChosen record.input) := by
    unfold ReferenceCollectionPhaseHistory.collectionWindow
    rw [hdrop, htail]
    simp
  intro r hr
  rw [hwindow] at hr
  have hmember : r ∈ (tail.takeWhile (fun record =>
      !ReferenceCollectionPhaseHistory.laterChosen record.input)).drop (ell - 1) := by
    cases ell with
    | zero => omega
    | succ n => simpa [List.drop] using hr
  have htake := mem_takeWhile_pred
    (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input)
    tail (List.mem_of_mem_drop hmember)
  simpa only [Bool.not_eq_true'] using htake

private theorem collection_window_prefix
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (w : ℕ) (hw : w < records.length) :
    ReferenceCollectionPhaseHistory.collectionWindow records w <+: records.drop w := by
  have hdropLength : 0 < (records.drop w).length := by
    simp only [List.length_drop]
    omega
  obtain ⟨head, tail, hdrop⟩ := List.exists_cons_of_ne_nil
    (List.ne_nil_of_length_pos hdropLength)
  have htail : records.drop (w + 1) = tail := by
    rw [List.drop_add_one_eq_tail_drop, hdrop]
    rfl
  have hwindow : ReferenceCollectionPhaseHistory.collectionWindow records w =
      head :: tail.takeWhile (fun record =>
        !ReferenceCollectionPhaseHistory.laterChosen record.input) := by
    unfold ReferenceCollectionPhaseHistory.collectionWindow
    rw [hdrop, htail]
    simp
  rw [hwindow, hdrop]
  exact List.cons_prefix_cons.mpr ⟨rfl, List.takeWhile_prefix _⟩

private theorem collection_step_phase
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate) (saved)
    (hc : x.state.coordinator = .collection payload ledger saved)
    (hno : ReferenceCollectionPhaseHistory.laterChosen x = false) :
    ReferenceCollectionPhaseHistory.CollectionPhase
      (ReferenceActivePhysicalStep.step x).next.coordinator := by
  change ReferenceCollectionPhaseHistory.CollectionPhase
    (ReferenceActivePhysicalStep.prepare x).observeCoordinator.configuration
  by_cases hvalid : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
  · let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
    let clock := ReferenceActivePhysicalStep.collectionClock payload ledger saved cutoff
    have hcut : (ReferenceActivePhysicalStep.prepare x).coordinator =
        .collection payload ledger clock cutoff
          (CoordinatorRoundDispatch.dispatchCollection
            (ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff)) := by
      simp only [ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch,
        hc, hvalid, cutoff, clock]
      rfl
    rw [ReferenceActivePhysicalStep.observeCoordinator_collection_equation
      (ReferenceActivePhysicalStep.prepare x) payload ledger clock cutoff _ hcut]
    split
    · exact Or.inl rfl
    · cases outcome : (CoordinatorRoundDispatch.dispatchCollection
          (ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff)) with
      | continuing core snapshot boundary scores =>
          exact ReferenceCollectionPhaseHistory.collectionPostChoice_no_installation
            (ReferenceActivePhysicalStep.prepare x) payload ledger snapshot.clockStarted
            (CoordinatorCollectionInteractive.PreObservationInputs.weights
              (ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff)
              snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq)
      | laterChosen core consistent started hstart instruction hi output hcons data installed selected =>
          simp [ReferenceCollectionPhaseHistory.laterChosen, hcut, outcome] at hno
      | _ => exact Or.inl rfl
  · have hcut : (ReferenceActivePhysicalStep.prepare x).coordinator =
        .invalidCollectionCutoff := by
      have hbad := ReferenceActivePhysicalStep.dispatch_collection_invalid_cutoff
        x payload ledger saved hc hvalid
      simp only [ReferenceActivePhysicalStep.prepare, hbad.1]
    simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator, hcut,
      ReferenceCollectionPhaseHistory.CollectionPhase,
      ReferenceActivePhysicalStep.coordinatorFailure]

private theorem connected_collection_phase
    {rate : ReferenceActivePhysicalStep.RateInput p}
    {initial final : ReferenceActivePhysicalStep.State p rate}
    {records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))}
    (chain : ReferenceActivePhysicalHorizon.Connected initial records final)
    (phase : ReferenceCollectionPhaseHistory.CollectionPhase initial.coordinator)
    (hno : ∀ r ∈ records, ReferenceCollectionPhaseHistory.laterChosen r.input = false) :
    ReferenceCollectionPhaseHistory.CollectionPhase final.coordinator := by
  induction records generalizing initial with
  | nil =>
      subst final
      exact phase
  | cons record rest ih =>
      obtain ⟨hpre, hrest⟩ := chain
      apply ih hrest
      · rw [record.output_eq]
        rcases phase with hd | ⟨payload, ledger, saved, hc⟩
        · exact Or.inl ((ReferenceActivePhysicalStep.step_coordinator_dagger
            record.input (hpre ▸ hd)).1)
        · exact collection_step_phase record.input payload ledger saved
            (hpre ▸ hc) (hno record (by simp))
      · intro r hr
        exact hno r (List.mem_cons_of_mem _ hr)

private theorem run_count_eq
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start left right : ℕ) (hl : start + left ≤ p.T) (hr : start + right ≤ p.T)
    (mode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (heq : left = right) :
    ReferenceActivePhysicalHorizon.run initial rows selected rewards start left hl mode =
      ReferenceActivePhysicalHorizon.run initial rows selected rewards start right hr mode := by
  subst right
  rfl

private theorem run_prefix_records_take
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start total : ℕ) (hspan : start + total ≤ p.T)
    (mode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (n : ℕ) (hn : n ≤ total) :
    (ReferenceActivePhysicalHorizon.run initial rows selected rewards start total
      hspan mode).records.take n =
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start n
        (by omega) mode).records := by
  obtain ⟨suffix, heq⟩ := ReferenceCollectionPhaseHistory.run_records_prefix
    initial rows selected rewards start n (total - n) (by omega) mode
  have hcount : n + (total - n) = total := Nat.add_sub_of_le hn
  have hrunEq := run_count_eq initial rows selected rewards start
    (n + (total - n)) total (by omega) hspan mode hcount
  rw [hrunEq] at heq
  rw [heq, List.take_append_of_le_length (by
    rw [ReferenceActivePhysicalHorizon.run_record_count])]
  simp [ReferenceActivePhysicalHorizon.run_record_count]

private theorem connected_endpoint_unique
    {rate : ReferenceActivePhysicalStep.RateInput p}
    {initial left right : ReferenceActivePhysicalStep.State p rate}
    {records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))}
    (hl : ReferenceActivePhysicalHorizon.Connected initial records left)
    (hr : ReferenceActivePhysicalHorizon.Connected initial records right) : left = right := by
  induction records generalizing initial left right with
  | nil =>
      change left = initial at hl
      change right = initial at hr
      exact hl.trans hr.symm
  | cons record rest ih =>
      simp only [ReferenceActivePhysicalHorizon.Connected] at hl hr
      exact ih hl.2 hr.2

/-- The first actual empty-pending stream ledger anchors the corresponding
physical prefix. The rest of the finite first collection window is the
literal contiguous suffix of that same run, including failed and dagger
records. -/
theorem actual_first_collection_empty_stream_suffix
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (count : ℕ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput
        source rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput
          source rewards C_star C_h rate)).completed + count ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count hspan).records).length < count)
    (d : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
      (rate := rate) source rewards C_star C_h count hcross hspan hshort) :
      let out := d.stream
      let s := ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput
            source rewards C_star C_h rate)).completed
      let I := ReferenceFirstCollectionEpochAlignment.actualLaunchState
        rate source rewards C_star C_h hcross
      let rows := source.1.2
      let J := ActualInitializationPhysicalStep.selectedRowIndex p source
      let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count hspan
      let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length
      let B := ReferenceCollectionPhaseHistory.collectionWindow E.records w
      let mode := (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
        rate source rewards C_star C_h hcross).1
      ∃ (hb : w + out.ell ≤ count) (hB : w + B.length ≤ count),
        let b := w + out.ell
        let P := ReferenceActivePhysicalHorizon.run I rows J rewards s b
          (by dsimp only [b]; omega) mode
        let modeP := ReferenceActivePhysicalHorizon.run_allActiveAtEnd
          I rows J rewards s b
          (by dsimp only [b]; omega) mode
        let S := ReferenceActivePhysicalHorizon.run P.finalState rows J rewards
          (s + b) (count - b)
          (by dsimp only [b]; omega) modeP
        P.finalState = d.record.output.next ∧
        P.finalState.coordinator = .collection out.payload d.ledger out.saved ∧
        E.records = P.records ++ S.records ∧
        E.finalState = S.finalState ∧
        B.drop out.ell = S.records.take (B.length - out.ell) ∧
        (out.ell < B.length -> d.ledger.pending = ∅) ∧
        ∀ (k : Fin B.length) (hkTail : out.ell ≤ k.val),
          let c := k.val - out.ell
          let Sk := ReferenceActivePhysicalHorizon.run P.finalState rows J rewards
            (s + b) c
            (by dsimp only [b, c]
                omega) modeP
          Sk.records = (B.drop out.ell).take c ∧
          Sk.finalState = B[k.val].input.state ∧
          ReferenceCollectionPhaseHistory.nextInput P.finalState rows J rewards
            (s + b) c
            (by dsimp only [b, c]
                omega) modeP = B[k.val].input ∧
          B[k.val].input.time.val = s + w + k.val ∧
          B[k.val].input.rows = rows ∧
          B[k.val].input.selected = J ∧
          B[k.val].input.rewards = rewards ∧
          ReferenceSourcePrefixHistoryFiltration.actualRecord
            rate rewards C_star C_h B[k.val].input.time source = some B[k.val] ∧
          ReferenceCollectionPhaseHistory.CollectionPhase
            B[k.val].input.state.coordinator ∧
          ∀ (cp : ReferenceActivePhysicalStep.Payload rate)
            (l : ReferenceActivePhysicalStep.Ledger rate)
            (saved : Option (Fin p.T × Bool)),
            B[k.val].input.state.coordinator = .collection cp l saved →
              l.pending = ∅ ∧ l.sigma = d.ledger.sigma := by
  classical
  dsimp only
  let out := d.stream
  let s := ReferenceInitializationRun.elapsed p
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
  let I := ReferenceFirstCollectionEpochAlignment.actualLaunchState
    rate source rewards C_star C_h hcross
  let rows := source.1.2
  let J := ActualInitializationPhysicalStep.selectedRowIndex p source
  let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
    rate source rewards C_star C_h hcross count hspan
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length
  let B := ReferenceCollectionPhaseHistory.collectionWindow E.records w
  let mode := (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
    rate source rewards C_star C_h hcross).1
  let b := w + out.ell

  have hEcount : E.records.length = count := by
    simpa [E, ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun] using
      (ReferenceActivePhysicalHorizon.run_record_count I rows J rewards s count hspan mode)
  have hwcount : w < count := by
    simpa [w, E, ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun] using hshort
  have hwlt : w < E.records.length := by
    rw [hEcount]
    exact hwcount
  have hBprefix : B <+: E.records.drop w := by
    simpa [B] using collection_window_prefix E.records w hwlt
  have hBbound : w + B.length ≤ count := by
    have hlen := hBprefix.length_le
    simp only [List.length_drop] at hlen
    rw [hEcount] at hlen
    omega
  have hwindowEq : out.window = B := by
    rw [out.windowIsActual]
    rfl
  have hellB : out.ell ≤ B.length := by
    rw [← hwindowEq]
    exact out.withinWindow
  have hb : w + out.ell ≤ count := by omega
  have hs : s + count ≤ p.T := by simpa [s] using hspan
  let P := ReferenceActivePhysicalHorizon.run I rows J rewards s b
    (by have hs' := hs; dsimp only [b]; omega) mode
  let modeP := ReferenceActivePhysicalHorizon.run_allActiveAtEnd
    I rows J rewards s b
    (by have hs' := hs; dsimp only [b]; omega) mode
  let S := ReferenceActivePhysicalHorizon.run P.finalState rows J rewards
    (s + b) (count - b)
    (by have hs' := hs; dsimp only [b]; omega) modeP
  have hrunSplit := actual_run_suffix_split I rows J rewards s b (count - b)
    (by have hs' := hs; dsimp only [b]; omega) mode
  have hsplitRecords : E.records = P.records ++ S.records := by
    simpa [E, P, S, b, modeP, ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun,
      Nat.add_sub_of_le hb] using hrunSplit.2
  have hsplitFinal : E.finalState = S.finalState := by
    simpa [E, P, S, b, modeP, ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun,
      Nat.add_sub_of_le hb] using hrunSplit.1
  have hPlength : P.records.length = b := by
    exact ReferenceActivePhysicalHorizon.run_record_count I rows J rewards s b
      (by have hs' := hs; dsimp only [b]; omega) mode

  have hrecordWindowIndex : d.last.val < out.window.length :=
    Nat.lt_of_lt_of_le d.last.isLt out.withinWindow
  have hrecordWindow : out.window[d.last.val] = d.record :=
    Option.some.inj ((List.getElem?_eq_getElem hrecordWindowIndex).symm.trans d.recordAt)
  have hlastStream : d.last.val + 1 = out.ell := by
    change d.last.val + 1 = d.stream.ell
    exact d.lastIsLast
  have hrecordGlobal : E.records[w + d.last.val]? = some d.record := by
    have ha := out.alignment ⟨d.last.val, hrecordWindowIndex⟩
    have ha' : E.records[w + d.last.val]? = some out.window[d.last.val] := by
      simpa [out, E, w, s, ReferenceFirstCollectionReadyStream.actualEpoch,
        ReferenceFirstCollectionReadyStream.startTime,
        ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun] using ha.1
    rw [hrecordWindow] at ha'
    exact ha'
  have hglobalIndex : w + d.last.val < count := by
    have h := (List.getElem?_eq_some_iff.mp hrecordGlobal).1
    rw [hEcount] at h
    exact h
  have hcanonicalLast : E.records[w + d.last.val]? =
      some (ReferenceAssignmentPayloadChronology.actualRunRecordAt I rows J rewards s
        (w + d.last.val) (by omega) mode) := by
    have hindexE : w + d.last.val < E.records.length := by
      rw [hEcount]
      exact hglobalIndex
    have hget := ReferenceLocalReleaseGateChronology.run_record_at I rows J rewards s mode
      count hspan ⟨w + d.last.val, hglobalIndex⟩
    have hget' : E.records[w + d.last.val] =
        ReferenceAssignmentPayloadChronology.actualRunRecordAt I rows J rewards s
          (w + d.last.val) (by omega) mode := by
      simpa [E, ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun] using hget
    exact (List.getElem?_eq_getElem hindexE).trans (congrArg some hget')
  have hcanonicalLastEq :
      ReferenceAssignmentPayloadChronology.actualRunRecordAt I rows J rewards s
        (w + d.last.val) (by omega) mode = d.record :=
    Option.some.inj (hcanonicalLast.symm.trans hrecordGlobal)
  have hbLast : w + d.last.val + 1 = b := by
    dsimp [b]
    omega
  have hPfinal : P.finalState = d.record.output.next := by
    have hsucc := ReferenceAssignmentPayloadChronology.run_successor_finalState_eq_actualRunRecordAt
      I rows J rewards s (w + d.last.val)
      (by have hs : s + count ≤ p.T := hspan; omega) mode
    have hsucc' : P.finalState =
        (ReferenceAssignmentPayloadChronology.actualRunRecordAt I rows J rewards s
          (w + d.last.val) (by have hs : s + count ≤ p.T := hspan; omega) mode).output.next := by
      simpa [P, b, hbLast] using hsucc
    have hnext := congrArg (fun record => record.output.next) hcanonicalLastEq
    exact hsucc'.trans hnext
  have hprefixCoordinator : P.finalState.coordinator =
      .collection out.payload d.ledger out.saved := by
    rw [hPfinal]
    exact d.actualNextCoordinator

  have hwindowBIndex : ∀ k : Fin B.length,
      E.records[w + k.val]? = some B[k.val] ∧
        B[k.val].input.time.val + 1 = s + w + 1 + k.val := by
    intro k
    have hk : k.val < out.window.length := by
      rw [hwindowEq]
      exact k.isLt
    have ha := out.alignment ⟨k.val, hk⟩
    simpa [out, hwindowEq, E, w, s,
      ReferenceFirstCollectionReadyStream.actualEpoch,
      ReferenceFirstCollectionReadyStream.startTime,
      ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun] using ha
  have hemptyLedger : out.ell < B.length → d.ledger.pending = ∅ := by
    intro hnotExhausted
    have hstreamShorter : out.ell < out.window.length := by
      rw [hwindowEq]
      exact hnotExhausted
    have hlastEmpty := out.last_empty_of_not_exhausted hstreamShorter
    have hlastIndex : d.last =
        ⟨d.stream.ell - 1, by have hp := d.stream.positiveLength; omega⟩ := by
      apply Fin.ext
      change d.last.val = d.stream.ell - 1
      have hlastNat : d.last.val + 1 = d.stream.ell := d.lastIsLast
      omega
    rw [d.ledgerIsLast, hlastIndex]
    simpa [out] using hlastEmpty

  have hBtake : B = (E.records.drop w).take B.length :=
    List.prefix_iff_eq_take.mp hBprefix
  have hEdropSuffix : E.records.drop (w + out.ell) = S.records := by
    have hindex : w + out.ell = P.records.length := by
      calc
        w + out.ell = b := rfl
        _ = P.records.length := hPlength.symm
    rw [hsplitRecords, hindex, List.drop_append_length]
  have hdropWindow : B.drop out.ell = S.records.take (B.length - out.ell) := by
    calc
      B.drop out.ell = ((E.records.drop w).take B.length).drop out.ell := by
        exact congrArg (fun records => records.drop out.ell) hBtake
      _ = ((E.records.drop w).drop out.ell).take (B.length - out.ell) := by
        rw [List.drop_take]
      _ = (E.records.drop (w + out.ell)).take (B.length - out.ell) := by
        rw [List.drop_drop]
      _ = S.records.take (B.length - out.ell) := by rw [hEdropSuffix]

  refine ⟨hb, hBbound, ?_⟩
  refine ⟨hPfinal, hprefixCoordinator, hsplitRecords, hsplitFinal, hdropWindow,
    hemptyLedger, ?_⟩
  intro k hkTail
  let c := k.val - out.ell
  have hkB : k.val < B.length := by
    exact k.isLt
  have hglobalK : w + k.val ≤ count := by
    have hk := hkB
    omega
  have hinputIndex : w + k.val < count := by
    have hk := hkB
    omega
  have hinputIndexE : w + k.val < E.records.length := by
    rw [hEcount]
    exact hinputIndex
  have hsum : b + c = w + k.val := by
    dsimp [b, c]
    omega
  have hbc : b + c ≤ count := by rw [hsum]; exact hglobalK
  have hSkSpan : s + b + c ≤ p.T := by
    have hs0 : s + count ≤ p.T := hs
    omega
  have hRunSpan : s + (b + c) ≤ p.T := by omega
  have hNextInputSpan : s + b + (c + 1) ≤ p.T := by
    calc
      s + b + (c + 1) = s + (b + c) + 1 := by omega
      _ = s + (w + k.val) + 1 := by rw [hsum]
      _ ≤ s + count := by omega
      _ ≤ p.T := hs
  let Sk := ReferenceActivePhysicalHorizon.run P.finalState rows J rewards
    (s + b) c hSkSpan modeP
  have hrunAtK := actual_run_suffix_split I rows J rewards s b c
    hRunSpan mode
  have hsplitAtKRecords :
      (ReferenceActivePhysicalHorizon.run I rows J rewards s (b + c)
        hRunSpan mode).records =
        P.records ++ Sk.records := by
    simpa [P, Sk, c, b, modeP] using hrunAtK.2
  have hprefixAtK :
      (ReferenceActivePhysicalHorizon.run I rows J rewards s (b + c)
        hRunSpan mode).records =
      E.records.take (b + c) := by
    have htake := run_prefix_records_take I rows J rewards s count hs mode
      (b + c) hbc
    simpa [E, ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun] using htake.symm
  have hrecordK : E.records[w + k.val] = B[k.val] := by
    exact Option.some.inj
      ((List.getElem?_eq_getElem hinputIndexE).symm.trans (hwindowBIndex k).1)
  have hconnectedE : ReferenceActivePhysicalHorizon.Connected I E.records E.finalState := by
    simpa [E, ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun] using
      ReferenceActivePhysicalHorizon.run_connected I rows J rewards s count hspan mode
  have hprefixChain := ReferenceFollowerReplyChronology.connected_take_to_input
      hconnectedE (w + k.val) hinputIndexE
  have hprefixChain' : ReferenceActivePhysicalHorizon.Connected I
      (E.records.take (w + k.val)) B[k.val].input.state := by
    rw [hrecordK] at hprefixChain
    exact hprefixChain
  have hrunKChain : ReferenceActivePhysicalHorizon.Connected I
      (ReferenceActivePhysicalHorizon.run I rows J rewards s (b + c)
        hRunSpan mode).records
      B[k.val].input.state := by
    rw [hprefixAtK, show b + c = w + k.val by dsimp [b, c]; omega]
    exact hprefixChain'
  have hrunKFinal :
      (ReferenceActivePhysicalHorizon.run I rows J rewards s (b + c)
        hRunSpan mode).finalState =
      B[k.val].input.state :=
    connected_endpoint_unique
      (ReferenceActivePhysicalHorizon.run_connected I rows J rewards s (b + c)
        hRunSpan mode)
      hrunKChain
  have hSkFinal : Sk.finalState = B[k.val].input.state := by
    have hfinal := hrunAtK.1
    simpa [Sk, c, b, modeP] using hfinal.symm.trans hrunKFinal
  have hPlengthAtK : P.records.length = b := hPlength
  have htakeAtK :
      (ReferenceActivePhysicalHorizon.run I rows J rewards s (b + c)
        hRunSpan mode).records =
        P.records ++ S.records.take c := by
    have hleftLength : P.records.length ≤ b + c := by rw [hPlengthAtK]; omega
    calc
      (ReferenceActivePhysicalHorizon.run I rows J rewards s (b + c)
        hRunSpan mode).records =
          E.records.take (b + c) := hprefixAtK
      _ = (P.records ++ S.records).take (b + c) := by rw [hsplitRecords]
      _ = P.records ++ S.records.take c := by
        rw [List.take_append]
        rw [List.take_of_length_le hleftLength]
        rw [hPlengthAtK]
        simp
  have hSkTake : Sk.records = S.records.take c := by
    have hconcat : P.records ++ S.records.take c = P.records ++ Sk.records := by
      calc
        P.records ++ S.records.take c =
            (ReferenceActivePhysicalHorizon.run I rows J rewards s (b + c)
              hRunSpan mode).records :=
          htakeAtK.symm
        _ = P.records ++ Sk.records := hsplitAtKRecords
    exact (List.append_cancel_left hconcat).symm
  have hSkRecords : Sk.records = (B.drop out.ell).take c := by
    have hlenTail : c ≤ B.length - out.ell := by dsimp [c]; omega
    simpa [hdropWindow, List.take_take, Nat.min_eq_left hlenTail] using hSkTake
  have hnoLater : ∀ r ∈ Sk.records,
      ReferenceCollectionPhaseHistory.laterChosen r.input = false := by
    intro r hr
    have hmem : r ∈ B.drop out.ell := by
      rw [hSkRecords] at hr
      exact List.mem_of_mem_take hr
    have hno := collection_window_tail_no_later E.records w out.ell hwlt
      (by have hp := out.positiveLength; omega) r hmem
    simpa [B] using hno

  have hinputs : B[k.val].input.rows = rows ∧
      B[k.val].input.selected = J ∧ B[k.val].input.rewards = rewards := by
    have hk : k.val < out.window.length := by rw [hwindowEq]; exact k.isLt
    simpa [out, hwindowEq, rows, J] using
      (out.originalInputs ⟨k.val, hk⟩)
  have htimeK : B[k.val].input.time.val = s + w + k.val := by
    have ht := (hwindowBIndex k).2
    omega
  have hnextInput : ReferenceCollectionPhaseHistory.nextInput P.finalState rows J rewards
      (s + b) c
      hNextInputSpan modeP = B[k.val].input := by
    change ReferenceActivePhysicalHorizon.roundInputAt P.finalState rows J rewards
      (s + b) modeP Sk ⟨s + b + c, by omega, by omega⟩ = B[k.val].input
    apply roundInput_eq_of_fields
    · exact hSkFinal
    · simpa [ReferenceActivePhysicalHorizon.roundInputAt] using hinputs.1.symm
    · simpa [ReferenceActivePhysicalHorizon.roundInputAt] using hinputs.2.1.symm
    · dsimp [ReferenceActivePhysicalHorizon.roundInputAt]
      calc
        s + b + c = s + (w + k.val) := by omega
        _ = B[k.val].input.time.val := by omega
    · simpa [ReferenceActivePhysicalHorizon.roundInputAt] using hinputs.2.2.symm

  have hphaseStart : ReferenceCollectionPhaseHistory.CollectionPhase P.finalState.coordinator := by
    rw [hprefixCoordinator]
    exact Or.inr ⟨out.payload, d.ledger, out.saved, rfl⟩
  have hphaseSk : ReferenceCollectionPhaseHistory.CollectionPhase Sk.finalState.coordinator :=
    connected_collection_phase Sk.connected hphaseStart hnoLater
  have hphaseK : ReferenceCollectionPhaseHistory.CollectionPhase
      B[k.val].input.state.coordinator := by
    rw [← hSkFinal]
    exact hphaseSk

  have hendpoint : ∀ (cp : ReferenceActivePhysicalStep.Payload rate)
      (l : ReferenceActivePhysicalStep.Ledger rate)
      (saved : Option (Fin p.T × Bool)),
      B[k.val].input.state.coordinator = .collection cp l saved →
        l.pending = ∅ ∧ l.sigma = d.ledger.sigma := by
    intro cp l saved hcollection
    have hcollectionSk : Sk.finalState.coordinator = .collection cp l saved := by
      rw [hSkFinal]
      exact hcollection
    have hnested := ReferenceCollectionPhaseHistory.run_collection_pending_nested_block
      P.finalState rows J rewards (s + b) c
      hSkSpan modeP out.payload d.ledger out.saved cp l saved
      hprefixCoordinator hcollectionSk hnoLater
    have hdEmpty := hemptyLedger (by omega)
    have hlEmpty : l.pending = ∅ := by
      apply (Finset.subset_empty.mp ?_)
      simpa [hdEmpty] using hnested.1
    exact ⟨hlEmpty, hnested.2⟩

  refine ⟨hSkRecords, hSkFinal, hnextInput, htimeK, hinputs.1, hinputs.2.1,
    hinputs.2.2, ?_, hphaseK, hendpoint⟩

  have hlaunchData := ReferenceCorrectedInitializationLaunch.correctedLaunch_all_active_at_start
    rate source rewards C_star C_h hcross
  obtain ⟨active, hlaunch, _hactive⟩ := hlaunchData
  have hactiveI : I = active := by
    dsimp [I, ReferenceFirstCollectionEpochAlignment.actualLaunchState]
    exact (Option.get_of_eq_some
      ((ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
        rate source rewards C_star C_h).2 hcross) hlaunch)
  have hlaunchI : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h = some I := by
    exact hlaunch.trans (congrArg some hactiveI.symm)
  have hphysicalStart : ReferenceCompletePhysicalHistory.physicalStart
      rate source rewards C_star C_h = s := by
    rfl
  have hsourceStart : ReferenceCompletePhysicalHistory.physicalStart
      rate source rewards C_star C_h ≤ B[k.val].input.time.val := by
    rw [hphysicalStart, htimeK]
    dsimp [s]
    omega
  have hsourceLookup := ReferenceSourcePrefixHistoryFiltration.actualRecord_on_launch
    rate rewards C_star C_h B[k.val].input.time source I hlaunchI hsourceStart
  have hrecordSpan : s + ((w + k.val) + 1) ≤ p.T := by
    have hs0 : s + count ≤ p.T := hs
    omega
  have hcanonicalK : ReferenceAssignmentPayloadChronology.actualRunRecordAt
      I rows J rewards s (w + k.val) hrecordSpan mode = B[k.val] := by
    have hrunOpt : E.records[w + k.val]? =
        some (ReferenceAssignmentPayloadChronology.actualRunRecordAt I rows J rewards s
          (w + k.val) hrecordSpan mode) := by
      have hidx : w + k.val < count := hinputIndex
      have hidxE : w + k.val < E.records.length := by
        rw [hEcount]
        exact hidx
      have hget := ReferenceLocalReleaseGateChronology.run_record_at I rows J rewards s mode
        count hspan ⟨w + k.val, hidx⟩
      have hget' : E.records[w + k.val] =
          ReferenceAssignmentPayloadChronology.actualRunRecordAt I rows J rewards s
            (w + k.val) hrecordSpan mode := by
        simpa [E, ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun] using hget
      exact (List.getElem?_eq_getElem hidxE).trans (congrArg some hget')
    exact Option.some.inj (hrunOpt.symm.trans (hwindowBIndex k).1)
  have hsourceLookup' : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h B[k.val].input.time source =
      some (ReferenceAssignmentPayloadChronology.actualRunRecordAt I rows J rewards s
        (w + k.val) hrecordSpan mode) := by
    have hindex : B[k.val].input.time.val -
        ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h =
        w + k.val := by
      rw [hphysicalStart, htimeK]
      dsimp [s]
      omega
    have hindexStart : B[k.val].input.time.val - s = w + k.val := by
      simpa [hphysicalStart] using hindex
    have hlaunchMode : ReferenceCompletePhysicalHistory.activeMode_of_launch_eq_some
        rate source rewards C_star C_h I hlaunchI = mode := by
      exact Subsingleton.elim _ _
    simpa [hphysicalStart, hindexStart, rows, J, hlaunchMode] using hsourceLookup
  rw [hsourceLookup', hcanonicalK]

end Bandits.Support.ReferenceFirstCollectionEmptyStreamSuffix
end
