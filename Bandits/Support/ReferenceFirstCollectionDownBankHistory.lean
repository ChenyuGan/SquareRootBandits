/-
Copyright (c) 2026 The Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionUnacceptedDownAwaitedPrefix

import Lean.Elab.Tactic.Omega

/-!
# Actual cutoff bank and strict-prefix DOWN replay

Sources: `sources/zip4/manuscript/06_interruptions.tex:163-174,476-480`,
`sources/zip4/manuscript/05_binary_transport.tex:27-53,100-124`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:92-109,139-157`.

The exported result is tied to the corrected initialization launch and its
canonical first-collection physical run.  Its initial bank is the actual
cutoff input bank, including every pending and completed entry.  A prefix is
replayed from that bank through the physical records retained by the actual
window; no reset or empty-bank premise is used.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions

namespace Bandits.Support.ReferenceFirstCollectionDownBankHistory

variable {p : Parameters}

private theorem connected_final_unique
    {rate : ReferenceActivePhysicalStep.RateInput p}
    {initial final₁ final₂ : ReferenceActivePhysicalHorizon.State p rate}
    {records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))}
    (h₁ : ReferenceActivePhysicalHorizon.Connected initial records final₁)
    (h₂ : ReferenceActivePhysicalHorizon.Connected initial records final₂) :
    final₁ = final₂ := by
  induction records generalizing initial final₁ final₂ with
  | nil =>
      simp only [ReferenceActivePhysicalHorizon.Connected] at h₁ h₂
      cases h₁
      cases h₂
      rfl
  | cons record rest ih =>
      simp only [ReferenceActivePhysicalHorizon.Connected] at h₁ h₂
      exact ih h₁.2 h₂.2

private theorem foldl_round_records_append
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start : ℕ)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (entries : List (ReferenceActivePhysicalHorizon.CalendarEntry p start))
    (acc : ReferenceActivePhysicalHorizon.Run initial) :
    ∃ suffix,
      (entries.foldl
        (ReferenceActivePhysicalHorizon.foldRound initial rows selected rewards start hmode)
        acc).records = acc.records ++ suffix := by
  induction entries generalizing acc with
  | nil => exact ⟨[], by simp⟩
  | cons entry rest ih =>
      let next := ReferenceActivePhysicalHorizon.foldRound initial rows selected rewards
        start hmode acc entry
      let input := ReferenceActivePhysicalHorizon.roundInputAt initial rows selected rewards
        start hmode acc entry
      obtain ⟨suffix, hsuffix⟩ := ih next
      have hrecords : next.records = acc.records ++
          [⟨input, ReferenceActivePhysicalStep.step input, rfl⟩] := by
        dsimp [next, input, ReferenceActivePhysicalHorizon.foldRound]
      refine ⟨[⟨input, ReferenceActivePhysicalStep.step input, rfl⟩] ++ suffix, ?_⟩
      simp only [List.foldl_cons]
      rw [hsuffix, hrecords]
      simp [List.append_assoc]

private theorem run_records_prefix
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start a b : ℕ) (hab : a ≤ b) (hspan : start + b ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start) :
    (ReferenceActivePhysicalHorizon.run initial rows selected rewards start a
      (by omega) hmode).records =
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start b
        hspan hmode).records.take a := by
  let short := ReferenceActivePhysicalHorizon.run initial rows selected rewards start a
    (by omega) hmode
  let whole := ReferenceActivePhysicalHorizon.run initial rows selected rewards start b
    hspan hmode
  have happend : whole = ReferenceActivePhysicalHorizon.foldCalendar initial rows selected
      rewards start (start + a) (b - a) (by omega) (by omega) hmode short := by
    have h := ReferenceActivePhysicalHorizon.run_append initial rows selected rewards
      start a (b - a) (by omega) hmode
    simpa [short, whole, Nat.add_sub_of_le hab] using h
  obtain ⟨suffix, hsuffix⟩ := foldl_round_records_append initial rows selected rewards
    start hmode
    (ReferenceActivePhysicalHorizon.calendarEntries start (start + a) (b - a)
      (by omega) (by omega)) short
  have hrecords : whole.records = short.records ++ suffix := by
    rw [happend]
    exact hsuffix
  have hlength := ReferenceActivePhysicalHorizon.run_record_count initial rows selected
    rewards start a (by omega) hmode
  rw [hrecords]
  simp [short, hlength]

private theorem collectionWindow_take_drop
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (w n : ℕ) (_hw : w < records.length)
    (hn : n ≤ (ReferenceCollectionPhaseHistory.collectionWindow records w).length) :
    (ReferenceCollectionPhaseHistory.collectionWindow records w).take n =
      (records.drop w).take n := by
  let tail := records.drop (w + 1)
  let selectedTail := tail.takeWhile
    (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input)
  let afterTail := tail.dropWhile
    (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input)
  have hsplit : records.drop w =
      (records.drop w).take 1 ++ tail := by
    simp [tail]
  have htail : tail = selectedTail ++ afterTail := by
    exact List.takeWhile_append_dropWhile.symm
  have hwindow : ReferenceCollectionPhaseHistory.collectionWindow records w ++ afterTail =
      records.drop w := by
    calc
      ReferenceCollectionPhaseHistory.collectionWindow records w ++ afterTail =
          (records.drop w).take 1 ++ (selectedTail ++ afterTail) := by
            simp [ReferenceCollectionPhaseHistory.collectionWindow, selectedTail, tail,
              List.append_assoc]
      _ = (records.drop w).take 1 ++ tail := by rw [← htail]
      _ = records.drop w := hsplit.symm
  have htake := congrArg (fun xs : List _ => xs.take n) hwindow
  simpa only [List.take_append, Nat.sub_eq_zero_of_le hn, List.take_zero,
    List.append_nil] using htake

private theorem collectionWindow_isPrefix
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (w : ℕ) :
    ∃ suffix,
      ReferenceCollectionPhaseHistory.collectionWindow records w ++ suffix = records.drop w := by
  let tail := records.drop (w + 1)
  let suffix := tail.dropWhile
    (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input)
  have htail : tail.takeWhile
      (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input) ++ suffix = tail := by
    dsimp [suffix]
    exact List.takeWhile_append_dropWhile
  have hsplit : records.drop w = (records.drop w).take 1 ++ tail := by
    simp [tail]
  refine ⟨suffix, ?_⟩
  calc
    ReferenceCollectionPhaseHistory.collectionWindow records w ++ suffix =
        (records.drop w).take 1 ++
          ((records.drop (w + 1)).takeWhile
            (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input) ++ suffix) := by
          simp [ReferenceCollectionPhaseHistory.collectionWindow, suffix, tail,
            List.append_assoc]
    _ = (records.drop w).take 1 ++ tail := by
          rw [htail]
    _ = records.drop w := hsplit.symm

private theorem collectionWindow_getElem_drop
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (w n : ℕ) (hw : w < records.length)
    (hn : n < (ReferenceCollectionPhaseHistory.collectionWindow records w).length) :
    (ReferenceCollectionPhaseHistory.collectionWindow records w)[n] =
      (records.drop w)[n]'(by
        obtain ⟨suffix, hsuffix⟩ := collectionWindow_isPrefix records w
        have hlen := congrArg List.length hsuffix
        simp only [List.length_append] at hlen
        have hdrop : (ReferenceCollectionPhaseHistory.collectionWindow records w).length ≤
            (records.drop w).length := by omega
        exact lt_of_lt_of_le hn hdrop) := by
  have hdropBound : n < (records.drop w).length := by
    obtain ⟨suffix, hsuffix⟩ := collectionWindow_isPrefix records w
    have hlen := congrArg List.length hsuffix
    simp only [List.length_append] at hlen
    omega
  have htake := collectionWindow_take_drop records w (n + 1) hw (by omega)
  have hopt : (ReferenceCollectionPhaseHistory.collectionWindow records w)[n]? =
      (records.drop w)[n]? := by
    have h := congrArg (fun xs : List _ => xs[n]?) htake
    have hleft :
        ((ReferenceCollectionPhaseHistory.collectionWindow records w).take (n + 1))[n]? =
          (ReferenceCollectionPhaseHistory.collectionWindow records w)[n]? :=
      List.getElem?_take_of_lt (by omega)
    have hright : ((records.drop w).take (n + 1))[n]? = (records.drop w)[n]? :=
      List.getElem?_take_of_lt (by omega)
    rw [hleft, hright] at h
    exact h
  have hleft := (List.getElem?_eq_some_iff.mpr ⟨hn, rfl⟩ :
    (ReferenceCollectionPhaseHistory.collectionWindow records w)[n]? =
      some (ReferenceCollectionPhaseHistory.collectionWindow records w)[n])
  have hright := (List.getElem?_eq_some_iff.mpr ⟨hdropBound, rfl⟩ :
    (records.drop w)[n]? = some (records.drop w)[n])
  rw [hleft, hright] at hopt
  exact Option.some.inj hopt

private theorem run_final_eq_input_at
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count j : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hj : j < count) :
    (ReferenceActivePhysicalHorizon.run initial rows selected rewards start j
      (by omega) hmode).finalState =
      ((ReferenceActivePhysicalHorizon.run initial rows selected rewards start count
        hspan hmode).records[j]'(by
          have hlen := ReferenceActivePhysicalHorizon.run_record_count initial rows selected
            rewards start count hspan hmode
          rw [hlen]
          exact hj)).input.state := by
  let Rprefix := ReferenceActivePhysicalHorizon.run initial rows selected rewards start j
    (by omega) hmode
  let Rwhole := ReferenceActivePhysicalHorizon.run initial rows selected rewards start count
    hspan hmode
  have hprefix := run_records_prefix initial rows selected rewards start j count
    (by omega) hspan hmode
  have hconnectedPrefix := ReferenceActivePhysicalHorizon.run_connected initial rows selected
    rewards start j (by omega) hmode
  have hconnectedWhole := ReferenceActivePhysicalHorizon.run_connected initial rows selected
    rewards start count hspan hmode
  have hconnectedInput := ReferenceFollowerReplyChronology.connected_take_to_input
    hconnectedWhole j (by
      have hlen := ReferenceActivePhysicalHorizon.run_record_count initial rows selected
        rewards start count hspan hmode
      rw [hlen]
      exact hj)
  have hstate := connected_final_unique hconnectedPrefix
      (by simpa [Rprefix, Rwhole, hprefix] using hconnectedInput)
  simpa [Rprefix, Rwhole] using hstate

private theorem actual_down_positive_samples
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (row : CompletePublicTable.CompleteRow p)
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (hrows : ∀ record ∈ records, record.input.row = row)
    (i : Fin (p.m - 1)) :
    ∀ entry ∈ ReferenceFollowerDownDecoderReplay.actualDownPositives i records,
      entry.sample = (row.2 entry.time).2 (0, i) := by
  classical
  intro entry hentry
  obtain ⟨call, hcall, hpositive⟩ := List.mem_flatMap.mp hentry
  obtain ⟨record, hrecord, hcall⟩ := List.mem_filterMap.mp hcall
  cases hchoice : ReferenceFollowerDownDecoderReplay.preparedChoiceConfiguration record i with
  | dagger =>
      simp only [ReferenceFollowerDownDecoderReplay.actualDownCall, hchoice] at hcall
      cases hcall
  | ordinary choice memory =>
      rw [ReferenceFollowerDownDecoderReplay.actualDownCall_ordinary
        record i choice memory hchoice] at hcall
      cases hcall
      have hrow : ReferenceFollowerDownDecoderReplay.preparedChoiceRow record i = row :=
        (record.output.preparation.follower_alignment i).1.trans (hrows record hrecord)
      unfold AffineBatchDecoder.positiveAt at hpositive
      split at hpositive
      · have hentryEq := List.mem_singleton.mp hpositive
        subst entry
        dsimp only [AffineBatchDecoder.entry,
          ActiveFollowerDownAcceptance.currentInputExtension,
          ActiveFollowerDownAcceptance.currentRoundInput]
        rw [hrow]
      · exact (List.not_mem_nil hpositive).elim

/-- Actual-source strict-prefix DOWN replay from the retained first-cutoff
bank.  The cutoff bank is selected once for each follower from the actual
ordinary chronology at the first record of the canonical collection window.
Every requested prefix starts from that same full bank, preserving all
completed and pending entries present at the cutoff. -/
theorem actual_cutoff_down_prefix_replay
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
    let start := ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
    let active := ReferenceFirstCollectionEpochAlignment.actualLaunchState
      rate source rewards C_star C_h hcross
    let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
      rate source rewards C_star C_h hcross count hspan
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length
    let B := ReferenceCollectionPhaseHistory.collectionWindow E.records w
    ∃ cut suffix,
      E.records = ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records ++ cut :: suffix ∧
      ∃ hBlen : 0 < B.length,
        B[0]'(by omega) = cut ∧
      ReferenceCollectionPhaseHistory.cutoffChosen cut.input = true ∧
      cut.input.time.val = start + w ∧
      cut.input.state = (ReferenceActivePhysicalHorizon.run active source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start w
        (by
          have hw : w < count := by simpa [w, E] using hshort
          omega) (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
          rate source rewards C_star C_h hcross).1).finalState ∧
      ReferenceFollowerDecoderChronology.downBatchSeed active start ∧
      ∀ (n : Fin B.length) (i : Fin (p.m - 1))
        (before : ReferencePrelaunchFollower.State p rate.eta)
        (memory : ActiveFollowerLifecycle.LocalMemory p),
          (B[n.val]'n.isLt).input.state.followers i = .ordinary before memory →
          ∃ cutoffState : ReferencePrelaunchFollower.State p rate.eta,
            ∃ cutoffMemory : ActiveFollowerLifecycle.LocalMemory p,
              cut.input.state.followers i = .ordinary cutoffState cutoffMemory ∧
              let W0 := cutoffState.downBatch
              let C := ReferenceFollowerDownDecoderReplay.actualDownCalls i (B.take n.val)
              let P := ReferenceFollowerDownDecoderReplay.actualDownPositives i (B.take n.val)
              before.downBatch = ReferenceFollowerDownDecoderReplay.foldDownCalls C W0 ∧
              AffineBatchDecoder.collected before.downBatch =
                AffineBatchDecoder.collected W0 ++ P ∧
              W0.pending.length < AffineBatchDecoder.quota p ∧
              (∀ entry ∈ W0.pending, entry.time.val < start + w) ∧
              (C.map Prod.fst).map Fin.val =
                ReferenceActivePhysicalHorizon.calendar (start + w) n.val ∧
              P.Pairwise (fun earlier later => earlier.time.val < later.time.val) ∧
              (∀ entry ∈ P, start + w ≤ entry.time.val ∧ entry.time.val < start + w + n.val) ∧
              (∀ entry ∈ P, entry.sample =
                ((source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).2
                  entry.time).2 (0, i)) ∧
              (∀ completed ∈ W0.completed,
                completed.length = AffineBatchDecoder.quota p) ∧
              (AffineBatchDecoder.collected W0).Pairwise
                (fun earlier later => earlier.time.val < later.time.val) ∧
              (∀ entry ∈ AffineBatchDecoder.collected W0, entry.time.val < start + w) ∧
              before.downBatch.completed =
                (ReferenceFollowerDownDecoderReplay.foldDownCalls C W0).completed := by
  classical
  let start := ReferenceInitializationRun.elapsed p
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
  let active := ReferenceFirstCollectionEpochAlignment.actualLaunchState
    rate source rewards C_star C_h hcross
  let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
    rate source rewards C_star C_h hcross count hspan
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length
  let B := ReferenceCollectionPhaseHistory.collectionWindow E.records w
  obtain ⟨cut, suffix, hsplit, htime, r, q, base, hcutState, _hlive,
    dispatched, hstart, ledger, hinit, hledger, hdomain, hclock, hpending,
    hnoAssignment, selected, hbranch, _hrest⟩ :=
      ReferenceFirstCollectionEpochAlignment.actual_first_collection_epoch_replay
        rate source rewards C_star C_h count hcross hspan hshort
  have hactualSeed := ReferenceCorrectedInitializationLaunch.correctedLaunch_downBatchSeed
    rate source rewards C_star C_h hcross
  obtain ⟨actual, hlaunch, hseed⟩ := hactualSeed
  have hactualLaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h = some active := by
    exact (Option.some_get ((ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
      rate source rewards C_star C_h).2 hcross)).symm
  have hactualEq : actual = active := Option.some.inj (hlaunch.symm.trans hactualLaunch)
  have hseedActive : ReferenceFollowerDecoderChronology.downBatchSeed active start := by
    rw [← hactualEq]
    simpa [start] using hseed
  have hmode := (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
    rate source rewards C_star C_h hcross).1
  have hcutState' : cut.input.state =
      (ReferenceActivePhysicalHorizon.run active source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start w
        (by
          have hwshort : w < count := by
            simpa [w, E] using hshort
          omega)
        hmode).finalState := by
    simpa [E, w, active, start,
      ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun] using hcutState
  have hElen : E.records.length = count := by
    dsimp [E, ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun]
    exact ReferenceActivePhysicalHorizon.run_record_count active source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start count hspan hmode
  have hw : w < E.records.length := by
    rw [hElen]
    simpa [w, E] using hshort
  have hdropCut : E.records.drop w = cut :: suffix := by
    rw [hsplit]
    rw [List.drop_append_length]
  have hBlen : 0 < B.length := by
    simp [B, ReferenceCollectionPhaseHistory.collectionWindow, hdropCut]
  have hB0 : B[0]'(by omega) = cut := by
    have hget := collectionWindow_getElem_drop E.records w 0 hw (by
      simpa [B] using hBlen)
    simpa [B, hdropCut] using hget
  have hcutIndex : E.records[w]'(by omega) = cut := by
    have hhead : (E.records.drop w)[0]'(by simp [hdropCut]) = cut := by
      simp [hdropCut]
    simpa only [List.getElem_drop, Nat.add_zero] using hhead
  have hchosen : ReferenceCollectionPhaseHistory.cutoffChosen cut.input = true := by
    have hprep : (ReferenceActivePhysicalStep.prepare cut.input).coordinator =
        .live r q base (.cutoffChosen dispatched hstart ledger hinit hledger hdomain hclock
          hpending hnoAssignment selected) := by
      have h := hbranch
      rw [cut.output_eq] at h
      simpa [ReferenceActivePhysicalStep.step] using h
    simp [ReferenceCollectionPhaseHistory.cutoffChosen, hprep]
  have hblenDrop : B.length ≤ (E.records.drop w).length := by
    obtain ⟨tail, hprefix⟩ := collectionWindow_isPrefix E.records w
    have hlen := congrArg List.length hprefix
    have hlen' : B.length + tail.length = (E.records.drop w).length := by
      simpa only [List.length_append] using hlen
    clear hlen
    have hlen := hlen'
    omega
  have hwindowTake (n : ℕ) (hn : n ≤ B.length) :
      B.take n = (E.records.drop w).take n := by
    exact collectionWindow_take_drop E.records w n hw (by simpa [B] using hn)
  have hboundaryOrd (i : Fin (p.m - 1)) (before : ReferencePrelaunchFollower.State p rate.eta)
      (memory : ActiveFollowerLifecycle.LocalMemory p) (n : Fin B.length)
      (hfi : (B[n.val]'n.isLt).input.state.followers i = .ordinary before memory) :
      ∃ cutoffState : ReferencePrelaunchFollower.State p rate.eta,
        ∃ cutoffMemory : ActiveFollowerLifecycle.LocalMemory p,
          cut.input.state.followers i = .ordinary cutoffState cutoffMemory := by
    have hvalid : w + n.val < E.records.length := by
      have hlen := List.length_drop (l := E.records) (i := w)
      rw [hElen] at hlen
      have hdrop : n.val < (E.records.drop w).length := lt_of_lt_of_le n.isLt hblenDrop
      omega
    have hget : B[n.val]'n.isLt = E.records[w + n.val]'hvalid := by
      calc
        B[n.val]'n.isLt = (E.records.drop w)[n.val]'(by
            exact lt_of_lt_of_le n.isLt hblenDrop) := by
              simpa [B] using collectionWindow_getElem_drop E.records w n.val hw n.isLt
        _ = E.records[w + n.val] := by simp only [List.getElem_drop]
    have hconnectedStart := ReferenceFollowerReplyChronology.connected_drop_from_input
      E.connected w hw
    have hnDrop : n.val < (E.records.drop w).length := lt_of_lt_of_le n.isLt hblenDrop
    have hconnectedN := ReferenceFollowerReplyChronology.connected_take_to_input
      hconnectedStart n.val hnDrop
    have hfiRecord : (E.records[w + n.val]'hvalid).input.state.followers i =
        .ordinary before memory := by
      simpa [hget] using hfi
    have hfiDrop : (E.records.drop w)[n.val].input.state.followers i =
        .ordinary before memory := by
      simpa only [List.getElem_drop] using hfiRecord
    obtain ⟨cutoffState, cutoffMemory, hcutoffOrd, _, _, _⟩ :=
      ReferenceFollowerReplyChronology.connected_ordinary_chronology hconnectedN i
        before memory hfiDrop
    refine ⟨cutoffState, cutoffMemory, ?_⟩
    rw [← hcutIndex]
    exact hcutoffOrd
  refine ⟨cut, suffix, hsplit, ⟨hBlen, hB0, hchosen, htime, hcutState', hseedActive, ?_⟩⟩
  · intro n i before memory hfi
    obtain ⟨cutoffState, cutoffMemory, hcutoffOrd⟩ := hboundaryOrd i before memory n hfi
    refine ⟨cutoffState, cutoffMemory, hcutoffOrd, ?_⟩
    let b := w + n.val
    have hnDrop : n.val < (E.records.drop w).length := lt_of_lt_of_le n.isLt hblenDrop
    have hbLe : b ≤ count := by
      have hlen := List.length_drop (l := E.records) (i := w)
      rw [hElen] at hlen
      omega
    have hspanB : start + b ≤ p.T := by dsimp [b]; omega
    have hrunRecords :
        (ReferenceActivePhysicalHorizon.run active source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start b hspanB hmode).records =
          E.records.take b := by
      dsimp [E, ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun]
      exact run_records_prefix active source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start b count
        (by dsimp [b]; omega) hspan hmode
    have hrunDrop :
        (ReferenceActivePhysicalHorizon.run active source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start b hspanB hmode).records.drop w =
          (E.records.drop w).take n.val := by
      rw [hrunRecords]
      simp [b, Nat.add_comm, List.drop_take]
    have hwindowPrefix := hwindowTake n.val (Nat.le_of_lt n.isLt)
    have hactualInterval : B.take n.val =
        (ReferenceActivePhysicalHorizon.run active source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start b hspanB hmode).records.drop w := by
      rw [hwindowPrefix, hrunDrop]
    have hvalid : w + n.val < E.records.length := by
      have hlen := List.length_drop (l := E.records) (i := w)
      rw [hElen] at hlen
      omega
    have hrecordIndex : B[n.val]'n.isLt = E.records[w + n.val]'hvalid := by
      simpa [b] using (collectionWindow_getElem_drop E.records w n.val hw n.isLt).trans
        (by simp only [List.getElem_drop])
    have hrunFinal := run_final_eq_input_at active source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start count
      (w + n.val) hspan hmode (lt_of_lt_of_eq hvalid hElen)
    have hordinaryB :
        (ReferenceActivePhysicalHorizon.run active source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start b hspanB hmode).finalState.followers i =
          .ordinary before memory := by
      have hcurrent := hfi
      rw [hrecordIndex] at hcurrent
      have hcurrentFull := hcurrent
      change
          ((ReferenceActivePhysicalHorizon.run active source.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start count hspan hmode).records[
              w + n.val]'hvalid).input.state.followers i = .ordinary before memory at hcurrentFull
      have hfinalFollower := congrArg (fun state => state.followers i) hrunFinal
      calc
        (ReferenceActivePhysicalHorizon.run active source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start b hspanB hmode).finalState.followers i =
            (ReferenceActivePhysicalHorizon.run active source.1.2
              (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start (w + n.val)
              (by omega) hmode).finalState.followers i := by simp [b]
        _ = .ordinary before memory := by rw [hfinalFollower]; exact hcurrentFull
    obtain ⟨stateA, memoryA, hstateA, hfacts⟩ :=
      ReferenceFollowerDownIntervalWindow.run_interval_downBatch_replay
        p rate active source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
        rewards start w b (by dsimp [b]; omega) hspanB hmode hseedActive i before memory hordinaryB
    have hcutBoundary :
        (ReferenceActivePhysicalHorizon.run active source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start w
          (by omega) hmode).finalState.followers i =
          .ordinary cutoffState cutoffMemory := by
      rw [← hcutState']
      exact hcutoffOrd
    have hstateEq : stateA.downBatch = cutoffState.downBatch := by
      have hstates := hstateA.symm.trans hcutBoundary
      cases hstates
      rfl
    have hprefixSpec := ReferenceFollowerDecoderChronology.run_downBatch_spec
      active source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
      start w (by omega) hmode hseedActive i cutoffState cutoffMemory hcutBoundary
    have hwell := hprefixSpec.1.1
    have hcollectedTime := hprefixSpec.1.2.2
    rcases hfacts with ⟨_hrecords, hcallPair, hcallDates, hbank, hcollected,
      _hpending, _hpendingTime, hpositivePair, hpositiveTime⟩
    let C := ReferenceFollowerDownDecoderReplay.actualDownCalls i (B.take n.val)
    let P := ReferenceFollowerDownDecoderReplay.actualDownPositives i (B.take n.val)
    have hcallEq : C = ReferenceFollowerDownDecoderReplay.actualDownCalls i
        ((ReferenceActivePhysicalHorizon.run active source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start b hspanB hmode).records.drop w) := by
      dsimp [C]
      rw [hactualInterval]
    have hpositiveEq : P = ReferenceFollowerDownDecoderReplay.actualDownPositives i
        ((ReferenceActivePhysicalHorizon.run active source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start b hspanB hmode).records.drop w) := by
      dsimp [P, ReferenceFollowerDownDecoderReplay.actualDownPositives]
      rw [hactualInterval]
    have hbank' : before.downBatch = ReferenceFollowerDownDecoderReplay.foldDownCalls C cutoffState.downBatch := by
      rw [hcallEq]
      simpa [hstateEq] using hbank
    have hcollected' : AffineBatchDecoder.collected before.downBatch =
        AffineBatchDecoder.collected cutoffState.downBatch ++ P := by
      simpa [P, hpositiveEq, hstateEq] using hcollected
    have hcallDates' : (C.map Prod.fst).map Fin.val =
        ReferenceActivePhysicalHorizon.calendar (start + w) n.val := by
      rw [hcallEq]
      simpa [b, Nat.add_sub_cancel_left] using hcallDates
    have hpositivePair' : P.Pairwise
        (fun earlier later => earlier.time.val < later.time.val) := by
      simpa [P, hpositiveEq] using hpositivePair
    have hpositiveTime' : ∀ entry ∈ P,
        start + w ≤ entry.time.val ∧ entry.time.val < start + w + n.val := by
      intro entry hentry
      have h := hpositiveTime entry (by simpa [P, hpositiveEq] using hentry)
      simpa [b, Nat.add_assoc] using h
    have hpendingSize : cutoffState.downBatch.pending.length < AffineBatchDecoder.quota p :=
      hwell.1
    have hpendingTime : ∀ entry ∈ cutoffState.downBatch.pending,
        entry.time.val < start + w := by
      intro entry hentry
      apply hcollectedTime entry
      simp [AffineBatchDecoder.collected, hentry]
    have hrows : ∀ record ∈ B.take n.val,
        record.input.row = source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) := by
      intro record hrecord
      have hmemDrop : record ∈ E.records.drop w := by
        rw [hwindowPrefix] at hrecord
        exact List.mem_of_mem_take hrecord
      have hmem : record ∈ E.records := List.mem_of_mem_drop hmemDrop
      have hinputs := ReferenceActivePhysicalHorizon.run_record_inputs active source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start count
        hspan hmode record hmem
      simp only [ReferenceActivePhysicalStep.RoundInput.row, hinputs.1, hinputs.2.1]
    have hsamples := actual_down_positive_samples
      (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source))
      (B.take n.val) hrows i
    refine ⟨hbank', hcollected', hpendingSize, hpendingTime, hcallDates',
      hpositivePair', hpositiveTime', hsamples, hwell.2, hprefixSpec.1.2.1,
      hcollectedTime, ?_⟩
    exact congrArg AffineBatchDecoder.State.completed hbank'


/-- The actual record frame for a retained executed DOWN diagnostic. The
logged bank is the state entering this record, and its decoder result is the
literal current-input update. -/
private theorem retained_down_record_decoder_update
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1))
    (before : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hinput : record.input.state.followers i = .ordinary before memory)
    (diagnostic : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (hdown : (record.output.followers i).down = some diagnostic)
    (hcompared : diagnostic.rawComparison ≠ none)
    (bound : ℕ)
    (hbefore : ReferenceFollowerDecoderChronology.downBatchEndpoint before bound)
    (hoccupied : before.status ≠ .unoccupied → before.downBatch.pending = []) :
    ∃ choice : ReferencePrelaunchFollower.State p rate.eta,
      ∃ choiceMemory : ActiveFollowerLifecycle.LocalMemory p,
      ∃ logged : ReferencePrelaunchFollower.State p rate.eta,
        let prep := record.output.preparation.followers.followers i
        let observation := record.output.preparation.feedback.observations
          (PublicDiscreteDraws.followerPlayer p.two_le_m i)
        let own := (prep.arm, observation)
        let input := ActiveFollowerDownAcceptance.currentRoundInput p prep.follower prep.row
          prep.time observation rate logged
        let decoded := ActiveFollowerDownAcceptance.currentDecodeStep p prep.follower prep.row
          prep.time observation rate logged
        let trace := ActiveFollowerDownAcceptance.currentInputExtension p input
        prep.follower = i ∧
        prep.configuration = .ordinary choice choiceMemory ∧
        choice.status = .unoccupied ∧ logged.status = .unoccupied ∧
        (record.output.followers i).downInput = some logged ∧
        logged.downBatch = before.downBatch ∧
        diagnostic = ReferenceDownReception.referenceDownCut p
          record.output.preparation.coordinator.downView prep.follower prep.row prep.time
          observation rate logged ∧
        input.sample = (prep.row.2 prep.time).2 (0, prep.follower) ∧
        diagnostic.raw = decoded.2 ∧
        decoded = ReferencePrelaunchFollower.decodeAt prep.follower prep.row prep.activation
          prep.time own logged.downBatch ∧
        AffineBatchDecoder.collected decoded.1 =
          AffineBatchDecoder.collected logged.downBatch ++
            AffineBatchDecoder.positiveAt p trace prep.time ∧
        (0 < observation.val.val →
          AffineBatchDecoder.collected decoded.1 = AffineBatchDecoder.collected logged.downBatch ++
            [AffineBatchDecoder.entry p trace prep.time]) ∧
        (observation.val.val = 0 → decoded = (logged.downBatch, none) ∧ diagnostic.raw = none) ∧
        (0 < observation.val.val → logged.downBatch.pending.length + 1 <
          AffineBatchDecoder.quota p →
          decoded = (⟨logged.downBatch.pending ++
            [AffineBatchDecoder.entry p trace prep.time], logged.downBatch.completed⟩, none) ∧
          diagnostic.raw = none) ∧
        (0 < observation.val.val → logged.downBatch.pending.length + 1 =
          AffineBatchDecoder.quota p →
          decoded =
            (⟨[], logged.downBatch.completed ++ [logged.downBatch.pending ++
              [AffineBatchDecoder.entry p
                (ReferencePrelaunchFollower.traceAt prep.follower prep.row prep.activation
                  prep.time own) prep.time]]⟩,
             AffineBatchDecoder.batchOutput (logged.downBatch.pending ++
              [AffineBatchDecoder.entry p
                (ReferencePrelaunchFollower.traceAt prep.follower prep.row prep.activation
                  prep.time own) prep.time])) ∧
          (diagnostic.raw = none ↔ AffineBatchDecoder.batchOutput
            (logged.downBatch.pending ++ [AffineBatchDecoder.entry p
              (ReferencePrelaunchFollower.traceAt prep.follower prep.row prep.activation
                prep.time own) prep.time]) = none)) := by
  classical
  let prep := record.output.preparation.followers.followers i
  let observation := record.output.preparation.feedback.observations
    (PublicDiscreteDraws.followerPlayer p.two_le_m i)
  let own := (prep.arm, observation)
  obtain ⟨choice, choiceMemory, logged, hprepared, hchoiceStatus, hlogging,
      hdownInput, hcutEq⟩ :=
    ReferenceFollowerSparseEmissionRecovery.actualDownDiagnostic_choice record i diagnostic hdown
  have hprepIndex : prep.follower = i :=
    record.output.preparation.follower_alignment i |>.2.1
  have hloggingFrame := ActiveFollowerLogging.checkedLogging_success_frame
    prep.follower prep.row prep.activation prep.time own choice logged hlogging
  rcases hloggingFrame with ⟨_, _, _, _, hloggedStatus, hloggedBank, _⟩
  have hloggedUnoccupied : logged.status = .unoccupied := hloggedStatus.trans hchoiceStatus
  have hprepareFrame := ReferenceFollowerDecoderChronology.run_interruption_downBatch_frame
    record i before choice memory choiceMemory hinput hprepared hoccupied
  have hbankLogged : logged.downBatch = before.downBatch := hloggedBank.trans hprepareFrame.1
  have hcomparedCut :
      (ReferenceDownReception.referenceDownCut p record.output.preparation.coordinator.downView
        prep.follower prep.row prep.time observation rate logged).rawComparison ≠ none := by
    simpa [hcutEq] using hcompared
  have hselected : ActiveFollowerDownAcceptance.downSelected p prep.follower prep.row prep.time := by
    by_contra hnot
    unfold ReferenceDownReception.referenceDownCut at hcomparedCut
    simp [hnot] at hcomparedCut
  have hdownInputEq :
      ActiveFollowerDownAcceptance.currentRoundInput p prep.follower prep.row prep.time
        observation rate logged =
      ReferencePrelaunchFollower.downInput prep.follower prep.row prep.activation prep.time own := by
    let selected : Prop :=
      PublicDiscreteDraws.slotDraw (prep.row.2 prep.time).1 = PublicDiscreteDraws.downSlot ∧
        PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
          (prep.row.2 prep.time).1 = prep.follower
    have hselectedBool : decide selected =
        decide (prep.activation.val ≤ prep.time.val + 1 ∧ selected) := by
      by_cases hs : selected <;> simp [hs, prep.active]
    simp only [ActiveFollowerDownAcceptance.currentRoundInput,
      ReferencePrelaunchFollower.downInput, hloggedUnoccupied]
    rw [hselectedBool]
    rfl
  have htraceCurrent :
      (ActiveFollowerDownAcceptance.currentInputExtension p
        (ActiveFollowerDownAcceptance.currentRoundInput p prep.follower prep.row prep.time
          observation rate logged)) prep.time =
      (ReferencePrelaunchFollower.traceAt prep.follower prep.row prep.activation prep.time own)
        prep.time := by
    simpa [ActiveFollowerDownAcceptance.currentInputExtension,
      ReferencePrelaunchFollower.traceAt] using hdownInputEq
  have hdecodeSame := ActiveFollowerDownAcceptance.decodeStep_depends_on_current_input p
    (ActiveFollowerDownAcceptance.currentInputExtension p
      (ActiveFollowerDownAcceptance.currentRoundInput p prep.follower prep.row prep.time
        observation rate logged))
    (ReferencePrelaunchFollower.traceAt prep.follower prep.row prep.activation prep.time own)
    logged.downBatch prep.time htraceCurrent
  have hdownSelected :
      (ReferencePrelaunchFollower.downInput prep.follower prep.row prep.activation prep.time own).selected = true := by
    change decide (prep.activation.val ≤ prep.time.val + 1 ∧
      PublicDiscreteDraws.slotDraw (prep.row.2 prep.time).1 = PublicDiscreteDraws.downSlot ∧
      PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
        (prep.row.2 prep.time).1 = prep.follower) = true
    rw [decide_eq_true_eq]
    exact ⟨prep.active, hselected.1, hselected.2⟩
  have hdecodeAt :
      ActiveFollowerDownAcceptance.currentDecodeStep p prep.follower prep.row prep.time
        observation rate logged =
      ReferencePrelaunchFollower.decodeAt prep.follower prep.row prep.activation prep.time own
        logged.downBatch := by
    unfold ActiveFollowerDownAcceptance.currentDecodeStep
    rw [hdecodeSame]
    simp [ReferencePrelaunchFollower.decodeAt, hdownSelected]
  have hraw : diagnostic.raw =
      (ActiveFollowerDownAcceptance.currentDecodeStep p prep.follower prep.row prep.time
        observation rate logged).2 := by
    rw [hcutEq]
    exact ReferenceDownReception.referenceDownCut_raw_eq_currentDecodeStep_of_compared
      record.output.preparation.coordinator.downView prep.follower prep.row prep.time observation
      rate logged hcomparedCut
  have hbankWell : ReferenceFollowerDecoderChronology.downBatchWellFormed logged.downBatch := by
    rw [hbankLogged]
    exact hbefore.1
  have hbatchSpec := ReferenceFollowerDecoderChronology.currentDecodeStep_batch_spec
    prep.follower prep.row prep.time observation logged hbankWell
  have heligible : AffineBatchDecoder.eligible
      (ActiveFollowerDownAcceptance.currentRoundInput p prep.follower prep.row prep.time
        observation rate logged) ↔
      ActiveFollowerDownAcceptance.downSelected p prep.follower prep.row prep.time ∧
        logged.status = .unoccupied ∧ 0 < observation.val.val :=
    ActiveFollowerDownAcceptance.currentRoundInput_eligible_iff p prep.follower prep.row
      prep.time observation rate logged
  have hpositiveAt (hpositive : 0 < observation.val.val) :
      AffineBatchDecoder.positiveAt p
        (ActiveFollowerDownAcceptance.currentInputExtension p
          (ActiveFollowerDownAcceptance.currentRoundInput p prep.follower prep.row prep.time
            observation rate logged)) prep.time =
        [AffineBatchDecoder.entry p
          (ActiveFollowerDownAcceptance.currentInputExtension p
            (ActiveFollowerDownAcceptance.currentRoundInput p prep.follower prep.row prep.time
              observation rate logged)) prep.time] := by
    have hpos : AffineBatchDecoder.eligible
        (ActiveFollowerDownAcceptance.currentRoundInput p prep.follower prep.row prep.time
          observation rate logged) := heligible.mpr ⟨hselected, hloggedUnoccupied, hpositive⟩
    simp [ActiveFollowerDownAcceptance.currentInputExtension,
      AffineBatchDecoder.positiveAt, hpos]
  have hzeroUpdate (hzero : observation.val.val = 0) :
      ActiveFollowerDownAcceptance.currentDecodeStep p prep.follower prep.row prep.time
        observation rate logged = (logged.downBatch, none) := by
    have hnot : ¬ AffineBatchDecoder.eligible
        (ActiveFollowerDownAcceptance.currentRoundInput p prep.follower prep.row prep.time
          observation rate logged) := by
      rw [heligible]
      rintro ⟨_, _, hpositive⟩
      rw [hzero] at hpositive
      exact (lt_irrefl 0) hpositive
    have hnotTrace : ¬ AffineBatchDecoder.eligible
        ((ActiveFollowerDownAcceptance.currentInputExtension p
          (ActiveFollowerDownAcceptance.currentRoundInput p prep.follower prep.row prep.time
            observation rate logged)) prep.time) := by
      simpa [ActiveFollowerDownAcceptance.currentInputExtension] using hnot
    exact AffineBatchDecoder.decodeStep_ineligible p
      (ActiveFollowerDownAcceptance.currentInputExtension p
        (ActiveFollowerDownAcceptance.currentRoundInput p prep.follower prep.row prep.time
          observation rate logged)) logged.downBatch prep.time hbankWell.1 hnotTrace
  have hpartial (hpositive : 0 < observation.val.val)
      (hsmall : logged.downBatch.pending.length + 1 < AffineBatchDecoder.quota p) :
      ActiveFollowerDownAcceptance.currentDecodeStep p prep.follower prep.row prep.time
        observation rate logged =
        (⟨logged.downBatch.pending ++ [AffineBatchDecoder.entry p
          (ActiveFollowerDownAcceptance.currentInputExtension p
            (ActiveFollowerDownAcceptance.currentRoundInput p prep.follower prep.row prep.time
              observation rate logged)) prep.time], logged.downBatch.completed⟩, none) := by
    simp only [ActiveFollowerDownAcceptance.currentDecodeStep,
      AffineBatchDecoder.decodeStep, AffineBatchDecoder.step, AffineBatchDecoder.stepOutput,
      hpositiveAt hpositive, List.length_append, List.length_singleton, hsmall, ite_true]
  have hcomplete (hpositive : 0 < observation.val.val)
      (hquota : logged.downBatch.pending.length + 1 = AffineBatchDecoder.quota p) :
      ActiveFollowerDownAcceptance.currentDecodeStep p prep.follower prep.row prep.time
        observation rate logged =
        (⟨[], logged.downBatch.completed ++ [logged.downBatch.pending ++
          [AffineBatchDecoder.entry p
            (ReferencePrelaunchFollower.traceAt prep.follower prep.row prep.activation prep.time own)
            prep.time]]⟩,
         AffineBatchDecoder.batchOutput (logged.downBatch.pending ++
          [AffineBatchDecoder.entry p
            (ReferencePrelaunchFollower.traceAt prep.follower prep.row prep.activation prep.time own)
            prep.time])) := by
    have hinputEligible := heligible.mpr ⟨hselected, hloggedUnoccupied, hpositive⟩
    have htraceEligible : AffineBatchDecoder.eligible
        (ReferencePrelaunchFollower.traceAt prep.follower prep.row prep.activation prep.time own
          prep.time) := by
      rw [← htraceCurrent]
      exact hinputEligible
    have hdecodeComplete := ReferencePrelaunchFollower.decodeAt_complete prep.follower prep.row
      prep.activation prep.time own logged.downBatch htraceEligible hquota
    simpa [hdecodeAt] using hdecodeComplete
  let input := ActiveFollowerDownAcceptance.currentRoundInput p prep.follower prep.row prep.time
    observation rate logged
  let decoded := ActiveFollowerDownAcceptance.currentDecodeStep p prep.follower prep.row prep.time
    observation rate logged
  let trace := ActiveFollowerDownAcceptance.currentInputExtension p input
  have hsample : input.sample = (prep.row.2 prep.time).2 (0, prep.follower) := by
    rfl
  refine ⟨choice, choiceMemory, logged, ?_⟩
  dsimp only
  refine ⟨hprepIndex, hprepared, hchoiceStatus, hloggedUnoccupied, hdownInput,
    hbankLogged, hcutEq, hsample, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [decoded] using hraw
  · simpa [decoded] using hdecodeAt
  · simpa [decoded, trace, input] using hbatchSpec.2
  · intro hpositive
    simpa [decoded, hpositiveAt hpositive] using hbatchSpec.2
  · intro hzero
    refine ⟨?_, ?_⟩
    · simpa [decoded] using hzeroUpdate hzero
    · simpa [decoded] using hraw.trans (congrArg Prod.snd (hzeroUpdate hzero))
  · intro hpositive hsmall
    refine ⟨hpartial hpositive hsmall, ?_⟩
    exact hraw.trans (congrArg Prod.snd (hpartial hpositive hsmall))
  · intro hpositive hquota
    refine ⟨hcomplete hpositive hquota, ?_⟩
    have hrawComplete := hraw.trans (congrArg Prod.snd (hcomplete hpositive hquota))
    constructor
    · intro hnone
      rw [hrawComplete] at hnone
      exact hnone
    · intro hnone
      rw [hrawComplete]
      exact hnone

/-- The canonical source-level boundary context for a retained, executed DOWN
diagnostic in the first collection window.  It supplies the cutoff replay,
actual row and time, and public endpoint facts needed by
`retained_down_record_decoder_update`; the conditional diagnostic conclusion
therefore stays tied to this actual record and source row. -/
theorem actual_cutoff_retained_down_diagnostic
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
    let start := ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
    let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
      rate source rewards C_star C_h hcross count hspan
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length
    let B := ReferenceCollectionPhaseHistory.collectionWindow E.records w
    ∀ (n : Fin B.length) (i : Fin (p.m - 1))
      (before : ReferencePrelaunchFollower.State p rate.eta)
      (memory : ActiveFollowerLifecycle.LocalMemory p),
      (B[n.val]'n.isLt).input.state.followers i = .ordinary before memory →
      ∃ hBlen : 0 < B.length,
        ∃ cutoffState : ReferencePrelaunchFollower.State p rate.eta,
        ∃ cutoffMemory : ActiveFollowerLifecycle.LocalMemory p,
          (B[0]'hBlen).input.state.followers i = .ordinary cutoffState cutoffMemory ∧
          (let W0 := cutoffState.downBatch
            let C := ReferenceFollowerDownDecoderReplay.actualDownCalls i (B.take n.val)
            let P := ReferenceFollowerDownDecoderReplay.actualDownPositives i (B.take n.val)
            before.downBatch = ReferenceFollowerDownDecoderReplay.foldDownCalls C W0 ∧
            AffineBatchDecoder.collected before.downBatch =
              AffineBatchDecoder.collected W0 ++ P ∧
            W0.pending.length < AffineBatchDecoder.quota p ∧
            (∀ entry ∈ W0.pending, entry.time.val < start + w) ∧
            (C.map Prod.fst).map Fin.val =
              ReferenceActivePhysicalHorizon.calendar (start + w) n.val ∧
            P.Pairwise (fun earlier later => earlier.time.val < later.time.val) ∧
            (∀ entry ∈ P, start + w ≤ entry.time.val ∧ entry.time.val < start + w + n.val) ∧
            (∀ entry ∈ P, entry.sample =
              ((source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).2
                entry.time).2 (0, i)) ∧
            (∀ completed ∈ W0.completed,
              completed.length = AffineBatchDecoder.quota p) ∧
            (AffineBatchDecoder.collected W0).Pairwise
              (fun earlier later => earlier.time.val < later.time.val) ∧
            (∀ entry ∈ AffineBatchDecoder.collected W0, entry.time.val < start + w) ∧
            before.downBatch.completed =
              (ReferenceFollowerDownDecoderReplay.foldDownCalls C W0).completed) ∧
          ((B[n.val]'n.isLt).output.preparation.followers.followers i).time.val =
            start + w + n.val ∧
          ((B[n.val]'n.isLt).output.preparation.followers.followers i).row =
            source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) ∧
          (ReferenceFollowerDecoderChronology.downBatchEndpoint before
            (start + (w + n.val)) ∧
           (before.status ≠ .unoccupied → before.downBatch.pending = [])) ∧
          (∀ (diagnostic : ReferenceDownReception.ReferenceDownCutOutput p rate),
            ((B[n.val]'n.isLt).output.followers i).down = some diagnostic →
            diagnostic.rawComparison ≠ none →
            ∃ choice : ReferencePrelaunchFollower.State p rate.eta,
              ∃ choiceMemory : ActiveFollowerLifecycle.LocalMemory p,
              ∃ logged : ReferencePrelaunchFollower.State p rate.eta,
                let prep := (B[n.val]'n.isLt).output.preparation.followers.followers i
                let observation := (B[n.val]'n.isLt).output.preparation.feedback.observations
                  (PublicDiscreteDraws.followerPlayer p.two_le_m i)
                let own := (prep.arm, observation)
                let input := ActiveFollowerDownAcceptance.currentRoundInput p prep.follower prep.row
                  prep.time observation rate logged
                let decoded := ActiveFollowerDownAcceptance.currentDecodeStep p prep.follower prep.row
                  prep.time observation rate logged
                let trace := ActiveFollowerDownAcceptance.currentInputExtension p input
                prep.follower = i ∧
                prep.configuration = .ordinary choice choiceMemory ∧
                choice.status = .unoccupied ∧ logged.status = .unoccupied ∧
                ((B[n.val]'n.isLt).output.followers i).downInput = some logged ∧
                logged.downBatch = before.downBatch ∧
                diagnostic = ReferenceDownReception.referenceDownCut p
                  (B[n.val]'n.isLt).output.preparation.coordinator.downView prep.follower prep.row prep.time
                  observation rate logged ∧
                input.sample = (prep.row.2 prep.time).2 (0, prep.follower) ∧
                diagnostic.raw = decoded.2 ∧
                decoded = ReferencePrelaunchFollower.decodeAt prep.follower prep.row prep.activation
                  prep.time own logged.downBatch ∧
                AffineBatchDecoder.collected decoded.1 =
                  AffineBatchDecoder.collected logged.downBatch ++
                    AffineBatchDecoder.positiveAt p trace prep.time ∧
                (0 < observation.val.val →
                  AffineBatchDecoder.collected decoded.1 = AffineBatchDecoder.collected logged.downBatch ++
                    [AffineBatchDecoder.entry p trace prep.time]) ∧
                (observation.val.val = 0 → decoded = (logged.downBatch, none) ∧ diagnostic.raw = none) ∧
                (0 < observation.val.val → logged.downBatch.pending.length + 1 <
                  AffineBatchDecoder.quota p →
                  decoded = (⟨logged.downBatch.pending ++
                    [AffineBatchDecoder.entry p trace prep.time], logged.downBatch.completed⟩, none) ∧
                  diagnostic.raw = none) ∧
                (0 < observation.val.val → logged.downBatch.pending.length + 1 =
                  AffineBatchDecoder.quota p →
                  decoded =
                    (⟨[], logged.downBatch.completed ++ [logged.downBatch.pending ++
                      [AffineBatchDecoder.entry p
                        (ReferencePrelaunchFollower.traceAt prep.follower prep.row prep.activation
                          prep.time own) prep.time]]⟩,
                     AffineBatchDecoder.batchOutput (logged.downBatch.pending ++
                      [AffineBatchDecoder.entry p
                        (ReferencePrelaunchFollower.traceAt prep.follower prep.row prep.activation
                          prep.time own) prep.time])) ∧
                  (diagnostic.raw = none ↔ AffineBatchDecoder.batchOutput
                    (logged.downBatch.pending ++ [AffineBatchDecoder.entry p
                      (ReferencePrelaunchFollower.traceAt prep.follower prep.row prep.activation
                        prep.time own) prep.time]) = none))) := by
  classical
  intro start E w B n i before memory hfi
  let active := ReferenceFirstCollectionEpochAlignment.actualLaunchState
    rate source rewards C_star C_h hcross
  have hprefix := actual_cutoff_down_prefix_replay
    (p := p) rate source rewards C_star C_h count hcross hspan hshort
  rcases hprefix with ⟨cut, suffix, hsplit, hBlen, hB0, hchosen, htimeCut,
    hcutState, hseed, hreplay⟩
  obtain ⟨cutoffState, cutoffMemory, hcutOrd, hbank, hcollected, hpending,
      hpendingOld, hcalls, hpositivePair, hpositiveTime, hsamples, hcompletedSize,
      hcutChronological, hcutCollectedTime, hcompleted⟩ :=
    hreplay n i before memory hfi
  have hcutOrdB : (B[0]'hBlen).input.state.followers i = .ordinary cutoffState cutoffMemory := by
    rw [hB0]
    exact hcutOrd
  -- The actual connected run identifies each current input with the ordinary
  -- prefix endpoint; the public decoder chronology supplies its full bank.
  have hcount : E.records.length = count := by
    dsimp [E, ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun]
    exact ReferenceActivePhysicalHorizon.run_record_count active source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start count hspan
      (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
        rate source rewards C_star C_h hcross).1
  have hmode := (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
    rate source rewards C_star C_h hcross).1
  have hw : w < E.records.length := by
    rw [hcount]
    simpa [w, E] using hshort
  have hBdrop : B.length ≤ (E.records.drop w).length := by
    obtain ⟨tail, hprefix⟩ := collectionWindow_isPrefix E.records w
    have hlen := congrArg List.length hprefix
    have hlen' : B.length + tail.length = (E.records.drop w).length := by
      simpa only [B, List.length_append] using hlen
    omega
  have hnDrop : n.val < (E.records.drop w).length := lt_of_lt_of_le n.isLt hBdrop
  have hindex : w + n.val < E.records.length := by
    rw [List.length_drop] at hnDrop
    rw [hcount] at hnDrop
    omega
  let record := B[n.val]'n.isLt
  have hrecordIndex : record = E.records[w + n.val]'hindex := by
    dsimp [record]
    calc
      B[n.val]'n.isLt = (E.records.drop w)[n.val]'hnDrop :=
        collectionWindow_getElem_drop E.records w n.val hw n.isLt
      _ = E.records[w + n.val]'hindex := by simp only [List.getElem_drop]
  have hinputs := ReferenceActivePhysicalHorizon.run_record_inputs active source.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start count hspan hmode
    record (by rw [hrecordIndex]; exact List.getElem_mem hindex)
  have hrow : record.input.row = source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) := by
    simp [ReferenceActivePhysicalStep.RoundInput.row, hinputs]
  have htime : record.input.time.val = start + w + n.val := by
    have htimes := ReferenceActivePhysicalHorizon.run_time_values active source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start count hspan hmode
    have hget : E.records[w + n.val]? = some record := by
      rw [List.getElem?_eq_getElem hindex, hrecordIndex]
    have hgetRun :
        (ReferenceActivePhysicalHorizon.run active source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start count
          hspan hmode).records[w + n.val]? = some record := by
      simpa [E, ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun] using hget
    have hmap := congrArg (fun xs : List ℕ => xs[w + n.val]?) htimes
    rw [List.getElem?_map, hgetRun] at hmap
    have hj : w + n.val < count := by
      rw [hcount] at hindex
      exact hindex
    have hcal : (ReferenceActivePhysicalHorizon.calendar start count)[w + n.val]? =
        some (start + (w + n.val)) := by
      simp only [ReferenceActivePhysicalHorizon.calendar, List.getElem?_range' hj, Nat.one_mul]
    rw [hcal] at hmap
    simp only [Option.map_some] at hmap
    have htime' := Option.some.inj hmap
    omega
  have hrunFinal := run_final_eq_input_at active source.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start count
    (w + n.val) hspan hmode (by rw [hcount] at hindex; exact hindex)
  have hcurrent : record.input.state.followers i = .ordinary before memory := by
    simpa [record] using hfi
  have hordinary :
      (ReferenceActivePhysicalHorizon.run active source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start
        (w + n.val) (by omega) hmode).finalState.followers i = .ordinary before memory := by
    calc
      _ = (ReferenceActivePhysicalHorizon.run active source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start
          (w + n.val) (by omega) hmode).finalState.followers i := by simp
      _ = .ordinary before memory := by
        rw [congrArg (fun state => state.followers i) hrunFinal]
        rw [hrecordIndex] at hcurrent
        exact hcurrent
  obtain ⟨hbefore, hoccupied⟩ := ReferenceFollowerDecoderChronology.run_downBatch_spec
    active source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
    start (w + n.val) (by omega) hmode hseed i before memory hordinary
  have hprepRow : (record.output.preparation.followers.followers i).row =
      source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) := by
    exact (record.output.preparation.follower_alignment i).1.trans hrow
  have hprepTime : (record.output.preparation.followers.followers i).time.val =
      start + w + n.val := by
    rw [(record.output.preparation.follower_alignment i).2.2.1]
    exact htime
  refine ⟨hBlen, cutoffState, cutoffMemory, hcutOrdB,
    ⟨hbank, hcollected, hpending, hpendingOld, hcalls, hpositivePair, hpositiveTime,
      hsamples, hcompletedSize, hcutChronological, hcutCollectedTime, hcompleted⟩,
    hprepTime, hprepRow,
    ⟨hbefore, hoccupied⟩, ?_⟩
  intro diagnostic hdown hcompared
  exact retained_down_record_decoder_update rate (B[n.val]'n.isLt) i before memory hfi
    diagnostic hdown hcompared (start + (w + n.val)) hbefore hoccupied

end ReferenceFirstCollectionDownBankHistory

end Support

end Bandits
