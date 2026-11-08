/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedUpCallBankReplay

/-!
# Canonical reset intervals for actual generated UP calls

Sources: `sources/zip4/manuscript/appendix_a_local_protocol.tex:112-157`,
`sources/zip4/manuscript/05_binary_transport.tex:20-42,70-124`,
`sources/zip4/manuscript/06_interruptions.tex:277-284,327-348`, and
`sources/zip4/manuscript/07_public_setup.tex:121-164`.

The results retain the original corrected launch, rows, selected private row,
rewards, controls, and physical records. For each actual generated UP call,
they identify the last earlier actual quota completion on its selected channel
and derive the resulting same-run reset interval. Solver output, parsing,
acceptance, and physical commit remain separate from decoder quota completion.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceGeneratedActivePrefixFactor
open Bandits.Support.ReferenceCoordinatorUpDecoderReplay
open Bandits.Support.CoordinatorUpReception
open Bandits.Support.AffineBatchDecoder

namespace Bandits.Support.ReferenceGeneratedUpResetCalendar

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev TimeControl := ContinuousLearningRows.TimeControl

variable {p : Parameters} {rate : RateInput p}

private theorem foldCalendar_records_take_acc
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start : ℕ) (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (entries : List (ReferenceActivePhysicalHorizon.CalendarEntry p start))
    (acc : ReferenceActivePhysicalHorizon.Run initial) :
    (entries.foldl
      (ReferenceActivePhysicalHorizon.foldRound initial rows selected rewards start hmode)
      acc).records.take acc.records.length = acc.records := by
  induction entries generalizing acc with
  | nil => simp
  | cons entry entries ih =>
      change ((entries.foldl
        (ReferenceActivePhysicalHorizon.foldRound initial rows selected rewards start hmode)
        (ReferenceActivePhysicalHorizon.foldRound initial rows selected rewards start hmode
          acc entry)).records).take acc.records.length = acc.records
      let next := ReferenceActivePhysicalHorizon.foldRound initial rows selected rewards start hmode
        acc entry
      have htail := ih (acc := next)
      have hlen : acc.records.length ≤ next.records.length := by
        simp [next, ReferenceActivePhysicalHorizon.foldRound]
      calc
        _ = ((entries.foldl
              (ReferenceActivePhysicalHorizon.foldRound initial rows selected rewards start hmode)
              next).records.take next.records.length).take acc.records.length := by
          simp [next, List.take_take, Nat.min_eq_left hlen]
        _ = next.records.take acc.records.length := by rw [htail]
        _ = acc.records := by simp [next, ReferenceActivePhysicalHorizon.foldRound]

private theorem foldCalendar_records_take_acc_of_calendar
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (origin intervalStart count : ℕ) (horigin : origin ≤ intervalStart)
    (hspan : intervalStart + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial origin)
    (acc : ReferenceActivePhysicalHorizon.Run initial) :
    (ReferenceActivePhysicalHorizon.foldCalendar initial rows selected rewards origin intervalStart
      count horigin hspan hmode acc).records.take acc.records.length = acc.records := by
  exact foldCalendar_records_take_acc initial rows selected rewards origin hmode
    (ReferenceActivePhysicalHorizon.calendarEntries origin intervalStart count horigin hspan) acc

private theorem run_record_input_state_eq_prefix
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (k : ℕ) (hk : k < count) :
    let fullRun := ReferenceActivePhysicalHorizon.run initial rows selected rewards start count
      hspan hmode
    let prefixRun := ReferenceActivePhysicalHorizon.run initial rows selected rewards start k
      (by omega) hmode
    (fullRun.records[k]'(by
      dsimp only [fullRun]
      rw [ReferenceActivePhysicalHorizon.run_record_count]
      exact hk)).input.state = prefixRun.finalState ∧
      prefixRun.records = fullRun.records.take k ∧
      (fullRun.records[k]'(by
        dsimp only [fullRun]
        rw [ReferenceActivePhysicalHorizon.run_record_count]
        exact hk)).output.next =
        (ReferenceActivePhysicalHorizon.run initial rows selected rewards start (k + 1)
          (by omega) hmode).finalState := by
  dsimp only
  let fullRun := ReferenceActivePhysicalHorizon.run initial rows selected rewards start count hspan hmode
  let prefixRun := ReferenceActivePhysicalHorizon.run initial rows selected rewards start k
    (by omega) hmode
  have hfullCount := ReferenceActivePhysicalHorizon.run_record_count initial rows selected rewards
    start count hspan hmode
  have hkFull : k < fullRun.records.length := by
    simpa [fullRun, hfullCount] using hk
  have hkLe : k ≤ count := by omega
  have hprefixCount := ReferenceActivePhysicalHorizon.run_record_count initial rows selected rewards
    start k (by omega) hmode
  have hsplit0 := ReferenceActivePhysicalHorizon.run_append initial rows selected rewards start k
    (count - k) (by omega) hmode
  have hsplit : fullRun = ReferenceActivePhysicalHorizon.foldCalendar initial rows selected rewards
      start (start + k) (count - k) (by omega) (by omega) hmode prefixRun := by
    dsimp [fullRun, prefixRun] at hsplit0 ⊢
    simpa [Nat.add_sub_of_le hkLe] using hsplit0
  have htakeAcc := foldCalendar_records_take_acc_of_calendar initial rows selected rewards
    start (start + k) (count - k) (by omega) (by omega) hmode prefixRun
  have hprefixRecords : prefixRun.records = fullRun.records.take k := by
    have htake : fullRun.records.take prefixRun.records.length = prefixRun.records := by
      rw [hsplit]
      exact htakeAcc
    have hprefixLen : prefixRun.records.length = k := by
      simpa [prefixRun] using hprefixCount
    simpa [hprefixLen] using htake.symm

  have hkSucc : k + 1 ≤ count := by omega
  let successorRun := ReferenceActivePhysicalHorizon.run initial rows selected rewards start (k + 1)
    (by omega) hmode
  have hsuccessorCount := ReferenceActivePhysicalHorizon.run_record_count initial rows selected rewards
    start (k + 1) (by omega) hmode
  have hsplitSucc0 := ReferenceActivePhysicalHorizon.run_append initial rows selected rewards start
    (k + 1) (count - (k + 1)) (by omega) hmode
  have hsplitSucc : fullRun = ReferenceActivePhysicalHorizon.foldCalendar initial rows selected
      rewards start (start + (k + 1)) (count - (k + 1)) (by omega) (by omega) hmode successorRun := by
    dsimp [fullRun, successorRun] at hsplitSucc0 ⊢
    simpa [Nat.add_sub_of_le hkSucc] using hsplitSucc0
  have htakeSuccAcc := foldCalendar_records_take_acc_of_calendar initial rows selected rewards
    start (start + (k + 1)) (count - (k + 1)) (by omega) (by omega) hmode successorRun
  have hsuccessorRecords : successorRun.records = fullRun.records.take (k + 1) := by
    have htake : fullRun.records.take successorRun.records.length = successorRun.records := by
      rw [hsplitSucc]
      exact htakeSuccAcc
    have hsuccessorLen : successorRun.records.length = k + 1 := by
      simpa [successorRun] using hsuccessorCount
    simpa [hsuccessorLen] using htake.symm

  let entry : ReferenceActivePhysicalHorizon.CalendarEntry p start :=
    ⟨start + k, by omega, by omega⟩
  let input := ReferenceActivePhysicalHorizon.roundInputAt initial rows selected rewards start hmode
    prefixRun entry
  have hstepRun := ReferenceActivePhysicalHorizon.run_successor_step initial rows selected rewards
    start k (by omega) hmode
  have hsuccessorRecordList : successorRun.records = prefixRun.records ++
      [⟨input, ReferenceActivePhysicalStep.step input, rfl⟩] := by
    simpa [successorRun, prefixRun, input, entry,
      ReferenceActivePhysicalHorizon.foldRound,
      ReferenceActivePhysicalHorizon.roundInputAt] using
        congrArg ReferenceActivePhysicalHorizon.Run.records hstepRun
  have hprefixLen : prefixRun.records.length = k := by
    simpa [prefixRun] using hprefixCount
  have hrecordAtSuccessor? : successorRun.records[k]? =
      some ⟨input, ReferenceActivePhysicalStep.step input, rfl⟩ := by
    rw [hsuccessorRecordList]
    simp [hprefixLen]
  have hrecordFull? : fullRun.records[k]? =
      some ⟨input, ReferenceActivePhysicalStep.step input, rfl⟩ := by
    calc
      fullRun.records[k]? = (fullRun.records.take (k + 1))[k]? := by simp [hkFull]
      _ = successorRun.records[k]? := by rw [← hsuccessorRecords]
      _ = some ⟨input, ReferenceActivePhysicalStep.step input, rfl⟩ := hrecordAtSuccessor?
  have hrecordEq : fullRun.records[k]'hkFull =
      ⟨input, ReferenceActivePhysicalStep.step input, rfl⟩ := by
    simpa [List.getElem?_eq_getElem hkFull] using hrecordFull?
  have hsuccessorFinal : successorRun.finalState =
      (ReferenceActivePhysicalStep.step input).next := by
    rw [show successorRun = ReferenceActivePhysicalHorizon.run initial rows selected rewards start
      (k + 1) (by omega) hmode by rfl, hstepRun]
    rfl
  have hrecordNext : (fullRun.records[k]'hkFull).output.next = successorRun.finalState := by
    rw [hrecordEq]
    exact hsuccessorFinal.symm
  constructor
  · rw [hrecordEq]
    rfl
  constructor
  · exact hprefixRecords
  · exact hrecordNext

private theorem run_prefix_records_eq
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (left : ℕ) (hleft : left ≤ count) :
    (ReferenceActivePhysicalHorizon.run initial rows selected rewards start left
      (by omega) hmode).records =
    (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count
      hspan hmode).records.take left := by
  let whole := ReferenceActivePhysicalHorizon.run initial rows selected rewards start count hspan hmode
  let preRun := ReferenceActivePhysicalHorizon.run initial rows selected rewards start left (by omega) hmode
  have hcount := ReferenceActivePhysicalHorizon.run_record_count initial rows selected rewards
    start count hspan hmode
  have hprefixCount := ReferenceActivePhysicalHorizon.run_record_count initial rows selected rewards
    start left (by omega) hmode
  have hsplit0 := ReferenceActivePhysicalHorizon.run_append initial rows selected rewards start left
    (count - left) (by omega) hmode
  have hsplit : whole = ReferenceActivePhysicalHorizon.foldCalendar initial rows selected rewards
      start (start + left) (count - left) (by omega) (by omega) hmode preRun := by
    dsimp [whole, preRun] at hsplit0 ⊢
    simpa [Nat.add_sub_of_le hleft] using hsplit0
  have htakeAcc := foldCalendar_records_take_acc_of_calendar initial rows selected rewards
    start (start + left) (count - left) (by omega) (by omega) hmode preRun
  have htake : whole.records.take preRun.records.length = preRun.records := by
    rw [hsplit]
    exact htakeAcc
  have hprefixLen : preRun.records.length = left := by simpa [preRun] using hprefixCount
  simpa [whole, hprefixLen] using htake.symm

private theorem connected_drop_after_prefix
    {initial middle final : ReferenceActivePhysicalStep.State p rate}
    {records preRecords : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))}
    (left : ℕ)
    (hconnected : ReferenceActivePhysicalHorizon.Connected initial records final)
    (hrecords : records.take left = preRecords)
    (hprefix : ReferenceActivePhysicalHorizon.Connected initial preRecords middle) :
    ReferenceActivePhysicalHorizon.Connected middle (records.drop left) final := by
  induction left generalizing initial middle records preRecords with
  | zero =>
      simp only [List.take_zero, List.drop_zero] at hrecords
      subst preRecords
      simp only [ReferenceActivePhysicalHorizon.Connected] at hprefix
      subst middle
      exact hconnected
  | succ left ih =>
      cases records with
      | nil =>
          simp at hrecords
          subst preRecords
          have hmiddle : middle = initial := by
            simpa [ReferenceActivePhysicalHorizon.Connected] using hprefix
          have hfinal : final = initial := by
            simpa [ReferenceActivePhysicalHorizon.Connected] using hconnected
          rw [hfinal, hmiddle]
          simp [ReferenceActivePhysicalHorizon.Connected]
      | cons head tail =>
          cases preRecords with
          | nil => simp at hrecords
          | cons first rest =>
              change head.input.state = initial ∧
                ReferenceActivePhysicalHorizon.Connected head.output.next tail final at hconnected
              have htailRecords : tail.take left = rest := by
                have h := congrArg List.tail hrecords
                simpa using h
              have hprefix' :
                  ReferenceActivePhysicalHorizon.Connected head.output.next rest middle := by
                change first.input.state = initial ∧
                  ReferenceActivePhysicalHorizon.Connected first.output.next rest middle at hprefix
                have hfirst : first = head := by
                  have hcons : head :: List.take left tail = first :: rest := by
                    simpa using hrecords
                  exact (List.cons.inj hcons).1.symm
                subst first
                exact hprefix.2
              simpa using ih hconnected.2 htailRecords hprefix'

private theorem calendar_drop
    (start count left : ℕ) (hleft : left ≤ count) :
    (ReferenceActivePhysicalHorizon.calendar start count).drop left =
      ReferenceActivePhysicalHorizon.calendar (start + left) (count - left) := by
  induction left generalizing start count with
  | zero => simp [ReferenceActivePhysicalHorizon.calendar]
  | succ left ih =>
      cases count with
      | zero => omega
      | succ count =>
          have hleft' : left ≤ count := by omega
          simpa [ReferenceActivePhysicalHorizon.calendar,
            List.range'_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            ih (start + 1) count hleft'

private theorem foldEntries_drop_acc
    {initial reset : ReferenceActivePhysicalStep.State p rate}
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (origin resetOrigin : ℕ)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial origin)
    (hresetMode : ReferenceActivePhysicalHorizon.allActiveAtStart reset resetOrigin)
    (entries : List (ReferenceActivePhysicalHorizon.CalendarEntry p origin))
    (resetEntries : List (ReferenceActivePhysicalHorizon.CalendarEntry p resetOrigin))
    (hvalues : entries.map Subtype.val = resetEntries.map Subtype.val)
    (dropCount : ℕ)
    (left : ReferenceActivePhysicalHorizon.Run initial)
    (right : ReferenceActivePhysicalHorizon.Run reset)
    (hstate : left.finalState = right.finalState)
    (hdrop : right.records = left.records.drop dropCount)
    (hlen : dropCount ≤ left.records.length) :
    let leftResult := entries.foldl
      (ReferenceActivePhysicalHorizon.foldRound initial rows selected rewards origin hmode) left
    let rightResult := resetEntries.foldl
      (ReferenceActivePhysicalHorizon.foldRound reset rows selected rewards resetOrigin hresetMode) right
    rightResult.records = leftResult.records.drop dropCount ∧
      rightResult.finalState = leftResult.finalState := by
  induction entries generalizing resetEntries left right with
  | nil =>
      cases resetEntries with
      | nil => simpa using ⟨hdrop, hstate.symm⟩
      | cons entry rest => simp at hvalues
  | cons entry entries ih =>
      cases resetEntries with
      | nil => simp at hvalues
      | cons resetEntry resetEntries =>
        have hmap : entry.val :: (entries.map Subtype.val) =
            resetEntry.val :: (resetEntries.map Subtype.val) := by
          simpa only [List.map_cons] using hvalues
        have hvalue : entry.val = resetEntry.val := (List.cons.inj hmap).1
        have htailValues : entries.map Subtype.val = resetEntries.map Subtype.val :=
          (List.cons.inj hmap).2
        let leftNext := ReferenceActivePhysicalHorizon.foldRound initial rows selected rewards
          origin hmode left entry
        let rightNext := ReferenceActivePhysicalHorizon.foldRound reset rows selected rewards
          resetOrigin hresetMode right resetEntry
        have hinput :
            ReferenceActivePhysicalHorizon.roundInputAt initial rows selected rewards origin hmode
              left entry =
            ReferenceActivePhysicalHorizon.roundInputAt reset rows selected rewards resetOrigin hresetMode
              right resetEntry := by
          cases left with
          | mk leftState leftRecords leftActivation leftConnected =>
            cases right with
            | mk rightState rightRecords rightActivation rightConnected =>
              change leftState = rightState at hstate
              have htime : (⟨entry.val, entry.property.2⟩ : Fin p.T) =
                  ⟨resetEntry.val, resetEntry.property.2⟩ := by
                apply Fin.ext
                exact hvalue
              cases hstate
              simp only [ReferenceActivePhysicalHorizon.roundInputAt]
              congr 1 <;> try rfl
              all_goals first
              | exact htime
              | apply Subsingleton.elim
              | (funext i; exact Subsingleton.elim _ _)
        let leftInput := ReferenceActivePhysicalHorizon.roundInputAt initial rows selected rewards
          origin hmode left entry
        let rightInput := ReferenceActivePhysicalHorizon.roundInputAt reset rows selected rewards
          resetOrigin hresetMode right resetEntry
        let leftRecord : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) :=
          ⟨leftInput, ReferenceActivePhysicalStep.step leftInput, rfl⟩
        let rightRecord : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) :=
          ⟨rightInput, ReferenceActivePhysicalStep.step rightInput, rfl⟩
        have hrecord : leftRecord = rightRecord := by
          exact congrArg (fun input =>
            (⟨input, ReferenceActivePhysicalStep.step input, rfl⟩ :
              ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))) hinput
        have hleftNext : leftNext.records = left.records ++ [leftRecord] := by
          rfl
        have hrightNext : rightNext.records = right.records ++ [rightRecord] := by
          rfl
        have hstateNext : leftNext.finalState = rightNext.finalState := by
          change leftRecord.output.next = rightRecord.output.next
          exact congrArg (fun record => record.output.next) hrecord
        have hdropNext : rightNext.records = leftNext.records.drop dropCount := by
          rw [hleftNext, hrightNext, List.drop_append_of_le_length hlen, hdrop, hrecord]
        have hlenNext : dropCount ≤ leftNext.records.length := by
          rw [hleftNext, List.length_append]
          omega
        simpa [leftNext, rightNext] using
          ih resetEntries htailValues leftNext rightNext hstateNext hdropNext hlenNext

private theorem run_suffix_records
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start leftCount rightCount : ℕ)
    (hspan : start + (leftCount + rightCount) ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start) :
    let prefixRun := ReferenceActivePhysicalHorizon.run initial rows selected rewards start leftCount
      (by omega) hmode
    let resetMode := ReferenceActivePhysicalHorizon.run_allActiveAtEnd initial rows selected rewards
      start leftCount (by omega) hmode
    (ReferenceActivePhysicalHorizon.run prefixRun.finalState rows selected rewards
      (start + leftCount) rightCount (by omega) resetMode).records =
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start
        (leftCount + rightCount) hspan hmode).records.drop leftCount ∧
    (ReferenceActivePhysicalHorizon.run prefixRun.finalState rows selected rewards
      (start + leftCount) rightCount (by omega) resetMode).finalState =
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start
        (leftCount + rightCount) hspan hmode).finalState := by
  dsimp only
  let prefixRun := ReferenceActivePhysicalHorizon.run initial rows selected rewards start leftCount
    (by omega) hmode
  let resetMode := ReferenceActivePhysicalHorizon.run_allActiveAtEnd initial rows selected rewards
    start leftCount (by omega) hmode
  let emptyRun : ReferenceActivePhysicalHorizon.Run prefixRun.finalState :=
    ⟨prefixRun.finalState, [], rfl, by simp [ReferenceActivePhysicalHorizon.Connected]⟩
  have hprefixLen : prefixRun.records.length = leftCount := by
    simpa [prefixRun] using ReferenceActivePhysicalHorizon.run_record_count initial rows selected
      rewards start leftCount (by omega) hmode
  have hemptyDrop : emptyRun.records = prefixRun.records.drop leftCount := by
    simp [emptyRun, hprefixLen]
  have hpair := foldEntries_drop_acc rows selected rewards start (start + leftCount) hmode resetMode
    (ReferenceActivePhysicalHorizon.calendarEntries start (start + leftCount) rightCount
      (by omega) (by omega))
    (ReferenceActivePhysicalHorizon.calendarEntries (start + leftCount) (start + leftCount)
      rightCount le_rfl (by omega))
    (by
      change (ReferenceActivePhysicalHorizon.calendarEntries start (start + leftCount)
        rightCount (by omega) (by omega)).unattach =
        (ReferenceActivePhysicalHorizon.calendarEntries (start + leftCount)
          (start + leftCount) rightCount le_rfl (by omega)).unattach
      rw [ReferenceActivePhysicalHorizon.calendarEntries_time_values,
        ReferenceActivePhysicalHorizon.calendarEntries_time_values])
    leftCount prefixRun emptyRun rfl hemptyDrop (by omega)
  have happend := ReferenceActivePhysicalHorizon.run_append initial rows selected rewards start
    leftCount rightCount hspan hmode
  let suffixRun := ReferenceActivePhysicalHorizon.run prefixRun.finalState rows selected rewards
    (start + leftCount) rightCount (by omega) resetMode
  let wholeRun := ReferenceActivePhysicalHorizon.run initial rows selected rewards start
    (leftCount + rightCount) hspan hmode
  let continued := ReferenceActivePhysicalHorizon.foldCalendar initial rows selected rewards start
    (start + leftCount) rightCount (by omega) (by omega) hmode prefixRun
  have happend' : wholeRun = continued := by
    simpa [wholeRun, continued, prefixRun] using happend
  have hright : suffixRun.records =
      ((ReferenceActivePhysicalHorizon.calendarEntries (start + leftCount)
        (start + leftCount) rightCount le_rfl (by omega)).foldl
        (ReferenceActivePhysicalHorizon.foldRound prefixRun.finalState rows selected rewards
          (start + leftCount) resetMode) emptyRun).records := by
    rfl
  constructor
  · calc
      suffixRun.records = continued.records.drop leftCount := by
        rw [hright]
        simpa [continued, ReferenceActivePhysicalHorizon.foldCalendar] using hpair.1
      _ = wholeRun.records.drop leftCount := by rw [← happend']
  · have hstatePair : suffixRun.finalState = continued.finalState := by
      simpa [suffixRun, continued, prefixRun, emptyRun, ReferenceActivePhysicalHorizon.run,
        ReferenceActivePhysicalHorizon.foldCalendar] using hpair.2
    calc
      suffixRun.finalState = continued.finalState := hstatePair
      _ = wholeRun.finalState := congrArg ReferenceActivePhysicalHorizon.Run.finalState happend'.symm

private def actualUpQuotaCompletion
    (i : Fin (p.m - 1))
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) : Prop :=
  ∃ diagnostic : ReferenceActivePhysicalStep.UpDiagnostic p rate,
    record.output.coordinator.up = some diagnostic ∧
    diagnostic.input.selectedFollower = i ∧
    ReferenceGeneratedAffineHashHalf.directionPositive 1 record.input = true ∧
    (record.input.state.upDecoderBank i).pending.length + 1 = AffineBatchDecoder.quota p

private noncomputable def actualUpQuotaOffsets
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (i : Fin (p.m - 1)) (count : ℕ) (hcount : count ≤ records.length) : Finset (Fin count) := by
  classical
  exact Finset.univ.filter fun j => actualUpQuotaCompletion i (records[j.val]'(by omega))

private theorem actualUpQuotaCompletion_none_of_empty_offsets
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (i : Fin (p.m - 1)) (count : ℕ) (hcount : count = records.length)
    (hempty : actualUpQuotaOffsets records i count (Nat.le_of_eq hcount) = ∅) :
    ∀ j : Fin count, ¬ actualUpQuotaCompletion i (records[j.val]'(by omega)) := by
  classical
  intro j hcompletion
  have hmem : j ∈ actualUpQuotaOffsets records i count (Nat.le_of_eq hcount) := by
    simp [actualUpQuotaOffsets, hcompletion]
  rw [hempty] at hmem
  simp at hmem

private theorem actualUpQuotaCompletion_none_after_max
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (i : Fin (p.m - 1)) (count : ℕ) (hcount : count = records.length)
    (j : Fin count)
    (hmax : ∀ l : Fin count,
      actualUpQuotaCompletion i (records[l.val]'(by omega)) → l.val ≤ j.val) :
    ∀ record, record ∈ records.drop (j.val + 1) →
      ¬ actualUpQuotaCompletion i record := by
  intro record hmem hcompletion
  obtain ⟨n, hn, hget⟩ := List.mem_iff_getElem.mp hmem
  have hbound : j.val + 1 + n < records.length := by
    have hlength := hn
    simp [List.length_drop] at hlength
    omega
  have hcountEq : records.length = count := hcount.symm
  let l : Fin count := ⟨j.val + 1 + n, by omega⟩
  have hrecord : records[l.val]'(by omega) = record := by
    simpa [l, List.getElem_drop] using hget
  have hmax' := hmax l (by simpa [hrecord] using hcompletion)
  change j.val + 1 + n ≤ j.val at hmax'
  omega

private theorem actualUpQuotaCompletion_none_of_empty_after_drop
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (i : Fin (p.m - 1)) (count : ℕ) (hcount : count = records.length)
    (hempty : actualUpQuotaOffsets records i count (Nat.le_of_eq hcount) = ∅)
    (dropCount : ℕ) (hdrop : dropCount ≤ count) :
    ∀ record, record ∈ records.drop dropCount →
      ¬ actualUpQuotaCompletion i record := by
  intro record hmem hcompletion
  obtain ⟨n, hn, hget⟩ := List.mem_iff_getElem.mp hmem
  have hbound : dropCount + n < records.length := by
    have hlength := hn
    simp [List.length_drop] at hlength
    omega
  have hcountEq : records.length = count := hcount.symm
  let j : Fin count := ⟨dropCount + n, by omega⟩
  have hrecord : records[j.val]'(by omega) = record := by
    simpa [j, List.getElem_drop] using hget
  have hnone := actualUpQuotaCompletion_none_of_empty_offsets records i count hcount hempty j
  exact hnone (by simpa [hrecord] using hcompletion)

private theorem actual_record_channel_completed_unchanged
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1))
    (hinvariant : ReferenceUpDecoderBankInvariant.upBankInvariant record.input.state)
    (hsurvives : record.output.next.coordinator ≠ .dagger)
    (hno : ¬ actualUpQuotaCompletion i record) :
    (record.output.next.upDecoderBank i).completed =
      (record.input.state.upDecoderBank i).completed := by
  classical
  have hreplay := ReferenceCoordinatorUpDecoderReplay.ordinaryRecord_upDecoderBank_replay
    record hinvariant hsurvives
  cases hdiagnostic : record.output.coordinator.up with
  | none =>
      have hbank : record.output.next.upDecoderBank = record.input.state.upDecoderBank := by
        simpa [ReferenceCoordinatorUpDecoderReplay.replayOption, hdiagnostic] using hreplay
      rw [hbank]
  | some diagnostic =>
      obtain ⟨_, _, _, hinput, hafter, _, _, _, _, _, htime, hbank, _, _⟩ :=
        Bandits.Support.ReferenceGeneratedUpBatchCalendar.record_up_executed_fields
          record diagnostic hdiagnostic
      have hbankSelectedAt : diagnostic.input.upDecoderBank diagnostic.input.selectedFollower =
          record.input.state.upDecoderBank diagnostic.input.selectedFollower := congrFun hbank _
      have htransition : (CoordinatorUpReception.decoderTransition diagnostic.input).1 =
          (AffineBatchDecoder.decodeStep p
            (ReferenceCoordinatorUpDecoderReplay.constantInputTrace diagnostic.input)
            (record.input.state.upDecoderBank diagnostic.input.selectedFollower)
            diagnostic.input.time).1 := by
        change (AffineBatchDecoder.decodeStep p
          (ReferenceCoordinatorUpDecoderReplay.constantInputTrace diagnostic.input)
          (diagnostic.input.upDecoderBank diagnostic.input.selectedFollower)
          diagnostic.input.time).1 = _
        rw [hbankSelectedAt]
      have hcomponent : record.output.next.upDecoderBank i =
          Function.update record.input.state.upDecoderBank diagnostic.input.selectedFollower
            ((CoordinatorUpReception.decoderTransition diagnostic.input).1) i := by
        have h := congrFun hreplay i
        have htmp : record.output.next.upDecoderBank i =
            Function.update record.input.state.upDecoderBank diagnostic.input.selectedFollower
              (AffineBatchDecoder.decodeStep p
                (ReferenceCoordinatorUpDecoderReplay.constantInputTrace diagnostic.input)
                (record.input.state.upDecoderBank diagnostic.input.selectedFollower)
                diagnostic.input.time).1 i := by
          simpa [ReferenceCoordinatorUpDecoderReplay.replayOption,
            ReferenceCoordinatorUpDecoderReplay.replayOne,
            ReferenceCoordinatorUpDecoderReplay.retainedUpFollower,
            ReferenceCoordinatorUpDecoderReplay.retainedUpTime, hdiagnostic] using h
        rw [← htransition] at htmp
        exact htmp
      by_cases hselected : diagnostic.input.selectedFollower = i
      · have hsmall : (record.input.state.upDecoderBank i).pending.length <
            AffineBatchDecoder.quota p := by
          have hinvariant' := hinvariant
          change ReferenceUpDecoderBankInvariant.coordinatorBankInvariant
            record.input.state.coordinator record.input.state.upDecoderBank at hinvariant'
          exact (hinvariant'.1 i).1
        have hdirection : ReferenceGeneratedAffineHashHalf.directionPositive 1 record.input =
            decide (AffineBatchDecoder.eligible
              (CoordinatorUpReception.roundInput diagnostic.input)) := by
          calc
            _ = ReferenceActiveAffinePositiveTest.upPositive record.input := by
              simp [ReferenceGeneratedAffineHashHalf.directionPositive]
            _ = ReferenceActiveAffinePositiveTest.upDiagnosticPositive
                record.output.coordinator.up :=
              ReferenceActiveAffinePositiveTest.record_upPositive record
            _ = decide (AffineBatchDecoder.eligible
                (CoordinatorUpReception.roundInput diagnostic.input)) := by
              rw [hdiagnostic]
              rfl
        have htransitionSelected : (CoordinatorUpReception.decoderTransition diagnostic.input).1 =
            (AffineBatchDecoder.decodeStep p
              (ReferenceCoordinatorUpDecoderReplay.constantInputTrace diagnostic.input)
              (record.input.state.upDecoderBank i) diagnostic.input.time).1 := by
          simpa [hselected] using htransition
        by_cases hpositive :
            ReferenceGeneratedAffineHashHalf.directionPositive 1 record.input = true
        · have hnotquota : ¬
              (record.input.state.upDecoderBank i).pending.length + 1 =
                AffineBatchDecoder.quota p := by
            intro hquota
            exact hno ⟨diagnostic, hdiagnostic, hselected, hpositive, hquota⟩
          have hdecision : decide (AffineBatchDecoder.eligible
              (CoordinatorUpReception.roundInput diagnostic.input)) = true := by
            rw [← hdirection]
            exact hpositive
          have heligible : AffineBatchDecoder.eligible
              (ReferenceCoordinatorUpDecoderReplay.constantInputTrace diagnostic.input
                diagnostic.input.time) := by
            simpa [ReferenceCoordinatorUpDecoderReplay.constantInputTrace] using
              of_decide_eq_true hdecision
          have hbelow : (record.input.state.upDecoderBank i).pending.length + 1 <
              AffineBatchDecoder.quota p := by omega
          have hstep :
              (AffineBatchDecoder.decodeStep p
                (ReferenceCoordinatorUpDecoderReplay.constantInputTrace diagnostic.input)
                (record.input.state.upDecoderBank i) diagnostic.input.time).1.completed =
              (record.input.state.upDecoderBank i).completed := by
            simp [AffineBatchDecoder.decodeStep, AffineBatchDecoder.step,
              AffineBatchDecoder.positiveAt, heligible, List.length_append, hbelow]
          rw [hcomponent]
          simp only [hselected, Function.update_self]
          rw [htransitionSelected]
          exact hstep
        · have hdecision : decide (AffineBatchDecoder.eligible
              (CoordinatorUpReception.roundInput diagnostic.input)) = false := by
            rw [← hdirection]
            have hpositiveFalse :
                ReferenceGeneratedAffineHashHalf.directionPositive 1 record.input = false := by
              cases hdir : ReferenceGeneratedAffineHashHalf.directionPositive 1 record.input <;>
                simp_all
            exact hpositiveFalse
          have hnoteligible : ¬ AffineBatchDecoder.eligible
              (ReferenceCoordinatorUpDecoderReplay.constantInputTrace diagnostic.input
                diagnostic.input.time) := by
            simpa [ReferenceCoordinatorUpDecoderReplay.constantInputTrace] using
              of_decide_eq_false hdecision
          have hstep := AffineBatchDecoder.decodeStep_ineligible p
            (ReferenceCoordinatorUpDecoderReplay.constantInputTrace diagnostic.input)
            (record.input.state.upDecoderBank i) diagnostic.input.time hsmall hnoteligible
          have hcompleted :
              (AffineBatchDecoder.decodeStep p
                (ReferenceCoordinatorUpDecoderReplay.constantInputTrace diagnostic.input)
                (record.input.state.upDecoderBank i) diagnostic.input.time).1.completed =
              (record.input.state.upDecoderBank i).completed := by
            rw [hstep]
          rw [hcomponent]
          simp only [hselected, Function.update_self]
          rw [htransitionSelected]
          exact hcompleted
      · have hunchanged :
            (Function.update record.input.state.upDecoderBank diagnostic.input.selectedFollower
              ((CoordinatorUpReception.decoderTransition diagnostic.input).1)) i =
              record.input.state.upDecoderBank i := by
          exact Function.update_of_ne (Ne.symm hselected)
            ((CoordinatorUpReception.decoderTransition diagnostic.input).1)
            record.input.state.upDecoderBank
        rw [hcomponent, hunchanged]

private theorem connected_suffix_of_record_mem
    {initial final : ReferenceActivePhysicalStep.State p rate}
    {records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))}
    (hconnected : ReferenceActivePhysicalHorizon.Connected initial records final)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hmem : record ∈ records) :
    ∃ suffix, ReferenceActivePhysicalHorizon.Connected record.output.next suffix final := by
  induction records generalizing initial with
  | nil => simp at hmem
  | cons head tail ih =>
      change head.input.state = initial ∧
        ReferenceActivePhysicalHorizon.Connected head.output.next tail final at hconnected
      rcases List.mem_cons.mp hmem with heq | htail
      · cases heq
        exact ⟨tail, hconnected.2⟩
      · exact ih hconnected.2 htail

private theorem connected_record_successors_ordinary
    {initial final : ReferenceActivePhysicalStep.State p rate}
    {records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))}
    (hconnected : ReferenceActivePhysicalHorizon.Connected initial records final)
    (hfinal : final.coordinator ≠ .dagger) :
    ∀ record, record ∈ records → record.output.next.coordinator ≠ .dagger := by
  intro record hmem hdagger
  obtain ⟨suffix, htail⟩ := connected_suffix_of_record_mem hconnected record hmem
  exact hfinal (ReferenceActivePhysicalHorizon.Connected.coordinator_dagger htail hdagger).1

private theorem connected_up_completed_unchanged
    {initial final : ReferenceActivePhysicalStep.State p rate}
    {records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))}
    (hconnected : ReferenceActivePhysicalHorizon.Connected initial records final)
    (hinvariant : ∀ record, record ∈ records →
      ReferenceUpDecoderBankInvariant.upBankInvariant record.input.state)
    (hfinal : final.coordinator ≠ .dagger)
    (i : Fin (p.m - 1))
    (hno : ∀ record, record ∈ records → ¬ actualUpQuotaCompletion i record) :
    (final.upDecoderBank i).completed = (initial.upDecoderBank i).completed := by
  induction records generalizing initial with
  | nil =>
      have hfinalEq : final = initial := by simpa [ReferenceActivePhysicalHorizon.Connected] using hconnected
      rw [hfinalEq]
  | cons head tail ih =>
      change head.input.state = initial ∧
        ReferenceActivePhysicalHorizon.Connected head.output.next tail final at hconnected
      have hheadInv : ReferenceUpDecoderBankInvariant.upBankInvariant head.input.state :=
        hinvariant head (by simp)
      have hheadNo : ¬ actualUpQuotaCompletion i head := hno head (by simp)
      have hheadOrd : head.output.next.coordinator ≠ .dagger := by
        intro hdagger
        exact hfinal
          (ReferenceActivePhysicalHorizon.Connected.coordinator_dagger hconnected.2 hdagger).1
      have htailInv : ∀ record, record ∈ tail →
          ReferenceUpDecoderBankInvariant.upBankInvariant record.input.state := by
        intro record hrecord
        exact hinvariant record (List.mem_cons_of_mem _ hrecord)
      have htailNo : ∀ record, record ∈ tail → ¬ actualUpQuotaCompletion i record := by
        intro record hrecord
        exact hno record (List.mem_cons_of_mem _ hrecord)
      have htail := ih hconnected.2 htailInv htailNo
      have hstep := actual_record_channel_completed_unchanged head i hheadInv hheadOrd hheadNo
      calc
        (final.upDecoderBank i).completed = (head.output.next.upDecoderBank i).completed := htail
        _ = (head.input.state.upDecoderBank i).completed := hstep
        _ = (initial.upDecoderBank i).completed := by rw [hconnected.1]

private theorem actual_run_up_reset_interval_tail
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (currentState : ReferenceActivePhysicalStep.State p rate)
    (hcurrentState : currentState =
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count hspan hmode).finalState)
    (hordinary : currentState.coordinator ≠ .dagger)
    (hinvariant : ReferenceUpDecoderBankInvariant.upBankInvariant currentState)
    (i : Fin (p.m - 1))
    (resetCount : ℕ) (hresetCount : resetCount ≤ count)
    (resetState : ReferenceActivePhysicalStep.State p rate)
    (hresetState : resetState =
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start resetCount
        (by omega) hmode).finalState)
    (hresetPending : (resetState.upDecoderBank i).pending = [])
    (hresetInvariant : ReferenceUpDecoderBankInvariant.upBankInvariant resetState)
    (hno : ∀ record,
      record ∈ ((ReferenceActivePhysicalHorizon.run initial rows selected rewards start count
        hspan hmode).records.drop resetCount) → ¬ actualUpQuotaCompletion i record) :
    let resetMode := Eq.mp
      (congrArg (fun state => ReferenceActivePhysicalHorizon.allActiveAtStart state
        (start + resetCount)) hresetState).symm
      (ReferenceActivePhysicalHorizon.run_allActiveAtEnd initial rows selected rewards
        start resetCount (by omega) hmode)
    let suffixRun := ReferenceActivePhysicalHorizon.run resetState rows selected rewards
      (start + resetCount) (count - resetCount) (by omega) resetMode
    suffixRun.records =
        List.drop resetCount
          ((ReferenceActivePhysicalHorizon.run initial rows selected rewards start count hspan hmode).records) ∧
      suffixRun.finalState =
        (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count hspan hmode).finalState ∧
      ReferenceActivePhysicalHorizon.Connected resetState suffixRun.records suffixRun.finalState ∧
      suffixRun.records.map (fun record => record.input.time.val) =
        ReferenceActivePhysicalHorizon.calendar (start + resetCount) (count - resetCount) ∧
      (∀ record, record ∈ suffixRun.records →
        ReferenceUpDecoderBankInvariant.upBankInvariant record.input.state) ∧
      (∀ record, record ∈ suffixRun.records → ¬ actualUpQuotaCompletion i record) ∧
      (suffixRun.finalState.upDecoderBank i).completed =
        (resetState.upDecoderBank i).completed ∧
      (suffixRun.finalState.upDecoderBank i).pending =
        ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries suffixRun.records i ∧
      (suffixRun.finalState.upDecoderBank i).pending.length < AffineBatchDecoder.quota p ∧
      (∀ record, record ∈ suffixRun.records →
        record.input.rows = rows ∧ record.input.selected = selected ∧ record.input.rewards = rewards) := by
  dsimp only
  let prefixRun := ReferenceActivePhysicalHorizon.run initial rows selected rewards start count hspan hmode
  let resetPrefix := ReferenceActivePhysicalHorizon.run initial rows selected rewards start resetCount
    (by omega) hmode
  let resetModePrefix := ReferenceActivePhysicalHorizon.run_allActiveAtEnd initial rows selected rewards
    start resetCount (by omega) hmode
  let resetMode := Eq.mp
    (congrArg (fun state => ReferenceActivePhysicalHorizon.allActiveAtStart state
      (start + resetCount)) hresetState).symm resetModePrefix
  let suffixRun := ReferenceActivePhysicalHorizon.run resetState rows selected rewards
    (start + resetCount) (count - resetCount) (by omega) resetMode
  have hsplit := run_suffix_records initial rows selected rewards start resetCount
    (count - resetCount) (by omega) hmode
  have hrecords : suffixRun.records = prefixRun.records.drop resetCount := by
    cases hresetState
    simpa [suffixRun, resetMode, resetModePrefix, resetPrefix, prefixRun,
      Nat.add_sub_of_le hresetCount] using hsplit.1
  have hfinal : suffixRun.finalState = prefixRun.finalState := by
    cases hresetState
    simpa [suffixRun, resetMode, resetModePrefix, resetPrefix, prefixRun,
      Nat.add_sub_of_le hresetCount] using hsplit.2
  have hcurrentOrdinary : prefixRun.finalState.coordinator ≠ .dagger := by
    rw [← hcurrentState]
    exact hordinary
  have hfinalOrdinary : suffixRun.finalState.coordinator ≠ .dagger := by
    rw [hfinal]
    exact hcurrentOrdinary
  have hfinalInvariant :
      ReferenceUpDecoderBankInvariant.upBankInvariant suffixRun.finalState := by
    rw [hfinal, ← hcurrentState]
    exact hinvariant
  have hrecordsInvariant : ∀ record, record ∈ suffixRun.records →
      ReferenceUpDecoderBankInvariant.upBankInvariant record.input.state := by
    intro record hrecord
    exact ReferenceUpDecoderBankInvariant.run_record_input_upBankInvariant
      resetState rows selected rewards (start + resetCount) (count - resetCount) (by omega)
      resetMode hresetInvariant record hrecord
  have hcalendar := ReferenceActivePhysicalHorizon.run_time_values resetState rows selected rewards
    (start + resetCount) (count - resetCount) (by omega) resetMode
  have hcompleted := connected_up_completed_unchanged suffixRun.connected hrecordsInvariant
    hfinalOrdinary i (by
      intro record hrecord
      apply hno record
      rw [hrecords] at hrecord
      exact hrecord)
  have hinvariant' := hfinalInvariant
  change ReferenceUpDecoderBankInvariant.coordinatorBankInvariant
    suffixRun.finalState.coordinator suffixRun.finalState.upDecoderBank at hinvariant'
  have hfresh := Bandits.Support.ReferenceGeneratedUpBatchCalendar.connected_up_fresh_interval_pending
    suffixRun.records (start + resetCount) (count - resetCount) hcalendar suffixRun.connected
    hrecordsInvariant hfinalOrdinary i hresetPending hcompleted
  have hroots := ReferenceActivePhysicalHorizon.run_record_inputs resetState rows selected rewards
    (start + resetCount) (count - resetCount) (by omega) resetMode
  exact ⟨hrecords, hfinal, suffixRun.connected, hcalendar, hrecordsInvariant,
    (by
      intro record hrecord
      apply hno record
      rw [hrecords] at hrecord
      exact hrecord), hcompleted, hfresh.1, (hinvariant'.1 i).1,
    (by intro record hrecord; exact hroots record hrecord)⟩

private theorem actual_run_up_canonical_reset
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hinitial : ReferenceUpDecoderBankInvariant.upBankInvariant initial)
    (hinitialEmpty : ∀ i : Fin (p.m - 1),
      (initial.upDecoderBank i).pending = [])
    (hfinalOrdinary : (ReferenceActivePhysicalHorizon.run initial rows selected rewards
      start count hspan hmode).finalState.coordinator ≠ .dagger)
    (i : Fin (p.m - 1)) :
    ∃ resetCount resetState,
      resetCount ≤ count ∧
      (∃ hresetSpan : start + resetCount ≤ p.T,
      resetState = (ReferenceActivePhysicalHorizon.run initial rows selected rewards start
        resetCount hresetSpan hmode).finalState ∧
      (resetState.upDecoderBank i).pending = [] ∧
      ReferenceUpDecoderBankInvariant.upBankInvariant resetState ∧
      (∀ record, record ∈
        (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count
          hspan hmode).records.drop resetCount → ¬ actualUpQuotaCompletion i record) ∧
      ((resetCount = 0 ∧ resetState = initial) ∨
        ∃ j : Fin count,
          ∃ diagnostic : ReferenceActivePhysicalStep.UpDiagnostic p rate,
            let marker := (ReferenceActivePhysicalHorizon.run initial rows selected rewards
              start count hspan hmode).records[j.val]'(by
                have h := ReferenceActivePhysicalHorizon.run_record_count initial rows selected
                  rewards start count hspan hmode
                omega)
            marker.output.coordinator.up = some diagnostic ∧
            diagnostic.input.selectedFollower = i ∧
            ReferenceGeneratedAffineHashHalf.directionPositive 1 marker.input = true ∧
            (marker.input.state.upDecoderBank i).pending.length + 1 =
              AffineBatchDecoder.quota p ∧
            (∀ l : Fin count,
              (∃ earlier : ReferenceActivePhysicalStep.UpDiagnostic p rate,
                let earlierRecord :=
                  (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count
                    hspan hmode).records[l.val]'(by
                      have h := ReferenceActivePhysicalHorizon.run_record_count initial rows selected
                        rewards start count hspan hmode
                      omega)
                earlierRecord.output.coordinator.up = some earlier ∧
                earlier.input.selectedFollower = i ∧
                ReferenceGeneratedAffineHashHalf.directionPositive 1 earlierRecord.input = true ∧
                (earlierRecord.input.state.upDecoderBank i).pending.length + 1 =
                  AffineBatchDecoder.quota p) → l.val ≤ j.val) ∧
            resetCount = j.val + 1 ∧
            resetState = marker.output.next ∧
            marker.output.next.coordinator ≠ .dagger ∧
            ReferenceUpDecoderBankInvariant.upBankInvariant marker.input.state ∧
            (marker.output.next.upDecoderBank i).completed =
              (marker.input.state.upDecoderBank i).completed ++
                [(marker.input.state.upDecoderBank i).pending ++
                  [AffineBatchDecoder.entry p
                    (ReferenceCoordinatorUpDecoderReplay.constantInputTrace diagnostic.input)
                    diagnostic.input.time]])) := by
  classical
  let whole := ReferenceActivePhysicalHorizon.run initial rows selected rewards start count
    hspan hmode
  have hcount := ReferenceActivePhysicalHorizon.run_record_count initial rows selected rewards
    start count hspan hmode
  have hlength : whole.records.length = count := by simpa [whole] using hcount
  have hcountLength : count = whole.records.length := hlength.symm
  have hrunInvariant := ReferenceUpDecoderBankInvariant.run_upBankInvariant initial rows selected
    rewards start count hspan hmode hinitial
  have hoffsetBound : count ≤ whole.records.length := by omega
  let offsets := actualUpQuotaOffsets whole.records i count hoffsetBound
  by_cases hempty : offsets = ∅
  · have hnone := actualUpQuotaCompletion_none_of_empty_after_drop whole.records i count
      hcountLength hempty 0 (by omega)
    refine ⟨0, initial, by omega,
      ⟨by omega, ?_, hinitialEmpty i, hinitial, hnone, Or.inl ?_⟩⟩
    · exact (ReferenceActivePhysicalHorizon.run_zero_final initial rows selected rewards start
        (by omega) hmode).symm
    · simp
  · have hnonempty : offsets.Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
    let j : Fin count := offsets.max' hnonempty
    have hjmem : j ∈ offsets := Finset.max'_mem offsets hnonempty
    have hjcompletion : actualUpQuotaCompletion i (whole.records[j.val]'(by omega)) := by
      change actualUpQuotaCompletion i (whole.records[j.val]'(by omega))
      exact (Finset.mem_filter.mp hjmem).2
    have hmax : ∀ l : Fin count,
        actualUpQuotaCompletion i (whole.records[l.val]'(by omega)) → l.val ≤ j.val := by
      intro l hcompletion
      have hlmem : l ∈ offsets := by
        simp [offsets, actualUpQuotaOffsets, hcompletion]
      have hle : l ≤ j := Finset.le_max' offsets l hlmem
      exact Fin.le_iff_val_le_val.mp hle
    let marker := whole.records[j.val]'(by omega)
    rcases hjcompletion with ⟨diagnostic, hdiagnostic, hselected, hpositive, hquota⟩
    have hjRecord : j.val < whole.records.length := by omega
    have hmarkerMem : marker ∈ whole.records :=
      List.mem_iff_getElem.mpr ⟨j.val, hjRecord, rfl⟩
    have hmarkerOrdinary : marker.output.next.coordinator ≠ .dagger :=
      connected_record_successors_ordinary whole.connected hfinalOrdinary marker hmarkerMem
    have hmarkerInvariant :
        ReferenceUpDecoderBankInvariant.upBankInvariant marker.input.state :=
      ReferenceUpDecoderBankInvariant.run_record_input_upBankInvariant initial rows selected
        rewards start count hspan hmode hinitial marker hmarkerMem
    have hsurvivingCompletion :=
      Bandits.Support.ReferenceGeneratedUpCallBankReplay.record_up_surviving_quota_completion
        marker diagnostic hdiagnostic hmarkerInvariant hmarkerOrdinary i hselected hpositive hquota
    let resetCount := j.val + 1
    let resetState := marker.output.next
    have hjlt : j.val < count := j.isLt
    have hmarkerPrefix := run_record_input_state_eq_prefix initial rows selected rewards start
      count hspan hmode j.val hjlt
    have hresetSpan : start + resetCount ≤ p.T := by omega
    have hresetState : resetState =
        (ReferenceActivePhysicalHorizon.run initial rows selected rewards start resetCount
          hresetSpan hmode).finalState := by
      simpa [resetState, resetCount, marker, whole] using hmarkerPrefix.2.2
    have hresetPending : (resetState.upDecoderBank i).pending = [] := by
      simpa [resetState] using hsurvivingCompletion.2.1
    have hresetInvariant : ReferenceUpDecoderBankInvariant.upBankInvariant resetState := by
      rw [hresetState]
      exact ReferenceUpDecoderBankInvariant.run_upBankInvariant initial rows selected rewards
        start resetCount hresetSpan hmode hinitial
    have hno := actualUpQuotaCompletion_none_after_max whole.records i count hcountLength j hmax
    refine ⟨resetCount, resetState, by omega,
      ⟨hresetSpan, hresetState, hresetPending, hresetInvariant, hno, Or.inr ?_⟩⟩
    refine ⟨j, diagnostic, hdiagnostic, hselected, hpositive, hquota, ?_, rfl, rfl,
      hmarkerOrdinary, hmarkerInvariant, ?_⟩
    · intro l hearlier
      exact hmax l (by
        rcases hearlier with ⟨earlier, hEarlierDiag, hEarlierSelected, hEarlierPositive,
          hEarlierQuota⟩
        exact ⟨earlier, hEarlierDiag, hEarlierSelected, hEarlierPositive, hEarlierQuota⟩)
    · exact hsurvivingCompletion.2.2

/-- Arbitrary-count version of C's actual-call producer.  The same generated
launch fibre and whole physical inputs are used for every `count`; the call
is located in the actual run, and its incoming bank history is derived from
that run's prefix. -/
theorem generated_up_actual_call_prefix
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T)
    (s : ℕ) (hs : s ≤ t.val) (control0 : TimeControl p)
    (x : ReferenceRetainedBoundaryMeasurability.RetainedLaunchStart
      rate rewards C_star C_h q t s hs control0)
    (control : TimeControl p) (count : ℕ) (hcount : count ≤ p.T - s) :
    let fields := Bandits.Support.ReferenceGeneratedUpBatchCalendar.retained_launch_start_fields
      rate rewards C_star C_h q t s hs control0 x
    let hstart := (ReferenceInitializationControlRemainder.launchStartRemainderEvent_control_independent
      rate rewards C_star C_h q t s x.1 fields.1 control0 control).mp fields.2
    let source := ReferenceGeneratedActivePrefixFactor.splitSource q t control x.1
    let active := ReferenceGeneratedActivePrefixFactor.generatedActiveSeed
      rate rewards C_star C_h q t control x.1 fields.1 s hs hstart
    let hmode := (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
      rate rewards C_star C_h q t control x.1 fields.1 s hs hstart).2.1
    let rows := source.1.2
    let selected := ActualInitializationPhysicalStep.selectedRowIndex p source
    let fullRun := ReferenceActivePhysicalHorizon.run active rows selected rewards s count
      (by omega) hmode
    ∀ (k : Fin fullRun.records.length)
      (d : ReferenceActivePhysicalStep.UpDiagnostic p rate),
      let record := fullRun.records[k.val]'k.isLt
      (hd : record.output.coordinator.up = some d) →
      record.input.state =
          (ReferenceActivePhysicalHorizon.run active rows selected rewards s k.val (by
            have hc := ReferenceActivePhysicalHorizon.run_record_count active rows selected rewards
              s count (by omega) hmode
            have hkFull : k.val < fullRun.records.length := k.isLt
            have hc' : fullRun.records.length = count := by
              simpa [fullRun] using hc
            have _hk : k.val < count := Nat.lt_of_lt_of_eq hkFull hc'
            omega) hmode).finalState ∧
        (ReferenceActivePhysicalHorizon.run active rows selected rewards s k.val (by
            have hc := ReferenceActivePhysicalHorizon.run_record_count active rows selected rewards
              s count (by omega) hmode
            have hkFull : k.val < fullRun.records.length := k.isLt
            have hc' : fullRun.records.length = count := by
              simpa [fullRun] using hc
            have _hk : k.val < count := Nat.lt_of_lt_of_eq hkFull hc'
            omega) hmode).records = fullRun.records.take k.val ∧
        record.input.rows = rows ∧ record.input.selected = selected ∧
          record.input.rewards = rewards ∧ record.input.time.val = s + k.val ∧
        record.input.state.coordinator ≠ .dagger ∧
        ReferenceUpDecoderBankInvariant.upBankInvariant record.input.state ∧
        (∀ i : Fin (p.m - 1),
          AffineBatchDecoder.collected (record.input.state.upDecoderBank i) =
              ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries
                (fullRun.records.take k.val) i ∧
            (ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries
                (fullRun.records.take k.val) i).length =
              (record.input.state.upDecoderBank i).completed.length * AffineBatchDecoder.quota p +
                (record.input.state.upDecoderBank i).pending.length ∧
            (record.input.state.upDecoderBank i).completed.flatten =
              (ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries
                (fullRun.records.take k.val) i).take
                ((record.input.state.upDecoderBank i).completed.length * AffineBatchDecoder.quota p) ∧
            (record.input.state.upDecoderBank i).pending =
              (ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries
                (fullRun.records.take k.val) i).drop
                ((record.input.state.upDecoderBank i).completed.length * AffineBatchDecoder.quota p)) ∧
        (∃ ledger,
          ReferenceCoordinatorUpPhysicalCall.siteLedger? (x := record.input) = some ledger ∧
          CoordinatorUpReception.receptionInputCheck
            (ReferenceCoordinatorUpPhysicalCall.actualUpInput record.input ledger) = true ∧
          d.input = ReferenceCoordinatorUpPhysicalCall.actualUpInput record.input ledger ∧
          d.decoderAfter = (CoordinatorUpReception.decoderTransition d.input).1 ∧
          d.raw = (CoordinatorUpReception.decoderTransition d.input).2 ∧
          d.parsed = ReferenceUpReception.rawParsedOutput rate d.input ∧
          d.locallyAccepted = ReferenceUpReception.rawParsedLocalAcceptance rate d.input) ∧
        ((∃ ledger,
            (ReferenceActivePhysicalStep.receiveUp
              (ReferenceActivePhysicalStep.prepare record.input) ledger).result = .invalid ∧
            record.output.next.upDecoderBank = record.input.state.upDecoderBank) ∨
          ∃ ledger out,
            ((ReferenceActivePhysicalStep.receiveUp
                (ReferenceActivePhysicalStep.prepare record.input) ledger).result = .success out ∨
              (ReferenceActivePhysicalStep.receiveUp
                (ReferenceActivePhysicalStep.prepare record.input) ledger).result = .rejected out) ∧
            out.2 = CoordinatorUpReception.decoderBankAfter d.input ∧
            record.output.next.upDecoderBank = out.2) ∧
        (record.output.next.coordinator ≠ .dagger →
          record.output.next.upDecoderBank = CoordinatorUpReception.decoderBankAfter d.input ∧
            ∀ i : Fin (p.m - 1),
              d.input.selectedFollower = i →
              ReferenceGeneratedAffineHashHalf.directionPositive 1 record.input = true →
              (record.input.state.upDecoderBank i).pending.length + 1 =
                AffineBatchDecoder.quota p →
              record.output.next.upDecoderBank i = d.decoderAfter ∧
                (record.output.next.upDecoderBank i).pending = [] ∧
                (record.output.next.upDecoderBank i).completed =
                  (record.input.state.upDecoderBank i).completed ++
                    [(record.input.state.upDecoderBank i).pending ++
                      [AffineBatchDecoder.entry p
                        (ReferenceCoordinatorUpDecoderReplay.constantInputTrace d.input)
                        d.input.time]]) := by
  dsimp only
  intro k d hd
  let fields := Bandits.Support.ReferenceGeneratedUpBatchCalendar.retained_launch_start_fields
    rate rewards C_star C_h q t s hs control0 x
  let hstart := (ReferenceInitializationControlRemainder.launchStartRemainderEvent_control_independent
    rate rewards C_star C_h q t s x.1 fields.1 control0 control).mp fields.2
  let source := ReferenceGeneratedActivePrefixFactor.splitSource q t control x.1
  let active := ReferenceGeneratedActivePrefixFactor.generatedActiveSeed
    rate rewards C_star C_h q t control x.1 fields.1 s hs hstart
  let hmode := (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
    rate rewards C_star C_h q t control x.1 fields.1 s hs hstart).2.1
  let rows := source.1.2
  let selected := ActualInitializationPhysicalStep.selectedRowIndex p source
  let fullRun := ReferenceActivePhysicalHorizon.run active rows selected rewards s count
    (by omega) hmode
  let record := fullRun.records[k.val]'k.isLt
  have hcount := ReferenceActivePhysicalHorizon.run_record_count active rows selected rewards s count
    (by omega) hmode
  have hcount' : fullRun.records.length = count := by simpa [fullRun] using hcount
  have hkFull : k.val < fullRun.records.length := k.isLt
  have hk : k.val < count := Nat.lt_of_lt_of_eq hkFull hcount'
  have hkSpan : k.val ≤ p.T - s := by omega
  obtain ⟨hstate, hrecords, _⟩ := run_record_input_state_eq_prefix active rows selected rewards s count
    (by omega) hmode k.val hk
  have hmem : record ∈ fullRun.records := List.mem_iff_getElem.mpr ⟨k.val, k.isLt, rfl⟩
  obtain ⟨hrows, hselected, hrewards⟩ := ReferenceActivePhysicalHorizon.run_record_inputs
    active rows selected rewards s count (by omega) hmode record hmem
  have htimes := ReferenceActivePhysicalHorizon.run_time_values active rows selected rewards s
    count (by omega) hmode
  have hgetTimes := congrArg (fun times : List ℕ => times[k.val]?) htimes
  have hrecordGet : fullRun.records[k.val]? = some record := by simp [record]
  have hrecordTime :
      (fullRun.records.map fun current => current.input.time.val)[k.val]? =
        some record.input.time.val := by
    simp only [List.getElem?_map, hrecordGet, Option.map_some]
  have hkCalendar : k.val < (ReferenceActivePhysicalHorizon.calendar s count).length := by
    simpa [ReferenceActivePhysicalHorizon.calendar] using hk
  have hcalendar : (ReferenceActivePhysicalHorizon.calendar s count)[k.val] = s + k.val := by
    change (List.range' s count)[k.val] = s + k.val
    exact List.getElem_range'_1 k.val hkCalendar
  have hcalendarTime : (ReferenceActivePhysicalHorizon.calendar s count)[k.val]? =
      some (s + k.val) := by
    rw [List.getElem?_eq_getElem hkCalendar, hcalendar]
  have htime : record.input.time.val = s + k.val := by
    rw [hrecordTime, hcalendarTime] at hgetTimes
    exact Option.some.inj hgetTimes
  obtain ⟨ledger, hsite, hcheck, hinput, hafter, hraw, hparsed, hlocal, _⟩ :=
    Bandits.Support.ReferenceGeneratedUpBatchCalendar.record_up_executed_fields record d hd
  have hordinary : record.input.state.coordinator ≠ .dagger := by
    intro hdagger
    have hsiteNone : ReferenceCoordinatorUpPhysicalCall.siteLedger?
        (x := record.input) = none := by
      have hprepared : (ReferenceActivePhysicalStep.prepare record.input).coordinator = .dagger := by
        simpa [ReferenceActivePhysicalStep.prepare] using
          ReferenceActivePhysicalStep.dispatch_dagger record.input hdagger
      simp [ReferenceCoordinatorUpPhysicalCall.siteLedger?, hprepared]
    rw [hsiteNone] at hsite
    cases hsite
  have hprefixOrdinary :
      (ReferenceActivePhysicalHorizon.run active rows selected rewards s k.val (by omega) hmode).finalState.coordinator ≠ ReferenceActivePhysicalStep.CoordinatorConfiguration.dagger := by
    rw [← hstate]
    exact hordinary
  have hgeneratedInvariantAndChronology :=
    Bandits.Support.ReferenceGeneratedUpBatchCalendar.generated_up_prefix_bank_chronology
      rate rewards C_star C_h q t s hs control0 x control k.val hkSpan
        ⟨0, by have hm := p.two_le_m; omega⟩
  have hgeneratedInvariant :
      ReferenceUpDecoderBankInvariant.upBankInvariant
        (ReferenceActivePhysicalHorizon.run active rows selected rewards s k.val (by omega)
          hmode).finalState := hgeneratedInvariantAndChronology.1
  have hrecordInvariant : ReferenceUpDecoderBankInvariant.upBankInvariant record.input.state := by
    rw [hstate]
    exact hgeneratedInvariant
  have hchannels : ∀ i : Fin (p.m - 1),
      AffineBatchDecoder.collected (record.input.state.upDecoderBank i) =
          ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries
            (fullRun.records.take k.val) i ∧
        (ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries
            (fullRun.records.take k.val) i).length =
          (record.input.state.upDecoderBank i).completed.length * AffineBatchDecoder.quota p +
            (record.input.state.upDecoderBank i).pending.length ∧
        (record.input.state.upDecoderBank i).completed.flatten =
          (ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries
            (fullRun.records.take k.val) i).take
            ((record.input.state.upDecoderBank i).completed.length * AffineBatchDecoder.quota p) ∧
        (record.input.state.upDecoderBank i).pending =
          (ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries
            (fullRun.records.take k.val) i).drop
            ((record.input.state.upDecoderBank i).completed.length * AffineBatchDecoder.quota p) := by
    intro i
    have hi := Bandits.Support.ReferenceGeneratedUpBatchCalendar.generated_up_prefix_bank_chronology
      rate rewards C_star C_h q t s hs control0 x control k.val hkSpan i
    have hbank := hi.2 hprefixOrdinary
    rw [← hstate, hrecords] at hbank
    exact hbank
  have hcommit := Bandits.Support.ReferenceGeneratedUpBatchCalendar.record_up_physical_commit_cases
    record d hd hrecordInvariant
  refine ⟨hstate, hrecords, hrows, hselected, hrewards, htime, hordinary,
    hrecordInvariant, hchannels, ?_, ?_, ?_⟩
  · exact ⟨ledger, hsite, hcheck, hinput, hafter, hraw, hparsed, hlocal⟩
  · obtain ⟨commitLedger, hsiteCommit, hcheckCommit, hinputCommit, hafterCommit, hcases⟩ := hcommit
    rcases hcases with hinvalid | ⟨out, hresult, hbank, hnext⟩
    · exact Or.inl ⟨commitLedger, hinvalid.1, hinvalid.2⟩
    · exact Or.inr ⟨commitLedger, out, hresult, hbank, hnext⟩
  · intro hsurvives
    have hsurvivingCommit :=
      Bandits.Support.ReferenceGeneratedUpCallBankReplay.record_up_surviving_commit
        record d hd hrecordInvariant hsurvives
    refine ⟨hsurvivingCommit.1, ?_⟩
    intro i hselectedDiagnostic hpositive hquota
    exact Bandits.Support.ReferenceGeneratedUpCallBankReplay.record_up_surviving_quota_completion
      record d hd hrecordInvariant hsurvives i hselectedDiagnostic hpositive hquota

/-- For an actual generated UP call, the last earlier decoded quota completion
on its selected channel canonically chooses the reset state. The following
physical suffix is the same `H.run` from that reset through the current
pre-call endpoint, and the current decoder completion joins that exact suffix
even when the current physical successor is rejected. Apply
`generated_up_actual_call_prefix` at the same telescope to retain the actual
raw, parsed, local-acceptance, physical-branch, and surviving-commit fields. -/
theorem generated_up_actual_call_reset_interval
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T)
    (s : ℕ) (hs : s ≤ t.val) (control0 : TimeControl p)
    (x : ReferenceRetainedBoundaryMeasurability.RetainedLaunchStart
      rate rewards C_star C_h q t s hs control0)
    (control : TimeControl p) (count : ℕ) (hcount : count ≤ p.T - s) :
    let fields := Bandits.Support.ReferenceGeneratedUpBatchCalendar.retained_launch_start_fields
      rate rewards C_star C_h q t s hs control0 x
    let hstart := (ReferenceInitializationControlRemainder.launchStartRemainderEvent_control_independent
      rate rewards C_star C_h q t s x.1 fields.1 control0 control).mp fields.2
    let source := ReferenceGeneratedActivePrefixFactor.splitSource q t control x.1
    let active := ReferenceGeneratedActivePrefixFactor.generatedActiveSeed
      rate rewards C_star C_h q t control x.1 fields.1 s hs hstart
    let hmode := (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
      rate rewards C_star C_h q t control x.1 fields.1 s hs hstart).2.1
    let rows := source.1.2
    let selected := ActualInitializationPhysicalStep.selectedRowIndex p source
    let fullRun := ReferenceActivePhysicalHorizon.run active rows selected rewards s count
      (by omega) hmode
    ∀ (k : Fin fullRun.records.length)
      (d : ReferenceActivePhysicalStep.UpDiagnostic p rate),
      let record := fullRun.records[k.val]'k.isLt
      (hd : record.output.coordinator.up = some d) →
      have hfullLength : fullRun.records.length = count := by
        simpa [fullRun] using ReferenceActivePhysicalHorizon.run_record_count active rows selected
          rewards s count (by omega) hmode
      have hkcount : k.val < count := Nat.lt_of_lt_of_eq k.isLt hfullLength
      have hkspan : s + k.val ≤ p.T := by omega
      let prefixRun := ReferenceActivePhysicalHorizon.run active rows selected rewards s k.val
        hkspan hmode
      prefixRun.records = fullRun.records.take k.val ∧
      ∃ alpha resetCount resetState,
        alpha = s + resetCount ∧
        (∃ hresetCount : resetCount ≤ k.val, alpha ≤ s + k.val ∧
        ∃ hresetSpan : s + resetCount ≤ p.T,
          (∃ hresetState : resetState = (ReferenceActivePhysicalHorizon.run active rows selected
            rewards s resetCount hresetSpan hmode).finalState,
          (resetState.upDecoderBank d.input.selectedFollower).pending = [] ∧
          ReferenceUpDecoderBankInvariant.upBankInvariant resetState ∧
          resetState.coordinator ≠ .dagger ∧
          ((resetCount = 0 ∧ alpha = s ∧ resetState = active ∧
              (resetState.upDecoderBank d.input.selectedFollower).completed =
                (active.upDecoderBank d.input.selectedFollower).completed) ∨
            ∃ j : Fin k.val,
              ∃ diagnostic : ReferenceActivePhysicalStep.UpDiagnostic p rate,
                let marker := fullRun.records[j.val]'(by omega)
                alpha = s + j.val + 1 ∧
                marker.output.coordinator.up = some diagnostic ∧
                diagnostic.input.selectedFollower = d.input.selectedFollower ∧
                ReferenceGeneratedAffineHashHalf.directionPositive 1 marker.input = true ∧
                (marker.input.state.upDecoderBank d.input.selectedFollower).pending.length + 1 =
                  AffineBatchDecoder.quota p ∧
                (∀ l : Fin k.val,
                  (∃ earlier : ReferenceActivePhysicalStep.UpDiagnostic p rate,
                    let earlierRecord := prefixRun.records[l.val]'(by
                      have h := ReferenceActivePhysicalHorizon.run_record_count active rows selected
                        rewards s k.val hkspan hmode
                      have hprefLength : prefixRun.records.length = k.val := by
                        simpa [prefixRun] using h
                      omega)
                    earlierRecord.output.coordinator.up = some earlier ∧
                    earlier.input.selectedFollower = d.input.selectedFollower ∧
                    ReferenceGeneratedAffineHashHalf.directionPositive 1 earlierRecord.input = true ∧
                    (earlierRecord.input.state.upDecoderBank d.input.selectedFollower).pending.length +
                      1 = AffineBatchDecoder.quota p) → l.val ≤ j.val) ∧
                resetCount = j.val + 1 ∧ resetState = marker.output.next ∧
                marker.output.next.coordinator ≠ .dagger ∧
                ReferenceUpDecoderBankInvariant.upBankInvariant marker.input.state ∧
                (marker.output.next.upDecoderBank d.input.selectedFollower).completed =
                  (marker.input.state.upDecoderBank d.input.selectedFollower).completed ++
                    [(marker.input.state.upDecoderBank d.input.selectedFollower).pending ++
                      [AffineBatchDecoder.entry p
                        (ReferenceCoordinatorUpDecoderReplay.constantInputTrace diagnostic.input)
                        diagnostic.input.time]]) ∧
          (∀ marker, marker ∈ prefixRun.records.drop resetCount →
            ¬ ∃ diagnostic : ReferenceActivePhysicalStep.UpDiagnostic p rate,
              marker.output.coordinator.up = some diagnostic ∧
              diagnostic.input.selectedFollower = d.input.selectedFollower ∧
              ReferenceGeneratedAffineHashHalf.directionPositive 1 marker.input = true ∧
              (marker.input.state.upDecoderBank d.input.selectedFollower).pending.length + 1 =
                AffineBatchDecoder.quota p) ∧
          let resetMode := Eq.mp
            (congrArg (fun state => ReferenceActivePhysicalHorizon.allActiveAtStart state
              (s + resetCount)) hresetState).symm
            (ReferenceActivePhysicalHorizon.run_allActiveAtEnd active rows selected rewards
              s resetCount hresetSpan hmode)
          let suffixRun := ReferenceActivePhysicalHorizon.run resetState rows selected rewards
            (s + resetCount) (k.val - resetCount) (by omega) resetMode
          suffixRun.records = prefixRun.records.drop resetCount ∧
          suffixRun.finalState = record.input.state ∧
          ReferenceActivePhysicalHorizon.Connected resetState suffixRun.records suffixRun.finalState ∧
          suffixRun.records.map (fun prior => prior.input.time.val) =
            ReferenceActivePhysicalHorizon.calendar (s + resetCount) (k.val - resetCount) ∧
          (∀ prior, prior ∈ suffixRun.records →
            ReferenceUpDecoderBankInvariant.upBankInvariant prior.input.state) ∧
          (∀ prior, prior ∈ suffixRun.records →
            ¬ ∃ diagnostic : ReferenceActivePhysicalStep.UpDiagnostic p rate,
              prior.output.coordinator.up = some diagnostic ∧
              diagnostic.input.selectedFollower = d.input.selectedFollower ∧
              ReferenceGeneratedAffineHashHalf.directionPositive 1 prior.input = true ∧
              (prior.input.state.upDecoderBank d.input.selectedFollower).pending.length + 1 =
                AffineBatchDecoder.quota p) ∧
          (suffixRun.finalState.upDecoderBank d.input.selectedFollower).completed =
            (resetState.upDecoderBank d.input.selectedFollower).completed ∧
          (suffixRun.finalState.upDecoderBank d.input.selectedFollower).pending =
            ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries suffixRun.records
              d.input.selectedFollower ∧
          (suffixRun.finalState.upDecoderBank d.input.selectedFollower).pending.length <
            AffineBatchDecoder.quota p ∧
          (∀ prior, prior ∈ suffixRun.records →
            prior.input.rows = rows ∧ prior.input.selected = selected ∧
              prior.input.rewards = rewards) ∧
          (∀ hpositive : ReferenceGeneratedAffineHashHalf.directionPositive 1 record.input = true,
            (record.input.state.upDecoderBank d.input.selectedFollower).pending.length + 1 =
              AffineBatchDecoder.quota p →
            d.decoderAfter.pending = [] ∧
              d.decoderAfter.completed =
                (resetState.upDecoderBank d.input.selectedFollower).completed ++
                  [ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries suffixRun.records
                      d.input.selectedFollower ++
                    [AffineBatchDecoder.entry p
                      (ReferenceCoordinatorUpDecoderReplay.constantInputTrace d.input)
                      d.input.time]]))) := by
  dsimp only
  intro k d hd
  have hprefix := generated_up_actual_call_prefix rate rewards C_star C_h q t s hs control0 x
      control count hcount
  obtain ⟨hstate, hprefixRecords, _, _, _, _, hordinary, hinvariant, _⟩ := hprefix k d hd
  let fields := Bandits.Support.ReferenceGeneratedUpBatchCalendar.retained_launch_start_fields
    rate rewards C_star C_h q t s hs control0 x
  let hstart := (ReferenceInitializationControlRemainder.launchStartRemainderEvent_control_independent
    rate rewards C_star C_h q t s x.1 fields.1 control0 control).mp fields.2
  let source := ReferenceGeneratedActivePrefixFactor.splitSource q t control x.1
  let active := ReferenceGeneratedActivePrefixFactor.generatedActiveSeed
    rate rewards C_star C_h q t control x.1 fields.1 s hs hstart
  let hmode := (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
    rate rewards C_star C_h q t control x.1 fields.1 s hs hstart).2.1
  let rows := source.1.2
  let selected := ActualInitializationPhysicalStep.selectedRowIndex p source
  let fullRun := ReferenceActivePhysicalHorizon.run active rows selected rewards s count
    (by omega) hmode
  let record := fullRun.records[k.val]'k.isLt
  have hfullLength : fullRun.records.length = count := by
    simpa [fullRun] using ReferenceActivePhysicalHorizon.run_record_count active rows selected
      rewards s count (by omega) hmode
  have hkcount : k.val < count := Nat.lt_of_lt_of_eq k.isLt hfullLength
  have hkspan : s + k.val ≤ p.T := by omega
  let prefixRun := ReferenceActivePhysicalHorizon.run active rows selected rewards s k.val
    hkspan hmode
  have hprefixOrdinary : prefixRun.finalState.coordinator ≠ .dagger := by
    rw [← hstate]
    exact hordinary
  have hprefixInvariant :
      ReferenceUpDecoderBankInvariant.upBankInvariant prefixRun.finalState := by
    rw [← hstate]
    exact hinvariant
  have hinitial := Bandits.Support.ReferenceGeneratedUpBatchCalendar.generated_up_initial_bank_invariant
    rate rewards C_star C_h q t s hs control0 x control
  have hbankEmpty := Bandits.Support.ReferenceGeneratedUpBatchCalendar.generated_up_initial_bank_empty
    rate rewards C_star C_h q t s hs control0 x control
  have hinitialEmpty : ∀ i : Fin (p.m - 1), (active.upDecoderBank i).pending = [] := by
    intro i
    have hbank := congrFun hbankEmpty i
    rw [hbank]
    simp [CoordinatorUpReception.initialUpDecoderBank, AffineBatchDecoder.initial]
  obtain ⟨resetCount, resetState, hresetLe, ⟨hresetSpan, hresetState, hresetPending,
    hresetInvariant, hno, hbranch⟩⟩ := actual_run_up_canonical_reset active rows selected
      rewards s k.val (by omega) hmode hinitial hinitialEmpty hprefixOrdinary
      d.input.selectedFollower
  have hinitialOrdinary : active.coordinator ≠ .dagger := by
    intro hdagger
    exact hprefixOrdinary
      (ReferenceActivePhysicalHorizon.Connected.coordinator_dagger prefixRun.connected hdagger).1
  have hresetOrdinary : resetState.coordinator ≠ .dagger := by
    rcases hbranch with ⟨_, hstateZero⟩ |
      ⟨_, _, _, _, _, _, _, _, hstateReset, hmarkerOrdinary, _, _⟩
    · simpa [hstateZero] using hinitialOrdinary
    · simpa [hstateReset] using hmarkerOrdinary
  have htail := actual_run_up_reset_interval_tail active rows selected rewards s k.val
    hkspan hmode prefixRun.finalState rfl hprefixOrdinary hprefixInvariant d.input.selectedFollower
    resetCount hresetLe resetState hresetState hresetPending hresetInvariant hno
  dsimp only at htail
  rcases htail with ⟨hsuffixRecords, hfinal, hconnected, hcalendar, hsuffixInvariant,
    hsuffixNo, hcompleted, hpending, hpendingSmall, hroots⟩
  have hrecordPrefixState : record.input.state = prefixRun.finalState := hstate
  have hfinalRecord :
      (ReferenceActivePhysicalHorizon.run resetState rows selected rewards
        (s + resetCount) (k.val - resetCount) (by omega)
        (Eq.mp
          (congrArg (fun state => ReferenceActivePhysicalHorizon.allActiveAtStart state
            (s + resetCount)) hresetState).symm
          (ReferenceActivePhysicalHorizon.run_allActiveAtEnd active rows selected rewards
            s resetCount hresetSpan hmode))).finalState = record.input.state := by
    exact hfinal.trans hrecordPrefixState.symm
  have hrecordCompleted :
      (record.input.state.upDecoderBank d.input.selectedFollower).completed =
        (resetState.upDecoderBank d.input.selectedFollower).completed := by
    rw [← hfinalRecord]
    exact hcompleted
  have hrecordPending :
      (record.input.state.upDecoderBank d.input.selectedFollower).pending =
        ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries
          ((ReferenceActivePhysicalHorizon.run resetState rows selected rewards
            (s + resetCount) (k.val - resetCount) (by omega)
            (Eq.mp
              (congrArg (fun state => ReferenceActivePhysicalHorizon.allActiveAtStart state
                (s + resetCount)) hresetState).symm
              (ReferenceActivePhysicalHorizon.run_allActiveAtEnd active rows selected rewards
                s resetCount hresetSpan hmode))).records) d.input.selectedFollower := by
    rw [← hfinalRecord]
    exact hpending
  refine ⟨hprefixRecords, ?_⟩
  refine ⟨s + resetCount, resetCount, resetState, rfl,
    ⟨hresetLe, by omega, ⟨hresetSpan,
      ⟨hresetState, hresetPending, hresetInvariant, hresetOrdinary, ?_, ?_, ?_⟩⟩⟩⟩
  ·
    rcases hbranch with hempty | hcompletion
    · rcases hempty with ⟨hzero, hstateZero⟩
      subst resetCount
      subst resetState
      simp [active]
    · rcases hcompletion with ⟨j, diagnostic, hdiag, hselected, hpositive, hquota,
        hmax, hcountReset, hstateReset, hmarkerOrdinary, hmarkerInvariant, hcompletedMarker⟩
      have hjFull : j.val < fullRun.records.length := by omega
      have hmarkerEq : prefixRun.records[j.val]'(by
          have hprefLength := ReferenceActivePhysicalHorizon.run_record_count active rows selected
            rewards s k.val hkspan hmode
          have hprefLength' : prefixRun.records.length = k.val := by
            simpa [prefixRun] using hprefLength
          omega) = fullRun.records[j.val]'hjFull := by
        have hprefIndex : j.val < prefixRun.records.length := by
          have hprefLength := ReferenceActivePhysicalHorizon.run_record_count active rows selected
            rewards s k.val hkspan hmode
          have hprefLength' : prefixRun.records.length = k.val := by
            simpa [prefixRun] using hprefLength
          omega
        have hprefixGet := List.getElem?_eq_getElem hprefIndex
        have hfullGet := List.getElem?_eq_getElem hjFull
        have hget : prefixRun.records[j.val]? = (fullRun.records.take k.val)[j.val]? :=
          congrArg (fun records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p)
            (rate := rate)) => records[j.val]?) hprefixRecords
        have htakeGet : (fullRun.records.take k.val)[j.val]? = fullRun.records[j.val]? := by
          simp [List.getElem?_take, j.isLt]
        have hgetFinal := hget.trans htakeGet
        rw [hprefixGet, hfullGet] at hgetFinal
        exact Option.some.inj hgetFinal
      have hdiag' : (fullRun.records[j.val]'hjFull).output.coordinator.up = some diagnostic := by
        rw [← hmarkerEq]
        exact hdiag
      have hpositive' : ReferenceGeneratedAffineHashHalf.directionPositive 1
          (fullRun.records[j.val]'hjFull).input = true := by
        rw [← hmarkerEq]
        exact hpositive
      have hquota' :
          ((fullRun.records[j.val]'hjFull).input.state.upDecoderBank d.input.selectedFollower).pending.length + 1 =
            AffineBatchDecoder.quota p := by
        rw [← hmarkerEq]
        exact hquota
      have hstateReset' : resetState = (fullRun.records[j.val]'hjFull).output.next := by
        rw [← hmarkerEq]
        exact hstateReset
      have hmarkerOrdinary' :
          (fullRun.records[j.val]'hjFull).output.next.coordinator ≠ .dagger := by
        rw [← hmarkerEq]
        exact hmarkerOrdinary
      have hmarkerInvariant' : ReferenceUpDecoderBankInvariant.upBankInvariant
          (fullRun.records[j.val]'hjFull).input.state := by
        rw [← hmarkerEq]
        exact hmarkerInvariant
      have hcompletedMarker' :
          ((fullRun.records[j.val]'hjFull).output.next.upDecoderBank d.input.selectedFollower).completed =
            ((fullRun.records[j.val]'hjFull).input.state.upDecoderBank d.input.selectedFollower).completed ++
              [((fullRun.records[j.val]'hjFull).input.state.upDecoderBank d.input.selectedFollower).pending ++
                [AffineBatchDecoder.entry p
                  (ReferenceCoordinatorUpDecoderReplay.constantInputTrace diagnostic.input)
                  diagnostic.input.time]] := by
        rw [← hmarkerEq]
        exact hcompletedMarker
      exact Or.inr ⟨j, diagnostic, by omega, hdiag', hselected, hpositive', hquota',
        hmax, hcountReset, hstateReset', hmarkerOrdinary', hmarkerInvariant', hcompletedMarker'⟩
  · intro marker hmem
    exact hno marker (by simpa [prefixRun] using hmem)
  · refine ⟨hsuffixRecords, hfinalRecord, hconnected, hcalendar, hsuffixInvariant,
      hsuffixNo, hcompleted, hpending, hpendingSmall, hroots, ?_⟩
    intro hpositive hquota
    have hjoin := Bandits.Support.ReferenceGeneratedUpBatchCalendar.record_up_quota_completion
      record d hd d.input.selectedFollower rfl hpositive hquota
    refine ⟨hjoin.1, ?_⟩
    rw [← hrecordCompleted, ← hrecordPending]
    exact hjoin.2.1

end Bandits.Support.ReferenceGeneratedUpResetCalendar

end
