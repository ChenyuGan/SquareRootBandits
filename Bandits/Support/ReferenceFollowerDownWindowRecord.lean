/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import Lean.Elab.Tactic.Omega
import Mathlib.Data.List.Intervals
public import Bandits.Support.ReferenceFollowerDownIntervalWindow

/-!
# Physical DOWN completed-window record bridge

Sources: `sources/zip4/manuscript/05_binary_transport.tex:36-53`,
`sources/zip4/manuscript/06_interruptions.tex:248-275,327-348`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:92-109,151-157`.

This module connects the accepted conditional two-batch interval geometry to
its actual maximal positive record and retained DOWN cut. Its count selector
remains an explicit conditional input; no word uniqueness or acceptance claim
is made.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.ActiveFollowerLifecycle
open Bandits.Support.ActiveFollowerDownAcceptance
open Bandits.Support.ReferenceFollowerDecoderChronology
open Bandits.Support.ReferenceFollowerDownDecoderReplay
open Bandits.Support.AffineBatchDecoder

namespace Bandits.Support.ReferenceFollowerDownWindowRecord

private abbrev Parameters := ConstructorDimensions.Parameters
private abbrev RateInput := ReferenceActivePhysicalStep.RateInput
private abbrev Record := ReferenceFollowerDownDecoderReplay.Record
private abbrev Call := ReferenceFollowerDownDecoderReplay.Call

private theorem filterMap_take_all_some
    {α β : Type} (f : α → Option β) (items : List α) (count : ℕ)
    (hall : ∀ item ∈ items, ∃ value, f item = some value) :
    List.filterMap f (items.take count) = (List.filterMap f items).take count := by
  induction count generalizing items with
  | zero => simp
  | succ count ih =>
      cases items with
      | nil => simp
      | cons head rest =>
          obtain ⟨value, hvalue⟩ := hall head (by simp)
          have htail : ∀ item ∈ rest, ∃ value, f item = some value := by
            intro item hitem
            exact hall item (by simp [hitem])
          simp only [List.take_succ_cons, List.filterMap_cons, hvalue]
          rw [ih rest htail]

private theorem connected_final_unique
    {p : Parameters} {rate : RateInput p}
    {initial leftFinal rightFinal : ReferenceActivePhysicalHorizon.State p rate}
    {records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))}
    (hleft : ReferenceActivePhysicalHorizon.Connected initial records leftFinal)
    (hright : ReferenceActivePhysicalHorizon.Connected initial records rightFinal) :
    leftFinal = rightFinal := by
  induction records generalizing initial leftFinal rightFinal with
  | nil =>
      simp only [ReferenceActivePhysicalHorizon.Connected] at hleft hright
      rw [hleft, hright]
  | cons record rest ih =>
      rcases hleft with ⟨_, hleft⟩
      rcases hright with ⟨_, hright⟩
      exact ih hleft hright

private theorem connected_take_to_input
    {p : Parameters} {rate : RateInput p}
    {initial final : ReferenceActivePhysicalHorizon.State p rate}
    {records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))}
    (chain : ReferenceActivePhysicalHorizon.Connected initial records final)
    (n : ℕ) (hn : n < records.length) :
    ReferenceActivePhysicalHorizon.Connected initial (records.take n) records[n].input.state := by
  induction records generalizing initial final n with
  | nil => simp at hn
  | cons record rest ih =>
      obtain ⟨hinput, hrest⟩ := chain
      cases n with
      | zero => exact hinput
      | succ n => exact ⟨hinput, ih hrest n (by simp at hn; omega)⟩

private theorem connected_output_ordinary
    {p : Parameters} {rate : RateInput p}
    {initial final : ReferenceActivePhysicalHorizon.State p rate}
    {records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))}
    (chain : ReferenceActivePhysicalHorizon.Connected initial records final)
    (i : Fin (p.m - 1)) (last : ReferencePrelaunchFollower.State p rate.eta)
    (lastMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hfinal : final.followers i = .ordinary last lastMemory)
    (n : ℕ) (hn : n < records.length) :
    ∃ next memory, records[n].output.next.followers i = .ordinary next memory := by
  induction records generalizing initial final n with
  | nil => simp at hn
  | cons record rest ih =>
      obtain ⟨_, hrest⟩ := chain
      cases n with
      | zero =>
          cases hnext : record.output.next.followers i with
          | ordinary next memory => exact ⟨next, memory, hnext⟩
          | dagger =>
              have hfinalDag := (hrest.follower_dagger i hnext).1
              rw [hfinalDag] at hfinal
              cases hfinal
      | succ n => exact ih hrest hfinal n (by simp at hn; omega)

private theorem finishFollower_ordinary_inversion_local
    {p : Parameters} {rate : RateInput p}
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (prepared : DeclaredFollowerLocalRound.PreparedRound p rate)
    (observation : ReferencePrelaunchFollower.Observation p)
    (next : ReferencePrelaunchFollower.State p rate.eta)
    (nextMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hout : (ReferenceActivePhysicalStep.finishFollower view prepared observation).configuration =
      .ordinary next nextMemory) :
    ∃ choice memory post,
      prepared.configuration = .ordinary choice memory ∧
      (ReferenceActivePhysicalStep.recordFollower view prepared.follower prepared.row
        prepared.activation prepared.time prepared.active prepared.arm observation choice).result =
          .ok post ∧
      DeclaredFollowerLocalRound.releaseAndFinish rate prepared.follower prepared.row prepared.time
        observation choice memory post = .ok (next, nextMemory) ∧
      (ReferenceActivePhysicalStep.finishFollower view prepared observation).downInput =
        (ReferenceActivePhysicalStep.recordFollower view prepared.follower prepared.row
          prepared.activation prepared.time prepared.active prepared.arm observation choice).downInput ∧
      (ReferenceActivePhysicalStep.finishFollower view prepared observation).down =
        (ReferenceActivePhysicalStep.recordFollower view prepared.follower prepared.row
          prepared.activation prepared.time prepared.active prepared.arm observation choice).down := by
  cases hc : prepared.configuration with
  | dagger => simp [ReferenceActivePhysicalStep.finishFollower, hc] at hout
  | ordinary choice memory =>
      cases hr : (ReferenceActivePhysicalStep.recordFollower view prepared.follower prepared.row
          prepared.activation prepared.time prepared.active prepared.arm observation choice).result with
      | error failure => simp [ReferenceActivePhysicalStep.finishFollower, hc, hr] at hout
      | ok post =>
          cases hf : DeclaredFollowerLocalRound.releaseAndFinish rate prepared.follower prepared.row
              prepared.time observation choice memory post with
          | error failure => simp [ReferenceActivePhysicalStep.finishFollower, hc, hr, hf] at hout
          | ok pair =>
              rcases pair with ⟨out, outMemory⟩
              simp only [ReferenceActivePhysicalStep.finishFollower, hc, hr, hf] at hout
              injection hout with houtState houtMemory
              subst out
              subst outMemory
              refine ⟨choice, memory, post, rfl, hr, hf, ?_, ?_⟩ <;>
                simp [ReferenceActivePhysicalStep.finishFollower, hc, hr, hf]

private theorem referenceDownCut_compared_of_consumed_success
    (p : Parameters) (rate : RateInput p)
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (time : Fin p.T) (observation : ReferencePrelaunchFollower.Observation p)
    (state post : ReferencePrelaunchFollower.State p rate.eta)
    (hselected : ActiveFollowerDownAcceptance.downSelected p i row time)
    (hstatus : state.status = .unoccupied)
    (hbatch : ReferenceFollowerDecoderChronology.downBatchWellFormed state.downBatch)
    (hout : DeclaredFollowerLocalRound.consumeDownResult rate
      (ReferenceDownReception.referenceDownCut p view i row time observation rate state).outcome =
        .ok post) :
    ActiveFollowerDownAcceptance.registerInputDomain p rate state ∧
    ActiveFollowerDownAcceptance.decoderInputDomain p state.downBatch ∧
    ActiveFollowerDownAcceptance.bufferInputDomain p state.buffer ∧
    (ReferenceDownReception.referenceDownCut p view i row time observation rate state).rawComparison ≠
      none := by
  classical
  have hregisters : ActiveFollowerDownAcceptance.registerInputDomain p rate state := by
    by_contra hbad
    have hcut : (ReferenceDownReception.referenceDownCut p view i row time observation rate state).outcome =
        .inputFailure state .registers := by
      simp [ReferenceDownReception.referenceDownCut, hselected, hstatus, hbad]
    rw [hcut, DeclaredFollowerLocalRound.consumeDownResult] at hout
    cases hout
  have hdecoder : ActiveFollowerDownAcceptance.decoderInputDomain p state.downBatch := by
    simpa [ReferenceFollowerDecoderChronology.downBatchWellFormed,
      ActiveFollowerDownAcceptance.decoderInputDomain] using hbatch
  have hbuffer : ActiveFollowerDownAcceptance.bufferInputDomain p state.buffer := by
    by_contra hbad
    have hcut : (ReferenceDownReception.referenceDownCut p view i row time observation rate state).outcome =
        .inputFailure state .sparseBuffer := by
      simp [ReferenceDownReception.referenceDownCut, hselected, hstatus,
        hregisters, hdecoder, hbad]
    rw [hcut, DeclaredFollowerLocalRound.consumeDownResult] at hout
    cases hout
  let decoded := ActiveFollowerDownAcceptance.currentDecodeStep p i row time observation rate state
  refine ⟨hregisters, hdecoder, hbuffer, ?_⟩
  by_cases hmatches : decoded.2 =
      ReferenceDownReception.expectedDownFlatWord view i row time
  · simp [ReferenceDownReception.referenceDownCut, hselected, hstatus,
      hregisters, hdecoder, hbuffer, decoded, hmatches]
  · simp [ReferenceDownReception.referenceDownCut, hselected, hstatus,
      hregisters, hdecoder, hbuffer, decoded, hmatches]

/-- Locate the last positive of the conditional second batch at its real
physical record, replay that record's prefix bank, and recover the retained
constructor cut. The sole extra premise is the local interval observation
count selector. -/
def intervalDownCompletedWindowRecordResult
    (p : ConstructorDimensions.Parameters)
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start a b : ℕ) (hab : a ≤ b) (hspan : start + b ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (i : Fin (p.m - 1)) : Prop :=
    ∃ stateA : ReferencePrelaunchFollower.State p rate.eta,
      ∃ memoryA : ActiveFollowerLifecycle.LocalMemory p,
        (ReferenceActivePhysicalHorizon.run initial rows selected rewards
          start a (by omega) hmode).finalState.followers i = .ordinary stateA memoryA ∧
        (let Rb := ReferenceActivePhysicalHorizon.run initial rows selected rewards
          start b hspan hmode
         let I := Rb.records.drop a
         let calls := ReferenceFollowerDownDecoderReplay.actualDownCalls i I
         let positives := ReferenceFollowerDownDecoderReplay.actualDownPositives i I
         let window := positives.drop
           (AffineBatchDecoder.quota p - stateA.downBatch.pending.length)
         (positives.length = AffineBatchDecoder.quota p - stateA.downBatch.pending.length +
           AffineBatchDecoder.quota p) →
         ∃ (index : ℕ) (call : ReferenceFollowerDownDecoderReplay.Call p)
           (entry : AffineBatchDecoder.Entry p.T
             (AffineBatchDecoder.width p))
           (record : ReferenceFollowerDownDecoderReplay.Record p rate)
           (choice : ReferencePrelaunchFollower.State p rate.eta)
           (choiceMemory : ActiveFollowerLifecycle.LocalMemory p)
           (logged : ReferencePrelaunchFollower.State p rate.eta)
           (postRecord next : ReferencePrelaunchFollower.State p rate.eta)
           (nextMemory : ActiveFollowerLifecycle.LocalMemory p),
           index < calls.length ∧
           calls = calls.take index ++ call :: calls.drop (index + 1) ∧
           entry ∈ window ∧
           (∀ other ∈ window, other.time.val ≤ entry.time.val) ∧
           record ∈ I ∧
           ReferenceFollowerDownDecoderReplay.actualDownCall i record = some call ∧
           call.1 = record.input.time ∧
           ReferenceFollowerDownDecoderReplay.preparedChoiceConfiguration record i =
             .ordinary choice choiceMemory ∧
           choice.status = .unoccupied ∧
           ActiveFollowerDownAcceptance.downSelected p i
             (ReferenceFollowerDownDecoderReplay.preparedChoiceRow record i)
             (ReferenceFollowerDownDecoderReplay.preparedChoiceTime record i) ∧
           0 < (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i).val.val ∧
           ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i =
             record.output.preparation.feedback.observations
               (Bandits.Support.PublicDiscreteDraws.followerPlayer p.two_le_m i) ∧
           (ReferenceActivePhysicalStep.finishFollower
             record.output.preparation.coordinator.downView
             (record.output.preparation.followers.followers i)
             (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i)).configuration =
               .ordinary next nextMemory ∧
           record.output.next.followers i = .ordinary next nextMemory ∧
           (ReferenceActivePhysicalStep.recordFollower
             record.output.preparation.coordinator.downView i
             (ReferenceFollowerDownDecoderReplay.preparedChoiceRow record i)
             (record.output.preparation.followers.followers i).activation
             (ReferenceFollowerDownDecoderReplay.preparedChoiceTime record i)
             (record.output.preparation.followers.followers i).active
             (record.output.preparation.followers.followers i).arm
             (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i) choice).result =
               .ok postRecord ∧
           DeclaredFollowerLocalRound.releaseAndFinish rate i
             (ReferenceFollowerDownDecoderReplay.preparedChoiceRow record i)
             (ReferenceFollowerDownDecoderReplay.preparedChoiceTime record i)
             (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i)
             choice choiceMemory postRecord = .ok (next, nextMemory) ∧
           ActiveFollowerLogging.checkedLogging i
             (ReferenceFollowerDownDecoderReplay.preparedChoiceRow record i)
             (record.output.preparation.followers.followers i).activation
             (ReferenceFollowerDownDecoderReplay.preparedChoiceTime record i)
             ((record.output.preparation.followers.followers i).arm,
               ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i) choice =
                 .ok logged ∧
           ActiveFollowerLifecycle.localBufferValid choice ∧
           ActiveFollowerLifecycle.localBufferValid logged ∧
           logged.downBatch = choice.downBatch ∧
           (record.output.preparation.observeFollower i).downInput = some logged ∧
           (record.output.preparation.observeFollower i).down =
             some (ReferenceDownReception.referenceDownCut p
               record.output.preparation.coordinator.downView i
               (ReferenceFollowerDownDecoderReplay.preparedChoiceRow record i)
               (ReferenceFollowerDownDecoderReplay.preparedChoiceTime record i)
               (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i) rate logged) ∧
           ActiveFollowerDownAcceptance.registerInputDomain p rate logged ∧
           ActiveFollowerDownAcceptance.decoderInputDomain p logged.downBatch ∧
           ActiveFollowerDownAcceptance.bufferInputDomain p logged.buffer ∧
           (ReferenceDownReception.referenceDownCut p
             record.output.preparation.coordinator.downView i
             (ReferenceFollowerDownDecoderReplay.preparedChoiceRow record i)
             (ReferenceFollowerDownDecoderReplay.preparedChoiceTime record i)
             (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i) rate logged).rawComparison ≠ none ∧
           (ReferenceDownReception.referenceDownCut p
             record.output.preparation.coordinator.downView i
             (ReferenceFollowerDownDecoderReplay.preparedChoiceRow record i)
             (ReferenceFollowerDownDecoderReplay.preparedChoiceTime record i)
             (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i) rate logged).raw =
               AffineBatchDecoder.batchOutput window)

/-- Prove the result predicate from the accepted interval replay and the
physical run's actual maximal positive DOWN call. -/
theorem run_interval_down_completed_window_record
    (p : ConstructorDimensions.Parameters)
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start a b : ℕ) (hab : a ≤ b) (hspan : start + b ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hseed : ReferenceFollowerDecoderChronology.downBatchSeed initial start)
    (i : Fin (p.m - 1))
    (stateB : ReferencePrelaunchFollower.State p rate.eta)
    (memoryB : ActiveFollowerLifecycle.LocalMemory p)
    (hordinaryB :
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards
        start b hspan hmode).finalState.followers i = .ordinary stateB memoryB) : intervalDownCompletedWindowRecordResult p rate initial rows selected rewards start a b hab hspan hmode i := by
  let Ra := ReferenceActivePhysicalHorizon.run initial rows selected rewards start a (by omega) hmode
  let Rb := ReferenceActivePhysicalHorizon.run initial rows selected rewards start b hspan hmode
  let I := Rb.records.drop a
  let calls := ReferenceFollowerDownDecoderReplay.actualDownCalls i I
  let positives := ReferenceFollowerDownDecoderReplay.actualDownPositives i I
  obtain ⟨stateA, memoryA, hstateA, hfacts⟩ :=
    ReferenceFollowerDownIntervalWindow.run_interval_downBatch_replay
      p rate initial rows selected rewards start a b hab hspan hmode hseed i stateB memoryB
      hordinaryB
  rcases hfacts with ⟨hprefix, hcallPair, hcallCalendar, hbank, hcollected, hpending,
    hpendingTime, hpositivePair, hpositiveTime⟩
  obtain ⟨stateAWindow, memoryAWindow, hstateAWindow, hconditional⟩ :=
    ReferenceFollowerDownIntervalWindow.run_interval_down_two_batch_window
      p rate initial rows selected rewards start a b hab hspan hmode hseed i stateB memoryB
      hordinaryB
  have hstatePair := hstateAWindow.symm.trans hstateA
  injection hstatePair with hstateEq hmemoryEq
  subst stateAWindow
  subst memoryAWindow
  let window := positives.drop
    (AffineBatchDecoder.quota p - stateA.downBatch.pending.length)
  refine ⟨stateA, memoryA, hstateA, ?_⟩
  dsimp only
  intro hcount
  classical
  dsimp only at hconditional
  rcases hconditional hcount with ⟨_, _, _, _, _, _, ⟨trace, hcurrent, index, call, entry,
    hindex, hsplit, hentry, hentryTime, hlast, hcallEligible, hraw⟩⟩
  have hcallMem' : call ∈ ReferenceFollowerDownDecoderReplay.actualDownCalls i I := by
    rw [hsplit]
    simp
  have hcallMem : call ∈ calls := by simpa [calls] using hcallMem'
  obtain ⟨record, hrecord, hactual⟩ := List.mem_filterMap.mp hcallMem
  have hrecordB : record ∈ Rb.records := List.mem_of_mem_drop hrecord
  have hcorr := ReferenceFollowerDownDecoderReplay.run_downCall_calendar_correspondence
    initial rows selected rewards start b hspan hmode i stateB memoryB hordinaryB
  obtain ⟨choice, choiceMemory, hprepared, _⟩ := hcorr.2.2 record hrecordB
  have hcallEq : call = (ReferenceFollowerDownDecoderReplay.preparedChoiceTime record i,
      ActiveFollowerDownAcceptance.currentRoundInput p i
        (ReferenceFollowerDownDecoderReplay.preparedChoiceRow record i)
        (ReferenceFollowerDownDecoderReplay.preparedChoiceTime record i)
        (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i) rate choice) :=
    Option.some.inj (hactual.symm.trans
      (ReferenceFollowerDownDecoderReplay.actualDownCall_ordinary record i choice choiceMemory hprepared))
  have hcallTime : call.1 = record.input.time := by
    simpa only [ReferenceFollowerDownDecoderReplay.preparedChoiceTime_eq_recordTime] using
      congrArg Prod.fst hcallEq
  have hcallFirst := congrArg Prod.fst hcallEq
  have hcallSecond := congrArg Prod.snd hcallEq
  have hcallAt : calls[index]? = some call := by
    change (ReferenceFollowerDownDecoderReplay.actualDownCalls i I)[index]? = some call
    rw [hsplit, List.getElem?_append_right (by simp)]
    simp [Nat.min_eq_left (Nat.le_of_lt hindex)]
  have hintervalTime : call.1.val = start + a + index := by
    have hmap := congrArg (fun ts : List ℕ => ts[index]?) hcallCalendar
    have hleft : ((calls.map Prod.fst).map Fin.val)[index]? = some call.1.val := by
      simp [List.getElem?_map, hcallAt]
    rw [hleft] at hmap
    have hlengths : calls.length =
        (ReferenceActivePhysicalHorizon.calendar (start + a) (b - a)).length := by
      simpa using congrArg List.length hcallCalendar
    have hlen : index < (ReferenceActivePhysicalHorizon.calendar (start + a) (b - a)).length := by
      rw [← hlengths]
      exact hindex
    have hcalendar : (ReferenceActivePhysicalHorizon.calendar (start + a) (b - a))[index]? =
        some (start + a + index) := by
      rw [List.getElem?_eq_getElem hlen]
      simp [ReferenceActivePhysicalHorizon.calendar]
    rw [hcalendar] at hmap
    exact Option.some.inj hmap
  obtain ⟨j, hj, hget⟩ := List.getElem_of_mem hrecordB
  have htimeRun : record.input.time.val = start + j := by
    have htimes := ReferenceActivePhysicalHorizon.run_time_values initial rows selected rewards
      start b hspan hmode
    have hmap := congrArg (fun ts : List ℕ => ts[j]?) htimes
    have hleft : (Rb.records.map (fun r => r.input.time.val))[j]? = some record.input.time.val := by
      simp [List.getElem?_map, List.getElem?_eq_getElem hj, hget]
    rw [hleft] at hmap
    have hrunCount := ReferenceActivePhysicalHorizon.run_record_count initial rows selected
      rewards start b hspan hmode
    have hjb : j < b := by
      have hcountRb : Rb.records.length = b := by simpa [Rb] using hrunCount
      rw [hcountRb] at hj
      exact hj
    have hlen : j < (ReferenceActivePhysicalHorizon.calendar start b).length := by
      simpa [ReferenceActivePhysicalHorizon.calendar] using hjb
    have hcalendar : (ReferenceActivePhysicalHorizon.calendar start b)[j]? = some (start + j) := by
      rw [List.getElem?_eq_getElem hlen]
      simp [ReferenceActivePhysicalHorizon.calendar]
    rw [hcalendar] at hmap
    exact Option.some.inj hmap
  have hjEq : j = a + index := by
    have hcallVal := congrArg Fin.val hcallTime
    have hsum : start + j = start + (a + index) := by
      calc
        start + j = record.input.time.val := htimeRun.symm
        _ = call.1.val := hcallVal.symm
        _ = start + a + index := hintervalTime
        _ = start + (a + index) := Nat.add_assoc _ _ _
    exact Nat.add_left_cancel hsum
  have hindexBound : index < b - a := by
    have hlen : calls.length = b - a := by
      simpa [ReferenceActivePhysicalHorizon.calendar] using congrArg List.length hcallCalendar
    rw [← hlen]
    exact hindex
  have hn : a + index ≤ b := by omega
  let Rn := ReferenceActivePhysicalHorizon.run initial rows selected rewards
    start (a + index) (by omega) hmode
  obtain ⟨_, _, _, hprefixFactsN⟩ :=
    ReferenceFollowerDownIntervalWindow.run_interval_downBatch_replay
      p rate initial rows selected rewards start (a + index) b (by omega) hspan hmode hseed
      i stateB memoryB hordinaryB
  have hrunTake : Rn.records = Rb.records.take (a + index) := by
    simpa [Rn, Rb] using hprefixFactsN.1
  have hrecordsPrefix : Rn.records = Ra.records ++ I.take index := by
    calc
      Rn.records = Rb.records.take (a + index) := hrunTake
      _ = Ra.records ++ I.take index := by
        rw [List.take_add, ← hprefix]
  have hconnectedB := ReferenceActivePhysicalHorizon.run_connected initial rows selected
    rewards start b hspan hmode
  have hconnectedInput := connected_take_to_input hconnectedB j hj
  have hconnectedN := ReferenceActivePhysicalHorizon.run_connected initial rows selected
    rewards start (a + index) (by omega) hmode
  have hconnectedInput' : ReferenceActivePhysicalHorizon.Connected initial
      (Rb.records.take (a + index)) record.input.state := by
    rw [← hget, ← hjEq]
    exact hconnectedInput
  have hconnectedPrefix : ReferenceActivePhysicalHorizon.Connected initial Rn.records record.input.state := by
    rw [hrunTake]
    exact hconnectedInput'
  have hsameFinal := connected_final_unique hconnectedPrefix hconnectedN
  have houtputOrdinary : ∃ next nextMemory,
      record.output.next.followers i = .ordinary next nextMemory := by
    obtain ⟨next, nextMemory, hnext⟩ := connected_output_ordinary
      hconnectedB i stateB memoryB hordinaryB j hj
    exact ⟨next, nextMemory, by rw [← hget]; exact hnext⟩
  obtain ⟨next, nextMemory, hnext⟩ := houtputOrdinary
  have hinputOrdinary : ∃ before beforeMemory,
      record.input.state.followers i = .ordinary before beforeMemory := by
    cases hbefore : record.input.state.followers i with
    | ordinary before beforeMemory => exact ⟨before, beforeMemory, rfl⟩
    | dagger =>
        have hdagger := ReferenceActivePhysicalStep.step_follower_dagger record.input i hbefore
        rw [record.output_eq] at hnext
        rw [hdagger] at hnext
        cases hnext
  obtain ⟨before, beforeMemory, hbefore⟩ := hinputOrdinary
  have hordinaryN : Rn.finalState.followers i = .ordinary before beforeMemory := by
    rw [← hsameFinal]
    exact hbefore
  obtain ⟨initialFollower, initialMemory, hinitial, _, _, _, _⟩ := hseed i
  have hspecN := ReferenceFollowerDecoderChronology.run_downBatch_spec initial rows selected
    rewards start (a + index) (by omega) hmode hseed i before beforeMemory hordinaryN
  have hreplayN := ReferenceFollowerDownDecoderReplay.run_downBatch_replay initial rows selected
    rewards start (a + index) (by omega) hmode hseed i initialFollower initialMemory hinitial
    before beforeMemory hordinaryN
  have hreplayA := ReferenceFollowerDownDecoderReplay.run_downBatch_replay initial rows selected
    rewards start a (by omega) hmode hseed i initialFollower initialMemory hinitial
    stateA memoryA hstateA
  have hallCalls : ∀ r ∈ I,
      ∃ c, ReferenceFollowerDownDecoderReplay.actualDownCall i r = some c := by
    intro r hr
    obtain ⟨choiceR, memoryR, hchoiceR, _⟩ :=
      hcorr.2.2 r (List.mem_of_mem_drop hr)
    exact ⟨(ReferenceFollowerDownDecoderReplay.preparedChoiceTime r i,
      ActiveFollowerDownAcceptance.currentRoundInput p i
        (ReferenceFollowerDownDecoderReplay.preparedChoiceRow r i)
        (ReferenceFollowerDownDecoderReplay.preparedChoiceTime r i)
        (ReferenceFollowerDownDecoderReplay.preparedOwnObservation r i) rate choiceR),
      ReferenceFollowerDownDecoderReplay.actualDownCall_ordinary r i choiceR memoryR hchoiceR⟩
  have hfilter := filterMap_take_all_some (ReferenceFollowerDownDecoderReplay.actualDownCall i)
    I index hallCalls
  have hactualPrefix : ReferenceFollowerDownDecoderReplay.actualDownCalls i Rn.records =
      ReferenceFollowerDownDecoderReplay.actualDownCalls i Ra.records ++ calls.take index := by
    rw [hrecordsPrefix]
    simp only [ReferenceFollowerDownDecoderReplay.actualDownCalls, List.filterMap_append]
    simpa [calls, ReferenceFollowerDownDecoderReplay.actualDownCalls] using hfilter
  have hbankBefore : before.downBatch =
      AffineBatchDecoder.run p trace ((calls.take index).map Prod.fst) stateA.downBatch := by
    have hbankA : stateA.downBatch =
        ReferenceFollowerDownDecoderReplay.foldDownCalls
          (ReferenceFollowerDownDecoderReplay.actualDownCalls i Ra.records) initialFollower.downBatch := by
      simpa [ReferenceFollowerDownDecoderReplay.replayDownCalls] using hreplayA.1
    calc
      before.downBatch = ReferenceFollowerDownDecoderReplay.foldDownCalls
          (ReferenceFollowerDownDecoderReplay.actualDownCalls i Rn.records) initialFollower.downBatch := hreplayN.1
      _ = ReferenceFollowerDownDecoderReplay.foldDownCalls
          (ReferenceFollowerDownDecoderReplay.actualDownCalls i Ra.records ++ calls.take index)
          initialFollower.downBatch := by rw [hactualPrefix]
      _ = ReferenceFollowerDownDecoderReplay.foldDownCalls (calls.take index)
          (ReferenceFollowerDownDecoderReplay.foldDownCalls
            (ReferenceFollowerDownDecoderReplay.actualDownCalls i Ra.records) initialFollower.downBatch) := by
            simp [ReferenceFollowerDownDecoderReplay.foldDownCalls, List.foldl_append]
      _ = ReferenceFollowerDownDecoderReplay.foldDownCalls (calls.take index) stateA.downBatch := by
            rw [← hbankA]
      _ = AffineBatchDecoder.run p trace ((calls.take index).map Prod.fst) stateA.downBatch :=
            ReferenceFollowerDownIntervalWindow.foldDownCalls_eq_run trace (by
              intro c hc
              exact hcurrent c (List.mem_of_mem_take hc)) stateA.downBatch
  have hframe := ReferenceFollowerDecoderChronology.run_interruption_downBatch_frame
    record i before choice beforeMemory choiceMemory hbefore hprepared
    hspecN.2
  have hchoiceBank : choice.downBatch =
      AffineBatchDecoder.run p trace ((calls.take index).map Prod.fst) stateA.downBatch :=
    hframe.1.trans hbankBefore
  have htraceActual : trace call.1 = ActiveFollowerDownAcceptance.currentInputExtension p
      (ActiveFollowerDownAcceptance.currentRoundInput p i
        (ReferenceFollowerDownDecoderReplay.preparedChoiceRow record i)
        (ReferenceFollowerDownDecoderReplay.preparedChoiceTime record i)
        (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i) rate choice) call.1 := by
    calc
      trace call.1 = ActiveFollowerDownAcceptance.currentInputExtension p call.2 call.1 :=
        hcurrent call hcallMem
      _ = _ := by rw [hcallSecond]
  have hinputEligible : AffineBatchDecoder.eligible
      (ActiveFollowerDownAcceptance.currentRoundInput p i
        (ReferenceFollowerDownDecoderReplay.preparedChoiceRow record i)
        (ReferenceFollowerDownDecoderReplay.preparedChoiceTime record i)
        (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i) rate choice) := by
    have hext : AffineBatchDecoder.eligible
        (ActiveFollowerDownAcceptance.currentInputExtension p
          (ActiveFollowerDownAcceptance.currentRoundInput p i
            (ReferenceFollowerDownDecoderReplay.preparedChoiceRow record i)
            (ReferenceFollowerDownDecoderReplay.preparedChoiceTime record i)
            (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i) rate choice) call.1) := by
      rw [← htraceActual]
      exact hcallEligible
    simpa [ActiveFollowerDownAcceptance.currentInputExtension] using hext
  have hconditions := (ReferenceFollowerDownDecoderReplay.actualDownCall_eligible_iff
    record i choice).mp hinputEligible
  have hchoiceStatus : choice.status = .unoccupied := hconditions.2.1
  have hdecodeCurrent : AffineBatchDecoder.decodeStep p trace
      (AffineBatchDecoder.run p trace ((calls.take index).map Prod.fst) stateA.downBatch) call.1 =
      AffineBatchDecoder.decodeStep p
        (ActiveFollowerDownAcceptance.currentInputExtension p
          (ActiveFollowerDownAcceptance.currentRoundInput p i
            (ReferenceFollowerDownDecoderReplay.preparedChoiceRow record i)
            (ReferenceFollowerDownDecoderReplay.preparedChoiceTime record i)
            (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i) rate choice))
        choice.downBatch (ReferenceFollowerDownDecoderReplay.preparedChoiceTime record i) := by
    calc
      _ = AffineBatchDecoder.decodeStep p
          (ActiveFollowerDownAcceptance.currentInputExtension p call.2)
          (AffineBatchDecoder.run p trace ((calls.take index).map Prod.fst) stateA.downBatch) call.1 :=
            ActiveFollowerDownAcceptance.decodeStep_depends_on_current_input p trace
              (ActiveFollowerDownAcceptance.currentInputExtension p call.2) _ call.1 (hcurrent call hcallMem)
      _ = _ := by rw [hcallSecond, hcallFirst, ← hchoiceBank]
  have hrawChoice : (ActiveFollowerDownAcceptance.currentDecodeStep p i
      (ReferenceFollowerDownDecoderReplay.preparedChoiceRow record i)
      (ReferenceFollowerDownDecoderReplay.preparedChoiceTime record i)
      (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i) rate choice).2 =
      AffineBatchDecoder.batchOutput window := by
    simpa [ActiveFollowerDownAcceptance.currentDecodeStep] using
      (congrArg Prod.snd hdecodeCurrent).symm.trans hraw
  let prepared := record.output.preparation.followers.followers i
  let observation := ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i
  let view := record.output.preparation.coordinator.downView
  have hfinish : (ReferenceActivePhysicalStep.finishFollower view prepared observation).configuration =
      .ordinary next nextMemory := by
    have hout := hnext
    rw [record.output_eq] at hout
    have hobserve : (record.output.preparation.observeFollower i).configuration =
        .ordinary next nextMemory := by
      rw [record.output_eq]
      simpa [ReferenceActivePhysicalStep.step] using hout
    simpa [view, prepared, observation, ReferenceFollowerDownDecoderReplay.preparedOwnObservation,
      ReferenceActivePhysicalStep.PreparedRound.observeFollower] using hobserve
  have hprepIndex : prepared.follower = i :=
    record.output.preparation.follower_alignment i |>.2.1
  obtain ⟨choice', choiceMemory', postRecord, hprepared', hrecordOk, hreleaseOk,
      hdownInputEq, hdownEq⟩ := finishFollower_ordinary_inversion_local
    view prepared observation next nextMemory hfinish
  have hconfig : DeclaredFollowerLocalRound.LocalConfiguration.ordinary choice' choiceMemory' =
      .ordinary choice choiceMemory := hprepared'.symm.trans
        (by simpa [prepared, ReferenceFollowerDownDecoderReplay.preparedChoiceConfiguration] using hprepared)
  injection hconfig with hchoiceEq hmemoryEq
  subst choice'
  subst choiceMemory'
  have hloggingStatus : choice.status = .unoccupied := hchoiceStatus
  cases hlogging : ActiveFollowerLogging.checkedLogging i prepared.row prepared.activation
      prepared.time (prepared.arm, observation) choice with
  | error reason =>
      simp [ReferenceActivePhysicalStep.recordFollower, hprepIndex, hloggingStatus, hlogging] at hrecordOk
  | ok logged =>
      have hconsume : DeclaredFollowerLocalRound.consumeDownResult rate
          (ReferenceDownReception.referenceDownCut p view i prepared.row prepared.time
            observation rate logged).outcome = .ok postRecord := by
        simpa [ReferenceActivePhysicalStep.recordFollower, hprepIndex, hloggingStatus, hlogging] using hrecordOk
      have hloggedFields := ActiveFollowerLogging.checkedLogging_success_frame i prepared.row
        prepared.activation prepared.time (prepared.arm, observation) choice logged hlogging
      rcases hloggedFields with ⟨_, _, _, _, hloggedStatus, hloggedBank, _⟩
      have hloggingValidity := ActiveFollowerLogging.checkedLogging_success_iff i prepared.row
        prepared.activation prepared.time (prepared.arm, observation) choice logged |>.mp hlogging
      rcases hloggingValidity with ⟨hchoiceBuffer, _, hloggedBuffer⟩
      have hloggedWell : ReferenceFollowerDecoderChronology.downBatchWellFormed logged.downBatch := by
        rw [hloggedBank, hframe.1]
        exact hspecN.1.1
      have hcompared := referenceDownCut_compared_of_consumed_success p rate view i prepared.row
        prepared.time observation logged postRecord hconditions.1 (hloggedStatus.trans hchoiceStatus)
        hloggedWell hconsume
      rcases hcompared with ⟨hregisterDomain, hdecoderDomain, hbufferDomain, hrawCompared⟩
      have hcutRaw := ReferenceDownReception.referenceDownCut_raw_eq_currentDecodeStep_of_compared
        view i prepared.row prepared.time observation rate logged hrawCompared
      have hdecodedSame :
          ActiveFollowerDownAcceptance.currentDecodeStep p i prepared.row prepared.time
            observation rate logged =
          ActiveFollowerDownAcceptance.currentDecodeStep p i prepared.row prepared.time
            observation rate choice := by
        simp [ActiveFollowerDownAcceptance.currentDecodeStep,
          ActiveFollowerDownAcceptance.currentRoundInput, hloggedStatus, hloggingStatus, hloggedBank]
      have hcutWindow :
          (ReferenceDownReception.referenceDownCut p view i prepared.row prepared.time
            observation rate logged).raw = AffineBatchDecoder.batchOutput window := by
        calc
          _ = (ActiveFollowerDownAcceptance.currentDecodeStep p i prepared.row prepared.time
            observation rate logged).2 := hcutRaw
          _ = (ActiveFollowerDownAcceptance.currentDecodeStep p i prepared.row prepared.time
            observation rate choice).2 := congrArg Prod.snd hdecodedSame
          _ = AffineBatchDecoder.batchOutput window := hrawChoice
      refine ⟨index, call, entry, record, choice, choiceMemory, logged, postRecord, next,
        nextMemory, hindex, hsplit, hentry, hlast, hrecord, hactual, hcallTime, hprepared,
        hchoiceStatus, hconditions.1, hconditions.2.2, rfl, hfinish, hnext, ?_, ?_, hlogging,
        hchoiceBuffer, hloggedBuffer, hloggedBank, ?_, ?_, hregisterDomain, hdecoderDomain,
        hbufferDomain, hrawCompared, hcutWindow⟩
      · simpa [prepared, observation, view, hprepIndex,
          ReferenceFollowerDownDecoderReplay.preparedChoiceRow,
          ReferenceFollowerDownDecoderReplay.preparedChoiceTime] using hrecordOk
      · simpa [prepared, observation, view, hprepIndex,
          ReferenceFollowerDownDecoderReplay.preparedChoiceRow,
          ReferenceFollowerDownDecoderReplay.preparedChoiceTime] using hreleaseOk
      · have hlogged := ReferenceActivePhysicalStep.recordFollower_logged view i prepared.row
          prepared.activation prepared.time prepared.active prepared.arm observation choice logged
          hloggingStatus hlogging
        have hdownInputEq' := by simpa [hprepIndex] using hdownInputEq
        simpa [prepared, observation, view, hprepIndex,
          ReferenceActivePhysicalStep.PreparedRound.observeFollower,
          ReferenceFollowerDownDecoderReplay.preparedOwnObservation,
          ReferenceFollowerDownDecoderReplay.preparedChoiceRow,
          ReferenceFollowerDownDecoderReplay.preparedChoiceTime] using hdownInputEq'.trans hlogged.1
      · have hlogged := ReferenceActivePhysicalStep.recordFollower_logged view i prepared.row
          prepared.activation prepared.time prepared.active prepared.arm observation choice logged
          hloggingStatus hlogging
        have hdownEq' := by simpa [hprepIndex] using hdownEq
        simpa [prepared, observation, view, hprepIndex,
          ReferenceActivePhysicalStep.PreparedRound.observeFollower,
          ReferenceFollowerDownDecoderReplay.preparedOwnObservation,
          ReferenceFollowerDownDecoderReplay.preparedChoiceRow,
          ReferenceFollowerDownDecoderReplay.preparedChoiceTime] using hdownEq'.trans hlogged.2

/-- The actual launched-boundary specialization. All initialization inputs
remain explicit; the clipped block start, all-active mode, and decoder seed
are constructed from them before applying the generic record bridge. -/
theorem run_actualLaunched_interval_down_completed_window_record
    (p : ConstructorDimensions.Parameters)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (rate : ReferenceActivePhysicalStep.RateInput p) (C_star C_h : ℝ)
    (boundary : ReferenceInitializationRun.Boundary p)
    (hboundary : boundary.completed < BootstrapDimensions.n_boot p)
    (actual : ActualInitializationRun.BlockCarry p rate
      (ReferenceInitializationRun.nextBlock boundary hboundary))
    (past : List (ActualInitializationRun.PhysicalRoundRecord p rate source rewards))
    (hr : ActualReferenceInitializationBlock.BlockStartRelated source rewards
      C_star C_h rate (ReferenceInitializationRun.nextBlock boundary hboundary) actual
      boundary past)
    (hdown : ∀ i, ¬ InitializationFailureProvenance.generatedBlockDown
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
      boundary hboundary i)
    (hclean : ∀ (i : Fin (p.m - 1))
      (hi : ActualReferenceInitializationBlock.refFollower i ∈
        (ReferenceInitializationRun.physical
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
          boundary hboundary).uninformed),
      BootstrapAllCandidateController.cleanPrefix
        (ReferenceInitializationRun.physical
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
          boundary hboundary)
        source.1.2 ⟨ActualReferenceInitializationBlock.refFollower i, hi⟩
        (ActualInitializationPhysicalStep.selectedRowIndex p source) p.T)
    (hforce : ∀ i, ReferenceInitializationRun.forced
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
      boundary hboundary i = false)
    (launch : BootstrapCoordinatorLocalRound.LaunchedBlock p)
    (learnerSeed : ActualInitializationRun.CoordinatorLearnerZeroSeed p)
    (hlaunched : (ActualInitializationRun.combinedBoundaryHandoff p rate
      (ReferenceInitializationRun.nextBlock boundary hboundary) source rewards actual.C_star
      actual.C_h (ActualInitializationRun.foldBlock p rate
        (ReferenceInitializationRun.nextBlock boundary hboundary) source rewards actual)).disposition =
          .launched launch learnerSeed)
    (rows : CompletePublicTable.CompleteRows p)
    (a intervalEnd : ℕ) (ha : a ≤ intervalEnd)
    (hspan : BootstrapObservedFollower.blockStop p
      (ReferenceInitializationRun.nextBlock boundary hboundary) + intervalEnd ≤ p.T)
    (i : Fin (p.m - 1))
    (stateB : ReferencePrelaunchFollower.State p rate.eta)
    (memoryB : ActiveFollowerLifecycle.LocalMemory p)
    (hordinaryB : (ReferenceActivePhysicalHorizon.run
      (ActualInitializationLaunchState.ofActualLaunchedBoundary source rewards rate C_star C_h
        boundary hboundary actual past hr hdown hclean hforce launch learnerSeed hlaunched)
      rows (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
      (BootstrapObservedFollower.blockStop p
        (ReferenceInitializationRun.nextBlock boundary hboundary))
      intervalEnd hspan (by
        intro j
        exact ActualInitializationLaunchState.ofActualLaunchedBoundary_activation_le_blockStop
          source rewards rate C_star C_h boundary hboundary actual past hr hdown hclean hforce
          launch learnerSeed hlaunched j)).finalState.followers i = .ordinary stateB memoryB) :
    let initial := ActualInitializationLaunchState.ofActualLaunchedBoundary source rewards rate
      C_star C_h boundary hboundary actual past hr hdown hclean hforce launch learnerSeed hlaunched
    let start := BootstrapObservedFollower.blockStop p
      (ReferenceInitializationRun.nextBlock boundary hboundary)
    ∃ hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start,
      ∃ _hseed : ReferenceFollowerDecoderChronology.downBatchSeed initial start,
        intervalDownCompletedWindowRecordResult p rate initial rows
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start a intervalEnd
          ha hspan hmode i := by
  let initial := ActualInitializationLaunchState.ofActualLaunchedBoundary source rewards rate
    C_star C_h boundary hboundary actual past hr hdown hclean hforce launch learnerSeed hlaunched
  let start := BootstrapObservedFollower.blockStop p
    (ReferenceInitializationRun.nextBlock boundary hboundary)
  have hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start := by
    intro j
    exact ActualInitializationLaunchState.ofActualLaunchedBoundary_activation_le_blockStop
      source rewards rate C_star C_h boundary hboundary actual past hr hdown hclean hforce
      launch learnerSeed hlaunched j
  have hseed := ReferenceFollowerDecoderChronology.ofActualLaunchedBoundary_downBatchSeed
    source rewards rate C_star C_h boundary hboundary actual past hr hdown hclean hforce launch
    learnerSeed hlaunched
  refine ⟨hmode, hseed, ?_⟩
  exact run_interval_down_completed_window_record p rate initial rows
    (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start a intervalEnd ha
    hspan hmode hseed i stateB memoryB (by simpa [initial, start] using hordinaryB)

end Bandits.Support.ReferenceFollowerDownWindowRecord

end
