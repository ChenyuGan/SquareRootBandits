/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import Lean.Elab.Tactic.Omega
import Mathlib.Data.List.Intervals
public import Bandits.Support.ReferenceFollowerDownWindowRecord

/-!
# Physical DOWN completed-window cut

Sources: `sources/zip4/manuscript/05_binary_transport.tex:36-53`,
`sources/zip4/manuscript/06_interruptions.tex:248-275,327-348`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:92-109,151-157`.

This module strengthens the accepted physical record bridge with one coherent
maximal-entry/call/record witness, its actual prefix decoder bank, and the
literal completed-batch state at the retained cut. It keeps the positive-count
equation as a conditional conclusion after fixing the actual A-prefix state;
it makes no uniqueness or acceptance claim.
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

namespace Bandits.Support.ReferenceFollowerDownWindowCompletedCut

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

private theorem decoderRun_append
    {p : Parameters} (trace : AffineBatchDecoder.Trace p)
    (left right : List (Fin p.T))
    (state : AffineBatchDecoder.State p.T (AffineBatchDecoder.width p)) :
    AffineBatchDecoder.run p trace (left ++ right) state =
      AffineBatchDecoder.run p trace right (AffineBatchDecoder.run p trace left state) := by
  induction left generalizing state with
  | nil => rfl
  | cons time rest ih =>
      simp only [List.cons_append, AffineBatchDecoder.run]
      exact ih _

private theorem decoderRun_ineligible
    {p : Parameters} (trace : AffineBatchDecoder.Trace p)
    (rounds : List (Fin p.T))
    (state : AffineBatchDecoder.State p.T (AffineBatchDecoder.width p))
    (hpending : state.pending.length < AffineBatchDecoder.quota p)
    (hineligible : ∀ time ∈ rounds, ¬ AffineBatchDecoder.eligible (trace time)) :
    AffineBatchDecoder.run p trace rounds state = state := by
  induction rounds generalizing state with
  | nil => rfl
  | cons time rest ih =>
      have hhead := hineligible time (by simp)
      have htail : ∀ current ∈ rest, ¬ AffineBatchDecoder.eligible (trace current) := by
        intro current hcurrent
        exact hineligible current (by simp [hcurrent])
      simp only [AffineBatchDecoder.run,
        AffineBatchDecoder.step_ineligible p trace state time hpending hhead]
      exact ih state hpending htail

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

private theorem last_positive_decode_complete
    (p : Parameters) (calls : List (Call p))
    (trace : AffineBatchDecoder.Trace p)
    (hcurrent : ∀ call ∈ calls,
      trace call.1 = ActiveFollowerDownAcceptance.currentInputExtension p call.2 call.1)
    (hcallPair : calls.Pairwise (fun left right => left.1.val < right.1.val))
    (bank : AffineBatchDecoder.State p.T (AffineBatchDecoder.width p))
    (hbank : ReferenceFollowerDecoderChronology.downBatchWellFormed bank)
    (positives : List (AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p)))
    (hpositives : ReferenceFollowerDownDecoderReplay.positiveCallEntries calls = positives)
    (hpositivePair : positives.Pairwise
      (fun earlier later => earlier.time.val < later.time.val))
    (first window : List (AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p)))
    (hwindow : window = positives.drop
      (AffineBatchDecoder.quota p - bank.pending.length))
    (hrun : AffineBatchDecoder.run p trace (calls.map Prod.fst) bank =
      ⟨[], bank.completed ++ [first, window]⟩)
    (index : ℕ) (call : Call p)
    (entry : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p))
    (hsplit : calls = calls.take index ++ call :: calls.drop (index + 1))
    (hentry : entry ∈ window)
    (hentryTime : entry.time = call.1)
    (hlast : ∀ other ∈ window, other.time.val ≤ entry.time.val)
    (hcallEligible : AffineBatchDecoder.eligible (trace call.1)) :
    let before := AffineBatchDecoder.run p trace ((calls.take index).map Prod.fst) bank
    before.pending ++ AffineBatchDecoder.positiveAt p trace call.1 = window ∧
    AffineBatchDecoder.decodeStep p trace before call.1 =
      (⟨[], bank.completed ++ [first, window]⟩,
        AffineBatchDecoder.batchOutput window) := by
  classical
  let before := AffineBatchDecoder.run p trace ((calls.take index).map Prod.fst) bank
  have hcallTailPair : (call :: calls.drop (index + 1)).Pairwise
      (fun left right => left.1.val < right.1.val) := by
    have hsplitPair : (calls.take index ++ call :: calls.drop (index + 1)).Pairwise
        (fun left right => left.1.val < right.1.val) := by
      rw [← hsplit]
      exact hcallPair
    exact (List.pairwise_append.mp hsplitPair).2.1
  have hcallTail : ∀ later ∈ calls.drop (index + 1), call.1.val < later.1.val := by
    intro later hlater
    have hpair := hcallTailPair
    simp only [List.pairwise_cons] at hpair
    exact hpair.1 later hlater
  have hlastBound : ∀ item ∈ positives, item.time.val ≤ entry.time.val := by
    intro item hitem
    let count := AffineBatchDecoder.quota p - bank.pending.length
    have hsplitPos : positives.take count ++ window = positives := by
      rw [hwindow, List.take_append_drop]
    have hpairSplit : (positives.take count ++ window).Pairwise
        (fun earlier later => earlier.time.val < later.time.val) := by
      rw [hsplitPos]
      exact hpositivePair
    have hmem : item ∈ positives.take count ++ window := by
      rw [hsplitPos]
      exact hitem
    rcases List.mem_append.mp hmem with hleft | hright
    · obtain ⟨_, _, hcross⟩ := List.pairwise_append.mp hpairSplit
      exact Nat.le_of_lt (hcross item hleft entry hentry)
    · exact hlast item hright
  have htailIneligible : ∀ later ∈ calls.drop (index + 1),
      ¬ AffineBatchDecoder.eligible (trace later.1) := by
    intro later hlater heligible
    have hnewCall : AffineBatchDecoder.entry p trace later.1 ∈
        ReferenceFollowerDownDecoderReplay.positiveCallEntries calls := by
      apply List.mem_flatMap.mpr
      refine ⟨later, List.mem_of_mem_drop hlater, ?_⟩
      have hinputEligible : AffineBatchDecoder.eligible
          ((ActiveFollowerDownAcceptance.currentInputExtension p later.2) later.1) := by
        rw [← hcurrent later (List.mem_of_mem_drop hlater)]
        exact heligible
      have hentryEq : AffineBatchDecoder.entry p trace later.1 =
          AffineBatchDecoder.entry p
            (ActiveFollowerDownAcceptance.currentInputExtension p later.2) later.1 := by
        simp only [AffineBatchDecoder.entry,
          hcurrent later (List.mem_of_mem_drop hlater)]
      simp only [AffineBatchDecoder.positiveAt, hinputEligible, ↓reduceIte]
      exact List.mem_singleton.mpr hentryEq
    have hnew : AffineBatchDecoder.entry p trace later.1 ∈ positives := by
      rw [← hpositives]
      exact hnewCall
    have hbound := hlastBound _ hnew
    have htime : (AffineBatchDecoder.entry p trace later.1).time = later.1 := rfl
    have hlt := hcallTail later hlater
    rw [htime, hentryTime] at hbound
    omega
  have hbeforeWell := AffineBatchDecoder.run_spec p trace
    ((calls.take index).map Prod.fst) bank hbank.1 hbank.2
  have hstepBound : (AffineBatchDecoder.step p trace before call.1).pending.length <
      AffineBatchDecoder.quota p := by
    simpa [before, AffineBatchDecoder.run] using
      (AffineBatchDecoder.run_spec p trace [call.1] before
        hbeforeWell.1 hbeforeWell.2.1).1
  have hroundsSplit : calls.map Prod.fst =
      (calls.take index).map Prod.fst ++
        ([call.1] ++ (calls.drop (index + 1)).map Prod.fst) := by
    calc
      calls.map Prod.fst = (calls.take index ++ call :: calls.drop (index + 1)).map Prod.fst :=
        congrArg (List.map Prod.fst) hsplit
      _ = _ := by simp [List.map_append]
  have hafterRun : AffineBatchDecoder.run p trace (calls.map Prod.fst) bank =
      AffineBatchDecoder.step p trace before call.1 := by
    calc
      _ = AffineBatchDecoder.run p trace
          ((calls.take index).map Prod.fst ++
            ([call.1] ++ (calls.drop (index + 1)).map Prod.fst)) bank := by
              rw [hroundsSplit]
      _ = AffineBatchDecoder.run p trace
          ([call.1] ++ (calls.drop (index + 1)).map Prod.fst) before :=
            decoderRun_append trace _ _ _
      _ = AffineBatchDecoder.run p trace ((calls.drop (index + 1)).map Prod.fst)
          (AffineBatchDecoder.step p trace before call.1) := by
            rw [decoderRun_append]
            rfl
      _ = AffineBatchDecoder.step p trace before call.1 :=
        decoderRun_ineligible trace _ _ hstepBound (by
          intro time htime heligible
          obtain ⟨later, hlater, rfl⟩ := List.mem_map.mp htime
          exact htailIneligible later hlater heligible)
  have hafterShape : AffineBatchDecoder.step p trace before call.1 =
      ⟨[], bank.completed ++ [first, window]⟩ := hafterRun.symm.trans hrun
  have hquota : before.pending.length + 1 = AffineBatchDecoder.quota p := by
    by_contra hnot
    have hlt : before.pending.length + 1 < AffineBatchDecoder.quota p := by
      have hbeforeBound : before.pending.length < AffineBatchDecoder.quota p := by
        simpa [before] using hbeforeWell.1
      omega
    have hstepPending : (AffineBatchDecoder.step p trace before call.1).pending =
        before.pending ++ [AffineBatchDecoder.entry p trace call.1] := by
      simp [AffineBatchDecoder.step, AffineBatchDecoder.positiveAt, hcallEligible, hlt]
    have hnil := congrArg AffineBatchDecoder.State.pending hafterShape
    rw [hstepPending] at hnil
    simp at hnil
  have hcompleted : before.completed ++
      [before.pending ++ [AffineBatchDecoder.entry p trace call.1]] =
      bank.completed ++ [first, window] := by
    have hstates := congrArg AffineBatchDecoder.State.completed hafterShape
    rw [AffineBatchDecoder.step_complete p trace before call.1 hcallEligible hquota] at hstates
    exact hstates
  have hbatchEq : before.pending ++ [AffineBatchDecoder.entry p trace call.1] = window := by
    have hlastOpt := congrArg List.getLast? hcompleted
    have hleftLast : (before.completed ++
        [before.pending ++ [AffineBatchDecoder.entry p trace call.1]]).getLast? =
          some (before.pending ++ [AffineBatchDecoder.entry p trace call.1]) := by simp
    have hrightLast : (bank.completed ++ [first, window]).getLast? = some window := by simp
    rw [hleftLast, hrightLast] at hlastOpt
    exact Option.some.inj hlastOpt
  have htested : before.pending ++ AffineBatchDecoder.positiveAt p trace call.1 = window := by
    simpa [AffineBatchDecoder.positiveAt, hcallEligible] using hbatchEq
  have hdecode : AffineBatchDecoder.decodeStep p trace before call.1 =
      (⟨[], bank.completed ++ [first, window]⟩,
        AffineBatchDecoder.batchOutput window) := by
    calc
      _ = (⟨[], before.completed ++
            [before.pending ++ [AffineBatchDecoder.entry p trace call.1]]⟩,
          AffineBatchDecoder.batchOutput
            (before.pending ++ [AffineBatchDecoder.entry p trace call.1])) :=
          AffineBatchDecoder.decodeStep_complete p trace before call.1 hcallEligible hquota
      _ = _ := by rw [hcompleted, hbatchEq]
  exact ⟨by simpa [before] using htested, by simpa [before] using hdecode⟩

/-- The strengthened actual record/cut result. The A-prefix state is selected
before the count implication; when its exact positive-count equation holds, the
same witness tuple links the maximal entry, physical call, record, prefix bank,
tested batch, and completed current decoder step. -/
def intervalDownCompletedWindowCutResult
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
         let first := stateA.downBatch.pending ++ positives.take
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
           entry.time = call.1 ∧
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
               AffineBatchDecoder.batchOutput window ∧
           ∃ hindexBound : index < b - a,
           ∃ trace : AffineBatchDecoder.Trace p,
             (∀ listed ∈ calls,
               trace listed.1 = ActiveFollowerDownAcceptance.currentInputExtension p listed.2 listed.1) ∧
             ∃ prefixState : ReferencePrelaunchFollower.State p rate.eta,
               ∃ prefixMemory : ActiveFollowerLifecycle.LocalMemory p,
                 (ReferenceActivePhysicalHorizon.run initial rows selected rewards
                   start (a + index) (by omega) hmode).finalState.followers i =
                     .ordinary prefixState prefixMemory ∧
                 record.input.state.followers i = .ordinary prefixState prefixMemory ∧
                 prefixState.downBatch = AffineBatchDecoder.run p trace
                   ((calls.take index).map Prod.fst) stateA.downBatch ∧
                 choice.downBatch = prefixState.downBatch ∧
                 choice.downBatch.pending ++ AffineBatchDecoder.positiveAt p trace call.1 = window ∧
                 logged.downBatch.pending ++ AffineBatchDecoder.positiveAt p trace call.1 = window ∧
                 (choice.downBatch.pending ++ AffineBatchDecoder.positiveAt p trace call.1).length =
                   AffineBatchDecoder.quota p ∧
                 (ActiveFollowerDownAcceptance.currentDecodeStep p i
                   (ReferenceFollowerDownDecoderReplay.preparedChoiceRow record i)
                   (ReferenceFollowerDownDecoderReplay.preparedChoiceTime record i)
                   (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i) rate logged).1 =
                     ⟨[], stateA.downBatch.completed ++ [first, window]⟩)

/-- Prove the strengthened result from the accepted interval replay and the
physical run's actual maximal positive DOWN call. The count equation remains
inside the result implication, rather than becoming a theorem premise. -/
theorem run_interval_down_completed_window_cut
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
        start b hspan hmode).finalState.followers i = .ordinary stateB memoryB) : intervalDownCompletedWindowCutResult p rate initial rows selected rewards start a b hab hspan hmode i := by
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
  let first := stateA.downBatch.pending ++ positives.take
    (AffineBatchDecoder.quota p - stateA.downBatch.pending.length)
  refine ⟨stateA, memoryA, hstateA, ?_⟩
  dsimp only
  intro hcount
  classical
  dsimp only at hconditional
  rcases hconditional hcount with ⟨hshape, hfirstLen, hwindowLen, hwindowPair,
    hpendingDisjoint, hwindowFacts, ⟨trace, hcurrent, index, call, entry,
    hindex, hsplit, hentry, hentryTime, hlast, hcallEligible, hraw⟩⟩
  have hshape' : stateB.downBatch =
      ⟨[], stateA.downBatch.completed ++ [first, window]⟩ := by
    simpa [first, window] using hshape
  have hbankWell : ReferenceFollowerDecoderChronology.downBatchWellFormed
      stateA.downBatch :=
    (ReferenceFollowerDecoderChronology.run_downBatch_spec initial rows selected rewards
      start a (by omega) hmode hseed i stateA memoryA hstateA).1.1
  have hpositiveCallEq : ReferenceFollowerDownDecoderReplay.positiveCallEntries calls = positives := by
    rfl
  have hbankFull : stateB.downBatch =
      AffineBatchDecoder.run p trace (calls.map Prod.fst) stateA.downBatch := by
    calc
      stateB.downBatch = ReferenceFollowerDownDecoderReplay.foldDownCalls calls
          stateA.downBatch := by simpa [calls, I, Rb] using hbank
      _ = AffineBatchDecoder.run p trace (calls.map Prod.fst) stateA.downBatch :=
        ReferenceFollowerDownIntervalWindow.foldDownCalls_eq_run trace hcurrent stateA.downBatch
  have hrunShape : AffineBatchDecoder.run p trace (calls.map Prod.fst) stateA.downBatch =
      ⟨[], stateA.downBatch.completed ++ [first, window]⟩ := hbankFull.symm.trans hshape'
  have hcompletion := last_positive_decode_complete p calls trace hcurrent hcallPair
    stateA.downBatch hbankWell positives hpositiveCallEq hpositivePair first window rfl
    hrunShape index call entry hsplit hentry hentryTime hlast hcallEligible
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
      have hchoiceTest : choice.downBatch.pending ++
          AffineBatchDecoder.positiveAt p trace call.1 = window := by
        calc
          _ = (AffineBatchDecoder.run p trace
              ((calls.take index).map Prod.fst) stateA.downBatch).pending ++
                AffineBatchDecoder.positiveAt p trace call.1 := by rw [hchoiceBank]
          _ = window := hcompletion.1
      have hloggedTest : logged.downBatch.pending ++
          AffineBatchDecoder.positiveAt p trace call.1 = window := by
        calc
          _ = choice.downBatch.pending ++ AffineBatchDecoder.positiveAt p trace call.1 := by
                rw [hloggedBank]
          _ = window := hchoiceTest
      have hchoiceTestLength : (choice.downBatch.pending ++
          AffineBatchDecoder.positiveAt p trace call.1).length = AffineBatchDecoder.quota p := by
        calc
          _ = window.length := congrArg List.length hchoiceTest
          _ = AffineBatchDecoder.quota p := hwindowLen
      have hfirstAdmin :
          (AffineBatchDecoder.decodeStep p trace
            (AffineBatchDecoder.run p trace ((calls.take index).map Prod.fst)
              stateA.downBatch) call.1).1 =
            ⟨[], stateA.downBatch.completed ++ [first, window]⟩ :=
        congrArg Prod.fst hcompletion.2
      have hfirstCurrentChoice :
          (ActiveFollowerDownAcceptance.currentDecodeStep p i
            (ReferenceFollowerDownDecoderReplay.preparedChoiceRow record i)
            (ReferenceFollowerDownDecoderReplay.preparedChoiceTime record i)
            (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i) rate choice).1 =
            ⟨[], stateA.downBatch.completed ++ [first, window]⟩ := by
        calc
          _ = (AffineBatchDecoder.decodeStep p trace
              (AffineBatchDecoder.run p trace ((calls.take index).map Prod.fst)
                stateA.downBatch) call.1).1 := by
                  simpa [ActiveFollowerDownAcceptance.currentDecodeStep] using
                    (congrArg Prod.fst hdecodeCurrent).symm
          _ = ⟨[], stateA.downBatch.completed ++ [first, window]⟩ := hfirstAdmin
      have hfirstLogged :
          (ActiveFollowerDownAcceptance.currentDecodeStep p i prepared.row prepared.time
            observation rate logged).1 =
            ⟨[], stateA.downBatch.completed ++ [first, window]⟩ := by
        calc
          _ = (ActiveFollowerDownAcceptance.currentDecodeStep p i prepared.row prepared.time
              observation rate choice).1 := congrArg Prod.fst hdecodedSame
          _ = ⟨[], stateA.downBatch.completed ++ [first, window]⟩ := by
                simpa [prepared, observation, ReferenceFollowerDownDecoderReplay.preparedChoiceRow,
                  ReferenceFollowerDownDecoderReplay.preparedChoiceTime] using hfirstCurrentChoice
      refine ⟨index, call, entry, record, choice, choiceMemory, logged, postRecord, next,
        nextMemory, hindex, hsplit, hentry, hlast, hentryTime, hrecord, hactual, hcallTime, hprepared,
        hchoiceStatus, hconditions.1, hconditions.2.2, rfl, hfinish, hnext, ?_, ?_, hlogging,
        hchoiceBuffer, hloggedBuffer, hloggedBank, ?_, ?_, hregisterDomain, hdecoderDomain,
        hbufferDomain, hrawCompared, hcutWindow, hindexBound, trace, hcurrent, before, beforeMemory,
        hordinaryN, hbefore, hbankBefore, hframe.1, hchoiceTest, hloggedTest,
        hchoiceTestLength, hfirstLogged⟩
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

/-- The actual launched-boundary specialization with the original source rows
and selected row index. All initialization inputs remain explicit; the clipped
block start, all-active mode, and decoder seed are constructed from them before
applying the generic cut bridge. -/
theorem run_actualLaunched_interval_down_completed_window_cut
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
    (a intervalEnd : ℕ) (ha : a ≤ intervalEnd)
    (hspan : BootstrapObservedFollower.blockStop p
      (ReferenceInitializationRun.nextBlock boundary hboundary) + intervalEnd ≤ p.T)
    (i : Fin (p.m - 1))
    (stateB : ReferencePrelaunchFollower.State p rate.eta)
    (memoryB : ActiveFollowerLifecycle.LocalMemory p)
    (hordinaryB : (ReferenceActivePhysicalHorizon.run
      (ActualInitializationLaunchState.ofActualLaunchedBoundary source rewards rate C_star C_h
        boundary hboundary actual past hr hdown hclean hforce launch learnerSeed hlaunched)
      source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
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
        intervalDownCompletedWindowCutResult p rate initial source.1.2
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
  exact run_interval_down_completed_window_cut p rate initial source.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start a intervalEnd ha
    hspan hmode hseed i stateB memoryB (by simpa [initial, start] using hordinaryB)

end Bandits.Support.ReferenceFollowerDownWindowCompletedCut

end
