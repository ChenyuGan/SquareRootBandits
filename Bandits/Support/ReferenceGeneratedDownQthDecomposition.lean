/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedDownQthCalendar

import Lean.Elab.Tactic.Omega
import Mathlib.Data.List.TakeDrop

/-!
# Decomposition of the actual fresh-reset DOWN q-th event

Sources: `sources/zip4/manuscript/appendix_a_local_protocol.tex:112-138`,
`sources/zip4/manuscript/05_binary_transport.tex:20-42`,
`sources/zip4/manuscript/07_public_setup.tex:127-142`, and
`sources/zip4/manuscript/08_main_theorem.tex:29-42`.

All events below use the original generated launch source and its physical run
through T. These are deterministic internal identities for genuine postlaunch
fresh resets. No probability, conditional law, or manuscript closure is asserted.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Bandits.Support.ReferenceGeneratedDownQthDecomposition

open ReferenceGeneratedDownBatchCalendar
open ReferenceDownCompletedAmbiguityMeasurability

variable {p : ConstructorDimensions.Parameters} {rate : RateInput p}

private theorem survives_iff (candidate : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (q : ℕ) (tests : List (ExecutedTest p)) :
    survives candidate q tests ↔ q ≤ tests.length ∧
      ∀ test ∈ tests.take q, ExecutedTest.good candidate test := by
  induction q generalizing tests with
  | zero => simp only [survives, Nat.zero_le, List.take_zero, List.not_mem_nil,
      false_implies, implies_true, and_self]
  | succ q ih =>
      cases tests with
      | nil =>
          constructor
          · intro h; exact False.elim h
          · intro h; exact Nat.not_succ_le_zero q h.1
      | cons test tests =>
          rw [survives, ih]
          simp only [List.length_cons, Nat.succ_le_succ_iff, List.take_succ_cons,
            List.mem_cons, forall_eq_or_imp]
          exact and_left_comm

private theorem survives_take (candidate : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (q cap : ℕ) (hcap : q ≤ cap) (tests : List (ExecutedTest p)) :
    survives candidate q (tests.take cap) ↔ survives candidate q tests := by
  rw [survives_iff, survives_iff, List.length_take, List.take_take,
    Nat.min_eq_left hcap]
  exact and_congr_left fun _ => by omega

private theorem survives_filterMap_location {α : Type*}
    (candidate : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (f : α → Option (ExecutedTest p)) (l : List α) (q : ℕ) (hq : 1 ≤ q)
    (h : survives candidate q (l.filterMap f)) :
    ∃ m, ∃ hm : m < l.length, ∃ test,
      f l[m] = some test ∧ ((l.take m).filterMap f).length = q - 1 ∧
      (∀ prior ∈ (l.take m).filterMap f, ExecutedTest.good candidate prior) ∧
      ExecutedTest.good candidate test := by
  induction l generalizing q with
  | nil =>
      have hlen := ((survives_iff candidate q []).mp h).1
      simp only [List.length_nil] at hlen
      omega
  | cons a l ih =>
      cases hf : f a with
      | none =>
          rw [List.filterMap_cons_none hf] at h
          obtain ⟨m, hm, test, htest, hlength, hgood, hcurrent⟩ := ih q hq h
          refine ⟨m + 1, by simpa only [List.length_cons] using Nat.succ_lt_succ hm,
            test, ?_, ?_, ?_, hcurrent⟩
          · exact htest
          · simpa only [List.take_succ_cons, List.filterMap_cons_none hf] using hlength
          · simpa only [List.take_succ_cons, List.filterMap_cons_none hf] using hgood
      | some test =>
          rw [List.filterMap_cons_some hf] at h
          cases q with
          | zero => omega
          | succ q =>
              change ExecutedTest.good candidate test ∧ survives candidate q (l.filterMap f) at h
              cases q with
              | zero =>
                  exact ⟨0, by simp only [List.length_cons]; omega, test, hf,
                    rfl, by simp only [List.take_zero, List.filterMap_nil, List.not_mem_nil,
                      false_implies, implies_true], h.1⟩
              | succ q =>
                  obtain ⟨m, hm, next, hnext, hlength, hgood, hcurrent⟩ :=
                    ih (q + 1) (by omega) h.2
                  refine ⟨m + 1, by simpa only [List.length_cons] using Nat.succ_lt_succ hm,
                    next, hnext, ?_, ?_, hcurrent⟩
                  · simp only [List.take_succ_cons, List.filterMap_cons_some hf,
                      List.length_cons]
                    omega
                  · simp only [List.take_succ_cons, List.filterMap_cons_some hf,
                      List.mem_cons, forall_eq_or_imp]
                    exact ⟨h.1, hgood⟩

private theorem filterMap_split_at {α β : Type*} (f : α → Option β)
    (l : List α) (m : ℕ) (hm : m < l.length) (test : β)
    (hcurrent : f l[m] = some test) :
    l.filterMap f = (l.take m).filterMap f ++ test :: (l.drop (m + 1)).filterMap f := by
  nth_rw 1 [← List.take_append_drop m l]
  rw [List.filterMap_append, List.drop_eq_getElem_cons hm,
    List.filterMap_cons_some hcurrent]

private theorem survives_of_location {α : Type*}
    (candidate : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (f : α → Option (ExecutedTest p)) (l : List α) (m : ℕ)
    (hm : m < l.length) (test : ExecutedTest p) (hcurrent : f l[m] = some test)
    (hgood : ∀ prior ∈ (l.take m).filterMap f, ExecutedTest.good candidate prior)
    (hcurrentGood : ExecutedTest.good candidate test) :
    survives candidate (((l.take m).filterMap f).length + 1) (l.filterMap f) := by
  rw [filterMap_split_at f l m hm test hcurrent, survives_iff]
  constructor
  · simp only [List.length_append, List.length_cons]; omega
  · rw [List.take_append, List.take_of_length_le (Nat.le_succ _),
      Nat.add_sub_cancel_left]
    simp only [List.take_succ_cons, List.take_zero, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false]
    intro prior hprior
    rcases hprior with hprior | rfl
    · exact hgood prior hprior
    · exact hcurrentGood

private theorem survives_prior_of_location {α : Type*}
    (candidate : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (f : α → Option (ExecutedTest p)) (l : List α) (m : ℕ)
    (hm : m < l.length) (test : ExecutedTest p) (hcurrent : f l[m] = some test)
    (hgood : ∀ prior ∈ (l.take m).filterMap f, ExecutedTest.good candidate prior) :
    survives candidate ((l.take m).filterMap f).length (l.filterMap f) := by
  rw [filterMap_split_at f l m hm test hcurrent, survives_iff]
  constructor
  · simp only [List.length_append, List.length_cons]; omega
  · simpa only [List.take_left] using hgood

/-- An actual current test forces every earlier incoming focal state to be
ordinary. The full record is identified through V's actual observation theorem;
prepared-call inversion and connected-run dagger absorption rule out an earlier
dagger. The current successor is unrestricted. -/
theorem executedTest_prefix_ordinary
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (input : ReferenceActiveHorizonMeasurability.ActiveRunInput (p := p) (rate := rate) start)
    (i : Fin (p.m - 1)) (k : Fin count) (test : ExecutedTest p)
    (htest : executedTestOfRound rate
      ((runDownObservation start count hspan i input).2 k) = some test)
    (n : ℕ) (hn : n ≤ k.val) :
    ∃ state memory,
      (ReferenceActiveHorizonMeasurability.runOfInput start n (by omega) input).finalState.followers i =
        .ordinary state memory := by
  let record : ReferenceFollowerDownDecoderReplay.Record p rate :=
    ⟨prefixInput start k.val (by omega) input,
      ReferenceActivePhysicalStep.step (prefixInput start k.val (by omega) input), rfl⟩
  have hcodes := (runDownObservation_eq_actual start count hspan i input).2
  rw [run_records_eq_ofFn, List.map_ofFn] at hcodes
  have hcode := congrFun (List.ofFn_inj.mp hcodes) k
  change (runDownObservation start count hspan i input).2 k =
    roundDownObservation record.input i at hcode
  rw [hcode] at htest
  obtain ⟨call, hcall, _heligible, _htime, _hsample, _horiginalTime,
    _horiginalSample, _hsent⟩ :=
    ReferenceGeneratedDownPrefixList.executedTestOfRound_some_actual record i test htest
  have hmember : record ∈
      (ReferenceActiveHorizonMeasurability.runOfInput start count hspan input).records.drop n := by
    rw [run_records_eq_ofFn]
    apply List.mem_drop_iff_getElem.mpr
    refine ⟨k.val - n, by simp only [List.length_ofFn]; omega, ?_⟩
    have hindex : n + (k.val - n) = k.val := by omega
    simp only [List.getElem_ofFn, hindex]
    rfl
  cases hc : (ReferenceActiveHorizonMeasurability.runOfInput start n
      (by omega) input).finalState.followers i with
  | dagger =>
      have hnone := ReferenceExecutedDownBankRecurrence.run_suffix_downCallObservation_none_of_dagger
        input.1.1 input.1.2.1 input.1.2.2.1 input.1.2.2.2 start n (count - n)
        (by omega) input.2 i hc
      have htotal : n + (count - n) = count := by omega
      simp only [htotal] at hnone
      have hrecordNone := hnone record hmember
      have hreconstruct := downCallObservation_reconstructs i record
      rw [hrecordNone, Option.map_none, hcall] at hreconstruct
      cases hreconstruct
  | ordinary state memory => exact ⟨state, memory, rfl⟩

/-- In particular the executed current test has an ordinary incoming state,
even if that same physical round subsequently fails. -/
theorem executedTest_incoming_ordinary
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (input : ReferenceActiveHorizonMeasurability.ActiveRunInput (p := p) (rate := rate) start)
    (i : Fin (p.m - 1)) (k : Fin count) (test : ExecutedTest p)
    (htest : executedTestOfRound rate
      ((runDownObservation start count hspan i input).2 k) = some test) :
    ∃ state memory,
      (ReferenceActiveHorizonMeasurability.runOfInput start k.val (by omega) input).finalState.followers i =
        .ordinary state memory :=
  executedTest_prefix_ordinary start count hspan input i k test htest k.val le_rfl

section Generated

variable (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
  (i : Fin (p.m - 1)) (alpha : ℕ) (halpha : s < alpha) (halphaT : alpha < p.T)
  (candidate : AffineChannelLaw.Word (AffineBatchDecoder.width p))
  (q : ℕ) (hq : 1 ≤ q) (hqQ : q ≤ AffineBatchDecoder.quota p)
  (x : LaunchSource rate rewards C_star C_h s hs)

/-- The actual marker, with its cap removed using q-1<Q. Its boundary is the
original completed round at alpha-1 and ordinary incoming alpha, and its prior
tests are the uncapped restriction of the same full run. -/
theorem sourcePrefixMarker_iff
    (r : Fin p.T) (hsr : s ≤ r.val) (har : alpha ≤ r.val) :
    ReferenceGeneratedDownPrefixEvent.sourcePrefixMarker rate rewards C_star C_h
      r s hs hsr i alpha halpha har candidate q hq hqQ x ↔
    generatedSourceBatchBoundary rate rewards C_star C_h s hs i alpha halpha halphaT x ∧
    (∃ state memory,
      (ReferenceActiveHorizonMeasurability.runOfInput s (r.val - s) (by omega)
        (generatedSourceRunInput rate rewards C_star C_h s hs x)).finalState.followers i =
          .ordinary state memory) ∧
    let prior := ((List.ofFn (generatedSourceObservation rate rewards C_star C_h s hs i x).2).take
      (r.val - s)).filterMap (fun round =>
        if alpha ≤ round.1.val then executedTestOfRound rate round else none)
    prior.length = q - 1 ∧ ∀ test ∈ prior, ExecutedTest.good candidate test := by
  unfold ReferenceGeneratedDownPrefixEvent.sourcePrefixMarker
  dsimp only
  rw [ReferenceGeneratedDownQthCalendar.generatedSourceObservation_prefix_round
    rewards C_star C_h s hs i x r hsr ⟨alpha - 1 - s, by omega⟩]
  change generatedSourceBatchBoundary rate rewards C_star C_h s hs i alpha halpha halphaT x ∧
      _ ∧ _ ↔ _
  rw [ReferenceGeneratedDownQthCalendar.sourcePrefixTests_eq_fullRunPrefix
    rewards C_star C_h s hs i alpha halpha halphaT x r hsr har]
  let prior := ((List.ofFn (generatedSourceObservation rate rewards C_star C_h s hs i x).2).take
    (r.val - s)).filterMap (fun round =>
      if alpha ≤ round.1.val then executedTestOfRound rate round else none)
  change (_ ∧ _ ∧ (prior.take _).length = q - 1 ∧ (prior.take _).length < _ ∧
    ∀ test ∈ prior.take _, ExecutedTest.good candidate test) ↔
      (_ ∧ _ ∧ prior.length = q - 1 ∧ ∀ test ∈ prior, ExecutedTest.good candidate test)
  constructor
  · rintro ⟨hb, ho, hlen, _hsmall, hg⟩
    have hraw : prior.length = q - 1 := by
      rw [List.length_take] at hlen
      omega
    have htake : prior.take (AffineBatchDecoder.quota p) = prior :=
      List.take_of_length_le (by omega)
    exact ⟨hb, ho, hraw, by simpa only [htake] using hg⟩
  · rintro ⟨hb, ho, hlen, hg⟩
    have htake : prior.take (AffineBatchDecoder.quota p) = prior :=
      List.take_of_length_le (by omega)
    exact ⟨hb, ho, by rw [htake]; exact hlen,
      by rw [htake, hlen]; omega, by simpa only [htake] using hg⟩

/-- D_q is exactly the union of the real local q-th events. The ordinary
incoming branch is produced from current execution, including when that same
round later fails; no ordinary successor or no-failure run is assumed. -/
theorem generatedDownD_iff_exists_qth :
    generatedDownD rate rewards C_star C_h s q hs i alpha halpha halphaT candidate x ↔
      ∃ r : Fin p.T, ∃ hsr : s ≤ r.val, ∃ har : alpha ≤ r.val,
        ReferenceGeneratedDownQthCalendar.generatedDownQthAt rewards C_star C_h s hs
          i alpha halpha halphaT candidate q hq hqQ x r hsr har := by
  let code := generatedSourceObservation rate rewards C_star C_h s hs i x
  let rounds := List.ofFn code.2
  let choose (round : DownRoundCode p rate) : Option (ExecutedTest p) :=
    if alpha ≤ round.1.val then executedTestOfRound rate round else none
  have hlength : rounds.length = p.T - s := List.length_ofFn
  constructor
  · rintro ⟨hboundary, hsurvives⟩
    change survives candidate q ((rounds.filterMap choose).take _) at hsurvives
    have hraw := (survives_take candidate q _ hqQ (rounds.filterMap choose)).mp hsurvives
    obtain ⟨m, hm, test, hcurrent, hcount, hgood, htestGood⟩ :=
      survives_filterMap_location candidate choose rounds q hq hraw
    have hmT : m < p.T - s := by omega
    let r : Fin p.T := ⟨s + m, by omega⟩
    have hsr : s ≤ r.val := by dsimp [r]; omega
    have hindex : r.val - s = m := by dsimp [r]; omega
    have hround : rounds[m] = code.2 ⟨m, hmT⟩ := List.getElem_ofFn ..
    have htime : (code.2 ⟨m, hmT⟩).1 = r := by
      have ht := ReferenceGeneratedDownQthCalendar.generatedSourceObservation_round_time
        rewards C_star C_h s hs i x r hsr
      simpa only [hindex] using ht
    have har : alpha ≤ r.val := by
      dsimp only [choose] at hcurrent
      rw [hround, htime] at hcurrent
      by_contra hn
      rw [ite_eq_right hn] at hcurrent
      cases hcurrent
    have hexecuted : executedTestOfRound rate (code.2 ⟨r.val - s, by omega⟩) = some test := by
      dsimp only [choose] at hcurrent
      rw [hround, htime, ite_eq_left har] at hcurrent
      simpa only [hindex] using hcurrent
    have hordinary := executedTest_incoming_ordinary s (p.T - s) (by omega)
      (generatedSourceRunInput rate rewards C_star C_h s hs x) i
      ⟨r.val - s, by omega⟩ test hexecuted
    refine ⟨r, hsr, har, ?_, test, hexecuted, htestGood⟩
    apply (sourcePrefixMarker_iff rewards C_star C_h s hs i alpha halpha halphaT
      candidate q hq hqQ x r hsr har).mpr
    refine ⟨hboundary, hordinary, ?_, ?_⟩
    · simpa only [hindex] using hcount
    · simpa only [hindex] using hgood
  · rintro ⟨r, hsr, har, hmarker, test, hexecuted, htestGood⟩
    obtain ⟨hboundary, _hordinary, hcount, hgood⟩ :=
      (sourcePrefixMarker_iff rewards C_star C_h s hs i alpha halpha halphaT
        candidate q hq hqQ x r hsr har).mp hmarker
    have hm : r.val - s < rounds.length := by rw [hlength]; omega
    have hround : rounds[r.val - s] = code.2 ⟨r.val - s, by omega⟩ :=
      List.getElem_ofFn ..
    have htime := ReferenceGeneratedDownQthCalendar.generatedSourceObservation_round_time
      rewards C_star C_h s hs i x r hsr
    have hcurrent : choose rounds[r.val - s] = some test := by
      dsimp only [choose]
      rw [hround, htime, ite_eq_left har]
      exact hexecuted
    have hsurvives := survives_of_location candidate choose rounds (r.val - s) hm
      test hcurrent hgood htestGood
    change ((rounds.take (r.val - s)).filterMap choose).length = q - 1 at hcount
    rw [hcount, Nat.sub_add_cancel hq] at hsurvives
    exact ⟨hboundary, (survives_take candidate q _ hqQ _).mpr hsurvives⟩

/-- Erasing only the current candidate hash preserves the actual marker,
executed test, and original sent-word exclusion. -/
theorem generatedDownQthAt_implies_sent
    (r : Fin p.T) (hsr : s ≤ r.val) (har : alpha ≤ r.val)
    (h : ReferenceGeneratedDownQthCalendar.generatedDownQthAt rewards C_star C_h s hs
      i alpha halpha halphaT candidate q hq hqQ x r hsr har) :
    ReferenceGeneratedDownQthCalendar.generatedDownQthAtSent rewards C_star C_h s hs
      i alpha halpha halphaT candidate q hq hqQ x r hsr har := by
  obtain ⟨hmarker, test, hexecuted, hgood⟩ := h
  exact ⟨hmarker, test, hexecuted, hgood.1⟩

/-- Q's retained-bank identity restored to the original full source. The bank
at alpha is empty; the current incoming bank consists of precisely the q-1
previous stamped tests, and no completed bank has been added since alpha. -/
theorem generatedDownQthAt_bank_identity
    (r : Fin p.T) (hsr : s ≤ r.val) (har : alpha ≤ r.val)
    (h : ReferenceGeneratedDownQthCalendar.generatedDownQthAt rewards C_star C_h s hs
      i alpha halpha halphaT candidate q hq hqQ x r hsr har) :
    let input := generatedSourceRunInput rate rewards C_star C_h s hs x
    let tests := observedTestsFrom rate alpha (r.val - s)
      (runDownObservation s (r.val - s) (by omega) i input)
    ∃ stateA memoryA,
      (ReferenceActiveHorizonMeasurability.runOfInput s (alpha - s) (by omega) input).finalState.followers i = .ordinary stateA memoryA ∧
      stateA.downBatch.pending = [] ∧
      ∃ stateR memoryR,
        (ReferenceActiveHorizonMeasurability.runOfInput s (r.val - s) (by omega) input).finalState.followers i = .ordinary stateR memoryR ∧
        stateR.downBatch.pending = tests.map ReferenceGeneratedDownPrefixList.stampedTest ∧
        stateR.downBatch.completed = stateA.downBatch.completed ∧
        stateR.downBatch.pending.length = q - 1 := by
  let j := ActualInitializationPhysicalStep.selectedRowIndex p x.1
  let control0 : ContinuousLearningRows.TimeControl p := (x.1.1.2 j).2 r
  let retained := ReferenceRetainedBoundaryMeasurability.retainedLaunchStartInputOfSource
    rate rewards C_star C_h j r s hsr control0 x.1 rfl x.2.1 x.2.2
  have hinput := ReferenceGeneratedDownPrefixEvent.retainedPrefixRunInput_eq_source
    rate rewards C_star C_h j r s hs hsr x rfl retained rfl
  have hbank := ReferenceGeneratedDownQthCalendar.generatedDownQthAt_retainedBank
    rewards C_star C_h s hs i alpha halpha halphaT candidate q hq hqQ x r hsr har h
  dsimp only at hbank
  let retainedInput := ReferenceGeneratedDownPrefixEvent.retainedPrefixRunInput
    rate rewards C_star C_h j r s hsr control0 retained
  change ∃ stateA memoryA,
    (ReferenceActiveHorizonMeasurability.runOfInput s (alpha - s) (by omega)
      retainedInput).finalState.followers i = .ordinary stateA memoryA ∧
    stateA.downBatch.pending = [] ∧ ∃ stateR memoryR,
      (ReferenceActiveHorizonMeasurability.runOfInput s (r.val - s) (by omega)
        retainedInput).finalState.followers i = .ordinary stateR memoryR ∧
      stateR.downBatch.pending = (observedTestsFrom rate alpha (r.val - s)
        (runDownObservation s (r.val - s) (by omega) i retainedInput)).map
          ReferenceGeneratedDownPrefixList.stampedTest ∧
      stateR.downBatch.completed = stateA.downBatch.completed at hbank
  change retainedInput = generatedSourceRunInput rate rewards C_star C_h s hs x at hinput
  rw [hinput] at hbank
  obtain ⟨stateA, memoryA, hA, hreset, stateR, memoryR, hR, hpending, hcompleted⟩ := hbank
  refine ⟨stateA, memoryA, hA, hreset, stateR, memoryR, hR, hpending, hcompleted, ?_⟩
  rw [hpending, List.length_map]
  exact h.1.2.2.1

/-- Any actual hash-erased q-th event lies in D_(q-1) on this same source.
At q=1 the conclusion is the real boundary event via D.generatedDownD_zero. -/
theorem generatedDownQthAtSent_implies_previous
    (r : Fin p.T) (hsr : s ≤ r.val) (har : alpha ≤ r.val)
    (h : ReferenceGeneratedDownQthCalendar.generatedDownQthAtSent rewards C_star C_h s hs
      i alpha halpha halphaT candidate q hq hqQ x r hsr har) :
    generatedDownD rate rewards C_star C_h s (q - 1) hs i alpha halpha halphaT candidate x := by
  obtain ⟨hmarker, test, hexecuted, _hsent⟩ := h
  obtain ⟨hboundary, _hordinary, hcount, hgood⟩ :=
    (sourcePrefixMarker_iff rewards C_star C_h s hs i alpha halpha halphaT
      candidate q hq hqQ x r hsr har).mp hmarker
  by_cases hqOne : q = 1
  · subst q
    exact (generatedDownD_zero rate rewards C_star C_h s hs i alpha halpha halphaT
      candidate x).mpr hboundary
  · let code := generatedSourceObservation rate rewards C_star C_h s hs i x
    let rounds := List.ofFn code.2
    let choose (round : DownRoundCode p rate) : Option (ExecutedTest p) :=
      if alpha ≤ round.1.val then executedTestOfRound rate round else none
    have hm : r.val - s < rounds.length := by
      have hlength : rounds.length = p.T - s := List.length_ofFn
      omega
    have hround : rounds[r.val - s] = code.2 ⟨r.val - s, by omega⟩ :=
      List.getElem_ofFn ..
    have htime := ReferenceGeneratedDownQthCalendar.generatedSourceObservation_round_time
      rewards C_star C_h s hs i x r hsr
    have hcurrent : choose rounds[r.val - s] = some test := by
      dsimp only [choose]
      rw [hround, htime, ite_eq_left har]
      exact hexecuted
    have hsurvives := survives_prior_of_location candidate choose rounds (r.val - s)
      hm test hcurrent hgood
    change ((rounds.take (r.val - s)).filterMap choose).length = q - 1 at hcount
    rw [hcount] at hsurvives
    exact ⟨hboundary, (survives_take candidate (q - 1) _ (by omega) _).mpr hsurvives⟩

/-- Strong events inherit the existing actual Sent uniqueness. -/
theorem generatedDownQthAt_unique
    (r₁ r₂ : Fin p.T) (hsr₁ : s ≤ r₁.val) (har₁ : alpha ≤ r₁.val)
    (hsr₂ : s ≤ r₂.val) (har₂ : alpha ≤ r₂.val)
    (h₁ : ReferenceGeneratedDownQthCalendar.generatedDownQthAt rewards C_star C_h s hs
      i alpha halpha halphaT candidate q hq hqQ x r₁ hsr₁ har₁)
    (h₂ : ReferenceGeneratedDownQthCalendar.generatedDownQthAt rewards C_star C_h s hs
      i alpha halpha halphaT candidate q hq hqQ x r₂ hsr₂ har₂) : r₁ = r₂ := by
  exact ReferenceGeneratedDownQthCalendar.generatedDownQthAtSent_unique rewards C_star C_h
    s hs i alpha halpha halphaT candidate q hq hqQ x r₁ r₂ hsr₁ har₁ hsr₂ har₂
    (generatedDownQthAt_implies_sent rewards C_star C_h s hs i alpha halpha halphaT
      candidate q hq hqQ x r₁ hsr₁ har₁ h₁)
    (generatedDownQthAt_implies_sent rewards C_star C_h s hs i alpha halpha halphaT
      candidate q hq hqQ x r₂ hsr₂ har₂ h₂)

/-- On D_q there is exactly one real q-th round, and conversely. -/
theorem generatedDownD_iff_existsUnique_qth :
    generatedDownD rate rewards C_star C_h s q hs i alpha halpha halphaT candidate x ↔
      ∃! r : {r : Fin p.T // alpha ≤ r.val},
        ReferenceGeneratedDownQthCalendar.generatedDownQthAt rewards C_star C_h s hs
          i alpha halpha halphaT candidate q hq hqQ x r.1 (by omega) r.2 := by
  rw [generatedDownD_iff_exists_qth rewards C_star C_h s hs i alpha halpha halphaT
    candidate q hq hqQ x]
  constructor
  · rintro ⟨r, hsr, har, h⟩
    refine ⟨⟨r, har⟩, h, ?_⟩
    intro t ht
    apply Subtype.ext
    exact generatedDownQthAt_unique rewards C_star C_h s hs i alpha halpha halphaT
      candidate q hq hqQ x t.1 r (by omega) t.2 hsr har ht h
  · rintro ⟨r, h, _hunique⟩
    exact ⟨r.1, by omega, r.2, h⟩

/-- Exact pointwise finite strong-indicator identity on the original source. -/
theorem generatedDownQthAt_indicator_sum
    : let Valid := {r : Fin p.T // alpha ≤ r.val}
      let detects (r : Valid) := ReferenceGeneratedDownQthCalendar.generatedDownQthAt
        rewards C_star C_h s hs i alpha halpha halphaT candidate q hq hqQ x
          r.1 (by omega) r.2
      (∑ r : Valid, if detects r then (1 : ℝ) else 0) =
        if generatedDownD rate rewards C_star C_h s q hs i alpha halpha halphaT candidate x
          then 1 else 0 := by
  dsimp only
  let Valid := {r : Fin p.T // alpha ≤ r.val}
  let detects (r : Valid) := ReferenceGeneratedDownQthCalendar.generatedDownQthAt
    rewards C_star C_h s hs i alpha halpha halphaT candidate q hq hqQ x
      r.1 (by omega) r.2
  by_cases hD : generatedDownD rate rewards C_star C_h s q hs i alpha halpha halphaT candidate x
  · obtain ⟨r, hr, huniq⟩ := (generatedDownD_iff_existsUnique_qth rewards C_star C_h
      s hs i alpha halpha halphaT candidate q hq hqQ x).mp hD
    have hsum : (∑ t : Valid, if detects t then (1 : ℝ) else 0) =
        if detects r then 1 else 0 := by
      apply Finset.sum_eq_single r
      · intro t _ht hne
        apply ite_eq_right
        intro hdetect
        exact hne (huniq t hdetect)
      · intro hnot
        exact False.elim (hnot (Finset.mem_univ r))
    rw [ite_eq_left hD]
    exact hsum.trans (ite_eq_left hr)
  · rw [ite_eq_right hD]
    apply Finset.sum_eq_zero
    intro r _hr
    apply ite_eq_right
    intro hdetect
    exact hD ((generatedDownD_iff_exists_qth rewards C_star C_h s hs i alpha halpha
      halphaT candidate q hq hqQ x).mpr ⟨r.1, by omega, r.2, hdetect⟩)

/-- The hash-erased finite sum is bounded by the actual D_(q-1) indicator.
This uses Q's proved at-most-one bound and the same-source existence implication. -/
theorem generatedDownQthAtSent_indicator_sum_le_previous
    : let Valid := {r : Fin p.T // alpha ≤ r.val}
      let detects (r : Valid) := ReferenceGeneratedDownQthCalendar.generatedDownQthAtSent
        rewards C_star C_h s hs i alpha halpha halphaT candidate q hq hqQ x
          r.1 (by omega) r.2
      (∑ r : Valid, if detects r then (1 : ℝ) else 0) ≤
        if generatedDownD rate rewards C_star C_h s (q - 1) hs i alpha halpha halphaT
          candidate x then 1 else 0 := by
  dsimp only
  let Valid := {r : Fin p.T // alpha ≤ r.val}
  let detects (r : Valid) := ReferenceGeneratedDownQthCalendar.generatedDownQthAtSent
    rewards C_star C_h s hs i alpha halpha halphaT candidate q hq hqQ x
      r.1 (by omega) r.2
  by_cases hD : generatedDownD rate rewards C_star C_h s (q - 1) hs i alpha halpha halphaT
      candidate x
  · rw [ite_eq_left hD]
    have hbound := ReferenceGeneratedDownQthCalendar.generatedDownQthAtSent_indicator_sum_le_one
      rewards C_star C_h s hs i alpha halpha halphaT candidate q hq hqQ x
    dsimp only at hbound
    simpa only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero] using hbound
  · rw [ite_eq_right hD]
    apply le_of_eq
    apply Finset.sum_eq_zero
    intro r _hr
    apply ite_eq_right
    intro hdetect
    exact hD (generatedDownQthAtSent_implies_previous rewards C_star C_h s hs i alpha
      halpha halphaT candidate q hq hqQ x r.1 (by omega) r.2 hdetect)

end Generated

end Bandits.Support.ReferenceGeneratedDownQthDecomposition

end
