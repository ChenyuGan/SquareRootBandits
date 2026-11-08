/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedDownPrefixEvent
public import Bandits.Support.ReferenceGeneratedDownPrefixList

import Lean.Elab.Tactic.Omega
import Mathlib.Data.Fin.Tuple.Take

/-!
# The q-th test on the generated fresh-reset DOWN calendar

Sources: `sources/zip4/manuscript/appendix_a_local_protocol.tex:112-138`,
`sources/zip4/manuscript/05_binary_transport.tex:20-42`,
`sources/zip4/manuscript/07_public_setup.tex:127-142`, and
`sources/zip4/manuscript/08_main_theorem.tex:29-42`.

The predicates in this module refer to D's original generated seed, full
continuous rows, selected row, private data, rewards, and physical run to `T`.
The prefix observations are restrictions of that run. No probability law or
stopping rule is introduced here.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Bandits.Support.ReferenceGeneratedDownQthCalendar

open Bandits.Support.ConstructorDimensions
open ReferenceGeneratedDownBatchCalendar
open ReferenceDownCompletedAmbiguityMeasurability

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceGeneratedDownBatchCalendar.RateInput
abbrev LaunchSource {p : Parameters} (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T) :=
  ReferenceGeneratedDownBatchCalendar.LaunchSource rate rewards C_star C_h s hs

variable {p : Parameters} {rate : RateInput p}

/-- The literal local q-th event at physical round `r` in D's original
generated run. The preceding marker is E's actual source marker; the current
test is read from the same full run and retains its original sent-word tag. -/
def generatedDownQthAt
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (i : Fin (p.m - 1)) (alpha : ℕ) (halpha : s < alpha)
    (_halphaT : alpha < p.T)
    (candidate : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (q : ℕ) (hq : 1 ≤ q) (hqQ : q ≤ AffineBatchDecoder.quota p)
    (x : LaunchSource rate rewards C_star C_h s hs)
    (r : Fin p.T) (hsr : s ≤ r.val) (halphaR : alpha ≤ r.val) : Prop :=
  ReferenceGeneratedDownPrefixEvent.sourcePrefixMarker rate rewards C_star C_h
      r s hs hsr i alpha
      (by omega) halphaR candidate q hq hqQ x ∧
    ∃ test : ExecutedTest p,
      executedTestOfRound rate
        ((generatedSourceObservation rate rewards C_star C_h s hs i x).2
          ⟨r.val - s, by omega⟩) = some test ∧
      ExecutedTest.good candidate test

/-- The same source marker and current executed test, with only the current
candidate hash equation erased. The actual sent-word exclusion remains. -/
def generatedDownQthAtSent
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (i : Fin (p.m - 1)) (alpha : ℕ) (halpha : s < alpha)
    (_halphaT : alpha < p.T)
    (candidate : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (q : ℕ) (hq : 1 ≤ q) (hqQ : q ≤ AffineBatchDecoder.quota p)
    (x : LaunchSource rate rewards C_star C_h s hs)
    (r : Fin p.T) (hsr : s ≤ r.val) (halphaR : alpha ≤ r.val) : Prop :=
  ReferenceGeneratedDownPrefixEvent.sourcePrefixMarker rate rewards C_star C_h
      r s hs hsr i alpha
      (by omega) halphaR candidate q hq hqQ x ∧
    ∃ test : ExecutedTest p,
      executedTestOfRound rate
        ((generatedSourceObservation rate rewards C_star C_h s hs i x).2
          ⟨r.val - s, by omega⟩) = some test ∧
      test.sent ≠ some candidate

private theorem ofFn_prefix {α : Type*} {n m : ℕ} (h : m ≤ n) (f : Fin n → α) :
    List.ofFn (fun k : Fin m => f ⟨k.val, by omega⟩) = (List.ofFn f).take m := by
  have hf : (fun k : Fin m => f ⟨k.val, by omega⟩) = Fin.take m h f := by
    funext k
    rfl
  rw [hf]
  exact Fin.ofFn_take_eq_take_ofFn h f

/-- Every observation before `r` is the corresponding observation of D's
whole run from the original launch. This is the finite-array restriction
identity, including the original round's diagnostic fields. -/
theorem generatedSourceObservation_prefix_round
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (i : Fin (p.m - 1)) (x : LaunchSource rate rewards C_star C_h s hs)
    (r : Fin p.T) (hsr : s ≤ r.val) (k : Fin (r.val - s)) :
    (runDownObservation (p := p) (rate := rate) s (r.val - s) (by omega) i
        (generatedSourceRunInput rate rewards C_star C_h s hs x)).2 k =
      (generatedSourceObservation rate rewards C_star C_h s hs i x).2
        ⟨k.val, by omega⟩ := by
  rfl

/-- The index of physical round `r` in D's full observation array carries the
same original finite time coordinate `r`. -/
theorem generatedSourceObservation_round_time
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (i : Fin (p.m - 1)) (x : LaunchSource rate rewards C_star C_h s hs)
    (r : Fin p.T) (hsr : s ≤ r.val) :
    ((generatedSourceObservation rate rewards C_star C_h s hs i x).2
      ⟨r.val - s, by omega⟩).1 = r := by
  apply Fin.ext
  simp only [generatedSourceObservation, runDownObservation, roundDownObservation, prefixInput,
    ReferenceActiveHorizonMeasurability.runOfInput,
    ReferenceActivePhysicalHorizon.roundInputAt]
  omega

/-- E's tests on `[alpha,r)` are exactly the original tagged tests
from D's full observation array restricted to rounds before `r`. In particular,
the test's sent `Option` word is preserved. -/
theorem sourcePrefixTests_eq_fullRunPrefix
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (i : Fin (p.m - 1)) (alpha : ℕ) (_halpha : s < alpha)
    (_halphaT : alpha < p.T)
    (x : LaunchSource rate rewards C_star C_h s hs)
    (r : Fin p.T) (hsr : s ≤ r.val) (_halphaR : alpha ≤ r.val) :
    observedTestsFrom rate alpha (r.val - s)
      (runDownObservation (p := p) (rate := rate) s (r.val - s) (by omega) i
        (generatedSourceRunInput rate rewards C_star C_h s hs x)) =
    (((List.ofFn (generatedSourceObservation rate rewards C_star C_h s hs i x).2).take
        (r.val - s)).filterMap fun round =>
      if alpha ≤ round.1.val then executedTestOfRound rate round else none).take
        (AffineBatchDecoder.quota p) := by
  classical
  let shortCode := runDownObservation (p := p) (rate := rate) s (r.val - s) (by omega) i
    (generatedSourceRunInput rate rewards C_star C_h s hs x)
  let fullCode := generatedSourceObservation rate rewards C_star C_h s hs i x
  let choose (round : DownRoundCode p rate) : Option (ExecutedTest p) :=
    if alpha ≤ round.1.val then executedTestOfRound rate round else none
  have hprefix : List.ofFn shortCode.2 = (List.ofFn fullCode.2).take (r.val - s) := by
    have hround : ∀ k : Fin (r.val - s),
        shortCode.2 k = fullCode.2 ⟨k.val, by omega⟩ := by
      intro k
      rfl
    have hfunction : shortCode.2 = fun k : Fin (r.val - s) =>
        fullCode.2 ⟨k.val, by omega⟩ := funext hround
    rw [hfunction]
    exact ofFn_prefix (by omega) fullCode.2
  change ((List.ofFn shortCode.2).filterMap choose).take _ = _
  rw [hprefix]

/-- E's reset and ordinary incoming state at `alpha` are D's literal
generated-source boundary. The completed diagnostic is the same indexed
round in the actual full run. -/
theorem sourcePrefixMarker_boundary
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (i : Fin (p.m - 1)) (alpha : ℕ) (halpha : s < alpha)
    (halphaT : alpha < p.T)
    (candidate : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (q : ℕ) (hq : 1 ≤ q) (hqQ : q ≤ AffineBatchDecoder.quota p)
    (x : LaunchSource rate rewards C_star C_h s hs)
    (r : Fin p.T) (hsr : s ≤ r.val) (halphaR : alpha ≤ r.val)
    (hmarker : ReferenceGeneratedDownPrefixEvent.sourcePrefixMarker rate rewards
      C_star C_h r s hs hsr i alpha halpha halphaR candidate q hq hqQ x) :
    generatedSourceBatchBoundary rate rewards C_star C_h s hs i alpha halpha halphaT x := by
  unfold ReferenceGeneratedDownPrefixEvent.sourcePrefixMarker at hmarker
  dsimp only at hmarker
  have hround := generatedSourceObservation_prefix_round rewards C_star C_h s hs i x r hsr
    ⟨alpha - 1 - s, by omega⟩
  rw [hround] at hmarker
  change completedBatchAtRound rate
      ((generatedSourceObservation rate rewards C_star C_h s hs i x).2
        ⟨alpha - 1 - s, by omega⟩) ∧
    ∃ state memory,
      (ReferenceActiveHorizonMeasurability.runOfInput (p := p) (rate := rate)
        s (alpha - s) (by omega)
        (generatedSourceRunInput rate rewards C_star C_h s hs x)).finalState.followers i =
          .ordinary state memory
  exact hmarker.1

/-- Executed tests on any original suffix keep the strict order of their
physical timestamps. This is L's diagnostic inversion and the actual canonical
calendar order; it does not assume that the successor survives. -/
theorem generatedSourceRun_executedTests_chronological
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (i : Fin (p.m - 1)) (alpha : ℕ) (halpha : s ≤ alpha)
    (x : LaunchSource rate rewards C_star C_h s hs) :
    (((generatedSourceRun rate rewards C_star C_h s hs x).records.drop (alpha - s)).filterMap
      (fun record => executedTestOfRound rate
        (roundDownObservation record.input i))).Pairwise
      (fun earlier later => earlier.time.val < later.time.val) := by
  let input := generatedSourceRunInput rate rewards C_star C_h s hs x
  exact ReferenceGeneratedDownPrefixList.run_executedTests_chronological
    input.val.1 input.val.2.1 input.val.2.2.1 input.val.2.2.2 s (p.T - s)
    (by omega) input.property i (alpha - s)

/-- A detecting prefix consumes L's actual retained-bank identity. The
retained launch input is constructed from the same source's original selected
row and launch evidence; no source-equality or boundary premise is supplied. -/
theorem generatedDownQthAt_retainedBank
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (i : Fin (p.m - 1)) (alpha : ℕ) (halpha : s < alpha)
    (halphaT : alpha < p.T)
    (candidate : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (q : ℕ) (hq : 1 ≤ q) (hqQ : q ≤ AffineBatchDecoder.quota p)
    (x : LaunchSource rate rewards C_star C_h s hs)
    (r : Fin p.T) (hsr : s ≤ r.val) (halphaR : alpha ≤ r.val)
    (hlocal : generatedDownQthAt rewards C_star C_h s hs i alpha halpha halphaT
      candidate q hq hqQ x r hsr halphaR) :
    let j := ActualInitializationPhysicalStep.selectedRowIndex p x.1
    let control0 : ContinuousLearningRows.TimeControl p := (x.1.1.2 j).2 r
    let retained := ReferenceRetainedBoundaryMeasurability.retainedLaunchStartInputOfSource
      rate rewards C_star C_h j r s hsr control0 x.1 rfl x.2.1 x.2.2
    let source := ReferenceGeneratedActivePrefixFactor.splitSource j r control0 retained.1
    let seed := ReferenceRetainedBoundaryMeasurability.retainedGeneratedActiveSeed
      rate rewards C_star C_h j r s hsr control0 retained
    let mode := (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
      rate rewards C_star C_h j r control0 retained.1 retained.2.1 s hsr retained.2.2).2.1
    ∃ stateA memoryA,
      (ReferenceActivePhysicalHorizon.run seed source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s
        (alpha - s) (by omega) mode).finalState.followers i = .ordinary stateA memoryA ∧
      stateA.downBatch.pending = [] ∧
      ∃ stateR memoryR,
        (ReferenceActivePhysicalHorizon.run seed source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s
          (r.val - s) (by omega) mode).finalState.followers i = .ordinary stateR memoryR ∧
        stateR.downBatch.pending =
          (retainedBatchPrefix rate rewards C_star C_h j r s hs hsr control0
            i alpha halpha halphaR retained).map ReferenceGeneratedDownPrefixList.stampedTest ∧
        stateR.downBatch.completed = stateA.downBatch.completed := by
  dsimp only
  let j := ActualInitializationPhysicalStep.selectedRowIndex p x.1
  let control0 : ContinuousLearningRows.TimeControl p := (x.1.1.2 j).2 r
  let retained := ReferenceRetainedBoundaryMeasurability.retainedLaunchStartInputOfSource
    rate rewards C_star C_h j r s hsr control0 x.1 rfl x.2.1 x.2.2
  have hselected : ActualInitializationPhysicalStep.selectedRowIndex p x.1 = j := rfl
  change ReferenceGeneratedDownPrefixEvent.sourcePrefixMarker rate rewards C_star C_h
      r s hs hsr i alpha halpha halphaR candidate q hq hqQ x ∧ _ at hlocal
  have hretainedMarker :=
    (ReferenceGeneratedDownPrefixEvent.sourcePrefixMarker_eq_retained
      rate rewards C_star C_h j r s hs hsr control0 i alpha halpha halphaR
      candidate q hq hqQ x hselected).mp hlocal.1
  change retainedBatchBoundary rate rewards C_star C_h j r s hs hsr control0
      i alpha halpha halphaR retained ∧
    (∃ state memory, retainedBatchIncoming rate rewards C_star C_h j r s hs hsr
      control0 i alpha halpha halphaR retained = .ordinary state memory) ∧
    (retainedBatchPrefix rate rewards C_star C_h j r s hs hsr control0
      i alpha halpha halphaR retained).length = q - 1 ∧
    (retainedBatchPrefix rate rewards C_star C_h j r s hs hsr control0
      i alpha halpha halphaR retained).length < AffineBatchDecoder.quota p ∧ _
    at hretainedMarker
  rcases hretainedMarker with ⟨hboundary, ⟨stateR, memoryR, hordinary⟩,
    _hcount, hsmall, _hgood⟩
  have hbank := ReferenceGeneratedDownPrefixList.retainedBatchPrefix_bank_identity
    rewards C_star C_h j r s hs hsr control0 i alpha halpha halphaR retained
    hboundary stateR memoryR hordinary hsmall
  rcases hbank with ⟨_hselected, _hprefix, _hentries, _hsmall, _hchronological,
    hresult⟩
  rcases hresult with ⟨stateA, memoryA, hordinaryA, hreset, hpending, hcompleted,
    _hendpointA, _hendpointR, _hpendingFinal⟩
  exact ⟨stateA, memoryA, hordinaryA, hreset, stateR, memoryR, hordinary, hpending, hcompleted⟩

/-- If two candidate locations satisfy the same preceding-count marker, the
earlier current executed test forces the later prefix count to be at least one
larger. This uses the indexed physical observations, not a second trace. -/
private theorem filterMap_take_current_le
    {α β : Type*} {b : β} (l : List α) (f : α → Option β) (m n : ℕ)
    (hn : n ≤ l.length) (hmn : m < n) (hcurrent : f l[m] = some b) :
    ((l.take m).filterMap f).length + 1 ≤ ((l.take n).filterMap f).length := by
  have hm : m < l.length := lt_of_lt_of_le hmn hn
  have hnext : l.take (m + 1) = l.take m ++ [l[m]] :=
    (List.take_concat_get' l m hm).symm
  have hlenLeft : (l.take (m + 1)).length = m + 1 := by
    simp only [List.length_take, Nat.min_eq_left (by omega : m + 1 ≤ l.length)]
  have hsplit : l.take n = l.take (m + 1) ++ (l.drop (m + 1)).take (n - (m + 1)) := by
    nth_rw 1 [← List.take_append_drop (m + 1) l]
    rw [List.take_append]
    rw [List.take_of_length_le (by rw [hlenLeft]; omega)]
    rw [hlenLeft]
  have hfirst : ((l.take m).filterMap f).length + 1 ≤
      ((l.take (m + 1)).filterMap f).length := by
    rw [hnext, List.filterMap_append]
    simp [hcurrent]
  have htail : ((l.take (m + 1)).filterMap f).length ≤
      ((l.take n).filterMap f).length := by
    rw [hsplit, List.filterMap_append]
    rw [List.length_append]
    exact Nat.le_add_right _ _
  exact hfirst.trans htail

/-- The hash-erased local events are pointwise disjoint in physical time.
The proof uses the exact `[alpha,r)` prefix counts from E and the retained
original executed test at the earlier round. -/
theorem generatedDownQthAtSent_unique
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (i : Fin (p.m - 1)) (alpha : ℕ) (halpha : s < alpha)
    (halphaT : alpha < p.T)
    (candidate : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (q : ℕ) (hq : 1 ≤ q) (hqQ : q ≤ AffineBatchDecoder.quota p)
    (x : LaunchSource rate rewards C_star C_h s hs)
    (r₁ r₂ : Fin p.T) (hsr₁ : s ≤ r₁.val) (halphaR₁ : alpha ≤ r₁.val)
    (hsr₂ : s ≤ r₂.val) (halphaR₂ : alpha ≤ r₂.val)
    (h₁ : generatedDownQthAtSent rewards C_star C_h s hs i alpha halpha halphaT
      candidate q hq hqQ x r₁ hsr₁ halphaR₁)
    (h₂ : generatedDownQthAtSent rewards C_star C_h s hs i alpha halpha halphaT
      candidate q hq hqQ x r₂ hsr₂ halphaR₂) : r₁ = r₂ := by
  by_contra hne
  have htimes : r₁.val < r₂.val ∨ r₂.val < r₁.val := by omega
  let fullCode := generatedSourceObservation rate rewards C_star C_h s hs i x
  let rounds := List.ofFn fullCode.2
  let choose (round : DownRoundCode p rate) : Option (ExecutedTest p) :=
    if alpha ≤ round.1.val then executedTestOfRound rate round else none
  have hroundsLength : rounds.length = p.T - s := by
    simp [rounds, fullCode, generatedSourceObservation]
  rcases htimes with h12 | h21
  · rcases h₁ with ⟨hmarker₁, ⟨test₁, htest₁, _⟩⟩
    rcases h₂ with ⟨hmarker₂, _⟩
    let m₁ := r₁.val - s
    let m₂ := r₂.val - s
    let raw₁ := (rounds.take m₁).filterMap choose
    let raw₂ := (rounds.take m₂).filterMap choose
    have hm₁ : m₁ < m₂ := by dsimp [m₁, m₂]; omega
    have hm₂ : m₂ ≤ rounds.length := by
      rw [hroundsLength]
      dsimp [m₂]
      omega
    have hlen₁ : (observedTestsFrom rate alpha m₁
        (runDownObservation (p := p) (rate := rate) s m₁ (by omega) i
          (generatedSourceRunInput rate rewards C_star C_h s hs x))).length = q - 1 := by
      exact hmarker₁.2.2.1
    have hlen₂ : (observedTestsFrom rate alpha m₂
        (runDownObservation (p := p) (rate := rate) s m₂ (by omega) i
          (generatedSourceRunInput rate rewards C_star C_h s hs x))).length = q - 1 := by
      exact hmarker₂.2.2.1
    rw [sourcePrefixTests_eq_fullRunPrefix rewards C_star C_h s hs i alpha halpha
      halphaT x r₁ hsr₁ halphaR₁] at hlen₁
    rw [sourcePrefixTests_eq_fullRunPrefix rewards C_star C_h s hs i alpha halpha
      halphaT x r₂ hsr₂ halphaR₂] at hlen₂
    change (raw₁.take (AffineBatchDecoder.quota p)).length = q - 1 at hlen₁
    change (raw₂.take (AffineBatchDecoder.quota p)).length = q - 1 at hlen₂
    have hraw₁ : raw₁.length = q - 1 := by
      rw [List.length_take] at hlen₁
      omega
    have hraw₂ : raw₂.length = q - 1 := by
      rw [List.length_take] at hlen₂
      omega
    have hroundTime := generatedSourceObservation_round_time rewards C_star C_h s hs
      i x r₁ hsr₁
    have hcurrent : choose rounds[m₁] = some test₁ := by
      have hm₁bound : m₁ < p.T - s := by
        dsimp [m₁]
        omega
      have hcode' : rounds[m₁] = fullCode.2 ⟨m₁, hm₁bound⟩ := by
        simp [rounds, List.getElem_ofFn, fullCode]
      have htime : (fullCode.2 ⟨m₁, hm₁bound⟩).1 = r₁ := by
        simpa [m₁, fullCode] using hroundTime
      dsimp [choose]
      rw [hcode', if_pos (by rw [htime]; exact halphaR₁), htest₁]
    have hmore := filterMap_take_current_le rounds choose m₁ m₂ hm₂ hm₁ hcurrent
    have : q - 1 + 1 ≤ q - 1 := by rw [hraw₁, hraw₂] at hmore; exact hmore
    omega
  · have hEq := generatedDownQthAtSent_unique rewards C_star C_h s hs i alpha halpha
      halphaT candidate q hq hqQ x r₂ r₁ hsr₂ halphaR₂ hsr₁ halphaR₁ h₂ h₁
    exact hne hEq.symm

/-- The hash-erased local events have a finite indicator sum bounded by one.
The index type contains only physical rounds at or after the original alpha. -/
theorem generatedDownQthAtSent_indicator_sum_le_one
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (i : Fin (p.m - 1)) (alpha : ℕ) (halpha : s < alpha)
    (halphaT : alpha < p.T)
    (candidate : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (q : ℕ) (hq : 1 ≤ q) (hqQ : q ≤ AffineBatchDecoder.quota p)
    (x : LaunchSource rate rewards C_star C_h s hs) :
    let Valid := {r : Fin p.T // alpha ≤ r.val}
    let detects (r : Valid) := generatedDownQthAtSent rewards C_star C_h s hs i
      alpha halpha halphaT candidate q hq hqQ x r.1 (by omega) r.2
    ((∑ r : Valid, if detects r then (1 : ℕ) else 0) : ℝ) ≤ 1 := by
  dsimp only
  let Valid := {r : Fin p.T // alpha ≤ r.val}
  let detects (r : Valid) := generatedDownQthAtSent rewards C_star C_h s hs i
    alpha halpha halphaT candidate q hq hqQ x r.1 (by omega) r.2
  have hcard : (Finset.univ.filter detects).card ≤ 1 := by
    apply Finset.card_le_one_iff.mpr
    intro r t hr ht
    rcases Finset.mem_filter.mp hr with ⟨_, hr⟩
    rcases Finset.mem_filter.mp ht with ⟨_, ht⟩
    apply Subtype.ext
    exact generatedDownQthAtSent_unique rewards C_star C_h s hs i alpha halpha
      halphaT candidate q hq hqQ x r.1 t.1 (by omega) r.2 (by omega) t.2 hr ht
  have hsumNat : (∑ r : Valid, if detects r then (1 : ℕ) else 0) =
      (Finset.univ.filter detects).card := by
    simpa using (Finset.sum_boole detects (Finset.univ : Finset Valid))
  have hboundNat : (∑ r : Valid, if detects r then (1 : ℕ) else 0) ≤ 1 := by
    rw [hsumNat]
    exact hcard
  exact_mod_cast hboundNat
