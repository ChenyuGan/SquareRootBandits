/-
Copyright (c) 2026 The Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceRetainedBoundaryMeasurability
public import Bandits.Support.ReferenceDownCompletedAmbiguityMeasurability
public import Bandits.Support.ReferenceSourceAffineHashHalf

import Lean.Elab.Tactic.Omega

/-!
# Actual generated fresh-reset DOWN batch calendars

Sources: `sources/zip4/manuscript/appendix_a_local_protocol.tex:112-153`,
`sources/zip4/manuscript/05_binary_transport.tex:20-42`,
`sources/zip4/manuscript/07_public_setup.tex:127-142`,
`sources/zip4/manuscript/08_main_theorem.tex:29-42`, and
`sources/zip4/manuscript/appendix_b_communication.tex:25-58`.

This module starts from the genuine generated crossing and corrected launch,
and projects executed DOWN diagnostics from the existing physical records.
Its countable observations retain real samples, actual expected words, raw
comparison presence, the complete diagnostic registers, and own feedback.
The work here is deterministic and Borel support only. It proves no affine
probability recurrence, source `E_false`/`E_amb` coverage, stopped-event bound,
or manuscript closure. `AdaptiveAffineBatchTail` is not in the public
transitive import closure, so the list predicates below are literal local
definitions rather than an imported policy experiment.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped Classical

namespace Bandits.Support.ReferenceGeneratedDownBatchCalendar

open Bandits.Support.ConstructorDimensions
open Bandits.Support.AffineChannelLaw

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput
variable {p : Parameters}

/-- The exact generated launch branch at elapsed time `s`. The source carrier
is unchanged: it still contains all rows, private arrays, and the original J.
The subtype records only the actual crossing and its actual elapsed index. -/
abbrev LaunchSource (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (_hs : s < p.T) :=
  {source : SourceInput p //
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true ∧
    ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed = s}

/-- The actual expected DOWN word and actual focal sample attached to one
executed positive diagnostic. The word may be absent; absence is retained as
`none`, which is different from the fixed candidate. -/
structure ExecutedTest (p : Parameters) where
  time : Fin p.T
  sample : Sample (AffineBatchDecoder.width p)
  sent : Option (Word (AffineBatchDecoder.width p))
  deriving DecidableEq

namespace ExecutedTest

/-- The source's per-test candidate condition. -/
def good (candidate : Word (AffineBatchDecoder.width p)) (test : ExecutedTest p) : Prop :=
  test.sent ≠ some candidate ∧ AffineChannelLaw.affineHash test.sample candidate = 1

end ExecutedTest

/-- The local source-shaped first-q predicate; no law or policy is supplied. -/
def survives (candidate : Word (AffineBatchDecoder.width p)) : ℕ → List (ExecutedTest p) → Prop
  | 0, _ => True
  | _ + 1, [] => False
  | q + 1, test :: rest =>
      ExecutedTest.good candidate test ∧ survives candidate q rest

/-- The literal current round code emitted by V. Only `rawComparison.isSome`
marks an executed decoder call. A stored `some false` is retained just like
`some true`; ordinary acceptance is not used as a call flag. -/
def executedTestOfRound
    (rate : RateInput p)
    (round : ReferenceDownCompletedAmbiguityMeasurability.DownRoundCode p rate) :
    Option (ExecutedTest p) := by
  classical
  let diagnostic := round.2.2.2
  let cut? := diagnostic.2.2
  exact match round.2.2.1, cut? with
    | some call, some cut =>
        if 0 < (ActualInitializationPhysicalStep.observationOfGrid p round.2.1).val.val ∧
            cut.2.2.1.isSome then
          some ⟨call.1, call.2.2.2.1, cut.2.1⟩
        else none
    | _, _ => none

/-- A completed batch is recognized from the logged decoder state and the
actual decoded transition. It does not inspect raw uniqueness, parsing,
acceptance, or later recovery. -/
def completedBatchAtRound
    (rate : RateInput p)
    (round : ReferenceDownCompletedAmbiguityMeasurability.DownRoundCode p rate) : Prop := by
  classical
  let diagnostic := round.2.2.2
  let call? := round.2.2.1
  let logged? := diagnostic.1
  let cut? := diagnostic.2.2
  exact ∃ call logged cut,
    call? = some call ∧ logged? = some logged ∧ cut? = some cut ∧
    call.1 = round.1 ∧ cut.2.2.1.isSome ∧
    0 < (ActualInitializationPhysicalStep.observationOfGrid p round.2.1).val.val ∧
    let before := FollowerDownMeasurability.decoderBatchOfCode logged.downBatch
    before.pending.length + 1 = AffineBatchDecoder.quota p ∧
    ReferenceDownCompletedAmbiguityMeasurability.decodedLoggedBank call logged =
      ⟨[], before.completed ++
        [before.pending ++ [⟨round.1, call.2.2.2.1⟩]]⟩

/-- The original whole source evaluated at its actual generated seed. The seed
is built from G's accepted launch-start subtype at the source's actual J and
control coordinate. -/
structure SourceLaunchContext
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (x : LaunchSource rate rewards C_star C_h s hs) where
  selected : Fin (M p)
  selected_eq : ActualInitializationPhysicalStep.selectedRowIndex p x.1 = selected
  time : Fin p.T
  time_val : time.val = s
  control : ContinuousLearningRows.TimeControl p
  remainder : ReferenceGeneratedActivePrefixFactor.Remainder p selected time
  remainder_mem : remainder ∈
    ReferenceFixedTimeSourceControlCoupling.fixedControlRemainderStratum p selected time
  launch_mem : remainder ∈ ReferenceInitializationControlRemainder.launchStartRemainderEvent
    rate rewards C_star C_h selected time s control
  source_eq : ReferenceGeneratedActivePrefixFactor.splitSource selected time control remainder = x.1

def sourceLaunchContext
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (x : LaunchSource rate rewards C_star C_h s hs) :
    SourceLaunchContext rate rewards C_star C_h s hs x := by
  let selected := ActualInitializationPhysicalStep.selectedRowIndex p x.1
  let time : Fin p.T := ⟨s, hs⟩
  let control : ContinuousLearningRows.TimeControl p := (x.1.1.2 selected).2 time
  let split := ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p selected time x.1
  have hselected : ActualInitializationPhysicalStep.selectedRowIndex p x.1 = selected := rfl
  have hrem : split.2 ∈
      ReferenceFixedTimeSourceControlCoupling.fixedControlRemainderStratum p selected time := by
    change PrivateSourceStreams.coordinatorIndex p (split.2.2.1.2) = selected
    rw [show split = ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p selected time x.1 from rfl,
      ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_private]
    change ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p x.1 = selected
    rw [ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex]
  have hstart : split.2 ∈
      ReferenceInitializationControlRemainder.launchStartRemainderEvent
        rate rewards C_star C_h selected time s control := by
    apply (ReferenceInitializationControlRemainder.launchStartRemainderEvent_iff_source
      rate rewards C_star C_h selected time control x.1 hselected s (by simp [time])).2
    exact x.2
  have hsource : ReferenceGeneratedActivePrefixFactor.splitSource selected time control split.2 = x.1 := by
    change (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p selected time).symm
      (control, split.2) = x.1
    exact (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p selected time).symm_apply_apply x.1
  exact ⟨selected, hselected, time, rfl, control, split.2, hrem, hstart, hsource⟩

/-- The G-produced seed on the exact launch context above. -/
def generatedSourceSeed
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (x : LaunchSource rate rewards C_star C_h s hs) :
    ReferenceActivePhysicalStep.State p rate := by
  let ctx := sourceLaunchContext rate rewards C_star C_h s hs x
  exact ReferenceGeneratedActivePrefixFactor.generatedActiveSeed
    rate rewards C_star C_h ctx.selected ctx.time ctx.control ctx.remainder
    ctx.remainder_mem s (by simp [ctx.time_val]) ctx.launch_mem

/-- The actual corrected-launch equality, all-active mode, and decoder seed
are inherited from G's exact generated seed specification. -/
theorem generatedSourceSeed_spec
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (x : LaunchSource rate rewards C_star C_h s hs) :
    ReferenceCorrectedInitializationLaunch.correctedLaunch rate x.1 rewards C_star C_h =
        some (generatedSourceSeed rate rewards C_star C_h s hs x) ∧
      ReferenceActivePhysicalHorizon.allActiveAtStart
        (generatedSourceSeed rate rewards C_star C_h s hs x) s ∧
      ReferenceFollowerDecoderChronology.downBatchSeed
        (generatedSourceSeed rate rewards C_star C_h s hs x) s := by
  let ctx := sourceLaunchContext rate rewards C_star C_h s hs x
  have hspec := ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
    rate rewards C_star C_h ctx.selected ctx.time ctx.control ctx.remainder
    ctx.remainder_mem s (by simp [ctx.time_val]) ctx.launch_mem
  have hsource := ctx.source_eq
  constructor
  · simpa [generatedSourceSeed, ctx, hsource] using hspec.1
  · constructor
    · simpa [generatedSourceSeed, ctx, hsource, ctx.time_val] using hspec.2.1
    · simpa [generatedSourceSeed, ctx, hsource, ctx.time_val] using hspec.2.2

/-- The actual full postlaunch input: complete continuous rows, original J,
whole grid rewards, and the generated seed's proved activation mode. -/
def generatedSourceRunInput
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (x : LaunchSource rate rewards C_star C_h s hs) :
    ReferenceActiveHorizonMeasurability.ActiveRunInput (p := p) (rate := rate) s := by
  refine ⟨(generatedSourceSeed rate rewards C_star C_h s hs x,
    (x.1.1.2, (ActualInitializationPhysicalStep.selectedRowIndex p x.1, rewards))), ?_⟩
  exact (generatedSourceSeed_spec rate rewards C_star C_h s hs x).2.1

/-- The actual physical run continues to T. Its records are the original
reference execution, with no analytical stopping cutoff. -/
def generatedSourceRun
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (x : LaunchSource rate rewards C_star C_h s hs) :=
  ReferenceActiveHorizonMeasurability.runOfInput (p := p) (rate := rate)
    s (p.T - s) (by omega) (generatedSourceRunInput rate rewards C_star C_h s hs x)

/-- The countable V observation of those same actual records. -/
def generatedSourceObservation
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (i : Fin (p.m - 1))
    (x : LaunchSource rate rewards C_star C_h s hs) :=
  ReferenceDownCompletedAmbiguityMeasurability.runDownObservation
    (p := p) (rate := rate) s (p.T - s) (by omega) i
      (generatedSourceRunInput rate rewards C_star C_h s hs x)

/-- The at-most-Q actual executed tests formed after an ordinary incoming
boundary. The caller supplies only the computed observation and boundary
index; it does not supply a trace, policy, state, or source execution. -/
def observedTestsFrom
    (rate : RateInput p) (alpha : ℕ)
    (count : ℕ)
    (code : ReferenceDownCompletedAmbiguityMeasurability.RunDownObservationCode
      p rate count) : List (ExecutedTest p) :=
  ((List.ofFn code.2).filterMap fun round =>
    if alpha ≤ round.1.val then executedTestOfRound rate round else none).take
      (AffineBatchDecoder.quota p)

/-- The actual full fresh-reset batch: retain the first Q executed positives
after alpha, or all positives through T if fewer occur. -/
def generatedDownBatchTests
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (i : Fin (p.m - 1)) (alpha : ℕ)
    (x : LaunchSource rate rewards C_star C_h s hs) : List (ExecutedTest p) :=
  observedTestsFrom (p := p) rate alpha (p.T - s)
    (generatedSourceObservation rate rewards C_star C_h s hs i x)

/-- The computed source batch is capped at the actual decoder quota. -/
theorem generatedDownBatchTests_length_le_quota
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (i : Fin (p.m - 1)) (alpha : ℕ)
    (x : LaunchSource rate rewards C_star C_h s hs) :
    (generatedDownBatchTests rate rewards C_star C_h s hs i alpha x).length ≤
      AffineBatchDecoder.quota p := by
  exact List.length_take_le _ _

/-- The tests before current physical round r in the genuine retained
launch-start remainder. They are extracted from the computed existing run;
the current control at r is removed by B's original remainder subtype. -/
def retainedBatchPrefix
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (r : Fin p.T) (s : ℕ)
    (_hs : s < p.T) (hsr : s ≤ r.val) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1)) (alpha : ℕ) (_halpha : s < alpha) (_halphaR : alpha ≤ r.val)
    (x : ReferenceRetainedBoundaryMeasurability.RetainedLaunchStart
      rate rewards C_star C_h q r s hsr control0) : List (ExecutedTest p) := by
  let input : ReferenceActiveHorizonMeasurability.ActiveRunInput (p := p) (rate := rate) s :=
    ⟨((ReferenceRetainedBoundaryMeasurability.retainedGeneratedActiveSeed
        rate rewards C_star C_h q r s hsr control0 x),
      ((ReferenceGeneratedActivePrefixFactor.splitSource q r control0 x.1).1.2,
        (q, rewards))),
      (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
        rate rewards C_star C_h q r control0 x.1 x.2.1 s hsr x.2.2).2.1⟩
  let code := ReferenceDownCompletedAmbiguityMeasurability.runDownObservation
    (p := p) (rate := rate) s (r.val - s) (by omega) i input
  exact ((List.ofFn code.2).filterMap fun round =>
    if alpha ≤ round.1.val then executedTestOfRound rate round else none).take
      (AffineBatchDecoder.quota p)

/-- The ordinary configuration immediately before physical pair `r`, from the
same retained generated prefix used by `retainedBatchPrefix`. -/
def retainedBatchIncoming
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (r : Fin p.T) (s : ℕ)
    (_hs : s < p.T) (hsr : s ≤ r.val) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1)) (alpha : ℕ) (_halpha : s < alpha) (_halphaR : alpha ≤ r.val)
    (x : ReferenceRetainedBoundaryMeasurability.RetainedLaunchStart
      rate rewards C_star C_h q r s hsr control0) :
    DeclaredFollowerLocalRound.LocalConfiguration p rate := by
  let input : ReferenceActiveHorizonMeasurability.ActiveRunInput (p := p) (rate := rate) s :=
    ⟨((ReferenceRetainedBoundaryMeasurability.retainedGeneratedActiveSeed
        rate rewards C_star C_h q r s hsr control0 x),
      ((ReferenceGeneratedActivePrefixFactor.splitSource q r control0 x.1).1.2,
        (q, rewards))),
      (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
        rate rewards C_star C_h q r control0 x.1 x.2.1 s hsr x.2.2).2.1⟩
  exact (ReferenceActiveHorizonMeasurability.runOfInput (p := p) (rate := rate)
    s (r.val - s) (by omega) input).finalState.followers i

/-- The retained prefix is also capped at the decoder quota. -/
theorem retainedBatchPrefix_length_le_quota
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (r : Fin p.T) (s : ℕ)
    (hs : s < p.T) (hsr : s ≤ r.val) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1)) (alpha : ℕ) (halpha : s < alpha) (halphaR : alpha ≤ r.val)
    (x : ReferenceRetainedBoundaryMeasurability.RetainedLaunchStart
      rate rewards C_star C_h q r s hsr control0) :
    (retainedBatchPrefix rate rewards C_star C_h q r s hs hsr control0
      i alpha halpha halphaR x).length ≤ AffineBatchDecoder.quota p := by
  exact List.length_take_le _ _

/-- The real reset event B_alpha. At alpha-1 the code must show a diagnostic
call whose decoded logged bank completes Q equations, and the actual incoming
physical follower at alpha must be ordinary. No acceptance or parser success
is required. -/
def retainedBatchBoundary
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (r : Fin p.T) (s : ℕ)
    (_hs : s < p.T) (hsr : s ≤ r.val) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1)) (alpha : ℕ) (halpha : s < alpha) (halphaR : alpha ≤ r.val)
    (x : ReferenceRetainedBoundaryMeasurability.RetainedLaunchStart
      rate rewards C_star C_h q r s hsr control0) : Prop := by
  let input : ReferenceActiveHorizonMeasurability.ActiveRunInput (p := p) (rate := rate) s :=
    ⟨((ReferenceRetainedBoundaryMeasurability.retainedGeneratedActiveSeed
        rate rewards C_star C_h q r s hsr control0 x),
      ((ReferenceGeneratedActivePrefixFactor.splitSource q r control0 x.1).1.2,
        (q, rewards))),
      (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
        rate rewards C_star C_h q r control0 x.1 x.2.1 s hsr x.2.2).2.1⟩
  let code := ReferenceDownCompletedAmbiguityMeasurability.runDownObservation
    (p := p) (rate := rate) s (r.val - s) (by omega) i input
  let completedRound := code.2 ⟨alpha - 1 - s, by omega⟩
  let incoming := (ReferenceActiveHorizonMeasurability.runOfInput
    (p := p) (rate := rate) s (alpha - s) (by omega) input).finalState.followers i
  exact completedBatchAtRound rate completedRound ∧
    ∃ state memory, incoming = .ordinary state memory

/-- Before-pair marker I_(q,r), using the same computed batch and the literal
previous sent words and affine hashes. -/
def retainedPrefixMarker
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (qJ : Fin (M p)) (r : Fin p.T) (s q : ℕ)
    (hs : s < p.T) (hsr : s ≤ r.val) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1)) (alpha : ℕ) (halpha : s < alpha) (halphaR : alpha ≤ r.val)
    (candidate : Word (AffineBatchDecoder.width p))
    (_hq : 1 ≤ q) (_hqQ : q ≤ AffineBatchDecoder.quota p)
    (x : ReferenceRetainedBoundaryMeasurability.RetainedLaunchStart
      rate rewards C_star C_h qJ r s hsr control0) : Prop := by
  let tests := retainedBatchPrefix rate rewards C_star C_h qJ r s hs hsr control0
    i alpha halpha halphaR x
  exact retainedBatchBoundary rate rewards C_star C_h qJ r s hs hsr control0
      i alpha halpha halphaR x ∧
    (∃ state memory,
      retainedBatchIncoming rate rewards C_star C_h qJ r s hs hsr control0
        i alpha halpha halphaR x = .ordinary state memory) ∧
    tests.length = q - 1 ∧ tests.length < AffineBatchDecoder.quota p ∧
    ∀ test ∈ tests, ExecutedTest.good candidate test

/-- The reset event on the actual generated source branch. -/
def generatedSourceBatchBoundary
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (i : Fin (p.m - 1)) (alpha : ℕ) (halpha : s < alpha) (halphaT : alpha < p.T)
    (x : LaunchSource rate rewards C_star C_h s hs) : Prop := by
  let input := generatedSourceRunInput rate rewards C_star C_h s hs x
  let code := generatedSourceObservation rate rewards C_star C_h s hs i x
  let completedRound := code.2 ⟨alpha - 1 - s, by omega⟩
  let incoming := (ReferenceActiveHorizonMeasurability.runOfInput
    (p := p) (rate := rate) s (alpha - s) (by omega) input).finalState.followers i
  exact completedBatchAtRound rate completedRound ∧
    ∃ state memory, incoming = .ordinary state memory

/-- Local literal D_q event on the actual generated batch. -/
def generatedDownD
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s q : ℕ) (hs : s < p.T)
    (i : Fin (p.m - 1)) (alpha : ℕ) (halpha : s < alpha) (halphaT : alpha < p.T)
    (candidate : Word (AffineBatchDecoder.width p))
    (x : LaunchSource rate rewards C_star C_h s hs) : Prop :=
  generatedSourceBatchBoundary rate rewards C_star C_h s hs i alpha halpha halphaT x ∧
    survives candidate q (generatedDownBatchTests rate rewards C_star C_h s hs i alpha x)

/-- D_0 is exactly B_alpha, since the empty-prefix predicate is true. -/
theorem generatedDownD_zero
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (i : Fin (p.m - 1)) (alpha : ℕ) (halpha : s < alpha) (halphaT : alpha < p.T)
    (candidate : Word (AffineBatchDecoder.width p))
    (x : LaunchSource rate rewards C_star C_h s hs) :
    generatedDownD rate rewards C_star C_h s 0 hs i alpha halpha halphaT candidate x ↔
      generatedSourceBatchBoundary rate rewards C_star C_h s hs i alpha halpha halphaT x := by
  simp [generatedDownD, survives]

end Bandits.Support.ReferenceGeneratedDownBatchCalendar

end
