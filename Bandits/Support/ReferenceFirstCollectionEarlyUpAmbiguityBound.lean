/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionEarlyUpSourceAwaited

/-!
# Probability bound for the literal early second UP batch event

Sources: `sources/zip4/manuscript/05_binary_transport.tex:20-53`,
`sources/zip4/manuscript/06_interruptions.tex:164-177,246-295,327-348`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:139-157`, and
`sources/zip4/manuscript/08_main_theorem.tex:29-42`.

The event below is the literal physical-source event for one retained early
DOWN record and one saved second UP batch. It keeps the carried pending bank,
completed history, and cutoff-inclusive interval on the same source. Its
probability statements use the measure of an arbitrary set, hence outer
measure: this module does not establish Borel measurability of the event.
The deterministic containment is uniform in the externally supplied time
control, and the existing all-J envelope already accounts for the original
selected-row index.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal Classical

namespace Bandits.Support.ReferenceFirstCollectionEarlyUpAmbiguityBound

open Bandits.Support.ConstructorDimensions
open Bandits.Support.AffineChannelLaw
open Bandits.Support.AffineBatchDecoder
open Bandits.Support.ReferenceGeneratedUpAwaitedAmbiguityTail

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

/-- A literal actual-source witness for ambiguity in the saved early second
UP batch. All runs, rows, rewards, and decoder banks are computed from the
same original source. The interval includes its cutoff record, and its bank
retains both pending equations and previously completed batches. -/
def earlySecondBatchAmbiguityEvent
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) :
    Set (BootstrapPrivateRoundStreams.SourceInput p) :=
  {source |
    ∃ (count : ℕ)
      (hcross : (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
      (hspan : ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed + count ≤ p.T)
      (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
          rate source rewards C_star C_h hcross count hspan).records).length < count),
      let x0 := ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate
      let b0 := ReferenceInitializationRun.output x0
      let s := ReferenceInitializationRun.elapsed p b0.completed
      let I := ReferenceFirstCollectionEpochAlignment.actualLaunchState
        rate source rewards C_star C_h hcross
      let Erun := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count hspan
      let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow Erun.records
      let w := W.length
      let B := ReferenceCollectionPhaseHistory.collectionWindow Erun.records w
      let rows := source.1.2
      let J := ActualInitializationPhysicalStep.selectedRowIndex p source
      let active := (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
        rate source rewards C_star C_h hcross).1
      ∃ (i : Fin (p.m - 1)) (j : Fin Erun.records.length)
        (M : ReferenceAcceptedUpFollowerHistory.DownRecord (p := p) (rate := rate)),
        j.val < w ∧
        ReferenceAcceptedUpFollowerHistory.RetainedDown Erun.records[j.val] i M ∧
        ∃ (n : ℕ),
          0 < n ∧ n ≤ B.length ∧
          ∃ (hspanN : s + (w + n) ≤ p.T),
            let Cn := ReferenceActivePhysicalHorizon.run I rows J rewards s (w + n) hspanN active
            let preRun := ReferenceActivePhysicalHorizon.run I rows J rewards s w
              ((Nat.add_le_add_left (Nat.le_add_right w n) s).trans hspanN) active
            let interval := Cn.records.drop w
            let trace := ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace interval i
            let rounds := ReferenceCoordinatorUpIntervalWindow.intervalRounds
              I rows J rewards s w (w + n) hspanN active
            let positive := AffineBatchDecoder.positives p trace rounds
            let channel := preRun.finalState.upDecoderBank i
            let Q := AffineBatchDecoder.quota p
            let window := positive.drop (Q - channel.pending.length)
            Cn.finalState.coordinator ≠ .dagger ∧
            Cn.finalState.followers i ≠ .dagger ∧
            positive.length = Q - channel.pending.length + Q ∧
            ∃ (v1 v2 : AffineChannelLaw.Word (AffineBatchDecoder.width p)),
              v1 ≠ v2 ∧
              AffineBatchDecoder.satisfies (AffineBatchDecoder.samples window) v1 ∧
              AffineBatchDecoder.satisfies (AffineBatchDecoder.samples window) v2}

/-- Every control slice contains the same literal early event in the already
proved all-J ambiguity envelope. The event itself is control-free. -/
theorem earlySecondBatchAmbiguityEvent_subset_envelope
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p) :
    earlySecondBatchAmbiguityEvent (rate := rate) rewards C_star C_h ⊆
      upAwaitedAmbiguityEnvelope (rate := rate) rewards C_star C_h control0 := by
  intro source hsource
  simp only [earlySecondBatchAmbiguityEvent, Set.mem_ofPred_eq] at hsource
  rcases hsource with
    ⟨count, hcross, hspan, hshort, i, j, M, hj, hretained,
      n, _hnPos, hn, hspanN, hcoord, hfollower, hCount, hamb⟩
  let x0 := ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate
  let b0 := ReferenceInitializationRun.output x0
  let s := ReferenceInitializationRun.elapsed p b0.completed
  let I := ReferenceFirstCollectionEpochAlignment.actualLaunchState
    rate source rewards C_star C_h hcross
  let Erun := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
    rate source rewards C_star C_h hcross count hspan
  let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow Erun.records
  let w := W.length
  let B := ReferenceCollectionPhaseHistory.collectionWindow Erun.records w
  let rows := source.1.2
  let J := ActualInitializationPhysicalStep.selectedRowIndex p source
  let active := (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
    rate source rewards C_star C_h hcross).1
  have hcoverage :=
    ReferenceFirstCollectionEarlyUpSourceAwaited.actual_early_second_batch_ambiguous_source_coverage
      rate source rewards C_star C_h count hcross hspan hshort
  obtain ⟨hspanN', hbranches⟩ := hcoverage i j M hj hretained n hn
  have hspanN_eq : hspanN' = hspanN := Subsingleton.elim _ _
  subst hspanN'
  rcases hbranches with hbadCoordinator | hbadFollower | hordinary
  · exact False.elim (hcoord hbadCoordinator)
  · exact False.elim (hfollower hbadFollower)
  · have hmember := hordinary hCount control0 hamb
    exact upAwaitedAmbiguityEvent_subset_envelope
      (rate := rate) rewards C_star C_h control0 hmember

/-- The literal event's measure (outer measure when it is not known
measurable) is bounded by the existing all-J envelope estimate. -/
theorem earlySecondBatchAmbiguityEvent_measure_le
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p) :
    BootstrapPrivateRoundStreams.sourceInputLaw p
        (earlySecondBatchAmbiguityEvent (rate := rate) rewards C_star C_h) ≤
      ((p.m - 1 : ℕ) : ℝ≥0∞) * p.T * 2 ^ AffineBatchDecoder.width p *
        ((1 : ℝ≥0∞) / 2) ^ AffineBatchDecoder.quota p := by
  calc
    BootstrapPrivateRoundStreams.sourceInputLaw p
        (earlySecondBatchAmbiguityEvent (rate := rate) rewards C_star C_h)
      ≤ BootstrapPrivateRoundStreams.sourceInputLaw p
          (upAwaitedAmbiguityEnvelope (rate := rate) rewards C_star C_h control0) :=
        measure_mono (earlySecondBatchAmbiguityEvent_subset_envelope
          (rate := rate) rewards C_star C_h control0)
    _ ≤ _ := upAwaitedAmbiguityEnvelope_measure_le
      (rate := rate) rewards C_star C_h control0

/-- The real outer-measure bound follows from `measureReal_mono`; finiteness
of the envelope measure is supplied explicitly by the probability source law. -/
theorem earlySecondBatchAmbiguityEvent_measureReal_le
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p) :
    (BootstrapPrivateRoundStreams.sourceInputLaw p).real
        (earlySecondBatchAmbiguityEvent (rate := rate) rewards C_star C_h) ≤
      1 / (4 * (N p : ℝ) ^ 2) := by
  let μ := BootstrapPrivateRoundStreams.sourceInputLaw p
  let envelope := upAwaitedAmbiguityEnvelope
    (rate := rate) rewards C_star C_h control0
  have huniv : μ Set.univ = 1 := measure_univ
  have hfinite : μ envelope ≠ ∞ := by
    apply ne_of_lt
    calc
      μ envelope ≤ μ Set.univ := measure_mono (Set.subset_univ _)
      _ < ∞ := by rw [huniv]; norm_num
  calc
    μ.real (earlySecondBatchAmbiguityEvent (rate := rate) rewards C_star C_h)
      ≤ μ.real envelope :=
        MeasureTheory.measureReal_mono
          (earlySecondBatchAmbiguityEvent_subset_envelope
            (rate := rate) rewards C_star C_h control0) hfinite
    _ ≤ 1 / (4 * (N p : ℝ) ^ 2) :=
      upAwaitedAmbiguityEnvelope_measureReal_le
        (rate := rate) rewards C_star C_h control0

end Bandits.Support.ReferenceFirstCollectionEarlyUpAmbiguityBound

end
