/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedUpAwaitedBatchCoverage
public import Bandits.Support.ReferenceGeneratedUpSourceTail
public import Bandits.Support.ReferenceSuppressedDownTail

/-!
# Original-source awaited UP ambiguity tail

Sources: sources/zip4/manuscript/appendix_a_local_protocol.tex:92-157,
sources/zip4/manuscript/05_binary_transport.tex:20-53,
sources/zip4/manuscript/06_interruptions.tex:164-177,277-284,327-348, and
sources/zip4/manuscript/08_main_theorem.tex:29-42.

This module composes the literal awaited-UP source branch with its actual
completed-batch coverage, then bounds the resulting event through the
unconditional original-source all-J calendar tail. It does not produce
awaitedness for arbitrary replies or identify the first-overflow prefix.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal Classical

namespace Bandits.Support.ReferenceGeneratedUpAwaitedAmbiguityTail

open Bandits.Support.ConstructorDimensions
open Bandits.Support.AffineChannelLaw
open Bandits.Support.AffineBatchDecoder
open Bandits.Support.ReferenceGeneratedUpBatchPrefixEvent
open Bandits.Support.ReferenceGeneratedUpPrefixPositiveHalf
open Bandits.Support.ReferenceGeneratedUpSourceCalendar
open Bandits.Support.ReferenceGeneratedUpSourceTail
open Bandits.Support.ReferenceGeneratedUpAwaitedBatchCoverage

variable {p : ReferenceGeneratedUpSourceTail.Parameters}
  {rate : ReferenceGeneratedUpSourceTail.RateInput p}

/-- The literal actual-source UP event branch with one completed ambiguous
batch. Its launch proof, current diagnostic, whole pending bank, and awaited
trace all refer to this same original source. Every retained batch entry is
kept in the awaited interval. -/
def upAwaitedAmbiguityEvent
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p) :
    Set (ReferenceGeneratedUpSourceTail.SourceInput p) :=
  {source | ∃ (q : Fin (M p)) (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val)
      (i : Fin (p.m - 1))
      (hz : source ∈ ReferenceGeneratedAffineHashHalf.generatedLaunchBranch
        (rate := rate) rewards C_star C_h q t (1, i) s)
      (d : ReferenceActivePhysicalStep.UpDiagnostic p rate),
      let z : ReferenceGeneratedUpBatchPrefixEvent.UpLaunchSource
          (rate := rate) rewards C_star C_h q t s i := ⟨source, hz⟩
      let current := originalSourceCurrentRecord
        (rate := rate) rewards C_star C_h q t s hs control0 i z
      let bank := current.input.state.upDecoderBank i
      current.output.coordinator.up = some d ∧
      d.input.selectedFollower = i ∧
      ReferenceActiveAffinePositiveTest.upPositive current.input = true ∧
      bank.pending.length + 1 = AffineBatchDecoder.quota p ∧
      (∃ (message : OrdinaryMessageCodec.UpRecord
          (CoordinatorCollectionLedger.codecParams p rate.eta)) (beta : ℕ),
        awaited_up_source_trace rewards C_star C_h q t s hs control0 i z beta message ∧
        ∀ entry ∈ bank.pending ++
          [AffineBatchDecoder.entry p
            (ReferenceCoordinatorUpDecoderReplay.constantInputTrace d.input) d.input.time],
          beta ≤ entry.time.val) ∧
      ∃ v₁ v₂ : AffineChannelLaw.Word (AffineBatchDecoder.width p),
        v₁ ≠ v₂ ∧
        AffineBatchDecoder.satisfies
          ((bank.pending ++
            [AffineBatchDecoder.entry p
              (ReferenceCoordinatorUpDecoderReplay.constantInputTrace d.input) d.input.time]).map
                AffineBatchDecoder.Entry.sample) v₁ ∧
        AffineBatchDecoder.satisfies
          ((bank.pending ++
            [AffineBatchDecoder.entry p
              (ReferenceCoordinatorUpDecoderReplay.constantInputTrace d.input) d.input.time]).map
                AffineBatchDecoder.Entry.sample) v₂}

/-- The finite union over only the UP follower, calendar start, and candidate.
The source's original-J union is already part of each all-J tail event. -/
def upAwaitedAmbiguityEnvelope
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p) :
    Set (ReferenceGeneratedUpSourceTail.SourceInput p) :=
  ⋃ i : Fin (p.m - 1), ⋃ alpha : Fin p.T,
    ⋃ candidate : ReferenceGeneratedUpSourceTail.Candidate p,
      ReferenceGeneratedUpSourceTail.upSourceAllJSurvivalEvent (rate := rate)
        rewards C_star C_h control0 alpha.val candidate i (AffineBatchDecoder.quota p)

/-- Measurability follows from the public measurability theorem for each
original-source all-J survival event. -/
theorem measurableSet_upAwaitedAmbiguityEnvelope
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p) :
    MeasurableSet (upAwaitedAmbiguityEnvelope (rate := rate)
      rewards C_star C_h control0) := by
  apply MeasurableSet.iUnion
  intro i
  apply MeasurableSet.iUnion
  intro alpha
  apply MeasurableSet.iUnion
  intro candidate
  exact ReferenceGeneratedUpSourceTail.measurableSet_upSourceAllJSurvivalEvent
    (rate := rate) rewards C_star C_h control0 alpha.val candidate i
      (AffineBatchDecoder.quota p)

/-- Each literal event witness is sent through the exact actual awaited-batch
coverage theorem. Its one birth is then embedded in the finite all-J union. -/
theorem upAwaitedAmbiguityEvent_subset_envelope
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p) :
    upAwaitedAmbiguityEvent (rate := rate) rewards C_star C_h control0 ⊆
      upAwaitedAmbiguityEnvelope (rate := rate) rewards C_star C_h control0 := by
  intro source hsource
  simp only [upAwaitedAmbiguityEvent, Set.mem_ofPred_eq] at hsource
  rcases hsource with ⟨q, t, s, hs, i, hz, d, hd, hi, hp, hQ, hawaited, hamb⟩
  let z : ReferenceGeneratedUpBatchPrefixEvent.UpLaunchSource
      (rate := rate) rewards C_star C_h q t s i := ⟨source, hz⟩
  have hcoverage :=
    ReferenceGeneratedUpAwaitedBatchCoverage.awaited_up_ambiguous_source_coverage
      (rate := rate) rewards C_star C_h q t s hs control0 i z d hd hi hp hQ
        hawaited hamb
  obtain ⟨alpha, hsAlpha, hAlphaT, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      hsurvival⟩ := hcoverage
  obtain ⟨candidate, _, _, hcandidateSurvives⟩ := hsurvival
  have hAlphaLt : alpha < p.T := lt_of_le_of_lt hAlphaT t.isLt
  let alphaFin : Fin p.T := ⟨alpha, hAlphaLt⟩
  simp only [upAwaitedAmbiguityEnvelope, Set.mem_iUnion]
  refine ⟨i, alphaFin, candidate, ?_⟩
  change source ∈ ⋃ q' : Fin (M p),
    ReferenceGeneratedUpSourceCalendar.upSourceSurvivalEvent (rate := rate)
      rewards C_star C_h q' control0 alpha candidate i (AffineBatchDecoder.quota p)
  exact Set.mem_iUnion.mpr ⟨q, by simpa only [z] using hcandidateSurvives⟩

/-- The envelope has at most (m-1) T 2^width all-J tail events. Each tail
uses the original source law and its geometric quota bound. -/
theorem upAwaitedAmbiguityEnvelope_measure_le
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p) :
    BootstrapPrivateRoundStreams.sourceInputLaw p
        (upAwaitedAmbiguityEnvelope (rate := rate) rewards C_star C_h control0) ≤
      ((p.m - 1 : ℕ) : ℝ≥0∞) * p.T * 2 ^ AffineBatchDecoder.width p *
        ((1 : ℝ≥0∞) / 2) ^ AffineBatchDecoder.quota p := by
  classical
  let μ := BootstrapPrivateRoundStreams.sourceInputLaw p
  calc
    μ (⋃ i : Fin (p.m - 1), ⋃ alpha : Fin p.T,
        ⋃ candidate : ReferenceGeneratedUpSourceTail.Candidate p,
          ReferenceGeneratedUpSourceTail.upSourceAllJSurvivalEvent (rate := rate)
            rewards C_star C_h control0 alpha.val candidate i (AffineBatchDecoder.quota p))
        ≤ ∑ i : Fin (p.m - 1),
            μ (⋃ alpha : Fin p.T, ⋃ candidate : ReferenceGeneratedUpSourceTail.Candidate p,
              ReferenceGeneratedUpSourceTail.upSourceAllJSurvivalEvent (rate := rate)
                rewards C_star C_h control0 alpha.val candidate i (AffineBatchDecoder.quota p)) :=
          measure_iUnion_fintype_le μ _
    _ ≤ ∑ i : Fin (p.m - 1), ∑ alpha : Fin p.T,
          ∑ candidate : ReferenceGeneratedUpSourceTail.Candidate p,
            ((1 : ℝ≥0∞) / 2) ^ AffineBatchDecoder.quota p := by
      apply Finset.sum_le_sum
      intro i _
      apply le_trans (measure_iUnion_fintype_le μ _)
      apply Finset.sum_le_sum
      intro alpha _
      apply le_trans (measure_iUnion_fintype_le μ _)
      exact Finset.sum_le_sum fun candidate _ =>
        ReferenceGeneratedUpSourceTail.upSourceAllJSurvivalEvent_measure_le_geometric
          (rate := rate) rewards C_star C_h control0 alpha.val candidate i
            (AffineBatchDecoder.quota p) (le_refl _)
    _ = ((p.m - 1 : ℕ) : ℝ≥0∞) * p.T * 2 ^ AffineBatchDecoder.width p *
          ((1 : ℝ≥0∞) / 2) ^ AffineBatchDecoder.quota p := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        ReferenceGeneratedUpSourceTail.Candidate, AffineChannelLaw.Word,
        AffineChannelLaw.Bit, Fintype.card_fun, ZMod.card, nsmul_eq_mul,
        Nat.cast_pow, Nat.cast_ofNat, mul_assoc]

private theorem unionFactor_ne_top (p : ConstructorDimensions.Parameters) :
    ((p.m - 1 : ℕ) : ℝ≥0∞) * p.T * 2 ^ AffineBatchDecoder.width p *
      (2 ^ AffineBatchDecoder.quota p : ℝ≥0∞)⁻¹ ≠ ∞ := by
  exact ENNReal.mul_ne_top
    (ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.natCast_ne_top _))
      (ENNReal.pow_ne_top (by norm_num)))
    (ENNReal.inv_ne_top.mpr (pow_ne_zero _ (by norm_num)))

private theorem halfPow_eq_invPow (n : ℕ) :
    ((1 : ℝ≥0∞) / 2) ^ n = (2 ^ n : ℝ≥0∞)⁻¹ := by
  rw [one_div, ← ENNReal.inv_pow]

/-- The envelope's real measure bound uses explicit ENNReal finiteness and
the admitted source quota arithmetic. -/
theorem upAwaitedAmbiguityEnvelope_measureReal_le
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p) :
    (BootstrapPrivateRoundStreams.sourceInputLaw p).real
        (upAwaitedAmbiguityEnvelope (rate := rate) rewards C_star C_h control0) ≤
      1 / (4 * (N p : ℝ) ^ 2) := by
  have hbound := upAwaitedAmbiguityEnvelope_measure_le
    (rate := rate) rewards C_star C_h control0
  have hbound' :
      BootstrapPrivateRoundStreams.sourceInputLaw p
          (upAwaitedAmbiguityEnvelope (rate := rate) rewards C_star C_h control0) ≤
        ((p.m - 1 : ℕ) : ℝ≥0∞) * p.T * 2 ^ AffineBatchDecoder.width p *
          (2 ^ AffineBatchDecoder.quota p : ℝ≥0∞)⁻¹ := by
    calc
      _ ≤ ((p.m - 1 : ℕ) : ℝ≥0∞) * p.T * 2 ^ AffineBatchDecoder.width p *
          ((1 : ℝ≥0∞) / 2) ^ AffineBatchDecoder.quota p := hbound
      _ = _ := by rw [halfPow_eq_invPow]
  have htoReal := ENNReal.toReal_mono (unionFactor_ne_top p) hbound'
  have hreal :
      (BootstrapPrivateRoundStreams.sourceInputLaw p).real
          (upAwaitedAmbiguityEnvelope (rate := rate) rewards C_star C_h control0) ≤
        ((p.m - 1 : ℕ) : ℝ) * p.T * 2 ^ AffineBatchDecoder.width p *
          (2 ^ AffineBatchDecoder.quota p : ℝ)⁻¹ := by
    simpa only [measureReal_def, ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ENNReal.toReal_pow, ENNReal.toReal_ofNat, ENNReal.toReal_inv] using htoReal
  exact hreal.trans (ReferenceSuppressedDownTail.quota_union_factor_le p)

/-- The ordinary measure (outer measure when needed) of the literal event is
bounded by the same finite all-J survival envelope. -/
theorem upAwaitedAmbiguityEvent_measure_le
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p) :
    BootstrapPrivateRoundStreams.sourceInputLaw p
        (upAwaitedAmbiguityEvent (rate := rate) rewards C_star C_h control0) ≤
      ((p.m - 1 : ℕ) : ℝ≥0∞) * p.T * 2 ^ AffineBatchDecoder.width p *
        ((1 : ℝ≥0∞) / 2) ^ AffineBatchDecoder.quota p := by
  calc
    _ ≤ BootstrapPrivateRoundStreams.sourceInputLaw p
        (upAwaitedAmbiguityEnvelope (rate := rate) rewards C_star C_h control0) :=
      measure_mono (upAwaitedAmbiguityEvent_subset_envelope
        (rate := rate) rewards C_star C_h control0)
    _ ≤ _ := upAwaitedAmbiguityEnvelope_measure_le
      (rate := rate) rewards C_star C_h control0

/-- The literal event's real outer measure is at most 1/(4 N^2), by
monotonicity through an explicitly finite ENNReal quota factor. -/
theorem upAwaitedAmbiguityEvent_measureReal_le
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p) :
    (BootstrapPrivateRoundStreams.sourceInputLaw p).real
        (upAwaitedAmbiguityEvent (rate := rate) rewards C_star C_h control0) ≤
      1 / (4 * (N p : ℝ) ^ 2) := by
  have hbound := upAwaitedAmbiguityEvent_measure_le
    (rate := rate) rewards C_star C_h control0
  have hbound' :
      BootstrapPrivateRoundStreams.sourceInputLaw p
          (upAwaitedAmbiguityEvent (rate := rate) rewards C_star C_h control0) ≤
        ((p.m - 1 : ℕ) : ℝ≥0∞) * p.T * 2 ^ AffineBatchDecoder.width p *
          (2 ^ AffineBatchDecoder.quota p : ℝ≥0∞)⁻¹ := by
    calc
      _ ≤ ((p.m - 1 : ℕ) : ℝ≥0∞) * p.T * 2 ^ AffineBatchDecoder.width p *
          ((1 : ℝ≥0∞) / 2) ^ AffineBatchDecoder.quota p := hbound
      _ = _ := by rw [halfPow_eq_invPow]
  have htoReal := ENNReal.toReal_mono (unionFactor_ne_top p) hbound'
  have hreal :
      (BootstrapPrivateRoundStreams.sourceInputLaw p).real
          (upAwaitedAmbiguityEvent (rate := rate) rewards C_star C_h control0) ≤
        ((p.m - 1 : ℕ) : ℝ) * p.T * 2 ^ AffineBatchDecoder.width p *
          (2 ^ AffineBatchDecoder.quota p : ℝ)⁻¹ := by
    simpa only [measureReal_def, ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ENNReal.toReal_pow, ENNReal.toReal_ofNat, ENNReal.toReal_inv] using htoReal
  exact hreal.trans (ReferenceSuppressedDownTail.quota_union_factor_le p)

end Bandits.Support.ReferenceGeneratedUpAwaitedAmbiguityTail

end
