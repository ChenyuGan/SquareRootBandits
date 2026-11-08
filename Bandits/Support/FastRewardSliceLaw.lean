/-
Copyright (c) 2026 The Bandits Lean regret formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.CanonicalFastSampling
public import Bandits.Support.CanonicalRecordingSlice
public import Bandits.Support.MixedAuxiliaryReward
public import Bandits.Support.SnapshotRecordingKernel

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Continuous fast-reward and correlated-recorder adapter

The scalar and one-slice identities below realize the accepted fast sampler
and fixed-snapshot recorder on their existing continuous uniform slice. The
joint recorder/fast map keeps both outputs on the same scalar slice, so no
independence between them is asserted.

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:20-37,96-155,379-390`
and `sources/zip4/manuscript/05_binary_transport.tex:352-429`.

These are fixed-round, supplied-snapshot results. They do not establish
chronological freshness, recorder correspondence along an execution, an
adaptive law, or closure of a manuscript statement.
-/

public section

open MeasureTheory
open scoped BigOperators

namespace Bandits.Support.FastRewardSliceLaw

open Bandits.Support.CanonicalFastSampling
open Bandits.Support.CanonicalOrientedSetLaw
open Bandits.Support.CanonicalRecordingRates
open Bandits.Support.ContinuousCategorical
open Bandits.Support.ContinuousControlSlice
open Bandits.Support.ConstructorDimensions
open Bandits.Support.MixedAuxiliaryReward
open Bandits.Support.SnapshotRecordingKernel

private theorem measurable_oneRoundAuxiliaryReward {p : Parameters}
    (r : Fin p.K → ℝ) (U : SlowSet p.K p.m) :
    Measurable (fun j : FastArm U => oneRoundAuxiliaryReward r U j) :=
  measurable_of_finite _

private theorem integrable_oneRoundAuxiliaryReward_comp
    {p : Parameters} {U : SlowSet p.K p.m} {α : Type*}
    [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (r : Fin p.K → ℝ) (hr : ∀ i, 0 ≤ r i ∧ r i ≤ 1)
    (f : α → FastArm U) (hf : Measurable f) :
    Integrable (fun x => oneRoundAuxiliaryReward r U (f x)) μ := by
  have hmeas : Measurable (fun x => oneRoundAuxiliaryReward r U (f x)) :=
    (measurable_oneRoundAuxiliaryReward r U).comp hf
  apply Integrable.of_bound hmeas.aestronglyMeasurable (p.m : ℝ)
  filter_upwards [] with x
  have hb := oneRoundAuxiliaryReward_bounds r hr U (f x)
  rw [Real.norm_eq_abs]
  exact abs_le.mpr ⟨by linarith [hb.1], hb.2⟩

/-- Measurability of the reward of the accepted continuous-scalar fast draw.

Source: `sources/zip4/manuscript/04_slow_fast_learner.tex:20-37`. -/
theorem measurable_oneRoundAuxiliaryReward_sampleFast (p : Parameters)
    (eta : ℝ) (heta : 0 < eta)
    (heta_le : eta ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ)))
    (v w : Fin p.K → ℝ) (hv : ∀ i, 0 < v i) (hw : ∀ i, 0 < w i)
    (hvw : ∀ i, v i ≤ w i) (hwv : ∀ i, w i ≤ 2 * v i)
    (r : Fin p.K → ℝ) (U : SlowSet p.K p.m) :
    Measurable (fun x : ContinuousCategorical.Scalar =>
      oneRoundAuxiliaryReward r U
        (sampleFast p eta heta heta_le v w hv hw hvw hwv U x)) := by
  exact (measurable_oneRoundAuxiliaryReward r U).comp
    (measurable_sampleFast p eta heta heta_le v w hv hw hvw hwv U)

/-- The bounded auxiliary reward is integrable under the actual continuous
uniform scalar law. -/
theorem integrable_oneRoundAuxiliaryReward_sampleFast (p : Parameters)
    (eta : ℝ) (heta : 0 < eta)
    (heta_le : eta ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ)))
    (v w : Fin p.K → ℝ) (hv : ∀ i, 0 < v i) (hw : ∀ i, 0 < w i)
    (hvw : ∀ i, v i ≤ w i) (hwv : ∀ i, w i ≤ 2 * v i)
    (r : Fin p.K → ℝ) (hr : ∀ i, 0 ≤ r i ∧ r i ≤ 1)
    (U : SlowSet p.K p.m) :
    Integrable
      (fun x : ContinuousCategorical.Scalar =>
        oneRoundAuxiliaryReward r U
          (sampleFast p eta heta heta_le v w hv hw hvw hwv U x))
      ContinuousCategorical.uniform := by
  exact integrable_oneRoundAuxiliaryReward_comp ContinuousCategorical.uniform
    r hr (sampleFast p eta heta heta_le v w hv hw hvw hwv U)
    (measurable_sampleFast p eta heta heta_le v w hv hw hvw hwv U)

/-- Finite-integral formula for the exact existing `qGammaPMF`.

The PMF is the one constructed from the literal `qGamma` masses by
`CanonicalFastSampling`; no new finite law is introduced here. -/
theorem qGammaPMF_integral_oneRoundAuxiliaryReward (p : Parameters)
    (eta : ℝ) (heta : 0 < eta)
    (heta_le : eta ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ)))
    (v w : Fin p.K → ℝ) (hv : ∀ i, 0 < v i) (hw : ∀ i, 0 < w i)
    (hvw : ∀ i, v i ≤ w i) (hwv : ∀ i, w i ≤ 2 * v i)
    (r : Fin p.K → ℝ) (U : SlowSet p.K p.m) :
    (∫ j : FastArm U, oneRoundAuxiliaryReward r U j ∂
      (qGammaPMF p eta heta heta_le v w hv hw hvw hwv U).toMeasure) =
      ∑ j : FastArm U,
        qGamma p eta heta heta_le v w hv hw hvw hwv U j *
          oneRoundAuxiliaryReward r U j := by
  rw [PMF.integral_eq_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [qGammaPMF_apply]
  rw [ENNReal.toReal_ofReal (qGamma_nonneg p heta heta_le v w hv hw hvw hwv U j)]
  rw [smul_eq_mul]

/-- The integral of the literal auxiliary reward after the actual scalar
sampler is exactly the finite `qGamma` reward sum.

The proof uses `uniform_map_sampleFast`, Mathlib's `integral_map`, and
`PMF.integral_eq_sum`, so the result is attached to the continuous realization
on `[0,1)`. -/
theorem integral_oneRoundAuxiliaryReward_sampleFast (p : Parameters)
    (eta : ℝ) (heta : 0 < eta)
    (heta_le : eta ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ)))
    (v w : Fin p.K → ℝ) (hv : ∀ i, 0 < v i) (hw : ∀ i, 0 < w i)
    (hvw : ∀ i, v i ≤ w i) (hwv : ∀ i, w i ≤ 2 * v i)
    (r : Fin p.K → ℝ) (U : SlowSet p.K p.m) :
    (∫ x : ContinuousCategorical.Scalar,
      oneRoundAuxiliaryReward r U
        (sampleFast p eta heta heta_le v w hv hw hvw hwv U x)
      ∂ ContinuousCategorical.uniform) =
      ∑ j : FastArm U,
        qGamma p eta heta heta_le v w hv hw hvw hwv U j *
          oneRoundAuxiliaryReward r U j := by
  let reward : FastArm U → ℝ := oneRoundAuxiliaryReward r U
  have hreward : Measurable reward := measurable_oneRoundAuxiliaryReward r U
  have hmap := MeasureTheory.integral_map
    (μ := ContinuousCategorical.uniform)
    (measurable_sampleFast p eta heta heta_le v w hv hw hvw hwv U).aemeasurable
    hreward.aestronglyMeasurable
  calc
    (∫ x : ContinuousCategorical.Scalar,
        oneRoundAuxiliaryReward r U
          (sampleFast p eta heta heta_le v w hv hw hvw hwv U x)
        ∂ ContinuousCategorical.uniform) =
        ∫ j : FastArm U, reward j ∂
          ContinuousCategorical.uniform.map
            (sampleFast p eta heta heta_le v w hv hw hvw hwv U) := by
      simpa only [reward] using hmap.symm
    _ = ∫ j : FastArm U, reward j ∂
          (qGammaPMF p eta heta heta_le v w hv hw hvw hwv U).toMeasure := by
      rw [uniform_map_sampleFast p eta heta heta_le v w hv hw hvw hwv U]
    _ = ∑ j : FastArm U,
          qGamma p eta heta heta_le v w hv hw hvw hwv U j *
            oneRoundAuxiliaryReward r U j := by
      simpa only [reward] using
        qGammaPMF_integral_oneRoundAuxiliaryReward p eta heta heta_le
          v w hv hw hvw hwv r U

/-- Measurability of the reward read from the reserved fast coordinate of the
existing continuous control slice. -/
theorem measurable_oneRoundAuxiliaryReward_fastArmDraw (p : Parameters)
    (eta : ℝ) (heta : 0 < eta)
    (heta_le : eta ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ)))
    (v w : Fin p.K → ℝ) (hv : ∀ i, 0 < v i) (hw : ∀ i, 0 < w i)
    (hvw : ∀ i, v i ≤ w i) (hwv : ∀ i, w i ≤ 2 * v i)
    (r : Fin p.K → ℝ) (a : ActiveRoundActions.Assignment p.m p.K) :
    Measurable (fun x : CanonicalRecordingSlice.Slice p.m p.K =>
      oneRoundAuxiliaryReward r (assignmentSlowSet p a)
        (fastArmDraw p eta heta heta_le v w hv hw hvw hwv a x)) := by
  exact (measurable_oneRoundAuxiliaryReward r (assignmentSlowSet p a)).comp
    (measurable_fastArmDraw p eta heta heta_le v w hv hw hvw hwv a)

/-- The sampled auxiliary reward is integrable on the reserved fast
coordinate of the existing continuous control slice. -/
theorem integrable_oneRoundAuxiliaryReward_fastArmDraw (p : Parameters)
    (eta : ℝ) (heta : 0 < eta)
    (heta_le : eta ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ)))
    (v w : Fin p.K → ℝ) (hv : ∀ i, 0 < v i) (hw : ∀ i, 0 < w i)
    (hvw : ∀ i, v i ≤ w i) (hwv : ∀ i, w i ≤ 2 * v i)
    (r : Fin p.K → ℝ) (hr : ∀ i, 0 ≤ r i ∧ r i ≤ 1)
    (a : ActiveRoundActions.Assignment p.m p.K) :
    Integrable
      (fun x : CanonicalRecordingSlice.Slice p.m p.K =>
        oneRoundAuxiliaryReward r (assignmentSlowSet p a)
          (fastArmDraw p eta heta heta_le v w hv hw hvw hwv a x))
      (ContinuousControlSlice.sliceLaw p.m p.K) := by
  exact integrable_oneRoundAuxiliaryReward_comp
    (ContinuousControlSlice.sliceLaw p.m p.K) r hr
    (fastArmDraw p eta heta heta_le v w hv hw hvw hwv a)
    (measurable_fastArmDraw p eta heta heta_le v w hv hw hvw hwv a)

/-- Integrating the literal auxiliary reward of the accepted fast-arm map on
the `fast` coordinate of the existing continuous slice gives the same finite
`qGamma` reward sum as its scalar realization. -/
theorem integral_oneRoundAuxiliaryReward_fastArmDraw (p : Parameters)
    (eta : ℝ) (heta : 0 < eta)
    (heta_le : eta ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ)))
    (v w : Fin p.K → ℝ) (hv : ∀ i, 0 < v i) (hw : ∀ i, 0 < w i)
    (hvw : ∀ i, v i ≤ w i) (hwv : ∀ i, w i ≤ 2 * v i)
    (r : Fin p.K → ℝ) (a : ActiveRoundActions.Assignment p.m p.K) :
    (∫ x : CanonicalRecordingSlice.Slice p.m p.K,
      oneRoundAuxiliaryReward r (assignmentSlowSet p a)
        (fastArmDraw p eta heta heta_le v w hv hw hvw hwv a x)
      ∂ ContinuousControlSlice.sliceLaw p.m p.K) =
      ∑ j : FastArm (assignmentSlowSet p a),
        qGamma p eta heta heta_le v w hv hw hvw hwv
          (assignmentSlowSet p a) j *
          oneRoundAuxiliaryReward r (assignmentSlowSet p a) j := by
  let U := assignmentSlowSet p a
  let reward : FastArm U → ℝ := oneRoundAuxiliaryReward r U
  have hreward : Measurable reward := measurable_oneRoundAuxiliaryReward r U
  have hmap := MeasureTheory.integral_map
    (μ := ContinuousControlSlice.sliceLaw p.m p.K)
    (measurable_fastArmDraw p eta heta heta_le v w hv hw hvw hwv a).aemeasurable
    hreward.aestronglyMeasurable
  calc
    (∫ x : CanonicalRecordingSlice.Slice p.m p.K,
        oneRoundAuxiliaryReward r U
          (fastArmDraw p eta heta heta_le v w hv hw hvw hwv a x)
        ∂ ContinuousControlSlice.sliceLaw p.m p.K) =
        ∫ j : FastArm U, reward j ∂
          (ContinuousControlSlice.sliceLaw p.m p.K).map
            (fastArmDraw p eta heta heta_le v w hv hw hvw hwv a) := by
      simpa only [reward] using hmap.symm
    _ = ∫ j : FastArm U, reward j ∂
          (qGammaPMF p eta heta heta_le v w hv hw hvw hwv U).toMeasure := by
      rw [map_fastArmDraw p eta heta heta_le v w hv hw hvw hwv a]
    _ = ∑ j : FastArm U,
          qGamma p eta heta heta_le v w hv hw hvw hwv U j *
            oneRoundAuxiliaryReward r U j := by
      simpa only [reward] using
        qGammaPMF_integral_oneRoundAuxiliaryReward p eta heta heta_le
          v w hv hw hvw hwv r U

/-- The literal one-slice pair of recorder output and fast arm. Both maps use
the same `x`; in particular, this is not a product of marginal laws.

Source: `sources/zip4/manuscript/05_binary_transport.tex:352-423`. -/
@[expose] noncomputable def liveRecordingFastPair (p : Parameters) (eta : ℝ)
    (heta : 0 < eta)
    (heta_le : eta ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ)))
    (v w : Fin p.K → ℝ) (hv : ∀ i, 0 < v i) (hw : ∀ i, 0 < w i)
    (hvw : ∀ i, v i ≤ w i) (hwv : ∀ i, w i ≤ 2 * v i)
    (a : ActiveRoundActions.Assignment p.m p.K)
    (s : ActiveRoundActions.Snapshot a) :
    CanonicalRecordingSlice.Slice p.m p.K →
      Option (Fin p.K) × FastArm (assignmentSlowSet p a) :=
  fun x =>
    (recordingMap p (.live a s) true eta heta heta_le v w hv hw hvw hwv x,
      fastArmDraw p eta heta heta_le v w hv hw hvw hwv a x)

/-- The actual joint pushforward law of recorder output and fast arm on one
existing continuous control slice. -/
@[expose] noncomputable def liveRecordingFastPushforward (p : Parameters)
    (eta : ℝ) (heta : 0 < eta)
    (heta_le : eta ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ)))
    (v w : Fin p.K → ℝ) (hv : ∀ i, 0 < v i) (hw : ∀ i, 0 < w i)
    (hvw : ∀ i, v i ≤ w i) (hwv : ∀ i, w i ≤ 2 * v i)
    (a : ActiveRoundActions.Assignment p.m p.K)
    (s : ActiveRoundActions.Snapshot a) :
    Measure (Option (Fin p.K) × FastArm (assignmentSlowSet p a)) :=
  (ContinuousControlSlice.sliceLaw p.m p.K).map
    (liveRecordingFastPair p eta heta heta_le v w hv hw hvw hwv a s)

/-- The same-slice pair map is measurable, using the existing fixed-snapshot
recorder and fast-arm measurability theorems. -/
theorem measurable_liveRecordingFastPair (p : Parameters) (eta : ℝ)
    (heta : 0 < eta)
    (heta_le : eta ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ)))
    (v w : Fin p.K → ℝ) (hv : ∀ i, 0 < v i) (hw : ∀ i, 0 < w i)
    (hvw : ∀ i, v i ≤ w i) (hwv : ∀ i, w i ≤ 2 * v i)
    (a : ActiveRoundActions.Assignment p.m p.K)
    (s : ActiveRoundActions.Snapshot a) :
    Measurable (liveRecordingFastPair p eta heta heta_le v w hv hw hvw hwv a s) := by
  exact (measurable_recordingMap p (.live a s) eta heta heta_le v w hv hw hvw hwv true).prodMk
    (measurable_fastArmDraw p eta heta heta_le v w hv hw hvw hwv a)

/-- The auxiliary reward of the fast component is measurable on the finite
joint recorder/fast output carrier. -/
theorem measurable_liveRecordingFastPushforward_auxiliaryReward
    (p : Parameters) (r : Fin p.K → ℝ)
    (a : ActiveRoundActions.Assignment p.m p.K) :
    Measurable (fun z : Option (Fin p.K) × FastArm (assignmentSlowSet p a) =>
      oneRoundAuxiliaryReward r (assignmentSlowSet p a) z.2) := by
  exact (measurable_oneRoundAuxiliaryReward r (assignmentSlowSet p a)).comp measurable_snd

/-- The recorder marginal of the actual same-slice joint pushforward is the
existing `recordingOutcomePMF` measure. -/
theorem liveRecordingFastPushforward_fst (p : Parameters) (eta : ℝ)
    (heta : 0 < eta)
    (heta_le : eta ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ)))
    (v w : Fin p.K → ℝ) (hv : ∀ i, 0 < v i) (hw : ∀ i, 0 < w i)
    (hvw : ∀ i, v i ≤ w i) (hwv : ∀ i, w i ≤ 2 * v i)
    (a : ActiveRoundActions.Assignment p.m p.K)
    (s : ActiveRoundActions.Snapshot a) :
    (liveRecordingFastPushforward p eta heta heta_le v w hv hw hvw hwv a s).map Prod.fst =
      (RecordedRoundMoments.recordingOutcomePMF
        (recordingRates p eta heta heta_le v hv)).toMeasure := by
  change ((ContinuousControlSlice.sliceLaw p.m p.K).map
      (liveRecordingFastPair p eta heta heta_le v w hv hw hvw hwv a s)).map Prod.fst = _
  rw [Measure.map_map measurable_fst
    (measurable_liveRecordingFastPair p eta heta heta_le v w hv hw hvw hwv a s)]
  change (ContinuousControlSlice.sliceLaw p.m p.K).map
    (recordingMap p (.live a s) true eta heta heta_le v w hv hw hvw hwv) = _
  exact map_recordingMap p (.live a s) eta heta heta_le
    v w hv hw hvw hwv

/-- The fast-arm marginal of the actual same-slice joint pushforward is the
existing `qGammaPMF` measure on the assignment complement. -/
theorem liveRecordingFastPushforward_snd (p : Parameters) (eta : ℝ)
    (heta : 0 < eta)
    (heta_le : eta ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ)))
    (v w : Fin p.K → ℝ) (hv : ∀ i, 0 < v i) (hw : ∀ i, 0 < w i)
    (hvw : ∀ i, v i ≤ w i) (hwv : ∀ i, w i ≤ 2 * v i)
    (a : ActiveRoundActions.Assignment p.m p.K)
    (s : ActiveRoundActions.Snapshot a) :
    (liveRecordingFastPushforward p eta heta heta_le v w hv hw hvw hwv a s).map Prod.snd =
      (qGammaPMF p eta heta heta_le v w hv hw hvw hwv
        (assignmentSlowSet p a)).toMeasure := by
  change ((ContinuousControlSlice.sliceLaw p.m p.K).map
      (liveRecordingFastPair p eta heta heta_le v w hv hw hvw hwv a s)).map Prod.snd = _
  rw [Measure.map_map measurable_snd
    (measurable_liveRecordingFastPair p eta heta heta_le v w hv hw hvw hwv a s)]
  change (ContinuousControlSlice.sliceLaw p.m p.K).map
    (fastArmDraw p eta heta heta_le v w hv hw hvw hwv a) = _
  exact map_fastArmDraw p eta heta heta_le v w hv hw hvw hwv a

/-- The literal auxiliary reward integrated against the same-slice joint
recorder/fast pushforward is the conditional `qGamma` reward sum. The proof
uses its actual second marginal; it makes no independence claim.

This is a supplied-assignment, supplied-snapshot statement only. -/
theorem liveRecordingFastPushforward_integral_auxiliaryReward
    (p : Parameters) (eta : ℝ) (heta : 0 < eta)
    (heta_le : eta ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ)))
    (v w : Fin p.K → ℝ) (hv : ∀ i, 0 < v i) (hw : ∀ i, 0 < w i)
    (hvw : ∀ i, v i ≤ w i) (hwv : ∀ i, w i ≤ 2 * v i)
    (r : Fin p.K → ℝ) (a : ActiveRoundActions.Assignment p.m p.K)
    (s : ActiveRoundActions.Snapshot a) :
    (∫ z : Option (Fin p.K) × FastArm (assignmentSlowSet p a),
      oneRoundAuxiliaryReward r (assignmentSlowSet p a) z.2 ∂
        liveRecordingFastPushforward p eta heta heta_le v w hv hw hvw hwv a s) =
      ∑ j : FastArm (assignmentSlowSet p a),
        qGamma p eta heta heta_le v w hv hw hvw hwv
          (assignmentSlowSet p a) j *
          oneRoundAuxiliaryReward r (assignmentSlowSet p a) j := by
  let U := assignmentSlowSet p a
  let reward : FastArm U → ℝ := oneRoundAuxiliaryReward r U
  have hreward : Measurable reward := measurable_oneRoundAuxiliaryReward r U
  have hmap := MeasureTheory.integral_map
    (μ := liveRecordingFastPushforward p eta heta heta_le v w hv hw hvw hwv a s)
    measurable_snd.aemeasurable hreward.aestronglyMeasurable
  calc
    (∫ z : Option (Fin p.K) × FastArm U,
        oneRoundAuxiliaryReward r U z.2 ∂
          liveRecordingFastPushforward p eta heta heta_le v w hv hw hvw hwv a s) =
        ∫ j : FastArm U, reward j ∂
          (liveRecordingFastPushforward p eta heta heta_le v w hv hw hvw hwv a s).map
            Prod.snd := by
      simpa only [reward] using hmap.symm
    _ = ∫ j : FastArm U, reward j ∂
          (qGammaPMF p eta heta heta_le v w hv hw hvw hwv U).toMeasure := by
      rw [liveRecordingFastPushforward_snd p eta heta heta_le v w hv hw hvw hwv a s]
    _ = ∑ j : FastArm U,
          qGamma p eta heta heta_le v w hv hw hvw hwv U j *
            oneRoundAuxiliaryReward r U j := by
      simpa only [reward] using
        qGammaPMF_integral_oneRoundAuxiliaryReward p eta heta heta_le
          v w hv hw hvw hwv r U

/-- Integrability of the auxiliary reward on the actual same-slice joint
recorder/fast pushforward. -/
theorem integrable_liveRecordingFastPushforward_auxiliaryReward
    (p : Parameters) (eta : ℝ) (heta : 0 < eta)
    (heta_le : eta ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ)))
    (v w : Fin p.K → ℝ) (hv : ∀ i, 0 < v i) (hw : ∀ i, 0 < w i)
    (hvw : ∀ i, v i ≤ w i) (hwv : ∀ i, w i ≤ 2 * v i)
    (r : Fin p.K → ℝ) (hr : ∀ i, 0 ≤ r i ∧ r i ≤ 1)
    (a : ActiveRoundActions.Assignment p.m p.K)
    (s : ActiveRoundActions.Snapshot a) :
    Integrable
      (fun z : Option (Fin p.K) × FastArm (assignmentSlowSet p a) =>
        oneRoundAuxiliaryReward r (assignmentSlowSet p a) z.2)
      (liveRecordingFastPushforward p eta heta heta_le v w hv hw hvw hwv a s) := by
  have hreward := measurable_liveRecordingFastPushforward_auxiliaryReward p r a
  have hpair := measurable_liveRecordingFastPair p eta heta heta_le
    v w hv hw hvw hwv a s
  have hsource := integrable_oneRoundAuxiliaryReward_fastArmDraw p eta heta heta_le
    v w hv hw hvw hwv r hr a
  have hcomp : Integrable
      ((fun z : Option (Fin p.K) × FastArm (assignmentSlowSet p a) =>
        oneRoundAuxiliaryReward r (assignmentSlowSet p a) z.2) ∘
          liveRecordingFastPair p eta heta heta_le v w hv hw hvw hwv a s)
      (ContinuousControlSlice.sliceLaw p.m p.K) := by
    simpa only [Function.comp_def, liveRecordingFastPair] using hsource
  exact (integrable_map_measure hreward.aestronglyMeasurable hpair.aemeasurable).2 hcomp

/-- Averaging the genuine continuous scalar reward over the existing
`slowSetPMF` is exactly `mixedAuxiliaryRewardExpectation`. -/
theorem continuousMixedAuxiliaryRewardExpectation_eq
    (p : Parameters) (eta : ℝ) (heta : 0 < eta)
    (heta_le : eta ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ)))
    (v w : Fin p.K → ℝ) (hv : ∀ i, 0 < v i) (hw : ∀ i, 0 < w i)
    (hvw : ∀ i, v i ≤ w i) (hwv : ∀ i, w i ≤ 2 * v i)
    (r : Fin p.K → ℝ) :
    (∑ U : SlowSet p.K p.m,
      (slowSetPMF w v p.two_le_m p.m_lt_K hw hv U).toReal *
        ∫ x : ContinuousCategorical.Scalar,
          oneRoundAuxiliaryReward r U
            (sampleFast p eta heta heta_le v w hv hw hvw hwv U x)
          ∂ ContinuousCategorical.uniform) =
      mixedAuxiliaryRewardExpectation p eta heta heta_le v w hv hw hvw hwv r := by
  classical
  rw [mixedAuxiliaryRewardExpectation]
  apply Finset.sum_congr rfl
  intro U hU
  rw [integral_oneRoundAuxiliaryReward_sampleFast p eta heta heta_le
    v w hv hw hvw hwv r U]

/-- The exact mixed auxiliary-reward lower bound holds for the real
continuous-scalar realization averaged over the existing `slowSetPMF`. -/
theorem continuousMixedAuxiliaryRewardExpectation_ge_theta_sub_gamma
    (p : Parameters) (eta : ℝ) (heta : 0 < eta)
    (heta_le : eta ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ)))
    (v w : Fin p.K → ℝ) (hv : ∀ i, 0 < v i) (hw : ∀ i, 0 < w i)
    (hvw : ∀ i, v i ≤ w i) (hwv : ∀ i, w i ≤ 2 * v i)
    (r : Fin p.K → ℝ) (hr : ∀ i, 0 ≤ r i ∧ r i ≤ 1) :
    (∑ U : SlowSet p.K p.m,
      (slowSetPMF w v p.two_le_m p.m_lt_K hw hv U).toReal *
        ∫ x : ContinuousCategorical.Scalar,
          oneRoundAuxiliaryReward r U
            (sampleFast p eta heta heta_le v w hv hw hvw hwv U x)
          ∂ ContinuousCategorical.uniform) ≥
      (∑ i : Fin p.K, ProductSetLaw.theta p.m w i * r i) - gamma p eta := by
  rw [continuousMixedAuxiliaryRewardExpectation_eq p eta heta heta_le
    v w hv hw hvw hwv r]
  exact mixedAuxiliaryRewardExpectation_ge_theta_sub_gamma p eta heta heta_le
    v w hv hw hvw hwv r hr

end Bandits.Support.FastRewardSliceLaw

end
