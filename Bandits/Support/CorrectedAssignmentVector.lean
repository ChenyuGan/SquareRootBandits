/-
Copyright (c) 2026 The Bandits Lean regret formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.CanonicalAssignmentVector
public import Bandits.Support.CanonicalOrientedSetLaw
public import Bandits.Support.ConstructorDimensions
public import Bandits.Support.ContinuousControlSlice
public import Bandits.Support.FiniteFibreLift
public import Bandits.Support.FiniteOrientationDisintegration
public import Bandits.Support.OrientedAssignmentLaw
public import Bandits.Support.ProductSetLaw
public import Bandits.Support.PrefixSetSampler
public import Bandits.Support.RecordedCorrectedWindow
public import Bandits.Support.RecordedQueueRun
public import Bandits.Support.RecordedSlowRefresh

import Mathlib.Tactic.Ring

/-!
# Corrected full-vector assignment sampler and fibre law

The sampler consumes the actual-prefix corrected mass from
`RecordedCorrectedWindow` and the full continuous assignment vector from
`OrientedAssignmentLaw`. Its finite orientation sums give the slow-set mass
from the corrected assignment law itself. The mass formula is the one in
`sources/zip4/manuscript/appendix_a_local_protocol.tex:66-77`, with the
fixed-anchor slow marginals from
`sources/zip4/manuscript/04_slow_fast_learner.tex:7-37`; the corresponding
finite-fibre construction is the internal measure step at
`sources/zip4/manuscript/06_interruptions.tex:410-423`.

This module proves a deterministic actual-prefix sampler and its entire
unconditional continuous-vector fibre law. It does not identify prefix
indices with an interruption schedule, construct the pending physical
refresh-PMF iteration, or establish physical-history conditioning.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Bandits.Support.CorrectedAssignmentVector

open Bandits.Support

local instance orientedOutcomeMeasurableSpace (K m : ℕ) :
    MeasurableSpace (OrientedAssignmentLaw.AssignmentOutcome K m) := ⊤

local instance orientedOutcomeDiscreteMeasurableSpace (K m : ℕ) :
    DiscreteMeasurableSpace (OrientedAssignmentLaw.AssignmentOutcome K m) :=
  ⟨fun _ => trivial⟩

local instance orientedSlowMeasurableSpace (K m : ℕ) :
    MeasurableSpace (OrientedAssignmentLaw.SlowSetCarrier K m) := ⊤

local instance orientedSlowDiscreteMeasurableSpace (K m : ℕ) :
    DiscreteMeasurableSpace (OrientedAssignmentLaw.SlowSetCarrier K m) :=
  ⟨fun _ => trivial⟩

local instance canonicalSlowMeasurableSpace (K m : ℕ) :
    MeasurableSpace (CanonicalOrientedSetLaw.SlowSet K m) := ⊤

local instance canonicalSlowDiscreteMeasurableSpace (K m : ℕ) :
    DiscreteMeasurableSpace (CanonicalOrientedSetLaw.SlowSet K m) :=
  ⟨fun _ => trivial⟩

local instance followerVectorMeasurableSpace (K m : ℕ) :
    MeasurableSpace (Fin (m - 1) → Fin K) := ⊤

local instance followerVectorDiscreteMeasurableSpace (K m : ℕ) :
    DiscreteMeasurableSpace (Fin (m - 1) → Fin K) := ⟨fun _ => trivial⟩

/-- The existing recorded slow marginal at the actual queue state after the
first `r` inputs of `rounds`. The anchor is fixed across all prefixes. -/
noncomputable def recordedPrefixSlowMass
    (p : ConstructorDimensions.Parameters) (q : RecordedQueueRun.Parameters)
    (rounds : List (RecordedQueueRun.RoundInput p.K)) (r : ℕ)
    (anchor : Fin p.K → ℝ) (hanchor : ∀ i, 0 < anchor i)
    (U : CanonicalOrientedSetLaw.SlowSet p.K p.m) : ℝ :=
  RecordedSlowRefresh.recordedSlowMass p q
    (RecordedQueueRun.run q (rounds.take r)) anchor hanchor U

/-- The literal corrected slow-fibre mass at prefix `v`, with `p_r` the
existing `recordedSlowMass` of the actual `rounds.take r` state and the same
fixed anchor at every prefix. This is a definition, not an assumed law. -/
noncomputable def slowFibreMass
    (p : ConstructorDimensions.Parameters) (q : RecordedQueueRun.Parameters)
    (_hcap : q.eta ≤ 1 /
      (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (Bandits.Support.CanonicalRecordingRates.L_stab p : ℝ)))
    (rounds : List (RecordedQueueRun.RoundInput p.K)) (u v : ℕ)
    (_hu : 1 ≤ u) (_huv : u ≤ v) (_hv : v ≤ rounds.length)
    (anchor : Fin p.K → ℝ) (hanchor : ∀ i, 0 < anchor i)
    (U : CanonicalOrientedSetLaw.SlowSet p.K p.m) : ℝ :=
  recordedPrefixSlowMass p q rounds v anchor hanchor U +
    (1 - RecordedSlowRefresh.hazard p q) ^ (v - u + 1) /
      RecordedSlowRefresh.hazard p q *
      (recordedPrefixSlowMass p q rounds u anchor hanchor U -
        recordedPrefixSlowMass p q rounds (u - 1) anchor hanchor U)

/-- The actual corrected full assignment sampler. Its first `K` scalars feed
the existing deterministic prefix sampler, while scalar `K` orients the
sampled set using the single fixed positive anchor. -/
noncomputable def correctedSampler
    (p : ConstructorDimensions.Parameters) (q : RecordedQueueRun.Parameters)
    (hcap : q.eta ≤ 1 /
      (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (Bandits.Support.CanonicalRecordingRates.L_stab p : ℝ)))
    (rounds : List (RecordedQueueRun.RoundInput p.K)) (u v : ℕ)
    (hu : 1 ≤ u) (huv : u ≤ v) (hv : v ≤ rounds.length)
    (anchor : Fin p.K → ℝ) (hanchor : ∀ i, 0 < anchor i) :
    (Fin (p.K + 1) → ContinuousControlSlice.Scalar) →
      OrientedAssignmentLaw.AssignmentOutcome p.K p.m :=
  OrientedAssignmentLaw.sampler p.two_le_m p.m_lt_K
    (RecordedCorrectedWindow.actualPrefixSamplerMass p q hcap rounds u v hu huv hv)
    anchor hanchor

/-- The slow-set output of the corrected full-vector sampler, transported to
the existing canonical supported-set carrier. -/
noncomputable def correctedSlowSampler
    (p : ConstructorDimensions.Parameters) (q : RecordedQueueRun.Parameters)
    (hcap : q.eta ≤ 1 /
      (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (Bandits.Support.CanonicalRecordingRates.L_stab p : ℝ)))
    (rounds : List (RecordedQueueRun.RoundInput p.K)) (u v : ℕ)
    (hu : 1 ≤ u) (huv : u ≤ v) (hv : v ≤ rounds.length)
    (anchor : Fin p.K → ℝ) (hanchor : ∀ i, 0 < anchor i)
    (x : Fin (p.K + 1) → ContinuousControlSlice.Scalar) :
    CanonicalOrientedSetLaw.SlowSet p.K p.m :=
  CanonicalAssignmentVector.slowCarrierEquiv p.two_le_m
    (OrientedAssignmentLaw.slowSampler p.two_le_m p.m_lt_K
      (RecordedCorrectedWindow.actualPrefixSamplerMass p q hcap rounds u v hu huv hv)
      anchor hanchor x)

/-- The actual follower-arm vector in increasing arm-label order. -/
noncomputable def correctedFollowerArms
    (p : ConstructorDimensions.Parameters) (q : RecordedQueueRun.Parameters)
    (hcap : q.eta ≤ 1 /
      (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (Bandits.Support.CanonicalRecordingRates.L_stab p : ℝ)))
    (rounds : List (RecordedQueueRun.RoundInput p.K)) (u v : ℕ)
    (hu : 1 ≤ u) (huv : u ≤ v) (hv : v ≤ rounds.length)
    (anchor : Fin p.K → ℝ) (hanchor : ∀ i, 0 < anchor i)
    (x : Fin (p.K + 1) → ContinuousControlSlice.Scalar) :
    Fin (p.m - 1) → Fin p.K :=
  fun r => CanonicalAssignmentVector.followerArm p.two_le_m
    (correctedSlowSampler p q hcap rounds u v hu huv hv anchor hanchor x) r

/-- Measurability of the full-vector oriented sampler. -/
theorem correctedSampler_measurable
    (p : ConstructorDimensions.Parameters) (q : RecordedQueueRun.Parameters)
    (hcap : q.eta ≤ 1 /
      (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (Bandits.Support.CanonicalRecordingRates.L_stab p : ℝ)))
    (rounds : List (RecordedQueueRun.RoundInput p.K)) (u v : ℕ)
    (hu : 1 ≤ u) (huv : u ≤ v) (hv : v ≤ rounds.length)
    (anchor : Fin p.K → ℝ) (hanchor : ∀ i, 0 < anchor i) :
    Measurable (correctedSampler p q hcap rounds u v hu huv hv anchor hanchor) := by
  unfold correctedSampler
  exact OrientedAssignmentLaw.measurable_sampler p.two_le_m p.m_lt_K
    (RecordedCorrectedWindow.actualPrefixSamplerMass p q hcap rounds u v hu huv hv)
    anchor hanchor

/-- Measurability of the canonical slow-set output. -/
theorem correctedSlowSampler_measurable
    (p : ConstructorDimensions.Parameters) (q : RecordedQueueRun.Parameters)
    (hcap : q.eta ≤ 1 /
      (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (Bandits.Support.CanonicalRecordingRates.L_stab p : ℝ)))
    (rounds : List (RecordedQueueRun.RoundInput p.K)) (u v : ℕ)
    (hu : 1 ≤ u) (huv : u ≤ v) (hv : v ≤ rounds.length)
    (anchor : Fin p.K → ℝ) (hanchor : ∀ i, 0 < anchor i) :
    Measurable (correctedSlowSampler p q hcap rounds u v hu huv hv anchor hanchor) := by
  have hslow := OrientedAssignmentLaw.measurable_slowSampler p.two_le_m p.m_lt_K
    (RecordedCorrectedWindow.actualPrefixSamplerMass p q hcap rounds u v hu huv hv)
    anchor hanchor
  exact (measurable_of_finite _).comp hslow

/-- Measurability of the ordered follower-arm vector. -/
theorem correctedFollowerArms_measurable
    (p : ConstructorDimensions.Parameters) (q : RecordedQueueRun.Parameters)
    (hcap : q.eta ≤ 1 /
      (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (Bandits.Support.CanonicalRecordingRates.L_stab p : ℝ)))
    (rounds : List (RecordedQueueRun.RoundInput p.K)) (u v : ℕ)
    (hu : 1 ≤ u) (huv : u ≤ v) (hv : v ≤ rounds.length)
    (anchor : Fin p.K → ℝ) (hanchor : ∀ i, 0 < anchor i) :
    Measurable (correctedFollowerArms p q hcap rounds u v hu huv hv anchor hanchor) := by
  have hslow := correctedSlowSampler_measurable p q hcap rounds u v hu huv hv anchor hanchor
  have hfollow : Measurable (fun U : CanonicalOrientedSetLaw.SlowSet p.K p.m =>
      fun r => CanonicalAssignmentVector.followerArm p.two_le_m U r) :=
    measurable_of_finite _
  exact hfollow.comp hslow

/-- Exact joint atom mass of the full continuous-vector sampler. The corrected
mass can be zero; no positivity is required. -/
theorem correctedSampler_outcome_atom_mass
    (p : ConstructorDimensions.Parameters) (q : RecordedQueueRun.Parameters)
    (hcap : q.eta ≤ 1 /
      (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (Bandits.Support.CanonicalRecordingRates.L_stab p : ℝ)))
    (rounds : List (RecordedQueueRun.RoundInput p.K)) (u v : ℕ)
    (hu : 1 ≤ u) (huv : u ≤ v) (hv : v ≤ rounds.length)
    (anchor : Fin p.K → ℝ) (hanchor : ∀ i, 0 < anchor i)
    (S : PrefixSetSampler.SetCarrier p.K p.m)
    (j : {j : Fin p.K // j ∈ S.1}) :
    ContinuousControlSlice.assignmentLaw p.K
      (correctedSampler p q hcap rounds u v hu huv hv anchor hanchor ⁻¹'
        {⟨(S, j.1), j.2⟩}) =
      ENNReal.ofReal
        (RecordedCorrectedWindow.actualPrefixCorrectedMass p q hcap rounds u v hu huv hv
          (RecordedCorrectedWindow.samplerProductSetEquiv p.K p.m S) *
          FiniteOrientationDisintegration.orientationProbability anchor S.1
            (OrientedAssignmentLaw.sampled_set_nonempty p.two_le_m S)
            (fun i _ => hanchor i) j) := by
  unfold correctedSampler
  rw [OrientedAssignmentLaw.assignmentLaw_sampler_singleton,
    RecordedCorrectedWindow.actualPrefixSamplerMass_weight]

/-- Exact atom mass for a slow set with one valid inserted fast arm. -/
theorem correctedSampler_insertedOutcome_atom_mass
    (p : ConstructorDimensions.Parameters) (q : RecordedQueueRun.Parameters)
    (hcap : q.eta ≤ 1 /
      (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (Bandits.Support.CanonicalRecordingRates.L_stab p : ℝ)))
    (rounds : List (RecordedQueueRun.RoundInput p.K)) (u v : ℕ)
    (hu : 1 ≤ u) (huv : u ≤ v) (hv : v ≤ rounds.length)
    (anchor : Fin p.K → ℝ) (hanchor : ∀ i, 0 < anchor i)
    (U : OrientedAssignmentLaw.SlowSetCarrier p.K p.m)
    (j : {j : Fin p.K // j ∈ Finset.univ \ U.1}) :
    ContinuousControlSlice.assignmentLaw p.K
      (correctedSampler p q hcap rounds u v hu huv hv anchor hanchor ⁻¹'
        {OrientedAssignmentLaw.insertedOutcome U j}) =
      ENNReal.ofReal
        (RecordedCorrectedWindow.actualPrefixCorrectedMass p q hcap rounds u v hu huv hv
          (RecordedCorrectedWindow.samplerProductSetEquiv p.K p.m
            (OrientedAssignmentLaw.insertedSet U j)) *
          FiniteOrientationDisintegration.orientationProbability anchor
            (insert j.1 U.1) (Finset.insert_nonempty _ _)
            (fun i _ => hanchor i) ⟨j.1, Finset.mem_insert_self _ _⟩) := by
  have h := correctedSampler_outcome_atom_mass p q hcap rounds u v hu huv hv
    anchor hanchor (OrientedAssignmentLaw.insertedSet U j)
    ⟨j.1, Finset.mem_insert_self _ _⟩
  simpa only [OrientedAssignmentLaw.insertedOutcome, OrientedAssignmentLaw.insertedSet] using h

/-- If a corrected set atom is zero, each oriented outcome over it remains a
zero atom of the continuous sampler. -/
theorem correctedSampler_outcome_atom_eq_zero_of_set_mass_eq_zero
    (p : ConstructorDimensions.Parameters) (q : RecordedQueueRun.Parameters)
    (hcap : q.eta ≤ 1 /
      (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (Bandits.Support.CanonicalRecordingRates.L_stab p : ℝ)))
    (rounds : List (RecordedQueueRun.RoundInput p.K)) (u v : ℕ)
    (hu : 1 ≤ u) (huv : u ≤ v) (hv : v ≤ rounds.length)
    (anchor : Fin p.K → ℝ) (hanchor : ∀ i, 0 < anchor i)
    (S : PrefixSetSampler.SetCarrier p.K p.m)
    (j : {j : Fin p.K // j ∈ S.1})
    (hzero : RecordedCorrectedWindow.actualPrefixCorrectedMass p q hcap rounds u v hu huv hv
      (RecordedCorrectedWindow.samplerProductSetEquiv p.K p.m S) = 0) :
    ContinuousControlSlice.assignmentLaw p.K
      (correctedSampler p q hcap rounds u v hu huv hv anchor hanchor ⁻¹'
        {⟨(S, j.1), j.2⟩}) = 0 := by
  rw [correctedSampler_outcome_atom_mass]
  simp [hzero]

private theorem recordedPrefixSlowMass_eq_productOrientationSum
    (p : ConstructorDimensions.Parameters) (q : RecordedQueueRun.Parameters)
    (rounds : List (RecordedQueueRun.RoundInput p.K)) (r : ℕ)
    (anchor : Fin p.K → ℝ) (hanchor : ∀ i, 0 < anchor i)
    (U : CanonicalOrientedSetLaw.SlowSet p.K p.m) :
    recordedPrefixSlowMass p q rounds r anchor hanchor U =
      OrientedAssignmentLaw.slowOutcomeMass p.two_le_m
        (CanonicalAssignmentVector.productQNormalizedMass p.two_le_m p.m_lt_K
          (RecordedCorrectedWindow.prefixScoreWeight p q rounds r)
          (fun i => RecordedSlowRefresh.scoreWeight_pos q
            (RecordedQueueRun.run q (rounds.take r)) i))
        anchor hanchor ((CanonicalAssignmentVector.slowCarrierEquiv p.two_le_m).symm U) := by
  let w := RecordedCorrectedWindow.prefixScoreWeight p q rounds r
  have hw : ∀ i, 0 < w i := by
    intro i
    exact RecordedSlowRefresh.scoreWeight_pos q
      (RecordedQueueRun.run q (rounds.take r)) i
  have h := CanonicalAssignmentVector.slowOutcomeMass_eq_slowMarginal
    p.two_le_m p.m_lt_K w anchor hw hanchor
    ((CanonicalAssignmentVector.slowCarrierEquiv p.two_le_m).symm U)
  change CanonicalOrientedSetLaw.slowMarginal w anchor p.two_le_m p.m_lt_K
      hw hanchor U =
    OrientedAssignmentLaw.slowOutcomeMass p.two_le_m
      (CanonicalAssignmentVector.productQNormalizedMass p.two_le_m p.m_lt_K w hw)
      anchor hanchor ((CanonicalAssignmentVector.slowCarrierEquiv p.two_le_m).symm U)
  exact h.symm

/-- The finite insertion sum of the constructed corrected assignment law is
the exact corrected slow-fibre formula. It is derived by summing the actual
corrected orientation atoms, then distributing the finite sums over the
actual-prefix corrected-mass identity. -/
theorem correctedSlowOutcomeMass_eq_slowFibreMass
    (p : ConstructorDimensions.Parameters) (q : RecordedQueueRun.Parameters)
    (hcap : q.eta ≤ 1 /
      (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (Bandits.Support.CanonicalRecordingRates.L_stab p : ℝ)))
    (rounds : List (RecordedQueueRun.RoundInput p.K)) (u v : ℕ)
    (hu : 1 ≤ u) (huv : u ≤ v) (hv : v ≤ rounds.length)
    (anchor : Fin p.K → ℝ) (hanchor : ∀ i, 0 < anchor i)
    (U : CanonicalOrientedSetLaw.SlowSet p.K p.m) :
    OrientedAssignmentLaw.slowOutcomeMass p.two_le_m
        (RecordedCorrectedWindow.actualPrefixSamplerMass p q hcap rounds u v hu huv hv)
        anchor hanchor ((CanonicalAssignmentVector.slowCarrierEquiv p.two_le_m).symm U) =
      slowFibreMass p q hcap rounds u v hu huv hv anchor hanchor U := by
  classical
  let Uo := (CanonicalAssignmentVector.slowCarrierEquiv p.two_le_m).symm U
  let D := (Finset.univ \ Uo.1).attach
  let alpha (j : {j : Fin p.K // j ∈ Finset.univ \ Uo.1}) : ℝ :=
    FiniteOrientationDisintegration.orientationProbability anchor (insert j.1 Uo.1)
      (Finset.insert_nonempty _ _) (fun i _ => hanchor i)
      ⟨j.1, Finset.mem_insert_self _ _⟩
  let a (r : ℕ) (j : {j : Fin p.K // j ∈ Finset.univ \ Uo.1}) : ℝ :=
    RecordedCorrectedWindow.prefixQ p q rounds r
      (RecordedCorrectedWindow.samplerProductSetEquiv p.K p.m
        (OrientedAssignmentLaw.insertedSet Uo j))
  have hcorrectedAtom (j : {j : Fin p.K // j ∈ Finset.univ \ Uo.1}) :
      (RecordedCorrectedWindow.actualPrefixSamplerMass p q hcap rounds u v hu huv hv).weight
          (OrientedAssignmentLaw.insertedSet Uo j) =
        a v j +
          (1 - RecordedSlowRefresh.hazard p q) ^ (v - u + 1) /
            RecordedSlowRefresh.hazard p q * (a u j - a (u - 1) j) := by
    rw [RecordedCorrectedWindow.actualPrefixSamplerMass_weight,
      RecordedCorrectedWindow.actualPrefixCorrectedMass_formula]
  have hdecompose :
      (∑ j ∈ D,
        (a v j +
          (1 - RecordedSlowRefresh.hazard p q) ^ (v - u + 1) /
            RecordedSlowRefresh.hazard p q * (a u j - a (u - 1) j)) * alpha j) =
        (∑ j ∈ D, a v j * alpha j) +
          (1 - RecordedSlowRefresh.hazard p q) ^ (v - u + 1) /
            RecordedSlowRefresh.hazard p q *
            ((∑ j ∈ D, a u j * alpha j) - (∑ j ∈ D, a (u - 1) j * alpha j)) := by
    calc
      _ = ∑ j ∈ D, (
          a v j * alpha j +
            ((1 - RecordedSlowRefresh.hazard p q) ^ (v - u + 1) /
              RecordedSlowRefresh.hazard p q) *
              ((a u j - a (u - 1) j) * alpha j)) := by
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        congr 1
        simp_rw [sub_mul]
        rw [Finset.sum_sub_distrib]
  have hsum (r : ℕ) :
      (∑ j ∈ D, a r j * alpha j) = recordedPrefixSlowMass p q rounds r anchor hanchor U := by
    change OrientedAssignmentLaw.slowOutcomeMass p.two_le_m
        (CanonicalAssignmentVector.productQNormalizedMass p.two_le_m p.m_lt_K
          (RecordedCorrectedWindow.prefixScoreWeight p q rounds r)
          (fun i => RecordedSlowRefresh.scoreWeight_pos q
            (RecordedQueueRun.run q (rounds.take r)) i))
        anchor hanchor Uo = recordedPrefixSlowMass p q rounds r anchor hanchor U
    exact (recordedPrefixSlowMass_eq_productOrientationSum p q rounds r anchor hanchor U).symm
  unfold OrientedAssignmentLaw.slowOutcomeMass
  calc
    _ = ∑ j ∈ D,
        (a v j +
          (1 - RecordedSlowRefresh.hazard p q) ^ (v - u + 1) /
            RecordedSlowRefresh.hazard p q * (a u j - a (u - 1) j)) * alpha j := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [hcorrectedAtom]
    _ = _ := by rw [hdecompose, hsum v, hsum u, hsum (u - 1)]; rfl

/-- The concrete corrected slow-fibre masses are nonnegative, as follows from
their representation as insertion sums of the constructed sampler. -/
theorem slowFibreMass_nonneg
    (p : ConstructorDimensions.Parameters) (q : RecordedQueueRun.Parameters)
    (hcap : q.eta ≤ 1 /
      (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (Bandits.Support.CanonicalRecordingRates.L_stab p : ℝ)))
    (rounds : List (RecordedQueueRun.RoundInput p.K)) (u v : ℕ)
    (hu : 1 ≤ u) (huv : u ≤ v) (hv : v ≤ rounds.length)
    (anchor : Fin p.K → ℝ) (hanchor : ∀ i, 0 < anchor i)
    (U : CanonicalOrientedSetLaw.SlowSet p.K p.m) :
    0 ≤ slowFibreMass p q hcap rounds u v hu huv hv anchor hanchor U := by
  rw [← correctedSlowOutcomeMass_eq_slowFibreMass p q hcap rounds u v hu huv hv
    anchor hanchor U]
  exact OrientedAssignmentLaw.slowOutcomeMass_nonneg p.two_le_m
    (RecordedCorrectedWindow.actualPrefixSamplerMass p q hcap rounds u v hu huv hv)
    anchor hanchor ((CanonicalAssignmentVector.slowCarrierEquiv p.two_le_m).symm U)

/-- The concrete corrected slow-fibre masses normalize to one. The equality is
inherited from the finite-fibre partition of the constructed sampler. -/
theorem slowFibreMass_sum_eq_one
    (p : ConstructorDimensions.Parameters) (q : RecordedQueueRun.Parameters)
    (hcap : q.eta ≤ 1 /
      (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (Bandits.Support.CanonicalRecordingRates.L_stab p : ℝ)))
    (rounds : List (RecordedQueueRun.RoundInput p.K)) (u v : ℕ)
    (hu : 1 ≤ u) (huv : u ≤ v) (hv : v ≤ rounds.length)
    (anchor : Fin p.K → ℝ) (hanchor : ∀ i, 0 < anchor i) :
    (∑ U : CanonicalOrientedSetLaw.SlowSet p.K p.m,
      slowFibreMass p q hcap rounds u v hu huv hv anchor hanchor U) = 1 := by
  let e : OrientedAssignmentLaw.SlowSetCarrier p.K p.m ≃
      CanonicalOrientedSetLaw.SlowSet p.K p.m :=
    CanonicalAssignmentVector.slowCarrierEquiv p.two_le_m
  have hsum := Fintype.sum_equiv e
    (fun U => OrientedAssignmentLaw.slowOutcomeMass p.two_le_m
      (RecordedCorrectedWindow.actualPrefixSamplerMass p q hcap rounds u v hu huv hv)
      anchor hanchor U)
    (fun U => slowFibreMass p q hcap rounds u v hu huv hv anchor hanchor U)
    (fun U => by
      simpa [e] using correctedSlowOutcomeMass_eq_slowFibreMass p q hcap rounds u v hu huv hv
        anchor hanchor (e U))
  calc
    _ = ∑ U : OrientedAssignmentLaw.SlowSetCarrier p.K p.m,
        OrientedAssignmentLaw.slowOutcomeMass p.two_le_m
          (RecordedCorrectedWindow.actualPrefixSamplerMass p q hcap rounds u v hu huv hv)
          anchor hanchor U := hsum.symm
    _ = 1 := OrientedAssignmentLaw.slowOutcomeMass_sum_eq_one p.two_le_m p.m_lt_K
      (RecordedCorrectedWindow.actualPrefixSamplerMass p q hcap rounds u v hu huv hv)
      anchor hanchor

/-- The derived fibre mass of the canonical slow-set sampler is the exact
corrected slow marginal, including zero-mass fibres. -/
theorem correctedSlowSampler_fibreMass
    (p : ConstructorDimensions.Parameters) (q : RecordedQueueRun.Parameters)
    (hcap : q.eta ≤ 1 /
      (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (Bandits.Support.CanonicalRecordingRates.L_stab p : ℝ)))
    (rounds : List (RecordedQueueRun.RoundInput p.K)) (u v : ℕ)
    (hu : 1 ≤ u) (huv : u ≤ v) (hv : v ≤ rounds.length)
    (anchor : Fin p.K → ℝ) (hanchor : ∀ i, 0 < anchor i)
    (U : CanonicalOrientedSetLaw.SlowSet p.K p.m) :
    FiniteFibreLift.fibreMass (ContinuousControlSlice.assignmentLaw p.K)
        (correctedSlowSampler p q hcap rounds u v hu huv hv anchor hanchor) U =
      ENNReal.ofReal (slowFibreMass p q hcap rounds u v hu huv hv anchor hanchor U) := by
  let μ := RecordedCorrectedWindow.actualPrefixSamplerMass p q hcap rounds u v hu huv hv
  let e : OrientedAssignmentLaw.SlowSetCarrier p.K p.m ≃
      CanonicalOrientedSetLaw.SlowSet p.K p.m :=
    CanonicalAssignmentVector.slowCarrierEquiv p.two_le_m
  have hpre :
      correctedSlowSampler p q hcap rounds u v hu huv hv anchor hanchor ⁻¹' {U} =
        OrientedAssignmentLaw.slowSampler p.two_le_m p.m_lt_K μ anchor hanchor ⁻¹'
          {e.symm U} := by
    ext x
    change e (OrientedAssignmentLaw.slowSampler p.two_le_m p.m_lt_K μ anchor hanchor x) = U ↔
      OrientedAssignmentLaw.slowSampler p.two_le_m p.m_lt_K μ anchor hanchor x = e.symm U
    constructor
    · intro h
      have h' := congrArg e.symm h
      simpa using h'
    · intro h
      have h' := congrArg e h
      simpa using h'
  calc
    _ = FiniteFibreLift.fibreMass (ContinuousControlSlice.assignmentLaw p.K)
        (OrientedAssignmentLaw.slowSampler p.two_le_m p.m_lt_K μ anchor hanchor) (e.symm U) := by
      change ContinuousControlSlice.assignmentLaw p.K
        (correctedSlowSampler p q hcap rounds u v hu huv hv anchor hanchor ⁻¹' {U}) =
        ContinuousControlSlice.assignmentLaw p.K
          (OrientedAssignmentLaw.slowSampler p.two_le_m p.m_lt_K μ anchor hanchor ⁻¹'
            {e.symm U})
      rw [hpre]
    _ = ENNReal.ofReal
        (OrientedAssignmentLaw.slowOutcomeMass p.two_le_m μ anchor hanchor (e.symm U)) :=
      OrientedAssignmentLaw.fibreMass_eq_slowOutcomeMass p.two_le_m p.m_lt_K μ anchor hanchor
        (e.symm U)
    _ = ENNReal.ofReal (slowFibreMass p q hcap rounds u v hu huv hv anchor hanchor U) := by
      rw [correctedSlowOutcomeMass_eq_slowFibreMass p q hcap rounds u v hu huv hv
        anchor hanchor U]

/-- Mixing by the constructed corrected fibre masses and their concrete
full-vector fibre measures recovers the entire assignment-law measure. -/
theorem correctedSlowSampler_fibre_mixture
    (p : ConstructorDimensions.Parameters) (q : RecordedQueueRun.Parameters)
    (hcap : q.eta ≤ 1 /
      (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (Bandits.Support.CanonicalRecordingRates.L_stab p : ℝ)))
    (rounds : List (RecordedQueueRun.RoundInput p.K)) (u v : ℕ)
    (hu : 1 ≤ u) (huv : u ≤ v) (hv : v ≤ rounds.length)
    (anchor : Fin p.K → ℝ) (hanchor : ∀ i, 0 < anchor i) :
    (∑ U : CanonicalOrientedSetLaw.SlowSet p.K p.m,
      ENNReal.ofReal (slowFibreMass p q hcap rounds u v hu huv hv anchor hanchor U) •
        FiniteFibreLift.fibreMeasure (ContinuousControlSlice.assignmentLaw p.K)
          (correctedSlowSampler p q hcap rounds u v hu huv hv anchor hanchor) U) =
      ContinuousControlSlice.assignmentLaw p.K := by
  calc
    _ = ∑ U : CanonicalOrientedSetLaw.SlowSet p.K p.m,
        FiniteFibreLift.fibreMass (ContinuousControlSlice.assignmentLaw p.K)
          (correctedSlowSampler p q hcap rounds u v hu huv hv anchor hanchor) U •
        FiniteFibreLift.fibreMeasure (ContinuousControlSlice.assignmentLaw p.K)
          (correctedSlowSampler p q hcap rounds u v hu huv hv anchor hanchor) U := by
      apply Finset.sum_congr rfl
      intro U hU
      rw [correctedSlowSampler_fibreMass]
    _ = ContinuousControlSlice.assignmentLaw p.K :=
      FiniteFibreLift.sum_fibreMass_smul_fibreMeasure
        (μ := ContinuousControlSlice.assignmentLaw p.K)
        (F := correctedSlowSampler p q hcap rounds u v hu huv hv anchor hanchor)
        (correctedSlowSampler_measurable p q hcap rounds u v hu huv hv anchor hanchor)

/-- On a positive corrected fibre, the lifted full-vector measure returns the
chosen slow set almost everywhere. -/
theorem ae_correctedSlowSampler_fibre_eq
    (p : ConstructorDimensions.Parameters) (q : RecordedQueueRun.Parameters)
    (hcap : q.eta ≤ 1 /
      (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (Bandits.Support.CanonicalRecordingRates.L_stab p : ℝ)))
    (rounds : List (RecordedQueueRun.RoundInput p.K)) (u v : ℕ)
    (hu : 1 ≤ u) (huv : u ≤ v) (hv : v ≤ rounds.length)
    (anchor : Fin p.K → ℝ) (hanchor : ∀ i, 0 < anchor i)
    (U : CanonicalOrientedSetLaw.SlowSet p.K p.m)
    (hpositive : 0 < slowFibreMass p q hcap rounds u v hu huv hv anchor hanchor U) :
    ∀ᵐ x ∂FiniteFibreLift.fibreMeasure (ContinuousControlSlice.assignmentLaw p.K)
        (correctedSlowSampler p q hcap rounds u v hu huv hv anchor hanchor) U,
      correctedSlowSampler p q hcap rounds u v hu huv hv anchor hanchor x = U :=
  FiniteFibreLift.ae_fibreMeasure_eq
    (μ := ContinuousControlSlice.assignmentLaw p.K)
    (F := correctedSlowSampler p q hcap rounds u v hu huv hv anchor hanchor)
    (a := U)
    (correctedSlowSampler_measurable p q hcap rounds u v hu huv hv anchor hanchor)
    (by
      rw [correctedSlowSampler_fibreMass]
      exact ne_of_gt (ENNReal.ofReal_pos.mpr hpositive))

/-- A null corrected fibre retains the accepted original full-vector law. -/
theorem correctedSlowSampler_null_fibre_measure
    (p : ConstructorDimensions.Parameters) (q : RecordedQueueRun.Parameters)
    (hcap : q.eta ≤ 1 /
      (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (Bandits.Support.CanonicalRecordingRates.L_stab p : ℝ)))
    (rounds : List (RecordedQueueRun.RoundInput p.K)) (u v : ℕ)
    (hu : 1 ≤ u) (huv : u ≤ v) (hv : v ≤ rounds.length)
    (anchor : Fin p.K → ℝ) (hanchor : ∀ i, 0 < anchor i)
    (U : CanonicalOrientedSetLaw.SlowSet p.K p.m)
    (hzero : slowFibreMass p q hcap rounds u v hu huv hv anchor hanchor U = 0) :
    FiniteFibreLift.fibreMeasure (ContinuousControlSlice.assignmentLaw p.K)
        (correctedSlowSampler p q hcap rounds u v hu huv hv anchor hanchor) U =
      ContinuousControlSlice.assignmentLaw p.K := by
  apply FiniteFibreLift.fibreMeasure_of_eq_zero
  rw [correctedSlowSampler_fibreMass, hzero]
  simp

/-- Exact conditional probability of an inserted fast outcome on a positive
corrected slow fibre. This is the corrected law `f_v(U ∪ {j}) α_j(U ∪ {j}) /
ν_v(U)`; it is not asserted to equal the canonical `q_w(j | U)`. -/
theorem corrected_conditional_insertedOutcome_probability
    (p : ConstructorDimensions.Parameters) (q : RecordedQueueRun.Parameters)
    (hcap : q.eta ≤ 1 /
      (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (Bandits.Support.CanonicalRecordingRates.L_stab p : ℝ)))
    (rounds : List (RecordedQueueRun.RoundInput p.K)) (u v : ℕ)
    (hu : 1 ≤ u) (huv : u ≤ v) (hv : v ≤ rounds.length)
    (anchor : Fin p.K → ℝ) (hanchor : ∀ i, 0 < anchor i)
    (U : OrientedAssignmentLaw.SlowSetCarrier p.K p.m)
    (j : {j : Fin p.K // j ∈ Finset.univ \ U.1})
    (hpositive : 0 < slowFibreMass p q hcap rounds u v hu huv hv anchor hanchor
      (CanonicalAssignmentVector.slowCarrierEquiv p.two_le_m U)) :
    FiniteFibreLift.fibreMeasure (ContinuousControlSlice.assignmentLaw p.K)
        (correctedSlowSampler p q hcap rounds u v hu huv hv anchor hanchor)
        (CanonicalAssignmentVector.slowCarrierEquiv p.two_le_m U)
      (correctedSampler p q hcap rounds u v hu huv hv anchor hanchor ⁻¹'
        {OrientedAssignmentLaw.insertedOutcome U j}) =
      ENNReal.ofReal
        (RecordedCorrectedWindow.actualPrefixCorrectedMass p q hcap rounds u v hu huv hv
          (RecordedCorrectedWindow.samplerProductSetEquiv p.K p.m
            (OrientedAssignmentLaw.insertedSet U j)) *
          FiniteOrientationDisintegration.orientationProbability anchor
            (insert j.1 U.1) (Finset.insert_nonempty _ _)
            (fun i _ => hanchor i) ⟨j.1, Finset.mem_insert_self _ _⟩ /
          slowFibreMass p q hcap rounds u v hu huv hv anchor hanchor
            (CanonicalAssignmentVector.slowCarrierEquiv p.two_le_m U)) := by
  let e : OrientedAssignmentLaw.SlowSetCarrier p.K p.m ≃
      CanonicalOrientedSetLaw.SlowSet p.K p.m :=
    CanonicalAssignmentVector.slowCarrierEquiv p.two_le_m
  let Uc := e U
  let F := correctedSlowSampler p q hcap rounds u v hu huv hv anchor hanchor
  let C := correctedSampler p q hcap rounds u v hu huv hv anchor hanchor ⁻¹'
    {OrientedAssignmentLaw.insertedOutcome U j}
  have hmass :
      FiniteFibreLift.fibreMass (ContinuousControlSlice.assignmentLaw p.K) F Uc ≠ 0 := by
    rw [correctedSlowSampler_fibreMass]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr hpositive)
  have hsampler := correctedSampler_measurable p q hcap rounds u v hu huv hv anchor hanchor
  have hC : MeasurableSet C := hsampler (measurableSet_singleton _)
  have hsubset : C ⊆ FiniteFibreLift.fibre F Uc := by
    intro x hx
    change correctedSampler p q hcap rounds u v hu huv hv anchor hanchor x =
      OrientedAssignmentLaw.insertedOutcome U j at hx
    change e (OrientedAssignmentLaw.slowOutcome
      (OrientedAssignmentLaw.sampler p.two_le_m p.m_lt_K
        (RecordedCorrectedWindow.actualPrefixSamplerMass p q hcap rounds u v hu huv hv)
        anchor hanchor x)) = Uc
    have hx' : OrientedAssignmentLaw.sampler p.two_le_m p.m_lt_K
        (RecordedCorrectedWindow.actualPrefixSamplerMass p q hcap rounds u v hu huv hv)
        anchor hanchor x = OrientedAssignmentLaw.insertedOutcome U j := by
      simpa [correctedSampler] using hx
    rw [hx', OrientedAssignmentLaw.slowOutcome_insertedOutcome]
  have hinter : C ∩ FiniteFibreLift.fibre F Uc = C := Set.inter_eq_left.mpr hsubset
  have happly := FiniteFibreLift.fibreMeasure_apply
    (μ := ContinuousControlSlice.assignmentLaw p.K) (F := F) (a := Uc) hmass hC
  calc
    _ = ContinuousControlSlice.assignmentLaw p.K C /
        FiniteFibreLift.fibreMass (ContinuousControlSlice.assignmentLaw p.K) F Uc := by
      rw [happly, hinter]
    _ = ENNReal.ofReal
          (RecordedCorrectedWindow.actualPrefixCorrectedMass p q hcap rounds u v hu huv hv
            (RecordedCorrectedWindow.samplerProductSetEquiv p.K p.m
              (OrientedAssignmentLaw.insertedSet U j)) *
            FiniteOrientationDisintegration.orientationProbability anchor
              (insert j.1 U.1) (Finset.insert_nonempty _ _)
              (fun i _ => hanchor i) ⟨j.1, Finset.mem_insert_self _ _⟩) /
        ENNReal.ofReal (slowFibreMass p q hcap rounds u v hu huv hv anchor hanchor Uc) := by
      rw [correctedSlowSampler_fibreMass]
      dsimp [C]
      rw [correctedSampler_insertedOutcome_atom_mass]
    _ = _ := by
      rw [← ENNReal.ofReal_div_of_pos hpositive]

/-- The formula remains valid at the boundary case `v = u`; the exponent is
then exactly one and no positive-mass assumption has been added. -/
theorem slowFibreMass_at_window_start
    (p : ConstructorDimensions.Parameters) (q : RecordedQueueRun.Parameters)
    (hcap : q.eta ≤ 1 /
      (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (Bandits.Support.CanonicalRecordingRates.L_stab p : ℝ)))
    (rounds : List (RecordedQueueRun.RoundInput p.K)) (u : ℕ)
    (hu : 1 ≤ u) (huLen : u ≤ rounds.length)
    (anchor : Fin p.K → ℝ) (hanchor : ∀ i, 0 < anchor i)
    (U : CanonicalOrientedSetLaw.SlowSet p.K p.m) :
    slowFibreMass p q hcap rounds u u hu le_rfl huLen anchor hanchor U =
      recordedPrefixSlowMass p q rounds u anchor hanchor U +
        (1 - RecordedSlowRefresh.hazard p q) /
          RecordedSlowRefresh.hazard p q *
          (recordedPrefixSlowMass p q rounds u anchor hanchor U -
            recordedPrefixSlowMass p q rounds (u - 1) anchor hanchor U) := by
  rw [slowFibreMass]
  simp

end Bandits.Support.CorrectedAssignmentVector

end
