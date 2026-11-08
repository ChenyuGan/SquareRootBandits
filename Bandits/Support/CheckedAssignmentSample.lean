/-
Copyright (c) 2026 The Bandits Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.CheckedPrefixSampler
public import Bandits.Support.CheckedAssignmentOrientation
public import Bandits.Support.CanonicalAssignmentVector
public import Bandits.Support.CorrectedAssignmentVector
public import Bandits.Support.FiniteFibreLift
public import Bandits.Support.RecordedCorrectedWindow
public import Bandits.Support.ContinuousControlSlice
public import Bandits.Support.ConstructorDimensions
public import Bandits.Support.OrientedAssignmentLaw
public import Bandits.Support.PrefixSamplerLaw

/-!
# Checked assignment from the original full scalar vector

This module composes the accepted checked prefix operation with the accepted
checked orientation operation on the same original `K + 1` scalar vector.
Prefix failures short-circuit orientation, and orientation failures remain
explicit. The source passages are
`sources/zip4/manuscript/04_slow_fast_learner.tex:7-37`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:8-12,66-77`, and
`sources/zip4/manuscript/06_interruptions.tex:410-423`.

All probabilistic statements here use fixed supplied input. They do not assert
freshness conditional on a physical or adaptive history.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal BigOperators

namespace Bandits.Support.CheckedAssignmentSample

open Bandits.Support
open Bandits.Support.ContinuousControlSlice
open Bandits.Support.PrefixSamplerLaw
open Bandits.Support.OrientedAssignmentLaw

local instance assignmentOutcomeMeasurableSpace (K m : ℕ) :
    MeasurableSpace (OrientedAssignmentLaw.AssignmentOutcome K m) := ⊤

local instance assignmentOutcomeDiscreteMeasurableSpace (K m : ℕ) :
    DiscreteMeasurableSpace (OrientedAssignmentLaw.AssignmentOutcome K m) :=
  ⟨fun _ => trivial⟩

local instance canonicalSlowMeasurableSpace (K m : ℕ) :
    MeasurableSpace (CanonicalOrientedSetLaw.SlowSet K m) := ⊤

local instance canonicalSlowDiscreteMeasurableSpace (K m : ℕ) :
    DiscreteMeasurableSpace (CanonicalOrientedSetLaw.SlowSet K m) :=
  ⟨fun _ => trivial⟩

/-- The original assignment input: all `K + 1` labelled half-open scalars. -/
abbrev AssignmentVector (p : ConstructorDimensions.Parameters) :=
  Fin (p.K + 1) → ContinuousControlSlice.Scalar

/-- The finite result carrier keeps both local failure sites distinct and
retains the first prefix failure's arm and reason. -/
inductive Result (p : ConstructorDimensions.Parameters) where
  | prefixFailure (arm : Option (Fin p.K))
      (reason : CheckedPrefixSampler.FailureReason)
  | orientationFailure (set : PrefixSetSampler.SetCarrier p.K p.m)
  | sampled (outcome : OrientedAssignmentLaw.AssignmentOutcome p.K p.m)
  deriving DecidableEq, Fintype

local instance resultMeasurableSpace (p : ConstructorDimensions.Parameters) :
    MeasurableSpace (Result p) := ⊤

local instance resultDiscreteMeasurableSpace (p : ConstructorDimensions.Parameters) :
    DiscreteMeasurableSpace (Result p) := ⟨fun _ => trivial⟩

local instance optionSlowMeasurableSpace (K m : ℕ) :
    MeasurableSpace (Option (CanonicalOrientedSetLaw.SlowSet K m)) := ⊤

local instance optionSlowDiscreteMeasurableSpace (K m : ℕ) :
    DiscreteMeasurableSpace (Option (CanonicalOrientedSetLaw.SlowSet K m)) :=
  ⟨fun _ => trivial⟩

local instance prefixResultMeasurableSpace (K m : ℕ) :
    MeasurableSpace (CheckedPrefixSampler.Result K m) := ⊤

local instance prefixResultDiscreteMeasurableSpace (K m : ℕ) :
    DiscreteMeasurableSpace (CheckedPrefixSampler.Result K m) :=
  ⟨fun _ => trivial⟩

/-- Continue from the finite checked-prefix result. This continuation is kept
separate so the two calls and their short-circuit order remain directly
auditable. -/
noncomputable def finishOrientation
    (p : ConstructorDimensions.Parameters)
    (S : PrefixSetSampler.SetCarrier p.K p.m)
    (o : CheckedAssignmentOrientation.Output p.K)
    (hmem : ∀ j, o = .sampled j → j ∈ S.1) : Result p :=
  match o with
  | .failure => .orientationFailure S
  | .sampled j => .sampled ⟨(S, j), hmem j rfl⟩

theorem finishOrientation_eq_failure_iff
    (p : ConstructorDimensions.Parameters)
    (S : PrefixSetSampler.SetCarrier p.K p.m)
    (o : CheckedAssignmentOrientation.Output p.K)
    (hmem : ∀ j, o = .sampled j → j ∈ S.1) :
    finishOrientation p S o hmem = .orientationFailure S ↔ o = .failure := by
  cases o <;> simp [finishOrientation]

theorem finishOrientation_eq_sampled_iff
    (p : ConstructorDimensions.Parameters)
    (S : PrefixSetSampler.SetCarrier p.K p.m)
    (o : CheckedAssignmentOrientation.Output p.K)
    (hmem : ∀ j, o = .sampled j → j ∈ S.1)
    (j : Fin p.K) (hj : j ∈ S.1) :
    finishOrientation p S o hmem = .sampled ⟨(S, j), hj⟩ ↔ o = .sampled j := by
  cases o <;> simp [finishOrientation]

theorem finishOrientation_eq_prefixFailure_iff
    (p : ConstructorDimensions.Parameters)
    (S : PrefixSetSampler.SetCarrier p.K p.m)
    (o : CheckedAssignmentOrientation.Output p.K)
    (hmem : ∀ j, o = .sampled j → j ∈ S.1)
    (arm : Option (Fin p.K)) (reason : CheckedPrefixSampler.FailureReason) :
    finishOrientation p S o hmem = .prefixFailure arm reason ↔ False := by
  cases o <;> simp [finishOrientation]

theorem finishOrientation_eq_orientationFailure_iff
    (p : ConstructorDimensions.Parameters)
    (S' S : PrefixSetSampler.SetCarrier p.K p.m)
    (o : CheckedAssignmentOrientation.Output p.K)
    (hmem : ∀ j, o = .sampled j → j ∈ S'.1) :
    finishOrientation p S' o hmem = .orientationFailure S ↔
      S' = S ∧ o = .failure := by
  cases o <;> simp [finishOrientation]

theorem finishOrientation_eq_sampledOutcome_iff
    (p : ConstructorDimensions.Parameters)
    (S : PrefixSetSampler.SetCarrier p.K p.m)
    (o : CheckedAssignmentOrientation.Output p.K)
    (hmem : ∀ j, o = .sampled j → j ∈ S.1)
    (outcome : OrientedAssignmentLaw.AssignmentOutcome p.K p.m) :
    finishOrientation p S o hmem = .sampled outcome ↔
      S = outcome.1.1 ∧ o = .sampled outcome.1.2 := by
  cases o with
  | failure => simp [finishOrientation]
  | sampled k =>
      rcases outcome with ⟨⟨T, l⟩, hTl⟩
      simp [finishOrientation, Result.sampled.injEq]

noncomputable def finishPrefix
    (p : ConstructorDimensions.Parameters) (anchor : Fin p.K → ℝ)
    (v : AssignmentVector p) : CheckedPrefixSampler.Result p.K p.m → Result p
  | .failed arm reason => .prefixFailure arm reason
  | .sampled S =>
      finishOrientation p S
        (CheckedAssignmentOrientation.checkedOrientation p S anchor (v (Fin.last p.K)))
        (fun j h => CheckedAssignmentOrientation.checkedOrientation_sampled_mem
          p S anchor (v (Fin.last p.K)) j h)

/-- Run the two accepted checked calls on the original vector. The prefix call
receives exactly `prefixValues v`, and the orientation call is evaluated only
after that prefix call returns a supported set. -/
noncomputable def checkedAssignmentSample
    (p : ConstructorDimensions.Parameters)
    (mass : PrefixSetSampler.SetCarrier p.K p.m → ℝ)
    (anchor : Fin p.K → ℝ) (v : AssignmentVector p) : Result p :=
  finishPrefix p anchor v
    (CheckedPrefixSampler.checkedSample mass (PrefixSamplerLaw.prefixValues v))

/-- The public computation equation exposes the two actual calls and their
short-circuit order. -/
theorem checkedAssignmentSample_eq_calls
    (p : ConstructorDimensions.Parameters)
    (mass : PrefixSetSampler.SetCarrier p.K p.m → ℝ)
    (anchor : Fin p.K → ℝ) (v : AssignmentVector p) :
    checkedAssignmentSample p mass anchor v =
      match CheckedPrefixSampler.checkedSample mass (PrefixSamplerLaw.prefixValues v) with
      | .failed arm reason => Result.prefixFailure arm reason
      | .sampled S =>
          finishOrientation p S
            (CheckedAssignmentOrientation.checkedOrientation p S anchor
              (v (Fin.last p.K)))
            (fun j h => CheckedAssignmentOrientation.checkedOrientation_sampled_mem
              p S anchor (v (Fin.last p.K)) j h) := rfl

/-- Exact prefix-failure equation, including the recorded arm and reason. -/
theorem checkedAssignmentSample_prefixFailure
    (p : ConstructorDimensions.Parameters)
    (mass : PrefixSetSampler.SetCarrier p.K p.m → ℝ)
    (anchor : Fin p.K → ℝ) (v : AssignmentVector p)
    (arm : Option (Fin p.K)) (reason : CheckedPrefixSampler.FailureReason)
    (hprefix : CheckedPrefixSampler.checkedSample mass (PrefixSamplerLaw.prefixValues v) =
      .failed arm reason) :
    checkedAssignmentSample p mass anchor v = .prefixFailure arm reason := by
  rw [checkedAssignmentSample_eq_calls, hprefix]

/-- Exact orientation-failure equation, retaining the already sampled set. -/
theorem checkedAssignmentSample_orientationFailure
    (p : ConstructorDimensions.Parameters)
    (mass : PrefixSetSampler.SetCarrier p.K p.m → ℝ)
    (anchor : Fin p.K → ℝ) (v : AssignmentVector p)
    (S : PrefixSetSampler.SetCarrier p.K p.m)
    (hprefix : CheckedPrefixSampler.checkedSample mass (PrefixSamplerLaw.prefixValues v) =
      .sampled S)
    (horientation : CheckedAssignmentOrientation.checkedOrientation p S anchor
      (v (Fin.last p.K)) = .failure) :
    checkedAssignmentSample p mass anchor v = .orientationFailure S := by
  change finishPrefix p anchor v
    (CheckedPrefixSampler.checkedSample mass (PrefixSamplerLaw.prefixValues v)) = _
  calc
    _ = finishPrefix p anchor v (.sampled S) :=
      congrArg (finishPrefix p anchor v) hprefix
    _ = .orientationFailure S := by
      change finishOrientation p S
        (CheckedAssignmentOrientation.checkedOrientation p S anchor (v (Fin.last p.K)))
        (fun j h => CheckedAssignmentOrientation.checkedOrientation_sampled_mem
          p S anchor (v (Fin.last p.K)) j h) = .orientationFailure S
      exact (finishOrientation_eq_failure_iff p S _ _).2 horientation

/-- Exact supported success equation for the two actual checked calls. -/
theorem checkedAssignmentSample_success
    (p : ConstructorDimensions.Parameters)
    (mass : PrefixSetSampler.SetCarrier p.K p.m → ℝ)
    (anchor : Fin p.K → ℝ) (v : AssignmentVector p)
    (S : PrefixSetSampler.SetCarrier p.K p.m) (j : Fin p.K)
    (hprefix : CheckedPrefixSampler.checkedSample mass (PrefixSamplerLaw.prefixValues v) =
      .sampled S)
    (horientation : CheckedAssignmentOrientation.checkedOrientation p S anchor
      (v (Fin.last p.K)) = .sampled j) :
    checkedAssignmentSample p mass anchor v =
      .sampled ⟨(S, j), CheckedAssignmentOrientation.checkedOrientation_sampled_mem
        p S anchor (v (Fin.last p.K)) j horientation⟩ := by
  change finishPrefix p anchor v
    (CheckedPrefixSampler.checkedSample mass (PrefixSamplerLaw.prefixValues v)) = _
  calc
    _ = finishPrefix p anchor v (.sampled S) :=
      congrArg (finishPrefix p anchor v) hprefix
    _ = .sampled ⟨(S, j),
          CheckedAssignmentOrientation.checkedOrientation_sampled_mem
            p S anchor (v (Fin.last p.K)) j horientation⟩ := by
      change finishOrientation p S
        (CheckedAssignmentOrientation.checkedOrientation p S anchor (v (Fin.last p.K)))
        (fun j' h => CheckedAssignmentOrientation.checkedOrientation_sampled_mem
          p S anchor (v (Fin.last p.K)) j' h) = _
      exact (finishOrientation_eq_sampled_iff p S _ _ j _).2 horientation

/-- A slow output exists only on the success arm; failure has no substituted
or default slow set. -/
def successfulSlowSet
    (p : ConstructorDimensions.Parameters) (result : Result p) :
    Option (CanonicalOrientedSetLaw.SlowSet p.K p.m) :=
  match result with
  | .prefixFailure _ _ => none
  | .orientationFailure _ => none
  | .sampled outcome =>
      some (CheckedAssignmentOrientation.slowSetAfter p outcome.1.1 outcome.1.2 outcome.2)

/-- The successful slow carrier is the existing canonical carrier on
`S.erase j`. -/
theorem successfulSlowSet_value
    (p : ConstructorDimensions.Parameters)
    (S : PrefixSetSampler.SetCarrier p.K p.m) (j : Fin p.K) (hj : j ∈ S.1) :
    successfulSlowSet p (.sampled ⟨(S, j), hj⟩) =
      some (CheckedAssignmentOrientation.slowSetAfter p S j hj) := rfl

/-- The underlying successful slow finite set is exactly the sampled set with
the accepted orientation removed. -/
theorem successfulSlowSet_erase
    (p : ConstructorDimensions.Parameters)
    (S : PrefixSetSampler.SetCarrier p.K p.m) (j : Fin p.K) (hj : j ∈ S.1) :
    (CheckedAssignmentOrientation.slowSetAfter p S j hj).1 = S.1.erase j :=
  CheckedAssignmentOrientation.slowSetAfter_val p S j hj

/-- The successful slow set has the source cardinality `m - 1`. -/
theorem successfulSlowSet_card
    (p : ConstructorDimensions.Parameters)
    (S : PrefixSetSampler.SetCarrier p.K p.m) (j : Fin p.K) (hj : j ∈ S.1) :
    (CheckedAssignmentOrientation.slowSetAfter p S j hj).1.card = p.m - 1 :=
  CheckedAssignmentOrientation.slowSetAfter_card p S j hj

/-- The accepted follower arm map is strictly increasing in original arm
labels. -/
theorem successfulSlowSet_followerArm_strictMono
    (p : ConstructorDimensions.Parameters)
    (S : PrefixSetSampler.SetCarrier p.K p.m) (j : Fin p.K) (hj : j ∈ S.1) :
    StrictMono (CanonicalAssignmentVector.followerArm p.two_le_m
      (CheckedAssignmentOrientation.slowSetAfter p S j hj)) :=
  CheckedAssignmentOrientation.slowSetAfter_followerArm_strictMono p S j hj

/-- The accepted increasing enumeration has image exactly `S.erase j`. -/
theorem successfulSlowSet_followerArm_image
    (p : ConstructorDimensions.Parameters)
    (S : PrefixSetSampler.SetCarrier p.K p.m) (j : Fin p.K) (hj : j ∈ S.1) :
    Finset.univ.image (CanonicalAssignmentVector.followerArm p.two_le_m
      (CheckedAssignmentOrientation.slowSetAfter p S j hj)) = S.1.erase j :=
  CheckedAssignmentOrientation.slowSetAfter_followerArm_image p S j hj

/-- The selected fast arm is disjoint from the successful slow set. -/
theorem successfulSlowSet_fast_not_mem
    (p : ConstructorDimensions.Parameters)
    (S : PrefixSetSampler.SetCarrier p.K p.m) (j : Fin p.K) (hj : j ∈ S.1) :
    j ∉ (CheckedAssignmentOrientation.slowSetAfter p S j hj).1 := by
  rw [CheckedAssignmentOrientation.slowSetAfter_val]
  exact Finset.notMem_erase _ _

/-- A normalized accepted mass and globally positive anchor make both checked
calls succeed at every original scalar vector. This is pointwise, including
all CDF endpoints under the existing strict/inclusive branch conventions. -/
theorem checkedAssignmentSample_eq_orientedSampler
    (p : ConstructorDimensions.Parameters)
    (mass : PrefixSetSampler.NormalizedMass p.K p.m (Nat.le_of_lt p.m_lt_K))
    (anchor : Fin p.K → ℝ) (hanchor : ∀ i, 0 < anchor i)
    (v : AssignmentVector p) :
    checkedAssignmentSample p mass.weight anchor v =
      .sampled (OrientedAssignmentLaw.sampler p.two_le_m p.m_lt_K mass anchor hanchor v) := by
  let S := PrefixSetSampler.sample mass (PrefixSamplerLaw.prefixValues v)
  let j := OrientedAssignmentLaw.orientationArm p.two_le_m anchor hanchor S
    (v (Fin.last p.K))
  have hpref : CheckedPrefixSampler.checkedSample mass.weight
      (PrefixSamplerLaw.prefixValues v) =
      .sampled S := CheckedPrefixSampler.checkedSample_eq_sample mass
        (PrefixSamplerLaw.prefixValues v)
  have horientation : CheckedAssignmentOrientation.checkedOrientation p S anchor
      (v (Fin.last p.K)) = .sampled j := by
    dsimp [j]
    exact CheckedAssignmentOrientation.checkedOrientation_eq_orientationArm p S anchor
      (v (Fin.last p.K)) hanchor
  rw [checkedAssignmentSample_success p mass.weight anchor v S j hpref horientation]
  apply congrArg Result.sampled
  apply Subtype.ext
  rfl

/-- Normalized inputs have no prefix or orientation failure outputs. -/
theorem checkedAssignmentSample_normalized_success
    (p : ConstructorDimensions.Parameters)
    (mass : PrefixSetSampler.NormalizedMass p.K p.m (Nat.le_of_lt p.m_lt_K))
    (anchor : Fin p.K → ℝ) (hanchor : ∀ i, 0 < anchor i)
    (v : AssignmentVector p) :
    ∃ outcome, checkedAssignmentSample p mass.weight anchor v = .sampled outcome := by
  exact ⟨OrientedAssignmentLaw.sampler p.two_le_m p.m_lt_K mass anchor hanchor v,
    checkedAssignmentSample_eq_orientedSampler p mass anchor hanchor v⟩

/-- The exact oriented atom law of the checked composition on the complete
`K + 1` coordinate assignment vector. -/
theorem assignmentLaw_checkedAssignmentSample_atom
    (p : ConstructorDimensions.Parameters)
    (mass : PrefixSetSampler.NormalizedMass p.K p.m (Nat.le_of_lt p.m_lt_K))
    (anchor : Fin p.K → ℝ) (hanchor : ∀ i, 0 < anchor i)
    (S : PrefixSetSampler.SetCarrier p.K p.m)
    (j : {j : Fin p.K // j ∈ S.1}) :
    ContinuousControlSlice.assignmentLaw p.K
      {v | checkedAssignmentSample p mass.weight anchor v =
        .sampled ⟨(S, j.1), j.2⟩} =
      ENNReal.ofReal (mass.weight S *
        FiniteOrientationDisintegration.orientationProbability anchor S.1
          (OrientedAssignmentLaw.sampled_set_nonempty p.two_le_m S)
          (fun i _ => hanchor i) j) := by
  have hpre :
      {v : AssignmentVector p | checkedAssignmentSample p mass.weight anchor v =
        .sampled ⟨(S, j.1), j.2⟩} =
      OrientedAssignmentLaw.sampler p.two_le_m p.m_lt_K mass anchor hanchor ⁻¹'
        {⟨(S, j.1), j.2⟩} := by
    ext v
    change checkedAssignmentSample p mass.weight anchor v =
      .sampled ⟨(S, j.1), j.2⟩ ↔
        OrientedAssignmentLaw.sampler p.two_le_m p.m_lt_K mass anchor hanchor v =
          ⟨(S, j.1), j.2⟩
    rw [checkedAssignmentSample_eq_orientedSampler p mass anchor hanchor v]
    simp only [Result.sampled.injEq]
  rw [hpre]
  exact OrientedAssignmentLaw.assignmentLaw_sampler_singleton
    p.two_le_m p.m_lt_K mass anchor hanchor S j

/-- Projection of any supported checked output uses the exact accepted
oriented slow-outcome carrier. -/
theorem successfulSlowSet_sampled_eq_existing
    (p : ConstructorDimensions.Parameters)
    (outcome : OrientedAssignmentLaw.AssignmentOutcome p.K p.m) :
    successfulSlowSet p (.sampled outcome) =
      some (CanonicalAssignmentVector.slowCarrierEquiv p.two_le_m
        (OrientedAssignmentLaw.slowOutcome outcome)) := by
  rcases outcome with ⟨⟨S, j⟩, hj⟩
  exact congrArg some
    (CheckedAssignmentOrientation.slowSetAfter_eq_existingSlowOutcome p S j hj)

/-- The checked slow output refines the existing slow-set projection of the
accepted oriented sampler for every vector. -/
theorem successfulSlowSet_eq_orientedSlowSampler
    (p : ConstructorDimensions.Parameters)
    (mass : PrefixSetSampler.NormalizedMass p.K p.m (Nat.le_of_lt p.m_lt_K))
    (anchor : Fin p.K → ℝ) (hanchor : ∀ i, 0 < anchor i)
    (v : AssignmentVector p) :
    successfulSlowSet p (checkedAssignmentSample p mass.weight anchor v) =
      some (CanonicalAssignmentVector.slowCarrierEquiv p.two_le_m
        (OrientedAssignmentLaw.slowSampler p.two_le_m p.m_lt_K mass anchor hanchor v)) := by
  rw [checkedAssignmentSample_eq_orientedSampler p mass anchor hanchor v]
  exact successfulSlowSet_sampled_eq_existing p
    (OrientedAssignmentLaw.sampler p.two_le_m p.m_lt_K mass anchor hanchor v)

/-- The combined result is jointly Borel measurable in the raw real anchor
vector and the original full assignment vector, for fixed raw mass. -/
theorem measurable_checkedAssignmentSample
    (p : ConstructorDimensions.Parameters)
    (mass : PrefixSetSampler.SetCarrier p.K p.m → ℝ) :
    Measurable (fun z : (Fin p.K → ℝ) × AssignmentVector p =>
      checkedAssignmentSample p mass z.1 z.2) := by
  classical
  let prefixAt : (Fin p.K → ℝ) × AssignmentVector p →
      CheckedPrefixSampler.Result p.K p.m :=
    fun z => CheckedPrefixSampler.checkedSample mass (PrefixSamplerLaw.prefixValues z.2)
  let rawAt : (Fin p.K → ℝ) × AssignmentVector p →
      CheckedAssignmentOrientation.RawInput p :=
    fun z => (z.1, z.2 (Fin.last p.K))
  have hpref : Measurable prefixAt := by
    exact (CheckedPrefixSampler.measurable_checkedSample mass).comp
      ((PrefixSamplerLaw.measurable_prefixValues p.K).comp measurable_snd)
  have hraw : Measurable rawAt := by
    exact measurable_fst.prodMk
      ((measurable_pi_apply (Fin.last p.K)).comp measurable_snd)
  apply measurable_to_countable'
  intro y
  cases y with
  | prefixFailure arm reason =>
      have hpre :
          (fun z : (Fin p.K → ℝ) × AssignmentVector p =>
            checkedAssignmentSample p mass z.1 z.2) ⁻¹'
              {Result.prefixFailure arm reason} =
            prefixAt ⁻¹' {CheckedPrefixSampler.Result.failed arm reason} := by
        ext z
        simp only [Set.mem_preimage, Set.mem_singleton_iff]
        cases hprefix : CheckedPrefixSampler.checkedSample mass
            (PrefixSamplerLaw.prefixValues z.2) with
        | failed arm' reason' =>
            simp [checkedAssignmentSample, finishPrefix, prefixAt, hprefix]
        | sampled S' =>
            simp only [checkedAssignmentSample, finishPrefix, prefixAt, hprefix]
            change finishOrientation p S'
              (CheckedAssignmentOrientation.checkedOrientation p S' z.1
                (z.2 (Fin.last p.K)))
              (fun j h => CheckedAssignmentOrientation.checkedOrientation_sampled_mem
                p S' z.1 (z.2 (Fin.last p.K)) j h) = Result.prefixFailure arm reason ↔
              CheckedPrefixSampler.Result.sampled S' =
                CheckedPrefixSampler.Result.failed arm reason
            have hne := (finishOrientation_eq_prefixFailure_iff p S'
              (CheckedAssignmentOrientation.checkedOrientation p S' z.1
                (z.2 (Fin.last p.K)))
              (fun j h => CheckedAssignmentOrientation.checkedOrientation_sampled_mem
                p S' z.1 (z.2 (Fin.last p.K)) j h) arm reason).mp
            constructor
            · intro h
              exact False.elim (hne h)
            · intro h
              cases h
      rw [hpre]
      exact hpref (measurableSet_singleton _)
  | orientationFailure S =>
      let orientationAt : CheckedAssignmentOrientation.RawInput p →
          CheckedAssignmentOrientation.Output p.K :=
        fun z => CheckedAssignmentOrientation.checkedOrientation p S z.1 z.2
      have horient := (CheckedAssignmentOrientation.measurable_checkedOrientation p S)
        (measurableSet_singleton CheckedAssignmentOrientation.Output.failure)
      have hpre :
          (fun z : (Fin p.K → ℝ) × AssignmentVector p =>
            checkedAssignmentSample p mass z.1 z.2) ⁻¹'
              {Result.orientationFailure S} =
            (prefixAt ⁻¹' {CheckedPrefixSampler.Result.sampled S}) ∩
              (rawAt ⁻¹' (orientationAt ⁻¹'
                {CheckedAssignmentOrientation.Output.failure})) := by
        ext z
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff]
        cases hprefix : CheckedPrefixSampler.checkedSample mass
            (PrefixSamplerLaw.prefixValues z.2) with
        | failed arm reason =>
            simp [checkedAssignmentSample, finishPrefix, prefixAt, rawAt, orientationAt, hprefix]
        | sampled S' =>
            simp only [checkedAssignmentSample, finishPrefix, prefixAt, rawAt, orientationAt,
              hprefix]
            change finishOrientation p S'
              (CheckedAssignmentOrientation.checkedOrientation p S' z.1
                (z.2 (Fin.last p.K)))
              (fun j h => CheckedAssignmentOrientation.checkedOrientation_sampled_mem p S' z.1
                (z.2 (Fin.last p.K)) j h) = Result.orientationFailure S ↔
              (CheckedPrefixSampler.Result.sampled S' = .sampled S) ∧
                CheckedAssignmentOrientation.checkedOrientation p S z.1
                  (z.2 (Fin.last p.K)) = .failure
            have hfinish := finishOrientation_eq_orientationFailure_iff p S' S
              (CheckedAssignmentOrientation.checkedOrientation p S' z.1
                (z.2 (Fin.last p.K)))
              (fun j h => CheckedAssignmentOrientation.checkedOrientation_sampled_mem p S' z.1
                (z.2 (Fin.last p.K)) j h)
            constructor
            · intro heq
              rcases hfinish.mp heq with ⟨hS, horient⟩
              constructor
              · exact congrArg CheckedPrefixSampler.Result.sampled hS
              · subst S'
                exact horient
            · rintro ⟨hpre, horient⟩
              have hS : S' = S := by
                injection hpre with hS
              subst S'
              exact hfinish.mpr ⟨rfl, horient⟩
      rw [hpre]
      exact (hpref (measurableSet_singleton _)).inter (hraw horient)
  | sampled outcome =>
      let S : PrefixSetSampler.SetCarrier p.K p.m := outcome.1.1
      let j : Fin p.K := outcome.1.2
      let orientationAt : CheckedAssignmentOrientation.RawInput p →
          CheckedAssignmentOrientation.Output p.K :=
        fun z => CheckedAssignmentOrientation.checkedOrientation p S z.1 z.2
      have horient := (CheckedAssignmentOrientation.measurable_checkedOrientation p S)
        (measurableSet_singleton (CheckedAssignmentOrientation.Output.sampled j))
      have hpre :
          (fun z : (Fin p.K → ℝ) × AssignmentVector p =>
            checkedAssignmentSample p mass z.1 z.2) ⁻¹' {Result.sampled outcome} =
            (prefixAt ⁻¹' {CheckedPrefixSampler.Result.sampled S}) ∩
              (rawAt ⁻¹' (orientationAt ⁻¹'
                {CheckedAssignmentOrientation.Output.sampled j})) := by
        ext z
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff]
        cases hprefix : CheckedPrefixSampler.checkedSample mass
            (PrefixSamplerLaw.prefixValues z.2) with
        | failed arm reason =>
            simp [checkedAssignmentSample, finishPrefix, prefixAt, rawAt, orientationAt, hprefix]
        | sampled S' =>
            simp only [checkedAssignmentSample, finishPrefix, prefixAt, rawAt, orientationAt,
              hprefix]
            change finishOrientation p S'
              (CheckedAssignmentOrientation.checkedOrientation p S' z.1
                (z.2 (Fin.last p.K)))
              (fun j' h => CheckedAssignmentOrientation.checkedOrientation_sampled_mem p S' z.1
                (z.2 (Fin.last p.K)) j' h) = .sampled outcome ↔
              (CheckedPrefixSampler.Result.sampled S' = .sampled S) ∧
                CheckedAssignmentOrientation.checkedOrientation p S z.1
                  (z.2 (Fin.last p.K)) = .sampled j
            have hfinish := finishOrientation_eq_sampledOutcome_iff p S'
              (CheckedAssignmentOrientation.checkedOrientation p S' z.1
                (z.2 (Fin.last p.K)))
              (fun j' h => CheckedAssignmentOrientation.checkedOrientation_sampled_mem p S' z.1
                (z.2 (Fin.last p.K)) j' h) outcome
            constructor
            · intro heq
              rcases hfinish.mp heq with ⟨hS, horient⟩
              constructor
              · exact congrArg CheckedPrefixSampler.Result.sampled hS
              · subst S'
                exact horient
            · rintro ⟨hpre, horient⟩
              have hS : S' = S := by
                injection hpre with hS
              subst S'
              exact hfinish.mpr ⟨rfl, horient⟩
      rw [hpre]
      exact (hpref (measurableSet_singleton _)).inter (hraw horient)

/-- The successful slow projection is measurable without assigning any slow
set to either failure arm. -/
theorem measurable_successfulSlowSet
    (p : ConstructorDimensions.Parameters)
    (mass : PrefixSetSampler.SetCarrier p.K p.m → ℝ) :
    Measurable (fun z : (Fin p.K → ℝ) × AssignmentVector p =>
      successfulSlowSet p (checkedAssignmentSample p mass z.1 z.2)) := by
  have hmap : Measurable (fun r : Result p => successfulSlowSet p r) :=
    Measurable.of_discrete
  exact hmap.comp (measurable_checkedAssignmentSample p mass)

/-- The actual product-weight specialization retains every supplied
weight-positivity hypothesis. -/
theorem productQ_checkedAssignmentSample_eq_sampler
    (p : ConstructorDimensions.Parameters)
    (w anchor : Fin p.K → ℝ) (hw : ∀ i, 0 < w i)
    (hanchor : ∀ i, 0 < anchor i) (v : AssignmentVector p) :
    checkedAssignmentSample p
        (CanonicalAssignmentVector.productQNormalizedMass p.two_le_m p.m_lt_K w hw).weight
        anchor v =
      .sampled (CanonicalAssignmentVector.sampler p.two_le_m p.m_lt_K w anchor hw hanchor v) := by
  rw [checkedAssignmentSample_eq_orientedSampler]
  rfl

/-- The successful product-weight slow output is exactly the accepted
canonical slow sampler's output. -/
theorem productQ_successfulSlowSet_eq_canonical
    (p : ConstructorDimensions.Parameters)
    (w anchor : Fin p.K → ℝ) (hw : ∀ i, 0 < w i)
    (hanchor : ∀ i, 0 < anchor i) (v : AssignmentVector p) :
    successfulSlowSet p (checkedAssignmentSample p
      (CanonicalAssignmentVector.productQNormalizedMass p.two_le_m p.m_lt_K w hw).weight
      anchor v) =
      some (CanonicalAssignmentVector.canonicalSlowSampler p.two_le_m p.m_lt_K
        w anchor hw hanchor v) := by
  rw [successfulSlowSet_eq_orientedSlowSampler, CanonicalAssignmentVector.canonicalSlowSampler]

/-- The product-weight checked slow output has the accepted canonical slow-set
pushforward, embedded into `Option` only on the success arm. -/
theorem productQ_checkedSlow_pushforward
    (p : ConstructorDimensions.Parameters)
    (w anchor : Fin p.K → ℝ) (hw : ∀ i, 0 < w i)
    (hanchor : ∀ i, 0 < anchor i) :
    (ContinuousControlSlice.assignmentLaw p.K).map
        (fun x => successfulSlowSet p (checkedAssignmentSample p
          (CanonicalAssignmentVector.productQNormalizedMass p.two_le_m p.m_lt_K w hw).weight
          anchor x)) =
      Measure.map some (PMF.toMeasure
        (CanonicalOrientedSetLaw.slowSetPMF w anchor p.two_le_m p.m_lt_K hw hanchor)) := by
  calc
    _ = (ContinuousControlSlice.assignmentLaw p.K).map
        (fun x => some (CanonicalAssignmentVector.canonicalSlowSampler p.two_le_m p.m_lt_K
          w anchor hw hanchor x)) := by
      congr 1
      funext x
      exact productQ_successfulSlowSet_eq_canonical p w anchor hw hanchor x
    _ = ((ContinuousControlSlice.assignmentLaw p.K).map
        (CanonicalAssignmentVector.canonicalSlowSampler p.two_le_m p.m_lt_K
          w anchor hw hanchor)).map some := by
      rw [Measure.map_map (Measurable.of_discrete)
        (CanonicalAssignmentVector.measurable_canonicalSlowSampler p.two_le_m p.m_lt_K
          w anchor hw hanchor)]
      rfl
    _ = Measure.map some (PMF.toMeasure
        (CanonicalOrientedSetLaw.slowSetPMF w anchor p.two_le_m p.m_lt_K hw hanchor)) := by
      rw [CanonicalAssignmentVector.assignmentLaw_map_canonicalSlowSampler]

/-- Every successful product-weight checked fibre is exactly the accepted
canonical slow-sampler fibre. -/
theorem productQ_checkedSlow_fibre_eq
    (p : ConstructorDimensions.Parameters)
    (w anchor : Fin p.K → ℝ) (hw : ∀ i, 0 < w i)
    (hanchor : ∀ i, 0 < anchor i) (U : CanonicalOrientedSetLaw.SlowSet p.K p.m) :
    FiniteFibreLift.fibre
        (successfulSlowSet p ∘ checkedAssignmentSample p
          (CanonicalAssignmentVector.productQNormalizedMass p.two_le_m p.m_lt_K w hw).weight
          anchor) (some U) =
      CanonicalAssignmentVector.canonicalSlowSampler p.two_le_m p.m_lt_K
        w anchor hw hanchor ⁻¹' {U} := by
  ext v
  change successfulSlowSet p (checkedAssignmentSample p
      (CanonicalAssignmentVector.productQNormalizedMass p.two_le_m p.m_lt_K w hw).weight
      anchor v) = some U ↔
    CanonicalAssignmentVector.canonicalSlowSampler p.two_le_m p.m_lt_K
      w anchor hw hanchor v = U
  rw [productQ_successfulSlowSet_eq_canonical p w anchor hw hanchor v]
  simp

/-- Product-weight checked fibres inherit the accepted full-vector
normalized restriction, not a coordinatewise substitute. -/
theorem productQ_checkedSlow_fibreMeasure_eq
    (p : ConstructorDimensions.Parameters)
    (w anchor : Fin p.K → ℝ) (hw : ∀ i, 0 < w i)
    (hanchor : ∀ i, 0 < anchor i) (U : CanonicalOrientedSetLaw.SlowSet p.K p.m) :
    FiniteFibreLift.fibreMeasure (ContinuousControlSlice.assignmentLaw p.K)
        (successfulSlowSet p ∘ checkedAssignmentSample p
          (CanonicalAssignmentVector.productQNormalizedMass p.two_le_m p.m_lt_K w hw).weight
          anchor) (some U) =
      FiniteFibreLift.fibreMeasure (ContinuousControlSlice.assignmentLaw p.K)
        (CanonicalAssignmentVector.canonicalSlowSampler p.two_le_m p.m_lt_K
          w anchor hw hanchor) U := by
  have hset := productQ_checkedSlow_fibre_eq p w anchor hw hanchor U
  have hset' :
      FiniteFibreLift.fibre
          (successfulSlowSet p ∘ checkedAssignmentSample p
            (CanonicalAssignmentVector.productQNormalizedMass p.two_le_m p.m_lt_K w hw).weight
            anchor) (some U) =
        FiniteFibreLift.fibre
          (CanonicalAssignmentVector.canonicalSlowSampler p.two_le_m p.m_lt_K
            w anchor hw hanchor) U := by
    simpa [FiniteFibreLift.fibre] using hset
  have hmass :
      FiniteFibreLift.fibreMass (ContinuousControlSlice.assignmentLaw p.K)
          (successfulSlowSet p ∘ checkedAssignmentSample p
            (CanonicalAssignmentVector.productQNormalizedMass p.two_le_m p.m_lt_K w hw).weight
            anchor) (some U) =
        FiniteFibreLift.fibreMass (ContinuousControlSlice.assignmentLaw p.K)
          (CanonicalAssignmentVector.canonicalSlowSampler p.two_le_m p.m_lt_K
            w anchor hw hanchor) U := by
    unfold FiniteFibreLift.fibreMass
    rw [hset']
  simp only [FiniteFibreLift.fibreMeasure, hmass, hset']

/-- The Option-valued checked slow output has the original full-vector law as
its fibre mixture. The `none` outcome is the actual failure event and is not
replaced by a default slow set. -/
theorem checkedSlow_fibre_mixture
    (p : ConstructorDimensions.Parameters)
    (mass : PrefixSetSampler.NormalizedMass p.K p.m (Nat.le_of_lt p.m_lt_K))
    (anchor : Fin p.K → ℝ) (_hanchor : ∀ i, 0 < anchor i) :
    (∑ U : Option (CanonicalOrientedSetLaw.SlowSet p.K p.m),
      FiniteFibreLift.fibreMass (ContinuousControlSlice.assignmentLaw p.K)
        (successfulSlowSet p ∘ checkedAssignmentSample p mass.weight anchor) U •
      FiniteFibreLift.fibreMeasure (ContinuousControlSlice.assignmentLaw p.K)
        (successfulSlowSet p ∘ checkedAssignmentSample p mass.weight anchor) U) =
      ContinuousControlSlice.assignmentLaw p.K := by
  exact FiniteFibreLift.sum_fibreMass_smul_fibreMeasure
    (μ := ContinuousControlSlice.assignmentLaw p.K)
    (F := successfulSlowSet p ∘ checkedAssignmentSample p mass.weight anchor)
    (by
      exact (measurable_successfulSlowSet p mass.weight).comp
        (measurable_const.prodMk measurable_id))

/-- The corrected recorded-window specialization is the same checked
composition with the actual corrected mass. The cap, concrete queue path,
window indices, and their validity premises remain explicit. -/
theorem actualCorrected_checkedAssignmentSample_eq_sampler
    (p : ConstructorDimensions.Parameters) (q : RecordedQueueRun.Parameters)
    (hcap : q.eta ≤ 1 /
      (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (CanonicalRecordingRates.L_stab p : ℝ)))
    (rounds : List (RecordedQueueRun.RoundInput p.K)) (u v : ℕ)
    (hu : 1 ≤ u) (huv : u ≤ v) (hv : v ≤ rounds.length)
    (anchor : Fin p.K → ℝ) (hanchor : ∀ i, 0 < anchor i)
    (x : AssignmentVector p) :
    checkedAssignmentSample p
        (RecordedCorrectedWindow.actualPrefixSamplerMass p q hcap rounds u v hu huv hv).weight
        anchor x =
      .sampled (CorrectedAssignmentVector.correctedSampler p q hcap rounds u v hu huv hv
        anchor hanchor x) := by
  rw [checkedAssignmentSample_eq_orientedSampler]
  rfl

/-- The successful corrected slow output is exactly the existing corrected
slow sampler, with the supplied logical path and window hypotheses intact. -/
theorem actualCorrected_successfulSlowSet_eq_sampler
    (p : ConstructorDimensions.Parameters) (q : RecordedQueueRun.Parameters)
    (hcap : q.eta ≤ 1 /
      (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (CanonicalRecordingRates.L_stab p : ℝ)))
    (rounds : List (RecordedQueueRun.RoundInput p.K)) (u v : ℕ)
    (hu : 1 ≤ u) (huv : u ≤ v) (hv : v ≤ rounds.length)
    (anchor : Fin p.K → ℝ) (hanchor : ∀ i, 0 < anchor i)
    (x : AssignmentVector p) :
    successfulSlowSet p (checkedAssignmentSample p
      (RecordedCorrectedWindow.actualPrefixSamplerMass p q hcap rounds u v hu huv hv).weight
      anchor x) =
      some (CorrectedAssignmentVector.correctedSlowSampler p q hcap rounds u v hu huv hv
        anchor hanchor x) := by
  rw [successfulSlowSet_eq_orientedSlowSampler,
    CorrectedAssignmentVector.correctedSlowSampler]

/-- Each successful corrected checked fibre is exactly the existing
corrected full-vector fibre, including when its corrected mass is zero. -/
theorem actualCorrected_checkedSlow_fibre_eq
    (p : ConstructorDimensions.Parameters) (q : RecordedQueueRun.Parameters)
    (hcap : q.eta ≤ 1 /
      (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (CanonicalRecordingRates.L_stab p : ℝ)))
    (rounds : List (RecordedQueueRun.RoundInput p.K)) (u v : ℕ)
    (hu : 1 ≤ u) (huv : u ≤ v) (hv : v ≤ rounds.length)
    (anchor : Fin p.K → ℝ) (hanchor : ∀ i, 0 < anchor i)
    (U : CanonicalOrientedSetLaw.SlowSet p.K p.m) :
    FiniteFibreLift.fibre
        (successfulSlowSet p ∘ checkedAssignmentSample p
          (RecordedCorrectedWindow.actualPrefixSamplerMass p q hcap rounds u v hu huv hv).weight
          anchor) (some U) =
      CorrectedAssignmentVector.correctedSlowSampler p q hcap rounds u v hu huv hv
        anchor hanchor ⁻¹' {U} := by
  ext x
  change successfulSlowSet p (checkedAssignmentSample p
      (RecordedCorrectedWindow.actualPrefixSamplerMass p q hcap rounds u v hu huv hv).weight
      anchor x) = some U ↔
    CorrectedAssignmentVector.correctedSlowSampler p q hcap rounds u v hu huv hv
      anchor hanchor x = U
  rw [actualCorrected_successfulSlowSet_eq_sampler p q hcap rounds u v hu huv hv
    anchor hanchor x]
  simp

/-- The corrected checked fibre uses the same normalized restriction as the
accepted lift, with the accepted original-law convention on null fibres. -/
theorem actualCorrected_checkedSlow_fibreMeasure_eq
    (p : ConstructorDimensions.Parameters) (q : RecordedQueueRun.Parameters)
    (hcap : q.eta ≤ 1 /
      (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (CanonicalRecordingRates.L_stab p : ℝ)))
    (rounds : List (RecordedQueueRun.RoundInput p.K)) (u v : ℕ)
    (hu : 1 ≤ u) (huv : u ≤ v) (hv : v ≤ rounds.length)
    (anchor : Fin p.K → ℝ) (hanchor : ∀ i, 0 < anchor i)
    (U : CanonicalOrientedSetLaw.SlowSet p.K p.m) :
    FiniteFibreLift.fibreMeasure (ContinuousControlSlice.assignmentLaw p.K)
        (successfulSlowSet p ∘ checkedAssignmentSample p
          (RecordedCorrectedWindow.actualPrefixSamplerMass p q hcap rounds u v hu huv hv).weight
          anchor) (some U) =
      FiniteFibreLift.fibreMeasure (ContinuousControlSlice.assignmentLaw p.K)
        (CorrectedAssignmentVector.correctedSlowSampler p q hcap rounds u v hu huv hv
          anchor hanchor) U := by
  have hset := actualCorrected_checkedSlow_fibre_eq p q hcap rounds u v hu huv hv
    anchor hanchor U
  have hset' :
      FiniteFibreLift.fibre
          (successfulSlowSet p ∘ checkedAssignmentSample p
            (RecordedCorrectedWindow.actualPrefixSamplerMass p q hcap rounds u v hu huv hv).weight
            anchor) (some U) =
        FiniteFibreLift.fibre
          (CorrectedAssignmentVector.correctedSlowSampler p q hcap rounds u v hu huv hv
            anchor hanchor) U := by
    simpa [FiniteFibreLift.fibre] using hset
  have hmass :
      FiniteFibreLift.fibreMass (ContinuousControlSlice.assignmentLaw p.K)
          (successfulSlowSet p ∘ checkedAssignmentSample p
            (RecordedCorrectedWindow.actualPrefixSamplerMass p q hcap rounds u v hu huv hv).weight
            anchor) (some U) =
        FiniteFibreLift.fibreMass (ContinuousControlSlice.assignmentLaw p.K)
          (CorrectedAssignmentVector.correctedSlowSampler p q hcap rounds u v hu huv hv
            anchor hanchor) U := by
    unfold FiniteFibreLift.fibreMass
    rw [hset']
  simp only [FiniteFibreLift.fibreMeasure, hmass, hset']

/-- The actual corrected checked slow fibre mass is the accepted corrected
slow-set pushforward atom. This preserves zero-mass fibres verbatim. -/
theorem actualCorrected_checkedSlow_fibreMass
    (p : ConstructorDimensions.Parameters) (q : RecordedQueueRun.Parameters)
    (hcap : q.eta ≤ 1 /
      (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (CanonicalRecordingRates.L_stab p : ℝ)))
    (rounds : List (RecordedQueueRun.RoundInput p.K)) (u v : ℕ)
    (hu : 1 ≤ u) (huv : u ≤ v) (hv : v ≤ rounds.length)
    (anchor : Fin p.K → ℝ) (hanchor : ∀ i, 0 < anchor i)
    (U : CanonicalOrientedSetLaw.SlowSet p.K p.m) :
    FiniteFibreLift.fibreMass (ContinuousControlSlice.assignmentLaw p.K)
        (successfulSlowSet p ∘ checkedAssignmentSample p
          (RecordedCorrectedWindow.actualPrefixSamplerMass p q hcap rounds u v hu huv hv).weight
          anchor) (some U) =
      ENNReal.ofReal (CorrectedAssignmentVector.slowFibreMass p q hcap rounds u v hu huv hv
        anchor hanchor U) := by
  calc
    _ = FiniteFibreLift.fibreMass (ContinuousControlSlice.assignmentLaw p.K)
        (CorrectedAssignmentVector.correctedSlowSampler p q hcap rounds u v hu huv hv
          anchor hanchor) U := by
      unfold FiniteFibreLift.fibreMass
      rw [actualCorrected_checkedSlow_fibre_eq p q hcap rounds u v hu huv hv
        anchor hanchor U]
      rfl
    _ = _ := CorrectedAssignmentVector.correctedSlowSampler_fibreMass p q hcap rounds u v
      hu huv hv anchor hanchor U

/-- The actual corrected checked slow output has the corrected slow-set law
as its pushforward. The concrete cap, queue path, and window assumptions are
all retained in the statement. -/
theorem actualCorrected_checkedSlow_pushforward
    (p : ConstructorDimensions.Parameters) (q : RecordedQueueRun.Parameters)
    (hcap : q.eta ≤ 1 /
      (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (CanonicalRecordingRates.L_stab p : ℝ)))
    (rounds : List (RecordedQueueRun.RoundInput p.K)) (u v : ℕ)
    (hu : 1 ≤ u) (huv : u ≤ v) (hv : v ≤ rounds.length)
    (anchor : Fin p.K → ℝ) (hanchor : ∀ i, 0 < anchor i) :
    (ContinuousControlSlice.assignmentLaw p.K).map
        (fun x => successfulSlowSet p (checkedAssignmentSample p
          (RecordedCorrectedWindow.actualPrefixSamplerMass p q hcap rounds u v hu huv hv).weight
          anchor x)) =
      Measure.map some (PMF.toMeasure
        (PMF.ofFintype
          (fun U : CanonicalOrientedSetLaw.SlowSet p.K p.m =>
            ENNReal.ofReal (CorrectedAssignmentVector.slowFibreMass p q hcap rounds u v
              hu huv hv anchor hanchor U))
          (by
            rw [← ENNReal.ofReal_sum_of_nonneg (s := Finset.univ)]
            · rw [CorrectedAssignmentVector.slowFibreMass_sum_eq_one
                p q hcap rounds u v hu huv hv anchor hanchor]
              simp
            · intro U _hU
              exact CorrectedAssignmentVector.slowFibreMass_nonneg
                p q hcap rounds u v hu huv hv anchor hanchor U))) := by
  let ν : PMF (CanonicalOrientedSetLaw.SlowSet p.K p.m) :=
    PMF.ofFintype
      (fun U => ENNReal.ofReal (CorrectedAssignmentVector.slowFibreMass p q hcap rounds u v
        hu huv hv anchor hanchor U))
      (by
        rw [← ENNReal.ofReal_sum_of_nonneg (s := Finset.univ)]
        · rw [CorrectedAssignmentVector.slowFibreMass_sum_eq_one
            p q hcap rounds u v hu huv hv anchor hanchor]
          simp
        · intro U _hU
          exact CorrectedAssignmentVector.slowFibreMass_nonneg
            p q hcap rounds u v hu huv hv anchor hanchor U)
  have hcorrectedMap :
      (ContinuousControlSlice.assignmentLaw p.K).map
          (CorrectedAssignmentVector.correctedSlowSampler p q hcap rounds u v
            hu huv hv anchor hanchor) = PMF.toMeasure ν := by
    apply Measure.ext_of_singleton
    intro U
    rw [Measure.map_apply
      (CorrectedAssignmentVector.correctedSlowSampler_measurable p q hcap rounds u v
        hu huv hv anchor hanchor) (measurableSet_singleton U)]
    change FiniteFibreLift.fibreMass (ContinuousControlSlice.assignmentLaw p.K)
        (CorrectedAssignmentVector.correctedSlowSampler p q hcap rounds u v
          hu huv hv anchor hanchor) U = PMF.toMeasure ν {U}
    rw [CorrectedAssignmentVector.correctedSlowSampler_fibreMass p q hcap rounds u v
      hu huv hv anchor hanchor U,
      PMF.toMeasure_apply_singleton ν U (measurableSet_singleton U)]
    rfl
  calc
    _ = (ContinuousControlSlice.assignmentLaw p.K).map
        (fun x => some (CorrectedAssignmentVector.correctedSlowSampler p q hcap rounds u v
          hu huv hv anchor hanchor x)) := by
      congr 1
      funext x
      exact actualCorrected_successfulSlowSet_eq_sampler p q hcap rounds u v hu huv hv
        anchor hanchor x
    _ = ((ContinuousControlSlice.assignmentLaw p.K).map
        (CorrectedAssignmentVector.correctedSlowSampler p q hcap rounds u v
          hu huv hv anchor hanchor)).map some := by
      rw [Measure.map_map (Measurable.of_discrete)
        (CorrectedAssignmentVector.correctedSlowSampler_measurable p q hcap rounds u v
          hu huv hv anchor hanchor)]
      rfl
    _ = Measure.map some (PMF.toMeasure ν) := by rw [hcorrectedMap]

/-- The mixture of all corrected checked slow fibres, including the failure
fibre and every zero-mass corrected fibre, recovers the entire assignment
vector law. -/
theorem actualCorrected_checkedSlow_fibre_mixture
    (p : ConstructorDimensions.Parameters) (q : RecordedQueueRun.Parameters)
    (hcap : q.eta ≤ 1 /
      (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (CanonicalRecordingRates.L_stab p : ℝ)))
    (rounds : List (RecordedQueueRun.RoundInput p.K)) (u v : ℕ)
    (hu : 1 ≤ u) (huv : u ≤ v) (hv : v ≤ rounds.length)
    (anchor : Fin p.K → ℝ) (_hanchor : ∀ i, 0 < anchor i) :
    (∑ U : Option (CanonicalOrientedSetLaw.SlowSet p.K p.m),
      FiniteFibreLift.fibreMass (ContinuousControlSlice.assignmentLaw p.K)
        (successfulSlowSet p ∘ checkedAssignmentSample p
          (RecordedCorrectedWindow.actualPrefixSamplerMass p q hcap rounds u v hu huv hv).weight
          anchor) U •
      FiniteFibreLift.fibreMeasure (ContinuousControlSlice.assignmentLaw p.K)
        (successfulSlowSet p ∘ checkedAssignmentSample p
          (RecordedCorrectedWindow.actualPrefixSamplerMass p q hcap rounds u v hu huv hv).weight
          anchor) U) = ContinuousControlSlice.assignmentLaw p.K := by
  exact FiniteFibreLift.sum_fibreMass_smul_fibreMeasure
    (μ := ContinuousControlSlice.assignmentLaw p.K)
    (F := successfulSlowSet p ∘ checkedAssignmentSample p
      (RecordedCorrectedWindow.actualPrefixSamplerMass p q hcap rounds u v hu huv hv).weight
      anchor)
    (by
      have hfix : Measurable
          (fun x : AssignmentVector p =>
            (anchor, x) : AssignmentVector p →
              (Fin p.K → ℝ) × AssignmentVector p) :=
        measurable_const.prodMk measurable_id
      have hjoint := measurable_successfulSlowSet p
        (RecordedCorrectedWindow.actualPrefixSamplerMass p q hcap rounds u v hu huv hv).weight
      exact hjoint.comp hfix)

end Bandits.Support.CheckedAssignmentSample

end
