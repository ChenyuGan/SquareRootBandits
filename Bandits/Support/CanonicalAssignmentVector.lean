/-
Copyright (c) 2026 The Bandits Lean regret formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.OrientedAssignmentLaw
public import Bandits.Support.CanonicalOrientedSetLaw
public import Bandits.Support.ProductSetDistribution
import Mathlib.MeasureTheory.Measure.Dirac.Basic

/-!
# Canonical product-weight assignment sampler

This module instantiates the accepted entire-vector oriented assignment
sampler with the actual product-weight law `Q`, identifies the canonical
slow-set pushforward, and exposes the resulting full-vector fibre mixture.

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:7-37`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:66-77`,
`sources/zip4/manuscript/appendix_b_communication.tex:25-44`, and
`sources/zip4/manuscript/06_interruptions.tex:410-423`.

These are fully proved internal results. They do not formalize the corrected
finite-window law, physical-history measurability, or assignment coupling.
-/

public section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Bandits.Support.CanonicalAssignmentVector

open Bandits.Support
open Bandits.Support.OrientedAssignmentLaw
open Bandits.Support.CanonicalOrientedSetLaw
open Bandits.Support.ProductSetLaw

local instance orientedSlowMeasurableSpace (K m : ℕ) :
    MeasurableSpace (OrientedAssignmentLaw.SlowSetCarrier K m) := ⊤

local instance orientedSlowDiscreteMeasurableSpace (K m : ℕ) :
    DiscreteMeasurableSpace (OrientedAssignmentLaw.SlowSetCarrier K m) :=
  ⟨fun _ => trivial⟩

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

/-- The actual product-weight law as the normalized mass consumed by the
accepted prefix sampler.

Source: `sources/zip4/manuscript/04_slow_fast_learner.tex:7-13`. -/
@[expose] noncomputable def productQNormalizedMass {K m : ℕ}
    (hm : 2 ≤ m) (hmK : m < K) (w : Fin K → ℝ)
    (hw : ∀ i, 0 < w i) :
    PrefixSetSampler.NormalizedMass K m (Nat.le_of_lt hmK) where
  weight := fun S => ProductSetLaw.Q m w S
  weight_nonneg := fun S => (ProductSetLaw.Q_pos w (by omega) hmK hw S).le
  weight_sum_eq_one := by
    change (∑ S : ProductSetLaw.ProductSet K m, ProductSetLaw.Q m w S) = 1
    exact ProductSetLaw.Q_sum_eq_one w (by omega) hmK hw

/-- Convert the oriented sampler's equation-form slow carrier to the existing
supported `(m - 1)`-set carrier. The underlying finite set is unchanged. -/
@[expose] def slowCarrierEquiv {K m : ℕ} (hm : 2 ≤ m) :
    OrientedAssignmentLaw.SlowSetCarrier K m ≃
      CanonicalOrientedSetLaw.SlowSet K m where
  toFun U := ⟨U.1, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, by
    have h := U.2
    omega⟩⟩
  invFun U := ⟨U.1, by
    have h := (Finset.mem_powersetCard.mp U.2).2
    omega⟩
  left_inv U := by
    apply Subtype.ext
    rfl
  right_inv U := by
    apply Subtype.ext
    rfl

@[simp] theorem slowCarrierEquiv_val {K m : ℕ} (hm : 2 ≤ m)
    (U : OrientedAssignmentLaw.SlowSetCarrier K m) :
    (slowCarrierEquiv hm U).1 = U.1 := rfl

@[simp] theorem slowCarrierEquiv_symm_val {K m : ℕ} (hm : 2 ≤ m)
    (U : CanonicalOrientedSetLaw.SlowSet K m) :
    ((slowCarrierEquiv hm).symm U).1 = U.1 := rfl

/-- The cardinality used to enumerate a supported canonical slow set. -/
theorem slowSet_card_eq_sub_one {K m : ℕ} (hm : 2 ≤ m)
    (U : CanonicalOrientedSetLaw.SlowSet K m) : U.1.card = m - 1 := by
  have h := CanonicalOrientedSetLaw.slowSet_card hm U
  omega

/-- The sorted follower arm at rank `r`, using the order isomorphism of the
canonical slow set. -/
@[expose] def followerArm {K m : ℕ} (hm : 2 ≤ m)
    (U : CanonicalOrientedSetLaw.SlowSet K m) (r : Fin (m - 1)) : Fin K :=
  ((U.1.orderIsoOfFin (slowSet_card_eq_sub_one hm U)) r).1

/-- The sorted follower arm map is injective. -/
theorem followerArm_injective {K m : ℕ} (hm : 2 ≤ m)
    (U : CanonicalOrientedSetLaw.SlowSet K m) :
    Function.Injective (followerArm hm U) := by
  let e := U.1.orderIsoOfFin (slowSet_card_eq_sub_one hm U)
  intro r s hrs
  apply e.injective
  exact Subtype.ext hrs

/-- The sorted follower arm map is strictly increasing in arm-label order. -/
theorem followerArm_strictMono {K m : ℕ} (hm : 2 ≤ m)
    (U : CanonicalOrientedSetLaw.SlowSet K m) : StrictMono (followerArm hm U) := by
  let e := U.1.orderIsoOfFin (slowSet_card_eq_sub_one hm U)
  intro r s hrs
  exact e.strictMono hrs

/-- The sorted follower arm map has image exactly the canonical slow set. -/
theorem followerArm_image {K m : ℕ} (hm : 2 ≤ m)
    (U : CanonicalOrientedSetLaw.SlowSet K m) :
    Finset.univ.image (followerArm hm U) = U.1 := by
  let e := U.1.orderIsoOfFin (slowSet_card_eq_sub_one hm U)
  change Finset.univ.image (fun r => (e r).1) = U.1
  ext i
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨r, hr⟩
    rw [← hr]
    exact (e r).2
  · intro hi
    let r := e.symm ⟨i, hi⟩
    exact ⟨r, congrArg Subtype.val (e.apply_symm_apply ⟨i, hi⟩)⟩

/-- No sorted follower arm is the fast arm, which lies in the complement of
the canonical slow set. -/
theorem followerArm_ne_of_fastCandidate {K m : ℕ} (hm : 2 ≤ m)
    (U : CanonicalOrientedSetLaw.SlowSet K m)
    (j : {j : Fin K // j ∈ Finset.univ \ U.1}) (r : Fin (m - 1)) :
    followerArm hm U r ≠ j.1 := by
  intro h
  have hr : followerArm hm U r ∈ Finset.univ.image (followerArm hm U) :=
    Finset.mem_image.mpr ⟨r, Finset.mem_univ _, rfl⟩
  rw [followerArm_image hm U, h] at hr
  exact (Finset.mem_sdiff.mp j.2).2 hr

/-- The accepted assignment sampler with the literal `Q_w` product law and
fixed positive anchor, retaining all `K+1` scalar coordinates. -/
@[expose] noncomputable def sampler {K m : ℕ} (hm : 2 ≤ m) (hmK : m < K)
    (w anchor : Fin K → ℝ) (hw : ∀ i, 0 < w i)
    (hanchor : ∀ i, 0 < anchor i) :
    (Fin (K + 1) → ContinuousControlSlice.Scalar) →
      OrientedAssignmentLaw.AssignmentOutcome K m :=
  OrientedAssignmentLaw.sampler hm hmK
    (productQNormalizedMass hm hmK w hw) anchor hanchor

/-- The full-vector oriented atom law factors as the canonical slow marginal
times the existing fixed-anchor conditional fast-arm law, evaluated at the
actual `insertedOutcome(U,j)`.

Source: `sources/zip4/manuscript/04_slow_fast_learner.tex:16-37`. -/
theorem assignmentLaw_insertedOutcome {K m : ℕ} (hm : 2 ≤ m) (hmK : m < K)
    (w anchor : Fin K → ℝ) (hw : ∀ i, 0 < w i)
    (hanchor : ∀ i, 0 < anchor i)
    (U : OrientedAssignmentLaw.SlowSetCarrier K m)
    (j : {j : Fin K // j ∈ Finset.univ \ U.1}) :
    ContinuousControlSlice.assignmentLaw K
      (sampler hm hmK w anchor hw hanchor ⁻¹'
        {OrientedAssignmentLaw.insertedOutcome U j}) =
      ENNReal.ofReal
        (CanonicalOrientedSetLaw.slowMarginal w anchor hm hmK hw hanchor
            (slowCarrierEquiv hm U) *
          CanonicalOrientedSetLaw.fastArmConditionalMass w anchor hm hmK
            hw hanchor (slowCarrierEquiv hm U)
            ⟨j.1, by simp⟩) := by
  let Uc := slowCarrierEquiv hm U
  let jc : {j : Fin K // j ∈ Finset.univ \ Uc.1} := ⟨j.1, by
    simp [Uc]⟩
  have hatom := OrientedAssignmentLaw.assignmentLaw_sampler_singleton
    hm hmK (productQNormalizedMass hm hmK w hw) anchor hanchor
    (OrientedAssignmentLaw.insertedSet U j) ⟨j.1, Finset.mem_insert_self _ _⟩
  have hjoint :
      ContinuousControlSlice.assignmentLaw K
        (sampler hm hmK w anchor hw hanchor ⁻¹'
          {OrientedAssignmentLaw.insertedOutcome U j}) =
        ENNReal.ofReal
          (FiniteOrientationDisintegration.orientedJointMass
            (Finset.univ : Finset (Fin K)) m w anchor Uc.1
            (Finset.subset_univ _) (CanonicalOrientedSetLaw.slowSet_card hm Uc)
            (fun i _ => hw i) (fun i _ => hanchor i) jc) := by
    rw [show OrientedAssignmentLaw.insertedOutcome U j =
        ⟨(OrientedAssignmentLaw.insertedSet U j, j.1),
          Finset.mem_insert_self _ _⟩ by
            apply Subtype.ext
            rfl]
    rw [sampler, hatom]
    rw [CanonicalOrientedSetLaw.orientedJointMass_eq_Q_mul_orientationProbability
      w anchor hm hmK hw hanchor Uc jc]
    rfl
  have hdis :=
    FiniteOrientationDisintegration.orientedJointMass_eq_slowMarginal_mul_conditionalFastLaw
      (Finset.univ : Finset (Fin K)) Uc.1 m w anchor
      (Finset.subset_univ _) (CanonicalOrientedSetLaw.slowSet_card hm Uc)
      (CanonicalOrientedSetLaw.slowSet_complement_nonempty hm hmK Uc)
      (fun i _ => hw i) (fun i _ => hanchor i) jc
  calc
    _ = ENNReal.ofReal
        (FiniteOrientationDisintegration.orientedJointMass
          (Finset.univ : Finset (Fin K)) m w anchor Uc.1
          (Finset.subset_univ _) (CanonicalOrientedSetLaw.slowSet_card hm Uc)
          (fun i _ => hw i) (fun i _ => hanchor i) jc) := hjoint
    _ = ENNReal.ofReal
        (CanonicalOrientedSetLaw.slowMarginal w anchor hm hmK hw hanchor Uc *
          CanonicalOrientedSetLaw.fastArmConditionalMass w anchor hm hmK
            hw hanchor Uc jc) := by
      exact congrArg ENNReal.ofReal
        (by simpa only [CanonicalOrientedSetLaw.slowMarginal,
          CanonicalOrientedSetLaw.fastArmConditionalMass] using hdis)

/-- The actual slow-set sampler, transported to the existing canonical
supported-set carrier. -/
@[expose] noncomputable def canonicalSlowSampler {K m : ℕ} (hm : 2 ≤ m) (hmK : m < K)
    (w anchor : Fin K → ℝ) (hw : ∀ i, 0 < w i)
    (hanchor : ∀ i, 0 < anchor i)
    (v : Fin (K + 1) → ContinuousControlSlice.Scalar) :
    CanonicalOrientedSetLaw.SlowSet K m :=
  slowCarrierEquiv hm
    (OrientedAssignmentLaw.slowSampler hm hmK
      (productQNormalizedMass hm hmK w hw) anchor hanchor v)

theorem measurable_canonicalSlowSampler {K m : ℕ} (hm : 2 ≤ m) (hmK : m < K)
    (w anchor : Fin K → ℝ) (hw : ∀ i, 0 < w i)
    (hanchor : ∀ i, 0 < anchor i) :
    Measurable (canonicalSlowSampler hm hmK w anchor hw hanchor) := by
  have hslow := OrientedAssignmentLaw.measurable_slowSampler hm hmK
    (productQNormalizedMass hm hmK w hw) anchor hanchor
  have hequiv : Measurable (slowCarrierEquiv hm :
      OrientedAssignmentLaw.SlowSetCarrier K m →
        CanonicalOrientedSetLaw.SlowSet K m) := measurable_of_finite _
  exact hequiv.comp hslow

/-- The sampler's slow-outcome mass is the canonical slow marginal, identified
by the actual finite insertion sum and the accepted oriented disintegration. -/
theorem slowOutcomeMass_eq_slowMarginal {K m : ℕ} (hm : 2 ≤ m) (hmK : m < K)
    (w anchor : Fin K → ℝ) (hw : ∀ i, 0 < w i)
    (hanchor : ∀ i, 0 < anchor i)
    (U : OrientedAssignmentLaw.SlowSetCarrier K m) :
    OrientedAssignmentLaw.slowOutcomeMass hm
        (productQNormalizedMass hm hmK w hw) anchor hanchor U =
      CanonicalOrientedSetLaw.slowMarginal w anchor hm hmK hw hanchor
        (slowCarrierEquiv hm U) := by
  classical
  let Uc := slowCarrierEquiv hm U
  unfold OrientedAssignmentLaw.slowOutcomeMass
    CanonicalOrientedSetLaw.slowMarginal
  apply Finset.sum_congr rfl
  intro j hj
  let jc : {j : Fin K // j ∈ Finset.univ \ Uc.1} := ⟨j.1, by
    simp [Uc]⟩
  symm
  exact (CanonicalOrientedSetLaw.orientedJointMass_eq_Q_mul_orientationProbability
    w anchor hm hmK hw hanchor Uc jc).symm

/-- Every canonical slow marginal is strictly positive. -/
theorem slowMarginal_pos {K m : ℕ} (hm : 2 ≤ m) (hmK : m < K)
    (w anchor : Fin K → ℝ) (hw : ∀ i, 0 < w i)
    (hanchor : ∀ i, 0 < anchor i) (U : CanonicalOrientedSetLaw.SlowSet K m) :
    0 < CanonicalOrientedSetLaw.slowMarginal w anchor hm hmK hw hanchor U :=
  CanonicalOrientedSetLaw.slowMarginal_pos w anchor hm hmK hw hanchor U

/-- The derived fibre mass of the full assignment vector is exactly the
canonical slow marginal in ENNReal, for every supported slow set. -/
theorem canonicalSlowSampler_fibreMass {K m : ℕ} (hm : 2 ≤ m) (hmK : m < K)
    (w anchor : Fin K → ℝ) (hw : ∀ i, 0 < w i)
    (hanchor : ∀ i, 0 < anchor i) (U : CanonicalOrientedSetLaw.SlowSet K m) :
    FiniteFibreLift.fibreMass (ContinuousControlSlice.assignmentLaw K)
        (canonicalSlowSampler hm hmK w anchor hw hanchor) U =
      ENNReal.ofReal
        (CanonicalOrientedSetLaw.slowMarginal w anchor hm hmK hw hanchor U) := by
  have hpre :
      canonicalSlowSampler hm hmK w anchor hw hanchor ⁻¹' {U} =
        OrientedAssignmentLaw.slowSampler hm hmK
          (productQNormalizedMass hm hmK w hw) anchor hanchor ⁻¹'
            {(slowCarrierEquiv hm).symm U} := by
    ext v
    change slowCarrierEquiv hm
        (OrientedAssignmentLaw.slowSampler hm hmK
          (productQNormalizedMass hm hmK w hw) anchor hanchor v) = U ↔
      OrientedAssignmentLaw.slowSampler hm hmK
          (productQNormalizedMass hm hmK w hw) anchor hanchor v =
        (slowCarrierEquiv hm).symm U
    constructor
    · intro h
      have h' := congrArg (slowCarrierEquiv hm).symm h
      simpa using h'
    · intro h
      have h' := congrArg (slowCarrierEquiv hm) h
      simpa using h'
  rw [show FiniteFibreLift.fibreMass (ContinuousControlSlice.assignmentLaw K)
      (canonicalSlowSampler hm hmK w anchor hw hanchor) U =
        FiniteFibreLift.fibreMass (ContinuousControlSlice.assignmentLaw K)
          (OrientedAssignmentLaw.slowSampler hm hmK
            (productQNormalizedMass hm hmK w hw) anchor hanchor)
          ((slowCarrierEquiv hm).symm U) by
        change ContinuousControlSlice.assignmentLaw K
            (canonicalSlowSampler hm hmK w anchor hw hanchor ⁻¹' {U}) =
          ContinuousControlSlice.assignmentLaw K
            (OrientedAssignmentLaw.slowSampler hm hmK
              (productQNormalizedMass hm hmK w hw) anchor hanchor ⁻¹'
                {(slowCarrierEquiv hm).symm U})
        rw [hpre]]
  change FiniteFibreLift.fibreMass (ContinuousControlSlice.assignmentLaw K)
      (OrientedAssignmentLaw.slowSampler hm hmK
        (productQNormalizedMass hm hmK w hw) anchor hanchor)
      ((slowCarrierEquiv hm).symm U) = _
  rw [OrientedAssignmentLaw.fibreMass_eq_slowOutcomeMass hm hmK
    (productQNormalizedMass hm hmK w hw) anchor hanchor]
  rw [slowOutcomeMass_eq_slowMarginal hm hmK w anchor hw hanchor]
  simp [Equiv.apply_symm_apply]

/-- Every canonical slow-set fibre has positive assignment-vector mass. -/
theorem canonicalSlowSampler_fibreMass_pos {K m : ℕ} (hm : 2 ≤ m)
    (hmK : m < K) (w anchor : Fin K → ℝ) (hw : ∀ i, 0 < w i)
    (hanchor : ∀ i, 0 < anchor i) (U : CanonicalOrientedSetLaw.SlowSet K m) :
    0 < FiniteFibreLift.fibreMass (ContinuousControlSlice.assignmentLaw K)
      (canonicalSlowSampler hm hmK w anchor hw hanchor) U := by
  rw [canonicalSlowSampler_fibreMass]
  exact ENNReal.ofReal_pos.mpr (slowMarginal_pos hm hmK w anchor hw hanchor U)

/-- Under the canonical slow-set fibre measure, the conditional probability
of an inserted oriented outcome is exactly the accepted fast-arm law.

Source: `sources/zip4/manuscript/04_slow_fast_learner.tex:24-37` and
`sources/zip4/manuscript/06_interruptions.tex:410-423`. -/
theorem conditionalInsertedOutcome_probability {K m : ℕ} (hm : 2 ≤ m)
    (hmK : m < K) (w anchor : Fin K → ℝ) (hw : ∀ i, 0 < w i)
    (hanchor : ∀ i, 0 < anchor i)
    (U : OrientedAssignmentLaw.SlowSetCarrier K m)
    (j : {j : Fin K // j ∈ Finset.univ \ U.1}) :
    FiniteFibreLift.fibreMeasure (ContinuousControlSlice.assignmentLaw K)
        (canonicalSlowSampler hm hmK w anchor hw hanchor) (slowCarrierEquiv hm U)
        (sampler hm hmK w anchor hw hanchor ⁻¹'
          {OrientedAssignmentLaw.insertedOutcome U j}) =
      ENNReal.ofReal
        (CanonicalOrientedSetLaw.fastArmConditionalMass w anchor hm hmK
          hw hanchor (slowCarrierEquiv hm U)
          ⟨j.1, by simp⟩) := by
  let F := canonicalSlowSampler hm hmK w anchor hw hanchor
  let Uc := slowCarrierEquiv hm U
  have hjnot : j.1 ∉ Uc.1 := by
    simpa [Uc] using (Finset.mem_sdiff.mp j.2).2
  let jc : {j : Fin K // j ∈ Finset.univ \ Uc.1} :=
    ⟨j.1, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hjnot⟩⟩
  let C := sampler hm hmK w anchor hw hanchor ⁻¹'
    {OrientedAssignmentLaw.insertedOutcome U j}
  have hsampler : Measurable (sampler hm hmK w anchor hw hanchor) := by
    dsimp [sampler]
    exact OrientedAssignmentLaw.measurable_sampler hm hmK
      (productQNormalizedMass hm hmK w hw) anchor hanchor
  have hC : MeasurableSet C := hsampler (measurableSet_singleton _)
  have hsubset : C ⊆ FiniteFibreLift.fibre F Uc := by
    intro v hv
    change OrientedAssignmentLaw.sampler hm hmK
        (productQNormalizedMass hm hmK w hw) anchor hanchor v =
          OrientedAssignmentLaw.insertedOutcome U j at hv
    change slowCarrierEquiv hm
        (OrientedAssignmentLaw.slowOutcome
          (OrientedAssignmentLaw.sampler hm hmK
            (productQNormalizedMass hm hmK w hw) anchor hanchor v)) =
      slowCarrierEquiv hm U
    rw [hv, OrientedAssignmentLaw.slowOutcome_insertedOutcome]
  have hinter : C ∩ FiniteFibreLift.fibre F Uc = C :=
    Set.inter_eq_left.mpr hsubset
  have happly := FiniteFibreLift.fibreMeasure_apply
    (μ := ContinuousControlSlice.assignmentLaw K) (F := F) (a := Uc)
    (ne_of_gt (canonicalSlowSampler_fibreMass_pos hm hmK w anchor hw hanchor Uc)) hC
  rw [hinter] at happly
  calc
    _ = ContinuousControlSlice.assignmentLaw K C /
        FiniteFibreLift.fibreMass (ContinuousControlSlice.assignmentLaw K) F Uc := by
      rw [happly]
    _ = ENNReal.ofReal
          (CanonicalOrientedSetLaw.slowMarginal w anchor hm hmK hw hanchor Uc *
            CanonicalOrientedSetLaw.fastArmConditionalMass w anchor hm hmK
              hw hanchor Uc jc) /
        ENNReal.ofReal (CanonicalOrientedSetLaw.slowMarginal w anchor hm hmK
          hw hanchor Uc) := by
      rw [assignmentLaw_insertedOutcome, canonicalSlowSampler_fibreMass]
    _ = ENNReal.ofReal
        (CanonicalOrientedSetLaw.fastArmConditionalMass w anchor hm hmK
          hw hanchor Uc jc) := by
      rw [← ENNReal.ofReal_div_of_pos
        (CanonicalOrientedSetLaw.slowMarginal_pos w anchor hm hmK hw hanchor Uc)]
      congr 1
      field_simp [ne_of_gt
        (CanonicalOrientedSetLaw.slowMarginal_pos w anchor hm hmK hw hanchor Uc)]

/-- The entire assignment-vector slow-set pushforward is the accepted
canonical slow-set PMF. -/
theorem assignmentLaw_map_canonicalSlowSampler {K m : ℕ} (hm : 2 ≤ m)
    (hmK : m < K) (w anchor : Fin K → ℝ) (hw : ∀ i, 0 < w i)
    (hanchor : ∀ i, 0 < anchor i) :
    (ContinuousControlSlice.assignmentLaw K).map
        (canonicalSlowSampler hm hmK w anchor hw hanchor) =
      (CanonicalOrientedSetLaw.slowSetPMF w anchor hm hmK hw hanchor).toMeasure := by
  apply Measure.ext_of_singleton
  intro U
  rw [Measure.map_apply (measurable_canonicalSlowSampler hm hmK w anchor hw hanchor)
    (measurableSet_singleton U)]
  change FiniteFibreLift.fibreMass (ContinuousControlSlice.assignmentLaw K)
      (canonicalSlowSampler hm hmK w anchor hw hanchor) U = _
  rw [canonicalSlowSampler_fibreMass,
    PMF.toMeasure_apply_singleton
      (CanonicalOrientedSetLaw.slowSetPMF w anchor hm hmK hw hanchor) U
      (measurableSet_singleton U), CanonicalOrientedSetLaw.slowSetPMF_apply]

/-- Mixing the canonical slow marginal with the accepted conditional measure
on each full-vector fibre recovers the complete `K+1`-coordinate assignment
measure. -/
theorem canonicalSlowSampler_fibre_mixture {K m : ℕ} (hm : 2 ≤ m)
    (hmK : m < K) (w anchor : Fin K → ℝ) (hw : ∀ i, 0 < w i)
    (hanchor : ∀ i, 0 < anchor i) :
    (∑ U : CanonicalOrientedSetLaw.SlowSet K m,
      ENNReal.ofReal
          (CanonicalOrientedSetLaw.slowMarginal w anchor hm hmK hw hanchor U) •
        FiniteFibreLift.fibreMeasure (ContinuousControlSlice.assignmentLaw K)
          (canonicalSlowSampler hm hmK w anchor hw hanchor) U) =
      ContinuousControlSlice.assignmentLaw K := by
  calc
    _ = ∑ U : CanonicalOrientedSetLaw.SlowSet K m,
        FiniteFibreLift.fibreMass (ContinuousControlSlice.assignmentLaw K)
          (canonicalSlowSampler hm hmK w anchor hw hanchor) U •
        FiniteFibreLift.fibreMeasure (ContinuousControlSlice.assignmentLaw K)
          (canonicalSlowSampler hm hmK w anchor hw hanchor) U := by
      apply Finset.sum_congr rfl
      intro U hU
      rw [canonicalSlowSampler_fibreMass]
    _ = ContinuousControlSlice.assignmentLaw K :=
      FiniteFibreLift.sum_fibreMass_smul_fibreMeasure
        (μ := ContinuousControlSlice.assignmentLaw K)
        (F := canonicalSlowSampler hm hmK w anchor hw hanchor)
        (measurable_canonicalSlowSampler hm hmK w anchor hw hanchor)

/-- On each positive canonical fibre, the accepted lifted measure returns the
chosen slow set almost surely. -/
theorem ae_canonicalSlowSampler_fibre_eq {K m : ℕ} (hm : 2 ≤ m)
    (hmK : m < K) (w anchor : Fin K → ℝ) (hw : ∀ i, 0 < w i)
    (hanchor : ∀ i, 0 < anchor i) (U : CanonicalOrientedSetLaw.SlowSet K m) :
    ∀ᵐ v ∂FiniteFibreLift.fibreMeasure (ContinuousControlSlice.assignmentLaw K)
        (canonicalSlowSampler hm hmK w anchor hw hanchor) U,
      canonicalSlowSampler hm hmK w anchor hw hanchor v = U :=
  FiniteFibreLift.ae_fibreMeasure_eq
    (μ := ContinuousControlSlice.assignmentLaw K)
    (F := canonicalSlowSampler hm hmK w anchor hw hanchor) (a := U)
    (measurable_canonicalSlowSampler hm hmK w anchor hw hanchor)
    (ne_of_gt (canonicalSlowSampler_fibreMass_pos hm hmK w anchor hw hanchor U))

end Bandits.Support.CanonicalAssignmentVector

end
