/- Copyright (c) 2026. Released under Apache 2.0 license. -/
module

public import Bandits.Support.PrefixSamplerLaw
public import Bandits.Support.ContinuousCategorical
public import Bandits.Support.FiniteOrientationDisintegration
public import Bandits.Support.FiniteFibreLift

/-!
# The literal oriented assignment sampler

This module applies the accepted finite prefix sampler to the first `K`
coordinates of the actual `K + 1` assignment vector, and uses the final
coordinate to orient the sampled set in increasing arm-label order.

The input `NormalizedMass` is the actual normalized set-law interface. No
canonical product-set law or slow-set normalization is assumed here.

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:7-37`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:66-77`,
`sources/zip4/manuscript/appendix_b_communication.tex:40-44`, and
`sources/zip4/manuscript/06_interruptions.tex:410-423`.
-/

@[expose] public section
noncomputable section

namespace Bandits.Support.OrientedAssignmentLaw

open MeasureTheory Set
open scoped BigOperators ENNReal

abbrev SetCarrier := PrefixSetSampler.SetCarrier
abbrev NormalizedMass := PrefixSetSampler.NormalizedMass
abbrev Scalar := ContinuousControlSlice.Scalar

local instance setCarrierMeasurableSpace (K m : ℕ) :
    MeasurableSpace (SetCarrier K m) := ⊤

local instance setCarrierDiscreteMeasurableSpace (K m : ℕ) :
    DiscreteMeasurableSpace (SetCarrier K m) := ⟨fun _ => trivial⟩

/-- The finite carrier of an assignment set together with one selected arm. -/
abbrev AssignmentOutcome (K m : ℕ) :=
  {p : SetCarrier K m × Fin K // p.2 ∈ p.1.1}

/-- The finite carrier of slow sets of size `m - 1`, in equation form. -/
abbrev SlowSetCarrier (K m : ℕ) :=
  {U : Finset (Fin K) // U.card + 1 = m}

local instance assignmentOutcomeMeasurableSpace (K m : ℕ) :
    MeasurableSpace (AssignmentOutcome K m) := ⊤

local instance assignmentOutcomeDiscreteMeasurableSpace (K m : ℕ) :
    DiscreteMeasurableSpace (AssignmentOutcome K m) := ⟨fun _ => trivial⟩

local instance slowSetMeasurableSpace (K m : ℕ) :
    MeasurableSpace (SlowSetCarrier K m) := ⊤

local instance slowSetDiscreteMeasurableSpace (K m : ℕ) :
    DiscreteMeasurableSpace (SlowSetCarrier K m) := ⟨fun _ => trivial⟩

/-- The positive cardinality of a sampled set, derived from `2 ≤ m`. -/
theorem sampled_set_nonempty {K m : ℕ} (hm : 2 ≤ m)
    (S : SetCarrier K m) : S.1.Nonempty := by
  have hcard : S.1.card = m := (Finset.mem_powersetCard.mp S.2).2
  apply Finset.card_pos.mp
  omega

/-- The orientation probabilities in the fixed increasing arm-label order. -/
def orientationMasses {K m : ℕ} (hm : 2 ≤ m)
    (anchor : Fin K → ℝ) (hanchor : ∀ i, 0 < anchor i)
    (S : SetCarrier K m) : Fin S.1.card → ℝ := fun r =>
  FiniteOrientationDisintegration.orientationProbability anchor S.1
    (sampled_set_nonempty hm S) (fun i _ => hanchor i)
    ⟨S.1.orderEmbOfFin rfl r,
      S.1.orderEmbOfFin_mem rfl r⟩

/-- Every supported arm has a positive orientation mass. -/
theorem orientationMasses_pos {K m : ℕ} (hm : 2 ≤ m)
    (anchor : Fin K → ℝ) (hanchor : ∀ i, 0 < anchor i)
    (S : SetCarrier K m) (r : Fin S.1.card) :
    0 < orientationMasses hm anchor hanchor S r := by
  exact FiniteOrientationDisintegration.orientationProbability_pos anchor S.1
    (sampled_set_nonempty hm S) (fun i _ => hanchor i)
    ⟨S.1.orderEmbOfFin rfl r,
      S.1.orderEmbOfFin_mem rfl r⟩

/-- The orientation masses normalize by the accepted finite disintegration. -/
theorem orientationMasses_sum_eq_one {K m : ℕ} (hm : 2 ≤ m)
    (anchor : Fin K → ℝ) (hanchor : ∀ i, 0 < anchor i)
    (S : SetCarrier K m) :
    (∑ r, orientationMasses hm anchor hanchor S r) = 1 := by
  classical
  let e : Fin S.1.card ≃ {i // i ∈ S.1} :=
    (S.1.orderIsoOfFin rfl).toEquiv
  calc
    (∑ r, orientationMasses hm anchor hanchor S r) =
        ∑ i : {i // i ∈ S.1},
          FiniteOrientationDisintegration.orientationProbability anchor S.1
            (sampled_set_nonempty hm S) (fun i _ => hanchor i) i := by
      apply Fintype.sum_equiv e
      intro r
      rfl
    _ = 1 := by
      change (∑ i ∈ S.1.attach,
        FiniteOrientationDisintegration.orientationProbability anchor S.1
          (sampled_set_nonempty hm S) (fun i _ => hanchor i) i) = 1
      exact FiniteOrientationDisintegration.orientationProbability_sum_eq_one anchor S.1
        (sampled_set_nonempty hm S) (fun i _ => hanchor i)

/-- The inverse-CDF orientation index on the ordered members of `S`. -/
def orientationIndex {K m : ℕ} (hm : 2 ≤ m)
    (anchor : Fin K → ℝ) (hanchor : ∀ i, 0 < anchor i)
    (S : SetCarrier K m) (x : Scalar) : Fin S.1.card :=
  ContinuousCategorical.sample (Finset.card_pos.mpr (sampled_set_nonempty hm S))
    (orientationMasses hm anchor hanchor S)
    (orientationMasses_sum_eq_one hm anchor hanchor S) x

/-- The arm selected at that index; `orderEmbOfFin` is the increasing order. -/
def orientationArm {K m : ℕ} (hm : 2 ≤ m)
    (anchor : Fin K → ℝ) (hanchor : ∀ i, 0 < anchor i)
    (S : SetCarrier K m) (x : Scalar) : Fin K :=
  S.1.orderEmbOfFin rfl
    (orientationIndex hm anchor hanchor S x)

/-- The inverse rank of an arm in the increasing order of `S`. -/
def orientationRank {K m : ℕ} (S : SetCarrier K m)
    (j : {j : Fin K // j ∈ S.1}) : Fin S.1.card :=
  (S.1.orderIsoOfFin rfl).symm j

/-- The actual assignment sampler, retaining and consuming all `K + 1`
coordinates. The first `K` coordinates feed the accepted prefix sampler; the
last coordinate supplies the orientation draw. -/
def sampler {K m : ℕ} (hm : 2 ≤ m) (_hmK : m < K)
    {hm' : m ≤ K} (μ : NormalizedMass K m hm')
    (anchor : Fin K → ℝ) (hanchor : ∀ i, 0 < anchor i)
    (v : Fin (K + 1) → Scalar) : AssignmentOutcome K m :=
  let S := PrefixSetSampler.sample μ (PrefixSamplerLaw.prefixValues v)
  ⟨(S, orientationArm hm anchor hanchor S (v (Fin.last K))),
    S.1.orderEmbOfFin_mem rfl
      (orientationIndex hm anchor hanchor S (v (Fin.last K)))⟩

/-- Split the accepted assignment vector into its final scalar and the entire
first-`K` block. -/
def splitLast {K : ℕ} (v : Fin (K + 1) → Scalar) :
    Scalar × (Fin K → Scalar) :=
  (v (Fin.last K), PrefixSamplerLaw.prefixValues v)

/-- Measurability of the full vector split. -/
theorem measurable_splitLast (K : ℕ) :
    Measurable (splitLast (K := K)) := by
  exact (measurable_pi_apply (Fin.last K)).prodMk
    (PrefixSamplerLaw.measurable_prefixValues K)

/-- The real product-vector law factors the last coordinate from the whole
first-`K` vector. This is a joint product-law statement, not a claim from
coordinate marginals alone. -/
theorem assignmentLaw_map_splitLast (K : ℕ) :
    (ContinuousControlSlice.assignmentLaw K).map (splitLast (K := K)) =
      ContinuousControlSlice.scalarLaw.prod (PrefixSamplerLaw.cubeLaw K) := by
  let e := MeasurableEquiv.piFinSuccAbove
    (fun _ : Fin (K + 1) => Scalar) (Fin.last K)
  have hmp : MeasurePreserving e (ContinuousControlSlice.assignmentLaw K)
      (ContinuousControlSlice.scalarLaw.prod
        (Measure.pi fun _ : Fin K => ContinuousControlSlice.scalarLaw)) :=
    measurePreserving_piFinSuccAbove (fun _ => ContinuousControlSlice.scalarLaw)
      (Fin.last K)
  have h := hmp.map_eq
  have he : (fun v : Fin (K + 1) → Scalar =>
      (v (Fin.last K), fun i : Fin K => v ((Fin.last K).succAbove i))) =
      splitLast (K := K) := by
    funext v
    apply Prod.ext
    · rfl
    · funext i
      simp [splitLast, PrefixSamplerLaw.prefixValues,
        Fin.succAbove_last_apply]
  change (ContinuousControlSlice.assignmentLaw K).map
    (fun v : Fin (K + 1) → Scalar =>
      (v (Fin.last K), fun i : Fin K => v ((Fin.last K).succAbove i))) = _ at h
  rw [he] at h
  simpa [PrefixSamplerLaw.cubeLaw] using h

/-- The sampled set is independent of the final scalar, while the whole first
`K` vector remains the input to that set sampler. -/
theorem assignmentLaw_map_sampleAndLast {K m : ℕ} {hm' : m ≤ K}
    (μ : NormalizedMass K m hm') :
    (ContinuousControlSlice.assignmentLaw K).map
      (fun v => (v (Fin.last K),
        PrefixSetSampler.sample μ (PrefixSamplerLaw.prefixValues v))) =
      ContinuousControlSlice.scalarLaw.prod
        (PrefixSamplerLaw.massPMF μ).toMeasure := by
  have hsample : Measurable (PrefixSetSampler.sample μ) :=
    PrefixSamplerLaw.measurable_sample μ
  have hid : Measurable (id : Scalar → Scalar) := measurable_id
  have hpair : Measurable
      (Prod.map id (PrefixSetSampler.sample μ)) := hid.prodMap hsample
  calc
    _ = ((ContinuousControlSlice.assignmentLaw K).map
          (splitLast (K := K))).map
            (Prod.map id (PrefixSetSampler.sample μ)) := by
      rw [Measure.map_map hpair (measurable_splitLast K)]
      rfl
    _ = (ContinuousControlSlice.scalarLaw.prod (PrefixSamplerLaw.cubeLaw K)).map
          (Prod.map id (PrefixSetSampler.sample μ)) := by
      rw [assignmentLaw_map_splitLast]
    _ = (ContinuousControlSlice.scalarLaw.map (fun x : Scalar => x)).prod
          ((PrefixSamplerLaw.cubeLaw K).map (PrefixSetSampler.sample μ)) := by
      rw [← Measure.map_prod_map _ _ hid hsample]
      rfl
    _ = _ := by
      rw [Measure.map_id', PrefixSamplerLaw.cubeLaw_map_sample]

/-- The sampled-set/last-scalar map is measurable. -/
theorem measurable_sampleAndLast {K m : ℕ} {hm' : m ≤ K}
    (μ : NormalizedMass K m hm') :
    Measurable (fun v : Fin (K + 1) → Scalar =>
      (v (Fin.last K), PrefixSetSampler.sample μ
        (PrefixSamplerLaw.prefixValues v))) := by
  exact (measurable_pi_apply (Fin.last K)).prodMk
    (PrefixSamplerLaw.measurable_sample_prefixValues μ)

/-- The scalar interval that gives rank `r` in the increasing orientation
order. -/
def orientationScalarFibre {K m : ℕ} (hm : 2 ≤ m)
    (anchor : Fin K → ℝ) (hanchor : ∀ i, 0 < anchor i)
    (S : SetCarrier K m) (r : Fin S.1.card) : Set Scalar :=
  ContinuousCategorical.sample (Finset.card_pos.mpr (sampled_set_nonempty hm S))
    (orientationMasses hm anchor hanchor S)
    (orientationMasses_sum_eq_one hm anchor hanchor S) ⁻¹' {r}

/-- The increasing order enumerates exactly the arms in the orientation
categorical draw. -/
theorem orientationArm_eq_iff {K m : ℕ} (hm : 2 ≤ m)
    (anchor : Fin K → ℝ) (hanchor : ∀ i, 0 < anchor i)
    (S : SetCarrier K m) (x : Scalar) (j : {j : Fin K // j ∈ S.1}) :
    orientationArm hm anchor hanchor S x = j.1 ↔
      ContinuousCategorical.sample (Finset.card_pos.mpr (sampled_set_nonempty hm S))
        (orientationMasses hm anchor hanchor S)
        (orientationMasses_sum_eq_one hm anchor hanchor S) x = orientationRank S j := by
  let e := S.1.orderIsoOfFin rfl
  constructor
  · intro h
    have hmem : e (orientationIndex hm anchor hanchor S x) = j := by
      apply Subtype.ext
      change S.1.orderEmbOfFin rfl (orientationIndex hm anchor hanchor S x) = j.1
      exact h
    have hidx : orientationIndex hm anchor hanchor S x = e.symm j := by
      apply e.injective
      rw [e.apply_symm_apply]
      exact hmem
    simpa [orientationIndex, orientationRank] using hidx
  · intro h
    have hidx : orientationIndex hm anchor hanchor S x = e.symm j := by
      simpa [orientationIndex, orientationRank] using h
    calc
      orientationArm hm anchor hanchor S x =
          ((e (orientationIndex hm anchor hanchor S x) : S.1) : Fin K) := by
        change S.1.orderEmbOfFin rfl (orientationIndex hm anchor hanchor S x) = _
        exact (Finset.coe_orderIsoOfFin_apply S.1 rfl _).symm
      _ = ((e (e.symm j) : S.1) : Fin K) := congrArg (fun r => (e r).1) hidx
      _ = j.1 := congrArg Subtype.val (e.apply_symm_apply j)

/-- The last-coordinate orientation interval has exactly its supplied
`orientationProbability` mass. -/
theorem scalarLaw_orientationScalarFibre {K m : ℕ} (hm : 2 ≤ m)
    (anchor : Fin K → ℝ) (hanchor : ∀ i, 0 < anchor i)
    (S : SetCarrier K m) (r : Fin S.1.card) :
    ContinuousControlSlice.scalarLaw (orientationScalarFibre hm anchor hanchor S r) =
      ENNReal.ofReal (orientationMasses hm anchor hanchor S r) := by
  change ContinuousCategorical.uniform
    (ContinuousCategorical.sample _ _ _ ⁻¹' {r}) = _
  exact ContinuousCategorical.uniform_sample_singleton
    (Finset.card_pos.mpr (sampled_set_nonempty hm S))
    (fun i => (orientationMasses_pos hm anchor hanchor S i).le)
    (orientationMasses_sum_eq_one hm anchor hanchor S) r

/-- Measurability of each fixed-set orientation interval. -/
theorem measurable_orientationScalarFibre {K m : ℕ} (hm : 2 ≤ m)
    (anchor : Fin K → ℝ) (hanchor : ∀ i, 0 < anchor i)
    (S : SetCarrier K m) (r : Fin S.1.card) :
    MeasurableSet (orientationScalarFibre hm anchor hanchor S r) := by
  change MeasurableSet
    (ContinuousCategorical.sample _ _ _ ⁻¹' {r})
  exact (ContinuousCategorical.measurable_sample
    (Finset.card_pos.mpr (sampled_set_nonempty hm S))
    (fun i => (orientationMasses_pos hm anchor hanchor S i).le)
    (orientationMasses_sum_eq_one hm anchor hanchor S))
    (measurableSet_singleton _)

/-- The sampler's singleton fibre is the cylinder fixing the first-block set
and the last-coordinate orientation rank. -/
theorem sampler_preimage_singleton {K m : ℕ} (hm : 2 ≤ m) (hmK : m < K)
    {hm' : m ≤ K} (μ : NormalizedMass K m hm')
    (anchor : Fin K → ℝ) (hanchor : ∀ i, 0 < anchor i)
    (S : SetCarrier K m) (j : {j : Fin K // j ∈ S.1}) :
    sampler hm hmK μ anchor hanchor ⁻¹' {⟨(S, j.1), j.2⟩} =
      (fun v => (v (Fin.last K), PrefixSetSampler.sample μ
        (PrefixSamplerLaw.prefixValues v))) ⁻¹'
        (orientationScalarFibre hm anchor hanchor S (orientationRank S j) ×ˢ {S}) := by
  ext v
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_prod]
  constructor
  · intro hv
    have hval := congrArg Subtype.val hv
    simp only [sampler, Prod.mk.injEq] at hval
    rcases hval with ⟨hS, hArm⟩
    refine ⟨?_, hS⟩
    rw [hS] at hArm
    change ContinuousCategorical.sample _ _ _ _ = orientationRank S j
    exact (orientationArm_eq_iff hm anchor hanchor S
      (v (Fin.last K)) j).mp hArm
  · rintro ⟨hRank, hS⟩
    dsimp [sampler]
    apply Subtype.ext
    apply Prod.ext
    · exact hS
    · have hsetArm := congrArg
        (fun T : SetCarrier K m => orientationArm hm anchor hanchor T (v (Fin.last K))) hS
      exact hsetArm.trans
        ((orientationArm_eq_iff hm anchor hanchor S (v (Fin.last K)) j).mpr hRank)

/-- Measurability of the literal sampler, from its exact singleton fibres. -/
theorem measurable_sampler {K m : ℕ} (hm : 2 ≤ m) (hmK : m < K)
    {hm' : m ≤ K} (μ : NormalizedMass K m hm')
    (anchor : Fin K → ℝ) (hanchor : ∀ i, 0 < anchor i) :
    Measurable (sampler hm hmK μ anchor hanchor) := by
  apply measurable_to_countable'
  intro o
  rcases o with ⟨⟨S, j⟩, hj⟩
  rw [sampler_preimage_singleton hm hmK μ anchor hanchor S ⟨j, hj⟩]
  exact (measurable_sampleAndLast μ)
    (measurableSet_prod.mpr (Or.inl ⟨
      measurable_orientationScalarFibre hm anchor hanchor S
        (orientationRank S ⟨j, hj⟩),
      measurableSet_singleton S⟩))

/-- Exact joint atom mass from the full assignment vector. The first factor is
the accepted `K`-coordinate sampler law; the final independent coordinate
contributes the existing inverse-anchor orientation probability. -/
theorem assignmentLaw_sampler_singleton {K m : ℕ} (hm : 2 ≤ m) (hmK : m < K)
    {hm' : m ≤ K} (μ : NormalizedMass K m hm')
    (anchor : Fin K → ℝ) (hanchor : ∀ i, 0 < anchor i)
    (S : SetCarrier K m) (j : {j : Fin K // j ∈ S.1}) :
    ContinuousControlSlice.assignmentLaw K
      (sampler hm hmK μ anchor hanchor ⁻¹' {⟨(S, j.1), j.2⟩}) =
      ENNReal.ofReal (μ.weight S *
        FiniteOrientationDisintegration.orientationProbability anchor S.1
          (sampled_set_nonempty hm S) (fun i _ => hanchor i) j) := by
  have hrect : MeasurableSet
      (orientationScalarFibre hm anchor hanchor S (orientationRank S j) ×ˢ {S}) :=
    measurableSet_prod.mpr (Or.inl ⟨
      measurable_orientationScalarFibre hm anchor hanchor S (orientationRank S j),
      measurableSet_singleton S⟩)
  rw [sampler_preimage_singleton hm hmK μ anchor hanchor S j,
    ← Measure.map_apply (measurable_sampleAndLast μ) hrect]
  rw [assignmentLaw_map_sampleAndLast μ, Measure.prod_prod,
    scalarLaw_orientationScalarFibre]
  have hα : orientationMasses hm anchor hanchor S (orientationRank S j) =
      FiniteOrientationDisintegration.orientationProbability anchor S.1
        (sampled_set_nonempty hm S) (fun i _ => hanchor i) j := by
    dsimp [orientationMasses, orientationRank]
    congr 1
    apply Subtype.ext
    exact congrArg Subtype.val ((S.1.orderIsoOfFin rfl).apply_symm_apply j)
  rw [PMF.toMeasure_apply_singleton _ S (measurableSet_singleton S),
    PrefixSamplerLaw.massPMF_apply, hα]
  have hw := μ.weight_nonneg S
  calc
    _ = ENNReal.ofReal (μ.weight S) *
        ENNReal.ofReal (FiniteOrientationDisintegration.orientationProbability anchor S.1
          (sampled_set_nonempty hm S) (fun i _ => hanchor i) j) := by rw [mul_comm]
    _ = _ := (ENNReal.ofReal_mul hw).symm

/-- The slow set assigned after deleting the selected fast arm. -/
def slowOutcome {K m : ℕ} (o : AssignmentOutcome K m) : SlowSetCarrier K m :=
  ⟨o.1.1.1.erase o.1.2, by
    have hmem : o.1.2 ∈ o.1.1.1 := o.2
    have hcard : o.1.1.1.card = m :=
      (Finset.mem_powersetCard.mp o.1.1.2).2
    rw [Finset.card_erase_add_one hmem, hcard]⟩

/-- The selected arm is outside the returned slow set. -/
theorem slowOutcome_arm_not_mem {K m : ℕ} (o : AssignmentOutcome K m) :
    o.1.2 ∉ (slowOutcome o).1 := by
  change o.1.2 ∉ o.1.1.1.erase o.1.2
  exact Finset.notMem_erase _ _

/-- The slow outcome has exactly `m - 1` arms. -/
theorem slowOutcome_card {K m : ℕ} (o : AssignmentOutcome K m) :
    (slowOutcome o).1.card = m - 1 := by
  have h := (slowOutcome o).2
  omega

/-- The actual insertion of a complement arm produces a supported `m`-set. -/
def insertedSet {K m : ℕ} (U : SlowSetCarrier K m)
    (j : {j : Fin K // j ∈ Finset.univ \ U.1}) : SetCarrier K m :=
  ⟨insert j.1 U.1, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, by
    rw [Finset.card_insert_of_notMem (Finset.mem_sdiff.mp j.2).2, U.2]⟩⟩

/-- The oriented insertion outcome associated with a slow set and an arm
outside it. -/
def insertedOutcome {K m : ℕ} (U : SlowSetCarrier K m)
    (j : {j : Fin K // j ∈ Finset.univ \ U.1}) : AssignmentOutcome K m :=
  ⟨(insertedSet U j, j.1), Finset.mem_insert_self _ _⟩

/-- Deleting the inserted arm recovers the chosen slow set. -/
theorem slowOutcome_insertedOutcome {K m : ℕ} (U : SlowSetCarrier K m)
    (j : {j : Fin K // j ∈ Finset.univ \ U.1}) :
    slowOutcome (insertedOutcome U j) = U := by
  apply Subtype.ext
  change (insert j.1 U.1).erase j.1 = U.1
  exact Finset.erase_insert (Finset.mem_sdiff.mp j.2).2

/-- The actual slow sampler, obtained from the oriented assignment sampler. -/
def slowSampler {K m : ℕ} (hm : 2 ≤ m) (hmK : m < K)
    {hm' : m ≤ K} (μ : NormalizedMass K m hm')
    (anchor : Fin K → ℝ) (hanchor : ∀ i, 0 < anchor i)
    (v : Fin (K + 1) → Scalar) : SlowSetCarrier K m :=
  slowOutcome (sampler hm hmK μ anchor hanchor v)

/-- The finite outcome projection is measurable. -/
theorem measurable_slowOutcome {K m : ℕ} :
    Measurable (slowOutcome : AssignmentOutcome K m → SlowSetCarrier K m) :=
  measurable_of_finite _

/-- Measurability of the actual slow sampler. -/
theorem measurable_slowSampler {K m : ℕ} (hm : 2 ≤ m) (hmK : m < K)
    {hm' : m ≤ K} (μ : NormalizedMass K m hm')
    (anchor : Fin K → ℝ) (hanchor : ∀ i, 0 < anchor i) :
    Measurable (slowSampler hm hmK μ anchor hanchor) :=
  (measurable_slowOutcome (K := K) (m := m)).comp
    (measurable_sampler hm hmK μ anchor hanchor)

/-- The literal slow outcome mass, summed over insertion arms and their
orientation probabilities. -/
def slowOutcomeMass {K m : ℕ} (_hm : 2 ≤ m)
    {hm' : m ≤ K} (μ : NormalizedMass K m hm')
    (anchor : Fin K → ℝ) (hanchor : ∀ i, 0 < anchor i)
    (U : SlowSetCarrier K m) : ℝ :=
  ∑ j ∈ (Finset.univ \ U.1).attach,
    μ.weight (insertedSet U j) *
      FiniteOrientationDisintegration.orientationProbability anchor
        (insert j.1 U.1) (Finset.insert_nonempty _ _) (fun i _ => hanchor i)
        ⟨j.1, Finset.mem_insert_self _ _⟩

/-- The slow-sampler fibre is the disjoint union over all valid insertion
arms. -/
theorem slowSampler_preimage_eq_biUnion {K m : ℕ} (hm : 2 ≤ m) (hmK : m < K)
    {hm' : m ≤ K} (μ : NormalizedMass K m hm')
    (anchor : Fin K → ℝ) (hanchor : ∀ i, 0 < anchor i)
    (U : SlowSetCarrier K m) :
    slowSampler hm hmK μ anchor hanchor ⁻¹' {U} =
      ⋃ j ∈ (Finset.univ \ U.1).attach,
        sampler hm hmK μ anchor hanchor ⁻¹' {insertedOutcome U j} := by
  ext v
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion,
    Finset.mem_attach]
  constructor
  · intro hv
    let o := sampler hm hmK μ anchor hanchor v
    have hslow : slowOutcome o = U := hv
    let j : Fin K := o.1.2
    have hjnot : j ∉ U.1 := by
      intro hj
      have hmem : j ∈ (slowOutcome o).1 := by
        rw [hslow]
        exact hj
      exact (slowOutcome_arm_not_mem o) hmem
    let j' : {j : Fin K // j ∈ Finset.univ \ U.1} :=
      ⟨j, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hjnot⟩⟩
    have hslowVal := congrArg Subtype.val hslow
    change o.1.1.1.erase j = U.1 at hslowVal
    have hsetFin : o.1.1.1 = insert j U.1 := by
      calc
        o.1.1.1 = insert j (o.1.1.1.erase j) := (Finset.insert_erase o.2).symm
        _ = insert j U.1 := by rw [hslowVal]
    have hset : o.1.1 = insertedSet U j' := by
      apply Subtype.ext
      exact hsetFin
    have hout : o = insertedOutcome U j' := by
      apply Subtype.ext
      apply Prod.ext
      · exact hset
      · rfl
    exact ⟨j', ⟨trivial, hout⟩⟩
  · rintro ⟨j, hj⟩
    rcases hj with ⟨_, hj⟩
    have h := congrArg slowOutcome hj
    simpa only [slowSampler, slowOutcome_insertedOutcome] using h

/-- The literal insertion sum is exactly the sampler's slow-set fibre mass.
The proof uses only the `K+1`-coordinate assignment law and the exact
oriented atom law. -/
theorem fibreMass_eq_slowOutcomeMass {K m : ℕ} (hm : 2 ≤ m) (hmK : m < K)
    {hm' : m ≤ K} (μ : NormalizedMass K m hm')
    (anchor : Fin K → ℝ) (hanchor : ∀ i, 0 < anchor i)
    (U : SlowSetCarrier K m) :
    FiniteFibreLift.fibreMass (ContinuousControlSlice.assignmentLaw K)
      (slowSampler hm hmK μ anchor hanchor) U =
        ENNReal.ofReal (slowOutcomeMass hm μ anchor hanchor U) := by
  change (ContinuousControlSlice.assignmentLaw K)
      (slowSampler hm hmK μ anchor hanchor ⁻¹' {U}) = _
  rw [slowSampler_preimage_eq_biUnion hm hmK μ anchor hanchor U]
  let D := (Finset.univ \ U.1).attach
  have hdisj : Set.PairwiseDisjoint (↑D) (fun j =>
      sampler hm hmK μ anchor hanchor ⁻¹' {insertedOutcome U j}) := by
    intro j hj k hk hjk
    apply Set.disjoint_left.mpr
    intro v hvj hvk
    change sampler hm hmK μ anchor hanchor v = insertedOutcome U j at hvj
    change sampler hm hmK μ anchor hanchor v = insertedOutcome U k at hvk
    have heq : insertedOutcome U j = insertedOutcome U k := hvj.symm.trans hvk
    apply hjk
    apply Subtype.ext
    exact congrArg Prod.snd (congrArg Subtype.val heq)
  have hmSets : ∀ j ∈ D, MeasurableSet
      (sampler hm hmK μ anchor hanchor ⁻¹' {insertedOutcome U j}) := by
    intro j hj
    exact measurable_sampler hm hmK μ anchor hanchor
      (measurableSet_singleton _)
  rw [measure_biUnion_finset hdisj hmSets]
  have hAtom (j : {j : Fin K // j ∈ Finset.univ \ U.1}) :
      (ContinuousControlSlice.assignmentLaw K)
        (sampler hm hmK μ anchor hanchor ⁻¹' {insertedOutcome U j}) =
      ENNReal.ofReal (μ.weight (insertedSet U j) *
        FiniteOrientationDisintegration.orientationProbability anchor
          (insert j.1 U.1) (Finset.insert_nonempty _ _)
          (fun i _ => hanchor i) ⟨j.1, Finset.mem_insert_self _ _⟩) := by
    simpa only [insertedOutcome, insertedSet] using
      assignmentLaw_sampler_singleton hm hmK μ anchor hanchor
        (insertedSet U j) ⟨j.1, Finset.mem_insert_self _ _⟩
  simp_rw [hAtom]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun j hj =>
    mul_nonneg (μ.weight_nonneg (insertedSet U j))
      (FiniteOrientationDisintegration.orientationProbability_pos anchor
        (insert j.1 U.1) (Finset.insert_nonempty _ _)
        (fun i _ => hanchor i) ⟨j.1, Finset.mem_insert_self _ _⟩).le)]
  rfl

/-- Every insertion summand is nonnegative. -/
theorem slowOutcomeMass_nonneg {K m : ℕ} (hm : 2 ≤ m)
    {hm' : m ≤ K} (μ : NormalizedMass K m hm')
    (anchor : Fin K → ℝ) (hanchor : ∀ i, 0 < anchor i)
    (U : SlowSetCarrier K m) : 0 ≤ slowOutcomeMass hm μ anchor hanchor U := by
  unfold slowOutcomeMass
  apply Finset.sum_nonneg
  intro j hj
  exact mul_nonneg (μ.weight_nonneg (insertedSet U j))
    (FiniteOrientationDisintegration.orientationProbability_pos anchor
      (insert j.1 U.1) (Finset.insert_nonempty _ _)
      (fun i _ => hanchor i) ⟨j.1, Finset.mem_insert_self _ _⟩).le

/-- The insertion-defined slow outcome masses normalize, proved from the
sampler fibre identity and the finite-fibre partition. -/
theorem slowOutcomeMass_sum_eq_one {K m : ℕ} (hm : 2 ≤ m) (hmK : m < K)
    {hm' : m ≤ K} (μ : NormalizedMass K m hm')
    (anchor : Fin K → ℝ) (hanchor : ∀ i, 0 < anchor i) :
    (∑ U : SlowSetCarrier K m, slowOutcomeMass hm μ anchor hanchor U) = 1 := by
  have hsum := FiniteFibreLift.sum_fibreMass
    (μ := ContinuousControlSlice.assignmentLaw K)
    (F := slowSampler hm hmK μ anchor hanchor)
    (measurable_slowSampler hm hmK μ anchor hanchor)
  simp_rw [fibreMass_eq_slowOutcomeMass hm hmK μ anchor hanchor] at hsum
  have hreal : ENNReal.ofReal
      (∑ U : SlowSetCarrier K m, slowOutcomeMass hm μ anchor hanchor U) = 1 := by
    calc
      _ = ∑ U : SlowSetCarrier K m,
          ENNReal.ofReal (slowOutcomeMass hm μ anchor hanchor U) :=
        ENNReal.ofReal_sum_of_nonneg (fun U _ =>
          slowOutcomeMass_nonneg hm μ anchor hanchor U)
      _ = 1 := hsum
  have hnonneg : 0 ≤ ∑ U : SlowSetCarrier K m,
      slowOutcomeMass hm μ anchor hanchor U :=
    Finset.sum_nonneg (fun U _ => slowOutcomeMass_nonneg hm μ anchor hanchor U)
  have hto := congrArg ENNReal.toReal hreal
  simpa [ENNReal.toReal_ofReal hnonneg] using hto

/-- Mixing the accepted fibre measures with the actual sampler's fibre masses
recovers the full `K+1`-vector assignment law. -/
theorem slowSampler_fibre_mixture {K m : ℕ} (hm : 2 ≤ m) (hmK : m < K)
    {hm' : m ≤ K} (μ : NormalizedMass K m hm')
    (anchor : Fin K → ℝ) (hanchor : ∀ i, 0 < anchor i) :
    (∑ U : SlowSetCarrier K m,
      FiniteFibreLift.fibreMass (ContinuousControlSlice.assignmentLaw K)
          (slowSampler hm hmK μ anchor hanchor) U •
        FiniteFibreLift.fibreMeasure (ContinuousControlSlice.assignmentLaw K)
          (slowSampler hm hmK μ anchor hanchor) U) =
      ContinuousControlSlice.assignmentLaw K :=
  FiniteFibreLift.sum_fibreMass_smul_fibreMeasure
    (μ := ContinuousControlSlice.assignmentLaw K)
    (F := slowSampler hm hmK μ anchor hanchor)
    (measurable_slowSampler hm hmK μ anchor hanchor)

/-- On every positive slow-set fibre, the lifted full-vector sample returns
that chosen slow set almost surely. -/
theorem ae_slowSampler_fibre_eq {K m : ℕ} (hm : 2 ≤ m) (hmK : m < K)
    {hm' : m ≤ K} (μ : NormalizedMass K m hm')
    (anchor : Fin K → ℝ) (hanchor : ∀ i, 0 < anchor i)
    (U : SlowSetCarrier K m)
    (hU : FiniteFibreLift.fibreMass (ContinuousControlSlice.assignmentLaw K)
      (slowSampler hm hmK μ anchor hanchor) U ≠ 0) :
    ∀ᵐ v ∂FiniteFibreLift.fibreMeasure (ContinuousControlSlice.assignmentLaw K)
      (slowSampler hm hmK μ anchor hanchor) U,
      slowSampler hm hmK μ anchor hanchor v = U :=
  FiniteFibreLift.ae_fibreMeasure_eq
    (μ := ContinuousControlSlice.assignmentLaw K)
    (F := slowSampler hm hmK μ anchor hanchor) (a := U)
    (measurable_slowSampler hm hmK μ anchor hanchor) hU

/-- The source-permitted null-fibre branch keeps the original full-vector
assignment law. -/
theorem slowSampler_null_fibre_measure {K m : ℕ} (hm : 2 ≤ m) (hmK : m < K)
    {hm' : m ≤ K} (μ : NormalizedMass K m hm')
    (anchor : Fin K → ℝ) (hanchor : ∀ i, 0 < anchor i)
    (U : SlowSetCarrier K m)
    (hU : FiniteFibreLift.fibreMass (ContinuousControlSlice.assignmentLaw K)
      (slowSampler hm hmK μ anchor hanchor) U = 0) :
    FiniteFibreLift.fibreMeasure (ContinuousControlSlice.assignmentLaw K)
      (slowSampler hm hmK μ anchor hanchor) U =
        ContinuousControlSlice.assignmentLaw K :=
  FiniteFibreLift.fibreMeasure_of_eq_zero
    (μ := ContinuousControlSlice.assignmentLaw K)
    (F := slowSampler hm hmK μ anchor hanchor) (a := U) hU

end Bandits.Support.OrientedAssignmentLaw

end
