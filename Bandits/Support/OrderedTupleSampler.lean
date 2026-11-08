/- Copyright (c) 2026. Released under Apache 2.0 license. -/
module

public import Bandits.Support.ContinuousControlSlice
public import Bandits.Support.ContinuousCategorical
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Fintype.CardEmbedding
public import Mathlib.Data.Nat.Factorial.BigOperators

/-!
# Ordered sampling without replacement

Literal construction from
`sources/zip4/manuscript/appendix_b_communication.tex:25-44`, especially line 42.
Arms use zero-based `Fin K`; index `j` in the increasing remainder is the source
arm of rank `1+j`. Scalars have the genuine half-open domain `[0,1)`.
This module concerns one unconditional slice, without adaptive history claims.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.OrderedTupleSampler

open MeasureTheory Set
open ContinuousControlSlice
open scoped BigOperators ENNReal

/-- The genuine carrier of ordered injective tuples. -/
abbrev Tuple (m K : ℕ) := {f : Fin m → Fin K // Function.Injective f}

variable {m K r : ℕ}

/-- Arms remaining after an injective prefix, retaining the arm order. -/
def remainder (f : Tuple r K) : Finset (Fin K) :=
  Finset.univ \ (Finset.univ.image f.val)

theorem mem_remainder (f : Tuple r K) (a : Fin K) :
    a ∈ remainder f ↔ a ∉ Set.range f.val := by
  simp [remainder]

theorem card_remainder (f : Tuple r K) : (remainder f).card = K - r := by
  rw [remainder, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
    Fintype.card_fin, Finset.card_image_of_injective _ f.property,
    Finset.card_univ, Fintype.card_fin]

/-- Zero-based version of the displayed rank `1+floor(n*v)`. -/
def rank (n : ℕ) (hn : 0 < n) (v : Scalar) : Fin n :=
  ⟨Nat.floor ((n : ℝ) * v.val), (Nat.floor_lt (mul_nonneg (Nat.cast_nonneg n)
    v.property.1)).mpr (by
      simpa using mul_lt_mul_of_pos_left v.property.2 (Nat.cast_pos.mpr hn))⟩

theorem rank_val (n : ℕ) (hn : 0 < n) (v : Scalar) :
    (rank n hn v).val = Nat.floor ((n : ℝ) * v.val) := rfl

/-- The displayed one-based rank is always valid, at every cube input. -/
theorem source_rank_bounds (n : ℕ) (hn : 0 < n) (v : Scalar) :
    1 ≤ 1 + Nat.floor ((n : ℝ) * v.val) ∧
      1 + Nat.floor ((n : ℝ) * v.val) ≤ n := by
  have hi := (rank n hn v).isLt
  rw [rank_val] at hi
  omega

theorem rank_eq_iff (n : ℕ) (hn : 0 < n) (v : Scalar) (i : Fin n) :
    rank n hn v = i ↔
      (i.val : ℝ) / n ≤ v.val ∧ v.val < ((i.val : ℝ) + 1) / n := by
  rw [Fin.ext_iff, rank_val, Nat.floor_eq_iff
    (mul_nonneg (Nat.cast_nonneg n) v.property.1)]
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  rw [div_le_iff₀ hn', lt_div_iff₀ hn']
  simp only [mul_comm]

/-- Select the displayed rank in the increasing remainder. No arbitrary arm
selection or out-of-domain branch occurs. -/
def next (f : Tuple r K) (hr : r < K) (v : Scalar) : Fin K :=
  (remainder f).orderEmbOfFin (card_remainder f)
    (rank (K - r) (Nat.sub_pos_of_lt hr) v)

theorem next_mem_remainder (f : Tuple r K) (hr : r < K) (v : Scalar) :
    next f hr v ∈ remainder f :=
  Finset.orderEmbOfFin_mem _ _ _

/-- Append exactly the selected arm. -/
def append (f : Tuple r K) (hr : r < K) (v : Scalar) : Tuple (r + 1) K :=
  ⟨Fin.snoc f.val (next f hr v), Fin.snoc_injective_of_injective f.property
    ((mem_remainder f _).mp (next_mem_remainder f hr v))⟩

theorem append_castSucc (f : Tuple r K) (hr : r < K) (v : Scalar) (i : Fin r) :
    (append f hr v).val i.castSucc = f.val i := by
  change (@Fin.snoc r (fun _ => Fin K) f.val (next f hr v)) i.castSucc = f.val i
  exact Fin.snoc_castSucc _ _ _

theorem append_last (f : Tuple r K) (hr : r < K) (v : Scalar) :
    (append f hr v).val (Fin.last r) = next f hr v := by
  change (@Fin.snoc r (fun _ => Fin K) f.val (next f hr v)) (Fin.last r) = next f hr v
  exact Fin.snoc_last _ _

/-- The actual finite recursion, starting with the empty tuple and reading
input `r` only at its append step. -/
def buildPrefix (h : m < K) (v : Fin m → Scalar) : (r : ℕ) → r ≤ m → Tuple r K
  | 0, _ => ⟨Fin.elim0, fun i => Fin.elim0 i⟩
  | r + 1, hr => append (buildPrefix h v r (by omega)) (by omega) (v ⟨r, by omega⟩)

theorem prefix_zero (h : m < K) (v : Fin m → Scalar) :
    (buildPrefix h v 0 (Nat.zero_le m)).val = Fin.elim0 := rfl

theorem prefix_succ (h : m < K) (v : Fin m → Scalar) (r : ℕ) (hr : r + 1 ≤ m) :
    buildPrefix h v (r + 1) hr =
      append (buildPrefix h v r (by omega)) (by omega) (v ⟨r, by omega⟩) := rfl

theorem prefix_succ_castSucc (h : m < K) (v : Fin m → Scalar)
    (r : ℕ) (hr : r + 1 ≤ m) (i : Fin r) :
    (buildPrefix h v (r + 1) hr).val i.castSucc =
      (buildPrefix h v r (by omega)).val i := append_castSucc _ _ _ _

theorem prefix_succ_last (h : m < K) (v : Fin m → Scalar)
    (r : ℕ) (hr : r + 1 ≤ m) :
    (buildPrefix h v (r + 1) hr).val (Fin.last r) =
      next (buildPrefix h v r (by omega)) (by omega) (v ⟨r, by omega⟩) :=
  append_last _ _ _

theorem prefix_coherent (h : m < K) (v : Fin m → Scalar)
    {r s : ℕ} (hrs : r ≤ s) (hs : s ≤ m) (i : Fin r) :
    (buildPrefix h v s hs).val (Fin.castLE hrs i) =
      (buildPrefix h v r (hrs.trans hs)).val i := by
  induction s with
  | zero =>
      have : r = 0 := by omega
      subst r
      exact Fin.elim0 i
  | succ s ih =>
      by_cases hrs' : r ≤ s
      · have heq : Fin.castLE hrs i = (Fin.castLE hrs' i).castSucc := rfl
        rw [heq, prefix_succ_castSucc]
        exact ih hrs' (by omega)
      · have : r = s + 1 := by omega
        subst r
        rfl

/-- Restriction of an injective tuple to its first `r` entries. -/
def restrict (f : Tuple m K) (r : ℕ) (hr : r ≤ m) : Tuple r K :=
  ⟨fun i => f.val (Fin.castLE hr i), f.property.comp (Fin.castLE_injective hr)⟩

theorem restrict_self (f : Tuple m K) : restrict f m le_rfl = f := rfl

/-- Cube sampler, separated from the reading of the slice labels. -/
def sampleCube (h : m < K) (v : Fin m → Scalar) : Tuple m K :=
  buildPrefix h v m le_rfl

/-- The only scalar inputs used by the tuple algorithm. -/
def tupleInputs (x : Slice m K) : Fin m → Scalar := fun i => x (Label.tuple i)

/-- Source-domain sampler (`2 ≤ m < K`), factored through its `m` tuple inputs. -/
def sample (_hm : 2 ≤ m) (h : m < K) (x : Slice m K) : Tuple m K :=
  sampleCube h (tupleInputs x)

theorem sample_factorization (hm : 2 ≤ m) (h : m < K) :
    sample hm h = sampleCube h ∘ (tupleInputs : Slice m K → _) := rfl

theorem sample_eq_of_tupleInputs_eq (hm : 2 ≤ m) (h : m < K)
    {x y : Slice m K} (hxy : ∀ i : Fin m, x (Label.tuple i) = y (Label.tuple i)) :
    sample hm h x = sample hm h y :=
  congrArg (sampleCube h) (funext hxy)

theorem sample_injective (hm : 2 ≤ m) (h : m < K) (x : Slice m K) :
    Function.Injective (sample hm h x).val := (sample hm h x).property

theorem sampleCube_prefix (h : m < K) (v : Fin m → Scalar) (r : ℕ) (hr : r ≤ m) :
    restrict (sampleCube h v) r hr = buildPrefix h v r hr := by
  apply Subtype.ext
  funext i
  exact prefix_coherent h v hr le_rfl i

/-- Exact pointwise append equation for the final tuple. -/
theorem sampleCube_apply (h : m < K) (v : Fin m → Scalar) (i : Fin m) :
    (sampleCube h v).val i =
      next (buildPrefix h v i.val (Nat.le_of_lt i.isLt))
        (i.isLt.trans h) (v i) := by
  have hc := prefix_coherent h v (Nat.succ_le_of_lt i.isLt) le_rfl (Fin.last i.val)
  calc
    (sampleCube h v).val i =
        (buildPrefix h v (i.val + 1) (Nat.succ_le_of_lt i.isLt)).val (Fin.last i.val) :=
      hc
    _ = _ := prefix_succ_last h v _ _

theorem sample_prefix (hm : 2 ≤ m) (h : m < K) (x : Slice m K)
    (r : ℕ) (hr : r ≤ m) :
    restrict (sample hm h x) r hr = buildPrefix h (tupleInputs x) r hr :=
  sampleCube_prefix h (tupleInputs x) r hr

/-- The final tuple satisfies the literal source rank rule in the increasing
remainder of its own previous entries. `Fin` indexes rank `1+floor(...)` by
`floor(...)`. This holds everywhere, including interval endpoints. -/
theorem sample_source_equation (hm : 2 ≤ m) (h : m < K) (x : Slice m K) (i : Fin m) :
    (sample hm h x).val i =
      (remainder (restrict (sample hm h x) i.val (Nat.le_of_lt i.isLt))).orderEmbOfFin
        (card_remainder _)
        (rank (K - i.val) (Nat.sub_pos_of_lt (i.isLt.trans h)) (x (Label.tuple i))) := by
  change (sampleCube h (tupleInputs x)).val i =
    next (restrict (sample hm h x) i.val (Nat.le_of_lt i.isLt))
      (i.isLt.trans h) (x (Label.tuple i))
  rw [sampleCube_apply, sample_prefix]
  rfl

theorem sample_mem_remainder (hm : 2 ≤ m) (h : m < K) (x : Slice m K) (i : Fin m) :
    (sample hm h x).val i ∈
      remainder (restrict (sample hm h x) i.val (Nat.le_of_lt i.isLt)) := by
  rw [sample_source_equation]
  exact Finset.orderEmbOfFin_mem _ _ _

/-- A fixed tuple's next entry belongs to its own increasing remainder. -/
theorem fixed_mem_remainder (f : Tuple m K) (i : Fin m) :
    f.val i ∈ remainder (restrict f i.val (Nat.le_of_lt i.isLt)) := by
  rw [mem_remainder]
  rintro ⟨j, hj⟩
  have he := f.property hj
  have hjlt := j.isLt
  have hv := congrArg Fin.val he
  change j.val = i.val at hv
  omega

/-- The unique zero-based increasing-remainder rank of a fixed tuple entry. -/
def tupleRank (f : Tuple m K) (i : Fin m) : Fin (K - i.val) :=
  ((remainder (restrict f i.val (Nat.le_of_lt i.isLt))).orderIsoOfFin
    (card_remainder _)).symm ⟨f.val i, fixed_mem_remainder f i⟩

theorem next_eq_iff_rank (f : Tuple r K) (hr : r < K) (v : Scalar)
    (a : {a // a ∈ remainder f}) :
    next f hr v = a.val ↔ rank (K - r) (Nat.sub_pos_of_lt hr) v =
      ((remainder f).orderIsoOfFin (card_remainder f)).symm a := by
  change ((remainder f).orderIsoOfFin (card_remainder f)
    (rank (K - r) (Nat.sub_pos_of_lt hr) v)).val = a.val ↔ _
  rw [Subtype.coe_inj]
  exact (OrderIso.eq_symm_apply _).symm

theorem next_fixed_eq_iff (h : m < K) (f : Tuple m K) (i : Fin m) (v : Scalar) :
    next (restrict f i.val (Nat.le_of_lt i.isLt)) (i.isLt.trans h) v = f.val i ↔
      rank (K - i.val) (Nat.sub_pos_of_lt (i.isLt.trans h)) v = tupleRank f i :=
  next_eq_iff_rank _ _ _ ⟨f.val i, fixed_mem_remainder f i⟩

/-- All rank tests of a fixed tuple are necessary and sufficient, pointwise. -/
theorem sampleCube_eq_iff_ranks (h : m < K) (v : Fin m → Scalar) (f : Tuple m K) :
    sampleCube h v = f ↔ ∀ i : Fin m,
      rank (K - i.val) (Nat.sub_pos_of_lt (i.isLt.trans h)) (v i) = tupleRank f i := by
  constructor
  · intro he i
    apply (next_fixed_eq_iff h f i (v i)).mp
    have hp : buildPrefix h v i.val (Nat.le_of_lt i.isLt) =
        restrict f i.val (Nat.le_of_lt i.isLt) := by
      rw [← sampleCube_prefix, he]
    rw [← hp, ← sampleCube_apply, he]
  · intro hranks
    have hp : ∀ (r : ℕ) (hr : r ≤ m),
        buildPrefix h v r hr = restrict f r hr := by
      intro r
      induction r with
      | zero =>
          intro hr
          apply Subtype.ext
          funext i
          exact Fin.elim0 i
      | succ r ih =>
          intro hr
          apply Subtype.ext
          funext j
          induction j using Fin.lastCases with
          | cast j =>
              rw [prefix_succ_castSucc, ih (by omega)]
              rfl
          | last =>
              rw [prefix_succ_last, ih (by omega)]
              exact (next_fixed_eq_iff h f ⟨r, by omega⟩ _).mpr (hranks ⟨r, by omega⟩)
    exact (hp m le_rfl).trans (restrict_self f)

/-- Half-open scalar rank interval, including its lower endpoint. -/
def rankCell (n : ℕ) (i : Fin n) : Set Scalar :=
  Subtype.val ⁻¹' Ico ((i.val : ℝ) / n) (((i.val : ℝ) + 1) / n)

theorem measurableSet_rankCell (n : ℕ) (i : Fin n) :
    MeasurableSet (rankCell n i) := measurableSet_Ico.preimage measurable_subtype_coe

theorem rank_interval_subset (n : ℕ) (hn : 0 < n) (i : Fin n) :
    Ico ((i.val : ℝ) / n) (((i.val : ℝ) + 1) / n) ⊆ Ico (0 : ℝ) 1 := by
  intro v hv
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hi : (i.val : ℝ) + 1 ≤ n := by exact_mod_cast i.isLt
  exact ⟨(div_nonneg (Nat.cast_nonneg _) hn'.le).trans hv.1,
    hv.2.trans_le ((div_le_one hn').mpr hi)⟩

/-- The length computation for each actual scalar rank interval. -/
theorem scalarLaw_rankCell (n : ℕ) (hn : 0 < n) (i : Fin n) :
    scalarLaw (rankCell n i) = (n : ℝ≥0∞)⁻¹ := by
  change ContinuousCategorical.uniform (rankCell n i) = _
  rw [rankCell, ContinuousCategorical.uniform_preimage_val,
    inter_eq_self_of_subset_left (rank_interval_subset n hn i), Real.volume_Ico]
  have he : ((i.val : ℝ) + 1) / n - (i.val : ℝ) / n = 1 / n := by ring
  rw [he, ENNReal.ofReal_div_of_pos (Nat.cast_pos.mpr hn), ENNReal.ofReal_one,
    ENNReal.ofReal_natCast, one_div]

/-- The fibre is exactly a rectangle, including every boundary case. -/
theorem sampleCube_preimage_singleton (h : m < K) (f : Tuple m K) :
    sampleCube h ⁻¹' {f} =
      Set.univ.pi (fun i : Fin m => rankCell (K - i.val) (tupleRank f i)) := by
  ext v
  simp only [mem_preimage, mem_singleton_iff, Set.mem_univ_pi, rankCell, mem_Ico]
  rw [sampleCube_eq_iff_ranks]
  exact forall_congr' (fun i => rank_eq_iff _ _ _ _)

/-- The same rectangle characterization on the integrated slice, explicitly
factored through the reserved tuple labels. -/
theorem sample_preimage_singleton (hm : 2 ≤ m) (h : m < K) (f : Tuple m K) :
    sample hm h ⁻¹' {f} = tupleInputs ⁻¹'
      Set.univ.pi (fun i : Fin m => rankCell (K - i.val) (tupleRank f i)) := by
  rw [← sampleCube_preimage_singleton h f]
  rfl

theorem measurable_sampleCube (h : m < K) : Measurable (sampleCube h) := by
  apply measurable_to_countable'
  intro f
  rw [sampleCube_preimage_singleton]
  exact MeasurableSet.univ_pi (fun i => measurableSet_rankCell _ _)

theorem measurable_tupleInputs (m K : ℕ) :
    Measurable (tupleInputs : Slice m K → Fin m → Scalar) :=
  measurable_pi_iff.mpr (fun i => measurable_pi_apply (Label.tuple i))

theorem measurable_sample (hm : 2 ≤ m) (h : m < K) : Measurable (sample hm h) :=
  (measurable_sampleCube h).comp (measurable_tupleInputs m K)

/-- The tuple-coordinate vector has the product scalar law, using only the
integrated slice law and the disjoint tuple labels. -/
theorem map_tupleInputs (m K : ℕ) :
    (sliceLaw m K).map tupleInputs = Measure.pi (fun _ : Fin m => scalarLaw) := by
  have hinj : Function.Injective (Label.tuple : Fin m → Label m K) := by
    intro i j hij
    exact Sum.inl_injective (Sum.inr_injective hij)
  have hind := (iIndepFun_coordinate m K).precomp hinj
  have hmap := hind.map_fun_eq_pi_map
    (fun i => (measurable_coordinate (Label.tuple i)).aemeasurable)
  change (sliceLaw m K).map tupleInputs =
    Measure.pi (fun i : Fin m => (sliceLaw m K).map (coordinate (Label.tuple i))) at hmap
  simpa only [map_coordinate] using hmap

theorem cube_sampleCube_singleton (h : m < K) (f : Tuple m K) :
    (Measure.pi (fun _ : Fin m => scalarLaw)) (sampleCube h ⁻¹' {f}) =
      ∏ i : Fin m, ((K - i.val : ℕ) : ℝ≥0∞)⁻¹ := by
  rw [sampleCube_preimage_singleton, Measure.pi_pi]
  exact Finset.prod_congr rfl (fun i _ => scalarLaw_rankCell _
    (Nat.sub_pos_of_lt (i.isLt.trans h)) _)

/-- The finite falling factorial is exactly the displayed product. -/
theorem fallingFactorial_eq_prod (m K : ℕ) :
    K.descFactorial m = ∏ i : Fin m, (K - i.val) := by
  rw [Nat.descFactorial_eq_prod_range, Finset.prod_range]

/-- Genuine injective tuples have the falling-factorial cardinality. -/
theorem card_tuple (m K : ℕ) :
    Fintype.card (Tuple m K) = K.descFactorial m := by
  classical
  let e : Tuple m K ≃ (Fin m ↪ Fin K) :=
    { toFun := fun f => ⟨f.val, f.property⟩
      invFun := fun f => ⟨f, f.injective⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e, Fintype.card_embedding_eq, Fintype.card_fin,
    Fintype.card_fin]

theorem fallingFactorial_pos (h : m < K) : 0 < K.descFactorial m :=
  Nat.descFactorial_pos.mpr h.le

theorem inverse_product_eq (m K : ℕ) :
    (∏ i : Fin m, ((K - i.val : ℕ) : ℝ≥0∞)⁻¹) =
      (K.descFactorial m : ℝ≥0∞)⁻¹ := by
  rw [← ENNReal.prod_inv_distrib (fun _ _ _ _ _ => Or.inr (ENNReal.natCast_ne_top _))]
  congr 1
  rw [fallingFactorial_eq_prod, Nat.cast_prod]

/-- Exact atom law on the tuple cube, derived from rectangle lengths. -/
theorem cube_sampleCube_mass (h : m < K) (f : Tuple m K) :
    (Measure.pi (fun _ : Fin m => scalarLaw)) (sampleCube h ⁻¹' {f}) =
      (K.descFactorial m : ℝ≥0∞)⁻¹ := by
  rw [cube_sampleCube_singleton, inverse_product_eq]

open scoped Classical in
/-- Normalization is proved from the cardinality, rather than assumed. -/
theorem tuple_mass_sum (h : m < K) :
    (∑ _f : Tuple m K, (K.descFactorial m : ℝ≥0∞)⁻¹) = 1 := by
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_tuple]
  exact ENNReal.mul_inv_cancel (by exact_mod_cast (fallingFactorial_pos h).ne')
    (ENNReal.natCast_ne_top _)

open scoped Classical in
/-- Uniform Mathlib PMF on the genuine injective-tuple subtype. Its mass and
normalization have been computed, without assuming a uniform sampler law. -/
def uniformTuplePMF (h : m < K) : PMF (Tuple m K) :=
  PMF.ofFintype (fun _ => (K.descFactorial m : ℝ≥0∞)⁻¹) (tuple_mass_sum h)

theorem uniformTuplePMF_apply (h : m < K) (f : Tuple m K) :
    uniformTuplePMF h f = (K.descFactorial m : ℝ≥0∞)⁻¹ := rfl

/-- The complete cube pushforward law, on the actual injective-tuple carrier. -/
theorem cube_map_sampleCube (h : m < K) :
    (Measure.pi (fun _ : Fin m => scalarLaw)).map (sampleCube h) =
      (uniformTuplePMF h).toMeasure := by
  apply Measure.ext_of_singleton
  intro f
  rw [Measure.map_apply (measurable_sampleCube h) (measurableSet_singleton f),
    cube_sampleCube_mass, PMF.toMeasure_apply_singleton _ f (measurableSet_singleton f),
    uniformTuplePMF_apply]

/-- The exact source slice law of the constructed sampler. -/
theorem map_sample (hm : 2 ≤ m) (h : m < K) :
    (sliceLaw m K).map (sample hm h) = (uniformTuplePMF h).toMeasure := by
  calc
    _ = ((sliceLaw m K).map tupleInputs).map (sampleCube h) :=
      (Measure.map_map (measurable_sampleCube h) (measurable_tupleInputs m K)).symm
    _ = _ := by rw [map_tupleInputs, cube_map_sampleCube]

/-- Every fixed injective tuple has exactly probability
`1/[K(K-1)...(K-m+1)]`, under the integrated continuous slice law. -/
theorem sample_singleton (hm : 2 ≤ m) (h : m < K) (f : Tuple m K) :
    (sliceLaw m K) (sample hm h ⁻¹' {f}) = (K.descFactorial m : ℝ≥0∞)⁻¹ := by
  rw [← Measure.map_apply (measurable_sample hm h) (measurableSet_singleton f),
    map_sample, PMF.toMeasure_apply_singleton _ f (measurableSet_singleton f),
    uniformTuplePMF_apply]

theorem sample_singleton_pos (hm : 2 ≤ m) (h : m < K) (f : Tuple m K) :
    0 < (sliceLaw m K) (sample hm h ⁻¹' {f}) := by
  rw [sample_singleton]
  exact ENNReal.inv_pos.mpr (ENNReal.natCast_ne_top _)

end Bandits.Support.OrderedTupleSampler
