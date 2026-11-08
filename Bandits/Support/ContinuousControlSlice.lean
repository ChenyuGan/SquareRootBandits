/-
Copyright (c) 2026 Bandits Lean preparation contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Fintype.Sum
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Probability.Independence.Basic

/-!
# One continuous learning/control slice

The labels and scalar law are literal constructions from
`sources/zip4/manuscript/appendix_b_communication.tex:25-44`. Each label is
present even when its potential call is unread. The carrier is the genuine
cube of functions into `[0,1)`, with the finite product of restricted Lebesgue
measures. No invalid scalar inputs require evaluation.

The joint assignment-vector law supplies the unconditional cube measure used
in `sources/zip4/manuscript/06_interruptions.tex:410-423`. This module constructs
one scalar slice only; it does not assert an adaptive conditional law or the
assignment coupling lemma.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ContinuousControlSlice

open MeasureTheory ProbabilityTheory

/-- The six unindexed label tags. `recorder` is the tag for source `rec`. -/
inductive NamedLabel where
  | slot
  | sel
  | recorder
  | fast
  | thin
  | prop
  deriving DecidableEq

instance : Fintype NamedLabel where
  elems := {.slot, .sel, .recorder, .fast, .thin, .prop}
  complete c := by cases c <;> simp

/-- The disjoint scalar labels of Appendix B, lines 25-44: six named labels,
tuple and pilot labels indexed by the players, and `K+1` assignment labels. -/
abbrev Label (m K : ℕ) := NamedLabel ⊕ (Fin m ⊕ (Fin m ⊕ Fin (K + 1)))

/-- Appendix B, line 38: a single calendar slice has `2m+K+7` scalars. -/
theorem card_label (m K : ℕ) : Fintype.card (Label m K) = 2 * m + K + 7 := by
  have hnamed : Fintype.card NamedLabel = 6 := by decide
  simp only [Label, Fintype.card_sum, Fintype.card_fin, hnamed]
  omega

namespace Label

/-- Source label `slot`. -/
def slot {m K : ℕ} : Label m K := Sum.inl NamedLabel.slot
/-- Source label `sel`. -/
def sel {m K : ℕ} : Label m K := Sum.inl NamedLabel.sel
/-- Source label `rec`. -/
def rec {m K : ℕ} : Label m K := Sum.inl NamedLabel.recorder
/-- Source label `fast`. -/
def fast {m K : ℕ} : Label m K := Sum.inl NamedLabel.fast
/-- Source label `thin`. -/
def thin {m K : ℕ} : Label m K := Sum.inl NamedLabel.thin
/-- Source label `prop`. -/
def prop {m K : ℕ} : Label m K := Sum.inl NamedLabel.prop
/-- Source label `tuple_r`, for the player `r.val ∈ {0,...,m-1}`. -/
def tuple {m K : ℕ} (r : Fin m) : Label m K := Sum.inr (Sum.inl r)
/-- Source label `pilot_r`, for the player `r.val ∈ {0,...,m-1}`. -/
def pilot {m K : ℕ} (r : Fin m) : Label m K := Sum.inr (Sum.inr (Sum.inl r))
/-- Source label `assign_(r.val + 1)`, in source order `1,...,K+1`. -/
def assign {m K : ℕ} (r : Fin (K + 1)) : Label m K :=
  Sum.inr (Sum.inr (Sum.inr r))

theorem assign_injective (m K : ℕ) :
    Function.Injective (assign : Fin (K + 1) → Label m K) := by
  intro r s h
  exact Sum.inr_injective (Sum.inr_injective (Sum.inr_injective h))

end Label

/-- A scalar has exactly the source domain `[0,1)`. -/
abbrev Scalar := {x : ℝ // 0 ≤ x ∧ x < 1}

/-- Lebesgue measure transported to its measurable subtype `[0,1)`. The
interval has length one, so no normalization factor is needed. -/
def scalarLaw : Measure Scalar :=
  (volume : Measure ℝ).comap Subtype.val

theorem scalarLaw_apply (s : Set Scalar) :
    scalarLaw s = (volume : Measure ℝ) (Subtype.val '' s) :=
  comap_subtype_coe_apply measurableSet_Ico volume s

instance scalarLaw_probability : IsProbabilityMeasure scalarLaw where
  measure_univ := by
    rw [scalarLaw_apply, Set.image_univ, Subtype.range_coe_subtype]
    exact (Real.volume_Ico.trans (by simp only [sub_zero, ENNReal.ofReal_one]))

/-- The subtype law is exactly restricted Lebesgue, including the open upper
endpoint. This is an equality of measures, not merely an almost-sure claim. -/
theorem scalarLaw_map_val :
    scalarLaw.map (Subtype.val : Scalar → ℝ) = volume.restrict (Set.Ico 0 1) :=
  map_comap_subtype_coe measurableSet_Ico volume

theorem measurePreserving_scalar_val :
    MeasurePreserving (Subtype.val : Scalar → ℝ) scalarLaw
      (volume.restrict (Set.Ico 0 1)) :=
  ⟨measurable_subtype_coe, scalarLaw_map_val⟩

/-- The complete scalar slice, with a coordinate for every potential call. -/
abbrev Slice (m K : ℕ) := Label m K → Scalar

/-- Every scalar label is sampled independently with the continuous uniform
law. No reading or branch predicate is involved in this product. -/
def sliceLaw (m K : ℕ) : Measure (Slice m K) :=
  Measure.pi (fun _ : Label m K => scalarLaw)

instance sliceLaw_probability (m K : ℕ) : IsProbabilityMeasure (sliceLaw m K) := by
  change IsProbabilityMeasure (Measure.pi (fun _ : Label m K => scalarLaw))
  infer_instance

/-- Read a valid scalar at one fixed label. -/
def coordinate {m K : ℕ} (c : Label m K) (x : Slice m K) : Scalar := x c

theorem measurable_coordinate {m K : ℕ} (c : Label m K) :
    Measurable (coordinate c) :=
  measurable_pi_apply c

theorem measurePreserving_coordinate {m K : ℕ} (c : Label m K) :
    MeasurePreserving (coordinate c) (sliceLaw m K) scalarLaw :=
  measurePreserving_eval (fun _ : Label m K => scalarLaw) c

theorem map_coordinate {m K : ℕ} (c : Label m K) :
    (sliceLaw m K).map (coordinate c) = scalarLaw :=
  (measurePreserving_coordinate c).map_eq

/-- The real value of a coordinate; the subtype proof supplies both endpoints. -/
def realCoordinate {m K : ℕ} (c : Label m K) (x : Slice m K) : ℝ :=
  (coordinate c x).val

theorem realCoordinate_mem_Ico {m K : ℕ} (c : Label m K) (x : Slice m K) :
    realCoordinate c x ∈ Set.Ico (0 : ℝ) 1 :=
  (coordinate c x).property

theorem measurePreserving_realCoordinate {m K : ℕ} (c : Label m K) :
    MeasurePreserving (realCoordinate c) (sliceLaw m K)
      (volume.restrict (Set.Ico 0 1)) :=
  measurePreserving_scalar_val.comp (measurePreserving_coordinate c)

/-- Exact one-coordinate continuous uniform law, as a measure on the reals. -/
theorem map_realCoordinate {m K : ℕ} (c : Label m K) :
    (sliceLaw m K).map (realCoordinate c) = volume.restrict (Set.Ico 0 1) :=
  (measurePreserving_realCoordinate c).map_eq

/-- All scalar coordinates are jointly independent, including unread ones. -/
theorem iIndepFun_coordinate (m K : ℕ) :
    iIndepFun (fun c : Label m K => coordinate c) (sliceLaw m K) :=
  iIndepFun_pi (fun _ : Label m K => aemeasurable_id)

/-- The actual real-valued scalar inputs are also jointly independent. -/
theorem iIndepFun_realCoordinate (m K : ℕ) :
    iIndepFun (fun c : Label m K => realCoordinate c) (sliceLaw m K) :=
  iIndepFun_pi (fun _ : Label m K => measurable_subtype_coe.aemeasurable)

/-- Assignment inputs in source order: index `r` denotes `assign_(r.val + 1)`.
In particular, index `K` is the orientation input `assign_(K+1)`. -/
def assignmentVector {m K : ℕ} (x : Slice m K) : Fin (K + 1) → Scalar :=
  fun r => x (Label.assign r)

/-- Product Lebesgue probability measure on the genuine assignment cube. -/
def assignmentLaw (K : ℕ) : Measure (Fin (K + 1) → Scalar) :=
  Measure.pi (fun _ : Fin (K + 1) => scalarLaw)

instance assignmentLaw_probability (K : ℕ) : IsProbabilityMeasure (assignmentLaw K) := by
  change IsProbabilityMeasure (Measure.pi (fun _ : Fin (K + 1) => scalarLaw))
  infer_instance

theorem measurable_assignmentVector (m K : ℕ) :
    Measurable (assignmentVector : Slice m K → Fin (K + 1) → Scalar) :=
  measurable_pi_iff.mpr (fun r => measurable_pi_apply (Label.assign r))

/-- The entire assignment vector has the product-uniform law, rather than
only uniform one-dimensional marginals. The injectivity of the constructor
ensures no assignment coordinate is reused. -/
theorem map_assignmentVector (m K : ℕ) :
    (sliceLaw m K).map assignmentVector = assignmentLaw K := by
  have hind : iIndepFun (fun r : Fin (K + 1) => coordinate (Label.assign r))
      (sliceLaw m K) :=
    (iIndepFun_coordinate m K).precomp (Label.assign_injective m K)
  have hmap := hind.map_fun_eq_pi_map
    (fun r => (measurable_coordinate (Label.assign r)).aemeasurable)
  change (sliceLaw m K).map assignmentVector =
    Measure.pi (fun r : Fin (K + 1) =>
      (sliceLaw m K).map (coordinate (Label.assign r))) at hmap
  simpa only [map_coordinate, assignmentLaw] using hmap

theorem measurePreserving_assignmentVector (m K : ℕ) :
    MeasurePreserving (assignmentVector : Slice m K → Fin (K + 1) → Scalar)
      (sliceLaw m K) (assignmentLaw K) :=
  ⟨measurable_assignmentVector m K, map_assignmentVector m K⟩

/-- Forget only the endpoint proofs in an assignment vector. -/
def assignmentValues {K : ℕ} (v : Fin (K + 1) → Scalar) : Fin (K + 1) → ℝ :=
  fun r => (v r).val

/-- As a real-vector measure, the assignment cube is exactly product Lebesgue
restricted to `[0,1)^(K+1)`. -/
theorem assignmentLaw_map_values (K : ℕ) :
    (assignmentLaw K).map assignmentValues =
      (Measure.pi (fun _ : Fin (K + 1) => (volume : Measure ℝ))).restrict
        (Set.univ.pi (fun _ => Set.Ico 0 1)) := by
  have hmap := (measurePreserving_pi
    (fun _ : Fin (K + 1) => scalarLaw)
    (fun _ : Fin (K + 1) => volume.restrict (Set.Ico (0 : ℝ) 1))
    (fun _ => measurePreserving_scalar_val)).map_eq
  rw [Measure.restrict_pi_pi]
  exact hmap

/-- Joint law of all `K+1` physical assignment scalars on the real cube. This
is unconditional; no physical history or adaptive sampler is assumed here. -/
theorem map_assignmentValues (m K : ℕ) :
    (sliceLaw m K).map (fun x => assignmentValues (assignmentVector x)) =
      (Measure.pi (fun _ : Fin (K + 1) => (volume : Measure ℝ))).restrict
        (Set.univ.pi (fun _ => Set.Ico 0 1)) := by
  have hval : Measurable (assignmentValues : (Fin (K + 1) → Scalar) → _) :=
    measurable_pi_iff.mpr
      (fun r => measurable_subtype_coe.comp (measurable_pi_apply r))
  calc
    _ = ((sliceLaw m K).map assignmentVector).map assignmentValues :=
      (Measure.map_map hval (measurable_assignmentVector m K)).symm
    _ = _ := by rw [map_assignmentVector, assignmentLaw_map_values]

end Bandits.Support.ContinuousControlSlice
