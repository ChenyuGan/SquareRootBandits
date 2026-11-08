/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.CompletePublicTable
public import Bandits.Support.IdentificationBlockBalance
public import Bandits.Support.IdentificationColumnBalance
public import Bandits.Support.IdentificationRectangleExclusion

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Simultaneous good identification arrays

The literal simultaneous event for the three accepted identification-array
properties, and its preimage on the existing published-output carrier.
Source: `sources/zip4/manuscript/appendix_b_communication.tex:193-244`,
`sources/zip4/manuscript/07_public_setup.tex:13-25`, and
`sources/zip4/manuscript/08_main_theorem.tex:26-27`.
-/

public section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.CompletePublicTable
open Bandits.Support.IdentificationBlockBalance
open Bandits.Support.IdentificationColumnBalance
open Bandits.Support.IdentificationLocalRowBalance
open Bandits.Support.IdentificationRectangleExclusion

namespace Bandits.Support.IdentificationGoodEvent

/-- The single literal simultaneous good-ID event: column balance, all-one
rectangle exclusion, and block/support interval balance on the same ID array.
The block/support clause includes empty supports and the clipped final block.
Source: `appendix_b_communication.tex:193-203`.-/
@[expose] noncomputable def identificationGoodEvent
    (p : ConstructorDimensions.Parameters) : Set (CompletePublicTable.IDArray p) :=
  {id | columnBalanced p id ∧ idArrayPropertyII p id ∧ propertyIII p id}

/-- The same ID-good event lifted to complete published outputs through the
existing projection, leaving every complete row coordinate in its original
carrier. Source: `07_public_setup.tex:13-25` and
`08_main_theorem.tex:26-27`.-/
@[expose] noncomputable def identificationPublicGoodEvent
    (p : ConstructorDimensions.Parameters) : Set (PublishedOutput p) :=
  publishedID p ⁻¹' identificationGoodEvent p

/-- Membership in the simultaneous event is exactly its three accepted
component properties on one and the same array.-/
theorem mem_identificationGoodEvent_iff_components
    (p : ConstructorDimensions.Parameters) (id : CompletePublicTable.IDArray p) :
    id ∈ identificationGoodEvent p ↔
      columnBalanced p id ∧ idArrayPropertyII p id ∧ propertyIII p id := Iff.rfl

/-- The literal event is measurable on the finite ID-array carrier.-/
theorem measurableSet_identificationGoodEvent (p : ConstructorDimensions.Parameters) :
    MeasurableSet (identificationGoodEvent p) := by
  classical
  exact (Set.toFinite _).measurableSet

/-- The published-output lift is measurable as a preimage under the existing
ID projection.-/
theorem measurableSet_identificationPublicGoodEvent
    (p : ConstructorDimensions.Parameters) :
    MeasurableSet (identificationPublicGoodEvent p) :=
  (measurable_publishedID p) (measurableSet_identificationGoodEvent p)

/-- Membership in the public event is exactly membership of the projected ID
array in the one literal simultaneous event.-/
theorem mem_identificationPublicGoodEvent_iff
    (p : ConstructorDimensions.Parameters) (y : PublishedOutput p) :
    y ∈ identificationPublicGoodEvent p ↔
      publishedID p y ∈ identificationGoodEvent p := Iff.rfl

/-- The public event exposes the same three component characterizations after
the existing ID projection.-/
theorem mem_identificationPublicGoodEvent_iff_components
    (p : ConstructorDimensions.Parameters) (y : PublishedOutput p) :
    y ∈ identificationPublicGoodEvent p ↔
      columnBalanced p (publishedID p y) ∧
        idArrayPropertyII p (publishedID p y) ∧
        propertyIII p (publishedID p y) := by
  rw [mem_identificationPublicGoodEvent_iff,
    mem_identificationGoodEvent_iff_components]

/-- Every ID column and either bit has at least one third of the ID labels on
any array in the simultaneous event.-/
theorem identificationGoodEvent_column_count
    (p : ConstructorDimensions.Parameters) (id : CompletePublicTable.IDArray p)
    (hgood : id ∈ identificationGoodEvent p) (t : Fin p.T) (e : Bool) :
    (A_id p : ℝ) / 3 ≤
      ((Finset.univ.filter fun u : Fin (A_id p) => id u t = e).card : ℝ) := by
  have hcomponents := (mem_identificationGoodEvent_iff_components p id).mp hgood
  exact hcomponents.1 t e

/-- Every source-size time rectangle has fewer than `L0` all-one ID rows on an
array in the simultaneous event.-/
theorem identificationGoodEvent_rectangle_exclusion
    (p : ConstructorDimensions.Parameters) (id : CompletePublicTable.IDArray p)
    (hgood : id ∈ identificationGoodEvent p) (S : Finset (Fin p.T))
    (hS : S.card = 6 * b_N p) :
    (Finset.univ.filter fun u : Fin (A_id p) =>
      ∀ t ∈ S, id u t = true).card < L0 p := by
  have hcomponents := (mem_identificationGoodEvent_iff_components p id).mp hgood
  exact hcomponents.2.1 S hS

/-- Every actual block and support retains the complete-row source count:
at least three quarters of the ID labels satisfy the local balance predicate
simultaneously over all intervals and bits.-/
theorem identificationGoodEvent_block_support_row_count
    (p : ConstructorDimensions.Parameters) (id : CompletePublicTable.IDArray p)
    (hgood : id ∈ identificationGoodEvent p) (s : Fin (n_boot p))
    (x : BlockSupport p s) :
    (3 * (A_id p : ℝ)) / 4 ≤
      (propertyIIIGoodRowCount p id s x : ℝ) := by
  have hcomponents := (mem_identificationGoodEvent_iff_components p id).mp hgood
  exact hcomponents.2.2 s x

/-- For each interval of an actual block and each bit, the rows in the source
local-balance inequality are at least the same three-quarter threshold. This
also applies to empty supports, empty intervals, and the clipped final block.
-/
theorem identificationGoodEvent_interval_row_count
    (p : ConstructorDimensions.Parameters) (id : CompletePublicTable.IDArray p)
    (hgood : id ∈ identificationGoodEvent p) (s : Fin (n_boot p))
    (x : BlockSupport p s) (a b : BlockEndpoint p s) (hab : a.val ≤ b.val)
    (e : Bool) :
    (3 * (A_id p : ℝ)) / 4 ≤
      ((Finset.univ.filter fun u : Fin (A_id p) =>
        ((localBalanceIDCount (calendarInterval p s a b) x.1 e (id u) : ℕ) : ℝ) ≥
          (localBalanceSupportCount (calendarInterval p s a b) x.1 : ℝ) / 3 -
            8 * (b_N p : ℝ)).card : ℝ) := by
  classical
  have hwhole := identificationGoodEvent_block_support_row_count p id hgood s x
  have hsubset :
      (Finset.univ.filter fun u : Fin (A_id p) =>
        id ∈ localBalanceRowEvent p s x u) ⊆
      (Finset.univ.filter fun u : Fin (A_id p) =>
        ((localBalanceIDCount (calendarInterval p s a b) x.1 e (id u) : ℕ) : ℝ) ≥
          (localBalanceSupportCount (calendarInterval p s a b) x.1 : ℝ) / 3 -
            8 * (b_N p : ℝ)) := by
    intro u hu
    have huEvent : id ∈ localBalanceRowEvent p s x u :=
      (Finset.mem_filter.mp hu).2
    have hrow : localBalanceRowPredicate p s x (id u) := by
      simpa only [localBalanceRowEvent, Set.mem_ofPred_eq] using huEvent
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_univ _
    · exact hrow a b hab e
  have hcard : propertyIIIGoodRowCount p id s x ≤
      (Finset.univ.filter fun u : Fin (A_id p) =>
        ((localBalanceIDCount (calendarInterval p s a b) x.1 e (id u) : ℕ) : ℝ) ≥
          (localBalanceSupportCount (calendarInterval p s a b) x.1 : ℝ) / 3 -
            8 * (b_N p : ℝ)).card := by
    change (Finset.univ.filter fun u : Fin (A_id p) =>
      id ∈ localBalanceRowEvent p s x u).card ≤ _
    exact Finset.card_le_card hsubset
  exact hwhole.trans (by exact_mod_cast hcard)

/-- On the source construction branch, the complement of the simultaneous
ID event has mass at most the sum of its accepted component bounds.-/
theorem identificationGoodEvent_compl_measure_le_sum
    (C_b : ℝ) (p : ConstructorDimensions.Parameters) (hCb : 16 ≤ C_b)
    (hbranch : constructionBranchBound C_b p) :
    (idArrayMeasure p).real (identificationGoodEvent p)ᶜ ≤
      (2 : ℝ) / (N p : ℝ) + (1 / (N p : ℝ)) ^ 2 := by
  let columnFailure : Set (CompletePublicTable.IDArray p) :=
    {id | ¬ columnBalanced p id}
  let rectangleFailure : Set (CompletePublicTable.IDArray p) :=
    {id | ¬ idArrayPropertyII p id}
  let blockFailure : Set (CompletePublicTable.IDArray p) :=
    {id | ¬ propertyIII p id}
  have hsubset : (identificationGoodEvent p)ᶜ ⊆
      columnFailure ∪ (rectangleFailure ∪ blockFailure) := by
    intro id hid
    change ¬ (columnBalanced p id ∧ idArrayPropertyII p id ∧ propertyIII p id) at hid
    by_cases hc : columnBalanced p id
    · by_cases hr : idArrayPropertyII p id
      · have hb : ¬ propertyIII p id := by
          intro hb
          exact hid ⟨hc, hr, hb⟩
        exact Or.inr (Or.inr hb)
      · exact Or.inr (Or.inl hr)
    · exact Or.inl hc
  have hcolumn :=
    columnBalanced_compl_measure_le C_b p hCb hbranch
  have hrectangle := idArrayPropertyII_failure_mass_le p
  have hblock := propertyIII_failure_probability_le C_b p hCb hbranch
  calc
    (idArrayMeasure p).real (identificationGoodEvent p)ᶜ ≤
        (idArrayMeasure p).real (columnFailure ∪ (rectangleFailure ∪ blockFailure)) :=
      measureReal_mono hsubset
    _ ≤ (idArrayMeasure p).real columnFailure +
        (idArrayMeasure p).real (rectangleFailure ∪ blockFailure) :=
      measureReal_union_le _ _
    _ ≤ (idArrayMeasure p).real columnFailure +
        ((idArrayMeasure p).real rectangleFailure +
          (idArrayMeasure p).real blockFailure) := by
      exact add_le_add (le_refl _) (measureReal_union_le _ _)
    _ ≤ (1 / (N p : ℝ)) +
        ((1 / (N p : ℝ)) ^ 2 + 1 / (N p : ℝ)) :=
      add_le_add hcolumn (add_le_add hrectangle hblock)
    _ = (2 : ℝ) / (N p : ℝ) + (1 / (N p : ℝ)) ^ 2 := by ring

/-- Since `N ≥ 1`, the preceding sharp sum is at most `3/N`, the source bound
for the simultaneous identification event.-/
theorem identificationGoodEvent_compl_measure_le
    (C_b : ℝ) (p : ConstructorDimensions.Parameters) (hCb : 16 ≤ C_b)
    (hbranch : constructionBranchBound C_b p) :
    (idArrayMeasure p).real (identificationGoodEvent p)ᶜ ≤
      (3 : ℝ) / (N p : ℝ) := by
  have hsum := identificationGoodEvent_compl_measure_le_sum C_b p hCb hbranch
  have hNpos : 0 < (N p : ℝ) := Nat.cast_pos.mpr (N_pos p)
  have hNge : 1 ≤ (N p : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr (N_pos p))
  have hreciprocal : (1 / (N p : ℝ)) ^ 2 ≤ 1 / (N p : ℝ) := by
    rw [one_div_pow]
    apply (div_le_div_iff₀ (pow_pos hNpos 2) hNpos).2
    nlinarith
  calc
    (idArrayMeasure p).real (identificationGoodEvent p)ᶜ ≤
        (2 : ℝ) / (N p : ℝ) + (1 / (N p : ℝ)) ^ 2 := hsum
    _ ≤ 2 / (N p : ℝ) + 1 / (N p : ℝ) :=
      add_le_add (le_refl _) hreciprocal
    _ = (3 : ℝ) / (N p : ℝ) := by ring

/-- On the source construction branch, the simultaneous ID-good event has
mass at least `1 - 3/N` under the existing ID-array law.-/
theorem identificationGoodEvent_mass_ge
    (C_b : ℝ) (p : ConstructorDimensions.Parameters) (hCb : 16 ≤ C_b)
    (hbranch : constructionBranchBound C_b p) :
    1 - (3 : ℝ) / (N p : ℝ) ≤
      (idArrayMeasure p).real (identificationGoodEvent p) := by
  have hsum :
      (idArrayMeasure p).real (identificationGoodEvent p) +
          (idArrayMeasure p).real (identificationGoodEvent p)ᶜ = 1 := by
    rw [measureReal_add_measureReal_compl
      (measurableSet_identificationGoodEvent p)]
    simp
  have hcompl := identificationGoodEvent_compl_measure_le C_b p hCb hbranch
  linarith

/-- The published-output event has exactly the ID-array event's mass under
the accepted published-output law, by the existing measure-preserving ID
projection. The complete rows remain in the published-output carrier.-/
theorem identificationPublicGoodEvent_mass_eq
    (p : ConstructorDimensions.Parameters) :
    (publishedOutputMeasure p).real (identificationPublicGoodEvent p) =
      (idArrayMeasure p).real (identificationGoodEvent p) := by
  calc
    (publishedOutputMeasure p).real (identificationPublicGoodEvent p) =
        ((publishedOutputMeasure p).map (publishedID p)).real
          (identificationGoodEvent p) := by
            change (publishedOutputMeasure p).real
              (publishedID p ⁻¹' identificationGoodEvent p) = _
            rw [measureReal_def, measureReal_def,
              Measure.map_apply_of_aemeasurable
                (measurable_publishedID p).aemeasurable
                (measurableSet_identificationGoodEvent p)]
    _ = (idArrayMeasure p).real (identificationGoodEvent p) := by
      rw [map_publishedID]

/-- The public lift obeys the same complement-mass bound with the same source
branch inputs.-/
theorem identificationPublicGoodEvent_compl_measure_le
    (C_b : ℝ) (p : ConstructorDimensions.Parameters) (hCb : 16 ≤ C_b)
    (hbranch : constructionBranchBound C_b p) :
    (publishedOutputMeasure p).real (identificationPublicGoodEvent p)ᶜ ≤
      (3 : ℝ) / (N p : ℝ) := by
  have hpre : (identificationPublicGoodEvent p)ᶜ =
      publishedID p ⁻¹' (identificationGoodEvent p)ᶜ := by
    rw [identificationPublicGoodEvent, Set.preimage_compl]
  have hmass :
      (publishedOutputMeasure p).real (identificationPublicGoodEvent p)ᶜ =
        (idArrayMeasure p).real (identificationGoodEvent p)ᶜ := by
    rw [measureReal_def, measureReal_def,
      hpre,
      ← Measure.map_apply_of_aemeasurable
        (measurable_publishedID p).aemeasurable
        (measurableSet_identificationGoodEvent p).compl,
      map_publishedID]
  rw [hmass]
  exact identificationGoodEvent_compl_measure_le C_b p hCb hbranch

/-- The public-output lift retains the same source lower bound `1 - 3/N`.-/
theorem identificationPublicGoodEvent_mass_ge
    (C_b : ℝ) (p : ConstructorDimensions.Parameters) (hCb : 16 ≤ C_b)
    (hbranch : constructionBranchBound C_b p) :
    1 - (3 : ℝ) / (N p : ℝ) ≤
      (publishedOutputMeasure p).real (identificationPublicGoodEvent p) := by
  rw [identificationPublicGoodEvent_mass_eq]
  exact identificationGoodEvent_mass_ge C_b p hCb hbranch

/-- Every ID column and bit count bound is directly available from membership
in the lifted public event.-/
theorem identificationPublicGoodEvent_column_count
    (p : ConstructorDimensions.Parameters) (y : PublishedOutput p)
    (hgood : y ∈ identificationPublicGoodEvent p) (t : Fin p.T) (e : Bool) :
    (A_id p : ℝ) / 3 ≤
      ((Finset.univ.filter fun u : Fin (A_id p) =>
        publishedID p y u t = e).card : ℝ) := by
  exact identificationGoodEvent_column_count p (publishedID p y)
    ((mem_identificationPublicGoodEvent_iff p y).mp hgood) t e

/-- Every source-size all-one rectangle is excluded directly from membership
in the lifted public event.-/
theorem identificationPublicGoodEvent_rectangle_exclusion
    (p : ConstructorDimensions.Parameters) (y : PublishedOutput p)
    (hgood : y ∈ identificationPublicGoodEvent p) (S : Finset (Fin p.T))
    (hS : S.card = 6 * b_N p) :
    (Finset.univ.filter fun u : Fin (A_id p) =>
      ∀ t ∈ S, publishedID p y u t = true).card < L0 p := by
  exact identificationGoodEvent_rectangle_exclusion p (publishedID p y)
    ((mem_identificationPublicGoodEvent_iff p y).mp hgood) S hS

/-- Every actual public block/support retains the source interval-good row
count, including empty supports and the clipped final block.-/
theorem identificationPublicGoodEvent_interval_row_count
    (p : ConstructorDimensions.Parameters) (y : PublishedOutput p)
    (hgood : y ∈ identificationPublicGoodEvent p) (s : Fin (n_boot p))
    (x : BlockSupport p s) (a b : BlockEndpoint p s) (hab : a.val ≤ b.val)
    (e : Bool) :
    (3 * (A_id p : ℝ)) / 4 ≤
      ((Finset.univ.filter fun u : Fin (A_id p) =>
        ((localBalanceIDCount (calendarInterval p s a b) x.1 e
          (publishedID p y u) : ℕ) : ℝ) ≥
            (localBalanceSupportCount (calendarInterval p s a b) x.1 : ℝ) / 3 -
              8 * (b_N p : ℝ)).card : ℝ) := by
  exact identificationGoodEvent_interval_row_count p (publishedID p y)
    ((mem_identificationPublicGoodEvent_iff p y).mp hgood) s x a b hab e

end Bandits.Support.IdentificationGoodEvent

end
