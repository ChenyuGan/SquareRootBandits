/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.CompletePublicTable
public import Bandits.Support.ContinuousLearningRows
public import Bandits.Support.PublicDiscreteDraws
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Complete-row future coordinates at pre-round stopping times

The existing complete row is reindexed by calendar time without changing its
symbols: at each time it contains the full forward-ID bit vector and the whole
continuous control slice together with every affine coefficient/offset pair.
Finite product splitting then gives the strict-past/future law for arbitrary
independent side input and any stopping-time event measurable from that side
input and strict past. Sources: `sources/zip4/manuscript/07_public_setup.tex:11-25`,
`sources/zip4/manuscript/08_main_theorem.tex:78-83`, and
`sources/zip4/manuscript/06_interruptions.tex:391-426`.

The stopping-time measurability data here is generic. This module does not
identify a protocol history or a launch monitor with a physical chronological
history, and it makes no claim about conditioning on a complete published
output.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.CompletePublicTable
open Bandits.Support.ContinuousLearningRows
open scoped ENNReal

namespace Bandits.Support.CompleteRowStoppingLaw

abbrev Parameters := ConstructorDimensions.Parameters

/-- One calendar entry retains the entire forward-ID vector and one complete
continuous learning/control slice. -/
abbrev CalendarEntry (p : Parameters) :=
  (Fin (BootstrapDimensions.A_id p) → Bool) × ContinuousLearningRows.TimeControl p

/-- The original complete row, reindexed by its actual calendar coordinates. -/
abbrev CalendarArray (p : Parameters) := Fin p.T → CalendarEntry p

/-- The time-`t` law, including every forward bit and every continuous control
and affine sample. -/
def calendarEntryLaw (p : Parameters) : Measure (CalendarEntry p) :=
  (Measure.pi (fun _ : Fin (BootstrapDimensions.A_id p) => forwardBitLaw p)).prod
    (ContinuousLearningRows.timeControlLaw p)

/-- Literal time product of the complete calendar-entry laws. -/
def calendarArrayLaw (p : Parameters) : Measure (CalendarArray p) :=
  Measure.pi (fun _ : Fin p.T => calendarEntryLaw p)

instance calendarEntryLaw_probability (p : Parameters) :
    IsProbabilityMeasure (calendarEntryLaw p) := by
  unfold calendarEntryLaw
  infer_instance

instance calendarArrayLaw_probability (p : Parameters) :
    IsProbabilityMeasure (calendarArrayLaw p) := by
  unfold calendarArrayLaw
  infer_instance

/-- Reindex the original `ForwardRow × LearningRow` by calendar time. -/
def calendarizeRow (p : Parameters)
    (r : CompletePublicTable.CompleteRow p) : CalendarArray p :=
  fun t => (fun u => r.1 u t, r.2 t)

/-- The explicit inverse reassembles the same forward and learning symbols. -/
def uncalendarizeRow (p : Parameters) (x : CalendarArray p) :
    CompletePublicTable.CompleteRow p :=
  ((fun u t => (x t).1 u), fun t => (x t).2)

/-- Explicit measurable equivalence between the existing complete row and
its calendar array. -/
def calendarizeRowEquiv (p : Parameters) :
    CompletePublicTable.CompleteRow p ≃ᵐ CalendarArray p where
  toEquiv :=
    { toFun := calendarizeRow p
      invFun := uncalendarizeRow p
      left_inv := by
        intro r
        cases r with
        | mk f l => rfl
      right_inv := by
        intro x
        funext t
        apply Prod.ext
        · funext u
          rfl
        · rfl }
  measurable_toFun := by
    apply measurable_pi_iff.mpr
    intro t
    apply Measurable.prodMk
    · apply measurable_pi_iff.mpr
      intro u
      exact (measurable_pi_apply t).comp
        ((measurable_pi_apply u).comp measurable_fst)
    · exact (measurable_pi_apply t).comp measurable_snd
  measurable_invFun := by
    apply Measurable.prodMk
    · apply measurable_pi_iff.mpr
      intro u
      apply measurable_pi_iff.mpr
      intro t
      exact (measurable_pi_apply u).comp
        ((measurable_fst.comp (measurable_pi_apply t)))
    · apply measurable_pi_iff.mpr
      intro t
      exact (measurable_snd.comp (measurable_pi_apply t))

/-- The row equivalence sends the existing complete-row probability measure to
the literal product over times of full forward vectors paired with full
continuous controls. -/
theorem measurePreserving_calendarizeRow (p : Parameters) :
    MeasurePreserving (calendarizeRowEquiv p)
      (CompletePublicTable.completeRowMeasure p) (calendarArrayLaw p) := by
  classical
  let forwardTranspose :
      CompletePublicTable.ForwardRow p ≃ᵐ
        (Fin p.T → Fin (BootstrapDimensions.A_id p) → Bool) :=
    { toEquiv :=
        { toFun := fun f t u => f u t
          invFun := fun f u t => f t u
          left_inv := by intro f; funext u t; rfl
          right_inv := by intro f; funext t u; rfl }
      measurable_toFun := by
        apply measurable_pi_iff.mpr
        intro t
        apply measurable_pi_iff.mpr
        intro u
        exact (measurable_pi_apply t).comp (measurable_pi_apply u)
      measurable_invFun := by
        apply measurable_pi_iff.mpr
        intro u
        apply measurable_pi_iff.mpr
        intro t
        exact (measurable_pi_apply u).comp (measurable_pi_apply t) }
  have hforward : MeasurePreserving forwardTranspose
      (CompletePublicTable.forwardRowMeasure p)
      (Measure.pi (fun _ : Fin p.T =>
        Measure.pi (fun _ : Fin (BootstrapDimensions.A_id p) => forwardBitLaw p))) := by
    let timeForwardFlatten :
        (Fin p.T → Fin (BootstrapDimensions.A_id p) → Bool) ≃ᵐ
          (Fin p.T × Fin (BootstrapDimensions.A_id p) → Bool) :=
      { toEquiv :=
          { toFun := fun f tu => f tu.1 tu.2
            invFun := fun f t u => f (t, u)
            left_inv := by intro f; funext t u; rfl
            right_inv := by intro f; funext tu; cases tu; rfl }
        measurable_toFun := by
          apply measurable_pi_iff.mpr
          intro tu
          exact (measurable_pi_apply tu.2).comp (measurable_pi_apply tu.1)
        measurable_invFun := by
          apply measurable_pi_iff.mpr
          intro t
          apply measurable_pi_iff.mpr
          intro u
          exact measurable_pi_apply (t, u) }
    have htimeForwardFlatten : MeasurePreserving timeForwardFlatten
        (Measure.pi (fun _ : Fin p.T =>
          Measure.pi (fun _ : Fin (BootstrapDimensions.A_id p) => forwardBitLaw p)))
        (Measure.pi (fun _ : Fin p.T × Fin (BootstrapDimensions.A_id p) => forwardBitLaw p)) := by
      refine ⟨timeForwardFlatten.measurable, ?_⟩
      symm
      apply Measure.pi_eq
      intro s hs
      rw [Measure.map_apply_of_aemeasurable timeForwardFlatten.measurable.aemeasurable
        (MeasurableSet.univ_pi hs)]
      have hpre : timeForwardFlatten ⁻¹' Set.univ.pi s =
          Set.univ.pi (fun t => Set.univ.pi (fun u => s (t, u))) := by
        ext f
        simp [timeForwardFlatten]
      rw [hpre]
      simp_rw [Measure.pi_pi]
      exact (Fintype.prod_prod_type'
        (fun t u => forwardBitLaw p (s (t, u)))).symm
    have hsourceFlatten : MeasurePreserving (CompletePublicTable.forwardRowFlatten p)
        (CompletePublicTable.forwardRowMeasure p)
        (Measure.pi (fun _ : Fin (BootstrapDimensions.A_id p) × Fin p.T =>
          forwardBitLaw p)) :=
      ⟨CompletePublicTable.measurable_forwardRowFlatten p,
        CompletePublicTable.forwardRow_flatten_law p⟩
    have hindex : MeasurePreserving
        (MeasurableEquiv.piCongrLeft
          (fun _ : Fin (BootstrapDimensions.A_id p) × Fin p.T => Bool)
          (Equiv.prodComm (Fin p.T) (Fin (BootstrapDimensions.A_id p)) :
            Fin p.T × Fin (BootstrapDimensions.A_id p) ≃
            Fin (BootstrapDimensions.A_id p) × Fin p.T))
        (Measure.pi (fun _ : Fin p.T × Fin (BootstrapDimensions.A_id p) => forwardBitLaw p))
        (Measure.pi (fun _ : Fin (BootstrapDimensions.A_id p) × Fin p.T => forwardBitLaw p)) := by
      exact measurePreserving_piCongrLeft
        (fun _ : Fin (BootstrapDimensions.A_id p) × Fin p.T => forwardBitLaw p)
        (Equiv.prodComm (Fin p.T) (Fin (BootstrapDimensions.A_id p)) :
          Fin p.T × Fin (BootstrapDimensions.A_id p) ≃
          Fin (BootstrapDimensions.A_id p) × Fin p.T)
    have hcomposed := htimeForwardFlatten.symm.comp (hindex.symm.comp hsourceFlatten)
    convert hcomposed using 1
    funext f t u
    rfl
  have hprod : MeasurePreserving
      (Prod.map forwardTranspose id)
      (CompletePublicTable.completeRowMeasure p)
      ((Measure.pi (fun _ : Fin p.T =>
          Measure.pi (fun _ : Fin (BootstrapDimensions.A_id p) => forwardBitLaw p))).prod
        (ContinuousLearningRows.learningRowLaw p)) := by
    change MeasurePreserving (Prod.map forwardTranspose id)
      ((CompletePublicTable.forwardRowMeasure p).prod
        (ContinuousLearningRows.learningRowLaw p)) _
    exact hforward.prod (MeasurePreserving.id _)
  have hcalendar : MeasurePreserving
      (MeasurableEquiv.arrowProdEquivProdArrow
        (Fin (BootstrapDimensions.A_id p) → Bool)
        (ContinuousLearningRows.TimeControl p) (Fin p.T)).symm
      (((Measure.pi (fun _ : Fin p.T =>
          Measure.pi (fun _ : Fin (BootstrapDimensions.A_id p) => forwardBitLaw p))).prod
        (ContinuousLearningRows.learningRowLaw p)))
      (calendarArrayLaw p) := by
    change MeasurePreserving
      (MeasurableEquiv.arrowProdEquivProdArrow
        (Fin (BootstrapDimensions.A_id p) → Bool)
        (ContinuousLearningRows.TimeControl p) (Fin p.T)).symm
      ((Measure.pi (fun _ : Fin p.T =>
          Measure.pi (fun _ : Fin (BootstrapDimensions.A_id p) => forwardBitLaw p))).prod
        (Measure.pi (fun _ : Fin p.T => ContinuousLearningRows.timeControlLaw p)))
      (Measure.pi (fun _ : Fin p.T => calendarEntryLaw p))
    exact (measurePreserving_arrowProdEquivProdArrow
      (Fin (BootstrapDimensions.A_id p) → Bool)
      (ContinuousLearningRows.TimeControl p) (Fin p.T)
      (fun _ => Measure.pi (fun _ : Fin (BootstrapDimensions.A_id p) => forwardBitLaw p))
      (fun _ => ContinuousLearningRows.timeControlLaw p)).symm
  have hcomp := hcalendar.comp hprod
  convert hcomp using 1
  funext r t
  apply Prod.ext
  · funext u
    rfl
  · rfl

/-- Calendar indices strictly before stopping index `σ`. -/
abbrev PastIndex (p : Parameters) (σ : Fin (p.T + 1)) :=
  {s : Fin p.T // s.val < σ.val}

/-- Calendar indices at or after stopping index `σ`; at `σ = T` this subtype
is genuinely empty. -/
abbrev FutureIndex (p : Parameters) (σ : Fin (p.T + 1)) :=
  {s : Fin p.T // ¬ s.val < σ.val}

/-- Initial pre-round index, before calendar round zero. -/
def initialStoppingIndex (p : Parameters) : Fin (p.T + 1) := 0

/-- The no-launch sentinel at the horizon. -/
def horizonStoppingIndex (p : Parameters) : Fin (p.T + 1) :=
  ⟨p.T, Nat.lt_succ_self p.T⟩

/-- The complement subtype is exactly the non-strict future interval. -/
theorem futureIndex_ge (p : Parameters) (σ : Fin (p.T + 1))
    (s : FutureIndex p σ) : σ.val ≤ s.val := by
  dsimp [FutureIndex] at s
  omega

/-- Membership in the future subtype is equivalent to the source interval
condition `σ ≤ s`. -/
theorem futureIndex_iff (p : Parameters) (σ : Fin (p.T + 1)) (s : Fin p.T) :
    (∃ i : FutureIndex p σ, i.1 = s) ↔ σ.val ≤ s.val := by
  constructor
  · rintro ⟨i, rfl⟩
    exact futureIndex_ge p σ i
  · intro hs
    exact ⟨⟨s, by omega⟩, rfl⟩

/-- There is no strict past before calendar index zero. -/
theorem pastIndexAtInitial_isEmpty (p : Parameters) :
    IsEmpty (PastIndex p (initialStoppingIndex p)) := by
  refine ⟨fun s => ?_⟩
  have hs := s.2
  simp [initialStoppingIndex] at hs

/-- At the no-launch sentinel `σ = T`, the complete future index is genuinely
empty. -/
theorem futureIndexAtHorizon_isEmpty (p : Parameters) :
    IsEmpty (FutureIndex p (horizonStoppingIndex p)) := by
  refine ⟨fun s => ?_⟩
  have hs := futureIndex_ge p (horizonStoppingIndex p) s
  have hst := s.1.isLt
  simp [horizonStoppingIndex] at hs
  omega

/-- Strict-past calendar coordinates. -/
abbrev PastArray (p : Parameters) (σ : Fin (p.T + 1)) :=
  PastIndex p σ → CalendarEntry p

/-- Whole future calendar vector, including empty future at the no-launch
sentinel `σ = T`. -/
abbrev FutureArray (p : Parameters) (σ : Fin (p.T + 1)) :=
  FutureIndex p σ → CalendarEntry p

/-- The no-launch future vector has a singleton function carrier because its
index set is empty; no fallback future symbol is added. -/
theorem futureArrayAtHorizon_subsingleton (p : Parameters) :
    Subsingleton (FutureArray p (horizonStoppingIndex p)) := by
  have hEmpty := futureIndexAtHorizon_isEmpty p
  exact ⟨fun f g => by
    funext i
    exact False.elim (hEmpty.false i)⟩

/-- Literal strict-past product law. -/
def pastArrayLaw (p : Parameters) (σ : Fin (p.T + 1)) : Measure (PastArray p σ) :=
  Measure.pi (fun _ : PastIndex p σ => calendarEntryLaw p)

/-- Literal full-future product law. -/
def futureArrayLaw (p : Parameters) (σ : Fin (p.T + 1)) : Measure (FutureArray p σ) :=
  Measure.pi (fun _ : FutureIndex p σ => calendarEntryLaw p)

instance pastArrayLaw_probability (p : Parameters) (σ : Fin (p.T + 1)) :
    IsProbabilityMeasure (pastArrayLaw p σ) := by
  unfold pastArrayLaw
  infer_instance

instance futureArrayLaw_probability (p : Parameters) (σ : Fin (p.T + 1)) :
    IsProbabilityMeasure (futureArrayLaw p σ) := by
  unfold futureArrayLaw
  infer_instance

/-- Split an actual calendar vector into its strict past and complete future
using Mathlib's finite dependent-product equivalence. -/
def calendarSplitEquiv (p : Parameters) (σ : Fin (p.T + 1)) :
    CalendarArray p ≃ᵐ PastArray p σ × FutureArray p σ :=
  MeasurableEquiv.piEquivPiSubtypeProd
    (fun _ : Fin p.T => CalendarEntry p) (fun s => s.val < σ.val)

/-- The actual time product splits into the strict-past product times the
complete-future product. The proof also covers either empty subtype. -/
theorem measurePreserving_calendarSplit (p : Parameters) (σ : Fin (p.T + 1)) :
    MeasurePreserving (calendarSplitEquiv p σ) (calendarArrayLaw p)
      ((pastArrayLaw p σ).prod (futureArrayLaw p σ)) := by
  exact measurePreserving_piEquivPiSubtypeProd
    (fun _ : Fin p.T => calendarEntryLaw p) (fun s => s.val < σ.val)

/-- Side input paired with strict-past coordinates. -/
abbrev SidePast (Ω : Type*) (p : Parameters) (σ : Fin (p.T + 1)) :=
  Ω × PastArray p σ

/-- Explicit side/past/future equivalence, with the future kept as its entire
subtype-indexed vector. -/
def sideCalendarSplitEquiv (Ω : Type*) [MeasurableSpace Ω] (p : Parameters)
    (σ : Fin (p.T + 1)) :
    Ω × CalendarArray p ≃ᵐ (SidePast Ω p σ × FutureArray p σ) :=
  (MeasurableEquiv.prodCongr (MeasurableEquiv.refl Ω) (calendarSplitEquiv p σ)).trans
    (MeasurableEquiv.prodAssoc.symm)

/-- The side-input product and the true calendar row push forward by the
explicit equivalence to independent side/past and future product measures. -/
theorem measurePreserving_sideCalendarSplit (Ω : Type*) [MeasurableSpace Ω]
    (ν : Measure Ω) [SFinite ν] (p : Parameters) (σ : Fin (p.T + 1)) :
    MeasurePreserving (sideCalendarSplitEquiv Ω p σ)
      (ν.prod (calendarArrayLaw p))
      ((ν.prod (pastArrayLaw p σ)).prod (futureArrayLaw p σ)) := by
  have hprod := (MeasurePreserving.id ν).prod (measurePreserving_calendarSplit p σ)
  have hassoc :=
    (measurePreserving_prodAssoc ν (pastArrayLaw p σ) (futureArrayLaw p σ)).symm
  convert hassoc.comp hprod using 1
  funext z
  simp [sideCalendarSplitEquiv, MeasurableEquiv.prodCongr]

/-- Explicit measurable equivalence from the original complete row, paired
with independent side input, to side/strict-past and the entire future. -/
def sideCompleteRowSplitEquiv (Ω : Type*) [MeasurableSpace Ω]
    (p : Parameters) (σ : Fin (p.T + 1)) :
    Ω × CompletePublicTable.CompleteRow p ≃ᵐ
      (SidePast Ω p σ × FutureArray p σ) :=
  (MeasurableEquiv.prodCongr (MeasurableEquiv.refl Ω) (calendarizeRowEquiv p)).trans
    (sideCalendarSplitEquiv Ω p σ)

/-- The actual law `ν.prod completeRowMeasure` pushes forward to the literal
product of side input, strict past and full future. -/
theorem measurePreserving_sideCompleteRowSplit (Ω : Type*) [MeasurableSpace Ω]
    (ν : Measure Ω) [SFinite ν] (p : Parameters) (σ : Fin (p.T + 1)) :
    MeasurePreserving (sideCompleteRowSplitEquiv Ω p σ)
      (ν.prod (CompletePublicTable.completeRowMeasure p))
      ((ν.prod (pastArrayLaw p σ)).prod (futureArrayLaw p σ)) := by
  have hrow := (MeasurePreserving.id ν).prod (measurePreserving_calendarizeRow p)
  have hsplit := measurePreserving_sideCalendarSplit Ω ν p σ
  convert hsplit.comp hrow using 1
  funext z
  simp [sideCompleteRowSplitEquiv, sideCalendarSplitEquiv,
    MeasurableEquiv.prodCongr]

/-- Exact factorization for a measurable event in side input and strict past
and a measurable set in the entire future vector. -/
theorem side_past_future_event_factorization
    {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (p : Parameters) (σ : Fin (p.T + 1))
    (A : Set (SidePast Ω p σ)) (B : Set (FutureArray p σ))
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    (ν.prod (CompletePublicTable.completeRowMeasure p))
      ((sideCompleteRowSplitEquiv Ω p σ) ⁻¹' (A ×ˢ B)) =
        (ν.prod (pastArrayLaw p σ)) A * (futureArrayLaw p σ) B := by
  calc
    (ν.prod (CompletePublicTable.completeRowMeasure p))
        ((sideCompleteRowSplitEquiv Ω p σ) ⁻¹' (A ×ˢ B)) =
      ((ν.prod (CompletePublicTable.completeRowMeasure p)).map
        (sideCompleteRowSplitEquiv Ω p σ)) (A ×ˢ B) := by
          rw [Measure.map_apply_of_aemeasurable
            (sideCompleteRowSplitEquiv Ω p σ).measurable.aemeasurable (hA.prod hB)]
    _ = ((ν.prod (pastArrayLaw p σ)).prod (futureArrayLaw p σ)) (A ×ˢ B) := by
      rw [(measurePreserving_sideCompleteRowSplit Ω ν p σ).map_eq]
    _ = (ν.prod (pastArrayLaw p σ)) A * (futureArrayLaw p σ) B := Measure.prod_prod A B

/-- Boolean past-event form of the set factorization. -/
theorem side_past_event_function_factorization
    {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (p : Parameters) (σ : Fin (p.T + 1))
    (event : SidePast Ω p σ → Bool) (hevent : Measurable event)
    (B : Set (FutureArray p σ)) (hB : MeasurableSet B) :
    (ν.prod (CompletePublicTable.completeRowMeasure p))
      {z | event ((sideCompleteRowSplitEquiv Ω p σ) z).1 = true ∧
        (sideCompleteRowSplitEquiv Ω p σ z).2 ∈ B} =
      (ν.prod (pastArrayLaw p σ)) {x | event x = true} * (futureArrayLaw p σ) B := by
  have hA : MeasurableSet {x | event x = true} :=
    (measurableSet_singleton true).preimage hevent
  have hfactor := side_past_future_event_factorization ν p σ
    {x | event x = true} B hA hB
  have hset : {z | event ((sideCompleteRowSplitEquiv Ω p σ z).1) = true ∧
      (sideCompleteRowSplitEquiv Ω p σ z).2 ∈ B} =
      (sideCompleteRowSplitEquiv Ω p σ) ⁻¹'
        ({x | event x = true} ×ˢ B) := by
    ext z
    simp [Set.mem_preimage, Set.mem_prod]
  rw [hset]
  exact hfactor

/-- A generic pre-round stopping time. Its event `{σ = t}` is supplied only as
a measurable function of side input and the strict-past calendar coordinates.
This is an honest measurability input; a chronological protocol producer must
establish it separately. -/
structure PreRoundStoppingTime (Ω : Type*) [MeasurableSpace Ω] (p : Parameters) where
  stop : Ω × CompletePublicTable.CompleteRow p → Fin (p.T + 1)
  eventAt : (σ : Fin (p.T + 1)) → SidePast Ω p σ → Bool
  measurable_eventAt : ∀ σ, Measurable (eventAt σ)
  eventAt_eq : ∀ (σ : Fin (p.T + 1)) (ω : Ω)
    (r : CompletePublicTable.CompleteRow p),
      eventAt σ (ω, (calendarSplitEquiv p σ (calendarizeRow p r)).1) =
        decide (stop (ω, r) = σ)

/-- The event that a generic stopping time equals `σ` is exactly the given
measurable function of side input and strict past. -/
theorem stopping_event_is_strict_past
    {Ω : Type*} [MeasurableSpace Ω] {p : Parameters}
    (τ : PreRoundStoppingTime Ω p) (σ : Fin (p.T + 1)) :
    Measurable (τ.eventAt σ) ∧ ∀ ω r,
      τ.eventAt σ (ω, (calendarSplitEquiv p σ (calendarizeRow p r)).1) =
        decide (τ.stop (ω, r) = σ) :=
  ⟨τ.measurable_eventAt σ, τ.eventAt_eq σ⟩

/-- Bounded measurable functions on side/past are integrable under their
actual probability product law. -/
private theorem integrable_of_bounded_probability
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (f : α → ℝ) (hf : Measurable f) (C : ℝ)
    (hC : ∀ x, ‖f x‖ ≤ C) : Integrable f μ := by
  apply Integrable.of_bound hf.aestronglyMeasurable C
  exact Filter.Eventually.of_forall hC

/-- Product integral factorization for arbitrary bounded measurable past and
future tests, under the original complete-row law with independent side input.
The integrability obligations are derived here from boundedness and the
probability instances. -/
theorem side_past_future_integral_factorization
    {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (p : Parameters) (σ : Fin (p.T + 1))
    (f : SidePast Ω p σ → ℝ) (hf : Measurable f) (Cf : ℝ)
    (hCf : ∀ x, ‖f x‖ ≤ Cf)
    (g : FutureArray p σ → ℝ) (hg : Measurable g) (Cg : ℝ)
    (hCg : ∀ y, ‖g y‖ ≤ Cg) :
    ∫ z, f ((sideCompleteRowSplitEquiv Ω p σ z).1) *
      g ((sideCompleteRowSplitEquiv Ω p σ z).2)
        ∂(ν.prod (CompletePublicTable.completeRowMeasure p)) =
      (∫ x, f x ∂(ν.prod (pastArrayLaw p σ))) *
        ∫ y, g y ∂(futureArrayLaw p σ) := by
  let μPast := ν.prod (pastArrayLaw p σ)
  let μFuture := futureArrayLaw p σ
  have hfint : Integrable f μPast :=
    integrable_of_bounded_probability μPast f hf Cf hCf
  have hgint : Integrable g μFuture :=
    integrable_of_bounded_probability μFuture g hg Cg hCg
  let hsplit := measurePreserving_sideCompleteRowSplit Ω ν p σ
  let H : SidePast Ω p σ × FutureArray p σ → ℝ := fun z => f z.1 * g z.2
  have hH : Measurable H := (hf.comp measurable_fst).mul (hg.comp measurable_snd)
  calc
    ∫ z, f ((sideCompleteRowSplitEquiv Ω p σ z).1) *
        g ((sideCompleteRowSplitEquiv Ω p σ z).2)
        ∂(ν.prod (CompletePublicTable.completeRowMeasure p)) =
      ∫ z, H z ∂(μPast.prod μFuture) := by
        exact hsplit.integral_comp (sideCompleteRowSplitEquiv Ω p σ).measurableEmbedding H
    _ = (∫ x, f x ∂μPast) * ∫ y, g y ∂μFuture := by
      exact integral_prod_mul f g

/-- At each stopping index, multiplying a bounded past test by the stopping
event still factors from every bounded measurable test of the whole future. -/
theorem stopping_event_integral_factorization
    {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (p : Parameters) (τ : PreRoundStoppingTime Ω p) (σ : Fin (p.T + 1))
    (f : SidePast Ω p σ → ℝ) (hf : Measurable f) (Cf : ℝ)
    (hCf : ∀ x, ‖f x‖ ≤ Cf)
    (g : FutureArray p σ → ℝ) (hg : Measurable g) (Cg : ℝ)
    (hCg : ∀ y, ‖g y‖ ≤ Cg) :
    ∫ z, (if τ.stop z = σ then
        f ((sideCompleteRowSplitEquiv Ω p σ z).1) *
          g ((sideCompleteRowSplitEquiv Ω p σ z).2) else 0)
        ∂(ν.prod (CompletePublicTable.completeRowMeasure p)) =
      (∫ x, (if τ.eventAt σ x = true then f x else 0)
        ∂(ν.prod (pastArrayLaw p σ))) * ∫ y, g y ∂(futureArrayLaw p σ) := by
  let fStop : SidePast Ω p σ → ℝ := fun x => if τ.eventAt σ x = true then f x else 0
  have hstopSet : MeasurableSet {x | τ.eventAt σ x = true} :=
    (measurableSet_singleton true).preimage (τ.measurable_eventAt σ)
  have hfStop : Measurable fStop :=
    Measurable.ite hstopSet hf measurable_const
  have hCfStop : ∀ x, ‖fStop x‖ ≤ Cf := by
    intro x
    by_cases hx : τ.eventAt σ x = true
    · simpa [fStop, hx] using hCf x
    · simpa [fStop, hx] using le_trans (norm_nonneg (f x)) (hCf x)
  have hfactor := side_past_future_integral_factorization ν p σ
    fStop hfStop Cf hCfStop g hg Cg hCg
  have hstop : ∀ z, fStop ((sideCompleteRowSplitEquiv Ω p σ z).1) =
      if τ.stop z = σ then f ((sideCompleteRowSplitEquiv Ω p σ z).1) else 0 := by
    intro z
    rcases z with ⟨ω, r⟩
    have heq : τ.eventAt σ ((sideCompleteRowSplitEquiv Ω p σ (ω, r)).1) =
        decide (τ.stop (ω, r) = σ) := by
      change τ.eventAt σ (ω, (calendarSplitEquiv p σ (calendarizeRow p r)).1) = _
      exact τ.eventAt_eq σ ω r
    by_cases h : τ.stop (ω, r) = σ
    · have hevt : τ.eventAt σ ((sideCompleteRowSplitEquiv Ω p σ (ω, r)).1) = true := by
        simpa [h] using heq
      simp [fStop, h, hevt]
    · have hevt : τ.eventAt σ ((sideCompleteRowSplitEquiv Ω p σ (ω, r)).1) ≠ true := by
        rw [heq]
        simp [h]
      simp [fStop, h, hevt]
  calc
    ∫ z, (if τ.stop z = σ then
        f ((sideCompleteRowSplitEquiv Ω p σ z).1) *
          g ((sideCompleteRowSplitEquiv Ω p σ z).2) else 0)
        ∂(ν.prod (CompletePublicTable.completeRowMeasure p)) =
      ∫ z, fStop ((sideCompleteRowSplitEquiv Ω p σ z).1) *
        g ((sideCompleteRowSplitEquiv Ω p σ z).2)
          ∂(ν.prod (CompletePublicTable.completeRowMeasure p)) := by
        apply integral_congr_ae
        filter_upwards [] with z
        rw [hstop]
        by_cases hz : τ.stop z = σ <;> simp [hz]
    _ = (∫ x, fStop x ∂(ν.prod (pastArrayLaw p σ))) *
        ∫ y, g y ∂(futureArrayLaw p σ) := hfactor

/-- Finite sum of the stopping-time pieces, with each term factored at its
own strict-past/future split. The sentinel `σ = T` uses the empty subtype
future from `FutureIndex`; no fallback symbol is introduced. -/
theorem stopping_time_finite_sum
    {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (p : Parameters) (τ : PreRoundStoppingTime Ω p)
    (f : ∀ σ : Fin (p.T + 1), SidePast Ω p σ → ℝ)
    (hf : ∀ σ, Measurable (f σ)) (Cf : ℝ)
    (hCf : ∀ σ x, ‖f σ x‖ ≤ Cf)
    (g : ∀ σ : Fin (p.T + 1), FutureArray p σ → ℝ)
    (hg : ∀ σ, Measurable (g σ)) (Cg : ℝ)
    (hCg : ∀ σ y, ‖g σ y‖ ≤ Cg) :
    ∑ σ : Fin (p.T + 1),
        ∫ z, (if τ.stop z = σ then
          f σ ((sideCompleteRowSplitEquiv Ω p σ z).1) *
            g σ ((sideCompleteRowSplitEquiv Ω p σ z).2) else 0)
          ∂(ν.prod (CompletePublicTable.completeRowMeasure p)) =
      ∑ σ : Fin (p.T + 1),
        (∫ x, (if τ.eventAt σ x = true then f σ x else 0)
          ∂(ν.prod (pastArrayLaw p σ))) *
            ∫ y, g σ y ∂(futureArrayLaw p σ) := by
  apply Finset.sum_congr rfl
  intro σ hσ
  exact stopping_event_integral_factorization ν p τ σ
    (f σ) (hf σ) Cf (hCf σ) (g σ) (hg σ) Cg (hCg σ)

end Bandits.Support.CompleteRowStoppingLaw

end
