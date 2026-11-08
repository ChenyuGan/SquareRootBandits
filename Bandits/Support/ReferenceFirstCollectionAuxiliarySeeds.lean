/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionSamplerCall

/-!
# Independent auxiliary coordinates on an actual collection-call cell

Sources: `sources/zip4/manuscript/06_interruptions.tex:376-423`,
`sources/zip4/manuscript/04_slow_fast_learner.tex:176-180,206-208`, and
`sources/zip4/manuscript/07_public_setup.tex:123-164`.

The source factor below is exactly the existing physical `SourceInput` and its
`sourceInputLaw`, retaining all rows, arrays, and the original private index
`J`. The second factor consists only of analytical independent scalar
coordinates. On the actual first-call `(u,t)` event, restriction to the
specified trigger-refresh and `[u,t)` subarray has the unnormalized joint
product law. This records independence on actual cells; it does not assert a
logical refresh law, score path, filtration, or assignment coupling.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions

namespace Bandits.Support.ReferenceFirstCollectionAuxiliarySeeds

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev SourceInput (p : Parameters) := BootstrapPrivateRoundStreams.SourceInput p
abbrev Rewards (p : Parameters) := ActualInitializationPhysicalStep.GridRewardTable p
abbrev Scalar := ContinuousControlSlice.Scalar
abbrev Coordinate (p : Parameters) := Fin p.T × Fin 2
abbrev AuxiliaryArray (p : Parameters) := Coordinate p → Scalar

variable {p : Parameters}

/-- The literal label/time predicate for the seed subarray attached to a
physical cutoff `u` and collection calendar coordinate `t`. -/
def auxiliaryCellIndexPredicate (u t : Fin p.T) (q : Coordinate p) : Prop :=
  (q.2 = 1 ∧ q.1.val + 1 = u.val) ∨
    (u.val ≤ q.1.val ∧ q.1.val < t.val)

/-- The finite subtype of proposal and refresh coordinates used on one cell. -/
abbrev AuxiliaryCellIndex (u t : Fin p.T) :=
  {q : Coordinate p // auxiliaryCellIndexPredicate u t q}

/-- The actual first-call event after forgetting its continuous parameter. -/
def actualCollectionCallCell (rate : RateInput p) (rewards : Rewards p)
    (C_star C_h : ℝ) (u t : Fin p.T) : Set (SourceInput p) :=
  {source | (ReferenceFirstCollectionSamplerCall.firstCollectionCall
    rate rewards C_star C_h source).map (fun c => (c.1, c.2.1)) = some (u, t)}

/-- The actual event that no later collection sampler is called in the suffix. -/
def noCollectionCallEvent (rate : RateInput p) (rewards : Rewards p)
    (C_star C_h : ℝ) : Set (SourceInput p) :=
  {source | ReferenceFirstCollectionSamplerCall.firstCollectionCall
    rate rewards C_star C_h source = none}

/-- The full analytical array law, with independent uniform `[0,1)` entries
at every calendar and both labels. These coordinates do not alter the physical
source or any player's randomness. -/
def auxiliaryUniformLaw (p : Parameters) : Measure (AuxiliaryArray p) :=
  Measure.pi (fun _ : Coordinate p => ContinuousControlSlice.scalarLaw)

/-- The original physical source law paired with a separate analytical array. -/
def auxiliarySourceLaw (p : Parameters) : Measure (SourceInput p × AuxiliaryArray p) :=
  (BootstrapPrivateRoundStreams.sourceInputLaw p).prod (auxiliaryUniformLaw p)

/-- The unchanged physical marginal of the analytical enlargement. -/
instance auxiliaryUniformLaw_probability (p : Parameters) :
    IsProbabilityMeasure (auxiliaryUniformLaw p) := by
  change IsProbabilityMeasure
    (Measure.pi (fun _ : Coordinate p => ContinuousControlSlice.scalarLaw))
  infer_instance

theorem auxiliarySourceLaw_isProbabilityMeasure (p : Parameters) :
    IsProbabilityMeasure (auxiliarySourceLaw p) := by
  change IsProbabilityMeasure
    ((BootstrapPrivateRoundStreams.sourceInputLaw p).prod (auxiliaryUniformLaw p))
  infer_instance

theorem auxiliarySourceLaw_fst (p : Parameters) :
    (auxiliarySourceLaw p).map Prod.fst = BootstrapPrivateRoundStreams.sourceInputLaw p := by
  exact (measurePreserving_fst (μ := BootstrapPrivateRoundStreams.sourceInputLaw p)
    (ν := auxiliaryUniformLaw p)).map_eq

/-- The actual cell event is Borel on the original source space. -/
theorem measurableSet_actualCollectionCallCell (rate : RateInput p)
    (rewards : Rewards p) (C_star C_h : ℝ) (u t : Fin p.T) :
    MeasurableSet (actualCollectionCallCell rate rewards C_star C_h u t) := by
  exact ReferenceFirstCollectionSamplerCall.measurableSet_firstCollectionCall_cell
    rate rewards C_star C_h u t

/-- Intersecting an actual cell with a measurable source event remains Borel. -/
theorem measurableSet_source_inter_actualCollectionCallCell (rate : RateInput p)
    (rewards : Rewards p) (C_star C_h : ℝ) (u t : Fin p.T)
    (Aset : Set (SourceInput p)) (hA : MeasurableSet Aset) :
    MeasurableSet (Aset ∩ actualCollectionCallCell rate rewards C_star C_h u t) :=
  hA.inter (measurableSet_actualCollectionCallCell rate rewards C_star C_h u t)

/-- The actual no-call event is Borel on the original source space. -/
theorem measurableSet_noCollectionCallEvent (rate : RateInput p)
    (rewards : Rewards p) (C_star C_h : ℝ) :
    MeasurableSet (noCollectionCallEvent rate rewards C_star C_h) := by
  exact ReferenceFirstCollectionSamplerCall.measurableSet_firstCollectionCall_none
    rate rewards C_star C_h

theorem measurableSet_source_inter_noCollectionCallEvent (rate : RateInput p)
    (rewards : Rewards p) (C_star C_h : ℝ)
    (Aset : Set (SourceInput p)) (hA : MeasurableSet Aset) :
    MeasurableSet (Aset ∩ noCollectionCallEvent rate rewards C_star C_h) :=
  hA.inter (measurableSet_noCollectionCallEvent rate rewards C_star C_h)

/-- Literal restriction of the analytical array to the indexed subtype. -/
def auxiliaryBlock (u t : Fin p.T) (array : AuxiliaryArray p) :
    AuxiliaryCellIndex u t → Scalar :=
  fun i => array i.1

/-- The independent finite Pi law on exactly the coordinates in the cell. -/
noncomputable def auxiliaryCellLaw (u t : Fin p.T) :
    Measure (AuxiliaryCellIndex u t → Scalar) := by
  classical
  exact Measure.pi (fun _ : AuxiliaryCellIndex u t => ContinuousControlSlice.scalarLaw)

instance auxiliaryCellLaw_probability (u t : Fin p.T) :
    IsProbabilityMeasure (auxiliaryCellLaw u t) := by
  classical
  change IsProbabilityMeasure
    (Measure.pi (fun _ : AuxiliaryCellIndex u t => ContinuousControlSlice.scalarLaw))
  infer_instance

/-- Restriction to any finite subtype of the original Pi coordinates is
measurable in the existing product Borel structures. -/
theorem measurable_auxiliaryBlock (u t : Fin p.T) :
    Measurable (auxiliaryBlock (p := p) u t) := by
  apply measurable_pi_iff.mpr
  intro i
  exact measurable_pi_apply i.1

/-- The restricted block has the existing finite Pi scalar law, including
when its index subtype is empty. This is the finite Pi-subtype product
decomposition, followed by projection of the independent complementary Pi. -/
theorem auxiliaryUniformLaw_map_auxiliaryBlock (u t : Fin p.T) :
    (auxiliaryUniformLaw p).map (auxiliaryBlock (p := p) u t) = auxiliaryCellLaw u t := by
  classical
  let split : AuxiliaryArray p ≃ᵐ
      (AuxiliaryCellIndex u t → Scalar) ×
        ({q : Coordinate p // ¬ auxiliaryCellIndexPredicate u t q} → Scalar) :=
    MeasurableEquiv.piEquivPiSubtypeProd
      (fun _ : Coordinate p => Scalar) (auxiliaryCellIndexPredicate u t)
  have hsplit : MeasurePreserving split (auxiliaryUniformLaw p)
      ((auxiliaryCellLaw u t).prod
        (Measure.pi (fun _ : {q : Coordinate p // ¬ auxiliaryCellIndexPredicate u t q} =>
          ContinuousControlSlice.scalarLaw))) := by
    simpa only [split, auxiliaryUniformLaw, auxiliaryCellLaw] using
      (measurePreserving_piEquivPiSubtypeProd
      (fun _ : Coordinate p => ContinuousControlSlice.scalarLaw)
      (auxiliaryCellIndexPredicate u t))
  have hprojection : MeasurePreserving Prod.fst
      ((auxiliaryCellLaw u t).prod
        (Measure.pi (fun _ : {q : Coordinate p // ¬ auxiliaryCellIndexPredicate u t q} =>
          ContinuousControlSlice.scalarLaw))) (auxiliaryCellLaw u t) :=
    measurePreserving_fst
  have hblock : auxiliaryBlock (p := p) u t = Prod.fst ∘ split := by
    funext array
    funext i
    rfl
  calc
    (auxiliaryUniformLaw p).map (auxiliaryBlock (p := p) u t) =
        (auxiliaryUniformLaw p).map (Prod.fst ∘ split) := by rw [hblock]
    _ = ((auxiliaryUniformLaw p).map split).map Prod.fst := by
      rw [Measure.map_map measurable_fst split.measurable]
    _ = auxiliaryCellLaw u t := by rw [hsplit.map_eq, hprojection.map_eq]

/-- The first projection of the enlarged law is exactly the original source
law, not a replacement physical law. -/
theorem auxiliarySourceLaw_physical_marginal (p : Parameters) :
    (auxiliarySourceLaw p).map Prod.fst = BootstrapPrivateRoundStreams.sourceInputLaw p :=
  auxiliarySourceLaw_fst p

/-- The actual-cell joint identity, without normalization or a positive-mass
premise. The equality is valid for every source set; the preceding Borel lemma
records the requested measurable-set case. -/
theorem auxiliaryBlock_jointLaw_on_actualCollectionCallCell (rate : RateInput p)
    (rewards : Rewards p) (C_star C_h : ℝ) (u t : Fin p.T)
    (Aset : Set (SourceInput p)) :
    ((auxiliarySourceLaw p).restrict
      ((Aset ∩ actualCollectionCallCell rate rewards C_star C_h u t) ×ˢ Set.univ)).map
        (fun w : SourceInput p × AuxiliaryArray p =>
          (w.1, auxiliaryBlock (p := p) u t w.2)) =
      ((BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
        (Aset ∩ actualCollectionCallCell rate rewards C_star C_h u t)).prod
        (auxiliaryCellLaw u t) := by
  change (((BootstrapPrivateRoundStreams.sourceInputLaw p).prod (auxiliaryUniformLaw p)).restrict
      ((Aset ∩ actualCollectionCallCell rate rewards C_star C_h u t) ×ˢ Set.univ)).map
        (Prod.map id (auxiliaryBlock (p := p) u t)) = _
  rw [← Measure.restrict_prod_eq_prod_univ]
  rw [← Measure.map_prod_map
    ((BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
      (Aset ∩ actualCollectionCallCell rate rewards C_star C_h u t))
    (auxiliaryUniformLaw p) measurable_id (measurable_auxiliaryBlock (p := p) u t)]
  rw [Measure.map_id, auxiliaryUniformLaw_map_auxiliaryBlock]

/-- On the actual no-call event, the entire auxiliary array remains an
independent Pi factor. The identity is unnormalized and needs no positive-mass
assumption; it too holds for every source set. -/
theorem auxiliaryArrayLaw_on_noCollectionCall (rate : RateInput p)
    (rewards : Rewards p) (C_star C_h : ℝ) (Aset : Set (SourceInput p)) :
    (auxiliarySourceLaw p).restrict
      ((Aset ∩ noCollectionCallEvent rate rewards C_star C_h) ×ˢ Set.univ) =
      ((BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
        (Aset ∩ noCollectionCallEvent rate rewards C_star C_h)).prod
        (auxiliaryUniformLaw p) := by
  change ((BootstrapPrivateRoundStreams.sourceInputLaw p).prod (auxiliaryUniformLaw p)).restrict
      ((Aset ∩ noCollectionCallEvent rate rewards C_star C_h) ×ˢ Set.univ) = _
  rw [← Measure.restrict_prod_eq_prod_univ]

end Bandits.Support.ReferenceFirstCollectionAuxiliarySeeds

end
