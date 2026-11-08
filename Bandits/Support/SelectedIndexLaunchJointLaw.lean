/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceInitializationIndexMixture
public import Bandits.Support.ReferenceLaunchJointFutureLaw

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Prod

/-!
# The original selected-index launch law before public revelation

For each original coordinator-selected index and source launch index, this
module splits the complete original row family and private point into every
nonselected complete row, the accepted selected-row joint past, and its entire
joint future.  The law remains the literal product of the original extended
private law and the complete-row product law.

Sources: `sources/zip4/manuscript/07_public_setup.tex:123-164`,
`sources/zip4/manuscript/appendix_b_communication.tex:786-798`, and
`sources/zip4/manuscript/08_main_theorem.tex:27-42,67-83`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.CompletePublicTable
open Bandits.Support.CompleteRowStoppingLaw
open Bandits.Support.PrivateSourceStreams
open Bandits.Support.ReferenceLaunchJointFutureLaw
open Bandits.Support.ReferenceLaunchPrivateRoundLaw
open scoped ENNReal

namespace Bandits.Support.SelectedIndexLaunchJointLaw

abbrev Parameters := ConstructorDimensions.Parameters
abbrev LaunchIndex (p : Parameters) := ReferenceLaunchJointFutureLaw.LaunchIndex p

private theorem measurable_of_finite_cases {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [Finite β] [MeasurableSingletonClass β]
    [MeasurableSpace γ] (key : α → β) (hkey : Measurable key)
    (branch : β → α → γ) (hbranch : ∀ b, Measurable (branch b)) :
    Measurable (fun x => branch (key x) x) :=
  (measurable_from_prod_countable_right
    (f := fun v : β × α => branch v.1 v.2) hbranch).comp
      (hkey.prodMk measurable_id)

/-- The complete rows other than one fixed sampled index, with their original
labels retained as a subtype of `Fin (M p)`. -/
abbrev NonselectedRows (p : Parameters) (j : Fin (M p)) :=
  {i : Fin (M p) // i ≠ j} → CompleteRow p

local instance nonselectedRowsMeasurableSpace (p : Parameters) (j : Fin (M p)) :
    MeasurableSpace (NonselectedRows p j) := MeasurableSpace.pi

local instance selectedRowSubtypeUnique (p : Parameters) (j : Fin (M p)) :
    Unique {i : Fin (M p) // ¬ i ≠ j} where
  default := ⟨j, by simp⟩
  uniq i := by
    apply Subtype.ext
    exact not_not.mp i.property

/-- The original source carrier, with private labels first as in the source
product law. -/
abbrev OriginalCoordinates (p : Parameters) :=
  ExtendedPrivateCoordinates p × CompleteRows p

/-- Literal nonselected-row product; no conditional or finite replacement
family is introduced. -/
def nonselectedRowsLaw (p : Parameters) (j : Fin (M p)) : Measure (NonselectedRows p j) :=
  Measure.pi (fun _ : {i : Fin (M p) // i ≠ j} => completeRowMeasure p)

instance nonselectedRowsLaw_probability (p : Parameters) (j : Fin (M p)) :
    IsProbabilityMeasure (nonselectedRowsLaw p j) := by
  dsimp [nonselectedRowsLaw]
  infer_instance

/-- The exact original private and complete-family product law. -/
def originalLaw (p : Parameters) : Measure (OriginalCoordinates p) :=
  (extendedPrivateLaw p).prod (completeRowsMeasure p)

instance originalLaw_probability (p : Parameters) : IsProbabilityMeasure (originalLaw p) := by
  dsimp [originalLaw]
  infer_instance

/-- Split a complete family into all nonselected rows and the selected row.
This is the finite dependent-product subtype split followed by the unique
singleton-coordinate equivalence. -/
def selectedRowsEquiv (p : Parameters) (j : Fin (M p)) :
    CompleteRows p ≃ᵐ (NonselectedRows p j × CompleteRow p) := by
  exact (MeasurableEquiv.piEquivPiSubtypeProd (fun _ => CompleteRow p)
      (fun i : Fin (M p) => i ≠ j)).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _)
      (MeasurableEquiv.piUnique (fun _ : {i : Fin (M p) // ¬ i ≠ j} => CompleteRow p)))

/-- Every nonselected family coordinate keeps its source row label. -/
theorem selectedRowsEquiv_nonselected (p : Parameters) (j : Fin (M p))
    (rows : CompleteRows p) (i : {i : Fin (M p) // i ≠ j}) :
    (selectedRowsEquiv p j rows).1 i = rows i.1 := rfl

/-- The selected coordinate is exactly the original row `j`. -/
theorem selectedRowsEquiv_selected (p : Parameters) (j : Fin (M p))
    (rows : CompleteRows p) : (selectedRowsEquiv p j rows).2 = rows j := rfl

/-- The inverse reconstructs every nonselected row at its full original label. -/
theorem selectedRowsEquiv_symm_nonselected (p : Parameters) (j : Fin (M p))
    (rows : NonselectedRows p j × CompleteRow p)
    (i : {i : Fin (M p) // i ≠ j}) :
    ((selectedRowsEquiv p j).symm rows) i.1 = rows.1 i := by
  have h := congrArg (fun x : NonselectedRows p j × CompleteRow p => x.1 i)
    ((selectedRowsEquiv p j).apply_symm_apply rows)
  simpa only [selectedRowsEquiv_nonselected] using h

/-- The inverse reconstructs the selected row at the original index. -/
theorem selectedRowsEquiv_symm_selected (p : Parameters) (j : Fin (M p))
    (rows : NonselectedRows p j × CompleteRow p) :
    ((selectedRowsEquiv p j).symm rows) j = rows.2 := by
  have h := congrArg Prod.snd ((selectedRowsEquiv p j).apply_symm_apply rows)
  simpa only [selectedRowsEquiv_selected] using h

/-- The complete-family split preserves the literal product of complete-row
measures. -/
theorem measurePreserving_selectedRowsEquiv (p : Parameters) (j : Fin (M p)) :
    MeasurePreserving (selectedRowsEquiv p j) (completeRowsMeasure p)
      ((nonselectedRowsLaw p j).prod (completeRowMeasure p)) := by
  have hsplit := measurePreserving_piEquivPiSubtypeProd
    (fun _ : Fin (M p) => completeRowMeasure p) (fun i : Fin (M p) => i ≠ j)
  have hsingle := measurePreserving_piUnique
    (fun _ : {i : Fin (M p) // ¬ i ≠ j} => completeRowMeasure p)
  have htail := (MeasurePreserving.id (nonselectedRowsLaw p j)).prod hsingle
  change MeasurePreserving (selectedRowsEquiv p j) (completeRowsMeasure p)
    ((nonselectedRowsLaw p j).prod (completeRowMeasure p))
  exact htail.comp hsplit

/-- Product reassociation and commutation move the original private point next
to row `j`, leaving every other complete row as a distinct outer factor. -/
def privateRowsReorder (p : Parameters) (j : Fin (M p)) :
    ExtendedPrivateCoordinates p × (NonselectedRows p j × CompleteRow p) ≃ᵐ
      NonselectedRows p j × (ExtendedPrivateCoordinates p × CompleteRow p) :=
  MeasurableEquiv.prodAssoc.symm.trans
    ((MeasurableEquiv.prodCongr MeasurableEquiv.prodComm (MeasurableEquiv.refl _)).trans
      MeasurableEquiv.prodAssoc)

/-- The all-label split from the original private/family point to
`(nonselected rows × joint past) × entire joint future`. -/
def selectedJointSplitEquiv (p : Parameters) (j : Fin (M p)) (σ : LaunchIndex p) :
    OriginalCoordinates p ≃ᵐ
      ((NonselectedRows p j × JointPast p σ) × JointFuture p σ) :=
  ((MeasurableEquiv.prodCongr (MeasurableEquiv.refl _) (selectedRowsEquiv p j)).trans
    (privateRowsReorder p j)).trans
      ((MeasurableEquiv.prodCongr (MeasurableEquiv.refl _)
        (ReferenceLaunchJointFutureLaw.jointSplitEquiv p σ)).trans
          MeasurableEquiv.prodAssoc.symm)

/-- Exact preservation of the original private/family product under the full
selected-index split. -/
theorem measurePreserving_selectedJointSplit (p : Parameters) (j : Fin (M p))
    (σ : LaunchIndex p) :
    MeasurePreserving (selectedJointSplitEquiv p j σ) (originalLaw p)
      (((nonselectedRowsLaw p j).prod (jointPastLaw p σ)).prod (jointFutureLaw p σ)) := by
  let μe := extendedPrivateLaw p
  let μn := nonselectedRowsLaw p j
  let μr := completeRowMeasure p
  let μs := jointPastLaw p σ
  let μf := jointFutureLaw p σ
  have hrows := measurePreserving_selectedRowsEquiv p j
  have hfirst := (MeasurePreserving.id μe).prod hrows
  have hreorder : MeasurePreserving (privateRowsReorder p j)
      (μe.prod (μn.prod μr)) (μn.prod (μe.prod μr)) := by
    have h₁ := (measurePreserving_prodAssoc μe μn μr).symm
    have h₂ := (Measure.measurePreserving_swap (μ := μe) (ν := μn)).prod
      (MeasurePreserving.id μr)
    have h₃ := measurePreserving_prodAssoc μn μe μr
    exact h₃.comp (h₂.comp h₁)
  have hjoint := ReferenceLaunchJointFutureLaw.measurePreserving_jointSplit p σ
  have hwithNonselected := (MeasurePreserving.id μn).prod hjoint
  have hfinal := (measurePreserving_prodAssoc μn μs μf).symm
  have h := hfinal.comp (hwithNonselected.comp (hreorder.comp hfirst))
  change MeasurePreserving (selectedJointSplitEquiv p j σ) (originalLaw p)
    ((μn.prod μs).prod μf)
  convert h using 1 <;> rfl

/-- The map of the original product law is the literal three-factor product. -/
theorem map_selectedJointSplit (p : Parameters) (j : Fin (M p)) (σ : LaunchIndex p) :
    (originalLaw p).map (selectedJointSplitEquiv p j σ) =
      ((nonselectedRowsLaw p j).prod (jointPastLaw p σ)).prod (jointFutureLaw p σ) :=
  (measurePreserving_selectedJointSplit p j σ).map_eq

/-- The selected-row part of the full split is precisely the accepted original
private/row joint split. -/
theorem selectedJointSplit_selectedCoordinates (p : Parameters) (j : Fin (M p))
    (σ : LaunchIndex p) (z : OriginalCoordinates p) :
    ((selectedJointSplitEquiv p j σ z).1.2, (selectedJointSplitEquiv p j σ z).2) =
      ReferenceLaunchJointFutureLaw.jointSplitEquiv p σ (z.1, z.2 j) := rfl

/-- Every nonselected row is projected to its unchanged original label. -/
theorem selectedJointSplit_nonselectedRow (p : Parameters) (j : Fin (M p))
    (σ : LaunchIndex p) (z : OriginalCoordinates p)
    (i : {i : Fin (M p) // i ≠ j}) :
    (selectedJointSplitEquiv p j σ z).1.1 i = z.2 i.1 := rfl

/-- Every complete calendar entry of the selected row at a strict-past label
is retained in the past factor. -/
theorem selectedJointSplit_selectedRow_past (p : Parameters) (j : Fin (M p))
    (σ : LaunchIndex p) (z : OriginalCoordinates p) (t : PastIndex p σ) :
    calendarizeRow p (z.2 j) t.1 =
      (selectedJointSplitEquiv p j σ z).1.2.2 t := rfl

/-- Every complete calendar entry of the selected row at a future label,
including the launch round, is retained in the future factor. -/
theorem selectedJointSplit_selectedRow_future (p : Parameters) (j : Fin (M p))
    (σ : LaunchIndex p) (z : OriginalCoordinates p) (t : FutureIndex p σ) :
    calendarizeRow p (z.2 j) t.1 =
      (selectedJointSplitEquiv p j σ z).2.1 t := rfl

/-- At the source sentinel `T+1`, both strict-future label subtypes are empty;
no calendar entry or player-round scalar is introduced after the horizon. -/
theorem sourceSentinel_futureLabels_empty (p : Parameters) :
    IsEmpty (FutureIndex p (horizonStoppingIndex p)) ∧
      IsEmpty (FuturePlayerRoundLabel p (horizonStoppingIndex p)) :=
  ReferenceLaunchJointFutureLaw.joint_future_labels_at_terminal_isEmpty p

/-- At the source sentinel, the entire joint future is the Dirac law on the
unique pair of empty-index functions. -/
theorem sourceSentinel_jointFutureLaw (p : Parameters) :
    jointFutureLaw p (horizonStoppingIndex p) =
      Measure.dirac (ReferenceLaunchJointFutureLaw.terminalFuture p) :=
  ReferenceLaunchJointFutureLaw.jointFutureLaw_at_terminal_eq_dirac p

/-- Original player-round scalars before the stopping index keep their labels
in the selected joint past. -/
theorem selectedJointSplit_playerRound_past (p : Parameters) (j : Fin (M p))
    (σ : LaunchIndex p) (z : OriginalCoordinates p)
    (label : PastPlayerRoundLabel p σ) :
    z.1.2.1 label.1 =
      (selectedJointSplitEquiv p j σ z).1.2.1.2.1 label := rfl

/-- Original player-round scalars at or after the stopping index, including
all players in the launch round, keep their labels in the joint future. -/
theorem selectedJointSplit_playerRound_future (p : Parameters) (j : Fin (M p))
    (σ : LaunchIndex p) (z : OriginalCoordinates p)
    (label : FuturePlayerRoundLabel p σ) :
    z.1.2.1 label.1 = (selectedJointSplitEquiv p j σ z).2.2 label := by
  rfl

/-- The original coordinator scalar is unchanged in the retained joint past. -/
theorem selectedJointSplit_coordinatorScalar (p : Parameters) (j : Fin (M p))
    (σ : LaunchIndex p) (z : OriginalCoordinates p) :
    (selectedJointSplitEquiv p j σ z).1.2.1.1.2 = z.1.1.2 := by
  rfl

/-- The original block-triple family is unchanged in the retained joint past. -/
theorem selectedJointSplit_blockTriples (p : Parameters) (j : Fin (M p))
    (σ : LaunchIndex p) (z : OriginalCoordinates p) :
    (selectedJointSplitEquiv p j σ z).1.2.1.1.1 = z.1.1.1 := by
  exact congrArg Prod.fst
    (ReferenceLaunchJointFutureLaw.jointSplit_private p σ (z.1, z.2 j))

/-- All coordinator target scalars remain unchanged in the retained joint
past. -/
theorem selectedJointSplit_targets (p : Parameters) (j : Fin (M p))
    (σ : LaunchIndex p) (z : OriginalCoordinates p) :
    (selectedJointSplitEquiv p j σ z).1.2.1.2.2 = z.1.2.2 := by
  rfl

/-- Applying the inverse to a split point recovers the original private point
and every complete row, without changing any source label. -/
theorem selectedJointSplit_inverse_apply (p : Parameters) (j : Fin (M p))
    (σ : LaunchIndex p)
    (z : OriginalCoordinates p) :
    (selectedJointSplitEquiv p j σ).symm (selectedJointSplitEquiv p j σ z) = z :=
  (selectedJointSplitEquiv p j σ).symm_apply_apply z

/-- Every side, past and future label is recovered by the forward map after
reconstructing from a split point. -/
theorem selectedJointSplit_apply_symm (p : Parameters) (j : Fin (M p))
    (σ : LaunchIndex p)
    (w : (NonselectedRows p j × JointPast p σ) × JointFuture p σ) :
    selectedJointSplitEquiv p j σ ((selectedJointSplitEquiv p j σ).symm w) = w :=
  (selectedJointSplitEquiv p j σ).apply_symm_apply w

/-- The sampled index recovered from a retained side/past point uses the
original coordinator scalar, not a replacement selector. -/
def sidePastSelectedIndex (p : Parameters) (j : Fin (M p)) (σ : LaunchIndex p)
    (w : NonselectedRows p j × JointPast p σ) : Fin (M p) :=
  coordinatorIndex p w.2.1.1.2

/-- The selector is the projection of the original scalar and hence depends
only on the retained joint past. -/
theorem selectedJointSplit_selector (p : Parameters) (j : Fin (M p))
    (σ : LaunchIndex p) (z : OriginalCoordinates p) :
    sidePastSelectedIndex p j σ (selectedJointSplitEquiv p j σ z).1 =
      coordinatorIndex p z.1.1.2 := by
  exact congrArg (coordinatorIndex p)
    (selectedJointSplit_coordinatorScalar p j σ z).symm

/-- A fixed-index observable has the exact `1/M` original-index factor when
it is invariant under changing only the original coordinator scalar. The
invariance premise is essential: an arbitrary side/past event may inspect
that numerical scalar and has no such automatic factor. -/
theorem fixedIndex_scalarInvariant_event_disintegration
    {p : Parameters} {β : Type*} [MeasurableSpace β]
    (f : CompleteRow p → ExtendedPrivateCoordinates p → β)
    (hFixed : Measurable (fun z : CompleteRow p × ExtendedPrivateCoordinates p =>
      f z.1 z.2))
    (hinv : ∀ row q s t,
      f row (ReferenceInitializationIndexMixture.insertScalarResidual (s, q)) =
        f row (ReferenceInitializationIndexMixture.insertScalarResidual (t, q)))
    (j : Fin (M p)) (A : Set β) (hA : MeasurableSet A) :
    originalLaw p {z | coordinatorIndex p z.1.1.2 = j ∧ f (z.2 j) z.1 ∈ A} =
      ENNReal.ofReal (1 / (M p : ℝ)) *
        GeneratedBootstrapRoundLaw.originalLaw p {z | f z.1 z.2 ∈ A} := by
  let E : Set (CompleteRows p × ExtendedPrivateCoordinates p) :=
    {w | coordinatorIndex p w.2.1.2 = j ∧
      f (w.1 (coordinatorIndex p w.2.1.2)) w.2 ∈ A}
  have hIndex : Measurable (fun w : CompleteRows p × ExtendedPrivateCoordinates p =>
      coordinatorIndex p w.2.1.2) :=
    (PrivateSourceStreams.measurable_coordinatorIndex p).comp
      (measurable_snd.comp (measurable_fst.comp measurable_snd))
  have hrow : Measurable (fun w : CompleteRows p × ExtendedPrivateCoordinates p =>
      w.1 (coordinatorIndex p w.2.1.2)) :=
    measurable_of_finite_cases _ hIndex (fun k w => w.1 k)
      (fun k => (measurable_pi_apply k).comp measurable_fst)
  have hE : MeasurableSet E := by
    exact (hIndex (measurableSet_singleton j)).inter
      ((hFixed.comp (hrow.prodMk measurable_snd)) hA)
  have hswap : MeasurePreserving (Prod.swap : OriginalCoordinates p →
      CompleteRows p × ExtendedPrivateCoordinates p) (originalLaw p)
      ((completeRowsMeasure p).prod (extendedPrivateLaw p)) := by
    change MeasurePreserving Prod.swap
      ((extendedPrivateLaw p).prod (completeRowsMeasure p))
      ((completeRowsMeasure p).prod (extendedPrivateLaw p))
    exact Measure.measurePreserving_swap
  have hpre : Prod.swap ⁻¹' E =
      {z : OriginalCoordinates p |
        coordinatorIndex p z.1.1.2 = j ∧
          f (z.2 j) z.1 ∈ A} := by
    ext z
    rcases z with ⟨e, rows⟩
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, E, Prod.swap]
    constructor
    · rintro ⟨hJ, hf⟩
      have hrow : rows (coordinatorIndex p e.1.2) = rows j := congrArg rows hJ
      exact ⟨hJ, hrow ▸ hf⟩
    · rintro ⟨hJ, hf⟩
      have hrow : rows (coordinatorIndex p e.1.2) = rows j := congrArg rows hJ
      exact ⟨hJ, hrow.symm ▸ hf⟩
  calc
    originalLaw p {z | coordinatorIndex p z.1.1.2 = j ∧ f (z.2 j) z.1 ∈ A} =
        ((originalLaw p).map Prod.swap) E := by
          rw [← hpre, Measure.map_apply hswap.measurable hE]
    _ = ((completeRowsMeasure p).prod (extendedPrivateLaw p)) E := by
          rw [hswap.map_eq]
    _ = ENNReal.ofReal (1 / (M p : ℝ)) *
          GeneratedBootstrapRoundLaw.originalLaw p {z | f z.1 z.2 ∈ A} :=
        ReferenceInitializationIndexMixture.completeFamily_index_event_pullback
          f hFixed hinv j A hA

/-- The actual launch event on the cell `J = j` is exactly the accepted
strict-past event functional for selected row `j`. -/
theorem actualLaunch_eq_launchEventAt (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (j : Fin (M p))
    (σ : LaunchIndex p) (z : OriginalCoordinates p)
    (hJ : coordinatorIndex p z.1.1.2 = j) :
    ReferenceInitializationIndexMixture.actualLaunchRound p ids rewards C_star C_h eta
        z.2 z.1 = σ.val + 1 ↔
      ReferenceLaunchJointFutureLaw.launchEventAt p ids rewards C_star C_h eta σ
        (selectedJointSplitEquiv p j σ z).1.2 = true := by
  have hrow : ReferenceInitializationIndexMixture.actualLaunchRound p ids rewards C_star C_h
      eta z.2 z.1 =
      ReferenceInitializationIndexMixture.fixedRowLaunchRound p ids rewards C_star C_h eta
        (z.2 j) z.1 := by
    simp only [ReferenceInitializationIndexMixture.actualLaunchRound,
      ReferenceInitializationIndexMixture.fixedRowLaunchRound, hJ]
  have hcoords := selectedJointSplit_selectedCoordinates p j σ z
  have hpast : (selectedJointSplitEquiv p j σ z).1.2 =
      (ReferenceLaunchJointFutureLaw.jointSplitEquiv p σ (z.1, z.2 j)).1 :=
    congrArg Prod.fst hcoords
  rw [hrow]
  change ReferenceInitializationRun.launchRound
      (ReferenceLaunchJointFutureLaw.actualInput p ids rewards C_star C_h eta (z.1, z.2 j)) =
        σ.val + 1 ↔ _
  rw [hpast, ReferenceLaunchJointFutureLaw.launchEventAt_eq_actual p ids rewards C_star C_h eta σ
    (z.1, z.2 j)]
  simp only [decide_eq_true_eq]

/-- The selector and actual selected-row launch event form a measurable event
of the retained whole side/past. -/
def selectedLaunchPastEvent (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (j : Fin (M p))
    (σ : LaunchIndex p) : Set (NonselectedRows p j × JointPast p σ) :=
  {w | sidePastSelectedIndex p j σ w = j ∧
    ReferenceLaunchJointFutureLaw.launchEventAt p ids rewards C_star C_h eta σ w.2 = true}

theorem measurable_selectedLaunchPastEvent (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (j : Fin (M p))
    (σ : LaunchIndex p) :
    MeasurableSet (selectedLaunchPastEvent p ids rewards C_star C_h eta j σ) := by
  have hIndex : Measurable (fun w : NonselectedRows p j × JointPast p σ =>
      sidePastSelectedIndex p j σ w) :=
    (PrivateSourceStreams.measurable_coordinatorIndex p).comp
      (measurable_snd.comp (measurable_fst.comp
        (measurable_fst.comp (measurable_snd.comp measurable_id))))
  have hLaunch : Measurable (fun w : NonselectedRows p j × JointPast p σ =>
      ReferenceLaunchJointFutureLaw.launchEventAt p ids rewards C_star C_h eta σ w.2) :=
    (ReferenceLaunchJointFutureLaw.measurable_launchEventAt p ids rewards C_star C_h eta σ).comp
      measurable_snd
  apply MeasurableSet.inter
  · exact hIndex (measurableSet_singleton j)
  · exact (measurableSet_singleton true).preimage hLaunch

/-- The actual cell with an arbitrary event of all nonselected rows and the
selected joint past, and an arbitrary event of the entire selected future. -/
def actualLaunchCell (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (j : Fin (M p))
    (σ : LaunchIndex p) (A : Set (NonselectedRows p j × JointPast p σ))
    (B : Set (JointFuture p σ)) : Set (OriginalCoordinates p) :=
  {z | coordinatorIndex p z.1.1.2 = j ∧
    ReferenceInitializationIndexMixture.actualLaunchRound p ids rewards C_star C_h eta
      z.2 z.1 = σ.val + 1 ∧
    (selectedJointSplitEquiv p j σ z).1 ∈ A ∧
    (selectedJointSplitEquiv p j σ z).2 ∈ B}

/-- The actual selected-index/launch cell is the pullback of a past event times
an entire-future event under the exact original-label split. -/
theorem actualLaunchCell_eq_preimage (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (j : Fin (M p))
    (σ : LaunchIndex p) (A : Set (NonselectedRows p j × JointPast p σ))
    (B : Set (JointFuture p σ)) :
    actualLaunchCell p ids rewards C_star C_h eta j σ A B =
      (selectedJointSplitEquiv p j σ) ⁻¹' ((A ∩
        selectedLaunchPastEvent p ids rewards C_star C_h eta j σ) ×ˢ B) := by
  ext z
  simp only [actualLaunchCell, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_prod,
    Set.mem_inter_iff, selectedLaunchPastEvent]
  constructor
  · rintro ⟨hJ, hlaunch, hA, hB⟩
    have hselector := (selectedJointSplit_selector p j σ z).symm.trans hJ
    exact ⟨⟨hA, hselector,
      (actualLaunch_eq_launchEventAt p ids rewards C_star C_h eta j σ z hJ).mp hlaunch⟩, hB⟩
  · rintro ⟨⟨hA, hSelectorPast, hLaunchPast⟩, hB⟩
    have hJ := (selectedJointSplit_selector p j σ z).trans hSelectorPast
    refine ⟨hJ, ?_, hA, hB⟩
    exact (actualLaunch_eq_launchEventAt p ids rewards C_star C_h eta j σ z hJ).mpr
      hLaunchPast

/-- The actual selected-index/launch cell mass is its unnormalized
side/past mass. -/
theorem actual_launch_side_past_mass (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (j : Fin (M p))
    (σ : LaunchIndex p) (A : Set (NonselectedRows p j × JointPast p σ))
    (hA : MeasurableSet A) :
    originalLaw p (actualLaunchCell p ids rewards C_star C_h eta j σ A Set.univ) =
      ((nonselectedRowsLaw p j).prod (jointPastLaw p σ))
        (A ∩ selectedLaunchPastEvent p ids rewards C_star C_h eta j σ) := by
  let E := selectedLaunchPastEvent p ids rewards C_star C_h eta j σ
  have hE : MeasurableSet E := measurable_selectedLaunchPastEvent p ids rewards C_star C_h eta j σ
  calc
    originalLaw p (actualLaunchCell p ids rewards C_star C_h eta j σ A Set.univ) =
        ((originalLaw p).map (selectedJointSplitEquiv p j σ))
          ((A ∩ E) ×ˢ Set.univ) := by
            rw [actualLaunchCell_eq_preimage p ids rewards C_star C_h eta j σ A Set.univ]
            rw [← Measure.map_apply (selectedJointSplitEquiv p j σ).measurable
              ((hA.inter hE).prod MeasurableSet.univ)]
    _ = (((nonselectedRowsLaw p j).prod (jointPastLaw p σ)).prod (jointFutureLaw p σ))
          ((A ∩ E) ×ˢ Set.univ) := by rw [map_selectedJointSplit]
    _ = ((nonselectedRowsLaw p j).prod (jointPastLaw p σ)) (A ∩ E) := by
          rw [Measure.prod_prod, measure_univ, mul_one]

/-- Factorization for any measurable event of all nonselected rows and the
selected joint past, against any measurable event of the complete joint
future. The cell is not normalized, so zero-mass cells are included. -/
theorem actual_launch_event_factorization (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (j : Fin (M p))
    (σ : LaunchIndex p) (A : Set (NonselectedRows p j × JointPast p σ))
    (hA : MeasurableSet A) (B : Set (JointFuture p σ)) (hB : MeasurableSet B) :
    originalLaw p (actualLaunchCell p ids rewards C_star C_h eta j σ A B) =
      originalLaw p (actualLaunchCell p ids rewards C_star C_h eta j σ A Set.univ) *
        jointFutureLaw p σ B := by
  let E := selectedLaunchPastEvent p ids rewards C_star C_h eta j σ
  have hE : MeasurableSet E := measurable_selectedLaunchPastEvent p ids rewards C_star C_h eta j σ
  calc
    originalLaw p (actualLaunchCell p ids rewards C_star C_h eta j σ A B) =
        (((nonselectedRowsLaw p j).prod (jointPastLaw p σ)).prod (jointFutureLaw p σ))
          ((A ∩ E) ×ˢ B) := by
            rw [actualLaunchCell_eq_preimage p ids rewards C_star C_h eta j σ A B]
            rw [← Measure.map_apply (selectedJointSplitEquiv p j σ).measurable
              ((hA.inter hE).prod hB), map_selectedJointSplit]
    _ = ((nonselectedRowsLaw p j).prod (jointPastLaw p σ)) (A ∩ E) *
          jointFutureLaw p σ B := Measure.prod_prod _ _
    _ = originalLaw p (actualLaunchCell p ids rewards C_star C_h eta j σ A Set.univ) *
          jointFutureLaw p σ B := by
            rw [← actual_launch_side_past_mass p ids rewards C_star C_h eta j σ A hA]

/-- Actual launch cells retain their selector scalar in the past even when
the side event inspects its numerical value. -/
theorem actual_launch_event_factorization_with_side_past_mass
    (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (j : Fin (M p))
    (σ : LaunchIndex p) (A : Set (NonselectedRows p j × JointPast p σ))
    (hA : MeasurableSet A) (B : Set (JointFuture p σ)) (hB : MeasurableSet B) :
    originalLaw p (actualLaunchCell p ids rewards C_star C_h eta j σ A B) =
      ((nonselectedRowsLaw p j).prod (jointPastLaw p σ))
        (A ∩ selectedLaunchPastEvent p ids rewards C_star C_h eta j σ) *
        jointFutureLaw p σ B := by
  rw [actual_launch_event_factorization p ids rewards C_star C_h eta j σ A hA B hB,
    actual_launch_side_past_mass p ids rewards C_star C_h eta j σ A hA]

/-- A finite family of actual launch observables, one measurable whole-future
test and one measurable side/past event for each `(original index, launch)`
cell. -/
abbrev LaunchCell (p : Parameters) := Fin (M p) × LaunchIndex p

abbrev LaunchCellSidePast (p : Parameters) (c : LaunchCell p) :=
  NonselectedRows p c.1 × JointPast p c.2

abbrev LaunchCellFuture (p : Parameters) (c : LaunchCell p) := JointFuture p c.2

def actualLaunchObservables (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (A : (c : LaunchCell p) → Set (LaunchCellSidePast p c))
    (B : (c : LaunchCell p) → Set (LaunchCellFuture p c)) : Set (OriginalCoordinates p) :=
  ⋃ c : LaunchCell p, actualLaunchCell p ids rewards C_star C_h eta c.1 c.2
    (A c) (B c)

theorem measurable_actualLaunchCell (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (c : LaunchCell p)
    (A : Set (LaunchCellSidePast p c)) (hA : MeasurableSet A)
    (B : Set (LaunchCellFuture p c)) (hB : MeasurableSet B) :
    MeasurableSet (actualLaunchCell p ids rewards C_star C_h eta c.1 c.2 A B) := by
  apply MeasurableSet.inter
  · exact ((PrivateSourceStreams.measurable_coordinatorIndex p).comp
      (measurable_snd.comp (measurable_fst.comp measurable_fst)))
      (measurableSet_singleton c.1)
  · apply MeasurableSet.inter
    · exact (measurableSet_singleton (c.2.val + 1)).preimage <|
        (ReferenceInitializationIndexMixture.measurable_actualLaunchRound_family
          p ids rewards C_star C_h eta).comp measurable_swap
    · apply MeasurableSet.inter
      · exact hA.preimage ((measurable_fst.comp
          (selectedJointSplitEquiv p c.1 c.2).measurable))
      · exact hB.preimage ((measurable_snd.comp
          (selectedJointSplitEquiv p c.1 c.2).measurable))

/-- The actual launch cells are pairwise disjoint because the original index
and source launch round each have one value. -/
theorem pairwiseDisjoint_actualLaunchCell (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (A : (c : LaunchCell p) → Set (LaunchCellSidePast p c))
    (B : (c : LaunchCell p) → Set (LaunchCellFuture p c)) :
    Pairwise (fun c d => Disjoint
      (actualLaunchCell p ids rewards C_star C_h eta c.1 c.2 (A c) (B c))
      (actualLaunchCell p ids rewards C_star C_h eta d.1 d.2 (A d) (B d))) := by
  intro c d hcd
  apply Set.disjoint_left.mpr
  intro z hzC hzD
  have hj := hzC.1.symm.trans hzD.1
  have hs : c.2 = d.2 := by
    apply Fin.ext
    have heq := hzC.2.1.symm.trans hzD.2.1
    omega
  exact hcd (Prod.ext hj hs)

/-- Finite `(j, sigma)` disintegration for actual launch observables. The
whole-future tests may vary arbitrarily from cell to cell; each term factors
directly from its disjoint actual cell. -/
theorem actualLaunchObservables_disintegration (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (A : (c : LaunchCell p) → Set (LaunchCellSidePast p c))
    (hA : ∀ c, MeasurableSet (A c))
    (B : (c : LaunchCell p) → Set (LaunchCellFuture p c))
    (hB : ∀ c, MeasurableSet (B c)) :
    originalLaw p (actualLaunchObservables p ids rewards C_star C_h eta A B) =
      ∑ c : LaunchCell p,
        originalLaw p (actualLaunchCell p ids rewards C_star C_h eta c.1 c.2 (A c) Set.univ) *
          jointFutureLaw p c.2 (B c) := by
  have hcell : ∀ c, MeasurableSet
      (actualLaunchCell p ids rewards C_star C_h eta c.1 c.2 (A c) (B c)) := by
    intro c
    exact measurable_actualLaunchCell p ids rewards C_star C_h eta c (A c) (hA c)
      (B c) (hB c)
  have hunion : actualLaunchObservables p ids rewards C_star C_h eta A B =
      ⋃ c : LaunchCell p,
        actualLaunchCell p ids rewards C_star C_h eta c.1 c.2 (A c) (B c) := rfl
  calc
    _ = ∑' c : LaunchCell p,
        originalLaw p (actualLaunchCell p ids rewards C_star C_h eta c.1 c.2 (A c) (B c)) := by
      rw [hunion, measure_iUnion (pairwiseDisjoint_actualLaunchCell p ids rewards C_star C_h eta A B)
        hcell]
    _ = ∑ c : LaunchCell p,
        originalLaw p (actualLaunchCell p ids rewards C_star C_h eta c.1 c.2 (A c) (B c)) :=
      tsum_fintype _
    _ = ∑ c : LaunchCell p,
        originalLaw p (actualLaunchCell p ids rewards C_star C_h eta c.1 c.2 (A c) Set.univ) *
          jointFutureLaw p c.2 (B c) := by
      apply Finset.sum_congr rfl
      intro c hc
      exact actual_launch_event_factorization p ids rewards C_star C_h eta c.1 c.2
        (A c) (hA c) (B c) (hB c)

end Bandits.Support.SelectedIndexLaunchJointLaw

end
