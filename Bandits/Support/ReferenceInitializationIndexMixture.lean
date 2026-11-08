/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceInitializationMeasurability
public import Bandits.Support.GeneratedBootstrapRoundLaw

import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The actual private row-index mixture for reference initialization

For a fixed complete-row family, the coordinator's original continuous scalar
selects the same row used by the actual initialization. The existing run is
pointwise invariant under changing only that scalar when the selected row is
held fixed. This gives an exact J-atom disintegration for the actual output
and launch, and the complete-family version pulls back through the accepted
whole-row evaluation law.

These are internal initialization constructions. They do not assert actual to
reference agreement, a failure or cost bound, a postlaunch execution, or
startup-proposition closure.

Sources: `sources/zip4/manuscript/07_public_setup.tex:123-164`,
`sources/zip4/manuscript/appendix_b_communication.tex:786-798`, and
`sources/zip4/manuscript/08_main_theorem.tex:27-48,67-83`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.CompletePublicTable
open Bandits.Support.ContinuousCategorical
open Bandits.Support.PrivateSourceStreams
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ReferenceInitializationRun
open Bandits.Support.ReferenceInitializationCausality
open Bandits.Support.ReferenceInitializationPrefixInvariance
open Bandits.Support.ReferenceInitializationMeasurability
open scoped ENNReal

namespace Bandits.Support.ReferenceInitializationIndexMixture

private theorem measurable_of_finite_cases {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [Finite β] [MeasurableSingletonClass β]
    [MeasurableSpace γ] (key : α → β) (hkey : Measurable key)
    (branch : β → α → γ) (hbranch : ∀ b, Measurable (branch b)) :
    Measurable (fun x => branch (key x) x) :=
  (measurable_from_prod_countable_right
    (f := fun v : β × α => branch v.1 v.2) hbranch).comp
      (hkey.prodMk measurable_id)

abbrev Parameters := ConstructorDimensions.Parameters
abbrev Scalar := ContinuousCategorical.Scalar
abbrev PrivateResidual (p : Parameters) :=
  PrivateSourceStreams.FollowerBlockInputs p ×
    (PlayerRoundScalars p × CoordinatorTargetScalars p)

/-- Replace the actual coordinator J scalar while keeping every other private
coordinate literal and in its original position. -/
@[expose] def withCoordinatorScalar {p : Parameters}
    (e : ExtendedPrivateCoordinates p) (s : Scalar) : ExtendedPrivateCoordinates p :=
  ((e.1.1, s), e.2)

/-- Reorder the original private product with the J scalar first. No coordinate
is added, dropped, sampled, or completed by this map. -/
@[expose] def scalarAndResidual {p : Parameters} (e : ExtendedPrivateCoordinates p) :
    Scalar × PrivateResidual p :=
  (e.1.2, (e.1.1, e.2))

/-- Reinsert a scalar into the literal residual coordinates. -/
@[expose] def insertScalarResidual {p : Parameters}
    (z : Scalar × PrivateResidual p) : ExtendedPrivateCoordinates p :=
  ((z.2.1, z.1), z.2.2)

@[simp] theorem scalarAndResidual_insert {p : Parameters}
    (z : Scalar × PrivateResidual p) :
    scalarAndResidual (insertScalarResidual z) = z := rfl

@[simp] theorem insert_scalarAndResidual {p : Parameters}
    (e : ExtendedPrivateCoordinates p) :
    insertScalarResidual (scalarAndResidual e) = e := rfl

/-- The residual private-stream product law after moving the original J scalar
to the first factor. -/
@[expose] def privateResidualLaw (p : Parameters) : Measure (PrivateResidual p) :=
  PrivateSourceStreams.followerBlockInputsLaw p |>.prod (extraPrivateStreamsLaw p)

instance privateResidualLaw_probability (p : Parameters) :
    IsProbabilityMeasure (privateResidualLaw p) := by
  dsimp [privateResidualLaw]
  infer_instance

/-- Literal scalar-first factorization of the accepted extended private law. -/
theorem measurePreserving_scalarAndResidual (p : Parameters) :
    MeasurePreserving (scalarAndResidual (p := p)) (extendedPrivateLaw p)
      (ContinuousCategorical.uniform.prod (privateResidualLaw p)) := by
  change MeasurePreserving (fun e : ((PrivateSourceStreams.FollowerBlockInputs p × Scalar) ×
      (PlayerRoundScalars p × CoordinatorTargetScalars p)) =>
        (e.1.2, (e.1.1, e.2)))
      ((PrivateSourceStreams.followerBlockInputsLaw p |>.prod coordinatorScalarLaw) |>.prod
        (extraPrivateStreamsLaw p))
      (ContinuousCategorical.uniform.prod
        (PrivateSourceStreams.followerBlockInputsLaw p |>.prod (extraPrivateStreamsLaw p)))
  have h₁ := measurePreserving_prodAssoc
    (PrivateSourceStreams.followerBlockInputsLaw p) coordinatorScalarLaw
    (extraPrivateStreamsLaw p)
  have h₂ : MeasurePreserving
      (fun z : PrivateSourceStreams.FollowerBlockInputs p ×
          (Scalar × (PlayerRoundScalars p × CoordinatorTargetScalars p)) =>
        (z.1, (z.2.2, z.2.1)))
      (PrivateSourceStreams.followerBlockInputsLaw p |>.prod
        (coordinatorScalarLaw.prod (extraPrivateStreamsLaw p)))
      (PrivateSourceStreams.followerBlockInputsLaw p |>.prod
        ((extraPrivateStreamsLaw p).prod coordinatorScalarLaw)) := by
    exact (MeasurePreserving.id (PrivateSourceStreams.followerBlockInputsLaw p)).prod
      (Measure.measurePreserving_swap (μ := coordinatorScalarLaw)
        (ν := extraPrivateStreamsLaw p))
  have h₃ := (measurePreserving_prodAssoc
    (PrivateSourceStreams.followerBlockInputsLaw p) (extraPrivateStreamsLaw p)
    coordinatorScalarLaw).symm
  have h₄ := Measure.measurePreserving_swap
    (μ := PrivateSourceStreams.followerBlockInputsLaw p |>.prod (extraPrivateStreamsLaw p))
    (ν := coordinatorScalarLaw)
  have h := h₄.comp (h₃.comp (h₂.comp h₁))
  convert h using 1 <;> rfl

/-- The fixed selected-row input built by the existing initialization adapter. -/
@[expose] def fixedRowInput (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (row : CompleteRow p)
    (e : ExtendedPrivateCoordinates p) : Input p :=
  inputOfCoordinates p C_star C_h eta rewards (ids, (row, e))

/-- Every literal premise of the existing run-prefix relation holds when only
the coordinator scalar changes: IDs, rewards, constants, row entries, block
triples, target scalars, and player-round scalars compare by reflexivity. -/
theorem runPrefixInputEq_of_coordinatorScalar_change (p : Parameters)
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (row : CompleteRow p) (e : ExtendedPrivateCoordinates p) (s : Scalar) (r : ℕ) :
    ReferenceInitializationCausality.runPrefixInputEq
      (fixedRowInput p ids rewards C_star C_h eta row (withCoordinatorScalar e s))
      (fixedRowInput p ids rewards C_star C_h eta row e) r := by
  rcases e with ⟨⟨blocks, oldScalar⟩, ⟨rounds, targets⟩⟩
  dsimp [ReferenceInitializationCausality.runPrefixInputEq, fixedRowInput,
    withCoordinatorScalar, inputOfCoordinates]
  exact ⟨rfl, rfl, rfl, rfl, rfl,
    (by intro t ht; exact ⟨by intro u; rfl, rfl⟩),
    (by intro q hq j; rfl), (by intro q hq; rfl),
    (by intro i t ht; rfl)⟩

/-- Every literal strict-past premise of the existing launch-prefix relation
holds under the same scalar change. -/
theorem launchPrefixInputEq_of_coordinatorScalar_change (p : Parameters)
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (row : CompleteRow p) (e : ExtendedPrivateCoordinates p) (s : Scalar) (n : ℕ) :
    ReferenceInitializationCausality.launchPrefixInputEq
      (fixedRowInput p ids rewards C_star C_h eta row (withCoordinatorScalar e s))
      (fixedRowInput p ids rewards C_star C_h eta row e) n := by
  rcases e with ⟨⟨blocks, oldScalar⟩, ⟨rounds, targets⟩⟩
  dsimp [ReferenceInitializationCausality.launchPrefixInputEq, fixedRowInput,
    withCoordinatorScalar, inputOfCoordinates]
  exact ⟨rfl, rfl, rfl, rfl, rfl,
    (by intro t ht; exact ⟨by intro u; rfl, rfl⟩),
    (by intro q hq; exact ⟨by intro i; rfl, rfl⟩),
    (by intro i t ht; rfl)⟩

/-- The actual existing stopped boundary is invariant at every run index when
only the J scalar changes and the selected complete row is held fixed. -/
theorem fixedRow_run_eq_of_coordinatorScalar_change (p : Parameters)
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (row : CompleteRow p) (e : ExtendedPrivateCoordinates p) (s : Scalar) (r : ℕ) :
    ReferenceInitializationRun.run
      (fixedRowInput p ids rewards C_star C_h eta row (withCoordinatorScalar e s)) r =
    ReferenceInitializationRun.run (fixedRowInput p ids rewards C_star C_h eta row e) r := by
  exact ReferenceInitializationPrefixInvariance.run_eq_of_runPrefixInputEq _ _ r
    (runPrefixInputEq_of_coordinatorScalar_change p ids rewards C_star C_h eta row e s r)

/-- The actual terminal output boundary is invariant under changing only the
coordinator scalar. -/
theorem fixedRow_output_eq_of_coordinatorScalar_change (p : Parameters)
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (row : CompleteRow p) (e : ExtendedPrivateCoordinates p) (s : Scalar) :
    ReferenceInitializationRun.output
      (fixedRowInput p ids rewards C_star C_h eta row (withCoordinatorScalar e s)) =
    ReferenceInitializationRun.output (fixedRowInput p ids rewards C_star C_h eta row e) := by
  exact fixedRow_run_eq_of_coordinatorScalar_change p ids rewards C_star C_h eta row e s
    (n_boot p)

/-- The actual launch round, including its `T+1` no-launch convention, is
invariant under changing only the coordinator scalar. -/
theorem fixedRow_launchRound_eq_of_coordinatorScalar_change (p : Parameters)
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (row : CompleteRow p) (e : ExtendedPrivateCoordinates p) (s : Scalar) :
    ReferenceInitializationRun.launchRound
      (fixedRowInput p ids rewards C_star C_h eta row (withCoordinatorScalar e s)) =
    ReferenceInitializationRun.launchRound (fixedRowInput p ids rewards C_star C_h eta row e) := by
  unfold ReferenceInitializationRun.launchRound
  rw [fixedRow_output_eq_of_coordinatorScalar_change p ids rewards C_star C_h eta row e s]

/-- The actual initialization output for a fixed full published row family;
the original continuous scalar selects `J` and is passed unchanged. -/
@[expose] def actualOutput (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (rows : CompleteRows p)
    (e : ExtendedPrivateCoordinates p) : Boundary p :=
  ReferenceInitializationRun.output
    (fixedRowInput p ids rewards C_star C_h eta (rows (coordinatorIndex p e.1.2)) e)

/-- The actual initialization launch round for a fixed row family, with the
existing `T+1` sentinel retained. -/
@[expose] def actualLaunchRound (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (rows : CompleteRows p)
    (e : ExtendedPrivateCoordinates p) : ℕ :=
  ReferenceInitializationRun.launchRound
    (fixedRowInput p ids rewards C_star C_h eta (rows (coordinatorIndex p e.1.2)) e)

/-- The actual output from one fixed selected row, on the original extended
private coordinates. -/
@[expose] def fixedRowOutput (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (row : CompleteRow p)
    (e : ExtendedPrivateCoordinates p) : Boundary p :=
  ReferenceInitializationRun.output (fixedRowInput p ids rewards C_star C_h eta row e)

/-- The actual launch round from one fixed selected row. -/
@[expose] def fixedRowLaunchRound (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (row : CompleteRow p)
    (e : ExtendedPrivateCoordinates p) : ℕ :=
  ReferenceInitializationRun.launchRound (fixedRowInput p ids rewards C_star C_h eta row e)

theorem measurable_fixedRowOutput (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (row : CompleteRow p) :
    Measurable (fixedRowOutput p ids rewards C_star C_h eta row) := by
  have hinput : Measurable (fun e : ExtendedPrivateCoordinates p =>
      (ids, (row, e))) := by
    exact measurable_const.prodMk (measurable_const.prodMk measurable_id)
  exact (ReferenceInitializationMeasurability.measurable_output
    p C_star C_h eta rewards).comp hinput

theorem measurable_fixedRowLaunchRound (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (row : CompleteRow p) :
    Measurable (fixedRowLaunchRound p ids rewards C_star C_h eta row) := by
  have hinput : Measurable (fun e : ExtendedPrivateCoordinates p =>
      (ids, (row, e))) := by
    exact measurable_const.prodMk (measurable_const.prodMk measurable_id)
  exact (ReferenceInitializationMeasurability.measurable_launchRound
    p C_star C_h eta rewards).comp hinput

/-- Measurability of the actual fixed-row initialization output when the full
row and original private coordinates are both variables. -/
theorem measurable_fixedRowOutput_pair (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) :
    Measurable (fun z : CompleteRow p × ExtendedPrivateCoordinates p =>
      fixedRowOutput p ids rewards C_star C_h eta z.1 z.2) := by
  have hinput : Measurable (fun z : CompleteRow p × ExtendedPrivateCoordinates p =>
      (ids, (z.1, z.2))) := measurable_const.prodMk measurable_id
  exact (ReferenceInitializationMeasurability.measurable_output
    p C_star C_h eta rewards).comp hinput

/-- Measurability of the actual fixed-row launch map with both its row and
original private coordinates variable. -/
theorem measurable_fixedRowLaunchRound_pair (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) :
    Measurable (fun z : CompleteRow p × ExtendedPrivateCoordinates p =>
      fixedRowLaunchRound p ids rewards C_star C_h eta z.1 z.2) := by
  have hinput : Measurable (fun z : CompleteRow p × ExtendedPrivateCoordinates p =>
      (ids, (z.1, z.2))) := measurable_const.prodMk measurable_id
  exact (ReferenceInitializationMeasurability.measurable_launchRound
    p C_star C_h eta rewards).comp hinput

theorem measurable_actualOutput (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (rows : CompleteRows p) :
    Measurable (actualOutput p ids rewards C_star C_h eta rows) := by
  have hJ : Measurable (fun e : ExtendedPrivateCoordinates p =>
      coordinatorIndex p e.1.2) :=
    (PrivateSourceStreams.measurable_coordinatorIndex p).comp
      (measurable_snd.comp measurable_fst)
  have hrow : Measurable (fun e : ExtendedPrivateCoordinates p =>
      rows (coordinatorIndex p e.1.2)) :=
    (measurable_of_finite rows).comp hJ
  have hinput : Measurable (fun e : ExtendedPrivateCoordinates p =>
      (ids, (rows (coordinatorIndex p e.1.2), e))) :=
    measurable_const.prodMk (hrow.prodMk measurable_id)
  exact (ReferenceInitializationMeasurability.measurable_output
    p C_star C_h eta rewards).comp hinput

theorem measurable_actualLaunchRound (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (rows : CompleteRows p) :
    Measurable (actualLaunchRound p ids rewards C_star C_h eta rows) := by
  have hJ : Measurable (fun e : ExtendedPrivateCoordinates p =>
      coordinatorIndex p e.1.2) :=
    (PrivateSourceStreams.measurable_coordinatorIndex p).comp
      (measurable_snd.comp measurable_fst)
  have hrow : Measurable (fun e : ExtendedPrivateCoordinates p =>
      rows (coordinatorIndex p e.1.2)) :=
    (measurable_of_finite rows).comp hJ
  have hinput : Measurable (fun e : ExtendedPrivateCoordinates p =>
      (ids, (rows (coordinatorIndex p e.1.2), e))) :=
    measurable_const.prodMk (hrow.prodMk measurable_id)
  exact (ReferenceInitializationMeasurability.measurable_launchRound
    p C_star C_h eta rewards).comp hinput

/-- Measurability of the actual selected-row initialization output as a
function of the full family and the original private labels. -/
theorem measurable_actualOutput_family (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) :
    Measurable (fun z : CompleteRows p × ExtendedPrivateCoordinates p =>
      actualOutput p ids rewards C_star C_h eta z.1 z.2) := by
  have hJ : Measurable (fun z : CompleteRows p × ExtendedPrivateCoordinates p =>
      coordinatorIndex p z.2.1.2) :=
    (PrivateSourceStreams.measurable_coordinatorIndex p).comp
      (measurable_snd.comp (measurable_fst.comp measurable_snd))
  have hrow : Measurable (fun z : CompleteRows p × ExtendedPrivateCoordinates p =>
      z.1 (coordinatorIndex p z.2.1.2)) := by
    exact measurable_of_finite_cases (fun z : CompleteRows p × ExtendedPrivateCoordinates p =>
      coordinatorIndex p z.2.1.2) hJ (fun j z => z.1 j)
      (fun j => (measurable_pi_apply j).comp measurable_fst)
  have hinput : Measurable (fun z : CompleteRows p × ExtendedPrivateCoordinates p =>
      (ids, (z.1 (coordinatorIndex p z.2.1.2), z.2))) :=
    measurable_const.prodMk (hrow.prodMk measurable_snd)
  exact (ReferenceInitializationMeasurability.measurable_output
    p C_star C_h eta rewards).comp hinput

/-- Measurability of the actual selected-row launch map as a function of the
full family and original private labels. -/
theorem measurable_actualLaunchRound_family (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) :
    Measurable (fun z : CompleteRows p × ExtendedPrivateCoordinates p =>
      actualLaunchRound p ids rewards C_star C_h eta z.1 z.2) := by
  have hJ : Measurable (fun z : CompleteRows p × ExtendedPrivateCoordinates p =>
      coordinatorIndex p z.2.1.2) :=
    (PrivateSourceStreams.measurable_coordinatorIndex p).comp
      (measurable_snd.comp (measurable_fst.comp measurable_snd))
  have hrow : Measurable (fun z : CompleteRows p × ExtendedPrivateCoordinates p =>
      z.1 (coordinatorIndex p z.2.1.2)) := by
    exact measurable_of_finite_cases (fun z : CompleteRows p × ExtendedPrivateCoordinates p =>
      coordinatorIndex p z.2.1.2) hJ (fun j z => z.1 j)
      (fun j => (measurable_pi_apply j).comp measurable_fst)
  have hinput : Measurable (fun z : CompleteRows p × ExtendedPrivateCoordinates p =>
      (ids, (z.1 (coordinatorIndex p z.2.1.2), z.2))) :=
    measurable_const.prodMk (hrow.prodMk measurable_snd)
  exact (ReferenceInitializationMeasurability.measurable_launchRound
    p C_star C_h eta rewards).comp hinput

private theorem fixedRow_scalar_invariant_output (p : Parameters)
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (row : CompleteRow p) (q : PrivateResidual p) (s t : Scalar) :
    fixedRowOutput p ids rewards C_star C_h eta row
      (insertScalarResidual (s, q)) =
    fixedRowOutput p ids rewards C_star C_h eta row
      (insertScalarResidual (t, q)) := by
  exact (fixedRow_output_eq_of_coordinatorScalar_change p ids rewards C_star C_h eta row
    (insertScalarResidual (t, q)) s)

private theorem fixedRow_scalar_invariant_launch (p : Parameters)
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (row : CompleteRow p) (q : PrivateResidual p) (s t : Scalar) :
    fixedRowLaunchRound p ids rewards C_star C_h eta row
      (insertScalarResidual (s, q)) =
    fixedRowLaunchRound p ids rewards C_star C_h eta row
      (insertScalarResidual (t, q)) := by
  exact (fixedRow_launchRound_eq_of_coordinatorScalar_change p ids rewards C_star C_h eta row
    (insertScalarResidual (t, q)) s)

private theorem coordinatorIndex_event_disintegration
    {p : Parameters} {β : Type*} [MeasurableSpace β]
    (f : ExtendedPrivateCoordinates p → β) (hf : Measurable f)
    (hinv : ∀ q s t, f (insertScalarResidual (s, q)) =
      f (insertScalarResidual (t, q))) (j : Fin (M p)) (A : Set β)
    (hA : MeasurableSet A) :
    extendedPrivateLaw p {e | coordinatorIndex p e.1.2 = j ∧ f e ∈ A} =
      ENNReal.ofReal (1 / (M p : ℝ)) *
        extendedPrivateLaw p {e | f e ∈ A} := by
  let s₀ : Scalar := ⟨0, by norm_num⟩
  let atom : Set Scalar := {s | coordinatorIndex p s = j}
  let event : Set (PrivateResidual p) :=
    {q | f (insertScalarResidual (s₀, q)) ∈ A}
  have hJ : MeasurableSet atom := by
    exact (PrivateSourceStreams.measurable_coordinatorIndex p)
      (measurableSet_singleton j)
  have hEvent : MeasurableSet event := by
    have hrestore : Measurable (fun q : PrivateResidual p =>
        insertScalarResidual (s₀, q)) := by
      exact (measurable_fst.prodMk measurable_const).prodMk measurable_snd
    exact (hf.comp hrestore) hA
  have hrect : MeasurableSet (atom ×ˢ event) := hJ.prod hEvent
  have hpre : scalarAndResidual (p := p) ⁻¹' (atom ×ˢ event) =
      {e : ExtendedPrivateCoordinates p |
        coordinatorIndex p e.1.2 = j ∧ f e ∈ A} := by
    ext e
    rcases e with ⟨⟨blocks, scalar⟩, extra⟩
    simp only [Set.mem_preimage, Set.mem_prod, atom, event, scalarAndResidual,
      insertScalarResidual, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hJ, hAevent⟩
      refine ⟨hJ, ?_⟩
      exact (hinv (blocks, extra) scalar s₀).symm ▸ hAevent
    · rintro ⟨hJ, hfe⟩
      exact ⟨hJ, hinv (blocks, extra) scalar s₀ ▸ hfe⟩
  have hpreRight : scalarAndResidual (p := p) ⁻¹' (Set.univ ×ˢ event) =
      {e : ExtendedPrivateCoordinates p | f e ∈ A} := by
    ext e
    rcases e with ⟨⟨blocks, scalar⟩, extra⟩
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, true_and, event,
      scalarAndResidual, insertScalarResidual, Set.mem_setOf_eq]
    exact ⟨fun h => (hinv (blocks, extra) scalar s₀).symm ▸ h,
      fun h => (hinv (blocks, extra) scalar s₀) ▸ h⟩
  have hmp := measurePreserving_scalarAndResidual p
  have hleft : extendedPrivateLaw p
      {e | coordinatorIndex p e.1.2 = j ∧ f e ∈ A} =
        ContinuousCategorical.uniform atom * privateResidualLaw p event := by
    calc
      extendedPrivateLaw p {e | coordinatorIndex p e.1.2 = j ∧ f e ∈ A} =
          (extendedPrivateLaw p).map (scalarAndResidual (p := p)) (atom ×ˢ event) := by
            rw [← hpre, Measure.map_apply hmp.measurable hrect]
      _ = ContinuousCategorical.uniform atom * privateResidualLaw p event := by
            rw [hmp.map_eq, Measure.prod_prod]
  have hatom : ContinuousCategorical.uniform atom =
      ENNReal.ofReal (1 / (M p : ℝ)) := by
    have hset : atom = coordinatorIndex p ⁻¹' {j} := by
      ext s
      simp [atom]
    rw [hset]
    exact PrivateSourceStreams.coordinatorIndex_uniform_atom p j
  have hright : extendedPrivateLaw p {e | f e ∈ A} =
      privateResidualLaw p event := by
    calc
      extendedPrivateLaw p {e | f e ∈ A} =
          (extendedPrivateLaw p).map (scalarAndResidual (p := p)) (Set.univ ×ˢ event) := by
            rw [← hpreRight, Measure.map_apply hmp.measurable
              (MeasurableSet.univ.prod hEvent)]
      _ = privateResidualLaw p event := by
            rw [hmp.map_eq, Measure.prod_prod, ContinuousCategorical.uniform_univ, one_mul]
  rw [hleft, hatom, ← hright]

/-- Equality of the selected-index sublaw and a scalar multiple of a
fixed-selected-row law, characterized by the exact event disintegration. -/
theorem coordinatorIndex_restricted_map_eq_smul
    {p : Parameters} {β : Type*} [MeasurableSpace β]
    (g h : ExtendedPrivateCoordinates p → β)
    (hg : Measurable g) (hh : Measurable h)
    (j : Fin (M p))
    (hEvent : ∀ (A : Set β), MeasurableSet A →
      extendedPrivateLaw p {e | coordinatorIndex p e.1.2 = j ∧ g e ∈ A} =
        ENNReal.ofReal (1 / (M p : ℝ)) * extendedPrivateLaw p {e | h e ∈ A}) :
    ((extendedPrivateLaw p).restrict {e | coordinatorIndex p e.1.2 = j}).map g =
      ENNReal.ofReal (1 / (M p : ℝ)) • (extendedPrivateLaw p).map h := by
  have hJ : MeasurableSet {e : ExtendedPrivateCoordinates p |
      coordinatorIndex p e.1.2 = j} := by
    exact (PrivateSourceStreams.measurable_coordinatorIndex p).comp
      (measurable_snd.comp measurable_fst) (measurableSet_singleton j)
  apply Measure.ext
  intro A hA
  rw [Measure.map_apply hg hA, Measure.restrict_apply (hg hA),
    Measure.smul_apply, smul_eq_mul, Measure.map_apply hh hA]
  have hset :
      g ⁻¹' A ∩ {e : ExtendedPrivateCoordinates p |
          coordinatorIndex p e.1.2 = j} =
        {e | coordinatorIndex p e.1.2 = j ∧ g e ∈ A} := by
    ext e
    simp [and_comm]
  rw [hset]
  exact hEvent A hA

/-- A bounded measurable real test composed with a measurable observable is
integrable for every finite measure. -/
theorem integrable_bounded_measurable_comp
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} [IsFiniteMeasure μ] (f : α → β) (hf : Measurable f)
    (φ : β → ℝ) (hφ : Measurable φ) (lo hi : ℝ)
    (hbound : ∀ b, φ b ∈ Set.Icc lo hi) : Integrable (fun x => φ (f x)) μ := by
  apply Integrable.of_mem_Icc lo hi (hφ.comp hf).aemeasurable
  exact ae_of_all _ fun x => hbound (f x)

/-- Bounded-test disintegration follows from the selected-index sublaw; the
integrals over the restricted measure and the original private law are both
well defined. -/
theorem bounded_test_integral_of_restricted_map_eq_smul
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [IsFiniteMeasure μ] (E : Set α) (g h : α → β)
    (hg : Measurable g) (hh : Measurable h)
    (c : ℝ≥0∞) (hmap : (μ.restrict E).map g = c • μ.map h)
    (φ : β → ℝ) (hφ : Measurable φ) (lo hi : ℝ)
    (hbound : ∀ b, φ b ∈ Set.Icc lo hi) :
    Integrable (fun x => φ (g x)) (μ.restrict E) ∧
      Integrable (fun x => φ (h x)) μ ∧
      (∫ x in E, φ (g x) ∂μ = c.toReal * ∫ x, φ (h x) ∂μ) := by
  have : IsFiniteMeasure (μ.restrict E) := by infer_instance
  have hIleft := integrable_bounded_measurable_comp (μ := μ.restrict E)
    g hg φ hφ lo hi hbound
  have hIright := integrable_bounded_measurable_comp (μ := μ)
    h hh φ hφ lo hi hbound
  refine ⟨hIleft, hIright, ?_⟩
  calc
    ∫ x in E, φ (g x) ∂μ =
        ∫ y, φ y ∂(μ.restrict E).map g := by
          change ∫ x, φ (g x) ∂μ.restrict E = _
          exact (integral_map_of_stronglyMeasurable hg hφ.stronglyMeasurable).symm
    _ = ∫ y, φ y ∂(c • μ.map h) := by rw [hmap]
    _ = c.toReal * ∫ y, φ y ∂μ.map h := by
          rw [integral_smul_measure, smul_eq_mul]
    _ = c.toReal * ∫ x, φ (h x) ∂μ := by
          rw [integral_map_of_stronglyMeasurable hh hφ.stronglyMeasurable]

/-- Move an independent complete-row family next to the residual private
streams while exposing the original continuous coordinator scalar first. -/
@[expose] def liftScalarResidual {α : Type*} {p : Parameters}
    (z : α × ExtendedPrivateCoordinates p) : Scalar × (α × PrivateResidual p) :=
  (z.2.1.2, (z.1, (z.2.1.1, z.2.2)))

/-- Product-law factorization for the literal scalar-first reordering with an
independent public coordinate. -/
theorem measurePreserving_liftScalarResidual {α : Type*} [MeasurableSpace α]
    (p : Parameters) (μ : Measure α) [SFinite μ] :
    MeasurePreserving (liftScalarResidual (p := p)) (μ.prod (extendedPrivateLaw p))
      (ContinuousCategorical.uniform.prod (μ.prod (privateResidualLaw p))) := by
  have hprod : MeasurePreserving
      (fun z : α × ExtendedPrivateCoordinates p =>
        (z.1, scalarAndResidual (p := p) z.2))
      (μ.prod (extendedPrivateLaw p))
      (μ.prod (ContinuousCategorical.uniform.prod (privateResidualLaw p))) :=
    (MeasurePreserving.id μ).prod (measurePreserving_scalarAndResidual p)
  have h₁ := (measurePreserving_prodAssoc μ ContinuousCategorical.uniform
    (privateResidualLaw p)).symm
  have h₂ := (Measure.measurePreserving_swap (μ := μ)
    (ν := ContinuousCategorical.uniform)).prod
      (MeasurePreserving.id (privateResidualLaw p))
  have h₃ := measurePreserving_prodAssoc ContinuousCategorical.uniform μ
    (privateResidualLaw p)
  have h := h₃.comp (h₂.comp (h₁.comp hprod))
  convert h using 1
  funext z
  rfl

abbrev SampledResidual (p : Parameters) := CompleteRows p × PrivateResidual p

/-- Residual law for the independently sampled whole published row family
and all private labels other than the original J scalar. -/
@[expose] def sampledResidualLaw (p : Parameters) : Measure (SampledResidual p) :=
  completeRowsMeasure p |>.prod (privateResidualLaw p)

instance sampledResidualLaw_probability (p : Parameters) :
    IsProbabilityMeasure (sampledResidualLaw p) := by
  dsimp [sampledResidualLaw]
  infer_instance

/-- Exact pullback of a J-indexed initialization event from an independent
complete-row family to the accepted fixed-selected-row product law. The only
row law used is the existing whole-family evaluation law. -/
theorem completeFamily_index_event_pullback
    {p : Parameters} {β : Type*} [MeasurableSpace β]
    (f : CompleteRow p → ExtendedPrivateCoordinates p → β)
    (hFixed : Measurable (fun z : CompleteRow p × ExtendedPrivateCoordinates p =>
      f z.1 z.2))
    (hinv : ∀ row q s t,
      f row (insertScalarResidual (s, q)) = f row (insertScalarResidual (t, q)))
    (j : Fin (M p)) (A : Set β) (hA : MeasurableSet A) :
    (completeRowsMeasure p).prod (extendedPrivateLaw p)
        {z | coordinatorIndex p z.2.1.2 = j ∧
          f (z.1 (coordinatorIndex p z.2.1.2)) z.2 ∈ A} =
      ENNReal.ofReal (1 / (M p : ℝ)) *
        GeneratedBootstrapRoundLaw.originalLaw p {z | f z.1 z.2 ∈ A} := by
  let s₀ : Scalar := ⟨0, by norm_num⟩
  let atom : Set Scalar := {s | coordinatorIndex p s = j}
  let familyEvent : Set (SampledResidual p) :=
    {w | f (w.1 j) (insertScalarResidual (s₀, w.2)) ∈ A}
  let rowEvent : Set (CompleteRow p × PrivateResidual p) :=
    {w | f w.1 (insertScalarResidual (s₀, w.2)) ∈ A}
  have hAtom : MeasurableSet atom :=
    PrivateSourceStreams.measurable_coordinatorIndex p (measurableSet_singleton j)
  have hRestore : Measurable (fun q : PrivateResidual p =>
      insertScalarResidual (s₀, q)) :=
    (measurable_fst.prodMk measurable_const).prodMk measurable_snd
  have hFamilyEval : Measurable (fun w : SampledResidual p =>
      (w.1 j, insertScalarResidual (s₀, w.2))) := by
    have hrow : Measurable (fun w : SampledResidual p => w.1 j) :=
      (CompletePublicTable.measurable_completeRowProjection p j).comp measurable_fst
    exact hrow.prodMk (hRestore.comp measurable_snd)
  have hFamilyEvent : MeasurableSet familyEvent := hFixed.comp hFamilyEval hA
  have hRowEval : Measurable (fun w : CompleteRow p × PrivateResidual p =>
      (w.1, insertScalarResidual (s₀, w.2))) :=
    measurable_fst.prodMk (hRestore.comp measurable_snd)
  have hRowEvent : MeasurableSet rowEvent := hFixed.comp hRowEval hA
  have hpreFamily : liftScalarResidual (p := p) ⁻¹' (atom ×ˢ familyEvent) =
      {z : CompleteRows p × ExtendedPrivateCoordinates p |
        coordinatorIndex p z.2.1.2 = j ∧
          f (z.1 (coordinatorIndex p z.2.1.2)) z.2 ∈ A} := by
    ext z
    rcases z with ⟨rows, ⟨⟨blocks, scalar⟩, extra⟩⟩
    simp only [Set.mem_preimage, Set.mem_prod, atom, familyEvent,
      liftScalarResidual, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hj, hfa⟩
      refine ⟨hj, ?_⟩
      have hrow : rows (coordinatorIndex p scalar) = rows j := congrArg rows hj
      have hval : f (rows j) (insertScalarResidual (scalar, (blocks, extra))) ∈ A :=
        (hinv (rows j) (blocks, extra) scalar s₀).symm ▸ hfa
      exact hrow.symm ▸ hval
    · rintro ⟨hj, hfa⟩
      refine ⟨hj, ?_⟩
      have hrow : rows (coordinatorIndex p scalar) = rows j := congrArg rows hj
      have hval : f (rows j) (insertScalarResidual (scalar, (blocks, extra))) ∈ A :=
        hrow ▸ hfa
      exact (hinv (rows j) (blocks, extra) scalar s₀) ▸ hval
  have hpreRow : liftScalarResidual (p := p) ⁻¹' (Set.univ ×ˢ rowEvent) =
      {z : CompleteRow p × ExtendedPrivateCoordinates p | f z.1 z.2 ∈ A} := by
    ext z
    rcases z with ⟨row, ⟨⟨blocks, scalar⟩, extra⟩⟩
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, true_and, rowEvent,
      liftScalarResidual, Set.mem_setOf_eq]
    exact ⟨fun h => (hinv row (blocks, extra) scalar s₀).symm ▸ h,
      fun h => (hinv row (blocks, extra) scalar s₀) ▸ h⟩
  have hSample := measurePreserving_liftScalarResidual p (completeRowsMeasure p)
  have hOriginal := measurePreserving_liftScalarResidual p (completeRowMeasure p)
  have hFamilyRect : MeasurableSet (atom ×ˢ familyEvent) := hAtom.prod hFamilyEvent
  have hRowRect : MeasurableSet ((Set.univ : Set Scalar) ×ˢ rowEvent) :=
    MeasurableSet.univ.prod hRowEvent
  have hLeft :
      (completeRowsMeasure p).prod (extendedPrivateLaw p)
          {z | coordinatorIndex p z.2.1.2 = j ∧
            f (z.1 (coordinatorIndex p z.2.1.2)) z.2 ∈ A} =
        ContinuousCategorical.uniform atom * sampledResidualLaw p familyEvent := by
    calc
      _ = ((completeRowsMeasure p).prod (extendedPrivateLaw p)).map
            (liftScalarResidual (p := p)) (atom ×ˢ familyEvent) := by
              rw [← hpreFamily, Measure.map_apply hSample.measurable hFamilyRect]
      _ = ContinuousCategorical.uniform atom * sampledResidualLaw p familyEvent := by
              rw [hSample.map_eq, Measure.prod_prod]
              rfl
  have hOriginalMass : GeneratedBootstrapRoundLaw.originalLaw p
      {z | f z.1 z.2 ∈ A} =
        ContinuousCategorical.uniform Set.univ *
          (completeRowMeasure p |>.prod (privateResidualLaw p)) rowEvent := by
    calc
      _ = (GeneratedBootstrapRoundLaw.originalLaw p).map
            (liftScalarResidual (p := p)) (Set.univ ×ˢ rowEvent) := by
              rw [← hpreRow, Measure.map_apply hOriginal.measurable hRowRect]
      _ = ContinuousCategorical.uniform Set.univ *
            (completeRowMeasure p |>.prod (privateResidualLaw p)) rowEvent := by
              change ((completeRowMeasure p).prod (extendedPrivateLaw p)).map
                (liftScalarResidual (p := p)) (Set.univ ×ˢ rowEvent) = _
              rw [hOriginal.map_eq, Measure.prod_prod]
  have hEval : MeasurePreserving
      (fun w : SampledResidual p => (w.1 j, w.2)) (sampledResidualLaw p)
      (completeRowMeasure p |>.prod (privateResidualLaw p)) := by
    exact (CompletePublicTable.measurePreserving_completeRowProjection p j).prod
      (MeasurePreserving.id (privateResidualLaw p))
  have hEvalSet :
      (fun w : SampledResidual p => (w.1 j, w.2)) ⁻¹' rowEvent = familyEvent := by
    ext w
    rfl
  have hEvalMass : sampledResidualLaw p familyEvent =
      (completeRowMeasure p |>.prod (privateResidualLaw p)) rowEvent := by
    calc
      _ = (sampledResidualLaw p).map (fun w : SampledResidual p => (w.1 j, w.2)) rowEvent := by
            rw [← hEvalSet, Measure.map_apply hEval.measurable hRowEvent]
      _ = _ := by rw [hEval.map_eq]
  have hAtom : ContinuousCategorical.uniform atom =
      ENNReal.ofReal (1 / (M p : ℝ)) := by
    have hset : atom = coordinatorIndex p ⁻¹' {j} := by
      ext s
      simp [atom]
    rw [hset]
    exact PrivateSourceStreams.coordinatorIndex_uniform_atom p j
  calc
    (completeRowsMeasure p).prod (extendedPrivateLaw p)
        {z | coordinatorIndex p z.2.1.2 = j ∧
          f (z.1 (coordinatorIndex p z.2.1.2)) z.2 ∈ A} =
      ContinuousCategorical.uniform atom * sampledResidualLaw p familyEvent := hLeft
    _ = ENNReal.ofReal (1 / (M p : ℝ)) *
        GeneratedBootstrapRoundLaw.originalLaw p {z | f z.1 z.2 ∈ A} := by
      rw [hAtom, hEvalMass, hOriginalMass, ContinuousCategorical.uniform_univ]
      simp

/-- Exact Borel-event disintegration for the actual private initialization
output with a fixed full row family. The J event uses the same original
continuous coordinator scalar used to select `R(J(e))`. -/
theorem actualOutput_event_disintegration (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (rows : CompleteRows p)
    (j : Fin (M p)) (A : Set (Boundary p)) (hA : MeasurableSet A) :
    extendedPrivateLaw p
        {e | coordinatorIndex p e.1.2 = j ∧ actualOutput p ids rewards C_star C_h eta rows e ∈ A} =
      ENNReal.ofReal (1 / (M p : ℝ)) *
        extendedPrivateLaw p
          {e | fixedRowOutput p ids rewards C_star C_h eta (rows j) e ∈ A} := by
  have hset : {e : ExtendedPrivateCoordinates p |
      coordinatorIndex p e.1.2 = j ∧ actualOutput p ids rewards C_star C_h eta rows e ∈ A} =
      {e | coordinatorIndex p e.1.2 = j ∧
        fixedRowOutput p ids rewards C_star C_h eta (rows j) e ∈ A} := by
    ext e
    simp only [Set.mem_setOf_eq, actualOutput, fixedRowOutput, fixedRowInput]
    by_cases hj : coordinatorIndex p e.1.2 = j
    · simp [hj]
    · simp [hj]
  rw [hset]
  exact coordinatorIndex_event_disintegration
    (f := fixedRowOutput p ids rewards C_star C_h eta (rows j))
    (hf := measurable_fixedRowOutput p ids rewards C_star C_h eta (rows j))
    (hinv := fun q s t => fixedRow_scalar_invariant_output p ids rewards C_star C_h eta
      (rows j) q s t) j A hA

/-- Exact Borel-event disintegration for the actual launch round, preserving
the existing `T+1` no-launch sentinel. -/
theorem actualLaunchRound_event_disintegration (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (rows : CompleteRows p)
    (j : Fin (M p)) (A : Set ℕ) (hA : MeasurableSet A) :
    extendedPrivateLaw p
        {e | coordinatorIndex p e.1.2 = j ∧ actualLaunchRound p ids rewards C_star C_h eta rows e ∈ A} =
      ENNReal.ofReal (1 / (M p : ℝ)) *
        extendedPrivateLaw p
          {e | fixedRowLaunchRound p ids rewards C_star C_h eta (rows j) e ∈ A} := by
  have hset : {e : ExtendedPrivateCoordinates p |
      coordinatorIndex p e.1.2 = j ∧ actualLaunchRound p ids rewards C_star C_h eta rows e ∈ A} =
      {e | coordinatorIndex p e.1.2 = j ∧
        fixedRowLaunchRound p ids rewards C_star C_h eta (rows j) e ∈ A} := by
    ext e
    simp only [Set.mem_setOf_eq, actualLaunchRound, fixedRowLaunchRound, fixedRowInput]
    by_cases hj : coordinatorIndex p e.1.2 = j
    · simp [hj]
    · simp [hj]
  rw [hset]
  exact coordinatorIndex_event_disintegration
    (f := fixedRowLaunchRound p ids rewards C_star C_h eta (rows j))
    (hf := measurable_fixedRowLaunchRound p ids rewards C_star C_h eta (rows j))
    (hinv := fun q s t => fixedRow_scalar_invariant_launch p ids rewards C_star C_h eta
      (rows j) q s t) j A hA

/-- Pullback of an initialization output event to independently sampled whole
complete rows. It uses the existing evaluation law for `R(j)` and retains the
entire original private-coordinate product. -/
theorem actualOutput_completeFamily_event_pullback (p : Parameters)
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (j : Fin (M p)) (A : Set (Boundary p)) (hA : MeasurableSet A) :
    (completeRowsMeasure p).prod (extendedPrivateLaw p)
        {z | coordinatorIndex p z.2.1.2 = j ∧
          actualOutput p ids rewards C_star C_h eta z.1 z.2 ∈ A} =
      ENNReal.ofReal (1 / (M p : ℝ)) *
        GeneratedBootstrapRoundLaw.originalLaw p
          {z | fixedRowOutput p ids rewards C_star C_h eta z.1 z.2 ∈ A} := by
  exact completeFamily_index_event_pullback
    (f := fixedRowOutput p ids rewards C_star C_h eta)
    (hFixed := measurable_fixedRowOutput_pair p ids rewards C_star C_h eta)
    (hinv := fun row q s t => fixedRow_scalar_invariant_output p ids rewards C_star C_h
      eta row q s t) j A hA

/-- Pullback of an initialization launch event to independently sampled whole
complete rows. The sentinel remains the actual source value `T+1`. -/
theorem actualLaunchRound_completeFamily_event_pullback (p : Parameters)
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (j : Fin (M p)) (A : Set ℕ) (hA : MeasurableSet A) :
    (completeRowsMeasure p).prod (extendedPrivateLaw p)
        {z | coordinatorIndex p z.2.1.2 = j ∧
          actualLaunchRound p ids rewards C_star C_h eta z.1 z.2 ∈ A} =
      ENNReal.ofReal (1 / (M p : ℝ)) *
        GeneratedBootstrapRoundLaw.originalLaw p
          {z | fixedRowLaunchRound p ids rewards C_star C_h eta z.1 z.2 ∈ A} := by
  exact completeFamily_index_event_pullback
    (f := fixedRowLaunchRound p ids rewards C_star C_h eta)
    (hFixed := measurable_fixedRowLaunchRound_pair p ids rewards C_star C_h eta)
    (hinv := fun row q s t => fixedRow_scalar_invariant_launch p ids rewards C_star C_h
      eta row q s t) j A hA

/-- Pushforward form of fixed-family output disintegration, on the event that
the original coordinator scalar selected `j`. -/
theorem actualOutput_restricted_map_eq_smul (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (rows : CompleteRows p)
    (j : Fin (M p)) :
    ((extendedPrivateLaw p).restrict {e | coordinatorIndex p e.1.2 = j}).map
        (actualOutput p ids rewards C_star C_h eta rows) =
      ENNReal.ofReal (1 / (M p : ℝ)) • (extendedPrivateLaw p).map
        (fixedRowOutput p ids rewards C_star C_h eta (rows j)) := by
  exact coordinatorIndex_restricted_map_eq_smul
    (actualOutput p ids rewards C_star C_h eta rows)
    (fixedRowOutput p ids rewards C_star C_h eta (rows j))
    (measurable_actualOutput p ids rewards C_star C_h eta rows)
    (measurable_fixedRowOutput p ids rewards C_star C_h eta (rows j)) j
    (fun A hA => actualOutput_event_disintegration p ids rewards C_star C_h eta rows j A hA)

/-- Pushforward form of fixed-family launch disintegration. The no-launch value
is unchanged and remains exactly `T+1`. -/
theorem actualLaunchRound_restricted_map_eq_smul (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (rows : CompleteRows p)
    (j : Fin (M p)) :
    ((extendedPrivateLaw p).restrict {e | coordinatorIndex p e.1.2 = j}).map
        (actualLaunchRound p ids rewards C_star C_h eta rows) =
      ENNReal.ofReal (1 / (M p : ℝ)) • (extendedPrivateLaw p).map
        (fixedRowLaunchRound p ids rewards C_star C_h eta (rows j)) := by
  exact coordinatorIndex_restricted_map_eq_smul
    (actualLaunchRound p ids rewards C_star C_h eta rows)
    (fixedRowLaunchRound p ids rewards C_star C_h eta (rows j))
    (measurable_actualLaunchRound p ids rewards C_star C_h eta rows)
    (measurable_fixedRowLaunchRound p ids rewards C_star C_h eta (rows j)) j
    (fun A hA => actualLaunchRound_event_disintegration p ids rewards C_star C_h eta rows j A hA)

/-- Integrable actual and fixed-row output tests, together with their exact
private J-atom integral disintegration. Boundedness is given by literal finite
lower and upper bounds for the real test. -/
theorem actualOutput_bounded_test_disintegration (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (rows : CompleteRows p)
    (j : Fin (M p)) (φ : Boundary p → ℝ) (hφ : Measurable φ)
    (lo hi : ℝ) (hbound : ∀ b, φ b ∈ Set.Icc lo hi) :
    Integrable (fun e => φ (actualOutput p ids rewards C_star C_h eta rows e))
        ((extendedPrivateLaw p).restrict {e | coordinatorIndex p e.1.2 = j}) ∧
      Integrable (fun e => φ (fixedRowOutput p ids rewards C_star C_h eta (rows j) e))
        (extendedPrivateLaw p) ∧
      (∫ e in {e | coordinatorIndex p e.1.2 = j},
          φ (actualOutput p ids rewards C_star C_h eta rows e) ∂extendedPrivateLaw p =
        (1 / (M p : ℝ)) * ∫ e,
          φ (fixedRowOutput p ids rewards C_star C_h eta (rows j) e) ∂extendedPrivateLaw p) := by
  have h := bounded_test_integral_of_restricted_map_eq_smul
    (extendedPrivateLaw p) {e | coordinatorIndex p e.1.2 = j}
    (actualOutput p ids rewards C_star C_h eta rows)
    (fixedRowOutput p ids rewards C_star C_h eta (rows j))
    (measurable_actualOutput p ids rewards C_star C_h eta rows)
    (measurable_fixedRowOutput p ids rewards C_star C_h eta (rows j))
    (ENNReal.ofReal (1 / (M p : ℝ)))
    (actualOutput_restricted_map_eq_smul p ids rewards C_star C_h eta rows j)
    φ hφ lo hi hbound
  rcases h with ⟨hleft, hright, hformula⟩
  have hc : (ENNReal.ofReal (1 / (M p : ℝ))).toReal = 1 / (M p : ℝ) := by
    rw [ENNReal.toReal_ofReal]
    positivity
  exact ⟨hleft, hright, by simpa only [hc] using hformula⟩

/-- Integrable actual and fixed-row launch tests, with the unchanged source
sentinel and exact J-atom integral disintegration. -/
theorem actualLaunchRound_bounded_test_disintegration (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (rows : CompleteRows p)
    (j : Fin (M p)) (φ : ℕ → ℝ) (hφ : Measurable φ)
    (lo hi : ℝ) (hbound : ∀ n, φ n ∈ Set.Icc lo hi) :
    Integrable (fun e => φ (actualLaunchRound p ids rewards C_star C_h eta rows e))
        ((extendedPrivateLaw p).restrict {e | coordinatorIndex p e.1.2 = j}) ∧
      Integrable (fun e => φ (fixedRowLaunchRound p ids rewards C_star C_h eta (rows j) e))
        (extendedPrivateLaw p) ∧
      (∫ e in {e | coordinatorIndex p e.1.2 = j},
          φ (actualLaunchRound p ids rewards C_star C_h eta rows e) ∂extendedPrivateLaw p =
        (1 / (M p : ℝ)) * ∫ e,
          φ (fixedRowLaunchRound p ids rewards C_star C_h eta (rows j) e) ∂extendedPrivateLaw p) := by
  have h := bounded_test_integral_of_restricted_map_eq_smul
    (extendedPrivateLaw p) {e | coordinatorIndex p e.1.2 = j}
    (actualLaunchRound p ids rewards C_star C_h eta rows)
    (fixedRowLaunchRound p ids rewards C_star C_h eta (rows j))
    (measurable_actualLaunchRound p ids rewards C_star C_h eta rows)
    (measurable_fixedRowLaunchRound p ids rewards C_star C_h eta (rows j))
    (ENNReal.ofReal (1 / (M p : ℝ)))
    (actualLaunchRound_restricted_map_eq_smul p ids rewards C_star C_h eta rows j)
    φ hφ lo hi hbound
  rcases h with ⟨hleft, hright, hformula⟩
  have hc : (ENNReal.ofReal (1 / (M p : ℝ))).toReal = 1 / (M p : ℝ) := by
    rw [ENNReal.toReal_ofReal]
    positivity
  exact ⟨hleft, hright, by simpa only [hc] using hformula⟩

/-- Summing the J atoms recovers the finite uniform mixture of fixed-row
initialization event probabilities for one fixed full row family. -/
theorem actualOutput_finite_uniform_average (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (rows : CompleteRows p)
    (A : Set (Boundary p)) (hA : MeasurableSet A) :
    extendedPrivateLaw p {e | actualOutput p ids rewards C_star C_h eta rows e ∈ A} =
      ∑ j : Fin (M p), ENNReal.ofReal (1 / (M p : ℝ)) *
        extendedPrivateLaw p
          {e | fixedRowOutput p ids rewards C_star C_h eta (rows j) e ∈ A} := by
  let event : Fin (M p) → Set (ExtendedPrivateCoordinates p) := fun j =>
    {e | coordinatorIndex p e.1.2 = j ∧
      actualOutput p ids rewards C_star C_h eta rows e ∈ A}
  have hJ : Measurable (fun e : ExtendedPrivateCoordinates p =>
      coordinatorIndex p e.1.2) :=
    (PrivateSourceStreams.measurable_coordinatorIndex p).comp
      (measurable_snd.comp measurable_fst)
  have hmeas : ∀ j, MeasurableSet (event j) := by
    intro j
    exact (hJ (measurableSet_singleton j)).inter
      ((measurable_actualOutput p ids rewards C_star C_h eta rows) hA)
  have hdisj : Pairwise (fun j k => Disjoint (event j) (event k)) := by
    intro j k hjk
    apply Set.disjoint_left.mpr
    intro e he₁ he₂
    exact hjk (he₁.1.symm.trans he₂.1)
  have hunion : {e : ExtendedPrivateCoordinates p |
      actualOutput p ids rewards C_star C_h eta rows e ∈ A} = ⋃ j, event j := by
    ext e
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, event]
    constructor
    · intro he
      exact ⟨coordinatorIndex p e.1.2, rfl, he⟩
    · rintro ⟨j, hj, he⟩
      exact he
  calc
    extendedPrivateLaw p {e | actualOutput p ids rewards C_star C_h eta rows e ∈ A} =
        ∑' j : Fin (M p), extendedPrivateLaw p (event j) := by
          rw [hunion, measure_iUnion hdisj hmeas]
    _ = ∑ j : Fin (M p), ENNReal.ofReal (1 / (M p : ℝ)) *
          extendedPrivateLaw p
            {e | fixedRowOutput p ids rewards C_star C_h eta (rows j) e ∈ A} := by
          rw [tsum_fintype]
          apply Finset.sum_congr rfl
          intro j hj
          exact actualOutput_event_disintegration p ids rewards C_star C_h eta rows j A hA

/-- Summing launch-index atoms recovers the finite uniform mixture of
fixed-row launch laws, retaining the `T+1` sentinel. -/
theorem actualLaunchRound_finite_uniform_average (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (rows : CompleteRows p)
    (A : Set ℕ) (hA : MeasurableSet A) :
    extendedPrivateLaw p {e | actualLaunchRound p ids rewards C_star C_h eta rows e ∈ A} =
      ∑ j : Fin (M p), ENNReal.ofReal (1 / (M p : ℝ)) *
        extendedPrivateLaw p
          {e | fixedRowLaunchRound p ids rewards C_star C_h eta (rows j) e ∈ A} := by
  let event : Fin (M p) → Set (ExtendedPrivateCoordinates p) := fun j =>
    {e | coordinatorIndex p e.1.2 = j ∧
      actualLaunchRound p ids rewards C_star C_h eta rows e ∈ A}
  have hJ : Measurable (fun e : ExtendedPrivateCoordinates p =>
      coordinatorIndex p e.1.2) :=
    (PrivateSourceStreams.measurable_coordinatorIndex p).comp
      (measurable_snd.comp measurable_fst)
  have hmeas : ∀ j, MeasurableSet (event j) := by
    intro j
    exact (hJ (measurableSet_singleton j)).inter
      ((measurable_actualLaunchRound p ids rewards C_star C_h eta rows) hA)
  have hdisj : Pairwise (fun j k => Disjoint (event j) (event k)) := by
    intro j k hjk
    apply Set.disjoint_left.mpr
    intro e he₁ he₂
    exact hjk (he₁.1.symm.trans he₂.1)
  have hunion : {e : ExtendedPrivateCoordinates p |
      actualLaunchRound p ids rewards C_star C_h eta rows e ∈ A} = ⋃ j, event j := by
    ext e
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, event]
    constructor
    · intro he
      exact ⟨coordinatorIndex p e.1.2, rfl, he⟩
    · rintro ⟨j, hj, he⟩
      exact he
  calc
    extendedPrivateLaw p {e | actualLaunchRound p ids rewards C_star C_h eta rows e ∈ A} =
        ∑' j : Fin (M p), extendedPrivateLaw p (event j) := by
          rw [hunion, measure_iUnion hdisj hmeas]
    _ = ∑ j : Fin (M p), ENNReal.ofReal (1 / (M p : ℝ)) *
          extendedPrivateLaw p
            {e | fixedRowLaunchRound p ids rewards C_star C_h eta (rows j) e ∈ A} := by
          rw [tsum_fintype]
          apply Finset.sum_congr rfl
          intro j hj
          exact actualLaunchRound_event_disintegration p ids rewards C_star C_h eta rows j A hA

end Bandits.Support.ReferenceInitializationIndexMixture

end
