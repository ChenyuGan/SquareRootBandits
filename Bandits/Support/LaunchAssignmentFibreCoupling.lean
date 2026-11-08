/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.LaunchAssignmentCoordinateSplit
public import Bandits.Support.FiniteFibreLift
public import Bandits.Support.CanonicalAssignmentVector
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# First reference launch assignment-fibre coupling

At a fixed nonterminal actual reference launch and an arbitrary measurable
event of its accepted joint past, this module lifts the exact unit-weight
canonical slow-set marginal through the existing full-vector fibre kernel.
The second marginal is the restriction of the original complete-row and
private-coordinate law to the actual launch-and-past event, including when
that event is null. The assignment vector retains its final orientation scalar.

This is the first-launch internal reconstruction only. It does not define a
physical protocol or a later adaptive assignment law.

Sources: `sources/zip4/manuscript/06_interruptions.tex:397-423`,
`sources/zip4/manuscript/07_public_setup.tex:123-164`, and
`sources/zip4/manuscript/appendix_b_communication.tex:25-58,786-798`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.CompletePublicTable
open Bandits.Support.CompleteRowStoppingLaw
open Bandits.Support.ContinuousControlSlice
open Bandits.Support.CanonicalOrientedSetLaw
open Bandits.Support.CanonicalAssignmentVector
open Bandits.Support.LaunchAssignmentCoordinateSplit
open Bandits.Support.ReferenceLaunchJointFutureLaw
open Bandits.Support.ReferenceLaunchAssignmentLaw
open Bandits.Support.ReferenceLaunchPrivateRoundLaw
open Bandits.Support.ReferenceInitializationRun
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.CanonicalRecordingRates
open scoped ENNReal BigOperators

namespace Bandits.Support.LaunchAssignmentFibreCoupling

abbrev Parameters := ConstructorDimensions.Parameters
abbrev LearningRate := ReferencePrelaunchFollower.LearningRate
abbrev LaunchIndex (p : Parameters) := Fin (p.T + 1)
abbrev SlowSet (p : Parameters) := CanonicalOrientedSetLaw.SlowSet p.K p.m
abbrev AssignmentVector (p : Parameters) :=
  LaunchAssignmentCoordinateSplit.AssignmentVector p
abbrev Remainder (p : Parameters) (σ : LaunchIndex p) :=
  LaunchAssignmentCoordinateSplit.Remainder p σ
abbrev Past (p : Parameters) (σ : LaunchIndex p) :=
  ReferenceLaunchJointFutureLaw.JointPast p σ
abbrev Future (p : Parameters) (σ : LaunchIndex p) :=
  ReferenceLaunchJointFutureLaw.JointFuture p σ
abbrev Original (p : Parameters) :=
  ReferenceLaunchJointFutureLaw.OriginalCoordinates p

local instance slowSetMeasurableSpace (K m : ℕ) :
    MeasurableSpace (CanonicalOrientedSetLaw.SlowSet K m) := ⊤

/-- The exact existing canonical sampler used by the first reference start:
all current and anchor weights are one, and the input is the whole `K+1`
assignment cube, including the orientation scalar at `Fin.last K`.

Source: `sources/zip4/manuscript/06_interruptions.tex:410-423` and
`sources/zip4/manuscript/appendix_b_communication.tex:42-44`.
-/
@[expose] noncomputable def firstLaunchSampler (p : Parameters) :
    AssignmentVector p → SlowSet p :=
  CanonicalAssignmentVector.canonicalSlowSampler p.two_le_m p.m_lt_K
    (fun _ => 1) (fun _ => 1) (by intro i; norm_num) (by intro i; norm_num)

/-- The canonical finite slow-set mass, read from the accepted canonical
slow marginal rather than supplied as a probability parameter.
-/
@[expose] noncomputable def slowSetMass (p : Parameters) (U : SlowSet p) : ℝ≥0∞ :=
  ENNReal.ofReal (CanonicalOrientedSetLaw.slowMarginal (fun _ => 1) (fun _ => 1)
    p.two_le_m p.m_lt_K (by intro i; norm_num) (by intro i; norm_num) U)

theorem measurable_firstLaunchSampler (p : Parameters) :
    Measurable (firstLaunchSampler p) :=
  CanonicalAssignmentVector.measurable_canonicalSlowSampler p.two_le_m p.m_lt_K
    (fun _ => 1) (fun _ => 1) (by intro i; norm_num) (by intro i; norm_num)

theorem slowSetMass_eq_fibreMass (p : Parameters) (U : SlowSet p) :
    slowSetMass p U = FiniteFibreLift.fibreMass
      (ContinuousControlSlice.assignmentLaw p.K) (firstLaunchSampler p) U := by
  exact (CanonicalAssignmentVector.canonicalSlowSampler_fibreMass
    p.two_le_m p.m_lt_K (fun _ => 1) (fun _ => 1)
    (by intro i; norm_num) (by intro i; norm_num) U).symm

theorem slowSetMass_pos (p : Parameters) (U : SlowSet p) : 0 < slowSetMass p U := by
  rw [slowSetMass]
  exact ENNReal.ofReal_pos.mpr
    (CanonicalOrientedSetLaw.slowMarginal_pos (fun _ => 1) (fun _ => 1)
      p.two_le_m p.m_lt_K (by intro i; norm_num) (by intro i; norm_num) U)

theorem slowSetMass_ne_zero (p : Parameters) (U : SlowSet p) : slowSetMass p U ≠ 0 :=
  (slowSetMass_pos p U).ne'

theorem slowSetMass_eq_canonicalPMF (p : Parameters) (U : SlowSet p) :
    slowSetMass p U =
      (CanonicalOrientedSetLaw.slowSetPMF (fun _ => 1) (fun _ => 1)
        p.two_le_m p.m_lt_K (by intro i; norm_num) (by intro i; norm_num)).toMeasure {U} := by
  rw [slowSetMass,
    (CanonicalOrientedSetLaw.slowSetPMF (fun _ => 1) (fun _ => 1)
      p.two_le_m p.m_lt_K (by intro i; norm_num) (by intro i; norm_num)).toMeasure_apply_singleton
        U (measurableSet_singleton U), CanonicalOrientedSetLaw.slowSetPMF_apply]

/-- The sampler's full finite-outcome mass is its canonical slow marginal. -/
theorem sampler_fibreMass_eq_slowSetMass (p : Parameters) (U : SlowSet p) :
    FiniteFibreLift.fibreMass (ContinuousControlSlice.assignmentLaw p.K)
      (firstLaunchSampler p) U = slowSetMass p U :=
  (slowSetMass_eq_fibreMass p U).symm

/-- The original accepted joint future law, conditioned on the canonical
full-vector fibre by the existing finite-fibre kernel and then reconstructed
through the accepted remainder inverse.
-/
@[expose] noncomputable def futureFibreMeasure (p : Parameters) (σ : LaunchIndex p)
    (hσ : σ.val < p.T) (U : SlowSet p) : Measure (Future p σ) :=
  ((FiniteFibreLift.fibreMeasure (ContinuousControlSlice.assignmentLaw p.K)
      (firstLaunchSampler p) U).prod (LaunchAssignmentCoordinateSplit.remainderLaw p σ)).map
    (LaunchAssignmentCoordinateSplit.jointFutureCoordinateSplitEquiv p σ hσ).symm

instance futureFibreMeasure_probability (p : Parameters) (σ : LaunchIndex p)
    (hσ : σ.val < p.T) (U : SlowSet p) :
    IsProbabilityMeasure (futureFibreMeasure p σ hσ U) := by
  dsimp [futureFibreMeasure]
  infer_instance

/-- The weighted mixture of all literal reconstructed fibre futures is the
entire accepted joint future measure.
-/
theorem futureFibreMeasure_mixture (p : Parameters) (σ : LaunchIndex p)
    (hσ : σ.val < p.T) :
    (∑ U : SlowSet p, slowSetMass p U • futureFibreMeasure p σ hσ U) =
      ReferenceLaunchJointFutureLaw.jointFutureLaw p σ := by
  classical
  let e := LaunchAssignmentCoordinateSplit.jointFutureCoordinateSplitEquiv p σ hσ
  have hfibre :
      (∑ U : SlowSet p, slowSetMass p U •
        FiniteFibreLift.fibreMeasure (ContinuousControlSlice.assignmentLaw p.K)
          (firstLaunchSampler p) U) = ContinuousControlSlice.assignmentLaw p.K := by
    simpa [slowSetMass, firstLaunchSampler] using
      CanonicalAssignmentVector.canonicalSlowSampler_fibre_mixture
        p.two_le_m p.m_lt_K (fun _ => 1) (fun _ => 1)
        (by intro i; norm_num) (by intro i; norm_num)
  have hprod :
      (∑ U : SlowSet p, slowSetMass p U •
        (FiniteFibreLift.fibreMeasure (ContinuousControlSlice.assignmentLaw p.K)
          (firstLaunchSampler p) U).prod
          (LaunchAssignmentCoordinateSplit.remainderLaw p σ)) =
        (ContinuousControlSlice.assignmentLaw p.K).prod
          (LaunchAssignmentCoordinateSplit.remainderLaw p σ) := by
    calc
      _ = ∑ U : SlowSet p,
          (slowSetMass p U •
            FiniteFibreLift.fibreMeasure (ContinuousControlSlice.assignmentLaw p.K)
              (firstLaunchSampler p) U).prod
            (LaunchAssignmentCoordinateSplit.remainderLaw p σ) := by
        apply Finset.sum_congr rfl
        intro U hU
        rw [Measure.prod_smul_left]
      _ = Measure.sum (fun U : SlowSet p =>
          (slowSetMass p U •
            FiniteFibreLift.fibreMeasure (ContinuousControlSlice.assignmentLaw p.K)
              (firstLaunchSampler p) U).prod
            (LaunchAssignmentCoordinateSplit.remainderLaw p σ)) := by
        rw [← Measure.sum_fintype]
      _ = (Measure.sum (fun U : SlowSet p => slowSetMass p U •
          FiniteFibreLift.fibreMeasure (ContinuousControlSlice.assignmentLaw p.K)
            (firstLaunchSampler p) U)).prod
            (LaunchAssignmentCoordinateSplit.remainderLaw p σ) :=
        (Measure.prod_sum_left _ _).symm
      _ = (∑ U : SlowSet p, slowSetMass p U •
          FiniteFibreLift.fibreMeasure (ContinuousControlSlice.assignmentLaw p.K)
            (firstLaunchSampler p) U).prod
            (LaunchAssignmentCoordinateSplit.remainderLaw p σ) := by
        rw [Measure.sum_fintype]
      _ = _ := by rw [hfibre]
  calc
    _ = ((∑ U : SlowSet p, slowSetMass p U •
        (FiniteFibreLift.fibreMeasure (ContinuousControlSlice.assignmentLaw p.K)
          (firstLaunchSampler p) U).prod
          (LaunchAssignmentCoordinateSplit.remainderLaw p σ)).map e.symm) := by
        have hmap := Measure.map_sum
          (m := fun U : SlowSet p => slowSetMass p U •
            (FiniteFibreLift.fibreMeasure (ContinuousControlSlice.assignmentLaw p.K)
              (firstLaunchSampler p) U).prod
              (LaunchAssignmentCoordinateSplit.remainderLaw p σ))
          (f := e.symm) e.symm.measurable.aemeasurable
        simpa only [Measure.sum_fintype,
          Measure.map_smul _ e.symm.measurable.aemeasurable,
          futureFibreMeasure, e] using hmap.symm
    _ = ((ContinuousControlSlice.assignmentLaw p.K).prod
        (LaunchAssignmentCoordinateSplit.remainderLaw p σ)).map e.symm := by rw [hprod]
    _ = ReferenceLaunchJointFutureLaw.jointFutureLaw p σ := by
      have hmap :=
        (LaunchAssignmentCoordinateSplit.measurePreserving_jointFutureCoordinateSplitEquiv
          p σ hσ).map_eq
      rw [← hmap, e.map_symm_map]

/-- The source event `L_A`: the actual launch round is `σ.val+1` and the
accepted joint past belongs to `A`. It carries no positive-probability
premise.
-/
@[expose] def launchAndPastEvent (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : LearningRate) (σ : LaunchIndex p) (A : Set (Past p σ)) : Set (Original p) :=
  {z | ReferenceInitializationRun.launchRound
        (ReferenceLaunchJointFutureLaw.actualInput p ids rewards C_star C_h eta z) =
          σ.val + 1 ∧
      (ReferenceLaunchJointFutureLaw.jointSplitEquiv p σ z).1 ∈ A}

theorem measurable_launchAndPastEvent (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : LearningRate) (σ : LaunchIndex p) (A : Set (Past p σ))
    (hA : MeasurableSet A) : MeasurableSet (launchAndPastEvent p ids rewards
      C_star C_h eta σ A) := by
  have hlaunch : MeasurableSet
      {z : Original p | ReferenceInitializationRun.launchRound
        (ReferenceLaunchJointFutureLaw.actualInput p ids rewards C_star C_h eta z) =
          σ.val + 1} :=
    (measurableSet_singleton (σ.val + 1)).preimage
      (ReferenceLaunchJointFutureLaw.measurable_sourceLaunchRound
        p ids rewards C_star C_h eta)
  have hpast : MeasurableSet
      {z : Original p | (ReferenceLaunchJointFutureLaw.jointSplitEquiv p σ z).1 ∈ A} :=
    hA.preimage (measurable_fst.comp
      (ReferenceLaunchJointFutureLaw.jointSplitEquiv p σ).measurable)
  exact hlaunch.inter hpast

/-- The enlarged-past form of the source launch-and-past event. -/
def launchPastSet (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : LearningRate) (σ : LaunchIndex p) (A : Set (Past p σ)) : Set (Past p σ) :=
  A ∩ {past | ReferenceLaunchJointFutureLaw.launchEventAt
    p ids rewards C_star C_h eta σ past = true}

theorem measurable_launchPastSet (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : LearningRate) (σ : LaunchIndex p) (A : Set (Past p σ))
    (hA : MeasurableSet A) : MeasurableSet (launchPastSet p ids rewards C_star C_h eta σ A) := by
  exact hA.inter ((measurableSet_singleton true).preimage
    (ReferenceLaunchJointFutureLaw.measurable_launchEventAt
      p ids rewards C_star C_h eta σ))

/-- The exact joint-past law restricted to the genuine source event. -/
@[expose] def restrictedLaunchPastLaw (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : LearningRate) (σ : LaunchIndex p) (A : Set (Past p σ)) : Measure (Past p σ) :=
  (ReferenceLaunchJointFutureLaw.jointPastLaw p σ).restrict
    (launchPastSet p ids rewards C_star C_h eta σ A)

theorem launchAndPastEvent_mass (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : LearningRate) (σ : LaunchIndex p) (A : Set (Past p σ))
    (hA : MeasurableSet A) :
    ReferenceLaunchJointFutureLaw.originalLaw p (launchAndPastEvent p ids rewards
        C_star C_h eta σ A) = restrictedLaunchPastLaw p ids rewards C_star C_h eta σ A Set.univ := by
  rw [restrictedLaunchPastLaw, Measure.restrict_apply_univ]
  exact ReferenceLaunchJointFutureLaw.actual_launch_past_event_mass
    p ids rewards C_star C_h eta σ A hA

theorem launchAndPastEvent_jointSplit_preimage (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : LearningRate) (σ : LaunchIndex p) (A : Set (Past p σ)) :
    launchAndPastEvent p ids rewards C_star C_h eta σ A =
      (ReferenceLaunchJointFutureLaw.jointSplitEquiv p σ) ⁻¹'
        (launchPastSet p ids rewards C_star C_h eta σ A ×ˢ Set.univ) := by
  ext z
  simp only [launchAndPastEvent, launchPastSet, Set.mem_setOf_eq, Set.mem_preimage,
    Set.mem_prod, Set.mem_inter_iff, Set.mem_univ, and_true]
  rw [ReferenceLaunchJointFutureLaw.launchEventAt_eq_true_iff]
  exact and_comm

/-- Reconstruct an original point from its unchanged joint past and the
full-vector fibre inverse with a remainder. -/
@[expose] def reconstructOriginal (p : Parameters) (σ : LaunchIndex p)
    (hσ : σ.val < p.T) (past : Past p σ) (v : AssignmentVector p)
    (rem : Remainder p σ) : Original p :=
  (ReferenceLaunchJointFutureLaw.jointSplitEquiv p σ).symm
    (past, (LaunchAssignmentCoordinateSplit.jointFutureCoordinateSplitEquiv p σ hσ).symm
      (v, rem))

theorem reconstructOriginal_jointSplit (p : Parameters) (σ : LaunchIndex p)
    (hσ : σ.val < p.T) (past : Past p σ) (v : AssignmentVector p)
    (rem : Remainder p σ) :
    ReferenceLaunchJointFutureLaw.jointSplitEquiv p σ
      (reconstructOriginal p σ hσ past v rem) =
        (past, (LaunchAssignmentCoordinateSplit.jointFutureCoordinateSplitEquiv p σ hσ).symm
          (v, rem)) := by
  exact (ReferenceLaunchJointFutureLaw.jointSplitEquiv p σ).apply_symm_apply _

theorem reconstructOriginal_assignmentVector (p : Parameters) (σ : LaunchIndex p)
    (hσ : σ.val < p.T) (past : Past p σ) (v : AssignmentVector p)
    (rem : Remainder p σ) :
    LaunchAssignmentCoordinateSplit.originalAssignmentVectorAtLaunch p σ hσ
      (reconstructOriginal p σ hσ past v rem) = v := by
  rw [LaunchAssignmentCoordinateSplit.originalAssignmentVectorAtLaunch,
    reconstructOriginal_jointSplit]
  exact congrArg Prod.fst
    ((LaunchAssignmentCoordinateSplit.jointFutureCoordinateSplitEquiv p σ hσ).apply_symm_apply
      (v, rem))

theorem originalAssignmentVectorAtLaunch_reconstruct (p : Parameters)
    (σ : LaunchIndex p) (hσ : σ.val < p.T) (past : Past p σ)
    (future : Future p σ) :
    LaunchAssignmentCoordinateSplit.originalAssignmentVectorAtLaunch p σ hσ
      ((ReferenceLaunchJointFutureLaw.jointSplitEquiv p σ).symm (past, future)) =
        ReferenceLaunchAssignmentLaw.futureAssignmentVectorAtSigma p σ hσ future.1 := by
  rw [LaunchAssignmentCoordinateSplit.originalAssignmentVectorAtLaunch,
    (ReferenceLaunchJointFutureLaw.jointSplitEquiv p σ).apply_symm_apply,
    LaunchAssignmentCoordinateSplit.jointFutureCoordinateSplit_first]

theorem reconstructOriginal_past_private (p : Parameters) (σ : LaunchIndex p)
    (hσ : σ.val < p.T) (past : Past p σ) (v : AssignmentVector p)
    (rem : Remainder p σ) :
    (reconstructOriginal p σ hσ past v rem).1.1 = past.1.1 := by
  exact ReferenceLaunchJointFutureLaw.jointSplit_symm_private p σ
    (past, (LaunchAssignmentCoordinateSplit.jointFutureCoordinateSplitEquiv p σ hσ).symm
      (v, rem))

theorem reconstructOriginal_past_targets (p : Parameters) (σ : LaunchIndex p)
    (hσ : σ.val < p.T) (past : Past p σ) (v : AssignmentVector p)
    (rem : Remainder p σ) :
    (reconstructOriginal p σ hσ past v rem).1.2.2 = past.1.2.2 := by
  exact ReferenceLaunchJointFutureLaw.jointSplit_symm_targets p σ
    (past, (LaunchAssignmentCoordinateSplit.jointFutureCoordinateSplitEquiv p σ hσ).symm
      (v, rem))

theorem reconstructOriginal_past_privateRound (p : Parameters) (σ : LaunchIndex p)
    (hσ : σ.val < p.T) (past : Past p σ) (v : AssignmentVector p)
    (rem : Remainder p σ)
    (label : ReferenceLaunchPrivateRoundLaw.PastPlayerRoundLabel p σ) :
    (reconstructOriginal p σ hσ past v rem).1.2.1 label.1 = past.1.2.1 label := by
  exact ReferenceLaunchJointFutureLaw.jointSplit_symm_private_past p σ
    (past, (LaunchAssignmentCoordinateSplit.jointFutureCoordinateSplitEquiv p σ hσ).symm
      (v, rem)) label

theorem reconstructOriginal_pastRow (p : Parameters) (σ : LaunchIndex p)
    (hσ : σ.val < p.T) (past : Past p σ) (v : AssignmentVector p)
    (rem : Remainder p σ) (t : PastIndex p σ) :
    calendarizeRow p (reconstructOriginal p σ hσ past v rem).2 t.1 = past.2 t := by
  exact ReferenceLaunchJointFutureLaw.jointSplit_symm_row_past p σ
    (past, (LaunchAssignmentCoordinateSplit.jointFutureCoordinateSplitEquiv p σ hσ).symm
      (v, rem)) t

theorem reconstructOriginal_rowFuture (p : Parameters) (σ : LaunchIndex p)
    (hσ : σ.val < p.T) (past : Past p σ) (v : AssignmentVector p)
    (rem : Remainder p σ) (t : FutureIndex p σ) :
    calendarizeRow p (reconstructOriginal p σ hσ past v rem).2 t.1 =
      ((LaunchAssignmentCoordinateSplit.jointFutureCoordinateSplitEquiv p σ hσ).symm
        (v, rem)).1 t :=
  ReferenceLaunchJointFutureLaw.jointSplit_symm_row_future p σ
    (past, (LaunchAssignmentCoordinateSplit.jointFutureCoordinateSplitEquiv p σ hσ).symm
      (v, rem)) t

theorem reconstructOriginal_assignmentScalar (p : Parameters) (σ : LaunchIndex p)
    (hσ : σ.val < p.T) (past : Past p σ) (v : AssignmentVector p)
    (rem : Remainder p σ) (r : Fin (p.K + 1)) :
    (((LaunchAssignmentCoordinateSplit.jointFutureCoordinateSplitEquiv p σ hσ).symm
      (v, rem)).1 (LaunchAssignmentCoordinateSplit.launchFutureIndex p σ hσ)).2.1
        (ContinuousControlSlice.Label.assign r) = v r :=
  LaunchAssignmentCoordinateSplit.jointFutureCoordinateSplit_symm_assignment
    p σ hσ v rem r

theorem reconstructOriginal_orientationScalar (p : Parameters) (σ : LaunchIndex p)
    (hσ : σ.val < p.T) (past : Past p σ) (v : AssignmentVector p)
    (rem : Remainder p σ) :
    (((LaunchAssignmentCoordinateSplit.jointFutureCoordinateSplitEquiv p σ hσ).symm
      (v, rem)).1 (LaunchAssignmentCoordinateSplit.launchFutureIndex p σ hσ)).2.1
        (ContinuousControlSlice.Label.assign (Fin.last p.K)) = v (Fin.last p.K) :=
  reconstructOriginal_assignmentScalar p σ hσ past v rem (Fin.last p.K)

theorem reconstructOriginal_nonassignmentScalar (p : Parameters) (σ : LaunchIndex p)
    (hσ : σ.val < p.T) (past : Past p σ) (v : AssignmentVector p)
    (rem : Remainder p σ) (c : LaunchAssignmentCoordinateSplit.NonAssignmentLabel p) :
    (((LaunchAssignmentCoordinateSplit.jointFutureCoordinateSplitEquiv p σ hσ).symm
      (v, rem)).1 (LaunchAssignmentCoordinateSplit.launchFutureIndex p σ hσ)).2.1 c.1 =
        rem.1 c :=
  LaunchAssignmentCoordinateSplit.jointFutureCoordinateSplit_symm_launchScalar
    p σ hσ v rem c

theorem reconstructOriginal_launchForward (p : Parameters) (σ : LaunchIndex p)
    (hσ : σ.val < p.T) (past : Past p σ) (v : AssignmentVector p)
    (rem : Remainder p σ) (u : Fin (A_id p)) :
    (((LaunchAssignmentCoordinateSplit.jointFutureCoordinateSplitEquiv p σ hσ).symm
      (v, rem)).1 (LaunchAssignmentCoordinateSplit.launchFutureIndex p σ hσ)).1 u =
        rem.2.1 u :=
  LaunchAssignmentCoordinateSplit.jointFutureCoordinateSplit_symm_launchForward
    p σ hσ v rem u

theorem reconstructOriginal_launchAffine (p : Parameters) (σ : LaunchIndex p)
    (hσ : σ.val < p.T) (past : Past p σ) (v : AssignmentVector p)
    (rem : Remainder p σ) (channel : ContinuousLearningRows.Channel p) :
    (((LaunchAssignmentCoordinateSplit.jointFutureCoordinateSplitEquiv p σ hσ).symm
      (v, rem)).1 (LaunchAssignmentCoordinateSplit.launchFutureIndex p σ hσ)).2.2 channel =
        rem.2.2.1 channel :=
  LaunchAssignmentCoordinateSplit.jointFutureCoordinateSplit_symm_launchAffine
    p σ hσ v rem channel

theorem reconstructOriginal_laterCalendar (p : Parameters) (σ : LaunchIndex p)
    (hσ : σ.val < p.T) (past : Past p σ) (v : AssignmentVector p)
    (rem : Remainder p σ) (i : LaunchAssignmentCoordinateSplit.AfterLaunchIndex p σ) :
    ((LaunchAssignmentCoordinateSplit.jointFutureCoordinateSplitEquiv p σ hσ).symm
      (v, rem)).1 i.1 = rem.2.2.2.1 i :=
  LaunchAssignmentCoordinateSplit.jointFutureCoordinateSplit_symm_laterCalendar
    p σ hσ v rem i

theorem reconstructOriginal_futurePrivateRound (p : Parameters) (σ : LaunchIndex p)
    (hσ : σ.val < p.T) (past : Past p σ) (v : AssignmentVector p)
    (rem : Remainder p σ)
    (label : ReferenceLaunchPrivateRoundLaw.FuturePlayerRoundLabel p σ) :
    ((LaunchAssignmentCoordinateSplit.jointFutureCoordinateSplitEquiv p σ hσ).symm
      (v, rem)).2 label = rem.2.2.2.2 label :=
  LaunchAssignmentCoordinateSplit.jointFutureCoordinateSplit_symm_private
    p σ hσ v rem label

theorem reconstructOriginal_sourceAssignmentScalar (p : Parameters) (σ : LaunchIndex p)
    (hσ : σ.val < p.T) (past : Past p σ) (v : AssignmentVector p)
    (rem : Remainder p σ) (r : Fin (p.K + 1)) :
    (calendarizeRow p (reconstructOriginal p σ hσ past v rem).2
      (LaunchAssignmentCoordinateSplit.launchFutureIndex p σ hσ).1).2.1
        (ContinuousControlSlice.Label.assign r) = v r := by
  rw [reconstructOriginal_rowFuture]
  exact reconstructOriginal_assignmentScalar p σ hσ past v rem r

theorem reconstructOriginal_sourceNonassignmentScalar (p : Parameters)
    (σ : LaunchIndex p) (hσ : σ.val < p.T) (past : Past p σ)
    (v : AssignmentVector p) (rem : Remainder p σ)
    (c : LaunchAssignmentCoordinateSplit.NonAssignmentLabel p) :
    (calendarizeRow p (reconstructOriginal p σ hσ past v rem).2
      (LaunchAssignmentCoordinateSplit.launchFutureIndex p σ hσ).1).2.1 c.1 = rem.1 c := by
  rw [reconstructOriginal_rowFuture]
  exact reconstructOriginal_nonassignmentScalar p σ hσ past v rem c

theorem reconstructOriginal_sourceLaunchForward (p : Parameters) (σ : LaunchIndex p)
    (hσ : σ.val < p.T) (past : Past p σ) (v : AssignmentVector p)
    (rem : Remainder p σ) (u : Fin (A_id p)) :
    (calendarizeRow p (reconstructOriginal p σ hσ past v rem).2
      (LaunchAssignmentCoordinateSplit.launchFutureIndex p σ hσ).1).1 u = rem.2.1 u := by
  rw [reconstructOriginal_rowFuture]
  exact reconstructOriginal_launchForward p σ hσ past v rem u

theorem reconstructOriginal_sourceLaunchAffine (p : Parameters) (σ : LaunchIndex p)
    (hσ : σ.val < p.T) (past : Past p σ) (v : AssignmentVector p)
    (rem : Remainder p σ) (channel : ContinuousLearningRows.Channel p) :
    (calendarizeRow p (reconstructOriginal p σ hσ past v rem).2
      (LaunchAssignmentCoordinateSplit.launchFutureIndex p σ hσ).1).2.2 channel =
        rem.2.2.1 channel := by
  rw [reconstructOriginal_rowFuture]
  exact reconstructOriginal_launchAffine p σ hσ past v rem channel

theorem reconstructOriginal_sourceLaterCalendar (p : Parameters) (σ : LaunchIndex p)
    (hσ : σ.val < p.T) (past : Past p σ) (v : AssignmentVector p)
    (rem : Remainder p σ) (i : LaunchAssignmentCoordinateSplit.AfterLaunchIndex p σ) :
    calendarizeRow p (reconstructOriginal p σ hσ past v rem).2 i.1.1 =
      rem.2.2.2.1 i := by
  rw [reconstructOriginal_rowFuture]
  exact reconstructOriginal_laterCalendar p σ hσ past v rem i

theorem reconstructOriginal_sourceFuturePrivateRound (p : Parameters)
    (σ : LaunchIndex p) (hσ : σ.val < p.T) (past : Past p σ)
    (v : AssignmentVector p) (rem : Remainder p σ)
    (label : ReferenceLaunchPrivateRoundLaw.FuturePlayerRoundLabel p σ) :
    (reconstructOriginal p σ hσ past v rem).1.2.1 label.1 = rem.2.2.2.2 label := by
  exact (ReferenceLaunchJointFutureLaw.jointSplit_symm_private_future p σ
    (past, (LaunchAssignmentCoordinateSplit.jointFutureCoordinateSplitEquiv p σ hσ).symm
      (v, rem)) label).trans
        (reconstructOriginal_futurePrivateRound p σ hσ past v rem label)

/-- The finite lifted measure: its `U` component has canonical weight `pi(U)`,
the actual joint-past law restricted to the genuine launch event and `A`, and
the literal reconstructed full-vector fibre future.
-/
@[expose] noncomputable def liftedComponent (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : LearningRate) (σ : LaunchIndex p) (hσ : σ.val < p.T)
    (A : Set (Past p σ)) (U : SlowSet p) :
    Measure (SlowSet p × Original p) :=
  slowSetMass p U •
    ((restrictedLaunchPastLaw p ids rewards C_star C_h eta σ A).prod
      (futureFibreMeasure p σ hσ U)).map
        (fun w => (U, (ReferenceLaunchJointFutureLaw.jointSplitEquiv p σ).symm w))

@[expose] noncomputable def liftedMeasure (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : LearningRate) (σ : LaunchIndex p) (hσ : σ.val < p.T)
    (A : Set (Past p σ)) : Measure (SlowSet p × Original p) :=
  ∑ U : SlowSet p, liftedComponent p ids rewards C_star C_h eta σ hσ A U

theorem measurable_reconstructPoint (p : Parameters) (σ : LaunchIndex p)
    (U : SlowSet p) :
    Measurable (fun w : Past p σ × Future p σ =>
      (U, (ReferenceLaunchJointFutureLaw.jointSplitEquiv p σ).symm w)) := by
  exact measurable_const.prodMk
    ((ReferenceLaunchJointFutureLaw.jointSplitEquiv p σ).symm.measurable.comp measurable_id)

theorem liftedComponent_secondMarginal (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : LearningRate) (σ : LaunchIndex p) (hσ : σ.val < p.T)
    (A : Set (Past p σ)) (U : SlowSet p) :
    (liftedComponent p ids rewards C_star C_h eta σ hσ A U).map Prod.snd =
      slowSetMass p U •
        ((restrictedLaunchPastLaw p ids rewards C_star C_h eta σ A).prod
          (futureFibreMeasure p σ hσ U)).map
            (ReferenceLaunchJointFutureLaw.jointSplitEquiv p σ).symm := by
  rw [liftedComponent, Measure.map_smul _ measurable_snd.aemeasurable,
    Measure.map_map measurable_snd (measurable_reconstructPoint p σ U)]
  rfl

theorem liftedMeasure_secondMarginal_eq_split (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : LearningRate) (σ : LaunchIndex p) (hσ : σ.val < p.T)
    (A : Set (Past p σ)) (hA : MeasurableSet A) :
    (liftedMeasure p ids rewards C_star C_h eta σ hσ A).map Prod.snd =
      ((restrictedLaunchPastLaw p ids rewards C_star C_h eta σ A).prod
        (ReferenceLaunchJointFutureLaw.jointFutureLaw p σ)).map
          (ReferenceLaunchJointFutureLaw.jointSplitEquiv p σ).symm := by
  classical
  let e := ReferenceLaunchJointFutureLaw.jointSplitEquiv p σ
  have hprod :
      (∑ U : SlowSet p, slowSetMass p U •
        (restrictedLaunchPastLaw p ids rewards C_star C_h eta σ A).prod
          (futureFibreMeasure p σ hσ U)) =
        (restrictedLaunchPastLaw p ids rewards C_star C_h eta σ A).prod
          (∑ U : SlowSet p, slowSetMass p U • futureFibreMeasure p σ hσ U) := by
    calc
      _ = ∑ U : SlowSet p,
          (restrictedLaunchPastLaw p ids rewards C_star C_h eta σ A).prod
            (slowSetMass p U • futureFibreMeasure p σ hσ U) := by
        apply Finset.sum_congr rfl
        intro U hU
        rw [Measure.prod_smul_right]
      _ = Measure.sum (fun U : SlowSet p =>
          (restrictedLaunchPastLaw p ids rewards C_star C_h eta σ A).prod
            (slowSetMass p U • futureFibreMeasure p σ hσ U)) := by
        rw [← Measure.sum_fintype]
      _ = (restrictedLaunchPastLaw p ids rewards C_star C_h eta σ A).prod
          (Measure.sum fun U : SlowSet p => slowSetMass p U • futureFibreMeasure p σ hσ U) :=
        (Measure.prod_sum_right _ _).symm
      _ = (restrictedLaunchPastLaw p ids rewards C_star C_h eta σ A).prod
          (∑ U : SlowSet p, slowSetMass p U • futureFibreMeasure p σ hσ U) := by
        rw [Measure.sum_fintype]
  have hmapSum :
      (∑ U : SlowSet p, slowSetMass p U •
        ((restrictedLaunchPastLaw p ids rewards C_star C_h eta σ A).prod
          (futureFibreMeasure p σ hσ U)).map e.symm) =
        (∑ U : SlowSet p, slowSetMass p U •
          (restrictedLaunchPastLaw p ids rewards C_star C_h eta σ A).prod
            (futureFibreMeasure p σ hσ U)).map e.symm := by
    have h := Measure.map_sum
      (m := fun U : SlowSet p => slowSetMass p U •
        (restrictedLaunchPastLaw p ids rewards C_star C_h eta σ A).prod
          (futureFibreMeasure p σ hσ U))
      (f := e.symm) e.symm.measurable.aemeasurable
    simpa only [Measure.sum_fintype,
      Measure.map_smul _ e.symm.measurable.aemeasurable, e] using h.symm
  calc
    _ = (∑ U : SlowSet p, slowSetMass p U •
        ((restrictedLaunchPastLaw p ids rewards C_star C_h eta σ A).prod
          (futureFibreMeasure p σ hσ U)).map e.symm) := by
      have h := Measure.map_sum
        (m := fun U : SlowSet p => liftedComponent p ids rewards C_star C_h eta σ hσ A U)
        (f := Prod.snd) measurable_snd.aemeasurable
      simpa only [liftedMeasure, Measure.sum_fintype,
        liftedComponent_secondMarginal, e] using h
    _ = (∑ U : SlowSet p, slowSetMass p U •
        (restrictedLaunchPastLaw p ids rewards C_star C_h eta σ A).prod
          (futureFibreMeasure p σ hσ U)).map e.symm := hmapSum
    _ = ((restrictedLaunchPastLaw p ids rewards C_star C_h eta σ A).prod
        (∑ U : SlowSet p, slowSetMass p U • futureFibreMeasure p σ hσ U)).map e.symm := by
      rw [hprod]
    _ = _ := by rw [futureFibreMeasure_mixture]

theorem liftedMeasure_secondMarginal (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : LearningRate) (σ : LaunchIndex p) (hσ : σ.val < p.T)
    (A : Set (Past p σ)) (hA : MeasurableSet A) :
    (liftedMeasure p ids rewards C_star C_h eta σ hσ A).map Prod.snd =
      (ReferenceLaunchJointFutureLaw.originalLaw p).restrict
        (launchAndPastEvent p ids rewards C_star C_h eta σ A) := by
  let e := ReferenceLaunchJointFutureLaw.jointSplitEquiv p σ
  let E := launchPastSet p ids rewards C_star C_h eta σ A
  have hsplit :
      ((ReferenceLaunchJointFutureLaw.originalLaw p).restrict
        (launchAndPastEvent p ids rewards C_star C_h eta σ A)).map e =
        (restrictedLaunchPastLaw p ids rewards C_star C_h eta σ A).prod
          (ReferenceLaunchJointFutureLaw.jointFutureLaw p σ) := by
    rw [launchAndPastEvent_jointSplit_preimage,
      ← e.restrict_map (ReferenceLaunchJointFutureLaw.originalLaw p) (E ×ˢ Set.univ),
      ReferenceLaunchJointFutureLaw.map_jointSplit,
      ← Measure.restrict_prod_eq_prod_univ E]
    rfl
  calc
    _ = ((restrictedLaunchPastLaw p ids rewards C_star C_h eta σ A).prod
        (ReferenceLaunchJointFutureLaw.jointFutureLaw p σ)).map e.symm :=
      liftedMeasure_secondMarginal_eq_split p ids rewards C_star C_h eta σ hσ A hA
    _ = ((((ReferenceLaunchJointFutureLaw.originalLaw p).restrict
        (launchAndPastEvent p ids rewards C_star C_h eta σ A)).map e).map e.symm) := by
      rw [hsplit]
    _ = (ReferenceLaunchJointFutureLaw.originalLaw p).restrict
        (launchAndPastEvent p ids rewards C_star C_h eta σ A) := by
      rw [e.map_symm_map]

/-- The first marginal has the exact canonical masses multiplied by the
original probability of `L_A`.
-/
theorem liftedMeasure_firstMarginal_mass (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : LearningRate) (σ : LaunchIndex p) (hσ : σ.val < p.T)
    (A : Set (Past p σ)) (hA : MeasurableSet A) (U : SlowSet p) :
    (liftedMeasure p ids rewards C_star C_h eta σ hσ A).map Prod.fst {U} =
      (ReferenceLaunchJointFutureLaw.originalLaw p)
        (launchAndPastEvent p ids rewards C_star C_h eta σ A) * slowSetMass p U := by
  classical
  have hcomponent (V : SlowSet p) :
      (liftedComponent p ids rewards C_star C_h eta σ hσ A V).map Prod.fst {U} =
        if V = U then slowSetMass p V *
          (restrictedLaunchPastLaw p ids rewards C_star C_h eta σ A Set.univ) else 0 := by
    rw [liftedComponent, Measure.map_smul _ measurable_fst.aemeasurable,
      Measure.map_map measurable_fst (measurable_reconstructPoint p σ V)]
    change slowSetMass p V *
      (Measure.map (fun _ : Past p σ × Future p σ => V)
        ((restrictedLaunchPastLaw p ids rewards C_star C_h eta σ A).prod
          (futureFibreMeasure p σ hσ V))) {U} = _
    rw [Measure.map_apply measurable_const (measurableSet_singleton U)]
    by_cases hVU : V = U
    · subst U
      simp only [Set.preimage_const, Set.mem_singleton_iff, if_true]
      rw [← Set.univ_prod_univ, Measure.prod_prod]
      simp
    · simp [hVU, Measure.smul_apply]
  rw [liftedMeasure, ← Measure.sum_fintype, Measure.map_sum measurable_fst.aemeasurable,
    Measure.sum_fintype, Measure.finsetSum_apply]
  simp_rw [hcomponent]
  rw [← launchAndPastEvent_mass p ids rewards C_star C_h eta σ A hA]
  simp [mul_comm]

theorem liftedMeasure_finite (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : LearningRate) (σ : LaunchIndex p) (hσ : σ.val < p.T)
    (A : Set (Past p σ)) (hA : MeasurableSet A) :
    IsFiniteMeasure (liftedMeasure p ids rewards C_star C_h eta σ hσ A) := by
  refine ⟨?_⟩
  have htotal := congrArg (fun μ : Measure (Original p) => μ Set.univ)
    (liftedMeasure_secondMarginal p ids rewards C_star C_h eta σ hσ A hA)
  rw [Measure.map_apply_of_aemeasurable measurable_snd.aemeasurable MeasurableSet.univ,
    Set.preimage_univ, Measure.restrict_apply_univ] at htotal
  rw [htotal]
  exact measure_lt_top (ReferenceLaunchJointFutureLaw.originalLaw p) _

/-- The reconstructed first-start operation uses precisely the vector
recovered from the accepted assignment/remainder split.
-/
theorem actualFirstStart_coordinates (p : Parameters) (eta : LearningRate)
    (hcap : eta.val ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (CanonicalRecordingRates.L_stab p : ℝ)))
    (n : ℕ) (hn : (n : ℝ) = eta.val * (D p : ℝ))
    (σ : LaunchIndex p) (hσ : σ.val < p.T) (z : Original p) :
    (ReferenceLaunchAssignmentLaw.actualStartAtSigma p eta hcap n hn σ hσ z.2).coordinates =
      LaunchAssignmentCoordinateSplit.originalAssignmentVectorAtLaunch p σ hσ z :=
  LaunchAssignmentCoordinateSplit.actualStart_coordinates_eq_split_first
    p eta hcap n hn σ hσ z

@[expose] noncomputable def actualFirstStartSlowSet (p : Parameters) (eta : LearningRate)
    (hcap : eta.val ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (CanonicalRecordingRates.L_stab p : ℝ)))
    (n : ℕ) (hn : (n : ℝ) = eta.val * (D p : ℝ))
    (σ : LaunchIndex p) (hσ : σ.val < p.T) (z : Original p) : SlowSet p :=
  (ReferenceLaunchAssignmentLaw.actualStartAtSigma p eta hcap n hn σ hσ z.2).slowSet

theorem actualFirstStartSlowSet_eq_sampler (p : Parameters) (eta : LearningRate)
    (hcap : eta.val ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (CanonicalRecordingRates.L_stab p : ℝ)))
    (n : ℕ) (hn : (n : ℝ) = eta.val * (D p : ℝ))
    (σ : LaunchIndex p) (hσ : σ.val < p.T) (z : Original p) :
    actualFirstStartSlowSet p eta hcap n hn σ hσ z =
      firstLaunchSampler p
        (LaunchAssignmentCoordinateSplit.originalAssignmentVectorAtLaunch p σ hσ z) := by
  change ReferenceLaunchAssignmentLaw.actualSlowSetAtSigma p eta hcap n hn σ hσ z.2 = _
  rw [ReferenceLaunchAssignmentLaw.actualSlowSetAtSigma_eq_canonical]
  rw [LaunchAssignmentCoordinateSplit.originalAssignmentVectorAtLaunch_eq_original]
  rfl

theorem measurable_actualFirstStartSlowSet (p : Parameters) (eta : LearningRate)
    (hcap : eta.val ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (CanonicalRecordingRates.L_stab p : ℝ)))
    (n : ℕ) (hn : (n : ℝ) = eta.val * (D p : ℝ))
    (σ : LaunchIndex p) (hσ : σ.val < p.T) :
    Measurable (actualFirstStartSlowSet p eta hcap n hn σ hσ) := by
  exact (ReferenceLaunchAssignmentLaw.measurable_actualSlowSetAtSigma
    p eta hcap n hn σ hσ).comp measurable_snd

/-- On the finite lifted law, the actual first-start slow set equals its
lifted canonical outcome almost surely. -/
theorem liftedMeasure_actualFirstStart_agrees (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : LearningRate) (hcap : eta.val ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (CanonicalRecordingRates.L_stab p : ℝ)))
    (n : ℕ) (hn : (n : ℝ) = eta.val * (D p : ℝ))
    (σ : LaunchIndex p) (hσ : σ.val < p.T) (A : Set (Past p σ))
    (hA : MeasurableSet A) :
    ∀ᵐ x ∂liftedMeasure p ids rewards C_star C_h eta σ hσ A,
      actualFirstStartSlowSet p eta hcap n hn σ hσ x.2 = x.1 := by
  classical
  let P : SlowSet p × Original p → Prop := fun x =>
    actualFirstStartSlowSet p eta hcap n hn σ hσ x.2 = x.1
  have hmeas : MeasurableSet {x : SlowSet p × Original p | P x} := by
    exact measurableSet_eq_fun
      ((measurable_actualFirstStartSlowSet p eta hcap n hn σ hσ).comp measurable_snd)
      measurable_fst
  have hfuture (U : SlowSet p) :
      ∀ᵐ future ∂futureFibreMeasure p σ hσ U,
        firstLaunchSampler p
          (ReferenceLaunchAssignmentLaw.futureAssignmentVectorAtSigma p σ hσ future.1) = U := by
    let e := LaunchAssignmentCoordinateSplit.jointFutureCoordinateSplitEquiv p σ hσ
    have hcube : ∀ᵐ x ∂
        (FiniteFibreLift.fibreMeasure (ContinuousControlSlice.assignmentLaw p.K)
          (firstLaunchSampler p) U).prod
            (LaunchAssignmentCoordinateSplit.remainderLaw p σ),
        firstLaunchSampler p x.1 = U := by
      have hsingle : MeasurableSet
          {x : AssignmentVector p × Remainder p σ | firstLaunchSampler p x.1 = U} :=
        (measurableSet_singleton U).preimage
          ((measurable_firstLaunchSampler p).comp measurable_fst)
      apply (Measure.ae_prod_iff_ae_ae hsingle).2
      filter_upwards [FiniteFibreLift.ae_fibreMeasure_eq
        (μ := ContinuousControlSlice.assignmentLaw p.K)
        (F := firstLaunchSampler p) (a := U) (measurable_firstLaunchSampler p)
        (by rw [← slowSetMass_eq_fibreMass]; exact (slowSetMass_ne_zero p U))]
        with v hv
      exact Filter.Eventually.of_forall fun rem => hv
    have hmap : ∀ᵐ future ∂futureFibreMeasure p σ hσ U,
        firstLaunchSampler p
          ((LaunchAssignmentCoordinateSplit.jointFutureCoordinateSplitEquiv p σ hσ future).1) = U := by
      have hset : MeasurableSet {future : Future p σ |
          firstLaunchSampler p
            ((LaunchAssignmentCoordinateSplit.jointFutureCoordinateSplitEquiv p σ hσ future).1) = U} :=
        (measurableSet_singleton U).preimage
          ((measurable_firstLaunchSampler p).comp
            (measurable_fst.comp
              (LaunchAssignmentCoordinateSplit.jointFutureCoordinateSplitEquiv p σ hσ).measurable))
      change ∀ᵐ future ∂
        ((FiniteFibreLift.fibreMeasure (ContinuousControlSlice.assignmentLaw p.K)
          (firstLaunchSampler p) U).prod
            (LaunchAssignmentCoordinateSplit.remainderLaw p σ)).map
              (LaunchAssignmentCoordinateSplit.jointFutureCoordinateSplitEquiv p σ hσ).symm,
        firstLaunchSampler p
          ((LaunchAssignmentCoordinateSplit.jointFutureCoordinateSplitEquiv p σ hσ future).1) = U
      exact (ae_map_iff e.symm.measurable.aemeasurable hset).2 (by
        filter_upwards [hcube] with x hx
        change firstLaunchSampler p (e (e.symm x)).1 = U
        rw [e.apply_symm_apply]
        exact hx)
    filter_upwards [hmap] with future hfuture
    simpa only [LaunchAssignmentCoordinateSplit.jointFutureCoordinateSplit_first] using hfuture
  have hcomponent (U : SlowSet p) :
      ∀ᵐ x ∂liftedComponent p ids rewards C_star C_h eta σ hσ A U, P x := by
    have hsource : ∀ᵐ w ∂
        (restrictedLaunchPastLaw p ids rewards C_star C_h eta σ A).prod
          (futureFibreMeasure p σ hσ U),
        actualFirstStartSlowSet p eta hcap n hn σ hσ
          ((ReferenceLaunchJointFutureLaw.jointSplitEquiv p σ).symm w) = U := by
      have hfutureMeasurable : Measurable (fun w : Past p σ × Future p σ =>
          firstLaunchSampler p
            (ReferenceLaunchAssignmentLaw.futureAssignmentVectorAtSigma p σ hσ w.2.1)) :=
        (measurable_firstLaunchSampler p).comp
          ((ReferenceLaunchAssignmentLaw.measurable_futureAssignmentVectorAtSigma p σ hσ).comp
            (measurable_fst.comp measurable_snd))
      have hfutureSet : MeasurableSet {w : Past p σ × Future p σ |
          firstLaunchSampler p
            (ReferenceLaunchAssignmentLaw.futureAssignmentVectorAtSigma p σ hσ w.2.1) = U} :=
        (measurableSet_singleton U).preimage hfutureMeasurable
      have hfutureProduct : ∀ᵐ w ∂
          (restrictedLaunchPastLaw p ids rewards C_star C_h eta σ A).prod
            (futureFibreMeasure p σ hσ U),
          firstLaunchSampler p
            (ReferenceLaunchAssignmentLaw.futureAssignmentVectorAtSigma p σ hσ w.2.1) = U := by
        apply (Measure.ae_prod_iff_ae_ae hfutureSet).2
        exact Filter.Eventually.of_forall fun _ => hfuture U
      exact hfutureProduct.mono fun w hw => by
        rcases w with ⟨past, future⟩
        have hstart := actualFirstStartSlowSet_eq_sampler p eta hcap n hn σ hσ
          ((ReferenceLaunchJointFutureLaw.jointSplitEquiv p σ).symm (past, future))
        have hvect := originalAssignmentVectorAtLaunch_reconstruct p σ hσ past future
        exact (hstart.trans (congrArg (firstLaunchSampler p) hvect)).trans hw
    have hmap := ae_map_iff
      (μ := (restrictedLaunchPastLaw p ids rewards C_star C_h eta σ A).prod
        (futureFibreMeasure p σ hσ U))
      (f := fun w => (U, (ReferenceLaunchJointFutureLaw.jointSplitEquiv p σ).symm w))
      ((measurable_reconstructPoint p σ U).aemeasurable)
      hmeas
    have hscaled := (MeasureTheory.Measure.ae_ennreal_smul_measure_iff
      (slowSetMass_ne_zero p U)).2
      ((hmap).2 hsource)
    simpa only [liftedComponent, P] using hscaled
  rw [ae_iff]
  rw [liftedMeasure, Measure.finsetSum_apply]
  have hzero : ∀ U : SlowSet p,
      liftedComponent p ids rewards C_star C_h eta σ hσ A U
        {x | ¬ P x} = 0 := by
    intro U
    exact ae_iff.mp (hcomponent U)
  apply Finset.sum_eq_zero
  intro U hU
  simpa only [P] using hzero U

/-- Measurability of the source event recording the canonical slow outcome,
an arbitrary measurable assignment-cube event, and an arbitrary measurable
full remainder event. -/
theorem measurable_sourceFibreRectangle (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : LearningRate) (σ : LaunchIndex p) (hσ : σ.val < p.T)
    (A : Set (Past p σ)) (hA : MeasurableSet A) (U : SlowSet p)
    (C : Set (AssignmentVector p)) (hC : MeasurableSet C)
    (E : Set (Remainder p σ)) (hE : MeasurableSet E) :
    MeasurableSet {z : Original p |
      z ∈ launchAndPastEvent p ids rewards C_star C_h eta σ A ∧
      firstLaunchSampler p
        (LaunchAssignmentCoordinateSplit.originalAssignmentVectorAtLaunch p σ hσ z) = U ∧
      LaunchAssignmentCoordinateSplit.originalAssignmentVectorAtLaunch p σ hσ z ∈ C ∧
      LaunchAssignmentCoordinateSplit.exactRemainderAtLaunch p σ hσ z ∈ E} := by
  have hC' : MeasurableSet {v : AssignmentVector p |
      firstLaunchSampler p v = U ∧ v ∈ C} :=
    ((measurableSet_singleton U).preimage (measurable_firstLaunchSampler p)).inter hC
  have hrect :=
    LaunchAssignmentCoordinateSplit.measurable_actual_launch_assignment_remainder_event
      p ids rewards C_star C_h eta σ hσ A hA {v | firstLaunchSampler p v = U ∧ v ∈ C}
      hC' E hE
  simpa [launchAndPastEvent, Set.mem_setOf_eq, and_assoc] using hrect

/-- The explicit finite-event formula on the original complete coordinate
space. It is unnormalized, and so remains valid for null launch/past events
and zero-mass fibres.
-/
theorem sourceFibreRectangle_mass (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : LearningRate) (σ : LaunchIndex p) (hσ : σ.val < p.T)
    (A : Set (Past p σ)) (hA : MeasurableSet A) (U : SlowSet p)
    (C : Set (AssignmentVector p)) (hC : MeasurableSet C)
    (E : Set (Remainder p σ)) (hE : MeasurableSet E) :
    ReferenceLaunchJointFutureLaw.originalLaw p
      {z : Original p |
        z ∈ launchAndPastEvent p ids rewards C_star C_h eta σ A ∧
        firstLaunchSampler p
          (LaunchAssignmentCoordinateSplit.originalAssignmentVectorAtLaunch p σ hσ z) = U ∧
        LaunchAssignmentCoordinateSplit.originalAssignmentVectorAtLaunch p σ hσ z ∈ C ∧
        LaunchAssignmentCoordinateSplit.exactRemainderAtLaunch p σ hσ z ∈ E} =
      ReferenceLaunchJointFutureLaw.originalLaw p
        (launchAndPastEvent p ids rewards C_star C_h eta σ A) *
        slowSetMass p U *
        FiniteFibreLift.fibreMeasure (ContinuousControlSlice.assignmentLaw p.K)
          (firstLaunchSampler p) U C *
        LaunchAssignmentCoordinateSplit.remainderLaw p σ E := by
  let CU : Set (AssignmentVector p) :=
    {v | firstLaunchSampler p v = U ∧ v ∈ C}
  have hCU : MeasurableSet CU :=
    ((measurableSet_singleton U).preimage (measurable_firstLaunchSampler p)).inter hC
  have hmass : (ContinuousControlSlice.assignmentLaw p.K) CU =
      slowSetMass p U *
        FiniteFibreLift.fibreMeasure (ContinuousControlSlice.assignmentLaw p.K)
          (firstLaunchSampler p) U C := by
    have hrest := FiniteFibreLift.fibreMass_smul_fibreMeasure
      (μ := ContinuousControlSlice.assignmentLaw p.K) (F := firstLaunchSampler p) (a := U)
    have hrest' := congrArg (fun μ : Measure (AssignmentVector p) => μ C) hrest
    rw [← slowSetMass_eq_fibreMass p U] at hrest'
    rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hC] at hrest'
    have hCUeq : CU = C ∩ firstLaunchSampler p ⁻¹' ({U} : Set (SlowSet p)) := by
      ext v
      simp [CU, and_comm]
    rw [hCUeq]
    exact hrest'.symm
  have hfactor :=
    LaunchAssignmentCoordinateSplit.actual_launch_assignment_remainder_factorization
      p ids rewards C_star C_h eta σ hσ A hA CU hCU E hE
  have hset :
      {z : Original p |
        z ∈ launchAndPastEvent p ids rewards C_star C_h eta σ A ∧
        firstLaunchSampler p
          (LaunchAssignmentCoordinateSplit.originalAssignmentVectorAtLaunch p σ hσ z) = U ∧
        LaunchAssignmentCoordinateSplit.originalAssignmentVectorAtLaunch p σ hσ z ∈ C ∧
        LaunchAssignmentCoordinateSplit.exactRemainderAtLaunch p σ hσ z ∈ E} =
      {z | ReferenceInitializationRun.launchRound
          (ReferenceLaunchJointFutureLaw.actualInput p ids rewards C_star C_h eta z) =
            σ.val + 1 ∧
        (ReferenceLaunchJointFutureLaw.jointSplitEquiv p σ z).1 ∈ A ∧
        LaunchAssignmentCoordinateSplit.originalAssignmentVectorAtLaunch p σ hσ z ∈ CU ∧
        LaunchAssignmentCoordinateSplit.exactRemainderAtLaunch p σ hσ z ∈ E} := by
    ext z
    simp [launchAndPastEvent, CU, and_assoc]
  rw [hset, hfactor, hmass]
  ac_rfl

end Bandits.Support.LaunchAssignmentFibreCoupling

end
