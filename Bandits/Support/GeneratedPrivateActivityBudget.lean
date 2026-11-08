/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Bandits Lean Project
-/
module

public import Bandits.Support.GeneratedBlockDrawLaw
public import Bandits.Support.GeneratedPrivateIDFibers
public import Bandits.Support.GeneratedEligibleFamily
public import Bandits.Support.GeneratedFalseForwardEvent
public import Bandits.Support.ReferenceInitializationPrefixInvariance
public import Bandits.Support.ReferenceInitializationRun

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic.Ring

/-!
# Fixed-table private activity admission

For a fixed entire published output and selected true row, this module proves
the exact `1/m` admission identity for each genuinely processed, incoming
uninformed follower. The events are defined from the accepted stopped
reference run and its actual output-side private-ID code. The full current
block scalar split retains the original coordinator selector and separates
the boundary from the existing follower activity, held-arm, private-ID, and
target coordinates.

Sources: `sources/zip4/manuscript/07_public_setup.tex:27-38,63-113` and
`sources/zip4/manuscript/appendix_b_communication.tex:350-365`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.CompletePublicTable
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.PrivateSourceStreams
open Bandits.Support.ContinuousCategorical
open Bandits.Support.BootstrapPhysicalInput
open Bandits.Support.BootstrapPrivateIDFibers
open Bandits.Support.ReferenceInitializationRun
open Bandits.Support.GeneratedForwardPrefixTests
open Bandits.Support.GeneratedEligibleFamily
open Bandits.Support.GeneratedBlockDrawLaw
open scoped ENNReal
open scoped BigOperators

namespace Bandits.Support.GeneratedPrivateActivityBudget

abbrev Parameters := ConstructorDimensions.Parameters

/-- The boundary predicate for the actual opportunity at source block `s`:
the stopped run has not crossed, has completed exactly the preceding blocks,
and the selected source follower is still incoming and uninformed. -/
def processedUninformedBoundaryCondition (p : Parameters)
    (s : Fin (n_boot p)) (j : Fin (p.m - 1))
    (b : ReferenceInitializationRun.Boundary p) : Prop :=
  b.crossing = none ∧ b.completed = s.val ∧
    j ∈ ReferenceInitializationRun.uninformed b

/-- The actual processed-uninformed event on the original private product,
with the complete numeric published output and selected row held fixed. -/
def processedUninformedEvent (p : Parameters) (P : PublishedOutput p)
    (J : Fin (M p)) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (s : Fin (n_boot p)) (j : Fin (p.m - 1)) :
    Set (ExtendedPrivateCoordinates p) :=
  {rho | processedUninformedBoundaryCondition p s j
    (GeneratedBlockDrawLaw.generatedBoundary p s P.1 (P.2 J)
      rewards C_star C_h eta rho)}

/-- The actual output-side code event, formed on the same fixed output and
original private-coordinate carrier. -/
def activePrivateIDCodeSomeEvent (p : Parameters) (P : PublishedOutput p)
    (J : Fin (M p)) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (s : Fin (n_boot p)) (j : Fin (p.m - 1)) :
    Set (ExtendedPrivateCoordinates p) :=
  {rho | ∃ u : Fin (A_id p),
    GeneratedEligibleFamily.activePrivateIDCodeOnPublishedOutput
      C_star C_h eta rewards J s j (P, rho) = some u}

/-- The active processed-uninformed subevent, using exactly the accepted
actual private-ID code to witness activity. -/
def activeProcessedUninformedEvent (p : Parameters) (P : PublishedOutput p)
    (J : Fin (M p)) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (s : Fin (n_boot p)) (j : Fin (p.m - 1)) :
    Set (ExtendedPrivateCoordinates p) :=
  processedUninformedEvent p P J rewards C_star C_h eta s j ∩
    activePrivateIDCodeSomeEvent p P J rewards C_star C_h eta s j

/-- The same processed-uninformed boundary predicate on the retained side of
the original current-block scalar split. -/
def processedUninformedOtherSet (p : Parameters) (P : PublishedOutput p)
    (J : Fin (M p)) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (s : Fin (n_boot p)) (j : Fin (p.m - 1)) :
    Set (GeneratedBlockDrawLaw.OtherPrivateCoordinates p s) :=
  {w | processedUninformedBoundaryCondition p s j
    (GeneratedBlockDrawLaw.boundaryFromOther p s P.1 (P.2 J)
      rewards C_star C_h eta w)}

/-- The current activity coin's literal event in the original full follower
triple profile of block `s`. Held-arm and private-ID coordinates remain in the
same profile and are not replaced. -/
def currentProfileActivitySet (p : Parameters) (j : Fin (p.m - 1)) :
    Set (GeneratedBlockDrawLaw.FollowerTripleProfile p) :=
  {x | PrivateSourceStreams.activityScalarDraw p
    (x (sourceFollowerIndex p j)).1 = true}

/-- Measurability of the actual processed-uninformed event. Every subset of
the accepted boundary carrier is measurable, and the boundary is the actual
generated stopped run. -/
theorem measurableSet_processedUninformedEvent (p : Parameters)
    (P : PublishedOutput p) (J : Fin (M p))
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (s : Fin (n_boot p)) (j : Fin (p.m - 1)) :
    MeasurableSet (processedUninformedEvent p P J rewards C_star C_h eta s j) := by
  let q : Set (ReferenceInitializationRun.Boundary p) :=
    {b | processedUninformedBoundaryCondition p s j b}
  have hq : MeasurableSet q := by
    change MeasurableSet[⊤] q
    exact MeasurableSpace.measurableSet_top
  change MeasurableSet
    ((GeneratedBlockDrawLaw.generatedBoundary p s P.1 (P.2 J)
      rewards C_star C_h eta) ⁻¹' q)
  exact (GeneratedBlockDrawLaw.measurable_generatedBoundary p s P.1
    (P.2 J) rewards C_star C_h eta) hq

/-- Measurability of the actual active-ID event uses the accepted measurable
output-side code and a finite union over the original ID alphabet. -/
theorem measurableSet_activePrivateIDCodeSomeEvent (p : Parameters)
    (P : PublishedOutput p) (J : Fin (M p))
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (s : Fin (n_boot p)) (j : Fin (p.m - 1)) :
    MeasurableSet (activePrivateIDCodeSomeEvent p P J rewards C_star C_h eta s j) := by
  let code := fun rho : ExtendedPrivateCoordinates p =>
    GeneratedEligibleFamily.activePrivateIDCodeOnPublishedOutput
      C_star C_h eta rewards J s j (P, rho)
  have hcode : Measurable code := by
    dsimp [code]
    exact (GeneratedEligibleFamily.measurable_activePrivateIDCodeOnPublishedOutput
      C_star C_h eta rewards J s j).comp
        (measurable_const.prodMk measurable_id)
  have hset : activePrivateIDCodeSomeEvent p P J rewards C_star C_h eta s j =
      ⋃ u : Fin (A_id p), {rho | code rho = some u} := by
    ext rho
    simp [activePrivateIDCodeSomeEvent, code]
  rw [hset]
  exact MeasurableSet.iUnion fun u => hcode (measurableSet_singleton (some u))

/-- Both actual event layers are measurable on the original private law. -/
theorem measurableSet_activeProcessedUninformedEvent (p : Parameters)
    (P : PublishedOutput p) (J : Fin (M p))
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (s : Fin (n_boot p)) (j : Fin (p.m - 1)) :
    MeasurableSet (activeProcessedUninformedEvent p P J rewards C_star C_h eta s j) :=
  (measurableSet_processedUninformedEvent p P J rewards C_star C_h eta s j).inter
    (measurableSet_activePrivateIDCodeSomeEvent p P J rewards C_star C_h eta s j)

/-- The retained-side boundary event is measurable by the accepted generated
boundary map and the discrete boundary encoding. -/
theorem measurableSet_processedUninformedOtherSet (p : Parameters)
    (P : PublishedOutput p) (J : Fin (M p))
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (s : Fin (n_boot p)) (j : Fin (p.m - 1)) :
    MeasurableSet (processedUninformedOtherSet p P J rewards C_star C_h eta s j) := by
  let q : Set (ReferenceInitializationRun.Boundary p) :=
    {b | processedUninformedBoundaryCondition p s j b}
  have hq : MeasurableSet q := by
    change MeasurableSet[⊤] q
    exact MeasurableSpace.measurableSet_top
  change MeasurableSet
    ((GeneratedBlockDrawLaw.boundaryFromOther p s P.1 (P.2 J)
      rewards C_star C_h eta) ⁻¹' q)
  exact (GeneratedBlockDrawLaw.measurable_boundaryFromOther p s P.1
    (P.2 J) rewards C_star C_h eta) hq

/-- The source Bernoulli activity marginal in the full original current-block
scalar profile. The other follower triples and each follower's held-arm and
private-ID scalars are retained in the product law. -/
theorem blockScalarProfile_activity_mass (p : Parameters)
    (j : Fin (p.m - 1)) :
    PrivateSourceStreams.blockScalarProfileLaw p
      (currentProfileActivitySet p j) =
        ENNReal.ofReal (1 / (p.m : ℝ)) := by
  let eval : GeneratedBlockDrawLaw.FollowerTripleProfile p →
      PrivateSourceStreams.BlockScalars := fun x => x (sourceFollowerIndex p j)
  let first : PrivateSourceStreams.BlockScalars → PrivateSourceStreams.Scalar :=
    Prod.fst
  let coinSet : Set PrivateSourceStreams.Scalar :=
    PrivateSourceStreams.activityScalarDraw p ⁻¹' {true}
  have heval : MeasurePreserving eval
      (PrivateSourceStreams.blockScalarProfileLaw p)
      PrivateSourceStreams.blockScalarsLaw := by
    change MeasurePreserving (Function.eval (sourceFollowerIndex p j))
      (Measure.pi (fun _ : Fin (p.m - 1) => PrivateSourceStreams.blockScalarsLaw))
      PrivateSourceStreams.blockScalarsLaw
    exact measurePreserving_eval
      (fun _ : Fin (p.m - 1) => PrivateSourceStreams.blockScalarsLaw)
      (sourceFollowerIndex p j)
  have hfirst : MeasurePreserving first PrivateSourceStreams.blockScalarsLaw
      ContinuousCategorical.uniform := by
    dsimp [first, PrivateSourceStreams.blockScalarsLaw]
    exact measurePreserving_fst
  have hmap := hfirst.comp heval
  have hcoin : MeasurableSet coinSet :=
    (PrivateSourceStreams.activityScalarDraw_measurable p)
      (measurableSet_singleton true)
  have hpre : currentProfileActivitySet p j = (first ∘ eval) ⁻¹' coinSet := by
    ext x
    rfl
  calc
    PrivateSourceStreams.blockScalarProfileLaw p (currentProfileActivitySet p j) =
        (PrivateSourceStreams.blockScalarProfileLaw p).map (first ∘ eval) coinSet := by
          rw [hpre, Measure.map_apply hmap.measurable hcoin]
    _ = ContinuousCategorical.uniform coinSet := by
          rw [hmap.map_eq]
    _ = ENNReal.ofReal (1 / (p.m : ℝ)) :=
          PrivateSourceStreams.activityScalarDraw_uniform_mass p true

/-- The activity event on the original full current-block profile is
measurable. -/
theorem measurableSet_currentProfileActivitySet (p : Parameters)
    (j : Fin (p.m - 1)) :
    MeasurableSet (currentProfileActivitySet p j) := by
  change MeasurableSet
    ((fun x : GeneratedBlockDrawLaw.FollowerTripleProfile p =>
      PrivateSourceStreams.activityScalarDraw p
        (x (sourceFollowerIndex p j)).1) ⁻¹' {true})
  exact ((PrivateSourceStreams.activityScalarDraw_measurable p).comp
    (measurable_fst.comp (measurable_pi_apply (sourceFollowerIndex p j))))
      (measurableSet_singleton true)

/-- The current full profile's private-ID field is the exact original
private-ID scalar U in the accepted focal split. -/
theorem generatedCurrentProfile_privateID_eq_originalU (p : Parameters)
    (s : Fin (n_boot p)) (j : Fin (p.m - 1))
    (hj : j.val + 1 < p.m) (b : ReferenceInitializationRun.Boundary p)
    (rho : ExtendedPrivateCoordinates p) :
    (generatedCurrentBlockProfile p s b rho j).2.2 =
      PrivateSourceStreams.privateIDScalarDraw p
        ((BootstrapPrivateIDFibers.splitEquiv p s j hj rho).2.1) := by
  change PrivateSourceStreams.privateIDScalarDraw p (rho.1.1 s j).2.2 =
    PrivateSourceStreams.privateIDScalarDraw p
      ((BootstrapPrivateIDFibers.splitEquiv p s j hj rho).2.1)
  rw [BootstrapPrivateIDFibers.split_id_scalar]

/-- For the actual processed boundary, physical activity of the selected
source follower is its original activity scalar in the full profile. -/
theorem actualIncomingActivity_eq_originalScalar (p : Parameters)
    (P : PublishedOutput p) (J : Fin (M p))
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (s : Fin (n_boot p)) (j : Fin (p.m - 1))
    (hj : j.val + 1 < p.m) (rho : ExtendedPrivateCoordinates p)
    (h : GeneratedForwardPrefixTests.processesBlock
      (GeneratedEligibleFamily.referenceInputOfPublishedOutput
        C_star C_h eta rewards J (P, rho)) s)
    (hin : j ∈
      (GeneratedForwardPrefixTests.actualPhysicalBlock
        (GeneratedEligibleFamily.referenceInputOfPublishedOutput
          C_star C_h eta rewards J (P, rho)) s h).uninformed) :
    (GeneratedForwardPrefixTests.actualPhysicalBlock
      (GeneratedEligibleFamily.referenceInputOfPublishedOutput
        C_star C_h eta rewards J (P, rho)) s h).active ⟨j, hin⟩ =
      PrivateSourceStreams.activityScalarDraw p (rho.1.1 s j).1 := by
  let x := GeneratedEligibleFamily.referenceInputOfPublishedOutput
    C_star C_h eta rewards J (P, rho)
  let b := ReferenceInitializationRun.run x s.val
  let hrem := GeneratedForwardPrefixTests.actualBlockRemaining x s h
  let e := GeneratedForwardPrefixTests.actualBlockIndex x s h
  let phys := ReferenceInitializationRun.physical
    (BootstrapPrivateIDFibers.initialRunInput p P J rewards C_star C_h eta rho) b hrem
  have hb : generatedBoundary p s P.1 (P.2 J) rewards C_star C_h eta rho = b := rfl
  have hc : b.completed = s.val := h.2
  have hn : b.crossing = none := h.1
  have hinput : x = BootstrapPrivateIDFibers.initialRunInput p P J rewards C_star C_h eta rho := rfl
  have hinCast : j ∈ (e ▸ phys).uninformed := by
    change j ∈
      (GeneratedForwardPrefixTests.actualPhysicalBlock x s h).uninformed
    exact hin
  have hcastUn : (e ▸ phys).uninformed = phys.uninformed :=
    GeneratedEligibleFamily.castPhysicalBlock_uninformed e phys
  have hinb : j ∈ ReferenceInitializationRun.uninformed b := by
    rw [hcastUn] at hinCast
    exact hinCast
  have hsame : sourceFollower p j = j := by apply Fin.ext; rfl
  have hinSource : sourceFollower p j ∈ ReferenceInitializationRun.uninformed b :=
    hsame ▸ hinb
  let i : {i // i ∈ ReferenceInitializationRun.uninformed b} :=
    ⟨sourceFollower p j, hinSource⟩
  have hraw := GeneratedPrivateIDFibers.physical_focal_fields p s j hj P J
    rewards C_star C_h eta rho b hrem hc hinSource
  have hrawActive :
      phys.active i = PrivateSourceStreams.activityScalarDraw p (rho.1.1 s j).1 := by
    have h := congrArg (fun d : PrivateSourceStreams.BlockDraw p => d.1) hraw
    change phys.active i = PrivateSourceStreams.activityScalarDraw p
      ((BootstrapPrivateIDFibers.splitEquiv p s j hj rho).1.1.1.1) at h
    rw [BootstrapPrivateIDFibers.split_activity_scalar] at h
    exact h
  have hcast :
      (e ▸ phys).active (GeneratedEligibleFamily.castPhysicalFollower e phys i) =
        phys.active i :=
    GeneratedEligibleFamily.castPhysicalFollower_active e phys i
  have hmember :
      GeneratedEligibleFamily.castPhysicalFollower e phys i =
        (⟨j, hin⟩ :
          {i // i ∈ (GeneratedForwardPrefixTests.actualPhysicalBlock x s h).uninformed}) := by
    apply Subtype.ext
    exact hsame
  calc
    (GeneratedForwardPrefixTests.actualPhysicalBlock x s h).active
        ⟨j, hin⟩ = phys.active i := by
          rw [hmember] at hcast
          change (e ▸ phys).active ⟨j, hin⟩ = phys.active i
          exact hcast
    _ = PrivateSourceStreams.activityScalarDraw p (rho.1.1 s j).1 := hrawActive

/-- The accepted output-side code is present exactly for a real active
incoming context with the ORIGINAL ID scalar `U`. -/
theorem actualIncomingPrivateID_eq_originalU (p : Parameters)
    (P : PublishedOutput p) (J : Fin (M p))
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (s : Fin (n_boot p)) (j : Fin (p.m - 1))
    (hj : j.val + 1 < p.m) (rho : ExtendedPrivateCoordinates p)
    (h : GeneratedForwardPrefixTests.processesBlock
      (GeneratedEligibleFamily.referenceInputOfPublishedOutput
        C_star C_h eta rewards J (P, rho)) s)
    (hin : j ∈
      (GeneratedForwardPrefixTests.actualPhysicalBlock
        (GeneratedEligibleFamily.referenceInputOfPublishedOutput
          C_star C_h eta rewards J (P, rho)) s h).uninformed) :
    (GeneratedForwardPrefixTests.actualPhysicalBlock
      (GeneratedEligibleFamily.referenceInputOfPublishedOutput
        C_star C_h eta rewards J (P, rho)) s h).privateId ⟨j, hin⟩ =
      PrivateSourceStreams.privateIDScalarDraw p
        ((BootstrapPrivateIDFibers.splitEquiv p s j hj rho).2.1) := by
  let x := GeneratedEligibleFamily.referenceInputOfPublishedOutput
    C_star C_h eta rewards J (P, rho)
  let b := ReferenceInitializationRun.run x s.val
  let hrem := GeneratedForwardPrefixTests.actualBlockRemaining x s h
  let e := GeneratedForwardPrefixTests.actualBlockIndex x s h
  let phys := ReferenceInitializationRun.physical
    (BootstrapPrivateIDFibers.initialRunInput p P J rewards C_star C_h eta rho) b hrem
  have hinCast : j ∈ (e ▸ phys).uninformed := by
    change j ∈ (GeneratedForwardPrefixTests.actualPhysicalBlock x s h).uninformed
    exact hin
  have hcastUn : (e ▸ phys).uninformed = phys.uninformed :=
    GeneratedEligibleFamily.castPhysicalBlock_uninformed e phys
  have hinb : j ∈ ReferenceInitializationRun.uninformed b := by
    rw [hcastUn] at hinCast
    exact hinCast
  have hsame : sourceFollower p j = j := by apply Fin.ext; rfl
  have hinSource : sourceFollower p j ∈ ReferenceInitializationRun.uninformed b :=
    hsame ▸ hinb
  let i : {i // i ∈ ReferenceInitializationRun.uninformed b} :=
    ⟨sourceFollower p j, hinSource⟩
  have hc : b.completed = s.val := h.2
  have hraw := GeneratedPrivateIDFibers.physical_focal_fields p s j hj P J
    rewards C_star C_h eta rho b hrem hc hinSource
  have hrawID : phys.privateId i =
      PrivateSourceStreams.privateIDScalarDraw p
        ((BootstrapPrivateIDFibers.splitEquiv p s j hj rho).2.1) := by
    have h := congrArg (fun d : PrivateSourceStreams.BlockDraw p => d.2.2) hraw
    change phys.privateId i =
      PrivateSourceStreams.privateIDScalarDraw p
        ((BootstrapPrivateIDFibers.splitEquiv p s j hj rho).2.1) at h
    exact h
  have hcast := GeneratedEligibleFamily.castPhysicalFollower_privateID e phys i
  have hmember :
      GeneratedEligibleFamily.castPhysicalFollower e phys i =
        (⟨j, hin⟩ :
          {i // i ∈ (GeneratedForwardPrefixTests.actualPhysicalBlock x s h).uninformed}) := by
    apply Subtype.ext
    exact hsame
  calc
    (GeneratedForwardPrefixTests.actualPhysicalBlock x s h).privateId ⟨j, hin⟩ =
        phys.privateId i := by
          rw [hmember] at hcast
          change (e ▸ phys).privateId ⟨j, hin⟩ = phys.privateId i
          exact hcast
    _ = PrivateSourceStreams.privateIDScalarDraw p
        ((BootstrapPrivateIDFibers.splitEquiv p s j hj rho).2.1) := hrawID

/-- The accepted output-side code is present exactly for a real active
incoming context and the same original `U` that supplies its physical ID. -/
theorem activePrivateIDCodeOnPublishedOutput_eq_some_iff_originalUContext
    (p : Parameters) (P : PublishedOutput p) (J : Fin (M p))
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (s : Fin (n_boot p)) (j : Fin (p.m - 1)) (rho : ExtendedPrivateCoordinates p)
    (u : Fin (A_id p)) :
    GeneratedEligibleFamily.activePrivateIDCodeOnPublishedOutput
      C_star C_h eta rewards J s j (P, rho) = some u ↔
      ∃ h : GeneratedForwardPrefixTests.processesBlock
          (GeneratedEligibleFamily.referenceInputOfPublishedOutput
            C_star C_h eta rewards J (P, rho)) s,
        ∃ a : GeneratedForwardPrefixTests.ActiveIncomingFollower
          (GeneratedEligibleFamily.referenceInputOfPublishedOutput
            C_star C_h eta rewards J (P, rho)) s h,
          a.val.val = j ∧
            PrivateSourceStreams.privateIDScalarDraw p
              ((BootstrapPrivateIDFibers.splitEquiv p s j
                (by
                  have hn := j.isLt
                  change j.val < p.m - 1 at hn
                  omega) rho).2.1) = u := by
  have hj : j.val + 1 < p.m := by
    have hn := j.isLt
    change j.val < p.m - 1 at hn
    omega
  constructor
  · intro hcode
    rcases (GeneratedFalseForwardEvent.activePrivateIDCodeOnPublishedOutput_eq_some_iff_actualContext
      C_star C_h eta rewards J P rho s j u).1 hcode with ⟨h, a, hindex, hid⟩
    have hin : j ∈
        (GeneratedForwardPrefixTests.actualPhysicalBlock
          (GeneratedEligibleFamily.referenceInputOfPublishedOutput
            C_star C_h eta rewards J (P, rho)) s h).uninformed := by
      exact hindex ▸ a.val.property
    have hsub : a.val = ⟨j, hin⟩ := Subtype.ext hindex
    have hU := actualIncomingPrivateID_eq_originalU p P J rewards C_star C_h
      eta s j hj rho h hin
    rw [hsub, hU] at hid
    exact ⟨h, a, hindex, hid⟩
  · rintro ⟨h, a, hindex, hU⟩
    have hin : j ∈
        (GeneratedForwardPrefixTests.actualPhysicalBlock
          (GeneratedEligibleFamily.referenceInputOfPublishedOutput
            C_star C_h eta rewards J (P, rho)) s h).uninformed := by
      exact hindex ▸ a.val.property
    have hsub : a.val = ⟨j, hin⟩ := Subtype.ext hindex
    have hphysical := actualIncomingPrivateID_eq_originalU p P J rewards C_star C_h
      eta s j hj rho h hin
    have hid :
        (GeneratedForwardPrefixTests.actualPhysicalBlock
          (GeneratedEligibleFamily.referenceInputOfPublishedOutput
            C_star C_h eta rewards J (P, rho)) s h).privateId a.val = u := by
      rw [hsub, hphysical]
      exact hU
    exact (GeneratedFalseForwardEvent.activePrivateIDCodeOnPublishedOutput_eq_some_iff_actualContext
      C_star C_h eta rewards J P rho s j u).2 ⟨h, a, hindex, hid⟩

/-- The accepted output-side code is present exactly for a real active
incoming context, retaining the accepted actual physical private ID witness. -/
theorem mem_activePrivateIDCodeSomeEvent_iff_actualContext (p : Parameters)
    (P : PublishedOutput p) (J : Fin (M p))
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (s : Fin (n_boot p)) (j : Fin (p.m - 1)) (rho : ExtendedPrivateCoordinates p) :
    rho ∈ activePrivateIDCodeSomeEvent p P J rewards C_star C_h eta s j ↔
      ∃ h : GeneratedForwardPrefixTests.processesBlock
          (GeneratedEligibleFamily.referenceInputOfPublishedOutput
            C_star C_h eta rewards J (P, rho)) s,
        ∃ a : GeneratedForwardPrefixTests.ActiveIncomingFollower
          (GeneratedEligibleFamily.referenceInputOfPublishedOutput
            C_star C_h eta rewards J (P, rho)) s h,
          a.val.val = j := by
  classical
  constructor
  · rintro ⟨u, hcode⟩
    rcases (activePrivateIDCodeOnPublishedOutput_eq_some_iff_originalUContext
      p P J rewards C_star C_h eta s j rho u).1 hcode with ⟨h, a, hindex, _⟩
    exact ⟨h, a, hindex⟩
  · rintro ⟨h, a, hindex⟩
    have hj : j.val + 1 < p.m := by
      have hn := j.isLt
      change j.val < p.m - 1 at hn
      omega
    have hin : j ∈
        (GeneratedForwardPrefixTests.actualPhysicalBlock
          (GeneratedEligibleFamily.referenceInputOfPublishedOutput
            C_star C_h eta rewards J (P, rho)) s h).uninformed := by
      exact hindex ▸ a.val.property
    have hU := actualIncomingPrivateID_eq_originalU p P J rewards C_star C_h
      eta s j hj rho h hin
    have hcode :=
      (activePrivateIDCodeOnPublishedOutput_eq_some_iff_originalUContext
        p P J rewards C_star C_h eta s j rho
        (PrivateSourceStreams.privateIDScalarDraw p
          ((BootstrapPrivateIDFibers.splitEquiv p s j hj rho).2.1))).2
        ⟨h, a, hindex, rfl⟩
    let u := PrivateSourceStreams.privateIDScalarDraw p
      ((BootstrapPrivateIDFibers.splitEquiv p s j hj rho).2.1)
    exact ⟨u, hcode⟩

/-- The processed-uninformed event is exactly the actual run's block-progress
and incoming condition. In particular, a stopped or already-informed
follower contributes no event. -/
theorem mem_processedUninformedEvent_iff_actualIncoming (p : Parameters)
    (P : PublishedOutput p) (J : Fin (M p))
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (s : Fin (n_boot p)) (j : Fin (p.m - 1)) (rho : ExtendedPrivateCoordinates p) :
    rho ∈ processedUninformedEvent p P J rewards C_star C_h eta s j ↔
      ∃ h : GeneratedForwardPrefixTests.processesBlock
          (GeneratedEligibleFamily.referenceInputOfPublishedOutput
            C_star C_h eta rewards J (P, rho)) s,
        j ∈
          (GeneratedForwardPrefixTests.actualPhysicalBlock
            (GeneratedEligibleFamily.referenceInputOfPublishedOutput
              C_star C_h eta rewards J (P, rho)) s h).uninformed := by
  let x := GeneratedEligibleFamily.referenceInputOfPublishedOutput
    C_star C_h eta rewards J (P, rho)
  let b := ReferenceInitializationRun.run x s.val
  have hb : generatedBoundary p s P.1 (P.2 J) rewards C_star C_h eta rho = b := rfl
  have hj : j.val + 1 < p.m := by
    have h := j.isLt
    change j.val < p.m - 1 at h
    omega
  constructor
  · intro he
    change processedUninformedBoundaryCondition p s j
      (generatedBoundary p s P.1 (P.2 J) rewards C_star C_h eta rho) at he
    rw [hb] at he
    rcases he with ⟨hn, hc, hin⟩
    have hprogress := GeneratedPrivateIDFibers.generatedBoundary_processed
      p s P J rewards C_star C_h eta rho hn
    have hcompleted : b.completed = s.val := hprogress.1
    have hrun : GeneratedForwardPrefixTests.processesBlock x s := ⟨hn, hcompleted⟩
    let hrem := GeneratedForwardPrefixTests.actualBlockRemaining x s hrun
    let e := GeneratedForwardPrefixTests.actualBlockIndex x s hrun
    let phys := ReferenceInitializationRun.physical x b hrem
    have hcastUn : (e ▸ phys).uninformed = phys.uninformed :=
      GeneratedEligibleFamily.castPhysicalBlock_uninformed e phys
    have hinFinal : j ∈ (e ▸ phys).uninformed := by
      rw [hcastUn]
      exact hin
    have hinActual : j ∈ (GeneratedForwardPrefixTests.actualPhysicalBlock x s hrun).uninformed := by
      change j ∈ (e ▸ phys).uninformed
      exact hinFinal
    exact ⟨hrun, hinActual⟩
  · rintro ⟨hrun, hin⟩
    have hn : b.crossing = none := hrun.1
    have hprogress := GeneratedPrivateIDFibers.generatedBoundary_processed
      p s P J rewards C_star C_h eta rho hn
    have hc : b.completed = s.val := hprogress.1
    let hrem := GeneratedForwardPrefixTests.actualBlockRemaining x s hrun
    let e := GeneratedForwardPrefixTests.actualBlockIndex x s hrun
    let phys := ReferenceInitializationRun.physical x b hrem
    have hcastUn : (e ▸ phys).uninformed = phys.uninformed :=
      GeneratedEligibleFamily.castPhysicalBlock_uninformed e phys
    have hinb : j ∈ ReferenceInitializationRun.uninformed b := by
      have hmem : j ∈ (e ▸ phys).uninformed := by
        change j ∈ (GeneratedForwardPrefixTests.actualPhysicalBlock x s hrun).uninformed
        exact hin
      rw [hcastUn] at hmem
      exact hmem
    change processedUninformedBoundaryCondition p s j
      (generatedBoundary p s P.1 (P.2 J) rewards C_star C_h eta rho)
    rw [hb]
    exact ⟨hn, hc, hinb⟩

/-- The output-side active code is present precisely when the real processed
incoming follower's original activity scalar is true. This uses the accepted
code-to-actual-ID equivalence and the accepted physical current-block draw
field law. -/
theorem mem_activePrivateIDCodeSomeEvent_iff_originalActivity (p : Parameters)
    (P : PublishedOutput p) (J : Fin (M p))
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (s : Fin (n_boot p)) (j : Fin (p.m - 1)) (rho : ExtendedPrivateCoordinates p) :
    rho ∈ activePrivateIDCodeSomeEvent p P J rewards C_star C_h eta s j ↔
      ∃ h : GeneratedForwardPrefixTests.processesBlock
          (GeneratedEligibleFamily.referenceInputOfPublishedOutput
            C_star C_h eta rewards J (P, rho)) s,
        j ∈
          (GeneratedForwardPrefixTests.actualPhysicalBlock
            (GeneratedEligibleFamily.referenceInputOfPublishedOutput
              C_star C_h eta rewards J (P, rho)) s h).uninformed ∧
        PrivateSourceStreams.activityScalarDraw p (rho.1.1 s j).1 = true := by
  constructor
  · intro hcode
    rcases (mem_activePrivateIDCodeSomeEvent_iff_actualContext p P J rewards
      C_star C_h eta s j rho).1 hcode with ⟨h, a, hindex⟩
    have hin : j ∈
        (GeneratedForwardPrefixTests.actualPhysicalBlock
          (GeneratedEligibleFamily.referenceInputOfPublishedOutput
            C_star C_h eta rewards J (P, rho)) s h).uninformed := by
      exact hindex ▸ a.val.property
    have hsub : a.val = ⟨j, hin⟩ := Subtype.ext hindex
    have hactive :
        (GeneratedForwardPrefixTests.actualPhysicalBlock
          (GeneratedEligibleFamily.referenceInputOfPublishedOutput
            C_star C_h eta rewards J (P, rho)) s h).active
          ⟨j, hin⟩ = true := by
      rw [← hsub]
      exact a.property
    have hj : j.val + 1 < p.m := by
      have h := j.isLt
      change j.val < p.m - 1 at h
      omega
    have hcoin := actualIncomingActivity_eq_originalScalar p P J rewards
      C_star C_h eta s j hj rho h hin
    exact ⟨h, hin, hcoin.symm.trans hactive⟩
  · rintro ⟨h, hin, hcoin⟩
    have hj : j.val + 1 < p.m := by
      have h := j.isLt
      change j.val < p.m - 1 at h
      omega
    have hactive := actualIncomingActivity_eq_originalScalar p P J rewards
      C_star C_h eta s j hj rho h hin
    have hctx :
        ∃ a : GeneratedForwardPrefixTests.ActiveIncomingFollower
          (GeneratedEligibleFamily.referenceInputOfPublishedOutput
            C_star C_h eta rewards J (P, rho)) s h,
          a.val.val = j := by
      let a : GeneratedForwardPrefixTests.ActiveIncomingFollower
          (GeneratedEligibleFamily.referenceInputOfPublishedOutput
            C_star C_h eta rewards J (P, rho)) s h :=
        ⟨⟨j, hin⟩, hactive.trans hcoin⟩
      refine ⟨a, ?_⟩
      apply Fin.ext
      rfl
    exact (mem_activePrivateIDCodeSomeEvent_iff_actualContext p P J rewards
      C_star C_h eta s j rho).2 (by rcases hctx with ⟨a, ha⟩; exact ⟨h, a, ha⟩)

/-- The accepted active code cuts out exactly the original scalar activity
coin among genuinely processed incoming opportunities. -/
theorem mem_activeProcessedUninformedEvent_iff_scalarActivity (p : Parameters)
    (P : PublishedOutput p) (J : Fin (M p))
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (s : Fin (n_boot p)) (j : Fin (p.m - 1)) (rho : ExtendedPrivateCoordinates p) :
    rho ∈ activeProcessedUninformedEvent p P J rewards C_star C_h eta s j ↔
      rho ∈ processedUninformedEvent p P J rewards C_star C_h eta s j ∧
        PrivateSourceStreams.activityScalarDraw p (rho.1.1 s j).1 = true := by
  constructor
  · rintro ⟨hprocessed, hcode⟩
    rcases (mem_activePrivateIDCodeSomeEvent_iff_originalActivity p P J rewards
      C_star C_h eta s j rho).1 hcode with ⟨_, _, hcoin⟩
    exact ⟨hprocessed, hcoin⟩
  · rintro ⟨hprocessed, hcoin⟩
    rcases (mem_processedUninformedEvent_iff_actualIncoming p P J rewards
      C_star C_h eta s j rho).1 hprocessed with ⟨h, hin⟩
    have hcode := (mem_activePrivateIDCodeSomeEvent_iff_originalActivity p P J rewards
      C_star C_h eta s j rho).2 ⟨h, hin, hcoin⟩
    exact ⟨hprocessed, hcode⟩

/-- The processed boundary event factors through the retained coordinates of
the genuine current-block split. -/
theorem processedUninformedEvent_eq_splitCylinder (p : Parameters)
    (P : PublishedOutput p) (J : Fin (M p))
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (s : Fin (n_boot p)) (j : Fin (p.m - 1)) :
    processedUninformedEvent p P J rewards C_star C_h eta s j =
      (GeneratedBlockDrawLaw.extendedPrivateBlockSplitEquiv p s) ⁻¹'
        (processedUninformedOtherSet p P J rewards C_star C_h eta s j ×ˢ
          (Set.univ : Set (GeneratedBlockDrawLaw.CurrentBlockCoordinates p))) := by
  ext rho
  simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, processedUninformedEvent,
    processedUninformedOtherSet]
  change processedUninformedBoundaryCondition p s j
      (GeneratedBlockDrawLaw.generatedBoundary p s P.1 (P.2 J)
        rewards C_star C_h eta rho) ↔
    processedUninformedBoundaryCondition p s j
      (GeneratedBlockDrawLaw.boundaryFromOther p s P.1 (P.2 J)
        rewards C_star C_h eta
        (GeneratedBlockDrawLaw.extendedPrivateBlockSplitEquiv p s rho).1) ∧ True
  rw [GeneratedBlockDrawLaw.generatedBoundary_eq_boundaryFromOther]
  simp

/-- The active event is the cylinder that leaves the full original follower
profile present and restricts just its selected activity scalar. The target
scalar and the original coordinator-selector scalar remain in their original
product coordinates. -/
theorem activeProcessedUninformedEvent_eq_splitCylinder (p : Parameters)
    (P : PublishedOutput p) (J : Fin (M p))
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (s : Fin (n_boot p)) (j : Fin (p.m - 1)) :
    activeProcessedUninformedEvent p P J rewards C_star C_h eta s j =
      (GeneratedBlockDrawLaw.extendedPrivateBlockSplitEquiv p s) ⁻¹'
        (processedUninformedOtherSet p P J rewards C_star C_h eta s j ×ˢ
          (currentProfileActivitySet p j ×ˢ
            (Set.univ : Set BootstrapPrivateRoundStreams.Scalar))) := by
  ext rho
  have hbase :
      rho ∈ processedUninformedEvent p P J rewards C_star C_h eta s j ↔
        (GeneratedBlockDrawLaw.extendedPrivateBlockSplitEquiv p s rho).1 ∈
          processedUninformedOtherSet p P J rewards C_star C_h eta s j := by
    change processedUninformedBoundaryCondition p s j
        (GeneratedBlockDrawLaw.generatedBoundary p s P.1 (P.2 J)
          rewards C_star C_h eta rho) ↔
      processedUninformedBoundaryCondition p s j
        (GeneratedBlockDrawLaw.boundaryFromOther p s P.1 (P.2 J)
          rewards C_star C_h eta
          (GeneratedBlockDrawLaw.extendedPrivateBlockSplitEquiv p s rho).1)
    rw [GeneratedBlockDrawLaw.generatedBoundary_eq_boundaryFromOther]
  have hcoin : PrivateSourceStreams.activityScalarDraw p (rho.1.1 s j).1 = true ↔
      (GeneratedBlockDrawLaw.extendedPrivateBlockSplitEquiv p s rho).2.1 ∈
        currentProfileActivitySet p j := by
    change PrivateSourceStreams.activityScalarDraw p (rho.1.1 s j).1 = true ↔
      PrivateSourceStreams.activityScalarDraw p
        (((GeneratedBlockDrawLaw.extendedPrivateBlockSplitEquiv p s rho).2.1)
          (sourceFollowerIndex p j)).1 = true
    have hprofile := GeneratedBlockDrawLaw.extendedPrivateBlockSplit_profile p s rho
    have hindex : sourceFollowerIndex p j = j := by
      apply Fin.ext
      rfl
    rw [← hprofile, hindex]
  rw [mem_activeProcessedUninformedEvent_iff_scalarActivity p P J rewards
    C_star C_h eta s j rho, hbase, hcoin]
  simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, and_true]

/-- Measurability of the exact retained-boundary/current-profile cylinder. -/
theorem measurableSet_activeProcessedUninformedSplitCylinder (p : Parameters)
    (P : PublishedOutput p) (J : Fin (M p))
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (s : Fin (n_boot p)) (j : Fin (p.m - 1)) :
    MeasurableSet
      (processedUninformedOtherSet p P J rewards C_star C_h eta s j ×ˢ
        (currentProfileActivitySet p j ×ˢ
          (Set.univ : Set BootstrapPrivateRoundStreams.Scalar))) := by
  exact (measurableSet_processedUninformedOtherSet p P J rewards C_star C_h
    eta s j).prod ((measurableSet_currentProfileActivitySet p j).prod
      MeasurableSet.univ)

/-- Exact unnormalized current-coin admission identity on the original
extended private law. This identity also covers a zero-mass retained
boundary. -/
theorem activeProcessedUninformedEvent_measure_eq_activityFactor (p : Parameters)
    (P : PublishedOutput p) (J : Fin (M p))
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (s : Fin (n_boot p)) (j : Fin (p.m - 1)) :
    BootstrapPrivateRoundStreams.extendedPrivateLaw p
        (activeProcessedUninformedEvent p P J rewards C_star C_h eta s j) =
      ENNReal.ofReal (1 / (p.m : ℝ)) *
        BootstrapPrivateRoundStreams.extendedPrivateLaw p
          (processedUninformedEvent p P J rewards C_star C_h eta s j) := by
  let e := GeneratedBlockDrawLaw.extendedPrivateBlockSplitEquiv p s
  let O := processedUninformedOtherSet p P J rewards C_star C_h eta s j
  let A := currentProfileActivitySet p j
  let μO := GeneratedBlockDrawLaw.otherPrivateLaw p s
  let μP := PrivateSourceStreams.blockScalarProfileLaw p
  let μU := ContinuousCategorical.uniform
  have hsplit := GeneratedBlockDrawLaw.extendedPrivateBlockSplit_measurePreserving p s
  have hsplitCylinder : MeasurableSet (O ×ˢ (A ×ˢ (Set.univ : Set BootstrapPrivateRoundStreams.Scalar))) := by
    exact (measurableSet_processedUninformedOtherSet p P J rewards C_star C_h
      eta s j).prod ((measurableSet_currentProfileActivitySet p j).prod MeasurableSet.univ)
  have hbaseCylinder : MeasurableSet (O ×ˢ (Set.univ : Set (GeneratedBlockDrawLaw.CurrentBlockCoordinates p))) := by
    exact (measurableSet_processedUninformedOtherSet p P J rewards C_star C_h eta s j).prod
      MeasurableSet.univ
  have hactiveSet : activeProcessedUninformedEvent p P J rewards C_star C_h eta s j =
      e ⁻¹' (O ×ˢ (A ×ˢ (Set.univ : Set BootstrapPrivateRoundStreams.Scalar))) := by
    simpa [e, O, A] using
      (activeProcessedUninformedEvent_eq_splitCylinder p P J rewards C_star C_h eta s j)
  have hbaseSet : processedUninformedEvent p P J rewards C_star C_h eta s j =
      e ⁻¹' (O ×ˢ (Set.univ : Set (GeneratedBlockDrawLaw.CurrentBlockCoordinates p))) := by
    simpa [e, O] using
      (processedUninformedEvent_eq_splitCylinder p P J rewards C_star C_h eta s j)
  have hprofileMass : μP A = ENNReal.ofReal (1 / (p.m : ℝ)) := by
    simpa [A] using blockScalarProfile_activity_mass p j
  have hactiveMeasure :
      BootstrapPrivateRoundStreams.extendedPrivateLaw p
          (activeProcessedUninformedEvent p P J rewards C_star C_h eta s j) =
        μO O * (μP A * μU Set.univ) := by
    calc
      _ = BootstrapPrivateRoundStreams.extendedPrivateLaw p
          (e ⁻¹' (O ×ˢ (A ×ˢ (Set.univ : Set BootstrapPrivateRoundStreams.Scalar)))) :=
            congrArg (fun S => BootstrapPrivateRoundStreams.extendedPrivateLaw p S) hactiveSet
      _ = (μO.prod (μP.prod μU))
          (O ×ˢ (A ×ˢ (Set.univ : Set BootstrapPrivateRoundStreams.Scalar))) :=
            hsplit.measure_preimage hsplitCylinder.nullMeasurableSet
      _ = μO O * (μP A * μU Set.univ) := by rw [Measure.prod_prod, Measure.prod_prod]
  have hbaseMeasure :
      BootstrapPrivateRoundStreams.extendedPrivateLaw p
          (processedUninformedEvent p P J rewards C_star C_h eta s j) = μO O := by
    calc
      _ = BootstrapPrivateRoundStreams.extendedPrivateLaw p
          (e ⁻¹' (O ×ˢ (Set.univ : Set (GeneratedBlockDrawLaw.CurrentBlockCoordinates p)))) :=
            congrArg (fun S => BootstrapPrivateRoundStreams.extendedPrivateLaw p S) hbaseSet
      _ = (μO.prod (μP.prod μU))
          (O ×ˢ (Set.univ : Set (GeneratedBlockDrawLaw.CurrentBlockCoordinates p))) :=
            hsplit.measure_preimage hbaseCylinder.nullMeasurableSet
      _ = μO O := by simp [Measure.prod_prod]
  calc
    _ = μO O * (μP A * μU Set.univ) := hactiveMeasure
    _ = ENNReal.ofReal (1 / (p.m : ℝ)) * μO O := by
      rw [hprofileMass, measure_univ]
      ring
    _ = _ := by rw [hbaseMeasure]

/-- Each actual active processed-uninformed event has real mass at most
`1/m`. The exact identity above is applied without conditioning on a positive
boundary event. -/
theorem activeProcessedUninformedEvent_real_mass_le (p : Parameters)
    (P : PublishedOutput p) (J : Fin (M p))
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (s : Fin (n_boot p)) (j : Fin (p.m - 1)) :
    (BootstrapPrivateRoundStreams.extendedPrivateLaw p).real
        (activeProcessedUninformedEvent p P J rewards C_star C_h eta s j) ≤
      1 / (p.m : ℝ) := by
  have hfactor := activeProcessedUninformedEvent_measure_eq_activityFactor
    p P J rewards C_star C_h eta s j
  have hnonneg : 0 ≤ 1 / (p.m : ℝ) := by positivity
  rw [measureReal_def, hfactor, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hnonneg]
  calc
    (1 / (p.m : ℝ)) *
        (BootstrapPrivateRoundStreams.extendedPrivateLaw p
          (processedUninformedEvent p P J rewards C_star C_h eta s j)).toReal ≤
      (1 / (p.m : ℝ)) * 1 :=
        mul_le_mul_of_nonneg_left measureReal_le_one hnonneg
    _ = 1 / (p.m : ℝ) := by ring

/-- Summing actual admission masses over every source block and all `d=m-1`
followers gives `n_boot * d/m`. -/
theorem total_activeAdmission_real_mass_le_fraction (p : Parameters)
    (P : PublishedOutput p) (J : Fin (M p))
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) :
    (∑ s : Fin (n_boot p), ∑ j : Fin (p.m - 1),
      (BootstrapPrivateRoundStreams.extendedPrivateLaw p).real
        (activeProcessedUninformedEvent p P J rewards C_star C_h eta s j)) ≤
      (n_boot p : ℝ) * ((p.m - 1 : ℕ) : ℝ) / (p.m : ℝ) := by
  calc
    _ ≤ ∑ s : Fin (n_boot p), ∑ j : Fin (p.m - 1), (1 / (p.m : ℝ)) := by
      apply Finset.sum_le_sum
      intro s hs
      apply Finset.sum_le_sum
      intro j hj
      exact activeProcessedUninformedEvent_real_mass_le p P J rewards C_star C_h eta s j
    _ = (n_boot p : ℝ) * ((p.m - 1 : ℕ) : ℝ) / (p.m : ℝ) := by
      simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
      ring

/-- The total actual admission mass is at most `n_boot`, since the admitted
follower fraction `(m-1)/m` is at most one. -/
theorem total_activeAdmission_real_mass_le_nboot (p : Parameters)
    (P : PublishedOutput p) (J : Fin (M p))
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) :
    (∑ s : Fin (n_boot p), ∑ j : Fin (p.m - 1),
      (BootstrapPrivateRoundStreams.extendedPrivateLaw p).real
        (activeProcessedUninformedEvent p P J rewards C_star C_h eta s j)) ≤
      (n_boot p : ℝ) := by
  have htotal := total_activeAdmission_real_mass_le_fraction p P J rewards C_star C_h eta
  have hmpos : 0 < (p.m : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) p.two_le_m)
  have hratio : ((p.m - 1 : ℕ) : ℝ) / (p.m : ℝ) ≤ 1 := by
    apply (div_le_iff₀ hmpos).2
    have hnat : p.m - 1 ≤ p.m := Nat.sub_le _ _
    have hnatReal : ((p.m - 1 : ℕ) : ℝ) ≤ (p.m : ℝ) := by exact_mod_cast hnat
    simpa only [one_mul] using hnatReal
  have hbound :
      (n_boot p : ℝ) * ((p.m - 1 : ℕ) : ℝ) / (p.m : ℝ) ≤ (n_boot p : ℝ) := by
    calc
      (n_boot p : ℝ) * ((p.m - 1 : ℕ) : ℝ) / (p.m : ℝ) =
          (n_boot p : ℝ) * (((p.m - 1 : ℕ) : ℝ) / (p.m : ℝ)) := by ring
      _ ≤ (n_boot p : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left hratio (Nat.cast_nonneg _)
      _ = (n_boot p : ℝ) := by ring
  exact htotal.trans hbound

/-- Optional nonnegative-epsilon scaling of the complete fixed-table
admission budget. -/
theorem epsilon_mul_total_activeAdmission_real_mass_le (p : Parameters)
    (P : PublishedOutput p) (J : Fin (M p))
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (epsilon : ℝ)
    (hepsilon : 0 ≤ epsilon) :
    epsilon *
        (∑ s : Fin (n_boot p), ∑ j : Fin (p.m - 1),
          (BootstrapPrivateRoundStreams.extendedPrivateLaw p).real
            (activeProcessedUninformedEvent p P J rewards C_star C_h eta s j)) ≤
      epsilon * (n_boot p : ℝ) :=
  mul_le_mul_of_nonneg_left
    (total_activeAdmission_real_mass_le_nboot p P J rewards C_star C_h eta) hepsilon

end Bandits.Support.GeneratedPrivateActivityBudget

end
