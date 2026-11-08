/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.GeneratedBlockStartLaw
public import Bandits.Support.BootstrapBlockIsolation
public import Bandits.Support.BootstrapPhysicalInput

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Guard laws at an actual generated bootstrap boundary

This module converts the accepted law of the original complete row and
extended-private coordinates into the guards used at an actual generated
boundary. It keeps the entire future-row event in every unnormalized formula,
and identifies incoming physical fields with the corresponding original
profile entries before using the finite product law.

Sources: `sources/zip4/manuscript/appendix_b_communication.tex:376-395,
485-506,635-675` and `sources/zip4/manuscript/07_public_setup.tex:63-112`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal BigOperators

open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.BootstrapWeightPotential
open Bandits.Support.BootstrapBlockIsolation
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.PrivateSourceStreams
open Bandits.Support.ReferenceInitializationRun
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.GeneratedBlockDrawLaw
open Bandits.Support.GeneratedBlockStartLaw
open Bandits.Support.BootstrapPhysicalInput

namespace Bandits.Support.GeneratedBlockGuardLaw

abbrev Parameters := ConstructorDimensions.Parameters

abbrev OriginalCoordinates (p : Parameters) :=
  GeneratedBlockStartLaw.OriginalCoordinates p

abbrev Profile (p : Parameters) := PrivateSourceStreams.BlockDrawProfile p

abbrev Incoming (p : Parameters) (b : ReferenceInitializationRun.Boundary p) :=
  {j : ActiveRoundActions.Follower p.m // j ∈ ReferenceInitializationRun.uninformed b}

abbrev IncomingProfile (p : Parameters) (b : ReferenceInitializationRun.Boundary p) :=
  Incoming p b → PrivateSourceStreams.BlockDraw p

abbrev FutureRow (p : Parameters) (s : Fin (n_boot p)) :=
  CompleteRowStoppingLaw.FutureArray p (GeneratedBlockStartLaw.blockStartIndex p s)

/-- The accepted physical action carrier and private draw carrier use the
same follower labels. -/
theorem sourceFollowerIndex_injective (p : Parameters) :
    Function.Injective (BootstrapPhysicalInput.sourceFollowerIndex p) := by
  intro i j hij
  apply Fin.ext
  exact congrArg Fin.val hij

/-- The exact source-coordinate image of the actual incoming uninformed set.
No coordinates outside this image are declared to be physical followers. -/
def sourceIncomingFinset (p : Parameters)
    (b : ReferenceInitializationRun.Boundary p) : Finset (Fin (p.m - 1)) :=
  (ReferenceInitializationRun.uninformed b).image
    (BootstrapPhysicalInput.sourceFollowerIndex p)

theorem mem_sourceIncomingFinset_iff (p : Parameters)
    (b : ReferenceInitializationRun.Boundary p) (k : Fin (p.m - 1)) :
    k ∈ sourceIncomingFinset p b ↔
      ∃ j : ActiveRoundActions.Follower p.m,
        j ∈ ReferenceInitializationRun.uninformed b ∧
        BootstrapPhysicalInput.sourceFollowerIndex p j = k := by
  simp [sourceIncomingFinset, Finset.mem_image]

theorem sourceIncomingFinset_card (p : Parameters)
    (b : ReferenceInitializationRun.Boundary p) :
    (sourceIncomingFinset p b).card =
      (ReferenceInitializationRun.uninformed b).card := by
  unfold sourceIncomingFinset
  exact Finset.card_image_of_injective _ (sourceFollowerIndex_injective p)

theorem sourceIncomingFinset_card_le (p : Parameters)
    (b : ReferenceInitializationRun.Boundary p) :
    (sourceIncomingFinset p b).card ≤ p.m - 1 := by
  rw [sourceIncomingFinset_card]
  exact (Finset.card_le_univ _).trans_eq (by simp [PublicDiscreteDraws.followerCount])

theorem sourceFollowerIndex_mem_sourceIncomingFinset (p : Parameters)
    (b : ReferenceInitializationRun.Boundary p) (i : Incoming p b) :
    BootstrapPhysicalInput.sourceFollowerIndex p i.1 ∈ sourceIncomingFinset p b := by
  exact Finset.mem_image.mpr ⟨i.1, i.2, rfl⟩

theorem sourceIncomingFinset_other_count_le (p : Parameters)
    (b : ReferenceInitializationRun.Boundary p) (i : Incoming p b) :
    (sourceIncomingFinset p b).card - 1 ≤ p.m - 2 :=
  BootstrapBlockIsolation.otherUninformed_count_le p (sourceIncomingFinset p b)
    (BootstrapPhysicalInput.sourceFollowerIndex p i.1)
    (sourceFollowerIndex_mem_sourceIncomingFinset p b i)

/-- Restrict a complete accepted original-coordinate profile to exactly the
incoming physical follower set. -/
def sourceRestrictedProfile (p : Parameters)
    (b : ReferenceInitializationRun.Boundary p) (c : Profile p) : IncomingProfile p b :=
  fun i => c (BootstrapPhysicalInput.sourceFollowerIndex p i.1)

/-- Physical triples at the accepted processed boundary, indexed only by
actual incoming followers. -/
def actualProcessedProfile (p : Parameters) (s : Fin (n_boot p))
    (ids : CompletePublicTable.IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (b : ReferenceInitializationRun.Boundary p) (hcompleted : b.completed = s.val)
    (hnotStopped : b.crossing = none) (e : OriginalCoordinates p) : IncomingProfile p b :=
  fun i => GeneratedBlockDrawLaw.generatedPhysicalBlockDraw p s ids e.1 rewards
    C_star C_h eta b hcompleted hnotStopped i e.2

/-- The physical coordinator target at the accepted processed boundary. -/
def actualProcessedTarget (p : Parameters) (s : Fin (n_boot p))
    (ids : CompletePublicTable.IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (b : ReferenceInitializationRun.Boundary p) (hcompleted : b.completed = s.val)
    (hnotStopped : b.crossing = none) (e : OriginalCoordinates p) : Fin p.K :=
  GeneratedBlockDrawLaw.generatedPhysicalBlockTarget p s ids e.1 rewards C_star C_h eta
    b hcompleted hnotStopped e.2

/-- Exact physical-field identification for every incoming follower. The
fields are read from the actual processed block in the reference run. -/
theorem actualProcessedProfile_eq_generatedProfile (p : Parameters)
    (s : Fin (n_boot p)) (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (b : ReferenceInitializationRun.Boundary p) (hcompleted : b.completed = s.val)
    (hnotStopped : b.crossing = none) (e : OriginalCoordinates p)
    (hb : GeneratedBlockStartLaw.boundaryAtOriginal p s ids rewards C_star C_h eta e = b) :
    actualProcessedProfile p s ids rewards C_star C_h eta b hcompleted hnotStopped e =
      sourceRestrictedProfile p b
        (GeneratedBlockDrawLaw.generatedCurrentBlockProfile p s b e.2) := by
  funext i
  have hfields := GeneratedBlockDrawLaw.actualProcessedBlock_draw_fields p s ids e.1
    rewards C_star C_h eta e.2 b (by
      simpa [GeneratedBlockStartLaw.boundaryAtOriginal] using hb) hcompleted hnotStopped
  rcases hfields with ⟨_, hprofile, _⟩
  simpa [actualProcessedProfile, sourceRestrictedProfile,
    GeneratedBlockDrawLaw.generatedPhysicalBlockDraw] using hprofile i

/-- Exact physical target identification at the accepted processed boundary. -/
theorem actualProcessedTarget_eq_generatedTarget (p : Parameters)
    (s : Fin (n_boot p)) (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (b : ReferenceInitializationRun.Boundary p) (hcompleted : b.completed = s.val)
    (hnotStopped : b.crossing = none) (e : OriginalCoordinates p)
    (hb : GeneratedBlockStartLaw.boundaryAtOriginal p s ids rewards C_star C_h eta e = b) :
    actualProcessedTarget p s ids rewards C_star C_h eta b hcompleted hnotStopped e =
      GeneratedBlockDrawLaw.generatedCurrentTarget p s e.2 := by
  have hfields := GeneratedBlockDrawLaw.actualProcessedBlock_draw_fields p s ids e.1
    rewards C_star C_h eta e.2 b (by
      simpa [GeneratedBlockStartLaw.boundaryAtOriginal] using hb) hcompleted hnotStopped
  rcases hfields with ⟨_, _, htarget⟩
  simpa [actualProcessedTarget, GeneratedBlockDrawLaw.generatedPhysicalBlockTarget] using
    htarget

/-- Focal incoming follower stays active on held arm `a`. -/
def focalActiveHeldGuard (p : Parameters)
    (b : ReferenceInitializationRun.Boundary p) (i : Incoming p b) (a : Fin p.K) :
    Set (IncomingProfile p b) :=
  {q | (q i).1 = true ∧ (q i).2.1 = a}

/-- Focal active-held event plus inactivity of every other actual incoming
uninformed follower. -/
def focalIsolationGuard (p : Parameters)
    (b : ReferenceInitializationRun.Boundary p) (i : Incoming p b) (a : Fin p.K) :
    Set (IncomingProfile p b) :=
  {q | (q i).1 = true ∧ (q i).2.1 = a ∧
    ∀ j : Incoming p b, j ≠ i → (q j).1 = false}

/-- The isolated focal active-held event with its original private index `U`
specified. -/
def focalIsolationPrivateIdGuard (p : Parameters)
    (b : ReferenceInitializationRun.Boundary p) (i : Incoming p b) (a : Fin p.K)
    (u : Fin (A_id p)) : Set (IncomingProfile p b) :=
  {q | q ∈ focalIsolationGuard p b i a ∧ (q i).2.2 = u}

/-- Every actual incoming uninformed follower is inactive. -/
def allIncomingInactiveGuard (p : Parameters)
    (b : ReferenceInitializationRun.Boundary p) : Set (IncomingProfile p b) :=
  {q | ∀ j : Incoming p b, (q j).1 = false}

/-- A guarded event at the actual generated boundary, with the whole future
row event retained. Both exact field-identification clauses are part of the
event, and are discharged only on the specified boundary atom. -/
def generatedProcessedGuardFutureEvent (p : Parameters)
    (s : Fin (n_boot p)) (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (b : ReferenceInitializationRun.Boundary p) (hcompleted : b.completed = s.val)
    (hnotStopped : b.crossing = none)
    (G : Set (IncomingProfile p b)) (H : Set (Fin p.K))
    (C : Set (FutureRow p s)) : Set (OriginalCoordinates p) :=
  {e | GeneratedBlockStartLaw.boundaryAtOriginal p s ids rewards C_star C_h eta e = b ∧
    actualProcessedProfile p s ids rewards C_star C_h eta b hcompleted hnotStopped e ∈ G ∧
    actualProcessedTarget p s ids rewards C_star C_h eta b hcompleted hnotStopped e ∈ H ∧
    GeneratedBlockStartLaw.futureRowOf p s e ∈ C ∧
    actualProcessedProfile p s ids rewards C_star C_h eta b hcompleted hnotStopped e =
      sourceRestrictedProfile p b
        (GeneratedBlockDrawLaw.generatedCurrentBlockProfile p s b e.2) ∧
    actualProcessedTarget p s ids rewards C_star C_h eta b hcompleted hnotStopped e =
      GeneratedBlockDrawLaw.generatedCurrentTarget p s e.2}

/-- Source profile atoms whose actual incoming restriction satisfies `G`. -/
def profileGuardAtoms (p : Parameters)
    (b : ReferenceInitializationRun.Boundary p) (G : Set (IncomingProfile p b)) :
    Finset (Profile p) :=
  by classical exact Finset.univ.filter fun c => sourceRestrictedProfile p b c ∈ G

/-- Uniform target atoms selected by `H`. -/
def targetGuardAtoms (p : Parameters) (H : Set (Fin p.K)) : Finset (Fin p.K) :=
  by classical exact Finset.univ.filter fun z => z ∈ H

/-- Joint profile and target atoms selected by the actual guard. -/
def guardedProfileTargetAtoms (p : Parameters)
    (b : ReferenceInitializationRun.Boundary p) (G : Set (IncomingProfile p b))
    (H : Set (Fin p.K)) : Finset (Profile p × Fin p.K) :=
  (profileGuardAtoms p b G).product (targetGuardAtoms p H)

private theorem generatedProcessedGuardFutureEvent_eq_atom_union (p : Parameters)
    (s : Fin (n_boot p)) (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (b : ReferenceInitializationRun.Boundary p) (hcompleted : b.completed = s.val)
    (hnotStopped : b.crossing = none)
    (G : Set (IncomingProfile p b)) (H : Set (Fin p.K))
    (C : Set (FutureRow p s)) :
    generatedProcessedGuardFutureEvent p s ids rewards C_star C_h eta b hcompleted
      hnotStopped G H C =
    ⋃ q ∈ guardedProfileTargetAtoms p b G H,
      GeneratedBlockStartLaw.generatedBoundaryProfileTargetFutureEvent p s ids rewards
        C_star C_h eta b q.1 q.2 C := by
  classical
  ext e
  constructor
  · intro he
    let c := GeneratedBlockDrawLaw.generatedCurrentBlockProfile p s b e.2
    let z := GeneratedBlockDrawLaw.generatedCurrentTarget p s e.2
    have hp := actualProcessedProfile_eq_generatedProfile p s ids rewards C_star C_h eta
      b hcompleted hnotStopped e he.1
    have hz := actualProcessedTarget_eq_generatedTarget p s ids rewards C_star C_h eta
      b hcompleted hnotStopped e he.1
    have hP : sourceRestrictedProfile p b c ∈ G := by
      dsimp [c]
      rw [← hp]
      exact he.2.1
    have hZ : z ∈ H := by
      dsimp [z]
      rw [← hz]
      exact he.2.2.1
    have hq : (c, z) ∈ guardedProfileTargetAtoms p b G H := by
      simp [guardedProfileTargetAtoms, profileGuardAtoms, targetGuardAtoms, hP, hZ]
    refine Set.mem_iUnion.2 ⟨(c, z), Set.mem_iUnion.2 ⟨hq, ?_⟩⟩
    exact ⟨he.1, rfl, rfl, he.2.2.2.1⟩
  · intro he
    rcases Set.mem_iUnion.1 he with ⟨q, hq⟩
    rcases Set.mem_iUnion.1 hq with ⟨hqmem, hcell⟩
    have hguard : q ∈ guardedProfileTargetAtoms p b G H := hqmem
    have hguard' : sourceRestrictedProfile p b q.1 ∈ G ∧ q.2 ∈ H := by
      simpa [guardedProfileTargetAtoms, profileGuardAtoms, targetGuardAtoms] using hguard
    simp only [GeneratedBlockStartLaw.generatedBoundaryProfileTargetFutureEvent,
      Set.mem_ofPred_eq] at hcell
    have hp := actualProcessedProfile_eq_generatedProfile p s ids rewards C_star C_h eta
      b hcompleted hnotStopped e hcell.1
    have hz := actualProcessedTarget_eq_generatedTarget p s ids rewards C_star C_h eta
      b hcompleted hnotStopped e hcell.1
    have hP : sourceRestrictedProfile p b
        (GeneratedBlockDrawLaw.generatedCurrentBlockProfile p s b e.2) ∈ G := by
      rw [hcell.2.1]
      exact hguard'.1
    have hZ : GeneratedBlockDrawLaw.generatedCurrentTarget p s e.2 ∈ H := by
      rw [hcell.2.2.1]
      exact hguard'.2
    refine ⟨hcell.1, ?_, ?_, hcell.2.2.2, ?_, ?_⟩
    · rw [hp]
      exact hP
    · rw [hz]
      exact hZ
    · exact hp
    · exact hz

private theorem sum_profile_atoms_eq_ofReal_probability (p : Parameters)
    (b : ReferenceInitializationRun.Boundary p) (G : Set (IncomingProfile p b)) :
    (∑ c ∈ profileGuardAtoms p b G,
      BootstrapBlockIsolation.privateBlockProfileLaw p b.numerators b.weight_ge_one c) =
    ENNReal.ofReal (BootstrapBlockIsolation.privateBlockProfileEventProbability p
      b.numerators b.weight_ge_one (fun c => sourceRestrictedProfile p b c ∈ G)) := by
  classical
  let law := BootstrapBlockIsolation.privateBlockProfileLaw p b.numerators b.weight_ge_one
  let guard := fun c : Profile p => sourceRestrictedProfile p b c ∈ G
  calc
    (∑ c ∈ profileGuardAtoms p b G, law c) =
        ∑ c : Profile p, if guard c then law c else 0 := by
      simp only [profileGuardAtoms, Finset.sum_filter]
      simp [guard]
    _ = ∑ c : Profile p,
        ENNReal.ofReal (if guard c then (law c).toReal else 0) := by
      apply Finset.sum_congr rfl
      intro c hc
      by_cases hg : guard c
      · simp [hg, ENNReal.ofReal_toReal (law.apply_ne_top c)]
      · simp [hg]
    _ = ENNReal.ofReal (∑ c : Profile p,
          if guard c then (law c).toReal else 0) := by
      symm
      apply ENNReal.ofReal_sum_of_nonneg
      intro c hc
      by_cases hg : guard c <;> simp [hg]
    _ = ENNReal.ofReal (BootstrapBlockIsolation.privateBlockProfileEventProbability p
          b.numerators b.weight_ge_one guard) := by
      simp [guard, law, BootstrapBlockIsolation.privateBlockProfileEventProbability]

private theorem sum_target_atoms_eq_ofReal_probability (p : Parameters)
    (H : Set (Fin p.K)) :
    (∑ _z ∈ targetGuardAtoms p H, ENNReal.ofReal (1 / (p.K : ℝ))) =
      ENNReal.ofReal (∑ _z ∈ targetGuardAtoms p H, 1 / (p.K : ℝ)) := by
  classical
  have hkpos : (0 : ℝ) < (p.K : ℝ) := by exact_mod_cast K_pos p
  symm
  apply ENNReal.ofReal_sum_of_nonneg
  intro z hz
  positivity

private theorem sum_guarded_atom_masses (p : Parameters)
    (b : ReferenceInitializationRun.Boundary p) (G : Set (IncomingProfile p b))
    (H : Set (Fin p.K)) (B F : ℝ≥0∞) :
    (∑ q ∈ guardedProfileTargetAtoms p b G H,
        B * BootstrapBlockIsolation.privateBlockProfileLaw p b.numerators b.weight_ge_one q.1 *
          ENNReal.ofReal (1 / (p.K : ℝ)) * F) =
      B * (∑ c ∈ profileGuardAtoms p b G,
          BootstrapBlockIsolation.privateBlockProfileLaw p b.numerators b.weight_ge_one c) *
        (∑ _z ∈ targetGuardAtoms p H, ENNReal.ofReal (1 / (p.K : ℝ))) * F := by
  classical
  rw [guardedProfileTargetAtoms, Finset.product_eq_sprod, Finset.sum_product]
  calc
    _ = ∑ c ∈ profileGuardAtoms p b G,
        ∑ _z ∈ targetGuardAtoms p H,
          (B * BootstrapBlockIsolation.privateBlockProfileLaw p b.numerators
            b.weight_ge_one c) * (ENNReal.ofReal (1 / (p.K : ℝ)) * F) := by
      apply Finset.sum_congr rfl
      intro c hc
      apply Finset.sum_congr rfl
      intro z hz
      ac_rfl
    _ = ∑ c ∈ profileGuardAtoms p b G,
        (B * BootstrapBlockIsolation.privateBlockProfileLaw p b.numerators
          b.weight_ge_one c) *
          (∑ _z ∈ targetGuardAtoms p H,
            ENNReal.ofReal (1 / (p.K : ℝ)) * F) := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [Finset.mul_sum]
    _ = ∑ c ∈ profileGuardAtoms p b G,
        (B * BootstrapBlockIsolation.privateBlockProfileLaw p b.numerators
          b.weight_ge_one c) *
          ((∑ _z ∈ targetGuardAtoms p H, ENNReal.ofReal (1 / (p.K : ℝ))) * F) := by
      congr 1
      rw [← Finset.sum_mul]
    _ = (∑ c ∈ profileGuardAtoms p b G,
        B * BootstrapBlockIsolation.privateBlockProfileLaw p b.numerators
          b.weight_ge_one c) *
          ((∑ _z ∈ targetGuardAtoms p H, ENNReal.ofReal (1 / (p.K : ℝ))) * F) := by
      rw [← Finset.sum_mul]
    _ = _ := by
      rw [← Finset.mul_sum]
      ac_rfl

/-- Every guarded event is measurable as a finite disjoint union of actual
generated boundary/profile/target/future atoms. -/
theorem measurableSet_generatedProcessedGuardFutureEvent (p : Parameters)
    (s : Fin (n_boot p)) (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (b : ReferenceInitializationRun.Boundary p) (hcompleted : b.completed = s.val)
    (hnotStopped : b.crossing = none)
    (G : Set (IncomingProfile p b)) (H : Set (Fin p.K))
    (C : Set (FutureRow p s)) (hC : MeasurableSet C) :
    MeasurableSet (generatedProcessedGuardFutureEvent p s ids rewards C_star C_h eta b
      hcompleted hnotStopped G H C) := by
  rw [generatedProcessedGuardFutureEvent_eq_atom_union]
  exact Finset.measurableSet_biUnion (guardedProfileTargetAtoms p b G H) fun q hq =>
    GeneratedBlockStartLaw.measurableSet_generatedBoundaryProfileTargetFutureEvent p s ids
      rewards C_star C_h eta b q.1 q.2 C hC

/-- Unnormalized generated-boundary law for a guard on the actual incoming
physical profile, an arbitrary coordinator-target guard, and an arbitrary
measurable event of the entire future row. It is proved by summing the exact
accepted boundary/profile/target atoms. -/
theorem generatedProcessedGuardFutureEvent_joint_law (p : Parameters)
    (s : Fin (n_boot p)) (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (b : ReferenceInitializationRun.Boundary p) (hcompleted : b.completed = s.val)
    (hnotStopped : b.crossing = none)
    (G : Set (IncomingProfile p b)) (H : Set (Fin p.K))
    (C : Set (FutureRow p s)) (hC : MeasurableSet C) :
    GeneratedBlockStartLaw.originalCoordinatesLaw p
      (generatedProcessedGuardFutureEvent p s ids rewards C_star C_h eta b hcompleted
        hnotStopped G H C) =
      GeneratedBlockStartLaw.originalCoordinatesLaw p
        {e | GeneratedBlockStartLaw.boundaryAtOriginal p s ids rewards C_star C_h eta e = b} *
      ENNReal.ofReal (BootstrapBlockIsolation.privateBlockProfileEventProbability p
        b.numerators b.weight_ge_one
        (fun c => sourceRestrictedProfile p b c ∈ G)) *
      ENNReal.ofReal (∑ _z ∈ targetGuardAtoms p H, 1 / (p.K : ℝ)) *
      CompleteRowStoppingLaw.futureArrayLaw p (GeneratedBlockStartLaw.blockStartIndex p s) C := by
  classical
  rw [generatedProcessedGuardFutureEvent_eq_atom_union]
  have hdisj : Set.PairwiseDisjoint
      (↑(guardedProfileTargetAtoms p b G H) : Set (Profile p × Fin p.K))
      (fun q : Profile p × Fin p.K =>
        GeneratedBlockStartLaw.generatedBoundaryProfileTargetFutureEvent p s ids
          rewards C_star C_h eta b q.1 q.2 C) := by
    intro q hq r hr hqr
    apply Set.disjoint_left.2
    intro e heq her
    simp only [GeneratedBlockStartLaw.generatedBoundaryProfileTargetFutureEvent,
      Set.mem_ofPred_eq] at heq her
    apply hqr
    apply Prod.ext
    · exact heq.2.1.symm.trans her.2.1
    · exact heq.2.2.1.symm.trans her.2.2.1
  have hmeas : ∀ q ∈ guardedProfileTargetAtoms p b G H,
      MeasurableSet (GeneratedBlockStartLaw.generatedBoundaryProfileTargetFutureEvent p s ids
        rewards C_star C_h eta b q.1 q.2 C) := by
    intro q hq
    exact GeneratedBlockStartLaw.measurableSet_generatedBoundaryProfileTargetFutureEvent
      p s ids rewards C_star C_h eta b q.1 q.2 C hC
  calc
    _ = ∑ q ∈ guardedProfileTargetAtoms p b G H,
        GeneratedBlockStartLaw.originalCoordinatesLaw p
          (GeneratedBlockStartLaw.generatedBoundaryProfileTargetFutureEvent p s ids
            rewards C_star C_h eta b q.1 q.2 C) :=
      MeasureTheory.measure_biUnion_finset hdisj hmeas
    _ = ∑ q ∈ guardedProfileTargetAtoms p b G H,
        (GeneratedBlockStartLaw.originalCoordinatesLaw p
            {e | GeneratedBlockStartLaw.boundaryAtOriginal p s ids rewards C_star C_h eta e = b} *
          BootstrapBlockIsolation.privateBlockProfileLaw p b.numerators b.weight_ge_one q.1 *
          ENNReal.ofReal (1 / (p.K : ℝ)) *
          CompleteRowStoppingLaw.futureArrayLaw p
            (GeneratedBlockStartLaw.blockStartIndex p s) C) := by
      apply Finset.sum_congr rfl
      intro q hq
      exact GeneratedBlockStartLaw.generatedBoundary_jointProfileTargetFuture_factorization
        p s ids rewards C_star C_h eta b q.1 q.2 C hC
    _ = _ := by
      rw [sum_guarded_atom_masses, sum_profile_atoms_eq_ofReal_probability,
        sum_target_atoms_eq_ofReal_probability]

/-- The all-target atom sum is one. -/
theorem targetProbability_univ (p : Parameters) :
    (∑ _z ∈ targetGuardAtoms p (Set.univ : Set (Fin p.K)),
      1 / (p.K : ℝ)) = 1 := by
  classical
  have hset : targetGuardAtoms p (Set.univ : Set (Fin p.K)) = Finset.univ := by
    ext z
    simp [targetGuardAtoms]
  rw [hset]
  calc
    _ = ∑ z : Fin p.K, 1 / (p.K : ℝ) := by simp
    _ = (p.K : ℝ) * (1 / (p.K : ℝ)) := by
      simp [Finset.sum_const, nsmul_eq_mul, Fintype.card_fin]
    _ = 1 := by
      field_simp [Nat.cast_ne_zero.mpr (K_pos p).ne']

private theorem profileProbability_focalActiveHeld (p : Parameters)
    (b : ReferenceInitializationRun.Boundary p) (i : Incoming p b) (a : Fin p.K) :
    BootstrapBlockIsolation.privateBlockProfileEventProbability p b.numerators
      b.weight_ge_one (fun c => sourceRestrictedProfile p b c ∈ focalActiveHeldGuard p b i a) =
      BootstrapWeightPotential.probability (b_N p)
        (b.numerators (BootstrapPhysicalInput.sourceFollowerIndex p i.1)) a / (p.m : ℝ) := by
  have hevent : (fun c : Profile p =>
      sourceRestrictedProfile p b c ∈ focalActiveHeldGuard p b i a) =
      BootstrapBlockIsolation.distinguishedEvent
        (BootstrapPhysicalInput.sourceFollowerIndex p i.1) a := by
    funext c
    apply propext
    simp [focalActiveHeldGuard, sourceRestrictedProfile,
      BootstrapBlockIsolation.distinguishedEvent]
  rw [hevent]
  exact BootstrapBlockIsolation.distinguishedEvent_probability p b.numerators
    b.weight_ge_one (BootstrapPhysicalInput.sourceFollowerIndex p i.1) a

private theorem sourceRestriction_focalIsolation_iff (p : Parameters)
    (b : ReferenceInitializationRun.Boundary p) (i : Incoming p b) (a : Fin p.K)
    (c : Profile p) :
    sourceRestrictedProfile p b c ∈ focalIsolationGuard p b i a ↔
      BootstrapBlockIsolation.isolatedBootstrapEvent (sourceIncomingFinset p b)
        (BootstrapPhysicalInput.sourceFollowerIndex p i.1) a c := by
  constructor
  · intro h
    refine ⟨⟨h.1, h.2.1⟩, ?_⟩
    intro k hk
    obtain ⟨hkNe, hkU⟩ := Finset.mem_erase.mp hk
    obtain ⟨j, hj, hindex⟩ := (mem_sourceIncomingFinset_iff p b k).mp hkU
    have hji : (⟨j, hj⟩ : Incoming p b) ≠ i := by
      intro hEq
      have hEqIndex : k = BootstrapPhysicalInput.sourceFollowerIndex p i.1 := by
        have hjiVal : j = i.1 := congrArg Subtype.val hEq
        exact hindex.symm.trans
          (congrArg (BootstrapPhysicalInput.sourceFollowerIndex p) hjiVal)
      exact hkNe hEqIndex
    simpa [sourceRestrictedProfile, hindex] using h.2.2 ⟨j, hj⟩ hji
  · rintro ⟨hactive, hinactive⟩
    refine ⟨?_, ?_, ?_⟩
    · simpa [sourceRestrictedProfile, focalIsolationGuard,
        BootstrapBlockIsolation.distinguishedEvent] using hactive.1
    · simpa [sourceRestrictedProfile, focalIsolationGuard,
        BootstrapBlockIsolation.distinguishedEvent] using hactive.2
    · intro j hji
      have hindexNe : BootstrapPhysicalInput.sourceFollowerIndex p j.1 ≠
          BootstrapPhysicalInput.sourceFollowerIndex p i.1 := by
        intro hEq
        exact hji (Subtype.ext (sourceFollowerIndex_injective p hEq))
      have hmember := sourceFollowerIndex_mem_sourceIncomingFinset p b j
      have hstatus := hinactive (BootstrapPhysicalInput.sourceFollowerIndex p j.1)
        (Finset.mem_erase.mpr ⟨hindexNe, hmember⟩)
      simpa [sourceRestrictedProfile] using hstatus

private theorem profileProbability_focalIsolation (p : Parameters)
    (b : ReferenceInitializationRun.Boundary p) (i : Incoming p b) (a : Fin p.K) :
    BootstrapBlockIsolation.privateBlockProfileEventProbability p b.numerators
      b.weight_ge_one (fun c => sourceRestrictedProfile p b c ∈ focalIsolationGuard p b i a) =
      (BootstrapWeightPotential.probability (b_N p)
        (b.numerators (BootstrapPhysicalInput.sourceFollowerIndex p i.1)) a / (p.m : ℝ)) *
        (1 - 1 / (p.m : ℝ)) ^ ((sourceIncomingFinset p b).card - 1) := by
  have hevent : (fun c : Profile p =>
      sourceRestrictedProfile p b c ∈ focalIsolationGuard p b i a) =
      BootstrapBlockIsolation.isolatedBootstrapEvent (sourceIncomingFinset p b)
        (BootstrapPhysicalInput.sourceFollowerIndex p i.1) a := by
    funext c
    exact propext (sourceRestriction_focalIsolation_iff p b i a c)
  rw [hevent]
  exact BootstrapBlockIsolation.isolatedBootstrapEvent_probability p b.numerators
    b.weight_ge_one (sourceIncomingFinset p b)
    (BootstrapPhysicalInput.sourceFollowerIndex p i.1)
    (sourceFollowerIndex_mem_sourceIncomingFinset p b i) a

private theorem profileProbability_focalIsolationPrivateId (p : Parameters)
    (b : ReferenceInitializationRun.Boundary p) (i : Incoming p b) (a : Fin p.K)
    (u : Fin (A_id p)) :
    BootstrapBlockIsolation.privateBlockProfileEventProbability p b.numerators
      b.weight_ge_one
      (fun c => sourceRestrictedProfile p b c ∈ focalIsolationPrivateIdGuard p b i a u) =
      ((BootstrapWeightPotential.probability (b_N p)
          (b.numerators (BootstrapPhysicalInput.sourceFollowerIndex p i.1)) a / (p.m : ℝ)) *
        BootstrapBlockConstruction.privateIdProbability p u) *
        (1 - 1 / (p.m : ℝ)) ^ ((sourceIncomingFinset p b).card - 1) := by
  have hevent : (fun c : Profile p =>
      sourceRestrictedProfile p b c ∈ focalIsolationPrivateIdGuard p b i a u) =
      (fun c => BootstrapBlockIsolation.isolatedBootstrapEvent (sourceIncomingFinset p b)
        (BootstrapPhysicalInput.sourceFollowerIndex p i.1) a c ∧
        (c (BootstrapPhysicalInput.sourceFollowerIndex p i.1)).2.2 = u) := by
    funext c
    apply propext
    change (sourceRestrictedProfile p b c ∈ focalIsolationGuard p b i a ∧
      (sourceRestrictedProfile p b c i).2.2 = u) ↔ _
    rw [sourceRestriction_focalIsolation_iff]
    rfl
  rw [hevent]
  exact BootstrapBlockIsolation.isolatedBootstrapEvent_privateId_probability p b.numerators
    b.weight_ge_one (sourceIncomingFinset p b)
    (BootstrapPhysicalInput.sourceFollowerIndex p i.1)
    (sourceFollowerIndex_mem_sourceIncomingFinset p b i) a u

private theorem profileProbability_allIncomingInactive (p : Parameters)
    (b : ReferenceInitializationRun.Boundary p) :
    BootstrapBlockIsolation.privateBlockProfileEventProbability p b.numerators
      b.weight_ge_one
      (fun c => sourceRestrictedProfile p b c ∈ allIncomingInactiveGuard p b) =
      (1 - 1 / (p.m : ℝ)) ^ (sourceIncomingFinset p b).card := by
  classical
  let U := sourceIncomingFinset p b
  let condition : Fin (p.m - 1) → PrivateSourceStreams.BlockDraw p → Prop :=
    fun k outcome => k ∈ U → outcome.1 = false
  have hevent : (fun c : Profile p =>
      sourceRestrictedProfile p b c ∈ allIncomingInactiveGuard p b) =
      fun c => ∀ k, condition k (c k) := by
    funext c
    apply propext
    constructor
    · intro h k hk
      obtain ⟨i, hi, hindex⟩ := (mem_sourceIncomingFinset_iff p b k).mp hk
      have hstatus := h ⟨i, hi⟩
      simpa [sourceRestrictedProfile, hindex] using hstatus
    · intro h i
      have hstatus := h (BootstrapPhysicalInput.sourceFollowerIndex p i.1)
        (sourceFollowerIndex_mem_sourceIncomingFinset p b i)
      simpa [condition, sourceRestrictedProfile] using hstatus
  rw [hevent, BootstrapBlockIsolation.privateBlockProfileEventProbability_forall]
  have hprod :
      (∏ k : Fin (p.m - 1),
        BootstrapBlockIsolation.privateBlockDrawEventMass p (b.numerators k)
          (b.weight_ge_one k) (condition k)) =
        ∏ k : Fin (p.m - 1),
          if k ∈ U then BootstrapBlockConstruction.activityProbability p false else 1 := by
    apply Finset.prod_congr rfl
    intro k hk
    by_cases hku : k ∈ U
    · simp [condition, hku,
        BootstrapBlockIsolation.privateBlockDrawEventMass,
        BootstrapBlockIsolation.privateBlockDrawLaw_inactive_event_mass]
    · simp [condition, hku,
        BootstrapBlockIsolation.privateBlockDrawEventMass,
        BootstrapBlockIsolation.privateBlockDrawLaw_real_mass_sum_eq_one]
  rw [hprod, Finset.prod_ite_mem]
  simp [U, BootstrapBlockConstruction.activityProbability]

/-- A focal active-held event, including any measurable event of the entire
future row, has boundary mass times `p_b(a)/m` times that future-row mass. -/
theorem focalActiveHeld_joint_future_law (p : Parameters)
    (s : Fin (n_boot p)) (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (b : ReferenceInitializationRun.Boundary p) (hcompleted : b.completed = s.val)
    (hnotStopped : b.crossing = none) (i : Incoming p b) (a : Fin p.K)
    (C : Set (FutureRow p s)) (hC : MeasurableSet C) :
    GeneratedBlockStartLaw.originalCoordinatesLaw p
      (generatedProcessedGuardFutureEvent p s ids rewards C_star C_h eta b hcompleted
        hnotStopped (focalActiveHeldGuard p b i a) Set.univ C) =
      GeneratedBlockStartLaw.originalCoordinatesLaw p
        {e | GeneratedBlockStartLaw.boundaryAtOriginal p s ids rewards C_star C_h eta e = b} *
      ENNReal.ofReal (BootstrapWeightPotential.probability (b_N p)
        (b.numerators (BootstrapPhysicalInput.sourceFollowerIndex p i.1)) a / (p.m : ℝ)) *
      CompleteRowStoppingLaw.futureArrayLaw p (GeneratedBlockStartLaw.blockStartIndex p s) C := by
  rw [generatedProcessedGuardFutureEvent_joint_law p s ids rewards C_star C_h eta b
      hcompleted hnotStopped (focalActiveHeldGuard p b i a) Set.univ C hC,
    profileProbability_focalActiveHeld,
    targetProbability_univ]
  simp

/-- Requiring every other actual incoming uninformed follower to be inactive
multiplies the focal active-held mass by the exact product over the source
image. -/
theorem focalIsolation_joint_future_law (p : Parameters)
    (s : Fin (n_boot p)) (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (b : ReferenceInitializationRun.Boundary p) (hcompleted : b.completed = s.val)
    (hnotStopped : b.crossing = none) (i : Incoming p b) (a : Fin p.K)
    (C : Set (FutureRow p s)) (hC : MeasurableSet C) :
    GeneratedBlockStartLaw.originalCoordinatesLaw p
      (generatedProcessedGuardFutureEvent p s ids rewards C_star C_h eta b hcompleted
        hnotStopped (focalIsolationGuard p b i a) Set.univ C) =
      GeneratedBlockStartLaw.originalCoordinatesLaw p
        {e | GeneratedBlockStartLaw.boundaryAtOriginal p s ids rewards C_star C_h eta e = b} *
      ENNReal.ofReal ((BootstrapWeightPotential.probability (b_N p)
        (b.numerators (BootstrapPhysicalInput.sourceFollowerIndex p i.1)) a / (p.m : ℝ)) *
        (1 - 1 / (p.m : ℝ)) ^ ((sourceIncomingFinset p b).card - 1)) *
      CompleteRowStoppingLaw.futureArrayLaw p (GeneratedBlockStartLaw.blockStartIndex p s) C := by
  rw [generatedProcessedGuardFutureEvent_joint_law p s ids rewards C_star C_h eta b
      hcompleted hnotStopped (focalIsolationGuard p b i a) Set.univ C hC,
    profileProbability_focalIsolation,
    targetProbability_univ]
  simp

/-- Specifying the actual focal private index `U=u` adds its original uniform
`1/A_id` factor without conditioning on peer private-ID paths. -/
theorem focalIsolationPrivateId_joint_future_law (p : Parameters)
    (s : Fin (n_boot p)) (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (b : ReferenceInitializationRun.Boundary p) (hcompleted : b.completed = s.val)
    (hnotStopped : b.crossing = none) (i : Incoming p b) (a : Fin p.K)
    (u : Fin (A_id p)) (C : Set (FutureRow p s)) (hC : MeasurableSet C) :
    GeneratedBlockStartLaw.originalCoordinatesLaw p
      (generatedProcessedGuardFutureEvent p s ids rewards C_star C_h eta b hcompleted
        hnotStopped (focalIsolationPrivateIdGuard p b i a u) Set.univ C) =
      GeneratedBlockStartLaw.originalCoordinatesLaw p
        {e | GeneratedBlockStartLaw.boundaryAtOriginal p s ids rewards C_star C_h eta e = b} *
      ENNReal.ofReal (((BootstrapWeightPotential.probability (b_N p)
        (b.numerators (BootstrapPhysicalInput.sourceFollowerIndex p i.1)) a / (p.m : ℝ)) *
        (1 / (A_id p : ℝ))) *
        (1 - 1 / (p.m : ℝ)) ^ ((sourceIncomingFinset p b).card - 1)) *
      CompleteRowStoppingLaw.futureArrayLaw p (GeneratedBlockStartLaw.blockStartIndex p s) C := by
  rw [generatedProcessedGuardFutureEvent_joint_law p s ids rewards C_star C_h eta b
      hcompleted hnotStopped (focalIsolationPrivateIdGuard p b i a u) Set.univ C hC,
    profileProbability_focalIsolationPrivateId, targetProbability_univ]
  simp [BootstrapBlockConstruction.privateIdProbability]

private theorem targetAvoidance_probability (p : Parameters) (a : Fin p.K) :
    (∑ _z ∈ targetGuardAtoms p {z | z ≠ a}, 1 / (p.K : ℝ)) =
      ((p.K - 1 : ℕ) : ℝ) / (p.K : ℝ) := by
  classical
  have ha : a ∈ (Finset.univ : Finset (Fin p.K)) := Finset.mem_univ _
  have hatoms : targetGuardAtoms p {z | z ≠ a} = Finset.univ.erase a := by
    ext z
    simp [targetGuardAtoms]
  calc
    _ = ∑ z ∈ Finset.univ.erase a, 1 / (p.K : ℝ) := by rw [hatoms]
    _ = ((p.K - 1 : ℕ) : ℝ) * (1 / (p.K : ℝ)) := by
      simp [Finset.sum_const, nsmul_eq_mul, Finset.card_erase_of_mem ha,
        Fintype.card_fin]
    _ = ((p.K - 1 : ℕ) : ℝ) / (p.K : ℝ) := by ring

/-- The coordinator's independent target avoids the focal held arm with exact
factor `(K-1)/K`, retaining the full future-row event. -/
theorem focalTargetAvoidance_joint_future_law (p : Parameters)
    (s : Fin (n_boot p)) (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (b : ReferenceInitializationRun.Boundary p) (hcompleted : b.completed = s.val)
    (hnotStopped : b.crossing = none) (i : Incoming p b) (a : Fin p.K)
    (C : Set (FutureRow p s)) (hC : MeasurableSet C) :
    GeneratedBlockStartLaw.originalCoordinatesLaw p
      (generatedProcessedGuardFutureEvent p s ids rewards C_star C_h eta b hcompleted
        hnotStopped (focalActiveHeldGuard p b i a) {z | z ≠ a} C) =
      GeneratedBlockStartLaw.originalCoordinatesLaw p
        {e | GeneratedBlockStartLaw.boundaryAtOriginal p s ids rewards C_star C_h eta e = b} *
      ENNReal.ofReal (BootstrapWeightPotential.probability (b_N p)
        (b.numerators (BootstrapPhysicalInput.sourceFollowerIndex p i.1)) a / (p.m : ℝ)) *
      ENNReal.ofReal (((p.K - 1 : ℕ) : ℝ) / (p.K : ℝ)) *
      CompleteRowStoppingLaw.futureArrayLaw p (GeneratedBlockStartLaw.blockStartIndex p s) C := by
  rw [generatedProcessedGuardFutureEvent_joint_law p s ids rewards C_star C_h eta b
      hcompleted hnotStopped (focalActiveHeldGuard p b i a) {z | z ≠ a} C hC,
    profileProbability_focalActiveHeld,
    targetAvoidance_probability]

/-- All incoming followers inactive has exact activity factor `q^|U|`. -/
theorem allIncomingInactive_joint_future_law (p : Parameters)
    (s : Fin (n_boot p)) (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (b : ReferenceInitializationRun.Boundary p) (hcompleted : b.completed = s.val)
    (hnotStopped : b.crossing = none) (C : Set (FutureRow p s)) (hC : MeasurableSet C) :
    GeneratedBlockStartLaw.originalCoordinatesLaw p
      (generatedProcessedGuardFutureEvent p s ids rewards C_star C_h eta b hcompleted
        hnotStopped (allIncomingInactiveGuard p b) Set.univ C) =
      GeneratedBlockStartLaw.originalCoordinatesLaw p
        {e | GeneratedBlockStartLaw.boundaryAtOriginal p s ids rewards C_star C_h eta e = b} *
      ENNReal.ofReal ((1 - 1 / (p.m : ℝ)) ^ (sourceIncomingFinset p b).card) *
      CompleteRowStoppingLaw.futureArrayLaw p (GeneratedBlockStartLaw.blockStartIndex p s) C := by
  rw [generatedProcessedGuardFutureEvent_joint_law p s ids rewards C_star C_h eta b
      hcompleted hnotStopped (allIncomingInactiveGuard p b) Set.univ C hC,
    profileProbability_allIncomingInactive, targetProbability_univ]
  simp

private theorem inactive_power_m_minus_one_ge_quarter (p : Parameters) :
    (1 / 4 : ℝ) ≤ (1 - 1 / (p.m : ℝ)) ^ (p.m - 1) := by
  have hm1 : 1 ≤ p.m := le_trans (by decide) p.two_le_m
  have hmpos : 0 < (p.m : ℝ) := Nat.cast_pos.mpr (m_pos p)
  have hsubcast : ((p.m - 1 : ℕ) : ℝ) = (p.m : ℝ) - 1 := by
    rw [Nat.cast_sub hm1]
    norm_num
  let x : ℝ := 1 + ((p.m - 1 : ℕ) : ℝ)⁻¹
  have hx : 1 ≤ x := by
    dsimp [x]
    exact le_add_of_nonneg_right (inv_nonneg.mpr (Nat.cast_nonneg _))
  have hexp : x ^ (p.m - 1) ≤ Real.exp 1 := by
    dsimp [x]
    exact Real.one_add_inv_pow_le_exp
  have hpow_lt : x ^ (p.m - 1) < 3 :=
    hexp.trans_lt Real.exp_one_lt_three
  have hsubpos : 0 < (p.m : ℝ) - 1 := by
    have hmNat : 1 < p.m := lt_of_lt_of_le (by decide) p.two_le_m
    exact sub_pos.mpr (by exact_mod_cast hmNat)
  have hq : 1 - 1 / (p.m : ℝ) = x⁻¹ := by
    dsimp [x]
    rw [hsubcast]
    field_simp [hmpos.ne', hsubpos.ne']
    ring
  have hinv : (1 / 3 : ℝ) < (x ^ (p.m - 1))⁻¹ := by
    simpa [one_div] using
      (one_div_lt_one_div_of_lt (a := x ^ (p.m - 1)) (b := (3 : ℝ))
        (pow_pos (by linarith [hx]) _) hpow_lt)
  exact (calc
    (1 / 4 : ℝ) ≤ 1 / 3 := by norm_num
    _ < (x ^ (p.m - 1))⁻¹ := hinv
    _ = (1 - 1 / (p.m : ℝ)) ^ (p.m - 1) := by rw [hq, inv_pow]).le

/-- The actual number of incoming uninformed followers is at most `m-1`, so
the all-inactive activity factor is at least one quarter. -/
theorem allIncomingInactive_probability_ge_quarter (p : Parameters)
    (b : ReferenceInitializationRun.Boundary p) :
    (1 / 4 : ℝ) ≤ (1 - 1 / (p.m : ℝ)) ^ (sourceIncomingFinset p b).card := by
  have hqnonneg : 0 ≤ 1 - 1 / (p.m : ℝ) :=
    BootstrapBlockConstruction.activityProbability_nonneg p false
  have hqle : 1 - 1 / (p.m : ℝ) ≤ 1 := by
    have hmpos : 0 < (p.m : ℝ) := Nat.cast_pos.mpr (m_pos p)
    have hdiv : 0 ≤ 1 / (p.m : ℝ) := by positivity
    linarith
  calc
    (1 / 4 : ℝ) ≤ (1 - 1 / (p.m : ℝ)) ^ (p.m - 1) :=
      inactive_power_m_minus_one_ge_quarter p
    _ ≤ (1 - 1 / (p.m : ℝ)) ^ (sourceIncomingFinset p b).card :=
      pow_le_pow_of_le_one hqnonneg hqle (sourceIncomingFinset_card_le p b)

/-- Isolation has probability at least one quarter relative to the focal
active-held boundary event, expressed without dividing by either boundary
mass or future-row mass. -/
theorem focalIsolation_mass_ge_quarter (p : Parameters)
    (s : Fin (n_boot p)) (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (b : ReferenceInitializationRun.Boundary p) (hcompleted : b.completed = s.val)
    (hnotStopped : b.crossing = none) (i : Incoming p b) (a : Fin p.K)
    (C : Set (FutureRow p s)) (hC : MeasurableSet C) :
    (1 / 4 : ℝ≥0∞) *
      GeneratedBlockStartLaw.originalCoordinatesLaw p
        (generatedProcessedGuardFutureEvent p s ids rewards C_star C_h eta b hcompleted
          hnotStopped (focalActiveHeldGuard p b i a) Set.univ C) ≤
      GeneratedBlockStartLaw.originalCoordinatesLaw p
        (generatedProcessedGuardFutureEvent p s ids rewards C_star C_h eta b hcompleted
          hnotStopped (focalIsolationGuard p b i a) Set.univ C) := by
  have hcount := sourceIncomingFinset_other_count_le p b i
  have hqnonneg : 0 ≤ 1 - 1 / (p.m : ℝ) :=
    BootstrapBlockConstruction.activityProbability_nonneg p false
  have hqle : 1 - 1 / (p.m : ℝ) ≤ 1 := by
    have hmpos : 0 < (p.m : ℝ) := Nat.cast_pos.mpr (m_pos p)
    have hdiv : 0 ≤ 1 / (p.m : ℝ) := by positivity
    linarith
  have hpow : (1 / 4 : ℝ) ≤
      (1 - 1 / (p.m : ℝ)) ^ ((sourceIncomingFinset p b).card - 1) := by
    calc
      (1 / 4 : ℝ) ≤ (1 - 1 / (p.m : ℝ)) ^ (p.m - 2) :=
        BootstrapBlockIsolation.inactivity_power_lower_bound p
      _ ≤ (1 - 1 / (p.m : ℝ)) ^ ((sourceIncomingFinset p b).card - 1) :=
        pow_le_pow_of_le_one hqnonneg hqle hcount
  have hprob : 0 < BootstrapWeightPotential.probability (b_N p)
      (b.numerators (BootstrapPhysicalInput.sourceFollowerIndex p i.1)) a :=
    BootstrapBlockConstruction.heldArmProbability_pos p
      (b.numerators (BootstrapPhysicalInput.sourceFollowerIndex p i.1)) a
  have hfp : 0 ≤ BootstrapWeightPotential.probability (b_N p)
      (b.numerators (BootstrapPhysicalInput.sourceFollowerIndex p i.1)) a / (p.m : ℝ) :=
    div_nonneg hprob.le (Nat.cast_nonneg _)
  have hreal := mul_le_mul_of_nonneg_left hpow hfp
  have hreal' : (1 / 4 : ℝ) *
      (BootstrapWeightPotential.probability (b_N p)
        (b.numerators (BootstrapPhysicalInput.sourceFollowerIndex p i.1)) a / (p.m : ℝ)) ≤
      (BootstrapWeightPotential.probability (b_N p)
        (b.numerators (BootstrapPhysicalInput.sourceFollowerIndex p i.1)) a / (p.m : ℝ)) *
        (1 - 1 / (p.m : ℝ)) ^ ((sourceIncomingFinset p b).card - 1) := by
    simpa only [mul_comm] using hreal
  have hfactor : ENNReal.ofReal (1 / 4 : ℝ) *
      ENNReal.ofReal (BootstrapWeightPotential.probability (b_N p)
        (b.numerators (BootstrapPhysicalInput.sourceFollowerIndex p i.1)) a / (p.m : ℝ)) ≤
      ENNReal.ofReal ((BootstrapWeightPotential.probability (b_N p)
        (b.numerators (BootstrapPhysicalInput.sourceFollowerIndex p i.1)) a / (p.m : ℝ)) *
        (1 - 1 / (p.m : ℝ)) ^ ((sourceIncomingFinset p b).card - 1)) := by
    rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 4)]
    exact ENNReal.ofReal_le_ofReal hreal'
  rw [focalActiveHeld_joint_future_law p s ids rewards C_star C_h eta b hcompleted
      hnotStopped i a C hC,
    focalIsolation_joint_future_law p s ids rewards C_star C_h eta b hcompleted
      hnotStopped i a C hC]
  have hquarterENN : (1 / 4 : ℝ≥0∞) = ENNReal.ofReal (1 / 4 : ℝ) := by
    norm_num [ENNReal.ofReal_div_of_pos]
  rw [hquarterENN]
  calc
    _ = (GeneratedBlockStartLaw.originalCoordinatesLaw p
          {e | GeneratedBlockStartLaw.boundaryAtOriginal p s ids rewards C_star C_h eta e = b} *
        CompleteRowStoppingLaw.futureArrayLaw p
          (GeneratedBlockStartLaw.blockStartIndex p s) C) *
        (ENNReal.ofReal (1 / 4 : ℝ) *
          ENNReal.ofReal (BootstrapWeightPotential.probability (b_N p)
            (b.numerators (BootstrapPhysicalInput.sourceFollowerIndex p i.1)) a / (p.m : ℝ))) := by
      ac_rfl
    _ ≤ (GeneratedBlockStartLaw.originalCoordinatesLaw p
          {e | GeneratedBlockStartLaw.boundaryAtOriginal p s ids rewards C_star C_h eta e = b} *
        CompleteRowStoppingLaw.futureArrayLaw p
          (GeneratedBlockStartLaw.blockStartIndex p s) C) *
        ENNReal.ofReal ((BootstrapWeightPotential.probability (b_N p)
          (b.numerators (BootstrapPhysicalInput.sourceFollowerIndex p i.1)) a / (p.m : ℝ)) *
          (1 - 1 / (p.m : ℝ)) ^ ((sourceIncomingFinset p b).card - 1)) := by
      calc
        _ = (ENNReal.ofReal (1 / 4 : ℝ) *
            ENNReal.ofReal (BootstrapWeightPotential.probability (b_N p)
              (b.numerators (BootstrapPhysicalInput.sourceFollowerIndex p i.1)) a /
              (p.m : ℝ))) *
            (GeneratedBlockStartLaw.originalCoordinatesLaw p
              {e | GeneratedBlockStartLaw.boundaryAtOriginal p s ids rewards C_star C_h eta e = b} *
             CompleteRowStoppingLaw.futureArrayLaw p
              (GeneratedBlockStartLaw.blockStartIndex p s) C) := by ac_rfl
        _ ≤ ENNReal.ofReal ((BootstrapWeightPotential.probability (b_N p)
              (b.numerators (BootstrapPhysicalInput.sourceFollowerIndex p i.1)) a /
              (p.m : ℝ)) *
              (1 - 1 / (p.m : ℝ)) ^ ((sourceIncomingFinset p b).card - 1)) *
            (GeneratedBlockStartLaw.originalCoordinatesLaw p
              {e | GeneratedBlockStartLaw.boundaryAtOriginal p s ids rewards C_star C_h eta e = b} *
             CompleteRowStoppingLaw.futureArrayLaw p
              (GeneratedBlockStartLaw.blockStartIndex p s) C) :=
          mul_le_mul_left hfactor _
        _ = _ := by ac_rfl
    _ = _ := by ac_rfl

/-- The target avoids the focal arm with probability at least one half
relative to the focal active-held boundary event, without conditioning on a
positive boundary or future-row mass. -/
theorem focalTargetAvoidance_mass_ge_half (p : Parameters)
    (s : Fin (n_boot p)) (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (b : ReferenceInitializationRun.Boundary p) (hcompleted : b.completed = s.val)
    (hnotStopped : b.crossing = none) (i : Incoming p b) (a : Fin p.K)
    (C : Set (FutureRow p s)) (hC : MeasurableSet C) :
    (1 / 2 : ℝ≥0∞) *
      GeneratedBlockStartLaw.originalCoordinatesLaw p
        (generatedProcessedGuardFutureEvent p s ids rewards C_star C_h eta b hcompleted
          hnotStopped (focalActiveHeldGuard p b i a) Set.univ C) ≤
      GeneratedBlockStartLaw.originalCoordinatesLaw p
        (generatedProcessedGuardFutureEvent p s ids rewards C_star C_h eta b hcompleted
          hnotStopped (focalActiveHeldGuard p b i a) {z | z ≠ a} C) := by
  have hmK : 2 ≤ p.K := le_trans p.two_le_m (Nat.le_of_lt p.m_lt_K)
  have hkReal : (2 : ℝ) ≤ (p.K : ℝ) := by exact_mod_cast hmK
  have hkcast : ((p.K - 1 : ℕ) : ℝ) = (p.K : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  have htarget : (1 / 2 : ℝ) ≤ ((p.K - 1 : ℕ) : ℝ) / (p.K : ℝ) := by
    rw [hkcast]
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2)
      (Nat.cast_pos.mpr (K_pos p))]
    nlinarith [hkReal]
  have hprob : 0 < BootstrapWeightPotential.probability (b_N p)
      (b.numerators (BootstrapPhysicalInput.sourceFollowerIndex p i.1)) a :=
    BootstrapBlockConstruction.heldArmProbability_pos p
      (b.numerators (BootstrapPhysicalInput.sourceFollowerIndex p i.1)) a
  have hfp : 0 ≤ BootstrapWeightPotential.probability (b_N p)
      (b.numerators (BootstrapPhysicalInput.sourceFollowerIndex p i.1)) a / (p.m : ℝ) :=
    div_nonneg hprob.le (Nat.cast_nonneg _)
  have hreal := mul_le_mul_of_nonneg_left htarget hfp
  have hfactor : ENNReal.ofReal (1 / 2 : ℝ) *
      ENNReal.ofReal (BootstrapWeightPotential.probability (b_N p)
        (b.numerators (BootstrapPhysicalInput.sourceFollowerIndex p i.1)) a / (p.m : ℝ)) ≤
      ENNReal.ofReal (BootstrapWeightPotential.probability (b_N p)
        (b.numerators (BootstrapPhysicalInput.sourceFollowerIndex p i.1)) a / (p.m : ℝ)) *
        ENNReal.ofReal (((p.K - 1 : ℕ) : ℝ) / (p.K : ℝ)) := by
    rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2),
      ← ENNReal.ofReal_mul hfp]
    exact ENNReal.ofReal_le_ofReal (by simpa only [mul_comm] using hreal)
  rw [focalActiveHeld_joint_future_law p s ids rewards C_star C_h eta b hcompleted
      hnotStopped i a C hC,
    focalTargetAvoidance_joint_future_law p s ids rewards C_star C_h eta b hcompleted
      hnotStopped i a C hC]
  have hhalfENN : (1 / 2 : ℝ≥0∞) = ENNReal.ofReal (1 / 2 : ℝ) := by
    norm_num [ENNReal.ofReal_div_of_pos]
  rw [hhalfENN]
  calc
    _ = (GeneratedBlockStartLaw.originalCoordinatesLaw p
          {e | GeneratedBlockStartLaw.boundaryAtOriginal p s ids rewards C_star C_h eta e = b} *
        CompleteRowStoppingLaw.futureArrayLaw p (GeneratedBlockStartLaw.blockStartIndex p s) C) *
        (ENNReal.ofReal (1 / 2 : ℝ) *
          ENNReal.ofReal (BootstrapWeightPotential.probability (b_N p)
            (b.numerators (BootstrapPhysicalInput.sourceFollowerIndex p i.1)) a / (p.m : ℝ))) := by
      ac_rfl
    _ ≤ (GeneratedBlockStartLaw.originalCoordinatesLaw p
          {e | GeneratedBlockStartLaw.boundaryAtOriginal p s ids rewards C_star C_h eta e = b} *
        CompleteRowStoppingLaw.futureArrayLaw p (GeneratedBlockStartLaw.blockStartIndex p s) C) *
        (ENNReal.ofReal (BootstrapWeightPotential.probability (b_N p)
          (b.numerators (BootstrapPhysicalInput.sourceFollowerIndex p i.1)) a / (p.m : ℝ)) *
         ENNReal.ofReal (((p.K - 1 : ℕ) : ℝ) / (p.K : ℝ))) := by
      calc
        _ = (ENNReal.ofReal (1 / 2 : ℝ) *
            ENNReal.ofReal (BootstrapWeightPotential.probability (b_N p)
              (b.numerators (BootstrapPhysicalInput.sourceFollowerIndex p i.1)) a /
              (p.m : ℝ))) *
            (GeneratedBlockStartLaw.originalCoordinatesLaw p
              {e | GeneratedBlockStartLaw.boundaryAtOriginal p s ids rewards C_star C_h eta e = b} *
             CompleteRowStoppingLaw.futureArrayLaw p
              (GeneratedBlockStartLaw.blockStartIndex p s) C) := by ac_rfl
        _ ≤ (ENNReal.ofReal (BootstrapWeightPotential.probability (b_N p)
              (b.numerators (BootstrapPhysicalInput.sourceFollowerIndex p i.1)) a /
              (p.m : ℝ)) *
              ENNReal.ofReal (((p.K - 1 : ℕ) : ℝ) / (p.K : ℝ))) *
            (GeneratedBlockStartLaw.originalCoordinatesLaw p
              {e | GeneratedBlockStartLaw.boundaryAtOriginal p s ids rewards C_star C_h eta e = b} *
             CompleteRowStoppingLaw.futureArrayLaw p
              (GeneratedBlockStartLaw.blockStartIndex p s) C) :=
          mul_le_mul_left hfactor _
        _ = _ := by ac_rfl
    _ = _ := by ac_rfl

/-- A bounded constant times the indicator of a measurable event integrates
to its event mass. This identity supplies the finite-event integration step
for later block-gain and monitor averages. -/
theorem originalCoordinatesLaw_integral_indicator_const (p : Parameters)
    (A : Set (OriginalCoordinates p)) (hA : MeasurableSet A) (v : ℝ) :
    ∫ e, A.indicator (fun _ : OriginalCoordinates p => v) e
      ∂GeneratedBlockStartLaw.originalCoordinatesLaw p =
      (GeneratedBlockStartLaw.originalCoordinatesLaw p A).toReal * v := by
  rw [MeasureTheory.integral_indicator_const v hA]
  simp only [MeasureTheory.measureReal_def, smul_eq_mul]

/-- The all-inactive event has at least one-quarter of the boundary mass
times any measurable entire-future-row event. -/
theorem allIncomingInactive_mass_ge_quarter (p : Parameters)
    (s : Fin (n_boot p)) (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (b : ReferenceInitializationRun.Boundary p) (hcompleted : b.completed = s.val)
    (hnotStopped : b.crossing = none) (C : Set (FutureRow p s)) (hC : MeasurableSet C) :
    (1 / 4 : ℝ≥0∞) *
      (GeneratedBlockStartLaw.originalCoordinatesLaw p
        {e | GeneratedBlockStartLaw.boundaryAtOriginal p s ids rewards C_star C_h eta e = b} *
       CompleteRowStoppingLaw.futureArrayLaw p (GeneratedBlockStartLaw.blockStartIndex p s) C) ≤
      GeneratedBlockStartLaw.originalCoordinatesLaw p
        (generatedProcessedGuardFutureEvent p s ids rewards C_star C_h eta b hcompleted
          hnotStopped (allIncomingInactiveGuard p b) Set.univ C) := by
  have hquarter := allIncomingInactive_probability_ge_quarter p b
  have hfactor : ENNReal.ofReal (1 / 4 : ℝ) ≤
      ENNReal.ofReal ((1 - 1 / (p.m : ℝ)) ^ (sourceIncomingFinset p b).card) :=
    ENNReal.ofReal_le_ofReal hquarter
  rw [allIncomingInactive_joint_future_law p s ids rewards C_star C_h eta b hcompleted
      hnotStopped C hC]
  have hquarterENN : (1 / 4 : ℝ≥0∞) = ENNReal.ofReal (1 / 4 : ℝ) := by
    norm_num [ENNReal.ofReal_div_of_pos]
  rw [hquarterENN]
  calc
    _ = ENNReal.ofReal (1 / 4 : ℝ) *
        (GeneratedBlockStartLaw.originalCoordinatesLaw p
          {e | GeneratedBlockStartLaw.boundaryAtOriginal p s ids rewards C_star C_h eta e = b} *
          CompleteRowStoppingLaw.futureArrayLaw p (GeneratedBlockStartLaw.blockStartIndex p s) C) := by
      ac_rfl
    _ = (GeneratedBlockStartLaw.originalCoordinatesLaw p
          {e | GeneratedBlockStartLaw.boundaryAtOriginal p s ids rewards C_star C_h eta e = b} *
        CompleteRowStoppingLaw.futureArrayLaw p (GeneratedBlockStartLaw.blockStartIndex p s) C) *
        ENNReal.ofReal (1 / 4 : ℝ) := by ac_rfl
    _ ≤ (GeneratedBlockStartLaw.originalCoordinatesLaw p
          {e | GeneratedBlockStartLaw.boundaryAtOriginal p s ids rewards C_star C_h eta e = b} *
        CompleteRowStoppingLaw.futureArrayLaw p (GeneratedBlockStartLaw.blockStartIndex p s) C) *
        ENNReal.ofReal ((1 - 1 / (p.m : ℝ)) ^ (sourceIncomingFinset p b).card) := by
      calc
        _ = ENNReal.ofReal (1 / 4 : ℝ) *
            (GeneratedBlockStartLaw.originalCoordinatesLaw p
              {e | GeneratedBlockStartLaw.boundaryAtOriginal p s ids rewards C_star C_h eta e = b} *
             CompleteRowStoppingLaw.futureArrayLaw p
              (GeneratedBlockStartLaw.blockStartIndex p s) C) := by ac_rfl
        _ ≤ ENNReal.ofReal ((1 - 1 / (p.m : ℝ)) ^ (sourceIncomingFinset p b).card) *
            (GeneratedBlockStartLaw.originalCoordinatesLaw p
              {e | GeneratedBlockStartLaw.boundaryAtOriginal p s ids rewards C_star C_h eta e = b} *
             CompleteRowStoppingLaw.futureArrayLaw p
              (GeneratedBlockStartLaw.blockStartIndex p s) C) :=
          mul_le_mul_left hfactor _
        _ = _ := by ac_rfl
    _ = _ := by ac_rfl

end Bandits.Support.GeneratedBlockGuardLaw

end
