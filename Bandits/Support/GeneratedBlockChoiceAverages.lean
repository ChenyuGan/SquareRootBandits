/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.GeneratedBlockGuardLaw
public import Bandits.Support.IdentificationGoodEvent
public import Bandits.Support.IdentificationLocalRowBalance
public import Bandits.Support.BootstrapModeService

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Original-coordinate block-choice averages

This module computes the simultaneous isolation, private-ID, target, and
whole-future-row masses at actual generated block boundaries. It also defines
the literal rounded-reward support counts, their analytical support budget,
and the finite identification-ID averages used by the gain and productive
block assemblies.

Sources: `sources/zip4/manuscript/appendix_b_communication.tex:192-207,
376-407,476-506` and `sources/zip4/manuscript/07_public_setup.tex:63-112`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal BigOperators

open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.BootstrapWeightPotential
open Bandits.Support.BootstrapBlockConstruction
open Bandits.Support.BootstrapBlockIsolation
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.PrivateSourceStreams
open Bandits.Support.CompletePublicTable
open Bandits.Support.GeneratedBlockStartLaw
open Bandits.Support.GeneratedBlockDrawLaw
open Bandits.Support.GeneratedBlockGuardLaw
open Bandits.Support.ReferenceInitializationRun
open Bandits.Support.BootstrapPhysicalInput
open Bandits.Support.BootstrapPhysicalBlock
open Bandits.Support.BootstrapModeService
open Bandits.Support.IdentificationLocalRowBalance
open Bandits.Support.IdentificationBlockBalance
open Bandits.Support.IdentificationGoodEvent

namespace Bandits.Support.GeneratedBlockChoiceAverages

abbrev Parameters := GeneratedBlockGuardLaw.Parameters
abbrev OriginalCoordinates := GeneratedBlockGuardLaw.OriginalCoordinates
abbrev Incoming := GeneratedBlockGuardLaw.Incoming
abbrev FutureRow := GeneratedBlockGuardLaw.FutureRow

/-- The actual number of incoming uninformed followers, expressed through the
accepted source-coordinate image of the incoming set. -/
def incomingCount (p : Parameters) (b : ReferenceInitializationRun.Boundary p) : ℕ :=
  (GeneratedBlockGuardLaw.sourceIncomingFinset p b).card

/-- The source image preserves the cardinality of the existing actual
incoming set. -/
theorem incomingCount_eq_actual (p : Parameters)
    (b : ReferenceInitializationRun.Boundary p) :
    incomingCount p b = (ReferenceInitializationRun.uninformed b).card :=
  GeneratedBlockGuardLaw.sourceIncomingFinset_card p b

/-- The literal indicator of positivity of the rounded denominator-`D`
reward. -/
def roundedSupportChi (p : Parameters)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (t : Fin p.T) (a : Fin p.K) : ℝ :=
  if (rewards t a).val > 0 then 1 else 0

/-- On an existing physical input carrying these rewards, the literal rounded
support agrees with the accepted physical `chi`. -/
theorem roundedSupportChi_eq_physicalChi (p : Parameters)
    {s : Fin (n_boot p)} (x : BootstrapPhysicalBlock.Input p s)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (hRewards : x.rewards = rewards) (t : Fin p.T) (a : Fin p.K) :
    roundedSupportChi p rewards t a = BootstrapModeService.chi x t a := by
  have hpos (k : Fin (D p + 1)) :
      0 < RealRewardGridCount.realRewardGridValue (D p) (D_pos p) k ↔ 0 < k.val := by
    rw [RealRewardGridCount.realRewardGridValue]
    have hD : 0 < (D p : ℝ) := by exact_mod_cast D_pos p
    rw [div_pos_iff_of_pos_right hD]
    exact_mod_cast (show (0 : ℕ) < k.val ↔ 0 < k.val by rfl)
  rw [← hRewards]
  simp only [roundedSupportChi, BootstrapModeService.chi]
  by_cases hk : 0 < (x.rewards t a).val
  · have h := (hpos (x.rewards t a)).2 hk
    simp [hk, h]
  · have h : ¬ 0 < RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
        (x.rewards t a) := by
      intro hvalue
      exact hk ((hpos (x.rewards t a)).1 hvalue)
    simp [hk, h]

/-- Number of positive rounded rewards in the actual clipped calendar block. -/
def blockSupportCount (p : Parameters) (s : Fin (n_boot p))
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (a : Fin p.K) : ℝ :=
  ∑ t ∈ BootstrapDimensions.calendarBlock p s, roundedSupportChi p rewards t a

/-- Every literal support count is nonnegative. -/
theorem blockSupportCount_nonneg (p : Parameters) (s : Fin (n_boot p))
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (a : Fin p.K) :
    0 ≤ blockSupportCount p s rewards a := by
  apply Finset.sum_nonneg
  intro t ht
  by_cases h : 0 < (rewards t a).val <;> simp [roundedSupportChi, h]

/-- Number of supported block times whose original ID bit is zero. -/
def supportedIDZeroCount (p : Parameters) (s : Fin (n_boot p))
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (a : Fin p.K) (u : Fin (A_id p)) : ℝ :=
  ∑ t ∈ BootstrapDimensions.calendarBlock p s,
    roundedSupportChi p rewards t a * (if ids u t = false then 1 else 0)

/-- The literal support on the calendar block, packaged for the existing
local-row-balance predicate. -/
def literalBlockSupport (p : Parameters) (s : Fin (n_boot p))
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (a : Fin p.K) : BlockSupport p s :=
  ⟨(BootstrapDimensions.calendarBlock p s).filter
      (fun t => (rewards t a).val > 0), by
    intro t ht
    exact (Finset.mem_filter.mp ht).1⟩

/-- The actual literal good-ID set for this rounded-reward block support. -/
noncomputable def goodIDs (p : Parameters) (s : Fin (n_boot p))
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (a : Fin p.K) :
    Finset (Fin (A_id p)) :=
  by classical
    exact Finset.univ.filter fun u =>
      localBalanceRowPredicate p s (literalBlockSupport p s rewards a) (ids u)

/-- The good-ID set is exactly the accepted local-row event on the literal
rounded-reward support. -/
theorem mem_goodIDs_iff (p : Parameters) (s : Fin (n_boot p))
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (a : Fin p.K)
    (u : Fin (A_id p)) :
    u ∈ goodIDs p s ids rewards a ↔
      ids ∈ localBalanceRowEvent p s (literalBlockSupport p s rewards a) u := by
  simp [goodIDs, localBalanceRowEvent]

/-- The accepted property III count is the cardinality of this exact
good-ID set. -/
theorem goodIDs_card_eq_propertyIII_count (p : Parameters)
    (s : Fin (n_boot p)) (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (a : Fin p.K) :
    (goodIDs p s ids rewards a).card =
      IdentificationBlockBalance.propertyIIIGoodRowCount p ids s
        (literalBlockSupport p s rewards a) := by
  classical
  rfl

/-- On an accepted simultaneous good-ID array, the literal block support has
at least three quarters good IDs. -/
theorem goodIDs_card_lower (p : Parameters) (s : Fin (n_boot p))
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (a : Fin p.K)
    (hgood : ids ∈ IdentificationGoodEvent.identificationGoodEvent p) :
    (3 * (A_id p : ℝ)) / 4 ≤ ((goodIDs p s ids rewards a).card : ℝ) := by
  rw [goodIDs_card_eq_propertyIII_count]
  exact IdentificationGoodEvent.identificationGoodEvent_block_support_row_count
    p ids hgood s (literalBlockSupport p s rewards a)

/-- The zero-bit supported-count sum is the sum over calendar times of the
support indicator times the number of zero entries in that ID column. -/
theorem sum_supportedIDZeroCount_eq_time_sum (p : Parameters)
    (s : Fin (n_boot p)) (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (a : Fin p.K) :
    (∑ u : Fin (A_id p), supportedIDZeroCount p s ids rewards a u) =
      ∑ t ∈ BootstrapDimensions.calendarBlock p s,
        roundedSupportChi p rewards t a *
          ((Finset.univ.filter fun u : Fin (A_id p) => ids u t = false).card : ℝ) := by
  classical
  simp only [supportedIDZeroCount]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  rw [← Finset.mul_sum]
  congr 1
  simp [Finset.sum_boole]

/-- The column-balance property in the simultaneous good event gives an
average of at least one third zero ID bits at every calendar time. -/
theorem sum_supportedIDZeroCount_lower (p : Parameters)
    (s : Fin (n_boot p)) (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (a : Fin p.K)
    (hgood : ids ∈ IdentificationGoodEvent.identificationGoodEvent p) :
    (A_id p : ℝ) * blockSupportCount p s rewards a / 3 ≤
      ∑ u : Fin (A_id p), supportedIDZeroCount p s ids rewards a u := by
  rw [sum_supportedIDZeroCount_eq_time_sum, blockSupportCount]
  have hcolumns :=
    IdentificationGoodEvent.mem_identificationGoodEvent_iff_components p ids |>.mp hgood
  have hterm (t : Fin p.T) (ht : t ∈ BootstrapDimensions.calendarBlock p s) :
      roundedSupportChi p rewards t a * ((A_id p : ℝ) / 3) ≤
        roundedSupportChi p rewards t a *
          ((Finset.univ.filter fun u : Fin (A_id p) => ids u t = false).card : ℝ) := by
    have hcount := hcolumns.1 t false
    have hchi0 : 0 ≤ roundedSupportChi p rewards t a := by
      by_cases h : 0 < (rewards t a).val <;> simp [roundedSupportChi, h]
    exact mul_le_mul_of_nonneg_left hcount hchi0
  calc
    _ = ((A_id p : ℝ) / 3) *
        (∑ t ∈ BootstrapDimensions.calendarBlock p s,
          roundedSupportChi p rewards t a) := by
          ring
    _ = ∑ t ∈ BootstrapDimensions.calendarBlock p s,
        roundedSupportChi p rewards t a * ((A_id p : ℝ) / 3) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro t ht
          ring
    _ ≤ ∑ t ∈ BootstrapDimensions.calendarBlock p s,
        roundedSupportChi p rewards t a *
          ((Finset.univ.filter fun u : Fin (A_id p) => ids u t = false).card : ℝ) := by
          apply Finset.sum_le_sum
          intro t ht
          exact hterm t ht

/-- Actual active-held boundary event, with an arbitrary event retained on the
entire future row. -/
def activeHeldFutureEvent (p : Parameters)
    (s : Fin (n_boot p)) (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (b : ReferenceInitializationRun.Boundary p) (hcompleted : b.completed = s.val)
    (hnotStopped : b.crossing = none) (i : Incoming p b) (a : Fin p.K)
    (C : Set (FutureRow p s)) : Set (OriginalCoordinates p) :=
  GeneratedBlockGuardLaw.generatedProcessedGuardFutureEvent p s ids rewards C_star C_h eta
    b hcompleted hnotStopped (GeneratedBlockGuardLaw.focalActiveHeldGuard p b i a)
    Set.univ C

/-- The active-held boundary and whole-future mass has the accepted exact
original-coordinate law. -/
theorem activeHeldFutureEvent_mass (p : Parameters)
    (s : Fin (n_boot p)) (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (b : ReferenceInitializationRun.Boundary p) (hcompleted : b.completed = s.val)
    (hnotStopped : b.crossing = none) (i : Incoming p b) (a : Fin p.K)
    (C : Set (FutureRow p s)) (hC : MeasurableSet C) :
    GeneratedBlockStartLaw.originalCoordinatesLaw p
      (activeHeldFutureEvent p s ids rewards C_star C_h eta b hcompleted hnotStopped i a C) =
      GeneratedBlockStartLaw.originalCoordinatesLaw p
        {e | GeneratedBlockStartLaw.boundaryAtOriginal p s ids rewards C_star C_h eta e = b} *
        ENNReal.ofReal (BootstrapWeightPotential.probability (b_N p)
          (b.numerators (BootstrapPhysicalInput.sourceFollowerIndex p i.1)) a /
            (p.m : ℝ)) *
        CompleteRowStoppingLaw.futureArrayLaw p
          (GeneratedBlockStartLaw.blockStartIndex p s) C := by
  exact GeneratedBlockGuardLaw.focalActiveHeld_joint_future_law p s ids rewards C_star C_h
    eta b hcompleted hnotStopped i a C hC

/-- Exact raw guard for one private ID, simultaneous isolation of every other
actual incoming follower, target avoidance, and the entire future event. -/
def isolatedPrivateIDTargetFutureEvent (p : Parameters)
    (s : Fin (n_boot p)) (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (b : ReferenceInitializationRun.Boundary p) (hcompleted : b.completed = s.val)
    (hnotStopped : b.crossing = none) (i : Incoming p b) (a : Fin p.K)
    (u : Fin (A_id p)) (C : Set (FutureRow p s)) : Set (OriginalCoordinates p) :=
  GeneratedBlockGuardLaw.generatedProcessedGuardFutureEvent p s ids rewards C_star C_h eta
    b hcompleted hnotStopped
    (GeneratedBlockGuardLaw.focalIsolationPrivateIdGuard p b i a u)
    {z | z ≠ a} C

private theorem sourceRestriction_focalIsolation_iff (p : Parameters)
    (b : ReferenceInitializationRun.Boundary p) (i : Incoming p b)
    (a : Fin p.K) (c : GeneratedBlockGuardLaw.Profile p) :
    GeneratedBlockGuardLaw.sourceRestrictedProfile p b c ∈
        GeneratedBlockGuardLaw.focalIsolationGuard p b i a ↔
      BootstrapBlockIsolation.isolatedBootstrapEvent
        (GeneratedBlockGuardLaw.sourceIncomingFinset p b)
        (BootstrapPhysicalInput.sourceFollowerIndex p i.1) a c := by
  constructor
  · intro h
    refine ⟨⟨h.1, h.2.1⟩, ?_⟩
    intro k hk
    obtain ⟨hkNe, hkU⟩ := Finset.mem_erase.mp hk
    obtain ⟨j, hj, hindex⟩ :=
      (GeneratedBlockGuardLaw.mem_sourceIncomingFinset_iff p b k).mp hkU
    have hji : (⟨j, hj⟩ : Incoming p b) ≠ i := by
      intro hEq
      have hEqIndex : k = BootstrapPhysicalInput.sourceFollowerIndex p i.1 := by
        have hjiVal : j = i.1 := congrArg Subtype.val hEq
        exact hindex.symm.trans
          (congrArg (BootstrapPhysicalInput.sourceFollowerIndex p) hjiVal)
      exact hkNe hEqIndex
    simpa [GeneratedBlockGuardLaw.sourceRestrictedProfile, hindex] using
      h.2.2 ⟨j, hj⟩ hji
  · rintro ⟨hactive, hinactive⟩
    refine ⟨?_, ?_, ?_⟩
    · simpa [GeneratedBlockGuardLaw.sourceRestrictedProfile,
        GeneratedBlockGuardLaw.focalIsolationGuard,
        BootstrapBlockIsolation.distinguishedEvent] using hactive.1
    · simpa [GeneratedBlockGuardLaw.sourceRestrictedProfile,
        GeneratedBlockGuardLaw.focalIsolationGuard,
        BootstrapBlockIsolation.distinguishedEvent] using hactive.2
    · intro j hji
      have hindexNe : BootstrapPhysicalInput.sourceFollowerIndex p j.1 ≠
          BootstrapPhysicalInput.sourceFollowerIndex p i.1 := by
        intro hEq
        exact hji (Subtype.ext
          (GeneratedBlockGuardLaw.sourceFollowerIndex_injective p hEq))
      have hmember :=
        GeneratedBlockGuardLaw.sourceFollowerIndex_mem_sourceIncomingFinset p b j
      have hstatus := hinactive
        (BootstrapPhysicalInput.sourceFollowerIndex p j.1)
        (Finset.mem_erase.mpr ⟨hindexNe, hmember⟩)
      simpa [GeneratedBlockGuardLaw.sourceRestrictedProfile] using hstatus

private theorem privateIDProfileProbability (p : Parameters)
    (b : ReferenceInitializationRun.Boundary p) (i : Incoming p b)
    (a : Fin p.K) (u : Fin (A_id p)) :
    BootstrapBlockIsolation.privateBlockProfileEventProbability p b.numerators
      b.weight_ge_one
      (fun c => GeneratedBlockGuardLaw.sourceRestrictedProfile p b c ∈
        GeneratedBlockGuardLaw.focalIsolationPrivateIdGuard p b i a u) =
      ((BootstrapWeightPotential.probability (b_N p)
        (b.numerators (BootstrapPhysicalInput.sourceFollowerIndex p i.1)) a /
        (p.m : ℝ)) * (1 / (A_id p : ℝ))) *
        (1 - 1 / (p.m : ℝ)) ^ (incomingCount p b - 1) := by
  have hevent : (fun c : GeneratedBlockGuardLaw.Profile p =>
      GeneratedBlockGuardLaw.sourceRestrictedProfile p b c ∈
        GeneratedBlockGuardLaw.focalIsolationPrivateIdGuard p b i a u) =
      (fun c => BootstrapBlockIsolation.isolatedBootstrapEvent
        (GeneratedBlockGuardLaw.sourceIncomingFinset p b)
        (BootstrapPhysicalInput.sourceFollowerIndex p i.1) a c ∧
        (c (BootstrapPhysicalInput.sourceFollowerIndex p i.1)).2.2 = u) := by
    funext c
    apply propext
    change (GeneratedBlockGuardLaw.sourceRestrictedProfile p b c ∈
      GeneratedBlockGuardLaw.focalIsolationGuard p b i a ∧
      (GeneratedBlockGuardLaw.sourceRestrictedProfile p b c i).2.2 = u) ↔ _
    rw [sourceRestriction_focalIsolation_iff]
    rfl
  rw [hevent]
  rw [BootstrapBlockIsolation.isolatedBootstrapEvent_privateId_probability p b.numerators
    b.weight_ge_one (GeneratedBlockGuardLaw.sourceIncomingFinset p b)
    (BootstrapPhysicalInput.sourceFollowerIndex p i.1)
    (GeneratedBlockGuardLaw.sourceFollowerIndex_mem_sourceIncomingFinset p b i) a u]
  simp [BootstrapBlockConstruction.privateIdProbability, incomingCount]

private theorem targetAvoidanceProbability (p : Parameters) (a : Fin p.K) :
    (∑ _z ∈ GeneratedBlockGuardLaw.targetGuardAtoms p {z | z ≠ a},
      1 / (p.K : ℝ)) = ((p.K - 1 : ℕ) : ℝ) / (p.K : ℝ) := by
  classical
  have hatoms : GeneratedBlockGuardLaw.targetGuardAtoms p {z | z ≠ a} =
      Finset.univ.erase a := by
    ext z
    simp [GeneratedBlockGuardLaw.targetGuardAtoms]
  rw [hatoms]
  calc
    _ = ((Finset.univ.erase a).card : ℝ) * (1 / (p.K : ℝ)) := by
      simp [Finset.sum_const, nsmul_eq_mul]
    _ = ((p.K - 1 : ℕ) : ℝ) / (p.K : ℝ) := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_fin]
      ring

/-- Exact unnormalized mass of each original-coordinate ID event. It is
derived from the generic generated joint law, so the arbitrary measurable
whole-future event remains present without an independence or positive-mass
premise.
Sources: `appendix_b_communication.tex:376-403,485-506` and
`07_public_setup.tex:63-112`. -/
theorem isolatedPrivateIDTargetFutureEvent_mass (p : Parameters)
    (s : Fin (n_boot p)) (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (b : ReferenceInitializationRun.Boundary p) (hcompleted : b.completed = s.val)
    (hnotStopped : b.crossing = none) (i : Incoming p b) (a : Fin p.K)
    (u : Fin (A_id p)) (C : Set (FutureRow p s)) (hC : MeasurableSet C) :
    GeneratedBlockStartLaw.originalCoordinatesLaw p
      (isolatedPrivateIDTargetFutureEvent p s ids rewards C_star C_h eta b hcompleted
        hnotStopped i a u C) =
      GeneratedBlockStartLaw.originalCoordinatesLaw p
        {e | GeneratedBlockStartLaw.boundaryAtOriginal p s ids rewards C_star C_h eta e = b} *
      ENNReal.ofReal
        (((BootstrapWeightPotential.probability (b_N p)
          (b.numerators (BootstrapPhysicalInput.sourceFollowerIndex p i.1)) a /
          (p.m : ℝ)) * (1 / (A_id p : ℝ))) *
          (1 - 1 / (p.m : ℝ)) ^ (incomingCount p b - 1)) *
      ENNReal.ofReal (((p.K - 1 : ℕ) : ℝ) / (p.K : ℝ)) *
      CompleteRowStoppingLaw.futureArrayLaw p
        (GeneratedBlockStartLaw.blockStartIndex p s) C := by
  rw [isolatedPrivateIDTargetFutureEvent,
    GeneratedBlockGuardLaw.generatedProcessedGuardFutureEvent_joint_law p s ids rewards
      C_star C_h eta b hcompleted hnotStopped
      (GeneratedBlockGuardLaw.focalIsolationPrivateIdGuard p b i a u)
      {z | z ≠ a} C hC,
    privateIDProfileProbability, targetAvoidanceProbability]

/-- Exact raw guard for an isolated private ID whose original target equals
the focal held arm, retaining the entire future-row event. -/
def goodIDChoiceCell (p : Parameters)
    (s : Fin (n_boot p)) (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (b : ReferenceInitializationRun.Boundary p) (hcompleted : b.completed = s.val)
    (hnotStopped : b.crossing = none) (i : Incoming p b) (a : Fin p.K)
    (u : Fin (A_id p)) (C : Set (FutureRow p s)) : Set (OriginalCoordinates p) :=
  GeneratedBlockGuardLaw.generatedProcessedGuardFutureEvent p s ids rewards C_star C_h eta
    b hcompleted hnotStopped
    (GeneratedBlockGuardLaw.focalIsolationPrivateIdGuard p b i a u)
    {z | z = a} C

/-- The exact literal union of the isolation/target cells over IDs satisfying
the accepted local-row predicate on the rounded-reward support. -/
def goodIDChoiceFutureEvent (p : Parameters)
    (s : Fin (n_boot p)) (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (b : ReferenceInitializationRun.Boundary p) (hcompleted : b.completed = s.val)
    (hnotStopped : b.crossing = none) (i : Incoming p b) (a : Fin p.K)
    (C : Set (FutureRow p s)) : Set (OriginalCoordinates p) :=
  ⋃ u ∈ goodIDs p s ids rewards a,
    goodIDChoiceCell p s ids rewards C_star C_h eta b hcompleted hnotStopped i a u C

/-- Membership in the finite-choice event exposes the exact good-ID and
original-coordinate guard conditions for downstream clock/acceptance work. -/
theorem mem_goodIDChoiceFutureEvent_iff (p : Parameters)
    (s : Fin (n_boot p)) (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (b : ReferenceInitializationRun.Boundary p) (hcompleted : b.completed = s.val)
    (hnotStopped : b.crossing = none) (i : Incoming p b) (a : Fin p.K)
    (C : Set (FutureRow p s)) (e : OriginalCoordinates p) :
    e ∈ goodIDChoiceFutureEvent p s ids rewards C_star C_h eta b hcompleted
      hnotStopped i a C ↔
    ∃ u, u ∈ goodIDs p s ids rewards a ∧
      e ∈ goodIDChoiceCell p s ids rewards C_star C_h eta b hcompleted
        hnotStopped i a u C := by
  simp [goodIDChoiceFutureEvent]

/-- The exact finite-choice union ranges over IDs satisfying the existing
local row-balance event on the literal support. -/
theorem mem_goodIDChoiceFutureEvent_iff_literalBalance (p : Parameters)
    (s : Fin (n_boot p)) (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (b : ReferenceInitializationRun.Boundary p) (hcompleted : b.completed = s.val)
    (hnotStopped : b.crossing = none) (i : Incoming p b) (a : Fin p.K)
    (C : Set (FutureRow p s)) (e : OriginalCoordinates p) :
    e ∈ goodIDChoiceFutureEvent p s ids rewards C_star C_h eta b hcompleted
      hnotStopped i a C ↔
    ∃ u, ids ∈ localBalanceRowEvent p s (literalBlockSupport p s rewards a) u ∧
      e ∈ goodIDChoiceCell p s ids rewards C_star C_h eta b hcompleted
        hnotStopped i a u C := by
  rw [mem_goodIDChoiceFutureEvent_iff]
  simp only [mem_goodIDs_iff]

/-- Measurability of each exact target-arm choice cell. -/
theorem measurableSet_goodIDChoiceCell (p : Parameters)
    (s : Fin (n_boot p)) (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (b : ReferenceInitializationRun.Boundary p) (hcompleted : b.completed = s.val)
    (hnotStopped : b.crossing = none) (i : Incoming p b) (a : Fin p.K)
    (u : Fin (A_id p)) (C : Set (FutureRow p s)) (hC : MeasurableSet C) :
    MeasurableSet (goodIDChoiceCell p s ids rewards C_star C_h eta b hcompleted
      hnotStopped i a u C) :=
  GeneratedBlockGuardLaw.measurableSet_generatedProcessedGuardFutureEvent p s ids
    rewards C_star C_h eta b hcompleted hnotStopped
    (GeneratedBlockGuardLaw.focalIsolationPrivateIdGuard p b i a u)
    {z | z = a} C hC

/-- Measurability of the good-ID union. -/
theorem measurableSet_goodIDChoiceFutureEvent (p : Parameters)
    (s : Fin (n_boot p)) (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (b : ReferenceInitializationRun.Boundary p) (hcompleted : b.completed = s.val)
    (hnotStopped : b.crossing = none) (i : Incoming p b) (a : Fin p.K)
    (C : Set (FutureRow p s)) (hC : MeasurableSet C) :
    MeasurableSet (goodIDChoiceFutureEvent p s ids rewards C_star C_h eta b hcompleted
      hnotStopped i a C) := by
  rw [goodIDChoiceFutureEvent]
  exact Finset.measurableSet_biUnion (goodIDs p s ids rewards a) fun u hu =>
    measurableSet_goodIDChoiceCell p s ids rewards C_star C_h eta b hcompleted
      hnotStopped i a u C hC

/-- Distinct original private IDs give disjoint target-arm choice cells. -/
theorem goodIDChoiceCell_disjoint (p : Parameters)
    (s : Fin (n_boot p)) (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (b : ReferenceInitializationRun.Boundary p) (hcompleted : b.completed = s.val)
    (hnotStopped : b.crossing = none) (i : Incoming p b) (a : Fin p.K)
    (u v : Fin (A_id p)) (huv : u ≠ v) (C : Set (FutureRow p s)) :
    Disjoint (goodIDChoiceCell p s ids rewards C_star C_h eta b hcompleted
      hnotStopped i a u C)
      (goodIDChoiceCell p s ids rewards C_star C_h eta b hcompleted
        hnotStopped i a v C) := by
  apply Set.disjoint_left.2
  intro e heu hev
  have hu := (by
    simpa [goodIDChoiceCell] using heu : e ∈
      GeneratedBlockGuardLaw.generatedProcessedGuardFutureEvent p s ids rewards C_star C_h
        eta b hcompleted hnotStopped
        (GeneratedBlockGuardLaw.focalIsolationPrivateIdGuard p b i a u) {z | z = a} C)
  have hv := (by
    simpa [goodIDChoiceCell] using hev : e ∈
      GeneratedBlockGuardLaw.generatedProcessedGuardFutureEvent p s ids rewards C_star C_h
        eta b hcompleted hnotStopped
        (GeneratedBlockGuardLaw.focalIsolationPrivateIdGuard p b i a v) {z | z = a} C)
  exact huv (hu.2.1.2.symm.trans hv.2.1.2)

private theorem targetArmProbability (p : Parameters) (a : Fin p.K) :
    (∑ _z ∈ GeneratedBlockGuardLaw.targetGuardAtoms p {z | z = a},
      1 / (p.K : ℝ)) = 1 / (p.K : ℝ) := by
  classical
  have hatoms : GeneratedBlockGuardLaw.targetGuardAtoms p {z | z = a} = {a} := by
    ext z
    simp [GeneratedBlockGuardLaw.targetGuardAtoms]
  rw [hatoms]
  simp

/-- Exact unnormalized mass for one target-arm good-ID cell, with the
simultaneous isolation and full future-row event retained. -/
theorem goodIDChoiceCell_mass (p : Parameters)
    (s : Fin (n_boot p)) (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (b : ReferenceInitializationRun.Boundary p) (hcompleted : b.completed = s.val)
    (hnotStopped : b.crossing = none) (i : Incoming p b) (a : Fin p.K)
    (u : Fin (A_id p)) (C : Set (FutureRow p s)) (hC : MeasurableSet C) :
    GeneratedBlockStartLaw.originalCoordinatesLaw p
      (goodIDChoiceCell p s ids rewards C_star C_h eta b hcompleted hnotStopped i a u C) =
      GeneratedBlockStartLaw.originalCoordinatesLaw p
        {e | GeneratedBlockStartLaw.boundaryAtOriginal p s ids rewards C_star C_h eta e = b} *
      ENNReal.ofReal
        (((BootstrapWeightPotential.probability (b_N p)
          (b.numerators (BootstrapPhysicalInput.sourceFollowerIndex p i.1)) a /
          (p.m : ℝ)) * (1 / (A_id p : ℝ))) *
          (1 - 1 / (p.m : ℝ)) ^ (incomingCount p b - 1)) *
      ENNReal.ofReal (1 / (p.K : ℝ)) *
      CompleteRowStoppingLaw.futureArrayLaw p
        (GeneratedBlockStartLaw.blockStartIndex p s) C := by
  rw [goodIDChoiceCell,
    GeneratedBlockGuardLaw.generatedProcessedGuardFutureEvent_joint_law p s ids rewards
      C_star C_h eta b hcompleted hnotStopped
      (GeneratedBlockGuardLaw.focalIsolationPrivateIdGuard p b i a u)
      {z | z = a} C hC,
    privateIDProfileProbability, targetArmProbability]

/-- Exact mass of one target-arm choice cell factored against the actual
active-held/future event. This factorization does not cancel or divide by that
base mass and remains valid on its zero-mass cells. -/
private theorem goodIDChoiceCell_mass_factorized (p : Parameters)
    (s : Fin (n_boot p)) (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (b : ReferenceInitializationRun.Boundary p) (hcompleted : b.completed = s.val)
    (hnotStopped : b.crossing = none) (i : Incoming p b) (a : Fin p.K)
    (u : Fin (A_id p)) (C : Set (FutureRow p s)) (hC : MeasurableSet C) :
    GeneratedBlockStartLaw.originalCoordinatesLaw p
      (goodIDChoiceCell p s ids rewards C_star C_h eta b hcompleted hnotStopped i a u C) =
      GeneratedBlockStartLaw.originalCoordinatesLaw p
        (activeHeldFutureEvent p s ids rewards C_star C_h eta b hcompleted
          hnotStopped i a C) *
        ENNReal.ofReal ((1 - 1 / (p.m : ℝ)) ^ (incomingCount p b - 1)) *
        ENNReal.ofReal (1 / (p.K : ℝ)) * ENNReal.ofReal (1 / (A_id p : ℝ)) := by
  let pHeld := BootstrapWeightPotential.probability (b_N p)
    (b.numerators (BootstrapPhysicalInput.sourceFollowerIndex p i.1)) a /
      (p.m : ℝ)
  let idMass := 1 / (A_id p : ℝ)
  let isolate := (1 - 1 / (p.m : ℝ)) ^ (incomingCount p b - 1)
  have hpHeld : 0 ≤ pHeld := by
    exact div_nonneg
      (BootstrapBlockConstruction.heldArmProbability_pos p
        (b.numerators (BootstrapPhysicalInput.sourceFollowerIndex p i.1)) a).le
      (Nat.cast_nonneg _)
  have hidMass : 0 ≤ idMass := one_div_nonneg.mpr (Nat.cast_nonneg _)
  have hisolate : 0 ≤ isolate := by
    exact pow_nonneg
      (BootstrapBlockConstruction.activityProbability_nonneg p false)
      (incomingCount p b - 1)
  have htarget : 0 ≤ (1 / (p.K : ℝ)) := by positivity
  have hprofile : 0 ≤ pHeld * idMass := mul_nonneg hpHeld hidMass
  have hprofileFactor :
      ENNReal.ofReal ((pHeld * idMass) * isolate) =
        ENNReal.ofReal pHeld * ENNReal.ofReal idMass * ENNReal.ofReal isolate := by
    calc
      ENNReal.ofReal ((pHeld * idMass) * isolate) =
          ENNReal.ofReal (pHeld * idMass) * ENNReal.ofReal isolate :=
        ENNReal.ofReal_mul hprofile
      _ = ENNReal.ofReal pHeld * ENNReal.ofReal idMass * ENNReal.ofReal isolate := by
        rw [ENNReal.ofReal_mul hpHeld]
  rw [goodIDChoiceCell_mass p s ids rewards C_star C_h eta b hcompleted
    hnotStopped i a u C hC,
    activeHeldFutureEvent_mass p s ids rewards C_star C_h eta b hcompleted
      hnotStopped i a C hC]
  have hprofileFactor' := hprofileFactor
  dsimp [pHeld, idMass, isolate] at hprofileFactor'
  calc
    _ = (GeneratedBlockStartLaw.originalCoordinatesLaw p
        {e | GeneratedBlockStartLaw.boundaryAtOriginal p s ids rewards C_star C_h eta e = b} *
        (ENNReal.ofReal pHeld * ENNReal.ofReal idMass * ENNReal.ofReal isolate) *
        ENNReal.ofReal (1 / (p.K : ℝ)) *
        CompleteRowStoppingLaw.futureArrayLaw p
          (GeneratedBlockStartLaw.blockStartIndex p s) C) := by
      rw [hprofileFactor']
    _ = _ := by
      simp only [pHeld, idMass, isolate]
      ac_rfl

/-- Exact mass of the finite union over precisely the literal local-balance
good IDs. It is factored against the existing active-held boundary and future
mass; every event uses the original coordinates and the same future `C`. -/
theorem goodIDChoiceFutureEvent_mass (p : Parameters)
    (s : Fin (n_boot p)) (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (b : ReferenceInitializationRun.Boundary p) (hcompleted : b.completed = s.val)
    (hnotStopped : b.crossing = none) (i : Incoming p b) (a : Fin p.K)
    (C : Set (FutureRow p s)) (hC : MeasurableSet C) :
    GeneratedBlockStartLaw.originalCoordinatesLaw p
      (goodIDChoiceFutureEvent p s ids rewards C_star C_h eta b hcompleted
        hnotStopped i a C) =
      GeneratedBlockStartLaw.originalCoordinatesLaw p
        (activeHeldFutureEvent p s ids rewards C_star C_h eta b hcompleted
          hnotStopped i a C) *
      ENNReal.ofReal ((1 - 1 / (p.m : ℝ)) ^ (incomingCount p b - 1)) *
      ENNReal.ofReal (1 / (p.K : ℝ)) *
      ENNReal.ofReal (((goodIDs p s ids rewards a).card : ℝ) / (A_id p : ℝ)) := by
  classical
  let U := goodIDs p s ids rewards a
  let μ := GeneratedBlockStartLaw.originalCoordinatesLaw p
  let isolate := (1 - 1 / (p.m : ℝ)) ^ (incomingCount p b - 1)
  let idArm := 1 / (p.K : ℝ)
  let idMass := 1 / (A_id p : ℝ)
  let active := activeHeldFutureEvent p s ids rewards C_star C_h eta b hcompleted
    hnotStopped i a C
  let choice := fun u => goodIDChoiceCell p s ids rewards C_star C_h eta b
    hcompleted hnotStopped i a u C
  have hdisj : Set.PairwiseDisjoint (↑U) choice := by
    intro u hu v hv huv
    exact goodIDChoiceCell_disjoint p s ids rewards C_star C_h eta b hcompleted
      hnotStopped i a u v huv C
  have hmeas : ∀ u ∈ U, MeasurableSet (choice u) := by
    intro u hu
    exact measurableSet_goodIDChoiceCell p s ids rewards C_star C_h eta b hcompleted
      hnotStopped i a u C hC
  rw [goodIDChoiceFutureEvent, measure_biUnion_finset hdisj hmeas]
  calc
    (∑ u ∈ U, μ (choice u)) =
        ∑ u ∈ U, μ active * ENNReal.ofReal isolate *
          ENNReal.ofReal idArm * ENNReal.ofReal idMass := by
      apply Finset.sum_congr rfl
      intro u hu
      exact goodIDChoiceCell_mass_factorized p s ids rewards C_star C_h eta b
        hcompleted hnotStopped i a u C hC
    _ = μ active * ENNReal.ofReal isolate * ENNReal.ofReal idArm *
        ((U.card : ℝ≥0∞) * ENNReal.ofReal idMass) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ac_rfl
    _ = μ active * ENNReal.ofReal isolate * ENNReal.ofReal idArm *
        ENNReal.ofReal ((U.card : ℝ) / (A_id p : ℝ)) := by
      have hA : 0 < (A_id p : ℝ) :=
        Nat.cast_pos.mpr (BootstrapDimensions.A_id_pos p)
      have hcast :
          (U.card : ℝ≥0∞) * ENNReal.ofReal idMass =
            ENNReal.ofReal ((U.card : ℝ) / (A_id p : ℝ)) := by
        rw [← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg U.card)]
        congr 1
        dsimp [idMass]
        field_simp
      rw [hcast]

/-- The good-ID union has the requested structural lower mass under the
accepted simultaneous identification event. This is an isolation/target
choice mass statement only, not a learning or clock-acceptance probability. -/
theorem goodIDChoiceFutureEvent_mass_ge_three_sixteenths_over_K
    (p : Parameters) (s : Fin (n_boot p)) (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (b : ReferenceInitializationRun.Boundary p) (hcompleted : b.completed = s.val)
    (hnotStopped : b.crossing = none) (i : Incoming p b) (a : Fin p.K)
    (C : Set (FutureRow p s)) (hC : MeasurableSet C)
    (hgood : ids ∈ IdentificationGoodEvent.identificationGoodEvent p) :
    ENNReal.ofReal (3 / (16 * (p.K : ℝ))) *
        GeneratedBlockStartLaw.originalCoordinatesLaw p
          (activeHeldFutureEvent p s ids rewards C_star C_h eta b hcompleted
            hnotStopped i a C) ≤
      GeneratedBlockStartLaw.originalCoordinatesLaw p
        (goodIDChoiceFutureEvent p s ids rewards C_star C_h eta b hcompleted
          hnotStopped i a C) := by
  let isolate := (1 - 1 / (p.m : ℝ)) ^ (incomingCount p b - 1)
  let armMass := 1 / (p.K : ℝ)
  let idFraction := ((goodIDs p s ids rewards a).card : ℝ) / (A_id p : ℝ)
  have hqnonneg : 0 ≤ 1 - 1 / (p.m : ℝ) :=
    BootstrapBlockConstruction.activityProbability_nonneg p false
  have hqle : 1 - 1 / (p.m : ℝ) ≤ 1 := by
    have hmpos : 0 < (p.m : ℝ) := Nat.cast_pos.mpr (ConstructorDimensions.m_pos p)
    have hinv : 0 ≤ 1 / (p.m : ℝ) := by positivity
    linarith
  have hcount := GeneratedBlockGuardLaw.sourceIncomingFinset_other_count_le p b i
  have hisolate : (1 / 4 : ℝ) ≤ isolate := by
    calc
      (1 / 4 : ℝ) ≤ (1 - 1 / (p.m : ℝ)) ^ (p.m - 2) :=
        BootstrapBlockIsolation.inactivity_power_lower_bound p
      _ ≤ isolate := by
        dsimp [isolate, incomingCount]
        exact pow_le_pow_of_le_one hqnonneg hqle (by simpa using hcount)
  have hratio : (3 / 4 : ℝ) ≤ idFraction := by
    have hcard := goodIDs_card_lower p s ids rewards a hgood
    have hA : 0 < (A_id p : ℝ) :=
      Nat.cast_pos.mpr (BootstrapDimensions.A_id_pos p)
    dsimp [idFraction]
    rw [le_div_iff₀ hA]
    nlinarith [hcard]
  have hfactor : 3 / (16 * (p.K : ℝ)) ≤ isolate * armMass * idFraction := by
    have hmid : (1 / 4 : ℝ) * armMass * (3 / 4 : ℝ) ≤
        isolate * armMass * idFraction := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_right hisolate (by positivity)) hratio
        (by positivity) (by positivity)
    calc
      3 / (16 * (p.K : ℝ)) = (1 / 4 : ℝ) * armMass * (3 / 4 : ℝ) := by
        dsimp [armMass]
        field_simp
        ring
      _ ≤ isolate * armMass * idFraction := hmid
  have hcoeff : ENNReal.ofReal (3 / (16 * (p.K : ℝ))) ≤
      ENNReal.ofReal isolate * ENNReal.ofReal armMass * ENNReal.ofReal idFraction := by
    have hcast : ENNReal.ofReal isolate * ENNReal.ofReal armMass *
        ENNReal.ofReal idFraction = ENNReal.ofReal (isolate * armMass * idFraction) := by
      rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ isolate),
        ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ isolate * armMass)]
    rw [hcast]
    exact ENNReal.ofReal_le_ofReal hfactor
  rw [goodIDChoiceFutureEvent_mass p s ids rewards C_star C_h eta b hcompleted
    hnotStopped i a C hC]
  calc
    _ = ENNReal.ofReal (3 / (16 * (p.K : ℝ))) *
        GeneratedBlockStartLaw.originalCoordinatesLaw p
          (activeHeldFutureEvent p s ids rewards C_star C_h eta b hcompleted
            hnotStopped i a C) := rfl
    _ ≤ (ENNReal.ofReal isolate * ENNReal.ofReal armMass *
          ENNReal.ofReal idFraction) *
        GeneratedBlockStartLaw.originalCoordinatesLaw p
          (activeHeldFutureEvent p s ids rewards C_star C_h eta b hcompleted
            hnotStopped i a C) :=
      mul_le_mul_of_nonneg_right hcoeff bot_le
    _ = _ := by
      dsimp [isolate, armMass, idFraction]
      ac_rfl

/-- The target guard used by the analytical support budget. It retains the
same complete isolation event, target avoidance, and whole-future event as
the per-ID cells. -/
def supportChoiceGuardFutureEvent (p : Parameters)
    (s : Fin (n_boot p)) (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (b : ReferenceInitializationRun.Boundary p) (hcompleted : b.completed = s.val)
    (hnotStopped : b.crossing = none) (i : Incoming p b) (a : Fin p.K)
    (C : Set (FutureRow p s)) : Set (OriginalCoordinates p) :=
  GeneratedBlockGuardLaw.generatedProcessedGuardFutureEvent p s ids rewards C_star C_h eta
    b hcompleted hnotStopped (GeneratedBlockGuardLaw.focalIsolationGuard p b i a)
    {z | z ≠ a} C

/-- The private identifier read from the actual processed physical profile. -/
def actualProcessedPrivateID (p : Parameters)
    (s : Fin (n_boot p)) (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (b : ReferenceInitializationRun.Boundary p) (hcompleted : b.completed = s.val)
    (hnotStopped : b.crossing = none) (i : Incoming p b)
    (e : OriginalCoordinates p) : Fin (A_id p) :=
  ((GeneratedBlockGuardLaw.actualProcessedProfile p s ids rewards C_star C_h eta b
    hcompleted hnotStopped e i).2).2

/-- At an actual boundary atom, the processed profile is the accepted
original generated block profile restricted to actual incoming followers. -/
theorem actualProcessedProfile_eq_generatedProfile (p : Parameters)
    (s : Fin (n_boot p)) (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (b : ReferenceInitializationRun.Boundary p) (hcompleted : b.completed = s.val)
    (hnotStopped : b.crossing = none) (e : OriginalCoordinates p)
    (hboundary : GeneratedBlockStartLaw.boundaryAtOriginal p s ids rewards
      C_star C_h eta e = b) :
    GeneratedBlockGuardLaw.actualProcessedProfile p s ids rewards C_star C_h eta b
      hcompleted hnotStopped e =
      GeneratedBlockGuardLaw.sourceRestrictedProfile p b
        (GeneratedBlockDrawLaw.generatedCurrentBlockProfile p s b e.2) :=
  GeneratedBlockGuardLaw.actualProcessedProfile_eq_generatedProfile p s ids rewards
    C_star C_h eta b hcompleted hnotStopped e hboundary

/-- At the same actual boundary atom, the processed target is the accepted
original target coordinate. -/
theorem actualProcessedTarget_eq_generatedTarget (p : Parameters)
    (s : Fin (n_boot p)) (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (b : ReferenceInitializationRun.Boundary p) (hcompleted : b.completed = s.val)
    (hnotStopped : b.crossing = none) (e : OriginalCoordinates p)
    (hboundary : GeneratedBlockStartLaw.boundaryAtOriginal p s ids rewards
      C_star C_h eta e = b) :
    GeneratedBlockGuardLaw.actualProcessedTarget p s ids rewards C_star C_h eta b
      hcompleted hnotStopped e =
      GeneratedBlockDrawLaw.generatedCurrentTarget p s e.2 :=
  GeneratedBlockGuardLaw.actualProcessedTarget_eq_generatedTarget p s ids rewards
    C_star C_h eta b hcompleted hnotStopped e hboundary

/-- On a boundary atom, the profile and target clauses in a processed guard
are exactly the original generated private-profile and target conditions.
The identifications follow from the accepted boundary semantics. -/
theorem generatedProcessedGuardFutureEvent_mem_iff_originalCoordinates
    (p : Parameters) (s : Fin (n_boot p)) (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (b : ReferenceInitializationRun.Boundary p) (hcompleted : b.completed = s.val)
    (hnotStopped : b.crossing = none)
    (G : Set (GeneratedBlockGuardLaw.IncomingProfile p b)) (H : Set (Fin p.K))
    (C : Set (FutureRow p s)) (e : OriginalCoordinates p) :
    e ∈ GeneratedBlockGuardLaw.generatedProcessedGuardFutureEvent p s ids rewards
      C_star C_h eta b hcompleted hnotStopped G H C ↔
    GeneratedBlockStartLaw.boundaryAtOriginal p s ids rewards C_star C_h eta e = b ∧
      GeneratedBlockGuardLaw.sourceRestrictedProfile p b
        (GeneratedBlockDrawLaw.generatedCurrentBlockProfile p s b e.2) ∈ G ∧
      GeneratedBlockDrawLaw.generatedCurrentTarget p s e.2 ∈ H ∧
      GeneratedBlockStartLaw.futureRowOf p s e ∈ C := by
  simp only [GeneratedBlockGuardLaw.generatedProcessedGuardFutureEvent]
  constructor
  · rintro ⟨hb, hp, ht, hfuture, hprofileEq, htargetEq⟩
    rw [actualProcessedProfile_eq_generatedProfile p s ids rewards C_star C_h eta
      b hcompleted hnotStopped e hb] at hp
    rw [actualProcessedTarget_eq_generatedTarget p s ids rewards C_star C_h eta
      b hcompleted hnotStopped e hb] at ht
    exact ⟨hb, hp, ht, hfuture⟩
  · rintro ⟨hb, hp, ht, hfuture⟩
    have hprofileEq := actualProcessedProfile_eq_generatedProfile p s ids rewards
      C_star C_h eta b hcompleted hnotStopped e hb
    have htargetEq := actualProcessedTarget_eq_generatedTarget p s ids rewards
      C_star C_h eta b hcompleted hnotStopped e hb
    exact ⟨hb, by simpa [hprofileEq] using hp, by simpa [htargetEq] using ht,
      hfuture, hprofileEq, htargetEq⟩

/-- On a boundary atom, the private ID in the actual physical profile is the
same original ID coordinate used by the generated law. -/
theorem actualProcessedPrivateID_eq_generatedPrivateID (p : Parameters)
    (s : Fin (n_boot p)) (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (b : ReferenceInitializationRun.Boundary p) (hcompleted : b.completed = s.val)
    (hnotStopped : b.crossing = none) (i : Incoming p b)
    (e : OriginalCoordinates p)
    (hboundary : GeneratedBlockStartLaw.boundaryAtOriginal p s ids rewards
      C_star C_h eta e = b) :
    actualProcessedPrivateID p s ids rewards C_star C_h eta b hcompleted hnotStopped i e =
      (GeneratedBlockDrawLaw.generatedCurrentBlockProfile p s b e.2
        (BootstrapPhysicalInput.sourceFollowerIndex p i.1)).2.2 := by
  have hprofile := actualProcessedProfile_eq_generatedProfile p s ids rewards
    C_star C_h eta b hcompleted hnotStopped e hboundary
  exact congrArg (fun q : GeneratedBlockGuardLaw.IncomingProfile p b => (q i).2.2)
    hprofile

/-- Literal support-choice cell, before weighting by the analytical
supported-ID-zero count. -/
def supportChoiceCell (p : Parameters)
    (s : Fin (n_boot p)) (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (b : ReferenceInitializationRun.Boundary p) (hcompleted : b.completed = s.val)
    (hnotStopped : b.crossing = none) (i : Incoming p b) (a : Fin p.K)
    (u : Fin (A_id p)) (C : Set (FutureRow p s)) : Set (OriginalCoordinates p) :=
  isolatedPrivateIDTargetFutureEvent p s ids rewards C_star C_h eta b hcompleted
    hnotStopped i a u C

/-- The concrete analytical support budget: each original private-ID cell is
weighted by its supported zero-bit count divided by 16. This is not the
physical gain `G_{i,s}`. -/
def analyticalSupportBudget (p : Parameters)
    (s : Fin (n_boot p)) (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (b : ReferenceInitializationRun.Boundary p) (hcompleted : b.completed = s.val)
    (hnotStopped : b.crossing = none) (i : Incoming p b) (a : Fin p.K)
    (C : Set (FutureRow p s)) (e : OriginalCoordinates p) : ℝ :=
  ∑ u : Fin (A_id p),
    (supportChoiceCell p s ids rewards C_star C_h eta b hcompleted hnotStopped
      i a u C).indicator
      (fun _ => supportedIDZeroCount p s ids rewards a u / 16) e

/-- Measurability of every per-ID original-coordinate cell. -/
theorem measurableSet_supportChoiceCell (p : Parameters)
    (s : Fin (n_boot p)) (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (b : ReferenceInitializationRun.Boundary p) (hcompleted : b.completed = s.val)
    (hnotStopped : b.crossing = none) (i : Incoming p b) (a : Fin p.K)
    (u : Fin (A_id p)) (C : Set (FutureRow p s)) (hC : MeasurableSet C) :
    MeasurableSet (supportChoiceCell p s ids rewards C_star C_h eta b hcompleted
      hnotStopped i a u C) :=
  GeneratedBlockGuardLaw.measurableSet_generatedProcessedGuardFutureEvent p s ids
    rewards C_star C_h eta b hcompleted hnotStopped
    (GeneratedBlockGuardLaw.focalIsolationPrivateIdGuard p b i a u)
    {z | z ≠ a} C hC

/-- Different original private-ID cells are disjoint. -/
theorem supportChoiceCell_disjoint (p : Parameters)
    (s : Fin (n_boot p)) (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (b : ReferenceInitializationRun.Boundary p) (hcompleted : b.completed = s.val)
    (hnotStopped : b.crossing = none) (i : Incoming p b) (a : Fin p.K)
    (u v : Fin (A_id p)) (huv : u ≠ v) (C : Set (FutureRow p s)) :
    Disjoint (supportChoiceCell p s ids rewards C_star C_h eta b hcompleted
      hnotStopped i a u C)
      (supportChoiceCell p s ids rewards C_star C_h eta b hcompleted
        hnotStopped i a v C) := by
  apply Set.disjoint_left.2
  intro e heu hev
  have hu := (by
    simpa [supportChoiceCell] using heu : e ∈
      isolatedPrivateIDTargetFutureEvent p s ids rewards C_star C_h eta b hcompleted
        hnotStopped i a u C)
  have hv := (by
    simpa [supportChoiceCell] using hev : e ∈
      isolatedPrivateIDTargetFutureEvent p s ids rewards C_star C_h eta b hcompleted
        hnotStopped i a v C)
  have hEqU := hu.2.1.2
  have hEqV := hv.2.1.2
  exact huv (hEqU.symm.trans hEqV)

/-- A private-ID cell is exactly the common isolation/target/future event with
the actual processed profile's private identifier fixed to `u`. -/
theorem supportChoiceCell_mem_iff (p : Parameters)
    (s : Fin (n_boot p)) (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (b : ReferenceInitializationRun.Boundary p) (hcompleted : b.completed = s.val)
    (hnotStopped : b.crossing = none) (i : Incoming p b) (a : Fin p.K)
    (u : Fin (A_id p)) (C : Set (FutureRow p s)) (e : OriginalCoordinates p) :
    e ∈ supportChoiceCell p s ids rewards C_star C_h eta b hcompleted hnotStopped
      i a u C ↔
    e ∈ supportChoiceGuardFutureEvent p s ids rewards C_star C_h eta b hcompleted
        hnotStopped i a C ∧
      actualProcessedPrivateID p s ids rewards C_star C_h eta b hcompleted
        hnotStopped i e = u := by
  simp only [supportChoiceCell, isolatedPrivateIDTargetFutureEvent,
    supportChoiceGuardFutureEvent, actualProcessedPrivateID,
    GeneratedBlockGuardLaw.generatedProcessedGuardFutureEvent,
    GeneratedBlockGuardLaw.focalIsolationPrivateIdGuard,
    GeneratedBlockGuardLaw.focalIsolationGuard]
  constructor
  · rintro ⟨hb, hrest⟩
    rcases hrest with ⟨hprofileID, htail⟩
    rcases hprofileID with ⟨hprofile, hid⟩
    rcases htail with ⟨htarget, hfuture, hprofileEq, htargetEq⟩
    exact ⟨⟨hb, hprofile, htarget, hfuture, hprofileEq, htargetEq⟩, hid⟩
  · rintro ⟨⟨hb, hprofile, htarget, hfuture, hprofileEq, htargetEq⟩, hid⟩
    exact ⟨hb, ⟨hprofile, hid⟩, htarget, hfuture, hprofileEq, htargetEq⟩

/-- The analytical budget is pointwise the same common guard indicator,
weighted by the supported-zero sum at the private ID in the actual processed
profile. The boundary identification theorems above identify this field with
the original `U` coordinate on every boundary atom. -/
theorem analyticalSupportBudget_eq_actualProfileSupport (p : Parameters)
    (s : Fin (n_boot p)) (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (b : ReferenceInitializationRun.Boundary p) (hcompleted : b.completed = s.val)
    (hnotStopped : b.crossing = none) (i : Incoming p b) (a : Fin p.K)
    (C : Set (FutureRow p s)) (e : OriginalCoordinates p) :
    analyticalSupportBudget p s ids rewards C_star C_h eta b hcompleted hnotStopped
      i a C e =
    (supportChoiceGuardFutureEvent p s ids rewards C_star C_h eta b hcompleted
      hnotStopped i a C).indicator
      (fun e => supportedIDZeroCount p s ids rewards a
        (actualProcessedPrivateID p s ids rewards C_star C_h eta b hcompleted
          hnotStopped i e) / 16) e := by
  classical
  let common := supportChoiceGuardFutureEvent p s ids rewards C_star C_h eta b
    hcompleted hnotStopped i a C
  let actualID := actualProcessedPrivateID p s ids rewards C_star C_h eta b
    hcompleted hnotStopped i e
  have hcell (u : Fin (A_id p)) :
      e ∈ supportChoiceCell p s ids rewards C_star C_h eta b hcompleted
        hnotStopped i a u C ↔ e ∈ common ∧ actualID = u := by
    simpa [common, actualID] using
      supportChoiceCell_mem_iff p s ids rewards C_star C_h eta b hcompleted
        hnotStopped i a u C e
  by_cases he : e ∈ common
  · rw [analyticalSupportBudget]
    calc
      _ = ∑ u : Fin (A_id p),
          if actualID = u then supportedIDZeroCount p s ids rewards a u / 16 else 0 := by
            apply Finset.sum_congr rfl
            intro u hu
            by_cases hid : actualID = u
            · have hmem := (hcell u).2 ⟨he, hid⟩
              simp [hmem, hid]
            · have hnot : e ∉ supportChoiceCell p s ids rewards C_star C_h eta b
                  hcompleted hnotStopped i a u C := by
                intro hmem
                exact hid ((hcell u).mp hmem).2
              simp [hnot, hid]
      _ = supportedIDZeroCount p s ids rewards a actualID / 16 := by simp
      _ = (supportChoiceGuardFutureEvent p s ids rewards C_star C_h eta b
            hcompleted hnotStopped i a C).indicator
            (fun e => supportedIDZeroCount p s ids rewards a
              (actualProcessedPrivateID p s ids rewards C_star C_h eta b
                hcompleted hnotStopped i e) / 16) e := by
            rw [Set.indicator_of_mem he]
  · rw [analyticalSupportBudget]
    have hnot (u : Fin (A_id p)) :
        e ∉ supportChoiceCell p s ids rewards C_star C_h eta b hcompleted
          hnotStopped i a u C := by
      intro hmem
      exact he ((hcell u).mp hmem).1
    have hsum :
        (∑ u : Fin (A_id p),
          (supportChoiceCell p s ids rewards C_star C_h eta b hcompleted
            hnotStopped i a u C).indicator
            (fun _ => supportedIDZeroCount p s ids rewards a u / 16) e) = 0 := by
      apply Finset.sum_eq_zero
      intro u hu
      rw [Set.indicator_of_notMem (hnot u)]
    rw [hsum, Set.indicator_of_notMem he]

/-- On every actual boundary atom, the budget's supported-zero count is read
from the original extended-private `U` coordinate through the accepted
generated block profile. -/
theorem analyticalSupportBudget_eq_originalPrivateID_on_boundary (p : Parameters)
    (s : Fin (n_boot p)) (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (b : ReferenceInitializationRun.Boundary p) (hcompleted : b.completed = s.val)
    (hnotStopped : b.crossing = none) (i : Incoming p b) (a : Fin p.K)
    (C : Set (FutureRow p s)) (e : OriginalCoordinates p)
    (hboundary : GeneratedBlockStartLaw.boundaryAtOriginal p s ids rewards
      C_star C_h eta e = b) :
    analyticalSupportBudget p s ids rewards C_star C_h eta b hcompleted
      hnotStopped i a C e =
    (supportChoiceGuardFutureEvent p s ids rewards C_star C_h eta b hcompleted
      hnotStopped i a C).indicator
      (fun _ => supportedIDZeroCount p s ids rewards a
        ((GeneratedBlockDrawLaw.generatedCurrentBlockProfile p s b e.2
          (BootstrapPhysicalInput.sourceFollowerIndex p i.1)).2.2) / 16) e := by
  rw [analyticalSupportBudget_eq_actualProfileSupport]
  by_cases he : e ∈ supportChoiceGuardFutureEvent p s ids rewards C_star C_h eta b
      hcompleted hnotStopped i a C
  · simp only [Set.indicator_of_mem he]
    rw [actualProcessedPrivateID_eq_generatedPrivateID p s ids rewards C_star C_h eta
      b hcompleted hnotStopped i e hboundary]
  · simp [Set.indicator_of_notMem he]

/-- The real mass of one support-choice cell relative to the active-held
boundary/future cell. The identity remains valid when either base mass is
zero. -/
private theorem supportChoiceCell_real_mass (p : Parameters)
    (s : Fin (n_boot p)) (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (b : ReferenceInitializationRun.Boundary p) (hcompleted : b.completed = s.val)
    (hnotStopped : b.crossing = none) (i : Incoming p b) (a : Fin p.K)
    (u : Fin (A_id p)) (C : Set (FutureRow p s)) (hC : MeasurableSet C) :
    (GeneratedBlockStartLaw.originalCoordinatesLaw p
      (supportChoiceCell p s ids rewards C_star C_h eta b hcompleted
        hnotStopped i a u C)).toReal =
      (GeneratedBlockStartLaw.originalCoordinatesLaw p
        (activeHeldFutureEvent p s ids rewards C_star C_h eta b hcompleted
          hnotStopped i a C)).toReal *
        (1 - 1 / (p.m : ℝ)) ^ (incomingCount p b - 1) *
        (((p.K - 1 : ℕ) : ℝ) / (p.K : ℝ)) *
        (1 / (A_id p : ℝ)) := by
  let boundaryMass := GeneratedBlockStartLaw.originalCoordinatesLaw p
    {e | GeneratedBlockStartLaw.boundaryAtOriginal p s ids rewards C_star C_h eta e = b}
  let futureMass := CompleteRowStoppingLaw.futureArrayLaw p
    (GeneratedBlockStartLaw.blockStartIndex p s) C
  let pHeld := BootstrapWeightPotential.probability (b_N p)
    (b.numerators (BootstrapPhysicalInput.sourceFollowerIndex p i.1)) a /
      (p.m : ℝ)
  let isolate := (1 - 1 / (p.m : ℝ)) ^ (incomingCount p b - 1)
  let idMass := 1 / (A_id p : ℝ)
  let targetMass := ((p.K - 1 : ℕ) : ℝ) / (p.K : ℝ)
  have hpHeld : 0 ≤ pHeld := by
    exact div_nonneg
      (BootstrapBlockConstruction.heldArmProbability_pos p
        (b.numerators (BootstrapPhysicalInput.sourceFollowerIndex p i.1)) a).le
      (Nat.cast_nonneg _)
  have hIsolate : 0 ≤ isolate := by
    exact pow_nonneg (BootstrapBlockConstruction.activityProbability_nonneg p false)
      (incomingCount p b - 1)
  have hidMass : 0 ≤ idMass := by
    exact one_div_nonneg.mpr (Nat.cast_nonneg _)
  have htargetMass : 0 ≤ targetMass := by positivity
  have hprofile : 0 ≤ (pHeld * idMass) * isolate :=
    mul_nonneg (mul_nonneg hpHeld hidMass) hIsolate
  have hactive := activeHeldFutureEvent_mass p s ids rewards C_star C_h eta b
    hcompleted hnotStopped i a C hC
  have hcell := isolatedPrivateIDTargetFutureEvent_mass p s ids rewards C_star C_h
    eta b hcompleted hnotStopped i a u C hC
  have hactive' :
      GeneratedBlockStartLaw.originalCoordinatesLaw p
        (activeHeldFutureEvent p s ids rewards C_star C_h eta b hcompleted
          hnotStopped i a C) = boundaryMass * ENNReal.ofReal pHeld * futureMass := by
    simpa [activeHeldFutureEvent, boundaryMass, futureMass, pHeld] using hactive
  have hcell' :
      GeneratedBlockStartLaw.originalCoordinatesLaw p
        (supportChoiceCell p s ids rewards C_star C_h eta b hcompleted
          hnotStopped i a u C) =
      boundaryMass * ENNReal.ofReal ((pHeld * idMass) * isolate) *
        ENNReal.ofReal targetMass * futureMass := by
    simpa [supportChoiceCell, isolatedPrivateIDTargetFutureEvent,
      boundaryMass, futureMass, pHeld, isolate, idMass, targetMass] using hcell
  have hactiveReal := congrArg ENNReal.toReal hactive'
  have hcellReal := congrArg ENNReal.toReal hcell'
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hpHeld] at hactiveReal
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hprofile,
    ENNReal.toReal_ofReal htargetMass] at hcellReal
  rw [hcellReal, hactiveReal]
  dsimp [pHeld, isolate, idMass, targetMass]
  ring

/-- Exact real integral of the analytical support budget. The mass factor is
the existing focal active-held event with target `univ`, and the entire
measurable future-row event remains present. No positive-mass premise is used.
Sources: `appendix_b_communication.tex:376-407,476-506`. -/
theorem integral_analyticalSupportBudget_eq (p : Parameters)
    (s : Fin (n_boot p)) (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (b : ReferenceInitializationRun.Boundary p) (hcompleted : b.completed = s.val)
    (hnotStopped : b.crossing = none) (i : Incoming p b) (a : Fin p.K)
    (C : Set (FutureRow p s)) (hC : MeasurableSet C) :
    (∫ e, analyticalSupportBudget p s ids rewards C_star C_h eta b hcompleted
      hnotStopped i a C e ∂GeneratedBlockStartLaw.originalCoordinatesLaw p) =
      (GeneratedBlockStartLaw.originalCoordinatesLaw p
        (activeHeldFutureEvent p s ids rewards C_star C_h eta b hcompleted
          hnotStopped i a C)).toReal *
        (1 - 1 / (p.m : ℝ)) ^ (incomingCount p b - 1) *
        (((p.K - 1 : ℕ) : ℝ) / (p.K : ℝ)) *
        ((∑ u : Fin (A_id p), supportedIDZeroCount p s ids rewards a u) /
          (16 * (A_id p : ℝ))) := by
  classical
  let μ := GeneratedBlockStartLaw.originalCoordinatesLaw p
  unfold analyticalSupportBudget
  rw [integral_finsetSum (Finset.univ) (fun u hu =>
    (integrable_const _).indicator
      (measurableSet_supportChoiceCell p s ids rewards C_star C_h eta b hcompleted
        hnotStopped i a u C hC))]
  calc
    _ = ∑ u : Fin (A_id p),
        (μ (supportChoiceCell p s ids rewards C_star C_h eta b hcompleted
          hnotStopped i a u C)).toReal *
          (supportedIDZeroCount p s ids rewards a u / 16) := by
      apply Finset.sum_congr rfl
      intro u hu
      exact GeneratedBlockGuardLaw.originalCoordinatesLaw_integral_indicator_const p
        (supportChoiceCell p s ids rewards C_star C_h eta b hcompleted
          hnotStopped i a u C)
        (measurableSet_supportChoiceCell p s ids rewards C_star C_h eta b hcompleted
          hnotStopped i a u C hC)
        (supportedIDZeroCount p s ids rewards a u / 16)
    _ = ∑ u : Fin (A_id p),
        ((μ (activeHeldFutureEvent p s ids rewards C_star C_h eta b hcompleted
          hnotStopped i a C)).toReal *
          (1 - 1 / (p.m : ℝ)) ^ (incomingCount p b - 1) *
          (((p.K - 1 : ℕ) : ℝ) / (p.K : ℝ)) *
          (1 / (A_id p : ℝ))) *
          (supportedIDZeroCount p s ids rewards a u / 16) := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [supportChoiceCell_real_mass p s ids rewards C_star C_h eta b hcompleted
        hnotStopped i a u C hC]
    _ = (μ (activeHeldFutureEvent p s ids rewards C_star C_h eta b hcompleted
          hnotStopped i a C)).toReal *
        (1 - 1 / (p.m : ℝ)) ^ (incomingCount p b - 1) *
        (((p.K - 1 : ℕ) : ℝ) / (p.K : ℝ)) *
        ((∑ u : Fin (A_id p), supportedIDZeroCount p s ids rewards a u) /
          (16 * (A_id p : ℝ))) := by
      have hA : (A_id p : ℝ) ≠ 0 := by
        exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt (BootstrapDimensions.A_id_pos p))
      calc
        _ = ((μ (activeHeldFutureEvent p s ids rewards C_star C_h eta b hcompleted
              hnotStopped i a C)).toReal *
            (1 - 1 / (p.m : ℝ)) ^ (incomingCount p b - 1) *
            (((p.K - 1 : ℕ) : ℝ) / (p.K : ℝ)) *
            (1 / (A_id p : ℝ) * (1 / 16))) *
            (∑ u : Fin (A_id p), supportedIDZeroCount p s ids rewards a u) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro u hu
          ring
        _ = _ := by
          field_simp [hA]

/-- The exact isolation factor at the incoming source image is at least one
quarter. The image-cardinality theorem makes this the actual incoming count. -/
private theorem isolationPower_ge_quarter (p : Parameters)
    (b : ReferenceInitializationRun.Boundary p) (i : Incoming p b) :
    (1 / 4 : ℝ) ≤ (1 - 1 / (p.m : ℝ)) ^ (incomingCount p b - 1) := by
  have hqnonneg : 0 ≤ 1 - 1 / (p.m : ℝ) := by
    exact BootstrapBlockConstruction.activityProbability_nonneg p false
  have hqle : 1 - 1 / (p.m : ℝ) ≤ 1 := by
    have hmpos : 0 < (p.m : ℝ) := Nat.cast_pos.mpr (ConstructorDimensions.m_pos p)
    have hinv : 0 ≤ 1 / (p.m : ℝ) := by positivity
    linarith
  have hcount := GeneratedBlockGuardLaw.sourceIncomingFinset_other_count_le p b i
  calc
    (1 / 4 : ℝ) ≤ (1 - 1 / (p.m : ℝ)) ^ (p.m - 2) :=
      BootstrapBlockIsolation.inactivity_power_lower_bound p
    _ ≤ (1 - 1 / (p.m : ℝ)) ^ (incomingCount p b - 1) :=
      pow_le_pow_of_le_one hqnonneg hqle (by simpa [incomingCount] using hcount)

/-- The exact target-avoidance factor is at least one half. -/
private theorem targetAvoidance_ge_half (p : Parameters) :
    (1 / 2 : ℝ) ≤ ((p.K - 1 : ℕ) : ℝ) / (p.K : ℝ) := by
  have hK : 2 ≤ p.K := le_trans p.two_le_m (Nat.le_of_lt p.m_lt_K)
  have hKreal : (2 : ℝ) ≤ (p.K : ℝ) := by exact_mod_cast hK
  have hKpos : 0 < (p.K : ℝ) := Nat.cast_pos.mpr (ConstructorDimensions.K_pos p)
  have hcast : ((p.K - 1 : ℕ) : ℝ) = (p.K : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  rw [hcast, div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) hKpos]
  nlinarith

/-- The support budget's integral is at least one three-hundred-eighty-fourth
of the literal support times the actual active-held boundary/future mass.
This is still an analytical budget statement; it is not a physical-gain
claim. -/
theorem integral_analyticalSupportBudget_ge_support_div384 (p : Parameters)
    (s : Fin (n_boot p)) (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (b : ReferenceInitializationRun.Boundary p) (hcompleted : b.completed = s.val)
    (hnotStopped : b.crossing = none) (i : Incoming p b) (a : Fin p.K)
    (C : Set (FutureRow p s)) (hC : MeasurableSet C)
    (hgood : ids ∈ IdentificationGoodEvent.identificationGoodEvent p) :
    blockSupportCount p s rewards a / 384 *
        (GeneratedBlockStartLaw.originalCoordinatesLaw p
          (activeHeldFutureEvent p s ids rewards C_star C_h eta b hcompleted
            hnotStopped i a C)).toReal ≤
      ∫ e, analyticalSupportBudget p s ids rewards C_star C_h eta b hcompleted
        hnotStopped i a C e ∂GeneratedBlockStartLaw.originalCoordinatesLaw p := by
  rw [integral_analyticalSupportBudget_eq p s ids rewards C_star C_h eta b
    hcompleted hnotStopped i a C hC]
  let support := blockSupportCount p s rewards a
  let activeMass := (GeneratedBlockStartLaw.originalCoordinatesLaw p
    (activeHeldFutureEvent p s ids rewards C_star C_h eta b hcompleted
      hnotStopped i a C)).toReal
  let isolate := (1 - 1 / (p.m : ℝ)) ^ (incomingCount p b - 1)
  let target := ((p.K - 1 : ℕ) : ℝ) / (p.K : ℝ)
  let supportAverage :=
    (∑ u : Fin (A_id p), supportedIDZeroCount p s ids rewards a u) /
      (16 * (A_id p : ℝ))
  have hsupp : 0 ≤ support := blockSupportCount_nonneg p s rewards a
  have hmass : 0 ≤ activeMass := ENNReal.toReal_nonneg
  have hA : 0 < (A_id p : ℝ) :=
    Nat.cast_pos.mpr (BootstrapDimensions.A_id_pos p)
  have hsum := sum_supportedIDZeroCount_lower p s ids rewards a hgood
  have hratio : support / 48 ≤ supportAverage := by
    dsimp [supportAverage]
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 48)
      (mul_pos (by norm_num : (0 : ℝ) < 16) hA)).2
    nlinarith [hsum]
  have hisolate : (1 / 4 : ℝ) ≤ isolate := by
    exact isolationPower_ge_quarter p b i
  have htarget : (1 / 2 : ℝ) ≤ target := targetAvoidance_ge_half p
  have hfactor : (1 / 8 : ℝ) ≤ isolate * target := by
    calc
      (1 / 8 : ℝ) = (1 / 4 : ℝ) * (1 / 2 : ℝ) := by norm_num
      _ ≤ isolate * target :=
        mul_le_mul hisolate htarget (by norm_num) (by positivity)
  have hproduct : support / 384 ≤ isolate * target * supportAverage := by
    calc
      support / 384 = (1 / 8 : ℝ) * (support / 48) := by ring
      _ ≤ (isolate * target) * supportAverage :=
        mul_le_mul hfactor hratio (by positivity) (by positivity)
  calc
    _ ≤ (isolate * target * supportAverage) *
        (GeneratedBlockStartLaw.originalCoordinatesLaw p
          (activeHeldFutureEvent p s ids rewards C_star C_h eta b hcompleted
            hnotStopped i a C)).toReal :=
          mul_le_mul_of_nonneg_right hproduct hmass
    _ = _ := by ring

/-- The customary one-five-hundred-twelfth weakening of the support-budget
integral bound. -/
theorem integral_analyticalSupportBudget_ge_support_div512 (p : Parameters)
    (s : Fin (n_boot p)) (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (b : ReferenceInitializationRun.Boundary p) (hcompleted : b.completed = s.val)
    (hnotStopped : b.crossing = none) (i : Incoming p b) (a : Fin p.K)
    (C : Set (FutureRow p s)) (hC : MeasurableSet C)
    (hgood : ids ∈ IdentificationGoodEvent.identificationGoodEvent p) :
    blockSupportCount p s rewards a / 512 *
        (GeneratedBlockStartLaw.originalCoordinatesLaw p
          (activeHeldFutureEvent p s ids rewards C_star C_h eta b hcompleted
            hnotStopped i a C)).toReal ≤
      ∫ e, analyticalSupportBudget p s ids rewards C_star C_h eta b hcompleted
        hnotStopped i a C e ∂GeneratedBlockStartLaw.originalCoordinatesLaw p := by
  have h384 := integral_analyticalSupportBudget_ge_support_div384 p s ids rewards
    C_star C_h eta b hcompleted hnotStopped i a C hC hgood
  have hsupport := blockSupportCount_nonneg p s rewards a
  have hmass : 0 ≤ (GeneratedBlockStartLaw.originalCoordinatesLaw p
      (activeHeldFutureEvent p s ids rewards C_star C_h eta b hcompleted
        hnotStopped i a C)).toReal := ENNReal.toReal_nonneg
  have hweak : blockSupportCount p s rewards a / 512 ≤
      blockSupportCount p s rewards a / 384 := by
    nlinarith [hsupport]
  exact (mul_le_mul_of_nonneg_right hweak hmass).trans h384

/-- Every supported-zero count is nonnegative. -/
theorem supportedIDZeroCount_nonneg (p : Parameters)
    (s : Fin (n_boot p)) (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (a : Fin p.K)
    (u : Fin (A_id p)) :
    0 ≤ supportedIDZeroCount p s ids rewards a u := by
  apply Finset.sum_nonneg
  intro t ht
  have hchi : 0 ≤ roundedSupportChi p rewards t a := by
    by_cases h : 0 < (rewards t a).val <;> simp [roundedSupportChi, h]
  by_cases hbit : ids u t = false
  · simp [hbit]
    exact hchi
  · simp [hbit]

/-- A fixed ID's supported-zero count is bounded by the total support count. -/
theorem supportedIDZeroCount_le_blockSupportCount (p : Parameters)
    (s : Fin (n_boot p)) (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (a : Fin p.K)
    (u : Fin (A_id p)) :
    supportedIDZeroCount p s ids rewards a u ≤ blockSupportCount p s rewards a := by
  unfold supportedIDZeroCount blockSupportCount
  apply Finset.sum_le_sum
  intro t ht
  have hchi : 0 ≤ roundedSupportChi p rewards t a := by
    by_cases h : 0 < (rewards t a).val <;> simp [roundedSupportChi, h]
  have hbit : (if ids u t = false then (1 : ℝ) else 0) ≤ 1 := by
    split_ifs <;> norm_num
  calc
    roundedSupportChi p rewards t a * (if ids u t = false then 1 else 0) ≤
        roundedSupportChi p rewards t a * 1 := mul_le_mul_of_nonneg_left hbit hchi
    _ = roundedSupportChi p rewards t a := by ring

/-- The support is bounded by the actual calendar-block length, including
the clipped final block. -/
theorem blockSupportCount_le_calendarBlock_card (p : Parameters)
    (s : Fin (n_boot p)) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (a : Fin p.K) :
    blockSupportCount p s rewards a ≤
      (BootstrapDimensions.calendarBlock p s).card := by
  unfold blockSupportCount
  calc
    _ ≤ ∑ _t ∈ BootstrapDimensions.calendarBlock p s, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro t ht
      by_cases h : 0 < (rewards t a).val <;> simp [roundedSupportChi, h]
    _ = (BootstrapDimensions.calendarBlock p s).card := by simp

/-- Every weighted cell in the support budget is nonnegative. -/
theorem analyticalSupportBudget_nonneg (p : Parameters)
    (s : Fin (n_boot p)) (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (b : ReferenceInitializationRun.Boundary p) (hcompleted : b.completed = s.val)
    (hnotStopped : b.crossing = none) (i : Incoming p b) (a : Fin p.K)
    (C : Set (FutureRow p s)) (e : OriginalCoordinates p) :
    0 ≤ analyticalSupportBudget p s ids rewards C_star C_h eta b hcompleted
      hnotStopped i a C e := by
  unfold analyticalSupportBudget
  apply Finset.sum_nonneg
  intro u hu
  by_cases he : e ∈ supportChoiceCell p s ids rewards C_star C_h eta b hcompleted
      hnotStopped i a u C
  · simp [he]
    exact div_nonneg (supportedIDZeroCount_nonneg p s ids rewards a u) (by norm_num)
  · simp [he]

/-- The support budget is measurable on the original complete-row and
extended-private coordinate carrier. -/
theorem measurable_analyticalSupportBudget (p : Parameters)
    (s : Fin (n_boot p)) (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (b : ReferenceInitializationRun.Boundary p) (hcompleted : b.completed = s.val)
    (hnotStopped : b.crossing = none) (i : Incoming p b) (a : Fin p.K)
    (C : Set (FutureRow p s)) (hC : MeasurableSet C) :
    Measurable (analyticalSupportBudget p s ids rewards C_star C_h eta b
      hcompleted hnotStopped i a C) := by
  classical
  unfold analyticalSupportBudget
  apply Finset.measurable_fun_sum
  intro u hu
  exact measurable_const.indicator
    (measurableSet_supportChoiceCell p s ids rewards C_star C_h eta b hcompleted
      hnotStopped i a u C hC)

/-- The analytical support budget is integrable under the original
complete-row and extended-private product law. -/
theorem integrable_analyticalSupportBudget (p : Parameters)
    (s : Fin (n_boot p)) (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (b : ReferenceInitializationRun.Boundary p) (hcompleted : b.completed = s.val)
    (hnotStopped : b.crossing = none) (i : Incoming p b) (a : Fin p.K)
    (C : Set (FutureRow p s)) (hC : MeasurableSet C) :
    Integrable (analyticalSupportBudget p s ids rewards C_star C_h eta b
      hcompleted hnotStopped i a C) (GeneratedBlockStartLaw.originalCoordinatesLaw p) := by
  classical
  unfold analyticalSupportBudget
  apply integrable_finsetSum
  intro u hu
  exact (integrable_const _).indicator
    (measurableSet_supportChoiceCell p s ids rewards C_star C_h eta b hcompleted
      hnotStopped i a u C hC)

/-- Pointwise, the analytical support budget is no larger than one sixteenth
of the source block-length bound. -/
theorem analyticalSupportBudget_le_Bboot_div_sixteen (p : Parameters)
    (s : Fin (n_boot p)) (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (b : ReferenceInitializationRun.Boundary p) (hcompleted : b.completed = s.val)
    (hnotStopped : b.crossing = none) (i : Incoming p b) (a : Fin p.K)
    (C : Set (FutureRow p s)) (e : OriginalCoordinates p) :
    analyticalSupportBudget p s ids rewards C_star C_h eta b hcompleted
      hnotStopped i a C e ≤ (B_boot p : ℝ) / 16 := by
  rw [analyticalSupportBudget_eq_actualProfileSupport]
  by_cases he : e ∈ supportChoiceGuardFutureEvent p s ids rewards C_star C_h eta b
      hcompleted hnotStopped i a C
  · simp [Set.indicator_of_mem, he]
    have hcount := supportedIDZeroCount_le_blockSupportCount p s ids rewards a
      (actualProcessedPrivateID p s ids rewards C_star C_h eta b hcompleted
        hnotStopped i e)
    have hblock := blockSupportCount_le_calendarBlock_card p s rewards a
    have hcalendar := BootstrapDimensions.calendarBlock_card_le_B_boot p s
    exact (div_le_div_of_nonneg_right
      (le_trans hcount (le_trans hblock (by exact_mod_cast hcalendar))) (by norm_num))
  · simp [Set.indicator_of_notMem, he]
    exact div_nonneg (Nat.cast_nonneg _) (by norm_num)

end Bandits.Support.GeneratedBlockChoiceAverages

end
