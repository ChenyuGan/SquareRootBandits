/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.GeneratedProductiveSuccessCells
public import Bandits.Support.GeneratedBootstrapImportanceMean
public import Bandits.Support.ReferenceInitializationMeasurability

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Productive success on arbitrary causal-prefix cells

All events below use the original complete row and private coordinate law.
The prefix restriction is retained in the accepted causal product; no
conditioning on a continuous singleton or replacement boundary law is used.

Sources: `sources/zip4/manuscript/appendix_b_communication.tex:398-483,586-625`
and `sources/zip4/manuscript/07_public_setup.tex:63-113`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal BigOperators
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.CompletePublicTable
open Bandits.Support.ReferenceInitializationRun
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.ActiveRoundActions
open Bandits.Support.GeneratedBootstrapBlockFiltrationRepair
open Bandits.Support.GeneratedBlockChoiceAverages
open Bandits.Support.GeneratedProductiveSuccessCells

namespace Bandits.Support.GeneratedProductiveSuccessPrefixLaw

abbrev Parameters := ConstructorDimensions.Parameters
abbrev Coordinates (p : Parameters) := GeneratedBootstrapRoundLaw.Coordinates p

section BoundaryMass

variable (p : Parameters) (s : Fin (n_boot p)) (ids : IDArray p)
  (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
  (eta : LearningRate) (b : Boundary p) (hcompleted : b.completed = s.val)
  (hnotStopped : b.crossing = none) (i : Incoming p b) (a : Fin p.K)

/-- Exact prefix-weighted active-held mass on an actual incoming boundary.
The factorization is unnormalized, including unreachable boundary cells. -/
theorem activeHeldFutureEvent_prefix_measure
    (V : Set (SourcePrefix p s.val)) (hV : MeasurableSet V) :
    GeneratedBlockStartLaw.originalCoordinatesLaw p
      (sourcePrefix p s.val ⁻¹' V ∩
        activeHeldFutureEvent p s ids rewards C_star C_h eta b hcompleted
          hnotStopped i a Set.univ) =
      GeneratedBlockStartLaw.originalCoordinatesLaw p
        (GeneratedBootstrapImportanceMean.sourcePrefixBoundaryCell p s V ids rewards
          C_star C_h eta b) *
        ENNReal.ofReal (BootstrapWeightPotential.probability (b_N p)
          (b.numerators (BootstrapPhysicalInput.sourceFollowerIndex p i.1)) a /
            (p.m : ℝ)) := by
  have hfactor :=
    GeneratedBootstrapImportanceMean.generatedProcessedGuardFutureEventWithSide_measure
      p s ids rewards C_star C_h eta
      (GeneratedBootstrapImportanceMean.sourcePrefixSideCell p s V)
      (GeneratedBootstrapImportanceMean.measurableSet_sourcePrefixSideCell p s V hV)
      b hcompleted hnotStopped (GeneratedBlockGuardLaw.focalActiveHeldGuard p b i a)
      Set.univ Set.univ MeasurableSet.univ
  have hprofile : BootstrapBlockIsolation.privateBlockProfileEventProbability p
      b.numerators b.weight_ge_one
      (fun c => GeneratedBlockGuardLaw.sourceRestrictedProfile p b c ∈
        GeneratedBlockGuardLaw.focalActiveHeldGuard p b i a) =
      BootstrapWeightPotential.probability (b_N p)
        (b.numerators (BootstrapPhysicalInput.sourceFollowerIndex p i.1)) a /
          (p.m : ℝ) := by
    exact BootstrapBlockIsolation.distinguishedEvent_probability p b.numerators
      b.weight_ge_one (BootstrapPhysicalInput.sourceFollowerIndex p i.1) a
  have hevent :
      GeneratedBootstrapImportanceMean.generatedProcessedGuardFutureEventWithSide
        p s ids rewards C_star C_h eta
        (GeneratedBootstrapImportanceMean.sourcePrefixSideCell p s V) b hcompleted
        hnotStopped (GeneratedBlockGuardLaw.focalActiveHeldGuard p b i a)
        Set.univ Set.univ =
      sourcePrefix p s.val ⁻¹' V ∩
        activeHeldFutureEvent p s ids rewards C_star C_h eta b hcompleted
          hnotStopped i a Set.univ := by
    ext e
    change (_ ∧ _) ↔ (_ ∧ _)
    rw [GeneratedBootstrapImportanceMean.analysisSide_sourcePrefixSideCell_iff]
    rfl
  have hboundary :
      {e | GeneratedBlockStartLaw.analysisSideOf p s e ∈
          GeneratedBootstrapImportanceMean.sourcePrefixSideCell p s V ∧
        GeneratedBlockStartLaw.boundaryAtOriginal p s ids rewards C_star C_h eta e = b} =
      GeneratedBootstrapImportanceMean.sourcePrefixBoundaryCell p s V ids rewards
        C_star C_h eta b := by
    ext e
    exact GeneratedBootstrapImportanceMean.analysisSide_sourcePrefixBoundaryCell_iff
      p s V ids rewards C_star C_h eta b e
  rw [hevent, hboundary, hprofile, GeneratedBlockGuardLaw.targetProbability_univ] at hfactor
  simpa only [ENNReal.ofReal_one, mul_one, measure_univ] using hfactor

/-- Each fixed good-ID cell has its exact mass after an arbitrary measurable
source-prefix restriction. In this SUCCESS calculation the target equals `a`. -/
theorem goodIDChoiceCell_prefix_measure
    (V : Set (SourcePrefix p s.val)) (hV : MeasurableSet V) (u : Fin (A_id p)) :
    GeneratedBlockStartLaw.originalCoordinatesLaw p
      (sourcePrefix p s.val ⁻¹' V ∩
        goodIDChoiceCell p s ids rewards C_star C_h eta b hcompleted
          hnotStopped i a u Set.univ) =
      GeneratedBlockStartLaw.originalCoordinatesLaw p
        (sourcePrefix p s.val ⁻¹' V ∩
          activeHeldFutureEvent p s ids rewards C_star C_h eta b hcompleted
            hnotStopped i a Set.univ) *
      ENNReal.ofReal ((1 - 1 / (p.m : ℝ)) ^ (incomingCount p b - 1)) *
      ENNReal.ofReal (1 / (p.K : ℝ)) * ENNReal.ofReal (1 / (A_id p : ℝ)) := by
  have hfactor := GeneratedBootstrapImportanceMean.supportChoiceTargetCell_prefix_measure
    p s V hV ids rewards C_star C_h eta b hcompleted hnotStopped i a a u
  have hevent :
      GeneratedBootstrapImportanceMean.supportChoiceTargetCellWithSide
        p s ids rewards C_star C_h eta
        (GeneratedBootstrapImportanceMean.sourcePrefixSideCell p s V)
        b hcompleted hnotStopped i a a u =
      sourcePrefix p s.val ⁻¹' V ∩
        goodIDChoiceCell p s ids rewards C_star C_h eta b hcompleted
          hnotStopped i a u Set.univ := by
    ext e
    change (_ ∧ _) ↔ (_ ∧ _)
    rw [GeneratedBootstrapImportanceMean.analysisSide_sourcePrefixSideCell_iff]
    rfl
  rw [hevent] at hfactor
  rw [hfactor, activeHeldFutureEvent_prefix_measure p s ids rewards C_star C_h eta
    b hcompleted hnotStopped i a V hV]
  have hp : 0 ≤ BootstrapWeightPotential.probability (b_N p)
      (b.numerators (BootstrapPhysicalInput.sourceFollowerIndex p i.1)) a /
        (p.m : ℝ) :=
    div_nonneg (BootstrapBlockConstruction.heldArmProbability_pos p _ a).le
      (Nat.cast_nonneg _)
  have hid : 0 ≤ (1 / (A_id p : ℝ)) := by positivity
  rw [ENNReal.ofReal_mul (mul_nonneg hp hid), ENNReal.ofReal_mul hp]
  ac_rfl

/-- Finite disjoint summation over the accepted good IDs, with the SAME
prefix-active-held mass on the right. Good IDs balance every subinterval. -/
theorem goodIDChoiceFutureEvent_prefix_measure
    (V : Set (SourcePrefix p s.val)) (hV : MeasurableSet V) :
    GeneratedBlockStartLaw.originalCoordinatesLaw p
      (sourcePrefix p s.val ⁻¹' V ∩
        goodIDChoiceFutureEvent p s ids rewards C_star C_h eta b hcompleted
          hnotStopped i a Set.univ) =
      GeneratedBlockStartLaw.originalCoordinatesLaw p
        (sourcePrefix p s.val ⁻¹' V ∩
          activeHeldFutureEvent p s ids rewards C_star C_h eta b hcompleted
            hnotStopped i a Set.univ) *
      ENNReal.ofReal ((1 - 1 / (p.m : ℝ)) ^ (incomingCount p b - 1)) *
      ENNReal.ofReal (1 / (p.K : ℝ)) *
      ENNReal.ofReal (((goodIDs p s ids rewards a).card : ℝ) / (A_id p : ℝ)) := by
  classical
  let U := goodIDs p s ids rewards a
  let choice := fun u => sourcePrefix p s.val ⁻¹' V ∩
    goodIDChoiceCell p s ids rewards C_star C_h eta b hcompleted hnotStopped i a u Set.univ
  have hdisj : Set.PairwiseDisjoint (↑U) choice := by
    intro u hu v hv huv
    exact (goodIDChoiceCell_disjoint p s ids rewards C_star C_h eta b hcompleted
      hnotStopped i a u v huv Set.univ).mono Set.inter_subset_right Set.inter_subset_right
  have hmeas : ∀ u ∈ U, MeasurableSet (choice u) := by
    intro u hu
    exact (hV.preimage (measurable_sourcePrefix p s.val)).inter
      (measurableSet_goodIDChoiceCell p s ids rewards C_star C_h eta b hcompleted
        hnotStopped i a u Set.univ MeasurableSet.univ)
  simp only [goodIDChoiceFutureEvent, Set.inter_iUnion]
  rw [measure_biUnion_finset hdisj hmeas]
  dsimp only [choice]
  simp_rw [goodIDChoiceCell_prefix_measure p s ids rewards C_star C_h eta b hcompleted
    hnotStopped i a V hV]
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcast : (U.card : ℝ≥0∞) * ENNReal.ofReal (1 / (A_id p : ℝ)) =
      ENNReal.ofReal ((U.card : ℝ) / (A_id p : ℝ)) := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg U.card)]
    congr 1
    ring
  calc
    _ = (GeneratedBlockStartLaw.originalCoordinatesLaw p
          (sourcePrefix p s.val ⁻¹' V ∩
            activeHeldFutureEvent p s ids rewards C_star C_h eta b hcompleted
              hnotStopped i a Set.univ) *
        ENNReal.ofReal ((1 - 1 / (p.m : ℝ)) ^ (incomingCount p b - 1)) *
        ENNReal.ofReal (1 / (p.K : ℝ))) *
        ((U.card : ℝ≥0∞) * ENNReal.ofReal (1 / (A_id p : ℝ))) := by ac_rfl
    _ = _ := by rw [hcast]

/-- Prefix-weighted good-choice lower mass. No unconditional atom estimate
is multiplied by a prefix event, and no positive-mass premise is needed. -/
theorem goodIDChoiceFutureEvent_prefix_mass_ge
    (V : Set (SourcePrefix p s.val)) (hV : MeasurableSet V)
    (hgood : ids ∈ IdentificationGoodEvent.identificationGoodEvent p) :
    ENNReal.ofReal (3 / (16 * (p.K : ℝ))) *
      GeneratedBlockStartLaw.originalCoordinatesLaw p
        (sourcePrefix p s.val ⁻¹' V ∩
          activeHeldFutureEvent p s ids rewards C_star C_h eta b hcompleted
            hnotStopped i a Set.univ) ≤
      GeneratedBlockStartLaw.originalCoordinatesLaw p
        (sourcePrefix p s.val ⁻¹' V ∩
          goodIDChoiceFutureEvent p s ids rewards C_star C_h eta b hcompleted
            hnotStopped i a Set.univ) := by
  let isolate := (1 - 1 / (p.m : ℝ)) ^ (incomingCount p b - 1)
  let armMass := 1 / (p.K : ℝ)
  let idFraction := ((goodIDs p s ids rewards a).card : ℝ) / (A_id p : ℝ)
  have hqnonneg : 0 ≤ 1 - 1 / (p.m : ℝ) :=
    BootstrapBlockConstruction.activityProbability_nonneg p false
  have hqle : 1 - 1 / (p.m : ℝ) ≤ 1 := by
    have hinv : 0 ≤ 1 / (p.m : ℝ) := by positivity
    linarith only [hinv]
  have hisolate : (1 / 4 : ℝ) ≤ isolate := by
    calc
      (1 / 4 : ℝ) ≤ (1 - 1 / (p.m : ℝ)) ^ (p.m - 2) :=
        BootstrapBlockIsolation.inactivity_power_lower_bound p
      _ ≤ isolate := pow_le_pow_of_le_one hqnonneg hqle
        (GeneratedBlockGuardLaw.sourceIncomingFinset_other_count_le p b i)
  have hratio : (3 / 4 : ℝ) ≤ idFraction := by
    have hcard := goodIDs_card_lower p s ids rewards a hgood
    have hA : 0 < (A_id p : ℝ) := Nat.cast_pos.mpr (A_id_pos p)
    dsimp [idFraction]
    rw [le_div_iff₀ hA]
    linarith only [hcard]
  have hfactor : 3 / (16 * (p.K : ℝ)) ≤ isolate * armMass * idFraction := by
    calc
      _ = (1 / 4 : ℝ) * armMass * (3 / 4 : ℝ) := by dsimp [armMass]; ring
      _ ≤ isolate * armMass * idFraction :=
        mul_le_mul (mul_le_mul_of_nonneg_right hisolate (by positivity)) hratio
          (by positivity) (by positivity)
  have hcoeff : ENNReal.ofReal (3 / (16 * (p.K : ℝ))) ≤
      ENNReal.ofReal isolate * ENNReal.ofReal armMass * ENNReal.ofReal idFraction := by
    rw [← ENNReal.ofReal_mul (pow_nonneg hqnonneg _),
      ← ENNReal.ofReal_mul (mul_nonneg (pow_nonneg hqnonneg _) (by positivity))]
    exact ENNReal.ofReal_le_ofReal hfactor
  rw [goodIDChoiceFutureEvent_prefix_measure p s ids rewards C_star C_h eta b hcompleted
    hnotStopped i a V hV]
  calc
    _ ≤ (ENNReal.ofReal isolate * ENNReal.ofReal armMass * ENNReal.ofReal idFraction) *
        GeneratedBlockStartLaw.originalCoordinatesLaw p
          (sourcePrefix p s.val ⁻¹' V ∩
            activeHeldFutureEvent p s ids rewards C_star C_h eta b hcompleted
              hnotStopped i a Set.univ) := mul_le_mul_of_nonneg_right hcoeff bot_le
    _ = _ := by dsimp [isolate, armMass, idFraction]; ac_rfl

end BoundaryMass

section ActualCells

variable (p : Parameters) (s : Fin (n_boot p)) (ids : IDArray p)
  (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
  (eta : LearningRate)

/-- The accepted active-held guard on a processed boundary is exactly the
restriction of the literal enabled/held event from the partial producer. -/
theorem activeHeldFutureEvent_eq_boundary_inter_enabledHeldCell
    (b : Boundary p) (hcompleted : b.completed = s.val)
    (hnotStopped : b.crossing = none) (i : Incoming p b) (a : Fin p.K) :
    activeHeldFutureEvent p s ids rewards C_star C_h eta b hcompleted
      hnotStopped i a Set.univ =
    {e | GeneratedBlockStartLaw.boundaryAtOriginal p s ids rewards C_star C_h eta e = b} ∩
      enabledHeldCell p ids rewards C_star C_h eta s i.1 a := by
  ext e
  have hfields (hb : GeneratedBlockStartLaw.boundaryAtOriginal p s ids rewards
      C_star C_h eta e = b) :
      e ∈ enabledHeldCell p ids rewards C_star C_h eta s i.1 a ↔
      GeneratedBlockGuardLaw.actualProcessedProfile p s ids rewards C_star C_h eta
        b hcompleted hnotStopped e ∈ GeneratedBlockGuardLaw.focalActiveHeldGuard p b i a := by
    let x := referenceInput p ids rewards C_star C_h eta e
    have hrun : run (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e)
        s.val = b := hb
    have hc : (run x s.val).crossing = none := hrun ▸ hnotStopped
    have hi : i.1 ∈ uninformed (run x s.val) := hrun ▸ i.2
    let hv : b.completed < n_boot p := hcompleted ▸ s.isLt
    have hactual : GeneratedBootstrapPotential.actualBlock x i.1 s =
        weightInput x b hv i := by
      calc
        _ = weightInput x (run x s.val) _ ⟨i.1, hi⟩ :=
          GeneratedBootstrapPotential.actualBlock_eq_weightInput x i.1 s hc hi
        _ = weightInput x b hv i := by cases hrun; rfl
    change ((GeneratedBootstrapPotential.actualBlock x i.1 s).enabled = true ∧
      (GeneratedBootstrapPotential.actualBlock x i.1 s).held = a) ↔
      ((physical x b hv).active i = true ∧ (physical x b hv).held i = a)
    rw [hactual, (ReferenceInitializationMeasurability.weightInput_fields x b hv i).1,
      (ReferenceInitializationMeasurability.weightInput_fields x b hv i).2.1]
  constructor
  · rintro ⟨hb, hp, _, _, _, _⟩
    exact ⟨hb, (hfields hb).2 hp⟩
  · rintro ⟨hb, hcell⟩
    exact ⟨hb, (hfields hb).1 hcell, Set.mem_univ _, Set.mem_univ _,
      GeneratedBlockGuardLaw.actualProcessedProfile_eq_generatedProfile p s ids rewards
        C_star C_h eta b hcompleted hnotStopped e hb,
      GeneratedBlockGuardLaw.actualProcessedTarget_eq_generatedTarget p s ids rewards
        C_star C_h eta b hcompleted hnotStopped e hb⟩

/-- Countable boundary decomposition of the SAME enabled/held event.
Already stopped or informed blocks contribute no cell; their latent draws
remain in the original coordinate space. -/
theorem enabledHeldCell_eq_iUnion (i : Follower p.m) (a : Fin p.K) :
    enabledHeldCell p ids rewards C_star C_h eta s i a =
      ⋃ b : Boundary p, ⋃ hc : b.completed = s.val, ⋃ hn : b.crossing = none,
        ⋃ hi : i ∈ uninformed b,
          activeHeldFutureEvent p s ids rewards C_star C_h eta b hc hn ⟨i, hi⟩ a Set.univ := by
  ext e
  constructor
  · intro he
    let x := referenceInput p ids rewards C_star C_h eta e
    have henabled : (GeneratedBootstrapPotential.actualBlock x i s).enabled = true := he.1
    have hstate := GeneratedProductiveExitBudget.actualBlock_enabled_imp_no_crossing_and_activation_none
      x i s henabled
    have hc := GeneratedBootstrapPotential.completed_eq_of_no_crossing x s.val s.isLt.le hstate.1
    have hi : i ∈ uninformed (run x s.val) := (mem_uninformed _ _).2 hstate.2
    refine Set.mem_iUnion.mpr ⟨run x s.val, Set.mem_iUnion.mpr ⟨hc,
      Set.mem_iUnion.mpr ⟨hstate.1, Set.mem_iUnion.mpr ⟨hi, ?_⟩⟩⟩⟩
    rw [activeHeldFutureEvent_eq_boundary_inter_enabledHeldCell]
    exact ⟨rfl, he⟩
  · intro he
    rcases Set.mem_iUnion.mp he with ⟨b, he⟩
    rcases Set.mem_iUnion.mp he with ⟨hc, he⟩
    rcases Set.mem_iUnion.mp he with ⟨hn, he⟩
    rcases Set.mem_iUnion.mp he with ⟨hi, he⟩
    rw [activeHeldFutureEvent_eq_boundary_inter_enabledHeldCell] at he
    exact he.2

/-- Ambient measurability of the accepted literal enabled/held cell, proved
using the actual countable incoming boundaries. -/
theorem measurableSet_enabledHeldCell (i : Follower p.m) (a : Fin p.K) :
    MeasurableSet (enabledHeldCell p ids rewards C_star C_h eta s i a) := by
  rw [enabledHeldCell_eq_iUnion]
  apply MeasurableSet.iUnion
  intro b
  apply MeasurableSet.iUnion
  intro hc
  apply MeasurableSet.iUnion
  intro hn
  apply MeasurableSet.iUnion
  intro hi
  exact GeneratedBlockGuardLaw.measurableSet_generatedProcessedGuardFutureEvent
    p s ids rewards C_star C_h eta b hc hn
    (GeneratedBlockGuardLaw.focalActiveHeldGuard p b ⟨i, hi⟩ a)
    Set.univ Set.univ MeasurableSet.univ

end ActualCells

section ClockChoice

variable (p : Parameters) (s : Fin (n_boot p)) (ids : IDArray p)
  (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
  (eta : LearningRate)

private theorem literalBlockSupport_eq_positiveRewardBlockSupport (a : Fin p.K) :
    literalBlockSupport p s rewards a =
      GeneratedClockBlockBalance.positiveRewardBlockSupport p s rewards a := by
  apply Subtype.ext
  ext t
  simp only [literalBlockSupport, GeneratedClockBlockBalance.positiveRewardBlockSupport,
    GeneratedClockBlockBalance.positiveRewardSupport, Finset.mem_filter]
  have hD : 0 < (D p : ℝ) := Nat.cast_pos.mpr (D_pos p)
  have hpos : (0 : ℝ) < RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
      (rewards t a) ↔ 0 < (rewards t a).val := by
    rw [RealRewardGridCount.realRewardGridValue, div_pos_iff_of_pos_right hD]
    exact_mod_cast (Iff.rfl : (0 : ℕ) < (rewards t a).val ↔ 0 < (rewards t a).val)
  exact and_congr_right fun _ => hpos.symm

/-- The literal good-choice event equals its actual boundary atom intersected
with the accepted physical clock guard. This also identifies its analysis
measurability without declaring ambient events predictable. -/
theorem goodIDChoiceFutureEvent_eq_boundary_inter_clockGuard
    (b : Boundary p) (hc : b.completed = s.val) (hn : b.crossing = none)
    (i : Incoming p b) (a : Fin p.K) :
    goodIDChoiceFutureEvent p s ids rewards C_star C_h eta b hc hn i a Set.univ =
      {e | GeneratedBlockStartLaw.boundaryAtOriginal p s ids rewards C_star C_h eta e = b} ∩
      {e | GeneratedClockBlockBalance.generatedClockBlockGuard ids rewards C_star C_h eta
        s i.1 a e} := by
  ext e
  constructor
  · intro he
    have hstart := GeneratedClockBlockBalance.calendarBlock_start_lt_stop_local p s
    let t : Fin p.T := ⟨s.val * B_boot p, lt_of_lt_of_le hstart (Nat.min_le_left _ _)⟩
    have ht : t ∈ calendarBlock p s :=
      (mem_calendarBlock_iff p s t).2 ⟨le_rfl, hstart⟩
    have hguard := GeneratedBlockActivationAverage.goodIDChoiceFutureEvent_subset_generatedClockBlockGuard
      p s ids rewards C_star C_h eta b hc hn i a t ht he
    obtain ⟨u, _, hu⟩ := (mem_goodIDChoiceFutureEvent_iff
      p s ids rewards C_star C_h eta b hc hn i a Set.univ e).1 he
    exact ⟨hu.1, hguard⟩
  · rintro ⟨hb, hg⟩
    let x := GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e
    have hrun : run (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e)
        s.val = b := hb
    let hv : b.completed < n_boot p := hc ▸ s.isLt
    change (run x s.val).crossing = none ∧ (∀ h : (run x s.val).completed < n_boot p, _) at hg
    dsimp only [x] at hg
    rw [hrun] at hg
    have hphys := (hg.2 hv).2 i.2
    let u := (physical x b hv).privateId i
    have hu : u ∈ goodIDs p s ids rewards a := by
      rw [mem_goodIDs_iff]
      change IdentificationLocalRowBalance.localBalanceRowPredicate p s
        (literalBlockSupport p s rewards a) (ids u)
      rw [literalBlockSupport_eq_positiveRewardBlockSupport]
      exact hphys.2.2.2.2
    apply (mem_goodIDChoiceFutureEvent_iff p s ids rewards C_star C_h eta b hc hn i a
      Set.univ e).2
    refine ⟨u, hu, hb, ?_, ?_, Set.mem_univ _, ?_, ?_⟩
    · change (((physical x b hv).active i = true ∧ (physical x b hv).held i = a ∧
          ∀ j : Incoming p b, j ≠ i → (physical x b hv).active j = false) ∧
        (physical x b hv).privateId i = u)
      exact ⟨⟨hphys.1, hphys.2.1, hphys.2.2.2.1⟩, rfl⟩
    · exact hphys.2.2.1
    · exact GeneratedBlockGuardLaw.actualProcessedProfile_eq_generatedProfile
        p s ids rewards C_star C_h eta b hc hn e hb
    · exact GeneratedBlockGuardLaw.actualProcessedTarget_eq_generatedTarget
        p s ids rewards C_star C_h eta b hc hn e hb

/-- Actual good choices are measurable in the pre-block ANALYSIS sigma
required by localized clock failure, rather than merely in the ambient sigma. -/
theorem measurableSet_goodIDChoiceFutureEvent_at_blockStart
    (b : Boundary p) (hc : b.completed = s.val) (hn : b.crossing = none)
    (i : Incoming p b) (a : Fin p.K) :
    MeasurableSet[GeneratedBootstrapFiltration.analysisFiltration p
      (GeneratedClockBlockTail.blockClockStart p s - 1)]
      (goodIDChoiceFutureEvent p s ids rewards C_star C_h eta b hc hn i a Set.univ) := by
  rw [goodIDChoiceFutureEvent_eq_boundary_inter_clockGuard]
  have hb : MeasurableSet[boundarySigma p s.val]
      {e | GeneratedBlockStartLaw.boundaryAtOriginal p s ids rewards C_star C_h eta e = b} :=
    (measurableSet_singleton b).preimage
      (GeneratedBootstrapBlockFiltrationRepair.measurable_run p s.val ids rewards C_star C_h eta)
  exact ((boundarySigma_le_analysis_before_block_clock p s) _ hb).inter
    (GeneratedMulticastQuota.generatedClockBlockGuard_measurable ids rewards C_star C_h eta s i.1 a)

end ClockChoice

section ExitMeasurability

variable (p : Parameters) (s : Fin (n_boot p)) (ids : IDArray p)
  (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
  (eta : LearningRate)

/-- Ambient measurability of the actual productive indicator, including
completing and first-crossing blocks. -/
theorem measurable_productiveIndicator (i : Follower p.m) :
    Measurable (fun e : Coordinates p => GeneratedBootstrapGainBudget.productiveIndicator
      (referenceInput p ids rewards C_star C_h eta e) i s) := by
  classical
  let x := referenceInput p ids rewards C_star C_h eta
  let S : Set (Coordinates p) := {e |
    (GeneratedBootstrapGainBudget.blockAt (x e) i s).enabled = true ∧
    (GeneratedBootstrapGainBudget.startupThreshold (x e) : ℝ) ≤
      GeneratedBootstrapGainBudget.rewardSupportCountAt (x e) s
        (GeneratedBootstrapGainBudget.blockAt (x e) i s).held}
  have hsupport (e : Coordinates p) (a : Fin p.K) :
      (GeneratedBootstrapGainBudget.startupThreshold (x e) : ℝ) ≤
        GeneratedBootstrapGainBudget.rewardSupportCountAt (x e) s a ↔
      (BootstrapStartupCostScale.h_boot C_h p : ℝ) ≤ blockSupportCount p s rewards a := by
    rw [GeneratedBlockActivationAverage.blockSupportCount_eq_rewardSupportCount]
    rfl
  have heq : S = ⋃ a : Fin p.K,
      ⋃ (_ : (BootstrapStartupCostScale.h_boot C_h p : ℝ) ≤ blockSupportCount p s rewards a),
        enabledHeldCell p ids rewards C_star C_h eta s i a := by
    ext e
    constructor
    · rintro ⟨he, hs⟩
      exact Set.mem_iUnion.mpr ⟨(GeneratedBootstrapGainBudget.blockAt (x e) i s).held,
        Set.mem_iUnion.mpr ⟨(hsupport e _).1 hs, he, rfl⟩⟩
    · intro he
      obtain ⟨a, he⟩ := Set.mem_iUnion.mp he
      obtain ⟨hs, he, ha⟩ := Set.mem_iUnion.mp he
      exact ⟨he, (hsupport e _).2 (ha ▸ hs)⟩
  have hS : MeasurableSet S := by
    rw [heq]
    exact MeasurableSet.iUnion fun a => MeasurableSet.iUnion fun _ =>
      measurableSet_enabledHeldCell p s ids rewards C_star C_h eta i a
  exact Measurable.ite hS measurable_const measurable_const

/-- Ambient measurability of the actual productive-exit random variable.
The next-boundary guard is read from the actual recursion. -/
theorem measurable_productiveExitIndicator (i : Follower p.m) :
    Measurable (fun e : Coordinates p => GeneratedProductiveExitBudget.productiveExitIndicator
      (referenceInput p ids rewards C_star C_h eta e) i s) := by
  have hprod := measurable_productiveIndicator p s ids rewards C_star C_h eta i
  have hguard := GeneratedProductiveExitBudget.measurable_prelaunchUninformedIndicator
    p (s.val + 1) s.isLt ids rewards C_star C_h eta i
  have hguard' := hguard.mono (boundaryFiltration_le_ambient p (s.val + 1)) le_rfl
  exact hprod.mul (measurable_const.sub hguard')

/-- All events in the requested localized inequality are ambient measurable. -/
theorem measurableSet_productiveExit_intersections (i : Follower p.m) (a : Fin p.K)
    (A : Set (Coordinates p)) (hA : MeasurableSet[boundarySigma p s.val] A) :
    MeasurableSet (enabledHeldCell p ids rewards C_star C_h eta s i a) ∧
    MeasurableSet {e : Coordinates p | GeneratedProductiveExitBudget.productiveExitIndicator
      (referenceInput p ids rewards C_star C_h eta e) i s = 1} ∧
    MeasurableSet (A ∩ enabledHeldCell p ids rewards C_star C_h eta s i a) ∧
    MeasurableSet (A ∩ enabledHeldCell p ids rewards C_star C_h eta s i a ∩
      {e : Coordinates p | GeneratedProductiveExitBudget.productiveExitIndicator
        (referenceInput p ids rewards C_star C_h eta e) i s = 1}) := by
  have hE := measurableSet_enabledHeldCell p s ids rewards C_star C_h eta i a
  have hX := (measurableSet_singleton (1 : ℝ)).preimage
    (measurable_productiveExitIndicator p s ids rewards C_star C_h eta i)
  have hAE := ((boundaryFiltration_le_ambient p s.val) A hA).inter hE
  exact ⟨hE, hX, hAE, hAE.inter hX⟩

end ExitMeasurability

section LocalSuccess

variable (p : Parameters) (s : Fin (n_boot p)) (ids : IDArray p)
  (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
  (eta : LearningRate)
  (rowCompletion : CompleteRow p)
  (scalarCompletion : BootstrapPrivateRoundStreams.PlayerRoundScalars p)

/-- The accepted quota and true-test bridge applied to the literal good
choices. This implication is almost everywhere, as is the accepted clock
conditional-mean input; no physical-run or quota premise is supplied. -/
theorem good_choice_clock_implies_genuine_success_ae
    (b : Boundary p) (hc : b.completed = s.val) (hn : b.crossing = none)
    (i : Incoming p b) (a : Fin p.K)
    (hgood : ids ∈ IdentificationGoodEvent.identificationGoodEvent p)
    (hC_h : (4096 : ℝ) ≤ C_h)
    (hSupport : BootstrapStartupCostScale.h_boot C_h p ≤ blockSupportCount p s rewards a) :
    ∀ᵐ e ∂GeneratedBootstrapRoundLaw.originalLaw p,
      e ∈ goodIDChoiceFutureEvent p s ids rewards C_star C_h eta b hc hn i a Set.univ ∩
        GeneratedClockBlockTail.clockGood ids rewards C_star C_h eta
          rowCompletion scalarCompletion s i.1 →
      e ∈ GeneratedBlockActivationAverage.genuineSuccessEvent p ids rewards C_star C_h eta s i.1 := by
  have hid := ((IdentificationGoodEvent.mem_identificationGoodEvent_iff_components p ids).1 hgood).2.1
  have hSupport' : BootstrapStartupCostScale.h_boot C_h p ≤
      BootstrapDownCountMean.rewardSupportCount p s rewards a := by
    rw [← GeneratedBlockActivationAverage.blockSupportCount_eq_rewardSupportCount]
    exact hSupport
  have hquotaAE := GeneratedMulticastQuota.generated_multicast_quota_boundary_activation_ae
    ids rewards C_star C_h eta rowCompletion scalarCompletion s i.1 a hid hC_h hSupport'
  filter_upwards [hquotaAE] with e hquota
  intro he
  have hchoice := he.1
  rw [goodIDChoiceFutureEvent_eq_boundary_inter_clockGuard] at hchoice
  have hguard := hchoice.2
  rcases hquota hguard he.2 with ⟨hquotaClock, _⟩
  let src := GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e
  let bActual := run src s.val
  have hcross : bActual.crossing = none := hguard.1
  have hprocessed : (run (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e)
      s.val).crossing = none := hcross
  have hcompletedActual : bActual.completed = s.val :=
    GeneratedBootstrapRoundLaw.processed_completed ids rewards C_star C_h eta s e hprocessed
  have hvalidActual : bActual.completed < n_boot p := hcompletedActual ▸ s.isLt
  have hvalidGuard : bActual.completed < n_boot p :=
    GeneratedClockBlockBalance.processedBoundary_valid ids rewards C_star C_h eta s e hprocessed
  have hincoming : i.1 ∈ uninformed bActual := (hguard.2 hvalidGuard).1
  let phys := physical src bActual hvalidActual
  let j : {j // j ∈ phys.uninformed} := ⟨i.1, hincoming⟩
  have hactive : phys.active j = true := (hguard.2 hvalidGuard).2 hincoming |>.1
  have hheld : phys.held j = a := (hguard.2 hvalidGuard).2 hincoming |>.2.1
  have htarget : phys.target = a := (hguard.2 hvalidGuard).2 hincoming |>.2.2.1
  have haccept := BootstrapMulticastAcceptance.generated_multicast_quota_boundary_activation
    ids rewards C_star C_h eta rowCompletion scalarCompletion s e i.1 hprocessed hincoming
  have hactualSuccess := haccept hactive (hheld.trans htarget.symm) (by
    simpa only [GeneratedMulticastQuota.actualMulticastClockSum] using hquotaClock)
  rcases hactualSuccess with ⟨hpending, hactivation, _⟩
  rw [GeneratedBlockActivationAverage.genuineSuccessEvent]
  apply Set.mem_iUnion.mpr
  refine ⟨bActual, rfl, hcross, hcompletedActual, ?_⟩
  change e ∈ GeneratedBlockActivationAverage.fixedBoundaryGenuineSuccessEvent
    p ids rewards C_star C_h eta bActual i.1
  refine ⟨hvalidActual, j, rfl, ?_, ?_⟩
  · simpa only [j, phys, src, bActual, GeneratedBootstrapRoundLaw.input] using hpending
  · simpa only [j, phys, src, bActual, GeneratedBootstrapRoundLaw.input] using hactivation

include rowCompletion scalarCompletion in
/-- Actual success mass on any causal-prefix cell within a fixed processed
incoming boundary. The new prefix-weighted choice calculation is used before
the clock estimate, with the same event `A` throughout. -/
theorem genuine_success_mass_on_causalPrefix_boundary
    (b : Boundary p) (hc : b.completed = s.val) (hn : b.crossing = none)
    (i : Incoming p b) (a : Fin p.K)
    (hgood : ids ∈ IdentificationGoodEvent.identificationGoodEvent p)
    (hC_h : (4096 : ℝ) ≤ C_h)
    (hSupport : BootstrapStartupCostScale.h_boot C_h p ≤ blockSupportCount p s rewards a)
    (A : Set (Coordinates p)) (hA : MeasurableSet[boundarySigma p s.val] A) :
    (1 / (16 * (p.K : ℝ))) *
      (GeneratedBootstrapRoundLaw.originalLaw p).real
        (A ∩ activeHeldFutureEvent p s ids rewards C_star C_h eta b hc hn i a Set.univ) ≤
      (GeneratedBootstrapRoundLaw.originalLaw p).real
        (A ∩ activeHeldFutureEvent p s ids rewards C_star C_h eta b hc hn i a Set.univ ∩
          GeneratedBlockActivationAverage.genuineSuccessEvent p ids rewards C_star C_h eta s i.1) := by
  let mu := GeneratedBootstrapRoundLaw.originalLaw p
  let E := activeHeldFutureEvent p s ids rewards C_star C_h eta b hc hn i a Set.univ
  let Q := goodIDChoiceFutureEvent p s ids rewards C_star C_h eta b hc hn i a Set.univ
  let G := GeneratedClockBlockTail.clockGood ids rewards C_star C_h eta
    rowCompletion scalarCompletion s i.1
  obtain ⟨V, hV, hpre⟩ := boundarySigma_event_is_sourcePrefix_preimage p s A hA
  have hmass : ENNReal.ofReal (3 / (16 * (p.K : ℝ))) * mu (A ∩ E) ≤ mu (A ∩ Q) := by
    rw [← hpre]
    exact goodIDChoiceFutureEvent_prefix_mass_ge p s ids rewards C_star C_h eta
      b hc hn i a V hV hgood
  have hmassReal : (3 / (16 * (p.K : ℝ))) * mu.real (A ∩ E) ≤ mu.real (A ∩ Q) := by
    have h := ENNReal.toReal_mono (measure_ne_top mu (A ∩ Q)) hmass
    simpa only [Measure.real, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity :
      (0 : ℝ) ≤ 3 / (16 * (p.K : ℝ)))] using h
  have hQadapt := measurableSet_goodIDChoiceFutureEvent_at_blockStart
    p s ids rewards C_star C_h eta b hc hn i a
  have hfailure := clockGood_failure_localized_on_causalPrefix p ids rewards C_star C_h eta
    rowCompletion scalarCompletion s i.1 A Q hA hQadapt
  have hfailure' : mu.real (A ∩ Q ∩ Gᶜ) ≤ (1 / 8 : ℝ) * mu.real (A ∩ Q) :=
    hfailure.trans (mul_le_mul_of_nonneg_right
      (GeneratedClockBlockTail.source_clock_failure_exponent_bound p).2.le measureReal_nonneg)
  have hGmeas : MeasurableSet G := GeneratedClockBlockTail.clockGood_measurable
    ids rewards C_star C_h eta rowCompletion scalarCompletion s i.1
  have hpartition := measureReal_inter_add_sdiff (μ := mu) (s := A ∩ Q) hGmeas
    (measure_ne_top mu (A ∩ Q))
  have hclockmass : (7 / 8 : ℝ) * mu.real (A ∩ Q) ≤ mu.real (A ∩ Q ∩ G) := by
    rw [Set.sdiff_eq_compl_inter, Set.inter_comm Gᶜ] at hpartition
    linarith only [hpartition, hfailure']
  have hsuccess := good_choice_clock_implies_genuine_success_ae p s ids rewards C_star C_h eta
    rowCompletion scalarCompletion b hc hn i a hgood hC_h hSupport
  have hsubset : ∀ᵐ e ∂mu, e ∈ A ∩ Q ∩ G → e ∈ A ∩ E ∩
      GeneratedBlockActivationAverage.genuineSuccessEvent p ids rewards C_star C_h eta s i.1 := by
    filter_upwards [hsuccess] with e hs
    rintro ⟨⟨ha, hq⟩, hg⟩
    exact ⟨⟨ha, GeneratedBlockActivationAverage.goodIDChoiceFutureEvent_subset_activeHeldFutureEvent
      p s ids rewards C_star C_h eta b hc hn i a hq⟩, hs ⟨hq, hg⟩⟩
  have hsuccessmass : mu.real (A ∩ Q ∩ G) ≤ mu.real (A ∩ E ∩
      GeneratedBlockActivationAverage.genuineSuccessEvent p ids rewards C_star C_h eta s i.1) :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsubset)
  have hcoeff : (1 / (16 * (p.K : ℝ))) ≤ (7 / 8 : ℝ) * (3 / (16 * (p.K : ℝ))) := by
    have hK : 0 < (p.K : ℝ) := Nat.cast_pos.mpr (K_pos p)
    rw [← mul_div_assoc]
    exact (div_le_div_iff_of_pos_right (by positivity : 0 < 16 * (p.K : ℝ))).2 (by norm_num)
  calc
    _ ≤ ((7 / 8 : ℝ) * (3 / (16 * (p.K : ℝ)))) * mu.real (A ∩ E) :=
      mul_le_mul_of_nonneg_right hcoeff measureReal_nonneg
    _ = (7 / 8 : ℝ) * ((3 / (16 * (p.K : ℝ))) * mu.real (A ∩ E)) := by ring
    _ ≤ (7 / 8 : ℝ) * mu.real (A ∩ Q) :=
      mul_le_mul_of_nonneg_left hmassReal (by norm_num)
    _ ≤ mu.real (A ∩ Q ∩ G) := hclockmass
    _ ≤ _ := hsuccessmass

end LocalSuccess

/-- The actual localized productive-success inequality on EVERY measurable
causal-prefix cell. The shared constants and the original reward table are
unchanged. The proof sums actual countable boundaries and uses no division by
cell mass; null, unreachable, completing, first-crossing, and clipped-final
cells are all included.

Sources: `appendix_b_communication.tex:398-483,586-609` and
`07_public_setup.tex:63-113`. This is an internal probability producer; it
does not assert a conditional mean, tail bound, or manuscript closure. -/
theorem productive_success_on_causalPrefix
    (p : Parameters) (ids : IDArray p)
    (hgood : ids ∈ IdentificationGoodEvent.identificationGoodEvent p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : LearningRate) (hC_h : (4096 : ℝ) ≤ C_h)
    (s : Fin (n_boot p)) (i : Follower p.m) (a : Fin p.K)
    (hSupport : BootstrapStartupCostScale.h_boot C_h p ≤ blockSupportCount p s rewards a)
    (A : Set (Coordinates p)) (hA : MeasurableSet[boundarySigma p s.val] A) :
    (1 / (16 * (p.K : ℝ))) *
      (GeneratedBootstrapRoundLaw.originalLaw p).real
        (A ∩ enabledHeldCell p ids rewards C_star C_h eta s i a) ≤
      (GeneratedBootstrapRoundLaw.originalLaw p).real
        (A ∩ enabledHeldCell p ids rewards C_star C_h eta s i a ∩
          {e | GeneratedProductiveExitBudget.productiveExitIndicator
            (referenceInput p ids rewards C_star C_h eta e) i s = 1}) := by
  classical
  let mu := GeneratedBootstrapRoundLaw.originalLaw p
  let x := referenceInput p ids rewards C_star C_h eta
  let E := enabledHeldCell p ids rewards C_star C_h eta s i a
  let X : Set (Coordinates p) :=
    {e | GeneratedProductiveExitBudget.productiveExitIndicator (x e) i s = 1}
  let f : Coordinates p → Boundary p := fun e => run (x e) s.val
  let fiber : Boundary p → Set (Coordinates p) := fun b => {e | f e = b}
  let e₀ : Coordinates p := Classical.choice (nonempty_of_isProbabilityMeasure mu)
  have hmeas := measurableSet_productiveExit_intersections p s ids rewards C_star C_h eta i a A hA
  have hf : Measurable f :=
    (GeneratedBootstrapBlockFiltrationRepair.measurable_run p s.val ids rewards C_star C_h eta).mono
      (boundaryFiltration_le_ambient p s.val) le_rfl
  have hfiber (b : Boundary p) : MeasurableSet (fiber b) :=
    (measurableSet_singleton b).preimage hf
  have hcoeff : 0 ≤ 1 / (16 * (p.K : ℝ)) := by positivity
  have hboundary (b : Boundary p) :
      ENNReal.ofReal (1 / (16 * (p.K : ℝ))) * mu ((A ∩ E) ∩ fiber b) ≤
        mu ((A ∩ E ∩ X) ∩ fiber b) := by
    by_cases hvalid : b.completed = s.val ∧ b.crossing = none ∧ i ∈ uninformed b
    · obtain ⟨hc, hn, hi⟩ := hvalid
      let j : Incoming p b := ⟨i, hi⟩
      let B := activeHeldFutureEvent p s ids rewards C_star C_h eta b hc hn j a Set.univ
      have hB : B = fiber b ∩ E :=
        activeHeldFutureEvent_eq_boundary_inter_enabledHeldCell p s ids rewards C_star C_h eta
          b hc hn j a
      have hrestrict : (A ∩ E) ∩ fiber b = A ∩ B := by
        rw [hB]
        ext e
        exact ⟨fun he => ⟨he.1.1, he.2, he.1.2⟩,
          fun he => ⟨⟨he.1, he.2.2⟩, he.2.1⟩⟩
      have hsuccess := genuine_success_mass_on_causalPrefix_boundary
        p s ids rewards C_star C_h eta e₀.1 e₀.2.2.1 b hc hn j a hgood hC_h hSupport A hA
      have hsubset : A ∩ B ∩ GeneratedBlockActivationAverage.genuineSuccessEvent
          p ids rewards C_star C_h eta s i ⊆ (A ∩ E ∩ X) ∩ fiber b := by
        rintro e ⟨⟨ha, hb⟩, hs⟩
        have hb' : e ∈ fiber b ∩ E := by rw [← hB]; exact hb
        exact ⟨⟨⟨ha, hb'.2⟩,
          genuineSuccessEvent_implies_productiveExitIndicator_eq_one p ids rewards
            C_star C_h eta s i a hSupport e hb'.2 hs⟩, hb'.1⟩
      have hreal : (1 / (16 * (p.K : ℝ))) * mu.real ((A ∩ E) ∩ fiber b) ≤
          mu.real ((A ∩ E ∩ X) ∩ fiber b) := by
        rw [hrestrict]
        exact hsuccess.trans
          (ENNReal.toReal_mono (measure_ne_top mu _) (measure_mono hsubset))
      apply (ENNReal.toReal_le_toReal
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top mu _))
        (measure_ne_top mu _)).1
      simpa only [Measure.real, ENNReal.toReal_mul, ENNReal.toReal_ofReal hcoeff] using hreal
    · have hempty : (A ∩ E) ∩ fiber b = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro e he
        have henabled : (GeneratedBootstrapPotential.actualBlock (x e) i s).enabled = true :=
          he.1.2.1
        have hstate := GeneratedProductiveExitBudget.actualBlock_enabled_imp_no_crossing_and_activation_none
          (x e) i s henabled
        have hc := GeneratedBootstrapPotential.completed_eq_of_no_crossing
          (x e) s.val s.isLt.le hstate.1
        have hi := (mem_uninformed _ _).2 hstate.2
        have hb : run (x e) s.val = b := he.2
        exact hvalid ⟨hb ▸ hc, hb ▸ hstate.1, hb ▸ hi⟩
      rw [hempty, measure_empty, mul_zero]
      exact bot_le
  have hunion (U : Set (Coordinates p)) : (⋃ b : Boundary p, U ∩ fiber b) = U := by
    ext e
    constructor
    · intro he
      obtain ⟨b, he⟩ := Set.mem_iUnion.mp he
      exact he.1
    · intro he
      exact Set.mem_iUnion.mpr ⟨f e, he, rfl⟩
  have hdisjoint (U : Set (Coordinates p)) :
      Pairwise (fun b c : Boundary p => Disjoint (U ∩ fiber b) (U ∩ fiber c)) := by
    intro b c hbc
    apply Set.disjoint_left.2
    intro e hb hc
    exact hbc (hb.2.symm.trans hc.2)
  have hsum (U : Set (Coordinates p)) (hU : MeasurableSet U) :
      mu U = ∑' b : Boundary p, mu (U ∩ fiber b) := by
    calc
      mu U = mu (⋃ b : Boundary p, U ∩ fiber b) := congrArg mu (hunion U).symm
      _ = _ := measure_iUnion (hdisjoint U) (fun b => hU.inter (hfiber b))
  have htotal : ENNReal.ofReal (1 / (16 * (p.K : ℝ))) * mu (A ∩ E) ≤ mu (A ∩ E ∩ X) := by
    calc
      _ = ENNReal.ofReal (1 / (16 * (p.K : ℝ))) *
          ∑' b : Boundary p, mu ((A ∩ E) ∩ fiber b) := by rw [hsum (A ∩ E) hmeas.2.2.1]
      _ = ∑' b : Boundary p,
          ENNReal.ofReal (1 / (16 * (p.K : ℝ))) * mu ((A ∩ E) ∩ fiber b) :=
        ENNReal.tsum_mul_left.symm
      _ ≤ ∑' b : Boundary p, mu ((A ∩ E ∩ X) ∩ fiber b) := ENNReal.tsum_le_tsum hboundary
      _ = mu (A ∩ E ∩ X) := (hsum (A ∩ E ∩ X) hmeas.2.2.2).symm
  have hreal := ENNReal.toReal_mono (measure_ne_top mu (A ∩ E ∩ X)) htotal
  simpa only [Measure.real, ENNReal.toReal_mul, ENNReal.toReal_ofReal hcoeff] using hreal

end Bandits.Support.GeneratedProductiveSuccessPrefixLaw

end
