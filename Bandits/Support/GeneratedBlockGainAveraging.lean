/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.GeneratedStayBlockTower
public import Bandits.Support.GeneratedBlockChoiceAverages
public import Bandits.Support.GeneratedDownBlockBoundaryMean

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Ring

/-!
# Original-coordinate generated block gain averaging

The physical all-slot block gain dominates the analytical support budget on
the full active-held event. The proof partitions the isolated part of that
event by the original private index and the actual target, then discards the
remaining event using nonnegativity of the physical gain.

Sources: `sources/zip4/manuscript/appendix_b_communication.tex:485-506`
and `sources/zip4/manuscript/07_public_setup.tex:87-109`.
-/

public section

noncomputable section

open MeasureTheory
open scoped Classical BigOperators

namespace Bandits.Support.GeneratedBlockGainAveraging

open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.CompletePublicTable
open Bandits.Support.ReferenceInitializationRun
open Bandits.Support.GeneratedBlockStartLaw
open Bandits.Support.GeneratedBlockGuardLaw
open Bandits.Support.GeneratedBlockDrawLaw
open Bandits.Support.GeneratedBootstrapRoundLaw
open Bandits.Support.GeneratedBootstrapFiltration
open Bandits.Support.GeneratedStayConditionalMean
open Bandits.Support.GeneratedStayBlockTower
open Bandits.Support.GeneratedBlockChoiceAverages
open Bandits.Support.GeneratedDownBlockBoundaryMean

abbrev Parameters := GeneratedStayBlockTower.Parameters
abbrev OriginalCoordinates := GeneratedBlockChoiceAverages.OriginalCoordinates
abbrev Incoming := GeneratedBlockChoiceAverages.Incoming

variable {p : Parameters}

private def physicalGainCell (s : Fin (n_boot p)) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (b : Boundary p) (i : Incoming p b) (a z : Fin p.K)
    (u : Fin (A_id p)) : Set (OriginalCoordinates p) :=
  boundaryEvent ids rewards C_star C_h eta s b ∩
    GeneratedStayBlockTower.blockStartEvent ids rewards C_star C_h eta
      (s := s) i.1 a z u

private theorem actualProfile_eq_descriptorDraws
    (s : Fin (n_boot p)) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (b : Boundary p) (hcompleted : b.completed = s.val)
    (hnotStopped : b.crossing = none)
    (e : OriginalCoordinates p) (draws : PrivateSourceStreams.BlockDrawProfile p)
    (hboundary : boundaryAtOriginal p s ids rewards C_star C_h eta e = b)
    (hdraws : BootstrapPhysicalInput.currentBlockDrawProfile p s b.numerators
      b.weight_ge_one e.2 = draws) :
    actualProcessedProfile p s ids rewards C_star C_h eta b hcompleted
      hnotStopped e = fun j => draws (BootstrapPhysicalInput.sourceFollowerIndex p j.1) := by
  rw [GeneratedBlockChoiceAverages.actualProcessedProfile_eq_generatedProfile
    p s ids rewards C_star C_h eta
    b hcompleted hnotStopped e hboundary]
  funext j
  change (GeneratedBlockGuardLaw.sourceRestrictedProfile p b
    (GeneratedBlockDrawLaw.generatedCurrentBlockProfile p s b e.2)) j =
      draws (BootstrapPhysicalInput.sourceFollowerIndex p j.1)
  change BootstrapPhysicalInput.currentBlockDrawProfile p s b.numerators
    b.weight_ge_one e.2 (BootstrapPhysicalInput.sourceFollowerIndex p j.1) = _
  exact congrFun hdraws (BootstrapPhysicalInput.sourceFollowerIndex p j.1)

private theorem blockStartGuard_iff_processedFields
    (s : Fin (n_boot p)) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (b : Boundary p) (hcompleted : b.completed = s.val)
    (hnotStopped : b.crossing = none) (i : Incoming p b) (a z : Fin p.K)
    (u : Fin (A_id p)) (e : OriginalCoordinates p) (d : Descriptor p)
    (hboundary : boundaryAtOriginal p s ids rewards C_star C_h eta e = b)
    (hdb : d.1 = b)
    (hdraws : BootstrapPhysicalInput.currentBlockDrawProfile p s b.numerators
      b.weight_ge_one e.2 = d.2.1)
    (htarget : actualProcessedTarget p s ids rewards C_star C_h eta b
      hcompleted hnotStopped e = d.2.2.1) :
    GeneratedStayBlockTower.blockStartGuard ids rewards (s := s) i.1 a z u
        (some d) ↔
      actualProcessedProfile p s ids rewards C_star C_h eta b hcompleted
          hnotStopped e ∈ focalIsolationPrivateIdGuard p b i a u ∧
        actualProcessedTarget p s ids rewards C_star C_h eta b hcompleted
          hnotStopped e = z ∧ z ≠ a := by
  have hprofile := actualProfile_eq_descriptorDraws s ids rewards C_star C_h
    eta b hcompleted hnotStopped e d.2.1 hboundary hdraws
  simp only [GeneratedStayBlockTower.blockStartGuard,
    GeneratedStayConditionalMean.inputOfDescriptor,
    GeneratedBlockGuardLaw.focalIsolationPrivateIdGuard,
    GeneratedBlockGuardLaw.focalIsolationGuard, Set.mem_setOf_eq, hdb, htarget]
  constructor
  · rintro ⟨hi, ha, hh, hu, ht, hza, hother⟩
    have hpi := congrFun hprofile i
    refine ⟨⟨⟨?_, ⟨?_, ?_⟩⟩, ?_⟩, ⟨ht, hza⟩⟩
    · rw [hpi]
      exact ha
    · rw [hpi]
      exact hh
    · intro j hji
      have hjiVal : j.1 ≠ i.1 := by
        intro h
        apply hji
        exact Subtype.ext h
      let k : {k // k ∈ ReferenceInitializationRun.uninformed d.1} :=
        ⟨j.1, by simpa [hdb] using j.2⟩
      have hi' : i.1 ∈ ReferenceInitializationRun.uninformed d.1 := by
        simpa [hdb] using hi
      have hki : k ≠ ⟨i.1, hi'⟩ := by
        intro h
        apply hjiVal
        have hkval : j.1 = i.1 := by
          have hv := congrArg
            (fun x : {k // k ∈ ReferenceInitializationRun.uninformed d.1} => x.1) h
          simpa [k] using hv
        exact hkval
      rw [congrFun hprofile j]
      exact hother k hki
    · rw [hpi]
      exact hu
  · rintro ⟨⟨⟨ha, hh, hother⟩, hu⟩, ⟨ht, hza⟩⟩
    have hpi := congrFun hprofile i
    rw [hpi] at ha hh hu
    refine ⟨i.2, ?_⟩
    refine ⟨?_, ?_⟩
    · simpa using ha
    · refine ⟨?_, ?_⟩
      · simpa using hh
      · refine ⟨?_, ?_⟩
        · simpa using hu
        · refine ⟨?_, ?_⟩
          · simpa using ht
          · refine ⟨hza, ?_⟩
            intro k hki
            let j : Incoming p b := ⟨k.1, by simpa [hdb] using k.2⟩
            have hji : j ≠ i := by
              intro h
              apply hki
              have hval : k.1 = i.1 := by
                have hv := congrArg (fun x : Incoming p b => x.1) h
                simpa [j] using hv
              exact Subtype.ext hval
            have hj := hother j hji
            rw [congrFun hprofile j] at hj
            exact hj

private theorem physicalGainCell_iff_supportChoiceCell
    (s : Fin (n_boot p)) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (b : Boundary p) (hcompleted : b.completed = s.val)
    (hnotStopped : b.crossing = none) (i : Incoming p b) (a z : Fin p.K)
    (u : Fin (A_id p)) (e : OriginalCoordinates p) :
    e ∈ physicalGainCell s ids rewards C_star C_h eta b i a z u ↔
      e ∈ supportChoiceCell p s ids rewards C_star C_h eta b hcompleted
        hnotStopped i a u Set.univ ∧
      actualProcessedTarget p s ids rewards C_star C_h eta b hcompleted
        hnotStopped e = z ∧ z ≠ a := by
  constructor
  · rintro ⟨hboundary, hstart⟩
    change boundaryAtOriginal p s ids rewards C_star C_h eta e = b at hboundary
    have hrun : ReferenceInitializationRun.run
        (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e) s.val = b := by
      simpa [GeneratedBlockStartLaw.boundaryAtOriginal,
        GeneratedBlockDrawLaw.generatedBoundary,
        GeneratedBlockDrawLaw.fixedReferenceInput,
        GeneratedBootstrapRoundLaw.input,
        ReferenceInitializationMeasurability.inputOfCoordinates] using hboundary
    have hrunStopped : (ReferenceInitializationRun.run
        (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e) s.val).crossing =
        none := by rw [hrun]; exact hnotStopped
    have hdescriptorNe : GeneratedBootstrapRoundLaw.descriptor p ids rewards
        C_star C_h eta s (GeneratedStayBlockTower.blockStartRound p s) e ≠ none := by
      intro hd
      have hcross := (GeneratedBootstrapRoundLaw.descriptor_eq_none_iff ids rewards C_star C_h eta
        s (GeneratedStayBlockTower.blockStartRound p s) e).mp hd
      exact hcross hrunStopped
    cases hd : GeneratedBootstrapRoundLaw.descriptor p ids rewards C_star C_h eta s
        (GeneratedStayBlockTower.blockStartRound p s) e with
    | none => exact (hdescriptorNe hd).elim
    | some d =>
      have hrec := GeneratedStayConditionalMean.actualDescriptor_reconstructs_source_block
        p ids rewards C_star C_h eta (s := s)
        (t := GeneratedStayBlockTower.blockStartRound p s) e d hd
      dsimp only at hrec
      rcases hrec with ⟨hrunD, hrem, hdrawsRaw, htargetRaw, _, hnext⟩
      have hdb : d.1 = b := hrunD.symm.trans hrun
      have hdraws : BootstrapPhysicalInput.currentBlockDrawProfile p s
          b.numerators b.weight_ge_one e.2 = d.2.1 := by
        rw [hnext, hrun] at hdrawsRaw
        simpa [GeneratedBootstrapRoundLaw.input,
          ReferenceInitializationMeasurability.inputOfCoordinates] using hdrawsRaw
      have htarget : actualProcessedTarget p s ids rewards C_star C_h eta b
          hcompleted hnotStopped e = d.2.2.1 := by
        cases hrun
        simpa [GeneratedBlockGuardLaw.actualProcessedTarget,
          GeneratedBlockDrawLaw.generatedPhysicalBlockTarget,
          GeneratedBlockDrawLaw.fixedReferenceInput, GeneratedBootstrapRoundLaw.input,
          ReferenceInitializationMeasurability.inputOfCoordinates] using htargetRaw
      have hguard : GeneratedStayBlockTower.blockStartGuard ids rewards
          (s := s) i.1 a z u (some d) := by
        simpa [GeneratedStayBlockTower.blockStartEvent, hd] using hstart
      have hfields := (blockStartGuard_iff_processedFields s ids rewards
        C_star C_h eta b hcompleted hnotStopped i a z u e d hboundary hdb
        hdraws htarget).mp hguard
      rcases hfields with ⟨hprofilePrivate, htargetEq, hza⟩
      have hcommon : e ∈ supportChoiceGuardFutureEvent p s ids rewards C_star C_h
          eta b hcompleted hnotStopped i a Set.univ := by
        change e ∈ GeneratedBlockGuardLaw.generatedProcessedGuardFutureEvent p s ids
          rewards C_star C_h eta b hcompleted hnotStopped
          (focalIsolationGuard p b i a) {z | z ≠ a} Set.univ
        have hprofile := hprofilePrivate.1
        have hz : actualProcessedTarget p s ids rewards C_star C_h eta b
            hcompleted hnotStopped e ≠ a := by
          simpa [htargetEq] using hza
        have hprofileEq := GeneratedBlockChoiceAverages.actualProcessedProfile_eq_generatedProfile
          p s ids rewards
          C_star C_h eta b hcompleted hnotStopped e hboundary
        have htargetEq' := GeneratedBlockChoiceAverages.actualProcessedTarget_eq_generatedTarget
          p s ids rewards
          C_star C_h eta b hcompleted hnotStopped e hboundary
        exact ⟨hboundary, hprofile, hz, by simp,
          hprofileEq, htargetEq'⟩
      have hprivate : actualProcessedPrivateID p s ids rewards C_star C_h eta b
          hcompleted hnotStopped i e = u := hprofilePrivate.2
      have hcell := (supportChoiceCell_mem_iff p s ids rewards C_star C_h eta b
        hcompleted hnotStopped i a u Set.univ e).2 ⟨hcommon, hprivate⟩
      exact ⟨hcell, htargetEq, hza⟩
  · rintro ⟨hcell, htarget⟩
    have hfields := (supportChoiceCell_mem_iff p s ids rewards C_star C_h eta b
      hcompleted hnotStopped i a u Set.univ e).mp hcell
    rcases hfields with ⟨hcommon, hprivate⟩
    have hboundary : boundaryAtOriginal p s ids rewards C_star C_h eta e = b :=
      hcommon.1
    have hrun : ReferenceInitializationRun.run
        (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e) s.val = b := by
      simpa [GeneratedBlockStartLaw.boundaryAtOriginal,
        GeneratedBlockDrawLaw.generatedBoundary,
        GeneratedBlockDrawLaw.fixedReferenceInput,
        GeneratedBootstrapRoundLaw.input,
        ReferenceInitializationMeasurability.inputOfCoordinates] using hboundary
    have hrunStopped : (ReferenceInitializationRun.run
        (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e) s.val).crossing =
        none := by rw [hrun]; exact hnotStopped
    have hdescriptorNe : GeneratedBootstrapRoundLaw.descriptor p ids rewards
        C_star C_h eta s (GeneratedStayBlockTower.blockStartRound p s) e ≠ none := by
      intro hd
      have hcross := (GeneratedBootstrapRoundLaw.descriptor_eq_none_iff ids rewards C_star C_h eta
        s (GeneratedStayBlockTower.blockStartRound p s) e).mp hd
      exact hcross hrunStopped
    cases hd : GeneratedBootstrapRoundLaw.descriptor p ids rewards C_star C_h eta s
        (GeneratedStayBlockTower.blockStartRound p s) e with
    | none => exact (hdescriptorNe hd).elim
    | some d =>
      have hrec := GeneratedStayConditionalMean.actualDescriptor_reconstructs_source_block
        p ids rewards C_star C_h eta (s := s)
        (t := GeneratedStayBlockTower.blockStartRound p s) e d hd
      dsimp only at hrec
      rcases hrec with ⟨hrunD, hrem, hdrawsRaw, htargetRaw, _, hnext⟩
      have hdb : d.1 = b := hrunD.symm.trans hrun
      have hdraws : BootstrapPhysicalInput.currentBlockDrawProfile p s
          b.numerators b.weight_ge_one e.2 = d.2.1 := by
        rw [hnext, hrun] at hdrawsRaw
        simpa [GeneratedBootstrapRoundLaw.input,
          ReferenceInitializationMeasurability.inputOfCoordinates] using hdrawsRaw
      have htargetD : actualProcessedTarget p s ids rewards C_star C_h eta b
          hcompleted hnotStopped e = d.2.2.1 := by
        cases hrun
        simpa [GeneratedBlockGuardLaw.actualProcessedTarget,
          GeneratedBlockDrawLaw.generatedPhysicalBlockTarget,
          GeneratedBlockDrawLaw.fixedReferenceInput, GeneratedBootstrapRoundLaw.input,
          ReferenceInitializationMeasurability.inputOfCoordinates] using htargetRaw
      rcases htarget with ⟨htargetEq, htargetNe⟩
      have hnotA : actualProcessedTarget p s ids rewards C_star C_h eta b
          hcompleted hnotStopped e ≠ a := by
        simpa using hcommon.2.2.1
      have hza : z ≠ a := by
        intro heq
        apply hnotA
        rw [htargetEq]
        exact heq
      have hguard : GeneratedStayBlockTower.blockStartGuard ids rewards
          (s := s) i.1 a z u (some d) := by
        apply (blockStartGuard_iff_processedFields s ids rewards C_star C_h eta
          b hcompleted hnotStopped i a z u e d hboundary hdb hdraws htargetD).2
        exact ⟨⟨hcommon.2.1, hprivate⟩, ⟨htargetEq, hza⟩⟩
      have hstart : e ∈ GeneratedStayBlockTower.blockStartEvent ids rewards
          C_star C_h eta (s := s) i.1 a z u := by
        simpa [GeneratedStayBlockTower.blockStartEvent, hd] using hguard
      exact ⟨by simpa [boundaryEvent] using hboundary, hstart⟩

private theorem supportChoiceCell_eq_iUnion_physicalGainCell
    (s : Fin (n_boot p)) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (b : Boundary p) (hcompleted : b.completed = s.val)
    (hnotStopped : b.crossing = none) (i : Incoming p b) (a : Fin p.K)
    (u : Fin (A_id p)) :
    supportChoiceCell p s ids rewards C_star C_h eta b hcompleted hnotStopped
        i a u Set.univ =
      ⋃ z : Fin p.K, physicalGainCell s ids rewards C_star C_h eta b i a z u := by
  classical
  ext e
  constructor
  · intro he
    have hfields := (supportChoiceCell_mem_iff p s ids rewards C_star C_h eta b
      hcompleted hnotStopped i a u Set.univ e).mp he
    let z := actualProcessedTarget p s ids rewards C_star C_h eta b
      hcompleted hnotStopped e
    have hnotA : actualProcessedTarget p s ids rewards C_star C_h eta b
        hcompleted hnotStopped e ≠ a := by
      simpa using hfields.1.2.2.1
    have hza : z ≠ a := by
      intro heq
      apply hnotA
      simpa [z] using heq
    refine Set.mem_iUnion.2 ⟨z, ?_⟩
    exact (physicalGainCell_iff_supportChoiceCell s ids rewards C_star C_h eta
      b hcompleted hnotStopped i a z u e).2 ⟨he, rfl, hza⟩
  · intro he
    rcases Set.mem_iUnion.mp he with ⟨z, hz⟩
    have hiff := (physicalGainCell_iff_supportChoiceCell s ids rewards C_star C_h eta
      b hcompleted hnotStopped i a z u e).1 hz
    exact hiff.1

private theorem physicalGainCell_pairwise_disjoint
    (s : Fin (n_boot p)) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (b : Boundary p) (hcompleted : b.completed = s.val)
    (hnotStopped : b.crossing = none) (i : Incoming p b) (a : Fin p.K) :
    Pairwise (fun q r : Fin (A_id p) × Fin p.K => Disjoint
      (physicalGainCell s ids rewards C_star C_h eta b i a q.2 q.1)
      (physicalGainCell s ids rewards C_star C_h eta b i a r.2 r.1)) := by
  classical
  intro x y hxy
  rcases x with ⟨u, z⟩
  rcases y with ⟨v, w⟩
  apply Set.disjoint_left.2
  intro e hx hy
  have hleft := (physicalGainCell_iff_supportChoiceCell s ids rewards C_star C_h eta
    b hcompleted hnotStopped i a z u e).1 hx
  have hright := (physicalGainCell_iff_supportChoiceCell s ids rewards C_star C_h eta
    b hcompleted hnotStopped i a w v e).1 hy
  rcases hleft with ⟨hcellU, htargetU, _⟩
  rcases hright with ⟨hcellV, htargetV, _⟩
  by_cases huv : u = v
  · subst v
    have hzw : z = w := htargetU.symm.trans htargetV
    apply hxy
    exact Prod.ext rfl hzw
  · have hdis := GeneratedBlockChoiceAverages.supportChoiceCell_disjoint p s ids
      rewards C_star C_h eta b hcompleted hnotStopped i a u v huv Set.univ
    exact Set.disjoint_left.mp hdis hcellU hcellV

private theorem supportChoiceCell_subset_activeHeldEvent
    (s : Fin (n_boot p)) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (b : Boundary p) (hcompleted : b.completed = s.val)
    (hnotStopped : b.crossing = none) (i : Incoming p b) (a : Fin p.K)
    (u : Fin (A_id p)) :
    supportChoiceCell p s ids rewards C_star C_h eta b hcompleted hnotStopped
        i a u Set.univ ⊆
      activeHeldFutureEvent p s ids rewards C_star C_h eta b hcompleted
        hnotStopped i a Set.univ := by
  intro e he
  have hfields := (supportChoiceCell_mem_iff p s ids rewards C_star C_h eta b
    hcompleted hnotStopped i a u Set.univ e).mp he
  change e ∈ GeneratedBlockGuardLaw.generatedProcessedGuardFutureEvent p s ids
    rewards C_star C_h eta b hcompleted hnotStopped
    (focalActiveHeldGuard p b i a) Set.univ Set.univ
  have hcommon := hfields.1
  change e ∈ GeneratedBlockGuardLaw.generatedProcessedGuardFutureEvent p s ids
    rewards C_star C_h eta b hcompleted hnotStopped
    (focalIsolationGuard p b i a) {z | z ≠ a} Set.univ at hcommon
  rcases hcommon with ⟨hb, hprofile, htarget, _, hprofileEq, htargetEq⟩
  change actualProcessedProfile p s ids rewards C_star C_h eta b hcompleted
    hnotStopped e ∈ focalIsolationGuard p b i a at hprofile
  rcases hprofile with ⟨hactive, hheld, _⟩
  exact ⟨hb, ⟨hactive, hheld⟩, trivial, trivial, hprofileEq, htargetEq⟩

private theorem supportCoefficient_eq_blockStartGainCoefficient
    (s : Fin (n_boot p)) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (a : Fin p.K)
    (u : Fin (A_id p)) :
    supportedIDZeroCount p s ids rewards a u / 16 =
      GeneratedStayBlockTower.blockStartGainCoefficient ids rewards (s := s) a u := by
  unfold supportedIDZeroCount GeneratedStayBlockTower.blockStartGainCoefficient
    GeneratedBlockChoiceAverages.roundedSupportChi GeneratedStayBlockTower.sourceChi
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro t ht
  have hD : 0 < (D p : ℝ) := by exact_mod_cast D_pos p
  have hpositive :
      0 < RealRewardGridCount.realRewardGridValue (D p) (D_pos p) (rewards t a) ↔
        0 < (rewards t a).val := by
    rw [RealRewardGridCount.realRewardGridValue]
    rw [div_pos_iff_of_pos_right hD]
    exact_mod_cast (show (0 : ℕ) < (rewards t a).val ↔
      0 < (rewards t a).val by rfl)
  simp [GeneratedBlockChoiceAverages.roundedSupportChi,
    GeneratedStayBlockTower.sourceChi, hpositive]

private theorem physicalGainCell_measurable
    (s : Fin (n_boot p)) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (b : Boundary p) (i : Incoming p b) (a z : Fin p.K)
    (u : Fin (A_id p)) :
    MeasurableSet[analysisFiltration p
      (GeneratedStayBlockTower.blockStartRound p s).val]
      (physicalGainCell s ids rewards C_star C_h eta b i a z u) := by
  exact (GeneratedDownBlockBoundaryMean.measurableSet_boundaryEvent_at_blockStart
    ids rewards C_star C_h eta s b).inter
    (GeneratedStayBlockTower.blockStartEvent_measurable ids rewards C_star C_h eta
      (s := s) i.1 a z u)

private theorem physicalGainCell_measurable_ambient
    (s : Fin (n_boot p)) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (b : Boundary p) (i : Incoming p b) (a z : Fin p.K)
    (u : Fin (A_id p)) :
    MeasurableSet (physicalGainCell s ids rewards C_star C_h eta b i a z u) := by
  exact (MeasurableSpace.le_def.mp
    (GeneratedBootstrapFiltration.analysisFiltration_le p
      (GeneratedStayBlockTower.blockStartRound p s).val)) _
    (physicalGainCell_measurable s ids rewards C_star C_h eta b i a z u)

private theorem physicalGainCell_gain_lower_bound
    (s : Fin (n_boot p)) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (b : Boundary p) (hcompleted : b.completed = s.val)
    (hnotStopped : b.crossing = none) (i : Incoming p b) (a z : Fin p.K)
    (u : Fin (A_id p)) :
    (supportedIDZeroCount p s ids rewards a u / 16) *
        (GeneratedBootstrapRoundLaw.originalLaw p).real
          (physicalGainCell s ids rewards C_star C_h eta b i a z u) ≤
      ∫ e in physicalGainCell s ids rewards C_star C_h eta b i a z u,
        actualBlockGain ids rewards C_star C_h eta (s := s) i.1 e ∂originalLaw p := by
  have hsubset : physicalGainCell s ids rewards C_star C_h eta b i a z u ⊆
      GeneratedStayBlockTower.blockStartEvent ids rewards C_star C_h eta
        (s := s) i.1 a z u := Set.inter_subset_right
  have hTower := GeneratedStayBlockTower.actualBlockGain_setIntegral_ge_on_blockStartEvent
    ids rewards C_star C_h eta (s := s) i.1 a z u
    (physicalGainCell s ids rewards C_star C_h eta b i a z u)
    (physicalGainCell_measurable s ids rewards C_star C_h eta b i a z u) hsubset
  have hcoeff := supportCoefficient_eq_blockStartGainCoefficient s ids rewards a u
  have hboundary :
      (GeneratedBootstrapRoundLaw.originalLaw p).real
        (physicalGainCell s ids rewards C_star C_h eta b i a z u) =
      (originalLaw p).real
        (physicalGainCell s ids rewards C_star C_h eta b i a z u) := rfl
  have hTower' :
      GeneratedStayBlockTower.blockStartGainCoefficient ids rewards (s := s) a u *
        (originalLaw p).real
          (physicalGainCell s ids rewards C_star C_h eta b i a z u) ≤
      ∫ e in physicalGainCell s ids rewards C_star C_h eta b i a z u,
        actualBlockGain ids rewards C_star C_h eta (s := s) i.1 e ∂originalLaw p := by
    simpa [GeneratedStayBlockTower.blockStartGainCoefficient, hboundary] using hTower
  calc
    _ = GeneratedStayBlockTower.blockStartGainCoefficient ids rewards (s := s) a u *
        (originalLaw p).real
          (physicalGainCell s ids rewards C_star C_h eta b i a z u) := by rw [hcoeff]
    _ ≤ _ := hTower'

theorem actualBlockGain_integral_ge_analyticalSupportBudget
    (p : Parameters) (s : Fin (n_boot p)) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (b : Boundary p) (hcompleted : b.completed = s.val)
    (hnotStopped : b.crossing = none) (i : Incoming p b) (a : Fin p.K) :
    ∫ e, analyticalSupportBudget p s ids rewards C_star C_h eta b hcompleted
        hnotStopped i a Set.univ e ∂GeneratedBlockStartLaw.originalCoordinatesLaw p ≤
      ∫ e in activeHeldFutureEvent p s ids rewards C_star C_h eta b hcompleted
          hnotStopped i a Set.univ,
        actualBlockGain ids rewards C_star C_h eta (s := s) i.1 e ∂originalLaw p := by
  classical
  let μ := GeneratedBlockStartLaw.originalCoordinatesLaw p
  let E := activeHeldFutureEvent p s ids rewards C_star C_h eta b hcompleted
    hnotStopped i a Set.univ
  let cells : Fin (A_id p) × Fin p.K → Set (OriginalCoordinates p) := fun q =>
    physicalGainCell s ids rewards C_star C_h eta b i a q.2 q.1
  have hcellMeas : ∀ u : Fin (A_id p),
      MeasurableSet (supportChoiceCell p s ids rewards C_star C_h eta b hcompleted
        hnotStopped i a u Set.univ) := by
    intro u
    exact measurableSet_supportChoiceCell p s ids rewards C_star C_h eta b
      hcompleted hnotStopped i a u Set.univ MeasurableSet.univ
  have hbudgetInt :
      (∫ e, analyticalSupportBudget p s ids rewards C_star C_h eta b hcompleted
        hnotStopped i a Set.univ e ∂μ) =
        ∑ u : Fin (A_id p), (supportedIDZeroCount p s ids rewards a u / 16) *
          μ.real (supportChoiceCell p s ids rewards C_star C_h eta b hcompleted
            hnotStopped i a u Set.univ) := by
    unfold analyticalSupportBudget
    rw [integral_finsetSum (Finset.univ) (fun u hu =>
      (integrable_const _).indicator (hcellMeas u))]
    apply Finset.sum_congr rfl
    intro u hu
    rw [integral_indicator_const _ (hcellMeas u)]
    simp only [smul_eq_mul]
    ring
  have hcellUnion : ∀ u : Fin (A_id p),
      supportChoiceCell p s ids rewards C_star C_h eta b hcompleted hnotStopped
        i a u Set.univ = ⋃ z : Fin p.K, cells (u, z) := by
    intro u
    exact supportChoiceCell_eq_iUnion_physicalGainCell s ids rewards C_star C_h eta
      b hcompleted hnotStopped i a u
  have hpair : Pairwise fun q r => Disjoint (cells q) (cells r) := by
    exact physicalGainCell_pairwise_disjoint s ids rewards C_star C_h eta b
      hcompleted hnotStopped i a
  have hmassUnion : ∀ u : Fin (A_id p),
      μ.real (supportChoiceCell p s ids rewards C_star C_h eta b hcompleted
        hnotStopped i a u Set.univ) =
        ∑ z : Fin p.K, μ.real (cells (u, z)) := by
    intro u
    rw [hcellUnion u]
    have hpairU : Pairwise (fun z w : Fin p.K => Disjoint (cells (u, z)) (cells (u, w))) := by
      intro z w hzw
      apply hpair
      intro h
      exact hzw (congrArg Prod.snd h)
    exact measureReal_iUnion_fintype hpairU
      (fun z => physicalGainCell_measurable_ambient s ids rewards C_star C_h eta b i a z u)
      (fun z => measure_ne_top μ (cells (u, z)))
  have hbudgetSum :
      (∫ e, analyticalSupportBudget p s ids rewards C_star C_h eta b hcompleted
        hnotStopped i a Set.univ e ∂μ) =
        ∑ q : Fin (A_id p) × Fin p.K,
          (supportedIDZeroCount p s ids rewards a q.1 / 16) * μ.real (cells q) := by
    rw [hbudgetInt]
    calc
      _ = ∑ u : Fin (A_id p), (supportedIDZeroCount p s ids rewards a u / 16) *
          (∑ z : Fin p.K, μ.real (cells (u, z))) := by
            apply Finset.sum_congr rfl
            intro u hu
            rw [hmassUnion u]
      _ = ∑ u : Fin (A_id p), ∑ z : Fin p.K,
          (supportedIDZeroCount p s ids rewards a u / 16) * μ.real (cells (u, z)) := by
            apply Finset.sum_congr rfl
            intro u hu
            rw [Finset.mul_sum]
      _ = ∑ q : Fin (A_id p) × Fin p.K,
          (supportedIDZeroCount p s ids rewards a q.1 / 16) * μ.real (cells q) := by
            simpa [cells] using (Fintype.sum_prod_type'
              (fun u : Fin (A_id p) => fun z : Fin p.K =>
                (supportedIDZeroCount p s ids rewards a u / 16) *
                  μ.real (cells (u, z)))).symm
  have hcellLower : ∀ q : Fin (A_id p) × Fin p.K,
      (supportedIDZeroCount p s ids rewards a q.1 / 16) * μ.real (cells q) ≤
        ∫ e in cells q, actualBlockGain ids rewards C_star C_h eta (s := s)
          i.1 e ∂originalLaw p := by
    rintro ⟨u, z⟩
    exact physicalGainCell_gain_lower_bound s ids rewards C_star C_h eta b
      hcompleted hnotStopped i a z u
  have hsumLower := Finset.sum_le_sum (s := Finset.univ) (fun q hq => hcellLower q)
  have hphysicalUnion :
      (∑ q : Fin (A_id p) × Fin p.K,
        ∫ e in cells q, actualBlockGain ids rewards C_star C_h eta (s := s)
          i.1 e ∂originalLaw p) ≤
        ∫ e in E, actualBlockGain ids rewards C_star C_h eta (s := s) i.1 e ∂originalLaw p := by
    have hUnion := integral_iUnion_fintype (s := cells)
      (fun q => physicalGainCell_measurable_ambient s ids rewards C_star C_h eta b i a q.2 q.1)
      hpair
      (fun q => (GeneratedStayBlockTower.integrable_actualBlockGain ids rewards C_star C_h
        eta (s := s) i.1).integrableOn (s := cells q))
    have hsubset : (⋃ q : Fin (A_id p) × Fin p.K, cells q) ⊆ E := by
      intro e he
      rcases Set.mem_iUnion.mp he with ⟨q, hq⟩
      have hcell := (physicalGainCell_iff_supportChoiceCell s ids rewards C_star C_h eta
        b hcompleted hnotStopped i a q.2 q.1 e).1 hq
      exact supportChoiceCell_subset_activeHeldEvent s ids rewards C_star C_h eta b
        hcompleted hnotStopped i a q.1 hcell.1
    have hnonneg : ∀ e, 0 ≤ actualBlockGain ids rewards C_star C_h eta
        (s := s) i.1 e :=
      fun e => (GeneratedStayBlockTower.actualBlockGain_nonneg_le_B ids rewards C_star C_h
        eta (s := s) i.1 e).1
    have hmono := setIntegral_mono_set
      ((GeneratedStayBlockTower.integrable_actualBlockGain ids rewards C_star C_h eta
        (s := s) i.1).integrableOn)
      (Filter.Eventually.of_forall fun e => hnonneg e)
      (Filter.Eventually.of_forall hsubset)
    calc
      _ = ∫ e in (⋃ q : Fin (A_id p) × Fin p.K, cells q),
          actualBlockGain ids rewards C_star C_h eta (s := s) i.1 e ∂originalLaw p := by
            symm
            exact hUnion
      _ ≤ _ := hmono
  exact hbudgetSum ▸ hsumLower.trans hphysicalUnion

theorem actualBlockGain_integral_ge_support_div512
    (p : Parameters) (s : Fin (n_boot p)) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (b : Boundary p) (hcompleted : b.completed = s.val)
    (hnotStopped : b.crossing = none) (i : Incoming p b) (a : Fin p.K)
    (hgood : ids ∈ Bandits.Support.IdentificationGoodEvent.identificationGoodEvent p) :
    blockSupportCount p s rewards a / 512 *
        (GeneratedBlockStartLaw.originalCoordinatesLaw p
          (activeHeldFutureEvent p s ids rewards C_star C_h eta b hcompleted
            hnotStopped i a Set.univ)).toReal ≤
      ∫ e in activeHeldFutureEvent p s ids rewards C_star C_h eta b hcompleted
          hnotStopped i a Set.univ,
        actualBlockGain ids rewards C_star C_h eta (s := s) i.1 e ∂originalLaw p := by
  have hbudget := actualBlockGain_integral_ge_analyticalSupportBudget p s ids rewards
    C_star C_h eta b hcompleted hnotStopped i a
  have hsupport := integral_analyticalSupportBudget_ge_support_div512 p s ids rewards
    C_star C_h eta b hcompleted hnotStopped i a Set.univ MeasurableSet.univ hgood
  exact hsupport.trans hbudget

end Bandits.Support.GeneratedBlockGainAveraging

end
