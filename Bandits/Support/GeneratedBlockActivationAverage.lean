/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.GeneratedMulticastQuota
public import Bandits.Support.GeneratedBlockChoiceAverages
public import Bandits.Support.GeneratedDownBlockBoundaryMean
public import Bandits.Support.GeneratedBlockGuardLaw
public import Bandits.Support.ReferenceInitializationMeasurability

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Actual one-block boundary activation average

This module combines the accepted finite-choice mass with the actual generated
multicast quota at a fixed processed boundary. Its success event records the
true-only pending candidate and the exact next-boundary activation.

Sources: `sources/zip4/manuscript/appendix_b_communication.tex:398-483` and
`sources/zip4/manuscript/07_public_setup.tex:27-38,93-112`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal

open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.GeneratedBootstrapRoundLaw
open Bandits.Support.GeneratedBootstrapFiltration
open Bandits.Support.ReferenceInitializationRun
open Bandits.Support.ActiveRoundActions

namespace Bandits.Support.GeneratedBlockActivationAverage

abbrev Parameters := ConstructorDimensions.Parameters
abbrev OriginalCoordinates := GeneratedBlockStartLaw.OriginalCoordinates
abbrev Incoming := GeneratedBlockChoiceAverages.Incoming

def fixedBoundaryGenuineSuccessEvent (p : Parameters)
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (b : ReferenceInitializationRun.Boundary p) (focal : Follower p.m) :
    Set (OriginalCoordinates p) :=
  {e | ∃ hvalid : b.completed < n_boot p,
    ∃ i : {i // i ∈ (ReferenceInitializationRun.physical
        (ReferenceInitializationMeasurability.inputOfCoordinates p C_star C_h eta rewards
          (ids, e)) b hvalid).uninformed},
      i.1 = focal ∧
        (ReferenceInitializationRun.candidate
          (ReferenceInitializationMeasurability.inputOfCoordinates p C_star C_h eta rewards
            (ids, e)) b hvalid i).pending = true ∧
        (ReferenceInitializationRun.finishBlock
          (ReferenceInitializationMeasurability.inputOfCoordinates p C_star C_h eta rewards
            (ids, e)) b hvalid).activation focal =
          some (BootstrapObservedFollower.nextActivationRound p
            (ReferenceInitializationRun.nextBlock b hvalid))}

/-- The source rounded-support sum is the accepted DOWN support count. -/
theorem blockSupportCount_eq_rewardSupportCount (p : Parameters)
    (s : Fin (n_boot p)) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (a : Fin p.K) :
    GeneratedBlockChoiceAverages.blockSupportCount p s rewards a =
      BootstrapDownCountMean.rewardSupportCount p s rewards a := by
  rw [← GeneratedDownBlockBoundaryMean.roundedPositiveCount_eq_rewardSupportCount
    (p := p) s rewards a]
  unfold GeneratedBlockChoiceAverages.blockSupportCount
    GeneratedBlockChoiceAverages.roundedSupportChi
    GeneratedDownBlockBoundaryMean.roundedPositiveCount
  apply Finset.sum_congr rfl
  intro t ht
  have hD : 0 < (D p : ℝ) := by exact_mod_cast D_pos p
  have hpos :
      (0 : ℝ) < RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
          (rewards t a) ↔ 0 < (rewards t a).val := by
    rw [RealRewardGridCount.realRewardGridValue, div_pos_iff_of_pos_right hD]
    exact_mod_cast (show (0 : ℕ) < (rewards t a).val ↔ 0 < (rewards t a).val by rfl)
  by_cases h : 0 < (rewards t a).val
  · have hne : rewards t a ≠ 0 := by
      intro hz
      simp [hz] at h
    simp [h, hne]
  · have hn : ¬ 0 < RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
        (rewards t a) := by
      intro hvalue
      exact h (hpos.mp hvalue)
    have hz : rewards t a = 0 := Fin.ext (Nat.eq_zero_of_not_pos h)
    simp [h, hn, hz]

/-- Every good-ID choice cell has the active-held event as its ambient event
superset, retaining the same boundary, physical profile, target, and whole
future-row coordinates. -/
theorem goodIDChoiceFutureEvent_subset_activeHeldFutureEvent
    (p : Parameters) (s : Fin (n_boot p)) (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (b : ReferenceInitializationRun.Boundary p) (hcompleted : b.completed = s.val)
    (hnotStopped : b.crossing = none) (i : Incoming p b) (a : Fin p.K) :
    GeneratedBlockChoiceAverages.goodIDChoiceFutureEvent p s ids rewards C_star C_h eta
        b hcompleted hnotStopped i a Set.univ ⊆
      GeneratedBlockChoiceAverages.activeHeldFutureEvent p s ids rewards C_star C_h eta
        b hcompleted hnotStopped i a Set.univ := by
  intro e he
  rcases (GeneratedBlockChoiceAverages.mem_goodIDChoiceFutureEvent_iff_literalBalance
    p s ids rewards C_star C_h eta b hcompleted hnotStopped i a Set.univ e).mp he with
      ⟨u, _, hcell⟩
  change e ∈ GeneratedBlockGuardLaw.generatedProcessedGuardFutureEvent p s ids rewards
    C_star C_h eta b hcompleted hnotStopped
      (GeneratedBlockGuardLaw.focalIsolationPrivateIdGuard p b i a u)
      {z | z = a} Set.univ at hcell
  simp only [GeneratedBlockGuardLaw.generatedProcessedGuardFutureEvent,
    Set.mem_setOf_eq] at hcell
  rcases hcell with ⟨hboundary, hprofile, htarget, hfuture, hprofileEq, htargetEq⟩
  have hprofileIsolation :
      GeneratedBlockGuardLaw.actualProcessedProfile p s ids rewards C_star C_h eta
          b hcompleted hnotStopped e ∈
        GeneratedBlockGuardLaw.focalIsolationGuard p b i a := by
    change
      (GeneratedBlockGuardLaw.actualProcessedProfile p s ids rewards C_star C_h eta
        b hcompleted hnotStopped e ∈
          GeneratedBlockGuardLaw.focalIsolationGuard p b i a) ∧
        (GeneratedBlockGuardLaw.actualProcessedProfile p s ids rewards C_star C_h eta
          b hcompleted hnotStopped e i).2.2 = u at hprofile
    exact hprofile.1
  have hprofileActiveHeld :
      GeneratedBlockGuardLaw.actualProcessedProfile p s ids rewards C_star C_h eta
          b hcompleted hnotStopped e ∈
        GeneratedBlockGuardLaw.focalActiveHeldGuard p b i a := by
    change
      (GeneratedBlockGuardLaw.actualProcessedProfile p s ids rewards C_star C_h eta
        b hcompleted hnotStopped e i).1 = true ∧
      (GeneratedBlockGuardLaw.actualProcessedProfile p s ids rewards C_star C_h eta
        b hcompleted hnotStopped e i).2.1 = a
    exact ⟨hprofileIsolation.1, hprofileIsolation.2.1⟩
  change
    e ∈ GeneratedBlockGuardLaw.generatedProcessedGuardFutureEvent p s ids rewards
      C_star C_h eta b hcompleted hnotStopped
      (GeneratedBlockGuardLaw.focalActiveHeldGuard p b i a) Set.univ Set.univ
  simp only [GeneratedBlockGuardLaw.generatedProcessedGuardFutureEvent,
    Set.mem_setOf_eq]
  exact ⟨hboundary, hprofileActiveHeld, Set.mem_univ _, Set.mem_univ _,
    hprofileEq, htargetEq⟩

private def goodChoiceDescriptorPredicate (p : Parameters)
    (s : Fin (n_boot p)) (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (b : ReferenceInitializationRun.Boundary p)
    (i : Incoming p b) (a : Fin p.K) :
    Option (GeneratedBootstrapRoundLaw.Descriptor p) → Prop
  | none => False
  | some (boundary, (profile, (target, _state))) =>
      boundary = b ∧ target = a ∧
        ∃ u, ids ∈ IdentificationLocalRowBalance.localBalanceRowEvent p s
            (GeneratedBlockChoiceAverages.literalBlockSupport p s rewards a) u ∧
          GeneratedBlockGuardLaw.sourceRestrictedProfile p b profile ∈
            GeneratedBlockGuardLaw.focalIsolationPrivateIdGuard p b i a u

/-- The good-ID event is read from the original block descriptor: its actual
boundary, labelled private profile and target, before the future row begins. -/
private theorem goodIDChoiceFutureEvent_eq_descriptorPreimage
    (p : Parameters) (s : Fin (n_boot p)) (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (b : ReferenceInitializationRun.Boundary p) (hcompleted : b.completed = s.val)
    (hnotStopped : b.crossing = none) (i : Incoming p b) (a : Fin p.K)
    (t : Fin p.T) (ht : t ∈ BootstrapDimensions.calendarBlock p s) :
    GeneratedBlockChoiceAverages.goodIDChoiceFutureEvent p s ids rewards C_star C_h eta
      b hcompleted hnotStopped i a Set.univ =
    (GeneratedBootstrapRoundLaw.descriptor p ids rewards C_star C_h eta s t) ⁻¹'
      {d | goodChoiceDescriptorPredicate p s ids rewards b i a d} := by
  classical
  ext e
  constructor
  · intro he
    rcases (GeneratedBlockChoiceAverages.mem_goodIDChoiceFutureEvent_iff_literalBalance
      p s ids rewards C_star C_h eta b hcompleted hnotStopped i a Set.univ e).mp he with
      ⟨u, hu, hcell⟩
    change e ∈ GeneratedBlockGuardLaw.generatedProcessedGuardFutureEvent p s ids rewards
      C_star C_h eta b hcompleted hnotStopped
        (GeneratedBlockGuardLaw.focalIsolationPrivateIdGuard p b i a u)
        {z | z = a} Set.univ at hcell
    simp only [GeneratedBlockGuardLaw.generatedProcessedGuardFutureEvent,
      Set.mem_setOf_eq] at hcell
    rcases hcell with ⟨hboundary, hprofile, htarget, _, _, _⟩
    have hrun : ReferenceInitializationRun.run
        (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e) s.val = b := by
      simpa [GeneratedBlockStartLaw.boundaryAtOriginal,
        GeneratedBlockDrawLaw.generatedBoundary, GeneratedBlockDrawLaw.fixedReferenceInput,
        GeneratedBootstrapRoundLaw.input,
        ReferenceInitializationMeasurability.inputOfCoordinates] using hboundary
    let hvalid : b.completed < n_boot p := by
      rw [hcompleted]
      exact s.isLt
    have hnext : ReferenceInitializationRun.nextBlock b hvalid = s := by
      apply Fin.ext
      exact hcompleted
    have hrunValid : (ReferenceInitializationRun.run
        (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e) s.val).completed <
        n_boot p := by
      simpa [hrun] using hvalid
    have hrunNext : ReferenceInitializationRun.nextBlock
        (ReferenceInitializationRun.run
          (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e) s.val)
        hrunValid = s := by
      simpa [hrun] using hnext
    let profile := BootstrapPhysicalInput.currentBlockDrawProfile p
      (ReferenceInitializationRun.nextBlock
        (ReferenceInitializationRun.run
          (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e) s.val) hrunValid)
      (ReferenceInitializationRun.run
        (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e) s.val).numerators
      (ReferenceInitializationRun.run
        (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e) s.val).weight_ge_one
      (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e).coordinates
    let target := (ReferenceInitializationRun.physical
      (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e)
      (ReferenceInitializationRun.run
        (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e) s.val) hrunValid).target
    let state := BootstrapPhysicalBlock.run
      (ReferenceInitializationRun.physical
        (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e)
        (ReferenceInitializationRun.run
          (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e) s.val) hrunValid) t.val
    have hdesc : GeneratedBootstrapRoundLaw.descriptor p ids rewards C_star C_h eta s t e =
        some (b, (profile, (target, state))) := by
      apply (GeneratedBootstrapRoundLaw.descriptor_eq_some_iff ids rewards C_star C_h eta
        s t e b profile target state).2
      refine ⟨hrun, ?_, ⟨hrunValid, rfl, rfl, rfl⟩⟩
      · rw [hrun]
        exact hnotStopped
    have hprofileEq := GeneratedBlockGuardLaw.actualProcessedProfile_eq_generatedProfile
      p s ids rewards C_star C_h eta b hcompleted hnotStopped e hboundary
    have htargetEq := GeneratedBlockGuardLaw.actualProcessedTarget_eq_generatedTarget
      p s ids rewards C_star C_h eta b hcompleted hnotStopped e hboundary
    have hprofileDesc : GeneratedBlockDrawLaw.generatedCurrentBlockProfile p s b e.2 =
        profile := by
      cases hrun
      dsimp [profile, GeneratedBlockDrawLaw.generatedCurrentBlockProfile,
        BootstrapPhysicalInput.currentBlockDrawProfile]
      rw [hrunNext]
      rfl
    have htargetDesc : GeneratedBlockDrawLaw.generatedCurrentTarget p s e.2 = target := by
      cases hrun
      dsimp [target, GeneratedBlockDrawLaw.generatedCurrentTarget,
        BootstrapPhysicalInput.targetArmMap, BootstrapPhysicalInput.coordinatorTargetScalarAt,
        ReferenceInitializationRun.physical, BootstrapPhysicalInput.blockInput]
      rw [hrunNext]
      rfl
    have hprofile' : GeneratedBlockGuardLaw.sourceRestrictedProfile p b profile ∈
        GeneratedBlockGuardLaw.focalIsolationPrivateIdGuard p b i a u := by
      rw [← hprofileDesc]
      rw [← hprofileEq]
      exact hprofile
    have htarget' : target = a := by
      have htargetValue : GeneratedBlockGuardLaw.actualProcessedTarget p s ids rewards
          C_star C_h eta b hcompleted hnotStopped e = a := by
        simpa using htarget
      rw [htargetEq] at htargetValue
      rw [htargetDesc] at htargetValue
      exact htargetValue
    change goodChoiceDescriptorPredicate p s ids rewards b i a
      (GeneratedBootstrapRoundLaw.descriptor p ids rewards C_star C_h eta s t e)
    rw [hdesc]
    exact ⟨rfl, htarget', u, hu, hprofile'⟩
  · intro he
    change goodChoiceDescriptorPredicate p s ids rewards b i a
      (GeneratedBootstrapRoundLaw.descriptor p ids rewards C_star C_h eta s t e) at he
    cases hd : GeneratedBootstrapRoundLaw.descriptor p ids rewards C_star C_h eta s t e with
    | none => simp [goodChoiceDescriptorPredicate, hd] at he
    | some value =>
      cases value with
      | mk boundary rest =>
        cases rest with
        | mk profile rest =>
          cases rest with
          | mk target state =>
            simp only [goodChoiceDescriptorPredicate, hd] at he
            rcases he with ⟨hboundaryValue, htargetValue, u, hu, hprofileValue⟩
            have hfields := (GeneratedBootstrapRoundLaw.descriptor_eq_some_iff
              ids rewards C_star C_h eta s t e boundary profile target state).mp hd
            rcases hfields with ⟨hrun, hcross, ⟨hdescValid, hdescProfile, hdescTarget, _⟩⟩
            subst boundary
            have hrunB : ReferenceInitializationRun.run
                (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e) s.val = b := hrun
            have hb : GeneratedBlockStartLaw.boundaryAtOriginal p s ids rewards C_star C_h eta e = b := by
              simpa [GeneratedBlockStartLaw.boundaryAtOriginal,
                GeneratedBlockDrawLaw.generatedBoundary, GeneratedBlockDrawLaw.fixedReferenceInput,
                GeneratedBootstrapRoundLaw.input,
                ReferenceInitializationMeasurability.inputOfCoordinates] using hrunB
            have hvalid : b.completed < n_boot p := by
              rw [hcompleted]
              exact s.isLt
            have hnext : ReferenceInitializationRun.nextBlock b hvalid = s := by
              apply Fin.ext
              exact hcompleted
            have hprofileEq : GeneratedBlockDrawLaw.generatedCurrentBlockProfile p s b e.2 =
                profile := by
              cases hrunB
              have hnextActual := GeneratedBootstrapRoundLaw.processed_nextBlock
                ids rewards C_star C_h eta s e hcross hdescValid
              have hdescProfile' := hdescProfile
              rw [hnextActual] at hdescProfile'
              simpa [GeneratedBlockDrawLaw.generatedCurrentBlockProfile,
                BootstrapPhysicalInput.currentBlockDrawProfile,
                ReferenceInitializationMeasurability.inputOfCoordinates,
                GeneratedBootstrapRoundLaw.input] using hdescProfile'
            have hgeneratedTarget : GeneratedBlockDrawLaw.generatedCurrentTarget p s e.2 =
                target := by
              cases hrunB
              have hnextActual := GeneratedBootstrapRoundLaw.processed_nextBlock
                ids rewards C_star C_h eta s e hcross hdescValid
              have hdescTarget' := hdescTarget
              dsimp [ReferenceInitializationRun.physical, BootstrapPhysicalInput.blockInput,
                BootstrapPhysicalInput.targetArmMap,
                BootstrapPhysicalInput.coordinatorTargetScalarAt] at hdescTarget'
              rw [hnextActual] at hdescTarget'
              simpa [GeneratedBlockDrawLaw.generatedCurrentTarget,
                ReferenceInitializationMeasurability.inputOfCoordinates,
                GeneratedBootstrapRoundLaw.input] using hdescTarget'
            have hprofileActual := GeneratedBlockGuardLaw.actualProcessedProfile_eq_generatedProfile
              p s ids rewards C_star C_h eta b hcompleted hnotStopped e hb
            have htargetActual := GeneratedBlockGuardLaw.actualProcessedTarget_eq_generatedTarget
              p s ids rewards C_star C_h eta b hcompleted hnotStopped e hb
            have hprofileGuard :
                GeneratedBlockGuardLaw.actualProcessedProfile p s ids rewards C_star C_h eta
                    b hcompleted hnotStopped e ∈
                  GeneratedBlockGuardLaw.focalIsolationPrivateIdGuard p b i a u := by
              rw [hprofileActual, hprofileEq]
              exact hprofileValue
            have htargetGuard :
                GeneratedBlockGuardLaw.actualProcessedTarget p s ids rewards C_star C_h eta
                    b hcompleted hnotStopped e ∈ {z | z = a} := by
              rw [htargetActual]
              rw [hgeneratedTarget]
              simpa [htargetValue]
            have hcell : e ∈ GeneratedBlockChoiceAverages.goodIDChoiceCell p s ids rewards
                C_star C_h eta b hcompleted hnotStopped i a u Set.univ := by
              change e ∈ GeneratedBlockGuardLaw.generatedProcessedGuardFutureEvent p s ids rewards
                C_star C_h eta b hcompleted hnotStopped
                  (GeneratedBlockGuardLaw.focalIsolationPrivateIdGuard p b i a u)
                  {z | z = a} Set.univ
              simp only [GeneratedBlockGuardLaw.generatedProcessedGuardFutureEvent,
                Set.mem_setOf_eq]
              exact ⟨hb, hprofileGuard, htargetGuard, Set.mem_univ _, hprofileActual,
                htargetActual⟩
            exact (GeneratedBlockChoiceAverages.mem_goodIDChoiceFutureEvent_iff_literalBalance
              p s ids rewards C_star C_h eta b hcompleted hnotStopped i a Set.univ e).2
              ⟨u, hu, hcell⟩

private theorem measurableSet_goodIDChoiceFutureEvent_at_blockStart
    (p : Parameters) (s : Fin (n_boot p)) (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (b : ReferenceInitializationRun.Boundary p) (hcompleted : b.completed = s.val)
    (hnotStopped : b.crossing = none) (i : Incoming p b) (a : Fin p.K) :
    MeasurableSet[GeneratedBootstrapFiltration.analysisFiltration p
      (GeneratedClockBlockTail.blockClockStart p s - 1)]
      (GeneratedBlockChoiceAverages.goodIDChoiceFutureEvent p s ids rewards C_star C_h eta
        b hcompleted hnotStopped i a Set.univ) := by
  have hstartStop := GeneratedClockBlockBalance.calendarBlock_start_lt_stop_local p s
  have hstartT : s.val * B_boot p < p.T :=
    lt_of_lt_of_le hstartStop (Nat.min_le_left _ _)
  let t : Fin p.T := ⟨s.val * B_boot p, hstartT⟩
  have ht : t ∈ BootstrapDimensions.calendarBlock p s :=
    (BootstrapDimensions.mem_calendarBlock_iff p s t).mpr
      ⟨le_rfl, hstartStop⟩
  have hdesc := GeneratedBootstrapFiltration.measurable_descriptor p ids rewards C_star C_h eta
    s t ht
  have hpredicate : MeasurableSet
      {d : Option (GeneratedBootstrapRoundLaw.Descriptor p) |
        goodChoiceDescriptorPredicate p s ids rewards b i a d} :=
    MeasurableSet.of_discrete
  have hpre : MeasurableSet[GeneratedBootstrapFiltration.analysisFiltration p t.val]
      ((GeneratedBootstrapRoundLaw.descriptor p ids rewards C_star C_h eta s t) ⁻¹'
        {d | goodChoiceDescriptorPredicate p s ids rewards b i a d}) := hdesc hpredicate
  rw [goodIDChoiceFutureEvent_eq_descriptorPreimage p s ids rewards C_star C_h eta b
    hcompleted hnotStopped i a t ht]
  change MeasurableSet[GeneratedBootstrapFiltration.analysisFiltration p
    (s.val * B_boot p)] _
  simpa [GeneratedClockBlockTail.blockClockStart, t] using hpre

private theorem generatedClockBlockGuard_iff_descriptorGuardPredicate_local
    (p : Parameters) (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (s : Fin (n_boot p))
    (focal : Follower p.m) (a : Fin p.K) (t : Fin p.T)
    (ht : t ∈ BootstrapDimensions.calendarBlock p s) (e : OriginalCoordinates p) :
    GeneratedClockBlockBalance.generatedClockBlockGuard ids rewards C_star C_h eta s focal a e ↔
      GeneratedMulticastQuota.descriptorGuardPredicate ids rewards s focal a
        (GeneratedBootstrapRoundLaw.descriptor p ids rewards C_star C_h eta s t e) := by
  classical
  let src := GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e
  let boundary := ReferenceInitializationRun.run src s.val
  by_cases hcross : boundary.crossing = none
  · have hvalid := GeneratedClockBlockBalance.processedBoundary_valid ids rewards C_star C_h eta s e
      (by simpa [src, boundary] using hcross)
    let phys := ReferenceInitializationRun.physical src boundary hvalid
    let profile := BootstrapPhysicalInput.currentBlockDrawProfile p s boundary.numerators
      boundary.weight_ge_one src.coordinates
    let st := BootstrapPhysicalBlock.run phys t.val
    have hnext : ReferenceInitializationRun.nextBlock boundary hvalid = s := by
      exact GeneratedBootstrapRoundLaw.processed_nextBlock ids rewards C_star C_h eta s e
        (by simpa [src, boundary] using hcross) hvalid
    have hdesc : GeneratedBootstrapRoundLaw.descriptor p ids rewards C_star C_h eta s t e =
        some (boundary, (profile, (phys.target, st))) := by
      apply (GeneratedBootstrapRoundLaw.descriptor_eq_some_iff ids rewards C_star C_h eta
        s t e boundary profile phys.target st).2
      refine ⟨rfl, ?_, ⟨hvalid, ?_, rfl, rfl⟩⟩
      · simpa [boundary] using hcross
      · rw [hnext]
    rw [hdesc]
    simp [GeneratedMulticastQuota.descriptorGuardPredicate,
      GeneratedClockBlockBalance.generatedClockBlockGuard, src, boundary, hvalid, phys,
      profile, st, hnext, hcross, ReferenceInitializationRun.physical,
      BootstrapPhysicalInput.blockInput, BootstrapPhysicalInput.activityMap,
      BootstrapPhysicalInput.heldMap, BootstrapPhysicalInput.privateIDMap,
      BootstrapPhysicalInput.currentBlockDrawProfileMap, Subtype.ext_iff]
  · have hcross' : boundary.crossing ≠ none := hcross
    have hnone : GeneratedBootstrapRoundLaw.descriptor p ids rewards C_star C_h eta s t e = none :=
      (GeneratedBootstrapRoundLaw.descriptor_eq_none_iff ids rewards C_star C_h eta s t e).2
        (by simpa [src, boundary] using hcross')
    rw [hnone]
    constructor
    · intro hguard
      exact (hcross (by simpa [src, boundary] using hguard.1)).elim
    · intro hfalse
      exact hfalse.elim

private theorem literalBlockSupport_eq_positiveRewardBlockSupport
    (p : Parameters) (s : Fin (n_boot p))
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (a : Fin p.K) :
    GeneratedBlockChoiceAverages.literalBlockSupport p s rewards a =
      GeneratedClockBlockBalance.positiveRewardBlockSupport p s rewards a := by
  apply Subtype.ext
  ext t
  simp only [GeneratedBlockChoiceAverages.literalBlockSupport,
    GeneratedClockBlockBalance.positiveRewardBlockSupport,
    GeneratedClockBlockBalance.positiveRewardSupport, Finset.mem_filter]
  have hD : 0 < (D p : ℝ) := by exact_mod_cast D_pos p
  have hpos :
      (0 : ℝ) < RealRewardGridCount.realRewardGridValue (D p) (D_pos p) (rewards t a) ↔
        0 < (rewards t a).val := by
    rw [RealRewardGridCount.realRewardGridValue, div_pos_iff_of_pos_right hD]
    exact_mod_cast (show (0 : ℕ) < (rewards t a).val ↔ 0 < (rewards t a).val by rfl)
  exact and_congr_right fun _ => hpos.symm

/-- The exact choice event is contained in the existing runtime guard. The
private ID in the guard is the same raw profile ID that witnesses its literal
local-balance row event. -/
theorem goodIDChoiceFutureEvent_subset_generatedClockBlockGuard
    (p : Parameters) (s : Fin (n_boot p)) (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (b : ReferenceInitializationRun.Boundary p) (hcompleted : b.completed = s.val)
    (hnotStopped : b.crossing = none) (i : Incoming p b) (a : Fin p.K)
    (t : Fin p.T) (ht : t ∈ BootstrapDimensions.calendarBlock p s) :
    GeneratedBlockChoiceAverages.goodIDChoiceFutureEvent p s ids rewards C_star C_h eta
      b hcompleted hnotStopped i a Set.univ ⊆
    {e | GeneratedClockBlockBalance.generatedClockBlockGuard ids rewards C_star C_h eta s i.1 a e} := by
  classical
  intro e he
  have hedesc : goodChoiceDescriptorPredicate p s ids rewards b i a
      (GeneratedBootstrapRoundLaw.descriptor p ids rewards C_star C_h eta s t e) := by
    rw [goodIDChoiceFutureEvent_eq_descriptorPreimage p s ids rewards C_star C_h eta b
      hcompleted hnotStopped i a t ht] at he
    change goodChoiceDescriptorPredicate p s ids rewards b i a
      (GeneratedBootstrapRoundLaw.descriptor p ids rewards C_star C_h eta s t e)
    exact he
  have hdescriptorGuard : GeneratedMulticastQuota.descriptorGuardPredicate ids rewards s i.1 a
      (GeneratedBootstrapRoundLaw.descriptor p ids rewards C_star C_h eta s t e) := by
    cases hd : GeneratedBootstrapRoundLaw.descriptor p ids rewards C_star C_h eta s t e with
    | none => simp [goodChoiceDescriptorPredicate, hd] at hedesc
    | some value =>
      cases value with
      | mk boundary rest =>
        cases rest with
        | mk profile rest =>
          cases rest with
          | mk target state =>
            simp only [goodChoiceDescriptorPredicate, hd] at hedesc
            rcases hedesc with ⟨hboundary, htarget, u, hu, hprofile⟩
            have hrow : IdentificationLocalRowBalance.localBalanceRowPredicate p s
                (GeneratedBlockChoiceAverages.literalBlockSupport p s rewards a) (ids u) := by
              simpa [IdentificationLocalRowBalance.localBalanceRowEvent] using hu
            have hprofileFields :
                (GeneratedBlockGuardLaw.sourceRestrictedProfile p b profile i).1 = true ∧
                (GeneratedBlockGuardLaw.sourceRestrictedProfile p b profile i).2.1 = a ∧
                (∀ k : Incoming p b, k ≠ i →
                  (GeneratedBlockGuardLaw.sourceRestrictedProfile p b profile k).1 = false) ∧
                (GeneratedBlockGuardLaw.sourceRestrictedProfile p b profile i).2.2 = u := by
              subst boundary
              change
                (GeneratedBlockGuardLaw.sourceRestrictedProfile p b profile ∈
                    GeneratedBlockGuardLaw.focalIsolationGuard p b i a) ∧
                  (GeneratedBlockGuardLaw.sourceRestrictedProfile p b profile i).2.2 = u at hprofile
              rcases hprofile with ⟨hguard, hid⟩
              change
                (GeneratedBlockGuardLaw.sourceRestrictedProfile p b profile i).1 = true ∧
                (GeneratedBlockGuardLaw.sourceRestrictedProfile p b profile i).2.1 = a ∧
                (∀ k : Incoming p b, k ≠ i →
                  (GeneratedBlockGuardLaw.sourceRestrictedProfile p b profile k).1 = false) at hguard
              exact ⟨hguard.1, hguard.2.1, hguard.2.2, hid⟩
            have hrowPositive : IdentificationLocalRowBalance.localBalanceRowPredicate p s
                (GeneratedClockBlockBalance.positiveRewardBlockSupport p s rewards a) (ids u) := by
              rw [← literalBlockSupport_eq_positiveRewardBlockSupport p s rewards a]
              exact hrow
            have hguardDesc : GeneratedMulticastQuota.descriptorGuardPredicate ids rewards s i.1 a
                (some (boundary, (profile, (target, state)))) := by
              change boundary.crossing = none ∧ i.1 ∈ ReferenceInitializationRun.uninformed boundary ∧
                ∀ hm : i.1 ∈ ReferenceInitializationRun.uninformed boundary,
                  let j : {j // j ∈ ReferenceInitializationRun.uninformed boundary} := ⟨i.1, hm⟩
                  let draw := profile (BootstrapPhysicalInput.sourceFollowerIndex p j.1)
                  draw.1 = true ∧ draw.2.1 = a ∧ target = a ∧
                    (∀ k : {j // j ∈ ReferenceInitializationRun.uninformed boundary},
                      k ≠ j → (profile (BootstrapPhysicalInput.sourceFollowerIndex p k.1)).1 = false) ∧
                    IdentificationLocalRowBalance.localBalanceRowPredicate p s
                      (GeneratedClockBlockBalance.positiveRewardBlockSupport p s rewards a)
                      (ids draw.2.2)
              subst boundary
              refine ⟨hnotStopped, i.2, ?_⟩
              intro hm
              let j : {j // j ∈ ReferenceInitializationRun.uninformed b} := ⟨i.1, hm⟩
              have hj : j = i := Subtype.ext rfl
              have hprivate : (profile (BootstrapPhysicalInput.sourceFollowerIndex p i.1)).2.2 = u := by
                simpa [GeneratedBlockGuardLaw.sourceRestrictedProfile] using hprofileFields.2.2.2
              refine ⟨?_, ?_, ?_, ?_, ?_⟩
              · simpa [j, hj, GeneratedBlockGuardLaw.sourceRestrictedProfile] using hprofileFields.1
              · simpa [j, hj, GeneratedBlockGuardLaw.sourceRestrictedProfile] using hprofileFields.2.1
              · exact htarget
              · intro k hk
                have hkIncoming : (⟨k.1, k.2⟩ : Incoming p b) ≠ i := by
                  intro hEq
                  apply hk
                  apply Subtype.ext
                  simpa [j] using congrArg Subtype.val hEq
                have hfalse := hprofileFields.2.2.1 ⟨k.1, k.2⟩ hkIncoming
                simpa [GeneratedBlockGuardLaw.sourceRestrictedProfile] using hfalse
              · have hdrawBalance : IdentificationLocalRowBalance.localBalanceRowPredicate p s
                    (GeneratedClockBlockBalance.positiveRewardBlockSupport p s rewards a)
                    (ids ((profile (BootstrapPhysicalInput.sourceFollowerIndex p i.1)).2.2)) := by
                  rw [hprivate]
                  exact hrowPositive
                simpa [j, hj] using hdrawBalance
            simpa [hd] using hguardDesc
  exact (generatedClockBlockGuard_iff_descriptorGuardPredicate_local p ids rewards C_star C_h
    eta s i.1 a t ht e).2 hdescriptorGuard

/-- The actual true-row candidate is pending at the end of opportunity `s`,
and `finishBlock` activates the focal follower at the exact next boundary.
The witness `hvalid` remains indexed by the actual run boundary. -/
def genuineSuccessEvent (p : Parameters)
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (s : Fin (n_boot p)) (focal : Follower p.m) : Set (OriginalCoordinates p) :=
  ⋃ b : ReferenceInitializationRun.Boundary p,
    {e | ReferenceInitializationRun.run
        (ReferenceInitializationMeasurability.inputOfCoordinates p C_star C_h eta rewards
          (ids, e)) s.val = b ∧
      b.crossing = none ∧ b.completed = s.val ∧
      e ∈ fixedBoundaryGenuineSuccessEvent p ids rewards C_star C_h eta b focal}

/-- The actual success event is measurable in the original coordinate space. -/
theorem measurableSet_genuineSuccessEvent (p : Parameters)
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (s : Fin (n_boot p)) (focal : Follower p.m) :
    MeasurableSet (genuineSuccessEvent p ids rewards C_star C_h eta s focal) := by
  classical
  have hcoordinates : Measurable
      ((fun e : OriginalCoordinates p => (ids, e)) :
        OriginalCoordinates p → ReferenceInitializationMeasurability.InputCoordinates p) :=
    measurable_const.prodMk measurable_id
  have hrun : Measurable (fun e : OriginalCoordinates p =>
      ReferenceInitializationRun.run
        (ReferenceInitializationMeasurability.inputOfCoordinates p C_star C_h eta rewards
          (ids, e)) s.val) :=
    by
      exact (ReferenceInitializationMeasurability.measurable_run
        p C_star C_h eta rewards s.val).comp hcoordinates
  rw [genuineSuccessEvent]
  apply MeasurableSet.iUnion
  intro b
  have hboundary : MeasurableSet {e : OriginalCoordinates p |
      ReferenceInitializationRun.run
        (ReferenceInitializationMeasurability.inputOfCoordinates p C_star C_h eta rewards
          (ids, e)) s.val = b} :=
    (measurableSet_singleton b).preimage hrun
  have hfixed : MeasurableSet
      (fixedBoundaryGenuineSuccessEvent p ids rewards C_star C_h eta b focal) := by
    by_cases hv : b.completed < n_boot p
    · let h := hv
      have hcoords : Measurable
          ((fun e : OriginalCoordinates p => (ids, e)) :
            OriginalCoordinates p → ReferenceInitializationMeasurability.InputCoordinates p) :=
        measurable_const.prodMk measurable_id
      have hunion : fixedBoundaryGenuineSuccessEvent p ids rewards C_star C_h eta b focal =
          ⋃ i : {i // i ∈ ReferenceInitializationRun.uninformed b},
            {e |
              i.1 = focal ∧
              (ReferenceInitializationRun.candidate
                (ReferenceInitializationMeasurability.inputOfCoordinates p C_star C_h eta rewards
                  (ids, e)) b h i).pending = true ∧
              (ReferenceInitializationRun.finishBlock
                (ReferenceInitializationMeasurability.inputOfCoordinates p C_star C_h eta rewards
                  (ids, e)) b h).activation focal =
                some (BootstrapObservedFollower.nextActivationRound p
                  (ReferenceInitializationRun.nextBlock b h))} := by
        ext e
        simp only [fixedBoundaryGenuineSuccessEvent, Set.mem_setOf_eq,
          Set.mem_iUnion]
        constructor
        · rintro ⟨hvalid, i, ⟨hi, hpending, hactivation⟩⟩
          have hproof : hvalid = h := Subsingleton.elim _ _
          subst hvalid
          exact ⟨i, ⟨hi, hpending, hactivation⟩⟩
        · rintro ⟨i, ⟨hi, hpending, hactivation⟩⟩
          exact ⟨h, i, ⟨hi, hpending, hactivation⟩⟩
      rw [hunion]
      apply MeasurableSet.iUnion
      intro i
      have hcandidate : Measurable (fun e : OriginalCoordinates p =>
          ReferenceInitializationRun.candidate
            (ReferenceInitializationMeasurability.inputOfCoordinates p C_star C_h eta rewards
              (ids, e)) b h i) :=
        (ReferenceInitializationMeasurability.measurable_candidate_at_fixedBoundary
          p C_star C_h eta rewards b h i).comp hcoords
      have hpending : Measurable (fun e : OriginalCoordinates p =>
          (ReferenceInitializationRun.candidate
            (ReferenceInitializationMeasurability.inputOfCoordinates p C_star C_h eta rewards
              (ids, e)) b h i).pending) :=
        (measurable_of_countable
          (fun r : BootstrapTruePrefixController.Registers => r.pending)).comp hcandidate
      have hfinish : Measurable (fun e : OriginalCoordinates p =>
          ReferenceInitializationRun.finishBlock
            (ReferenceInitializationMeasurability.inputOfCoordinates p C_star C_h eta rewards
              (ids, e)) b h) :=
        (ReferenceInitializationMeasurability.measurable_finishBlock_at_fixedBoundary
          p C_star C_h eta rewards b h).comp hcoords
      have hactivation : Measurable (fun e : OriginalCoordinates p =>
          (ReferenceInitializationRun.finishBlock
            (ReferenceInitializationMeasurability.inputOfCoordinates p C_star C_h eta rewards
              (ids, e)) b h).activation focal) :=
        (measurable_of_countable (fun c : ReferenceInitializationRun.Boundary p =>
          c.activation focal)).comp hfinish
      have hi : MeasurableSet {e : OriginalCoordinates p | i.1 = focal} := by
        by_cases hif : i.1 = focal
        · simpa [hif] using
            (MeasurableSet.univ : MeasurableSet (Set.univ : Set (OriginalCoordinates p)))
        · have heq : {e : OriginalCoordinates p | i.1 = focal} = ∅ := by
            ext e
            simp [hif]
          rw [heq]
          exact MeasurableSet.empty
      have hpendingSet : MeasurableSet {e : OriginalCoordinates p |
          (ReferenceInitializationRun.candidate
            (ReferenceInitializationMeasurability.inputOfCoordinates p C_star C_h eta rewards
              (ids, e)) b h i).pending = true} :=
        (measurableSet_singleton true).preimage hpending
      have hactivationSet : MeasurableSet {e : OriginalCoordinates p |
          (ReferenceInitializationRun.finishBlock
            (ReferenceInitializationMeasurability.inputOfCoordinates p C_star C_h eta rewards
              (ids, e)) b h).activation focal =
            some (BootstrapObservedFollower.nextActivationRound p
              (ReferenceInitializationRun.nextBlock b h))} :=
        (measurableSet_singleton _).preimage hactivation
      exact hi.inter (hpendingSet.inter hactivationSet)
    · have hempty :
          fixedBoundaryGenuineSuccessEvent p ids rewards C_star C_h eta b focal = ∅ := by
        ext e
        simp only [fixedBoundaryGenuineSuccessEvent, Set.mem_setOf_eq,
          Set.mem_empty_iff_false]
        constructor
        · rintro ⟨hvalid, _, _, _, _⟩
          exact (hv hvalid).elim
        · intro hfalse
          exact hfalse.elim
      rw [hempty]
      exact MeasurableSet.empty
  have hcrossing : MeasurableSet {e : OriginalCoordinates p | b.crossing = none} := by
    by_cases hc : b.crossing = none
    · simpa [hc] using
        (MeasurableSet.univ : MeasurableSet (Set.univ : Set (OriginalCoordinates p)))
    · have heq : {e : OriginalCoordinates p | b.crossing = none} = ∅ := by
        ext e
        simp [hc]
      rw [heq]
      exact MeasurableSet.empty
  have hcompleted : MeasurableSet {e : OriginalCoordinates p | b.completed = s.val} := by
    by_cases hc : b.completed = s.val
    · simpa [hc] using
        (MeasurableSet.univ : MeasurableSet (Set.univ : Set (OriginalCoordinates p)))
    · have heq : {e : OriginalCoordinates p | b.completed = s.val} = ∅ := by
        ext e
        simp [hc]
      rw [heq]
      exact MeasurableSet.empty
  exact hboundary.inter (hcrossing.inter (hcompleted.inter hfixed))

/-! The following result is an actual, unnormalized probability bound on one
fixed processed boundary atom. The clock localization is applied only to the
preblock measurable choice event with the whole future row retained. -/

theorem generated_one_block_genuine_success_mass
    (p : Parameters) (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (rowCompletion : CompletePublicTable.CompleteRow p)
    (scalarCompletion : BootstrapPrivateRoundStreams.PlayerRoundScalars p)
    (s : Fin (n_boot p)) (b : ReferenceInitializationRun.Boundary p)
    (hcompleted : b.completed = s.val) (hnotStopped : b.crossing = none)
    (i : Incoming p b) (a : Fin p.K)
    (hgood : ids ∈ IdentificationGoodEvent.identificationGoodEvent p)
    (hC_h : (4096 : ℝ) ≤ C_h)
    (hproductive : BootstrapStartupCostScale.h_boot C_h p ≤
      GeneratedBlockChoiceAverages.blockSupportCount p s rewards a) :
    (1 / (16 * (p.K : ℝ))) *
        (GeneratedBlockStartLaw.originalCoordinatesLaw p).real
          (GeneratedBlockChoiceAverages.activeHeldFutureEvent p s ids rewards C_star C_h eta
            b hcompleted hnotStopped i a Set.univ) ≤
      (GeneratedBlockStartLaw.originalCoordinatesLaw p).real
        (GeneratedBlockChoiceAverages.activeHeldFutureEvent p s ids rewards C_star C_h eta
          b hcompleted hnotStopped i a Set.univ ∩
            genuineSuccessEvent p ids rewards C_star C_h eta s i.1) := by
  let mu : Measure (OriginalCoordinates p) := GeneratedBlockStartLaw.originalCoordinatesLaw p
  let E : Set (OriginalCoordinates p) :=
    GeneratedBlockChoiceAverages.activeHeldFutureEvent p s ids rewards C_star C_h eta
      b hcompleted hnotStopped i a Set.univ
  let Q : Set (OriginalCoordinates p) :=
    GeneratedBlockChoiceAverages.goodIDChoiceFutureEvent p s ids rewards C_star C_h eta
      b hcompleted hnotStopped i a Set.univ
  let clockGood : Set (OriginalCoordinates p) :=
    GeneratedClockBlockTail.clockGood ids rewards C_star C_h eta rowCompletion scalarCompletion s i.1
  have hcomponents :=
    (IdentificationGoodEvent.mem_identificationGoodEvent_iff_components p ids).mp hgood
  have hid : IdentificationRectangleExclusion.idArrayPropertyII p ids := hcomponents.2.1
  have hproductive' : BootstrapStartupCostScale.h_boot C_h p ≤
      BootstrapDownCountMean.rewardSupportCount p s rewards a := by
    rw [← blockSupportCount_eq_rewardSupportCount p s rewards a]
    exact hproductive
  have hQmass : ENNReal.ofReal (3 / (16 * (p.K : ℝ))) * mu E ≤ mu Q := by
    simpa [mu, E, Q, GeneratedBlockStartLaw.originalCoordinatesLaw] using
      (GeneratedBlockChoiceAverages.goodIDChoiceFutureEvent_mass_ge_three_sixteenths_over_K
        p s ids rewards C_star C_h eta b hcompleted hnotStopped i a Set.univ
        MeasurableSet.univ hgood)
  have hQmeas : MeasurableSet Q := by
    exact GeneratedBlockChoiceAverages.measurableSet_goodIDChoiceFutureEvent p s ids rewards
      C_star C_h eta b hcompleted hnotStopped i a Set.univ MeasurableSet.univ
  have hEmeas : MeasurableSet E := by
    change MeasurableSet (GeneratedBlockGuardLaw.generatedProcessedGuardFutureEvent p s ids
      rewards C_star C_h eta b hcompleted hnotStopped
      (GeneratedBlockGuardLaw.focalActiveHeldGuard p b i a) Set.univ Set.univ)
    exact GeneratedBlockGuardLaw.measurableSet_generatedProcessedGuardFutureEvent p s ids
      rewards C_star C_h eta b hcompleted hnotStopped
      (GeneratedBlockGuardLaw.focalActiveHeldGuard p b i a) Set.univ Set.univ
      MeasurableSet.univ
  have hQadapt : MeasurableSet[GeneratedBootstrapFiltration.analysisFiltration p
      (GeneratedClockBlockTail.blockClockStart p s - 1)] Q := by
    exact measurableSet_goodIDChoiceFutureEvent_at_blockStart p s ids rewards C_star C_h eta
      b hcompleted hnotStopped i a
  have hQguard : Q ⊆ {e | GeneratedClockBlockBalance.generatedClockBlockGuard ids rewards
      C_star C_h eta s i.1 a e} :=
    goodIDChoiceFutureEvent_subset_generatedClockBlockGuard p s ids rewards C_star C_h eta
      b hcompleted hnotStopped i a
      ⟨s.val * B_boot p, by
        have hstartStop := GeneratedClockBlockBalance.calendarBlock_start_lt_stop_local p s
        exact lt_of_lt_of_le hstartStop (Nat.min_le_left _ _)
      ⟩
      ((BootstrapDimensions.mem_calendarBlock_iff p s
        ⟨s.val * B_boot p, by
          have hstartStop := GeneratedClockBlockBalance.calendarBlock_start_lt_stop_local p s
          exact lt_of_lt_of_le hstartStop (Nat.min_le_left _ _)
        ⟩).mpr ⟨le_rfl,
          GeneratedClockBlockBalance.calendarBlock_start_lt_stop_local p s⟩)
  have hQsubsetE : Q ⊆ E :=
    goodIDChoiceFutureEvent_subset_activeHeldFutureEvent p s ids rewards C_star C_h eta
      b hcompleted hnotStopped i a
  have hclockMeas : MeasurableSet clockGood := by
    exact GeneratedClockBlockTail.clockGood_measurable ids rewards C_star C_h eta
      rowCompletion scalarCompletion s i.1
  have hclockLocalized := GeneratedClockBlockTail.clockGood_failure_localized ids rewards
    C_star C_h eta rowCompletion scalarCompletion s i.1 Q hQadapt
  have hfailureReal : mu.real (Q ∩ clockGoodᶜ) ≤
      Real.exp (-(4 * (ConstructorDimensions.b_N p : ℝ))) * mu.real Q := by
    simpa [mu, Q, clockGood, GeneratedBootstrapRoundLaw.originalLaw,
      GeneratedBlockStartLaw.originalCoordinatesLaw] using hclockLocalized
  have hQdiffMeas : MeasurableSet (Q \ clockGood) := hQmeas.diff hclockMeas
  have hsuccessMeas : MeasurableSet
      (genuineSuccessEvent p ids rewards C_star C_h eta s i.1) :=
    measurableSet_genuineSuccessEvent p ids rewards C_star C_h eta s i.1
  have hresultMeas : MeasurableSet (E ∩ genuineSuccessEvent p ids rewards C_star C_h eta s i.1) :=
    hEmeas.inter hsuccessMeas
  have hmassQReal : (3 / (16 * (p.K : ℝ))) * mu.real E ≤ mu.real Q := by
    have hK : 0 < (p.K : ℝ) := Nat.cast_pos.mpr (ConstructorDimensions.K_pos p)
    have hcoeff : 0 ≤ 3 / (16 * (p.K : ℝ)) := by positivity
    have htoReal := ENNReal.toReal_mono (measure_ne_top mu Q) hQmass
    simpa only [Measure.real, ENNReal.toReal_mul, ENNReal.toReal_ofReal hcoeff] using htoReal
  have hclockfailure : mu.real (Q ∩ clockGoodᶜ) ≤ (1 / 8 : ℝ) * mu.real Q := by
    calc
      mu.real (Q ∩ clockGoodᶜ) ≤
      Real.exp (-(4 * (ConstructorDimensions.b_N p : ℝ))) * mu.real Q := hfailureReal
      _ ≤ (1 / 8 : ℝ) * mu.real Q :=
        mul_le_mul_of_nonneg_right
          (GeneratedClockBlockTail.source_clock_failure_exponent_bound p).2.le
          measureReal_nonneg
  have hpartition : mu.real (Q ∩ clockGood) + mu.real (Q \ clockGood) = mu.real Q :=
    measureReal_inter_add_sdiff hclockMeas (measure_ne_top mu Q)
  have hdiffEq : Q \ clockGood = Q ∩ clockGoodᶜ := by
    ext e
    simp
  rw [hdiffEq] at hpartition
  have hclockSuccessMass : (7 / 8 : ℝ) * mu.real Q ≤ mu.real (Q ∩ clockGood) := by
    linarith [hpartition, hclockfailure]
  have hsuccessAE : ∀ᵐ e ∂mu, e ∈ Q ∩ clockGood →
      e ∈ genuineSuccessEvent p ids rewards C_star C_h eta s i.1 := by
    have hquotaAE := GeneratedMulticastQuota.generated_multicast_quota_boundary_activation_ae
      ids rewards C_star C_h eta rowCompletion scalarCompletion s i.1 a hid hC_h hproductive'
    filter_upwards [hquotaAE] with e hquota
    intro he
    have hguard : GeneratedClockBlockBalance.generatedClockBlockGuard ids rewards C_star C_h
        eta s i.1 a e := hQguard he.1
    rcases hquota hguard he.2 with ⟨hquotaClock, _⟩
    let src := GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e
    let bActual := ReferenceInitializationRun.run src s.val
    have hcross : bActual.crossing = none := by
      simpa [bActual, src] using hguard.1
    have hprocessed : (ReferenceInitializationRun.run
        (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e) s.val).crossing = none := by
      simpa [src] using hcross
    have hcompletedActual : bActual.completed = s.val := by
      exact GeneratedBootstrapRoundLaw.processed_completed ids rewards C_star C_h eta s e
        (by simpa [src, bActual] using hprocessed)
    have hbc : bActual.completed = s.val := by simpa [src, bActual] using hcompletedActual
    have hvalidActual : bActual.completed < n_boot p := hbc ▸ s.isLt
    have hvalidGuard : bActual.completed < n_boot p := by
      exact GeneratedClockBlockBalance.processedBoundary_valid ids rewards C_star C_h eta s e
        (by simpa [bActual, src] using hcross)
    have hincoming : i.1 ∈ ReferenceInitializationRun.uninformed bActual := by
      simpa [bActual, src, ReferenceInitializationRun.physical,
        BootstrapPhysicalInput.blockInput] using (hguard.2 hvalidGuard).1
    let phys := ReferenceInitializationRun.physical src bActual hvalidActual
    let j : {j // j ∈ phys.uninformed} := ⟨i.1, by
      simpa [phys, ReferenceInitializationRun.physical,
        BootstrapPhysicalInput.blockInput] using hincoming⟩
    have hactive : phys.active j = true := (hguard.2 hvalidGuard).2 hincoming |>.1
    have hheld : phys.held j = a := (hguard.2 hvalidGuard).2 hincoming |>.2.1
    have htarget : phys.target = a := (hguard.2 hvalidGuard).2 hincoming |>.2.2.1
    have haccept := BootstrapMulticastAcceptance.generated_multicast_quota_boundary_activation
      ids rewards C_star C_h eta rowCompletion scalarCompletion s e i.1 hprocessed
      (by simpa [src, bActual] using hincoming)
    have hactualSuccess := haccept hactive (hheld.trans htarget.symm) (by
      simpa [GeneratedMulticastQuota.actualMulticastClockSum, src] using hquotaClock)
    rcases hactualSuccess with ⟨hpending, hactivation, _⟩
    have hsuccess : e ∈ genuineSuccessEvent p ids rewards C_star C_h eta s i.1 := by
      rw [genuineSuccessEvent]
      apply Set.mem_iUnion.mpr
      refine ⟨bActual, ?_⟩
      simp only [Set.mem_setOf_eq]
      refine ⟨?_, hcross, hcompletedActual, ?_⟩
      · simp [bActual, src, GeneratedBootstrapRoundLaw.input,
          ReferenceInitializationMeasurability.inputOfCoordinates]
      · change e ∈ fixedBoundaryGenuineSuccessEvent p ids rewards C_star C_h eta bActual i.1
        unfold fixedBoundaryGenuineSuccessEvent
        simp only [Set.mem_setOf_eq]
        refine ⟨hvalidActual, j, ?_⟩
        refine ⟨rfl, ?_, ?_⟩
        · simpa [j, phys, src, bActual, hvalidActual, hbc, hprocessed,
            GeneratedBootstrapRoundLaw.input] using hpending
        · simpa [j, phys, src, bActual, hvalidActual, hbc, hprocessed,
            GeneratedBootstrapRoundLaw.input] using hactivation
    exact hsuccess
  have hsuccessSubsetAE : ∀ᵐ e ∂mu, e ∈ Q ∩ clockGood →
      e ∈ E ∩ genuineSuccessEvent p ids rewards C_star C_h eta s i.1 := by
    filter_upwards [hsuccessAE] with e he
    intro heQGood
    exact ⟨hQsubsetE heQGood.1, he heQGood⟩
  have hsuccessMassENN : mu (Q ∩ clockGood) ≤
      mu (E ∩ genuineSuccessEvent p ids rewards C_star C_h eta s i.1) := by
    apply measure_mono_ae
    exact hsuccessSubsetAE
  have hsuccessMass : mu.real (Q ∩ clockGood) ≤
      mu.real (E ∩ genuineSuccessEvent p ids rewards C_star C_h eta s i.1) := by
    have htoReal := ENNReal.toReal_mono
      (measure_ne_top mu (E ∩ genuineSuccessEvent p ids rewards C_star C_h eta s i.1))
      hsuccessMassENN
    simpa only [Measure.real] using htoReal
  have hErealNonneg : 0 ≤ mu.real E := measureReal_nonneg
  have hK : 0 < (p.K : ℝ) := Nat.cast_pos.mpr (ConstructorDimensions.K_pos p)
  have hcoeff : (1 / (16 * (p.K : ℝ))) ≤
      (7 / 8 : ℝ) * (3 / (16 * (p.K : ℝ))) := by
    field_simp
    norm_num
  calc
    (1 / (16 * (p.K : ℝ))) * mu.real E ≤
        ((7 / 8 : ℝ) * (3 / (16 * (p.K : ℝ)))) * mu.real E :=
      mul_le_mul_of_nonneg_right hcoeff hErealNonneg
    _ = (7 / 8 : ℝ) * ((3 / (16 * (p.K : ℝ))) * mu.real E) := by ring
    _ ≤ (7 / 8 : ℝ) * mu.real Q :=
      mul_le_mul_of_nonneg_left hmassQReal (by norm_num)
    _ ≤ mu.real (Q ∩ clockGood) := hclockSuccessMass
    _ ≤ mu.real (E ∩ genuineSuccessEvent p ids rewards C_star C_h eta s i.1) := by
      exact hsuccessMass

end Bandits.Support.GeneratedBlockActivationAverage

end
