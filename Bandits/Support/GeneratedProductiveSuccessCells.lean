/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.CausalBootstrapBlockProduct
public import Bandits.Support.GeneratedBlockActivationAverage
public import Bandits.Support.GeneratedBlockChoiceAverages
public import Bandits.Support.GeneratedMulticastQuota
public import Bandits.Support.GeneratedClockBlockTail
public import Bandits.Support.GeneratedProductiveExitBudget
public import Bandits.Support.GeneratedBootstrapGainBudget
public import Bandits.Support.GeneratedBootstrapBlockFiltrationRepair

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Causal-prefix productive-success cells

This module uses the accepted original-coordinate bootstrap law. It records
the actual enabled/held cell at the incoming block and relates the accepted
true-row activation event to the actual productive-exit indicator.

Sources: `sources/zip4/manuscript/appendix_b_communication.tex:398-483,
586-625` and `sources/zip4/manuscript/07_public_setup.tex:63-113`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.CompletePublicTable
open Bandits.Support.ReferenceInitializationRun
open Bandits.Support.GeneratedBootstrapBlockFiltrationRepair
open Bandits.Support.GeneratedBootstrapGainBudget
open Bandits.Support.GeneratedProductiveExitBudget
open scoped ENNReal

namespace Bandits.Support.GeneratedProductiveSuccessCells

abbrev Parameters := ConstructorDimensions.Parameters
abbrev Coordinates (p : Parameters) := GeneratedBootstrapRoundLaw.Coordinates p

/-- The actual enabled/held-arm cell of an incoming follower's existing
analysis block. The latent arm is read from the original labelled draw. -/
def enabledHeldCell (p : Parameters) (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (s : Fin (n_boot p))
    (i : ActiveRoundActions.Follower p.m) (a : Fin p.K) : Set (Coordinates p) :=
  {e | (GeneratedBootstrapGainBudget.blockAt
      (referenceInput p ids rewards C_star C_h eta e) i s).enabled = true ∧
    (GeneratedBootstrapGainBudget.blockAt
      (referenceInput p ids rewards C_star C_h eta e) i s).held = a}

/-- A causal-prefix measurable set is the inverse image of a measurable set
on the exact source-prefix carrier. -/
theorem boundarySigma_event_is_sourcePrefix_preimage (p : Parameters)
    (s : Fin (n_boot p)) (A : Set (Coordinates p))
    (hA : MeasurableSet[GeneratedBootstrapBlockFiltrationRepair.boundarySigma p s.val] A) :
    ∃ V : Set (GeneratedBootstrapBlockFiltrationRepair.SourcePrefix p s.val),
      MeasurableSet V ∧
        (GeneratedBootstrapBlockFiltrationRepair.sourcePrefix p s.val) ⁻¹' V = A := by
  change MeasurableSet[MeasurableSpace.comap
    (GeneratedBootstrapBlockFiltrationRepair.sourcePrefix p s.val) inferInstance] A at hA
  rcases MeasurableSpace.measurableSet_comap.mp hA with ⟨V, hV, hpre⟩
  exact ⟨V, hV, hpre⟩

/-- Reconstruct the actual incoming boundary from a literal source prefix by
completing omitted coordinates from a fixed original point. The completion is
only a section; prefix invariance proves it gives the original run boundary. -/
def boundaryFromSourcePrefix (p : Parameters)
    (s : Fin (n_boot p)) (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (e₀ : Coordinates p)
    (v : GeneratedBootstrapBlockFiltrationRepair.SourcePrefix p s.val) :
    ReferenceInitializationRun.Boundary p :=
  ReferenceInitializationRun.run
    (GeneratedBootstrapBlockFiltrationRepair.referenceInput p ids rewards C_star C_h eta
      (GeneratedBootstrapBlockFiltrationRepair.completeSourcePrefix p s.val e₀ v)) s.val

/-- The prefix section reconstructs the actual boundary at every original
coordinate point, without changing the original physical trace. -/
theorem boundaryFromSourcePrefix_eq_original (p : Parameters)
    (s : Fin (n_boot p)) (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (e₀ e : Coordinates p) :
    boundaryFromSourcePrefix p s ids rewards C_star C_h eta e₀
        (GeneratedBootstrapBlockFiltrationRepair.sourcePrefix p s.val e) =
      ReferenceInitializationRun.run
        (GeneratedBootstrapBlockFiltrationRepair.referenceInput p ids rewards C_star C_h eta e)
        s.val := by
  unfold boundaryFromSourcePrefix
  exact GeneratedBootstrapBlockFiltrationRepair.run_eq_of_sourcePrefix_eq p s.val ids
    rewards C_star C_h eta
    (GeneratedBootstrapBlockFiltrationRepair.completeSourcePrefix p s.val e₀
      (GeneratedBootstrapBlockFiltrationRepair.sourcePrefix p s.val e)) e
    (GeneratedBootstrapBlockFiltrationRepair.sourcePrefix_completeSourcePrefix p s.val e₀
      (GeneratedBootstrapBlockFiltrationRepair.sourcePrefix p s.val e))

/-- The source-prefix boundary reconstruction is measurable on the prefix
carrier. -/
theorem measurable_boundaryFromSourcePrefix (p : Parameters)
    (s : Fin (n_boot p)) (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (e₀ : Coordinates p) :
    Measurable (boundaryFromSourcePrefix p s ids rewards C_star C_h eta e₀) := by
  change Measurable (fun v : GeneratedBootstrapBlockFiltrationRepair.SourcePrefix p s.val =>
    ReferenceInitializationRun.run
      (ReferenceInitializationMeasurability.inputOfCoordinates p C_star C_h eta rewards
        (ids, GeneratedBootstrapBlockFiltrationRepair.completeSourcePrefix p s.val e₀ v))
      s.val)
  exact (ReferenceInitializationMeasurability.measurable_run p C_star C_h eta rewards s.val).comp
    (measurable_const.prodMk
      (GeneratedBootstrapBlockFiltrationRepair.measurable_completeSourcePrefix p s.val e₀))

/-- The original causal boundary sigma algebra is contained in the analysis
sigma algebra immediately before the first clock index of block `s`, including
the final clipped calendar block. -/
theorem boundarySigma_le_analysis_before_block_clock (p : Parameters)
    (s : Fin (n_boot p)) :
    GeneratedBootstrapBlockFiltrationRepair.boundarySigma p s.val ≤
      GeneratedBootstrapFiltration.analysisFiltration p
        (GeneratedClockBlockTail.blockClockStart p s - 1) := by
  have hstart := GeneratedClockBlockBalance.calendarBlock_start_lt_stop_local p s
  have hstartT : s.val * B_boot p < p.T :=
    lt_of_lt_of_le hstart (Nat.min_le_left _ _)
  have htime : ReferenceInitializationRun.elapsed p s.val =
      GeneratedClockBlockTail.blockClockStart p s - 1 := by
    unfold ReferenceInitializationRun.elapsed GeneratedClockBlockTail.blockClockStart
    rw [Nat.min_eq_right (Nat.le_of_lt hstartT)]
    omega
  rw [← htime]
  exact GeneratedBootstrapBlockFiltrationRepair.boundaryFiltration_le_analysis_at_elapsed
    p s.val

/-- The accepted clock-failure localization remains valid after intersecting
with any causal-prefix event and any event measurable at the clock start. -/
theorem clockGood_failure_localized_on_causalPrefix
    (p : Parameters) (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (rowCompletion : CompletePublicTable.CompleteRow p)
    (scalarCompletion : BootstrapPrivateRoundStreams.PlayerRoundScalars p)
    (s : Fin (n_boot p)) (focal : ActiveRoundActions.Follower p.m)
    (A Q : Set (Coordinates p))
    (hA : MeasurableSet[GeneratedBootstrapBlockFiltrationRepair.boundarySigma p s.val] A)
    (hQ : MeasurableSet[GeneratedBootstrapFiltration.analysisFiltration p
      (GeneratedClockBlockTail.blockClockStart p s - 1)] Q) :
    (GeneratedBootstrapRoundLaw.originalLaw p).real
        (A ∩ Q ∩ (GeneratedClockBlockTail.clockGood ids rewards C_star C_h eta
          rowCompletion scalarCompletion s focal)ᶜ) ≤
      Real.exp (-(4 * (b_N p : ℝ))) *
        (GeneratedBootstrapRoundLaw.originalLaw p).real (A ∩ Q) := by
  have hA' : MeasurableSet[GeneratedBootstrapFiltration.analysisFiltration p
      (GeneratedClockBlockTail.blockClockStart p s - 1)] A :=
    (boundarySigma_le_analysis_before_block_clock p s) A hA
  have hAQ : MeasurableSet[GeneratedBootstrapFiltration.analysisFiltration p
      (GeneratedClockBlockTail.blockClockStart p s - 1)] (A ∩ Q) := hA'.inter hQ
  have hlocal := GeneratedClockBlockTail.clockGood_failure_localized ids rewards C_star C_h
    eta rowCompletion scalarCompletion s focal (A ∩ Q) hAQ
  simpa [Set.inter_assoc] using hlocal

/-- On a supported enabled/held cell, a genuine next-boundary success removes
the actual prelaunch-uninformed guard. A launch crossing can also remove that
guard; the implication here uses the activation equation already recorded by
`genuineSuccessEvent`. -/
theorem genuineSuccessEvent_implies_productiveExitIndicator_eq_one
    (p : Parameters) (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (s : Fin (n_boot p))
    (i : ActiveRoundActions.Follower p.m) (a : Fin p.K)
    (hSupport : BootstrapStartupCostScale.h_boot C_h p ≤
      GeneratedBlockChoiceAverages.blockSupportCount p s rewards a)
    (e : Coordinates p)
    (hCell : e ∈ enabledHeldCell p ids rewards C_star C_h eta s i a)
    (hSuccess : e ∈ GeneratedBlockActivationAverage.genuineSuccessEvent
      p ids rewards C_star C_h eta s i) :
    GeneratedProductiveExitBudget.productiveExitIndicator
      (referenceInput p ids rewards C_star C_h eta e) i s = 1 := by
  let x := referenceInput p ids rewards C_star C_h eta e
  have hCell' : (GeneratedBootstrapGainBudget.blockAt x i s).enabled = true ∧
      (GeneratedBootstrapGainBudget.blockAt x i s).held = a := by
    simpa [enabledHeldCell, x] using hCell
  have hSupport' : GeneratedBootstrapGainBudget.startupThreshold x ≤
      GeneratedBootstrapGainBudget.rewardSupportCountAt x s a := by
    have hSupportRaw : BootstrapStartupCostScale.h_boot C_h p ≤
        BootstrapDownCountMean.rewardSupportCount p s rewards a := by
      rw [← GeneratedBlockActivationAverage.blockSupportCount_eq_rewardSupportCount
        p s rewards a]
      exact hSupport
    simpa [GeneratedBootstrapGainBudget.startupThreshold,
      GeneratedBootstrapGainBudget.rewardSupportCountAt, x, referenceInput,
      GeneratedBootstrapRoundLaw.input,
      ReferenceInitializationMeasurability.inputOfCoordinates] using hSupportRaw
  have hProductive : GeneratedBootstrapGainBudget.productiveIndicator x i s = 1 := by
    change (if (GeneratedBootstrapGainBudget.blockAt x i s).enabled = true ∧
        (GeneratedBootstrapGainBudget.startupThreshold x : ℝ) ≤
          GeneratedBootstrapGainBudget.rewardSupportCountAt x s
            (GeneratedBootstrapGainBudget.blockAt x i s).held then 1 else 0) = 1
    rw [if_pos ⟨hCell'.1, by simpa [hCell'.2] using hSupport'⟩]
  have hSuccess' : e ∈ GeneratedBlockActivationAverage.genuineSuccessEvent
      p ids rewards C_star C_h eta s i := hSuccess
  simp only [GeneratedBlockActivationAverage.genuineSuccessEvent,
    Set.mem_iUnion, Set.mem_setOf_eq] at hSuccess'
  rcases hSuccess' with ⟨b, hboundary, hcrossing, hcompleted, hfixed⟩
  simp only [GeneratedBlockActivationAverage.fixedBoundaryGenuineSuccessEvent,
    Set.mem_setOf_eq] at hfixed
  rcases hfixed with ⟨hvalid, j, hj, hpending, hactivation⟩
  have hrun : ReferenceInitializationRun.run x s.val = b := by
    change ReferenceInitializationRun.run
      (ReferenceInitializationMeasurability.inputOfCoordinates p C_star C_h eta rewards
        (ids, e)) s.val = b
    exact hboundary
  have hnextRun : ReferenceInitializationRun.run x (s.val + 1) =
      ReferenceInitializationRun.finishBlock x b hvalid := by
    have hprocess := GeneratedBootstrapPotential.run_processes_opportunity x s
      (by simpa only [hrun] using hcrossing)
    simpa only [hrun] using hprocess.2.2
  have hsavedActivation :
      (ReferenceInitializationRun.finishBlock x b hvalid).activation i =
        some (ReferenceInitializationRun.boundaryActivation b) := by
    have hsaved := ReferenceInitializationRun.saved_activation
      (ReferenceInitializationMeasurability.inputOfCoordinates p C_star C_h eta rewards
        (ids, e)) b hvalid j hpending
    simpa [hj, x, referenceInput, GeneratedBootstrapRoundLaw.input,
      ReferenceInitializationMeasurability.inputOfCoordinates] using hsaved
  have hfinishActivation :
      (ReferenceInitializationRun.finishBlock x b hvalid).activation i =
        some (BootstrapObservedFollower.nextActivationRound p
          (ReferenceInitializationRun.nextBlock b hvalid)) := by
    simpa [x, referenceInput, GeneratedBootstrapRoundLaw.input,
      ReferenceInitializationMeasurability.inputOfCoordinates] using hactivation
  have hactivationRound : ReferenceInitializationRun.boundaryActivation b =
      BootstrapObservedFollower.nextActivationRound p
        (ReferenceInitializationRun.nextBlock b hvalid) :=
    Option.some.inj (hsavedActivation.symm.trans hfinishActivation)
  have hnextActivation :
      (ReferenceInitializationRun.run x (s.val + 1)).activation i ≠ none := by
    rw [hnextRun, hsavedActivation]
    exact Option.some_ne_none _
  have _hactivationRound := hactivationRound
  have hnextGuard : GeneratedProductiveExitBudget.prelaunchUninformedIndicator
      x i (s.val + 1) = 0 := by
    simp [GeneratedProductiveExitBudget.prelaunchUninformedIndicator,
      hnextActivation]
  change GeneratedProductiveExitBudget.productiveExitIndicator x i s = 1
  simp [GeneratedProductiveExitBudget.productiveExitIndicator, hProductive,
    hnextGuard]

end Bandits.Support.GeneratedProductiveSuccessCells

end
