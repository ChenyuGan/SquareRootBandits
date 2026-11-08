/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferencePostReplacementCollectionStoppedSignedTowerReduction
public import Bandits.Support.ReferencePostReplacementCollectionUpWeightedWaitingCost

import Mathlib.Tactic

/-!
# Numeric signed cost of stopped post-rawK releases

This theorem combines the accepted signed DATA-plus-UP reduction with the
accepted numerical UP waiting-cost estimate on the same original source,
stopped sigma algebra, reward table, and unrestricted constants.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ContinuousLearningRows
open Bandits.Support.PhaseStartConditionalWaiting
open Bandits.Support.ReferencePostReplacementCollectionStoppedReleaseAdaptation
open Bandits.Support.ReferenceSourcePrefixHistoryFiltration
open Bandits.Support.ReferencePostReplacementCollectionStoppedSignedTowerReduction
open Bandits.Support.ReferencePostReplacementCollectionUpWeightedWaitingCost
open scoped Classical BigOperators

namespace Bandits.Support.ReferencePostReplacementCollectionStoppedReleaseSignedCost

variable {p : ConstructorDimensions.Parameters}

/-- The signed post-rawK release deficit charge is bounded by the DATA quota
and the numerical UP waiting cost, conditional on the actual release start
under the original source-input law. -/
theorem actualPostRawKSignedReleaseDeficitCharge_condExp_numeric_bound
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p) :
    (sourceInputLaw p)[
      actualPostRawKSignedReleaseDeficitCharge rate rewards C_star C_h |
        PhaseStartConditionalWaiting.phaseStartSigmaAlgebra
          (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0)
          (postRawKReleaseSigma rate rewards C_star C_h)
          (postRawKRelease_sigma_stopping rate rewards C_star C_h control0)] ≤ᵐ[
            sourceInputLaw p]
      fun _ =>
        2 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) +
          12 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) /
            (1 - Real.exp (-1)) *
              (Real.log ((p.m - 1 : ℕ) : ℝ) + 1) := by
  let μ := sourceInputLaw p
  let F := ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0
  let sigma := postRawKReleaseSigma rate rewards C_star C_h
  let mSigma := PhaseStartConditionalWaiting.phaseStartSigmaAlgebra F sigma
    (postRawKRelease_sigma_stopping rate rewards C_star C_h control0)
  have hObservation :
      ReferencePostReplacementCollectionStoppedSignedTowerReduction.actualPostRawKOmegaUpperCharge
          rate rewards C_star C_h =
        ReferencePostReplacementCollectionUpWeightedWaitingCost.postRawKUpWeightedWaitingCharge
          rate rewards C_star C_h := by
    rfl
  have hSigned := actualPostRawKSignedReleaseDeficitCharge_condExp_data_bound
    rate rewards C_star C_h control0
  have hWaiting := postRawKUpWeightedWaitingCharge_condExp_bound
    rate rewards C_star C_h control0
  change μ[actualPostRawKSignedReleaseDeficitCharge rate rewards C_star C_h |
      mSigma] ≤ᵐ[μ]
    fun z => 2 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) +
      μ[actualPostRawKOmegaUpperCharge rate rewards C_star C_h | mSigma] z
    at hSigned
  change μ[postRawKUpWeightedWaitingCharge rate rewards C_star C_h | mSigma] ≤ᵐ[μ]
    fun _ =>
      12 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) /
        (1 - Real.exp (-1)) *
          (Real.log ((p.m - 1 : ℕ) : ℝ) + 1)
    at hWaiting
  have hWaitingObservation :
      μ[actualPostRawKOmegaUpperCharge rate rewards C_star C_h | mSigma] ≤ᵐ[μ]
        fun _ =>
          12 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) /
            (1 - Real.exp (-1)) *
              (Real.log ((p.m - 1 : ℕ) : ℝ) + 1) := by
    simpa only [hObservation] using hWaiting
  change μ[actualPostRawKSignedReleaseDeficitCharge rate rewards C_star C_h |
      mSigma] ≤ᵐ[μ]
    fun z =>
      2 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) +
        12 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) /
          (1 - Real.exp (-1)) *
            (Real.log ((p.m - 1 : ℕ) : ℝ) + 1)
  filter_upwards [hSigned, hWaitingObservation] with z hSignedBound hWaitingBound
  calc
    μ[actualPostRawKSignedReleaseDeficitCharge rate rewards C_star C_h | mSigma] z ≤
        2 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) +
          μ[actualPostRawKOmegaUpperCharge rate rewards C_star C_h | mSigma] z :=
      hSignedBound
    _ ≤
        2 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) +
          12 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) /
            (1 - Real.exp (-1)) *
              (Real.log ((p.m - 1 : ℕ) : ℝ) + 1) :=
      add_le_add_right hWaitingBound _

end Bandits.Support.ReferencePostReplacementCollectionStoppedReleaseSignedCost
