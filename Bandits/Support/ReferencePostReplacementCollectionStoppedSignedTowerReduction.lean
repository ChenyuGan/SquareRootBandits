/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferencePostReplacementCollectionSentinelSectionLaw
public import Bandits.Support.ReferencePostReplacementCollectionDataWaitingCost

import Mathlib.Tactic

/-!
# Stopped signed post-rawK release tower reduction

This module localizes the accepted signed one-round release estimate to the
actual phase-start field for the stopped post-rawK collection. The observations
retain the original source input, reward table, stored payload, and strict-past
stop. This is an analytical source-prefix field, not a manuscript filtration.

The mathematical source is `sources/zip4/manuscript/05_binary_transport.tex`
around the release-cost argument and `sources/zip4/manuscript/06_interruptions.tex`
for the inclusive first-failure update.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ContinuousLearningRows
open Bandits.Support.PhaseStartConditionalWaiting
open Bandits.Support.ReferencePostReplacementCollectionStoppedReleaseAdaptation
open Bandits.Support.ReferencePostReplacementCollectionSentinelSectionLaw
open Bandits.Support.ReferencePostReplacementCollectionDataWaitingCost
open Bandits.Support.ReferencePostReplacementCollectionReleaseResamplingData
open Bandits.Support.ReferenceSourcePrefixHistoryFiltration
open scoped Classical BigOperators

namespace Bandits.Support.ReferencePostReplacementCollectionStoppedSignedTowerReduction

variable {p : ConstructorDimensions.Parameters}

/-- The finite original-source signed physical deficit over the literal
stopped post-rawK release dates. -/
def actualPostRawKSignedReleaseDeficitCharge
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) : ℝ :=
  ∑ t : Fin p.T,
    postRawKStoppedSignedReleaseDeficit
      rate rewards C_star C_h t z

/-- The finite original-source upper observation used by the accepted signed
one-round law. It uses the same stopped pending set and actual omega. -/
def actualPostRawKOmegaUpperCharge
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) : ℝ :=
  ∑ t : Fin p.T,
    (if (postRawKStoppedPendingSet rate rewards C_star C_h t z).Nonempty
      then (1 : ℝ) else 0) *
      postRawKReleaseOmega rate rewards C_star C_h t z

private def stoppedPendingProcess
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) :
    ℕ → BootstrapPrivateRoundStreams.SourceInput p → Finset (Fin (p.m - 1)) :=
  fun n z => if hn : n < p.T then
    postRawKStoppedPendingSet rate rewards C_star C_h ⟨n, hn⟩ z
  else ∅

private theorem stoppedPending_nonempty_measurable_preRound
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p) (t : Fin p.T) :
    MeasurableSet[
      ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0
        (t.val + 1)]
      {z : BootstrapPrivateRoundStreams.SourceInput p |
        (postRawKStoppedPendingSet rate rewards C_star C_h t z).Nonempty} := by
  have heq : {z : BootstrapPrivateRoundStreams.SourceInput p |
      (postRawKStoppedPendingSet rate rewards C_star C_h t z).Nonempty} =
      ⋃ i : Fin (p.m - 1), {z | i ∈ postRawKStoppedPendingSet rate rewards C_star C_h t z} := by
    ext z
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Finset.Nonempty]
  rw [heq]
  exact MeasurableSet.iUnion fun i =>
    postRawKStoppedPendingSet_mem_measurable_preRound
      rate rewards C_star C_h control0 t i

/-- Ambient Borel measurability of the signed stopped release charge. -/
theorem actualPostRawKSignedReleaseDeficitCharge_measurable
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p) :
    Measurable (actualPostRawKSignedReleaseDeficitCharge rate rewards C_star C_h) := by
  unfold actualPostRawKSignedReleaseDeficitCharge
  exact Finset.measurable_fun_sum _ fun t _ =>
    postRawKStoppedSignedReleaseDeficit_measurable
      rate rewards C_star C_h control0 t

/-- Integrability of the signed stopped release charge on the original source
law follows from the accepted one-round signed bound. -/
theorem actualPostRawKSignedReleaseDeficitCharge_integrable
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p) :
    Integrable (actualPostRawKSignedReleaseDeficitCharge rate rewards C_star C_h)
      (sourceInputLaw p) := by
  unfold actualPostRawKSignedReleaseDeficitCharge
  apply integrable_finsetSum Finset.univ
  intro t ht
  exact postRawKStoppedSignedReleaseDeficit_integrable
    rate rewards C_star C_h control0 t

/-- Ambient Borel measurability of the actual finite omega upper observation. -/
theorem actualPostRawKOmegaUpperCharge_measurable
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p) :
    Measurable (actualPostRawKOmegaUpperCharge rate rewards C_star C_h) := by
  unfold actualPostRawKOmegaUpperCharge
  apply Finset.measurable_fun_sum
  intro t ht
  let F := ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0
  have hactive : MeasurableSet[F (t.val + 1)]
      {z : BootstrapPrivateRoundStreams.SourceInput p |
        (postRawKStoppedPendingSet rate rewards C_star C_h t z).Nonempty} :=
    stoppedPending_nonempty_measurable_preRound rate rewards C_star C_h control0 t
  have hactive' : MeasurableSet
      {z : BootstrapPrivateRoundStreams.SourceInput p |
        (postRawKStoppedPendingSet rate rewards C_star C_h t z).Nonempty} :=
    F.le (t.val + 1) _ hactive
  have hmask : Measurable (fun z : BootstrapPrivateRoundStreams.SourceInput p =>
      if (postRawKStoppedPendingSet rate rewards C_star C_h t z).Nonempty
      then (1 : ℝ) else 0) :=
    measurable_const.ite hactive' measurable_const
  have hOmega : Measurable
      (postRawKReleaseOmega rate rewards C_star C_h t) :=
    (postRawKReleaseOmega_measurable_preChoice
      rate rewards C_star C_h control0 t).mono (F.le (t.val + 1)) le_rfl
  exact hmask.mul hOmega

/-- Integrability of the actual omega upper observation from its unit bound. -/
private theorem stoppedOmegaUpperRound_integrable
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p) (t : Fin p.T) :
    Integrable
      (fun z : BootstrapPrivateRoundStreams.SourceInput p =>
        (if (postRawKStoppedPendingSet rate rewards C_star C_h t z).Nonempty
          then (1 : ℝ) else 0) *
          postRawKReleaseOmega rate rewards C_star C_h t z)
      (sourceInputLaw p) := by
  let F := ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0
  have hactive : MeasurableSet[F (t.val + 1)]
      {z : BootstrapPrivateRoundStreams.SourceInput p |
        (postRawKStoppedPendingSet rate rewards C_star C_h t z).Nonempty} :=
    stoppedPending_nonempty_measurable_preRound rate rewards C_star C_h control0 t
  have hactive' : MeasurableSet
      {z : BootstrapPrivateRoundStreams.SourceInput p |
        (postRawKStoppedPendingSet rate rewards C_star C_h t z).Nonempty} :=
    F.le (t.val + 1) _ hactive
  have hmask : Measurable (fun z : BootstrapPrivateRoundStreams.SourceInput p =>
      if (postRawKStoppedPendingSet rate rewards C_star C_h t z).Nonempty
      then (1 : ℝ) else 0) :=
    measurable_const.ite hactive' measurable_const
  have hOmega : Measurable (postRawKReleaseOmega rate rewards C_star C_h t) :=
    (postRawKReleaseOmega_measurable_preChoice
      rate rewards C_star C_h control0 t).mono (F.le (t.val + 1)) le_rfl
  have hterm : Measurable (fun z : BootstrapPrivateRoundStreams.SourceInput p =>
      (if (postRawKStoppedPendingSet rate rewards C_star C_h t z).Nonempty
        then (1 : ℝ) else 0) * postRawKReleaseOmega rate rewards C_star C_h t z) :=
    hmask.mul hOmega
  have hUnit : ∀ z : BootstrapPrivateRoundStreams.SourceInput p,
      (if (postRawKStoppedPendingSet rate rewards C_star C_h t z).Nonempty
        then (1 : ℝ) else 0) * postRawKReleaseOmega rate rewards C_star C_h t z ∈
          Set.Icc (0 : ℝ) 1 := by
    intro z
    by_cases hpending : (postRawKStoppedPendingSet rate rewards C_star C_h t z).Nonempty
    · simpa [hpending, Set.mem_Icc] using
        postRawKReleaseOmega_bounds rate rewards C_star C_h t z
    · simp [hpending, Set.mem_Icc]
  apply (integrable_const (1 : ℝ)).mono' hterm.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun z => by
    have hb := hUnit z
    simpa only [Real.norm_eq_abs, abs_of_nonneg hb.1] using hb.2

theorem actualPostRawKOmegaUpperCharge_integrable
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p) :
    Integrable (actualPostRawKOmegaUpperCharge rate rewards C_star C_h)
      (sourceInputLaw p) := by
  unfold actualPostRawKOmegaUpperCharge
  apply integrable_finsetSum Finset.univ
  intro t ht
  let F := ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0
  have hterm : Measurable (fun z : BootstrapPrivateRoundStreams.SourceInput p =>
      (if (postRawKStoppedPendingSet rate rewards C_star C_h t z).Nonempty
        then (1 : ℝ) else 0) *
        postRawKReleaseOmega rate rewards C_star C_h t z) := by
    have hactive : MeasurableSet[F (t.val + 1)]
        {z : BootstrapPrivateRoundStreams.SourceInput p |
          (postRawKStoppedPendingSet rate rewards C_star C_h t z).Nonempty} :=
      stoppedPending_nonempty_measurable_preRound rate rewards C_star C_h control0 t
    have hactive' : MeasurableSet
        {z : BootstrapPrivateRoundStreams.SourceInput p |
          (postRawKStoppedPendingSet rate rewards C_star C_h t z).Nonempty} :=
      F.le (t.val + 1) _ hactive
    have hmask : Measurable (fun z : BootstrapPrivateRoundStreams.SourceInput p =>
        if (postRawKStoppedPendingSet rate rewards C_star C_h t z).Nonempty
        then (1 : ℝ) else 0) :=
      measurable_const.ite hactive' measurable_const
    have hOmega : Measurable
        (postRawKReleaseOmega rate rewards C_star C_h t) :=
      (postRawKReleaseOmega_measurable_preChoice
        rate rewards C_star C_h control0 t).mono (F.le (t.val + 1)) le_rfl
    exact hmask.mul hOmega
  have hUnit : ∀ z : BootstrapPrivateRoundStreams.SourceInput p,
      (if (postRawKStoppedPendingSet rate rewards C_star C_h t z).Nonempty
        then (1 : ℝ) else 0) *
        postRawKReleaseOmega rate rewards C_star C_h t z ∈
          Set.Icc (0 : ℝ) 1 := by
    intro z
    by_cases hp : (postRawKStoppedPendingSet rate rewards C_star C_h t z).Nonempty
    · simpa [hp, Set.mem_Icc] using
        postRawKReleaseOmega_bounds rate rewards C_star C_h t z
    · simp [hp, Set.mem_Icc]
  apply (integrable_const (1 : ℝ)).mono' hterm.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun z => by
    have hb := hUnit z
    simpa only [Real.norm_eq_abs, abs_of_nonneg hb.1] using hb.2

private theorem stoppedSignedDataRound_integrable
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p) (t : Fin p.T) :
    Integrable
      (fun z : BootstrapPrivateRoundStreams.SourceInput p =>
        ∑ i : Fin (p.m - 1), stoppedAssignedChi rate rewards C_star C_h t i z)
      (sourceInputLaw p) := by
  apply integrable_finsetSum Finset.univ
  intro i hi
  exact stoppedAssignedChi_integrable rate rewards C_star C_h control0 t i

/-- The localized signed inequality on every set in the actual
post-rawK phase-start sigma algebra. -/
theorem actualPostRawKSignedReleaseDeficitCharge_setIntegral_bound
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p)
    (B : Set (BootstrapPrivateRoundStreams.SourceInput p))
    (hB : MeasurableSet[
      PhaseStartConditionalWaiting.phaseStartSigmaAlgebra
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0)
        (postRawKReleaseSigma rate rewards C_star C_h)
        (postRawKRelease_sigma_stopping rate rewards C_star C_h control0)] B) :
    ∫ z in B,
        actualPostRawKSignedReleaseDeficitCharge rate rewards C_star C_h z
          ∂sourceInputLaw p ≤
      ∫ z in B,
        actualPostRawKDataWaitingCharge rate rewards C_star C_h z ∂sourceInputLaw p +
      ∫ z in B,
        actualPostRawKOmegaUpperCharge rate rewards C_star C_h z ∂sourceInputLaw p := by
  let μ := sourceInputLaw p
  let F := ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0
  let sigma := postRawKReleaseSigma rate rewards C_star C_h
  let theta := postRawKReleaseTheta rate rewards C_star C_h
  let hsigma := postRawKRelease_sigma_stopping rate rewards C_star C_h control0
  have hBambient : MeasurableSet B :=
    (PhaseStartConditionalWaiting.phaseStartSigmaAlgebra_le F sigma hsigma) B hB
  have hSignedSum :
      ∫ z in B, actualPostRawKSignedReleaseDeficitCharge rate rewards C_star C_h z ∂μ =
        ∑ t : Fin p.T,
          ∫ z in B,
            postRawKStoppedSignedReleaseDeficit rate rewards C_star C_h t z ∂μ := by
    unfold actualPostRawKSignedReleaseDeficitCharge
    rw [integral_finsetSum]
    intro t ht
    exact (postRawKStoppedSignedReleaseDeficit_integrable
      rate rewards C_star C_h control0 t).integrableOn
  have hDataSum :
      ∫ z in B, actualPostRawKDataWaitingCharge rate rewards C_star C_h z ∂μ =
        ∑ t : Fin p.T,
          ∫ z in B,
            (∑ i : Fin (p.m - 1), stoppedAssignedChi rate rewards C_star C_h t i z) ∂μ := by
    classical
    calc
      _ = ∑ i : Fin (p.m - 1),
            ∫ z in B,
              (∑ t : Fin p.T, stoppedAssignedChi rate rewards C_star C_h t i z) ∂μ := by
          unfold actualPostRawKDataWaitingCharge
          rw [integral_finsetSum]
          intro i hi
          apply integrable_finsetSum Finset.univ
          intro t ht
          exact (stoppedAssignedChi_integrable
            rate rewards C_star C_h control0 t i).integrableOn
      _ = ∑ i : Fin (p.m - 1), ∑ t : Fin p.T,
            ∫ z in B, stoppedAssignedChi rate rewards C_star C_h t i z ∂μ := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [integral_finsetSum]
          intro t ht
          exact (stoppedAssignedChi_integrable
            rate rewards C_star C_h control0 t i).integrableOn
      _ = ∑ t : Fin p.T, ∑ i : Fin (p.m - 1),
            ∫ z in B, stoppedAssignedChi rate rewards C_star C_h t i z ∂μ :=
          Finset.sum_comm
      _ = _ := by
          apply Finset.sum_congr rfl
          intro t ht
          rw [integral_finsetSum]
          intro i hi
          exact (stoppedAssignedChi_integrable
            rate rewards C_star C_h control0 t i).integrableOn
  have hOmegaSum :
      ∑ t : Fin p.T,
          ∫ z in B,
            (if (postRawKStoppedPendingSet rate rewards C_star C_h t z).Nonempty
              then (1 : ℝ) else 0) *
              postRawKReleaseOmega rate rewards C_star C_h t z ∂μ =
        ∫ z in B, actualPostRawKOmegaUpperCharge rate rewards C_star C_h z ∂μ := by
    classical
    symm
    unfold actualPostRawKOmegaUpperCharge
    rw [integral_finsetSum]
    intro t ht
    exact stoppedOmegaUpperRound_integrable rate rewards C_star C_h control0 t |>.integrableOn
  have hRoundBound (t : Fin p.T) :
      ∫ z in B, postRawKStoppedSignedReleaseDeficit rate rewards C_star C_h t z ∂μ ≤
        ∫ z in B,
          (∑ i : Fin (p.m - 1), stoppedAssignedChi rate rewards C_star C_h t i z) ∂μ +
        ∫ z in B,
          (if (postRawKStoppedPendingSet rate rewards C_star C_h t z).Nonempty
            then (1 : ℝ) else 0) *
            postRawKReleaseOmega rate rewards C_star C_h t z ∂μ := by
    let P := stoppedPendingProcess rate rewards C_star C_h
    let A : Set (BootstrapPrivateRoundStreams.SourceInput p) :=
      {z | (postRawKStoppedPendingSet rate rewards C_star C_h t z).Nonempty}
    let E : Set (BootstrapPrivateRoundStreams.SourceInput p) := B ∩ A
    let n := t.val
    let f := postRawKStoppedSignedReleaseDeficit rate rewards C_star C_h t
    let data := fun z : BootstrapPrivateRoundStreams.SourceInput p =>
      ∑ i : Fin (p.m - 1), stoppedAssignedChi rate rewards C_star C_h t i z
    let up := fun z : BootstrapPrivateRoundStreams.SourceInput p =>
      (if (postRawKStoppedPendingSet rate rewards C_star C_h t z).Nonempty
        then (1 : ℝ) else 0) *
        postRawKReleaseOmega rate rewards C_star C_h t z
    have hn : n < p.T := t.isLt
    have hP : ∀ i j, j < p.T →
        MeasurableSet[F (j + 1)] {z | i ∈ P j z} := by
      intro i j hj
      let tj : Fin p.T := ⟨j, hj⟩
      simpa [P, stoppedPendingProcess, tj, hj] using
        postRawKStoppedPendingSet_mem_measurable_preRound
          rate rewards C_star C_h control0 tj i
    have hphase : ∀ j, j < p.T → ∀ z, (P j z).Nonempty →
        sigma z ≤ j + 1 ∧ j + 1 < theta z := by
      intro j hj z hactive
      let tj : Fin p.T := ⟨j, hj⟩
      have hcurrent :
          (postRawKStoppedPendingSet rate rewards C_star C_h tj z).Nonempty := by
        simpa [P, stoppedPendingProcess, tj, hj] using hactive
      obtain ⟨i, hi⟩ := hcurrent
      have hdate :=
        (postRawKStoppedPendingSet_mem_iff rate rewards C_star C_h tj z i).mp hi |>.1
      have hsupported : tj.val + 1 ∈ postRawKStoppedSupport rate rewards C_star C_h z :=
        (postRawKStoppedSupport_mem_iff rate rewards C_star C_h z (tj.val + 1)).mpr
          ⟨tj, hdate, rfl⟩
      have hinterval :=
        (postRawKRelease_interval rate rewards C_star C_h control0 z).1
      rw [hinterval, Finset.mem_Ico] at hsupported
      simpa [sigma, theta, tj] using hsupported
    have hE : MeasurableSet[F (t.val + 1)] E := by
      dsimp [E, A]
      simpa [P, stoppedPendingProcess, n, t.isLt] using
        (PhaseStartConditionalWaiting.phaseStart_inter_active_measurable
          F P sigma theta hsigma hP hphase B hB n hn)
    have hEambient : MeasurableSet E := F.le (t.val + 1) E hE
    have hDiff : MeasurableSet (B \ E) := hBambient.diff hEambient
    have hFint : Integrable f μ :=
      postRawKStoppedSignedReleaseDeficit_integrable
        rate rewards C_star C_h control0 t
    have hDataInt : Integrable data μ :=
      stoppedSignedDataRound_integrable rate rewards C_star C_h control0 t
    have hUpInt : Integrable up μ := by
      have hactive : MeasurableSet[F (t.val + 1)]
          {z : BootstrapPrivateRoundStreams.SourceInput p |
            (postRawKStoppedPendingSet rate rewards C_star C_h t z).Nonempty} :=
        stoppedPending_nonempty_measurable_preRound rate rewards C_star C_h control0 t
      have hactive' : MeasurableSet
          {z : BootstrapPrivateRoundStreams.SourceInput p |
            (postRawKStoppedPendingSet rate rewards C_star C_h t z).Nonempty} :=
        F.le (t.val + 1) _ hactive
      have hmask : Measurable (fun z : BootstrapPrivateRoundStreams.SourceInput p =>
          if (postRawKStoppedPendingSet rate rewards C_star C_h t z).Nonempty
          then (1 : ℝ) else 0) :=
        measurable_const.ite hactive' measurable_const
      have hOmega : Measurable
          (postRawKReleaseOmega rate rewards C_star C_h t) :=
        (postRawKReleaseOmega_measurable_preChoice
          rate rewards C_star C_h control0 t).mono (F.le (t.val + 1)) le_rfl
      have hUpMeas : Measurable up := by
        dsimp [up]
        exact hmask.mul hOmega
      have hUnit : ∀ z : BootstrapPrivateRoundStreams.SourceInput p,
          up z ∈ Set.Icc (0 : ℝ) 1 := by
        intro z
        by_cases hpending :
            (postRawKStoppedPendingSet rate rewards C_star C_h t z).Nonempty
        · simpa [up, hpending, Set.mem_Icc] using
            postRawKReleaseOmega_bounds rate rewards C_star C_h t z
        · simp [up, hpending, Set.mem_Icc]
      exact (integrable_const (μ := μ) (1 : ℝ)).mono'
        hUpMeas.aestronglyMeasurable
        (Filter.Eventually.of_forall fun z => by
        have hb := hUnit z
        simpa only [Real.norm_eq_abs, abs_of_nonneg hb.1] using hb.2)
    have hnotActive (z : BootstrapPrivateRoundStreams.SourceInput p)
        (hz : z ∈ B \ E) : ¬ (postRawKStoppedPendingSet rate rewards C_star C_h t z).Nonempty := by
      intro hactive
      exact hz.2 ⟨hz.1, hactive⟩
    have hPendingEmpty (z : BootstrapPrivateRoundStreams.SourceInput p)
        (hz : z ∈ B \ E) : postRawKStoppedPendingSet rate rewards C_star C_h t z = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp (hnotActive z hz)
    have hSignedNonpos (z : BootstrapPrivateRoundStreams.SourceInput p)
        (hz : z ∈ B \ E) : f z ≤ 0 :=
      postRawKStoppedSignedReleaseDeficit_nonpos_of_empty
        rate rewards C_star C_h control0 t z (hPendingEmpty z hz)
    have hDataZero (z : BootstrapPrivateRoundStreams.SourceInput p)
        (hz : z ∈ B \ E) : data z = 0 := by
      unfold data
      apply Finset.sum_eq_zero
      intro i hi
      have hip : i ∉ postRawKStoppedPendingSet rate rewards C_star C_h t z := by
        rw [hPendingEmpty z hz]
        simp
      simp [stoppedAssignedChi, hip]
    have hUpZero (z : BootstrapPrivateRoundStreams.SourceInput p)
        (hz : z ∈ B \ E) : up z = 0 := by
      simp [up, hnotActive z hz]
    have hDataB : ∫ z in B, data z ∂μ = ∫ z in E, data z ∂μ :=
      setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hBambient
        Set.inter_subset_left hDataZero
    have hUpB : ∫ z in B, up z ∂μ = ∫ z in E, up z ∂μ :=
      setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hBambient
        Set.inter_subset_left hUpZero
    have hComplement : ∫ z in B \ E, f z ∂μ ≤ 0 := by
      calc
        _ ≤ ∫ z in B \ E, (fun _ : BootstrapPrivateRoundStreams.SourceInput p => (0 : ℝ)) z ∂μ :=
          setIntegral_mono_on hFint.integrableOn (integrable_const (0 : ℝ)).integrableOn
            hDiff hSignedNonpos
        _ = 0 := by simp
    have hSplit : ∫ z in B, f z ∂μ =
        ∫ z in E, f z ∂μ + ∫ z in B \ E, f z ∂μ := by
      have hFintB : IntegrableOn f B μ := hFint.integrableOn
      have hdiff := setIntegral_sdiff (s := B) (t := E)
        hEambient hFintB Set.inter_subset_left
      linarith
    have hOneRound : ∫ z in E, f z ∂μ ≤
        ∫ z in E, data z ∂μ + ∫ z in E, up z ∂μ := by
      have hcond :
          μ[f | F (t.val + 1)] ≤ᵐ[μ] fun z => data z + up z := by
        filter_upwards [postRawKStoppedSignedReleaseDeficit_condExp_le
            rate rewards C_star C_h control0] with z hz
        simpa [f, data, up] using hz t
      calc
        _ = ∫ z in E, μ[f | F (t.val + 1)] z ∂μ := by
          symm
          exact setIntegral_condExp (F.le (t.val + 1)) hFint hE
        _ ≤ ∫ z in E, (data z + up z) ∂μ :=
          setIntegral_mono_ae integrable_condExp.integrableOn
            (hDataInt.add hUpInt).integrableOn hcond
        _ = ∫ z in E, data z ∂μ + ∫ z in E, up z ∂μ :=
          integral_add hDataInt.integrableOn hUpInt.integrableOn
    calc
      _ = ∫ z in E, f z ∂μ + ∫ z in B \ E, f z ∂μ := hSplit
      _ ≤ ∫ z in E, f z ∂μ := by linarith
      _ ≤ ∫ z in E, data z ∂μ + ∫ z in E, up z ∂μ := hOneRound
      _ = ∫ z in B, data z ∂μ + ∫ z in B, up z ∂μ := by rw [← hDataB, ← hUpB]
  calc
    _ = ∑ t : Fin p.T,
          ∫ z in B,
            postRawKStoppedSignedReleaseDeficit rate rewards C_star C_h t z ∂μ := hSignedSum
    _ ≤ ∑ t : Fin p.T,
          (∫ z in B,
            (∑ i : Fin (p.m - 1), stoppedAssignedChi rate rewards C_star C_h t i z) ∂μ +
           ∫ z in B,
            (if (postRawKStoppedPendingSet rate rewards C_star C_h t z).Nonempty
              then (1 : ℝ) else 0) *
              postRawKReleaseOmega rate rewards C_star C_h t z ∂μ) :=
      Finset.sum_le_sum fun t _ => hRoundBound t
    _ = (∑ t : Fin p.T,
          ∫ z in B,
            (∑ i : Fin (p.m - 1), stoppedAssignedChi rate rewards C_star C_h t i z) ∂μ) +
        ∑ t : Fin p.T,
          ∫ z in B,
            (if (postRawKStoppedPendingSet rate rewards C_star C_h t z).Nonempty
              then (1 : ℝ) else 0) *
              postRawKReleaseOmega rate rewards C_star C_h t z ∂μ := by
        rw [Finset.sum_add_distrib]
    _ = ∫ z in B, actualPostRawKDataWaitingCharge rate rewards C_star C_h z ∂μ +
        ∫ z in B, actualPostRawKOmegaUpperCharge rate rewards C_star C_h z ∂μ := by
        rw [← hDataSum, hOmegaSum]

/-- The localized set-integral inequality gives the conditional inequality on
the very same actual phase-start sigma algebra. -/
theorem actualPostRawKSignedReleaseDeficitCharge_condExp_bound
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p) :
    (sourceInputLaw p)[
      actualPostRawKSignedReleaseDeficitCharge rate rewards C_star C_h |
        PhaseStartConditionalWaiting.phaseStartSigmaAlgebra
          (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0)
          (postRawKReleaseSigma rate rewards C_star C_h)
          (postRawKRelease_sigma_stopping rate rewards C_star C_h control0)] ≤ᵐ[sourceInputLaw p]
      fun z =>
        (sourceInputLaw p)[actualPostRawKDataWaitingCharge rate rewards C_star C_h |
          PhaseStartConditionalWaiting.phaseStartSigmaAlgebra
            (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0)
            (postRawKReleaseSigma rate rewards C_star C_h)
            (postRawKRelease_sigma_stopping rate rewards C_star C_h control0)] z +
        (sourceInputLaw p)[actualPostRawKOmegaUpperCharge rate rewards C_star C_h |
          PhaseStartConditionalWaiting.phaseStartSigmaAlgebra
            (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0)
            (postRawKReleaseSigma rate rewards C_star C_h)
            (postRawKRelease_sigma_stopping rate rewards C_star C_h control0)] z := by
  let μ := sourceInputLaw p
  let F := ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0
  let sigma := postRawKReleaseSigma rate rewards C_star C_h
  let hsigma := postRawKRelease_sigma_stopping rate rewards C_star C_h control0
  let mSigma := PhaseStartConditionalWaiting.phaseStartSigmaAlgebra F sigma hsigma
  have hSignedInt := actualPostRawKSignedReleaseDeficitCharge_integrable
    rate rewards C_star C_h control0
  have hDataInt := actualPostRawKDataWaitingCharge_integrable
    rate rewards C_star C_h control0
  have hOmegaInt := actualPostRawKOmegaUpperCharge_integrable
    rate rewards C_star C_h control0
  have hdiffInt : Integrable
      (fun z => actualPostRawKSignedReleaseDeficitCharge rate rewards C_star C_h z -
        actualPostRawKDataWaitingCharge rate rewards C_star C_h z -
        actualPostRawKOmegaUpperCharge rate rewards C_star C_h z) μ :=
    (hSignedInt.sub hDataInt).sub hOmegaInt
  have hset : ∀ B, MeasurableSet[mSigma] B →
      ∫ z in B,
        (actualPostRawKSignedReleaseDeficitCharge rate rewards C_star C_h z -
          actualPostRawKDataWaitingCharge rate rewards C_star C_h z -
          actualPostRawKOmegaUpperCharge rate rewards C_star C_h z) ∂μ ≤ 0 := by
    intro B hB
    have hbound := actualPostRawKSignedReleaseDeficitCharge_setIntegral_bound
      rate rewards C_star C_h control0 B hB
    have hsub :
        ∫ z in B,
          (actualPostRawKSignedReleaseDeficitCharge rate rewards C_star C_h z -
            actualPostRawKDataWaitingCharge rate rewards C_star C_h z -
            actualPostRawKOmegaUpperCharge rate rewards C_star C_h z) ∂μ =
          (∫ z in B,
            actualPostRawKSignedReleaseDeficitCharge rate rewards C_star C_h z ∂μ) -
          (∫ z in B,
            actualPostRawKDataWaitingCharge rate rewards C_star C_h z ∂μ) -
          (∫ z in B,
            actualPostRawKOmegaUpperCharge rate rewards C_star C_h z ∂μ) := by
      calc
        _ = (∫ z in B,
              (actualPostRawKSignedReleaseDeficitCharge rate rewards C_star C_h z -
                actualPostRawKDataWaitingCharge rate rewards C_star C_h z) ∂μ) -
              ∫ z in B,
                actualPostRawKOmegaUpperCharge rate rewards C_star C_h z ∂μ :=
          integral_sub ((hSignedInt.sub hDataInt).integrableOn) hOmegaInt.integrableOn
        _ = _ := by
          rw [integral_sub hSignedInt.integrableOn hDataInt.integrableOn]
    rw [hsub]
    linarith
  have hcond := (PhaseStartConditionalWaiting.setIntegral_iff_condExp_le μ mSigma
    (PhaseStartConditionalWaiting.phaseStartSigmaAlgebra_le F sigma hsigma)
    (fun z => actualPostRawKSignedReleaseDeficitCharge rate rewards C_star C_h z -
      actualPostRawKDataWaitingCharge rate rewards C_star C_h z -
      actualPostRawKOmegaUpperCharge rate rewards C_star C_h z)
    0 hdiffInt).1 (fun B hB => by simpa using hset B hB)
  have hfun :
      (fun z => actualPostRawKSignedReleaseDeficitCharge rate rewards C_star C_h z -
        actualPostRawKDataWaitingCharge rate rewards C_star C_h z -
        actualPostRawKOmegaUpperCharge rate rewards C_star C_h z) =
      actualPostRawKSignedReleaseDeficitCharge rate rewards C_star C_h -
        actualPostRawKDataWaitingCharge rate rewards C_star C_h -
        actualPostRawKOmegaUpperCharge rate rewards C_star C_h := by
    funext z
    simp only [Pi.sub_apply]
  have hcond' :
      μ[actualPostRawKSignedReleaseDeficitCharge rate rewards C_star C_h -
        actualPostRawKDataWaitingCharge rate rewards C_star C_h -
        actualPostRawKOmegaUpperCharge rate rewards C_star C_h | mSigma] ≤ᵐ[μ]
        (fun z => 0) := by
    simpa only [hfun] using hcond
  have hsub1 := condExp_sub hSignedInt hDataInt (m := mSigma)
  have hsub2 := condExp_sub (hSignedInt.sub hDataInt) hOmegaInt (m := mSigma)
  have hceAlgebra :
      (fun z => μ[(actualPostRawKSignedReleaseDeficitCharge rate rewards C_star C_h -
          actualPostRawKDataWaitingCharge rate rewards C_star C_h -
          actualPostRawKOmegaUpperCharge rate rewards C_star C_h) | mSigma] z) =ᵐ[μ]
        (fun z => μ[actualPostRawKSignedReleaseDeficitCharge rate rewards C_star C_h | mSigma] z -
          μ[actualPostRawKDataWaitingCharge rate rewards C_star C_h | mSigma] z -
          μ[actualPostRawKOmegaUpperCharge rate rewards C_star C_h | mSigma] z) := by
    filter_upwards [hsub1, hsub2] with z hsub1z hsub2z
    calc
      _ = μ[(actualPostRawKSignedReleaseDeficitCharge rate rewards C_star C_h -
            actualPostRawKDataWaitingCharge rate rewards C_star C_h) | mSigma] z -
          μ[actualPostRawKOmegaUpperCharge rate rewards C_star C_h | mSigma] z := by
            simpa [μ] using hsub2z
      _ = _ := by
        simpa [μ] using hsub1z
  change μ[actualPostRawKSignedReleaseDeficitCharge rate rewards C_star C_h | mSigma] ≤ᵐ[μ]
    fun z => μ[actualPostRawKDataWaitingCharge rate rewards C_star C_h | mSigma] z +
      μ[actualPostRawKOmegaUpperCharge rate rewards C_star C_h | mSigma] z
  filter_upwards [hcond', hceAlgebra] with z hz halgebra
  rw [halgebra] at hz
  linarith

/-- Consume the accepted DATA waiting bound and retain the literal actual
omega upper charge in the conditional result. -/
theorem actualPostRawKSignedReleaseDeficitCharge_condExp_data_bound
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p) :
    (sourceInputLaw p)[
      actualPostRawKSignedReleaseDeficitCharge rate rewards C_star C_h |
        PhaseStartConditionalWaiting.phaseStartSigmaAlgebra
          (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0)
          (postRawKReleaseSigma rate rewards C_star C_h)
          (postRawKRelease_sigma_stopping rate rewards C_star C_h control0)] ≤ᵐ[sourceInputLaw p]
      fun z => 2 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) +
        (sourceInputLaw p)[actualPostRawKOmegaUpperCharge rate rewards C_star C_h |
          PhaseStartConditionalWaiting.phaseStartSigmaAlgebra
            (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0)
            (postRawKReleaseSigma rate rewards C_star C_h)
            (postRawKRelease_sigma_stopping rate rewards C_star C_h control0)] z := by
  let μ := sourceInputLaw p
  let F := ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0
  let sigma := postRawKReleaseSigma rate rewards C_star C_h
  let hsigma := postRawKRelease_sigma_stopping rate rewards C_star C_h control0
  let mSigma := PhaseStartConditionalWaiting.phaseStartSigmaAlgebra F sigma hsigma
  have hTower := actualPostRawKSignedReleaseDeficitCharge_condExp_bound
    rate rewards C_star C_h control0
  have hData := actualPostRawKDataWaitingCharge_condExp_bound
    rate rewards C_star C_h control0
  change μ[actualPostRawKSignedReleaseDeficitCharge rate rewards C_star C_h | mSigma] ≤ᵐ[μ]
    fun z => μ[actualPostRawKDataWaitingCharge rate rewards C_star C_h | mSigma] z +
      μ[actualPostRawKOmegaUpperCharge rate rewards C_star C_h | mSigma] z at hTower
  change μ[actualPostRawKDataWaitingCharge rate rewards C_star C_h | mSigma] ≤ᵐ[μ]
    fun _ => 2 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) at hData
  filter_upwards [hTower, hData] with z hz hdz
  calc
    (sourceInputLaw p)[actualPostRawKSignedReleaseDeficitCharge rate rewards C_star C_h |
        PhaseStartConditionalWaiting.phaseStartSigmaAlgebra
          (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0)
          (postRawKReleaseSigma rate rewards C_star C_h)
          (postRawKRelease_sigma_stopping rate rewards C_star C_h control0)] z ≤
        (sourceInputLaw p)[actualPostRawKDataWaitingCharge rate rewards C_star C_h |
          PhaseStartConditionalWaiting.phaseStartSigmaAlgebra
            (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0)
            (postRawKReleaseSigma rate rewards C_star C_h)
            (postRawKRelease_sigma_stopping rate rewards C_star C_h control0)] z +
          (sourceInputLaw p)[actualPostRawKOmegaUpperCharge rate rewards C_star C_h |
            PhaseStartConditionalWaiting.phaseStartSigmaAlgebra
              (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0)
              (postRawKReleaseSigma rate rewards C_star C_h)
              (postRawKRelease_sigma_stopping rate rewards C_star C_h control0)] z := hz
    _ ≤ 2 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) +
        (sourceInputLaw p)[actualPostRawKOmegaUpperCharge rate rewards C_star C_h |
          PhaseStartConditionalWaiting.phaseStartSigmaAlgebra
            (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0)
            (postRawKReleaseSigma rate rewards C_star C_h)
            (postRawKRelease_sigma_stopping rate rewards C_star C_h control0)] z :=
      add_le_add_left hdz
        ((sourceInputLaw p)[actualPostRawKOmegaUpperCharge rate rewards C_star C_h |
          PhaseStartConditionalWaiting.phaseStartSigmaAlgebra
            (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0)
            (postRawKReleaseSigma rate rewards C_star C_h)
            (postRawKRelease_sigma_stopping rate rewards C_star C_h control0)] z)

/-- Empty stopped support uses the actual `T+1` sentinel and all three literal
charges vanish. -/
theorem actualPostRawKCharges_zero_of_empty_support
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hempty : postRawKStoppedSupport rate rewards C_star C_h z = ∅) :
    postRawKReleaseSigma rate rewards C_star C_h z = p.T + 1 ∧
      postRawKReleaseTheta rate rewards C_star C_h z = p.T + 1 ∧
      actualPostRawKSignedReleaseDeficitCharge rate rewards C_star C_h z = 0 ∧
      actualPostRawKDataWaitingCharge rate rewards C_star C_h z = 0 ∧
      actualPostRawKOmegaUpperCharge rate rewards C_star C_h z = 0 := by
  have hendpoints := postRawKRelease_endpoints_empty
    rate rewards C_star C_h z hempty
  have hnotDate (t : Fin p.T) : ¬ postRawKStoppedDate rate rewards C_star C_h t z := by
    intro hdate
    have hsupported : t.val + 1 ∈ postRawKStoppedSupport rate rewards C_star C_h z :=
      (postRawKStoppedSupport_mem_iff rate rewards C_star C_h z (t.val + 1)).mpr
        ⟨t, hdate, rfl⟩
    rw [hempty] at hsupported
    simp at hsupported
  have hpending (t : Fin p.T) : postRawKStoppedPendingSet rate rewards C_star C_h t z = ∅ :=
    postRawKStoppedPendingSet_eq_empty_of_not_kept
      rate rewards C_star C_h t z (hnotDate t)
  refine ⟨hendpoints.1, hendpoints.2, ?_, ?_, ?_⟩
  · unfold actualPostRawKSignedReleaseDeficitCharge
    apply Finset.sum_eq_zero
    intro t ht
    simp [ReferencePostReplacementCollectionSentinelSectionLaw.postRawKStoppedSignedReleaseDeficit,
      hnotDate t]
  · unfold actualPostRawKDataWaitingCharge
    apply Finset.sum_eq_zero
    intro i hi
    apply Finset.sum_eq_zero
    intro t ht
    have hip : i ∉ postRawKStoppedPendingSet rate rewards C_star C_h t z := by
      rw [hpending t]
      simp
    simp [stoppedAssignedChi, hip]
  · unfold actualPostRawKOmegaUpperCharge
    apply Finset.sum_eq_zero
    intro t ht
    simp [hpending t]

end Bandits.Support.ReferencePostReplacementCollectionStoppedSignedTowerReduction

end noncomputable section
