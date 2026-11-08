/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferencePostReplacementCollectionReleaseResamplingData

import Mathlib.Tactic

/-!
# Conditional waiting cost for stopped post-rawK DATA releases

The charge is the finite sum of the actual stopped assigned-arm coefficients
under the original source-input law. Each follower is treated as its own
one-task process, with its own incoming assignment and assigned arm.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ContinuousLearningRows
open Bandits.Support.PhaseServiceWaiting
open Bandits.Support.PhaseStartConditionalWaiting
open Bandits.Support.ReferencePostReplacementCollectionReleaseResamplingData
open Bandits.Support.ReferencePostReplacementCollectionStoppedReleaseAdaptation
open Bandits.Support.ReferenceSourcePrefixHistoryFiltration
open Bandits.Support.ReferenceLocalReleaseWaitingPaths
open scoped Classical BigOperators

namespace Bandits.Support.ReferencePostReplacementCollectionDataWaitingCost

variable {p : ConstructorDimensions.Parameters}

/-- The literal finite sum of the assigned chi coefficients on every source
date and every original follower. Each summand already vanishes off the
stopped pending support. -/
def actualPostRawKDataWaitingCharge
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) : ℝ :=
  ∑ i : Fin (p.m - 1),
    ∑ t : Fin p.T, stoppedAssignedChi rate rewards C_star C_h t i z

private def dataTaskSet
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) :
    ℕ → BootstrapPrivateRoundStreams.SourceInput p → Finset (Fin 1) :=
  fun n z => if hn : n < p.T then
    if i ∈ postRawKStoppedPendingSet rate rewards C_star C_h ⟨n, hn⟩ z then
      {⟨0, by omega⟩}
    else ∅
  else ∅

private def dataTaskObservation
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) :
    Fin 1 → ℕ → BootstrapPrivateRoundStreams.SourceInput p → Bool :=
  fun _ n z => if hn : n < p.T then
    actualData rate rewards C_star C_h i ⟨n, hn⟩ z
  else false

private def dataTaskWeight
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) :
    ℕ → BootstrapPrivateRoundStreams.SourceInput p → ℝ :=
  fun n z => if hn : n < p.T then
    stoppedAssignedChi rate rewards C_star C_h ⟨n, hn⟩ i z
  else 0

abbrev dataTaskStart
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) : BootstrapPrivateRoundStreams.SourceInput p → ℕ :=
  postRawKReleaseSigma rate rewards C_star C_h

private def dataTaskEnd
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) : BootstrapPrivateRoundStreams.SourceInput p → ℕ :=
  postRawKReleaseTheta rate rewards C_star C_h

def dataTaskFollowerCharge
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1))
    (z : BootstrapPrivateRoundStreams.SourceInput p) : ℝ :=
  ∑ t : Fin p.T, stoppedAssignedChi rate rewards C_star C_h t i z

private theorem stoppedDate_source_start_le
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hkeep : postRawKStoppedDate rate rewards C_star C_h t z) :
    ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h ≤ t.val := by
  have hrel : ReferencePostReplacementCollectionReleaseSupport.rawReleaseRecords
      rate rewards C_star C_h z ≠ [] := by
    intro hnil
    obtain ⟨r, hr, _⟩ :=
      (ReferencePostReplacementCollectionReleaseSupport.rawReleaseRecords_support_iff
        rate rewards C_star C_h z t).mpr hkeep.1
    rw [hnil] at hr
    simp at hr
  obtain ⟨_, _, _, _, _, _, _, hdates⟩ :=
    postRawKReleaseSupport_inherited_prefix rate rewards C_star C_h control0 z hrel
  exact (hdates t hkeep.1).1

private theorem dataTaskSet_mem_iff
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (n : ℕ) (hn : n < p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (j : Fin 1) :
    j ∈ dataTaskSet rate rewards C_star C_h i n z ↔
      j = ⟨0, by omega⟩ ∧
        i ∈ postRawKStoppedPendingSet rate rewards C_star C_h ⟨n, hn⟩ z := by
  have hj : j = ⟨0, by omega⟩ := Fin.ext (by have := j.isLt; omega)
  subst j
  simp only [dataTaskSet, dif_pos hn]
  by_cases hp : i ∈ postRawKStoppedPendingSet rate rewards C_star C_h ⟨n, hn⟩ z
  · simp [hp]
  · simp [hp]

private theorem stoppedPending_localTask_mem
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s b : ℕ)
    (source : ReferenceLocalReleaseWaitingPaths.SourceEvent
      rate rewards C_star C_h s)
    (theta : ReferenceLocalReleaseWaitingPaths.SourceEvent
      rate rewards C_star C_h s → ℕ)
    (horizon : s ≤ p.T)
    (htheta : ∀ x, 1 ≤ theta x ∧ theta x ≤ p.T + 1)
    (i : Fin (p.m - 1)) (t : Fin p.T)
    (hst : s ≤ t.val) (hcut : t.val + 1 < theta source)
    (hpending : i ∈ ReferenceSourcePrefixHistoryFiltration.pending
      rate rewards C_star C_h b t source.val) :
    i ∈ pendingTheta rate rewards C_star C_h s horizon b theta t.val source := by
  have hcalendar := ReferenceSourcePrefixHistoryFiltration.pending_source_calendar
    rate rewards C_star C_h b t s hst source
  rw [pendingTheta, if_pos hcut]
  rw [← hcalendar]
  exact hpending

private theorem stoppedPending_localDataObservation_eq
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s b : ℕ)
    (source : ReferenceLocalReleaseWaitingPaths.SourceEvent
      rate rewards C_star C_h s)
    (horizon : s ≤ p.T) (i : Fin (p.m - 1)) (t : Fin p.T) (hst : s ≤ t.val) :
    actualData rate rewards C_star C_h i t source.val =
      dataObservation rate rewards C_star C_h s horizon b i t.val source := by
  exact (ReferenceSourcePrefixHistoryFiltration.flags_source_calendar
    rate rewards C_star C_h b i t s hst source).2.1

private theorem localTask_pending_actual_mem
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s b : ℕ)
    (source : ReferenceLocalReleaseWaitingPaths.SourceEvent
      rate rewards C_star C_h s)
    (horizon : s ≤ p.T)
    (t : Fin p.T) (hst : s ≤ t.val)
    (hcut : t.val + 1 < postRawKReleaseTheta rate rewards C_star C_h source.val)
    (i : Fin (p.m - 1))
    (hi : i ∈ pendingTheta rate rewards C_star C_h s horizon b
      (fun x => postRawKReleaseTheta rate rewards C_star C_h x.val) t.val source) :
    i ∈ ReferenceSourcePrefixHistoryFiltration.pending rate rewards C_star C_h b t source.val := by
  have hcalendar := ReferenceSourcePrefixHistoryFiltration.pending_source_calendar
    rate rewards C_star C_h b t s hst source
  have hi' : i ∈
      (ReferenceLocalReleaseWaitingPaths.calendarPendingReadout rate rewards C_star C_h
        s horizon b source t.val).getD ∅ := by
    simpa [ReferenceLocalReleaseWaitingPaths.pendingTheta, hcut] using hi
  rw [hcalendar]
  exact hi'

/-- The actual assigned-chi sum for one fixed original follower has the
phase-start conditional bound from the original DATA law. -/
theorem actualPostRawKDataFollower_condExp_bound
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1)) :
    (BootstrapPrivateRoundStreams.sourceInputLaw p)[
      dataTaskFollowerCharge rate rewards C_star C_h i |
        PhaseStartConditionalWaiting.phaseStartSigmaAlgebra
          (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0)
          (dataTaskStart rate rewards C_star C_h)
          (ReferencePostReplacementCollectionStoppedReleaseAdaptation.postRawKRelease_sigma_stopping
            rate rewards C_star C_h control0)] ≤ᵐ[BootstrapPrivateRoundStreams.sourceInputLaw p]
      fun _ => 2 * (p.K : ℝ) := by
  let μ := BootstrapPrivateRoundStreams.sourceInputLaw p
  let F := ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0
  let P := dataTaskSet rate rewards C_star C_h i
  let X := dataTaskObservation rate rewards C_star C_h i
  let w := dataTaskWeight rate rewards C_star C_h i
  let sigma := dataTaskStart rate rewards C_star C_h
  let theta := dataTaskEnd rate rewards C_star C_h
  let hsigma := ReferencePostReplacementCollectionStoppedReleaseAdaptation.postRawKRelease_sigma_stopping
    rate rewards C_star C_h control0
  let htheta := ReferencePostReplacementCollectionStoppedReleaseAdaptation.postRawKRelease_theta_stopping
    rate rewards C_star C_h control0
  let a : ℝ := 1 / (2 * (p.K : ℝ))
  let i₀ : Fin 1 := ⟨0, by omega⟩
  have hm2 : 2 ≤ p.m := p.two_le_m
  have hm1 : 1 ≤ p.m := by omega
  have hd : 0 < p.m - 1 := by omega
  have hT : 0 < p.T := ConstructorDimensions.T_pos p
  have hK : 0 < p.K := ConstructorDimensions.K_pos p
  have hq : 0 < 1 := by omega
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hstart : ∀ z, 1 ≤ sigma z := by
    intro z
    exact (ReferencePostReplacementCollectionStoppedReleaseAdaptation.postRawKRelease_interval
      rate rewards C_star C_h control0 z).2.1
  have hordered : ∀ z, sigma z ≤ theta z := by
    intro z
    exact (ReferencePostReplacementCollectionStoppedReleaseAdaptation.postRawKRelease_interval
      rate rewards C_star C_h control0 z).2.2.1
  have hthetaBound : ∀ z, theta z ≤ p.T + 1 := by
    intro z
    exact (ReferencePostReplacementCollectionStoppedReleaseAdaptation.postRawKRelease_interval
      rate rewards C_star C_h control0 z).2.2.2
  have hP : ∀ j n, n < p.T →
      MeasurableSet[F (n + 1)] {z | j ∈ P n z} := by
    intro j n hn
    have hj : j = i₀ := Fin.ext (by have := j.isLt; omega)
    subst j
    have hset : {z | i₀ ∈ P n z} =
        {z | i ∈ postRawKStoppedPendingSet rate rewards C_star C_h ⟨n, hn⟩ z} := by
      ext z
      change i₀ ∈ dataTaskSet rate rewards C_star C_h i n z ↔ _
      exact (dataTaskSet_mem_iff rate rewards C_star C_h i n hn z i₀).trans
        (by simp [i₀])
    rw [hset]
    simpa [F] using
      (ReferencePostReplacementCollectionStoppedReleaseAdaptation.postRawKStoppedPendingSet_mem_measurable_preRound
        rate rewards C_star C_h control0 ⟨n, hn⟩ i)
  have hphase : ∀ n, n < p.T → ∀ z, (P n z).Nonempty →
      sigma z ≤ n + 1 ∧ n + 1 < theta z := by
    intro n hn z hne
    let t : Fin p.T := ⟨n, hn⟩
    have hi₀ : i₀ ∈ P n z := by
      have hmem := hne
      obtain ⟨j, hj⟩ := hmem
      have hji : j = i₀ := Fin.ext (by have := j.isLt; omega)
      exact hji ▸ hj
    have hpending : i ∈ postRawKStoppedPendingSet rate rewards C_star C_h t z := by
      have hmem' : i₀ ∈ dataTaskSet rate rewards C_star C_h i n z := by
        simpa [P] using hi₀
      exact ((dataTaskSet_mem_iff rate rewards C_star C_h i n hn z i₀).mp hmem').2
    have hkeep := (postRawKStoppedPendingSet_mem_iff
      rate rewards C_star C_h t z i).mp hpending |>.1
    have hsupport : n + 1 ∈ postRawKStoppedSupport rate rewards C_star C_h z :=
      (postRawKStoppedSupport_mem_iff rate rewards C_star C_h z (n + 1)).mpr
        ⟨t, hkeep, rfl⟩
    have hinterval := (postRawKRelease_interval rate rewards C_star C_h control0 z).1
    rw [hinterval, Finset.mem_Ico] at hsupport
    exact hsupport
  have hwMeas : ∀ n, n < p.T → StronglyMeasurable[F (n + 1)] (w n) := by
    intro n hn
    have hweight : w n = stoppedAssignedChi rate rewards C_star C_h ⟨n, hn⟩ i := by
      funext z
      simp [w, dataTaskWeight, hn]
    rw [hweight]
    change StronglyMeasurable[F (n + 1)]
      (stoppedAssignedChi rate rewards C_star C_h ⟨n, hn⟩ i)
    simpa [F] using
      (stoppedAssignedChi_measurable_preChoice rate rewards C_star C_h control0
        ⟨n, hn⟩ i).stronglyMeasurable
  have hwBound : ∀ n, n < p.T → ∀ z, w n z ∈ Set.Icc (0 : ℝ) (p.K : ℝ) := by
    have hKone : (1 : ℝ) ≤ (p.K : ℝ) := by
      have hKoneNat : 1 ≤ p.K := by omega
      exact_mod_cast hKoneNat
    intro n hn z
    have hb := stoppedAssignedChi_bounds rate rewards C_star C_h ⟨n, hn⟩ i z
    constructor
    · simpa [w, dataTaskWeight, hn] using hb.1
    · exact le_trans (by simpa [w, dataTaskWeight, hn] using hb.2) hKone
  have hXMeas : ∀ j n, n < p.T →
      StronglyMeasurable[F (n + 2)] (PhaseServiceWaiting.observation X j n) := by
    intro j n hn
    have hj : j = i₀ := Fin.ext (by have := j.isLt; omega)
    subst j
    have hobs : PhaseServiceWaiting.observation X i₀ n =
        (fun z => if actualData rate rewards C_star C_h i ⟨n, hn⟩ z then (1 : ℝ) else 0) := by
      funext z
      simp [PhaseServiceWaiting.observation, X, dataTaskObservation, dif_pos hn, i₀]
    rw [hobs]
    change StronglyMeasurable[F (n + 2)]
      (fun z => if actualData rate rewards C_star C_h i ⟨n, hn⟩ z then (1 : ℝ) else 0)
    simpa [F] using
      (ReferenceSourcePrefixHistoryFiltration.flags_stronglyMeasurable
        rate rewards C_star C_h control0 i ⟨n, hn⟩).2.1
  have hQuota : ∀ j n, n < p.T → ∀ z, j ∈ P n z →
      PhaseServiceWaiting.N P X j n z < 1 := by
    intro j n hn z hjpending
    have hj : j = i₀ := Fin.ext (by have := j.isLt; omega)
    subst j
    let t : Fin p.T := ⟨n, hn⟩
    have hpending : i ∈ postRawKStoppedPendingSet rate rewards C_star C_h t z := by
      have hmem' : i₀ ∈ dataTaskSet rate rewards C_star C_h i n z := by
        simpa [P] using hjpending
      exact ((dataTaskSet_mem_iff rate rewards C_star C_h i n hn z i₀).mp hmem').2
    have hkeep := (postRawKStoppedPendingSet_mem_iff
      rate rewards C_star C_h t z i).mp hpending |>.1
    have hrel : ReferencePostReplacementCollectionReleaseSupport.rawReleaseRecords
        rate rewards C_star C_h z ≠ [] := by
      intro hnil
      have hsupport : n + 1 ∈ postRawKStoppedSupport rate rewards C_star C_h z :=
        (postRawKStoppedSupport_mem_iff rate rewards C_star C_h z (n + 1)).mpr
          ⟨t, hkeep, rfl⟩
      rw [postRawKStoppedSupport_empty_of_rawReleaseRecords_empty
        rate rewards C_star C_h z hnil] at hsupport
      simp at hsupport
    obtain ⟨hc, _a, _cutoff, _M, _hcutLow, _hcutHigh, _hstamp, _hrecords, _hread⟩ :=
      postRawKStoppedRecords_source rate rewards C_star C_h control0 z hrel
    let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    let source : ReferenceLocalReleaseWaitingPaths.SourceEvent rate rewards C_star C_h s :=
      ⟨z, hc, rfl⟩
    let thetaLocal : ReferenceLocalReleaseWaitingPaths.SourceEvent rate rewards C_star C_h s → ℕ :=
      fun x => postRawKReleaseTheta rate rewards C_star C_h x.val
    have hthetaLocal : ∀ x, 1 ≤ thetaLocal x ∧ thetaLocal x ≤ p.T + 1 := by
      intro x
      have hi := postRawKRelease_interval rate rewards C_star C_h control0 x.val
      constructor
      · dsimp [thetaLocal]
        exact le_trans hi.2.1 hi.2.2.1
      · dsimp [thetaLocal]
        exact hi.2.2.2
    obtain ⟨u, hut, hu, huPending⟩ :=
      postRawKStoppedPendingDate_same_occurrence rate rewards C_star C_h t i z hkeep
        ((postRawKStoppedPendingSet_mem_iff rate rewards C_star C_h t z i).mp hpending).2
    have hstartSource : s ≤ n :=
      stoppedDate_source_start_le rate rewards C_star C_h control0 t z hkeep
    have hstartHorizon : s ≤ p.T := le_trans hstartSource (Nat.le_of_lt hn)
    have hsupport : n + 1 ∈ postRawKStoppedSupport rate rewards C_star C_h z :=
      (postRawKStoppedSupport_mem_iff rate rewards C_star C_h z (n + 1)).mpr
        ⟨t, hkeep, rfl⟩
    have hthetaCurrent : n + 1 < thetaLocal source := by
      have hI := (postRawKRelease_interval rate rewards C_star C_h control0 z).1
      rw [hI, Finset.mem_Ico] at hsupport
      exact hsupport.2
    have hcurrentLocal : i ∈ pendingTheta rate rewards C_star C_h s hstartHorizon
        u.val thetaLocal n source := by
      apply stoppedPending_localTask_mem rate rewards C_star C_h s u.val source thetaLocal
        hstartHorizon hthetaLocal i t hstartSource hthetaCurrent
      exact huPending.2
    have hstrict := ReferenceLocalReleaseWaitingPaths.strict_prior_N_zero_at_pending
      rate rewards C_star C_h s hstartHorizon u.val thetaLocal hthetaLocal
      source n i hcurrentLocal
    have hNle : PhaseServiceWaiting.N P X i₀ n z ≤
        PhaseServiceWaiting.N
          (ReferenceLocalReleaseWaitingPaths.pendingTheta rate rewards C_star C_h s
            hstartHorizon u.val thetaLocal)
          (ReferenceLocalReleaseWaitingPaths.dataObservation rate rewards C_star C_h s
            hstartHorizon u.val) i n source := by
      unfold PhaseServiceWaiting.N
      apply Finset.sum_le_sum
      intro k hk
      have hklt : k < n := Finset.mem_range.mp hk
      have hkT : k < p.T := by omega
      let tk : Fin p.T := ⟨k, hkT⟩
      by_cases htask : i₀ ∈ P k z
      · have hpendingK : i ∈ postRawKStoppedPendingSet rate rewards C_star C_h tk z := by
          have hmem' : i₀ ∈ dataTaskSet rate rewards C_star C_h i k z := by
            simpa [P] using htask
          exact ((dataTaskSet_mem_iff rate rewards C_star C_h i k hkT z i₀).mp hmem').2
        have hkeepK := (postRawKStoppedPendingSet_mem_iff
          rate rewards C_star C_h tk z i).mp hpendingK |>.1
        have hpendingDateK := (postRawKStoppedPendingSet_mem_iff
          rate rewards C_star C_h tk z i).mp hpendingK |>.2
        obtain ⟨u', hu'lt, hu', hu'Pending⟩ :=
          postRawKStoppedPendingDate_same_occurrence rate rewards C_star C_h tk i z
            hkeepK hpendingDateK
        have huEq : u' = u :=
          ReferencePostReplacementCollectionReleaseSupport.postRawKOccurrence_unique
            rate rewards C_star C_h u' u z hu' hu
        have hsK : s ≤ k :=
          stoppedDate_source_start_le rate rewards C_star C_h control0 tk z hkeepK
        have hsupportK : k + 1 ∈ postRawKStoppedSupport rate rewards C_star C_h z :=
          (postRawKStoppedSupport_mem_iff rate rewards C_star C_h z (k + 1)).mpr
            ⟨tk, hkeepK, rfl⟩
        have hcutK : k + 1 < thetaLocal source := by
          have hI := (postRawKRelease_interval rate rewards C_star C_h control0 z).1
          rw [hI, Finset.mem_Ico] at hsupportK
          exact hsupportK.2
        have hlocalPendingK : i ∈ pendingTheta rate rewards C_star C_h s hstartHorizon
            u.val thetaLocal k source := by
          subst u'
          apply stoppedPending_localTask_mem rate rewards C_star C_h s u.val source
            thetaLocal hstartHorizon hthetaLocal i tk hsK hcutK
          exact hu'Pending.2
        have hdataEq := stoppedPending_localDataObservation_eq rate rewards C_star C_h
          s u.val source hstartHorizon i tk hsK
        have hflag : X i₀ k z =
            ReferenceLocalReleaseWaitingPaths.dataObservation rate rewards C_star C_h
              s hstartHorizon u.val i k source := by
          simpa [X, dataTaskObservation, hkT, tk, i₀] using hdataEq
        simp [htask, hlocalPendingK, hflag]
      · simp [htask]
    rw [hstrict.2.2.1] at hNle
    omega
  have hservice : ∀ j n, n < p.T →
      ∀ᵐ z ∂μ, j ∈ P n z →
        a * w n z ≤ μ[PhaseServiceWaiting.observation X j n | F (n + 1)] z := by
    intro j n hn
    have hj : j = i₀ := Fin.ext (by have := j.isLt; omega)
    subst j
    let t : Fin p.T := ⟨n, hn⟩
    have hmask := postRawKStoppedPendingSet_mem_measurable_preRound
      rate rewards C_star C_h control0 t i
    have hobsEq : PhaseServiceWaiting.observation X i₀ n =
        (fun source => if actualData rate rewards C_star C_h i t source then (1 : ℝ) else 0) := by
      funext source
      simp [PhaseServiceWaiting.observation, X, dataTaskObservation, dif_pos hn, t, i₀]
    have hobsInt : Integrable (PhaseServiceWaiting.observation X i₀ n) μ := by
      rw [hobsEq]
      exact ReferenceSourcePhysicalFlagConditionalLaw.actualData_observation_integrable
        rate rewards C_star C_h control0 i t
    have hfactor := condExp_indicator hobsInt hmask
    have hmasked := stoppedPending_actualData_condExp rate rewards C_star C_h control0
    filter_upwards [hfactor, hmasked] with z hf hm
    intro hjpending
    have hmem' : i₀ ∈ dataTaskSet rate rewards C_star C_h i n z := by
      simpa [P] using hjpending
    have hpending :=
      ((dataTaskSet_mem_iff rate rewards C_star C_h i n hn z i₀).mp hmem').2
    have hpendingT : i ∈ postRawKStoppedPendingSet rate rewards C_star C_h t z := by
      simpa [t] using hpending
    have hzmem : z ∈ {x | i ∈ postRawKStoppedPendingSet rate rewards C_star C_h t x} := hpendingT
    have hf' := hf
    rw [Set.indicator_of_mem hzmem] at hf'
    have hcond := hm i t
    have hmaskedObs :
        ({x | i ∈ postRawKStoppedPendingSet rate rewards C_star C_h t x}.indicator
          (PhaseServiceWaiting.observation X i₀ n)) =
        ({x | i ∈ postRawKStoppedPendingSet rate rewards C_star C_h t x}.indicator
          (fun x => if actualData rate rewards C_star C_h i t x then (1 : ℝ) else 0)) := by
      funext x
      simp [hobsEq]
    have hmaskedCE :
        μ[({x | i ∈ postRawKStoppedPendingSet rate rewards C_star C_h t x}.indicator
          (PhaseServiceWaiting.observation X i₀ n)) | F (n + 1)] z =
        μ[({x | i ∈ postRawKStoppedPendingSet rate rewards C_star C_h t x}.indicator
          (fun x => if actualData rate rewards C_star C_h i t x then (1 : ℝ) else 0)) |
          F (n + 1)] z := by
      exact congrArg (fun f => μ[f | F (n + 1)] z) hmaskedObs
    have hmean' : μ[PhaseServiceWaiting.observation X i₀ n | F (n + 1)] z =
        stoppedAssignedChi rate rewards C_star C_h t i z / (2 * (p.K : ℝ)) := by
      calc
        _ = μ[({x | i ∈ postRawKStoppedPendingSet rate rewards C_star C_h t x}.indicator
            (PhaseServiceWaiting.observation X i₀ n)) | F (n + 1)] z :=
          hf'.symm
        _ = μ[({x | i ∈ postRawKStoppedPendingSet rate rewards C_star C_h t x}.indicator
            (fun x => if actualData rate rewards C_star C_h i t x then (1 : ℝ) else 0)) |
              F (n + 1)] z := hmaskedCE
        _ = stoppedAssignedChi rate rewards C_star C_h t i z / (2 * (p.K : ℝ)) := by
          simpa [μ, F, t] using hcond
    rw [hmean']
    have hweight : w n z = stoppedAssignedChi rate rewards C_star C_h t i z := by
      simp [w, dataTaskWeight, hn, t]
    rw [hweight]
    change (1 / (2 * (p.K : ℝ))) *
        stoppedAssignedChi rate rewards C_star C_h t i z ≤ _
    have hKpos : (2 * (p.K : ℝ)) ≠ 0 := by positivity
    apply le_of_eq
    field_simp [hKpos]
  have hTaskBound :=
    PhaseStartConditionalWaiting.phase_start_task_charge_condExp_bound
      μ (by omega) hT hK hq F P X w sigma theta a ha hsigma htheta hstart
      hordered hthetaBound hP hphase
      (by
        intro s t hst ht z hσ hθ j hj
        by_cases hst' : s = t
        · subst t
          exact Finset.Subset.rfl hj
        · have hstlt : s < t := by omega
          let ts : Fin p.T := ⟨s, by omega⟩
          let tt : Fin p.T := ⟨t, ht⟩
          have hj0 : j = i₀ := Fin.ext (by have := j.isLt; omega)
          subst j
          have hLater : i ∈ postRawKStoppedPendingSet rate rewards C_star C_h tt z := by
            have hmem' : i₀ ∈ dataTaskSet rate rewards C_star C_h i t z := by
              simpa [P] using hj
            exact ((dataTaskSet_mem_iff rate rewards C_star C_h i t ht z i₀).mp hmem').2
          have hkeepLater := (postRawKStoppedPendingSet_mem_iff
            rate rewards C_star C_h tt z i).mp hLater |>.1
          have hdateLater := (postRawKStoppedPendingSet_mem_iff
            rate rewards C_star C_h tt z i).mp hLater |>.2
          have hrel : ReferencePostReplacementCollectionReleaseSupport.rawReleaseRecords
              rate rewards C_star C_h z ≠ [] := by
            intro hnil
            have hsupport : t + 1 ∈ postRawKStoppedSupport rate rewards C_star C_h z :=
              (postRawKStoppedSupport_mem_iff rate rewards C_star C_h z (t + 1)).mpr
                ⟨tt, hkeepLater, rfl⟩
            rw [postRawKStoppedSupport_empty_of_rawReleaseRecords_empty
              rate rewards C_star C_h z hnil] at hsupport
            simp at hsupport
          obtain ⟨hc, _a, _cutoff, _M, _hcutLow, _hcutHigh, _hstamp,
            _hrecords, _hread⟩ :=
            postRawKStoppedRecords_source rate rewards C_star C_h control0 z hrel
          let start := ReferenceCompletePhysicalHistory.physicalStart
            rate z rewards C_star C_h
          let source : ReferenceLocalReleaseWaitingPaths.SourceEvent
              rate rewards C_star C_h start := ⟨z, hc, rfl⟩
          let thetaLocal : ReferenceLocalReleaseWaitingPaths.SourceEvent
              rate rewards C_star C_h start → ℕ :=
            fun x => postRawKReleaseTheta rate rewards C_star C_h x.val
          have hthetaLocal : ∀ x, 1 ≤ thetaLocal x ∧ thetaLocal x ≤ p.T + 1 := by
            intro x
            have hi := postRawKRelease_interval rate rewards C_star C_h control0 x.val
            constructor
            · dsimp [thetaLocal]
              exact le_trans hi.2.1 hi.2.2.1
            · dsimp [thetaLocal]
              exact hi.2.2.2
          obtain ⟨u, hult, hu, huPending⟩ :=
            postRawKStoppedPendingDate_same_occurrence rate rewards C_star C_h tt i z
              hkeepLater hdateLater
          have hI := (postRawKRelease_interval rate rewards C_star C_h control0 z).1
          have hsuppS : s + 1 ∈ postRawKStoppedSupport rate rewards C_star C_h z := by
            rw [hI, Finset.mem_Ico]
            have hσ' : postRawKReleaseSigma rate rewards C_star C_h z ≤ s + 1 := by
              simpa [sigma, dataTaskStart] using hσ
            have hθ' : t + 1 < postRawKReleaseTheta rate rewards C_star C_h z := by
              simpa [theta, dataTaskEnd] using hθ
            exact ⟨hσ', by omega⟩
          obtain ⟨tS, hkeepS, htSEq⟩ :=
            (postRawKStoppedSupport_mem_iff rate rewards C_star C_h z (s + 1)).mp hsuppS
          have htSEq' : tS = ts := by
            apply Fin.ext
            have hval : tS.val = s := Nat.add_right_cancel htSEq
            simpa [ts] using hval
          subst tS
          obtain ⟨v, hvs, hvS, hentryS⟩ := hkeepS.1
          have hvEq : v = u :=
            ReferencePostReplacementCollectionReleaseSupport.postRawKOccurrence_unique
              rate rewards C_star C_h v u z hvS hu
          subst v
          have hentryT₀ := hkeepLater.1
          obtain ⟨v, hvt, hvT, hentryT⟩ := hentryT₀
          have hvEqT : v = u :=
            ReferencePostReplacementCollectionReleaseSupport.postRawKOccurrence_unique
              rate rewards C_star C_h v u z hvT hu
          subst v
          let startSource := ReferenceCompletePhysicalHistory.physicalStart
            rate z rewards C_star C_h
          have hsSource : startSource ≤ s :=
            stoppedDate_source_start_le rate rewards C_star C_h control0 ts z hkeepS
          have htSource : startSource ≤ t :=
            stoppedDate_source_start_le rate rewards C_star C_h control0 tt z hkeepLater
          have hstartHorizon : startSource ≤ p.T := le_trans hsSource (by omega)
          have hentryCalS := ReferenceSourcePrefixHistoryFiltration.entry_source_calendar
            rate rewards C_star C_h u.val ts startSource hsSource source
          have hentryCalT := ReferenceSourcePrefixHistoryFiltration.entry_source_calendar
            rate rewards C_star C_h u.val tt startSource htSource source
          have hgateS : ReferenceLocalReleaseCalendarCounts.calendarGate rate z rewards C_star C_h
              hc startSource (p.T - startSource) rfl (by omega) u.val s = some true := by
            have hmap := congrArg (Option.map Prod.fst) hentryCalS
            rw [hmap] at hentryS
            simpa [ReferenceLocalReleaseCalendarCounts.calendarGate,
              ReferenceLocalReleaseCalendarCounts.calendarEntry,
              ReferenceRetainedReleasePhaseObservation.localReleaseEntry,
              ReferenceRetainedReleasePhaseObservation.localReleaseGate, ts] using hentryS
          have hgateT : ReferenceLocalReleaseCalendarCounts.calendarGate rate z rewards C_star C_h
              hc startSource (p.T - startSource) rfl (by omega) u.val t = some true := by
            have hmap := congrArg (Option.map Prod.fst) hentryCalT
            rw [hmap] at hentryT
            simpa [ReferenceLocalReleaseCalendarCounts.calendarGate,
              ReferenceLocalReleaseCalendarCounts.calendarEntry,
              ReferenceRetainedReleasePhaseObservation.localReleaseEntry,
              ReferenceRetainedReleasePhaseObservation.localReleaseGate, tt] using hentryT
          let alpha := ReferenceLocalReleaseGateChronology.gateAlpha u.val
            (ReferenceLocalReleaseWaitingPaths.sourceRunAtLaunch rate rewards C_star C_h
              startSource hstartHorizon source).records
          let beta := ReferenceLocalReleaseGateChronology.gateBeta u.val
            (ReferenceLocalReleaseWaitingPaths.sourceRunAtLaunch rate rewards C_star C_h
              startSource hstartHorizon source).records
          have hintervalS := ReferenceLocalReleaseCalendarCounts.calendarGate_inside_interval
            rate z rewards C_star C_h hc startSource (p.T - startSource) rfl (by omega)
            u.val s hgateS
          have hintervalT := ReferenceLocalReleaseCalendarCounts.calendarGate_inside_interval
            rate z rewards C_star C_h hc startSource (p.T - startSource) rfl (by omega)
            u.val t hgateT
          have hcutS : s + 1 < thetaLocal source := by
            have hsupp := hsuppS
            rw [hI, Finset.mem_Ico] at hsupp
            simpa [thetaLocal] using hsupp.2
          have hcutT : t + 1 < thetaLocal source := by
            have hsupp : t + 1 ∈ postRawKStoppedSupport rate rewards C_star C_h z :=
              (postRawKStoppedSupport_mem_iff rate rewards C_star C_h z (t + 1)).mpr
                ⟨tt, hkeepLater, rfl⟩
            rw [hI, Finset.mem_Ico] at hsupp
            simpa [thetaLocal] using hsupp.2
          have halphaBeta : alpha < min beta (thetaLocal source) := by
            have hAlphaBeta : alpha < beta := by
              dsimp [alpha, beta,
                ReferenceLocalReleaseWaitingPaths.sourceRunAtLaunch]
              exact Nat.lt_of_le_of_lt hintervalS.1 hintervalS.2
            have hAlphaTheta : alpha < thetaLocal source :=
              lt_of_le_of_lt (by
                dsimp [alpha, ReferenceLocalReleaseWaitingPaths.sourceRunAtLaunch]
                exact hintervalS.1) hcutS
            exact Nat.lt_min.mpr ⟨hAlphaBeta, hAlphaTheta⟩
          have hAlphaLocal : ReferenceLocalReleaseWaitingPaths.localGateAlpha
              rate rewards C_star C_h startSource hstartHorizon u.val source = alpha := by
            rfl
          have hBetaLocal : ReferenceLocalReleaseWaitingPaths.localGateBeta
              rate rewards C_star C_h startSource hstartHorizon u.val source = beta := by
            rfl
          have hAlphaAtS : alpha ≤ s + 1 := by
            simpa [alpha, ReferenceLocalReleaseWaitingPaths.sourceRunAtLaunch] using hintervalS.1
          have hlocalStart : ReferenceLocalReleaseWaitingPaths.localPhaseSigma
              rate rewards C_star C_h startSource hstartHorizon u.val thetaLocal source ≤ s + 1 := by
            unfold ReferenceLocalReleaseWaitingPaths.localPhaseSigma
            simp only [hAlphaLocal, hBetaLocal, if_pos halphaBeta]
            exact hAlphaAtS
          have hlocalEnd : t + 1 < ReferenceLocalReleaseWaitingPaths.localPhaseEndpoint
              rate rewards C_star C_h startSource hstartHorizon u.val thetaLocal source := by
            have hmin : t + 1 < min beta (thetaLocal source) :=
              Nat.lt_min.mpr ⟨hintervalT.2, hcutT⟩
            unfold ReferenceLocalReleaseWaitingPaths.localPhaseEndpoint
            simp only [hAlphaLocal, hBetaLocal, if_pos halphaBeta]
            exact hmin
          have hlocalLater : i ∈ ReferenceLocalReleaseWaitingPaths.pendingTheta
              rate rewards C_star C_h startSource hstartHorizon u.val thetaLocal t source := by
            apply stoppedPending_localTask_mem rate rewards C_star C_h startSource u.val source
              thetaLocal hstartHorizon hthetaLocal i tt htSource hcutT
            exact huPending.2
          have hlocalEarlier :=
            ReferenceLocalReleaseWaitingPaths.pendingTheta_nested_inside_interval
              rate rewards C_star C_h startSource hstartHorizon u.val thetaLocal hthetaLocal
              source s t (Nat.le_of_lt hstlt) ht hlocalStart hlocalEnd hlocalLater
          have hPendingAtS : i ∈ pending rate rewards C_star C_h u.val ts z := by
            apply localTask_pending_actual_mem rate rewards C_star C_h startSource u.val
              source hstartHorizon ts hsSource hcutS i
            exact hlocalEarlier
          have hpendingSupportS : ReferencePostReplacementCollectionReleaseSupport.postRawKPendingSupport
              rate rewards C_star C_h ts i z :=
            ⟨u, hvs, hu, hPendingAtS⟩
          have hdateS : postRawKStoppedPendingDate rate rewards C_star C_h ts i z :=
            ⟨hpendingSupportS, hkeepS.2.1, hkeepS.2.2⟩
          have hmemS : i ∈ postRawKStoppedPendingSet rate rewards C_star C_h ts z :=
            (postRawKStoppedPendingSet_mem_iff rate rewards C_star C_h ts z i).mpr
              ⟨hkeepS, hdateS⟩
          have hmem' : i₀ ∈ dataTaskSet rate rewards C_star C_h i s z :=
            (dataTaskSet_mem_iff rate rewards C_star C_h i s ts.isLt z i₀).mpr
              ⟨rfl, hmemS⟩
          simpa [P, ts] using hmem'
      )
      hwMeas hwBound hXMeas hQuota hservice i₀
  have hChargeEq (z : BootstrapPrivateRoundStreams.SourceInput p) :
      dataTaskFollowerCharge rate rewards C_star C_h i z =
        PhaseServiceWaiting.G P w i₀ p.T z := by
    classical
    unfold dataTaskFollowerCharge
    rw [Finset.sum_fin_eq_sum_range]
    unfold PhaseServiceWaiting.G
    apply Finset.sum_congr rfl
    intro n hn
    have hnT : n < p.T := Finset.mem_range.mp hn
    let t : Fin p.T := ⟨n, hnT⟩
    by_cases hp : i ∈ postRawKStoppedPendingSet rate rewards C_star C_h t z
    · simp [P, dataTaskSet, w, dataTaskWeight, PhaseServiceWaiting.J, hnT, t, hp, i₀]
    · have hzero : stoppedAssignedChi rate rewards C_star C_h t i z = 0 := by
        unfold stoppedAssignedChi
        simp [hp]
      simp [P, dataTaskSet, w, dataTaskWeight, PhaseServiceWaiting.J, hnT, t, hp, hzero, i₀]
  have hcoef : (1 : ℝ) / a = 2 * (p.K : ℝ) := by
    dsimp [a]
    field_simp
  change μ[(fun z => dataTaskFollowerCharge rate rewards C_star C_h i z) |
      PhaseStartConditionalWaiting.phaseStartSigmaAlgebra F sigma hsigma] ≤ᵐ[μ]
    fun _ => 2 * (p.K : ℝ)
  rw [show (fun z => dataTaskFollowerCharge rate rewards C_star C_h i z) =
      (fun z => PhaseServiceWaiting.G P w i₀ p.T z) from funext hChargeEq]
  simpa [hcoef] using hTaskBound

/-- Each actual follower's finite stopped DATA charge is integrable under the
original source-input law. -/
theorem actualPostRawKDataFollower_integrable
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1)) :
    Integrable (dataTaskFollowerCharge rate rewards C_star C_h i)
      (BootstrapPrivateRoundStreams.sourceInputLaw p) := by
  unfold dataTaskFollowerCharge
  apply integrable_finsetSum Finset.univ
  intro t ht
  exact stoppedAssignedChi_integrable rate rewards C_star C_h control0 t i

/-- The literal total post-rawK DATA waiting charge is integrable on the
original source law. -/
theorem actualPostRawKDataWaitingCharge_integrable
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p) :
    Integrable (actualPostRawKDataWaitingCharge rate rewards C_star C_h)
      (BootstrapPrivateRoundStreams.sourceInputLaw p) := by
  unfold actualPostRawKDataWaitingCharge
  apply integrable_finsetSum Finset.univ
  intro i hi
  apply integrable_finsetSum Finset.univ
  intro t ht
  exact stoppedAssignedChi_integrable rate rewards C_star C_h control0 t i

/-- Summing the fixed-follower phase-start DATA bounds gives the exact total
post-rawK stopped waiting charge bound under the same original source law. -/
theorem actualPostRawKDataWaitingCharge_condExp_bound
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p) :
    (BootstrapPrivateRoundStreams.sourceInputLaw p)[
      actualPostRawKDataWaitingCharge rate rewards C_star C_h |
        PhaseStartConditionalWaiting.phaseStartSigmaAlgebra
          (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0)
          (dataTaskStart rate rewards C_star C_h)
          (ReferencePostReplacementCollectionStoppedReleaseAdaptation.postRawKRelease_sigma_stopping
            rate rewards C_star C_h control0)] ≤ᵐ[BootstrapPrivateRoundStreams.sourceInputLaw p]
      fun _ => 2 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) := by
  let μ := BootstrapPrivateRoundStreams.sourceInputLaw p
  let F := ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0
  let sigma := dataTaskStart rate rewards C_star C_h
  let hsigma := ReferencePostReplacementCollectionStoppedReleaseAdaptation.postRawKRelease_sigma_stopping
    rate rewards C_star C_h control0
  let mσ := PhaseStartConditionalWaiting.phaseStartSigmaAlgebra F sigma hsigma
  have hsum := condExp_finsetSum (μ := μ) (s := Finset.univ)
    (f := fun i z => dataTaskFollowerCharge rate rewards C_star C_h i z)
    (fun i _ => actualPostRawKDataFollower_integrable rate rewards C_star C_h control0 i)
    mσ
  have harg : actualPostRawKDataWaitingCharge rate rewards C_star C_h =
      ∑ i : Fin (p.m - 1),
        (fun z => dataTaskFollowerCharge rate rewards C_star C_h i z) := by
    funext z
    simp [actualPostRawKDataWaitingCharge, dataTaskFollowerCharge, Finset.sum_apply]
  have hsumArg : μ[actualPostRawKDataWaitingCharge rate rewards C_star C_h | mσ] =ᵐ[μ]
      μ[∑ i : Fin (p.m - 1),
        (fun z => dataTaskFollowerCharge rate rewards C_star C_h i z) | mσ] :=
    condExp_congr_ae (Filter.Eventually.of_forall fun z => congrFun harg z)
  have hsum' := hsumArg.trans hsum
  have hfollowers : ∀ᵐ z ∂μ, ∀ i : Fin (p.m - 1),
      μ[dataTaskFollowerCharge rate rewards C_star C_h i | mσ] z ≤ 2 * (p.K : ℝ) := by
    apply ae_all_iff.mpr
    intro i
    exact actualPostRawKDataFollower_condExp_bound rate rewards C_star C_h control0 i
  change μ[actualPostRawKDataWaitingCharge rate rewards C_star C_h | mσ] ≤ᵐ[μ]
    fun _ => 2 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ)
  filter_upwards [hsum', hfollowers] with z hsumz hfollowersz
  simp only [Finset.sum_apply] at hsumz
  rw [hsumz]
  calc
    (∑ i : Fin (p.m - 1), μ[dataTaskFollowerCharge rate rewards C_star C_h i | mσ] z) ≤
        ∑ _i : Fin (p.m - 1), 2 * (p.K : ℝ) :=
      Finset.sum_le_sum fun i _ => hfollowersz i
    _ = 2 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) := by
      simp
      ring

end Bandits.Support.ReferencePostReplacementCollectionDataWaitingCost

end noncomputable section
