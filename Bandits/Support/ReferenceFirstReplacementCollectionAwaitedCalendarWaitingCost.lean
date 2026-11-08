/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstReplacementCollectionAwaitedCalendarPhaseSupport
public import Bandits.Support.ReferenceFirstReplacementCollectionAwaitedCalendarServiceLaw

/-!
# Waiting charge on the new awaited replacement calendar

This module assembles the supported-date charge and its phase-start waiting
bound under the original source-input law. Its analytical support endpoints
are not identified with the physical cutoff.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support
open ConstructorDimensions
open BootstrapPrivateRoundStreams
open PhaseServiceWaiting
open PhaseStartConditionalWaiting
open PhaseStartInclusiveCountWaiting
open ReferenceSourcePrefixHistoryFiltration
open scoped Classical

namespace Bandits.Support.ReferenceFirstReplacementCollectionAwaitedCalendarWaitingCost

variable {p : ConstructorDimensions.Parameters}

/-- Literal whole-row waiting charge over the nonempty dates of the accepted
new awaited support. The supported detecting date is included. -/
def W
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (control0 : ContinuousLearningRows.TimeControl p)
    (z : BootstrapPrivateRoundStreams.SourceInput p) : ℝ :=
  ∑ n ∈ Finset.range p.T,
    if (ReferenceFirstReplacementCollectionAwaitedTaskSupport.Pnew
        rate rewards C_star C_h control0 n z).Nonempty then
      ReferenceFirstCollectionRoundEndObservation.g rewards n z
    else 0

/-- The literal supported-date sum is exactly the accepted phase service
totalCharge with its empty-calendar sentinel endpoints. -/
theorem W_eq_totalCharge
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (control0 : ContinuousLearningRows.TimeControl p)
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    W rate rewards C_star C_h control0 z =
      PhaseServiceWaiting.totalCharge
        (ReferenceFirstReplacementCollectionAwaitedCalendarPhaseSupport.Awaited
          rate rewards C_star C_h control0)
        (ReferenceFirstReplacementCollectionAwaitedCalendarPhaseSupport.sigma
          rate rewards C_star C_h control0)
        (ReferenceFirstReplacementCollectionAwaitedCalendarPhaseSupport.theta
          rate rewards C_star C_h control0)
        (fun n source => ReferenceFirstCollectionRoundEndObservation.g rewards n source)
        p.T z := by
  simpa [W, ReferenceFirstReplacementCollectionAwaitedCalendarPhaseSupport.Awaited] using
    (ReferenceFirstReplacementCollectionAwaitedCalendarPhaseSupport.supported_charge_eq_totalCharge
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
      (control0 := control0)
      (fun n source => ReferenceFirstCollectionRoundEndObservation.g rewards n source) z)

private theorem W_waiting_bounds
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (control0 : ContinuousLearningRows.TimeControl p)
    (B : Set (BootstrapPrivateRoundStreams.SourceInput p))
    (hB : MeasurableSet[
      PhaseStartConditionalWaiting.phaseStartSigmaAlgebra
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0)
        (ReferenceFirstReplacementCollectionAwaitedCalendarPhaseSupport.sigma
          (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
          (control0 := control0))
        (ReferenceFirstReplacementCollectionAwaitedCalendarPhaseSupport.sigma_is_pre_round_stopping_time
          (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
          (control0 := control0))] B) :
    Integrable (W rate rewards C_star C_h control0)
        (BootstrapPrivateRoundStreams.sourceInputLaw p) ∧
      (∫ z in B, W rate rewards C_star C_h control0 z
        ∂BootstrapPrivateRoundStreams.sourceInputLaw p) ≤
        ReferenceFirstCollectionAwaitedWaitingCost.Bcol (p := p) *
          (BootstrapPrivateRoundStreams.sourceInputLaw p).real B ∧
      (BootstrapPrivateRoundStreams.sourceInputLaw p)[
        W rate rewards C_star C_h control0 |
          PhaseStartConditionalWaiting.phaseStartSigmaAlgebra
            (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0)
            (ReferenceFirstReplacementCollectionAwaitedCalendarPhaseSupport.sigma
              (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
              (control0 := control0))
            (ReferenceFirstReplacementCollectionAwaitedCalendarPhaseSupport.sigma_is_pre_round_stopping_time
              (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
              (control0 := control0))] ≤ᵐ[BootstrapPrivateRoundStreams.sourceInputLaw p]
        fun _ => ReferenceFirstCollectionAwaitedWaitingCost.Bcol (p := p) := by
  let d : ℕ := p.m - 1
  let q : ℕ := 4 * AffineBatchDecoder.quota p
  let a : ℝ := 1 / ((8 : ℝ) * (d : ℝ) * (p.K : ℝ))
  let F := ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0
  let P : ℕ → BootstrapPrivateRoundStreams.SourceInput p → Finset (Fin d) :=
    fun n z => ReferenceFirstReplacementCollectionAwaitedTaskSupport.Pnew
      rate rewards C_star C_h control0 n z
  let X : Fin d → ℕ → BootstrapPrivateRoundStreams.SourceInput p → Bool :=
    fun i n z => ReferenceFirstReplacementCollectionAwaitedTaskSupport.x
      rate rewards C_star C_h control0 i n z
  let w : ℕ → BootstrapPrivateRoundStreams.SourceInput p → ℝ :=
    fun n z => ReferenceFirstCollectionRoundEndObservation.g rewards n z
  let sigma : BootstrapPrivateRoundStreams.SourceInput p → ℕ :=
    ReferenceFirstReplacementCollectionAwaitedCalendarPhaseSupport.sigma
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
      (control0 := control0)
  let theta : BootstrapPrivateRoundStreams.SourceInput p → ℕ :=
    ReferenceFirstReplacementCollectionAwaitedCalendarPhaseSupport.theta
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
      (control0 := control0)
  let hsigma :=
    ReferenceFirstReplacementCollectionAwaitedCalendarPhaseSupport.sigma_is_pre_round_stopping_time
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
      (control0 := control0)
  let htheta :=
    ReferenceFirstReplacementCollectionAwaitedCalendarPhaseSupport.theta_is_pre_round_stopping_time
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
      (control0 := control0)
  have hm2 : 2 ≤ p.m := p.two_le_m
  have hm1 : 1 ≤ p.m := by omega
  have hdNat : 0 < d := by
    dsimp [d]
    exact Nat.sub_pos_of_lt (by omega)
  have hd : 0 < (d : ℝ) := Nat.cast_pos.mpr hdNat
  have hT : 0 < p.T := ConstructorDimensions.T_pos p
  have hK : 0 < p.K := ConstructorDimensions.K_pos p
  have hq : 0 < q := by
    dsimp [q]
    exact Nat.mul_pos (by decide) (AffineBatchDecoder.quota_pos p)
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hstart : ∀ z, 1 ≤ sigma z := by
    intro z
    exact (ReferenceFirstReplacementCollectionAwaitedCalendarPhaseSupport.endpoint_bounds
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
      (control0 := control0) z).1
  have hordered : ∀ z, sigma z ≤ theta z := by
    intro z
    exact (ReferenceFirstReplacementCollectionAwaitedCalendarPhaseSupport.endpoint_bounds
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
      (control0 := control0) z).2.1
  have hthetaBound : ∀ z, theta z ≤ p.T + 1 := by
    intro z
    exact (ReferenceFirstReplacementCollectionAwaitedCalendarPhaseSupport.endpoint_bounds
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
      (control0 := control0) z).2.2
  have hP : ∀ i n, n < p.T →
      MeasurableSet[F (n + 1)] {z | i ∈ P n z} := by
    intro i n hn
    simpa [F, P] using
      (ReferenceFirstReplacementCollectionAwaitedTaskSupport.Pnew_mem_measurable
        (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
        (control0 := control0) n i)
  have hphase : ∀ n, n < p.T → ∀ z, (P n z).Nonempty →
      sigma z ≤ n + 1 ∧ n + 1 < theta z := by
    intro n hn z hne
    simpa [P, sigma, theta] using
      (ReferenceFirstReplacementCollectionAwaitedCalendarPhaseSupport.support_nonempty_iff_phase
        (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
        (control0 := control0) z n).mp hne
  have hnested : ∀ s t, s ≤ t → t < p.T → ∀ z,
      sigma z ≤ s + 1 → t + 1 < theta z → P t z ⊆ P s z := by
    intro s t hst ht z hs hend
    simpa [P, sigma, theta] using
      (ReferenceFirstReplacementCollectionAwaitedCalendarPhaseSupport.Pnew_nested_within_phase
        (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
        (control0 := control0) z hst ht hs hend)
  have hwMeas : ∀ n, n < p.T → StronglyMeasurable[F (n + 1)] (w n) := by
    intro n hn
    simpa [F, w] using
      (ReferenceFirstCollectionRoundEndObservation.g_stronglyMeasurable
        rewards control0 n)
  have hwBound : ∀ n, n < p.T → ∀ z, w n z ∈ Set.Icc (0 : ℝ) (p.K : ℝ) := by
    intro n hn z
    exact ReferenceFirstCollectionRoundEndObservation.g_mem_Icc rewards n z
  have hXMeas : ∀ i n, n < p.T →
      StronglyMeasurable[F (n + 2)]
        (PhaseServiceWaiting.observation X i n) := by
    intro i n hn
    simpa [F, X] using
      (ReferenceFirstReplacementCollectionAwaitedCalendarServiceLaw.observation_stronglyMeasurable
        (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
        (control0 := control0) i n)
  have hterminalCount : ∀ (i : Fin d) z,
      PhaseServiceWaiting.N P X i p.T z ≤ q := by
    intro i z
    simpa [P, X, q] using
      (ReferenceFirstReplacementCollectionAwaitedTaskSupport.N_le_quota
        (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
        (control0 := control0) i p.T z)
  have hservice : ∀ i n, n < p.T →
      ∀ᵐ z ∂BootstrapPrivateRoundStreams.sourceInputLaw p,
        i ∈ P n z →
          a * w n z ≤
            (BootstrapPrivateRoundStreams.sourceInputLaw p)[
              PhaseServiceWaiting.observation X i n | F (n + 1)] z := by
    intro i n hn
    filter_upwards
      [ReferenceFirstReplacementCollectionAwaitedCalendarServiceLaw.observation_service_lower_bound
        (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
        (control0 := control0) n hn i] with z hz
    intro hi
    simpa [a, w, d, F, X, Nat.cast_sub hm1] using hz hi
  have hchargeInt := PhaseServiceWaiting.totalCharge_exp_integrable
    (BootstrapPrivateRoundStreams.sourceInputLaw p) F P sigma theta w a ha
    hsigma htheta hP hwMeas hphase hwBound
  have hcoefficient :
      (((q : ℝ) + Real.log (d : ℝ)) /
          (PhaseServiceWaiting.kappa * a)) =
        ReferenceFirstCollectionAwaitedWaitingCost.Bcol (p := p) := by
    have hdReal : (d : ℝ) ≠ 0 := ne_of_gt hd
    have hKReal : (p.K : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hK)
    have hkappa : PhaseServiceWaiting.kappa ≠ 0 :=
      ne_of_gt PhaseServiceWaiting.kappa_pos
    have hdenom : (8 : ℝ) * (d : ℝ) * (p.K : ℝ) ≠ 0 := by
      positivity
    have hkappa' : 1 - Real.exp (-1) ≠ 0 := by
      simpa [PhaseServiceWaiting.kappa] using hkappa
    dsimp [a, q, d, ReferenceFirstCollectionAwaitedWaitingCost.Bcol]
    rw [PhaseServiceWaiting.kappa]
    norm_cast
    field_simp [hdenom, hkappa']
  have hsetGeneric :=
    PhaseStartInclusiveCountWaiting.phase_start_totalCharge_setIntegral_bound_of_terminalCount
      (BootstrapPrivateRoundStreams.sourceInputLaw p) hdNat hT hK hq F P X w sigma theta a ha
      hsigma htheta hstart hordered hthetaBound hP hphase hnested hwMeas hwBound
      hXMeas hterminalCount hservice B hB
  have hcondGeneric :=
    PhaseStartInclusiveCountWaiting.phase_start_totalCharge_condExp_bound_of_terminalCount
      (BootstrapPrivateRoundStreams.sourceInputLaw p) hdNat hT hK hq F P X w sigma theta a ha
      hsigma htheta hstart hordered hthetaBound hP hphase hnested hwMeas hwBound
      hXMeas hterminalCount hservice
  have hW : W rate rewards C_star C_h control0 =
      PhaseServiceWaiting.totalCharge P sigma theta w p.T := by
    funext z
    simpa [P, w, sigma, theta,
      ReferenceFirstReplacementCollectionAwaitedCalendarPhaseSupport.Awaited] using
      W_eq_totalCharge rate rewards C_star C_h control0 z
  refine ⟨?_, ?_, ?_⟩
  · simpa only [hW] using hchargeInt.1
  · calc
      (∫ z in B, W rate rewards C_star C_h control0 z
        ∂BootstrapPrivateRoundStreams.sourceInputLaw p) ≤
          (((q : ℝ) + Real.log (d : ℝ)) /
            (PhaseServiceWaiting.kappa * a)) *
              (BootstrapPrivateRoundStreams.sourceInputLaw p).real B := by
        simpa only [hW] using hsetGeneric
      _ = ReferenceFirstCollectionAwaitedWaitingCost.Bcol (p := p) *
            (BootstrapPrivateRoundStreams.sourceInputLaw p).real B := by
        rw [hcoefficient]
  · simpa only [hW, hcoefficient] using hcondGeneric

/-- The supported new awaited-calendar charge is integrable under the original
source-input law. -/
theorem W_integrable
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (control0 : ContinuousLearningRows.TimeControl p) :
    Integrable (W rate rewards C_star C_h control0)
      (BootstrapPrivateRoundStreams.sourceInputLaw p) := by
  exact (W_waiting_bounds rate rewards C_star C_h control0 Set.univ
    MeasurableSet.univ).1

/-- Every event in the exact supported phase-start sigma-algebra localizes
the new waiting charge with its unnormalized original-law mass. -/
theorem W_setIntegral_bound
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (control0 : ContinuousLearningRows.TimeControl p)
    (B : Set (BootstrapPrivateRoundStreams.SourceInput p))
    (hB : MeasurableSet[
      PhaseStartConditionalWaiting.phaseStartSigmaAlgebra
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0)
        (ReferenceFirstReplacementCollectionAwaitedCalendarPhaseSupport.sigma
          (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
          (control0 := control0))
        (ReferenceFirstReplacementCollectionAwaitedCalendarPhaseSupport.sigma_is_pre_round_stopping_time
          (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
          (control0 := control0))] B) :
    (∫ z in B, W rate rewards C_star C_h control0 z
      ∂BootstrapPrivateRoundStreams.sourceInputLaw p) ≤
      ReferenceFirstCollectionAwaitedWaitingCost.Bcol (p := p) *
        (BootstrapPrivateRoundStreams.sourceInputLaw p).real B := by
  exact (W_waiting_bounds rate rewards C_star C_h control0 B hB).2.1

/-- The supported new awaited-calendar charge has the `Bcol` conditional
expectation bound at the same analytical phase start. -/
theorem W_condExp_bound
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (control0 : ContinuousLearningRows.TimeControl p) :
    (BootstrapPrivateRoundStreams.sourceInputLaw p)[
      W rate rewards C_star C_h control0 |
        PhaseStartConditionalWaiting.phaseStartSigmaAlgebra
          (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0)
          (ReferenceFirstReplacementCollectionAwaitedCalendarPhaseSupport.sigma
            (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
            (control0 := control0))
          (ReferenceFirstReplacementCollectionAwaitedCalendarPhaseSupport.sigma_is_pre_round_stopping_time
            (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
            (control0 := control0))] ≤ᵐ[BootstrapPrivateRoundStreams.sourceInputLaw p]
      fun _ => ReferenceFirstCollectionAwaitedWaitingCost.Bcol (p := p) := by
  exact (W_waiting_bounds rate rewards C_star C_h control0 Set.univ
    MeasurableSet.univ).2.2

end Bandits.Support.ReferenceFirstReplacementCollectionAwaitedCalendarWaitingCost

end
