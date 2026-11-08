/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionAwaitedPhaseSupport

/-!
# Waiting charge on the original first-collection awaited support

Sources: `sources/zip4/manuscript/05_binary_transport.tex:180-240`,
`sources/zip4/manuscript/06_interruptions.tex:425-431,459-487`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:141-157`.

The phase is the existing strict-past-corrected `Pawait` process, with its
source-prefix endpoints, original round-end observation, whole reward table,
and original source-input law. This gives a phase-start waiting estimate for
its own charge; it does not identify a transfer start or assemble the larger
collection and transfer-cost theorem.
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
open ReferenceFirstCollectionAwaitedPhaseSupport
open ReferenceFirstCollectionAwaitedTaskSupport
open ReferenceFirstCollectionRoundEndObservation
open ReferenceSourcePrefixHistoryFiltration
open scoped Classical

namespace Bandits.Support.ReferenceFirstCollectionAwaitedWaitingCost

variable {p : ConstructorDimensions.Parameters}

/-- Literal total charge on the actual `Pawait` mask and its actual first and
one-past-last supported dates. -/
def actualFirstCollectionAwaitedWaitingCharge
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p) : ℝ :=
  PhaseServiceWaiting.totalCharge
    (fun n source => Pawait rate rewards C_star C_h n source)
    (ReferenceFirstCollectionAwaitedPhaseSupport.sigma
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h))
    (ReferenceFirstCollectionAwaitedPhaseSupport.theta
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h))
    (fun n source => ReferenceFirstCollectionRoundEndObservation.g rewards n source)
    p.T z

/-- The literal `Pawait` charge is the sum of the original deterministic
round weight over exactly its nonempty support dates. -/
theorem actualFirstCollectionAwaitedWaitingCharge_eq_supported_sum
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    actualFirstCollectionAwaitedWaitingCharge rate rewards C_star C_h z =
      ∑ n ∈ ReferenceFirstCollectionAwaitedPhaseSupport.supportIndices
        (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) z,
          ReferenceFirstCollectionRoundEndObservation.g rewards n z := by
  classical
  unfold actualFirstCollectionAwaitedWaitingCharge PhaseServiceWaiting.totalCharge
    PhaseServiceWaiting.A
  simp only [Set.indicator_apply]
  rw [ReferenceFirstCollectionAwaitedPhaseSupport.supportIndices,
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  have hnT : n < p.T := Finset.mem_range.mp hn
  have hphase := ReferenceFirstCollectionAwaitedPhaseSupport.support_nonempty_iff_phase
    (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) z n
  change (Pawait rate rewards C_star C_h n z).Nonempty ↔ _ at hphase
  by_cases hnonempty : (Pawait rate rewards C_star C_h n z).Nonempty
  · have hinterval := hphase.mp hnonempty
    simp [hnonempty, hinterval]
  · simp [hnonempty]

/-- The analytical first-collection waiting constant from the inclusive
`4Q` service count and the actual service probability `1/(8 d K)`. -/
def Bcol : ℝ :=
  (((8 : ℝ) * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ)) /
      (1 - Real.exp (-1))) *
    (4 * (AffineBatchDecoder.quota p : ℝ) +
      Real.log ((p.m - 1 : ℕ) : ℝ))

private theorem actual_first_collection_awaited_waiting_bounds
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (B : Set (BootstrapPrivateRoundStreams.SourceInput p))
    (hB : MeasurableSet[
      PhaseStartConditionalWaiting.phaseStartSigmaAlgebra
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0)
        (ReferenceFirstCollectionAwaitedPhaseSupport.sigma
          (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h))
        (ReferenceFirstCollectionAwaitedPhaseSupport.sigma_is_pre_round_stopping_time
          (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
          control0)] B) :
    Integrable
        (actualFirstCollectionAwaitedWaitingCharge rate rewards C_star C_h)
        (BootstrapPrivateRoundStreams.sourceInputLaw p) ∧
      (∫ z in B,
        actualFirstCollectionAwaitedWaitingCharge rate rewards C_star C_h z
          ∂BootstrapPrivateRoundStreams.sourceInputLaw p) ≤
        Bcol (p := p) * (BootstrapPrivateRoundStreams.sourceInputLaw p).real B ∧
      (BootstrapPrivateRoundStreams.sourceInputLaw p)[
        actualFirstCollectionAwaitedWaitingCharge rate rewards C_star C_h |
          PhaseStartConditionalWaiting.phaseStartSigmaAlgebra
            (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0)
            (ReferenceFirstCollectionAwaitedPhaseSupport.sigma
              (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h))
            (ReferenceFirstCollectionAwaitedPhaseSupport.sigma_is_pre_round_stopping_time
              (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
              control0)] ≤ᵐ[BootstrapPrivateRoundStreams.sourceInputLaw p]
        fun _ => Bcol (p := p) := by
  let d : ℕ := p.m - 1
  let q : ℕ := 4 * AffineBatchDecoder.quota p
  let a : ℝ := 1 / ((8 : ℝ) * (d : ℝ) * (p.K : ℝ))
  let F := ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0
  let P : ℕ → BootstrapPrivateRoundStreams.SourceInput p → Finset (Fin d) :=
    fun n z => Pawait rate rewards C_star C_h n z
  let X : Fin d → ℕ → BootstrapPrivateRoundStreams.SourceInput p → Bool :=
    fun i n z => ReferenceFirstCollectionRoundEndObservation.x
      (rate := rate) rewards C_star C_h i n z
  let w : ℕ → BootstrapPrivateRoundStreams.SourceInput p → ℝ :=
    fun n z => ReferenceFirstCollectionRoundEndObservation.g rewards n z
  let sigma : BootstrapPrivateRoundStreams.SourceInput p → ℕ :=
    ReferenceFirstCollectionAwaitedPhaseSupport.sigma
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
  let theta : BootstrapPrivateRoundStreams.SourceInput p → ℕ :=
    ReferenceFirstCollectionAwaitedPhaseSupport.theta
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
  let hsigma := ReferenceFirstCollectionAwaitedPhaseSupport.sigma_is_pre_round_stopping_time
    (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) control0
  let htheta := ReferenceFirstCollectionAwaitedPhaseSupport.theta_is_pre_round_stopping_time
    (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) control0
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
    exact (ReferenceFirstCollectionAwaitedPhaseSupport.endpoint_bounds
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) z).1
  have hordered : ∀ z, sigma z ≤ theta z := by
    intro z
    exact (ReferenceFirstCollectionAwaitedPhaseSupport.endpoint_bounds
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) z).2.1
  have hthetaBound : ∀ z, theta z ≤ p.T + 1 := by
    intro z
    exact (ReferenceFirstCollectionAwaitedPhaseSupport.endpoint_bounds
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) z).2.2
  have hP : ∀ i n, n < p.T →
      MeasurableSet[F (n + 1)] {z | i ∈ P n z} := by
    intro i n hn
    simpa [F, P] using
      (ReferenceFirstCollectionAwaitedTaskSupport.Pawait_mem_measurable
        control0 rate rewards C_star C_h i ⟨n, hn⟩)
  have hphase : ∀ n, n < p.T → ∀ z, (P n z).Nonempty →
      sigma z ≤ n + 1 ∧ n + 1 < theta z := by
    intro n hn z hne
    simpa [P, sigma, theta, ReferenceFirstCollectionAwaitedPhaseSupport.Awaited] using
      (ReferenceFirstCollectionAwaitedPhaseSupport.support_nonempty_iff_phase
        (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) z n).mp hne
  have hnested : ∀ s t, s ≤ t → t < p.T → ∀ z,
      sigma z ≤ s + 1 → t + 1 < theta z → P t z ⊆ P s z := by
    intro s t hst ht z hs htheta'
    simpa [P, sigma, theta, ReferenceFirstCollectionAwaitedPhaseSupport.Awaited] using
      (ReferenceFirstCollectionAwaitedPhaseSupport.Pawait_shrinking
        (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
        z hst hs htheta')
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
      (ReferenceFirstCollectionRoundEndObservation.observation_stronglyMeasurable
        (rate := rate) rewards C_star C_h control0 i n)
  have hterminalCount : ∀ (i : Fin d) z,
      PhaseServiceWaiting.N P X i p.T z ≤ q := by
    intro i z
    simpa [P, X, q] using
      (ReferenceFirstCollectionAwaitedPhaseSupport.N_le_fourQ
        (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
        control0 z i p.T)
  have hservice : ∀ i n, n < p.T →
      ∀ᵐ z ∂BootstrapPrivateRoundStreams.sourceInputLaw p,
        i ∈ P n z →
          a * w n z ≤
            (BootstrapPrivateRoundStreams.sourceInputLaw p)[
              PhaseServiceWaiting.observation X i n | F (n + 1)] z := by
    intro i n hn
    filter_upwards [ReferenceFirstCollectionAwaitedTaskSupport.Pawait_service
      (control0 := control0) (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h)] with z hz
    intro hi
    have hmean := hz i ⟨n, hn⟩ hi
    have hobs := ReferenceFirstCollectionRoundEndObservation.observation_eq_X
      (rate := rate) rewards C_star C_h i n hn
    rw [← hobs] at hmean
    have hmean' :
        (BootstrapPrivateRoundStreams.sourceInputLaw p)[
          PhaseServiceWaiting.observation X i n |
            ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (n + 1)] z =
          (ReferenceFirstCollectionUpConditionalService.positiveRewardCount
            rewards ⟨n, hn⟩ : ℝ) /
            (8 * (p.m - 1 : ℝ) * (p.K : ℝ)) := by
      simpa [X] using hmean
    have hvalue :
        (BootstrapPrivateRoundStreams.sourceInputLaw p)[
          PhaseServiceWaiting.observation X i n | F (n + 1)] z =
          w n z / ((8 : ℝ) * (d : ℝ) * (p.K : ℝ)) := by
      simpa [F, w, d, Nat.cast_sub hm1,
        ReferenceFirstCollectionRoundEndObservation.g, hn] using hmean'
    rw [hvalue]
    change (1 / ((8 : ℝ) * (d : ℝ) * (p.K : ℝ))) * w n z ≤ _
    rw [div_eq_mul_inv]
    exact le_of_eq (by ring)
  have hchargeInt := PhaseServiceWaiting.totalCharge_exp_integrable
    (BootstrapPrivateRoundStreams.sourceInputLaw p) F P sigma theta w a ha
    hsigma htheta hP hwMeas hphase hwBound
  have hcoefficient :
      (((q : ℝ) + Real.log (d : ℝ)) /
          (PhaseServiceWaiting.kappa * a)) = Bcol (p := p) := by
    have hdReal : (d : ℝ) ≠ 0 := ne_of_gt hd
    have hKReal : (p.K : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hK)
    have hkappa : PhaseServiceWaiting.kappa ≠ 0 :=
      ne_of_gt PhaseServiceWaiting.kappa_pos
    have hdenom : (8 : ℝ) * (d : ℝ) * (p.K : ℝ) ≠ 0 := by
      positivity
    have hkappa' : 1 - Real.exp (-1) ≠ 0 := by
      simpa [PhaseServiceWaiting.kappa] using hkappa
    dsimp [a, q, d, Bcol]
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
  refine ⟨?_, ?_, ?_⟩
  · change Integrable
      (PhaseServiceWaiting.totalCharge P sigma theta w p.T)
      (BootstrapPrivateRoundStreams.sourceInputLaw p)
    exact hchargeInt.1
  · calc
      (∫ z in B,
        actualFirstCollectionAwaitedWaitingCharge rate rewards C_star C_h z
          ∂BootstrapPrivateRoundStreams.sourceInputLaw p) ≤
          (((q : ℝ) + Real.log (d : ℝ)) /
            (PhaseServiceWaiting.kappa * a)) *
              (BootstrapPrivateRoundStreams.sourceInputLaw p).real B := by
        simpa [actualFirstCollectionAwaitedWaitingCharge, P, X, w, sigma, theta] using
          hsetGeneric
      _ = Bcol (p := p) * (BootstrapPrivateRoundStreams.sourceInputLaw p).real B := by
        rw [hcoefficient]
  · change (BootstrapPrivateRoundStreams.sourceInputLaw p)[
      PhaseServiceWaiting.totalCharge P sigma theta w p.T |
        PhaseStartConditionalWaiting.phaseStartSigmaAlgebra F sigma hsigma] ≤ᵐ[
          BootstrapPrivateRoundStreams.sourceInputLaw p]
      fun _ => Bcol (p := p)
    simpa only [hcoefficient] using hcondGeneric

/-- Integrability of the actual awaited waiting charge under the original
source-input law. -/
theorem actual_first_collection_awaited_waiting_charge_integrable
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p) :
    Integrable
      (actualFirstCollectionAwaitedWaitingCharge rate rewards C_star C_h)
      (BootstrapPrivateRoundStreams.sourceInputLaw p) := by
  exact (actual_first_collection_awaited_waiting_bounds
    rate rewards C_star C_h control0 Set.univ MeasurableSet.univ).1

/-- Every event in the exact source phase-start σ-algebra localizes the
actual awaited waiting charge with its unnormalized source-law mass. -/
theorem actual_first_collection_awaited_waiting_charge_setIntegral_bound
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (B : Set (BootstrapPrivateRoundStreams.SourceInput p))
    (hB : MeasurableSet[
      PhaseStartConditionalWaiting.phaseStartSigmaAlgebra
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0)
        (ReferenceFirstCollectionAwaitedPhaseSupport.sigma
          (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h))
        (ReferenceFirstCollectionAwaitedPhaseSupport.sigma_is_pre_round_stopping_time
          (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
          control0)] B) :
    (∫ z in B,
      actualFirstCollectionAwaitedWaitingCharge rate rewards C_star C_h z
        ∂BootstrapPrivateRoundStreams.sourceInputLaw p) ≤
      Bcol (p := p) * (BootstrapPrivateRoundStreams.sourceInputLaw p).real B := by
  exact (actual_first_collection_awaited_waiting_bounds
    rate rewards C_star C_h control0 B hB).2.1

/-- The actual `Pawait` charge has the phase-start conditional-expectation
bound under the same original source-input law and history field. -/
theorem actual_first_collection_awaited_waiting_charge_condExp_bound
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p) :
      (BootstrapPrivateRoundStreams.sourceInputLaw p)[
      actualFirstCollectionAwaitedWaitingCharge rate rewards C_star C_h |
        PhaseStartConditionalWaiting.phaseStartSigmaAlgebra
          (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0)
          (ReferenceFirstCollectionAwaitedPhaseSupport.sigma
            (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h))
          (ReferenceFirstCollectionAwaitedPhaseSupport.sigma_is_pre_round_stopping_time
            (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
            control0)] ≤ᵐ[BootstrapPrivateRoundStreams.sourceInputLaw p]
      fun _ => Bcol (p := p) := by
  exact (actual_first_collection_awaited_waiting_bounds
    rate rewards C_star C_h control0 Set.univ MeasurableSet.univ).2.2

end Bandits.Support.ReferenceFirstCollectionAwaitedWaitingCost

end
