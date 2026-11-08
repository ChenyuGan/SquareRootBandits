/-
Copyright (c) 2026 The Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveConditionalWeightedDrift
public import Bandits.Support.ReferenceFirstLaunchCommonUpdateSource

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# First-launch queue energy on the actual source stratum

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:140-188,245-318`,
`sources/zip4/manuscript/06_interruptions.tex:391-408,425-426`,
`sources/zip4/manuscript/07_public_setup.tex:145-164`, and
`sources/zip4/manuscript/08_main_theorem.tex:78-104`.

This module bounds the energy and backlog exponential after the inclusive
first-launch update, integrating over the inherited, possibly null source
stratum. The accepted first-launch source law and common update are consumed
without redrawing the assignment, selected index, or private coordinates. This
is an internal initialization estimate; it does not close a calendar sum or a
manuscript theorem.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Bandits.Support.ReferenceFirstLaunchEnergyInitialization

open ConstructorDimensions
open RecordedQueueRun

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev RewardTable := ActualInitializationPhysicalStep.GridRewardTable
abbrev TimeControl := ContinuousLearningRows.TimeControl

variable {p : Parameters} (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (q : Fin (ConstructorDimensions.M p))
    (t : Fin p.T) (control0 : TimeControl p)

local notation "Zbirth" => ReferenceTotalSourceDisintegration.SourceStratum
  rate rewards C_star C_h t
  (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t)
local notation "muBirth" => ReferenceTotalSourceDisintegration.sourceStratumMeasure
  rate rewards C_star C_h t
  (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t)
local notation "Q" => ReferenceFirstLaunchNumericalCell.queueParameters rate
local notation "beta" => CanonicalRecordingRates.beta p rate.eta.val
local notation "birthY" => ReferenceFirstLaunchCommonUpdateSource.firstConservedReadout
  rate rewards C_star C_h q t control0
local notation "firstUpdate" => ReferenceFirstLaunchCommonUpdateSource.firstUpdate
  rate rewards C_star C_h q t control0

/-- The actual post-update weighted square potential on the first-launch
source stratum. -/
def birthPotential (z : Zbirth) : ℝ :=
  RecordedWeightedDrift.weightedSquarePotential p.m Q (firstUpdate z)

/-- The canonical beta-exponential of an actual post-update normalized backlog.
The run is the inclusive first update, even when it crosses overflow. -/
def birthBacklogExponential (j : Fin p.K) (z : Zbirth) : ℝ :=
  Real.exp (beta * StoppedQueueBound.normalizedBacklog Q (firstUpdate z) j)

private theorem birthSourceMass_eq_remainderMass :
    muBirth Set.univ =
      ReferenceRetainedSourceCoupling.retainedRemainderMeasure rate rewards C_star C_h
        q t t.val le_rfl control0 Set.univ := by
  let g := fun z : Zbirth =>
    let c := ReferenceFirstLaunchRecordingSourceLaw.sourceCoordinates
      rate rewards C_star C_h q t control0 z
    ((c.1, c.2.1), ReferenceFirstLaunchRecordingSourceLaw.sourceMarker
      rate rewards C_star C_h q t control0 z)
  have hcoords := ReferenceFirstLaunchRecordingSourceLaw.measurable_sourceCoordinates
    rate rewards C_star C_h q t control0
  have hmarker := ReferenceFirstLaunchRecordingSourceLaw.measurable_sourceMarker
    rate rewards C_star C_h q t control0
  have hg : Measurable g := by
    dsimp only [g]
    exact (hcoords.fst.prodMk hcoords.snd.fst).prodMk hmarker
  have hmap :
      (muBirth).map g =
        ((ReferenceRetainedSourceCoupling.retainedRemainderMeasure rate rewards C_star C_h
          q t t.val le_rfl control0).prod (ContinuousControlSlice.assignmentLaw p.K)).prod
            (ReferenceFirstLaunchRecordingSourceLaw.outcomeLaw rate) := by
    simpa only [g] using
      (ReferenceFirstLaunchRecordingSourceLaw.source_joint_map
        rate rewards C_star C_h q t control0)
  have hmass := congrArg (fun μ => μ Set.univ) hmap
  rw [Measure.map_apply hg MeasurableSet.univ, Set.preimage_univ,
    ← Set.univ_prod_univ, Measure.prod_prod,
    ← Set.univ_prod_univ, Measure.prod_prod] at hmass
  have hassignMass : (ContinuousControlSlice.assignmentLaw p.K) Set.univ = 1 :=
    measure_univ
  have houtcomeMass :
      (ReferenceFirstLaunchRecordingSourceLaw.outcomeLaw rate) Set.univ = 1 :=
    measure_univ
  rw [hassignMass, houtcomeMass] at hmass
  simpa only [mul_one] using hmass

private theorem birthSourceRealMass_eq_remainderRealMass :
    (muBirth Set.univ).toReal =
      (ReferenceRetainedSourceCoupling.retainedRemainderMeasure rate rewards C_star C_h
        q t t.val le_rfl control0 Set.univ).toReal := by
  exact congrArg ENNReal.toReal
    (birthSourceMass_eq_remainderMass rate rewards C_star C_h q t control0)

private theorem birthAssignmentRealMass :
    (ContinuousControlSlice.assignmentLaw p.K Set.univ).toReal = 1 := by
  simp

private theorem birth_readout_bounds (z : Zbirth) (j : Fin p.K) :
    0 ≤ birthY z j ∧ birthY z j ≤ 1 / beta := by
  let rho : ℝ := ((rewards t j).val : ℝ) / (D p : ℝ)
  let xi : ℝ := CanonicalRecordingRates.xi p rate.eta.val (fun _ => 1) j
  let value : ℝ := QuantizedRecordingMoments.quantizedValue
    (D p) rate.eta.val xi rho
  have hD : 0 < (D p : ℝ) := Nat.cast_pos.mpr (D_pos p)
  have hrho : rho ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [rho]
    refine ⟨div_nonneg (Nat.cast_nonneg _) hD.le, (div_le_one hD).2 ?_⟩
    exact_mod_cast Nat.le_of_lt_succ (rewards t j).isLt
  have hbeta : 0 < beta := CanonicalRecordingRates.beta_pos p rate.eta.property
  have hxi : 0 < xi := by
    exact CanonicalRecordingRates.xi_pos p rate.eta.property (fun _ => 1) j
  have hbetaxi : beta ≤ xi := by
    exact CanonicalRecordingRates.beta_le_xi p rate.eta.property (fun _ => 1) j
  have hvalue_nonneg := QuantizedRecordingMoments.quantizedValue_nonneg
    (D p) rate.eta.val xi rho rate.eta.property
  have hvalue_bound := QuantizedRecordingMoments.quantizedValue_le_inv_of_beta_le
    (D p) rate.eta.val xi rho beta (D_pos p) rate.eta.property hxi hrho hbeta hbetaxi
  have hreadout := ReferenceFirstLaunchCommonUpdateSource.firstConservedReadout_eq_sourceMarker
    rate rewards C_star C_h q t control0 z j
  change birthY z j = (if
    ReferenceFirstLaunchRecordingSourceLaw.sourceMarker rate rewards C_star C_h q t control0 z = some j
    then value else 0) at hreadout
  by_cases hmarker : ReferenceFirstLaunchRecordingSourceLaw.sourceMarker
      rate rewards C_star C_h q t control0 z = some j
  · rw [hreadout, ite_eq_left hmarker]
    exact ⟨hvalue_nonneg, hvalue_bound⟩
  · rw [hreadout, ite_eq_right hmarker]
    exact ⟨by norm_num, (one_div_pos.mpr hbeta).le⟩

private theorem birth_backlog_eq_max (z : Zbirth) (j : Fin p.K) :
    StoppedQueueBound.normalizedBacklog Q (firstUpdate z) j =
      max 0 (birthY z j - 4) := by
  have hstep := ReferenceFirstLaunchCommonUpdateSource.source_first_update
    rate rewards C_star C_h q t control0 z
  have hreadout : birthY z j =
      (ReferenceFirstLaunchCommonUpdateSource.firstArrival
        rate rewards C_star C_h q t control0 z j : ℝ) /
        (rate.n : ℝ) := by
    have htotal := (hstep.1 j).2.2
    have hcast :
        ((((firstUpdate z).registers j).1 + ((firstUpdate z).registers j).2 : ℕ) : ℝ) =
          (ReferenceFirstLaunchCommonUpdateSource.firstArrival
            rate rewards C_star C_h q t control0 z j : ℝ) := by
      exact_mod_cast htotal
    change ((((firstUpdate z).registers j).1 + ((firstUpdate z).registers j).2 : ℕ) : ℝ) /
        (rate.eta.val * (D p : ℝ)) = _
    rw [hcast]
    rw [rate.n_scale]
  have henabled :
      (ReferenceFirstLaunchCommonUpdateSource.firstCell
        rate rewards C_star C_h q t control0 z).enabled = true := rfl
  have hraw :
      RecordedRoundMoments.rawEstimate Q (RecordedQueueRun.initialState p.K)
        (ReferenceFirstLaunchCommonUpdateSource.firstCell
          rate rewards C_star C_h q t control0 z) j = birthY z j := by
    rw [RecordedRoundMoments.rawEstimate_eq_normalizedQuantizedArrival_of_enabled
      Q (RecordedQueueRun.initialState p.K)
      (ReferenceFirstLaunchCommonUpdateSource.firstCell
        rate rewards C_star C_h q t control0 z) j henabled rfl]
    unfold RecordedRoundMoments.normalizedQuantizedArrival
    change (ReferenceFirstLaunchCommonUpdateSource.firstArrival
      rate rewards C_star C_h q t control0 z j : ℝ) /
        ((ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ) = birthY z j
    rw [hreadout]
    simp [ReferenceFirstLaunchNumericalCell.queueParameters]
  change StoppedQueueBound.normalizedBacklog Q
      (RecordedQueueRun.step Q (RecordedQueueRun.initialState p.K)
        (ReferenceFirstLaunchCommonUpdateSource.firstCell
          rate rewards C_star C_h q t control0 z)) j = _
  rw [RecordedWeightedDrift.normalizedBacklog_step_eq_queueNext
    Q (RecordedQueueRun.initialState p.K)
    (ReferenceFirstLaunchCommonUpdateSource.firstCell
      rate rewards C_star C_h q t control0 z) henabled rfl j,
    hraw]
  simp [QueueSquareDrift.queueNext, RecordedQueueRun.initialState,
    StoppedQueueBound.normalizedBacklog]

private theorem birth_backlog_bounds (z : Zbirth) (j : Fin p.K) :
    0 ≤ StoppedQueueBound.normalizedBacklog Q (firstUpdate z) j ∧
      StoppedQueueBound.normalizedBacklog Q (firstUpdate z) j ≤ birthY z j ∧
      StoppedQueueBound.normalizedBacklog Q (firstUpdate z) j ≤ 1 / beta := by
  have hy := birth_readout_bounds rate rewards C_star C_h q t control0 z j
  rw [birth_backlog_eq_max]
  have hmax0 : 0 ≤ max 0 (birthY z j - 4) := le_max_left _ _
  have hmaxY : max 0 (birthY z j - 4) ≤ birthY z j := by
    apply max_le
    · exact hy.1
    · linarith
  exact ⟨hmax0, hmaxY, hmaxY.trans hy.2⟩

private theorem measurable_birthReadout (j : Fin p.K) :
    Measurable (fun z : Zbirth => birthY z j) := by
  exact (ReferenceFirstLaunchCommonUpdateSource.first_update_all_arm_source_moments
    rate rewards C_star C_h q t control0 j Set.univ Set.univ
    MeasurableSet.univ MeasurableSet.univ).1

private theorem measurable_birthBacklog (j : Fin p.K) :
    Measurable (fun z : Zbirth =>
      StoppedQueueBound.normalizedBacklog Q (firstUpdate z) j) := by
  have hy := measurable_birthReadout rate rewards C_star C_h q t control0 j
  have hmax := ((measurable_const : Measurable (fun _ : Zbirth => (0 : ℝ))).max
    (hy.sub_const 4))
  have heq : (fun z : Zbirth =>
      StoppedQueueBound.normalizedBacklog Q (firstUpdate z) j) =
      fun z => max 0 (birthY z j - 4) := by
    funext z
    exact birth_backlog_eq_max rate rewards C_star C_h q t control0 z j
  rw [heq]
  exact hmax

private theorem measurable_birthArrival (j : Fin p.K) :
    Measurable (fun z : Zbirth =>
      ReferenceFirstLaunchCommonUpdateSource.firstArrival
        rate rewards C_star C_h q t control0 z j) := by
  have hy := measurable_birthReadout rate rewards C_star C_h q t control0 j
  have hfloor (z : Zbirth) :
      Nat.floor (birthY z j * (rate.n : ℝ)) =
        ReferenceFirstLaunchCommonUpdateSource.firstArrival
          rate rewards C_star C_h q t control0 z j := by
    have hreadout : birthY z j =
          (ReferenceFirstLaunchCommonUpdateSource.firstArrival
            rate rewards C_star C_h q t control0 z j : ℝ) /
            (rate.n : ℝ) := by
      have hstep := ReferenceFirstLaunchCommonUpdateSource.source_first_update
        rate rewards C_star C_h q t control0 z
      have htotal := (hstep.1 j).2.2
      have hcast :
          ((((firstUpdate z).registers j).1 + ((firstUpdate z).registers j).2 : ℕ) : ℝ) =
            (ReferenceFirstLaunchCommonUpdateSource.firstArrival
              rate rewards C_star C_h q t control0 z j : ℝ) := by
        exact_mod_cast htotal
      change ((((firstUpdate z).registers j).1 + ((firstUpdate z).registers j).2 : ℕ) : ℝ) /
          (rate.eta.val * (D p : ℝ)) = _
      rw [hcast]
      rw [rate.n_scale]
    rw [hreadout]
    have hn : (rate.n : ℝ) ≠ 0 := by
      exact_mod_cast (ActiveFollowerDownAcceptance.rate_n_pos p rate).ne'
    rw [div_mul_cancel₀ _ hn]
    simp
  have hEq : (fun z : Zbirth =>
      ReferenceFirstLaunchCommonUpdateSource.firstArrival
        rate rewards C_star C_h q t control0 z j) =
      fun z => Nat.floor (birthY z j * (rate.n : ℝ)) := by
    funext z
    exact (hfloor z).symm
  rw [hEq]
  exact Nat.measurable_floor.comp (hy.mul_const _)

private theorem measurable_birthWeightVector :
    Measurable (fun z : Zbirth =>
      fun j : Fin p.K => RecordedQueueRun.scoreWeight Q (firstUpdate z) j) := by
  apply measurable_pi_iff.mpr
  intro j
  have harrival := measurable_birthArrival rate rewards C_star C_h q t control0 j
  have hscoreEq (z : Zbirth) :
      ((firstUpdate z).registers j).1 = min (4 * rate.n)
        (ReferenceFirstLaunchCommonUpdateSource.firstArrival
          rate rewards C_star C_h q t control0 z j) := by
    exact congrArg Prod.fst
      ((ReferenceFirstLaunchCommonUpdateSource.source_first_update
        rate rewards C_star C_h q t control0 z).1 j).2.1
  have hscore : Measurable (fun z : Zbirth => ((firstUpdate z).registers j).1) := by
    have hfun : (fun z : Zbirth => ((firstUpdate z).registers j).1) =
        fun z => min (4 * rate.n)
          (ReferenceFirstLaunchCommonUpdateSource.firstArrival
            rate rewards C_star C_h q t control0 z j) := by
      funext z
      exact hscoreEq z
    rw [hfun]
    exact measurable_const.min harrival
  change Measurable (fun z : Zbirth =>
    ScoreWeights.scoreWeight (1 + 1 / ((ReferenceFirstLaunchNumericalCell.queueParameters rate).D : ℝ))
      ((firstUpdate z).registers j).1)
  exact measurable_const.pow hscore

private theorem measurable_birthThetaVector (j : Fin p.K) :
    Measurable (fun z : Zbirth => ProductSetLaw.theta p.m
      (fun i : Fin p.K => RecordedQueueRun.scoreWeight Q (firstUpdate z) i) j) := by
  have hw := measurable_birthWeightVector rate rewards C_star C_h q t control0
  have hsetWeight (S : Finset (Fin p.K)) :
      Measurable (fun z : Zbirth => ProductSetLaw.setWeight
        (fun i : Fin p.K => RecordedQueueRun.scoreWeight Q (firstUpdate z) i) S) := by
    unfold ProductSetLaw.setWeight
    exact Finset.measurable_fun_prod S (fun i _ => (measurable_pi_apply i).comp hw)
  have htotal : Measurable (fun z : Zbirth =>
      FiniteNormalization.totalMass (ProductSetLaw.support p.K p.m)
        (fun S => ProductSetLaw.setWeight
          (fun i : Fin p.K => RecordedQueueRun.scoreWeight Q (firstUpdate z) i) S)) := by
    unfold FiniteNormalization.totalMass
    exact Finset.measurable_fun_sum _ (fun S _ => hsetWeight S)
  unfold ProductSetLaw.theta FiniteNormalization.mass
  apply Finset.measurable_fun_sum
  intro S hS
  unfold FiniteNormalization.normalizedWeight
  exact (hsetWeight S).div htotal

private theorem measurable_birthPotential_internal :
    Measurable (birthPotential rate rewards C_star C_h q t control0) := by
  unfold birthPotential RecordedWeightedDrift.weightedSquarePotential
  apply Finset.measurable_fun_sum
  intro j hj
  exact (measurable_birthThetaVector rate rewards C_star C_h q t control0 j).mul
    ((measurable_birthBacklog rate rewards C_star C_h q t control0 j).pow_const 2)

/-- Measurability of the literal first-update weighted square potential. -/
theorem measurable_birthPotential :
    Measurable (birthPotential rate rewards C_star C_h q t control0) :=
  measurable_birthPotential_internal rate rewards C_star C_h q t control0

private theorem birth_initialWeight_eq_one (j : Fin p.K) :
    RecordedQueueRun.scoreWeight Q (RecordedQueueRun.initialState p.K) j = 1 := by
  simp [RecordedQueueRun.scoreWeight, RecordedQueueRun.initialState,
    ScoreWeights.scoreWeight]

private theorem birth_theta_nonneg (z : Zbirth) (j : Fin p.K) :
    0 ≤ ProductSetLaw.theta p.m
      (fun i : Fin p.K => RecordedQueueRun.scoreWeight Q (firstUpdate z) i) j := by
  exact (RecordedMarginalGrowth.state_theta_pos Q (firstUpdate z) j
    (ConstructorDimensions.m_pos p) p.m_lt_K).le

private theorem birth_potential_nonneg (z : Zbirth) :
    0 ≤ birthPotential rate rewards C_star C_h q t control0 z := by
  unfold birthPotential RecordedWeightedDrift.weightedSquarePotential
  apply Finset.sum_nonneg
  intro j hj
  exact mul_nonneg (birth_theta_nonneg rate rewards C_star C_h q t control0 z j)
    (sq_nonneg _)

private theorem birth_potential_uniform_bound (z : Zbirth) :
    birthPotential rate rewards C_star C_h q t control0 z ≤
      (p.m : ℝ) * (1 / beta) ^ 2 := by
  have hsum := RecordedMarginalGrowth.state_sum_theta_eq_m Q (firstUpdate z)
    (ConstructorDimensions.m_pos p) p.m_lt_K
  have hinv : 0 ≤ 1 / beta := (one_div_pos.mpr
    (CanonicalRecordingRates.beta_pos p rate.eta.property)).le
  unfold birthPotential RecordedWeightedDrift.weightedSquarePotential
  calc
    _ ≤ ∑ j : Fin p.K,
        ProductSetLaw.theta p.m
          (fun i : Fin p.K => RecordedQueueRun.scoreWeight Q (firstUpdate z) i) j *
          (1 / beta) ^ 2 := by
      apply Finset.sum_le_sum
      intro j hj
      have hb := birth_backlog_bounds rate rewards C_star C_h q t control0 z j
      have hsq :
          StoppedQueueBound.normalizedBacklog Q (firstUpdate z) j ^ 2 ≤
            (1 / beta) ^ 2 := (sq_le_sq₀ hb.1 hinv).2 hb.2.2
      exact mul_le_mul_of_nonneg_left hsq
        (birth_theta_nonneg rate rewards C_star C_h q t control0 z j)
    _ = (p.m : ℝ) * (1 / beta) ^ 2 := by
      rw [← Finset.sum_mul, hsum]

/-- Integrability follows from the actual first-arrival bound and finiteness of
the inherited source stratum, without any mass normalization. -/
theorem integrable_birthPotential :
    Integrable (birthPotential rate rewards C_star C_h q t control0) muBirth := by
  have hmeas := measurable_birthPotential rate rewards C_star C_h q t control0
  have hC : 0 ≤ (p.m : ℝ) * (1 / beta) ^ 2 := by positivity
  apply Integrable.of_bound hmeas.aestronglyMeasurable
    ((p.m : ℝ) * (1 / beta) ^ 2)
  filter_upwards with z
  rw [Real.norm_eq_abs, abs_of_nonneg
    (birth_potential_nonneg rate rewards C_star C_h q t control0 z)]
  exact birth_potential_uniform_bound rate rewards C_star C_h q t control0 z

private theorem birth_weightedArrival_square_integrable :
    Integrable (fun z : Zbirth => ∑ j : Fin p.K,
      ProductSetLaw.theta p.m
        (fun _ : Fin p.K => (1 : ℝ)) j * (birthY z j) ^ 2) muBirth := by
  apply integrable_finsetSum Finset.univ
  intro j hj
  have hmom := ReferenceFirstLaunchCommonUpdateSource.first_update_all_arm_source_moments
    rate rewards C_star C_h q t control0 j Set.univ Set.univ
    MeasurableSet.univ MeasurableSet.univ
  exact hmom.2.2.2.1.const_mul
    (ProductSetLaw.theta p.m (fun _ : Fin p.K => (1 : ℝ)) j)

private theorem birth_weightedArrival_square_integral_bound :
    (∫ z : Zbirth, ∑ j : Fin p.K,
      ProductSetLaw.theta p.m (fun _ : Fin p.K => (1 : ℝ)) j * (birthY z j) ^ 2
      ∂muBirth) ≤ CanonicalRecordingRates.R p * (muBirth Set.univ).toReal := by
  have hmass := birthSourceRealMass_eq_remainderRealMass rate rewards C_star C_h q t control0
  have hmass_nonneg : 0 ≤ (muBirth Set.univ).toReal := MeasureTheory.measureReal_nonneg
  have hR := CanonicalRecordingRates.sum_theta_div_xi_le_R p rate.eta.property
    (fun _ => 1) (fun _ => 1) (by intro i; norm_num)
    (by intro i; exact ⟨le_rfl, by norm_num⟩)
  have hterm (j : Fin p.K) :
      (∫ z : Zbirth, ProductSetLaw.theta p.m (fun _ : Fin p.K => (1 : ℝ)) j *
        (birthY z j) ^ 2 ∂muBirth) ≤
        (muBirth Set.univ).toReal *
          (ProductSetLaw.theta p.m (fun _ : Fin p.K => (1 : ℝ)) j /
            CanonicalRecordingRates.xi p rate.eta.val (fun _ => 1) j) := by
    let xi : ℝ := CanonicalRecordingRates.xi p rate.eta.val (fun _ => 1) j
    let rho : ℝ := ((rewards t j).val : ℝ) / (D p : ℝ)
    let value : ℝ := QuantizedRecordingMoments.quantizedValue (D p) rate.eta.val xi rho
    have hmom := ReferenceFirstLaunchCommonUpdateSource.first_update_all_arm_source_moments
      rate rewards C_star C_h q t control0 j Set.univ Set.univ
      MeasurableSet.univ MeasurableSet.univ
    have hsecond :
        (∫ z : Zbirth, (birthY z j) ^ 2 ∂muBirth) =
          (muBirth Set.univ).toReal * (xi * value ^ 2) := by
      have hraw := hmom.2.2.2.2.2
      have hfactor :
          (ReferenceRetainedSourceCoupling.retainedRemainderMeasure rate rewards C_star C_h
            q t t.val le_rfl control0 Set.univ).toReal *
            (ContinuousControlSlice.assignmentLaw p.K Set.univ).toReal =
              (muBirth Set.univ).toReal := by
        rw [birthAssignmentRealMass (p := p)]
        rw [← hmass]
        ring
      have hraw' := hraw
      have hset :
          {z : Zbirth |
            (ReferenceFirstLaunchRecordingSourceLaw.sourceCoordinates
              rate rewards C_star C_h q t control0 z).1 ∈ Set.univ ∧
            (ReferenceFirstLaunchRecordingSourceLaw.sourceCoordinates
              rate rewards C_star C_h q t control0 z).2.1 ∈ Set.univ} =
            (Set.univ : Set Zbirth) := by
        ext z
        simp
      rw [hset, setIntegral_univ] at hraw'
      calc
        _ = (ReferenceRetainedSourceCoupling.retainedRemainderMeasure rate rewards C_star C_h
            q t t.val le_rfl control0 Set.univ).toReal *
              ((ContinuousControlSlice.assignmentLaw p.K Set.univ).toReal * (xi * value ^ 2)) := by
            simpa only [xi, rho, value, mul_assoc] using hraw'
        _ = (muBirth Set.univ).toReal * (xi * value ^ 2) := by
            calc
              _ = ((ReferenceRetainedSourceCoupling.retainedRemainderMeasure rate rewards C_star C_h
                  q t t.val le_rfl control0 Set.univ).toReal *
                  (ContinuousControlSlice.assignmentLaw p.K Set.univ).toReal) *
                    (xi * value ^ 2) := by ring
              _ = _ := by rw [hfactor]
    have hcoef := ReferenceFirstLaunchCommonUpdateSource.first_update_moment_coefficients_bounds
      rate rewards t j
    have hcoefBound : xi * value ^ 2 ≤ 1 / xi := by
      dsimp only [xi, rho, value] at hcoef ⊢
      exact hcoef.2.2.1.trans hcoef.2.2.2
    have htheta0 : 0 ≤ ProductSetLaw.theta p.m (fun _ : Fin p.K => (1 : ℝ)) j := by
      exact (ProductSetLaw.theta_pos (fun _ => 1) j
        (Nat.zero_lt_of_lt p.two_le_m) p.m_lt_K (by intro i; norm_num)).le
    have hxi_pos : 0 < xi := by
      exact CanonicalRecordingRates.xi_pos p rate.eta.property (fun _ => 1) j
    rw [integral_const_mul]
    rw [hsecond]
    calc
      ProductSetLaw.theta p.m (fun _ : Fin p.K => (1 : ℝ)) j *
          ((muBirth Set.univ).toReal * (xi * value ^ 2)) ≤
        ProductSetLaw.theta p.m (fun _ : Fin p.K => (1 : ℝ)) j *
          ((muBirth Set.univ).toReal * (1 / xi)) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hcoefBound hmass_nonneg) htheta0
      _ = (muBirth Set.univ).toReal *
          (ProductSetLaw.theta p.m (fun _ : Fin p.K => (1 : ℝ)) j / xi) := by
            rw [div_eq_mul_inv]
            ring
  have hsumInt := birth_weightedArrival_square_integrable
    rate rewards C_star C_h q t control0
  calc
    _ = ∑ j : Fin p.K, ∫ z : Zbirth,
        ProductSetLaw.theta p.m (fun _ : Fin p.K => (1 : ℝ)) j *
          (birthY z j) ^ 2 ∂muBirth := by
      rw [integral_finsetSum Finset.univ]
      intro j hj
      have hmom := ReferenceFirstLaunchCommonUpdateSource.first_update_all_arm_source_moments
        rate rewards C_star C_h q t control0 j Set.univ Set.univ
        MeasurableSet.univ MeasurableSet.univ
      exact hmom.2.2.2.1.const_mul _
    _ ≤ ∑ j : Fin p.K, (muBirth Set.univ).toReal *
        (ProductSetLaw.theta p.m (fun _ : Fin p.K => (1 : ℝ)) j /
          CanonicalRecordingRates.xi p rate.eta.val (fun _ => 1) j) :=
      Finset.sum_le_sum (fun j hj => hterm j)
    _ = (muBirth Set.univ).toReal * ∑ j : Fin p.K,
        ProductSetLaw.theta p.m (fun _ : Fin p.K => (1 : ℝ)) j /
          CanonicalRecordingRates.xi p rate.eta.val (fun _ => 1) j := by
      rw [← Finset.mul_sum]
    _ ≤ (muBirth Set.univ).toReal * CanonicalRecordingRates.R p := by
      exact mul_le_mul_of_nonneg_left hR hmass_nonneg
    _ = CanonicalRecordingRates.R p * (muBirth Set.univ).toReal := by ring

private theorem birth_eta_R_bound :
    8 * rate.eta.val * CanonicalRecordingRates.R p ≤ (p.m : ℝ) := by
  have hm : 0 < (p.m : ℝ) := Nat.cast_pos.mpr (ConstructorDimensions.m_pos p)
  have hK : 0 < (p.K : ℝ) := Nat.cast_pos.mpr (ConstructorDimensions.K_pos p)
  have hLnat := CanonicalRecordingRates.L_stab_ge_one p
  have hL : (1 : ℝ) ≤ (CanonicalRecordingRates.L_stab p : ℝ) := by exact_mod_cast hLnat
  have hden : 0 < 1024 * (p.m : ℝ) * (p.K : ℝ) *
      (CanonicalRecordingRates.L_stab p : ℝ) := by positivity
  have hEtaDen : rate.eta.val *
      (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (CanonicalRecordingRates.L_stab p : ℝ)) ≤ 1 :=
    (le_div_iff₀ hden).mp rate.sourceCap
  have hKfactor : (2 * (p.K : ℝ) - (p.m : ℝ)) ≤
      2 * (p.K : ℝ) * (CanonicalRecordingRates.L_stab p : ℝ) := by
    have hmK : (p.m : ℝ) ≤ (p.K : ℝ) := by
      exact_mod_cast Nat.le_of_lt p.m_lt_K
    calc
      2 * (p.K : ℝ) - (p.m : ℝ) ≤ 2 * (p.K : ℝ) := by linarith
      _ = 2 * (p.K : ℝ) * 1 := by ring
      _ ≤ 2 * (p.K : ℝ) * (CanonicalRecordingRates.L_stab p : ℝ) :=
        mul_le_mul_of_nonneg_left hL (by positivity)
  have hcoef :
      512 * (p.m : ℝ) ^ 2 * (2 * (p.K : ℝ) - (p.m : ℝ)) ≤
        (p.m : ℝ) * (1024 * (p.m : ℝ) * (p.K : ℝ) *
          (CanonicalRecordingRates.L_stab p : ℝ)) := by
    have := mul_le_mul_of_nonneg_left hKfactor (by positivity :
      0 ≤ 512 * (p.m : ℝ) ^ 2)
    nlinarith only [this]
  calc
    8 * rate.eta.val * CanonicalRecordingRates.R p =
        rate.eta.val *
          (512 * (p.m : ℝ) ^ 2 * (2 * (p.K : ℝ) - (p.m : ℝ))) := by
            simp [CanonicalRecordingRates.R]
            ring
    _ ≤ rate.eta.val *
        ((p.m : ℝ) * (1024 * (p.m : ℝ) * (p.K : ℝ) *
          (CanonicalRecordingRates.L_stab p : ℝ))) :=
            mul_le_mul_of_nonneg_left hcoef rate.eta.property.le
    _ = (p.m : ℝ) *
        (rate.eta.val * (1024 * (p.m : ℝ) * (p.K : ℝ) *
          (CanonicalRecordingRates.L_stab p : ℝ))) := by ring
    _ ≤ (p.m : ℝ) := by nlinarith only [hEtaDen, hm]

/-- The first-update potential integral has the requested source constant. -/
theorem integral_birthPotential :
    (∫ z : Zbirth, birthPotential rate rewards C_star C_h q t control0 z ∂muBirth) ≤
      (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) *
        (muBirth Set.univ).toReal := by
  let factor : ℝ := 1 + 8 * rate.eta.val
  let theta0 : Fin p.K → ℝ := fun j => ProductSetLaw.theta p.m (fun _ => 1) j
  let A : Zbirth → ℝ := fun z => ∑ j : Fin p.K, theta0 j * (birthY z j) ^ 2
  have hfactor : 0 ≤ factor := by
    have heta := rate.eta.property
    dsimp [factor]
    linarith
  have hmass : 0 ≤ (muBirth Set.univ).toReal := MeasureTheory.measureReal_nonneg
  have hsmall : rate.eta.val ≤ 1 / 64 := by
    have hcap : (ReferenceFirstLaunchNumericalCell.queueParameters rate).eta ≤
        1 / (1024 * (p.m : ℝ) * (p.K : ℝ) *
          (CanonicalRecordingRates.L_stab p : ℝ)) := by
      simpa only [ReferenceFirstLaunchNumericalCell.queueParameters] using rate.sourceCap
    exact RecordedWeightedDrift.eta_le_one_div_sixtyFour p
      (ReferenceFirstLaunchNumericalCell.queueParameters rate) hcap
  have hpoint (z : Zbirth) : birthPotential rate rewards C_star C_h q t control0 z ≤
      factor * A z := by
    have hgrowth (j : Fin p.K) := RecordedMarginalGrowth.step_theta_growth
      Q (RecordedQueueRun.initialState p.K)
      (ReferenceFirstLaunchCommonUpdateSource.firstCell
        rate rewards C_star C_h q t control0 z) j p.two_le_m p.m_lt_K hsmall
    have hweight0 :
        (RecordedQueueRun.scoreWeight Q (RecordedQueueRun.initialState p.K)) =
          fun _ => 1 := by
      funext j
      exact birth_initialWeight_eq_one rate j
    have hsum :
        birthPotential rate rewards C_star C_h q t control0 z =
          ∑ j : Fin p.K,
            ProductSetLaw.theta p.m
              (fun i : Fin p.K => RecordedQueueRun.scoreWeight Q (firstUpdate z) i) j *
              (StoppedQueueBound.normalizedBacklog Q (firstUpdate z) j) ^ 2 := rfl
    rw [hsum]
    calc
      _ ≤ ∑ j : Fin p.K,
          (1 + 8 * rate.eta.val) * theta0 j * (birthY z j) ^ 2 := by
        apply Finset.sum_le_sum
        intro j hj
        have hgrowthj := hgrowth j
        have htheta := hgrowthj.1.trans hgrowthj.2
        rw [hweight0] at htheta
        have hb := birth_backlog_bounds rate rewards C_star C_h q t control0 z j
        have hθ0 : 0 ≤ theta0 j := by
          dsimp [theta0]
          exact (ProductSetLaw.theta_pos (fun _ => 1) j
            (Nat.zero_lt_of_lt p.two_le_m) p.m_lt_K (by intro i; norm_num)).le
        have hsq :
            (StoppedQueueBound.normalizedBacklog Q (firstUpdate z) j) ^ 2 ≤
              (birthY z j) ^ 2 := (sq_le_sq₀ hb.1 (birth_readout_bounds
                rate rewards C_star C_h q t control0 z j).1).2 hb.2.1
        calc
          ProductSetLaw.theta p.m
              (fun i : Fin p.K => RecordedQueueRun.scoreWeight Q (firstUpdate z) i) j *
                (StoppedQueueBound.normalizedBacklog Q (firstUpdate z) j) ^ 2 ≤
              ((1 + 8 * rate.eta.val) * theta0 j) *
                (StoppedQueueBound.normalizedBacklog Q (firstUpdate z) j) ^ 2 :=
            mul_le_mul_of_nonneg_right htheta (sq_nonneg _)
          _ ≤ ((1 + 8 * rate.eta.val) * theta0 j) * (birthY z j) ^ 2 :=
            mul_le_mul_of_nonneg_left hsq
              (mul_nonneg (by positivity [rate.eta.property]) hθ0)
          _ = (1 + 8 * rate.eta.val) * theta0 j * (birthY z j) ^ 2 := by ring
      _ = factor * A z := by
        dsimp [factor, A]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring

  have hsumInt := birth_weightedArrival_square_integrable
    rate rewards C_star C_h q t control0
  have hAint : Integrable A muBirth := by
    simpa only [A, theta0] using hsumInt
  have hpotentialInt := integrable_birthPotential
    rate rewards C_star C_h q t control0
  have hfactorInt : Integrable (fun z : Zbirth => factor * A z) muBirth :=
    hAint.const_mul factor
  have hRhs := birth_weightedArrival_square_integral_bound
    rate rewards C_star C_h q t control0
  have hRsum := CanonicalRecordingRates.sum_theta_div_xi_le_R p rate.eta.property
    (fun _ => 1) (fun _ => 1) (by intro i; norm_num)
    (by intro i; exact ⟨le_rfl, by norm_num⟩)
  have hR_nonneg : 0 ≤ CanonicalRecordingRates.R p := by
    unfold CanonicalRecordingRates.R
    have hmK : (p.m : ℝ) ≤ (p.K : ℝ) := by
      exact_mod_cast Nat.le_of_lt p.m_lt_K
    have hsub : 0 ≤ 2 * (p.K : ℝ) - (p.m : ℝ) := by linarith
    positivity
  have hbudget : factor * CanonicalRecordingRates.R p ≤
      CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ) := by
    dsimp [factor]
    have hEtaR := birth_eta_R_bound rate
    have hm_nonneg : 0 ≤ (p.m : ℝ) := Nat.cast_nonneg _
    nlinarith only [hEtaR, hR_nonneg,
      hm_nonneg]
  calc
    _ ≤ ∫ z : Zbirth, factor * A z ∂muBirth :=
      integral_mono hpotentialInt hfactorInt hpoint
    _ = factor * ∫ z : Zbirth, A z ∂muBirth := by
      rw [integral_const_mul]
    _ ≤ factor * (CanonicalRecordingRates.R p * (muBirth Set.univ).toReal) :=
      mul_le_mul_of_nonneg_left hRhs hfactor
    _ ≤ (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) *
        (muBirth Set.univ).toReal := by
      calc
        factor * (CanonicalRecordingRates.R p * (muBirth Set.univ).toReal) =
            (factor * CanonicalRecordingRates.R p) * (muBirth Set.univ).toReal := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hbudget hmass

private theorem measurable_birthExponential_internal (j : Fin p.K) :
    Measurable (birthBacklogExponential rate rewards C_star C_h q t control0 j) := by
  unfold birthBacklogExponential
  exact Real.measurable_exp.comp
    ((measurable_const.mul
      (measurable_birthBacklog rate rewards C_star C_h q t control0 j)))

/-- Measurability of every actual first-update backlog exponential. -/
theorem measurable_birthExponential (j : Fin p.K) :
    Measurable (birthBacklogExponential rate rewards C_star C_h q t control0 j) :=
  measurable_birthExponential_internal rate rewards C_star C_h q t control0 j

private theorem integrable_birthExponential_internal (j : Fin p.K) :
    Integrable (birthBacklogExponential rate rewards C_star C_h q t control0 j) muBirth := by
  have hmeas := measurable_birthExponential rate rewards C_star C_h q t control0 j
  have hbeta : 0 < beta := CanonicalRecordingRates.beta_pos p rate.eta.property
  have hbound (z : Zbirth) :
      ‖birthBacklogExponential rate rewards C_star C_h q t control0 j z‖ ≤ Real.exp 1 := by
    rw [birthBacklogExponential, Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
    have hb := birth_backlog_bounds rate rewards C_star C_h q t control0 z j
    have hmul : beta *
        StoppedQueueBound.normalizedBacklog Q (firstUpdate z) j ≤ 1 := by
      calc
        _ ≤ beta * (1 / beta) := mul_le_mul_of_nonneg_left hb.2.2 hbeta.le
        _ = 1 := by field_simp
    exact Real.exp_le_exp.mpr hmul
  exact Integrable.of_bound hmeas.aestronglyMeasurable (Real.exp 1)
    (Filter.Eventually.of_forall hbound)

/-- Every exponential is integrable from the actual bounded first arrival and
the finite inherited stratum measure. -/
theorem integrable_birthExponential (j : Fin p.K) :
    Integrable (birthBacklogExponential rate rewards C_star C_h q t control0 j) muBirth :=
  integrable_birthExponential_internal rate rewards C_star C_h q t control0 j

private theorem birth_exponential_pointwise_bound (z : Zbirth) (j : Fin p.K) :
    birthBacklogExponential rate rewards C_star C_h q t control0 j z ≤
      1 + Real.exp (beta * (birthY z j - 4)) := by
  rw [birthBacklogExponential, birth_backlog_eq_max]
  by_cases h : birthY z j - 4 ≤ 0
  · rw [max_eq_left h, mul_zero, Real.exp_zero]
    have := Real.exp_pos (beta * (birthY z j - 4))
    linarith
  · have hpos : 0 < birthY z j - 4 := lt_of_not_ge h
    rw [max_eq_right hpos.le]
    linarith

private theorem birth_shiftedExponential_integrable (j : Fin p.K) :
    Integrable (fun z : Zbirth => Real.exp (beta * (birthY z j - 4))) muBirth := by
  have hy := measurable_birthReadout rate rewards C_star C_h q t control0 j
  have hbeta : 0 < beta := CanonicalRecordingRates.beta_pos p rate.eta.property
  have hmeas : Measurable (fun z : Zbirth =>
      Real.exp (beta * (birthY z j - 4))) := by
    exact Real.measurable_exp.comp (measurable_const.mul (hy.sub_const 4))
  have hbound (z : Zbirth) :
      ‖Real.exp (beta * (birthY z j - 4))‖ ≤ Real.exp 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
    have hb := birth_readout_bounds rate rewards C_star C_h q t control0 z j
    have hle : beta * (birthY z j - 4) ≤ 1 := by
      have : beta * birthY z j ≤ 1 := by
        calc
          _ ≤ beta * (1 / beta) := mul_le_mul_of_nonneg_left hb.2
            (CanonicalRecordingRates.beta_pos p rate.eta.property).le
          _ = 1 := by field_simp
      nlinarith only [this, CanonicalRecordingRates.beta_pos p rate.eta.property]
    exact Real.exp_le_exp.mpr hle
  exact Integrable.of_bound hmeas.aestronglyMeasurable (Real.exp 1)
    (Filter.Eventually.of_forall hbound)

private theorem birth_firstMoment_integral_bound (j : Fin p.K) :
    (∫ z : Zbirth, birthY z j ∂muBirth) ≤ (muBirth Set.univ).toReal := by
  let xi : ℝ := CanonicalRecordingRates.xi p rate.eta.val (fun _ => 1) j
  let rho : ℝ := ((rewards t j).val : ℝ) / (D p : ℝ)
  let value : ℝ := QuantizedRecordingMoments.quantizedValue (D p) rate.eta.val xi rho
  have hmom := ReferenceFirstLaunchCommonUpdateSource.first_update_all_arm_source_moments
    rate rewards C_star C_h q t control0 j Set.univ Set.univ
    MeasurableSet.univ MeasurableSet.univ
  have hmass := birthSourceRealMass_eq_remainderRealMass rate rewards C_star C_h q t control0
  have hfirst : (∫ z : Zbirth, birthY z j ∂muBirth) =
      (muBirth Set.univ).toReal * (xi * value) := by
    have hraw := hmom.2.2.2.2.1
    have hfactor :
        (ReferenceRetainedSourceCoupling.retainedRemainderMeasure rate rewards C_star C_h
          q t t.val le_rfl control0 Set.univ).toReal *
          (ContinuousControlSlice.assignmentLaw p.K Set.univ).toReal =
            (muBirth Set.univ).toReal := by
      rw [birthAssignmentRealMass (p := p)]
      rw [← hmass]
      ring
    have hraw' := hraw
    have hset :
        {z : Zbirth |
          (ReferenceFirstLaunchRecordingSourceLaw.sourceCoordinates
            rate rewards C_star C_h q t control0 z).1 ∈ Set.univ ∧
          (ReferenceFirstLaunchRecordingSourceLaw.sourceCoordinates
            rate rewards C_star C_h q t control0 z).2.1 ∈ Set.univ} =
          (Set.univ : Set Zbirth) := by
      ext z
      simp
    rw [hset, setIntegral_univ] at hraw'
    calc
      _ = (ReferenceRetainedSourceCoupling.retainedRemainderMeasure rate rewards C_star C_h
          q t t.val le_rfl control0 Set.univ).toReal *
            ((ContinuousControlSlice.assignmentLaw p.K Set.univ).toReal * (xi * value)) := by
          simpa only [xi, rho, value, mul_assoc] using hraw'
      _ = (muBirth Set.univ).toReal * (xi * value) := by
          calc
            _ = ((ReferenceRetainedSourceCoupling.retainedRemainderMeasure rate rewards C_star C_h
                q t t.val le_rfl control0 Set.univ).toReal *
                (ContinuousControlSlice.assignmentLaw p.K Set.univ).toReal) * (xi * value) := by ring
            _ = _ := by rw [hfactor]
  have hcoef := ReferenceFirstLaunchCommonUpdateSource.first_update_moment_coefficients_bounds
    rate rewards t j
  have hcoefBound : xi * value ≤ 1 := by
    dsimp only [xi, rho, value] at hcoef ⊢
    exact hcoef.2.1.trans (by
      have hD : 0 < (D p : ℝ) := Nat.cast_pos.mpr (D_pos p)
      apply (div_le_one hD).2
      exact_mod_cast Nat.le_of_lt_succ (rewards t j).isLt)
  have hmass_nonneg : 0 ≤ (muBirth Set.univ).toReal := MeasureTheory.measureReal_nonneg
  rw [hfirst]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hcoefBound hmass_nonneg

private theorem birth_expArrival_integral_bound (j : Fin p.K) :
    (∫ z : Zbirth, Real.exp (beta * birthY z j) ∂muBirth) ≤
      (1 + 2 * beta) * (muBirth Set.univ).toReal := by
  have hy := measurable_birthReadout rate rewards C_star C_h q t control0 j
  have hmom := ReferenceFirstLaunchCommonUpdateSource.first_update_all_arm_source_moments
    rate rewards C_star C_h q t control0 j Set.univ Set.univ
    MeasurableSet.univ MeasurableSet.univ
  have hyint := hmom.2.2.1
  have hexpMeas : Measurable (fun z : Zbirth => Real.exp (beta * birthY z j)) :=
    Real.measurable_exp.comp (measurable_const.mul hy)
  have hbeta : 0 < beta := CanonicalRecordingRates.beta_pos p rate.eta.property
  have hexpBound (z : Zbirth) :
      Real.exp (beta * birthY z j) ≤ 1 + 2 * (beta * birthY z j) := by
    apply RecordedMarginalGrowth.exp_le_one_add_two_mul_of_mem_unit_interval
    · exact mul_nonneg hbeta.le (birth_readout_bounds rate rewards C_star C_h q t control0 z j).1
    · calc
        beta * birthY z j ≤ beta * (1 / beta) :=
          mul_le_mul_of_nonneg_left
            (birth_readout_bounds rate rewards C_star C_h q t control0 z j).2 hbeta.le
        _ = 1 := by field_simp
  have hexpInt : Integrable (fun z : Zbirth => Real.exp (beta * birthY z j)) muBirth := by
    have hbound (z : Zbirth) :
        ‖Real.exp (beta * birthY z j)‖ ≤ Real.exp 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
      have hybound := birth_readout_bounds rate rewards C_star C_h q t control0 z j
      have hle : beta * birthY z j ≤ 1 := by
        calc
          _ ≤ beta * (1 / beta) := mul_le_mul_of_nonneg_left hybound.2 hbeta.le
          _ = 1 := by field_simp
      exact Real.exp_le_exp.mpr hle
    exact Integrable.of_bound hexpMeas.aestronglyMeasurable (Real.exp 1)
      (Filter.Eventually.of_forall hbound)
  have hlinearInt : Integrable (fun z : Zbirth =>
      1 + (2 * beta) * birthY z j) muBirth :=
    (integrable_const 1).add (hyint.const_mul (2 * beta))
  have hlinearPoint (z : Zbirth) :
      Real.exp (beta * birthY z j) ≤ 1 + (2 * beta) * birthY z j := by
    have h := hexpBound z
    nlinarith only [h]
  have hmono := integral_mono hexpInt hlinearInt hlinearPoint
  have hfirst := birth_firstMoment_integral_bound
    rate rewards C_star C_h q t control0 j
  have hmass_nonneg : 0 ≤ (muBirth Set.univ).toReal := MeasureTheory.measureReal_nonneg
  have hlinearIntegral :
      (∫ z : Zbirth, 1 + (2 * beta) * birthY z j ∂muBirth) =
        (muBirth Set.univ).toReal +
          2 * beta * (∫ z : Zbirth, birthY z j ∂muBirth) := by
    rw [integral_add (integrable_const 1) (hyint.const_mul (2 * beta))]
    rw [integral_const, integral_const_mul]
    simp [Measure.real]
  have hlinearBound :
      (∫ z : Zbirth, 1 + (2 * beta) * birthY z j ∂muBirth) ≤
        (1 + 2 * beta) * (muBirth Set.univ).toReal := by
    rw [hlinearIntegral]
    have hfirstScaled := mul_le_mul_of_nonneg_left hfirst
      (show 0 ≤ 2 * beta by positivity)
    nlinarith only [hfirstScaled, hmass_nonneg]
  exact hmono.trans hlinearBound

/-- The first-update backlog exponential is bounded in integral by twice the
actual unnormalized birth-stratum mass. -/
theorem integral_birthExponential (j : Fin p.K) :
    (∫ z : Zbirth,
      birthBacklogExponential rate rewards C_star C_h q t control0 j z ∂muBirth) ≤
      2 * (muBirth Set.univ).toReal := by
  have hbeta : 0 < beta := CanonicalRecordingRates.beta_pos p rate.eta.property
  have hxp := integrable_birthExponential rate rewards C_star C_h q t control0 j
  have hshift := birth_shiftedExponential_integrable
    rate rewards C_star C_h q t control0 j
  have hbound := birth_exponential_pointwise_bound
    rate rewards C_star C_h q t control0
  have hshiftEq (z : Zbirth) :
      Real.exp (beta * (birthY z j - 4)) =
        Real.exp (-4 * beta) * Real.exp (beta * birthY z j) := by
    rw [show beta * (birthY z j - 4) = beta * birthY z j + (-4 * beta) by ring,
      Real.exp_add]
    ring
  have hExpY := birth_expArrival_integral_bound
    rate rewards C_star C_h q t control0 j
  have hExpFactor : Real.exp (-4 * beta) * (1 + 2 * beta) ≤ 1 := by
    have hlower : 1 + 2 * beta ≤ Real.exp (4 * beta) := by
      have htwice : 2 * beta ≤ 4 * beta := by nlinarith [hbeta]
      calc
        1 + 2 * beta ≤ 1 + 4 * beta := by linarith
        _ = 4 * beta + 1 := by ring
        _ ≤ Real.exp (4 * beta) := Real.add_one_le_exp (4 * beta)
    calc
      Real.exp (-4 * beta) * (1 + 2 * beta) =
          (1 + 2 * beta) / Real.exp (4 * beta) := by
            rw [show -4 * beta = -(4 * beta) by ring, Real.exp_neg]
            ring
      _ ≤ 1 := by
        have hlower' : 1 + 2 * beta ≤ 1 * Real.exp (4 * beta) := by
          simpa only [one_mul] using hlower
        exact (div_le_iff₀ (Real.exp_pos _)).2 hlower'
  have hmass_nonneg : 0 ≤ (muBirth Set.univ).toReal := MeasureTheory.measureReal_nonneg
  have hsumPoint (z : Zbirth) :
      birthBacklogExponential rate rewards C_star C_h q t control0 j z ≤
        1 + Real.exp (beta * (birthY z j - 4)) := hbound z j
  have hsumInt : Integrable (fun z : Zbirth =>
      1 + Real.exp (beta * (birthY z j - 4))) muBirth :=
    (integrable_const 1).add hshift
  have hmono := integral_mono hxp hsumInt (fun z => hsumPoint z)
  have hshiftIntegral :
      (∫ z : Zbirth, Real.exp (beta * (birthY z j - 4)) ∂muBirth) =
        Real.exp (-4 * beta) *
          (∫ z : Zbirth, Real.exp (beta * birthY z j) ∂muBirth) := by
    simp_rw [hshiftEq]
    rw [integral_const_mul]
  have hconstant : (∫ z : Zbirth, (1 : ℝ) ∂muBirth) = (muBirth Set.univ).toReal := by
    simp [integral_const, Measure.real]
  have hsumIntegral :
      (∫ z : Zbirth, 1 + Real.exp (beta * (birthY z j - 4)) ∂muBirth) =
        (muBirth Set.univ).toReal + Real.exp (-4 * beta) *
          (∫ z : Zbirth, Real.exp (beta * birthY z j) ∂muBirth) := by
    rw [integral_add (integrable_const 1) hshift, hconstant, hshiftIntegral]
  rw [hsumIntegral] at hmono
  have hshiftBound :
      Real.exp (-4 * beta) *
          (∫ z : Zbirth, Real.exp (beta * birthY z j) ∂muBirth) ≤
        (muBirth Set.univ).toReal := by
    calc
      _ ≤ Real.exp (-4 * beta) * ((1 + 2 * beta) * (muBirth Set.univ).toReal) :=
        mul_le_mul_of_nonneg_left hExpY (Real.exp_nonneg _)
      _ = (Real.exp (-4 * beta) * (1 + 2 * beta)) * (muBirth Set.univ).toReal := by ring
      _ ≤ 1 * (muBirth Set.univ).toReal :=
        mul_le_mul_of_nonneg_right hExpFactor hmass_nonneg
      _ = _ := by ring
  calc
    _ ≤ (muBirth Set.univ).toReal +
        Real.exp (-4 * beta) *
          (∫ z : Zbirth, Real.exp (beta * birthY z j) ∂muBirth) := hmono
    _ ≤ 2 * (muBirth Set.univ).toReal := by linarith [hshiftBound]

end Bandits.Support.ReferenceFirstLaunchEnergyInitialization

end
