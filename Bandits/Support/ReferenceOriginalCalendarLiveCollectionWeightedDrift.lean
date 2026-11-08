/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceOriginalCalendarContinuingLiveRetainedEnergyStep

import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Tactic

/-!
# Original-calendar LIVE and collection weighted-square drift

The square-potential and weighted-backlog observations are read from the full
original numerical prefix. This module transports their retained one-step
drift through the original LIVE and unrestricted collection source laws.
-/

@[expose] public section

noncomputable section

open MeasureTheory Bandits.Support ConstructorDimensions
open BootstrapPrivateRoundStreams (SourceInput sourceInputLaw)
open ContinuousLearningRows (TimeControl)
open ReferenceSourcePrefixHistoryFiltration (sourcePrefixFiltration)
open ReferenceFirstCollectionRenewalIncomingQueueMeasurability (stateReadout)
open scoped Classical BigOperators

local instance optionMeasurableSpace {A : Type*} [MeasurableSpace A] :
    MeasurableSpace (Option A) :=
  ReferenceOriginalCalendarCollectionRetainedEnergyStep.optionMeasurableSpace

local instance sumMeasurableSingleton {A B : Type*} [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSingletonClass A] [MeasurableSingletonClass B] :
    MeasurableSingletonClass (A ⊕ B) where
  measurableSet_singleton x := by
    cases x with
    | inl a =>
        simpa only [Set.image_singleton] using
          (MeasurableSet.singleton a).inl_image
    | inr b =>
        simpa only [Set.image_singleton] using
          (MeasurableSet.singleton b).inr_image

local instance optionMeasurableSingleton {A : Type*} [MeasurableSpace A]
    [MeasurableSingletonClass A] : MeasurableSingletonClass (Option A) where
  measurableSet_singleton x := by
    have h := (comap_measurable (Equiv.optionEquivSumPUnit A))
      (MeasurableSet.singleton (Equiv.optionEquivSumPUnit A x))
    convert h using 1
    ext y
    simp only [Set.mem_singleton_iff, Set.mem_preimage,
      (Equiv.optionEquivSumPUnit A).injective.eq_iff]

namespace Bandits.Support.ReferenceOriginalCalendarLiveCollectionWeightedDrift

variable {p : Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ)

local notation "X" => SourceInput p
local notation "mu" => sourceInputLaw p
local notation "Q" => ReferenceFirstLaunchNumericalCell.queueParameters rate
local notation "Readout" => ReferenceFirstCollectionCurrentQueueReadout.QueueReadout p.K
local notation "Inputs" => ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
  rate rewards C_star C_h
local notation "P" => ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout
  rate rewards C_star C_h

/-- The literal zero-extended weighted-square observation of the actual full
numerical prefix. -/
public def V (n : ℕ) (z : X) : ℝ :=
  (Inputs n z).elim 0 (fun past =>
    RecordedWeightedDrift.weightedSquarePotential p.m Q (RecordedQueueRun.run Q past))

/-- The literal zero-extended weighted backlog, using the same current score
marginals as `V`. -/
public def C (n : ℕ) (z : X) : ℝ :=
  (Inputs n z).elim 0 (fun past =>
    RecordedWeightedDrift.weightedBacklog p.m Q (RecordedQueueRun.run Q past))

/-- Current full-prefix product-set marginal, with the same zero extension as
the prefix observation. -/
public def thetaAt (n : ℕ) (i : Fin p.K) (z : X) : ℝ :=
  (Inputs n z).elim 0 (fun past =>
    ProductSetLaw.theta p.m
      (RecordedQueueRun.scoreWeight Q (RecordedQueueRun.run Q past)) i)

private def stateFromReadout (r : Readout) : RecordedQueueRun.RunState p.K :=
  { registers := r.1, overflow := r.2.1, records := r.2.2 }

private theorem stateFromReadout_stateReadout (state : RecordedQueueRun.RunState p.K) :
    stateFromReadout (stateReadout state) = state := by
  cases state
  rfl

private theorem observation_measurable {F : MeasurableSpace X} (n : ℕ)
    (hP : Measurable[F] (P n)) (f : RecordedQueueRun.RunState p.K → ℝ)
    (hf : Measurable (fun r : Readout => f (stateFromReadout r))) :
    Measurable[F] (fun z => (Inputs n z).elim (0 : ℝ) (fun past => f (RecordedQueueRun.run Q past))) := by
  let obs : Option Readout → ℝ := fun o => o.elim 0 (fun r => f (stateFromReadout r))
  have hobs : Measurable obs := by
    convert (hf.sumElim measurable_const).comp
      (comap_measurable (Equiv.optionEquivSumPUnit Readout)) using 1
    funext o
    cases o <;> rfl
  convert hobs.comp hP using 1
  funext z
  cases hpast : Inputs n z with
  | none => simp only [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout,
      hpast, Option.map_none, obs, Option.elim_none, Function.comp_apply]
  | some past => simp only [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout,
      hpast, Option.map_some, obs, Option.elim_some, Function.comp_apply,
      stateFromReadout_stateReadout]

/-- Full current-score marginals are measurable in the accepted pre-choice field. -/
public theorem thetaAt_measurable (control0 : TimeControl p) (q : Fin p.T) (i : Fin p.K) :
    Measurable[sourcePrefixFiltration control0 (q.val + 1)]
      (thetaAt rate rewards C_star C_h q.val i) :=
  observation_measurable rate rewards C_star C_h q.val
    (ReferenceOriginalCalendarContinuingLiveRetainedEnergyStep.P_measurable
      rate rewards C_star C_h control0 q)
    (fun state => ProductSetLaw.theta p.m (RecordedQueueRun.scoreWeight Q state) i)
    (by
      unfold RecordedQueueRun.scoreWeight stateFromReadout ProductSetLaw.theta
        FiniteNormalization.mass FiniteNormalization.normalizedWeight
        FiniteNormalization.totalMass ProductSetLaw.setWeight ProductSetLaw.support
        ScoreWeights.scoreWeight
      fun_prop)

/-- Full-prefix inclusion marginals are nonnegative and at most one, including
the zero extension on an absent prefix. -/
public theorem thetaAt_bounds (n : ℕ) (i : Fin p.K) (z : X) :
    0 ≤ thetaAt rate rewards C_star C_h n i z ∧
      thetaAt rate rewards C_star C_h n i z ≤ 1 := by
  cases hpast : Inputs n z with
  | none => simp [thetaAt, hpast]
  | some past =>
      simp only [thetaAt, hpast, Option.elim_some]
      have hpos := RecordedMarginalGrowth.state_theta_pos Q
        (RecordedQueueRun.run Q past) i (Nat.zero_lt_of_lt p.two_le_m) p.m_lt_K
      have hlt := ProductSetLaw.theta_lt_one
        (RecordedQueueRun.scoreWeight Q (RecordedQueueRun.run Q past)) i
        (Nat.zero_lt_of_lt p.two_le_m) p.m_lt_K
        (fun j => RecordedMarginalGrowth.state_scoreWeight_pos Q
          (RecordedQueueRun.run Q past) j)
      exact ⟨hpos.le, hlt.le⟩

private theorem thetaAt_sum_eq_of_prefix (n : ℕ) (z : X)
    (past : List (RecordedQueueRun.RoundInput p.K))
    (hpast : Inputs n z = some past) :
    (∑ i : Fin p.K, thetaAt rate rewards C_star C_h n i z) = (p.m : ℝ) := by
  simp only [thetaAt, hpast, Option.elim_some]
  exact RecordedMarginalGrowth.state_sum_theta_eq_m Q
    (RecordedQueueRun.run Q past) (Nat.zero_lt_of_lt p.two_le_m) p.m_lt_K
/-- Successor minus predecessor of the actual original-calendar observation.
The successor is taken after the actual date, including a detecting update. -/
public def deltaV (q : Fin p.T) (z : X) : ℝ :=
  V rate rewards C_star C_h (q.val + 1) z - V rate rewards C_star C_h q.val z

private theorem integrable_of_uniform_bound {f : X → ℝ}
    (hf : AEStronglyMeasurable f mu) (c : ℝ) (hc : ∀ z, ‖f z‖ ≤ c) :
    Integrable f mu :=
  (integrable_const c).mono' hf (Filter.Eventually.of_forall hc)

private theorem integral_predictable_mul_condExp
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {F : MeasurableSpace Ω} (hF : F ≤ mΩ) [SigmaFinite (μ.trim hF)]
    {w f : Ω → ℝ} (hw : Measurable[F] w) (hbound : ∀ x, ‖w x‖ ≤ 1)
    (hf : Integrable f μ) :
    (∫ x, w x * f x ∂μ) = ∫ x, w x * (μ[f | F]) x ∂μ := by
  have hwμ : AEStronglyMeasurable[mΩ] w μ := (hw.mono hF le_rfl).aestronglyMeasurable
  have hprod : Integrable (fun x => w x * f x) μ := by
    have h := hf.bdd_mul hwμ (Filter.Eventually.of_forall hbound)
    simpa only [mul_comm] using h
  have hce := condExp_mul_of_aestronglyMeasurable_left (m := F)
    hw.aestronglyMeasurable hprod hf
  exact (integral_condExp (f := fun x => w x * f x) hF).symm.trans
    (integral_congr_ae hce)

/-- On the actual LIVE retained gate, the two observations are exactly the
before and after potentials of the same appended original cell. -/
public theorem live_deltaV_transition (q : Fin p.T) (z : X)
    (hz : z ∈ ReferenceOriginalCalendarContinuingLiveRetainedEnergyStep.liveRetainedGate
      rate rewards C_star C_h q) :
    ∃ (past : List (RecordedQueueRun.RoundInput p.K))
      (cell : RecordedQueueRun.RoundInput p.K),
      Inputs q.val z = some past ∧
      ReferenceOriginalCalendarCarriedStoppedEnergy.actualCellAt
        rate rewards C_star C_h q z = some cell ∧
      deltaV rate rewards C_star C_h q z =
        RecordedWeightedDrift.weightedSquarePotential p.m Q
          (RecordedQueueRun.step Q (RecordedQueueRun.run Q past) cell) -
        RecordedWeightedDrift.weightedSquarePotential p.m Q
          (RecordedQueueRun.run Q past) := by
  obtain ⟨past, cell, hpast, hcell, hnext, _, _⟩ :=
    ReferenceOriginalCalendarContinuingLiveRetainedEnergyStep.presentPrefix_append
      rate rewards C_star C_h q z hz.1
  refine ⟨past, cell, hpast, ?_, ?_⟩
  · exact hcell
  · simp [deltaV, V, hpast, hnext,
      ReferenceFirstCollectionRenewalFutureNumericalPrefix.run_append_one]

/-- The unrestricted collection readout likewise appends its actual current
cell to the same inherited prefix. -/
public theorem collection_deltaV_transition (q : Fin p.T) (z : X)
    (hz : z ∈ ReferenceOriginalCalendarCollectionRetainedEnergyStep.G
      rate rewards C_star C_h q) :
    ∃ (past : List (RecordedQueueRun.RoundInput p.K))
      (cell : RecordedQueueRun.RoundInput p.K),
      Inputs q.val z = some past ∧
      ReferenceFirstCollectionOldRecorderFoundation.oldCell?
        rate rewards C_star C_h q z = some cell ∧
      deltaV rate rewards C_star C_h q z =
        RecordedWeightedDrift.weightedSquarePotential p.m Q
          (RecordedQueueRun.step Q (RecordedQueueRun.run Q past) cell) -
        RecordedWeightedDrift.weightedSquarePotential p.m Q
          (RecordedQueueRun.run Q past) := by
  obtain ⟨past, cell, hpast, hcell, hnext, _, _⟩ :=
    ReferenceOriginalCalendarCollectionRetainedEnergyStep.presentPrefix_append
      rate rewards C_star C_h q z hz.1.1
  refine ⟨past, cell, hpast, hcell, ?_⟩
  simp [deltaV, V, hpast, hnext,
    ReferenceFirstCollectionRenewalFutureNumericalPrefix.run_append_one]

/-- Actual LIVE prefix witnesses preserve the square observation after incoming overflow
(and under a disabled update); no condition is imposed on the outgoing flag. -/
public theorem live_disabled_or_overflow_preservation (q : Fin p.T) (z : X) :
    z ∈ ReferenceOriginalCalendarContinuingLiveRetainedEnergyStep.retainedSupport
      rate rewards C_star C_h q →
    ∃ past cell, Inputs q.val z = some past ∧
      ReferenceOriginalCalendarCarriedStoppedEnergy.actualCellAt
        rate rewards C_star C_h q z = some cell ∧
      (cell.enabled = false ∨ (RecordedQueueRun.run Q past).overflow = true →
        deltaV rate rewards C_star C_h q z = 0) := by
  intro hz
  obtain ⟨past, cell, hpast, hc, hnext, _, _⟩ :=
    ReferenceOriginalCalendarContinuingLiveRetainedEnergyStep.presentPrefix_append
      rate rewards C_star C_h q z hz
  refine ⟨past, cell, hpast, hc, ?_⟩
  intro hstop
  simp only [deltaV, V, hpast, hnext, Option.elim_some,
    ReferenceFirstCollectionRenewalFutureNumericalPrefix.run_append_one]
  exact sub_eq_zero.mpr (RecordedWeightedDrift.weightedSquarePotential_step_eq_of_disabled_or_overflowed
    p.m Q (RecordedQueueRun.run Q past) cell hstop)

/-- The same preservation holds on every present collection prefix, including disabled
cutoff cells. The inherited queues and full score weights are kept. -/
public theorem collection_disabled_or_overflow_preservation (q : Fin p.T) (z : X) :
    z ∈ ReferenceOriginalCalendarCollectionRetainedEnergyStep.B rate rewards C_star C_h q →
    ∃ past cell, Inputs q.val z = some past ∧
      ReferenceFirstCollectionOldRecorderFoundation.oldCell? rate rewards C_star C_h q z = some cell ∧
      (cell.enabled = false ∨ (RecordedQueueRun.run Q past).overflow = true →
        deltaV rate rewards C_star C_h q z = 0) := by
  intro hz
  obtain ⟨past, cell, hpast, hc, hnext, _, _⟩ :=
    ReferenceOriginalCalendarCollectionRetainedEnergyStep.presentPrefix_append rate rewards C_star C_h q z hz
  refine ⟨past, cell, hpast, hc, ?_⟩
  intro hstop
  simp only [deltaV, V, hpast, hnext, Option.elim_some,
    ReferenceFirstCollectionRenewalFutureNumericalPrefix.run_append_one]
  exact sub_eq_zero.mpr (RecordedWeightedDrift.weightedSquarePotential_step_eq_of_disabled_or_overflowed
    p.m Q (RecordedQueueRun.run Q past) cell hstop)

private theorem coordinate_step_le (past : List (RecordedQueueRun.RoundInput p.K))
    (cell : RecordedQueueRun.RoundInput p.K)
    (hpast : ∀ c ∈ past, ∀ i, 32 * (Q).eta ≤ c.rate i)
    (hrate : ∀ i, 32 * (Q).eta ≤ cell.rate i)
    (hen : cell.enabled = true) (hclear : (RecordedQueueRun.run Q past).overflow = false)
    (i : Fin p.K) :
    ProductSetLaw.theta p.m (RecordedQueueRun.scoreWeight Q
        (RecordedQueueRun.step Q (RecordedQueueRun.run Q past) cell)) i *
        StoppedQueueBound.normalizedBacklog Q
          (RecordedQueueRun.step Q (RecordedQueueRun.run Q past) cell) i ^ 2 -
      ProductSetLaw.theta p.m (RecordedQueueRun.scoreWeight Q (RecordedQueueRun.run Q past)) i *
        StoppedQueueBound.normalizedBacklog Q (RecordedQueueRun.run Q past) i ^ 2 ≤
      ProductSetLaw.theta p.m (RecordedQueueRun.scoreWeight Q (RecordedQueueRun.run Q past)) i *
        ((2 * StoppedQueueBound.normalizedBacklog Q (RecordedQueueRun.run Q past) i + 1 / 2) *
          RecordedRoundMoments.normalizedQuantizedArrival Q cell i +
          RecordedRoundMoments.normalizedQuantizedArrival Q cell i ^ 2 -
          (15 / 2 : ℝ) * StoppedQueueBound.normalizedBacklog Q (RecordedQueueRun.run Q past) i + 16) := by
  let state := RecordedQueueRun.run Q past
  let b := StoppedQueueBound.normalizedBacklog Q state i
  let r := RecordedRoundMoments.normalizedQuantizedArrival Q cell i
  let b' := StoppedQueueBound.normalizedBacklog Q (RecordedQueueRun.step Q state cell) i
  have hb : 0 ≤ b := by
    dsimp [b, StoppedQueueBound.normalizedBacklog]
    positivity
  have hr : 0 ≤ r := by
    dsimp [r, RecordedRoundMoments.normalizedQuantizedArrival]
    positivity
  have hrec : b' = QueueSquareDrift.queueNext b r := by
    dsimp [b', b, r]
    rw [RecordedWeightedDrift.normalizedBacklog_step_eq_queueNext Q state cell hen hclear i]
    rw [RecordedRoundMoments.rawEstimate_eq_normalizedQuantizedArrival_of_enabled
      Q state cell i hen hclear]
  have hnext := RecordedWeightedDrift.successor_normalizedBacklog_le Q past hpast cell hrate i
  have hsq := QueueSquareDrift.queueNext_sq_sub_le b r hb hr
  have hcap := QueueSquareDrift.queueNext_sq_le_cap_mul b r (1 / (32 * (Q).eta))
    hb hr (by positivity [(Q).eta_pos]) (by rwa [← hrec])
  rw [← hrec] at hsq hcap
  have hscaled := mul_le_mul_of_nonneg_left hcap (show 0 ≤ 8 * (Q).eta by positivity [(Q).eta_pos])
  have hcoef := RecordedWeightedDrift.sixteen_eta_mul_backlogCap Q
  have hscaled' : 8 * (Q).eta * b' ^ 2 ≤ (1 / 2 : ℝ) * (b + r) := by
    calc
      _ ≤ 8 * (Q).eta * (2 * (1 / (32 * (Q).eta)) * (b + r)) := hscaled
      _ = (16 * (Q).eta * (1 / (32 * (Q).eta))) * (b + r) := by ring
      _ = _ := by rw [hcoef]
  have hinner : b' ^ 2 - b ^ 2 + 8 * (Q).eta * b' ^ 2 ≤
      (2 * b + 1 / 2) * r + r ^ 2 - (15 / 2 : ℝ) * b + 16 := by
    nlinarith only [hsq, hscaled']
  have ht := (RecordedMarginalGrowth.state_theta_pos Q state i
    (Nat.zero_lt_of_lt p.two_le_m) p.m_lt_K).le
  have heta := RecordedWeightedDrift.eta_le_one_div_sixtyFour p Q rate.sourceCap
  have hg := RecordedMarginalGrowth.step_theta_growth Q state cell i p.two_le_m p.m_lt_K heta
  exact (QueueSquareDrift.weighted_square_step _ _ (Q).eta b' b ht (Q).eta_pos.le
    (hg.1.trans hg.2)).trans (mul_le_mul_of_nonneg_left hinner ht)

/-- The literal full-prefix normalized backlog, zero on actual absence. -/
public def backlogAt (n : ℕ) (i : Fin p.K) (z : X) : ℝ :=
  (Inputs n z).elim 0 (fun past =>
    StoppedQueueBound.normalizedBacklog Q (RecordedQueueRun.run Q past) i)

private theorem prefix_clear (q : Fin p.T) (z : X)
    (past : List (RecordedQueueRun.RoundInput p.K)) (hpast : Inputs q.val z = some past)
    (hH : z ∈ ReferenceFirstCollectionCurrentRetainedGate.H rate rewards C_star C_h q) :
    (RecordedQueueRun.run Q past).overflow = false := by
  obtain ⟨v, hv, hclear⟩ := hH
  have hP : P q.val z = some (stateReadout (RecordedQueueRun.run Q past)) := by
    simp only [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout,
      hpast, Option.map_some]
  have he := (ReferenceOriginalCalendarCollectionRetainedEnergyStep.P_eq_current
    rate rewards C_star C_h q z).trans hv
  change P q.val z = some v at he
  rw [hP] at he
  have heq := Option.some.inj he
  simpa only [← heq, stateReadout] using hclear

/-- Original LIVE pointwise transport of the retained square drift, before
conditional moments are applied. The outgoing overflow flag is unrestricted. -/
public theorem live_deltaV_le (q : Fin p.T) (z : X)
    (hz : z ∈ ReferenceOriginalCalendarContinuingLiveRetainedEnergyStep.liveRetainedGate
      rate rewards C_star C_h q) :
    deltaV rate rewards C_star C_h q z ≤ ∑ i : Fin p.K,
      thetaAt rate rewards C_star C_h q.val i z *
        ((2 * backlogAt rate rewards C_star C_h q.val i z + 1 / 2) *
          ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualArrival
            rate rewards C_star C_h q i z +
          ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualArrival
            rate rewards C_star C_h q i z ^ 2 -
          (15 / 2 : ℝ) * backlogAt rate rewards C_star C_h q.val i z + 16) := by
  obtain ⟨past, cell, hpast, hc, hnext, _, _⟩ :=
    ReferenceOriginalCalendarContinuingLiveRetainedEnergyStep.presentPrefix_append
      rate rewards C_star C_h q z hz.1
  obtain ⟨_, cell', _, _, _, _, hen, hc'⟩ :=
    ReferenceOriginalCalendarContinuingLiveRetainedEnergyStep.liveDomain_cell0
      rate rewards C_star C_h q z hz.1.1
  have heq : cell' = cell := Option.some.inj (hc'.symm.trans hc)
  subst cell'
  have hclear := prefix_clear rate rewards C_star C_h q z past hpast hz.2
  have hp := ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.prefixInputs_rate_bounds
    rate rewards C_star C_h q.val z past hpast
  have hall := ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.prefixInputs_rate_bounds
    rate rewards C_star C_h (q.val + 1) z (past ++ [cell]) hnext
  have hr : ∀ i, 32 * (Q).eta ≤ cell.rate i := fun i => hall cell (by simp) i
  simp only [deltaV, V, hpast, hnext, Option.elim_some,
    ReferenceFirstCollectionRenewalFutureNumericalPrefix.run_append_one,
    RecordedWeightedDrift.weightedSquarePotential, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro i _
  rw [ReferenceOriginalCalendarContinuingLiveRetainedEnergyStep.actualArrival_eq_cell
    rate rewards C_star C_h q i z hz.1.1 cell hc]
  simpa only [thetaAt, backlogAt, hpast, Option.elim_some] using
    coordinate_step_le rate past cell hp hr hen hclear i

/-- Original unrestricted collection pointwise transport. No old-selector or
before-first-call restriction is imposed, and the detecting update is included. -/
public theorem collection_deltaV_le (q : Fin p.T) (z : X)
    (hz : z ∈ ReferenceOriginalCalendarCollectionRetainedEnergyStep.G
      rate rewards C_star C_h q) :
    deltaV rate rewards C_star C_h q z ≤ ∑ i : Fin p.K,
      thetaAt rate rewards C_star C_h q.val i z *
        ((2 * backlogAt rate rewards C_star C_h q.val i z + 1 / 2) *
          ReferenceFirstCollectionOldRecorderFoundation.oldRaw rate rewards C_star C_h q i z +
          ReferenceFirstCollectionOldRecorderFoundation.oldRaw rate rewards C_star C_h q i z ^ 2 -
          (15 / 2 : ℝ) * backlogAt rate rewards C_star C_h q.val i z + 16) := by
  obtain ⟨past, cell, hpast, hc, hnext, _, _⟩ :=
    ReferenceOriginalCalendarCollectionRetainedEnergyStep.presentPrefix_append
      rate rewards C_star C_h q z hz.1.1
  have hc' : ReferenceFirstCollectionOldRecorderFoundation.oldCell?
      rate rewards C_star C_h q z = some cell := hc
  have he := ReferenceFirstCollectionOldRecorderFoundation.oldCell_enabled_eq_incoming
    rate rewards C_star C_h q z cell hc'
  have hen : cell.enabled = true := Option.some.inj (he.symm.trans hz.2.2)
  have hclear := prefix_clear rate rewards C_star C_h q z past hpast hz.1.2
  have hp := ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.prefixInputs_rate_bounds
    rate rewards C_star C_h q.val z past hpast
  have hall := ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.prefixInputs_rate_bounds
    rate rewards C_star C_h (q.val + 1) z (past ++ [cell]) hnext
  have hr : ∀ i, 32 * (Q).eta ≤ cell.rate i := fun i => hall cell (by simp) i
  simp only [deltaV, V, hpast, hnext, Option.elim_some,
    ReferenceFirstCollectionRenewalFutureNumericalPrefix.run_append_one,
    RecordedWeightedDrift.weightedSquarePotential, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro i _
  simpa only [thetaAt, backlogAt, hpast, Option.elim_some,
    ReferenceFirstCollectionOldRecorderFoundation.oldRaw, hc'] using
    coordinate_step_le rate past cell hp hr hen hclear i

/-- The old raw collection value factors through the actual incoming payload
on every present collection readout, without a before-call restriction. -/
private theorem collection_raw_amplitude_identity (q : Fin p.T) (a : Fin p.K)
    (z : X) (hz : z ∈ ReferenceOriginalCalendarCollectionRetainedEnergyStep.D
      rate rewards C_star C_h q) :
    ReferenceFirstCollectionOldRecorderFoundation.oldRaw
        rate rewards C_star C_h q a z =
      (if ReferenceFirstCollectionOldRecorderFoundation.oldMarker?
          rate rewards C_star C_h q z = some (some a) then 1 else 0) *
        (ReferenceFirstCollectionOldRecorderFoundation.incomingAmplitude?
          rate rewards C_star C_h q a z).getD 0 := by
  obtain ⟨_record, cell, payload, _, hcell, hpayload, hrate, _⟩ :=
    ReferenceOriginalCalendarCollectionRetainedEnergyStep.presentCell_recordingMap
      rate rewards C_star C_h q z hz
  change ReferenceFirstCollectionOldRecorderFoundation.oldCell?
    rate rewards C_star C_h q z = some cell at hcell
  have hreward := ReferenceFirstCollectionOldRecorderFoundation.oldCell_reward
    rate rewards C_star C_h q z cell hcell
  by_cases ha : cell.recordedArm = some a
  · simp only [ReferenceFirstCollectionOldRecorderFoundation.oldRaw, hcell]
    rw [RecordedRoundMoments.normalizedQuantizedArrival_eq_quantizedValue_of_recorded
      _ cell a ha]
    simp only [ReferenceFirstCollectionOldRecorderFoundation.oldMarker?, hcell,
      Option.map_some, ha, ↓reduceIte,
      ReferenceFirstCollectionOldRecorderFoundation.incomingAmplitude?, hpayload,
      Option.getD_some, one_mul, hrate, hreward]
    rfl
  · simp only [ReferenceFirstCollectionOldRecorderFoundation.oldRaw, hcell,
      RecordedRoundMoments.normalizedQuantizedArrival,
      RecordedQueueRun.quantizedArrival, ha, ite_false, Nat.cast_zero, zero_div]
    simp only [ReferenceFirstCollectionOldRecorderFoundation.oldMarker?, hcell,
      Option.map_some, Option.some.injEq, ha, ite_false, zero_mul]

private theorem live_arrival_sq_factor (q : Fin p.T) (a : Fin p.K) :
    (ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualArrival
      rate rewards C_star C_h q a) ^ 2 =
      (fun z => ((ReferenceFirstCollectionOldRecorderFoundation.incomingAmplitude?
        rate rewards C_star C_h q a z).getD 0) ^ 2) *
        ReferenceOriginalCalendarContinuingLiveRecorderLaw.markerTest
          rate rewards C_star C_h q (some (some a)) := by
  rw [ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualArrival_factor]
  funext z
  have htest :
      ReferenceOriginalCalendarContinuingLiveRecorderLaw.markerTest
        rate rewards C_star C_h q (some (some a)) z = 0 ∨
      ReferenceOriginalCalendarContinuingLiveRecorderLaw.markerTest
        rate rewards C_star C_h q (some (some a)) z = 1 := by
    by_cases hz : z ∈ ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualDomain
        rate rewards C_star C_h q
    · by_cases hm : ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualMarker
          rate rewards C_star C_h q z = some (some a) <;>
        simp [ReferenceOriginalCalendarContinuingLiveRecorderLaw.markerTest, hz, hm]
    · simp [ReferenceOriginalCalendarContinuingLiveRecorderLaw.markerTest, hz]
  rcases htest with htest | htest <;> simp [htest, pow_two]

/-- Exact LIVE square pull-out under the original source law. The marker test
uses the actual present arm atom; outer absence and present bottom remain
distinct in the underlying marker law. -/
public theorem live_arrival_square_condExp (control0 : TimeControl p)
    (q : Fin p.T) (a : Fin p.K) :
    mu[(ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualArrival
        rate rewards C_star C_h q a) ^ 2 |
      sourcePrefixFiltration control0 (q.val + 1)] =ᵐ[mu]
      (fun z => ((ReferenceFirstCollectionOldRecorderFoundation.incomingAmplitude?
        rate rewards C_star C_h q a z).getD 0) ^ 2) *
        ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualRate
          rate rewards C_star C_h q a := by
  let amp := fun z : X =>
    (ReferenceFirstCollectionOldRecorderFoundation.incomingAmplitude?
      rate rewards C_star C_h q a z).getD 0
  let marker := ReferenceOriginalCalendarContinuingLiveRecorderLaw.markerTest
    rate rewards C_star C_h q (some (some a))
  have hamp : Measurable[sourcePrefixFiltration control0 (q.val + 1)] amp :=
    ReferenceFirstCollectionOldRecorderFoundation.incomingAmplitudeValue_measurable
      rate rewards C_star C_h control0 q a
  have hmarkerI := ReferenceOriginalCalendarContinuingLiveRecorderLaw.markerTest_integrable
    rate rewards C_star C_h q (some (some a))
  have hArrivalI := ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualArrival_integrable
    rate rewards C_star C_h control0 q a
  have hbeta := CanonicalRecordingRates.beta_pos p rate.eta.property
  have hsqI : Integrable
      ((ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualArrival
        rate rewards C_star C_h q a) ^ 2) mu := by
    have hbound : ∀ᵐ z ∂mu, ‖ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualArrival
        rate rewards C_star C_h q a z‖ ≤ 1 / CanonicalRecordingRates.beta p rate.eta.val := by
      filter_upwards [] with z
      rcases ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualArrival_bounds
        rate rewards C_star C_h q a z with ⟨hlo, hhi⟩
      rw [Real.norm_eq_abs, abs_of_nonneg hlo]
      exact hhi
    convert hArrivalI.mul_bdd hArrivalI.aestronglyMeasurable hbound using 1
    funext z
    simp only [pow_two, Pi.mul_apply]
  have hprod :
      (ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualArrival
        rate rewards C_star C_h q a) ^ 2 = (fun z => amp z ^ 2) * marker := by
    simpa only [amp, marker] using live_arrival_sq_factor rate rewards C_star C_h q a
  have hprodI : Integrable ((fun z => amp z ^ 2) * marker) mu :=
    hsqI.congr (Filter.Eventually.of_forall (fun z => congrFun hprod z))
  have hce := condExp_mul_of_stronglyMeasurable_left
    (hamp.pow_const 2).stronglyMeasurable hprodI hmarkerI
  rw [hprod]
  have hmarkerCE :=
    ReferenceOriginalCalendarContinuingLiveRecorderLaw.marker_arm_condExp
      rate rewards C_star C_h control0 q a
  filter_upwards [hce, hmarkerCE] with z hce hm
  calc
    mu[((fun x => amp x ^ 2) * marker) |
        sourcePrefixFiltration control0 (q.val + 1)] z =
        amp z ^ 2 * mu[marker | sourcePrefixFiltration control0 (q.val + 1)] z := by
          exact hce
    _ = amp z ^ 2 * ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualRate
        rate rewards C_star C_h q a z := by rw [hm]

private theorem live_amplitude_square_rate_le (q : Fin p.T) (a : Fin p.K)
    (z : X) (hz : z ∈ ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualDomain
      rate rewards C_star C_h q) :
    ((ReferenceFirstCollectionOldRecorderFoundation.incomingAmplitude?
      rate rewards C_star C_h q a z).getD 0) ^ 2 *
        ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualRate
          rate rewards C_star C_h q a z ≤
      1 / ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualRate
        rate rewards C_star C_h q a z := by
  obtain ⟨record, regs, owned, base, cell, selected, hrecord, hcoord, _hread,
    hcell, _henabled, hselected, hrate, _hreward, _hfloor⟩ :=
    ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualCell_data
      rate rewards C_star C_h q z hz
  have hpayload :=
    ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualSelection_incomingPayload
      rate rewards C_star C_h q z record hrecord ⟨regs, owned, base, hcoord⟩
      selected hselected
  have hxi : ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualRate
      rate rewards C_star C_h q a z = selected.view.payload.rate a := by
    simp [ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualRate,
      ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualParameters, hz, hcell, hrate]
  have hamp : (ReferenceFirstCollectionOldRecorderFoundation.incomingAmplitude?
      rate rewards C_star C_h q a z).getD 0 =
      QuantizedRecordingMoments.quantizedValue (D p) rate.eta.val
        (selected.view.payload.rate a)
        (ReferenceFirstCollectionOldRecorderFoundation.roundedReward rewards q a) := by
    simp [ReferenceFirstCollectionOldRecorderFoundation.incomingAmplitude?, hpayload]
  have hxiPos : 0 < selected.view.payload.rate a :=
    (CanonicalRecordingRates.beta_pos p rate.eta.property).trans_le
      (selected.view.payload.beta_le_rate a)
  have hrw := ReferenceFirstCollectionOldRecorderFoundation.roundedReward_bounds
    rewards q a
  have hsecond := QuantizedRecordingMoments.quantizedValue_secondMoment_le
    (D p) rate.eta.val (selected.view.payload.rate a)
    (ReferenceFirstCollectionOldRecorderFoundation.roundedReward rewards q a)
    (D_pos p) rate.eta.property hxiPos hrw
  calc
    _ = selected.view.payload.rate a *
        (QuantizedRecordingMoments.quantizedValue (D p) rate.eta.val
          (selected.view.payload.rate a)
          (ReferenceFirstCollectionOldRecorderFoundation.roundedReward rewards q a)) ^ 2 := by
          rw [hamp, hxi]
          ring
    _ ≤ (ReferenceFirstCollectionOldRecorderFoundation.roundedReward rewards q a) ^ 2 /
        selected.view.payload.rate a := hsecond
    _ ≤ 1 / selected.view.payload.rate a :=
          div_le_div_of_nonneg_right (by nlinarith [hrw.2]) hxiPos.le
    _ = _ := by rw [hxi]

/-- The actual LIVE coordinate square moment is bounded by the reciprocal of
the same original payload rate. -/
public theorem live_arrival_square_condExp_bound_on_domain
    (control0 : TimeControl p) (q : Fin p.T) (a : Fin p.K) :
    ∀ᵐ z ∂mu,
      z ∈ ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualDomain
        rate rewards C_star C_h q →
      mu[(ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualArrival
          rate rewards C_star C_h q a) ^ 2 |
        sourcePrefixFiltration control0 (q.val + 1)] z ≤
        1 / ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualRate
          rate rewards C_star C_h q a z := by
  filter_upwards [live_arrival_square_condExp rate rewards C_star C_h control0 q a] with z hce
  intro hz
  have hbound := live_amplitude_square_rate_le rate rewards C_star C_h q a z hz
  simpa only [Pi.mul_apply] using hce.trans_le hbound

/-- The original unrestricted collection arm test, still gated by ANY present
collection readout, factors the physical raw value through its incoming floor. -/
public theorem collection_oldRaw_condExp_factor (control0 : TimeControl p)
    (q : Fin p.T) (a : Fin p.K) :
    mu[ReferenceFirstCollectionOldRecorderFoundation.oldRaw
        rate rewards C_star C_h q a |
      sourcePrefixFiltration control0 (q.val + 1)] =ᵐ[mu]
      (fun z => (ReferenceFirstCollectionOldRecorderFoundation.incomingAmplitude?
        rate rewards C_star C_h q a z).getD 0) *
        mu[(ReferenceOriginalCalendarCollectionRetainedEnergyStep.D
          rate rewards C_star C_h q).indicator (fun z =>
            if ReferenceFirstCollectionOldRecorderFoundation.oldMarker?
                rate rewards C_star C_h q z = some (some a) then (1 : ℝ) else 0) |
          sourcePrefixFiltration control0 (q.val + 1)] := by
  let domain := ReferenceOriginalCalendarCollectionRetainedEnergyStep.D
    rate rewards C_star C_h q
  let amp := fun z : X =>
    (ReferenceFirstCollectionOldRecorderFoundation.incomingAmplitude?
      rate rewards C_star C_h q a z).getD 0
  let marker := fun z : X =>
    if ReferenceFirstCollectionOldRecorderFoundation.oldMarker?
        rate rewards C_star C_h q z = some (some a) then (1 : ℝ) else 0
  let test := domain.indicator marker
  have hdomainF := ReferenceOriginalCalendarCollectionRetainedEnergyStep.measurableSet_D
    rate rewards C_star C_h control0 q
  have hdomain := (sourcePrefixFiltration control0).le' (q.val + 1) _ hdomainF
  have htarget : MeasurableSet
      ({some (some a)} : Set (Option (Option (Fin p.K)))) :=
    MeasurableSet.singleton (some (some a))
  have hmarkerMeas : Measurable marker := by
    dsimp [marker]
    exact Measurable.ite
      (htarget.preimage (ReferenceFirstCollectionOldRecorderFoundation.oldMarker_measurable
        rate rewards C_star C_h q)) measurable_const measurable_const
  have htestMeas : Measurable test := hmarkerMeas.indicator hdomain
  have htest_range (z : X) : test z = 0 ∨ test z = 1 := by
    by_cases hz : z ∈ domain
    · by_cases hm : ReferenceFirstCollectionOldRecorderFoundation.oldMarker?
          rate rewards C_star C_h q z = some (some a)
      · simp [test, marker, Set.indicator_of_mem hz, hm]
      · simp [test, marker, Set.indicator_of_mem hz, hm]
    · simp [test, marker, Set.indicator_of_notMem hz]
  have htestI : Integrable test mu := by
    apply integrable_of_uniform_bound htestMeas.aestronglyMeasurable 1
    intro z
    rcases htest_range z with hzero | hone
    · simp [hzero]
    · simp [hone]
  have hamp := ReferenceFirstCollectionOldRecorderFoundation.incomingAmplitudeValue_measurable
    rate rewards C_star C_h control0 q a
  have hrawI := ReferenceFirstCollectionOldRecorderFoundation.oldRaw_integrable
    rate rewards C_star C_h q a
  have hfactor :
      ReferenceFirstCollectionOldRecorderFoundation.oldRaw rate rewards C_star C_h q a =
        amp * test := by
    funext z
    by_cases hz : z ∈ domain
    · rw [collection_raw_amplitude_identity rate rewards C_star C_h q a z hz]
      simp [amp, marker, test, Set.indicator_of_mem hz]
    · have hnone : ReferenceFirstCollectionOldRecorderFoundation.oldCell?
          rate rewards C_star C_h q z = none := by
        cases hc : ReferenceFirstCollectionOldRecorderFoundation.oldCell?
            rate rewards C_star C_h q z with
        | none => rfl
        | some cell =>
            have hD : z ∈ ReferenceOriginalCalendarCollectionRetainedEnergyStep.D
                rate rewards C_star C_h q := by
              change (ReferenceOriginalCalendarCollectionRetainedEnergyStep.C
                rate rewards C_star C_h q z).isSome = true
              simp [ReferenceOriginalCalendarCollectionRetainedEnergyStep.C, hc]
            exact False.elim (hz hD)
      simp [ReferenceFirstCollectionOldRecorderFoundation.oldRaw, hnone, test, hz]
  have hprodI : Integrable (amp * test) mu := by
    exact hrawI.congr (Filter.Eventually.of_forall (fun z => congrFun hfactor z))
  have hce := condExp_mul_of_stronglyMeasurable_left
    hamp.stronglyMeasurable hprodI htestI
  rw [hfactor]
  simpa only [amp, test, domain] using hce

/-- The same unrestricted collection source transport for the square of the
raw value; the inner marker law is not narrowed to `oldSelector`. -/
public theorem collection_oldRaw_square_condExp_factor (control0 : TimeControl p)
    (q : Fin p.T) (a : Fin p.K) :
    mu[(ReferenceFirstCollectionOldRecorderFoundation.oldRaw
        rate rewards C_star C_h q a) ^ 2 |
      sourcePrefixFiltration control0 (q.val + 1)] =ᵐ[mu]
      (fun z => (ReferenceFirstCollectionOldRecorderFoundation.incomingAmplitude?
        rate rewards C_star C_h q a z).getD 0 ^ 2) *
        mu[(ReferenceOriginalCalendarCollectionRetainedEnergyStep.D
          rate rewards C_star C_h q).indicator (fun z =>
            if ReferenceFirstCollectionOldRecorderFoundation.oldMarker?
                rate rewards C_star C_h q z = some (some a) then (1 : ℝ) else 0) |
          sourcePrefixFiltration control0 (q.val + 1)] := by
  let amp := fun z : X =>
    (ReferenceFirstCollectionOldRecorderFoundation.incomingAmplitude?
      rate rewards C_star C_h q a z).getD 0
  let domain := ReferenceOriginalCalendarCollectionRetainedEnergyStep.D
    rate rewards C_star C_h q
  let marker := fun z : X =>
    if ReferenceFirstCollectionOldRecorderFoundation.oldMarker?
        rate rewards C_star C_h q z = some (some a) then (1 : ℝ) else 0
  let test := domain.indicator marker
  have hmeas : Measurable[sourcePrefixFiltration control0 (q.val + 1)] amp :=
    ReferenceFirstCollectionOldRecorderFoundation.incomingAmplitudeValue_measurable
      rate rewards C_star C_h control0 q a
  have hdomainF := ReferenceOriginalCalendarCollectionRetainedEnergyStep.measurableSet_D
    rate rewards C_star C_h control0 q
  have hdomain := (sourcePrefixFiltration control0).le' (q.val + 1) _ hdomainF
  have htarget : MeasurableSet
      ({some (some a)} : Set (Option (Option (Fin p.K)))) :=
    MeasurableSet.singleton (some (some a))
  have hmarkerMeas : Measurable marker := by
    dsimp [marker]
    exact Measurable.ite
      (htarget.preimage (ReferenceFirstCollectionOldRecorderFoundation.oldMarker_measurable
        rate rewards C_star C_h q)) measurable_const measurable_const
  have htestMeas : Measurable test := hmarkerMeas.indicator hdomain
  have htest_range (z : X) : test z = 0 ∨ test z = 1 := by
    by_cases hz : z ∈ domain
    · by_cases hm : ReferenceFirstCollectionOldRecorderFoundation.oldMarker?
          rate rewards C_star C_h q z = some (some a)
      · simp [test, marker, Set.indicator_of_mem hz, hm]
      · simp [test, marker, Set.indicator_of_mem hz, hm]
    · simp [test, marker, Set.indicator_of_notMem hz]
  have htestI : Integrable test mu := by
    apply integrable_of_uniform_bound htestMeas.aestronglyMeasurable 1
    intro z
    rcases htest_range z with hzero | hone
    · simp [hzero]
    · simp [hone]
  have hrawI := ReferenceFirstCollectionOldRecorderFoundation.oldRaw_integrable
    rate rewards C_star C_h q a
  have hbeta := CanonicalRecordingRates.beta_pos p rate.eta.property
  have hrawSqI : Integrable
      ((ReferenceFirstCollectionOldRecorderFoundation.oldRaw rate rewards C_star C_h q a) ^ 2) mu := by
    have hbound : ∀ᵐ z ∂mu, ‖ReferenceFirstCollectionOldRecorderFoundation.oldRaw
        rate rewards C_star C_h q a z‖ ≤ 1 / CanonicalRecordingRates.beta p rate.eta.val := by
      filter_upwards [] with z
      rcases ReferenceFirstCollectionOldRecorderFoundation.oldRaw_bounds
        rate rewards C_star C_h q a z with ⟨hlo, hhi⟩
      rw [Real.norm_eq_abs, abs_of_nonneg hlo]
      exact hhi
    convert hrawI.mul_bdd hrawI.aestronglyMeasurable hbound using 1
    funext z
    simp only [pow_two, Pi.mul_apply]
  have hfactor :
      (ReferenceFirstCollectionOldRecorderFoundation.oldRaw rate rewards C_star C_h q a) ^ 2 =
        (fun z => amp z ^ 2) * test := by
    funext z
    change ReferenceFirstCollectionOldRecorderFoundation.oldRaw
        rate rewards C_star C_h q a z ^ 2 = _
    by_cases hz : z ∈ domain
    · rw [collection_raw_amplitude_identity rate rewards C_star C_h q a z hz]
      by_cases hm : ReferenceFirstCollectionOldRecorderFoundation.oldMarker?
          rate rewards C_star C_h q z = some (some a)
      · simp [test, marker, amp, domain, Set.indicator_of_mem hz, hm, pow_two]
      · simp [test, marker, amp, domain, Set.indicator_of_mem hz, hm, pow_two]
    · have hnone : ReferenceFirstCollectionOldRecorderFoundation.oldCell?
          rate rewards C_star C_h q z = none := by
        cases hc : ReferenceFirstCollectionOldRecorderFoundation.oldCell?
            rate rewards C_star C_h q z with
        | none => rfl
        | some cell =>
            have hD : z ∈ ReferenceOriginalCalendarCollectionRetainedEnergyStep.D
                rate rewards C_star C_h q := by
              change (ReferenceOriginalCalendarCollectionRetainedEnergyStep.C
                rate rewards C_star C_h q z).isSome = true
              simp [ReferenceOriginalCalendarCollectionRetainedEnergyStep.C, hc]
            exact False.elim (hz hD)
      simp [ReferenceFirstCollectionOldRecorderFoundation.oldRaw, hnone, test, hz]
  have hprodI : Integrable ((fun z => amp z ^ 2) * test) mu :=
    hrawSqI.congr (Filter.Eventually.of_forall (fun z => congrFun hfactor z))
  have hce := condExp_mul_of_stronglyMeasurable_left
    (hmeas.pow_const 2).stronglyMeasurable hprodI htestI
  rw [hfactor]
  simpa only [amp, test, domain] using hce

private theorem collection_amplitude_square_rate_le (q : Fin p.T) (a : Fin p.K)
    (z : X) (hz : z ∈ ReferenceOriginalCalendarCollectionRetainedEnergyStep.D
      rate rewards C_star C_h q) :
    ((ReferenceFirstCollectionOldRecorderFoundation.incomingAmplitude?
      rate rewards C_star C_h q a z).getD 0) ^ 2 *
        ((ReferenceFirstCollectionOldRecorderFoundation.incomingRates?
          rate rewards C_star C_h q z).getD (fun _ => 0) a) ≤
      1 / ((ReferenceFirstCollectionOldRecorderFoundation.incomingRates?
        rate rewards C_star C_h q z).getD (fun _ => 0) a) := by
  obtain ⟨_record, cell, payload, _hrecord, _hcell, hpayload, hrate, _hmarker⟩ :=
    ReferenceOriginalCalendarCollectionRetainedEnergyStep.presentCell_recordingMap
      rate rewards C_star C_h q z hz
  have hxi : (ReferenceFirstCollectionOldRecorderFoundation.incomingRates?
      rate rewards C_star C_h q z).getD (fun _ => 0) a = payload.rate a := by
    simp [ReferenceFirstCollectionOldRecorderFoundation.incomingRates?, hpayload]
  have hamp : (ReferenceFirstCollectionOldRecorderFoundation.incomingAmplitude?
      rate rewards C_star C_h q a z).getD 0 =
      QuantizedRecordingMoments.quantizedValue (D p) rate.eta.val
        (payload.rate a)
        (ReferenceFirstCollectionOldRecorderFoundation.roundedReward rewards q a) := by
    simp [ReferenceFirstCollectionOldRecorderFoundation.incomingAmplitude?, hpayload]
  have hxiPos : 0 < payload.rate a :=
    (CanonicalRecordingRates.beta_pos p rate.eta.property).trans_le
      (payload.beta_le_rate a)
  have hrw := ReferenceFirstCollectionOldRecorderFoundation.roundedReward_bounds
    rewards q a
  have hsecond := QuantizedRecordingMoments.quantizedValue_secondMoment_le
    (D p) rate.eta.val (payload.rate a)
    (ReferenceFirstCollectionOldRecorderFoundation.roundedReward rewards q a)
    (D_pos p) rate.eta.property hxiPos hrw
  calc
    _ = payload.rate a * (QuantizedRecordingMoments.quantizedValue (D p) rate.eta.val
        (payload.rate a)
        (ReferenceFirstCollectionOldRecorderFoundation.roundedReward rewards q a)) ^ 2 := by
          rw [hamp, hxi]
          ring
    _ ≤ (ReferenceFirstCollectionOldRecorderFoundation.roundedReward rewards q a) ^ 2 /
        payload.rate a := hsecond
    _ ≤ 1 / payload.rate a :=
          div_le_div_of_nonneg_right (by nlinarith [hrw.2]) hxiPos.le
    _ = _ := by rw [hxi]

private theorem collection_amplitude_first_rate_le (q : Fin p.T) (a : Fin p.K)
    (z : X) (hz : z ∈ ReferenceOriginalCalendarCollectionRetainedEnergyStep.D
      rate rewards C_star C_h q) :
    ((ReferenceFirstCollectionOldRecorderFoundation.incomingRates?
      rate rewards C_star C_h q z).getD (fun _ => 0) a) *
        (ReferenceFirstCollectionOldRecorderFoundation.incomingAmplitude?
          rate rewards C_star C_h q a z).getD 0 ≤ 1 := by
  obtain ⟨_record, _cell, payload, _hrecord, _hcell, hpayload, _hrate, _hmarker⟩ :=
    ReferenceOriginalCalendarCollectionRetainedEnergyStep.presentCell_recordingMap
      rate rewards C_star C_h q z hz
  have hxi : (ReferenceFirstCollectionOldRecorderFoundation.incomingRates?
      rate rewards C_star C_h q z).getD (fun _ => 0) a = payload.rate a := by
    simp [ReferenceFirstCollectionOldRecorderFoundation.incomingRates?, hpayload]
  have hamp : (ReferenceFirstCollectionOldRecorderFoundation.incomingAmplitude?
      rate rewards C_star C_h q a z).getD 0 =
      QuantizedRecordingMoments.quantizedValue (D p) rate.eta.val
        (payload.rate a)
        (ReferenceFirstCollectionOldRecorderFoundation.roundedReward rewards q a) := by
    simp [ReferenceFirstCollectionOldRecorderFoundation.incomingAmplitude?, hpayload]
  have hxiPos : 0 < payload.rate a :=
    (CanonicalRecordingRates.beta_pos p rate.eta.property).trans_le
      (payload.beta_le_rate a)
  have hrw := ReferenceFirstCollectionOldRecorderFoundation.roundedReward_bounds rewards q a
  calc
    _ = payload.rate a *
        QuantizedRecordingMoments.quantizedValue (D p) rate.eta.val
          (payload.rate a)
          (ReferenceFirstCollectionOldRecorderFoundation.roundedReward rewards q a) := by
          rw [hxi, hamp]
    _ ≤ ReferenceFirstCollectionOldRecorderFoundation.roundedReward rewards q a :=
          QuantizedRecordingMoments.quantizedValue_firstMoment_le (D p) rate.eta.val
            (payload.rate a)
            (ReferenceFirstCollectionOldRecorderFoundation.roundedReward rewards q a)
            (D_pos p) rate.eta.property hxiPos hrw
    _ ≤ 1 := hrw.2

/-- The original unrestricted collection first moment is bounded on the
retained collection gate using the same incoming payload and marker law. -/
public theorem collection_oldRaw_condExp_upper_on_G
    (control0 : TimeControl p) (q : Fin p.T) (a : Fin p.K) :
    ∀ᵐ z ∂mu,
      z ∈ ReferenceOriginalCalendarCollectionRetainedEnergyStep.G
        rate rewards C_star C_h q →
      mu[ReferenceFirstCollectionOldRecorderFoundation.oldRaw
          rate rewards C_star C_h q a |
        sourcePrefixFiltration control0 (q.val + 1)] z ≤ 1 := by
  have hrawCE := collection_oldRaw_condExp_factor rate rewards C_star C_h control0 q a
  have hmarkerCE :=
    ReferenceOriginalCalendarCollectionRetainedEnergyStep.presentCell_marker_condExp
      rate rewards C_star C_h control0 q (some a)
  filter_upwards [hrawCE, hmarkerCE] with z hraw hmarker
  intro hG
  have hB : z ∈ ReferenceOriginalCalendarCollectionRetainedEnergyStep.B
      rate rewards C_star C_h q := hG.1.1
  have hD : z ∈ ReferenceOriginalCalendarCollectionRetainedEnergyStep.D
      rate rewards C_star C_h q := hB.1
  have hE : z ∈ ReferenceOriginalCalendarCollectionRetainedEnergyStep.E
      rate rewards C_star C_h q := hG.2
  have hEnabled := hE.2
  change ReferenceFirstCollectionOldRecorderFoundation.incomingEnabled?
    rate rewards C_star C_h q z = some true at hEnabled
  have hcoeff : (sourceInputLaw p)[
      (ReferenceOriginalCalendarCollectionRetainedEnergyStep.D rate rewards C_star C_h q).indicator
        (fun x => if ReferenceFirstCollectionOldRecorderFoundation.oldMarker?
            rate rewards C_star C_h q x = some (some a) then (1 : ℝ) else 0) |
        sourcePrefixFiltration control0 (q.val + 1)] z =
      (ReferenceFirstCollectionOldRecorderFoundation.incomingRates?
        rate rewards C_star C_h q z).getD (fun _ => 0) a := by
    rw [hmarker, Set.indicator_of_mem hD]
    simp [hEnabled]
  have hmoment := collection_amplitude_first_rate_le rate rewards C_star C_h q a z hD
  calc
    _ = ((ReferenceFirstCollectionOldRecorderFoundation.incomingAmplitude?
          rate rewards C_star C_h q a z).getD 0) *
        ((sourceInputLaw p)[
          (ReferenceOriginalCalendarCollectionRetainedEnergyStep.D rate rewards C_star C_h q).indicator
            (fun x => if ReferenceFirstCollectionOldRecorderFoundation.oldMarker?
                rate rewards C_star C_h q x = some (some a) then (1 : ℝ) else 0) |
            sourcePrefixFiltration control0 (q.val + 1)] z) := by
          simpa only [Pi.mul_apply] using hraw
    _ = ((ReferenceFirstCollectionOldRecorderFoundation.incomingAmplitude?
          rate rewards C_star C_h q a z).getD 0) *
        ((ReferenceFirstCollectionOldRecorderFoundation.incomingRates?
          rate rewards C_star C_h q z).getD (fun _ => 0) a) := by rw [hcoeff]
    _ ≤ 1 := by
          have h := hmoment
          rw [mul_comm] at h
          exact h

/-- Unrestricted collection square transport, restricted only by the actual
retained collection gate. Its reciprocal is the incoming payload rate. -/
public theorem collection_oldRaw_square_condExp_bound_on_G
    (control0 : TimeControl p) (q : Fin p.T) (a : Fin p.K) :
    ∀ᵐ z ∂mu,
      z ∈ ReferenceOriginalCalendarCollectionRetainedEnergyStep.G
        rate rewards C_star C_h q →
      mu[(ReferenceFirstCollectionOldRecorderFoundation.oldRaw
          rate rewards C_star C_h q a) ^ 2 |
        sourcePrefixFiltration control0 (q.val + 1)] z ≤
        1 / ((ReferenceFirstCollectionOldRecorderFoundation.incomingRates?
          rate rewards C_star C_h q z).getD (fun _ => 0) a) := by
  have hrawCE := collection_oldRaw_square_condExp_factor
    rate rewards C_star C_h control0 q a
  have hmarkerCE :=
    ReferenceOriginalCalendarCollectionRetainedEnergyStep.presentCell_marker_condExp
      rate rewards C_star C_h control0 q (some a)
  filter_upwards [hrawCE, hmarkerCE] with z hraw hmarker
  intro hG
  have hB : z ∈ ReferenceOriginalCalendarCollectionRetainedEnergyStep.B
      rate rewards C_star C_h q := hG.1.1
  have hD : z ∈ ReferenceOriginalCalendarCollectionRetainedEnergyStep.D
      rate rewards C_star C_h q := hB.1
  have hE : z ∈ ReferenceOriginalCalendarCollectionRetainedEnergyStep.E
      rate rewards C_star C_h q := hG.2
  have hEnabled := hE.2
  change ReferenceFirstCollectionOldRecorderFoundation.incomingEnabled?
    rate rewards C_star C_h q z = some true at hEnabled
  have hcoeff : (sourceInputLaw p)[
      (ReferenceOriginalCalendarCollectionRetainedEnergyStep.D rate rewards C_star C_h q).indicator
        (fun x => if ReferenceFirstCollectionOldRecorderFoundation.oldMarker?
            rate rewards C_star C_h q x = some (some a) then (1 : ℝ) else 0) |
        sourcePrefixFiltration control0 (q.val + 1)] z =
      (ReferenceFirstCollectionOldRecorderFoundation.incomingRates?
        rate rewards C_star C_h q z).getD (fun _ => 0) a := by
    rw [hmarker, Set.indicator_of_mem hD]
    simp [hEnabled]
  have hmoment := collection_amplitude_square_rate_le rate rewards C_star C_h q a z hD
  calc
    _ = ((ReferenceFirstCollectionOldRecorderFoundation.incomingAmplitude?
          rate rewards C_star C_h q a z).getD 0) ^ 2 *
        ((ReferenceFirstCollectionOldRecorderFoundation.incomingRates?
          rate rewards C_star C_h q z).getD (fun _ => 0) a) := by
          calc
            _ = ((ReferenceFirstCollectionOldRecorderFoundation.incomingAmplitude?
                  rate rewards C_star C_h q a z).getD 0) ^ 2 *
                (sourceInputLaw p)[
                  (ReferenceOriginalCalendarCollectionRetainedEnergyStep.D
                    rate rewards C_star C_h q).indicator (fun x =>
                      if ReferenceFirstCollectionOldRecorderFoundation.oldMarker?
                          rate rewards C_star C_h q x = some (some a) then (1 : ℝ) else 0) |
                  sourcePrefixFiltration control0 (q.val + 1)] z := by
                    simpa only [Pi.mul_apply] using hraw
            _ = _ := by rw [hcoeff]
    _ ≤ _ := hmoment

private theorem backlogAt_bounds (n : ℕ) (i : Fin p.K) (z : X) :
    0 ≤ backlogAt rate rewards C_star C_h n i z ∧
      backlogAt rate rewards C_star C_h n i z ≤ 2 * (1 / (32 * rate.eta.val)) := by
  cases hpast : Inputs n z with
  | none => simp only [backlogAt, hpast, Option.elim_none]; exact ⟨le_rfl, mul_nonneg (by norm_num) (one_div_nonneg.mpr (mul_nonneg (by norm_num) rate.eta.property.le))⟩
  | some past =>
    have hP : P n z = some (stateReadout (RecordedQueueRun.run Q past)) := by
      simp only [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout,
        hpast, Option.map_some]
    simpa only [backlogAt, hpast, Option.elim_some, StoppedQueueBound.normalizedBacklog,
      stateReadout] using
      ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.prefixReadout_backlog_bounds
        rate rewards C_star C_h n z _ hP i

private theorem backlogAt_measurable (control0 : TimeControl p) (q : Fin p.T) (i : Fin p.K) :
    Measurable[sourcePrefixFiltration control0 (q.val + 1)]
      (backlogAt rate rewards C_star C_h q.val i) :=
  observation_measurable rate rewards C_star C_h q.val
    (ReferenceOriginalCalendarContinuingLiveRetainedEnergyStep.P_measurable
      rate rewards C_star C_h control0 q)
    (fun state => StoppedQueueBound.normalizedBacklog Q state i)
    (by unfold StoppedQueueBound.normalizedBacklog stateFromReadout; fun_prop)

private theorem theta_memLp (n : ℕ) (i : Fin p.K) :
    MemLp (thetaAt rate rewards C_star C_h n i) ⊤ mu := by
  apply memLp_top_of_bound (observation_measurable rate rewards C_star C_h n
    ((ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.measurable_prefixReadout
      rate rewards C_star C_h n).mono le_rfl le_top)
    (fun state => ProductSetLaw.theta p.m (RecordedQueueRun.scoreWeight Q state) i)
    (by
      unfold RecordedQueueRun.scoreWeight stateFromReadout ProductSetLaw.theta
        FiniteNormalization.mass FiniteNormalization.normalizedWeight
        FiniteNormalization.totalMass ProductSetLaw.setWeight ProductSetLaw.support
        ScoreWeights.scoreWeight
      fun_prop)).aestronglyMeasurable 1
  filter_upwards [] with z
  change ‖thetaAt rate rewards C_star C_h n i z‖ ≤ 1
  rw [Real.norm_eq_abs, abs_of_nonneg (thetaAt_bounds rate rewards C_star C_h n i z).1]
  exact (thetaAt_bounds rate rewards C_star C_h n i z).2

private theorem backlog_memLp (n : ℕ) (i : Fin p.K) :
    MemLp (backlogAt rate rewards C_star C_h n i) ⊤ mu := by
  apply memLp_top_of_bound (observation_measurable rate rewards C_star C_h n
    ((ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.measurable_prefixReadout
      rate rewards C_star C_h n).mono le_rfl le_top)
    (fun state => StoppedQueueBound.normalizedBacklog Q state i)
    (by unfold StoppedQueueBound.normalizedBacklog stateFromReadout; fun_prop)).aestronglyMeasurable (2 * (1 / (32 * rate.eta.val)))
  filter_upwards [] with z
  change ‖backlogAt rate rewards C_star C_h n i z‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg (backlogAt_bounds rate rewards C_star C_h n i z).1]
  exact (backlogAt_bounds rate rewards C_star C_h n i z).2

private theorem V_eq_sum (n : ℕ) (z : X) : V rate rewards C_star C_h n z =
    ∑ i : Fin p.K, thetaAt rate rewards C_star C_h n i z *
      backlogAt rate rewards C_star C_h n i z ^ 2 := by
  cases h : Inputs n z <;> simp [V, thetaAt, backlogAt, h,
    RecordedWeightedDrift.weightedSquarePotential]

/-- Finite uniform envelopes from the actual full-prefix queue cap imply integrability. -/
public theorem V_integrable (n : ℕ) : Integrable (V rate rewards C_star C_h n) mu := by
  have hi i : MemLp (fun z => thetaAt rate rewards C_star C_h n i z *
      backlogAt rate rewards C_star C_h n i z ^ 2) ⊤ mu := by
    simpa only [pow_two, Pi.mul_apply] using (theta_memLp rate rewards C_star C_h n i).fun_mul (r := ⊤)
      ((backlog_memLp rate rewards C_star C_h n i).fun_mul (r := ⊤) (backlog_memLp rate rewards C_star C_h n i))
  have h := integrable_finsetSum Finset.univ (fun i _ => MemLp.integrable le_top (hi i))
  exact h.congr (Filter.Eventually.of_forall (fun z => (V_eq_sum rate rewards C_star C_h n z).symm))

private theorem coordinate_conditional_bound
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {F : MeasurableSpace Ω} (hF : F ≤ mΩ) (G : Set Ω) (hG : MeasurableSet[F] G)
    (t b r v : Ω → ℝ) (ht : MemLp t ⊤ μ) (hb : MemLp b ⊤ μ) (hr : MemLp r ⊤ μ)
    (htF : Measurable[F] t) (hbF : Measurable[F] b)
    (hv : MemLp (G.indicator v) ⊤ μ)
    (hn : ∀ z, 0 ≤ t z ∧ 0 ≤ b z)
    (hm : ∀ᵐ z ∂μ, z ∈ G → μ[r | F] z ≤ 1 ∧ μ[(fun x => r x ^ 2) | F] z ≤ v z) :
    let A := G.indicator (fun z => t z *
      ((2 * b z + 1 / 2) * r z + r z ^ 2 - (15 / 2 : ℝ) * b z + 16))
    let B := G.indicator (fun z => t z * (-(11 / 2 : ℝ) * b z + v z + 33 / 2))
    Integrable A μ ∧ Integrable B μ ∧ μ[A | F] ≤ᵐ[μ] B := by
  let u := fun z => t z * (2 * b z + 1 / 2)
  let w := fun z => t z * (-(15 / 2 : ℝ) * b z + 16)
  have hu : MemLp u ⊤ μ := ht.fun_mul (r := ⊤) ((hb.const_mul 2).add (memLp_const (1 / 2 : ℝ)))
  have hw : MemLp w ⊤ μ := ht.fun_mul (r := ⊤) ((hb.const_mul (-(15 / 2 : ℝ))).add (memLp_const 16))
  have hr2 : MemLp (fun z => r z ^ 2) ⊤ μ := by
    simpa only [pow_two] using hr.fun_mul (r := ⊤) hr
  have hur := MemLp.integrable le_top (hu.fun_mul (r := ⊤) hr)
  have htr2 := MemLp.integrable le_top (ht.fun_mul (r := ⊤) hr2)
  have hwI := MemLp.integrable le_top hw
  have hAeq : (fun z => t z *
      ((2 * b z + 1 / 2) * r z + r z ^ 2 - (15 / 2 : ℝ) * b z + 16)) =
      (fun z => (u z * r z + t z * r z ^ 2) + w z) := by
    funext z; dsimp [u, w]; ring
  have hAI : Integrable (G.indicator (fun z => t z *
      ((2 * b z + 1 / 2) * r z + r z ^ 2 - (15 / 2 : ℝ) * b z + 16))) μ := by
    rw [hAeq]; exact ((hur.add htr2).add hwI).indicator (hF _ hG)
  have hbase : MemLp (fun z => t z * (-(11 / 2 : ℝ) * b z + 33 / 2)) ⊤ μ :=
    ht.fun_mul (r := ⊤) ((hb.const_mul (-(11 / 2 : ℝ))).add (memLp_const (33 / 2 : ℝ)))
  have hBI : Integrable (G.indicator (fun z => t z *
      (-(11 / 2 : ℝ) * b z + v z + 33 / 2))) μ := by
    have h := MemLp.integrable le_top ((hbase.indicator (hF _ hG).nullMeasurableSet).add
      (ht.fun_mul (r := ⊤) hv))
    convert h using 1
    funext z
    by_cases hz : z ∈ G
    · simp only [Pi.add_apply, Set.indicator_of_mem hz]; ring
    · simp only [Pi.add_apply, Set.indicator_of_notMem hz, mul_zero, add_zero]
  have huF : Measurable[F] u := htF.mul ((measurable_const.mul hbF).add measurable_const)
  have hwF : Measurable[F] w := htF.mul ((measurable_const.mul hbF).add measurable_const)
  have hce := condExp_add (hur.add htr2) hwI F
  have hce' := condExp_add hur htr2 F
  have hpull1 := condExp_mul_of_stronglyMeasurable_left huF.stronglyMeasurable hur
    (MemLp.integrable le_top hr)
  have hpull2 := condExp_mul_of_stronglyMeasurable_left htF.stronglyMeasurable htr2
    (MemLp.integrable le_top hr2)
  have hwce := condExp_of_stronglyMeasurable hF hwF.stronglyMeasurable hwI
  have hgate := condExp_indicator ((hur.add htr2).add hwI) hG
  refine ⟨hAI, hBI, ?_⟩
  rw [hAeq]
  change μ[G.indicator (((fun z => u z * r z) + (fun z => t z * r z ^ 2)) + w) | F] ≤ᵐ[μ] _
  filter_upwards [hgate, hce, hce', hpull1, hpull2, hm] with z hg hc hc' hp1 hp2 hmz
  change μ[(fun x => u x * r x) | F] z = u z * μ[r | F] z at hp1
  change μ[(fun x => t x * r x ^ 2) | F] z = t z * μ[(fun x => r x ^ 2) | F] z at hp2
  by_cases hz : z ∈ G
  · rw [hg, Set.indicator_of_mem hz, hc, Pi.add_apply, hc', Pi.add_apply,
      hp1, hp2, hwce, Set.indicator_of_mem hz]
    have h1 := mul_le_mul_of_nonneg_left (hmz hz).1
      (mul_nonneg (hn z).1 (show 0 ≤ 2 * b z + 1 / 2 by linarith only [(hn z).2]))
    have h2 := mul_le_mul_of_nonneg_left (hmz hz).2 (hn z).1
    dsimp only [u, w] at *
    nlinarith only [h1, h2]
  · rw [hg, Set.indicator_of_notMem hz, Set.indicator_of_notMem hz]

private theorem source_drift_bound (control0 : TimeControl p) (q : Fin p.T)
    (G : Set X) (raw inv : Fin p.K → X → ℝ)
    (hG : MeasurableSet[sourcePrefixFiltration control0 (q.val + 1)] G)
    (hr : ∀ i, MemLp (raw i) ⊤ mu) (hv : ∀ i, MemLp (G.indicator (inv i)) ⊤ mu)
    (hm : ∀ i, ∀ᵐ z ∂mu, z ∈ G →
      mu[raw i | sourcePrefixFiltration control0 (q.val + 1)] z ≤ 1 ∧
      mu[(fun x => raw i x ^ 2) | sourcePrefixFiltration control0 (q.val + 1)] z ≤ inv i z)
    (hpresent : ∀ z ∈ G, ∃ past, Inputs q.val z = some past)
    (hpoint : ∀ z ∈ G, deltaV rate rewards C_star C_h q z ≤ ∑ i : Fin p.K,
      thetaAt rate rewards C_star C_h q.val i z *
        ((2 * backlogAt rate rewards C_star C_h q.val i z + 1 / 2) * raw i z +
          raw i z ^ 2 - (15 / 2 : ℝ) * backlogAt rate rewards C_star C_h q.val i z + 16)) :
    let R := fun z => -(11 / 2 : ℝ) * C rate rewards C_star C_h q.val z +
      (∑ i : Fin p.K, thetaAt rate rewards C_star C_h q.val i z * inv i z) + (33 / 2 : ℝ) * p.m
    Integrable (G.indicator (deltaV rate rewards C_star C_h q)) mu ∧
      Integrable (G.indicator R) mu ∧
      mu[G.indicator (deltaV rate rewards C_star C_h q) |
        sourcePrefixFiltration control0 (q.val + 1)] ≤ᵐ[mu] G.indicator R ∧
      (∫ z, G.indicator (deltaV rate rewards C_star C_h q) z ∂mu) ≤
        ∫ z, G.indicator R z ∂mu := by
  let F := sourcePrefixFiltration control0 (q.val + 1)
  let t := thetaAt rate rewards C_star C_h q.val
  let b := backlogAt rate rewards C_star C_h q.val
  let A := fun i => G.indicator (fun z => t i z *
    ((2 * b i z + 1 / 2) * raw i z + raw i z ^ 2 - (15 / 2 : ℝ) * b i z + 16))
  let B := fun i => G.indicator (fun z => t i z * (-(11 / 2 : ℝ) * b i z + inv i z + 33 / 2))
  have hF := (sourcePrefixFiltration control0).le' (q.val + 1)
  have hc i := coordinate_conditional_bound hF G hG (t i) (b i) (raw i) (inv i)
    (theta_memLp rate rewards C_star C_h q.val i) (backlog_memLp rate rewards C_star C_h q.val i)
    (hr i) (thetaAt_measurable rate rewards C_star C_h control0 q i)
    (backlogAt_measurable rate rewards C_star C_h control0 q i) (hv i)
    (fun z => ⟨(thetaAt_bounds rate rewards C_star C_h q.val i z).1,
      (backlogAt_bounds rate rewards C_star C_h q.val i z).1⟩) (hm i)
  have hAI : Integrable (fun z => ∑ i : Fin p.K, A i z) mu :=
    integrable_finsetSum Finset.univ (fun i _ => (hc i).1)
  have hBI : Integrable (fun z => ∑ i : Fin p.K, B i z) mu :=
    integrable_finsetSum Finset.univ (fun i _ => (hc i).2.1)
  have hD := ((V_integrable rate rewards C_star C_h (q.val + 1)).sub
    (V_integrable rate rewards C_star C_h q.val)).indicator (hF _ hG)
  have hmono : G.indicator (deltaV rate rewards C_star C_h q) ≤ᵐ[mu]
      (fun z => ∑ i : Fin p.K, A i z) := by
    filter_upwards [] with z
    by_cases hz : z ∈ G
    · simpa only [A, Set.indicator_of_mem hz] using hpoint z hz
    · simp only [A, Set.indicator_of_notMem hz, Finset.sum_const_zero]; exact le_rfl
  have hsum : (fun z => ∑ i : Fin p.K, B i z) = G.indicator (fun z =>
      -(11 / 2 : ℝ) * C rate rewards C_star C_h q.val z +
        (∑ i : Fin p.K, t i z * inv i z) + (33 / 2 : ℝ) * p.m) := by
    funext z
    by_cases hz : z ∈ G
    · obtain ⟨past, hpast⟩ := hpresent z hz
      have hth := thetaAt_sum_eq_of_prefix rate rewards C_star C_h q.val z past hpast
      have hC : C rate rewards C_star C_h q.val z = ∑ i : Fin p.K, t i z * b i z := by
        simp only [C, t, b, thetaAt, backlogAt, hpast, Option.elim_some,
          RecordedWeightedDrift.weightedBacklog]
      simp only [B, Set.indicator_of_mem hz]
      simp_rw [mul_add, Finset.sum_add_distrib, mul_left_comm (t _ z) (-(11 / 2 : ℝ)),
        ← Finset.mul_sum, ← hC, mul_comm (t _ z) (33 / 2 : ℝ)]
      rw [← Finset.mul_sum, hth]
    · simp only [B, Set.indicator_of_notMem hz, Finset.sum_const_zero]
  have hce := condExp_mono (m := F) hD hAI hmono
  have hceSum := condExp_finsetSum (s := Finset.univ) (f := A) (fun i _ => (hc i).1) F
  have hfunSum : (∑ i : Fin p.K, A i) = (fun z => ∑ i : Fin p.K, A i z) := by
    ext z; simp only [Finset.sum_apply]
  rw [hfunSum] at hceSum
  have hle : mu[G.indicator (deltaV rate rewards C_star C_h q) | F] ≤ᵐ[mu]
      (fun z => ∑ i : Fin p.K, B i z) := by
    have hall : ∀ᵐ z ∂mu, ∀ i : Fin p.K, mu[A i | F] z ≤ B i z :=
      ae_all_iff.mpr (fun i => (hc i).2.2)
    filter_upwards [hce, hceSum, hall] with z hz he hallz
    apply hz.trans
    rw [he, Finset.sum_apply]
    exact Finset.sum_le_sum (fun i _ => hallz i)
  rw [hsum] at hBI hle
  refine ⟨hD, hBI, hle, ?_⟩
  calc
    _ = ∫ z, mu[G.indicator (deltaV rate rewards C_star C_h q) | F] z ∂mu :=
      (integral_condExp hF).symm
    _ ≤ _ := integral_mono_ae integrable_condExp hBI hle

private theorem reciprocal_memLp (control0 : TimeControl p) (q : Fin p.T)
    (G : Set X) (hG : MeasurableSet[sourcePrefixFiltration control0 (q.val + 1)] G)
    (xi : X → ℝ) (hxi : Measurable[sourcePrefixFiltration control0 (q.val + 1)] xi)
    (hlo : ∀ z ∈ G, CanonicalRecordingRates.beta p rate.eta.val ≤ xi z) :
    MemLp (G.indicator (fun z => 1 / xi z)) ⊤ mu := by
  have hF := (sourcePrefixFiltration control0).le' (q.val + 1)
  apply memLp_top_of_bound (((measurable_const.div hxi).indicator hG).mono hF le_rfl).aestronglyMeasurable
    (1 / CanonicalRecordingRates.beta p rate.eta.val)
  filter_upwards [] with z
  change ‖G.indicator (fun x => 1 / xi x) z‖ ≤ _
  have hb := CanonicalRecordingRates.beta_pos p rate.eta.property
  by_cases hz : z ∈ G
  · rw [Set.indicator_of_mem hz, Real.norm_eq_abs, abs_of_nonneg (one_div_nonneg.mpr (hb.trans_le (hlo z hz)).le)]
    exact one_div_le_one_div_of_le hb (hlo z hz)
  · rw [Set.indicator_of_notMem hz, norm_zero]; exact (one_div_pos.mpr hb).le

/-- The collection retained first-moment contribution, using the full current marginals. -/
public def collectionWeightedArrival (q : Fin p.T) (z : X) : ℝ :=
  ∑ i : Fin p.K, (ReferenceOriginalCalendarCollectionRetainedEnergyStep.G
    rate rewards C_star C_h q).indicator (thetaAt rate rewards C_star C_h q.val i) z *
    ReferenceFirstCollectionOldRecorderFoundation.oldRaw rate rewards C_star C_h q i z

/-- The LIVE retained first-moment contribution, using the full current marginals. -/
public def liveWeightedArrival (q : Fin p.T) (z : X) : ℝ :=
  ∑ i : Fin p.K, (ReferenceOriginalCalendarContinuingLiveRetainedEnergyStep.liveRetainedGate
    rate rewards C_star C_h q).indicator (thetaAt rate rewards C_star C_h q.val i) z *
    ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualArrival rate rewards C_star C_h q i z

private theorem weighted_arrival_bound (control0 : TimeControl p) (q : Fin p.T)
    (G : Set X) (raw : Fin p.K → X → ℝ)
    (hG : MeasurableSet[sourcePrefixFiltration control0 (q.val + 1)] G)
    (hraw : ∀ i, Integrable (raw i) mu)
    (hmean : ∀ i, ∀ᵐ z ∂mu, z ∈ G →
      mu[raw i | sourcePrefixFiltration control0 (q.val + 1)] z ≤ 1)
    (hpresent : ∀ z ∈ G, ∃ past, Inputs q.val z = some past) :
    Integrable (fun z => ∑ i : Fin p.K, G.indicator
        (thetaAt rate rewards C_star C_h q.val i) z * raw i z) mu ∧
    (∫ z, ∑ i : Fin p.K, G.indicator
        (thetaAt rate rewards C_star C_h q.val i) z * raw i z ∂mu) ≤
      (p.m : ℝ) * (mu).real G := by
  let w := fun i => G.indicator (thetaAt rate rewards C_star C_h q.val i)
  have hF := (sourcePrefixFiltration control0).le' (q.val + 1)
  have hw i : Measurable[sourcePrefixFiltration control0 (q.val + 1)] (w i) :=
    (thetaAt_measurable rate rewards C_star C_h control0 q i).indicator hG
  have hb i z : 0 ≤ w i z ∧ w i z ≤ 1 := by
    by_cases hz : z ∈ G
    · simpa only [w, Set.indicator_of_mem hz] using
        thetaAt_bounds rate rewards C_star C_h q.val i z
    · simp only [w, Set.indicator_of_notMem hz]; norm_num
  have hn i z : ‖w i z‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (hb i z).1]; exact (hb i z).2
  have hwI i : Integrable (w i) mu :=
    integrable_of_uniform_bound ((hw i).mono hF le_rfl).aestronglyMeasurable 1 (hn i)
  have hmI i : Integrable (fun z => w i z * raw i z) mu := by
    exact (hraw i).bdd_mul
      ((hw i).mono hF le_rfl).aestronglyMeasurable (Filter.Eventually.of_forall (hn i))
  have hle i : (∫ z, w i z * raw i z ∂mu) ≤ ∫ z, w i z ∂mu := by
    rw [integral_predictable_mul_condExp hF (hw i) (hn i) (hraw i)]
    have hprod : Integrable (fun z => w i z * mu[raw i |
        sourcePrefixFiltration control0 (q.val + 1)] z) mu := by
      exact (integrable_condExp (f := raw i)).bdd_mul
        ((hw i).mono hF le_rfl).aestronglyMeasurable (Filter.Eventually.of_forall (hn i))
    apply integral_mono_ae hprod (hwI i)
    filter_upwards [hmean i] with z hz
    by_cases h : z ∈ G
    · exact (mul_le_mul_of_nonneg_left (hz h) (hb i z).1).trans_eq (mul_one _)
    · simp only [w, Set.indicator_of_notMem h, zero_mul]; exact le_rfl
  refine ⟨integrable_finsetSum Finset.univ (fun i _ => hmI i), ?_⟩
  change (∫ z, ∑ i : Fin p.K, w i z * raw i z ∂mu) ≤ _
  rw [integral_finsetSum _ (fun i _ => hmI i)]
  calc
    _ ≤ ∑ i : Fin p.K, ∫ z, w i z ∂mu := Finset.sum_le_sum (fun i _ => hle i)
    _ = ∫ z, ∑ i : Fin p.K, w i z ∂mu :=
      (integral_finsetSum _ (fun i _ => hwI i)).symm
    _ = ∫ z, G.indicator (fun _ : X => (p.m : ℝ)) z ∂mu := by
      apply integral_congr_ae; filter_upwards [] with z
      by_cases hz : z ∈ G
      · obtain ⟨past, hpast⟩ := hpresent z hz
        simpa only [w, Set.indicator_of_mem hz] using
          thetaAt_sum_eq_of_prefix rate rewards C_star C_h q.val z past hpast
      · simp only [w, Set.indicator_of_notMem hz, Finset.sum_const_zero]
    _ = _ := by rw [integral_indicator_const _ (hF _ hG), smul_eq_mul]; ring

private theorem collection_arrival_bound (control0 : TimeControl p) (q : Fin p.T) :
    Integrable (collectionWeightedArrival rate rewards C_star C_h q) mu ∧
    (∫ z, collectionWeightedArrival rate rewards C_star C_h q z ∂mu) ≤
      (p.m : ℝ) * (mu).real (ReferenceOriginalCalendarCollectionRetainedEnergyStep.G
        rate rewards C_star C_h q) := by
  apply weighted_arrival_bound rate rewards C_star C_h control0 q
    _ _ (ReferenceOriginalCalendarCollectionRetainedEnergyStep.measurableSet_G
      rate rewards C_star C_h control0 q)
    (fun i => ReferenceFirstCollectionOldRecorderFoundation.oldRaw_integrable
      rate rewards C_star C_h q i)
    (fun i => collection_oldRaw_condExp_upper_on_G rate rewards C_star C_h control0 q i)
  intro z hz
  obtain ⟨past, _, hpast, _⟩ := collection_deltaV_transition rate rewards C_star C_h q z hz
  exact ⟨past, hpast⟩

private theorem live_arrival_bound (control0 : TimeControl p) (q : Fin p.T) :
    Integrable (liveWeightedArrival rate rewards C_star C_h q) mu ∧
    (∫ z, liveWeightedArrival rate rewards C_star C_h q z ∂mu) ≤
      (p.m : ℝ) * (mu).real (ReferenceOriginalCalendarContinuingLiveRetainedEnergyStep.liveRetainedGate
        rate rewards C_star C_h q) := by
  refine weighted_arrival_bound rate rewards C_star C_h control0 q
    _ _ (ReferenceOriginalCalendarContinuingLiveRetainedEnergyStep.measurableSet_liveRetainedGate
      rate rewards C_star C_h control0 q)
    (fun i => ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualArrival_integrable
      rate rewards C_star C_h control0 q i) ?_ ?_
  · intro i
    filter_upwards [ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualArrival_condExp_bounds
      rate rewards C_star C_h control0 q i] with z hz
    intro hG
    exact (hz hG.1.1).2.trans (by
      simpa only [ReferenceFirstCollectionOldRecorderFoundation.roundedReward] using
        (ReferenceFirstCollectionOldRecorderFoundation.roundedReward_bounds rewards q i).2)
  · intro z hz
    obtain ⟨past, _, hpast, _⟩ := live_deltaV_transition rate rewards C_star C_h q z hz
    exact ⟨past, hpast⟩

/-- Integrability of the unrestricted retained collection weighted arrivals. -/
public theorem collectionWeightedArrival_integrable (control0 : TimeControl p) (q : Fin p.T) :
    Integrable (collectionWeightedArrival rate rewards C_star C_h q) mu :=
  (collection_arrival_bound rate rewards C_star C_h control0 q).1

/-- The unrestricted collection arrivals cost at most `m` times the actual gate mass. -/
public theorem collectionWeightedArrival_integral_le (control0 : TimeControl p) (q : Fin p.T) :
    (∫ z, collectionWeightedArrival rate rewards C_star C_h q z ∂mu) ≤
      (p.m : ℝ) * (mu).real (ReferenceOriginalCalendarCollectionRetainedEnergyStep.G
        rate rewards C_star C_h q) :=
  (collection_arrival_bound rate rewards C_star C_h control0 q).2

/-- Integrability of the actual retained LIVE weighted arrivals. -/
public theorem liveWeightedArrival_integrable (control0 : TimeControl p) (q : Fin p.T) :
    Integrable (liveWeightedArrival rate rewards C_star C_h q) mu :=
  (live_arrival_bound rate rewards C_star C_h control0 q).1

/-- The LIVE arrivals cost at most `m` times the actual retained gate mass. -/
public theorem liveWeightedArrival_integral_le (control0 : TimeControl p) (q : Fin p.T) :
    (∫ z, liveWeightedArrival rate rewards C_star C_h q z ∂mu) ≤
      (p.m : ℝ) * (mu).real (ReferenceOriginalCalendarContinuingLiveRetainedEnergyStep.liveRetainedGate
        rate rewards C_star C_h q) :=
  (live_arrival_bound rate rewards C_star C_h control0 q).2

private theorem live_raw_memLp (control0 : TimeControl p) (q : Fin p.T) (i : Fin p.K) :
    MemLp (ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualArrival
      rate rewards C_star C_h q i) ⊤ mu := by
  apply memLp_top_of_bound (ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualArrival_integrable
    rate rewards C_star C_h control0 q i).aestronglyMeasurable (1 / CanonicalRecordingRates.beta p rate.eta.val)
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_of_nonneg (ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualArrival_bounds
    rate rewards C_star C_h q i z).1]
  exact (ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualArrival_bounds rate rewards C_star C_h q i z).2

private theorem collection_raw_memLp (q : Fin p.T) (i : Fin p.K) :
    MemLp (ReferenceFirstCollectionOldRecorderFoundation.oldRaw rate rewards C_star C_h q i) ⊤ mu := by
  apply memLp_top_of_bound (ReferenceFirstCollectionOldRecorderFoundation.oldRaw_integrable
    rate rewards C_star C_h q i).aestronglyMeasurable (1 / CanonicalRecordingRates.beta p rate.eta.val)
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_of_nonneg (ReferenceFirstCollectionOldRecorderFoundation.oldRaw_bounds
    rate rewards C_star C_h q i z).1]
  exact (ReferenceFirstCollectionOldRecorderFoundation.oldRaw_bounds rate rewards C_star C_h q i z).2

/-- Actual LIVE raw squares are integrable, including recorded zero floors. -/
public theorem live_arrival_square_integrable (control0 : TimeControl p) (q : Fin p.T) (i : Fin p.K) :
    Integrable (fun z => ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualArrival
      rate rewards C_star C_h q i z ^ 2) mu := by
  simpa only [pow_two] using MemLp.integrable le_top
    ((live_raw_memLp rate rewards C_star C_h control0 q i).fun_mul (r := ⊤)
      (live_raw_memLp rate rewards C_star C_h control0 q i))

/-- Actual unrestricted collection raw squares are integrable. -/
public theorem collection_oldRaw_square_integrable (q : Fin p.T) (i : Fin p.K) :
    Integrable (fun z => ReferenceFirstCollectionOldRecorderFoundation.oldRaw
      rate rewards C_star C_h q i z ^ 2) mu := by
  simpa only [pow_two] using MemLp.integrable le_top
    ((collection_raw_memLp rate rewards C_star C_h q i).fun_mul (r := ⊤)
      (collection_raw_memLp rate rewards C_star C_h q i))

/-- The LIVE drift allowance retains the actual payload reciprocal-rate sum. -/
public def liveDriftRHS (q : Fin p.T) (z : X) : ℝ :=
  -(11 / 2 : ℝ) * C rate rewards C_star C_h q.val z +
    (∑ i : Fin p.K, thetaAt rate rewards C_star C_h q.val i z /
      ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualRate rate rewards C_star C_h q i z) +
    (33 / 2 : ℝ) * p.m

/-- The unrestricted collection allowance uses the same incoming payload rates. -/
public def collectionDriftRHS (q : Fin p.T) (z : X) : ℝ :=
  -(11 / 2 : ℝ) * C rate rewards C_star C_h q.val z +
    (∑ i : Fin p.K, thetaAt rate rewards C_star C_h q.val i z /
      (ReferenceFirstCollectionOldRecorderFoundation.incomingRates?
        rate rewards C_star C_h q z).getD (fun _ => 0) i) + (33 / 2 : ℝ) * p.m

/-- Conditional and integrated actual LIVE weighted-square drift under the original joint
source law. Both sides are integrable; retention inspects only the incoming overflow. -/
public theorem live_retained_weightedSquare_drift (control0 : TimeControl p) (q : Fin p.T) :
    let G := ReferenceOriginalCalendarContinuingLiveRetainedEnergyStep.liveRetainedGate rate rewards C_star C_h q
    Integrable (G.indicator (deltaV rate rewards C_star C_h q)) mu ∧
      Integrable (G.indicator (liveDriftRHS rate rewards C_star C_h q)) mu ∧
      mu[G.indicator (deltaV rate rewards C_star C_h q) |
        sourcePrefixFiltration control0 (q.val + 1)] ≤ᵐ[mu]
        G.indicator (liveDriftRHS rate rewards C_star C_h q) ∧
      (∫ z, G.indicator (deltaV rate rewards C_star C_h q) z ∂mu) ≤
        ∫ z, G.indicator (liveDriftRHS rate rewards C_star C_h q) z ∂mu := by
  let G := ReferenceOriginalCalendarContinuingLiveRetainedEnergyStep.liveRetainedGate rate rewards C_star C_h q
  have hG := ReferenceOriginalCalendarContinuingLiveRetainedEnergyStep.measurableSet_liveRetainedGate
    rate rewards C_star C_h control0 q
  have hv i : MemLp (G.indicator (fun z => 1 /
      ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualRate rate rewards C_star C_h q i z)) ⊤ mu := by
    apply reciprocal_memLp rate control0 q G hG _
      (ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualRate_measurable rate rewards C_star C_h control0 q i)
    intro z hz
    obtain ⟨_, _, _, _, cell, selected, _, _, _, hc, _, _, hr, _, _⟩ :=
      ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualCell_data rate rewards C_star C_h q z hz.1.1
    have hzD : z ∈ ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualDomain
        rate rewards C_star C_h q := hz.1.1
    simpa only [ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualRate,
      ite_eq_left hzD, ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualParameters,
      hc, Option.map_some, hr] using selected.view.payload.beta_le_rate i
  have hm i : ∀ᵐ z ∂mu, z ∈ G →
      mu[ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualArrival rate rewards C_star C_h q i |
        sourcePrefixFiltration control0 (q.val + 1)] z ≤ 1 ∧
      mu[(fun x => ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualArrival rate rewards C_star C_h q i x ^ 2) |
        sourcePrefixFiltration control0 (q.val + 1)] z ≤
        1 / ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualRate rate rewards C_star C_h q i z := by
    filter_upwards [ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualArrival_condExp_bounds
      rate rewards C_star C_h control0 q i,
      live_arrival_square_condExp_bound_on_domain rate rewards C_star C_h control0 q i] with z hm hs
    intro hz
    exact ⟨(hm hz.1.1).2.trans (by simpa only [ReferenceFirstCollectionOldRecorderFoundation.roundedReward]
      using (ReferenceFirstCollectionOldRecorderFoundation.roundedReward_bounds rewards q i).2), hs hz.1.1⟩
  have hp z (hz : z ∈ G) : ∃ past, Inputs q.val z = some past := by
    obtain ⟨past, _, hpast, _⟩ := live_deltaV_transition rate rewards C_star C_h q z hz
    exact ⟨past, hpast⟩
  have hR : (fun z => -(11 / 2 : ℝ) * C rate rewards C_star C_h q.val z +
      (∑ i : Fin p.K, thetaAt rate rewards C_star C_h q.val i z * (1 /
        ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualRate rate rewards C_star C_h q i z)) +
      (33 / 2 : ℝ) * p.m) = liveDriftRHS rate rewards C_star C_h q := by
    funext z; simp only [liveDriftRHS, mul_one_div]
  have h := source_drift_bound rate rewards C_star C_h control0 q G
      (ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualArrival rate rewards C_star C_h q)
      (fun i z => 1 / ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualRate rate rewards C_star C_h q i z)
      hG (live_raw_memLp rate rewards C_star C_h control0 q) hv hm hp
      (live_deltaV_le rate rewards C_star C_h q)
  dsimp only at h
  rw [hR] at h
  exact h

/-- Conditional and integrated unrestricted collection weighted-square drift. The domain
includes every present collection/cutoff cell, with no before-first-call restriction. -/
public theorem collection_retained_weightedSquare_drift (control0 : TimeControl p) (q : Fin p.T) :
    let G := ReferenceOriginalCalendarCollectionRetainedEnergyStep.G rate rewards C_star C_h q
    Integrable (G.indicator (deltaV rate rewards C_star C_h q)) mu ∧
      Integrable (G.indicator (collectionDriftRHS rate rewards C_star C_h q)) mu ∧
      mu[G.indicator (deltaV rate rewards C_star C_h q) |
        sourcePrefixFiltration control0 (q.val + 1)] ≤ᵐ[mu]
        G.indicator (collectionDriftRHS rate rewards C_star C_h q) ∧
      (∫ z, G.indicator (deltaV rate rewards C_star C_h q) z ∂mu) ≤
        ∫ z, G.indicator (collectionDriftRHS rate rewards C_star C_h q) z ∂mu := by
  let G := ReferenceOriginalCalendarCollectionRetainedEnergyStep.G rate rewards C_star C_h q
  let xi := fun i z => (ReferenceFirstCollectionOldRecorderFoundation.incomingRates?
    rate rewards C_star C_h q z).getD (fun _ => 0) i
  have hG := ReferenceOriginalCalendarCollectionRetainedEnergyStep.measurableSet_G
    rate rewards C_star C_h control0 q
  have hxi i : Measurable[sourcePrefixFiltration control0 (q.val + 1)] (xi i) := by
    have hg : Measurable (fun o : Option (Fin p.K → ℝ) => o.getD (fun _ => 0) i) := by
      convert ((measurable_pi_apply i).sumElim (measurable_const (a := (0 : ℝ)))).comp
        (comap_measurable (Equiv.optionEquivSumPUnit (Fin p.K → ℝ))) using 1
      funext o; cases o <;> rfl
    exact hg.comp (ReferenceFirstCollectionOldRecorderFoundation.incomingRates_measurable
      rate rewards C_star C_h control0 q)
  have hv i : MemLp (G.indicator (fun z => 1 / xi i z)) ⊤ mu := by
    apply reciprocal_memLp rate control0 q G hG _ (hxi i)
    intro z hz
    obtain ⟨_, _, payload, _, _, hp, _, _⟩ :=
      ReferenceOriginalCalendarCollectionRetainedEnergyStep.presentCell_recordingMap
        rate rewards C_star C_h q z hz.1.1.1
    simpa only [xi, ReferenceFirstCollectionOldRecorderFoundation.incomingRates?, hp,
      Option.map_some, Option.getD_some] using payload.beta_le_rate i
  have hm i : ∀ᵐ z ∂mu, z ∈ G →
      mu[ReferenceFirstCollectionOldRecorderFoundation.oldRaw rate rewards C_star C_h q i |
        sourcePrefixFiltration control0 (q.val + 1)] z ≤ 1 ∧
      mu[(fun x => ReferenceFirstCollectionOldRecorderFoundation.oldRaw rate rewards C_star C_h q i x ^ 2) |
        sourcePrefixFiltration control0 (q.val + 1)] z ≤ 1 / xi i z := by
    filter_upwards [collection_oldRaw_condExp_upper_on_G rate rewards C_star C_h control0 q i,
      collection_oldRaw_square_condExp_bound_on_G rate rewards C_star C_h control0 q i] with z hm hs
    exact fun hz => ⟨hm hz, hs hz⟩
  have hp z (hz : z ∈ G) : ∃ past, Inputs q.val z = some past := by
    obtain ⟨past, _, hpast, _⟩ := collection_deltaV_transition rate rewards C_star C_h q z hz
    exact ⟨past, hpast⟩
  have hR : (fun z => -(11 / 2 : ℝ) * C rate rewards C_star C_h q.val z +
      (∑ i : Fin p.K, thetaAt rate rewards C_star C_h q.val i z * (1 / xi i z)) +
      (33 / 2 : ℝ) * p.m) = collectionDriftRHS rate rewards C_star C_h q := by
    funext z; simp only [collectionDriftRHS, xi, mul_one_div]
  have h := source_drift_bound rate rewards C_star C_h control0 q G
      (ReferenceFirstCollectionOldRecorderFoundation.oldRaw rate rewards C_star C_h q)
      (fun i z => 1 / xi i z) hG (collection_raw_memLp rate rewards C_star C_h q) hv hm hp
      (collection_deltaV_le rate rewards C_star C_h q)
  dsimp only at h
  rw [hR] at h
  exact h

end Bandits.Support.ReferenceOriginalCalendarLiveCollectionWeightedDrift

end
