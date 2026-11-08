/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionCorrectedFutureRetainedMoment
public import Bandits.Support.ReferenceFirstCollectionCorrectedStoppedEnergyTelescope

import Mathlib.Tactic

/-!
# Original-source corrected-cell energy and overflow

Sources: `04_slow_fast_learner.tex:140-188,245-290` and
`06_interruptions.tex:355-426`. These are internal probabilistic components
for the physical first-collection overflow cover. The birth observation is the
actual inherited AFTER energy. No global birth-energy sum is asserted here.
-/

@[expose] public section
noncomputable section

open MeasureTheory Bandits.Support ConstructorDimensions
open BootstrapPrivateRoundStreams (SourceInput sourceInputLaw)
open ContinuousLearningRows (TimeControl)
open ReferenceSourcePrefixHistoryFiltration (sourcePrefixFiltration actualRecord)
open ReferenceFirstCollectionRenewalIncomingQueueMeasurability (stateReadout)
open ReferenceFirstCollectionCorrectedStoppedEnergyTelescope
  (energyCeiling energyIncrement energyIncrement_actual_step energyIncrement_eq_zero
    energyIncrement_off_cell integrable_energyIncrement integrable_stoppedEnergy
    integral_stoppedEnergy_telescope measurable_stoppedEnergy stoppedEnergy
    stoppedEnergy_birth_actual stoppedEnergy_bounds stoppedEnergy_eq_readout stoppedEnergy_off_cell
    stoppedEnergy_terminal_actual)
open ReferenceFirstCollectionCorrectedFutureRetainedMoment
  (condExp_exp_retainedIncrement_le_one exp_retainedIncrement_integrable
    exp_retainedIncrement_measurable futureArrival prefixInputs_eq_pastCells
    prefixReadout_eq_current retainedGate retainedIncrement retainedIncrement_bounds
    retainedIncrement_off_gate)
open ReferenceFirstCollectionCorrectedSliceNumericalPrefix
  (birthIndex correctedCell cutoffDelta endDate endpoint_exp_gt_cap firstCell_birth_time liveTail
    overflowEvent overflowEvent_iff_endpoint prefixInputs prefixReadout sourceRecords sourceStart)
open ReferenceFirstCollectionCorrectedFutureRecordingView
  (futureCell futureGate futureParameters)
open ReferenceFirstCollectionCorrectedNextRetainedMoment
  (condExp_exp_successorIncrement_le_one exp_successorIncrement_integrable nextArrival
    retainedIncrement_eq_on_gate retainedIncrement_of_not_mem retained_successor_queue_witness
    successorIncrement)
open ReferenceFirstCollectionCorrectedNextRetainedGate
  (firstCell_after_eq_successor_prefix)
open ReferenceFirstCollectionCorrectedNextPhysicalReadout
  (firstCell_next_readouts firstCell_successor_records nextCell nextParameters)
open scoped Classical BigOperators

namespace Bandits.Support.ReferenceFirstCollectionCorrectedOriginalSourceOverflow

variable {p : Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)

local notation "X" => SourceInput p
local notation "mu" => sourceInputLaw p
local notation "Q" => ReferenceFirstLaunchNumericalCell.queueParameters rate
local notation "beta" => CanonicalRecordingRates.beta p rate.eta.val
local notation "Input" => RecordedQueueRun.RoundInput p.K
local notation "Readout" => ReferenceFirstCollectionCurrentQueueReadout.QueueReadout p.K

local instance optionMeasurableSpace {A : Type*} [MeasurableSpace A] :
    MeasurableSpace (Option A) :=
  LaterAssignmentStartMeasurability.optionMeasurableSpace

/-- Scalar observation of the actual optional incoming readout. An absent
readout has zero scalar energy, without inventing a queue state. -/
def currentEnergy (q : Fin p.T) (a : Fin p.K) (x : X) : ℝ :=
  (ReferenceFirstCollectionCurrentRetainedGate.prefixReadout?
    rate rewards C_star C_h q x).elim 0 (fun o =>
      Real.exp (beta * ((o.1 a).2 : ℝ) / ((Q).n : ℝ)))

/-- Incoming energy multiplied by the real strict-future retention gate. -/
def futureMultiplier (u t q : Fin p.T) (a : Fin p.K) : X → ℝ :=
  (retainedGate rate rewards C_star C_h u t q).indicator
    (stoppedEnergy rate rewards C_star C_h u t a q.val)

theorem currentEnergy_predictable (control0 : TimeControl p) (q : Fin p.T)
    (a : Fin p.K) :
    Measurable[sourcePrefixFiltration control0 (q.val + 1)]
      (currentEnergy rate rewards C_star C_h q a) := by
  have he : Measurable (fun v : Readout =>
      Real.exp (beta * ((v.1 a).2 : ℝ) / ((Q).n : ℝ))) :=
    (measurable_of_countable (fun n : ℕ => Real.exp (beta * (n : ℝ) / ((Q).n : ℝ)))).comp
      (measurable_snd.comp ((measurable_pi_apply a).comp measurable_fst))
  have hs : Measurable (fun o : Option Readout => o.elim 0 (fun v =>
      Real.exp (beta * ((v.1 a).2 : ℝ) / ((Q).n : ℝ)))) := by
    convert (he.sumElim measurable_const).comp
      (comap_measurable (Equiv.optionEquivSumPUnit Readout)) using 1
    funext o
    cases o <;> rfl
  exact hs.comp
    (ReferenceFirstCollectionCurrentRetainedGate.prefixReadout_measurable
      rate rewards C_star C_h control0 q)

/-- The full-horizon clamp disappears only on the actual active gate. -/
theorem futureMultiplier_eq_current (u t q : Fin p.T)
    (hfuture : t.val + 1 ≤ q.val) (a : Fin p.K) :
    futureMultiplier rate rewards C_star C_h u t q a =
      (retainedGate rate rewards C_star C_h u t q).indicator
        (currentEnergy rate rewards C_star C_h q a) := by
  funext x
  by_cases hg : x ∈ retainedGate rate rewards C_star C_h u t q
  · obtain ⟨o, ho, _⟩ := hg.1.2
    have he := stoppedEnergy_eq_readout rate rewards C_star C_h u t a q.val x
      hg.1.1.1 (by omega) hg.1.1.2.le o ho
    simp only [futureMultiplier, Set.indicator_of_mem hg, he, currentEnergy,
      ← prefixReadout_eq_current, ho, Option.elim_some]
  · simp only [futureMultiplier, Set.indicator_of_notMem hg]

theorem futureMultiplier_predictable (control0 : TimeControl p) (u t q : Fin p.T)
    (hfuture : t.val + 1 < q.val) (a : Fin p.K) :
    Measurable[sourcePrefixFiltration control0 (q.val + 1)]
      (futureMultiplier rate rewards C_star C_h u t q a) := by
  rw [futureMultiplier_eq_current rate rewards C_star C_h u t q hfuture.le a]
  exact (currentEnergy_predictable rate rewards C_star C_h control0 q a).indicator
    (ReferenceFirstCollectionCorrectedFutureRetainedMoment.retainedGate_measurable rate rewards C_star C_h control0 u t q hfuture)

theorem futureMultiplier_bounds (u t q : Fin p.T) (a : Fin p.K) (x : X) :
    0 ≤ futureMultiplier rate rewards C_star C_h u t q a x ∧
      futureMultiplier rate rewards C_star C_h u t q a x ≤ energyCeiling rate := by
  by_cases hg : x ∈ retainedGate rate rewards C_star C_h u t q
  · simpa only [futureMultiplier, Set.indicator_of_mem hg] using
      stoppedEnergy_bounds rate rewards C_star C_h u t a q.val x
  · simp only [futureMultiplier, Set.indicator_of_notMem hg]
    exact ⟨le_rfl, (Real.exp_pos _).le⟩

theorem futureMultiplier_integrable (control0 : TimeControl p) (u t q : Fin p.T)
    (hfuture : t.val + 1 < q.val) (a : Fin p.K) :
    Integrable (futureMultiplier rate rewards C_star C_h u t q a) mu := by
  exact (integrable_stoppedEnergy rate rewards C_star C_h u t a q.val).indicator
    (((sourcePrefixFiltration control0).le' (q.val + 1)) _
      (ReferenceFirstCollectionCorrectedFutureRetainedMoment.retainedGate_measurable
        rate rewards C_star C_h control0 u t q hfuture))

private theorem step_exp_le (s : RecordedQueueRun.RunState p.K) (c : Input)
    (a : Fin p.K) (hf : s.overflow = false) (he : c.enabled = true) :
    Real.exp (beta * (((RecordedQueueRun.step Q s c).registers a).2 : ℝ) / ((Q).n : ℝ)) ≤
      1 + Real.exp (beta * ((s.registers a).2 : ℝ) / ((Q).n : ℝ)) *
        Real.exp (beta * (RecordedRoundMoments.rawEstimate Q s c a - 4)) := by
  have hr := CanonicalQueueProcess.normalizedBacklog_step_of_retained Q s c a hf he
  have hb := CanonicalQueueProcess.exp_mul_max_le
    (StoppedQueueBound.normalizedBacklog Q s a)
    (RecordedRoundMoments.rawEstimate Q s c a - 4) beta
  rw [show StoppedQueueBound.normalizedBacklog Q s a +
      (RecordedRoundMoments.rawEstimate Q s c a - 4) =
      StoppedQueueBound.normalizedBacklog Q s a +
        RecordedRoundMoments.rawEstimate Q s c a - 4 by ring] at hb
  rw [← hr] at hb
  simpa only [StoppedQueueBound.normalizedBacklog, mul_div_assoc] using hb

/-- Actual cell alignment for the scalar telescope, on its literal open slice. -/
theorem energyIncrement_cell (u t q : Fin p.T) (a : Fin p.K) (x : X)
    (hx : x ∈ correctedCell rate rewards C_star C_h u t)
    (hq : t.val + 1 ≤ q.val) (hqe : q.val < endDate rate rewards C_star C_h t x) :
    ∃ L c, prefixInputs rate rewards C_star C_h q.val x = some L ∧
      (actualRecord rate rewards C_star C_h q x).bind
        (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate) = some c ∧
      stoppedEnergy rate rewards C_star C_h u t a q.val x =
        Real.exp (beta * (((RecordedQueueRun.run Q L).registers a).2 : ℝ) / ((Q).n : ℝ)) ∧
      energyIncrement rate rewards C_star C_h u t a q x =
        Real.exp (beta * (((RecordedQueueRun.step Q (RecordedQueueRun.run Q L) c).registers a).2 : ℝ) /
          ((Q).n : ℝ)) -
        Real.exp (beta * (((RecordedQueueRun.run Q L).registers a).2 : ℝ) / ((Q).n : ℝ)) := by
  obtain ⟨L, r, c, hL, hr, hc, _hnext, hdelta⟩ :=
    energyIncrement_actual_step rate rewards C_star C_h u t a q x hx hq hqe
  have hb := firstCell_birth_time rate rewards C_star C_h u t x hx
  have hs : ReferenceCompletePhysicalHistory.physicalStart rate x rewards C_star C_h ≤ q.val := by
    change sourceStart rate rewards C_star C_h x ≤ q.val
    omega
  have har : actualRecord rate rewards C_star C_h q x = some r := by
    simpa only [actualRecord, ite_eq_left hs, sourceRecords, sourceStart] using hr
  refine ⟨L, c, hL, by rw [har, Option.bind_some]; exact hc, ?_, hdelta⟩
  apply stoppedEnergy_eq_readout rate rewards C_star C_h u t a q.val x hx hq hqe.le
    (stateReadout (RecordedQueueRun.run Q L))
  simp only [prefixReadout, hL, Option.map_some]

/-- One actual strict-future energy difference, retaining the outgoing crossing. -/
theorem energyIncrement_le_future (u t q : Fin p.T)
    (hfuture : t.val + 1 ≤ q.val) (a : Fin p.K) (x : X) :
    energyIncrement rate rewards C_star C_h u t a q x ≤
      (retainedGate rate rewards C_star C_h u t q).indicator (fun _ => (1 : ℝ)) x +
      futureMultiplier rate rewards C_star C_h u t q a x *
        Real.exp (beta * retainedIncrement rate rewards C_star C_h u t q a x) -
      futureMultiplier rate rewards C_star C_h u t q a x := by
  by_cases hx : x ∈ correctedCell rate rewards C_star C_h u t
  · by_cases hqe : q.val < endDate rate rewards C_star C_h t x
    · obtain ⟨L, c, hL, hc, hbefore, hdelta⟩ :=
        energyIncrement_cell rate rewards C_star C_h u t q a x hx (by omega) hqe
      have hfg : x ∈ futureGate rate rewards C_star C_h u t q := ⟨hx, hqe⟩
      have hcell : futureCell rate rewards C_star C_h u t q x = some c := by
        simpa only [futureCell, ite_eq_left hfg] using hc
      by_cases hf : (RecordedQueueRun.run Q L).overflow = false
      · by_cases he : c.enabled = true
        · have hg : x ∈ retainedGate rate rewards C_star C_h u t q :=
            ⟨⟨hfg, stateReadout (RecordedQueueRun.run Q L), by
              simp only [prefixReadout, hL, Option.map_some], hf⟩,
              c.rate, by simp only [futureParameters, hcell, Option.map_some, he]⟩
          have hi : retainedIncrement rate rewards C_star C_h u t q a x =
              RecordedRoundMoments.rawEstimate Q (RecordedQueueRun.run Q L) c a - 4 := by
            simp only [retainedIncrement, Set.indicator_of_mem hg, futureArrival, hL, hcell]
          rw [hdelta, Set.indicator_of_mem hg, futureMultiplier,
            Set.indicator_of_mem hg, hbefore, hi]
          linarith only [step_exp_le rate (RecordedQueueRun.run Q L) c a hf he]
        · have hg : x ∉ retainedGate rate rewards C_star C_h u t q := by
            rintro ⟨_, xi, hp⟩
            simp only [futureParameters, hcell, Option.map_some, Option.some.injEq,
              Prod.mk.injEq] at hp
            exact he hp.1
          have hp := (RecordedQueueRun.step_disabled_preserves Q (RecordedQueueRun.run Q L)
            c (Bool.eq_false_iff.mpr he) a).1
          simp only [hdelta, hp, sub_self, Set.indicator_of_notMem hg, futureMultiplier,
            zero_mul, add_zero, le_refl]
      · have ht := Bool.eq_true_of_not_eq_false hf
        have hg : x ∉ retainedGate rate rewards C_star C_h u t q := by
          rintro ⟨⟨_, o, ho, hflag⟩, _⟩
          have hr : stateReadout (RecordedQueueRun.run Q L) = o :=
            Option.some.inj (by simpa only [prefixReadout, hL, Option.map_some] using ho)
          exact hf ((congrArg (fun v => v.2.1) hr).trans hflag)
        have hp := (RecordedQueueRun.step_after_overflow_preserves Q (RecordedQueueRun.run Q L)
          c ht a).1
        simp only [hdelta, hp, sub_self, Set.indicator_of_notMem hg, futureMultiplier,
          zero_mul, add_zero, le_refl]
    · have hg : x ∉ retainedGate rate rewards C_star C_h u t q := fun h => hqe h.1.1.2
      rw [energyIncrement_eq_zero rate rewards C_star C_h u t a q x (Or.inr (by omega))]
      simp only [Set.indicator_of_notMem hg, futureMultiplier, zero_mul, add_zero, sub_zero, le_refl]
  · have hg : x ∉ retainedGate rate rewards C_star C_h u t q := fun h => hx h.1.1.1
    rw [energyIncrement_off_cell rate rewards C_star C_h u t a q x hx]
    simp only [Set.indicator_of_notMem hg, futureMultiplier, zero_mul, add_zero, sub_zero, le_refl]

/-- Product regularity follows from the actual queue and arrival envelopes. -/
theorem futureMultiplier_product_integrable (control0 : TimeControl p)
    (u t q : Fin p.T) (hfuture : t.val + 1 < q.val) (a : Fin p.K) :
    Integrable (fun x => futureMultiplier rate rewards C_star C_h u t q a x *
      Real.exp (beta * retainedIncrement rate rewards C_star C_h u t q a x)) mu := by
  have hm := (futureMultiplier_predictable rate rewards C_star C_h control0 u t q hfuture a).mono
    ((sourcePrefixFiltration control0).le' (q.val + 1)) le_rfl
  have hz := exp_retainedIncrement_measurable rate rewards C_star C_h control0 u t q hfuture a
  apply (integrable_const (energyCeiling rate * Real.exp 1)).mono'
    (hm.mul hz).aestronglyMeasurable
  filter_upwards [] with x
  have hw := futureMultiplier_bounds rate rewards C_star C_h u t q a x
  have hz0 : 0 ≤ Real.exp (beta * retainedIncrement rate rewards C_star C_h u t q a x) :=
    Real.exp_nonneg _
  have hz1 : Real.exp (beta * retainedIncrement rate rewards C_star C_h u t q a x) ≤
      Real.exp 1 := by
    apply Real.exp_le_exp.mpr
    calc
      _ ≤ beta * (1 / beta) := mul_le_mul_of_nonneg_left
        (retainedIncrement_bounds rate rewards C_star C_h u t q hfuture a x).2
        (CanonicalRecordingRates.beta_pos p rate.eta.property).le
      _ = 1 := by field_simp [ne_of_gt (CanonicalRecordingRates.beta_pos p rate.eta.property)]
  simp only [Pi.mul_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hw.1 hz0)]
  exact mul_le_mul hw.2 hz1 hz0 (Real.exp_nonneg _)

private theorem integral_predictable_mul_le (control0 : TimeControl p) (q : Fin p.T)
    (W Z : X → ℝ) (hW : Measurable[sourcePrefixFiltration control0 (q.val + 1)] W)
    (hWi : Integrable W mu) (hZi : Integrable Z mu) (hWZi : Integrable (W * Z) mu)
    (hW0 : ∀ x, 0 ≤ W x)
    (hZ : mu[Z | sourcePrefixFiltration control0 (q.val + 1)] ≤ᵐ[mu] (fun _ => (1 : ℝ))) :
    (∫ x, W x * Z x ∂mu) ≤ ∫ x, W x ∂mu := by
  have hp := condExp_mul_of_stronglyMeasurable_left hW.stronglyMeasurable hWZi hZi
  have hb : mu[W * Z | sourcePrefixFiltration control0 (q.val + 1)] ≤ᵐ[mu] W := by
    filter_upwards [hp, hZ] with x hx hz
    rw [hx]
    simpa only [Pi.mul_apply, mul_one] using mul_le_mul_of_nonneg_left hz (hW0 x)
  calc
    _ = ∫ x, mu[W * Z | sourcePrefixFiltration control0 (q.val + 1)] x ∂mu :=
      (integral_condExp ((sourcePrefixFiltration control0).le' (q.val + 1))).symm
    _ ≤ _ := integral_mono_ae integrable_condExp hWi hb

/-- A sharper strict-future bound by the actual retained enabled gate mass. -/
theorem integral_energyIncrement_le_future_gate (control0 : TimeControl p)
    (u t q : Fin p.T) (hfuture : t.val + 1 < q.val) (a : Fin p.K) :
    (∫ x, energyIncrement rate rewards C_star C_h u t a q x ∂mu) ≤
      (mu (retainedGate rate rewards C_star C_h u t q)).toReal := by
  let W := futureMultiplier rate rewards C_star C_h u t q a
  let Z : X → ℝ := fun x => Real.exp (beta * retainedIncrement rate rewards C_star C_h u t q a x)
  let G := retainedGate rate rewards C_star C_h u t q
  have hG : MeasurableSet G := ((sourcePrefixFiltration control0).le' (q.val + 1)) _
    (ReferenceFirstCollectionCorrectedFutureRetainedMoment.retainedGate_measurable rate rewards C_star C_h control0 u t q hfuture)
  have hWi : Integrable W mu := futureMultiplier_integrable rate rewards C_star C_h control0 u t q hfuture a
  have hWZi : Integrable (W * Z) mu :=
    futureMultiplier_product_integrable rate rewards C_star C_h control0 u t q hfuture a
  have hGi : Integrable (G.indicator (fun _ : X => (1 : ℝ))) mu :=
    (integrable_const _).indicator hG
  have hprod : (∫ x, W x * Z x ∂mu) ≤ ∫ x, W x ∂mu :=
    integral_predictable_mul_le control0 q W Z
      (futureMultiplier_predictable rate rewards C_star C_h control0 u t q hfuture a)
      hWi (exp_retainedIncrement_integrable rate rewards C_star C_h control0 u t q hfuture a)
      hWZi (fun x => (futureMultiplier_bounds rate rewards C_star C_h u t q a x).1)
      (condExp_exp_retainedIncrement_le_one rate rewards C_star C_h control0 u t q hfuture a)
  calc
    _ ≤ ∫ x, G.indicator (fun _ : X => (1 : ℝ)) x + W x * Z x - W x ∂mu :=
      integral_mono (integrable_energyIncrement rate rewards C_star C_h u t a q)
        ((hGi.add hWZi).sub hWi)
        (energyIncrement_le_future rate rewards C_star C_h u t q hfuture.le a)
    _ = (mu G).toReal + (∫ x, W x * Z x ∂mu) - ∫ x, W x ∂mu := by
      change Integrable (fun x => W x * Z x) mu at hWZi
      rw [integral_sub (f := fun x => G.indicator (fun _ : X => (1 : ℝ)) x + W x * Z x)
          (hGi.add hWZi) hWi,
        integral_add (f := G.indicator (fun _ : X => (1 : ℝ)))
          (g := fun x => W x * Z x) hGi hWZi,
        integral_indicator hG]
      simp only [setIntegral_const, smul_eq_mul, mul_one, measureReal_def]
    _ ≤ _ := by linarith only [hprod]


/-- The admitted immediate retained gate uses the actual inherited AFTER flag. -/
def nextGate (u t : Fin p.T) (hq : t.val + 1 < p.T) : Set X :=
  {x | x ∈ correctedCell rate rewards C_star C_h u t ∧
    (∃ o, ReferenceFirstCollectionCurrentQueueReadout.after?
      rate rewards C_star C_h t x = some o ∧ o.2.1 = false) ∧
    ∃ xi, nextParameters rate rewards C_star C_h t hq x = some (true, xi)}

/-- A present adjacent cell is either continuing or the retained chosen cutoff.
Consequently it belongs to the same actual numerical slice. -/
theorem nextCell_present_before_end (u t : Fin p.T) (hq : t.val + 1 < p.T)
    (x : X) (hx : x ∈ correctedCell rate rewards C_star C_h u t)
    (c : Input) (hc : nextCell rate rewards C_star C_h t hq x = some c) :
    t.val + 1 < endDate rate rewards C_star C_h t x := by
  obtain ⟨r0, r, _h0, h1, _ha0, har, _ht0, _ht1, _hstate, _hrows,
    _hj, _hrewards, _hchosen⟩ :=
    firstCell_successor_records rate rewards C_star C_h u t hq x hx.1
  change (sourceRecords rate rewards C_star C_h x)[birthIndex rate rewards C_star C_h x + 1]? =
    some r at h1
  have hcell : ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r = some c := by
    simpa only [nextCell, har, Option.bind_some] using hc
  have hread := firstCell_next_readouts rate rewards C_star C_h u t hq x hx.1 r har
  have hi := (List.getElem?_eq_some_iff.mp h1).1
  have hget := (List.getElem?_eq_some_iff.mp h1).2
  have hdrop : (sourceRecords rate rewards C_star C_h x).drop
      (birthIndex rate rewards C_star C_h x + 1) =
      r :: (sourceRecords rate rewards C_star C_h x).drop
        (birthIndex rate rewards C_star C_h x + 1 + 1) := by
    rw [List.drop_eq_getElem_cons hi, hget]
  have htail : liveTail rate rewards C_star C_h x =
      (r :: (sourceRecords rate rewards C_star C_h x).drop
        (birthIndex rate rewards C_star C_h x + 1 + 1)).takeWhile
          ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen := by
    unfold liveTail ReferenceFirstReplacementLiveFollowerPrefix.continuingTail
    rw [hdrop]
  cases hd : r.output.preparation.coordinator <;> simp only [hd] at hread
  all_goals try (rw [hread] at hcell; cases hcell)
  rename_i out
  cases out <;> simp only at hread
  all_goals try (rw [hread] at hcell; cases hcell)
  case continuingChosen =>
    have hlen : 0 < (liveTail rate rewards C_star C_h x).length := by
      have hf : ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen r = true := by
        simp only [ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen, hd]
      rw [htail, List.takeWhile_cons_of_pos hf, List.length_cons]
      omega
    unfold endDate
    omega
  case cutoffChosen =>
    have hlen : (liveTail rate rewards C_star C_h x).length = 0 := by
      have hf : ¬ ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen r = true := by
        simp only [ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen, hd,
          Bool.false_eq_true, not_false_eq_true]
      rw [htail, List.takeWhile_cons_of_neg hf]
      rfl
    have hdelta : cutoffDelta rate rewards C_star C_h x = 1 := by
      simp only [cutoffDelta, hlen, Nat.add_zero, h1, hd]
    unfold endDate
    omega

/-- Literal equality of the successor and open-slice retained gates. No end-date
predictability is assumed: presence of the actual cell proves activity. -/
theorem nextGate_eq_future (u t : Fin p.T) (hq : t.val + 1 < p.T) :
    nextGate rate rewards C_star C_h u t hq =
      retainedGate rate rewards C_star C_h u t ⟨t.val + 1, hq⟩ := by
  ext x
  have hafter (hx : x ∈ correctedCell rate rewards C_star C_h u t) :
      ReferenceFirstCollectionCurrentQueueReadout.after? rate rewards C_star C_h t x =
        prefixReadout rate rewards C_star C_h (t.val + 1) x := by
    rw [prefixReadout_eq_current rate rewards C_star C_h ⟨t.val + 1, hq⟩ x]
    exact firstCell_after_eq_successor_prefix rate rewards C_star C_h u t hq x hx.1
  constructor
  · rintro ⟨hx, ⟨o, ho, hf⟩, xi, hp⟩
    unfold nextParameters at hp
    obtain ⟨c, hc, he⟩ := Option.map_eq_some_iff.mp hp
    have hactive := nextCell_present_before_end rate rewards C_star C_h u t hq x hx c hc
    have hfg : x ∈ futureGate rate rewards C_star C_h u t ⟨t.val + 1, hq⟩ := ⟨hx, hactive⟩
    have hcell : futureCell rate rewards C_star C_h u t ⟨t.val + 1, hq⟩ x =
        nextCell rate rewards C_star C_h t hq x := by
      simp only [futureCell, ite_eq_left hfg, nextCell]
    refine ⟨⟨hfg, o, (hafter hx).symm.trans ho, hf⟩, xi, ?_⟩
    simpa only [futureParameters, hcell,
      nextParameters] using hp
  · rintro ⟨⟨hfg, o, ho, hf⟩, xi, hp⟩
    have hcell : futureCell rate rewards C_star C_h u t ⟨t.val + 1, hq⟩ x =
        nextCell rate rewards C_star C_h t hq x := by
      simp only [futureCell, ite_eq_left hfg, nextCell]
    refine ⟨hfg.1, ⟨o, (hafter hfg.1).trans ho, hf⟩, xi, ?_⟩
    simpa only [futureParameters, hcell,
      nextParameters] using hp


/-- The immediate incoming scalar is exactly the actual inherited AFTER birth
energy, by the admitted birth witness rather than a reset initial queue. -/
theorem birthEnergy_eq_current (u t : Fin p.T) (hq : t.val + 1 < p.T)
    (a : Fin p.K) (x : X)
    (hx : x ∈ correctedCell rate rewards C_star C_h u t) :
    stoppedEnergy rate rewards C_star C_h u t a (t.val + 1) x =
      currentEnergy rate rewards C_star C_h ⟨t.val + 1, hq⟩ a x := by
  obtain ⟨L, c, _hL, _hc, hinputs, henergy⟩ :=
    stoppedEnergy_birth_actual rate rewards C_star C_h u t a x hx
  rw [henergy, currentEnergy,
    ← prefixReadout_eq_current rate rewards C_star C_h ⟨t.val + 1, hq⟩ x]
  simp only [prefixReadout, hinputs, Option.map_some, Option.elim_some, stateReadout]

/-- Gating the birth identity uses N's actual AFTER event on both sides. -/
theorem nextMultiplier_eq_current (u t : Fin p.T) (hq : t.val + 1 < p.T)
    (a : Fin p.K) :
    futureMultiplier rate rewards C_star C_h u t ⟨t.val + 1, hq⟩ a =
      (nextGate rate rewards C_star C_h u t hq).indicator
        (currentEnergy rate rewards C_star C_h ⟨t.val + 1, hq⟩ a) := by
  funext x
  unfold futureMultiplier
  rw [← nextGate_eq_future rate rewards C_star C_h u t hq]
  by_cases hx : x ∈ nextGate rate rewards C_star C_h u t hq
  · simp only [Set.indicator_of_mem hx]
    exact birthEnergy_eq_current rate rewards C_star C_h u t hq a x hx.1
  · simp only [Set.indicator_of_notMem hx]

/-- The same gated energy is predictable at the immediate successor using the
admitted actual AFTER interface. -/
theorem nextMultiplier_predictable (control0 : TimeControl p) (u t : Fin p.T)
    (hq : t.val + 1 < p.T) (a : Fin p.K) :
    Measurable[sourcePrefixFiltration control0 (t.val + 2)]
      (futureMultiplier rate rewards C_star C_h u t ⟨t.val + 1, hq⟩ a) := by
  rw [nextMultiplier_eq_current rate rewards C_star C_h u t hq a]
  exact (currentEnergy_predictable rate rewards C_star C_h control0 ⟨t.val + 1, hq⟩ a).indicator
    (ReferenceFirstCollectionCorrectedNextRetainedGate.retainedGate_measurable rate rewards C_star C_h control0 u t hq)

/-- Actual scalar alignment with N's original-law optional successor increment. -/
theorem next_retainedIncrement_eq (u t : Fin p.T) (hq : t.val + 1 < p.T)
    (a : Fin p.K) :
    retainedIncrement rate rewards C_star C_h u t ⟨t.val + 1, hq⟩ a =
      successorIncrement rate rewards C_star C_h u t a := by
  funext x
  have hgate := nextGate_eq_future rate rewards C_star C_h u t hq
  by_cases hg : x ∈ nextGate rate rewards C_star C_h u t hq
  · have hgm : x ∈ retainedGate rate rewards C_star C_h u t ⟨t.val + 1, hq⟩ := by
      rwa [← hgate]
    obtain ⟨L, hpast, hafter, hf⟩ := retained_successor_queue_witness
      rate rewards C_star C_h u t hq x hg
    have hL : prefixInputs rate rewards C_star C_h (t.val + 1) x = some L := by
      rw [prefixInputs_eq_pastCells rate rewards C_star C_h ⟨t.val + 1, hq⟩ x]
      exact hpast
    obtain ⟨xi, hp⟩ := hg.2.2
    unfold nextParameters at hp
    obtain ⟨c, hc, he⟩ := Option.map_eq_some_iff.mp hp
    have henabled : c.enabled = true := congrArg Prod.fst he
    have hcell : futureCell rate rewards C_star C_h u t ⟨t.val + 1, hq⟩ x = some c := by
      simpa only [futureCell, ite_eq_left hgm.1.1, nextCell] using hc
    have hnext : successorIncrement
        rate rewards C_star C_h u t a x =
        nextArrival rate rewards C_star C_h t hq a x - 4 := by
      unfold successorIncrement
      rw [dite_eq_left hq]
      exact retainedIncrement_eq_on_gate
        rate rewards C_star C_h u t hq a x hg
    rw [hnext]
    simp only [retainedIncrement,
      Set.indicator_of_mem hgm, futureArrival,
      hL, hcell, nextArrival, hc]
    rw [RecordedRoundMoments.rawEstimate_eq_normalizedQuantizedArrival_of_enabled Q _ c a henabled hf]
  · have hgm : x ∉ retainedGate
        rate rewards C_star C_h u t ⟨t.val + 1, hq⟩ := by
      rwa [← hgate]
    rw [retainedIncrement_off_gate
      rate rewards C_star C_h u t ⟨t.val + 1, hq⟩ a x hgm]
    unfold successorIncrement
    rw [dite_eq_left hq]
    exact (retainedIncrement_of_not_mem
      rate rewards C_star C_h u t hq a x hg).symm

/-- Immediate-successor energy iteration with no supplied moment or birth bound. -/
theorem integral_energyIncrement_le_next_gate (control0 : TimeControl p)
    (u t : Fin p.T) (hq : t.val + 1 < p.T) (a : Fin p.K) :
    (∫ x, energyIncrement rate rewards C_star C_h u t a ⟨t.val + 1, hq⟩ x ∂mu) ≤
      (mu (nextGate rate rewards C_star C_h u t hq)).toReal := by
  let q : Fin p.T := ⟨t.val + 1, hq⟩
  let W := futureMultiplier rate rewards C_star C_h u t q a
  let Z : X → ℝ := fun x => Real.exp (beta * successorIncrement rate rewards C_star C_h u t a x)
  let G := nextGate rate rewards C_star C_h u t hq
  have hG : MeasurableSet G := ((sourcePrefixFiltration control0).le' (t.val + 2)) _
    (ReferenceFirstCollectionCorrectedNextRetainedGate.retainedGate_measurable rate rewards C_star C_h control0 u t hq)
  have hW : Measurable[sourcePrefixFiltration control0 (q.val + 1)] W :=
    nextMultiplier_predictable rate rewards C_star C_h control0 u t hq a
  have hWi : Integrable W mu := by
    change Integrable ((retainedGate rate rewards C_star C_h u t q).indicator
      (stoppedEnergy rate rewards C_star C_h u t a q.val)) mu
    rw [← nextGate_eq_future rate rewards C_star C_h u t hq]
    exact (integrable_stoppedEnergy rate rewards C_star C_h u t a q.val).indicator hG
  have hZi : Integrable Z mu :=
    exp_successorIncrement_integrable rate rewards C_star C_h u t control0 a
  have hWZi : Integrable (fun x => W x * Z x) mu := by
    apply hZi.bdd_mul hWi.aestronglyMeasurable
    filter_upwards [] with x
    have hb := futureMultiplier_bounds rate rewards C_star C_h u t q a x
    simpa only [W, Real.norm_eq_abs, abs_of_nonneg hb.1] using hb.2
  have hprod : (∫ x, W x * Z x ∂mu) ≤ ∫ x, W x ∂mu :=
    integral_predictable_mul_le control0 q W Z hW hWi hZi hWZi
      (fun x => (futureMultiplier_bounds rate rewards C_star C_h u t q a x).1)
      (condExp_exp_successorIncrement_le_one rate rewards C_star C_h u t control0 a)
  have hGi : Integrable (G.indicator (fun _ : X => (1 : ℝ))) mu :=
    (integrable_const _).indicator hG
  have hpoint : energyIncrement rate rewards C_star C_h u t a q ≤
      (fun x => G.indicator (fun _ : X => (1 : ℝ)) x + W x * Z x - W x) := by
    intro x
    have h := energyIncrement_le_future rate rewards C_star C_h u t q le_rfl a x
    simpa only [q, ← nextGate_eq_future rate rewards C_star C_h u t hq,
      next_retainedIncrement_eq rate rewards C_star C_h u t hq a] using h
  calc
    _ ≤ ∫ x, G.indicator (fun _ : X => (1 : ℝ)) x + W x * Z x - W x ∂mu :=
      integral_mono (integrable_energyIncrement rate rewards C_star C_h u t a q)
        ((hGi.add hWZi).sub hWi) hpoint
    _ = (mu G).toReal + (∫ x, W x * Z x ∂mu) - ∫ x, W x ∂mu := by
      rw [integral_sub (f := fun x => G.indicator (fun _ : X => (1 : ℝ)) x + W x * Z x)
          (hGi.add hWZi) hWi,
        integral_add (f := G.indicator (fun _ : X => (1 : ℝ)))
          (g := fun x => W x * Z x) hGi hWZi, integral_indicator hG]
      simp only [setIntegral_const, smul_eq_mul, mul_one, measureReal_def]
    _ ≤ _ := by linarith only [hprod]

/-- The actual endpoint characterization is a Borel energy threshold, including
birth overflow and the first retained detecting update. -/
theorem overflowEvent_eq_terminal_threshold (u t : Fin p.T) (a : Fin p.K) :
    overflowEvent rate rewards C_star C_h u t a =
      {x | Real.exp (beta / (32 * rate.eta.val)) <
        stoppedEnergy rate rewards C_star C_h u t a p.T x} := by
  ext x
  constructor
  · intro hx
    obtain ⟨hc, _⟩ := (overflowEvent_iff_endpoint rate rewards C_star C_h u t a x).mp hx
    obtain ⟨o, ho, hcap⟩ := endpoint_exp_gt_cap rate rewards C_star C_h u t a x hx
    obtain ⟨L, _hL, hread, henergy⟩ := stoppedEnergy_terminal_actual rate rewards C_star C_h u t a x hc
    have he : o = stateReadout (RecordedQueueRun.run Q L) := Option.some.inj (ho.symm.trans hread)
    change Real.exp (beta / (32 * rate.eta.val)) < _
    rw [henergy]
    simpa only [he, stateReadout, mul_div_assoc] using hcap
  · intro hx
    change Real.exp (beta / (32 * rate.eta.val)) <
      stoppedEnergy
        rate rewards C_star C_h u t a p.T x at hx
    have hc : x ∈ correctedCell rate rewards C_star C_h u t := by
      by_contra hn
      rw [stoppedEnergy_off_cell rate rewards C_star C_h u t a p.T x hn] at hx
      exact (not_lt_of_ge (Real.exp_pos _).le) hx
    obtain ⟨L, _hL, hread, henergy⟩ := stoppedEnergy_terminal_actual rate rewards C_star C_h u t a x hc
    apply (overflowEvent_iff_endpoint rate rewards C_star C_h u t a x).mpr
    refine ⟨hc, stateReadout (RecordedQueueRun.run Q L), hread, ?_⟩
    rw [henergy] at hx
    have hlt := Real.exp_lt_exp.mp hx
    change 1 / (32 * rate.eta.val) < (((RecordedQueueRun.run Q L).registers a).2 : ℝ) / ((Q).n : ℝ)
    apply (mul_lt_mul_iff_right₀ (CanonicalRecordingRates.beta_pos p rate.eta.property)).mp
    simpa only [mul_one_div, ← mul_div_assoc, mul_one] using hlt

theorem measurableSet_overflowEvent (u t : Fin p.T) (a : Fin p.K) :
    MeasurableSet (overflowEvent rate rewards C_star C_h u t a) := by
  rw [overflowEvent_eq_terminal_threshold rate rewards C_star C_h u t a]
  exact measurableSet_lt measurable_const
    (measurable_stoppedEnergy rate rewards C_star C_h u t a p.T)

/-- Original-mu Markov cover before the energy iteration is substituted. -/
theorem overflowEvent_measure_le_terminal (u t : Fin p.T) (a : Fin p.K) :
    (mu (overflowEvent rate rewards C_star C_h u t a)).toReal ≤
      Real.exp (-beta / (32 * rate.eta.val)) *
        ∫ x, stoppedEnergy rate rewards C_star C_h u t a p.T x ∂mu := by
  let A := overflowEvent rate rewards C_star C_h u t a
  let cap := Real.exp (beta / (32 * rate.eta.val))
  have hA : MeasurableSet A := measurableSet_overflowEvent rate rewards C_star C_h u t a
  have hpoint : A.indicator (fun _ : X => cap) ≤
      stoppedEnergy rate rewards C_star C_h u t a p.T := by
    intro x
    by_cases hx : x ∈ A
    · rw [Set.indicator_of_mem hx]
      exact le_of_lt (by
        have he := overflowEvent_eq_terminal_threshold rate rewards C_star C_h u t a
        change x ∈ overflowEvent
          rate rewards C_star C_h u t a at hx
        rw [he] at hx
        exact hx)
    · rw [Set.indicator_of_notMem hx]
      exact (stoppedEnergy_bounds rate rewards C_star C_h u t a p.T x).1
  have hint := integral_mono ((integrable_const cap).indicator hA)
    (integrable_stoppedEnergy rate rewards C_star C_h u t a p.T) hpoint
  have hmass : cap * (mu A).toReal ≤
      ∫ x, stoppedEnergy rate rewards C_star C_h u t a p.T x ∂mu := by
    simpa only [integral_indicator hA, setIntegral_const, smul_eq_mul, measureReal_def,
      mul_comm] using hint
  have hcap : 0 < cap := Real.exp_pos _
  have hinv : Real.exp (-beta / (32 * rate.eta.val)) = cap⁻¹ := by
    rw [neg_div, Real.exp_neg]
  rw [hinv]
  exact (le_inv_mul_iff₀ hcap).mpr hmass

/-- Each actual calendar increment costs at most the original corrected-cell
mass. Before birth there is no action; the immediate date consumes N and every
strict-future date consumes ReferenceFirstCollectionCorrectedFutureRetainedMoment. -/
theorem integral_energyIncrement_le_cell (control0 : TimeControl p)
    (u t : Fin p.T) (a : Fin p.K) (q : Fin p.T) :
    (∫ x, energyIncrement rate rewards C_star C_h u t a q x ∂mu) ≤
      (mu (correctedCell rate rewards C_star C_h u t)).toReal := by
  by_cases hbefore : q.val < t.val + 1
  · have hz : energyIncrement rate rewards C_star C_h u t a q = (fun _ => 0) := by
      funext x
      exact energyIncrement_eq_zero rate rewards C_star C_h u t a q x (Or.inl hbefore)
    rw [hz, integral_zero]
    exact ENNReal.toReal_nonneg
  · by_cases heq : q.val = t.val + 1
    · have hq : t.val + 1 < p.T := by omega
      have hqeq : q = ⟨t.val + 1, hq⟩ := Fin.ext heq
      rw [hqeq]
      apply (integral_energyIncrement_le_next_gate rate rewards C_star C_h control0 u t hq a).trans
      exact ENNReal.toReal_mono (measure_ne_top mu _)
        (measure_mono (fun x hx => hx.1))
    · have hfuture : t.val + 1 < q.val := by omega
      apply (integral_energyIncrement_le_future_gate rate rewards C_star C_h control0 u t q hfuture a).trans
      exact ENNReal.toReal_mono (measure_ne_top mu _)
        (measure_mono (fun x hx => hx.1.1.1))

/-- Iteration of the admitted exact telescope retains its actual inherited
birth energy, which need not be at most one. -/
theorem integral_terminal_stoppedEnergy_le (control0 : TimeControl p)
    (u t : Fin p.T) (a : Fin p.K) :
    (∫ x, stoppedEnergy rate rewards C_star C_h u t a p.T x ∂mu) ≤
      (∫ x, stoppedEnergy rate rewards C_star C_h u t a (t.val + 1) x ∂mu) +
        (p.T : ℝ) * (mu (correctedCell rate rewards C_star C_h u t)).toReal := by
  rw [integral_stoppedEnergy_telescope rate rewards C_star C_h u t a]
  apply add_le_add (le_refl _)
  calc
    _ ≤ ∑ _q : Fin p.T, (mu (correctedCell rate rewards C_star C_h u t)).toReal :=
      Finset.sum_le_sum (fun q _ =>
        integral_energyIncrement_le_cell rate rewards C_star C_h control0 u t a q)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- Original-source arm-overflow Markov estimate on the same corrected slice.
The only energy input on the right is the actual inherited birth observation.
Global birth sums and physical/logical coupling remain separate obligations. -/
theorem overflowEvent_measure_le (control0 : TimeControl p)
    (u t : Fin p.T) (a : Fin p.K) :
    (mu (overflowEvent rate rewards C_star C_h u t a)).toReal ≤
      Real.exp (-beta / (32 * rate.eta.val)) *
        ((∫ x, stoppedEnergy rate rewards C_star C_h u t a (t.val + 1) x ∂mu) +
          (p.T : ℝ) * (mu (correctedCell rate rewards C_star C_h u t)).toReal) := by
  exact (overflowEvent_measure_le_terminal rate rewards C_star C_h u t a).trans
    (mul_le_mul_of_nonneg_left
      (integral_terminal_stoppedEnergy_le rate rewards C_star C_h control0 u t a)
      (Real.exp_nonneg _))

end Bandits.Support.ReferenceFirstCollectionCorrectedOriginalSourceOverflow
end
