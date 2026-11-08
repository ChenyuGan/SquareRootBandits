/-
Copyright (c) 2026 The Bandits Lean regret formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveAllArmAcceptedConditionalMoments
public import Bandits.Support.RecordedWeightedDrift

import Mathlib.Tactic

/-!
# First-live adapted queue energy and its pointwise drift envelope

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:140-188,245-318`,
`sources/zip4/manuscript/06_interruptions.tex:391-408,425-426`, and
`sources/zip4/manuscript/07_public_setup.tex:127-164`.

This module reuses the accepted all-arm conditional-moment telescope and the
actual chronological queue. It identifies the strict-past register readout on
the same unnormalized branch measure and explicit prefix field, derives every
cell's canonical rate floor, and proves the weighted quadratic envelope before
any conditional integration. It does not compare the actual anchor-rate sum
with `R`, identify the field with manuscript `F_t`, or close a manuscript
queue or regret assertion.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators Classical

namespace Bandits.Support.ReferenceFirstLiveQueueEnergyEnvelope

abbrev Parameters := ReferenceFirstLiveAllArmAcceptedConditionalMoments.Parameters
abbrev RateInput := ReferenceFirstLiveAllArmAcceptedConditionalMoments.RateInput
abbrev RewardTable := ReferenceFirstLiveAllArmAcceptedConditionalMoments.RewardTable
abbrev TimeControl := ReferenceFirstLiveAllArmAcceptedConditionalMoments.TimeControl

variable {p : Parameters} (rate : RateInput p) (rewards : RewardTable p)
  (C_star C_h : ℝ) (q : Fin (ConstructorDimensions.M p)) (t : Fin p.T)
  (s : ℕ) (hs : s ≤ t.val) (control0 : TimeControl p)

local notation "Zplus" =>
  ReferenceFirstLiveRecordingSourceCylinder.SourcePlus
    rate rewards C_star C_h q t s hs control0
local notation "muPlus" =>
  ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure
    rate rewards C_star C_h q t s hs control0
local notation "Fplus" =>
  ReferenceFirstLiveAllArmPrefixAdaptation.sourcePlusPrefixField
    rate rewards C_star C_h q t s hs control0
local notation "G" =>
  ReferenceFirstLiveAllArmPrefixAdaptation.strictPastOverflowFalseSet
    rate rewards C_star C_h q t s hs control0
local notation "n" => t.val - s
local notation "cells" =>
  ReferenceFirstLiveSourceCellReadout.cells rate rewards C_star C_h q t s hs control0
local notation "cell" =>
  ReferenceFirstLiveSourceCellReadout.cell rate rewards C_star C_h q t s hs control0
local notation "queue" => ReferenceFirstLaunchNumericalCell.queueParameters rate
local notation "past" => fun z : Zplus =>
  RecordedQueueRun.run queue (List.take n (cells z))
local notation "post" => fun z : Zplus =>
  RecordedQueueRun.run queue (List.take (n + 1) (cells z))
local notation "scale" => rate.eta.val * (ConstructorDimensions.D p : ℝ)
local notation "Bcap" => 1 / (32 * rate.eta.val)

/-- The actual inclusion marginal before the current source cell. -/
def thetaBefore (j : Fin p.K) (z : Zplus) : ℝ :=
  ProductSetLaw.theta p.m (RecordedQueueRun.scoreWeight queue (past z)) j

/-- The actual inclusion marginal after the current source cell. -/
def thetaAfter (j : Fin p.K) (z : Zplus) : ℝ :=
  ProductSetLaw.theta p.m (RecordedQueueRun.scoreWeight queue (post z)) j

/-- The actual weighted-square queue potential on the strict past. -/
def potentialBefore (z : Zplus) : ℝ :=
  RecordedWeightedDrift.weightedSquarePotential p.m queue (past z)

/-- The actual weighted-square queue potential after the current cell. -/
def potentialAfter (z : Zplus) : ℝ :=
  RecordedWeightedDrift.weightedSquarePotential p.m queue (post z)

/-- The source weighted backlog at the strict-past queue state. -/
def weightedBacklogBefore (z : Zplus) : ℝ :=
  RecordedWeightedDrift.weightedBacklog p.m queue (past z)

/-- The strict-past run is exactly the register/overflow/record readout
already exposed by A. The comparison uses the accepted `n+1`-to-`n` source
cell prefix theorem, including the source-stratum proof identifications. -/
theorem numericalCountRunReadoutPlus_eq_past (z : Zplus) :
    ReferenceFirstLiveAllArmPrefixAdaptation.numericalCountRunReadoutPlus
      rate rewards C_star C_h q t s hs control0 z =
      ((past z).registers, ((past z).overflow, (past z).records)) := by
  have hrun := ReferenceFirstLiveNumericalPrefixTemporal.numerical_run_count_eq
    rate rewards C_star C_h q t s hs control0 z.val
  have hstate :
      RecordedQueueRun.run queue (List.take n (cells z)) =
        RecordedQueueRun.run queue
          (ReferenceFirstWindowNumericalStream.actualLiveSourceCells rate z.val.val
            rewards C_star C_h z.val.property.2.1 n (by
              have hz := ReferenceFirstLiveNumericalPrefixTemporal.sourceStratum_facts
                rate rewards C_star C_h q t s hs z.val
              rw [hz.2.2]
              omega)) := by
    simpa only [ReferenceFirstLiveSourceCellReadout.cells,
      ReferenceFirstLiveSourceCellReadout.sourceCurrentCount] using hrun
  have hreadout := congrArg
    (fun state : RecordedQueueRun.RunState p.K =>
      (state.registers, (state.overflow, state.records))) hstate
  simpa only [ReferenceFirstLiveAllArmPrefixAdaptation.numericalCountRunReadoutPlus,
    ReferenceFirstLiveNumericalQueueBorel.numericalCountRunReadout,
    ReferenceFirstLiveSourceCellReadout.cells,
    ReferenceFirstLiveSourceCellReadout.sourceCurrentCount] using hreadout.symm

/-- The `.1` register component of the actual strict-past readout is the
literal `past` run's register vector. -/
theorem numericalCountRunReadoutPlus_registers (z : Zplus) :
    (ReferenceFirstLiveAllArmPrefixAdaptation.numericalCountRunReadoutPlus
      rate rewards C_star C_h q t s hs control0 z).1 = (past z).registers := by
  exact congrArg Prod.fst
    (numericalCountRunReadoutPlus_eq_past rate rewards C_star C_h q t s hs control0 z)

/-- The existing strict-past readout remains measurable on A's exact
current-control comap field. -/
theorem measurable_numericalCountRunReadoutPlus :
    Measurable[Fplus]
      (ReferenceFirstLiveAllArmPrefixAdaptation.numericalCountRunReadoutPlus
        rate rewards C_star C_h q t s hs control0) :=
  ReferenceFirstLiveAllArmPrefixAdaptation.measurable_numericalCountRunReadoutPlus
    rate rewards C_star C_h q t s hs control0

/-- The run's register vector is a genuinely countable-valued readout. -/
theorem measurable_pastRegisterReadout :
    Measurable[Fplus] (fun z : Zplus => (past z).registers) := by
  have h := measurable_fst.comp
    (measurable_numericalCountRunReadoutPlus rate rewards C_star C_h q t s hs control0)
  have heq :
      (fun z : Zplus =>
        (ReferenceFirstLiveAllArmPrefixAdaptation.numericalCountRunReadoutPlus
          rate rewards C_star C_h q t s hs control0 z).1) =
        (fun z : Zplus => (past z).registers) := by
    funext z
    exact numericalCountRunReadoutPlus_registers rate rewards C_star C_h q t s hs control0 z
  rw [← heq]
  exact h

/-- Each past score coordinate is measurable as a natural-number readout. -/
theorem measurable_pastScore (j : Fin p.K) :
    Measurable[Fplus] (fun z : Zplus => ((past z).registers j).1) := by
  exact measurable_fst.comp
    ((measurable_pi_apply j).comp
      (measurable_pastRegisterReadout rate rewards C_star C_h q t s hs control0))

/-- Each past natural backlog coordinate is measurable on the exact prefix
field, with its countable register carrier left intact. -/
theorem measurable_pastBacklogRegister (j : Fin p.K) :
    Measurable[Fplus] (fun z : Zplus => ((past z).registers j).2) := by
  exact measurable_snd.comp
    ((measurable_pi_apply j).comp
      (measurable_pastRegisterReadout rate rewards C_star C_h q t s hs control0))

/-- Each normalized strict-past backlog is measurable on `Fplus`. -/
theorem measurable_backlogBefore (j : Fin p.K) :
    Measurable[Fplus]
      (fun z : Zplus =>
        ReferenceFirstLiveAllArmAcceptedConditionalMoments.backlogBefore
          rate rewards C_star C_h q t s hs control0 j z) := by
  have hcast : Measurable[Fplus]
      (fun z : Zplus => (((past z).registers j).2 : ℝ)) :=
    (measurable_of_countable _).comp
      (measurable_pastBacklogRegister rate rewards C_star C_h q t s hs control0 j)
  have hfun :
      (fun z : Zplus => (((past z).registers j).2 : ℝ) / scale) =
        (fun z : Zplus =>
          ReferenceFirstLiveAllArmAcceptedConditionalMoments.backlogBefore
            rate rewards C_star C_h q t s hs control0 j z) := rfl
  rw [← hfun]
  exact hcast.div_const scale

/-- The exact source scale is the queue's integer `n` cast to the reals.
This is the existing source identity `n = eta * D`, not a new premise. -/
theorem queue_scale_eq : (rate.n : ℝ) = scale := by
  exact rate.n_scale

/-- M's normalized backlog is exactly the queue potential's integer
normalization, by the accepted source identity `n = eta * D`. -/
theorem backlogBefore_eq_normalized (j : Fin p.K) (z : Zplus) :
    ReferenceFirstLiveAllArmAcceptedConditionalMoments.backlogBefore
      rate rewards C_star C_h q t s hs control0 j z =
      StoppedQueueBound.normalizedBacklog queue (past z) j := by
  change (((past z).registers j).2 : ℝ) / scale =
    (((past z).registers j).2 : ℝ) / (rate.n : ℝ)
  rw [rate.n_scale]

/-- The same exact normalization identity holds after the actual current
successor, including its first overflow crossing. -/
theorem backlogAfter_eq_normalized (j : Fin p.K) (z : Zplus) :
    ReferenceFirstLiveAllArmAcceptedConditionalMoments.backlogAfter
      rate rewards C_star C_h q t s hs control0 j z =
      StoppedQueueBound.normalizedBacklog queue (post z) j := by
  change (((post z).registers j).2 : ℝ) / scale =
    (((post z).registers j).2 : ℝ) / (rate.n : ℝ)
  rw [rate.n_scale]

/-- The queue potential's normalization of the strict-past register is
measurable on the same explicit prefix field. -/
theorem measurable_normalizedBacklogBefore (j : Fin p.K) :
    Measurable[Fplus]
      (fun z : Zplus => StoppedQueueBound.normalizedBacklog queue (past z) j) := by
  have h := measurable_backlogBefore rate rewards C_star C_h q t s hs control0 j
  have heq :
      (fun z : Zplus =>
        ReferenceFirstLiveAllArmAcceptedConditionalMoments.backlogBefore
          rate rewards C_star C_h q t s hs control0 j z) =
      (fun z : Zplus => StoppedQueueBound.normalizedBacklog queue (past z) j) := by
    funext z
    exact backlogBefore_eq_normalized rate rewards C_star C_h q t s hs control0 j z
  rw [← heq]
  exact h

/-- The rate input's source-cap field implies the small-rate bound used by
the accepted one-step marginal-growth lemma. -/
theorem eta_le_one_div_sixtyFour : rate.eta.val ≤ 1 / 64 := by
  exact RecordedWeightedDrift.eta_le_one_div_sixtyFour p
    (ReferenceFirstLaunchNumericalCell.queueParameters rate) rate.sourceCap

/-- Every cell in the actual complete `C.cells z` list has the canonical
recording-rate lower bound. Each list element is read from its actual selected
cell payload; no rate family is supplied to this theorem. -/
theorem cells_rate_lower_bound (z : Zplus) :
    ∀ round ∈ cells z, ∀ j : Fin p.K, 32 * rate.eta.val ≤ round.rate j := by
  intro round hround j
  obtain ⟨k, hk, hget⟩ := List.mem_iff_getElem.mp hround
  have hkWindow : k < (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
      rate z.val.val rewards C_star C_h z.val.property.2.1
      (ReferenceFirstLiveSourceCellReadout.sourceCurrentCount t s)
      (ReferenceFirstLiveSourceCellReadout.source_current_span
        rate rewards C_star C_h q t s hs control0 z)).length := by
    have hklen : k < (cells z).length := hk
    have hkcount : k < ReferenceFirstLiveSourceCellReadout.sourceCurrentCount t s := by
      rw [ReferenceFirstLiveSourceCellReadout.cells_length] at hklen
      exact hklen
    have hwinlen :
        (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow rate z.val.val rewards C_star C_h
          z.val.property.2.1 (ReferenceFirstLiveSourceCellReadout.sourceCurrentCount t s)
          (ReferenceFirstLiveSourceCellReadout.source_current_span
            rate rewards C_star C_h q t s hs control0 z)).length =
          ReferenceFirstLiveSourceCellReadout.sourceCurrentCount t s := by
      simpa only [ReferenceFirstLiveSourceCellReadout.sourceCurrentWindow] using
        ReferenceFirstLiveSourceCellReadout.source_current_window_length
          rate rewards C_star C_h q t s hs control0 z
    rw [hwinlen]
    exact hkcount
  let sourceCell := ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
    rate z.val.val rewards C_star C_h z.val.property.2.1
    (ReferenceFirstLiveSourceCellReadout.sourceCurrentCount t s)
    (ReferenceFirstLiveSourceCellReadout.source_current_span
      rate rewards C_star C_h q t s hs control0 z) ⟨k, hkWindow⟩
  have hinput : round = sourceCell.input := by
    dsimp only [sourceCell]
    simpa only [ReferenceFirstLiveSourceCellReadout.cells,
      ReferenceFirstWindowNumericalStream.actualLiveSourceCells,
      ReferenceFirstLiveSourceCellReadout.sourceCurrentCount,
      List.getElem_ofFn] using hget.symm
  rw [hinput]
  change 32 * rate.eta.val ≤ sourceCell.input.rate j
  have hfacts := ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt_facts
    rate z.val.val rewards C_star C_h z.val.property.2.1
    (ReferenceFirstLiveSourceCellReadout.sourceCurrentCount t s)
    (ReferenceFirstLiveSourceCellReadout.source_current_span
      rate rewards C_star C_h q t s hs control0 z)
    ⟨k, hkWindow⟩
  dsimp only at hfacts
  rcases hfacts with ⟨_, _, _, _, _, _, hrate, _, _⟩
  rw [hrate, sourceCell.selected.view.payload.rate_eq_canonical]
  exact CanonicalRecordingRates.thirtyTwo_mul_eta_le_xi p rate.eta.property
    sourceCell.selected.view.payload.anchor j

/-- All actual strict-past and successor prefixes meet the exact rate
hypothesis required by `StoppedQueueBound`. -/
theorem cells_prefix_rate_lower_bound (z : Zplus) :
    ∀ round ∈ cells z, ∀ j : Fin p.K, 32 * rate.eta.val ≤ round.rate j := by
  intro round hround j
  have h := cells_rate_lower_bound rate rewards C_star C_h q t s hs control0 z
    round hround j
  exact h

/-- The actual strict-past overflow event is A's literal no-overflow test on
the first `n` entries of the `n+1` complete source-cell list. -/
theorem mem_G_iff_past_not_overflow (z : Zplus) :
    z ∈ G ↔ (past z).overflow = false := by
  rfl

/-- Every normalized backlog in the actual queue states is nonnegative. -/
theorem backlogBefore_nonneg (j : Fin p.K) (z : Zplus) :
    0 ≤ ReferenceFirstLiveAllArmAcceptedConditionalMoments.backlogBefore
      rate rewards C_star C_h q t s hs control0 j z := by
  unfold ReferenceFirstLiveAllArmAcceptedConditionalMoments.backlogBefore
  exact div_nonneg (Nat.cast_nonneg _) (le_of_lt
    (ReferenceFirstLiveAllArmAcceptedConditionalMoments.scale_pos rate))

/-- Every actual normalized successor backlog, including the inclusive first
overflow update, is nonnegative. -/
theorem backlogAfter_nonneg (j : Fin p.K) (z : Zplus) :
    0 ≤ ReferenceFirstLiveAllArmAcceptedConditionalMoments.backlogAfter
      rate rewards C_star C_h q t s hs control0 j z := by
  unfold ReferenceFirstLiveAllArmAcceptedConditionalMoments.backlogAfter
  exact div_nonneg (Nat.cast_nonneg _) (le_of_lt
    (ReferenceFirstLiveAllArmAcceptedConditionalMoments.scale_pos rate))

/-- The strict-past backlog is at most `Bcap` on the literal retained set. -/
theorem backlogBefore_le_Bcap_of_mem_G (j : Fin p.K) (z : Zplus)
    (hz : z ∈ G) :
    ReferenceFirstLiveAllArmAcceptedConditionalMoments.backlogBefore
      rate rewards C_star C_h q t s hs control0 j z ≤ Bcap := by
  have hfalse := (mem_G_iff_past_not_overflow rate rewards C_star C_h q t s hs control0 z).mp hz
  have h := StoppedQueueBound.run_prefix_normalized_backlog_le_threshold_of_overflow_false
    queue (cells z) n j hfalse
  rw [backlogBefore_eq_normalized rate rewards C_star C_h q t s hs control0 j z]
  simpa [ReferenceFirstLaunchNumericalCell.queueParameters] using h

/-- The inclusive current successor, including a first crossing, is bounded
by `2 * Bcap` on every source point. -/
theorem backlogAfter_le_two_Bcap (j : Fin p.K) (z : Zplus) :
    ReferenceFirstLiveAllArmAcceptedConditionalMoments.backlogAfter
      rate rewards C_star C_h q t s hs control0 j z ≤ 2 * Bcap := by
  have h := StoppedQueueBound.run_prefix_normalized_backlog_le_twice_threshold
    queue (cells z) (cells_prefix_rate_lower_bound rate rewards C_star C_h q t s hs control0 z)
    (n + 1) j
  rw [backlogAfter_eq_normalized rate rewards C_star C_h q t s hs control0 j z]
  simpa [ReferenceFirstLaunchNumericalCell.queueParameters] using h

/-- The strict-past state is bounded by `2 * Bcap` everywhere, whether or
not the retained event holds. -/
theorem backlogBefore_le_two_Bcap (j : Fin p.K) (z : Zplus) :
    ReferenceFirstLiveAllArmAcceptedConditionalMoments.backlogBefore
      rate rewards C_star C_h q t s hs control0 j z ≤ 2 * Bcap := by
  have h := StoppedQueueBound.run_prefix_normalized_backlog_le_twice_threshold
    queue (cells z) (cells_prefix_rate_lower_bound rate rewards C_star C_h q t s hs control0 z)
    n j
  rw [backlogBefore_eq_normalized rate rewards C_star C_h q t s hs control0 j z]
  simpa [ReferenceFirstLaunchNumericalCell.queueParameters] using h

/-- The after-backlog is exactly the actual current enabled update on `G`,
and the stopped register is unchanged off `G`. -/
theorem backlogAfter_eq_actual_update (j : Fin p.K) (z : Zplus) :
    ReferenceFirstLiveAllArmAcceptedConditionalMoments.backlogAfter
      rate rewards C_star C_h q t s hs control0 j z =
      if z ∈ G then
        max 0 (ReferenceFirstLiveAllArmAcceptedConditionalMoments.backlogBefore
          rate rewards C_star C_h q t s hs control0 j z +
          ReferenceFirstLiveAllArmAcceptedConditionalMoments.acceptedA
            rate rewards C_star C_h q t s hs control0 j z - 4)
      else ReferenceFirstLiveAllArmAcceptedConditionalMoments.backlogBefore
        rate rewards C_star C_h q t s hs control0 j z := by
  by_cases hz : z ∈ G
  · rw [ite_eq_left hz]
    exact (ReferenceFirstLiveAllArmAcceptedConditionalMoments.backlogAfter_eq_max_on_G
      rate rewards C_star C_h q t s hs control0 j z hz).trans (by
        exact max_comm _ _)
  · rw [ite_eq_right hz]
    exact (ReferenceFirstLiveAllArmAcceptedConditionalMoments.stopped_queue_noop_off_G
      rate rewards C_star C_h q t s hs control0 j z hz).2.2.1

/-- The strict-past queue's canonical weight vector is a countable-valued
readout of the existing finite product of natural registers. -/
theorem measurable_thetaBefore (j : Fin p.K) :
    Measurable[Fplus] (thetaBefore rate rewards C_star C_h q t s hs control0 j) := by
  let phi : (Fin p.K → ℕ × ℕ) → ℝ := fun registers =>
    ProductSetLaw.theta p.m
      (fun i => ScoreWeights.scoreWeight
        (1 + 1 / (ConstructorDimensions.D p : ℝ)) (registers i).1) j
  have hphi : Measurable phi := measurable_of_countable _
  have hreadout := measurable_fst.comp
    (measurable_numericalCountRunReadoutPlus rate rewards C_star C_h q t s hs control0)
  have hfun : thetaBefore rate rewards C_star C_h q t s hs control0 j =
      fun z => phi ((ReferenceFirstLiveAllArmPrefixAdaptation.numericalCountRunReadoutPlus
        rate rewards C_star C_h q t s hs control0 z).1) := by
    funext z
    rw [numericalCountRunReadoutPlus_registers rate rewards C_star C_h q t s hs control0 z]
    change ProductSetLaw.theta p.m (RecordedQueueRun.scoreWeight queue (past z)) j =
      ProductSetLaw.theta p.m
        (fun i => ScoreWeights.scoreWeight
          (1 + 1 / (ConstructorDimensions.D p : ℝ)) ((past z).registers i).1) j
    rfl
  rw [hfun]
  exact hphi.comp hreadout

/-- Every actual inclusion coefficient lies in `[0,1]`. -/
theorem thetaBefore_bounds (j : Fin p.K) (z : Zplus) :
    0 ≤ thetaBefore rate rewards C_star C_h q t s hs control0 j z ∧
      thetaBefore rate rewards C_star C_h q t s hs control0 j z ≤ 1 := by
  have hpos := RecordedMarginalGrowth.state_theta_pos queue (past z) j
    (ConstructorDimensions.m_pos p) p.m_lt_K
  have hlt := ProductSetLaw.theta_lt_one
    (RecordedQueueRun.scoreWeight queue (past z)) j
    (ConstructorDimensions.m_pos p) p.m_lt_K
    (RecordedMarginalGrowth.state_scoreWeight_pos queue (past z))
  exact ⟨hpos.le, hlt.le⟩

/-- Every after-update inclusion coefficient lies in `[0,1]`. -/
theorem thetaAfter_bounds (j : Fin p.K) (z : Zplus) :
    0 ≤ thetaAfter rate rewards C_star C_h q t s hs control0 j z ∧
      thetaAfter rate rewards C_star C_h q t s hs control0 j z ≤ 1 := by
  have hpos := RecordedMarginalGrowth.state_theta_pos queue (post z) j
    (ConstructorDimensions.m_pos p) p.m_lt_K
  have hlt := ProductSetLaw.theta_lt_one
    (RecordedQueueRun.scoreWeight queue (post z)) j
    (ConstructorDimensions.m_pos p) p.m_lt_K
    (RecordedMarginalGrowth.state_scoreWeight_pos queue (post z))
  exact ⟨hpos.le, hlt.le⟩

/-- The strict-past marginals sum to the source cardinality `m`. -/
theorem sum_thetaBefore_eq_m (z : Zplus) :
    (∑ j : Fin p.K, thetaBefore rate rewards C_star C_h q t s hs control0 j z) =
      (p.m : ℝ) := by
  exact RecordedMarginalGrowth.state_sum_theta_eq_m queue (past z)
    (ConstructorDimensions.m_pos p) p.m_lt_K

/-- The actual post-update score vector, computed from the accepted queue
record. This helper is a readout of the existing update, not a second queue
process. -/
def postScoreReadout (j : Fin p.K) (z : Zplus) : ℕ :=
  if z ∈ G then
    ((past z).registers j).1 + min (4 * rate.n)
      (((past z).registers j).2 + Nat.floor
        (ReferenceFirstLiveAllArmAcceptedConditionalMoments.acceptedA
          rate rewards C_star C_h q t s hs control0 j z * scale))
  else ((past z).registers j).1

/-- The normalized accepted record, multiplied by the exact source scale,
recovers its natural-number arrival. -/
theorem acceptedA_scale_floor_eq_arrival (j : Fin p.K) (z : Zplus) :
    Nat.floor (ReferenceFirstLiveAllArmAcceptedConditionalMoments.acceptedA
      rate rewards C_star C_h q t s hs control0 j z * scale) =
      RecordedQueueRun.acceptedArrival
        (RecordedQueueRun.acceptedRecord queue (past z) (cell z).input j) := by
  rw [ReferenceFirstLiveAllArmAcceptedConditionalMoments.acceptedA]
  have hscale := ReferenceFirstLiveAllArmAcceptedConditionalMoments.scale_pos rate
  rw [div_mul_cancel₀ _ hscale.ne', Nat.floor_natCast]

/-- The actual post score equals the readout formed from the real accepted
record; on `G` the exact max/min queue recurrence includes enabled zero-arrival
service, and off `G` both registers stay fixed. -/
theorem post_score_eq_postScoreReadout (j : Fin p.K) (z : Zplus) :
    ((post z).registers j).1 = postScoreReadout rate rewards C_star C_h q t s hs control0 j z := by
  by_cases hz : z ∈ G
  · rw [postScoreReadout, ite_eq_left hz]
    rw [(ReferenceFirstLiveAllArmAcceptedConditionalMoments.integer_registers_update_on_G
      rate rewards C_star C_h q t s hs control0 j z hz).1]
    have harrival := acceptedA_scale_floor_eq_arrival
      rate rewards C_star C_h q t s hs control0 j z
    have hrecord := ReferenceFirstLiveAllArmAcceptedConditionalMoments.acceptedRecord_eq_if_strictPast
      rate rewards C_star C_h q t s hs control0 j z
    rw [ite_eq_left hz] at hrecord
    rw [hrecord, RecordedQueueRun.acceptedArrival] at harrival
    simpa using congrArg (fun x : ℕ =>
      ((past z).registers j).1 + min (4 * rate.n) (((past z).registers j).2 + x)) harrival.symm
  · rw [postScoreReadout, ite_eq_right hz]
    exact congrArg Prod.fst
      (ReferenceFirstLiveAllArmAcceptedConditionalMoments.integer_registers_unchanged_off_G
        rate rewards C_star C_h q t s hs control0 j z hz).1

/-- The actual post marginal is Borel on the inherited ambient source space.
It is obtained from the measurable strict-past natural registers and the
actual accepted-arrival readout on `G`; no Borel assumption is supplied. -/
theorem measurable_thetaAfter (j : Fin p.K) :
    Measurable (thetaAfter rate rewards C_star C_h q t s hs control0 j) := by
  let afterScores : Zplus → Fin p.K → ℕ := fun z i =>
    postScoreReadout rate rewards C_star C_h q t s hs control0 i z
  have hpastScore : ∀ i, Measurable (fun z : Zplus => ((past z).registers i).1) := by
    intro i
    exact (measurable_pastScore rate rewards C_star C_h q t s hs control0 i).mono
      (ReferenceFirstLiveAllArmPrefixAdaptation.sourcePlusPrefixField_le
        rate rewards C_star C_h q t s hs control0) le_rfl
  have hpastBacklog : ∀ i, Measurable (fun z : Zplus => ((past z).registers i).2) := by
    intro i
    exact (measurable_pastBacklogRegister rate rewards C_star C_h q t s hs control0 i).mono
      (ReferenceFirstLiveAllArmPrefixAdaptation.sourcePlusPrefixField_le
        rate rewards C_star C_h q t s hs control0) le_rfl
  have haccepted : ∀ i, Measurable (fun z : Zplus =>
      ReferenceFirstLiveAllArmAcceptedConditionalMoments.acceptedA
        rate rewards C_star C_h q t s hs control0 i z) := by
    intro i
    exact ReferenceFirstLiveAllArmAcceptedConditionalMoments.measurable_acceptedA
      rate rewards C_star C_h q t s hs control0 i
  have harrival : ∀ i, Measurable (fun z : Zplus => Nat.floor
      (ReferenceFirstLiveAllArmAcceptedConditionalMoments.acceptedA
        rate rewards C_star C_h q t s hs control0 i z * scale)) := by
    intro i
    exact Nat.measurable_floor.comp
      ((haccepted i).mul measurable_const)
  have hG : MeasurableSet G :=
    ReferenceFirstLiveAllArmPrefixAdaptation.measurableSet_strictPastOverflowFalseSet_ambient
      rate rewards C_star C_h q t s hs control0
  have hscore : ∀ i, Measurable (afterScores · i) := by
    intro i
    have htuple : Measurable (fun z : Zplus =>
        (((past z).registers i).1, ((past z).registers i).2,
          Nat.floor (ReferenceFirstLiveAllArmAcceptedConditionalMoments.acceptedA
            rate rewards C_star C_h q t s hs control0 i z * scale))) :=
      (hpastScore i).prodMk ((hpastBacklog i).prodMk (harrival i))
    have hstep : Measurable (fun x : ℕ × ℕ × ℕ => x.1 + min (4 * rate.n) (x.2.1 + x.2.2)) :=
      measurable_of_countable _
    have hstep := hstep.comp htuple
    exact Measurable.ite hG hstep (hpastScore i)
  have hafterScores : Measurable afterScores := by
    apply measurable_pi_iff.mpr
    intro i
    exact hscore i
  let phi : (Fin p.K → ℕ) → ℝ := fun scores =>
    ProductSetLaw.theta p.m
      (fun i => ScoreWeights.scoreWeight
        (1 + 1 / (ConstructorDimensions.D p : ℝ)) (scores i)) j
  have hphi : Measurable phi := measurable_of_countable _
  have htheta := hphi.comp hafterScores
  have heq : thetaAfter rate rewards C_star C_h q t s hs control0 j =
      fun z => phi (afterScores z) := by
    funext z
    unfold thetaAfter phi afterScores
    congr 1
    funext i
    change ScoreWeights.scoreWeight (1 + 1 / (ConstructorDimensions.D p : ℝ))
      ((post z).registers i).1 =
      ScoreWeights.scoreWeight (1 + 1 / (ConstructorDimensions.D p : ℝ))
        (postScoreReadout rate rewards C_star C_h q t s hs control0 i z)
    rw [post_score_eq_postScoreReadout rate rewards C_star C_h q t s hs control0 i z]
  rw [heq]
  exact htheta.mono le_rfl le_rfl

/-- The after-backlog is ambient Borel, by the actual max recurrence on `G`
and the exact stopped-state equality off `G`. -/
theorem measurable_backlogAfter (j : Fin p.K) :
    Measurable (fun z : Zplus =>
      ReferenceFirstLiveAllArmAcceptedConditionalMoments.backlogAfter
        rate rewards C_star C_h q t s hs control0 j z) := by
  have hbefore : Measurable (fun z : Zplus =>
      ReferenceFirstLiveAllArmAcceptedConditionalMoments.backlogBefore
        rate rewards C_star C_h q t s hs control0 j z) :=
    (measurable_backlogBefore rate rewards C_star C_h q t s hs control0 j).mono
      (ReferenceFirstLiveAllArmPrefixAdaptation.sourcePlusPrefixField_le
        rate rewards C_star C_h q t s hs control0) le_rfl
  have haccepted := ReferenceFirstLiveAllArmAcceptedConditionalMoments.measurable_acceptedA
    rate rewards C_star C_h q t s hs control0 j
  have hG : MeasurableSet G :=
    ReferenceFirstLiveAllArmPrefixAdaptation.measurableSet_strictPastOverflowFalseSet_ambient
      rate rewards C_star C_h q t s hs control0
  have hrecurrence : Measurable (fun z : Zplus => max 0
      (ReferenceFirstLiveAllArmAcceptedConditionalMoments.backlogBefore
        rate rewards C_star C_h q t s hs control0 j z +
       ReferenceFirstLiveAllArmAcceptedConditionalMoments.acceptedA
        rate rewards C_star C_h q t s hs control0 j z - 4)) := by
    exact (measurable_const : Measurable (fun _ : Zplus => (0 : ℝ))).max
      ((hbefore.add haccepted).sub
        (measurable_const : Measurable fun _ : Zplus => (4 : ℝ)))
  have hpiece : Measurable (fun z : Zplus =>
      if z ∈ G then max 0 (
        ReferenceFirstLiveAllArmAcceptedConditionalMoments.backlogBefore
          rate rewards C_star C_h q t s hs control0 j z +
        ReferenceFirstLiveAllArmAcceptedConditionalMoments.acceptedA
          rate rewards C_star C_h q t s hs control0 j z - 4)
      else ReferenceFirstLiveAllArmAcceptedConditionalMoments.backlogBefore
        rate rewards C_star C_h q t s hs control0 j z) :=
    Measurable.ite hG hrecurrence hbefore
  have heq := backlogAfter_eq_actual_update rate rewards C_star C_h q t s hs control0 j
  have heqFun :
      (fun z : Zplus =>
        ReferenceFirstLiveAllArmAcceptedConditionalMoments.backlogAfter
          rate rewards C_star C_h q t s hs control0 j z) =
      (fun z : Zplus =>
        if z ∈ G then max 0 (
          ReferenceFirstLiveAllArmAcceptedConditionalMoments.backlogBefore
            rate rewards C_star C_h q t s hs control0 j z +
          ReferenceFirstLiveAllArmAcceptedConditionalMoments.acceptedA
            rate rewards C_star C_h q t s hs control0 j z - 4)
        else ReferenceFirstLiveAllArmAcceptedConditionalMoments.backlogBefore
          rate rewards C_star C_h q t s hs control0 j z) := by
    funext z
    exact heq z
  rw [heqFun]
  exact hpiece

/-- The after-register queue normalization is ambient Borel by the accepted
current update. -/
theorem measurable_normalizedBacklogAfter (j : Fin p.K) :
    Measurable
      (fun z : Zplus => StoppedQueueBound.normalizedBacklog queue (post z) j) := by
  have h := measurable_backlogAfter rate rewards C_star C_h q t s hs control0 j
  have heq :
      (fun z : Zplus =>
        ReferenceFirstLiveAllArmAcceptedConditionalMoments.backlogAfter
          rate rewards C_star C_h q t s hs control0 j z) =
      (fun z : Zplus => StoppedQueueBound.normalizedBacklog queue (post z) j) := by
    funext z
    exact backlogAfter_eq_normalized rate rewards C_star C_h q t s hs control0 j z
  rw [← heq]
  exact h

/-- The before marginal is measurable on `Fplus`; the natural register vector
is the canonical countable carrier used for this real-valued readout. -/
theorem measurable_thetaBefore_field (j : Fin p.K) :
    Measurable[Fplus] (thetaBefore rate rewards C_star C_h q t s hs control0 j) :=
  measurable_thetaBefore rate rewards C_star C_h q t s hs control0 j

/-- The exact strict-past weighted-square potential is measurable on `Fplus`.
-/
theorem measurable_potentialBefore :
    Measurable[Fplus] (potentialBefore rate rewards C_star C_h q t s hs control0) := by
  unfold potentialBefore RecordedWeightedDrift.weightedSquarePotential
  apply Finset.measurable_sum
  intro j hj
  exact (measurable_thetaBefore rate rewards C_star C_h q t s hs control0 j).mul
    ((measurable_normalizedBacklogBefore rate rewards C_star C_h q t s hs control0 j).pow_const 2)

/-- The strict-past weighted backlog coefficient is measurable on the same
explicit prefix field used by the accepted conditional moments. -/
theorem measurable_weightedBacklogBefore :
    Measurable[Fplus] (weightedBacklogBefore rate rewards C_star C_h q t s hs control0) := by
  unfold weightedBacklogBefore RecordedWeightedDrift.weightedBacklog
  apply Finset.measurable_sum
  intro j hj
  exact (measurable_thetaBefore rate rewards C_star C_h q t s hs control0 j).mul
    (measurable_normalizedBacklogBefore rate rewards C_star C_h q t s hs control0 j)

/-- The actual post potential is Borel on the inherited source space, using
the measured post registers and actual post backlogs. -/
theorem measurable_potentialAfter :
    Measurable (potentialAfter rate rewards C_star C_h q t s hs control0) := by
  unfold potentialAfter RecordedWeightedDrift.weightedSquarePotential
  apply Finset.measurable_sum
  intro j hj
  exact (measurable_thetaAfter rate rewards C_star C_h q t s hs control0 j).mul
    ((measurable_normalizedBacklogAfter rate rewards C_star C_h q t s hs control0 j).pow_const 2)

/-- Both current actual marginals are the same exact finite-set cardinality
sum; the first update is included in the post state. -/
theorem sum_thetaAfter_eq_m (z : Zplus) :
    (∑ j : Fin p.K, thetaAfter rate rewards C_star C_h q t s hs control0 j z) =
      (p.m : ℝ) := by
  exact RecordedMarginalGrowth.state_sum_theta_eq_m queue (post z)
    (ConstructorDimensions.m_pos p) p.m_lt_K

/-- The literal after marginal grows by at most `1 + 8 eta` from the actual
current accepted step, including its retained first crossing. -/
theorem thetaAfter_le_growth (j : Fin p.K) (z : Zplus) :
    thetaAfter rate rewards C_star C_h q t s hs control0 j z ≤
      (1 + 8 * rate.eta.val) * thetaBefore rate rewards C_star C_h q t s hs control0 j z := by
  have hlen : n < (cells z).length := by
    rw [ReferenceFirstLiveSourceCellReadout.cells_length]
    change t.val - s < t.val - s + 1
    omega
  have h := RecordedMarginalGrowth.run_prefix_theta_growth queue (cells z) n hlen
    j p.two_le_m p.m_lt_K
    (by simpa [ReferenceFirstLaunchNumericalCell.queueParameters] using
      eta_le_one_div_sixtyFour rate)
  simpa [thetaBefore, thetaAfter, ReferenceFirstLaunchNumericalCell.queueParameters] using
    h.1.trans h.2

/-- The post score equals the real queue update: on `G` it uses M's exact
max/min recurrence, and off `G` the old registers and potential persist. -/
theorem potentialAfter_eq_potentialBefore_of_not_mem_G (z : Zplus)
    (hz : z ∉ G) :
    potentialAfter rate rewards C_star C_h q t s hs control0 z =
      potentialBefore rate rewards C_star C_h q t s hs control0 z := by
  have hregs : (post z).registers = (past z).registers := by
    funext j
    exact (ReferenceFirstLiveAllArmAcceptedConditionalMoments.integer_registers_unchanged_off_G
      rate rewards C_star C_h q t s hs control0 j z hz).1
  have hweight : RecordedQueueRun.scoreWeight queue (post z) =
      RecordedQueueRun.scoreWeight queue (past z) := by
    funext j
    change ScoreWeights.scoreWeight (1 + 1 / (ConstructorDimensions.D p : ℝ))
        ((post z).registers j).1 =
      ScoreWeights.scoreWeight (1 + 1 / (ConstructorDimensions.D p : ℝ))
        ((past z).registers j).1
    rw [congrArg (fun registers => (registers j).1) hregs]
  unfold potentialAfter potentialBefore RecordedWeightedDrift.weightedSquarePotential
  rw [hweight]
  apply Finset.sum_congr rfl
  intro j hj
  simp [StoppedQueueBound.normalizedBacklog, hregs]

/-- Pointwise weighted square drift on the retained strict-past event. The
proof uses the queue-square lemmas and the exact identity
`16 * eta * Bcap = 1/2`. -/
theorem potential_drift_envelope_on_G (z : Zplus) (hz : z ∈ G) :
    potentialAfter rate rewards C_star C_h q t s hs control0 z -
      potentialBefore rate rewards C_star C_h q t s hs control0 z ≤
      ∑ j : Fin p.K, thetaBefore rate rewards C_star C_h q t s hs control0 j z *
        ((2 * ReferenceFirstLiveAllArmAcceptedConditionalMoments.backlogBefore
            rate rewards C_star C_h q t s hs control0 j z + 1 / 2) *
          ReferenceFirstLiveAllArmAcceptedConditionalMoments.acceptedA
            rate rewards C_star C_h q t s hs control0 j z +
          (ReferenceFirstLiveAllArmAcceptedConditionalMoments.acceptedA
            rate rewards C_star C_h q t s hs control0 j z) ^ 2 -
          (15 / 2 : ℝ) * ReferenceFirstLiveAllArmAcceptedConditionalMoments.backlogBefore
            rate rewards C_star C_h q t s hs control0 j z + 16) := by
  let b := fun j : Fin p.K =>
    ReferenceFirstLiveAllArmAcceptedConditionalMoments.backlogBefore
      rate rewards C_star C_h q t s hs control0 j z
  let a := fun j : Fin p.K =>
    ReferenceFirstLiveAllArmAcceptedConditionalMoments.acceptedA
      rate rewards C_star C_h q t s hs control0 j z
  have hsplit : potentialAfter rate rewards C_star C_h q t s hs control0 z -
      potentialBefore rate rewards C_star C_h q t s hs control0 z =
      ∑ j : Fin p.K,
        (thetaAfter rate rewards C_star C_h q t s hs control0 j z *
            ((ReferenceFirstLiveAllArmAcceptedConditionalMoments.backlogAfter
              rate rewards C_star C_h q t s hs control0 j z) ^ 2) -
          thetaBefore rate rewards C_star C_h q t s hs control0 j z * b j ^ 2) := by
    unfold potentialAfter potentialBefore RecordedWeightedDrift.weightedSquarePotential
    rw [← Finset.sum_sub_distrib]
    congr 1
    funext i
    dsimp [b]
    rw [← backlogAfter_eq_normalized rate rewards C_star C_h q t s hs control0 i z,
      ← backlogBefore_eq_normalized rate rewards C_star C_h q t s hs control0 i z]
    simp only [thetaAfter, thetaBefore]
  rw [hsplit]
  apply Finset.sum_le_sum
  intro j hj
  have hb : 0 ≤ b j := by
    exact backlogBefore_nonneg rate rewards C_star C_h q t s hs control0 j z
  have hr : 0 ≤ a j :=
    (ReferenceFirstLiveAllArmAcceptedConditionalMoments.acceptedA_pointwise_bounds
      rate rewards C_star C_h q t s hs control0 j z).1
  have htheta : 0 ≤ thetaBefore rate rewards C_star C_h q t s hs control0 j z :=
    (thetaBefore_bounds rate rewards C_star C_h q t s hs control0 j z).1
  have hpostCap :
      ReferenceFirstLiveAllArmAcceptedConditionalMoments.backlogAfter
        rate rewards C_star C_h q t s hs control0 j z ≤ 2 * Bcap :=
    backlogAfter_le_two_Bcap rate rewards C_star C_h q t s hs control0 j z
  have hnext :
      ReferenceFirstLiveAllArmAcceptedConditionalMoments.backlogAfter
        rate rewards C_star C_h q t s hs control0 j z =
        QueueSquareDrift.queueNext (b j) (a j) := by
    rw [ReferenceFirstLiveAllArmAcceptedConditionalMoments.backlogAfter_eq_max_on_G
      rate rewards C_star C_h q t s hs control0 j z hz]
    simp [QueueSquareDrift.queueNext, max_comm, b, a]
  have hsq := QueueSquareDrift.queueNext_sq_sub_le (b j) (a j) hb hr
  have hcap := QueueSquareDrift.queueNext_sq_le_cap_mul
    (b j) (a j) Bcap hb hr (by positivity [rate.eta.property]) (by
      rw [← hnext]
      exact hpostCap)
  have hscaled0 := mul_le_mul_of_nonneg_left hcap
    (show 0 ≤ 8 * rate.eta.val by positivity [rate.eta.property])
  have hcoeff : 16 * rate.eta.val * Bcap = (1 / 2 : ℝ) := by
    simpa [ReferenceFirstLaunchNumericalCell.queueParameters] using
      RecordedWeightedDrift.sixteen_eta_mul_backlogCap queue
  have hscaled : 8 * rate.eta.val *
      (ReferenceFirstLiveAllArmAcceptedConditionalMoments.backlogAfter
        rate rewards C_star C_h q t s hs control0 j z) ^ 2 ≤
        (1 / 2 : ℝ) * (b j + a j) := by
    calc
      _ ≤ 8 * rate.eta.val * (2 * Bcap * (b j + a j)) := by
        simpa only [hnext] using hscaled0
      _ = (1 / 2 : ℝ) * (b j + a j) := by
        calc
          _ = (16 * rate.eta.val * Bcap) * (b j + a j) := by ring
          _ = _ := by rw [hcoeff]
  have hinner :
      (ReferenceFirstLiveAllArmAcceptedConditionalMoments.backlogAfter
        rate rewards C_star C_h q t s hs control0 j z) ^ 2 - (b j) ^ 2 +
          8 * rate.eta.val *
            (ReferenceFirstLiveAllArmAcceptedConditionalMoments.backlogAfter
              rate rewards C_star C_h q t s hs control0 j z) ^ 2 ≤
        (2 * b j + 1 / 2) * a j + (a j) ^ 2 -
          (15 / 2 : ℝ) * b j + 16 := by
    rw [← hnext] at hsq hcap
    nlinarith only [hsq, hscaled]
  have hgrowth := thetaAfter_le_growth rate rewards C_star C_h q t s hs control0 j z
  have hweighted := QueueSquareDrift.weighted_square_step
    (thetaAfter rate rewards C_star C_h q t s hs control0 j z)
    (thetaBefore rate rewards C_star C_h q t s hs control0 j z)
    rate.eta.val
    (ReferenceFirstLiveAllArmAcceptedConditionalMoments.backlogAfter
      rate rewards C_star C_h q t s hs control0 j z) (b j)
    htheta rate.eta.property.le hgrowth
  calc
    _ ≤ thetaBefore rate rewards C_star C_h q t s hs control0 j z *
        ((ReferenceFirstLiveAllArmAcceptedConditionalMoments.backlogAfter
          rate rewards C_star C_h q t s hs control0 j z) ^ 2 - (b j) ^ 2 +
          8 * rate.eta.val *
            (ReferenceFirstLiveAllArmAcceptedConditionalMoments.backlogAfter
              rate rewards C_star C_h q t s hs control0 j z) ^ 2) := hweighted
    _ ≤ thetaBefore rate rewards C_star C_h q t s hs control0 j z *
        ((2 * b j + 1 / 2) * a j + (a j) ^ 2 -
          (15 / 2 : ℝ) * b j + 16) :=
      mul_le_mul_of_nonneg_left hinner htheta

/-- Off the retained event the actual post potential is unchanged. -/
theorem potentialAfter_eq_potentialBefore_off_G (z : Zplus)
    (hz : z ∉ G) :
    potentialAfter rate rewards C_star C_h q t s hs control0 z =
      potentialBefore rate rewards C_star C_h q t s hs control0 z :=
  potentialAfter_eq_potentialBefore_of_not_mem_G rate rewards C_star C_h q t s hs control0 z hz

/-- The pointwise envelope in the exact `G`-indicator form consumed by the
next conditional-expectation worker on this same `muPlus` and `Fplus`. -/
theorem potential_drift_envelope_indicator (z : Zplus) :
    Set.indicator G (fun x => potentialAfter rate rewards C_star C_h q t s hs control0 x -
        potentialBefore rate rewards C_star C_h q t s hs control0 x) z ≤
      Set.indicator G (fun x =>
        ∑ j : Fin p.K, thetaBefore rate rewards C_star C_h q t s hs control0 j x *
          ((2 * ReferenceFirstLiveAllArmAcceptedConditionalMoments.backlogBefore
              rate rewards C_star C_h q t s hs control0 j x + 1 / 2) *
            ReferenceFirstLiveAllArmAcceptedConditionalMoments.acceptedA
              rate rewards C_star C_h q t s hs control0 j x +
            (ReferenceFirstLiveAllArmAcceptedConditionalMoments.acceptedA
              rate rewards C_star C_h q t s hs control0 j x) ^ 2 -
            (15 / 2 : ℝ) * ReferenceFirstLiveAllArmAcceptedConditionalMoments.backlogBefore
              rate rewards C_star C_h q t s hs control0 j x + 16)) z := by
  by_cases hz : z ∈ G
  · simp only [Set.indicator_of_mem hz]
    exact potential_drift_envelope_on_G rate rewards C_star C_h q t s hs control0 z hz
  · simp [Set.indicator, hz]

/-- The strict-past weighted-square potential is nonnegative and has the
uniform queue-cap bound `m * (2 * Bcap)^2`. -/
theorem potentialBefore_bounds (z : Zplus) :
    0 ≤ potentialBefore rate rewards C_star C_h q t s hs control0 z ∧
      potentialBefore rate rewards C_star C_h q t s hs control0 z ≤
        (p.m : ℝ) * (2 * Bcap) ^ 2 := by
  have hsum := sum_thetaBefore_eq_m rate rewards C_star C_h q t s hs control0 z
  unfold potentialBefore RecordedWeightedDrift.weightedSquarePotential
  constructor
  · apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (thetaBefore_bounds rate rewards C_star C_h q t s hs control0 j z).1
      (sq_nonneg _)
  · calc
      _ ≤ ∑ j : Fin p.K,
          thetaBefore rate rewards C_star C_h q t s hs control0 j z * (2 * Bcap) ^ 2 :=
        Finset.sum_le_sum fun j hj => by
          apply mul_le_mul_of_nonneg_left _
            (thetaBefore_bounds rate rewards C_star C_h q t s hs control0 j z).1
          have hb0 := backlogBefore_nonneg rate rewards C_star C_h q t s hs control0 j z
          have hb := backlogBefore_le_two_Bcap rate rewards C_star C_h q t s hs control0 j z
          have hnorm0 := hb0
          rw [backlogBefore_eq_normalized rate rewards C_star C_h q t s hs control0 j z] at hnorm0
          have hnorm := hb
          rw [backlogBefore_eq_normalized rate rewards C_star C_h q t s hs control0 j z] at hnorm
          have hcap0 : 0 ≤ 2 * Bcap := by positivity [rate.eta.property]
          have hprod := mul_nonneg (sub_nonneg.mpr hnorm)
            (add_nonneg hcap0 hnorm0)
          have hsq : (StoppedQueueBound.normalizedBacklog queue (past z) j) ^ 2 ≤
              (2 * Bcap) ^ 2 := by nlinarith [hprod]
          exact hsq
      _ = (p.m : ℝ) * (2 * Bcap) ^ 2 := by
        rw [← Finset.sum_mul, hsum]

/-- The post potential obeys the same uniform bound, including the first
overflow successor. -/
theorem potentialAfter_bounds (z : Zplus) :
    0 ≤ potentialAfter rate rewards C_star C_h q t s hs control0 z ∧
      potentialAfter rate rewards C_star C_h q t s hs control0 z ≤
        (p.m : ℝ) * (2 * Bcap) ^ 2 := by
  have hsum := sum_thetaAfter_eq_m rate rewards C_star C_h q t s hs control0 z
  unfold potentialAfter RecordedWeightedDrift.weightedSquarePotential
  constructor
  · apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (thetaAfter_bounds rate rewards C_star C_h q t s hs control0 j z).1
      (sq_nonneg _)
  · calc
      _ ≤ ∑ j : Fin p.K,
          thetaAfter rate rewards C_star C_h q t s hs control0 j z * (2 * Bcap) ^ 2 :=
        Finset.sum_le_sum fun j hj => by
          apply mul_le_mul_of_nonneg_left _
            (thetaAfter_bounds rate rewards C_star C_h q t s hs control0 j z).1
          have hb0 : 0 ≤
              ReferenceFirstLiveAllArmAcceptedConditionalMoments.backlogAfter
                rate rewards C_star C_h q t s hs control0 j z := by
            unfold ReferenceFirstLiveAllArmAcceptedConditionalMoments.backlogAfter
            exact div_nonneg (Nat.cast_nonneg _) (le_of_lt
              (ReferenceFirstLiveAllArmAcceptedConditionalMoments.scale_pos rate))
          have hb := backlogAfter_le_two_Bcap rate rewards C_star C_h q t s hs control0 j z
          have hnorm0 := hb0
          rw [backlogAfter_eq_normalized rate rewards C_star C_h q t s hs control0 j z] at hnorm0
          have hnorm := hb
          rw [backlogAfter_eq_normalized rate rewards C_star C_h q t s hs control0 j z] at hnorm
          have hcap0 : 0 ≤ 2 * Bcap := by positivity [rate.eta.property]
          have hprod := mul_nonneg (sub_nonneg.mpr hnorm)
            (add_nonneg hcap0 hnorm0)
          have hsq : (StoppedQueueBound.normalizedBacklog queue (post z) j) ^ 2 ≤
              (2 * Bcap) ^ 2 := by nlinarith [hprod]
          exact hsq
      _ = (p.m : ℝ) * (2 * Bcap) ^ 2 := by
        rw [← Finset.sum_mul, hsum]

/-- The weighted backlog is nonnegative and at most `m * 2 * Bcap`. -/
theorem weightedBacklogBefore_bounds (z : Zplus) :
    0 ≤ weightedBacklogBefore rate rewards C_star C_h q t s hs control0 z ∧
      weightedBacklogBefore rate rewards C_star C_h q t s hs control0 z ≤
        (p.m : ℝ) * (2 * Bcap) := by
  have hsum := sum_thetaBefore_eq_m rate rewards C_star C_h q t s hs control0 z
  unfold weightedBacklogBefore RecordedWeightedDrift.weightedBacklog
  constructor
  · apply Finset.sum_nonneg
    intro j hj
    have hb0 := backlogBefore_nonneg rate rewards C_star C_h q t s hs control0 j z
    rw [backlogBefore_eq_normalized rate rewards C_star C_h q t s hs control0 j z] at hb0
    exact mul_nonneg (thetaBefore_bounds rate rewards C_star C_h q t s hs control0 j z).1 hb0
  · calc
      _ ≤ ∑ j : Fin p.K,
          thetaBefore rate rewards C_star C_h q t s hs control0 j z * (2 * Bcap) :=
        Finset.sum_le_sum fun j hj => by
          have hb := backlogBefore_le_two_Bcap rate rewards C_star C_h q t s hs control0 j z
          rw [backlogBefore_eq_normalized rate rewards C_star C_h q t s hs control0 j z] at hb
          exact mul_le_mul_of_nonneg_left hb
            (thetaBefore_bounds rate rewards C_star C_h q t s hs control0 j z).1
      _ = (p.m : ℝ) * (2 * Bcap) := by
        rw [← Finset.sum_mul, hsum]

/-- A finite unnormalized branch measure integrates every measurable function
with a proved uniform norm bound. -/
private theorem integrable_of_norm_le_uniform {f : Zplus → ℝ} {C : ℝ}
    (hf : Measurable f) (_hC : 0 ≤ C) (hbound : ∀ z, ‖f z‖ ≤ C) :
    Integrable f muPlus := by
  refine (integrable_const C).mono' hf.aestronglyMeasurable ?_
  filter_upwards [] with z
  simpa only [Real.norm_eq_abs, abs_of_nonneg _hC] using hbound z

/-- The before potential is integrable on the existing unnormalized branch
measure, including when the branch measure is zero. -/
theorem integrable_potentialBefore :
    Integrable (potentialBefore rate rewards C_star C_h q t s hs control0) muPlus := by
  apply integrable_of_norm_le_uniform rate rewards C_star C_h q t s hs control0
    (C := (p.m : ℝ) * (2 * Bcap) ^ 2)
    ((measurable_potentialBefore rate rewards C_star C_h q t s hs control0).mono
      (ReferenceFirstLiveAllArmPrefixAdaptation.sourcePlusPrefixField_le
        rate rewards C_star C_h q t s hs control0) le_rfl)
    (by positivity [rate.eta.property])
  intro z
  rw [Real.norm_eq_abs, abs_of_nonneg
    (potentialBefore_bounds rate rewards C_star C_h q t s hs control0 z).1]
  exact (potentialBefore_bounds rate rewards C_star C_h q t s hs control0 z).2

/-- The post potential is integrable under the same finite branch measure. -/
theorem integrable_potentialAfter :
    Integrable (potentialAfter rate rewards C_star C_h q t s hs control0) muPlus := by
  apply integrable_of_norm_le_uniform rate rewards C_star C_h q t s hs control0
    (C := (p.m : ℝ) * (2 * Bcap) ^ 2)
    (measurable_potentialAfter rate rewards C_star C_h q t s hs control0)
    (by positivity [rate.eta.property])
  intro z
  rw [Real.norm_eq_abs, abs_of_nonneg
    (potentialAfter_bounds rate rewards C_star C_h q t s hs control0 z).1]
  exact (potentialAfter_bounds rate rewards C_star C_h q t s hs control0 z).2

/-- The potential difference is integrable; its norm is bounded by the same
uniform cap as either nonnegative potential. -/
theorem integrable_potentialDifference :
    Integrable (fun z : Zplus =>
      potentialAfter rate rewards C_star C_h q t s hs control0 z -
        potentialBefore rate rewards C_star C_h q t s hs control0 z) muPlus := by
  have hmeas : Measurable (fun z : Zplus =>
      potentialAfter rate rewards C_star C_h q t s hs control0 z -
        potentialBefore rate rewards C_star C_h q t s hs control0 z) :=
    (measurable_potentialAfter rate rewards C_star C_h q t s hs control0).sub
      ((measurable_potentialBefore rate rewards C_star C_h q t s hs control0).mono
        (ReferenceFirstLiveAllArmPrefixAdaptation.sourcePlusPrefixField_le
          rate rewards C_star C_h q t s hs control0) le_rfl)
  apply integrable_of_norm_le_uniform rate rewards C_star C_h q t s hs control0
    (C := (p.m : ℝ) * (2 * Bcap) ^ 2)
    hmeas (by positivity [rate.eta.property])
  intro z
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · linarith [(potentialBefore_bounds rate rewards C_star C_h q t s hs control0 z).2,
      (potentialAfter_bounds rate rewards C_star C_h q t s hs control0 z).1]
  · linarith [(potentialAfter_bounds rate rewards C_star C_h q t s hs control0 z).2,
      (potentialBefore_bounds rate rewards C_star C_h q t s hs control0 z).1]

/-- The predictable product `thetaBefore * Bpast` is nonnegative and at most
`2 * Bcap`, with no assumed integrability input. -/
theorem thetaBefore_mul_backlogBefore_bounds (j : Fin p.K) (z : Zplus) :
    0 ≤ thetaBefore rate rewards C_star C_h q t s hs control0 j z *
        ReferenceFirstLiveAllArmAcceptedConditionalMoments.backlogBefore
          rate rewards C_star C_h q t s hs control0 j z ∧
      thetaBefore rate rewards C_star C_h q t s hs control0 j z *
        ReferenceFirstLiveAllArmAcceptedConditionalMoments.backlogBefore
          rate rewards C_star C_h q t s hs control0 j z ≤ 2 * Bcap := by
  have htheta := thetaBefore_bounds rate rewards C_star C_h q t s hs control0 j z
  have hback0 := backlogBefore_nonneg rate rewards C_star C_h q t s hs control0 j z
  have hback := backlogBefore_le_two_Bcap rate rewards C_star C_h q t s hs control0 j z
  refine ⟨mul_nonneg htheta.1 hback0, ?_⟩
  calc
    _ ≤ 1 * ReferenceFirstLiveAllArmAcceptedConditionalMoments.backlogBefore
        rate rewards C_star C_h q t s hs control0 j z :=
      mul_le_mul_of_nonneg_right htheta.2 hback0
    _ ≤ 1 * (2 * Bcap) := by gcongr
    _ = 2 * Bcap := by ring

/-- The predictable product `thetaBefore * Bpast * acceptedA` has a uniform
bound from the actual cap and M's pointwise accepted-arrival bound. -/
theorem thetaBefore_mul_backlogBefore_mul_acceptedA_bounds
    (j : Fin p.K) (z : Zplus) :
    0 ≤ thetaBefore rate rewards C_star C_h q t s hs control0 j z *
        ReferenceFirstLiveAllArmAcceptedConditionalMoments.backlogBefore
          rate rewards C_star C_h q t s hs control0 j z *
        ReferenceFirstLiveAllArmAcceptedConditionalMoments.acceptedA
          rate rewards C_star C_h q t s hs control0 j z ∧
      thetaBefore rate rewards C_star C_h q t s hs control0 j z *
        ReferenceFirstLiveAllArmAcceptedConditionalMoments.backlogBefore
          rate rewards C_star C_h q t s hs control0 j z *
        ReferenceFirstLiveAllArmAcceptedConditionalMoments.acceptedA
          rate rewards C_star C_h q t s hs control0 j z ≤
        (2 * Bcap) / ReferenceFirstLiveSourceSavedMoments.beta rate := by
  have htheta := thetaBefore_bounds rate rewards C_star C_h q t s hs control0 j z
  have hback := backlogBefore_le_two_Bcap rate rewards C_star C_h q t s hs control0 j z
  have harrival := ReferenceFirstLiveAllArmAcceptedConditionalMoments.acceptedA_pointwise_bounds
    rate rewards C_star C_h q t s hs control0 j z
  refine ⟨mul_nonneg (mul_nonneg htheta.1 (backlogBefore_nonneg
    rate rewards C_star C_h q t s hs control0 j z)) harrival.1, ?_⟩
  calc
    _ ≤ (1 * (2 * Bcap)) *
        ReferenceFirstLiveAllArmAcceptedConditionalMoments.acceptedA
          rate rewards C_star C_h q t s hs control0 j z := by
      have hprod := thetaBefore_mul_backlogBefore_bounds
        rate rewards C_star C_h q t s hs control0 j z
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hprod.2 harrival.1
    _ ≤ (1 * (2 * Bcap)) * (1 / ReferenceFirstLiveSourceSavedMoments.beta rate) := by
      exact mul_le_mul_of_nonneg_left harrival.2 (by positivity [rate.eta.property])
    _ = (2 * Bcap) / ReferenceFirstLiveSourceSavedMoments.beta rate := by ring

/-- The predictable backlog product is integrable on the same finite,
unnormalized branch measure. -/
theorem integrable_thetaBefore_mul_backlogBefore (j : Fin p.K) :
    Integrable (fun z : Zplus =>
      thetaBefore rate rewards C_star C_h q t s hs control0 j z *
        ReferenceFirstLiveAllArmAcceptedConditionalMoments.backlogBefore
          rate rewards C_star C_h q t s hs control0 j z) muPlus := by
  have htheta : Measurable (fun z : Zplus =>
      thetaBefore rate rewards C_star C_h q t s hs control0 j z) :=
    ((measurable_thetaBefore rate rewards C_star C_h q t s hs control0 j).mono
      (ReferenceFirstLiveAllArmPrefixAdaptation.sourcePlusPrefixField_le
        rate rewards C_star C_h q t s hs control0) le_rfl)
  have hback : Measurable (fun z : Zplus =>
      ReferenceFirstLiveAllArmAcceptedConditionalMoments.backlogBefore
        rate rewards C_star C_h q t s hs control0 j z) :=
    ((measurable_backlogBefore rate rewards C_star C_h q t s hs control0 j).mono
      (ReferenceFirstLiveAllArmPrefixAdaptation.sourcePlusPrefixField_le
        rate rewards C_star C_h q t s hs control0) le_rfl)
  apply integrable_of_norm_le_uniform rate rewards C_star C_h q t s hs control0
    (C := 2 * Bcap) (htheta.mul hback)
    (by positivity [rate.eta.property])
  intro z
  change ‖thetaBefore rate rewards C_star C_h q t s hs control0 j z *
      ReferenceFirstLiveAllArmAcceptedConditionalMoments.backlogBefore
        rate rewards C_star C_h q t s hs control0 j z‖ ≤ 2 * Bcap
  rw [Real.norm_eq_abs, abs_of_nonneg
    (thetaBefore_mul_backlogBefore_bounds rate rewards C_star C_h q t s hs control0 j z).1]
  exact (thetaBefore_mul_backlogBefore_bounds rate rewards C_star C_h q t s hs control0 j z).2

/-- The product with the current accepted arrival is integrable from its
actual pointwise bound, not a supplied integrability premise. -/
theorem integrable_thetaBefore_mul_backlogBefore_mul_acceptedA (j : Fin p.K) :
    Integrable (fun z : Zplus =>
      thetaBefore rate rewards C_star C_h q t s hs control0 j z *
        ReferenceFirstLiveAllArmAcceptedConditionalMoments.backlogBefore
          rate rewards C_star C_h q t s hs control0 j z *
        ReferenceFirstLiveAllArmAcceptedConditionalMoments.acceptedA
          rate rewards C_star C_h q t s hs control0 j z) muPlus := by
  have htheta : Measurable (fun z : Zplus =>
      thetaBefore rate rewards C_star C_h q t s hs control0 j z) :=
    ((measurable_thetaBefore rate rewards C_star C_h q t s hs control0 j).mono
      (ReferenceFirstLiveAllArmPrefixAdaptation.sourcePlusPrefixField_le
        rate rewards C_star C_h q t s hs control0) le_rfl)
  have hback : Measurable (fun z : Zplus =>
      ReferenceFirstLiveAllArmAcceptedConditionalMoments.backlogBefore
        rate rewards C_star C_h q t s hs control0 j z) :=
    ((measurable_backlogBefore rate rewards C_star C_h q t s hs control0 j).mono
      (ReferenceFirstLiveAllArmPrefixAdaptation.sourcePlusPrefixField_le
        rate rewards C_star C_h q t s hs control0) le_rfl)
  have hpair : Measurable (fun z : Zplus =>
      thetaBefore rate rewards C_star C_h q t s hs control0 j z *
        ReferenceFirstLiveAllArmAcceptedConditionalMoments.backlogBefore
          rate rewards C_star C_h q t s hs control0 j z) := htheta.mul hback
  have hmeas : Measurable (fun z : Zplus =>
      (thetaBefore rate rewards C_star C_h q t s hs control0 j z *
        ReferenceFirstLiveAllArmAcceptedConditionalMoments.backlogBefore
          rate rewards C_star C_h q t s hs control0 j z) *
        ReferenceFirstLiveAllArmAcceptedConditionalMoments.acceptedA
          rate rewards C_star C_h q t s hs control0 j z) :=
    hpair.mul (ReferenceFirstLiveAllArmAcceptedConditionalMoments.measurable_acceptedA
      rate rewards C_star C_h q t s hs control0 j)
  have hC : 0 ≤ (2 * Bcap) / ReferenceFirstLiveSourceSavedMoments.beta rate :=
    div_nonneg (by positivity [rate.eta.property])
      (le_of_lt (CanonicalRecordingRates.beta_pos p rate.eta.property))
  apply integrable_of_norm_le_uniform rate rewards C_star C_h q t s hs control0
    (C := (2 * Bcap) / ReferenceFirstLiveSourceSavedMoments.beta rate)
    hmeas hC
  intro z
  rw [Real.norm_eq_abs, abs_of_nonneg
    (thetaBefore_mul_backlogBefore_mul_acceptedA_bounds
      rate rewards C_star C_h q t s hs control0 j z).1]
  exact (thetaBefore_mul_backlogBefore_mul_acceptedA_bounds
    rate rewards C_star C_h q t s hs control0 j z).2

/-- The strict-past weighted backlog itself is integrable under the original
finite branch measure, using its derived `m * 2 * Bcap` bound. -/
theorem integrable_weightedBacklogBefore :
    Integrable (weightedBacklogBefore rate rewards C_star C_h q t s hs control0) muPlus := by
  have hmeas : Measurable (weightedBacklogBefore rate rewards C_star C_h q t s hs control0) :=
    (measurable_weightedBacklogBefore rate rewards C_star C_h q t s hs control0).mono
      (ReferenceFirstLiveAllArmPrefixAdaptation.sourcePlusPrefixField_le
        rate rewards C_star C_h q t s hs control0) le_rfl
  apply integrable_of_norm_le_uniform rate rewards C_star C_h q t s hs control0
    (C := (p.m : ℝ) * (2 * Bcap))
    hmeas (by positivity [rate.eta.property])
  intro z
  rw [Real.norm_eq_abs, abs_of_nonneg
    (weightedBacklogBefore_bounds rate rewards C_star C_h q t s hs control0 z).1]
  exact (weightedBacklogBefore_bounds rate rewards C_star C_h q t s hs control0 z).2

end Bandits.Support.ReferenceFirstLiveQueueEnergyEnvelope

end
