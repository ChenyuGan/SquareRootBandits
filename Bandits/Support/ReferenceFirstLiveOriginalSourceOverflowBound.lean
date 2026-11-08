/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSReferenceFirstLiveCalendarExponentialBound.
-/
module

public import Bandits.Support.ReferenceFirstLiveCalendarExponentialBound
public import Bandits.Support.ReferenceFirstLiveOverflowMeasurability

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-!
# Original-source first-live overflow tail

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:140-188,245-290`,
`sources/zip4/manuscript/06_interruptions.tex:391-408,425-426`,
`sources/zip4/manuscript/07_public_setup.tex:145-164`, and
`sources/zip4/manuscript/08_main_theorem.tex:29-42,111-128`.

This module turns the accepted actual first-live calendar exponential estimate
into the Markov and finite-arm tail for the literal first-window overflow
event. Its source carrier and original finite measure are unchanged. It proves
neither the later-window/collection overflow producers nor a global queue or
regret bound.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped Classical
open Bandits.Support

namespace Bandits.Support.ReferenceFirstLiveOriginalSourceOverflowBound

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev RewardTable := ActualInitializationPhysicalStep.GridRewardTable
abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput
abbrev TimeControl := ContinuousLearningRows.TimeControl

variable {p : Parameters}

local notation "N0" => ConstructorDimensions.N p
/-- The literal administrative event: the actual whole-source first-live
overflow observation is present in its original `Option ℕ` space. -/
def firstWindowOverflow (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) : Set (SourceInput p) :=
  {omega | ReferenceFirstLiveOverflowReadout.wholeFirstLiveOverflowRound rate rewards C_star C_h omega ≠ none}

/-- The terminal backlog threshold event for the actual first-live queue. -/
def terminalBacklogThresholdEvent (rate : RateInput p)
    (rewards : RewardTable p) (C_star C_h : ℝ) : Set (SourceInput p) :=
  ⋃ j : Fin p.K,
    {omega | 1 / (32 * rate.eta.val) <
      ReferenceFirstLiveCalendarPrefixReadout.firstWindowBacklogAt rate rewards C_star C_h j p.T omega}

/-- The canonical exponential scale times the printed source threshold is
exactly the canonical stability logarithm. -/
theorem beta_mul_overflowCap_eq_L_stab (rate : RateInput p) :
    ReferenceFirstLiveSourceSavedMoments.beta rate *
      (1 / (32 * rate.eta.val)) = (CanonicalRecordingRates.L_stab p : ℝ) := by
  rw [ReferenceFirstLiveSourceSavedMoments.beta, CanonicalRecordingRates.beta]
  field_simp [ne_of_gt rate.eta.property]

/-- The original-source event is Borel in the unchanged `Option` readout. -/
theorem measurableSet_firstWindowOverflow (rate : RateInput p)
    (rewards : RewardTable p) (C_star C_h : ℝ) :
    MeasurableSet (firstWindowOverflow rate rewards C_star C_h) := by
  have hround := ReferenceFirstLiveOverflowMeasurability.measurable_wholeFirstLiveOverflowRound rate rewards C_star C_h
  have hnone : MeasurableSet ({none} : Set (Option ℕ)) := measurableSet_singleton none
  change MeasurableSet
    ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveOverflowRound
      rate rewards C_star C_h) ⁻¹' ({none} : Set (Option ℕ))ᶜ)
  exact hnone.compl.preimage hround

/-- The terminal arm-union threshold event is Borel on the original source. -/
theorem measurableSet_terminalBacklogThresholdEvent (rate : RateInput p)
    (rewards : RewardTable p) (C_star C_h : ℝ) :
    MeasurableSet (terminalBacklogThresholdEvent rate rewards C_star C_h) := by
  apply MeasurableSet.iUnion
  intro j
  exact measurableSet_lt measurable_const
    (ReferenceFirstLiveCalendarPrefixReadout.measurable_firstWindowBacklogAt rate rewards C_star C_h j p.T)

private theorem exists_actual_overflow_fiber (rate : RateInput p)
    (rewards : RewardTable p) (C_star C_h : ℝ) (omega : SourceInput p)
    (homega : omega ∈ firstWindowOverflow rate rewards C_star C_h) :
    ∃ s : Fin (p.T + 1),
      ∃ x : ReferenceFirstLiveOverflowReadout.LaunchFiber rate rewards C_star C_h s.val,
        x.val = omega ∧
          ReferenceFirstLiveOverflowReadout.firstLiveOverflowRound rate rewards C_star C_h s.val
            (p.T - s.val) (ReferenceFirstLiveOverflowReadout.maximal_span s) x ≠ none := by
  classical
  change ReferenceFirstLiveOverflowReadout.wholeFirstLiveOverflowRound rate rewards C_star C_h omega ≠ none at homega
  cases hcross : (ReferenceCompletePhysicalHistory.generatedBoundary
      rate omega rewards C_star C_h).crossing with
  | none =>
      have hnone := ReferenceFirstLiveOverflowReadout.wholeFirstLive_no_launch rate rewards C_star C_h omega hcross
      rw [hnone.2.2.2.2] at homega
      exact False.elim (homega rfl)
  | some crossing =>
      have hc : (ReferenceCompletePhysicalHistory.generatedBoundary
          rate omega rewards C_star C_h).crossing.isSome = true := by
        simp [hcross]
      let start := ReferenceCompletePhysicalHistory.physicalStart
        rate omega rewards C_star C_h
      have hstart : start ≤ p.T :=
        ReferenceCompletePhysicalHistory.physicalStart_le_T rate omega rewards C_star C_h
      let s : Fin (p.T + 1) := ⟨start, Nat.lt_succ_of_le hstart⟩
      let x : ReferenceFirstLiveOverflowReadout.LaunchFiber rate rewards C_star C_h start :=
        ⟨omega, ⟨hc, rfl⟩⟩
      have hreadouts := ReferenceFirstLiveOverflowReadout.wholeFirstLive_readouts_on_fiber
        rate rewards C_star C_h s x
      have hround : ReferenceFirstLiveOverflowReadout.wholeFirstLiveOverflowRound rate rewards C_star C_h omega =
          ReferenceFirstLiveOverflowReadout.firstLiveOverflowRound rate rewards C_star C_h s.val
            (p.T - s.val) (ReferenceFirstLiveOverflowReadout.maximal_span s) x := hreadouts.2.2.2.2.2
      have hsome : ReferenceFirstLiveOverflowReadout.firstLiveOverflowRound rate rewards C_star C_h s.val
          (p.T - s.val) (ReferenceFirstLiveOverflowReadout.maximal_span s) x ≠ none := by
        rw [← hround]
        exact homega
      exact ⟨s, x, rfl, hsome⟩

/-- Every observed calendar round is the one-based date of an actual included
crossing record, and lies within the public horizon. -/
theorem firstWindowOverflow_round_bounds (rate : RateInput p)
    (rewards : RewardTable p) (C_star C_h : ℝ) (omega : SourceInput p)
    (homega : omega ∈ firstWindowOverflow rate rewards C_star C_h) :
    ∃ v, ReferenceFirstLiveOverflowReadout.wholeFirstLiveOverflowRound rate rewards C_star C_h omega = some v ∧
      0 < v ∧ v ≤ p.T := by
  classical
  obtain ⟨s, x, hx, hsome⟩ :=
    exists_actual_overflow_fiber rate rewards C_star C_h omega homega
  cases hr : ReferenceFirstLiveOverflowReadout.firstLiveOverflowRound rate rewards C_star C_h s.val
      (p.T - s.val) (ReferenceFirstLiveOverflowReadout.maximal_span s) x with
  | none => exact False.elim (hsome hr)
  | some v =>
      have hk : ReferenceFirstLiveOverflowReadout.firstLiveOverflowPrefix rate rewards C_star C_h
          s.val (p.T - s.val) (ReferenceFirstLiveOverflowReadout.maximal_span s) x ≤
          ReferenceFirstLiveOverflowReadout.firstLiveLength rate rewards C_star C_h
            s.val (p.T - s.val) (ReferenceFirstLiveOverflowReadout.maximal_span s) x := by
        by_contra hnot
        have hnone : ReferenceFirstLiveOverflowReadout.firstLiveOverflowRound rate rewards C_star C_h
            s.val (p.T - s.val) (ReferenceFirstLiveOverflowReadout.maximal_span s) x = none := by
          simp [ReferenceFirstLiveOverflowReadout.firstLiveOverflowRound, hnot]
        exact hsome hnone
      have hv : v = s.val + ReferenceFirstLiveOverflowReadout.firstLiveOverflowPrefix
          rate rewards C_star C_h s.val (p.T - s.val)
            (ReferenceFirstLiveOverflowReadout.maximal_span s) x := by
        have hsomeEq : some (s.val + ReferenceFirstLiveOverflowReadout.firstLiveOverflowPrefix
            rate rewards C_star C_h s.val (p.T - s.val)
              (ReferenceFirstLiveOverflowReadout.maximal_span s) x) = some v := by
          simpa [ReferenceFirstLiveOverflowReadout.firstLiveOverflowRound, hk] using hr
        exact (Option.some.inj hsomeEq).symm
      obtain ⟨_hj, _htime, htimeNext, htimeLe⟩ :=
        ReferenceFirstLiveOverflowReadout.firstLive_crossing_time
          rate rewards C_star C_h s.val (p.T - s.val)
          (ReferenceFirstLiveOverflowReadout.maximal_span s) x hk
      have hround := ReferenceFirstLiveOverflowReadout.wholeFirstLive_readouts_on_fiber rate rewards C_star C_h s x
      have hwhole : ReferenceFirstLiveOverflowReadout.wholeFirstLiveOverflowRound
          rate rewards C_star C_h x.val =
          ReferenceFirstLiveOverflowReadout.firstLiveOverflowRound rate rewards C_star C_h
            s.val (p.T - s.val) (ReferenceFirstLiveOverflowReadout.maximal_span s) x :=
        hround.2.2.2.2.2
      rw [hx] at hwhole
      refine ⟨v, ?_, ?_, ?_⟩
      · rw [hwhole, hr]
      · rw [hv, ← htimeNext]
        omega
      · rw [hv]
        exact htimeLe

/-- The literal first-window overflow event is produced by an actual terminal
arm backlog above the printed threshold. -/
theorem firstWindowOverflow_subset_terminalBacklogThresholdEvent
    (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ) :
    firstWindowOverflow rate rewards C_star C_h ⊆
      terminalBacklogThresholdEvent rate rewards C_star C_h := by
  intro omega homega
  classical
  obtain ⟨s, x, hx, hsome⟩ :=
    exists_actual_overflow_fiber rate rewards C_star C_h omega homega
  let cells := ReferenceFirstLiveOverflowReadout.firstLiveCells rate rewards C_star C_h s.val
    (p.T - s.val) (ReferenceFirstLiveOverflowReadout.maximal_span s) x
  let q := ReferenceFirstLaunchNumericalCell.queueParameters rate
  let kappa := ReferenceFirstLiveOverflowReadout.firstLiveOverflowPrefix rate rewards C_star C_h s.val
    (p.T - s.val) (ReferenceFirstLiveOverflowReadout.maximal_span s) x
  have hkappaLength : kappa ≤ ReferenceFirstLiveOverflowReadout.firstLiveLength rate rewards C_star C_h s.val
      (p.T - s.val) (ReferenceFirstLiveOverflowReadout.maximal_span s) x := by
    by_contra hnot
    have hnone : ReferenceFirstLiveOverflowReadout.firstLiveOverflowRound rate rewards C_star C_h s.val
        (p.T - s.val) (ReferenceFirstLiveOverflowReadout.maximal_span s) x = none := by
      simp [ReferenceFirstLiveOverflowReadout.firstLiveOverflowRound, kappa, hnot]
    exact hsome hnone
  have hlenCount := ReferenceFirstLiveOverflowReadout.firstLiveLength_le_count rate rewards C_star C_h s.val
    (p.T - s.val) (ReferenceFirstLiveOverflowReadout.maximal_span s) x
  have hcellsLength := ReferenceFirstLiveOverflowReadout.firstLiveCells_length rate rewards C_star C_h s.val
    (p.T - s.val) (ReferenceFirstLiveOverflowReadout.maximal_span s) x
  have hkappaCells : kappa ≤ cells.length := by
    rw [hcellsLength]
    exact hkappaLength
  have hcross := UnstoppedRecordedQueueComparison.replay_crosses_overflow_at_first q cells hkappaCells
  obtain ⟨j, hnormalized⟩ :=
    (UnstoppedRecordedQueueComparison.replay_crosses_overflow_iff_normalized q cells kappa).mp hcross
  have hregs := UnstoppedRecordedQueueComparison.prefix_registers_eq_unstopped_replay q cells cells.length le_rfl j
  have hkappaEq : kappa = UnstoppedRecordedQueueComparison.firstOverflowPrefix q cells := by
    rfl
  have hmin : min cells.length (UnstoppedRecordedQueueComparison.firstOverflowPrefix q cells) =
      UnstoppedRecordedQueueComparison.firstOverflowPrefix q cells := by
    apply Nat.min_eq_right
    simpa [kappa, cells, q, ReferenceFirstLiveOverflowReadout.firstLiveOverflowPrefix,
      ReferenceFirstLaunchNumericalCell.queueParameters] using hkappaCells
  have hregs' : (RecordedQueueRun.run q cells).registers j =
      UnstoppedRecordedQueueComparison.unstoppedReplay q cells kappa j := by
    rw [List.take_length, hmin, ← hkappaEq] at hregs
    exact hregs
  have hsourceCells := (ReferenceFirstLiveOverflowReadout.wholeFirstLive_on_fiber rate rewards C_star C_h s x).2
  rw [hx] at hsourceCells
  have hfiber : x.val ∈ ReferenceGeneratedDownAmbiguityMeasurability.generatedLaunchFiberSet
      (rate := rate) rewards C_star C_h s.val := x.property
  have hfiber' :
      ((ReferenceCompletePhysicalHistory.generatedBoundary rate x.val rewards C_star C_h).crossing.isSome = true) ∧
        ReferenceCompletePhysicalHistory.physicalStart rate x.val rewards C_star C_h = s.val := by
    exact hfiber
  have hphysicalStart : ReferenceCompletePhysicalHistory.physicalStart
      rate omega rewards C_star C_h = s.val := by
    rw [← hx]
    exact hfiber'.2
  have hterminalTake : cells.take (p.T - s.val) = cells := by
    apply List.take_of_length_le
    rw [hcellsLength]
    exact hlenCount
  have hbacklog : ReferenceFirstLiveCalendarPrefixReadout.firstWindowBacklogAt rate rewards C_star C_h j p.T omega =
      (((UnstoppedRecordedQueueComparison.unstoppedReplay q cells kappa j).2 : ℝ) / (q.n : ℝ)) := by
    rw [ReferenceFirstLiveCalendarPrefixReadout.firstWindowBacklogAt]
    change StoppedQueueBound.normalizedBacklog q
      (RecordedQueueRun.run q
        ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h omega).take
          (p.T - ReferenceCompletePhysicalHistory.physicalStart
            rate omega rewards C_star C_h))) j = _
    rw [hsourceCells, hphysicalStart]
    change StoppedQueueBound.normalizedBacklog q
      (RecordedQueueRun.run q (cells.take (p.T - s.val))) j = _
    rw [hterminalTake, StoppedQueueBound.normalizedBacklog, hregs']
  rw [terminalBacklogThresholdEvent, Set.mem_iUnion]
  refine ⟨j, ?_⟩
  change 1 / (32 * rate.eta.val) <
    ReferenceFirstLiveCalendarPrefixReadout.firstWindowBacklogAt rate rewards C_star C_h j p.T omega
  rw [hbacklog]
  change (((UnstoppedRecordedQueueComparison.unstoppedReplay q cells kappa j).2 : ℝ) / (q.n : ℝ)) >
    1 / (32 * rate.eta.val)
  simpa [q, ReferenceFirstLaunchNumericalCell.queueParameters] using hnormalized

/-- The terminal arm-union tail follows from the accepted exponential calendar
estimate by Markov's inequality, with the original source law unchanged. -/
theorem terminalBacklogThresholdEvent_measureReal_le_exp
    (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ)
    (control0 : TimeControl p) :
    (BootstrapPrivateRoundStreams.sourceInputLaw p).real (terminalBacklogThresholdEvent rate rewards C_star C_h) ≤
      (p.K : ℝ) * ((p.T : ℝ) + 1) *
        Real.exp (-(CanonicalRecordingRates.L_stab p : ℝ)) := by
  have hbeta : 0 < ReferenceFirstLiveSourceSavedMoments.beta rate := by
    change 0 < CanonicalRecordingRates.beta p rate.eta.val
    exact CanonicalRecordingRates.beta_pos p rate.eta.property
  have hscale := beta_mul_overflowCap_eq_L_stab (p := p) rate
  have hArm (j : Fin p.K) :
      (BootstrapPrivateRoundStreams.sourceInputLaw p).real {omega | 1 / (32 * rate.eta.val) <
          ReferenceFirstLiveCalendarPrefixReadout.firstWindowBacklogAt rate rewards C_star C_h j p.T omega} ≤
        ((p.T : ℝ) + 1) * Real.exp (-(CanonicalRecordingRates.L_stab p : ℝ)) := by
    let backlog := ReferenceFirstLiveCalendarPrefixReadout.firstWindowBacklogAt rate rewards C_star C_h j p.T
    let expBacklog (omega : SourceInput p) :=
      Real.exp (ReferenceFirstLiveSourceSavedMoments.beta rate * backlog omega)
    let expLevel := Real.exp (CanonicalRecordingRates.L_stab p : ℝ)
    let highSet := {omega : SourceInput p | expLevel ≤ expBacklog omega}
    have hsubset : {omega | 1 / (32 * rate.eta.val) < backlog omega} ⊆ highSet := by
      intro omega homega
      have hmul := mul_lt_mul_of_pos_left homega hbeta
      rw [hscale] at hmul
      change expLevel ≤ expBacklog omega
      exact Real.exp_le_exp.mpr hmul.le
    have hnonneg : 0 ≤ᵐ[BootstrapPrivateRoundStreams.sourceInputLaw p] expBacklog :=
      Filter.Eventually.of_forall (fun omega => (Real.exp_nonneg _))
    have hintegrable : Integrable expBacklog (BootstrapPrivateRoundStreams.sourceInputLaw p) := by
      simpa only [expBacklog, backlog] using
        ReferenceFirstLiveCalendarExponentialBound.integrable_firstWindowExpBacklogAt rate rewards C_star C_h j p.T
    have hmarkov := mul_meas_ge_le_integral_of_nonneg hnonneg hintegrable expLevel
    have hintegral := ReferenceFirstLiveCalendarExponentialBound.integral_exp_calendar_terminal
      rate rewards C_star C_h control0 j
    have hhigh : (BootstrapPrivateRoundStreams.sourceInputLaw p).real highSet ≤ ((p.T : ℝ) + 1) / expLevel := by
      apply (le_div_iff₀ (Real.exp_pos _)).2
      have hmarkov' : expLevel * (BootstrapPrivateRoundStreams.sourceInputLaw p).real highSet ≤ (p.T : ℝ) + 1 := by
        simpa only [highSet, expLevel, expBacklog] using hmarkov.trans hintegral
      nlinarith [hmarkov']
    calc
      (BootstrapPrivateRoundStreams.sourceInputLaw p).real {omega | 1 / (32 * rate.eta.val) < backlog omega} ≤ (BootstrapPrivateRoundStreams.sourceInputLaw p).real highSet :=
        measureReal_mono hsubset
      _ ≤ ((p.T : ℝ) + 1) / expLevel := hhigh
      _ = ((p.T : ℝ) + 1) * Real.exp (-(CanonicalRecordingRates.L_stab p : ℝ)) := by
        dsimp [expLevel]
        rw [Real.exp_neg, div_eq_mul_inv]

  calc
    (BootstrapPrivateRoundStreams.sourceInputLaw p).real (terminalBacklogThresholdEvent rate rewards C_star C_h) ≤
        ∑ j : Fin p.K, (BootstrapPrivateRoundStreams.sourceInputLaw p).real
          {omega | 1 / (32 * rate.eta.val) <
            ReferenceFirstLiveCalendarPrefixReadout.firstWindowBacklogAt rate rewards C_star C_h j p.T omega} :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ j : Fin p.K,
          ((p.T : ℝ) + 1) * Real.exp (-(CanonicalRecordingRates.L_stab p : ℝ)) := by
      apply Finset.sum_le_sum
      intro j hj
      exact hArm j
    _ = (p.K : ℝ) * ((p.T : ℝ) + 1) *
          Real.exp (-(CanonicalRecordingRates.L_stab p : ℝ)) := by
      simp [Finset.sum_const, nsmul_eq_mul, mul_assoc]

/-- The actual first-window overflow event has the same finite-arm exponential
tail as its terminal backlog-threshold producer. -/
theorem firstWindowOverflow_measureReal_le_exp
    (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ)
    (control0 : TimeControl p) :
    (BootstrapPrivateRoundStreams.sourceInputLaw p).real (firstWindowOverflow rate rewards C_star C_h) ≤
      (p.K : ℝ) * ((p.T : ℝ) + 1) *
        Real.exp (-(CanonicalRecordingRates.L_stab p : ℝ)) := by
  calc
    (BootstrapPrivateRoundStreams.sourceInputLaw p).real (firstWindowOverflow rate rewards C_star C_h) ≤
        (BootstrapPrivateRoundStreams.sourceInputLaw p).real (terminalBacklogThresholdEvent rate rewards C_star C_h) :=
      measureReal_mono (firstWindowOverflow_subset_terminalBacklogThresholdEvent
        rate rewards C_star C_h)
    _ ≤ _ := terminalBacklogThresholdEvent_measureReal_le_exp
      rate rewards C_star C_h control0

/-- The literal canonical logarithm turns the first-window exponential tail
into the printed inverse-square scale. -/
theorem firstWindowOverflow_measureReal_le_inv_N_sq
    (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ)
    (control0 : TimeControl p) :
    (BootstrapPrivateRoundStreams.sourceInputLaw p).real (firstWindowOverflow rate rewards C_star C_h) ≤
      1 / (N0 : ℝ) ^ 2 := by
  have hExp := firstWindowOverflow_measureReal_le_exp
    rate rewards C_star C_h control0
  have hArgNat : 0 < 2 * p.K * (p.T + 1) * N0 ^ 2 := by
    exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by decide)
      (ConstructorDimensions.K_pos p)) (Nat.zero_lt_succ p.T))
      (Nat.pow_pos (ConstructorDimensions.N_pos p))
  have hlog := CanonicalRecordingRates.log_stabArgument_le_L_stab p
  have hexpNat :
      ((2 * p.K * (p.T + 1) * N0 ^ 2 : ℕ) : ℝ) ≤
        Real.exp (CanonicalRecordingRates.L_stab p : ℝ) := by
    have hexp := Real.exp_le_exp.mpr hlog
    rw [Real.exp_log (by exact_mod_cast hArgNat)] at hexp
    exact hexp
  have hK : 0 < (p.K : ℝ) := Nat.cast_pos.mpr (ConstructorDimensions.K_pos p)
  have hT : 0 < (p.T : ℝ) + 1 := by positivity
  have hN : 0 < (N0 : ℝ) := Nat.cast_pos.mpr (ConstructorDimensions.N_pos p)
  have hN2 : 0 < (N0 : ℝ) ^ 2 := sq_pos_of_pos hN
  have hden : 0 < Real.exp (CanonicalRecordingRates.L_stab p : ℝ) := Real.exp_pos _
  have hlarge :
      ((p.K : ℝ) * ((p.T : ℝ) + 1)) * (N0 : ℝ) ^ 2 ≤
        Real.exp (CanonicalRecordingRates.L_stab p : ℝ) := by
    have hcast :
        2 * (p.K : ℝ) * ((p.T : ℝ) + 1) * (N0 : ℝ) ^ 2 ≤
          Real.exp (CanonicalRecordingRates.L_stab p : ℝ) := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one,
        Nat.cast_pow] using hexpNat
    nlinarith
  have hnum :
      ((p.K : ℝ) * ((p.T : ℝ) + 1)) * Real.exp (-(CanonicalRecordingRates.L_stab p : ℝ)) ≤
        1 / (N0 : ℝ) ^ 2 := by
    rw [Real.exp_neg]
    field_simp [ne_of_gt hden, ne_of_gt hN2]
    nlinarith [hlarge]
  exact hExp.trans hnum

end Bandits.Support.ReferenceFirstLiveOriginalSourceOverflowBound

end
