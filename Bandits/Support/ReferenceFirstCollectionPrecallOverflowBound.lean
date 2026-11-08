/-
Copyright (c) 2026 Bandits Lean formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionPrecallIncomingExponentialEnvelope

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-!
# Original-source pre-first-invocation overflow boundary

The event below tests only actual present optional prefixes in the unchanged
source execution. Its terminal characterization keeps the first detecting
queue update, and its first-call witness identifies an actual processed
source update strictly before the invocation round.

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:140-188,245-290`,
`sources/zip4/manuscript/05_binary_transport.tex:352-431`, and
`sources/zip4/manuscript/06_interruptions.tex:35-100,355-426`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators Classical

namespace Bandits.Support.ReferenceFirstCollectionPrecallOverflowBound

open Bandits.Support.ConstructorDimensions
open BootstrapPrivateRoundStreams (SourceInput sourceInputLaw)
open ActualInitializationPhysicalStep (GridRewardTable)
open ReferenceActivePhysicalStep (RateInput)
open ContinuousLearningRows (TimeControl)

variable {p : Parameters}
  (rate : RateInput p) (rewards : GridRewardTable p)
  (C_star C_h : ℝ)

local notation "S" => SourceInput p
local notation "Q" => ReferenceFirstLaunchNumericalCell.queueParameters rate
local notation "cap" => (1 / (32 * rate.eta.val))
local notation "beta" => CanonicalRecordingRates.beta p rate.eta.val
local notation "Lstab" => (CanonicalRecordingRates.L_stab p : ℝ)

/-- Literal overflow in a present original pre-first-invocation prefix. An
absent readout remains absent and is never turned into a zero-state run. -/
def precallOverflow : Set S :=
  {z | ∃ n : ℕ, n ≤ p.T ∧
    ∃ L : List (RecordedQueueRun.RoundInput p.K),
      ReferenceFirstCollectionPrecallCalendarSupport.precallCells?
        rate rewards C_star C_h n z = some L ∧
      (RecordedQueueRun.run Q L).overflow = true}

/-- The union of the literal terminal normalized-backlog thresholds. -/
def terminalThreshold : Set S :=
  ⋃ a : Fin p.K,
    {z | cap < ReferenceFirstCollectionPrecallCalendarSupport.precallBacklog
      rate rewards C_star C_h p.T a z}

private theorem execute_append (first second :
    List (RecordedQueueRun.RoundInput p.K)) (state : RecordedQueueRun.RunState p.K) :
    RecordedQueueRun.execute Q (first ++ second) state =
      RecordedQueueRun.execute Q second (RecordedQueueRun.execute Q first state) := by
  induction first generalizing state with
  | nil => simp [RecordedQueueRun.execute]
  | cons round first ih =>
      simp only [List.cons_append, RecordedQueueRun.execute]
      exact ih (RecordedQueueRun.step Q state round)

/-- The terminal stopped flag is exactly the arm-union threshold, including
the optional absent-prefix branch. -/
theorem precallOverflow_eq_terminalThreshold :
    precallOverflow rate rewards C_star C_h =
      terminalThreshold rate rewards C_star C_h := by
  classical
  ext z
  constructor
  · rintro ⟨n, hn, L, hcells, hoverflow⟩
    obtain hnone | ⟨hlaunch, Lterm, hterm, hlen, hslots, hslot⟩ :=
      ReferenceFirstCollectionPrecallCalendarSupport.precallPrefix_support
        rate rewards C_star C_h n hn z
    · exact False.elim (by rw [hnone.2] at hcells; cases hcells)
    · have hlaunchT :
          ReferenceSourcePrefixHistoryFiltration.actualLaunchBy rate rewards C_star C_h
            (ReferenceFirstCollectionPrecallCalendarSupport.cutBoundary
              rate rewards C_star C_h p.T z) z := by
        rcases hlaunch with ⟨hc, hs⟩
        have hcut :
            ReferenceFirstCollectionPrecallCalendarSupport.cutBoundary
              rate rewards C_star C_h n z ≤
            ReferenceFirstCollectionPrecallCalendarSupport.cutBoundary
              rate rewards C_star C_h p.T z := by
          change min n (ReferenceFirstCollectionPrecallCalendarSupport.firstCallBoundary
              rate rewards C_star C_h z) ≤
            min p.T (ReferenceFirstCollectionPrecallCalendarSupport.firstCallBoundary
              rate rewards C_star C_h z)
          exact min_le_min hn le_rfl
        exact ⟨hc, hs.trans hcut⟩
      obtain ⟨Lterm, hterminal, _, _, _⟩ :=
        ReferenceFirstCollectionPrecallCalendarSupport.precallPrefix_present
          rate rewards C_star C_h p.T le_rfl z hlaunchT
      have htake := ReferenceFirstCollectionPrecallCalendarSupport.precallCells_take
        rate rewards C_star C_h n p.T hn z Lterm hterminal
      have hlist : L = Lterm.take
          (ReferenceFirstCollectionPrecallCalendarSupport.cutBoundary
            rate rewards C_star C_h n z -
            ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) := by
        have hcutLaunch :
            ReferenceSourcePrefixHistoryFiltration.actualLaunchBy rate rewards C_star C_h
              (ReferenceFirstCollectionPrecallCalendarSupport.cutBoundary
                rate rewards C_star C_h n z) z := hlaunch
        rw [htake, ite_eq_left hcutLaunch] at hcells
        exact (Option.some.inj hcells).symm
      have hprefix :
          (RecordedQueueRun.run Q
            (Lterm.take
              (ReferenceFirstCollectionPrecallCalendarSupport.cutBoundary
                rate rewards C_star C_h n z -
                ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h))).overflow = true := by
        simpa only [hlist] using hoverflow
      have hprefixExec :
          (RecordedQueueRun.execute Q
            (Lterm.take
              (ReferenceFirstCollectionPrecallCalendarSupport.cutBoundary
                rate rewards C_star C_h n z -
                ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h))
            (RecordedQueueRun.initialState p.K)).overflow = true := by
        simpa [RecordedQueueRun.run, RecordedQueueRun.initialState] using hprefix
      have hfull : (RecordedQueueRun.run Q Lterm).overflow = true := by
        unfold RecordedQueueRun.run
        rw [← List.take_append_drop
          (ReferenceFirstCollectionPrecallCalendarSupport.cutBoundary
            rate rewards C_star C_h n z -
            ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) Lterm,
          execute_append]
        exact (RecordedQueueRun.execute_after_overflow_preserves Q
          (Lterm.drop
            (ReferenceFirstCollectionPrecallCalendarSupport.cutBoundary
              rate rewards C_star C_h n z -
              ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h))
          (RecordedQueueRun.execute Q
            (Lterm.take
              (ReferenceFirstCollectionPrecallCalendarSupport.cutBoundary
                rate rewards C_star C_h n z -
                ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h))
            (RecordedQueueRun.initialState p.K)) hprefixExec).1
      obtain ⟨a, hbacklog⟩ :=
        (StoppedQueueBound.run_overflow_iff_terminal_threshold Q Lterm).1 hfull
      rw [terminalThreshold, Set.mem_iUnion]
      refine ⟨a, ?_⟩
      change cap <
        ReferenceFirstCollectionPrecallCalendarSupport.precallBacklog
          rate rewards C_star C_h p.T a z
      simpa [ReferenceFirstCollectionPrecallCalendarSupport.precallBacklog, hterminal,
        ReferenceFirstLaunchNumericalCell.queueParameters] using hbacklog
  · intro hthreshold
    obtain ⟨a, hbacklog⟩ := by
      rw [terminalThreshold, Set.mem_iUnion] at hthreshold
      exact hthreshold
    rcases ReferenceFirstCollectionPrecallCalendarSupport.precallPrefix_support
        rate rewards C_star C_h p.T le_rfl z with hnone |
      ⟨_, L, hcells, _, _, _⟩
    · have hzero := hnone.2
      change cap < ReferenceFirstCollectionPrecallCalendarSupport.precallBacklog
        rate rewards C_star C_h p.T a z at hbacklog
      have hbacklog0 : cap < 0 := by
        simpa [ReferenceFirstCollectionPrecallCalendarSupport.precallBacklog, hzero]
          using hbacklog
      have hcap : 0 < cap := by
        exact one_div_pos.mpr (mul_pos (by norm_num) rate.eta.property)
      exact False.elim (not_lt_of_ge (le_of_lt hcap) hbacklog0)
    · have hrun : (RecordedQueueRun.run Q L).overflow = true := by
        have hbacklog' :
            StoppedQueueBound.normalizedBacklog Q (RecordedQueueRun.run Q L) a >
              1 / (32 * (ReferenceFirstLaunchNumericalCell.queueParameters rate).eta) := by
          have hnorm : cap < StoppedQueueBound.normalizedBacklog Q
              (RecordedQueueRun.run Q L) a := by
            simpa [ReferenceFirstCollectionPrecallCalendarSupport.precallBacklog, hcells] using
              hbacklog
          simpa [ReferenceFirstLaunchNumericalCell.queueParameters] using hnorm
        exact (StoppedQueueBound.run_overflow_iff_terminal_threshold Q L).2
          ⟨a, hbacklog'⟩
      exact ⟨p.T, le_rfl, L, hcells, hrun⟩

/-- The exact canonical scale converts the printed normalized threshold to
the stability logarithm. -/
theorem beta_mul_cap_eq_Lstab : beta * cap = Lstab := by
  rw [CanonicalRecordingRates.beta]
  field_simp [ne_of_gt rate.eta.property]

/-- The terminal backlog event is exactly the union of the corresponding
literal exponential threshold events. -/
theorem terminalThreshold_eq_exponential :
    terminalThreshold rate rewards C_star C_h =
      ⋃ a : Fin p.K,
        {z | Real.exp Lstab <
          ReferenceFirstCollectionPrecallIncomingExponentialEnvelope.Y
            rate rewards C_star C_h a p.T z} := by
  ext z
  simp only [terminalThreshold, Set.mem_iUnion]
  constructor
  · rintro ⟨a, hbacklog⟩
    refine ⟨a, ?_⟩
    have hbeta : 0 < beta := CanonicalRecordingRates.beta_pos p rate.eta.property
    have hmul := mul_lt_mul_of_pos_left hbacklog hbeta
    rw [beta_mul_cap_eq_Lstab] at hmul
    simpa [ReferenceFirstCollectionPrecallIncomingExponentialEnvelope.Y] using
      (Real.exp_lt_exp.mpr hmul)
  · rintro ⟨a, hexp⟩
    refine ⟨a, ?_⟩
    have hbeta : 0 < beta := CanonicalRecordingRates.beta_pos p rate.eta.property
    have hmul := (Real.exp_lt_exp.mp (by
      simpa [ReferenceFirstCollectionPrecallIncomingExponentialEnvelope.Y] using hexp))
    rw [← beta_mul_cap_eq_Lstab rate] at hmul
    exact lt_of_mul_lt_mul_left hmul hbeta.le

/-- Measurability is inherited from the literal terminal scalar on the
original continuous source space. -/
theorem measurableSet_terminalThreshold (control0 : TimeControl p) :
    MeasurableSet (terminalThreshold rate rewards C_star C_h) := by
  rw [terminalThreshold_eq_exponential rate rewards C_star C_h]
  apply MeasurableSet.iUnion
  intro a
  exact measurableSet_lt measurable_const
    (ReferenceFirstCollectionPrecallIncomingExponentialEnvelope.Y_measurable
      rate rewards C_star C_h a control0 p.T le_rfl)

/-- The literal optional-prefix event is measurable on the original source
space; no measurability of a variable whole-list readout is assumed. -/
theorem measurableSet_precallOverflow (control0 : TimeControl p) :
    MeasurableSet (precallOverflow rate rewards C_star C_h) := by
  rw [precallOverflow_eq_terminalThreshold rate rewards C_star C_h]
  exact measurableSet_terminalThreshold rate rewards C_star C_h control0

/-- One terminal arm's strict threshold has the Markov bound from the
accepted incoming exponential envelope. -/
private theorem terminalArm_measureReal_le_exp (control0 : TimeControl p)
    (a : Fin p.K) :
    (sourceInputLaw p).real {z | cap < ReferenceFirstCollectionPrecallCalendarSupport.precallBacklog
        rate rewards C_star C_h p.T a z} ≤
      ((p.T : ℝ) + 1) * Real.exp (-Lstab) := by
  have hbeta : 0 < beta := CanonicalRecordingRates.beta_pos p rate.eta.property
  have hscale := beta_mul_cap_eq_Lstab rate
  let expBacklog (z : S) :=
    ReferenceFirstCollectionPrecallIncomingExponentialEnvelope.Y
      rate rewards C_star C_h a p.T z
  let expLevel := Real.exp Lstab
  let highSet := {z : S | expLevel ≤ expBacklog z}
  have hsubset :
      {z | cap < ReferenceFirstCollectionPrecallCalendarSupport.precallBacklog
        rate rewards C_star C_h p.T a z} ⊆ highSet := by
    intro z hz
    have hmul := mul_lt_mul_of_pos_left hz hbeta
    rw [hscale] at hmul
    change expLevel ≤ expBacklog z
    exact Real.exp_le_exp.mpr hmul.le
  have hnonneg : 0 ≤ᵐ[sourceInputLaw p] expBacklog :=
    Filter.Eventually.of_forall (fun z => Real.exp_nonneg _)
  have hintegrable : Integrable expBacklog (sourceInputLaw p) := by
    exact ReferenceFirstCollectionPrecallIncomingExponentialEnvelope.Y_integrable
      rate rewards C_star C_h a control0 p.T le_rfl
  have hmarkov := mul_meas_ge_le_integral_of_nonneg hnonneg hintegrable expLevel
  have hintegral :=
    ReferenceFirstCollectionPrecallIncomingExponentialEnvelope.integral_Y_terminal
      rate rewards C_star C_h a control0
  have hhigh : (sourceInputLaw p).real highSet ≤ ((p.T : ℝ) + 1) / expLevel := by
    apply (le_div_iff₀ (Real.exp_pos _)).2
    have hmarkov' : expLevel * (sourceInputLaw p).real highSet ≤ (p.T : ℝ) + 1 := by
      simpa only [highSet, expLevel, expBacklog] using hmarkov.trans hintegral
    nlinarith [hmarkov']
  calc
    (sourceInputLaw p).real {z | cap <
        ReferenceFirstCollectionPrecallCalendarSupport.precallBacklog
          rate rewards C_star C_h p.T a z} ≤ (sourceInputLaw p).real highSet :=
      measureReal_mono hsubset
    _ ≤ ((p.T : ℝ) + 1) / expLevel := hhigh
    _ = ((p.T : ℝ) + 1) * Real.exp (-Lstab) := by
      dsimp [expLevel]
      rw [Real.exp_neg, div_eq_mul_inv]

/-- The literal pre-call event obeys the finite-arm exponential tail. The
single terminal envelope charges `T+1` once per arm, not once per prefix. -/
theorem precallOverflow_measureReal_le_exp (control0 : TimeControl p) :
    (sourceInputLaw p).real (precallOverflow rate rewards C_star C_h) ≤
      (p.K : ℝ) * ((p.T : ℝ) + 1) * Real.exp (-Lstab) := by
  rw [precallOverflow_eq_terminalThreshold rate rewards C_star C_h]
  calc
    (sourceInputLaw p).real (terminalThreshold rate rewards C_star C_h) ≤
        ∑ a : Fin p.K, (sourceInputLaw p).real {z | cap <
          ReferenceFirstCollectionPrecallCalendarSupport.precallBacklog
            rate rewards C_star C_h p.T a z} :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ a : Fin p.K, ((p.T : ℝ) + 1) * Real.exp (-Lstab) := by
      apply Finset.sum_le_sum
      intro a _
      exact terminalArm_measureReal_le_exp rate rewards C_star C_h control0 a
    _ = (p.K : ℝ) * ((p.T : ℝ) + 1) * Real.exp (-Lstab) := by
      simp [Finset.sum_const, nsmul_eq_mul, mul_assoc]

/-- The canonical logarithm gives the printed inverse-square tail scale. -/
theorem precallOverflow_measureReal_le_inv_N_sq (control0 : TimeControl p) :
    (sourceInputLaw p).real (precallOverflow rate rewards C_star C_h) ≤
      1 / (N p : ℝ) ^ 2 := by
  have hExp := precallOverflow_measureReal_le_exp rate rewards C_star C_h control0
  have hArgNat : 0 < 2 * p.K * (p.T + 1) * (N p) ^ 2 := by
    exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by decide)
      (ConstructorDimensions.K_pos p)) (Nat.zero_lt_succ p.T))
      (Nat.pow_pos (ConstructorDimensions.N_pos p))
  have hlog := CanonicalRecordingRates.log_stabArgument_le_L_stab p
  have hexpNat :
      (((2 * p.K * (p.T + 1) * (N p) ^ 2 : ℕ) : ℝ)) ≤ Real.exp Lstab := by
    have hexp := Real.exp_le_exp.mpr hlog
    rw [Real.exp_log (by exact_mod_cast hArgNat)] at hexp
    exact hexp
  have hK : 0 < (p.K : ℝ) := Nat.cast_pos.mpr (ConstructorDimensions.K_pos p)
  have hT : 0 < (p.T : ℝ) + 1 := by positivity
  have hN : 0 < (N p : ℝ) := Nat.cast_pos.mpr (ConstructorDimensions.N_pos p)
  have hN2 : 0 < (N p : ℝ) ^ 2 := sq_pos_of_pos hN
  have hden : 0 < Real.exp Lstab := Real.exp_pos _
  have hlarge :
      ((p.K : ℝ) * ((p.T : ℝ) + 1)) * (N p : ℝ) ^ 2 ≤ Real.exp Lstab := by
    have hcast :
        2 * (p.K : ℝ) * ((p.T : ℝ) + 1) * (N p : ℝ) ^ 2 ≤ Real.exp Lstab := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one,
        Nat.cast_pow] using hexpNat
    nlinarith
  have hnum :
      ((p.K : ℝ) * ((p.T : ℝ) + 1)) * Real.exp (-Lstab) ≤
        1 / (N p : ℝ) ^ 2 := by
    rw [Real.exp_neg]
    field_simp [ne_of_gt hden, ne_of_gt hN2]
    nlinarith [hlarge]
  exact hExp.trans hnum

/-- No actual initialization launch means there is no pre-call overflow
event; scalar zero localization is used only to discharge the threshold. -/
theorem not_mem_precallOverflow_of_no_launch (z : S)
    (hnone : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h = none) :
    z ∉ precallOverflow rate rewards C_star C_h := by
  intro hz
  rw [precallOverflow_eq_terminalThreshold rate rewards C_star C_h] at hz
  rcases (by
    rw [terminalThreshold, Set.mem_iUnion] at hz
    exact hz) with ⟨a, hbacklog⟩
  have hzero := ReferenceFirstCollectionPrecallCalendarSupport.precallPrefix_no_launch
    rate rewards C_star C_h z hnone p.T a
  change cap < ReferenceFirstCollectionPrecallCalendarSupport.precallBacklog
    rate rewards C_star C_h p.T a z at hbacklog
  have hbacklog0 : cap < 0 := by
    rw [ReferenceFirstCollectionPrecallCalendarSupport.precallBacklog, hzero.1] at hbacklog
    exact hbacklog
  have hcap : 0 < cap := by
    exact one_div_pos.mpr (mul_pos (by norm_num) rate.eta.property)
  exact (not_lt_of_ge (le_of_lt hcap)) hbacklog0

/-- A launch at the terminal source date reads the genuine empty prefix. -/
theorem precallCells_terminal_launch (z : S)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (hs : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h = p.T) :
    ReferenceFirstCollectionPrecallCalendarSupport.precallCells?
      rate rewards C_star C_h p.T z = some [] := by
  have h := ReferenceFirstCollectionPrecallCalendarSupport.precallPrefix_terminal_launch
    rate rewards C_star C_h p.T le_rfl z hc hs
  simpa using h

/-- With no first call, terminal optional slots are precisely all original
source records through the horizon, with each actual `cell0` result intact. -/
theorem precallSlots_terminal_no_call (z : S)
    (hnone : ReferenceFirstCollectionSamplerCall.firstCollectionCall
      rate rewards C_star C_h z = none) :
    ReferenceFirstCollectionPrecallCalendarSupport.precallSlots
        rate rewards C_star C_h p.T z =
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h).map
        (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate) :=
  ReferenceFirstCollectionPrecallCalendarSupport.precallSlots_terminal_no_call
    rate rewards C_star C_h z hnone

/-- On the no-call branch, the terminal optional cell list is the `mapM`
readout of every original source record, conditional only on the actual
launch predicate already built into `precallCells?`. -/
theorem precallCells_terminal_no_call (z : S)
    (hnone : ReferenceFirstCollectionSamplerCall.firstCollectionCall
      rate rewards C_star C_h z = none) :
    ReferenceFirstCollectionPrecallCalendarSupport.precallCells?
        rate rewards C_star C_h p.T z =
      if ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
          rate rewards C_star C_h p.T z then
        ((ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h).map
          (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate)).mapM id
      else none :=
  ReferenceFirstCollectionPrecallCalendarSupport.precallCells_terminal_no_call
    rate rewards C_star C_h z hnone

/-- At a first-cell endpoint, the terminal prefix is the same existing
strict-past list read by the current before-call gate. -/
theorem precallCells_terminal_eq_pastCells_on_firstCell (u t : Fin p.T) (z : S)
    (hz : z ∈ ReferenceCalendarCollectionCallControlLaw.firstCell
      rate rewards C_star C_h u t) :
    ReferenceFirstCollectionPrecallCalendarSupport.precallCells?
      rate rewards C_star C_h p.T z =
    ReferenceFirstCollectionCurrentRetainedGate.pastCells?
      rate rewards C_star C_h t z :=
  ReferenceFirstCollectionPrecallCalendarSupport.precallCells_at_or_after_firstCell
    rate rewards C_star C_h u t p.T (Nat.le_of_lt t.isLt) z hz

/-- The terminal scalar readout on a first-call cell is exactly the source's
original current before-call readout. -/
theorem precallReadout_terminal_eq_before_on_firstCell (u t : Fin p.T) (a : Fin p.K)
    (z : S)
    (hz : z ∈ ReferenceCalendarCollectionCallControlLaw.firstCell
      rate rewards C_star C_h u t) :
    ReferenceFirstCollectionPrecallCalendarSupport.precallReadout?
      rate rewards C_star C_h p.T z =
    ReferenceFirstCollectionCurrentQueueReadout.before?
      rate rewards C_star C_h t z := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hreadout, _⟩ :=
    ReferenceFirstCollectionPrecallCalendarSupport.precallPrefix_terminal_on_firstCell
      rate rewards C_star C_h u t a z hz
  exact hreadout

/-- Overflow on a first-call cell has a genuine processed original source
update before that invocation. The index is in the actual terminal list, and
its one-based source date is at most `t.val`. -/
theorem firstCell_overflow_has_processed_preCall_update (u t : Fin p.T) (z : S)
    (hzCell : z ∈ ReferenceCalendarCollectionCallControlLaw.firstCell
      rate rewards C_star C_h u t)
    (hzOverflow : z ∈ precallOverflow rate rewards C_star C_h) :
    ∃ (L : List (RecordedQueueRun.RoundInput p.K)) (k : Fin L.length)
      (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)),
      ReferenceFirstCollectionPrecallCalendarSupport.precallCells?
          rate rewards C_star C_h p.T z = some L ∧
      (RecordedQueueRun.run Q (L.take (k.val + 1))).overflow = true ∧
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[k.val]? = some r ∧
      r.input.time.val =
        ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + k.val ∧
      r.input.time.val + 1 ≤ t.val := by
  obtain ⟨_, _, _, _, _, _, D, L, _, _, _, hPast, hlength, _, _, _⟩ :=
    ReferenceFirstCollectionPrecallCalendarSupport.precallPrefix_firstCell_chronology
      rate rewards C_star C_h u t z hzCell
  have hterminal :
      ReferenceFirstCollectionPrecallCalendarSupport.precallCells?
        rate rewards C_star C_h p.T z = some L := by
    rw [ReferenceFirstCollectionPrecallCalendarSupport.precallCells_at_or_after_firstCell
      rate rewards C_star C_h u t p.T (Nat.le_of_lt t.isLt) z hzCell]
    exact hPast
  have hlaunch :
      ReferenceSourcePrefixHistoryFiltration.actualLaunchBy rate rewards C_star C_h
        (ReferenceFirstCollectionPrecallCalendarSupport.cutBoundary
          rate rewards C_star C_h p.T z) z := by
    by_contra hnot
    have hnone := ReferenceFirstCollectionPrecallCalendarSupport.precallCells_no_launch
      rate rewards C_star C_h p.T z hnot
    rw [hnone] at hterminal
    cases hterminal
  obtain ⟨L', hterminal', hlength', _, hslot⟩ :=
    ReferenceFirstCollectionPrecallCalendarSupport.precallPrefix_present
      rate rewards C_star C_h p.T le_rfl z hlaunch
  have hLists : L' = L := Option.some.inj (hterminal'.symm.trans hterminal)
  subst L'
  have hfull : (RecordedQueueRun.run Q L).overflow = true := by
    rw [precallOverflow_eq_terminalThreshold rate rewards C_star C_h] at hzOverflow
    obtain ⟨a, hbacklog⟩ := by
      rw [terminalThreshold, Set.mem_iUnion] at hzOverflow
      exact hzOverflow
    have hnormal : StoppedQueueBound.normalizedBacklog Q
        (RecordedQueueRun.run Q L) a >
          1 / (32 * (ReferenceFirstLaunchNumericalCell.queueParameters rate).eta) := by
      have hnorm : cap < StoppedQueueBound.normalizedBacklog Q
          (RecordedQueueRun.run Q L) a := by
        simpa [ReferenceFirstCollectionPrecallCalendarSupport.precallBacklog, hterminal] using
          hbacklog
      simpa [ReferenceFirstLaunchNumericalCell.queueParameters] using hnorm
    exact (StoppedQueueBound.run_overflow_iff_terminal_threshold Q L).2
      ⟨a, hnormal⟩
  obtain ⟨j, hj, hprefix⟩ :=
    (StoppedQueueBound.run_overflow_iff_exists_prefix_overflow Q L).mp hfull
  obtain ⟨r, hr, hdate, _⟩ := hslot ⟨j, hj⟩
  refine ⟨L, ⟨j, hj⟩, r, hterminal, hprefix, ?_, ?_, ?_⟩
  · exact hr
  · exact hdate
  · rw [hlength] at hj
    omega

end Bandits.Support.ReferenceFirstCollectionPrecallOverflowBound

end
