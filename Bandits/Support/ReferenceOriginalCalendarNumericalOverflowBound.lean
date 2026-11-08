/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceOriginalCalendarBirthExcessEnergyReduction
public import Bandits.Support.ReferenceOriginalCalendarBirthBranchIncrementTransport
public import Bandits.Support.ReferenceCompletePhysicalCalendarFirstCrossing

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic

/-!
# Original-calendar carried-energy expectation and overflow tail

The same-date renewed-birth event and increment from the excess-energy
reduction are identified with the selected branch transport. Its actual
successful-event mass cancels the signed excess on the unrestricted original
source law. The resulting terminal exponential moment controls both the
original numerical detector and its deterministic complete-physical-calendar
first-crossing event.
-/

@[expose] public section

noncomputable section

open MeasureTheory Bandits.Support ConstructorDimensions
open BootstrapPrivateRoundStreams (SourceInput sourceInputLaw)
open ReferenceActivePhysicalStep (RateInput)
open ActualInitializationPhysicalStep (GridRewardTable)
open ContinuousLearningRows (TimeControl)
open scoped Classical BigOperators

namespace Bandits.Support.ReferenceOriginalCalendarNumericalOverflowBound

variable {p : Parameters}
variable (rate : RateInput p) (rewards : GridRewardTable p)
  (C_star C_h : ℝ) (control0 : TimeControl p)

local notation "X" => SourceInput p
local notation "μ" => sourceInputLaw p
local notation "CE" =>
  ReferenceOriginalCalendarCarriedStoppedEnergy.carriedStoppedEnergy
    rate rewards C_star C_h

/-- The actual same-date birth increment and selected branch event are the
literal same indicator and carried-energy difference in the two public roots. -/
private theorem activeBirthIncrement_eq_selected_increment
    (a : Fin p.K) (q : Fin p.T) :
    ReferenceOriginalCalendarBirthExcessEnergyReduction.activeBirthIncrement
        rate rewards C_star C_h a q =
      (ReferenceOriginalCalendarBirthBranchIncrementTransport.renewedBirthActiveUpdateSet
        rate rewards C_star C_h q).indicator
        (fun z => CE (q.val + 1) a z - CE q.val a z) := by
  rfl

include control0 in
/-- Every actual original-calendar prefix has the source-law exponential
moment bound after cancellation of the signed renewed-birth excesses. -/
public theorem integral_carriedStoppedEnergy_prefix_le
    (n : ℕ) (hn : n ≤ p.T) (a : Fin p.K) :
    (∫ z : X, CE n a z ∂μ) ≤ (n : ℝ) + 1 := by
  have hprefix :=
    ReferenceOriginalCalendarBirthExcessEnergyReduction.integral_carriedStoppedEnergy_prefix_le_birth_excess
      rate rewards C_star C_h control0 a n hn
  have hsum :
      ∑ q ∈ Finset.univ.filter (fun q : Fin p.T => q.val < n),
        ((∫ z : X,
            ReferenceOriginalCalendarBirthExcessEnergyReduction.activeBirthIncrement
              rate rewards C_star C_h a q z ∂μ) -
          (sourceInputLaw p).real (ReferenceOriginalCalendarBirthExcessEnergyReduction.activeBirthEvent
            rate rewards C_star C_h q)) ≤ 0 := by
    apply Finset.sum_nonpos
    intro q _
    have hsameEvent :
        ReferenceOriginalCalendarBirthExcessEnergyReduction.activeBirthEvent
            rate rewards C_star C_h q =
          ReferenceOriginalCalendarBirthBranchIncrementTransport.renewedBirthActiveUpdateSet
            rate rewards C_star C_h q := by
      rfl
    have hsameIncrement :=
      activeBirthIncrement_eq_selected_increment rate rewards C_star C_h a q
    have hmass :=
      ReferenceOriginalCalendarBirthBranchIncrementTransport.renewedBirthActiveUpdate_carriedIncrement_integral_le_mass
        rate rewards C_star C_h control0 q a
    have hselectedMeasurable :
        MeasurableSet
          (ReferenceOriginalCalendarBirthBranchIncrementTransport.renewedBirthActiveUpdateSet
            rate rewards C_star C_h q) := by
      rw [← hsameEvent]
      exact ReferenceOriginalCalendarBirthExcessEnergyReduction.measurableSet_activeBirthEvent
        rate rewards C_star C_h q
    have hmassIntegral :
        (∫ z : X,
          (ReferenceOriginalCalendarBirthBranchIncrementTransport.renewedBirthActiveUpdateSet
            rate rewards C_star C_h q).indicator (fun _ => (1 : ℝ)) z ∂μ) =
          (sourceInputLaw p).real
            (ReferenceOriginalCalendarBirthBranchIncrementTransport.renewedBirthActiveUpdateSet
              rate rewards C_star C_h q) := by
      rw [integral_indicator_const (1 : ℝ) hselectedMeasurable]
      simp only [smul_eq_mul, mul_one]
    have hmass' := hmass.1
    rw [hmassIntegral] at hmass'
    change
      (∫ z : X,
        ReferenceOriginalCalendarBirthExcessEnergyReduction.activeBirthIncrement
          rate rewards C_star C_h a q z ∂μ) -
        (sourceInputLaw p).real (ReferenceOriginalCalendarBirthExcessEnergyReduction.activeBirthEvent
          rate rewards C_star C_h q) ≤ 0
    rw [hsameIncrement, hsameEvent]
    exact sub_nonpos.mpr hmass'
  exact hprefix.trans (by linarith)

private theorem beta_mul_backlogCap_eq_L_stab :
    CanonicalRecordingRates.beta p rate.eta.val *
        ReferenceOriginalCalendarCarriedStoppedEnergy.backlogCap rate =
      (CanonicalRecordingRates.L_stab p : ℝ) := by
  rw [CanonicalRecordingRates.beta,
    ReferenceOriginalCalendarCarriedStoppedEnergy.backlogCap]
  field_simp [ne_of_gt rate.eta.property]

include control0 in
private theorem terminalArm_measureReal_le_exp
    (a : Fin p.K) :
    (sourceInputLaw p).real {z : X |
      Real.exp (CanonicalRecordingRates.beta p rate.eta.val *
        ReferenceOriginalCalendarCarriedStoppedEnergy.backlogCap rate) <
        CE p.T a z} ≤
      ((p.T : ℝ) + 1) *
        Real.exp (-(CanonicalRecordingRates.L_stab p : ℝ)) := by
  let level := Real.exp (CanonicalRecordingRates.L_stab p : ℝ)
  have hscale := beta_mul_backlogCap_eq_L_stab rate
  have hlevel :
      Real.exp (CanonicalRecordingRates.beta p rate.eta.val *
        ReferenceOriginalCalendarCarriedStoppedEnergy.backlogCap rate) = level := by
    exact congrArg Real.exp hscale
  have hsubset :
      {z : X | Real.exp (CanonicalRecordingRates.beta p rate.eta.val *
          ReferenceOriginalCalendarCarriedStoppedEnergy.backlogCap rate) <
          CE p.T a z} ⊆ {z : X | level ≤ CE p.T a z} := by
    intro z hz
    change Real.exp (CanonicalRecordingRates.beta p rate.eta.val *
      ReferenceOriginalCalendarCarriedStoppedEnergy.backlogCap rate) <
      CE p.T a z at hz
    rw [hlevel] at hz
    exact hz.le
  have hnonneg : 0 ≤ᵐ[μ] CE p.T a := by
    filter_upwards with z
    have hbound :=
      ReferenceOriginalCalendarCarriedStoppedEnergy.carriedStoppedEnergy_bounds
        rate rewards C_star C_h p.T le_rfl a z
    exact le_trans (by norm_num) hbound.1
  have hintegrable :=
    ReferenceOriginalCalendarCarriedStoppedEnergy.integrable_carriedStoppedEnergy
      rate rewards C_star C_h p.T le_rfl a
  have hmarkov := mul_meas_ge_le_integral_of_nonneg hnonneg hintegrable level
  have hhigh : (sourceInputLaw p).real {z : X | level ≤ CE p.T a z} ≤
      ((p.T : ℝ) + 1) / level := by
    apply (le_div_iff₀ (Real.exp_pos _)).2
    have hmarkov' :
        level * (sourceInputLaw p).real {z : X | level ≤ CE p.T a z} ≤ (p.T : ℝ) + 1 := by
      have hterminal :=
        integral_carriedStoppedEnergy_prefix_le rate rewards C_star C_h
          control0 p.T le_rfl a
      simpa only [level] using hmarkov.trans hterminal
    nlinarith [hmarkov']
  calc
    (sourceInputLaw p).real {z : X | Real.exp (CanonicalRecordingRates.beta p rate.eta.val *
        ReferenceOriginalCalendarCarriedStoppedEnergy.backlogCap rate) <
        CE p.T a z} ≤ (sourceInputLaw p).real {z : X | level ≤ CE p.T a z} :=
      measureReal_mono hsubset
    _ ≤ ((p.T : ℝ) + 1) / level := hhigh
    _ = ((p.T : ℝ) + 1) *
        Real.exp (-(CanonicalRecordingRates.L_stab p : ℝ)) := by
      dsimp [level]
      rw [Real.exp_neg, div_eq_mul_inv]

/-- Borelness of the actual first numerical overflow event on the unrestricted
original source-input space. -/
public theorem measurableSet_observedNumericalOverflowEvent :
    MeasurableSet
      (ReferenceOriginalNumericalFirstOverflowLocator.observedNumericalOverflowEvent
        rate rewards C_star C_h) :=
  ReferenceOriginalNumericalFirstOverflowLocator.measurableSet_observedNumericalOverflowEvent
    rate rewards C_star C_h

include control0 in
/-- The actual original-calendar detector has one terminal Markov charge per
arm, with no additional prefix union factor. -/
public theorem observedNumericalOverflowEvent_measureReal_le_exp :
    (sourceInputLaw p).real
      (ReferenceOriginalNumericalFirstOverflowLocator.observedNumericalOverflowEvent
        rate rewards C_star C_h) ≤
      (p.K : ℝ) * ((p.T : ℝ) + 1) *
        Real.exp (-(CanonicalRecordingRates.L_stab p : ℝ)) := by
  rw [ReferenceOriginalCalendarCarriedStoppedEnergy.observedNumericalOverflowEvent_eq_terminalCarriedEnergy
    rate rewards C_star C_h]
  have hUnion :
      {z : X | ∃ a : Fin p.K,
          Real.exp (CanonicalRecordingRates.beta p rate.eta.val *
            ReferenceOriginalCalendarCarriedStoppedEnergy.backlogCap rate) <
            CE p.T a z} =
        ⋃ a : Fin p.K, {z : X |
          Real.exp (CanonicalRecordingRates.beta p rate.eta.val *
            ReferenceOriginalCalendarCarriedStoppedEnergy.backlogCap rate) <
            CE p.T a z} := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
  rw [hUnion]
  calc
    (sourceInputLaw p).real (⋃ a : Fin p.K, {z : X |
        Real.exp (CanonicalRecordingRates.beta p rate.eta.val *
          ReferenceOriginalCalendarCarriedStoppedEnergy.backlogCap rate) <
          CE p.T a z}) ≤
        ∑ a : Fin p.K, (sourceInputLaw p).real {z : X |
          Real.exp (CanonicalRecordingRates.beta p rate.eta.val *
            ReferenceOriginalCalendarCarriedStoppedEnergy.backlogCap rate) <
            CE p.T a z} := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _a : Fin p.K,
        ((p.T : ℝ) + 1) *
          Real.exp (-(CanonicalRecordingRates.L_stab p : ℝ)) := by
      apply Finset.sum_le_sum
      intro a _
      exact terminalArm_measureReal_le_exp rate rewards C_star C_h control0 a
    _ = (p.K : ℝ) * ((p.T : ℝ) + 1) *
        Real.exp (-(CanonicalRecordingRates.L_stab p : ℝ)) := by
      simp [Finset.sum_const, nsmul_eq_mul, mul_assoc]

include control0 in
/-- The canonical stability logarithm turns the exponential detector bound
into the source's inverse-square scale. -/
public theorem observedNumericalOverflowEvent_measureReal_le_inv_N_sq :
    (sourceInputLaw p).real
      (ReferenceOriginalNumericalFirstOverflowLocator.observedNumericalOverflowEvent
        rate rewards C_star C_h) ≤
      1 / (N p : ℝ) ^ 2 := by
  have hExp :=
    observedNumericalOverflowEvent_measureReal_le_exp rate rewards C_star C_h control0
  have hArgNat :
      0 < 2 * p.K * (p.T + 1) * (N p) ^ 2 := by
    exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by decide)
      (ConstructorDimensions.K_pos p)) (Nat.zero_lt_succ p.T))
      (Nat.pow_pos (ConstructorDimensions.N_pos p))
  have hlog := CanonicalRecordingRates.log_stabArgument_le_L_stab p
  have hexpNat :
      (((2 * p.K * (p.T + 1) * (N p) ^ 2 : ℕ) : ℝ)) ≤
        Real.exp (CanonicalRecordingRates.L_stab p : ℝ) := by
    have hexp := Real.exp_le_exp.mpr hlog
    rw [Real.exp_log (by exact_mod_cast hArgNat)] at hexp
    exact hexp
  have hK : 0 < (p.K : ℝ) := Nat.cast_pos.mpr (ConstructorDimensions.K_pos p)
  have hT : 0 < (p.T : ℝ) + 1 := by positivity
  have hN : 0 < (N p : ℝ) := Nat.cast_pos.mpr (ConstructorDimensions.N_pos p)
  have hN2 : 0 < (N p : ℝ) ^ 2 := sq_pos_of_pos hN
  have hden : 0 < Real.exp (CanonicalRecordingRates.L_stab p : ℝ) := Real.exp_pos _
  have hlarge :
      ((p.K : ℝ) * ((p.T : ℝ) + 1)) * (N p : ℝ) ^ 2 ≤
        Real.exp (CanonicalRecordingRates.L_stab p : ℝ) := by
    have hcast :
        2 * (p.K : ℝ) * ((p.T : ℝ) + 1) * (N p : ℝ) ^ 2 ≤
          Real.exp (CanonicalRecordingRates.L_stab p : ℝ) := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one,
        Nat.cast_pow] using hexpNat
    nlinarith
  have hnum :
      ((p.K : ℝ) * ((p.T : ℝ) + 1)) *
          Real.exp (-(CanonicalRecordingRates.L_stab p : ℝ)) ≤
        1 / (N p : ℝ) ^ 2 := by
    rw [Real.exp_neg]
    field_simp [ne_of_gt hden, ne_of_gt hN2]
    nlinarith [hlarge]
  exact hExp.trans hnum

/-- The complete-suffix physical integer first-crossing event is Borel under
the same unrestricted original source-input law. -/
public theorem measurableSet_physicalFirstOverflowEvent :
    MeasurableSet
      (ReferenceCompletePhysicalCalendarFirstCrossing.physicalFirstOverflowEvent
        rate rewards C_star C_h) := by
  rw [ReferenceCompletePhysicalCalendarFirstCrossing.physicalFirstOverflowEvent_eq_observedNumericalOverflowEvent
      rate rewards C_star C_h]
  exact measurableSet_observedNumericalOverflowEvent rate rewards C_star C_h

include control0 in
/-- The complete-suffix physical first-crossing event inherits the same
single-terminal exponential tail through the accepted deterministic bridge. -/
public theorem physicalFirstOverflowEvent_measureReal_le_exp :
    (sourceInputLaw p).real
      (ReferenceCompletePhysicalCalendarFirstCrossing.physicalFirstOverflowEvent
        rate rewards C_star C_h) ≤
      (p.K : ℝ) * ((p.T : ℝ) + 1) *
        Real.exp (-(CanonicalRecordingRates.L_stab p : ℝ)) := by
  rw [ReferenceCompletePhysicalCalendarFirstCrossing.physicalFirstOverflowEvent_eq_observedNumericalOverflowEvent
      rate rewards C_star C_h]
  exact observedNumericalOverflowEvent_measureReal_le_exp
    rate rewards C_star C_h control0

include control0 in
/-- The complete-suffix physical first-crossing event has the same
inverse-square tail under the original source-input law. -/
public theorem physicalFirstOverflowEvent_measureReal_le_inv_N_sq :
    (sourceInputLaw p).real
      (ReferenceCompletePhysicalCalendarFirstCrossing.physicalFirstOverflowEvent
        rate rewards C_star C_h) ≤
      1 / (N p : ℝ) ^ 2 := by
  rw [ReferenceCompletePhysicalCalendarFirstCrossing.physicalFirstOverflowEvent_eq_observedNumericalOverflowEvent
      rate rewards C_star C_h]
  exact observedNumericalOverflowEvent_measureReal_le_inv_N_sq
    rate rewards C_star C_h control0

end Bandits.Support.ReferenceOriginalCalendarNumericalOverflowBound

end
