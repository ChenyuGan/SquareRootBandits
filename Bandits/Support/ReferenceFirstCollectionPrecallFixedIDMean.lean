/-
Copyright (c) 2026 Bandits Lean formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFixedIDSourceSection
public import Bandits.Support.ReferenceFirstLiveRetainedIDExponentialStep

import Mathlib.Tactic

/-!
# Fixed-ID pre-first-invocation overflow mean

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:140-188,245-290`,
`06_interruptions.tex:355-426`, `07_public_setup.tex:123-164`, and
`08_main_theorem.tex:26-75,111-130`.

The original-ID cylinder is retained in both calendar increments. Their
combined mass is bounded by that same cylinder's mass, before normalization
by its positive finite ID atom. A single terminal Markov estimate per arm
then bounds the existing selected-index private complete-row mean.

These internal estimates concern only overflow before the first invocation.
The named consumers are the precall-row-tail mean-plus-deviation assembly
and the product public-cost decomposition. No manuscript closure is claimed.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators Classical

namespace Bandits.Support.ReferenceFirstCollectionPrecallFixedIDMean

open ConstructorDimensions (Parameters N)
open ReferenceActivePhysicalStep (RateInput)
open ActualInitializationPhysicalStep (GridRewardTable)
open BootstrapPrivateRoundStreams (SourceInput sourceInputLaw)
open ContinuousLearningRows (TimeControl)

variable {p : Parameters}
  (rate : RateInput p) (rewards : GridRewardTable p)
  (C_star C_h : ℝ) (control0 : TimeControl p)
  (ids : CompletePublicTable.IDArray p)

local notation "S" => SourceInput p
local notation "mu" => sourceInputLaw p
local notation "D" => ReferenceFixedIDSourceSection.fixedIDSourceSection ids
local notation "kappa" => ReferenceFixedIDSourceSection.fixedIDSourceLaw ids
local notation "beta" => CanonicalRecordingRates.beta p rate.eta.val
local notation "Lstab" => (CanonicalRecordingRates.L_stab p : ℝ)
local notation "cap" => (1 / (32 * rate.eta.val))
local notation "Y" => ReferenceFirstCollectionPrecallIncomingExponentialEnvelope.Y rate rewards
  C_star C_h
local notation "liveExp" => fun (a : Fin p.K) (n : ℕ) (z : S) => Real.exp (beta *
  ReferenceFirstLiveCalendarPrefixReadout.firstWindowBacklogAt
    rate rewards C_star C_h a n z)
local notation "phase" => ReferenceFirstLiveSourcePhasePartition.sourcePhase
  rate rewards C_star C_h

/-- Both admitted localizations use the literal same original ID projection. -/
theorem fixedIDSourceSection_eq_originalIDSet :
    D = ReferenceFirstLiveRetainedIDExponentialStep.originalIDSet {ids} := by
  ext z
  simp only [ReferenceFixedIDSourceSection.fixedIDSourceSection,
    ReferenceFirstLiveRetainedIDExponentialStep.originalIDSet, Set.mem_ofPred_eq,
    Set.mem_singleton_iff]

/-- The ID cylinder is predictable in the existing source-prefix filtration. -/
theorem measurableSet_fixedIDSourceSection_prefix (n : ℕ) :
    MeasurableSet[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
      control0 (n + 1)] D := by
  rw [fixedIDSourceSection_eq_originalIDSet ids]
  exact ReferenceFirstLiveRetainedIDExponentialStep.measurableSet_originalIDSet_prefix
    control0 n {ids} (measurableSet_singleton ids)

include control0

/-- LIVE and retained OLD share the mass of this exact ID cylinder. In
particular, localization does not replace the available mass by one. -/
theorem fixedID_live_old_mass_le (t : Fin p.T) :
    (mu).real (D ∩ (phase t 2 ∪ phase t 3 ∪ phase t 4)) +
      (mu).real (D ∩ ReferenceFirstCollectionOldCalendarExponentialStep.G
        rate rewards C_star C_h t) ≤ (mu).real D := by
  have hD := ReferenceFixedIDSourceSection.measurable_fixedIDSourceSection ids
  have hG := ReferenceFirstCollectionPrecallLiveOldMass.measurableSet_G_ambient
    rate rewards C_star C_h t control0
  have hdisjoint : Disjoint
      (D ∩ (phase t 2 ∪ phase t 3 ∪ phase t 4))
      (D ∩ ReferenceFirstCollectionOldCalendarExponentialStep.G rate rewards C_star C_h t) := by
    apply Set.disjoint_left.mpr
    intro z hzLive hzOld
    have hE : z ∈ ReferenceFirstCollectionOldCalendarExponentialStep.E
        rate rewards C_star C_h t := hzOld.2.1.1
    exact (Set.disjoint_left.mp
      (ReferenceFirstCollectionPrecallLiveOldMass.old_event_disjoint_source_phases
        rate rewards C_star C_h t control0))
      hE hzLive.2
  calc
    _ = (mu).real ((D ∩ (phase t 2 ∪ phase t 3 ∪ phase t 4)) ∪
        (D ∩ ReferenceFirstCollectionOldCalendarExponentialStep.G rate rewards C_star C_h t)) :=
      (measureReal_union hdisjoint (hD.inter hG)).symm
    _ ≤ (mu).real D := measureReal_mono (by
      intro z hz
      rcases hz with hz | hz
      · exact hz.1
      · exact hz.1)

/-- Actual LIVE and OLD exponential increments localized on the same ID
section consume at most that section's unnormalized mass. -/
theorem setIntegral_live_add_old_increment_le_mass (a : Fin p.K) (t : Fin p.T) :
    (∫ z in D, liveExp a (t.val + 1) z - liveExp a t.val z ∂mu) +
      (∫ z in D, ReferenceFirstCollectionOldCalendarExponentialStep.Xplus
          rate rewards C_star C_h t a z -
        ReferenceFirstCollectionOldCalendarExponentialStep.Xminus
          rate rewards C_star C_h t a z ∂mu) ≤ (mu).real D := by
  have hLive := ReferenceFirstLiveRetainedIDExponentialStep.integral_exp_calendar_originalID_step
    rate rewards C_star C_h t control0 a {ids} (measurableSet_singleton ids)
  rw [← fixedIDSourceSection_eq_originalIDSet ids] at hLive
  have hOld :=
    ReferenceFirstCollectionOldCalendarExponentialStep.setIntegral_Xplus_sub_Xminus_le_G_mass
      rate rewards C_star C_h control0 t a D
      (measurableSet_fixedIDSourceSection_prefix control0 ids t.val)
  exact (add_le_add hLive hOld).trans
    (fixedID_live_old_mass_le rate rewards C_star C_h control0 ids t)

/-- Integrating the pointwise calendar recurrence on the original ID section
uses genuine integrability of each original-source summand. -/
theorem setIntegral_Y_calendar_increment (a : Fin p.K) (t : Fin p.T) :
    (∫ z in D, Y a (t.val + 1) z ∂mu) =
      (∫ z in D, Y a t.val z ∂mu) +
        (∫ z in D, liveExp a (t.val + 1) z - liveExp a t.val z ∂mu) +
        (∫ z in D, ReferenceFirstCollectionOldCalendarExponentialStep.Xplus
            rate rewards C_star C_h t a z -
          ReferenceFirstCollectionOldCalendarExponentialStep.Xminus
            rate rewards C_star C_h t a z ∂mu) := by
  have hY : Integrable (Y a t.val) ((mu).restrict D) :=
    (ReferenceFirstCollectionPrecallIncomingExponentialEnvelope.Y_integrable
      rate rewards C_star C_h a control0 t.val (Nat.le_of_lt t.isLt)).integrableOn
  have hLive : Integrable
      (fun z : S => liveExp a (t.val + 1) z - liveExp a t.val z)
      ((mu).restrict D) :=
    ((ReferenceFirstLiveCalendarPrefixReadout.integrable_firstWindowExpBacklogAt
      rate rewards C_star C_h a (t.val + 1)).sub
      (ReferenceFirstLiveCalendarPrefixReadout.integrable_firstWindowExpBacklogAt
        rate rewards C_star C_h a t.val)).integrableOn
  have hOld : Integrable
      (fun z : S => ReferenceFirstCollectionOldCalendarExponentialStep.Xplus
          rate rewards C_star C_h t a z -
        ReferenceFirstCollectionOldCalendarExponentialStep.Xminus
          rate rewards C_star C_h t a z) ((mu).restrict D) :=
    ((ReferenceFirstCollectionOldCalendarExponentialStep.Xplus_integrable
      rate rewards C_star C_h t a control0).sub
      (ReferenceFirstCollectionOldCalendarExponentialStep.Xminus_integrable
        rate rewards C_star C_h t a control0)).integrableOn
  have heq : Y a (t.val + 1) = fun z : S => Y a t.val z +
      (liveExp a (t.val + 1) z - liveExp a t.val z) +
      (ReferenceFirstCollectionOldCalendarExponentialStep.Xplus rate rewards C_star C_h t a z -
        ReferenceFirstCollectionOldCalendarExponentialStep.Xminus rate rewards C_star C_h t a z) :=
    funext (ReferenceFirstCollectionPrecallIncomingExponentialEnvelope.Y_calendar_step_eq
      rate rewards C_star C_h a t)
  rw [heq]
  exact (integral_add (hY.add hLive) hOld).trans
    (congrArg (fun x : ℝ => x +
      ∫ z in D, ReferenceFirstCollectionOldCalendarExponentialStep.Xplus
          rate rewards C_star C_h t a z -
        ReferenceFirstCollectionOldCalendarExponentialStep.Xminus
          rate rewards C_star C_h t a z ∂mu)
      (integral_add hY hLive))

/-- One actual calendar update adds at most the same original ID mass. -/
theorem setIntegral_Y_calendar_step (a : Fin p.K) (t : Fin p.T) :
    (∫ z in D, Y a (t.val + 1) z ∂mu) ≤
      (∫ z in D, Y a t.val z ∂mu) + (mu).real D := by
  rw [setIntegral_Y_calendar_increment rate rewards C_star C_h control0 ids a t]
  have h := setIntegral_live_add_old_increment_le_mass
    rate rewards C_star C_h control0 ids a t
  linarith

/-- Finite-calendar incoming envelope before normalization. Boundary zero
and the actual terminal boundary are both included. -/
theorem setIntegral_Y_calendar_le (a : Fin p.K) (n : ℕ) (hn : n ≤ p.T) :
    (∫ z in D, Y a n z ∂mu) ≤ ((n : ℝ) + 1) * (mu).real D := by
  induction n with
  | zero =>
      have heq : Y a 0 = fun _ : S => (1 : ℝ) :=
        funext (ReferenceFirstCollectionPrecallIncomingExponentialEnvelope.Y_zero
          rate rewards C_star C_h a)
      rw [heq]
      simp only [integral_const, smul_eq_mul, mul_one,
        measureReal_restrict_apply_univ, Nat.cast_zero, zero_add, one_mul, le_refl]
  | succ n ih =>
      have hnt : n < p.T := by omega
      have hprev := ih (by omega)
      have hstep := setIntegral_Y_calendar_step
        rate rewards C_star C_h control0 ids a ⟨n, hnt⟩
      calc
        _ ≤ (∫ z in D, Y a n z ∂mu) + (mu).real D := hstep
        _ ≤ ((n : ℝ) + 1) * (mu).real D + (mu).real D := add_le_add hprev le_rfl
        _ = (((n + 1 : ℕ) : ℝ) + 1) * (mu).real D := by
          push_cast
          ring

/-- Integrability under the literal fixed-ID law follows from its proved
probability instance and the measurable bounded terminal scalar, rather
than from integrability under an unrelated measure. -/
theorem fixedIDSourceLaw_Y_integrable (a : Fin p.K) (n : ℕ) (hn : n ≤ p.T) :
    Integrable (Y a n) kappa := by
  apply Integrable.of_mem_Icc 0 (Real.exp (2 * Lstab))
    (ReferenceFirstCollectionPrecallIncomingExponentialEnvelope.Y_measurable
      rate rewards C_star C_h a control0 n hn).aemeasurable
  exact ae_of_all _ (ReferenceFirstCollectionPrecallIncomingExponentialEnvelope.Y_pointwise_bound
    rate rewards C_star C_h a n hn)

/-- Divide the original restricted integral by the strictly positive REAL
ID atom. The original source restriction identity fixes the section law. -/
theorem fixedIDSourceLaw_integral_Y_calendar_le
    (a : Fin p.K) (n : ℕ) (hn : n ≤ p.T) :
    (∫ z, Y a n z ∂kappa) ≤ (n : ℝ) + 1 := by
  have h := setIntegral_Y_calendar_le rate rewards C_star C_h control0 ids a n hn
  rw [ReferenceFixedIDSourceSection.sourceInputLaw_setIntegral_fixedIDSourceSection,
    ReferenceFixedIDSourceSection.sourceInputLaw_real_fixedIDSourceSection] at h
  have hpos := ReferenceFixedIDSourceSection.idArrayAtom_positive ids
  apply (mul_le_mul_iff_right₀ hpos).mp
  simpa only [mul_comm] using h

/-- The single terminal incoming envelope under the fixed-ID law. -/
theorem fixedIDSourceLaw_integral_Y_terminal (a : Fin p.K) :
    (∫ z, Y a p.T z ∂kappa) ≤ (p.T : ℝ) + 1 :=
  fixedIDSourceLaw_integral_Y_calendar_le rate rewards C_star C_h control0 ids
    a p.T le_rfl

/-- Markov's inequality for one arm at the actual terminal boundary, under
the literal fixed-ID law and without a survival or launch premise. -/
theorem fixedIDSourceLaw_terminalArm_measureReal_le_exp (a : Fin p.K) :
    (kappa).real {z | cap < ReferenceFirstCollectionPrecallCalendarSupport.precallBacklog
      rate rewards C_star C_h p.T a z} ≤
      ((p.T : ℝ) + 1) * Real.exp (-Lstab) := by
  let expLevel := Real.exp Lstab
  let highSet := {z : S | expLevel ≤ Y a p.T z}
  have hbeta : 0 < beta := CanonicalRecordingRates.beta_pos p rate.eta.property
  have hsubset :
      {z | cap < ReferenceFirstCollectionPrecallCalendarSupport.precallBacklog
        rate rewards C_star C_h p.T a z} ⊆ highSet := by
    intro z hz
    have hmul := mul_lt_mul_of_pos_left hz hbeta
    rw [ReferenceFirstCollectionPrecallOverflowBound.beta_mul_cap_eq_Lstab rate] at hmul
    exact Real.exp_le_exp.mpr hmul.le
  have hnonneg : 0 ≤ᵐ[kappa] Y a p.T :=
    ae_of_all _ fun z => Real.exp_nonneg _
  have hmarkov := mul_meas_ge_le_integral_of_nonneg hnonneg
    (fixedIDSourceLaw_Y_integrable rate rewards C_star C_h control0 ids a p.T le_rfl)
    expLevel
  have hintegral := fixedIDSourceLaw_integral_Y_terminal
    rate rewards C_star C_h control0 ids a
  have hhigh : (kappa).real highSet ≤ ((p.T : ℝ) + 1) / expLevel := by
    apply (le_div_iff₀ (Real.exp_pos _)).2
    have hm : expLevel * (kappa).real highSet ≤ (p.T : ℝ) + 1 :=
      hmarkov.trans hintegral
    nlinarith only [hm]
  calc
    _ ≤ (kappa).real highSet := measureReal_mono hsubset
    _ ≤ ((p.T : ℝ) + 1) / expLevel := hhigh
    _ = ((p.T : ℝ) + 1) * Real.exp (-Lstab) := by
      dsimp only [expLevel]
      rw [Real.exp_neg, div_eq_mul_inv]

/-- Only the finite arm union is charged, using one terminal envelope per
arm. There is no union over dates. -/
theorem fixedIDSourceLaw_precallOverflow_measureReal_le_exp :
    (kappa).real (ReferenceFirstCollectionPrecallOverflowBound.precallOverflow rate rewards C_star
      C_h) ≤
      (p.K : ℝ) * ((p.T : ℝ) + 1) * Real.exp (-Lstab) := by
  rw [ReferenceFirstCollectionPrecallOverflowBound.precallOverflow_eq_terminalThreshold rate rewards
    C_star C_h]
  calc
    _ ≤ ∑ a : Fin p.K, (kappa).real {z | cap <
        ReferenceFirstCollectionPrecallCalendarSupport.precallBacklog
          rate rewards C_star C_h p.T a z} :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ a : Fin p.K, ((p.T : ℝ) + 1) * Real.exp (-Lstab) := by
      apply Finset.sum_le_sum
      intro a _
      exact fixedIDSourceLaw_terminalArm_measureReal_le_exp
        rate rewards C_star C_h control0 ids a
    _ = (p.K : ℝ) * ((p.T : ℝ) + 1) * Real.exp (-Lstab) := by
      simp [Finset.sum_const, nsmul_eq_mul, mul_assoc]

/-- The canonical stability logarithm bounds the same original pre-call
overflow probability for every original identification array. -/
theorem fixedIDSourceLaw_precallOverflow_measureReal_le_inv_N_sq :
    (kappa).real (ReferenceFirstCollectionPrecallOverflowBound.precallOverflow rate rewards C_star
      C_h) ≤
      1 / (N p : ℝ) ^ 2 := by
  have hExp := fixedIDSourceLaw_precallOverflow_measureReal_le_exp
    rate rewards C_star C_h control0 ids
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

/-- The existing selected-index private complete-row mean has the same
inverse-square bound, with the whole reward table and unrestricted shared
construction witnesses fixed before the row/private expectation. -/
theorem originalIDPrecallOverflowRowMean_le_inv_N_sq :
    ReferenceFirstCollectionPrecallOverflowSelectedRowExpectation.originalIDPrecallOverflowRowMean
      rate rewards C_star C_h ids ≤ 1 / (N p : ℝ) ^ 2 := by
  rw [← ReferenceFixedIDSourceSection.fixedIDSourceLaw_precallOverflow_eq_originalIDRowMean
    rate rewards C_star C_h control0 ids]
  exact fixedIDSourceLaw_precallOverflow_measureReal_le_inv_N_sq
    rate rewards C_star C_h control0 ids

end Bandits.Support.ReferenceFirstCollectionPrecallFixedIDMean

end
