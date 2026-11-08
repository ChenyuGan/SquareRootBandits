/-
Copyright (c) 2026 Bandits Lean formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionOldCalendarExponentialStep
public import Bandits.Support.ReferenceFirstCollectionPrecallCalendarIncrementIdentity
public import Bandits.Support.ReferenceFirstCollectionPrecallLiveOldMass

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Original-source pre-first-invocation incoming exponential envelope

This module bounds the literal scalar backlog in the existing original
pre-call calendar prefix. An absent prefix contributes the specified scalar
zero backlog, and no physical state is assigned on that branch. The proof
keeps the first overflow-detecting update and the unchanged original source
law.

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:140-188,245-290`,
`sources/zip4/manuscript/05_binary_transport.tex:352-431`, and
`sources/zip4/manuscript/06_interruptions.tex:35-100,355-426`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators Classical

namespace Bandits.Support.ReferenceFirstCollectionPrecallIncomingExponentialEnvelope

open ConstructorDimensions (Parameters)
open ReferenceActivePhysicalStep (RateInput)
open ActualInitializationPhysicalStep (GridRewardTable)
open BootstrapPrivateRoundStreams (SourceInput sourceInputLaw)
open ContinuousLearningRows (TimeControl)

/-- Literal exponential of the existing optional pre-call scalar backlog.
The absent-prefix branch remains P's scalar zero; it does not describe a
physical queue state. -/
def Y {p : Parameters}
    (rate : RateInput p) (rewards : GridRewardTable p) (C_star C_h : ℝ)
    (a : Fin p.K) (n : ℕ) (z : SourceInput p) : ℝ :=
  Real.exp (CanonicalRecordingRates.beta p rate.eta.val *
    ReferenceFirstCollectionPrecallCalendarSupport.precallBacklog
      rate rewards C_star C_h n a z)

variable {p : Parameters}
  (rate : RateInput p) (rewards : GridRewardTable p)
  (C_star C_h : ℝ) (control0 : TimeControl p) (a : Fin p.K)

local notation "S" => SourceInput p
local notation "mu" => sourceInputLaw p
local notation "beta" => CanonicalRecordingRates.beta p rate.eta.val
local notation "liveExp" => fun (n : ℕ) (z : S) => Real.exp (beta *
  ReferenceFirstLiveCalendarPrefixReadout.firstWindowBacklogAt
    rate rewards C_star C_h a n z)

/-- At calendar boundary zero the literal incoming exponential is one. -/
theorem Y_zero (z : S) : Y rate rewards C_star C_h a 0 z = 1 := by
  have hback : Bandits.Support.ReferenceFirstCollectionPrecallCalendarSupport.precallBacklog
      rate rewards C_star C_h 0 a z = 0 := by
    by_cases hlaunch : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
        rate rewards C_star C_h 0 z
    · simp [Bandits.Support.ReferenceFirstCollectionPrecallCalendarSupport.precallBacklog,
        Bandits.Support.ReferenceFirstCollectionPrecallCalendarSupport.precallCells?,
        Bandits.Support.ReferenceFirstCollectionPrecallCalendarSupport.precallSlots,
        Bandits.Support.ReferenceFirstCollectionPrecallCalendarSupport.cutBoundary,
        hlaunch, RecordedQueueRun.run, RecordedQueueRun.execute,
        RecordedQueueRun.initialState, StoppedQueueBound.normalizedBacklog]
    · simp [Bandits.Support.ReferenceFirstCollectionPrecallCalendarSupport.precallBacklog,
        Bandits.Support.ReferenceFirstCollectionPrecallCalendarSupport.precallCells?,
        Bandits.Support.ReferenceFirstCollectionPrecallCalendarSupport.cutBoundary,
        hlaunch]
  rw [Y, hback]
  simp

/-- The literal exponential remains bounded by the existing stopped-run
backlog envelope at every horizon-valid boundary. -/
theorem Y_pointwise_bound (n : ℕ) (hn : n ≤ p.T) (z : S) :
    0 ≤ Y rate rewards C_star C_h a n z ∧
      Y rate rewards C_star C_h a n z ≤
        Real.exp (2 * (CanonicalRecordingRates.L_stab p : ℝ)) := by
  have hback := ReferenceFirstCollectionOldCalendarExponentialStep.precallBacklog_bounds
    rate rewards C_star C_h a n hn z
  have hbeta := CanonicalRecordingRates.beta_pos p rate.eta.property
  rw [Y]
  constructor
  · exact Real.exp_nonneg _
  · apply Real.exp_le_exp.mpr
    unfold CanonicalRecordingRates.beta
    calc
      32 * rate.eta.val * (CanonicalRecordingRates.L_stab p : ℝ) *
          ReferenceFirstCollectionPrecallCalendarSupport.precallBacklog
            rate rewards C_star C_h n a z ≤
        (32 * rate.eta.val * (CanonicalRecordingRates.L_stab p : ℝ)) *
          (2 * (1 / (32 * rate.eta.val))) :=
            mul_le_mul_of_nonneg_left hback.2 (le_of_lt hbeta)
      _ = 2 * (CanonicalRecordingRates.L_stab p : ℝ) := by
        field_simp [ne_of_gt rate.eta.property]

/-- Every actual calendar increment splits into the same first-live and OLD
increments, with no supplied phase partition or favorable-path premise. -/
theorem Y_calendar_increment (t : Fin p.T) (z : S) :
    Y rate rewards C_star C_h a (t.val + 1) z -
        Y rate rewards C_star C_h a t.val z =
      (liveExp (t.val + 1) z - liveExp t.val z) +
      (ReferenceFirstCollectionOldCalendarExponentialStep.Xplus
          rate rewards C_star C_h t a z -
        ReferenceFirstCollectionOldCalendarExponentialStep.Xminus
          rate rewards C_star C_h t a z) :=
  ReferenceFirstCollectionPrecallCalendarIncrementIdentity.precallCalendarIncrementIdentity
    rate rewards C_star C_h a t z

/-- Additive form of the literal scalar calendar recurrence. -/
theorem Y_calendar_step_eq (t : Fin p.T) (z : S) :
    Y rate rewards C_star C_h a (t.val + 1) z =
      Y rate rewards C_star C_h a t.val z +
        (liveExp (t.val + 1) z - liveExp t.val z) +
        (ReferenceFirstCollectionOldCalendarExponentialStep.Xplus
            rate rewards C_star C_h t a z -
          ReferenceFirstCollectionOldCalendarExponentialStep.Xminus
            rate rewards C_star C_h t a z) := by
  have h := Y_calendar_increment rate rewards C_star C_h a t z
  linarith

/-- Ambient measurability follows along actual calendar increments under the
existing continuous source measurable space. -/
theorem Y_measurable (control0 : TimeControl p) (n : ℕ) (hn : n ≤ p.T) :
    Measurable (Y rate rewards C_star C_h a n) := by
  induction n with
  | zero =>
      have heq : Y rate rewards C_star C_h a 0 = fun _ : S => (1 : ℝ) :=
        funext (Y_zero rate rewards C_star C_h a)
      rw [heq]
      exact measurable_const
  | succ n ih =>
      have hnt : n < p.T := by omega
      let t : Fin p.T := ⟨n, hnt⟩
      have heq : Y rate rewards C_star C_h a (n + 1) = fun z : S =>
          Y rate rewards C_star C_h a n z +
            (liveExp (n + 1) z - liveExp n z) +
            (ReferenceFirstCollectionOldCalendarExponentialStep.Xplus
                rate rewards C_star C_h t a z -
              ReferenceFirstCollectionOldCalendarExponentialStep.Xminus
                rate rewards C_star C_h t a z) := by
        funext z
        exact Y_calendar_step_eq rate rewards C_star C_h a t z
      rw [heq]
      exact ((ih (by omega)).add
        ((ReferenceFirstLiveCalendarPrefixReadout.measurable_firstWindowExpBacklogAt
            rate rewards C_star C_h a (n + 1)).sub
          (ReferenceFirstLiveCalendarPrefixReadout.measurable_firstWindowExpBacklogAt
            rate rewards C_star C_h a n))).add
        ((ReferenceFirstCollectionOldCalendarExponentialStep.Xplus_measurable
            rate rewards C_star C_h t a control0).sub
          (ReferenceFirstCollectionOldCalendarExponentialStep.Xminus_measurable_ambient
            rate rewards C_star C_h t a control0))

/-- Integrability is produced by finite induction from the constant initial
value and the already integrable actual LIVE and OLD increments. -/
theorem Y_integrable (control0 : TimeControl p) (n : ℕ) (hn : n ≤ p.T) :
    Integrable (Y rate rewards C_star C_h a n) mu := by
  let : IsProbabilityMeasure mu :=
    BootstrapPrivateRoundStreams.sourceInputLaw_probability p
  induction n with
  | zero =>
      have heq : Y rate rewards C_star C_h a 0 = fun _ : S => (1 : ℝ) :=
        funext (Y_zero rate rewards C_star C_h a)
      rw [heq]
      exact integrable_const _
  | succ n ih =>
      have hnt : n < p.T := by omega
      let t : Fin p.T := ⟨n, hnt⟩
      have heq : Y rate rewards C_star C_h a (n + 1) = fun z : S =>
          Y rate rewards C_star C_h a n z +
            (liveExp (n + 1) z - liveExp n z) +
            (ReferenceFirstCollectionOldCalendarExponentialStep.Xplus
                rate rewards C_star C_h t a z -
              ReferenceFirstCollectionOldCalendarExponentialStep.Xminus
                rate rewards C_star C_h t a z) := by
        funext z
        exact Y_calendar_step_eq rate rewards C_star C_h a t z
      rw [heq]
      exact ((ih (by omega)).add
        ((ReferenceFirstLiveCalendarExponentialBound.integrable_firstWindowExpBacklogAt
            rate rewards C_star C_h a (n + 1)).sub
          (ReferenceFirstLiveCalendarExponentialBound.integrable_firstWindowExpBacklogAt
            rate rewards C_star C_h a n))).add
        ((ReferenceFirstCollectionOldCalendarExponentialStep.Xplus_integrable
            rate rewards C_star C_h t a control0).sub
          (ReferenceFirstCollectionOldCalendarExponentialStep.Xminus_integrable
            rate rewards C_star C_h t a control0))

/-- Exact integration of the actual scalar recurrence, before applying any
mass bound. All three terms use the unchanged original source law. -/
theorem integral_Y_calendar_increment (control0 : TimeControl p) (t : Fin p.T) :
    (∫ z : S, Y rate rewards C_star C_h a (t.val + 1) z ∂mu) =
      (∫ z : S, Y rate rewards C_star C_h a t.val z ∂mu) +
        (∫ z : S, liveExp (t.val + 1) z - liveExp t.val z ∂mu) +
        (∫ z : S,
          ReferenceFirstCollectionOldCalendarExponentialStep.Xplus
              rate rewards C_star C_h t a z -
            ReferenceFirstCollectionOldCalendarExponentialStep.Xminus
              rate rewards C_star C_h t a z ∂mu) := by
  have hY := Y_integrable rate rewards C_star C_h a control0 t.val
    (Nat.le_of_lt t.isLt)
  have hLive : Integrable
      (fun z : S => liveExp (t.val + 1) z - liveExp t.val z) mu :=
    (ReferenceFirstLiveCalendarExponentialBound.integrable_firstWindowExpBacklogAt
      rate rewards C_star C_h a (t.val + 1)).sub
    (ReferenceFirstLiveCalendarExponentialBound.integrable_firstWindowExpBacklogAt
      rate rewards C_star C_h a t.val)
  have hOld :=
    (ReferenceFirstCollectionOldCalendarExponentialStep.Xplus_integrable
      rate rewards C_star C_h t a control0).sub
    (ReferenceFirstCollectionOldCalendarExponentialStep.Xminus_integrable
      rate rewards C_star C_h t a control0)
  have heq : Y rate rewards C_star C_h a (t.val + 1) = fun z : S =>
      Y rate rewards C_star C_h a t.val z +
        (liveExp (t.val + 1) z - liveExp t.val z) +
        (ReferenceFirstCollectionOldCalendarExponentialStep.Xplus
            rate rewards C_star C_h t a z -
          ReferenceFirstCollectionOldCalendarExponentialStep.Xminus
            rate rewards C_star C_h t a z) :=
    funext (Y_calendar_step_eq rate rewards C_star C_h a t)
  rw [heq]
  exact (integral_add (hY.add hLive) hOld).trans
    (congrArg (fun x : ℝ => x +
      ∫ z : S,
        ReferenceFirstCollectionOldCalendarExponentialStep.Xplus
            rate rewards C_star C_h t a z -
          ReferenceFirstCollectionOldCalendarExponentialStep.Xminus
            rate rewards C_star C_h t a z ∂mu)
      (integral_add hY hLive))

/-- LIVE birth, nonempty, and empty increments and the retained OLD increment
share one unnormalized probability budget at this actual calendar date. -/
theorem integral_live_add_old_increment_le_one (control0 : TimeControl p)
    (t : Fin p.T) :
    (∫ z : S, liveExp (t.val + 1) z - liveExp t.val z ∂mu) +
      (∫ z : S,
        ReferenceFirstCollectionOldCalendarExponentialStep.Xplus
            rate rewards C_star C_h t a z -
          ReferenceFirstCollectionOldCalendarExponentialStep.Xminus
            rate rewards C_star C_h t a z ∂mu) ≤ 1 := by
  have hLiveStep := ReferenceFirstLiveCalendarIntegralAssembly.integral_exp_calendar_step
    rate rewards C_star C_h t control0 a
  dsimp only [ReferenceFirstLiveSourceSavedMoments.beta] at hLiveStep
  rw [hLiveStep]
  refine le_trans (add_le_add (add_le_add ?_ ?_)
    (ReferenceFirstCollectionOldCalendarExponentialStep.integral_Xplus_sub_Xminus_le_G_mass
      rate rewards C_star C_h t a control0))
    (ReferenceFirstCollectionPrecallLiveOldMass.source_cell_masses_add_G_le_one
      rate rewards C_star C_h t control0)
  · apply Finset.sum_le_sum
    intro q _
    exact ReferenceFirstLiveCalendarExponentialBound.integral_exp_birth_difference_le_mass
      rate rewards C_star C_h q t control0 a
  · apply Finset.sum_le_sum
    intro q _
    apply Finset.sum_le_sum
    intro v _
    exact add_le_add
      (ReferenceFirstLiveCalendarExponentialBound.integral_exp_nonempty_difference_le_mass
        rate rewards C_star C_h q t control0 a v.val (Nat.lt_succ_iff.mp v.isLt))
      (ReferenceFirstLiveCalendarExponentialBound.integral_exp_empty_difference_le_mass
        rate rewards C_star C_h q t control0 a v.val (Nat.lt_succ_iff.mp v.isLt))

/-- One original calendar date costs at most one unit of incoming exponential
expectation, including every absent, terminal, and stopped branch. -/
theorem integral_Y_calendar_step (control0 : TimeControl p) (t : Fin p.T) :
    (∫ z : S, Y rate rewards C_star C_h a (t.val + 1) z ∂mu) ≤
      (∫ z : S, Y rate rewards C_star C_h a t.val z ∂mu) + 1 := by
  rw [integral_Y_calendar_increment rate rewards C_star C_h a control0 t]
  have h := integral_live_add_old_increment_le_one rate rewards C_star C_h a control0 t
  linarith

/-- Finite original-source incoming envelope. The only condition on the
calendar boundary is its horizon index typing. -/
theorem integral_Y_calendar_le (control0 : TimeControl p) (n : ℕ) (hn : n ≤ p.T) :
    (∫ z : S, Y rate rewards C_star C_h a n z ∂mu) ≤ (n : ℝ) + 1 := by
  let : IsProbabilityMeasure mu :=
    BootstrapPrivateRoundStreams.sourceInputLaw_probability p
  induction n with
  | zero =>
      have heq : Y rate rewards C_star C_h a 0 = fun _ : S => (1 : ℝ) :=
        funext (Y_zero rate rewards C_star C_h a)
      rw [heq]
      simp
  | succ n ih =>
      have hnt : n < p.T := by omega
      have hprev := ih (by omega)
      have hstep := integral_Y_calendar_step rate rewards C_star C_h a control0 ⟨n, hnt⟩
      calc
        (∫ z : S, Y rate rewards C_star C_h a (n + 1) z ∂mu) ≤
            (∫ z : S, Y rate rewards C_star C_h a n z ∂mu) + 1 := hstep
        _ ≤ ((n : ℝ) + 1) + 1 := add_le_add hprev le_rfl
        _ = ((n + 1 : ℕ) : ℝ) + 1 := by simp only [Nat.cast_add, Nat.cast_one]

/-- The real terminal no-call boundary is retained in the same envelope. -/
theorem integral_Y_terminal (control0 : TimeControl p) :
    (∫ z : S, Y rate rewards C_star C_h a p.T z ∂mu) ≤ (p.T : ℝ) + 1 :=
  integral_Y_calendar_le rate rewards C_star C_h a control0 p.T le_rfl

/-- On every actual first-call cell the terminal scalar is exactly the
original current incoming exponential, including the cutoff head once. -/
theorem Y_terminal_eq_current_on_firstCell (u t : Fin p.T) (z : S)
    (hz : z ∈ ReferenceCalendarCollectionCallControlLaw.firstCell
      rate rewards C_star C_h u t) :
    Y rate rewards C_star C_h a p.T z =
      Real.exp (beta * ReferenceFirstCollectionCurrentQueueReadout.bMinus
        rate rewards C_star C_h u t a z) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hminus⟩ :=
    Bandits.Support.ReferenceFirstCollectionPrecallCalendarSupport.precallPrefix_terminal_on_firstCell
      rate rewards C_star C_h u t a z hz
  rw [Y, hminus]

/-- Each actual first-invocation incoming term is the indicator of the same
terminal scalar, including unsuccessful checked-sampler invocations. -/
theorem XMinus_eq_terminal_indicator (u t : Fin p.T) :
    ReferenceFirstCollectionCurrentExponentialQueueStep.XMinus
        rate rewards C_star C_h u t a =
      (ReferenceCalendarCollectionCallControlLaw.firstCell
        rate rewards C_star C_h u t).indicator
        (Y rate rewards C_star C_h a p.T) := by
  funext z
  by_cases hz : z ∈ ReferenceCalendarCollectionCallControlLaw.firstCell
      rate rewards C_star C_h u t
  · rw [ReferenceFirstCollectionCurrentExponentialQueueStep.XMinus,
      Set.indicator_of_mem hz, Set.indicator_of_mem hz]
    exact (Y_terminal_eq_current_on_firstCell
      rate rewards C_star C_h a u t z hz).symm
  · rw [ReferenceFirstCollectionCurrentExponentialQueueStep.XMinus,
      Set.indicator_of_notMem hz, Set.indicator_of_notMem hz]

/-- The actual first-call indicators select at most one calendar cell. -/
theorem firstCell_indicator_sum_le_one (z : S) :
    (∑ u : Fin p.T, ∑ t : Fin p.T,
      (ReferenceCalendarCollectionCallControlLaw.firstCell
        rate rewards C_star C_h u t).indicator (fun _ : S => (1 : ℝ)) z) ≤ 1 := by
  classical
  cases hcall : ReferenceFirstCollectionSamplerCall.firstCollectionCall
      rate rewards C_star C_h z with
  | none => simp [ReferenceCalendarCollectionCallControlLaw.firstCell, hcall]
  | some call =>
      rcases call with ⟨u₀, t₀, θ⟩
      rcases θ with ⟨θ₁, θ₂⟩
      have heq (u t : Fin p.T) :
          (ReferenceCalendarCollectionCallControlLaw.firstCell
            rate rewards C_star C_h u t).indicator (fun _ : S => (1 : ℝ)) z =
            if u = u₀ ∧ t = t₀ then 1 else 0 := by
        simp [Set.indicator, ReferenceCalendarCollectionCallControlLaw.firstCell,
          hcall, Prod.mk.injEq, eq_comm]
      simp_rw [heq]
      calc
        (∑ u : Fin p.T, ∑ t : Fin p.T,
            if u = u₀ ∧ t = t₀ then (1 : ℝ) else 0) =
          ∑ u : Fin p.T, if u = u₀ then (1 : ℝ) else 0 := by
            apply Finset.sum_congr rfl
            intro u hu
            by_cases h : u = u₀
            · subst u
              simp
            · simp [h]
        _ = 1 := by simp
        _ ≤ 1 := le_rfl

/-- Pointwise terminal domination by the disjoint actual first-call
partition. -/
theorem firstCell_XMinus_sum_le_Y_terminal (z : S) :
    (∑ u : Fin p.T, ∑ t : Fin p.T,
      ReferenceFirstCollectionCurrentExponentialQueueStep.XMinus
        rate rewards C_star C_h u t a z) ≤
      Y rate rewards C_star C_h a p.T z := by
  have hnonneg : 0 ≤ Y rate rewards C_star C_h a p.T z := by
    exact Real.exp_nonneg _
  have hterm (u t : Fin p.T) :
      ReferenceFirstCollectionCurrentExponentialQueueStep.XMinus
          rate rewards C_star C_h u t a z ≤
        (ReferenceCalendarCollectionCallControlLaw.firstCell
          rate rewards C_star C_h u t).indicator
            (fun _ : S => Y rate rewards C_star C_h a p.T z) z := by
    by_cases hz : z ∈ ReferenceCalendarCollectionCallControlLaw.firstCell
        rate rewards C_star C_h u t
    · rw [ReferenceFirstCollectionCurrentExponentialQueueStep.XMinus,
        Set.indicator_of_mem hz, Set.indicator_of_mem hz]
      rw [← Y_terminal_eq_current_on_firstCell rate rewards C_star C_h a u t z hz]
    · rw [ReferenceFirstCollectionCurrentExponentialQueueStep.XMinus,
        Set.indicator_of_notMem hz, Set.indicator_of_notMem hz]
  calc
    _ ≤ ∑ u : Fin p.T, ∑ t : Fin p.T,
        (ReferenceCalendarCollectionCallControlLaw.firstCell
          rate rewards C_star C_h u t).indicator
            (fun _ : S => Y rate rewards C_star C_h a p.T z) z := by
      apply Finset.sum_le_sum
      intro u hu
      apply Finset.sum_le_sum
      intro t ht
      exact hterm u t
    _ = Y rate rewards C_star C_h a p.T z *
        (∑ u : Fin p.T, ∑ t : Fin p.T,
          (ReferenceCalendarCollectionCallControlLaw.firstCell
            rate rewards C_star C_h u t).indicator (fun _ : S => (1 : ℝ)) z) := by
      have hfactor (u t : Fin p.T) :
          (ReferenceCalendarCollectionCallControlLaw.firstCell
            rate rewards C_star C_h u t).indicator
              (fun _ : S => Y rate rewards C_star C_h a p.T z) z =
            Y rate rewards C_star C_h a p.T z *
              (ReferenceCalendarCollectionCallControlLaw.firstCell
                rate rewards C_star C_h u t).indicator
                  (fun _ : S => (1 : ℝ)) z := by
        by_cases hz : z ∈ ReferenceCalendarCollectionCallControlLaw.firstCell
            rate rewards C_star C_h u t <;> simp [Set.indicator, hz]
      calc
        _ = ∑ u : Fin p.T, ∑ t : Fin p.T,
            Y rate rewards C_star C_h a p.T z *
              (ReferenceCalendarCollectionCallControlLaw.firstCell
                rate rewards C_star C_h u t).indicator
                  (fun _ : S => (1 : ℝ)) z := by
          apply Finset.sum_congr rfl
          intro u hu
          apply Finset.sum_congr rfl
          intro t ht
          exact hfactor u t
        _ = ∑ u : Fin p.T, Y rate rewards C_star C_h a p.T z *
            (∑ t : Fin p.T,
              (ReferenceCalendarCollectionCallControlLaw.firstCell
                rate rewards C_star C_h u t).indicator
                  (fun _ : S => (1 : ℝ)) z) := by
          apply Finset.sum_congr rfl
          intro u hu
          exact (Finset.mul_sum _ _ _).symm
        _ = Y rate rewards C_star C_h a p.T z *
            (∑ u : Fin p.T, ∑ t : Fin p.T,
              (ReferenceCalendarCollectionCallControlLaw.firstCell
                rate rewards C_star C_h u t).indicator
                  (fun _ : S => (1 : ℝ)) z) := (Finset.mul_sum _ _ _).symm
    _ ≤ Y rate rewards C_star C_h a p.T z := by
      have hsum := firstCell_indicator_sum_le_one rate rewards C_star C_h z
      calc
        Y rate rewards C_star C_h a p.T z *
            (∑ u : Fin p.T, ∑ t : Fin p.T,
              (ReferenceCalendarCollectionCallControlLaw.firstCell
                rate rewards C_star C_h u t).indicator (fun _ : S => (1 : ℝ)) z) ≤
          Y rate rewards C_star C_h a p.T z * 1 :=
            mul_le_mul_of_nonneg_left hsum hnonneg
        _ = Y rate rewards C_star C_h a p.T z := by ring

/-- The finite sum of actual first-call incoming exponentials is integrable
under the unchanged whole-source law. -/
theorem firstCell_XMinus_sum_integrable (control0 : TimeControl p) :
    Integrable (fun z : S =>
      ∑ u : Fin p.T, ∑ t : Fin p.T,
        ReferenceFirstCollectionCurrentExponentialQueueStep.XMinus
          rate rewards C_star C_h u t a z) mu := by
  apply integrable_finsetSum
  intro u _
  apply integrable_finsetSum
  intro t _
  exact ReferenceFirstCollectionCurrentExponentialQueueStep.XMinus_integrable
    rate rewards C_star C_h control0 u t a

/-- The finite unnormalized sum of terminal first-call integrals is the
integral of the pointwise finite sum. -/
theorem firstCell_XMinus_integral_sum_eq (control0 : TimeControl p) :
    (∑ u : Fin p.T, ∑ t : Fin p.T,
      ∫ z : S, ReferenceFirstCollectionCurrentExponentialQueueStep.XMinus
        rate rewards C_star C_h u t a z ∂mu) =
      ∫ z : S,
        ∑ u : Fin p.T, ∑ t : Fin p.T,
          ReferenceFirstCollectionCurrentExponentialQueueStep.XMinus
            rate rewards C_star C_h u t a z ∂mu := by
  symm
  rw [integral_finsetSum Finset.univ (fun u _ =>
    integrable_finsetSum Finset.univ (fun t _ =>
      ReferenceFirstCollectionCurrentExponentialQueueStep.XMinus_integrable
        rate rewards C_star C_h control0 u t a))]
  apply Finset.sum_congr rfl
  intro u _
  rw [integral_finsetSum Finset.univ (fun t _ =>
    ReferenceFirstCollectionCurrentExponentialQueueStep.XMinus_integrable
      rate rewards C_star C_h control0 u t a)]

/-- Integrating the actual first-call partition costs only the one terminal
envelope, rather than a new bound for each pair of dates. -/
theorem firstCell_XMinus_integral_sum_le_terminal (control0 : TimeControl p) :
    (∑ u : Fin p.T, ∑ t : Fin p.T,
      ∫ z : S, ReferenceFirstCollectionCurrentExponentialQueueStep.XMinus
        rate rewards C_star C_h u t a z ∂mu) ≤
      ∫ z : S, Y rate rewards C_star C_h a p.T z ∂mu := by
  rw [firstCell_XMinus_integral_sum_eq rate rewards C_star C_h a control0]
  exact integral_mono
    (firstCell_XMinus_sum_integrable rate rewards C_star C_h a control0)
    (Y_integrable rate rewards C_star C_h a control0 p.T le_rfl)
    (firstCell_XMinus_sum_le_Y_terminal rate rewards C_star C_h a)

/-- Sharp original-source incoming estimate for the actual first invocation.
There are no call, survival, endpoint, or event-coverage hypotheses. -/
theorem firstCell_XMinus_integral_sum_le (control0 : TimeControl p) :
    (∑ u : Fin p.T, ∑ t : Fin p.T,
      ∫ z : S, ReferenceFirstCollectionCurrentExponentialQueueStep.XMinus
        rate rewards C_star C_h u t a z ∂mu) ≤ (p.T : ℝ) + 1 :=
  (firstCell_XMinus_integral_sum_le_terminal rate rewards C_star C_h a control0).trans
    (integral_Y_terminal rate rewards C_star C_h a control0)

/-- Both inequalities of the literal first-call incoming envelope under the
unchanged whole-source law, ready for the actual-call incoming energy term. -/
theorem firstCell_incoming_exponential_envelope (control0 : TimeControl p) :
    (∑ u : Fin p.T, ∑ t : Fin p.T,
        ∫ z : S, ReferenceFirstCollectionCurrentExponentialQueueStep.XMinus
          rate rewards C_star C_h u t a z ∂mu) ≤
        (∫ z : S, Y rate rewards C_star C_h a p.T z ∂mu) ∧
      (∫ z : S, Y rate rewards C_star C_h a p.T z ∂mu) ≤ (p.T : ℝ) + 1 :=
  ⟨firstCell_XMinus_integral_sum_le_terminal rate rewards C_star C_h a control0,
    integral_Y_terminal rate rewards C_star C_h a control0⟩

end Bandits.Support.ReferenceFirstCollectionPrecallIncomingExponentialEnvelope

end
