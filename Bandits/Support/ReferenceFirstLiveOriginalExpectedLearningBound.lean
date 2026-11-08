/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Bandits Lean Project contributors
-/
module

public import Bandits.Support.ReferenceFirstLiveOriginalCalendarRoundedComparison
public import Bandits.Support.ReferenceFirstLiveOriginalSignedCorrection

import Mathlib.Tactic

/-!
# Original-source expectation of the first-live learning bound

The raw potential and rounded comparison are integrated on the unchanged
original source-input law. The all-successor signed marginal correction keeps
its terminal successor, including the boundary at `T`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Bandits.Support.ReferenceFirstLiveOriginalExpectedLearningBound

variable {p : ConstructorDimensions.Parameters}
  (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ)

local notation "mu" => BootstrapPrivateRoundStreams.sourceInputLaw p
local notation "Q" => _root_.Bandits.Support.ReferenceFirstLiveRawPotentialBound.firstWindowQueue rate

/-- The actual first-live raw-potential comparison integrated under the
complete original source-input law. -/
theorem integral_firstWindowRawGap_le (S : ProductSetLaw.ProductSet p.K p.m)
    (control0 : ContinuousLearningRows.TimeControl p) :
    (∫ omega : BootstrapPrivateRoundStreams.SourceInput p,
      _root_.Bandits.Support.ReferenceFirstLiveRawPotentialBound.firstWindowRawGap
        rate rewards C_star C_h omega S ∂mu) ≤
      Real.log (Nat.choose p.K p.m : ℝ) /
          RecordedPotentialStep.potentialLambda Q +
        16 * (p.m : ℝ) ^ 2 * RecordedPotentialStep.potentialLambda Q * (p.T : ℝ) +
        (p.m : ℝ) / (16 * rate.eta.val) +
        ((16 / 11 : ℝ) * CanonicalRecordingRates.R p + 32 * (p.m : ℝ)) *
          rate.eta.val * (p.T : ℝ) := by
  let base : ℝ :=
    Real.log (Nat.choose p.K p.m : ℝ) / RecordedPotentialStep.potentialLambda Q +
      16 * (p.m : ℝ) ^ 2 * RecordedPotentialStep.potentialLambda Q * (p.T : ℝ) +
      (p.m : ℝ) / (16 * rate.eta.val)
  let correction :=
    _root_.Bandits.Support.ReferenceFirstLiveRawPotentialBound.firstWindowMarginalBacklogCorrection
      rate rewards C_star C_h
  have hraw : Integrable
      (fun omega : BootstrapPrivateRoundStreams.SourceInput p =>
        _root_.Bandits.Support.ReferenceFirstLiveRawPotentialBound.firstWindowRawGap
          rate rewards C_star C_h omega S) mu :=
    _root_.Bandits.Support.ReferenceFirstLiveOriginalCalendarRoundedComparison.integrable_firstWindowRawGap
      rate rewards C_star C_h S control0
  have hcorrection : Integrable
      (fun omega : BootstrapPrivateRoundStreams.SourceInput p =>
        _root_.Bandits.Support.ReferenceFirstLiveRawPotentialBound.firstWindowMarginalBacklogCorrection
          rate rewards C_star C_h omega) mu :=
    _root_.Bandits.Support.ReferenceFirstLiveOriginalSignedCorrection.integrable_firstWindowMarginalBacklogCorrection
      rate rewards C_star C_h
  have hbase : Integrable
      (fun _ : BootstrapPrivateRoundStreams.SourceInput p => base) mu :=
    integrable_const _
  have hsum : Integrable
      (fun omega : BootstrapPrivateRoundStreams.SourceInput p => base + correction omega) mu :=
    hbase.add hcorrection
  have hpoint (omega : BootstrapPrivateRoundStreams.SourceInput p) :
      _root_.Bandits.Support.ReferenceFirstLiveRawPotentialBound.firstWindowRawGap
          rate rewards C_star C_h omega S ≤ base + correction omega := by
    simpa [base, correction] using
      (_root_.Bandits.Support.ReferenceFirstLiveRawPotentialBound.firstWindowRawGap_le
        rate rewards C_star C_h omega S)
  have hmono := integral_mono_ae hraw hsum
    (Filter.Eventually.of_forall hpoint)
  have hcorrectionMean :=
    _root_.Bandits.Support.ReferenceFirstLiveOriginalSignedCorrection.integral_firstWindowMarginalBacklogCorrection_le
      rate rewards C_star C_h control0
  have hcorrectionMean' :
      (∫ omega : BootstrapPrivateRoundStreams.SourceInput p, correction omega ∂mu) ≤
        ((16 / 11 : ℝ) * CanonicalRecordingRates.R p + 32 * (p.m : ℝ)) *
          rate.eta.val * (p.T : ℝ) := by
    simpa [correction] using hcorrectionMean
  calc
    (∫ omega : BootstrapPrivateRoundStreams.SourceInput p,
        _root_.Bandits.Support.ReferenceFirstLiveRawPotentialBound.firstWindowRawGap
          rate rewards C_star C_h omega S ∂mu) ≤
        ∫ omega, base + correction omega ∂mu := hmono
    _ = base + ∫ omega, correction omega ∂mu := by
      rw [integral_add hbase hcorrection]
      simp [correction]
    _ ≤ base +
        ((16 / 11 : ℝ) * CanonicalRecordingRates.R p + 32 * (p.m : ℝ)) *
          rate.eta.val * (p.T : ℝ) :=
      add_le_add_right hcorrectionMean' base
    _ = _ := by rfl

/-- The precise-lambda rounded estimate retains the exact expected positive
floor-loss term from the same enabled calendar cells. -/
theorem integral_sum_calendarRoundedGap_le_firstWindowLearning_add_expectedFloor
    (S : ProductSetLaw.ProductSet p.K p.m)
    (control0 : ContinuousLearningRows.TimeControl p) :
    (∫ omega : BootstrapPrivateRoundStreams.SourceInput p,
      ∑ t : Fin p.T,
        _root_.Bandits.Support.ReferenceFirstLiveOriginalCalendarRoundedComparison.calendarRoundedGap
          rate rewards C_star C_h t S omega ∂mu) ≤
      Real.log (Nat.choose p.K p.m : ℝ) /
          RecordedPotentialStep.potentialLambda Q +
        16 * (p.m : ℝ) ^ 2 * RecordedPotentialStep.potentialLambda Q * (p.T : ℝ) +
        (p.m : ℝ) / (16 * rate.eta.val) +
        ((16 / 11 : ℝ) * CanonicalRecordingRates.R p + 32 * (p.m : ℝ)) *
          rate.eta.val * (p.T : ℝ) +
        ∫ omega : BootstrapPrivateRoundStreams.SourceInput p,
          ∑ t : Fin p.T,
            _root_.Bandits.Support.ReferenceFirstLiveOriginalCalendarRoundedComparison.calendarFloorLoss
              rate rewards C_star C_h t S omega ∂mu := by
  calc
    _ ≤ (∫ omega : BootstrapPrivateRoundStreams.SourceInput p,
          _root_.Bandits.Support.ReferenceFirstLiveRawPotentialBound.firstWindowRawGap
            rate rewards C_star C_h omega S ∂mu) +
        ∫ omega : BootstrapPrivateRoundStreams.SourceInput p,
          ∑ t : Fin p.T,
            _root_.Bandits.Support.ReferenceFirstLiveOriginalCalendarRoundedComparison.calendarFloorLoss
              rate rewards C_star C_h t S omega ∂mu :=
      _root_.Bandits.Support.ReferenceFirstLiveOriginalCalendarRoundedComparison.integral_sum_calendarRoundedGap_le_firstWindowRawGap_add_floor
          rate rewards C_star C_h S control0
    _ ≤ _ := add_le_add_left
      (integral_firstWindowRawGap_le rate rewards C_star C_h S control0) _

private theorem firstWindowRawGap_integral_coarse
    (S : ProductSetLaw.ProductSet p.K p.m)
    (control0 : ContinuousLearningRows.TimeControl p) :
    (∫ omega : BootstrapPrivateRoundStreams.SourceInput p,
      _root_.Bandits.Support.ReferenceFirstLiveRawPotentialBound.firstWindowRawGap
        rate rewards C_star C_h omega S ∂mu) ≤
      (2 * Real.log (Nat.choose p.K p.m : ℝ) + (p.m : ℝ) / 16) /
          rate.eta.val +
        (16 * (p.m : ℝ) ^ 2 + (16 / 11 : ℝ) * CanonicalRecordingRates.R p +
          32 * (p.m : ℝ)) * rate.eta.val * (p.T : ℝ) := by
  have hprecise := integral_firstWindowRawGap_le rate rewards C_star C_h S control0
  have hchooseNat : 0 < Nat.choose p.K p.m :=
    Nat.choose_pos (Nat.le_of_lt p.m_lt_K)
  have hchooseOne : 1 ≤ (Nat.choose p.K p.m : ℝ) := by
    have hnat : 1 ≤ Nat.choose p.K p.m := Nat.succ_le_iff.mpr hchooseNat
    exact_mod_cast hnat
  have hlog : 0 ≤ Real.log (Nat.choose p.K p.m : ℝ) := Real.log_nonneg hchooseOne
  have hlower := RecordedPotentialStep.eta_div_two_le_potentialLambda Q
  have hupper := RecordedPotentialStep.potentialLambda_le_eta Q
  have hlogBound :
      Real.log (Nat.choose p.K p.m : ℝ) /
          RecordedPotentialStep.potentialLambda Q ≤
        2 * Real.log (Nat.choose p.K p.m : ℝ) / rate.eta.val := by
    calc
      _ ≤ Real.log (Nat.choose p.K p.m : ℝ) / (rate.eta.val / 2) :=
        div_le_div_of_nonneg_left hlog (half_pos rate.eta.property) hlower
      _ = _ := by field_simp [ne_of_gt rate.eta.property]
  have hpotentialBound :
      16 * (p.m : ℝ) ^ 2 * RecordedPotentialStep.potentialLambda Q * (p.T : ℝ) ≤
        16 * (p.m : ℝ) ^ 2 * rate.eta.val * (p.T : ℝ) := by
    have hfactor : 0 ≤ 16 * (p.m : ℝ) ^ 2 * (p.T : ℝ) := by positivity
    calc
      _ = (16 * (p.m : ℝ) ^ 2 * (p.T : ℝ)) *
          RecordedPotentialStep.potentialLambda Q := by ring
      _ ≤ (16 * (p.m : ℝ) ^ 2 * (p.T : ℝ)) * rate.eta.val :=
        mul_le_mul_of_nonneg_left hupper hfactor
      _ = _ := by ring
  have hterminal :
      (p.m : ℝ) / (16 * rate.eta.val) = ((p.m : ℝ) / 16) / rate.eta.val := by
    field_simp [ne_of_gt rate.eta.property]
  have hsplit :
      (2 * Real.log (Nat.choose p.K p.m : ℝ) + (p.m : ℝ) / 16) /
          rate.eta.val =
        2 * Real.log (Nat.choose p.K p.m : ℝ) / rate.eta.val +
          ((p.m : ℝ) / 16) / rate.eta.val := by
    field_simp [ne_of_gt rate.eta.property]
  calc
    _ ≤ Real.log (Nat.choose p.K p.m : ℝ) /
          RecordedPotentialStep.potentialLambda Q +
        16 * (p.m : ℝ) ^ 2 * RecordedPotentialStep.potentialLambda Q * (p.T : ℝ) +
        (p.m : ℝ) / (16 * rate.eta.val) +
        ((16 / 11 : ℝ) * CanonicalRecordingRates.R p + 32 * (p.m : ℝ)) *
          rate.eta.val * (p.T : ℝ) := hprecise
    _ ≤ _ := by
      rw [hsplit]
      nlinarith only [hlogBound, hpotentialBound, hterminal]

/-- The coarse original-source first-live expected rounded learning bound. -/
theorem integral_sum_calendarRoundedGap_le_firstWindowLearningBound
    (S : ProductSetLaw.ProductSet p.K p.m)
    (control0 : ContinuousLearningRows.TimeControl p) :
    (∫ omega : BootstrapPrivateRoundStreams.SourceInput p,
      ∑ t : Fin p.T,
        _root_.Bandits.Support.ReferenceFirstLiveOriginalCalendarRoundedComparison.calendarRoundedGap
          rate rewards C_star C_h t S omega ∂mu) ≤
      (2 * Real.log (Nat.choose p.K p.m : ℝ) + (p.m : ℝ) / 16) /
          rate.eta.val +
        (16 * (p.m : ℝ) ^ 2 + (16 / 11 : ℝ) * CanonicalRecordingRates.R p +
          32 * (p.m : ℝ)) * rate.eta.val * (p.T : ℝ) +
        (p.m : ℝ) * (p.T : ℝ) /
          (rate.eta.val * (ConstructorDimensions.D p : ℝ)) := by
  calc
    _ ≤ (∫ omega : BootstrapPrivateRoundStreams.SourceInput p,
          _root_.Bandits.Support.ReferenceFirstLiveRawPotentialBound.firstWindowRawGap
            rate rewards C_star C_h omega S ∂mu) +
        (p.m : ℝ) * (p.T : ℝ) /
          (rate.eta.val * (ConstructorDimensions.D p : ℝ)) := by
      simpa using
        (_root_.Bandits.Support.ReferenceFirstLiveOriginalCalendarRoundedComparison.integral_sum_calendarRoundedGap_le_firstWindowRawGap_add_coarseFloor
            rate rewards C_star C_h S control0)
    _ ≤ _ := add_le_add_left
      (firstWindowRawGap_integral_coarse rate rewards C_star C_h S control0) _

end Bandits.Support.ReferenceFirstLiveOriginalExpectedLearningBound

end
