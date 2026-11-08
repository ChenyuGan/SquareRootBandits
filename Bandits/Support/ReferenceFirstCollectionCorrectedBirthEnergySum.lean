/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionCorrectedStoppedEnergyTelescope
public import Bandits.Support.ReferenceFirstCollectionPrecallOverflowBound

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-!
# Actual inherited birth energy at the first collection call

The birth term is the original stopped energy at the first post-call date.
Its actual readout agrees pointwise with the matching post-update exponential
queue term, so the finite sum is charged to the unique actual-call telescope.

Sources: `04_slow_fast_learner.tex:157-187,256-290`,
`06_interruptions.tex:355-361,391-408,425-426`, and
`appendix_a_local_protocol.tex:28-64` under `sources/zip4/manuscript/`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ActualInitializationPhysicalStep (GridRewardTable)
open Bandits.Support.ReferenceActivePhysicalStep (RateInput)
open Bandits.Support.BootstrapPrivateRoundStreams (SourceInput sourceInputLaw)
open Bandits.Support.ContinuousLearningRows (TimeControl)
open scoped BigOperators

namespace Bandits.Support.ReferenceFirstCollectionCorrectedBirthEnergySum

local instance sourceInputMeasurableSpace {p : Parameters} :
    MeasurableSpace (SourceInput p) := by
  change MeasurableSpace
    (CompletePublicTable.PublishedOutput p ×
      BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

variable {p : Parameters}
variable (rate : RateInput p) (rewards : GridRewardTable p)
  (C_star C_h : ℝ)

local notation "S" => SourceInput p
local notation "mu" => sourceInputLaw p
local notation "Q" => ReferenceFirstLaunchNumericalCell.queueParameters rate

/-- The actual stopped energy at the first after-call date, with the inherited
queue from the original launch. -/
def birthEnergy (u t : Fin p.T) (a : Fin p.K) (x : S) : ℝ :=
  ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.stoppedEnergy
    rate rewards C_star C_h u t a (t.val + 1) x

/-- At every input, the birth energy is the corrected-cell indicator of the
matching actual post-update exponential queue readout. -/
theorem birthEnergy_eq_correctedCell_indicator_XPlus
    (u t : Fin p.T) (a : Fin p.K) (x : S) :
    birthEnergy rate rewards C_star C_h u t a x =
      (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.correctedCell
        rate rewards C_star C_h u t).indicator
        (fun z => ReferenceFirstCollectionCurrentExponentialQueueStep.XPlus
          rate rewards C_star C_h u t a z) x := by
  by_cases hx : x ∈
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.correctedCell
        rate rewards C_star C_h u t
  · obtain ⟨L, c, hL, hc, _hinputs, hbirth⟩ :=
      ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.stoppedEnergy_birth_actual
        rate rewards C_star C_h u t a x hx
    obtain ⟨L', c', hL', hc', _hminus, hplus⟩ :=
      ReferenceFirstCollectionCurrentExponentialQueueStep.firstCell_XMinus_XPlus_actual_readouts
        rate rewards C_star C_h u t a x hx.1
    have hL'Eq : L' = L := Option.some.inj (hL'.symm.trans hL)
    have hc'Eq : c' = c := Option.some.inj (hc'.symm.trans hc)
    subst L'
    subst c'
    have hrun : RecordedQueueRun.run Q (L ++ [c]) =
        RecordedQueueRun.step Q (RecordedQueueRun.run Q L) c :=
      ReferenceFirstCollectionRenewalFutureNumericalPrefix.run_append_one rate L c
    have hupdate :=
      ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.readoutUpdate_step
        rate (RecordedQueueRun.run Q L) c
    have hpost :
        ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
          (RecordedQueueRun.run Q (L ++ [c])) =
        ReferenceFirstCollectionCurrentQueueReadout.readoutUpdate rate
          (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
            (RecordedQueueRun.run Q L))
          (ReferenceLaterCollectionSourceReadoutMeasurability.arrivalCoordinates rate c) := by
      rw [hrun]
      exact hupdate.symm
    have hregister :
        (((RecordedQueueRun.run Q (L ++ [c])).registers a).2 : ℝ) /
            ((Q).n : ℝ) =
          ReferenceFirstCollectionCurrentQueueReadout.normalizedReadoutBacklog rate
            (some (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
              (RecordedQueueRun.run Q (L ++ [c])))) a := by
      rfl
    have hscalar :
        Real.exp (CanonicalRecordingRates.beta p rate.eta.val *
          (((RecordedQueueRun.run Q (L ++ [c])).registers a).2 : ℝ) /
            ((Q).n : ℝ)) =
        Real.exp (CanonicalRecordingRates.beta p rate.eta.val *
          ReferenceFirstCollectionCurrentQueueReadout.normalizedReadoutBacklog rate
            (some (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
              (RecordedQueueRun.step Q (RecordedQueueRun.run Q L) c))) a) := by
      calc
        _ = Real.exp (CanonicalRecordingRates.beta p rate.eta.val *
            ReferenceFirstCollectionCurrentQueueReadout.normalizedReadoutBacklog rate
            (some (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
                (RecordedQueueRun.run Q (L ++ [c])))) a) := by
          rw [mul_div_assoc, hregister]
        _ = Real.exp (CanonicalRecordingRates.beta p rate.eta.val *
            ReferenceFirstCollectionCurrentQueueReadout.normalizedReadoutBacklog rate
              (some (ReferenceFirstCollectionCurrentQueueReadout.readoutUpdate rate
                (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
                  (RecordedQueueRun.run Q L))
                (ReferenceLaterCollectionSourceReadoutMeasurability.arrivalCoordinates
                  rate c))) a) := by rw [hpost]
        _ = Real.exp (CanonicalRecordingRates.beta p rate.eta.val *
            ReferenceFirstCollectionCurrentQueueReadout.normalizedReadoutBacklog rate
              (some (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
                (RecordedQueueRun.step Q (RecordedQueueRun.run Q L) c))) a) := by
          rw [ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.readoutUpdate_step
            rate (RecordedQueueRun.run Q L) c]
    change ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.stoppedEnergy
      rate rewards C_star C_h u t a (t.val + 1) x = _
    rw [Set.indicator_of_mem hx]
    calc
      _ = Real.exp (CanonicalRecordingRates.beta p rate.eta.val *
          (((RecordedQueueRun.run Q (L ++ [c])).registers a).2 : ℝ) /
            ((Q).n : ℝ)) := hbirth
      _ = Real.exp (CanonicalRecordingRates.beta p rate.eta.val *
          ReferenceFirstCollectionCurrentQueueReadout.normalizedReadoutBacklog rate
            (some (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
              (RecordedQueueRun.step Q (RecordedQueueRun.run Q L) c))) a) := hscalar
      _ = ReferenceFirstCollectionCurrentExponentialQueueStep.XPlus
          rate rewards C_star C_h u t a x := hplus.symm
  · change ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.stoppedEnergy
      rate rewards C_star C_h u t a (t.val + 1) x = _
    rw [ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.stoppedEnergy_off_cell
      rate rewards C_star C_h u t a (t.val + 1) x hx,
      Set.indicator_of_notMem hx]

/-- Pointwise nonnegativity and domination by the actual post-update queue
term, including every off-cell input. -/
theorem birthEnergy_bounds (u t : Fin p.T) (a : Fin p.K) (x : S) :
    0 ≤ birthEnergy rate rewards C_star C_h u t a x ∧
      birthEnergy rate rewards C_star C_h u t a x ≤
        ReferenceFirstCollectionCurrentExponentialQueueStep.XPlus
          rate rewards C_star C_h u t a x := by
  have hplus := ReferenceFirstCollectionCurrentExponentialQueueStep.XPlus_bounds
    rate rewards C_star C_h u t a x
  rw [birthEnergy_eq_correctedCell_indicator_XPlus rate rewards C_star C_h u t a x]
  by_cases hx : x ∈
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.correctedCell
        rate rewards C_star C_h u t
  · rw [Set.indicator_of_mem hx]
    exact ⟨hplus.1, le_rfl⟩
  · rw [Set.indicator_of_notMem hx]
    exact ⟨le_rfl, hplus.1⟩

/-- The unnormalized finite sum of birth integrals is dominated by the
integral of the actual post-update call sum under the same source law. -/
theorem birthEnergy_integral_sum_le_callXPlus
    (control0 : TimeControl p) (a : Fin p.K) :
    (∑ u : Fin p.T, ∑ t : Fin p.T,
      ∫ x, birthEnergy rate rewards C_star C_h u t a x ∂mu) ≤
      ∫ x, ReferenceFirstCollectionActualCallExponentialQueueEstimate.callXPlus
        rate rewards C_star C_h a x ∂mu := by
  unfold ReferenceFirstCollectionActualCallExponentialQueueEstimate.callXPlus
  rw [integral_finsetSum Finset.univ (fun u _ =>
    integrable_finsetSum Finset.univ (fun t _ =>
      ReferenceFirstCollectionCurrentExponentialQueueStep.XPlus_integrable
        rate rewards C_star C_h control0 u t a))]
  apply Finset.sum_le_sum
  intro u _
  rw [integral_finsetSum Finset.univ (fun t _ =>
    ReferenceFirstCollectionCurrentExponentialQueueStep.XPlus_integrable
      rate rewards C_star C_h control0 u t a)]
  apply Finset.sum_le_sum
  intro t _
  exact integral_mono
    (ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.integrable_stoppedEnergy
      rate rewards C_star C_h u t a (t.val + 1))
    (ReferenceFirstCollectionCurrentExponentialQueueStep.XPlus_integrable
      rate rewards C_star C_h control0 u t a)
    (fun x => (birthEnergy_bounds rate rewards C_star C_h u t a x).2)

/-- The actual birth sum pays the one retained first-call event mass. -/
theorem birthEnergy_integral_sum_le_callXMinus_add_retainedFirstCall_measure
    (control0 : TimeControl p) (a : Fin p.K) :
    (∑ u : Fin p.T, ∑ t : Fin p.T,
      ∫ x, birthEnergy rate rewards C_star C_h u t a x ∂mu) ≤
      (∫ x, ReferenceFirstCollectionActualCallExponentialQueueEstimate.callXMinus
        rate rewards C_star C_h a x ∂mu) +
        (mu).real (ReferenceFirstCollectionActualCallExponentialQueueEstimate.retainedFirstCall
          rate rewards C_star C_h) := by
  calc
    _ ≤ ∫ x, ReferenceFirstCollectionActualCallExponentialQueueEstimate.callXPlus
        rate rewards C_star C_h a x ∂mu :=
      birthEnergy_integral_sum_le_callXPlus rate rewards C_star C_h control0 a
    _ ≤ _ :=
      ReferenceFirstCollectionActualCallExponentialQueueEstimate.integral_callXPlus_le_integral_callXMinus_add_retainedFirstCall_measure
        rate rewards C_star C_h control0 a

/-- Replacing the incoming call integral by its same-law finite sum gives the
retained-event version of the useful birth-energy budget. -/
theorem birthEnergy_integral_sum_le_T_add_one_add_retainedFirstCall_measure
    (control0 : TimeControl p) (a : Fin p.K) :
    (∑ u : Fin p.T, ∑ t : Fin p.T,
      ∫ x, birthEnergy rate rewards C_star C_h u t a x ∂mu) ≤
      (p.T : ℝ) + 1 +
        (mu).real (ReferenceFirstCollectionActualCallExponentialQueueEstimate.retainedFirstCall
          rate rewards C_star C_h) := by
  have hminus :
      (∫ x, ReferenceFirstCollectionActualCallExponentialQueueEstimate.callXMinus
        rate rewards C_star C_h a x ∂mu) ≤ (p.T : ℝ) + 1 := by
    change (∫ x, ∑ u : Fin p.T, ∑ t : Fin p.T,
      ReferenceFirstCollectionCurrentExponentialQueueStep.XMinus
        rate rewards C_star C_h u t a x ∂mu) ≤ (p.T : ℝ) + 1
    rw [← ReferenceFirstCollectionPrecallIncomingExponentialEnvelope.firstCell_XMinus_integral_sum_eq
      rate rewards C_star C_h a control0]
    exact ReferenceFirstCollectionPrecallIncomingExponentialEnvelope.firstCell_XMinus_integral_sum_le
      rate rewards C_star C_h a control0
  calc
    _ ≤ (∫ x, ReferenceFirstCollectionActualCallExponentialQueueEstimate.callXMinus
        rate rewards C_star C_h a x ∂mu) +
        (mu).real (ReferenceFirstCollectionActualCallExponentialQueueEstimate.retainedFirstCall
          rate rewards C_star C_h) :=
      birthEnergy_integral_sum_le_callXMinus_add_retainedFirstCall_measure
        rate rewards C_star C_h control0 a
    _ ≤ (p.T : ℝ) + 1 +
        (mu).real (ReferenceFirstCollectionActualCallExponentialQueueEstimate.retainedFirstCall
          rate rewards C_star C_h) := by linarith

/-- The retained first-call event has mass at most one, yielding the final
unnormalized bound `(T : ℝ) + 2` for each arm. -/
theorem birthEnergy_integral_sum_le_T_add_two
    (control0 : TimeControl p) (a : Fin p.K) :
    (∑ u : Fin p.T, ∑ t : Fin p.T,
      ∫ x, birthEnergy rate rewards C_star C_h u t a x ∂mu) ≤ (p.T : ℝ) + 2 := by
  have hmass := ReferenceFirstCollectionActualCallExponentialQueueEstimate.retainedFirstCall_measure_le_one
    rate rewards C_star C_h
  calc
    _ ≤ (p.T : ℝ) + 1 +
        (mu).real (ReferenceFirstCollectionActualCallExponentialQueueEstimate.retainedFirstCall
          rate rewards C_star C_h) :=
      birthEnergy_integral_sum_le_T_add_one_add_retainedFirstCall_measure
        rate rewards C_star C_h control0 a
    _ ≤ (p.T : ℝ) + 2 := by linarith

end Bandits.Support.ReferenceFirstCollectionCorrectedBirthEnergySum

end
