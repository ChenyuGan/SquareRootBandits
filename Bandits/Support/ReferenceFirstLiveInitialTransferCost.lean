/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveStoppedHandoverCost
public import Bandits.Support.ReferenceFirstLiveInitialTransferChronology
public import Bandits.Support.ReferenceFirstLiveInitialTransferStartFields

/-!
# Initial first-live transfer cost

The initial transfer has no collection phase. Its charge is the capped
support on the actual stopped handover dates plus the actual signed release
calendar charge, both on the original source-input law.

Sources: ZIP4 `06_interruptions.tex:431-490` and
`05_binary_transport.tex:180-281`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open scoped BigOperators Classical ENNReal

namespace Bandits.Support.ReferenceFirstLiveInitialTransferCost

section Context

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ)
  (control0 : ContinuousLearningRows.TimeControl p)

local notation "Source" => BootstrapPrivateRoundStreams.SourceInput p
local notation "mu" => BootstrapPrivateRoundStreams.sourceInputLaw p
local notation "F" =>
  ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0
local notation "L" => fun z : Source =>
  ReferenceInitializationRun.launchRound
    (ReferenceCompletePhysicalHistory.generatedInput rate z rewards C_star C_h)
local notation "hL" =>
  ReferenceFirstLiveInitialTransferStartFields.initial_launch_preRound_stopping
    rate rewards C_star C_h control0
local notation "FL" => PhaseStartConditionalWaiting.phaseStartSigmaAlgebra F L hL
local notation "SH" =>
  ReferenceFirstLiveSourceStoppedHandoverEndpoint.supportDates rate rewards C_star C_h
local notation "SR" =>
  ReferenceFirstLiveSourceStoppedReleaseEndpoint.actualFirstReleaseSupport
    rate rewards C_star C_h
local notation "D" =>
  ReferenceFirstLiveInitialTransferChronology.stoppedInitialDates
    rate rewards C_star C_h
local notation "gH" =>
  ReferenceFirstLiveStoppedHandoverAdaptation.g_H rate rewards C_star C_h control0
local notation "ghTotal" =>
  ReferenceFirstLiveStoppedHandoverAdaptation.G_H rate rewards C_star C_h control0
local notation "signedStep" =>
  ReferenceFirstLiveStoppedReleaseCalendarSignedCost.signedStep
    rate rewards C_star C_h
local notation "releaseCost" =>
  ReferenceFirstLiveStoppedReleaseCalendarSignedCost.totalSignedCost
    rate rewards C_star C_h

/-- The source-literal capped support on the actual stopped handover dates. -/
def cappedH (z : Source) : ℝ :=
  ∑ v ∈ SH z,
    min (p.m : ℝ) (gH (v - 1) z)

/-- The initial-transfer charge: capped actual handover support plus the
actual signed release deficit on its stopped calendar. -/
def initialCharge (z : Source) : ℝ :=
  cappedH rate rewards C_star C_h control0 z + releaseCost z

/-- The handover term from the source's initial-transfer bound. -/
def Bh : ℝ :=
  8 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) /
    PhaseServiceWaiting.kappa *
      (2 * (AffineBatchDecoder.quota p : ℝ) +
        Real.log ((p.m - 1 : ℕ) : ℝ) + 1)

/-- The signed release term from the source's initial-transfer bound. -/
def Br : ℝ :=
  2 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) +
    12 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) /
      PhaseServiceWaiting.kappa *
        (Real.log ((p.m - 1 : ℕ) : ℝ) + 1)

private theorem gH_nonneg (z : Source) (v : ℕ) : 0 ≤ gH v z := by
  by_cases hv : v < p.T
  · let t : Fin p.T := ⟨v, hv⟩
    rw [ReferenceFirstLiveStoppedHandoverAdaptation.g_H_eq_card
      rate rewards C_star C_h control0 t z]
    positivity
  · rw [ReferenceFirstLiveStoppedHandoverAdaptation.g_H_eq_zero_of_not_lt
      rate rewards C_star C_h control0 v z hv]

/-- The literal capped handover readout is nonnegative. -/
theorem cappedH_nonneg (z : Source) :
    0 ≤ cappedH rate rewards C_star C_h control0 z := by
  unfold cappedH
  apply Finset.sum_nonneg
  intro v hv
  exact le_min (by positivity) (gH_nonneg rate rewards C_star C_h control0 z (v - 1))

/-- Capping each actual handover round never increases the same uncapped
stopped support sum. -/
theorem cappedH_le_GH (z : Source) :
    cappedH rate rewards C_star C_h control0 z ≤ ghTotal z := by
  change (∑ v ∈ SH z, min (p.m : ℝ) (gH (v - 1) z)) ≤
    ∑ v ∈ SH z, gH (v - 1) z
  apply Finset.sum_le_sum
  intro v hv
  exact min_le_right _ _

private theorem cappedH_eq_round_sum (z : Source) :
    cappedH rate rewards C_star C_h control0 z =
      ∑ t ∈ Finset.range p.T,
        if t + 1 ∈ SH z then min (p.m : ℝ) (gH t z) else 0 := by
  classical
  unfold cappedH
  symm
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun t _ => t + 1)
  · intro t ht
    exact (Finset.mem_filter.mp ht).2
  · intro t ht u hu htu
    omega
  · intro v hv
    obtain ⟨hlo, hhi⟩ :=
      ReferenceFirstLiveSourceStoppedHandoverEndpoint.supportDates_member_bounds
        rate rewards C_star C_h z v hv
    have hvlt : v - 1 < p.T := by omega
    refine ⟨v - 1, Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr hvlt, ?_⟩, ?_⟩
    · have hdate : (v - 1) + 1 = v := by omega
      simpa [hdate] using hv
    · omega
  · intro t ht
    have hdate : (t + 1) - 1 = t := by omega
    rw [hdate]

private theorem cappedH_measurable :
    Measurable (cappedH rate rewards C_star C_h control0) := by
  classical
  have hEq :
      (fun z : Source => cappedH rate rewards C_star C_h control0 z) =
        fun z => ∑ t ∈ Finset.range p.T,
          if t + 1 ∈ SH z then min (p.m : ℝ) (gH t z) else 0 := by
    funext z
    exact cappedH_eq_round_sum rate rewards C_star C_h control0 z
  change Measurable (fun z : Source => cappedH rate rewards C_star C_h control0 z)
  rw [hEq]
  apply Finset.measurable_fun_sum
  intro t ht
  have htlt : t < p.T := Finset.mem_range.mp ht
  let tf : Fin p.T := ⟨t, htlt⟩
  have hsupport : MeasurableSet[
      ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (t + 1)]
      {z : Source | t + 1 ∈ SH z} := by
    simpa only [tf, Fin.val_mk] using
      ReferenceFirstLiveStoppedHandoverAdaptation.supportDates_preRound_measurableSet
        rate rewards C_star C_h control0 tf
  have hsupport' : MeasurableSet {z : Source | t + 1 ∈ SH z} :=
    (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le
      (t + 1) _ hsupport
  have hweight : Measurable (fun z : Source => min (p.m : ℝ) (gH t z)) := by
    have hEq :
        (fun z : Source => min (p.m : ℝ) (gH t z)) =
          fun _ => min (p.m : ℝ)
            (((Finset.univ.filter fun a : Fin p.K =>
              0 < (rewards tf a).val).card : ℝ)) := by
      funext z
      rw [ReferenceFirstLiveStoppedHandoverAdaptation.g_H_eq_card
        rate rewards C_star C_h control0 tf z]
    rw [hEq]
    exact measurable_const
  exact hweight.ite hsupport' measurable_const

/-- The capped handover support is integrable on the original source law. -/
theorem integrable_cappedH :
    Integrable (cappedH rate rewards C_star C_h control0) mu := by
  have hG : Integrable (ghTotal) mu :=
    ReferenceFirstLiveStoppedHandoverCost.integrable_G_H
      rate rewards C_star C_h control0
  have hcapMeas : AEStronglyMeasurable
      (cappedH rate rewards C_star C_h control0) mu :=
    (cappedH_measurable rate rewards C_star C_h control0).aestronglyMeasurable
  apply hG.mono' hcapMeas
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_of_nonneg
    (cappedH_nonneg rate rewards C_star C_h control0 z)]
  exact cappedH_le_GH rate rewards C_star C_h control0 z

/-- Integrability of the literal initial-transfer charge, including its
possibly negative signed release term. -/
theorem initialCharge_integrable :
    Integrable (initialCharge rate rewards C_star C_h control0) mu := by
  exact (integrable_cappedH rate rewards C_star C_h control0).add
    (ReferenceFirstLiveStoppedReleaseCalendarSignedCost.totalSignedCost_integrable
      rate rewards C_star C_h control0)

private theorem handover_field_inclusion : FL ≤
    PhaseStartConditionalWaiting.phaseStartSigmaAlgebra F
      (ReferenceFirstLiveSourceStoppedHandoverEndpoint.sigma rate rewards C_star C_h)
      (ReferenceFirstLiveStoppedHandoverAdaptation.sigma_preRound_stopping
        rate rewards C_star C_h control0) :=
  (ReferenceFirstLiveInitialTransferStartFields.initial_phase_start_sigmaAlgebra_inclusions
    rate rewards C_star C_h control0).1

private theorem release_field_inclusion : FL ≤
    PhaseStartConditionalWaiting.phaseStartSigmaAlgebra F
      (ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstReleaseSigma
        rate rewards C_star C_h)
      (ReferenceFirstLiveSourceStoppedReleaseAdaptation.first_release_sigma_stopping
        rate rewards C_star C_h control0) :=
  (ReferenceFirstLiveInitialTransferStartFields.initial_phase_start_sigmaAlgebra_inclusions
    rate rewards C_star C_h control0).2

/-- Localized initial-transfer charge bound on every event measurable at the
actual launch field. The release input is the actual signed cost and may be
negative. -/
theorem initialCharge_setIntegral_bound
    (B : Set Source) (hB : MeasurableSet[FL] B) :
    ∫ z in B, initialCharge rate rewards C_star C_h control0 z ∂mu ≤
      (Bh (p := p) + Br (p := p)) *
        (BootstrapPrivateRoundStreams.sourceInputLaw p).real B := by
  let : IsProbabilityMeasure mu := BootstrapPrivateRoundStreams.sourceInputLaw_probability p
  have hBambient : MeasurableSet B :=
    PhaseStartConditionalWaiting.phaseStartSigmaAlgebra_le F L hL B hB
  have hcapInt := integrable_cappedH rate rewards C_star C_h control0
  have hGHInt := ReferenceFirstLiveStoppedHandoverCost.integrable_G_H
    rate rewards C_star C_h control0
  have hreleaseInt := ReferenceFirstLiveStoppedReleaseCalendarSignedCost.totalSignedCost_integrable
    rate rewards C_star C_h control0
  have hsplit :
      ∫ z in B, initialCharge rate rewards C_star C_h control0 z ∂mu =
        (∫ z in B, cappedH rate rewards C_star C_h control0 z ∂mu) +
          (∫ z in B, releaseCost z ∂mu) := by
    simpa only [initialCharge] using
      (integral_add hcapInt.integrableOn hreleaseInt.integrableOn)
  have hcaple :
      ∫ z in B, cappedH rate rewards C_star C_h control0 z ∂mu ≤
        ∫ z in B, ghTotal z ∂mu := by
    apply setIntegral_mono_on hcapInt.integrableOn hGHInt.integrableOn hBambient
    intro z hz
    exact cappedH_le_GH rate rewards C_star C_h control0 z
  have hhand := ReferenceFirstLiveStoppedHandoverCost.G_H_setIntegral_bound
    rate rewards C_star C_h control0 B (handover_field_inclusion rate rewards C_star C_h control0 B hB)
  have hrel := ReferenceFirstLiveStoppedReleaseSignedCost.actual_first_release_signed_cost_setIntegral_bound
    rate rewards C_star C_h control0 B
      (release_field_inclusion rate rewards C_star C_h control0 B hB)
  have hdcast : (p.m : ℝ) - 1 = ((p.m - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by have := p.two_le_m; omega : 1 ≤ p.m)]
    norm_num
  have hBh :
      (8 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) / PhaseServiceWaiting.kappa) *
        (2 * (AffineBatchDecoder.quota p : ℝ) +
          Real.log ((p.m - 1 : ℕ) : ℝ) + 1) = Bh (p := p) := rfl
  have hBr :
      (2 * ((p.m : ℝ) - 1) * (p.K : ℝ) +
        (12 * ((p.m : ℝ) - 1) * (p.K : ℝ) /
          (1 - Real.exp (-1))) * (Real.log ((p.m : ℝ) - 1) + 1)) = Br (p := p) := by
    rw [hdcast, ← PhaseServiceWaiting.kappa]
    rfl
  calc
    _ = (∫ z in B, cappedH rate rewards C_star C_h control0 z ∂mu) +
        (∫ z in B, releaseCost z ∂mu) := hsplit
    _ ≤ (Bh (p := p) * (BootstrapPrivateRoundStreams.sourceInputLaw p).real B) +
        (Br (p := p) * (BootstrapPrivateRoundStreams.sourceInputLaw p).real B) := by
      apply add_le_add
      · exact hcaple.trans (by simpa only [hBh] using hhand)
      · simpa only [hBr] using hrel
    _ = (Bh (p := p) + Br (p := p)) *
        (BootstrapPrivateRoundStreams.sourceInputLaw p).real B := by ring

/-- Almost-everywhere conditional expectation bound at the actual initial
launch field under the original source product law. -/
theorem initialCharge_condExp_bound :
    mu[initialCharge rate rewards C_star C_h control0 | FL] ≤ᵐ[mu]
      fun _ => Bh (p := p) + Br (p := p) := by
  let : IsProbabilityMeasure mu := BootstrapPrivateRoundStreams.sourceInputLaw_probability p
  exact (PhaseStartConditionalWaiting.setIntegral_iff_condExp_le mu FL
    (PhaseStartConditionalWaiting.phaseStartSigmaAlgebra_le F L hL)
    (initialCharge rate rewards C_star C_h control0) (Bh (p := p) + Br (p := p))
    (initialCharge_integrable rate rewards C_star C_h control0)).1
      (initialCharge_setIntegral_bound rate rewards C_star C_h control0)

/-- Unconditional initial-transfer bound on the original source law. -/
theorem initialCharge_expectation_bound :
    ∫ z, initialCharge rate rewards C_star C_h control0 z ∂mu ≤
      Bh (p := p) + Br (p := p) := by
  have h := initialCharge_setIntegral_bound rate rewards C_star C_h control0
    Set.univ MeasurableSet.univ
  have hmu : (BootstrapPrivateRoundStreams.sourceInputLaw p).real Set.univ = 1 := by
    simp [Measure.real]
  simpa only [MeasureTheory.setIntegral_univ, hmu, mul_one] using h

/-- The literal charge on the actual initial calendar. The accepted chronology
identifies the disjoint handover/release supports with the consecutive dates
from launch through the first stopped boundary; the boundary theorem also
records that a missing release phase is empty whenever handover is empty. -/
theorem initialCharge_calendar_characterization (z : Source) :
    Disjoint (SH z) (SR z) ∧
      SH z ∪ SR z = D z ∧
      D z = Finset.Ico
        (ReferenceInitializationRun.launchRound
          (ReferenceCompletePhysicalHistory.generatedInput rate z rewards C_star C_h))
        (min
          (ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart
            rate rewards C_star C_h z +
              (ReferenceFirstLiveSourceStoppedHandoverEndpoint.window
                rate rewards C_star C_h z).length + 1)
          (ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstExcluded
            rate rewards C_star C_h z)) ∧
      (SH z = ∅ → SR z = ∅) ∧
      initialCharge rate rewards C_star C_h control0 z =
        (∑ t ∈ Finset.range p.T,
          if t + 1 ∈ SH z then min (p.m : ℝ) (gH t z) else 0) +
          (∑ t : Fin p.T, signedStep t z) := by
  have hcal := ReferenceFirstLiveInitialTransferChronology.stopped_initial_calendar
    rate rewards C_star C_h z
  have hboundary := ReferenceFirstLiveInitialTransferChronology.initial_phase_boundary
    rate rewards C_star C_h z
  refine ⟨hcal.1, hcal.2.1, hcal.2.2.1, hboundary.2.1, ?_⟩
  rw [initialCharge, cappedH_eq_round_sum rate rewards C_star C_h control0 z]
  rfl

/-- If the actual handover support is empty, chronology forces the release
support empty too, so both literal finite charges vanish. -/
theorem initialCharge_eq_zero_of_empty_handover (z : Source)
    (hH : SH z = ∅) : initialCharge rate rewards C_star C_h control0 z = 0 := by
  have hR : SR z = ∅ :=
    (ReferenceFirstLiveInitialTransferChronology.initial_phase_boundary
      rate rewards C_star C_h z).2.1 hH
  rw [initialCharge]
  simp [cappedH, hH,
    ReferenceFirstLiveStoppedReleaseCalendarSignedCost.totalSignedCost_eq_zero_of_support_empty
      rate rewards C_star C_h z hR]

end Context

end Bandits.Support.ReferenceFirstLiveInitialTransferCost

end
