/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceOriginalFixedInstallationHandoverWaitingCost
public import Bandits.Support.ReferenceOriginalKthHandoverBirthLocalization

import Mathlib.Tactic

/-!
# Conditional waiting cost for one original ranked handover

The uncapped positive-arm charge on the original kth stopped-transfer window
inherits the fixed-installation waiting bound by localizing each actual birth
mark at that same original stopped-start field. The capped support charge is
bounded by the same estimate.

Sources: ZIP4 `05_binary_transport.tex:244-289`,
`06_interruptions.tex:431-490,493-533`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open scoped BigOperators Classical ENNReal

namespace Bandits.Support.ReferenceOriginalKthHandoverConditionalWaitingCost

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)

local notation "Source" => BootstrapPrivateRoundStreams.SourceInput p
local notation "μ" => BootstrapPrivateRoundStreams.sourceInputLaw p

local notation "BirthMark" =>
  ReferenceOriginalKthBirthMarkLocalization.kthBirthMark rate rewards C_star C_h

local notation "StartDate" =>
  ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
    rate rewards C_star C_h

/-- The analytical source-prefix stopped field at the original kth transfer
start, including the absent-rank sentinel. -/
@[instance_reducible] public noncomputable def kthHStartSigmaAlgebra
    (k : Fin (p.T + 1)) : MeasurableSpace Source :=
  PhaseStartConditionalWaiting.phaseStartSigmaAlgebra
    (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0)
    (StartDate k)
    (ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate_isPreRoundStoppingTime
      rate rewards C_star C_h control0 k)

/-- The full original positive-arm support charge on the actual kth H dates. -/
public def kthHCharge (k : Fin (p.T + 1)) : Source → ℝ :=
  ReferenceOriginalKthHandoverBirthLocalization.kthHChargePrefix
    rate rewards C_star C_h k p.T

/-- The capped positive-arm support charge on the same actual kth H dates. -/
public def kthHCappedCharge (k : Fin (p.T + 1)) : Source → ℝ :=
  ReferenceOriginalKthHandoverBirthLocalization.kthHCappedChargePrefix
    rate rewards C_star C_h k p.T

private theorem kthBirthMark_measurable (control0 : ContinuousLearningRows.TimeControl p)
    (k : Fin (p.T + 1)) (ell : Fin p.T) :
    MeasurableSet (BirthMark k ell) := by
  exact (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le'
    (ell.val + 1) _
    (ReferenceOriginalKthBirthMarkLocalization.mark_preRound_measurable
      rate rewards C_star C_h control0 k ell)

private theorem positiveArmCount_eq_positiveRewardCount (t : Fin p.T) :
    (((ReferenceActualLiveEmptySignedRewardCalendar.positiveArms rewards t).card : ℕ) : ℝ) =
      (ReferenceFirstCollectionUpConditionalService.positiveRewardCount rewards t : ℝ) := by
  have hden : 0 < ((D p : ℕ) : ℝ) := by exact_mod_cast D_pos p
  have hrow (a : Fin p.K) :
      0 < (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t).val a ↔
        0 < rewards t a := by
    change 0 < (rewards t a : ℝ) / (D p : ℝ) ↔ 0 < rewards t a
    rw [div_pos_iff_of_pos_right hden]
    constructor <;> intro h <;> exact_mod_cast h
  have hsets :
      ReferenceActualLiveEmptySignedRewardCalendar.positiveArms rewards t =
        ReferenceFirstCollectionUpConditionalService.positiveRewardArms rewards t := by
    ext a
    simp only [ReferenceActualLiveEmptySignedRewardCalendar.positiveArms,
      ReferenceFirstCollectionUpConditionalService.positiveRewardArms,
      Finset.mem_filter, Finset.mem_univ, true_and]
    exact hrow a
  unfold ReferenceFirstCollectionUpConditionalService.positiveRewardCount
  rw [hsets]

private theorem fixedHDate_mem_iff_pending_nonempty (ell t : Fin p.T) (z : Source) :
    t ∈ ReferenceOriginalKthHandoverBirthLocalization.fixedHDates
        rate rewards C_star C_h ell z ↔
      (ReferenceOriginalFixedInstallationHandoverSupport.pendingSet
        rate rewards C_star C_h ell t z).Nonempty := by
  classical
  simp [ReferenceOriginalKthHandoverBirthLocalization.fixedHDates,
    ReferenceOriginalFixedInstallationHandoverSupport.pendingSet, Finset.Nonempty]

private theorem pending_nonempty_iff_pending_exists (ell t : Fin p.T) (z : Source) :
    (ReferenceOriginalFixedInstallationHandoverSupport.pendingSet
      rate rewards C_star C_h ell t z).Nonempty ↔
      ∃ i : Fin (p.m - 1),
        ReferenceOriginalFixedInstallationHandoverSupport.pending
          rate rewards C_star C_h ell t i z := by
  classical
  simp [ReferenceOriginalFixedInstallationHandoverSupport.pendingSet, Finset.Nonempty]

private theorem fixedHChargePrefix_full_eq_G_H (ell : Fin p.T) (z : Source) :
    ReferenceOriginalKthHandoverBirthLocalization.fixedHChargePrefix
        rate rewards C_star C_h ell p.T z =
      ReferenceOriginalFixedInstallationHandoverWaitingCost.G_H
        rate rewards C_star C_h ell z := by
  classical
  have hfilter :
      (ReferenceOriginalKthHandoverBirthLocalization.fixedHDates
        rate rewards C_star C_h ell z).filter (fun t : Fin p.T => t.val < p.T) =
        ReferenceOriginalKthHandoverBirthLocalization.fixedHDates
          rate rewards C_star C_h ell z :=
    Finset.filter_true_of_mem (fun t _ => t.isLt)
  unfold ReferenceOriginalKthHandoverBirthLocalization.fixedHChargePrefix
    ReferenceOriginalFixedInstallationHandoverWaitingCost.G_H
  rw [hfilter,
    ReferenceOriginalKthHandoverBirthLocalization.fixedHDates, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro t ht
  simp only [pending_nonempty_iff_pending_exists,
    positiveArmCount_eq_positiveRewardCount]

private theorem B_hand_nonneg :
    0 ≤ ReferenceOriginalFixedInstallationHandoverWaitingCost.B_hand (p := p) := by
  have hm : 0 < ((p.m - 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_pos_of_lt
      (lt_of_lt_of_le (by decide : 1 < 2) p.two_le_m)
  have hK : 0 < (p.K : ℝ) := by exact_mod_cast ConstructorDimensions.K_pos p
  have hmarg : 1 ≤ ((p.m - 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_sub_one_of_lt
      (lt_of_lt_of_le (by decide : 1 < 2) p.two_le_m)
  have hlog : 0 ≤ Real.log ((p.m - 1 : ℕ) : ℝ) := Real.log_nonneg hmarg
  have hden : 0 < 1 - Real.exp (-1 : ℝ) := by
    have hexp : Real.exp (-1 : ℝ) < 1 :=
      Real.exp_lt_one_iff.mpr (by norm_num)
    linarith
  dsimp [ReferenceOriginalFixedInstallationHandoverWaitingCost.B_hand]
  positivity

private theorem kthHCharge_eq_marked_G_H (k : Fin (p.T + 1)) (z : Source) :
    kthHCharge rate rewards C_star C_h k z =
      ∑ ell : Fin p.T,
        (BirthMark k ell).indicator
          (ReferenceOriginalFixedInstallationHandoverWaitingCost.G_H
            rate rewards C_star C_h ell) z := by
  classical
  calc
    kthHCharge rate rewards C_star C_h k z =
        ReferenceOriginalKthHandoverBirthLocalization.kthHChargePrefix
          rate rewards C_star C_h k p.T z := rfl
    _ = ∑ ell : Fin p.T,
          (BirthMark k ell).indicator
            (ReferenceOriginalKthHandoverBirthLocalization.fixedHChargePrefix
              rate rewards C_star C_h ell p.T) z :=
      ReferenceOriginalKthHandoverBirthLocalization.chargePrefix_mark_reindex
        rate rewards C_star C_h k p.T z
    _ = ∑ ell : Fin p.T,
          (BirthMark k ell).indicator
            (ReferenceOriginalFixedInstallationHandoverWaitingCost.G_H
              rate rewards C_star C_h ell) z := by
      apply Finset.sum_congr rfl
      intro ell hell
      by_cases hz : z ∈ BirthMark k ell
      · simp [hz, fixedHChargePrefix_full_eq_G_H]
      · simp [hz]

/-- The original kth uncapped support charge is integrable on the original
source law. -/
public theorem kthHCharge_integrable (k : Fin (p.T + 1)) :
    Integrable (kthHCharge rate rewards C_star C_h k) μ := by
  simpa [kthHCharge] using
    ReferenceOriginalKthHandoverBirthLocalization.kthHChargePrefix_integrable
      rate rewards C_star C_h k p.T

/-- The original kth capped support charge is integrable on the original
source law. -/
public theorem kthHCappedCharge_integrable (k : Fin (p.T + 1)) :
    Integrable (kthHCappedCharge rate rewards C_star C_h k) μ := by
  simpa [kthHCappedCharge] using
    ReferenceOriginalKthHandoverBirthLocalization.kthHCappedChargePrefix_integrable
      rate rewards C_star C_h k p.T

/-- Integrating the uncapped kth H charge over any event in the same original
stopped-start field costs at most the fixed handover constant times its mass. -/
public theorem setIntegral_kthHCharge_le_B_hand (k : Fin (p.T + 1))
    (B0 : Set Source)
    (hB0 : MeasurableSet[kthHStartSigmaAlgebra rate rewards C_star C_h control0 k] B0) :
    ∫ z in B0, kthHCharge rate rewards C_star C_h k z ∂μ ≤
      ReferenceOriginalFixedInstallationHandoverWaitingCost.B_hand (p := p) *
        (BootstrapPrivateRoundStreams.sourceInputLaw p).real B0 := by
  classical
  let markedEvent : Fin p.T → Set Source := fun ell => B0 ∩ BirthMark k ell
  have hfieldLe :
      kthHStartSigmaAlgebra rate rewards C_star C_h control0 k ≤
        (inferInstance : MeasurableSpace Source) :=
    PhaseStartConditionalWaiting.phaseStartSigmaAlgebra_le
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0)
      (StartDate k)
      (ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate_isPreRoundStoppingTime
        rate rewards C_star C_h control0 k)
  have hB0Ambient : MeasurableSet B0 := hfieldLe B0 hB0
  have htermsIntegral : ∀ ell ∈ Finset.univ,
      Integrable (fun z : Source =>
        (BirthMark k ell).indicator
          (ReferenceOriginalFixedInstallationHandoverWaitingCost.G_H
            rate rewards C_star C_h ell) z)
        ((BootstrapPrivateRoundStreams.sourceInputLaw p).restrict B0) := by
    intro ell hell
    exact ((ReferenceOriginalFixedInstallationHandoverWaitingCost.integrable_G_H
      rate rewards C_star C_h control0 ell).indicator
      (kthBirthMark_measurable rate rewards C_star C_h control0 k ell)).mono_measure
        Measure.restrict_le_self
  have hsumIntegral :
      ∫ z in B0, (∑ ell : Fin p.T,
        (BirthMark k ell).indicator
          (ReferenceOriginalFixedInstallationHandoverWaitingCost.G_H
            rate rewards C_star C_h ell) z) ∂μ =
        ∑ ell : Fin p.T, ∫ z in B0,
          (BirthMark k ell).indicator
            (ReferenceOriginalFixedInstallationHandoverWaitingCost.G_H
              rate rewards C_star C_h ell) z ∂μ := by
    exact integral_finsetSum Finset.univ htermsIntegral
  have hlocal :
      ∀ ell : Fin p.T,
        ∫ z in markedEvent ell,
          ReferenceOriginalFixedInstallationHandoverWaitingCost.G_H
            rate rewards C_star C_h ell z ∂μ ≤
        ReferenceOriginalFixedInstallationHandoverWaitingCost.B_hand (p := p) *
          (BootstrapPrivateRoundStreams.sourceInputLaw p).real (markedEvent ell) := by
    intro ell
    have hmarkField : MeasurableSet[
        ReferenceOriginalFixedInstallationHandoverWaitingCost.phaseStartSigmaAlgebra
          rate rewards C_star C_h control0 ell] (markedEvent ell) := by
      simpa only [markedEvent, ReferenceOriginalFixedInstallationHandoverWaitingCost.phaseStartSigmaAlgebra]
        using ReferenceOriginalKthHandoverBirthLocalization.marked_event_at_rawSigma
          rate rewards C_star C_h control0 k ell B0 hB0
    exact ReferenceOriginalFixedInstallationHandoverWaitingCost.setIntegral_G_H_le_B_hand
      rate rewards C_star C_h control0 ell (markedEvent ell) hmarkField
  have hpairwise : Set.PairwiseDisjoint
      (↑(Finset.univ : Finset (Fin p.T))) markedEvent := by
    intro ell hell ell' hell' hne
    apply Set.disjoint_left.mpr
    intro z hz hz'
    exact Set.disjoint_left.mp
      (ReferenceOriginalKthBirthMarkLocalization.marks_disjoint
        rate rewards C_star C_h k ell ell' hne) hz.2 hz'.2
  have hmarkedMeasurable : ∀ ell ∈ Finset.univ, MeasurableSet (markedEvent ell) := by
    intro ell hell
    exact hB0Ambient.inter
      (kthBirthMark_measurable rate rewards C_star C_h control0 k ell)
  have hunionSubset : (⋃ ell ∈ Finset.univ, markedEvent ell) ⊆ B0 := by
    intro z hz
    simp only [Set.mem_iUnion, Finset.mem_univ] at hz
    rcases hz with ⟨ell, _, hz⟩
    exact hz.1
  have hmass :
      (∑ ell : Fin p.T,
        (BootstrapPrivateRoundStreams.sourceInputLaw p).real (markedEvent ell)) ≤
        (BootstrapPrivateRoundStreams.sourceInputLaw p).real B0 := by
    calc
      (∑ ell : Fin p.T,
        (BootstrapPrivateRoundStreams.sourceInputLaw p).real (markedEvent ell)) =
          (BootstrapPrivateRoundStreams.sourceInputLaw p).real
            (⋃ ell ∈ Finset.univ, markedEvent ell) := by
        symm
        exact measureReal_biUnion_finset hpairwise hmarkedMeasurable
      _ ≤ (BootstrapPrivateRoundStreams.sourceInputLaw p).real B0 :=
        measureReal_mono hunionSubset
  calc
    ∫ z in B0, kthHCharge rate rewards C_star C_h k z ∂μ =
        ∫ z in B0, (∑ ell : Fin p.T,
          (BirthMark k ell).indicator
            (ReferenceOriginalFixedInstallationHandoverWaitingCost.G_H
              rate rewards C_star C_h ell) z) ∂μ := by
      apply setIntegral_congr_fun hB0Ambient
      intro z hz
      exact kthHCharge_eq_marked_G_H rate rewards C_star C_h k z
    _ = ∑ ell : Fin p.T, ∫ z in B0,
          (BirthMark k ell).indicator
            (ReferenceOriginalFixedInstallationHandoverWaitingCost.G_H
              rate rewards C_star C_h ell) z ∂μ := hsumIntegral
    _ = ∑ ell : Fin p.T, ∫ z in markedEvent ell,
          ReferenceOriginalFixedInstallationHandoverWaitingCost.G_H
            rate rewards C_star C_h ell z ∂μ := by
      apply Finset.sum_congr rfl
      intro ell hell
      exact setIntegral_indicator
        (kthBirthMark_measurable rate rewards C_star C_h control0 k ell)
    _ ≤ ∑ ell : Fin p.T,
          ReferenceOriginalFixedInstallationHandoverWaitingCost.B_hand (p := p) *
            (BootstrapPrivateRoundStreams.sourceInputLaw p).real (markedEvent ell) :=
      Finset.sum_le_sum fun ell hell => hlocal ell
    _ = ReferenceOriginalFixedInstallationHandoverWaitingCost.B_hand (p := p) *
          ∑ ell : Fin p.T,
            (BootstrapPrivateRoundStreams.sourceInputLaw p).real (markedEvent ell) := by
      rw [← Finset.mul_sum]
    _ ≤ ReferenceOriginalFixedInstallationHandoverWaitingCost.B_hand (p := p) *
          (BootstrapPrivateRoundStreams.sourceInputLaw p).real B0 :=
      mul_le_mul_of_nonneg_left hmass B_hand_nonneg

/-- Almost-everywhere conditional expectation bound for the original kth
uncapped H charge, conditioned on that same original kth stopped-start field. -/
public theorem condExp_kthHCharge_le_B_hand (k : Fin (p.T + 1)) :
    μ[kthHCharge rate rewards C_star C_h k |
      kthHStartSigmaAlgebra rate rewards C_star C_h control0 k] ≤ᵐ[μ]
      fun _ => ReferenceOriginalFixedInstallationHandoverWaitingCost.B_hand (p := p) := by
  have hfieldLe :
      kthHStartSigmaAlgebra rate rewards C_star C_h control0 k ≤
        (inferInstance : MeasurableSpace Source) :=
    PhaseStartConditionalWaiting.phaseStartSigmaAlgebra_le
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0)
      (StartDate k)
      (ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate_isPreRoundStoppingTime
        rate rewards C_star C_h control0 k)
  have hcondInt : Integrable
      (μ[kthHCharge rate rewards C_star C_h k |
        kthHStartSigmaAlgebra rate rewards C_star C_h control0 k]) μ :=
    integrable_condExp
  have hcondTrim : Integrable
      (μ[kthHCharge rate rewards C_star C_h k |
        kthHStartSigmaAlgebra rate rewards C_star C_h control0 k])
      ((BootstrapPrivateRoundStreams.sourceInputLaw p).trim hfieldLe) :=
    hcondInt.trim hfieldLe stronglyMeasurable_condExp
  have hconstTrim : Integrable
      (fun _ : Source =>
        ReferenceOriginalFixedInstallationHandoverWaitingCost.B_hand (p := p))
      ((BootstrapPrivateRoundStreams.sourceInputLaw p).trim hfieldLe) :=
    (integrable_const _).trim hfieldLe stronglyMeasurable_const
  have htrimBound :
      μ[kthHCharge rate rewards C_star C_h k |
        kthHStartSigmaAlgebra rate rewards C_star C_h control0 k] ≤ᵐ[
          (BootstrapPrivateRoundStreams.sourceInputLaw p).trim hfieldLe]
        fun _ => ReferenceOriginalFixedInstallationHandoverWaitingCost.B_hand (p := p) := by
    apply ae_le_of_forall_setIntegral_le hcondTrim hconstTrim
    intro B hB hBfinite
    calc
      ∫ z in B, μ[kthHCharge rate rewards C_star C_h k |
          kthHStartSigmaAlgebra rate rewards C_star C_h control0 k] z ∂
            (BootstrapPrivateRoundStreams.sourceInputLaw p).trim hfieldLe =
          ∫ z in B, μ[kthHCharge rate rewards C_star C_h k |
              kthHStartSigmaAlgebra rate rewards C_star C_h control0 k] z ∂μ :=
        (setIntegral_trim hfieldLe stronglyMeasurable_condExp hB).symm
      _ = ∫ z in B, kthHCharge rate rewards C_star C_h k z ∂μ :=
        setIntegral_condExp hfieldLe
          (kthHCharge_integrable rate rewards C_star C_h k) hB
      _ ≤ ReferenceOriginalFixedInstallationHandoverWaitingCost.B_hand (p := p) *
          (BootstrapPrivateRoundStreams.sourceInputLaw p).real B :=
        setIntegral_kthHCharge_le_B_hand rate rewards C_star C_h control0 k B hB
      _ = ∫ z in B,
            (fun _ : Source =>
              ReferenceOriginalFixedInstallationHandoverWaitingCost.B_hand (p := p)) z ∂μ := by
        simp [smul_eq_mul, mul_comm]
      _ = ∫ z in B,
            (fun _ : Source =>
              ReferenceOriginalFixedInstallationHandoverWaitingCost.B_hand (p := p)) z ∂
                (BootstrapPrivateRoundStreams.sourceInputLaw p).trim hfieldLe :=
        setIntegral_trim hfieldLe stronglyMeasurable_const hB
  exact ae_le_of_ae_le_trim htrimBound

/-- The capped kth support charge is pointwise bounded by the uncapped charge,
using the source live-empty cap on the same dates. -/
public theorem kthHCappedCharge_le_kthHCharge (k : Fin (p.T + 1)) (z : Source) :
    kthHCappedCharge rate rewards C_star C_h k z ≤
      kthHCharge rate rewards C_star C_h k z :=
  ReferenceOriginalKthHandoverBirthLocalization.kthHCappedChargePrefix_le
    rate rewards C_star C_h k p.T z

/-- The capped kth H charge inherits the same stopped-event integral bound. -/
public theorem setIntegral_kthHCappedCharge_le_B_hand (k : Fin (p.T + 1))
    (B0 : Set Source)
    (hB0 : MeasurableSet[kthHStartSigmaAlgebra rate rewards C_star C_h control0 k] B0) :
    ∫ z in B0, kthHCappedCharge rate rewards C_star C_h k z ∂μ ≤
      ReferenceOriginalFixedInstallationHandoverWaitingCost.B_hand (p := p) *
        (BootstrapPrivateRoundStreams.sourceInputLaw p).real B0 := by
  exact (setIntegral_mono_ae_restrict
      (kthHCappedCharge_integrable rate rewards C_star C_h k).integrableOn
      (kthHCharge_integrable rate rewards C_star C_h k).integrableOn
      (Filter.Eventually.of_forall fun z => kthHCappedCharge_le_kthHCharge
        rate rewards C_star C_h k z)).trans
    (setIntegral_kthHCharge_le_B_hand rate rewards C_star C_h control0 k B0 hB0)

/-- Almost-everywhere conditional expectation bound for the capped kth H
support charge at the same original stopped-start field. -/
public theorem condExp_kthHCappedCharge_le_B_hand (k : Fin (p.T + 1)) :
    μ[kthHCappedCharge rate rewards C_star C_h k |
      kthHStartSigmaAlgebra rate rewards C_star C_h control0 k] ≤ᵐ[μ]
      fun _ => ReferenceOriginalFixedInstallationHandoverWaitingCost.B_hand (p := p) := by
  exact (condExp_mono
      (kthHCappedCharge_integrable rate rewards C_star C_h k)
      (kthHCharge_integrable rate rewards C_star C_h k)
      (Filter.Eventually.of_forall fun z => kthHCappedCharge_le_kthHCharge
        rate rewards C_star C_h k z)).trans
    (condExp_kthHCharge_le_B_hand rate rewards C_star C_h control0 k)

end Bandits.Support.ReferenceOriginalKthHandoverConditionalWaitingCost

end
