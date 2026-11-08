/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveInitialStopIdentification
public import Bandits.Support.ReferenceOriginalKthReleaseSignedChargeLocalization

import Mathlib.Probability.Process.Stopping
import Mathlib.Tactic

/-!
# Original initial fixed-installation signed release cost

The initial physical installation branch is transported to the accepted
first-live signed release estimate on its literal launch event.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open scoped Classical BigOperators

namespace Bandits.Support.ReferenceOriginalInitialReleaseSignedCost

abbrev Parameters := ConstructorDimensions.Parameters
abbrev Source (p : Parameters) := BootstrapPrivateRoundStreams.SourceInput p

variable {p : Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ)

local notation "L" => fun z : Source p =>
  ReferenceInitializationRun.launchRound
    (ReferenceCompletePhysicalHistory.generatedInput rate z rewards C_star C_h)
local notation "s" =>
  ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart rate rewards C_star C_h

private theorem initial_marker_iff_physicalStart (ell : Fin p.T) (z : Source p) :
    ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferInitialMarkerAt
        rate rewards C_star C_h ell z ↔ s z = ell.val := by
  constructor
  · intro h
    exact h.2.1.symm
  · intro h
    exact ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferInitialMarkerAt_of_launch
      rate rewards C_star C_h ell z h.symm

private theorem initial_marker_iff_launch_round (ell : Fin p.T) (z : Source p)
    :
    ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferInitialMarkerAt
        rate rewards C_star C_h ell z ↔ L z = ell.val + 1 := by
  have hstart :=
    ReferenceFirstLiveInitialTransferStartFields.initial_transfer_start_fields
      rate rewards C_star C_h z
  constructor
  · intro hmarker
    have hphysical :=
      (initial_marker_iff_physicalStart rate rewards C_star C_h ell z).mp hmarker
    calc
      L z = s z + 1 := hstart.1
      _ = ell.val + 1 := by rw [hphysical]
  · intro hlaunch
    have hphysical : s z = ell.val := by
      exact Nat.succ.inj (hstart.1.symm.trans hlaunch)
    exact (initial_marker_iff_physicalStart rate rewards C_star C_h ell z).mpr hphysical

private theorem initial_marker_measurable_at_launch
    (control0 : ContinuousLearningRows.TimeControl p) (ell : Fin p.T) :
    MeasurableSet[
      PhaseStartConditionalWaiting.phaseStartSigmaAlgebra
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0) L
        (ReferenceFirstLiveInitialTransferStartFields.initial_launch_preRound_stopping
          rate rewards C_star C_h control0)]
      {z : Source p |
        ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferInitialMarkerAt
          rate rewards C_star C_h ell z} := by
  let hL := ReferenceFirstLiveInitialTransferStartFields.initial_launch_preRound_stopping
    rate rewards C_star C_h control0
  let hLstop := PhaseStartConditionalWaiting.isStoppingTime_of_preRound
    (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0) L hL
  have hset :
      {z : Source p |
        ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferInitialMarkerAt
          rate rewards C_star C_h ell z} =
        {z | (L z : WithTop ℕ) = (ell.val + 1 : WithTop ℕ)} := by
    ext z
    change
      ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferInitialMarkerAt
        rate rewards C_star C_h ell z ↔
      (L z : WithTop ℕ) = (ell.val + 1 : WithTop ℕ)
    rw [initial_marker_iff_launch_round rate rewards C_star C_h ell z]
    norm_cast
  rw [hset]
  exact hLstop.measurableSet_eq' (ell.val + 1)

public theorem initial_support_iff_firstLive_support
    (ell : Fin p.T) (z : Source p)
    (hmarker : ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferInitialMarkerAt
      rate rewards C_star C_h ell z) (t : Fin p.T) :
    ReferenceOriginalInstallationStoppedReleasePhase.supportAt
        rate rewards C_star C_h ell.val t.val z ↔
      t.val + 1 ∈ ReferenceFirstLiveSourceStoppedReleaseEndpoint.actualFirstReleaseSupport
        rate rewards C_star C_h z := by
  let W := ReferenceFirstLiveSourceStoppedHandoverEndpoint.window rate rewards C_star C_h
  let missing := ReferenceFirstLiveSourceStoppedHandoverEndpoint.missing rate
  have hstart : s z = ell.val :=
    (initial_marker_iff_physicalStart rate rewards C_star C_h ell z).mp hmarker
  have hgateEq :
      ReferenceOriginalInstallationStoppedReleasePhase.originalGateSupport
          rate rewards C_star C_h ell.val z =
        ReferenceFirstLiveSourceStoppedReleaseEndpoint.actualGateSupport
          rate rewards C_star C_h z := by
    change ReferenceLocalReleaseGateChronology.gateSupport ell.val
        (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h) =
      ReferenceLocalReleaseGateChronology.gateSupport
        (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
        (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)
    rw [← hstart]
    simp only [ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart]
  have hraw := ReferenceFirstLiveInitialTransferChronology.raw_release_calendar
    rate rewards C_star C_h z
  have hbad := ReferenceFirstLiveInitialStopIdentification.releaseSupport_eq_originalFirstBadFilter
    rate rewards C_star C_h z
  have hmemBad :=
    ReferenceFirstLiveInitialStopIdentification.originalFirstBadReleaseFilter_mem_iff
      rate rewards C_star C_h z
  have hsupport :=
    ReferenceOriginalInstallationStoppedReleasePhase.supportAt_iff_stopped_originalGate
      rate rewards C_star C_h ell.val (t.val) z t.isLt
  constructor
  · intro hsupp
    obtain ⟨hgate, hdate⟩ := hsupport.mp hsupp
    rw [hgateEq] at hgate
    rw [hraw] at hgate
    obtain ⟨r, hr, hdateR⟩ := Finset.mem_image.mp hgate
    obtain ⟨hr, hempty⟩ := Finset.mem_filter.mp hr
    obtain ⟨k, hk, heq⟩ := List.mem_iff_getElem.mp (List.mem_toFinset.mp hr)
    have hdateK : (W z)[k].input.time.val + 1 = t.val + 1 := by
      rw [← heq] at hdateR
      exact hdateR
    have hemptyK : missing ((W z)[k]) = ∅ := by
      rw [← heq] at hempty
      exact hempty
    let kFin : Fin (W z).length := ⟨k, hk⟩
    have hfilter :
        t.val + 1 ∈
          ReferenceFirstLiveInitialStopIdentification.originalFirstBadReleaseFilter
            rate rewards C_star C_h z :=
      (hmemBad (t.val + 1)).2 ⟨kFin, hdateK, hemptyK, by simpa using hdate⟩
    rw [hbad]
    exact hfilter
  · intro hrelease
    rw [hbad] at hrelease
    obtain ⟨k, hdate, hempty, hbound⟩ := (hmemBad (t.val + 1)).mp hrelease
    have hgate : t.val + 1 ∈
        ReferenceFirstLiveSourceStoppedReleaseEndpoint.actualGateSupport
          rate rewards C_star C_h z := by
      rw [hraw]
      apply Finset.mem_image.mpr
      refine ⟨(W z)[k.val], Finset.mem_filter.mpr ?_, hdate⟩
      exact ⟨List.mem_toFinset.mpr (List.getElem_mem k.isLt), hempty⟩
    have hgate' : t.val + 1 ∈
        ReferenceOriginalInstallationStoppedReleasePhase.originalGateSupport
          rate rewards C_star C_h ell.val z := by
      rw [hgateEq]
      exact hgate
    exact hsupport.mpr ⟨hgate', hbound⟩

private theorem initial_supportDates_eq_firstLive_support
    (ell : Fin p.T) (z : Source p)
    (hmarker : ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferInitialMarkerAt
      rate rewards C_star C_h ell z) :
    ReferenceOriginalInstallationStoppedReleasePhase.supportDates
        rate rewards C_star C_h ell.val z =
      ReferenceFirstLiveSourceStoppedReleaseEndpoint.actualFirstReleaseSupport
        rate rewards C_star C_h z := by
  classical
  ext d
  simp only [ReferenceOriginalInstallationStoppedReleasePhase.supportDates,
    Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨t, hs, hdate⟩
    have hsupport :=
      (initial_support_iff_firstLive_support rate rewards C_star C_h ell z hmarker t).mp hs
    simpa only [hdate] using hsupport
  · intro hd
    have hbad :=
      ReferenceFirstLiveInitialStopIdentification.releaseSupport_eq_originalFirstBadFilter
        rate rewards C_star C_h z
    have hmemBad :=
      ReferenceFirstLiveInitialStopIdentification.originalFirstBadReleaseFilter_mem_iff
        rate rewards C_star C_h z d
    obtain ⟨k, hdate, hempty, hbound⟩ := (hmemBad).mp (hbad ▸ hd)
    let t := (ReferenceFirstLiveSourceStoppedHandoverEndpoint.window
      rate rewards C_star C_h z)[k.val].input.time
    refine ⟨t, ?_, ?_⟩
    · have hgateDate : t.val + 1 ∈
          ReferenceFirstLiveSourceStoppedReleaseEndpoint.actualFirstReleaseSupport
            rate rewards C_star C_h z := by
        simpa only [t, hdate] using hd
      exact (initial_support_iff_firstLive_support rate rewards C_star C_h ell z
        hmarker t).mpr hgateDate
    · simpa only [t] using hdate

public theorem initial_sigmaR_eq_firstLive_sigma
    (ell : Fin p.T) (z : Source p)
    (hmarker : ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferInitialMarkerAt
      rate rewards C_star C_h ell z) :
    ReferenceOriginalInstallationStoppedReleasePhase.sigmaR
        rate rewards C_star C_h ell.val z =
      ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstReleaseSigma
        rate rewards C_star C_h z := by
  have hdates := initial_supportDates_eq_firstLive_support
    rate rewards C_star C_h ell z hmarker
  have hb := ReferenceOriginalInstallationStoppedReleasePhase.sigmaR_bounds
    rate rewards C_star C_h ell.val z
  have hb' := ReferenceFirstLiveSourceStoppedReleaseEndpoint.actual_first_release_interval
    rate rewards C_star C_h z
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hn : ReferenceOriginalInstallationStoppedReleasePhase.sigmaR
        rate rewards C_star C_h ell.val z ≤ p.T := by omega
    obtain ⟨t, ht, hsupp⟩ :=
      (ReferenceOriginalInstallationStoppedReleasePhase.sigmaR_le_iff_exists_supported_date
        rate rewards C_star C_h ell.val z
        (ReferenceOriginalInstallationStoppedReleasePhase.sigmaR
          rate rewards C_star C_h ell.val z) hn).mp le_rfl
    have hlive := (initial_support_iff_firstLive_support rate rewards C_star C_h
      ell z hmarker t).mp hsupp
    have hstart :=
      (ReferenceFirstLiveSourceStoppedReleaseAdaptation.first_release_sigma_le_iff
        rate rewards C_star C_h z _ hn).2 ⟨t, ht, hlive⟩
    omega
  · have hn : ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstReleaseSigma
        rate rewards C_star C_h z ≤ p.T := by omega
    obtain ⟨t, ht, hlive⟩ :=
      (ReferenceFirstLiveSourceStoppedReleaseAdaptation.first_release_sigma_le_iff
        rate rewards C_star C_h z
        (ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstReleaseSigma
          rate rewards C_star C_h z) hn).mp le_rfl
    have hsupp := (initial_support_iff_firstLive_support rate rewards C_star C_h
      ell z hmarker t).mpr hlive
    have hstart :=
      (ReferenceOriginalInstallationStoppedReleasePhase.sigmaR_le_iff_exists_supported_date
        rate rewards C_star C_h ell.val z _ hn).2 ⟨t, ht, hsupp⟩
    omega

public theorem initial_thetaR_eq_firstLive_theta
    (ell : Fin p.T) (z : Source p)
    (hmarker : ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferInitialMarkerAt
      rate rewards C_star C_h ell z) :
    ReferenceOriginalInstallationStoppedReleasePhase.thetaR
        rate rewards C_star C_h ell.val z =
      ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstReleaseTheta
        rate rewards C_star C_h z := by
  have hdates := initial_supportDates_eq_firstLive_support
    rate rewards C_star C_h ell z hmarker
  have hsigma := initial_sigmaR_eq_firstLive_sigma rate rewards C_star C_h ell z hmarker
  have hinterval :=
    ReferenceOriginalInstallationStoppedReleasePhase.supportDates_eq_Ico_sigma_theta
      rate rewards C_star C_h ell.val z
  have hinterval' :=
    ReferenceFirstLiveSourceStoppedReleaseEndpoint.actual_first_release_interval
      rate rewards C_star C_h z
  by_cases hempty :
      ReferenceFirstLiveSourceStoppedReleaseEndpoint.actualFirstReleaseSupport
        rate rewards C_star C_h z = ∅
  · have hdatesEmpty :
        ReferenceOriginalInstallationStoppedReleasePhase.supportDates
          rate rewards C_star C_h ell.val z = ∅ := hdates.trans hempty
    have hsentinel :=
      ReferenceFirstLiveSourceStoppedReleaseEndpoint.empty_first_release_endpoints
        rate rewards C_star C_h z hempty
    have htheta : ReferenceOriginalInstallationStoppedReleasePhase.thetaR
        rate rewards C_star C_h ell.val z = p.T + 1 := by
      simp [ReferenceOriginalInstallationStoppedReleasePhase.thetaR, hdatesEmpty]
    omega
  · have hIco :
        Finset.Ico
          (ReferenceOriginalInstallationStoppedReleasePhase.sigmaR
            rate rewards C_star C_h ell.val z)
          (ReferenceOriginalInstallationStoppedReleasePhase.thetaR
            rate rewards C_star C_h ell.val z) =
        Finset.Ico
          (ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstReleaseSigma
            rate rewards C_star C_h z)
          (ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstReleaseTheta
            rate rewards C_star C_h z) := by
      rw [← hinterval, hdates, hinterval'.1]
    by_contra hneTheta
    rcases lt_or_gt_of_ne hneTheta with hlt | hgt
    · have hleft : ReferenceOriginalInstallationStoppedReleasePhase.sigmaR
          rate rewards C_star C_h ell.val z ≤
        ReferenceOriginalInstallationStoppedReleasePhase.thetaR
          rate rewards C_star C_h ell.val z :=
        (ReferenceOriginalInstallationStoppedReleasePhase.sigmaR_bounds
          rate rewards C_star C_h ell.val z).2.1
      have hmem : ReferenceOriginalInstallationStoppedReleasePhase.thetaR
          rate rewards C_star C_h ell.val z ∈
        Finset.Ico
          (ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstReleaseSigma
            rate rewards C_star C_h z)
          (ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstReleaseTheta
            rate rewards C_star C_h z) := by
        exact Finset.mem_Ico.mpr ⟨by rw [← hsigma]; exact hleft, hlt⟩
      have := Finset.mem_Ico.mp (hIco.symm ▸ hmem)
      omega
    · have hleft : ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstReleaseSigma
          rate rewards C_star C_h z ≤
        ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstReleaseTheta
          rate rewards C_star C_h z := hinterval'.2.2.1
      have hmem : ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstReleaseTheta
          rate rewards C_star C_h z ∈
        Finset.Ico
          (ReferenceOriginalInstallationStoppedReleasePhase.sigmaR
            rate rewards C_star C_h ell.val z)
          (ReferenceOriginalInstallationStoppedReleasePhase.thetaR
            rate rewards C_star C_h ell.val z) := by
        exact Finset.mem_Ico.mpr ⟨by rw [hsigma]; exact hleft, hgt⟩
      have := Finset.mem_Ico.mp (hIco ▸ hmem)
      omega

public theorem initial_signed_total_eq_firstLive
    (ell : Fin p.T) (z : Source p)
    (hmarker : ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferInitialMarkerAt
      rate rewards C_star C_h ell z) :
    (∑ t : Fin p.T,
      if ReferenceOriginalInstallationStoppedReleasePhase.supportAt
          rate rewards C_star C_h ell.val t.val z then
        ReferenceOriginalInstallationReleaseSignedCharge.actualFixedReleaseSignedDeficit
          rate rewards C_star C_h ell.val t z else 0) =
      ReferenceFirstLiveStoppedReleaseCalendarSignedCost.totalSignedCost
        rate rewards C_star C_h z := by
  rw [ReferenceFirstLiveStoppedReleaseCalendarSignedCost.totalSignedCost]
  apply Finset.sum_congr rfl
  intro t ht
  have hsupport := initial_support_iff_firstLive_support
    rate rewards C_star C_h ell z hmarker t
  by_cases hs : ReferenceOriginalInstallationStoppedReleasePhase.supportAt
      rate rewards C_star C_h ell.val t.val z
  · have hmem := hsupport.mp hs
    have hentry :
        (ReferenceSourcePrefixHistoryFiltration.entry rate rewards C_star C_h
          ell.val t z).map Prod.fst = some true := by
      exact (ReferenceOriginalInstallationStoppedReleasePhase.supportAt_iff
        rate rewards C_star C_h ell.val t.val z t.isLt).mp hs |>.1
    simp only [hs]
    rw [ReferenceFirstLiveStoppedReleaseCalendarSignedCost.signedStep,
      ite_eq_left hmem]
    simp only [ReferenceOriginalInstallationReleaseSignedCharge.actualFixedReleaseSignedDeficit,
      hentry]
    rfl
  · have hmem : ¬ t.val + 1 ∈
        ReferenceFirstLiveSourceStoppedReleaseEndpoint.actualFirstReleaseSupport
          rate rewards C_star C_h z := fun h => hs (hsupport.mpr h)
    simp [hs, ReferenceFirstLiveStoppedReleaseCalendarSignedCost.signedStep, hmem]

/-- The initial fixed-installation branch inherits the actual first-release
signed-cost estimate by transporting its stopped event across the launch
fiber. -/
public theorem initial_fixed_label_release_setIntegral_bound
    (control0 : ContinuousLearningRows.TimeControl p) (ell : Fin p.T)
    (B : Set (Source p))
    (hB : MeasurableSet[
      PhaseStartConditionalWaiting.phaseStartSigmaAlgebra
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0)
        (ReferenceOriginalInstallationStoppedReleasePhase.sigmaR
          rate rewards C_star C_h ell.val)
        (ReferenceOriginalInstallationStoppedReleasePhase.sigmaR_stopping
          rate rewards C_star C_h control0 ell.val)] B) :
    (∫ z in B ∩ {z : Source p |
      ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferInitialMarkerAt
        rate rewards C_star C_h ell z},
      ∑ t : Fin p.T,
        if ReferenceOriginalInstallationStoppedReleasePhase.supportAt
            rate rewards C_star C_h ell.val t.val z then
          ReferenceOriginalInstallationReleaseSignedCharge.actualFixedReleaseSignedDeficit
            rate rewards C_star C_h ell.val t z else 0
      ∂BootstrapPrivateRoundStreams.sourceInputLaw p) ≤
      (2 * ((p.m : ℝ) - 1) * (p.K : ℝ) +
        (12 * ((p.m : ℝ) - 1) * (p.K : ℝ) / (1 - Real.exp (-1))) *
          (Real.log ((p.m : ℝ) - 1) + 1)) *
        Measure.real (BootstrapPrivateRoundStreams.sourceInputLaw p)
          (B ∩ {z : Source p |
            ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferInitialMarkerAt
              rate rewards C_star C_h ell z}) := by
  let H := ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0
  let ρ := ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstReleaseSigma
    rate rewards C_star C_h
  let τ := ReferenceOriginalInstallationStoppedReleasePhase.sigmaR
    rate rewards C_star C_h ell.val
  let I : Set (Source p) := {z |
    ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferInitialMarkerAt
      rate rewards C_star C_h ell z}
  let hL := ReferenceFirstLiveInitialTransferStartFields.initial_launch_preRound_stopping
    rate rewards C_star C_h control0
  let hρ := ReferenceFirstLiveSourceStoppedReleaseAdaptation.first_release_sigma_stopping
    rate rewards C_star C_h control0
  let hτ := ReferenceOriginalInstallationStoppedReleasePhase.sigmaR_stopping
    rate rewards C_star C_h control0 ell.val
  let FR := PhaseStartConditionalWaiting.phaseStartSigmaAlgebra H ρ hρ
  have hlaunchIncluded :
      PhaseStartConditionalWaiting.phaseStartSigmaAlgebra H
        (fun z : Source p => L z) hL ≤ FR := by
    exact (ReferenceFirstLiveInitialTransferStartFields.initial_phase_start_sigmaAlgebra_inclusions
      rate rewards C_star C_h control0).2
  have hIlaunch := initial_marker_measurable_at_launch
    rate rewards C_star C_h control0 ell
  have hIFirst : MeasurableSet[FR] I := by
    exact hlaunchIncluded I (by simpa [I, hL] using hIlaunch)
  have hρstop := PhaseStartConditionalWaiting.isStoppingTime_of_preRound H ρ hρ
  have hIsigma := (hρstop.measurableSet I).mp hIFirst
  have hTstop := PhaseStartConditionalWaiting.isStoppingTime_of_preRound H τ hτ
  have hBstop := (hTstop.measurableSet B).mp hB
  have hQ : MeasurableSet[FR] (B ∩ I) := by
    apply (hρstop.measurableSet (B ∩ I)).mpr
    refine ⟨hBstop.1.inter hIsigma.1, ?_⟩
    intro n
    have hset : (B ∩ I) ∩ {z | (ρ z : WithTop ℕ) ≤ (n : WithTop ℕ)} =
        (B ∩ {z | (τ z : WithTop ℕ) ≤ (n : WithTop ℕ)}) ∩
          (I ∩ {z | (ρ z : WithTop ℕ) ≤ (n : WithTop ℕ)}) := by
      ext z
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨⟨hzB, hzI⟩, hzρ⟩
        have hends := initial_sigmaR_eq_firstLive_sigma
          rate rewards C_star C_h ell z hzI
        have hEq : τ z = ρ z := by simpa [τ, ρ] using hends
        have hzτ : (τ z : WithTop ℕ) ≤ (n : WithTop ℕ) := by
          rw [hEq]
          exact hzρ
        exact ⟨⟨hzB, hzτ⟩, hzI, hzρ⟩
      · rintro ⟨⟨hzB, hzτ⟩, hzI, hzρ⟩
        exact ⟨⟨hzB, hzI⟩, hzρ⟩
    exact hset.symm ▸ (hBstop.2 n).inter (hIsigma.2 n)
  have hcost (z : Source p) (hz : z ∈ B ∩ I) :=
    initial_signed_total_eq_firstLive rate rewards C_star C_h ell z hz.2
  have hQambient :=
    (PhaseStartConditionalWaiting.phaseStartSigmaAlgebra_le H ρ hρ) (B ∩ I) hQ
  have hbound :=
    ReferenceFirstLiveStoppedReleaseSignedCost.actual_first_release_signed_cost_setIntegral_bound
      rate rewards C_star C_h control0 (B ∩ I) hQ
  have hrewrite :
      (∫ z in B ∩ I,
        (∑ t : Fin p.T,
          if ReferenceOriginalInstallationStoppedReleasePhase.supportAt
              rate rewards C_star C_h ell.val t.val z then
            ReferenceOriginalInstallationReleaseSignedCharge.actualFixedReleaseSignedDeficit
              rate rewards C_star C_h ell.val t z else 0)
        ∂BootstrapPrivateRoundStreams.sourceInputLaw p) =
      ∫ z in B ∩ I,
        ReferenceFirstLiveStoppedReleaseCalendarSignedCost.totalSignedCost
          rate rewards C_star C_h z ∂BootstrapPrivateRoundStreams.sourceInputLaw p := by
    refine setIntegral_congr_fun hQambient ?_
    intro z hz
    exact hcost z hz
  rw [hrewrite]
  simpa [H, ρ, τ, FR, I] using hbound

end Bandits.Support.ReferenceOriginalInitialReleaseSignedCost

end
