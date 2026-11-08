/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceOriginalKthBirthMarkLocalization
public import Bandits.Support.ReferenceOriginalInitialReleaseSignedCost
public import Bandits.Support.ReferenceOriginalInstallationReleaseWaitingCost

import Mathlib.Probability.Process.Stopping
import Mathlib.Tactic

/-!
# Conditional signed cost of one original ranked stopped release

The actual original `k`th stopped release is localized to its finite actual
birth marks. Each mark is split into its actual initial and later-installation
branches before applying the corresponding fixed-label release-cost bound.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ContinuousLearningRows
open Bandits.Support.PhaseStartConditionalWaiting
open Bandits.Support.ReferenceSourcePrefixHistoryFiltration
open Function
open scoped BigOperators Classical

namespace Bandits.Support.ReferenceOriginalKthReleaseSignedCost

abbrev Parameters := ConstructorDimensions.Parameters
abbrev SourceInput (p : Parameters) := BootstrapPrivateRoundStreams.SourceInput p

variable {p : Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ)

/-- The manuscript's single signed release-cost bound. -/
public def B_rel : ℝ :=
  2 * ((p.m : ℝ) - 1) * (p.K : ℝ) +
    (12 * ((p.m : ℝ) - 1) * (p.K : ℝ) / (1 - Real.exp (-1))) *
      (Real.log ((p.m : ℝ) - 1) + 1)

private theorem natBound_eq_B_rel :
    2 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) +
        12 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) /
          (1 - Real.exp (-1)) *
            (Real.log ((p.m - 1 : ℕ) : ℝ) + 1) =
      B_rel (p := p) := by
  have hm : 1 ≤ p.m := (by decide : 1 ≤ 2).trans p.two_le_m
  rw [Nat.cast_sub hm]
  simp only [Nat.cast_one]
  dsimp [B_rel]

private theorem B_rel_nonneg : 0 ≤ B_rel (p := p) := by
  have hm : 1 ≤ (p.m : ℝ) - 1 := by
    have hmc : (2 : ℝ) ≤ (p.m : ℝ) := by exact_mod_cast p.two_le_m
    linarith
  have hK : 0 ≤ (p.K : ℝ) := by positivity
  have hden : 0 < 1 - Real.exp (-1) := by simp
  have hlog : 0 ≤ Real.log ((p.m : ℝ) - 1) := Real.log_nonneg hm
  dsimp [B_rel]
  positivity

private theorem fixedPrefix_full (ell : Fin p.T) (z : SourceInput p) :
    ReferenceOriginalKthBirthMarkLocalization.fixedSignedPrefix
        rate rewards C_star C_h ell p.T z =
      ∑ t : Fin p.T,
        if ReferenceOriginalInstallationStoppedReleasePhase.supportAt
            rate rewards C_star C_h ell.val t.val z then
          ReferenceOriginalInstallationReleaseSignedCharge.actualFixedReleaseSignedDeficit
            rate rewards C_star C_h ell.val t z else 0 := by
  unfold ReferenceOriginalKthBirthMarkLocalization.fixedSignedPrefix
  rw [Finset.filter_eq_self.mpr (by
    intro t ht
    exact t.isLt)]

private theorem laterBirth_preRound_measurable
    (control0 : TimeControl p) (ell : Fin p.T) :
    MeasurableSet[(sourcePrefixFiltration control0) (ell.val + 1)]
      {z : SourceInput p |
        ReferenceOriginalLaterReleasePredictableService.laterBirth
          rate rewards C_star C_h ell.val z} := by
  let L : Set (SourceInput p) := {z |
    ReferenceOriginalLaterReleasePredictableService.laterBirth
      rate rewards C_star C_h ell.val z}
  have hL : MeasurableSet L := by
    exact ReferenceOriginalLaterReleasePredictableService.laterBirth_measurable
      rate rewards C_star C_h ell.val
  have hset : L = (sourcePrefix control0 ell.val) ⁻¹' L := by
    ext z
    exact (ReferenceOriginalLaterReleasePredictableService.laterBirth_prefix_factor
      rate rewards C_star C_h control0 ell ell.val le_rfl z)
  change MeasurableSet[(sourcePrefixFiltration control0) (ell.val + 1)] L
  rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration_succ]
  change ∃ S, MeasurableSet S ∧ (sourcePrefix control0 ell.val) ⁻¹' S = L
  exact ⟨L, hL, hset.symm⟩

private theorem laterBirth_stopped_measurable
    (control0 : TimeControl p) (ell : Fin p.T) :
    MeasurableSet[PhaseStartConditionalWaiting.phaseStartSigmaAlgebra
      (sourcePrefixFiltration control0)
      (ReferenceOriginalInstallationStoppedReleasePhase.sigmaR rate rewards C_star C_h ell.val)
      (ReferenceOriginalInstallationStoppedReleasePhase.sigmaR_stopping
        rate rewards C_star C_h control0 ell.val)]
      {z : SourceInput p |
        ReferenceOriginalLaterReleasePredictableService.laterBirth
          rate rewards C_star C_h ell.val z} := by
  let F := sourcePrefixFiltration control0
  let sigma := ReferenceOriginalInstallationStoppedReleasePhase.sigmaR
    rate rewards C_star C_h ell.val
  let hσ := ReferenceOriginalInstallationStoppedReleasePhase.sigmaR_stopping
    rate rewards C_star C_h control0 ell.val
  let L : Set (SourceInput p) := {z |
    ReferenceOriginalLaterReleasePredictableService.laterBirth
      rate rewards C_star C_h ell.val z}
  have hLpre : MeasurableSet[F (ell.val + 1)] L :=
    laterBirth_preRound_measurable rate rewards C_star C_h control0 ell
  change MeasurableSet[PhaseStartConditionalWaiting.phaseStartSigmaAlgebra F sigma hσ] L
  refine ⟨le_iSup F (ell.val + 1) L hLpre, ?_⟩
  intro n
  change MeasurableSet[F n] (L ∩ {z | (sigma z : WithTop ℕ) ≤ (n : WithTop ℕ)})
  have hset : {z | (sigma z : WithTop ℕ) ≤ (n : WithTop ℕ)} = {z | sigma z ≤ n} := by
    ext z
    norm_cast
  rw [hset]
  by_cases hn : ell.val + 1 ≤ n
  · exact (F.mono hn _ hLpre).inter (hσ n)
  · have hempty : L ∩ {z | sigma z ≤ n} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro z ⟨_, hz⟩
      have horder := ReferenceOriginalKthBirthMarkLocalization.markedDate_le_releaseStart
        rate rewards C_star C_h ell z
      change sigma z ≤ n at hz
      change ell.val + 1 ≤ sigma z at horder
      omega
    rw [hempty]
    exact @MeasurableSet.empty (SourceInput p) (F n)

private theorem marked_initial_iff_not_later
    (k : Fin (p.T + 1)) (ell : Fin p.T) (z : SourceInput p)
    (hmark : z ∈ ReferenceOriginalKthBirthMarkLocalization.kthBirthMark
      rate rewards C_star C_h k ell) :
    ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferInitialMarkerAt
        rate rewards C_star C_h ell z ↔
      ¬ ReferenceOriginalLaterReleasePredictableService.laterBirth
        rate rewards C_star C_h ell.val z := by
  constructor
  · intro hinitial
    obtain ⟨record, hrecord, hfirst⟩ :=
      (ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferInitialMarkerAt_iff_record_first
        rate rewards C_star C_h ell z).mp hinitial
    exact ReferenceOriginalLaterReleasePredictableService.not_laterBirth_of_actual_first
      rate rewards C_star C_h ell z record hrecord hfirst
  · intro hnotLater
    obtain ⟨b, M, hdate, _hbirth, hbranch⟩ :=
      ReferenceOriginalKthBirthMarkLocalization.mark_actual_installation
        rate rewards C_star C_h k ell z hmark
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let a := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    have hell : ell.val =
        ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + b.val := by
      omega
    rcases hbranch with hfirst | hlater
    · have hrecord : ReferenceSourcePrefixHistoryFiltration.actualRecord
          rate rewards C_star C_h ell z = some R[b.val] := by
        unfold ReferenceSourcePrefixHistoryFiltration.actualRecord
        rw [hell, ite_eq_left (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
        exact List.getElem?_eq_getElem b.isLt
      exact (ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferInitialMarkerAt_iff_record_first
        rate rewards C_star C_h ell z).mpr ⟨R[b.val], hrecord, hfirst.2.1⟩
    · have hlaterBirth :=
        ReferenceOriginalLaterReleasePredictableService.laterBirth_of_actualSuffixIndex
          rate rewards C_star C_h z b hlater.1
      have hlaterAtMark :
          ReferenceOriginalLaterReleasePredictableService.laterBirth
            rate rewards C_star C_h ell.val z := by
        simpa only [hell] using hlaterBirth
      exact (hnotLater hlaterAtMark).elim

private theorem markedCharge_setIntegral_bound
    (control0 : TimeControl p) (k : Fin (p.T + 1)) (ell : Fin p.T)
    (B0 : Set (SourceInput p))
    (hB0 : MeasurableSet[PhaseStartConditionalWaiting.phaseStartSigmaAlgebra
      (sourcePrefixFiltration control0)
      (ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
        rate rewards C_star C_h k)
      (ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate_isPreRoundStoppingTime
        rate rewards C_star C_h control0 k)] B0) :
    ∫ z in B0 ∩ ReferenceOriginalKthBirthMarkLocalization.kthBirthMark
        rate rewards C_star C_h k ell,
      ReferenceOriginalKthBirthMarkLocalization.fixedSignedPrefix
        rate rewards C_star C_h ell p.T z ∂sourceInputLaw p ≤
      B_rel (p := p) * (sourceInputLaw p).real
        (B0 ∩ ReferenceOriginalKthBirthMarkLocalization.kthBirthMark
          rate rewards C_star C_h k ell) := by
  let F := sourcePrefixFiltration control0
  let sigma := ReferenceOriginalInstallationStoppedReleasePhase.sigmaR
    rate rewards C_star C_h ell.val
  let hσ := ReferenceOriginalInstallationStoppedReleasePhase.sigmaR_stopping
    rate rewards C_star C_h control0 ell.val
  let E := ReferenceOriginalKthBirthMarkLocalization.kthBirthMark
    rate rewards C_star C_h k ell
  let C := B0 ∩ E
  let L : Set (SourceInput p) := {z |
    ReferenceOriginalLaterReleasePredictableService.laterBirth
      rate rewards C_star C_h ell.val z}
  let I : Set (SourceInput p) := {z |
    ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferInitialMarkerAt
      rate rewards C_star C_h ell z}
  let μ := sourceInputLaw p
  let f := ReferenceOriginalKthBirthMarkLocalization.fixedSignedPrefix
    rate rewards C_star C_h ell p.T
  have hC : MeasurableSet[PhaseStartConditionalWaiting.phaseStartSigmaAlgebra F sigma hσ] C := by
    exact ReferenceOriginalKthBirthMarkLocalization.marked_event_at_release_start
      rate rewards C_star C_h control0 k ell B0 hB0
  have hLσ : MeasurableSet[PhaseStartConditionalWaiting.phaseStartSigmaAlgebra F sigma hσ] L :=
    laterBirth_stopped_measurable rate rewards C_star C_h control0 ell
  have hLamb : MeasurableSet L := by
    exact (PhaseStartConditionalWaiting.phaseStartSigmaAlgebra_le F sigma hσ) L hLσ
  have hA : MeasurableSet[PhaseStartConditionalWaiting.phaseStartSigmaAlgebra F sigma hσ]
      (C ∩ L) := hC.inter hLσ
  have hAamb : MeasurableSet (C ∩ L) := by
    exact (PhaseStartConditionalWaiting.phaseStartSigmaAlgebra_le F sigma hσ) (C ∩ L) hA
  have hprefixInt := ReferenceOriginalKthBirthMarkLocalization.fixedPrefix_integrable
    rate rewards C_star C_h ell p.T
  have hpartition : C \ L = C ∩ I := by
    ext z
    simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_ofPred_eq, C, E, L, I]
    constructor
    · rintro ⟨⟨hzB, hmark⟩, hnotLater⟩
      exact ⟨⟨hzB, hmark⟩,
        (marked_initial_iff_not_later rate rewards C_star C_h k ell z hmark).mpr hnotLater⟩
    · rintro ⟨⟨hzB, hmark⟩, hinitial⟩
      exact ⟨⟨hzB, hmark⟩,
        (marked_initial_iff_not_later rate rewards C_star C_h k ell z hmark).mp hinitial⟩
  have hprefix_later (z : SourceInput p) (hz : z ∈ L) :
      f z = ReferenceOriginalInstallationReleaseWaitingCost.laterSignedCharge
        rate rewards C_star C_h ell.val z := by
    obtain ⟨hs, b, hdate, hlater, _hrecord⟩ :=
      ReferenceOriginalLaterReleasePredictableService.laterBirth_actualSuffixIndex
        rate rewards C_star C_h ell.val z hz
    have hspecial :=
      ReferenceOriginalInstallationReleaseWaitingCost.laterSignedCharge_actualLater_specialization
        rate rewards C_star C_h z b hlater
    have hcharge :
        ReferenceOriginalInstallationReleaseWaitingCost.laterSignedCharge
            rate rewards C_star C_h ell.val z =
          ∑ t : Fin p.T,
            if ReferenceOriginalInstallationStoppedReleasePhase.supportAt
                rate rewards C_star C_h ell.val t.val z then
              ReferenceOriginalInstallationReleaseSignedCharge.actualFixedReleaseSignedDeficit
                rate rewards C_star C_h ell.val t z else 0 := by
      have hcharge' := hspecial.2.2
      change ReferenceOriginalInstallationReleaseWaitingCost.laterSignedCharge
          rate rewards C_star C_h
            (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + b.val) z = _
        at hcharge'
      rw [← hdate] at hcharge'
      exact hcharge'
    change ReferenceOriginalKthBirthMarkLocalization.fixedSignedPrefix
      rate rewards C_star C_h ell p.T z =
        ReferenceOriginalInstallationReleaseWaitingCost.laterSignedCharge
          rate rewards C_star C_h ell.val z
    exact (fixedPrefix_full rate rewards C_star C_h ell z).trans hcharge.symm
  have hinitial_bound :=
    ReferenceOriginalInitialReleaseSignedCost.initial_fixed_label_release_setIntegral_bound
      rate rewards C_star C_h control0 ell C hC
  have hlater_bound :=
    ReferenceOriginalInstallationReleaseWaitingCost.laterSignedCharge_setIntegral_bound
      rate rewards C_star C_h control0 ell.val (C ∩ L) hA
  rw [natBound_eq_B_rel (p := p)] at hlater_bound
  have hfirstPart :
      ∫ z in C ∩ L, f z ∂μ ≤ B_rel (p := p) * μ.real (C ∩ L) := by
    calc
      ∫ z in C ∩ L, f z ∂μ =
          ∫ z in C ∩ L,
            ReferenceOriginalInstallationReleaseWaitingCost.laterSignedCharge
              rate rewards C_star C_h ell.val z ∂μ := by
        apply setIntegral_congr_fun hAamb
        intro z hz
        exact hprefix_later z hz.2
      _ ≤ B_rel (p := p) * μ.real (C ∩ L) := hlater_bound
  have hsecondPart :
      ∫ z in C \ L, f z ∂μ ≤ B_rel (p := p) * μ.real (C \ L) := by
    calc
      ∫ z in C \ L, f z ∂μ = ∫ z in C ∩ I, f z ∂μ := by rw [hpartition]
      _ = ∫ z in C ∩ I,
          ∑ t : Fin p.T,
            if ReferenceOriginalInstallationStoppedReleasePhase.supportAt
                rate rewards C_star C_h ell.val t.val z then
              ReferenceOriginalInstallationReleaseSignedCharge.actualFixedReleaseSignedDeficit
                rate rewards C_star C_h ell t z else 0 ∂μ := by
        congr 1
        funext z
        exact fixedPrefix_full rate rewards C_star C_h ell z
      _ ≤ _ := by
        simpa only [B_rel, μ, C, I] using hinitial_bound
      _ = B_rel (p := p) * μ.real (C \ L) := by
        rw [hpartition]
        rfl
  have hdecomp := integral_inter_add_sdiff (s := C) (t := L) (f := f)
    hLamb hprefixInt.integrableOn
  calc
    ∫ z in C, f z ∂μ =
        ∫ z in C ∩ L, f z ∂μ + ∫ z in C \ L, f z ∂μ := hdecomp.symm
    _ ≤ B_rel (p := p) * μ.real (C ∩ L) +
        B_rel (p := p) * μ.real (C \ L) := add_le_add hfirstPart hsecondPart
    _ = B_rel (p := p) * μ.real C := by
      rw [← mul_add, measureReal_inter_add_sdiff hLamb]

/-- Integrability of the actual original ranked signed release charge. -/
public theorem kthReleaseSignedCharge_integrable (k : Fin (p.T + 1)) :
    Integrable
      (fun z : SourceInput p =>
        ReferenceOriginalKthReleaseSignedChargeLocalization.kthReleaseSignedCharge
          rate rewards C_star C_h z k)
      (BootstrapPrivateRoundStreams.sourceInputLaw p) :=
  ReferenceOriginalKthBirthMarkLocalization.kthCharge_integrable
    rate rewards C_star C_h k

/-- The actual kth signed release charge is bounded on every event in its
existing ranked stopped-start field. -/
public theorem kthReleaseSignedCharge_setIntegral_bound
    (control0 : TimeControl p) (k : Fin (p.T + 1)) (B0 : Set (SourceInput p))
    (hB0 : MeasurableSet[PhaseStartConditionalWaiting.phaseStartSigmaAlgebra
      (sourcePrefixFiltration control0)
      (ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
        rate rewards C_star C_h k)
      (ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate_isPreRoundStoppingTime
        rate rewards C_star C_h control0 k)] B0) :
    ∫ z in B0,
      ReferenceOriginalKthReleaseSignedChargeLocalization.kthReleaseSignedCharge
        rate rewards C_star C_h z k ∂BootstrapPrivateRoundStreams.sourceInputLaw p ≤
      B_rel (p := p) * (BootstrapPrivateRoundStreams.sourceInputLaw p).real B0 := by
  let μ := sourceInputLaw p
  let F := sourcePrefixFiltration control0
  let sigma := ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
    rate rewards C_star C_h k
  let hσ := ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate_isPreRoundStoppingTime
    rate rewards C_star C_h control0 k
  let E : Fin p.T → Set (SourceInput p) := fun ell =>
    ReferenceOriginalKthBirthMarkLocalization.kthBirthMark rate rewards C_star C_h k ell
  let f : Fin p.T → SourceInput p → ℝ := fun ell z =>
    if z ∈ E ell then
      ReferenceOriginalKthBirthMarkLocalization.fixedSignedPrefix
        rate rewards C_star C_h ell p.T z
    else 0
  let m0 : MeasurableSpace (SourceInput p) := Prod.instMeasurableSpace
  have hmσ : PhaseStartConditionalWaiting.phaseStartSigmaAlgebra F sigma hσ ≤ m0 :=
    PhaseStartConditionalWaiting.phaseStartSigmaAlgebra_le F sigma hσ
  have hBambient : MeasurableSet[m0] B0 := hmσ B0 hB0
  have hEambient (ell : Fin p.T) : MeasurableSet[m0] (E ell) := by
    exact (F.le (ell.val + 1) (E ell))
      (ReferenceOriginalKthBirthMarkLocalization.mark_preRound_measurable
        rate rewards C_star C_h control0 k ell)
  have htermInt (ell : Fin p.T) : Integrable (f ell) μ := by
    simpa only [f, E] using
      (ReferenceOriginalKthBirthMarkLocalization.markedPrefix_integrable
        rate rewards C_star C_h k ell p.T)
  have hsumIdentity (z : SourceInput p) :
      ReferenceOriginalKthReleaseSignedChargeLocalization.kthReleaseSignedCharge
          rate rewards C_star C_h z k =
        ∑ ell : Fin p.T, f ell z := by
    have hfilter :
        (ReferenceOriginalKthReleaseGateAlignment.kthReleaseDates
          rate rewards C_star C_h z k).filter (fun t => t.val < p.T) =
          ReferenceOriginalKthReleaseGateAlignment.kthReleaseDates
            rate rewards C_star C_h z k :=
      Finset.filter_eq_self.mpr (fun t _ht => t.isLt)
    unfold ReferenceOriginalKthReleaseSignedChargeLocalization.kthReleaseSignedCharge
    rw [← hfilter]
    simpa only [f, E, Set.indicator_apply] using
      (ReferenceOriginalKthBirthMarkLocalization.signed_prefix_mark_reindex
        rate rewards C_star C_h k p.T z)
  have hdisjoint : Pairwise (Disjoint on fun ell : Fin p.T => B0 ∩ E ell) := by
    intro ell ell' hne
    apply Set.disjoint_left.mpr
    intro z hz hz'
    exact (Set.disjoint_left.mp
      (ReferenceOriginalKthBirthMarkLocalization.marks_disjoint
        rate rewards C_star C_h k ell ell' hne)) hz.2 hz'.2
  have hCmeas (ell : Fin p.T) : MeasurableSet[m0] (B0 ∩ E ell) :=
    hBambient.inter (hEambient ell)
  have hMass : (∑ ell : Fin p.T, μ.real (B0 ∩ E ell)) ≤ μ.real B0 := by
    have hUnion : (∑ ell : Fin p.T, μ.real (B0 ∩ E ell)) =
        μ.real (⋃ ell : Fin p.T, B0 ∩ E ell) := by
      symm
      exact measureReal_iUnion_fintype (μ := μ) hdisjoint hCmeas (fun _ => by finiteness)
    rw [hUnion]
    apply measureReal_mono
    · exact Set.iUnion_subset fun ell z hz => hz.1
    · finiteness
  have hsetIntegrable (ell : Fin p.T) : Integrable (f ell) (μ.restrict B0) :=
    (htermInt ell).mono_measure (Measure.restrict_le_self)
  calc
    ∫ z in B0,
        ReferenceOriginalKthReleaseSignedChargeLocalization.kthReleaseSignedCharge
          rate rewards C_star C_h z k ∂μ =
      ∫ z in B0, ∑ ell : Fin p.T, f ell z ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun z => hsumIdentity z
    _ = ∑ ell : Fin p.T, ∫ z in B0, f ell z ∂μ := by
      exact integral_finsetSum Finset.univ (fun ell _ => hsetIntegrable ell)
    _ = ∑ ell : Fin p.T, ∫ z in B0 ∩ E ell,
        ReferenceOriginalKthBirthMarkLocalization.fixedSignedPrefix
          rate rewards C_star C_h ell p.T z ∂μ := by
      apply Finset.sum_congr rfl
      intro ell hell
      rw [show (fun z : SourceInput p => f ell z) =
        (E ell).indicator (ReferenceOriginalKthBirthMarkLocalization.fixedSignedPrefix
          rate rewards C_star C_h ell p.T) from by
          funext z
          by_cases hz : z ∈ E ell <;> simp [f, hz]]
      rw [setIntegral_indicator (hEambient ell)]
    _ ≤ ∑ ell : Fin p.T,
        B_rel (p := p) * μ.real (B0 ∩ E ell) := by
      apply Finset.sum_le_sum
      intro ell hell
      simpa only [E, μ] using
        (markedCharge_setIntegral_bound rate rewards C_star C_h control0 k ell B0 hB0)
    _ = B_rel (p := p) * ∑ ell : Fin p.T, μ.real (B0 ∩ E ell) := by
      rw [Finset.mul_sum]
    _ ≤ B_rel (p := p) * μ.real B0 :=
      mul_le_mul_of_nonneg_left hMass (B_rel_nonneg (p := p))

/-- The same actual ranked stopped-start field bounds the conditional
expectation of the original kth signed release charge. -/
public theorem kthReleaseSignedCharge_condExp_bound
    (control0 : TimeControl p) (k : Fin (p.T + 1)) :
    (BootstrapPrivateRoundStreams.sourceInputLaw p)[
      (fun z => ReferenceOriginalKthReleaseSignedChargeLocalization.kthReleaseSignedCharge
        rate rewards C_star C_h z k) |
      PhaseStartConditionalWaiting.phaseStartSigmaAlgebra
        (sourcePrefixFiltration control0)
        (ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
          rate rewards C_star C_h k)
        (ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate_isPreRoundStoppingTime
          rate rewards C_star C_h control0 k)] ≤ᵐ[BootstrapPrivateRoundStreams.sourceInputLaw p]
      fun _ => B_rel (p := p) := by
  let μ := sourceInputLaw p
  let F := sourcePrefixFiltration control0
  let sigma := ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
    rate rewards C_star C_h k
  let hσ := ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate_isPreRoundStoppingTime
    rate rewards C_star C_h control0 k
  let m0 : MeasurableSpace (SourceInput p) := Prod.instMeasurableSpace
  have hmσ : PhaseStartConditionalWaiting.phaseStartSigmaAlgebra F sigma hσ ≤ m0 :=
    PhaseStartConditionalWaiting.phaseStartSigmaAlgebra_le F sigma hσ
  have hint := kthReleaseSignedCharge_integrable rate rewards C_star C_h k
  have hset : ∀ B, MeasurableSet[PhaseStartConditionalWaiting.phaseStartSigmaAlgebra F sigma hσ] B →
      ∫ z in B,
        ReferenceOriginalKthReleaseSignedChargeLocalization.kthReleaseSignedCharge
          rate rewards C_star C_h z k ∂μ ≤ B_rel (p := p) * μ.real B := by
    intro B hB
    exact kthReleaseSignedCharge_setIntegral_bound
      rate rewards C_star C_h control0 k B hB
  exact (PhaseStartConditionalWaiting.setIntegral_iff_condExp_le
    (m := m0) μ
    (PhaseStartConditionalWaiting.phaseStartSigmaAlgebra F sigma hσ) hmσ
    (ReferenceOriginalKthReleaseSignedChargeLocalization.kthReleaseSignedCharge
      rate rewards C_star C_h · k) (B_rel (p := p)) hint).mp hset

end Bandits.Support.ReferenceOriginalKthReleaseSignedCost

end
