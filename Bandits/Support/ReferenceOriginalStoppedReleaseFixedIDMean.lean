/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceOriginalKthReleaseSignedCost

import Mathlib.Tactic

/-!
# Original stopped release signed mean under every fixed ID

The release observable is the signed sum on the existing original stopped
calendar. Its ranked decomposition retains the original source input, including
the inclusive first bad update. Each rank is bounded on its active event in
the same stopped source field, then transported through the positive atom of
the original shared ID array.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ContinuousLearningRows
open Bandits.Support.ReferenceOriginalKthReleaseSignedCost
open scoped BigOperators Classical

namespace Bandits.Support.ReferenceOriginalStoppedReleaseFixedIDMean

abbrev Parameters := ConstructorDimensions.Parameters
abbrev SourceInput (p : Parameters) := BootstrapPrivateRoundStreams.SourceInput p

variable {p : Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ)

/-- The literal signed release charge on the actual original stopped release
dates. The date observable keeps its signed deficits. -/
public def stoppedReleaseSignedCharge (z : SourceInput p) : ℝ :=
  ∑ t ∈ ReferenceOriginalCalendarTransferPhaseCover.releasePhaseDates
      rate rewards C_star C_h z,
    ReferenceOriginalCalendarTransferPhaseCover.actualDateSignedDelta
      rate rewards C_star C_h z t

private theorem releasePhaseDates_subset_retained (z : SourceInput p)
    (t : Fin p.T)
    (ht : t ∈ ReferenceOriginalCalendarTransferPhaseCover.releasePhaseDates
      rate rewards C_star C_h z) :
    t ∈ ReferenceOriginalCalendarTransferPhaseCover.retainedSuffixDates
      rate rewards C_star C_h z := by
  rw [← ReferenceOriginalCalendarTransferPhaseCover.stopped_phase_dates_cover
    rate rewards C_star C_h z]
  exact Finset.mem_union.mpr (Or.inr ht)

/-- The original release dates partition into the literal ranked stopped
windows intersected with those same release dates. -/
private theorem ranked_release_dates_biUnion_eq_release_dates
    (z : SourceInput p) :
    (Finset.univ : Finset (Fin (p.T + 1))).biUnion
        (ReferenceOriginalKthReleaseGateAlignment.kthReleaseDates
          rate rewards C_star C_h z) =
      ReferenceOriginalCalendarTransferPhaseCover.releasePhaseDates
        rate rewards C_star C_h z := by
  classical
  apply Finset.ext
  intro t
  constructor
  · intro ht
    obtain ⟨k, _hk, hkt⟩ := Finset.mem_biUnion.mp ht
    exact (Finset.mem_inter.mp hkt).2
  · intro ht
    have hret := releasePhaseDates_subset_retained rate rewards C_star C_h z t ht
    have hwindowUnion :=
      ReferenceOriginalStoppedTransferSignedReindex.ranked_windows_biUnion_eq_retained_suffix
        rate rewards C_star C_h z
    have hwindow : t ∈
        (Finset.univ : Finset (Fin (p.T + 1))).biUnion
          (ReferenceOriginalStoppedTransferSignedReindex.kthStoppedTransferWindowDates
            rate rewards C_star C_h z) := by
      rw [hwindowUnion]
      exact hret
    obtain ⟨k, hk, hkt⟩ := Finset.mem_biUnion.mp hwindow
    refine Finset.mem_biUnion.mpr ⟨k, hk, ?_⟩
    exact Finset.mem_inter.mpr ⟨hkt, ht⟩

/-- Pointwise reindexing of the literal stopped signed release observable into
the accepted original kth-release charges. -/
public theorem stoppedReleaseSignedCharge_eq_sum_kthReleaseSignedCharge
    (z : SourceInput p) :
    stoppedReleaseSignedCharge rate rewards C_star C_h z =
      ∑ k : Fin (p.T + 1),
        ReferenceOriginalKthReleaseSignedChargeLocalization.kthReleaseSignedCharge
          rate rewards C_star C_h z k := by
  classical
  have hdisjoint : Set.PairwiseDisjoint
      (↑(Finset.univ : Finset (Fin (p.T + 1))))
      (ReferenceOriginalKthReleaseGateAlignment.kthReleaseDates
        rate rewards C_star C_h z) := by
    intro k hk l hl hne
    apply Finset.disjoint_left.mpr
    intro t htk htl
    exact (Finset.disjoint_left.mp
      (ReferenceOriginalStoppedTransferSignedReindex.kthStoppedTransferWindowDates_disjoint
        rate rewards C_star C_h z k l hne))
        (Finset.mem_inter.mp htk).1 (Finset.mem_inter.mp htl).1
  unfold stoppedReleaseSignedCharge
    ReferenceOriginalKthReleaseSignedChargeLocalization.kthReleaseSignedCharge
  rw [← Finset.sum_biUnion hdisjoint,
    ranked_release_dates_biUnion_eq_release_dates rate rewards C_star C_h z]

private theorem integrable_fixedID_of_integrable
    (ids : CompletePublicTable.IDArray p) {f : SourceInput p → ℝ}
    (hf : Integrable f (BootstrapPrivateRoundStreams.sourceInputLaw p)) :
    Integrable f (ReferenceFixedIDSourceSection.fixedIDSourceLaw ids) := by
  have hRestricted : Integrable f
      ((BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
        (ReferenceFixedIDSourceSection.fixedIDSourceSection ids)) := hf.integrableOn
  rw [ReferenceFixedIDSourceSection.sourceInputLaw_restrict_fixedIDSourceSection
    (p := p) ids] at hRestricted
  have hAtom : CompletePublicTable.idArrayMeasure p {ids} ≠ 0 := by
    exact (MeasureTheory.measureReal_ne_zero_iff
      (h := (ReferenceFixedIDSourceSection.idArrayAtom_lt_top (p := p) ids).ne)).mp
        (ne_of_gt (ReferenceFixedIDSourceSection.idArrayAtom_positive (p := p) ids))
  exact (integrable_smul_measure hAtom
    (ReferenceFixedIDSourceSection.idArrayAtom_lt_top (p := p) ids).ne).mp hRestricted

private theorem fixedIDSourceSection_mem_sourcePrefix
    (control0 : TimeControl p) (ids : CompletePublicTable.IDArray p) (n : ℕ) :
    MeasurableSet[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
      control0 n]
      (ReferenceFixedIDSourceSection.fixedIDSourceSection ids) := by
  classical
  cases n with
  | zero =>
      rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration_zero_eq_one]
      rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration_succ]
      refine ⟨ReferenceFixedIDSourceSection.fixedIDSourceSection ids,
        ReferenceFixedIDSourceSection.measurable_fixedIDSourceSection ids, ?_⟩
      ext z
      change (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 0 z).1.1 = ids ↔
        z.1.1 = ids
      rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefix_ids]
  | succ n =>
      rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration_succ]
      refine ⟨ReferenceFixedIDSourceSection.fixedIDSourceSection ids,
        ReferenceFixedIDSourceSection.measurable_fixedIDSourceSection ids, ?_⟩
      ext z
      change (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 (n + 1) z).1.1 = ids ↔
        z.1.1 = ids
      rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefix_ids]

private theorem rankedStartField_sections_measurable
    (control0 : TimeControl p) (ids : CompletePublicTable.IDArray p)
    (k : Fin (p.T + 1)) :
    MeasurableSet[PhaseStartConditionalWaiting.phaseStartSigmaAlgebra
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0)
        (ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
          rate rewards C_star C_h k)
        (ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate_isPreRoundStoppingTime
          rate rewards C_star C_h control0 k)]
        (ReferenceFixedIDSourceSection.fixedIDSourceSection ids) ∧
      MeasurableSet[PhaseStartConditionalWaiting.phaseStartSigmaAlgebra
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0)
        (ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
          rate rewards C_star C_h k)
        (ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate_isPreRoundStoppingTime
          rate rewards C_star C_h control0 k)]
        {z : SourceInput p |
          ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
            rate rewards C_star C_h k z ≤ p.T} := by
  let F := ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0
  let sigma := ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
    rate rewards C_star C_h k
  let hsigma :=
    ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate_isPreRoundStoppingTime
      rate rewards C_star C_h control0 k
  let hstop := PhaseStartConditionalWaiting.isStoppingTime_of_preRound F sigma hsigma
  let D := ReferenceFixedIDSourceSection.fixedIDSourceSection ids
  let E : Set (SourceInput p) := {z | sigma z ≤ p.T}
  have hDstop : MeasurableSet[PhaseStartConditionalWaiting.phaseStartSigmaAlgebra
      F sigma hsigma] D := by
    change MeasurableSet[hstop.measurableSpace] D
    rw [hstop.measurableSet]
    refine ⟨?_, fun n => ?_⟩
    · exact (le_iSup F 0) D
        (fixedIDSourceSection_mem_sourcePrefix control0 ids 0)
    · exact (fixedIDSourceSection_mem_sourcePrefix control0 ids n).inter
        (hstop.measurableSet_le n)
  have hEstop : MeasurableSet[PhaseStartConditionalWaiting.phaseStartSigmaAlgebra
      F sigma hsigma] E := by
    change MeasurableSet[hstop.measurableSpace] E
    rw [hstop.measurableSet]
    have hET : MeasurableSet[F p.T] E := by
      change MeasurableSet[F p.T] {z | sigma z ≤ p.T}
      exact hsigma p.T
    refine ⟨(le_iSup F p.T) E hET, fun n => ?_⟩
    by_cases hn : n ≤ p.T
    · have hEq : E ∩ {z | (sigma z : WithTop ℕ) ≤ (n : WithTop ℕ)} =
          {z | (sigma z : WithTop ℕ) ≤ (n : WithTop ℕ)} := by
        ext z
        simp only [E, Set.mem_ofPred_eq, Set.mem_inter_iff]
        constructor
        · rintro ⟨_, hσ⟩
          exact hσ
        · intro hσ
          refine ⟨?_, hσ⟩
          have hnat : sigma z ≤ n := by exact_mod_cast hσ
          exact hnat.trans hn
      change MeasurableSet[F n]
        (E ∩ {z | (sigma z : WithTop ℕ) ≤ (n : WithTop ℕ)})
      rw [hEq]
      exact hstop.measurableSet_le n
    · have htn : p.T < n := by omega
      have hTn : p.T ≤ n := Nat.le_of_lt htn
      exact (F.mono hTn E hET).inter (hstop.measurableSet_le n)
  exact ⟨hDstop, hEstop⟩

private theorem kthReleaseSignedCharge_zero_of_absent
    (k : Fin (p.T + 1)) (z : SourceInput p)
    (habsent : ¬ ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
      rate rewards C_star C_h k z ≤ p.T) :
    ReferenceOriginalKthReleaseSignedChargeLocalization.kthReleaseSignedCharge
      rate rewards C_star C_h z k = 0 := by
  unfold ReferenceOriginalKthReleaseSignedChargeLocalization.kthReleaseSignedCharge
  rw [ReferenceOriginalKthReleaseGateAlignment.kthReleaseDates_eq_empty_of_absent_rank
    rate rewards C_star C_h z k habsent]
  simp

/-- Integrability of the actual stopped signed release charge under the
original full source law. -/
public theorem stoppedReleaseSignedCharge_integrable_source :
    Integrable (stoppedReleaseSignedCharge rate rewards C_star C_h)
      (BootstrapPrivateRoundStreams.sourceInputLaw p) := by
  have hfun : (stoppedReleaseSignedCharge rate rewards C_star C_h) =
      fun z => ∑ k : Fin (p.T + 1),
        ReferenceOriginalKthReleaseSignedChargeLocalization.kthReleaseSignedCharge
          rate rewards C_star C_h z k := by
    funext z
    exact stoppedReleaseSignedCharge_eq_sum_kthReleaseSignedCharge
      rate rewards C_star C_h z
  rw [hfun]
  exact integrable_finsetSum Finset.univ (fun k _ =>
    ReferenceOriginalKthReleaseSignedCost.kthReleaseSignedCharge_integrable
      rate rewards C_star C_h k)

/-- Integrability of the same actual stopped signed release charge under
every literal fixed-ID section of the original source law. -/
public theorem stoppedReleaseSignedCharge_integrable_fixedID
    (ids : CompletePublicTable.IDArray p) :
    Integrable (stoppedReleaseSignedCharge rate rewards C_star C_h)
      (ReferenceFixedIDSourceSection.fixedIDSourceLaw ids) := by
  have hfun : (stoppedReleaseSignedCharge rate rewards C_star C_h) =
      fun z => ∑ k : Fin (p.T + 1),
        ReferenceOriginalKthReleaseSignedChargeLocalization.kthReleaseSignedCharge
          rate rewards C_star C_h z k := by
    funext z
    exact stoppedReleaseSignedCharge_eq_sum_kthReleaseSignedCharge
      rate rewards C_star C_h z
  rw [hfun]
  exact integrable_finsetSum Finset.univ (fun k _ =>
    integrable_fixedID_of_integrable ids
      (ReferenceOriginalKthReleaseSignedCost.kthReleaseSignedCharge_integrable
        rate rewards C_star C_h k))

/-- For each original rank, the signed charge mean under a fixed-ID law is
bounded by the mass of that rank's actual active event. -/
public theorem kthReleaseSignedCharge_fixedID_mean_le_activeMass
    (control0 : TimeControl p) (ids : CompletePublicTable.IDArray p)
    (k : Fin (p.T + 1)) :
    ∫ z : SourceInput p,
      ReferenceOriginalKthReleaseSignedChargeLocalization.kthReleaseSignedCharge
        rate rewards C_star C_h z k
      ∂ReferenceFixedIDSourceSection.fixedIDSourceLaw ids ≤
      B_rel (p := p) *
        (ReferenceFixedIDSourceSection.fixedIDSourceLaw ids).real
          {z : SourceInput p |
            ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
              rate rewards C_star C_h k z ≤ p.T} := by
  let F := ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0
  let sigma := ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
    rate rewards C_star C_h k
  let hsigma :=
    ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate_isPreRoundStoppingTime
      rate rewards C_star C_h control0 k
  let E : Set (SourceInput p) := {z | sigma z ≤ p.T}
  let D := ReferenceFixedIDSourceSection.fixedIDSourceSection ids
  let μ := BootstrapPrivateRoundStreams.sourceInputLaw p
  let ν := ReferenceFixedIDSourceSection.fixedIDSourceLaw ids
  let f : SourceInput p → ℝ := fun z =>
    ReferenceOriginalKthReleaseSignedChargeLocalization.kthReleaseSignedCharge
      rate rewards C_star C_h z k
  have hsections := rankedStartField_sections_measurable
    rate rewards C_star C_h control0 ids k
  have hDstop := hsections.1
  have hEstop := hsections.2
  have hμE : MeasurableSet E :=
    (PhaseStartConditionalWaiting.phaseStartSigmaAlgebra_le F sigma hsigma) E hEstop
  have hB0 : MeasurableSet[PhaseStartConditionalWaiting.phaseStartSigmaAlgebra
      F sigma hsigma] (D ∩ E) := hDstop.inter hEstop
  have hsource := ReferenceOriginalKthReleaseSignedCost.kthReleaseSignedCharge_setIntegral_bound
    rate rewards C_star C_h control0 k (D ∩ E) hB0
  have hsectionIntegral :
      (∫ z in D ∩ E, f z ∂μ) =
        (CompletePublicTable.idArrayMeasure p).real {ids} *
          ∫ z in E, f z ∂ν := by
    calc
      (∫ z in D ∩ E, f z ∂μ) = ∫ z in D, E.indicator f z ∂μ := by
        symm
        exact setIntegral_indicator hμE
      _ = (CompletePublicTable.idArrayMeasure p).real {ids} *
          ∫ z, E.indicator f z ∂ν := by
        exact ReferenceFixedIDSourceSection.sourceInputLaw_setIntegral_fixedIDSourceSection
          (p := p) ids (E.indicator f)
      _ = (CompletePublicTable.idArrayMeasure p).real {ids} *
          ∫ z in E, f z ∂ν := by
        congr 1
        rw [← setIntegral_univ, setIntegral_indicator hμE]
        simp
  have hsectionMass : μ.real (D ∩ E) =
      (CompletePublicTable.idArrayMeasure p).real {ids} * ν.real E :=
    ReferenceFixedIDSourceSection.sourceInputLaw_real_inter_fixedIDSourceSection
      (p := p) ids E hμE
  have hAtomPos : 0 < (CompletePublicTable.idArrayMeasure p).real {ids} :=
    ReferenceFixedIDSourceSection.idArrayAtom_positive (p := p) ids
  have hscaled :
      ((CompletePublicTable.idArrayMeasure p).real {ids}) *
          (∫ z in E, f z ∂ν) ≤
        ((CompletePublicTable.idArrayMeasure p).real {ids}) *
          (B_rel (p := p) * ν.real E) := by
    calc
      _ = ∫ z in D ∩ E, f z ∂μ := hsectionIntegral.symm
      _ ≤ B_rel (p := p) * μ.real (D ∩ E) := hsource
      _ = B_rel (p := p) *
          ((CompletePublicTable.idArrayMeasure p).real {ids} * ν.real E) := by
        rw [hsectionMass]
      _ = _ := by ring
  have hcancel :
      (∫ z in E, f z ∂ν) * (CompletePublicTable.idArrayMeasure p).real {ids} ≤
        (B_rel (p := p) * ν.real E) *
          (CompletePublicTable.idArrayMeasure p).real {ids} := by
    calc
      _ = (CompletePublicTable.idArrayMeasure p).real {ids} *
          (∫ z in E, f z ∂ν) := by ring
      _ ≤ (CompletePublicTable.idArrayMeasure p).real {ids} *
          (B_rel (p := p) * ν.real E) := hscaled
      _ = _ := by ring
  have hactive := (mul_le_mul_iff_left₀ hAtomPos).mp hcancel
  have hzeroInactive : ∀ z ∉ E,
      f z = 0 := by
    intro z hz
    apply kthReleaseSignedCharge_zero_of_absent rate rewards C_star C_h k z
    simpa only [E, Set.mem_ofPred_eq] using hz
  have hwhole :
      (∫ z : SourceInput p, f z ∂ν) = ∫ z in E, f z ∂ν := by
    calc
      (∫ z : SourceInput p, f z ∂ν) =
          ∫ z, E.indicator f z ∂ν := by
        apply integral_congr_ae
        filter_upwards with z
        by_cases hz : z ∈ E
        · simp [hz]
        · simp [hz, hzeroInactive z hz]
      _ = ∫ z in E, f z ∂ν := by
        exact integral_indicator hμE
  rw [hwhole]
  exact hactive

private theorem B_rel_nonneg : 0 ≤ B_rel (p := p) := by
  have hm : 1 ≤ (p.m : ℝ) - 1 := by
    have hmc : (2 : ℝ) ≤ (p.m : ℝ) := by exact_mod_cast p.two_le_m
    linarith
  have hK : 0 ≤ (p.K : ℝ) := by positivity
  have hden : 0 < 1 - Real.exp (-1) := by simp
  have hlog : 0 ≤ Real.log ((p.m : ℝ) - 1) := Real.log_nonneg hm
  dsimp [ReferenceOriginalKthReleaseSignedCost.B_rel]
  positivity

private theorem stoppedPhysicalTransferCount_integrable_fixedID
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p)
    (ids : CompletePublicTable.IDArray p) :
    Integrable (fun z : SourceInput p =>
      (ReferenceOriginalCalendarPhysicalTransferCount.actualStoppedPhysicalTransferCount
        rate rewards C_star C_h z : ℝ))
      (ReferenceFixedIDSourceSection.fixedIDSourceLaw ids) := by
  let ν := ReferenceFixedIDSourceSection.fixedIDSourceLaw ids
  let E : Fin (p.T + 1) → Set (SourceInput p) := fun k =>
    {z | ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
      rate rewards C_star C_h k z ≤ p.T}
  have hactive (k : Fin (p.T + 1)) : MeasurableSet (E k) := by
    have hfield := rankedStartField_sections_measurable
      rate rewards C_star C_h control0 ids k
    exact (PhaseStartConditionalWaiting.phaseStartSigmaAlgebra_le
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0)
      (ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
        rate rewards C_star C_h k)
      (ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate_isPreRoundStoppingTime
        rate rewards C_star C_h control0 k)) (E k) hfield.2
  have hind (k : Fin (p.T + 1)) : Integrable
      (fun z : SourceInput p => if z ∈ E k then (1 : ℝ) else 0) ν := by
    apply Integrable.of_mem_Icc
      (μ := ReferenceFixedIDSourceSection.fixedIDSourceLaw ids) 0 1
      ((Measurable.ite (hactive k) measurable_const measurable_const).aemeasurable)
    exact ae_of_all _ fun z => by
      split_ifs <;> norm_num
  have hsum : Integrable (fun z : SourceInput p =>
      ∑ k : Fin (p.T + 1), if z ∈ E k then (1 : ℝ) else 0) ν :=
    integrable_finsetSum Finset.univ (fun k _ => hind k)
  have hcount : (fun z : SourceInput p =>
      ∑ k : Fin (p.T + 1), if z ∈ E k then (1 : ℝ) else 0) =
      fun z => (ReferenceOriginalCalendarPhysicalTransferCount.actualStoppedPhysicalTransferCount
        rate rewards C_star C_h z : ℝ) := by
    funext z
    have hnat :=
      ReferenceOriginalStoppedPhysicalTransferStarts.sum_indicator_stoppedPhysicalTransferStartDate_eq_actualCount
        rate rewards C_star C_h z
    have hcast := congrArg (fun n : ℕ => (n : ℝ)) hnat
    simpa only [E, Set.mem_ofPred_eq, Nat.cast_sum, Nat.cast_ite,
      Nat.cast_one, Nat.cast_zero] using hcast
  rw [hcount] at hsum
  exact hsum

private theorem stoppedPhysicalTransferCount_mean_le_actualCount
    (control0 : TimeControl p) (ids : CompletePublicTable.IDArray p) :
    (∫ z : SourceInput p,
      (ReferenceOriginalCalendarPhysicalTransferCount.actualStoppedPhysicalTransferCount
        rate rewards C_star C_h z : ℝ)
      ∂ReferenceFixedIDSourceSection.fixedIDSourceLaw ids) ≤
    ∫ z : SourceInput p,
      (ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferCount
        rate rewards C_star C_h z : ℝ)
      ∂ReferenceFixedIDSourceSection.fixedIDSourceLaw ids := by
  have hstopped := stoppedPhysicalTransferCount_integrable_fixedID
    rate rewards C_star C_h control0 ids
  have hfull := ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferCount_integrable_fixedID
    rate rewards C_star C_h ids
  apply integral_mono hstopped hfull
  intro z
  change (ReferenceOriginalCalendarPhysicalTransferCount.actualStoppedPhysicalTransferCount
      rate rewards C_star C_h z : ℝ) ≤
    (ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferCount
      rate rewards C_star C_h z : ℝ)
  exact_mod_cast ReferenceOriginalCalendarPhysicalTransferCount.actualStoppedPhysicalTransferCount_le_full
    rate rewards C_star C_h z

/-- The total signed release mean under every fixed-ID law is bounded by the
same release constant times the expected actual stopped physical transfer
count. -/
public theorem stoppedReleaseSignedCharge_fixedID_mean_le_stoppedCount
    (control0 : TimeControl p) (ids : CompletePublicTable.IDArray p) :
    (∫ z : SourceInput p, stoppedReleaseSignedCharge rate rewards C_star C_h z
      ∂ReferenceFixedIDSourceSection.fixedIDSourceLaw ids) ≤
      B_rel (p := p) *
        ∫ z : SourceInput p,
          (ReferenceOriginalCalendarPhysicalTransferCount.actualStoppedPhysicalTransferCount
            rate rewards C_star C_h z : ℝ)
          ∂ReferenceFixedIDSourceSection.fixedIDSourceLaw ids := by
  let ν := ReferenceFixedIDSourceSection.fixedIDSourceLaw ids
  let E : Fin (p.T + 1) → Set (SourceInput p) := fun k =>
    {z | ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
      rate rewards C_star C_h k z ≤ p.T}
  have hE (k : Fin (p.T + 1)) : MeasurableSet (E k) := by
    have hfield := rankedStartField_sections_measurable
      rate rewards C_star C_h control0 ids k
    exact (PhaseStartConditionalWaiting.phaseStartSigmaAlgebra_le
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0)
      (ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
        rate rewards C_star C_h k)
      (ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate_isPreRoundStoppingTime
        rate rewards C_star C_h control0 k)) (E k) hfield.2
  have hindicator (k : Fin (p.T + 1)) : Integrable
      (fun z : SourceInput p => if z ∈ E k then (1 : ℝ) else 0) ν := by
    apply Integrable.of_mem_Icc
      (μ := ReferenceFixedIDSourceSection.fixedIDSourceLaw ids) 0 1
      ((Measurable.ite (hE k) measurable_const measurable_const).aemeasurable)
    exact ae_of_all _ fun z => by
      split_ifs <;> norm_num
  have hcountIntegral :
      (∑ k : Fin (p.T + 1), ν.real (E k)) =
        ∫ z : SourceInput p,
          (ReferenceOriginalCalendarPhysicalTransferCount.actualStoppedPhysicalTransferCount
            rate rewards C_star C_h z : ℝ) ∂ν := by
    have hsum :
        (∫ z : SourceInput p,
          ∑ k : Fin (p.T + 1), if z ∈ E k then (1 : ℝ) else 0 ∂ν) =
          ∫ z : SourceInput p,
            (ReferenceOriginalCalendarPhysicalTransferCount.actualStoppedPhysicalTransferCount
              rate rewards C_star C_h z : ℝ) ∂ν := by
      apply integral_congr_ae
      filter_upwards with z
      have hnat :=
        ReferenceOriginalStoppedPhysicalTransferStarts.sum_indicator_stoppedPhysicalTransferStartDate_eq_actualCount
          rate rewards C_star C_h z
      have hcast := congrArg (fun n : ℕ => (n : ℝ)) hnat
      simpa only [E, Set.mem_ofPred_eq, Nat.cast_sum, Nat.cast_ite,
        Nat.cast_one, Nat.cast_zero] using hcast
    calc
      _ = ∑ k : Fin (p.T + 1),
          ∫ z : SourceInput p, if z ∈ E k then (1 : ℝ) else 0 ∂ν := by
        apply Finset.sum_congr rfl
        intro k _
        calc
          ν.real (E k) =
              ∫ z : SourceInput p, (E k).indicator
                (fun _ => (1 : ℝ)) z ∂ν :=
            (integral_indicator_one
              (μ := ReferenceFixedIDSourceSection.fixedIDSourceLaw ids) (hE k)).symm
          _ = ∫ z : SourceInput p,
              if z ∈ E k then (1 : ℝ) else 0 ∂ν := by
            apply integral_congr_ae
            filter_upwards with z
            by_cases hz : ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
                rate rewards C_star C_h k z ≤ p.T <;>
              simp [Set.indicator, E, hz]
      _ = ∫ z : SourceInput p,
          ∑ k : Fin (p.T + 1), if z ∈ E k then (1 : ℝ) else 0 ∂ν := by
        symm
        exact integral_finsetSum Finset.univ (fun k _ => hindicator k)
      _ = _ := hsum
  have hchargeFun : (stoppedReleaseSignedCharge rate rewards C_star C_h) =
      fun z => ∑ k : Fin (p.T + 1),
        ReferenceOriginalKthReleaseSignedChargeLocalization.kthReleaseSignedCharge
          rate rewards C_star C_h z k := by
    funext z
    exact stoppedReleaseSignedCharge_eq_sum_kthReleaseSignedCharge
      rate rewards C_star C_h z
  calc
    _ = ∑ k : Fin (p.T + 1),
        ∫ z : SourceInput p,
          ReferenceOriginalKthReleaseSignedChargeLocalization.kthReleaseSignedCharge
            rate rewards C_star C_h z k ∂ν := by
      rw [hchargeFun]
      exact integral_finsetSum Finset.univ (fun k _ =>
        integrable_fixedID_of_integrable ids
          (ReferenceOriginalKthReleaseSignedCost.kthReleaseSignedCharge_integrable
            rate rewards C_star C_h k))
    _ ≤ ∑ k : Fin (p.T + 1), B_rel (p := p) * ν.real (E k) := by
      apply Finset.sum_le_sum
      intro k hk
      simpa only [ν, E, Set.mem_ofPred_eq] using
        kthReleaseSignedCharge_fixedID_mean_le_activeMass
          rate rewards C_star C_h control0 ids k
    _ = B_rel (p := p) *
        ∫ z : SourceInput p,
          (ReferenceOriginalCalendarPhysicalTransferCount.actualStoppedPhysicalTransferCount
            rate rewards C_star C_h z : ℝ) ∂ν := by
      rw [← Finset.mul_sum, hcountIntegral]

/-- The original fixed-ID stopped signed release mean obeys the manuscript's
transfer-count envelope with the same `B_rel`, `m`, `eta`, and horizon. -/
public theorem stoppedReleaseSignedCharge_fixedID_mean_le
    (control0 : TimeControl p) (ids : CompletePublicTable.IDArray p) :
    (∫ z : SourceInput p, stoppedReleaseSignedCharge rate rewards C_star C_h z
      ∂ReferenceFixedIDSourceSection.fixedIDSourceLaw ids) ≤
      B_rel (p := p) *
        ((4 * (p.m : ℝ) + 128) * rate.eta.val * (p.T : ℝ) + 2) := by
  have hbase := stoppedReleaseSignedCharge_fixedID_mean_le_stoppedCount
    rate rewards C_star C_h control0 ids
  have hcount := stoppedPhysicalTransferCount_mean_le_actualCount
    rate rewards C_star C_h control0 ids
  have hfull := ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferCount_fixedID_mean_le
    rate rewards C_star C_h ids
  have hstopped := hcount.trans hfull
  calc
    _ ≤ B_rel (p := p) *
        ∫ z : SourceInput p,
          (ReferenceOriginalCalendarPhysicalTransferCount.actualStoppedPhysicalTransferCount
            rate rewards C_star C_h z : ℝ)
          ∂ReferenceFixedIDSourceSection.fixedIDSourceLaw ids := hbase
    _ ≤ B_rel (p := p) *
        ((4 * (p.m : ℝ) + 128) * rate.eta.val * (p.T : ℝ) + 2) :=
      mul_le_mul_of_nonneg_left hstopped B_rel_nonneg

end Bandits.Support.ReferenceOriginalStoppedReleaseFixedIDMean

end
