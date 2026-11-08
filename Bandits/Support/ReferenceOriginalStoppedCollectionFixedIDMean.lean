/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceOriginalKthCollectionConditionalWaitingCost

import Mathlib.Tactic

/-!
# Fixed-ID expectation of the literal original stopped collection support

The two costs use the original calendar collection dates, original rounded
rewards, and the inclusive first-detection stop shared by the accepted kth-C
processes. Ranked-window reindexing is performed pointwise in the expectation
argument, retaining the mass of every rank that is actually present.

Sources: ZIP4 `06_interruptions.tex:431-490`,
`05_binary_transport.tex:180-240,293-349`, and `08_main_theorem.tex:78-109`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceOriginalKthCollectionPhaseSupport
open Bandits.Support.ReferenceOriginalKthCollectionSourceSections
open Bandits.Support.ReferenceOriginalKthCollectionCutoffAlignment
open Bandits.Support.ReferenceOriginalStoppedPhysicalTransferStarts
open Bandits.Support.ReferenceOriginalCalendarTransferPhaseCover
open Bandits.Support.ReferenceOriginalCalendarPhysicalTransferCount
open Bandits.Support.ReferenceFixedIDSourceSection
open Bandits.Support.ReferenceOriginalKthCollectionConditionalWaitingCost
open scoped BigOperators Classical ENNReal

namespace Bandits.Support.ReferenceOriginalStoppedCollectionFixedIDMean

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceOriginalKthCollectionConditionalWaitingCost.RateInput
abbrev SourceInput (p : Parameters) := BootstrapPrivateRoundStreams.SourceInput p
abbrev GridRewardTable (p : Parameters) := ReferenceOriginalKthCollectionConditionalWaitingCost.GridRewardTable p

variable {p : Parameters}
variable (rate : RateInput p) (rewards : GridRewardTable p)
  (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
  (k : Fin (p.T + 1))

local notation "Source" => SourceInput p
local notation "μ" => BootstrapPrivateRoundStreams.sourceInputLaw p
local notation "F" => ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0

/-- The literal uncapped original stopped C total on the source phase-cover dates. -/
public def C_uncap (z : Source) : ℝ :=
  ∑ t ∈ ReferenceOriginalCalendarTransferPhaseCover.collectionPhaseDates
      rate rewards C_star C_h z,
    (ReferenceFirstCollectionUpConditionalService.positiveRewardCount rewards t : ℝ)

/-- The literal capped original stopped C total on the same source dates. -/
public def C_cap (z : Source) : ℝ :=
  ∑ t ∈ ReferenceOriginalCalendarTransferPhaseCover.collectionPhaseDates
      rate rewards C_star C_h z,
    min (p.m : ℝ)
      (ReferenceFirstCollectionUpConditionalService.positiveRewardCount rewards t : ℝ)

private theorem collection_dates_in_retained_suffix (z : Source) :
    ReferenceOriginalCalendarTransferPhaseCover.collectionPhaseDates
        rate rewards C_star C_h z ⊆
      ReferenceOriginalCalendarTransferPhaseCover.retainedSuffixDates
        rate rewards C_star C_h z := by
  intro t ht
  rw [← ReferenceOriginalCalendarTransferPhaseCover.stopped_phase_dates_cover
    rate rewards C_star C_h z]
  simp [ht]

private theorem kthCDates_pairwise_disjoint (z : Source) :
    Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin (p.T + 1))))
      (fun k => ReferenceOriginalKthCollectionCutoffAlignment.kthCDates
        rate rewards C_star C_h z k) := by
  intro k hk l hl hne
  apply Finset.disjoint_left.mpr
  intro t hkt hlt
  have hkw := (Finset.mem_inter.mp hkt).1
  have hlw := (Finset.mem_inter.mp hlt).1
  exact (Finset.disjoint_left.mp
    (ReferenceOriginalStoppedTransferSignedReindex.kthStoppedTransferWindowDates_disjoint
      rate rewards C_star C_h z k l hne) hkw hlw)

private theorem kthCDates_biUnion_eq_collection (z : Source) :
    (Finset.univ : Finset (Fin (p.T + 1))).biUnion
        (fun k => ReferenceOriginalKthCollectionCutoffAlignment.kthCDates
          rate rewards C_star C_h z k) =
      ReferenceOriginalCalendarTransferPhaseCover.collectionPhaseDates
        rate rewards C_star C_h z := by
  ext t
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and,
    ReferenceOriginalKthCollectionCutoffAlignment.kthCDates, Finset.mem_inter]
  constructor
  · rintro ⟨k, _, htC⟩
    exact htC
  · intro htC
    have htRet := collection_dates_in_retained_suffix rate rewards C_star C_h z htC
    have hwindow : t ∈ (Finset.univ : Finset (Fin (p.T + 1))).biUnion
        (ReferenceOriginalStoppedTransferSignedReindex.kthStoppedTransferWindowDates
          rate rewards C_star C_h z) := by
      rw [ReferenceOriginalStoppedTransferSignedReindex.ranked_windows_biUnion_eq_retained_suffix]
      exact htRet
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at hwindow
    obtain ⟨k, hwindow⟩ := hwindow
    exact ⟨k, hwindow, htC⟩

/-- Pointwise finite reindexing of the literal uncapped original C total. -/
public theorem C_uncap_eq_ranked_sum (z : Source) :
    C_uncap rate rewards C_star C_h z =
      ∑ k : Fin (p.T + 1),
        ReferenceOriginalKthCollectionConditionalWaitingCost.kthCWaitingCharge
          rate rewards C_star C_h control0 k z := by
  classical
  have hdisjoint := kthCDates_pairwise_disjoint rate rewards C_star C_h z
  have hunion := kthCDates_biUnion_eq_collection rate rewards C_star C_h z
  unfold C_uncap ReferenceOriginalKthCollectionConditionalWaitingCost.kthCWaitingCharge
  rw [← Finset.sum_biUnion hdisjoint, hunion]

/-- Pointwise finite reindexing of the literal capped original C total. -/
public theorem C_cap_eq_ranked_sum (z : Source) :
    C_cap rate rewards C_star C_h z =
      ∑ k : Fin (p.T + 1),
        ReferenceOriginalKthCollectionConditionalWaitingCost.kthCappedWaitingCharge
          rate rewards C_star C_h control0 k z := by
  classical
  have hdisjoint := kthCDates_pairwise_disjoint rate rewards C_star C_h z
  have hunion := kthCDates_biUnion_eq_collection rate rewards C_star C_h z
  unfold C_cap ReferenceOriginalKthCollectionConditionalWaitingCost.kthCappedWaitingCharge
  rw [← Finset.sum_biUnion hdisjoint, hunion]

/-- The original capped kth-C charge reindexed to the predictable pending
set at each source date. -/
public theorem kthCappedWaitingCharge_eq_active_sum
    (k : Fin (p.T + 1)) (z : Source) :
    ReferenceOriginalKthCollectionConditionalWaitingCost.kthCappedWaitingCharge
        rate rewards C_star C_h control0 k z =
      ∑ n ∈ Finset.range p.T,
        if hn : n < p.T then
          if (ReferenceOriginalKthCollectionPhaseSupport.P
              rate rewards C_star C_h k n z).Nonempty then
            min (p.m : ℝ)
              (ReferenceFirstCollectionUpConditionalService.positiveRewardCount
                rewards ⟨n, hn⟩ : ℝ)
          else 0
        else 0 := by
  have hfilter : (Finset.univ.filter fun t : Fin p.T =>
      (ReferenceOriginalKthCollectionPhaseSupport.P
        rate rewards C_star C_h k t.val z).Nonempty) =
      ReferenceOriginalKthCollectionCutoffAlignment.kthCDates
        rate rewards C_star C_h z k := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ReferenceOriginalKthCollectionPhaseSupport.P_nonempty_iff_mem_kthCDates
      rate rewards C_star C_h k t.val z t.isLt
  calc
    ReferenceOriginalKthCollectionConditionalWaitingCost.kthCappedWaitingCharge
        rate rewards C_star C_h control0 k z =
      ∑ t ∈ ReferenceOriginalKthCollectionCutoffAlignment.kthCDates
        rate rewards C_star C_h z k,
        min (p.m : ℝ)
          (ReferenceFirstCollectionUpConditionalService.positiveRewardCount rewards t : ℝ) := rfl
    _ = ∑ t : Fin p.T, if (ReferenceOriginalKthCollectionPhaseSupport.P
        rate rewards C_star C_h k t.val z).Nonempty then
          min (p.m : ℝ)
            (ReferenceFirstCollectionUpConditionalService.positiveRewardCount rewards t : ℝ)
        else 0 := by rw [← hfilter, Finset.sum_filter]
    _ = ∑ n ∈ Finset.range p.T,
          if hn : n < p.T then
            if (ReferenceOriginalKthCollectionPhaseSupport.P
                rate rewards C_star C_h k n z).Nonempty then
              min (p.m : ℝ)
                (ReferenceFirstCollectionUpConditionalService.positiveRewardCount
                  rewards ⟨n, hn⟩ : ℝ)
            else 0
          else 0 := by
        rw [Finset.sum_range]
        apply Finset.sum_congr rfl
        intro n hn
        simp

/-- The capped charge vanishes when the actual ranked start is the horizon
sentinel. -/
public theorem kthCappedWaitingCharge_eq_zero_of_absent
    (k : Fin (p.T + 1)) (z : Source)
    (habsent : ¬ ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
      rate rewards C_star C_h k z ≤ p.T) :
    ReferenceOriginalKthCollectionConditionalWaitingCost.kthCappedWaitingCharge
      rate rewards C_star C_h control0 k z = 0 := by
  have hdates := ReferenceOriginalKthCollectionCutoffAlignment.kthCDates_empty_of_absent
    rate rewards C_star C_h z k habsent
  unfold ReferenceOriginalKthCollectionConditionalWaitingCost.kthCappedWaitingCharge
  rw [hdates]
  simp

public theorem kthCWaitingCharge_eq_zero_of_absent
    (k : Fin (p.T + 1)) (z : Source)
    (habsent : ¬ ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
      rate rewards C_star C_h k z ≤ p.T) :
    ReferenceOriginalKthCollectionConditionalWaitingCost.kthCWaitingCharge
      rate rewards C_star C_h control0 k z = 0 := by
  have hdates := ReferenceOriginalKthCollectionCutoffAlignment.kthCDates_empty_of_absent
    rate rewards C_star C_h z k habsent
  unfold ReferenceOriginalKthCollectionConditionalWaitingCost.kthCWaitingCharge
  rw [hdates]
  simp

private theorem fixedIDSourceSection_preRound
    (ids : CompletePublicTable.IDArray p) (n : ℕ) :
    MeasurableSet[F n]
      (ReferenceFixedIDSourceSection.fixedIDSourceSection ids) := by
  have hprefix : Measurable[F n]
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 (n - 1)) := by
    change Measurable[(inferInstance : MeasurableSpace (SourceInput p)).comap
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 (n - 1))]
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 (n - 1))
    exact comap_measurable _
  have hids : Measurable[F n] (fun z : SourceInput p =>
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 (n - 1) z).1.1) :=
    measurable_fst.comp (measurable_fst.comp hprefix)
  have hset : ReferenceFixedIDSourceSection.fixedIDSourceSection ids =
      (fun z : SourceInput p =>
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 (n - 1) z).1.1) ⁻¹'
          {ids} := by
    ext z
    simp [ReferenceFixedIDSourceSection.fixedIDSourceSection,
      ReferenceSourcePrefixHistoryFiltration.sourcePrefix_ids]
  rw [hset]
  exact (measurableSet_singleton ids).preimage hids

private theorem fixedIDSourceSection_stoppedStart_measurable
    (ids : CompletePublicTable.IDArray p) (k : Fin (p.T + 1)) :
    MeasurableSet[
      PhaseStartConditionalWaiting.phaseStartSigmaAlgebra F
        (ReferenceOriginalKthCollectionPhaseSupport.sigma rate rewards C_star C_h k)
        (ReferenceOriginalKthCollectionPhaseSupport.sigma_is_pre_round_stopping_time
          rate rewards C_star C_h control0 k)]
      (ReferenceFixedIDSourceSection.fixedIDSourceSection ids) := by
  let τ := ReferenceOriginalKthCollectionPhaseSupport.sigma rate rewards C_star C_h k
  have hτ := ReferenceOriginalKthCollectionPhaseSupport.sigma_is_pre_round_stopping_time
    rate rewards C_star C_h control0 k
  let hstop := PhaseStartConditionalWaiting.isStoppingTime_of_preRound F τ hτ
  apply (hstop.measurableSet
    (ReferenceFixedIDSourceSection.fixedIDSourceSection ids)).mpr
  have hD0 := fixedIDSourceSection_preRound control0 ids 0
  refine ⟨(le_iSup F 0) _ hD0, ?_⟩
  intro n
  have hround : MeasurableSet[F n] {z | (τ z : WithTop ℕ) ≤ n} := by
    convert hτ n using 1
    ext z
    norm_cast
  exact (fixedIDSourceSection_preRound control0 ids n).inter hround

private theorem stoppedStart_present_measurable
    (control0 : ContinuousLearningRows.TimeControl p) (k : Fin (p.T + 1)) :
    MeasurableSet {z : Source |
      ReferenceOriginalKthCollectionPhaseSupport.sigma rate rewards C_star C_h k z ≤ p.T} := by
  have hτ := ReferenceOriginalKthCollectionPhaseSupport.sigma_is_pre_round_stopping_time
    rate rewards C_star C_h control0 k
  exact (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le'
    p.T _ (hτ p.T)

private theorem stoppedStart_present_stoppedMeasurable
    (k : Fin (p.T + 1)) :
    MeasurableSet[
      PhaseStartConditionalWaiting.phaseStartSigmaAlgebra F
        (ReferenceOriginalKthCollectionPhaseSupport.sigma rate rewards C_star C_h k)
        (ReferenceOriginalKthCollectionPhaseSupport.sigma_is_pre_round_stopping_time
          rate rewards C_star C_h control0 k)]
      {z : Source |
        ReferenceOriginalKthCollectionPhaseSupport.sigma rate rewards C_star C_h k z ≤ p.T} := by
  let τ := ReferenceOriginalKthCollectionPhaseSupport.sigma rate rewards C_star C_h k
  have hτ := ReferenceOriginalKthCollectionPhaseSupport.sigma_is_pre_round_stopping_time
    rate rewards C_star C_h control0 k
  let hstop := PhaseStartConditionalWaiting.isStoppingTime_of_preRound F τ hτ
  have h := hstop.measurableSet_le' p.T
  simpa [τ] using h

private theorem kthCWaitingCharge_fixedID_mean_le_present_mass
    (ids : CompletePublicTable.IDArray p) (k : Fin (p.T + 1)) :
    (∫ z : Source,
      ReferenceOriginalKthCollectionConditionalWaitingCost.kthCWaitingCharge
        rate rewards C_star C_h control0 k z
      ∂ReferenceFixedIDSourceSection.fixedIDSourceLaw (p := p) ids) ≤
      ReferenceOriginalKthCollectionConditionalWaitingCost.B_col (p := p) *
        (ReferenceFixedIDSourceSection.fixedIDSourceLaw (p := p) ids).real
          {z : Source |
            ReferenceOriginalKthCollectionPhaseSupport.sigma
              rate rewards C_star C_h k z ≤ p.T} := by
  let τ := ReferenceOriginalKthCollectionPhaseSupport.sigma rate rewards C_star C_h k
  let D := ReferenceFixedIDSourceSection.fixedIDSourceSection ids
  let A : Set Source := {z | τ z ≤ p.T}
  let E := D ∩ A
  let ν := ReferenceFixedIDSourceSection.fixedIDSourceLaw (p := p) ids
  let f := ReferenceOriginalKthCollectionConditionalWaitingCost.kthCWaitingCharge
    rate rewards C_star C_h control0 k
  have hτ := ReferenceOriginalKthCollectionPhaseSupport.sigma_is_pre_round_stopping_time
    rate rewards C_star C_h control0 k
  have hEStop := (fixedIDSourceSection_stoppedStart_measurable
    rate rewards C_star C_h control0 ids k).inter
      (stoppedStart_present_stoppedMeasurable rate rewards C_star C_h control0 k)
  have hDMeas := ReferenceFixedIDSourceSection.measurable_fixedIDSourceSection ids
  have hAMeas := stoppedStart_present_measurable rate rewards C_star C_h control0 k
  have hEMeas : MeasurableSet E := hDMeas.inter hAMeas
  have hDInt := ReferenceOriginalKthCollectionConditionalWaitingCost.kthCWaiting_bounds
    rate rewards C_star C_h control0 k E hEStop
  have hsourceLocalized := hDInt.2.1
  have hsourceInt := hDInt.1
  have hDsubset : E ⊆ D := fun _ hz => hz.1
  have houtsideZero : (∫ z in D \ E, f z
      ∂BootstrapPrivateRoundStreams.sourceInputLaw p) = 0 := by
    calc
      _ = ∫ z in D \ E, (fun _ : Source => (0 : ℝ)) z
          ∂BootstrapPrivateRoundStreams.sourceInputLaw p := by
        apply setIntegral_congr_fun (hDMeas.diff hEMeas)
        intro z hz
        have hnotA : z ∉ A := by
          intro hA
          exact hz.2 ⟨hz.1, hA⟩
        have habsent : ¬ ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
            rate rewards C_star C_h k z ≤ p.T := by
          simpa [A, τ, ReferenceOriginalKthCollectionPhaseSupport.sigma] using hnotA
        exact kthCWaitingCharge_eq_zero_of_absent rate rewards C_star C_h control0
          k z habsent
      _ = 0 := by simp
  have hfs : IntegrableOn f D (BootstrapPrivateRoundStreams.sourceInputLaw p) :=
    hsourceInt.mono_measure Measure.restrict_le_self
  have hDminus := setIntegral_sdiff hEMeas hfs hDsubset
  have hlocalizedEq :
      (∫ z in D, f z ∂BootstrapPrivateRoundStreams.sourceInputLaw p) =
        ∫ z in E, f z ∂BootstrapPrivateRoundStreams.sourceInputLaw p := by
    rw [houtsideZero] at hDminus
    linarith
  have hAtomPos := ReferenceFixedIDSourceSection.idArrayAtom_positive (p := p) ids
  have hsectionIntegral := ReferenceFixedIDSourceSection.sourceInputLaw_setIntegral_fixedIDSourceSection
    (p := p) ids f
  have hsectionMass := ReferenceFixedIDSourceSection.sourceInputLaw_real_inter_fixedIDSourceSection
    (p := p) ids A hAMeas
  have hscaled :
      (CompletePublicTable.idArrayMeasure p).real {ids} *
          (∫ z, f z ∂ν) ≤
        ReferenceOriginalKthCollectionConditionalWaitingCost.B_col (p := p) *
          ((CompletePublicTable.idArrayMeasure p).real {ids} * ν.real A) := by
    calc
      _ = ∫ z in D, f z ∂BootstrapPrivateRoundStreams.sourceInputLaw p :=
        hsectionIntegral.symm
      _ = ∫ z in E, f z ∂BootstrapPrivateRoundStreams.sourceInputLaw p := hlocalizedEq
      _ ≤ ReferenceOriginalKthCollectionConditionalWaitingCost.B_col (p := p) *
          (BootstrapPrivateRoundStreams.sourceInputLaw p).real E := hsourceLocalized
      _ = ReferenceOriginalKthCollectionConditionalWaitingCost.B_col (p := p) *
          ((CompletePublicTable.idArrayMeasure p).real {ids} * ν.real A) := by
        rw [hsectionMass]
  have hmean :
      (∫ z, f z ∂ν) ≤
        ReferenceOriginalKthCollectionConditionalWaitingCost.B_col (p := p) * ν.real A := by
    have hc : 0 < (CompletePublicTable.idArrayMeasure p).real {ids} := hAtomPos
    calc
      _ = (((CompletePublicTable.idArrayMeasure p).real {ids} *
            (∫ z, f z ∂ν)) /
          (CompletePublicTable.idArrayMeasure p).real {ids}) := by
        field_simp [ne_of_gt hc]
      _ ≤ (ReferenceOriginalKthCollectionConditionalWaitingCost.B_col (p := p) *
            ((CompletePublicTable.idArrayMeasure p).real {ids} * ν.real A)) /
          (CompletePublicTable.idArrayMeasure p).real {ids} :=
        div_le_div_of_nonneg_right hscaled hc.le
      _ = ReferenceOriginalKthCollectionConditionalWaitingCost.B_col (p := p) * ν.real A := by
        field_simp [ne_of_gt hc]
  simpa [f, ν, A, τ] using hmean

private theorem kthCappedWaitingCharge_integrable
    (k : Fin (p.T + 1)) :
    Integrable (ReferenceOriginalKthCollectionConditionalWaitingCost.kthCappedWaitingCharge
      rate rewards C_star C_h control0 k) μ := by
  let G : Fin p.T → Source → ℝ := fun t z =>
    if (ReferenceOriginalKthCollectionPhaseSupport.P
        rate rewards C_star C_h k t.val z).Nonempty then
      min (p.m : ℝ)
        (ReferenceFirstCollectionUpConditionalService.positiveRewardCount rewards t : ℝ)
    else 0
  have hterm : ∀ t : Fin p.T, Integrable (G t) μ := by
    intro t
    have hpendingF : MeasurableSet[F (t.val + 1)]
        {z : Source | (ReferenceOriginalKthCollectionPhaseSupport.P
          rate rewards C_star C_h k t.val z).Nonempty} := by
      have hmem : {z : Source | (ReferenceOriginalKthCollectionPhaseSupport.P
          rate rewards C_star C_h k t.val z).Nonempty} =
          ⋃ i : Fin (p.m - 1), {z : Source |
            i ∈ ReferenceOriginalKthCollectionPhaseSupport.P
              rate rewards C_star C_h k t.val z} := by
        ext z
        simp only [Set.mem_ofPred_eq, Finset.Nonempty, Set.mem_iUnion]
      rw [hmem]
      exact MeasurableSet.iUnion fun i =>
        ReferenceOriginalKthCollectionPhaseSupport.P_mem_preRound_measurable_any
          rate rewards C_star C_h control0 k t.val i
    have hpending : MeasurableSet {z : Source |
        (ReferenceOriginalKthCollectionPhaseSupport.P
          rate rewards C_star C_h k t.val z).Nonempty} :=
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
        control0).le' (t.val + 1) _ hpendingF
    have hG : Measurable (G t) := by
      dsimp [G]
      exact Measurable.ite hpending measurable_const measurable_const
    have hbound : ∀ z, G t z ∈ Set.Icc (0 : ℝ) (p.m : ℝ) := by
      intro z
      by_cases hp : (ReferenceOriginalKthCollectionPhaseSupport.P
        rate rewards C_star C_h k t.val z).Nonempty
      · simp only [G, hp, ↓reduceIte]
        constructor
        · exact le_min (by positivity) (Nat.cast_nonneg _)
        · exact min_le_left _ _
      · simp [G, hp]
    apply Integrable.of_mem_Icc 0 (p.m : ℝ) hG.aemeasurable
    exact ae_of_all μ hbound
  have hsum : Integrable (fun z : Source => ∑ t : Fin p.T, G t z) μ := by
    apply integrable_finsetSum (Finset.univ : Finset (Fin p.T))
    intro t ht
    exact hterm t
  have hpointwise (z : Source) :
      ReferenceOriginalKthCollectionConditionalWaitingCost.kthCappedWaitingCharge
          rate rewards C_star C_h control0 k z = ∑ t : Fin p.T, G t z := by
    rw [kthCappedWaitingCharge_eq_active_sum]
    simp only [G]
    rw [Finset.sum_range]
    apply Finset.sum_congr rfl
    intro n hn
    simp
  exact hsum.congr (ae_of_all μ fun z => (hpointwise z).symm)

private theorem kthCWaitingCharge_integrable_source
    (k : Fin (p.T + 1)) :
    Integrable (ReferenceOriginalKthCollectionConditionalWaitingCost.kthCWaitingCharge
      rate rewards C_star C_h control0 k) μ := by
  exact (ReferenceOriginalKthCollectionConditionalWaitingCost.kthCWaiting_bounds
    rate rewards C_star C_h control0 k Set.univ MeasurableSet.univ).1

/-- Both literal stopped C totals are integrable on the unchanged original
source law. -/
public theorem C_totals_integrable_source
    (control0 : ContinuousLearningRows.TimeControl p) :
    Integrable (C_uncap rate rewards C_star C_h) μ ∧
      Integrable (C_cap rate rewards C_star C_h) μ := by
  have huncapSum : Integrable (fun z : Source =>
      ∑ k : Fin (p.T + 1),
        ReferenceOriginalKthCollectionConditionalWaitingCost.kthCWaitingCharge
          rate rewards C_star C_h control0 k z) μ := by
    apply integrable_finsetSum (Finset.univ : Finset (Fin (p.T + 1)))
    intro k hk
    exact kthCWaitingCharge_integrable_source rate rewards C_star C_h control0 k
  have huncapEq : (fun z : Source => C_uncap rate rewards C_star C_h z) =
      (fun z => ∑ k : Fin (p.T + 1),
        ReferenceOriginalKthCollectionConditionalWaitingCost.kthCWaitingCharge
          rate rewards C_star C_h control0 k z) := by
    funext z
    exact C_uncap_eq_ranked_sum rate rewards C_star C_h control0 z
  have hcapSum : Integrable (fun z : Source =>
      ∑ k : Fin (p.T + 1),
        ReferenceOriginalKthCollectionConditionalWaitingCost.kthCappedWaitingCharge
          rate rewards C_star C_h control0 k z) μ := by
    apply integrable_finsetSum (Finset.univ : Finset (Fin (p.T + 1)))
    intro k hk
    exact kthCappedWaitingCharge_integrable rate rewards C_star C_h control0 k
  have hcapEq : (fun z : Source => C_cap rate rewards C_star C_h z) =
      (fun z => ∑ k : Fin (p.T + 1),
        ReferenceOriginalKthCollectionConditionalWaitingCost.kthCappedWaitingCharge
          rate rewards C_star C_h control0 k z) := by
    funext z
    exact C_cap_eq_ranked_sum rate rewards C_star C_h control0 z
  exact ⟨huncapSum.congr (ae_of_all μ fun z => (congrFun huncapEq z).symm),
    hcapSum.congr (ae_of_all μ fun z => (congrFun hcapEq z).symm)⟩

private theorem integrable_under_fixedID_of_source
    (ids : CompletePublicTable.IDArray p) (f : Source → ℝ)
    (hf : Integrable f μ) :
    Integrable f (ReferenceFixedIDSourceSection.fixedIDSourceLaw (p := p) ids) := by
  have hrestrict : Integrable f
      ((BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
        (ReferenceFixedIDSourceSection.fixedIDSourceSection ids)) :=
    hf.mono_measure Measure.restrict_le_self
  rw [ReferenceFixedIDSourceSection.sourceInputLaw_restrict_fixedIDSourceSection] at hrestrict
  have hAtomPos := ReferenceFixedIDSourceSection.idArrayAtom_positive (p := p) ids
  have hAtomLt : CompletePublicTable.idArrayMeasure p {ids} < ∞ :=
    measure_lt_top _ _
  have hAtomFinite : CompletePublicTable.idArrayMeasure p {ids} ≠ ∞ := ne_of_lt hAtomLt
  have hAtomNe : CompletePublicTable.idArrayMeasure p {ids} ≠ 0 :=
    (measureReal_ne_zero_iff hAtomFinite).mp (ne_of_gt hAtomPos)
  exact (integrable_smul_measure hAtomNe hAtomFinite).mp hrestrict

/-- The two stopped C totals remain integrable under every original fixed-ID
section law, with all rows and private coordinates still in their source
product. -/
public theorem C_totals_integrable_fixedID
    (control0 : ContinuousLearningRows.TimeControl p)
    (ids : CompletePublicTable.IDArray p) :
    Integrable (C_uncap rate rewards C_star C_h)
        (ReferenceFixedIDSourceSection.fixedIDSourceLaw (p := p) ids) ∧
      Integrable (C_cap rate rewards C_star C_h)
        (ReferenceFixedIDSourceSection.fixedIDSourceLaw (p := p) ids) := by
  have hsource := C_totals_integrable_source rate rewards C_star C_h control0
  exact ⟨integrable_under_fixedID_of_source ids _ hsource.1,
    integrable_under_fixedID_of_source ids _ hsource.2⟩

private def stoppedStartPresentIndicator (k : Fin (p.T + 1))
    (z : Source) : ℝ :=
  if ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
      rate rewards C_star C_h k z ≤ p.T then 1 else 0

private theorem stoppedStartPresentIndicator_integrable_fixedID
    (control0 : ContinuousLearningRows.TimeControl p)
    (ids : CompletePublicTable.IDArray p) (k : Fin (p.T + 1)) :
    Integrable (stoppedStartPresentIndicator rate rewards C_star C_h k)
      (ReferenceFixedIDSourceSection.fixedIDSourceLaw (p := p) ids) := by
  have hpresent := stoppedStart_present_measurable rate rewards C_star C_h control0 k
  have hmeas : Measurable (stoppedStartPresentIndicator rate rewards C_star C_h k) := by
    change Measurable (fun z : Source =>
      if ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
          rate rewards C_star C_h k z ≤ p.T then (1 : ℝ) else 0)
    exact Measurable.ite hpresent measurable_const measurable_const
  apply Integrable.of_mem_Icc 0 1 hmeas.aemeasurable
  exact ae_of_all _ fun z => by
    dsimp [stoppedStartPresentIndicator]
    split <;> norm_num

private theorem stoppedStartPresentIndicator_integral
    (control0 : ContinuousLearningRows.TimeControl p)
    (ids : CompletePublicTable.IDArray p) (k : Fin (p.T + 1)) :
    (∫ z : Source, stoppedStartPresentIndicator rate rewards C_star C_h k z
      ∂ReferenceFixedIDSourceSection.fixedIDSourceLaw (p := p) ids) =
      (ReferenceFixedIDSourceSection.fixedIDSourceLaw (p := p) ids).real
        {z : Source |
          ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
            rate rewards C_star C_h k z ≤ p.T} := by
  have hpresent := stoppedStart_present_measurable rate rewards C_star C_h control0 k
  have hEq : stoppedStartPresentIndicator rate rewards C_star C_h k =
      ({z : Source |
        ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
          rate rewards C_star C_h k z ≤ p.T}.indicator fun _ => (1 : ℝ)) := by
    funext z
    by_cases hp : ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
        rate rewards C_star C_h k z ≤ p.T <;>
      simp [stoppedStartPresentIndicator, hp]
  rw [hEq]
  exact integral_indicator_one hpresent

/-- The actual inclusive stopped physical count is integrable under every
fixed-ID law, with its exact ranked-start indicator representation. -/
public theorem actualStoppedPhysicalTransferCount_integrable_fixedID
    (control0 : ContinuousLearningRows.TimeControl p)
    (ids : CompletePublicTable.IDArray p) :
    Integrable (fun z : Source =>
      (ReferenceOriginalCalendarPhysicalTransferCount.actualStoppedPhysicalTransferCount
        rate rewards C_star C_h z : ℝ))
      (ReferenceFixedIDSourceSection.fixedIDSourceLaw (p := p) ids) := by
  have hsum : Integrable (fun z : Source =>
      ∑ k : Fin (p.T + 1), stoppedStartPresentIndicator rate rewards C_star C_h k z)
      (ReferenceFixedIDSourceSection.fixedIDSourceLaw (p := p) ids) := by
    apply integrable_finsetSum (Finset.univ : Finset (Fin (p.T + 1)))
    intro k hk
    exact stoppedStartPresentIndicator_integrable_fixedID rate rewards C_star C_h control0 ids k
  have hEq : (fun z : Source =>
      (ReferenceOriginalCalendarPhysicalTransferCount.actualStoppedPhysicalTransferCount
        rate rewards C_star C_h z : ℝ)) =
      (fun z => ∑ k : Fin (p.T + 1),
        stoppedStartPresentIndicator rate rewards C_star C_h k z) := by
    funext z
    have hNat := ReferenceOriginalStoppedPhysicalTransferStarts.sum_indicator_stoppedPhysicalTransferStartDate_eq_actualCount
        rate rewards C_star C_h z
    rw [← hNat]
    simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hp : ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
        rate rewards C_star C_h k z ≤ p.T <;>
      simp [stoppedStartPresentIndicator, hp]
  exact hsum.congr (ae_of_all _ fun z => (congrFun hEq z).symm)

/-- The fixed-ID mean of the actual inclusive stopped count is the sum of the
present-rank probabilities, with no horizon multiplier. -/
public theorem actualStoppedPhysicalTransferCount_fixedID_mean_eq_ranked_present_mass
    (control0 : ContinuousLearningRows.TimeControl p)
    (ids : CompletePublicTable.IDArray p) :
    (∫ z : Source,
      (ReferenceOriginalCalendarPhysicalTransferCount.actualStoppedPhysicalTransferCount
        rate rewards C_star C_h z : ℝ)
      ∂ReferenceFixedIDSourceSection.fixedIDSourceLaw (p := p) ids) =
      ∑ k : Fin (p.T + 1),
        (ReferenceFixedIDSourceSection.fixedIDSourceLaw (p := p) ids).real
          {z : Source |
            ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
              rate rewards C_star C_h k z ≤ p.T} := by
  have hterm := fun k => stoppedStartPresentIndicator_integrable_fixedID
    rate rewards C_star C_h control0 ids k
  have hcountEq : (fun z : Source =>
      (ReferenceOriginalCalendarPhysicalTransferCount.actualStoppedPhysicalTransferCount
        rate rewards C_star C_h z : ℝ)) =
      (fun z => ∑ k : Fin (p.T + 1),
        stoppedStartPresentIndicator rate rewards C_star C_h k z) := by
    funext z
    have hNat := ReferenceOriginalStoppedPhysicalTransferStarts.sum_indicator_stoppedPhysicalTransferStartDate_eq_actualCount
        rate rewards C_star C_h z
    rw [← hNat]
    simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hp : ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
        rate rewards C_star C_h k z ≤ p.T <;>
      simp [stoppedStartPresentIndicator, hp]
  calc
    _ = ∫ z : Source,
        (∑ k : Fin (p.T + 1), stoppedStartPresentIndicator rate rewards C_star C_h k z)
        ∂ReferenceFixedIDSourceSection.fixedIDSourceLaw (p := p) ids := by
          exact congrArg (fun g : Source → ℝ =>
            ∫ z : Source, g z
              ∂ReferenceFixedIDSourceSection.fixedIDSourceLaw (p := p) ids) hcountEq
    _ = ∑ k : Fin (p.T + 1),
        ∫ z : Source, stoppedStartPresentIndicator rate rewards C_star C_h k z
          ∂ReferenceFixedIDSourceSection.fixedIDSourceLaw (p := p) ids := by
          rw [integral_finsetSum (Finset.univ : Finset (Fin (p.T + 1)))
            (fun k hk => hterm k)]
    _ = ∑ k : Fin (p.T + 1),
        (ReferenceFixedIDSourceSection.fixedIDSourceLaw (p := p) ids).real
          {z : Source |
            ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
              rate rewards C_star C_h k z ≤ p.T} := by
          apply Finset.sum_congr rfl
          intro k hk
          exact stoppedStartPresentIndicator_integral rate rewards C_star C_h control0 ids k

/-- The original uncapped stopped C mean is bounded using the actual stopped
physical count and the mass of each present original rank. -/
public theorem C_uncap_fixedID_mean_le_Bcol_mul_stoppedCount_mean
    (control0 : ContinuousLearningRows.TimeControl p)
    (ids : CompletePublicTable.IDArray p) :
    (∫ z : Source, C_uncap rate rewards C_star C_h z
      ∂ReferenceFixedIDSourceSection.fixedIDSourceLaw (p := p) ids) ≤
      ReferenceOriginalKthCollectionConditionalWaitingCost.B_col (p := p) *
        (∫ z : Source,
          (ReferenceOriginalCalendarPhysicalTransferCount.actualStoppedPhysicalTransferCount
            rate rewards C_star C_h z : ℝ)
          ∂ReferenceFixedIDSourceSection.fixedIDSourceLaw (p := p) ids) := by
  have htermInt : ∀ k : Fin (p.T + 1), Integrable
      (ReferenceOriginalKthCollectionConditionalWaitingCost.kthCWaitingCharge
        rate rewards C_star C_h control0 k)
      (ReferenceFixedIDSourceSection.fixedIDSourceLaw (p := p) ids) := by
    intro k
    exact integrable_under_fixedID_of_source ids _
      (kthCWaitingCharge_integrable_source rate rewards C_star C_h control0 k)
  have huncapRank : (fun z : Source => C_uncap rate rewards C_star C_h z) =
      (fun z => ∑ k : Fin (p.T + 1),
        ReferenceOriginalKthCollectionConditionalWaitingCost.kthCWaitingCharge
          rate rewards C_star C_h control0 k z) := by
    funext z
    exact C_uncap_eq_ranked_sum rate rewards C_star C_h control0 z
  have hUncapIntegral :
      (∫ z : Source, C_uncap rate rewards C_star C_h z
        ∂ReferenceFixedIDSourceSection.fixedIDSourceLaw (p := p) ids) =
        ∑ k : Fin (p.T + 1),
          ∫ z : Source,
            ReferenceOriginalKthCollectionConditionalWaitingCost.kthCWaitingCharge
              rate rewards C_star C_h control0 k z
            ∂ReferenceFixedIDSourceSection.fixedIDSourceLaw (p := p) ids := by
    calc
      _ = ∫ z : Source,
          (∑ k : Fin (p.T + 1),
            ReferenceOriginalKthCollectionConditionalWaitingCost.kthCWaitingCharge
              rate rewards C_star C_h control0 k z)
          ∂ReferenceFixedIDSourceSection.fixedIDSourceLaw (p := p) ids := by
            exact congrArg (fun g : Source → ℝ =>
              ∫ z : Source, g z
                ∂ReferenceFixedIDSourceSection.fixedIDSourceLaw (p := p) ids) huncapRank
      _ = _ := by
        rw [integral_finsetSum (Finset.univ : Finset (Fin (p.T + 1)))
          (fun k hk => htermInt k)]
  calc
    _ = ∑ k : Fin (p.T + 1),
        ∫ z : Source,
          ReferenceOriginalKthCollectionConditionalWaitingCost.kthCWaitingCharge
            rate rewards C_star C_h control0 k z
          ∂ReferenceFixedIDSourceSection.fixedIDSourceLaw (p := p) ids := hUncapIntegral
    _ ≤ ∑ k : Fin (p.T + 1),
        ReferenceOriginalKthCollectionConditionalWaitingCost.B_col (p := p) *
          (ReferenceFixedIDSourceSection.fixedIDSourceLaw (p := p) ids).real
            {z : Source |
              ReferenceOriginalKthCollectionPhaseSupport.sigma
                rate rewards C_star C_h k z ≤ p.T} := by
          apply Finset.sum_le_sum
          intro k hk
          exact kthCWaitingCharge_fixedID_mean_le_present_mass
            rate rewards C_star C_h control0 ids k
    _ = ReferenceOriginalKthCollectionConditionalWaitingCost.B_col (p := p) *
          (∫ z : Source,
            (ReferenceOriginalCalendarPhysicalTransferCount.actualStoppedPhysicalTransferCount
              rate rewards C_star C_h z : ℝ)
            ∂ReferenceFixedIDSourceSection.fixedIDSourceLaw (p := p) ids) := by
          rw [actualStoppedPhysicalTransferCount_fixedID_mean_eq_ranked_present_mass
            rate rewards C_star C_h control0 ids, Finset.mul_sum]
          simp [ReferenceOriginalKthCollectionPhaseSupport.sigma]

/-- The literal capped total is pointwise below the literal uncapped total on
the same original stopped collection dates. -/
public theorem C_cap_le_C_uncap (z : Source) :
    C_cap rate rewards C_star C_h z ≤ C_uncap rate rewards C_star C_h z := by
  unfold C_cap C_uncap
  apply Finset.sum_le_sum
  intro t ht
  exact min_le_right _ _

/-- The fixed-ID capped mean is bounded by the uncapped mean, with both
integrability obligations supplied under the original fixed-ID source law. -/
public theorem C_cap_fixedID_mean_le_C_uncap_fixedID_mean
    (control0 : ContinuousLearningRows.TimeControl p)
    (ids : CompletePublicTable.IDArray p) :
    (∫ z : Source, C_cap rate rewards C_star C_h z
      ∂ReferenceFixedIDSourceSection.fixedIDSourceLaw (p := p) ids) ≤
      (∫ z : Source, C_uncap rate rewards C_star C_h z
        ∂ReferenceFixedIDSourceSection.fixedIDSourceLaw (p := p) ids) := by
  have hInt := C_totals_integrable_fixedID rate rewards C_star C_h control0 ids
  apply integral_mono hInt.2 hInt.1
  intro z
  exact C_cap_le_C_uncap rate rewards C_star C_h z

/-- The accepted source constant multiplying the actual stopped count is
nonnegative. -/
public theorem B_col_nonneg :
    0 ≤ ReferenceOriginalKthCollectionConditionalWaitingCost.B_col (p := p) := by
  have hm2 : 2 ≤ p.m := p.two_le_m
  have hm : 1 ≤ p.m - 1 := by omega
  have hlog : 0 ≤ Real.log ((p.m - 1 : ℕ) : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast hm
  have hden : 0 < 1 - Real.exp (-1) := by
    have hk : PhaseServiceWaiting.kappa = 1 - Real.exp (-1) := rfl
    rw [← hk]
    exact PhaseServiceWaiting.kappa_pos
  unfold ReferenceOriginalKthCollectionConditionalWaitingCost.B_col
  apply mul_nonneg
  · apply div_nonneg
    · positivity
    · exact hden.le
  · positivity

/-- The actual inclusive stopped physical-count mean inherits the accepted
fixed-ID all-horizon source bound. -/
public theorem actualStoppedPhysicalTransferCount_fixedID_mean_le_source_bound
    (control0 : ContinuousLearningRows.TimeControl p)
    (ids : CompletePublicTable.IDArray p) :
    (∫ z : Source,
      (ReferenceOriginalCalendarPhysicalTransferCount.actualStoppedPhysicalTransferCount
        rate rewards C_star C_h z : ℝ)
      ∂ReferenceFixedIDSourceSection.fixedIDSourceLaw (p := p) ids) ≤
        (4 * (p.m : ℝ) + 128) * rate.eta.val * (p.T : ℝ) + 2 := by
  have hStopped := actualStoppedPhysicalTransferCount_integrable_fixedID
    rate rewards C_star C_h control0 ids
  have hFull :=
    ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferCount_integrable_fixedID
      (p := p) rate rewards C_star C_h ids
  have hmean :
      (∫ z : Source,
        (ReferenceOriginalCalendarPhysicalTransferCount.actualStoppedPhysicalTransferCount
          rate rewards C_star C_h z : ℝ)
        ∂ReferenceFixedIDSourceSection.fixedIDSourceLaw (p := p) ids) ≤
      (∫ z : Source,
        (ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferCount
          rate rewards C_star C_h z : ℝ)
        ∂ReferenceFixedIDSourceSection.fixedIDSourceLaw (p := p) ids) := by
    apply integral_mono hStopped hFull
    intro z
    change (ReferenceOriginalCalendarPhysicalTransferCount.actualStoppedPhysicalTransferCount
      rate rewards C_star C_h z : ℝ) ≤
        (ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferCount
          rate rewards C_star C_h z : ℝ)
    exact_mod_cast
      ReferenceOriginalCalendarPhysicalTransferCount.actualStoppedPhysicalTransferCount_le_full
        rate rewards C_star C_h z
  exact hmean.trans
    (ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferCount_fixedID_mean_le
      (p := p) rate rewards C_star C_h ids)

/-- The requested fixed-ID expectation chain for the original capped and
uncapped stopped collection totals and the actual inclusive stopped physical
count. -/
public theorem fixedID_collection_mean_chain
    (control0 : ContinuousLearningRows.TimeControl p)
    (ids : CompletePublicTable.IDArray p) :
    (∫ z : Source, C_cap rate rewards C_star C_h z
      ∂ReferenceFixedIDSourceSection.fixedIDSourceLaw (p := p) ids) ≤
        (∫ z : Source, C_uncap rate rewards C_star C_h z
          ∂ReferenceFixedIDSourceSection.fixedIDSourceLaw (p := p) ids) ∧
      (∫ z : Source, C_uncap rate rewards C_star C_h z
        ∂ReferenceFixedIDSourceSection.fixedIDSourceLaw (p := p) ids) ≤
        ReferenceOriginalKthCollectionConditionalWaitingCost.B_col (p := p) *
          (∫ z : Source,
            (ReferenceOriginalCalendarPhysicalTransferCount.actualStoppedPhysicalTransferCount
              rate rewards C_star C_h z : ℝ)
            ∂ReferenceFixedIDSourceSection.fixedIDSourceLaw (p := p) ids) ∧
      ReferenceOriginalKthCollectionConditionalWaitingCost.B_col (p := p) *
          (∫ z : Source,
            (ReferenceOriginalCalendarPhysicalTransferCount.actualStoppedPhysicalTransferCount
              rate rewards C_star C_h z : ℝ)
            ∂ReferenceFixedIDSourceSection.fixedIDSourceLaw (p := p) ids) ≤
        ReferenceOriginalKthCollectionConditionalWaitingCost.B_col (p := p) *
          ((4 * (p.m : ℝ) + 128) * rate.eta.val * (p.T : ℝ) + 2) := by
  refine ⟨C_cap_fixedID_mean_le_C_uncap_fixedID_mean
      rate rewards C_star C_h control0 ids,
    C_uncap_fixedID_mean_le_Bcol_mul_stoppedCount_mean
      rate rewards C_star C_h control0 ids, ?_⟩
  exact mul_le_mul_of_nonneg_left
    (actualStoppedPhysicalTransferCount_fixedID_mean_le_source_bound
      rate rewards C_star C_h control0 ids)
    (B_col_nonneg (p := p))


end Bandits.Support.ReferenceOriginalStoppedCollectionFixedIDMean

end
