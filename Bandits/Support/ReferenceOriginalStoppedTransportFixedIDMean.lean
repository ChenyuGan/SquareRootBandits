/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceOriginalStoppedCollectionFixedIDMean
public import Bandits.Support.ReferenceOriginalStoppedReleaseFixedIDMean
public import Bandits.Support.ReferenceOriginalKthHandoverConditionalWaitingCost

import Mathlib.Tactic

/-!
# Fixed-ID mean of the literal original stopped transport charge

The capped handover support is localized at the same original ranked stopped
start as its conditional waiting estimate. The literal collection, handover,
and signed release charges are then recombined on the actual original stopped
phase dates.

Sources: ZIP4 `05_binary_transport.tex:244-349`,
`06_interruptions.tex:431-533`, and `08_main_theorem.tex:78-109`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ContinuousLearningRows
open Bandits.Support.PhaseStartConditionalWaiting
open scoped BigOperators Classical ENNReal

namespace Bandits.Support.ReferenceOriginalStoppedTransportFixedIDMean

abbrev Parameters := ConstructorDimensions.Parameters
abbrev SourceInput (p : Parameters) := BootstrapPrivateRoundStreams.SourceInput p
abbrev RateInput := ReferenceOriginalStoppedCollectionFixedIDMean.RateInput
abbrev GridRewardTable := ReferenceOriginalStoppedCollectionFixedIDMean.GridRewardTable

variable {p : Parameters}
variable (rate : RateInput p) (rewards : GridRewardTable p)
  (C_star C_h : ℝ) (control0 : TimeControl p)

local notation "Source" => SourceInput p
local notation "μ" => BootstrapPrivateRoundStreams.sourceInputLaw p
local notation "F" => ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0

/-- The literal capped H support total on the actual original handover dates. -/
public def H_cap (z : Source) : ℝ :=
  ∑ t ∈ ReferenceOriginalCalendarTransferPhaseCover.handoverPhaseDates
      rate rewards C_star C_h z,
    ReferenceActualLiveEmptySignedRewardCalendar.liveEmptyCap rewards t

/-- The literal original stopped transport charge: capped support on collection
and handover dates, plus the signed actual release diagnostic. -/
public def J_stop (z : Source) : ℝ :=
  (∑ t ∈ (ReferenceOriginalCalendarTransferPhaseCover.collectionPhaseDates
      rate rewards C_star C_h z ∪
      ReferenceOriginalCalendarTransferPhaseCover.handoverPhaseDates
        rate rewards C_star C_h z),
    ReferenceActualLiveEmptySignedRewardCalendar.liveEmptyCap rewards t) +
  ∑ t ∈ ReferenceOriginalCalendarTransferPhaseCover.releasePhaseDates
      rate rewards C_star C_h z,
    ReferenceOriginalCalendarTransferPhaseCover.actualDateSignedDelta
      rate rewards C_star C_h z t

/-- The source's transport constant, with its three original phase bounds. -/
public def C_tr : ℝ :=
  ReferenceOriginalKthCollectionConditionalWaitingCost.B_col (p := p) +
    ReferenceOriginalFixedInstallationHandoverWaitingCost.B_hand (p := p) +
    ReferenceOriginalKthReleaseSignedCost.B_rel (p := p)

private theorem handover_dates_in_retained_suffix (z : Source) :
    ReferenceOriginalCalendarTransferPhaseCover.handoverPhaseDates
        rate rewards C_star C_h z ⊆
      ReferenceOriginalCalendarTransferPhaseCover.retainedSuffixDates
        rate rewards C_star C_h z := by
  rw [← ReferenceOriginalCalendarTransferPhaseCover.stopped_phase_dates_cover
    rate rewards C_star C_h z]
  intro t ht
  simp [ht]

private theorem kthHDates_pairwise_disjoint (z : Source) :
    Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin (p.T + 1))))
      (fun k => ReferenceOriginalKthHandoverBirthLocalization.kthHDates
        rate rewards C_star C_h k z) := by
  intro k hk l hl hne
  apply Finset.disjoint_left.mpr
  intro t hkt hlt
  have hkw := (Finset.mem_inter.mp hkt).1
  have hlw := (Finset.mem_inter.mp hlt).1
  exact (Finset.disjoint_left.mp
    (ReferenceOriginalStoppedTransferSignedReindex.kthStoppedTransferWindowDates_disjoint
      rate rewards C_star C_h z k l hne) hkw hlw)

private theorem kthHDates_biUnion_eq_handover (z : Source) :
    (Finset.univ : Finset (Fin (p.T + 1))).biUnion
        (fun k => ReferenceOriginalKthHandoverBirthLocalization.kthHDates
          rate rewards C_star C_h k z) =
      ReferenceOriginalCalendarTransferPhaseCover.handoverPhaseDates
        rate rewards C_star C_h z := by
  ext t
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and,
    ReferenceOriginalKthHandoverBirthLocalization.kthHDates, Finset.mem_inter]
  constructor
  · rintro ⟨k, _, htH⟩
    exact htH
  · intro htH
    have htRet := handover_dates_in_retained_suffix rate rewards C_star C_h z htH
    have hwindow : t ∈ (Finset.univ : Finset (Fin (p.T + 1))).biUnion
        (ReferenceOriginalStoppedTransferSignedReindex.kthStoppedTransferWindowDates
          rate rewards C_star C_h z) := by
      rw [ReferenceOriginalStoppedTransferSignedReindex.ranked_windows_biUnion_eq_retained_suffix]
      exact htRet
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at hwindow
    obtain ⟨k, hwindow⟩ := hwindow
    exact ⟨k, hwindow, htH⟩

private theorem kthHCappedCharge_eq_full_sum (k : Fin (p.T + 1)) (z : Source) :
    ReferenceOriginalKthHandoverConditionalWaitingCost.kthHCappedCharge
        rate rewards C_star C_h k z =
      ∑ t ∈ ReferenceOriginalKthHandoverBirthLocalization.kthHDates
        rate rewards C_star C_h k z,
        ReferenceActualLiveEmptySignedRewardCalendar.liveEmptyCap rewards t := by
  have hfilter :
      (ReferenceOriginalKthHandoverBirthLocalization.kthHDates
        rate rewards C_star C_h k z).filter (fun t : Fin p.T => t.val < p.T) =
      ReferenceOriginalKthHandoverBirthLocalization.kthHDates
        rate rewards C_star C_h k z :=
    Finset.filter_true_of_mem (fun t _ => t.isLt)
  unfold ReferenceOriginalKthHandoverConditionalWaitingCost.kthHCappedCharge
    ReferenceOriginalKthHandoverBirthLocalization.kthHCappedChargePrefix
  rw [hfilter]

/-- The actual capped H total is exactly the sum of the original ranked kth-H
charges, including empty and absent ranks. -/
public theorem H_cap_eq_ranked_sum (z : Source) :
    H_cap rate rewards C_star C_h z =
      ∑ k : Fin (p.T + 1),
        ReferenceOriginalKthHandoverConditionalWaitingCost.kthHCappedCharge
          rate rewards C_star C_h k z := by
  classical
  have hdisjoint := kthHDates_pairwise_disjoint rate rewards C_star C_h z
  have hunion := kthHDates_biUnion_eq_handover rate rewards C_star C_h z
  calc
    H_cap rate rewards C_star C_h z =
        ∑ t ∈ (Finset.univ : Finset (Fin (p.T + 1))).biUnion
          (fun k => ReferenceOriginalKthHandoverBirthLocalization.kthHDates
            rate rewards C_star C_h k z),
          ReferenceActualLiveEmptySignedRewardCalendar.liveEmptyCap rewards t := by
      unfold H_cap
      rw [hunion]
    _ = ∑ k : Fin (p.T + 1),
          ∑ t ∈ ReferenceOriginalKthHandoverBirthLocalization.kthHDates
            rate rewards C_star C_h k z,
            ReferenceActualLiveEmptySignedRewardCalendar.liveEmptyCap rewards t :=
      Finset.sum_biUnion hdisjoint
    _ = ∑ k : Fin (p.T + 1),
          ReferenceOriginalKthHandoverConditionalWaitingCost.kthHCappedCharge
            rate rewards C_star C_h k z := by
      apply Finset.sum_congr rfl
      intro k hk
      exact (kthHCappedCharge_eq_full_sum rate rewards C_star C_h k z).symm

private theorem kthHCappedCharge_eq_zero_of_absent
    (k : Fin (p.T + 1)) (z : Source)
    (habsent : ¬ ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
      rate rewards C_star C_h k z ≤ p.T) :
    ReferenceOriginalKthHandoverConditionalWaitingCost.kthHCappedCharge
      rate rewards C_star C_h k z = 0 := by
  have hwindow := ReferenceOriginalStoppedTransferSignedReindex.absent_ranked_window_empty
    rate rewards C_star C_h z k habsent
  have hdates : ReferenceOriginalKthHandoverBirthLocalization.kthHDates
      rate rewards C_star C_h k z = ∅ := by
    simp [ReferenceOriginalKthHandoverBirthLocalization.kthHDates, hwindow]
  rw [kthHCappedCharge_eq_full_sum rate rewards C_star C_h k z, hdates]
  simp

private theorem fixedIDSourceSection_preRound
    (ids : CompletePublicTable.IDArray p) (n : ℕ) :
    MeasurableSet[F n]
      (ReferenceFixedIDSourceSection.fixedIDSourceSection ids) := by
  have hprefix : Measurable[F n]
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 (n - 1)) := by
    change Measurable[(inferInstance : MeasurableSpace Source).comap
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 (n - 1))]
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 (n - 1))
    exact comap_measurable _
  have hids : Measurable[F n] (fun z : Source =>
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 (n - 1) z).1.1) :=
    measurable_fst.comp (measurable_fst.comp hprefix)
  have hset : ReferenceFixedIDSourceSection.fixedIDSourceSection ids =
      (fun z : Source =>
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 (n - 1) z).1.1) ⁻¹'
          {ids} := by
    ext z
    simp [ReferenceFixedIDSourceSection.fixedIDSourceSection,
      ReferenceSourcePrefixHistoryFiltration.sourcePrefix_ids]
  rw [hset]
  exact (measurableSet_singleton ids).preimage hids

private theorem fixedIDSourceSection_stoppedStart_measurable
    (ids : CompletePublicTable.IDArray p) (k : Fin (p.T + 1)) :
    MeasurableSet[ReferenceOriginalKthHandoverConditionalWaitingCost.kthHStartSigmaAlgebra
        rate rewards C_star C_h control0 k]
      (ReferenceFixedIDSourceSection.fixedIDSourceSection ids) := by
  let τ := ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
    rate rewards C_star C_h k
  let hτ := ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate_isPreRoundStoppingTime
    rate rewards C_star C_h control0 k
  let hstop := PhaseStartConditionalWaiting.isStoppingTime_of_preRound F τ hτ
  apply (hstop.measurableSet
    (ReferenceFixedIDSourceSection.fixedIDSourceSection ids)).mpr
  have hD0 := fixedIDSourceSection_preRound control0 ids 0
  refine ⟨(le_iSup F 0) _ hD0, ?_⟩
  intro n
  have hround : MeasurableSet[F n]
      {z | (τ z : WithTop ℕ) ≤ n} := by
    convert hτ n using 1
    ext z
    norm_cast
  exact (fixedIDSourceSection_preRound control0 ids n).inter hround

private theorem stoppedStart_present_stoppedMeasurable
    (k : Fin (p.T + 1)) :
    MeasurableSet[ReferenceOriginalKthHandoverConditionalWaitingCost.kthHStartSigmaAlgebra
        rate rewards C_star C_h control0 k]
      {z : Source |
        ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
          rate rewards C_star C_h k z ≤ p.T} := by
  let τ := ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
    rate rewards C_star C_h k
  let hτ := ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate_isPreRoundStoppingTime
    rate rewards C_star C_h control0 k
  let hstop := PhaseStartConditionalWaiting.isStoppingTime_of_preRound F τ hτ
  have h := hstop.measurableSet_le' p.T
  simpa [τ] using h

private theorem kthHCappedCharge_fixedID_mean_le_present_mass
    (control0 : TimeControl p) (ids : CompletePublicTable.IDArray p)
    (k : Fin (p.T + 1)) :
    (∫ z : Source,
      ReferenceOriginalKthHandoverConditionalWaitingCost.kthHCappedCharge
        rate rewards C_star C_h k z
      ∂ReferenceFixedIDSourceSection.fixedIDSourceLaw (p := p) ids) ≤
      ReferenceOriginalFixedInstallationHandoverWaitingCost.B_hand (p := p) *
        (ReferenceFixedIDSourceSection.fixedIDSourceLaw (p := p) ids).real
          {z : Source |
            ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
              rate rewards C_star C_h k z ≤ p.T} := by
  let τ := ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
    rate rewards C_star C_h k
  let A : Set Source := {z | τ z ≤ p.T}
  let D := ReferenceFixedIDSourceSection.fixedIDSourceSection ids
  let E := D ∩ A
  let ν := ReferenceFixedIDSourceSection.fixedIDSourceLaw (p := p) ids
  let f := ReferenceOriginalKthHandoverConditionalWaitingCost.kthHCappedCharge
    rate rewards C_star C_h k
  have hDfield := fixedIDSourceSection_stoppedStart_measurable
    rate rewards C_star C_h control0 ids k
  have hAfield0 := stoppedStart_present_stoppedMeasurable
    rate rewards C_star C_h control0 k
  have hAfield : MeasurableSet[
      ReferenceOriginalKthHandoverConditionalWaitingCost.kthHStartSigmaAlgebra
        rate rewards C_star C_h control0 k] A := by
    simpa [A, τ] using hAfield0
  have hDMeas := ReferenceFixedIDSourceSection.measurable_fixedIDSourceSection
    (p := p) ids
  have hAMeas : MeasurableSet A := by
    have hτ := ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate_isPreRoundStoppingTime
      rate rewards C_star C_h control0 k
    exact (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le'
      p.T _ (hτ p.T)
  have hEMeas : MeasurableSet E := by
    exact hDMeas.inter hAMeas
  have hEfield : MeasurableSet[
      ReferenceOriginalKthHandoverConditionalWaitingCost.kthHStartSigmaAlgebra
        rate rewards C_star C_h control0 k] E := hDfield.inter hAfield
  have hsourceBound :=
    ReferenceOriginalKthHandoverConditionalWaitingCost.setIntegral_kthHCappedCharge_le_B_hand
      rate rewards C_star C_h control0 k E hEfield
  have hsourceInt :=
    ReferenceOriginalKthHandoverConditionalWaitingCost.kthHCappedCharge_integrable
      rate rewards C_star C_h k
  have hDsubset : E ⊆ D := fun _ hz => hz.1
  have houtsideZero :
      (∫ z in D \ E, f z ∂BootstrapPrivateRoundStreams.sourceInputLaw p) = 0 := by
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
          simpa [A, τ] using hnotA
        exact kthHCappedCharge_eq_zero_of_absent rate rewards C_star C_h k z habsent
      _ = 0 := by simp
  have hfs : IntegrableOn f D (BootstrapPrivateRoundStreams.sourceInputLaw p) :=
    hsourceInt.mono_measure Measure.restrict_le_self
  have hDminus := setIntegral_sdiff hEMeas hfs hDsubset
  have hlocalized :
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
      (CompletePublicTable.idArrayMeasure p).real {ids} * (∫ z, f z ∂ν) ≤
        ReferenceOriginalFixedInstallationHandoverWaitingCost.B_hand (p := p) *
          ((CompletePublicTable.idArrayMeasure p).real {ids} * ν.real A) := by
    calc
      _ = ∫ z in D, f z ∂BootstrapPrivateRoundStreams.sourceInputLaw p :=
        hsectionIntegral.symm
      _ = ∫ z in E, f z ∂BootstrapPrivateRoundStreams.sourceInputLaw p := hlocalized
      _ ≤ ReferenceOriginalFixedInstallationHandoverWaitingCost.B_hand (p := p) *
          (BootstrapPrivateRoundStreams.sourceInputLaw p).real E := hsourceBound
      _ = ReferenceOriginalFixedInstallationHandoverWaitingCost.B_hand (p := p) *
          ((CompletePublicTable.idArrayMeasure p).real {ids} * ν.real A) := by
        rw [hsectionMass]
  have hmean :
      (∫ z, f z ∂ν) ≤
        ReferenceOriginalFixedInstallationHandoverWaitingCost.B_hand (p := p) * ν.real A := by
    have hc : 0 < (CompletePublicTable.idArrayMeasure p).real {ids} := hAtomPos
    calc
      _ = (((CompletePublicTable.idArrayMeasure p).real {ids} *
            (∫ z, f z ∂ν)) /
          (CompletePublicTable.idArrayMeasure p).real {ids}) := by
        field_simp [ne_of_gt hc]
      _ ≤ (ReferenceOriginalFixedInstallationHandoverWaitingCost.B_hand (p := p) *
            ((CompletePublicTable.idArrayMeasure p).real {ids} * ν.real A)) /
          (CompletePublicTable.idArrayMeasure p).real {ids} :=
        div_le_div_of_nonneg_right hscaled hc.le
      _ = ReferenceOriginalFixedInstallationHandoverWaitingCost.B_hand (p := p) * ν.real A := by
        field_simp [ne_of_gt hc]
  simpa [f, ν, A, τ] using hmean

private theorem integrable_fixedID_of_source
    (ids : CompletePublicTable.IDArray p) {f : Source → ℝ}
    (hf : Integrable f μ) :
    Integrable f (ReferenceFixedIDSourceSection.fixedIDSourceLaw (p := p) ids) := by
  have hrestrict : Integrable f
      ((BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
        (ReferenceFixedIDSourceSection.fixedIDSourceSection ids)) :=
    hf.mono_measure Measure.restrict_le_self
  rw [ReferenceFixedIDSourceSection.sourceInputLaw_restrict_fixedIDSourceSection
    (p := p) ids] at hrestrict
  have hAtom : CompletePublicTable.idArrayMeasure p {ids} ≠ 0 := by
    exact (measureReal_ne_zero_iff
      (h := (ReferenceFixedIDSourceSection.idArrayAtom_lt_top (p := p) ids).ne)).mp
        (ne_of_gt (ReferenceFixedIDSourceSection.idArrayAtom_positive (p := p) ids))
  exact (integrable_smul_measure hAtom
    (ReferenceFixedIDSourceSection.idArrayAtom_lt_top (p := p) ids).ne).mp hrestrict

/-- The actual capped H total is integrable under the unchanged source law. -/
public theorem H_cap_integrable_source :
    Integrable (H_cap rate rewards C_star C_h) μ := by
  have hsum : Integrable (fun z : Source =>
      ∑ k : Fin (p.T + 1),
        ReferenceOriginalKthHandoverConditionalWaitingCost.kthHCappedCharge
          rate rewards C_star C_h k z) μ := by
    apply integrable_finsetSum (Finset.univ : Finset (Fin (p.T + 1)))
    intro k hk
    exact ReferenceOriginalKthHandoverConditionalWaitingCost.kthHCappedCharge_integrable
      rate rewards C_star C_h k
  have hfun : (H_cap rate rewards C_star C_h) = fun z =>
      ∑ k : Fin (p.T + 1),
        ReferenceOriginalKthHandoverConditionalWaitingCost.kthHCappedCharge
          rate rewards C_star C_h k z := by
    funext z
    exact H_cap_eq_ranked_sum rate rewards C_star C_h z
  exact hsum.congr (ae_of_all μ fun z => (congrFun hfun z).symm)

/-- The actual capped H total remains integrable under every original fixed-ID
section law. -/
public theorem H_cap_integrable_fixedID
    (ids : CompletePublicTable.IDArray p) :
    Integrable (H_cap rate rewards C_star C_h)
      (ReferenceFixedIDSourceSection.fixedIDSourceLaw (p := p) ids) := by
  exact integrable_fixedID_of_source ids
    (H_cap_integrable_source rate rewards C_star C_h)

/-- The total capped H support mean is bounded by the handover constant times
the expected actual inclusive stopped physical transfer count. -/
public theorem H_cap_fixedID_mean_le_stoppedCount
    (control0 : TimeControl p) (ids : CompletePublicTable.IDArray p) :
    (∫ z : Source, H_cap rate rewards C_star C_h z
      ∂ReferenceFixedIDSourceSection.fixedIDSourceLaw (p := p) ids) ≤
      ReferenceOriginalFixedInstallationHandoverWaitingCost.B_hand (p := p) *
        (∫ z : Source,
          (ReferenceOriginalCalendarPhysicalTransferCount.actualStoppedPhysicalTransferCount
            rate rewards C_star C_h z : ℝ)
          ∂ReferenceFixedIDSourceSection.fixedIDSourceLaw (p := p) ids) := by
  let ν := ReferenceFixedIDSourceSection.fixedIDSourceLaw (p := p) ids
  have htermInt : ∀ k : Fin (p.T + 1), Integrable
      (ReferenceOriginalKthHandoverConditionalWaitingCost.kthHCappedCharge
        rate rewards C_star C_h k) ν := by
    intro k
    exact integrable_fixedID_of_source ids
      (ReferenceOriginalKthHandoverConditionalWaitingCost.kthHCappedCharge_integrable
        rate rewards C_star C_h k)
  have hsumInt : Integrable (fun z : Source =>
      ∑ k : Fin (p.T + 1),
        ReferenceOriginalKthHandoverConditionalWaitingCost.kthHCappedCharge
          rate rewards C_star C_h k z) ν := by
    apply integrable_finsetSum (Finset.univ : Finset (Fin (p.T + 1)))
    intro k hk
    exact htermInt k
  have hfun : (H_cap rate rewards C_star C_h) = fun z =>
      ∑ k : Fin (p.T + 1),
        ReferenceOriginalKthHandoverConditionalWaitingCost.kthHCappedCharge
          rate rewards C_star C_h k z := by
    funext z
    exact H_cap_eq_ranked_sum rate rewards C_star C_h z
  have hcount :
      (∫ z : Source,
        (ReferenceOriginalCalendarPhysicalTransferCount.actualStoppedPhysicalTransferCount
          rate rewards C_star C_h z : ℝ) ∂ν) =
        ∑ k : Fin (p.T + 1),
          ν.real {z : Source |
            ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
              rate rewards C_star C_h k z ≤ p.T} :=
    ReferenceOriginalStoppedCollectionFixedIDMean.actualStoppedPhysicalTransferCount_fixedID_mean_eq_ranked_present_mass
      rate rewards C_star C_h control0 ids
  calc
    _ = ∑ k : Fin (p.T + 1),
        ∫ z : Source,
          ReferenceOriginalKthHandoverConditionalWaitingCost.kthHCappedCharge
            rate rewards C_star C_h k z ∂ν := by
      rw [hfun]
      exact integral_finsetSum Finset.univ (fun k hk => htermInt k)
    _ ≤ ∑ k : Fin (p.T + 1),
        ReferenceOriginalFixedInstallationHandoverWaitingCost.B_hand (p := p) *
          ν.real {z : Source |
            ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
              rate rewards C_star C_h k z ≤ p.T} := by
      apply Finset.sum_le_sum
      intro k hk
      exact kthHCappedCharge_fixedID_mean_le_present_mass
        rate rewards C_star C_h control0 ids k
    _ = ReferenceOriginalFixedInstallationHandoverWaitingCost.B_hand (p := p) *
        ∫ z : Source,
          (ReferenceOriginalCalendarPhysicalTransferCount.actualStoppedPhysicalTransferCount
            rate rewards C_star C_h z : ℝ) ∂ν := by
      rw [← Finset.mul_sum, hcount]

private theorem liveEmptyCap_eq_cappedPositiveRewardCount (t : Fin p.T) :
    ReferenceActualLiveEmptySignedRewardCalendar.liveEmptyCap rewards t =
      min (p.m : ℝ)
        (ReferenceFirstCollectionUpConditionalService.positiveRewardCount rewards t : ℝ) := by
  have hden : 0 < ((D p : ℕ) : ℝ) := by exact_mod_cast D_pos p
  have hrow (a : Fin p.K) :
      0 < (rewards t a : ℝ) / (D p : ℝ) ↔ 0 < rewards t a := by
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
  unfold ReferenceActualLiveEmptySignedRewardCalendar.liveEmptyCap
    ReferenceFirstCollectionUpConditionalService.positiveRewardCount
  rw [hsets]

private theorem C_cap_eq_collection_liveEmptyCap (z : Source) :
    ReferenceOriginalStoppedCollectionFixedIDMean.C_cap rate rewards C_star C_h z =
      ∑ t ∈ ReferenceOriginalCalendarTransferPhaseCover.collectionPhaseDates
        rate rewards C_star C_h z,
        ReferenceActualLiveEmptySignedRewardCalendar.liveEmptyCap rewards t := by
  unfold ReferenceOriginalStoppedCollectionFixedIDMean.C_cap
  apply Finset.sum_congr rfl
  intro t ht
  exact (liveEmptyCap_eq_cappedPositiveRewardCount rewards t).symm

/-- The literal source transport total equals the accepted capped C total, the
actual capped H total, and the accepted signed R total. -/
public theorem J_stop_eq_components (z : Source) :
    J_stop rate rewards C_star C_h z =
      ReferenceOriginalStoppedCollectionFixedIDMean.C_cap rate rewards C_star C_h z +
        H_cap rate rewards C_star C_h z +
        ReferenceOriginalStoppedReleaseFixedIDMean.stoppedReleaseSignedCharge
          rate rewards C_star C_h z := by
  have hdisjoint :=
    (ReferenceOriginalCalendarTransferPhaseCover.stopped_phase_dates_pairwise_disjoint
      rate rewards C_star C_h z).1
  unfold J_stop H_cap
  rw [Finset.sum_union hdisjoint,
    ← C_cap_eq_collection_liveEmptyCap rate rewards C_star C_h z]
  rfl

/-- The literal stopped transport total is integrable on the original source
law. -/
public theorem J_stop_integrable_source (control0 : TimeControl p) :
    Integrable (J_stop rate rewards C_star C_h) μ := by
  have hC := ReferenceOriginalStoppedCollectionFixedIDMean.C_totals_integrable_source
    rate rewards C_star C_h control0
  have hH := H_cap_integrable_source rate rewards C_star C_h
  have hR := ReferenceOriginalStoppedReleaseFixedIDMean.stoppedReleaseSignedCharge_integrable_source
    rate rewards C_star C_h
  have hsum : Integrable (fun z : Source =>
      ReferenceOriginalStoppedCollectionFixedIDMean.C_cap rate rewards C_star C_h z +
        H_cap rate rewards C_star C_h z +
        ReferenceOriginalStoppedReleaseFixedIDMean.stoppedReleaseSignedCharge
          rate rewards C_star C_h z) μ :=
    hC.2.add hH |>.add hR
  have hfun : (J_stop rate rewards C_star C_h) = fun z =>
      ReferenceOriginalStoppedCollectionFixedIDMean.C_cap rate rewards C_star C_h z +
        H_cap rate rewards C_star C_h z +
        ReferenceOriginalStoppedReleaseFixedIDMean.stoppedReleaseSignedCharge
          rate rewards C_star C_h z := by
    funext z
    exact J_stop_eq_components rate rewards C_star C_h z
  exact hsum.congr (ae_of_all μ fun z => (congrFun hfun z).symm)

/-- The same literal stopped transport total is integrable under every
original fixed-ID section law. -/
public theorem J_stop_integrable_fixedID
    (control0 : TimeControl p) (ids : CompletePublicTable.IDArray p) :
    Integrable (J_stop rate rewards C_star C_h)
      (ReferenceFixedIDSourceSection.fixedIDSourceLaw (p := p) ids) := by
  have hC := ReferenceOriginalStoppedCollectionFixedIDMean.C_totals_integrable_fixedID
    rate rewards C_star C_h control0 ids
  have hH := H_cap_integrable_fixedID rate rewards C_star C_h ids
  have hR := ReferenceOriginalStoppedReleaseFixedIDMean.stoppedReleaseSignedCharge_integrable_fixedID
    rate rewards C_star C_h ids
  have hsum : Integrable (fun z : Source =>
      ReferenceOriginalStoppedCollectionFixedIDMean.C_cap rate rewards C_star C_h z +
        H_cap rate rewards C_star C_h z +
        ReferenceOriginalStoppedReleaseFixedIDMean.stoppedReleaseSignedCharge
          rate rewards C_star C_h z)
      (ReferenceFixedIDSourceSection.fixedIDSourceLaw (p := p) ids) :=
    hC.2.add hH |>.add hR
  have hfun : (J_stop rate rewards C_star C_h) = fun z =>
      ReferenceOriginalStoppedCollectionFixedIDMean.C_cap rate rewards C_star C_h z +
        H_cap rate rewards C_star C_h z +
        ReferenceOriginalStoppedReleaseFixedIDMean.stoppedReleaseSignedCharge
          rate rewards C_star C_h z := by
    funext z
    exact J_stop_eq_components rate rewards C_star C_h z
  exact hsum.congr (ae_of_all _ fun z => (congrFun hfun z).symm)

/-- The manuscript's handover constant is nonnegative. -/
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

private theorem B_rel_nonneg :
    0 ≤ ReferenceOriginalKthReleaseSignedCost.B_rel (p := p) := by
  have hm : 1 ≤ (p.m : ℝ) - 1 := by
    have hmc : (2 : ℝ) ≤ (p.m : ℝ) := by exact_mod_cast p.two_le_m
    linarith
  have hK : 0 ≤ (p.K : ℝ) := by positivity
  have hden : 0 < 1 - Real.exp (-1 : ℝ) := by simp
  have hlog : 0 ≤ Real.log ((p.m : ℝ) - 1) := Real.log_nonneg hm
  dsimp [ReferenceOriginalKthReleaseSignedCost.B_rel]
  positivity

/-- The sum of the three source constants is nonnegative. -/
private theorem C_tr_nonneg : 0 ≤ C_tr (p := p) := by
  have hcol := ReferenceOriginalStoppedCollectionFixedIDMean.B_col_nonneg
    (p := p)
  have hhand := B_hand_nonneg (p := p)
  have hrel := B_rel_nonneg (p := p)
  unfold C_tr
  linarith

/-- The actual stopped transport mean is bounded by the sum of the three
accepted phase constants times the same actual stopped-count mean. -/
public theorem J_stop_fixedID_mean_le_stoppedCount
    (control0 : TimeControl p) (ids : CompletePublicTable.IDArray p) :
    (∫ z : Source, J_stop rate rewards C_star C_h z
      ∂ReferenceFixedIDSourceSection.fixedIDSourceLaw (p := p) ids) ≤
      C_tr (p := p) *
        (∫ z : Source,
          (ReferenceOriginalCalendarPhysicalTransferCount.actualStoppedPhysicalTransferCount
            rate rewards C_star C_h z : ℝ)
          ∂ReferenceFixedIDSourceSection.fixedIDSourceLaw (p := p) ids) := by
  let ν := ReferenceFixedIDSourceSection.fixedIDSourceLaw (p := p) ids
  have hCInt :=
    ReferenceOriginalStoppedCollectionFixedIDMean.C_totals_integrable_fixedID
      rate rewards C_star C_h control0 ids
  have hHInt := H_cap_integrable_fixedID rate rewards C_star C_h ids
  have hRInt :=
    ReferenceOriginalStoppedReleaseFixedIDMean.stoppedReleaseSignedCharge_integrable_fixedID
      rate rewards C_star C_h ids
  have hfun : (J_stop rate rewards C_star C_h) = fun z : Source =>
      ReferenceOriginalStoppedCollectionFixedIDMean.C_cap rate rewards C_star C_h z +
        H_cap rate rewards C_star C_h z +
        ReferenceOriginalStoppedReleaseFixedIDMean.stoppedReleaseSignedCharge
          rate rewards C_star C_h z := by
    funext z
    exact J_stop_eq_components rate rewards C_star C_h z
  have hint :
      (∫ z : Source, J_stop rate rewards C_star C_h z ∂ν) =
        (∫ z : Source,
          ReferenceOriginalStoppedCollectionFixedIDMean.C_cap rate rewards C_star C_h z ∂ν) +
        (∫ z : Source, H_cap rate rewards C_star C_h z ∂ν) +
        (∫ z : Source,
          ReferenceOriginalStoppedReleaseFixedIDMean.stoppedReleaseSignedCharge
            rate rewards C_star C_h z ∂ν) := by
    calc
      _ = ∫ z : Source,
          ReferenceOriginalStoppedCollectionFixedIDMean.C_cap rate rewards C_star C_h z +
            H_cap rate rewards C_star C_h z +
            ReferenceOriginalStoppedReleaseFixedIDMean.stoppedReleaseSignedCharge
              rate rewards C_star C_h z ∂ν := by
        exact congrArg (fun f : Source → ℝ => ∫ z : Source, f z ∂ν) hfun
      _ = (∫ z : Source,
          ReferenceOriginalStoppedCollectionFixedIDMean.C_cap rate rewards C_star C_h z +
            H_cap rate rewards C_star C_h z ∂ν) +
          ∫ z : Source,
            ReferenceOriginalStoppedReleaseFixedIDMean.stoppedReleaseSignedCharge
              rate rewards C_star C_h z ∂ν := by
        exact integral_add (hCInt.2.add hHInt) hRInt
      _ = _ := by
        rw [integral_add hCInt.2 hHInt]
  have hchain :=
    ReferenceOriginalStoppedCollectionFixedIDMean.fixedID_collection_mean_chain
      rate rewards C_star C_h control0 ids
  have hCbound := hchain.1.trans hchain.2.1
  have hHbound := H_cap_fixedID_mean_le_stoppedCount
    rate rewards C_star C_h control0 ids
  have hRbound :=
    ReferenceOriginalStoppedReleaseFixedIDMean.stoppedReleaseSignedCharge_fixedID_mean_le_stoppedCount
      rate rewards C_star C_h control0 ids
  calc
    _ = _ := hint
    _ ≤ ReferenceOriginalKthCollectionConditionalWaitingCost.B_col (p := p) *
          (∫ z : Source,
            (ReferenceOriginalCalendarPhysicalTransferCount.actualStoppedPhysicalTransferCount
              rate rewards C_star C_h z : ℝ) ∂ν) +
        ReferenceOriginalFixedInstallationHandoverWaitingCost.B_hand (p := p) *
          (∫ z : Source,
            (ReferenceOriginalCalendarPhysicalTransferCount.actualStoppedPhysicalTransferCount
              rate rewards C_star C_h z : ℝ) ∂ν) +
        ReferenceOriginalKthReleaseSignedCost.B_rel (p := p) *
          (∫ z : Source,
            (ReferenceOriginalCalendarPhysicalTransferCount.actualStoppedPhysicalTransferCount
              rate rewards C_star C_h z : ℝ) ∂ν) :=
      add_le_add (add_le_add hCbound hHbound) hRbound
    _ = C_tr (p := p) *
          (∫ z : Source,
            (ReferenceOriginalCalendarPhysicalTransferCount.actualStoppedPhysicalTransferCount
              rate rewards C_star C_h z : ℝ) ∂ν) := by
      unfold C_tr
      ring

/-- The literal total original stopped transport charge has the manuscript's
fixed-ID envelope with the exact source constants and actual stopped count. -/
public theorem J_stop_fixedID_mean_le
    (control0 : TimeControl p) (ids : CompletePublicTable.IDArray p) :
    (∫ z : Source, J_stop rate rewards C_star C_h z
      ∂ReferenceFixedIDSourceSection.fixedIDSourceLaw (p := p) ids) ≤
      C_tr (p := p) * ((4 * (p.m : ℝ) + 128) * rate.eta.val * (p.T : ℝ) + 2) := by
  have hbase := J_stop_fixedID_mean_le_stoppedCount
    rate rewards C_star C_h control0 ids
  have hcount :=
    ReferenceOriginalStoppedCollectionFixedIDMean.actualStoppedPhysicalTransferCount_fixedID_mean_le_source_bound
      rate rewards C_star C_h control0 ids
  calc
    _ ≤ C_tr (p := p) *
        (∫ z : Source,
          (ReferenceOriginalCalendarPhysicalTransferCount.actualStoppedPhysicalTransferCount
            rate rewards C_star C_h z : ℝ)
          ∂ReferenceFixedIDSourceSection.fixedIDSourceLaw (p := p) ids) := hbase
    _ ≤ C_tr (p := p) *
        ((4 * (p.m : ℝ) + 128) * rate.eta.val * (p.T : ℝ) + 2) :=
      mul_le_mul_of_nonneg_left hcount (C_tr_nonneg (p := p))

end Bandits.Support.ReferenceOriginalStoppedTransportFixedIDMean

end
