/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveWholeSourceReadout

import Mathlib.Tactic

/-!
# Original-source estimates on one nonempty first-live branch

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:140-188,245-318`,
`sources/zip4/manuscript/06_interruptions.tex:391-408,425-426`,
`sources/zip4/manuscript/07_public_setup.tex:145-164`, and
`sources/zip4/manuscript/08_main_theorem.tex:78-104`.

These results transport the existing unnormalized continuing source measure
to the original-source event where the whole-calendar strict-past queue has
not overflowed. They preserve the literal readouts and the canonical rate
remainder. They do not assemble the other calendar branches or bound that
remainder by the manuscript's global rate sum.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators Classical ENNReal

namespace Bandits.Support.ReferenceFirstLiveOriginalBranchEstimates

variable {p : ReferenceFirstLiveCalendarPrefixReadout.Parameters}
variable (rate : ReferenceFirstLiveCalendarPrefixReadout.RateInput p)
  (rewards : ReferenceFirstLiveCalendarPrefixReadout.RewardTable p)
  (C_star C_h : ℝ) (q : Fin (ConstructorDimensions.M p)) (t : Fin p.T)
  (s : ℕ) (hs : s ≤ t.val)
  (control0 : ReferenceFirstLiveBranchIntegralTransport.TimeControl p)

local notation "S" => BootstrapPrivateRoundStreams.SourceInput p
local notation "Z" => ReferenceTotalSourceDisintegration.SourceStratum rate rewards C_star C_h t
  (ReferenceFirstLiveRecordingSourceCylinder.stratumIndex q t s hs)
local notation "Zplus" => ReferenceFirstLiveRecordingSourceCylinder.SourcePlus
  rate rewards C_star C_h q t s hs control0
local notation "muPlus" => ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure
  rate rewards C_star C_h q t s hs control0
local notation "mu0" => BootstrapPrivateRoundStreams.sourceInputLaw p
local notation "E" => Bandits.Support.ReferenceFirstLiveBranchIntegralTransport.originalBranchEvent rate rewards C_star C_h q t s hs control0
local notation "G" => Bandits.Support.ReferenceFirstLiveAllArmPrefixAdaptation.strictPastOverflowFalseSet rate rewards C_star C_h q t s hs control0
local notation "L" => fun omega : S => ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells
  rate rewards C_star C_h omega
local notation "start" => fun omega : S =>
  ReferenceCompletePhysicalHistory.physicalStart rate omega rewards C_star C_h
local notation "Q" => ReferenceFirstLaunchNumericalCell.queueParameters rate
local notation "n" => t.val - s
local notation "H" => ((fun omega : S =>
  RecordedQueueRun.RunState.overflow (RecordedQueueRun.run Q
    (List.take (t.val - start omega) (L omega))) = false) : Set S)
local notation "V" => Bandits.Support.ReferenceFirstLiveCalendarPrefixReadout.firstWindowPotentialAt rate rewards C_star C_h
local notation "Wb" => Bandits.Support.ReferenceFirstLiveCalendarPrefixReadout.firstWindowWeightedBacklogAt rate rewards C_star C_h
local notation "b" => Bandits.Support.ReferenceFirstLiveCalendarPrefixReadout.firstWindowBacklogAt rate rewards C_star C_h
local notation "beta" => ReferenceFirstLiveSourceSavedMoments.beta rate
local notation "armExp" => fun (j : Fin p.K) (v : ℕ) (omega : S) =>
  Real.exp (beta * b j v omega)

/-- On this same source subtype, the literal strict-past event is exactly the
whole-source overflow-false test from Bandits.Support.ReferenceFirstLiveWholeSourceReadout. -/
theorem strictPastOverflowFalse_iff_wholeSource (z : Zplus) :
    G z ↔ H z.val.val := by
  have hWhole := Bandits.Support.ReferenceFirstLiveWholeSourceReadout.actualOverflowFalseSet_iff rate rewards C_star C_h q t s hs z.val
  change (RecordedQueueRun.run Q
      ((ReferenceFirstLiveSourceCellReadout.cells rate rewards C_star C_h q t s hs control0 z).take n)).overflow = false ↔
    (RecordedQueueRun.run Q
      ((L (z.val.val)).take
        (t.val - start (z.val.val)))).overflow = false
  rw [← Bandits.Support.ReferenceFirstLiveBranchIntegralTransport.actualSourceCells_eq_sourceCells rate rewards C_star C_h q t s hs control0 z]
  exact hWhole

private theorem forgetBranch_mem_originalBranch (z : Zplus) :
    Bandits.Support.ReferenceFirstLiveBranchIntegralTransport.forgetBranch rate rewards C_star C_h q t s hs control0 z ∈ E := by
  change z.val.val ∈ Subtype.val ''
    Bandits.Support.ReferenceFirstLiveBranchIntegralTransport.continuingSourceBranchSet rate rewards C_star C_h q t s hs control0
  exact ⟨z.val, z.property, rfl⟩

/-- The whole-source branch event pulls back to A's strict-past set. -/
theorem preimage_originalBranch_intersection_eq_strictPast :
    Bandits.Support.ReferenceFirstLiveBranchIntegralTransport.forgetBranch rate rewards C_star C_h q t s hs control0 ⁻¹' (E ∩ H) = G := by
  ext z
  constructor
  · intro hz
    have hz' : Bandits.Support.ReferenceFirstLiveBranchIntegralTransport.forgetBranch rate rewards C_star C_h q t s hs control0 z ∈ E ∩ H := by
      simpa only [Set.mem_preimage] using hz
    exact (strictPastOverflowFalse_iff_wholeSource rate rewards C_star C_h q t s hs control0 z).2 hz'.2
  · intro hz
    apply Set.mem_preimage.mpr
    exact ⟨forgetBranch_mem_originalBranch rate rewards C_star C_h q t s hs control0 z,
      (strictPastOverflowFalse_iff_wholeSource rate rewards C_star C_h q t s hs control0 z).1 hz⟩

/-- The image of A's strict-past set is precisely the original-source
intersection; this uses the same points and source coordinates as E. -/
theorem image_strictPast_eq_originalBranch_intersection :
    Bandits.Support.ReferenceFirstLiveBranchIntegralTransport.forgetBranch rate rewards C_star C_h q t s hs control0 '' G = E ∩ H := by
  ext omega
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨forgetBranch_mem_originalBranch rate rewards C_star C_h q t s hs control0 z,
      (strictPastOverflowFalse_iff_wholeSource rate rewards C_star C_h q t s hs control0 z).1 hz⟩
  · rintro ⟨hE, hH⟩
    rcases hE with ⟨z, hz, rfl⟩
    let zplus : Zplus := ⟨z, hz⟩
    refine ⟨zplus, ?_, rfl⟩
    exact (strictPastOverflowFalse_iff_wholeSource rate rewards C_star C_h q t s hs control0 zplus).2 hH

/-- The restricted event is Borel by its image representation and the public
ambient measurability of A's strict-past set. -/
theorem measurableSet_originalBranch_intersection : MeasurableSet (E ∩ H) := by
  rw [← image_strictPast_eq_originalBranch_intersection rate rewards C_star C_h q t s hs control0]
  exact (Bandits.Support.ReferenceFirstLiveBranchIntegralTransport.measurableEmbedding_forgetBranch rate rewards C_star C_h q t s hs control0).measurableSet_image.mpr
    (Bandits.Support.ReferenceFirstLiveAllArmPrefixAdaptation.measurableSet_strictPastOverflowFalseSet_ambient rate rewards C_star C_h q t s hs control0)

/-- The unnormalized branch mass is the original source mass of E intersected
with the whole-source strict-past event. -/
theorem branchSourceMeasure_strictPast_mass :
    muPlus G = mu0 (E ∩ H) := by
  let hEmbed := Bandits.Support.ReferenceFirstLiveBranchIntegralTransport.measurableEmbedding_forgetBranch rate rewards C_star C_h q t s hs control0
  have hInter : MeasurableSet (E ∩ H) :=
    measurableSet_originalBranch_intersection rate rewards C_star C_h q t s hs control0
  calc
    muPlus G = muPlus (Bandits.Support.ReferenceFirstLiveBranchIntegralTransport.forgetBranch rate rewards C_star C_h q t s hs control0 ⁻¹' (E ∩ H)) := by
      rw [preimage_originalBranch_intersection_eq_strictPast rate rewards C_star C_h q t s hs control0]
    _ = (Measure.map (Bandits.Support.ReferenceFirstLiveBranchIntegralTransport.forgetBranch rate rewards C_star C_h q t s hs control0) muPlus) (E ∩ H) := by
      rw [← Measure.map_apply hEmbed.measurable hInter]
    _ = (Measure.restrict mu0 E) (E ∩ H) := by
      rw [Bandits.Support.ReferenceFirstLiveBranchIntegralTransport.branchSourceMeasure_map_original rate rewards C_star C_h q t s hs control0]
    _ = mu0 (E ∩ H) := by
      rw [Measure.restrict_apply' (Bandits.Support.ReferenceFirstLiveBranchIntegralTransport.measurableSet_originalBranchEvent rate rewards C_star C_h q t s hs control0)]
      congr 1
      ext omega
      change (E omega ∧ H omega) ∧ E omega ↔ E omega ∧ H omega
      constructor
      · rintro ⟨⟨hE, hH⟩, _⟩
        exact ⟨hE, hH⟩
      · rintro ⟨hE, hH⟩
        exact ⟨⟨hE, hH⟩, hE⟩

/-- Real mass form of the same unnormalized identity, including zero mass. -/
theorem branchSourceMeasure_strictPast_mass_real :
    (ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure
      rate rewards C_star C_h q t s hs control0).real G =
      (BootstrapPrivateRoundStreams.sourceInputLaw p).real (E ∩ H) := by
  change (muPlus G).toReal = (mu0 (E ∩ H)).toReal
  rw [branchSourceMeasure_strictPast_mass rate rewards C_star C_h q t s hs control0]

/-- Original-source integrability of the strict-past potential. -/
theorem integrableOn_originalPotentialBefore : IntegrableOn (V t.val) E mu0 := by
  exact (Bandits.Support.ReferenceFirstLiveCalendarPrefixReadout.integrable_firstWindowPotentialAt rate rewards C_star C_h t.val).integrableOn

/-- Original-source integrability of the potential after the current update. -/
theorem integrableOn_originalPotentialAfter : IntegrableOn (V (t.val + 1)) E mu0 := by
  exact (Bandits.Support.ReferenceFirstLiveCalendarPrefixReadout.integrable_firstWindowPotentialAt rate rewards C_star C_h (t.val + 1)).integrableOn

/-- Original-source integrability of the one-step potential difference. -/
theorem integrableOn_originalPotentialDifference :
    IntegrableOn (fun omega => V (t.val + 1) omega - V t.val omega) E mu0 := by
  exact (integrableOn_originalPotentialAfter rate rewards C_star C_h q t s hs control0).sub
    (integrableOn_originalPotentialBefore rate rewards C_star C_h q t s hs control0)

/-- Original-source integrability of the weighted backlog on E intersected
with the strict-past no-overflow event. -/
theorem integrableOn_originalGoodWeightedBacklog :
    IntegrableOn (Wb t.val) (E ∩ H) mu0 := by
  exact (Bandits.Support.ReferenceFirstLiveCalendarPrefixReadout.integrable_firstWindowWeightedBacklogAt rate rewards C_star C_h t.val).integrableOn.mono_set
    (Set.inter_subset_left)

/-- Original-source integrability of each strict-past exponential backlog. -/
theorem integrableOn_originalExpBacklogBefore (j : Fin p.K) :
    IntegrableOn (armExp j t.val) E mu0 := by
  exact (Bandits.Support.ReferenceFirstLiveCalendarPrefixReadout.integrable_firstWindowExpBacklogAt rate rewards C_star C_h j t.val).integrableOn

/-- Original-source integrability of each exponential backlog after the
current update. -/
theorem integrableOn_originalExpBacklogAfter (j : Fin p.K) :
    IntegrableOn (armExp j (t.val + 1)) E mu0 := by
  exact (Bandits.Support.ReferenceFirstLiveCalendarPrefixReadout.integrable_firstWindowExpBacklogAt rate rewards C_star C_h j (t.val + 1)).integrableOn

/-- The original-source before-potential integral is the inherited energy
readout on the same unnormalized SourcePlus measure. -/
theorem integral_originalPotentialBefore :
    (∫ omega in E, V t.val omega ∂mu0) =
      ∫ z : Zplus, ReferenceFirstLiveQueueEnergyEnvelope.potentialBefore
        rate rewards C_star C_h q t s hs control0 z ∂muPlus := by
  calc
    _ = ∫ z : Zplus, V t.val (Bandits.Support.ReferenceFirstLiveBranchIntegralTransport.forgetBranch rate rewards C_star C_h q t s hs control0 z) ∂muPlus :=
      (Bandits.Support.ReferenceFirstLiveBranchIntegralTransport.integral_originalBranch rate rewards C_star C_h q t s hs control0 _).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with z
      simpa only [Bandits.Support.ReferenceFirstLiveBranchIntegralTransport.forgetBranch] using
        Bandits.Support.ReferenceFirstLiveCalendarPrefixReadout.firstWindowPotentialAt_before
          rate rewards C_star C_h q t s hs control0 z

/-- The original-source after-potential integral is the inherited energy
readout with the first current-cell update retained. -/
theorem integral_originalPotentialAfter :
    (∫ omega in E, V (t.val + 1) omega ∂mu0) =
      ∫ z : Zplus, ReferenceFirstLiveQueueEnergyEnvelope.potentialAfter
        rate rewards C_star C_h q t s hs control0 z ∂muPlus := by
  calc
    _ = ∫ z : Zplus, V (t.val + 1) (Bandits.Support.ReferenceFirstLiveBranchIntegralTransport.forgetBranch rate rewards C_star C_h q t s hs control0 z) ∂muPlus :=
      (Bandits.Support.ReferenceFirstLiveBranchIntegralTransport.integral_originalBranch rate rewards C_star C_h q t s hs control0 _).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with z
      simpa only [Bandits.Support.ReferenceFirstLiveBranchIntegralTransport.forgetBranch] using
        Bandits.Support.ReferenceFirstLiveCalendarPrefixReadout.firstWindowPotentialAt_after
          rate rewards C_star C_h q t s hs control0 z

/-- The original-source one-step potential integral is the same inherited
energy difference, without changing or normalizing its branch measure. -/
theorem integral_originalPotentialDifference :
    (∫ omega in E, V (t.val + 1) omega - V t.val omega ∂mu0) =
      ∫ z : Zplus,
        ReferenceFirstLiveQueueEnergyEnvelope.potentialAfter
            rate rewards C_star C_h q t s hs control0 z -
          ReferenceFirstLiveQueueEnergyEnvelope.potentialBefore
            rate rewards C_star C_h q t s hs control0 z ∂muPlus := by
  calc
    _ = ∫ z : Zplus,
        V (t.val + 1) (Bandits.Support.ReferenceFirstLiveBranchIntegralTransport.forgetBranch rate rewards C_star C_h q t s hs control0 z) -
          V t.val (Bandits.Support.ReferenceFirstLiveBranchIntegralTransport.forgetBranch rate rewards C_star C_h q t s hs control0 z) ∂muPlus :=
      (Bandits.Support.ReferenceFirstLiveBranchIntegralTransport.integral_originalBranch rate rewards C_star C_h q t s hs control0 _).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with z
      simp only [Bandits.Support.ReferenceFirstLiveBranchIntegralTransport.forgetBranch]
      rw [Bandits.Support.ReferenceFirstLiveCalendarPrefixReadout.firstWindowPotentialAt_after rate rewards C_star C_h q t s hs control0 z,
        Bandits.Support.ReferenceFirstLiveCalendarPrefixReadout.firstWindowPotentialAt_before rate rewards C_star C_h q t s hs control0 z]

/-- The original-source strict-past weighted backlog integral is exactly A's
indicator readout on the same SourcePlus measure. -/
theorem integral_originalGoodWeightedBacklog :
    (∫ omega in E ∩ H, Wb t.val omega ∂mu0) =
      ∫ z : Zplus, Set.indicator G
        (ReferenceFirstLiveQueueEnergyEnvelope.weightedBacklogBefore
          rate rewards C_star C_h q t s hs control0) z ∂muPlus := by
  have hInter : MeasurableSet (E ∩ H) :=
    measurableSet_originalBranch_intersection rate rewards C_star C_h q t s hs control0
  have hDomain : E ∩ (E ∩ H) = E ∩ H := by
    ext omega
    change E omega ∧ (E omega ∧ H omega) ↔ E omega ∧ H omega
    constructor
    · rintro ⟨hE, hEH⟩
      exact hEH
    · rintro ⟨hE, hH⟩
      exact ⟨hE, ⟨hE, hH⟩⟩
  have hSetIntegral :
      (∫ omega in E, (E ∩ H).indicator (Wb t.val) omega ∂mu0) =
        ∫ omega in E ∩ H, Wb t.val omega ∂mu0 := by
    calc
      _ = ∫ omega in E ∩ (E ∩ H), Wb t.val omega ∂mu0 := setIntegral_indicator hInter
      _ = _ := by rw [hDomain]
  calc
    _ = ∫ omega in E, (E ∩ H).indicator (Wb t.val) omega ∂mu0 := hSetIntegral.symm
    _ = ∫ z : Zplus,
        (E ∩ H).indicator (Wb t.val)
          (Bandits.Support.ReferenceFirstLiveBranchIntegralTransport.forgetBranch rate rewards C_star C_h q t s hs control0 z) ∂muPlus :=
      (Bandits.Support.ReferenceFirstLiveBranchIntegralTransport.integral_originalBranch rate rewards C_star C_h q t s hs control0 _).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with z
      have hzE := forgetBranch_mem_originalBranch rate rewards C_star C_h q t s hs control0 z
      by_cases hz : z ∈ G
      · have hzH := (strictPastOverflowFalse_iff_wholeSource rate rewards C_star C_h q t s hs control0 z).1 hz
        have hmem : Bandits.Support.ReferenceFirstLiveBranchIntegralTransport.forgetBranch rate rewards C_star C_h q t s hs control0 z ∈ E ∩ H :=
          ⟨hzE, hzH⟩
        rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hz]
        simpa only [Bandits.Support.ReferenceFirstLiveBranchIntegralTransport.forgetBranch] using
          Bandits.Support.ReferenceFirstLiveCalendarPrefixReadout.firstWindowWeightedBacklogAt_before
            rate rewards C_star C_h q t s hs control0 z
      · have hzH : ¬ H (Bandits.Support.ReferenceFirstLiveBranchIntegralTransport.forgetBranch rate rewards C_star C_h q t s hs control0 z) := by
          intro h
          exact hz ((strictPastOverflowFalse_iff_wholeSource rate rewards C_star C_h q t s hs control0 z).2 h)
        have hnot : Bandits.Support.ReferenceFirstLiveBranchIntegralTransport.forgetBranch rate rewards C_star C_h q t s hs control0 z ∉ E ∩ H := by
          change ¬ (E (Bandits.Support.ReferenceFirstLiveBranchIntegralTransport.forgetBranch rate rewards C_star C_h q t s hs control0 z) ∧
            H (Bandits.Support.ReferenceFirstLiveBranchIntegralTransport.forgetBranch rate rewards C_star C_h q t s hs control0 z))
          exact fun h => hzH h.2
        rw [Set.indicator_of_notMem hnot, Set.indicator_of_notMem hz]

/-- The original-source before exponential integral is the inherited
per-arm queue exponential readout. -/
theorem integral_originalExpBacklogBefore (j : Fin p.K) :
    (∫ omega in E, armExp j t.val omega ∂mu0) =
      ∫ z : Zplus, Bandits.Support.ReferenceFirstLiveConditionalExponentialQueue.expBacklogBefore rate rewards C_star C_h q t s hs control0 j z ∂muPlus := by
  calc
    _ = ∫ z : Zplus, armExp j t.val
        (Bandits.Support.ReferenceFirstLiveBranchIntegralTransport.forgetBranch rate rewards C_star C_h q t s hs control0 z) ∂muPlus :=
      (Bandits.Support.ReferenceFirstLiveBranchIntegralTransport.integral_originalBranch rate rewards C_star C_h q t s hs control0 _).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with z
      simp only [Bandits.Support.ReferenceFirstLiveBranchIntegralTransport.forgetBranch]
      rw [Bandits.Support.ReferenceFirstLiveCalendarPrefixReadout.firstWindowBacklogAt_before
        rate rewards C_star C_h q t s hs control0 z j,
        Bandits.Support.ReferenceFirstLiveConditionalExponentialQueue.expBacklogBefore]

/-- The original-source after exponential integral is the inherited per-arm
queue exponential readout, including the current update. -/
theorem integral_originalExpBacklogAfter (j : Fin p.K) :
    (∫ omega in E, armExp j (t.val + 1) omega ∂mu0) =
      ∫ z : Zplus, Bandits.Support.ReferenceFirstLiveConditionalExponentialQueue.expBacklogAfter rate rewards C_star C_h q t s hs control0 j z ∂muPlus := by
  calc
    _ = ∫ z : Zplus, armExp j (t.val + 1)
        (Bandits.Support.ReferenceFirstLiveBranchIntegralTransport.forgetBranch rate rewards C_star C_h q t s hs control0 z) ∂muPlus :=
      (Bandits.Support.ReferenceFirstLiveBranchIntegralTransport.integral_originalBranch rate rewards C_star C_h q t s hs control0 _).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with z
      simp only [Bandits.Support.ReferenceFirstLiveBranchIntegralTransport.forgetBranch]
      rw [Bandits.Support.ReferenceFirstLiveCalendarPrefixReadout.firstWindowBacklogAt_after
        rate rewards C_star C_h q t s hs control0 z j,
        Bandits.Support.ReferenceFirstLiveConditionalExponentialQueue.expBacklogAfter]

/-- The one-step potential drift transported to the original source event,
retaining D's sharp canonical marker-rate integral term. -/
theorem potential_drift_integral_originalBranch_rate_sum :
    (∫ omega in E, V (t.val + 1) omega - V t.val omega ∂mu0) ≤
      -(11 / 2 : ℝ) * (∫ omega in E ∩ H, Wb t.val omega ∂mu0) +
        ∫ z : Zplus, Set.indicator G
          (Bandits.Support.ReferenceFirstLiveConditionalWeightedDrift.markerRateWeightSum rate rewards C_star C_h q t s hs control0) z ∂muPlus +
        (33 / 2 : ℝ) * (p.m : ℝ) * (BootstrapPrivateRoundStreams.sourceInputLaw p).real (E ∩ H) := by
  let wplus := ReferenceFirstLiveQueueEnergyEnvelope.weightedBacklogBefore
    rate rewards C_star C_h q t s hs control0
  let rplus := Bandits.Support.ReferenceFirstLiveConditionalWeightedDrift.markerRateWeightSum rate rewards C_star C_h q t s hs control0
  let c : ℝ := (33 / 2 : ℝ) * (p.m : ℝ)
  have hG : MeasurableSet G :=
    Bandits.Support.ReferenceFirstLiveAllArmPrefixAdaptation.measurableSet_strictPastOverflowFalseSet_ambient rate rewards C_star C_h q t s hs control0
  have hw : Integrable wplus muPlus :=
    ReferenceFirstLiveQueueEnergyEnvelope.integrable_weightedBacklogBefore
      rate rewards C_star C_h q t s hs control0
  have hr : Integrable rplus muPlus :=
    Bandits.Support.ReferenceFirstLiveConditionalWeightedDrift.integrable_markerRateWeightSum rate rewards C_star C_h q t s hs control0
  have hwG : Integrable (Set.indicator G wplus) muPlus := hw.indicator hG
  have hrG : Integrable (Set.indicator G rplus) muPlus := hr.indicator hG
  have hcG : Integrable (Set.indicator G (fun _ : Zplus => c)) muPlus :=
    (integrable_const c).indicator hG
  have hpoint :
      (fun z : Zplus => Set.indicator G (fun x =>
        -(11 / 2 : ℝ) * wplus x + rplus x + c) z) =
      (fun z : Zplus => (-(11 / 2 : ℝ) * Set.indicator G wplus z +
        Set.indicator G rplus z) + Set.indicator G (fun _ : Zplus => c) z) := by
    funext z
    by_cases hz : z ∈ G <;> simp [Set.indicator, hz]
  have hsplit :
      (∫ z : Zplus, Set.indicator G (fun x =>
        -(11 / 2 : ℝ) * wplus x + rplus x + c) z ∂muPlus) =
        -(11 / 2 : ℝ) * (∫ z : Zplus, Set.indicator G wplus z ∂muPlus) +
          (∫ z : Zplus, Set.indicator G rplus z ∂muPlus) +
          (∫ z : Zplus, Set.indicator G (fun _ : Zplus => c) z ∂muPlus) := by
    calc
      _ = ∫ z : Zplus,
          (-(11 / 2 : ℝ) * Set.indicator G wplus z + Set.indicator G rplus z) +
            Set.indicator G (fun _ : Zplus => c) z ∂muPlus := by
        apply integral_congr_ae
        filter_upwards [] with z
        exact congrFun hpoint z
      _ = _ := by
        calc
          _ = (∫ z : Zplus,
              -(11 / 2 : ℝ) * Set.indicator G wplus z + Set.indicator G rplus z ∂muPlus) +
              ∫ z : Zplus, Set.indicator G (fun _ : Zplus => c) z ∂muPlus :=
            integral_add ((hwG.const_mul (-(11 / 2 : ℝ))).add hrG) hcG
          _ = _ := by
            rw [integral_add (hwG.const_mul (-(11 / 2 : ℝ))) hrG, integral_const_mul]
  have hrateDrift := Bandits.Support.ReferenceFirstLiveConditionalWeightedDrift.potential_drift_integral_rate_sum
    rate rewards C_star C_h q t s hs control0
  calc
    _ = ∫ z : Zplus,
        ReferenceFirstLiveQueueEnergyEnvelope.potentialAfter
            rate rewards C_star C_h q t s hs control0 z -
          ReferenceFirstLiveQueueEnergyEnvelope.potentialBefore
            rate rewards C_star C_h q t s hs control0 z ∂muPlus :=
      integral_originalPotentialDifference rate rewards C_star C_h q t s hs control0
    _ ≤ ∫ z : Zplus, Set.indicator G (fun x =>
        -(11 / 2 : ℝ) * ReferenceFirstLiveQueueEnergyEnvelope.weightedBacklogBefore
          rate rewards C_star C_h q t s hs control0 x +
          Bandits.Support.ReferenceFirstLiveConditionalWeightedDrift.markerRateWeightSum rate rewards C_star C_h q t s hs control0 x +
          (33 / 2 : ℝ) * (p.m : ℝ)) z ∂muPlus := hrateDrift
    _ = _ := by
      rw [hsplit, integral_originalGoodWeightedBacklog rate rewards C_star C_h q t s hs control0,
        integral_indicator_const c hG, smul_eq_mul,
        branchSourceMeasure_strictPast_mass_real rate rewards C_star C_h q t s hs control0]
      simp only [wplus, rplus, c]
      ring

/-- Each per-arm exponential queue step on the original event has the exact
strict-past mass correction, even when that event has zero measure. -/
theorem integral_expBacklogAfter_step_originalBranch (j : Fin p.K) :
    (∫ omega in E, armExp j (t.val + 1) omega ∂mu0) ≤
      (∫ omega in E, armExp j t.val omega ∂mu0) + (BootstrapPrivateRoundStreams.sourceInputLaw p).real (E ∩ H) := by
  rw [integral_originalExpBacklogAfter rate rewards C_star C_h q t s hs control0 j,
    integral_originalExpBacklogBefore rate rewards C_star C_h q t s hs control0 j,
    ← branchSourceMeasure_strictPast_mass_real rate rewards C_star C_h q t s hs control0]
  exact Bandits.Support.ReferenceFirstLiveConditionalExponentialQueue.integral_expBacklogAfter_step rate rewards C_star C_h q t s hs control0 j

end Bandits.Support.ReferenceFirstLiveOriginalBranchEstimates

end
