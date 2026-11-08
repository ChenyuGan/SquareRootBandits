/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveSourcePrefixBranchInvariance

/-!
# Conditional moments of the actual current saved emission

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:142-174,256-264`,
`sources/zip4/manuscript/06_interruptions.tex:391-408`,
`sources/zip4/manuscript/07_public_setup.tex:127-164`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:34-64`.

These are internal results on the original continuing, actually unoccupied
follower source subtype. The measure is the inherited unnormalized comap,
including zero mass. The field is the analysis strict-prefix field. No
identification with a manuscript history, retention mask, overflow event,
successful physical execution, or complete recording law is asserted.

The current real saved emission is restored at the original WHOLE current
control. Its first and square conditional moments then follow from the
existing original-source cell integrals, with every field cell factored
through the literal produced prefix of the remainder.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ContinuousLearningRows
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open scoped Classical

namespace Bandits.Support.ReferenceFirstLiveSourceSavedConditionalMoments

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev RewardTable := ActualInitializationPhysicalStep.GridRewardTable
abbrev TimeControl := ContinuousLearningRows.TimeControl
abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput

local instance sourceInputMeasurableSpace (p : Parameters) : MeasurableSpace (SourceInput p) := by
  change MeasurableSpace (CompletePublicTable.PublishedOutput p ×
    BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

variable {p : Parameters} (rate : RateInput p) (rewards : RewardTable p)
  (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
  (hs : s ≤ t.val) (control0 : TimeControl p)

local notation "Z" => ReferenceTotalSourceDisintegration.SourceStratum rate rewards C_star C_h t
  (ReferenceFirstLiveRecordingSourceCylinder.stratumIndex q t s hs)
local notation "X" => ReferenceFirstLiveRecordingReadoutMeasurability.SourceX
  rate rewards C_star C_h q t s hs control0
local notation "ret" => ReferenceFirstLiveRecordingSourceCylinder.sourceRetained
  rate rewards C_star C_h q t s hs control0
local notation "pre" => ReferenceFirstLiveSourcePrefixBranchInvariance.prefixZ
  rate rewards C_star C_h q t s hs control0
local notation "inp" => ReferenceFirstLiveRecordingSourceBranch.actualCurrentInput
  rate rewards C_star C_h q t s hs control0

variable (i : Fin (p.m - 1))

local notation "Xi" => ReferenceFirstLiveRecordingReadoutMeasurability.XFollower
  rate rewards C_star C_h q t s hs control0 i
local notation "Zi" => ReferenceFirstLiveSourceSavedMoments.SourceFollower
  rate rewards C_star C_h q t s hs control0 i
local notation "μCi" => ReferenceFirstLiveSourceSavedMoments.followerRemainderMeasure
  rate rewards C_star C_h q t s hs control0 i
local notation "μZi" => ReferenceFirstLiveSourceSavedMoments.followerSourceMeasure
  rate rewards C_star C_h q t s hs control0 i
local notation "xof" => ReferenceFirstLiveSourcePrefixBranchInvariance.sourceFollowerRetained
  rate rewards C_star C_h q t s hs control0 i
local notation "prei" => ReferenceFirstLiveSourcePrefixBranchInvariance.prefixZi
  rate rewards C_star C_h q t s hs control0 i
local notation "Fi" => ReferenceFirstLiveSourcePrefixBranchInvariance.sourceFollowerPrefixField
  rate rewards C_star C_h q t s hs control0 i
local notation "xiZ" => ReferenceFirstLiveSourcePrefixBranchInvariance.xiZ
  rate rewards C_star C_h q t s hs control0 i
local notation "vZ" => ReferenceFirstLiveSourcePrefixBranchInvariance.vZ
  rate rewards C_star C_h q t s hs control0 i
local notation "saved" => ReferenceFirstLiveSourceSavedMoments.sourceSaved
  rate rewards C_star C_h q t s hs control0 i

private theorem currentInput_time (x : X) : (inp x).time = t := by
  rw [ReferenceFirstLiveRecordingSourceBranch.actualCurrentInput_eq_retainedIncomingBoundary]
  rfl

private theorem currentInput_selected (x : X) : (inp x).selected = q := by
  rw [ReferenceFirstLiveRecordingSourceBranch.actualCurrentInput_eq_retainedIncomingBoundary]
  exact ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary_selected_eq_q
    rate rewards C_star C_h q t s hs control0 x

private theorem currentInput_rows (x : X) :
    (inp x).rows = (ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.val).1.2 := by
  rw [ReferenceFirstLiveRecordingSourceBranch.actualCurrentInput_eq_retainedIncomingBoundary]
  rfl

private theorem currentInput_rewards (x : X) : (inp x).rewards = rewards := by
  rw [ReferenceFirstLiveRecordingSourceBranch.actualCurrentInput_eq_retainedIncomingBoundary]
  rfl

/-- The retained baseline rows and their produced prefix agree strictly before
the current calendar index. Whole future rows are not equated. -/
theorem source_prefix_past_control (z : Z) (v : Fin p.T) (hv : v.val < t.val) :
    (inp (ret z)).row.2 v = (inp (ret (pre z))).row.2 v := by
  have hq : ActualInitializationPhysicalStep.selectedRowIndex p z.val = q := z.property.1
  rw [RoundInput.row, RoundInput.row, currentInput_rows, currentInput_rows,
    currentInput_selected, currentInput_selected,
    ReferenceFirstLiveSourcePrefixBranchInvariance.splitSource_sourceRetained,
    ReferenceFirstLiveSourcePrefixBranchInvariance.splitSource_sourceRetained_prefix]
  have hne : v ≠ t := by intro h; subst v; exact (Nat.lt_irrefl _ hv)
  simp only [ReferenceFixedTimeSourceControlCoupling.replaceSourceControl,
    ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex,
    hq, Function.update_self, Function.update_of_ne hne]
  have hp := ReferenceSourcePrefixHistoryFiltration.sourcePrefix_control control0 t.val z.val v
  simp only [hq, ite_eq_left hv] at hp
  exact hp.symm

/-- Current-step locality for the actual sparse emission. All alternatives of
the prepared configuration and every logging diagnostic remain in `logEmission`.
The only comparison inputs are the incoming state, selected row index, time,
whole current control, past proposal scalars, and current reward vector. -/
theorem logEmission_eq_of_temporal_inputs
    (left right : RoundInput p rate)
    (hstate : left.state = right.state) (htime : left.time = right.time)
    (hselected : left.selected = right.selected)
    (hcurrent : left.row.2 left.time = right.row.2 right.time)
    (hpast : ∀ v : Fin p.T, v.val < left.time.val →
      (left.row.2 v).1 ContinuousControlSlice.Label.prop =
        (right.row.2 v).1 ContinuousControlSlice.Label.prop)
    (hrewards : left.rewards left.time = right.rewards right.time) :
    ReferenceFollowerBufferProvenance.logEmission i ⟨left, step left, rfl⟩ =
      ReferenceFollowerBufferProvenance.logEmission i ⟨right, step right, rfl⟩ := by
  cases left with
  | mk state rows selected time active rewardsL =>
    cases right with
    | mk stateR rowsR selectedR timeR activeR rewardsR =>
      dsimp only at hstate htime hselected
      subst stateR
      subst timeR
      subst selectedR
      have hevidence := ReferenceActiveTemporalAssembly.computedEvidence_eq_of_temporal_reads
        state rows rowsR selected time active rewardsL rewardsR hcurrent hpast hrewards
      have hown := congrArg (fun e : RoundEvidence (p := p) (rate := rate) => e.ownEntries)
        hevidence
      have hconfiguration := congrArg Prod.snd
        (ReferenceActiveTemporalCausality.prepare_projections_eq_of_current
          i (state.activations i) (active i) (state.followers i) hcurrent)
      have hlog : ∀ own,
          ReferencePrelaunchFollower.logAt i (rows selected) (state.activations i) time own =
            ReferencePrelaunchFollower.logAt i (rowsR selected) (state.activations i) time own := by
        intro own
        unfold ReferencePrelaunchFollower.logAt ReferencePrelaunchFollower.loggingRound
        change (rows selected).2 time = (rowsR selected).2 time at hcurrent
        rw [hcurrent]
      change (step (RoundInput.mk state rows selected time active rewardsL)).ownEntries =
        (step (RoundInput.mk state rowsR selected time activeR rewardsR)).ownEntries at hown
      change ((prepare (RoundInput.mk state rows selected time active rewardsL)).followers.followers i).configuration =
        ((prepare (RoundInput.mk state rowsR selected time activeR rewardsR)).followers.followers i).configuration
          at hconfiguration
      unfold ReferenceFollowerBufferProvenance.logEmission
      dsimp only
      change ((step (RoundInput.mk state rows selected time active rewardsL)).preparation.followers.followers i).configuration =
        ((step (RoundInput.mk state rowsR selected time activeR rewardsR)).preparation.followers.followers i).configuration
          at hconfiguration
      rw [hconfiguration]
      cases ((step (RoundInput.mk state rowsR selected time activeR rewardsR)).preparation.followers.followers i).configuration with
      | dagger => rfl
      | ordinary follower memory =>
        by_cases hu : follower.status = .unoccupied
        · simp only [hu, dite_true]
          rw [hown]
          exact hlog _
        · simp only [hu, dite_false]

/-- Replacing the current controls by the SAME whole value preserves the
comparison inputs needed by the actual logging operation. The past-control
and reward inputs are overt and are supplied from the actual prefix below. -/
theorem logEmission_atControl_eq_of_temporal_inputs
    (left right : RoundInput p rate)
    (hstate : left.state = right.state) (htime : left.time = right.time)
    (hselected : left.selected = right.selected)
    (hpast : ∀ v : Fin p.T, v.val < left.time.val →
      (left.row.2 v).1 ContinuousControlSlice.Label.prop =
        (right.row.2 v).1 ContinuousControlSlice.Label.prop)
    (hrewards : left.rewards left.time = right.rewards right.time)
    (u : TimeControl p) :
    ReferenceFollowerBufferProvenance.logEmission i
        ⟨ReferenceContinuingLiveSlicePreparation.inputAtControl left u,
          step (ReferenceContinuingLiveSlicePreparation.inputAtControl left u), rfl⟩ =
      ReferenceFollowerBufferProvenance.logEmission i
        ⟨ReferenceContinuingLiveSlicePreparation.inputAtControl right u,
          step (ReferenceContinuingLiveSlicePreparation.inputAtControl right u), rfl⟩ := by
  apply logEmission_eq_of_temporal_inputs rate i
    (ReferenceContinuingLiveSlicePreparation.inputAtControl left u)
    (ReferenceContinuingLiveSlicePreparation.inputAtControl right u)
  · exact hstate
  · exact htime
  · exact hselected
  · simp only [ReferenceContinuingLiveSlicePreparation.inputAtControl_time,
      ReferenceContinuingLiveSlicePreparation.inputAtControl_row,
      ReferenceContinuingLiveSlicePreparation.rowAtControl_time]
  · intro v hv
    change v.val < left.time.val at hv
    have hleft : v ≠ left.time := by
      intro heq
      rw [heq] at hv
      exact (Nat.lt_irrefl _ hv)
    have hright : v ≠ right.time := by rwa [← htime]
    rw [ReferenceContinuingLiveSlicePreparation.inputAtControl_row,
      ReferenceContinuingLiveSlicePreparation.inputAtControl_row,
      ReferenceContinuingLiveSlicePreparation.rowAtControl_other_time _ _ _ hleft,
      ReferenceContinuingLiveSlicePreparation.rowAtControl_other_time _ _ _ hright]
    exact hpast v hv
  · exact hrewards

/-- At the SAME arbitrary whole current control, prefixing preserves the
actual current emission. This comparison does not identify future runs. -/
theorem source_prefix_logEmission (z : Z) (u : TimeControl p) :
    ReferenceFollowerBufferProvenance.logEmission i
        (ReferenceFirstLiveRecordingReadoutMeasurability.sourceRecordAtControl (ret z) u) =
      ReferenceFollowerBufferProvenance.logEmission i
        (ReferenceFirstLiveRecordingReadoutMeasurability.sourceRecordAtControl (ret (pre z)) u) := by
  have hstate := ReferenceFirstLiveSourcePrefixBranchInvariance.source_prefix_incoming
    rate rewards C_star C_h q t s hs control0 z
  have htime := (currentInput_time rate rewards C_star C_h q t s hs control0 (ret z)).trans
    (currentInput_time rate rewards C_star C_h q t s hs control0 (ret (pre z))).symm
  have hselected := (currentInput_selected rate rewards C_star C_h q t s hs control0 (ret z)).trans
    (currentInput_selected rate rewards C_star C_h q t s hs control0 (ret (pre z))).symm
  have hpast : ∀ v : Fin p.T, v.val < (inp (ret z)).time.val →
      ((inp (ret z)).row.2 v).1 ContinuousControlSlice.Label.prop =
        ((inp (ret (pre z))).row.2 v).1 ContinuousControlSlice.Label.prop := by
    intro v hv
    rw [currentInput_time] at hv
    exact congrArg (fun c : TimeControl p => c.1 ContinuousControlSlice.Label.prop)
      (source_prefix_past_control rate rewards C_star C_h q t s hs control0 z v hv)
  have hrewards : (inp (ret z)).rewards (inp (ret z)).time =
      (inp (ret (pre z))).rewards (inp (ret (pre z))).time := by
    rw [currentInput_rewards, currentInput_rewards, currentInput_time, currentInput_time]
  exact logEmission_atControl_eq_of_temporal_inputs rate i
    (inp (ret z)) (inp (ret (pre z))) hstate htime hselected hpast hrewards u

/-- Restore the actual saved real emission after prefix projection, using its
existing identity with the original current physical record. -/
theorem sourceSaved_eq_prefix_restored (z : Zi) :
    saved z = ReferenceFirstLiveSourceSavedMoments.f
      rate rewards C_star C_h q t s hs control0 i (xof (prei z))
      (ReferenceFirstLiveRecordingSourceCylinder.originalControl
        rate rewards C_star C_h q t s hs z.val) := by
  rw [ReferenceFirstLiveSourceSavedMoments.sourceSaved_eq_originalCurrentRecord]
  rw [← ReferenceFirstLiveRecordingSourceCylinder.sourceRecordAtControl_eq_original]
  have hpayload := ReferenceFirstLiveSourcePrefixBranchInvariance.selectedBaselinePayloadZ_prefix
    rate rewards C_star C_h q t s hs control0 i z
  change ReferenceFirstLiveSourceSavedMoments.selectedBaselinePayload
      rate rewards C_star C_h q t s hs control0 i (xof (prei z)) =
    ReferenceFirstLiveSourceSavedMoments.selectedBaselinePayload
      rate rewards C_star C_h q t s hs control0 i (xof z) at hpayload
  let u := ReferenceFirstLiveRecordingSourceCylinder.originalControl
    rate rewards C_star C_h q t s hs z.val
  change ReferenceContinuingSavedIncrementMoments.normalizedCurrentSavedContribution
      (ReferenceFirstLiveRecordingReadoutMeasurability.sourceRecordAtControl (ret z.val) u)
      (ReferenceFirstLiveSourceSavedMoments.selectedBaselinePayload
        rate rewards C_star C_h q t s hs control0 i (xof z)) i =
    ReferenceContinuingSavedIncrementMoments.normalizedCurrentSavedContribution
      (ReferenceFirstLiveRecordingReadoutMeasurability.sourceRecordAtControl (ret (pre z.val)) u)
      (ReferenceFirstLiveSourceSavedMoments.selectedBaselinePayload
        rate rewards C_star C_h q t s hs control0 i (xof (prei z))) i
  rw [hpayload]
  unfold ReferenceContinuingSavedIncrementMoments.normalizedCurrentSavedContribution
    ReferenceContinuingRecordingPhysicalReward.actualCurrentSavedContribution
  have htime : (ReferenceFirstLiveRecordingReadoutMeasurability.sourceRecordAtControl
        (ret z.val) u).input.time =
      (ReferenceFirstLiveRecordingReadoutMeasurability.sourceRecordAtControl
        (ret (pre z.val)) u).input.time :=
    (currentInput_time rate rewards C_star C_h q t s hs control0 (ret z.val)).trans
      (currentInput_time rate rewards C_star C_h q t s hs control0 (ret (pre z.val))).symm
  rw [htime, source_prefix_logEmission rate rewards C_star C_h q t s hs control0 i z.val]

/-- The exact analysis field is included in the inherited source Borel space. -/
theorem sourceFollowerPrefixField_le : Fi ≤ (inferInstance : MeasurableSpace Zi) := by
  exact ((ReferenceSourceCurrentControlFreshness.measurable_c_t control0 t).comp
    (measurable_subtype_coe.comp measurable_subtype_coe)).comap_le

/-- Finite trimming is valid without a positive branch-mass assumption. -/
theorem sourceFollowerPrefixField_trim_finite :
    IsFiniteMeasure ((μZi).trim
      (sourceFollowerPrefixField_le rate rewards C_star C_h q t s hs control0 i)) := by
  infer_instance

/-- Strict prefixing erases replacement of the whole current control. All
private arrays, IDs, forward coordinates and other rows stay literal. -/
theorem sourcePrefix_replace_current (source : SourceInput p) (u : TimeControl p) :
    ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t source u) =
      ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val source := by
  apply Prod.ext
  · apply Prod.ext
    · rfl
    · funext j
      by_cases hj : j = ActualInitializationPhysicalStep.selectedRowIndex p source
      · subst j
        simp only [ReferenceSourcePrefixHistoryFiltration.sourcePrefix,
          ReferenceFixedTimeSourceControlCoupling.replaceSourceControl,
          ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex,
          ActualInitializationPhysicalStep.selectedRowIndex, Function.update_self]
        apply Prod.ext
        · rfl
        · funext v
          by_cases hv : v.val < t.val
          · have hne : v ≠ t := by
              intro heq
              subst v
              exact (Nat.lt_irrefl _ hv)
            simp only [hv, ite_true, Function.update_of_ne hne]
          · simp only [hv, ite_false]
      · have hj' : j ≠ PrivateSourceStreams.coordinatorIndex p source.2.1.2 := hj
        simp only [ReferenceSourcePrefixHistoryFiltration.sourcePrefix,
          ReferenceFixedTimeSourceControlCoupling.replaceSourceControl,
          ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex,
          ActualInitializationPhysicalStep.selectedRowIndex, Function.update_of_ne hj']
  · rfl

/-- The produced strict prefix computed solely from the actual remainder at
the fixed baseline. This is a literal source map, not a replacement law. -/
def remainderPrefix (x : X) : SourceInput p :=
  ReferenceSourceCurrentControlFreshness.c_t p control0 t
    (ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.val)

theorem measurable_remainderPrefix :
    Measurable (remainderPrefix rate rewards C_star C_h q t s hs control0) := by
  have hsplit : Measurable (fun x : X =>
      ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.val) :=
    (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).symm.measurable.comp
      (measurable_const.prodMk measurable_subtype_coe)
  exact (ReferenceSourceCurrentControlFreshness.measurable_c_t control0 t).comp hsplit

/-- The remainder prefix is exactly B's produced prefix of the ORIGINAL
source, independently of the original current whole control. -/
theorem remainderPrefix_sourceRetained (z : Z) :
    remainderPrefix rate rewards C_star C_h q t s hs control0 (ret z) = (pre z).val := by
  unfold remainderPrefix
  rw [ReferenceFirstLiveSourcePrefixBranchInvariance.splitSource_sourceRetained,
    ReferenceSourcePhysicalFlagConditionalLaw.c_t_eq_sourcePrefix,
    sourcePrefix_replace_current,
    ReferenceFirstLiveSourcePrefixBranchInvariance.prefixZ_val]

/-- Every measurable cell of Fi is an actual measurable remainder cell.
The witness is the pullback of the source cell by `remainderPrefix`; no cell
identity, current-control independence or product law is supplied as input. -/
theorem prefixField_cell (S : Set Zi) (hS : MeasurableSet[Fi] S) :
    ∃ A : Set X, MeasurableSet A ∧
      {z : Zi | ret z.val ∈ A} = S := by
  obtain ⟨V, hV, hVS⟩ := MeasurableSpace.measurableSet_comap.mp hS
  let A : Set X := (remainderPrefix rate rewards C_star C_h q t s hs control0) ⁻¹' V
  refine ⟨A, hV.preimage
    (measurable_remainderPrefix rate rewards C_star C_h q t s hs control0), ?_⟩
  calc
    {z : Zi | ret z.val ∈ A} =
        (fun z : Zi => ReferenceSourceCurrentControlFreshness.c_t p control0 t z.val.val) ⁻¹' V := by
      ext z
      change remainderPrefix rate rewards C_star C_h q t s hs control0 (ret z.val) ∈ V ↔ _
      rw [remainderPrefix_sourceRetained,
        ReferenceFirstLiveSourcePrefixBranchInvariance.prefixZ_val,
        ← ReferenceSourcePhysicalFlagConditionalLaw.c_t_eq_sourcePrefix]
      rfl
    _ = S := hVS

private theorem measurable_sourceFollowerRetained : Measurable xof :=
  measurable_fst.comp (ReferenceFirstLiveSourceSavedMoments.measurable_followerSourceSplit
    rate rewards C_star C_h q t s hs control0 i)

/-- The SAME inherited source measure has M's follower remainder as marginal.
This consumes the admitted split/product theorem and the original whole
TimeControl probability law. There is no normalization of either branch. -/
theorem sourceFollowerRetained_map : (μZi).map xof = μCi := by
  change (μZi).map
    (Prod.fst ∘ ReferenceFirstLiveSourceSavedMoments.followerSourceSplit
      rate rewards C_star C_h q t s hs control0 i) = μCi
  rw [← Measure.map_map measurable_fst
    (ReferenceFirstLiveSourceSavedMoments.measurable_followerSourceSplit
      rate rewards C_star C_h q t s hs control0 i),
    ReferenceFirstLiveSourceSavedMoments.followerSourceSplit_product,
    Measure.map_fst_prod, measure_univ, one_smul]

/-- Integration of a measurable remainder function over the corresponding
actual source cell. Both integrals use the original inherited measures.
The explicit generic inputs are just the function and its Borel measurability
and the Borel cell; the project-specific measure identity is proved above. -/
theorem sourceFollowerRetained_cell_integral (g : Xi → ℝ) (hg : Measurable g)
    (A : Set X) (hA : MeasurableSet A) :
    (∫ z in {z : Zi | ret z.val ∈ A}, g (xof z) ∂μZi) =
      ∫ x in {x : Xi | x.val ∈ A}, g x ∂μCi := by
  let cell : Set Xi := {x | x.val ∈ A}
  have hcell : MeasurableSet cell := hA.preimage measurable_subtype_coe
  have hsource : MeasurableSet {z : Zi | ret z.val ∈ A} :=
    hA.preimage ((ReferenceFirstLiveRecordingSourceCylinder.measurable_sourceRetained
      rate rewards C_star C_h q t s hs control0).comp measurable_subtype_coe)
  have hindicator :
      (fun z : Zi => ({z : Zi | ret z.val ∈ A}).indicator (fun z => g (xof z)) z) =
        (cell.indicator g) ∘ xof := by
    funext z
    exact Set.indicator_comp_right xof (s := cell) (g := g) (x := z)
  calc
    _ = ∫ z, ({z : Zi | ret z.val ∈ A}).indicator (fun z => g (xof z)) z ∂μZi :=
      (integral_indicator hsource).symm
    _ = ∫ z, (cell.indicator g) (xof z) ∂μZi := by
      rw [hindicator]
      rfl
    _ = ∫ x, cell.indicator g x ∂((μZi).map xof) :=
      (integral_map (measurable_sourceFollowerRetained
        rate rewards C_star C_h q t s hs control0 i).aemeasurable
        (hg.indicator hcell).aestronglyMeasurable).symm
    _ = ∫ x, cell.indicator g x ∂μCi := by
      rw [sourceFollowerRetained_map]
    _ = ∫ x in {x : Xi | x.val ∈ A}, g x ∂μCi := integral_indicator hcell

/-- Scalar envelopes for the candidate first and square means, derived from
the actual fixed-remainder moments and their original scalar bounds. -/
theorem follower_mean_bounds (x : Xi) :
    (0 ≤ ReferenceFirstLiveSourceSavedMoments.xi rate rewards C_star C_h q t s hs control0 i x *
        ReferenceFirstLiveSourceSavedMoments.value rate rewards C_star C_h q t s hs control0 i x ∧
      ReferenceFirstLiveSourceSavedMoments.xi rate rewards C_star C_h q t s hs control0 i x *
        ReferenceFirstLiveSourceSavedMoments.value rate rewards C_star C_h q t s hs control0 i x ≤ 1) ∧
    (0 ≤ ReferenceFirstLiveSourceSavedMoments.xi rate rewards C_star C_h q t s hs control0 i x *
        (ReferenceFirstLiveSourceSavedMoments.value rate rewards C_star C_h q t s hs control0 i x) ^ 2 ∧
      ReferenceFirstLiveSourceSavedMoments.xi rate rewards C_star C_h q t s hs control0 i x *
        (ReferenceFirstLiveSourceSavedMoments.value rate rewards C_star C_h q t s hs control0 i x) ^ 2 ≤
          1 / ReferenceFirstLiveSourceSavedMoments.beta rate) := by
  rcases ReferenceFirstLiveSourceSavedMoments.actual_follower_saved_moments
      rate rewards C_star C_h q t s hs control0 i x with
    ⟨⟨hxi, hbeta, hbetaXi, _, hrho⟩, _, _, _, hfirst, hsecond, _, hupper, _, hsquare, hbounds⟩
  constructor
  · constructor
    · rw [← hfirst]
      exact integral_nonneg (fun u => (hbounds u).1)
    · rw [← hfirst]
      exact hupper.trans hrho
  · constructor
    · exact mul_nonneg hxi.le (sq_nonneg _)
    · rw [← hsecond]
      exact hsquare.trans (one_div_le_one_div_of_le hbeta hbetaXi)

/-- First candidate is measurable in precisely Fi. -/
theorem first_mean_adapted : Measurable[Fi] (fun z : Zi => xiZ z * vZ z) :=
  (ReferenceFirstLiveSourcePrefixBranchInvariance.xiZ_adapted
    rate rewards C_star C_h q t s hs control0 i).mul
    (ReferenceFirstLiveSourcePrefixBranchInvariance.vZ_adapted
      rate rewards C_star C_h q t s hs control0 i)

/-- Square candidate is measurable in precisely Fi. -/
theorem second_mean_adapted : Measurable[Fi] (fun z : Zi => xiZ z * (vZ z) ^ 2) :=
  (ReferenceFirstLiveSourcePrefixBranchInvariance.xiZ_adapted
    rate rewards C_star C_h q t s hs control0 i).mul
    ((ReferenceFirstLiveSourcePrefixBranchInvariance.vZ_adapted
      rate rewards C_star C_h q t s hs control0 i).pow_const 2)

/-- The first candidate is integrable under the inherited unnormalized source
measure, by its actual scalar envelope. This includes a zero source measure. -/
theorem first_mean_integrable : Integrable (fun z : Zi => xiZ z * vZ z) μZi := by
  have hm := sourceFollowerPrefixField_le rate rewards C_star C_h q t s hs control0 i
  have hmeas : Measurable (fun z : Zi => xiZ z * vZ z) :=
    (first_mean_adapted rate rewards C_star C_h q t s hs control0 i).mono hm le_rfl
  apply Integrable.of_bound hmeas.aestronglyMeasurable 1
  apply Filter.Eventually.of_forall
  intro z
  have hb := (follower_mean_bounds rate rewards C_star C_h q t s hs control0 i (xof z)).1
  change 0 ≤ xiZ z * vZ z ∧ xiZ z * vZ z ≤ 1 at hb
  rw [Real.norm_eq_abs, abs_of_nonneg hb.1]
  exact hb.2

/-- The square candidate has its actual common beta envelope on the SAME
finite source measure; no integrability input is required from consumers. -/
theorem second_mean_integrable : Integrable (fun z : Zi => xiZ z * (vZ z) ^ 2) μZi := by
  have hm := sourceFollowerPrefixField_le rate rewards C_star C_h q t s hs control0 i
  have hmeas : Measurable (fun z : Zi => xiZ z * (vZ z) ^ 2) :=
    (second_mean_adapted rate rewards C_star C_h q t s hs control0 i).mono hm le_rfl
  apply Integrable.of_bound hmeas.aestronglyMeasurable
    (1 / ReferenceFirstLiveSourceSavedMoments.beta rate)
  apply Filter.Eventually.of_forall
  intro z
  have hb := (follower_mean_bounds rate rewards C_star C_h q t s hs control0 i (xof z)).2
  change 0 ≤ xiZ z * (vZ z) ^ 2 ∧
    xiZ z * (vZ z) ^ 2 ≤ 1 / ReferenceFirstLiveSourceSavedMoments.beta rate at hb
  rw [Real.norm_eq_abs, abs_of_nonneg hb.1]
  exact hb.2

/-- The actual first cell integral on EVERY Fi-measurable source cell.
The remainder cell is produced inside, and M's RHS is transferred back via
its admitted follower source product split. -/
theorem sourceSaved_firstMoment_prefixField_integral (S : Set Zi)
    (hS : MeasurableSet[Fi] S) :
    (∫ z in S, saved z ∂μZi) = ∫ z in S, xiZ z * vZ z ∂μZi := by
  obtain ⟨A, hA, hAS⟩ := prefixField_cell rate rewards C_star C_h q t s hs control0 i S hS
  rw [← hAS]
  rw [ReferenceFirstLiveSourceSavedMoments.sourceSaved_firstMoment_cell_integral
    rate rewards C_star C_h q t s hs control0 i A hA]
  exact (sourceFollowerRetained_cell_integral rate rewards C_star C_h q t s hs control0 i
    (fun x => ReferenceFirstLiveSourceSavedMoments.xi rate rewards C_star C_h q t s hs control0 i x *
      ReferenceFirstLiveSourceSavedMoments.value rate rewards C_star C_h q t s hs control0 i x)
    ((ReferenceFirstLiveSourceSavedMoments.measurable_xi
      rate rewards C_star C_h q t s hs control0 i).mul
      (ReferenceFirstLiveSourceSavedMoments.measurable_value
        rate rewards C_star C_h q t s hs control0 i)) A hA).symm

/-- The actual square cell integral on EVERY Fi-measurable source cell,
on the same unnormalized source and the same produced remainder cell. -/
theorem sourceSaved_secondMoment_prefixField_integral (S : Set Zi)
    (hS : MeasurableSet[Fi] S) :
    (∫ z in S, (saved z) ^ 2 ∂μZi) = ∫ z in S, xiZ z * (vZ z) ^ 2 ∂μZi := by
  obtain ⟨A, hA, hAS⟩ := prefixField_cell rate rewards C_star C_h q t s hs control0 i S hS
  rw [← hAS]
  rw [ReferenceFirstLiveSourceSavedMoments.sourceSaved_secondMoment_cell_integral
    rate rewards C_star C_h q t s hs control0 i A hA]
  exact (sourceFollowerRetained_cell_integral rate rewards C_star C_h q t s hs control0 i
    (fun x => ReferenceFirstLiveSourceSavedMoments.xi rate rewards C_star C_h q t s hs control0 i x *
      (ReferenceFirstLiveSourceSavedMoments.value rate rewards C_star C_h q t s hs control0 i x) ^ 2)
    ((ReferenceFirstLiveSourceSavedMoments.measurable_xi
      rate rewards C_star C_h q t s hs control0 i).mul
      ((ReferenceFirstLiveSourceSavedMoments.measurable_value
        rate rewards C_star C_h q t s hs control0 i).pow_const 2)) A hA).symm

/-- First conditional identity for the actual current saved real emission
on B's exact analysis strict-prefix field and M's SAME inherited source measure.
All inclusion, measurability, finite-trim and cell-integral premises are produced.
No positive branch mass, physical success or supplied conditional law is used. -/
theorem sourceSaved_condExp_firstMoment :
    μZi[saved | Fi] =ᵐ[μZi] (fun z : Zi => xiZ z * vZ z) := by
  have hm := sourceFollowerPrefixField_le rate rewards C_star C_h q t s hs control0 i
  have : IsFiniteMeasure ((μZi).trim hm) :=
    sourceFollowerPrefixField_trim_finite rate rewards C_star C_h q t s hs control0 i
  apply Filter.EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq hm
    (ReferenceFirstLiveSourceSavedMoments.followerSource_saved_integrable
      rate rewards C_star C_h q t s hs control0 i)
  · intro S _ _
    exact (first_mean_integrable rate rewards C_star C_h q t s hs control0 i).integrableOn
  · intro S hS _
    exact (sourceSaved_firstMoment_prefixField_integral
      rate rewards C_star C_h q t s hs control0 i S hS).symm
  · exact (first_mean_adapted
      rate rewards C_star C_h q t s hs control0 i).aestronglyMeasurable

/-- Square conditional identity for the SAME actual real saved emission,
analysis field, rate, whole rewards, arbitrary C_star/C_h and source measure. -/
theorem sourceSaved_condExp_secondMoment :
    μZi[(fun z : Zi => (saved z) ^ 2) | Fi] =ᵐ[μZi]
      (fun z : Zi => xiZ z * (vZ z) ^ 2) := by
  have hm := sourceFollowerPrefixField_le rate rewards C_star C_h q t s hs control0 i
  have : IsFiniteMeasure ((μZi).trim hm) :=
    sourceFollowerPrefixField_trim_finite rate rewards C_star C_h q t s hs control0 i
  apply Filter.EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq hm
    (ReferenceFirstLiveSourceSavedMoments.followerSource_saved_sq_integrable
      rate rewards C_star C_h q t s hs control0 i)
  · intro S _ _
    exact (second_mean_integrable rate rewards C_star C_h q t s hs control0 i).integrableOn
  · intro S hS _
    exact (sourceSaved_secondMoment_prefixField_integral
      rate rewards C_star C_h q t s hs control0 i S hS).symm
  · exact (second_mean_adapted
      rate rewards C_star C_h q t s hs control0 i).aestronglyMeasurable

/-- The first-assignment boundary has the empty continuing follower subtype
and zero inherited measures, as in M. The conditional identities above already
cover this case and every other zero-mass branch without normalization. -/
theorem follower_measures_eq_zero_of_s_eq_t (hfirst : s = t.val) :
    μCi = 0 ∧ μZi = 0 :=
  ReferenceFirstLiveSourceSavedMoments.follower_measures_eq_zero_of_s_eq_t
    rate rewards C_star C_h q t s hs control0 i hfirst

end Bandits.Support.ReferenceFirstLiveSourceSavedConditionalMoments

end
