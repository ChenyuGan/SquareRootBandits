/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceSourcePhysicalFlagConditionalLaw
public import Bandits.Support.ReferenceFirstLiveReleaseCylinderIntegral

/-!
# Actual first-live source flags and control sections

Sources: `sources/zip4/manuscript/05_binary_transport.tex:74-124,293-345`,
`sources/zip4/manuscript/06_interruptions.tex:376-426,435-492`,
`sources/zip4/manuscript/07_public_setup.tex:127-164`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-79`.

The branch below is a literal computed event on the original source. It
retains the original private index, all private arrays, the complete reward
table, and the actual optional selector. No inhabitance or positive mass is
asserted. These are internal identifications, not manuscript closure or a
service law on all stopped pending support.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open scoped Classical ENNReal

namespace Bandits.Support.ReferenceFirstLiveActualFlagSections

abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput
abbrev TimeControl := ContinuousLearningRows.TimeControl

variable {p : Parameters} (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) (q : Fin (M p)) (s : ℕ) (hs : s ≤ t.val)

local notation "X" => ReferenceRetainedBoundaryMeasurability.RetainedLaunchStart
  rate rewards C_star C_h q t s hs control0
local notation "S" => ReferenceFirstLiveReleaseSourceCylinder.selectedEmptyPendingRemainder
  (rate := rate) rewards C_star C_h q t s hs control0 i
local notation "β" => ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary
  rate rewards C_star C_h q t s hs control0
local notation "W" => ReferenceFirstLiveReleaseControlTransport.retainedWindow
  (rate := rate) rewards C_star C_h q t s hs control0
local notation "split" => ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t

/-- The actual initialization stratum and actual selected-empty/pending
remainder test. There is no operational fallback payload or state. -/
def firstLiveSourceBranch : Set (SourceInput p) :=
  {z | ∃ hj : ActualInitializationPhysicalStep.selectedRowIndex p z = q,
    ∃ hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true,
    ∃ he : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed = s,
      ReferenceRetainedBoundaryMeasurability.retainedLaunchStartInputOfSource
        rate rewards C_star C_h q t s hs control0 z hj hc he ∈ S}

local notation "E" => firstLiveSourceBranch rate rewards C_star C_h control0 i t q s hs

/-- The image characterization is proved from the literal source event; it
does not replace the operational definition. -/
theorem firstLiveSourceBranch_iff_remainder (z : SourceInput p) :
    z ∈ E ↔ (split z).2 ∈ Subtype.val '' S := by
  constructor
  · rintro ⟨hj, hc, he, hx⟩
    exact ⟨ReferenceRetainedBoundaryMeasurability.retainedLaunchStartInputOfSource
      rate rewards C_star C_h q t s hs control0 z hj hc he, hx, rfl⟩
  · rintro ⟨x, hx, hval⟩
    have hrem : (split z).2 ∈
        ReferenceRetainedBoundaryMeasurability.retainedLaunchStartSet
          rate rewards C_star C_h q t s control0 := hval ▸ x.property
    obtain ⟨hj, hc, he⟩ :=
      (ReferenceRetainedSourceCoupling.retainedSourceEvent_iff_remainder
        rate rewards C_star C_h q t s hs control0 z).mpr hrem
    have hj' : ActualInitializationPhysicalStep.selectedRowIndex p z = q :=
      (ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex p z).symm.trans hj
    refine ⟨hj', hc, he, ?_⟩
    have heq : ReferenceRetainedBoundaryMeasurability.retainedLaunchStartInputOfSource
        rate rewards C_star C_h q t s hs control0 z hj' hc he = x :=
      Subtype.ext hval.symm
    rw [heq]
    exact hx

/-- Ambient Borel measurability preserves continuous remainder fibres. -/
theorem measurableSet_firstLiveSourceBranch : MeasurableSet E := by
  have hS := ReferenceFirstLiveReleaseSourceCylinder.measurableSet_selectedEmptyPendingRemainder
    (rate := rate) rewards C_star C_h q t s hs control0 i
  have hsub := MeasurableEmbedding.subtype_coe
    (ReferenceRetainedBoundaryMeasurability.measurableSet_retainedLaunchStartSet
      rate rewards C_star C_h q t s hs control0)
  have hpre := (hsub.measurableSet_image.mpr hS).preimage
    (measurable_snd.comp (split).measurable)
  have heq : E = (fun z : SourceInput p => (split z).2) ⁻¹' (Subtype.val '' S) := by
    ext z
    exact firstLiveSourceBranch_iff_remainder rate rewards C_star C_h control0 i t q s hs z
  rw [heq]
  exact hpre

/-- The retained object exists only on the literal branch. Its value is the
unique original fixed-control remainder, as specified below. -/
def firstLiveRemainder (z : SourceInput p) (hz : z ∈ E) : X :=
  ReferenceRetainedBoundaryMeasurability.retainedLaunchStartInputOfSource
    rate rewards C_star C_h q t s hs control0 z hz.choose
      hz.choose_spec.choose hz.choose_spec.choose_spec.choose

theorem firstLiveRemainder_val (z : SourceInput p) (hz : z ∈ E) :
    (firstLiveRemainder rate rewards C_star C_h control0 i t q s hs z hz).val =
      (split z).2 := rfl

theorem firstLiveRemainder_mem (z : SourceInput p) (hz : z ∈ E) :
    firstLiveRemainder rate rewards C_star C_h control0 i t q s hs z hz ∈ S :=
  hz.choose_spec.choose_spec.choose_spec

/-- Replacing the whole current control preserves the actual branch and
recovers exactly the same retained remainder, including all private arrays. -/
theorem firstLiveSourceBranch_replace (z : SourceInput p) (hz : z ∈ E)
    (u : TimeControl p) :
    let zu := ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z u
    ∃ hzu : zu ∈ E,
      firstLiveRemainder rate rewards C_star C_h control0 i t q s hs zu hzu =
        firstLiveRemainder rate rewards C_star C_h control0 i t q s hs z hz := by
  intro zu
  have hj : ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p z = q :=
    (ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex p z).trans hz.choose
  have hsource := ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_replaceSourceControl
    p q t z u hj
  have hsplit : (split zu).2 = (split z).2 := by
    dsimp only [zu]
    rw [← hsource, (split).apply_symm_apply]
  have hzu : zu ∈ E :=
    (firstLiveSourceBranch_iff_remainder rate rewards C_star C_h control0 i t q s hs zu).mpr
      (hsplit ▸ (firstLiveSourceBranch_iff_remainder
        rate rewards C_star C_h control0 i t q s hs z).mp hz)
  refine ⟨hzu, Subtype.ext ?_⟩
  exact hsplit

section PrefixComparison

variable {rate}

open ReferenceActivePhysicalStep (State RoundInput prepare liveRegistersAt liveOwnedAt)
open ReferenceActivePhysicalHorizon (run allActiveAtStart)
open ReferenceCollectionPhaseHistory (cutoffChosen)

-- Compare the actual dispatch constructor tags locally. No private cutoff
-- theorem from an imported module is used.
private def liveCutoffTag
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ) (row : CompletePublicTable.CompleteRow p)
    (out : CoordinatorRoundDispatch.LiveOutcome
      { eta := rate.eta, registers := r, ownedRegisters := owned,
        followerBaseScore := base, row := row }) : Bool :=
  match out with
  | .cutoffChosen _ _ _ _ _ _ _ _ _ _ => true
  | _ => false

private theorem liveCutoffTag_eq_projection
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ) (row : CompletePublicTable.CompleteRow p)
    (out : CoordinatorRoundDispatch.LiveOutcome
      { eta := rate.eta, registers := r, ownedRegisters := owned,
        followerBaseScore := base, row := row }) :
    liveCutoffTag r owned base row out =
      (match (ReferenceActiveDispatchTemporal.liveOutcomeData r owned base row out).2.2 with
      | .inr (.inr (.inr _)) => true
      | _ => false) := by
  cases out <;> rfl

private theorem cutoffChosen_live
    (input : RoundInput p rate)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ)
    (hphase : input.state.coordinator = .live r owned base) :
    cutoffChosen input =
      liveCutoffTag (liveRegistersAt r input.time)
        (liveOwnedAt r owned input.time) base input.row
        (CoordinatorRoundDispatch.dispatchLive
          (ReferenceActivePhysicalStep.liveInput input r owned base)) := by
  dsimp only [cutoffChosen, prepare,
    ReferenceActivePhysicalStep.dispatch]
  simp only [hphase, CoordinatorRoundDispatch.dispatch]
  cases CoordinatorRoundDispatch.dispatchLive
    (ReferenceActivePhysicalStep.liveInput input r owned base) <;> rfl

private theorem cutoffChosen_eq_of_current
    (state : State p rate) (rows otherRows : CompletePublicTable.CompleteRows p)
    (selected otherSelected : Fin (M p)) (time : Fin p.T)
    (active : ∀ i, (state.activations i).val ≤ time.val + 1)
    (rewards otherRewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (hcurrent : (rows selected).2 time = (otherRows otherSelected).2 time) :
    cutoffChosen ⟨state, rows, selected, time, active, rewards⟩ =
      cutoffChosen ⟨state, otherRows, otherSelected, time, active, otherRewards⟩ := by
  classical
  cases hphase : state.coordinator with
  | first =>
      dsimp only [cutoffChosen, prepare, ReferenceActivePhysicalStep.dispatch]
      simp only [hphase,
        CoordinatorRoundDispatch.dispatch]
      rfl
  | live r owned base =>
      have hdata := ReferenceActiveDispatchTemporal.liveOutcomeData_eq_of_current (liveRegistersAt r time)
        (liveOwnedAt r owned time) base (rows selected) (otherRows otherSelected) hcurrent
      have htag := congrArg (fun data =>
        match data.2.2 with
        | .inr (.inr (.inr _)) => true
        | _ => false) hdata
      rw [← liveCutoffTag_eq_projection, ← liveCutoffTag_eq_projection] at htag
      rw [cutoffChosen_live _ r owned base hphase,
        cutoffChosen_live _ r owned base hphase]
      simpa only [
        ReferenceActivePhysicalStep.liveInput, RoundInput.row,
        liveCutoffTag] using htag
  | collection payload ledger proposal =>
      dsimp only [cutoffChosen, prepare, ReferenceActivePhysicalStep.dispatch]
      simp only [hphase]
      by_cases hc : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
      · simp only [dite_eq_left hc, CoordinatorRoundDispatch.dispatch]
        rfl
      · simp only [dite_eq_right hc]
  | dagger =>
      dsimp only [cutoffChosen, prepare, ReferenceActivePhysicalStep.dispatch]
      simp only [hphase]

private theorem cutoffChosen_congr (left right : RoundInput p rate)
    (hstate : left.state = right.state) (htime : left.time = right.time)
    (hcurrent : left.row.2 left.time = right.row.2 right.time) :
    cutoffChosen left = cutoffChosen right := by
  cases left
  cases right
  dsimp only at hstate htime hcurrent
  cases hstate
  cases htime
  exact cutoffChosen_eq_of_current _ _ _ _ _ _ _ _ _ hcurrent

/-- Earlier PREPARE cutoff tags agree by equality of the actual prefix states
and current temporal dispatch data. Evidence equality alone is not used as a
substitute for these tags. -/
private theorem run_cutoffTags_eq
    (initial : State p rate) (rows otherRows : CompletePublicTable.CompleteRows p)
    (selected : Fin (M p)) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : allActiveAtStart initial start)
    (hcontrols : ∀ j : Fin p.T, start ≤ j.val → j.val < start + count →
      (rows selected).2 j = (otherRows selected).2 j)
    (hbefore : ∀ j : Fin p.T, j.val < start →
      ((rows selected).2 j).1 ContinuousControlSlice.Label.prop =
        ((otherRows selected).2 j).1 ContinuousControlSlice.Label.prop) :
    (run initial rows selected rewards start count hspan hmode).records.map
        (fun record => cutoffChosen record.input) =
      (run initial otherRows selected rewards start count hspan hmode).records.map
        (fun record => cutoffChosen record.input) := by
  induction count with
  | zero => rw [ReferenceActivePhysicalHorizon.run_zero_records, ReferenceActivePhysicalHorizon.run_zero_records]
  | succ count ih =>
      have hprefix : start + count ≤ p.T := by omega
      have hcontrolsPrefix : ∀ j : Fin p.T, start ≤ j.val → j.val < start + count →
          (rows selected).2 j = (otherRows selected).2 j := by
        intro j hj hk
        exact hcontrols j hj (by omega)
      have htags := ih hprefix hcontrolsPrefix
      have hstate := (ReferenceActiveTemporalAssembly.run_eq_of_temporal_reads initial
        rows otherRows selected rewards rewards start count hprefix hmode
        hcontrolsPrefix (fun _ _ _ => rfl) (fun _ => hbefore)).1
      rw [ReferenceActivePhysicalHorizon.run_successor_step, ReferenceActivePhysicalHorizon.run_successor_step]
      simp only [ReferenceActivePhysicalHorizon.foldRound, List.map_append, List.map_singleton]
      rw [htags]
      congr 1
      apply congrArg List.singleton
      apply cutoffChosen_congr
      · exact hstate
      · rfl
      · exact hcontrols ⟨start + count, by omega⟩ (by dsimp; omega) (by dsimp; omega)

private theorem run_cutoffTags_congr_initial
    (left right : State p rate) (heq : left = right)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hl : allActiveAtStart left start)
    (hr : allActiveAtStart right start) :
    (run left rows selected rewards start count hspan hl).records.map
        (fun record => cutoffChosen record.input) =
      (run right rows selected rewards start count hspan hr).records.map
        (fun record => cutoffChosen record.input) := by
  cases heq
  rfl

private theorem run_cutoffTags_eq_of_initial_eq
    (left right : State p rate) (heq : left = right)
    (rows otherRows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hl : allActiveAtStart left start)
    (hr : allActiveAtStart right start)
    (hcontrols : ∀ j : Fin p.T, start ≤ j.val → j.val < start + count →
      (rows selected).2 j = (otherRows selected).2 j)
    (hbefore : ∀ j : Fin p.T, j.val < start →
      ((rows selected).2 j).1 ContinuousControlSlice.Label.prop =
        ((otherRows selected).2 j).1 ContinuousControlSlice.Label.prop) :
    (run left rows selected rewards start count hspan hl).records.map
        (fun record => cutoffChosen record.input) =
      (run right otherRows selected rewards start count hspan hr).records.map
        (fun record => cutoffChosen record.input) := by
  cases heq
  exact run_cutoffTags_eq _ _ _ _ _ _ _ _ _ hcontrols hbefore

private theorem run_state_eq_of_initial_eq
    (left right : State p rate) (heq : left = right)
    (rows otherRows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hl : allActiveAtStart left start) (hr : allActiveAtStart right start)
    (hcontrols : ∀ j : Fin p.T, j.val < start + count →
      (rows selected).2 j = (otherRows selected).2 j) :
    (run left rows selected rewards start count hspan hl).finalState =
      (run right otherRows selected rewards start count hspan hr).finalState := by
  cases heq
  exact (ReferenceActiveTemporalAssembly.run_eq_of_temporal_reads
    left rows otherRows selected rewards rewards start count hspan hl
    (fun j _ hj => hcontrols j hj) (fun _ _ _ => rfl)
    (fun _ j hj => congrArg (fun u => u.1 ContinuousControlSlice.Label.prop)
      (hcontrols j (by omega)))).1

private theorem live_downView_eq
    (left right : RoundInput p rate)
    (hstate : left.state = right.state) (hselected : left.selected = right.selected)
    (htime : left.time = right.time)
    (hcurrent : left.row.2 left.time = right.row.2 right.time)
    (hlive : ∃ r owned base, left.state.coordinator = .live r owned base) :
    (prepare left).coordinator.downView = (prepare right).coordinator.downView := by
  cases left
  cases right
  dsimp only at hstate hselected htime hcurrent hlive
  cases hstate
  cases hselected
  cases htime
  obtain ⟨r, owned, base, hphase⟩ := hlive
  exact congrArg (fun data => data.2.1)
    (ReferenceActiveDispatchTemporal.live_dispatch_data_eq_of_current
      _ _ _ _ _ _ _ _ r owned base hphase hcurrent)

private theorem roundInput_eq (left right : RoundInput p rate)
    (hstate : left.state = right.state) (hrows : left.rows = right.rows)
    (hselected : left.selected = right.selected) (htime : left.time = right.time)
    (hrewards : left.rewards = right.rewards) : left = right := by
  cases left
  cases right
  simp_all only

private theorem retained_current_input (x : X)
    (hn : t.val - s < (W x control0).length) :
    (W x control0)[t.val - s].input = β x := by
  let source := ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.val
  let seed := ReferenceRetainedBoundaryMeasurability.retainedGeneratedActiveSeed
    rate rewards C_star C_h q t s hs control0 x
  have hmode := (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
    rate rewards C_star C_h q t control0 x.val x.property.1 s hs x.property.2).2.1
  have hp := List.takeWhile_prefix
    (l := (ReferenceFirstLiveReleaseControlTransport.retainedRun
      rewards C_star C_h q t s hs control0 x control0).records)
    (fun record => !cutoffChosen record.input)
  have hget := ReferenceLocalReleaseGateChronology.run_record_at
    seed source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
    rewards s hmode (t.val - s + 1) (by omega) ⟨t.val - s, by omega⟩
  have hrecord : (W x control0)[t.val - s] =
      ReferenceAssignmentPayloadChronology.actualRunRecordAt seed source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source)
        rewards s (t.val - s) (by omega) hmode :=
    (hp.getElem hn).trans hget
  rw [hrecord]
  change ReferenceActivePhysicalHorizon.roundInputAt seed source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s hmode
      (run seed source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
        rewards s (t.val - s) (by omega) hmode) ⟨s + (t.val - s), by omega, by omega⟩ = β x
  apply roundInput_eq
  · rfl
  · rfl
  · rfl
  · apply Fin.ext
    change s + (t.val - s) = t.val
    omega
  · rfl

/-- A conditional deterministic prefix comparison. Both inputs are actual
retained launch remainders; the corrected seed and every selected control
through the queried round must agree. No whole-record equality is assumed. -/
theorem selectedEmptyPendingRemainder_of_prefix
    (x y : X)
    (hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch rate
        (ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.val) rewards C_star C_h =
      ReferenceCorrectedInitializationLaunch.correctedLaunch rate
        (ReferenceGeneratedActivePrefixFactor.splitSource q t control0 y.val) rewards C_star C_h)
    (hcontrols : ∀ v : Fin p.T, v.val ≤ t.val →
      ((ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.val).1.2 q).2 v =
        ((ReferenceGeneratedActivePrefixFactor.splitSource q t control0 y.val).1.2 q).2 v)
    (hx : x ∈ S) : y ∈ S := by
  let sourceX := ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.val
  let sourceY := ReferenceGeneratedActivePrefixFactor.splitSource q t control0 y.val
  let seedX := ReferenceRetainedBoundaryMeasurability.retainedGeneratedActiveSeed
    rate rewards C_star C_h q t s hs control0 x
  let seedY := ReferenceRetainedBoundaryMeasurability.retainedGeneratedActiveSeed
    rate rewards C_star C_h q t s hs control0 y
  have hspecX := ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
    rate rewards C_star C_h q t control0 x.val x.property.1 s hs x.property.2
  have hspecY := ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
    rate rewards C_star C_h q t control0 y.val y.property.1 s hs y.property.2
  have hseed : seedX = seedY := Option.some.inj
    (hspecX.1.symm.trans (hlaunch.trans hspecY.1))
  have hjX : ActualInitializationPhysicalStep.selectedRowIndex p sourceX = q :=
    ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary_selected_eq_q
      rate rewards C_star C_h q t s hs control0 x
  have hjY : ActualInitializationPhysicalStep.selectedRowIndex p sourceY = q :=
    ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary_selected_eq_q
      rate rewards C_star C_h q t s hs control0 y
  have htags :
      (ReferenceFirstLiveReleaseControlTransport.retainedRun
        rewards C_star C_h q t s hs control0 x control0).records.map
          (fun record => cutoffChosen record.input) =
      (ReferenceFirstLiveReleaseControlTransport.retainedRun
        rewards C_star C_h q t s hs control0 y control0).records.map
          (fun record => cutoffChosen record.input) := by
    change (run seedX sourceX.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p sourceX)
      rewards s (t.val - s + 1) (by omega) hspecX.2.1).records.map _ =
      (run seedY sourceY.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p sourceY)
        rewards s (t.val - s + 1) (by omega) hspecY.2.1).records.map _
    rw [hjX, hjY]
    exact run_cutoffTags_eq_of_initial_eq _ _ hseed _ _ q rewards s _ _ _ _
      (fun v _ hv => hcontrols v (by omega))
      (fun v hv => congrArg (fun u => u.1 ContinuousControlSlice.Label.prop)
        (hcontrols v (by omega)))
  obtain ⟨hn, selected0, hselected, hempty, hi⟩ := hx
  have hpX := List.takeWhile_prefix
    (l := (ReferenceFirstLiveReleaseControlTransport.retainedRun
      rewards C_star C_h q t s hs control0 x control0).records)
    (fun record => !cutoffChosen record.input)
  have hlenX : (ReferenceFirstLiveReleaseControlTransport.retainedRun
      rewards C_star C_h q t s hs control0 x control0).records.length = t.val - s + 1 :=
    ReferenceActivePhysicalHorizon.run_record_count _ _ _ _ _ _ _ _
  change (W x control0).IsPrefix (ReferenceFirstLiveReleaseControlTransport.retainedRun
    rewards C_star C_h q t s hs control0 x control0).records at hpX
  have hfullX : W x control0 = (ReferenceFirstLiveReleaseControlTransport.retainedRun
      rewards C_star C_h q t s hs control0 x control0).records :=
    hpX.eq_of_length (by have hle := hpX.length_le; omega)
  have hallX : ∀ record ∈ (ReferenceFirstLiveReleaseControlTransport.retainedRun
      rewards C_star C_h q t s hs control0 x control0).records,
      cutoffChosen record.input = false := by
    intro record hmem
    rw [← hfullX] at hmem
    have htest := List.mem_takeWhile_imp hmem
    simpa only [Bool.not_eq_true'] using htest
  have hallY : ∀ record ∈ (ReferenceFirstLiveReleaseControlTransport.retainedRun
      rewards C_star C_h q t s hs control0 y control0).records,
      cutoffChosen record.input = false := by
    intro record hmem
    have htagmem : cutoffChosen record.input ∈
        (ReferenceFirstLiveReleaseControlTransport.retainedRun
          rewards C_star C_h q t s hs control0 y control0).records.map
            (fun r => cutoffChosen r.input) := List.mem_map.mpr ⟨record, hmem, rfl⟩
    rw [← htags] at htagmem
    obtain ⟨other, hother, heq⟩ := List.mem_map.mp htagmem
    exact heq.symm.trans (hallX other hother)
  have hfullY : W y control0 = (ReferenceFirstLiveReleaseControlTransport.retainedRun
      rewards C_star C_h q t s hs control0 y control0).records :=
    List.takeWhile_eq_self_iff.mpr (by
      intro record hmem
      simp only [hallY record hmem, Bool.not_false])
  have hny : t.val - s < (W y control0).length := by
    have hlenY : (ReferenceFirstLiveReleaseControlTransport.retainedRun
        rewards C_star C_h q t s hs control0 y control0).records.length = t.val - s + 1 :=
      ReferenceActivePhysicalHorizon.run_record_count _ _ _ _ _ _ _ _
    rw [hfullY, hlenY]
    omega
  have hstate : (β x).state = (β y).state := by
    change (run seedX sourceX.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p sourceX)
      rewards s (t.val - s) (by omega) hspecX.2.1).finalState =
      (run seedY sourceY.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p sourceY)
        rewards s (t.val - s) (by omega) hspecY.2.1).finalState
    rw [hjX, hjY]
    exact run_state_eq_of_initial_eq _ _ hseed _ _ q rewards s _ _ _ _
      (fun v hv => hcontrols v (by omega))
  have hinX := retained_current_input rewards C_star C_h control0 t q s hs x hn
  have hinY := retained_current_input rewards C_star C_h control0 t q s hs y hny
  obtain ⟨r, owned, base, _, hlive, _⟩ :=
    ReferenceFirstLiveReleaseControlTransport.retained_first_live_control_transport
      rewards C_star C_h q t s hs control0 x hn selected0 hselected hempty
  have hdown := live_downView_eq
    (W x control0)[t.val - s].input (W y control0)[t.val - s].input
    (by rw [hinX, hinY]; exact hstate)
    (by rw [hinX, hinY, ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary_selected_eq_q,
      ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary_selected_eq_q])
    (by rw [hinX, hinY, ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary_time,
      ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary_time])
    (by
      rw [hinX, hinY]
      simp only [ReferenceActivePhysicalStep.RoundInput.row,
        ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary_rows,
        ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary_selected_eq_q,
        ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary_time]
      exact hcontrols t le_rfl)
    ⟨r, owned, base, hlive⟩
  have hselectedPrep : (prepare (W x control0)[t.val - s].input).coordinator.selection =
      some selected0 := by
    have h := hselected
    change (W x control0)[t.val - s].output.preparation.coordinator.selection = some selected0 at h
    rw [(W x control0)[t.val - s].output_eq] at h
    exact h
  change (prepare (W x control0)[t.val - s].input).coordinator.selection.map
      ReferenceActivePhysicalStep.Selection.view =
    (prepare (W y control0)[t.val - s].input).coordinator.selection.map
      ReferenceActivePhysicalStep.Selection.view at hdown
  rw [hselectedPrep, Option.map_some] at hdown
  cases hselY : (prepare (W y control0)[t.val - s].input).coordinator.selection with
  | none => rw [hselY, Option.map_none] at hdown; cases hdown
  | some selectedY =>
      rw [hselY, Option.map_some] at hdown
      have hview := (Option.some.inj hdown).symm
      refine ⟨hny, selectedY, ?_, ?_, ?_⟩
      · change (W y control0)[t.val - s].output.preparation.coordinator.selection = some selectedY
        rw [(W y control0)[t.val - s].output_eq]
        exact hselY
      · rw [hview]
        exact hempty
      · rw [hview, ← hstate]
        exact hi

end PrefixComparison

/-- The strict prefix discards the current whole-control replacement. -/
theorem sourcePrefix_replace_current (z : SourceInput p) (u : TimeControl p) :
    ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z u) =
      ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z := by
  apply Prod.ext
  · refine Prod.ext rfl ?_
    funext a
    by_cases ha : a = ActualInitializationPhysicalStep.selectedRowIndex p z
    · subst a
      dsimp only [ReferenceSourcePrefixHistoryFiltration.sourcePrefix,
        ReferenceFixedTimeSourceControlCoupling.replaceSourceControl,
        ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex,
        ActualInitializationPhysicalStep.selectedRowIndex]
      simp only [Function.update_self]
      refine Prod.ext rfl ?_
      funext v
      by_cases hv : v.val < t.val
      · have hne : v ≠ t := by intro heq; subst v; omega
        simp only [hv, ite_true, Function.update_of_ne hne]
      · simp only [hv, ite_false]
    · have ha' : a ≠ PrivateSourceStreams.coordinatorIndex p z.2.1.2 := ha
      dsimp only [ReferenceSourcePrefixHistoryFiltration.sourcePrefix,
        ReferenceFixedTimeSourceControlCoupling.replaceSourceControl,
        ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex,
        ActualInitializationPhysicalStep.selectedRowIndex]
      simp only [Function.update_of_ne ha']
  · rfl

private theorem selected_branch_prefix_iff (z : SourceInput p)
    (hj : ActualInitializationPhysicalStep.selectedRowIndex p z = q)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (he : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed = s)
    (hcc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z)
        rewards C_star C_h rate)).crossing.isSome = true)
    (hec : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput
          (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z)
          rewards C_star C_h rate)).completed = s) :
    ReferenceRetainedBoundaryMeasurability.retainedLaunchStartInputOfSource
      rate rewards C_star C_h q t s hs control0 z hj hc he ∈ S ↔
    ReferenceRetainedBoundaryMeasurability.retainedLaunchStartInputOfSource
      rate rewards C_star C_h q t s hs control0
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z)
      hj hcc hec ∈ S := by
  let c := ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z
  let x := ReferenceRetainedBoundaryMeasurability.retainedLaunchStartInputOfSource
    rate rewards C_star C_h q t s hs control0 z hj hc he
  let y := ReferenceRetainedBoundaryMeasurability.retainedLaunchStartInputOfSource
    rate rewards C_star C_h q t s hs control0 c hj hcc hec
  let sourceX := ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.val
  let sourceY := ReferenceGeneratedActivePrefixFactor.splitSource q t control0 y.val
  have hindex : ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p z = q := hj
  have hxsource : sourceX = ReferenceFixedTimeSourceControlCoupling.replaceSourceControl
      p t z control0 := ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_replaceSourceControl
        p q t z control0 hindex
  have hcy : (split c).1 = control0 := by
    rw [ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_control]
    rw [← hj]
    rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefix_control, ite_eq_right (lt_irrefl _)]
  have hysource : sourceY = c := by
    change (split).symm (control0, (split c).2) = c
    rw [← hcy, (split).symm_apply_apply]
  have hprefix : ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val sourceX = c := by
    rw [hxsource, sourcePrefix_replace_current]
  obtain ⟨hcrossX, helapsedX⟩ := ReferenceRetainedBoundaryMeasurability.retainedLaunchStart_source_facts
    rate rewards C_star C_h q t s hs control0 x.val x.property.1 x.property.2
  have hstartX : ReferenceCompletePhysicalHistory.physicalStart rate sourceX rewards C_star C_h = s := helapsedX
  have hby : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy rate rewards C_star C_h t.val sourceX :=
    ⟨hcrossX, by rw [hstartX]; exact hs⟩
  have hlaunch := (ReferenceSourcePrefixHistoryFiltration.sourcePrefix_preserves_actual_launch
    rate rewards C_star C_h control0 t.val (Nat.le_of_lt t.isLt) sourceX hby).2
  rw [hprefix, ← hysource] at hlaunch
  have hcontrols : ∀ v : Fin p.T, v.val ≤ t.val →
      (sourceX.1.2 q).2 v = (sourceY.1.2 q).2 v := by
    intro v hv
    rw [hysource, ← hprefix]
    have hjX : ActualInitializationPhysicalStep.selectedRowIndex p sourceX = q :=
      ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary_selected_eq_q
        rate rewards C_star C_h q t s hs control0 x
    rw [← hjX, ReferenceSourcePrefixHistoryFiltration.sourcePrefix_control]
    by_cases hlt : v.val < t.val
    · rw [ite_eq_left hlt]
    · rw [ite_eq_right hlt]
      have hvt : v = t := Fin.ext (by omega)
      subst v
      change (((split).symm (control0, x.val)).1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p sourceX)).2 t = control0
      rw [hjX]
      exact ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_symm_control p q t control0 x.val
  constructor
  · exact selectedEmptyPendingRemainder_of_prefix rewards C_star C_h control0 i t q s hs
      x y hlaunch hcontrols
  · exact selectedEmptyPendingRemainder_of_prefix rewards C_star C_h control0 i t q s hs
      y x hlaunch.symm (fun v hv => (hcontrols v hv).symm)

/-- The literal computed branch factors through the strict source prefix.
Launch, seed, no-cutoff tests, and actual optional views are proved to agree. -/
theorem firstLiveSourceBranch_factor (z : SourceInput p) :
    z ∈ E ↔ ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z ∈ E := by
  have hstratum := ReferenceSourcePrefixHistoryFiltration.actualLaunchStratum_factor
    rate rewards C_star C_h control0 t.val (Nat.le_of_lt t.isLt) s hs z
  constructor
  · rintro ⟨hj, hc, he, hx⟩
    obtain ⟨hcc, hec⟩ := hstratum.mp ⟨hc, he⟩
    refine ⟨hj, hcc, hec, ?_⟩
    exact (selected_branch_prefix_iff rate rewards C_star C_h control0 i t q s hs
      z hj hc he hcc hec).mp hx
  · rintro ⟨hj, hcc, hec, hy⟩
    obtain ⟨hc, he⟩ := hstratum.mpr ⟨hcc, hec⟩
    refine ⟨hj, hc, he, ?_⟩
    exact (selected_branch_prefix_iff rate rewards C_star C_h control0 i t q s hs
      z hj hc he hcc hec).mpr hy

/-- Adaptation in the analysis prefix field, which retains all original
private arrays and is not identified with the manuscript's logical field. -/
theorem firstLiveSourceBranch_measurable :
    MeasurableSet[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (t.val + 1)] E := by
  rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration_succ]
  refine ⟨E, measurableSet_firstLiveSourceBranch rate rewards C_star C_h control0 i t q s hs, ?_⟩
  ext z
  exact (firstLiveSourceBranch_factor rate rewards C_star C_h control0 i t q s hs z).symm

private theorem recordOfInput_eq
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) :
    ReferencePhysicalReleaseObservability.recordOfInput record.input = record := by
  rcases record with ⟨input, output, hout⟩
  cases hout
  rfl

/-- The full-horizon original first-live lookup is the actual calendar
lookup whenever that first-live lookup is present. -/
theorem actualRecord_eq_originalWindow (z : SourceInput p)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (he : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed = s)
    (hn : t.val - s < (ReferenceFirstLiveReleaseCylinderIntegral.originalWindow
      rate rewards C_star C_h s (by omega) z hc he).length) :
    ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z =
      some ((ReferenceFirstLiveReleaseCylinderIntegral.originalWindow
        rate rewards C_star C_h s (by omega) z hc he)[t.val - s]'hn) := by
  let seed := ReferenceFirstLiveReleaseCylinderIntegral.originalSeed rate rewards C_star C_h z hc
  have hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h = some seed := by
    exact (Option.some_get _).symm
  have hstart : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h = s := he
  have hfull : ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h =
      (ReferenceFirstLiveReleaseCylinderIntegral.originalRun
        rate rewards C_star C_h s z hc he (p.T - s) (by omega)).records := by
    rw [ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
      rate z rewards C_star C_h seed hlaunch]
    cases hstart
    rfl
  have hp := List.takeWhile_prefix
    (l := (ReferenceFirstLiveReleaseCylinderIntegral.originalRun
      rate rewards C_star C_h s z hc he (p.T - s) (by omega)).records)
    (fun record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) =>
      !ReferenceCollectionPhaseHistory.cutoffChosen record.input)
  have hindex := lt_of_lt_of_le hn hp.length_le
  rw [ReferenceSourcePrefixHistoryFiltration.actualRecord, hstart, ite_eq_left hs, hfull,
    List.getElem?_eq_getElem hindex]
  exact congrArg some (hp.getElem hn).symm

/-- On the branch, A's record is the current original-source input, with
all rows, rewards and the original private selected index restored. -/
theorem actualRecord_eq_current (z : SourceInput p) (hz : z ∈ E) :
    ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z =
      some (ReferencePhysicalReleaseObservability.recordOfInput
        (ReferenceFixedTimeSourceControlCoupling.roundInputAtSource p rate
          (β (firstLiveRemainder rate rewards C_star C_h control0 i t q s hs z hz)) z)) := by
  obtain ⟨hn, hrecord⟩ := ReferenceFirstLiveReleaseCylinderIntegral.source_current_record
    rate rewards C_star C_h q t s hs control0 i z hz.choose
      hz.choose_spec.choose hz.choose_spec.choose_spec.choose
      hz.choose_spec.choose_spec.choose_spec
  rw [actualRecord_eq_originalWindow rate rewards C_star C_h t s hs z
    hz.choose_spec.choose hz.choose_spec.choose_spec.choose hn, hrecord]
  rfl

/-- The actual live coordinator, rather than a freely supplied payload,
stores the baseline selector's whole payload under every current control. -/
theorem actual_storedPayload_eq_baseline (z : SourceInput p) (hz : z ∈ E)
    (u : TimeControl p) :
    let x := firstLiveRemainder rate rewards C_star C_h control0 i t q s hs z hz
    let hx := firstLiveRemainder_mem rate rewards C_star C_h control0 i t q s hs z hz
    let selected0 := ReferenceFirstLiveReleaseCylinderIntegral.baselineSelection
      rate rewards C_star C_h q t s hs control0 i x hx
    ReferenceAssignmentPayloadPersistence.storedPayload
      (ReferenceFirstLiveReleaseCylinderIntegral.currentInput
        rate rewards C_star C_h q t s hs control0 x u).state.coordinator =
      some selected0.view.payload := by
  intro x hx selected0
  have hn := ReferenceFirstLiveReleaseCylinderIntegral.baseline_index_lt
    rate rewards C_star C_h q t s hs control0 i x hx
  have hspec := ReferenceFirstLiveReleaseCylinderIntegral.baselineSelection_spec
    rate rewards C_star C_h q t s hs control0 i x hx
  obtain ⟨r, owned, base, hbeta, hstate, _, _, _, _, hpayload, _⟩ :=
    ReferenceFirstLiveReleaseControlTransport.retained_first_live_control_transport
      rewards C_star C_h q t s hs control0 x hn selected0 hspec.1 hspec.2.1
  change ReferenceAssignmentPayloadPersistence.storedPayload (β x).state.coordinator = _
  rw [hbeta, hstate, ReferenceAssignmentPayloadPersistence.storedPayload_live, hpayload]

/-- ALL whole controls reconstruct the same branch and the SAME actual
record. Consequently both raw flags use the actual stored payload. -/
theorem actual_flags_eq_retained_flags (z : SourceInput p) (hz : z ∈ E)
    (u : TimeControl p) :
    let x := firstLiveRemainder rate rewards C_star C_h control0 i t q s hs z hz
    let hx := firstLiveRemainder_mem rate rewards C_star C_h control0 i t q s hs z hz
    let selected0 := ReferenceFirstLiveReleaseCylinderIntegral.baselineSelection
      rate rewards C_star C_h q t s hs control0 i x hx
    let zu := ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z u
    ∃ hu : t.val - s < (W x u).length,
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t zu =
        some ((W x u)[t.val - s]'hu) ∧
      ReferenceAssignmentPayloadPersistence.storedPayload ((W x u)[t.val - s]'hu).input.state.coordinator =
        some selected0.view.payload ∧
      ReferenceSourcePrefixHistoryFiltration.actualUp rate rewards C_star C_h i t zu =
        ReferencePhysicalReleaseQuota.upFlag selected0.view.payload ((W x u)[t.val - s]'hu) i ∧
      ReferenceSourcePrefixHistoryFiltration.actualData rate rewards C_star C_h i t zu =
        ReferencePhysicalReleaseQuota.dataFlag selected0.view.payload ((W x u)[t.val - s]'hu) i := by
  intro x hx selected0 zu
  obtain ⟨hzu, hxu⟩ := firstLiveSourceBranch_replace
    rate rewards C_star C_h control0 i t q s hs z hz u
  have hrecord := actualRecord_eq_current rate rewards C_star C_h control0 i t q s hs zu hzu
  rw [hxu] at hrecord
  have hj : ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p z = q :=
    (ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex p z).trans hz.choose
  have hsource := ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_replaceSourceControl
    p q t z u hj
  have hsource' : ReferenceGeneratedActivePrefixFactor.splitSource q t u x.val = zu := hsource
  have hinput : ReferenceFirstLiveReleaseCylinderIntegral.currentInput
      rate rewards C_star C_h q t s hs control0 x u =
        ReferenceFixedTimeSourceControlCoupling.roundInputAtSource p rate (β x) zu := by
    rw [ReferenceFirstLiveReleaseCylinderIntegral.currentInput_eq_next,
      ReferenceRetainedBoundaryMeasurability.retainedGeneratedNextInput_eq_roundInputAtSource,
      hsource']
  obtain ⟨_, hcontrols⟩ := ReferenceFirstLiveReleaseCylinderIntegral.baselineSelection_all_controls
    rate rewards C_star C_h q t s hs control0 i x hx
  obtain ⟨hu, selectedU, hwu, _, _, _, _, _⟩ := hcontrols u
  have hactual : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t zu =
      some ((W x u)[t.val - s]'hu) := by
    rw [hrecord, ← hinput, ← hwu, recordOfInput_eq]
  have hpayload : ReferenceAssignmentPayloadPersistence.storedPayload
      ((W x u)[t.val - s]'hu).input.state.coordinator = some selected0.view.payload := by
    rw [hwu]
    exact actual_storedPayload_eq_baseline rate rewards C_star C_h control0 i t q s hs z hz u
  refine ⟨hu, hactual, hpayload, ?_, ?_⟩
  · simp only [ReferenceSourcePrefixHistoryFiltration.actualUp, hactual,
      Option.bind_some, hpayload, Option.map_some, Option.getD_some]
  · simp only [ReferenceSourcePrefixHistoryFiltration.actualData, hactual,
      Option.bind_some, hpayload, Option.map_some, Option.getD_some]

private theorem actual_source_flag_iff_window (up : Bool) (z : SourceInput p)
    (hj : ActualInitializationPhysicalStep.selectedRowIndex p z = q)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (he : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed = s)
    (hx : ReferenceRetainedBoundaryMeasurability.retainedLaunchStartInputOfSource
      rate rewards C_star C_h q t s hs control0 z hj hc he ∈ S) :
    let x := ReferenceRetainedBoundaryMeasurability.retainedLaunchStartInputOfSource
      rate rewards C_star C_h q t s hs control0 z hj hc he
    (if up then ReferenceSourcePrefixHistoryFiltration.actualUp rate rewards C_star C_h i t z
      else ReferenceSourcePrefixHistoryFiltration.actualData rate rewards C_star C_h i t z) = true ↔
      ∃ payload, ReferenceFirstLiveReleaseCylinderIntegral.baselinePayload
        rate rewards C_star C_h q t s hs control0 x = some payload ∧
      ∃ hn : t.val - s < (ReferenceFirstLiveReleaseCylinderIntegral.originalWindow
        rate rewards C_star C_h s (by omega) z hc he).length,
        ReferenceFirstLiveReleaseCylinderIntegral.physicalFlag rate up payload
          ((ReferenceFirstLiveReleaseCylinderIntegral.originalWindow
            rate rewards C_star C_h s (by omega) z hc he)[t.val - s]'hn) i = true := by
  intro x
  let hz : z ∈ E := ⟨hj, hc, he, hx⟩
  let selected0 := ReferenceFirstLiveReleaseCylinderIntegral.baselineSelection
    rate rewards C_star C_h q t s hs control0 i x hx
  have hbase := (ReferenceFirstLiveReleaseCylinderIntegral.baselineSelection_all_controls
    rate rewards C_star C_h q t s hs control0 i x hx).1
  obtain ⟨hn, hcurrent⟩ := ReferenceFirstLiveReleaseCylinderIntegral.source_current_record
    rate rewards C_star C_h q t s hs control0 i z hj hc he hx
  have hstored : ReferenceAssignmentPayloadPersistence.storedPayload
      (β x).state.coordinator = some selected0.view.payload :=
    actual_storedPayload_eq_baseline rate rewards C_star C_h control0 i t q s hs z hz control0
  have hstoredRecord : ReferenceAssignmentPayloadPersistence.storedPayload
      ((ReferenceFirstLiveReleaseCylinderIntegral.originalWindow
        rate rewards C_star C_h s (by omega) z hc he)[t.val - s]'hn).input.state.coordinator =
      some selected0.view.payload := by
    rw [hcurrent]
    exact hstored
  have hactual := actualRecord_eq_originalWindow rate rewards C_star C_h t s hs z hc he hn
  have hflag : (if up then ReferenceSourcePrefixHistoryFiltration.actualUp rate rewards C_star C_h i t z
      else ReferenceSourcePrefixHistoryFiltration.actualData rate rewards C_star C_h i t z) =
      ReferenceFirstLiveReleaseCylinderIntegral.physicalFlag rate up selected0.view.payload
        ((ReferenceFirstLiveReleaseCylinderIntegral.originalWindow
          rate rewards C_star C_h s (by omega) z hc he)[t.val - s]'hn) i := by
    cases up
    · change ReferenceSourcePrefixHistoryFiltration.actualData rate rewards C_star C_h i t z = _
      simp only [ReferenceSourcePrefixHistoryFiltration.actualData, hactual, Option.bind_some,
        hstoredRecord, Option.map_some, Option.getD_some]
      rfl
    · change ReferenceSourcePrefixHistoryFiltration.actualUp rate rewards C_star C_h i t z = _
      simp only [ReferenceSourcePrefixHistoryFiltration.actualUp, hactual, Option.bind_some,
        hstoredRecord, Option.map_some, Option.getD_some]
      rfl
  constructor
  · intro hf
    exact ⟨selected0.view.payload, hbase, hn, hflag.symm.trans hf⟩
  · rintro ⟨payload, hpayload, hn', hf⟩
    have heq : selected0.view.payload = payload := Option.some.inj (hbase.symm.trans hpayload)
    subst payload
    rw [hflag]
    exact hf

/-- R's original-source cylinder is exactly the literal computed branch
intersected with A's actual raw flag. The measure remains unnormalized. -/
theorem sourceCylinder_eq_actual_flag_branch (up : Bool) :
    ReferenceFirstLiveReleaseCylinderIntegral.sourceCylinder
      rate rewards C_star C_h q t s hs control0 up i Set.univ =
      E ∩ {z | (if up then ReferenceSourcePrefixHistoryFiltration.actualUp
        rate rewards C_star C_h i t z else ReferenceSourcePrefixHistoryFiltration.actualData
          rate rewards C_star C_h i t z) = true} := by
  ext z
  constructor
  · rintro ⟨hj, hc, he, hx, hwindow⟩
    exact ⟨⟨hj, hc, he, hx.2⟩,
      (actual_source_flag_iff_window rate rewards C_star C_h control0 i t q s hs
        up z hj hc he hx.2).mpr hwindow⟩
  · rintro ⟨⟨hj, hc, he, hx⟩, hflag⟩
    exact ⟨hj, hc, he, ⟨Set.mem_univ _, hx⟩,
      (actual_source_flag_iff_window rate rewards C_star C_h control0 i t q s hs
        up z hj hc he hx).mp hflag⟩

/-- Flags after current-control replacement depend on the prefix THROUGH
the current round. Future table-bearing records are never equated. -/
theorem actual_flags_after_prefix_restore (z : SourceInput p) (u : TimeControl p) :
    let zu := ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z u
    let cu := ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z) u
    ReferenceSourcePrefixHistoryFiltration.actualUp rate rewards C_star C_h i t zu =
        ReferenceSourcePrefixHistoryFiltration.actualUp rate rewards C_star C_h i t cu ∧
      ReferenceSourcePrefixHistoryFiltration.actualData rate rewards C_star C_h i t zu =
        ReferenceSourcePrefixHistoryFiltration.actualData rate rewards C_star C_h i t cu ∧
      ReferenceSourcePrefixHistoryFiltration.actualRelease rate rewards C_star C_h i t zu =
        ReferenceSourcePrefixHistoryFiltration.actualRelease rate rewards C_star C_h i t cu := by
  intro zu cu
  have hprefix : ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 (t.val + 1) zu = cu := by
    rw [ReferenceSourcePrefixHistoryFiltration.prefix_successor_restore,
      sourcePrefix_replace_current]
    have hcurrent : (zu.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p zu)).2 t = u := by
      simp only [zu, ReferenceFixedTimeSourceControlCoupling.replaceSourceControl,
        ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex,
        ActualInitializationPhysicalStep.selectedRowIndex, Function.update_self]
    rw [hcurrent]
  have hflags := ReferenceSourcePrefixHistoryFiltration.flags_factor
    rate rewards C_star C_h control0 i t zu
  rw [hprefix] at hflags
  exact hflags

/-- The actual replaced-source flag is exactly R's joint-event section. -/
theorem jointEvent_iff_actual_flag (z : SourceInput p) (hz : z ∈ E)
    (up : Bool) (u : TimeControl p) :
    let x := firstLiveRemainder rate rewards C_star C_h control0 i t q s hs z hz
    (x, u) ∈ ReferenceFirstLiveReleaseCylinderIntegral.jointEvent
      rate rewards C_star C_h q t s hs control0 up i ↔
      (if up then ReferenceSourcePrefixHistoryFiltration.actualUp rate rewards C_star C_h i t
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z u)
      else ReferenceSourcePrefixHistoryFiltration.actualData rate rewards C_star C_h i t
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z u)) = true := by
  intro x
  have hx := firstLiveRemainder_mem rate rewards C_star C_h control0 i t q s hs z hz
  let selected0 := ReferenceFirstLiveReleaseCylinderIntegral.baselineSelection
    rate rewards C_star C_h q t s hs control0 i x hx
  have hn := ReferenceFirstLiveReleaseCylinderIntegral.baseline_index_lt
    rate rewards C_star C_h q t s hs control0 i x hx
  have hspec := ReferenceFirstLiveReleaseCylinderIntegral.baselineSelection_spec
    rate rewards C_star C_h q t s hs control0 i x hx
  obtain ⟨hu, _, _, hup, hdata⟩ := actual_flags_eq_retained_flags
    rate rewards C_star C_h control0 i t q s hs z hz u
  have hflag : (if up then ReferenceSourcePrefixHistoryFiltration.actualUp rate rewards C_star C_h i t
      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z u)
    else ReferenceSourcePrefixHistoryFiltration.actualData rate rewards C_star C_h i t
      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z u)) =
      ReferenceFirstLiveReleaseCylinderIntegral.physicalFlag rate up selected0.view.payload
        ((W x u)[t.val - s]'hu) i := by
    cases up
    · exact hdata
    · exact hup
  constructor
  · rintro ⟨_, hn', selected', hselected', hu', hf⟩
    have heq := ReferenceFirstLiveReleaseCylinderIntegral.baselineSelection_eq
      rate rewards C_star C_h q t s hs control0 i x hx hn' selected' hselected'
    subst selected'
    rw [hflag]
    exact hf
  · intro hf
    exact ⟨hx, hn, selected0, hspec.1, hu, hflag.symm.trans hf⟩

private theorem bool_indicator_eq {α : Type*} (f : α → Bool) (event : Set α)
    (h : ∀ u, u ∈ event ↔ f u = true) :
    (fun u => if f u then (1 : ℝ) else 0) = event.indicator (fun _ => 1) := by
  funext u
  by_cases hu : u ∈ event
  · rw [Set.indicator_of_mem hu, (h u).mp hu]
    rfl
  · rw [Set.indicator_of_notMem hu]
    have hf : f u = false := Bool.eq_false_iff.mpr (mt (h u).mpr hu)
    rw [hf]
    rfl

/-- Restore the literal integration argument of A without equating full
sources or their future records. -/
theorem jointEvent_iff_actual_prefix_flag (z : SourceInput p) (hz : z ∈ E)
    (up : Bool) (u : TimeControl p) :
    let x := firstLiveRemainder rate rewards C_star C_h control0 i t q s hs z hz
    (x, u) ∈ ReferenceFirstLiveReleaseCylinderIntegral.jointEvent
      rate rewards C_star C_h q t s hs control0 up i ↔
      (if up then ReferenceSourcePrefixHistoryFiltration.actualUp rate rewards C_star C_h i t
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
          (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z) u)
      else ReferenceSourcePrefixHistoryFiltration.actualData rate rewards C_star C_h i t
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
          (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z) u)) = true := by
  intro x
  apply Iff.trans (jointEvent_iff_actual_flag rate rewards C_star C_h control0 i t q s hs z hz up u)
  have hrestore := actual_flags_after_prefix_restore rate rewards C_star C_h control0 i t z u
  cases up
  · exact Iff.of_eq (congrArg (fun b : Bool => b = true) hrestore.2.1)
  · exact Iff.of_eq (congrArg (fun b : Bool => b = true) hrestore.1)

private theorem integral_bool_test {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : α → Bool) (event : Set α)
    (hmeas : MeasurableSet event) (h : ∀ u, u ∈ event ↔ f u = true) :
    (∫ u, (if f u then (1 : ℝ) else 0) ∂μ) = (μ event).toReal := by
  rw [bool_indicator_eq f event h]
  exact integral_indicator_one hmeas

/-- A's exact UP integral is the real mass of the genuine joint section. -/
theorem actual_up_section_eq_sliceMass (z : SourceInput p) (hz : z ∈ E) :
    let x := firstLiveRemainder rate rewards C_star C_h control0 i t q s hs z hz
    ReferenceSourcePhysicalFlagConditionalLaw.actualUpControlSection
        rate rewards C_star C_h control0 i t z =
      (ReferenceFirstLiveReleaseCylinderIntegral.sliceMass
        rate rewards C_star C_h q t s hs control0 true i x).toReal := by
  intro x
  unfold ReferenceSourcePhysicalFlagConditionalLaw.actualUpControlSection
  rw [ReferenceSourcePhysicalFlagConditionalLaw.c_t_eq_sourcePrefix]
  exact integral_bool_test (ContinuousLearningRows.timeControlLaw p)
    (fun u => ReferenceSourcePrefixHistoryFiltration.actualUp rate rewards C_star C_h i t
      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z) u))
    (Prod.mk x ⁻¹' ReferenceFirstLiveReleaseCylinderIntegral.jointEvent
      rate rewards C_star C_h q t s hs control0 true i)
    ((ReferenceFirstLiveReleaseCylinderIntegral.measurableSet_jointEvent
      rate rewards C_star C_h q t s hs control0 true i).preimage measurable_prodMk_left)
    (fun u => jointEvent_iff_actual_prefix_flag
      rate rewards C_star C_h control0 i t q s hs z hz true u)

/-- A's exact DATA integral has the same whole-control section carrier. -/
theorem actual_data_section_eq_sliceMass (z : SourceInput p) (hz : z ∈ E) :
    let x := firstLiveRemainder rate rewards C_star C_h control0 i t q s hs z hz
    ReferenceSourcePhysicalFlagConditionalLaw.actualDataControlSection
        rate rewards C_star C_h control0 i t z =
      (ReferenceFirstLiveReleaseCylinderIntegral.sliceMass
        rate rewards C_star C_h q t s hs control0 false i x).toReal := by
  intro x
  unfold ReferenceSourcePhysicalFlagConditionalLaw.actualDataControlSection
  rw [ReferenceSourcePhysicalFlagConditionalLaw.c_t_eq_sourcePrefix]
  exact integral_bool_test (ContinuousLearningRows.timeControlLaw p)
    (fun u => ReferenceSourcePrefixHistoryFiltration.actualData rate rewards C_star C_h i t
      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z) u))
    (Prod.mk x ⁻¹' ReferenceFirstLiveReleaseCylinderIntegral.jointEvent
      rate rewards C_star C_h q t s hs control0 false i)
    ((ReferenceFirstLiveReleaseCylinderIntegral.measurableSet_jointEvent
      rate rewards C_star C_h q t s hs control0 false i).preimage measurable_prodMk_left)
    (fun u => jointEvent_iff_actual_prefix_flag
      rate rewards C_star C_h control0 i t q s hs z hz false u)

/-- Both exact sections, without altering either raw section off E. -/
theorem actual_up_data_sections_eq_sliceMass (z : SourceInput p) (hz : z ∈ E) :
    let x := firstLiveRemainder rate rewards C_star C_h control0 i t q s hs z hz
    ReferenceSourcePhysicalFlagConditionalLaw.actualUpControlSection
        rate rewards C_star C_h control0 i t z =
      (ReferenceFirstLiveReleaseCylinderIntegral.sliceMass
        rate rewards C_star C_h q t s hs control0 true i x).toReal ∧
    ReferenceSourcePhysicalFlagConditionalLaw.actualDataControlSection
        rate rewards C_star C_h control0 i t z =
      (ReferenceFirstLiveReleaseCylinderIntegral.sliceMass
        rate rewards C_star C_h q t s hs control0 false i x).toReal :=
  ⟨actual_up_section_eq_sliceMass rate rewards C_star C_h control0 i t q s hs z hz,
    actual_data_section_eq_sliceMass rate rewards C_star C_h control0 i t q s hs z hz⟩

private theorem release_indicator_add
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) :
    (if ReferencePhysicalReleaseQuota.releaseFlag payload record i then (1 : ℝ) else 0) =
      (if ReferencePhysicalReleaseQuota.upFlag payload record i then (1 : ℝ) else 0) +
      (if ReferencePhysicalReleaseQuota.dataFlag payload record i then (1 : ℝ) else 0) := by
  cases hrelease : ReferencePhysicalReleaseQuota.releaseFlag payload record i with
  | false =>
      simp only [ReferencePhysicalReleaseQuota.upFlag, ReferencePhysicalReleaseQuota.dataFlag,
        hrelease, Bool.false_and, Bool.false_eq_true, ite_false, add_zero]
  | true =>
      have hcondition := of_decide_eq_true hrelease
      change ActiveFollowerLifecycle.releaseCondition rate.eta i
        (ActiveFollowerLifecycle.publicRowOfCompleteRow record.input.row record.input.time)
        (record.ownEntries (PublicDiscreteDraws.followerPlayer p.two_le_m i)).2
        (payload.downRecord i) at hcondition
      have hslot : PublicDiscreteDraws.slotDraw (record.input.row.2 record.input.time).1 =
          PublicDiscreteDraws.upSlot ∨
        PublicDiscreteDraws.slotDraw (record.input.row.2 record.input.time).1 =
          PublicDiscreteDraws.dataSlot := hcondition.2.elim
            (fun hup => Or.inl hup.1) (fun hdata => Or.inr hdata.1)
      have hne : PublicDiscreteDraws.upSlot ≠ PublicDiscreteDraws.dataSlot := by decide
      rcases hslot with hup | hdata
      · have hdata : PublicDiscreteDraws.slotDraw (record.input.row.2 record.input.time).1 ≠
            PublicDiscreteDraws.dataSlot := fun h => hne (hup.symm.trans h)
        have huf : ReferencePhysicalReleaseQuota.upFlag payload record i = true := by
          simp only [ReferencePhysicalReleaseQuota.upFlag, hrelease, Bool.true_and, hup, decide_true]
        have hdf : ReferencePhysicalReleaseQuota.dataFlag payload record i = false := by
          simp only [ReferencePhysicalReleaseQuota.dataFlag, hrelease, Bool.true_and, hdata, decide_false]
        rw [huf, hdf]
        norm_num
      · have hup : PublicDiscreteDraws.slotDraw (record.input.row.2 record.input.time).1 ≠
            PublicDiscreteDraws.upSlot := fun h => hne (h.symm.trans hdata)
        have huf : ReferencePhysicalReleaseQuota.upFlag payload record i = false := by
          simp only [ReferencePhysicalReleaseQuota.upFlag, hrelease, Bool.true_and, hup, decide_false]
        have hdf : ReferencePhysicalReleaseQuota.dataFlag payload record i = true := by
          simp only [ReferencePhysicalReleaseQuota.dataFlag, hrelease, Bool.true_and, hdata, decide_true]
        rw [huf, hdf]
        norm_num

private theorem option_release_indicator_add
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (payload : Option (ReferenceActivePhysicalStep.Payload rate)) :
    (if (payload.map (fun M => ReferencePhysicalReleaseQuota.releaseFlag M record i)).getD false
      then (1 : ℝ) else 0) =
    (if (payload.map (fun M => ReferencePhysicalReleaseQuota.upFlag M record i)).getD false
      then (1 : ℝ) else 0) +
    (if (payload.map (fun M => ReferencePhysicalReleaseQuota.dataFlag M record i)).getD false
      then (1 : ℝ) else 0) := by
  cases payload with
  | none => norm_num
  | some M => exact release_indicator_add rate i M record

/-- The raw release observation is the sum of its disjoint UP and DATA
indicators, including absent-record and absent-payload paths. -/
theorem actual_release_indicator_add (z : SourceInput p) :
    (if ReferenceSourcePrefixHistoryFiltration.actualRelease rate rewards C_star C_h i t z
      then (1 : ℝ) else 0) =
    (if ReferenceSourcePrefixHistoryFiltration.actualUp rate rewards C_star C_h i t z
      then (1 : ℝ) else 0) +
    (if ReferenceSourcePrefixHistoryFiltration.actualData rate rewards C_star C_h i t z
      then (1 : ℝ) else 0) := by
  unfold ReferenceSourcePrefixHistoryFiltration.actualRelease
    ReferenceSourcePrefixHistoryFiltration.actualUp ReferenceSourcePrefixHistoryFiltration.actualData
  cases hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z with
  | none => norm_num
  | some record =>
      simp only [Option.bind_some]
      exact option_release_indicator_add rate i record
        (ReferenceAssignmentPayloadPersistence.storedPayload record.input.state.coordinator)

/-- Integrate the exact disjoint release decomposition. This identity does
not change the raw section values away from the computed first-live branch. -/
theorem actual_release_section_add (z : SourceInput p) :
    ReferenceSourcePhysicalFlagConditionalLaw.actualReleaseControlSection
      rate rewards C_star C_h control0 i t z =
    ReferenceSourcePhysicalFlagConditionalLaw.actualUpControlSection
      rate rewards C_star C_h control0 i t z +
    ReferenceSourcePhysicalFlagConditionalLaw.actualDataControlSection
      rate rewards C_star C_h control0 i t z := by
  let c := ReferenceSourceCurrentControlFreshness.c_t p control0 t z
  let fup := fun u => ReferenceSourcePhysicalFlagConditionalLaw.actualUpControlSectionIntegrand
    rate rewards C_star C_h i t (c, u)
  let fdata := fun u => ReferenceSourcePhysicalFlagConditionalLaw.actualDataControlSectionIntegrand
    rate rewards C_star C_h i t (c, u)
  have hmu : Measurable fup :=
    (ReferenceSourcePhysicalFlagConditionalLaw.actualUpControlSectionIntegrand_measurable
      rate rewards C_star C_h control0 i t).comp measurable_prodMk_left
  have hmd : Measurable fdata :=
    (ReferenceSourcePhysicalFlagConditionalLaw.actualDataControlSectionIntegrand_measurable
      rate rewards C_star C_h control0 i t).comp measurable_prodMk_left
  have hiu : Integrable fup (ContinuousLearningRows.timeControlLaw p) :=
    (integrable_const (1 : ℝ)).mono' hmu.aestronglyMeasurable (Filter.Eventually.of_forall (fun u => by
      dsimp only [fup, ReferenceSourcePhysicalFlagConditionalLaw.actualUpControlSectionIntegrand]
      split <;> norm_num))
  have hid : Integrable fdata (ContinuousLearningRows.timeControlLaw p) :=
    (integrable_const (1 : ℝ)).mono' hmd.aestronglyMeasurable (Filter.Eventually.of_forall (fun u => by
      dsimp only [fdata, ReferenceSourcePhysicalFlagConditionalLaw.actualDataControlSectionIntegrand]
      split <;> norm_num))
  calc
    _ = ∫ u, (fup u + fdata u) ∂ContinuousLearningRows.timeControlLaw p := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun u => actual_release_indicator_add rate rewards C_star C_h i t
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t c u))
    _ = _ := integral_add hiu hid

/-- The actual three control sections and the UP lower bound on the literal
first-live branch. The exposed `upReleaseMassFormula` is exactly
`chi(row,e) * (1 - qGamma(v,w,U,e)) / (4*(m-1)*K)`, with the computed
selector's complete weights. Validity and auxiliary minimality are produced
in the proof; neither is a caller premise. -/
theorem actual_control_sections_on_first_live_branch :
    ∀ z : SourceInput p, ∀ hz : z ∈ E,
    let x := firstLiveRemainder rate rewards C_star C_h control0 i t q s hs z hz
    let hx := firstLiveRemainder_mem rate rewards C_star C_h control0 i t q s hs z hz
    let selected0 := ReferenceFirstLiveReleaseCylinderIntegral.baselineSelection
      rate rewards C_star C_h q t s hs control0 i x hx
    let hvalid := ReferenceFirstLiveReleaseCylinderIntegral.baselineSelection_valid
      rate rewards C_star C_h q t s hs control0 i x hx
    let row := ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t
    let upMass := ReferenceFirstLiveReleaseSliceMass.upReleaseMassFormula selected0 hvalid row
    let dataMass := ReleaseRoundKernel.chi row (selected0.view.payload.assignment.assigned i) /
      (2 * (p.K : ℝ))
    ReferenceSourcePhysicalFlagConditionalLaw.actualUpControlSection
        rate rewards C_star C_h control0 i t z = upMass ∧
      ReferenceSourcePhysicalFlagConditionalLaw.actualDataControlSection
        rate rewards C_star C_h control0 i t z = dataMass ∧
      ReferenceSourcePhysicalFlagConditionalLaw.actualReleaseControlSection
        rate rewards C_star C_h control0 i t z = upMass + dataMass ∧
      ReleaseRoundKernel.chi row selected0.view.payload.assignment.auxiliary /
          (12 * (p.m - 1 : ℝ) * (p.K : ℝ)) ≤
        ReferenceSourcePhysicalFlagConditionalLaw.actualUpControlSection
          rate rewards C_star C_h control0 i t z := by
  intro z hz x hx selected0 hvalid row upMass dataMass
  let payload := selected0.view.payload
  let e := ReleaseRoundKernel.auxiliaryFastArm payload.assignment payload.slowSet
    payload.assignment_image.symm
  have haux : e.val = payload.auxiliaryArm := rfl
  have hmin : ∀ j : CanonicalFastSampling.FastArm payload.slowSet,
      payload.anchor e.val ≤ payload.anchor j.val := by
    intro j
    rw [haux]
    exact payload.auxiliaryArm_anchor_minimum j.val j.property
  have hq := CanonicalFastSampling.qGamma_auxiliary_arm_le_two_thirds
    p rate.eta.property payload.eta_le_source_cap payload.anchor
    (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights selected0) payload.anchor_pos
    (fun a => (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights_bounds selected0 hvalid a).1)
    (fun a => (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights_bounds selected0 hvalid a).2.1)
    (fun a => (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights_bounds selected0 hvalid a).2.2)
    payload.slowSet e hmin
  have hchi : ∀ a, 0 ≤ ReleaseRoundKernel.chi row a := by
    intro a
    unfold ReleaseRoundKernel.chi
    split <;> norm_num
  have hm : (2 : ℝ) ≤ p.m := by exact_mod_cast p.two_le_m
  have hd : (0 : ℝ) ≤ p.m - 1 := by linarith only [hm]
  have hupNonneg : 0 ≤ upMass := by
    change 0 ≤ ReferenceFirstLiveReleaseSliceMass.upReleaseMassFormula selected0 hvalid row
    unfold ReferenceFirstLiveReleaseSliceMass.upReleaseMassFormula
    exact div_nonneg (mul_nonneg (hchi _) (sub_nonneg.mpr (hq.trans (by norm_num))))
      (mul_nonneg (mul_nonneg (by norm_num) hd) (Nat.cast_nonneg _))
  have hdataNonneg : 0 ≤ dataMass :=
    div_nonneg (hchi _) (by positivity)
  have hlowerNonneg : 0 ≤ ReleaseRoundKernel.chi row payload.assignment.auxiliary /
      (12 * (p.m - 1 : ℝ) * (p.K : ℝ)) :=
    div_nonneg (hchi _) (mul_nonneg (mul_nonneg (by norm_num) hd) (Nat.cast_nonneg _))
  have hmass := ReferenceFirstLiveReleaseCylinderIntegral.sliceMass_eq_closed
    rate rewards C_star C_h q t s hs control0 i x
  have hup : ReferenceSourcePhysicalFlagConditionalLaw.actualUpControlSection
      rate rewards C_star C_h control0 i t z = upMass := by
    rw [actual_up_section_eq_sliceMass rate rewards C_star C_h control0 i t q s hs z hz,
      hmass.1, ReferenceFirstLiveReleaseCylinderIntegral.upClosedMass, dite_eq_left hx]
    exact ENNReal.toReal_ofReal hupNonneg
  have hdata : ReferenceSourcePhysicalFlagConditionalLaw.actualDataControlSection
      rate rewards C_star C_h control0 i t z = dataMass := by
    rw [actual_data_section_eq_sliceMass rate rewards C_star C_h control0 i t q s hs z hz,
      hmass.2.1, ReferenceFirstLiveReleaseCylinderIntegral.dataClosedMass, dite_eq_left hx]
    exact ENNReal.toReal_ofReal hdataNonneg
  have hfinite : ReferenceFirstLiveReleaseCylinderIntegral.upClosedMass
      rate rewards C_star C_h q t s hs control0 i x ≠ ⊤ := by
    rw [ReferenceFirstLiveReleaseCylinderIntegral.upClosedMass, dite_eq_left hx]
    exact ENNReal.ofReal_ne_top
  have hbound := ENNReal.toReal_mono hfinite hmass.2.2
  have hx' : x ∈ S := hx
  simp only [ReferenceFirstLiveReleaseCylinderIntegral.upLowerMass,
    ReferenceFirstLiveReleaseCylinderIntegral.upClosedMass, dite_eq_left hx'] at hbound
  rw [ENNReal.toReal_ofReal hlowerNonneg, ENNReal.toReal_ofReal hupNonneg] at hbound
  refine ⟨hup, hdata, ?_, ?_⟩
  · rw [actual_release_section_add, hup, hdata]
  · rw [hup]
    exact hbound

end Bandits.Support.ReferenceFirstLiveActualFlagSections

end
