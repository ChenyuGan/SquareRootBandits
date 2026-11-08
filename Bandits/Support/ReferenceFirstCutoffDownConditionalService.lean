/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bandits Lean regret formalization contributors.
-/
module

public import Bandits.Support.ReferenceFirstCollectionDownConditionalService
public import Bandits.Support.ReferenceFirstCutoffDownFreshGeometry

import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Positivity

/-!
# Actual first-cutoff old-DOWN conditional service

Sources: `sources/zip4/manuscript/06_interruptions.tex:459-490`,
`sources/zip4/manuscript/05_binary_transport.tex:20-53,70-124`,
`sources/zip4/manuscript/07_public_setup.tex:127-164`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-79,92-157`.

This joins the produced first-cutoff geometry to the existing actual
collection DOWN readout, fixed-word service law, and full-current-control
conditional expectation. Its hypotheses are the actual initialization
crossing and finite first-run span; it is an internal conditional result, not a
manuscript closure or a stopped-stage allowance.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ContinuousLearningRows
open Bandits.Support.PublicDiscreteDraws
open Bandits.Support.OrderedTupleSampler
open Bandits.Support.AffineChannelLaw
open Bandits.Support.ReferenceFirstCollectionDownConditionalService
open Bandits.Support.ReferenceFirstCutoffDownFreshGeometry
open ProbabilityTheory
open scoped BigOperators ENNReal

namespace Bandits.Support.ReferenceFirstCutoffDownConditionalService

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput
abbrev RewardTable := ActualInitializationPhysicalStep.GridRewardTable
abbrev TimeControl := ContinuousLearningRows.TimeControl

variable {p : Parameters}

/-- On one source null set, every actual first-cutoff old-DOWN branch has the
fixed-word fresh-control law and the corresponding `m_t` conditional
expectation. The source, full reward table, both constants, and baseline
control are fixed before that null set. -/
theorem actual_first_cutoff_down_condExp_service
    (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ)
    (control0 : TimeControl p) :
    ∀ᵐ source ∂BootstrapPrivateRoundStreams.sourceInputLaw p,
    ∀ (count : ℕ)
      (hcross : (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
      (hspan : ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed +
            count ≤ p.T)
      (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
          rate source rewards C_star C_h hcross count hspan).records).length < count),
    let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
      rate source rewards C_star C_h hcross count hspan
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length
    let B := ReferenceCollectionPhaseHistory.collectionWindow E.records w
    ∃ d : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
        source rewards C_star C_h count hcross hspan hshort,
      let x := d.stream.cutoff.cut.input
      d.stream.window = B ∧
      d.stream.window[0]'d.stream.windowNonempty = d.stream.cutoff.cut ∧
      x.time.val = ReferenceFirstCollectionReadyStream.startTime (rate := rate)
        source rewards C_star C_h + w ∧
      x.rows = source.1.2 ∧
      x.selected = ActualInitializationPhysicalStep.selectedRowIndex p source ∧
      x.rewards = rewards ∧
      ∃ (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
        (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
        (base : Fin (p.m - 1) → ℕ)
        (old : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
        (memory : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p),
      x.state.coordinator = .live r q base ∧ d.stream.payload = r.payload ∧
      (∀ j, x.state.followers j = .ordinary (old j) (memory j) ∧
        let cj : ReferencePrelaunchFollower.State p rate.eta :=
          { old j with status := .unoccupied }
        cj.lastDown = (old j).lastDown ∧ cj.S = (old j).S ∧
        cj.delta = (old j).delta ∧ cj.backlog = (old j).backlog ∧
        cj.buffer = (old j).buffer ∧ cj.downBatch = (old j).downBatch ∧
        cj.initializationFailure = (old j).initializationFailure ∧
        ActiveFollowerLifecycle.localStateDomainValid cj ∧
        ActiveFollowerLifecycle.startRound rate.eta x.time (old j) (memory j) =
          .ok (cj, memory j)) ∧
      ∀ i : Fin (p.m - 1), (old i).lastDown = none →
      ∃ wD : AffineChannelLaw.Word (AffineBatchDecoder.width p),
        wD = CoordinatorLocalArmChoice.storedDownFlatWord r.payload i ∧
        ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
          x.time source = some d.stream.cutoff.cut ∧
        (∀ c : TimeControl p,
          c ∈ freshCoordinatorDownServiceSet x i ↔
            c ∈ downServiceFormulaSet rewards x.time i wD) ∧
        (ContinuousLearningRows.timeControlLaw p)
          (freshCoordinatorDownServiceSet x i) =
          ENNReal.ofReal ((ReferenceFirstCollectionUpConditionalService.positiveRewardCount
            rewards x.time : ℝ) / (8 * (p.m - 1 : ℝ) * p.K)) ∧
        actualFirstCollectionDownFreshSection (rate := rate) rewards C_star C_h
          control0 i x.time source =
          (ReferenceFirstCollectionUpConditionalService.positiveRewardCount
            rewards x.time : ℝ) / (8 * (p.m - 1 : ℝ) * p.K) ∧
        (BootstrapPrivateRoundStreams.sourceInputLaw p)[
          actualFirstCollectionDownReadout (rate := rate) rewards C_star C_h i x.time |
            ReferenceSourceCurrentControlFreshness.m_t p control0 x.time] source =
          (ReferenceFirstCollectionUpConditionalService.positiveRewardCount
            rewards x.time : ℝ) / (8 * (p.m - 1 : ℝ) * p.K) := by
  classical
  have hce : ∀ᵐ source ∂BootstrapPrivateRoundStreams.sourceInputLaw p,
      ∀ i : Fin (p.m - 1), ∀ t : Fin p.T,
      (BootstrapPrivateRoundStreams.sourceInputLaw p)[
        actualFirstCollectionDownReadout (rate := rate) rewards C_star C_h i t |
          ReferenceSourceCurrentControlFreshness.m_t p control0 t] source =
        actualFirstCollectionDownFreshSection (rate := rate)
          rewards C_star C_h control0 i t source :=
    ae_all_iff.mpr fun i => ae_all_iff.mpr fun t =>
      ReferenceFirstCollectionDownConditionalService.actual_first_collection_down_condExp
        rewards C_star C_h control0 i t
  filter_upwards [hce] with source hce
  intro count hcross hspan hshort E w B
  obtain ⟨d, hwindow, hhead, htime, hrows, hselected, hrew, r, q, base,
    old, memory, hphase, hpayload, hfamily, hservice⟩ :=
    ReferenceFirstCutoffDownFreshGeometry.actual_first_cutoff_down_control_geometry
      rate source rewards C_star C_h count hcross hspan hshort
  let x := d.stream.cutoff.cut.input
  let initial := ReferenceFirstCollectionEpochAlignment.actualLaunchState
    rate source rewards C_star C_h hcross
  let start := ReferenceFirstCollectionReadyStream.startTime (rate := rate)
    source rewards C_star C_h
  have hactive : ReferenceActivePhysicalHorizon.allActiveAtStart initial start := by
    simpa only [initial, start, ReferenceFirstCollectionReadyStream.startTime] using
      (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
        rate source rewards C_star C_h hcross).1
  have hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h = some initial :=
    Option.eq_some_of_isSome ((ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
      rate source rewards C_star C_h).2 hcross)
  have hrecordRunCount : E.records.length = count := by
    exact ReferenceActivePhysicalHorizon.run_record_count _ _ _ _ _ _ _ _
  have hw : w < count := by
    change w < count at hshort
    exact hshort
  have hcutTime : d.stream.cutoff.cut.input.time.val = start + w := by
    simpa only [x, start, ReferenceFirstCollectionReadyStream.startTime] using htime
  have hrunRecord : E.records[w]'(by rw [hrecordRunCount]; exact hshort) =
      ReferenceAssignmentPayloadChronology.actualRunRecordAt initial source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start w
        (by omega) hactive := by
    simpa only [E, start, ReferenceFirstCollectionReadyStream.startTime,
      ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun] using
      (ReferenceLocalReleaseGateChronology.run_record_at initial source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start hactive
        count hspan ⟨w, hw⟩)
  have hcutEqualsRunRecord :
      ReferenceAssignmentPayloadChronology.actualRunRecordAt initial source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start w
        (by omega) hactive = d.stream.cutoff.cut := by
    apply Option.some.inj
    have hlookup : E.records[w]? = some
        (ReferenceAssignmentPayloadChronology.actualRunRecordAt initial source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start w
          (by omega) hactive) := by
      rw [List.getElem?_eq_getElem (by rw [hrecordRunCount]; exact hshort)]
      exact congrArg some hrunRecord
    exact hlookup.symm.trans d.stream.cutoff.cutIndex
  have hstart : ReferenceCompletePhysicalHistory.physicalStart
      rate source rewards C_star C_h = start := rfl
  have hsourceLaunchRecord :=
    ReferenceSourcePrefixHistoryFiltration.actualRecord_on_launch
      rate rewards C_star C_h x.time source initial hlaunch (by
        rw [hstart, hcutTime]
        omega)
  have hactualRecord :
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
        x.time source = some d.stream.cutoff.cut := by
    have hsourceRunRecord :
        ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
          x.time source = some
            (ReferenceAssignmentPayloadChronology.actualRunRecordAt initial source.1.2
              (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start w
              (by omega) hactive) := by
      simpa only [x, hstart, hcutTime, Nat.add_sub_cancel_left] using hsourceLaunchRecord
    exact hsourceRunRecord.trans (congrArg some hcutEqualsRunRecord)
  refine ⟨d, hwindow, hhead, ?_, hrows, hselected, hrew, r, q, base,
    old, memory, hphase, hpayload, hfamily, ?_⟩
  · exact hcutTime
  · intro i hnone
    let wD := CoordinatorLocalArmChoice.storedDownFlatWord r.payload i
    have hfixed := hservice i hnone
    dsimp only [wD] at hfixed
    obtain ⟨hwD, _hparsed, hcontrols⟩ := hfixed
    have hevent (c : TimeControl p) :
        c ∈ freshCoordinatorDownServiceSet x i ↔
          c ∈ downServiceFormulaSet rewards x.time i wD := by
      change (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K c.1 = i ∧
          ReferenceActiveAffinePositiveTest.downPositive
            (ReferenceLaterOptionalControlResampling.withControl x c) = true) ↔
        (PublicDiscreteDraws.slotDraw c.1 = PublicDiscreteDraws.downSlot ∧
          PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K c.1 = i ∧
          AffineChannelLaw.affineHash (c.2 (0, i)) wD = 1 ∧
          0 < rewards x.time ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K
            c.1).val (ReferenceFirstCollectionDownControlGeometry.followerPlayerAt i)))
      have hc := hcontrols c
      obtain ⟨selected, hsel, hpay, hpending, hvalid, hbound, hcutoff,
        hreset, hinj, hdown, _hup, _hactions⟩ := hc
      have hplayer : PublicDiscreteDraws.followerPlayer p.two_le_m i =
          ReferenceFirstCollectionDownControlGeometry.followerPlayerAt i := by
        apply Fin.ext
        rfl
      simpa only [hplayer] using hdown
    have hset : freshCoordinatorDownServiceSet x i =
        downServiceFormulaSet rewards x.time i wD := Set.ext hevent
    have hmeasure : (ContinuousLearningRows.timeControlLaw p)
        (freshCoordinatorDownServiceSet x i) =
        ENNReal.ofReal ((ReferenceFirstCollectionUpConditionalService.positiveRewardCount
          rewards x.time : ℝ) / (8 * (p.m - 1 : ℝ) * p.K)) := by
      rw [hset]
      exact ReferenceFirstCollectionDownConditionalService.downServiceFormulaSet_probability
        rewards x.time i wD
    have hmpos : 0 < (p.m : ℝ) - 1 := by
      have hm : (1 : ℝ) < (p.m : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) p.two_le_m)
      exact sub_pos.mpr hm
    have hKpos : 0 < (p.K : ℝ) :=
      Nat.cast_pos.mpr (ConstructorDimensions.K_pos p)
    have hden : 0 < (8 : ℝ) * (p.m - 1 : ℝ) * p.K := by positivity
    have hcoeff : 0 ≤
        (ReferenceFirstCollectionUpConditionalService.positiveRewardCount
          rewards x.time : ℝ) / (8 * (p.m - 1 : ℝ) * p.K) :=
      div_nonneg (Nat.cast_nonneg _) (le_of_lt hden)
    have hsection : actualFirstCollectionDownFreshSection (rate := rate)
        rewards C_star C_h control0 i x.time source =
        (ReferenceFirstCollectionUpConditionalService.positiveRewardCount
          rewards x.time : ℝ) / (8 * (p.m - 1 : ℝ) * p.K) := by
      rw [ReferenceFirstCollectionDownConditionalService.actualFirstCollectionDownFreshSection_eq_measure
        rewards C_star C_h control0 i x.time source d.stream.cutoff.cut hactualRecord,
        measureReal_def, hmeasure, ENNReal.toReal_ofReal hcoeff]
    have hconditional :
        (BootstrapPrivateRoundStreams.sourceInputLaw p)[
          actualFirstCollectionDownReadout (rate := rate) rewards C_star C_h i x.time |
            ReferenceSourceCurrentControlFreshness.m_t p control0 x.time] source =
        (ReferenceFirstCollectionUpConditionalService.positiveRewardCount
          rewards x.time : ℝ) / (8 * (p.m - 1 : ℝ) * p.K) :=
      (hce i x.time).trans hsection
    exact ⟨wD, hwD, hactualRecord, hevent, hmeasure, hsection, hconditional⟩

end Bandits.Support.ReferenceFirstCutoffDownConditionalService

end
