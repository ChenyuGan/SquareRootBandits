/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstReplacementCollectionOrdinaryStages
public import Bandits.Support.ReferenceFirstReplacementCollectionActualCalendarTasks

import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator

/-!
# Original-source law of literal first replacement collection service

Sources: pinned ZIP4 `06_interruptions.tex:180-239,246-349,459-487` and
`appendix_a_local_protocol.tex:28-85,92-157`.

The service here is the existing actual calendar observation, including its
strict-past stopping mask and the detecting round. This module supplies no
waiting, transfer-cost, or all-phase statement.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support ConstructorDimensions
open scoped Classical

namespace Bandits.Support.ReferenceFirstReplacementCollectionCalendarServiceLaw


local instance propDecidable (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

variable {p : Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}

/-- Literal channel selection is exactly the DOWN slot and focal receiver draw. -/
theorem selectedChannel_down_iff (h : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1)) :
    ReferenceSelectedAffinePairLaw.selectedChannel p h.1 = some (0, i) ↔
      PublicDiscreteDraws.slotDraw h.1 = PublicDiscreteDraws.downSlot ∧
      PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K h.1 = i := by
  unfold ReferenceSelectedAffinePairLaw.selectedChannel
    ReferenceSelectedAffinePairLaw.channelFromDraws
  dsimp only
  split
  · rename_i hd
    constructor
    · intro he
      exact ⟨hd, (Prod.mk.inj (Option.some.inj he)).2⟩
    · rintro ⟨_, hi⟩
      rw [hi]
      rfl
  · rename_i hd
    split
    · constructor
      · intro he
        have he' := congrArg (fun q : Fin 2 × Fin (p.m - 1) => q.1.val)
          (Option.some.inj he)
        norm_num at he'
      · intro he
        exact (hd he.1).elim
    · constructor
      · intro he
        cases he
      · intro he
        exact (hd he.1).elim

/-- On an ordinary valid unoccupied choice, the calendar DOWN observation is
exactly the executed positive test. Later decoder failures are retained. -/
theorem downPositive_eq_test
    (r : ReferenceFirstReplacementCollectionActualCalendarTasks.Record (rate := rate)) (i : Fin (p.m - 1))
    (choice : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hc : (ReferenceFollowerFixedReply.actualChoice r i).configuration =
      .ordinary choice memory)
    (hs : choice.status = .unoccupied)
    (hv : ActiveFollowerLifecycle.localStateDomainValid choice) :
    (ReferenceFirstReplacementCollectionActualCalendarTasks.downPositive r i : ℝ) =
      if PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
          (r.input.row.2 r.input.time).1 = i ∧
          ReferenceActiveAffinePositiveTest.downPositive r.input = true then 1 else 0 := by
  have hc' : ((ReferenceActivePhysicalStep.prepare r.input).followers.followers i).configuration =
      .ordinary choice memory := by
    simpa only [ReferenceFollowerFixedReply.actualChoice, r.output_eq, ReferenceActivePhysicalStep.step] using hc
  by_cases hi : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
      (r.input.row.2 r.input.time).1 = i
  · have hindex := (ReferenceActiveAffinePositiveTest.upSenderIndex_eq_draw r.input).trans hi
    have hg := ReferenceFirstCutoffDownControlGeometry.down_gate_eq_decide_downSelected_of_prepared_unoccupied
      r.input i choice memory hindex hc' hs hv
    have hpos : ReferenceActiveAffinePositiveTest.downPositive r.input = true ↔
        ActiveFollowerDownAcceptance.downSelected p i r.input.row r.input.time ∧
          0 < (ReferenceFollowerDownDecoderReplay.preparedOwnObservation r i).val.val := by
      unfold ReferenceActiveAffinePositiveTest.downPositive
      dsimp only [PublicDiscreteDraws.followerCount, ContinuousLearningRows.d]
      rw [ReferenceActiveAffinePositiveTest.downCallGate_eq_prefix]
      have halign := (ReferenceActivePhysicalStep.prepare r.input).follower_alignment i
      rw [hindex, halign.1, halign.2.1, halign.2.2.1]
      have hg' : ReferenceActiveAffinePositiveTest.downPrefixGate i r.input.row r.input.time
          ((ReferenceActivePhysicalStep.prepare r.input).followers.followers i).configuration =
          decide (ActiveFollowerDownAcceptance.downSelected p i r.input.row r.input.time) := by
        simpa only [ReferenceActiveAffinePositiveTest.downGate, hindex] using hg
      rw [hg']
      have hobs : (ReferenceActivePhysicalStep.prepare r.input).feedback.observations
          (PublicDiscreteDraws.followerPlayer p.two_le_m i) =
          ReferenceFollowerDownDecoderReplay.preparedOwnObservation r i := by
        rw [ReferenceFollowerDownDecoderReplay.preparedOwnObservation, r.output_eq]
        rfl
      rw [hobs]
      simp only [Bool.and_eq_true, decide_eq_true_eq]
    simp only [ReferenceFirstReplacementCollectionActualCalendarTasks.downPositive, PublicDiscreteDraws.followerCount, selectedChannel_down_iff, hpos,
      ActiveFollowerDownAcceptance.downSelected, hi, and_true, true_and]
    split_ifs <;> simp
  · have hn : ¬ ReferenceSelectedAffinePairLaw.selectedChannel p
        (r.input.row.2 r.input.time).1 = some (0, i) := by
      rw [selectedChannel_down_iff]
      exact fun h => hi h.2
    have hnot : ¬ (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
        (r.input.row.2 r.input.time).1 = i ∧
        ReferenceActiveAffinePositiveTest.downPositive r.input = true) := fun h => hi h.1
    have hz : ReferenceFirstReplacementCollectionActualCalendarTasks.downPositive r i = 0 := by
      unfold ReferenceFirstReplacementCollectionActualCalendarTasks.downPositive
      split
      · rename_i he
        exact (hn he.1).elim
      · rfl
    rw [hz, Nat.cast_zero]
    exact (ite_eq_right hnot).symm

/-- The length of the actual saved UP append is the selected executed test,
including rejection and failure after the receiver ran. -/
theorem upPositive_eq_test (r : ReferenceFirstReplacementCollectionActualCalendarTasks.Record (rate := rate)) (i : Fin (p.m - 1)) :
    (ReferenceFirstReplacementCollectionActualCalendarTasks.upPositive r i : ℝ) =
      if PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
          (r.input.row.2 r.input.time).1 = i ∧
          ReferenceActiveAffinePositiveTest.upPositive r.input = true then 1 else 0 := by
  cases hd : r.output.coordinator.up with
  | none =>
    have hz : ReferenceActiveAffinePositiveTest.upPositive r.input = false := by
      rw [ReferenceActiveAffinePositiveTest.record_upPositive, hd]
      rfl
    simp only [ReferenceFirstReplacementCollectionActualCalendarTasks.upPositive,
      ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries, hd, List.length_nil,
      Nat.cast_zero, hz, Bool.false_eq_true, and_false, ite_false]
  | some d =>
    obtain ⟨ledger, _, _, hinput, _⟩ :=
      ReferenceGeneratedUpBatchCalendar.record_up_executed_fields r d hd
    have hsel : ReferenceCoordinatorUpDecoderReplay.retainedUpFollower d =
        PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
          (r.input.row.2 r.input.time).1 := by
      unfold ReferenceCoordinatorUpDecoderReplay.retainedUpFollower
      rw [hinput]
      exact ReferenceActiveAffinePositiveTest.upSenderIndex_eq_draw r.input
    have hequiv : ReferenceActiveAffinePositiveTest.upPositive r.input = true ↔
        AffineBatchDecoder.eligible
          (ReferenceCoordinatorUpDecoderReplay.constantInputTrace d.input
            (ReferenceCoordinatorUpDecoderReplay.retainedUpTime d)) := by
      rw [ReferenceActiveAffinePositiveTest.record_upPositive, hd]
      exact decide_eq_true_iff
    simp only [ReferenceFirstReplacementCollectionActualCalendarTasks.upPositive,
      ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries, hd]
    by_cases hi : ReferenceCoordinatorUpDecoderReplay.retainedUpFollower d = i
    · rw [ite_eq_left hi]
      unfold AffineBatchDecoder.positiveAt
      split
      · rename_i he
        have htest : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
            (r.input.row.2 r.input.time).1 = i ∧
            ReferenceActiveAffinePositiveTest.upPositive r.input = true :=
          ⟨hsel.symm.trans hi, hequiv.mpr he⟩
        rw [ite_eq_left htest]
        simp only [List.length_singleton, Nat.cast_one]
      · rename_i he
        have htest : ¬ (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
            (r.input.row.2 r.input.time).1 = i ∧
            ReferenceActiveAffinePositiveTest.upPositive r.input = true) :=
          fun h => he (hequiv.mp h.2)
        rw [ite_eq_right htest]
        simp only [List.length_nil, Nat.cast_zero]
    · rw [ite_eq_right hi]
      have htest : ¬ (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
          (r.input.row.2 r.input.time).1 = i ∧
          ReferenceActiveAffinePositiveTest.upPositive r.input = true) :=
        fun h => hi (hsel.trans h.1)
      rw [ite_eq_right htest]
      simp only [List.length_nil, Nat.cast_zero]

private theorem integral_of_indicator_formula
    (g : ContinuousLearningRows.TimeControl p → ℝ)
    (E : Set (ContinuousLearningRows.TimeControl p))
    (hg : Measurable g) (he : ∀ h, g h = E.indicator (fun _ => (1 : ℝ)) h) :
    ∫ h, g h ∂ContinuousLearningRows.timeControlLaw p =
      (ContinuousLearningRows.timeControlLaw p).real E := by
  have hE : MeasurableSet E := by
    have hset : E = g ⁻¹' {1} := by
      ext h
      rw [Set.mem_preimage, Set.mem_singleton_iff, he h]
      by_cases hm : h ∈ E <;> simp [Set.indicator, hm]
    rw [hset]
    exact hg (measurableSet_singleton 1)
  calc
    _ = ∫ h, E.indicator (fun _ => (1 : ℝ)) h
        ∂ContinuousLearningRows.timeControlLaw p := integral_congr_ae
          (Filter.Eventually.of_forall he)
    _ = _ := integral_indicator_one hE

private theorem coefficient_nonneg
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (t : Fin p.T) :
    0 ≤ (ReferenceFirstCollectionUpConditionalService.positiveRewardCount rewards t : ℝ) / (8 * (p.m - 1 : ℝ) * p.K) := by
  have hm : (1 : ℝ) < p.m := by exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) p.two_le_m)
  have hK : (0 : ℝ) < p.K := by exact_mod_cast (K_pos p)
  exact div_nonneg (Nat.cast_nonneg _) (by positivity)

private theorem down_integral_of_formula
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (i : Fin (p.m - 1)) (t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (w : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (he : ∀ h, ReferenceFirstCollectionDownConditionalService.actualFirstCollectionDownReadout (rate := rate) rewards C_star C_h i t
      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z h) =
        (ReferenceFirstCollectionDownConditionalService.downServiceFormulaSet rewards t i w).indicator (fun _ => (1 : ℝ)) h) :
    ∫ h, ReferenceFirstCollectionDownConditionalService.actualFirstCollectionDownReadout (rate := rate) rewards C_star C_h i t
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z h)
        ∂ContinuousLearningRows.timeControlLaw p =
      (ReferenceFirstCollectionUpConditionalService.positiveRewardCount rewards t : ℝ) / (8 * (p.m - 1 : ℝ) * p.K) := by
  have hg : Measurable (fun h => ReferenceFirstCollectionDownConditionalService.actualFirstCollectionDownReadout
      (rate := rate) rewards C_star C_h i t
      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z h)) :=
    (ReferenceFirstCollectionDownConditionalService.measurable_actualFirstCollectionDownReadout
      (rate := rate) rewards C_star C_h i t).comp
      ((ReferenceSourcePhysicalFlagConditionalLaw.measurable_replaceSourceControl p t).comp
        ((measurable_const : Measurable (fun _ : ContinuousLearningRows.TimeControl p => z)).prodMk measurable_id))
  calc
    _ = (ContinuousLearningRows.timeControlLaw p).real
        (ReferenceFirstCollectionDownConditionalService.downServiceFormulaSet rewards t i w) :=
      integral_of_indicator_formula _ _ hg he
    _ = _ := by rw [measureReal_def,
    ReferenceFirstCollectionDownConditionalService.downServiceFormulaSet_probability, ENNReal.toReal_ofReal (coefficient_nonneg rewards t)]

private theorem up_integral_of_formula
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (i : Fin (p.m - 1)) (t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (reply : ReferenceFirstCollectionUpConditionalService.UpRecord rate)
    (he : ∀ h, ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpReadout (rate := rate) rewards C_star C_h i t
      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z h) =
        (ReferenceFirstCollectionUpConditionalService.coordinatorUpServiceFormulaSet (rate := rate) rewards t i reply).indicator
          (fun _ => (1 : ℝ)) h) :
    ∫ h, ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpReadout (rate := rate) rewards C_star C_h i t
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z h)
        ∂ContinuousLearningRows.timeControlLaw p =
      (ReferenceFirstCollectionUpConditionalService.positiveRewardCount rewards t : ℝ) / (8 * (p.m - 1 : ℝ) * p.K) := by
  have hg := (ReferenceSourcePhysicalFlagConditionalLaw.measurable_replaceSourceControl p t)
  have hm : Measurable (fun h => ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpReadout
      (rate := rate) rewards C_star C_h i t
      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z h)) :=
    (ReferenceFirstCollectionUpConditionalService.measurable_actualFirstCollectionUpReadout (rate := rate)
    rewards C_star C_h i t).comp (hg.comp ((measurable_const : Measurable (fun _ : ContinuousLearningRows.TimeControl p => z)).prodMk measurable_id))
  calc
    _ = (ContinuousLearningRows.timeControlLaw p).real
        (ReferenceFirstCollectionUpConditionalService.coordinatorUpServiceFormulaSet (rate := rate) rewards t i reply) :=
      integral_of_indicator_formula _ _ hm he
    _ = _ := by rw [measureReal_def,
    ReferenceFirstCollectionUpConditionalService.coordinatorUpServiceFormulaSet_probability,
    ENNReal.toReal_ofReal (coefficient_nonneg rewards t)]

/-- Localization and ordinary-stage service are consumed on the SAME actual K
coordinate. Both literal observations and both whole-current-control integrals
are obtained without a caller-supplied stage or execution premise. -/
theorem pending_service_data
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (i : Fin (p.m - 1)) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hi : i ∈ ReferenceFirstReplacementCollectionPendingFoundation.P_repl rate rewards C_star C_h control0 t.val z) :
    (ReferenceFirstReplacementCollectionPredictableStages.OLD rate rewards C_star C_h control0 t.val i z ∨
      ReferenceFirstReplacementCollectionPredictableStages.FORMED rate rewards C_star C_h control0 t.val i z) ∧
    ((ReferenceFirstReplacementCollectionActualCalendarTasks.oldService rate rewards C_star C_h control0 t.val i z : ℝ) =
      if ReferenceFirstReplacementCollectionPredictableStages.OLD rate rewards C_star C_h control0 t.val i z then
        ReferenceFirstCollectionDownConditionalService.actualFirstCollectionDownReadout (rate := rate) rewards C_star C_h i t z else 0) ∧
    ((ReferenceFirstReplacementCollectionActualCalendarTasks.formedService rate rewards C_star C_h control0 t.val i z : ℝ) =
      if ReferenceFirstReplacementCollectionPredictableStages.FORMED rate rewards C_star C_h control0 t.val i z then
        ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpReadout (rate := rate) rewards C_star C_h i t z else 0) ∧
    (ReferenceFirstReplacementCollectionPredictableStages.OLD rate rewards C_star C_h control0 t.val i z →
      ∫ h, ReferenceFirstCollectionDownConditionalService.actualFirstCollectionDownReadout (rate := rate) rewards C_star C_h i t
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z h)
        ∂ContinuousLearningRows.timeControlLaw p =
        (ReferenceFirstCollectionUpConditionalService.positiveRewardCount rewards t : ℝ) / (8 * (p.m - 1 : ℝ) * p.K)) ∧
    (ReferenceFirstReplacementCollectionPredictableStages.FORMED rate rewards C_star C_h control0 t.val i z →
      ∫ h, ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpReadout (rate := rate) rewards C_star C_h i t
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z h)
        ∂ContinuousLearningRows.timeControlLaw p =
        (ReferenceFirstCollectionUpConditionalService.positiveRewardCount rewards t : ℝ) / (8 * (p.m - 1 : ℝ) * p.K)) := by
  have hC := ReferenceFirstReplacementCollectionActualCalendarTasks.complete_first_replacement_actual_calendar_tasks rate rewards C_star C_h control0 z
  have hO := ReferenceFirstReplacementCollectionOrdinaryStages.complete_first_replacement_collection_ordinary_stage_service
    rate z rewards C_star C_h control0
  have hG := ReferenceFirstReplacementCollectionFreshFollowerGeometry.complete_first_replacement_collection_follower_control_geometry
    rate z rewards C_star C_h
  dsimp only at hC hO hG
  set R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  set w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  set v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
  set tail := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v
  set c := v + 1 + tail.length
  cases hb : R[v]? with
  | none =>
    simp only [hb] at hC
    rw [hC t.val] at hi
    exact (Finset.notMem_empty i hi).elim
  | some birth =>
    simp only [hb] at hC hO hG
    cases hbirth : birth.output.preparation.coordinator <;>
      try (simp only [hbirth] at hC; rw [hC t.val] at hi; exact (Finset.notMem_empty i hi).elim)
    rename_i old ledger clock cutoff outcome
    simp only [hbirth] at hC hO hG
    cases outcome <;>
      try (rw [hC t.val] at hi; exact (Finset.notMem_empty i hi).elim)
    rename_i core consistent started hstart instruction hinstruction output hconsistent
      clockData installed selectedBirth
    dsimp only [ReferenceActivePhysicalStep.collectionInput] at hC hO hG
    cases hc : R[c]? with
    | none =>
      simp only [hc] at hC
      rw [hC t.val] at hi
      exact (Finset.notMem_empty i hi).elim
    | some cut =>
      simp only [hc] at hC hO hG
      cases hcut : cut.output.preparation.coordinator <;>
        try (simp only [hcut] at hC; rw [hC t.val] at hi; exact (Finset.notMem_empty i hi).elim)
      rename_i registers owned base outcome
      simp only [hcut] at hC hO hG
      cases outcome <;>
        try (rw [hC t.val] at hi; exact (Finset.notMem_empty i hi).elim)
      rename_i dispatched hs ledger hiLedger hledger hdata hclock hpending hnone selectedCut
      dsimp only at hC hO hG
      let P := installed.registers.payload
      let u := cut.input.time.val + 1
      let K := cut :: (R.drop (c + 1)).takeWhile
        (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
      obtain ⟨a, hdate, htime, _⟩ := hC.1 t.val ⟨i, hi⟩
      have hfin : (K.get a).input.time = t := Fin.ext htime
      have hactual := (hC.2.2.1 a).2.2.1
      obtain ⟨sel, _hsel, _hpay, _hcut, hbranches⟩ := hO a
      obtain ⟨choice, memory, reply, hchoice, hstatus, hvalid, _⟩ := hG a i
      have hdown := downPositive_eq_test (K.get a) i choice memory hchoice hstatus hvalid
      have hup := upPositive_eq_test (K.get a) i
      have hbranch := hbranches i (by rw [← hdate]; exact hi)
      have hrecords : ReferenceSourcePrefixHistoryFiltration.actualRecord
          rate rewards C_star C_h t z = some (K.get a) := by rw [← hfin]; exact hactual
      have hd : (ReferenceFirstReplacementCollectionActualCalendarTasks.oldService rate rewards C_star C_h control0 t.val i z : ℝ) =
          if ReferenceFirstReplacementCollectionPredictableStages.OLD rate rewards C_star C_h control0 t.val i z then
            ReferenceFirstCollectionDownConditionalService.actualFirstCollectionDownReadout (rate := rate) rewards C_star C_h i t z else 0 := by
        unfold ReferenceFirstReplacementCollectionActualCalendarTasks.oldService
        rw [dite_eq_left t.isLt, hrecords]
        rw [hfin] at hdown
        by_cases ho : ReferenceFirstReplacementCollectionPredictableStages.OLD rate rewards C_star C_h control0 t.val i z
        · simp only [ite_eq_left ho, ReferenceFirstCollectionDownConditionalService.actualFirstCollectionDownReadout, hrecords]
          exact hdown
        · simp only [ite_eq_right ho, Nat.cast_zero]
      have hu : (ReferenceFirstReplacementCollectionActualCalendarTasks.formedService rate rewards C_star C_h control0 t.val i z : ℝ) =
          if ReferenceFirstReplacementCollectionPredictableStages.FORMED rate rewards C_star C_h control0 t.val i z then
            ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpReadout (rate := rate) rewards C_star C_h i t z else 0 := by
        unfold ReferenceFirstReplacementCollectionActualCalendarTasks.formedService
        rw [dite_eq_left t.isLt, hrecords]
        rw [hfin] at hup
        by_cases hf : ReferenceFirstReplacementCollectionPredictableStages.FORMED rate rewards C_star C_h control0 t.val i z
        · simp only [ite_eq_left hf, ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpReadout, hrecords]
          refine hup.trans ?_
          apply ite_congr
          · rfl
          · intro _; rfl
          · intro _; rfl
        · simp only [ite_eq_right hf, Nat.cast_zero]
      rw [← hdate] at hbranch
      rcases hbranch with ⟨ho, _hold, hall⟩ | ⟨hf, _hformed, choiceU, memoryU, replyU,
          _hchoiceU, _hstatusU, _hdownU, _hfieldsU, _hsigmaU, _hpositiveU, hall⟩
      · refine ⟨Or.inl ho, hd, hu, ?_, ?_⟩
        · intro _
          apply down_integral_of_formula rewards C_star C_h i t z
            (CoordinatorLocalArmChoice.storedDownFlatWord P i)
          intro h
          obtain ⟨rh, vh, _hr, _hx, _hv, _hp, _hpend, _hcutoff, _hL, _hOld, he⟩ := hall h
          rw [hfin] at he
          exact he
        · intro hf
          exact (ReferenceFirstReplacementCollectionPredictableStages.OLD_FORMED_disjoint rate rewards C_star C_h control0 t.val i z ⟨ho, hf⟩).elim
      · refine ⟨Or.inr hf, hd, hu, ?_, ?_⟩
        · intro ho
          exact (ReferenceFirstReplacementCollectionPredictableStages.OLD_FORMED_disjoint rate rewards C_star C_h control0 t.val i z ⟨ho, hf⟩).elim
        · intro _
          apply up_integral_of_formula rewards C_star C_h i t z replyU
          intro h
          obtain ⟨rh, vh, _hr, _hx, _hv, _hp, _hpend, _hcutoff, _hL, _hFormed, he⟩ := hall h
          rw [hfin] at he
          exact he

/-- The literal OLD calendar service equals the predictable OLD mask times
the general actual DOWN readout, on the whole source carrier. -/
theorem oldService_eq_indicator
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T) (i : Fin (p.m - 1)) :
    (fun z => (ReferenceFirstReplacementCollectionActualCalendarTasks.oldService rate rewards C_star C_h control0 t.val i z : ℝ)) =
      {z | ReferenceFirstReplacementCollectionPredictableStages.OLD rate rewards C_star C_h control0 t.val i z}.indicator
        (ReferenceFirstCollectionDownConditionalService.actualFirstCollectionDownReadout (rate := rate) rewards C_star C_h i t) := by
  funext z
  by_cases hi : i ∈ ReferenceFirstReplacementCollectionPendingFoundation.P_repl rate rewards C_star C_h control0 t.val z
  · exact (pending_service_data rate rewards C_star C_h control0 t i z hi).2.1
  · have hz := (ReferenceFirstReplacementCollectionActualCalendarTasks.services_of_not_pending (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) (control0 := control0) t.val i z hi).1
    have ho := ReferenceFirstReplacementCollectionPredictableStages.not_OLD_of_not_pending rate rewards C_star C_h control0 t.val i z hi
    rw [hz, Nat.cast_zero]
    symm
    exact Set.indicator_of_notMem
      (s := {z | ReferenceFirstReplacementCollectionPredictableStages.OLD rate rewards C_star C_h control0 t.val i z}) ho
      (ReferenceFirstCollectionDownConditionalService.actualFirstCollectionDownReadout (rate := rate) rewards C_star C_h i t)

/-- The current-reply service counts the actual saved UP entries, with the
predictable FORMED mask and no positives from before formation. -/
theorem formedService_eq_indicator
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T) (i : Fin (p.m - 1)) :
    (fun z => (ReferenceFirstReplacementCollectionActualCalendarTasks.formedService rate rewards C_star C_h control0 t.val i z : ℝ)) =
      {z | ReferenceFirstReplacementCollectionPredictableStages.FORMED rate rewards C_star C_h control0 t.val i z}.indicator
        (ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpReadout (rate := rate) rewards C_star C_h i t) := by
  funext z
  by_cases hi : i ∈ ReferenceFirstReplacementCollectionPendingFoundation.P_repl rate rewards C_star C_h control0 t.val z
  · exact (pending_service_data rate rewards C_star C_h control0 t i z hi).2.2.1
  · have hz := (ReferenceFirstReplacementCollectionActualCalendarTasks.services_of_not_pending (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) (control0 := control0) t.val i z hi).2.1
    have hf := ReferenceFirstReplacementCollectionPredictableStages.not_FORMED_of_not_pending rate rewards C_star C_h control0 t.val i z hi
    rw [hz, Nat.cast_zero]
    symm
    exact Set.indicator_of_notMem
      (s := {z | ReferenceFirstReplacementCollectionPredictableStages.FORMED rate rewards C_star C_h control0 t.val i z}) hf
      (ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpReadout (rate := rate) rewards C_star C_h i t)

/-- Exact whole-source decomposition of the existing literal calendar service. -/
theorem service_eq_masked_readouts
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T) (i : Fin (p.m - 1)) :
    (fun z => (ReferenceFirstReplacementCollectionActualCalendarTasks.service rate rewards C_star C_h control0 t.val i z : ℝ)) =
      {z | ReferenceFirstReplacementCollectionPredictableStages.OLD rate rewards C_star C_h control0 t.val i z}.indicator
        (ReferenceFirstCollectionDownConditionalService.actualFirstCollectionDownReadout (rate := rate) rewards C_star C_h i t) +
      {z | ReferenceFirstReplacementCollectionPredictableStages.FORMED rate rewards C_star C_h control0 t.val i z}.indicator
        (ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpReadout (rate := rate) rewards C_star C_h i t) := by
  rw [← oldService_eq_indicator, ← formedService_eq_indicator]
  funext z
  exact Nat.cast_add _ _

/-- Ambient Borel measurability is derived from the actual masked readouts. -/
theorem measurable_service
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T) (i : Fin (p.m - 1)) :
    Measurable (fun z => (ReferenceFirstReplacementCollectionActualCalendarTasks.service rate rewards C_star C_h control0 t.val i z : ℝ)) := by
  rw [service_eq_masked_readouts]
  exact ((ReferenceFirstCollectionDownConditionalService.measurable_actualFirstCollectionDownReadout (rate := rate)
      rewards C_star C_h i t).indicator
      (ReferenceFirstReplacementCollectionPredictableStages.OLD_borel rate rewards C_star C_h control0 t.val i)).add
    ((ReferenceFirstCollectionUpConditionalService.measurable_actualFirstCollectionUpReadout (rate := rate)
      rewards C_star C_h i t).indicator
      (ReferenceFirstReplacementCollectionPredictableStages.FORMED_borel rate rewards C_star C_h control0 t.val i))

/-- Integrability is proved under the unchanged original source input law. -/
theorem integrable_service
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T) (i : Fin (p.m - 1)) :
    Integrable (fun z => (ReferenceFirstReplacementCollectionActualCalendarTasks.service rate rewards C_star C_h control0 t.val i z : ℝ))
      (BootstrapPrivateRoundStreams.sourceInputLaw p) := by
  rw [service_eq_masked_readouts]
  exact ((ReferenceFirstCollectionDownConditionalService.integrable_actualFirstCollectionDownReadout (rate := rate)
      rewards C_star C_h i t).indicator
      (ReferenceFirstReplacementCollectionPredictableStages.OLD_borel rate rewards C_star C_h control0 t.val i)).add
    ((ReferenceFirstCollectionUpConditionalService.integrable_actualFirstCollectionUpReadout (rate := rate)
      rewards C_star C_h i t).indicator
      (ReferenceFirstReplacementCollectionPredictableStages.FORMED_borel rate rewards C_star C_h control0 t.val i))

/-- OLD's strict-past factor permits applying the same actual-run constructor
to `c_t`. The full current control is then integrated using its fixed word. -/
theorem downFreshSection_of_OLD
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T) (i : Fin (p.m - 1))
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (ho : ReferenceFirstReplacementCollectionPredictableStages.OLD rate rewards C_star C_h control0 t.val i z) :
    ReferenceFirstCollectionDownConditionalService.actualFirstCollectionDownFreshSection (rate := rate) rewards C_star C_h control0 i t z =
      (ReferenceFirstCollectionUpConditionalService.positiveRewardCount rewards t : ℝ) / (8 * (p.m - 1 : ℝ) * p.K) := by
  let zp := ReferenceSourceCurrentControlFreshness.c_t p control0 t z
  have ho' : ReferenceFirstReplacementCollectionPredictableStages.OLD rate rewards C_star C_h control0 t.val i zp := by
    unfold ReferenceFirstReplacementCollectionPredictableStages.OLD at ho ⊢
    rw [show zp = ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z from
      ReferenceSourcePhysicalFlagConditionalLaw.c_t_eq_sourcePrefix control0 t z,
      ← ReferenceFirstReplacementCollectionPredictableStages.taskStage_factor rate rewards C_star C_h control0 t.val i z]
    exact ho
  have hi' : i ∈ ReferenceFirstReplacementCollectionPendingFoundation.P_repl rate rewards C_star C_h control0 t.val zp := by
    by_contra hn
    exact ReferenceFirstReplacementCollectionPredictableStages.not_OLD_of_not_pending rate rewards C_star C_h control0 t.val i zp hn ho'
  exact (pending_service_data rate rewards C_star C_h control0 t i zp hi').2.2.2.1 ho'

/-- FORMED is treated by the same original prefix. Its actual UP record is
produced inside the ordinary-stage theorem, and its coefficient is uniform. -/
theorem upFreshSection_of_FORMED
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T) (i : Fin (p.m - 1))
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hf : ReferenceFirstReplacementCollectionPredictableStages.FORMED rate rewards C_star C_h control0 t.val i z) :
    ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpFreshSection (rate := rate) rewards C_star C_h control0 i t z =
      (ReferenceFirstCollectionUpConditionalService.positiveRewardCount rewards t : ℝ) / (8 * (p.m - 1 : ℝ) * p.K) := by
  let zp := ReferenceSourceCurrentControlFreshness.c_t p control0 t z
  have hf' : ReferenceFirstReplacementCollectionPredictableStages.FORMED rate rewards C_star C_h control0 t.val i zp := by
    unfold ReferenceFirstReplacementCollectionPredictableStages.FORMED at hf ⊢
    rw [show zp = ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z from
      ReferenceSourcePhysicalFlagConditionalLaw.c_t_eq_sourcePrefix control0 t z,
      ← ReferenceFirstReplacementCollectionPredictableStages.taskStage_factor rate rewards C_star C_h control0 t.val i z]
    exact hf
  have hi' : i ∈ ReferenceFirstReplacementCollectionPendingFoundation.P_repl rate rewards C_star C_h control0 t.val zp := by
    by_contra hn
    exact ReferenceFirstReplacementCollectionPredictableStages.not_FORMED_of_not_pending rate rewards C_star C_h control0 t.val i zp hn hf'
  exact (pending_service_data rate rewards C_star C_h control0 t i zp hi').2.2.2.2 hf'

/-- Whole-source conditional expectation of the EXISTING literal actual service.
The field is the original strict-past source-prefix filtration; neither a
replacement law nor a stage, survival, or history premise is assumed. -/
theorem actual_first_replacement_collection_condExp
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T) (i : Fin (p.m - 1)) :
    (BootstrapPrivateRoundStreams.sourceInputLaw p)[
      (fun z => (ReferenceFirstReplacementCollectionActualCalendarTasks.service rate rewards C_star C_h control0 t.val i z : ℝ)) |
      ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (t.val + 1)] =ᵐ[
      BootstrapPrivateRoundStreams.sourceInputLaw p]
    {z | i ∈ ReferenceFirstReplacementCollectionPendingFoundation.P_repl rate rewards C_star C_h control0 t.val z}.indicator
      (fun _ => (ReferenceFirstCollectionUpConditionalService.positiveRewardCount rewards t : ℝ) / (8 * (p.m - 1 : ℝ) * p.K)) := by
  let mu := BootstrapPrivateRoundStreams.sourceInputLaw p
  let F := ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (t.val + 1)
  let A := {z | ReferenceFirstReplacementCollectionPredictableStages.OLD rate rewards C_star C_h control0 t.val i z}
  let B := {z | ReferenceFirstReplacementCollectionPredictableStages.FORMED rate rewards C_star C_h control0 t.val i z}
  let d := ReferenceFirstCollectionDownConditionalService.actualFirstCollectionDownReadout (rate := rate) rewards C_star C_h i t
  let u := ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpReadout (rate := rate) rewards C_star C_h i t
  have hd : Integrable d mu := ReferenceFirstCollectionDownConditionalService.integrable_actualFirstCollectionDownReadout rewards C_star C_h i t
  have hu : Integrable u mu := ReferenceFirstCollectionUpConditionalService.integrable_actualFirstCollectionUpReadout rewards C_star C_h i t
  have hA : MeasurableSet[F] A := ReferenceFirstReplacementCollectionPredictableStages.OLD_measurable rate rewards C_star C_h control0 t.val i
  have hB : MeasurableSet[F] B := ReferenceFirstReplacementCollectionPredictableStages.FORMED_measurable rate rewards C_star C_h control0 t.val i
  have hDA : Integrable (A.indicator d) mu :=
    hd.indicator (ReferenceFirstReplacementCollectionPredictableStages.OLD_borel rate rewards C_star C_h control0 t.val i)
  have hUB : Integrable (B.indicator u) mu :=
    hu.indicator (ReferenceFirstReplacementCollectionPredictableStages.FORMED_borel rate rewards C_star C_h control0 t.val i)
  have hsum := condExp_add hDA hUB F
  have hmaskD := condExp_indicator hd hA
  have hmaskU := condExp_indicator hu hB
  have hfield : F = ReferenceSourceCurrentControlFreshness.m_t p control0 t :=
    ReferenceSourcePhysicalFlagConditionalLaw.sourcePrefixField_eq_m_t control0 t
  have hcondD : mu[d | F] =ᵐ[mu]
      ReferenceFirstCollectionDownConditionalService.actualFirstCollectionDownFreshSection (rate := rate) rewards C_star C_h control0 i t := by
    rw [hfield]
    exact ReferenceFirstCollectionDownConditionalService.actual_first_collection_down_condExp rewards C_star C_h control0 i t
  have hcondU : mu[u | F] =ᵐ[mu]
      ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpFreshSection (rate := rate) rewards C_star C_h control0 i t := by
    rw [hfield]
    exact ReferenceFirstCollectionUpConditionalService.actual_first_collection_up_condExp rewards C_star C_h control0 i t
  rw [service_eq_masked_readouts]
  filter_upwards [hsum, hmaskD, hmaskU, hcondD, hcondU] with z hsum hmaskD hmaskU hcondD hcondU
  change mu[A.indicator d + B.indicator u | F] z = _
  rw [hsum]
  change mu[A.indicator d | F] z + mu[B.indicator u | F] z = _
  rw [hmaskD, hmaskU]
  by_cases hi : i ∈ ReferenceFirstReplacementCollectionPendingFoundation.P_repl rate rewards C_star C_h control0 t.val z
  · have hiSet : z ∈ {z | i ∈ ReferenceFirstReplacementCollectionPendingFoundation.P_repl
        rate rewards C_star C_h control0 t.val z} := hi
    rw [Set.indicator_of_mem hiSet]
    rcases (pending_service_data rate rewards C_star C_h control0 t i z hi).1 with ho | hf
    · have hn : z ∉ B := fun hf => ReferenceFirstReplacementCollectionPredictableStages.OLD_FORMED_disjoint
        rate rewards C_star C_h control0 t.val i z ⟨ho, hf⟩
      have hoSet : z ∈ A := ho
      rw [Set.indicator_of_mem hoSet, Set.indicator_of_notMem hn, add_zero, hcondD]
      exact downFreshSection_of_OLD rate rewards C_star C_h control0 t i z ho
    · have hn : z ∉ A := fun ho => ReferenceFirstReplacementCollectionPredictableStages.OLD_FORMED_disjoint
        rate rewards C_star C_h control0 t.val i z ⟨ho, hf⟩
      have hfSet : z ∈ B := hf
      rw [Set.indicator_of_notMem hn, Set.indicator_of_mem hfSet, zero_add, hcondU]
      exact upFreshSection_of_FORMED rate rewards C_star C_h control0 t i z hf
  · have hnA : z ∉ A := ReferenceFirstReplacementCollectionPredictableStages.not_OLD_of_not_pending rate rewards C_star C_h control0 t.val i z hi
    have hnB : z ∉ B := ReferenceFirstReplacementCollectionPredictableStages.not_FORMED_of_not_pending rate rewards C_star C_h control0 t.val i z hi
    rw [Set.indicator_of_notMem hnA, Set.indicator_of_notMem hnB]
    have hiSet : z ∉ {z | i ∈ ReferenceFirstReplacementCollectionPendingFoundation.P_repl
        rate rewards C_star C_h control0 t.val z} := hi
    rw [Set.indicator_of_notMem hiSet, add_zero]

/-- Pending-point form used by the separate actual collection waiting assembly.
All exceptional paths stay in the unchanged pending mask. -/
theorem actual_first_replacement_collection_condExp_of_pending
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (control0 : ContinuousLearningRows.TimeControl p) (n : ℕ) (hn : n < p.T)
    (i : Fin (p.m - 1)) :
    ∀ᵐ z ∂BootstrapPrivateRoundStreams.sourceInputLaw p,
      i ∈ ReferenceFirstReplacementCollectionPendingFoundation.P_repl rate rewards C_star C_h control0 n z →
      (BootstrapPrivateRoundStreams.sourceInputLaw p)[
        (fun z => (ReferenceFirstReplacementCollectionActualCalendarTasks.service rate rewards C_star C_h control0 n i z : ℝ)) |
        ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (n + 1)] z =
        (ReferenceFirstCollectionUpConditionalService.positiveRewardCount rewards ⟨n, hn⟩ : ℝ) / (8 * (p.m - 1 : ℝ) * p.K) := by
  filter_upwards [actual_first_replacement_collection_condExp rate rewards C_star C_h control0 ⟨n, hn⟩ i]
    with z hz
  intro hi
  have hiSet : z ∈ {z | i ∈ ReferenceFirstReplacementCollectionPendingFoundation.P_repl
      rate rewards C_star C_h control0 n z} := hi
  exact hz.trans (Set.indicator_of_mem hiSet _)

end Bandits.Support.ReferenceFirstReplacementCollectionCalendarServiceLaw

end
