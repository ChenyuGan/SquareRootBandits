/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveInspectedNumericalPast

/-!
# Actual first-live numerical cells in the inspected field

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:140-188,256-264`,
`sources/zip4/manuscript/05_binary_transport.tex:293-308,331-345`,
`sources/zip4/manuscript/06_interruptions.tex:391-397,425-426`,
`sources/zip4/manuscript/07_public_setup.tex:127-164`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-64`.

The field is exactly the pullback of the existing inspected history field to
the original first-live source stratum. Calendar presence and membership in
the first-live cutoff prefix are separate steps. Real reward and rate vectors
keep their full product Borel spaces. All results here are deterministic
internal support results, not queue, overflow, law, or manuscript closure.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceFirstWindowNumericalStream

namespace Bandits.Support.ReferenceFirstLiveInspectedNumericalCells

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev RewardTable := ActualInitializationPhysicalStep.GridRewardTable

variable {p : Parameters} (rate : RateInput p) (rewards : RewardTable p)
  (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val)

local notation "Z" => ReferenceFirstLiveInspectedNumericalPast.SourceZ
  rate rewards C_star C_h q t s hs
local notation "KZ" => ReferenceFirstLiveInspectedNumericalPast.InspectedOnZ
  rate rewards C_star C_h q t s hs
local notation "n" => t.val - s

theorem sourceCrossing (z : Z) :
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z.val rewards C_star C_h rate)).crossing.isSome = true :=
  z.property.2.1

theorem sourceElapsed (z : Z) :
    ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z.val rewards C_star C_h rate)).completed = s :=
  z.property.2.2

theorem sourceCountSpan (z : Z) :
    ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z.val rewards C_star C_h rate)).completed + n ≤ p.T := by
  rw [sourceElapsed rate rewards C_star C_h q t s hs z]
  omega

def countRun (z : Z) :=
  actualFirstLiveRun rate z.val rewards C_star C_h
    (sourceCrossing rate rewards C_star C_h q t s hs z) n
    (sourceCountSpan rate rewards C_star C_h q t s hs z)

private def countWindow (z : Z) :=
  actualFirstLiveWindow rate z.val rewards C_star C_h
    (sourceCrossing rate rewards C_star C_h q t s hs z) n
    (sourceCountSpan rate rewards C_star C_h q t s hs z)

private theorem countRun_length (z : Z) :
    (countRun rate rewards C_star C_h q t s hs z).records.length = n :=
  ReferenceActivePhysicalHorizon.run_record_count _ _ _ _ _ _ _ _

def countRecord (k : Fin n) (z : Z) :
    ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) :=
  (countRun rate rewards C_star C_h q t s hs z).records[k.val]'(by
    rw [countRun_length]; exact k.isLt)

private theorem countRun_eq_suffix_take (z : Z) :
    (countRun rate rewards C_star C_h q t s hs z).records =
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z.val rewards C_star C_h).take n := by
  let x : ReferenceGeneratedDownAmbiguityMeasurability.GeneratedLaunchFiber
      (rate := rate) rewards C_star C_h s :=
    ⟨z.val, sourceCrossing rate rewards C_star C_h q t s hs z,
      sourceElapsed rate rewards C_star C_h q t s hs z⟩
  have hstate : ReferenceFirstLaunchNumericalCell.launchState rate z.val rewards C_star C_h
      (sourceCrossing rate rewards C_star C_h q t s hs z) =
      (ReferenceGeneratedDownAmbiguityMeasurability.generatedActiveRunInput
        (rate := rate) rewards C_star C_h s x).val.1 := by
    exact Option.some.inj
      ((ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
        rate z.val rewards C_star C_h (sourceCrossing rate rewards C_star C_h q t s hs z)).symm.trans
        (ReferenceCompletePhysicalHistory.correctedLaunch_eq_some_payload
          rate z.val rewards C_star C_h
          (ReferenceGeneratedDownAmbiguityMeasurability.generatedLaunch_ne_none
            (rate := rate) rewards C_star C_h s x)))
  have heq : countRun rate rewards C_star C_h q t s hs z =
      ReferenceActiveHorizonMeasurability.runOfInput s n (by omega)
        (ReferenceGeneratedDownAmbiguityMeasurability.generatedActiveRunInput
          (rate := rate) rewards C_star C_h s x) := by
    unfold countRun actualFirstLiveRun ReferenceActiveHorizonMeasurability.runOfInput
    simp only [sourceElapsed rate rewards C_star C_h q t s hs z]
    rfl
  rw [heq]
  exact ReferenceGeneratedDownAmbiguityMeasurability.generatedRun_records_eq_completeSuffixRecords_take
    rewards C_star C_h s n (by omega) x

/-- The count-`n` window is literally the cutoff prefix of the actual suffix
taken to `n`; cutoff exclusion is distinct from calendar absence. -/
theorem countWindow_eq_completeSuffix_take (z : Z) :
    actualFirstLiveWindow rate z.val rewards C_star C_h z.property.2.1 n
      (sourceCountSpan rate rewards C_star C_h q t s hs z) =
      ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        ((ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z.val rewards C_star C_h).take n) := by
  change ReferenceFirstLiveConfirmationHistory.firstLiveWindow
    (countRun rate rewards C_star C_h q t s hs z).records = _
  rw [countRun_eq_suffix_take]

private theorem countRecord_fields (k : Fin n) (z : Z) :
    (countRecord rate rewards C_star C_h q t s hs k z).input.rows = z.val.1.2 ∧
    (countRecord rate rewards C_star C_h q t s hs k z).input.selected =
      ActualInitializationPhysicalStep.selectedRowIndex p z.val ∧
    (countRecord rate rewards C_star C_h q t s hs k z).input.rewards = rewards ∧
    (countRecord rate rewards C_star C_h q t s hs k z).input.time.val = s + k.val := by
  let E := countRun rate rewards C_star C_h q t s hs z
  let r := countRecord rate rewards C_star C_h q t s hs k z
  have hm : r ∈ E.records := List.getElem_mem _
  have hi := ReferenceActivePhysicalHorizon.run_record_inputs
    _ _ _ _ _ _ _ _ r hm
  refine ⟨hi.1, hi.2.1, hi.2.2, ?_⟩
  have ht := ReferenceActivePhysicalHorizon.run_time_values
    (ReferenceFirstLaunchNumericalCell.launchState rate z.val rewards C_star C_h
      (sourceCrossing rate rewards C_star C_h q t s hs z)) z.val.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p z.val) rewards _ n
    (sourceCountSpan rate rewards C_star C_h q t s hs z)
    (actualFirstLiveSeed rate z.val rewards C_star C_h
      (sourceCrossing rate rewards C_star C_h q t s hs z)).activeAtStart
  have hj : k.val < E.records.length := by rw [countRun_length]; exact k.isLt
  have h := List.getElem_of_eq ht (by
    simpa only [List.length_map, E, countRun, actualFirstLiveRun] using hj)
  simpa only [List.getElem_map, ReferenceActivePhysicalHorizon.calendar,
    List.getElem_range', one_mul, sourceElapsed rate rewards C_star C_h q t s hs z,
    r, countRecord, E, countRun, actualFirstLiveRun] using h

/-- At every local strict-past offset the original calendar record exists,
even when that record lies after the first-live cutoff. -/
theorem actualRecord_local (k : Fin n) (z : Z) :
    ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
      ⟨s + k.val, by omega⟩ z.val =
      some (countRecord rate rewards C_star C_h q t s hs k z) := by
  have hstart : ReferenceCompletePhysicalHistory.physicalStart
      rate z.val rewards C_star C_h = s := sourceElapsed rate rewards C_star C_h q t s hs z
  have hrec := congrArg (fun records => records[k.val]?)
    (countRun_eq_suffix_take rate rewards C_star C_h q t s hs z)
  rw [List.getElem?_take, ite_eq_left k.isLt] at hrec
  have hj : k.val < (countRun rate rewards C_star C_h q t s hs z).records.length := by
    rw [countRun_length]; exact k.isLt
  rw [List.getElem?_eq_getElem hj] at hrec
  simpa only [ReferenceSourcePrefixHistoryFiltration.actualRecord, hstart,
    show s ≤ s + k.val by omega, ite_true, Nat.add_sub_cancel_left, countRecord] using hrec.symm

private theorem measurable_of_some {X Y : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] (f : X → Y) (hf : Measurable (fun x => some (f x))) :
    Measurable f := by
  have he : Measurable (Equiv.optionEquivSumPUnit Y) := comap_measurable _
  have hi : MeasurableEmbedding (@Sum.inl Y PUnit) :=
    ⟨Sum.inl_injective, measurable_inl, fun _ hs => hs.inl_image⟩
  exact hi.measurable_comp_iff.mp (he.comp hf)

private theorem measurable_countRecordCode (k : Fin n) :
    Measurable[KZ] (fun z : Z => ReferenceActiveHorizonMeasurability.roundRecordCode
      (countRecord rate rewards C_star C_h q t s hs k z)) := by
  apply @measurable_of_some Z _ KZ _
  convert ReferenceFirstLiveInspectedNumericalPast.measurable_pastRoundObservationAt
    rate rewards C_star C_h q t s hs k using 1
  funext z
  change some _ = (ReferenceSourcePrefixHistoryFiltration.actualRecord
    rate rewards C_star C_h ⟨s + k.val, by omega⟩ z.val).map _
  rw [actualRecord_local]
  rfl

/- The following completion is used only to evaluate analytical projections.
Its future controls are never asserted to be the original future controls.
The original incoming state and every control that can be read by the earlier
round are retained; the projection equalities below are proved separately. -/
private def inspectedRows (control0 : ContinuousLearningRows.TimeControl p) (z : Z) :
    CompletePublicTable.CompleteRows p :=
  fun _ => (ReferenceSourceOwnHistoryContainment.selectedForwardRow z.val,
    fun v : Fin p.T => if hv : v.val < t.val then
      ReferenceSourceOwnHistoryContainment.selectedControlPrefix t.val
        (Nat.le_of_lt t.isLt) z.val ⟨v.val, hv⟩ else control0)

private theorem measurable_pi_of_coordinates {X I : Type*} [mX : MeasurableSpace X]
    {F : I → Type*} [∀ i, MeasurableSpace (F i)] (f : X → ∀ i, F i)
    (hf : ∀ i, Measurable (fun x => f x i)) : Measurable f :=
  measurable_pi_iff.mpr hf

private theorem measurable_inspectedRows (control0 : ContinuousLearningRows.TimeControl p) :
    Measurable[KZ] (inspectedRows rate rewards C_star C_h q t s hs control0) := by
  apply measurable_pi_of_coordinates (mX := KZ)
  intro j
  apply (ReferenceFirstLiveInspectedNumericalPast.measurable_selectedForwardRow
    rate rewards C_star C_h q t s hs).prodMk
  apply measurable_pi_of_coordinates (mX := KZ)
  intro v
  by_cases hv : v.val < t.val
  · simpa only [inspectedRows, dite_eq_left hv, Function.comp_def] using
      (measurable_pi_apply ⟨v.val, hv⟩).comp
        (ReferenceFirstLiveInspectedNumericalPast.measurable_selectedControlPrefix
          rate rewards C_star C_h q t s hs)
  · simp only [dite_eq_right hv]
    exact measurable_const

private theorem inspectedRows_control (control0 : ContinuousLearningRows.TimeControl p)
    (z : Z) (v : Fin p.T) (hv : v.val < t.val) (j : Fin (M p)) :
    (inspectedRows rate rewards C_star C_h q t s hs control0 z j).2 v =
      (z.val.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z.val)).2 v := by
  simp only [inspectedRows, dite_eq_left hv,
    ReferenceSourceOwnHistoryContainment.selectedControlPrefix]
  rfl

private def inspectedInput (control0 : ContinuousLearningRows.TimeControl p)
    (k : Fin n) (z : Z) : ReferenceActivePhysicalStep.RoundInput p rate where
  state := (countRecord rate rewards C_star C_h q t s hs k z).input.state
  rows := inspectedRows rate rewards C_star C_h q t s hs control0 z
  selected := (countRecord rate rewards C_star C_h q t s hs k z).input.selected
  time := (countRecord rate rewards C_star C_h q t s hs k z).input.time
  active := (countRecord rate rewards C_star C_h q t s hs k z).input.active
  rewards := rewards

private theorem measurable_inspectedInput (control0 : ContinuousLearningRows.TimeControl p)
    (k : Fin n) :
    Measurable[KZ] (inspectedInput rate rewards C_star C_h q t s hs control0 k) := by
  have hc := measurable_countRecordCode rate rewards C_star C_h q t s hs k
  have hstate : Measurable[KZ] (fun z : Z =>
      (countRecord rate rewards C_star C_h q t s hs k z).input.state) := by
    apply measurable_comap_iff.mpr
    exact measurable_fst.comp (measurable_snd.comp hc)
  have hj : Measurable[KZ] (fun z : Z =>
      (countRecord rate rewards C_star C_h q t s hs k z).input.selected) := by
    have heq : (fun z : Z =>
        (countRecord rate rewards C_star C_h q t s hs k z).input.selected) = fun _ => q := by
      funext z
      exact (countRecord_fields rate rewards C_star C_h q t s hs k z).2.1.trans
        (ReferenceFirstLiveNumericalPrefixTemporal.sourceStratum_facts
          rate rewards C_star C_h q t s hs z).1
    rw [heq]
    exact measurable_const
  have ht : Measurable[KZ] (fun z : Z =>
      (countRecord rate rewards C_star C_h q t s hs k z).input.time) := by
    have heq : (fun z : Z => (countRecord rate rewards C_star C_h q t s hs k z).input.time) =
        fun _ => (⟨s + k.val, by omega⟩ : Fin p.T) := by
      funext z
      exact Fin.ext (countRecord_fields rate rewards C_star C_h q t s hs k z).2.2.2
    rw [heq]
    exact measurable_const
  apply measurable_comap_iff.mpr
  exact (hstate.prodMk ((measurable_inspectedRows rate rewards C_star C_h q t s hs control0).prodMk
    (hj.prodMk (ht.prodMk measurable_const)))).subtype_mk

private theorem inspectedInput_current (control0 : ContinuousLearningRows.TimeControl p)
    (k : Fin n) (z : Z) :
    (inspectedInput rate rewards C_star C_h q t s hs control0 k z).row.2
        (inspectedInput rate rewards C_star C_h q t s hs control0 k z).time =
      (countRecord rate rewards C_star C_h q t s hs k z).input.row.2
        (countRecord rate rewards C_star C_h q t s hs k z).input.time := by
  have hf := countRecord_fields rate rewards C_star C_h q t s hs k z
  change (inspectedRows rate rewards C_star C_h q t s hs control0 z
    (countRecord rate rewards C_star C_h q t s hs k z).input.selected).2
      (countRecord rate rewards C_star C_h q t s hs k z).input.time = _
  rw [inspectedRows_control rate rewards C_star C_h q t s hs control0 z _ (by
    rw [hf.2.2.2]; omega)]
  simp only [ReferenceActivePhysicalStep.RoundInput.row, hf.1, hf.2.1]

private theorem inspectedInput_code (control0 : ContinuousLearningRows.TimeControl p)
    (k : Fin n) (z : Z) :
    ReferenceActiveHorizonMeasurability.roundRecordCode
      ⟨inspectedInput rate rewards C_star C_h q t s hs control0 k z,
        ReferenceActivePhysicalStep.step
          (inspectedInput rate rewards C_star C_h q t s hs control0 k z), rfl⟩ =
      ReferenceActiveHorizonMeasurability.roundRecordCode
        (countRecord rate rewards C_star C_h q t s hs k z) := by
  let r := countRecord rate rewards C_star C_h q t s hs k z
  have hf := countRecord_fields rate rewards C_star C_h q t s hs k z
  have hpast : ∀ v : Fin p.T, v.val < r.input.time.val →
      ((inspectedInput rate rewards C_star C_h q t s hs control0 k z).row.2 v).1
          ContinuousControlSlice.Label.prop =
        (r.input.row.2 v).1 ContinuousControlSlice.Label.prop := by
    intro v hv
    change ((inspectedRows rate rewards C_star C_h q t s hs control0 z r.input.selected).2 v).1 _ = _
    rw [inspectedRows_control rate rewards C_star C_h q t s hs control0 z v (by
      change v.val < (countRecord rate rewards C_star C_h q t s hs k z).input.time.val at hv
      rw [hf.2.2.2] at hv; omega)]
    simp only [ReferenceActivePhysicalStep.RoundInput.row, r, hf.1, hf.2.1]
  have h := ReferenceInspectedPastRoundObservations.roundRecordCode_eq_of_temporal_reads
    (inspectedInput rate rewards C_star C_h q t s hs control0 k z) r.input
    rfl rfl rfl hf.2.2.1.symm
    (inspectedInput_current rate rewards C_star C_h q t s hs control0 k z) hpast
  exact h

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
    liveCutoffTag rate r owned base row out =
      (match (ReferenceActiveDispatchTemporal.liveOutcomeData r owned base row out).2.2 with
      | .inr (.inr (.inr _)) => true
      | _ => false) := by
  cases out <;> rfl

private theorem cutoffChosen_live
    (input : ReferenceActivePhysicalStep.RoundInput p rate)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ)
    (hphase : input.state.coordinator = .live r owned base) :
    ReferenceCollectionPhaseHistory.cutoffChosen input =
      liveCutoffTag rate (ReferenceActivePhysicalStep.liveRegistersAt r input.time)
        (ReferenceActivePhysicalStep.liveOwnedAt r owned input.time) base input.row
        (CoordinatorRoundDispatch.dispatchLive
          (ReferenceActivePhysicalStep.liveInput input r owned base)) := by
  dsimp only [ReferenceCollectionPhaseHistory.cutoffChosen,
    ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch]
  simp only [hphase, CoordinatorRoundDispatch.dispatch]
  cases CoordinatorRoundDispatch.dispatchLive
    (ReferenceActivePhysicalStep.liveInput input r owned base) <;> rfl

private theorem cutoffChosen_eq_of_current
    (state : ReferenceActivePhysicalStep.State p rate)
    (rows otherRows : CompletePublicTable.CompleteRows p)
    (selected otherSelected : Fin (M p)) (time : Fin p.T)
    (active : ∀ i, (state.activations i).val ≤ time.val + 1)
    (rewards otherRewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (hcurrent : (rows selected).2 time = (otherRows otherSelected).2 time) :
    ReferenceCollectionPhaseHistory.cutoffChosen
        ⟨state, rows, selected, time, active, rewards⟩ =
      ReferenceCollectionPhaseHistory.cutoffChosen
        ⟨state, otherRows, otherSelected, time, active, otherRewards⟩ := by
  classical
  cases hphase : state.coordinator with
  | first =>
      dsimp only [ReferenceCollectionPhaseHistory.cutoffChosen,
        ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch]
      simp only [hphase, CoordinatorRoundDispatch.dispatch]
      rfl
  | live r owned base =>
      have hdata := ReferenceActiveDispatchTemporal.liveOutcomeData_eq_of_current
        (ReferenceActivePhysicalStep.liveRegistersAt r time)
        (ReferenceActivePhysicalStep.liveOwnedAt r owned time) base
        (rows selected) (otherRows otherSelected) hcurrent
      have htag := congrArg (fun data =>
        match data.2.2 with
        | .inr (.inr (.inr _)) => true
        | _ => false) hdata
      rw [← liveCutoffTag_eq_projection rate, ← liveCutoffTag_eq_projection rate] at htag
      rw [cutoffChosen_live rate _ r owned base hphase,
        cutoffChosen_live rate _ r owned base hphase]
      simpa only [ReferenceActivePhysicalStep.liveInput,
        ReferenceActivePhysicalStep.RoundInput.row, liveCutoffTag] using htag
  | collection payload ledger proposal =>
      dsimp only [ReferenceCollectionPhaseHistory.cutoffChosen,
        ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch]
      simp only [hphase]
      by_cases hc : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
      · simp only [dite_eq_left hc, CoordinatorRoundDispatch.dispatch]
        rfl
      · simp only [dite_eq_right hc]
  | dagger =>
      dsimp only [ReferenceCollectionPhaseHistory.cutoffChosen,
        ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch]
      simp only [hphase]

private theorem cutoffChosen_congr (left right : ReferenceActivePhysicalStep.RoundInput p rate)
    (hstate : left.state = right.state) (htime : left.time = right.time)
    (hcurrent : left.row.2 left.time = right.row.2 right.time) :
    ReferenceCollectionPhaseHistory.cutoffChosen left =
      ReferenceCollectionPhaseHistory.cutoffChosen right := by
  cases left
  cases right
  dsimp only at hstate htime hcurrent
  cases hstate
  cases htime
  exact cutoffChosen_eq_of_current rate _ _ _ _ _ _ _ _ _ hcurrent


private def outcomeIsCutoff : ReferenceLiveDispatchOutputMeasurability.OutcomeData p → Bool
  | .cutoffChosen _ _ _ => true
  | _ => false

private theorem measurable_cutoffChosen
    {rate : ReferenceActivePhysicalStep.RateInput p} :
    Measurable (ReferenceCollectionPhaseHistory.cutoffChosen (p := p) (rate := rate)) := by
  apply measurable_of_restrict_of_restrict_compl
    ReferenceFirstLiveCoordinatorStepMeasurability.measurableSet_liveSet
  · have htag : Measurable (outcomeIsCutoff (p := p)) := measurable_of_countable _
    have h := htag.comp
      (ReferenceLiveDispatchOutputMeasurability.measurable_dispatchLive_outcomeData.comp
        (ReferenceFirstLiveCoordinatorStepMeasurability.measurable_liveCoordinates
          (p := p) (rate := rate)))
    convert h using 1
    funext x
    dsimp only [Function.comp_def, Set.domRestrict,
      ReferenceFirstLiveCoordinatorStepMeasurability.liveCoordinates]
    rw [ReferenceLiveDispatchOutputMeasurability.outcomeData_originalInput]
    unfold ReferenceCollectionPhaseHistory.cutoffChosen ReferenceActivePhysicalStep.prepare
    dsimp only
    rw [ReferenceLiveDispatchMeasurability.canonicalDispatch_live_reconstruction
      x.val _ _ _ (ReferenceFirstLiveCoordinatorStepMeasurability.live_state x)]
    cases CoordinatorRoundDispatch.dispatchLive (ReferenceActivePhysicalStep.liveInput x.val
      (ReferenceFirstLiveCoordinatorStepMeasurability.liveRegisters x)
      (ReferenceFirstLiveCoordinatorStepMeasurability.liveOwned x)
      (ReferenceFirstLiveCoordinatorStepMeasurability.liveBase x)) <;> rfl
  · have heq : (fun x : ↥((ReferenceFirstLiveCoordinatorStepMeasurability.liveSet
        (p := p) (rate := rate))ᶜ) => ReferenceCollectionPhaseHistory.cutoffChosen x.val) =
        fun _ => false := by
      funext x
      cases hc : x.val.state.coordinator with
      | first =>
          simp only [ReferenceCollectionPhaseHistory.cutoffChosen,
            ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch,
            hc, CoordinatorRoundDispatch.dispatch]
          rfl
      | live r q base =>
          exfalso
          exact x.property ⟨(r.payload,
            ReferenceActivePhysicalStepMeasurability.encodeLive r q base), by
              simp only [ReferenceActivePhysicalStepMeasurability.encodeState,
                hc, ReferenceActivePhysicalStepMeasurability.encodeCoordinator]⟩
      | collection payload ledger proposal =>
          simp only [ReferenceCollectionPhaseHistory.cutoffChosen,
            ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch,
            hc, CoordinatorRoundDispatch.dispatch]
          by_cases hcut : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
          · simp only [hcut, and_self, dite_true]
            rfl
          · simp only [hcut, dite_false]
      | dagger =>
          simp only [ReferenceCollectionPhaseHistory.cutoffChosen,
            ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch, hc]
    change Measurable (fun x : ↥((ReferenceFirstLiveCoordinatorStepMeasurability.liveSet
      (p := p) (rate := rate))ᶜ) => ReferenceCollectionPhaseHistory.cutoffChosen x.val)
    rw [heq]
    exact measurable_const


private theorem measurable_countCutoff (control0 : ContinuousLearningRows.TimeControl p)
    (k : Fin n) :
    Measurable[KZ] (fun z : Z => ReferenceCollectionPhaseHistory.cutoffChosen
      (countRecord rate rewards C_star C_h q t s hs k z).input) := by
  have heq : (fun z : Z => ReferenceCollectionPhaseHistory.cutoffChosen
      (countRecord rate rewards C_star C_h q t s hs k z).input) =
      fun z => ReferenceCollectionPhaseHistory.cutoffChosen
        (inspectedInput rate rewards C_star C_h q t s hs control0 k z) := by
    funext z
    exact cutoffChosen_congr rate _ _ rfl rfl
      (inspectedInput_current rate rewards C_star C_h q t s hs control0 k z).symm
  rw [heq]
  exact measurable_cutoffChosen.comp
    (measurable_inspectedInput rate rewards C_star C_h q t s hs control0 k)

private theorem measurable_countWindow_length (control0 : ContinuousLearningRows.TimeControl p) :
    Measurable[KZ] (fun z : Z =>
      (countWindow rate rewards C_star C_h q t s hs z).length) := by
  let flags (z : Z) : Fin n → Bool := fun k =>
    ReferenceCollectionPhaseHistory.cutoffChosen
      (countRecord rate rewards C_star C_h q t s hs k z).input
  have hflags : Measurable[KZ] flags :=
    measurable_pi_of_coordinates (mX := KZ) flags
      (measurable_countCutoff rate rewards C_star C_h q t s hs control0)
  let f (v : Fin n → Bool) := ((List.ofFn v).takeWhile (! ·)).length
  have hf : Measurable f := measurable_of_countable _
  convert hf.comp hflags using 1
  funext z
  let E := countRun rate rewards C_star C_h q t s hs z
  have hlist : List.ofFn (flags z) = E.records.map
      (fun record => ReferenceCollectionPhaseHistory.cutoffChosen record.input) := by
    apply List.ext_getElem
    · simp only [List.length_ofFn, List.length_map, E, countRun_length]
    · intro j hj hj'
      simp only [List.getElem_ofFn, List.getElem_map]
      rfl
  change (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length =
    ((List.ofFn (flags z)).takeWhile (! ·)).length
  rw [hlist]
  simp only [ReferenceFirstLiveConfirmationHistory.firstLiveWindow,
    List.takeWhile_map, List.length_map, Function.comp_def]

private theorem measurable_sigma_sections {ι : Type*} {F : ι → Type*}
    [∀ i, MeasurableSpace (F i)] {Y : Type*} [MeasurableSpace Y]
    (f : Sigma F → Y) (hf : ∀ i, Measurable (fun x : F i => f ⟨i, x⟩)) :
    Measurable f := by
  intro u hu
  change MeasurableSet[(⨅ i, (inferInstance : MeasurableSpace (F i)).map (Sigma.mk i))]
    {x | f x ∈ u}
  rw [MeasurableSpace.measurableSet_iInf]
  intro i
  rw [MeasurableSpace.map_def]
  exact hf i hu

private def preparedStatusTag {rate : ReferenceActivePhysicalStep.RateInput p}
    (z : FollowerVaryingActivationMeasurability.VaryingPreparedOutput p rate) : Option (Fin 3) :=
  z.2.2.2.map fun data => FollowerDownMeasurability.followerStatusCode
    (FollowerDownMeasurability.followerStatusOfCode data.1.1.1.status)

private theorem measurable_preparedStatusTag {rate : ReferenceActivePhysicalStep.RateInput p} :
    Measurable (preparedStatusTag (p := p) (rate := rate)) := by
  have hs : Measurable (fun z : FollowerObservationStageMeasurabilityRepair.CarriedState p rate =>
      FollowerDownMeasurability.followerStatusCode
        (FollowerDownMeasurability.followerStatusOfCode z.1.1.status)) := by
    apply measurable_sigma_sections
    intro index
    change Measurable (fun _ => FollowerDownMeasurability.followerStatusCode
      (FollowerDownMeasurability.followerStatusOfCode index.1.status))
    exact measurable_const
  have ht : Measurable (fun z : Unit ⊕
      (FollowerPrepareJointMeasurability.CarriedState p rate ×
        FollowerPrepareJointMeasurability.LocalMemoryCode p) =>
      z.elim (fun _ => (none : Option (Fin 3)))
        (fun data => some (FollowerDownMeasurability.followerStatusCode
          (FollowerDownMeasurability.followerStatusOfCode data.1.1.1.status)))) :=
    Measurable.sumElim measurable_const
      ((measurable_of_countable (some : Fin 3 → Option (Fin 3))).comp (hs.comp measurable_fst))
  apply measurable_sigma_sections
  intro activation
  convert ht.comp ((FollowerPrepareJointMeasurability.measurable_incomingConfigurationToSum rate).comp
    (measurable_snd.comp measurable_snd)) using 1
  funext z
  cases hi : z.2.2 <;>
    simp only [preparedStatusTag, Function.comp_def,
      FollowerPrepareJointMeasurability.incomingConfigurationToSum, hi,
      Option.map_none, Option.map_some, Sum.elim_inl, Sum.elim_inr]

private theorem preparedStatusTag_ordinary
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (input : ReferenceActivePhysicalStep.RoundInput p rate) (i : Fin (p.m - 1))
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (ho : ((ReferenceActivePhysicalStep.prepare input).followers.followers i).configuration =
      .ordinary state memory) :
    preparedStatusTag (ReferenceActivePhysicalStepMeasurability.preparedFollowerCode input i) =
      some (FollowerDownMeasurability.followerStatusCode state.status) := by
  let tag (config : DeclaredFollowerLocalRound.LocalConfiguration p rate) : Option (Fin 3) :=
    match config with
    | .dagger => none
    | .ordinary state _ => some (FollowerDownMeasurability.followerStatusCode state.status)
  have h := congrArg (fun prepared => tag prepared.configuration)
    (ReferenceActivePhysicalStepMeasurability.preparedFollowerCode_reconstruct input i)
  rw [ho] at h
  change _ = some (FollowerDownMeasurability.followerStatusCode state.status) at h
  convert h using 1
  generalize hz : ReferenceActivePhysicalStepMeasurability.preparedFollowerCode input i = z
  cases hi : z.2.2.2 <;>
    simp only [preparedStatusTag, FollowerPrepareJointMeasurability.preparedRoundOfOutput,
      FollowerPrepareJointMeasurability.localConfigurationOfIncoming, hi,
      Option.map_none, Option.map_some, tag,
      FollowerObservationStageMeasurabilityRepair.reconstructCarriedState,
      FollowerDownMeasurability.followerStateOfCode]

private def scoreVector (p : Parameters) (scores : Fin p.K → ℕ) : Fin p.K → ℝ :=
  fun a => ScoreWeights.scoreWeight (AssignmentScoreReconstruction.sourceWeightBase p) (scores a)

private theorem sourceWeights_register_range
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (hunit : ∀ a, r.payload.anchor a = 1) :
    ∃ scores : Fin p.K → ℕ,
      ReferenceFirstWindowNumericalStream.sourceWeights r.payload r.complementWeights =
        scoreVector p scores := by
  classical
  refine ⟨fun a => if ha : a ∈ r.payload.slowSet.val then 0 else
    r.complementScores ⟨a, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ha⟩⟩, ?_⟩
  funext a
  by_cases ha : a ∈ r.payload.slowSet.val
  · simp only [ReferenceFirstWindowNumericalStream.sourceWeights, ha, dite_true,
      scoreVector, ScoreWeights.scoreWeight, pow_zero, hunit]
  · simp only [ReferenceFirstWindowNumericalStream.sourceWeights, ha, dite_false,
      scoreVector, CoordinatorLiveChoiceRecorderStep.Registers.complementWeights]

private theorem recordingMap_congr
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (a b : SnapshotRecordingKernel.Regime p) (va vb wa wb : Fin p.K → ℝ)
    (hva : ∀ j, 0 < va j) (hvb : ∀ j, 0 < vb j)
    (hwa : ∀ j, 0 < wa j) (hwb : ∀ j, 0 < wb j)
    (hloA : ∀ j, va j ≤ wa j) (hloB : ∀ j, vb j ≤ wb j)
    (hhiA : ∀ j, wa j ≤ 2 * va j) (hhiB : ∀ j, wb j ≤ 2 * vb j)
    (hab : a = b) (hv : va = vb) (hw : wa = wb)
    (row : CanonicalRecordingSlice.Slice p.m p.K) :
    SnapshotRecordingKernel.recordingMap p a true rate.eta.val rate.eta.property rate.sourceCap
      va wa hva hwa hloA hhiA row =
    SnapshotRecordingKernel.recordingMap p b true rate.eta.val rate.eta.property rate.sourceCap
      vb wb hvb hwb hloB hhiB row := by
  cases hab
  cases hv
  cases hw
  rfl


private theorem prepare_configuration_eq_of_roundInputs
    (left right : ReferenceActivePhysicalStep.RoundInput p rate)
    (hstate : left.state = right.state) (hselected : left.selected = right.selected)
    (htime : left.time = right.time)
    (hcurrent : left.row.2 left.time = right.row.2 right.time)
    (i : Fin (p.m - 1)) :
    ((ReferenceActivePhysicalStep.prepare left).followers.followers i).configuration =
      ((ReferenceActivePhysicalStep.prepare right).followers.followers i).configuration := by
  cases left with
  | mk leftState leftRows leftSelected leftTime leftActive leftRewards =>
    cases right with
    | mk rightState rightRows rightSelected rightTime rightActive rightRewards =>
      dsimp only at hstate hselected htime hcurrent
      cases hstate
      cases hselected
      cases htime
      have hproj := ReferenceActiveTemporalCausality.prepare_projections_eq_of_current
        (row := leftRows leftSelected) (otherRow := rightRows leftSelected) (t := leftTime)
        i (leftState.activations i) (leftActive i) (leftState.followers i) hcurrent
      exact congrArg Prod.snd hproj


private theorem measurable_cell_readout
    {rate : ReferenceActivePhysicalStep.RateInput p} {X : Type*} [MeasurableSpace X]
    (r : X → ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (c : ∀ x, ReferenceFirstWindowNumericalStream.ActualLiveSourceCell (r x))
    (hsel : Measurable (fun x =>
      ReferenceLiveDispatchOutputMeasurability.encodeSelection (c x).selected))
    (hstatus : Measurable (fun x => fun i : Fin (p.m - 1) =>
      FollowerDownMeasurability.followerStatusCode ((c x).states i).status))
    (hslice : Measurable (fun x => ((r x).input.row.2 (r x).input.time).1))
    (hreward : Measurable (fun x => fun a : Fin p.K =>
      (((r x).input.rewards (r x).input.time a).val : ℝ) / (D p : ℝ)))
    (hunit : ∀ x a, (c x).selected.view.payload.anchor a = 1)
    (hscore : ∀ x, ∃ scores : Fin p.K → ℕ,
      ReferenceFirstWindowNumericalStream.sourceWeights (c x).selected.view.payload
        (c x).selected.view.complementWeights = scoreVector p scores) :
    Measurable (fun x => ((c x).input.enabled,
      ((c x).input.recordedArm, ((c x).input.reward, (c x).input.rate)))) := by
  classical
  have hview := (comap_measurable
    (ReferenceDownReceptionMeasurability.choiceTimeViewObservation (p := p) (rate := rate))).comp
      (measurable_fst.comp hsel)
  have hpayload := measurable_fst.comp hview
  have hpobs := (comap_measurable
    (LaterAssignmentStartMeasurability.payloadObservation (p := p) (eta := rate.eta))).comp hpayload
  have hslow := (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp hpobs)))
  have haux := (AssignmentPayloadDerivedMeasurability.measurable_inputAuxiliary).comp hpayload
  have hpending := measurable_fst.comp (measurable_snd.comp hview)
  let weights (x : X) := ReferenceFirstWindowNumericalStream.sourceWeights
    (c x).selected.view.payload (c x).selected.view.complementWeights
  have hw : Measurable weights := by
    apply measurable_pi_iff.mpr
    intro a
    have hfast := (measurable_pi_apply a).comp
      (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp hview)))
    have hm : MeasurableSet {x | a ∈ (c x).selected.view.payload.slowSet.val} :=
      (Set.toFinite {u : Finset (Fin p.K) | a ∈ u}).measurableSet.preimage hslow
    have h : Measurable (fun x => if a ∈ (c x).selected.view.payload.slowSet.val then
        (1 : ℝ) else ReferenceDownReceptionMeasurability.choiceTimeViewWeightVector
          (c x).selected.view a) := measurable_const.ite hm hfast
    convert h using 1
    funext x
    by_cases ha : a ∈ (c x).selected.view.payload.slowSet.val
    · simp only [weights, ReferenceFirstWindowNumericalStream.sourceWeights, ha,
        dite_true, ite_true, hunit]
    · have hf : a ∈ CanonicalFastSampling.fastArmFinset (c x).selected.view.payload.slowSet :=
        Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ha⟩
      simp only [weights, ReferenceFirstWindowNumericalStream.sourceWeights, ha,
        dite_false, ite_false, ReferenceDownReceptionMeasurability.choiceTimeViewWeightVector,
        hf, dite_true]
  let WeightImage := Set.range (scoreVector p)
  let : Countable WeightImage := (Set.countable_range (scoreVector p)).to_subtype
  let key (x : X) := ((c x).selected.view.payload.slowSet.val,
    ((c x).selected.view.payload.auxiliaryArm, ((c x).selected.view.pendingAtChoice,
      ((fun i => FollowerDownMeasurability.followerStatusCode ((c x).states i).status),
        (⟨weights x, by obtain ⟨scores, h⟩ := hscore x; exact ⟨scores, h.symm⟩⟩ : WeightImage)))))
  have hkey : Measurable key := hslow.prodMk (haux.prodMk (hpending.prodMk
    (hstatus.prodMk hw.subtype_mk)))
  let KeyRange := Set.range key
  let code (x : X) : KeyRange := ⟨key x, x, rfl⟩
  let representative (k : KeyRange) : X := Classical.choose k.property
  let sourceMap (k : KeyRange) :=
    let z := representative k
    let selected := (c z).selected
    SnapshotRecordingKernel.recordingMap p
      (.live selected.view.payload.assignment
        { missing := selected.view.pendingAtChoice, status := fun i => ((c z).states i).status })
      true rate.eta.val rate.eta.property rate.sourceCap selected.view.payload.anchor (weights z)
      selected.view.payload.anchor_pos
      (ReferenceFirstWindowNumericalStream.sourceWeights_pos selected.view.payload
        selected.view.complementWeights selected.view.cutoff (r z).input.time (c z).choiceInputsValid)
      (ReferenceFirstWindowNumericalStream.sourceWeights_lower selected.view.payload
        selected.view.complementWeights selected.view.cutoff (r z).input.time (c z).choiceInputsValid)
      (ReferenceFirstWindowNumericalStream.sourceWeights_upper selected.view.payload
        selected.view.complementWeights selected.view.cutoff (r z).input.time (c z).choiceInputsValid)
  have hm (k : KeyRange) : Measurable (fun x => sourceMap k (((r x).input.row.2 (r x).input.time).1)) :=
    (SnapshotRecordingKernel.measurable_recordingMap p _ _ _ _ _ _ _ _ _ _ true).comp hslice
  have h := CoordinatorCollectionRunMeasurabilityRepair.measurable_of_countable_cases
    code hkey.subtype_mk (fun k x => sourceMap k (((r x).input.row.2 (r x).input.time).1)) hm
  have hmarker : Measurable (fun x => (c x).input.recordedArm) := by
    convert h using 1
    funext x
    have hk : key (representative (code x)) = key x := Classical.choose_spec (code x).property
    have hslowEq := congrArg (fun k => k.1) hk
    have hauxEq := congrArg (fun k => k.2.1) hk
    have hpendingEq := congrArg (fun k => k.2.2.1) hk
    have hstatusEq := congrArg (fun k => k.2.2.2.1) hk
    have hwEq := congrArg (fun k => k.2.2.2.2) hk
    dsimp only [key] at hslowEq hauxEq hpendingEq hstatusEq hwEq
    have hs : (c (representative (code x))).selected.view.payload.slowSet =
        (c x).selected.view.payload.slowSet := Subtype.ext hslowEq
    have ha : (c (representative (code x))).selected.view.payload.anchor =
        (c x).selected.view.payload.anchor := funext fun a => (hunit _ a).trans (hunit _ a).symm
    have hassignment : (c (representative (code x))).selected.view.payload.assignment =
        (c x).selected.view.payload.assignment := by
      simp only [AssignmentStartPayload.Input.assignment, hs, hauxEq]
    have hstates := congrArg (fun values => fun i =>
      FollowerDownMeasurability.followerStatusOfCode (values i)) hstatusEq
    simp only [FollowerDownMeasurability.followerStatusOfCode_code] at hstates
    have hweights := congrArg Subtype.val hwEq
    dsimp only [weights] at hweights
    have regimeCongr (a b : ActiveRoundActions.Assignment p.m p.K)
        (pa pb : Finset (Fin (p.m - 1)))
        (sa sb : Fin (p.m - 1) → ActiveRoundActions.FollowerStatus)
        (hab : a = b) (hp : pa = pb) (hs : sa = sb) :
        SnapshotRecordingKernel.Regime.live (p := p) a ⟨pa, sa⟩ = .live b ⟨pb, sb⟩ := by
      cases hab
      cases hp
      cases hs
      rfl
    have hregime := regimeCongr _ _ _ _ _ _ hassignment hpendingEq hstates
    rw [(c x).recordedArm_eq]
    dsimp only [ReferenceFirstWindowNumericalStream.sourceArm, sourceMap, weights]
    exact recordingMap_congr (rate := rate) _ _ _ _ _ _ _ _ _ _ _ _ _ _
      hregime.symm ha.symm hweights.symm _
  have hrate := AssignmentPayloadDerivedMeasurability.measurable_inputRate.comp hpayload
  have henabled : Measurable (fun _ : X => true) := measurable_const
  have hall := henabled.prodMk (hmarker.prodMk (hreward.prodMk hrate))
  convert hall using 1
  funext x
  rw [(c x).input_eq]
  rfl


private theorem sourceCell_anchor_one
    (z : Z)
    (k : Fin (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow rate z.val rewards
      C_star C_h (sourceCrossing rate rewards C_star C_h q t s hs z) (t.val - s)
      (sourceCountSpan rate rewards C_star C_h q t s hs z)).length) :
    ∀ a : Fin p.K,
      (ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt rate z.val rewards C_star C_h
        (sourceCrossing rate rewards C_star C_h q t s hs z) (t.val - s)
        (sourceCountSpan rate rewards C_star C_h q t s hs z) k).selected.view.payload.anchor a = 1 := by
  classical
  let hc := sourceCrossing rate rewards C_star C_h q t s hs z
  let span := sourceCountSpan rate rewards C_star C_h q t s hs z
  let I := ReferenceFirstLaunchNumericalCell.launchState rate z.val rewards C_star C_h hc
  let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed rate z.val rewards C_star C_h hc
  let E := ReferenceFirstWindowNumericalStream.actualFirstLiveRun rate z.val rewards C_star C_h hc
    (t.val - s) span
  let W := ReferenceFirstWindowNumericalStream.actualFirstLiveWindow rate z.val rewards C_star C_h hc
    (t.val - s) span
  let cell := ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt rate z.val rewards C_star C_h
    hc (t.val - s) span k
  have hcount : 0 < t.val - s := by
    have hw : W.IsPrefix E.records := List.takeWhile_prefix _
    have hlen : E.records.length = t.val - s := by
      dsimp [E, ReferenceFirstWindowNumericalStream.actualFirstLiveRun]
      exact ReferenceActivePhysicalHorizon.run_record_count _ _ _ _ _ _ _ _
    exact (Nat.zero_lt_of_lt k.isLt).trans_le (hw.length_le.trans_eq hlen)
  have hs : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z.val rewards C_star C_h rate)).completed < p.T := by
    rw [sourceElapsed rate rewards C_star C_h q t s hs z]
    exact lt_of_le_of_lt hs t.isLt
  have hbirth := ReferenceFirstDownRecoveryBudget.run_first_selected_payload I z.val.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p z.val) rewards _ (t.val - s) span
    seed.activeAtStart seed.coordinatorFirst k cell.selected cell.selection_actual
  obtain ⟨birth, hmem, htime, hbirth, _⟩ := hbirth
  have hfirst : ReferenceFirstLaunchNumericalCell.firstPhysicalRecord
      rate z.val rewards C_star C_h hc hs ∈ E.records := by
    obtain ⟨tail, htail⟩ := ReferenceCollectionPhaseHistory.run_records_prefix
      I z.val.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z.val)
      rewards _ 1 ((t.val - s) - 1) (by omega) seed.activeAtStart
    have htail' : E.records =
        (ReferenceFirstLaunchNumericalCell.firstPhysicalRun rate z.val rewards C_star C_h hc hs).records ++ tail := by
      simpa only [E, ReferenceFirstWindowNumericalStream.actualFirstLiveRun,
        ReferenceFirstLaunchNumericalCell.firstPhysicalRun, I,
        Nat.add_sub_of_le hcount] using htail
    rw [htail', ReferenceFirstLaunchNumericalCell.firstPhysicalRun_records]
    exact List.mem_append_left _ (List.mem_singleton_self _)
  have hfirstInputs := ReferenceFirstLaunchNumericalCell.firstPhysicalRecord_source_inputs
    rate z.val rewards C_star C_h hc hs
  have heq : birth = ReferenceFirstLaunchNumericalCell.firstPhysicalRecord
      rate z.val rewards C_star C_h hc hs :=
    ReferenceAssignmentPayloadChronology.run_records_time_injective I z.val.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p z.val) rewards _ (t.val - s) span
      seed.activeAtStart hmem hfirst (htime.trans hfirstInputs.2.1.symm)
  rw [heq] at hbirth
  have hdispatch : (ReferenceFirstLaunchNumericalCell.firstPhysicalRecord
      rate z.val rewards C_star C_h hc hs).output.preparation.coordinator =
      ReferenceActivePhysicalStep.dispatch
        (ReferenceFirstLaunchNumericalCell.firstPhysicalRecord rate z.val rewards C_star C_h hc hs).input := by
    rw [(ReferenceFirstLaunchNumericalCell.firstPhysicalRecord rate z.val rewards C_star C_h hc hs).output_eq]
    rfl
  have hfirstState : (ReferenceFirstLaunchNumericalCell.firstPhysicalRecord
      rate z.val rewards C_star C_h hc hs).input.state.coordinator = .first := by
    rw [hfirstInputs.1]
    exact seed.coordinatorFirst
  simp only [ReferenceAssignmentPayloadPersistence.InstallationBirth, hdispatch,
    ReferenceActivePhysicalStep.dispatch, hfirstState, CoordinatorRoundDispatch.dispatch] at hbirth
  cases hchosen : CoordinatorRoundDispatch.dispatchFirst
      (ReferenceActivePhysicalStep.firstInput
        (ReferenceFirstLaunchNumericalCell.firstPhysicalRecord rate z.val rewards C_star C_h hc hs).input) with
  | choiceDomainFailure installed =>
      simp only [hchosen] at hbirth
      exact False.elim hbirth
  | recorderBoundaryFailure installed =>
      simp only [hchosen] at hbirth
      exact False.elim hbirth
  | choiceRejected installed =>
      simp only [hchosen] at hbirth
      exact False.elim hbirth
  | chosen installed arm =>
      simp only [hchosen] at hbirth
      have hpayload := hbirth.1
      have hfacts := ReferenceFirstLaunchNumericalCell.first_installation_payload_facts
        rate z.val rewards C_star C_h hc hs installed arm hchosen
      intro a
      rw [hpayload]
      exact hfacts.2.1 a

private theorem sourceCell_sourceWeights_range
    (z : Z)
    (k : Fin (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow rate z.val rewards
      C_star C_h (sourceCrossing rate rewards C_star C_h q t s hs z) (t.val - s)
      (sourceCountSpan rate rewards C_star C_h q t s hs z)).length) :
    ∃ scores : Fin p.K → ℕ,
      let cell := ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt rate z.val rewards C_star C_h
        (sourceCrossing rate rewards C_star C_h q t s hs z) (t.val - s)
        (sourceCountSpan rate rewards C_star C_h q t s hs z) k
      ReferenceFirstWindowNumericalStream.sourceWeights cell.selected.view.payload
        cell.selected.view.complementWeights = scoreVector p scores := by
  classical
  let hc := sourceCrossing rate rewards C_star C_h q t s hs z
  let span := sourceCountSpan rate rewards C_star C_h q t s hs z
  let I := ReferenceFirstLaunchNumericalCell.launchState rate z.val rewards C_star C_h hc
  let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed rate z.val rewards C_star C_h hc
  let cell := ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt rate z.val rewards C_star C_h
    hc (t.val - s) span k
  change ∃ scores : Fin p.K → ℕ,
    ReferenceFirstWindowNumericalStream.sourceWeights cell.selected.view.payload
      cell.selected.view.complementWeights = scoreVector p scores
  have hunit : ∀ a : Fin p.K, cell.selected.view.payload.anchor a = 1 := by
    exact sourceCell_anchor_one rate rewards C_star C_h q t s hs z k
  have htruth := ReferenceFirstWindowRecordingTruth.run_first_live_window_recording_truth
    I z.val.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z.val) rewards _ (t.val - s) span
    seed.activeAtStart seed.coordinatorFirst seed.followers seed.memory seed.configuration
    seed.S_zero seed.delta_zero seed.backlog_zero seed.lastDown_none seed.unoccupied
    seed.bufferValid seed.chronologicalBuffer seed.bufferStamps seed.decoderValid k
  rcases htruth with ⟨_, _, states, memories, _, hbranch⟩
  rcases hbranch with hfirst | hcontinuing
  · rcases hfirst with ⟨installed, arm, _, _, _, selected, hselected, hselection, _⟩
    have heq : cell.selected = selected :=
      Option.some.inj (cell.selection_actual.symm.trans hselected)
    have hu : ∀ a, installed.registers.payload.anchor a = 1 := by
      simpa only [heq, hselection,
        ReferenceCoordinatorRecorderCallCorrespondence.selectionOfArm,
        ReferenceActivePhysicalStep.firstInput] using hunit
    rw [heq, hselection]
    exact sourceWeights_register_range installed.registers hu
  · rcases hcontinuing with
      ⟨r, q0, base, dispatched, _, continuation, arm, _, _, selected, hselected, hselection, _⟩
    have heq : cell.selected = selected :=
      Option.some.inj (cell.selection_actual.symm.trans hselected)
    have hu : ∀ a, r.payload.anchor a = 1 := by
      simpa only [heq, hselection,
        ReferenceCoordinatorRecorderCallCorrespondence.selectionOfArm,
        ReferenceActivePhysicalStep.liveInput, ReferenceActivePhysicalStep.liveRegistersAt] using hunit
    rw [heq, hselection]
    exact sourceWeights_register_range r hu


private abbrev LiveIndex (k : Fin n) :=
  {z : Z // k.val < (countWindow rate rewards C_star C_h q t s hs z).length}

private def indexedCellReadout (k : Fin n)
    (x : LiveIndex rate rewards C_star C_h q t s hs k) :
    ReferenceFirstLiveNumericalPrefixBorel.NumericalCellReadout p :=
  let cell := actualLiveSourceCellAt rate x.val.val rewards C_star C_h
    (sourceCrossing rate rewards C_star C_h q t s hs x.val) n
    (sourceCountSpan rate rewards C_star C_h q t s hs x.val) ⟨k.val, x.property⟩
  (cell.input.enabled, (cell.input.recordedArm, (cell.input.reward, cell.input.rate)))

private theorem measurable_indexedCellReadout
    (control0 : ContinuousLearningRows.TimeControl p) (k : Fin n) :
    Measurable[(KZ).comap Subtype.val]
      (indexedCellReadout rate rewards C_star C_h q t s hs k) := by
  let : MeasurableSpace (LiveIndex rate rewards C_star C_h q t s hs k) := (KZ).comap Subtype.val
  let record (x : LiveIndex rate rewards C_star C_h q t s hs k) :=
    (countWindow rate rewards C_star C_h q t s hs x.val)[k.val]'x.property
  let cell (x : LiveIndex rate rewards C_star C_h q t s hs k) :=
    actualLiveSourceCellAt rate x.val.val rewards C_star C_h
      (sourceCrossing rate rewards C_star C_h q t s hs x.val) n
      (sourceCountSpan rate rewards C_star C_h q t s hs x.val) ⟨k.val, x.property⟩
  have hrecord (x) : record x = countRecord rate rewards C_star C_h q t s hs k x.val := by
    have hp : countWindow rate rewards C_star C_h q t s hs x.val <+:
        (countRun rate rewards C_star C_h q t s hs x.val).records := List.takeWhile_prefix _
    exact hp.getElem x.property
  have hproj : Measurable[inferInstance, KZ]
      (Subtype.val : LiveIndex rate rewards C_star C_h q t s hs k → Z) :=
    comap_measurable _
  have hcode : Measurable (fun x => ReferenceActiveHorizonMeasurability.roundRecordCode (record x)) := by
    convert (measurable_countRecordCode rate rewards C_star C_h q t s hs k).comp hproj using 1
    funext x
    rw [hrecord]
    rfl
  have hsel : Measurable (fun x =>
      ReferenceLiveDispatchOutputMeasurability.encodeSelection (cell x).selected) := by
    apply measurable_of_some
    have h := measurable_fst.comp (measurable_fst.comp
      (measurable_snd.comp (measurable_snd.comp hcode)))
    convert h using 1
    funext x
    have hp : (record x).output.preparation.coordinator =
        ReferenceActivePhysicalStep.dispatch (record x).input := by
      rw [(record x).output_eq]
      rfl
    change some _ = (ReferenceActivePhysicalStep.dispatch (record x).input).selection.map _
    have hselected : (record x).output.preparation.coordinator.selection = some (cell x).selected :=
      (cell x).selection_actual
    rw [← hp, hselected]
    rfl
  have hinput := (measurable_inspectedInput rate rewards C_star C_h q t s hs control0 k).comp hproj
  have hstatus : Measurable (fun x => fun i : Fin (p.m - 1) =>
      FollowerDownMeasurability.followerStatusCode ((cell x).states i).status) := by
    apply measurable_pi_iff.mpr
    intro i
    have ht := measurable_preparedStatusTag.comp
      ((ReferenceActivePhysicalStepMeasurability.measurable_preparedFollowerCode i).comp hinput)
    have htag (x) : preparedStatusTag
        (ReferenceActivePhysicalStepMeasurability.preparedFollowerCode
          (inspectedInput rate rewards C_star C_h q t s hs control0 k x.val) i) =
        some (FollowerDownMeasurability.followerStatusCode ((cell x).states i).status) := by
      apply preparedStatusTag_ordinary _ i _ ((cell x).memories i)
      rw [prepare_configuration_eq_of_roundInputs rate
        (inspectedInput rate rewards C_star C_h q t s hs control0 k x.val)
        (countRecord rate rewards C_star C_h q t s hs k x.val).input rfl rfl rfl
        (inspectedInput_current rate rewards C_star C_h q t s hs control0 k x.val) i,
        ← hrecord x]
      have hp : (record x).output.preparation = ReferenceActivePhysicalStep.prepare (record x).input := by
        rw [(record x).output_eq]
        rfl
      rw [← hp]
      exact (cell x).ordinary i
    apply measurable_to_countable'
    intro v
    convert (measurableSet_singleton (some v)).preimage ht using 1
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Function.comp_def]
    rw [htag]
    simp only [Option.some.injEq]
  have hslice : Measurable (fun x => ((record x).input.row.2 (record x).input.time).1) := by
    have heq : (fun x => ((record x).input.row.2 (record x).input.time).1) =
        fun x => (ReferenceSourceOwnHistoryContainment.selectedControlPrefix t.val
          (Nat.le_of_lt t.isLt) x.val.val ⟨s + k.val, by omega⟩).1 := by
      funext x
      rw [hrecord]
      have hf := countRecord_fields rate rewards C_star C_h q t s hs k x.val
      have htime : (countRecord rate rewards C_star C_h q t s hs k x.val).input.time =
          (⟨s + k.val, by omega⟩ : Fin p.T) := Fin.ext hf.2.2.2
      simp only [ReferenceActivePhysicalStep.RoundInput.row, hf.1, hf.2.1, htime,
        ReferenceSourceOwnHistoryContainment.selectedControlPrefix]
      rfl
    rw [heq]
    exact measurable_fst.comp
      ((ReferenceFirstLiveInspectedNumericalPast.measurable_localSelectedControl
        rate rewards C_star C_h q t s hs k).comp hproj)
  have hreward : Measurable (fun x => fun a : Fin p.K =>
      (((record x).input.rewards (record x).input.time a).val : ℝ) / (D p : ℝ)) := by
    have heq : (fun x => fun a : Fin p.K =>
        (((record x).input.rewards (record x).input.time a).val : ℝ) / (D p : ℝ)) =
        fun _ => fun a => ((rewards ⟨s + k.val, by omega⟩ a).val : ℝ) / (D p : ℝ) := by
      funext x
      rw [hrecord]
      have hf := countRecord_fields rate rewards C_star C_h q t s hs k x.val
      have htime : (countRecord rate rewards C_star C_h q t s hs k x.val).input.time =
          (⟨s + k.val, by omega⟩ : Fin p.T) := Fin.ext hf.2.2.2
      rw [hf.2.2.1, htime]
    rw [heq]
    exact measurable_const' (fun _ _ => rfl)
  exact measurable_cell_readout record cell hsel hstatus hslice hreward
    (fun x => sourceCell_anchor_one rate rewards C_star C_h q t s hs x.val ⟨k.val, x.property⟩)
    (fun x => sourceCell_sourceWeights_range rate rewards C_star C_h q t s hs x.val ⟨k.val, x.property⟩)

/-- Every strict-past tagged numerical coordinate is measurable in the exact
inspected pullback field. No event, matching trace, or measurability premise
is added. The complete reward and recording-rate vectors are retained. -/
theorem measurable_numericalCountPastReadoutAt
    (control0 : ContinuousLearningRows.TimeControl p) (k : Fin n) :
    Measurable[KZ] (fun z : Z =>
      ReferenceFirstLiveNumericalPrefixBorel.numericalCountPastReadout
        rate rewards C_star C_h q t s hs control0 z k) := by
  classical
  let present : Set Z := {z | k.val < (countWindow rate rewards C_star C_h q t s hs z).length}
  have hpresent : MeasurableSet[KZ] present :=
    measurableSet_lt measurable_const
      (measurable_countWindow_length rate rewards C_star C_h q t s hs control0)
  have hfield := measurable_indexedCellReadout rate rewards C_star C_h q t s hs control0 k
  have hleft : Measurable[(KZ).comap Subtype.val] (fun x : present =>
      (Sum.inr (indexedCellReadout rate rewards C_star C_h q t s hs k x) :
        Unit ⊕ ReferenceFirstLiveNumericalPrefixBorel.NumericalCellReadout p)) :=
    measurable_inr.comp hfield
  have hright : Measurable[(KZ).comap Subtype.val] (fun _ : ↥(presentᶜ) =>
      (Sum.inl () : Unit ⊕ ReferenceFirstLiveNumericalPrefixBorel.NumericalCellReadout p)) :=
    measurable_const
  have htagged : Measurable[KZ] (fun z : Z =>
      if h : z ∈ present then
        Sum.inr (indexedCellReadout rate rewards C_star C_h q t s hs k ⟨z, h⟩)
      else (Sum.inl () : Unit ⊕ ReferenceFirstLiveNumericalPrefixBorel.NumericalCellReadout p)) :=
    hleft.dite hright hpresent
  convert htagged using 1
  funext z
  have hlength := actualLiveSourceCells_length rate z.val rewards C_star C_h
    (sourceCrossing rate rewards C_star C_h q t s hs z) n
    (sourceCountSpan rate rewards C_star C_h q t s hs z)
  by_cases hk : k.val < (countWindow rate rewards C_star C_h q t s hs z).length
  · have hc : k.val < (actualLiveSourceCells rate z.val rewards C_star C_h
        (sourceCrossing rate rewards C_star C_h q t s hs z) n
        (sourceCountSpan rate rewards C_star C_h q t s hs z)).length := by
      rw [hlength]; exact hk
    simp only [ReferenceFirstLiveNumericalPrefixBorel.numericalCountPastReadout,
      List.getElem?_eq_getElem hc]
    rw [actualLiveSourceCells_get rate z.val rewards C_star C_h
      (sourceCrossing rate rewards C_star C_h q t s hs z) n
      (sourceCountSpan rate rewards C_star C_h q t s hs z) ⟨k.val, hk⟩]
    simp only [present, Set.mem_ofPred_eq, dite_eq_left hk, indexedCellReadout]
  · have hc : (actualLiveSourceCells rate z.val rewards C_star C_h
        (sourceCrossing rate rewards C_star C_h q t s hs z) n
        (sourceCountSpan rate rewards C_star C_h q t s hs z)).length ≤ k.val := by
      rw [hlength]; exact Nat.le_of_not_gt hk
    simp only [ReferenceFirstLiveNumericalPrefixBorel.numericalCountPastReadout,
      List.getElem?_eq_none hc, present, Set.mem_ofPred_eq, dite_eq_right hk]

/-- The same whole finite tagged tuple is measurable in the inspected field.
The coordinate proof is assembled by `measurable_pi_iff`, also when `n = 0`.
The control at `t.val` is outside the coordinate domain. -/
theorem measurable_numericalCountPastReadout
    (control0 : ContinuousLearningRows.TimeControl p) :
    Measurable[KZ] (ReferenceFirstLiveNumericalPrefixBorel.numericalCountPastReadout
      rate rewards C_star C_h q t s hs control0) :=
  measurable_pi_of_coordinates (mX := KZ) _
    (measurable_numericalCountPastReadoutAt rate rewards C_star C_h q t s hs control0)

end Bandits.Support.ReferenceFirstLiveInspectedNumericalCells

end
