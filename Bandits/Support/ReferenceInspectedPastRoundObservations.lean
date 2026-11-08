/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceSourceOwnHistoryContainment
public import Bandits.Support.ReferenceFirstLiveSourceReleaseSupport

/-!
# Actual strict-past whole-round observations in the inspected history field

Sources: `sources/zip4/manuscript/05_binary_transport.tex:45-55,74-124,180-188,297-308`,
`sources/zip4/manuscript/06_interruptions.tex:391-426`,
`sources/zip4/manuscript/07_public_setup.tex:127-164`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-64`.

This internal construction retains the actual optional postlaunch records,
including full continuous buffers, raw diagnostics and exceptional paths.
The factor inputs below are analytical inputs on the present-record fibre,
never a second execution or a seed on the absent branch. No identification
with a manuscript or local-policy filtration, stopping law, numerical-cell
reconstruction, or manuscript closure is asserted.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open scoped Classical

namespace Bandits.Support.ReferenceInspectedPastRoundObservations


variable {p : ConstructorDimensions.Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}

local instance : MeasurableSpace (CoordinatorPhaseClock.StartRoundResult p) := ⊤

/-- Literal whole-round codes at every strict-past calendar offset. Absence
before launch or at a terminal launch is retained as `none`. -/
def pastRoundObservations (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (n : ℕ) (hn : n ≤ p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    Fin n → Option (ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate)) :=
  fun j => (ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h (Fin.castLE hn j) z).map
    ReferenceActiveHorizonMeasurability.roundRecordCode

/-- Exact indexed reconstruction on a present actual record. -/
theorem pastRoundObservations_some (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (n : ℕ) (hn : n ≤ p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (j : Fin n)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h (Fin.castLE hn j) z = some r) :
    pastRoundObservations rate rewards C_star C_h n hn z j = some (ReferenceActiveHorizonMeasurability.roundRecordCode r) := by
  simp only [pastRoundObservations, hr, Option.map_some]

/-- No input is reconstructed when the actual lookup is absent. -/
theorem pastRoundObservations_none_iff (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (n : ℕ) (hn : n ≤ p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (j : Fin n) :
    pastRoundObservations rate rewards C_star C_h n hn z j = none ↔
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h (Fin.castLE hn j) z = none := by
  simp only [pastRoundObservations, Option.map_eq_none_iff]

private theorem measurable_option_get {X Y : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] (f : X → Option Y) (hf : Measurable f)
    (h : ∀ x, (f x).isSome = true) : Measurable (fun x => (f x).get (h x)) := by
  intro s hs
  have hm := (hs.inl_image (β := PUnit)).preimage (measurable_comap_iff.mp hf)
  convert hm using 1
  ext x
  cases hx : f x with
  | none => have hh := h x; simp only [hx, Option.isSome_none, Bool.false_eq_true] at hh
  | some y => simp [hx, Equiv.optionEquivSumPUnit]

private theorem measurable_option_isSome {Y : Type*} [MeasurableSpace Y] :
    Measurable (Option.isSome : Option Y → Bool) := by
  have h : Measurable (Sum.elim (fun _ : Y => true) (fun _ : PUnit => false)) :=
    measurable_const.sumElim measurable_const
  convert h.comp (comap_measurable (Equiv.optionEquivSumPUnit Y)) using 1
  funext x
  cases x <;> rfl

/-- Measurability of the complete selected forward row follows directly
from its public defining comap, with no private imported helper. -/
theorem selectedForwardRow_measurable_in_inspectedHistorySpace
    (rate : ReferenceActivePhysicalStep.RateInput p) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (n : ℕ) (hn : n ≤ p.T) :
    Measurable[ReferenceSourceOwnHistoryContainment.inspectedHistorySpace rate rewards C_star C_h n hn]
      (ReferenceSourceOwnHistoryContainment.selectedForwardRow (p := p)) := by
  apply (comap_measurable ReferenceSourceOwnHistoryContainment.selectedForwardRow).mono _ le_rfl
  dsimp [ReferenceSourceOwnHistoryContainment.inspectedHistorySpace]
  exact le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left
    (le_sup_of_le_left (le_sup_of_le_right le_rfl))))

/-- All original private coordinates, including the coordinator index,
are generators of the exact inspected field. -/
theorem privateCoordinates_measurable_in_inspectedHistorySpace
    (rate : ReferenceActivePhysicalStep.RateInput p) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (n : ℕ) (hn : n ≤ p.T) :
    Measurable[ReferenceSourceOwnHistoryContainment.inspectedHistorySpace rate rewards C_star C_h n hn]
      (Prod.snd : BootstrapPrivateRoundStreams.SourceInput p → _) := by
  apply (comap_measurable Prod.snd).mono _ le_rfl
  dsimp [ReferenceSourceOwnHistoryContainment.inspectedHistorySpace]
  exact le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left
    (le_sup_of_le_right le_rfl)))

/-- The strict selected-control vector is a literal generator, retaining
its entire continuous and affine control products. -/
theorem selectedControlPrefix_measurable_in_inspectedHistorySpace
    (rate : ReferenceActivePhysicalStep.RateInput p) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (n : ℕ) (hn : n ≤ p.T) :
    Measurable[ReferenceSourceOwnHistoryContainment.inspectedHistorySpace rate rewards C_star C_h n hn]
      (ReferenceSourceOwnHistoryContainment.selectedControlPrefix (p := p) n hn) := by
  apply (comap_measurable (ReferenceSourceOwnHistoryContainment.selectedControlPrefix n hn)).mono _ le_rfl
  dsimp [ReferenceSourceOwnHistoryContainment.inspectedHistorySpace]
  exact le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_right le_rfl))

private theorem actualRecord_input_fields (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r) :
    r.input.rows = z.1.2 ∧
      r.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p z ∧
      r.input.time = t ∧ r.input.rewards = rewards := by
  by_cases hz : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy rate rewards C_star C_h t.val z
  · have hl := ReferenceLocalReleaseGateChronology.sourceSeed_launch rate z rewards C_star C_h hz.1
    have hrec := ReferenceSourcePrefixHistoryFiltration.actualRecord_on_launch rate rewards C_star C_h t z _ hl hz.2
    have heq := Option.some.inj (hr.symm.trans hrec)
    subst r
    refine ⟨rfl, rfl, ?_, rfl⟩
    apply Fin.ext
    dsimp only [ReferenceAssignmentPayloadChronology.actualRunRecordAt,
      ReferenceActivePhysicalHorizon.roundInputAt]
    have hs := hz.2
    omega
  · rw [ReferenceSourcePrefixHistoryFiltration.actualRecord_eq_none_of_not_launchBy rate rewards C_star C_h t z hz] at hr
    cases hr

private abbrev DispatchTailArgs :=
  Unit ⊕ (Unit ⊕ (ReferenceActiveDispatchTemporal.LiveArgs p rate ⊕
    ReferenceActiveDispatchTemporal.CollectionArgs p rate))

private def selectionCodeFromDispatchData
    (data : Fin p.K × (Option (ReferenceDownReception.ChoiceTimeView p rate.eta) ×
      DispatchTailArgs (p := p) (rate := rate))) :
    Option (ReferenceLiveDispatchOutputMeasurability.SelectionData p rate) :=
  match data.2.1, data.2.2 with
  | some view, Sum.inr (Sum.inr (Sum.inl args)) => some (view, (args.2.2.2, data.1))
  | some view, Sum.inr (Sum.inr (Sum.inr args)) => some (view, (args.2.2.1, data.1))
  | _, _ => none

private theorem selectionCode_eq_of_cutData
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (cut : ReferenceActivePhysicalStep.DispatchCut x) :
    cut.selection.map (ReferenceLiveDispatchOutputMeasurability.encodeSelection) =
      selectionCodeFromDispatchData (ReferenceActiveDispatchTemporal.cutData cut) := by
  classical
  cases cut with
  | first outcome =>
      cases outcome
      all_goals simp_all [selectionCodeFromDispatchData, ReferenceActiveDispatchTemporal.cutData,
          ReferenceActiveDispatchTemporal.tailArgs, ReferenceActivePhysicalStep.DispatchCut.arm,
          ReferenceActivePhysicalStep.DispatchCut.downView,
          ReferenceActivePhysicalStep.DispatchCut.selection, ReferenceActivePhysicalStep.selectionAt,
          ReferenceLiveDispatchOutputMeasurability.encodeSelection]
      all_goals
        split_ifs <;> simp_all
  | live registers owned base outcome =>
      cases outcome
      all_goals simp_all [selectionCodeFromDispatchData, ReferenceActiveDispatchTemporal.cutData,
          ReferenceActiveDispatchTemporal.tailArgs, ReferenceActivePhysicalStep.DispatchCut.arm,
          ReferenceActivePhysicalStep.DispatchCut.downView,
          ReferenceActivePhysicalStep.DispatchCut.selection, ReferenceActivePhysicalStep.selectionAt,
          ReferenceLiveDispatchOutputMeasurability.encodeSelection]
  | collection payload ledger clock cutoff outcome =>
      cases outcome
      all_goals simp_all [selectionCodeFromDispatchData, ReferenceActiveDispatchTemporal.cutData,
          ReferenceActiveDispatchTemporal.tailArgs, ReferenceActivePhysicalStep.DispatchCut.arm,
          ReferenceActivePhysicalStep.DispatchCut.downView,
          ReferenceActivePhysicalStep.DispatchCut.selection, ReferenceActivePhysicalStep.selectionAt,
          ReferenceLiveDispatchOutputMeasurability.encodeSelection]
      all_goals
        split_ifs <;> simp_all
  | invalidCollectionCutoff =>
      simp [selectionCodeFromDispatchData, ReferenceActiveDispatchTemporal.cutData,
        ReferenceActiveDispatchTemporal.tailArgs, ReferenceActivePhysicalStep.DispatchCut.arm,
        ReferenceActivePhysicalStep.DispatchCut.downView, ReferenceActivePhysicalStep.DispatchCut.selection]
  | dagger =>
      simp [selectionCodeFromDispatchData, ReferenceActiveDispatchTemporal.cutData,
        ReferenceActiveDispatchTemporal.tailArgs, ReferenceActivePhysicalStep.DispatchCut.arm,
        ReferenceActivePhysicalStep.DispatchCut.downView, ReferenceActivePhysicalStep.DispatchCut.selection]

private theorem selectionCode_eq_of_dispatchData
    (left right : ReferenceActivePhysicalStep.RoundInput p rate)
    (hdata : ReferenceActiveDispatchTemporal.dispatchData left =
      ReferenceActiveDispatchTemporal.dispatchData right) :
    (ReferenceActivePhysicalStep.dispatch left).selection.map
        ReferenceLiveDispatchOutputMeasurability.encodeSelection =
      (ReferenceActivePhysicalStep.dispatch right).selection.map
        ReferenceLiveDispatchOutputMeasurability.encodeSelection := by
  have hleft := selectionCode_eq_of_cutData (ReferenceActivePhysicalStep.dispatch left)
  have hright := selectionCode_eq_of_cutData (ReferenceActivePhysicalStep.dispatch right)
  rw [hleft, hright]
  exact congrArg selectionCodeFromDispatchData hdata

private theorem firstOutcome_is_chosen (input : CoordinatorRoundDispatch.FirstInput p) :
    ∃ selected,
      CoordinatorRoundDispatch.dispatchFirst input =
        .chosen (CoordinatorAssignmentRegisterInstall.installFirst
          (CoordinatorRoundDispatch.firstLaunchInput input)) selected := by
  classical
  unfold CoordinatorRoundDispatch.dispatchFirst
  extract_lets launch installed started payload weights cutoff hpayload hstarted hcutoff
    hweights hchoice hboundary hnonempty
  split
  · exact False.elim (hnonempty ‹CoordinatorLocalArmChoice.coordinatorArmChoice
      payload started.pending cutoff installed.registers.time weights input.row = none›)
  · rename_i arm hselected
    exact ⟨{
      arm := arm
      choiceInputsValid := hchoice
      recorderBoundaryValid := hboundary
      armChoice_eq := hselected }, rfl⟩

private def firstTailArgs
    (launch : FirstAssignmentLaunch.Input p rate.eta) :
    ReferenceActiveDispatchTemporal.LiveArgs p rate :=
  ⟨(CoordinatorAssignmentRegisterInstall.installFirst launch).registers,
    (CoordinatorAssignmentRegisterInstall.installFirst launch).ownedRegisters,
    ((CoordinatorAssignmentRegisterInstall.installFirst launch).followerBaseScore,
      (CoordinatorAssignmentRegisterInstall.installFirst launch).startRoundResult)⟩

private theorem first_dispatch_tailArgs
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (hfirst : x.state.coordinator = .first) :
    ReferenceActiveDispatchTemporal.tailArgs (ReferenceActivePhysicalStep.dispatch x) =
      .inr (.inr (.inl (firstTailArgs
        (CoordinatorRoundDispatch.firstLaunchInput
          (ReferenceActivePhysicalStep.firstInput x))))) := by
  rw [ReferenceActivePhysicalStep.dispatch_first x hfirst]
  obtain ⟨selection, hchosen⟩ := firstOutcome_is_chosen (ReferenceActivePhysicalStep.firstInput x)
  rw [hchosen]
  have htime :
      (CoordinatorAssignmentRegisterInstall.installFirst
        (CoordinatorRoundDispatch.firstLaunchInput
          (ReferenceActivePhysicalStep.firstInput x))).registers.time = x.time := rfl
  simp only [ReferenceActiveDispatchTemporal.tailArgs,
    ReferenceActivePhysicalStep.DispatchCut.selection,
    ReferenceActivePhysicalStep.selectionAt, htime, dite_true, Option.some_ne_none]
  rfl

private theorem dispatchData_eq_of_current
    (state : ReferenceActivePhysicalHorizon.State p rate)
    (rows otherRows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (time : Fin p.T) (active : ∀ i, (state.activations i).val ≤ time.val + 1)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (hcurrent : (rows selected).2 time = (otherRows selected).2 time) :
    ReferenceActiveDispatchTemporal.dispatchData
        (⟨state, rows, selected, time, active, rewards⟩ : ReferenceActivePhysicalStep.RoundInput p rate) =
      ReferenceActiveDispatchTemporal.dispatchData
        (⟨state, otherRows, selected, time, active, rewards⟩ : ReferenceActivePhysicalStep.RoundInput p rate) := by
  let x : ReferenceActivePhysicalStep.RoundInput p rate :=
    ⟨state, rows, selected, time, active, rewards⟩
  let y : ReferenceActivePhysicalStep.RoundInput p rate :=
    ⟨state, otherRows, selected, time, active, rewards⟩
  change ReferenceActiveDispatchTemporal.cutData (ReferenceActivePhysicalStep.dispatch x) =
    ReferenceActiveDispatchTemporal.cutData (ReferenceActivePhysicalStep.dispatch y)
  cases hphase : state.coordinator with
  | first =>
      have hpair := ReferenceActiveTemporalCausality.first_dispatch_projections_eq_of_current
        state rows otherRows selected active rewards rewards hphase hcurrent
      have hlaunch := ReferenceActiveTemporalAssembly.firstLaunchInput_eq_of_current
        state rows otherRows selected time active rewards rewards hcurrent
      have htail : ReferenceActiveDispatchTemporal.tailArgs
          (ReferenceActivePhysicalStep.dispatch x) =
        ReferenceActiveDispatchTemporal.tailArgs
          (ReferenceActivePhysicalStep.dispatch y) := by
        rw [first_dispatch_tailArgs x hphase, first_dispatch_tailArgs y hphase]
        exact congrArg (fun args => Sum.inr (Sum.inr (Sum.inl args)))
          (congrArg firstTailArgs hlaunch)
      exact congrArg₂ (fun head tail => (head.1, head.2, tail)) hpair htail
  | live registers owned base =>
      exact ReferenceActiveDispatchTemporal.live_dispatch_data_eq_of_current
        state rows otherRows selected time active rewards rewards registers owned base
        hphase hcurrent
  | collection payload ledger proposal =>
      exact ReferenceActiveDispatchTemporal.collection_dispatch_data_eq_of_current
        state rows otherRows selected time active rewards rewards payload ledger proposal
        hphase hcurrent
  | dagger =>
      rw [ReferenceActivePhysicalStep.dispatch_dagger x hphase,
        ReferenceActivePhysicalStep.dispatch_dagger y hphase]
      rfl


private theorem prepareOutput_tail_eq_of_current
    (i : Fin (p.m - 1)) (activation : ReferencePrelaunchFollower.Activation p)
    (incoming : FollowerPrepareJointMeasurability.IncomingConfiguration p rate)
    (row row' : CompletePublicTable.CompleteRow p)
    (time : FollowerPrepareJointMeasurability.ActiveCalendarTime p activation)
    (hc : row.2 time.val = row'.2 time.val) :
    (FollowerPrepareJointMeasurability.prepareOutputOnInput rate i activation
      (FollowerPrepareJointMeasurability.assemblePrepareInput incoming row time)).2 =
    (FollowerPrepareJointMeasurability.prepareOutputOnInput rate i activation
      (FollowerPrepareJointMeasurability.assemblePrepareInput incoming row' time)).2 := by
  cases incoming with
  | none => rfl
  | some data =>
    rcases data with ⟨⟨index, values⟩, memory⟩
    have hp := ReferenceActiveTemporalCausality.prepare_projections_eq_of_current
      i activation time.property
      (FollowerLifecycleMeasurability.localConfigurationOfCode rate
        (some (index.1, memory))
        (FollowerDownJointMeasurability.bufferFromSkeletonAndScalars index.2.2 values)) hc
    have hcode := congrArg (fun pair =>
      FollowerLifecycleMeasurability.PreparedRoundCode.mk pair.1
        (FollowerLifecycleMeasurability.localConfigurationCode pair.2)) hp
    change FollowerLifecycleMeasurability.prepareRoundCodeAt rate i activation
        (some (index.1, memory)) index.2.2 row time values =
      FollowerLifecycleMeasurability.prepareRoundCodeAt rate i activation
        (some (index.1, memory)) index.2.2 row' time values at hcode
    simp only [FollowerPrepareJointMeasurability.prepareOutputOnInput,
      FollowerPrepareJointMeasurability.assemblePrepareInput,
      FollowerPrepareJointMeasurability.prepareRoundCodeOnInput,
      FollowerPrepareJointMeasurability.prepareOutputConfiguration, hcode]

private theorem loggingObservable_eq_of_current
    (i : Fin (p.m - 1)) (activation : ReferencePrelaunchFollower.Activation p)
    (carry : FollowerObservationStageMeasurabilityRepair.CarriedState p rate)
    (row row' : CompletePublicTable.CompleteRow p)
    (time : FollowerPrepareJointMeasurability.ActiveCalendarTime p activation)
    (feedback : Fin (D p + 1)) (arm : Fin p.K)
    (hu : FollowerObservationStageMeasurabilityRepair.assembleObservationInput
      carry row time feedback arm ∈
        ReferenceFollowerLoggingMeasurability.unoccupiedLoggingInputs rate activation)
    (hu' : FollowerObservationStageMeasurabilityRepair.assembleObservationInput
      carry row' time feedback arm ∈
        ReferenceFollowerLoggingMeasurability.unoccupiedLoggingInputs rate activation)
    (hc : row.2 time.val = row'.2 time.val) :
    ReferenceFollowerLoggingMeasurability.checkedLoggingObservable rate i activation
      ⟨FollowerObservationStageMeasurabilityRepair.assembleObservationInput
        carry row time feedback arm, hu⟩ =
    ReferenceFollowerLoggingMeasurability.checkedLoggingObservable rate i activation
      ⟨FollowerObservationStageMeasurabilityRepair.assembleObservationInput
        carry row' time feedback arm, hu'⟩ := by
  classical
  let factor (current : ContinuousLearningRows.TimeControl p) :
      ReferenceFollowerLoggingMeasurability.LoggingObservable p rate :=
    if ActiveFollowerLifecycle.localBufferValid
        (FollowerObservationStageMeasurabilityRepair.reconstructCarriedState carry.1 carry.2) then
      if (decide (PublicDiscreteDraws.slotDraw current.1 = PublicDiscreteDraws.dataSlot) &&
          decide (PublicDiscreteDraws.recorderSourceDraw p.two_le_m p.m_lt_K current.1 =
            PublicDiscreteDraws.followerPlayer p.two_le_m i) &&
          decide (∀ j : Fin p.m, j ≠ PublicDiscreteDraws.followerPlayer p.two_le_m i →
            PublicDiscreteDraws.pilotDraw (K_pos p) j current.1 ≠ arm)) = true then
        if ∀ old ∈ (FollowerObservationStageMeasurabilityRepair.representativeState rate carry.1).buffer,
            (old.calendarRound, old.pilot) ≠ (time.val.val + 1, arm) then
          .inr ⟨(carry.1.1, ⟨carry.1.2.1 + 1,
            Fin.lastCases (time.val.val + 1, arm) carry.1.2.2⟩),
            Fin.lastCases ((FollowerDownMeasurability.feedbackAtGrid p feedback).val,
              current.1 ContinuousControlSlice.Label.thin) carry.2⟩
        else .inl .invalidOutputBuffer
      else .inr carry
    else .inl .invalidInputBuffer
  have hf := congrArg factor hc
  dsimp only [factor] at hf
  convert hf using 1 <;>
    simp only [ReferenceFollowerLoggingMeasurability.checkedLoggingObservable,
      FollowerObservationStageMeasurabilityRepair.assembleObservationInput,
      FollowerObservationStageMeasurabilityRepair.observationInputCarriedState,
      FollowerObservationStageMeasurabilityRepair.loggingInputOfFiber,
      FollowerObservationStageMeasurabilityRepair.fiberValues,
      FollowerObservationStageMeasurabilityRepair.fiberRow,
      FollowerObservationStageMeasurabilityRepair.fiberTime,
      FollowerObservationStageMeasurabilityRepair.fiberFeedbackIndex,
      FollowerObservationStageMeasurabilityRepair.fiberPlayedArm,
      FollowerObservationStageMeasurabilityRepair.observationInputRow,
      FollowerObservationStageMeasurabilityRepair.observationInputTime,
      FollowerObservationStageMeasurabilityRepair.observationInputFeedbackIndex,
      FollowerObservationStageMeasurabilityRepair.observationInputPlayedArm,
      FollowerLoggingDownMeasurability.loggingGateBit,
      FollowerLoggingDownMeasurability.currentKeyFresh,
      FollowerLoggingDownMeasurability.inputSliceAt,
      FollowerLoggingDownMeasurability.inputRow,
      FollowerLoggingDownMeasurability.inputTime,
      FollowerLoggingDownMeasurability.inputPlayedArm,
      ContinuousLearningRows.sliceAt, CompletePublicTable.completeRowLearning]
  all_goals
    apply dite_congr rfl
    · intro hvalid
      apply dite_congr rfl
      · intro hgate
        apply dite_congr rfl <;> intro hfresh <;> rfl
      · intro hgate
        rfl
    · intro hvalid
      rfl

private theorem occupiedCode_eq_of_current
    (i : Fin (p.m - 1)) (activation : ReferencePrelaunchFollower.Activation p)
    (carry : FollowerObservationStageMeasurabilityRepair.CarriedState p rate)
    (row row' : CompletePublicTable.CompleteRow p)
    (time : FollowerPrepareJointMeasurability.ActiveCalendarTime p activation)
    (feedback : Fin (D p + 1)) (arm : Fin p.K)
    (hc : row.2 time.val = row'.2 time.val) :
    ReferenceFollowerTailComposition.occupiedCode rate i activation
      (FollowerObservationStageMeasurabilityRepair.assembleObservationInput carry row time feedback arm) =
    ReferenceFollowerTailComposition.occupiedCode rate i activation
      (FollowerObservationStageMeasurabilityRepair.assembleObservationInput carry row' time feedback arm) := by
  unfold ReferenceFollowerTailComposition.occupiedCode FollowerServiceMeasurability.occupiedRoundCodeAtJoint
  rw [FollowerServiceMeasurability.checkedServiceCodeAtJoint_eq_readFactor,
    FollowerServiceMeasurability.checkedServiceCodeAtJoint_eq_readFactor]
  congr 2
  dsimp only [FollowerObservationStageMeasurabilityRepair.assembleObservationInput]
  unfold FollowerServiceMeasurability.serviceReadForState
  cases hlast : (FollowerObservationStageMeasurabilityRepair.representativeState rate carry.1).lastDown with
  | none => rfl
  | some M =>
    unfold FollowerServiceMeasurability.recorderReadForDownAt
      FollowerServiceMeasurability.recorderGateBit
      ActiveFollowerQueueOperation.recorderGate
    dsimp only [FollowerDownJointMeasurability.jointRow,
      FollowerDownJointMeasurability.jointTime, FollowerDownJointMeasurability.jointRowTime,
      FollowerObservationStageMeasurabilityRepair.serviceInputOfFiber,
      FollowerObservationStageMeasurabilityRepair.fiberRow,
      FollowerObservationStageMeasurabilityRepair.fiberTime]
    congr 1
    apply decide_eq_decide.mpr
    apply Iff.of_eq
    exact congrArg (fun current : ContinuousLearningRows.TimeControl p =>
      PublicDiscreteDraws.slotDraw current.1 = PublicDiscreteDraws.dataSlot ∧
      PublicDiscreteDraws.recorderSourceDraw p.two_le_m p.m_lt_K current.1 =
        PublicDiscreteDraws.followerPlayer p.two_le_m i ∧
      CanonicalRecordingSlice.recordingMask (K_pos p)
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)
        (PrelaunchBufferRecovery.downArm rate.eta M) current.1 ∧
      (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.thin current.1).val ≤
        ActiveFollowerQueueOperation.thinningProbability rate.eta M) hc

private theorem recordObservable_eq_of_temporal_reads
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (i : Fin (p.m - 1)) (activation : ReferencePrelaunchFollower.Activation p)
    (carry : FollowerObservationStageMeasurabilityRepair.CarriedState p rate)
    (row row' : CompletePublicTable.CompleteRow p)
    (time : FollowerPrepareJointMeasurability.ActiveCalendarTime p activation)
    (feedback : Fin (D p + 1)) (arm : Fin p.K)
    (hc : row.2 time.val = row'.2 time.val)
    (hpast : ∀ v : Fin p.T, v.val < time.val.val →
      (row.2 v).1 ContinuousControlSlice.Label.prop =
        (row'.2 v).1 ContinuousControlSlice.Label.prop) :
    ReferenceFollowerTailComposition.recordObservable rate i activation
      (view, FollowerObservationStageMeasurabilityRepair.assembleObservationInput
        carry row time feedback arm) =
    ReferenceFollowerTailComposition.recordObservable rate i activation
      (view, FollowerObservationStageMeasurabilityRepair.assembleObservationInput
        carry row' time feedback arm) := by
  unfold ReferenceFollowerTailComposition.recordObservable
  have hu : (FollowerObservationStageMeasurabilityRepair.assembleObservationInput
      carry row time feedback arm ∈
        ReferenceFollowerLoggingMeasurability.unoccupiedLoggingInputs rate activation) ↔
      (FollowerObservationStageMeasurabilityRepair.assembleObservationInput
      carry row' time feedback arm ∈
        ReferenceFollowerLoggingMeasurability.unoccupiedLoggingInputs rate activation) := Iff.rfl
  by_cases h : FollowerObservationStageMeasurabilityRepair.assembleObservationInput
      carry row time feedback arm ∈
        ReferenceFollowerLoggingMeasurability.unoccupiedLoggingInputs rate activation
  · rw [dite_eq_left h, dite_eq_left (hu.mp h)]
    unfold ReferenceFollowerTailComposition.unoccupiedRecord
    rw [loggingObservable_eq_of_current i activation carry row row' time feedback arm h (hu.mp h) hc]
    cases ReferenceFollowerLoggingMeasurability.checkedLoggingObservable rate i activation
      ⟨FollowerObservationStageMeasurabilityRepair.assembleObservationInput
        carry row' time feedback arm, hu.mp h⟩ with
    | inl reason => rfl
    | inr logged =>
      dsimp only
      unfold ReferenceFollowerTailComposition.downCall
      dsimp only [FollowerObservationStageMeasurabilityRepair.observationInputRow_assemble,
        FollowerObservationStageMeasurabilityRepair.observationInputTime_assemble,
        FollowerObservationStageMeasurabilityRepair.observationInputFeedbackIndex_assemble]
      rw [ReferenceActiveTemporalCausality.referenceDownCut_eq_of_temporal_reads
        view i _ _ hc hpast]
  · rw [dite_eq_right h, dite_eq_right (fun h' => h (hu.mpr h'))]
    unfold ReferenceFollowerTailComposition.occupiedRecord
    rw [occupiedCode_eq_of_current i activation carry row row' time feedback arm hc]
    rfl

private theorem finishFollowerCode_eq_of_temporal_reads
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (i : Fin (p.m - 1)) (activation : ReferencePrelaunchFollower.Activation p)
    (incoming : FollowerPrepareJointMeasurability.IncomingConfiguration p rate)
    (row row' : CompletePublicTable.CompleteRow p)
    (time : FollowerPrepareJointMeasurability.ActiveCalendarTime p activation)
    (feedback : Fin (D p + 1)) (arm : Fin p.K)
    (hc : row.2 time.val = row'.2 time.val)
    (hpast : ∀ v : Fin p.T, v.val < time.val.val →
      (row.2 v).1 ContinuousControlSlice.Label.prop =
        (row'.2 v).1 ContinuousControlSlice.Label.prop) :
    ReferenceFollowerTailComposition.finishFollowerObservable rate i activation
      (view, ((row, time), (arm, incoming)), feedback) =
    ReferenceFollowerTailComposition.finishFollowerObservable rate i activation
      (view, ((row', time), (arm, incoming)), feedback) := by
  unfold ReferenceFollowerTailComposition.finishFollowerObservable
  cases incoming with
  | none => rfl
  | some data =>
    rcases data with ⟨carry, memory⟩
    change ReferenceFollowerTailComposition.ordinaryObservable rate i activation
      (view, FollowerObservationStageMeasurabilityRepair.assembleObservationInput
        carry row time feedback arm, memory) =
      ReferenceFollowerTailComposition.ordinaryObservable rate i activation
      (view, FollowerObservationStageMeasurabilityRepair.assembleObservationInput
        carry row' time feedback arm, memory)
    unfold ReferenceFollowerTailComposition.ordinaryObservable
    dsimp only
    rw [recordObservable_eq_of_temporal_reads view i activation carry row row' time feedback arm hc hpast]
    have hf (result : DeclaredFollowerLocalRound.RoundFailure ⊕
        FollowerObservationStageMeasurabilityRepair.CarriedState p rate) :
        ReferenceFollowerTailComposition.finishRecordResult rate i activation result
          (FollowerObservationStageMeasurabilityRepair.assembleObservationInput
            carry row time feedback arm, memory) =
        ReferenceFollowerTailComposition.finishRecordResult rate i activation result
          (FollowerObservationStageMeasurabilityRepair.assembleObservationInput
            carry row' time feedback arm, memory) := by
      unfold ReferenceFollowerTailComposition.finishRecordResult
      cases result with
      | inl reason => rfl
      | inr postRecord =>
        dsimp only [FollowerObservationStageMeasurabilityRepair.observationInputCarriedState_assemble,
          FollowerObservationStageMeasurabilityRepair.observationInputRow_assemble,
          FollowerObservationStageMeasurabilityRepair.observationInputTime_assemble,
          FollowerObservationStageMeasurabilityRepair.observationInputFeedbackIndex_assemble]
        rw [FollowerReleaseFinishJointMeasurability.releaseAndFinishResultCodeAtComponents_eq_of_currentTimeControl_eq
          rate i carry postRecord memory row row' time.val feedback hc]
    rw [hf]

/-- Full-code temporal congruence. Equality of the state, selected index,
time, whole reward table, current control and strict-past proposal reads is
explicit comparison data only. -/
theorem roundRecordCode_eq_of_temporal_reads
    (left right : ReferenceActivePhysicalStep.RoundInput p rate)
    (hstate : left.state = right.state) (hselected : left.selected = right.selected)
    (htime : left.time = right.time) (hrewards : left.rewards = right.rewards)
    (hcurrent : left.row.2 left.time = right.row.2 right.time)
    (hpast : ∀ v : Fin p.T, v.val < left.time.val →
      (left.row.2 v).1 ContinuousControlSlice.Label.prop =
        (right.row.2 v).1 ContinuousControlSlice.Label.prop) :
    ReferenceActiveHorizonMeasurability.roundRecordCode
        ⟨left, ReferenceActivePhysicalStep.step left, rfl⟩ =
      ReferenceActiveHorizonMeasurability.roundRecordCode
        ⟨right, ReferenceActivePhysicalStep.step right, rfl⟩ := by
  rcases left with ⟨leftState, leftRows, leftSelected, leftTime, leftActive, leftRewards⟩
  rcases right with ⟨rightState, rightRows, rightSelected, rightTime, rightActive, rightRewards⟩
  dsimp only at hstate hselected htime hrewards hcurrent hpast
  cases hstate
  cases hselected
  cases htime
  cases hrewards
  let x : ReferenceActivePhysicalStep.RoundInput p rate :=
    ⟨leftState, leftRows, leftSelected, leftTime, leftActive, leftRewards⟩
  let y : ReferenceActivePhysicalStep.RoundInput p rate :=
    ⟨leftState, rightRows, leftSelected, leftTime, leftActive, leftRewards⟩
  have hdata := dispatchData_eq_of_current (rate := rate)
    leftState leftRows rightRows leftSelected leftTime leftActive leftRewards hcurrent
  have hotherRows := ReferenceActivePhysicalHorizon.computedEvidence_rows
    leftState leftRows (fun _ => leftRows leftSelected) leftSelected leftTime leftActive leftRewards rfl
  have htemporal := ReferenceActiveTemporalAssembly.computedEvidence_eq_of_temporal_reads
    leftState (fun _ => leftRows leftSelected) rightRows leftSelected leftTime leftActive
    leftRewards leftRewards hcurrent hpast rfl
  have hevidence := hotherRows.trans htemporal
  have hactions : (ReferenceActivePhysicalStep.prepare x).arms.actions =
      (ReferenceActivePhysicalStep.prepare y).arms.actions := by
    have h := congrArg ReferenceActivePhysicalHorizon.RoundEvidence.actions hevidence
    simpa only [ReferenceActivePhysicalHorizon.computedEvidence,
      ReferenceActivePhysicalHorizon.RoundRecord.evidence,
      ReferenceActivePhysicalHorizon.RoundRecord.actions,
      ReferenceActivePhysicalStep.step] using h
  have hfeedback : (ReferenceActivePhysicalStep.prepare x).feedback.feedback =
      (ReferenceActivePhysicalStep.prepare y).feedback.feedback := by
    have h := congrArg ReferenceActivePhysicalHorizon.RoundEvidence.gridFeedback hevidence
    simpa only [ReferenceActivePhysicalHorizon.computedEvidence,
      ReferenceActivePhysicalHorizon.RoundRecord.evidence,
      ReferenceActivePhysicalHorizon.RoundRecord.gridFeedback,
      ReferenceActivePhysicalStep.step] using h
  have hcoordinator : (ReferenceActivePhysicalStep.prepare x).observeCoordinator =
      (ReferenceActivePhysicalStep.prepare y).observeCoordinator := by
    have h := congrArg ReferenceActivePhysicalHorizon.RoundEvidence.coordinator hevidence
    simpa only [ReferenceActivePhysicalHorizon.computedEvidence,
      ReferenceActivePhysicalHorizon.RoundRecord.evidence,
      ReferenceActivePhysicalHorizon.RoundRecord.coordinatorDiagnostics,
      ReferenceActivePhysicalStep.step] using h
  have hnext : (ReferenceActivePhysicalStep.step x).next =
      (ReferenceActivePhysicalStep.step y).next := by
    have h := congrArg ReferenceActivePhysicalHorizon.RoundEvidence.after hevidence
    simpa only [ReferenceActivePhysicalHorizon.computedEvidence,
      ReferenceActivePhysicalHorizon.RoundRecord.evidence] using h
  have hselection := selectionCode_eq_of_dispatchData x y hdata
  have hdispatchView : (ReferenceActivePhysicalStep.dispatch x).downView =
      (ReferenceActivePhysicalStep.dispatch y).downView := by
    have h := congrArg (fun data : _ => data.2.1) hdata
    simpa only [ReferenceActiveDispatchTemporal.dispatchData,
      ReferenceActiveDispatchTemporal.cutData] using h
  have hphysical :
      ReferenceFirstLiveCoordinatorStepMeasurability.physicalCode x =
        ReferenceFirstLiveCoordinatorStepMeasurability.physicalCode y := by
    unfold ReferenceFirstLiveCoordinatorStepMeasurability.physicalCode
    apply Prod.ext
    · exact hselection
    · apply Prod.ext
      · exact hdispatchView
      · apply Prod.ext
        · exact hactions
        · apply Prod.ext
          · exact hfeedback
          · exact congrArg
              ReferenceCollectionServiceTailMeasurability.encodeCollectionObservation hcoordinator
  have hfollowersCode : ∀ i,
      ReferenceActiveStepCompositionMeasurability.followerObservable x i =
        ReferenceActiveStepCompositionMeasurability.followerObservable y i := by
    intro i
    let activation := leftState.activations i
    let incoming := FollowerPrepareJointMeasurability.incomingOfLocalConfiguration rate
      (leftState.followers i)
    let time : FollowerPrepareJointMeasurability.ActiveCalendarTime p activation :=
      ⟨leftTime, leftActive i⟩
    let prepared (row : CompletePublicTable.CompleteRow p) :=
      FollowerPrepareJointMeasurability.prepareOutputOnInput rate i activation
        (FollowerPrepareJointMeasurability.assemblePrepareInput incoming row time)
    have hrepr (row : CompletePublicTable.CompleteRow p) :
        prepared row = ((row, time), (prepared row).2) := by
      dsimp only [prepared, FollowerPrepareJointMeasurability.prepareOutputOnInput]
      cases incoming <;> rfl
    have htail := prepareOutput_tail_eq_of_current i activation incoming
      (leftRows leftSelected) (rightRows leftSelected) time hcurrent
    unfold ReferenceActiveStepCompositionMeasurability.followerObservable
      ReferenceFollowerTailComposition.observeFollowerObservable
      ReferenceFollowerTailComposition.canonicalFollowerInput
    change ReferenceFollowerTailComposition.finishFollowerObservable rate i activation
      ((ReferenceActivePhysicalStep.dispatch x).downView,
        prepared (leftRows leftSelected),
        (ReferenceActivePhysicalStep.prepare x).feedback.feedback
          (PublicDiscreteDraws.followerPlayer p.two_le_m i)) =
      ReferenceFollowerTailComposition.finishFollowerObservable rate i activation
      ((ReferenceActivePhysicalStep.dispatch y).downView,
        prepared (rightRows leftSelected),
        (ReferenceActivePhysicalStep.prepare y).feedback.feedback
          (PublicDiscreteDraws.followerPlayer p.two_le_m i))
    rw [hrepr (leftRows leftSelected), hrepr (rightRows leftSelected),
      hdispatchView, hfeedback]
    calc
      _ = ReferenceFollowerTailComposition.finishFollowerObservable rate i activation
          ((ReferenceActivePhysicalStep.dispatch y).downView,
            ((rightRows leftSelected, time), (prepared (leftRows leftSelected)).2),
            (ReferenceActivePhysicalStep.prepare y).feedback.feedback
              (PublicDiscreteDraws.followerPlayer p.two_le_m i)) :=
        finishFollowerCode_eq_of_temporal_reads _ i activation _ _ _ time _ _ hcurrent hpast
      _ = _ := by rw [show (prepared (leftRows leftSelected)).2 =
          (prepared (rightRows leftSelected)).2 from htail]
  have hwhole :
      ReferenceActiveStepCompositionMeasurability.wholeStepCode x =
        ReferenceActiveStepCompositionMeasurability.wholeStepCode y := by
    unfold ReferenceActiveStepCompositionMeasurability.wholeStepCode
    apply Prod.ext
    · exact hphysical
    · apply Prod.ext
      · funext i
        exact hfollowersCode i
      · exact congrArg ReferenceActivePhysicalStepMeasurability.encodeState hnext
  simp only [ReferenceActiveHorizonMeasurability.roundRecordCode, x, y, hwhole]

/-- The original IDs are another defining comap of the exact inspected
field. No information about unselected rows is added here. -/
theorem ids_measurable_in_inspectedHistorySpace
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (n : ℕ) (hn : n ≤ p.T) :
    Measurable[ReferenceSourceOwnHistoryContainment.inspectedHistorySpace
      rate rewards C_star C_h n hn]
      (fun z : BootstrapPrivateRoundStreams.SourceInput p => z.1.1) := by
  apply (comap_measurable (fun z : BootstrapPrivateRoundStreams.SourceInput p => z.1.1)).mono _ le_rfl
  dsimp [ReferenceSourceOwnHistoryContainment.inspectedHistorySpace]
  exact le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left
    (le_sup_of_le_left (le_sup_of_le_left le_rfl))))

-- Fixed controls below are used only for a measurable analytical factor of
-- one existing round input. They never define an execution on an absent input.
private def fixedControl (p : ConstructorDimensions.Parameters) :
    ContinuousLearningRows.TimeControl p :=
  (fun _ => ⟨0, le_rfl, zero_lt_one⟩, fun _ => (fun _ => 0, 0))

private def factorRows (n : ℕ) (hn : n ≤ p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p) : CompletePublicTable.CompleteRows p :=
  fun _ => (ReferenceSourceOwnHistoryContainment.selectedForwardRow z,
    fun v : Fin p.T => if hv : v.val < n then
      ReferenceSourceOwnHistoryContainment.selectedControlPrefix n hn z ⟨v.val, hv⟩
    else fixedControl p)

private theorem measurable_factorRows
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (n : ℕ) (hn : n ≤ p.T) :
    Measurable[ReferenceSourceOwnHistoryContainment.inspectedHistorySpace
      rate rewards C_star C_h n hn] (factorRows n hn) := by
  let : MeasurableSpace (BootstrapPrivateRoundStreams.SourceInput p) :=
    ReferenceSourceOwnHistoryContainment.inspectedHistorySpace rate rewards C_star C_h n hn
  apply measurable_pi_iff.mpr
  intro q
  apply (selectedForwardRow_measurable_in_inspectedHistorySpace
    rate rewards C_star C_h n hn).prodMk
  apply measurable_pi_iff.mpr
  intro v
  by_cases hv : v.val < n
  · have h := (measurable_pi_apply (⟨v.val, hv⟩ : Fin n)).comp
      (selectedControlPrefix_measurable_in_inspectedHistorySpace
        rate rewards C_star C_h n hn)
    simpa only [factorRows, dite_eq_left hv, Function.comp_def] using h
  · simp only [dite_eq_right hv]
    exact measurable_const

private theorem factorRows_control (n : ℕ) (hn : n ≤ p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (v : Fin p.T) (hv : v.val < n)
    (q : Fin (M p)) :
    ((factorRows n hn z) q).2 v =
      (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)).2 v := by
  simp only [factorRows, dite_eq_left hv,
    ReferenceSourceOwnHistoryContainment.selectedControlPrefix]
  rfl

private abbrev Present (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T) :=
  {z : BootstrapPrivateRoundStreams.SourceInput p //
    (ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z).isSome = true}

private def presentRecord (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T) (x : Present rate rewards C_star C_h t) :=
  (ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t x.val).get x.property

private theorem presentRecord_lookup (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T) (x : Present rate rewards C_star C_h t) :
    ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t x.val =
      some (presentRecord rate rewards C_star C_h t x) :=
  (Option.some_get x.property).symm

private theorem presentRecord_decode_incoming
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T) (x : Present rate rewards C_star C_h t)
    (h : (ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t x.val).isSome = true) :
    ReferenceActivePhysicalStepMeasurability.decodeState
      ((ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t x.val).get h) =
        (presentRecord rate rewards C_star C_h t x).input.state := by
  simp only [ReferenceSourcePrefixHistoryFiltration.incoming,
    presentRecord_lookup rate rewards C_star C_h t x, Option.map_some, Option.get_some,
    ReferenceActivePhysicalStepMeasurability.decodeState_encodeState]

private def factorInput (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (n : ℕ) (hn : n ≤ p.T)
    (t : Fin p.T) (x : Present rate rewards C_star C_h t) :
    ReferenceActivePhysicalStep.RoundInput p rate where
  state := (presentRecord rate rewards C_star C_h t x).input.state
  rows := factorRows n hn x.val
  selected := ActualInitializationPhysicalStep.selectedRowIndex p x.val
  time := t
  active := by
    have ht := (actualRecord_input_fields rate rewards C_star C_h t x.val
      (presentRecord rate rewards C_star C_h t x)
      (presentRecord_lookup rate rewards C_star C_h t x)).2.2.1
    simpa only [ht] using (presentRecord rate rewards C_star C_h t x).input.active
  rewards := rewards

private theorem measurable_factorInput (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (n : ℕ) (hn : n ≤ p.T) (t : Fin p.T) (ht : t.val < n) :
    let : MeasurableSpace (BootstrapPrivateRoundStreams.SourceInput p) :=
      ReferenceSourceOwnHistoryContainment.inspectedHistorySpace rate rewards C_star C_h n hn
    Measurable (factorInput rate rewards C_star C_h n hn t) := by
  let : MeasurableSpace (BootstrapPrivateRoundStreams.SourceInput p) :=
    ReferenceSourceOwnHistoryContainment.inspectedHistorySpace rate rewards C_star C_h n hn
  have hin := (ReferenceSourceOwnHistoryContainment.incoming_measurable_in_inspectedHistorySpace
    rate rewards C_star C_h n hn t (Nat.le_of_lt ht)).comp
      (measurable_subtype_coe : Measurable (Subtype.val : Present rate rewards C_star C_h t → _))
  have hpresent (x : Present rate rewards C_star C_h t) :
      (ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t x.val).isSome = true := by
    simp only [ReferenceSourcePrefixHistoryFiltration.incoming, Option.isSome_map, x.property]
  have hstateCode := measurable_option_get _ hin hpresent
  have hdecoded (x : Present rate rewards C_star C_h t) :=
    presentRecord_decode_incoming rate rewards C_star C_h t x (hpresent x)
  have hstate : Measurable (fun x : Present rate rewards C_star C_h t =>
      (presentRecord rate rewards C_star C_h t x).input.state) := by
    apply measurable_comap_iff.mpr
    change Measurable (fun x : Present rate rewards C_star C_h t =>
      ReferenceActivePhysicalStepMeasurability.encodeState
        (presentRecord rate rewards C_star C_h t x).input.state)
    convert hstateCode using 1
    funext x
    have hencode : ReferenceActivePhysicalStepMeasurability.encodeState
        (presentRecord rate rewards C_star C_h t x).input.state =
      ReferenceActivePhysicalStepMeasurability.encodeState
        (ReferenceActivePhysicalStepMeasurability.decodeState
          ((ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t x.val).get (hpresent x))) :=
      congrArg ReferenceActivePhysicalStepMeasurability.encodeState (hdecoded x).symm
    rw [hencode]
    simp only [Function.comp_def, ReferenceSourcePrefixHistoryFiltration.incoming,
      presentRecord_lookup rate rewards C_star C_h t x, Option.map_some, Option.get_some,
      ReferenceActivePhysicalStepMeasurability.decodeState_encodeState]
  have hrows := (measurable_factorRows rate rewards C_star C_h n hn).comp
    (measurable_subtype_coe : Measurable (Subtype.val : Present rate rewards C_star C_h t → _))
  have hprivate := (privateCoordinates_measurable_in_inspectedHistorySpace
    rate rewards C_star C_h n hn).comp
    (measurable_subtype_coe : Measurable (Subtype.val : Present rate rewards C_star C_h t → _))
  have hselected : Measurable (fun x : Present rate rewards C_star C_h t =>
      ActualInitializationPhysicalStep.selectedRowIndex p x.val) :=
    (PrivateSourceStreams.measurable_coordinatorIndex p).comp
      (measurable_snd.comp (measurable_fst.comp hprivate))
  apply measurable_comap_iff.mpr
  apply Measurable.subtype_mk
  exact hstate.prodMk (hrows.prodMk (hselected.prodMk
    (measurable_const.prodMk measurable_const)))

private theorem factorInput_code_eq (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (n : ℕ) (hn : n ≤ p.T) (t : Fin p.T) (ht : t.val < n)
    (x : Present rate rewards C_star C_h t) :
    ReferenceActiveHorizonMeasurability.roundRecordCode
      (presentRecord rate rewards C_star C_h t x) =
    ReferenceActiveHorizonMeasurability.roundRecordCode
      ⟨factorInput rate rewards C_star C_h n hn t x,
        ReferenceActivePhysicalStep.step (factorInput rate rewards C_star C_h n hn t x), rfl⟩ := by
  let r := presentRecord rate rewards C_star C_h t x
  obtain ⟨hrows, hselected, htime, hrewards⟩ := actualRecord_input_fields
    rate rewards C_star C_h t x.val r (presentRecord_lookup rate rewards C_star C_h t x)
  have hcanonical : ReferenceActiveHorizonMeasurability.roundRecordCode r =
      ReferenceActiveHorizonMeasurability.roundRecordCode
        ⟨r.input, ReferenceActivePhysicalStep.step r.input, rfl⟩ := rfl
  rw [hcanonical]
  apply roundRecordCode_eq_of_temporal_reads r.input
    (factorInput rate rewards C_star C_h n hn t x) rfl hselected htime hrewards
  · change (r.input.rows r.input.selected).2 r.input.time =
      ((factorRows n hn x.val) (ActualInitializationPhysicalStep.selectedRowIndex p x.val)).2 t
    rw [hrows, hselected, htime]
    exact (factorRows_control n hn x.val t ht _).symm
  · intro v hv
    have hvn : v.val < n := by rw [htime] at hv; omega
    change ((r.input.rows r.input.selected).2 v).1 ContinuousControlSlice.Label.prop =
      (((factorRows n hn x.val) (ActualInitializationPhysicalStep.selectedRowIndex p x.val)).2 v).1
        ContinuousControlSlice.Label.prop
    rw [hrows, hselected, factorRows_control n hn x.val v hvn]

/-- Exact some-tag reconstruction, including every code component. -/
theorem pastRoundObservations_some_iff (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (n : ℕ) (hn : n ≤ p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (j : Fin n)
    (code : ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate)) :
    pastRoundObservations rate rewards C_star C_h n hn z j = some code ↔
      ∃ r, ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
        (Fin.castLE hn j) z = some r ∧
        ReferenceActiveHorizonMeasurability.roundRecordCode r = code := by
  simp only [pastRoundObservations, Option.map_eq_some_iff]

private theorem measurable_pastRoundObservation (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (n : ℕ) (hn : n ≤ p.T) (j : Fin n) :
    Measurable[ReferenceSourceOwnHistoryContainment.inspectedHistorySpace
      rate rewards C_star C_h n hn]
      (fun z => pastRoundObservations rate rewards C_star C_h n hn z j) := by
  let : MeasurableSpace (BootstrapPrivateRoundStreams.SourceInput p) :=
    ReferenceSourceOwnHistoryContainment.inspectedHistorySpace rate rewards C_star C_h n hn
  let t := Fin.castLE hn j
  let present : Set (BootstrapPrivateRoundStreams.SourceInput p) :=
    {z | (ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z).isSome = true}
  have hin := ReferenceSourceOwnHistoryContainment.incoming_measurable_in_inspectedHistorySpace
    rate rewards C_star C_h n hn t (Nat.le_of_lt j.isLt)
  have hs : MeasurableSet present := by
    have h := (measurable_option_isSome.comp hin) (measurableSet_singleton true)
    simpa only [Function.comp_def, present, ReferenceSourcePrefixHistoryFiltration.incoming,
      Option.isSome_map, Set.preimage, Set.mem_singleton_iff] using h
  apply measurable_of_restrict_of_restrict_compl hs
  · have hi := measurable_factorInput rate rewards C_star C_h n hn t j.isLt
    have hw := ReferenceActiveStepCompositionMeasurability.measurable_wholeStepCode.comp hi
    have hstate := ReferenceActivePhysicalStepMeasurability.measurable_encodeState.comp
      (ReferenceActivePhysicalStepMeasurability.measurable_state.comp hi)
    have hc : Measurable (fun x : Present rate rewards C_star C_h t =>
        ReferenceActiveHorizonMeasurability.roundRecordCode
          ⟨factorInput rate rewards C_star C_h n hn t x,
            ReferenceActivePhysicalStep.step (factorInput rate rewards C_star C_h n hn t x), rfl⟩) :=
      measurable_const.prodMk (hstate.prodMk hw)
    have hsome : Measurable (some :
        ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate) → Option _) :=
      measurable_comap_iff.mpr measurable_inl
    convert hsome.comp hc using 1
    funext x
    change (ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t x.val).map
      ReferenceActiveHorizonMeasurability.roundRecordCode = _
    rw [presentRecord_lookup rate rewards C_star C_h t x, Option.map_some,
      factorInput_code_eq rate rewards C_star C_h n hn t j.isLt x]
    rfl
  · have heq : (fun x : (presentᶜ : Set (BootstrapPrivateRoundStreams.SourceInput p)) => pastRoundObservations rate rewards C_star C_h n hn x.val j) =
        fun _ => none := by
      funext x
      apply (pastRoundObservations_none_iff rate rewards C_star C_h n hn x.val j).mpr
      cases hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t x.val with
      | none => rfl
      | some r =>
        exact False.elim (x.property (by simp only [present, Set.mem_ofPred_eq, hr, Option.isSome_some]))
    change Measurable (fun x : (presentᶜ : Set (BootstrapPrivateRoundStreams.SourceInput p)) =>
      pastRoundObservations rate rewards C_star C_h n hn x.val j)
    rw [heq]
    exact measurable_const

/-- The actual finite vector of optional whole-round observations is measurable
in exactly the existing inspected-history field. No adaptation or success
premise is supplied. The empty vector at `n = 0` is included. -/
theorem pastRoundObservations_measurable_in_inspectedHistorySpace
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (n : ℕ) (hn : n ≤ p.T) :
    Measurable[ReferenceSourceOwnHistoryContainment.inspectedHistorySpace
      rate rewards C_star C_h n hn]
      (pastRoundObservations rate rewards C_star C_h n hn) := by
  let : MeasurableSpace (BootstrapPrivateRoundStreams.SourceInput p) :=
    ReferenceSourceOwnHistoryContainment.inspectedHistorySpace rate rewards C_star C_h n hn
  exact measurable_pi_iff.mpr (measurable_pastRoundObservation rate rewards C_star C_h n hn)

/-- Ambient original-source Borel measurability follows by the established
containment of the exact inspected field in the original source space. -/
theorem measurable_pastRoundObservations
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (n : ℕ) (hn : n ≤ p.T) :
    Measurable (pastRoundObservations rate rewards C_star C_h n hn) :=
  (pastRoundObservations_measurable_in_inspectedHistorySpace rate rewards C_star C_h n hn).mono
    (ReferenceSourceOwnHistoryContainment.inspectedHistorySpace_le_original
      rate rewards C_star C_h (fixedControl p) n hn) le_rfl

/-- Literal strict-past postlaunch saved-wrong diagnostic. The existential
retains the some tag; it is neither a source decoder-error event nor a
prelaunch suppression test. -/
def pastSavedWrongFlag (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (n : ℕ) (hn : n ≤ p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p) : Bool :=
  decide (∃ j : Fin n, ∃ code,
    pastRoundObservations rate rewards C_star C_h n hn z j = some code ∧
      ReferenceSavedWrongUniqueMeasurability.savedWrongCode code = true)

/-- The flag is exactly an actual strict-past retained diagnostic, with its
original record and all absence tags. This is an internal characterization. -/
theorem pastSavedWrongFlag_eq_true_iff (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (n : ℕ) (hn : n ≤ p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    pastSavedWrongFlag rate rewards C_star C_h n hn z = true ↔
      ∃ j : Fin n, ∃ r,
        ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
          (Fin.castLE hn j) z = some r ∧
        ReferenceActiveStoppedPrefixCoupling.saved_wrong_unique_accepted r := by
  simp only [pastSavedWrongFlag, decide_eq_true_eq]
  constructor
  · rintro ⟨j, code, hcode, hwrong⟩
    obtain ⟨r, hr, rfl⟩ := (pastRoundObservations_some_iff
      rate rewards C_star C_h n hn z j code).mp hcode
    exact ⟨j, r, hr, (ReferenceSavedWrongUniqueMeasurability.savedWrongCode_roundRecord_iff r).mp hwrong⟩
  · rintro ⟨j, r, hr, hwrong⟩
    exact ⟨j, ReferenceActiveHorizonMeasurability.roundRecordCode r,
      pastRoundObservations_some rate rewards C_star C_h n hn z j r hr,
      (ReferenceSavedWrongUniqueMeasurability.savedWrongCode_roundRecord_iff r).mpr hwrong⟩

private theorem measurable_savedWrongOption : Measurable
    (fun code : Option (ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate)) =>
      code.elim false ReferenceSavedWrongUniqueMeasurability.savedWrongCode) := by
  have h := (ReferenceSavedWrongUniqueMeasurability.measurable_savedWrongCode (p := p) (rate := rate)).sumElim
    (measurable_const : Measurable (fun _ : PUnit => false))
  convert h.comp (comap_measurable (Equiv.optionEquivSumPUnit
    (ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate)))) using 1
  funext code
  cases code <;> rfl

/-- The retained strict-past saved-wrong flag is measurable in the same exact
field, without a decoder correctness, queue, launch-stratum, or mass premise. -/
theorem pastSavedWrongFlag_measurable_in_inspectedHistorySpace
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (n : ℕ) (hn : n ≤ p.T) :
    Measurable[ReferenceSourceOwnHistoryContainment.inspectedHistorySpace
      rate rewards C_star C_h n hn]
      (pastSavedWrongFlag rate rewards C_star C_h n hn) := by
  let : MeasurableSpace (BootstrapPrivateRoundStreams.SourceInput p) :=
    ReferenceSourceOwnHistoryContainment.inspectedHistorySpace rate rewards C_star C_h n hn
  have htest (j : Fin n) : Measurable (fun z =>
      (pastRoundObservations rate rewards C_star C_h n hn z j).elim false
        ReferenceSavedWrongUniqueMeasurability.savedWrongCode) :=
    measurable_savedWrongOption.comp (measurable_pastRoundObservation rate rewards C_star C_h n hn j)
  have hs : MeasurableSet {z | ∃ j : Fin n,
      (pastRoundObservations rate rewards C_star C_h n hn z j).elim false
        ReferenceSavedWrongUniqueMeasurability.savedWrongCode = true} := by
    have h := MeasurableSet.iUnion fun j => (htest j) (measurableSet_singleton true)
    convert h using 1
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_preimage, Set.mem_singleton_iff]
  apply measurable_to_bool
  convert hs using 1
  ext z
  simp only [Set.mem_preimage, Set.mem_singleton_iff, pastSavedWrongFlag,
    decide_eq_true_eq, Set.mem_ofPred_eq]
  apply exists_congr
  intro j
  cases hcode : pastRoundObservations rate rewards C_star C_h n hn z j <;> simp

/-- The same diagnostic is Borel on the unchanged whole original source. -/
theorem measurable_pastSavedWrongFlag
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (n : ℕ) (hn : n ≤ p.T) :
    Measurable (pastSavedWrongFlag rate rewards C_star C_h n hn) :=
  (pastSavedWrongFlag_measurable_in_inspectedHistorySpace rate rewards C_star C_h n hn).mono
    (ReferenceSourceOwnHistoryContainment.inspectedHistorySpace_le_original
      rate rewards C_star C_h (fixedControl p) n hn) le_rfl

/-- The zero-length history is the unique empty finite vector. -/
theorem pastRoundObservations_zero (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (hn : 0 ≤ p.T) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    pastRoundObservations rate rewards C_star C_h 0 hn z = fun j => Fin.elim0 j := by
  funext j
  exact Fin.elim0 j

/-- Before an actual launch there is no postlaunch whole-round observation. -/
theorem pastRoundObservations_none_of_not_launchBy
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (n : ℕ) (hn : n ≤ p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (j : Fin n)
    (h : ¬ ReferenceSourcePrefixHistoryFiltration.actualLaunchBy rate rewards C_star C_h j.val z) :
    pastRoundObservations rate rewards C_star C_h n hn z j = none :=
  (pastRoundObservations_none_iff rate rewards C_star C_h n hn z j).mpr
    (ReferenceSourcePrefixHistoryFiltration.actualRecord_eq_none_of_not_launchBy
      rate rewards C_star C_h (Fin.castLE hn j) z h)

/-- The calendar observation remains absent strictly before its actual start. -/
theorem pastRoundObservations_none_of_future_start
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (n : ℕ) (hn : n ≤ p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (j : Fin n)
    (h : j.val < ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) :
    pastRoundObservations rate rewards C_star C_h n hn z j = none :=
  (pastRoundObservations_none_iff rate rewards C_star C_h n hn z j).mpr
    (ReferenceSourcePrefixHistoryFiltration.actualRecord_eq_none_of_future_start
      rate rewards C_star C_h (Fin.castLE hn j) z h)

/-- An elapsed-`T` launch has no physical round in the observation vector. -/
theorem pastRoundObservations_none_of_terminal_start
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (n : ℕ) (hn : n ≤ p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (h : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h = p.T) :
    pastRoundObservations rate rewards C_star C_h n hn z = fun _ => none := by
  funext j
  exact (pastRoundObservations_none_iff rate rewards C_star C_h n hn z j).mpr
    (ReferenceSourcePrefixHistoryFiltration.actualRecord_eq_none_of_terminal_start
      rate rewards C_star C_h (Fin.castLE hn j) z h)

/-- Actual no-launch input has only absent postlaunch observations. -/
theorem pastRoundObservations_none_of_no_crossing
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (n : ℕ) (hn : n ≤ p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (h : (ReferenceCompletePhysicalHistory.generatedBoundary rate z rewards C_star C_h).crossing = none) :
    pastRoundObservations rate rewards C_star C_h n hn z = fun _ => none := by
  funext j
  exact (pastRoundObservations_none_iff rate rewards C_star C_h n hn z j).mpr
    (ReferenceSourcePrefixHistoryFiltration.actualRecord_eq_none_of_no_crossing
      rate rewards C_star C_h (Fin.castLE hn j) z h)

/-- At an actual in-horizon launch, the retained record is present and its
incoming coordinator is the genuine corrected-launch FIRST configuration. -/
theorem pastRoundObservations_at_launch
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (n : ℕ) (hn : n ≤ p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (j : Fin n)
    (hcross : (ReferenceCompletePhysicalHistory.generatedBoundary rate z rewards C_star C_h).crossing.isSome = true)
    (hstart : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h = j.val) :
    ∃ r, ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
        (Fin.castLE hn j) z = some r ∧
      pastRoundObservations rate rewards C_star C_h n hn z j =
        some (ReferenceActiveHorizonMeasurability.roundRecordCode r) ∧
      r.input.state.coordinator = .first := by
  let seed := ReferenceLocalReleaseGateChronology.sourceSeed rate z rewards C_star C_h hcross
  have hl := ReferenceLocalReleaseGateChronology.sourceSeed_launch rate z rewards C_star C_h hcross
  have hs : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h ≤
      (Fin.castLE hn j).val := by rw [hstart]; exact le_rfl
  have hr := ReferenceSourcePrefixHistoryFiltration.actualRecord_on_launch
    rate rewards C_star C_h (Fin.castLE hn j) z seed hl hs
  refine ⟨_, hr, pastRoundObservations_some rate rewards C_star C_h n hn z j _ hr, ?_⟩
  have hzero : (Fin.castLE hn j).val -
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h = 0 := by
    rw [hstart]
    exact Nat.sub_self j.val
  dsimp only [ReferenceAssignmentPayloadChronology.actualRunRecordAt,
    ReferenceActivePhysicalHorizon.roundInputAt]
  simp only [hzero, ReferenceActivePhysicalHorizon.run_zero_final]
  exact (ReferenceLocalReleaseGateChronology.canonical_seed_release_inputs
    rate z rewards C_star C_h hcross).1

/-- No postlaunch diagnostic occurs in the empty strict-past vector. -/
theorem pastSavedWrongFlag_zero (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (hn : 0 ≤ p.T) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    pastSavedWrongFlag rate rewards C_star C_h 0 hn z = false := by
  simp only [pastSavedWrongFlag, Fin.exists_fin_zero, decide_false]

end Bandits.Support.ReferenceInspectedPastRoundObservations
