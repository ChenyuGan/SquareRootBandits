/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedDownBatchCalendar

import Lean.Elab.Tactic.Omega

/-!
# Borel and control factors for generated DOWN batch prefixes

Sources: `sources/zip4/manuscript/appendix_a_local_protocol.tex:112-138`,
`sources/zip4/manuscript/05_binary_transport.tex:20-42`,
`sources/zip4/manuscript/07_public_setup.tex:127-142`, and
`sources/zip4/manuscript/08_main_theorem.tex:29-42`.

This module factors the actual finite prefix used by the generated DOWN
calendar. Its retained inputs are the original selected-row remainder
intersected with the computed launch-start event. It does not replace the
physical batch bank or prove a probability recurrence. The source-marker
factor below is internal support; no manuscript event coverage or closure is
asserted.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open scoped Classical

namespace Bandits.Support.ReferenceGeneratedDownPrefixEvent

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceGeneratedDownBatchCalendar.RateInput
abbrev TimeControl := ContinuousLearningRows.TimeControl
abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput

variable {p : Parameters} {rate : RateInput p}

open ReferenceGeneratedDownBatchCalendar
open ReferenceRetainedBoundaryMeasurability
open ReferenceDownCompletedAmbiguityMeasurability
open ReferenceActiveHorizonMeasurability
open ReferenceActivePhysicalHorizon
open ReferenceGeneratedActivePrefixFactor
open ReferenceFixedTimeSourceControlCoupling

local instance : MeasurableSingletonClass
    (ReferenceDownReceptionMeasurability.ReferenceDownCutCode p rate) := ⟨fun _ => trivial⟩

private theorem measurableSet_option_singleton {α : Type*}
    [MeasurableSpace α] [MeasurableSingletonClass α] (a : Option α) :
    MeasurableSet[LaterAssignmentStartMeasurability.optionMeasurableSpace] {a} := by
  let e := Equiv.optionEquivSumPUnit α
  have he : @Measurable (Option α) (α ⊕ PUnit)
      LaterAssignmentStartMeasurability.optionMeasurableSpace inferInstance e := comap_measurable _
  have hset : ({a} : Set (Option α)) = e ⁻¹' {e a} := by
    ext x
    exact ⟨fun h => congrArg e h, fun h => e.injective h⟩
  rw [hset]
  apply he
  cases h : e a with
  | inl value =>
      simpa only [Set.image_singleton] using
        (measurableSet_singleton value).inl_image (β := PUnit)
  | inr value =>
      simpa only [Set.image_singleton] using
        (measurableSet_singleton value).inr_image (α := α)

local instance {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] :
    @MeasurableSingletonClass (Option α) LaterAssignmentStartMeasurability.optionMeasurableSpace :=
  ⟨measurableSet_option_singleton⟩

/-- The same generated all-active run input used literally by D's retained
calendar projections. The state, whole rows, selected original J, and complete
reward table are kept as their actual coordinates. -/
def retainedPrefixRunInput
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (j : Fin (M p)) (r : Fin p.T) (s : ℕ)
    (hsr : s ≤ r.val) (control0 : TimeControl p)
    (x : RetainedLaunchStart rate rewards C_star C_h j r s hsr control0) :
    ActiveRunInput (p := p) (rate := rate) s := by
  refine ⟨(retainedGeneratedActiveSeed rate rewards C_star C_h j r s hsr control0 x,
    ((splitSource j r control0 x.1).1.2, (j, rewards))), ?_⟩
  exact (generatedActiveSeed_spec rate rewards C_star C_h j r control0 x.1 x.2.1
    s hsr x.2.2).2.1

/-- This map is Borel on B's inherited original-remainder launch-start
subtype. Only the generated seed and the row/reward coordinates vary. -/
theorem measurable_retainedPrefixRunInput
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (j : Fin (M p)) (r : Fin p.T) (s : ℕ)
    (hsr : s ≤ r.val) (control0 : TimeControl p) :
    Measurable (retainedPrefixRunInput rate rewards C_star C_h j r s hsr control0) := by
  let source := fun x : RetainedLaunchStart rate rewards C_star C_h j r s hsr control0 =>
    splitSource j r control0 x.1
  have hsource : Measurable source := by
    change Measurable (fun x : RetainedLaunchStart rate rewards C_star C_h j r s hsr control0 =>
      (fixedControlSplit p j r).symm (control0, x.1))
    exact (fixedControlSplit p j r).symm.measurable.comp
      (measurable_const.prodMk measurable_subtype_coe)
  have hseed : Measurable (fun x : RetainedLaunchStart
      rate rewards C_star C_h j r s hsr control0 =>
      retainedGeneratedActiveSeed rate rewards C_star C_h j r s hsr control0 x) :=
    measurable_retainedGeneratedActiveSeed rate rewards C_star C_h j r s hsr control0
  have hrows : Measurable (fun x : RetainedLaunchStart
      rate rewards C_star C_h j r s hsr control0 => (source x).1.2) :=
    measurable_snd.comp (measurable_fst.comp hsource)
  have hdata : Measurable (fun x : RetainedLaunchStart
      rate rewards C_star C_h j r s hsr control0 =>
      (retainedGeneratedActiveSeed rate rewards C_star C_h j r s hsr control0 x,
        ((source x).1.2, (j, rewards)))) :=
    hseed.prodMk (hrows.prodMk (measurable_const.prodMk measurable_const))
  have hinput : Measurable
      (retainedPrefixRunInput rate rewards C_star C_h j r s hsr control0) := by
    exact hdata.subtype_mk
  exact hinput

/-- The actual V observation over the half-open physical interval `[s,r)`
used by D's marker. -/
def retainedPrefixObservation
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (j : Fin (M p)) (r : Fin p.T) (s : ℕ)
    (hsr : s ≤ r.val) (control0 : TimeControl p)
    (i : Fin (p.m - 1))
    (x : RetainedLaunchStart rate rewards C_star C_h j r s hsr control0) :=
  runDownObservation (p := p) (rate := rate) s (r.val - s) (by omega) i
    (retainedPrefixRunInput rate rewards C_star C_h j r s hsr control0 x)

private theorem measurable_retainedIncomingRegisters
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (j : Fin (M p)) (r : Fin p.T) (s : ℕ)
    (hsr : s ≤ r.val) (control0 : TimeControl p)
    (i : Fin (p.m - 1)) (count : ℕ) (hspan : s + count ≤ p.T) :
    Measurable (fun x : RetainedLaunchStart rate rewards C_star C_h j r s hsr control0 =>
      incomingRegisters (FollowerPrepareJointMeasurability.incomingOfLocalConfiguration rate
        (((ReferenceActiveHorizonMeasurability.runOfInput (p := p) (rate := rate)
          s count hspan (retainedPrefixRunInput rate rewards C_star C_h j r s hsr control0 x)).finalState).followers i))) := by
  have hstate : Measurable (fun x : RetainedLaunchStart
      rate rewards C_star C_h j r s hsr control0 =>
      (ReferenceActiveHorizonMeasurability.runOfInput (p := p) (rate := rate)
        s count hspan (retainedPrefixRunInput rate rewards C_star C_h j r s hsr control0 x)).finalState) :=
    (ReferenceActiveHorizonMeasurability.measurable_runFinalState
      (p := p) (rate := rate) s count hspan).comp
      (measurable_retainedPrefixRunInput rate rewards C_star C_h j r s hsr control0)
  have hfollowers : Measurable (fun x : RetainedLaunchStart
      rate rewards C_star C_h j r s hsr control0 =>
      FollowerPrepareJointMeasurability.incomingOfLocalConfiguration rate
        (((ReferenceActiveHorizonMeasurability.runOfInput (p := p) (rate := rate)
          s count hspan (retainedPrefixRunInput rate rewards C_star C_h j r s hsr control0 x)).finalState).followers i)) := by
    exact (measurable_pi_apply i).comp
      (ReferenceActivePhysicalStepMeasurability.measurable_followerCodes.comp hstate)
  exact measurable_incomingRegisters.comp hfollowers

private theorem localConfiguration_isOrdinary_iff
    (rate : RateInput p)
    (configuration : DeclaredFollowerLocalRound.LocalConfiguration p rate) :
    (∃ state memory, configuration = .ordinary state memory) ↔
      (incomingRegisters (FollowerPrepareJointMeasurability.incomingOfLocalConfiguration
        rate configuration)).isSome = true := by
  cases configuration <;> simp [incomingRegisters_actual]

private theorem followerStateCode_reconstructCarriedState
    (carry : FollowerObservationStageMeasurabilityRepair.CarriedState p rate) :
    FollowerDownMeasurability.followerStateCode rate
      (FollowerObservationStageMeasurabilityRepair.reconstructCarriedState carry.1 carry.2) =
      carry.1.1 := by
  have hstatus (status : Fin 3) : FollowerDownMeasurability.followerStatusCode
      (FollowerDownMeasurability.followerStatusOfCode status) = status := by
    fin_cases status <;> rfl
  rcases carry with ⟨⟨code, skeleton⟩, values⟩
  cases code
  simp only [FollowerObservationStageMeasurabilityRepair.reconstructCarriedState,
    FollowerDownMeasurability.followerStateOfCode, FollowerDownMeasurability.followerStateCode,
    hstatus, FollowerDownMeasurability.decoderBatchOfCode,
    FollowerDownMeasurability.decoderBatchCode, List.map_map, Function.comp_def,
    FollowerDownMeasurability.decoderEntryCode, FollowerDownMeasurability.decoderEntryOfCode,
    Prod.eta, List.map_id']

private theorem preparedRegisters_eq_of_configuration_eq
    (x y : ReferenceActivePhysicalStep.RoundInput p rate) (i : Fin (p.m - 1))
    (hconfiguration :
      ((ReferenceActivePhysicalStep.prepare x).followers.followers i).configuration =
      ((ReferenceActivePhysicalStep.prepare y).followers.followers i).configuration) :
    ReferenceDownCompletedAmbiguityMeasurability.preparedRegisters x i =
      ReferenceDownCompletedAmbiguityMeasurability.preparedRegisters y i := by
  let codeX := ReferenceActivePhysicalStepMeasurability.preparedFollowerCode x i
  let codeY := ReferenceActivePhysicalStepMeasurability.preparedFollowerCode y i
  have hdecodedX : FollowerPrepareJointMeasurability.localConfigurationOfIncoming rate
      codeX.2.2.2 = ((ReferenceActivePhysicalStep.prepare x).followers.followers i).configuration := by
    exact congrArg DeclaredFollowerLocalRound.PreparedRound.configuration
      (ReferenceActivePhysicalStepMeasurability.preparedFollowerCode_reconstruct x i)
  have hdecodedY : FollowerPrepareJointMeasurability.localConfigurationOfIncoming rate
      codeY.2.2.2 = ((ReferenceActivePhysicalStep.prepare y).followers.followers i).configuration := by
    exact congrArg DeclaredFollowerLocalRound.PreparedRound.configuration
      (ReferenceActivePhysicalStepMeasurability.preparedFollowerCode_reconstruct y i)
  have hdecoded : FollowerPrepareJointMeasurability.localConfigurationOfIncoming rate
      codeX.2.2.2 =
      FollowerPrepareJointMeasurability.localConfigurationOfIncoming rate codeY.2.2.2 :=
    hdecodedX.trans (hconfiguration.trans hdecodedY.symm)
  change incomingRegisters codeX.2.2.2 = incomingRegisters codeY.2.2.2
  cases hx : codeX.2.2.2 with
  | none =>
      have hy : codeY.2.2.2 = none := by
        cases hcode : codeY.2.2.2 with
        | none => rfl
        | some data => simp [FollowerPrepareJointMeasurability.localConfigurationOfIncoming,
            hx, hcode] at hdecoded
      rw [hy]
  | some dataX =>
      rcases dataX with ⟨carryX, memoryX⟩
      cases hy : codeY.2.2.2 with
      | none =>
          simp [FollowerPrepareJointMeasurability.localConfigurationOfIncoming, hx, hy] at hdecoded
      | some dataY =>
          rcases dataY with ⟨carryY, memoryY⟩
          simp only [FollowerPrepareJointMeasurability.localConfigurationOfIncoming, hx, hy] at hdecoded
          have hstate : FollowerObservationStageMeasurabilityRepair.reconstructCarriedState
              carryX.1 carryX.2 =
            FollowerObservationStageMeasurabilityRepair.reconstructCarriedState carryY.1 carryY.2 := by
            injection hdecoded with hstate
          have hregisters := (followerStateCode_reconstructCarriedState (p := p) (rate := rate) carryX).symm
          have hregisters' := followerStateCode_reconstructCarriedState (p := p) (rate := rate) carryY
          simpa [ReferenceDownCompletedAmbiguityMeasurability.incomingRegisters, hx, hy] using
            congrArg some (hregisters.trans
              ((congrArg (FollowerDownMeasurability.followerStateCode rate) hstate).trans hregisters'))

private theorem diagnosticProjection_reconstruct
    (output : ReferenceFollowerTailComposition.FollowerObservable p rate) :
    ReferenceDownCompletedAmbiguityMeasurability.diagnosticProjection output =
      ((ReferenceFollowerTailComposition.reconstructFollowerObservable output).downInput.map
        (FollowerDownMeasurability.followerStateCode rate),
       (ReferenceFollowerTailComposition.reconstructFollowerObservable output).failure,
       (ReferenceFollowerTailComposition.reconstructFollowerObservable output).down.map
         ReferenceDownCompletedAmbiguityMeasurability.cutFields) := by
  rcases output with ⟨incoming, failure, input, cut⟩
  cases input with
  | inl absent => rfl
  | inr carry =>
      cases cut with
      | none =>
          simp only [ReferenceDownCompletedAmbiguityMeasurability.diagnosticProjection,
            ReferenceFollowerTailComposition.reconstructFollowerObservable,
            ReferenceFollowerTailComposition.reconstructDownInput,
            ReferenceFollowerTailComposition.reconstructDown, Option.map_some,
            Option.map_none, ReferenceFollowerTailComposition.reconstructCarry,
            followerStateCode_reconstructCarriedState]
      | some code =>
          simp only [ReferenceDownCompletedAmbiguityMeasurability.diagnosticProjection,
            ReferenceFollowerTailComposition.reconstructFollowerObservable,
            ReferenceFollowerTailComposition.reconstructDownInput,
            ReferenceFollowerTailComposition.reconstructDown, Option.map_some,
            ReferenceFollowerTailComposition.reconstructCarry,
            followerStateCode_reconstructCarriedState]
          congr 2
          simp only [ReferenceDownCompletedAmbiguityMeasurability.cutCodeFields,
            ReferenceDownCompletedAmbiguityMeasurability.cutFields,
            ReferenceDownReceptionMeasurability.reconstructReferenceDownCutCode,
            decide_eq_true_eq]
          cases code.ordinaryAcceptance <;> rfl

private def diagnosticOfFollower
    (output : ReferenceActivePhysicalStep.FollowerObservation p rate) :
    ReferenceDownCompletedAmbiguityMeasurability.DownDiagnosticCode p rate :=
  (output.downInput.map (FollowerDownMeasurability.followerStateCode rate),
    output.failure, output.down.map ReferenceDownCompletedAmbiguityMeasurability.cutFields)

private theorem roundDownObservation_eq_of_temporal_reads
    (state : ReferenceActivePhysicalStep.State p rate)
    (rows otherRows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (time : Fin p.T)
    (active : ∀ i, (state.activations i).val ≤ time.val + 1)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (i : Fin (p.m - 1))
    (hcurrent : (rows selected).2 time = (otherRows selected).2 time)
    (hpast : ∀ j : Fin p.T, j.val < time.val →
      ((rows selected).2 j).1 ContinuousControlSlice.Label.prop =
        ((otherRows selected).2 j).1 ContinuousControlSlice.Label.prop) :
    ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation
        (⟨state, rows, selected, time, active, rewards⟩ : ReferenceActivePhysicalStep.RoundInput p rate) i =
      ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation
        (⟨state, otherRows, selected, time, active, rewards⟩ : ReferenceActivePhysicalStep.RoundInput p rate) i := by
  let x : ReferenceActivePhysicalStep.RoundInput p rate := ⟨state, rows, selected, time, active, rewards⟩
  let y : ReferenceActivePhysicalStep.RoundInput p rate := ⟨state, otherRows, selected, time, active, rewards⟩
  have hcurrent' : (x.row.2 x.time) = (y.row.2 y.time) := by
    change (rows selected).2 time = (otherRows selected).2 time
    exact hcurrent
  have hpast' : ∀ j : Fin p.T, j.val < x.time.val →
      (x.row.2 j).1 ContinuousControlSlice.Label.prop = (y.row.2 j).1 ContinuousControlSlice.Label.prop := by
    intro j hj
    change ((rows selected).2 j).1 ContinuousControlSlice.Label.prop =
      ((otherRows selected).2 j).1 ContinuousControlSlice.Label.prop
    exact hpast j hj
  have hevidence := ReferenceActiveTemporalAssembly.computedEvidence_eq_of_temporal_reads
    state rows otherRows selected time active rewards rewards hcurrent hpast rfl
  have hconfiguration :
      ((ReferenceActivePhysicalStep.prepare x).followers.followers i).configuration =
      ((ReferenceActivePhysicalStep.prepare y).followers.followers i).configuration := by
    rw [(ReferenceActivePhysicalStep.prepare x).followers.followers_eq i,
      (ReferenceActivePhysicalStep.prepare y).followers.followers_eq i,
      ReferenceActiveFeedbackCut.prepareFollowers_apply,
      ReferenceActiveFeedbackCut.prepareFollowers_apply]
    exact congrArg Prod.snd
      (ReferenceActiveTemporalCausality.prepare_projections_eq_of_current
        (row := x.row) (otherRow := y.row) (t := time) i (state.activations i)
        (active i) (state.followers i) hcurrent')
  have hregisters := preparedRegisters_eq_of_configuration_eq x y i hconfiguration
  have hfeedback :
      (ReferenceActivePhysicalStep.prepare x).feedback.feedback
          (PublicDiscreteDraws.followerPlayer p.two_le_m i) =
        (ReferenceActivePhysicalStep.prepare y).feedback.feedback
          (PublicDiscreteDraws.followerPlayer p.two_le_m i) := by
    have h := congrArg (fun evidence : ReferenceActivePhysicalHorizon.RoundEvidence =>
      evidence.gridFeedback (PublicDiscreteDraws.followerPlayer p.two_le_m i)) hevidence
    simpa [ReferenceActivePhysicalHorizon.computedEvidence,
      ReferenceActivePhysicalHorizon.RoundRecord.evidence,
      ReferenceActivePhysicalHorizon.RoundRecord.gridFeedback,
      ReferenceActivePhysicalStep.step] using h
  have hgrid : ReferenceDownCompletedAmbiguityMeasurability.ownGrid x i =
      ReferenceDownCompletedAmbiguityMeasurability.ownGrid y i := by
    unfold ReferenceDownCompletedAmbiguityMeasurability.ownGrid
    rw [(ReferenceActiveStepCompositionMeasurability.wholeStepCode_front x).2.2.2,
      (ReferenceActiveStepCompositionMeasurability.wholeStepCode_front y).2.2.2]
    exact hfeedback
  have hcall : ReferenceDownCompletedAmbiguityMeasurability.roundCallObservation x i =
      ReferenceDownCompletedAmbiguityMeasurability.roundCallObservation y i := by
    unfold ReferenceDownCompletedAmbiguityMeasurability.roundCallObservation
    have hdown : ActiveFollowerDownAcceptance.downSelected p i x.row x.time =
        ActiveFollowerDownAcceptance.downSelected p i y.row y.time := by
      simp only [ActiveFollowerDownAcceptance.downSelected, hcurrent']
    have hsample : (x.row.2 x.time).2 (0, i) = (y.row.2 y.time).2 (0, i) :=
      congrArg (fun control : TimeControl p => control.2 (0, i)) hcurrent'
    simp only [hregisters, hgrid, hdown, hsample]
    rfl
  have hdiagnostic :
      ReferenceDownCompletedAmbiguityMeasurability.diagnosticProjection
          ((ReferenceActiveStepCompositionMeasurability.wholeStepCode x).2.1 i) =
        ReferenceDownCompletedAmbiguityMeasurability.diagnosticProjection
          ((ReferenceActiveStepCompositionMeasurability.wholeStepCode y).2.1 i) := by
    rw [diagnosticProjection_reconstruct, diagnosticProjection_reconstruct]
    have hwholeX := ReferenceActiveStepCompositionMeasurability.wholeStepCode_reconstructs x
    have hwholeY := ReferenceActiveStepCompositionMeasurability.wholeStepCode_reconstructs y
    rw [hwholeX.2.1 i, hwholeY.2.1 i]
    have hfollowers := congrArg (fun evidence : ReferenceActivePhysicalHorizon.RoundEvidence =>
      evidence.followers i) hevidence
    simpa [ReferenceActivePhysicalHorizon.computedEvidence,
      ReferenceActivePhysicalHorizon.RoundRecord.evidence,
      ReferenceActivePhysicalHorizon.RoundRecord.followerDiagnostics,
      ReferenceActivePhysicalStep.step,
      diagnosticOfFollower] using congrArg diagnosticOfFollower hfollowers
  unfold ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · exact hgrid
    · apply Prod.ext
      · exact hcall
      · exact hdiagnostic

private theorem activeRoundInput_ext
    {left right : ReferenceActivePhysicalStep.RoundInput p rate}
    (hstate : left.state = right.state) (hrows : left.rows = right.rows)
    (hselected : left.selected = right.selected) (htime : left.time = right.time)
    (hrewards : left.rewards = right.rewards) : left = right := by
  cases left
  cases right
  simp_all

/-- The actual V observation over a half-open run is fixed by the initial
state and the temporal controls read by the generated computation. -/
private theorem runDownObservation_eq_of_temporal_reads
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows otherRows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hcontrols : ∀ j : Fin p.T, start ≤ j.val → j.val < start + count →
      (rows selected).2 j = (otherRows selected).2 j)
    (hbefore : ∀ j : Fin p.T, j.val < start →
      ((rows selected).2 j).1 ContinuousControlSlice.Label.prop =
        ((otherRows selected).2 j).1 ContinuousControlSlice.Label.prop)
    (i : Fin (p.m - 1)) :
    ReferenceDownCompletedAmbiguityMeasurability.runDownObservation
        (p := p) (rate := rate) start count hspan i
        (⟨(initial, (rows, (selected, rewards))), hmode⟩ : ActiveRunInput (p := p) (rate := rate) start) =
      ReferenceDownCompletedAmbiguityMeasurability.runDownObservation
        (p := p) (rate := rate) start count hspan i
        (⟨(initial, (otherRows, (selected, rewards))), hmode⟩ : ActiveRunInput (p := p) (rate := rate) start) := by
  let leftInput : ActiveRunInput (p := p) (rate := rate) start :=
    ⟨(initial, (rows, (selected, rewards))), hmode⟩
  let rightInput : ActiveRunInput (p := p) (rate := rate) start :=
    ⟨(initial, (otherRows, (selected, rewards))), hmode⟩
  unfold ReferenceDownCompletedAmbiguityMeasurability.runDownObservation
  apply Prod.ext
  · rfl
  · funext k
    let prefixCount := k.val
    have hprefixSpan : start + prefixCount ≤ p.T := by omega
    have hrun := ReferenceActiveTemporalAssembly.run_eq_of_temporal_reads initial
      rows otherRows selected rewards rewards start prefixCount hprefixSpan hmode
      (fun j hjstart hjend => hcontrols j hjstart (by omega))
      (fun _ _ _ => rfl)
      (by intro _ j hj; exact hbefore j hj)
    let leftRound := ReferenceDownCompletedAmbiguityMeasurability.prefixInput
      (p := p) (rate := rate) start k.val (by omega) leftInput
    let rightRound := ReferenceDownCompletedAmbiguityMeasurability.prefixInput
      (p := p) (rate := rate) start k.val (by omega) rightInput
    have hleftTime : leftRound.time.val = start + k.val := by
      simp [leftRound, ReferenceDownCompletedAmbiguityMeasurability.prefixInput,
        ReferenceActivePhysicalHorizon.roundInputAt]
    let commonRight : ReferenceActivePhysicalStep.RoundInput p rate :=
      ⟨leftRound.state, otherRows, selected, leftRound.time, leftRound.active, rewards⟩
    have hright : rightRound = commonRight := by
      apply activeRoundInput_ext
      · simpa [rightRound, leftRound, commonRight, leftInput, rightInput,
          ReferenceDownCompletedAmbiguityMeasurability.prefixInput,
          ReferenceActivePhysicalHorizon.roundInputAt,
          ReferenceActiveHorizonMeasurability.runOfInput] using hrun.1.symm
      · rfl
      · rfl
      · rfl
      · rfl
    have hcurrent : (leftRound.rows selected).2 leftRound.time =
        (otherRows selected).2 leftRound.time := by
      change (rows selected).2 leftRound.time = (otherRows selected).2 leftRound.time
      exact hcontrols leftRound.time (by omega) (by omega)
    have hpast : ∀ j : Fin p.T, j.val < leftRound.time.val →
        ((leftRound.rows selected).2 j).1 ContinuousControlSlice.Label.prop =
          ((otherRows selected).2 j).1 ContinuousControlSlice.Label.prop := by
      intro j hj
      by_cases hjbefore : j.val < start
      · change ((rows selected).2 j).1 ContinuousControlSlice.Label.prop =
          ((otherRows selected).2 j).1 ContinuousControlSlice.Label.prop
        exact hbefore j hjbefore
      · have hjstart : start ≤ j.val := by omega
        have hjend : j.val < start + count := by
          have hk : k.val < count := k.isLt
          omega
        have hread := hcontrols j hjstart hjend
        exact congrArg (fun control : TimeControl p =>
          control.1 ContinuousControlSlice.Label.prop) hread
    have hround := roundDownObservation_eq_of_temporal_reads leftRound.state
      leftRound.rows otherRows selected leftRound.time leftRound.active rewards i hcurrent hpast
    change ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation leftRound i =
      ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation rightRound i
    exact hround.trans (congrArg
      (fun input => ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation input i)
      hright.symm)

/-- The actual generated run input after replacing the whole selected-row
control at the current physical round. The original remainder keeps every
other row and every private source coordinate fixed. -/
def retainedPrefixRunInputAtControl
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (j : Fin (M p)) (r : Fin p.T) (s : ℕ)
    (hsr : s ≤ r.val) (control0 control : TimeControl p)
    (x : RetainedLaunchStart rate rewards C_star C_h j r s hsr control0) :
    ActiveRunInput (p := p) (rate := rate) s := by
  let hstart := (ReferenceInitializationControlRemainder.launchStartRemainderEvent_control_independent
    rate rewards C_star C_h j r s x.1 x.2.1 control0 control).mp x.2.2
  refine ⟨(ReferenceGeneratedActivePrefixFactor.generatedActiveSeed
    rate rewards C_star C_h j r control x.1 x.2.1 s hsr hstart,
    ((ReferenceGeneratedActivePrefixFactor.splitSource j r control x.1).1.2,
      (j, rewards))), ?_⟩
  exact (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
    rate rewards C_star C_h j r control x.1 x.2.1 s hsr hstart).2.1

/-- The actual before-current-round observation agrees under every whole
control replacement at `r`. It observes exactly `[s,r)`, so the replacement
at `r` is excluded while the generated seed and original source coordinates
are retained. -/
theorem retainedPrefixObservation_control_independent
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (j : Fin (M p)) (r : Fin p.T) (s : ℕ)
    (hsr : s ≤ r.val) (control0 control : TimeControl p)
    (i : Fin (p.m - 1))
    (x : RetainedLaunchStart rate rewards C_star C_h j r s hsr control0) :
    retainedPrefixObservation rate rewards C_star C_h j r s hsr control0 i x =
      runDownObservation (p := p) (rate := rate) s (r.val - s) (by omega) i
        (retainedPrefixRunInputAtControl rate rewards C_star C_h j r s hsr control0 control x) := by
  classical
  let hstart := (ReferenceInitializationControlRemainder.launchStartRemainderEvent_control_independent
    rate rewards C_star C_h j r s x.1 x.2.1 control0 control).mp x.2.2
  let input0 := retainedPrefixRunInput rate rewards C_star C_h j r s hsr control0 x
  let input := retainedPrefixRunInputAtControl rate rewards C_star C_h j r s hsr control0 control x
  let rows0 := (ReferenceGeneratedActivePrefixFactor.splitSource j r control0 x.1).1.2
  let rows := (ReferenceGeneratedActivePrefixFactor.splitSource j r control x.1).1.2
  let state0 := retainedGeneratedActiveSeed rate rewards C_star C_h j r s hsr control0 x
  let state := ReferenceGeneratedActivePrefixFactor.generatedActiveSeed
    rate rewards C_star C_h j r control x.1 x.2.1 s hsr hstart
  have hfactor := ReferenceGeneratedActivePrefixFactor.generatedActivePrefixFactor_control_independent
    rate rewards C_star C_h j r x.1 x.2.1 control0 s (r.val - s) hsr (by omega)
    x.2.2 control control0
  dsimp only at hfactor
  rcases hfactor with ⟨active, hlaunch0, hlaunch, _, hmode, _, _, _⟩
  have hseed0spec := ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
    rate rewards C_star C_h j r control0 x.1 x.2.1 s hsr x.2.2
  have hseedSpec := ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
    rate rewards C_star C_h j r control x.1 x.2.1 s hsr hstart
  have hstate0 : state0 = active := by
    apply Option.some.inj
    exact hseed0spec.1.symm.trans hlaunch0
  have hstate : state = active := by
    apply Option.some.inj
    exact hseedSpec.1.symm.trans hlaunch
  have hinput0 : input0 =
      (⟨(active, (rows0, (j, rewards))), hmode⟩ : ActiveRunInput (p := p) (rate := rate) s) := by
    apply Subtype.ext
    simp [input0, retainedPrefixRunInput, state0, rows0, hstate0]
  have hinput : input =
      (⟨(active, (rows, (j, rewards))), hmode⟩ : ActiveRunInput (p := p) (rate := rate) s) := by
    apply Subtype.ext
    simp [input, retainedPrefixRunInputAtControl, state, rows, hstate]
  have htime (u : Fin p.T) (hu : u.val < r.val) :
      (rows0 j).2 u = (rows j).2 u := by
    have hne : u ≠ r := Fin.ne_of_val_ne (by omega)
    let u' : ReferenceSelectedAffinePairLaw.Other r := ⟨u, hne⟩
    change (((ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p j r).symm
        (control0, x.1)).1.2 j).2 u =
      (((ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p j r).symm
        (control, x.1)).1.2 j).2 u
    exact (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_symm_otherTime
      p j r control0 x.1 u').trans
        (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_symm_otherTime
          p j r control x.1 u').symm
  have hcontrols : ∀ u : Fin p.T, s ≤ u.val → u.val < s + (r.val - s) →
      (rows0 j).2 u = (rows j).2 u := by
    intro u huStart huEnd
    apply htime
    omega
  have hbefore : ∀ u : Fin p.T, u.val < s →
      ((rows0 j).2 u).1 ContinuousControlSlice.Label.prop =
        ((rows j).2 u).1 ContinuousControlSlice.Label.prop := by
    intro u hu
    exact congrArg (fun c : TimeControl p =>
      c.1 ContinuousControlSlice.Label.prop) (htime u (by omega))
  have hobs := runDownObservation_eq_of_temporal_reads active rows0 rows j rewards
    s (r.val - s) (by omega) hmode hcontrols hbefore i
  change runDownObservation (p := p) (rate := rate) s (r.val - s) (by omega) i input0 =
    runDownObservation (p := p) (rate := rate) s (r.val - s) (by omega) i input
  rw [hinput0, hinput]
  exact hobs

/-- The actual retained before-current-pair marker is Borel on the original
launch-start remainder subtype. Its boundary refers to the completed
`alpha - 1` call and ordinary incoming `alpha`; the finite tests are the
literal projections of D's run prefix. -/
theorem measurableSet_retainedPrefixMarker
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (j : Fin (M p)) (r : Fin p.T) (s : ℕ)
    (hs : s < p.T) (hsr : s ≤ r.val) (control0 : TimeControl p)
    (i : Fin (p.m - 1)) (alpha : ℕ) (halpha : s < alpha) (halphaR : alpha ≤ r.val)
    (candidate : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (q : ℕ) (hq : 1 ≤ q) (hqQ : q ≤ AffineBatchDecoder.quota p) :
    MeasurableSet {x : RetainedLaunchStart rate rewards C_star C_h j r s hsr control0 |
      retainedPrefixMarker rate rewards C_star C_h j r s q hs hsr control0 i alpha
        halpha halphaR candidate hq hqQ x} := by
  classical
  let : MeasurableSpace (Option (DownCallCode p)) :=
    LaterAssignmentStartMeasurability.optionMeasurableSpace
  let : MeasurableSpace (Option Bool) :=
    LaterAssignmentStartMeasurability.optionMeasurableSpace
  let : MeasurableSpace (Option (AffineChannelLaw.Word (AffineBatchDecoder.width p))) :=
    CoordinatorUpMeasurability.rawDecoderOutputMeasurableSpace (AffineBatchDecoder.width p)
  let : MeasurableSpace (Option DeclaredFollowerLocalRound.RoundFailure) :=
    LaterAssignmentStartMeasurability.optionMeasurableSpace
  let : MeasurableSpace (Option (DownCutFields p)) :=
    LaterAssignmentStartMeasurability.optionMeasurableSpace
  let input := retainedPrefixRunInput rate rewards C_star C_h j r s hsr control0
  let code := retainedPrefixObservation rate rewards C_star C_h j r s hsr control0 i
  let tests := fun x : RetainedLaunchStart rate rewards C_star C_h j r s hsr control0 =>
    observedTestsFrom rate alpha (r.val - s) (code x)
  let incomingAtAlpha := fun x : RetainedLaunchStart rate rewards C_star C_h j r s hsr control0 =>
    (ReferenceActiveHorizonMeasurability.runOfInput (p := p) (rate := rate)
      s (alpha - s) (by omega) (input x)).finalState.followers i
  let incomingAtR := fun x : RetainedLaunchStart rate rewards C_star C_h j r s hsr control0 =>
    (ReferenceActiveHorizonMeasurability.runOfInput (p := p) (rate := rate)
      s (r.val - s) (by omega) (input x)).finalState.followers i
  let alphaOrdinary := fun x : RetainedLaunchStart rate rewards C_star C_h j r s hsr control0 =>
    (incomingRegisters (FollowerPrepareJointMeasurability.incomingOfLocalConfiguration rate
      (incomingAtAlpha x))).isSome
  let rOrdinary := fun x : RetainedLaunchStart rate rewards C_star C_h j r s hsr control0 =>
    (incomingRegisters (FollowerPrepareJointMeasurability.incomingOfLocalConfiguration rate
      (incomingAtR x))).isSome
  have hinput : Measurable input :=
    measurable_retainedPrefixRunInput rate rewards C_star C_h j r s hsr control0
  have hcode : Measurable code := by
    exact (measurable_runDownObservation (p := p) (rate := rate)
      s (r.val - s) (by omega) i).comp hinput
  have htestsLengthEq : Measurable (fun x => decide ((tests x).length = q - 1)) := by
    exact (measurable_of_countable (fun observed : RunDownObservationCode p rate (r.val - s) =>
      decide ((observedTestsFrom rate alpha (r.val - s) observed).length = q - 1))).comp hcode
  have htestsLengthLt : Measurable (fun x => decide
      ((tests x).length < AffineBatchDecoder.quota p)) := by
    exact (measurable_of_countable (fun observed : RunDownObservationCode p rate (r.val - s) =>
      decide ((observedTestsFrom rate alpha (r.val - s) observed).length <
        AffineBatchDecoder.quota p))).comp hcode
  have htestsGood : Measurable (fun x => decide
      (∀ test ∈ tests x, ExecutedTest.good candidate test)) := by
    exact (measurable_of_countable (fun observed : RunDownObservationCode p rate (r.val - s) =>
      decide (∀ test ∈ observedTestsFrom rate alpha (r.val - s) observed,
        ExecutedTest.good candidate test))).comp hcode
  have hAlphaRegs := measurable_retainedIncomingRegisters rate rewards C_star C_h j r s
    hsr control0 i (alpha - s) (by omega)
  have hRRegs := measurable_retainedIncomingRegisters rate rewards C_star C_h j r s
    hsr control0 i (r.val - s) (by omega)
  have hAlphaOrdinary : Measurable alphaOrdinary :=
    (measurable_of_countable (fun b : Option
      (FollowerDownMeasurability.FollowerStateCode p rate) => b.isSome)).comp hAlphaRegs
  have hROrdinary : Measurable rOrdinary :=
    (measurable_of_countable (fun b : Option
      (FollowerDownMeasurability.FollowerStateCode p rate) => b.isSome)).comp hRRegs
  let completedFlag := fun x : RetainedLaunchStart rate rewards C_star C_h j r s hsr control0 =>
    decide (completedBatchAtRound rate ((code x).2 ⟨alpha - 1 - s, by omega⟩))
  let completedIndex : Fin (r.val - s) := ⟨alpha - 1 - s, by omega⟩
  have hcompletedFlag : Measurable completedFlag := by
    convert (measurable_of_countable (fun round : DownRoundCode p rate =>
      decide (completedBatchAtRound rate round))).comp
        ((measurable_pi_apply completedIndex).comp
          (measurable_snd.comp hcode)) using 1
    rfl
  have hcompletedSet : MeasurableSet {x | completedFlag x = true} :=
    (measurableSet_singleton true).preimage hcompletedFlag
  have hAlphaSet : MeasurableSet {x | alphaOrdinary x = true} :=
    (measurableSet_singleton true).preimage hAlphaOrdinary
  have hRSet : MeasurableSet {x | rOrdinary x = true} :=
    (measurableSet_singleton true).preimage hROrdinary
  have htestsLengthEqSet : MeasurableSet {x | decide ((tests x).length = q - 1) = true} :=
    (measurableSet_singleton true).preimage htestsLengthEq
  have htestsLengthLtSet : MeasurableSet {x | decide
      ((tests x).length < AffineBatchDecoder.quota p) = true} :=
    (measurableSet_singleton true).preimage htestsLengthLt
  have htestsGoodSet : MeasurableSet {x | decide
      (∀ test ∈ tests x, ExecutedTest.good candidate test) = true} :=
    (measurableSet_singleton true).preimage htestsGood
  have hboundarySet : MeasurableSet {x : RetainedLaunchStart
      rate rewards C_star C_h j r s hsr control0 |
      retainedBatchBoundary rate rewards C_star C_h j r s hs hsr control0 i alpha
        halpha halphaR x} := by
    have heq : {x : RetainedLaunchStart rate rewards C_star C_h j r s hsr control0 |
        retainedBatchBoundary rate rewards C_star C_h j r s hs hsr control0 i alpha
          halpha halphaR x} =
        {x | completedFlag x = true} ∩ {x | alphaOrdinary x = true} := by
      ext x
      simp only [Set.mem_ofPred, Set.mem_inter_iff]
      constructor
      · intro h
        refine ⟨?_, ?_⟩
        · simpa [completedFlag, code, retainedPrefixObservation, retainedPrefixRunInput,
            retainedBatchBoundary] using h.1
        · rcases h.2 with ⟨state, memory, hconfiguration⟩
          have hordinary := (localConfiguration_isOrdinary_iff rate
            (incomingAtAlpha x)).mp ⟨state, memory, hconfiguration⟩
          simpa [alphaOrdinary, incomingAtAlpha, input, retainedPrefixRunInput] using hordinary
      · rintro ⟨hcomplete, hordinary⟩
        constructor
        · simpa [completedFlag, code, retainedPrefixObservation, retainedPrefixRunInput,
            retainedBatchBoundary] using hcomplete
        · have hsome :
              (incomingRegisters (FollowerPrepareJointMeasurability.incomingOfLocalConfiguration
                rate (incomingAtAlpha x))).isSome = true := by
            simpa [alphaOrdinary, incomingAtAlpha, input, retainedPrefixRunInput] using hordinary
          exact (localConfiguration_isOrdinary_iff rate (incomingAtAlpha x)).mpr hsome
    rw [heq]
    exact hcompletedSet.inter hAlphaSet
  have hRIncomingSet : MeasurableSet {x : RetainedLaunchStart
      rate rewards C_star C_h j r s hsr control0 |
      ∃ state memory, retainedBatchIncoming rate rewards C_star C_h j r s hs hsr control0
        i alpha halpha halphaR x = .ordinary state memory} := by
    have heq : {x : RetainedLaunchStart rate rewards C_star C_h j r s hsr control0 |
        ∃ state memory, retainedBatchIncoming rate rewards C_star C_h j r s hs hsr control0
          i alpha halpha halphaR x = .ordinary state memory} = {x | rOrdinary x = true} := by
      ext x
      simp only [Set.mem_ofPred]
      rw [localConfiguration_isOrdinary_iff]
      rfl
    rw [heq]
    exact hRSet
  have hprefix (x : RetainedLaunchStart rate rewards C_star C_h j r s hsr control0) :
      retainedBatchPrefix rate rewards C_star C_h j r s hs hsr control0
        i alpha halpha halphaR x = tests x := by
    rfl
  have hmarkerEq :
      {x : RetainedLaunchStart rate rewards C_star C_h j r s hsr control0 |
        retainedPrefixMarker rate rewards C_star C_h j r s q hs hsr control0 i alpha
          halpha halphaR candidate hq hqQ x} =
      {x | retainedBatchBoundary rate rewards C_star C_h j r s hs hsr control0 i alpha
          halpha halphaR x} ∩
      {x | ∃ state memory, retainedBatchIncoming rate rewards C_star C_h j r s hs hsr control0
          i alpha halpha halphaR x = .ordinary state memory} ∩
      {x | (tests x).length = q - 1} ∩
      {x | (tests x).length < AffineBatchDecoder.quota p} ∩
      {x | ∀ test ∈ tests x, ExecutedTest.good candidate test} := by
    ext x
    simp only [Set.mem_ofPred, Set.mem_inter_iff, retainedPrefixMarker]
    rw [← hprefix x]
    simp only [and_assoc]
  rw [hmarkerEq]
  simpa only [Set.inter_assoc, decide_eq_true_eq] using
    hboundarySet.inter (hRIncomingSet.inter
      (htestsLengthEqSet.inter (htestsLengthLtSet.inter htestsGoodSet)))


/-- The original launch membership is preserved under every current-control replacement. -/
theorem retainedAtControl_mem
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (j : Fin (M p)) (r : Fin p.T) (s : ℕ)
    (hsr : s ≤ r.val) (control0 control : TimeControl p)
    (x : RetainedLaunchStart rate rewards C_star C_h j r s hsr control0) :
    x.1 ∈ retainedLaunchStartSet rate rewards C_star C_h j r s control :=
  ⟨x.2.1,
    (ReferenceInitializationControlRemainder.launchStartRemainderEvent_control_independent
      rate rewards C_star C_h j r s x.1 x.2.1 control0 control).mp x.2.2⟩

private theorem selected_splitSource
    (j : Fin (M p)) (r : Fin p.T) (control : TimeControl p)
    (x : ReferenceGeneratedActivePrefixFactor.Remainder p j r)
    (hx : x ∈ fixedControlRemainderStratum p j r) :
    ActualInitializationPhysicalStep.selectedRowIndex p (splitSource j r control x) = j := by
  rw [← sourceCoordinatorIndex_eq_selectedRowIndex]
  exact fixedControlSplit_symm_coordinatorIndex p j r control x hx

private theorem retainedPrefixRunInputAtControl_eq
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (j : Fin (M p)) (r : Fin p.T) (s : ℕ)
    (hsr : s ≤ r.val) (control0 control : TimeControl p)
    (x : RetainedLaunchStart rate rewards C_star C_h j r s hsr control0)
    (y : RetainedLaunchStart rate rewards C_star C_h j r s hsr control)
    (hxy : x.1 = y.1) :
    retainedPrefixRunInputAtControl rate rewards C_star C_h j r s hsr control0 control x =
      retainedPrefixRunInput rate rewards C_star C_h j r s hsr control y := by
  apply Subtype.ext
  simp only [retainedPrefixRunInputAtControl, retainedPrefixRunInput,
    retainedGeneratedActiveSeed, hxy]

/-- The entire incoming state after any prefix ending by r is unchanged.
The generated seed and its mode come from the actual corrected launch. -/
private theorem retainedPrefixFinalState_atControl
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (j : Fin (M p)) (r : Fin p.T) (s : ℕ)
    (hsr : s ≤ r.val) (control0 control : TimeControl p)
    (x : RetainedLaunchStart rate rewards C_star C_h j r s hsr control0)
    (count : ℕ) (hcount : s + count ≤ r.val) :
    (runOfInput (p := p) (rate := rate) s count (by omega)
      (retainedPrefixRunInput rate rewards C_star C_h j r s hsr control0 x)).finalState =
    (runOfInput (p := p) (rate := rate) s count (by omega)
      (retainedPrefixRunInputAtControl rate rewards C_star C_h j r s hsr control0 control x)).finalState := by
  obtain ⟨active, _, _, _, _, _, hstate, _⟩ :=
    generatedActivePrefixFactor_control_independent rate rewards C_star C_h j r x.1 x.2.1
      control0 s count hsr hcount x.2.2 control0 control
  simpa only [generatedActivePrefixFactor, runOfInput, retainedPrefixRunInput,
    retainedGeneratedActiveSeed, retainedPrefixRunInputAtControl,
    selected_splitSource j r control0 x.1 x.2.1,
    selected_splitSource j r control x.1 x.2.1] using hstate

/-- The entire incoming state after any prefix ending by r is unchanged
under replacement of the current whole control. -/
theorem retainedPrefixFinalState_eq_of_remainder_eq
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (j : Fin (M p)) (r : Fin p.T) (s : ℕ)
    (hsr : s ≤ r.val) (control0 control : TimeControl p)
    (x : RetainedLaunchStart rate rewards C_star C_h j r s hsr control0)
    (y : RetainedLaunchStart rate rewards C_star C_h j r s hsr control)
    (hxy : x.1 = y.1) (count : ℕ) (hcount : s + count ≤ r.val) :
    (runOfInput (p := p) (rate := rate) s count (by omega)
      (retainedPrefixRunInput rate rewards C_star C_h j r s hsr control0 x)).finalState =
    (runOfInput (p := p) (rate := rate) s count (by omega)
      (retainedPrefixRunInput rate rewards C_star C_h j r s hsr control y)).finalState := by
  exact (retainedPrefixFinalState_atControl rate rewards C_star C_h j r s hsr control0
    control x count hcount).trans
      (congrArg (fun input : ActiveRunInput (p := p) (rate := rate) s =>
        (runOfInput (p := p) (rate := rate) s count (by omega) input).finalState)
        (retainedPrefixRunInputAtControl_eq rate rewards C_star C_h j r s hsr control0
          control x y hxy))

/-- The finite observation, including comparison presence and the actual
samples, is the same on every replacement fibre of the current whole control. -/
theorem retainedPrefixObservation_eq_of_remainder_eq
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (j : Fin (M p)) (r : Fin p.T) (s : ℕ)
    (hsr : s ≤ r.val) (control0 control : TimeControl p)
    (i : Fin (p.m - 1))
    (x : RetainedLaunchStart rate rewards C_star C_h j r s hsr control0)
    (y : RetainedLaunchStart rate rewards C_star C_h j r s hsr control)
    (hxy : x.1 = y.1) :
    retainedPrefixObservation rate rewards C_star C_h j r s hsr control0 i x =
    retainedPrefixObservation rate rewards C_star C_h j r s hsr control i y := by
  exact (retainedPrefixObservation_control_independent rate rewards C_star C_h j r s hsr
    control0 control i x).trans
      (congrArg (runDownObservation (p := p) (rate := rate) s (r.val - s) (by omega) i)
        (retainedPrefixRunInputAtControl_eq rate rewards C_star C_h j r s hsr control0 control
          x y hxy))

private theorem retainedPrefixMarker_iff
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (j : Fin (M p)) (r : Fin p.T) (s : ℕ)
    (hs : s < p.T) (hsr : s ≤ r.val) (control0 : TimeControl p)
    (i : Fin (p.m - 1)) (alpha : ℕ) (halpha : s < alpha) (halphaR : alpha ≤ r.val)
    (candidate : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (q : ℕ) (hq : 1 ≤ q) (hqQ : q ≤ AffineBatchDecoder.quota p)
    (x : RetainedLaunchStart rate rewards C_star C_h j r s hsr control0) :
    retainedPrefixMarker rate rewards C_star C_h j r s q hs hsr control0 i alpha
      halpha halphaR candidate hq hqQ x ↔
    let input := retainedPrefixRunInput rate rewards C_star C_h j r s hsr control0 x
    let code := runDownObservation (p := p) (rate := rate) s (r.val - s) (by omega) i input
    let tests := observedTestsFrom rate alpha (r.val - s) code
    (completedBatchAtRound rate (code.2 ⟨alpha - 1 - s, by omega⟩) ∧
      ∃ state memory, (runOfInput (p := p) (rate := rate) s (alpha - s) (by omega)
        input).finalState.followers i = .ordinary state memory) ∧
    (∃ state memory, (runOfInput (p := p) (rate := rate) s (r.val - s) (by omega)
      input).finalState.followers i = .ordinary state memory) ∧
    tests.length = q - 1 ∧ tests.length < AffineBatchDecoder.quota p ∧
    ∀ test ∈ tests, ExecutedTest.good candidate test := Iff.rfl

/-- Equality of the literal calendar marker, including the alpha-1 completed
call and the ordinary incoming configurations at both alpha and r. -/
theorem retainedPrefixMarker_control_independent
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (j : Fin (M p)) (r : Fin p.T) (s : ℕ)
    (hs : s < p.T) (hsr : s ≤ r.val) (control0 control : TimeControl p)
    (i : Fin (p.m - 1)) (alpha : ℕ) (halpha : s < alpha) (halphaR : alpha ≤ r.val)
    (candidate : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (q : ℕ) (hq : 1 ≤ q) (hqQ : q ≤ AffineBatchDecoder.quota p)
    (x : RetainedLaunchStart rate rewards C_star C_h j r s hsr control0)
    (y : RetainedLaunchStart rate rewards C_star C_h j r s hsr control)
    (hxy : x.1 = y.1) :
    retainedPrefixMarker rate rewards C_star C_h j r s q hs hsr control0 i alpha
      halpha halphaR candidate hq hqQ x ↔
    retainedPrefixMarker rate rewards C_star C_h j r s q hs hsr control i alpha
      halpha halphaR candidate hq hqQ
      y := by
  have hobs := retainedPrefixObservation_eq_of_remainder_eq rate rewards C_star C_h j r s hsr
    control0 control i x y hxy
  have ha := congrArg (fun state : ReferenceActivePhysicalStep.State p rate => state.followers i)
    (retainedPrefixFinalState_eq_of_remainder_eq rate rewards C_star C_h j r s hsr
      control0 control x y hxy (alpha - s) (by omega))
  have hr := congrArg (fun state : ReferenceActivePhysicalStep.State p rate => state.followers i)
    (retainedPrefixFinalState_eq_of_remainder_eq rate rewards C_star C_h j r s hsr
      control0 control x y hxy (r.val - s) (by omega))
  rw [retainedPrefixMarker_iff, retainedPrefixMarker_iff]
  dsimp only at hobs ⊢
  simp only [retainedPrefixObservation] at hobs
  rw [hobs, ha, hr]

/-- For every replacement whole control, an actual retained input with the
same original remainder exists and gives exactly the same literal D marker. -/
theorem exists_retainedPrefixMarker_replacement
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (j : Fin (M p)) (r : Fin p.T) (s : ℕ)
    (hs : s < p.T) (hsr : s ≤ r.val) (control0 control : TimeControl p)
    (i : Fin (p.m - 1)) (alpha : ℕ) (halpha : s < alpha) (halphaR : alpha ≤ r.val)
    (candidate : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (q : ℕ) (hq : 1 ≤ q) (hqQ : q ≤ AffineBatchDecoder.quota p)
    (x : RetainedLaunchStart rate rewards C_star C_h j r s hsr control0) :
    ∃ h : x.1 ∈ retainedLaunchStartSet rate rewards C_star C_h j r s control,
      (retainedPrefixMarker rate rewards C_star C_h j r s q hs hsr control0 i alpha
          halpha halphaR candidate hq hqQ x ↔
        retainedPrefixMarker rate rewards C_star C_h j r s q hs hsr control i alpha
          halpha halphaR candidate hq hqQ ⟨x.1, h⟩) := by
  have h := retainedAtControl_mem rate rewards C_star C_h j r s hsr control0 control x
  refine ⟨h, ?_⟩
  exact retainedPrefixMarker_control_independent rate rewards C_star C_h j r s hs hsr
    control0 control i alpha halpha halphaR candidate q hq hqQ x ⟨x.1, h⟩ rfl

/-- The physical source prefix marker. This directly runs D's actual source
input over [s,r), tests the completed alpha-1 call, and checks the incoming
ordinary configurations at alpha and r. No retained pullback defines it. -/
def sourcePrefixMarker
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (r : Fin p.T) (s : ℕ) (hs : s < p.T) (hsr : s ≤ r.val)
    (i : Fin (p.m - 1)) (alpha : ℕ) (halpha : s < alpha) (halphaR : alpha ≤ r.val)
    (candidate : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (q : ℕ) (_hq : 1 ≤ q) (_hqQ : q ≤ AffineBatchDecoder.quota p)
    (x : LaunchSource rate rewards C_star C_h s hs) : Prop := by
  let input := generatedSourceRunInput rate rewards C_star C_h s hs x
  let code := runDownObservation (p := p) (rate := rate) s (r.val - s) (by omega) i input
  let tests := observedTestsFrom rate alpha (r.val - s) code
  let incomingAlpha := (runOfInput (p := p) (rate := rate) s (alpha - s)
    (by omega) input).finalState.followers i
  let incomingR := (runOfInput (p := p) (rate := rate) s (r.val - s)
    (by omega) input).finalState.followers i
  exact (completedBatchAtRound rate (code.2 ⟨alpha - 1 - s, by omega⟩) ∧
    ∃ state memory, incomingAlpha = .ordinary state memory) ∧
    (∃ state memory, incomingR = .ordinary state memory) ∧
    tests.length = q - 1 ∧ tests.length < AffineBatchDecoder.quota p ∧
    ∀ test ∈ tests, ExecutedTest.good candidate test

/-- Restoring the actual current control gives the actual source input.
Seed equality follows from two correctedLaunch equalities at the SAME source;
rows, original J, rewards and mode are then restored literally. -/
theorem retainedPrefixRunInput_eq_source
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (j : Fin (M p)) (r : Fin p.T) (s : ℕ)
    (hs : s < p.T) (hsr : s ≤ r.val)
    (z : LaunchSource rate rewards C_star C_h s hs)
    (hselected : ActualInitializationPhysicalStep.selectedRowIndex p z.1 = j)
    (y : RetainedLaunchStart rate rewards C_star C_h j r s hsr
      ((fixedControlSplit p j r z.1).1))
    (hy : y.1 = (fixedControlSplit p j r z.1).2) :
    retainedPrefixRunInput rate rewards C_star C_h j r s hsr
      ((fixedControlSplit p j r z.1).1) y =
      generatedSourceRunInput rate rewards C_star C_h s hs z := by
  let control := (fixedControlSplit p j r z.1).1
  have hsource : splitSource j r control y.1 = z.1 := by
    change (fixedControlSplit p j r).symm (control, y.1) = z.1
    rw [hy]
    exact (fixedControlSplit p j r).symm_apply_apply z.1
  have hseed := (generatedActiveSeed_spec rate rewards C_star C_h j r control y.1
    y.2.1 s hsr y.2.2).1
  rw [hsource] at hseed
  have heq : retainedGeneratedActiveSeed rate rewards C_star C_h j r s hsr control y =
      generatedSourceSeed rate rewards C_star C_h s hs z :=
    Option.some.inj (hseed.symm.trans (generatedSourceSeed_spec rate rewards C_star C_h s hs z).1)
  apply Subtype.ext
  change (retainedGeneratedActiveSeed rate rewards C_star C_h j r s hsr control y,
      ((splitSource j r control y.1).1.2, (j, rewards))) = _
  rw [heq, hsource, ← hselected]
  rfl

/-- Actual-source identity is an output, with only the original J and computed
launch branch selected. It uses the same physical observations and reset. -/
theorem sourcePrefixMarker_eq_retained
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (j : Fin (M p)) (r : Fin p.T) (s : ℕ)
    (hs : s < p.T) (hsr : s ≤ r.val) (control0 : TimeControl p)
    (i : Fin (p.m - 1)) (alpha : ℕ) (halpha : s < alpha) (halphaR : alpha ≤ r.val)
    (candidate : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (q : ℕ) (hq : 1 ≤ q) (hqQ : q ≤ AffineBatchDecoder.quota p)
    (z : LaunchSource rate rewards C_star C_h s hs)
    (hselected : ActualInitializationPhysicalStep.selectedRowIndex p z.1 = j) :
    sourcePrefixMarker rate rewards C_star C_h r s hs hsr i alpha halpha halphaR
      candidate q hq hqQ z ↔
    retainedPrefixMarker rate rewards C_star C_h j r s q hs hsr control0 i alpha
      halpha halphaR candidate hq hqQ
      (retainedLaunchStartInputOfSource rate rewards C_star C_h j r s hsr control0
        z.1 hselected z.2.1 z.2.2) := by
  let x := retainedLaunchStartInputOfSource rate rewards C_star C_h j r s hsr control0
    z.1 hselected z.2.1 z.2.2
  let control := (fixedControlSplit p j r z.1).1
  obtain ⟨hcontrol, hmarker⟩ := exists_retainedPrefixMarker_replacement rate rewards C_star C_h
    j r s hs hsr control0 control i alpha halpha halphaR candidate q hq hqQ x
  let y : RetainedLaunchStart rate rewards C_star C_h j r s hsr control := ⟨x.1, hcontrol⟩
  have hy : y.1 = (fixedControlSplit p j r z.1).2 :=
    retainedLaunchStartInputOfSource_val rate rewards C_star C_h j r s hsr
      control0 z.1 hselected z.2.1 z.2.2
  have hinput := retainedPrefixRunInput_eq_source rate rewards C_star C_h j r s hs hsr
    z hselected y hy
  refine Iff.trans ?_ hmarker.symm
  rw [retainedPrefixMarker_iff]
  dsimp only
  rw [hinput]
  rfl

/-- The literal original-J/computed-launch stratum, with all source rows and
private coordinates still present. -/
def sourcePrefixStratum
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (j : Fin (M p)) (s : ℕ) : Set (SourceInput p) :=
  {z | ActualInitializationPhysicalStep.selectedRowIndex p z = j ∧
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true ∧
    ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed = s}

/-- Exact normalization of the computed source stratum, for every baseline
whole control. No extra source-event normalization is assumed. -/
theorem sourcePrefixStratum_eq_preimage
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (j : Fin (M p)) (r : Fin p.T) (s : ℕ)
    (hsr : s ≤ r.val) (control0 : TimeControl p) :
    sourcePrefixStratum rate rewards C_star C_h j s =
      (fun z => (fixedControlSplit p j r z).2) ⁻¹'
        retainedLaunchStartSet rate rewards C_star C_h j r s control0 := by
  ext z
  constructor
  · rintro ⟨hj, hc, he⟩
    exact retainedLaunchStartInputOfSource_mem rate rewards C_star C_h j r s hsr control0
      z hj hc he
  · rintro ⟨hrem, hstart⟩
    have hj : ActualInitializationPhysicalStep.selectedRowIndex p z = j := hrem
    exact ⟨hj, (ReferenceInitializationControlRemainder.launchStartRemainderEvent_iff_source
      rate rewards C_star C_h j r control0 z hj s hsr).mp hstart⟩

/-- Borel measurability of the literal original-J/computed-launch stratum. -/
theorem measurableSet_sourcePrefixStratum
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (j : Fin (M p)) (r : Fin p.T) (s : ℕ)
    (hsr : s ≤ r.val) (control0 : TimeControl p) :
    MeasurableSet (sourcePrefixStratum rate rewards C_star C_h j s) := by
  rw [sourcePrefixStratum_eq_preimage rate rewards C_star C_h j r s hsr control0]
  exact (measurableSet_retainedLaunchStartSet rate rewards C_star C_h j r s hsr control0).preimage
    (measurable_snd.comp (fixedControlSplit p j r).measurable)

/-- The source event is defined from the physical source formula above, on
its explicit original-J/computed-launch stratum. -/
def sourcePrefixEvent
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (j : Fin (M p)) (r : Fin p.T) (s : ℕ)
    (hs : s < p.T) (hsr : s ≤ r.val)
    (i : Fin (p.m - 1)) (alpha : ℕ) (halpha : s < alpha) (halphaR : alpha ≤ r.val)
    (candidate : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (q : ℕ) (hq : 1 ≤ q) (hqQ : q ≤ AffineBatchDecoder.quota p) : Set (SourceInput p) :=
  {z | ∃ h : z ∈ sourcePrefixStratum rate rewards C_star C_h j s,
    sourcePrefixMarker rate rewards C_star C_h r s hs hsr i alpha halpha halphaR
      candidate q hq hqQ ⟨z, h.2⟩}

/-- A concrete measurable whole-control remainder event, obtained by including
D's literal marker subset into the original remainder. -/
def retainedMarkerRemainderEvent
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (j : Fin (M p)) (r : Fin p.T) (s : ℕ)
    (hs : s < p.T) (hsr : s ≤ r.val) (control0 : TimeControl p)
    (i : Fin (p.m - 1)) (alpha : ℕ) (halpha : s < alpha) (halphaR : alpha ≤ r.val)
    (candidate : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (q : ℕ) (hq : 1 ≤ q) (hqQ : q ≤ AffineBatchDecoder.quota p) :
    Set (ReferenceGeneratedActivePrefixFactor.Remainder p j r) :=
  Subtype.val '' {x : RetainedLaunchStart rate rewards C_star C_h j r s hsr control0 |
    retainedPrefixMarker rate rewards C_star C_h j r s q hs hsr control0 i alpha
      halpha halphaR candidate hq hqQ x}

/-- Pointwise equality of the actual physical source event with its concrete
whole-control remainder pullback. Source identity is proved, not supplied. -/
theorem sourcePrefixEvent_eq_preimage
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (j : Fin (M p)) (r : Fin p.T) (s : ℕ)
    (hs : s < p.T) (hsr : s ≤ r.val) (control0 : TimeControl p)
    (i : Fin (p.m - 1)) (alpha : ℕ) (halpha : s < alpha) (halphaR : alpha ≤ r.val)
    (candidate : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (q : ℕ) (hq : 1 ≤ q) (hqQ : q ≤ AffineBatchDecoder.quota p) :
    sourcePrefixEvent rate rewards C_star C_h j r s hs hsr i alpha halpha halphaR
      candidate q hq hqQ =
    (fun z => (fixedControlSplit p j r z).2) ⁻¹'
      retainedMarkerRemainderEvent rate rewards C_star C_h j r s hs hsr control0
        i alpha halpha halphaR candidate q hq hqQ := by
  ext z
  constructor
  · rintro ⟨hz, hmarker⟩
    let x := retainedLaunchStartInputOfSource rate rewards C_star C_h j r s hsr control0
      z hz.1 hz.2.1 hz.2.2
    refine ⟨x, ?_, rfl⟩
    exact (sourcePrefixMarker_eq_retained rate rewards C_star C_h j r s hs hsr control0
      i alpha halpha halphaR candidate q hq hqQ ⟨z, hz.2⟩ hz.1).mp hmarker
  · rintro ⟨x, hmarker, hx⟩
    have hx' : x.1 = (fixedControlSplit p j r z).2 := hx
    have hmem : (fixedControlSplit p j r z).2 ∈
        retainedLaunchStartSet rate rewards C_star C_h j r s control0 :=
      Eq.mp (congrArg (fun v : ReferenceGeneratedActivePrefixFactor.Remainder p j r =>
        v ∈ retainedLaunchStartSet rate rewards C_star C_h j r s control0) hx') x.2
    have hz : z ∈ sourcePrefixStratum rate rewards C_star C_h j s := by
      rw [sourcePrefixStratum_eq_preimage rate rewards C_star C_h j r s hsr control0]
      exact hmem
    refine ⟨hz, (sourcePrefixMarker_eq_retained rate rewards C_star C_h j r s hs hsr control0
      i alpha halpha halphaR candidate q hq hqQ ⟨z, hz.2⟩ hz.1).mpr ?_⟩
    have heq : retainedLaunchStartInputOfSource rate rewards C_star C_h j r s hsr control0
        z hz.1 hz.2.1 hz.2.2 = x := Subtype.ext hx'.symm
    rw [heq]
    exact hmarker

/-- Borel measurability on the original ambient whole-control remainder. -/
theorem measurableSet_retainedMarkerRemainderEvent
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (j : Fin (M p)) (r : Fin p.T) (s : ℕ)
    (hs : s < p.T) (hsr : s ≤ r.val) (control0 : TimeControl p)
    (i : Fin (p.m - 1)) (alpha : ℕ) (halpha : s < alpha) (halphaR : alpha ≤ r.val)
    (candidate : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (q : ℕ) (hq : 1 ≤ q) (hqQ : q ≤ AffineBatchDecoder.quota p) :
    MeasurableSet (retainedMarkerRemainderEvent rate rewards C_star C_h j r s hs hsr control0
      i alpha halpha halphaR candidate q hq hqQ) :=
  (measurableSet_retainedLaunchStartSet rate rewards C_star C_h j r s hsr control0).subtype_image
    (measurableSet_retainedPrefixMarker rate rewards C_star C_h j r s hs hsr control0
      i alpha halpha halphaR candidate q hq hqQ)

/-- Borel measurability of the ambient restricted physical source event. -/
theorem measurableSet_sourcePrefixEvent
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (j : Fin (M p)) (r : Fin p.T) (s : ℕ)
    (hs : s < p.T) (hsr : s ≤ r.val) (control0 : TimeControl p)
    (i : Fin (p.m - 1)) (alpha : ℕ) (halpha : s < alpha) (halphaR : alpha ≤ r.val)
    (candidate : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (q : ℕ) (hq : 1 ≤ q) (hqQ : q ≤ AffineBatchDecoder.quota p) :
    MeasurableSet (sourcePrefixEvent rate rewards C_star C_h j r s hs hsr
      i alpha halpha halphaR candidate q hq hqQ) := by
  rw [sourcePrefixEvent_eq_preimage rate rewards C_star C_h j r s hs hsr control0]
  exact (measurableSet_retainedMarkerRemainderEvent rate rewards C_star C_h j r s hs hsr control0
    i alpha halpha halphaR candidate q hq hqQ).preimage
      (measurable_snd.comp (fixedControlSplit p j r).measurable)

/-- The literal marker is Borel on the fixed original-J/computed-launch
source subtype, with its inherited continuous measurable space. -/
theorem measurableSet_sourcePrefixMarker
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (j : Fin (M p)) (r : Fin p.T) (s : ℕ)
    (hs : s < p.T) (hsr : s ≤ r.val) (control0 : TimeControl p)
    (i : Fin (p.m - 1)) (alpha : ℕ) (halpha : s < alpha) (halphaR : alpha ≤ r.val)
    (candidate : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (q : ℕ) (hq : 1 ≤ q) (hqQ : q ≤ AffineBatchDecoder.quota p) :
    MeasurableSet {z : sourcePrefixStratum rate rewards C_star C_h j s |
      sourcePrefixMarker rate rewards C_star C_h r s hs hsr i alpha halpha halphaR
        candidate q hq hqQ ⟨z.1, z.2.2⟩} := by
  have heq : {z : sourcePrefixStratum rate rewards C_star C_h j s |
      sourcePrefixMarker rate rewards C_star C_h r s hs hsr i alpha halpha halphaR
        candidate q hq hqQ ⟨z.1, z.2.2⟩} =
      Subtype.val ⁻¹' sourcePrefixEvent rate rewards C_star C_h j r s hs hsr
        i alpha halpha halphaR candidate q hq hqQ := by
    ext z
    exact ⟨fun h => ⟨z.2, h⟩, fun ⟨_, h⟩ => h⟩
  rw [heq]
  exact (measurableSet_sourcePrefixEvent rate rewards C_star C_h j r s hs hsr control0
    i alpha halpha halphaR candidate q hq hqQ).preimage measurable_subtype_coe

/-- Forget only the other current controls from the original pair remainder.
All IDs, whole off-current rows/times and ALL private coordinates remain. -/
def pairToControlRemainder (j : Fin (M p)) (r : Fin p.T) (i : Fin (p.m - 1))
    (v : ReferenceSelectedAffinePairLaw.Remainder p j r (0, i)) :
    ReferenceGeneratedActivePrefixFactor.Remainder p j r :=
  ((v.1.1, ((v.1.2.1.1, v.1.2.1.2.2), v.1.2.2)), v.2)

theorem measurable_pairToControlRemainder
    (j : Fin (M p)) (r : Fin p.T) (i : Fin (p.m - 1)) :
    Measurable (pairToControlRemainder j r i) :=
  ((measurable_fst.comp measurable_fst).prodMk
    (((measurable_fst.comp (measurable_fst.comp (measurable_snd.comp measurable_fst))).prodMk
      (measurable_snd.comp (measurable_snd.comp
        (measurable_fst.comp (measurable_snd.comp measurable_fst))))).prodMk
      (measurable_snd.comp (measurable_snd.comp measurable_fst)))).prodMk measurable_snd

/-- The projection composes the two original source splits pointwise. -/
theorem pairToControlRemainder_source
    (j : Fin (M p)) (r : Fin p.T) (i : Fin (p.m - 1)) (z : SourceInput p) :
    pairToControlRemainder j r i ((ReferenceSelectedAffinePairLaw.fixedPairSplit p j r (0, i) z).2) =
      (fixedControlSplit p j r z).2 := rfl

/-- Concrete C_I for the original current focal-pair split. Other current
controls remain fixed on each fibre of this original split. -/
def prefixPairCylinder
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (j : Fin (M p)) (r : Fin p.T) (s : ℕ)
    (hs : s < p.T) (hsr : s ≤ r.val) (control0 : TimeControl p)
    (i : Fin (p.m - 1)) (alpha : ℕ) (halpha : s < alpha) (halphaR : alpha ≤ r.val)
    (candidate : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (q : ℕ) (hq : 1 ≤ q) (hqQ : q ≤ AffineBatchDecoder.quota p) :
    Set (ReferenceSelectedAffinePairLaw.Remainder p j r (0, i)) :=
  pairToControlRemainder j r i ⁻¹'
    retainedMarkerRemainderEvent rate rewards C_star C_h j r s hs hsr control0
      i alpha halpha halphaR candidate q hq hqQ

/-- The concrete actual pair-remainder cylinder is measurable. -/
theorem measurableSet_prefixPairCylinder
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (j : Fin (M p)) (r : Fin p.T) (s : ℕ)
    (hs : s < p.T) (hsr : s ≤ r.val) (control0 : TimeControl p)
    (i : Fin (p.m - 1)) (alpha : ℕ) (halpha : s < alpha) (halphaR : alpha ≤ r.val)
    (candidate : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (q : ℕ) (hq : 1 ≤ q) (hqQ : q ≤ AffineBatchDecoder.quota p) :
    MeasurableSet (prefixPairCylinder rate rewards C_star C_h j r s hs hsr control0
      i alpha halpha halphaR candidate q hq hqQ) :=
  (measurableSet_retainedMarkerRemainderEvent rate rewards C_star C_h j r s hs hsr control0
    i alpha halpha halphaR candidate q hq hqQ).preimage (measurable_pairToControlRemainder j r i)

/-- Pointwise original-source identity for the concrete C_I; no current
focal pair is read by the retained condition. -/
theorem sourcePrefixEvent_eq_pairCylinder
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (j : Fin (M p)) (r : Fin p.T) (s : ℕ)
    (hs : s < p.T) (hsr : s ≤ r.val) (control0 : TimeControl p)
    (i : Fin (p.m - 1)) (alpha : ℕ) (halpha : s < alpha) (halphaR : alpha ≤ r.val)
    (candidate : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (q : ℕ) (hq : 1 ≤ q) (hqQ : q ≤ AffineBatchDecoder.quota p) :
    sourcePrefixEvent rate rewards C_star C_h j r s hs hsr i alpha halpha halphaR
      candidate q hq hqQ =
    (fun z => (ReferenceSelectedAffinePairLaw.fixedPairSplit p j r (0, i) z).2) ⁻¹'
      prefixPairCylinder rate rewards C_star C_h j r s hs hsr control0
        i alpha halpha halphaR candidate q hq hqQ := by
  rw [sourcePrefixEvent_eq_preimage rate rewards C_star C_h j r s hs hsr control0]
  rfl

/-- Z's original pair API additionally selects the actual current DOWN
channel. This literal normalization adds only that computed selector. -/
theorem sourcePrefixEvent_inter_selector_eq_stratumEvent
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (j : Fin (M p)) (r : Fin p.T) (s : ℕ)
    (hs : s < p.T) (hsr : s ≤ r.val) (control0 : TimeControl p)
    (i : Fin (p.m - 1)) (alpha : ℕ) (halpha : s < alpha) (halphaR : alpha ≤ r.val)
    (candidate : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (q : ℕ) (hq : 1 ≤ q) (hqQ : q ≤ AffineBatchDecoder.quota p) :
    sourcePrefixEvent rate rewards C_star C_h j r s hs hsr i alpha halpha halphaR
        candidate q hq hqQ ∩
      {z | ReferenceSelectedAffinePairLaw.selector p r z = (j, some (0, i))} =
    ReferenceSelectedAffinePairLaw.stratumEvent p j r (0, i)
      (prefixPairCylinder rate rewards C_star C_h j r s hs hsr control0
        i alpha halpha halphaR candidate q hq hqQ) := by
  rw [sourcePrefixEvent_eq_pairCylinder rate rewards C_star C_h j r s hs hsr control0]
  ext z
  exact and_comm


/-- The original pair inverse has the full-pair times C_I preimage, pointwise. -/
theorem sourcePrefixEvent_pair_preimage
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (j : Fin (M p)) (r : Fin p.T) (s : ℕ)
    (hs : s < p.T) (hsr : s ≤ r.val) (control0 : TimeControl p)
    (i : Fin (p.m - 1)) (alpha : ℕ) (halpha : s < alpha) (halphaR : alpha ≤ r.val)
    (candidate : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (q : ℕ) (hq : 1 ≤ q) (hqQ : q ≤ AffineBatchDecoder.quota p) :
    (ReferenceSelectedAffinePairLaw.fixedPairSplit p j r (0, i)).symm ⁻¹'
      sourcePrefixEvent rate rewards C_star C_h j r s hs hsr
        i alpha halpha halphaR candidate q hq hqQ =
    Set.univ ×ˢ prefixPairCylinder rate rewards C_star C_h j r s hs hsr control0
      i alpha halpha halphaR candidate q hq hqQ := by
  rw [sourcePrefixEvent_eq_pairCylinder rate rewards C_star C_h j r s hs hsr control0]
  ext v
  simp only [Set.mem_preimage, MeasurableEquiv.apply_symm_apply, Set.mem_prod,
    Set.mem_univ, true_and]

/-- The additional computed selector required by Z's stratum API is Borel
with this concrete C_I, without a generic marker-measurability premise. -/
theorem measurableSet_sourcePrefixEvent_inter_selector
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (j : Fin (M p)) (r : Fin p.T) (s : ℕ)
    (hs : s < p.T) (hsr : s ≤ r.val) (control0 : TimeControl p)
    (i : Fin (p.m - 1)) (alpha : ℕ) (halpha : s < alpha) (halphaR : alpha ≤ r.val)
    (candidate : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (q : ℕ) (hq : 1 ≤ q) (hqQ : q ≤ AffineBatchDecoder.quota p) :
    MeasurableSet (sourcePrefixEvent rate rewards C_star C_h j r s hs hsr
        i alpha halpha halphaR candidate q hq hqQ ∩
      {z | ReferenceSelectedAffinePairLaw.selector p r z = (j, some (0, i))}) := by
  rw [sourcePrefixEvent_inter_selector_eq_stratumEvent rate rewards C_star C_h j r s hs hsr control0]
  exact ReferenceSelectedAffinePairLaw.measurableSet_stratumEvent p j r (0, i) _
    (measurableSet_prefixPairCylinder rate rewards C_star C_h j r s hs hsr control0
      i alpha halpha halphaR candidate q hq hqQ)

end Bandits.Support.ReferenceGeneratedDownPrefixEvent

end
