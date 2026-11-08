/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveReleaseSourceCylinder

/-!
# Original-source first-live release cylinders

Sources: `sources/zip4/manuscript/05_binary_transport.tex:74-124,293-345`,
`sources/zip4/manuscript/06_interruptions.tex:435-492`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-79`.

The remainder measure is unnormalized. All rewards, rows, private arrays and
initialization constants remain those of the original source. This is an
internal cylinder law, not a conditional law on the authentic source history
or a stopped quota, cost, or regret theorem. The next consumer is authentic
source-history conditional release service; the stopped pending quota/cost
argument also requires its remaining history and stopping producers.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open scoped Classical ENNReal

namespace Bandits.Support.ReferenceFirstLiveReleaseCylinderIntegral

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev TimeControl := ContinuousLearningRows.TimeControl
abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput

-- Only the finite optional cutoff endpoint is discrete here.
local instance choiceCutoffMeasurableSpace {p : Parameters} :
    MeasurableSpace (Option (CoordinatorLocalArmChoice.Cutoff p)) := ⊤

variable {p : Parameters} (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (ConstructorDimensions.M p)) (t : Fin p.T)
    (s : ℕ) (hs : s ≤ t.val) (control0 : TimeControl p)

local notation "X" =>
  ReferenceRetainedBoundaryMeasurability.RetainedLaunchStart rate rewards C_star C_h q t s hs control0
local notation "β" =>
  ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary rate rewards C_star C_h q t s hs control0
local notation "W" =>
  ReferenceFirstLiveReleaseControlTransport.retainedWindow (rate := rate) rewards C_star C_h q t s hs control0
local notation "S" => ReferenceFirstLiveReleaseSourceCylinder.selectedEmptyPendingRemainder (rate := rate)
  rewards C_star C_h q t s hs control0
local notation "μC" =>
  ReferenceRetainedSourceCoupling.retainedRemainderMeasure rate rewards C_star C_h q t s hs control0
local notation "controlLaw" => ContinuousLearningRows.timeControlLaw p
local notation "sourceMap" =>
  ReferenceRetainedSourceCoupling.retainedSourceMap rate rewards C_star C_h q t s hs control0

/-- The same literal physical flag, with `true` selecting UP and `false` DATA. -/
def physicalFlag (up : Bool) (payload : ReferenceActivePhysicalStep.Payload rate)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) (i : Fin (p.m - 1)) : Bool :=
  if up then ReferencePhysicalReleaseQuota.upFlag payload record i
  else ReferencePhysicalReleaseQuota.dataFlag payload record i

/-- Replace exactly the current whole control in the actual incoming input. -/
def currentInput (x : X) (u : TimeControl p) : ReferenceActivePhysicalStep.RoundInput p rate :=
  ReferenceLaterOptionalControlResampling.withControl (β x) u

private theorem measurable_currentInput :
    Measurable (fun z : X × TimeControl p =>
      currentInput rate rewards C_star C_h q t s hs control0 z.1 z.2) := by
  have hb : Measurable (fun z : X × TimeControl p => β z.1) :=
    (ReferenceRetainedBoundaryMeasurability.measurable_retainedIncomingBoundary
      rate rewards C_star C_h q t s hs control0).comp measurable_fst
  have hrows := ReferenceActivePhysicalStepMeasurability.measurable_rows.comp hb
  have hrow := ReferenceActivePhysicalStepMeasurability.measurable_row.comp hb
  have hnewrow := (measurable_fst.comp hrow).prodMk
    ((measurable_update' (a := t)).comp ((measurable_snd.comp hrow).prodMk measurable_snd))
  have hnewrows := (measurable_update' (a := q)).comp (hrows.prodMk hnewrow)
  apply measurable_comap_iff.mpr
  apply Measurable.subtype_mk
  convert (ReferenceActivePhysicalStepMeasurability.measurable_state.comp hb).prodMk
    (hnewrows.prodMk ((measurable_const (a := q)).prodMk
      ((measurable_const (a := t)).prodMk (measurable_const (a := rewards))))) using 1
  funext z
  simp only [currentInput, ReferenceLaterOptionalControlResampling.withControl, Function.comp_apply,
    ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary_selected_eq_q,
    ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary_time]
  rfl

/-- The actual optional baseline payload. Absence remains absence. -/
def baselinePayload (x : X) : Option (ReferenceActivePhysicalStep.Payload rate) :=
  (ReferenceActivePhysicalStep.dispatch
    (currentInput rate rewards C_star C_h q t s hs control0 x control0)).selection.map
    (fun selected => selected.view.payload)

private theorem measurable_baselinePayload :
    Measurable (baselinePayload rate rewards C_star C_h q t s hs control0) := by
  have hin := (measurable_currentInput rate rewards C_star C_h q t s hs control0).comp
    (measurable_id.prodMk (measurable_const (a := control0)))
  have hcode := measurable_fst.comp (measurable_fst.comp
    (ReferenceActiveStepCompositionMeasurability.measurable_wholeStepCode.comp hin))
  have hview : Measurable (fun view : ReferenceDownReception.ChoiceTimeView p rate.eta =>
      view.payload) := measurable_fst.comp
    (show Measurable (ReferenceDownReceptionMeasurability.choiceTimeViewObservation
      (p := p) (rate := rate)) from comap_measurable _)
  have hmap := LaterAssignmentFullOutputMeasurability.measurable_optionMap
    (fun selection : ReferenceLiveDispatchOutputMeasurability.SelectionData p rate => selection.1.payload)
    (hview.comp measurable_fst) _ hcode
  convert hmap using 1
  funext x
  change baselinePayload rate rewards C_star C_h q t s hs control0 x =
    ((ReferenceActiveStepCompositionMeasurability.wholeStepCode
      (currentInput rate rewards C_star C_h q t s hs control0 x control0)).1.1).map
        (fun selection => selection.1.payload)
  rw [(ReferenceActiveStepCompositionMeasurability.wholeStepCode_front _).1]
  simp only [baselinePayload, Option.map_map, ReferenceLiveDispatchOutputMeasurability.encodeSelection,
    Function.comp_def]

private theorem record_eq (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) :
    record = ReferencePhysicalReleaseObservability.recordOfInput record.input := by
  rcases record with ⟨input, output, hout⟩
  cases hout
  rfl

/-- A literal joint event: the computed branch, its actual baseline optional
selection, and the same physical current record in the replacement window. -/
def jointEvent (up : Bool) (i : Fin (p.m - 1)) : Set (X × TimeControl p) :=
  {z | z.1 ∈ S i ∧ ∃ hn : t.val - s < (W z.1 control0).length,
    ∃ selected0 : ReferenceActivePhysicalStep.Selection (W z.1 control0)[t.val - s].input,
      (W z.1 control0)[t.val - s].output.preparation.coordinator.selection = some selected0 ∧
      ∃ hu : t.val - s < (W z.1 z.2).length,
        physicalFlag rate up selected0.view.payload ((W z.1 z.2)[t.val - s]'hu) i = true}

private theorem baselinePayload_eq
    (i : Fin (p.m - 1)) (x : X)
    (hn : t.val - s < (W x control0).length)
    (selected0 : ReferenceActivePhysicalStep.Selection (W x control0)[t.val - s].input)
    (hselected : (W x control0)[t.val - s].output.preparation.coordinator.selection = some selected0)
    (hempty : selected0.view.pendingAtChoice = ∅)
    (hi : i ∈ ReferencePhysicalReleaseQuota.pendingAtStart selected0.view.payload
      (β x).time (β x).state) :
    baselinePayload rate rewards C_star C_h q t s hs control0 x = some selected0.view.payload := by
  obtain ⟨_, _, _, _, _, hcontrols⟩ := ReferenceFirstLiveReleaseSliceMass.retained_first_live_release_all_controls
    rewards C_star C_h q t s hs control0 x hn selected0 hselected hempty i hi
  obtain ⟨hu, selectedU, hinput, _, _, hprep, _, hpayload, _⟩ := hcontrols control0
  unfold baselinePayload currentInput
  rw [← hinput]
  change (ReferenceActivePhysicalStep.prepare (W x control0)[t.val - s].input).coordinator.selection.map
    (fun selected => selected.view.payload) = _
  rw [hprep, Option.map_some, hpayload]

private def optionFlag (up : Bool) (i : Fin (p.m - 1))
    (z : Option (ReferenceActivePhysicalStep.Payload rate) × ReferenceActivePhysicalStep.RoundInput p rate) : Bool :=
  match z.1 with
  | none => false
  | some payload => physicalFlag rate up payload (ReferencePhysicalReleaseObservability.recordOfInput z.2) i

private theorem measurable_optionFlag (up : Bool) (i : Fin (p.m - 1)) :
    Measurable (optionFlag rate up i) := by
  have hflag : Measurable (fun z : ReferenceActivePhysicalStep.Payload rate ×
      ReferenceActivePhysicalStep.RoundInput p rate =>
      physicalFlag rate up z.1 (ReferencePhysicalReleaseObservability.recordOfInput z.2) i) := by
    cases up
    · exact ReferencePhysicalReleaseObservability.measurable_dataFlag i
    · exact ReferencePhysicalReleaseObservability.measurable_upFlag i
  let e : (Option (ReferenceActivePhysicalStep.Payload rate) × ReferenceActivePhysicalStep.RoundInput p rate) ≃ᵐ
      ((ReferenceActivePhysicalStep.Payload rate × ReferenceActivePhysicalStep.RoundInput p rate) ⊕
        (PUnit × ReferenceActivePhysicalStep.RoundInput p rate)) :=
    (MeasurableEquiv.prodCongr
      (show Option (ReferenceActivePhysicalStep.Payload rate) ≃ᵐ ReferenceActivePhysicalStep.Payload rate ⊕ PUnit from
        { toEquiv := Equiv.optionEquivSumPUnit _
          measurable_toFun := comap_measurable _
          measurable_invFun := by
            rw [measurable_comap_iff]
            exact measurable_id })
      (MeasurableEquiv.refl _)).trans (MeasurableEquiv.sumProdDistrib _ _ _)
  have hm := (Measurable.sumElim hflag (measurable_const (a := false))).comp e.measurable_toFun
  convert hm using 1
  funext z
  rcases z with ⟨payload, input⟩
  cases payload <;> rfl

private theorem jointEvent_iff (up : Bool) (i : Fin (p.m - 1))
    (x : X) (u : TimeControl p) :
    (x, u) ∈ jointEvent rate rewards C_star C_h q t s hs control0 up i ↔
      x ∈ S i ∧ optionFlag rate up i
        (baselinePayload rate rewards C_star C_h q t s hs control0 x,
          currentInput rate rewards C_star C_h q t s hs control0 x u) = true := by
  constructor
  · rintro ⟨hx, hn, selected0, hselected, hu, hflag⟩
    obtain ⟨hn', selected', hs', hempty, hi⟩ := (show x ∈ S i from hx)
    have heq := ReferenceFirstLiveReleaseSourceCylinder.selectedEmptyPendingRemainder_selection_unique
      rewards C_star C_h q t s hs control0 i x hn hn' selected0 selected' hselected hs'
    subst selected'
    have hp := baselinePayload_eq rate rewards C_star C_h q t s hs control0
      i x hn selected0 hselected hempty hi
    obtain ⟨_, _, _, _, _, hcontrols⟩ := ReferenceFirstLiveReleaseSliceMass.retained_first_live_release_all_controls
      rewards C_star C_h q t s hs control0 x hn selected0 hselected hempty i hi
    obtain ⟨hu', _, hinput, _⟩ := hcontrols u
    change (W x u)[t.val - s].input =
      currentInput rate rewards C_star C_h q t s hs control0 x u at hinput
    refine ⟨hx, ?_⟩
    rw [hp]
    change physicalFlag rate up selected0.view.payload
      (ReferencePhysicalReleaseObservability.recordOfInput
        (currentInput rate rewards C_star C_h q t s hs control0 x u)) i = true
    rw [← hinput, ← record_eq rate ((W x u)[t.val - s]'hu')]
    exact hflag
  · rintro ⟨hx, hflag⟩
    obtain ⟨hn, selected0, hselected, hempty, hi⟩ := (show x ∈ S i from hx)
    have hp := baselinePayload_eq rate rewards C_star C_h q t s hs control0
      i x hn selected0 hselected hempty hi
    obtain ⟨_, _, _, _, _, hcontrols⟩ := ReferenceFirstLiveReleaseSliceMass.retained_first_live_release_all_controls
      rewards C_star C_h q t s hs control0 x hn selected0 hselected hempty i hi
    obtain ⟨hu, _, hinput, _⟩ := hcontrols u
    change (W x u)[t.val - s].input =
      currentInput rate rewards C_star C_h q t s hs control0 x u at hinput
    refine ⟨hx, hn, selected0, hselected, hu, ?_⟩
    rw [hp] at hflag
    change physicalFlag rate up selected0.view.payload
      (ReferencePhysicalReleaseObservability.recordOfInput
        (currentInput rate rewards C_star C_h q t s hs control0 x u)) i = true at hflag
    rw [← hinput, ← record_eq rate ((W x u)[t.val - s]'hu)] at hflag
    exact hflag

/-- Joint Borel measurability uses the actual optional selection and the joint
payload/input physical flag, retaining continuous payload and control fibres. -/
theorem measurableSet_jointEvent (up : Bool) (i : Fin (p.m - 1)) :
    MeasurableSet (jointEvent rate rewards C_star C_h q t s hs control0 up i) := by
  have hflag := (measurable_optionFlag rate up i).comp
    (((measurable_baselinePayload rate rewards C_star C_h q t s hs control0).comp
      measurable_fst).prodMk (measurable_currentInput rate rewards C_star C_h q t s hs control0))
  have hset := ((ReferenceFirstLiveReleaseSourceCylinder.measurableSet_selectedEmptyPendingRemainder
    rewards C_star C_h q t s hs control0 i).preimage measurable_fst).inter
      ((measurableSet_singleton true).preimage hflag)
  convert hset using 1
  ext z
  exact jointEvent_iff rate rewards C_star C_h q t s hs control0 up i z.1 z.2

/-- Sections are precisely the accepted actual-window events, for ANY actual
baseline selector. C's uniqueness removes both proof-index and witness choices. -/
theorem jointEvent_section
    (i : Fin (p.m - 1)) (x : X)
    (hn : t.val - s < (W x control0).length)
    (selected0 : ReferenceActivePhysicalStep.Selection (W x control0)[t.val - s].input)
    (hselected : (W x control0)[t.val - s].output.preparation.coordinator.selection = some selected0)
    (hempty : selected0.view.pendingAtChoice = ∅)
    (hi : i ∈ ReferencePhysicalReleaseQuota.pendingAtStart selected0.view.payload
      (β x).time (β x).state) :
    (Prod.mk x ⁻¹' jointEvent rate rewards C_star C_h q t s hs control0 true i =
      ReferenceFirstLiveReleaseSliceMass.retainedUpFlagEvent rewards C_star C_h q t s hs control0 x hn selected0 i) ∧
    (Prod.mk x ⁻¹' jointEvent rate rewards C_star C_h q t s hs control0 false i =
      ReferenceFirstLiveReleaseSliceMass.retainedDataFlagEvent
        rewards C_star C_h q t s hs control0 x hn selected0 i) := by
  have h (up : Bool) : ∀ u,
      (x, u) ∈ jointEvent rate rewards C_star C_h q t s hs control0 up i ↔
        ∃ hu : t.val - s < (W x u).length,
          physicalFlag rate up selected0.view.payload ((W x u)[t.val - s]'hu) i = true := by
    intro u
    constructor
    · rintro ⟨_, hn', selected', hs', hu, hflag⟩
      have heq := ReferenceFirstLiveReleaseSourceCylinder.selectedEmptyPendingRemainder_selection_unique
        rewards C_star C_h q t s hs control0 i x hn' hn selected' selected0 hs' hselected
      subst selected'
      exact ⟨hu, hflag⟩
    · rintro ⟨hu, hflag⟩
      exact ⟨⟨hn, selected0, hselected, hempty, hi⟩, hn, selected0, hselected, hu, hflag⟩
  constructor
  · ext u
    exact h true u
  · ext u
    exact h false u

/-- The reconstructed next input restores all source rows and the original J,
not merely the currently inspected scalar coordinates. -/
theorem currentInput_eq_next (x : X) (u : TimeControl p) :
    currentInput rate rewards C_star C_h q t s hs control0 x u =
      ReferenceRetainedBoundaryMeasurability.retainedGeneratedNextInput
        rate rewards C_star C_h q t s hs control0 x u := by
  let z0 := ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.1
  have hindex : ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p z0 = q :=
    ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_symm_coordinatorIndex
      p q t control0 x.1 x.2.1
  have hreplace : ReferenceGeneratedActivePrefixFactor.splitSource q t u x.1 =
      ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z0 u := by
    have h := ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_replaceSourceControl
      p q t z0 u hindex
    have hsplit : (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t z0).2 = x.1 :=
      congrArg Prod.snd ((ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).apply_symm_apply
        (control0, x.1))
    rw [hsplit] at h
    exact h
  rw [ReferenceRetainedBoundaryMeasurability.retainedGeneratedNextInput_eq_roundInputAtSource,
    hreplace]
  change currentInput rate rewards C_star C_h q t s hs control0 x u =
    ReferenceFixedTimeSourceControlCoupling.roundInputAtSource p rate (β x)
      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p (β x).time z0 u)
  rw [ReferenceFixedTimeSourceControlCoupling.roundInputAtSource_replaceSourceControl]
  rfl

/-- The actual corrected initialization seed of an ORIGINAL source. -/
def originalSeed (z : SourceInput p)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true) :
    ReferenceActivePhysicalStep.State p rate :=
  (ReferenceCorrectedInitializationLaunch.correctedLaunch rate z rewards C_star C_h).get
    ((ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
      rate z rewards C_star C_h).2 hc)

theorem originalSeed_active (z : SourceInput p)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (he : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed = s) :
    ReferenceActivePhysicalHorizon.allActiveAtStart
      (originalSeed rate rewards C_star C_h z hc) s := by
  obtain ⟨active, hactive, hmode⟩ :=
    ReferenceCorrectedInitializationLaunch.correctedLaunch_all_active_at_start
      rate z rewards C_star C_h hc
  have hseed : originalSeed rate rewards C_star C_h z hc = active := by
    unfold originalSeed
    simp only [hactive, Option.get_some]
  rw [hseed, ← he]
  exact hmode

/-- The existing run from that source's actual corrected seed, with its whole
original rows, original private selected index, and the same rewards. -/
def originalRun (z : SourceInput p)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (he : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed = s)
    (count : ℕ) (hspan : s + count ≤ p.T) :=
  ReferenceActivePhysicalHorizon.run (originalSeed rate rewards C_star C_h z hc)
    z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s count hspan
    (originalSeed_active rate rewards C_star C_h s z hc he)

/-- Original first-live window through the WHOLE remaining physical horizon. -/
def originalWindow (hsT : s ≤ p.T) (z : SourceInput p)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (he : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed = s) :=
  ReferenceFirstLiveConfirmationHistory.firstLiveWindow
    (originalRun rate rewards C_star C_h s z hc he (p.T - s) (Nat.add_sub_of_le hsT).le).records

private theorem takeWhile_prefix {α : Type*} (test : α → Bool) {a b : List α}
    (hab : a.IsPrefix b) : (a.takeWhile test).IsPrefix (b.takeWhile test) := by
  obtain ⟨tail, rfl⟩ := hab
  rw [List.takeWhile_append]
  split
  · exact (List.takeWhile_prefix _).trans (List.prefix_append _ _)
  · exact ⟨[], List.append_nil _⟩

private theorem retained_source_records
    (z : SourceInput p)
    (hj : ActualInitializationPhysicalStep.selectedRowIndex p z = q)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (he : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed = s) :
    let x := ReferenceRetainedBoundaryMeasurability.retainedLaunchStartInputOfSource
      rate rewards C_star C_h q t s hs control0 z hj hc he
    (ReferenceFirstLiveReleaseControlTransport.retainedRun rewards C_star C_h q t s hs control0 x
      (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t z).1).records =
      (originalRun rate rewards C_star C_h s z hc he (t.val - s + 1) (by omega)).records := by
  intro x
  let u := (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t z).1
  have hsource : ReferenceGeneratedActivePrefixFactor.splitSource q t u x.1 = z := by
    change (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).symm
      ((ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t z).1,
        (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t z).2) = z
    exact ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_reconstruct p q t z
  let hstart := (ReferenceInitializationControlRemainder.launchStartRemainderEvent_control_independent
    rate rewards C_star C_h q t s x.1 x.2.1 control0 u).mp x.2.2
  let seed := ReferenceGeneratedActivePrefixFactor.generatedActiveSeed
    rate rewards C_star C_h q t u x.1 x.2.1 s hs hstart
  have hseedSpec := ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
    rate rewards C_star C_h q t u x.1 x.2.1 s hs hstart
  have hseed : seed = originalSeed rate rewards C_star C_h z hc := by
    have hsome := hseedSpec.1
    rw [hsource] at hsome
    unfold originalSeed
    simp only [hsome, Option.get_some]
    rfl
  change (ReferenceActivePhysicalHorizon.run seed
    (ReferenceGeneratedActivePrefixFactor.splitSource q t u x.1).1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p
      (ReferenceGeneratedActivePrefixFactor.splitSource q t u x.1)) rewards s (t.val - s + 1)
    (by omega) hseedSpec.2.1).records = _
  calc
    _ = (ReferenceActivePhysicalHorizon.run seed z.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s (t.val - s + 1)
        (by omega) hseedSpec.2.1).records :=
      congrArg (fun source : SourceInput p =>
        (ReferenceActivePhysicalHorizon.run seed source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s
          (t.val - s + 1) (by omega) hseedSpec.2.1).records) hsource
    _ = _ := by
      have hi : (⟨seed, hseedSpec.2.1⟩ :
          {a : ReferenceActivePhysicalStep.State p rate //
            ReferenceActivePhysicalHorizon.allActiveAtStart a s}) =
          ⟨originalSeed rate rewards C_star C_h z hc,
            originalSeed_active rate rewards C_star C_h s z hc he⟩ := Subtype.ext hseed
      exact congrArg (fun initial =>
        (ReferenceActivePhysicalHorizon.run initial.val z.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s
          (t.val - s + 1) (by omega) initial.property).records) hi

/-- Prefix coherence at the actual current index. No equality of future runs
is asserted. Every record here uses the original source's physical input. -/
theorem source_current_record
    (i : Fin (p.m - 1)) (z : SourceInput p)
    (hj : ActualInitializationPhysicalStep.selectedRowIndex p z = q)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (he : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed = s)
    (hx : ReferenceRetainedBoundaryMeasurability.retainedLaunchStartInputOfSource
      rate rewards C_star C_h q t s hs control0 z hj hc he ∈ S i) :
    let x := ReferenceRetainedBoundaryMeasurability.retainedLaunchStartInputOfSource
      rate rewards C_star C_h q t s hs control0 z hj hc he
    ∃ hn : t.val - s < (originalWindow rate rewards C_star C_h s (by omega) z hc he).length,
      (originalWindow rate rewards C_star C_h s (by omega) z hc he)[t.val - s] =
        ReferencePhysicalReleaseObservability.recordOfInput
          (ReferenceFixedTimeSourceControlCoupling.roundInputAtSource p rate (β x) z) := by
  intro x
  let u := (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t z).1
  obtain ⟨hn0, selected0, hselected, hempty, hi⟩ := (show x ∈ S i from hx)
  obtain ⟨_, _, _, _, _, hcontrols⟩ :=
    ReferenceFirstLiveReleaseSliceMass.retained_first_live_release_all_controls
      rewards C_star C_h q t s hs control0 x hn0 selected0 hselected hempty i hi
  obtain ⟨hu, _, hinput, _⟩ := hcontrols u
  have hshort := retained_source_records rate rewards C_star C_h q t s hs control0 z hj hc he
  have hfull : s + ((t.val - s + 1) + (p.T - (t.val + 1))) ≤ p.T := by omega
  obtain ⟨tail, htail⟩ := ReferenceCollectionPhaseHistory.run_records_prefix
    (originalSeed rate rewards C_star C_h z hc) z.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s
    (t.val - s + 1) (p.T - (t.val + 1)) hfull
    (originalSeed_active rate rewards C_star C_h s z hc he)
  have hcounts : (t.val - s + 1) + (p.T - (t.val + 1)) = p.T - s := by omega
  have hp : (ReferenceFirstLiveReleaseControlTransport.retainedRun
      rewards C_star C_h q t s hs control0 x u).records.IsPrefix
      (originalRun rate rewards C_star C_h s z hc he (p.T - s) (by omega)).records := by
    rw [hshort]
    refine ⟨tail, ?_⟩
    simpa only [hcounts, originalRun] using htail.symm
  have hwp := takeWhile_prefix (fun r => !ReferenceCollectionPhaseHistory.cutoffChosen r.input) hp
  change (W x u).IsPrefix (originalWindow rate rewards C_star C_h s (by omega) z hc he) at hwp
  have hbound := lt_of_lt_of_le hu hwp.length_le
  refine ⟨hbound, ?_⟩
  rw [← hwp.getElem hu, record_eq rate ((W x u)[t.val - s])]
  change (W x u)[t.val - s].input = currentInput rate rewards C_star C_h q t s hs control0 x u at hinput
  rw [hinput, currentInput_eq_next]
  rw [ReferenceRetainedBoundaryMeasurability.retainedGeneratedNextInput_eq_of_source
    rate rewards C_star C_h q t s hs control0 z hj hc he]

/-- A literal ORIGINAL-source cylinder. The witnesses assert its original
private J, actual initialization crossing and elapsed start. The flag is on
its full-span original first-live window. No source is resampled here. -/
def sourceCylinder (up : Bool) (i : Fin (p.m - 1)) (Aset : Set X) : Set (SourceInput p) :=
  {z | ∃ hj : ActualInitializationPhysicalStep.selectedRowIndex p z = q,
    ∃ hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true,
    ∃ he : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed = s,
    let x := ReferenceRetainedBoundaryMeasurability.retainedLaunchStartInputOfSource
      rate rewards C_star C_h q t s hs control0 z hj hc he
    x ∈ Aset ∩ S i ∧ ∃ payload : ReferenceActivePhysicalStep.Payload rate,
      baselinePayload rate rewards C_star C_h q t s hs control0 x = some payload ∧
      ∃ hn : t.val - s < (originalWindow rate rewards C_star C_h s (by omega) z hc he).length,
        physicalFlag rate up payload
          ((originalWindow rate rewards C_star C_h s (by omega) z hc he)[t.val - s]'hn) i = true}

private theorem sourceCylinder_iff
    (up : Bool) (i : Fin (p.m - 1)) (Aset : Set X) (z : SourceInput p)
    (hj : ActualInitializationPhysicalStep.selectedRowIndex p z = q)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (he : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed = s) :
    let x := ReferenceRetainedBoundaryMeasurability.retainedLaunchStartInputOfSource
      rate rewards C_star C_h q t s hs control0 z hj hc he
    z ∈ sourceCylinder rate rewards C_star C_h q t s hs control0 up i Aset ↔
      x ∈ Aset ∩ S i ∧
        (x, (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t z).1) ∈
          jointEvent rate rewards C_star C_h q t s hs control0 up i := by
  intro x
  let u := (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t z).1
  have hin : ReferenceFixedTimeSourceControlCoupling.roundInputAtSource p rate (β x) z =
      currentInput rate rewards C_star C_h q t s hs control0 x u := by
    rw [currentInput_eq_next]
    exact (ReferenceRetainedBoundaryMeasurability.retainedGeneratedNextInput_eq_of_source
      rate rewards C_star C_h q t s hs control0 z hj hc he).symm
  constructor
  · rintro ⟨_, _, _, hx, payload, hp, hn, hflag⟩
    obtain ⟨hn', hrecord⟩ := source_current_record rate rewards C_star C_h q t s hs control0
      i z hj hc he hx.2
    refine ⟨hx, (jointEvent_iff rate rewards C_star C_h q t s hs control0 up i x u).2
      ⟨hx.2, ?_⟩⟩
    rw [hp]
    change physicalFlag rate up payload
      (ReferencePhysicalReleaseObservability.recordOfInput
        (currentInput rate rewards C_star C_h q t s hs control0 x u)) i = true
    rw [hrecord, hin] at hflag
    exact hflag
  · rintro ⟨hx, hjoint⟩
    obtain ⟨hn0, selected0, hselected, hempty, hi⟩ := (show x ∈ S i from hx.2)
    have hp := baselinePayload_eq rate rewards C_star C_h q t s hs control0
      i x hn0 selected0 hselected hempty hi
    obtain ⟨hn, hrecord⟩ := source_current_record rate rewards C_star C_h q t s hs control0
      i z hj hc he hx.2
    have hflag := ((jointEvent_iff rate rewards C_star C_h q t s hs control0 up i x u).1 hjoint).2
    rw [hp] at hflag
    refine ⟨hj, hc, he, hx, selected0.view.payload, hp, hn, ?_⟩
    rw [hrecord, hin]
    exact hflag

/-- The corresponding product cylinder, still using the literal joint event. -/
def jointCylinder (up : Bool) (i : Fin (p.m - 1)) (Aset : Set X) : Set (X × TimeControl p) :=
  (Prod.fst ⁻¹' (Aset ∩ S i)) ∩ jointEvent rate rewards C_star C_h q t s hs control0 up i

private theorem measurableSet_jointCylinder
    (up : Bool) (i : Fin (p.m - 1)) (Aset : Set X) (hAset : MeasurableSet Aset) :
    MeasurableSet (jointCylinder rate rewards C_star C_h q t s hs control0 up i Aset) :=
  ((hAset.inter (ReferenceFirstLiveReleaseSourceCylinder.measurableSet_selectedEmptyPendingRemainder
    rewards C_star C_h q t s hs control0 i)).preimage measurable_fst).inter
      (measurableSet_jointEvent rate rewards C_star C_h q t s hs control0 up i)

private theorem sourceMap_embedding : MeasurableEmbedding sourceMap := by
  have hsub := MeasurableEmbedding.subtype_coe
    (ReferenceRetainedBoundaryMeasurability.measurableSet_retainedLaunchStartSet
      rate rewards C_star C_h q t s hs control0)
  exact (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).symm.measurableEmbedding.comp
    (MeasurableEquiv.prodComm.measurableEmbedding.comp
      (hsub.prodMap (MeasurableEmbedding.id (α := TimeControl p))))

/-- Reconstruction equality for the literal original event. The image is a
proved characterization, not the definition of an original cylinder. -/
theorem sourceCylinder_eq_image
    (up : Bool) (i : Fin (p.m - 1)) (Aset : Set X) :
    sourceCylinder rate rewards C_star C_h q t s hs control0 up i Aset =
      sourceMap '' jointCylinder rate rewards C_star C_h q t s hs control0 up i Aset := by
  ext z
  constructor
  · intro hz
    obtain ⟨hj, hc, he, _⟩ := (show z ∈ sourceCylinder
      rate rewards C_star C_h q t s hs control0 up i Aset from hz)
    let x := ReferenceRetainedBoundaryMeasurability.retainedLaunchStartInputOfSource
      rate rewards C_star C_h q t s hs control0 z hj hc he
    have hmem := (sourceCylinder_iff rate rewards C_star C_h q t s hs control0
      up i Aset z hj hc he).1 hz
    refine ⟨(x, (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t z).1), hmem, ?_⟩
    exact ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_reconstruct p q t z
  · rintro ⟨⟨x, u⟩, hmem, rfl⟩
    let z := sourceMap (x, u)
    have hsplit : ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t z = (u, x.1) :=
      (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).apply_symm_apply _
    have hfacts : z ∈ ReferenceRetainedSourceCoupling.retainedSourceEvent rate rewards C_star C_h q s :=
      (ReferenceRetainedSourceCoupling.retainedSourceEvent_reconstruct_iff
        rate rewards C_star C_h q t s hs control0 x.1 u).2 x.2
    obtain ⟨hj, hc, he⟩ := hfacts
    have hj' : ActualInitializationPhysicalStep.selectedRowIndex p z = q := hj
    have hx : ReferenceRetainedBoundaryMeasurability.retainedLaunchStartInputOfSource
        rate rewards C_star C_h q t s hs control0 z hj' hc he = x := by
      apply Subtype.ext
      exact congrArg Prod.snd hsplit
    apply (sourceCylinder_iff rate rewards C_star C_h q t s hs control0
      up i Aset z hj' hc he).2
    rw [hx, hsplit]
    exact hmem

/-- These actual original-source events are Borel for every Borel remainder
set, including null or empty strata. -/
theorem measurableSet_sourceCylinder
    (up : Bool) (i : Fin (p.m - 1)) (Aset : Set X) (hAset : MeasurableSet Aset) :
    MeasurableSet (sourceCylinder rate rewards C_star C_h q t s hs control0 up i Aset) := by
  rw [sourceCylinder_eq_image]
  exact (sourceMap_embedding rate rewards C_star C_h q t s hs control0).measurableSet_image.mpr
    (measurableSet_jointCylinder rate rewards C_star C_h q t s hs control0 up i Aset hAset)

/-- Exact inverse reconstruction; all original private coordinates survive. -/
theorem sourceCylinder_preimage
    (up : Bool) (i : Fin (p.m - 1)) (Aset : Set X) :
    sourceMap ⁻¹' sourceCylinder rate rewards C_star C_h q t s hs control0 up i Aset =
      jointCylinder rate rewards C_star C_h q t s hs control0 up i Aset := by
  rw [sourceCylinder_eq_image]
  exact (sourceMap_embedding rate rewards C_star C_h q t s hs control0).injective.preimage_image _

/-- Genuine section measures. In particular their zero values off S are
measures of empty events, never operational fallback payloads. -/
def sliceMass (up : Bool) (i : Fin (p.m - 1)) (x : X) : ℝ≥0∞ :=
  controlLaw (Prod.mk x ⁻¹' jointEvent rate rewards C_star C_h q t s hs control0 up i)

theorem measurable_sliceMass (up : Bool) (i : Fin (p.m - 1)) :
    Measurable (sliceMass rate rewards C_star C_h q t s hs control0 up i) :=
  measurable_measure_prodMk_left
    (measurableSet_jointEvent rate rewards C_star C_h q t s hs control0 up i)

/-- Both actual section masses and the UP bound, with validity PRODUCED from
C's accepted laws. The same actual selector is used in every formula. -/
theorem sliceMass_closed_forms (i : Fin (p.m - 1)) (x : X) (hx : x ∈ S i) :
    ∃ hn : t.val - s < (W x control0).length,
    ∃ selected0 : ReferenceActivePhysicalStep.Selection (W x control0)[t.val - s].input,
    ∃ _hselected : (W x control0)[t.val - s].output.preparation.coordinator.selection = some selected0,
    ∃ _hempty : selected0.view.pendingAtChoice = ∅,
    ∃ _hi : i ∈ ReferencePhysicalReleaseQuota.pendingAtStart selected0.view.payload
      (β x).time (β x).state,
    ∃ hvalid : CoordinatorLocalArmChoice.ChoiceInputsValid selected0.view.payload
      selected0.view.cutoff (W x control0)[t.val - s].input.time selected0.view.complementWeights,
      sliceMass rate rewards C_star C_h q t s hs control0 true i x =
        ENNReal.ofReal
          (ReleaseRoundKernel.chi
              (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t)
              selected0.view.payload.assignment.auxiliary *
            (1 - CanonicalFastSampling.qGamma p rate.eta rate.eta.property
              selected0.view.payload.eta_le_source_cap selected0.view.payload.anchor
              (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights selected0)
              selected0.view.payload.anchor_pos
              (fun a => (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights_bounds
                selected0 hvalid a).1)
              (fun a => (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights_bounds
                selected0 hvalid a).2.1)
              (fun a => (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights_bounds
                selected0 hvalid a).2.2)
              selected0.view.payload.slowSet
              (ReleaseRoundKernel.auxiliaryFastArm selected0.view.payload.assignment
                selected0.view.payload.slowSet selected0.view.payload.assignment_image.symm)) /
            (4 * (p.m - 1 : ℝ) * (p.K : ℝ))) ∧
      ENNReal.ofReal (ReleaseRoundKernel.chi
          (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t)
          selected0.view.payload.assignment.auxiliary / (12 * (p.m - 1 : ℝ) * (p.K : ℝ))) ≤
        sliceMass rate rewards C_star C_h q t s hs control0 true i x ∧
      sliceMass rate rewards C_star C_h q t s hs control0 false i x =
        ENNReal.ofReal (ReleaseRoundKernel.chi
          (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t)
          (selected0.view.payload.assignment.assigned i) / (2 * (p.K : ℝ))) := by
  obtain ⟨hn, selected0, hselected, hempty, hi, hvalid, hup, hlower, hdata⟩ :=
    ReferenceFirstLiveReleaseSourceCylinder.selectedEmptyPendingRemainder_control_section_masses
      rewards C_star C_h q t s hs control0 i x hx
  have hsections := jointEvent_section rate rewards C_star C_h q t s hs control0
    i x hn selected0 hselected hempty hi
  refine ⟨hn, selected0, hselected, hempty, hi, hvalid, ?_, ?_, ?_⟩
  · simpa only [sliceMass, hsections.1] using hup
  · simpa only [sliceMass, hsections.1] using hlower
  · simpa only [sliceMass, hsections.2] using hdata

/-- The index is an actual membership proof supplied by S. -/
theorem baseline_index_lt (i : Fin (p.m - 1)) (x : X) (hx : x ∈ S i) :
    t.val - s < (W x control0).length := hx.choose

/-- The UNIQUE actual optional selection, chosen only on the computed branch.
The following specification and uniqueness theorem are part of this definition. -/
def baselineSelection (i : Fin (p.m - 1)) (x : X) (hx : x ∈ S i) :
    ReferenceActivePhysicalStep.Selection
      ((W x control0)[t.val - s]'(baseline_index_lt rate rewards C_star C_h q t s hs control0 i x hx)).input :=
  hx.choose_spec.choose

theorem baselineSelection_spec (i : Fin (p.m - 1)) (x : X) (hx : x ∈ S i) :
    let selected0 := baselineSelection rate rewards C_star C_h q t s hs control0 i x hx
    ((W x control0)[t.val - s]'
      (baseline_index_lt rate rewards C_star C_h q t s hs control0 i x hx)).output.preparation.coordinator.selection =
        some selected0 ∧
      selected0.view.pendingAtChoice = ∅ ∧
      i ∈ ReferencePhysicalReleaseQuota.pendingAtStart selected0.view.payload
        (β x).time (β x).state := hx.choose_spec.choose_spec

/-- Independence of dependent indices and ALL actual selector witnesses. -/
theorem baselineSelection_eq
    (i : Fin (p.m - 1)) (x : X) (hx : x ∈ S i)
    (hn : t.val - s < (W x control0).length)
    (selected0 : ReferenceActivePhysicalStep.Selection (W x control0)[t.val - s].input)
    (hselected : (W x control0)[t.val - s].output.preparation.coordinator.selection = some selected0) :
    baselineSelection rate rewards C_star C_h q t s hs control0 i x hx = selected0 :=
  ReferenceFirstLiveReleaseSourceCylinder.selectedEmptyPendingRemainder_selection_unique
    rewards C_star C_h q t s hs control0 i x
    (baseline_index_lt rate rewards C_star C_h q t s hs control0 i x hx) hn
    (baselineSelection rate rewards C_star C_h q t s hs control0 i x hx) selected0
    (baselineSelection_spec rate rewards C_star C_h q t s hs control0 i x hx).1 hselected

/-- Validity is proved for the actual selection, not supplied by an integrand
or cylinder caller. Its proof is irrelevant to all mass expressions. -/
theorem baselineSelection_valid (i : Fin (p.m - 1)) (x : X) (hx : x ∈ S i) :
    let selected0 := baselineSelection rate rewards C_star C_h q t s hs control0 i x hx
    CoordinatorLocalArmChoice.ChoiceInputsValid selected0.view.payload selected0.view.cutoff
      ((W x control0)[t.val - s]'
        (baseline_index_lt rate rewards C_star C_h q t s hs control0 i x hx)).input.time
      selected0.view.complementWeights := by
  have hs0 := baselineSelection_spec rate rewards C_star C_h q t s hs control0 i x hx
  exact (ReferenceFirstLiveReleaseSliceMass.retained_up_release_mass
    rewards C_star C_h q t s hs control0 x
    (baseline_index_lt rate rewards C_star C_h q t s hs control0 i x hx)
    (baselineSelection rate rewards C_star C_h q t s hs control0 i x hx)
    hs0.1 hs0.2.1 i hs0.2.2).choose

/-- All-control identities for the uniquely computed baseline selection.
Membership, current input, whole payload, pending set, cutoff and weights are
OUTPUTS of the actual constructor theorem, with no supplied trace equality. -/
theorem baselineSelection_all_controls (i : Fin (p.m - 1)) (x : X) (hx : x ∈ S i) :
    let selected0 := baselineSelection rate rewards C_star C_h q t s hs control0 i x hx
    baselinePayload rate rewards C_star C_h q t s hs control0 x = some selected0.view.payload ∧
    ∀ u : TimeControl p, ∃ hu : t.val - s < (W x u).length,
      ∃ selectedU : ReferenceActivePhysicalStep.Selection (W x u)[t.val - s].input,
        (W x u)[t.val - s].input =
            currentInput rate rewards C_star C_h q t s hs control0 x u ∧
        (W x u)[t.val - s].output.preparation.coordinator.selection = some selectedU ∧
        selectedU.view.payload = selected0.view.payload ∧
        selectedU.view.pendingAtChoice = selected0.view.pendingAtChoice ∧
        selectedU.view.cutoff = selected0.view.cutoff ∧
        HEq selectedU.view.complementWeights selected0.view.complementWeights := by
  intro selected0
  have hs0 := baselineSelection_spec rate rewards C_star C_h q t s hs control0 i x hx
  have hn := baseline_index_lt rate rewards C_star C_h q t s hs control0 i x hx
  refine ⟨baselinePayload_eq rate rewards C_star C_h q t s hs control0
    i x hn selected0 hs0.1 hs0.2.1 hs0.2.2, ?_⟩
  obtain ⟨_, _, _, _, _, hcontrols⟩ :=
    ReferenceFirstLiveReleaseSliceMass.retained_first_live_release_all_controls
      rewards C_star C_h q t s hs control0 x hn selected0 hs0.1 hs0.2.1 i hs0.2.2
  intro u
  obtain ⟨hu, selectedU, hinput, _, _, _, hselected, hpayload, hpending, hcutoff, hweights, _⟩ :=
    hcontrols u
  exact ⟨hu, selectedU, hinput, hselected, hpayload, hpending, hcutoff, hweights⟩

/-- Closed UP mass on S, extended by the genuine empty-event indicator. -/
def upClosedMass (i : Fin (p.m - 1)) (x : X) : ℝ≥0∞ :=
  if hx : x ∈ S i then ENNReal.ofReal
    (ReferenceFirstLiveReleaseSliceMass.upReleaseMassFormula
      (baselineSelection rate rewards C_star C_h q t s hs control0 i x hx)
      (baselineSelection_valid rate rewards C_star C_h q t s hs control0 i x hx)
      (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t)) else 0

/-- Closed DATA mass. There is no recording mask or thinning factor. -/
def dataClosedMass (i : Fin (p.m - 1)) (x : X) : ℝ≥0∞ :=
  if hx : x ∈ S i then ENNReal.ofReal
    (ReleaseRoundKernel.chi (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t)
      ((baselineSelection rate rewards C_star C_h q t s hs control0 i x hx).view.payload.assignment.assigned i) /
      (2 * (p.K : ℝ))) else 0

/-- The auxiliary-arm UP lower bound, with the same event indicator. -/
def upLowerMass (i : Fin (p.m - 1)) (x : X) : ℝ≥0∞ :=
  if hx : x ∈ S i then ENNReal.ofReal
    (ReleaseRoundKernel.chi (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t)
      (baselineSelection rate rewards C_star C_h q t s hs control0 i x hx).view.payload.assignment.auxiliary /
      (12 * (p.m - 1 : ℝ) * (p.K : ℝ))) else 0

/-- The closed expressions are the literal event kernels on the WHOLE carrier,
and the bound holds also on null/empty/zero-reward branches. -/
theorem sliceMass_eq_closed (i : Fin (p.m - 1)) (x : X) :
    sliceMass rate rewards C_star C_h q t s hs control0 true i x =
        upClosedMass rate rewards C_star C_h q t s hs control0 i x ∧
      sliceMass rate rewards C_star C_h q t s hs control0 false i x =
        dataClosedMass rate rewards C_star C_h q t s hs control0 i x ∧
      upLowerMass rate rewards C_star C_h q t s hs control0 i x ≤
        upClosedMass rate rewards C_star C_h q t s hs control0 i x := by
  by_cases hx : x ∈ S i
  · obtain ⟨hn, selected0, hselected, _, _, hvalid, hup, hlower, hdata⟩ :=
      sliceMass_closed_forms rate rewards C_star C_h q t s hs control0 i x hx
    have heq := baselineSelection_eq rate rewards C_star C_h q t s hs control0
      i x hx hn selected0 hselected
    subst selected0
    have hup' : sliceMass rate rewards C_star C_h q t s hs control0 true i x =
        upClosedMass rate rewards C_star C_h q t s hs control0 i x := by
      simp only [upClosedMass, dite_eq_left hx]
      exact hup
    refine ⟨hup', ?_, ?_⟩
    · simp only [dataClosedMass, dite_eq_left hx]
      exact hdata
    · rw [← hup']
      simpa only [upLowerMass, dite_eq_left hx] using hlower
  · have hempty (up : Bool) : Prod.mk x ⁻¹'
        jointEvent rate rewards C_star C_h q t s hs control0 up i = ∅ := by
      ext u
      simp only [Set.mem_preimage, jointEvent, Set.mem_ofPred_eq, hx, false_and,
        Set.mem_empty_iff_false]
    simp only [sliceMass, hempty, measure_empty, upClosedMass, dataClosedMass,
      upLowerMass, dite_eq_right hx, le_refl, and_self]

/-- The product mass of the actual joint event, by the pinned section law. -/
theorem jointEvent_integral (up : Bool) (i : Fin (p.m - 1)) :
    ((μC).prod controlLaw) (jointEvent rate rewards C_star C_h q t s hs control0 up i) =
      ∫⁻ x, sliceMass rate rewards C_star C_h q t s hs control0 up i x ∂μC :=
  Measure.prod_apply (measurableSet_jointEvent rate rewards C_star C_h q t s hs control0 up i)

/-- Measurability of the closed masses follows from their exact identities
with the genuine section kernels, without discretizing real payload fibres. -/
theorem measurable_closedMasses (i : Fin (p.m - 1)) :
    Measurable (upClosedMass rate rewards C_star C_h q t s hs control0 i) ∧
      Measurable (dataClosedMass rate rewards C_star C_h q t s hs control0 i) := by
  have hup : upClosedMass rate rewards C_star C_h q t s hs control0 i =
      sliceMass rate rewards C_star C_h q t s hs control0 true i :=
    funext fun x => (sliceMass_eq_closed rate rewards C_star C_h q t s hs control0 i x).1.symm
  have hdata : dataClosedMass rate rewards C_star C_h q t s hs control0 i =
      sliceMass rate rewards C_star C_h q t s hs control0 false i :=
    funext fun x => (sliceMass_eq_closed rate rewards C_star C_h q t s hs control0 i x).2.1.symm
  rw [hup, hdata]
  exact ⟨measurable_sliceMass rate rewards C_star C_h q t s hs control0 true i,
    measurable_sliceMass rate rewards C_star C_h q t s hs control0 false i⟩

/-- The original-source mass is its unnormalized remainder integral. -/
theorem sourceCylinder_integral
    (up : Bool) (i : Fin (p.m - 1)) (Aset : Set X) (hAset : MeasurableSet Aset) :
    BootstrapPrivateRoundStreams.sourceInputLaw p
        (sourceCylinder rate rewards C_star C_h q t s hs control0 up i Aset) =
      ∫⁻ x in Aset ∩ S i,
        sliceMass rate rewards C_star C_h q t s hs control0 up i x ∂μC := by
  let event := sourceCylinder rate rewards C_star C_h q t s hs control0 up i Aset
  have hevent := measurableSet_sourceCylinder rate rewards C_star C_h q t s hs control0 up i Aset hAset
  have hsub : event ⊆ ReferenceRetainedSourceCoupling.retainedSourceEvent rate rewards C_star C_h q s := by
    rintro z ⟨hj, hc, he, _⟩
    exact ⟨hj, hc, he⟩
  have hAS := hAset.inter (ReferenceFirstLiveReleaseSourceCylinder.measurableSet_selectedEmptyPendingRemainder
    rewards C_star C_h q t s hs control0 i)
  calc
    _ = ((BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
        (ReferenceRetainedSourceCoupling.retainedSourceEvent rate rewards C_star C_h q s)) event := by
      rw [Measure.restrict_apply hevent, Set.inter_eq_left.mpr hsub]
    _ = (((μC).prod controlLaw).map sourceMap) event := by
      rw [ReferenceRetainedSourceCoupling.retainedSourceMap_product]
    _ = ((μC).prod controlLaw) (jointCylinder rate rewards C_star C_h q t s hs control0 up i Aset) := by
      rw [Measure.map_apply
        (ReferenceRetainedSourceCoupling.measurable_retainedSourceMap rate rewards C_star C_h q t s hs control0)
        hevent]
      rw [sourceCylinder_preimage]
    _ = ∫⁻ z, (jointCylinder rate rewards C_star C_h q t s hs control0 up i Aset).indicator
        (fun _ => (1 : ℝ≥0∞)) z ∂(μC).prod controlLaw :=
      (lintegral_indicator_one (measurableSet_jointCylinder
        rate rewards C_star C_h q t s hs control0 up i Aset hAset)).symm
    _ = ∫⁻ x, ∫⁻ u,
        (jointCylinder rate rewards C_star C_h q t s hs control0 up i Aset).indicator
          (fun _ => (1 : ℝ≥0∞)) (x, u) ∂controlLaw ∂μC :=
      lintegral_prod _ (measurable_const.indicator (measurableSet_jointCylinder
        rate rewards C_star C_h q t s hs control0 up i Aset hAset)).aemeasurable
    _ = ∫⁻ x, controlLaw (Prod.mk x ⁻¹'
        jointCylinder rate rewards C_star C_h q t s hs control0 up i Aset) ∂μC := by
      apply lintegral_congr
      intro x
      have hsection : MeasurableSet (Prod.mk x ⁻¹'
          jointCylinder rate rewards C_star C_h q t s hs control0 up i Aset) :=
        (measurableSet_jointCylinder rate rewards C_star C_h q t s hs control0
          up i Aset hAset).preimage measurable_prodMk_left
      rw [← lintegral_indicator_one hsection]
      apply lintegral_congr
      intro u
      by_cases hu : (x, u) ∈ jointCylinder rate rewards C_star C_h q t s hs control0 up i Aset
      all_goals simp only [Set.indicator_apply, Set.mem_preimage, hu, ite_true, ite_false, Pi.one_apply]
    _ = ∫⁻ x, (Aset ∩ S i).indicator
        (sliceMass rate rewards C_star C_h q t s hs control0 up i) x ∂μC := by
      apply lintegral_congr
      intro x
      by_cases hx : x ∈ Aset ∩ S i
      · have heq : Prod.mk x ⁻¹' jointCylinder rate rewards C_star C_h q t s hs control0 up i Aset =
            Prod.mk x ⁻¹' jointEvent rate rewards C_star C_h q t s hs control0 up i := by
          ext u
          simp only [jointCylinder, Set.mem_preimage, Set.mem_inter_iff, hx, true_and]
        rw [heq, Set.indicator_of_mem hx]
        rfl
      · have heq : Prod.mk x ⁻¹' jointCylinder rate rewards C_star C_h q t s hs control0 up i Aset = ∅ := by
          ext u
          simp only [jointCylinder, Set.mem_preimage, Set.mem_inter_iff, hx, false_and,
            Set.mem_empty_iff_false]
        rw [heq, measure_empty, Set.indicator_of_notMem hx]
    _ = _ := lintegral_indicator hAS _

/-- One coherent original-source release law: closed UP and DATA integrals,
and the auxiliary UP lower-bound integral. No normalization or positive-mass
premise occurs. The SAME original-source branch is used throughout. -/
theorem original_source_release_integrals
    (i : Fin (p.m - 1)) (Aset : Set X) (hAset : MeasurableSet Aset) :
    BootstrapPrivateRoundStreams.sourceInputLaw p
        (sourceCylinder rate rewards C_star C_h q t s hs control0 true i Aset) =
      (∫⁻ x in Aset ∩ S i, upClosedMass rate rewards C_star C_h q t s hs control0 i x ∂μC) ∧
    BootstrapPrivateRoundStreams.sourceInputLaw p
        (sourceCylinder rate rewards C_star C_h q t s hs control0 false i Aset) =
      (∫⁻ x in Aset ∩ S i, dataClosedMass rate rewards C_star C_h q t s hs control0 i x ∂μC) ∧
    (∫⁻ x in Aset ∩ S i, upLowerMass rate rewards C_star C_h q t s hs control0 i x ∂μC) ≤
      BootstrapPrivateRoundStreams.sourceInputLaw p
        (sourceCylinder rate rewards C_star C_h q t s hs control0 true i Aset) := by
  have hup := sourceCylinder_integral rate rewards C_star C_h q t s hs control0 true i Aset hAset
  have hdata := sourceCylinder_integral rate rewards C_star C_h q t s hs control0 false i Aset hAset
  have hup' : BootstrapPrivateRoundStreams.sourceInputLaw p
      (sourceCylinder rate rewards C_star C_h q t s hs control0 true i Aset) =
      ∫⁻ x in Aset ∩ S i, upClosedMass rate rewards C_star C_h q t s hs control0 i x ∂μC := by
    rw [hup]
    exact lintegral_congr fun x =>
      (sliceMass_eq_closed rate rewards C_star C_h q t s hs control0 i x).1
  refine ⟨hup', ?_, ?_⟩
  · rw [hdata]
    exact lintegral_congr fun x =>
      (sliceMass_eq_closed rate rewards C_star C_h q t s hs control0 i x).2.1
  · rw [hup']
    exact lintegral_mono fun x =>
      (sliceMass_eq_closed rate rewards C_star C_h q t s hs control0 i x).2.2

end Bandits.Support.ReferenceFirstLiveReleaseCylinderIntegral

end
