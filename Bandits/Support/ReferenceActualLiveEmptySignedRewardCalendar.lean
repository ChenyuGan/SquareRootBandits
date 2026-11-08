/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteNumericalBranchObservation
public import Bandits.Support.SignedStoppedRegretAccounting
public import Bandits.Support.ReferenceFirstLiveStoppedReleaseCalendarSignedCost

/-!
# Actual live empty-confirmation physical signed-reward calendar

The observation reads the actual coordinator selection and simultaneous
physical action/feedback record on each retained live empty-confirmation
round. Its calendar projects the existing complete suffix and retains absent
readouts, failures, and every physical date.

Sources: `sources/zip4/manuscript/08_main_theorem.tex:78-109`,
`sources/zip4/manuscript/05_binary_transport.tex:293-325`, and
`sources/zip4/manuscript/06_interruptions.tex:246-256,286-295,364-374`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators
open Bandits.Support.ConstructorDimensions

namespace Bandits.Support.ReferenceActualLiveEmptySignedRewardCalendar

abbrev Source (p : ConstructorDimensions.Parameters) :=
  BootstrapPrivateRoundStreams.SourceInput p
abbrev Record {p : ConstructorDimensions.Parameters}
    (rate : ReferenceActivePhysicalStep.RateInput p) :=
  ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)
abbrev Code {p : ConstructorDimensions.Parameters}
    (rate : ReferenceActivePhysicalStep.RateInput p) :=
  ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate)
abbrev SelectionData {p : ConstructorDimensions.Parameters}
    (rate : ReferenceActivePhysicalStep.RateInput p) :=
  ReferenceLiveDispatchOutputMeasurability.SelectionData p rate
abbrev CellData {p : ConstructorDimensions.Parameters}
    (rate : ReferenceActivePhysicalStep.RateInput p) :=
  SelectionData rate × (Bool × (Bool × Option (CoordinatorRecordingOperation.Output p)))

local instance gateDecidable (P : Prop) : Decidable P := Classical.propDecidable P

/-- The number of positively rewarded arms in the original whole row. -/
def positiveArms {p : ConstructorDimensions.Parameters}
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (t : Fin p.T) :
    Finset (Fin p.K) :=
  Finset.univ.filter fun a =>
    0 < (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t).val a

/-- The rowwise envelope `min(m, g_t)` from the main regret accounting. -/
def liveEmptyCap {p : ConstructorDimensions.Parameters}
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (t : Fin p.T) : ℝ :=
  min (p.m : ℝ) ((positiveArms rewards t).card : ℝ)

/-- Sum the actual typed feedback values retained in a whole-step code. -/
def codeOwnTotal {p : ConstructorDimensions.Parameters}
    {rate : ReferenceActivePhysicalStep.RateInput p} (code : Code rate) : ℝ :=
  ∑ player : Fin p.m,
    ((ReferenceActiveHorizonMeasurability.roundRecordCodeOwnEntry code player).2).val.val

/-- The physical diagnostic `slowReward + coordinator fast reward`. This is
not the logical auxiliary reward. -/
def physicalDiagnostic {p : ConstructorDimensions.Parameters}
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (t : Fin p.T) (code : Code rate) (selected : SelectionData rate) : ℝ :=
  let row := ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t
  ReleaseRoundKernel.slowReward row selected.1.payload.slowSet +
    row.val (ReferenceActiveHorizonMeasurability.roundRecordCodeActions code
      (ActiveRoundActions.coordinator p.two_le_m))

/-- The retained selected call is live and its coordinator confirmation set is
empty at arm choice. -/
def liveEmptyGate {p : ConstructorDimensions.Parameters}
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (code : Code rate) (selected : SelectionData rate) : Prop :=
  _root_.Bandits.Support.ReferenceCoordinatorRecorderCallTrace.live code selected = true ∧
    selected.1.pendingAtChoice = ∅

private def cellGate {p : ConstructorDimensions.Parameters}
    {rate : ReferenceActivePhysicalStep.RateInput p} (cell : CellData rate) : Prop :=
  cell.2.1 = true ∧ cell.1.1.pendingAtChoice = ∅

private def observationFromCell {p : ConstructorDimensions.Parameters}
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (t : Fin p.T) (z : CellData rate × Code rate) : Option (ℝ × ℝ × ℝ) :=
  if cellGate z.1 then
    let e := physicalDiagnostic rate rewards t z.2 z.1.1
    some (e, codeOwnTotal z.2, e - codeOwnTotal z.2)
  else none

private def flattenOptional {α : Type*} : Option (Option α) → Option α
  | none => none
  | some value => value

private theorem measurable_flattenOptional {α : Type*} [MeasurableSpace α] :
    Measurable (flattenOptional : Option (Option α) → Option α) := by
  have hEquiv : Measurable (Equiv.optionEquivSumPUnit (Option α)) := comap_measurable _
  have hElim : Measurable
      (Sum.elim (id : Option α → Option α) (fun _ : PUnit => (none : Option α))) :=
    measurable_id.sumElim measurable_const
  have h := hElim.comp hEquiv
  convert h using 1
  funext value
  cases value <;> rfl

/-- Literal actual-source observation. The absent selection and failed gate
are both absent; neither is replaced by a physical zero. -/
def observation {p : ConstructorDimensions.Parameters}
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (t : Fin p.T) (code : Code rate) : Option (ℝ × ℝ × ℝ) :=
  match _root_.Bandits.Support.ReferenceCoordinatorRecorderCallTrace.selection code with
  | none => none
  | some selected =>
      if liveEmptyGate code selected then
        let e := physicalDiagnostic rate rewards t code selected
        some (e, codeOwnTotal code, e - codeOwnTotal code)
      else none

private theorem measurable_codeOwnTotal {p : ConstructorDimensions.Parameters}
    {rate : ReferenceActivePhysicalStep.RateInput p} :
    Measurable (codeOwnTotal (rate := rate)) := by
  have hvalue (player : Fin p.m) : Measurable (fun code : Code rate =>
      ((ReferenceActiveHorizonMeasurability.roundRecordCodeOwnEntry code player).2).val.val) := by
    have hentry := ReferenceActiveHorizonMeasurability.measurable_roundRecordCodeOwnEntry
      (p := p) (rate := rate) player
    exact (measurable_subtype_coe.comp measurable_subtype_coe).comp
      (measurable_snd.comp hentry)
  change Measurable (fun code : Code rate =>
    ∑ player : Fin p.m,
      ((ReferenceActiveHorizonMeasurability.roundRecordCodeOwnEntry code player).2).val.val)
  exact Finset.measurable_fun_sum Finset.univ (fun player _ => hvalue player)

private theorem measurable_physicalDiagnostic {p : ConstructorDimensions.Parameters}
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (t : Fin p.T) :
    Measurable (fun z : SelectionData rate × Code rate =>
      physicalDiagnostic rate rewards t z.2 z.1) := by
  have hview : Measurable (fun z : SelectionData rate × Code rate => z.1.1) :=
    measurable_fst.comp measurable_fst
  have hpayload : Measurable (fun z : SelectionData rate × Code rate => z.1.1.payload) :=
    (measurable_fst.comp (comap_measurable _)).comp hview
  have hslowSet : Measurable (fun z : SelectionData rate × Code rate =>
      z.1.1.payload.slowSet) :=
    (ReferenceCollectionDispatchMeasurability.measurable_payloadSlowSet
      (p := p) (rate := rate)).comp hpayload
  let hrow := ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t
  have hslow : Measurable (fun z : SelectionData rate × Code rate =>
      ReleaseRoundKernel.slowReward hrow z.1.1.payload.slowSet) :=
    (measurable_of_countable fun U : CanonicalOrientedSetLaw.SlowSet p.K p.m =>
      ReleaseRoundKernel.slowReward hrow U).comp hslowSet
  have hphysical : Measurable (fun code : Code rate => code.2.2.1) :=
    measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_id))
  have hprofile : Measurable (fun code : Code rate =>
      ReferenceActiveHorizonMeasurability.roundRecordCodeActions code) := by
    apply measurable_pi_iff.mpr
    intro player
    exact (measurable_pi_apply player).comp
      (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp hphysical)))
  have hcoord : Measurable (fun z : SelectionData rate × Code rate =>
      ReferenceActiveHorizonMeasurability.roundRecordCodeActions z.2
        (ActiveRoundActions.coordinator p.two_le_m)) :=
    (measurable_pi_apply (ActiveRoundActions.coordinator p.two_le_m)).comp
      (hprofile.comp measurable_snd)
  have hfast : Measurable (fun z : SelectionData rate × Code rate =>
      hrow.val (ReferenceActiveHorizonMeasurability.roundRecordCodeActions z.2
        (ActiveRoundActions.coordinator p.two_le_m))) :=
    (measurable_of_countable fun a : Fin p.K => hrow.val a).comp hcoord
  have heq : (fun z : SelectionData rate × Code rate =>
      physicalDiagnostic rate rewards t z.2 z.1) =
      (fun z => ReleaseRoundKernel.slowReward hrow z.1.1.payload.slowSet +
        hrow.val (ReferenceActiveHorizonMeasurability.roundRecordCodeActions z.2
          (ActiveRoundActions.coordinator p.two_le_m))) := by
    funext z
    rfl
  rw [heq]
  exact hslow.add hfast

private theorem measurable_observationFromCell {p : ConstructorDimensions.Parameters}
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (t : Fin p.T) :
    Measurable (observationFromCell rate rewards t) := by
  have hselected : Measurable (fun z : CellData rate × Code rate => z.1.1) :=
    measurable_fst.comp measurable_fst
  have hview : Measurable (fun z : CellData rate × Code rate => z.1.1.1) :=
    measurable_fst.comp hselected
  have hviewCoordinates : Measurable (fun z : CellData rate × Code rate =>
      ReferenceDownReceptionMeasurability.choiceTimeViewObservation z.1.1.1) :=
    (comap_measurable _).comp hview
  have hpending : Measurable (fun z : CellData rate × Code rate =>
      ((ReferenceDownReceptionMeasurability.choiceTimeViewObservation z.1.1.1).2).1) :=
    measurable_fst.comp (measurable_snd.comp hviewCoordinates)
  have hlive : Measurable (fun z : CellData rate × Code rate => z.1.2.1) :=
    measurable_fst.comp (measurable_snd.comp measurable_fst)
  have hgateBool : Measurable (fun z : CellData rate × Code rate =>
      decide (cellGate z.1)) := by
    have hdiscrete : Measurable (fun pair : Bool × Finset (Fin (p.m - 1)) =>
        decide (pair.1 = true ∧ pair.2 = ∅)) := measurable_of_countable _
    have hcomp := hdiscrete.comp (hlive.prodMk hpending)
    convert hcomp using 1
    funext z
    cases h : z.1.2.1 with
    | false => simp [cellGate, ReferenceDownReceptionMeasurability.choiceTimeViewObservation, h]
    | true =>
        simp [cellGate, ReferenceDownReceptionMeasurability.choiceTimeViewObservation, h]
        rfl
  have hset : MeasurableSet {z : CellData rate × Code rate | cellGate z.1} := by
    have heq : {z : CellData rate × Code rate | cellGate z.1} =
        (fun z => decide (cellGate z.1)) ⁻¹' {true} := by
      ext z
      simp
    rw [heq]
    exact (measurableSet_singleton true).preimage hgateBool
  have hpair : Measurable (fun z : CellData rate × Code rate => (z.1.1, z.2)) :=
    (measurable_fst.comp measurable_fst).prodMk measurable_snd
  have he := (measurable_physicalDiagnostic rate rewards t).comp hpair
  have hy : Measurable (fun z : CellData rate × Code rate => codeOwnTotal z.2) :=
    measurable_codeOwnTotal.comp measurable_snd
  have htuple : Measurable (fun z : CellData rate × Code rate =>
      let e := physicalDiagnostic rate rewards t z.2 z.1.1
      (e, codeOwnTotal z.2, e - codeOwnTotal z.2)) := by
    change Measurable (fun z : CellData rate × Code rate =>
      (physicalDiagnostic rate rewards t z.2 z.1.1,
        (codeOwnTotal z.2, physicalDiagnostic rate rewards t z.2 z.1.1 - codeOwnTotal z.2)))
    exact he.prodMk (hy.prodMk (he.sub hy))
  have hsome : Measurable (fun z : CellData rate × Code rate =>
      (some (let e := physicalDiagnostic rate rewards t z.2 z.1.1
        (e, codeOwnTotal z.2, e - codeOwnTotal z.2) : ℝ × ℝ × ℝ) :
        Option (ℝ × ℝ × ℝ))) := by
    apply measurable_comap_iff.mpr
    exact measurable_inl.comp htuple
  exact Measurable.ite hset hsome measurable_const

/-- The per-code readout is Borel in the existing code measurable space. -/
theorem measurable_observation {p : ConstructorDimensions.Parameters}
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (t : Fin p.T) :
    Measurable (fun code : Code rate => observation rate rewards t code) := by
  have hcell := _root_.Bandits.Support.ReferenceCoordinatorRecorderCallTrace.measurable_cell
    (p := p) (rate := rate)
  have hselection : Measurable
      (_root_.Bandits.Support.ReferenceCoordinatorRecorderCallTrace.selection
        (p := p) (rate := rate)) := by
    have hfirst : Measurable (fun z : CellData rate × Code rate => z.1.1) :=
      measurable_fst.comp measurable_fst
    have hmap := ReferenceCollectionInstallOutputMeasurability.measurable_optionMapDependent
      (fun z => z.1.1) hfirst
      (_root_.Bandits.Support.ReferenceCoordinatorRecorderCallTrace.cell
        (p := p) (rate := rate)) hcell
    have heq : (fun code : Code rate =>
        (_root_.Bandits.Support.ReferenceCoordinatorRecorderCallTrace.cell
          (p := p) (rate := rate) code).map Prod.fst) =
          _root_.Bandits.Support.ReferenceCoordinatorRecorderCallTrace.selection := by
      funext code
      simp [_root_.Bandits.Support.ReferenceCoordinatorRecorderCallTrace.cell,
        _root_.Bandits.Support.ReferenceCoordinatorRecorderCallTrace.selection,
        Function.comp_def]
    rw [← heq]
    exact hmap
  have hmap := ReferenceCollectionInstallOutputMeasurability.measurable_optionMapDependent
    (fun z : CellData rate × Code rate => observationFromCell rate rewards t z)
    (measurable_observationFromCell rate rewards t)
    (_root_.Bandits.Support.ReferenceCoordinatorRecorderCallTrace.cell
      (p := p) (rate := rate)) hcell
  have heq : (fun code : Code rate => observation rate rewards t code) =
      fun code => flattenOptional
        ((_root_.Bandits.Support.ReferenceCoordinatorRecorderCallTrace.cell
          (p := p) (rate := rate) code).map
          fun cell => observationFromCell rate rewards t (cell, code)) := by
    funext code
    cases h : _root_.Bandits.Support.ReferenceCoordinatorRecorderCallTrace.selection code with
    | none => simp [observation, flattenOptional,
        _root_.Bandits.Support.ReferenceCoordinatorRecorderCallTrace.cell, h]
    | some selected =>
        simp [observation, observationFromCell, cellGate, liveEmptyGate, flattenOptional,
          _root_.Bandits.Support.ReferenceCoordinatorRecorderCallTrace.cell, h]; rfl
  rw [heq]
  exact measurable_flattenOptional.comp hmap

/-- Literal map of every entry of B's complete-branch observation. -/
def calendar {p : ConstructorDimensions.Parameters}
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : Source p) :
    List (Fin p.T × Option (ℝ × ℝ × ℝ)) :=
  (_root_.Bandits.Support.ReferenceCompleteNumericalBranchObservation.completeBranchObservation
    rate rewards C_star C_h source).map fun entry =>
      (entry.1, observation rate rewards entry.1 entry.2.1)

/-- Record lookup reads the original rows, selected private row, exact date,
and unrestricted whole reward table from its genuine source chronology. -/
private theorem actualRecord_fields {p : ConstructorDimensions.Parameters}
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T) (source : Source p)
    (r : Record rate)
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t source = some r) :
    r.input.rows = source.1.2 ∧
      r.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p source ∧
      r.input.time = t ∧ r.input.rewards = rewards := by
  by_cases hby : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
      rate rewards C_star C_h t.val source
  · have hlaunch := ReferenceLocalReleaseGateChronology.sourceSeed_launch
      rate source rewards C_star C_h hby.1
    have hactual := ReferenceSourcePrefixHistoryFiltration.actualRecord_on_launch
      rate rewards C_star C_h t source _ hlaunch hby.2
    have heq := Option.some.inj (hr.symm.trans hactual)
    subst r
    refine ⟨rfl, rfl, ?_, rfl⟩
    apply Fin.ext
    dsimp only [ReferenceAssignmentPayloadChronology.actualRunRecordAt,
      ReferenceActivePhysicalHorizon.roundInputAt]
    have hstartBound := ReferenceCompletePhysicalHistory.physicalStart_le_T
      rate source rewards C_star C_h
    have hlaunchBy := hby.2
    omega
  · rw [ReferenceSourcePrefixHistoryFiltration.actualRecord_eq_none_of_not_launchBy
      rate rewards C_star C_h t source hby] at hr
    cases hr

private theorem actualCode_selection {p : ConstructorDimensions.Parameters}
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (r : Record rate) :
    _root_.Bandits.Support.ReferenceCoordinatorRecorderCallTrace.selection
        (ReferenceActiveHorizonMeasurability.roundRecordCode r) =
      r.output.preparation.coordinator.selection.map
        ReferenceLiveDispatchOutputMeasurability.encodeSelection := by
  have hprep : r.output.preparation = ReferenceActivePhysicalStep.prepare r.input := by
    simpa [ReferenceActivePhysicalStep.step] using
      congrArg (fun output : ReferenceActivePhysicalStep.RoundOutput r.input =>
        output.preparation) r.output_eq
  calc
    _ = (ReferenceActivePhysicalStep.dispatch r.input).selection.map
        ReferenceLiveDispatchOutputMeasurability.encodeSelection :=
      (ReferenceActiveHorizonMeasurability.roundRecordCode_front r).1
    _ = r.output.preparation.coordinator.selection.map
        ReferenceLiveDispatchOutputMeasurability.encodeSelection := by
      rw [hprep]
      rfl

private theorem record_coordinator_action {p : ConstructorDimensions.Parameters}
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (r : Record rate) (sel : ReferenceActivePhysicalStep.Selection r.input)
    (hsel : r.output.preparation.coordinator.selection = some sel) :
    r.actions (ActiveRoundActions.coordinator p.two_le_m) = sel.arm := by
  change r.output.preparation.arms.actions _ = _
  rw [ReferenceActivePhysicalStep.PreparedRound.action_coordinator]
  change ReferenceActivePhysicalStep.DispatchCut.arm r.output.preparation.coordinator = _
  simp only [ReferenceActivePhysicalStep.DispatchCut.arm, hsel]

private theorem reward_sum_le_card {K : ℕ}
    (row : ActiveRoundActions.RewardRow K) (S : Finset (Fin K)) :
    (∑ a ∈ S, row.val a) ≤ (S.card : ℝ) := by
  calc
    (∑ a ∈ S, row.val a) ≤ ∑ a ∈ S, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro a ha
      exact (row.property a).2
    _ = (S.card : ℝ) := by simp

private theorem reward_sum_le_positive_support {K : ℕ}
    (row : ActiveRoundActions.RewardRow K) (S : Finset (Fin K)) :
    (∑ a ∈ S, row.val a) ≤
      ((Finset.univ.filter fun a : Fin K => 0 < row.val a).card : ℝ) := by
  calc
    (∑ a ∈ S, row.val a) ≤
        ∑ a ∈ S, if 0 < row.val a then (1 : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro a ha
      by_cases hpos : 0 < row.val a
      · simpa [hpos] using (row.property a).2
      · have hzero : row.val a = 0 :=
          le_antisymm (le_of_not_gt hpos) (row.property a).1
        simp [hzero]
    _ = ((S.filter fun a : Fin K => 0 < row.val a).card : ℝ) := by
      rw [← Finset.natCast_card_filter]
    _ ≤ ((Finset.univ.filter fun a : Fin K => 0 < row.val a).card : ℝ) := by
      exact_mod_cast Finset.card_le_card (by
        intro a ha
        rcases Finset.mem_filter.mp ha with ⟨_, hpos⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpos⟩)

private theorem physicalDiagnostic_bounds {p : ConstructorDimensions.Parameters}
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (t : Fin p.T) (code : Code rate) (selected : SelectionData rate)
    (fast : CanonicalFastSampling.FastArm selected.1.payload.slowSet)
    (haction : ReferenceActiveHorizonMeasurability.roundRecordCodeActions code
        (ActiveRoundActions.coordinator p.two_le_m) = fast.1) :
    0 ≤ physicalDiagnostic rate rewards t code selected ∧
      physicalDiagnostic rate rewards t code selected ≤ liveEmptyCap rewards t := by
  let row := ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t
  let arms := insert fast.1 selected.1.payload.slowSet.val
  have hfastOut : fast.1 ∉ selected.1.payload.slowSet.val :=
    (Finset.mem_sdiff.mp fast.2).2
  have hcardSlow := CanonicalOrientedSetLaw.slowSet_card p.two_le_m
    selected.1.payload.slowSet
  have hcard : arms.card = p.m := by
    rw [Finset.card_insert_of_notMem hfastOut]
    omega
  have hsum : physicalDiagnostic rate rewards t code selected =
      ∑ a ∈ arms, row.val a := by
    change ReleaseRoundKernel.slowReward row selected.1.payload.slowSet +
      row.val (ReferenceActiveHorizonMeasurability.roundRecordCodeActions code
        (ActiveRoundActions.coordinator p.two_le_m)) = _
    rw [haction, ReleaseRoundKernel.slowReward, Finset.sum_insert hfastOut]
    ring
  have hnonneg : 0 ≤ ∑ a ∈ arms, row.val a := by
    apply Finset.sum_nonneg
    intro a ha
    exact (row.property a).1
  have hcardBound : (∑ a ∈ arms, row.val a) ≤ (p.m : ℝ) := by
    calc
      (∑ a ∈ arms, row.val a) ≤ (arms.card : ℝ) := reward_sum_le_card row arms
      _ = (p.m : ℝ) := by exact_mod_cast hcard
  have hpositiveBound : (∑ a ∈ arms, row.val a) ≤
      ((positiveArms rewards t).card : ℝ) := by
    simpa [positiveArms, row] using reward_sum_le_positive_support row arms
  refine ⟨?_, ?_⟩
  · rw [hsum]
    exact hnonneg
  · rw [hsum]
    change (∑ a ∈ arms, row.val a) ≤ min (p.m : ℝ)
      ((positiveArms rewards t).card : ℝ)
    exact le_min hcardBound hpositiveBound

/-- The actual code's selected cell is exactly the encoding of the physical
round's dependent coordinator selection. -/
theorem actualCode_selection_eq {p : ConstructorDimensions.Parameters}
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (r : Record rate) :
    _root_.Bandits.Support.ReferenceCoordinatorRecorderCallTrace.selection
        (ReferenceActiveHorizonMeasurability.roundRecordCode r) =
      r.output.preparation.coordinator.selection.map
        ReferenceLiveDispatchOutputMeasurability.encodeSelection :=
  actualCode_selection r

/-- A missing actual selection or a failed live-empty gate gives the literal
absent readout. -/
theorem observation_eq_none_iff {p : ConstructorDimensions.Parameters}
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (t : Fin p.T) (code : Code rate) :
    observation rate rewards t code = none ↔
      _root_.Bandits.Support.ReferenceCoordinatorRecorderCallTrace.selection code = none ∨
        ∀ selected, _root_.Bandits.Support.ReferenceCoordinatorRecorderCallTrace.selection code =
          some selected → ¬ liveEmptyGate code selected := by
  classical
  cases hselection : _root_.Bandits.Support.ReferenceCoordinatorRecorderCallTrace.selection code with
  | none => simp [observation, hselection]
  | some selected =>
      by_cases hgate : liveEmptyGate code selected
      · simp [observation, hselection, hgate]
      · simp [observation, hselection, hgate]

/-- At an actual record lookup, absence is exactly absent dispatcher
selection or failure of its encoded live-empty gate. -/
theorem actual_observation_eq_none_iff {p : ConstructorDimensions.Parameters}
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T) (source : Source p) (r : Record rate)
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t source = some r) :
    r.input.time = t ∧
      (observation rate rewards t (ReferenceActiveHorizonMeasurability.roundRecordCode r) = none ↔
        r.output.preparation.coordinator.selection = none ∨
          ∀ selected, r.output.preparation.coordinator.selection = some selected →
            ¬ liveEmptyGate (ReferenceActiveHorizonMeasurability.roundRecordCode r)
              (ReferenceLiveDispatchOutputMeasurability.encodeSelection selected)) := by
  have htime := (actualRecord_fields rate rewards C_star C_h t source r hr).2.2.1
  refine ⟨htime, ?_⟩
  rw [observation_eq_none_iff, actualCode_selection_eq]
  cases hselection : r.output.preparation.coordinator.selection <;> simp

/-- On an actual retained live empty-confirmation selection, the physical fast
arm is the coordinator's local fast draw and the readout has its signed
physical diagnostic and exact own-entry total. -/
theorem actual_live_empty_diagnostic {p : ConstructorDimensions.Parameters}
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T) (source : Source p)
    (r : Record rate)
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t source = some r)
    (sel : ReferenceActivePhysicalStep.Selection r.input)
    (hsel : r.output.preparation.coordinator.selection = some sel)
    (hgate : liveEmptyGate (ReferenceActiveHorizonMeasurability.roundRecordCode r)
      (ReferenceLiveDispatchOutputMeasurability.encodeSelection sel)) :
    r.input.time = t ∧ r.input.rewards = rewards ∧
      r.input.rows = source.1.2 ∧
      r.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p source ∧
      (sel.view.payload.slowSet).1.card = p.m - 1 ∧
      r.actions (ActiveRoundActions.coordinator p.two_le_m) = sel.arm ∧
      sel.arm = (CoordinatorLocalArmChoice.localFastDraw sel.view.payload sel.view.cutoff
        r.input.time sel.view.complementWeights
        (ReferenceLaterLiveNumericalReadout.selection_choiceValid sel)
        (r.input.row.2 r.input.time)).1 ∧
      sel.arm ∉ sel.view.payload.slowSet.val ∧
      observation rate rewards t (ReferenceActiveHorizonMeasurability.roundRecordCode r) =
        some (physicalDiagnostic rate rewards t
          (ReferenceActiveHorizonMeasurability.roundRecordCode r)
          (ReferenceLiveDispatchOutputMeasurability.encodeSelection sel),
          r.totalReward,
          physicalDiagnostic rate rewards t
            (ReferenceActiveHorizonMeasurability.roundRecordCode r)
            (ReferenceLiveDispatchOutputMeasurability.encodeSelection sel) - r.totalReward) ∧
      0 ≤ physicalDiagnostic rate rewards t
          (ReferenceActiveHorizonMeasurability.roundRecordCode r)
          (ReferenceLiveDispatchOutputMeasurability.encodeSelection sel) ∧
      physicalDiagnostic rate rewards t
          (ReferenceActiveHorizonMeasurability.roundRecordCode r)
          (ReferenceLiveDispatchOutputMeasurability.encodeSelection sel) ≤ liveEmptyCap rewards t ∧
      0 ≤ r.totalReward ∧ r.totalReward ≤ (p.m : ℝ) ∧
      |physicalDiagnostic rate rewards t
          (ReferenceActiveHorizonMeasurability.roundRecordCode r)
          (ReferenceLiveDispatchOutputMeasurability.encodeSelection sel) - r.totalReward| ≤
        (p.m : ℝ) := by
  let code := ReferenceActiveHorizonMeasurability.roundRecordCode r
  let selected := ReferenceLiveDispatchOutputMeasurability.encodeSelection sel
  rcases hgate with ⟨hLiveGate, hEmptyGate⟩
  have hfields := actualRecord_fields rate rewards C_star C_h t source r hr
  have htrace := actualCode_selection r
  have hlive : CoordinatorLocalArmChoice.assignmentIsLive sel.view.payload
      sel.view.cutoff r.input.time := by
    have hliveCode := _root_.Bandits.Support.ReferenceCoordinatorRecorderCallTrace.live_eq_assignmentIsLive
      code selected r.input.time (by rfl)
    change _root_.Bandits.Support.ReferenceCoordinatorRecorderCallTrace.live code selected = true at hLiveGate
    rw [hLiveGate] at hliveCode
    exact of_decide_eq_true hliveCode.symm
  have hempty : sel.view.pendingAtChoice = ∅ := hEmptyGate
  have hvalid := ReferenceLaterLiveNumericalReadout.selection_choiceValid sel
  have hfastChoice := CoordinatorLocalArmChoice.coordinatorArmChoiceCore_live_empty
    sel.view.payload sel.view.pendingAtChoice sel.view.cutoff r.input.time
    sel.view.complementWeights (r.input.row.2 r.input.time) hvalid hlive hempty
  let fastDraw := CoordinatorLocalArmChoice.localFastDraw
      sel.view.payload sel.view.cutoff r.input.time sel.view.complementWeights hvalid
      (r.input.row.2 r.input.time)
  have hchoice : sel.arm = fastDraw.1 := by
    have hactual := sel.choice_eq
    change CoordinatorLocalArmChoice.coordinatorArmChoiceCore sel.view.payload
      sel.view.pendingAtChoice sel.view.cutoff r.input.time sel.view.complementWeights
      (r.input.row.2 r.input.time) = some sel.arm at hactual
    rw [hfastChoice] at hactual
    exact (Option.some.inj hactual).symm
  have haction := record_coordinator_action r sel hsel
  have hfast : CanonicalFastSampling.FastArm sel.view.payload.slowSet := fastDraw
  have hfastOut : fastDraw.1 ∉ sel.view.payload.slowSet.val :=
    (Finset.mem_sdiff.mp fastDraw.2).2
  have hfastArm : sel.arm ∉ sel.view.payload.slowSet.val := by
    rw [hchoice]
    exact hfastOut
  have hcodeAction : ReferenceActiveHorizonMeasurability.roundRecordCodeActions code
      (ActiveRoundActions.coordinator p.two_le_m) = fastDraw.1 := by
    calc
      _ = r.actions (ActiveRoundActions.coordinator p.two_le_m) :=
        congrFun (ReferenceActiveHorizonMeasurability.roundRecordCode_front r).2.2.1 _
      _ = sel.arm := haction
      _ = fastDraw.1 := hchoice
  have hbound := physicalDiagnostic_bounds rate rewards t code selected fastDraw hcodeAction
  have htotal : codeOwnTotal code = r.totalReward := by
    unfold codeOwnTotal ReferenceActivePhysicalHorizon.RoundRecord.totalReward
      ReferenceActivePhysicalHorizon.observationValue
    apply Finset.sum_congr rfl
    intro player hplayer
    have hown :=
      (ReferenceActiveHorizonMeasurability.roundRecordCode_reconstructs r).2.2.2.2 player
    exact congrArg (fun entry : Fin p.K × ReferencePrelaunchFollower.Observation p =>
      entry.2.val.val)
      hown
  have hobs : observation rate rewards t code =
      some (physicalDiagnostic rate rewards t code selected, r.totalReward,
        physicalDiagnostic rate rewards t code selected - r.totalReward) := by
    simp [observation, code, selected, htrace, hsel, liveEmptyGate,
      hLiveGate, hEmptyGate, htotal]
  have htotalBounds := ReferenceActivePhysicalHorizon.RoundRecord.totalReward_bounds r
  have hEupper : physicalDiagnostic rate rewards t code selected ≤ (p.m : ℝ) :=
    le_trans hbound.2 (min_le_left _ _)
  have hslowCard : (sel.view.payload.slowSet).1.card = p.m - 1 := by
    have hc := CanonicalOrientedSetLaw.slowSet_card p.two_le_m sel.view.payload.slowSet
    omega
  refine ⟨hfields.2.2.1, hfields.2.2.2, hfields.1,
    hfields.2.1, hslowCard,
    haction, hchoice, hfastArm, hobs, hbound.1, hbound.2,
    htotalBounds.1, htotalBounds.2, ?_⟩
  rw [abs_le]
  constructor
  · linarith [hbound.1, htotalBounds.2]
  · linarith [hEupper, htotalBounds.1]

/-- The projected list has exactly B's complete-suffix length. -/
theorem calendar_length {p : ConstructorDimensions.Parameters}
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : Source p) :
    (calendar rate rewards C_star C_h source).length =
      p.T - ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h := by
  simp [calendar,
    _root_.Bandits.Support.ReferenceCompleteNumericalBranchObservation.completeBranchObservation,
    _root_.Bandits.Support.ReferenceCompleteNumericalBranchObservation.branchCalendar_length]

/-- The projected dates are exactly B's source suffix dates, including no
launch, terminal launch, and launch at the final physical date. -/
theorem calendar_times {p : ConstructorDimensions.Parameters}
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : Source p) :
    (calendar rate rewards C_star C_h source).map (fun entry => entry.1.val) =
      List.range' (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
        (p.T - ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h) 1 := by
  unfold calendar
  rw [List.map_map]
  change (_root_.Bandits.Support.ReferenceCompleteNumericalBranchObservation.completeBranchObservation
    rate rewards C_star C_h source).map (fun entry => entry.1.val) = _
  simpa [_root_.Bandits.Support.ReferenceCompleteNumericalBranchObservation.completeBranchObservation] using
    _root_.Bandits.Support.ReferenceCompleteNumericalBranchObservation.branchCalendar_times
      rate rewards C_star C_h 0 source

/-- When the actual record lookup is absent, the calendar has no suffix entry
at this date. -/
theorem no_calendar_entry_of_actualRecord_none {p : ConstructorDimensions.Parameters}
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : Source p) (t : Fin p.T)
    (hnone : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t source = none) :
    ∀ value, (t, value) ∉ calendar rate rewards C_star C_h source := by
  intro value hmem
  have hstart : t.val < ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h := by
    by_contra hnot
    have hle := Nat.le_of_not_gt hnot
    have hcross : (ReferenceCompletePhysicalHistory.generatedBoundary rate source
        rewards C_star C_h).crossing.isSome = true := by
      cases hc : (ReferenceCompletePhysicalHistory.generatedBoundary rate source
          rewards C_star C_h).crossing with
      | none =>
          have hterminal :=
            (ReferenceCorrectedInitializationLaunch.correctedLaunch_no_crossing_source
              rate source rewards C_star C_h hc).2.1
          change ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h = p.T at hterminal
          have ht := t.isLt
          omega
      | some active => simp
    have hlaunch := ReferenceLocalReleaseGateChronology.sourceSeed_launch
      rate source rewards C_star C_h hcross
    have hrecord := ReferenceSourcePrefixHistoryFiltration.actualRecord_on_launch
      rate rewards C_star C_h t source _ hlaunch hle
    rw [hrecord] at hnone
    cases hnone
  have htime : t.val ∈ (calendar rate rewards C_star C_h source).map
      (fun entry => entry.1.val) := by
    have hstartBound := ReferenceCompletePhysicalHistory.physicalStart_le_T
      rate source rewards C_star C_h
    apply List.mem_map.mpr
    exact ⟨(t, value), hmem, rfl⟩
  rw [calendar_times rate rewards C_star C_h source] at htime
  have hstart_le := List.left_le_of_mem_range' htime
  omega

/-- A present actual record is represented by the exact same record code at
the same source calendar index. -/
theorem actualRecord_calendar_value {p : ConstructorDimensions.Parameters}
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : Source p) (t : Fin p.T) (r : Record rate)
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t source = some r) :
    (t, observation rate rewards t
      (ReferenceActiveHorizonMeasurability.roundRecordCode r)) ∈
        calendar rate rewards C_star C_h source := by
  have hfields := actualRecord_fields rate rewards C_star C_h t source r hr
  have hstart : ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h ≤ t.val := by
    by_contra hnot
    have hnone := ReferenceSourcePrefixHistoryFiltration.actualRecord_eq_none_of_future_start
      rate rewards C_star C_h t source (Nat.lt_of_not_ge hnot)
    rw [hnone] at hr
    cases hr
  have hindex : t.val - ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h <
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h).length := by
    rw [ReferenceCompletePhysicalHistory.completeSuffixRecords_length]
    omega
  have hlookup : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[t.val -
        ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h]? = some r := by
    simpa [ReferenceSourcePrefixHistoryFiltration.actualRecord, hstart] using hr
  let k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length := ⟨
    t.val - ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h, hindex⟩
  have hrecord : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).get k = r :=
    (List.getElem?_eq_some_iff.mp hlookup).2
  have hlen :
      (_root_.Bandits.Support.ReferenceCompleteNumericalBranchObservation.branchCalendar
        rate rewards C_star C_h 0 source).length =
        (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h).length := by
    simp [_root_.Bandits.Support.ReferenceCompleteNumericalBranchObservation.branchCalendar]
  let bk : Fin (_root_.Bandits.Support.ReferenceCompleteNumericalBranchObservation.branchCalendar
      rate rewards C_star C_h 0 source).length :=
    ⟨k.val, by simp [hlen]⟩
  have hget := _root_.Bandits.Support.ReferenceCompleteNumericalBranchObservation.branchCalendar_get
    rate rewards C_star C_h 0 source k
  have hmem := List.get_mem
    (_root_.Bandits.Support.ReferenceCompleteNumericalBranchObservation.branchCalendar
      rate rewards C_star C_h 0 source) bk
  rw [hrecord] at hget
  have hget' : (_root_.Bandits.Support.ReferenceCompleteNumericalBranchObservation.branchCalendar
      rate rewards C_star C_h 0 source).get bk =
        (r.input.time,
          (ReferenceActiveHorizonMeasurability.roundRecordCode r,
            _root_.Bandits.Support.ReferenceCompleteNumericalBranchObservation.branchReadout
              rate 0 r)) := by
    simpa [bk] using hget
  rw [hget'] at hmem
  apply List.mem_map.mpr
  refine ⟨(r.input.time,
    (ReferenceActiveHorizonMeasurability.roundRecordCode r,
      _root_.Bandits.Support.ReferenceCompleteNumericalBranchObservation.branchReadout rate 0 r)),
    hmem, ?_⟩
  have htime := hfields.2.2.1
  simp [observation, htime]

/-- The projection is Borel on the original whole-source product space. -/
theorem measurable_calendar {p : ConstructorDimensions.Parameters}
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) :
    Measurable (calendar rate rewards C_star C_h) := by
  change Measurable (fun source =>
    (_root_.Bandits.Support.ReferenceCompleteNumericalBranchObservation.completeBranchObservation
      rate rewards C_star C_h source).map
        (fun entry => (entry.1, observation rate rewards entry.1 entry.2.1)))
  have hentry : Measurable (fun entry :
      _root_.Bandits.Support.ReferenceCompleteNumericalBranchObservation.NumericalEntry rate =>
      (entry.1, observation rate rewards entry.1 entry.2.1)) := by
    have hobs : Measurable (fun z : Fin p.T × Code rate =>
        observation rate rewards z.1 z.2) :=
      measurable_from_prod_countable_right fun t => measurable_observation rate rewards t
    exact measurable_fst.prodMk
      (hobs.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd)))
  exact ReferenceActiveHorizonMeasurability.measurable_list_map
    (records := _root_.Bandits.Support.ReferenceCompleteNumericalBranchObservation.completeBranchObservation
      rate rewards C_star C_h)
    (_root_.Bandits.Support.ReferenceCompleteNumericalBranchObservation.measurable_completeBranchObservation
      rate rewards C_star C_h)
    (fun entry => (entry.1, observation rate rewards entry.1 entry.2.1)) hentry
