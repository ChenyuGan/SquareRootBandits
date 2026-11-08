/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveConditionalWeightedDrift

import Mathlib.Data.List.TakeWhile

/-!
# Actual empty-pending first-live recording branch

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:140-188,245-318`,
`sources/zip4/manuscript/06_interruptions.tex:391-408,425-426`,
`sources/zip4/manuscript/07_public_setup.tex:145-164`, and
`sources/zip4/manuscript/08_main_theorem.tex:78-104`.

All readouts use the existing corrected launch, complete source, physical run,
and PREPARE. The inherited measures are finite and unnormalized, including
zero strata. Empty coordinator pending is distinct from the release-waiting
sets of individual followers. These are internal producers; no manuscript
closure, accepted moments, energy bound, or calendar exhaustion is asserted.

The next consumer is `ReferenceFirstLiveEmptyPendingAcceptedMoments`, using
these actual cells and atom identities for strict-past first/square moments.
-/

@[expose] public section

noncomputable section

local instance (a : Prop) : Decidable a := Classical.propDecidable a

open MeasureTheory
open scoped BigOperators
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ContinuousLearningRows
open Bandits.Support.ReferenceFirstLiveRecordingSourceBranch
open Bandits.Support.ReferenceFirstLiveRecordingReadoutMeasurability
open Bandits.Support.ReferenceContinuingLiveSlicePreparation
open Bandits.Support.ReferenceFirstLiveCoordinatorStepMeasurability
open Bandits.Support.ReferenceActivePhysicalStepMeasurability
open Bandits.Support.ReferenceLiveDispatchMeasurability

namespace Bandits.Support.ReferenceFirstLiveEmptyPendingMarkerLaw

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev RewardTable := ActualInitializationPhysicalStep.GridRewardTable
abbrev TimeControl := ContinuousLearningRows.TimeControl

variable {p : Parameters} (rate : RateInput p) (rewards : RewardTable p)
  (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T)
  (s : ℕ) (hs : s ≤ t.val) (control0 : TimeControl p)

local notation "X" => RetainedBranch rate rewards C_star C_h q t s hs control0
local notation "Z" => ReferenceTotalSourceDisintegration.SourceStratum rate rewards C_star C_h t
  (ReferenceFirstLiveRecordingSourceCylinder.stratumIndex q t s hs)
local notation "ret" => ReferenceFirstLiveRecordingSourceCylinder.sourceRetained
  rate rewards C_star C_h q t s hs control0
local notation "muZ" => ReferenceTotalSourceDisintegration.sourceStratumMeasure rate rewards C_star C_h t
  (ReferenceFirstLiveRecordingSourceCylinder.stratumIndex q t s hs)
local notation "nuX" => ReferenceRetainedSourceCoupling.retainedRemainderMeasure
  rate rewards C_star C_h q t s hs control0
local notation "inp" => actualCurrentInput rate rewards C_star C_h q t s hs control0
local notation "offset" => t.val - s

/-- Literal computed empty-pending branch on the original retained carrier. -/
def Bempty (x : X) : Prop :=
  offset > 0 ∧
    (∀ record ∈ (actualRetainedPrefixRun rate rewards C_star C_h q t s hs control0 x).records.take offset,
      ReferenceCollectionPhaseHistory.cutoffChosen record.input = false) ∧
    match (ReferenceActivePhysicalStep.prepare (inp x)).coordinator with
    | .live _ _ _ (.continuingChosen d _ _ _) =>
        d.startResult.pending = ∅ ∧ t.val + 1 < d.startResult.clock.g
    | _ => False

abbrev Xempty := {x : X // Bempty rate rewards C_star C_h q t s hs control0 x}
abbrev Zempty := {z : Z // Bempty rate rewards C_star C_h q t s hs control0 (ret z)}

local notation "Xe" => Xempty rate rewards C_star C_h q t s hs control0
local notation "Ze" => Zempty rate rewards C_star C_h q t s hs control0

/-- Inherited, unnormalized retained-source measure. -/
def nuEmpty : Measure Xe := (nuX).comap Subtype.val

/-- Inherited, unnormalized original-stratum measure. -/
def muEmpty : Measure Ze := (muZ).comap Subtype.val

local notation "nue" => nuEmpty rate rewards C_star C_h q t s hs control0
local notation "mue" => muEmpty rate rewards C_star C_h q t s hs control0

instance nuEmpty_finite : IsFiniteMeasure nue := by
  unfold nuEmpty
  infer_instance

instance muEmpty_finite : IsFiniteMeasure mue := by
  unfold muEmpty
  infer_instance

/-- Retain the same source remainder, including every original private array. -/
def xofEmpty (z : Ze) : Xe := ⟨ret z.val, z.property⟩

theorem measurable_xofEmpty :
    Measurable (xofEmpty rate rewards C_star C_h q t s hs control0) :=
  ((ReferenceFirstLiveRecordingSourceCylinder.measurable_sourceRetained
    rate rewards C_star C_h q t s hs control0).comp measurable_subtype_coe).subtype_mk

/-- Empty pending never turns a birth cell into a continuing cell. -/
theorem Bempty_offset_pos (x : Xe) : 0 < offset := x.property.1

private theorem retainedBranch_parts (x : X) :
    x.1 ∈ ReferenceFixedTimeSourceControlCoupling.fixedControlRemainderStratum p q t ∧
      x.1 ∈ ReferenceInitializationControlRemainder.launchStartRemainderEvent
        rate rewards C_star C_h q t s control0 := x.property

private theorem actualRetainedPrefixRun_records_append (x : X) :
    (actualRetainedPrefixRun rate rewards C_star C_h q t s hs control0 x).records =
      (ReferenceActivePhysicalHorizon.run (retainedSourceInitial x)
        (retainedSourceSplit x).1.2 q rewards s offset (by omega)
        (retainedSourceInitialMode x)).records ++
      [actualCurrentRecord rate rewards C_star C_h q t s hs control0 x] := by
  have helapsed := (retainedSourceFacts rate rewards C_star C_h q t s hs control0 x).2
  have hselected : ActualInitializationPhysicalStep.selectedRowIndex p
      (ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.val) = q := by
    rw [← ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex]
    exact ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_symm_coordinatorIndex
      p q t control0 x.val x.property.1
  simp only [actualRetainedPrefixRun, ReferenceFirstWindowNumericalStream.actualFirstLiveRun,
    helapsed, hselected]
  rw [ReferenceActivePhysicalHorizon.run_successor_step]
  rfl

private theorem empty_current_data
    (x : RetainedBranch rate rewards C_star C_h q t s hs control0)
    (hbranch : Bempty rate rewards C_star C_h q t s hs control0 x) :
    ∃ r owned base d hsStart c arm,
      (ReferenceActivePhysicalStep.prepare
        (actualCurrentInput rate rewards C_star C_h q t s hs control0 x)).coordinator =
        .live r owned base (.continuingChosen d hsStart c arm) ∧
      d.startResult.pending = ∅ ∧ t.val + 1 < d.startResult.clock.g := by
  rcases hbranch with ⟨_, _, hcurrent⟩
  cases hcoord : (ReferenceActivePhysicalStep.prepare
      (actualCurrentInput rate rewards C_star C_h q t s hs control0 x)).coordinator with
  | first out => simp [hcoord] at hcurrent
  | live r owned base outcome =>
      cases outcome with
      | continuingChosen d hsStart c arm =>
          simp [hcoord] at hcurrent
          exact ⟨r, owned, base, d, hsStart, c, arm, rfl, hcurrent.1, hcurrent.2⟩
      | _ => simp [hcoord] at hcurrent
  | collection payload ledger clock cutoff outcome => simp [hcoord] at hcurrent
  | invalidCollectionCutoff => simp [hcoord] at hcurrent
  | dagger => simp [hcoord] at hcurrent

private theorem empty_current_not_cutoff
    (x : RetainedBranch rate rewards C_star C_h q t s hs control0)
    (hbranch : Bempty rate rewards C_star C_h q t s hs control0 x) :
    ReferenceCollectionPhaseHistory.cutoffChosen
      (actualCurrentInput rate rewards C_star C_h q t s hs control0 x) = false := by
  obtain ⟨r, owned, base, d, hsStart, c, arm, hcoord, _, _⟩ :=
    empty_current_data rate rewards C_star C_h q t s hs control0 x hbranch
  simp [ReferenceCollectionPhaseHistory.cutoffChosen, hcoord]

theorem actualRetainedPrefixRun_current_in_firstLiveWindow
    (x : RetainedBranch rate rewards C_star C_h q t s hs control0)
    (hbranch : Bempty rate rewards C_star C_h q t s hs control0 x) :
    ∃ hn : t.val - s < (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (actualRetainedPrefixRun rate rewards C_star C_h q t s hs control0 x).records).length,
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (actualRetainedPrefixRun rate rewards C_star C_h q t s hs control0 x).records)[t.val - s]'hn =
        actualCurrentRecord rate rewards C_star C_h q t s hs control0 x := by
  let n := t.val - s
  let z := ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.1
  let initial := ReferenceFirstLaunchNumericalCell.launchState rate z rewards C_star C_h
    (retainedSourceFacts rate rewards C_star C_h q t s hs control0 x).1
  let hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial s := by
    rcases retainedSourceFacts rate rewards C_star C_h q t s hs control0 x with
      ⟨_, helapsed⟩
    simpa only [helapsed] using
      (actualRetainedSeed rate rewards C_star C_h q t s hs control0 x).activeAtStart
  let preRun := ReferenceActivePhysicalHorizon.run initial z.1.2 q rewards s n
    (by omega) hmode
  have hrecords := actualRetainedPrefixRun_records_append rate rewards C_star C_h
    q t s hs control0 x
  have hrecords' :
      (actualRetainedPrefixRun rate rewards C_star C_h q t s hs control0 x).records =
        preRun.records ++ [actualCurrentRecord rate rewards C_star C_h q t s hs control0 x] := by
    simpa only [preRun, initial, z, n, retainedSourceInitial, retainedSourceSplit] using hrecords
  have hprefixLength : preRun.records.length = n := by
    dsimp [preRun, n]
    exact ReferenceActivePhysicalHorizon.run_record_count initial z.1.2 q rewards s
      (t.val - s) (by omega) hmode
  have htake :
      (actualRetainedPrefixRun rate rewards C_star C_h q t s hs control0 x).records.take n =
        preRun.records := by
    rw [hrecords']
    rw [List.take_append_of_le_length (by omega : n ≤ preRun.records.length)]
    exact List.take_of_length_le (by omega : preRun.records.length ≤ n)
  have hpast := hbranch.2.1
  have hall : ∀ record ∈ preRun.records ++
      [actualCurrentRecord rate rewards C_star C_h q t s hs control0 x],
      (!ReferenceCollectionPhaseHistory.cutoffChosen record.input) = true := by
    intro record hrecord
    rcases List.mem_append.mp hrecord with hprefixRecord | hcurrentRecord
    · have hcut := hpast record (by rw [htake]; exact hprefixRecord)
      simp [hcut]
    · simp only [List.mem_singleton] at hcurrentRecord
      rcases hcurrentRecord with rfl
      have hcurrent := empty_current_not_cutoff rate rewards C_star C_h
        q t s hs control0 x hbranch
      change (!ReferenceCollectionPhaseHistory.cutoffChosen
        (actualCurrentInput rate rewards C_star C_h q t s hs control0 x)) = true
      simp [hcurrent]
  have hwindow : ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (actualRetainedPrefixRun rate rewards C_star C_h q t s hs control0 x).records =
      preRun.records ++ [actualCurrentRecord rate rewards C_star C_h q t s hs control0 x] := by
    change List.takeWhile _ _ = _
    rw [hrecords']
    exact List.takeWhile_eq_self_iff.mpr hall
  rw [hwindow]
  refine ⟨by simp [hprefixLength, n], ?_⟩
  simp [hprefixLength, n]

theorem actual_current_cell
    (x : RetainedBranch rate rewards C_star C_h q t s hs control0)
    (hbranch : Bempty rate rewards C_star C_h q t s hs control0 x) :
    Nonempty (ReferenceFirstWindowNumericalStream.ActualLiveSourceCell
      (actualCurrentRecord rate rewards C_star C_h q t s hs control0 x)) := by
  let z := ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.1
  rcases retainedSourceFacts rate rewards C_star C_h q t s hs control0 x with
    ⟨hc, helapsed⟩
  let n := t.val - s
  have hspan : s + (n + 1) ≤ p.T := by dsimp [n]; omega
  have hNspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed +
        (n + 1) ≤ p.T := by rw [helapsed]; exact hspan
  have hwindowIndex := actualRetainedPrefixRun_current_in_firstLiveWindow
    rate rewards C_star C_h q t s hs control0 x hbranch
  have hparts := retainedBranch_parts rate rewards C_star C_h q t s hs control0 x
  have hselected : ActualInitializationPhysicalStep.selectedRowIndex p z = q := by
    calc
      ActualInitializationPhysicalStep.selectedRowIndex p z =
          ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p z :=
        (ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex
          p z).symm
      _ = q := ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_symm_coordinatorIndex
        p q t control0 x.1 hparts.1
  have hrun : actualRetainedPrefixRun rate rewards C_star C_h q t s hs control0 x =
      ReferenceFirstWindowNumericalStream.actualFirstLiveRun rate z rewards C_star C_h hc
        (n + 1) hNspan := by
    simp [actualRetainedPrefixRun,
      ReferenceFirstWindowNumericalStream.actualFirstLiveRun,
      z, n]
  let hwindowControl : ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (actualRetainedPrefixRun rate rewards C_star C_h q t s hs control0 x).records =
    ReferenceFirstWindowNumericalStream.actualFirstLiveWindow rate z rewards C_star C_h hc
      (n + 1) hNspan := by
    exact congrArg (fun run : ReferenceActivePhysicalHorizon.Run _ =>
      ReferenceFirstLiveConfirmationHistory.firstLiveWindow run.records) hrun
  let k : Fin (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow rate z rewards C_star C_h hc
      (n + 1) hNspan).length :=
    ⟨n, by simpa [hwindowControl] using hwindowIndex.1⟩
  have hrecord :
      (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow rate z rewards C_star C_h hc
        (n + 1) hNspan)[k.val] =
          actualCurrentRecord rate rewards C_star C_h q t s hs control0 x := by
    simpa only [k, hwindowControl] using hwindowIndex.2
  obtain ⟨cell, _, _, _, _⟩ :=
    ReferenceFirstWindowNumericalStream.actual_first_live_source_cell rate z rewards C_star C_h
      hc (n + 1) hNspan k
  rw [hrecord] at cell
  exact ⟨cell⟩

private theorem actual_current_prepared_followers
    (x : X) (hbranch : Bempty rate rewards C_star C_h q t s hs control0 x) :
    ∃ states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta,
      ∃ memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p,
        ∀ i, ((ReferenceActivePhysicalStep.prepare (inp x)).followers.followers i).configuration =
          .ordinary (states i) (memories i) := by
  obtain ⟨cell⟩ := actual_current_cell rate rewards C_star C_h q t s hs control0 x hbranch
  exact ⟨cell.states, cell.memories, cell.ordinary⟩

theorem actual_empty_recording_inputs
    (x : X) (hbranch : Bempty rate rewards C_star C_h q t s hs control0 x) :
    let initial := retainedSourceInitial x
    let seed := actualRetainedSeed rate rewards C_star C_h q t s hs control0 x
    ∃ states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta,
      ∃ memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p,
      ∃ _ho : ∀ i, ((ReferenceActivePhysicalStep.prepare (inp x)).followers.followers i).configuration =
        .ordinary (states i) (memories i),
      ∃ r owned base d hsStart c arm,
      ∃ _hcoord : (ReferenceActivePhysicalStep.prepare (inp x)).coordinator =
        .live r owned base (.continuingChosen d hsStart c arm),
      ∃ _henabled : (inp x).time.val + 1 < d.startResult.clock.g,
        initial.coordinator = .first ∧
        (∀ i, initial.followers i = .ordinary (seed.followers i) (seed.memory i)) ∧
        (∀ i, (seed.followers i).status = .unoccupied) ∧
        (∀ i, ActiveFollowerLifecycle.localBufferValid (seed.followers i)) ∧
        (∀ i, (seed.followers i).buffer.Pairwise
          (fun a b => a.calendarRound < b.calendarRound)) ∧
        (∀ i saved, saved ∈ (seed.followers i).buffer → saved.calendarRound ≤ s) := by
  intro initial seed
  obtain ⟨states, memories, ho⟩ :=
    actual_current_prepared_followers rate rewards C_star C_h q t s hs control0 x hbranch
  obtain ⟨r, owned, base, d, hsStart, c, arm, hcoord, _, henabled⟩ :=
    empty_current_data rate rewards C_star C_h q t s hs control0 x hbranch
  have htime : (inp x).time.val = t.val := by
    change s + (t.val - s) = t.val
    omega
  refine ⟨states, memories, ho, r, owned, base, d, hsStart, c, arm, hcoord,
    by simpa only [htime] using henabled, seed.coordinatorFirst, seed.configuration,
    seed.unoccupied, seed.bufferValid, seed.chronologicalBuffer, ?_⟩
  intro i saved hsaved
  have h := seed.bufferStamps i saved hsaved
  rw [(retainedSourceFacts rate rewards C_star C_h q t s hs control0 x).2] at h
  exact h

/-- Presence is produced from the actual continuing constructor. -/
theorem selection_present (x : Xe) :
    ((ReferenceActivePhysicalStep.prepare (inp x.val)).coordinator.selection).isSome = true := by
  obtain ⟨r, owned, base, d, hsStart, c, arm, hcoord, _, _⟩ :=
    empty_current_data rate rewards C_star C_h q t s hs control0 x.val x.property
  simp [hcoord, ReferenceActivePhysicalStep.DispatchCut.selection,
    ReferenceActivePhysicalStep.selectionAt]

/-- The unique present optional selection of the actual baseline PREPARE. -/
def selEmpty (x : Xe) : ReferenceActivePhysicalStep.Selection (inp x.val) :=
  ((ReferenceActivePhysicalStep.prepare (inp x.val)).coordinator.selection).get
    (selection_present rate rewards C_star C_h q t s hs control0 x)

/-- The getter reads the same actual registers; it does not choose a witness. -/
theorem selEmpty_payload_eq (x : Xe) :
    ∀ r owned base d hsStart c arm,
      (ReferenceActivePhysicalStep.prepare (inp x.val)).coordinator =
        .live r owned base (.continuingChosen d hsStart c arm) →
      (selEmpty rate rewards C_star C_h q t s hs control0 x).view.payload = r.payload := by
  intro r owned base d hsStart c arm hcoord
  simp [selEmpty, hcoord, ReferenceActivePhysicalStep.DispatchCut.selection,
    ReferenceActivePhysicalStep.selectionAt]

/-- Canonical rate at the anchor of that actual baseline selection. -/
def xiEmpty (x : Xe) (j : Fin p.K) : ℝ :=
  CanonicalRecordingRates.xi p rate.eta.val
    (selEmpty rate rewards C_star C_h q t s hs control0 x).view.payload.anchor j

/-- Actual physical marker after replacing exactly the whole current control. -/
def currentEmptyMarker (xu : Xe × TimeControl p) : Option (Fin p.K) :=
  ReferenceContinuingRecordingFastPair.physicalMarkerOnRecord
    (sourceRecordAtControl xu.1.val xu.2)
    (selEmpty rate rewards C_star C_h q t s hs control0 xu.1).view.payload true

/-- The complete operational telescope is discharged by the same actual seed
and window. In particular no follower is assumed pending for RELEASE. -/
theorem currentEmptyMarker_masses (x : Xe) :
    (∀ j : Fin p.K, timeControlLaw p {u | currentEmptyMarker
      rate rewards C_star C_h q t s hs control0 (x, u) = some j} =
      ENNReal.ofReal (xiEmpty rate rewards C_star C_h q t s hs control0 x j)) ∧
    timeControlLaw p {u | currentEmptyMarker rate rewards C_star C_h q t s hs control0 (x, u) = none} =
      ENNReal.ofReal (1 - ∑ j : Fin p.K, xiEmpty rate rewards C_star C_h q t s hs control0 x j) := by
  obtain ⟨states, memories, ho, r, owned, base, d, hsStart, c, arm, hcoord,
      henabled, hfirst, hseed, hunoccupied, hvalid, hpairwise, htime⟩ :=
    actual_empty_recording_inputs rate rewards C_star C_h q t s hs control0 x.val x.property
  have hpayload := selEmpty_payload_eq rate rewards C_star C_h q t s hs control0 x
    r owned base d hsStart c arm hcoord
  have hlaw := ReferenceContinuingRecordingFastLaw.actual_continuing_live_joint_law
    (retainedSourceInitial x.val) (retainedSourceSplit x.val).1.2 q rewards s
    (t.val - s) (retainedSourceCurrentSpan hs) (retainedSourceInitialMode x.val)
    (actualRetainedSeed rate rewards C_star C_h q t s hs control0 x.val).followers
    (actualRetainedSeed rate rewards C_star C_h q t s hs control0 x.val).memory
    hfirst hseed hunoccupied hvalid hpairwise htime
    r owned base d hsStart c arm hcoord states memories ho henabled
  rcases hlaw with ⟨hpair, _, _, _, _, hsome, hnone, _, _⟩
  rw [Measure.map_map measurable_fst hpair] at hsome hnone
  have hmarker : (fun u : TimeControl p =>
      currentEmptyMarker rate rewards C_star C_h q t s hs control0 (x, u)) =
      ReferenceContinuingRecordingFastPair.candidatePhysicalMarker
        (retainedSourceInitial x.val) (retainedSourceSplit x.val).1.2 q rewards s (t.val - s)
        (retainedSourceCurrentSpan hs) (retainedSourceInitialMode x.val) r.payload true := by
    funext u
    unfold currentEmptyMarker
    rw [hpayload, sourcePhysicalMarker_eq_candidatePhysicalMarker]
    rfl
  have hmeas : Measurable (fun u : TimeControl p =>
      currentEmptyMarker rate rewards C_star C_h q t s hs control0 (x, u)) := by
    rw [hmarker]
    exact measurable_fst.comp hpair
  simp only [Function.comp_def,
    ReferenceContinuingRecordingFastPair.candidatePhysicalFastPair] at hsome hnone
  constructor
  · intro j
    have h := hsome j
    rw [← hmarker, Measure.map_apply hmeas (measurableSet_singleton _)] at h
    simpa only [xiEmpty, hpayload, Set.preimage, Set.mem_singleton_iff] using h
  · rw [← hmarker, Measure.map_apply hmeas (measurableSet_singleton _)] at hnone
    simpa only [xiEmpty, hpayload, Set.preimage, Set.mem_singleton_iff] using hnone

/-- Transport of the actual constructor for every original current control. -/
theorem original_selection_data (z : Ze) :
    ((ReferenceActivePhysicalStep.prepare
      (ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord
        rate rewards C_star C_h q t s hs control0 z.val).input).coordinator.selection).map
      (fun selected => (selected.view.payload, selected.started)) =
    some ((selEmpty rate rewards C_star C_h q t s hs control0
      (xofEmpty rate rewards C_star C_h q t s hs control0 z)).view.payload,
      (selEmpty rate rewards C_star C_h q t s hs control0
        (xofEmpty rate rewards C_star C_h q t s hs control0 z)).started) := by
  let x := xofEmpty rate rewards C_star C_h q t s hs control0 z
  obtain ⟨r, owned, base, d, hsStart, c, arm, hcoord, _, _⟩ :=
    empty_current_data rate rewards C_star C_h q t s hs control0 x.val x.property
  obtain ⟨cu, au, hu⟩ := continuing_cut_at_control (inp x.val)
    r owned base d hsStart c arm hcoord
    (ReferenceFirstLiveRecordingSourceCylinder.originalControl rate rewards C_star C_h q t s hs z.val)
  have hpayload : ((ReferenceActivePhysicalStep.prepare
      (inputAtControl (inp x.val)
        (ReferenceFirstLiveRecordingSourceCylinder.originalControl
          rate rewards C_star C_h q t s hs z.val))).coordinator.selection).map
        (fun selected => (selected.view.payload, selected.started)) = some (r.payload, d.startResult) := by
    simp [hu, ReferenceActivePhysicalStep.DispatchCut.selection,
      ReferenceActivePhysicalStep.selectionAt]
  have horiginal := ReferenceFirstLiveRecordingSourceCylinder.sourceInputAtControl_eq_original
    rate rewards C_star C_h q t s hs control0 z.val
  change inputAtControl (inp x.val) _ = _ at horiginal
  rw [horiginal] at hpayload
  have hbaseline : (selEmpty rate rewards C_star C_h q t s hs control0 x).view.payload = r.payload ∧
      (selEmpty rate rewards C_star C_h q t s hs control0 x).started = d.startResult := by
    simp [selEmpty, hcoord, ReferenceActivePhysicalStep.DispatchCut.selection,
      ReferenceActivePhysicalStep.selectionAt]
  rw [hbaseline.1, hbaseline.2]
  exact hpayload

/-- Presence on the ORIGINAL PREPARE, produced by actual control transport. -/
theorem original_selection_present (z : Ze) :
    ((ReferenceActivePhysicalStep.prepare
      (ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord
        rate rewards C_star C_h q t s hs control0 z.val).input).coordinator.selection).isSome = true := by
  have h := original_selection_data rate rewards C_star C_h q t s hs control0 z
  exact Option.isSome_iff_ne_none.mpr (fun hn => by rw [hn] at h; cases h)

/-- The original current selection is obtained by the same proof-backed getter. -/
def originalSelEmpty (z : Ze) :=
  ((ReferenceActivePhysicalStep.prepare
    (ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord
      rate rewards C_star C_h q t s hs control0 z.val).input).coordinator.selection).get
    (original_selection_present rate rewards C_star C_h q t s hs control0 z)

theorem originalSelEmpty_payload_eq (z : Ze) :
    (originalSelEmpty rate rewards C_star C_h q t s hs control0 z).view.payload =
      (selEmpty rate rewards C_star C_h q t s hs control0
        (xofEmpty rate rewards C_star C_h q t s hs control0 z)).view.payload := by
  have h := original_selection_data rate rewards C_star C_h q t s hs control0 z
  have hget := Option.some_get (original_selection_present
    rate rewards C_star C_h q t s hs control0 z)
  rw [← hget] at h
  exact congrArg Prod.fst (Option.some.inj h)

/-- Original PREPARE preserves the entire start-result, including clock and pending. -/
theorem originalSelEmpty_started_eq (z : Ze) :
    (originalSelEmpty rate rewards C_star C_h q t s hs control0 z).started =
      (selEmpty rate rewards C_star C_h q t s hs control0
        (xofEmpty rate rewards C_star C_h q t s hs control0 z)).started := by
  have h := original_selection_data rate rewards C_star C_h q t s hs control0 z
  rw [← Option.some_get (original_selection_present rate rewards C_star C_h q t s hs control0 z)] at h
  exact congrArg Prod.snd (Option.some.inj h)

/-- The actual baseline selection has empty pending and is strictly enabled. -/
theorem selEmpty_started_empty (x : Xe) :
    (selEmpty rate rewards C_star C_h q t s hs control0 x).started.pending = ∅ ∧
    t.val + 1 < (selEmpty rate rewards C_star C_h q t s hs control0 x).started.clock.g := by
  obtain ⟨r, owned, base, d, hsStart, c, arm, hcoord, hpending, henabled⟩ :=
    empty_current_data rate rewards C_star C_h q t s hs control0 x.val x.property
  simpa only [selEmpty, hcoord, ReferenceActivePhysicalStep.DispatchCut.selection,
    ReferenceActivePhysicalStep.selectionAt, dite_true, Option.get_some] using And.intro hpending henabled

/-- Literal actual marker, with the ORIGINAL record and ORIGINAL selected payload. -/
def actualEmptyMarker (z : Ze) : Option (Fin p.K) :=
  ReferenceContinuingRecordingFastPair.physicalMarkerOnRecord
    (ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord
      rate rewards C_star C_h q t s hs control0 z.val)
    (originalSelEmpty rate rewards C_star C_h q t s hs control0 z).view.payload true

theorem actualEmptyMarker_eq_control (z : Ze) :
    actualEmptyMarker rate rewards C_star C_h q t s hs control0 z =
      currentEmptyMarker rate rewards C_star C_h q t s hs control0
        (xofEmpty rate rewards C_star C_h q t s hs control0 z,
          ReferenceFirstLiveRecordingSourceCylinder.originalControl rate rewards C_star C_h q t s hs z.val) := by
  unfold actualEmptyMarker currentEmptyMarker
  rw [originalSelEmpty_payload_eq]
  dsimp only [xofEmpty, Prod.fst, Prod.snd]
  rw [ReferenceFirstLiveRecordingSourceCylinder.sourceRecordAtControl_eq_original]


section Borel

open Bandits.Support.ReferenceLiveDispatchOutputMeasurability
open Bandits.Support.ReferenceActiveHorizonMeasurability

omit rate rewards C_star C_h q t s hs control0 in
/-- A literal predicate on the actual LIVE dispatch observation. -/
private def preparedEvent {rate : RateInput p} (P : OutcomeData p → Prop)
    (x : ReferenceActivePhysicalStep.RoundInput p rate) : Prop :=
  match (ReferenceActivePhysicalStep.prepare x).coordinator with
  | .live _ _ _ outcome => P (outcomeData outcome)
  | _ => False

omit rate rewards C_star C_h q t s hs control0 in
private theorem preparedEvent_live_iff {rate : RateInput p} (P : OutcomeData p → Prop)
    (x : LiveInput p rate) :
    preparedEvent P x.val ↔ P (dispatchObservation (liveCoordinates x)).2 := by
  have hdata := outcomeData_originalInput x.val (liveRegisters x) (liveOwned x) (liveBase x)
  change preparedEvent P x.val ↔ P (outcomeData (CoordinatorRoundDispatch.dispatchLive
    (liveInputOfCoordinates (liveCoordinates x))))
  unfold liveCoordinates
  rw [hdata]
  unfold preparedEvent ReferenceActivePhysicalStep.prepare
  dsimp only
  rw [live_dispatch_eq x]

omit rate rewards C_star C_h q t s hs control0 in
private theorem preparedEvent_mem_liveSet {rate : RateInput p} (P : OutcomeData p → Prop)
    (x : ReferenceActivePhysicalStep.RoundInput p rate) (hx : preparedEvent P x) :
    x ∈ liveSet := by
  cases hstate : x.state.coordinator with
  | first =>
      have hd : ReferenceActivePhysicalStep.dispatch x =
          .first (CoordinatorRoundDispatch.dispatchFirst (ReferenceActivePhysicalStep.firstInput x)) := by
        rw [ReferenceActivePhysicalStep.dispatch, hstate, CoordinatorRoundDispatch.dispatch]
        rfl
      simp only [preparedEvent, ReferenceActivePhysicalStep.prepare, hd] at hx
  | live r owned base =>
      exact ⟨(r.payload, encodeLive r owned base), by
        simp [encodeState, encodeCoordinator, hstate]⟩
  | collection payload ledger proposal =>
      by_cases hv : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
      · let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
        let clock := ReferenceActivePhysicalStep.collectionClock payload ledger proposal cutoff
        have hd : ReferenceActivePhysicalStep.dispatch x =
            .collection payload ledger clock cutoff
              (CoordinatorRoundDispatch.dispatchCollection
                (ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff)) := by
          rw [ReferenceActivePhysicalStep.dispatch, hstate]
          simp only [dite_eq_left hv, CoordinatorRoundDispatch.dispatch]
          rfl
        simp only [preparedEvent, ReferenceActivePhysicalStep.prepare, hd] at hx
      · simp [preparedEvent, ReferenceActivePhysicalStep.prepare,
          ReferenceActivePhysicalStep.dispatch, hstate, hv] at hx
  | dagger =>
      simp [preparedEvent, ReferenceActivePhysicalStep.prepare,
        ReferenceActivePhysicalStep.dispatch, hstate] at hx

omit rate rewards C_star C_h q t s hs control0 in
private theorem measurableSet_preparedEvent {rate : RateInput p} (P : OutcomeData p → Prop) :
    MeasurableSet {x : ReferenceActivePhysicalStep.RoundInput p rate | preparedEvent P x} := by
  have hsub : MeasurableSet {x : LiveInput p rate | preparedEvent P x.val} := by
    have h := (measurable_of_countable P).comp
      (measurable_snd.comp (measurable_liveDispatchObservation (rate := rate)))
    simpa only [Function.comp_apply, ← preparedEvent_live_iff] using h.setOf
  have himage := (MeasurableEmbedding.subtype_coe measurableSet_liveSet).measurableSet_image.mpr hsub
  convert himage using 1
  ext x
  constructor
  · intro hx
    exact ⟨⟨x, preparedEvent_mem_liveSet P x hx⟩, hx, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact hy

omit rate rewards C_star C_h q t s hs control0 in
private def cutoffEvent (outcome : OutcomeData p) : Prop :=
  match outcome with
  | .cutoffChosen .. => True
  | _ => False

omit rate rewards C_star C_h q t s hs control0 in
private theorem measurableSet_not_cutoff {rate : RateInput p} :
    MeasurableSet {x : ReferenceActivePhysicalStep.RoundInput p rate |
      ReferenceCollectionPhaseHistory.cutoffChosen x = false} := by
  have h := (measurableSet_preparedEvent (rate := rate) (cutoffEvent (p := p))).compl
  convert h using 1
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_compl_iff]
  unfold preparedEvent ReferenceCollectionPhaseHistory.cutoffChosen
  cases (ReferenceActivePhysicalStep.prepare x).coordinator with
  | live r owned base outcome => cases outcome <;> dsimp only [outcomeData, cutoffEvent] <;> decide
  | first outcome =>
      change (false = false ↔ ¬ False)
      exact iff_of_true rfl not_false
  | collection payload ledger clock cutoff outcome =>
      change (false = false ↔ ¬ False)
      exact iff_of_true rfl not_false
  | invalidCollectionCutoff =>
      change (false = false ↔ ¬ False)
      exact iff_of_true rfl not_false
  | dagger =>
      change (false = false ↔ ¬ False)
      exact iff_of_true rfl not_false

omit rate rewards C_star C_h q t s hs control0 in
private theorem measurable_candidateInput {rate : RateInput p} (start count : ℕ)
    (hspan : start + (count + 1) ≤ p.T) :
    Measurable (fun input : ActiveRunInput (p := p) (rate := rate) start =>
      ReferenceContinuingDataCandidateLogging.candidateInput input.val.1 input.val.2.1
        input.val.2.2.1 input.val.2.2.2 start count hspan input.property) := by
  have hd := (measurable_subtype_coe : Measurable
    (Subtype.val : ActiveRunInput (p := p) (rate := rate) start → _))
  have hr := measurable_runFinalState (p := p) (rate := rate) start count (le_trans (Nat.le_succ _) hspan)
  have hcoordinates : Measurable (fun input : ActiveRunInput (p := p) (rate := rate) start =>
      ((runOfInput start count (le_trans (Nat.le_succ _) hspan) input).finalState,
        (input.val.2.1, (input.val.2.2.1, ((⟨start + count, by omega⟩ : Fin p.T), input.val.2.2.2))))) :=
    hr.prodMk ((measurable_fst.comp (measurable_snd.comp hd)).prodMk
    ((measurable_fst.comp (measurable_snd.comp (measurable_snd.comp hd))).prodMk
      (measurable_const.prodMk
        (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp hd))))))
  apply measurable_comap_iff.mpr
  exact hcoordinates.subtype_mk

omit rate rewards C_star C_h q t s hs control0 in
private theorem run_records_succ {rate : RateInput p} (start count : ℕ)
    (hspan : start + (count + 1) ≤ p.T)
    (input : ActiveRunInput (p := p) (rate := rate) start) :
    (runOfInput start (count + 1) hspan input).records =
      (runOfInput start count (le_trans (Nat.le_succ _) hspan) input).records ++
      [⟨ReferenceContinuingDataCandidateLogging.candidateInput input.val.1 input.val.2.1
          input.val.2.2.1 input.val.2.2.2 start count hspan input.property,
        ReferenceActivePhysicalStep.step _, rfl⟩] := by
  unfold runOfInput
  rw [ReferenceActivePhysicalHorizon.run_successor,
    ReferenceActivePhysicalHorizon.foldCalendar,
    ReferenceActivePhysicalHorizon.calendarEntries_one start (start + count) (Nat.le_add_right _ _) hspan]
  rfl

omit rate rewards C_star C_h q t s hs control0 in
private theorem measurableSet_run_cutoff_free {rate : RateInput p} (start count : ℕ)
    (hspan : start + count ≤ p.T) :
    MeasurableSet {input : ActiveRunInput (p := p) (rate := rate) start |
      ∀ record ∈ (runOfInput start count hspan input).records,
        ReferenceCollectionPhaseHistory.cutoffChosen record.input = false} := by
  induction count with
  | zero =>
      simp only [runOfInput, ReferenceActivePhysicalHorizon.run_zero_records,
        List.not_mem_nil, false_implies, implies_true, Set.ofPred_true, MeasurableSet.univ]
  | succ count ih =>
      have hc := (measurableSet_not_cutoff (rate := rate)).preimage
        (measurable_candidateInput start count hspan)
      convert (ih (le_trans (Nat.le_succ _) hspan)).inter hc using 1
      ext input
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage]
      rw [run_records_succ start count hspan input]
      simp only [List.forall_mem_append, List.forall_mem_cons, List.not_mem_nil,
        false_implies, implies_true, and_true]

omit rate rewards C_star C_h q t s hs control0 in
private def emptyOutcomeEvent (round : ℕ) (outcome : OutcomeData p) : Prop :=
  match outcome with
  | .continuingChosen dispatched _ _ =>
      dispatched.1.pending = ∅ ∧ round < dispatched.1.clock.g
  | _ => False

/-- Borel producer for the LITERAL branch, including the actual strict past. -/
theorem measurableSet_Bempty :
    MeasurableSet {x : X | Bempty rate rewards C_star C_h q t s hs control0 x} := by
  let runInput : X → ActiveRunInput (p := p) (rate := rate) s :=
    fun x => ⟨(ReferenceRetainedBoundaryMeasurability.retainedGeneratedActiveSeed
      rate rewards C_star C_h q t s hs control0 x,
      ((ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.val).1.2, (q, rewards))),
      (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
        rate rewards C_star C_h q t control0 x.val x.property.1 s hs x.property.2).2.1⟩
  have hsource : Measurable (fun x : X =>
      ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.val) :=
    (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).symm.measurable.comp
      (measurable_const.prodMk measurable_subtype_coe)
  have hinput : Measurable runInput :=
    ((ReferenceRetainedBoundaryMeasurability.measurable_retainedGeneratedActiveSeed
      rate rewards C_star C_h q t s hs control0).prodMk
      ((measurable_snd.comp (measurable_fst.comp hsource)).prodMk
        (measurable_const.prodMk measurable_const))).subtype_mk
  have hpast := (measurableSet_run_cutoff_free (p := p) (rate := rate) s offset (by omega)).preimage hinput
  have hactual : Measurable inp := by
    convert ReferenceRetainedBoundaryMeasurability.measurable_retainedIncomingBoundary
      rate rewards C_star C_h q t s hs control0 using 1
    funext x
    exact actualCurrentInput_eq_retainedIncomingBoundary rate rewards C_star C_h q t s hs control0 x
  have hcurrent := (measurableSet_preparedEvent (rate := rate)
    (emptyOutcomeEvent (p := p) (t.val + 1))).preimage hactual
  have hpositive : MeasurableSet {x : X | offset > 0} := by
    by_cases h : offset > 0 <;> simp only [h, Set.ofPred_true, Set.ofPred_false] <;> measurability
  convert hpositive.inter (hpast.inter hcurrent) using 1
  ext x
  have hseed := ReferenceFirstLiveRecordingBranchMeasurability.retainedGeneratedActiveSeed_eq_launchState
    rate rewards C_star C_h q t s hs control0 x
  have happend := actualRetainedPrefixRun_records_append rate rewards C_star C_h q t s hs control0 x
  have hlen := ReferenceActivePhysicalHorizon.run_record_count
    (retainedSourceInitial x) (retainedSourceSplit x).1.2 q rewards s offset
    (by omega) (retainedSourceInitialMode x)
  have htake : (actualRetainedPrefixRun rate rewards C_star C_h q t s hs control0 x).records.take offset =
      (runOfInput s offset (by omega) (runInput x)).records := by
    rw [happend, List.take_append_of_le_length (by simpa using Nat.le_of_eq hlen.symm)]
    rw [List.take_of_length_le (by simpa using Nat.le_of_eq hlen)]
    dsimp only [runOfInput, runInput, retainedSourceInitial, retainedSourceSplit]
    cases hseed
    rfl
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, Bempty, htake]
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  unfold preparedEvent emptyOutcomeEvent
  cases (ReferenceActivePhysicalStep.prepare (inp x)).coordinator with
  | live r owned base outcome => cases outcome <;> rfl
  | first outcome => rfl
  | collection payload ledger clock cutoff outcome => rfl
  | invalidCollectionCutoff => rfl
  | dagger => rfl

end Borel


section Readouts

local instance : Countable ActiveRoundActions.FollowerStatus :=
  (Function.LeftInverse.injective
    FollowerDownMeasurability.followerStatusOfCode_code).countable

variable {rate rewards C_star C_h q t s hs control0}

/-- Literal payload projection of the actual optional-selection getter. -/
def selectedBaselinePayload (x : Xe) : ReferenceActivePhysicalStep.Payload rate :=
  (selEmpty rate rewards C_star C_h q t s hs control0 x).view.payload

private theorem payloadOption_eq_some (x : Xe) :
    sourceSelectionPayloadOption x.val = some (selectedBaselinePayload x) := by
  obtain ⟨r, owned, base, d, hsStart, c, arm, hcoord, _, _⟩ :=
    empty_current_data rate rewards C_star C_h q t s hs control0 x.val x.property
  have hpayload := selEmpty_payload_eq rate rewards C_star C_h q t s hs control0 x
    r owned base d hsStart c arm hcoord
  unfold sourceSelectionPayloadOption
  rw [(ReferenceActiveStepCompositionMeasurability.wholeStepCode_front (sourceCurrentInput x.val)).1]
  change ((ReferenceActivePhysicalStep.prepare (inp x.val)).coordinator.selection.map
    ReferenceLiveDispatchOutputMeasurability.encodeSelection).map _ = _
  simp [hcoord, selectedBaselinePayload, hpayload, ReferenceActivePhysicalStep.DispatchCut.selection,
    ReferenceActivePhysicalStep.selectionAt, ReferenceLiveDispatchOutputMeasurability.encodeSelection]

private theorem measurable_get_of_always_some {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (f : β → Option α) (hf : Measurable f)
    (hSome : ∀ x, ∃ a, f x = some a) :
    Measurable (fun x => (f x).get (by
      obtain ⟨a, ha⟩ := hSome x
      simp [ha])) := by
  let : MeasurableSpace (Option α) :=
    LaterAssignmentStartMeasurability.optionMeasurableSpace
  have hEquiv : Measurable (Equiv.optionEquivSumPUnit α) := comap_measurable _
  intro s hs
  have hSomeImage : MeasurableSet (some '' s : Set (Option α)) := by
    have hleft : MeasurableSet (Sum.inl '' s : Set (α ⊕ PUnit)) := hs.inl_image
    have hset : (some '' s : Set (Option α)) =
        (Equiv.optionEquivSumPUnit α) ⁻¹' (Sum.inl '' s) := by
      ext option
      cases option <;> simp [Equiv.optionEquivSumPUnit]
    rw [hset]
    exact hleft.preimage hEquiv
  have hpre : {x | (f x).get (by
      obtain ⟨a, ha⟩ := hSome x
      simp [ha]) ∈ s} = f ⁻¹' (some '' s) := by
    ext x
    obtain ⟨a, ha⟩ := hSome x
    simp [ha]
  change MeasurableSet {x | (f x).get (by
    obtain ⟨a, ha⟩ := hSome x
    simp [ha]) ∈ s}
  rw [hpre]
  exact hSomeImage.preimage hf

/-- The actual selected payload is Borel on the empty branch. -/
theorem measurable_selectedBaselinePayload :
    Measurable (selectedBaselinePayload (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) (q := q) (t := t) (s := s)
      (hs := hs) (control0 := control0)) := by
  have hget := measurable_get_of_always_some
    (fun x : Xe => sourceSelectionPayloadOption x.val)
    (measurable_sourceSelectionPayloadOption.comp measurable_subtype_coe)
    (fun x => ⟨selectedBaselinePayload x, payloadOption_eq_some x⟩)
  convert hget using 1
  funext x
  simp only [payloadOption_eq_some, Option.get_some]

/-- The baseline payload's literal derived rate vector remains Borel as it
varies with the actual selected payload. -/
theorem measurable_selectedBaselineInputRate :
    Measurable (fun x : Xe =>
      AssignmentPayloadDerivedMeasurability.inputRate
        (selectedBaselinePayload x)) :=
  AssignmentPayloadDerivedMeasurability.measurable_inputRate.comp
    measurable_selectedBaselinePayload

/-- The baseline payload's literal natural exponent vector remains Borel as
it varies with the actual selected payload. -/
theorem measurable_selectedBaselineInputExponent :
    Measurable (fun x : Xe =>
      AssignmentPayloadDerivedMeasurability.inputExponent
        (selectedBaselinePayload x)) :=
  AssignmentPayloadDerivedMeasurability.measurable_inputExponent.comp
    measurable_selectedBaselinePayload

/-- The actual selected payload's canonical assigned arm at follower `i`.
The arm is read from its literal slow-set assignment. -/
def selectedBaselineAssignedArm (i : Fin (p.m - 1))
    (x : Xe) : Fin p.K :=
  (selectedBaselinePayload x).assignment.assigned i

/-- The canonical arm assignment remains measurable as the retained source
varies, by the existing measurable slow-set payload projection. -/
theorem measurable_selectedBaselineAssignedArm (i : Fin (p.m - 1)) :
    Measurable (selectedBaselineAssignedArm (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) (q := q) (t := t) (s := s)
      (hs := hs) (control0 := control0) i) := by
  change Measurable (fun x : Xe =>
    CanonicalAssignmentVector.followerArm p.two_le_m
      (selectedBaselinePayload x).slowSet i)
  have harm : Measurable (fun slowSet : CanonicalOrientedSetLaw.SlowSet p.K p.m =>
      CanonicalAssignmentVector.followerArm p.two_le_m slowSet i) :=
    measurable_of_countable _
  exact harm.comp
    ((ReferenceCollectionDispatchMeasurability.measurable_payloadSlowSet).comp
      measurable_selectedBaselinePayload)

private theorem preparedIncoming_decodes (i : Fin (p.m - 1))
    (z : SourceX rate rewards C_star C_h q t s hs control0 × TimeControl p) :
    FollowerPrepareJointMeasurability.localConfigurationOfIncoming rate
        (sourcePreparedIncomingAtControl i z) =
      ((sourceRecordAtControl z.1 z.2).output.preparation.followers.followers i).configuration := by
  exact congrArg DeclaredFollowerLocalRound.PreparedRound.configuration
    (ReferenceActivePhysicalStepMeasurability.preparedFollowerCode_reconstruct
      (sourceInputAtControl z.1 z.2) i)

private theorem offer_status_decodes
    (incoming : FollowerPrepareJointMeasurability.IncomingConfiguration p rate) :
    incomingOfferStatus (ReferenceUpReceptionMeasurability.incomingOfferIndex incoming) =
      match FollowerPrepareJointMeasurability.localConfigurationOfIncoming rate incoming with
      | .dagger => none
      | .ordinary state _ => some state.status := by
  cases incoming with
  | none => rfl
  | some data => rfl

private theorem offer_down_decodes
    (incoming : FollowerPrepareJointMeasurability.IncomingConfiguration p rate) :
    incomingOfferLastDown (ReferenceUpReceptionMeasurability.incomingOfferIndex incoming) =
      match FollowerPrepareJointMeasurability.localConfigurationOfIncoming rate incoming with
      | .dagger => none
      | .ordinary state _ => state.lastDown := by
  cases incoming with
  | none => rfl
  | some data => rfl

private theorem sourceOwnEntry_eq_actual (player : Fin p.m)
    (z : SourceX rate rewards C_star C_h q t s hs control0 × TimeControl p) :
    sourceOwnEntryAtControl player z =
      (sourceRecordAtControl z.1 z.2).output.ownEntries player := by
  exact (ReferenceActiveHorizonMeasurability.roundRecordCode_reconstructs
    (sourceRecordAtControl z.1 z.2)).2.2.2.2 player

private theorem sourceSlice_eq_actual
    (z : SourceX rate rewards C_star C_h q t s hs control0 × TimeControl p) :
    ((sourceRecordAtControl z.1 z.2).input.row.2
      (sourceRecordAtControl z.1 z.2).input.time).1 = z.2.1 := by
  change ((ReferenceContinuingLiveSlicePreparation.inputAtControl
    (sourceCurrentInput z.1) z.2).row.2
    (ReferenceContinuingLiveSlicePreparation.inputAtControl
      (sourceCurrentInput z.1) z.2).time).1 = z.2.1
  rw [ReferenceContinuingLiveSlicePreparation.inputAtControl_row,
    ReferenceContinuingLiveSlicePreparation.inputAtControl_time,
    ReferenceContinuingLiveSlicePreparation.rowAtControl_time]

private theorem downInput_eq_checkedLogging
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1)) (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hprep : (record.output.preparation.followers.followers i).configuration =
      .ordinary state memory) (hstatus : state.status = .unoccupied) :
    (record.output.followers i).downInput =
      (ActiveFollowerLogging.checkedLogging i record.input.row
        (record.input.state.activations i) record.input.time
        (record.output.ownEntries (PublicDiscreteDraws.followerPlayer p.two_le_m i))
        state).toOption := by
  rw [ReferenceFollowerBufferProvenance.roundRecord_follower_eq_finishFollower]
  have halign := record.output.preparation.follower_alignment i
  rw [ReferenceFollowerBufferProvenance.round_ownEntry_eq_prepared]
  simp only [ReferenceActivePhysicalStep.finishFollower, hprep,
    ReferenceActivePhysicalStep.recordFollower, halign.1, halign.2.1,
    halign.2.2.1, halign.2.2.2, hstatus, dite_true]
  cases hlog : ActiveFollowerLogging.checkedLogging i record.input.row
      (record.input.state.activations i) record.input.time
      ((record.output.preparation.followers.followers i).arm,
        record.output.preparation.feedback.observations
          (PublicDiscreteDraws.followerPlayer p.two_le_m i)) state with
  | error reason => rfl
  | ok logged =>
      dsimp only
      cases hresult : DeclaredFollowerLocalRound.consumeDownResult rate
        (ReferenceDownReception.referenceDownCut p
          record.output.preparation.coordinator.downView i record.input.row record.input.time
          (record.output.preparation.feedback.observations
            (PublicDiscreteDraws.followerPlayer p.two_le_m i)) rate logged).outcome with
      | error reason => rfl
      | ok next =>
          dsimp only
          cases DeclaredFollowerLocalRound.releaseAndFinish rate i record.input.row
            record.input.time (record.output.preparation.feedback.observations
              (PublicDiscreteDraws.followerPlayer p.two_le_m i)) state memory next <;> rfl

private theorem logged_buffer_eq
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1)) (state logged : ReferencePrelaunchFollower.State p rate.eta)
    (hstatus : state.status = .unoccupied)
    (hlog : ActiveFollowerLogging.checkedLogging i record.input.row
      (record.input.state.activations i) record.input.time
      (record.output.ownEntries (PublicDiscreteDraws.followerPlayer p.two_le_m i))
      state = .ok logged) :
    logged.buffer = state.buffer ++ ReferencePrelaunchFollower.logAt i record.input.row
      (record.input.state.activations i) record.input.time
      (record.output.ownEntries (PublicDiscreteDraws.followerPlayer p.two_le_m i)) := by
  unfold ActiveFollowerLogging.checkedLogging at hlog
  split at hlog
  · dsimp only at hlog
    split at hlog
    · cases hlog
      simp only [ActiveFollowerLogging.loggingUpdate, ActiveFollowerLogging.loggingBranch,
        record.input.active i, hstatus, and_self, ite_true]
    · cases hlog
  · cases hlog

private theorem unoccupied_marker_formula
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (i : Fin (p.m - 1)) (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hprep : (record.output.preparation.followers.followers i).configuration =
      .ordinary state memory) (hstatus : state.status = .unoccupied) :
    ReferenceContinuingRecordingFastPair.currentUnoccupiedCandidateMarker record payload i state =
      if (record.output.followers i).downInput.isSome = true ∧
          SparseCalendarReplay.loggingTestsPass (ReferencePrelaunchFollower.loggingRound i
            record.input.row (record.input.state.activations i) record.input.time
            (record.output.ownEntries (PublicDiscreteDraws.followerPlayer p.two_le_m i))) ∧
          (record.output.ownEntries (PublicDiscreteDraws.followerPlayer p.two_le_m i)).1 =
            payload.assignment.assigned i ∧
          ((record.input.row.2 record.input.time).1 ContinuousControlSlice.Label.thin).val ≤
            ReferenceContinuingRecordingFastPair.savedInclusiveThinThreshold payload
              (payload.assignment.assigned i)
      then some (payload.assignment.assigned i) else none := by
  classical
  have hdown := downInput_eq_checkedLogging record i state memory hprep hstatus
  have hem : ReferenceFollowerBufferProvenance.logEmission i record =
      ReferencePrelaunchFollower.logAt i record.input.row
        (record.input.state.activations i) record.input.time
        (record.output.ownEntries (PublicDiscreteDraws.followerPlayer p.two_le_m i)) := by
    simp only [ReferenceFollowerBufferProvenance.logEmission, hprep, hstatus, dite_true]
  unfold ReferenceContinuingRecordingFastPair.currentUnoccupiedCandidateMarker
  rw [hdown]
  cases hlog : ActiveFollowerLogging.checkedLogging i record.input.row
      (record.input.state.activations i) record.input.time
      (record.output.ownEntries (PublicDiscreteDraws.followerPlayer p.two_le_m i)) state with
  | error reason => simp [Except.toOption]
  | ok logged =>
      have hbuffer := logged_buffer_eq record i state logged hstatus hlog
      simp only [Except.toOption, hlog, hbuffer, hem, true_and]
      by_cases htests : SparseCalendarReplay.loggingTestsPass
        (ReferencePrelaunchFollower.loggingRound i record.input.row
          (record.input.state.activations i) record.input.time
          (record.output.ownEntries (PublicDiscreteDraws.followerPlayer p.two_le_m i)))
      · rw [ActiveFollowerLogging.logAt_eq_singleton_of_tests _ _ _ _ _ htests]
        simp only [htests, true_and]
        simp [SparseCalendarReplay.recordAt, ReferencePrelaunchFollower.loggingRound]
      · rw [ActiveFollowerLogging.logAt_eq_nil_of_not_tests _ _ _ _ _ htests]
        simp [htests]

private def forgetPlusControl (z : Xe × TimeControl p) : X × TimeControl p :=
  (z.1.val, z.2)

private theorem measurable_forgetPlusControl : Measurable
    (forgetPlusControl (rate := rate) (rewards := rewards) (C_star := C_star)
      (C_h := C_h) (q := q) (t := t) (s := s) (hs := hs) (control0 := control0)) :=
  (measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd

private def sourceLoggingSucceededAtControl (i : Fin (p.m - 1))
    (z : SourceX rate rewards C_star C_h q t s hs control0 × TimeControl p) : Bool :=
  Sum.elim (fun _ => false) (fun _ => true)
    (((sourceWholeStepCodeAtControl z).2.1 i).2.2.1)

private theorem measurable_sourceLoggingSucceededAtControl (i : Fin (p.m - 1)) :
    Measurable (sourceLoggingSucceededAtControl (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) (q := q) (t := t) (s := s)
      (hs := hs) (control0 := control0) i) := by
  let : MeasurableSpace (Option DeclaredFollowerLocalRound.RoundFailure) :=
    LaterAssignmentStartMeasurability.optionMeasurableSpace
  let : MeasurableSpace (Option (ReferenceDownReceptionMeasurability.ReferenceDownCutCode p rate)) :=
    LaterAssignmentStartMeasurability.optionMeasurableSpace
  have hwhole := ReferenceActiveStepCompositionMeasurability.measurable_wholeStepCode.comp
    (measurable_sourceInputAtControl (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) (q := q) (t := t) (s := s)
      (hs := hs) (control0 := control0))
  exact (measurable_const.sumElim measurable_const).comp
    (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp
      ((measurable_pi_apply i).comp (measurable_fst.comp (measurable_snd.comp hwhole))))))

private theorem sourceLoggingSucceeded_eq_actual (i : Fin (p.m - 1))
    (z : SourceX rate rewards C_star C_h q t s hs control0 × TimeControl p) :
    sourceLoggingSucceededAtControl i z =
      ((sourceRecordAtControl z.1 z.2).output.followers i).downInput.isSome := by
  have h := congrArg (fun out : ReferenceActivePhysicalStep.FollowerObservation p rate =>
    out.downInput.isSome) ((ReferenceActiveHorizonMeasurability.roundRecordCode_reconstructs
      (sourceRecordAtControl z.1 z.2)).2.2.1 i)
  refine Eq.trans ?_ h
  change sourceLoggingSucceededAtControl i z =
    (ReferenceFollowerTailComposition.reconstructFollowerObservable
      ((sourceWholeStepCodeAtControl z).2.1 i)).downInput.isSome
  unfold sourceLoggingSucceededAtControl ReferenceFollowerTailComposition.reconstructFollowerObservable
    ReferenceFollowerTailComposition.reconstructDownInput
  cases ((sourceWholeStepCodeAtControl z).2.1 i).2.2.1 <;> rfl

private theorem measurable_assignedExponent (i : Fin (p.m - 1)) :
    Measurable (fun x : Xe =>
      (selectedBaselinePayload x).exponent (selectedBaselineAssignedArm i x)) := by
  have heval : Measurable (fun z : (Fin p.K → ℕ) × Fin p.K => z.1 z.2) :=
    measurable_from_prod_countable_left fun j => measurable_pi_apply j
  exact heval.comp (measurable_selectedBaselineInputExponent.prodMk
    (measurable_selectedBaselineAssignedArm i))

private theorem measurable_assignedThreshold (i : Fin (p.m - 1)) :
    Measurable (fun x : Xe =>
      ReferenceContinuingRecordingFastPair.savedInclusiveThinThreshold
        (selectedBaselinePayload x) (selectedBaselineAssignedArm i x)) := by
  let threshold : ℕ → ℝ := fun h =>
    (4 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) * (((2 : ℝ) ^ h)⁻¹)) /
      SparseCalendarReplay.sparseMaskProbability p.K (p.m - 1)
  exact (measurable_of_countable threshold).comp (measurable_assignedExponent i)

private def unoccupiedMarkerReadout (i : Fin (p.m - 1))
    (z : Xe × TimeControl p) : Option (Fin p.K) :=
  if sourceLoggingSucceededAtControl i (forgetPlusControl z) = true ∧
      sourceLoggingTestsPassBit i (forgetPlusControl z) = true ∧
      (sourceOwnEntryAtControl (PublicDiscreteDraws.followerPlayer p.two_le_m i)
        (forgetPlusControl z)).1 = selectedBaselineAssignedArm i z.1 ∧
      sourceCurrentThinScalar (forgetPlusControl z) ≤
        ReferenceContinuingRecordingFastPair.savedInclusiveThinThreshold
          (selectedBaselinePayload z.1) (selectedBaselineAssignedArm i z.1)
  then some (selectedBaselineAssignedArm i z.1) else none

private theorem measurable_unoccupiedMarkerReadout (i : Fin (p.m - 1)) :
    Measurable (unoccupiedMarkerReadout (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) (q := q) (t := t) (s := s)
      (hs := hs) (control0 := control0) i) := by
  have hforget := measurable_forgetPlusControl (rate := rate) (rewards := rewards)
    (C_star := C_star) (C_h := C_h) (q := q) (t := t) (s := s)
    (hs := hs) (control0 := control0)
  have harm : Measurable (fun z : Xe ×
      TimeControl p => selectedBaselineAssignedArm i z.1) :=
    (measurable_selectedBaselineAssignedArm (rate := rate) (rewards := rewards)
    (C_star := C_star) (C_h := C_h) (q := q) (t := t) (s := s)
    (hs := hs) (control0 := control0) i).comp measurable_fst
  have hsome : Measurable (fun z : Xe ×
      TimeControl p => some (selectedBaselineAssignedArm i z.1)) :=
    (measurable_of_countable (some : Fin p.K → Option (Fin p.K))).comp harm
  apply Measurable.ite _ hsome measurable_const
  exact (measurableSet_eq_fun ((measurable_sourceLoggingSucceededAtControl i).comp hforget)
    measurable_const).inter
    ((measurableSet_eq_fun ((measurable_sourceLoggingTestsPassBit i).comp hforget)
      measurable_const).inter
      ((measurableSet_eq_fun ((measurable_fst.comp
        (measurable_sourceOwnEntryAtControl (PublicDiscreteDraws.followerPlayer p.two_le_m i))).comp
          hforget) harm).inter
        (measurableSet_le (measurable_sourceCurrentThinScalar.comp hforget)
          ((measurable_assignedThreshold i).comp measurable_fst))))

private def occupiedMarkerReadout (i : Fin (p.m - 1))
    (slice : CanonicalRecordingSlice.Slice p.m p.K)
    (down : Option (OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))) :
    Option (Fin p.K) :=
  match down with
  | none => none
  | some d =>
      if CanonicalRecordingSlice.deterministicOwnedRecordingGate p.two_le_m p.m_lt_K
        (ConstructorDimensions.K_pos p) (PublicDiscreteDraws.followerPlayer p.two_le_m i)
        (PrelaunchBufferRecovery.downArm rate.eta d)
        (ActiveFollowerQueueOperation.thinningProbability rate.eta d) slice
      then some (PrelaunchBufferRecovery.downArm rate.eta d) else none

private theorem measurable_occupiedMarkerReadout (i : Fin (p.m - 1)) :
    Measurable (fun z : CanonicalRecordingSlice.Slice p.m p.K ×
      Option (OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)) =>
        occupiedMarkerReadout (rate := rate) i z.1 z.2) := by
  apply measurable_from_prod_countable_left
  intro down
  cases down with
  | none => exact measurable_const
  | some d =>
      exact Measurable.ite
        (CanonicalRecordingSlice.measurableSet_deterministicOwnedRecordingGate
          p.two_le_m p.m_lt_K (ConstructorDimensions.K_pos p)
          (PublicDiscreteDraws.followerPlayer p.two_le_m i)
          (PrelaunchBufferRecovery.downArm rate.eta d)
          (ActiveFollowerQueueOperation.thinningProbability rate.eta d))
        measurable_const measurable_const

private def followerMarkerReadout (i : Fin (p.m - 1))
    (z : Xe × TimeControl p) : Option (Fin p.K) :=
  if sourcePreparedStatusAtControl i (forgetPlusControl z) = some .unoccupied then
    unoccupiedMarkerReadout i z
  else occupiedMarkerReadout (rate := rate) i z.2.1
    (sourcePreparedLastDownAtControl i (forgetPlusControl z))

private theorem measurable_followerMarkerReadout (i : Fin (p.m - 1)) :
    Measurable (followerMarkerReadout (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) (q := q) (t := t) (s := s)
      (hs := hs) (control0 := control0) i) := by
  apply Measurable.ite
    (measurableSet_eq_fun ((measurable_sourcePreparedStatusAtControl i).comp
      measurable_forgetPlusControl) measurable_const) (measurable_unoccupiedMarkerReadout i)
  exact (measurable_occupiedMarkerReadout i).comp
    ((measurable_fst.comp measurable_snd).prodMk
      ((measurable_sourcePreparedLastDownAtControl i).comp measurable_forgetPlusControl))

private def dataMarkerReadout (source : Fin p.m)
    (z : Xe × TimeControl p) : Option (Fin p.K) :=
  if hc : source = ActiveRoundActions.coordinator p.two_le_m then
    sourceCoordinatorGateArmAtControl (forgetPlusControl z)
  else followerMarkerReadout (ActiveRoundActions.followerIndex p.two_le_m source hc) z

private theorem measurable_dataMarkerReadout (source : Fin p.m) :
    Measurable (dataMarkerReadout (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) (q := q) (t := t) (s := s)
      (hs := hs) (control0 := control0) source) := by
  unfold dataMarkerReadout
  split
  · exact measurable_sourceCoordinatorGateArmAtControl.comp measurable_forgetPlusControl
  · exact measurable_followerMarkerReadout _

private theorem followerMarkerReadout_eq_actual (i : Fin (p.m - 1))
    (z : Xe × TimeControl p) :
    followerMarkerReadout i z =
      match ((sourceRecordAtControl z.1.val z.2).output.preparation.followers.followers i).configuration with
      | .dagger => none
      | .ordinary state _ =>
          if state.status = .unoccupied then
            ReferenceContinuingRecordingFastPair.currentUnoccupiedCandidateMarker
              (sourceRecordAtControl z.1.val z.2) (selectedBaselinePayload z.1) i state
          else match state.lastDown with
            | none => none
            | some down => if ActiveFollowerQueueOperation.recorderGate rate.eta i
                (sourceRecordAtControl z.1.val z.2).input.row
                (sourceRecordAtControl z.1.val z.2).input.time down
              then some (PrelaunchBufferRecovery.downArm rate.eta down) else none := by
  have hstatus := offer_status_decodes (sourcePreparedIncomingAtControl i (forgetPlusControl z))
  have hdown := offer_down_decodes (sourcePreparedIncomingAtControl i (forgetPlusControl z))
  rw [preparedIncoming_decodes (rate := rate) i (forgetPlusControl z)] at hstatus hdown
  change sourcePreparedStatusAtControl i (forgetPlusControl z) = _ at hstatus
  change sourcePreparedLastDownAtControl i (forgetPlusControl z) = _ at hdown
  have hslice : ((sourceRecordAtControl z.1.val z.2).input.row.2
      (sourceRecordAtControl z.1.val z.2).input.time).1 = z.2.1 :=
    sourceSlice_eq_actual (z.1.val, z.2)
  unfold followerMarkerReadout
  dsimp only [forgetPlusControl] at hstatus hdown ⊢
  cases hp : ((sourceRecordAtControl z.1.val z.2).output.preparation.followers.followers i).configuration with
  | dagger => simp only [hp] at hstatus hdown ⊢; simp [hstatus, hdown, occupiedMarkerReadout]
  | ordinary state memory =>
      simp only [hp] at hstatus ⊢
      by_cases hu : state.status = .unoccupied
      · simp only [hstatus, hu, ite_true]
        rw [unoccupied_marker_formula _ _ i state memory hp hu]
        unfold unoccupiedMarkerReadout sourceLoggingTestsPassBit sourceLoggingTestsAtControl
          selectedBaselineAssignedArm sourceCurrentThinScalar
        rw [sourceLoggingSucceeded_eq_actual (rate := rate) i (forgetPlusControl z),
          sourceOwnEntry_eq_actual (PublicDiscreteDraws.followerPlayer p.two_le_m i) (forgetPlusControl z)]
        rw [hslice]
        simp only [decide_eq_true_eq]
        rfl
      · simp only [hp] at hdown
        simp only [hstatus, hu, Option.some.injEq, ite_false, hdown]
        cases hd : state.lastDown with
        | none => rfl
        | some down =>
            unfold occupiedMarkerReadout ActiveFollowerQueueOperation.recorderGate
              CanonicalRecordingSlice.deterministicOwnedRecordingGate
            dsimp only
            rw [hslice]

private theorem dataMarkerReadout_eq_actual (source : Fin p.m)
    (z : Xe × TimeControl p) :
    dataMarkerReadout source z = ReferenceContinuingRecordingFastPair.physicalDataMarkerOnRecord
      (sourceRecordAtControl z.1.val z.2) (selectedBaselinePayload z.1) source := by
  unfold dataMarkerReadout ReferenceContinuingRecordingFastPair.physicalDataMarkerOnRecord
  split
  · unfold sourceCoordinatorGateArmAtControl
    rw [sourceCoordinatorRecordingAtControl_eq_actual]
    rfl
  · exact followerMarkerReadout_eq_actual _ z

/-- Joint Borel measurability of the literal physical marker as BOTH the
retained source and the whole current control vary. No numerical-cell
transport or non-DATA ordinary-preparation hypothesis is used. -/
theorem measurable_currentEmptyMarker :
    Measurable (currentEmptyMarker rate rewards C_star C_h q t s hs control0) := by
  have hdata : Measurable (fun z :
      (Xe × TimeControl p) × Fin p.m =>
        dataMarkerReadout z.2 z.1) :=
    measurable_from_prod_countable_left measurable_dataMarkerReadout
  have hsource := measurable_sourceCurrentRecorderSource.comp
    (measurable_forgetPlusControl (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) (q := q) (t := t) (s := s)
      (hs := hs) (control0 := control0))
  have hread : Measurable (fun z : Xe ×
      TimeControl p => if PublicDiscreteDraws.slotDraw z.2.1 = PublicDiscreteDraws.dataSlot
      then dataMarkerReadout
        (PublicDiscreteDraws.recorderSourceDraw p.two_le_m p.m_lt_K z.2.1) z
      else none) := Measurable.ite
    (measurableSet_eq_fun (measurable_sourceCurrentSlotDraw.comp
      measurable_forgetPlusControl) measurable_const)
    (hdata.comp (measurable_id.prodMk hsource)) measurable_const
  convert hread using 1
  funext z
  unfold currentEmptyMarker ReferenceContinuingRecordingFastPair.physicalMarkerOnRecord
  have hslice : ((sourceRecordAtControl z.1.val z.2).input.row.2
      (sourceRecordAtControl z.1.val z.2).input.time).1 = z.2.1 :=
    sourceSlice_eq_actual (z.1.val, z.2)
  rw [hslice]
  simp only [dite_true]
  rw [dataMarkerReadout_eq_actual]
  rfl

end Readouts

/-- The canonical rates remain measurable on the inherited empty carrier. -/
theorem measurable_xiEmpty (j : Fin p.K) :
    Measurable (fun x : Xe => xiEmpty rate rewards C_star C_h q t s hs control0 x j) := by
  have h := (measurable_pi_apply j).comp
    (measurable_selectedBaselineInputRate (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) (q := q) (t := t) (s := s)
      (hs := hs) (control0 := control0))
  convert h using 1
  funext x
  exact ((selectedBaselinePayload x).rate_eq_canonical j).symm


/-- The literal branch event on the original source stratum is Borel. -/
theorem measurableSet_sourceEmpty :
    MeasurableSet {z : Z | Bempty rate rewards C_star C_h q t s hs control0 (ret z)} :=
  (measurableSet_Bempty rate rewards C_star C_h q t s hs control0).preimage
    (ReferenceFirstLiveRecordingSourceCylinder.measurable_sourceRetained
      rate rewards C_star C_h q t s hs control0)

/-- Empty and nonempty pending are disjoint computed branches. -/
theorem Bempty_not_continuing (x : Xe) :
    ¬ continuingRecordingBranch rate rewards C_star C_h q t s hs control0 x.val := by
  intro h
  obtain ⟨r, owned, base, d, hsStart, c, arm, hcoord, hpending, _⟩ :=
    empty_current_data rate rewards C_star C_h q t s hs control0 x.val x.property
  have hnonempty := h.2.2
  rw [hcoord] at hnonempty
  exact Finset.not_nonempty_empty (hpending ▸ hnonempty.1)

/-- Split the original empty branch, retaining the original whole control. -/
def emptySourceSplit (z : Ze) : Xe × TimeControl p :=
  (xofEmpty rate rewards C_star C_h q t s hs control0 z,
    ReferenceFirstLiveRecordingSourceCylinder.originalControl rate rewards C_star C_h q t s hs z.val)

theorem measurable_emptySourceSplit :
    Measurable (emptySourceSplit rate rewards C_star C_h q t s hs control0) :=
  (measurable_xofEmpty rate rewards C_star C_h q t s hs control0).prodMk
    ((ReferenceFirstLiveRecordingSourceCylinder.measurable_originalControl
      rate rewards C_star C_h q t s hs).comp measurable_subtype_coe)

/-- The split recovers the entire original source, including all private arrays and J. -/
theorem emptySourceSplit_recover (z : Ze) :
    ReferenceFirstLiveRecordingSourceCylinder.sourceRecover rate rewards C_star C_h q t s hs control0
      ((emptySourceSplit rate rewards C_star C_h q t s hs control0 z).1.val,
        (emptySourceSplit rate rewards C_star C_h q t s hs control0 z).2) = z.val :=
  ReferenceFirstLiveRecordingSourceCylinder.sourceRecover_sourceSplit
    rate rewards C_star C_h q t s hs control0 z.val

/-- Exact subtype restriction of C's product law on ALL of Z. No mass is divided out. -/
theorem emptySourceSplit_product :
    (mue).map (emptySourceSplit rate rewards C_star C_h q t s hs control0) =
      (nue).prod (timeControlLaw p) := by
  let forget : Xe × TimeControl p → X × TimeControl p := Prod.map Subtype.val id
  have hB := measurableSet_Bempty rate rewards C_star C_h q t s hs control0
  have hZ := measurableSet_sourceEmpty rate rewards C_star C_h q t s hs control0
  have hforget : MeasurableEmbedding forget :=
    (MeasurableEmbedding.subtype_coe hB).prodMap MeasurableEmbedding.id
  apply hforget.map_injective
  rw [Measure.map_map hforget.measurable
    (measurable_emptySourceSplit rate rewards C_star C_h q t s hs control0)]
  have hcomp : forget ∘ emptySourceSplit rate rewards C_star C_h q t s hs control0 =
      ReferenceFirstLiveRecordingSourceCylinder.sourceSplit rate rewards C_star C_h q t s hs control0 ∘
        Subtype.val := rfl
  rw [hcomp, ← Measure.map_map
    (ReferenceFirstLiveRecordingSourceCylinder.measurable_sourceSplit
      rate rewards C_star C_h q t s hs control0) measurable_subtype_coe]
  rw [show (mue).map (Subtype.val : Ze → Z) =
      (muZ).restrict {z | Bempty rate rewards C_star C_h q t s hs control0 (ret z)} from
    map_comap_subtype_coe hZ muZ]
  change ((muZ).restrict ((ReferenceFirstLiveRecordingSourceCylinder.sourceSplit
    rate rewards C_star C_h q t s hs control0) ⁻¹'
      (Prod.fst ⁻¹' {x : X | Bempty rate rewards C_star C_h q t s hs control0 x}))).map _ = _
  rw [← Measure.restrict_map
    (ReferenceFirstLiveRecordingSourceCylinder.measurable_sourceSplit
      rate rewards C_star C_h q t s hs control0) (measurable_fst hB),
    ReferenceFirstLiveRecordingSourceCylinder.sourceSplit_product rate rewards C_star C_h q t s hs control0]
  change ((nuX).prod (timeControlLaw p)).restrict
      (Prod.fst ⁻¹' {x : X | Bempty rate rewards C_star C_h q t s hs control0 x}) =
    ((nue).prod (timeControlLaw p)).map (Prod.map Subtype.val id)
  rw [← Measure.map_prod_map nue (timeControlLaw p) measurable_subtype_coe measurable_id,
    Measure.map_id, show (nue).map (Subtype.val : Xe → X) =
      (nuX).restrict {x | Bempty rate rewards C_star C_h q t s hs control0 x} from
    map_comap_subtype_coe hB nuX, Measure.restrict_prod_eq_prod_univ, Set.prod_univ]

theorem measurable_actualEmptyMarker :
    Measurable (actualEmptyMarker rate rewards C_star C_h q t s hs control0) := by
  have h := (measurable_currentEmptyMarker (rate := rate) (rewards := rewards)
    (C_star := C_star) (C_h := C_h) (q := q) (t := t) (s := s) (hs := hs)
    (control0 := control0)).comp
      (measurable_emptySourceSplit rate rewards C_star C_h q t s hs control0)
  convert h using 1
  funext z
  exact actualEmptyMarker_eq_control rate rewards C_star C_h q t s hs control0 z

/-- Arbitrary Borel cylinders on the genuine empty subtype, under the
original finite unnormalized measure. All recording inputs are produced above. -/
theorem original_source_cylinder (Aset : Set Xe) (hA : MeasurableSet Aset)
    (o : Option (Fin p.K)) :
    mue {z | xofEmpty rate rewards C_star C_h q t s hs control0 z ∈ Aset ∧
      actualEmptyMarker rate rewards C_star C_h q t s hs control0 z = o} =
    ∫⁻ x in Aset, (match o with
      | some j => ENNReal.ofReal (xiEmpty rate rewards C_star C_h q t s hs control0 x j)
      | none => ENNReal.ofReal (1 - ∑ j, xiEmpty rate rewards C_star C_h q t s hs control0 x j)) ∂nue := by
  let E : Set (Xe × TimeControl p) := {xu | xu.1 ∈ Aset ∧
    currentEmptyMarker rate rewards C_star C_h q t s hs control0 xu = o}
  have hE : MeasurableSet E := (hA.preimage measurable_fst).inter
    (measurableSet_eq_fun measurable_currentEmptyMarker measurable_const)
  have hmap := congrArg (fun mu : Measure (Xe × TimeControl p) => mu E)
    (emptySourceSplit_product rate rewards C_star C_h q t s hs control0)
  rw [Measure.map_apply (measurable_emptySourceSplit rate rewards C_star C_h q t s hs control0) hE,
    Measure.prod_apply hE] at hmap
  have hmarker : (emptySourceSplit rate rewards C_star C_h q t s hs control0) ⁻¹' E =
      {z | xofEmpty rate rewards C_star C_h q t s hs control0 z ∈ Aset ∧
        actualEmptyMarker rate rewards C_star C_h q t s hs control0 z = o} := by
    ext z
    simp only [Set.mem_preimage, E, Set.mem_ofPred_eq, emptySourceSplit,
      ← actualEmptyMarker_eq_control]
  rw [hmarker] at hmap
  rw [hmap, ← lintegral_indicator hA]
  apply lintegral_congr
  intro x
  by_cases hx : x ∈ Aset
  · have hevent : Prod.mk x ⁻¹' E = {u | currentEmptyMarker
        rate rewards C_star C_h q t s hs control0 (x, u) = o} := by
      ext u
      simp only [E, Set.mem_preimage, Set.mem_ofPred_eq, hx, true_and]
    rw [hevent, Set.indicator_of_mem hx]
    cases o with
    | none => exact (currentEmptyMarker_masses rate rewards C_star C_h q t s hs control0 x).2
    | some j => exact (currentEmptyMarker_masses rate rewards C_star C_h q t s hs control0 x).1 j
  · have hevent : Prod.mk x ⁻¹' E = ∅ := by
      ext u
      simp only [E, Set.mem_preimage, Set.mem_ofPred_eq, hx, false_and, Set.mem_empty_iff_false]
    rw [hevent, measure_empty, Set.indicator_of_notMem hx]

/-- The SOME atom identity on every Borel test set of the inherited empty fibre. -/
theorem original_source_cylinder_some (Aset : Set Xe) (hA : MeasurableSet Aset) (j : Fin p.K) :
    mue {z | xofEmpty rate rewards C_star C_h q t s hs control0 z ∈ Aset ∧
      actualEmptyMarker rate rewards C_star C_h q t s hs control0 z = some j} =
    ∫⁻ x in Aset, ENNReal.ofReal (xiEmpty rate rewards C_star C_h q t s hs control0 x j) ∂nue :=
  original_source_cylinder rate rewards C_star C_h q t s hs control0 Aset hA (some j)

/-- The NONE atom includes enabled zero-arrival service; its mass is retained. -/
theorem original_source_cylinder_none (Aset : Set Xe) (hA : MeasurableSet Aset) :
    mue {z | xofEmpty rate rewards C_star C_h q t s hs control0 z ∈ Aset ∧
      actualEmptyMarker rate rewards C_star C_h q t s hs control0 z = none} =
    ∫⁻ x in Aset, ENNReal.ofReal (1 - ∑ j,
      xiEmpty rate rewards C_star C_h q t s hs control0 x j) ∂nue :=
  original_source_cylinder rate rewards C_star C_h q t s hs control0 Aset hA none

section Prefix

open Bandits.Support.ReferenceFirstLiveSourcePrefixBranchInvariance

local notation "pre" => prefixZ rate rewards C_star C_h q t s hs control0

private theorem Bempty_iff_start (x : X) :
    Bempty rate rewards C_star C_h q t s hs control0 x ↔
    offset > 0 ∧
      (∀ record ∈ (actualRetainedPrefixRun rate rewards C_star C_h q t s hs control0 x).records.take offset,
        ReferenceCollectionPhaseHistory.cutoffChosen record.input = false) ∧
      (match preparedContinuingStart rate (inp x) with
      | some started => started.pending = ∅ ∧ t.val + 1 < started.clock.g
      | none => False) := by
  dsimp only [Bempty, preparedContinuingStart]
  cases (ReferenceActivePhysicalStep.prepare (inp x)).coordinator with
  | live r owned base outcome => cases outcome <;> rfl
  | first outcome => rfl
  | collection payload ledger clock cutoff outcome => rfl
  | invalidCollectionCutoff => rfl
  | dagger => rfl

/-- The entire computed empty event factors through the original strict prefix. -/
theorem Bempty_prefix_iff (z : Z) :
    Bempty rate rewards C_star C_h q t s hs control0 (ret (pre z)) ↔
      Bempty rate rewards C_star C_h q t s hs control0 (ret z) := by
  rw [Bempty_iff_start, Bempty_iff_start,
    ← source_prefix_preparedStart rate rewards C_star C_h q t s hs control0 z]
  apply and_congr_right
  intro _
  apply and_congr_left
  intro _
  have hall (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))) :
      (∀ record ∈ records, ReferenceCollectionPhaseHistory.cutoffChosen record.input = false) ↔
      ∀ tag ∈ records.map (fun record => ReferenceCollectionPhaseHistory.cutoffChosen record.input), tag = false := by
    simp only [List.mem_map, forall_exists_index, and_imp]
    constructor
    · intro h tag record hr heq
      exact heq ▸ h record hr
    · intro h record hr
      exact h _ record hr rfl
  rw [hall, hall, source_prefix_cutoffTags rate rewards C_star C_h q t s hs control0 z]

/-- The canonical empty subtype inherits the SAME original-source prefix. -/
def prefixEmpty (z : Ze) : Ze :=
  ⟨pre z.val, (Bempty_prefix_iff rate rewards C_star C_h q t s hs control0 z.val).mpr z.property⟩

/-- The original current-control field, restricted to the actual empty subtype. -/
@[instance_reducible] def Fempty : MeasurableSpace Ze :=
  (inferInstance : MeasurableSpace (BootstrapPrivateRoundStreams.SourceInput p)).comap
    (fun z : Ze => ReferenceSourceCurrentControlFreshness.c_t p control0 t z.val.val)

theorem Fempty_le : Fempty rate rewards C_star C_h q t s hs control0 ≤
    (inferInstance : MeasurableSpace Ze) :=
  ((ReferenceSourceCurrentControlFreshness.measurable_c_t control0 t).comp
    (measurable_subtype_coe.comp measurable_subtype_coe)).comap_le

theorem measurable_prefixEmpty :
    Measurable[Fempty rate rewards C_star C_h q t s hs control0]
      (prefixEmpty rate rewards C_star C_h q t s hs control0) := by
  apply Measurable.subtype_mk
  apply Measurable.subtype_mk
  change Measurable[Fempty rate rewards C_star C_h q t s hs control0]
    (fun z : Ze => ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z.val.val)
  have heq : (fun z : Ze => ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z.val.val) =
      fun z => ReferenceSourceCurrentControlFreshness.c_t p control0 t z.val.val := by
    funext z
    exact (ReferenceSourcePhysicalFlagConditionalLaw.c_t_eq_sourcePrefix control0 t z.val.val).symm
  rw [heq]
  exact comap_measurable _

/-- Prefix transport preserves the complete baseline payload, including its anchor. -/
theorem selected_payload_prefix (z : Ze) :
    selectedBaselinePayload (xofEmpty rate rewards C_star C_h q t s hs control0
      (prefixEmpty rate rewards C_star C_h q t s hs control0 z)) =
    selectedBaselinePayload (xofEmpty rate rewards C_star C_h q t s hs control0 z) := by
  let a := xofEmpty rate rewards C_star C_h q t s hs control0
    (prefixEmpty rate rewards C_star C_h q t s hs control0 z)
  let b := xofEmpty rate rewards C_star C_h q t s hs control0 z
  obtain ⟨r, owned, base, d, hsStart, c, arm, hc, _, _⟩ :=
    empty_current_data rate rewards C_star C_h q t s hs control0 a.val a.property
  obtain ⟨r', owned', base', d', hsStart', c', arm', hc', _, _⟩ :=
    empty_current_data rate rewards C_star C_h q t s hs control0 b.val b.property
  have hl := incoming_payload_of_continuing rate (inp a.val) r owned base d hsStart c arm hc
  have hr := incoming_payload_of_continuing rate (inp b.val) r' owned' base' d' hsStart' c' arm' hc'
  change (match (inp (ret z.val)).state.coordinator with
    | .live registers _ _ => some registers.payload | _ => none) = some r'.payload at hr
  rw [source_prefix_incoming rate rewards C_star C_h q t s hs control0 z.val] at hr
  have heq : r.payload = r'.payload := Option.some.inj (hl.symm.trans hr)
  exact (selEmpty_payload_eq rate rewards C_star C_h q t s hs control0 a
    r owned base d hsStart c arm hc).trans
    (heq.trans (selEmpty_payload_eq rate rewards C_star C_h q t s hs control0 b
      r' owned' base' d' hsStart' c' arm' hc').symm)

/-- Actual rate coefficients are measurable on the inherited original c_t field. -/
theorem measurable_xiEmpty_source (j : Fin p.K) :
    Measurable[Fempty rate rewards C_star C_h q t s hs control0]
      (fun z : Ze => xiEmpty rate rewards C_star C_h q t s hs control0
        (xofEmpty rate rewards C_star C_h q t s hs control0 z) j) := by
  have h := ((measurable_xiEmpty rate rewards C_star C_h q t s hs control0 j).comp
    (measurable_xofEmpty rate rewards C_star C_h q t s hs control0)).comp
      (measurable_prefixEmpty rate rewards C_star C_h q t s hs control0)
  convert h using 1
  funext z
  exact congrArg (fun payload : ReferenceActivePhysicalStep.Payload rate =>
    CanonicalRecordingRates.xi p rate.eta.val payload.anchor j)
    (selected_payload_prefix rate rewards C_star C_h q t s hs control0 z).symm

end Prefix

end Bandits.Support.ReferenceFirstLiveEmptyPendingMarkerLaw
