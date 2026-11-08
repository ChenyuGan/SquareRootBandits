/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionAwaitedDownBatchWitness
public import Bandits.Support.ReferenceFirstCollectionUnmaskedFormedUpCountOrAwaitedFailure
public import Bandits.Support.ReferenceFirstCollectionAwaitedDownFailureReadout

import Lean.Elab.Tactic.Omega

/-!
# First-collection awaited task support and inclusive service quotas

Sources: `sources/zip4/manuscript/05_binary_transport.tex:33-55,180-240`,
`sources/zip4/manuscript/06_interruptions.tex:246-282,425-431,459-481`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:92-108,141-157`.

The corrected support uses strict-past actual awaited-failure readouts while
retaining the original incoming pending observation and staged service law.
Its calendar quotas include the detecting update and make no global collection
cost claim.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support
open ConstructorDimensions
open scoped Classical

namespace Bandits.Support.ReferenceFirstCollectionAwaitedTaskSupport

variable {p : ConstructorDimensions.Parameters}

/-- Strict-past actual failures remove all pending tasks; the original raw
pending observation and its terminal empty extension are otherwise unchanged. -/
def Pawait
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (n : ℕ)
    (z : BootstrapPrivateRoundStreams.SourceInput p) : Finset (Fin (p.m - 1)) :=
  if ReferenceFirstCollectionAwaitedDownFailureReadout.pastFailureFlag
      rate rewards C_star C_h n z = false then
    ReferenceFirstCollectionPendingObservation.Praw rate rewards C_star C_h n z
  else ∅

/-- Actual finite-calendar OLD positive dates on the corrected support, using
the original staged support and observation. -/
def oldPositiveDates
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1))
    (z : BootstrapPrivateRoundStreams.SourceInput p) : Finset (Fin p.T) :=
  (Finset.univ : Finset (Fin p.T)).filter fun t =>
    i ∈ Pawait rate rewards C_star C_h t.val z ∧
    z ∈ ReferenceFirstCollectionStagedConditionalService.OLD
      (p := p) (rate := rate) rewards C_star C_h i t ∧
    ReferenceFirstCollectionRoundEndObservation.x
      (rate := rate) rewards C_star C_h i t.val z = true

/-- Actual finite-calendar FORMED positive dates on the same corrected
support and unchanged staged observation. -/
def formedPositiveDates
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1))
    (z : BootstrapPrivateRoundStreams.SourceInput p) : Finset (Fin p.T) :=
  (Finset.univ : Finset (Fin p.T)).filter fun t =>
    i ∈ Pawait rate rewards C_star C_h t.val z ∧
    z ∈ ReferenceFirstCollectionStagedConditionalService.FORMED
      (p := p) (rate := rate) rewards C_star C_h i t ∧
    ReferenceFirstCollectionRoundEndObservation.x
      (rate := rate) rewards C_star C_h i t.val z = true

/-- Positive staged service dates on the corrected support, read from the
original binary `x`. -/
def servicePositiveDates
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1))
    (z : BootstrapPrivateRoundStreams.SourceInput p) : Finset (Fin p.T) :=
  (Finset.univ : Finset (Fin p.T)).filter fun t =>
    i ∈ Pawait rate rewards C_star C_h t.val z ∧
    ReferenceFirstCollectionRoundEndObservation.x
      (rate := rate) rewards C_star C_h i t.val z = true

/-- Corrected membership is exactly raw pending membership and absence of a
strict-past actual awaited failure. -/
theorem mem_Pawait_iff
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (n : ℕ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) :
    i ∈ Pawait rate rewards C_star C_h n z ↔
      ReferenceFirstCollectionAwaitedDownFailureReadout.pastFailureFlag
        rate rewards C_star C_h n z = false ∧
      i ∈ ReferenceFirstCollectionPendingObservation.Praw rate rewards C_star C_h n z := by
  simp only [Pawait]
  split_ifs with h
  · simp [h]
  · simp [h]

@[simp] theorem Pawait_of_horizon_le
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (n : ℕ) (hn : p.T ≤ n)
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    Pawait rate rewards C_star C_h n z = ∅ := by
  rw [Pawait]
  split_ifs
  · exact ReferenceFirstCollectionPendingObservation.Praw_of_horizon_le
      rate rewards C_star C_h n hn z
  · rfl

private theorem no_failure_before_of_mem_Pawait
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (n : ℕ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1))
    (hmem : i ∈ Pawait rate rewards C_star C_h n z) :
    ∀ t : Fin p.T, t.val < n →
      ¬ ReferenceFirstCollectionAwaitedDownFailureReadout.failureAt
        rate rewards C_star C_h z t := by
  have hflag := (mem_Pawait_iff rate rewards C_star C_h n z i).1 hmem |>.1
  intro t htn hfailure
  have htrue : ReferenceFirstCollectionAwaitedDownFailureReadout.pastFailureFlag
      rate rewards C_star C_h n z = true := by
    simp only [ReferenceFirstCollectionAwaitedDownFailureReadout.pastFailureFlag,
      decide_eq_true_eq]
    exact ⟨t, htn, hfailure⟩
  rw [hflag] at htrue
  cases htrue

/-- The corrected support is measurable in the same pre-round filtration. -/
theorem Pawait_mem_measurable (control0 : ContinuousLearningRows.TimeControl p)
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (t : Fin p.T) :
    MeasurableSet[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
      control0 (t.val + 1)]
      {z : BootstrapPrivateRoundStreams.SourceInput p |
        i ∈ Pawait rate rewards C_star C_h t.val z} := by
  have hflag := ReferenceFirstCollectionAwaitedDownFailureReadout.pastFailureFlag_adapted
    rate rewards C_star C_h control0 t.val
  have hmask : MeasurableSet[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
      control0 (t.val + 1)]
      {z : BootstrapPrivateRoundStreams.SourceInput p |
        ReferenceFirstCollectionAwaitedDownFailureReadout.pastFailureFlag
          rate rewards C_star C_h t.val z = false} :=
    measurableSet_eq_fun hflag measurable_const
  have hraw := ReferenceFirstCollectionPendingObservation.Praw_mem_measurable
    (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) control0 i t
  have heq : {z : BootstrapPrivateRoundStreams.SourceInput p |
      i ∈ Pawait rate rewards C_star C_h t.val z} =
      {z | ReferenceFirstCollectionAwaitedDownFailureReadout.pastFailureFlag
        rate rewards C_star C_h t.val z = false} ∩
      {z | i ∈ ReferenceFirstCollectionPendingObservation.Praw
        rate rewards C_star C_h t.val z} := by
    ext z
    exact mem_Pawait_iff rate rewards C_star C_h t.val z i
  rw [heq]
  exact hmask.inter hraw

/-- Same-law conditional service transfers to the corrected subset by its
literal inclusion in unchanged `Praw`. -/
theorem Pawait_service (control0 : ContinuousLearningRows.TimeControl p)
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) :
    ∀ᵐ z ∂BootstrapPrivateRoundStreams.sourceInputLaw p,
      ∀ (i : Fin (p.m - 1)) (t : Fin p.T),
        i ∈ Pawait rate rewards C_star C_h t.val z →
        (BootstrapPrivateRoundStreams.sourceInputLaw p)[
          ReferenceFirstCollectionStagedConditionalService.X
            (rate := rate) rewards C_star C_h i t |
          ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (t.val + 1)] z =
          (ReferenceFirstCollectionUpConditionalService.positiveRewardCount rewards t : ℝ) /
            (8 * (p.m - 1 : ℝ) * (p.K : ℝ)) := by
  filter_upwards [ReferenceFirstCollectionPendingObservation.Praw_service
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) control0]
    with z hz
  intro i t hi
  exact hz i t ((mem_Pawait_iff rate rewards C_star C_h t.val z i).1 hi).2

/-- Corrected OLD and FORMED positive-date sets are disjoint by the original
staged-support disjointness theorem. -/
theorem disjoint_oldPositiveDates_formedPositiveDates
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1))
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    Disjoint (oldPositiveDates (p := p) rate rewards C_star C_h i z)
      (formedPositiveDates (p := p) rate rewards C_star C_h i z) := by
  rw [Finset.disjoint_left]
  intro t htOld htFormed
  rcases (Finset.mem_filter.mp htOld).2 with ⟨_, hOld, _⟩
  rcases (Finset.mem_filter.mp htFormed).2 with ⟨_, hFormed, _⟩
  exact (Set.disjoint_left.mp
    (ReferenceFirstCollectionStagedConditionalService.disjoint_OLD_FORMED
      (p := p) (rate := rate) rewards C_star C_h i t)) hOld hFormed

/-- The original binary service observation on `Pawait` is exactly the
disjoint union of OLD and FORMED positive dates. -/
theorem servicePositiveDates_eq_union
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1))
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    servicePositiveDates (p := p) rate rewards C_star C_h i z =
      oldPositiveDates (p := p) rate rewards C_star C_h i z ∪
        formedPositiveDates (p := p) rate rewards C_star C_h i z := by
  classical
  ext t
  simp only [servicePositiveDates, oldPositiveDates, formedPositiveDates,
    Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
  constructor
  · rintro ⟨hawait, hx⟩
    have hxX : ReferenceFirstCollectionStagedConditionalService.X
        (rate := rate) rewards C_star C_h i t z = 1 := by
      have hobs := ReferenceFirstCollectionRoundEndObservation.observation_eq_X
        (rate := rate) rewards C_star C_h i t.val t.isLt
      have hxobs : PhaseServiceWaiting.observation
          (ReferenceFirstCollectionRoundEndObservation.x
            (rate := rate) rewards C_star C_h) i t.val z = 1 := by
        simp [PhaseServiceWaiting.observation, hx]
      exact (congrFun hobs z).symm.trans hxobs
    by_cases hOld : z ∈ ReferenceFirstCollectionStagedConditionalService.OLD
        (p := p) (rate := rate) rewards C_star C_h i t
    · exact Or.inl ⟨hawait, hOld, hx⟩
    · have hFormed : z ∈ ReferenceFirstCollectionStagedConditionalService.FORMED
          (p := p) (rate := rate) rewards C_star C_h i t := by
        by_contra hnot
        have hzero : ReferenceFirstCollectionStagedConditionalService.X
            (rate := rate) rewards C_star C_h i t z = 0 := by
          simp [ReferenceFirstCollectionStagedConditionalService.X, hOld, hnot]
        rw [hzero] at hxX
        norm_num at hxX
      exact Or.inr ⟨hawait, hFormed, hx⟩
  · rintro (⟨hawait, _, hx⟩ | ⟨hawait, _, hx⟩)
    · exact ⟨hawait, hx⟩
    · exact ⟨hawait, hx⟩

private def localOrdinaryState?
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (configuration : DeclaredFollowerLocalRound.LocalConfiguration p rate) :
    Option (ReferencePrelaunchFollower.State p rate.eta) :=
  match configuration with
  | .ordinary state _ => some state
  | .dagger => none

private theorem ordinary_state_eq_of_config_eq
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (before old : ReferencePrelaunchFollower.State p rate.eta)
    (memory oldMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hconfiguration : DeclaredFollowerLocalRound.LocalConfiguration.ordinary before memory =
      DeclaredFollowerLocalRound.LocalConfiguration.ordinary old oldMemory) :
    before = old := by
  have h := congrArg (localOrdinaryState? (p := p) rate) hconfiguration
  have h' : some before = some old := by
    simpa only [localOrdinaryState?] using h
  exact Option.some.inj h'

private theorem ordinary_state_eq_of_two_configurations
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (configuration : DeclaredFollowerLocalRound.LocalConfiguration p rate)
    (before old : ReferencePrelaunchFollower.State p rate.eta)
    (memory oldMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hbefore : configuration = .ordinary before memory)
    (hold : configuration = .ordinary old oldMemory) :
    before = old := by
  exact ordinary_state_eq_of_config_eq rate before old memory oldMemory
    (hbefore.symm.trans hold)

private theorem ordinary_state_eq_of_aligned_states
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (i : Fin (p.m - 1))
    (state recordState : ReferenceActivePhysicalStep.State p rate)
    (before old : ReferencePrelaunchFollower.State p rate.eta)
    (memory oldMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hstate : state = recordState)
    (hordinary : state.followers i =
      DeclaredFollowerLocalRound.LocalConfiguration.ordinary before memory)
    (hfocus : recordState.followers i =
      DeclaredFollowerLocalRound.LocalConfiguration.ordinary old oldMemory) :
    before = old := by
  have hfollow : state.followers i = recordState.followers i :=
    congrArg (fun s => s.followers i) hstate
  exact ordinary_state_eq_of_config_eq rate before old memory oldMemory
    (hordinary.symm.trans (hfollow.trans hfocus))

private theorem ordinary_state_eq_of_followers_eq
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (before old : ReferencePrelaunchFollower.State p rate.eta)
    (memory oldMemory : ActiveFollowerLifecycle.LocalMemory p)
    {left right : DeclaredFollowerLocalRound.LocalConfiguration p rate}
    (hleftRight : left = right)
    (hleft : left = .ordinary before memory)
    (hright : right = .ordinary old oldMemory) :
    before = old := by
  exact ordinary_state_eq_of_config_eq rate before old memory oldMemory
    (hleft.symm.trans (hleftRight.trans hright))

private theorem prefix_ordinary_lastDown_none
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (i : Fin (p.m - 1))
    {state recordState : ReferenceActivePhysicalStep.State p rate}
    (before old : ReferencePrelaunchFollower.State p rate.eta)
    (memory oldMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hstate : state = recordState)
    (hordinary : state.followers i =
      DeclaredFollowerLocalRound.LocalConfiguration.ordinary before memory)
    (hfocus : recordState.followers i =
      DeclaredFollowerLocalRound.LocalConfiguration.ordinary old oldMemory)
    (hnone : old.lastDown = none) :
    before.lastDown = none := by
  have hfollowers := congrArg (fun s : ReferenceActivePhysicalStep.State p rate => s.followers i)
    hstate
  have hsame := ordinary_state_eq_of_followers_eq rate before old memory oldMemory
    hfollowers hordinary hfocus
  simpa only [hsame] using hnone

private theorem oldSupport_record_state
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hrecord : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z = some record)
    (hOld : z ∈ ReferenceFirstCollectionStagedConditionalService.OLD
      (p := p) (rate := rate) rewards C_star C_h i t) :
    ∃ old memory, record.input.state.followers i = .ordinary old memory ∧
      old.lastDown = none := by
  change z ∈ ReferenceFirstCutoffStageConditionalService.cutoffOldStageSupport
        (p := p) (rate := rate) rewards C_star C_h i t ∪
      ⋃ word : ReferenceFirstCollectionStagedConditionalService.DownWord p,
        ReferenceCollectionDownReadySupportMeasurability.collectionDownReadySupport
          (p := p) (rate := rate) rewards C_star C_h i t word at hOld
  rcases hOld with hcut | hcontinue
  · obtain ⟨word, hcut⟩ := Set.mem_iUnion.mp hcut
    rcases hcut with ⟨r, hr, registers, owned, base, hlive, hchosen,
      hallOrdinary, old, memory, hfocus, hnone, hword⟩
    have heq : r = record := Option.some.inj (hr.symm.trans hrecord)
    subst r
    exact ⟨old, memory, hfocus, hnone⟩
  · obtain ⟨word, hcontinue⟩ := Set.mem_iUnion.mp hcontinue
    rcases hcontinue with ⟨r, hr, payload, ledger, saved, old, memory,
      hready, hpending, hfocus, hnone, hword, hallOrdinary⟩
    have heq : r = record := Option.some.inj (hr.symm.trans hrecord)
    subst r
    exact ⟨old, memory, hfocus, hnone⟩

private theorem actualRecord_window
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (count : ℕ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : ReferenceFirstCollectionReadyStream.startTime
      (rate := rate) source rewards C_star C_h + count ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionReadyStream.actualEpoch
        (rate := rate) source rewards C_star C_h hcross count hspan).records).length < count)
    (n : Fin (ReferenceFirstCollectionReadyStream.actualWindow
      (rate := rate) source rewards C_star C_h hcross count hspan).length) :
    ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
      (ReferenceFirstCollectionReadyStream.actualWindow
        (rate := rate) source rewards C_star C_h hcross count hspan)[n.val].input.time
      source = some (ReferenceFirstCollectionReadyStream.actualWindow
        (rate := rate) source rewards C_star C_h hcross count hspan)[n.val] ∧
    (ReferenceFirstCollectionReadyStream.actualWindow
      (rate := rate) source rewards C_star C_h hcross count hspan)[n.val].input.time.val + 1 =
      ReferenceFirstCollectionReadyStream.startTime (rate := rate) source rewards C_star C_h +
        (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
          (ReferenceFirstCollectionReadyStream.actualEpoch
            (rate := rate) source rewards C_star C_h hcross count hspan).records).length + 1 + n.val := by
  let s := ReferenceFirstCollectionReadyStream.startTime
    (rate := rate) source rewards C_star C_h
  let initial := ReferenceFirstCollectionEpochAlignment.actualLaunchState
    rate source rewards C_star C_h hcross
  let E := ReferenceFirstCollectionReadyStream.actualEpoch
    (rate := rate) source rewards C_star C_h hcross count hspan
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length
  let B := ReferenceCollectionPhaseHistory.collectionWindow E.records w
  have hwindow := ReferenceFirstCollectionReadyStep.actual_collection_window_record_alignment
    rate source rewards C_star C_h count hcross hspan hshort n
  have hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h = some initial :=
    Option.eq_some_of_isSome
      ((ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
        rate source rewards C_star C_h).2 hcross)
  have hactive :=
    (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
      rate source rewards C_star C_h hcross).1
  have htime : B[n.val].input.time.val = s + (w + n.val) := by
    have ht := hwindow.2.1
    change B[n.val].input.time.val + 1 = s + w + 1 + n.val at ht
    omega
  have hcount : E.records.length = count :=
    ReferenceActivePhysicalHorizon.run_record_count _ _ _ _ _ _ _ _
  have hindex : w + n.val < count := by
    have hb' := (List.getElem?_eq_some_iff.mp hwindow.1).1
    have hb : w + n.val < E.records.length := by
      simpa only [E, w, ReferenceFirstCollectionReadyStream.actualEpoch] using hb'
    omega
  have hrecordAt : B[n.val] = ReferenceAssignmentPayloadChronology.actualRunRecordAt
      initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
      rewards s (w + n.val) (by omega) hactive := by
    have hat := ReferenceLocalReleaseGateChronology.run_record_at initial source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s hactive count
      (by simpa only [s, ReferenceFirstCollectionReadyStream.startTime] using hspan)
      ⟨w + n.val, hindex⟩
    apply Option.some.inj
    calc
      some B[n.val] = E.records[w + n.val]? := hwindow.1.symm
      _ = _ := by
        rw [List.getElem?_eq_getElem (by rw [hcount]; exact hindex)]
        simpa only [E, initial,
          ReferenceFirstCollectionReadyStream.actualEpoch,
          ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun] using
          congrArg some hat
  have hsource := ReferenceSourcePrefixHistoryFiltration.actualRecord_on_launch
    rate rewards C_star C_h B[n.val].input.time source initial hlaunch
    (by rw [show ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h = s by rfl,
      htime]; omega)
  have hsource' : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h B[n.val].input.time source =
        some (ReferenceAssignmentPayloadChronology.actualRunRecordAt initial source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s
          (w + n.val) (by omega) hactive) := by
    simpa only [show ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h = s by rfl,
      htime, Nat.add_sub_cancel_left] using hsource
  refine ⟨?_, ?_⟩
  · simpa only [B, E, w, ReferenceFirstCollectionReadyStream.actualWindow] using
      hsource'.trans (congrArg some hrecordAt.symm)
  · simpa only [B, E, w, ReferenceFirstCollectionReadyStream.actualWindow,
      ReferenceFirstCollectionReadyStream.actualEpoch] using hwindow.2.1

/-- A true existing staged OLD readout on its actual record is exactly one
positive entry in the record's literal replay call. -/
private theorem oldSupport_positive_singleton
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (htime : record.input.time = t)
    (hrecord : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z = some record)
    (hOld : z ∈ ReferenceFirstCollectionStagedConditionalService.OLD
      (p := p) (rate := rate) rewards C_star C_h i t)
    (hx : ReferenceFirstCollectionRoundEndObservation.x
      (rate := rate) rewards C_star C_h i t.val z = true) :
    ∃ entry : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p),
      entry.time = t ∧ entry ∈ ReferenceFollowerDownDecoderReplay.actualDownPositives
        (rate := rate) i [record] := by
  classical
  have hrecordTime : record.input.time = t := htime
  obtain ⟨old, memory, hfocus, hnone⟩ := oldSupport_record_state
    rate rewards C_star C_h i t z record hrecord hOld
  have hnotFormed : z ∉ ReferenceFirstCollectionStagedConditionalService.FORMED
      (p := p) (rate := rate) rewards C_star C_h i t := by
    intro hFormed
    exact (Set.disjoint_left.mp
      (ReferenceFirstCollectionStagedConditionalService.disjoint_OLD_FORMED
        (p := p) (rate := rate) rewards C_star C_h i t)) hOld hFormed
  have hobs : PhaseServiceWaiting.observation
      (ReferenceFirstCollectionRoundEndObservation.x
        (rate := rate) rewards C_star C_h) i t.val z = 1 := by
    simp [PhaseServiceWaiting.observation, hx]
  rw [ReferenceFirstCollectionRoundEndObservation.observation_eq_X
    (rate := rate) rewards C_star C_h i t.val t.isLt] at hobs
  have hreadout :
      ReferenceFirstCollectionDownConditionalService.actualFirstCollectionDownReadout
        (rate := rate) rewards C_star C_h i t z = 1 := by
    simpa [ReferenceFirstCollectionStagedConditionalService.X,
      Set.indicator_of_mem hOld, Set.indicator_of_notMem hnotFormed] using hobs
  have hservice :
      PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
          (record.input.row.2 t).1 = i ∧
        ReferenceActiveAffinePositiveTest.downPositive record.input = true := by
    simp only [ReferenceFirstCollectionDownConditionalService.actualFirstCollectionDownReadout,
      hrecord] at hreadout
    split_ifs at hreadout with h
    · exact h
    · norm_num at hreadout
  rcases hservice with ⟨hdraw, hpositive⟩
  have hselectedIndex : ReferenceActivePhysicalStep.upSenderIndex record.input = i := by
    unfold ReferenceActivePhysicalStep.upSenderIndex
    rw [CoordinatorUpMeasurability.selectedFollowerIndex_eq_draw]
    rw [hrecordTime]
    simpa [PublicDiscreteDraws.followerCount] using hdraw
  have hpositive' := hpositive
  rw [ReferenceActiveAffinePositiveTest.record_downPositive, hselectedIndex] at hpositive'
  simp only [Bool.and_eq_true] at hpositive'
  rcases hpositive' with ⟨hdiag, hown⟩
  have hownPos : 0 <
      (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i).val.val := by
    simpa only [decide_eq_true_eq,
      ReferenceFollowerDownDecoderReplay.preparedOwnObservation] using hown
  let prepared := record.output.preparation.followers.followers i
  let own := record.output.preparation.feedback.observations
    (PublicDiscreteDraws.followerPlayer p.two_le_m i)
  have hpreparedObservation : record.output.followers i =
      record.output.preparation.observeFollower i := by
    rw [record.output_eq]
    rfl
  have hdiag' : ReferenceActiveAffinePositiveTest.downDiagnosticCall
      (ReferenceActivePhysicalStep.finishFollower
        record.output.preparation.coordinator.downView prepared own) = true := by
    simpa [ReferenceActivePhysicalStep.PreparedRound.observeFollower, prepared, own,
      hpreparedObservation] using hdiag
  have hgate : ReferenceActiveAffinePositiveTest.downCallGate prepared own = true := by
    rw [← ReferenceActiveAffinePositiveTest.finishFollower_down_call]
    exact hdiag'
  have hchoiceConfig : ∃ choice choiceMemory,
      ReferenceFollowerDownDecoderReplay.preparedChoiceConfiguration record i =
        .ordinary choice choiceMemory := by
    cases hc : prepared.configuration with
    | dagger => simp [ReferenceActiveAffinePositiveTest.downCallGate, hc] at hgate
    | ordinary choice choiceMemory => exact ⟨choice, choiceMemory, by
        simp [ReferenceFollowerDownDecoderReplay.preparedChoiceConfiguration,
          prepared, hc]⟩
  rcases hchoiceConfig with ⟨choice, choiceMemory, hchoice⟩
  have hgatePrefix : ReferenceActiveAffinePositiveTest.downPrefixGate
      (p := p) (rate := rate) i
      (ReferenceFollowerDownDecoderReplay.preparedChoiceRow record i)
      (ReferenceFollowerDownDecoderReplay.preparedChoiceTime record i)
      (.ordinary choice choiceMemory) = true := by
    have h := hgate
    rw [ReferenceActiveAffinePositiveTest.downCallGate_eq_prefix] at h
    have hprepConfig : prepared.configuration = .ordinary choice choiceMemory := by
      simpa only [ReferenceFollowerDownDecoderReplay.preparedChoiceConfiguration,
        prepared] using hchoice
    change ReferenceActiveAffinePositiveTest.downPrefixGate prepared.follower prepared.row
      prepared.time prepared.configuration = true at h
    have hprepAlignment := record.output.preparation.follower_alignment i
    have hprepFollower : prepared.follower = i := hprepAlignment.2.1
    rw [hprepFollower, hprepConfig] at h
    change ReferenceActiveAffinePositiveTest.downPrefixGate i prepared.row prepared.time
      (.ordinary choice choiceMemory) = true
    exact h
  have hgateData :
      ActiveFollowerDownAcceptance.downSelected p i
          (ReferenceFollowerDownDecoderReplay.preparedChoiceRow record i)
          (ReferenceFollowerDownDecoderReplay.preparedChoiceTime record i) ∧
        choice.status = .unoccupied := by
    have h := hgatePrefix
    change decide (ActiveFollowerLifecycle.localBufferValid choice ∧
      ReferenceActiveAffinePositiveTest.downReceiverGate i
        (ReferenceFollowerDownDecoderReplay.preparedChoiceRow record i)
        (ReferenceFollowerDownDecoderReplay.preparedChoiceTime record i) choice) = true at h
    have hp := of_decide_eq_true h
    rcases hp with ⟨_, hreceiver⟩
    exact ⟨hreceiver.1, hreceiver.2.1⟩
  have heligible : AffineBatchDecoder.eligible
      (ActiveFollowerDownAcceptance.currentRoundInput p i
        (ReferenceFollowerDownDecoderReplay.preparedChoiceRow record i)
        (ReferenceFollowerDownDecoderReplay.preparedChoiceTime record i)
        (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i)
        rate choice) := by
    apply (ReferenceFollowerDownDecoderReplay.actualDownCall_eligible_iff
      record i choice).2
    exact ⟨hgateData.1, hgateData.2, hownPos⟩
  have hcall := ReferenceFollowerDownDecoderReplay.actualDownCall_ordinary
    record i choice choiceMemory hchoice
  let entry : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p) :=
    ⟨ReferenceFollowerDownDecoderReplay.preparedChoiceTime record i,
      ((ReferenceFollowerDownDecoderReplay.preparedChoiceRow record i).2
        (ReferenceFollowerDownDecoderReplay.preparedChoiceTime record i)).2 (0, i)⟩
  have hentry : entry ∈ ReferenceFollowerDownDecoderReplay.actualDownPositives
      (rate := rate) i [record] := by
    unfold ReferenceFollowerDownDecoderReplay.actualDownPositives
      ReferenceFollowerDownDecoderReplay.actualDownCalls
    simp only [List.filterMap_cons, List.filterMap_nil, hcall,
      ReferenceFollowerDownDecoderReplay.positiveCallEntries,
      List.flatMap_cons, List.flatMap_nil, List.append_nil]
    have hpositiveAt : AffineBatchDecoder.positiveAt p
        (ActiveFollowerDownAcceptance.currentInputExtension p
          (ActiveFollowerDownAcceptance.currentRoundInput p i
            (ReferenceFollowerDownDecoderReplay.preparedChoiceRow record i)
            (ReferenceFollowerDownDecoderReplay.preparedChoiceTime record i)
            (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i)
            rate choice)) (ReferenceFollowerDownDecoderReplay.preparedChoiceTime record i) =
        [entry] := by
      unfold AffineBatchDecoder.positiveAt
      have heligible' : AffineBatchDecoder.eligible
          (ActiveFollowerDownAcceptance.currentInputExtension p
            (ActiveFollowerDownAcceptance.currentRoundInput p i
              (ReferenceFollowerDownDecoderReplay.preparedChoiceRow record i)
              (ReferenceFollowerDownDecoderReplay.preparedChoiceTime record i)
              (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i)
              rate choice)
            (ReferenceFollowerDownDecoderReplay.preparedChoiceTime record i)) := by
        simpa only [ActiveFollowerDownAcceptance.currentInputExtension] using heligible
      rw [ite_eq_left heligible']
      simp [AffineBatchDecoder.entry, ActiveFollowerDownAcceptance.currentInputExtension,
        ActiveFollowerDownAcceptance.currentRoundInput, entry]
    rw [hpositiveAt]
    simp
  have hpreparedTime := ReferenceFollowerDownDecoderReplay.preparedChoiceTime_eq_recordTime record i
  refine ⟨entry, ?_, hentry⟩
  calc
    entry.time = ReferenceFollowerDownDecoderReplay.preparedChoiceTime record i := rfl
    _ = record.input.time := hpreparedTime
    _ = t := hrecordTime

private theorem positive_entries_append
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (i : Fin (p.m - 1))
    (left right : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))) :
    ReferenceFollowerDownDecoderReplay.actualDownPositives i (left ++ right) =
      ReferenceFollowerDownDecoderReplay.actualDownPositives i left ++
        ReferenceFollowerDownDecoderReplay.actualDownPositives i right := by
  simp only [ReferenceFollowerDownDecoderReplay.actualDownPositives,
    ReferenceFollowerDownDecoderReplay.actualDownCalls, List.filterMap_append,
    ReferenceFollowerDownDecoderReplay.positiveCallEntries, List.flatMap_append]

private theorem singleton_positive_mem_take
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (i : Fin (p.m - 1))
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (j k : ℕ) (hj : j < records.length) (hjk : j < k)
    (entry : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p))
    (hentry : entry ∈ ReferenceFollowerDownDecoderReplay.actualDownPositives
      i [records[j]]) :
    entry ∈ ReferenceFollowerDownDecoderReplay.actualDownPositives i (records.take k) := by
  have hfirst : entry ∈ ReferenceFollowerDownDecoderReplay.actualDownPositives
      i (records.take (j + 1)) := by
    rw [List.take_succ_eq_append_getElem hj, positive_entries_append]
    exact List.mem_append_right _ hentry
  have hdecomp : records.take k = records.take (j + 1) ++
      (records.take k).drop (j + 1) := by
    calc
      records.take k = (records.take k).take (j + 1) ++
          (records.take k).drop (j + 1) := (List.take_append_drop _ _).symm
      _ = records.take (j + 1) ++ (records.take k).drop (j + 1) := by
        rw [List.take_take, Nat.min_eq_left (by omega)]
  rw [hdecomp, positive_entries_append]
  exact List.mem_append_left _ hfirst

/-- Localize an earlier counted date and retain its literal stamped entry in
one fixed actual collection prefix. This helper has no endpoint-state lets. -/
private theorem earlier_counted_time_mem
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (count : ℕ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : ReferenceFirstCollectionReadyStream.startTime
      (rate := rate) source rewards C_star C_h + count ≤ p.T)
    (hcountEq : count = p.T -
      ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionReadyStream.actualEpoch
        (rate := rate) source rewards C_star C_h hcross count hspan).records).length < count)
    (k : Fin (ReferenceFirstCollectionReadyStream.actualWindow
      (rate := rate) source rewards C_star C_h hcross count hspan).length)
    (t : Fin p.T)
    (hbefore : t.val < (ReferenceFirstCollectionReadyStream.actualWindow
      (rate := rate) source rewards C_star C_h hcross count hspan)[k.val].input.time.val)
    (hraw : i ∈ ReferenceFirstCollectionPendingObservation.Praw
      rate rewards C_star C_h t.val source)
    (hOld : source ∈ ReferenceFirstCollectionStagedConditionalService.OLD
      (p := p) (rate := rate) rewards C_star C_h i t)
    (hx : ReferenceFirstCollectionRoundEndObservation.x
      (rate := rate) rewards C_star C_h i t.val source = true) :
    ∃ entry : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p),
      entry.time = t ∧ entry ∈ ReferenceFollowerDownDecoderReplay.actualDownPositives i
        ((ReferenceFirstCollectionReadyStream.actualWindow
          (rate := rate) source rewards C_star C_h hcross count hspan).take k.val) := by
  let E := ReferenceFirstCollectionReadyStream.actualEpoch
    (rate := rate) source rewards C_star C_h hcross count hspan
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length
  let B := ReferenceFirstCollectionReadyStream.actualWindow
    (rate := rate) source rewards C_star C_h hcross count hspan
  have hrecords := ReferenceCompleteFirstPhaseObservationRecovery.completeSuffixRecords_eq_actualFirstEpoch
    (rate := rate) rewards C_star C_h source hcross
  have hrecords' : ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h = E.records := by
    cases hcountEq
    simpa only [E, ReferenceFirstCollectionReadyStream.actualEpoch] using hrecords
  have hraw' : (ReferenceFirstCollectionPendingObservation.Praw rate rewards C_star C_h
      t.val source).Nonempty := ⟨i, hraw⟩
  have hlocT := ReferenceFirstCollectionPendingObservation.Praw_localization
    (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) t source hraw'
  dsimp only at hlocT
  let observed := fun records : List
      (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) =>
    ∃ j : Fin (ReferenceCollectionPhaseHistory.collectionWindow records
        (ReferenceFirstLiveConfirmationHistory.firstLiveWindow records).length).length,
      (ReferenceCollectionPhaseHistory.collectionWindow records
        (ReferenceFirstLiveConfirmationHistory.firstLiveWindow records).length)[j.val].input.time = t
  have hlocE : observed E.records := Eq.mp (congrArg observed hrecords') hlocT
  have hloc : ∃ j : Fin B.length, B[j.val].input.time = t := by
    simpa only [observed, B, E, ReferenceFirstCollectionReadyStream.actualWindow,
      ReferenceFirstCollectionReadyStream.actualEpoch] using hlocE
  rcases hloc with ⟨j, hjTime⟩
  have hrecordJ := actualRecord_window rate source rewards C_star C_h count
    hcross hspan hshort j
  have hrecordK := actualRecord_window rate source rewards C_star C_h count
    hcross hspan hshort k
  have hjDate : B[j.val].input.time.val + 1 =
      ReferenceFirstCollectionReadyStream.startTime
        (rate := rate) source rewards C_star C_h + w + 1 + j.val := hrecordJ.2
  have hkDate : B[k.val].input.time.val + 1 =
      ReferenceFirstCollectionReadyStream.startTime
        (rate := rate) source rewards C_star C_h + w + 1 + k.val := hrecordK.2
  have hdateT : t.val + 1 = ReferenceFirstCollectionReadyStream.startTime
      (rate := rate) source rewards C_star C_h + w + 1 + j.val :=
    (congrArg (fun u : Fin p.T => u.val + 1) hjTime).symm.trans hjDate
  have hbeforeB : t.val < B[k.val].input.time.val := hbefore
  have hjk : j.val < k.val := by omega
  have hrecordAtT : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t source = some B[j.val] :=
    (congrArg (fun u : Fin p.T => ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h u source) hjTime).symm.trans hrecordJ.1
  obtain ⟨entry, hentryTime, hentry⟩ := oldSupport_positive_singleton
    rate rewards C_star C_h i t source B[j.val] hjTime hrecordAtT hOld hx
  exact ⟨entry, hentryTime, singleton_positive_mem_take i B j.val k.val j.isLt hjk entry hentry⟩

private theorem pending_awaited_index_before_ell
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (count : ℕ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : ReferenceFirstCollectionReadyStream.startTime
      (rate := rate) source rewards C_star C_h + count ≤ p.T)
    (hcountEq : count = p.T -
      ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionReadyStream.actualEpoch
        (rate := rate) source rewards C_star C_h hcross count hspan).records).length < count)
    (d : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
      (rate := rate) source rewards C_star C_h count hcross hspan hshort)
    (t : Fin p.T) (i : Fin (p.m - 1))
    (hraw : i ∈ ReferenceFirstCollectionPendingObservation.Praw
      rate rewards C_star C_h t.val source) :
    ∃ k : Fin (ReferenceFirstCollectionReadyStream.actualWindow
      (rate := rate) source rewards C_star C_h hcross count hspan).length,
      (ReferenceFirstCollectionReadyStream.actualWindow
        (rate := rate) source rewards C_star C_h hcross count hspan)[k.val].input.time = t ∧
        k.val < d.stream.ell := by
  let E := ReferenceFirstCollectionReadyStream.actualEpoch
    (rate := rate) source rewards C_star C_h hcross count hspan
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length
  let B := ReferenceFirstCollectionReadyStream.actualWindow
    (rate := rate) source rewards C_star C_h hcross count hspan
  have hrecords := ReferenceCompleteFirstPhaseObservationRecovery.completeSuffixRecords_eq_actualFirstEpoch
    (rate := rate) rewards C_star C_h source hcross
  have hrecords' : ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h = E.records := by
    cases hcountEq
    simpa only [E, ReferenceFirstCollectionReadyStream.actualEpoch] using hrecords
  have hlocRaw := ReferenceFirstCollectionPendingObservation.Praw_localization
    (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
    t source ⟨i, hraw⟩
  dsimp only at hlocRaw
  let observed := fun records : List
      (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) =>
    ∃ k : Fin (ReferenceCollectionPhaseHistory.collectionWindow records
        (ReferenceFirstLiveConfirmationHistory.firstLiveWindow records).length).length,
      (ReferenceCollectionPhaseHistory.collectionWindow records
        (ReferenceFirstLiveConfirmationHistory.firstLiveWindow records).length)[k.val].input.time = t
  have hlocE : observed E.records := Eq.mp (congrArg observed hrecords') hlocRaw
  have hloc : ∃ k : Fin B.length, B[k.val].input.time = t := by
    simpa only [observed, B, E, ReferenceFirstCollectionReadyStream.actualWindow,
      w, ReferenceFirstCollectionReadyStream.actualEpoch] using hlocE
  rcases hloc with ⟨k, htime⟩
  have hQlatest : (ReferenceFirstCollectionPendingObservation.Q rate rewards C_star C_h
      (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h) t source).Nonempty := by
    simpa only [ReferenceFirstCollectionPendingObservation.Praw_at] using
      (show (ReferenceFirstCollectionPendingObservation.Praw rate rewards C_star C_h
        t.val source).Nonempty from ⟨i, hraw⟩)
  have hQwindow := ReferenceFirstCollectionPendingObservation.Q_window
    (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
    source count hcross hspan hshort d k
  have hQwindow' :
      ReferenceFirstCollectionPendingObservation.Q rate rewards C_star C_h
        (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
        B[k.val].input.time source =
      if k.val = 0 then Finset.univ else
        if hk : k.val < d.stream.ell then
          (d.stream.ledgers ⟨k.val - 1, by omega⟩).pending else ∅ := by
    simpa only [B, E, w, ReferenceFirstCollectionReadyStream.actualWindow,
      ReferenceFirstCollectionReadyStream.actualEpoch] using hQwindow
  have hkEll : k.val < d.stream.ell := by
    by_cases hk0 : k.val = 0
    · have hpos := d.stream.positiveLength
      omega
    · by_contra hnot
      have hqempty : ReferenceFirstCollectionPendingObservation.Q rate rewards C_star C_h
          (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
          B[k.val].input.time source = ∅ := by
        rw [hQwindow']
        simp [hk0, hnot]
      have hQloc : (ReferenceFirstCollectionPendingObservation.Q rate rewards C_star C_h
          (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
          B[k.val].input.time source).Nonempty := by
        simpa only [htime] using hQlatest
      rw [hqempty] at hQloc
      exact Finset.not_nonempty_empty hQloc
  refine ⟨k, ?_, hkEll⟩
  simpa only [B, E, w, ReferenceFirstCollectionReadyStream.actualWindow,
    ReferenceFirstCollectionReadyStream.actualEpoch] using htime

private theorem latest_prefix_positive_quota
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (source : BootstrapPrivateRoundStreams.SourceInput p) (i : Fin (p.m - 1))
    (latest : Fin p.T) (count : ℕ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : ReferenceFirstCollectionReadyStream.startTime
      (rate := rate) source rewards C_star C_h + count ≤ p.T)
    (hcountEq : count = p.T -
      ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionReadyStream.actualEpoch
        (rate := rate) source rewards C_star C_h hcross count hspan).records).length < count)
    (hawait : i ∈ Pawait rate rewards C_star C_h latest.val source)
    (hOld : source ∈ ReferenceFirstCollectionStagedConditionalService.OLD
      (p := p) (rate := rate) rewards C_star C_h i latest) :
    ∃ k : Fin (ReferenceFirstCollectionReadyStream.actualWindow
      (rate := rate) source rewards C_star C_h hcross count hspan).length,
      (ReferenceFirstCollectionReadyStream.actualWindow
        (rate := rate) source rewards C_star C_h hcross count hspan)[k.val].input.time = latest ∧
      (ReferenceFollowerDownDecoderReplay.actualDownPositives i
        ((ReferenceFirstCollectionReadyStream.actualWindow
          (rate := rate) source rewards C_star C_h hcross count hspan).take k.val)).length <
        2 * AffineBatchDecoder.quota p := by
  let s := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
  let E := ReferenceFirstCollectionReadyStream.actualEpoch
    (rate := rate) source rewards C_star C_h hcross count hspan
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length
  let B := ReferenceCollectionPhaseHistory.collectionWindow E.records w
  let Q := AffineBatchDecoder.quota p
  have hraw : i ∈ ReferenceFirstCollectionPendingObservation.Praw
      rate rewards C_star C_h latest.val source :=
    (mem_Pawait_iff rate rewards C_star C_h latest.val source i).1 hawait |>.2
  obtain ⟨d, hwindow, _hsigma, _hrecords, hprefix⟩ :=
    Bandits.Support.ReferenceFirstCollectionAwaitedDownBatchWitness.actual_first_collection_old_down_awaited_batch_witness
      rate source rewards C_star C_h count hcross hspan hshort control0
  dsimp only [ReferenceFirstCollectionReadyStream.actualWindow,
    ReferenceFirstCollectionReadyStream.actualEpoch] at hprefix
  rcases pending_awaited_index_before_ell rate rewards C_star C_h source count
    hcross hspan hcountEq hshort d latest i hraw with ⟨k, hkTime, hkEll⟩
  have hkTimeB : B[k.val].input.time = latest := by
    simpa only [B, E, w, ReferenceFirstCollectionReadyStream.actualWindow,
      ReferenceFirstCollectionReadyStream.actualEpoch] using hkTime
  have hstart : ReferenceFirstCollectionReadyStream.startTime
      (rate := rate) source rewards C_star C_h = s := rfl
  have hrecordWindow := actualRecord_window rate source rewards C_star C_h count
    hcross hspan hshort k
  have hcalendar : latest.val = s + w + k.val := by
    have hcalendar' : B[k.val].input.time.val + 1 =
        ReferenceFirstCollectionReadyStream.startTime
          (rate := rate) source rewards C_star C_h + w + 1 + k.val := by
      simpa only [B, E, w, ReferenceFirstCollectionReadyStream.actualWindow,
        ReferenceFirstCollectionReadyStream.actualEpoch] using hrecordWindow.2
    rw [hkTimeB, hstart] at hcalendar'
    omega
  rcases hprefix i with ⟨hBlen, cutoffState, cutoffMemory, hcutoff,
    hW0small, hQlower, hQupper, hforallB⟩
  rcases hforallB k (Nat.le_of_lt hkEll) with ⟨hbound, before, memory,
    hordinary, hinput, houtput, hterminal, hzero, hprior, hthreshold⟩
  have hOldWindow : source ∈ ReferenceFirstCollectionStagedConditionalService.OLD
      (p := p) (rate := rate) rewards C_star C_h i B[k.val].input.time := by
    simpa only [hkTimeB] using hOld
  have hfocusData := oldSupport_record_state rate rewards C_star C_h i
    B[k.val].input.time source B[k.val] hrecordWindow.1 hOldWindow
  rcases hfocusData with ⟨old, oldMemory, hfocus, hnone⟩
  have hbeforeNone := prefix_ordinary_lastDown_none rate i before old memory oldMemory
    (hinput k.isLt) hordinary hfocus hnone
  have hsmall :
      (ReferenceFollowerDownDecoderReplay.actualDownPositives i (B.take k.val)).length <
        Q - cutoffState.downBatch.pending.length + Q := by
    rcases hthreshold hbeforeNone with hsmall | hambiguous
    · exact hsmall
    · rcases hambiguous with ⟨j, hjB, hjpos, hjlt, hcount, hpriorCount,
        hselected, hdate, hrows, hselectedRow, hrewards, hactualRecord,
        W, hcompleted, hmultiple, hawaited⟩
      have hdateB : (B[j.val]'hjB).input.time.val = s + w + j.val := by
        have hdateRoot : (B[j.val]'hjB).input.time.val =
            ReferenceFirstCollectionReadyStream.startTime
              (rate := rate) source rewards C_star C_h + w + j.val := by
          simpa only [B, E, w, ReferenceFirstCollectionReadyStream.actualWindow,
            ReferenceFirstCollectionReadyStream.actualEpoch] using hdate
        rw [hstart] at hdateRoot
        exact hdateRoot
      have hjBeforeLatest : (B[j.val]'hjB).input.time.val < latest.val := by
        rw [hdateB, hcalendar]
        omega
      rcases hawaited with ⟨ha, habase, hentries, hselectedCalls⟩
      let record := B[j.val]'hjB
      let M := CoordinatorLocalArmChoice.storedDownFlatWord d.stream.payload i
      let a : Fin p.T := ⟨s + w, ha⟩
      have hdownFailure :
          ReferenceFirstCollectionAwaitedDownFailureReadout.fixedAwaitedDownFailureAt
            rate rewards C_star C_h source record.input.time := by
        refine ⟨record, i, M, W, a, hactualRecord, hcompleted, habase,
          hmultiple, ?_, ?_⟩
        · intro e he
          obtain ⟨hae, het, hequation, _hsample, re, hactualRe,
            _hretime, hpositive, hcall⟩ := hentries e he
          have hawaitRe :
              ReferenceFirstCollectionAwaitedDownFailureReadout.awaitedDownAt
                rate re i M := by
            change ReferenceFirstCollectionAwaitedDownFailureReadout.awaitedDownAt
              rate re i M at hcall
            exact hcall
          exact ⟨hae, het, hequation, re, hactualRe, hpositive, hawaitRe⟩
        · intro v hva hvb hchannel
          obtain ⟨rv, hactualRv, _htimeRv, hcall⟩ :=
            hselectedCalls v hva hvb hchannel
          have hawaitRv :
              ReferenceFirstCollectionAwaitedDownFailureReadout.awaitedDownAt
                rate rv i M := by
            change ReferenceFirstCollectionAwaitedDownFailureReadout.awaitedDownAt
              rate rv i M at hcall
            exact hcall
          exact ⟨rv, hactualRv, hawaitRv⟩
      have hfailure : ReferenceFirstCollectionAwaitedDownFailureReadout.failureAt
          rate rewards C_star C_h source record.input.time :=
        Or.inr (Or.inl hdownFailure)
      have hno := no_failure_before_of_mem_Pawait rate rewards C_star C_h
        latest.val source i hawait
      exact (hno record.input.time hjBeforeLatest hfailure).elim
  have hsmall' :
      (ReferenceFollowerDownDecoderReplay.actualDownPositives i (B.take k.val)).length <
        2 * AffineBatchDecoder.quota p := by
    omega
  exact ⟨k, hkTime, hsmall'⟩

/-- The inclusive corrected OLD quota on the original calendar. The final
positive observation is retained in the count. -/
theorem actual_first_collection_old_down_quota
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (i : Fin (p.m - 1)) :
    (oldPositiveDates (p := p) rate rewards C_star C_h i z).card ≤
      2 * AffineBatchDecoder.quota p := by
  classical
  let tests := oldPositiveDates (p := p) rate rewards C_star C_h i z
  by_cases hne : tests.Nonempty
  · let latest := tests.max' hne
    have hlatest : latest ∈ tests := Finset.max'_mem tests hne
    have hlatestMax (t : Fin p.T) (ht : t ∈ tests) : t ≤ latest :=
      Finset.le_max' tests t ht
    rcases (Finset.mem_filter.mp hlatest).2 with ⟨hawait, hOld, hx⟩
    have hraw : (ReferenceFirstCollectionPendingObservation.Praw
        rate rewards C_star C_h latest.val z).Nonempty := by
      exact ⟨i, (mem_Pawait_iff rate rewards C_star C_h latest.val z i).1 hawait |>.2⟩
    have hlaunch : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
        rate rewards C_star C_h latest.val z := by
      by_contra hnot
      rw [ReferenceFirstCollectionPendingObservation.Praw_at,
        ReferenceFirstCollectionPendingObservation.Q_eq_empty_of_not_launchBy
          (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
          (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
          latest z hnot] at hraw
      exact Finset.not_nonempty_empty hraw
    have hcross : (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true := by
      simpa only [ReferenceCompletePhysicalHistory.generatedBoundary,
        ReferenceCompletePhysicalHistory.generatedInput] using hlaunch.1
    let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    let count := p.T - s
    have hcountEq : count = p.T -
        ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h := rfl
    have hspan0 := ReferenceCompleteFirstPhaseObservationRecovery.firstPhaseReadySpan
      rate rewards C_star C_h z
    have hspan : s + count ≤ p.T := by
      dsimp only [s, count]
      exact hspan0
    have hboundary := ReferenceFirstCollectionDetectedQueueMask.actual_pending_boundary_window
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
      latest z hraw
    dsimp only at hboundary
    rcases hboundary with ⟨_pair, hpair, _⟩
    rcases hpair with ⟨_, _, _, _, _, hRshort⟩
    let E := ReferenceFirstCollectionReadyStream.actualEpoch
      (rate := rate) z rewards C_star C_h hcross count hspan
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length
    let B := ReferenceFirstCollectionReadyStream.actualWindow
      (rate := rate) z rewards C_star C_h hcross count hspan
    have hrecords := ReferenceCompleteFirstPhaseObservationRecovery.completeSuffixRecords_eq_actualFirstEpoch
      (rate := rate) rewards C_star C_h z hcross
    have hcount : E.records.length = count :=
      ReferenceActivePhysicalHorizon.run_record_count _ _ _ _ _ _ _ _
    have hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length < count := by
      have hshortR : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length < E.records.length := by
        simpa only [hrecords] using hRshort
      omega
    rcases latest_prefix_positive_quota rate rewards C_star C_h control0 z i latest
      count hcross hspan hcountEq hshort hawait hOld with ⟨k, hkTime, hsmall⟩
    change (ReferenceFollowerDownDecoderReplay.actualDownPositives
      i (B.take k.val)).length < 2 * AffineBatchDecoder.quota p at hsmall
    let earlier := tests.filter fun t => t.val < latest.val
    let times := (ReferenceFollowerDownDecoderReplay.actualDownPositives i (B.take k.val)).map
      (fun entry => entry.time) |>.toFinset
    have hearlierSubset : earlier ⊆ times := by
      intro t ht
      rcases Finset.mem_filter.mp ht with ⟨htests, hltLatest⟩
      rcases (Finset.mem_filter.mp htests).2 with ⟨hawaitT, htOld, htx⟩
      have hbefore : t.val < (ReferenceFirstCollectionReadyStream.actualWindow
          (rate := rate) z rewards C_star C_h hcross count hspan)[k.val].input.time.val := by
        rw [hkTime]
        exact hltLatest
      have hrawT := (mem_Pawait_iff rate rewards C_star C_h t.val z i).1 hawaitT |>.2
      obtain ⟨entry, hentryTime, hentryInPrefix⟩ := earlier_counted_time_mem
        rate rewards C_star C_h z i count hcross hspan hcountEq hshort k t
        hbefore hrawT htOld htx
      simp only [times, List.mem_toFinset, List.mem_map]
      exact ⟨entry, hentryInPrefix, hentryTime⟩
    have hearlyCard : earlier.card ≤ times.card := Finset.card_le_card hearlierSubset
    have htimesCard : times.card ≤
        (ReferenceFollowerDownDecoderReplay.actualDownPositives i (B.take k.val)).length := by
      calc
        times.card ≤ ((ReferenceFollowerDownDecoderReplay.actualDownPositives
            i (B.take k.val)).map (fun entry => entry.time)).length :=
          List.toFinset_card_le _
        _ = (ReferenceFollowerDownDecoderReplay.actualDownPositives
            i (B.take k.val)).length := List.length_map _
    have hearlyLt : earlier.card < 2 * AffineBatchDecoder.quota p := by omega
    have htestsEq : tests = insert latest earlier := by
      ext t
      simp only [Finset.mem_insert, earlier, Finset.mem_filter]
      constructor
      · intro ht
        by_cases heq : t = latest
        · exact Or.inl heq
        · right
          refine ⟨ht, ?_⟩
          have hle := hlatestMax t ht
          have hneVal : t.val ≠ latest.val := by
            intro hval
            exact heq (Fin.ext hval)
          omega
      · intro ht
        rcases ht with rfl | ⟨ht, _⟩
        · exact hlatest
        · exact ht
    have hlatestNotEarlier : latest ∉ earlier := by simp [earlier]
    have htestsCard : tests.card = earlier.card + 1 := by
      rw [htestsEq, Finset.card_insert_of_notMem hlatestNotEarlier]
    have htestsBound : tests.card ≤ 2 * AffineBatchDecoder.quota p := by
      rw [htestsCard]
      omega
    simpa only [tests] using htestsBound
  · have hzero : tests = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    rw [show oldPositiveDates (p := p) rate rewards C_star C_h i z = tests by rfl, hzero]
    exact Nat.zero_le _

/-- The inclusive corrected FORMED quota follows from the unmasked formed
test count. A contrary outcome is itself an earlier fixed-awaited UP failure. -/
theorem actual_first_collection_formed_up_quota
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) :
    (formedPositiveDates (p := p) rate rewards C_star C_h i z).card ≤
      2 * AffineBatchDecoder.quota p := by
  classical
  let tests := formedPositiveDates (p := p) rate rewards C_star C_h i z
  by_cases hne : tests.Nonempty
  · let latest := tests.max' hne
    have hlatest : latest ∈ tests := Finset.max'_mem tests hne
    have hlatestMax (t : Fin p.T) (ht : t ∈ tests) : t ≤ latest :=
      Finset.le_max' tests t ht
    rcases (Finset.mem_filter.mp hlatest).2 with ⟨hawait, hFormed, hx⟩
    have hraw := (mem_Pawait_iff rate rewards C_star C_h latest.val z i).1 hawait |>.2
    have horigin : latest ∈
        ReferenceFirstCollectionUnmaskedFormedUpOrigin.unmaskedFormedUpTests
          rate rewards C_star C_h i z := by
      simp only [ReferenceFirstCollectionUnmaskedFormedUpOrigin.unmaskedFormedUpTests,
        Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hraw, hFormed, hx⟩
    have hcountOrFailure :=
      Bandits.Support.ReferenceFirstCollectionUnmaskedFormedUpCountOrAwaitedFailure.actual_first_collection_unmasked_formed_up_count_or_awaited_failure
        rate rewards C_star C_h z i latest horigin
    have hcount :
        ((ReferenceFirstCollectionUnmaskedFormedUpOrigin.unmaskedFormedUpTests
          rate rewards C_star C_h i z).filter
          (fun t => t.val ≤ latest.val)).card ≤
          2 * AffineBatchDecoder.quota p := by
      rcases hcountOrFailure with hbound | ⟨a, ha, hfailure⟩
      · exact hbound
      · have hno := no_failure_before_of_mem_Pawait
          rate rewards C_star C_h latest.val z i hawait
        exact (hno a ha (Or.inr (Or.inr hfailure))).elim
    have hsubset : tests ⊆
        (ReferenceFirstCollectionUnmaskedFormedUpOrigin.unmaskedFormedUpTests
          rate rewards C_star C_h i z).filter
          (fun t => t.val ≤ latest.val) := by
      intro t ht
      rcases (Finset.mem_filter.mp ht).2 with ⟨hawaitT, hFormedT, hxT⟩
      have hrawT := (mem_Pawait_iff rate rewards C_star C_h t.val z i).1 hawaitT |>.2
      have horiginT : t ∈
          ReferenceFirstCollectionUnmaskedFormedUpOrigin.unmaskedFormedUpTests
            rate rewards C_star C_h i z := by
        simp only [ReferenceFirstCollectionUnmaskedFormedUpOrigin.unmaskedFormedUpTests,
          Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hrawT, hFormedT, hxT⟩
      have hle : t.val ≤ latest.val :=
        (Fin.le_iff_val_le_val).mp (hlatestMax t ht)
      exact Finset.mem_filter.mpr ⟨horiginT, hle⟩
    have hbound := (Finset.card_le_card hsubset).trans hcount
    simpa only [tests] using hbound
  · have hzero : tests = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    rw [show formedPositiveDates (p := p) rate rewards C_star C_h i z = tests by rfl,
      hzero]
    exact Nat.zero_le _

/-- The corrected service calendar is the disjoint OLD/FORMED union and has
the inclusive `4Q` quota. -/
theorem actual_first_collection_service_positive_dates_quota
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (i : Fin (p.m - 1)) :
    (servicePositiveDates (p := p) rate rewards C_star C_h i z).card ≤
      4 * AffineBatchDecoder.quota p := by
  have hold := actual_first_collection_old_down_quota
    rate rewards C_star C_h control0 z i
  have hformed := actual_first_collection_formed_up_quota
    rate rewards C_star C_h z i
  have hdisjoint := disjoint_oldPositiveDates_formedPositiveDates
    rate rewards C_star C_h i z
  calc
    (servicePositiveDates (p := p) rate rewards C_star C_h i z).card =
        (oldPositiveDates (p := p) rate rewards C_star C_h i z).card +
          (formedPositiveDates (p := p) rate rewards C_star C_h i z).card := by
      rw [servicePositiveDates_eq_union rate rewards C_star C_h i z,
        Finset.card_union_of_disjoint hdisjoint]
    _ ≤ 2 * AffineBatchDecoder.quota p + 2 * AffineBatchDecoder.quota p :=
      Nat.add_le_add hold hformed
    _ = 4 * AffineBatchDecoder.quota p := by omega

/-- Every original-calendar prefix obeys the same service counter bound. The
prefix is a filter of exact `Fin p.T` timestamps, so no endpoint is lost. -/
theorem actual_first_collection_service_positive_prefix_quota
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (i : Fin (p.m - 1))
    (latest : ℕ) :
    ((servicePositiveDates (p := p) rate rewards C_star C_h i z).filter
      (fun t => t.val ≤ latest)).card ≤ 4 * AffineBatchDecoder.quota p := by
  calc
    ((servicePositiveDates (p := p) rate rewards C_star C_h i z).filter
        (fun t => t.val ≤ latest)).card ≤
        (servicePositiveDates (p := p) rate rewards C_star C_h i z).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ ≤ 4 * AffineBatchDecoder.quota p :=
      actual_first_collection_service_positive_dates_quota
        rate rewards C_star C_h control0 z i

end Bandits.Support.ReferenceFirstCollectionAwaitedTaskSupport

end
