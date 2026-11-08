/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedInvocationCallSplice
public import Bandits.Support.ReferenceFirstCollectionLogicalPrefixExtension

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
# Initial nonrenewed invocation after analytical overflow

The event below uses the original first invocation and its strict numerical
past. Physical play and the entire original analytical tape are retained.

Sources: ZIP4 `06_interruptions.tex:391-426`,
`04_slow_fast_learner.tex:142-215,323-390`, and
`08_main_theorem.tex:78-109`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal Classical BigOperators
open Bandits.Support ConstructorDimensions
open ReferenceFirstLiveChronologicalPrefixFoundation
open ReferenceFirstLiveChronologicalPrefixMeasurability
open ReferenceSourcePrefixHistoryFiltration
open ReferenceFirstCollectionLogicalNumericalAlignment
open ReferenceActualCollectionHiddenRefreshPath (actualOriginalWord)
open ReferenceFirstLaunchNumericalCell (queueParameters)

namespace Bandits.Support.ReferenceInitialStoppedCalendar

variable {p : ConstructorDimensions.Parameters}

abbrev Source := BootstrapPrivateRoundStreams.SourceInput
abbrev Auxiliary := ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray
abbrev TimeControl := ContinuousLearningRows.TimeControl

local instance sourceMeasurableSpace : MeasurableSpace (Source p) := by
  change MeasurableSpace (CompletePublicTable.PublishedOutput p ×
    BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

local instance optionMeasurableSpace {A : Type*} [MeasurableSpace A] :
    MeasurableSpace (Option A) := LaterAssignmentStartMeasurability.optionMeasurableSpace

local instance slowSetMeasurableSpace : MeasurableSpace (SlowSet p) := ⊤
local instance slowSetDiscrete : DiscreteMeasurableSpace (SlowSet p) := ⟨fun _ => trivial⟩

variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)

local notation "Q" => queueParameters rate
local notation "start " z:max => ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
local notation "records " z:max => ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
local notation "readout" => ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout rate rewards C_star C_h
local notation "firstCell" => ReferenceFirstCollectionAuxiliarySeeds.actualCollectionCallCell rate rewards C_star C_h
local notation "past" => ReferenceFirstCollectionLogicalPrefixExtension.extendedPast rate rewards C_star C_h

/-- The omitted nonrenewed first-call alternative: overflow has already been
detected strictly before the invocation. The old boundary is compared with
the one-based physical date `t.val + 1`. -/
def initialStoppedEvent (u t : Fin p.T) : Set (Source p) :=
  ReferenceFirstCollectionCorrectedSliceNumericalPrefix.correctedCell
    rate rewards C_star C_h u t ∩
  {z | ∃ o, readout t.val z = some o ∧ o.2.1 = true}

abbrev StoppedSource (u t : Fin p.T) := ↥(initialStoppedEvent rate rewards C_star C_h u t)

theorem measurableSet_initialStoppedEvent (u t : Fin p.T) :
    MeasurableSet (initialStoppedEvent rate rewards C_star C_h u t) := by
  apply (ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.measurableSet_correctedCell
    rate rewards C_star C_h u t).inter
  have hm := (ReferenceCollectionOutcomeMeasurability.measurable_optionalElim false
    (fun o : ReferenceFirstCollectionCurrentQueueReadout.QueueReadout p.K => o.2.1)
    (measurable_fst.comp measurable_snd)).comp
      ((ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.measurable_prefixReadout
        rate rewards C_star C_h t.val).mono le_rfl le_top)
  have hs := (measurableSet_singleton true).preimage hm
  convert hs using 1
  ext z
  cases h : readout t.val z with
  | none => simp [ReferenceCollectionOutcomeMeasurability.optionalElim, h]
  | some o =>
    rcases o with ⟨registers, overflow, history⟩
    cases overflow <;> simp [ReferenceCollectionOutcomeMeasurability.optionalElim, h]

theorem initialStoppedEvent_subset_firstCell (u t : Fin p.T) :
    initialStoppedEvent rate rewards C_star C_h u t ⊆ firstCell u t :=
  fun _ hz => hz.1.1

theorem initialStoppedEvent_firstCall (u t : Fin p.T) (z : Source p)
    (hz : z ∈ initialStoppedEvent rate rewards C_star C_h u t) :
    ∃ theta, ReferenceFirstCollectionSamplerCall.firstCollectionCall
      rate rewards C_star C_h z = some (u, (t, theta)) := by
  have h := hz.1.1
  change (ReferenceFirstCollectionSamplerCall.firstCollectionCall
    rate rewards C_star C_h z).map (fun c => (c.1, c.2.1)) = some (u, t) at h
  obtain ⟨⟨u', t', theta⟩, hc, heq⟩ := Option.map_eq_some_iff.mp h
  cases heq
  exact ⟨theta, hc⟩

/-- Current and future physical controls do not decide this PRE event. -/
theorem initialStoppedEvent_suffix_forward (u t : Fin p.T) (z : Source p)
    (suffix : Fin p.T → TimeControl p)
    (hz : z ∈ initialStoppedEvent rate rewards C_star C_h u t) :
    ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix z t suffix ∈
      initialStoppedEvent rate rewards C_star C_h u t := by
  obtain ⟨theta, hc⟩ := initialStoppedEvent_firstCall rate rewards C_star C_h u t z hz
  refine ⟨⟨(ReferenceFirstCollectionRenewalPastLocality.actualCollectionCallCell_iff_replaceSelectedControlSuffix
    rate rewards C_star C_h z u t suffix).mp hz.1.1, ?_⟩, ?_⟩
  · rw [← ReferenceFirstCollectionRenewalPastLocality.oldFreezeAt?_eq_of_replaceSelectedControlSuffix
      rate rewards C_star C_h z u t theta suffix hc]
    exact hz.1.2
  · change ∃ o, readout t.val
        (ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix z t suffix) = some o ∧
        o.2.1 = true
    unfold ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout
    rw [ReferenceFirstLiveCollectionPathJoin.firstCall_prefixInputs_suffix
      rate rewards C_star C_h u t z theta suffix hc]
    exact hz.2

theorem initialStoppedEvent_suffix_iff (u t : Fin p.T) (z : Source p)
    (suffix : Fin p.T → TimeControl p) :
    z ∈ initialStoppedEvent rate rewards C_star C_h u t ↔
      ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix z t suffix ∈
        initialStoppedEvent rate rewards C_star C_h u t := by
  constructor
  · exact initialStoppedEvent_suffix_forward rate rewards C_star C_h u t z suffix
  · intro hz
    have h := initialStoppedEvent_suffix_forward rate rewards C_star C_h u t _
      (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)).2 hz
    rw [ReferenceFirstCollectionRenewalPastLocality.replaceSelectedControlSuffix_restore] at h
    exact h

theorem initialStoppedEvent_sourcePrefix (control0 : TimeControl p) (u t : Fin p.T)
    (n : ℕ) (htn : t.val ≤ n) (z : Source p) :
    z ∈ initialStoppedEvent rate rewards C_star C_h u t ↔
      sourcePrefix control0 n z ∈ initialStoppedEvent rate rewards C_star C_h u t := by
  have ht (w : Source p) : w ∈ initialStoppedEvent rate rewards C_star C_h u t ↔
      sourcePrefix control0 t.val w ∈ initialStoppedEvent rate rewards C_star C_h u t := by
    rw [sourcePrefix_eq_suffix control0 t.val t.isLt]
    exact initialStoppedEvent_suffix_iff rate rewards C_star C_h u t w (fun _ => control0)
  rw [ht z, ht (sourcePrefix control0 n z), sourcePrefix_sourcePrefix control0 t.val n htn]

/-- Measurability in the exact accepted PRE filtration. -/
theorem initialStoppedEvent_preMeasurable (control0 : TimeControl p) (u t : Fin p.T) :
    MeasurableSet[sourcePrefixFiltration control0 (t.val + 1)]
      (initialStoppedEvent rate rewards C_star C_h u t) := by
  rw [sourcePrefixFiltration_succ, MeasurableSpace.measurableSet_comap]
  refine ⟨initialStoppedEvent rate rewards C_star C_h u t,
    measurableSet_initialStoppedEvent rate rewards C_star C_h u t, ?_⟩
  ext z
  exact (initialStoppedEvent_sourcePrefix rate rewards C_star C_h control0 u t t.val le_rfl z).symm

theorem initialStoppedEvent_noCallBefore (u t : Fin p.T) (z : Source p)
    (hz : z ∈ initialStoppedEvent rate rewards C_star C_h u t) :
    ReferenceFirstCollectionLogicalPrefixExtension.NoCallBefore
      rate rewards C_star C_h t.castSucc z := by
  obtain ⟨theta, hc⟩ := initialStoppedEvent_firstCall rate rewards C_star C_h u t z hz
  have hf : ReferenceCalendarCollectionCallControlLaw.firstAt rate rewards C_star C_h t z =
      some (u, theta) := by
    simp only [ReferenceCalendarCollectionCallControlLaw.firstAt, hc, Option.bind_some, ite_true]
  rw [ReferenceCalendarCollectionCallControlLaw.firstAt_eq] at hf
  have hearlier : ∀ v : Fin p.T, v.val < t.val →
      ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h v z = none := by
    by_contra h
    rw [ite_eq_right h] at hf
    cases hf
  intro v hv
  exact (ReferenceFirstCollectionLogicalPrefixExtension.noCallAt_iff_callAt_none
    rate rewards C_star C_h v z).mpr (hearlier v hv)

/-- This root is separate from every active-rank owner's root, including
renewal roots whose PRE state may already be stopped. -/
theorem initialStoppedEvent_disjoint_branch (u t u' t' : Fin p.T) (b : Bool) :
    Disjoint (initialStoppedEvent rate rewards C_star C_h u t)
      (ReferencePostInvocationPrefixLocality.branchEvent rate rewards C_star C_h b u' t') := by
  apply Set.disjoint_left.mpr
  intro z hz hb
  have hfirst : z ∈ firstCell u' t' := by
    cases b with
    | false => exact (ReferenceFirstLiveCollectionPathJoin.firstLiveCollectionEvent_facts
        rate rewards C_star C_h u' t' z hb).1
    | true => exact hb.1
  have htags : (u, t) = (u', t') := Option.some.inj (hz.1.1.symm.trans hfirst)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj htags
  cases b with
  | false =>
    change z ∈ ReferenceFirstLiveCollectionPathJoin.firstLiveCollectionEvent
      rate rewards C_star C_h u t at hb
    rw [ReferenceFirstLiveCollectionPathJoin.firstLiveCollectionEvent_eq_correctedCell] at hb
    obtain ⟨o, ho, hstop⟩ := hz.2
    obtain ⟨o', ho', hclear⟩ := hb.2
    have heq : o = o' := Option.some.inj (ho.symm.trans ho')
    rw [heq, hclear] at hstop
    cases hstop
  | true =>
    obtain ⟨g, hg, hgt⟩ := hz.1.2
    obtain ⟨g', hg', hle⟩ := hb.2
    have heq : g = g' := Option.some.inj (hg.symm.trans hg')
    omega

/-- The original complete word, on a carrier where its real launch has
already been proved from the actual invocation. -/
def originalWord (u t : Fin p.T) (z : StoppedSource rate rewards C_star C_h u t) :
    List (RecordedQueueRun.RoundInput p.K) :=
  actualOriginalWord rate rewards C_star C_h z.val
    (firstCall_launch rate rewards C_star C_h u t z.val z.property.1.1)

theorem originalWord_length (u t : Fin p.T) (z : StoppedSource rate rewards C_star C_h u t) :
    (originalWord rate rewards C_star C_h u t z).length = p.T - start z.val := by
  rw [originalWord, ReferenceActualCollectionHiddenRefreshPath.actualOriginalWord_length,
    ReferenceCompletePhysicalHistory.completeSuffixRecords_length]

theorem originalWord_prefix (u t : Fin p.T) (z : StoppedSource rate rewards C_star C_h u t)
    (n : Fin (p.T + 1)) (htn : t.val ≤ n.val) :
    ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs rate rewards C_star C_h n.val z.val =
      some ((originalWord rate rewards C_star C_h u t z).take (n.val - start z.val)) := by
  have hd := firstCall_dates rate rewards C_star C_h u t z.val z.property.1.1
  exact (originalWord_calendar_prefix rate rewards C_star C_h z.val
    (firstCall_launch rate rewards C_star C_h u t z.val z.property.1.1)
    n (by omega)).2.2

theorem originalWord_stopped (u t : Fin p.T) (z : StoppedSource rate rewards C_star C_h u t) :
    (RecordedQueueRun.run Q ((originalWord rate rewards C_star C_h u t z).take
      (t.val - start z.val))).overflow = true := by
  obtain ⟨o, ho, hstop⟩ := z.property.2
  have hp := originalWord_prefix rate rewards C_star C_h u t z t.castSucc le_rfl
  simp only [Fin.val_castSucc] at hp
  rw [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout, hp, Option.map_some] at ho
  exact (congrArg (fun v => v.2.1) (Option.some.inj ho)).trans hstop

/-- The least detecting prefix of the actual complete numerical word. -/
def detectingPrefix (u t : Fin p.T) (z : StoppedSource rate rewards C_star C_h u t) : ℕ :=
  UnstoppedRecordedQueueComparison.firstOverflowPrefix Q (originalWord rate rewards C_star C_h u t z)

theorem detectingPrefix_bounds (u t : Fin p.T) (z : StoppedSource rate rewards C_star C_h u t) :
    0 < detectingPrefix rate rewards C_star C_h u t z ∧
      detectingPrefix rate rewards C_star C_h u t z ≤ t.val - start z.val := by
  refine ⟨UnstoppedRecordedQueueComparison.first_overflow_prefix_pos Q _, ?_⟩
  apply (UnstoppedRecordedQueueComparison.prefix_overflow_iff_first_overflow_prefix_le
    Q _ (t.val - start z.val) ?_).mp
    (originalWord_stopped rate rewards C_star C_h u t z)
  rw [originalWord_length]
  exact Nat.sub_le_sub_right (Nat.le_of_lt t.isLt) _

/-- The detecting update is strictly before the first invocation. -/
def detectingDate (u t : Fin p.T) (z : StoppedSource rate rewards C_star C_h u t) : Fin p.T :=
  ⟨start z.val + detectingPrefix rate rewards C_star C_h u t z - 1, by
    have hd := firstCall_dates rate rewards C_star C_h u t z.val z.property.1.1
    have hk := detectingPrefix_bounds rate rewards C_star C_h u t z
    have ht := t.isLt
    omega⟩

theorem detectingDate_lt (u t : Fin p.T) (z : StoppedSource rate rewards C_star C_h u t) :
    (detectingDate rate rewards C_star C_h u t z).val < t.val := by
  have hd := firstCall_dates rate rewards C_star C_h u t z.val z.property.1.1
  have hk := detectingPrefix_bounds rate rewards C_star C_h u t z
  dsimp only [detectingDate]
  omega

theorem detecting_update (u t : Fin p.T) (z : StoppedSource rate rewards C_star C_h u t) :
    let W := originalWord rate rewards C_star C_h u t z
    let k := detectingPrefix rate rewards C_star C_h u t z
    ∃ hk : k - 1 < W.length,
      (RecordedQueueRun.run Q (W.take (k - 1))).overflow = false ∧
      (RecordedQueueRun.run Q (W.take k)).overflow = true ∧
      RecordedQueueRun.step Q (RecordedQueueRun.run Q (W.take (k - 1))) W[k - 1] =
        RecordedQueueRun.run Q (W.take k) ∧ W[k - 1].enabled = true ∧
      ∀ i, (RecordedQueueRun.run Q (W.take k)).registers i =
        QueueReplay.transition (4 * (Q).n)
          ((RecordedQueueRun.run Q (W.take (k - 1))).registers i)
          (RecordedQueueRun.acceptedRecord Q
            (RecordedQueueRun.run Q (W.take (k - 1))) W[k - 1] i) := by
  dsimp only
  let W := originalWord rate rewards C_star C_h u t z
  let k := detectingPrefix rate rewards C_star C_h u t z
  have hb := detectingPrefix_bounds rate rewards C_star C_h u t z
  have hlen : k ≤ W.length := by
    rw [originalWord_length]
    exact hb.2.trans (Nat.sub_le_sub_right (Nat.le_of_lt t.isLt) _)
  have hk : k - 1 < W.length := by omega
  have hpre : (RecordedQueueRun.run Q (W.take (k - 1))).overflow = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    have hh := (UnstoppedRecordedQueueComparison.prefix_overflow_iff_first_overflow_prefix_le
      Q W (k - 1) (by omega)).mp h
    change k ≤ k - 1 at hh
    omega
  have hpost : (RecordedQueueRun.run Q (W.take k)).overflow = true :=
    (UnstoppedRecordedQueueComparison.prefix_overflow_iff_first_overflow_prefix_le
      Q W k hlen).mpr le_rfl
  have hstep : RecordedQueueRun.step Q (RecordedQueueRun.run Q (W.take (k - 1))) W[k - 1] =
      RecordedQueueRun.run Q (W.take k) := by
    have he : k - 1 + 1 = k := by omega
    rw [← RecordedSlowRefresh.run_append_singleton, List.take_append_getElem hk, he]
  have hen : W[k - 1].enabled = true := by
    by_contra h
    have hdisabled : W[k - 1].enabled = false := Bool.eq_false_iff.mpr h
    have hh := ReferenceFirstCollectionRenewalFutureNumericalPrefix.disabled_step_registers_and_records
      rate (RecordedQueueRun.run Q (W.take (k - 1))) W[k - 1] hdisabled
    have hcut := (RecordedQueueRun.run_overflow_iff_cutoff Q (W.take k)).mp hpost
    rw [← hstep, hh.1] at hcut
    have hbad := (RecordedQueueRun.run_overflow_iff_cutoff Q (W.take (k - 1))).mpr hcut
    rw [hpre] at hbad
    cases hbad
  refine ⟨hk, hpre, hpost, hstep, hen, ?_⟩
  have hretain := RecordedQueueRun.step_retains_first_overflow_update Q
    (RecordedQueueRun.run Q (W.take (k - 1))) W[k - 1] hpre (hstep.symm ▸ hpost)
  rw [hstep] at hretain
  exact hretain.2

/-- The detecting update is an actual whole cell of the unchanged accepted
prefix. Both its PRE and its POST are retained, before freezing starts. -/
theorem detecting_update_mem_prefix (u t : Fin p.T)
    (z : StoppedSource rate rewards C_star C_h u t) (a : Auxiliary p) :
    ∃ e ∈ past t.castSucc (z.val, a),
      e.time = detectingDate rate rewards C_star C_h u t z ∧
      e.before = RecordedQueueRun.run Q ((originalWord rate rewards C_star C_h u t z).take
        (detectingPrefix rate rewards C_star C_h u t z - 1)) ∧
      e.after = RecordedQueueRun.run Q ((originalWord rate rewards C_star C_h u t z).take
        (detectingPrefix rate rewards C_star C_h u t z)) ∧
      e.before.overflow = false ∧ e.after.overflow = true := by
  let W := originalWord rate rewards C_star C_h u t z
  let k := detectingPrefix rate rewards C_star C_h u t z
  let q := detectingDate rate rewards C_star C_h u t z
  obtain ⟨hk, hpre, hpost, _hstep, hen, _hret⟩ := detecting_update rate rewards C_star C_h u t z
  have hs : start z.val ≤ q.val := by
    have hb := detectingPrefix_bounds rate rewards C_star C_h u t z
    dsimp only [q, detectingDate]
    omega
  have hi : q.val - start z.val = k - 1 := by
    have hb := detectingPrefix_bounds rate rewards C_star C_h u t z
    dsimp only [q, detectingDate, k]
    omega
  have hi' : q.val + 1 - start z.val = k := by
    have hb := detectingPrefix_bounds rate rewards C_star C_h u t z
    dsimp only [q, detectingDate, k]
    omega
  have hchron := firstCall_generatedPast_chronology rate rewards C_star C_h u t z.val
    z.property.1.1 a t.castSucc le_rfl
  change k - 1 < W.length at hk
  change W[k - 1].enabled = true at hen
  change _ ∧ _ ∧ ∀ q : Fin p.T, start z.val ≤ q.val → q.val < t.val →
    (q.val < u.val ∨ ∃ hk : q.val - start z.val < W.length, W[q.val - start z.val].enabled = true) →
    ∃ e ∈ past t.castSucc (z.val, a), e.time = q at hchron
  obtain ⟨e, he, heq⟩ := hchron.2.2 q hs (detectingDate_lt rate rewards C_star C_h u t z)
    (Or.inr ⟨by simpa only [hi] using hk, by simpa only [hi] using hen⟩)
  have hd := firstCall_generatedPast_cell_data rate rewards C_star C_h u t z.val
    z.property.1.1 a t.castSucc e he
  obtain ⟨_hk, _hnum, hb, ha, _⟩ := hd
  change e.before = RecordedQueueRun.run Q (W.take (e.time.val - start z.val)) at hb
  change e.after = RecordedQueueRun.run Q (W.take (e.time.val + 1 - start z.val)) at ha
  rw [heq, hi] at hb
  rw [heq, hi'] at ha
  exact ⟨e, he, heq, hb, ha, hb ▸ hpre, ha ▸ hpost⟩

/-- Registers freeze, while the actual numerical word continues advancing
through every physical calendar date. -/
theorem originalWord_frozen_suffix (u t : Fin p.T)
    (z : StoppedSource rate rewards C_star C_h u t)
    (n : Fin (p.T + 1)) (htn : t.val ≤ n.val) :
    let W := originalWord rate rewards C_star C_h u t z
    let before := RecordedQueueRun.run Q (W.take (t.val - start z.val))
    let after := RecordedQueueRun.run Q (W.take (n.val - start z.val))
    after.overflow = true ∧ ∀ i, after.registers i = before.registers i := by
  dsimp only
  let W := originalWord rate rewards C_star C_h u t z
  have hm : t.val - start z.val ≤ n.val - start z.val := Nat.sub_le_sub_right htn _
  have he : W.take (n.val - start z.val) = W.take (t.val - start z.val) ++
      (W.drop (t.val - start z.val)).take (n.val - start z.val - (t.val - start z.val)) := by
    rw [← List.take_add, Nat.add_sub_of_le hm]
  rw [he, RecordedQueueRun.run, RecordedSlowRefresh.execute_append]
  exact RecordedQueueRun.execute_after_overflow_preserves Q _ _
    (originalWord_stopped rate rewards C_star C_h u t z)

/-- Every actual date after the call has a genuine original numerical input. -/
theorem suffix_index_lt (u t q : Fin p.T) (htq : t.val ≤ q.val)
    (z : StoppedSource rate rewards C_star C_h u t) :
    q.val - start z.val < (originalWord rate rewards C_star C_h u t z).length := by
  rw [originalWord_length]
  have hd := firstCall_dates rate rewards C_star C_h u t z.val z.property.1.1
  have hq := q.isLt
  omega

def suffixInput (u t q : Fin p.T) (htq : t.val ≤ q.val)
    (z : StoppedSource rate rewards C_star C_h u t) : RecordedQueueRun.RoundInput p.K :=
  (originalWord rate rewards C_star C_h u t z)[q.val - start z.val]'(suffix_index_lt
    rate rewards C_star C_h u t q htq z)

/-- The actual original record, with a proved in-range index; no absent
record is replaced by a default. -/
def suffixRecord (u t q : Fin p.T) (htq : t.val ≤ q.val)
    (z : StoppedSource rate rewards C_star C_h u t) : Record rate :=
  (records z.val)[q.val - start z.val]'(by
    rw [← ReferenceActualCollectionHiddenRefreshPath.actualOriginalWord_length rate rewards C_star C_h
      z.val (firstCall_launch rate rewards C_star C_h u t z.val z.property.1.1)]
    exact suffix_index_lt rate rewards C_star C_h u t q htq z)

theorem suffixRecord_spec (u t q : Fin p.T) (htq : t.val ≤ q.val)
    (z : StoppedSource rate rewards C_star C_h u t) :
    actualRecord rate rewards C_star C_h q z.val = some (suffixRecord rate rewards C_star C_h u t q htq z) ∧
      (suffixRecord rate rewards C_star C_h u t q htq z).input.time = q ∧
      ReferenceFirstCollectionCurrentRetainedGate.cell0 rate
        (suffixRecord rate rewards C_star C_h u t q htq z) =
        some (suffixInput rate rewards C_star C_h u t q htq z) := by
  have hd := firstCall_dates rate rewards C_star C_h u t z.val z.property.1.1
  have hs : start z.val ≤ q.val := by omega
  have hr : (records z.val)[q.val - start z.val]? =
      some (suffixRecord rate rewards C_star C_h u t q htq z) :=
    List.getElem?_eq_getElem _
  refine ⟨?_, ?_, ?_⟩
  · rw [actualRecord, ite_eq_left hs, hr]
  · apply Fin.ext
    have ht := ReferenceFirstCollectionRenewalRecordingFeedback.complete_record_time rate z.val
      rewards C_star C_h _ _ hr
    omega
  · have hm := congrArg (fun L => L[q.val - start z.val]?)
      (originalWord_record_map rate rewards C_star C_h z.val
        (firstCall_launch rate rewards C_star C_h u t z.val z.property.1.1))
    change ((records z.val).map (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate))[q.val - start z.val]? =
      ((originalWord rate rewards C_star C_h u t z).map some)[q.val - start z.val]? at hm
    rw [List.getElem?_map, hr, Option.map_some, List.getElem?_map,
      List.getElem?_eq_getElem (suffix_index_lt rate rewards C_star C_h u t q htq z), Option.map_some] at hm
    exact Option.some.inj hm

def suffixBefore (u t q : Fin p.T) (z : StoppedSource rate rewards C_star C_h u t) :
    RecordedQueueRun.RunState p.K :=
  RecordedQueueRun.run Q ((originalWord rate rewards C_star C_h u t z).take (q.val - start z.val))

theorem suffixBefore_stopped (u t q : Fin p.T) (htq : t.val ≤ q.val)
    (z : StoppedSource rate rewards C_star C_h u t) :
    (suffixBefore rate rewards C_star C_h u t q z).overflow = true :=
  (originalWord_frozen_suffix rate rewards C_star C_h u t z q.castSucc htq).1

/-- Literal stopped cell on the actual original record and numerical input.
The accepted-record flag is retained separately from its integer amount. -/
def suffixCell (u t q : Fin p.T) (htq : t.val ≤ q.val)
    (z : StoppedSource rate rewards C_star C_h u t) : LogicalCell p rate :=
  let r := suffixRecord rate rewards C_star C_h u t q htq z
  let c := suffixInput rate rewards C_star C_h u t q htq z
  let S := suffixBefore rate rewards C_star C_h u t q z
  { time := q
    physical := ReferenceActiveHorizonMeasurability.roundRecordCode r
    numerical := ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates c
    before := S
    after := RecordedQueueRun.step Q S c
    arrivals := RecordedQueueRun.acceptedRecord Q S c
    service := fun j => RecordedQueueRun.recordService (4 * (Q).n) (S.registers j)
      (RecordedQueueRun.acceptedRecord Q S c j)
    slowSet := frozenSlowSet p
    fastArm := frozenFastArm p
    proposal := false
    nextSlowSet := frozenSlowSet p }

theorem suffixCell_after (u t q : Fin p.T) (htq : t.val ≤ q.val)
    (z : StoppedSource rate rewards C_star C_h u t) :
    (suffixCell rate rewards C_star C_h u t q htq z).after =
      RecordedQueueRun.run Q ((originalWord rate rewards C_star C_h u t z).take
        (q.val + 1 - start z.val)) := by
  have hd := firstCall_dates rate rewards C_star C_h u t z.val z.property.1.1
  change RecordedQueueRun.step Q (RecordedQueueRun.run Q
    ((originalWord rate rewards C_star C_h u t z).take (q.val - start z.val)))
    ((originalWord rate rewards C_star C_h u t z)[q.val - start z.val]'(suffix_index_lt
      rate rewards C_star C_h u t q htq z)) = _
  rw [← RecordedSlowRefresh.run_append_singleton,
    List.take_append_getElem (suffix_index_lt rate rewards C_star C_h u t q htq z)]
  congr 2
  omega

/-- Even after stop, numerical histories acquire a record at every date.
The logical actions are the prescribed bounded continuation. -/
theorem suffixCell_frozen (u t q : Fin p.T) (htq : t.val ≤ q.val)
    (z : StoppedSource rate rewards C_star C_h u t) :
    let e := suffixCell rate rewards C_star C_h u t q htq z
    e.slowSet = frozenSlowSet p ∧ e.fastArm = frozenFastArm p ∧
      e.proposal = false ∧ e.nextSlowSet = frozenSlowSet p ∧
      ∀ i, e.arrivals i = (false, 0) ∧ e.service i = 0 ∧
        e.after.registers i = e.before.registers i ∧
        e.after.records i = e.before.records i ++ [(false, 0)] := by
  dsimp only
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro i
  have hs := suffixBefore_stopped rate rewards C_star C_h u t q htq z
  have hh := RecordedQueueRun.step_after_overflow_preserves Q
    (suffixBefore rate rewards C_star C_h u t q z)
    (suffixInput rate rewards C_star C_h u t q htq z) hs i
  refine ⟨hh.2, ?_, hh.1, ?_⟩
  · change RecordedQueueRun.recordService _ _ _ = 0
    rw [hh.2]
    rfl
  · simp only [suffixCell, RecordedQueueRun.step, RecordedQueueRun.acceptedRecord, hs, ite_true]

private theorem input_eq_suffix (u t q : Fin p.T) (htq : t.val ≤ q.val)
    (z : StoppedSource rate rewards C_star C_h u t) (r : Record rate)
    (c : RecordedQueueRun.RoundInput p.K)
    (hr : actualRecord rate rewards C_star C_h q z.val = some r)
    (hc : ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r = some c) :
    r = suffixRecord rate rewards C_star C_h u t q htq z ∧
      c = suffixInput rate rewards C_star C_h u t q htq z := by
  have hd := suffixRecord_spec rate rewards C_star C_h u t q htq z
  have he : r = suffixRecord rate rewards C_star C_h u t q htq z :=
    Option.some.inj (hr.symm.trans hd.1)
  refine ⟨he, ?_⟩
  exact Option.some.inj (hc.symm.trans (he ▸ hd.2.2))

/-- On a stopped source every actual later invocation uses this same frozen
cell. Its refresh scalar is immaterial; no tape is relabelled. -/
theorem nativeCell_eq_suffixCell (control0 : TimeControl p) (u t q : Fin p.T)
    (htq : t.val ≤ q.val) (z : StoppedSource rate rewards C_star C_h u t)
    (hc : (ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h q z.val).isSome = true)
    (x : ContinuousControlSlice.Scalar) :
    ReferenceGeneratedInvocationCallSplice.nativeCell rate rewards C_star C_h control0 q ⟨z.val, hc⟩ x =
      suffixCell rate rewards C_star C_h u t q htq z := by
  let v : ReferenceGeneratedInvocationCallSplice.InvocationSource rate rewards C_star C_h q := ⟨z.val, hc⟩
  have hd := ReferenceGeneratedInvocationCallSplice.nativeSourceCell_spec rate rewards C_star C_h q v
  have hinput : ReferenceFirstCollectionCurrentRetainedGate.cell0 rate
      (ReferenceGeneratedInvocationCallSplice.nativeRecord rate rewards C_star C_h q v) =
      some (ReferenceGeneratedInvocationCallSplice.nativeSourceCell rate rewards C_star C_h q v).input := by
    rw [ReferenceFirstCollectionCurrentRetainedGate.cell0, hd.2.2, Option.some_or]
  have hi := input_eq_suffix rate rewards C_star C_h u t q htq z _ _ hd.1 hinput
  have hp := ReferencePostInvocationNoncallGeometry.prefixNumerical_actualWord rate rewards C_star C_h
    q.castSucc z.val (firstCall_launch rate rewards C_star C_h u t z.val z.property.1.1)
    (by
      change start z.val ≤ q.val
      have hh := firstCall_dates rate rewards C_star C_h u t z.val z.property.1.1
      omega)
  have hb := ReferenceGeneratedInvocationCallSplice.nativeBefore_prefix rate rewards C_star C_h control0 q v
  have hs : ReferenceGeneratedInvocationCallSplice.nativeBefore rate rewards C_star C_h control0 q v =
      suffixBefore rate rewards C_star C_h u t q z := Option.some.inj (hb.symm.trans hp)
  have hstop := suffixBefore_stopped rate rewards C_star C_h u t q htq z
  dsimp only [v] at hs hi
  unfold ReferenceGeneratedInvocationCallSplice.nativeCell appendLogicalCell suffixCell
  simp only [hs, hstop, Bool.not_true, Bool.false_and, ite_true, hi.1, hi.2,
    (suffixRecord_spec rate rewards C_star C_h u t q htq z).2.1]
  rfl

private theorem noncallCell_frozen (q : Fin p.T) (z : Source p) (a : Auxiliary p)
    (U : SlowSet p) (e : LogicalCell p rate)
    (he : ReferencePostInvocationNoncallGeometry.noncallDateCell rate rewards C_star C_h q z a U = some e)
    (hs : e.before.overflow = true) :
    e.slowSet = frozenSlowSet p ∧ e.fastArm = frozenFastArm p ∧
      e.proposal = false ∧ e.nextSlowSet = frozenSlowSet p := by
  unfold ReferencePostInvocationNoncallGeometry.noncallDateCell at he
  split at he
  next h =>
    have heq := Option.some.inj he
    subst e
    change (ReferencePostInvocationNoncallGeometry.continuingBefore rate rewards C_star C_h q ⟨z, h⟩).overflow = true at hs
    simp only [ReferencePostInvocationNoncallGeometry.continuingLogicalCell, appendLogicalCell,
      hs, Bool.not_true, Bool.false_and, ite_true, and_self]
  next _ =>
    split at he
    next h =>
      unfold ReferencePostInvocationNoncallGeometry.laterCollectionCell? at he
      split at he
      next _ =>
        have heq := Option.some.inj he
        subst e
        change (ReferencePostInvocationNoncallGeometry.collectionBefore rate rewards C_star C_h q ⟨z, h⟩).overflow = true at hs
        simp only [ReferencePostInvocationNoncallGeometry.laterCollectionCell, hs,
          Bool.not_true, Bool.and_false, Bool.false_and, ite_true, and_self]
      next _ => cases he
    next _ => cases he

theorem noncallCell_eq_suffixCell (u t q : Fin p.T) (htq : t.val ≤ q.val)
    (z : StoppedSource rate rewards C_star C_h u t) (a : Auxiliary p)
    (e : LogicalCell p rate)
    (he : ReferencePostInvocationNoncallGeometry.noncallDateCell
      rate rewards C_star C_h q z.val a (frozenSlowSet p) = some e) :
    e = suffixCell rate rewards C_star C_h u t q htq z := by
  have hd := ReferencePostInvocationNoncallGeometry.noncallDateCell_actualWord rate rewards C_star C_h q z.val
    (firstCall_launch rate rewards C_star C_h u t z.val z.property.1.1) a (frozenSlowSet p) e he
  obtain ⟨htime, hb, ha, r, c, hr, hc, _hen, hphysical, hnum, harr, hservice⟩ := hd
  have hi := input_eq_suffix rate rewards C_star C_h u t q htq z r c hr hc
  change e.before = suffixBefore rate rewards C_star C_h u t q z at hb
  have hf := noncallCell_frozen rate rewards C_star C_h q z.val a (frozenSlowSet p) e he
    (hb ▸ suffixBefore_stopped rate rewards C_star C_h u t q htq z)
  have hafter : e.after = (suffixCell rate rewards C_star C_h u t q htq z).after := by
    exact ha.trans (suffixCell_after rate rewards C_star C_h u t q htq z).symm
  apply logicalCellProductCode_injective
  simp only [logicalCellProductCode, Prod.mk.injEq]
  refine ⟨htime, ?_, ?_, hb, hafter, ?_, ?_, hf.1, hf.2.1, hf.2.2.1, hf.2.2.2⟩
  · exact hphysical.trans (congrArg ReferenceActiveHorizonMeasurability.roundRecordCode hi.1)
  · exact hnum.trans (congrArg ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates hi.2)
  · change e.arrivals = RecordedQueueRun.acceptedRecord Q _ _
    rw [harr, hb, hi.2]
  · change e.service = fun j => RecordedQueueRun.recordService (4 * (Q).n) _ _
    rw [hservice, harr, hb, hi.2]

/-- Canonical actual cell dispatch. Invocation dates use the native accepted
constructor; other dates use the accepted optional noncall constructor. -/
def nativeCellOption (control0 : TimeControl p) (q : Fin p.T)
    (v : ReferenceGeneratedInvocationCallSplice.InvocationSource rate rewards C_star C_h q ×
      ContinuousControlSlice.Scalar) : Option (LogicalCell p rate) :=
  some (ReferenceGeneratedInvocationCallSplice.nativeCell rate rewards C_star C_h control0 q v.1 v.2)

theorem measurable_nativeCellOption (control0 : TimeControl p) (q : Fin p.T) :
    Measurable (nativeCellOption rate rewards C_star C_h control0 q) :=
  LaterAssignmentFullOutputMeasurability.measurable_some_of_measurable _
    (ReferenceGeneratedInvocationCallSplice.measurable_nativeCell rate rewards C_star C_h control0 q)

def callPairSet (q : Fin p.T) : Set (Source p × Auxiliary p) :=
  {za | (ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h q za.1).isSome = true}

def callPairCell (control0 : TimeControl p) (q : Fin p.T)
    (za : ↥(callPairSet rate rewards C_star C_h q)) : Option (LogicalCell p rate) :=
  nativeCellOption rate rewards C_star C_h control0 q (⟨za.val.1, za.property⟩, za.val.2 (q, 1))

private theorem measurable_callPairCell (control0 : TimeControl p) (q : Fin p.T) :
    Measurable (callPairCell rate rewards C_star C_h control0 q) := by
  let E := callPairSet rate rewards C_star C_h q
  have hv : Measurable (fun za : E =>
      ((⟨za.val.1, za.property⟩ : ReferenceGeneratedInvocationCallSplice.InvocationSource
        rate rewards C_star C_h q), za.val.2 (q, 1))) :=
    (((measurable_fst.comp measurable_subtype_coe).subtype_mk).prodMk
      ((measurable_pi_apply (q, 1)).comp (measurable_snd.comp measurable_subtype_coe)))
  change Measurable (nativeCellOption rate rewards C_star C_h control0 q ∘
    (fun za : E => ((⟨za.val.1, za.property⟩ : ReferenceGeneratedInvocationCallSplice.InvocationSource
      rate rewards C_star C_h q), za.val.2 (q, 1))))
  exact (measurable_nativeCellOption rate rewards C_star C_h control0 q).comp hv

def calendarCell (control0 : TimeControl p) (q : Fin p.T) (za : Source p × Auxiliary p) :
    Option (LogicalCell p rate) :=
  if hc : za ∈ callPairSet rate rewards C_star C_h q then
    callPairCell rate rewards C_star C_h control0 q ⟨za, hc⟩
  else ReferencePostInvocationNoncallGeometry.noncallDateCell rate rewards C_star C_h q za.1 za.2
    (frozenSlowSet p)

private theorem measurable_option_isSome {A : Type*} [MeasurableSpace A] :
    Measurable (Option.isSome : Option A → Bool) := by
  have hm : Measurable (Sum.elim (fun _ : A => true) (fun _ : PUnit => false)) :=
    measurable_const.sumElim measurable_const
  convert hm.comp (comap_measurable (Equiv.optionEquivSumPUnit A)) using 1
  funext x
  cases x <;> rfl

private theorem measurableSet_callPairSet (control0 : TimeControl p) (q : Fin p.T) :
    MeasurableSet (callPairSet rate rewards C_star C_h q) := by
  have hcall := (ReferenceCalendarCollectionCallControlLaw.callAt_measurable rate rewards C_star C_h control0 q).mono
    ((sourcePrefixFiltration control0).le _) le_rfl
  exact (measurableSet_singleton true).preimage
    (measurable_option_isSome.comp (hcall.comp measurable_fst))

private theorem measurable_noncallFixed (control0 : TimeControl p) (q : Fin p.T) :
    Measurable (fun za : Source p × Auxiliary p =>
      ReferencePostInvocationNoncallGeometry.noncallDateCell rate rewards C_star C_h q za.1 za.2
        (frozenSlowSet p)) := by
  have harg : Measurable (fun za : Source p × Auxiliary p => ((frozenSlowSet p), za)) :=
    measurable_const.prodMk measurable_id
  have h := (ReferencePostInvocationPrefixLocality.measurable_noncallDateCell rate rewards C_star C_h control0 q).comp harg
  dsimp only [Function.comp_def] at h
  exact h

theorem measurable_calendarCell (control0 : TimeControl p) (q : Fin p.T) :
    Measurable (calendarCell rate rewards C_star C_h control0 q) := by
  unfold calendarCell
  exact (measurable_callPairCell rate rewards C_star C_h control0 q).dite
    ((measurable_noncallFixed rate rewards C_star C_h control0 q).comp measurable_subtype_coe)
    (measurableSet_callPairSet rate rewards C_star C_h control0 q)

/-- There is precisely one literal frozen cell on enabled dates and none on
disabled dates. Actual calls cannot be missing numerical lookups. -/
theorem calendarCell_eq_suffix (control0 : TimeControl p) (u t q : Fin p.T)
    (htq : t.val ≤ q.val) (z : StoppedSource rate rewards C_star C_h u t) (a : Auxiliary p) :
    calendarCell rate rewards C_star C_h control0 q (z.val, a) =
      if (suffixInput rate rewards C_star C_h u t q htq z).enabled then
        some (suffixCell rate rewards C_star C_h u t q htq z) else none := by
  unfold calendarCell callPairCell nativeCellOption
  split
  next hc =>
    let v : ReferenceGeneratedInvocationCallSplice.InvocationSource rate rewards C_star C_h q := ⟨z.val, hc⟩
    have hs := ReferenceGeneratedInvocationCallSplice.nativeSourceCell_spec rate rewards C_star C_h q v
    have hi := input_eq_suffix rate rewards C_star C_h u t q htq z _ _ hs.1 (by
      rw [ReferenceFirstCollectionCurrentRetainedGate.cell0, hs.2.2, Option.some_or])
    have hen : (suffixInput rate rewards C_star C_h u t q htq z).enabled = true := by
      rw [← hi.2]
      exact (ReferenceGeneratedInvocationCallSplice.nativeSourceCell rate rewards C_star C_h q v).enabled
    simp only [hen, ite_true]
    exact congrArg some (nativeCell_eq_suffixCell rate rewards C_star C_h control0 u t q htq z hc _)
  next hc =>
    have hnone : ReferenceFirstCollectionLogicalPrefixExtension.noCallAt rate rewards C_star C_h q z.val := by
      apply (ReferenceFirstCollectionLogicalPrefixExtension.noCallAt_iff_callAt_none rate rewards C_star C_h q z.val).mpr
      cases h : ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h q z.val with
      | none => rfl
      | some c => exact False.elim (hc (by
          change (ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h q z.val).isSome = true
          rw [h]
          rfl))
    have hdate : start z.val < q.val := by
      have hd := firstCall_dates rate rewards C_star C_h u t z.val z.property.1.1
      omega
    have hp := ReferencePostInvocationNoncallGeometry.noncallDateCell_presence rate rewards C_star C_h q z.val
      hdate hnone a (frozenSlowSet p)
    have hr := suffixRecord_spec rate rewards C_star C_h u t q htq z
    rw [hr.1, Option.bind_some, hr.2.2, Option.any_some] at hp
    cases he : ReferencePostInvocationNoncallGeometry.noncallDateCell rate rewards C_star C_h q z.val a
        (frozenSlowSet p) with
    | none =>
      rw [he, Option.isSome_none] at hp
      simp only [← hp, Bool.false_eq_true, ite_false]
    | some e =>
      rw [he, Option.isSome_some] at hp
      simp only [← hp, ite_true]
      exact congrArg some (noncallCell_eq_suffixCell rate rewards C_star C_h u t q htq z a e he)

/-- Append only an existing logical entry. -/
def appendOptional (L : List (LogicalCell p rate)) : Option (LogicalCell p rate) → List (LogicalCell p rate)
  | none => L
  | some e => L ++ [e]

theorem measurable_appendOptional : Measurable (fun v : List (LogicalCell p rate) × Option (LogicalCell p rate) =>
    appendOptional rate v.1 v.2) := by
  let tag : Option (LogicalCell p rate) → Unit ⊕ LogicalCell p rate :=
    fun o => (Equiv.optionEquivSumPUnit _ o).elim Sum.inr (fun _ => Sum.inl ())
  have ht : Measurable tag :=
    (measurable_inr.sumElim measurable_const).comp (comap_measurable (Equiv.optionEquivSumPUnit _))
  have hm := (ReferenceFirstLiveCalendarMarkedTransition.measurable_appendCurrentTag rate).comp
    (measurable_fst.prodMk (ht.comp measurable_snd))
  convert hm using 1
  funext v
  rcases v with ⟨L, o⟩
  cases o <;> rfl

/-- Start from the same accepted prefix; thereafter scan the actual physical
calendar without stopping physical play at an analytical overflow. -/
def calendarPastAux (control0 : TimeControl p) (t : Fin p.T) :
    (n : ℕ) → n ≤ p.T → Source p × Auxiliary p → List (LogicalCell p rate)
  | 0, _, _ => []
  | k + 1, hn, za =>
      if k < t.val then past ⟨k + 1, Nat.lt_succ_of_le hn⟩ za else
        appendOptional rate (calendarPastAux control0 t k (Nat.le_of_succ_le hn) za)
          (calendarCell rate rewards C_star C_h control0 ⟨k, Nat.lt_of_succ_le hn⟩ za)

theorem measurable_calendarPastAux (control0 : TimeControl p) (t : Fin p.T) :
    ∀ n (hn : n ≤ p.T), Measurable (calendarPastAux rate rewards C_star C_h control0 t n hn) := by
  intro n
  induction n with
  | zero => intro hn; exact measurable_const
  | succ k ih =>
    intro hn
    dsimp only [calendarPastAux]
    split
    · exact ReferenceFirstCollectionLogicalPrefixExtension.measurable_extendedPast rate rewards C_star C_h control0 _
    · exact (measurable_appendOptional rate).comp
        ((ih (Nat.le_of_succ_le hn)).prodMk
          (measurable_calendarCell rate rewards C_star C_h control0 _))

def initialStoppedPast (control0 : TimeControl p) (u t : Fin p.T) (n : Fin (p.T + 1))
    (za : StoppedSource rate rewards C_star C_h u t × Auxiliary p) : List (LogicalCell p rate) :=
  calendarPastAux rate rewards C_star C_h control0 t n.val (Nat.le_of_lt_succ n.isLt) (za.1.val, za.2)

theorem measurable_initialStoppedPast (control0 : TimeControl p) (u t : Fin p.T) (n : Fin (p.T + 1)) :
    Measurable (initialStoppedPast rate rewards C_star C_h control0 u t n) :=
  (measurable_calendarPastAux rate rewards C_star C_h control0 t n.val (Nat.le_of_lt_succ n.isLt)).comp
    ((measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd)

theorem calendarPastAux_before (control0 : TimeControl p) (t : Fin p.T) :
    ∀ n (hn : n ≤ p.T), n ≤ t.val → ∀ za,
      calendarPastAux rate rewards C_star C_h control0 t n hn za = past ⟨n, Nat.lt_succ_of_le hn⟩ za := by
  intro n
  cases n with
  | zero => intro hn hnt za; rfl
  | succ k =>
    intro hn hnt za
    rw [calendarPastAux, ite_eq_left (show k < t.val by omega)]

theorem initialStoppedPast_before (control0 : TimeControl p) (u t : Fin p.T) (n : Fin (p.T + 1))
    (hnt : n.val ≤ t.val) (za : StoppedSource rate rewards C_star C_h u t × Auxiliary p) :
    initialStoppedPast rate rewards C_star C_h control0 u t n za = past n (za.1.val, za.2) :=
  calendarPastAux_before rate rewards C_star C_h control0 t n.val (Nat.le_of_lt_succ n.isLt) hnt _

theorem initialStoppedPast_succ (control0 : TimeControl p) (u t q : Fin p.T) (htq : t.val ≤ q.val)
    (za : StoppedSource rate rewards C_star C_h u t × Auxiliary p) :
    initialStoppedPast rate rewards C_star C_h control0 u t q.succ za =
      initialStoppedPast rate rewards C_star C_h control0 u t q.castSucc za ++
        if (suffixInput rate rewards C_star C_h u t q htq za.1).enabled then
          [suffixCell rate rewards C_star C_h u t q htq za.1] else [] := by
  change calendarPastAux rate rewards C_star C_h control0 t (q.val + 1) _ _ = _
  rw [calendarPastAux, ite_eq_right (show ¬q.val < t.val by omega),
    calendarCell_eq_suffix rate rewards C_star C_h control0 u t q htq za.1 za.2]
  cases he : (suffixInput rate rewards C_star C_h u t q htq za.1).enabled <;>
    simp only [Bool.false_eq_true, ite_false, ite_true, appendOptional, List.append_nil] <;> rfl

/-- Original source restricted to the genuine measurable subtype, times the
whole original independent analytical array; no normalization. -/
def initialStoppedSourceLaw (u t : Fin p.T) :
    Measure (StoppedSource rate rewards C_star C_h u t × Auxiliary p) :=
  ((BootstrapPrivateRoundStreams.sourceInputLaw p).comap Subtype.val).prod
    (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p)

theorem initialStoppedSourceLaw_originalPair (u t : Fin p.T) :
    (initialStoppedSourceLaw rate rewards C_star C_h u t).map (fun za => (za.1.val, za.2)) =
      ((BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
        (initialStoppedEvent rate rewards C_star C_h u t)).prod
        (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p) := by
  change ((((BootstrapPrivateRoundStreams.sourceInputLaw p).comap
    (Subtype.val : StoppedSource rate rewards C_star C_h u t → Source p)).prod
    (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p))).map (Prod.map Subtype.val id) = _
  rw [← Measure.map_prod_map _ _ measurable_subtype_coe measurable_id, Measure.map_id,
    map_comap_subtype_coe (measurableSet_initialStoppedEvent rate rewards C_star C_h u t)]

abbrev Observer (rate : ReferenceActivePhysicalStep.RateInput p) :=
  Source p × (Auxiliary p × List (LogicalCell p rate))

/-- The root retains every auxiliary label, including labels not used in
the killed prefix. -/
def rootObservation (control0 : TimeControl p) (u t : Fin p.T)
    (za : StoppedSource rate rewards C_star C_h u t × Auxiliary p) : Observer rate :=
  (sourcePrefix control0 t.val za.1.val, (za.2, past t.castSucc (za.1.val, za.2)))

theorem measurable_rootObservation (control0 : TimeControl p) (u t : Fin p.T) :
    Measurable (rootObservation rate rewards C_star C_h control0 u t) :=
  ((measurable_sourcePrefix control0 t.val).comp (measurable_subtype_coe.comp measurable_fst)).prodMk
    (measurable_snd.prodMk
      ((ReferenceFirstCollectionLogicalPrefixExtension.measurable_extendedPast
        rate rewards C_star C_h control0 t.castSucc).comp
        ((measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd)))

def initialStoppedRootLaw (control0 : TimeControl p) (u t : Fin p.T) : Measure (Observer rate) :=
  (initialStoppedSourceLaw rate rewards C_star C_h u t).map
    (rootObservation rate rewards C_star C_h control0 u t)

def coarseProjection (w : Observer rate) : ReferenceFirstLiveCalendarMarkedTransition.Observation p rate :=
  (w.1, (ReferenceFirstLiveCalendarMarkedTransition.labelZero w.2.1, w.2.2))

theorem measurable_coarseProjection : Measurable (coarseProjection (p := p) rate) :=
  measurable_fst.prodMk (((ReferenceFirstLiveCalendarMarkedTransition.measurable_labelZero p).comp
    (measurable_fst.comp measurable_snd)).prodMk (measurable_snd.comp measurable_snd))

/-- The enriched original-tape root projects exactly to the marked killed
law. This does not assert fresh controls at dates earlier than `t`. -/
theorem initialStoppedRootLaw_coarse (control0 : TimeControl p) (u t : Fin p.T) :
    (initialStoppedRootLaw rate rewards C_star C_h control0 u t).map (coarseProjection rate) =
      (ReferenceFirstCollectionLogicalPrefixExtension.betaPre rate rewards C_star C_h control0 t.castSucc).restrict
        {w | w.1 ∈ initialStoppedEvent rate rewards C_star C_h u t} := by
  let B := initialStoppedEvent rate rewards C_star C_h u t
  let f := ReferenceFirstCollectionLogicalPrefixExtension.extendedObservation rate rewards C_star C_h control0 t.castSucc
  have hf : Measurable f := ReferenceFirstCollectionLogicalPrefixExtension.measurable_extendedObservation
    rate rewards C_star C_h control0 t.castSucc
  have hforget : Measurable (fun za : StoppedSource rate rewards C_star C_h u t × Auxiliary p =>
      (za.1.val, za.2)) := (measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd
  have hB : MeasurableSet B := measurableSet_initialStoppedEvent rate rewards C_star C_h u t
  have hmark : MeasurableSet {w : ReferenceFirstLiveCalendarMarkedTransition.Observation p rate | w.1 ∈ B} :=
    hB.preimage measurable_fst
  rw [initialStoppedRootLaw, Measure.map_map (measurable_coarseProjection rate)
    (measurable_rootObservation rate rewards C_star C_h control0 u t)]
  change (initialStoppedSourceLaw rate rewards C_star C_h u t).map (f ∘ (fun za => (za.1.val, za.2))) = _
  rw [← Measure.map_map hf hforget, initialStoppedSourceLaw_originalPair,
    Measure.restrict_prod_eq_prod_univ]
  rw [← ReferenceFirstCollectionLogicalPrefixExtension.extendedObservation_map_restrict_eq_betaPre
    rate rewards C_star C_h control0 t.castSucc, Measure.restrict_map hf hmark]
  rw [Measure.restrict_restrict (hf hmark)]
  congr 2
  ext za
  change (za.1 ∈ B ∧ za.2 ∈ Set.univ) ↔
    sourcePrefix control0 t.val za.1 ∈ B ∧
      ReferenceFirstCollectionLogicalPrefixExtension.NoCallBefore rate rewards C_star C_h t.castSucc za.1
  rw [← initialStoppedEvent_sourcePrefix rate rewards C_star C_h control0 u t t.val le_rfl]
  exact ⟨fun h => ⟨h.1, initialStoppedEvent_noCallBefore rate rewards C_star C_h u t za.1 h.1⟩,
    fun h => ⟨h.1, Set.mem_univ _⟩⟩

def prefixSource (control0 : TimeControl p) (u t : Fin p.T) (m : ℕ) (htm : t.val ≤ m)
    (z : StoppedSource rate rewards C_star C_h u t) : StoppedSource rate rewards C_star C_h u t :=
  ⟨sourcePrefix control0 m z.val,
    (initialStoppedEvent_sourcePrefix rate rewards C_star C_h control0 u t m htm z.val).mp z.property⟩

private theorem numerical_injective : Function.Injective
    (ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates (p := p)) := by
  intro a b h
  cases a
  cases b
  simpa only [ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates,
    Prod.mk.injEq, RecordedQueueRun.RoundInput.mk.injEq] using h

private theorem flatten_branch (r : Record rate) :
    (ReferenceCompleteNumericalBranchObservation.leftProjection
      (ReferenceCompleteNumericalBranchObservation.branchReadout rate 0 r)).or
      (ReferenceCompleteNumericalBranchObservation.rightProjection
        (ReferenceCompleteNumericalBranchObservation.branchReadout rate 0 r)) =
      (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r).map
        ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates := by
  have h := ReferenceCompleteNumericalBranchObservation.branch_readout_projections rate 0 r
  have hl := congrArg Prod.fst h
  have hr := congrArg Prod.snd h
  dsimp only at hl hr
  rw [hl, hr,
    ReferenceFirstCollectionCurrentRetainedGate.cell0, Option.map_or]
  rfl

/-- The entire literal suffix cell ignores selected controls at and after
any later boundary. This includes both its continuous numerical vectors. -/
theorem suffixCell_sourcePrefix (control0 : TimeControl p) (u t q : Fin p.T)
    (htq : t.val ≤ q.val) (m : ℕ) (hm : m ≤ p.T) (hqm : q.val < m)
    (z : StoppedSource rate rewards C_star C_h u t) :
    let z' := prefixSource rate rewards C_star C_h control0 u t m (by omega) z
    suffixInput rate rewards C_star C_h u t q htq z = suffixInput rate rewards C_star C_h u t q htq z' ∧
      suffixCell rate rewards C_star C_h u t q htq z = suffixCell rate rewards C_star C_h u t q htq z' := by
  dsimp only
  let z' := prefixSource rate rewards C_star C_h control0 u t m (by omega) z
  have hr := suffixRecord_spec rate rewards C_star C_h u t q htq z
  have hr' := suffixRecord_spec rate rewards C_star C_h u t q htq z'
  have ho := ReferencePostInvocationPrefixLocality.actualObservation_sourcePrefix
    rate rewards C_star C_h control0 m hm q hqm z.val
  change _ = (actualRecord rate rewards C_star C_h q z'.val).map _ at ho
  rw [hr.1, hr'.1, Option.map_some, Option.map_some] at ho
  have he := Option.some.inj ho
  have hphysical := congrArg (fun v => v.2.1) he
  dsimp only at hphysical
  have hn := congrArg (fun v =>
    (ReferenceCompleteNumericalBranchObservation.leftProjection v.2.2).or
      (ReferenceCompleteNumericalBranchObservation.rightProjection v.2.2)) he
  rw [flatten_branch, flatten_branch, hr.2.2, hr'.2.2, Option.map_some, Option.map_some] at hn
  have hi := numerical_injective (Option.some.inj hn)
  have hp := ReferencePostInvocationPrefixLocality.prefixNumerical_sourcePrefix rate rewards C_star C_h
    control0 q.castSucc m (by simpa only [Fin.val_castSucc] using hqm.le) z.val
  have hpw (w : StoppedSource rate rewards C_star C_h u t) :
      ReferencePostInvocationNoncallGeometry.prefixNumerical rate rewards C_star C_h q.castSucc w.val =
        some (suffixBefore rate rewards C_star C_h u t q w) :=
    ReferencePostInvocationNoncallGeometry.prefixNumerical_actualWord rate rewards C_star C_h q.castSucc w.val
      (firstCall_launch rate rewards C_star C_h u t w.val w.property.1.1)
      (by
        change start w.val ≤ q.val
        have hd := firstCall_dates rate rewards C_star C_h u t w.val w.property.1.1
        omega)
  change _ = ReferencePostInvocationNoncallGeometry.prefixNumerical rate rewards C_star C_h q.castSucc z'.val at hp
  rw [hpw z, hpw z'] at hp
  have hb := Option.some.inj hp
  refine ⟨hi, ?_⟩
  change suffixCell rate rewards C_star C_h u t q htq z = suffixCell rate rewards C_star C_h u t q htq z'
  simp only [suffixCell]
  rw [hphysical, hi, hb]

theorem calendarCell_sourcePrefix (control0 : TimeControl p) (u t q : Fin p.T)
    (htq : t.val ≤ q.val) (m : ℕ) (hm : m ≤ p.T) (hqm : q.val < m)
    (z : StoppedSource rate rewards C_star C_h u t) (a : Auxiliary p) :
    calendarCell rate rewards C_star C_h control0 q (z.val, a) =
      calendarCell rate rewards C_star C_h control0 q (sourcePrefix control0 m z.val, a) := by
  let z' := prefixSource rate rewards C_star C_h control0 u t m (by omega) z
  have h := suffixCell_sourcePrefix rate rewards C_star C_h control0 u t q htq m hm hqm z
  change calendarCell rate rewards C_star C_h control0 q (z.val, a) =
    calendarCell rate rewards C_star C_h control0 q (z'.val, a)
  change suffixInput rate rewards C_star C_h u t q htq z = suffixInput rate rewards C_star C_h u t q htq z' ∧
    suffixCell rate rewards C_star C_h u t q htq z = suffixCell rate rewards C_star C_h u t q htq z' at h
  rw [calendarCell_eq_suffix rate rewards C_star C_h control0 u t q htq z a,
    calendarCell_eq_suffix rate rewards C_star C_h control0 u t q htq z' a, h.1, h.2]

theorem calendarPastAux_sourcePrefix (control0 : TimeControl p) (u t : Fin p.T)
    (m : ℕ) (hm : m ≤ p.T) (_htm : t.val ≤ m)
    (z : StoppedSource rate rewards C_star C_h u t) (a : Auxiliary p) :
    ∀ n (hn : n ≤ p.T), n ≤ m →
      calendarPastAux rate rewards C_star C_h control0 t n hn (z.val, a) =
        calendarPastAux rate rewards C_star C_h control0 t n hn (sourcePrefix control0 m z.val, a) := by
  intro n
  induction n with
  | zero => intro hn hnm; rfl
  | succ k ih =>
    intro hn hnm
    rw [calendarPastAux, calendarPastAux]
    split
    · have hp (w : Source p) := ReferenceFirstCollectionLogicalPrefixExtension.extendedPrefixStateAux_sourcePrefix
        rate rewards C_star C_h control0 (k + 1) hn w a
      have hp' := hp (sourcePrefix control0 m z.val)
      rw [sourcePrefix_sourcePrefix control0 (k + 1) m hnm] at hp'
      exact congrArg Prod.snd ((hp z.val).trans hp'.symm)
    · rw [ih (Nat.le_of_succ_le hn) (by omega),
        calendarCell_sourcePrefix rate rewards C_star C_h control0 u t ⟨k, Nat.lt_of_succ_le hn⟩
          (by simpa using Nat.le_of_not_gt ‹¬k < t.val›) m hm (by change k < m; omega) z a]

/-- Future current controls retain their full original law under this PRE
restriction. No independence from an unmasked complete source is asserted. -/
theorem initialStopped_currentControl_product (control0 : TimeControl p) (u t q : Fin p.T)
    (htq : t.val ≤ q.val) :
    ((BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
      (initialStoppedEvent rate rewards C_star C_h u t)).map
        (fun z => (sourcePrefix control0 q.val z, ReferenceSourceCurrentControlFreshness.u_t p q z)) =
      (((BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
        (initialStoppedEvent rate rewards C_star C_h u t)).map (sourcePrefix control0 q.val)).prod
          (ContinuousLearningRows.timeControlLaw p) := by
  let μ := BootstrapPrivateRoundStreams.sourceInputLaw p
  let B := initialStoppedEvent rate rewards C_star C_h u t
  let f := fun z : Source p => (sourcePrefix control0 q.val z, ReferenceSourceCurrentControlFreshness.u_t p q z)
  have hp := measurable_sourcePrefix control0 q.val
  have hf : Measurable f := hp.prodMk (ReferenceSourceCurrentControlFreshness.measurable_u_t q)
  have hB := measurableSet_initialStoppedEvent rate rewards C_star C_h u t
  have hpre : (sourcePrefix control0 q.val) ⁻¹' B = B := by
    ext z
    exact (initialStoppedEvent_sourcePrefix rate rewards C_star C_h control0 u t q.val htq z).symm
  have hpre' : f ⁻¹' (B ×ˢ Set.univ) = B := by
    ext z
    change (sourcePrefix control0 q.val z ∈ B ∧ True) ↔ z ∈ B
    rw [and_true]
    exact (initialStoppedEvent_sourcePrefix rate rewards C_star C_h control0 u t q.val htq z).symm
  calc
    (μ.restrict B).map f = (μ.map f).restrict (B ×ˢ Set.univ) := by
      rw [Measure.restrict_map hf (hB.prod MeasurableSet.univ), hpre']
    _ = ((μ.map (sourcePrefix control0 q.val)).prod (ContinuousLearningRows.timeControlLaw p)).restrict
        (B ×ˢ Set.univ) := by
      rw [ReferenceFirstLiveCalendarMarkedTransition.sourcePrefix_currentControl_product]
    _ = ((μ.map (sourcePrefix control0 q.val)).restrict B).prod (ContinuousLearningRows.timeControlLaw p) :=
      (Measure.restrict_prod_eq_prod_univ B).symm
    _ = ((μ.restrict B).map (sourcePrefix control0 q.val)).prod (ContinuousLearningRows.timeControlLaw p) := by
      rw [Measure.restrict_map hp hB, hpre]

/-- Archive the requested boundary list while the full physical source is
chronologically restored through the horizon. The complete tape is retained. -/
def boundaryObserverRaw (control0 : TimeControl p) (t : Fin p.T) (n q : Fin (p.T + 1))
    (za : Source p × Auxiliary p) : Observer rate :=
  (sourcePrefix control0 q.val za.1, (za.2,
    calendarPastAux rate rewards C_star C_h control0 t (min n.val q.val)
      ((Nat.min_le_left _ _).trans (Nat.le_of_lt_succ n.isLt)) za))

theorem measurable_boundaryObserverRaw (control0 : TimeControl p) (t : Fin p.T) (n q : Fin (p.T + 1)) :
    Measurable (boundaryObserverRaw rate rewards C_star C_h control0 t n q) :=
  ((measurable_sourcePrefix control0 q.val).comp measurable_fst).prodMk
    (measurable_snd.prodMk (measurable_calendarPastAux rate rewards C_star C_h control0 t _ _))

def boundaryObserver (control0 : TimeControl p) (u t : Fin p.T) (n q : Fin (p.T + 1))
    (za : StoppedSource rate rewards C_star C_h u t × Auxiliary p) : Observer rate :=
  boundaryObserverRaw rate rewards C_star C_h control0 t n q (za.1.val, za.2)

theorem measurable_boundaryObserver (control0 : TimeControl p) (u t : Fin p.T) (n q : Fin (p.T + 1)) :
    Measurable (boundaryObserver rate rewards C_star C_h control0 u t n q) :=
  (measurable_boundaryObserverRaw rate rewards C_star C_h control0 t n q).comp
    ((measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd)

theorem boundaryObserver_factor (control0 : TimeControl p) (u t : Fin p.T) (n q : Fin (p.T + 1))
    (htq : t.val ≤ q.val) (za : StoppedSource rate rewards C_star C_h u t × Auxiliary p) :
    boundaryObserverRaw rate rewards C_star C_h control0 t n q (sourcePrefix control0 q.val za.1.val, za.2) =
      boundaryObserver rate rewards C_star C_h control0 u t n q za := by
  dsimp only [boundaryObserverRaw, boundaryObserver]
  apply Prod.ext
  · exact sourcePrefix_sourcePrefix control0 q.val q.val le_rfl za.1.val
  · apply Prod.ext
    · rfl
    · exact (calendarPastAux_sourcePrefix rate rewards C_star C_h control0 u t q.val
        (Nat.le_of_lt_succ q.isLt) htq za.1 za.2 _ _ (Nat.min_le_right _ _)).symm

private theorem reorder_product {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    (a : Measure A) (b : Measure B) (c : Measure C) [SFinite a] [SFinite b] [SFinite c] :
    MeasurePreserving (fun v : (A × B) × C => ((v.1.1, v.2), v.1.2))
      ((a.prod b).prod c) ((a.prod c).prod b) := by
  exact (measurePreserving_prodAssoc a c b).symm.comp
    (((MeasurePreserving.id a).prod (Measure.measurePreserving_swap (μ := b) (ν := c))).comp
      (measurePreserving_prodAssoc a b c))

/-- Current-control factorization jointly retains every original auxiliary
coordinate and the complete archived logical history. -/
theorem boundaryObserver_current_product (control0 : TimeControl p) (u t q : Fin p.T)
    (htq : t.val ≤ q.val) (n : Fin (p.T + 1)) :
    (initialStoppedSourceLaw rate rewards C_star C_h u t).map (fun za =>
      (boundaryObserver rate rewards C_star C_h control0 u t n q.castSucc za,
        ReferenceSourceCurrentControlFreshness.u_t p q za.1.val)) =
      ((initialStoppedSourceLaw rate rewards C_star C_h u t).map
        (boundaryObserver rate rewards C_star C_h control0 u t n q.castSucc)).prod
          (ContinuousLearningRows.timeControlLaw p) := by
  let B := initialStoppedEvent rate rewards C_star C_h u t
  let μ := BootstrapPrivateRoundStreams.sourceInputLaw p
  let μb := μ.restrict B
  let μc := μb.map (sourcePrefix control0 q.val)
  let α := ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p
  let γ := ContinuousLearningRows.timeControlLaw p
  let f := fun z : Source p => (sourcePrefix control0 q.val z, ReferenceSourceCurrentControlFreshness.u_t p q z)
  have hf : Measurable f := (measurable_sourcePrefix control0 q.val).prodMk
    (ReferenceSourceCurrentControlFreshness.measurable_u_t q)
  have hs : MeasurePreserving (fun z : StoppedSource rate rewards C_star C_h u t => f z.val)
      (μ.comap Subtype.val) (μc.prod γ) := by
    refine ⟨hf.comp measurable_subtype_coe, ?_⟩
    change (μ.comap (Subtype.val : StoppedSource rate rewards C_star C_h u t → Source p)).map
      (f ∘ Subtype.val) = μc.prod γ
    rw [← Measure.map_map hf measurable_subtype_coe, map_comap_subtype_coe
      (measurableSet_initialStoppedEvent rate rewards C_star C_h u t)]
    exact initialStopped_currentControl_product rate rewards C_star C_h control0 u t q htq
  let g := boundaryObserverRaw rate rewards C_star C_h control0 t n q.castSucc
  have hg : Measurable g := measurable_boundaryObserverRaw rate rewards C_star C_h control0 t n q.castSucc
  have ho : MeasurePreserving g (μc.prod α) ((μc.prod α).map g) := ⟨hg, rfl⟩
  have hfull := (ho.prod (MeasurePreserving.id γ)).comp
    ((reorder_product μc γ α).comp (hs.prod (MeasurePreserving.id α)))
  have hjoint : (initialStoppedSourceLaw rate rewards C_star C_h u t).map (fun za =>
      (boundaryObserver rate rewards C_star C_h control0 u t n q.castSucc za,
        ReferenceSourceCurrentControlFreshness.u_t p q za.1.val)) = ((μc.prod α).map g).prod γ := by
    convert hfull.map_eq using 1
    congr 1
    funext za
    exact Prod.ext (boundaryObserver_factor rate rewards C_star C_h control0 u t n q.castSucc htq za).symm rfl
  have hm := congrArg Measure.fst hjoint
  have hu : Measurable (fun za : StoppedSource rate rewards C_star C_h u t × Auxiliary p =>
      ReferenceSourceCurrentControlFreshness.u_t p q za.1.val) :=
    (ReferenceSourceCurrentControlFreshness.measurable_u_t q).comp
      (measurable_subtype_coe.comp measurable_fst)
  rw [Measure.fst_map_prodMk (measurable_boundaryObserver rate rewards C_star C_h control0 u t n q.castSucc)
    hu, Measure.fst_prod] at hm
  rw [hm]
  exact hjoint

/-- Restore the complete current physical control, append the actual frozen
cell up to the archived boundary, and keep the whole analytical tape. -/
def stoppedSample (control0 : TimeControl p) (n : Fin (p.T + 1)) (q : Fin p.T)
    (v : Observer rate × TimeControl p) : Observer rate :=
  let z := ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p q v.1.1 v.2
  (z, (v.1.2.1, if q.val < n.val then
    appendOptional rate v.1.2.2 (calendarCell rate rewards C_star C_h control0 q (z, v.1.2.1)) else v.1.2.2))

theorem measurable_stoppedSample (control0 : TimeControl p) (n : Fin (p.T + 1)) (q : Fin p.T) :
    Measurable (stoppedSample rate rewards C_star C_h control0 n q) := by
  have hz : Measurable (fun v : Observer rate × TimeControl p =>
      ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p q v.1.1 v.2) :=
    (ReferenceSourcePhysicalFlagConditionalLaw.measurable_replaceSourceControl p q).comp
    ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have ha : Measurable (fun v : Observer rate × TimeControl p => v.1.2.1) :=
    measurable_fst.comp (measurable_snd.comp measurable_fst)
  have hL : Measurable (fun v : Observer rate × TimeControl p => v.1.2.2) :=
    measurable_snd.comp (measurable_snd.comp measurable_fst)
  have happ : Measurable (fun v : Observer rate × TimeControl p =>
      appendOptional rate v.1.2.2 (calendarCell rate rewards C_star C_h control0 q
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p q v.1.1 v.2, v.1.2.1))) :=
    (measurable_appendOptional rate).comp
    (hL.prodMk ((measurable_calendarCell rate rewards C_star C_h control0 q).comp (hz.prodMk ha)))
  have hlist : Measurable (fun v : Observer rate × TimeControl p => if q.val < n.val then
      appendOptional rate v.1.2.2 (calendarCell rate rewards C_star C_h control0 q
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p q v.1.1 v.2, v.1.2.1)) else v.1.2.2) := by
    by_cases h : q.val < n.val <;> simp only [h, ite_true, ite_false] <;> assumption
  exact hz.prodMk (ha.prodMk hlist)

theorem stoppedSample_actual (control0 : TimeControl p) (u t q : Fin p.T) (htq : t.val ≤ q.val)
    (n : Fin (p.T + 1)) (za : StoppedSource rate rewards C_star C_h u t × Auxiliary p) :
    stoppedSample rate rewards C_star C_h control0 n q
      (boundaryObserver rate rewards C_star C_h control0 u t n q.castSucc za,
        ReferenceSourceCurrentControlFreshness.u_t p q za.1.val) =
      boundaryObserver rate rewards C_star C_h control0 u t n q.succ za := by
  dsimp only [stoppedSample, boundaryObserver, boundaryObserverRaw, Fin.val_castSucc, Fin.val_succ]
  have hsource := prefix_successor_restore control0 q za.1.val
  change sourcePrefix control0 (q.val + 1) za.1.val =
    ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p q (sourcePrefix control0 q.val za.1.val)
      (ReferenceSourceCurrentControlFreshness.u_t p q za.1.val) at hsource
  rw [← hsource]
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · rfl
    · by_cases hqn : q.val < n.val
      · simp only [hqn, ite_true, Nat.min_eq_right hqn.le,
          Nat.min_eq_right (Nat.succ_le_of_lt hqn)]
        rw [calendarPastAux, ite_eq_right (show ¬q.val < t.val by omega)]
        rw [calendarCell_sourcePrefix rate rewards C_star C_h control0 u t q htq (q.val + 1)
          (Nat.succ_le_of_lt q.isLt) (Nat.lt_succ_self _) za.1 za.2]
      · have hnq : n.val ≤ q.val := Nat.le_of_not_gt hqn
        simp only [hqn, ite_false, Nat.min_eq_left hnq, Nat.min_eq_left (hnq.trans (Nat.le_succ _))]

def stoppedKernel (control0 : TimeControl p) (n : Fin (p.T + 1)) (q : Fin p.T) :
    ProbabilityTheory.Kernel (Observer rate) (Observer rate) :=
  ProbabilityTheory.Kernel.mapOfMeasurable
    (ProbabilityTheory.Kernel.prod ProbabilityTheory.Kernel.id
      (ProbabilityTheory.Kernel.const (Observer rate) (ContinuousLearningRows.timeControlLaw p)))
    (stoppedSample rate rewards C_star C_h control0 n q)
    (measurable_stoppedSample rate rewards C_star C_h control0 n q)

theorem stoppedKernel_apply (control0 : TimeControl p) (n : Fin (p.T + 1)) (q : Fin p.T) (w : Observer rate) :
    stoppedKernel rate rewards C_star C_h control0 n q w = (ContinuousLearningRows.timeControlLaw p).map
      (fun c => stoppedSample rate rewards C_star C_h control0 n q (w, c)) := by
  change ((ProbabilityTheory.Kernel.prod ProbabilityTheory.Kernel.id
    (ProbabilityTheory.Kernel.const (Observer rate) (ContinuousLearningRows.timeControlLaw p))) w).map _ = _
  rw [ProbabilityTheory.Kernel.prod_apply, ProbabilityTheory.Kernel.id_apply,
    ProbabilityTheory.Kernel.const_apply, Measure.dirac_prod,
    Measure.map_map (measurable_stoppedSample rate rewards C_star C_h control0 n q) measurable_prodMk_left]
  rfl

/-- Finite chronological kernel recursion rooted at the same marked killed
prefix; after the archived boundary only physical coordinates are filled. -/
def chronologicalLawAux (control0 : TimeControl p) (u t : Fin p.T) (n : Fin (p.T + 1)) :
    (j : ℕ) → t.val + j ≤ p.T → Measure (Observer rate)
  | 0, _ => initialStoppedRootLaw rate rewards C_star C_h control0 u t
  | j + 1, hj =>
      (chronologicalLawAux control0 u t n j (by omega)).bind
        (stoppedKernel rate rewards C_star C_h control0 n ⟨t.val + j, by omega⟩)

def initialStoppedChronologicalLaw (control0 : TimeControl p) (u t : Fin p.T) (n : Fin (p.T + 1)) :
    Measure (Observer rate) :=
  chronologicalLawAux rate rewards C_star C_h control0 u t n (p.T - t.val) (by omega)

theorem chronologicalLawAux_actual (control0 : TimeControl p) (u t : Fin p.T) (n : Fin (p.T + 1))
    (htn : t.val ≤ n.val) : ∀ j (hj : t.val + j ≤ p.T),
    chronologicalLawAux rate rewards C_star C_h control0 u t n j hj =
      (initialStoppedSourceLaw rate rewards C_star C_h u t).map
        (boundaryObserver rate rewards C_star C_h control0 u t n ⟨t.val + j, Nat.lt_succ_of_le hj⟩) := by
  intro j
  induction j with
  | zero =>
    intro hj
    unfold chronologicalLawAux initialStoppedRootLaw
    congr 1
    funext za
    dsimp only [rootObservation, boundaryObserver, boundaryObserverRaw, Nat.add_zero]
    simp only [Nat.min_eq_right htn]
    rw [calendarPastAux_before rate rewards C_star C_h control0 t t.val (Nat.le_of_lt t.isLt) le_rfl]
    rfl
  | succ j ih =>
    intro hj
    let q : Fin p.T := ⟨t.val + j, by omega⟩
    let μ := initialStoppedSourceLaw rate rewards C_star C_h u t
    let obs := boundaryObserver rate rewards C_star C_h control0 u t n q.castSucc
    let next := boundaryObserver rate rewards C_star C_h control0 u t n q.succ
    let F := stoppedSample rate rewards C_star C_h control0 n q
    have hobs : Measurable obs := measurable_boundaryObserver rate rewards C_star C_h control0 u t n q.castSucc
    have hnext : Measurable next := measurable_boundaryObserver rate rewards C_star C_h control0 u t n q.succ
    have hF : Measurable F := measurable_stoppedSample rate rewards C_star C_h control0 n q
    have hprod := boundaryObserver_current_product rate rewards C_star C_h control0 u t q (by dsimp only [q]; omega) n
    apply Measure.ext_of_lintegral
    intro Phi hPhi
    change (∫⁻ w, Phi w ∂(chronologicalLawAux rate rewards C_star C_h control0 u t n j _).bind
      (stoppedKernel rate rewards C_star C_h control0 n q)) = ∫⁻ w, Phi w ∂μ.map next
    rw [ih, Measure.lintegral_bind (ProbabilityTheory.Kernel.aemeasurable _) hPhi.aemeasurable,
      lintegral_map hPhi hnext]
    calc
      (∫⁻ w, ∫⁻ y, Phi y ∂stoppedKernel rate rewards C_star C_h control0 n q w ∂μ.map obs) =
          ∫⁻ v, Phi (F v) ∂(μ.map obs).prod (ContinuousLearningRows.timeControlLaw p) := by
        rw [lintegral_prod (fun v => Phi (F v)) (hPhi.comp hF).aemeasurable]
        apply lintegral_congr
        intro w
        rw [stoppedKernel_apply]
        exact lintegral_map hPhi (hF.comp measurable_prodMk_left)
      _ = ∫⁻ za, Phi (F (obs za, ReferenceSourceCurrentControlFreshness.u_t p q za.1.val)) ∂μ := by
        rw [← hprod]
        exact lintegral_map (hPhi.comp hF) (hobs.prodMk
          ((ReferenceSourceCurrentControlFreshness.measurable_u_t q).comp
            (measurable_subtype_coe.comp measurable_fst)))
      _ = ∫⁻ za, Phi (next za) ∂μ := by
        apply lintegral_congr
        intro za
        exact congrArg Phi (stoppedSample_actual rate rewards C_star C_h control0 u t q
          (by dsimp only [q]; omega) n za)

/-- Genuine full-source/original-tape joint law. Every remaining physical
control is filled by its original law before the complete source is exposed. -/
theorem initialStopped_fullSource_jointLaw (control0 : TimeControl p) (u t : Fin p.T)
    (n : Fin (p.T + 1)) (htn : t.val ≤ n.val) :
    (initialStoppedSourceLaw rate rewards C_star C_h u t).map (fun za =>
      (za.1.val, (za.2, initialStoppedPast rate rewards C_star C_h control0 u t n za))) =
      initialStoppedChronologicalLaw rate rewards C_star C_h control0 u t n := by
  rw [initialStoppedChronologicalLaw, chronologicalLawAux_actual rate rewards C_star C_h control0 u t n htn]
  congr 1
  funext za
  have ht := t.isLt
  have hsum : t.val + (p.T - t.val) = p.T := by omega
  simp only [boundaryObserver, boundaryObserverRaw, hsum,
    sourcePrefix_eq_self control0 p.T le_rfl, Nat.min_eq_left (Nat.le_of_lt_succ n.isLt)]
  rfl

theorem initialStopped_fullSource_test (control0 : TimeControl p) (u t : Fin p.T)
    (n : Fin (p.T + 1)) (htn : t.val ≤ n.val) (Phi : Observer rate → ℝ≥0∞) (hPhi : Measurable Phi) :
    (∫⁻ za, Phi (za.1.val, (za.2, initialStoppedPast rate rewards C_star C_h control0 u t n za))
      ∂initialStoppedSourceLaw rate rewards C_star C_h u t) =
      ∫⁻ w, Phi w ∂initialStoppedChronologicalLaw rate rewards C_star C_h control0 u t n := by
  rw [← initialStopped_fullSource_jointLaw rate rewards C_star C_h control0 u t n htn]
  exact (lintegral_map hPhi ((measurable_subtype_coe.comp measurable_fst).prodMk
    (measurable_snd.prodMk (measurable_initialStoppedPast rate rewards C_star C_h control0 u t n)))).symm

/-- The unchanged-source restricted marginal is a projection of the joint
chronological law, retaining all private arrays, rows, and continuous vectors. -/
theorem initialStoppedChronologicalLaw_source (control0 : TimeControl p) (u t : Fin p.T)
    (n : Fin (p.T + 1)) (htn : t.val ≤ n.val) :
    (initialStoppedChronologicalLaw rate rewards C_star C_h control0 u t n).map Prod.fst =
      (BootstrapPrivateRoundStreams.sourceInputLaw p).restrict (initialStoppedEvent rate rewards C_star C_h u t) := by
  have hfull : Measurable (fun za : StoppedSource rate rewards C_star C_h u t × Auxiliary p =>
      (za.1.val, (za.2, initialStoppedPast rate rewards C_star C_h control0 u t n za))) :=
    (measurable_subtype_coe.comp measurable_fst).prodMk
      (measurable_snd.prodMk (measurable_initialStoppedPast rate rewards C_star C_h control0 u t n))
  rw [← initialStopped_fullSource_jointLaw rate rewards C_star C_h control0 u t n htn,
    Measure.map_map measurable_fst hfull]
  have h := congrArg Measure.fst (initialStoppedSourceLaw_originalPair rate rewards C_star C_h u t)
  have hc : Measurable (fun za : StoppedSource rate rewards C_star C_h u t × Auxiliary p => za.1.val) :=
    measurable_subtype_coe.comp measurable_fst
  rw [Measure.fst_map_prodMk hc measurable_snd, Measure.fst_prod] at h
  exact h

/-- The exact existing grid-to-real convention for auxiliary reward. -/
def cellReward (e : LogicalCell p rate) : ℝ :=
  (∑ i ∈ e.slowSet.val, ((rewards e.time i).val : ℝ) / (D p : ℝ)) +
    ((rewards e.time e.fastArm).val : ℝ) / (D p : ℝ)

def frozenReward (q : Fin p.T) : ℝ :=
  (∑ i ∈ (frozenSlowSet p).val, ((rewards q i).val : ℝ) / (D p : ℝ)) +
    ((rewards q (frozenFastArm p)).val : ℝ) / (D p : ℝ)

/-- Sum over exactly the enabled physical dates in `[t,n)`, with their
prescribed frozen actions. The original physical rewards are unchanged. -/
def suffixPayoff (u t : Fin p.T) (n : Fin (p.T + 1))
    (z : StoppedSource rate rewards C_star C_h u t) : ℝ :=
  ∑ i : Fin n.val, if hti : t.val ≤ i.val then
    let q : Fin p.T := ⟨i.val, i.isLt.trans_le (Nat.le_of_lt_succ n.isLt)⟩
    if (suffixInput rate rewards C_star C_h u t q hti z).enabled then frozenReward rewards q else 0
    else 0

theorem suffixPayoff_initial (u t : Fin p.T) (z : StoppedSource rate rewards C_star C_h u t) :
    suffixPayoff rate rewards C_star C_h u t t.castSucc z = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  exact dite_eq_right (Nat.not_le_of_gt i.isLt)

theorem suffixPayoff_succ (u t q : Fin p.T) (htq : t.val ≤ q.val)
    (z : StoppedSource rate rewards C_star C_h u t) :
    suffixPayoff rate rewards C_star C_h u t q.succ z =
      suffixPayoff rate rewards C_star C_h u t q.castSucc z +
        if (suffixInput rate rewards C_star C_h u t q htq z).enabled then frozenReward rewards q else 0 := by
  unfold suffixPayoff
  simp only [Fin.val_succ, Fin.val_castSucc]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last, dite_eq_left htq]

/-- Exact additive accounting keeps the entire accepted prefix and the
whole enabled suffix. In particular its negative is never clipped. -/
theorem initialStoppedPast_payoff (control0 : TimeControl p) (u t : Fin p.T)
    (n : Fin (p.T + 1)) (htn : t.val ≤ n.val)
    (za : StoppedSource rate rewards C_star C_h u t × Auxiliary p) :
    ((initialStoppedPast rate rewards C_star C_h control0 u t n za).map (cellReward rate rewards)).sum =
      ((past t.castSucc (za.1.val, za.2)).map (cellReward rate rewards)).sum +
        suffixPayoff rate rewards C_star C_h u t n za.1 := by
  have hall : ∀ k (hk : k ≤ p.T), t.val ≤ k →
      ((initialStoppedPast rate rewards C_star C_h control0 u t ⟨k, Nat.lt_succ_of_le hk⟩ za).map
        (cellReward rate rewards)).sum =
      ((past t.castSucc (za.1.val, za.2)).map (cellReward rate rewards)).sum +
        suffixPayoff rate rewards C_star C_h u t ⟨k, Nat.lt_succ_of_le hk⟩ za.1 := by
    intro k hk htk
    induction htk with
    | refl =>
      rw [initialStoppedPast_before rate rewards C_star C_h control0 u t _ le_rfl za]
      change _ = ((past t.castSucc (za.1.val, za.2)).map (cellReward rate rewards)).sum +
        suffixPayoff rate rewards C_star C_h u t t.castSucc za.1
      rw [suffixPayoff_initial, add_zero]
      rfl
    | @step k htk ih =>
      let q : Fin p.T := ⟨k, by omega⟩
      change ((initialStoppedPast rate rewards C_star C_h control0 u t q.succ za).map _).sum =
        ((past t.castSucc (za.1.val, za.2)).map (cellReward rate rewards)).sum +
          suffixPayoff rate rewards C_star C_h u t q.succ za.1
      rw [initialStoppedPast_succ rate rewards C_star C_h control0 u t q htk za,
        suffixPayoff_succ rate rewards C_star C_h u t q htk za.1]
      have hprev := ih (Nat.le_of_succ_le hk)
      change ((initialStoppedPast rate rewards C_star C_h control0 u t q.castSucc za).map _).sum =
        ((past t.castSucc (za.1.val, za.2)).map (cellReward rate rewards)).sum +
          suffixPayoff rate rewards C_star C_h u t q.castSucc za.1 at hprev
      cases he : (suffixInput rate rewards C_star C_h u t q htk za.1).enabled <;>
        simp only [Bool.false_eq_true, ite_false, ite_true, List.map_append, List.sum_append,
          List.map_nil, List.sum_nil, List.map_cons, List.sum_cons, add_zero]
      · exact hprev
      · rw [hprev]
        change _ + frozenReward rewards q = _
        exact add_assoc _ _ _
  exact hall n.val (Nat.le_of_lt_succ n.isLt) htn

theorem calendarPastAux_prefix (control0 : TimeControl p) (t : Fin p.T) :
    ∀ n (hn : n ≤ p.T) m (_htm : t.val ≤ m) (hmn : m ≤ n) za,
      calendarPastAux rate rewards C_star C_h control0 t m (hmn.trans hn) za <+:
        calendarPastAux rate rewards C_star C_h control0 t n hn za := by
  intro n hn m htm hmn za
  induction hmn with
  | refl => exact List.prefix_refl _
  | @step k hmk ih =>
    apply (ih (Nat.le_of_succ_le hn)).trans
    have hnot : ¬k < t.val := Nat.not_lt_of_ge (htm.trans hmk)
    conv_rhs => rw [calendarPastAux, ite_eq_right hnot]
    cases calendarCell rate rewards C_star C_h control0 ⟨k, Nat.lt_of_succ_le hn⟩ za with
    | none => exact List.prefix_refl _
    | some e => exact List.prefix_append _ _

/-- The whole accepted prefix, including the detecting cell's proposal and
residual refresh, is retained without changing any field. -/
theorem initialStoppedPast_retains_prefix (control0 : TimeControl p) (u t : Fin p.T)
    (n : Fin (p.T + 1)) (htn : t.val ≤ n.val)
    (za : StoppedSource rate rewards C_star C_h u t × Auxiliary p) :
    past t.castSucc (za.1.val, za.2) <+: initialStoppedPast rate rewards C_star C_h control0 u t n za := by
  have h := calendarPastAux_prefix rate rewards C_star C_h control0 t n.val (Nat.le_of_lt_succ n.isLt)
    t.val le_rfl htn (za.1.val, za.2)
  rw [calendarPastAux_before rate rewards C_star C_h control0 t t.val (by omega) le_rfl] at h
  exact h

/-- Whole-list chronology gives at most one cell at each physical date. -/
theorem initialStoppedPast_chronology (control0 : TimeControl p) (u t : Fin p.T)
    (n : Fin (p.T + 1)) (za : StoppedSource rate rewards C_star C_h u t × Auxiliary p) :
    (initialStoppedPast rate rewards C_star C_h control0 u t n za).Pairwise (fun e f => e.time.val < f.time.val) ∧
      ∀ e ∈ initialStoppedPast rate rewards C_star C_h control0 u t n za, e.time.val < n.val := by
  have hall : ∀ k (hk : k ≤ p.T),
      (calendarPastAux rate rewards C_star C_h control0 t k hk (za.1.val, za.2)).Pairwise
        (fun e f => e.time.val < f.time.val) ∧
      ∀ e ∈ calendarPastAux rate rewards C_star C_h control0 t k hk (za.1.val, za.2), e.time.val < k := by
    intro k
    induction k with
    | zero => intro hk; exact ⟨List.Pairwise.nil, fun _ h => False.elim (List.not_mem_nil h)⟩
    | succ k ih =>
      intro hk
      rw [calendarPastAux]
      split
      next hkt =>
        have h := firstCall_generatedPast_chronology rate rewards C_star C_h u t za.1.val za.1.property.1.1 za.2
          ⟨k + 1, Nat.lt_succ_of_le hk⟩ (by simpa using hkt)
        exact ⟨h.1, fun e he => (h.2.1 e he).2⟩
      next hkt =>
        let q : Fin p.T := ⟨k, Nat.lt_of_succ_le hk⟩
        have htq : t.val ≤ q.val := Nat.le_of_not_gt hkt
        rw [calendarCell_eq_suffix rate rewards C_star C_h control0 u t q htq za.1 za.2]
        have hp := ih (Nat.le_of_succ_le hk)
        cases he : (suffixInput rate rewards C_star C_h u t q htq za.1).enabled
        · simp only [Bool.false_eq_true, ite_false, appendOptional]
          exact ⟨hp.1, fun e he => (hp.2 e he).trans (Nat.lt_succ_self _)⟩
        · simp only [ite_true, appendOptional]
          refine ⟨List.pairwise_append.mpr ⟨hp.1, by simp, ?_⟩, ?_⟩
          · intro e he f hf
            rw [List.mem_singleton.mp hf]
            exact hp.2 e he
          · intro e he
            rcases List.mem_append.mp he with he | he
            · exact (hp.2 e he).trans (Nat.lt_succ_self _)
            · rw [List.mem_singleton.mp he]
              exact Nat.lt_succ_self _
  exact hall n.val (Nat.le_of_lt_succ n.isLt)

/-- Every enabled suffix date occurs, including the invocation itself and
the final physical date. No positive-mass assumption is used. -/
theorem initialStoppedPast_enabled_mem (control0 : TimeControl p) (u t q : Fin p.T)
    (htq : t.val ≤ q.val) (n : Fin (p.T + 1)) (hqn : q.val < n.val)
    (za : StoppedSource rate rewards C_star C_h u t × Auxiliary p)
    (hen : (suffixInput rate rewards C_star C_h u t q htq za.1).enabled = true) :
    suffixCell rate rewards C_star C_h u t q htq za.1 ∈
      initialStoppedPast rate rewards C_star C_h control0 u t n za := by
  have hp := calendarPastAux_prefix rate rewards C_star C_h control0 t n.val (Nat.le_of_lt_succ n.isLt)
    (q.val + 1) (by omega) (Nat.succ_le_of_lt hqn) (za.1.val, za.2)
  apply hp.subset
  change _ ∈ initialStoppedPast rate rewards C_star C_h control0 u t q.succ za
  rw [initialStoppedPast_succ rate rewards C_star C_h control0 u t q htq za]
  simp only [hen, ite_true]
  exact List.mem_append_right _ (List.mem_singleton_self _)

/-- Every suffix entry is its literal enabled physical-date cell. Together
with chronology and enabled coverage this is one cell per enabled date. -/
theorem initialStoppedPast_suffix_fields (control0 : TimeControl p) (u t : Fin p.T)
    (n : Fin (p.T + 1)) (za : StoppedSource rate rewards C_star C_h u t × Auxiliary p)
    (e : LogicalCell p rate) (he : e ∈ initialStoppedPast rate rewards C_star C_h control0 u t n za)
    (hte : t.val ≤ e.time.val) :
    (suffixInput rate rewards C_star C_h u t e.time hte za.1).enabled = true ∧
      e = suffixCell rate rewards C_star C_h u t e.time hte za.1 := by
  have hall : ∀ k (hk : k ≤ p.T) (e : LogicalCell p rate),
      e ∈ calendarPastAux rate rewards C_star C_h control0 t k hk (za.1.val, za.2) →
      ∀ hte : t.val ≤ e.time.val,
        (suffixInput rate rewards C_star C_h u t e.time hte za.1).enabled = true ∧
          e = suffixCell rate rewards C_star C_h u t e.time hte za.1 := by
    intro k
    induction k with
    | zero => intro hk e he; exact False.elim (List.not_mem_nil he)
    | succ k ih =>
      intro hk e he hte
      rw [calendarPastAux] at he
      split at he
      next hkt =>
        have h := firstCall_generatedPast_chronology rate rewards C_star C_h u t za.1.val za.1.property.1.1 za.2
          ⟨k + 1, Nat.lt_succ_of_le hk⟩ (by simpa using hkt)
        have hb := (h.2.1 e he).2
        change e.time.val < k + 1 at hb
        omega
      next hkt =>
        let q : Fin p.T := ⟨k, Nat.lt_of_succ_le hk⟩
        have htq : t.val ≤ q.val := Nat.le_of_not_gt hkt
        rw [calendarCell_eq_suffix rate rewards C_star C_h control0 u t q htq za.1 za.2] at he
        cases hen : (suffixInput rate rewards C_star C_h u t q htq za.1).enabled
        · simp only [hen, Bool.false_eq_true, ite_false, appendOptional] at he
          exact ih (Nat.le_of_succ_le hk) e he hte
        · simp only [hen, ite_true, appendOptional, List.mem_append, List.mem_singleton] at he
          rcases he with he | he
          · exact ih (Nat.le_of_succ_le hk) e he hte
          · subst e
            exact ⟨hen, rfl⟩
  exact hall n.val (Nat.le_of_lt_succ n.isLt) e he hte

theorem initialStoppedPast_signedPayoff (control0 : TimeControl p) (u t : Fin p.T)
    (n : Fin (p.T + 1)) (htn : t.val ≤ n.val)
    (za : StoppedSource rate rewards C_star C_h u t × Auxiliary p) :
    -((initialStoppedPast rate rewards C_star C_h control0 u t n za).map (cellReward rate rewards)).sum =
      -((past t.castSucc (za.1.val, za.2)).map (cellReward rate rewards)).sum -
        suffixPayoff rate rewards C_star C_h u t n za.1 := by
  rw [initialStoppedPast_payoff rate rewards C_star C_h control0 u t n htn za, neg_add, sub_eq_add_neg]

end Bandits.Support.ReferenceInitialStoppedCalendar
