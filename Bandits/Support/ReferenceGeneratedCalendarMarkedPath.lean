/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedCalendarLivePayoff
public import Bandits.Support.ReferenceGeneratedCalendarJointRebase

import Mathlib.Tactic

/-!
# Marked cells of the actual generated calendar

Sources: ZIP4 `06_interruptions.tex:391-426`,
`04_slow_fast_learner.tex:142-215,323-390`, and
`08_main_theorem.tex:78-109`.

The lists, states, sources and auxiliary arrays below are readouts of the
existing raw calendar. Numerical prefixes retain disabled physical dates.
These deterministic identities do not assert conditional round laws or a
manuscript closure.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped Classical
open Bandits.Support ConstructorDimensions
open ReferenceFirstLiveChronologicalPrefixFoundation
open ReferenceFirstCollectionLogicalNumericalAlignment
open ReferencePostInvocationNoncallGeometry
open ReferencePostInvocationPrefixLocality
open ReferencePostInvocationGeneratedAlignment
open ReferenceNextRetainedEndpointFibreLaw
open ReferenceGeneratedInvocationCallSplice
open ReferenceGeneratedRankCalendarFoundation
open ReferenceGeneratedCalendarResidualBlock
open ReferenceGeneratedCalendarEndpointMixture
open ReferenceGeneratedCalendarNativePreservation
open ReferenceGeneratedCalendarPathAgreement
open ReferenceGeneratedCalendarLivePayoff
open ReferenceGeneratedNativeInvocationGeometry
open ReferenceSourcePrefixHistoryFiltration (sourcePrefix)

namespace Bandits.Support.ReferenceGeneratedCalendarMarkedPath

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)

local notation "Source" => BootstrapPrivateRoundStreams.SourceInput p
local notation "Auxiliary" => ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p
local notation "Cell" => LogicalCell p rate
local notation "Record" => ReferenceFirstLiveChronologicalPrefixFoundation.Record rate
local notation "Q" => ReferenceFirstLaunchNumericalCell.queueParameters rate
local notation "start " z:max => ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
local notation "records " z:max => ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
local notation "word" => ReferenceActualCollectionHiddenRefreshPath.actualOriginalWord rate rewards C_star C_h
local notation "recordAt" => ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
local notation "past" => ReferenceFirstCollectionLogicalPrefixExtension.extendedPast rate rewards C_star C_h
local notation "live" => firstLiveChronologicalPrefix rate rewards C_star C_h
local notation "firstCell" => ReferenceCalendarCollectionCallControlLaw.firstCell rate rewards C_star C_h

/-- The nominal schedule flag, before the analytical overflow gate. -/
def nominalEnabled (q : Fin p.T) (z : Source) : Bool :=
  ((recordAt q z).bind (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate)).any
    RecordedQueueRun.RoundInput.enabled

/-- The actual complete word's entry at its physical date. -/
theorem originalWord_inputAt (z : Source)
    (hl : ∃ active, ReferenceCorrectedInitializationLaunch.correctedLaunch rate z rewards C_star C_h = some active)
    (q : Fin p.T) (hsq : start z ≤ q.val) :
    ∃ hi : q.val - start z < (word z hl).length,
      (recordAt q z).bind (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate) =
        some (word z hl)[q.val - start z] := by
  have hiR : q.val - start z < (records z).length := by
    rw [ReferenceCompletePhysicalHistory.completeSuffixRecords_length]
    have := q.isLt
    omega
  have hi : q.val - start z < (word z hl).length := by
    rw [ReferenceActualCollectionHiddenRefreshPath.actualOriginalWord_length]
    exact hiR
  have hm := congrArg (fun L => L[q.val - start z]?)
    (originalWord_record_map rate rewards C_star C_h z hl)
  simp only [List.getElem?_map, List.getElem?_eq_getElem hiR,
    List.getElem?_eq_getElem hi, Option.map_some] at hm
  refine ⟨hi, ?_⟩
  rw [ReferenceSourcePrefixHistoryFiltration.actualRecord, ite_eq_left hsq,
    List.getElem?_eq_getElem hiR, Option.bind_some]
  exact Option.some.inj hm

private theorem live_time (z : Source) (a : Auxiliary) (i : ℕ)
    (hi : i < (live (z, a)).length) :
    ((live (z, a))[i]).time.val = start z + i := by
  have hiw : i < (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow rate rewards C_star C_h z).length := by
    simpa only [firstLiveChronologicalPrefix_length, ReferenceFirstLiveOverflowReadout.wholeFirstLiveLength] using hi
  rw [ReferenceFirstLiveChronologicalPrefixCausality.firstLiveChronologicalPrefix_cellTime rate rewards C_star C_h z a ⟨i, hiw⟩]
  have hp : ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow rate rewards C_star C_h z <+: records z :=
    List.takeWhile_prefix _
  have hr : (records z)[i]? = some (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow rate rewards C_star C_h z)[i] := by
    rw [List.getElem?_eq_getElem (hiw.trans_le hp.length_le), ← hp.getElem hiw]
  exact ReferenceFirstCollectionRenewalRecordingFeedback.complete_record_time rate z rewards C_star C_h i _ hr

/-- Every pre-root mark is the physical record of the same source and date,
including collection marks beyond the first LIVE window. -/
theorem firstPast_physical (z : Source) (a : Auxiliary) (n : Fin (p.T + 1))
    (e : Cell) (he : e ∈ past n (z, a)) :
    ∃ r, recordAt e.time z = some r ∧
      e.physical = ReferenceActiveHorizonMeasurability.roundRecordCode r := by
  by_cases hlive : e ∈ live (z, a)
  · obtain ⟨i, hi, hie⟩ := List.mem_iff_getElem.mp hlive
    have hiw : i < (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow rate rewards C_star C_h z).length := by
      simpa only [firstLiveChronologicalPrefix_length, ReferenceFirstLiveOverflowReadout.wholeFirstLiveLength] using hi
    have hp : ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow rate rewards C_star C_h z <+: records z :=
      List.takeWhile_prefix _
    let r := (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow rate rewards C_star C_h z)[i]
    have ht : e.time.val = start z + i := by rw [← hie]; exact live_time rate rewards C_star C_h z a i hi
    have hn := congrArg (fun L => L[i]?) (firstLiveChronologicalPrefix_physical rate rewards C_star C_h z a)
    simp only [List.getElem?_map, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hiw, Option.map_some] at hn
    refine ⟨r, ?_, ?_⟩
    · rw [ReferenceSourcePrefixHistoryFiltration.actualRecord, ite_eq_left (by omega), ht,
        Nat.add_sub_cancel_left, List.getElem?_eq_getElem (hiw.trans_le hp.length_le), ← hp.getElem hiw]
    · exact (congrArg LogicalCell.physical hie).symm.trans (Option.some.inj hn)
  · obtain ⟨q, r, hr, _hm, _U, _hqn, _hU, _hen, ht, hphysical, _⟩ :=
      ReferenceFirstCollectionLogicalPrefixExtension.generated_collection_cell_fields rate rewards C_star C_h n z a e he hlive
    exact ⟨r, ht ▸ hr, hphysical⟩

/-- Nominal enabledness of every first-prefix entry. Overflow never removes
an enabled mark from the list. -/
theorem firstPast_enabled (z : Source) (a : Auxiliary) (n : Fin (p.T + 1))
    (e : Cell) (he : e ∈ past n (z, a)) : e.numerical.1 = true := by
  by_cases hlive : e ∈ live (z, a)
  · obtain ⟨i, hi, hie⟩ := List.mem_iff_getElem.mp hlive
    have hiw : i < (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow rate rewards C_star C_h z).length := by
      simpa only [firstLiveChronologicalPrefix_length, ReferenceFirstLiveOverflowReadout.wholeFirstLiveLength] using hi
    rw [← hie, firstLiveChronologicalPrefix_get rate rewards C_star C_h z a ⟨i, hiw⟩]
    exact (wholeLiveCell rate rewards C_star C_h z _ (List.getElem_mem hiw)).enabled
  · obtain ⟨_q, _r, _hr, _hm, _U, _hqn, _hU, hen, _ht, _hphysical, hnum, _⟩ :=
      ReferenceFirstCollectionLogicalPrefixExtension.generated_collection_cell_fields rate rewards C_star C_h n z a e he hlive
    exact (congrArg Prod.fst hnum).trans hen

/-- Complete pre-root nominal coverage on an actual first-call source. The
first-call event supplies the launch and original numerical word internally. -/
theorem firstPast_enabled_iff (u t : Fin p.T) (z : Source) (hz : z ∈ firstCell u t)
    (a : Auxiliary) (n : Fin (p.T + 1)) (hnt : n.val ≤ t.val) (q : Fin p.T) (hqn : q.val < n.val) :
    (∃ e ∈ past n (z, a), e.time = q) ↔ nominalEnabled rate rewards C_star C_h q z = true := by
  let hl := firstCall_launch rate rewards C_star C_h u t z hz
  have hchron := firstCall_generatedPast_chronology rate rewards C_star C_h u t z hz a n hnt
  constructor
  · rintro ⟨e, he, rfl⟩
    obtain ⟨hi, hnum, _⟩ := firstCall_generatedPast_cell_data rate rewards C_star C_h u t z hz a n e he
    obtain ⟨_hi, hinput⟩ := originalWord_inputAt rate rewards C_star C_h z hl e.time (hchron.2.1 e he).1
    dsimp only [nominalEnabled]
    rw [hinput, Option.any_some]
    exact (congrArg Prod.fst hnum).symm.trans (firstPast_enabled rate rewards C_star C_h z a n e he)
  · intro hen
    have hs : start z ≤ q.val := by
      by_contra h
      have hr := ReferenceSourcePrefixHistoryFiltration.actualRecord_eq_none_of_future_start
        rate rewards C_star C_h q z (by omega)
      simp only [nominalEnabled, hr, Option.bind_none, Option.any_none, Bool.false_eq_true] at hen
    obtain ⟨hi, hinput⟩ := originalWord_inputAt rate rewards C_star C_h z hl q hs
    have hw : (word z hl)[q.val - start z].enabled = true := by
      simpa only [nominalEnabled, hinput, Option.any_some] using hen
    exact hchron.2.2 q hs hqn (Or.inr ⟨hi, hw⟩)

variable (control0 : ContinuousLearningRows.TimeControl p) (b0 : Bool) (u0 t0 : Fin p.T)

local notation "Sample" => CalendarSample rate rewards C_star C_h b0 u0 t0
local notation "observe" => calendarObservation rate rewards C_star C_h control0 b0 u0 t0
local notation "current" => calendarCurrentSource rate rewards C_star C_h control0 b0 u0 t0
local notation "original" => calendarOriginalLift rate rewards C_star C_h b0 u0 t0
local notation "stored" => calendarStoredState rate rewards C_star C_h control0 b0 u0 t0
local notation "ancestor" => calendarAncestor rate rewards C_star C_h b0 u0 t0
local notation "callFlag" => calendarCallFlag rate rewards C_star C_h control0 b0 u0 t0
local notation "invocation" => calendarInvocationCell rate rewards C_star C_h control0 b0 u0 t0
local notation "lastNative" => calendarLastNativeCell rate rewards C_star C_h control0 b0 u0 t0
local notation "law" => calendarLaw rate rewards C_star C_h control0 b0 u0 t0

private theorem prefix_shrink (n m : ℕ) (hmn : m ≤ n) (z z' : Source)
    (h : sourcePrefix control0 n z = sourcePrefix control0 n z') :
    sourcePrefix control0 m z = sourcePrefix control0 m z' := by
  have hs := congrArg (sourcePrefix control0 m) h
  simpa only [ReferenceSourcePrefixHistoryFiltration.sourcePrefix_sourcePrefix control0 m n hmn] using hs

/-- The full pre-root list, including collection cells, is retained literally.
The final current source and original tape determine that same list. -/
theorem calendar_root_prelist (w : Sample 0) :
    calendarNativePrelist rate rewards C_star C_h control0 b0 u0 t0 0 (by omega) w =
      past t0.castSucc (current 0 (by omega) w, (original 0 w).1.2) := by
  cases b0 with
  | false =>
    change (ReferenceFirstNextInvocationJointLift.EventSource rate rewards C_star C_h u0 t0 × Auxiliary) ×
      AssignmentParameterFibreKernel.AssignmentVector p at w
    unfold calendarNativePrelist
    rw [calendarObservation_initial rate rewards C_star C_h control0 false u0 t0 (by omega) w]
    change (ReferenceFirstNextInstallationTransitionLaw.postHistory
      (ReferenceFirstNextInstallationTransitionLaw.nonrenewedTransition rate rewards C_star C_h control0 u0 t0 w)).dropLast = _
    rw [ReferenceFirstNextInstallationTransitionLaw.nonrenewedTransition_postHistory, List.dropLast_concat]
    change past t0.castSucc (w.1.1.val, w.1.2) = past t0.castSucc
      (ReferenceFirstCollectionRenewalVectorInsertion.insert t0 w.1.1.val w.2, w.1.2)
    exact (congrArg Prod.snd (ReferenceFirstCollectionLogicalPrefixExtension.extendedPrefixStateAux_replace_current
      rate rewards C_star C_h control0 t0.val t0.isLt.le t0 le_rfl w.1.1.val w.1.2
      (ReferenceFirstCollectionRenewalVectorInsertion.ctrl t0 w.1.1.val w.2))).symm
  | true =>
    change ReferenceFirstCollectionRenewalInstallationCoupling.RenewalLift rate rewards C_star C_h u0 t0 at w
    unfold calendarNativePrelist
    rw [calendarObservation_initial rate rewards C_star C_h control0 true u0 t0 (by omega) w]
    change (ReferenceFirstNextInstallationTransitionLaw.postHistory
      (ReferenceFirstNextInstallationTransitionLaw.renewedTransition rate rewards C_star C_h control0 u0 t0 w)).dropLast = _
    rw [ReferenceFirstNextInstallationTransitionLaw.renewedTransition_postHistory, List.dropLast_concat]
    change past t0.castSucc (w.1.1.val, w.1.2) = past t0.castSucc
      ((ReferenceFirstCollectionRenewalVectorInsertion.put rate rewards C_star C_h u0 t0 w.1.1 w.2).val, w.1.2)
    rw [ReferenceFirstCollectionRenewalVectorInsertion.put_val]
    exact (congrArg Prod.snd (ReferenceFirstCollectionLogicalPrefixExtension.extendedPrefixStateAux_replace_current
      rate rewards C_star C_h control0 t0.val t0.isLt.le t0 le_rfl w.1.1.val w.1.2
      (ReferenceFirstCollectionRenewalVectorInsertion.ctrl t0 w.1.1.val w.2))).symm


/-- The cell appended by a literal raw step. This only reads the existing
call/noncall constructors and its actual incoming stored seed. -/
def calendarStepCell (k : ℕ) (hk : t0.val + 1 + k < p.T) (w : Sample k)
    (v : AssignmentParameterFibreKernel.AssignmentVector p) : Option Cell :=
  if hc : callFlag k (by omega) w = true then some (invocation k hk w v hc)
  else noncallDateCell rate rewards C_star C_h ⟨t0.val + 1 + k, hk⟩
    (current k hk.le w) (original k w).1.2 (stored k hk.le w).1

local notation "stepCell" => calendarStepCell rate rewards C_star C_h control0 b0 u0 t0

/-- One actual step appends its optional cell and otherwise preserves the
complete list and carried slow seed. -/
theorem calendarStoredState_succ (k : ℕ) (hk : t0.val + 1 + k < p.T) (w : Sample k)
    (v : AssignmentParameterFibreKernel.AssignmentVector p) :
    stored (k + 1) (by omega) (w, v) =
      match stepCell k hk w v with
      | none => stored k hk.le w
      | some e => (e.nextSlowSet, (stored k hk.le w).2 ++ [e]) := by
  by_cases hc : callFlag k (by omega) w = true
  · rw [calendarStepCell, dite_eq_left hc]
    exact (calendarObservation_call_append rate rewards C_star C_h control0 b0 u0 t0 k hk w v hc).1
  · rw [calendarStepCell, dite_eq_right hc]
    have hf : callFlag k (by omega) w = false := Bool.eq_false_iff.mpr hc
    rw [calendarObservation_noncall_step rate rewards C_star C_h control0 b0 u0 t0 k hk w v hf]
    rfl

/-- Exhaustive membership in the actual nested raw list: full root history,
root UPDATE, or one of the actual later optional UPDATEs. -/
theorem calendarStoredState_mem (k : ℕ) (hk : t0.val + 1 + k ≤ p.T) (w : Sample k) (e : Cell) :
    e ∈ (stored k hk w).2 ↔
      e ∈ (stored 0 (by omega) (ancestor k 0 (Nat.zero_le _) w)).2 ∨
      ∃ (j : ℕ) (hj : j < k),
        let x : Sample j × AssignmentParameterFibreKernel.AssignmentVector p :=
          ancestor k (j + 1) (by omega) w
        stepCell j (by omega) x.1 x.2 = some e := by
  induction k with
  | zero =>
    rw [calendarAncestor_self]
    constructor
    · exact Or.inl
    · rintro (h | ⟨j, hj, _⟩)
      · exact h
      · omega
  | succ k ih =>
    change Sample k × AssignmentParameterFibreKernel.AssignmentVector p at w
    rw [calendarStoredState_succ rate rewards C_star C_h control0 b0 u0 t0 k (by omega) w.1 w.2]
    cases hc : stepCell k (by omega) w.1 w.2 with
    | none =>
      dsimp only
      rw [ih (by omega) w.1]
      constructor
      · rintro (h | ⟨j, hj, he⟩)
        · exact Or.inl (by simpa only [calendarAncestor_succ rate rewards C_star C_h b0 u0 t0 k 0 (Nat.zero_le _) w] using h)
        · exact Or.inr ⟨j, by omega, by simpa only [calendarAncestor_succ rate rewards C_star C_h b0 u0 t0 k (j + 1) (by omega) w] using he⟩
      · rintro (h | ⟨j, hj, he⟩)
        · exact Or.inl (by simpa only [calendarAncestor_succ rate rewards C_star C_h b0 u0 t0 k 0 (Nat.zero_le _) w] using h)
        · by_cases hjk : j = k
          · subst j
            rw [calendarAncestor_self rate rewards C_star C_h b0 u0 t0 (k + 1) w] at he
            rw [hc] at he
            cases he
          · exact Or.inr ⟨j, by omega, by simpa only [calendarAncestor_succ rate rewards C_star C_h b0 u0 t0 k (j + 1) (by omega) w] using he⟩
    | some c =>
      dsimp only
      rw [List.mem_append, List.mem_singleton, ih (by omega) w.1]
      constructor
      · rintro ((h | ⟨j, hj, he⟩) | rfl)
        · exact Or.inl (by simpa only [calendarAncestor_succ rate rewards C_star C_h b0 u0 t0 k 0 (Nat.zero_le _) w] using h)
        · exact Or.inr ⟨j, by omega, by simpa only [calendarAncestor_succ rate rewards C_star C_h b0 u0 t0 k (j + 1) (by omega) w] using he⟩
        · exact Or.inr ⟨k, Nat.lt_succ_self _, by rw [calendarAncestor_self rate rewards C_star C_h b0 u0 t0 (k + 1) w]; exact hc⟩
      · rintro (h | ⟨j, hj, he⟩)
        · exact Or.inl (Or.inl (by simpa only [calendarAncestor_succ rate rewards C_star C_h b0 u0 t0 k 0 (Nat.zero_le _) w] using h))
        · by_cases hjk : j = k
          · subst j
            rw [calendarAncestor_self rate rewards C_star C_h b0 u0 t0 (k + 1) w] at he
            exact Or.inr (Option.some.inj (he.symm.trans hc))
          · exact Or.inl (Or.inr ⟨j, by omega, by simpa only [calendarAncestor_succ rate rewards C_star C_h b0 u0 t0 k (j + 1) (by omega) w] using he⟩)


/-- The exact full pre-root list is a prefix of every later stored list, on
that later source and the unchanged original auxiliary tape. -/
theorem calendar_archived_full_root_past (k : ℕ) (hk : t0.val + 1 + k ≤ p.T) (w : Sample k) :
    past t0.castSucc (current k hk w, (original k w).1.2) <+: (stored k hk w).2 := by
  let root := ancestor k 0 (Nat.zero_le _) w
  have hp := calendarObservation_ancestor_preserves rate rewards C_star C_h control0 b0 u0 t0 k hk w 0 (Nat.zero_le _)
  have hpre : sourcePrefix control0 t0.val (current k hk w) =
      sourcePrefix control0 t0.val (current 0 (by omega) root) :=
    prefix_shrink control0 (t0.val + 1) t0.val (Nat.le_succ _) _ _ hp.2.1
  have hstate := ReferenceFirstCollectionLogicalPrefixExtension.extendedPrefixStateAux_sourcePrefix
    rate rewards C_star C_h control0 t0.val t0.isLt.le (current k hk w) (original k w).1.2
  have hstate' := ReferenceFirstCollectionLogicalPrefixExtension.extendedPrefixStateAux_sourcePrefix
    rate rewards C_star C_h control0 t0.val t0.isLt.le (current 0 (by omega) root) (original k w).1.2
  rw [hpre] at hstate
  have hpast : past t0.castSucc (current k hk w, (original k w).1.2) =
      past t0.castSucc (current 0 (by omega) root, (original 0 root).1.2) := by
    have hsame : original 0 root = original k w :=
      calendarAncestor_original rate rewards C_star C_h b0 u0 t0 k 0 (Nat.zero_le _) w
    simpa only [hsame, ReferenceFirstCollectionLogicalPrefixExtension.extendedPast, Fin.val_castSucc] using congrArg Prod.snd (hstate.trans hstate'.symm)
  rw [hpast, ← calendar_root_prelist rate rewards C_star C_h control0 b0 u0 t0 root]
  have hr := (calendarObservation_root rate rewards C_star C_h control0 b0 u0 t0 (by omega) root).2.1
  apply List.IsPrefix.trans (l₂ := (stored 0 (by omega) root).2) _ hp.1
  rw [hr]
  exact List.prefix_append _ _

private theorem noncall_current (j : ℕ) (hj : t0.val + 1 + j < p.T) (w : Sample j)
    (v : AssignmentParameterFibreKernel.AssignmentVector p) (hc : callFlag j (by omega) w = false) :
    current (j + 1) (by omega) (w, v) = current j hj.le w := by
  let q : Fin p.T := ⟨t0.val + 1 + j, hj⟩
  let o : TaggedPrefix rate q.castSucc := observe j hj.le w
  have hn : ¬ (o.2, ((original j w).1.2, v)) ∈ calendarCallEvent rate rewards C_star C_h o.1 q := by
    change ¬ callFlag j (by omega) w = true
    rw [hc]
    exact Bool.false_ne_true
  change (calendarStep rate rewards C_star C_h control0 q
    (o, ((original j w).1.2, v))).2.val.1.1.1.2 = _
  rw [calendarStep, dite_eq_right hn]
  rfl

/-- An archived appended cell is its literal existing constructor on the
final source, with the actual local UPDATE label or carried collection seed. -/
theorem calendarStepCell_final_constructor (k : ℕ) (hk : t0.val + 1 + k ≤ p.T) (w : Sample k)
    (j : ℕ) (hj : j < k) (e : Cell) :
    let x : Sample j × AssignmentParameterFibreKernel.AssignmentVector p := ancestor k (j + 1) (by omega) w
    let q : Fin p.T := ⟨t0.val + 1 + j, by omega⟩
    stepCell j (by omega) x.1 x.2 = some e →
      (∃ z : InvocationSource rate rewards C_star C_h q,
        z.val = current k hk w ∧ callFlag j (by omega) x.1 = true ∧
        e = nativeCell rate rewards C_star C_h control0 q z
          ((original k w).1.2 (q, if (calendarPendingFlags rate rewards C_star C_h control0 b0 u0 t0 j (by omega) x.1).1 then 0 else 1))) ∨
      (callFlag j (by omega) x.1 = false ∧
        noncallDateCell rate rewards C_star C_h q (current k hk w) (original k w).1.2
          (stored j (by omega) x.1).1 = some e) := by
  dsimp only
  let x : Sample j × AssignmentParameterFibreKernel.AssignmentVector p := ancestor k (j + 1) (by omega) w
  let q : Fin p.T := ⟨t0.val + 1 + j, by omega⟩
  have hp := (calendarObservation_ancestor_preserves rate rewards C_star C_h control0 b0 u0 t0 k hk w
    (j + 1) (by omega)).2.1
  change sourcePrefix control0 (q.val + 1) (current k hk w) =
    sourcePrefix control0 (q.val + 1) (current (j + 1) (by omega) x) at hp
  have ha : (original j x.1).1.2 = (original k w).1.2 := by
    have h := calendarAncestor_original rate rewards C_star C_h b0 u0 t0 k (j + 1) (by omega) w
    exact congrArg (fun y => y.1.2) h
  intro he
  by_cases hc : callFlag j (by omega) x.1 = true
  · left
    rw [calendarStepCell, dite_eq_left hc] at he
    have heq : e = invocation j (by omega) x.1 x.2 hc := (Option.some.inj he).symm
    let z0 := calendarInvocationSource rate rewards C_star C_h control0 b0 u0 t0 j (by omega) x.1 x.2 hc
    have hsource : current (j + 1) (by omega) x = z0.val := by
      exact (calendarObservation_call_prelist rate rewards C_star C_h control0 b0 u0 t0 j (by omega) x.1 x.2 hc).2.2.1
    rw [hsource] at hp
    have hstrict := prefix_shrink control0 (q.val + 1) q.val (Nat.le_succ _) _ _ hp
    have hcall : ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h q (current k hk w) =
        ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h q z0.val := by
      rw [ReferenceCalendarCollectionCallControlLaw.callAt_factor rate rewards C_star C_h control0 q (current k hk w),
        ReferenceCalendarCollectionCallControlLaw.callAt_factor rate rewards C_star C_h control0 q z0.val, hstrict]
    let z : InvocationSource rate rewards C_star C_h q := ⟨current k hk w, by rw [hcall]; exact z0.property⟩
    refine ⟨z, rfl, hc, ?_⟩
    rw [heq, (calendarInvocationCell_update_readouts rate rewards C_star C_h control0 b0 u0 t0 j (by omega) x.1 x.2 hc).1, ha]
    exact nativeCell_sourcePrefix_congr rate rewards C_star C_h control0 q z0 z hp.symm _
  · right
    have hf := Bool.eq_false_iff.mpr hc
    rw [calendarStepCell, dite_eq_right hc] at he
    change sourcePrefix control0 (q.val + 1) (current k hk w) =
      sourcePrefix control0 (q.val + 1) (current (j + 1) (by omega) (x.1, x.2)) at hp
    rw [noncall_current rate rewards C_star C_h control0 b0 u0 t0 j (by omega) x.1 x.2 hf] at hp
    refine ⟨hf, ?_⟩
    rw [noncallDateCell_sourcePrefix rate rewards C_star C_h control0 (q.val + 1) (by omega) q
      (Nat.lt_succ_self _) (current k hk w), hp,
      ← noncallDateCell_sourcePrefix rate rewards C_star C_h control0 (q.val + 1) (by omega) q
        (Nat.lt_succ_self _) (current j (by omega) x.1), ← ha]
    exact he


/-- Physical and numerical fields of the literal native constructor. -/
theorem nativeCell_fields (s : Fin p.T) (z : InvocationSource rate rewards C_star C_h s)
    (x : ContinuousControlSlice.Scalar) :
    let e := nativeCell rate rewards C_star C_h control0 s z x
    let W := word z.val (nativeInvocation_launch rate rewards C_star C_h s z)
    (∃ r, recordAt e.time z.val = some r ∧ e.physical = ReferenceActiveHorizonMeasurability.roundRecordCode r) ∧
    e.before = RecordedQueueRun.run Q (W.take (e.time.val - start z.val)) ∧
    e.after = RecordedQueueRun.run Q (W.take (e.time.val + 1 - start z.val)) ∧
    ∃ hi : e.time.val - start z.val < W.length,
      W[e.time.val - start z.val].enabled = true ∧
      e.numerical = ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates W[e.time.val - start z.val] ∧
      e.arrivals = RecordedQueueRun.acceptedRecord Q e.before W[e.time.val - start z.val] ∧
      e.service = fun j => RecordedQueueRun.recordService (4 * (Q).n) (e.before.registers j) (e.arrivals j) := by
  dsimp only
  obtain ⟨ht, hb, ha, hi, hn, harr, hservice⟩ := nativeCell_originalWord rate rewards C_star C_h control0 s z x
  have hs := nativeSourceCell_spec rate rewards C_star C_h s z
  refine ⟨⟨nativeRecord rate rewards C_star C_h s z, ?_, rfl⟩, ?_⟩
  · rw [ht]
    exact hs.1
  · rw [ht]
    refine ⟨hb, ha, hi, ?_, hn, harr, hservice⟩
    exact (congrArg Prod.fst hn).symm.trans (nativeSourceCell rate rewards C_star C_h s z).enabled

/-- Same-source noncall fields, conditional only on a literal optional
constructor outcome and a launch. Generated callers produce both inputs. -/
theorem noncallDateCell_fields (z : Source)
    (hl : ∃ active, ReferenceCorrectedInitializationLaunch.correctedLaunch rate z rewards C_star C_h = some active)
    (a : Auxiliary) (q : Fin p.T) (U : SlowSet p) (e : Cell)
    (he : noncallDateCell rate rewards C_star C_h q z a U = some e) :
    let W := word z hl
    (∃ r, recordAt e.time z = some r ∧ e.physical = ReferenceActiveHorizonMeasurability.roundRecordCode r) ∧
    e.before = RecordedQueueRun.run Q (W.take (e.time.val - start z)) ∧
    e.after = RecordedQueueRun.run Q (W.take (e.time.val + 1 - start z)) ∧
    ∃ hi : e.time.val - start z < W.length,
      W[e.time.val - start z].enabled = true ∧
      e.numerical = ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates W[e.time.val - start z] ∧
      e.arrivals = RecordedQueueRun.acceptedRecord Q e.before W[e.time.val - start z] ∧
      e.service = fun j => RecordedQueueRun.recordService (4 * (Q).n) (e.before.registers j) (e.arrivals j) := by
  dsimp only
  obtain ⟨ht, hb, ha, r, c, hr, hc, hen, hphys, hn, harr, hservice⟩ :=
    noncallDateCell_actualWord rate rewards C_star C_h q z hl a U e he
  have hs := (actualRecord_index rate rewards C_star C_h q z r hr).choose_spec.2.2
  obtain ⟨hi, hinput⟩ := originalWord_inputAt rate rewards C_star C_h z hl q hs
  rw [hr, Option.bind_some, hc] at hinput
  have hci := Option.some.inj hinput
  rw [hci] at hen hn harr
  rw [ht]
  exact ⟨⟨r, hr, hphys⟩, hb, ha, hi, hen, hn, harr, hservice⟩

/-- The pre-root history in a final sample is exactly its original root
prelist, including every collection entry. -/
theorem calendar_root_prelist_final (k : ℕ) (hk : t0.val + 1 + k ≤ p.T) (w : Sample k) :
    calendarNativePrelist rate rewards C_star C_h control0 b0 u0 t0 0 (by omega)
      (ancestor k 0 (Nat.zero_le _) w) = past t0.castSucc (current k hk w, (original k w).1.2) := by
  let root := ancestor k 0 (Nat.zero_le _) w
  rw [calendar_root_prelist rate rewards C_star C_h control0 b0 u0 t0 root]
  have hp := (calendarObservation_ancestor_preserves rate rewards C_star C_h control0 b0 u0 t0 k hk w
    0 (Nat.zero_le _)).2.1
  have hpre : sourcePrefix control0 t0.val (current k hk w) =
      sourcePrefix control0 t0.val (current 0 (by omega) root) :=
    prefix_shrink control0 (t0.val + 1) t0.val (Nat.le_succ _) _ _ hp
  change (ReferenceFirstCollectionLogicalPrefixExtension.extendedPrefixStateAux rate rewards C_star C_h
    t0.val t0.isLt.le (current 0 (by omega) root, (original 0 root).1.2)).2 = _
  rw [ReferenceFirstCollectionLogicalPrefixExtension.extendedPrefixStateAux_sourcePrefix
    rate rewards C_star C_h control0 t0.val t0.isLt.le (current 0 (by omega) root)]
  change _ = (ReferenceFirstCollectionLogicalPrefixExtension.extendedPrefixStateAux rate rewards C_star C_h
    t0.val t0.isLt.le (current k hk w, (original k w).1.2)).2
  rw [ReferenceFirstCollectionLogicalPrefixExtension.extendedPrefixStateAux_sourcePrefix
    rate rewards C_star C_h control0 t0.val t0.isLt.le (current k hk w), hpre,
    ← calendarAncestor_original rate rewards C_star C_h b0 u0 t0 k 0 (Nat.zero_le _) w]

/-- Every generated mark, from all archived segments and the full pre-root
history, has its physical and numerical fields on the SAME final source.
The launch and complete original word are produced from its actual first call. -/
theorem calendar_cell_fields (k : ℕ) (hk : t0.val + 1 + k ≤ p.T) (w : Sample k) :
    let z := current k hk w
    let hl := firstCall_launch rate rewards C_star C_h u0 t0 z
      (calendarCurrentSource_firstCell rate rewards C_star C_h control0 b0 u0 t0 k hk w)
    let W := word z hl
    ∀ e ∈ (stored k hk w).2,
      (∃ r, recordAt e.time z = some r ∧ e.physical = ReferenceActiveHorizonMeasurability.roundRecordCode r) ∧
      e.before = RecordedQueueRun.run Q (W.take (e.time.val - start z)) ∧
      e.after = RecordedQueueRun.run Q (W.take (e.time.val + 1 - start z)) ∧
      ∃ hi : e.time.val - start z < W.length,
        W[e.time.val - start z].enabled = true ∧
        e.numerical = ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates W[e.time.val - start z] ∧
        e.arrivals = RecordedQueueRun.acceptedRecord Q e.before W[e.time.val - start z] ∧
        e.service = fun j => RecordedQueueRun.recordService (4 * (Q).n) (e.before.registers j) (e.arrivals j) := by
  dsimp only
  intro e he
  have hf := calendarCurrentSource_firstCell rate rewards C_star C_h control0 b0 u0 t0 k hk w
  let hl := firstCall_launch rate rewards C_star C_h u0 t0 (current k hk w) hf
  rcases (calendarStoredState_mem rate rewards C_star C_h control0 b0 u0 t0 k hk w e).mp he with hr | ⟨j, hj, hstep⟩
  · let root := ancestor k 0 (Nat.zero_le _) w
    rw [(calendarObservation_root rate rewards C_star C_h control0 b0 u0 t0 (by omega) root).2.1] at hr
    rcases List.mem_append.mp hr with hp | hc
    · rw [calendar_root_prelist_final rate rewards C_star C_h control0 b0 u0 t0 k hk w] at hp
      obtain ⟨hi, hn, hb, ha, harr, hservice, _hall⟩ := firstCall_generatedPast_cell_data rate rewards C_star C_h
        u0 t0 (current k hk w) hf (original k w).1.2 t0.castSucc e hp
      refine ⟨firstPast_physical rate rewards C_star C_h _ _ _ e hp, hb, ha, hi, ?_, hn, harr, hservice⟩
      exact (congrArg Prod.fst hn).symm.trans (firstPast_enabled rate rewards C_star C_h _ _ _ e hp)
    · have heq := List.mem_singleton.mp hc
      have hrn := (calendarObservation_root rate rewards C_star C_h control0 b0 u0 t0 (by omega) root).1
      obtain ⟨z, hz, hnative⟩ := calendarObservation_archived_native rate rewards C_star C_h control0 b0 u0 t0
        k hk w 0 (Nat.zero_le _)
      change z.val = current k hk w at hz
      have heq' : e = nativeCell rate rewards C_star C_h control0 (observe 0 (by omega) root).1 z
          ((original 0 root).1.2 ((observe 0 (by omega) root).1,
            if calendarNativeRenewal rate rewards C_star C_h control0 b0 u0 t0 0 (by omega) root then 0 else 1)) :=
        heq.trans (hrn.symm.trans hnative.symm)
      rw [heq']
      simpa only [hz] using nativeCell_fields rate rewards C_star C_h control0 _ z
        ((original 0 root).1.2 ((observe 0 (by omega) root).1,
          if calendarNativeRenewal rate rewards C_star C_h control0 b0 u0 t0 0 (by omega) root then 0 else 1))
  · rcases calendarStepCell_final_constructor rate rewards C_star C_h control0 b0 u0 t0 k hk w j hj e hstep with
      ⟨z, hz, _hc, heq⟩ | ⟨_hc, heq⟩
    · rw [heq]
      simpa only [hz] using nativeCell_fields rate rewards C_star C_h control0 _ z _
    · exact noncallDateCell_fields rate rewards C_star C_h _ hl _ _ _ e heq


private theorem cell0_coordinates (r : Record) :
    (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r).map
        ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates =
      (ReferenceCompleteNumericalBranchObservation.branchReadout rate 0 r).map (Sum.elim id id) := by
  have hp := ReferenceCompleteNumericalBranchObservation.branch_readout_projections rate 0 r
  rw [ReferenceFirstCollectionCurrentRetainedGate.cell0, Option.map_or]
  have hl := congrArg Prod.fst hp
  have hr := congrArg Prod.snd hp
  change ReferenceCompleteNumericalBranchObservation.leftProjection _ =
    (ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r).map
      ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates at hl
  change ReferenceCompleteNumericalBranchObservation.rightProjection _ =
    (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 r).map
      ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates at hr
  rw [← hl, ← hr]
  cases h : ReferenceCompleteNumericalBranchObservation.branchReadout rate 0 r with
  | none => rfl
  | some c => cases c <;> rfl

/-- Nominal enabledness uses only the physical prefix through its own date. -/
theorem nominalEnabled_sourcePrefix (n : ℕ) (hn : n ≤ p.T) (q : Fin p.T)
    (hqn : q.val < n) (z : Source) :
    nominalEnabled rate rewards C_star C_h q z =
      nominalEnabled rate rewards C_star C_h q (sourcePrefix control0 n z) := by
  have hobs := actualObservation_sourcePrefix rate rewards C_star C_h control0 n hn q hqn z
  have h := congrArg (fun o => o.bind (fun e => e.2.2.map (Sum.elim id id))) hobs
  have hnum : ((recordAt q z).bind (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate)).map
        ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates =
      ((recordAt q (sourcePrefix control0 n z)).bind (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate)).map
        ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates := by
    simpa only [Option.bind_map, Option.map_bind, Function.comp_def, cell0_coordinates] using h
  have he := congrArg (fun o => o.any Prod.fst) hnum
  simpa only [Option.any_map, nominalEnabled, ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates] using he

/-- Every actual optional appended cell has its calendar step's date. -/
theorem calendarStepCell_time (j : ℕ) (hj : t0.val + 1 + j < p.T) (w : Sample j)
    (v : AssignmentParameterFibreKernel.AssignmentVector p) (e : Cell)
    (he : stepCell j hj w v = some e) : e.time = ⟨t0.val + 1 + j, hj⟩ := by
  by_cases hc : callFlag j (by omega) w = true
  · rw [calendarStepCell, dite_eq_left hc] at he
    rw [← Option.some.inj he]
    exact (calendarObservation_call_append rate rewards C_star C_h control0 b0 u0 t0 j hj w v hc).2.2
  · rw [calendarStepCell, dite_eq_right hc] at he
    let z := calendarNativeSource rate rewards C_star C_h control0 b0 u0 t0 j hj.le w
    exact (noncallDateCell_actualWord rate rewards C_star C_h _ z.val
      (nativeInvocation_launch rate rewards C_star C_h _ z) _ _ e he).1

/-- Every nominally enabled later date actually appends a cell. The sample
is unrestricted; the stopped branch is included. -/
theorem calendar_enabled_step_exists (k : ℕ) (hk : t0.val + 1 + k ≤ p.T) (w : Sample k)
    (j : ℕ) (hj : j < k)
    (hen : nominalEnabled rate rewards C_star C_h ⟨t0.val + 1 + j, by omega⟩ (current k hk w) = true) :
    let x : Sample j × AssignmentParameterFibreKernel.AssignmentVector p := ancestor k (j + 1) (by omega) w
    ∃ e, stepCell j (by omega) x.1 x.2 = some e ∧ e.time = ⟨t0.val + 1 + j, by omega⟩ := by
  dsimp only
  let x : Sample j × AssignmentParameterFibreKernel.AssignmentVector p := ancestor k (j + 1) (by omega) w
  let q : Fin p.T := ⟨t0.val + 1 + j, by omega⟩
  by_cases hc : callFlag j (by omega) x.1 = true
  · refine ⟨invocation j (by omega) x.1 x.2 hc, ?_, ?_⟩
    · exact dite_eq_left hc
    · exact (calendarObservation_call_append rate rewards C_star C_h control0 b0 u0 t0 j (by omega) x.1 x.2 hc).2.2
  · have hf := Bool.eq_false_iff.mpr hc
    have hp := (calendarObservation_ancestor_preserves rate rewards C_star C_h control0 b0 u0 t0 k hk w
      (j + 1) (by omega)).2.1
    change sourcePrefix control0 (q.val + 1) (current k hk w) =
      sourcePrefix control0 (q.val + 1) (current (j + 1) (by omega) (x.1, x.2)) at hp
    rw [noncall_current rate rewards C_star C_h control0 b0 u0 t0 j (by omega) x.1 x.2 hf] at hp
    have heq : nominalEnabled rate rewards C_star C_h q (current k hk w) =
        nominalEnabled rate rewards C_star C_h q (current j (by omega) x.1) := by
      rw [nominalEnabled_sourcePrefix rate rewards C_star C_h control0 (q.val + 1) (by omega) q
        (Nat.lt_succ_self _) (current k hk w), hp,
        ← nominalEnabled_sourcePrefix rate rewards C_star C_h control0 (q.val + 1) (by omega) q
          (Nat.lt_succ_self _) (current j (by omega) x.1)]
    have hpresence := calendarObservation_noncall_presence rate rewards C_star C_h control0 b0 u0 t0
      j (by omega) x.1 hf
    change (noncallDateCell rate rewards C_star C_h q (current j (by omega) x.1)
      (original j x.1).1.2 (stored j (by omega) x.1).1).isSome =
        nominalEnabled rate rewards C_star C_h q (current j (by omega) x.1) at hpresence
    have hsome : (stepCell j (by omega) x.1 x.2).isSome = true := by
      rw [calendarStepCell, dite_eq_right hc, hpresence, ← heq]
      exact hen
    obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hsome
    exact ⟨e, he, calendarStepCell_time rate rewards C_star C_h control0 b0 u0 t0 j (by omega) x.1 x.2 e he⟩

/-- Full exact nominal coverage through any produced POST boundary. This
includes every date before the root, every archived segment, and the root at
`T-1`. Disabled dates have no cell. -/
theorem calendar_enabled_iff (k : ℕ) (hk : t0.val + 1 + k ≤ p.T) (w : Sample k)
    (q : Fin p.T) (hqn : q.val < t0.val + 1 + k) :
    (∃ e ∈ (stored k hk w).2, e.time = q) ↔
      nominalEnabled rate rewards C_star C_h q (current k hk w) = true := by
  have hf := calendarCurrentSource_firstCell rate rewards C_star C_h control0 b0 u0 t0 k hk w
  let hl := firstCall_launch rate rewards C_star C_h u0 t0 (current k hk w) hf
  constructor
  · rintro ⟨e, he, rfl⟩
    obtain ⟨⟨r, hr, _⟩, _hb, _ha, hi, hen, _⟩ := calendar_cell_fields rate rewards C_star C_h control0 b0 u0 t0 k hk w e he
    have hs := (actualRecord_index rate rewards C_star C_h e.time (current k hk w) r hr).choose_spec.2.2
    obtain ⟨_hi, hinput⟩ := originalWord_inputAt rate rewards C_star C_h _ hl e.time hs
    simpa only [nominalEnabled, hinput, Option.any_some] using hen
  · intro hen
    by_cases hbefore : q.val < t0.val
    · obtain ⟨e, he, ht⟩ := (firstPast_enabled_iff rate rewards C_star C_h u0 t0 (current k hk w)
        hf (original k w).1.2 t0.castSucc le_rfl q hbefore).mpr hen
      exact ⟨e, (calendar_archived_full_root_past rate rewards C_star C_h control0 b0 u0 t0 k hk w).sublist.subset he, ht⟩
    · by_cases hroot : q = t0
      · let root := ancestor k 0 (Nat.zero_le _) w
        have hm : lastNative 0 (by omega) root ∈ (stored k hk w).2 := by
          apply (calendarObservation_ancestor_preserves rate rewards C_star C_h control0 b0 u0 t0 k hk w
            0 (Nat.zero_le _)).1.sublist.subset
          apply (calendarObservation_native_prefix rate rewards C_star C_h control0 b0 u0 t0 0 (by omega) root).1.sublist.subset
          exact List.mem_append_right _ (List.mem_singleton_self _)
        refine ⟨_, hm, ?_⟩
        have ht : (lastNative 0 (by omega) root).time = (observe 0 (by omega) root).1 :=
          nativeCell_time rate rewards C_star C_h control0 _ _ _
        have htag : (observe 0 (by omega) root).1 = t0 := by cases b0 <;> rfl
        exact ht.trans (htag.trans hroot.symm)
      · have hafter : t0.val < q.val := by
          have hne : q.val ≠ t0.val := fun h => hroot (Fin.ext h)
          omega
        let j := q.val - (t0.val + 1)
        have hj : j < k := by dsimp only [j]; omega
        have hq : (⟨t0.val + 1 + j, by omega⟩ : Fin p.T) = q := Fin.ext (by dsimp only [j]; omega)
        obtain ⟨e, he, ht⟩ := calendar_enabled_step_exists rate rewards C_star C_h control0 b0 u0 t0 k hk w j hj
          (by rw [hq]; exact hen)
        refine ⟨e, (calendarStoredState_mem rate rewards C_star C_h control0 b0 u0 t0 k hk w e).mpr
          (Or.inr ⟨j, hj, he⟩), ht.trans hq⟩

/-- Strict chronology makes the marked cell at each date unique. -/
theorem calendar_time_injective (k : ℕ) (hk : t0.val + 1 + k ≤ p.T) (w : Sample k)
    (e f : Cell) (he : e ∈ (stored k hk w).2) (hf : f ∈ (stored k hk w).2)
    (ht : e.time = f.time) : e = f := by
  have hchron : (stored k hk w).2.Pairwise (fun e f => e.time.val < f.time.val) :=
    (calendarObservation_chronology rate rewards C_star C_h control0 b0 u0 t0 k hk w).1
  obtain ⟨i, hi, hie⟩ := List.mem_iff_getElem.mp he
  obtain ⟨j, hj, hjf⟩ := List.mem_iff_getElem.mp hf
  have hij : i = j := by
    by_contra h
    rcases lt_or_gt_of_ne h with hlt | hgt
    · have hrel := List.pairwise_iff_getElem.mp hchron i j hi hj hlt
      rw [hie, hjf, ht] at hrel
      exact (Nat.lt_irrefl _ hrel).elim
    · have hrel := List.pairwise_iff_getElem.mp hchron j i hj hi hgt
      rw [hie, hjf, ht] at hrel
      exact (Nat.lt_irrefl _ hrel).elim
  subst j
  exact hie.symm.trans hjf

/-- Exactly one cell occurs at each nominally enabled processed date. -/
theorem calendar_enabled_unique (k : ℕ) (hk : t0.val + 1 + k ≤ p.T) (w : Sample k)
    (q : Fin p.T) (hqn : q.val < t0.val + 1 + k) :
    (∃! e : Cell, e ∈ (stored k hk w).2 ∧ e.time = q) ↔
      nominalEnabled rate rewards C_star C_h q (current k hk w) = true := by
  constructor
  · rintro ⟨e, he, _⟩
    exact (calendar_enabled_iff rate rewards C_star C_h control0 b0 u0 t0 k hk w q hqn).mp ⟨e, he.1, he.2⟩
  · intro hen
    obtain ⟨e, he, ht⟩ := (calendar_enabled_iff rate rewards C_star C_h control0 b0 u0 t0 k hk w q hqn).mpr hen
    refine ⟨e, ⟨he, ht⟩, ?_⟩
    intro f hf
    exact calendar_time_injective rate rewards C_star C_h control0 b0 u0 t0 k hk w f e hf.1 he (hf.2.trans ht.symm)


/-- All-arm replay and the `4n` service bound for every mark, on the same
full source word. Disabled gaps remain in both run prefixes. -/
theorem calendar_cell_all_arm (k : ℕ) (hk : t0.val + 1 + k ≤ p.T) (w : Sample k)
    (e : Cell) (he : e ∈ (stored k hk w).2) :
    ∀ j, e.service j ≤ 4 * (Q).n ∧
      e.after.registers j = QueueReplay.transition (4 * (Q).n) (e.before.registers j) (e.arrivals j) := by
  obtain ⟨⟨r, hr, _⟩, hb, ha, hi, _hen, _hn, harr, hservice⟩ :=
    calendar_cell_fields rate rewards C_star C_h control0 b0 u0 t0 k hk w e he
  have hs := (actualRecord_index rate rewards C_star C_h e.time (current k hk w) r hr).choose_spec.2.2
  have hstep : e.after = RecordedQueueRun.step Q e.before
      ((word (current k hk w) (firstCall_launch rate rewards C_star C_h u0 t0 (current k hk w)
        (calendarCurrentSource_firstCell rate rewards C_star C_h control0 b0 u0 t0 k hk w)))[e.time.val - start (current k hk w)]) := by
    rw [ha, hb, Nat.sub_add_comm hs, ← List.take_append_getElem hi, RecordedSlowRefresh.run_append_singleton]
  intro j
  constructor
  · rw [hservice]
    exact RecordedQueueRun.recordService_le_capacity _ _ _
  · rw [hstep]
    change QueueReplay.transition (4 * (Q).n) (e.before.registers j) _ = _
    rw [harr]

/-- Disabled physical dates still append false/zero records to the complete
numerical history. Their registers are preserved; their full states need not
be equal because their record histories grow. -/
theorem calendar_disabled_padding (k : ℕ) (hk : t0.val + 1 + k ≤ p.T) (w : Sample k)
    (q : Fin p.T) (hsq : start (current k hk w) ≤ q.val)
    (hdisabled : nominalEnabled rate rewards C_star C_h q (current k hk w) = false) :
    let z := current k hk w
    let W := word z (firstCall_launch rate rewards C_star C_h u0 t0 z
      (calendarCurrentSource_firstCell rate rewards C_star C_h control0 b0 u0 t0 k hk w))
    let S := RecordedQueueRun.run Q (W.take (q.val - start z))
    let S' := RecordedQueueRun.run Q (W.take (q.val + 1 - start z))
    ∀ j, S'.registers j = S.registers j ∧ S'.records j = S.records j ++ [(false, 0)] := by
  dsimp only
  obtain ⟨hi, hinput⟩ := originalWord_inputAt rate rewards C_star C_h (current k hk w)
    (firstCall_launch rate rewards C_star C_h u0 t0 (current k hk w)
      (calendarCurrentSource_firstCell rate rewards C_star C_h control0 b0 u0 t0 k hk w)) q hsq
  have hen : ((word (current k hk w) (firstCall_launch rate rewards C_star C_h u0 t0 (current k hk w)
      (calendarCurrentSource_firstCell rate rewards C_star C_h control0 b0 u0 t0 k hk w)))[q.val - start (current k hk w)]).enabled = false := by
    simpa only [nominalEnabled, hinput, Option.any_some] using hdisabled
  rw [Nat.sub_add_comm hsq, ← List.take_append_getElem hi, RecordedSlowRefresh.run_append_singleton]
  intro j
  refine ⟨(RecordedQueueRun.step_disabled_preserves _ _ _ hen j).1, ?_⟩
  change _ ++ [_] = _
  simp only [RecordedQueueRun.acceptedRecord, hen, Bool.false_eq_true, ite_false, ite_self]


/-- Every first-prefix mark is its original LIVE constructor or its original
collection constructor with the generated incoming seed. -/
theorem firstPast_constructor (z : Source) (a : Auxiliary) (n : Fin (p.T + 1))
    (e : Cell) (he : e ∈ past n (z, a)) :
    (∃ i : Fin (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow rate rewards C_star C_h z).length,
      e = appendLogicalCell
        ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow rate rewards C_star C_h z)[i.val])
        (wholeLiveCell rate rewards C_star C_h z _ (List.getElem_mem i.isLt))
        (RecordedQueueRun.run Q ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h z).take i.val)) a) ∨
    ∃ (q : Fin p.T) (U : SlowSet p), q.val < n.val ∧
      (ReferenceFirstCollectionLogicalPrefixExtension.extendedPrefixStateAux rate rewards C_star C_h
        q.val q.isLt.le (z, a)).1 = some U ∧
      ReferenceFirstCollectionLogicalPrefixExtension.collectionCellAt rate rewards C_star C_h q U (z, a) = some e := by
  rcases ReferenceFirstCollectionLogicalPrefixExtension.extendedPast_collection_origin rate rewards C_star C_h
    n.val (Nat.le_of_lt_succ n.isLt) (z, a) e he with hlive | hcollection
  · left
    obtain ⟨i, hi, hie⟩ := List.mem_iff_getElem.mp hlive
    have hiw : i < (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow rate rewards C_star C_h z).length := by
      simpa only [firstLiveChronologicalPrefix_length, ReferenceFirstLiveOverflowReadout.wholeFirstLiveLength] using hi
    exact ⟨⟨i, hiw⟩, hie.symm.trans (firstLiveChronologicalPrefix_get rate rewards C_star C_h z a ⟨i, hiw⟩)⟩
  · exact Or.inr hcollection

/-- The optional noncall's two actual constructor alternatives. -/
theorem noncallDateCell_constructor (q : Fin p.T) (z : Source) (a : Auxiliary) (U : SlowSet p)
    (e : Cell) (he : noncallDateCell rate rewards C_star C_h q z a U = some e) :
    (∃ hz : z ∈ ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualDomain rate rewards C_star C_h q,
      e = continuingLogicalCell rate rewards C_star C_h q ⟨z, hz⟩ a) ∨
    (∃ hz : z ∈ collectionDateDomain rate rewards C_star C_h q,
      (collectionInput rate rewards C_star C_h q ⟨z, hz⟩).enabled = true ∧
      e = laterCollectionCell rate rewards C_star C_h q ⟨z, hz⟩ U a) := by
  unfold noncallDateCell at he
  split at he
  next h => exact Or.inl ⟨h, (Option.some.inj he).symm⟩
  next _ =>
    split at he
    next h =>
      unfold laterCollectionCell? at he
      split at he
      next hen => exact Or.inr ⟨h, hen, (Option.some.inj he).symm⟩
      next _ => cases he
    next _ => cases he

/-- Exhaustive mark provenance on the same final source. Pre-root entries
use the original prefix recursion; root and later calls use their actual
local UPDATE labels; noncalls use the actual archived carried seed. -/
theorem calendar_mark_origins (k : ℕ) (hk : t0.val + 1 + k ≤ p.T) (w : Sample k)
    (e : Cell) (he : e ∈ (stored k hk w).2) :
    let root := ancestor k 0 (Nat.zero_le _) w
    let s := (observe 0 (by omega) root).1
    let A := (original k w).1.2
    e ∈ past t0.castSucc (current k hk w, A) ∨
    (∃ z : InvocationSource rate rewards C_star C_h s,
      z.val = current k hk w ∧ e = nativeCell rate rewards C_star C_h control0 s z
        (A (s, if b0 then 0 else 1))) ∨
    ∃ (j : ℕ) (hj : j < k),
      let x : Sample j × AssignmentParameterFibreKernel.AssignmentVector p := ancestor k (j + 1) (by omega) w
      let q : Fin p.T := ⟨t0.val + 1 + j, by omega⟩
      (∃ z : InvocationSource rate rewards C_star C_h q,
        z.val = current k hk w ∧ callFlag j (by omega) x.1 = true ∧
        e = nativeCell rate rewards C_star C_h control0 q z
          (A (q, if (calendarPendingFlags rate rewards C_star C_h control0 b0 u0 t0 j (by omega) x.1).1 then 0 else 1))) ∨
      (callFlag j (by omega) x.1 = false ∧ noncallDateCell rate rewards C_star C_h q
        (current k hk w) A (stored j (by omega) x.1).1 = some e) := by
  dsimp only
  rcases (calendarStoredState_mem rate rewards C_star C_h control0 b0 u0 t0 k hk w e).mp he with hr | ⟨j, hj, hstep⟩
  · let root := ancestor k 0 (Nat.zero_le _) w
    rw [(calendarObservation_root rate rewards C_star C_h control0 b0 u0 t0 (by omega) root).2.1] at hr
    rcases List.mem_append.mp hr with hp | hc
    · exact Or.inl ((calendar_root_prelist_final rate rewards C_star C_h control0 b0 u0 t0 k hk w) ▸ hp)
    · right; left
      obtain ⟨z, hz, hnative⟩ := calendarObservation_archived_native rate rewards C_star C_h control0 b0 u0 t0 k hk w
        0 (Nat.zero_le _)
      refine ⟨z, hz, ?_⟩
      have hrn := (calendarObservation_root rate rewards C_star C_h control0 b0 u0 t0 (by omega) root).1
      have heq := (List.mem_singleton.mp hc).trans (hrn.symm.trans hnative.symm)
      have hA : (original 0 root).1.2 = (original k w).1.2 :=
        congrArg (fun y => y.1.2) (calendarAncestor_original rate rewards C_star C_h b0 u0 t0 k 0 (Nat.zero_le _) w)
      refine heq.trans ?_
      apply congrArg (nativeCell rate rewards C_star C_h control0 _ z)
      exact congrFun hA _
  · exact Or.inr (Or.inr ⟨j, hj,
      calendarStepCell_final_constructor rate rewards C_star C_h control0 b0 u0 t0 k hk w j hj e hstep⟩)


private theorem firstPast_stopped (z : Source) (a : Auxiliary) (n : Fin (p.T + 1))
    (e : Cell) (he : e ∈ past n (z, a)) (hstop : e.before.overflow = true) :
    e.slowSet = frozenSlowSet p ∧ e.fastArm = frozenFastArm p ∧
      e.proposal = false ∧ e.nextSlowSet = frozenSlowSet p := by
  by_cases hlive : e ∈ live (z, a)
  · obtain ⟨i, hi, hie⟩ := List.mem_iff_getElem.mp hlive
    have hiw : i < (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow rate rewards C_star C_h z).length := by
      simpa only [firstLiveChronologicalPrefix_length, ReferenceFirstLiveOverflowReadout.wholeFirstLiveLength] using hi
    have heq := hie.symm.trans (firstLiveChronologicalPrefix_get rate rewards C_star C_h z a ⟨i, hiw⟩)
    rw [heq] at hstop ⊢
    let S := RecordedQueueRun.run Q ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h z).take i)
    change S.overflow = true at hstop
    have h := appendLogicalCell_after_overflow
      ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow rate rewards C_star C_h z)[i])
      (wholeLiveCell rate rewards C_star C_h z _ (List.getElem_mem hiw)) S a hstop
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
  · obtain ⟨_q, _r, _hr, _hm, _U, _hqn, _hU, _hen, _ht, _hphysical,
        _hnum, hb, _ha, _harr, _hservice, hslow, hfast, hproposal, hnext, _hall⟩ :=
      ReferenceFirstCollectionLogicalPrefixExtension.generated_collection_cell_fields rate rewards C_star C_h n z a e he hlive
    have hov := (congrArg RecordedQueueRun.RunState.overflow hb).symm.trans hstop
    rw [hslow, hfast, hproposal, hnext, hov]
    simp only [ite_true, Bool.not_true, Bool.and_false, Bool.false_and, and_self]

private theorem nativeCell_stopped (s : Fin p.T) (z : InvocationSource rate rewards C_star C_h s)
    (x : ContinuousControlSlice.Scalar)
    (hstop : (nativeCell rate rewards C_star C_h control0 s z x).before.overflow = true) :
    let e := nativeCell rate rewards C_star C_h control0 s z x
    e.slowSet = frozenSlowSet p ∧ e.fastArm = frozenFastArm p ∧
      e.proposal = false ∧ e.nextSlowSet = frozenSlowSet p := by
  change (nativeBefore rate rewards C_star C_h control0 s z).overflow = true at hstop
  simp only [nativeCell, appendLogicalCell, hstop, ite_true, Bool.not_true, Bool.false_and, and_self]

private theorem noncallDateCell_stopped (q : Fin p.T) (z : Source) (a : Auxiliary) (U : SlowSet p)
    (e : Cell) (he : noncallDateCell rate rewards C_star C_h q z a U = some e)
    (hstop : e.before.overflow = true) :
    e.slowSet = frozenSlowSet p ∧ e.fastArm = frozenFastArm p ∧
      e.proposal = false ∧ e.nextSlowSet = frozenSlowSet p := by
  rcases noncallDateCell_constructor rate rewards C_star C_h q z a U e he with
    ⟨hz, heq⟩ | ⟨hz, _hen, heq⟩
  · rw [heq] at hstop ⊢
    have h := appendLogicalCell_after_overflow
      (continuingRecord rate rewards C_star C_h q ⟨z, hz⟩)
      (continuingSourceCell rate rewards C_star C_h q ⟨z, hz⟩)
      (continuingBefore rate rewards C_star C_h q ⟨z, hz⟩) a hstop
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
  · rw [heq] at hstop ⊢
    change (collectionBefore rate rewards C_star C_h q ⟨z, hz⟩).overflow = true at hstop
    simp only [laterCollectionCell, hstop, ite_true, Bool.not_true, Bool.and_false, Bool.false_and, and_self]

/-- The prescribed incoming-stopped continuation holds for every generated
cell, including the full pre-root history. Its physical mark is retained by
`calendar_cell_fields`. -/
theorem calendar_cell_stopped (k : ℕ) (hk : t0.val + 1 + k ≤ p.T) (w : Sample k)
    (e : Cell) (he : e ∈ (stored k hk w).2) (hstop : e.before.overflow = true) :
    e.slowSet = frozenSlowSet p ∧ e.fastArm = frozenFastArm p ∧
      e.proposal = false ∧ e.nextSlowSet = frozenSlowSet p ∧
      ∀ j, e.arrivals j = (false, 0) ∧ e.service j = 0 ∧ e.after.registers j = e.before.registers j := by
  have hlogical : e.slowSet = frozenSlowSet p ∧ e.fastArm = frozenFastArm p ∧
      e.proposal = false ∧ e.nextSlowSet = frozenSlowSet p := by
    rcases calendar_mark_origins rate rewards C_star C_h control0 b0 u0 t0 k hk w e he with
      hp | ⟨z, _hz, heq⟩ | ⟨j, _hj, hnative | hnoncall⟩
    · exact firstPast_stopped rate rewards C_star C_h _ _ _ e hp hstop
    · rw [heq] at hstop ⊢
      exact nativeCell_stopped rate rewards C_star C_h control0 _ z _ hstop
    · obtain ⟨z, _hz, _hc, heq⟩ := hnative
      rw [heq] at hstop ⊢
      exact nativeCell_stopped rate rewards C_star C_h control0 _ z _ hstop
    · exact noncallDateCell_stopped rate rewards C_star C_h _ _ _ _ e hnoncall.2 hstop
  obtain ⟨_hp, _hb, _ha, _hi, _hen, _hnum, harr, hservice⟩ :=
    calendar_cell_fields rate rewards C_star C_h control0 b0 u0 t0 k hk w e he
  have hacc (j) : e.arrivals j = (false, 0) := by
    rw [harr]
    exact ite_eq_left hstop
  refine ⟨hlogical.1, hlogical.2.1, hlogical.2.2.1, hlogical.2.2.2, ?_⟩
  intro j
  refine ⟨hacc j, ?_, ?_⟩
  · rw [hservice]
    change RecordedQueueRun.recordService (4 * (Q).n) (e.before.registers j) (e.arrivals j) = 0
    rw [hacc j]
    rfl
  · rw [(calendar_cell_all_arm rate rewards C_star C_h control0 b0 u0 t0 k hk w e he j).2, hacc]
    rfl

/-- Native clear PRE keeps its physical proposal and actual local residual
coordinate, including an UPDATE whose POST first detects overflow. -/
theorem nativeCell_clear_refresh (s : Fin p.T) (z : InvocationSource rate rewards C_star C_h s)
    (x : ContinuousControlSlice.Scalar)
    (hclear : (nativeCell rate rewards C_star C_h control0 s z x).before.overflow = false) :
    let e := nativeCell rate rewards C_star C_h control0 s z x
    let c := nativeSourceCell rate rewards C_star C_h s z
    e.proposal = ReferenceFirstLivePostUpdateProposalLaw.physicalProposalBit rate
      (ReferenceSourceCurrentControlFreshness.u_t p s z.val) ∧
    e.nextSlowSet = if e.proposal then residualDraw rate e.before c.input c.selected.view.payload.anchor
      c.selected.view.payload.anchor_pos x else c.selected.view.payload.slowSet := by
  dsimp only
  constructor
  · rw [nativeCell_proposal rate rewards C_star C_h control0 s z x, hclear]
    rfl
  · change (nativeBefore rate rewards C_star C_h control0 s z).overflow = false at hclear
    simp only [nativeCell, appendLogicalCell, hclear, Bool.false_eq_true, ite_false, Function.update_self]

/-- Collection clear PRE keeps the original proposal and refresh labels and
the actual incoming slow seed, without a POST-clear restriction. -/
theorem laterCollectionCell_clear_refresh (q : Fin p.T) (z : CollectionDateSource rate rewards C_star C_h q)
    (a : Auxiliary) (U : SlowSet p)
    (hclear : (collectionBefore rate rewards C_star C_h q z).overflow = false) :
    let e := laterCollectionCell rate rewards C_star C_h q z U a
    let I := collectionInput rate rewards C_star C_h q z
    let P := (collectionArguments rate rewards C_star C_h q z).1
    e.slowSet = U ∧
    e.proposal = (I.enabled && decide ((a (q, 0)).val < 4 * p.m * rate.eta.val)) ∧
    e.nextSlowSet = if e.proposal then residualDraw rate e.before I P.anchor P.anchor_pos (a (q, 1)) else U := by
  simp only [laterCollectionCell, hclear, Bool.false_eq_true, ite_false, Bool.not_false, Bool.and_true,
    true_and]


/-- Every calendar step's strict physical past agrees with the final source,
whether that step inserted a vector or was a noncall. -/
theorem calendar_step_prefix (k : ℕ) (hk : t0.val + 1 + k ≤ p.T) (w : Sample k)
    (j : ℕ) (hj : j < k) :
    let x : Sample j × AssignmentParameterFibreKernel.AssignmentVector p := ancestor k (j + 1) (by omega) w
    sourcePrefix control0 (t0.val + 1 + j) (current k hk w) =
      sourcePrefix control0 (t0.val + 1 + j) (current j (by omega) x.1) := by
  dsimp only
  let x : Sample j × AssignmentParameterFibreKernel.AssignmentVector p := ancestor k (j + 1) (by omega) w
  have hp := (calendarObservation_ancestor_preserves rate rewards C_star C_h control0 b0 u0 t0 k hk w
    (j + 1) (by omega)).2.1
  have hshort : sourcePrefix control0 (t0.val + 1 + j) (current k hk w) =
      sourcePrefix control0 (t0.val + 1 + j) (current (j + 1) (by omega) (x.1, x.2)) :=
    prefix_shrink control0 _ _ (by omega) _ _ hp
  have hstep : sourcePrefix control0 (t0.val + 1 + j) (current (j + 1) (by omega) (x.1, x.2)) =
      sourcePrefix control0 (t0.val + 1 + j) (current j (by omega) x.1) :=
    (calendarObservation_step_preserves rate rewards C_star C_h control0 b0 u0 t0 j (by omega) x.1 x.2).2
  exact hshort.trans hstep

/-- The call parameters used by an archived step are those of the final
source at that date. No equality of whole original and final sources is used. -/
theorem calendar_step_callAt (k : ℕ) (hk : t0.val + 1 + k ≤ p.T) (w : Sample k)
    (j : ℕ) (hj : j < k) :
    let x : Sample j × AssignmentParameterFibreKernel.AssignmentVector p := ancestor k (j + 1) (by omega) w
    let q : Fin p.T := ⟨t0.val + 1 + j, by omega⟩
    ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h q (current k hk w) =
      ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h q (current j (by omega) x.1) := by
  dsimp only
  rw [ReferenceCalendarCollectionCallControlLaw.callAt_factor rate rewards C_star C_h control0 _ (current k hk w),
    ReferenceCalendarCollectionCallControlLaw.callAt_factor rate rewards C_star C_h control0 _
      (current j (by omega) (ancestor k (j + 1) (by omega) w).1),
    calendar_step_prefix rate rewards C_star C_h control0 b0 u0 t0 k hk w j hj]

/-- The actual full original numerical word on the final current source.
Its launch is produced from that source's actual first invocation. -/
def calendarOriginalWord (k : ℕ) (hk : t0.val + 1 + k ≤ p.T) (w : Sample k) :
    List (RecordedQueueRun.RoundInput p.K) :=
  word (current k hk w) (firstCall_launch rate rewards C_star C_h u0 t0 (current k hk w)
    (calendarCurrentSource_firstCell rate rewards C_star C_h control0 b0 u0 t0 k hk w))

/-- Continuing LIVE updates use the same final-source physical proposal and
original label one. Only incoming overflow can suppress the refresh. -/
theorem continuingLogicalCell_clear_refresh (q : Fin p.T)
    (z : ContinuingLiveSource rate rewards C_star C_h q) (a : Auxiliary)
    (hclear : (continuingBefore rate rewards C_star C_h q z).overflow = false) :
    let e := continuingLogicalCell rate rewards C_star C_h q z a
    let c := continuingSourceCell rate rewards C_star C_h q z
    let r := continuingRecord rate rewards C_star C_h q z
    e.proposal = FollowerCutoffScan.completeRowProposalBit p rate.eta.val r.input.row r.input.time ∧
    e.nextSlowSet = if e.proposal then residualDraw rate e.before c.input c.selected.view.payload.anchor
      c.selected.view.payload.anchor_pos (a (q, 1)) else c.selected.view.payload.slowSet := by
  simp only [continuingLogicalCell, appendLogicalCell, hclear, Bool.not_false, Bool.true_and,
    Bool.false_eq_true, ite_false, continuingRecord_time, and_self]

/-- The first collection's actual scalar constructor uses its original
proposal and refresh labels, and gates solely on incoming overflow. -/
theorem firstCollectionCell_clear_refresh (z : Source) (q : Fin p.T) (r : Record)
    (hr : recordAt q z = some r)
    (hm : r ∈ ReferenceFirstCollectionOneRoundLogicalCell.firstCollection (rate := rate) rewards C_star C_h z)
    (U : SlowSet p) (a : Auxiliary)
    (hclear : (RecordedQueueRun.run Q
      (ReferenceFirstCollectionOneRoundLogicalCell.actualPast rewards C_star C_h z q r hr hm)).overflow = false) :
    let e := ReferenceFirstCollectionOneRoundLogicalCell.cellWithScalar rewards C_star C_h z q r hr hm U
      (ReferenceFirstLiveCalendarMarkedTransition.labelZero a)
      (ReferenceSourceFastScalarDisintegration.sourceFastScalar p q z) (a (q, 1))
    let I := ReferenceFirstCollectionOneRoundLogicalCell.actualInput rewards C_star C_h z q r hr hm
    e.slowSet = U ∧ e.proposal = (I.enabled && decide ((a (q, 0)).val < 4 * p.m * rate.eta.val)) ∧
    e.nextSlowSet = if e.proposal then residualDraw rate e.before I (fun _ => 1) (fun _ => zero_lt_one)
      (a (q, 1)) else U := by
  simp only [ReferenceFirstCollectionOneRoundLogicalCell.cellWithScalar,
    ReferenceFirstCollectionOneRoundLogicalCell.cellWithNext, ReferenceFirstCollectionOneRoundLogicalCell.nextSet,
    ReferenceFirstLiveCalendarMarkedTransition.labelZero, hclear, Bool.not_false, Bool.and_true,
    Bool.false_eq_true, ite_false, true_and]
  exact ⟨rfl, trivial⟩

/-- Simultaneous complete marked characterization of this generated component
at POST `T`, on its original unnormalized raw law. The word, launch, source,
original tape, all archived constructors and clear-call joins are produced
internally. No conditional recorder, FAST, proposal or episode law is asserted. -/
theorem ae_generatedCalendarLaw_terminal_marked_path :
    ∀ᵐ w ∂generatedCalendarLaw rate rewards C_star C_h control0 b0 u0 t0 (Fin.last p.T) (by simpa only [Fin.val_last] using t0.isLt),
      let k := p.T - (t0.val + 1)
      let hk : t0.val + 1 + k ≤ p.T := by dsimp only [k]; omega
      let Z := current k hk w
      let A := (original k w).1.2
      let H := (stored k hk w).2
      let W := calendarOriginalWord rate rewards C_star C_h control0 b0 u0 t0 k hk w
      let root := ancestor k 0 (Nat.zero_le _) w
      let s := (observe 0 (by omega) root).1
      Z ∈ firstCell u0 t0 ∧
      H.Pairwise (fun e f => e.time.val < f.time.val) ∧
      (∀ q : Fin p.T, (∃! e : Cell, e ∈ H ∧ e.time = q) ↔ nominalEnabled rate rewards C_star C_h q Z = true) ∧
      (∀ e ∈ H,
        (∃ r, recordAt e.time Z = some r ∧ e.physical = ReferenceActiveHorizonMeasurability.roundRecordCode r) ∧
        e.before = RecordedQueueRun.run Q (W.take (e.time.val - start Z)) ∧
        e.after = RecordedQueueRun.run Q (W.take (e.time.val + 1 - start Z)) ∧
        ∃ hi : e.time.val - start Z < W.length,
          W[e.time.val - start Z].enabled = true ∧
          e.numerical = ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates W[e.time.val - start Z] ∧
          e.arrivals = RecordedQueueRun.acceptedRecord Q e.before W[e.time.val - start Z] ∧
          e.service = (fun j => RecordedQueueRun.recordService (4 * (Q).n) (e.before.registers j) (e.arrivals j)) ∧
          (∀ j, e.service j ≤ 4 * (Q).n ∧ e.after.registers j =
            QueueReplay.transition (4 * (Q).n) (e.before.registers j) (e.arrivals j)) ∧
          (e.before.overflow = true → e.slowSet = frozenSlowSet p ∧ e.fastArm = frozenFastArm p ∧
            e.proposal = false ∧ e.nextSlowSet = frozenSlowSet p ∧
            ∀ j, e.arrivals j = (false, 0) ∧ e.service j = 0 ∧ e.after.registers j = e.before.registers j) ∧
          ((e ∈ past t0.castSucc (Z, A) ∧
            ((∃ i : Fin (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow rate rewards C_star C_h Z).length,
              e = appendLogicalCell
                ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow rate rewards C_star C_h Z)[i.val])
                (wholeLiveCell rate rewards C_star C_h Z _ (List.getElem_mem i.isLt))
                (RecordedQueueRun.run Q ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h Z).take i.val)) A) ∨
            ∃ (q : Fin p.T) (U : SlowSet p), q.val < t0.val ∧
              (ReferenceFirstCollectionLogicalPrefixExtension.extendedPrefixStateAux rate rewards C_star C_h
                q.val q.isLt.le (Z, A)).1 = some U ∧
              ReferenceFirstCollectionLogicalPrefixExtension.collectionCellAt rate rewards C_star C_h q U (Z, A) = some e)) ∨
          (∃ z : InvocationSource rate rewards C_star C_h s, z.val = Z ∧
            e = nativeCell rate rewards C_star C_h control0 s z (A (s, if b0 then 0 else 1))) ∨
          ∃ (j : ℕ) (hj : j < k),
            let x : Sample j × AssignmentParameterFibreKernel.AssignmentVector p := ancestor k (j + 1) (by omega) w
            let q : Fin p.T := ⟨t0.val + 1 + j, by omega⟩
            (∃ z : InvocationSource rate rewards C_star C_h q, z.val = Z ∧ callFlag j (by omega) x.1 = true ∧
              e = nativeCell rate rewards C_star C_h control0 q z
                (A (q, if (calendarPendingFlags rate rewards C_star C_h control0 b0 u0 t0 j (by omega) x.1).1 then 0 else 1))) ∨
            (callFlag j (by omega) x.1 = false ∧ noncallDateCell rate rewards C_star C_h q Z A
              (stored j (by omega) x.1).1 = some e ∧
              ((∃ hz : Z ∈ ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualDomain rate rewards C_star C_h q,
                e = continuingLogicalCell rate rewards C_star C_h q ⟨Z, hz⟩ A) ∨
              ∃ hz : Z ∈ collectionDateDomain rate rewards C_star C_h q,
                (collectionInput rate rewards C_star C_h q ⟨Z, hz⟩).enabled = true ∧
                e = laterCollectionCell rate rewards C_star C_h q ⟨Z, hz⟩ (stored j (by omega) x.1).1 A)))) ∧
      (((lastNative 0 (by omega) root).before.overflow = false) →
        calendarRootEndpoint rate rewards C_star C_h b0 u0 t0 root = some (lastNative 0 (by omega) root).slowSet) ∧
      ∀ (j : ℕ) (hj : j < k),
        let x : Sample j × AssignmentParameterFibreKernel.AssignmentVector p := ancestor k (j + 1) (by omega) w
        let q : Fin p.T := ⟨t0.val + 1 + j, by omega⟩
        let prev := observe j (by omega) x.1
        (∀ hc : callFlag j (by omega) x.1 = true,
          (calendarPendingFlags rate rewards C_star C_h control0 b0 u0 t0 j (by omega) x.1).2 = true →
          let c := invocation j (by omega) x.1 x.2 hc
          0 < calendarInstallationMass rate rewards C_star C_h control0 b0 u0 t0 j (by omega) x.1 ∧
          ∃ (cutoff : Fin p.T) (theta : AssignmentParameterFibreKernel.Theta p),
            ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h q Z = some (cutoff, theta) ∧
            AssignmentParameterFibreKernel.successfulSlowSet p theta x.2 = some c.slowSet ∧
            (if renewalFlag rate rewards C_star C_h (t := prev.1) q prev.2.val then
              freshEndpoint theta (A (q, 1)) else some (stored j (by omega) x.1).1) = some c.slowSet ∧
            some c.before = prev.2.val.2.2.1 ∧
            stored (j + 1) (by omega) x = (c.nextSlowSet, (stored j (by omega) x.1).2 ++ [c])) ∧
        (callFlag j (by omega) x.1 = false → ∀ e : Cell,
          stepCell j (by omega) x.1 x.2 = some e →
          (calendarPendingFlags rate rewards C_star C_h control0 b0 u0 t0 j (by omega) x.1).2 = true →
          e.slowSet = (stored j (by omega) x.1).1 ∧ some e.before = prev.2.val.2.2.1) := by
  change ∀ᵐ w ∂law (p.T - (t0.val + 1)) (by omega), _
  filter_upwards [ae_calendarLaw_archived_path rate rewards C_star C_h control0 b0 u0 t0
    (p.T - (t0.val + 1)) (by omega)] with w hpath
  dsimp only
  let k := p.T - (t0.val + 1)
  have hk : t0.val + 1 + k ≤ p.T := by dsimp only [k]; omega
  refine ⟨calendarCurrentSource_firstCell rate rewards C_star C_h control0 b0 u0 t0 k hk w,
    (calendarObservation_chronology rate rewards C_star C_h control0 b0 u0 t0 k hk w).1,
    ?_, ?_, hpath.2.2.1, ?_⟩
  · intro q
    exact calendar_enabled_unique rate rewards C_star C_h control0 b0 u0 t0 k hk w q (by have := q.isLt; dsimp only [k]; omega)
  · intro e he
    obtain ⟨hp, hb, ha, hi, hen, hn, harr, hservice⟩ :=
      calendar_cell_fields rate rewards C_star C_h control0 b0 u0 t0 k hk w e he
    refine ⟨hp, hb, ha, hi, hen, hn, harr, hservice,
      calendar_cell_all_arm rate rewards C_star C_h control0 b0 u0 t0 k hk w e he,
      calendar_cell_stopped rate rewards C_star C_h control0 b0 u0 t0 k hk w e he, ?_⟩
    rcases calendar_mark_origins rate rewards C_star C_h control0 b0 u0 t0 k hk w e he with hpre | hroot | hsteps
    · exact Or.inl ⟨hpre, firstPast_constructor rate rewards C_star C_h _ _ _ e hpre⟩
    · exact Or.inr (Or.inl hroot)
    · rcases hsteps with ⟨j, hj, hnative | ⟨hc, hnoncall⟩⟩
      · exact Or.inr (Or.inr ⟨j, hj, Or.inl hnative⟩)
      · exact Or.inr (Or.inr ⟨j, hj, Or.inr ⟨hc, hnoncall,
          noncallDateCell_constructor rate rewards C_star C_h _ _ _ _ e hnoncall⟩⟩)
  · intro j hj
    let x : Sample j × AssignmentParameterFibreKernel.AssignmentVector p := ancestor k (j + 1) (by omega) w
    let q : Fin p.T := ⟨t0.val + 1 + j, by omega⟩
    have hstep := hpath.2.2.2.2.2.2.2 j hj
    constructor
    · intro hc hclear
      obtain ⟨_hnative, hpos, cutoff, theta, hcall, hsample, hjoin, happend, _hprefix, hbefore, _⟩ := hstep.1 hc hclear
      have hA : (original j x.1).1.2 = (original k w).1.2 :=
        congrArg (fun y => y.1.2) (calendarAncestor_original rate rewards C_star C_h b0 u0 t0 k (j + 1) (by omega) w)
      refine ⟨hpos, cutoff, theta, ?_, hsample, ?_, hbefore, happend⟩
      · exact (calendar_step_callAt rate rewards C_star C_h control0 b0 u0 t0 k hk w j hj).trans hcall
      · rw [← hA]
        exact hjoin
    · intro hc e he hclear
      have hfalse : ¬ callFlag j (by omega) x.1 = true := by rw [hc]; exact Bool.false_ne_true
      rw [calendarStepCell, dite_eq_right hfalse] at he
      exact ((hstep.2.1 hc).2.2.2.1 e he).2.2.2 hclear

end Bandits.Support.ReferenceGeneratedCalendarMarkedPath
