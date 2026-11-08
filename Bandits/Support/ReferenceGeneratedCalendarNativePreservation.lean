/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedRankCalendarFoundation
public import Bandits.Support.ReferenceGeneratedNativeInvocationGeometry

import Mathlib.Tactic

/-!
# Native segments of the literal generated calendar

Sources: ZIP4 `06_interruptions.tex:391-426`,
`04_slow_fast_learner.tex:142-215,323-390`, and
`08_main_theorem.tex:78-109`.

The last initializer already stored in the canonical observer supplies the
native segment's PRE list. The original auxiliary array supplies both labels;
the local renewal readout below records which label its UPDATE used. All
numerical readouts refer to the complete CURRENT physical source.

These are deterministic geometry results. Agreement of an arbitrary sampled
assignment vector with the incoming logical endpoint is not a pointwise fact.
No logical history law, physical marginal or manuscript closure is asserted.
-/

@[expose] public section

noncomputable section

open scoped Classical
open Bandits.Support ConstructorDimensions
open ReferenceFirstLiveChronologicalPrefixFoundation
open ReferenceFirstNextInstallationTransitionLaw
open ReferenceFirstNextInstallationCellFactors
open ReferencePostInvocationNoncallGeometry
open ReferencePostInvocationPrefixLocality
open ReferencePostInvocationKilledJointLaw
open ReferenceNextRetainedEndpointFibreLaw
open ReferenceGeneratedInvocationCallSplice
open ReferenceGeneratedRankCalendarFoundation
open ReferenceGeneratedNativeInvocationGeometry
open ReferencePostInvocationGeneratedAlignment
open ReferenceFirstCollectionLogicalNumericalAlignment
open ReferenceFirstCollectionLogicalPrefixExtension (noCallAt extendedPast)
open ReferenceActualCollectionHiddenRefreshPath (actualOriginalWord)
open ReferenceCompletePhysicalHistory (physicalStart completeSuffixRecords)
open ReferenceSourcePrefixHistoryFiltration (sourcePrefix)
open RecordedQueueRun (RunState run)

namespace Bandits.Support.ReferenceGeneratedCalendarNativePreservation

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)

local notation "Cell" => LogicalCell p rate
local notation "Source" => BootstrapPrivateRoundStreams.SourceInput p
local notation "AuxiliaryArray" => ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p
local notation "FullVector" => AssignmentParameterFibreKernel.AssignmentVector p
local notation "TimeControls" => ContinuousLearningRows.TimeControl p
local notation "UniformScalar" => ContinuousControlSlice.Scalar
local notation "NativeSource" => InvocationSource rate rewards C_star C_h
local notation "nativeCellAt" => nativeCell rate rewards C_star C_h
local notation "numericalAt" => prefixNumerical rate rewards C_star C_h
local notation "sourceCall" => ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h
local notation "noncallRun" => noncallCalendar rate rewards C_star C_h
local notation "CallFree" => NoCallBetween rate rewards C_star C_h
local notation "insertVector" => ReferenceFirstCollectionRenewalVectorInsertion.insert
local notation "Q" => ReferenceFirstLaunchNumericalCell.queueParameters rate
local notation "start " z:max => physicalStart rate z rewards C_star C_h

/-- The first producer and arbitrary-rank extractor give the same cell on
the same source. This is independent of assignment-kernel support. -/
theorem nativeCell_eq_first (control0 : TimeControls) (s : Fin p.T)
    (z : FirstInvocationSource rate rewards C_star C_h s) (hz : (sourceCall s z.val).isSome = true)
    (x : UniformScalar) : nativeCellAt control0 s ⟨z.val, hz⟩ x =
      actualFirstCell rate rewards C_star C_h control0 s z x := by
  rfl

variable (control0 : ContinuousLearningRows.TimeControl p) (b0 : Bool) (u0 t0 : Fin p.T)

include control0

local notation "Sample" => CalendarSample rate rewards C_star C_h b0 u0 t0
local notation "original" => calendarOriginalLift rate rewards C_star C_h b0 u0 t0
local notation "observe" => calendarObservation rate rewards C_star C_h control0 b0 u0 t0
local notation "advance" => calendarStep rate rewards C_star C_h control0

/-- Read the renewal bit of the last actual call in this nested sample.
This is a readout of `calendarStep`, not another calendar constructor. In
particular later local renewal bits are distinct from the root branch `b0`. -/
def calendarNativeRenewal : (k : ℕ) → (hk : t0.val + 1 + k ≤ p.T) → Sample k → Bool
  | 0, _, _ => b0
  | k + 1, hk, w =>
      let q : Fin p.T := ⟨t0.val + 1 + k, by omega⟩
      let o : TaggedPrefix rate q.castSucc := observe k (by omega) w.1
      if (sourceCall q o.2.val.1.1.1.2).isSome = true then
        renewalFlag rate rewards C_star C_h (t := o.1) q o.2.val
      else calendarNativeRenewal k (by omega) w.1

local notation "nativeRenewal" => calendarNativeRenewal rate rewards C_star C_h control0 b0 u0 t0

/-- The native source is the actual CURRENT physical source in the observer.
Its sole proof is discharged by the admitted constructor's origin theorem. -/
def calendarNativeSource (k : ℕ) (hk : t0.val + 1 + k ≤ p.T) (w : Sample k) :
    NativeSource (observe k hk w).1 :=
  ⟨(observe k hk w).2.val.1.1.1.2,
    (calendarObservation_origin rate rewards C_star C_h control0 b0 u0 t0 k hk w).2.1⟩

local notation "nativeSource" => calendarNativeSource rate rewards C_star C_h control0 b0 u0 t0

/-- The exact PRE list at the last initializer, already stored by the canonical
observer. Dropping its final native cell does not resimulate any history. -/
def calendarNativePrelist (k : ℕ) (hk : t0.val + 1 + k ≤ p.T) (w : Sample k) : List Cell :=
  (observe k hk w).2.val.1.2.2.dropLast

local notation "prelist" => calendarNativePrelist rate rewards C_star C_h control0 b0 u0 t0

private theorem calendarObservation_native_initial_aux (k : ℕ) (hk : t0.val + 1 + k ≤ p.T)
    (w : Sample k) :
    let o := observe k hk w
    let a := (original k w).1.2
    ∀ hz : (sourceCall o.1 o.2.val.1.1.1.2).isSome = true,
    let c := nativeCellAt control0 o.1 ⟨o.2.val.1.1.1.2, hz⟩
      (a (o.1, if nativeRenewal k hk w then 0 else 1))
    o.2.val.1.2.2 = o.2.val.1.2.2.dropLast ++ [c] ∧
      o.2.val.1.2.1 = usedAuxiliary o.1 a := by
  induction k with
  | zero =>
      change BranchLift rate rewards C_star C_h b0 u0 t0 at w
      dsimp only
      intro hz
      constructor
      · cases b0 <;> change postHistory _ = (postHistory _).dropLast ++ [_]
        all_goals
          simp only [postHistory, List.dropLast_concat]
          rfl
      · cases b0 <;> rfl
  | succ k ih =>
      change Sample k × FullVector at w
      let q : Fin p.T := ⟨t0.val + 1 + k, by omega⟩
      let o : TaggedPrefix rate q.castSucc := observe k (by omega) w.1
      let a := (original k w.1).1.2
      have ho : observe (k + 1) hk w = advance q (o, (a, w.2)) := rfl
      by_cases hc : (o.2, (a, w.2)) ∈ calendarCallEvent rate rewards C_star C_h o.1 q
      · have hb : nativeRenewal (k + 1) hk w =
            renewalFlag rate rewards C_star C_h (t := o.1) q o.2.val := ite_eq_left hc
        dsimp only
        rw [ho, calendarStep, dite_eq_left hc, hb]
        intro hz
        constructor
        · change postHistory _ = (postHistory _).dropLast ++ [_]
          simp only [postHistory, List.dropLast_concat]
          dsimp only [calendarCallTransition, calendarCallPrefix, initialExtension,
            calendarCallInitial, insertedPhysicalSource]
          cases renewalFlag rate rewards C_star C_h (t := o.1) q o.2.val <;> rfl
        · rfl
      · have hb : nativeRenewal (k + 1) hk w = nativeRenewal k (by omega) w.1 := ite_eq_right hc
        dsimp only
        rw [ho, calendarStep, dite_eq_right hc, hb]
        exact ih (by omega) w.1

/-- The stored initializer consists of its exact earlier PRE list and the
native cell on this SAME current source. Its original used labels also survive. -/
theorem calendarObservation_native_initial (k : ℕ) (hk : t0.val + 1 + k ≤ p.T) (w : Sample k) :
    let o := observe k hk w
    let a := (original k w).1.2
    let c := nativeCellAt control0 o.1 (nativeSource k hk w)
      (a (o.1, if nativeRenewal k hk w then 0 else 1))
    o.2.val.1.2.2 = prelist k hk w ++ [c] ∧ o.2.val.1.2.1 = usedAuxiliary o.1 a :=
  calendarObservation_native_initial_aux rate rewards C_star C_h control0 b0 u0 t0 k hk w
    (nativeSource k hk w).property

private theorem calendarObservation_noncall_stored (k : ℕ) (hk : t0.val + 1 + k ≤ p.T)
    (w : Sample k) :
    let o := observe k hk w
    o.2.val.2.2.2 = o.2.val.1.2.2.getLast?.bind fun c =>
      noncallRun o.1 o.2.val.1.1.1.2 (original k w).1.2
        (c.nextSlowSet, o.2.val.1.2.2) (calendarBoundary t0 k hk).val := by
  induction k with
  | zero =>
      change BranchLift rate rewards C_star C_h b0 u0 t0 at w
      cases b0 <;> change _ = (postHistory _).getLast?.bind _
      all_goals
        rw [postHistory_last, Option.bind_some]
        rfl
  | succ k ih =>
      change Sample k × FullVector at w
      let q : Fin p.T := ⟨t0.val + 1 + k, by omega⟩
      let o : TaggedPrefix rate q.castSucc := observe k (by omega) w.1
      let a := (original k w.1).1.2
      have ho : observe (k + 1) hk w = advance q (o, (a, w.2)) := rfl
      dsimp only
      rw [ho]
      by_cases hc : (o.2, (a, w.2)) ∈ calendarCallEvent rate rewards C_star C_h o.1 q
      · rw [calendarStep, dite_eq_left hc]
        change _ = (postHistory _).getLast?.bind _
        rw [postHistory_last, Option.bind_some,
          noncallCalendar_initial rate rewards C_star C_h q _ _ _ _ (by dsimp only [calendarBoundary]; dsimp only [q]; omega)]
        exact (calendarCallPrefix_alignment rate rewards C_star C_h control0 o.1 q
          ⟨(o.2, (a, w.2)), hc⟩).2
      · rw [calendarStep, dite_eq_right hc]
        have hn : noCallAt rate rewards C_star C_h q o.2.val.1.1.1.2 := by
          rw [ReferenceFirstCollectionLogicalPrefixExtension.noCallAt_iff_callAt_none]
          exact Option.not_isSome_iff_eq_none.mp hc
        have hdate := (calendarObservation_origin rate rewards C_star C_h control0 b0 u0 t0 k (by omega) w.1).1
        change o.2.val.2.2.2.map _ = _
        rw [ih (by omega) w.1]
        rw [Option.map_bind]
        apply congrArg (Option.bind o.2.val.1.2.2.getLast?)
        funext c
        change (noncallRun o.1 o.2.val.1.1.1.2 a _ q.val).map _ =
          noncallRun o.1 o.2.val.1.1.1.2 a _ (q.val + 1)
        rw [noncallCalendar]
        change (noncallRun o.1 o.2.val.1.1.1.2 a (c.nextSlowSet, o.2.val.1.2.2) q.val).map _ =
          (noncallRun o.1 o.2.val.1.1.1.2 a (c.nextSlowSet, o.2.val.1.2.2) q.val).bind _
        cases noncallRun o.1 o.2.val.1.1.1.2 a (c.nextSlowSet, o.2.val.1.2.2) q.val with
        | none => rfl
        | some s =>
            simp only [Option.map_some, Option.bind_some]
            rw [dite_eq_left ⟨hdate, q.isLt⟩, ite_eq_left hn]
            exact congrArg some (appendNoncallDate_dateAuxiliary rate rewards C_star C_h q
              o.2.val.1.1.1.2 a s)

/-- The actual surviving PRE value is the literal noncall computation from
the last native initializer, on the same complete current source and tape. -/
theorem calendarObservation_noncall (k : ℕ) (hk : t0.val + 1 + k ≤ p.T) (w : Sample k) :
    let o := observe k hk w
    let a := (original k w).1.2
    let c := nativeCellAt control0 o.1 (nativeSource k hk w)
      (a (o.1, if nativeRenewal k hk w then 0 else 1))
    noncallRun o.1 (nativeSource k hk w).val a
      (c.nextSlowSet, prelist k hk w ++ [c]) (calendarBoundary t0 k hk).val = o.2.val.2.2.2 := by
  have hi := (calendarObservation_native_initial rate rewards C_star C_h control0 b0 u0 t0 k hk w).1
  have hs := calendarObservation_noncall_stored rate rewards C_star C_h control0 b0 u0 t0 k hk w
  dsimp only at hi hs ⊢
  rw [hi, List.getLast?_append, List.getLast?_singleton, Option.some_or, Option.bind_some] at hs
  exact hs.symm

/-- Stored numerical presence and identity are consequences of the native
call on the current source. The complete word includes disabled and stopped
dates, and the boundary may be the horizon. -/
theorem calendarObservation_word (k : ℕ) (hk : t0.val + 1 + k ≤ p.T) (w : Sample k) :
    let o := observe k hk w
    let z := nativeSource k hk w
    let hl := nativeInvocation_launch rate rewards C_star C_h o.1 z
    let W := actualOriginalWord rate rewards C_star C_h z.val hl
    o.2.val.2.2.1 = some (run Q (W.take ((calendarBoundary t0 k hk).val - start z.val))) ∧
      (completeSuffixRecords rate z.val rewards C_star C_h).map
        (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate) = W.map some := by
  dsimp only
  have hstart := (actualRecord_index rate rewards C_star C_h (observe k hk w).1
    (nativeSource k hk w).val _
    (nativeSourceCell_spec rate rewards C_star C_h (observe k hk w).1 (nativeSource k hk w)).1).choose_spec.2.2
  have hdate := (calendarObservation_origin rate rewards C_star C_h control0 b0 u0 t0 k hk w).1
  constructor
  · rw [calendarObservation_numerical]
    exact prefixNumerical_actualWord rate rewards C_star C_h _ _ _ (hstart.trans hdate.le)
  · exact originalWord_record_map rate rewards C_star C_h _ _

/-- The earlier PRE list at this actual call is unchanged by insertion of
the full current vector. Its noncall computation uses the same original tape;
the strict source prefix is exactly preserved. No sampler-support premise is used. -/
theorem calendarObservation_prelist_insert (k : ℕ) (hk : t0.val + 1 + k < p.T) (w : Sample k)
    (vector : FullVector) :
    let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
    let o := observe k hk.le w
    let z := nativeSource k hk.le w
    let a := (original k w).1.2
    let c := nativeCellAt control0 o.1 z (a (o.1, if nativeRenewal k hk.le w then 0 else 1))
    sourcePrefix control0 q.val (insertVector q z.val vector) = sourcePrefix control0 q.val z.val ∧
      noncallRun o.1 (insertVector q z.val vector) a
        (c.nextSlowSet, prelist k hk.le w ++ [c]) q.val = o.2.val.2.2.2 := by
  dsimp only
  constructor
  · exact ReferenceFirstCollectionOldRecorderFoundation.sourcePrefix_replaceCurrent control0
      ⟨t0.val + 1 + k, hk⟩ _ le_rfl _ _
  · rw [noncallCalendar_insert rate rewards C_star C_h control0]
    exact calendarObservation_noncall rate rewards C_star C_h control0 b0 u0 t0 k hk.le w

/-- On the actual continuing-LIVE, PRE-clear event the internally generated
seed agrees with the physical native input. Neither a phase history nor a
matching list, numerical seed or source word is an input. -/
theorem calendarObservation_live_seed (k : ℕ) (hk : t0.val + 1 + k < p.T) (w : Sample k)
    (hlive : (nativeSource k hk.le w).val ∈
      ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualDomain rate rewards C_star C_h
        ⟨t0.val + 1 + k, hk⟩)
    (hclear : preClearFlag rate (t := (observe k hk.le w).1) ⟨t0.val + 1 + k, hk⟩
      (observe k hk.le w).2.val = true) :
    let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
    let o := observe k hk.le w
    let a := (original k w).1.2
    let s := o.2.val.2.2.2.get o.2.property
    s.1 = (continuingSourceCell rate rewards C_star C_h q ⟨(nativeSource k hk.le w).val, hlive⟩).selected.view.payload.slowSet ∧
      noncallDateCell rate rewards C_star C_h q (nativeSource k hk.le w).val a s.1 =
        some (continuingLogicalCell rate rewards C_star C_h q ⟨(nativeSource k hk.le w).val, hlive⟩ a) ∧
      (continuingLogicalCell rate rewards C_star C_h q ⟨(nativeSource k hk.le w).val, hlive⟩ a).slowSet = s.1 ∧
      some (continuingLogicalCell rate rewards C_star C_h q ⟨(nativeSource k hk.le w).val, hlive⟩ a).before = o.2.val.2.2.1 := by
  dsimp only
  let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
  let o : TaggedPrefix rate q.castSucc := observe k hk.le w
  let z := nativeSource k hk.le w
  let a := (original k w).1.2
  let s := o.2.val.2.2.2.get o.2.property
  have hnum := (calendarObservation_word rate rewards C_star C_h control0 b0 u0 t0 k hk.le w).1
  let S := run Q ((actualOriginalWord rate rewards C_star C_h z.val
    (nativeInvocation_launch rate rewards C_star C_h o.1 z)).take (q.val - start z.val))
  have hS : numericalAt q.castSucc z.val = some S :=
    (calendarObservation_numerical rate rewards C_star C_h control0 b0 u0 t0 k hk.le w).symm.trans hnum
  have hclearS : S.overflow = false := by
    change o.2.val.2.2.1.any (fun R => !R.overflow) = true at hclear
    rw [hnum, Option.any_some, Bool.not_eq_true'] at hclear
    exact hclear
  have hs : noncallRun o.1 z.val a
      ((nativeCellAt control0 o.1 z (a (o.1, if nativeRenewal k hk.le w then 0 else 1))).nextSlowSet,
        prelist k hk.le w ++ [nativeCellAt control0 o.1 z (a (o.1, if nativeRenewal k hk.le w then 0 else 1))]) q.val = some s :=
    (calendarObservation_noncall rate rewards C_star C_h control0 b0 u0 t0 k hk.le w).trans
      (Option.some_get o.2.property).symm
  have hseed := nativeInvocation_generated_live_seed rate rewards C_star C_h control0 o.1 q z
    (calendarObservation_origin rate rewards C_star C_h control0 b0 u0 t0 k hk.le w).1 a
    (a (o.1, if nativeRenewal k hk.le w then 0 else 1)) (prelist k hk.le w) s S hs hS hclearS hlive
  refine ⟨hseed, ?_, ?_, ?_⟩
  · rw [noncallDateCell, dite_eq_left hlive]
  · have hb : continuingBefore rate rewards C_star C_h q ⟨z.val, hlive⟩ = S :=
      Option.some.inj ((continuingBefore_spec rate rewards C_star C_h q ⟨z.val, hlive⟩).symm.trans hS)
    change (if (continuingBefore rate rewards C_star C_h q ⟨z.val, hlive⟩).overflow then _ else _) = s.1
    simp only [hb, hclearS, Bool.false_eq_true, ite_false]
    exact hseed.symm
  · exact (continuingBefore_spec rate rewards C_star C_h q ⟨z.val, hlive⟩).symm.trans
      (calendarObservation_numerical rate rewards C_star C_h control0 b0 u0 t0 k hk.le w).symm

private theorem calendarObservation_clear_readout (k : ℕ) (hk : t0.val + 1 + k < p.T) (w : Sample k)
    (hclear : preClearFlag rate (t := (observe k hk.le w).1) ⟨t0.val + 1 + k, hk⟩
      (observe k hk.le w).2.val = true) :
    ∃ r, ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout rate rewards C_star C_h
      (t0.val + 1 + k) (nativeSource k hk.le w).val = some r ∧ r.2.1 = false := by
  let o := observe k hk.le w
  have hnum := calendarObservation_numerical rate rewards C_star C_h control0 b0 u0 t0 k hk.le w
  cases hn : o.2.val.2.2.1 with
  | none =>
      change o.2.val.2.2.1.any (fun S => !S.overflow) = true at hclear
      rw [hn] at hclear
      cases hclear
  | some S =>
      have hov : S.overflow = false := by
        change o.2.val.2.2.1.any (fun R => !R.overflow) = true at hclear
        rw [hn, Option.any_some, Bool.not_eq_true'] at hclear
        exact hclear
      have he : numericalAt (calendarBoundary t0 k hk.le) (nativeSource k hk.le w).val = some S :=
        hnum.symm.trans hn
      refine ⟨ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout S, ?_, hov⟩
      have hm := congrArg (Option.map ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout) he
      simpa only [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout,
        prefixNumerical, Option.map_map, Function.comp_def, Option.map_some, calendarBoundary] using hm

private theorem calendarObservation_retained_call (k : ℕ) (hk : t0.val + 1 + k < p.T) (w : Sample k)
    (hc : (sourceCall ⟨t0.val + 1 + k, hk⟩ (nativeSource k hk.le w).val).isSome = true)
    (hnr : renewalFlag rate rewards C_star C_h (t := (observe k hk.le w).1)
      ⟨t0.val + 1 + k, hk⟩ (observe k hk.le w).2.val = false) :
    ReferenceActualCollectionNonrenewedEndpointFibreJoin.actualNonrenewedCollectionCall rate rewards C_star C_h
      ⟨t0.val + 1 + k, hk⟩ (nativeSource k hk.le w).val := by
  let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
  let z := (nativeSource k hk.le w).val
  obtain ⟨⟨cutoff, theta⟩, hcall⟩ := Option.isSome_iff_exists.mp hc
  obtain ⟨r, hr, hselector⟩ := Option.bind_eq_some_iff.mp hcall
  obtain ⟨payload, ledger, saved, hcoord, _hcutoff, _hparameters⟩ :=
    (ReferenceFirstCollectionSamplerCall.collectionCallAt_spec r cutoff theta).mp hselector
  obtain ⟨i, _hi, hir, _hstart⟩ := actualRecord_index rate rewards C_star C_h q z r hr
  have hmem : r ∈ completeSuffixRecords rate z rewards C_star C_h := by
    rw [← hir]
    exact List.getElem_mem i.isLt
  have ht := (ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields
    rate rewards C_star C_h q z r hr).2.2.1
  have hf := ReferenceFirstCollectionRenewalAuxiliaryLaw.oldFreezeAt?_eq_of_record
    rate rewards C_star C_h q z r hmem ht payload ledger saved hcoord
  have hlt : q.val + 1 < ledger.freezeAt := by
    have hn : ¬ ledger.freezeAt ≤ q.val + 1 := by
      change (ReferenceFirstCollectionRenewalAuxiliaryLaw.oldFreezeAt? rate rewards C_star C_h q z).any
        (fun g => decide (g ≤ q.val + 1)) = false at hnr
      rw [hf, Option.any_some, decide_eq_false_iff_not] at hnr
      exact hnr
    exact lt_of_not_ge hn
  refine ⟨hc, r, hr, ?_⟩
  rw [hcoord, ht]
  exact hlt

open ReferenceActualCollectionHiddenRefreshPath
open ReferencePostInvocationRetainedEndpointRecurrence

/-- Actual generated nonrenewed endpoint recurrence and the exact consumed
addresses. The source, old payload, full word, native rank, surviving PRE list
and local UPDATE orientation are supplied internally from this calendar. -/
theorem calendarObservation_retained_endpoint (k : ℕ) (hk : t0.val + 1 + k < p.T) (w : Sample k)
    (hc : (sourceCall ⟨t0.val + 1 + k, hk⟩ (nativeSource k hk.le w).val).isSome = true)
    (hnr : renewalFlag rate rewards C_star C_h (t := (observe k hk.le w).1)
      ⟨t0.val + 1 + k, hk⟩ (observe k hk.le w).2.val = false)
    (hclear : preClearFlag rate (t := (observe k hk.le w).1) ⟨t0.val + 1 + k, hk⟩
      (observe k hk.le w).2.val = true) :
    let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
    let o := observe k hk.le w
    let z := nativeSource k hk.le w
    let a := (original k w).1.2
    let b := nativeRenewal k hk.le w
    ∃ (e n : ℕ) (cutoff : Fin p.T) (theta : AssignmentParameterFibreKernel.Theta p)
      (hw : z.val ∈ collectionPrefixCell rate rewards C_star C_h e n),
      sourceCall q z.val = some (cutoff, theta) ∧ start z.val + n = q.val ∧
      theta.1 = (RecordedCorrectedWindow.actualPrefixSamplerMass p Q
        (ReferenceActualCollectionNonrenewedEndpointFibreJoin.collectionQueue_sourceCap rate)
        (collectionWord rate rewards C_star C_h e n z.val hw) e n
        (collectionPrefixCell_trigger_positive rate rewards C_star C_h e n z.val hw)
        hw.1 (collectionWord_bound rate rewards C_star C_h e n z.val hw)).weight ∧
      theta.2 = (oldPayload rate rewards C_star C_h e n z.val hw).anchor ∧
      oldPayload rate rewards C_star C_h e n z.val hw = (nativeSourceCell rate rewards C_star C_h o.1 z).selected.view.payload ∧
      o.2.val.2.2.1 = some (collectionState rate rewards C_star C_h e n z.val hw n) ∧
      nativeRank rate rewards C_star C_h q z.val = nativeRank rate rewards C_star C_h o.1 z.val + 1 ∧
      o.1.val ≤ start z.val + e - 1 ∧
      o.2.val.2.2.2.map Prod.fst = some (sampledArrayPath rate rewards C_star C_h e n z.val hw (n - e) le_rfl
        (evaluatorArray b o.1 a) (Fin.last (n - e))) ∧
      Function.Injective (consumedAddress rate rewards C_star C_h e n z.val hw b o.1 (n - e) le_rfl) ∧
      ∀ i, let j := consumedAddress rate rewards C_star C_h e n z.val hw b o.1 (n - e) le_rfl i
        o.1.val < j.1.val ∨ (j.1 = o.1 ∧ j.2 = if b then 0 else 1) := by
  dsimp only
  let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
  let o : TaggedPrefix rate q.castSucc := observe k hk.le w
  let z := nativeSource k hk.le w
  have horigin := calendarObservation_origin rate rewards C_star C_h control0 b0 u0 t0 k hk.le w
  obtain ⟨e, n, cutoff, theta, hw, hcall, hdate, hweight, hanchor, hpay, hnum, htrigger, hpath, hinj, hunused⟩ :=
    native_retained_endpoint rate rewards C_star C_h control0 (nativeRenewal k hk.le w) o.1 q
      horigin.1 z (original k w).1.2 (prelist k hk.le w) horigin.2.2
      (calendarObservation_retained_call rate rewards C_star C_h control0 b0 u0 t0 k hk w hc hnr)
      (calendarObservation_clear_readout rate rewards C_star C_h control0 b0 u0 t0 k hk w hclear)
  refine ⟨e, n, cutoff, theta, hw, hcall, hdate, hweight, hanchor, hpay, ?_, ?_, htrigger, ?_, hinj, hunused⟩
  · exact (calendarObservation_numerical rate rewards C_star C_h control0 b0 u0 t0 k hk.le w).trans hnum
  · exact nativeRank_consecutive rate rewards C_star C_h o.1 q z horigin.1 horigin.2.2
  · have hs := calendarObservation_noncall rate rewards C_star C_h control0 b0 u0 t0 k hk.le w
    change noncallRun o.1 z.val (original k w).1.2 _ q.val = o.2.val.2.2.2 at hs
    rw [hs] at hpath
    exact hpath

omit control0 in
private theorem append_chronology (L : List Cell) (c : Cell) (n : ℕ)
    (hpair : L.Pairwise (fun e f => e.time.val < f.time.val))
    (htime : ∀ e ∈ L, e.time.val < n) (hc : c.time.val = n) :
    (L ++ [c]).Pairwise (fun e f => e.time.val < f.time.val) ∧
      ∀ e ∈ L ++ [c], e.time.val < n + 1 := by
  constructor
  · rw [List.pairwise_append]
    refine ⟨hpair, List.pairwise_singleton _ _, ?_⟩
    intro e he f hf
    rw [List.mem_singleton.mp hf, hc]
    exact htime e he
  · intro e he
    rcases List.mem_append.mp he with he | he
    · exact (htime e he).trans (Nat.lt_succ_self _)
    · rw [List.mem_singleton.mp he, hc]
      exact Nat.lt_succ_self _

private theorem branchInitial_chronology (w : Sample 0) :
    let H := (branchInitial rate rewards C_star C_h control0 b0 u0 t0 w).2.2
    H.Pairwise (fun e f => e.time.val < f.time.val) ∧ ∀ e ∈ H, e.time.val ≤ t0.val := by
  change BranchLift rate rewards C_star C_h b0 u0 t0 at w
  let z := ReferencePostInvocationRetainedEndpointRecurrence.producedSource rate rewards C_star C_h b0 u0 t0 w
  let d := branchTransition rate rewards C_star C_h control0 b0 u0 t0 w
  have hz : z.val ∈ ReferenceFirstCollectionAuxiliarySeeds.actualCollectionCallCell rate rewards C_star C_h u0 t0 := by
    cases b0
    · exact firstCall_insertVector_mem rate rewards C_star C_h u0 t0 w.1.1.val w.1.1.property.1 w.2
    · exact (ReferenceFirstCollectionRenewalVectorInsertion.put rate rewards C_star C_h u0 t0 w.1.1 w.2).property.1
  have hH : (branchInitial rate rewards C_star C_h control0 b0 u0 t0 w).2.2 =
      extendedPast rate rewards C_star C_h t0.castSucc (z.val, w.1.2) ++ [d.2.2.2] := by
    cases b0
    · exact (nonrenewed_initialization rate rewards C_star C_h control0 u0 t0 w).2.1
    · exact (renewed_initialization rate rewards C_star C_h control0 u0 t0 w).2.1
  have hct : d.2.2.2.time = t0 := by
    cases b0
    · exact (nonrenewed_initialization rate rewards C_star C_h control0 u0 t0 w).2.2.2.1
    · exact (renewed_initialization rate rewards C_star C_h control0 u0 t0 w).2.2.2.1
  have hp := firstCall_generatedPast_chronology rate rewards C_star C_h u0 t0 z.val hz w.1.2 t0.castSucc le_rfl
  dsimp only
  rw [hH]
  have h := append_chronology rate _ _ t0.val hp.1 (fun e he => (hp.2.1 e he).2) (congrArg Fin.val hct)
  exact ⟨h.1, fun e he => Nat.le_of_lt_succ (h.2 e he)⟩

private theorem calendarObservation_chronology_aux (k : ℕ) (hk : t0.val + 1 + k ≤ p.T) (w : Sample k) :
    let o := observe k hk w
    ∀ s, o.2.val.2.2.2 = some s →
      s.2.Pairwise (fun e f => e.time.val < f.time.val) ∧
      ∀ e ∈ s.2, e.time.val < (calendarBoundary t0 k hk).val := by
  induction k with
  | zero =>
      change BranchLift rate rewards C_star C_h b0 u0 t0 at w
      dsimp only
      intro s hs
      have hsome : (observe 0 hk w).2.val.2.2.2 = some
          ((branchTransition rate rewards C_star C_h control0 b0 u0 t0 w).2.2.2.nextSlowSet,
            (branchInitial rate rewards C_star C_h control0 b0 u0 t0 w).2.2) := by
        cases b0 <;> change noncallRun t0 _ _ _ (t0.val + 1) = _
        all_goals
          rw [noncallCalendar_initial rate rewards C_star C_h t0 _ _ _ _ le_rfl]
          rfl
      have heq := Option.some.inj (hs.symm.trans hsome)
      rw [heq]
      have h := branchInitial_chronology rate rewards C_star C_h control0 b0 u0 t0 w
      exact ⟨h.1, fun e he => Nat.lt_succ_of_le (h.2 e he)⟩
  | succ k ih =>
      change Sample k × FullVector at w
      let q : Fin p.T := ⟨t0.val + 1 + k, by omega⟩
      let o : TaggedPrefix rate q.castSucc := observe k (by omega) w.1
      let a := (original k w.1).1.2
      let prev := o.2.val.2.2.2.get o.2.property
      have hp : o.2.val.2.2.2 = some prev := (Option.some_get o.2.property).symm
      have hprev := ih (by omega) w.1 prev hp
      have ho : observe (k + 1) hk w = advance q (o, (a, w.2)) := rfl
      dsimp only
      rw [ho]
      intro s hs
      by_cases hc : (o.2, (a, w.2)) ∈ calendarCallEvent rate rewards C_star C_h o.1 q
      · rw [calendarStep, dite_eq_left hc] at hs
        rw [(calendarCallPrefix_alignment rate rewards C_star C_h control0 o.1 q ⟨(o.2, (a, w.2)), hc⟩).2] at hs
        have heq := (Option.some.inj hs).symm
        rw [heq]
        exact append_chronology rate _ _ q.val hprev.1 hprev.2
          (congrArg Fin.val (nativeCell_time rate rewards C_star C_h control0 q
            (calendarCallSource rate rewards C_star C_h control0 o.1 q ⟨(o.2, (a, w.2)), hc⟩) _))
      · rw [calendarStep, dite_eq_right hc] at hs
        change o.2.val.2.2.2.map _ = some s at hs
        rw [hp, Option.map_some] at hs
        have heq := (Option.some.inj hs).symm
        rw [heq, appendNoncallDate_dateAuxiliary]
        unfold appendNoncallDate
        cases hcell : noncallDateCell rate rewards C_star C_h q o.2.val.1.1.1.2 a prev.1 with
        | none => exact ⟨hprev.1, fun e he => (hprev.2 e he).trans (Nat.lt_succ_self _)⟩
        | some c =>
            have hl := nativeInvocation_launch rate rewards C_star C_h o.1
              (nativeSource k (by omega) w.1)
            have ht := (noncallDateCell_actualWord rate rewards C_star C_h q
              o.2.val.1.1.1.2 hl a prev.1 c hcell).1
            exact append_chronology rate _ _ q.val hprev.1 hprev.2 (congrArg Fin.val ht)

/-- All actual generated cells are chronological at every finite boundary,
including `n=T`. Disabled dates create no duplicate timestamp; stopped
enabled cells still retain their actual timestamp. -/
theorem calendarObservation_chronology (k : ℕ) (hk : t0.val + 1 + k ≤ p.T) (w : Sample k) :
    let o := observe k hk w
    let s := o.2.val.2.2.2.get o.2.property
    s.2.Pairwise (fun e f => e.time.val < f.time.val) ∧
      ∀ e ∈ s.2, e.time.val < (calendarBoundary t0 k hk).val :=
  calendarObservation_chronology_aux rate rewards C_star C_h control0 b0 u0 t0 k hk w _
    (Option.some_get _).symm

omit control0 in
private theorem noncallCalendar_prefix (s : Fin p.T) (z : Source) (a : AuxiliaryArray)
    (initial : SlowSet p × List Cell) (n : ℕ) (result : SlowSet p × List Cell)
    (hr : noncallRun s z a initial n = some result) : initial.2 <+: result.2 := by
  induction n generalizing result with
  | zero => cases Option.some.inj hr; exact List.prefix_refl _
  | succ n ih =>
      rw [noncallCalendar] at hr
      cases hp : noncallRun s z a initial n with
      | none => rw [hp, Option.bind_none] at hr; cases hr
      | some prev =>
          rw [hp, Option.bind_some] at hr
          have hprev := ih prev hp
          split at hr
          · split_ifs at hr
            have heq := (Option.some.inj hr).symm
            rw [heq]
            unfold appendNoncallDate
            split
            · exact hprev
            · exact hprev.trans (List.prefix_append _ _)
          · cases Option.some.inj hr
            exact hprev

/-- The SAME earlier PRE list and native call cell remain as an actual
prefix of the generated list. Every earlier PRE timestamp is strictly before
the native origin; no logical-law assertion follows from this identity. -/
theorem calendarObservation_native_prefix (k : ℕ) (hk : t0.val + 1 + k ≤ p.T) (w : Sample k) :
    let o := observe k hk w
    let a := (original k w).1.2
    let c := nativeCellAt control0 o.1 (nativeSource k hk w)
      (a (o.1, if nativeRenewal k hk w then 0 else 1))
    let s := o.2.val.2.2.2.get o.2.property
    (prelist k hk w ++ [c]) <+: s.2 ∧
      ∀ e ∈ prelist k hk w, e.time.val < o.1.val := by
  dsimp only
  have hs := (calendarObservation_noncall rate rewards C_star C_h control0 b0 u0 t0 k hk w).trans
    (Option.some_get (observe k hk w).2.property).symm
  have hp := noncallCalendar_prefix rate rewards C_star C_h _ _ _ _ _ _ hs
  refine ⟨hp, ?_⟩
  have hpair := (calendarObservation_chronology rate rewards C_star C_h control0 b0 u0 t0 k hk w).1.sublist hp.sublist
  rw [List.pairwise_append] at hpair
  intro e he
  have h := hpair.2.2 e he _ (List.mem_singleton_self _)
  rw [nativeCell_time] at h
  exact h

/-- At a literal call step the new native PRE list is exactly the previous
generated PRE list. Insertion preserves its strict source prefix, including
unread coordinates, private arrays and the coordinator index. -/
theorem calendarObservation_call_prelist (k : ℕ) (hk : t0.val + 1 + k < p.T) (w : Sample k)
    (vector : FullVector)
    (hc : (sourceCall ⟨t0.val + 1 + k, hk⟩ (nativeSource k hk.le w).val).isSome = true) :
    let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
    let o := observe k hk.le w
    let next := observe (k + 1) (by omega) (w, vector)
    nativeRenewal (k + 1) (by omega) (w, vector) = renewalFlag rate rewards C_star C_h (t := o.1) q o.2.val ∧
      prelist (k + 1) (by omega) (w, vector) = (o.2.val.2.2.2.get o.2.property).2 ∧
      next.2.val.1.1.1.2 = insertVector q o.2.val.1.1.1.2 vector ∧
      sourcePrefix control0 q.val next.2.val.1.1.1.2 = sourcePrefix control0 q.val o.2.val.1.1.1.2 := by
  dsimp only
  let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
  let o : TaggedPrefix rate q.castSucc := observe k hk.le w
  let a := (original k w).1.2
  have he : (o.2, (a, vector)) ∈ calendarCallEvent rate rewards C_star C_h o.1 q := hc
  have ho : observe (k + 1) (by omega) (w, vector) = advance q (o, (a, vector)) := rfl
  refine ⟨ite_eq_left he, ?_, ?_, ?_⟩
  · unfold calendarNativePrelist
    rw [ho, calendarStep, dite_eq_left he]
    change (postHistory _).dropLast = _
    simp only [postHistory, List.dropLast_concat]
    rfl
  · rw [ho, calendarStep, dite_eq_left he]
    rfl
  · rw [ho, calendarStep, dite_eq_left he]
    exact ReferenceFirstCollectionOldRecorderFoundation.sourcePrefix_replaceCurrent control0 q q.val le_rfl _ _

omit control0 in
private theorem noncallCalendar_processed (s : Fin p.T) (z : Source)
    (hl : ∃ active, ReferenceCorrectedInitializationLaunch.correctedLaunch rate z rewards C_star C_h = some active)
    (hstart : start z ≤ s.val) (a : AuxiliaryArray) (initial : SlowSet p × List Cell)
    (hinit : ∀ c ∈ initial.2, c.time.val ≤ s.val) (n : ℕ) (result : SlowSet p × List Cell)
    (hr : noncallRun s z a initial n = some result) :
    (∀ c ∈ result.2, c.time.val < max (s.val + 1) n) ∧
      ∀ v : Fin p.T, s.val < v.val → v.val < n →
        ((∃ c ∈ result.2, c.time = v) ↔
          ((ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h v z).bind
            (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate)).any RecordedQueueRun.RoundInput.enabled = true) := by
  induction n generalizing result with
  | zero =>
      cases Option.some.inj hr
      refine ⟨fun c hc => by have h := hinit c hc; omega, ?_⟩
      intro v _ hv
      exact (Nat.not_lt_zero _ hv).elim
  | succ n ih =>
      rw [noncallCalendar] at hr
      cases hp : noncallRun s z a initial n with
      | none => rw [hp, Option.bind_none] at hr; cases hr
      | some prev =>
          rw [hp, Option.bind_some] at hr
          obtain ⟨hbound, hdates⟩ := ih prev hp
          split at hr
          next hactive =>
            split_ifs at hr with hnocall
            have heq := (Option.some.inj hr).symm
            rw [heq]
            let q : Fin p.T := ⟨n, hactive.2⟩
            have hpresence := noncallDateCell_presence rate rewards C_star C_h q z
              (hstart.trans_lt hactive.1) hnocall a prev.1
            unfold appendNoncallDate
            cases hcell : noncallDateCell rate rewards C_star C_h q z a prev.1 with
            | none =>
                rw [hcell] at hpresence
                refine ⟨fun c hc => by have h := hbound c hc; omega, ?_⟩
                intro v hsv hv
                by_cases hvn : v.val < n
                · exact hdates v hsv hvn
                · have hvq : v = q := Fin.ext (by dsimp only [q]; omega)
                  subst v
                  constructor
                  · rintro ⟨c, hc, ht⟩
                    have hb := hbound c hc
                    have ht' : c.time.val = n := congrArg Fin.val ht
                    omega
                  · intro hen
                    rw [← hpresence] at hen
                    cases hen
            | some c =>
                rw [hcell] at hpresence
                have htime := (noncallDateCell_actualWord rate rewards C_star C_h q z hl a prev.1 c hcell).1
                have hctime : c.time.val = n := congrArg Fin.val htime
                refine ⟨?_, ?_⟩
                · intro e he
                  rcases List.mem_append.mp he with he | he
                  · have hb := hbound e he; omega
                  · rw [List.mem_singleton.mp he, hctime]
                    omega
                · intro v hsv hv
                  constructor
                  · rintro ⟨e, he, ht⟩
                    rcases List.mem_append.mp he with he | he
                    · have hb := hbound e he
                      have ht' := congrArg Fin.val ht
                      have hvn : v.val < n := by omega
                      exact (hdates v hsv hvn).mp ⟨e, he, ht⟩
                    · have hev := (congrArg LogicalCell.time (List.mem_singleton.mp he)).symm.trans ht
                      have hvq : v = q := hev.symm.trans htime
                      rw [hvq, ← hpresence]
                      rfl
                  · intro hen
                    by_cases hvn : v.val < n
                    · obtain ⟨e, he, ht⟩ := (hdates v hsv hvn).mpr hen
                      exact ⟨e, List.mem_append_left _ he, ht⟩
                    · have hvq : v = q := Fin.ext (by dsimp only [q]; omega)
                      exact ⟨c, List.mem_append_right _ (List.mem_singleton_self _), htime.trans hvq.symm⟩
          · cases Option.some.inj hr
            refine ⟨fun c hc => by have hb := hbound c hc; omega, ?_⟩
            intro v hsv hv
            have hvn : v.val < n := by omega
            exact hdates v hsv hvn

/-- The generated native segment processes exactly the enabled physical
dates. This includes enabled zero arrivals, stopped enabled cells, disabled
gaps and the terminal boundary; it is a timestamp identity, not a law. -/
theorem calendarObservation_processed (k : ℕ) (hk : t0.val + 1 + k ≤ p.T) (w : Sample k) :
    let o := observe k hk w
    let z := nativeSource k hk w
    let s := o.2.val.2.2.2.get o.2.property
    ∀ v : Fin p.T, o.1.val ≤ v.val → v.val < (calendarBoundary t0 k hk).val →
      ((∃ c ∈ s.2, c.time = v) ↔
        ((ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h v z.val).bind
          (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate)).any RecordedQueueRun.RoundInput.enabled = true) := by
  dsimp only
  let o := observe k hk w
  let z := nativeSource k hk w
  let a := (original k w).1.2
  let c := nativeCellAt control0 o.1 z (a (o.1, if nativeRenewal k hk w then 0 else 1))
  let s := o.2.val.2.2.2.get o.2.property
  have hnative := calendarObservation_native_prefix rate rewards C_star C_h control0 b0 u0 t0 k hk w
  have hstart := (actualRecord_index rate rewards C_star C_h o.1 z.val _
    (nativeSourceCell_spec rate rewards C_star C_h o.1 z).1).choose_spec.2.2
  have hinit : ∀ e ∈ prelist k hk w ++ [c], e.time.val ≤ o.1.val := by
    intro e he
    rcases List.mem_append.mp he with he | he
    · exact (hnative.2 e he).le
    · rw [List.mem_singleton.mp he, nativeCell_time]
  have hs := (calendarObservation_noncall rate rewards C_star C_h control0 b0 u0 t0 k hk w).trans
    (Option.some_get o.2.property).symm
  have hdates := (noncallCalendar_processed rate rewards C_star C_h o.1 z.val
    (nativeInvocation_launch rate rewards C_star C_h o.1 z) hstart a _ hinit _ s hs).2
  intro v hsv hv
  by_cases heq : v = o.1
  · subst v
    have hcell := nativeSourceCell_spec rate rewards C_star C_h o.1 z
    have hen : ((ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h o.1 z.val).bind
        (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate)).any RecordedQueueRun.RoundInput.enabled = true := by
      rw [hcell.1, Option.bind_some, ReferenceFirstCollectionCurrentRetainedGate.cell0,
        hcell.2.2, Option.some_or, Option.any_some]
      exact (nativeSourceCell rate rewards C_star C_h o.1 z).enabled
    constructor
    · intro _; exact hen
    · intro _
      exact ⟨c, hnative.1.sublist.subset (List.mem_append_right _ (List.mem_singleton_self _)),
        nativeCell_time rate rewards C_star C_h control0 o.1 z _⟩
  · have hlt : o.1.val < v.val := by
      change o.1.val ≤ v.val at hsv
      have hne : v.val ≠ o.1.val := fun h => heq (Fin.ext h)
      omega
    exact hdates v hlt hv

omit control0 in
private theorem noncallCalendar_cell_origin (s : Fin p.T) (z : Source) (a : AuxiliaryArray)
    (initial : SlowSet p × List Cell) (n : ℕ) (result : SlowSet p × List Cell)
    (hr : noncallRun s z a initial n = some result) (e : Cell) (he : e ∈ result.2) :
    e ∈ initial.2 ∨ ∃ (q : Fin p.T) (U : SlowSet p), s.val < q.val ∧ q.val < n ∧
      noncallDateCell rate rewards C_star C_h q z a U = some e := by
  induction n generalizing result with
  | zero => cases Option.some.inj hr; exact Or.inl he
  | succ n ih =>
      rw [noncallCalendar] at hr
      cases hp : noncallRun s z a initial n with
      | none => rw [hp, Option.bind_none] at hr; cases hr
      | some prev =>
          rw [hp, Option.bind_some] at hr
          have hprev (h : e ∈ prev.2) :
              e ∈ initial.2 ∨ ∃ (q : Fin p.T) (U : SlowSet p), s.val < q.val ∧ q.val < n + 1 ∧
                noncallDateCell rate rewards C_star C_h q z a U = some e := by
            rcases ih prev hp h with h | ⟨q, U, hsq, hqn, hcell⟩
            · exact Or.inl h
            · exact Or.inr ⟨q, U, hsq, hqn.trans (Nat.lt_succ_self _), hcell⟩
          split at hr
          next hactive =>
            split_ifs at hr
            have heq := (Option.some.inj hr).symm
            rw [heq] at he
            unfold appendNoncallDate at he
            split at he
            · exact hprev he
            next c hc =>
              rcases List.mem_append.mp he with he | he
              · exact hprev he
              · rw [List.mem_singleton.mp he]
                exact Or.inr ⟨⟨n, hactive.2⟩, prev.1, hactive.1, Nat.lt_succ_self _, hc⟩
          · cases Option.some.inj hr
            exact hprev he

/-- Every cell in the actual last-native segment has the complete current
source word's numerical input and canonical all-arm update. Earlier PRE cells
are retained literally; this theorem never identifies their logical law with
the sampled vector's law. -/
theorem calendarObservation_segment_cells (k : ℕ) (hk : t0.val + 1 + k ≤ p.T) (w : Sample k) :
    let o := observe k hk w
    let z := nativeSource k hk w
    let W := actualOriginalWord rate rewards C_star C_h z.val
      (nativeInvocation_launch rate rewards C_star C_h o.1 z)
    let s := o.2.val.2.2.2.get o.2.property
    ∀ e ∈ s.2, o.1.val ≤ e.time.val →
      e.before = run Q (W.take (e.time.val - start z.val)) ∧
      e.after = run Q (W.take (e.time.val + 1 - start z.val)) ∧
      ∃ hi : e.time.val - start z.val < W.length,
        W[e.time.val - start z.val].enabled = true ∧
        e.numerical = ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates W[e.time.val - start z.val] ∧
        e.arrivals = RecordedQueueRun.acceptedRecord Q e.before W[e.time.val - start z.val] ∧
        e.service = fun j => RecordedQueueRun.recordService (4 * (Q).n) (e.before.registers j) (e.arrivals j) := by
  dsimp only
  let o := observe k hk w
  let z := nativeSource k hk w
  let hl := nativeInvocation_launch rate rewards C_star C_h o.1 z
  let W := actualOriginalWord rate rewards C_star C_h z.val hl
  let a := (original k w).1.2
  let c := nativeCellAt control0 o.1 z (a (o.1, if nativeRenewal k hk w then 0 else 1))
  let s := o.2.val.2.2.2.get o.2.property
  have hs := (calendarObservation_noncall rate rewards C_star C_h control0 b0 u0 t0 k hk w).trans
    (Option.some_get o.2.property).symm
  intro e he hse
  rcases noncallCalendar_cell_origin rate rewards C_star C_h o.1 z.val a _ _ s hs e he with
    he | ⟨q, U, _hsq, _hqn, hcell⟩
  · rcases List.mem_append.mp he with he | he
    · have hb := (calendarObservation_native_prefix rate rewards C_star C_h control0 b0 u0 t0 k hk w).2 e he
      exact (Nat.not_lt_of_ge hse hb).elim
    · have heq : e = c := List.mem_singleton.mp he
      rw [heq]
      obtain ⟨ht, hb, ha, hi, hn, harr, hservice⟩ := nativeCell_originalWord rate rewards C_star C_h control0 o.1 z
        (a (o.1, if nativeRenewal k hk w then 0 else 1))
      have hen : W[o.1.val - start z.val].enabled = true := by
        have hcn : c.numerical.1 = true := (nativeSourceCell rate rewards C_star C_h o.1 z).enabled
        exact (congrArg Prod.fst hn).symm.trans hcn
      change c.time = o.1 at ht
      change c.before = _ at hb
      change c.after = _ at ha
      change c.numerical = _ at hn
      change c.arrivals = _ at harr
      change c.service = _ at hservice
      rw [ht]
      exact ⟨hb, ha, hi, hen, hn, harr, hservice⟩
  · obtain ⟨ht, hb, ha, r, input, hr, hinput, hen, _hphysical, hn, harr, hservice⟩ :=
      noncallDateCell_actualWord rate rewards C_star C_h q z.val hl a U e hcell
    obtain ⟨i, hi, hir, _hstart⟩ := actualRecord_index rate rewards C_star C_h q z.val r hr
    have hlookup : (completeSuffixRecords rate z.val rewards C_star C_h)[q.val - start z.val]? = some r := by
      rw [← hi, List.getElem?_eq_getElem i.isLt, hir]
    have hidx : q.val - start z.val < W.length := by
      rw [actualOriginalWord_length]
      rw [← hi]
      exact i.isLt
    have hm := congrArg (fun L => L[q.val - start z.val]?)
      (originalWord_record_map rate rewards C_star C_h z.val hl)
    rw [List.getElem?_map, hlookup, Option.map_some, hinput, List.getElem?_map,
      List.getElem?_eq_getElem hidx, Option.map_some] at hm
    have heq : input = W[q.val - start z.val] := Option.some.inj (Option.some.inj hm)
    rw [heq] at hn harr hen
    rw [ht]
    exact ⟨hb, ha, hidx, hen, hn, harr, hservice⟩

/-- A disabled actual noncall advances the boundary while preserving both
the learner seed and list. Its complete numerical readout is still recomputed;
in particular this statement does not replace it by the last cell's POST. -/
theorem calendarObservation_disabled_step (k : ℕ) (hk : t0.val + 1 + k < p.T) (w : Sample k)
    (vector : FullVector)
    (hnocall : sourceCall ⟨t0.val + 1 + k, hk⟩ (nativeSource k hk.le w).val = none)
    (hdisabled : ((ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
      ⟨t0.val + 1 + k, hk⟩ (nativeSource k hk.le w).val).bind
        (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate)).any RecordedQueueRun.RoundInput.enabled = false) :
    let o := observe k hk.le w
    let next := observe (k + 1) (by omega) (w, vector)
    next.1 = o.1 ∧ next.2.val.2.2.2 = o.2.val.2.2.2 ∧
      nativeRenewal (k + 1) (by omega) (w, vector) = nativeRenewal k hk.le w ∧
      prelist (k + 1) (by omega) (w, vector) = prelist k hk.le w := by
  dsimp only
  let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
  let o : TaggedPrefix rate q.castSucc := observe k hk.le w
  let z := nativeSource k hk.le w
  let a := (original k w).1.2
  have hc : noCallAt rate rewards C_star C_h q z.val :=
    (ReferenceFirstCollectionLogicalPrefixExtension.noCallAt_iff_callAt_none rate rewards C_star C_h q z.val).mpr hnocall
  have he : ¬ (o.2, (a, vector)) ∈ calendarCallEvent rate rewards C_star C_h o.1 q := by
    change ¬ (sourceCall q z.val).isSome = true
    rw [hnocall]
    exact Bool.false_ne_true
  have hstart := (actualRecord_index rate rewards C_star C_h o.1 z.val _
    (nativeSourceCell_spec rate rewards C_star C_h o.1 z).1).choose_spec.2.2
  have hdate := (calendarObservation_origin rate rewards C_star C_h control0 b0 u0 t0 k hk.le w).1
  have hnone (U : SlowSet p) : noncallDateCell rate rewards C_star C_h q z.val a U = none := by
    apply Option.not_isSome_iff_eq_none.mp
    rw [noncallDateCell_presence rate rewards C_star C_h q z.val (hstart.trans_lt hdate) hc a U, hdisabled]
    exact Bool.false_ne_true
  have ho : observe (k + 1) (by omega) (w, vector) = advance q (o, (a, vector)) := rfl
  refine ⟨?_, ?_, ite_eq_right he, ?_⟩
  · rw [ho, calendarStep, dite_eq_right he]
  · rw [ho, calendarStep, dite_eq_right he]
    change o.2.val.2.2.2.map _ = o.2.val.2.2.2
    rw [← Option.some_get o.2.property, Option.map_some]
    rw [appendNoncallDate_dateAuxiliary]
    change some (appendNoncallDate rate rewards C_star C_h q z.val a _) = _
    rw [appendNoncallDate, hnone]
  · unfold calendarNativePrelist
    rw [ho, calendarStep, dite_eq_right he]
    rfl

/-- A stopped native call uses the fixed logical continuation and no-op
accepted records, while the literal calendar continues its physical source. -/
theorem calendarObservation_native_stopped (k : ℕ) (hk : t0.val + 1 + k ≤ p.T) (w : Sample k)
    (hstop : (nativeBefore rate rewards C_star C_h control0 (observe k hk w).1 (nativeSource k hk w)).overflow = true) :
    let o := observe k hk w
    let z := nativeSource k hk w
    let a := (original k w).1.2
    let c := nativeCellAt control0 o.1 z (a (o.1, if nativeRenewal k hk w then 0 else 1))
    c.slowSet = frozenSlowSet p ∧ c.fastArm = frozenFastArm p ∧ c.proposal = false ∧
      c.nextSlowSet = frozenSlowSet p ∧
      ∀ j, c.arrivals j = (false, 0) ∧ c.service j = 0 ∧ c.after.registers j = c.before.registers j := by
  dsimp only
  simp only [nativeCell, appendLogicalCell, hstop, Bool.not_true, Bool.false_and, ite_true, true_and]
  intro j
  exact ⟨(RecordedQueueRun.step_after_overflow_preserves Q _ _ hstop j).2,
    by simp only [RecordedQueueRun.acceptedRecord, hstop, ite_true, RecordedQueueRun.recordService,
      Bool.false_eq_true, ite_false],
    (RecordedQueueRun.step_after_overflow_preserves Q _ _ hstop j).1⟩

/-- A native detecting update keeps its proposal and residual refresh. Only
PRE overflow gates these fields; detecting POST overflow cannot suppress them. -/
theorem calendarObservation_native_detecting_update (k : ℕ) (hk : t0.val + 1 + k ≤ p.T) (w : Sample k)
    (hclear : (nativeBefore rate rewards C_star C_h control0 (observe k hk w).1 (nativeSource k hk w)).overflow = false)
    (hdetect : (numericalAt (observe k hk w).1.succ (nativeSource k hk w).val).any
      (fun S => S.overflow) = true) :
    let o := observe k hk w
    let z := nativeSource k hk w
    let a := (original k w).1.2
    let c := nativeCellAt control0 o.1 z (a (o.1, if nativeRenewal k hk w then 0 else 1))
    c.proposal = ReferenceFirstLivePostUpdateProposalLaw.physicalProposalBit rate
      (ReferenceSourceCurrentControlFreshness.u_t p o.1 z.val) ∧
      c.nextSlowSet = (if c.proposal then residualDraw rate c.before
        (nativeSourceCell rate rewards C_star C_h o.1 z).input
        (nativeSourceCell rate rewards C_star C_h o.1 z).selected.view.payload.anchor
        (nativeSourceCell rate rewards C_star C_h o.1 z).selected.view.payload.anchor_pos
        (a (o.1, if nativeRenewal k hk w then 0 else 1))
        else (nativeSourceCell rate rewards C_star C_h o.1 z).selected.view.payload.slowSet) ∧
      (∃ j, 32 * (c.after.registers j).2 > (Q).D) ∧
      ∀ j, c.after.registers j = QueueReplay.transition (4 * (Q).n) (c.before.registers j) (c.arrivals j) := by
  dsimp only
  let o := observe k hk w
  let z := nativeSource k hk w
  let x := (original k w).1.2 (o.1, if nativeRenewal k hk w then 0 else 1)
  have hafter : (nativeCellAt control0 o.1 z x).after.overflow = true := by
    rw [nativeCell_after_prefix rate rewards C_star C_h control0 o.1 z x, Option.any_some] at hdetect
    exact hdetect
  refine ⟨?_, ?_, ?_⟩
  · have hp := nativeCell_proposal rate rewards C_star C_h control0 o.1 z x
    have hc : (nativeCellAt control0 o.1 z x).before.overflow = false := hclear
    simpa only [hc, Bool.not_false, Bool.true_and] using hp
  · dsimp only [nativeCell, appendLogicalCell]
    simp only [hclear, Bool.false_eq_true, ite_false, Function.update_self]
  · exact RecordedQueueRun.step_retains_first_overflow_update Q _ _ hclear hafter

omit control0 in
private theorem numericalCoordinates_injective : Function.Injective
    (ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates (p := p)) := by
  intro c d h
  cases c
  cases d
  simp_all only [ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates, Prod.mk.injEq]

omit control0 in
private theorem appendLogicalCell_code_congr (r s : ReferenceFirstLiveChronologicalPrefixFoundation.Record rate)
    (c : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell r)
    (d : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell s)
    (S : RunState p.K) (a : AuxiliaryArray) (ht : r.input.time = s.input.time)
    (hc : ReferenceActiveHorizonMeasurability.roundRecordCode r = ReferenceActiveHorizonMeasurability.roundRecordCode s) (hi : c.input = d.input)
    (hu : r.input.row.2 r.input.time = s.input.row.2 s.input.time) :
    appendLogicalCell r c S a = appendLogicalCell s d S a := by
  have hv : c.selected.view = d.selected.view := by
    have h := congrArg (fun code : ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate) => code.2.2.1.1) hc
    rw [(ReferenceActiveHorizonMeasurability.roundRecordCode_front r).1, (ReferenceActiveHorizonMeasurability.roundRecordCode_front s).1] at h
    have hr : (ReferenceActivePhysicalStep.dispatch r.input).selection = some c.selected := by
      simpa only [r.output_eq, ReferenceActivePhysicalStep.step, ReferenceActivePhysicalStep.prepare] using c.selection_actual
    have hs : (ReferenceActivePhysicalStep.dispatch s.input).selection = some d.selected := by
      simpa only [s.output_eq, ReferenceActivePhysicalStep.step, ReferenceActivePhysicalStep.prepare] using d.selection_actual
    rw [hr, hs, Option.map_some, Option.map_some] at h
    exact congrArg Prod.fst (Option.some.inj h)
  have hf : (reservedFastArm r c).val = (reservedFastArm s d).val := by
    unfold reservedFastArm
    rcases c with ⟨cs, cm, co, selected, ca, cl, cv, ci, ceq, cen, carm, cquant⟩
    rcases d with ⟨ds, dm, do_, selected', da, dl, dv, di, deq, den, darm, dquant⟩
    rcases selected with ⟨view, started, pending, cutoff, arm, choice⟩
    rcases selected' with ⟨view', started', pending', cutoff', arm', choice'⟩
    dsimp only at hv ⊢
    cases hv
    rw [hu]
  have hp : FollowerCutoffScan.completeRowProposalBit p rate.eta.val r.input.row r.input.time =
      FollowerCutoffScan.completeRowProposalBit p rate.eta.val s.input.row s.input.time := by
    unfold FollowerCutoffScan.completeRowProposalBit CompletePublicTable.completeRowLearning
    rw [hu]
  unfold appendLogicalCell
  dsimp only
  rw [hp]
  simp only [ht, hc, hi, hv, hf]

/-- The entire native cell, including its seed and residual draw, is fixed
by its physical prefix through the invocation date. Raw row-bearing records
are not equated; their actual codes, inputs and current control are compared. -/
theorem nativeCell_sourcePrefix_congr (s : Fin p.T) (z z' : NativeSource s)
    (hpre : sourcePrefix control0 (s.val + 1) z.val = sourcePrefix control0 (s.val + 1) z'.val)
    (x : UniformScalar) : nativeCellAt control0 s z x = nativeCellAt control0 s z' x := by
  let r := nativeRecord rate rewards C_star C_h s z
  let r' := nativeRecord rate rewards C_star C_h s z'
  have hr := nativeSourceCell_spec rate rewards C_star C_h s z
  have hr' := nativeSourceCell_spec rate rewards C_star C_h s z'
  have hobs := actualObservation_sourcePrefix rate rewards C_star C_h control0 (s.val + 1)
    (Nat.succ_le_of_lt s.isLt) s (Nat.lt_succ_self _) z.val
  rw [hpre] at hobs
  have hobs' := hobs.trans (actualObservation_sourcePrefix rate rewards C_star C_h control0 (s.val + 1)
    (Nat.succ_le_of_lt s.isLt) s (Nat.lt_succ_self _) z'.val).symm
  rw [hr.1, hr'.1, Option.map_some, Option.map_some] at hobs'
  have hentry := Option.some.inj hobs'
  have hcode : ReferenceActiveHorizonMeasurability.roundRecordCode r = ReferenceActiveHorizonMeasurability.roundRecordCode r' := congrArg (fun e => e.2.1) hentry
  have hinput : (nativeSourceCell rate rewards C_star C_h s z).input =
      (nativeSourceCell rate rewards C_star C_h s z').input := by
    have he (v : ReferenceFirstLiveChronologicalPrefixFoundation.Record rate) :
        ReferenceCompleteNumericalBranchObservation.leftProjection
          (ReferenceCompleteNumericalBranchObservation.branchReadout rate 0 v) =
        (ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 v).map
          ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates :=
      congrArg Prod.fst (ReferenceCompleteNumericalBranchObservation.branch_readout_projections rate 0 v)
    have hh := congrArg ReferenceCompleteNumericalBranchObservation.leftProjection
      (congrArg (fun e => e.2.2) hentry)
    rw [he, he, hr.2.2, hr'.2.2, Option.map_some, Option.map_some] at hh
    exact numericalCoordinates_injective (Option.some.inj hh)
  have hb : nativeBefore rate rewards C_star C_h control0 s z =
      nativeBefore rate rewards C_star C_h control0 s z' := by
    have he := (prefixNumerical_sourcePrefix rate rewards C_star C_h control0 s.castSucc (s.val + 1) (Nat.le_succ _) z.val).trans
      ((congrArg (numericalAt s.castSucc) hpre).trans
        (prefixNumerical_sourcePrefix rate rewards C_star C_h control0 s.castSucc (s.val + 1) (Nat.le_succ _) z'.val).symm)
    rw [nativeBefore_prefix, nativeBefore_prefix] at he
    exact Option.some.inj he
  have hcontrol : ReferenceSourceCurrentControlFreshness.u_t p s z.val =
      ReferenceSourceCurrentControlFreshness.u_t p s z'.val := by
    have h := congrArg (ReferenceSourceCurrentControlFreshness.u_t p s) hpre
    simpa only [ReferenceSourceCurrentControlFreshness.u_t,
      ReferenceSourcePrefixHistoryFiltration.sourcePrefix_selected,
      ReferenceSourcePrefixHistoryFiltration.sourcePrefix_control, ite_eq_left (Nat.lt_succ_self _)] using h
  have hu : r.input.row.2 r.input.time = r'.input.row.2 r'.input.time :=
    (nativeRecord_control rate rewards C_star C_h s z).trans
      (hcontrol.trans (nativeRecord_control rate rewards C_star C_h s z').symm)
  simp only [nativeCell, hr.2.1, hr'.2.1]
  rw [hb]
  exact appendLogicalCell_code_congr rate r r' _ _ _ _ (hr.2.1.trans hr'.2.1.symm) hcode hinput hu

/-- Strong insertion locality: recompute the OLD native origin on the actual
inserted current source, retaining the SAME internally constructed PRE list.
Its rank, whole native cell and surviving PRE computation are unchanged. -/
theorem calendarObservation_inserted_native_segment (k : ℕ) (hk : t0.val + 1 + k < p.T)
    (w : Sample k) (vector : FullVector) :
    let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
    let o := observe k hk.le w
    let z := nativeSource k hk.le w
    let a := (original k w).1.2
    let x := a (o.1, if nativeRenewal k hk.le w then 0 else 1)
    ∃ z' : NativeSource o.1, z'.val = insertVector q z.val vector ∧
      nativeRank rate rewards C_star C_h o.1 z'.val = nativeRank rate rewards C_star C_h o.1 z.val ∧
      nativeCellAt control0 o.1 z' x = nativeCellAt control0 o.1 z x ∧
      noncallRun o.1 z'.val a ((nativeCellAt control0 o.1 z' x).nextSlowSet,
        prelist k hk.le w ++ [nativeCellAt control0 o.1 z' x]) q.val = o.2.val.2.2.2 := by
  dsimp only
  let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
  let o : TaggedPrefix rate q.castSucc := observe k hk.le w
  let z := nativeSource k hk.le w
  have hdate : o.1.val < q.val :=
    (calendarObservation_origin rate rewards C_star C_h control0 b0 u0 t0 k hk.le w).1
  let z' : NativeSource o.1 := ⟨insertVector q z.val vector, by
    rw [callAt_insert rate rewards C_star C_h control0 q o.1 hdate.le]
    exact z.property⟩
  have hpre : sourcePrefix control0 (o.1.val + 1) z'.val = sourcePrefix control0 (o.1.val + 1) z.val :=
    ReferenceFirstCollectionOldRecorderFoundation.sourcePrefix_replaceCurrent control0 q _ hdate _ _
  have hc := nativeCell_sourcePrefix_congr rate rewards C_star C_h control0 o.1 z' z hpre
    ((original k w).1.2 (o.1, if nativeRenewal k hk.le w then 0 else 1))
  refine ⟨z', rfl, nativeRank_insert rate rewards C_star C_h control0 q o.1 hdate.le z.val vector, hc, ?_⟩
  rw [hc]
  exact (calendarObservation_prelist_insert rate rewards C_star C_h control0 b0 u0 t0 k hk w vector).2

end Bandits.Support.ReferenceGeneratedCalendarNativePreservation
