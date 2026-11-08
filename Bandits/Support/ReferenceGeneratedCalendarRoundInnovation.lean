/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedCalendarPathAgreement
public import Bandits.Support.ReferenceGeneratedCalendarJointRebase

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
# Past/innovation factorization and clear-call recorder/FAST transport

Sources: ZIP4 `06_interruptions.tex:391-426`,
`04_slow_fast_learner.tex:142-215,323-390`, and
`08_main_theorem.tex:78-109`.

The literal past retains the earlier archive, its current slow seed and the
strict physical prefix. Whole-current-control and auxiliary nonuse produce
the joint innovation split. Clear-call tests additionally retain the installed
assignment vector and evaluate recorder/FAST against their correlated native
kernel. All measures retain the original unnormalized first-branch mass.

Freshness below requires `t0 < q` and `t0 + 1 + k ≤ q`; the private
root-factorization helper concerns a later innovation, not the initializer at t0.
The recorder/FAST integral is restricted to actual calls with clear incoming PRE.
Standalone kernel-family measurability, full generated proposal/residual
evaluation, root initialization, and noncall round laws are downstream
obligations. This internal component asserts no manuscript closure.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal Classical
open Bandits.Support ConstructorDimensions
open ReferenceFirstLiveChronologicalPrefixFoundation
open ReferenceFirstNextInstallationTransitionLaw
open ReferencePostInvocationNoncallGeometry
open ReferencePostInvocationPrefixLocality
open ReferencePostInvocationSupportedDisintegration
open ReferencePostInvocationKilledJointLaw
open ReferenceNextRetainedEndpointFibreLaw
open ReferenceGeneratedInvocationCallSplice
open ReferenceGeneratedRankCalendarFoundation
open ReferenceGeneratedCalendarResidualBlock
open ReferenceGeneratedCalendarNativePreservation
open ReferenceGeneratedCalendarEndpointMixture
open ReferenceGeneratedCalendarPathAgreement
open ReferenceGeneratedCalendarJointRebase
open ReferenceFirstNextLiftFutureAuxiliaryPairLaw (auxiliaryPair measurable_auxiliaryPair)
open ReferenceSourcePrefixHistoryFiltration (sourcePrefix)

namespace Bandits.Support.ReferenceGeneratedCalendarRoundInnovation

variable {p : ConstructorDimensions.Parameters}

local notation "Source" => BootstrapPrivateRoundStreams.SourceInput p
local notation "Control" => ContinuousLearningRows.TimeControl p
local notation "Vector" => AssignmentParameterFibreKernel.AssignmentVector p
local notation "Scalar" => ContinuousControlSlice.Scalar
local notation "replace" => ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p

local instance sourceMeasurableSpace : MeasurableSpace Source := by
  change MeasurableSpace (CompletePublicTable.PublishedOutput p ×
    BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance
local instance controlMeasurableSpace : MeasurableSpace Control :=
  ReferencePostInvocationSupportedDisintegration.controlMeasurableSpace
local instance optionMeasurableSpace {X : Type*} [MeasurableSpace X] : MeasurableSpace (Option X) :=
  LaterAssignmentStartMeasurability.optionMeasurableSpace
local instance slowSetMeasurableSpace : MeasurableSpace (SlowSet p) := ⊤
local instance slowSetDiscrete : DiscreteMeasurableSpace (SlowSet p) := ⟨fun _ => trivial⟩

private theorem measurable_sigma_elim {I X : Type*} {B : I → Type*}
    [∀ i, MeasurableSpace (B i)] [MeasurableSpace X]
    (f : Sigma B → X) (hf : ∀ i, Measurable (fun b : B i => f ⟨i, b⟩)) : Measurable f := by
  intro S hS
  exact MeasurableSpace.measurableSet_iInf.mpr (fun i => hf i hS)

variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
  (control0 : ContinuousLearningRows.TimeControl p) (b0 : Bool) (u0 t0 : Fin p.T)

include control0

local notation "Sample" => CalendarSample rate rewards C_star C_h b0 u0 t0
local notation "observe" => calendarObservation rate rewards C_star C_h control0 b0 u0 t0
local notation "original" => calendarOriginalLift rate rewards C_star C_h b0 u0 t0
local notation "law" => calendarLaw rate rewards C_star C_h control0 b0 u0 t0
local notation "current" => calendarCurrentSource rate rewards C_star C_h control0 b0 u0 t0
local notation "stored" => calendarStoredState rate rewards C_star C_h control0 b0 u0 t0
local notation "pending" => calendarPendingFlags rate rewards C_star C_h control0 b0 u0 t0
local notation "callFlag" => calendarCallFlag rate rewards C_star C_h control0 b0 u0 t0
local notation "extension" => calendarExtensionKernel rate rewards C_star C_h control0 b0 u0 t0
local notation "erasePair" => calendarErasePair rate rewards C_star C_h b0 u0 t0
local notation "fillPair" => calendarFillPair rate rewards C_star C_h b0 u0 t0

/-- Explicit full-vector kernel on the actual incoming archive. The
no-call/stopped branches retain the existing vector; active calls use the
prescribed fibre at the same inherited or freshly initialized endpoint. -/
theorem calendarExtensionKernel_readout (k : ℕ) (hk : t0.val + 1 + k < p.T) (w : Sample k) :
    let r : Fin p.T := ⟨t0.val + 1 + k, hk⟩
    extension k (by omega) w =
      match ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h r (current k hk.le w) with
      | none => Measure.dirac (ReferenceFirstCollectionRenewalVectorInsertion.av r (current k hk.le w))
      | some a => if (pending k (by omega) w).2 then
          AssignmentParameterFibreKernel.fibreMeasure p a.2
            (if (pending k (by omega) w).1 then
              freshEndpoint a.2 ((original k w).1.2 (r, 1)) else some (stored k hk.le w).1)
        else Measure.dirac (ReferenceFirstCollectionRenewalVectorInsertion.av r (current k hk.le w)) := by
  dsimp only
  let r : Fin p.T := ⟨t0.val + 1 + k, hk⟩
  let o : TaggedPrefix rate r.castSucc := observe k hk.le w
  change (match installationSelection rate rewards C_star C_h (t := o.1) r
      (o.2.val, auxiliaryPair r (original k w).1.2) with
    | none => Measure.dirac (ReferenceFirstCollectionRenewalVectorInsertion.av r (current k hk.le w))
    | some a => AssignmentParameterFibreKernel.fibreMeasure p a.1 a.2) = _
  unfold installationSelection installationEndpoint endpointChoice retainedEndpoint
  change (match (match ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h r
      (current k hk.le w) with
    | none => none
    | some a => if (pending k (by omega) w).2 then some (a.2,
        endpointChoice ((pending k (by omega) w).1,
          ((a.2, (original k w).1.2 (r, 1)), (observe k hk.le w).2.val.2.2.2.map Prod.fst)))
      else none) with
    | none => Measure.dirac (ReferenceFirstCollectionRenewalVectorInsertion.av r (current k hk.le w))
    | some a => AssignmentParameterFibreKernel.fibreMeasure p a.1 a.2) = _
  rw [← calendarStoredState_spec rate rewards C_star C_h control0 b0 u0 t0 k hk.le w,
    Option.map_some]
  cases hc : ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h
      ⟨t0.val + 1 + k, hk⟩ (current k hk.le w) with
  | none => rfl
  | some a =>
      cases (pending k (by omega) w).2 <;> rfl

/-- The active branch of the literal generated vector kernel. -/
theorem calendarExtensionKernel_onClearCall (k : ℕ) (hk : t0.val + 1 + k < p.T) (w : Sample k)
    (a : Fin p.T × AssignmentParameterFibreKernel.Theta p)
    (hcall : ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h
      ⟨t0.val + 1 + k, hk⟩ (current k hk.le w) = some a)
    (hclear : (pending k (by omega) w).2 = true) :
    extension k (by omega) w = AssignmentParameterFibreKernel.fibreMeasure p a.2
      (if (pending k (by omega) w).1 then
        freshEndpoint a.2 ((original k w).1.2 (⟨t0.val + 1 + k, hk⟩, 1))
      else some (stored k hk.le w).1) := by
  rw [calendarExtensionKernel_readout rate rewards C_star C_h control0 b0 u0 t0 k hk,
    hcall, hclear]
  rfl

section PhysicalNonuse

variable (q : Fin p.T) (htq : t0.val < q.val)

/-- Change only one not-yet-read physical control in the original branch
source. Every earlier inserted vector and every auxiliary coordinate survive. -/
def calendarReplaceControl : (k : ℕ) → Sample k × Control → Sample k
  | 0, wc => ((replaceBranchSource rate rewards C_star C_h control0 b0 u0 t0 q htq
      wc.1.1.1 wc.2, wc.1.1.2), wc.1.2)
  | k + 1, wc => (calendarReplaceControl k (wc.1.1, wc.2), wc.1.2)

local notation "putControl" => calendarReplaceControl rate rewards C_star C_h control0 b0 u0 t0 q htq

theorem measurable_calendarReplaceControl (k : ℕ) : Measurable (putControl k) := by
  induction k with
  | zero =>
      have h : Measurable (fun wc : Sample 0 × Control => replace q wc.1.1.1.val wc.2) :=
        (ReferenceSourcePhysicalFlagConditionalLaw.measurable_replaceSourceControl p q).comp
        ((measurable_subtype_coe.comp measurable_fst.fst.fst).prodMk measurable_snd)
      exact (h.subtype_mk.prodMk measurable_fst.fst.snd).prodMk measurable_fst.snd
  | succ k ih =>
      exact (ih.comp (measurable_fst.fst.prodMk measurable_snd)).prodMk measurable_fst.snd

theorem calendarOriginalLift_replaceControl (k : ℕ) (w : Sample k) (c : Control) :
    original k (putControl k (w, c)) =
      ((replaceBranchSource rate rewards C_star C_h control0 b0 u0 t0 q htq
        (original k w).1.1 c, (original k w).1.2), (original k w).2) := by
  induction k with
  | zero => rfl
  | succ k ih => exact ih w.1

private theorem callAt_replaceControl (r : Fin p.T) (hrq : r.val ≤ q.val) (z : Source) (c : Control) :
    ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h r (replace q z c) =
      ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h r z := by
  rw [ReferenceCalendarCollectionCallControlLaw.callAt_factor rate rewards C_star C_h control0 r,
    ReferenceFirstCollectionOldRecorderFoundation.sourcePrefix_replaceCurrent control0 q r.val hrq,
    ← ReferenceCalendarCollectionCallControlLaw.callAt_factor rate rewards C_star C_h control0 r]

/-- Future raw-control replacement changes exactly the same control in the
CURRENT generated source, after all earlier assignment insertions. -/
theorem calendarCurrentSource_replaceControl (k : ℕ) (hk : t0.val + 1 + k ≤ p.T)
    (hq : t0.val + 1 + k ≤ q.val) (w : Sample k) (c : Control) :
    current k hk (putControl k (w, c)) = replace q (current k hk w) c := by
  induction k with
  | zero =>
      have hs (x : Sample 0) : current 0 hk x =
          ReferenceFirstCollectionRenewalVectorInsertion.insert t0 x.1.1.val x.2 := by
        cases b0
        · rfl
        · exact ReferenceFirstCollectionRenewalVectorInsertion.put_val rate rewards C_star C_h u0 t0
            x.1.1 x.2
      rw [hs, hs]
      exact insert_futureControl t0 q (Fin.ne_of_val_ne (Nat.ne_of_lt htq)) w.1.1.val w.2 c
  | succ k ih =>
      change Sample k × Vector at w
      change current (k + 1) hk (putControl k (w.1, c), w.2) = replace q (current (k + 1) hk w) c
      rw [calendarCurrentSource_succ rate rewards C_star C_h control0 b0 u0 t0 k (by omega),
        calendarCurrentSource_succ rate rewards C_star C_h control0 b0 u0 t0 k (by omega),
        ih (by omega) (by omega)]
      have hf : callFlag k (by omega) (putControl k (w.1, c)) = callFlag k (by omega) w.1 := by
        change (ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h
          ⟨t0.val + 1 + k, by omega⟩ (current k (by omega) (putControl k (w.1, c)))).isSome = _
        rw [ih (by omega) (by omega), callAt_replaceControl rate rewards C_star C_h control0 q
          ⟨t0.val + 1 + k, by omega⟩ (show t0.val + 1 + k ≤ q.val by omega)]
        rfl
      rw [hf]
      cases h : callFlag k (by omega) w.1
      · rfl
      · exact insert_futureControl ⟨t0.val + 1 + k, by omega⟩ q
          (Fin.ne_of_val_ne (show t0.val + 1 + k ≠ q.val by omega))
          (current k (by omega) w.1) w.2 c

/-- The actual selector at an earlier calendar date ignores this fresh whole
control. This is a nonuse theorem, not a supplied history premise. -/
theorem calendarCallFlag_replaceControl (k : ℕ) (hk : t0.val + 1 + k < p.T)
    (hq : t0.val + 1 + k ≤ q.val) (w : Sample k) (c : Control) :
    callFlag k (by omega) (putControl k (w, c)) = callFlag k (by omega) w := by
  change (ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h
    ⟨t0.val + 1 + k, hk⟩ (current k hk.le (putControl k (w, c)))).isSome = _
  rw [calendarCurrentSource_replaceControl rate rewards C_star C_h control0 b0 u0 t0 q htq k hk.le hq,
    callAt_replaceControl rate rewards C_star C_h control0 q ⟨t0.val + 1 + k, hk⟩ hq]
  rfl

private theorem oldFreezeAt_eq_of_prefix_eq (r : Fin p.T) (z z' : Source)
    (hp : sourcePrefix control0 r.val z = sourcePrefix control0 r.val z')
    (hc : (ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h r z).isSome = true) :
    ReferenceFirstCollectionRenewalAuxiliaryLaw.oldFreezeAt? rate rewards C_star C_h r z =
      ReferenceFirstCollectionRenewalAuxiliaryLaw.oldFreezeAt? rate rewards C_star C_h r z' := by
  have he : ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h r z =
      ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h r z' := by
    rw [ReferenceCalendarCollectionCallControlLaw.callAt_factor rate rewards C_star C_h control0 r z,
      hp, ← ReferenceCalendarCollectionCallControlLaw.callAt_factor rate rewards C_star C_h control0 r z']
  obtain ⟨⟨cutoff, theta⟩, hcall⟩ := Option.isSome_iff_exists.mp hc
  have hcall' := he.symm.trans hcall
  change ((ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h r z).bind
    ReferenceFirstCollectionSamplerCall.collectionCallAt) = some (cutoff, theta) at hcall
  change ((ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h r z').bind
    ReferenceFirstCollectionSamplerCall.collectionCallAt) = some (cutoff, theta) at hcall'
  obtain ⟨R, hR, hRc⟩ := Option.bind_eq_some_iff.mp hcall
  obtain ⟨R', hR', _⟩ := Option.bind_eq_some_iff.mp hcall'
  obtain ⟨payload, ledger, saved, hcoord, _, _⟩ :=
    (ReferenceFirstCollectionSamplerCall.collectionCallAt_spec R cutoff theta).mp hRc
  have hin : ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h r z =
      ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h r z' := by
    rw [ReferenceSourcePrefixHistoryFiltration.incoming_factor rate rewards C_star C_h control0 r z,
      hp, ← ReferenceSourcePrefixHistoryFiltration.incoming_factor rate rewards C_star C_h control0 r z']
  have hstate := ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualRecords_state_congr
    rate rewards C_star C_h r z z' R R' hR hR' hin
  obtain ⟨i, hi⟩ := ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualRecord_suffix_index
    rate rewards C_star C_h r z R hR
  obtain ⟨i', hi'⟩ := ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualRecord_suffix_index
    rate rewards C_star C_h r z' R' hR'
  have htime := (ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields
    rate rewards C_star C_h r z R hR).2.2.1
  have htime' := (ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields
    rate rewards C_star C_h r z' R' hR').2.2.1
  rw [ReferenceFirstCollectionRenewalAuxiliaryLaw.oldFreezeAt?_eq_of_record rate rewards C_star C_h
      r z R (hi ▸ List.getElem_mem i.isLt) htime payload ledger saved hcoord,
    ReferenceFirstCollectionRenewalAuxiliaryLaw.oldFreezeAt?_eq_of_record rate rewards C_star C_h
      r z' R' (hi' ▸ List.getElem_mem i'.isLt) htime' payload ledger saved
        ((congrArg ReferenceActivePhysicalStep.State.coordinator hstate).symm.trans hcoord)]

/-- At an actual call the retained/renewed orientation reads the incoming
ledger, before the current physical control is exposed. -/
theorem calendarPendingRenewal_replaceControl (k : ℕ) (hk : t0.val + 1 + k < p.T)
    (hq : t0.val + 1 + k ≤ q.val) (w : Sample k) (c : Control)
    (hc : callFlag k (by omega) w = true) :
    (pending k (by omega) (putControl k (w, c))).1 = (pending k (by omega) w).1 := by
  let r : Fin p.T := ⟨t0.val + 1 + k, hk⟩
  have hp : sourcePrefix control0 r.val (current k hk.le (putControl k (w, c))) =
      sourcePrefix control0 r.val (current k hk.le w) := by
    rw [calendarCurrentSource_replaceControl rate rewards C_star C_h control0 b0 u0 t0 q htq k hk.le hq,
      ReferenceFirstCollectionOldRecorderFoundation.sourcePrefix_replaceCurrent control0 q r.val hq]
  have ho := oldFreezeAt_eq_of_prefix_eq rate rewards C_star C_h control0 r
    (current k hk.le w) (current k hk.le (putControl k (w, c))) hp.symm hc
  change (ReferenceFirstCollectionRenewalAuxiliaryLaw.oldFreezeAt? rate rewards C_star C_h r
    (current k hk.le (putControl k (w, c)))).any _ = _
  rw [← ho]
  rfl

/-- The clear-PRE gate, including a first detecting update, ignores the
current physical control. No condition is placed on numerical POST. -/
theorem calendarPendingClear_replaceControl (k : ℕ) (hk : t0.val + 1 + k < p.T)
    (hq : t0.val + 1 + k ≤ q.val) (w : Sample k) (c : Control) :
    (pending k (by omega) (putControl k (w, c))).2 = (pending k (by omega) w).2 := by
  change (observe k hk.le (putControl k (w, c))).2.val.2.2.1.any _ = _
  change (observe k hk.le (putControl k (w, c))).2.val.2.2.1.any _ =
    (observe k hk.le w).2.val.2.2.1.any _
  rw [calendarObservation_numerical, calendarObservation_numerical]
  change (prefixNumerical rate rewards C_star C_h (calendarBoundary t0 k hk.le)
    (current k hk.le (putControl k (w, c)))).any _ = _
  rw [
    calendarCurrentSource_replaceControl rate rewards C_star C_h control0 b0 u0 t0 q htq k hk.le hq]
  rw [prefixNumerical_sourcePrefix rate rewards C_star C_h control0
      (calendarBoundary t0 k hk.le) (t0.val + 1 + k) le_rfl,
    ReferenceFirstCollectionOldRecorderFoundation.sourcePrefix_replaceCurrent control0 q
      (t0.val + 1 + k) hq,
    ← prefixNumerical_sourcePrefix rate rewards C_star C_h control0
      (calendarBoundary t0 k hk.le) (t0.val + 1 + k) le_rfl]
  rfl

theorem calendarInvocationCell_replaceControl (k : ℕ) (hk : t0.val + 1 + k < p.T)
    (hq : t0.val + 1 + k + 1 ≤ q.val) (w : Sample k) (v : Vector) (c : Control)
    (hc : callFlag k (by omega) w = true) :
    calendarInvocationCell rate rewards C_star C_h control0 b0 u0 t0 k hk
        (putControl k (w, c)) v
        ((calendarCallFlag_replaceControl rate rewards C_star C_h control0 b0 u0 t0 q htq
          k hk (by omega) w c).trans hc) =
      calendarInvocationCell rate rewards C_star C_h control0 b0 u0 t0 k hk w v hc := by
  let r : Fin p.T := ⟨t0.val + 1 + k, hk⟩
  let w' := putControl k (w, c)
  have hc' : callFlag k (by omega) w' = true :=
    (calendarCallFlag_replaceControl rate rewards C_star C_h control0 b0 u0 t0 q htq
      k hk (by omega) w c).trans hc
  let z := calendarInvocationSource rate rewards C_star C_h control0 b0 u0 t0 k hk w v hc
  let z' := calendarInvocationSource rate rewards C_star C_h control0 b0 u0 t0 k hk w' v hc'
  have hz : z'.val = replace q z.val c := by
    change ReferenceFirstCollectionRenewalVectorInsertion.insert r (current k hk.le w') v = _
    rw [calendarCurrentSource_replaceControl rate rewards C_star C_h control0 b0 u0 t0 q htq
      k hk.le (by omega)]
    exact insert_futureControl r q (Fin.ne_of_val_ne (show r.val ≠ q.val by dsimp only [r]; omega))
      (current k hk.le w) v c
  have hp : sourcePrefix control0 (r.val + 1) z'.val = sourcePrefix control0 (r.val + 1) z.val := by
    rw [hz, ReferenceFirstCollectionOldRecorderFoundation.sourcePrefix_replaceCurrent
      control0 q (r.val + 1) hq]
  have hb := calendarPendingRenewal_replaceControl rate rewards C_star C_h control0 b0 u0 t0 q htq
    k hk (by omega) w c hc
  have ha := calendarOriginalLift_replaceControl rate rewards C_star C_h control0 b0 u0 t0 q htq k w c
  have h1 := (calendarInvocationCell_update_readouts rate rewards C_star C_h control0 b0 u0 t0
    k hk w' v hc').1
  have h2 := (calendarInvocationCell_update_readouts rate rewards C_star C_h control0 b0 u0 t0
    k hk w v hc).1
  rw [h1, h2]
  change nativeCell rate rewards C_star C_h control0 r z'
    ((original k w').1.2 (r, if (pending k (by omega) w').1 then 0 else 1)) = _
  rw [ha, hb]
  exact nativeCell_sourcePrefix_congr rate rewards C_star C_h control0 r z' z hp _

/-- The complete archived logical past survives replacement of a fresh
physical control. It includes all preceding recorder/FAST/UPDATE cells. -/
theorem calendarStoredState_replaceControl (k : ℕ) (hk : t0.val + 1 + k ≤ p.T)
    (hq : t0.val + 1 + k ≤ q.val) (w : Sample k) (c : Control) :
    stored k hk (putControl k (w, c)) = stored k hk w := by
  induction k with
  | zero =>
      have hp := branchPast_futureControl rate rewards C_star C_h control0 b0 u0 t0 q htq
        t0.succ (Nat.lt_succ_self _) hq w.1.1 w.1.2 w.2 c
      apply Option.some.inj
      exact (calendarStoredState_spec rate rewards C_star C_h control0 b0 u0 t0 0 hk _).trans
        ((congrArg (fun o => o.2.2.2) hp).trans
          (calendarStoredState_spec rate rewards C_star C_h control0 b0 u0 t0 0 hk w).symm)
  | succ k ih =>
      change Sample k × Vector at w
      have hf := calendarCallFlag_replaceControl rate rewards C_star C_h control0 b0 u0 t0 q htq
        k (by omega) (by omega) w.1 c
      by_cases hc : callFlag k (by omega) w.1 = true
      · have hc' := hf.trans hc
        change stored (k + 1) hk (putControl k (w.1, c), w.2) = _
        rw [(calendarObservation_call_append rate rewards C_star C_h control0 b0 u0 t0
          k (by omega) _ w.2 hc').1,
          (calendarObservation_call_append rate rewards C_star C_h control0 b0 u0 t0
          k (by omega) w.1 w.2 hc).1,
          calendarInvocationCell_replaceControl rate rewards C_star C_h control0 b0 u0 t0 q htq
            k (by omega) hq w.1 w.2 c hc, ih (by omega) (by omega)]
      · have hn : callFlag k (by omega) w.1 = false := Bool.eq_false_iff.mpr hc
        have hn' := hf.trans hn
        change stored (k + 1) hk (putControl k (w.1, c), w.2) = _
        rw [calendarObservation_noncall_step rate rewards C_star C_h control0 b0 u0 t0
          k (by omega) _ w.2 hn',
          calendarObservation_noncall_step rate rewards C_star C_h control0 b0 u0 t0
          k (by omega) w.1 w.2 hn,
          calendarOriginalLift_replaceControl, ih (by omega) (by omega)]
        unfold appendNoncallDate
        have hz := calendarCurrentSource_replaceControl rate rewards C_star C_h control0 b0 u0 t0 q htq
          k (by omega) (by omega : t0.val + 1 + k ≤ q.val) w.1 c
        change (observe k (by omega) (putControl k (w.1, c))).2.val.1.1.1.2 =
          replace q (observe k (by omega) w.1).2.val.1.1.1.2 c at hz
        rw [noncallDateCell_sourcePrefix rate rewards C_star C_h control0 (t0.val + 1 + (k + 1))
          hk ⟨t0.val + 1 + k, by omega⟩ (show t0.val + 1 + k < t0.val + 1 + (k + 1) by omega),
          hz,
          ReferenceFirstCollectionOldRecorderFoundation.sourcePrefix_replaceCurrent control0 q
            (t0.val + 1 + (k + 1)) hq,
          ← noncallDateCell_sourcePrefix rate rewards C_star C_h control0 (t0.val + 1 + (k + 1))
            hk ⟨t0.val + 1 + k, by omega⟩ (show t0.val + 1 + k < t0.val + 1 + (k + 1) by omega)]

omit control0 htq in
private theorem currentControl_replace_other (r : Fin p.T) (hr : r ≠ q) (z : Source) (c : Control) :
    ReferenceSourceCurrentControlFreshness.u_t p r (replace q z c) =
      ReferenceSourceCurrentControlFreshness.u_t p r z := by
  simp only [ReferenceSourceCurrentControlFreshness.u_t,
    ReferenceFixedTimeSourceControlCoupling.replaceSourceControl,
    ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex,
    ActualInitializationPhysicalStep.selectedRowIndex, Function.update_self, Function.update_of_ne hr]

/-- Every preceding calendar insertion kernel ignores the whole fresh
physical control. No generated-history independence is assumed. -/
theorem calendarExtensionKernel_replaceControl (k : ℕ) (hk : t0.val + 1 + k < p.T)
    (hq : t0.val + 1 + k + 1 ≤ q.val) (w : Sample k) (c : Control) :
    extension k (by omega) (putControl k (w, c)) = extension k (by omega) w := by
  rw [calendarExtensionKernel_readout rate rewards C_star C_h control0 b0 u0 t0 k hk,
    calendarExtensionKernel_readout rate rewards C_star C_h control0 b0 u0 t0 k hk,
    calendarCurrentSource_replaceControl rate rewards C_star C_h control0 b0 u0 t0 q htq
      k hk.le (by omega),
    callAt_replaceControl rate rewards C_star C_h control0 q ⟨t0.val + 1 + k, hk⟩
      (show t0.val + 1 + k ≤ q.val by omega)]
  have hav : ReferenceFirstCollectionRenewalVectorInsertion.av ⟨t0.val + 1 + k, hk⟩
      (replace q (current k hk.le w) c) =
      ReferenceFirstCollectionRenewalVectorInsertion.av ⟨t0.val + 1 + k, hk⟩ (current k hk.le w) := by
    exact congrArg (fun u : Control => ContinuousControlSlice.assignmentVector u.1)
      (currentControl_replace_other q ⟨t0.val + 1 + k, hk⟩
        (Fin.ne_of_val_ne (show t0.val + 1 + k ≠ q.val by omega)) _ c)
  rw [hav]
  cases hc : ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h
      ⟨t0.val + 1 + k, hk⟩ (current k hk.le w) with
  | none => rfl
  | some a =>
      have hcall : callFlag k (by omega) w = true := by
        change (ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h
          ⟨t0.val + 1 + k, hk⟩ (current k hk.le w)).isSome = true
        rw [hc]
        rfl
      rw [calendarPendingClear_replaceControl rate rewards C_star C_h control0 b0 u0 t0 q htq
        k hk (by omega),
        calendarPendingRenewal_replaceControl rate rewards C_star C_h control0 b0 u0 t0 q htq
          k hk (by omega) w c hcall,
        calendarStoredState_replaceControl rate rewards C_star C_h control0 b0 u0 t0 q htq
          k hk.le (by omega),
        calendarOriginalLift_replaceControl]

/-- Remove exactly the current whole physical control and its two current
auxiliary scalars in the SAME raw sample. Earlier vectors are retained. -/
def calendarEraseInnovation (k : ℕ) (w : Sample k) : Sample k :=
  putControl k (erasePair q k w, control0)

/-- Original current physical control and both distinct analytical labels. -/
def calendarInnovation (k : ℕ) (w : Sample k) : Innovation p :=
  (ReferenceSourceCurrentControlFreshness.u_t p q (original k w).1.1.val,
    auxiliaryPair q (original k w).1.2)

local notation "eraseInnovation" => calendarEraseInnovation rate rewards C_star C_h control0 b0 u0 t0 q htq
local notation "innovation" => calendarInnovation rate rewards C_star C_h b0 u0 t0 q

theorem measurable_calendarEraseInnovation (k : ℕ) : Measurable (eraseInnovation k) :=
  (measurable_calendarReplaceControl rate rewards C_star C_h control0 b0 u0 t0 q htq k).comp
    ((measurable_calendarErasePair rate rewards C_star C_h b0 u0 t0 q k).prodMk measurable_const)

omit control0 htq in
theorem measurable_calendarInnovation (k : ℕ) : Measurable (innovation k) :=
  ((ReferenceSourceCurrentControlFreshness.measurable_u_t q).comp
    (measurable_subtype_coe.comp
      (measurable_calendarOriginalLift rate rewards C_star C_h b0 u0 t0 k).fst.fst)).prodMk
    ((measurable_auxiliaryPair q).comp
      (measurable_calendarOriginalLift rate rewards C_star C_h b0 u0 t0 k).fst.snd)

omit control0 in
private theorem map_split_of_sum_restore {I B X : Type*} {R : I → Type*}
    [Countable I] [MeasurableSpace B] [MeasurableSpace X] [∀ i, MeasurableSpace (R i)]
    (mu : Measure B) (nu : Measure X) [IsProbabilityMeasure nu]
    (rho : (i : I) → Measure (R i)) [∀ i, IsFiniteMeasure (rho i)]
    (restore : (i : I) → R i × X → B) (hm : ∀ i, Measurable (restore i))
    (hmu : mu = Measure.sum (fun i => ((rho i).prod nu).map (restore i)))
    (erase : B → B) (he : Measurable erase) (read : B → X) (hr : Measurable read) (x0 : X)
    (hs : ∀ i r x, (erase (restore i (r, x)), read (restore i (r, x))) =
      (erase (restore i (r, x0)), x)) :
    mu.map (fun w => (erase w, read w)) = (mu.map erase).prod nu := by
  let base := fun i (r : R i) => erase (restore i (r, x0))
  have hb (i : I) : Measurable (base i) := he.comp ((hm i).comp (measurable_id.prodMk measurable_const))
  let eta := Measure.sum (fun i => (rho i).map (base i))
  have h : mu.map (fun w => (erase w, read w)) = eta.prod nu := by
    rw [hmu, Measure.map_sum (he.prodMk hr).aemeasurable, Measure.prod_sum_left]
    congr 1
    funext i
    rw [Measure.map_map (he.prodMk hr) (hm i)]
    have hf : (fun w => (erase w, read w)) ∘ restore i = Prod.map (base i) id := by
      funext rx
      exact hs i rx.1 rx.2
    rw [hf, ← Measure.map_prod_map _ _ (hb i) measurable_id, Measure.map_id]
  have hfst := congrArg (fun m : Measure (B × X) => m.map Prod.fst) h
  rw [Measure.map_map measurable_fst (he.prodMk hr), Measure.map_fst_prod,
    measure_univ, one_smul] at hfst
  change mu.map erase = eta at hfst
  rw [hfst]
  exact h

omit control0 htq in
private theorem eraseAuxiliaryPair_fill (a : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p)
    (x : Scalar × Scalar) :
    ReferenceFirstNextLiftFutureAuxiliaryPairLaw.eraseAuxiliaryPair q
        (ReferenceFirstNextLiftFutureAuxiliaryPairLaw.fillAuxiliaryPair q a x) =
      ReferenceFirstNextLiftFutureAuxiliaryPairLaw.eraseAuxiliaryPair q a := by
  funext j
  by_cases h0 : j = (q, 0)
  · subst j
    simp only [ReferenceFirstNextLiftFutureAuxiliaryPairLaw.eraseAuxiliaryPair,
      Function.update_of_ne (show (q, (0 : Fin 2)) ≠ (q, (1 : Fin 2)) by simp), Function.update_self]
  by_cases h1 : j = (q, 1)
  · subst j
    simp only [ReferenceFirstNextLiftFutureAuxiliaryPairLaw.eraseAuxiliaryPair, Function.update_self]
  rw [ReferenceFirstNextLiftFutureAuxiliaryPairLaw.eraseAuxiliaryPair_apply_other q _ j h0 h1,
    ReferenceFirstNextLiftFutureAuxiliaryPairLaw.fillAuxiliaryPair_apply_other q a x j h0 h1,
    ReferenceFirstNextLiftFutureAuxiliaryPairLaw.eraseAuxiliaryPair_apply_other q a j h0 h1]

private theorem calendarEraseInnovation_restore (i : Fin (M p))
    (r : RemainderLift rate rewards C_star C_h control0 b0 u0 t0 q i) (x : Innovation p) :
    eraseInnovation 0 (restoreInnovation rate rewards C_star C_h control0 b0 u0 t0 q htq i (r, x)) =
      eraseInnovation 0 (restoreInnovation rate rewards C_star C_h control0 b0 u0 t0 q htq i
        (r, (control0, (ReferenceFirstLiveActualRefreshTestLaw.scalarZero,
          ReferenceFirstLiveActualRefreshTestLaw.scalarZero)))) := by
  have hsource (c : Control) :
      replace q ((ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p i q).symm
        (c, r.1.1.val)) control0 =
      (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p i q).symm
        (control0, r.1.1.val) := by
    have hi := ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_symm_coordinatorIndex
      p i q c r.1.1.val r.1.1.property.1
    have h := ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_replaceSourceControl p i q
      ((ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p i q).symm (c, r.1.1.val)) control0 hi
    rw [(ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p i q).apply_symm_apply] at h
    exact h.symm
  apply Prod.ext
  · apply Prod.ext
    · apply Subtype.ext
      exact (hsource x.1).trans (hsource control0).symm
    · exact (eraseAuxiliaryPair_fill q r.1.2 x.2).trans
        (eraseAuxiliaryPair_fill q r.1.2 _).symm
  · rfl

private theorem calendarLaw_root_innovation_product :
    (law 0 (by omega)).map (fun w => (eraseInnovation 0 w, innovation 0 w)) =
      ((law 0 (by omega)).map (eraseInnovation 0)).prod (innovationLaw (p := p)) := by
  let rho := erasedRemainderLaw rate rewards C_star C_h control0 b0 u0 t0 q htq
  let restore := restoreInnovation rate rewards C_star C_h control0 b0 u0 t0 q htq
  let : (i : Fin (M p)) → MeasurableSpace
      (RemainderLift rate rewards C_star C_h control0 b0 u0 t0 q i) := fun _ => inferInstance
  have hfinite (i : Fin (M p)) : IsFiniteMeasure (rho i) := by
    dsimp only [rho, erasedRemainderLaw]
    infer_instance
  let := hfinite
  apply map_split_of_sum_restore (law 0 (by omega)) (innovationLaw (p := p)) rho restore
    (measurable_restoreInnovation rate rewards C_star C_h control0 b0 u0 t0 q htq)
    (branchLaw_eq_sum_restore_innovation rate rewards C_star C_h control0 b0 u0 t0 q htq)
    (eraseInnovation 0)
    (measurable_calendarEraseInnovation rate rewards C_star C_h control0 b0 u0 t0 q htq 0)
    (innovation 0)
    (measurable_calendarInnovation rate rewards C_star C_h b0 u0 t0 q 0)
    (control0, (ReferenceFirstLiveActualRefreshTestLaw.scalarZero,
      ReferenceFirstLiveActualRefreshTestLaw.scalarZero))
  intro i r x
  apply Prod.ext
  · exact calendarEraseInnovation_restore rate rewards C_star C_h control0 b0 u0 t0 q htq i r x
  · have h := restoreInnovation_coordinates rate rewards C_star C_h control0 b0 u0 t0 q htq i r x
    have hc := congrArg (fun z : Control × Control => z.1) h.1
    exact Prod.ext hc h.2

omit control0 in
private theorem compProd_erased_factorization
    {B X V : Type*} [MeasurableSpace B] [MeasurableSpace X] [MeasurableSpace V]
    (mu : Measure B) [IsFiniteMeasure mu] (nu : Measure X) [IsProbabilityMeasure nu]
    (kernel : ProbabilityTheory.Kernel B V) [ProbabilityTheory.IsMarkovKernel kernel]
    (e : B → B) (he : Measurable e) (x : B → X) (hx : Measurable x)
    (hbase : mu.map (fun w => (e w, x w)) = (mu.map e).prod nu)
    (hnonuse : ∀ w, kernel w = kernel (e w)) :
    (mu.compProd kernel).map (fun w => ((e w.1, w.2), x w.1)) =
      ((mu.compProd kernel).map (fun w => (e w.1, w.2))).prod nu := by
  have hE : Measurable (fun w : B × V => (e w.1, w.2)) := he.prodMap measurable_id
  have hJ : Measurable (fun w : B × V => ((e w.1, w.2), x w.1)) := hE.prodMk (hx.comp measurable_fst)
  have hpush : (mu.compProd kernel).map (fun w => (e w.1, w.2)) = (mu.map e).compProd kernel := by
    ext s hs
    rw [Measure.map_apply hE hs, Measure.compProd_apply (hs.preimage hE), Measure.compProd_apply hs,
      lintegral_map (ProbabilityTheory.Kernel.measurable_kernel_prodMk_left hs) he]
    exact lintegral_congr fun w => congrArg (fun m : Measure V => m (Prod.mk (e w) ⁻¹' s)) (hnonuse w)
  rw [hpush]
  apply Measure.ext_prod
  intro s r hs hr
  let F : B → ℝ≥0∞ := fun w => kernel w (Prod.mk w ⁻¹' s)
  have hF : Measurable F := ProbabilityTheory.Kernel.measurable_kernel_prodMk_left hs
  let f : B × X → ℝ≥0∞ := fun wx => F wx.1 * r.indicator (fun _ => 1) wx.2
  have hf : Measurable f := (hF.comp measurable_fst).mul ((measurable_const.indicator hr).comp measurable_snd)
  rw [Measure.map_apply hJ (hs.prod hr), Measure.compProd_apply ((hs.prod hr).preimage hJ),
    Measure.prod_prod, Measure.compProd_apply hs]
  calc
    _ = ∫⁻ w, f (e w, x w) ∂mu := by
      apply lintegral_congr
      intro w
      change kernel w {v | (e w, v) ∈ s ∧ x w ∈ r} = F (e w) * r.indicator (fun _ => 1) (x w)
      rw [hnonuse w]
      by_cases hw : x w ∈ r <;> simp [F, hw, Set.preimage]
    _ = ∫⁻ wx, f wx ∂mu.map (fun w => (e w, x w)) := (lintegral_map hf (he.prodMk hx)).symm
    _ = ∫⁻ wx, f wx ∂(mu.map e).prod nu := by rw [hbase]
    _ = (∫⁻ w, F w ∂mu.map e) * nu r := by
      rw [lintegral_prod_mul hF.aemeasurable (measurable_const.indicator hr).aemeasurable,
        lintegral_indicator_const hr, one_mul]

/-- Proper generated raw-history/innovation split, proved by nonuse of
every actual preceding insertion kernel. The erased raw history retains
all earlier vectors, the original other coordinates and the correlated tape. -/
theorem calendarLaw_innovation_product (k : ℕ) (hk : t0.val + 1 + k ≤ p.T)
    (hq : t0.val + 1 + k ≤ q.val) :
    (law k hk).map (fun w => (eraseInnovation k w, innovation k w)) =
      ((law k hk).map (eraseInnovation k)).prod (innovationLaw (p := p)) := by
  induction k with
  | zero => exact calendarLaw_root_innovation_product rate rewards C_star C_h control0 b0 u0 t0 q htq
  | succ k ih =>
      exact compProd_erased_factorization (law k (by omega)) (innovationLaw (p := p))
        (extension k hk) (eraseInnovation k)
        (measurable_calendarEraseInnovation rate rewards C_star C_h control0 b0 u0 t0 q htq k)
        (innovation k) (measurable_calendarInnovation rate rewards C_star C_h b0 u0 t0 q k)
        (ih (by omega) (by omega)) (fun w => by
          change extension k hk w = extension k hk (putControl k (erasePair q k w, control0))
          rw [calendarExtensionKernel_replaceControl rate rewards C_star C_h control0 b0 u0 t0 q htq
            k (by omega) (by omega : t0.val + 1 + k + 1 ≤ q.val),
            calendarExtensionKernel_erasePair rate rewards C_star C_h control0 b0 u0 t0 q k hk hq])

/-- Refill exactly the erased innovation block in the same nested sample. -/
def calendarFillInnovation (k : ℕ) (wx : Sample k × Innovation p) : Sample k :=
  putControl k (fillPair q k (wx.1, wx.2.2), wx.2.1)

local notation "fillInnovation" => calendarFillInnovation rate rewards C_star C_h control0 b0 u0 t0 q htq

theorem measurable_calendarFillInnovation (k : ℕ) : Measurable (fillInnovation k) :=
  (measurable_calendarReplaceControl rate rewards C_star C_h control0 b0 u0 t0 q htq k).comp
    (((measurable_calendarFillPair rate rewards C_star C_h b0 u0 t0 q k).comp
      (measurable_fst.prodMk measurable_snd.snd)).prodMk measurable_snd.fst)

theorem calendarFillInnovation_eraseInnovation (k : ℕ) (w : Sample k) :
    fillInnovation k (eraseInnovation k w, innovation k w) = w := by
  induction k with
  | zero =>
      apply Prod.ext
      · apply Prod.ext
        · apply Subtype.ext
          change replace q (replace q w.1.1.val control0)
            (ReferenceSourceCurrentControlFreshness.u_t p q w.1.1.val) = w.1.1.val
          rw [replaceSourceControl_twice]
          exact ReferenceFixedTimeSourceControlCoupling.replaceSourceControl_original p q w.1.1.val
        · exact ReferenceFirstNextLiftFutureAuxiliaryPairLaw.fillAuxiliaryPair_erase_pair q w.1.2
      · rfl
  | succ k ih => exact Prod.ext (ih w.1) rfl

/-- Actual produced measure as a refill of its own erased law. This is not
a new execution and does not assert independence of the un-erased archive. -/
theorem calendarLaw_eq_restoreInnovation (k : ℕ) (hk : t0.val + 1 + k ≤ p.T)
    (hq : t0.val + 1 + k ≤ q.val) :
    law k hk = (((law k hk).map (eraseInnovation k)).prod (innovationLaw (p := p))).map
      (fillInnovation k) := by
  have he := measurable_calendarEraseInnovation rate rewards C_star C_h control0 b0 u0 t0 q htq k
  have hx := measurable_calendarInnovation rate rewards C_star C_h b0 u0 t0 q k
  have hf := measurable_calendarFillInnovation rate rewards C_star C_h control0 b0 u0 t0 q htq k
  have h := congrArg (fun mu : Measure (Sample k × Innovation p) => mu.map (fillInnovation k))
    (calendarLaw_innovation_product rate rewards C_star C_h control0 b0 u0 t0 q htq k hk hq)
  rw [Measure.map_map hf (he.prodMk hx)] at h
  have hid : fillInnovation k ∘ (fun w => (eraseInnovation k w, innovation k w)) = id :=
    funext (calendarFillInnovation_eraseInnovation rate rewards C_star C_h control0 b0 u0 t0 q htq k)
  rwa [hid, Measure.map_id] at h

end PhysicalNonuse

/-- At an active call the fibre kernel also ignores the CURRENT physical
control, before its recorder/FAST/proposal coordinates are exposed. The
existing-vector fallback is absent precisely on this actual source branch. -/
theorem calendarExtensionKernel_active_currentControl (k : ℕ) (hk : t0.val + 1 + k < p.T)
    (w : Sample k) (c : Control) (hc : callFlag k (by omega) w = true)
    (hclear : (pending k (by omega) w).2 = true) :
    let r : Fin p.T := ⟨t0.val + 1 + k, hk⟩
    extension k (by omega)
      (calendarReplaceControl rate rewards C_star C_h control0 b0 u0 t0 r
        (by dsimp only [r]; omega) k (w, c)) =
      extension k (by omega) w := by
  dsimp only
  let r : Fin p.T := ⟨t0.val + 1 + k, hk⟩
  have htr : t0.val < r.val := by dsimp only [r]; omega
  let w' := calendarReplaceControl rate rewards C_star C_h control0 b0 u0 t0 r htr k (w, c)
  change extension k (by omega) w' = extension k (by omega) w
  have hz := calendarCurrentSource_replaceControl rate rewards C_star C_h control0 b0 u0 t0 r htr
    k hk.le le_rfl w c
  have hcl := calendarPendingClear_replaceControl rate rewards C_star C_h control0 b0 u0 t0 r htr
    k hk le_rfl w c
  have hrenew := calendarPendingRenewal_replaceControl rate rewards C_star C_h control0 b0 u0 t0 r htr
    k hk le_rfl w c hc
  have hs := calendarStoredState_replaceControl rate rewards C_star C_h control0 b0 u0 t0 r htr
    k hk.le le_rfl w c
  have ha := calendarOriginalLift_replaceControl rate rewards C_star C_h control0 b0 u0 t0 r htr k w c
  obtain ⟨a, hcall⟩ := Option.isSome_iff_exists.mp hc
  change ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h r (current k hk.le w) =
    some a at hcall
  have hcall' : ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h r
      (current k hk.le w') = some a := by
    rw [hz, callAt_replaceControl rate rewards C_star C_h control0 r r le_rfl, hcall]
  have hclear' : (pending k (by omega) w').2 = true := hcl.trans hclear
  refine (calendarExtensionKernel_onClearCall rate rewards C_star C_h control0 b0 u0 t0
    k hk w' a hcall' hclear').trans ?_
  refine Eq.trans ?_ (calendarExtensionKernel_onClearCall rate rewards C_star C_h control0 b0 u0 t0
    k hk w a hcall hclear).symm
  apply congrArg (AssignmentParameterFibreKernel.fibreMeasure p a.2)
  rw [hrenew, hs, ha]



/-- Strict physical prefix together with the actual current hidden slow seed
and the entire earlier native-cell archive. Numerical PRE and physical incoming
registers are determined by this physical prefix. -/
def calendarRoundPast (k : ℕ) (hk : t0.val + 1 + k ≤ p.T) (w : Sample k) :
    Source × (SlowSet p × List (LogicalCell p rate)) :=
  (sourcePrefix control0 (t0.val + 1 + k) (current k hk w), stored k hk w)

local notation "past" => calendarRoundPast rate rewards C_star C_h control0 b0 u0 t0

omit control0 in
private theorem measurable_of_some {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]
    (f : X → A) (hf : Measurable (fun x => some (f x))) : Measurable f := by
  have he := (comap_measurable (Equiv.optionEquivSumPUnit A)).comp hf
  have hi : MeasurableEmbedding (@Sum.inl A PUnit) :=
    ⟨Sum.inl_injective, measurable_inl, fun _ hs => hs.inl_image⟩
  exact hi.measurable_comp_iff.mp he

theorem measurable_calendarRoundPast (k : ℕ) (hk : t0.val + 1 + k ≤ p.T) :
    Measurable (past k hk) := by
  have hs : Measurable (stored k hk) := by
    apply measurable_of_some
    have hobs : Measurable (fun o : TaggedPrefix rate (calendarBoundary t0 k hk) =>
        some ((o.2.val.2.2.2).get o.2.property)) := by
      apply measurable_sigma_elim
      intro s
      have he : (fun o : PresentPrefix rate s (calendarBoundary t0 k hk) =>
          some (o.val.2.2.2.get o.property)) = fun o => o.val.2.2.2 :=
        funext fun o => Option.some_get _
      rw [he]
      exact measurable_subtype_coe.snd.snd.snd
    exact hobs.comp (measurable_calendarObservation rate rewards C_star C_h control0 b0 u0 t0 k hk)
  exact ((ReferenceSourcePrefixHistoryFiltration.measurable_sourcePrefix control0 _).comp
    (measurable_calendarCurrentSource rate rewards C_star C_h control0 b0 u0 t0 k hk)).prodMk hs

theorem calendarRoundPast_numerical (k : ℕ) (hk : t0.val + 1 + k ≤ p.T) (w : Sample k) :
    prefixNumerical rate rewards C_star C_h (calendarBoundary t0 k hk) (past k hk w).1 =
      (observe k hk w).2.val.2.2.1 := by
  change prefixNumerical rate rewards C_star C_h (calendarBoundary t0 k hk)
    (sourcePrefix control0 (t0.val + 1 + k) (current k hk w)) = _
  rw [← prefixNumerical_sourcePrefix rate rewards C_star C_h control0
    (calendarBoundary t0 k hk) (t0.val + 1 + k) le_rfl]
  exact (calendarObservation_numerical rate rewards C_star C_h control0 b0 u0 t0 k hk w).symm

section RoundPastInnovation

variable (q : Fin p.T) (htq : t0.val < q.val)

local notation "putControl" => calendarReplaceControl rate rewards C_star C_h control0 b0 u0 t0 q htq
local notation "eraseInnovation" => calendarEraseInnovation rate rewards C_star C_h control0 b0 u0 t0 q htq
local notation "innovation" => calendarInnovation rate rewards C_star C_h b0 u0 t0 q
local notation "fillInnovation" => calendarFillInnovation rate rewards C_star C_h control0 b0 u0 t0 q htq

theorem calendarRoundPast_replaceControl (k : ℕ) (hk : t0.val + 1 + k ≤ p.T)
    (hq : t0.val + 1 + k ≤ q.val) (w : Sample k) (c : Control) :
    past k hk (putControl k (w, c)) = past k hk w := by
  unfold calendarRoundPast
  rw [calendarCurrentSource_replaceControl rate rewards C_star C_h control0 b0 u0 t0 q htq k hk hq,
    ReferenceFirstCollectionOldRecorderFoundation.sourcePrefix_replaceCurrent control0 q
      (t0.val + 1 + k) hq,
    calendarStoredState_replaceControl rate rewards C_star C_h control0 b0 u0 t0 q htq k hk hq]

theorem calendarRoundPast_erasePair (k : ℕ) (hk : t0.val + 1 + k ≤ p.T)
    (hq : t0.val + 1 + k ≤ q.val) (w : Sample k) :
    past k hk (erasePair q k w) = past k hk w := by
  have ho := calendarObservation_erasePair rate rewards C_star C_h control0 b0 u0 t0 q k hk hq w
  apply Prod.ext
  · exact congrArg (fun o : TaggedPrefix rate (calendarBoundary t0 k hk) =>
      sourcePrefix control0 (t0.val + 1 + k) o.2.val.1.1.1.2) ho
  · apply Option.some.inj
    exact (calendarStoredState_spec rate rewards C_star C_h control0 b0 u0 t0 k hk _).trans
      ((congrArg (fun o => o.2.val.2.2.2) ho).trans
        (calendarStoredState_spec rate rewards C_star C_h control0 b0 u0 t0 k hk w).symm)

theorem calendarRoundPast_eraseInnovation (k : ℕ) (hk : t0.val + 1 + k ≤ p.T)
    (hq : t0.val + 1 + k ≤ q.val) (w : Sample k) :
    past k hk (eraseInnovation k w) = past k hk w := by
  exact (calendarRoundPast_replaceControl rate rewards C_star C_h control0 b0 u0 t0 q htq k hk hq
    (erasePair q k w) control0).trans
      (calendarRoundPast_erasePair rate rewards C_star C_h control0 b0 u0 t0 q k hk hq w)

include htq in
/-- Current physical control and the original auxiliary pair are fresh
jointly with the actual archived native past. This is derived from literal
raw nonuse, rather than postulated as a filtration property. -/
theorem calendarLaw_roundPast_innovation_product (k : ℕ) (hk : t0.val + 1 + k ≤ p.T)
    (hq : t0.val + 1 + k ≤ q.val) :
    (law k hk).map (fun w => (past k hk w, innovation k w)) =
      ((law k hk).map (past k hk)).prod (innovationLaw (p := p)) := by
  have he := measurable_calendarEraseInnovation rate rewards C_star C_h control0 b0 u0 t0 q htq k
  have hx := measurable_calendarInnovation rate rewards C_star C_h b0 u0 t0 q k
  have hp := measurable_calendarRoundPast rate rewards C_star C_h control0 b0 u0 t0 k hk
  have h := congrArg (fun mu : Measure (Sample k × Innovation p) => mu.map (Prod.map (past k hk) id))
    (calendarLaw_innovation_product rate rewards C_star C_h control0 b0 u0 t0 q htq k hk hq)
  rw [Measure.map_map (hp.prodMap measurable_id) (he.prodMk hx)] at h
  have hleft : (Prod.map (past k hk) id) ∘ (fun w => (eraseInnovation k w, innovation k w)) =
      (fun w => (past k hk w, innovation k w)) := by
    funext w
    exact Prod.ext
      (calendarRoundPast_eraseInnovation rate rewards C_star C_h control0 b0 u0 t0 q htq k hk hq w) rfl
  rw [hleft, ← Measure.map_prod_map _ _ hp measurable_id, Measure.map_id, Measure.map_map hp he] at h
  have hright : past k hk ∘ eraseInnovation k = past k hk :=
    funext (calendarRoundPast_eraseInnovation rate rewards C_star C_h control0 b0 u0 t0 q htq k hk hq)
  rwa [hright] at h

/-- Actual one-date joint integral: first restore the original innovation,
then use the prescribed full-vector fibre kernel on that same refilled tape.
Arbitrary tests may inspect the complete augmented raw sample and hence the
actual current native cell and the un-erased archived PRE/POST observers. -/
theorem calendarLaw_round_innovation_test (k : ℕ) (hk : t0.val + 1 + k < p.T)
    (hq : t0.val + 1 + k ≤ q.val) (F : Sample k × Vector → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ wv, F wv ∂law (k + 1) (by omega)) =
      ∫⁻ w, ∫⁻ x, ∫⁻ v, F (fillInnovation k (w, x), v)
        ∂extension k (by omega) (fillInnovation k (w, x))
        ∂innovationLaw (p := p) ∂(law k hk.le).map (eraseInnovation k) := by
  have hg : Measurable (fun w : Sample k => ∫⁻ v, F (w, v) ∂extension k (by omega) w) :=
    hF.lintegral_kernel_prod_right'
  change (∫⁻ wv, F wv ∂(law k hk.le).compProd (extension k (by omega))) = _
  rw [Measure.lintegral_compProd hF]
  calc
    _ = ∫⁻ w, (∫⁻ v, F (w, v) ∂extension k (by omega) w)
        ∂(((law k hk.le).map (eraseInnovation k)).prod (innovationLaw (p := p))).map
          (fillInnovation k) :=
      congrArg (fun mu : Measure (Sample k) => ∫⁻ w, (∫⁻ v, F (w, v) ∂extension k (by omega) w) ∂mu)
        (calendarLaw_eq_restoreInnovation rate rewards C_star C_h control0 b0 u0 t0 q htq k hk.le hq)
    _ = ∫⁻ wx, (∫⁻ v, F (fillInnovation k wx, v) ∂extension k (by omega) (fillInnovation k wx))
        ∂((law k hk.le).map (eraseInnovation k)).prod (innovationLaw (p := p)) :=
      lintegral_map hg (measurable_calendarFillInnovation rate rewards C_star C_h control0 b0 u0 t0 q htq k)
    _ = _ := lintegral_prod (μ := (law k hk.le).map (eraseInnovation k)) (ν := innovationLaw (p := p)) _ (hg.comp
      (measurable_calendarFillInnovation rate rewards C_star C_h control0 b0 u0 t0 q htq k)).aemeasurable

end RoundPastInnovation


/-- Joint native transition readout with a separately identified legitimate
past. The full un-erased archive remains inside the second component. -/
def calendarRoundJointReadout (k : ℕ) (hk : t0.val + 1 + k < p.T) (wv : Sample k × Vector) :
    (Source × (SlowSet p × List (LogicalCell p rate))) ×
      CalendarJointOutput rate rewards C_star C_h b0 u0 t0 k hk :=
  (past k hk.le wv.1, calendarJointReadout rate rewards C_star C_h control0 b0 u0 t0 k hk wv)

local notation "roundJoint" => calendarRoundJointReadout rate rewards C_star C_h control0 b0 u0 t0

theorem measurable_calendarRoundJointReadout (k : ℕ) (hk : t0.val + 1 + k < p.T) :
    Measurable (roundJoint k hk) :=
  ((measurable_calendarRoundPast rate rewards C_star C_h control0 b0 u0 t0 k hk.le).comp
    measurable_fst).prodMk
      (measurable_calendarJointReadout rate rewards C_star C_h control0 b0 u0 t0 k hk)

section JointRefill

variable (q : Fin p.T) (htq : t0.val < q.val)

local notation "fillInnovation" => calendarFillInnovation rate rewards C_star C_h control0 b0 u0 t0 q htq
local notation "eraseInnovation" => calendarEraseInnovation rate rewards C_star C_h control0 b0 u0 t0 q htq

omit control0 htq in
private theorem calendarErasePair_fillPair (k : ℕ) (w : Sample k) (x : Scalar × Scalar) :
    erasePair q k (fillPair q k (w, x)) = erasePair q k w := by
  induction k with
  | zero => exact congrArg (fun a => ((w.1.1, a), w.2)) (eraseAuxiliaryPair_fill q w.1.2 x)
  | succ k ih => exact Prod.ext (ih w.1) rfl

theorem calendarRoundPast_fillInnovation (k : ℕ) (hk : t0.val + 1 + k ≤ p.T)
    (hq : t0.val + 1 + k ≤ q.val) (wx : Sample k × Innovation p) :
    past k hk (fillInnovation k wx) = past k hk wx.1 := by
  change past k hk (calendarReplaceControl rate rewards C_star C_h control0 b0 u0 t0 q htq k
    (fillPair q k (wx.1, wx.2.2), wx.2.1)) = _
  rw [calendarRoundPast_replaceControl rate rewards C_star C_h control0 b0 u0 t0 q htq k hk hq]
  exact (calendarRoundPast_erasePair rate rewards C_star C_h control0 b0 u0 t0 q k hk hq _).symm.trans
    ((congrArg (past k hk) (calendarErasePair_fillPair rate rewards C_star C_h b0 u0 t0 q k wx.1 wx.2.2)).trans
      (calendarRoundPast_erasePair rate rewards C_star C_h control0 b0 u0 t0 q k hk hq wx.1))

/-- Substantial joint history/native-output cylinder identity. The independent
innovation is integrated only after the actual past; the correlated full raw
sample, archived PRE and actual native POST are regenerated inside the integral. -/
theorem calendarLaw_round_joint_innovation_test (k : ℕ) (hk : t0.val + 1 + k < p.T)
    (hq : t0.val + 1 + k ≤ q.val)
    (F : (Source × (SlowSet p × List (LogicalCell p rate))) ×
      CalendarJointOutput rate rewards C_star C_h b0 u0 t0 k hk → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ wv, F (roundJoint k hk wv) ∂law (k + 1) (by omega)) =
      ∫⁻ w, ∫⁻ x, ∫⁻ v, F (past k hk.le w,
        calendarJointReadout rate rewards C_star C_h control0 b0 u0 t0 k hk (fillInnovation k (w, x), v))
        ∂extension k (by omega) (fillInnovation k (w, x))
        ∂innovationLaw (p := p) ∂(law k hk.le).map (eraseInnovation k) := by
  have hm : Measurable (fun wv : Sample k × Vector => F (roundJoint k hk wv)) :=
    hF.comp (measurable_calendarRoundJointReadout rate rewards C_star C_h control0 b0 u0 t0 k hk)
  refine (calendarLaw_round_innovation_test rate rewards C_star C_h control0 b0 u0 t0 q htq k hk hq _ hm).trans ?_
  apply lintegral_congr
  intro w
  apply lintegral_congr
  intro x
  apply lintegral_congr
  intro v
  unfold calendarRoundJointReadout
  rw [calendarRoundPast_fillInnovation rate rewards C_star C_h control0 b0 u0 t0 q htq k hk.le hq]

/-- The SAME joint integral on the admitted actual correlated splice target.
This identifies the archive inside that target, rather than combining two
separate source and logical marginals. -/
theorem calendarJointSpliceLaw_round_innovation_test (k : ℕ) (hk : t0.val + 1 + k < p.T)
    (hq : t0.val + 1 + k ≤ q.val)
    (F : (Source × (SlowSet p × List (LogicalCell p rate))) ×
      CalendarJointOutput rate rewards C_star C_h b0 u0 t0 k hk → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ j, F (past k hk.le j.1.1, j)
      ∂calendarJointSpliceLaw rate rewards C_star C_h control0 b0 u0 t0 k hk) =
      ∫⁻ w, ∫⁻ x, ∫⁻ v, F (past k hk.le w,
        calendarJointReadout rate rewards C_star C_h control0 b0 u0 t0 k hk (fillInnovation k (w, x), v))
        ∂extension k (by omega) (fillInnovation k (w, x))
        ∂innovationLaw (p := p) ∂(law k hk.le).map (eraseInnovation k) := by
  have htest : Measurable (fun j : CalendarJointOutput rate rewards C_star C_h b0 u0 t0 k hk =>
      F (past k hk.le j.1.1, j)) := hF.comp
    (((measurable_calendarRoundPast rate rewards C_star C_h control0 b0 u0 t0 k hk.le).comp
      measurable_fst.fst).prodMk measurable_id)
  rw [← calendarLaw_joint_test rate rewards C_star C_h control0 b0 u0 t0 k hk _ htest]
  exact calendarLaw_round_joint_innovation_test rate rewards C_star C_h control0 b0 u0 t0 q htq k hk hq F hF

end JointRefill

/-- Numerical and physical readouts of an actual generated invocation. The
input is produced by the SAME source's actual record and `cell0`, with its
whole reward row, nominal enablement and actual frozen recording rates. All
arms use `acceptedRecord`; POST overflow does not remove the first update. -/
theorem calendarInvocationCell_actualInput (k : ℕ) (hk : t0.val + 1 + k < p.T)
    (w : Sample k) (v : Vector) (hc : callFlag k (by omega) w = true) :
    let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
    let z := calendarInvocationSource rate rewards C_star C_h control0 b0 u0 t0 k hk w v hc
    let c := calendarInvocationCell rate rewards C_star C_h control0 b0 u0 t0 k hk w v hc
    let payload := (nativeSourceCell rate rewards C_star C_h q z).selected.view.payload
    ∃ input : RecordedQueueRun.RoundInput p.K,
      (ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h q z.val).bind
        (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate) = some input ∧
      input.enabled = true ∧
      input.reward = (fun j => ((rewards q j).val : ℝ) / (D p : ℝ)) ∧
      input.rate = payload.rate ∧
      c.numerical = (input.enabled, (input.recordedArm, (input.reward, input.rate))) ∧
      some c.before = (observe k hk.le w).2.val.2.2.1 ∧
      c.after = RecordedQueueRun.step (ReferenceFirstLaunchNumericalCell.queueParameters rate) c.before input ∧
      c.arrivals = RecordedQueueRun.acceptedRecord
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) c.before input ∧
      c.service = (fun j => RecordedQueueRun.recordService
        (4 * (ReferenceFirstLaunchNumericalCell.queueParameters rate).n)
        (c.before.registers j) (c.arrivals j)) := by
  dsimp only
  let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
  let z := calendarInvocationSource rate rewards C_star C_h control0 b0 u0 t0 k hk w v hc
  let s := nativeSourceCell rate rewards C_star C_h q z
  let c := calendarInvocationCell rate rewards C_star C_h control0 b0 u0 t0 k hk w v hc
  have hs := nativeSourceCell_spec rate rewards C_star C_h q z
  have hf := ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields
    rate rewards C_star C_h q z.val (nativeRecord rate rewards C_star C_h q z) hs.1
  have hcell := (calendarInvocationCell_update_readouts rate rewards C_star C_h control0 b0 u0 t0
    k hk w v hc).1
  refine ⟨s.input, ?_, s.enabled, ?_, ?_, ?_,
    calendarInvocationCell_before rate rewards C_star C_h control0 b0 u0 t0 k hk w v hc, ?_, ?_, ?_⟩
  · rw [hs.1, Option.bind_some]
    change (ReferenceLaterLiveNumericalReadout.laterLiveReadout 0
      (nativeRecord rate rewards C_star C_h q z)).or _ = _
    rw [hs.2.2, Option.some_or]
  · rw [s.input_eq]
    change (fun j => (((nativeRecord rate rewards C_star C_h q z).input.rewards
      (nativeRecord rate rewards C_star C_h q z).input.time j).val : ℝ) / (D p : ℝ)) = _
    rw [hf.2.2.1, hf.2.2.2]
  · rw [s.input_eq]
    rfl
  · rw [hcell]
    rfl
  · rw [hcell]
    rfl
  · rw [hcell]
    rfl
  · rw [hcell]
    rfl

/-- Change only the local UPDATE refresh label: renewed calls use zero,
retained calls use one. The original root branch bit is not read here. -/
def calendarWithUpdateScalar (k : ℕ) (hk : t0.val + 1 + k < p.T) (wx : Sample k × Scalar) : Sample k :=
  calendarWithAuxiliary rate rewards C_star C_h b0 u0 t0 k
    (wx.1, Function.update (original k wx.1).1.2
      (⟨t0.val + 1 + k, hk⟩, if (pending k (by omega) wx.1).1 then 0 else 1) wx.2)

local notation "withUpdate" => calendarWithUpdateScalar rate rewards C_star C_h control0 b0 u0 t0

theorem calendarObservation_withUpdateScalar (k : ℕ) (hk : t0.val + 1 + k < p.T)
    (w : Sample k) (x : Scalar) : observe k hk.le (withUpdate k hk (w, x)) = observe k hk.le w := by
  apply calendarObservation_withAuxiliary_prefix rate rewards C_star C_h control0 b0 u0 t0 k hk.le
  intro j hj
  apply Function.update_of_ne
  intro he
  have hv := congrArg (fun i : Fin p.T × Fin 2 => i.1.val) he
  change j.1.val = t0.val + 1 + k at hv
  omega

theorem measurable_calendarWithUpdateScalar (k : ℕ) (hk : t0.val + 1 + k < p.T) :
    Measurable (withUpdate k hk) := by
  classical
  have ha := (measurable_calendarOriginalLift rate rewards C_star C_h b0 u0 t0 k).fst.snd.comp
    (measurable_fst : Measurable (Prod.fst : Sample k × Scalar → Sample k))
  have hb := (measurable_calendarPendingFlags rate rewards C_star C_h control0 b0 u0 t0 k (by omega)).fst.comp
    (measurable_fst : Measurable (Prod.fst : Sample k × Scalar → Sample k))
  have hm : Measurable (fun wx : Sample k × Scalar => Function.update (original k wx.1).1.2
      (⟨t0.val + 1 + k, hk⟩, if (pending k (by omega) wx.1).1 then 0 else 1) wx.2) := by
    have h0 := (measurable_update' (a := (⟨t0.val + 1 + k, hk⟩, (0 : Fin 2)))).comp
      (ha.prodMk measurable_snd)
    have h1 := (measurable_update' (a := (⟨t0.val + 1 + k, hk⟩, (1 : Fin 2)))).comp
      (ha.prodMk measurable_snd)
    have he : (fun wx : Sample k × Scalar => Function.update (original k wx.1).1.2
        (⟨t0.val + 1 + k, hk⟩, if (pending k (by omega) wx.1).1 then 0 else 1) wx.2) =
        (fun wx => if (pending k (by omega) wx.1).1 then
          Function.update (original k wx.1).1.2 (⟨t0.val + 1 + k, hk⟩, 0) wx.2 else
          Function.update (original k wx.1).1.2 (⟨t0.val + 1 + k, hk⟩, 1) wx.2) := by
      funext wx
      split_ifs <;> rfl
    rw [he]
    exact h0.ite (measurableSet_eq_fun hb (measurable_const (a := true))) h1
  exact (measurable_calendarWithAuxiliary rate rewards C_star C_h b0 u0 t0 k).comp
    (measurable_fst.prodMk hm)

/-- The selected local UPDATE scalar is unused by the actual vector kernel.
In the renewed branch its other label still initializes the endpoint; in the
retained branch the whole inherited endpoint remains inside the kernel. -/
theorem calendarExtensionKernel_withUpdateScalar (k : ℕ) (hk : t0.val + 1 + k < p.T)
    (w : Sample k) (x : Scalar) :
    extension k (by omega) (withUpdate k hk (w, x)) = extension k (by omega) w := by
  let r : Fin p.T := ⟨t0.val + 1 + k, hk⟩
  let a := Function.update (original k w).1.2
    (r, if (pending k (by omega) w).1 then 0 else 1) x
  have hz := (calendarObservation_withAuxiliary_source_tag rate rewards C_star C_h control0 b0 u0 t0
    k hk.le w a).2
  have hp := calendarPendingFlags_withAuxiliary rate rewards C_star C_h control0 b0 u0 t0
    k (by omega) w a
  change current k hk.le (withUpdate k hk (w, x)) = current k hk.le w at hz
  change pending k (by omega) (withUpdate k hk (w, x)) = pending k (by omega) w at hp
  have ho : original k (withUpdate k hk (w, x)) = (((original k w).1.1, a), (original k w).2) :=
    calendarOriginalLift_withAuxiliary rate rewards C_star C_h b0 u0 t0 k w a
  have hs : stored k hk.le (withUpdate k hk (w, x)) = stored k hk.le w := by
    apply Option.some.inj
    exact (calendarStoredState_spec rate rewards C_star C_h control0 b0 u0 t0 k hk.le _).trans
      ((congrArg (fun o => o.2.val.2.2.2)
        (calendarObservation_withUpdateScalar rate rewards C_star C_h control0 b0 u0 t0 k hk w x)).trans
          (calendarStoredState_spec rate rewards C_star C_h control0 b0 u0 t0 k hk.le w).symm)
  rw [calendarExtensionKernel_readout rate rewards C_star C_h control0 b0 u0 t0 k hk,
    calendarExtensionKernel_readout rate rewards C_star C_h control0 b0 u0 t0 k hk,
    hz, hp, hs, ho]
  cases hc : ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h r (current k hk.le w) with
  | none => rfl
  | some y =>
      cases hb : (pending k (by omega) w).1
      · rfl
      · have h1 : a (r, 1) = (original k w).1.2 (r, 1) := by
          dsimp only [a]
          rw [hb]
          exact Function.update_of_ne (by simp) _ _
        dsimp only [r] at h1
        simp only [h1]

/-- The actual generated invocation after local-scalar refill is exactly
its own native source cell with that scalar. This equation retains the SAME
incoming PRE, numerical update, recorder, FAST arm and physical proposal. -/
theorem calendarInvocationCell_withUpdateScalar (k : ℕ) (hk : t0.val + 1 + k < p.T)
    (w : Sample k) (v : Vector) (hc : callFlag k (by omega) w = true) (x : Scalar) :
    let w' := withUpdate k hk (w, x)
    let hc' : callFlag k (by omega) w' = true :=
      (calendarCallFlag_withAuxiliary rate rewards C_star C_h control0 b0 u0 t0 k (by omega) w _).trans hc
    calendarInvocationCell rate rewards C_star C_h control0 b0 u0 t0 k hk w' v hc' =
      nativeCell rate rewards C_star C_h control0 ⟨t0.val + 1 + k, hk⟩
        (calendarInvocationSource rate rewards C_star C_h control0 b0 u0 t0 k hk w v hc) x := by
  dsimp only
  let r : Fin p.T := ⟨t0.val + 1 + k, hk⟩
  let a := Function.update (original k w).1.2
    (r, if (pending k (by omega) w).1 then 0 else 1) x
  let w' := withUpdate k hk (w, x)
  have hc' : callFlag k (by omega) w' = true :=
    (calendarCallFlag_withAuxiliary rate rewards C_star C_h control0 b0 u0 t0 k (by omega) w a).trans hc
  let z := calendarInvocationSource rate rewards C_star C_h control0 b0 u0 t0 k hk w v hc
  let z' := calendarInvocationSource rate rewards C_star C_h control0 b0 u0 t0 k hk w' v hc'
  have hz : z' = z := by
    apply Subtype.ext
    exact congrArg (fun s => ReferenceFirstCollectionRenewalVectorInsertion.insert r s v)
      (calendarObservation_withAuxiliary_source_tag rate rewards C_star C_h control0 b0 u0 t0 k hk.le w a).2
  have hp := calendarPendingFlags_withAuxiliary rate rewards C_star C_h control0 b0 u0 t0 k (by omega) w a
  change pending k (by omega) w' = pending k (by omega) w at hp
  have ho : original k w' = (((original k w).1.1, a), (original k w).2) :=
    calendarOriginalLift_withAuxiliary rate rewards C_star C_h b0 u0 t0 k w a
  have hcell := (calendarInvocationCell_update_readouts rate rewards C_star C_h control0 b0 u0 t0 k hk w' v hc').1
  rw [hcell]
  change nativeCell rate rewards C_star C_h control0 r z'
    ((original k w').1.2 (r, if (pending k (by omega) w').1 then 0 else 1)) = _
  rw [hz, hp, ho]
  change nativeCell rate rewards C_star C_h control0 r z
    (Function.update (original k w).1.2
      (r, if (pending k (by omega) w).1 then 0 else 1) x
        (r, if (pending k (by omega) w).1 then 0 else 1)) = _
  rw [Function.update_self]

/-- The uniform local UPDATE refill has the prescribed source residual
measure, with the overflow and no-proposal Dirac branches retained. This is
the explicit refill law; the surrounding generated integral is supplied by
`calendarLaw_round_joint_innovation_test`. -/
theorem calendarInvocationCell_updateScalar_map (k : ℕ) (hk : t0.val + 1 + k < p.T)
    (w : Sample k) (v : Vector) (hc : callFlag k (by omega) w = true) :
    let r : Fin p.T := ⟨t0.val + 1 + k, hk⟩
    let z := calendarInvocationSource rate rewards C_star C_h control0 b0 u0 t0 k hk w v hc
    (ContinuousControlSlice.scalarLaw).map (fun x =>
      calendarInvocationCell rate rewards C_star C_h control0 b0 u0 t0 k hk (withUpdate k hk (w, x)) v
        ((calendarCallFlag_withAuxiliary rate rewards C_star C_h control0 b0 u0 t0 k (by omega) w _).trans hc)) =
      @Measure.map (SlowSet p) (LogicalCell p rate) Subtype.instMeasurableSpace _
        (ReferenceFirstLiveCalendarMarkedTransition.logicalCellWithNext rate
          (nativeRecord rate rewards C_star C_h r z) (nativeSourceCell rate rewards C_star C_h r z)
          (nativeBefore rate rewards C_star C_h control0 r z))
        (ReferenceFirstLiveCalendarMarkedTransition.logicalCellResidualLaw rate
          (nativeRecord rate rewards C_star C_h r z) (nativeSourceCell rate rewards C_star C_h r z)
          (nativeBefore rate rewards C_star C_h control0 r z)) := by
  dsimp only
  have he := funext (calendarInvocationCell_withUpdateScalar rate rewards C_star C_h control0 b0 u0 t0 k hk w v hc)
  rw [he]
  exact ReferenceFirstLiveCalendarMarkedTransition.appendLogicalCell_residual_law rate _ _ _

private theorem installationPair_fixedVectorControl (q : Fin p.T)
    (z : InvocationSource rate rewards C_star C_h q) (c : Control) :
    let rank := nativeRank rate rewards C_star C_h q z.val
    let vector := ReferenceFirstCollectionSamplerOutputLaw.currentAssignmentVector q z.val
    ReferenceRankInstallationRecorderFastLaw.actualMarkerReservedFast rate rewards C_star C_h q
      (replace q z.val (fixedVectorControl vector c)) =
    ReferenceRankInstallationRecorderFastSourceLaw.actualPairFromHistoryRemainder
      rate rewards C_star C_h q
      (ReferenceRankInstallationRecorderFoundation.history rate rewards C_star C_h control0 rank q z.val)
      ((LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p c).2) := by
  dsimp only
  let rank := nativeRank rate rewards C_star C_h q z.val
  let vector := ReferenceFirstCollectionSamplerOutputLaw.currentAssignmentVector q z.val
  let e := LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p
  let z' := replace q z.val (fixedVectorControl vector c)
  have hz := native_installation rate rewards C_star C_h q z
  have hz' : z' ∈ ReferenceRankInstallationRecorderFoundation.installationEvent
      rate rewards C_star C_h rank q :=
    (ReferenceRankInstallationRecorderFoundation.installationEvent_replaceSourceControl
      rate rewards C_star C_h control0 rank q z.val _).mpr hz
  have hp : sourcePrefix control0 q.val z' = sourcePrefix control0 q.val z.val :=
    ReferenceFirstCollectionOldRecorderFoundation.sourcePrefix_replaceCurrent control0 q q.val le_rfl _ _
  have hc : ReferenceSourceCurrentControlFreshness.u_t p q z' = fixedVectorControl vector c :=
    currentControl_replaceSourceControl q z.val _
  have hs : e (ReferenceSourceCurrentControlFreshness.u_t p q z') = (vector, (e c).2) := by
    rw [hc]
    exact e.apply_symm_apply _
  have hv : ReferenceFirstCollectionSamplerOutputLaw.currentAssignmentVector q z' = vector :=
    congrArg Prod.fst hs
  have hh : ReferenceRankInstallationRecorderFoundation.history rate rewards C_star C_h control0 rank q z' =
      ReferenceRankInstallationRecorderFoundation.history rate rewards C_star C_h control0 rank q z.val := by
    rw [ReferenceRankInstallationRecorderFoundation.history_eq_prefixVectorHistory_of_installation
        rate rewards C_star C_h control0 rank q z' hz',
      ReferenceRankInstallationRecorderFoundation.history_eq_prefixVectorHistory_of_installation
        rate rewards C_star C_h control0 rank q z.val hz, hp, hv]
  have h := ReferenceRankInstallationRecorderFastSourceLaw.actualPair_eq_historyRemainder_of_installation
    rate rewards C_star C_h control0 rank q z' hz'
  rw [hh, congrArg Prod.snd hs] at h
  exact h

local notation "Past" => Source × (SlowSet p × List (LogicalCell p rate))
local notation "Pair" => ReferenceRankInstallationRecorderFastSourceLaw.RecorderFastOutput p
local notation "sourcePair" => ReferenceRankInstallationRecorderFastLaw.actualMarkerReservedFast rate rewards C_star C_h

/-- Complete original nonassignment remainder evaluated against the actual
strict physical prefix. The assignment vector is retained as a fibre variable;
neither the archived slow set nor its correlations are resampled. -/
def calendarRecorderFastKernel (q : Fin p.T) (h : Past) (v : Vector) : Measure Pair :=
  (ReferenceLaterOptionalControlResampling.controlRemainderLaw p).map
    (fun d => ReferenceRankInstallationRecorderFastSourceLaw.actualPairFromHistoryRemainder
      rate rewards C_star C_h q
      (ReferenceRankInstallationRecorderFoundation.prefixVectorHistory rate rewards C_star C_h control0 q (h.1, v)) d)

private theorem calendarInvocation_history (k : ℕ) (hk : t0.val + 1 + k < p.T)
    (w : Sample k) (v : Vector) (hc : callFlag k (by omega) w = true) :
    let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
    let z := calendarInvocationSource rate rewards C_star C_h control0 b0 u0 t0 k hk w v hc
    ReferenceRankInstallationRecorderFoundation.history rate rewards C_star C_h control0
      (nativeRank rate rewards C_star C_h q z.val) q z.val =
    ReferenceRankInstallationRecorderFoundation.prefixVectorHistory rate rewards C_star C_h control0 q
      ((past k hk.le w).1, v) := by
  dsimp only
  rw [ReferenceRankInstallationRecorderFoundation.history_eq_prefixVectorHistory_of_installation
    rate rewards C_star C_h control0 _ _ _ (native_installation rate rewards C_star C_h _ _)]
  congr 1
  apply Prod.ext
  · exact ReferenceFirstCollectionOldRecorderFoundation.sourcePrefix_replaceCurrent control0
      ⟨t0.val + 1 + k, hk⟩ _ le_rfl _ _
  · exact ReferenceFirstCollectionRenewalVectorInsertion.av_insert _ _ v

/-- The internally constructed prefix kernel is the actual native invocation's
prescribed correlated output kernel, with its actual frozen anchor and weights. -/
theorem calendarRecorderFastKernel_actual (k : ℕ) (hk : t0.val + 1 + k < p.T)
    (w : Sample k) (v : Vector) (hc : callFlag k (by omega) w = true) :
    let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
    let z := calendarInvocationSource rate rewards C_star C_h control0 b0 u0 t0 k hk w v hc
    let view := (nativeSourceCell rate rewards C_star C_h q z).selected.view
    ∃ valid : CoordinatorLocalArmChoice.ChoiceInputsValid view.payload view.cutoff q view.complementWeights,
      calendarRecorderFastKernel rate rewards C_star C_h control0 q (past k hk.le w) v =
        ReferenceRankInstallationSourceKernelComposition.installationRecorderFastOutputKernel rate q view valid := by
  dsimp only
  let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
  let z := calendarInvocationSource rate rewards C_star C_h control0 b0 u0 t0 k hk w v hc
  let view := (nativeSourceCell rate rewards C_star C_h q z).selected.view
  let valid := ReferenceRankInstallationRecorderFastLaw.actualInstallationView_valid rate rewards C_star C_h q z.val view
    (nativeCell_view rate rewards C_star C_h control0 q z)
  have h := ReferenceRankInstallationSourceKernelComposition.installationEvent_sourceLawOutput_pushforward
    rate rewards C_star C_h control0 (nativeRank rate rewards C_star C_h q z.val) q z.val
    (native_installation rate rewards C_star C_h q z) view valid
    (nativeCell_view rate rewards C_star C_h control0 q z)
  rw [calendarInvocation_history rate rewards C_star C_h control0 b0 u0 t0 k hk w v hc] at h
  exact ⟨valid, h⟩

private theorem calendarCall_pair_refill (k : ℕ) (hk : t0.val + 1 + k < p.T)
    (w : Sample k) (v : Vector) (hc : callFlag k (by omega) w = true) (c : Control) :
    let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
    sourcePair q (ReferenceFirstCollectionRenewalVectorInsertion.insert q (replace q (current k hk.le w) c) v) =
      ReferenceRankInstallationRecorderFastSourceLaw.actualPairFromHistoryRemainder rate rewards C_star C_h q
        (ReferenceRankInstallationRecorderFoundation.prefixVectorHistory rate rewards C_star C_h control0 q
          ((past k hk.le w).1, v)) ((LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p c).2) := by
  dsimp only
  let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
  let z := calendarInvocationSource rate rewards C_star C_h control0 b0 u0 t0 k hk w v hc
  have hz : ReferenceFirstCollectionRenewalVectorInsertion.insert q (replace q (current k hk.le w) c) v =
      replace q z.val (fixedVectorControl v c) := by
    unfold ReferenceFirstCollectionRenewalVectorInsertion.insert ReferenceFirstCollectionRenewalVectorInsertion.ctrl
    change replace q (replace q (current k hk.le w) c)
      (fixedVectorControl v (ReferenceFirstCollectionRenewalVectorInsertion.c q (replace q (current k hk.le w) c))) = _
    rw [show ReferenceFirstCollectionRenewalVectorInsertion.c q (replace q (current k hk.le w) c) = c from
      currentControl_replaceSourceControl q _ c, replaceSourceControl_twice]
    change _ = replace q (replace q (current k hk.le w) _) (fixedVectorControl v c)
    rw [replaceSourceControl_twice]
  rw [hz]
  have h := installationPair_fixedVectorControl rate rewards C_star C_h control0 q z c
  dsimp only at h
  rw [show ReferenceFirstCollectionSamplerOutputLaw.currentAssignmentVector q z.val = v from
      ReferenceFirstCollectionRenewalVectorInsertion.av_insert q _ v,
    calendarInvocation_history rate rewards C_star C_h control0 b0 u0 t0 k hk w v hc] at h
  exact h

omit rate rewards C_star C_h control0 b0 u0 t0 in
private theorem lintegral_control_pair_kernel {A V : Type*} [MeasurableSpace A] [MeasurableSpace V]
    (mu : Measure Control) [SFinite mu] (nu : Measure A) [SFinite nu]
    (kernel : ProbabilityTheory.Kernel A V) [ProbabilityTheory.IsSFiniteKernel kernel]
    (f : Control × (A × V) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ ca, ∫⁻ v, f (ca.1, (ca.2, v)) ∂kernel ca.2 ∂mu.prod nu) =
      ∫⁻ a, ∫⁻ v, ∫⁻ c, f (c, (a, v)) ∂mu ∂kernel a ∂nu := by
  have h : Measurable (fun ca : Control × A => ∫⁻ v, f (ca.1, (ca.2, v)) ∂kernel ca.2) :=
    (hf.comp (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))).lintegral_kernel_prod_right'
      (κ := kernel.comap Prod.snd measurable_snd)
  rw [lintegral_prod _ h.aemeasurable]
  calc
    _ = ∫⁻ c, ∫⁻ av, f (c, av) ∂nu.compProd kernel ∂mu := by
      apply lintegral_congr
      intro c
      exact (Measure.lintegral_compProd (hf.comp (measurable_const.prodMk measurable_id))).symm
    _ = ∫⁻ av, ∫⁻ c, f (c, av) ∂mu ∂nu.compProd kernel :=
      lintegral_lintegral_swap hf.aemeasurable
    _ = _ := Measure.lintegral_compProd hf.lintegral_prod_left'

/-- Joint generated-past/recorder/FAST identity on actual clear calls. The
whole current physical control has been integrated out. Auxiliary endpoint
selection and the assignment fibre remain correlated with the earlier archive;
the inner measure is identified with the prescribed native kernel above. -/
theorem calendarLaw_call_recorderFast_test (k : ℕ) (hk : t0.val + 1 + k < p.T)
    (F : (Past × Vector) × Pair → ℝ≥0∞) (hF : Measurable F) :
    let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
    (∫⁻ wv : Sample k × Vector,
      if wv.1 ∈ calendarActiveEvent rate rewards C_star C_h control0 b0 u0 t0 k hk then
        F ((past k hk.le wv.1, wv.2), sourcePair q (current (k + 1) (by omega) wv)) else 0
      ∂law (k + 1) (by omega)) =
      ∫⁻ w, if w ∈ calendarActiveEvent rate rewards C_star C_h control0 b0 u0 t0 k hk then
        ∫⁻ a, ∫⁻ v, ∫⁻ y, F ((past k hk.le w, v), y)
          ∂calendarRecorderFastKernel rate rewards C_star C_h control0 q (past k hk.le w) v
          ∂extension k (by omega) (fillPair q k (w, a)) ∂auxiliaryPairLaw else 0
        ∂(law k hk.le).map (calendarEraseInnovation rate rewards C_star C_h control0 b0 u0 t0 q
          (by change t0.val < t0.val + 1 + k; omega) k) := by
  dsimp only
  let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
  let hq : t0.val < q.val := by dsimp only [q]; omega
  let active := calendarActiveEvent rate rewards C_star C_h control0 b0 u0 t0 k hk
  let fill := calendarFillInnovation rate rewards C_star C_h control0 b0 u0 t0 q hq k
  let test : Sample k × Vector → ℝ≥0∞ := fun wv => if wv.1 ∈ active then
    F ((past k hk.le wv.1, wv.2), sourcePair q (current (k + 1) (by omega) wv)) else 0
  have hp := measurable_calendarRoundPast rate rewards C_star C_h control0 b0 u0 t0 k hk.le
  have hpair := ReferenceRankInstallationRecorderFastLaw.measurable_actualMarkerReservedFast rate rewards C_star C_h q
  have hm : Measurable test := (hF.comp (((hp.comp measurable_fst).prodMk measurable_snd).prodMk
    (hpair.comp (measurable_calendarCurrentSource rate rewards C_star C_h control0 b0 u0 t0 (k + 1) (by omega))))).ite
      ((measurableSet_calendarActiveEvent rate rewards C_star C_h control0 b0 u0 t0 k hk).preimage measurable_fst)
      measurable_const
  refine (calendarLaw_round_innovation_test rate rewards C_star C_h control0 b0 u0 t0 q hq k hk le_rfl test hm).trans ?_
  apply lintegral_congr
  intro w
  change (∫⁻ x, ∫⁻ v, test (fill (w, x), v) ∂extension k (by omega) (fill (w, x))
    ∂innovationLaw (p := p)) = _
  have hflags (x : Innovation p) : fill (w, x) ∈ active ↔ w ∈ active := by
    change (callFlag k (by omega) (calendarReplaceControl rate rewards C_star C_h control0 b0 u0 t0 q hq k
        (fillPair q k (w, x.2), x.1)) = true ∧
      (pending k (by omega) (calendarReplaceControl rate rewards C_star C_h control0 b0 u0 t0 q hq k
        (fillPair q k (w, x.2), x.1))).2 = true) ↔ _
    rw [calendarCallFlag_replaceControl rate rewards C_star C_h control0 b0 u0 t0 q hq k hk le_rfl,
      calendarPendingClear_replaceControl rate rewards C_star C_h control0 b0 u0 t0 q hq k hk le_rfl,
      calendarFillPair_eq_withAuxiliary,
      calendarCallFlag_withAuxiliary, calendarPendingFlags_withAuxiliary]
    rfl
  by_cases hw : w ∈ active
  · rw [ite_eq_left hw]
    have hcurrent (x : Innovation p) : current k hk.le (fill (w, x)) = replace q (current k hk.le w) x.1 := by
      change current k hk.le (calendarReplaceControl rate rewards C_star C_h control0 b0 u0 t0 q hq k
        (fillPair q k (w, x.2), x.1)) = _
      rw [calendarCurrentSource_replaceControl rate rewards C_star C_h control0 b0 u0 t0 q hq k hk.le le_rfl,
        calendarFillPair_eq_withAuxiliary]
      rw [(calendarObservation_withAuxiliary_source_tag rate rewards C_star C_h control0 b0 u0 t0 k hk.le w _).2]
    have he (x : Innovation p) :
        (∫⁻ v, test (fill (w, x), v) ∂extension k (by omega) (fill (w, x))) =
        ∫⁻ v, F ((past k hk.le w, v),
          sourcePair q (ReferenceFirstCollectionRenewalVectorInsertion.insert q
            (replace q (current k hk.le w) x.1) v)) ∂extension k (by omega) (fillPair q k (w, x.2)) := by
      have hcall : callFlag k (by omega) (fillPair q k (w, x.2)) = true := by
        rw [calendarFillPair_eq_withAuxiliary, calendarCallFlag_withAuxiliary]
        exact hw.1
      have hclear : (pending k (by omega) (fillPair q k (w, x.2))).2 = true := by
        rw [calendarFillPair_eq_withAuxiliary, calendarPendingFlags_withAuxiliary]
        exact hw.2
      have hK := calendarExtensionKernel_active_currentControl rate rewards C_star C_h control0 b0 u0 t0 k hk
        (fillPair q k (w, x.2)) x.1 hcall hclear
      change extension k (by omega) (fill (w, x)) = extension k (by omega) (fillPair q k (w, x.2)) at hK
      rw [hK]
      apply lintegral_congr
      intro v
      dsimp only [test]
      rw [ite_eq_left ((hflags x).mpr hw),
        calendarRoundPast_fillInnovation rate rewards C_star C_h control0 b0 u0 t0 q hq k hk.le le_rfl,
        calendarCurrentSource_succ rate rewards C_star C_h control0 b0 u0 t0 k (by omega),
        ite_eq_left ((hflags x).mpr hw).1, hcurrent]
    simp_rw [he]
    let kernel := (extension k (by omega)).comap (fun a => fillPair q k (w, a))
      ((measurable_calendarFillPair rate rewards C_star C_h b0 u0 t0 q k).comp
        (measurable_const.prodMk measurable_id))
    let f : Control × ((Scalar × Scalar) × Vector) → ℝ≥0∞ := fun cav =>
      F ((past k hk.le w, cav.2.2), sourcePair q (ReferenceFirstCollectionRenewalVectorInsertion.insert q
        (replace q (current k hk.le w) cav.1) cav.2.2))
    have hrep : Measurable (fun cav : Control × ((Scalar × Scalar) × Vector) =>
        replace q (current k hk.le w) cav.1) :=
      (ReferenceSourcePhysicalFlagConditionalLaw.measurable_replaceSourceControl p q).comp
        (measurable_const.prodMk measurable_fst)
    have hf : Measurable f := hF.comp ((measurable_const.prodMk measurable_snd.snd).prodMk (hpair.comp
      ((ReferenceFirstCollectionRenewalVectorInsertion.measurable_insert q).comp
        (hrep.prodMk measurable_snd.snd))))
    change (∫⁻ ca, ∫⁻ v, f (ca.1, (ca.2, v)) ∂kernel ca.2
      ∂(ContinuousLearningRows.timeControlLaw p).prod auxiliaryPairLaw) = _
    rw [lintegral_control_pair_kernel (ContinuousLearningRows.timeControlLaw p) auxiliaryPairLaw kernel f hf]
    apply lintegral_congr
    intro a
    apply lintegral_congr
    intro v
    let H := ReferenceRankInstallationRecorderFoundation.prefixVectorHistory rate rewards C_star C_h control0 q
      ((past k hk.le w).1, v)
    let g := fun d => F ((past k hk.le w, v),
      ReferenceRankInstallationRecorderFastSourceLaw.actualPairFromHistoryRemainder rate rewards C_star C_h q H d)
    have hreplace : (∫⁻ c, f (c, (a, v)) ∂ContinuousLearningRows.timeControlLaw p) =
        ∫⁻ c, g ((LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p c).2)
          ∂ContinuousLearningRows.timeControlLaw p := by
      apply lintegral_congr
      intro c
      exact congrArg (fun y => F ((past k hk.le w, v), y))
        (calendarCall_pair_refill rate rewards C_star C_h control0 b0 u0 t0 k hk w v hw.1 c)
    rw [hreplace]
    have hg : Measurable g := hF.comp (measurable_const.prodMk
      (Measurable.of_uncurry_left (ReferenceRankInstallationRecorderFastSourceLaw.measurable_actualPairFromHistoryRemainder
        rate rewards C_star C_h q)))
    have hrem := (measurePreserving_snd (μ := ContinuousControlSlice.assignmentLaw p.K)
      (ν := ReferenceLaterOptionalControlResampling.controlRemainderLaw p)).comp
        (LaunchAssignmentCoordinateSplit.measurePreserving_controlAssignmentSplitEquiv p)
    change (∫⁻ c, g ((LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p c).2)
      ∂ContinuousLearningRows.timeControlLaw p) = _
    calc
      _ = ∫⁻ d, g d ∂(ContinuousLearningRows.timeControlLaw p).map
          (Prod.snd ∘ LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p) :=
        (lintegral_map hg hrem.measurable).symm
      _ = ∫⁻ d, g d ∂ReferenceLaterOptionalControlResampling.controlRemainderLaw p :=
        congrArg (fun mu => ∫⁻ d, g d ∂mu) hrem.map_eq
      _ = _ := by
        have hread : Measurable (fun d : ReferenceLaterOptionalControlResampling.ControlRemainder p =>
            ReferenceRankInstallationRecorderFastSourceLaw.actualPairFromHistoryRemainder rate rewards C_star C_h q H d) :=
          Measurable.of_uncurry_left (ReferenceRankInstallationRecorderFastSourceLaw.measurable_actualPairFromHistoryRemainder
            rate rewards C_star C_h q)
        exact (lintegral_map (hF.comp (measurable_const.prodMk measurable_id)) hread).symm
  · rw [ite_eq_right hw]
    have he (x : Innovation p) : ∀ v, test (fill (w, x), v) = 0 := by
      intro v
      exact ite_eq_right (fun hx => hw ((hflags x).mp hx))
    simp only [he, lintegral_zero]

/-- The physical readout in the generated joint identity is the SAME native
logical recorder/FAST pair on clear PRE, even when this UPDATE detects overflow. -/
theorem calendarInvocationCell_recorderFast_readouts (k : ℕ) (hk : t0.val + 1 + k < p.T)
    (w : Sample k) (v : Vector) (hc : callFlag k (by omega) w = true)
    (hclear : (pending k (by omega) w).2 = true) :
    let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
    let z := calendarInvocationSource rate rewards C_star C_h control0 b0 u0 t0 k hk w v hc
    let c := calendarInvocationCell rate rewards C_star C_h control0 b0 u0 t0 k hk w v hc
    sourcePair q z.val = (some c.numerical.2.1, some c.fastArm) ∧
      c.slowSet = (nativeSourceCell rate rewards C_star C_h q z).selected.view.payload.slowSet := by
  dsimp only
  let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
  let z := calendarInvocationSource rate rewards C_star C_h control0 b0 u0 t0 k hk w v hc
  let c := calendarInvocationCell rate rewards C_star C_h control0 b0 u0 t0 k hk w v hc
  obtain ⟨input, hi, _, _, _, hn, hb, _⟩ := calendarInvocationCell_actualInput
    rate rewards C_star C_h control0 b0 u0 t0 k hk w v hc
  have hov : c.before.overflow = false := by
    change (observe k hk.le w).2.val.2.2.1.any (fun S => !S.overflow) = true at hclear
    rw [← hb, Option.any_some, Bool.not_eq_true'] at hclear
    exact hclear
  have hcell := (calendarInvocationCell_update_readouts rate rewards C_star C_h control0 b0 u0 t0 k hk w v hc).1
  have hbefore : (nativeBefore rate rewards C_star C_h control0 q z).overflow = false := hov
  constructor
  · apply Prod.ext
    · change ((ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h q z.val).bind
        (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate)).map (fun i => i.recordedArm) = _
      rw [hi, Option.map_some]
      exact (congrArg (fun n => some n.2.1) hn).symm
    · change ReferenceRankInstallationRecorderFastLaw.actualReservedFast rate rewards C_star C_h q z.val =
        some (calendarInvocationCell rate rewards C_star C_h control0 b0 u0 t0 k hk w v hc).fastArm
      rw [nativeSourceCell_fast rate rewards C_star C_h control0 q z, hcell]
      change some _ = some (if (nativeBefore rate rewards C_star C_h control0 q z).overflow then _ else _)
      rw [hbefore]
      rfl
  · rw [hcell]
    change (if (nativeBefore rate rewards C_star C_h control0 q z).overflow then _ else _) = _
    rw [hbefore]
    rfl

attribute [local instance] ReferenceRankInstallationRecorderFoundation.optionSingleton

/-- Explicit ξ and bottom masses and the prescribed FAST marginal of the
generated call kernel. The joint kernel itself remains correlated. -/
theorem calendarRecorderFastKernel_marginals (k : ℕ) (hk : t0.val + 1 + k < p.T)
    (w : Sample k) (v : Vector) (hc : callFlag k (by omega) w = true) :
    let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
    let z := calendarInvocationSource rate rewards C_star C_h control0 b0 u0 t0 k hk w v hc
    let view := (nativeSourceCell rate rewards C_star C_h q z).selected.view
    let K := calendarRecorderFastKernel rate rewards C_star C_h control0 q (past k hk.le w) v
    ∃ valid : CoordinatorLocalArmChoice.ChoiceInputsValid view.payload view.cutoff q view.complementWeights,
      (∀ j, (K.map Prod.fst) {some (some j)} = ENNReal.ofReal (view.payload.rate j)) ∧
      (K.map Prod.fst) {some none} = ENNReal.ofReal (1 - ∑ j, view.payload.rate j) ∧
      K.map Prod.snd = (CanonicalFastSampling.qGammaPMF p rate.eta.val rate.eta.property
        rate.sourceCap view.payload.anchor
        (ReferenceFirstWindowNumericalStream.sourceWeights view.payload view.complementWeights) view.payload.anchor_pos
        (ReferenceFirstWindowNumericalStream.sourceWeights_pos view.payload view.complementWeights view.cutoff q valid)
        (ReferenceFirstWindowNumericalStream.sourceWeights_lower view.payload view.complementWeights view.cutoff q valid)
        (ReferenceFirstWindowNumericalStream.sourceWeights_upper view.payload view.complementWeights view.cutoff q valid)
        view.payload.slowSet).toMeasure.map (fun j => some j.val) := by
  dsimp only
  obtain ⟨valid, hK⟩ := calendarRecorderFastKernel_actual rate rewards C_star C_h control0 b0 u0 t0 k hk w v hc
  have hm := ReferenceRankInstallationSourceKernelComposition.installationRecorderFastOutputKernel_marginals rate _ _ valid
  refine ⟨valid, ?_, ?_, ?_⟩
  · intro j
    rw [hK, hm.1, Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
    simp only [Set.preimage, Set.mem_singleton_iff, Option.some.injEq, Set.ofPred_eq_eq_singleton]
    rw [RecordedRoundMoments.recordingOutcomePMF_toMeasure_some]
    rfl
  · rw [hK, hm.1, Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
    simp only [Set.preimage, Set.mem_singleton_iff, Option.some.injEq, Set.ofPred_eq_eq_singleton]
    rw [RecordedRoundMoments.recordingOutcomePMF_toMeasure_none]
    rfl
  · rw [hK]
    have hslow (payload : AssignmentStartPayload.Input p rate.eta) :
        SnapshotRecordingKernel.assignmentSlowSet p payload.assignment = payload.slowSet := by
      apply Subtype.ext
      exact payload.assignment_image
    have hs := hslow (nativeSourceCell rate rewards C_star C_h ⟨t0.val + 1 + k, hk⟩
      (calendarInvocationSource rate rewards C_star C_h control0 b0 u0 t0 k hk w v hc)).selected.view.payload
    rw [hs] at hm
    exact hm.2

end Bandits.Support.ReferenceGeneratedCalendarRoundInnovation
