/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedCalendarEndpointMixture

import Mathlib.Tactic

/-!
# Native joins in the actual generated calendar

Sources: ZIP4 `06_interruptions.tex:391-426`,
`04_slow_fast_learner.tex:142-215,323-390`, and
`08_main_theorem.tex:78-109`.

All readouts refer to the existing nested `CalendarSample`, its unnormalized
`calendarLaw`, and its canonical `calendarObservation`. In particular the
original branch bit does not determine a later call's UPDATE label. A clear
PRE includes the first overflow-detecting UPDATE. Stopped PREs keep their
physical continuation and impose no assignment/endpoint equality.

These support and path identities assert no current-source marginal, logical
round law, payoff estimate, or manuscript closure.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal Classical
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
open ReferenceGeneratedCalendarResidualBlock
open ReferenceGeneratedCalendarNativePreservation
open ReferenceGeneratedCalendarEndpointMixture
open ReferenceGeneratedNativeInvocationGeometry
open ReferenceFirstCollectionLogicalPrefixExtension (noCallAt)
open ReferenceSourcePrefixHistoryFiltration (sourcePrefix)

namespace Bandits.Support.ReferenceGeneratedCalendarPathAgreement

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
  (control0 : ContinuousLearningRows.TimeControl p) (b0 : Bool) (u0 t0 : Fin p.T)

local notation "Cell" => LogicalCell p rate
local notation "Vector" => AssignmentParameterFibreKernel.AssignmentVector p
local notation "Theta" => AssignmentParameterFibreKernel.Theta p
local notation "Sample" => CalendarSample rate rewards C_star C_h b0 u0 t0
local notation "observe" => calendarObservation rate rewards C_star C_h control0 b0 u0 t0
local notation "original" => calendarOriginalLift rate rewards C_star C_h b0 u0 t0
local notation "law" => calendarLaw rate rewards C_star C_h control0 b0 u0 t0
local notation "sourceCall" => ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h
local notation "callFlag" => calendarCallFlag rate rewards C_star C_h control0 b0 u0 t0
local notation "pending" => calendarPendingFlags rate rewards C_star C_h control0 b0 u0 t0
local notation "lastFlags" => calendarLastFlags rate rewards C_star C_h control0 b0 u0 t0
local notation "matches" => calendarFibreMatch rate rewards C_star C_h control0 b0 u0 t0
local notation "mass" => calendarInstallationMass rate rewards C_star C_h control0 b0 u0 t0
local notation "sectionEvent" => calendarEndpointSection rate rewards C_star C_h control0 b0 u0 t0
local notation "insertVector" => ReferenceFirstCollectionRenewalVectorInsertion.insert

/-- The actual present logical seed/list, without any correctness predicate. -/
def calendarStoredState (k : ℕ) (hk : t0.val + 1 + k ≤ p.T) (w : Sample k) :
    SlowSet p × List Cell :=
  (observe k hk w).2.val.2.2.2.get (observe k hk w).2.property

local notation "stored" => calendarStoredState rate rewards C_star C_h control0 b0 u0 t0

theorem calendarStoredState_spec (k : ℕ) (hk : t0.val + 1 + k ≤ p.T) (w : Sample k) :
    some (stored k hk w) = (observe k hk w).2.val.2.2.2 := Option.some_get _

/-- Read the native cell of the actual transition, including its full source
and the local retained/renewed choice of UPDATE uniform. -/
def calendarInvocationCell (k : ℕ) (hk : t0.val + 1 + k < p.T) (w : Sample k)
    (v : Vector) (hc : callFlag k (by omega) w = true) : Cell :=
  let o := observe k hk.le w
  (calendarCallTransition rate rewards C_star C_h control0 o.1
    ⟨t0.val + 1 + k, hk⟩ ⟨(o.2, ((original k w).1.2, v)), hc⟩).2.2.2

local notation "invocation" => calendarInvocationCell rate rewards C_star C_h control0 b0 u0 t0

theorem calendarInvocationCell_before (k : ℕ) (hk : t0.val + 1 + k < p.T) (w : Sample k)
    (v : Vector) (hc : callFlag k (by omega) w = true) :
    some (invocation k hk w v hc).before = (observe k hk.le w).2.val.2.2.1 := by
  let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
  let o : TaggedPrefix rate q.castSucc := observe k hk.le w
  let x : calendarCallEvent rate rewards C_star C_h o.1 q :=
    ⟨(o.2, ((original k w).1.2, v)), hc⟩
  let z := calendarCallSource rate rewards C_star C_h control0 o.1 q x
  change some (nativeBefore rate rewards C_star C_h control0 q z) = _
  rw [← nativeBefore_prefix rate rewards C_star C_h control0 q z]
  change prefixNumerical rate rewards C_star C_h q.castSucc
      (insertVector q o.2.val.1.1.1.2 v) = o.2.val.2.2.1
  have hp : sourcePrefix control0 q.val (insertVector q o.2.val.1.1.1.2 v) =
      sourcePrefix control0 q.val o.2.val.1.1.1.2 :=
    ReferenceFirstCollectionOldRecorderFoundation.sourcePrefix_replaceCurrent control0 q q.val le_rfl _ _
  rw [prefixNumerical_sourcePrefix rate rewards C_star C_h control0 q.castSucc q.val le_rfl,
    hp, ← prefixNumerical_sourcePrefix rate rewards C_star C_h control0 q.castSucc q.val le_rfl]
  exact (calendarObservation_numerical rate rewards C_star C_h control0 b0 u0 t0 k hk.le w).symm

/-- A call appends its actual native cell to exactly the incoming list. No
sampler-support or PRE-clear assumption is needed for this literal equation. -/
theorem calendarObservation_call_append (k : ℕ) (hk : t0.val + 1 + k < p.T) (w : Sample k)
    (v : Vector) (hc : callFlag k (by omega) w = true) :
    let c := invocation k hk w v hc
    stored (k + 1) (by omega) (w, v) = (c.nextSlowSet, (stored k hk.le w).2 ++ [c]) ∧
      (observe (k + 1) (by omega) (w, v)).2.val.2.2.1 = some c.after ∧
      c.time = ⟨t0.val + 1 + k, hk⟩ := by
  dsimp only
  let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
  let o : TaggedPrefix rate q.castSucc := observe k hk.le w
  let x : calendarCallEvent rate rewards C_star C_h o.1 q :=
    ⟨(o.2, ((original k w).1.2, v)), hc⟩
  have hs := calendarCallPrefix_alignment rate rewards C_star C_h control0 o.1 q x
  have he : (o.2, ((original k w).1.2, v)) ∈ calendarCallEvent rate rewards C_star C_h o.1 q := hc
  have ho : observe (k + 1) (by omega) (w, v) =
      calendarStep rate rewards C_star C_h control0 q (o, ((original k w).1.2, v)) := rfl
  refine ⟨?_, ?_, ?_⟩
  · apply Option.some.inj
    exact (calendarStoredState_spec rate rewards C_star C_h control0 b0 u0 t0 (k + 1)
      (by omega) (w, v)).trans (by rw [ho, calendarStep, dite_eq_left he]; exact hs.2)
  · rw [ho, calendarStep, dite_eq_left he]
    exact hs.1
  · exact nativeCell_time rate rewards C_star C_h control0 q
      (calendarCallSource rate rewards C_star C_h control0 o.1 q x) _

/-- Unrestricted finite section partition: zero-support exceptions are null
under the actual unnormalized produced law, not removed by a new premise. -/
theorem ae_calendarLaw_call_support (k : ℕ) (hk : t0.val + 1 + k < p.T) :
    ∀ᵐ wv ∂law (k + 1) (by omega),
      callFlag k (by omega) wv.1 = true → (pending k (by omega) wv.1).2 = true →
        matches k hk wv = true ∧ 0 < mass k hk wv.1 ∧ (lastFlags k hk.le wv.1).2 = true := by
  have hm : ∀ᵐ w ∂law k hk.le, ∀ (renewed bs clear : Bool) (s : Fin p.T),
      s.val < t0.val + 1 + k → w ∈ sectionEvent renewed bs clear s k hk → 0 < mass k hk w := by
    apply ae_all_iff.mpr
    intro renewed
    apply ae_all_iff.mpr
    intro bs
    apply ae_all_iff.mpr
    intro clear
    apply ae_all_iff.mpr
    intro s
    by_cases hs : s.val < t0.val + 1 + k
    · filter_upwards [ae_imp_of_ae_restrict
        (ae_calendarLaw_section_mass_pos rate rewards C_star C_h control0 b0 u0 t0 renewed bs clear s k hk hs)]
        with w hw
      exact fun _ => hw
    · exact Filter.Eventually.of_forall fun _ h => (hs h).elim
  have hf : ∀ᵐ wv ∂law (k + 1) (by omega), ∀ (renewed bs clear : Bool) (s : Fin p.T),
      s.val < t0.val + 1 + k → wv.1 ∈ sectionEvent renewed bs clear s k hk → matches k hk wv = true := by
    apply ae_all_iff.mpr
    intro renewed
    apply ae_all_iff.mpr
    intro bs
    apply ae_all_iff.mpr
    intro clear
    apply ae_all_iff.mpr
    intro s
    by_cases hs : s.val < t0.val + 1 + k
    · filter_upwards [ae_imp_of_ae_restrict
        (ae_calendarLaw_section_fibreMatch rate rewards C_star C_h control0 b0 u0 t0 renewed bs clear s k hk hs)]
        with wv hw
      exact fun _ => hw
    · exact Filter.Eventually.of_forall fun _ h => (hs h).elim
  rw [← calendarLaw_succ_map_fst rate rewards C_star C_h control0 b0 u0 t0 k (by omega)] at hm
  filter_upwards [ae_of_ae_map measurable_fst.aemeasurable hm, hf] with wv hm hf hc hclear
  let w := wv.1
  let s := (observe k hk.le w).1
  let renewed := (pending k (by omega) w).1
  let bs := (lastFlags k hk.le w).1
  let clear := (lastFlags k hk.le w).2
  have hs : s.val < t0.val + 1 + k :=
    (calendarObservation_origin rate rewards C_star C_h control0 b0 u0 t0 k hk.le w).1
  have hE : w ∈ sectionEvent renewed bs clear s k hk :=
    ⟨⟨rfl, (Prod.eta _).symm⟩, hc, Prod.ext rfl hclear⟩
  exact ⟨hf renewed bs clear s hs hE, hm renewed bs clear s hs hE,
    calendarEndpointSection_native_clear rate rewards C_star C_h control0 b0 u0 t0 renewed bs clear s k hk w hE⟩

/-- Native sampler identification at a literal clear call. The temporary
fibre equality is supplied by `ae_calendarLaw_call_support` below. -/
theorem calendarInvocationCell_join_of_fibreMatch (k : ℕ) (hk : t0.val + 1 + k < p.T)
    (w : Sample k) (v : Vector) (hc : callFlag k (by omega) w = true)
    (hclear : (pending k (by omega) w).2 = true) (hmatch : matches k hk (w, v) = true) :
    let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
    let o := observe k hk.le w
    let c := invocation k hk w v hc
    ∃ (cutoff : Fin p.T) (theta : Theta),
      sourceCall q o.2.val.1.1.1.2 = some (cutoff, theta) ∧
      AssignmentParameterFibreKernel.successfulSlowSet p theta v = some c.slowSet ∧
      (if renewalFlag rate rewards C_star C_h (t := o.1) q o.2.val then
        freshEndpoint theta ((original k w).1.2 (q, 1)) else some (stored k hk.le w).1) = some c.slowSet := by
  dsimp only
  let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
  let o : TaggedPrefix rate q.castSucc := observe k hk.le w
  let a := (original k w).1.2
  let x : calendarCallEvent rate rewards C_star C_h o.1 q := ⟨(o.2, (a, v)), hc⟩
  let z := calendarCallSource rate rewards C_star C_h control0 o.1 q x
  let c := invocation k hk w v hc
  obtain ⟨⟨cutoff, theta⟩, hcall⟩ := Option.isSome_iff_exists.mp hc
  change sourceCall q o.2.val.1.1.1.2 = some (cutoff, theta) at hcall
  have hcall' : sourceCall q z.val = some (cutoff, theta) := by
    change sourceCall q (insertVector q o.2.val.1.1.1.2 v) = _
    rw [callAt_insert rate rewards C_star C_h control0 q q le_rfl]
    exact hcall
  have hselected := nativeCell_selected rate rewards C_star C_h control0 q z cutoff theta hcall'
  change AssignmentParameterFibreKernel.successfulSlowSet p theta
    (ReferenceFirstCollectionRenewalVectorInsertion.av q (insertVector q o.2.val.1.1.1.2 v)) = _ at hselected
  rw [ReferenceFirstCollectionRenewalVectorInsertion.av_insert] at hselected
  have hbefore := calendarInvocationCell_before rate rewards C_star C_h control0 b0 u0 t0 k hk w v hc
  have hov : c.before.overflow = false := by
    change o.2.val.2.2.1.any (fun S => !S.overflow) = true at hclear
    rw [← hbefore, Option.any_some, Bool.not_eq_true'] at hclear
    exact hclear
  have hslow : c.slowSet = (nativeSourceCell rate rewards C_star C_h q z).selected.view.payload.slowSet := by
    change (if (nativeBefore rate rewards C_star C_h control0 q z).overflow then frozenSlowSet p else _) = _
    have hov' : (nativeBefore rate rewards C_star C_h control0 q z).overflow = false := hov
    simp only [hov', Bool.false_eq_true, ite_false]
    rfl
  let chosen := calendarChosenEndpoint rate rewards C_star C_h control0 b0 u0 t0 k hk theta w
  have hsel : installationSelection rate rewards C_star C_h (t := o.1) q
      (o.2.val, ReferenceFirstNextLiftFutureAuxiliaryPairLaw.auxiliaryPair q a) = some (theta, chosen) := by
    have hclear' : preClearFlag rate (t := o.1) q o.2.val = true := hclear
    simp only [installationSelection, hcall, hclear', ite_true]
    rfl
  have hsampler : AssignmentParameterFibreKernel.successfulSlowSet p theta v = chosen := by
    change ReferenceNextInsertedSourceMarginal.fibreMatch rate rewards C_star C_h (t := o.1) q
      ((o.2.val, ReferenceFirstNextLiftFutureAuxiliaryPairLaw.auxiliaryPair q a), v) = true at hmatch
    simpa only [ReferenceNextInsertedSourceMarginal.fibreMatch, hsel, decide_eq_true_eq] using hmatch
  have heq : AssignmentParameterFibreKernel.successfulSlowSet p theta v = some c.slowSet :=
    hselected.trans (congrArg some hslow.symm)
  refine ⟨cutoff, theta, hcall, heq, ?_⟩
  have hchosen := hsampler.symm.trans heq
  change (if renewalFlag rate rewards C_star C_h (t := o.1) q o.2.val then
    freshEndpoint theta (a (q, 1)) else some (stored k hk.le w).1) = _
  change (if renewalFlag rate rewards C_star C_h (t := o.1) q o.2.val then
    freshEndpoint theta (a (q, 1)) else o.2.val.2.2.2.map Prod.fst) = _ at hchosen
  rw [← calendarStoredState_spec rate rewards C_star C_h control0 b0 u0 t0 k hk.le w,
    Option.map_some] at hchosen
  exact hchosen

/-- Actual generated clear-call join, on both renewal branches and at every
finite calendar date. There is no history, support, or sampler premise. -/
theorem ae_calendarLaw_call_join (k : ℕ) (hk : t0.val + 1 + k < p.T) :
    ∀ᵐ wv : Sample k × Vector ∂law (k + 1) (by omega),
      ∀ hc : callFlag k (by omega) wv.1 = true,
      (pending k (by omega) wv.1).2 = true →
      let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
      let o := observe k hk.le wv.1
      let c : Cell := invocation k hk wv.1 wv.2 hc
      (lastFlags k hk.le wv.1).2 = true ∧ 0 < mass k hk wv.1 ∧
      ∃ (cutoff : Fin p.T) (theta : Theta),
        sourceCall q o.2.val.1.1.1.2 = some (cutoff, theta) ∧
        AssignmentParameterFibreKernel.successfulSlowSet p theta wv.2 = some c.slowSet ∧
        (if renewalFlag rate rewards C_star C_h (t := o.1) q o.2.val then
          freshEndpoint theta ((original k wv.1).1.2 (q, 1))
          else some (stored k hk.le wv.1).1) = some c.slowSet ∧
        stored (k + 1) (by omega) wv = (c.nextSlowSet, (stored k hk.le wv.1).2 ++ [c]) ∧
        (observe (k + 1) (by omega) wv).2.val.2.2.1 = some c.after ∧
        some c.before = o.2.val.2.2.1 ∧ c.time = q := by
  filter_upwards [ae_calendarLaw_call_support rate rewards C_star C_h control0 b0 u0 t0 k hk]
    with wv hsupport hc hclear
  obtain ⟨hm, hpos, hnative⟩ := hsupport hc hclear
  obtain ⟨cutoff, theta, hcall, hsample, hjoin⟩ :=
    calendarInvocationCell_join_of_fibreMatch rate rewards C_star C_h control0 b0 u0 t0
      k hk wv.1 wv.2 hc hclear hm
  obtain ⟨happend, hpost, htime⟩ :=
    calendarObservation_call_append rate rewards C_star C_h control0 b0 u0 t0 k hk wv.1 wv.2 hc
  exact ⟨hnative, hpos, cutoff, theta, hcall, hsample, hjoin, happend, hpost,
    calendarInvocationCell_before rate rewards C_star C_h control0 b0 u0 t0 k hk wv.1 wv.2 hc, htime⟩

/-- Noncalls use exactly the canonical noncall date operation on the same
source and original array. An absent cell preserves the seed and list. -/
theorem calendarObservation_noncall_step (k : ℕ) (hk : t0.val + 1 + k < p.T) (w : Sample k)
    (v : Vector) (hc : callFlag k (by omega) w = false) :
    stored (k + 1) (by omega) (w, v) =
      appendNoncallDate rate rewards C_star C_h ⟨t0.val + 1 + k, hk⟩
        (observe k hk.le w).2.val.1.1.1.2 (original k w).1.2 (stored k hk.le w) := by
  let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
  let o : TaggedPrefix rate q.castSucc := observe k hk.le w
  have he : ¬ (o.2, ((original k w).1.2, v)) ∈ calendarCallEvent rate rewards C_star C_h o.1 q := by
    change ¬ callFlag k (by omega) w = true
    rw [hc]
    exact Bool.false_ne_true
  apply Option.some.inj
  have hs := calendarStoredState_spec rate rewards C_star C_h control0 b0 u0 t0 (k + 1) (by omega) (w, v)
  refine hs.trans ?_
  change (calendarStep rate rewards C_star C_h control0 q (o, ((original k w).1.2, v))).2.val.2.2.2 = _
  rw [calendarStep, dite_eq_right he]
  change o.2.val.2.2.2.map _ = _
  rw [← calendarStoredState_spec rate rewards C_star C_h control0 b0 u0 t0 k hk.le w, Option.map_some]
  exact congrArg some (appendNoncallDate_dateAuxiliary rate rewards C_star C_h q
    o.2.val.1.1.1.2 (original k w).1.2 (stored k hk.le w))

/-- Every single calendar step preserves the whole incoming archived list
and the complete strict source prefix, without a clear-PRE restriction. -/
theorem calendarObservation_step_preserves (k : ℕ) (hk : t0.val + 1 + k < p.T)
    (w : Sample k) (v : Vector) :
    (stored k hk.le w).2 <+: (stored (k + 1) (by omega) (w, v)).2 ∧
      sourcePrefix control0 (t0.val + 1 + k) (observe (k + 1) (by omega) (w, v)).2.val.1.1.1.2 =
        sourcePrefix control0 (t0.val + 1 + k) (observe k hk.le w).2.val.1.1.1.2 := by
  cases hc : callFlag k (by omega) w with
  | true =>
      constructor
      · rw [(calendarObservation_call_append rate rewards C_star C_h control0 b0 u0 t0 k hk w v hc).1]
        exact List.prefix_append _ _
      · exact (calendarObservation_call_prelist rate rewards C_star C_h control0 b0 u0 t0 k hk w v hc).2.2.2
  | false =>
      constructor
      · rw [calendarObservation_noncall_step rate rewards C_star C_h control0 b0 u0 t0 k hk w v hc]
        unfold appendNoncallDate
        split
        · exact List.prefix_refl _
        · exact List.prefix_append _ _
      · let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
        let o : TaggedPrefix rate q.castSucc := observe k hk.le w
        have he : ¬ (o.2, ((original k w).1.2, v)) ∈ calendarCallEvent rate rewards C_star C_h o.1 q := by
          change ¬ callFlag k (by omega) w = true
          rw [hc]
          exact Bool.false_ne_true
        change sourcePrefix control0 q.val
          (calendarStep rate rewards C_star C_h control0 q (o, ((original k w).1.2, v))).2.val.1.1.1.2 = _
        rw [calendarStep, dite_eq_right he]
        rfl

/-- Literal truncation of the nested sample. No history is reconstructed. -/
def calendarAncestor : (k j : ℕ) → j ≤ k → Sample k → Sample j
  | 0, j, h, w => by
      have hj : j = 0 := by omega
      subst j
      exact w
  | k + 1, j, h, w =>
      if hj : j = k + 1 then hj.symm ▸ w
      else calendarAncestor k j (by omega) w.1

local notation "ancestor" => calendarAncestor rate rewards C_star C_h b0 u0 t0

theorem calendarAncestor_self (k : ℕ) (w : Sample k) : ancestor k k le_rfl w = w := by
  cases k with
  | zero => rfl
  | succ k => simp only [calendarAncestor, dite_true]

theorem calendarAncestor_succ (k j : ℕ) (hj : j ≤ k) (w : Sample (k + 1)) :
    ancestor (k + 1) j (by omega) w = ancestor k j hj w.1 := by
  rw [calendarAncestor, dite_eq_right (by omega : j ≠ k + 1)]

/-- All already processed lists and numerical PRE readouts survive every
future insertion. This also applies to the final POST boundary `n=T`. -/
theorem calendarObservation_ancestor_preserves (k : ℕ) (hk : t0.val + 1 + k ≤ p.T) (w : Sample k)
    (j : ℕ) (hj : j ≤ k) :
    let earlier := ancestor k j hj w
    (stored j (by omega) earlier).2 <+: (stored k hk w).2 ∧
      sourcePrefix control0 (t0.val + 1 + j) (observe k hk w).2.val.1.1.1.2 =
        sourcePrefix control0 (t0.val + 1 + j) (observe j (by omega) earlier).2.val.1.1.1.2 ∧
      prefixNumerical rate rewards C_star C_h (calendarBoundary t0 j (by omega))
        (observe k hk w).2.val.1.1.1.2 = (observe j (by omega) earlier).2.val.2.2.1 := by
  have hp : (stored j (by omega) (ancestor k j hj w)).2 <+: (stored k hk w).2 ∧
      sourcePrefix control0 (t0.val + 1 + j) (observe k hk w).2.val.1.1.1.2 =
        sourcePrefix control0 (t0.val + 1 + j) (observe j (by omega) (ancestor k j hj w)).2.val.1.1.1.2 := by
    induction k with
    | zero =>
        have he : j = 0 := by omega
        subst j
        exact ⟨List.prefix_refl _, rfl⟩
    | succ k ih =>
        by_cases he : j = k + 1
        · subst j
          rw [calendarAncestor_self]
          exact ⟨List.prefix_refl _, rfl⟩
        · have hjk : j ≤ k := by omega
          have hi := ih (by omega) w.1 hjk
          have hs := calendarObservation_step_preserves rate rewards C_star C_h control0 b0 u0 t0
            k (by omega) w.1 w.2
          rw [calendarAncestor_succ rate rewards C_star C_h b0 u0 t0 k j hjk w]
          refine ⟨hi.1.trans hs.1, ?_⟩
          have heq := congrArg (sourcePrefix control0 (t0.val + 1 + j)) hs.2
          rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefix_sourcePrefix control0 _ _ (by omega),
            ReferenceSourcePrefixHistoryFiltration.sourcePrefix_sourcePrefix control0 _ _ (by omega)] at heq
          exact heq.trans hi.2
  refine ⟨hp.1, hp.2, ?_⟩
  rw [prefixNumerical_sourcePrefix rate rewards C_star C_h control0 (calendarBoundary t0 j (by omega))
    (t0.val + 1 + j) le_rfl, hp.2,
    ← prefixNumerical_sourcePrefix rate rewards C_star C_h control0 (calendarBoundary t0 j (by omega))
      (t0.val + 1 + j) le_rfl]
  exact (calendarObservation_numerical rate rewards C_star C_h control0 b0 u0 t0 j (by omega) _).symm

/-- The truncation retains the same complete original branch lift. -/
theorem calendarAncestor_original (k j : ℕ) (hj : j ≤ k) (w : Sample k) :
    original j (ancestor k j hj w) = original k w := by
  induction k with
  | zero =>
      have he : j = 0 := by omega
      subst j
      rfl
  | succ k ih =>
      by_cases he : j = k + 1
      · subst j
        rw [calendarAncestor_self]
      · rw [calendarAncestor_succ rate rewards C_star C_h b0 u0 t0 k j (by omega)]
        exact ih (by omega) w.1

/-- The last native cell of every archived prefix can be recomputed on the
final complete current source. All its fields, including UPDATE, are equal. -/
theorem calendarObservation_archived_native (k : ℕ) (hk : t0.val + 1 + k ≤ p.T) (w : Sample k)
    (j : ℕ) (hj : j ≤ k) :
    let earlier := ancestor k j hj w
    let o := observe j (by omega) earlier
    let a := (original j earlier).1.2
    let x := a (o.1, if calendarNativeRenewal rate rewards C_star C_h control0 b0 u0 t0 j (by omega) earlier then 0 else 1)
    ∃ z : InvocationSource rate rewards C_star C_h o.1,
      z.val = (observe k hk w).2.val.1.1.1.2 ∧
      nativeCell rate rewards C_star C_h control0 o.1 z x =
        nativeCell rate rewards C_star C_h control0 o.1
          (calendarNativeSource rate rewards C_star C_h control0 b0 u0 t0 j (by omega) earlier) x := by
  dsimp only
  let earlier := ancestor k j hj w
  let o := observe j (by omega) earlier
  let z0 := calendarNativeSource rate rewards C_star C_h control0 b0 u0 t0 j (by omega) earlier
  let finalSource := (observe k hk w).2.val.1.1.1.2
  have hp := (calendarObservation_ancestor_preserves rate rewards C_star C_h control0 b0 u0 t0 k hk w j hj).2.1
  have hdate := (calendarObservation_origin rate rewards C_star C_h control0 b0 u0 t0 j (by omega) earlier).1
  have hprefix : sourcePrefix control0 (o.1.val + 1) finalSource = sourcePrefix control0 (o.1.val + 1) z0.val := by
    have h := congrArg (sourcePrefix control0 (o.1.val + 1)) hp
    rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefix_sourcePrefix control0 _ _ (by exact hdate),
      ReferenceSourcePrefixHistoryFiltration.sourcePrefix_sourcePrefix control0 _ _ (by exact hdate)] at h
    exact h
  have hpre : sourcePrefix control0 o.1.val finalSource = sourcePrefix control0 o.1.val z0.val := by
    have h := congrArg (sourcePrefix control0 o.1.val) hprefix
    rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefix_sourcePrefix control0 _ _ (Nat.le_succ _),
      ReferenceSourcePrefixHistoryFiltration.sourcePrefix_sourcePrefix control0 _ _ (Nat.le_succ _)] at h
    exact h
  have hcall : sourceCall o.1 finalSource = sourceCall o.1 z0.val :=
    (ReferenceCalendarCollectionCallControlLaw.callAt_factor rate rewards C_star C_h control0 o.1 finalSource).trans
      ((congrArg (sourceCall o.1) hpre).trans
        (ReferenceCalendarCollectionCallControlLaw.callAt_factor rate rewards C_star C_h control0 o.1 z0.val).symm)
  let z : InvocationSource rate rewards C_star C_h o.1 := ⟨finalSource, by rw [hcall]; exact z0.property⟩
  exact ⟨z, rfl, nativeCell_sourcePrefix_congr rate rewards C_star C_h control0 o.1 z z0 hprefix _⟩

/-- Simultaneous actual call joins in every processed prefix of one produced
sample. The finite induction carries native slow-set and append equations,
rather than merely remembering the sampler graph tests. -/
theorem ae_calendarLaw_archived_call_joins (k : ℕ) (hk : t0.val + 1 + k ≤ p.T) :
    ∀ᵐ w ∂law k hk, ∀ (j : ℕ) (hj : j < k),
      let x : Sample j × Vector := ancestor k (j + 1) (by omega) w
      ∀ hc : callFlag j (by omega) x.1 = true,
      (pending j (by omega) x.1).2 = true →
      let q : Fin p.T := ⟨t0.val + 1 + j, by omega⟩
      let o := observe j (by omega) x.1
      let c : Cell := invocation j (by omega) x.1 x.2 hc
      (lastFlags j (by omega) x.1).2 = true ∧ 0 < mass j (by omega) x.1 ∧
      ∃ (cutoff : Fin p.T) (theta : Theta),
        sourceCall q o.2.val.1.1.1.2 = some (cutoff, theta) ∧
        AssignmentParameterFibreKernel.successfulSlowSet p theta x.2 = some c.slowSet ∧
        (if renewalFlag rate rewards C_star C_h (t := o.1) q o.2.val then
          freshEndpoint theta ((original j x.1).1.2 (q, 1))
          else some (stored j (by omega) x.1).1) = some c.slowSet ∧
        stored (j + 1) (by omega) x = (c.nextSlowSet, (stored j (by omega) x.1).2 ++ [c]) ∧
        (observe (j + 1) (by omega) x).2.val.2.2.1 = some c.after ∧
        some c.before = o.2.val.2.2.1 ∧ c.time = q := by
  induction k with
  | zero => exact Filter.Eventually.of_forall fun _ j hj => (Nat.not_lt_zero j hj).elim
  | succ k ih =>
      have hprev := ih (by omega)
      rw [← calendarLaw_succ_map_fst rate rewards C_star C_h control0 b0 u0 t0 k hk] at hprev
      filter_upwards [ae_of_ae_map measurable_fst.aemeasurable hprev,
        ae_calendarLaw_call_join rate rewards C_star C_h control0 b0 u0 t0 k (by omega)]
        with w hprev hnew j hj
      by_cases he : j = k
      · subst j
        dsimp only
        rw [calendarAncestor_self]
        exact hnew
      · have hjk : j + 1 ≤ k := by omega
        dsimp only
        rw [calendarAncestor_succ rate rewards C_star C_h b0 u0 t0 k (j + 1) hjk w]
        exact hprev j (by omega)

/-- Last native cell already stored by the actual initializer. -/
def calendarLastNativeCell (k : ℕ) (hk : t0.val + 1 + k ≤ p.T) (w : Sample k) : Cell :=
  let o := observe k hk w
  nativeCell rate rewards C_star C_h control0 o.1
    (calendarNativeSource rate rewards C_star C_h control0 b0 u0 t0 k hk w)
    ((original k w).1.2 (o.1,
      if calendarNativeRenewal rate rewards C_star C_h control0 b0 u0 t0 k hk w then 0 else 1))

local notation "lastNative" => calendarLastNativeCell rate rewards C_star C_h control0 b0 u0 t0

/-- Actual branch-root cell; this is a readout of the accepted root transition. -/
def calendarRootCell (w : Sample 0) : Cell := by
  cases b0 with
  | false => exact nonrenewedFirstCell rate rewards C_star C_h control0 t0 u0 w
  | true => exact renewedFirstCell rate rewards C_star C_h control0 t0 u0 w

local notation "rootCell" => calendarRootCell rate rewards C_star C_h control0 b0 u0 t0

omit control0 in
/-- The original root endpoint: the old generated endpoint on retention,
or the actual original label-one initial draw on renewal. -/
def calendarRootEndpoint (w : Sample 0) : AssignmentParameterFibreKernel.Outcome p := by
  cases b0 with
  | false => exact (ReferenceFirstCollectionLogicalPrefixExtension.extendedPrefixStateAux
      rate rewards C_star C_h t0.val (Nat.le_of_lt t0.isLt) (w.1.1.val, w.1.2)).1
  | true => exact some (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalAuxiliarySample
      rate rewards C_star C_h u0 t0 w.1.1 w.1.2)

local notation "rootEndpoint" => calendarRootEndpoint rate rewards C_star C_h b0 u0 t0

/-- Root initialization is the SAME native cell and surviving earlier list,
with its actual first UPDATE retained even when its POST detects overflow. -/
theorem calendarObservation_root (hk : t0.val + 1 ≤ p.T) (w : Sample 0) :
    lastNative 0 hk w = rootCell w ∧
      stored 0 hk w = ((rootCell w).nextSlowSet,
        calendarNativePrelist rate rewards C_star C_h control0 b0 u0 t0 0 hk w ++ [rootCell w]) ∧
      (observe 0 hk w).2.val = initialExtension rate rewards C_star C_h t0
        (branchInitial rate rewards C_star C_h control0 b0 u0 t0 w) := by
  have hi := (calendarObservation_native_initial rate rewards C_star C_h control0 b0 u0 t0 0 hk w).1
  change (observe 0 hk w).2.val.1.2.2 =
    calendarNativePrelist rate rewards C_star C_h control0 b0 u0 t0 0 hk w ++ [lastNative 0 hk w] at hi
  have hr : (observe 0 hk w).2.val.1.2.2.getLast? = some (rootCell w) := by
    cases b0 <;> exact postHistory_last rate t0 _
  have hn := congrArg List.getLast? hi
  simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or] at hn
  have he : lastNative 0 hk w = rootCell w := Option.some.inj (hn.symm.trans hr)
  refine ⟨he, ?_, calendarObservation_initial rate rewards C_star C_h control0 b0 u0 t0 hk w⟩
  apply Option.some.inj
  have hinit := calendarObservation_initial rate rewards C_star C_h control0 b0 u0 t0 hk w
  have hlist : (observe 0 hk w).2.val.1.2.2 =
      (branchInitial rate rewards C_star C_h control0 b0 u0 t0 w).2.2 :=
    congrArg (fun o => o.1.2.2) hinit
  have hs := calendarStoredState_spec rate rewards C_star C_h control0 b0 u0 t0 0 hk w
  refine hs.trans ?_
  rw [hinit]
  change ((branchInitial rate rewards C_star C_h control0 b0 u0 t0 w).2.2.getLast?).map _ = _
  have hr' : (branchInitial rate rewards C_star C_h control0 b0 u0 t0 w).2.2.getLast? = some (rootCell w) :=
    (congrArg List.getLast? hlist).symm.trans hr
  rw [hr', Option.map_some]
  rw [he] at hi
  exact congrArg (fun L => some ((rootCell w).nextSlowSet, L)) (hlist.symm.trans hi)

/-- Root support is taken from the two accepted root couplings, on this
same branch law. The only local restriction is the actual native PRE-clear. -/
theorem ae_calendarLaw_root_join (hk : t0.val + 1 ≤ p.T) :
    ∀ᵐ w ∂law 0 hk, (lastNative 0 hk w).before.overflow = false →
      rootEndpoint w = some (lastNative 0 hk w).slowSet := by
  have hroot : ∀ w : Sample 0, lastNative 0 hk w = rootCell w :=
    fun w => (calendarObservation_root rate rewards C_star C_h control0 b0 u0 t0 hk w).1
  simp_rw [hroot]
  cases b0 with
  | false =>
      filter_upwards [ae_nonrenewedFirstCell_installedSlowSet rate rewards C_star C_h control0 t0 u0]
        with w hs hclear
      change (firstBefore rate rewards C_star C_h control0 t0
        (nonrenewedFirstSource rate rewards C_star C_h t0 u0 w.1.1 w.2)).overflow = false at hclear
      change _ = some (if (firstBefore rate rewards C_star C_h control0 t0
        (nonrenewedFirstSource rate rewards C_star C_h t0 u0 w.1.1 w.2)).overflow then frozenSlowSet p else _)
      simp only [hclear, Bool.false_eq_true, ite_false]
      exact hs.symm
  | true =>
      filter_upwards [ae_renewedFirstCell_installedSlowSet rate rewards C_star C_h control0 t0 u0]
        with w hs hclear
      change (firstBefore rate rewards C_star C_h control0 t0
        (renewedFirstSource rate rewards C_star C_h t0 u0
          (ReferenceFirstCollectionRenewalInstallationCoupling.pair rate rewards C_star C_h u0 t0 w).2)).overflow = false at hclear
      change _ = some (if (firstBefore rate rewards C_star C_h control0 t0
        (renewedFirstSource rate rewards C_star C_h t0 u0
          (ReferenceFirstCollectionRenewalInstallationCoupling.pair rate rewards C_star C_h u0 t0 w).2)).overflow then frozenSlowSet p else _)
      simp only [hclear, Bool.false_eq_true, ite_false]
      exact congrArg some hs.symm

/-- Every actual enabled noncall joins the incoming logical seed while PRE
is clear. Its native before/after numerical states are the canonical readouts;
an enabled round with zero arrivals is still an appended UPDATE. -/
theorem calendarObservation_noncall_clear_cell (k : ℕ) (hk : t0.val + 1 + k < p.T)
    (w : Sample k) (v : Vector) (hc : callFlag k (by omega) w = false)
    (hclear : (pending k (by omega) w).2 = true) (e : Cell)
    (he : noncallDateCell rate rewards C_star C_h ⟨t0.val + 1 + k, hk⟩
      (observe k hk.le w).2.val.1.1.1.2 (original k w).1.2 (stored k hk.le w).1 = some e) :
    e.slowSet = (stored k hk.le w).1 ∧
      some e.before = (observe k hk.le w).2.val.2.2.1 ∧
      stored (k + 1) (by omega) (w, v) = (e.nextSlowSet, (stored k hk.le w).2 ++ [e]) := by
  let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
  let o : TaggedPrefix rate q.castSucc := observe k hk.le w
  let z := calendarNativeSource rate rewards C_star C_h control0 b0 u0 t0 k hk.le w
  let a := (original k w).1.2
  let s := stored k hk.le w
  have hword := noncallDateCell_actualWord rate rewards C_star C_h q z.val
    (nativeInvocation_launch rate rewards C_star C_h o.1 z) a s.1 e he
  have hb : some e.before = o.2.val.2.2.1 := by
    have hn := (calendarObservation_word rate rewards C_star C_h control0 b0 u0 t0 k hk.le w).1
    rw [hn]
    exact congrArg some hword.2.1
  have hov : e.before.overflow = false := by
    change o.2.val.2.2.1.any (fun S => !S.overflow) = true at hclear
    rw [← hb, Option.any_some, Bool.not_eq_true'] at hclear
    exact hclear
  refine ⟨?_, hb, ?_⟩
  · by_cases hlive : z.val ∈ ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualDomain rate rewards C_star C_h q
    · have hseed := calendarObservation_live_seed rate rewards C_star C_h control0 b0 u0 t0 k hk w hlive hclear
      have heq : continuingLogicalCell rate rewards C_star C_h q ⟨z.val, hlive⟩ a = e := by
        change noncallDateCell rate rewards C_star C_h q z.val a s.1 = some e at he
        rw [noncallDateCell, dite_eq_left hlive] at he
        exact Option.some.inj he
      exact heq ▸ hseed.2.2.1
    · change noncallDateCell rate rewards C_star C_h q z.val a s.1 = some e at he
      rw [noncallDateCell, dite_eq_right hlive] at he
      split at he
      next hcol =>
        unfold laterCollectionCell? at he
        split at he
        next hen =>
          have heq := Option.some.inj he
          subst e
          change (if (collectionBefore rate rewards C_star C_h q ⟨z.val, hcol⟩).overflow then frozenSlowSet p else s.1) = _
          change (collectionBefore rate rewards C_star C_h q ⟨z.val, hcol⟩).overflow = false at hov
          simp only [hov, Bool.false_eq_true, ite_false]
          rfl
        next hen => cases he
      next hcol => cases he
  · rw [calendarObservation_noncall_step rate rewards C_star C_h control0 b0 u0 t0 k hk w v hc]
    change appendNoncallDate rate rewards C_star C_h q z.val a s = _
    have he' : noncallDateCell rate rewards C_star C_h q z.val a s.1 = some e := he
    rw [appendNoncallDate, he']

/-- Disabled noncalls are distinguished by the actual enabled readout,
independently of whether an enabled UPDATE happens to have zero arrivals. -/
theorem calendarObservation_noncall_presence (k : ℕ) (hk : t0.val + 1 + k < p.T)
    (w : Sample k) (hc : callFlag k (by omega) w = false) :
    (noncallDateCell rate rewards C_star C_h ⟨t0.val + 1 + k, hk⟩
      (observe k hk.le w).2.val.1.1.1.2 (original k w).1.2 (stored k hk.le w).1).isSome =
      ((ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
        ⟨t0.val + 1 + k, hk⟩ (observe k hk.le w).2.val.1.1.1.2).bind
          (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate)).any RecordedQueueRun.RoundInput.enabled := by
  let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
  let o := observe k hk.le w
  let z := calendarNativeSource rate rewards C_star C_h control0 b0 u0 t0 k hk.le w
  have hn : noCallAt rate rewards C_star C_h q z.val := by
    rw [ReferenceFirstCollectionLogicalPrefixExtension.noCallAt_iff_callAt_none]
    apply Option.not_isSome_iff_eq_none.mp
    change ¬ callFlag k (by omega) w = true
    rw [hc]
    exact Bool.false_ne_true
  have hstart := (ReferencePostInvocationGeneratedAlignment.actualRecord_index rate rewards C_star C_h o.1 z.val _
    (nativeSourceCell_spec rate rewards C_star C_h o.1 z).1).choose_spec.2.2
  have hdate := (calendarObservation_origin rate rewards C_star C_h control0 b0 u0 t0 k hk.le w).1
  exact noncallDateCell_presence rate rewards C_star C_h q z.val (hstart.trans_lt hdate) hn _ _

/-- Absent cells preserve the actual logical state; this includes every
disabled noncall and does not discard an enabled zero-arrival service step. -/
theorem calendarObservation_noncall_absent (k : ℕ) (hk : t0.val + 1 + k < p.T)
    (w : Sample k) (v : Vector) (hc : callFlag k (by omega) w = false)
    (he : noncallDateCell rate rewards C_star C_h ⟨t0.val + 1 + k, hk⟩
      (observe k hk.le w).2.val.1.1.1.2 (original k w).1.2 (stored k hk.le w).1 = none) :
    stored (k + 1) (by omega) (w, v) = stored k hk.le w := by
  rw [calendarObservation_noncall_step rate rewards C_star C_h control0 b0 u0 t0 k hk w v hc]
  unfold appendNoncallDate
  rw [he]

/-- Every present noncall cell is appended, including after the stop. Its
POST is the actual next numerical readout, without a PRE-clear premise. -/
theorem calendarObservation_noncall_cell_post (k : ℕ) (hk : t0.val + 1 + k < p.T)
    (w : Sample k) (v : Vector) (hc : callFlag k (by omega) w = false) (e : Cell)
    (he : noncallDateCell rate rewards C_star C_h ⟨t0.val + 1 + k, hk⟩
      (observe k hk.le w).2.val.1.1.1.2 (original k w).1.2 (stored k hk.le w).1 = some e) :
    stored (k + 1) (by omega) (w, v) = (e.nextSlowSet, (stored k hk.le w).2 ++ [e]) ∧
      (observe (k + 1) (by omega) (w, v)).2.val.2.2.1 = some e.after := by
  let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
  let o : TaggedPrefix rate q.castSucc := observe k hk.le w
  let z := calendarNativeSource rate rewards C_star C_h control0 b0 u0 t0 k hk.le w
  have hword := noncallDateCell_actualWord rate rewards C_star C_h q z.val
    (nativeInvocation_launch rate rewards C_star C_h o.1 z) (original k w).1.2 (stored k hk.le w).1 e he
  constructor
  · rw [calendarObservation_noncall_step rate rewards C_star C_h control0 b0 u0 t0 k hk w v hc]
    unfold appendNoncallDate
    rw [he]
  · have hsource : (observe (k + 1) (by omega) (w, v)).2.val.1.1.1.2 = z.val := by
      have hn : ¬ (o.2, ((original k w).1.2, v)) ∈ calendarCallEvent rate rewards C_star C_h o.1 q := by
        change ¬ callFlag k (by omega) w = true
        rw [hc]
        exact Bool.false_ne_true
      change (calendarStep rate rewards C_star C_h control0 q (o, ((original k w).1.2, v))).2.val.1.1.1.2 = _
      rw [calendarStep, dite_eq_right hn]
      rfl
    have hstart := (ReferencePostInvocationGeneratedAlignment.actualRecord_index rate rewards C_star C_h o.1 z.val _
      (nativeSourceCell_spec rate rewards C_star C_h o.1 z).1).choose_spec.2.2
    have hdate := (calendarObservation_origin rate rewards C_star C_h control0 b0 u0 t0 k hk.le w).1
    have hbound : ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h ≤ q.val + 1 :=
      hstart.trans ((show o.1.val < q.val from hdate).le.trans (Nat.le_succ _))
    refine (calendarObservation_numerical rate rewards C_star C_h control0 b0 u0 t0
      (k + 1) (by omega) (w, v)).trans
        ((congrArg (prefixNumerical rate rewards C_star C_h q.succ) hsource).trans ?_)
    exact (prefixNumerical_actualWord rate rewards C_star C_h q.succ z.val
      (nativeInvocation_launch rate rewards C_star C_h o.1 z)
      hbound).trans (congrArg some hword.2.2.1.symm)

omit control0 in
theorem measurable_calendarAncestor (k j : ℕ) (hj : j ≤ k) : Measurable (ancestor k j hj) := by
  induction k with
  | zero =>
      have he : j = 0 := by omega
      subst j
      exact measurable_id
  | succ k ih =>
      by_cases he : j = k + 1
      · subst j
        have heq : ancestor (k + 1) (k + 1) le_rfl = id :=
          funext (calendarAncestor_self rate rewards C_star C_h b0 u0 t0 (k + 1))
        rw [heq]
        exact measurable_id
      · have hjk : j ≤ k := by omega
        have heq : ancestor (k + 1) j hj = ancestor k j hjk ∘ Prod.fst :=
          funext (calendarAncestor_succ rate rewards C_star C_h b0 u0 t0 k j hjk)
        rw [heq]
        exact (ih hjk).comp measurable_fst

/-- Truncation has the earlier produced calendar law, including its full
unnormalized mass and correlated original sample. -/
theorem calendarLaw_map_ancestor (k : ℕ) (hk : t0.val + 1 + k ≤ p.T) (j : ℕ) (hj : j ≤ k) :
    (law k hk).map (ancestor k j hj) = law j (by omega) := by
  induction k with
  | zero =>
      have he : j = 0 := by omega
      subst j
      exact Measure.map_id
  | succ k ih =>
      by_cases he : j = k + 1
      · subst j
        have heq : ancestor (k + 1) (k + 1) le_rfl = id :=
          funext (calendarAncestor_self rate rewards C_star C_h b0 u0 t0 (k + 1))
        rw [heq, Measure.map_id]
      · have hjk : j ≤ k := by omega
        have heq : ancestor (k + 1) j hj = ancestor k j hjk ∘ Prod.fst :=
          funext (calendarAncestor_succ rate rewards C_star C_h b0 u0 t0 k j hjk)
        rw [heq]
        have hm := Measure.map_map (μ := (law (k + 1) hk : Measure (Sample k × Vector)))
          (measurable_calendarAncestor rate rewards C_star C_h b0 u0 t0 k j hjk) measurable_fst
        exact hm.symm.trans ((congrArg (fun m : Measure (Sample k) => m.map (ancestor k j hjk))
          (calendarLaw_succ_map_fst rate rewards C_star C_h control0 b0 u0 t0 k hk)).trans
            (ih (by omega) hjk))

/-- The actual zero-support clear-call exception has zero unnormalized
measure; it is not excluded from the carrier or assumed impossible. -/
theorem calendarLaw_clear_call_zero_mass (k : ℕ) (hk : t0.val + 1 + k < p.T) :
    law (k + 1) (by omega) {wv : Sample k × Vector | callFlag k (by omega) wv.1 = true ∧
      (pending k (by omega) wv.1).2 = true ∧ mass k hk wv.1 = 0} = 0 := by
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [ae_calendarLaw_call_support rate rewards C_star C_h control0 b0 u0 t0 k hk]
    with wv hw hbad
  exact (ne_of_gt (hw hbad.1 hbad.2.1).2.1) hbad.2.2

/-- The complete source of the literal native call transition. -/
def calendarInvocationSource (k : ℕ) (hk : t0.val + 1 + k < p.T) (w : Sample k)
    (v : Vector) (hc : callFlag k (by omega) w = true) :
    InvocationSource rate rewards C_star C_h ⟨t0.val + 1 + k, hk⟩ :=
  let o := observe k hk.le w
  calendarCallSource rate rewards C_star C_h control0 o.1 ⟨t0.val + 1 + k, hk⟩
    ⟨(o.2, ((original k w).1.2, v)), hc⟩

local notation "invocationSource" => calendarInvocationSource rate rewards C_star C_h control0 b0 u0 t0

/-- Exact native UPDATE equations. Renewal uses original label zero here;
its label one has initialized the fresh endpoint. Retention uses label one.
Only PRE overflow gates proposal and refresh. -/
theorem calendarInvocationCell_update_readouts (k : ℕ) (hk : t0.val + 1 + k < p.T)
    (w : Sample k) (v : Vector) (hc : callFlag k (by omega) w = true) :
    let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
    let z := invocationSource k hk w v hc
    let c := invocation k hk w v hc
    let x := (original k w).1.2 (q, if (pending k (by omega) w).1 then 0 else 1)
    c = nativeCell rate rewards C_star C_h control0 q z x ∧
    c.proposal = (!c.before.overflow && ReferenceFirstLivePostUpdateProposalLaw.physicalProposalBit rate
      (ReferenceSourceCurrentControlFreshness.u_t p q z.val)) ∧
    c.nextSlowSet = (if c.before.overflow then frozenSlowSet p else
      if c.proposal then residualDraw rate c.before (nativeSourceCell rate rewards C_star C_h q z).input
        (nativeSourceCell rate rewards C_star C_h q z).selected.view.payload.anchor
        (nativeSourceCell rate rewards C_star C_h q z).selected.view.payload.anchor_pos x
      else (nativeSourceCell rate rewards C_star C_h q z).selected.view.payload.slowSet) := by
  dsimp only
  let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
  let z := invocationSource k hk w v hc
  have hcell : invocation k hk w v hc = nativeCell rate rewards C_star C_h control0 q z
      ((original k w).1.2 (q, if (pending k (by omega) w).1 then 0 else 1)) := by
    change nativeCell rate rewards C_star C_h control0 q z
      (if (pending k (by omega) w).1 then (original k w).1.2 (q, 0) else (original k w).1.2 (q, 1)) = _
    cases (pending k (by omega) w).1 <;> rfl
  refine ⟨hcell, ?_, ?_⟩
  · rw [hcell]
    exact nativeCell_proposal rate rewards C_star C_h control0 q z _
  · rw [hcell]
    dsimp only [nativeCell, appendLogicalCell]
    simp only [Function.update_self]
    rfl

/-- A stopped actual call still appends its prescribed native continuation.
It carries no slow-set equality with the incoming logical endpoint. -/
theorem calendarInvocationCell_stopped (k : ℕ) (hk : t0.val + 1 + k < p.T)
    (w : Sample k) (v : Vector) (hc : callFlag k (by omega) w = true)
    (hstop : (pending k (by omega) w).2 = false) :
    let c := invocation k hk w v hc
    c.slowSet = frozenSlowSet p ∧ c.fastArm = frozenFastArm p ∧ c.proposal = false ∧
      c.nextSlowSet = frozenSlowSet p ∧
      ∀ j, c.arrivals j = (false, 0) ∧ c.service j = 0 ∧ c.after.registers j = c.before.registers j := by
  dsimp only
  let c := invocation k hk w v hc
  let z := invocationSource k hk w v hc
  let Q := ReferenceFirstLaunchNumericalCell.queueParameters rate
  let input := (nativeSourceCell rate rewards C_star C_h ⟨t0.val + 1 + k, hk⟩ z).input
  have hb := calendarInvocationCell_before rate rewards C_star C_h control0 b0 u0 t0 k hk w v hc
  have hov : c.before.overflow = true := by
    change (observe k hk.le w).2.val.2.2.1.any (fun S => !S.overflow) = false at hstop
    rw [← hb, Option.any_some, Bool.not_eq_false'] at hstop
    exact hstop
  have hu := calendarInvocationCell_update_readouts rate rewards C_star C_h control0 b0 u0 t0 k hk w v hc
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact ite_eq_left hov
  · exact ite_eq_left hov
  · rw [hu.2.1]
    change (!c.before.overflow && _) = false
    rw [hov]
    rfl
  · rw [hu.2.2]
    exact ite_eq_left hov
  · intro j
    refine ⟨(RecordedQueueRun.step_after_overflow_preserves Q c.before input hov j).2, ?_,
      (RecordedQueueRun.step_after_overflow_preserves Q c.before input hov j).1⟩
    change RecordedQueueRun.recordService (4 * Q.n) (c.before.registers j)
      (RecordedQueueRun.acceptedRecord Q c.before input j) = 0
    simp only [RecordedQueueRun.acceptedRecord, hov, ite_true, RecordedQueueRun.recordService,
      Bool.false_eq_true, ite_false]

/-- One almost-everywhere archived path statement on the actual produced
sample. Root initialization, retained/renewed native joins, canonical noncalls,
and persistence are simultaneous. Calls are required to join their incoming
seed only through clear PRE, including the first detecting UPDATE. The final
boundary may be `T`; all transitions below have strictly earlier dates. -/
theorem ae_calendarLaw_archived_path (k : ℕ) (hk : t0.val + 1 + k ≤ p.T) :
    ∀ᵐ w ∂law k hk,
      let root := ancestor k 0 (Nat.zero_le _) w
      let o := observe k hk w
      let c := lastNative k hk w
      let a := (original k w).1.2
      lastNative 0 (by omega) root = rootCell root ∧
      stored 0 (by omega) root = ((rootCell root).nextSlowSet,
        calendarNativePrelist rate rewards C_star C_h control0 b0 u0 t0 0 (by omega) root ++ [rootCell root]) ∧
      ((lastNative 0 (by omega) root).before.overflow = false →
        rootEndpoint root = some (lastNative 0 (by omega) root).slowSet) ∧
      noncallCalendar rate rewards C_star C_h o.1 o.2.val.1.1.1.2 a
        (c.nextSlowSet, calendarNativePrelist rate rewards C_star C_h control0 b0 u0 t0 k hk w ++ [c])
        (calendarBoundary t0 k hk).val = some (stored k hk w) ∧
      (stored k hk w).2.Pairwise (fun e f => e.time.val < f.time.val) ∧
      (∀ e ∈ (stored k hk w).2, e.time.val < (calendarBoundary t0 k hk).val) ∧
      (∀ (j : ℕ) (hj : j ≤ k),
        let earlier := ancestor k j hj w
        let prev := observe j (by omega) earlier
        (stored j (by omega) earlier).2 <+: (stored k hk w).2 ∧
        sourcePrefix control0 (t0.val + 1 + j) o.2.val.1.1.1.2 =
          sourcePrefix control0 (t0.val + 1 + j) prev.2.val.1.1.1.2 ∧
        prefixNumerical rate rewards C_star C_h (calendarBoundary t0 j (by omega)) o.2.val.1.1.1.2 =
          prev.2.val.2.2.1 ∧
        ∃ z : InvocationSource rate rewards C_star C_h prev.1,
          z.val = o.2.val.1.1.1.2 ∧
          nativeCell rate rewards C_star C_h control0 prev.1 z
            ((original j earlier).1.2 (prev.1,
              if calendarNativeRenewal rate rewards C_star C_h control0 b0 u0 t0 j (by omega) earlier then 0 else 1)) =
            lastNative j (by omega) earlier) ∧
      (∀ (j : ℕ) (hj : j < k),
        let x : Sample j × Vector := ancestor k (j + 1) (by omega) w
        let q : Fin p.T := ⟨t0.val + 1 + j, by omega⟩
        let prev := observe j (by omega) x.1
        (∀ hc : callFlag j (by omega) x.1 = true,
          (pending j (by omega) x.1).2 = true →
          let cell : Cell := invocation j (by omega) x.1 x.2 hc
          let z := invocationSource j (by omega) x.1 x.2 hc
          let refresh := (original j x.1).1.2 (q, if (pending j (by omega) x.1).1 then 0 else 1)
          (lastFlags j (by omega) x.1).2 = true ∧ 0 < mass j (by omega) x.1 ∧
          ∃ (cutoff : Fin p.T) (theta : Theta),
            sourceCall q prev.2.val.1.1.1.2 = some (cutoff, theta) ∧
            AssignmentParameterFibreKernel.successfulSlowSet p theta x.2 = some cell.slowSet ∧
            (if renewalFlag rate rewards C_star C_h (t := prev.1) q prev.2.val then
              freshEndpoint theta ((original j x.1).1.2 (q, 1))
              else some (stored j (by omega) x.1).1) = some cell.slowSet ∧
            stored (j + 1) (by omega) x = (cell.nextSlowSet, (stored j (by omega) x.1).2 ++ [cell]) ∧
            ((stored j (by omega) x.1).2 ++ [cell]) <+: (stored k hk w).2 ∧
            some cell.before = prev.2.val.2.2.1 ∧
            (observe (j + 1) (by omega) x).2.val.2.2.1 = some cell.after ∧ cell.time = q ∧
            cell = nativeCell rate rewards C_star C_h control0 q z refresh ∧
            cell.proposal = (!cell.before.overflow && ReferenceFirstLivePostUpdateProposalLaw.physicalProposalBit rate
              (ReferenceSourceCurrentControlFreshness.u_t p q z.val)) ∧
            cell.nextSlowSet = (if cell.before.overflow then frozenSlowSet p else
              if cell.proposal then residualDraw rate cell.before (nativeSourceCell rate rewards C_star C_h q z).input
                (nativeSourceCell rate rewards C_star C_h q z).selected.view.payload.anchor
                (nativeSourceCell rate rewards C_star C_h q z).selected.view.payload.anchor_pos refresh
              else (nativeSourceCell rate rewards C_star C_h q z).selected.view.payload.slowSet)) ∧
        (callFlag j (by omega) x.1 = false →
          stored (j + 1) (by omega) x = appendNoncallDate rate rewards C_star C_h q
            prev.2.val.1.1.1.2 (original j x.1).1.2 (stored j (by omega) x.1) ∧
          (noncallDateCell rate rewards C_star C_h q prev.2.val.1.1.1.2
            (original j x.1).1.2 (stored j (by omega) x.1).1).isSome =
              ((ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h q prev.2.val.1.1.1.2).bind
                (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate)).any RecordedQueueRun.RoundInput.enabled ∧
          (noncallDateCell rate rewards C_star C_h q prev.2.val.1.1.1.2
            (original j x.1).1.2 (stored j (by omega) x.1).1 = none →
              stored (j + 1) (by omega) x = stored j (by omega) x.1) ∧
          (∀ e : Cell,
            noncallDateCell rate rewards C_star C_h q prev.2.val.1.1.1.2
              (original j x.1).1.2 (stored j (by omega) x.1).1 = some e →
            stored (j + 1) (by omega) x = (e.nextSlowSet, (stored j (by omega) x.1).2 ++ [e]) ∧
            (observe (j + 1) (by omega) x).2.val.2.2.1 = some e.after ∧
            ((stored j (by omega) x.1).2 ++ [e]) <+: (stored k hk w).2 ∧
            ((pending j (by omega) x.1).2 = true →
              e.slowSet = (stored j (by omega) x.1).1 ∧ some e.before = prev.2.val.2.2.1)) ∧
          calendarExtensionKernel rate rewards C_star C_h control0 b0 u0 t0 j (by omega) x.1 =
            Measure.dirac (ReferenceFirstCollectionRenewalVectorInsertion.av q prev.2.val.1.1.1.2)) ∧
        ((pending j (by omega) x.1).2 = false →
          calendarExtensionKernel rate rewards C_star C_h control0 b0 u0 t0 j (by omega) x.1 =
            Measure.dirac (ReferenceFirstCollectionRenewalVectorInsertion.av q prev.2.val.1.1.1.2) ∧
          ∀ hc : callFlag j (by omega) x.1 = true,
            let cell := invocation j (by omega) x.1 x.2 hc
            cell.slowSet = frozenSlowSet p ∧ cell.fastArm = frozenFastArm p ∧ cell.proposal = false ∧
            cell.nextSlowSet = frozenSlowSet p ∧ ∀ arm, cell.arrivals arm = (false, 0) ∧
              cell.service arm = 0 ∧ cell.after.registers arm = cell.before.registers arm)) := by
  have hroot := ae_calendarLaw_root_join rate rewards C_star C_h control0 b0 u0 t0 (by omega : t0.val + 1 ≤ p.T)
  rw [← calendarLaw_map_ancestor rate rewards C_star C_h control0 b0 u0 t0 k hk 0 (Nat.zero_le _)] at hroot
  filter_upwards [ae_of_ae_map
    (measurable_calendarAncestor rate rewards C_star C_h b0 u0 t0 k 0 (Nat.zero_le _)).aemeasurable hroot,
    ae_calendarLaw_archived_call_joins rate rewards C_star C_h control0 b0 u0 t0 k hk] with w hroot hcalls
  dsimp only
  have hr := calendarObservation_root rate rewards C_star C_h control0 b0 u0 t0 (by omega)
    (ancestor k 0 (Nat.zero_le _) w)
  have hcanonical := calendarObservation_noncall rate rewards C_star C_h control0 b0 u0 t0 k hk w
  have hchronology := calendarObservation_chronology rate rewards C_star C_h control0 b0 u0 t0 k hk w
  refine ⟨hr.1, hr.2.1, hroot, ?_, hchronology.1, hchronology.2, ?_, ?_⟩
  · exact hcanonical.trans (calendarStoredState_spec rate rewards C_star C_h control0 b0 u0 t0 k hk w).symm
  · intro j hj
    have hp := calendarObservation_ancestor_preserves rate rewards C_star C_h control0 b0 u0 t0 k hk w j hj
    exact ⟨hp.1, hp.2.1, hp.2.2,
      calendarObservation_archived_native rate rewards C_star C_h control0 b0 u0 t0 k hk w j hj⟩
  · intro j hj
    let x : Sample j × Vector := ancestor k (j + 1) (by omega) w
    let q : Fin p.T := ⟨t0.val + 1 + j, by omega⟩
    let prev := observe j (by omega) x.1
    refine ⟨?_, ?_, ?_⟩
    · intro hc hclear
      obtain ⟨hnative, hpos, cutoff, theta, hcall, hsample, hjoin, happend, hpost, hbefore, htime⟩ :=
        hcalls j hj hc hclear
      have hp := (calendarObservation_ancestor_preserves rate rewards C_star C_h control0 b0 u0 t0
        k hk w (j + 1) (by omega)).1
      have hp' : ((stored j (by omega) x.1).2 ++ [invocation j (by omega) x.1 x.2 hc]) <+:
          (stored k hk w).2 := by
        change (stored (j + 1) (by omega) x).2 <+: _ at hp
        rw [happend] at hp
        exact hp
      exact ⟨hnative, hpos, cutoff, theta, hcall, hsample, hjoin, happend, hp', hbefore, hpost, htime,
        calendarInvocationCell_update_readouts rate rewards C_star C_h control0 b0 u0 t0 j (by omega) x.1 x.2 hc⟩
    · intro hc
      have hnone : sourceCall q prev.2.val.1.1.1.2 = none := by
        apply Option.not_isSome_iff_eq_none.mp
        change ¬ callFlag j (by omega) x.1 = true
        rw [hc]
        exact Bool.false_ne_true
      refine ⟨calendarObservation_noncall_step rate rewards C_star C_h control0 b0 u0 t0 j (by omega) x.1 x.2 hc,
        calendarObservation_noncall_presence rate rewards C_star C_h control0 b0 u0 t0 j (by omega) x.1 hc,
        calendarObservation_noncall_absent rate rewards C_star C_h control0 b0 u0 t0 j (by omega) x.1 x.2 hc,
        ?_, calendarExtensionKernel_noCall rate rewards C_star C_h control0 b0 u0 t0 j (by omega) x.1 hnone⟩
      intro e he
      obtain ⟨happend, hpost⟩ := calendarObservation_noncall_cell_post rate rewards C_star C_h control0 b0 u0 t0
        j (by omega) x.1 x.2 hc e he
      have hp := (calendarObservation_ancestor_preserves rate rewards C_star C_h control0 b0 u0 t0
        k hk w (j + 1) (by omega)).1
      have hp' : ((stored j (by omega) x.1).2 ++ [e]) <+: (stored k hk w).2 := by
        change (stored (j + 1) (by omega) x).2 <+: _ at hp
        exact Eq.mp (congrArg (fun L : List Cell => L <+: (stored k hk w).2) (congrArg Prod.snd happend)) hp
      refine ⟨happend, hpost, hp', ?_⟩
      intro hclear
      have hs := calendarObservation_noncall_clear_cell rate rewards C_star C_h control0 b0 u0 t0 j (by omega)
        x.1 x.2 hc hclear e he
      exact ⟨hs.1, hs.2.1⟩
    · intro hstop
      refine ⟨calendarExtensionKernel_preStopped rate rewards C_star C_h control0 b0 u0 t0 j (by omega) x.1 hstop, ?_⟩
      intro hc
      exact calendarInvocationCell_stopped rate rewards C_star C_h control0 b0 u0 t0 j (by omega) x.1 x.2 hc hstop

/-- The produced clear-call sampler's failure outcome is null, on its actual
call parameters and entire assignment vector. No normalization is used. -/
theorem calendarLaw_clear_call_failure (k : ℕ) (hk : t0.val + 1 + k < p.T) :
    law (k + 1) (by omega) {wv : Sample k × Vector |
      callFlag k (by omega) wv.1 = true ∧ (pending k (by omega) wv.1).2 = true ∧
      ∀ (cutoff : Fin p.T) (theta : Theta),
        sourceCall ⟨t0.val + 1 + k, hk⟩ (observe k hk.le wv.1).2.val.1.1.1.2 = some (cutoff, theta) →
          AssignmentParameterFibreKernel.successfulSlowSet p theta wv.2 = none} = 0 := by
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [ae_calendarLaw_call_join rate rewards C_star C_h control0 b0 u0 t0 k hk]
    with wv hw hbad
  obtain ⟨_, _, cutoff, theta, hcall, hsample, _⟩ := hw hbad.1 hbad.2.1
  have hnone := hbad.2.2 cutoff theta hcall
  rw [hsample] at hnone
  cases hnone

/-- At the horizon the construction has processed `T-1` and stops at POST
`T`; there is no manufactured outgoing vector at terminal PRE. -/
theorem calendarBoundary_horizon :
    calendarBoundary t0 (p.T - (t0.val + 1)) (by omega) = Fin.last p.T := by
  apply Fin.ext
  dsimp only [calendarBoundary, Fin.val_last]
  have ht := t0.isLt
  omega

/-- Explicit final POST readout of the simultaneous archived-path theorem.
Every earlier cell and its numerical PRE still belongs to the final source. -/
theorem ae_calendarLaw_terminal_path_readout :
    ∀ᵐ w ∂law (p.T - (t0.val + 1)) (by omega),
      let k := p.T - (t0.val + 1)
      let hk : t0.val + 1 + k ≤ p.T := by dsimp only [k]; omega
      let o := observe k hk w
      let c := lastNative k hk w
      noncallCalendar rate rewards C_star C_h o.1 o.2.val.1.1.1.2 (original k w).1.2
        (c.nextSlowSet, calendarNativePrelist rate rewards C_star C_h control0 b0 u0 t0 k hk w ++ [c]) p.T =
          some (stored k hk w) ∧
      (∀ e ∈ (stored k hk w).2, e.time.val < p.T) ∧
      ∀ (j : ℕ) (hj : j ≤ k),
        let earlier := ancestor k j hj w
        (stored j (by omega) earlier).2 <+: (stored k hk w).2 ∧
        prefixNumerical rate rewards C_star C_h (calendarBoundary t0 j (by omega)) o.2.val.1.1.1.2 =
          (observe j (by omega) earlier).2.val.2.2.1 := by
  filter_upwards [ae_calendarLaw_archived_path rate rewards C_star C_h control0 b0 u0 t0
    (p.T - (t0.val + 1)) (by omega)] with w hw
  dsimp only
  have hterminal : (calendarBoundary t0 (p.T - (t0.val + 1)) (by omega)).val = p.T :=
    congrArg Fin.val (calendarBoundary_horizon t0)
  have hcanonical := hw.2.2.2.1
  rw [hterminal] at hcanonical
  have hchronology := hw.2.2.2.2.2.1
  rw [hterminal] at hchronology
  refine ⟨hcanonical, hchronology, ?_⟩
  intro j hj
  have hp := hw.2.2.2.2.2.2.1 j hj
  exact ⟨hp.1, hp.2.2.1⟩

end Bandits.Support.ReferenceGeneratedCalendarPathAgreement
