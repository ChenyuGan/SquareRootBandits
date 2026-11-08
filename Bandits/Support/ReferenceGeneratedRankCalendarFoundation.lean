/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedInvocationCallSplice

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
# Finite generated calendar and unused original-pair factorization

Sources: ZIP4 `06_interruptions.tex:391-426`,
`04_slow_fast_learner.tex:142-215,323-390`, and
`08_main_theorem.tex:78-109`.

This internal finite constructor keeps the entire original branch lift and
all successive full assignment vectors. Its observer uses the canonical native
cell on calls and the canonical successor on noncalls. An original auxiliary
pair at or beyond the current PRE boundary factors from the erased sample;
restoration recovers the full joint sample, including all prior vectors.

This does not establish a last-call UPDATE residual jointly with every future
auxiliary, generated PRE-list/segment preservation, endpoint mixture laws,
first-next joint splice/rebase, arbitrary-boundary original-source marginals,
or generated-past logical laws and payoff. No manuscript closure is asserted.
-/

@[expose] public section

noncomputable section

open scoped Classical
open Bandits.Support ConstructorDimensions
open ReferenceFirstLiveChronologicalPrefixFoundation
open ReferenceFirstNextInstallationTransitionLaw
open ReferenceFirstNextInstallationCellFactors
open ReferencePostInvocationNoncallGeometry
open ReferenceFirstCollectionLogicalPrefixExtension (noCallAt)
open ReferenceGeneratedInvocationCallSplice

namespace Bandits.Support.ReferenceGeneratedRankCalendarFoundation

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)

local notation "NativeSource" => InvocationSource rate rewards C_star C_h
local notation "AuxiliaryArray" => ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p
local notation "FullVector" => AssignmentParameterFibreKernel.AssignmentVector p
local notation "TimeControls" => ContinuousLearningRows.TimeControl p
local notation "UniformScalar" => ContinuousControlSlice.Scalar
local notation "insertVector" => ReferenceFirstCollectionRenewalVectorInsertion.insert
local notation "nativeCellAt" => nativeCell rate rewards C_star C_h
local notation "numericalAt" => prefixNumerical rate rewards C_star C_h
local notation "sourceCall" => ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h
local notation "CallFree" => NoCallBetween rate rewards C_star C_h

/-- Call selection uses the strict physical prefix, which insertion at the
same or a later date preserves. No geometry from an unaccepted module is used. -/
private theorem callAt_insert (control0 : TimeControls) (q v : Fin p.T)
    (hvq : v.val ≤ q.val) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (vector : FullVector) : sourceCall v (insertVector q z vector) = sourceCall v z := by
  have hf := ReferenceCalendarCollectionCallControlLaw.callAt_factor
    rate rewards C_star C_h control0 v
  calc
    sourceCall v (insertVector q z vector) = sourceCall v
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 v.val
          (insertVector q z vector)) := hf _
    _ = sourceCall v (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 v.val z) := by
      exact congrArg (sourceCall v)
        (ReferenceFirstCollectionOldRecorderFoundation.sourcePrefix_replaceCurrent
          control0 q v.val hvq z (ReferenceFirstCollectionRenewalVectorInsertion.ctrl q z vector))
    _ = sourceCall v z := (hf z).symm

section FiniteCalendar

open MeasureTheory
open ReferencePostInvocationPrefixLocality
open ReferencePostInvocationSupportedDisintegration
open ReferencePostInvocationKilledJointLaw
open ReferenceNextRetainedEndpointFibreLaw

local instance sourceMeasurableSpace : MeasurableSpace (BootstrapPrivateRoundStreams.SourceInput p) := by
  change MeasurableSpace (CompletePublicTable.PublishedOutput p ×
    BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance
local instance controlMeasurableSpace : MeasurableSpace TimeControls :=
  ReferencePostInvocationSupportedDisintegration.controlMeasurableSpace
local instance optionMeasurableSpace {X : Type*} [MeasurableSpace X] :
    MeasurableSpace (Option X) := LaterAssignmentStartMeasurability.optionMeasurableSpace
local instance slowSetMeasurableSpace : MeasurableSpace (SlowSet p) := ⊤
local instance slowSetDiscrete : DiscreteMeasurableSpace (SlowSet p) := ⟨fun _ => trivial⟩

private theorem measurable_sigma_mk {I : Type*} {B : I → Type*}
    [∀ i, MeasurableSpace (B i)] (i : I) : Measurable (Sigma.mk i : B i → Sigma B) :=
  measurable_iff_le_map.mpr (iInf_le _ i)

private theorem measurableEmbedding_sigma_mk {I : Type*} {B : I → Type*}
    [∀ i, MeasurableSpace (B i)] (i : I) : MeasurableEmbedding (Sigma.mk i : B i → Sigma B) := by
  refine ⟨fun _ _ h => by cases h; rfl, measurable_sigma_mk i, ?_⟩
  intro U hU
  apply MeasurableSpace.measurableSet_iInf.mpr
  intro j
  change MeasurableSet (Sigma.mk j ⁻¹' (Sigma.mk i '' U))
  by_cases h : j = i
  · subst j
    simpa only [sigma_mk_preimage_image_eq_self] using hU
  · rw [sigma_mk_preimage_image' (Ne.symm h)]
    exact MeasurableSet.empty

theorem measurable_sigma_prod_elim {I V X : Type*} {B : I → Type*}
    [Countable I] [∀ i, MeasurableSpace (B i)] [MeasurableSpace V] [MeasurableSpace X]
    (f : Sigma B × V → X) (hf : ∀ i, Measurable (fun bv : B i × V => f (⟨i, bv.1⟩, bv.2))) : Measurable f := by
  intro U hU
  have heq : f ⁻¹' U = ⋃ i, (Prod.map (Sigma.mk i) id) '' ((fun bv : B i × V => f (⟨i, bv.1⟩, bv.2)) ⁻¹' U) := by
    ext w
    constructor
    · intro hw
      exact Set.mem_iUnion.mpr ⟨w.1.1, ⟨(w.1.2, w.2), hw, rfl⟩⟩
    · rintro ⟨_, ⟨i, rfl⟩, y, hy, rfl⟩
      exact hy
  rw [heq]
  exact MeasurableSet.iUnion fun i =>
    ((measurableEmbedding_sigma_mk i).prodMap MeasurableEmbedding.id).measurableSet_image.mpr (hf i hU)

private theorem measurable_of_some {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]
    (f : X → A) (hf : Measurable (fun x => some (f x))) : Measurable f := by
  have hinl : MeasurableEmbedding (@Sum.inl A PUnit) :=
    ⟨Sum.inl_injective, measurable_inl, fun _ hs => hs.inl_image⟩
  exact hinl.measurable_comp_iff.mp ((comap_measurable (Equiv.optionEquivSumPUnit A)).comp hf)

/-- A literal event subspace of the canonical prefix carrier. The sole proof
allows Option.get; it asserts no numerical, rank, endpoint or law invariant. -/
abbrev PresentPrefix (s : Fin p.T) (n : Fin (p.T + 1)) := {o : PrefixObservation rate s n // o.2.2.2.isSome = true}

/-- The finite tag records the last invocation date; rank is never a field. -/
abbrev TaggedPrefix (n : Fin (p.T + 1)) := Σ s : Fin p.T, PresentPrefix rate s n

variable (control0 : ContinuousLearningRows.TimeControl p)

def calendarCallEvent (s q : Fin p.T) : Set (PresentPrefix rate s q.castSucc × (AuxiliaryArray ×
        FullVector)) := {x | (sourceCall q x.1.val.1.1.1.2).isSome = true}

local notation "CallEvent" => calendarCallEvent rate rewards C_star C_h

include control0 in
theorem measurableSet_calendarCallEvent (s q : Fin p.T) : MeasurableSet (CallEvent s q) := by
  have h : Measurable (fun x : PresentPrefix rate s q.castSucc × (AuxiliaryArray × FullVector) =>
      sourceCall q x.1.val.1.1.1.2) := ((ReferenceCalendarCollectionCallControlLaw.callAt_measurable
    rate rewards C_star C_h control0 q).mono
      ((ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le (q.val + 1)) le_rfl).comp
    (measurable_fst.fst.fst.snd.comp (measurable_subtype_coe.comp measurable_fst))
  have his : Measurable (Option.isSome : ReferenceCalendarCollectionCallControlLaw.CallAt p → Bool) := by
    convert ((measurable_const : Measurable (fun _ : Fin p.T ×
      AssignmentParameterFibreKernel.Theta p => true)).sumElim
      (measurable_const : Measurable (fun _ : PUnit => false))).comp
      (comap_measurable (Equiv.optionEquivSumPUnit _)) using 1
    funext o
    cases o <;> rfl
  exact measurableSet_eq_fun (his.comp h) measurable_const

def calendarCallSource (s q : Fin p.T) (x : CallEvent s q) : NativeSource q :=
  ⟨insertVector q x.val.1.val.1.1.1.2 x.val.2.2, by
    rw [callAt_insert rate rewards C_star C_h control0 q q le_rfl]
    exact x.property⟩

local notation "callSource" => calendarCallSource rate rewards C_star C_h control0

theorem measurable_calendarCallSource (s q : Fin p.T) : Measurable (callSource s q) :=
  ((ReferenceFirstCollectionRenewalVectorInsertion.measurable_insert (t := q)).comp
    ((measurable_fst.fst.fst.snd.comp (measurable_subtype_coe.comp
      (measurable_fst.comp measurable_subtype_coe))).prodMk
        (measurable_snd.snd.comp measurable_subtype_coe))).subtype_mk

/-- Actual call transition using the surviving PRE list and original tape.
Stopped PRE inputs use the same native frozen-cell branch. -/
def calendarCallTransition (s q : Fin p.T) (x : CallEvent s q) : TransitionData rate q :=
  let o := x.val.1.val
  let a := x.val.2.1
  let vector := x.val.2.2
  let z := callSource s q x
  let renewal := renewalFlag rate rewards C_star C_h (t := s) q o
  let c := nativeCellAt control0 q z (if renewal then a (q, 0) else a (q, 1))
  ((((o.1.1.1.2, (futureAuxiliarySplit q renewal a).1), vector), ((o.2.2.2.get x.val.1.property).2, (z.val, c))))

local notation "callTransitionAt" => calendarCallTransition rate rewards C_star C_h control0

theorem measurable_calendarCallTransition (s q : Fin p.T) : Measurable (callTransitionAt s q) := by
  have hx := (measurable_subtype_coe : Measurable (Subtype.val : CallEvent s q → _))
  have ho := measurable_subtype_coe.comp (measurable_fst.comp hx)
  have ha := measurable_snd.fst.comp hx
  have hv := measurable_snd.snd.comp hx
  have hz := measurable_calendarCallSource rate rewards C_star C_h control0 s q
  have hb := (measurable_renewalFlag rate rewards C_star C_h (t := s) q).comp ho
  have hr : Measurable (fun x : CallEvent s q =>
      if renewalFlag rate rewards C_star C_h (t := s) q x.val.1.val then x.val.2.1 (q, 0) else x.val.2.1 (q, 1)) :=
    ((measurable_pi_apply (q, 0)).comp ha).ite (measurableSet_eq_fun hb (measurable_const (a := true)))
      ((measurable_pi_apply (q, 1)).comp ha)
  have hc := (measurable_nativeCell rate rewards C_star C_h control0 q).comp (hz.prodMk hr)
  have hp : Measurable (fun x : CallEvent s q =>
      (x.val.1.val.2.2.2.get x.val.1.property)) := by
    apply measurable_of_some
    convert ho.snd.snd.snd using 1
    funext x
    exact Option.some_get _
  have hsplit : Measurable (fun ba : Bool × AuxiliaryArray =>
      (futureAuxiliarySplit q ba.1 ba.2).1) :=
    measurable_from_prod_countable_right fun c => (futureAuxiliarySplit q c).measurable.fst
  have he := hsplit.comp (hb.prodMk ha)
  exact ((ho.fst.fst.fst.snd.prodMk he).prodMk hv).prodMk
    (hp.snd.prodMk ((measurable_subtype_coe.comp hz).prodMk hc))

def calendarCallInitial (s q : Fin p.T) (x : CallEvent s q) : InitialObservation rate q :=
  let d := callTransitionAt s q x
  (((d.1.1.1, insertedPhysicalSource rate d), d.1.2),
    (usedAuxiliary q x.val.2.1, postHistory d))

local notation "callInitialAt" => calendarCallInitial rate rewards C_star C_h control0

theorem measurable_calendarCallInitial (s q : Fin p.T) : Measurable (callInitialAt s q) := by
  have hd := measurable_calendarCallTransition rate rewards C_star C_h control0 s q
  exact ((hd.fst.fst.fst.prodMk hd.snd.snd.fst).prodMk hd.fst.snd).prodMk
    (((measurable_usedAuxiliary q).comp (measurable_snd.fst.comp measurable_subtype_coe)).prodMk
      ((measurable_postHistory rate q).comp hd))

def calendarCallPrefix (s q : Fin p.T) (x : CallEvent s q) : PresentPrefix rate q q.succ :=
  ⟨initialExtension rate rewards C_star C_h q (callInitialAt s q x), by
    change ((postHistory (callTransitionAt s q x)).getLast?.map _).isSome = true
    rw [postHistory_last]
    rfl⟩

local notation "callPrefixAt" => calendarCallPrefix rate rewards C_star C_h control0

theorem measurable_calendarCallPrefix (s q : Fin p.T) : Measurable (callPrefixAt s q) :=
  ((measurable_initialExtension rate rewards C_star C_h q).comp
    (measurable_calendarCallInitial rate rewards C_star C_h control0 s q)).subtype_mk

def calendarNoncallPrefix (s q : Fin p.T) (x : PresentPrefix rate s q.castSucc × AuxiliaryArray) :
    PresentPrefix rate s q.succ := ⟨successor rate rewards C_star C_h s q
    (x.1.val, ReferenceFirstNextLiftFutureAuxiliaryPairLaw.auxiliaryPair q x.2), by
    change (x.1.val.2.2.2.map _).isSome = true
    simpa only [Option.isSome_map] using x.1.property⟩

local notation "noncallPrefixAt" => calendarNoncallPrefix rate rewards C_star C_h

include control0 in
theorem measurable_calendarNoncallPrefix (s q : Fin p.T) : Measurable (noncallPrefixAt s q) :=
  ((measurable_successor rate rewards C_star C_h s q control0).comp
    ((measurable_subtype_coe.comp measurable_fst).prodMk
      ((ReferenceFirstNextLiftFutureAuxiliaryPairLaw.measurable_auxiliaryPair q).comp
        measurable_snd))).subtype_mk

/-- One actual date: noncalls use the canonical successor; calls append a
native cell and rebase. No numerical PRE is taken from the last POST. -/
def calendarStep (q : Fin p.T) (x : TaggedPrefix rate q.castSucc × (AuxiliaryArray ×
        FullVector)) : TaggedPrefix rate q.succ := if hc : (x.1.2, x.2) ∈ CallEvent x.1.1 q then
    ⟨q, callPrefixAt x.1.1 q ⟨(x.1.2, x.2), hc⟩⟩
  else ⟨x.1.1, noncallPrefixAt x.1.1 q (x.1.2, x.2.1)⟩

local notation "advance" => calendarStep rate rewards C_star C_h control0

theorem measurable_calendarStep (q : Fin p.T) : Measurable (advance q) := by
  apply measurable_sigma_prod_elim
  intro s
  have hc := measurable_calendarCallPrefix rate rewards C_star C_h control0 s q
  have hc' := (measurable_sigma_mk (B := fun s => PresentPrefix rate s q.succ) q).comp hc
  have hn : Measurable (fun x : ↥((CallEvent s q)ᶜ) =>
      noncallPrefixAt s q (x.val.1, x.val.2.1)) :=
    (measurable_calendarNoncallPrefix rate rewards C_star C_h control0 s q).comp
      ((measurable_fst.comp measurable_subtype_coe).prodMk
        (measurable_snd.fst.comp measurable_subtype_coe))
  have hn' := (measurable_sigma_mk (B := fun s => PresentPrefix rate s q.succ) s).comp hn
  exact hc'.dite hn' (measurableSet_calendarCallEvent rate rewards C_star C_h control0 s q)

/-- Finite coproduct of the existing next-vector kernels; the actual
calendar samples, rather than a supplied law, determine its inputs below. -/
def calendarVectorKernel (q : Fin p.T) : ProbabilityTheory.Kernel
    (TaggedPrefix rate q.castSucc × AuxiliaryArray) FullVector where
  toFun x := nextVectorKernel rate rewards C_star C_h (t := x.1.1) (q := q) control0
    (x.1.2.val, ReferenceFirstNextLiftFutureAuxiliaryPairLaw.auxiliaryPair q x.2)
  measurable' := measurable_sigma_prod_elim _ fun s =>
    (nextVectorKernel rate rewards C_star C_h (t := s) (q := q) control0).measurable.comp
      ((measurable_subtype_coe.comp measurable_fst).prodMk
        ((ReferenceFirstNextLiftFutureAuxiliaryPairLaw.measurable_auxiliaryPair q).comp measurable_snd))

instance calendarVectorKernel_markov (q : Fin p.T) :
    ProbabilityTheory.IsMarkovKernel (calendarVectorKernel rate rewards C_star C_h control0 q) where
  isProbabilityMeasure x :=
    (ReferenceNextRetainedEndpointFibreLaw.nextVectorKernel_markov
      rate rewards C_star C_h (t := x.1.1) (q := q) control0).isProbabilityMeasure _

/-- The actual Borel kernel on a tagged prefix uses its original date-pair. -/
theorem calendarVectorKernel_apply (q : Fin p.T)
    (x : TaggedPrefix rate q.castSucc × AuxiliaryArray) :
    calendarVectorKernel rate rewards C_star C_h control0 q x =
      nextVectorKernel rate rewards C_star C_h (t := x.1.1) (q := q) control0
        (x.1.2.val, ReferenceFirstNextLiftFutureAuxiliaryPairLaw.auxiliaryPair q x.2) := rfl

/-- A date's native transition reads only original labels through that date.
The current source in the observer may already contain earlier insertions. -/
theorem calendarStep_auxiliary_ext (q : Fin p.T) (o : TaggedPrefix rate q.castSucc)
    (a a' : AuxiliaryArray) (v : FullVector) (ha : ∀ j, j.1.val ≤ q.val → a j = a' j) :
    advance q (o, (a, v)) = advance q (o, (a', v)) := by
  by_cases hc : (o.2, (a, v)) ∈ CallEvent o.1 q
  · have hc' : (o.2, (a', v)) ∈ CallEvent o.1 q := hc
    rw [calendarStep, dite_eq_left hc, calendarStep, dite_eq_left hc']
    apply congrArg (Sigma.mk q)
    apply Subtype.ext
    apply congrArg (initialExtension rate rewards C_star C_h q)
    dsimp only [calendarCallInitial, calendarCallTransition, insertedPhysicalSource, postHistory]
    rw [show usedAuxiliary q a = usedAuxiliary q a' from funext fun j => ha j.val j.property,
      ha (q, 0) le_rfl, ha (q, 1) le_rfl]
    rfl
  · have hc' : ¬ (o.2, (a', v)) ∈ CallEvent o.1 q := hc
    rw [calendarStep, dite_eq_right hc, calendarStep, dite_eq_right hc']
    apply congrArg (Sigma.mk o.1)
    apply Subtype.ext
    change successor rate rewards C_star C_h o.1 q (o.2.val, (a (q, 0), a (q, 1))) = _
    rw [ha (q, 0) le_rfl, ha (q, 1) le_rfl]
    rfl

/-- The call kernel leaves the original UPDATE label unused. Renewal's
initialization still consumes label one; all other original labels remain. -/
theorem calendarVectorKernel_update_nonuse (q : Fin p.T) (o : TaggedPrefix rate q.castSucc)
    (a : AuxiliaryArray) (x : UniformScalar) :
    let b := renewalFlag rate rewards C_star C_h (t := o.1) q o.2.val
    calendarVectorKernel rate rewards C_star C_h control0 q
      (o, Function.update a (q, if b then 0 else 1) x) =
    calendarVectorKernel rate rewards C_star C_h control0 q (o, a) := by
  dsimp only [calendarVectorKernel]
  cases hb : renewalFlag rate rewards C_star C_h (t := o.1) q o.2.val <;>
    simp [nextVectorKernel_apply, installationSelection, installationEndpoint, endpointChoice,
      ReferenceFirstNextLiftFutureAuxiliaryPairLaw.auxiliaryPair, currentVector, hb]

variable (b : Bool) (u t : Fin p.T)

/-- Raw finite sample: retain the complete original branch lift and every
successive full K+1 vector. The index counts calendar dates, never rank. -/
def CalendarSample : ℕ → Type
  | 0 => BranchLift rate rewards C_star C_h b u t
  | k + 1 => CalendarSample k × FullVector

local notation "Sample" => CalendarSample rate rewards C_star C_h b u t

instance calendarSampleMeasurable (k : ℕ) : MeasurableSpace (Sample k) := by
  induction k with
  | zero => exact inferInstanceAs (MeasurableSpace (BranchLift rate rewards C_star C_h b u t))
  | succ k ih => exact @Prod.instMeasurableSpace _ _ ih inferInstance

def calendarOriginalLift : (k : ℕ) → Sample k → BranchLift rate rewards C_star C_h b u t
  | 0, w => w
  | k + 1, w => calendarOriginalLift k w.1

local notation "original" => calendarOriginalLift rate rewards C_star C_h b u t

theorem measurable_calendarOriginalLift (k : ℕ) : Measurable (original k) := by
  induction k with
  | zero => exact measurable_id
  | succ k ih => exact ih.comp measurable_fst

def calendarBoundary (k : ℕ) (hk : t.val + 1 + k ≤ p.T) : Fin (p.T + 1) := ⟨t.val + 1 + k, Nat.lt_succ_of_le hk⟩

def calendarObservation : (k : ℕ) → (hk : t.val + 1 + k ≤ p.T) →
    Sample k → TaggedPrefix rate (calendarBoundary t k hk)
  | 0, _hk, w => ⟨t, ⟨branchObservation rate rewards C_star C_h control0 b u t t.succ w, by
      change BranchLift rate rewards C_star C_h b u t at w
      rw [branchObservation_prefix, postInvocationPrefix, Fin.val_succ,
        noncallCalendar_initial rate rewards C_star C_h t _ _ _ (t.val + 1) le_rfl]
      rfl⟩⟩
  | k + 1, hk, w => advance ⟨t.val + 1 + k, by omega⟩ (calendarObservation k (by omega) w.1,
        ((original k w.1).1.2, w.2))

local notation "observe" => calendarObservation rate rewards C_star C_h control0 b u t

theorem measurable_calendarObservation (k : ℕ) (hk : t.val + 1 + k ≤ p.T) : Measurable (observe k hk) := by
  induction k with
  | zero =>
      exact (measurable_sigma_mk (B := fun s => PresentPrefix rate s t.succ) t).comp
        (measurable_branchObservation rate rewards C_star C_h control0 b u t t.succ).subtype_mk
  | succ k ih =>
      exact (measurable_calendarStep rate rewards C_star C_h control0 _).comp
        ((ih (by omega)).comp measurable_fst |>.prodMk
          (((measurable_calendarOriginalLift rate rewards C_star C_h b u t k).fst.snd.comp
            measurable_fst).prodMk measurable_snd))

/-- Evaluate the finite coproduct on the constructed observer and original
tape. This performs no new sampler calculation. -/
def calendarExtensionKernel (k : ℕ) (hk : t.val + 1 + (k + 1) ≤ p.T) :
    ProbabilityTheory.Kernel (Sample k) FullVector :=
  (calendarVectorKernel rate rewards C_star C_h control0 ⟨t.val + 1 + k, by omega⟩).comap
    (fun w => (observe k (by omega) w, (original k w).1.2))
    ((measurable_calendarObservation rate rewards C_star C_h control0 b u t k (by omega)).prodMk
      (measurable_calendarOriginalLift rate rewards C_star C_h b u t k).fst.snd)

local notation "extension" => calendarExtensionKernel rate rewards C_star C_h control0 b u t

theorem calendarExtensionKernel_apply (k : ℕ) (hk : t.val + 1 + (k + 1) ≤ p.T)
    (w : Sample k) : extension k hk w =
      calendarVectorKernel rate rewards C_star C_h control0 ⟨t.val + 1 + k, by omega⟩
        (observe k (by omega) w, (original k w).1.2) := rfl

instance calendarExtensionKernel_markov (k : ℕ) (hk : t.val + 1 + (k + 1) ≤ p.T) :
    ProbabilityTheory.IsMarkovKernel (extension k hk) where
  isProbabilityMeasure _w :=
    (calendarVectorKernel_markov rate rewards C_star C_h control0 _).isProbabilityMeasure _

def calendarLaw : (k : ℕ) → (hk : t.val + 1 + k ≤ p.T) → Measure (Sample k)
  | 0, _ => branchLaw rate rewards C_star C_h control0 b u t
  | k + 1, hk => (calendarLaw k (by omega)).compProd (extension k hk)

local notation "law" => calendarLaw rate rewards C_star C_h control0 b u t

instance calendarLaw_finite (k : ℕ) (hk : t.val + 1 + k ≤ p.T) : IsFiniteMeasure (law k hk) := by
  induction k with
  | zero => exact ReferencePostInvocationKilledJointLaw.branchLaw_finite _ _ _ _ _ _ _ _
  | succ k ih =>
      have : IsFiniteMeasure (law k (by omega)) := ih (by omega)
      change IsFiniteMeasure ((law k (by omega)).compProd _)
      infer_instance

/-- The whole previous sample survives jointly, including all complete
sources, the original tape, and every earlier full vector. -/
theorem calendarLaw_succ_map_fst (k : ℕ) (hk : t.val + 1 + (k + 1) ≤ p.T) :
    (law (k + 1) hk).map Prod.fst = law k (by omega) := Measure.fst_compProd _ _

/-- Full Borel characterization of the produced successor law, with no
assumed law for the source contained in its sample. -/
theorem calendarLaw_succ_apply (k : ℕ) (hk : t.val + 1 + (k + 1) ≤ p.T)
    (S : Set (Sample (k + 1))) (hS : MeasurableSet S) :
    law (k + 1) hk S = ∫⁻ w, extension k hk w (Prod.mk w ⁻¹' S)
      ∂law k (by omega) := Measure.compProd_apply hS

/-- Every extension retains the complete original raw lift with its accepted
branch law. This marginal includes its original physical source and tape. -/
theorem calendarLaw_map_originalLift (k : ℕ) (hk : t.val + 1 + k ≤ p.T) :
    (law k hk).map (original k) = branchLaw rate rewards C_star C_h control0 b u t := by
  induction k with
  | zero => exact Measure.map_id
  | succ k ih =>
      calc
        _ = ((law (k + 1) hk).map Prod.fst).map (original k) :=
          (Measure.map_map (measurable_calendarOriginalLift rate rewards C_star C_h b u t k)
            measurable_fst).symm
        _ = (law k (by omega)).map (original k) :=
          congrArg (fun m : Measure (Sample k) => m.map (original k))
            (calendarLaw_succ_map_fst rate rewards C_star C_h control0 b u t k hk)
        _ = _ := ih (by omega)

/-- The finite construction neither normalizes the branch nor loses its mass. -/
theorem calendarLaw_mass (k : ℕ) (hk : t.val + 1 + k ≤ p.T) :
    law k hk Set.univ = branchLaw rate rewards C_star C_h control0 b u t Set.univ := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change ((law k (by omega)).compProd (extension k hk)) Set.univ = _
      rw [Measure.compProd_apply_univ]
      exact ih (by omega)

/-- The initial observer is literally the canonical extension of the accepted
branch initializer, with the full initial source, list, seed and labels. -/
theorem calendarObservation_initial (hk : t.val + 1 ≤ p.T) (w : Sample 0) :
    (observe 0 (by omega) w).2.val = initialExtension rate rewards C_star C_h t
      (branchInitial rate rewards C_star C_h control0 b u t w) :=
  branchObservation_initial rate rewards C_star C_h control0 b u t w

/-- Initializer and initial prefix are identified jointly, rather than by
separate marginals. No arbitrary-rank original-source marginal is asserted. -/
theorem calendarLaw_initial_joint (hk : t.val + 1 ≤ p.T) :
    (law 0 (by omega)).map (fun w =>
      (branchInitial rate rewards C_star C_h control0 b u t w, (observe 0 (by omega) w).2.val)) =
    (postCellLaw rate rewards C_star C_h control0 b u t).map
      (fun i => (i, initialExtension rate rewards C_star C_h t i)) := by
  rw [postCellLaw_eq_map]
  calc
    _ = (branchLaw rate rewards C_star C_h control0 b u t).map
        ((fun i => (i, initialExtension rate rewards C_star C_h t i)) ∘
          branchInitial rate rewards C_star C_h control0 b u t) := by
      apply Measure.map_congr
      exact Filter.Eventually.of_forall fun w =>
        Prod.ext rfl (calendarObservation_initial rate rewards C_star C_h control0 b u t hk w)
    _ = _ := (Measure.map_map
      (measurable_id.prodMk (measurable_initialExtension rate rewards C_star C_h t))
        (measurable_branchInitial rate rewards C_star C_h control0 b u t)).symm

/-- The constructor's actual initial marginal is the accepted post-cell law
rebased by the canonical initial extension. -/
theorem calendarLaw_initial (hk : t.val + 1 ≤ p.T) : (law 0 (by omega)).map
      (branchObservation rate rewards C_star C_h control0 b u t t.succ) =
    (postCellLaw rate rewards C_star C_h control0 b u t).map (initialExtension rate rewards C_star C_h t) := by
  rw [postCellLaw_eq_map, Measure.map_map (measurable_initialExtension rate rewards C_star C_h t)
    (measurable_branchInitial rate rewards C_star C_h control0 b u t)]
  apply Measure.map_congr
  exact Filter.Eventually.of_forall (branchObservation_initial rate rewards C_star C_h control0 b u t)

/-- The initializer appends exactly its surviving PRE list and rebases to
its own native POST numerical state and native residual seed. -/
theorem calendarCallPrefix_alignment (s q : Fin p.T) (x : CallEvent s q) :
    let d := callTransitionAt s q x
    (callPrefixAt s q x).val.2.2.1 = some d.2.2.2.after ∧
    (callPrefixAt s q x).val.2.2.2 =
      some (d.2.2.2.nextSlowSet, (x.val.1.val.2.2.2.get x.val.1.property).2 ++ [d.2.2.2]) := by
  constructor
  · exact nativeCell_after_prefix rate rewards C_star C_h control0 q (callSource s q x) _
  · change (postHistory (callTransitionAt s q x)).getLast?.map _ = _
    rw [postHistory_last]
    rfl

private theorem installationEvent_call (k : ℕ) (q : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : z ∈ ReferenceRankInstallationRecorderFoundation.installationEvent rate rewards C_star C_h k q) :
    (sourceCall q z).isSome = true := by
  obtain ⟨u, hu⟩ := Set.mem_iUnion.mp hz
  obtain ⟨⟨cutoff, theta⟩, hn, _⟩ := Option.map_eq_some_iff.mp hu
  rw [((ReferenceCollectionSamplerChronology.nthAt_eq_some_iff
    rate rewards C_star C_h k q z cutoff theta).mp hn).2]
  rfl

private theorem calendarStep_origin (q : Fin p.T) (x : TaggedPrefix rate q.castSucc × (AuxiliaryArray ×
        FullVector)) (hdate : x.1.1.val < q.val) (hcall : (sourceCall x.1.1 x.1.2.val.1.1.1.2).isSome = true)
    (hfree : CallFree x.1.1 q.castSucc x.1.2.val.1.1.1.2) :
    let o := advance q x
    o.1.val < q.succ.val ∧ (sourceCall o.1 o.2.val.1.1.1.2).isSome = true ∧
      CallFree o.1 q.succ o.2.val.1.1.1.2 := by
  by_cases hc : (x.1.2, x.2) ∈ CallEvent x.1.1 q
  · rw [calendarStep, dite_eq_left hc]
    exact ⟨Nat.lt_succ_self _, (callSource x.1.1 q ⟨(x.1.2, x.2), hc⟩).property,
      noCallBetween_initial rate rewards C_star C_h q _⟩
  · rw [calendarStep, dite_eq_right hc]
    have hn : noCallAt rate rewards C_star C_h q x.1.2.val.1.1.1.2 := by
      rw [ReferenceFirstCollectionLogicalPrefixExtension.noCallAt_iff_callAt_none]
      exact Option.not_isSome_iff_eq_none.mp hc
    exact ⟨hdate.trans (Nat.lt_succ_self _), hcall,
      (noCallBetween_succ rate rewards C_star C_h x.1.1 q _).mpr ⟨hfree, fun _ => hn⟩⟩

/-- The constructed tag is an actual invocation of the same source, and
there is no later call before the current boundary, including at the horizon. -/
theorem calendarObservation_origin (k : ℕ) (hk : t.val + 1 + k ≤ p.T) (w : Sample k) :
    let o := observe k hk w
    o.1.val < (calendarBoundary t k hk).val ∧ (sourceCall o.1 o.2.val.1.1.1.2).isSome = true ∧
      CallFree o.1 (calendarBoundary t k hk) o.2.val.1.1.1.2 := by
  induction k with
  | zero =>
      change BranchLift rate rewards C_star C_h b u t at w
      refine ⟨Nat.lt_succ_self _, ?_, noCallBetween_initial rate rewards C_star C_h t _⟩
      have hs := ReferencePostInvocationRetainedEndpointRecurrence.producedSource_val
        rate rewards C_star C_h control0 b u t w
      change (sourceCall t
        (branchObservation rate rewards C_star C_h control0 b u t t.succ w).1.1.1.2).isSome = true
      rw [branchObservation_source, ← hs]
      exact installationEvent_call rate rewards C_star C_h 0 t _
        (ReferencePostInvocationRetainedEndpointRecurrence.producedSource rate rewards C_star C_h b u t w).property
  | succ k ih =>
      obtain ⟨hd, hc, hf⟩ := ih (by omega) w.1
      exact calendarStep_origin rate rewards C_star C_h control0 _ _ hd hc hf

private theorem calendarStep_numerical (q : Fin p.T)
    (x : TaggedPrefix rate q.castSucc × (AuxiliaryArray × FullVector)) :
    let o := advance q x
    o.2.val.2.2.1 = numericalAt q.succ o.2.val.1.1.1.2 := by
  unfold calendarStep
  split <;> rfl

/-- Every constructed PRE numerical readout is recomputed from its complete
current source word, including disabled dates and the terminal boundary. -/
theorem calendarObservation_numerical (k : ℕ) (hk : t.val + 1 + k ≤ p.T) (w : Sample k) :
    let o := observe k hk w
    o.2.val.2.2.1 = numericalAt (calendarBoundary t k hk) o.2.val.1.1.1.2 := by
  cases k with
  | zero => cases b <;> rfl
  | succ k => exact calendarStep_numerical rate rewards C_star C_h control0 _ _

/-- Actual unnormalized branch-rooted finite calendar measure. Original auxiliaries
are read from the original lift; no new auxiliary tape is sampled. This
literal construction alone does not prove its arbitrary-rank source marginal. -/
def generatedCalendarLaw (n : Fin (p.T + 1)) (htn : t.val < n.val) :
    Measure (Sample (n.val - (t.val + 1))) := law (n.val - (t.val + 1)) (by omega)

/-- Its canonical tagged observer, obtained from that same finite sample. -/
def generatedCalendarObservation (n : Fin (p.T + 1)) (htn : t.val < n.val)
    (w : Sample (n.val - (t.val + 1))) : TaggedPrefix rate n := by
  have hboundary : calendarBoundary t (n.val - (t.val + 1)) (by omega) = n :=
    Fin.ext (by dsimp only [calendarBoundary]; omega)
  exact hboundary ▸ observe _ (by omega) w

private theorem measurable_transport_prefix {X : Type*} [MeasurableSpace X]
    {n m : Fin (p.T + 1)} (h : n = m) (f : X → TaggedPrefix rate n)
    (hf : Measurable f) : Measurable (fun x => h ▸ f x) := by
  cases h
  exact hf

theorem measurable_generatedCalendarObservation (n : Fin (p.T + 1)) (htn : t.val < n.val) :
    Measurable (generatedCalendarObservation rate rewards C_star C_h control0 b u t n htn) := by
  exact measurable_transport_prefix rate _ _
    (measurable_calendarObservation rate rewards C_star C_h control0 b u t _ _)

/-- Literal finite-boundary measure, including the terminal boundary `n=T`. -/
theorem generatedCalendarLaw_apply (n : Fin (p.T + 1)) (htn : t.val < n.val)
    (S : Set (Sample (n.val - (t.val + 1)))) :
    generatedCalendarLaw rate rewards C_star C_h control0 b u t n htn S =
      law (n.val - (t.val + 1)) (by omega) S := rfl

instance generatedCalendarLaw_finite (n : Fin (p.T + 1)) (htn : t.val < n.val) :
    IsFiniteMeasure (generatedCalendarLaw rate rewards C_star C_h control0 b u t n htn) :=
  calendarLaw_finite rate rewards C_star C_h control0 b u t _ _

theorem generatedCalendarLaw_map_originalLift (n : Fin (p.T + 1)) (htn : t.val < n.val) :
    (generatedCalendarLaw rate rewards C_star C_h control0 b u t n htn).map
      (original (n.val - (t.val + 1))) = branchLaw rate rewards C_star C_h control0 b u t :=
  calendarLaw_map_originalLift rate rewards C_star C_h control0 b u t _ _

theorem generatedCalendarLaw_mass (n : Fin (p.T + 1)) (htn : t.val < n.val) :
    generatedCalendarLaw rate rewards C_star C_h control0 b u t n htn Set.univ =
      branchLaw rate rewards C_star C_h control0 b u t Set.univ :=
  calendarLaw_mass rate rewards C_star C_h control0 b u t _ _

private theorem transport_prefix_property {n m : Fin (p.T + 1)} (h : n = m)
    (o : TaggedPrefix rate n) (P : (v : Fin (p.T + 1)) → TaggedPrefix rate v → Prop)
    (ho : P n o) : P m (h ▸ o) := by
  cases h
  exact ho

/-- The date-based interface has the same actual last-call/noncall interval
at every finite boundary, without requiring a physical round at the horizon. -/
theorem generatedCalendarObservation_origin (n : Fin (p.T + 1)) (htn : t.val < n.val)
    (w : Sample (n.val - (t.val + 1))) :
    let o := generatedCalendarObservation rate rewards C_star C_h control0 b u t n htn w
    o.1.val < n.val ∧ (sourceCall o.1 o.2.val.1.1.1.2).isSome = true ∧
      CallFree o.1 n o.2.val.1.1.1.2 := by
  unfold generatedCalendarObservation
  exact transport_prefix_property rate _ _ (fun n o =>
    o.1.val < n.val ∧ (sourceCall o.1 o.2.val.1.1.1.2).isSome = true ∧
      CallFree o.1 n o.2.val.1.1.1.2)
    (calendarObservation_origin rate rewards C_star C_h control0 b u t _ _ w)

/-- Complete PRE numerical-word characterization at any finite boundary,
including `n=T`. This does not identify the generated PRE cell list. -/
theorem generatedCalendarObservation_numerical (n : Fin (p.T + 1)) (htn : t.val < n.val)
    (w : Sample (n.val - (t.val + 1))) :
    let o := generatedCalendarObservation rate rewards C_star C_h control0 b u t n htn w
    o.2.val.2.2.1 = numericalAt n o.2.val.1.1.1.2 := by
  unfold generatedCalendarObservation
  exact transport_prefix_property rate _ _ (fun n o =>
    o.2.val.2.2.1 = numericalAt n o.2.val.1.1.1.2)
    (calendarObservation_numerical rate rewards C_star C_h control0 b u t _ _ w)

section OriginalPair

open ReferenceFirstNextLiftFutureAuxiliaryPairLaw
open scoped ENNReal

/-- Erase the SAME original pair, retaining every previously sampled vector.
Current sources and generated cells are regenerated by `calendarObservation`. -/
def calendarErasePair (q : Fin p.T) : (k : ℕ) → Sample k → Sample k
  | 0, w => eraseLift q w
  | k + 1, w => (calendarErasePair q k w.1, w.2)

/-- Reinsert an actual pair in the same original tape and keep all vectors. -/
def calendarFillPair (q : Fin p.T) : (k : ℕ) → Sample k × (UniformScalar × UniformScalar) → Sample k
  | 0, wx => restoreLift q wx
  | k + 1, wx => (calendarFillPair q k (wx.1.1, wx.2), wx.1.2)

local notation "erase" => calendarErasePair rate rewards C_star C_h b u t
local notation "fill" => calendarFillPair rate rewards C_star C_h b u t

theorem measurable_calendarErasePair (q : Fin p.T) (k : ℕ) : Measurable (erase q k) := by
  induction k with
  | zero => exact measurable_eraseLift q
  | succ k ih => exact ih.prodMap measurable_id

theorem measurable_calendarFillPair (q : Fin p.T) (k : ℕ) : Measurable (fill q k) := by
  induction k with
  | zero => exact measurable_restoreLift q
  | succ k ih => exact (ih.comp (measurable_fst.fst.prodMk measurable_snd)).prodMk measurable_fst.snd

theorem calendarOriginalLift_erasePair (q : Fin p.T) (k : ℕ) (w : Sample k) :
    original k (erase q k w) = eraseLift q (original k w) := by
  induction k with
  | zero => rfl
  | succ k ih => exact ih w.1

theorem calendarFillPair_erasePair (q : Fin p.T) (k : ℕ) (w : Sample k) :
    fill q k (erase q k w, auxiliaryPair q (original k w).1.2) = w := by
  induction k with
  | zero => exact restoreLift_erase_pair q w
  | succ k ih => exact Prod.ext (ih w.1) rfl

/-- At every produced PRE boundary, an original pair from that boundary or
later has not been read, even after earlier source/vector insertions. -/
theorem calendarObservation_erasePair (q : Fin p.T) (k : ℕ)
    (hk : t.val + 1 + k ≤ p.T) (hq : t.val + 1 + k ≤ q.val) (w : Sample k) :
    observe k hk (erase q k w) = observe k hk w := by
  induction k with
  | zero =>
      apply congrArg (Sigma.mk t)
      apply Subtype.ext
      apply branchObservation_auxiliary_pair rate rewards C_star C_h control0 b u t q
        t.succ (Nat.lt_succ_self _) hq
      intro j hj
      exact eraseAuxiliaryPair_apply_other q w.1.2 j
        (fun he => hj (congrArg Prod.fst he)) (fun he => hj (congrArg Prod.fst he))
  | succ k ih =>
      change advance ⟨t.val + 1 + k, by omega⟩
        (observe k (by omega) (erase q k w.1), ((original k (erase q k w.1)).1.2, w.2)) = _
      rw [ih (by omega) (by omega), calendarOriginalLift_erasePair]
      apply calendarStep_auxiliary_ext
      intro j hj
      change j.1.val ≤ t.val + 1 + k at hj
      have hne : j.1 ≠ q := by intro he; have := congrArg Fin.val he; omega
      exact eraseAuxiliaryPair_apply_other q (original k w.1).1.2 j
        (fun he => hne (congrArg Prod.fst he)) (fun he => hne (congrArg Prod.fst he))

/-- Each earlier vector kernel ignores this original pair. Its input uses
the current inserted source, rather than the unmodified first source. -/
theorem calendarExtensionKernel_erasePair (q : Fin p.T) (k : ℕ)
    (hk : t.val + 1 + (k + 1) ≤ p.T) (hq : t.val + 1 + (k + 1) ≤ q.val) (w : Sample k) :
    extension k hk (erase q k w) = extension k hk w := by
  change calendarVectorKernel rate rewards C_star C_h control0 ⟨t.val + 1 + k, by omega⟩
    (observe k (by omega) (erase q k w), (original k (erase q k w)).1.2) = _
  rw [calendarObservation_erasePair rate rewards C_star C_h control0 b u t q k
    (by omega) (by omega), calendarOriginalLift_erasePair]
  let r : Fin p.T := ⟨t.val + 1 + k, by omega⟩
  have hne : r ≠ q := by intro he; have := congrArg Fin.val he; dsimp only [r] at this; omega
  have hp : auxiliaryPair r (eraseAuxiliaryPair q (original k w).1.2) = auxiliaryPair r (original k w).1.2 := by
    apply Prod.ext <;> apply eraseAuxiliaryPair_apply_other <;>
      exact fun he => hne (congrArg Prod.fst he)
  change nextVectorKernel rate rewards C_star C_h (t := (observe k (by omega) w).1)
    (q := r) control0 ((observe k (by omega) w).2.val,
      auxiliaryPair r (eraseAuxiliaryPair q (original k w).1.2)) = _
  rw [hp]
  rfl

private theorem compProd_erased_factorization
    {B X V : Type*} [MeasurableSpace B] [MeasurableSpace X] [MeasurableSpace V]
    (mu : Measure B) [IsFiniteMeasure mu] (nu : Measure X) [IsProbabilityMeasure nu]
    (kernel : ProbabilityTheory.Kernel B V) [ProbabilityTheory.IsMarkovKernel kernel]
    (e : B → B) (he : Measurable e) (x : B → X) (hx : Measurable x)
    (hbase : mu.map (fun w => (e w, x w)) = (mu.map e).prod nu) (hnonuse : ∀ w, kernel w = kernel (e w)) :
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

/-- Produced-law factorization of a not-yet-read ORIGINAL pair. The erased
sample retains every previous full vector and the complete original source.
This is proved for this calendar's kernels, without a supplied law premise. -/
theorem calendarLaw_erasePair (q : Fin p.T) (k : ℕ) (hk : t.val + 1 + k ≤ p.T) (hq : t.val + 1 + k ≤ q.val) :
    (law k hk).map (fun w => (erase q k w, auxiliaryPair q (original k w).1.2)) =
      ((law k hk).map (erase q k)).prod auxiliaryPairLaw := by
  induction k with
  | zero =>
      cases b
      · exact nonrenewedLiftLaw_erase_pair rate rewards C_star C_h u t q (by omega) control0
      · exact renewalLiftLaw_erase_pair rate rewards C_star C_h u t q (by omega)
  | succ k ih =>
      exact compProd_erased_factorization (law k (by omega)) auxiliaryPairLaw
        (extension k hk) (erase q k) (measurable_calendarErasePair rate rewards C_star C_h b u t q k)
        (fun w => auxiliaryPair q (original k w).1.2) ((measurable_auxiliaryPair q).comp
          (measurable_calendarOriginalLift rate rewards C_star C_h b u t k).fst.snd)
        (ih (by omega) (by omega)) (fun w => (calendarExtensionKernel_erasePair
          rate rewards C_star C_h control0 b u t q k hk hq w).symm)

/-- Reinsert the SAME original pair to regenerate the complete current
observer and all archived observations, keeping the actual finite joint law. -/
theorem calendarLaw_eq_restorePair (q : Fin p.T) (k : ℕ) (hk : t.val + 1 + k ≤ p.T) (hq : t.val + 1 + k ≤ q.val) :
    law k hk = (((law k hk).map (erase q k)).prod auxiliaryPairLaw).map (fill q k) := by
  have h := congrArg (fun m => m.map (fill q k))
    (calendarLaw_erasePair rate rewards C_star C_h control0 b u t q k hk hq)
  have hj : Measurable (fun w : Sample k => (erase q k w, auxiliaryPair q (original k w).1.2)) :=
    (measurable_calendarErasePair rate rewards C_star C_h b u t q k).prodMk ((measurable_auxiliaryPair q).comp
        (measurable_calendarOriginalLift rate rewards C_star C_h b u t k).fst.snd)
  rw [Measure.map_map (measurable_calendarFillPair rate rewards C_star C_h b u t q k) hj] at h
  have hid : (fill q k) ∘ (fun w => (erase q k w, auxiliaryPair q (original k w).1.2)) = id :=
    funext (calendarFillPair_erasePair rate rewards C_star C_h b u t q k)
  rwa [hid, Measure.map_id] at h

/-- Restoration regenerates the whole observer jointly with the full raw
sample. The product factors the erased sample, never the un-erased tape. -/
theorem calendarLaw_joint_eq_restorePair (q : Fin p.T) (k : ℕ)
    (hk : t.val + 1 + k ≤ p.T) (hq : t.val + 1 + k ≤ q.val) :
    (law k hk).map (fun w => (w, observe k hk w)) =
      (((law k hk).map (erase q k)).prod auxiliaryPairLaw).map
        (fun wx => (fill q k wx, observe k hk (fill q k wx))) := by
  have h := congrArg (fun m : Measure (Sample k) => m.map (fun w => (w, observe k hk w)))
    (calendarLaw_eq_restorePair rate rewards C_star C_h control0 b u t q k hk hq)
  have hm := Measure.map_map (μ := ((law k hk).map (erase q k)).prod auxiliaryPairLaw)
    (measurable_id.prodMk (measurable_calendarObservation rate rewards C_star C_h control0 b u t k hk))
      (measurable_calendarFillPair rate rewards C_star C_h b u t q k)
  exact h.trans hm

end OriginalPair

end FiniteCalendar

end Bandits.Support.ReferenceGeneratedRankCalendarFoundation
