/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstNextInstallationTransitionLaw

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Tactic

/-!
# Future whole controls under the literal first next-installation lifts

The original event, auxiliary array and complete assignment vector are retained.
The future control is restored in both source readouts using the same value.
All measures are unnormalized, including event and private-index strata of mass
zero. This file proves physical-control factorization only.

Sources: ZIP4 `06_interruptions.tex:391-426`,
`04_slow_fast_learner.tex:142-215,323-390`, and `08_main_theorem.tex:78-109`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal
open Bandits.Support
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceFixedTimeSourceControlCoupling
open Bandits.Support.ReferenceSourcePrefixHistoryFiltration
open Bandits.Support.ReferenceFirstNextInstallationTransitionLaw

namespace Bandits.Support.ReferenceFirstNextLiftFutureControl

variable {p : ConstructorDimensions.Parameters}

local instance sourceInputMeasurableSpace :
    MeasurableSpace (BootstrapPrivateRoundStreams.SourceInput p) := by
  change MeasurableSpace (CompletePublicTable.PublishedOutput p ×
    BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput
abbrev TimeControl := ContinuousLearningRows.TimeControl
abbrev AuxArray := ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray
abbrev Vector := AssignmentParameterFibreKernel.AssignmentVector

local instance timeControlMeasurableSpace : MeasurableSpace (TimeControl p) := by
  unfold TimeControl ContinuousLearningRows.TimeControl
  infer_instance

local instance auxArrayMeasurableSpace : MeasurableSpace (AuxArray p) := by
  unfold AuxArray ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray
  infer_instance

local instance vectorMeasurableSpace : MeasurableSpace (Vector p) := by
  unfold Vector AssignmentParameterFibreKernel.AssignmentVector
  infer_instance

variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
  (control0 : TimeControl p) (u t q : Fin p.T) (htq : t.val < q.val)

include control0 htq in
/-- Future replacement preserves the actual nonrenewed branch event. -/
theorem nonrenewedEvent_future_invariant (z : SourceInput p) (c : TimeControl p) :
    replaceSourceControl p q z c ∈
      ReferenceFirstLiveCollectionPathJoin.firstLiveCollectionEvent rate rewards C_star C_h u t ↔
    z ∈ ReferenceFirstLiveCollectionPathJoin.firstLiveCollectionEvent rate rewards C_star C_h u t := by
  rw [← ReferenceFirstNextInvocationJointLift.event_sourcePrefix_iff
    rate rewards C_star C_h u t control0 (replaceSourceControl p q z c),
    ReferenceFirstCollectionOldRecorderFoundation.sourcePrefix_replaceCurrent
      control0 q t.val (Nat.le_of_lt htq) z c,
    ReferenceFirstNextInvocationJointLift.event_sourcePrefix_iff]

include control0 htq in
/-- Future replacement preserves the actual renewal event and anchor test. -/
theorem renewedEvent_future_invariant (z : SourceInput p) (c : TimeControl p) :
    replaceSourceControl p q z c ∈
      ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent rate rewards C_star C_h u t ↔
    z ∈ ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent rate rewards C_star C_h u t := by
  have hp (s : SourceInput p) :
      s ∈ ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent rate rewards C_star C_h u t ↔
      sourcePrefix control0 t.val s ∈
        ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent rate rewards C_star C_h u t :=
    ReferenceFirstCollectionRenewalPastLocality.renewalCallEvent_iff_replaceSelectedControlSuffix
      rate rewards C_star C_h s u t (fun _ => control0)
  rw [hp, ReferenceFirstCollectionOldRecorderFoundation.sourcePrefix_replaceCurrent
    control0 q t.val (Nat.le_of_lt htq) z c]
  exact (hp z).symm

/-- Replace a future whole control inside the original nonrenewed subtype. -/
def nonrenewedReplace
    (z : ReferenceFirstNextInvocationJointLift.EventSource rate rewards C_star C_h u t)
    (c : TimeControl p) :
    ReferenceFirstNextInvocationJointLift.EventSource rate rewards C_star C_h u t :=
  ⟨replaceSourceControl p q z.val c,
    (nonrenewedEvent_future_invariant rate rewards C_star C_h control0 u t q htq z.val c).mpr
      z.property⟩

/-- Replace a future whole control inside the original renewal subtype. -/
def renewedReplace
    (z : ReferenceFirstCollectionRenewalInstallationCoupling.Source rate rewards C_star C_h u t)
    (c : TimeControl p) :
    ReferenceFirstCollectionRenewalInstallationCoupling.Source rate rewards C_star C_h u t :=
  ⟨replaceSourceControl p q z.val c,
    (renewedEvent_future_invariant rate rewards C_star C_h control0 u t q htq z.val c).mpr
      z.property⟩

/-- The entire literal nonrenewed vector kernel ignores this future control. -/
theorem nonrenewedVectorKernel_future_invariant
    (z : ReferenceFirstNextInvocationJointLift.EventSource rate rewards C_star C_h u t)
    (c : TimeControl p) (a : AuxArray p) :
    ReferenceFirstNextInvocationJointLift.nonrenewedVectorKernel rate rewards C_star C_h u t
        control0 (nonrenewedReplace rate rewards C_star C_h control0 u t q htq z c, a) =
      ReferenceFirstNextInvocationJointLift.nonrenewedVectorKernel rate rewards C_star C_h u t
        control0 (z, a) := by
  apply nonrenewedVectorKernel_prefix_ext
  exact ReferenceFirstCollectionOldRecorderFoundation.sourcePrefix_replaceCurrent
    control0 q t.val (Nat.le_of_lt htq) z.val c

/-- The entire literal renewal vector kernel ignores this future control. -/
theorem renewedVectorKernel_future_invariant
    (z : ReferenceFirstCollectionRenewalInstallationCoupling.Source rate rewards C_star C_h u t)
    (c : TimeControl p) (a : AuxArray p) :
    ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalAssignmentFibreKernel
        rate rewards C_star C_h u t
        (renewedReplace rate rewards C_star C_h control0 u t q htq z c, a) =
      ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalAssignmentFibreKernel
        rate rewards C_star C_h u t (z, a) := by
  apply renewedVectorKernel_prefix_ext rate rewards C_star C_h control0
  exact ReferenceFirstCollectionOldRecorderFoundation.sourcePrefix_replaceCurrent
    control0 q t.val (Nat.le_of_lt htq) z.val c

section Insertion

open ReferenceFirstCollectionRenewalVectorInsertion

private theorem replace_control_other (s : SourceInput p) (c : TimeControl p)
    (hne : t ≠ q) :
    ReferenceFirstCollectionRenewalVectorInsertion.c t (replaceSourceControl p q s c) =
      ReferenceFirstCollectionRenewalVectorInsertion.c t s := by
  simp only [ReferenceFirstCollectionRenewalVectorInsertion.c,
    ReferenceFirstCollectionRenewalVectorInsertion.q, replaceSourceControl,
    sourceCoordinatorIndex, ActualInitializationPhysicalStep.selectedRowIndex,
    Function.update_self, Function.update_of_ne hne]

private theorem replace_controls_commute (s : SourceInput p) (ct cq : TimeControl p)
    (hne : t ≠ q) :
    replaceSourceControl p t (replaceSourceControl p q s cq) ct =
      replaceSourceControl p q (replaceSourceControl p t s ct) cq := by
  simp only [replaceSourceControl, sourceCoordinatorIndex, Function.update_self,
    Function.update_idem]
  rw [Function.update_comm hne]

include htq in
/-- Actual vector insertion at `t` commutes with whole-control replacement at
`q`. Equality is on the full original source, including all private arrays. -/
theorem insert_replace_future (s : SourceInput p) (v : Vector p) (c : TimeControl p) :
    insert t (replaceSourceControl p q s c) v =
      replaceSourceControl p q (insert t s v) c := by
  have hne : t ≠ q := by intro h; subst q; exact Nat.lt_irrefl _ htq
  unfold ReferenceFirstCollectionRenewalVectorInsertion.insert ctrl
  rw [replace_control_other t q s c hne]
  exact replace_controls_commute t q s _ c hne

/-- Commutation for the actual nonrenewed first-invocation source producer. -/
theorem nonrenewedFirstSource_replace_future
    (z : ReferenceFirstNextInvocationJointLift.EventSource rate rewards C_star C_h u t)
    (v : Vector p) (c : TimeControl p) :
    (ReferenceFirstNextInstallationCellFactors.nonrenewedFirstSource rate rewards C_star C_h t u
      (nonrenewedReplace rate rewards C_star C_h control0 u t q htq z c) v).val =
    replaceSourceControl p q
      (ReferenceFirstNextInstallationCellFactors.nonrenewedFirstSource
        rate rewards C_star C_h t u z v).val c :=
  insert_replace_future t q htq z.val v c

/-- Commutation for the actual renewal subtype insertion. -/
theorem renewedPut_replace_future
    (z : ReferenceFirstCollectionRenewalInstallationCoupling.Source rate rewards C_star C_h u t)
    (v : Vector p) (c : TimeControl p) :
    (put rate rewards C_star C_h u t
      (renewedReplace rate rewards C_star C_h control0 u t q htq z c) v).val =
    replaceSourceControl p q (put rate rewards C_star C_h u t z v).val c := by
  rw [put_val, put_val]
  exact insert_replace_future t q htq z.val v c

end Insertion

section Remainders

abbrev NonrenewedRemainder (i : Fin (M p)) :=
  EventRemainder control0 q
    (ReferenceFirstLiveCollectionPathJoin.firstLiveCollectionEvent rate rewards C_star C_h u t) i

abbrev RenewedRemainder (i : Fin (M p)) :=
  EventRemainder control0 q
    (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent rate rewards C_star C_h u t) i

local instance nonrenewedRemainderMeasurableSpace (i : Fin (M p)) :
    MeasurableSpace (NonrenewedRemainder rate rewards C_star C_h control0 u t q i) := by
  unfold NonrenewedRemainder EventRemainder
  infer_instance

local instance renewedRemainderMeasurableSpace (i : Fin (M p)) :
    MeasurableSpace (RenewedRemainder rate rewards C_star C_h control0 u t q i) := by
  unfold RenewedRemainder EventRemainder
  infer_instance

/-- Restore the exposed future control in the original nonrenewed event. -/
def nonrenewedRestore (i : Fin (M p)) :
    NonrenewedRemainder rate rewards C_star C_h control0 u t q i × TimeControl p →
      ReferenceFirstNextInvocationJointLift.EventSource rate rewards C_star C_h u t :=
  restoreEventSource control0 q _
    (nonrenewedEvent_future_invariant rate rewards C_star C_h control0 u t q htq) i

/-- Restore the exposed future control in the original renewal event. -/
def renewedRestore (i : Fin (M p)) :
    RenewedRemainder rate rewards C_star C_h control0 u t q i × TimeControl p →
      ReferenceFirstCollectionRenewalInstallationCoupling.Source rate rewards C_star C_h u t :=
  restoreEventSource control0 q _
    (renewedEvent_future_invariant rate rewards C_star C_h control0 u t q htq) i

theorem measurable_nonrenewedRestore (i : Fin (M p)) :
    Measurable (nonrenewedRestore rate rewards C_star C_h control0 u t q htq i) :=
  measurable_restoreEventSource control0 q _ _ i

theorem measurable_renewedRestore (i : Fin (M p)) :
    Measurable (renewedRestore rate rewards C_star C_h control0 u t q htq i) :=
  measurable_restoreEventSource control0 q _ _ i

/-- The full split is recovered exactly, so no original remainder coordinate
or private array (including `J`) changes with the exposed control. -/
theorem nonrenewedRestore_split (i : Fin (M p))
    (r : NonrenewedRemainder rate rewards C_star C_h control0 u t q i) (c : TimeControl p) :
    fixedControlSplit p i q
      (nonrenewedRestore rate rewards C_star C_h control0 u t q htq i (r, c)).val =
        (c, r.val) :=
  (fixedControlSplit p i q).apply_symm_apply _

theorem renewedRestore_split (i : Fin (M p))
    (r : RenewedRemainder rate rewards C_star C_h control0 u t q i) (c : TimeControl p) :
    fixedControlSplit p i q
      (renewedRestore rate rewards C_star C_h control0 u t q htq i (r, c)).val =
        (c, r.val) :=
  (fixedControlSplit p i q).apply_symm_apply _

private theorem restore_eq_replace (E : Set (SourceInput p))
    (hinv : ∀ z c, replaceSourceControl p q z c ∈ E ↔ z ∈ E)
    (i : Fin (M p)) (r : EventRemainder control0 q E i) (c : TimeControl p) :
    (restoreEventSource control0 q E hinv i (r, c)).val =
      replaceSourceControl p q
        (restoreEventSource control0 q E hinv i (r, control0)).val c := by
  let z := (fixedControlSplit p i q).symm (control0, r.val)
  have hi := fixedControlSplit_symm_coordinatorIndex p i q control0 r.val r.property.1
  have hr := congrArg Prod.snd ((fixedControlSplit p i q).apply_symm_apply (control0, r.val))
  have he := fixedControlSplit_replaceSourceControl p i q z c hi
  rw [hr] at he
  exact he

theorem nonrenewedRestore_eq_replace (i : Fin (M p))
    (r : NonrenewedRemainder rate rewards C_star C_h control0 u t q i) (c : TimeControl p) :
    nonrenewedRestore rate rewards C_star C_h control0 u t q htq i (r, c) =
      nonrenewedReplace rate rewards C_star C_h control0 u t q htq
        (nonrenewedRestore rate rewards C_star C_h control0 u t q htq i (r, control0)) c :=
  Subtype.ext (restore_eq_replace control0 q _ _ i r c)

theorem renewedRestore_eq_replace (i : Fin (M p))
    (r : RenewedRemainder rate rewards C_star C_h control0 u t q i) (c : TimeControl p) :
    renewedRestore rate rewards C_star C_h control0 u t q htq i (r, c) =
      renewedReplace rate rewards C_star C_h control0 u t q htq
        (renewedRestore rate rewards C_star C_h control0 u t q htq i (r, control0)) c :=
  Subtype.ext (restore_eq_replace control0 q _ _ i r c)

/-- Actual kernel on the nonrenewed event remainder and entire auxiliary array.
The reference filler is used only after the proved future-control nonuse. -/
def nonrenewedRemainderKernel (i : Fin (M p)) : ProbabilityTheory.Kernel
    (NonrenewedRemainder rate rewards C_star C_h control0 u t q i × AuxArray p) (Vector p) :=
  (ReferenceFirstNextInvocationJointLift.nonrenewedVectorKernel
    rate rewards C_star C_h u t control0).comap
      (fun ra => (nonrenewedRestore rate rewards C_star C_h control0 u t q htq i
        (ra.1, control0), ra.2))
      (((measurable_nonrenewedRestore rate rewards C_star C_h control0 u t q htq i).comp
        (measurable_fst.prodMk measurable_const)).prodMk measurable_snd)

/-- Actual renewal fibre kernel on the future-control remainder. -/
def renewedRemainderKernel (i : Fin (M p)) : ProbabilityTheory.Kernel
    (RenewedRemainder rate rewards C_star C_h control0 u t q i × AuxArray p) (Vector p) :=
  (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalAssignmentFibreKernel
    rate rewards C_star C_h u t).comap
      (fun ra => (renewedRestore rate rewards C_star C_h control0 u t q htq i
        (ra.1, control0), ra.2))
      (((measurable_renewedRestore rate rewards C_star C_h control0 u t q htq i).comp
        (measurable_fst.prodMk measurable_const)).prodMk measurable_snd)

instance nonrenewedRemainderKernel_markov (i : Fin (M p)) :
    ProbabilityTheory.IsMarkovKernel
      (nonrenewedRemainderKernel rate rewards C_star C_h control0 u t q htq i) := by
  unfold nonrenewedRemainderKernel
  infer_instance

instance renewedRemainderKernel_markov (i : Fin (M p)) :
    ProbabilityTheory.IsMarkovKernel
      (renewedRemainderKernel rate rewards C_star C_h control0 u t q htq i) := by
  unfold renewedRemainderKernel
  infer_instance

theorem nonrenewedRemainderKernel_restore (i : Fin (M p))
    (r : NonrenewedRemainder rate rewards C_star C_h control0 u t q i)
    (c : TimeControl p) (a : AuxArray p) :
    ReferenceFirstNextInvocationJointLift.nonrenewedVectorKernel rate rewards C_star C_h u t
      control0 (nonrenewedRestore rate rewards C_star C_h control0 u t q htq i (r, c), a) =
    nonrenewedRemainderKernel rate rewards C_star C_h control0 u t q htq i (r, a) := by
  rw [nonrenewedRestore_eq_replace,
    nonrenewedVectorKernel_future_invariant rate rewards C_star C_h control0 u t q htq]
  rfl

theorem renewedRemainderKernel_restore (i : Fin (M p))
    (r : RenewedRemainder rate rewards C_star C_h control0 u t q i)
    (c : TimeControl p) (a : AuxArray p) :
    ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalAssignmentFibreKernel
      rate rewards C_star C_h u t
      (renewedRestore rate rewards C_star C_h control0 u t q htq i (r, c), a) =
    renewedRemainderKernel rate rewards C_star C_h control0 u t q htq i (r, a) := by
  rw [renewedRestore_eq_replace,
    renewedVectorKernel_future_invariant rate rewards C_star C_h control0 u t q htq]
  rfl

/-- The original private-index/event mass, entire auxiliary law and actual
nonrenewed vector fibre. -/
def nonrenewedRemainderLiftLaw (i : Fin (M p)) : Measure
    ((NonrenewedRemainder rate rewards C_star C_h control0 u t q i × AuxArray p) × Vector p) :=
  ((eventRemainderLaw control0 q
    (ReferenceFirstLiveCollectionPathJoin.firstLiveCollectionEvent rate rewards C_star C_h u t) i).prod
      (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p)).compProd
        (nonrenewedRemainderKernel rate rewards C_star C_h control0 u t q htq i)

/-- The corresponding literal renewal remainder lift. -/
def renewedRemainderLiftLaw (i : Fin (M p)) : Measure
    ((RenewedRemainder rate rewards C_star C_h control0 u t q i × AuxArray p) × Vector p) :=
  ((eventRemainderLaw control0 q
    (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent rate rewards C_star C_h u t) i).prod
      (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p)).compProd
        (renewedRemainderKernel rate rewards C_star C_h control0 u t q htq i)

/-- Restore the original carrier without changing any auxiliary coordinate or
any of the `K+1` vector coordinates. -/
def nonrenewedRestoreLift (i : Fin (M p))
    (w : ((NonrenewedRemainder rate rewards C_star C_h control0 u t q i × AuxArray p) ×
      Vector p) × TimeControl p) :
    (ReferenceFirstNextInvocationJointLift.EventSource rate rewards C_star C_h u t × AuxArray p) ×
      Vector p :=
  ((nonrenewedRestore rate rewards C_star C_h control0 u t q htq i (w.1.1.1, w.2), w.1.1.2),
    w.1.2)

def renewedRestoreLift (i : Fin (M p))
    (w : ((RenewedRemainder rate rewards C_star C_h control0 u t q i × AuxArray p) ×
      Vector p) × TimeControl p) :
    ReferenceFirstCollectionRenewalInstallationCoupling.RenewalLift rate rewards C_star C_h u t :=
  ((renewedRestore rate rewards C_star C_h control0 u t q htq i (w.1.1.1, w.2), w.1.1.2),
    w.1.2)

theorem measurable_nonrenewedRestoreLift (i : Fin (M p)) :
    Measurable (nonrenewedRestoreLift rate rewards C_star C_h control0 u t q htq i) :=
  (((measurable_nonrenewedRestore rate rewards C_star C_h control0 u t q htq i).comp
    (measurable_fst.fst.fst.prodMk measurable_snd)).prodMk
      measurable_fst.fst.snd).prodMk measurable_fst.snd

theorem measurable_renewedRestoreLift (i : Fin (M p)) :
    Measurable (renewedRestoreLift rate rewards C_star C_h control0 u t q htq i) :=
  (((measurable_renewedRestore rate rewards C_star C_h control0 u t q htq i).comp
    (measurable_fst.fst.fst.prodMk measurable_snd)).prodMk
      measurable_fst.fst.snd).prodMk measurable_fst.snd

local instance nonrenewedRemainderLaw_finite (i : Fin (M p)) :
    IsFiniteMeasure (eventRemainderLaw control0 q
      (ReferenceFirstLiveCollectionPathJoin.firstLiveCollectionEvent rate rewards C_star C_h u t) i) :=
  eventRemainderLaw_finite control0 q _
    (ReferenceFirstLiveCollectionPathJoin.measurableSet_firstLiveCollectionEvent
      rate rewards C_star C_h u t) i

local instance renewedRemainderLaw_finite (i : Fin (M p)) :
    IsFiniteMeasure (eventRemainderLaw control0 q
      (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent rate rewards C_star C_h u t) i) :=
  eventRemainderLaw_finite control0 q _
    (ReferenceFirstCollectionRenewalAuxiliaryLaw.measurableSet_renewalCallEvent
      rate rewards C_star C_h u t) i

instance nonrenewedRemainderLiftLaw_finite (i : Fin (M p)) :
    IsFiniteMeasure (nonrenewedRemainderLiftLaw rate rewards C_star C_h control0 u t q htq i) := by
  unfold nonrenewedRemainderLiftLaw
  infer_instance

instance renewedRemainderLiftLaw_finite (i : Fin (M p)) :
    IsFiniteMeasure (renewedRemainderLiftLaw rate rewards C_star C_h control0 u t q htq i) := by
  unfold renewedRemainderLiftLaw
  infer_instance

private theorem nonrenewed_remainder_swap (i : Fin (M p))
    (r : NonrenewedRemainder rate rewards C_star C_h control0 u t q i)
    (f : (ReferenceFirstNextInvocationJointLift.EventSource rate rewards C_star C_h u t ×
      AuxArray p) × Vector p → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ c, ∫⁻ a, ∫⁻ v,
      f ((nonrenewedRestore rate rewards C_star C_h control0 u t q htq i (r, c), a), v)
        ∂nonrenewedRemainderKernel rate rewards C_star C_h control0 u t q htq i (r, a)
        ∂ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p
        ∂ContinuousLearningRows.timeControlLaw p) =
    ∫⁻ a, ∫⁻ v, ∫⁻ c,
      f ((nonrenewedRestore rate rewards C_star C_h control0 u t q htq i (r, c), a), v)
        ∂ContinuousLearningRows.timeControlLaw p
        ∂nonrenewedRemainderKernel rate rewards C_star C_h control0 u t q htq i (r, a)
        ∂ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p := by
  let restore := nonrenewedRestore rate rewards C_star C_h control0 u t q htq i
  let kr := nonrenewedRemainderKernel rate rewards C_star C_h control0 u t q htq i
  let aux := ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p
  let tc := ContinuousLearningRows.timeControlLaw p
  let ka := kr.comap (fun a : AuxArray p => (r, a))
    (measurable_const.prodMk measurable_id)
  have hm : Measurable restore :=
    measurable_nonrenewedRestore rate rewards C_star C_h control0 u t q htq i
  have hrc : Measurable (fun x : TimeControl p × (AuxArray p × Vector p) => (r, x.1)) :=
    measurable_const.prodMk measurable_fst
  have hF : Measurable (fun x : TimeControl p × (AuxArray p × Vector p) =>
      f ((restore (r, x.1), x.2.1), x.2.2)) :=
    hf.comp (((hm.comp hrc).prodMk
      measurable_snd.fst).prodMk measurable_snd.snd)
  calc
    _ = ∫⁻ c, ∫⁻ av, f ((restore (r, c), av.1), av.2) ∂aux.compProd ka ∂tc := by
      apply lintegral_congr
      intro c
      have hsection : Measurable (fun av : AuxArray p × Vector p => (c, av)) :=
        measurable_const.prodMk measurable_id
      have hh := hF.comp hsection
      exact (Measure.lintegral_compProd (μ := aux) (κ := ka) hh).symm
    _ = ∫⁻ av, ∫⁻ c, f ((restore (r, c), av.1), av.2) ∂tc ∂aux.compProd ka :=
      lintegral_lintegral_swap (μ := tc) (ν := aux.compProd ka) hF.aemeasurable
    _ = _ := Measure.lintegral_compProd (μ := aux) (κ := ka)
      (hF.lintegral_prod_left' (μ := tc))

/-- Exact future whole-control factorization on the ORIGINAL nonrenewed lift
carrier. The full original source remains inside every test after restoration. -/
theorem nonrenewedLiftLaw_eq_sum_restore_future :
    ReferenceFirstNextInvocationJointLift.nonrenewedLiftLaw rate rewards C_star C_h u t control0 =
      Measure.sum (fun i : Fin (M p) =>
        ((nonrenewedRemainderLiftLaw rate rewards C_star C_h control0 u t q htq i).prod
          (ContinuousLearningRows.timeControlLaw p)).map
            (nonrenewedRestoreLift rate rewards C_star C_h control0 u t q htq i)) := by
  let E := ReferenceFirstLiveCollectionPathJoin.firstLiveCollectionEvent rate rewards C_star C_h u t
  let mu := ReferenceFirstNextInvocationJointLift.eventSourceLaw rate rewards C_star C_h u t
  let aux := ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p
  let tc := ContinuousLearningRows.timeControlLaw p
  let k := ReferenceFirstNextInvocationJointLift.nonrenewedVectorKernel
    rate rewards C_star C_h u t control0
  let restore := nonrenewedRestore rate rewards C_star C_h control0 u t q htq
  let kr := nonrenewedRemainderKernel rate rewards C_star C_h control0 u t q htq
  have hm (i : Fin (M p)) : Measurable (restore i) :=
    measurable_nonrenewedRestore rate rewards C_star C_h control0 u t q htq i
  have hsource : mu = Measure.sum (fun i : Fin (M p) =>
      ((eventRemainderLaw control0 q E i).prod tc).map (restore i)) :=
    eventSourceLaw_eq_sum_restore control0 q E
      (ReferenceFirstLiveCollectionPathJoin.measurableSet_firstLiveCollectionEvent
        rate rewards C_star C_h u t)
      (nonrenewedEvent_future_invariant rate rewards C_star C_h control0 u t q htq)
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  let g := fun za => ∫⁻ v, f (za, v) ∂k za
  have hg : Measurable g := hf.lintegral_kernel_prod_right'
  let G := fun z => ∫⁻ a, g (z, a) ∂aux
  have hG : Measurable G := hg.lintegral_prod_right'
  calc
    _ = ∫⁻ z, G z ∂mu := by
      rw [ReferenceFirstNextInvocationJointLift.nonrenewedLiftLaw,
        Measure.lintegral_compProd hf]
      exact lintegral_prod g hg.aemeasurable
    _ = ∑' i : Fin (M p), ∫⁻ r, ∫⁻ c, ∫⁻ a, ∫⁻ v,
        f ((restore i (r, c), a), v) ∂kr i (r, a) ∂aux ∂tc
          ∂eventRemainderLaw control0 q E i := by
      rw [hsource, lintegral_sum_measure]
      apply tsum_congr
      intro i
      rw [lintegral_map hG (hm i),
        lintegral_prod (fun rc => G (restore i rc)) (hG.comp (hm i)).aemeasurable]
      apply lintegral_congr
      intro r
      apply lintegral_congr
      intro c
      apply lintegral_congr
      intro a
      dsimp only [G, g]
      rw [show k (restore i (r, c), a) = kr i (r, a) from
        nonrenewedRemainderKernel_restore rate rewards C_star C_h control0 u t q htq i r c a]
    _ = ∑' i : Fin (M p), ∫⁻ r, ∫⁻ a, ∫⁻ v, ∫⁻ c,
        f ((restore i (r, c), a), v) ∂tc ∂kr i (r, a) ∂aux
          ∂eventRemainderLaw control0 q E i := by
      apply tsum_congr
      intro i
      apply lintegral_congr
      intro r
      exact nonrenewed_remainder_swap rate rewards C_star C_h control0 u t q htq i r f hf
    _ = _ := by
      rw [lintegral_sum_measure]
      apply tsum_congr
      intro i
      rw [lintegral_map hf
        (measurable_nonrenewedRestoreLift rate rewards C_star C_h control0 u t q htq i)]
      let F := fun w : ((NonrenewedRemainder rate rewards C_star C_h control0 u t q i ×
          AuxArray p) × Vector p) × TimeControl p =>
        f (nonrenewedRestoreLift rate rewards C_star C_h control0 u t q htq i w)
      have hF : Measurable F := hf.comp
        (measurable_nonrenewedRestoreLift rate rewards C_star C_h control0 u t q htq i)
      rw [lintegral_prod _ hF.aemeasurable]
      change _ = ∫⁻ w, (∫⁻ c, F (w, c) ∂tc)
        ∂((eventRemainderLaw control0 q E i).prod aux).compProd (kr i)
      have hinner := hF.lintegral_prod_right' (ν := tc)
      rw [Measure.lintegral_compProd
        (μ := (eventRemainderLaw control0 q E i).prod aux) (κ := kr i) hinner]
      have hg' := hinner.lintegral_kernel_prod_right' (κ := kr i)
      exact (lintegral_prod (μ := eventRemainderLaw control0 q E i) (ν := aux)
        _ hg'.aemeasurable).symm

private theorem renewed_remainder_swap (i : Fin (M p))
    (r : RenewedRemainder rate rewards C_star C_h control0 u t q i)
    (f : (ReferenceFirstCollectionRenewalInstallationCoupling.Source rate rewards C_star C_h u t ×
      AuxArray p) × Vector p → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ c, ∫⁻ a, ∫⁻ v,
      f ((renewedRestore rate rewards C_star C_h control0 u t q htq i (r, c), a), v)
        ∂renewedRemainderKernel rate rewards C_star C_h control0 u t q htq i (r, a)
        ∂ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p
        ∂ContinuousLearningRows.timeControlLaw p) =
    ∫⁻ a, ∫⁻ v, ∫⁻ c,
      f ((renewedRestore rate rewards C_star C_h control0 u t q htq i (r, c), a), v)
        ∂ContinuousLearningRows.timeControlLaw p
        ∂renewedRemainderKernel rate rewards C_star C_h control0 u t q htq i (r, a)
        ∂ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p := by
  let restore := renewedRestore rate rewards C_star C_h control0 u t q htq i
  let kr := renewedRemainderKernel rate rewards C_star C_h control0 u t q htq i
  let aux := ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p
  let tc := ContinuousLearningRows.timeControlLaw p
  let ka := kr.comap (fun a : AuxArray p => (r, a))
    (measurable_const.prodMk measurable_id)
  have hm : Measurable restore :=
    measurable_renewedRestore rate rewards C_star C_h control0 u t q htq i
  have hrc : Measurable (fun x : TimeControl p × (AuxArray p × Vector p) => (r, x.1)) :=
    measurable_const.prodMk measurable_fst
  have hF : Measurable (fun x : TimeControl p × (AuxArray p × Vector p) =>
      f ((restore (r, x.1), x.2.1), x.2.2)) :=
    hf.comp (((hm.comp hrc).prodMk
      measurable_snd.fst).prodMk measurable_snd.snd)
  calc
    _ = ∫⁻ c, ∫⁻ av, f ((restore (r, c), av.1), av.2) ∂aux.compProd ka ∂tc := by
      apply lintegral_congr
      intro c
      have hsection : Measurable (fun av : AuxArray p × Vector p => (c, av)) :=
        measurable_const.prodMk measurable_id
      have hh := hF.comp hsection
      exact (Measure.lintegral_compProd (μ := aux) (κ := ka) hh).symm
    _ = ∫⁻ av, ∫⁻ c, f ((restore (r, c), av.1), av.2) ∂tc ∂aux.compProd ka :=
      lintegral_lintegral_swap (μ := tc) (ν := aux.compProd ka) hF.aemeasurable
    _ = _ := Measure.lintegral_compProd (μ := aux) (κ := ka)
      (hF.lintegral_prod_left' (μ := tc))

/-- Exact future whole-control factorization on the ORIGINAL renewal lift
carrier. The full original source remains inside every test after restoration. -/
theorem renewedLiftLaw_eq_sum_restore_future :
    ReferenceFirstCollectionRenewalInstallationCoupling.renewalLiftLaw rate rewards C_star C_h u t =
      Measure.sum (fun i : Fin (M p) =>
        ((renewedRemainderLiftLaw rate rewards C_star C_h control0 u t q htq i).prod
          (ContinuousLearningRows.timeControlLaw p)).map
            (renewedRestoreLift rate rewards C_star C_h control0 u t q htq i)) := by
  let E := ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent rate rewards C_star C_h u t
  let mu := ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t
  let aux := ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p
  let tc := ContinuousLearningRows.timeControlLaw p
  let k := ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalAssignmentFibreKernel
    rate rewards C_star C_h u t
  let restore := renewedRestore rate rewards C_star C_h control0 u t q htq
  let kr := renewedRemainderKernel rate rewards C_star C_h control0 u t q htq
  have hm (i : Fin (M p)) : Measurable (restore i) :=
    measurable_renewedRestore rate rewards C_star C_h control0 u t q htq i
  have hsource : mu = Measure.sum (fun i : Fin (M p) =>
      ((eventRemainderLaw control0 q E i).prod tc).map (restore i)) :=
    eventSourceLaw_eq_sum_restore control0 q E
      (ReferenceFirstCollectionRenewalAuxiliaryLaw.measurableSet_renewalCallEvent
        rate rewards C_star C_h u t)
      (renewedEvent_future_invariant rate rewards C_star C_h control0 u t q htq)
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  let g := fun za => ∫⁻ v, f (za, v) ∂k za
  have hg : Measurable g := hf.lintegral_kernel_prod_right'
  let G := fun z => ∫⁻ a, g (z, a) ∂aux
  have hG : Measurable G := hg.lintegral_prod_right'
  calc
    _ = ∫⁻ z, G z ∂mu := by
      change (∫⁻ w, f w ∂(mu.prod aux).compProd k) = _
      rw [Measure.lintegral_compProd hf]
      exact lintegral_prod g hg.aemeasurable
    _ = ∑' i : Fin (M p), ∫⁻ r, ∫⁻ c, ∫⁻ a, ∫⁻ v,
        f ((restore i (r, c), a), v) ∂kr i (r, a) ∂aux ∂tc
          ∂eventRemainderLaw control0 q E i := by
      rw [hsource, lintegral_sum_measure]
      apply tsum_congr
      intro i
      rw [lintegral_map hG (hm i),
        lintegral_prod (fun rc => G (restore i rc)) (hG.comp (hm i)).aemeasurable]
      apply lintegral_congr
      intro r
      apply lintegral_congr
      intro c
      apply lintegral_congr
      intro a
      dsimp only [G, g]
      rw [show k (restore i (r, c), a) = kr i (r, a) from
        renewedRemainderKernel_restore rate rewards C_star C_h control0 u t q htq i r c a]
    _ = ∑' i : Fin (M p), ∫⁻ r, ∫⁻ a, ∫⁻ v, ∫⁻ c,
        f ((restore i (r, c), a), v) ∂tc ∂kr i (r, a) ∂aux
          ∂eventRemainderLaw control0 q E i := by
      apply tsum_congr
      intro i
      apply lintegral_congr
      intro r
      exact renewed_remainder_swap rate rewards C_star C_h control0 u t q htq i r f hf
    _ = _ := by
      rw [lintegral_sum_measure]
      apply tsum_congr
      intro i
      rw [lintegral_map hf
        (measurable_renewedRestoreLift rate rewards C_star C_h control0 u t q htq i)]
      let F := fun w : ((RenewedRemainder rate rewards C_star C_h control0 u t q i ×
          AuxArray p) × Vector p) × TimeControl p =>
        f (renewedRestoreLift rate rewards C_star C_h control0 u t q htq i w)
      have hF : Measurable F := hf.comp
        (measurable_renewedRestoreLift rate rewards C_star C_h control0 u t q htq i)
      rw [lintegral_prod _ hF.aemeasurable]
      change _ = ∫⁻ w, (∫⁻ c, F (w, c) ∂tc)
        ∂((eventRemainderLaw control0 q E i).prod aux).compProd (kr i)
      have hinner := hF.lintegral_prod_right' (ν := tc)
      rw [Measure.lintegral_compProd
        (μ := (eventRemainderLaw control0 q E i).prod aux) (κ := kr i) hinner]
      have hg' := hinner.lintegral_kernel_prod_right' (κ := kr i)
      exact (lintegral_prod (μ := eventRemainderLaw control0 q E i) (ν := aux)
        _ hg'.aemeasurable).symm

private theorem restore_currentControl (E : Set (SourceInput p))
    (hinv : ∀ z c, replaceSourceControl p q z c ∈ E ↔ z ∈ E)
    (i : Fin (M p)) (r : EventRemainder control0 q E i) (c : TimeControl p) :
    ReferenceFirstCollectionRenewalVectorInsertion.c q
      (restoreEventSource control0 q E hinv i (r, c)).val = c := by
  have hi := fixedControlSplit_symm_coordinatorIndex p i q c r.val r.property.1
  change (((fixedControlSplit p i q).symm (c, r.val)).1.2
    (sourceCoordinatorIndex p ((fixedControlSplit p i q).symm (c, r.val)))).2 q = c
  rw [hi]
  exact fixedControlSplit_symm_control p i q c r.val

include htq in
private theorem insert_future_control (s : SourceInput p) (v : Vector p) :
    ReferenceFirstCollectionRenewalVectorInsertion.c q
        (ReferenceFirstCollectionRenewalVectorInsertion.insert t s v) =
      ReferenceFirstCollectionRenewalVectorInsertion.c q s := by
  have hne : q ≠ t := by intro h; subst q; exact Nat.lt_irrefl _ htq
  have hi := (ReferenceFirstCollectionRenewalVectorInsertion.insert_identity_private_selector
    t s v).2.2
  change ((ReferenceFirstCollectionRenewalVectorInsertion.insert t s v).1.2
    (ReferenceFirstCollectionRenewalVectorInsertion.q
      (ReferenceFirstCollectionRenewalVectorInsertion.insert t s v))).2 q = _
  rw [hi]
  exact ReferenceFirstCollectionRenewalVectorInsertion.insert_other_time t s v q hne

/-- Both actual full-source readouts contain the SAME exposed future control. -/
theorem nonrenewedRestore_same_control (i : Fin (M p))
    (r : NonrenewedRemainder rate rewards C_star C_h control0 u t q i)
    (v : Vector p) (c : TimeControl p) :
    (ReferenceFirstCollectionRenewalVectorInsertion.c q
        (nonrenewedRestore rate rewards C_star C_h control0 u t q htq i (r, c)).val,
      ReferenceFirstCollectionRenewalVectorInsertion.c q
        (ReferenceFirstNextInstallationCellFactors.nonrenewedFirstSource
          rate rewards C_star C_h t u
          (nonrenewedRestore rate rewards C_star C_h control0 u t q htq i (r, c)) v).val) =
      (c, c) := by
  have hc : ReferenceFirstCollectionRenewalVectorInsertion.c q
      (nonrenewedRestore rate rewards C_star C_h control0 u t q htq i (r, c)).val = c :=
    restore_currentControl control0 q _ _ i r c
  refine Prod.ext hc ?_
  exact (insert_future_control t q htq _ v).trans hc

theorem renewedRestore_same_control (i : Fin (M p))
    (r : RenewedRemainder rate rewards C_star C_h control0 u t q i)
    (v : Vector p) (c : TimeControl p) :
    (ReferenceFirstCollectionRenewalVectorInsertion.c q
        (renewedRestore rate rewards C_star C_h control0 u t q htq i (r, c)).val,
      ReferenceFirstCollectionRenewalVectorInsertion.c q
        (ReferenceFirstCollectionRenewalVectorInsertion.put rate rewards C_star C_h u t
          (renewedRestore rate rewards C_star C_h control0 u t q htq i (r, c)) v).val) =
      (c, c) := by
  have hc : ReferenceFirstCollectionRenewalVectorInsertion.c q
      (renewedRestore rate rewards C_star C_h control0 u t q htq i (r, c)).val = c :=
    restore_currentControl control0 q _ _ i r c
  refine Prod.ext hc ?_
  rw [ReferenceFirstCollectionRenewalVectorInsertion.put_val]
  exact (insert_future_control t q htq _ v).trans hc

/-- Full original/inserted readout, with every auxiliary and vector coordinate
unchanged, and the SAME `c` restored in both complete sources. -/
theorem nonrenewedRestoreLift_readout (i : Fin (M p))
    (r : NonrenewedRemainder rate rewards C_star C_h control0 u t q i)
    (a : AuxArray p) (v : Vector p) (c : TimeControl p) :
    let w := nonrenewedRestoreLift rate rewards C_star C_h control0 u t q htq i (((r, a), v), c)
    (((w.1.1.val, (ReferenceFirstNextInstallationCellFactors.nonrenewedFirstSource
        rate rewards C_star C_h t u w.1.1 w.2).val), w.1.2), w.2) =
    (((replaceSourceControl p q
        (nonrenewedRestore rate rewards C_star C_h control0 u t q htq i (r, control0)).val c,
      replaceSourceControl p q
        (ReferenceFirstNextInstallationCellFactors.nonrenewedFirstSource
          rate rewards C_star C_h t u
          (nonrenewedRestore rate rewards C_star C_h control0 u t q htq i (r, control0)) v).val c),
      a), v) := by
  dsimp only [nonrenewedRestoreLift]
  rw [nonrenewedRestore_eq_replace, nonrenewedFirstSource_replace_future]
  rfl

theorem renewedRestoreLift_readout (i : Fin (M p))
    (r : RenewedRemainder rate rewards C_star C_h control0 u t q i)
    (a : AuxArray p) (v : Vector p) (c : TimeControl p) :
    let w := renewedRestoreLift rate rewards C_star C_h control0 u t q htq i (((r, a), v), c)
    (((w.1.1.val, (ReferenceFirstCollectionRenewalVectorInsertion.put
        rate rewards C_star C_h u t w.1.1 w.2).val), w.1.2), w.2) =
    (((replaceSourceControl p q
        (renewedRestore rate rewards C_star C_h control0 u t q htq i (r, control0)).val c,
      replaceSourceControl p q
        (ReferenceFirstCollectionRenewalVectorInsertion.put rate rewards C_star C_h u t
          (renewedRestore rate rewards C_star C_h control0 u t q htq i (r, control0)) v).val c),
      a), v) := by
  dsimp only [renewedRestoreLift]
  rw [renewedRestore_eq_replace, renewedPut_replace_future]
  rfl

/-- All original private coordinates, including the separate selecting `J`,
are identical in the restored and inserted readouts. -/
theorem nonrenewedRestore_private (i : Fin (M p))
    (r : NonrenewedRemainder rate rewards C_star C_h control0 u t q i)
    (v : Vector p) (c : TimeControl p) :
    ((nonrenewedRestore rate rewards C_star C_h control0 u t q htq i (r, c)).val.2,
      (ReferenceFirstNextInstallationCellFactors.nonrenewedFirstSource rate rewards C_star C_h t u
        (nonrenewedRestore rate rewards C_star C_h control0 u t q htq i (r, c)) v).val.2) =
      (r.val.2, r.val.2) := by
  have hp : (nonrenewedRestore rate rewards C_star C_h control0 u t q htq i (r, c)).val.2 =
      r.val.2 := fixedControlSplit_symm_private p i q c r.val
  refine Prod.ext hp ?_
  exact (ReferenceFirstCollectionRenewalVectorInsertion.insert_identity_private_selector
    t _ v).2.1.trans hp

theorem renewedRestore_private (i : Fin (M p))
    (r : RenewedRemainder rate rewards C_star C_h control0 u t q i)
    (v : Vector p) (c : TimeControl p) :
    ((renewedRestore rate rewards C_star C_h control0 u t q htq i (r, c)).val.2,
      (ReferenceFirstCollectionRenewalVectorInsertion.put rate rewards C_star C_h u t
        (renewedRestore rate rewards C_star C_h control0 u t q htq i (r, c)) v).val.2) =
      (r.val.2, r.val.2) := by
  have hp : (renewedRestore rate rewards C_star C_h control0 u t q htq i (r, c)).val.2 =
      r.val.2 := fixedControlSplit_symm_private p i q c r.val
  refine Prod.ext hp ?_
  rw [ReferenceFirstCollectionRenewalVectorInsertion.put_val]
  exact (ReferenceFirstCollectionRenewalVectorInsertion.insert_identity_private_selector
    t _ v).2.1.trans hp

end Remainders

end Bandits.Support.ReferenceFirstNextLiftFutureControl
