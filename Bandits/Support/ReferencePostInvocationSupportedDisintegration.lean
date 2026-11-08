/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferencePostInvocationPrefixLocality
public import Bandits.Support.ReferencePostInvocationGeneratedAlignment
public import Bandits.Support.ReferenceFirstNextLiftFutureControl
public import Bandits.Support.ReferenceFirstNextLiftFutureAuxiliaryPairLaw

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
# Supported disintegration of the literal post-invocation lifts

The branch parameter is `false` for the original nonrenewed lift and `true`
for the original renewed lift. All measures retain their event and selected
private-index masses. Reconstruction retains the whole source, auxiliary
array, and assignment vector, rather than just their logical marginals.
The supported observer is an actual selected-observer image. The resulting
bounded surviving full-source identity supplies restoration for later native-law
assembly; no native finite outcome masses or one-round law are asserted.

Sources: ZIP4 `06_interruptions.tex:391-426`,
`04_slow_fast_learner.tex:142-215,323-390`, and `08_main_theorem.tex:78-109`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal Classical
open Bandits.Support ConstructorDimensions
open ReferenceFixedTimeSourceControlCoupling
open ReferenceFirstNextInstallationTransitionLaw

namespace Bandits.Support.ReferencePostInvocationSupportedDisintegration


variable {p : ConstructorDimensions.Parameters}

abbrev Auxiliary := ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray
abbrev Vector := AssignmentParameterFibreKernel.AssignmentVector
abbrev Control := ContinuousLearningRows.TimeControl
abbrev Scalar := ContinuousControlSlice.Scalar

local instance sourceMeasurableSpace :
    MeasurableSpace (BootstrapPrivateRoundStreams.SourceInput p) := by
  change MeasurableSpace (CompletePublicTable.PublishedOutput p ×
    BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

local instance controlMeasurableSpace : MeasurableSpace (Control p) := by
  unfold Control ContinuousLearningRows.TimeControl
  infer_instance

local instance auxiliaryMeasurableSpace : MeasurableSpace (Auxiliary p) := by
  unfold Auxiliary ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray
  infer_instance

local instance vectorMeasurableSpace : MeasurableSpace (Vector p) := by
  unfold Vector AssignmentParameterFibreKernel.AssignmentVector
  infer_instance

local instance optionMeasurableSpace {X : Type*} [MeasurableSpace X] :
    MeasurableSpace (Option X) := LaterAssignmentStartMeasurability.optionMeasurableSpace

variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
  (control0 : Control p) (b : Bool) (u t q : Fin p.T) (htq : t.val < q.val)

local notation "Lift" => ReferencePostInvocationPrefixLocality.BranchLift rate rewards C_star C_h b u t

section LiteralLifts

local instance slowSetMeasurableSpace :
    MeasurableSpace (ReferenceFirstLiveChronologicalPrefixFoundation.SlowSet p) := ⊤

local instance slowSetDiscrete : DiscreteMeasurableSpace
    (ReferenceFirstLiveChronologicalPrefixFoundation.SlowSet p) := ⟨fun _ => trivial⟩

/-- The two original fibre-weighted laws, without event normalization. -/
def branchLaw : Measure Lift := match b with
  | false => ReferenceFirstNextInvocationJointLift.nonrenewedLiftLaw
      rate rewards C_star C_h u t control0
  | true => ReferenceFirstCollectionRenewalInstallationCoupling.renewalLiftLaw
      rate rewards C_star C_h u t

abbrev Remainder (i : Fin (M p)) :=
  EventRemainder control0 q (ReferencePostInvocationPrefixLocality.branchEvent rate rewards C_star C_h b u t) i

abbrev RemainderLift (i : Fin (M p)) :=
  ((Remainder rate rewards C_star C_h control0 b u t q i × Auxiliary p) × Vector p)

/-- The accepted whole-control remainder law on the original private stratum. -/
def remainderLaw (i : Fin (M p)) :
    Measure (RemainderLift rate rewards C_star C_h control0 b u t q i) := match b with
  | false => ReferenceFirstNextLiftFutureControl.nonrenewedRemainderLiftLaw rate rewards C_star C_h control0 u t q htq i
  | true => ReferenceFirstNextLiftFutureControl.renewedRemainderLiftLaw rate rewards C_star C_h control0 u t q htq i

instance remainderLaw_finite (i : Fin (M p)) :
    IsFiniteMeasure (remainderLaw rate rewards C_star C_h control0 b u t q htq i) := by
  cases b
  · exact ReferenceFirstNextLiftFutureControl.nonrenewedRemainderLiftLaw_finite rate rewards C_star C_h control0 u t q htq i
  · exact ReferenceFirstNextLiftFutureControl.renewedRemainderLiftLaw_finite rate rewards C_star C_h control0 u t q htq i

/-- Restore the SAME physical control, with intrinsic original-event typing. -/
def restoreControl (i : Fin (M p))
    (w : RemainderLift rate rewards C_star C_h control0 b u t q i × Control p) : Lift :=
  ((restoreEventSource control0 q (ReferencePostInvocationPrefixLocality.branchEvent rate rewards C_star C_h b u t)
    (ReferencePostInvocationPrefixLocality.branchEvent_futureControl_iff rate rewards C_star C_h control0 b u t q htq)
      i (w.1.1.1, w.2), w.1.1.2), w.1.2)

theorem measurable_restoreControl (i : Fin (M p)) :
    Measurable (restoreControl rate rewards C_star C_h control0 b u t q htq i) :=
  (((measurable_restoreEventSource control0 q _ _ i).comp
    (measurable_fst.fst.fst.prodMk measurable_snd)).prodMk
      measurable_fst.fst.snd).prodMk measurable_fst.snd

theorem branchLaw_eq_sum_restore_control :
    branchLaw rate rewards C_star C_h control0 b u t =
      Measure.sum (fun i : Fin (M p) =>
        ((remainderLaw rate rewards C_star C_h control0 b u t q htq i).prod
          (ContinuousLearningRows.timeControlLaw p)).map
            (restoreControl rate rewards C_star C_h control0 b u t q htq i)) := by
  cases b
  · exact ReferenceFirstNextLiftFutureControl.nonrenewedLiftLaw_eq_sum_restore_future
      rate rewards C_star C_h control0 u t q htq
  · exact ReferenceFirstNextLiftFutureControl.renewedLiftLaw_eq_sum_restore_future
      rate rewards C_star C_h control0 u t q htq

include htq in
theorem branchLaw_eq_restore_pair :
    branchLaw rate rewards C_star C_h control0 b u t =
      (((branchLaw rate rewards C_star C_h control0 b u t).map (ReferenceFirstNextLiftFutureAuxiliaryPairLaw.eraseLift q)).prod
        (ContinuousControlSlice.scalarLaw.prod ContinuousControlSlice.scalarLaw)).map
          (ReferenceFirstNextLiftFutureAuxiliaryPairLaw.restoreLift q) := by
  cases b
  · exact ReferenceFirstNextLiftFutureAuxiliaryPairLaw.nonrenewedLiftLaw_eq_restore_pair rate rewards C_star C_h u t q htq control0
  · exact ReferenceFirstNextLiftFutureAuxiliaryPairLaw.renewalLiftLaw_eq_restore_pair rate rewards C_star C_h u t q htq

/-- The innovation block contains the whole control and both distinct labels. -/
abbrev Innovation (p : ConstructorDimensions.Parameters) := Control p × (Scalar × Scalar)

def innovationLaw : Measure (Innovation p) :=
  (ContinuousLearningRows.timeControlLaw p).prod
    (ContinuousControlSlice.scalarLaw.prod ContinuousControlSlice.scalarLaw)

instance innovationLaw_probability : IsProbabilityMeasure (innovationLaw (p := p)) := by
  unfold innovationLaw
  infer_instance

/-- Erase only the tested auxiliary pair in the accepted control remainder. -/
def erasedRemainderLaw (i : Fin (M p)) :
    Measure (RemainderLift rate rewards C_star C_h control0 b u t q i) :=
  (remainderLaw rate rewards C_star C_h control0 b u t q htq i).map (ReferenceFirstNextLiftFutureAuxiliaryPairLaw.eraseLift q)

/-- Restore both innovations to the original, unmodified literal lift type. -/
def restoreInnovation (i : Fin (M p))
    (w : RemainderLift rate rewards C_star C_h control0 b u t q i × Innovation p) : Lift :=
  ReferenceFirstNextLiftFutureAuxiliaryPairLaw.restoreLift q
    (restoreControl rate rewards C_star C_h control0 b u t q htq i (w.1, w.2.1), w.2.2)

theorem measurable_restoreInnovation (i : Fin (M p)) :
    Measurable (restoreInnovation rate rewards C_star C_h control0 b u t q htq i) :=
  (ReferenceFirstNextLiftFutureAuxiliaryPairLaw.measurable_restoreLift q).comp
    (((measurable_restoreControl rate rewards C_star C_h control0 b u t q htq i).comp
      (measurable_fst.prodMk measurable_snd.fst)).prodMk measurable_snd.snd)

/-- The physical control is the SAME in both full sources; the auxiliary
pair is the SAME pair used by the literal cell constructor. -/
theorem restoreInnovation_coordinates (i : Fin (M p))
    (w : RemainderLift rate rewards C_star C_h control0 b u t q i) (ω : Innovation p) :
    let restored := restoreInnovation rate rewards C_star C_h control0 b u t q htq i (w, ω)
    (ReferenceFirstCollectionRenewalVectorInsertion.c q restored.1.1.val,
      ReferenceFirstCollectionRenewalVectorInsertion.c q
        (ReferencePostInvocationNoncallGeometry.insertedPhysicalSource rate
          (ReferencePostInvocationPrefixLocality.branchTransition
            rate rewards C_star C_h control0 b u t restored))) = (ω.1, ω.1) ∧
    ReferenceFirstNextLiftFutureAuxiliaryPairLaw.auxiliaryPair q restored.1.2 = ω.2 := by
  constructor
  · cases b
    · exact ReferenceFirstNextLiftFutureControl.nonrenewedRestore_same_control
        rate rewards C_star C_h control0 u t q htq i w.1.1 w.2 ω.1
    · exact ReferenceFirstNextLiftFutureControl.renewedRestore_same_control
        rate rewards C_star C_h control0 u t q htq i w.1.1 w.2 ω.1
  · simp only [restoreInnovation, ReferenceFirstNextLiftFutureAuxiliaryPairLaw.restoreLift,
      ReferenceFirstNextLiftFutureAuxiliaryPairLaw.auxiliaryPair,
      ReferenceFirstNextLiftFutureAuxiliaryPairLaw.fillAuxiliaryPair, Function.update_self,
      Function.update_of_ne (show (q, (0 : Fin 2)) ≠ (q, (1 : Fin 2)) by simp), Prod.mk.eta]

/-- BOTH original lifts factor simultaneously over the SAME whole physical
control and the SAME original auxiliary pair. No stratum mass is divided out. -/
theorem branchLaw_eq_sum_restore_innovation :
    branchLaw rate rewards C_star C_h control0 b u t =
      Measure.sum (fun i : Fin (M p) =>
        ((erasedRemainderLaw rate rewards C_star C_h control0 b u t q htq i).prod
          (innovationLaw (p := p))).map
            (restoreInnovation rate rewards C_star C_h control0 b u t q htq i)) := by
  let tc := ContinuousLearningRows.timeControlLaw p
  let pair := ContinuousControlSlice.scalarLaw.prod ContinuousControlSlice.scalarLaw
  let μ := remainderLaw rate rewards C_star C_h control0 b u t q htq
  let ρ := restoreControl rate rewards C_star C_h control0 b u t q htq
  have hzero : (branchLaw rate rewards C_star C_h control0 b u t).map (ReferenceFirstNextLiftFutureAuxiliaryPairLaw.eraseLift q) =
      Measure.sum (fun i : Fin (M p) =>
        (((μ i).map (ReferenceFirstNextLiftFutureAuxiliaryPairLaw.eraseLift q)).prod tc).map (ρ i)) := by
    rw [branchLaw_eq_sum_restore_control rate rewards C_star C_h control0 b u t q htq,
      Measure.map_sum (ReferenceFirstNextLiftFutureAuxiliaryPairLaw.measurable_eraseLift q).aemeasurable]
    congr 1
    funext i
    rw [Measure.map_map (ReferenceFirstNextLiftFutureAuxiliaryPairLaw.measurable_eraseLift q)
      (measurable_restoreControl rate rewards C_star C_h control0 b u t q htq i)]
    conv_rhs => rw [← Measure.map_id (μ := tc)]
    rw [Measure.map_prod_map _ _ (ReferenceFirstNextLiftFutureAuxiliaryPairLaw.measurable_eraseLift q) measurable_id,
      Measure.map_map (measurable_restoreControl rate rewards C_star C_h control0 b u t q htq i)
        ((ReferenceFirstNextLiftFutureAuxiliaryPairLaw.measurable_eraseLift q).prodMap measurable_id)]
    rfl
  rw [branchLaw_eq_restore_pair rate rewards C_star C_h control0 b u t q htq, hzero,
    Measure.prod_sum_left, Measure.map_sum (ReferenceFirstNextLiftFutureAuxiliaryPairLaw.measurable_restoreLift q).aemeasurable]
  congr 1
  funext i
  change (((((μ i).map (ReferenceFirstNextLiftFutureAuxiliaryPairLaw.eraseLift q)).prod tc).map (ρ i)).prod pair).map
    (ReferenceFirstNextLiftFutureAuxiliaryPairLaw.restoreLift q) = _
  conv_lhs => rw [← Measure.map_id (μ := pair)]
  rw [Measure.map_prod_map _ _
    (measurable_restoreControl rate rewards C_star C_h control0 b u t q htq i) measurable_id,
    Measure.map_map (ReferenceFirstNextLiftFutureAuxiliaryPairLaw.measurable_restoreLift q)
      ((measurable_restoreControl rate rewards C_star C_h control0 b u t q htq i).prodMap measurable_id)]
  change _ = (((μ i).map (ReferenceFirstNextLiftFutureAuxiliaryPairLaw.eraseLift q)).prod (tc.prod pair)).map
    (restoreInnovation rate rewards C_star C_h control0 b u t q htq i)
  conv_rhs => rw [← Measure.prodAssoc_prod
    (μ := (μ i).map (ReferenceFirstNextLiftFutureAuxiliaryPairLaw.eraseLift q))
    (ν := tc) (τ := pair)]
  rw [Measure.map_map
    (measurable_restoreInnovation rate rewards C_star C_h control0 b u t q htq i)
      MeasurableEquiv.prodAssoc.measurable]
  rfl

section Observer

/-- The two labels erased from the genuine accepted observer. -/
def pairLabels : Finset (Fin 2) := {0, 1}

/-- Identify the accepted subtype-indexed innovation with the literal pair. -/
def testedPair (q : Fin p.T) (x : Scalar × Scalar) :
    ReferencePostInvocationPrefixLocality.TestedAuxiliary q pairLabels :=
  fun j => if j.val.2 = 0 then x.1 else x.2

theorem measurable_testedPair : Measurable (testedPair (p := p) q) := by
  apply measurable_pi_iff.mpr
  intro j
  by_cases h : j.val.2 = 0
  · simpa only [testedPair, h, ite_true] using
      (measurable_fst : Measurable (Prod.fst : Scalar × Scalar → Scalar))
  · simpa only [testedPair, h, ite_false] using
      (measurable_snd : Measurable (Prod.snd : Scalar × Scalar → Scalar))

/-- The accepted subtype-product fill is exactly the accepted literal pair fill. -/
theorem auxiliarySplit_fillPair (a : Auxiliary p) (x : Scalar × Scalar) :
    (ReferencePostInvocationPrefixLocality.auxiliarySplit q pairLabels).symm
        (testedPair q x,
          (ReferencePostInvocationPrefixLocality.auxiliarySplit q pairLabels a).2) =
      ReferenceFirstNextLiftFutureAuxiliaryPairLaw.fillAuxiliaryPair q a x := by
  funext j
  rcases j with ⟨v, l⟩
  by_cases hv : v = q
  · subst v
    change (if h : q = q ∧ l ∈ pairLabels then
        testedPair q x ⟨(q, l), h⟩ else a (q, l)) = _
    fin_cases l <;>
      simp [pairLabels, testedPair,
        ReferenceFirstNextLiftFutureAuxiliaryPairLaw.fillAuxiliaryPair]
  · change (if h : v = q ∧ l ∈ pairLabels then
        testedPair q x ⟨(v, l), h⟩ else a (v, l)) = _
    rw [dite_eq_right (fun h => hv h.1)]
    symm
    exact ReferenceFirstNextLiftFutureAuxiliaryPairLaw.fillAuxiliaryPair_apply_other
      q a x (v, l) (fun h => hv (congrArg Prod.fst h))
        (fun h => hv (congrArg Prod.fst h))

variable (i : Fin (M p))

local notation "R" => RemainderLift rate rewards C_star C_h control0 b u t q i
local notation "D" => ReferencePostInvocationPrefixLocality.AdmissibleObserver
  rate rewards C_star C_h control0 b u t q i pairLabels
local notation "observe" => ReferencePostInvocationPrefixLocality.erasedObserver
  rate rewards C_star C_h control0 b u t q i pairLabels

/-- A genuine selected lift, obtained from the accepted remainder by restoring
the reference control. Its generated PAST is computed, never postulated. -/
def referenceSelected (w : R) :
    ReferencePostInvocationPrefixLocality.SelectedBranchLift rate rewards C_star C_h b u t i :=
  ⟨restoreControl rate rewards C_star C_h control0 b u t q htq i (w, control0),
    fixedControlSplit_symm_coordinatorIndex p i q control0 w.1.1.val w.1.1.property.1⟩

theorem measurable_referenceSelected :
    Measurable (referenceSelected rate rewards C_star C_h control0 b u t q htq i) :=
  ((measurable_restoreControl rate rewards C_star C_h control0 b u t q htq i).comp
    (measurable_id.prodMk measurable_const)).subtype_mk

/-- This observer has the actual generated hidden list and numerical PRE. -/
def observedRemainder (w : R) : D :=
  ReferencePostInvocationPrefixLocality.selectedErasedObserver
    rate rewards C_star C_h control0 b u t q htq i pairLabels
      (referenceSelected rate rewards C_star C_h control0 b u t q htq i w)

theorem measurable_observedRemainder :
    Measurable (observedRemainder rate rewards C_star C_h control0 b u t q htq i) :=
  (ReferencePostInvocationPrefixLocality.measurable_selectedErasedObserver
    rate rewards C_star C_h control0 b u t q htq i pairLabels).comp
      (measurable_referenceSelected rate rewards C_star C_h control0 b u t q htq i)

/-- Restore the literal original lift through the accepted erased observer. -/
def restoreObserver (x : D × Innovation p) : Lift :=
  ReferencePostInvocationPrefixLocality.restoreLiteralLift
    rate rewards C_star C_h control0 b u t q htq i pairLabels
      (x.1, (x.2.1, testedPair q x.2.2))

theorem measurable_restoreObserver :
    Measurable (restoreObserver rate rewards C_star C_h control0 b u t q htq i) :=
  (ReferencePostInvocationPrefixLocality.measurable_restoreLiteralLift
    rate rewards C_star C_h control0 b u t q htq i pairLabels).comp
      (measurable_fst.prodMk (measurable_snd.fst.prodMk
        ((measurable_testedPair q).comp measurable_snd.snd)))

/-- Exact reconstruction for every actual remainder, with the SAME source,
private arrays, vector, and both original/inserted current innovations. -/
theorem restoreObserver_observedRemainder (w : R) (ω : Innovation p) :
    restoreObserver rate rewards C_star C_h control0 b u t q htq i
        (observedRemainder rate rewards C_star C_h control0 b u t q htq i w, ω) =
      restoreInnovation rate rewards C_star C_h control0 b u t q htq i (w, ω) := by
  apply Prod.ext
  · apply Prod.ext
    · apply Subtype.ext
      change (fixedControlSplit p i q).symm
        (ω.1, (fixedControlSplit p i q
          ((fixedControlSplit p i q).symm (control0, w.1.1.val))).2) =
        (fixedControlSplit p i q).symm (ω.1, w.1.1.val)
      rw [(fixedControlSplit p i q).apply_symm_apply]
    · exact auxiliarySplit_fillPair q w.1.2 ω.2
  · rfl

/-- Consistency of the entire stored PAST is derived on the actual image.
No assertion is made for an arbitrary admissible record. -/
theorem observedRemainder_consistent (w : R) (ω : Innovation p) :
    observe (restoreObserver rate rewards C_star C_h control0 b u t q htq i
      (observedRemainder rate rewards C_star C_h control0 b u t q htq i w, ω)) =
        (observedRemainder rate rewards C_star C_h control0 b u t q htq i w).val :=
  ReferencePostInvocationPrefixLocality.selectedErasedObserver_reinsert
    rate rewards C_star C_h control0 b u t q htq i pairLabels
      (referenceSelected rate rewards C_star C_h control0 b u t q htq i w)
        ω.1 (testedPair q ω.2)

/-- Restoring the reference control loses no actual selected observer. Thus
the remainder representation has exactly the canonical selected image. -/
theorem range_observedRemainder :
    Set.range (observedRemainder rate rewards C_star C_h control0 b u t q htq i) =
      Set.range (ReferencePostInvocationPrefixLocality.selectedErasedObserver
        rate rewards C_star C_h control0 b u t q htq i pairLabels) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨w, rfl⟩
    exact ⟨referenceSelected rate rewards C_star C_h control0 b u t q htq i w, rfl⟩
  · rintro _ ⟨w, rfl⟩
    let d := ReferencePostInvocationPrefixLocality.selectedErasedObserver
      rate rewards C_star C_h control0 b u t q htq i pairLabels w
    let r : R := ((⟨d.val.1.1.1, d.property⟩, w.val.1.2), w.val.2)
    refine ⟨r, Subtype.ext ?_⟩
    have hr : (referenceSelected rate rewards C_star C_h control0 b u t q htq i r).val =
        ReferencePostInvocationPrefixLocality.restoreLiteralLift
          rate rewards C_star C_h control0 b u t q htq i pairLabels
            (d, (control0, (ReferencePostInvocationPrefixLocality.auxiliarySplit
              q pairLabels w.val.1.2).1)) := by
      apply Prod.ext
      · apply Prod.ext
        · rfl
        · exact ((ReferencePostInvocationPrefixLocality.auxiliarySplit
            q pairLabels).symm_apply_apply w.val.1.2).symm
      · rfl
    change ReferencePostInvocationPrefixLocality.erasedObserver
      rate rewards C_star C_h control0 b u t q i pairLabels
        (referenceSelected rate rewards C_star C_h control0 b u t q htq i r).val = d.val
    rw [hr]
    exact ReferencePostInvocationPrefixLocality.selectedErasedObserver_reinsert
      rate rewards C_star C_h control0 b u t q htq i pairLabels w control0
        (ReferencePostInvocationPrefixLocality.auxiliarySplit q pairLabels w.val.1.2).1

end Observer

section SupportedObserver

variable (i : Fin (M p))

local notation "R" => RemainderLift rate rewards C_star C_h control0 b u t q i
local notation "D" => ReferencePostInvocationPrefixLocality.AdmissibleObserver
  rate rewards C_star C_h control0 b u t q i pairLabels

/-- The image of the ACTUAL selected observer. The intrinsic image witness
establishes stored-history consistency, beyond selected-index/event typing. -/
abbrev SupportedObserver := ↥(Set.range
  (ReferencePostInvocationPrefixLocality.selectedErasedObserver
    rate rewards C_star C_h control0 b u t q htq i pairLabels))

local notation "S" => SupportedObserver rate rewards C_star C_h control0 b u t q htq i

def supportedObservation (w : R) : S :=
  ⟨observedRemainder rate rewards C_star C_h control0 b u t q htq i w,
    referenceSelected rate rewards C_star C_h control0 b u t q htq i w, rfl⟩

theorem measurable_supportedObservation :
    Measurable (supportedObservation rate rewards C_star C_h control0 b u t q htq i) :=
  (measurable_observedRemainder rate rewards C_star C_h control0 b u t q htq i).subtype_mk

def supportedObserverLaw : Measure S :=
  (erasedRemainderLaw rate rewards C_star C_h control0 b u t q htq i).map
    (supportedObservation rate rewards C_star C_h control0 b u t q htq i)

instance erasedRemainderLaw_finite :
    IsFiniteMeasure (erasedRemainderLaw rate rewards C_star C_h control0 b u t q htq i) := by
  unfold erasedRemainderLaw
  infer_instance

instance supportedObserverLaw_finite :
    IsFiniteMeasure (supportedObserverLaw rate rewards C_star C_h control0 b u t q htq i) := by
  unfold supportedObserverLaw
  infer_instance

def restoreSupported (x : S × Innovation p) : Lift :=
  restoreObserver rate rewards C_star C_h control0 b u t q htq i (x.1.val, x.2)

theorem measurable_restoreSupported :
    Measurable (restoreSupported rate rewards C_star C_h control0 b u t q htq i) :=
  (measurable_restoreObserver rate rewards C_star C_h control0 b u t q htq i).comp
    ((measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd)

/-- EVERY point of the image carrier has the actual full stored PAST. -/
theorem supported_consistent (d : S) (ω : Innovation p) :
    ReferencePostInvocationPrefixLocality.erasedObserver
      rate rewards C_star C_h control0 b u t q i pairLabels
        (restoreSupported rate rewards C_star C_h control0 b u t q htq i (d, ω)) =
          d.val.val := by
  obtain ⟨w, hw⟩ := d.property
  change ReferencePostInvocationPrefixLocality.erasedObserver
    rate rewards C_star C_h control0 b u t q i pairLabels
      (restoreObserver rate rewards C_star C_h control0 b u t q htq i (d.val, ω)) = d.val.val
  rw [← hw]
  exact ReferencePostInvocationPrefixLocality.selectedErasedObserver_reinsert
    rate rewards C_star C_h control0 b u t q htq i pairLabels w ω.1 (testedPair q ω.2)

/-- Supported restoration reads back precisely the jointly sampled physical
control from both source fields, and the jointly sampled original pair. -/
theorem restoreSupported_coordinates (d : S) (ω : Innovation p) :
    let restored := restoreSupported rate rewards C_star C_h control0 b u t q htq i (d, ω)
    (ReferenceFirstCollectionRenewalVectorInsertion.c q restored.1.1.val,
      ReferenceFirstCollectionRenewalVectorInsertion.c q
        (ReferencePostInvocationNoncallGeometry.insertedPhysicalSource rate
          (ReferencePostInvocationPrefixLocality.branchTransition
            rate rewards C_star C_h control0 b u t restored))) = (ω.1, ω.1) ∧
    ReferenceFirstNextLiftFutureAuxiliaryPairLaw.auxiliaryPair q restored.1.2 = ω.2 := by
  have hd : d.val ∈ Set.range
      (observedRemainder rate rewards C_star C_h control0 b u t q htq i) := by
    rw [range_observedRemainder rate rewards C_star C_h control0 b u t q htq i]
    exact d.property
  obtain ⟨w, hw⟩ := hd
  have hrest : restoreSupported rate rewards C_star C_h control0 b u t q htq i (d, ω) =
      restoreInnovation rate rewards C_star C_h control0 b u t q htq i (w, ω) := by
    change restoreObserver rate rewards C_star C_h control0 b u t q htq i (d.val, ω) = _
    rw [← hw]
    exact restoreObserver_observedRemainder rate rewards C_star C_h control0 b u t q htq i w ω
  dsimp only
  rw [hrest]
  exact restoreInnovation_coordinates rate rewards C_star C_h control0 b u t q htq i w ω

/-- On BOTH literal lifts the inserted full-source family is obtained by
replacing precisely the SAME whole control. The auxiliary pair and stored
history are never used to choose a different physical source. -/
theorem restoreSupported_inserted_source (d : S) (ω ω' : Innovation p) :
    let z := fun x => ReferencePostInvocationNoncallGeometry.insertedPhysicalSource rate
      (ReferencePostInvocationPrefixLocality.branchTransition rate rewards C_star C_h control0 b u t
        (restoreSupported rate rewards C_star C_h control0 b u t q htq i (d, x)))
    z ω = replaceSourceControl p q (z ω') ω.1 := by
  let w := restoreSupported rate rewards C_star C_h control0 b u t q htq i (d, ω)
  let w' := restoreSupported rate rewards C_star C_h control0 b u t q htq i (d, ω')
  have hi : sourceCoordinatorIndex p w'.1.1.val = i := by
    change PrivateSourceStreams.coordinatorIndex p
      ((fixedControlSplit p i q).symm (ω'.1, d.val.val.1.1.1)).2.1.2 = i
    rw [fixedControlSplit_symm_private]
    exact d.val.property.1
  have hs : w.1.1.val = replaceSourceControl p q w'.1.1.val ω.1 := by
    have h := fixedControlSplit_replaceSourceControl p i q w'.1.1.val ω.1 hi
    change (fixedControlSplit p i q).symm (ω.1, (fixedControlSplit p i q
      ((fixedControlSplit p i q).symm (ω'.1, d.val.val.1.1.1))).2) = _ at h
    rw [(fixedControlSplit p i q).apply_symm_apply] at h
    exact h
  cases b
  all_goals
    first
    | change ReferenceFirstCollectionRenewalVectorInsertion.insert t w.1.1.val w.2 =
        replaceSourceControl p q (ReferenceFirstCollectionRenewalVectorInsertion.insert t w'.1.1.val w'.2) ω.1
    | change (ReferenceFirstCollectionRenewalVectorInsertion.put rate rewards C_star C_h u t
        ⟨w.1.1.val, w.1.1.property⟩ w.2).val = replaceSourceControl p q
          (ReferenceFirstCollectionRenewalVectorInsertion.put rate rewards C_star C_h u t
            ⟨w'.1.1.val, w'.1.1.property⟩ w'.2).val ω.1
      simp only [ReferenceFirstCollectionRenewalVectorInsertion.put_val]
    rw [hs, ReferencePostInvocationPrefixLocality.insert_futureControl
      t q (Fin.ne_of_val_ne (Nat.ne_of_lt htq))]
    rfl

/-- Entire old hidden list, incoming logical seed, and full numerical PRE,
read from the SAME restored original source. No history premise is supplied. -/
theorem supported_prefix_readout (d : S) (ω : Innovation p) :
    let w := restoreSupported rate rewards C_star C_h control0 b u t q htq i (d, ω)
    let transition := ReferencePostInvocationPrefixLocality.branchTransition
      rate rewards C_star C_h control0 b u t w
    ReferencePostInvocationPrefixLocality.erasedPrefixReadout rate t q i pairLabels d.val.val =
      (ReferencePostInvocationNoncallGeometry.postInvocationPrefix rate rewards C_star C_h
        t q.castSucc transition w.1.2,
      ReferencePostInvocationNoncallGeometry.prefixNumerical rate rewards C_star C_h q.castSucc
        (ReferencePostInvocationNoncallGeometry.insertedPhysicalSource rate transition)) := by
  dsimp only
  rw [← supported_consistent rate rewards C_star C_h control0 b u t q htq i d ω]
  exact ReferencePostInvocationPrefixLocality.erasedPrefixReadout_actual
    rate rewards C_star C_h control0 b u t q i pairLabels _

/-- The literal surviving-prefix/current-noCall domain at the next boundary. -/
def survivingDomain : Set Lift := {w |
  (ReferencePostInvocationNoncallGeometry.postInvocationPrefix rate rewards C_star C_h
    t q.castSucc (ReferencePostInvocationPrefixLocality.branchTransition
      rate rewards C_star C_h control0 b u t w) w.1.2).isSome = true ∧
  ReferenceFirstCollectionLogicalPrefixExtension.noCallAt rate rewards C_star C_h q
    (ReferencePostInvocationNoncallGeometry.insertedPhysicalSource rate
      (ReferencePostInvocationPrefixLocality.branchTransition
        rate rewards C_star C_h control0 b u t w))}

include htq in
theorem survivingDomain_iff_next_prefix (w : Lift) :
    w ∈ survivingDomain rate rewards C_star C_h control0 b u t q ↔
      (ReferencePostInvocationNoncallGeometry.postInvocationPrefix rate rewards C_star C_h
        t q.succ (ReferencePostInvocationPrefixLocality.branchTransition
          rate rewards C_star C_h control0 b u t w) w.1.2).isSome = true := by
  let transition := ReferencePostInvocationPrefixLocality.branchTransition
    rate rewards C_star C_h control0 b u t w
  let z := ReferencePostInvocationNoncallGeometry.insertedPhysicalSource rate transition
  let initial := (ReferencePostInvocationNoncallGeometry.postSeed rate transition,
    ReferenceFirstNextInstallationTransitionLaw.postHistory transition)
  change (ReferencePostInvocationNoncallGeometry.noncallCalendar rate rewards C_star C_h
    t z w.1.2 initial q.val).isSome = true ∧
      ReferenceFirstCollectionLogicalPrefixExtension.noCallAt rate rewards C_star C_h q z ↔
    (ReferencePostInvocationNoncallGeometry.noncallCalendar rate rewards C_star C_h
      t z w.1.2 initial (q.val + 1)).isSome = true
  rw [ReferencePostInvocationNoncallGeometry.noncallCalendar]
  cases hp : ReferencePostInvocationNoncallGeometry.noncallCalendar
    rate rewards C_star C_h t z w.1.2 initial q.val with
  | none => simp only [Option.isSome_none, Bool.false_eq_true, false_and, Option.bind_none]
  | some s =>
    rw [Option.bind_some, dite_eq_left ⟨htq, q.isLt⟩]
    by_cases hc : ReferenceFirstCollectionLogicalPrefixExtension.noCallAt rate rewards C_star C_h q z
    · simp only [hc, ite_true, Option.isSome_some, true_and]
    · simp only [hc, ite_false, Option.isSome_none, Bool.false_eq_true, and_false]

include i in
theorem measurableSet_survivingDomain :
    MeasurableSet (survivingDomain rate rewards C_star C_h control0 b u t q) := by
  have h := (ReferencePostInvocationPrefixLocality.measurableSet_erasedKillGate
    rate rewards C_star C_h control0 t q i pairLabels).preimage
      (ReferencePostInvocationPrefixLocality.measurable_erasedObserver
        rate rewards C_star C_h control0 b u t q i pairLabels)
  convert h using 1
  ext w
  exact (ReferencePostInvocationPrefixLocality.erasedKillGate_actual
    rate rewards C_star C_h control0 b u t q i pairLabels w).symm

def observerGate : Set S := {d |
  ReferencePostInvocationPrefixLocality.erasedKillGate rate rewards C_star C_h t q i pairLabels d.val.val}

theorem measurableSet_observerGate :
    MeasurableSet (observerGate rate rewards C_star C_h control0 b u t q htq i) :=
  (ReferencePostInvocationPrefixLocality.measurableSet_erasedKillGate
    rate rewards C_star C_h control0 t q i pairLabels).preimage
      (measurable_subtype_coe.comp measurable_subtype_coe)

/-- The actual kill/noCall restriction uses no tested innovation on the actual
supported observer. The full sources themselves remain joint readouts. -/
theorem survivingDomain_restoreSupported (d : S) (ω : Innovation p) :
    restoreSupported rate rewards C_star C_h control0 b u t q htq i (d, ω) ∈
      survivingDomain rate rewards C_star C_h control0 b u t q ↔
    d ∈ observerGate rate rewards C_star C_h control0 b u t q htq i := by
  change _ ∧ _ ↔ ReferencePostInvocationPrefixLocality.erasedKillGate
    rate rewards C_star C_h t q i pairLabels d.val.val
  rw [← ReferencePostInvocationPrefixLocality.erasedKillGate_actual
    rate rewards C_star C_h control0 b u t q i pairLabels,
    supported_consistent rate rewards C_star C_h control0 b u t q htq i d ω]

theorem branchLaw_eq_sum_restore_supported :
    branchLaw rate rewards C_star C_h control0 b u t =
      Measure.sum (fun i : Fin (M p) =>
        ((supportedObserverLaw rate rewards C_star C_h control0 b u t q htq i).prod
          (innovationLaw (p := p))).map
            (restoreSupported rate rewards C_star C_h control0 b u t q htq i)) := by
  rw [branchLaw_eq_sum_restore_innovation rate rewards C_star C_h control0 b u t q htq]
  congr 1
  funext i
  unfold supportedObserverLaw
  conv_rhs => rw [← Measure.map_id (μ := innovationLaw (p := p))]
  rw [Measure.map_prod_map _ _
    (measurable_supportedObservation rate rewards C_star C_h control0 b u t q htq i) measurable_id,
    Measure.map_map (measurable_restoreSupported rate rewards C_star C_h control0 b u t q htq i)
      ((measurable_supportedObservation rate rewards C_star C_h control0 b u t q htq i).prodMap measurable_id)]
  congr 1
  funext x
  exact (restoreObserver_observedRemainder rate rewards C_star C_h control0 b u t q htq i x.1 x.2).symm

end SupportedObserver

/-- The SAME local factorization, restricted by the actual surviving prefix.
Only the erased supported observer is restricted; innovation laws stay native. -/
theorem branchLaw_restrict_eq_sum_restore_supported :
    (branchLaw rate rewards C_star C_h control0 b u t).restrict
      (survivingDomain rate rewards C_star C_h control0 b u t q) =
    Measure.sum (fun i : Fin (M p) =>
      (((supportedObserverLaw rate rewards C_star C_h control0 b u t q htq i).restrict
        (observerGate rate rewards C_star C_h control0 b u t q htq i)).prod
          (innovationLaw (p := p))).map
            (restoreSupported rate rewards C_star C_h control0 b u t q htq i)) := by
  have hE := measurableSet_survivingDomain rate rewards C_star C_h control0 b u t q
    ⟨0, M_pos p⟩
  rw [branchLaw_eq_sum_restore_supported rate rewards C_star C_h control0 b u t q htq,
    Measure.restrict_sum _ hE]
  congr 1
  funext i
  rw [Measure.restrict_map
    (measurable_restoreSupported rate rewards C_star C_h control0 b u t q htq i) hE]
  have hpre : (restoreSupported rate rewards C_star C_h control0 b u t q htq i) ⁻¹'
      (survivingDomain rate rewards C_star C_h control0 b u t q) =
        (observerGate rate rewards C_star C_h control0 b u t q htq i) ×ˢ Set.univ := by
    ext x
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, and_true]
    exact survivingDomain_restoreSupported rate rewards C_star C_h control0 b u t q htq i x.1 x.2
  rw [hpre, ← Measure.restrict_prod_eq_prod_univ]

/-- Actual bounded Borel JOINT tests on BOTH literal surviving lifts. Every
original/inserted source and auxiliary coordinate is evaluated with the very
innovation being integrated, including the first detecting overflow update. -/
theorem surviving_joint_integral
    (Phi : ReferencePostInvocationNoncallGeometry.PrefixObservation rate t q.succ → ℝ)
    (hPhi : Measurable Phi) (B : ℝ) (hB : ∀ o, ‖Phi o‖ ≤ B) :
    (∫ w, Phi (ReferencePostInvocationPrefixLocality.branchObservation
        rate rewards C_star C_h control0 b u t q.succ w)
      ∂(branchLaw rate rewards C_star C_h control0 b u t).restrict
        (survivingDomain rate rewards C_star C_h control0 b u t q)) =
    ∑ i : Fin (M p),
      ∫ d in observerGate rate rewards C_star C_h control0 b u t q htq i,
        ∫ ω, Phi (ReferencePostInvocationPrefixLocality.branchObservation
          rate rewards C_star C_h control0 b u t q.succ
            (restoreSupported rate rewards C_star C_h control0 b u t q htq i (d, ω)))
          ∂innovationLaw (p := p)
        ∂supportedObserverLaw rate rewards C_star C_h control0 b u t q htq i := by
  let f : Lift → ℝ := fun w => Phi
    (ReferencePostInvocationPrefixLocality.branchObservation
      rate rewards C_star C_h control0 b u t q.succ w)
  have hf : Measurable f := hPhi.comp
    (ReferencePostInvocationPrefixLocality.measurable_branchObservation
      rate rewards C_star C_h control0 b u t q.succ)
  have hfB : ∀ w, ‖f w‖ ≤ B := fun w => hB _
  rw [branchLaw_restrict_eq_sum_restore_supported
    rate rewards C_star C_h control0 b u t q htq, Measure.sum_fintype]
  rw [integral_finsetSum_measure (fun i _ =>
    Integrable.of_bound hf.aestronglyMeasurable B (Filter.Eventually.of_forall hfB))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_map
    (measurable_restoreSupported rate rewards C_star C_h control0 b u t q htq i).aemeasurable
    hf.aestronglyMeasurable]
  exact integral_prod _ (Integrable.of_bound
    (hf.comp (measurable_restoreSupported rate rewards C_star C_h control0 b u t q htq i)).aestronglyMeasurable
      B (Filter.Eventually.of_forall (fun x => hfB _)))

section GeneratedAlignment

open ReferenceFirstLiveChronologicalPrefixFoundation

include htq in
/-- Native LIVE seed and numerical complement on each original lift. The
generated prefix is computed in the conclusion, rather than supplied. -/
theorem branch_live_alignment (w : Lift) :
    let transition := ReferencePostInvocationPrefixLocality.branchTransition
      rate rewards C_star C_h control0 b u t w
    let z := ReferencePostInvocationNoncallGeometry.insertedPhysicalSource rate transition
    match ReferencePostInvocationNoncallGeometry.postInvocationPrefix rate rewards C_star C_h
      t q.castSucc transition w.1.2 with
    | none => True
    | some s =>
      ∀ hlive : z ∈ ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualDomain
          rate rewards C_star C_h q,
        let live := ReferencePostInvocationNoncallGeometry.continuingSourceCell
          rate rewards C_star C_h q ⟨z, hlive⟩
        let S := ReferencePostInvocationNoncallGeometry.continuingBefore
          rate rewards C_star C_h q ⟨z, hlive⟩
        S.overflow = false → s.1 = live.selected.view.payload.slowSet ∧
          ∀ j : CanonicalFastSampling.FastArm live.selected.view.payload.slowSet,
            live.selected.view.complementWeights j =
              RecordedQueueRun.scoreWeight (ReferenceFirstLaunchNumericalCell.queueParameters rate) S j.val := by
  cases b
  all_goals
    first
    | have ha := ReferencePostInvocationGeneratedAlignment.nonrenewed_generated_alignment
        rate rewards C_star C_h control0 u t q htq w
    | have ha := ReferencePostInvocationGeneratedAlignment.renewed_generated_alignment
        rate rewards C_star C_h control0 u t q htq w
    dsimp only [ReferencePostInvocationPrefixLocality.branchTransition] at ha ⊢
    split at ha
    · simp_all only
    · rename_i s hp
      rw [hp]
      intro hlive hclear
      have hn := ReferencePostInvocationPrefixLocality.continuingBefore_spec
        rate rewards C_star C_h q ⟨_, hlive⟩
      have he := Option.some.inj (ha.2.1.symm.trans hn)
      have h := ha.2.2.2.2.2.1 hlive
      rw [he] at h
      exact h hclear

include htq in
/-- Actual old COLLECTION payload/segment, canonical rates, and all-arm
factor-two envelope on BOTH generated lifts. Logical `U` remains arbitrary;
it is never identified with the retained physical payload's slow set. -/
theorem branch_collection_alignment (w : Lift) :
    let transition := ReferencePostInvocationPrefixLocality.branchTransition
      rate rewards C_star C_h control0 b u t w
    let z := ReferencePostInvocationNoncallGeometry.insertedPhysicalSource rate transition
    match ReferencePostInvocationNoncallGeometry.postInvocationPrefix rate rewards C_star C_h
      t q.castSucc transition w.1.2 with
    | none => True
    | some _ =>
      ∀ hc : z ∈ ReferencePostInvocationNoncallGeometry.collectionDateDomain rate rewards C_star C_h q,
        let source : ReferencePostInvocationNoncallGeometry.CollectionDateSource rate rewards C_star C_h q := ⟨z, hc⟩
        let P := (ReferencePostInvocationNoncallGeometry.collectionArguments rate rewards C_star C_h q source).1
        let c := ReferencePostInvocationNoncallGeometry.collectionInput rate rewards C_star C_h q source
        let S := ReferencePostInvocationNoncallGeometry.collectionBefore rate rewards C_star C_h q source
        (∃ birth : ReferenceFirstNextInstallationCellFactors.FirstInvocationSource rate rewards C_star C_h t,
          birth.val = z ∧ P = (ReferenceFirstNextInstallationCellFactors.firstSourceCell
            rate rewards C_star C_h t birth).selected.view.payload) ∧
        (∃ (e : ℕ) (seg : ReferenceCollectionSegmentExtraction.Segment rate) (j : Fin seg.records.length),
          ReferenceCollectionSegmentExtraction.segmentAt
            (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h) e = some seg ∧
          e + j.val = q.val - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h ∧
          seg.records[j.val] = ReferencePostInvocationNoncallGeometry.collectionRecord
            rate rewards C_star C_h q source ∧ seg.context.payload = P) ∧
        c.rate = P.rate ∧ P.rate = CanonicalRecordingRates.xi p rate.eta.val P.anchor ∧
        (c.enabled = true → S.overflow = false →
          ∃ (hlo : ∀ j, P.anchor j ≤ RecordedQueueRun.scoreWeight
              (ReferenceFirstLaunchNumericalCell.queueParameters rate) S j)
            (hhi : ∀ j, RecordedQueueRun.scoreWeight
              (ReferenceFirstLaunchNumericalCell.queueParameters rate) S j ≤ 2 * P.anchor j),
            ∀ (U : SlowSet p) (j : CanonicalFastSampling.FastArm U),
              ReferencePostInvocationNoncallGeometry.collectionFastMass rate P.anchor
                (RecordedQueueRun.scoreWeight (ReferenceFirstLaunchNumericalCell.queueParameters rate) S)
                P.anchor_pos (RecordedSlowRefresh.scoreWeight_pos _ _) U j =
              CanonicalFastSampling.qGamma p rate.eta.val rate.eta.property rate.sourceCap P.anchor
                (RecordedQueueRun.scoreWeight (ReferenceFirstLaunchNumericalCell.queueParameters rate) S)
                P.anchor_pos (RecordedSlowRefresh.scoreWeight_pos _ _) hlo hhi U j) := by
  cases b
  all_goals
    first
    | have ha := ReferencePostInvocationGeneratedAlignment.nonrenewed_generated_alignment
        rate rewards C_star C_h control0 u t q htq w
    | have ha := ReferencePostInvocationGeneratedAlignment.renewed_generated_alignment
        rate rewards C_star C_h control0 u t q htq w
    dsimp only [ReferencePostInvocationPrefixLocality.branchTransition] at ha ⊢
    split at ha
    · simp_all only
    · rename_i s hp
      rw [hp]
      intro hc
      have hn := ReferencePostInvocationPrefixLocality.collectionBefore_spec
        rate rewards C_star C_h q ⟨_, hc⟩
      have he := Option.some.inj (ha.2.1.symm.trans hn)
      have h := ha.2.2.2.2.2.2 hc
      rw [he] at h
      have hr := ReferencePostInvocationGeneratedAlignment.collectionInput_parameters
        rate rewards C_star C_h q ⟨_, hc⟩
      refine ⟨?_, h.2.1, hr.1, hr.2.1, ?_⟩
      · first
        | exact ⟨ReferenceFirstNextInstallationCellFactors.nonrenewedFirstSource
            rate rewards C_star C_h t u w.1.1 w.2, rfl, h.1⟩
        | exact ⟨ReferenceFirstNextInstallationCellFactors.renewedFirstSource
            rate rewards C_star C_h t u
              (ReferenceFirstCollectionRenewalInstallationCoupling.pair rate rewards C_star C_h u t w).2,
            rfl, h.1⟩
      · intro hen hclear
        have hg := (ReferencePostInvocationGeneratedAlignment.collectionInput_oldGrid
          rate rewards C_star C_h q ⟨_, hc⟩).2
        rw [hen] at hg
        exact h.2.2 (of_decide_eq_true hg.symm) hclear

variable (i : Fin (M p))

/-- Genuine surviving-event localization of the actual observer image. -/
abbrev SurvivingObserver := {d : SupportedObserver rate rewards C_star C_h control0 b u t q htq i //
  d ∈ observerGate rate rewards C_star C_h control0 b u t q htq i}

/-- The entire old hidden list and incoming seed, without a default value. -/
def incomingPrefix (d : SurvivingObserver rate rewards C_star C_h control0 b u t q htq i) :
    SlowSet p × List (LogicalCell p rate) :=
  (ReferencePostInvocationPrefixLocality.erasedPrefixReadout rate t q i pairLabels d.val.val.val).1.get
    d.property.1

/-- Supported observers supply generated LIVE seed/complement correctness
internally. Only actual LIVE membership and PRE clarity localize the claim. -/
theorem supported_live_alignment
    (d : SurvivingObserver rate rewards C_star C_h control0 b u t q htq i) (ω : Innovation p) :
    let w := restoreSupported rate rewards C_star C_h control0 b u t q htq i (d.val, ω)
    let transition := ReferencePostInvocationPrefixLocality.branchTransition
      rate rewards C_star C_h control0 b u t w
    let z := ReferencePostInvocationNoncallGeometry.insertedPhysicalSource rate transition
    ∀ hlive : z ∈ ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualDomain
        rate rewards C_star C_h q,
      let live := ReferencePostInvocationNoncallGeometry.continuingSourceCell
        rate rewards C_star C_h q ⟨z, hlive⟩
      let S := ReferencePostInvocationNoncallGeometry.continuingBefore
        rate rewards C_star C_h q ⟨z, hlive⟩
      S.overflow = false →
        (incomingPrefix rate rewards C_star C_h control0 b u t q htq i d).1 =
          live.selected.view.payload.slowSet ∧
        ∀ j : CanonicalFastSampling.FastArm live.selected.view.payload.slowSet,
          live.selected.view.complementWeights j =
            RecordedQueueRun.scoreWeight (ReferenceFirstLaunchNumericalCell.queueParameters rate) S j.val := by
  dsimp only
  have hp := congrArg Prod.fst
    (supported_prefix_readout rate rewards C_star C_h control0 b u t q htq i d.val ω)
  dsimp only [Prod.fst] at hp
  have hs := hp.symm.trans (Option.some_get d.property.1).symm
  have ha := branch_live_alignment rate rewards C_star C_h control0 b u t q htq
    (restoreSupported rate rewards C_star C_h control0 b u t q htq i (d.val, ω))
  dsimp only at ha
  rw [hs] at ha
  exact ha

end GeneratedAlignment

section FiniteOutcome

open ReferenceFirstLiveChronologicalPrefixFoundation
open ReferenceFirstLiveChronologicalPrefixMeasurability

/-- Literal finite output: absent cell, or effective marker/FAST/proposal/next
set. The physical source and numerical update remain in the joint readout. -/
def Outcome (p : ConstructorDimensions.Parameters) : Type :=
  Unit ⊕ (Option (Fin p.K) × Fin p.K × Bool × SlowSet p)

instance outcomeFintype : Fintype (Outcome p) :=
  inferInstanceAs (Fintype (Unit ⊕ (Option (Fin p.K) × Fin p.K × Bool × SlowSet p)))

instance outcomeMeasurableSpace : MeasurableSpace (Outcome p) := ⊤
instance outcomeDiscrete : DiscreteMeasurableSpace (Outcome p) := ⟨fun _ => trivial⟩

def cellOutcome (e : LogicalCell p rate) : Outcome p :=
  Sum.inr (if e.before.overflow then none else e.numerical.2.1,
    e.fastArm, e.proposal, e.nextSlowSet)

theorem measurable_cellOutcome : Measurable (cellOutcome rate) := by
  let read : LogicalCell p rate → Bool × Option (Fin p.K) × Fin p.K × Bool × SlowSet p :=
    fun e => (e.before.overflow, e.numerical.2.1, e.fastArm, e.proposal, e.nextSlowSet)
  have hr : Measurable read :=
    ((measurable_of_countable (fun S : RecordedQueueRun.RunState p.K => S.overflow)).comp
      measurable_logicalCell_before).prodMk
      (measurable_logicalCell_numerical.snd.fst.prodMk
        (measurable_logicalCell_fastArm.prodMk
          (measurable_logicalCell_proposal.prodMk measurable_logicalCell_nextSlowSet)))
  let collapse : Bool × Option (Fin p.K) × Fin p.K × Bool × SlowSet p → Outcome p :=
    fun x => Sum.inr (if x.1 then none else x.2.1, x.2.2)
  have hc : Measurable collapse := measurable_of_finite _
  exact hc.comp hr

def optionalOutcome (e : Option (LogicalCell p rate)) : Outcome p :=
  match e with
  | none => Sum.inl ()
  | some e => cellOutcome rate e

theorem measurable_optionalOutcome : Measurable (optionalOutcome rate) := by
  let f : LogicalCell p rate ⊕ PUnit → Outcome p :=
    Sum.elim (cellOutcome rate) (fun _ => Sum.inl ())
  have hf : Measurable f := (measurable_cellOutcome rate).sumElim measurable_const
  convert hf.comp (comap_measurable (Equiv.optionEquivSumPUnit.{0, 0} (LogicalCell p rate))) using 1
  funext o
  cases o <;> rfl

private theorem measurable_option_cases {X H Y : Type*}
    [MeasurableSpace X] [MeasurableSpace H] [MeasurableSpace Y]
    (o : X → Option H) (ho : Measurable o) (f : X → Y) (hf : Measurable f)
    (g : X × H → Y) (hg : Measurable g) :
    Measurable (fun x => match o x with | none => f x | some h => g (x, h)) := by
  have hs := hg.sumElim (hf.comp (measurable_fst : Measurable (Prod.fst : X × PUnit → X)))
  have he := (MeasurableEquiv.prodSumDistrib X H PUnit).measurable.comp
    (measurable_id.prodMk ((comap_measurable (Equiv.optionEquivSumPUnit H)).comp ho))
  convert hs.comp he using 1
  funext x
  cases h : o x <;> simp only [Function.comp_apply, id_eq, h] <;> rfl

/-- The actual optional noncall cell at `q`, using the full generated incoming
set. No cell is fabricated after an already killed prefix. -/
def currentCell (w : Lift) : Option (LogicalCell p rate) :=
  let transition := ReferencePostInvocationPrefixLocality.branchTransition
    rate rewards C_star C_h control0 b u t w
  (ReferencePostInvocationNoncallGeometry.postInvocationPrefix rate rewards C_star C_h
    t q.castSucc transition w.1.2).bind fun s =>
      ReferencePostInvocationNoncallGeometry.noncallDateCell rate rewards C_star C_h q
        (ReferencePostInvocationNoncallGeometry.insertedPhysicalSource rate transition) w.1.2 s.1

theorem measurable_currentCell :
    Measurable (currentCell rate rewards C_star C_h control0 b u t q) := by
  let observation := ReferencePostInvocationPrefixLocality.branchObservation
    rate rewards C_star C_h control0 b u t q.castSucc
  let pastCells := fun w : Lift => (observation w).2.2.2
  have hO := ReferencePostInvocationPrefixLocality.measurable_branchObservation
    rate rewards C_star C_h control0 b u t q.castSucc
  have hp : Measurable pastCells := hO.snd.snd.snd
  have hz : Measurable (fun w : Lift => (observation w).1.1.1.2) := hO.fst.fst.fst.snd
  let args : (Lift × (SlowSet p × List (LogicalCell p rate))) →
      SlowSet p × (BootstrapPrivateRoundStreams.SourceInput p × Auxiliary p) :=
    fun ws => (ws.2.1, ((observation ws.1).1.1.1.2, ws.1.1.2))
  have hargs : Measurable args := measurable_snd.fst.prodMk
    ((hz.comp measurable_fst).prodMk measurable_fst.fst.snd)
  have hg := (ReferencePostInvocationPrefixLocality.measurable_noncallDateCell
    rate rewards C_star C_h control0 q).comp hargs
  convert measurable_option_cases pastCells hp
    (fun _ => (none : Option (LogicalCell p rate))) measurable_const _ hg using 1
  funext w
  cases b
  all_goals
    change (pastCells w).bind _ = _
    cases pastCells w <;> rfl

/-- The actual finite outcome on the erased supported fibre, using precisely
the SAME whole control and pair in the original and inserted full sources. -/
def outcomeOnSupported (i : Fin (M p))
    (x : SupportedObserver rate rewards C_star C_h control0 b u t q htq i × Innovation p) : Outcome p :=
  optionalOutcome rate (currentCell rate rewards C_star C_h control0 b u t q
    (restoreSupported rate rewards C_star C_h control0 b u t q htq i x))

theorem measurable_outcomeOnSupported (i : Fin (M p)) :
    Measurable (outcomeOnSupported rate rewards C_star C_h control0 b u t q htq i) :=
  (measurable_optionalOutcome rate).comp
    ((measurable_currentCell rate rewards C_star C_h control0 b u t q).comp
      (measurable_restoreSupported rate rewards C_star C_h control0 b u t q htq i))

/-- The incoming seed used by the actual finite outcome is the entire
supported stored prefix, recovered internally from the actual source. -/
theorem outcomeOnSupported_readout (i : Fin (M p))
    (d : SupportedObserver rate rewards C_star C_h control0 b u t q htq i) (ω : Innovation p) :
    let w := restoreSupported rate rewards C_star C_h control0 b u t q htq i (d, ω)
    let transition := ReferencePostInvocationPrefixLocality.branchTransition
      rate rewards C_star C_h control0 b u t w
    outcomeOnSupported rate rewards C_star C_h control0 b u t q htq i (d, ω) =
      optionalOutcome rate ((ReferencePostInvocationPrefixLocality.erasedPrefixReadout
        rate t q i pairLabels d.val.val).1.bind fun s =>
          ReferencePostInvocationNoncallGeometry.noncallDateCell rate rewards C_star C_h q
            (ReferencePostInvocationNoncallGeometry.insertedPhysicalSource rate transition) w.1.2 s.1) := by
  dsimp only
  have hp := congrArg Prod.fst
    (supported_prefix_readout rate rewards C_star C_h control0 b u t q htq i d ω)
  dsimp only [Prod.fst] at hp
  dsimp only [outcomeOnSupported]
  unfold currentCell
  dsimp only
  rw [← hp]

end FiniteOutcome

end LiteralLifts

end Bandits.Support.ReferencePostInvocationSupportedDisintegration
