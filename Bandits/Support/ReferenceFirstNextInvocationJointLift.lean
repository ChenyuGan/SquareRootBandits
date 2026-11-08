/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionLogicalPrefixExtension

import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Tactic

/-!
# Joint full-vector insertion at the next invocation

The nonrenewed first subsequent collection call retains the literal generated
logical prefix, original source coordinates, and the same sampled endpoint
path while replacing only the complete current assignment vector.

Sources: ZIP4 `06_interruptions.tex:376-426`,
`04_slow_fast_learner.tex:142-215,323-390`, and
`08_main_theorem.tex:78-109`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped Classical ENNReal
open Bandits.Support
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ContinuousControlSlice
open Bandits.Support.ReferenceFirstCollectionLogicalPrefixExtension
open Bandits.Support.ReferenceFirstLiveCollectionPathJoin
open Bandits.Support.ReferenceSourcePrefixHistoryFiltration
open Bandits.Support.ReferenceCalendarLaterSamplerPredictability
open Bandits.Support.ReferenceFirstCollectionRenewalVectorInsertion
open Bandits.Support.AssignmentParameterFibreKernel
open Bandits.Support.ReferenceActualCollectionNonrenewedEndpointFibreJoin
open Bandits.Support.LaunchAssignmentCoordinateSplit (controlAssignmentSplitEquiv)
open Bandits.Support.ReferenceFirstLiveCalendarMarkedTransition (labelZero)

namespace Bandits.Support.ReferenceFirstNextInvocationJointLift

variable {p : ConstructorDimensions.Parameters}

local instance sourceMeasurableSpace : MeasurableSpace (BootstrapPrivateRoundStreams.SourceInput p) := by
  change MeasurableSpace (CompletePublicTable.PublishedOutput p ×
    BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

local instance outcomeMeasurableSpace : MeasurableSpace (Outcome p) := ⊤
local instance outcomeDiscreteMeasurableSpace : DiscreteMeasurableSpace (Outcome p) := ⟨fun _ => trivial⟩
local instance outcomeFintype : Fintype (Outcome p) := inferInstance
local instance outcomeCountable : Countable (Outcome p) := inferInstance
local instance outcomeSingletons : MeasurableSingletonClass (Outcome p) := inferInstance
local instance slowSetFintype : Fintype (SlowSet p) := inferInstance
local instance slowSetCountable : Countable (SlowSet p) := inferInstance

variable (rate : ReferenceActivePhysicalStep.RateInput p)
variable (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
variable (C_star C_h : ℝ) (u t : Fin p.T)

abbrev EventSource :=
  ReferenceFirstLiveCollectionPathJoin.EventSource rate rewards C_star C_h u t

local notation "event" =>
  ReferenceFirstLiveCollectionPathJoin.firstLiveCollectionEvent rate rewards C_star C_h u t
local notation "obs" => ReferenceFirstCollectionLogicalPrefixExtension.extendedObservation
  rate rewards C_star C_h
local notation "past" => ReferenceFirstCollectionLogicalPrefixExtension.extendedPast
  rate rewards C_star C_h
local notation "path" => ReferenceFirstLiveCollectionPathJoin.collectionPath
  rate rewards C_star C_h u t
public def insertedSource (z : BootstrapPrivateRoundStreams.SourceInput p)
    (v : AssignmentParameterFibreKernel.AssignmentVector p) :
    BootstrapPrivateRoundStreams.SourceInput p :=
  ReferenceFirstCollectionRenewalVectorInsertion.insert t z v

/-- The retained prefix, whole label-zero array, generated complete old cell
list, and the original hidden collection path at the next invocation. -/
public def nextInvocationObservation (control0 : ContinuousLearningRows.TimeControl p)
    (w : EventSource rate rewards C_star C_h u t ×
      ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p) :
    ReferenceFirstCollectionLogicalPrefixExtension.Observation rate ×
      ReferenceFirstLiveCollectionPathJoin.Path u t :=
  (obs control0 t.castSucc (w.1.val, w.2), path w.1 w.2)

/-- The event restriction on the original source remains unnormalized. -/
public def eventSourceLaw : Measure (EventSource rate rewards C_star C_h u t) :=
  ReferenceFirstLiveCollectionPathJoin.eventSourceLaw rate rewards C_star C_h u t

public instance eventSourceLaw_finite : IsFiniteMeasure (eventSourceLaw rate rewards C_star C_h u t) := by
  unfold eventSourceLaw ReferenceFirstLiveCollectionPathJoin.eventSourceLaw
  infer_instance

/-- The subtype product law maps back to the literal unnormalized restriction
of the original source and private array law. -/
public theorem eventProductLaw_map :
    ((eventSourceLaw rate rewards C_star C_h u t).prod
        (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p)).map
      (Prod.map (Subtype.val : EventSource rate rewards C_star C_h u t →
        BootstrapPrivateRoundStreams.SourceInput p) id) =
    ((BootstrapPrivateRoundStreams.sourceInputLaw p).prod
        (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p)).restrict
      (event ×ˢ Set.univ) := by
  exact ReferenceFirstLiveCollectionPathJoin.eventProductLaw_map rate rewards C_star C_h u t

/-- The complete observation and generated path are jointly Borel. -/
public theorem measurable_nextInvocationObservation
    (control0 : ContinuousLearningRows.TimeControl p) :
    Measurable (nextInvocationObservation rate rewards C_star C_h u t control0) := by
  have hsource : Measurable
      (fun w : EventSource rate rewards C_star C_h u t ×
          ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p =>
        (w.1.val, w.2)) :=
    (measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd
  exact
    ((ReferenceFirstCollectionLogicalPrefixExtension.measurable_extendedObservation
      rate rewards C_star C_h control0 t.castSucc).comp hsource).prodMk
      (ReferenceFirstLiveCollectionPathJoin.measurable_collectionPath
        rate rewards C_star C_h u t)

/-- The whole-vector insertion preserves the source prefix, whole label-zero
array, and generated complete old logical-cell list. -/
public theorem nextInvocationPrefix_insertVector
    (control0 : ContinuousLearningRows.TimeControl p)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (a : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p)
    (v : AssignmentParameterFibreKernel.AssignmentVector p) :
    ReferenceFirstCollectionLogicalPrefixExtension.extendedObservation rate rewards C_star C_h
      control0 t.castSucc (insertedSource t z v, a) =
    ReferenceFirstCollectionLogicalPrefixExtension.extendedObservation rate rewards C_star C_h
      control0 t.castSucc (z, a) := by
  let c := ReferenceFirstCollectionRenewalVectorInsertion.ctrl t z v
  have hsource : insertedSource t z v =
      ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z c := rfl
  have hpast := ReferenceFirstCollectionLogicalPrefixExtension.extendedPrefixStateAux_replace_current
    rate rewards C_star C_h control0 t.val (Nat.le_of_lt t.isLt) t le_rfl z a c
  have hprefix := ReferenceFirstCollectionOriginalSourceFibreTransport.sourcePrefix_replaceSourceControl
    control0 t z c
  change (sourcePrefix control0 t.val (insertedSource t z v),
      (labelZero a, extendedPast rate rewards C_star C_h t.castSucc (insertedSource t z v, a))) =
    (sourcePrefix control0 t.val z,
      (labelZero a, extendedPast rate rewards C_star C_h t.castSucc (z, a)))
  apply Prod.ext
  · exact (congrArg (sourcePrefix control0 t.val) hsource).trans hprefix
  · apply Prod.ext
    · rfl
    · dsimp only [ReferenceFirstCollectionLogicalPrefixExtension.extendedPast]
      exact congrArg Prod.snd hpast

/-- The original source prefix is jointly independent of the complete current
assignment vector and its unchanged non-assignment remainder. This is derived
from the accepted current-control product law and the measure-preserving
whole-control split. -/
public theorem sourcePrefix_currentVector_remainder_product
    (control0 : ContinuousLearningRows.TimeControl p) :
    (BootstrapPrivateRoundStreams.sourceInputLaw p).map
        (fun z =>
          (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z,
            controlAssignmentSplitEquiv p
              (ReferenceSourceCurrentControlFreshness.u_t p t z))) =
      ((BootstrapPrivateRoundStreams.sourceInputLaw p).map
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val)).prod
        ((ContinuousControlSlice.assignmentLaw p.K).prod
          ((LaunchAssignmentCoordinateSplit.nonAssignmentScalarLaw p).prod
            (ContinuousLearningRows.affineSamplesLaw p))) := by
  let μ := BootstrapPrivateRoundStreams.sourceInputLaw p
  let μprefix := μ.map (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val)
  let μcontrol := ContinuousLearningRows.timeControlLaw p
  let f := fun z : BootstrapPrivateRoundStreams.SourceInput p =>
    (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z,
      ReferenceSourceCurrentControlFreshness.u_t p t z)
  have hf : Measurable f :=
    (ReferenceSourcePrefixHistoryFiltration.measurable_sourcePrefix control0 t.val).prodMk
      (ReferenceSourceCurrentControlFreshness.measurable_u_t t)
  have hsource : MeasurePreserving f μ (μprefix.prod μcontrol) := by
    exact ⟨hf,
      ReferenceFirstLiveCalendarMarkedTransition.sourcePrefix_currentControl_product control0 t⟩
  have hsplit :=
    LaunchAssignmentCoordinateSplit.measurePreserving_controlAssignmentSplitEquiv p
  have hsplitProduct : MeasurePreserving
      (fun x : _ × ContinuousLearningRows.TimeControl p =>
        (x.1, controlAssignmentSplitEquiv p x.2))
      (μprefix.prod μcontrol)
      (μprefix.prod ((ContinuousControlSlice.assignmentLaw p.K).prod
        ((LaunchAssignmentCoordinateSplit.nonAssignmentScalarLaw p).prod
          (ContinuousLearningRows.affineSamplesLaw p)))) :=
    (MeasurePreserving.id μprefix).prod hsplit
  have htotal : MeasurePreserving
      (fun z =>
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z,
          controlAssignmentSplitEquiv p
            (ReferenceSourceCurrentControlFreshness.u_t p t z)))
      μ
      (μprefix.prod ((ContinuousControlSlice.assignmentLaw p.K).prod
        ((LaunchAssignmentCoordinateSplit.nonAssignmentScalarLaw p).prod
          (ContinuousLearningRows.affineSamplesLaw p)))) := by
    exact hsplitProduct.comp hsource
  exact htotal.map_eq

/-- Insertion retains the original selected-row remainder and every private
coordinate, including the selector `J`. -/
public theorem insertedVector_preserves_remainder_and_private
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (v : AssignmentParameterFibreKernel.AssignmentVector p) :
    (controlAssignmentSplitEquiv p)
        (ReferenceFirstCollectionRenewalVectorInsertion.c t (insertedSource t z v)) =
      (v, ((controlAssignmentSplitEquiv p)
        (ReferenceFirstCollectionRenewalVectorInsertion.c t z)).2) ∧
    (insertedSource t z v).1.1 = z.1.1 ∧
    (insertedSource t z v).2 = z.2 := by
  refine ⟨?_, ?_, ?_⟩
  · change (controlAssignmentSplitEquiv p)
      (ReferenceFirstCollectionRenewalVectorInsertion.c t (insert t z v)) = _
    rw [ReferenceFirstCollectionRenewalVectorInsertion.currentControl_insert]
    exact ReferenceFirstCollectionRenewalVectorInsertion.controlAssignmentSplit_ctrl t z v
  · exact (ReferenceFirstCollectionRenewalVectorInsertion.insert_identity_private_selector t z v).1
  · exact (ReferenceFirstCollectionRenewalVectorInsertion.insert_identity_private_selector t z v).2.1

/-- The actual sampler parameter read from the retained strict-prefix field
is the one consumed at the source's actual next call. -/
public theorem nextInvocationParameter_eq_actual
    (control0 : ContinuousLearningRows.TimeControl p)
    (w : EventSource rate rewards C_star C_h u t ×
      ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p) :
    calendarParameters rate rewards C_star C_h t
        (nextInvocationObservation rate rewards C_star C_h u t control0 w).1.1 =
      (ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h t w.1.val).map Prod.snd := by
  change calendarParameters rate rewards C_star C_h t
      (sourcePrefix control0 t.val w.1.val) = _
  rw [← ReferenceCalendarLaterSamplerPredictability.calendarParameters_factor
    rate rewards C_star C_h control0 t w.1.val]
  obtain ⟨_hactualCell, hcall, _hclear⟩ :=
    ReferenceFirstLiveCollectionPathJoin.firstLiveCollectionEvent_facts
      rate rewards C_star C_h u t w.1.val w.1.property
  obtain ⟨record, cutoff, theta, hrecord, hcallAt, payload, ledger, proposal,
      hstate, hcutoff, hparams, hlater, hcorrected⟩ :=
    ReferenceActualCollectionNonrenewedEndpointFibreJoin.actualNonrenewedCollectionCall_selector
      rate rewards C_star C_h t w.1.val hcall
  unfold calendarParameters
  rw [hrecord, Option.bind_some, hparams, hcallAt]
  rfl

/-- The event supplies an actual endpoint fibre, including zero-mass slow-set
atoms and the `none` outcome. -/
public theorem nonrenewedEndpointFibre
    (z : EventSource rate rewards C_star C_h u t) :
    ∃ (e b : ℕ) (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (cutoff : Fin p.T) (theta : AssignmentParameterFibreKernel.Theta p)
      (actualCall : ReferenceLaterSamplerParameterMeasurability.ActualSamplerCall
        (p := p) (rate := rate))
      (hcell : z.val ∈ ReferenceActualCollectionHiddenRefreshPath.collectionPrefixCell
        rate rewards C_star C_h e b),
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z.val =
          some record ∧
      ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h t z.val =
          some (cutoff, theta) ∧
      ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h + b = t.val ∧
      actualCall.val = record.input ∧
      ReferenceLaterSamplerParameterMeasurability.actualParameter actualCall = theta ∧
      AssignmentParameterFibreKernel.fibreMass p theta none = 0 ∧
      ∀ U : AssignmentParameterFibreKernel.SlowSet p,
        (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p)
            {array : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p |
              ReferenceActualCollectionHiddenRefreshPath.sampledArrayPath
                rate rewards C_star C_h e b z.val hcell (b - e) (by omega) array
                  (Fin.last (b - e)) = U} =
          AssignmentParameterFibreKernel.fibreMass p theta (some U) := by
  obtain ⟨hactualCell, hcall, hclear⟩ :=
    ReferenceFirstLiveCollectionPathJoin.firstLiveCollectionEvent_facts
      rate rewards C_star C_h u t z.val z.property
  obtain ⟨e, b, record, cutoff, theta, actualCall, hcell, hrecord, hcallAt,
      hdate, hinput, hparameter, _hweight, _hanchor, _hsampler, hnone, hfibre⟩ :=
    ReferenceActualCollectionNonrenewedEndpointFibreJoin.actualNonrenewedCollectionCall_endpoint_fibre
      rate rewards C_star C_h t z.val hcall hclear
  exact ⟨e, b, record, cutoff, theta, actualCall, hcell, hrecord, hcallAt,
    hdate, hinput, hparameter, hnone, fun U => (hfibre U).1⟩

/-- The parameter read from the literal retained observation is the actual
parameter supplied to the present nonrenewed sampler call. -/
public theorem nextInvocationSamplerParameter
    (control0 : ContinuousLearningRows.TimeControl p)
    (w : EventSource rate rewards C_star C_h u t ×
      ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p) :
    ∃ (theta : AssignmentParameterFibreKernel.Theta p)
      (actualCall : ReferenceLaterSamplerParameterMeasurability.ActualSamplerCall
        (p := p) (rate := rate)),
      ReferenceLaterSamplerParameterMeasurability.actualParameter actualCall = theta ∧
      calendarParameters rate rewards C_star C_h t
        (nextInvocationObservation rate rewards C_star C_h u t control0 w).1.1 = some theta := by
  obtain ⟨_e, _b, _record, _cutoff, theta, actualCall, _hcell, _hrecord,
      hcallAt, _hdate, _hinput, hparameter, _hnone, _hfibre⟩ :=
    nonrenewedEndpointFibre rate rewards C_star C_h u t w.1
  refine ⟨theta, actualCall, hparameter, ?_⟩
  rw [nextInvocationParameter_eq_actual rate rewards C_star C_h u t control0 w, hcallAt]
  rfl

/-- Insert into the same literal nonrenewed-event subtype. -/
public def insertEvent (z : EventSource rate rewards C_star C_h u t)
    (v : AssignmentVector p) : EventSource rate rewards C_star C_h u t :=
  ⟨insertedSource t z.val v,
    (firstLiveCollectionEvent_replace_current_iff rate rewards C_star C_h u t
      z.val (ctrl t z.val v)).mp z.property⟩

public theorem measurable_insertEvent :
    Measurable (fun zv : EventSource rate rewards C_star C_h u t × AssignmentVector p =>
      insertEvent rate rewards C_star C_h u t zv.1 zv.2) := by
  exact ((ReferenceFirstCollectionRenewalVectorInsertion.measurable_insert (t := t)).comp
    ((measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd)).subtype_mk

/-- Every point of the retained path is the incoming set generated at that
same boundary in the complete old logical recursion. -/
public theorem generatedIncoming_eq_path
    (z : EventSource rate rewards C_star C_h u t)
    (a : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p)
    (i : Fin (t.val - u.val + 1)) :
    (extendedPrefixStateAux rate rewards C_star C_h (u.val + i.val)
      (by have hd := firstLiveCollectionEvent_dates rate rewards C_star C_h u t z.val z.property
          have hi := i.isLt; omega) (z.val, a)).1 =
      some (path z a i) := by
  obtain ⟨K, hU, _hL, _hlen, _hmap⟩ := generated_collectionPath_prefix
    rate rewards C_star C_h u t z a i.val (by have hi := i.isLt; omega)
  exact hU

/-- Current-vector insertion preserves the SAME whole sampled path, proved
from actual generated-prefix locality at each boundary. -/
public theorem collectionPath_insertVector
    (control0 : ContinuousLearningRows.TimeControl p)
    (z : EventSource rate rewards C_star C_h u t)
    (a : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p)
    (v : AssignmentVector p) :
    path (insertEvent rate rewards C_star C_h u t z v) a = path z a := by
  funext i
  have hleft := generatedIncoming_eq_path rate rewards C_star C_h u t
    (insertEvent rate rewards C_star C_h u t z v) a i
  have hright := generatedIncoming_eq_path rate rewards C_star C_h u t z a i
  have hd := firstLiveCollectionEvent_dates rate rewards C_star C_h u t z.val z.property
  have hi := i.isLt
  have hlocal := extendedPrefixStateAux_replace_current rate rewards C_star C_h control0
    (u.val + i.val) (by have ht := t.isLt; omega) t (by omega)
    z.val a (ctrl t z.val v)
  exact Option.some.inj (hleft.symm.trans ((congrArg Prod.fst hlocal).trans hright))

/-- The complete retained observation, including all old cells and the SAME
hidden path, survives insertion pointwise. -/
public theorem nextInvocationObservation_insertVector
    (control0 : ContinuousLearningRows.TimeControl p)
    (z : EventSource rate rewards C_star C_h u t)
    (a : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p)
    (v : AssignmentVector p) :
    nextInvocationObservation rate rewards C_star C_h u t control0
      (insertEvent rate rewards C_star C_h u t z v, a) =
    nextInvocationObservation rate rewards C_star C_h u t control0 (z, a) :=
  Prod.ext (nextInvocationPrefix_insertVector rate rewards C_star C_h t control0 z.val a v)
    (collectionPath_insertVector rate rewards C_star C_h u t control0 z a v)

/-- In particular the incoming endpoint of the generated complete old list
is exactly the original path endpoint, before the new call is consumed. -/
public theorem generatedEndpoint_eq_path
    (z : EventSource rate rewards C_star C_h u t)
    (a : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p) :
    (extendedPrefixStateAux rate rewards C_star C_h t.val (Nat.le_of_lt t.isLt)
      (z.val, a)).1 = some (path z a (Fin.last (t.val - u.val))) := by
  have hd := firstLiveCollectionEvent_dates rate rewards C_star C_h u t z.val z.property
  simpa only [Fin.val_last, Nat.add_sub_of_le hd.2.1.le] using
    generatedIncoming_eq_path rate rewards C_star C_h u t z a (Fin.last (t.val - u.val))

public theorem nextParameter_isSome (control0 : ContinuousLearningRows.TimeControl p)
    (z : EventSource rate rewards C_star C_h u t) :
    (calendarParameters rate rewards C_star C_h t (sourcePrefix control0 t.val z.val)).isSome := by
  obtain ⟨theta, call, hcall, htheta⟩ := nextInvocationSamplerParameter
    rate rewards C_star C_h u t control0
      (z, ReferenceFirstLiveActualRefreshTestLaw.auxiliarySection)
  change calendarParameters rate rewards C_star C_h t
    (sourcePrefix control0 t.val z.val) = some theta at htheta
  rw [htheta]
  rfl

/-- Extract the actual present parameter on the literal event, with no
off-event default or extra law premise. -/
public def nextParameter (control0 : ContinuousLearningRows.TimeControl p)
    (z : EventSource rate rewards C_star C_h u t) : Theta p :=
  (calendarParameters rate rewards C_star C_h t (sourcePrefix control0 t.val z.val)).get
    (nextParameter_isSome rate rewards C_star C_h u t control0 z)

public theorem nextParameter_spec (control0 : ContinuousLearningRows.TimeControl p)
    (z : EventSource rate rewards C_star C_h u t) :
    calendarParameters rate rewards C_star C_h t (sourcePrefix control0 t.val z.val) =
      some (nextParameter rate rewards C_star C_h u t control0 z) :=
  (Option.some_get _).symm

private theorem measurableSet_some_image {A : Type*} [MeasurableSpace A]
    (s : Set A) (hs : MeasurableSet s) :
    MeasurableSet[LaterAssignmentStartMeasurability.optionMeasurableSpace]
      (some '' s : Set (Option A)) := by
  change MeasurableSet[(inferInstance : MeasurableSpace (A ⊕ PUnit)).comap
    (Equiv.optionEquivSumPUnit A)] (some '' s)
  rw [MeasurableSpace.measurableSet_comap]
  refine ⟨Sum.inl '' s, measurableSet_inl_image.mpr hs, ?_⟩
  ext value
  cases value <;> simp

public theorem measurable_nextParameter (control0 : ContinuousLearningRows.TimeControl p) :
    Measurable (nextParameter rate rewards C_star C_h u t control0) := by
  have hm := (calendarParameters_measurable rate rewards C_star C_h control0 t).mono
    ((sourcePrefixFiltration control0).le (t.val + 1)) le_rfl
  have hfactor : Measurable (fun z : EventSource rate rewards C_star C_h u t =>
      calendarParameters rate rewards C_star C_h t (sourcePrefix control0 t.val z.val)) := by
    exact hm.comp ((measurable_sourcePrefix control0 t.val).comp measurable_subtype_coe)
  intro s hs
  convert hfactor (measurableSet_some_image s hs) using 1
  ext z
  change nextParameter rate rewards C_star C_h u t control0 z ∈ s ↔
    calendarParameters rate rewards C_star C_h t (sourcePrefix control0 t.val z.val) ∈ some '' s
  rw [nextParameter_spec]
  simp

/-- The base measure retains the entire original source and auxiliary array;
its event mass is never divided out. -/
public def nonrenewedBaseLaw : Measure
    (EventSource rate rewards C_star C_h u t × ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p) :=
  (eventSourceLaw rate rewards C_star C_h u t).prod
    (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p)

public instance nonrenewedBaseLaw_finite :
    IsFiniteMeasure (nonrenewedBaseLaw rate rewards C_star C_h u t) := by
  unfold nonrenewedBaseLaw eventSourceLaw ReferenceFirstLiveCollectionPathJoin.eventSourceLaw
  infer_instance

/-- The existing full-vector fibre kernel at the actual parameter and the
SAME generated endpoint. Dependence on the hidden path is retained. -/
public def nonrenewedVectorKernel (control0 : ContinuousLearningRows.TimeControl p) :
    ProbabilityTheory.Kernel
      (EventSource rate rewards C_star C_h u t × ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p)
      (AssignmentVector p) :=
  (assignmentParameterFibreKernel p).comap
    (fun w => (nextParameter rate rewards C_star C_h u t control0 w.1,
      some (path w.1 w.2 (Fin.last (t.val - u.val)))))
    (((measurable_nextParameter rate rewards C_star C_h u t control0).comp measurable_fst).prodMk
      ((measurable_of_countable (some : SlowSet p → Outcome p)).comp
        ((measurable_pi_apply (Fin.last (t.val - u.val))).comp (measurable_collectionPath rate rewards C_star C_h u t))))

public instance nonrenewedVectorKernel_markov (control0 : ContinuousLearningRows.TimeControl p) :
    ProbabilityTheory.IsMarkovKernel (nonrenewedVectorKernel rate rewards C_star C_h u t control0) := by
  unfold nonrenewedVectorKernel
  infer_instance

/-- The literal event-restricted measure-kernel composition product. -/
public def nonrenewedLiftLaw (control0 : ContinuousLearningRows.TimeControl p) : Measure
    ((EventSource rate rewards C_star C_h u t × ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p) ×
      AssignmentVector p) :=
  Measure.compProd (nonrenewedBaseLaw rate rewards C_star C_h u t)
    (nonrenewedVectorKernel rate rewards C_star C_h u t control0)

public instance nonrenewedLiftLaw_finite (control0 : ContinuousLearningRows.TimeControl p) :
    IsFiniteMeasure (nonrenewedLiftLaw rate rewards C_star C_h u t control0) := by
  unfold nonrenewedLiftLaw
  infer_instance

public theorem nonrenewedLiftLaw_map_fst (control0 : ContinuousLearningRows.TimeControl p) :
    (nonrenewedLiftLaw rate rewards C_star C_h u t control0).map Prod.fst =
      nonrenewedBaseLaw rate rewards C_star C_h u t :=
  Measure.fst_compProd _ _

private theorem connected_consecutive {rate : ReferenceActivePhysicalStep.RateInput p}
    (L : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (initial final : ReferenceActivePhysicalStep.State p rate)
    (hc : ReferenceActivePhysicalHorizon.Connected initial L final)
    (k : ℕ) (hk : k + 1 < L.length) :
    (L[k + 1]'hk).input.state = (L[k]'(by omega)).output.next := by
  induction L generalizing initial k with
  | nil => simp only [List.length_nil] at hk; omega
  | cons head rest ih =>
      cases k with
      | zero =>
          cases rest with
          | nil => simp only [List.length_cons, List.length_nil] at hk; omega
          | cons next tail => exact hc.2.1
      | succ k =>
          exact ih head.output.next hc.2 k (by simp only [List.length_cons] at hk; omega)

private theorem readout_next_collection_phase
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (cell : RecordedQueueRun.RoundInput p.K)
    (hcell : ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 r = some cell) :
    ReferenceCollectionPhaseHistory.CollectionPhase r.output.next.coordinator := by
  obtain ⟨payload, ledger, started, weights, out, _, hpost, _⟩ :=
    ReferenceLaterCollectionArrivalReadout.laterCollectionReadout_call 0 r cell hcell
  have hp := ReferenceCollectionPhaseHistory.collectionPostChoice_no_installation
    r.output.preparation payload ledger started weights
  rw [← hpost] at hp
  have hn : r.output.next.coordinator = r.coordinatorDiagnostics.configuration := by
    change r.output.next.coordinator = r.output.coordinator.configuration
    rw [r.output_eq]; rfl
  rw [hn]
  exact hp

/-- Any endpoint-fibre prefix cell at this first invocation has the original
first cutoff index. The proof uses the actual connected record list: before
the first cutoff its test is false, and after it collection readouts keep the
next incoming configuration in collection (or dagger). -/
public theorem endpointPrefixCell_index
    (z : EventSource rate rewards C_star C_h u t) (e b : ℕ)
    (hc : z.val ∈ ReferenceActualCollectionHiddenRefreshPath.collectionPrefixCell
      rate rewards C_star C_h e b)
    (hdate : ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h + b = t.val) :
    e = u.val - ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h := by
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z.val rewards C_star C_h
  let start := ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  have hw : w = u.val - start :=
    (firstLiveCollectionEvent_canonicalPrefixCell rate rewards C_star C_h u t z.val z.property).1.symm
  obtain ⟨he, reg, owned, base, hlive, hcut, _hgrid, _hp⟩ :=
    ReferenceActualCollectionHiddenRefreshPath.collectionPrefixCell_live
      rate rewards C_star C_h e b z.val hc
  have heR : e < R.length := he
  change start + b = t.val at hdate
  have heb : e ≤ b := hc.1
  have hd := firstLiveCollectionEvent_dates rate rewards C_star C_h u t z.val z.property
  apply Eq.trans (b := w) _ hw
  by_contra hne
  rcases lt_or_gt_of_ne hne with hbefore | hafter
  · have hpre := (List.takeWhile_prefix
      (fun r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) =>
        !ReferenceCollectionPhaseHistory.cutoffChosen r.input) (l := R)).getElem hbefore
    have hall := List.all_eq_true.mp (List.all_takeWhile
      (l := R) (p := fun r => !ReferenceCollectionPhaseHistory.cutoffChosen r.input))
    have hfalse := hall _ (List.getElem_mem hbefore)
    change (!ReferenceCollectionPhaseHistory.cutoffChosen
      (R.takeWhile (fun r => !ReferenceCollectionPhaseHistory.cutoffChosen r.input))[e].input) = true at hfalse
    rw [hpre] at hfalse
    change ReferenceCollectionPhaseHistory.cutoffChosen R[e].input = true at hcut
    rw [hcut] at hfalse
    cases hfalse
  · let q : Fin p.T := ⟨start + (e - 1), by have ht := t.isLt; omega⟩
    obtain ⟨prev, hprev, hmem⟩ := actualDomain_of_collection_interval rate rewards C_star C_h q z.val
      (by change start + w ≤ start + (e - 1); omega)
      (by
        obtain ⟨theta, n, r, hfirst, _⟩ := firstLiveCollectionEvent_firstCall
          rate rewards C_star C_h u t z.val z.property
        simp only [ReferenceFirstCollectionPrecallCalendarSupport.firstCallBoundary, hfirst]
        dsimp [q]; omega)
    have hlookup : R[e - 1]? = some prev := by
      change (if start ≤ q.val then R[q.val - start]? else none) = some prev at hprev
      simpa only [q, Nat.le_add_right, ite_true, Nat.add_sub_cancel_left] using hprev
    have hprevEq : R[e - 1]'(by omega) = prev :=
      Option.some.inj ((List.getElem?_eq_getElem (by omega)).symm.trans hlookup)
    obtain ⟨cell, hcell⟩ := ReferenceFirstCollectionFastErasure.firstCollection_actual_collectionReadout
      rewards C_star C_h z.val prev hmem
    have hphase := readout_next_collection_phase rate prev cell hcell
    obtain ⟨active, hlaunch⟩ := ReferenceActualCollectionHiddenRefreshPath.collectionPrefixCell_launch
      rate rewards C_star C_h e b z.val hc
    have hchain := ReferenceCompletePhysicalHistory.completeSuffix_connected_on_launch
      rate z.val rewards C_star C_h active hlaunch
    have hnext := connected_consecutive R active _ hchain (e - 1) (by dsimp [R]; omega)
    have heq : e - 1 + 1 = e := by omega
    have hnext' : (R[e]'heR).input.state = prev.output.next := by
      simpa only [heq] using hnext.trans (congrArg (fun r => r.output.next) hprevEq)
    rw [← hnext', hlive] at hphase
    rcases hphase with h | ⟨payload, ledger, saved, h⟩ <;> cases h

/-- The auxiliary endpoint law is the full checked-sampler fibre mass for
this SAME generated path. The absent outcome has zero mass. -/
public theorem collectionPath_endpoint_fibreMass
    (control0 : ContinuousLearningRows.TimeControl p)
    (z : EventSource rate rewards C_star C_h u t) :
    fibreMass p (nextParameter rate rewards C_star C_h u t control0 z) none = 0 ∧
    ∀ U : SlowSet p,
      (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p)
        {a | path z a (Fin.last (t.val - u.val)) = U} =
      fibreMass p (nextParameter rate rewards C_star C_h u t control0 z) (some U) := by
  obtain ⟨e, b, record, cutoff, theta, call, hc, hrecord, hcallAt, hdate,
    hinput, hparameter, hnone, hfibre⟩ := nonrenewedEndpointFibre rate rewards C_star C_h u t z
  have he := endpointPrefixCell_index rate rewards C_star C_h u t z e b hc hdate
  have hb : b = t.val - ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h := by omega
  have htheta : theta = nextParameter rate rewards C_star C_h u t control0 z := by
    have hparam := nextInvocationParameter_eq_actual rate rewards C_star C_h u t control0
      (z, ReferenceFirstLiveActualRefreshTestLaw.auxiliarySection)
    rw [hcallAt] at hparam
    change calendarParameters rate rewards C_star C_h t (sourcePrefix control0 t.val z.val) = some theta at hparam
    exact Option.some.inj (hparam.symm.trans (nextParameter_spec rate rewards C_star C_h u t control0 z))
  subst e
  subst b
  rw [htheta] at hnone hfibre
  refine ⟨hnone, ?_⟩
  intro U
  have hd := firstLiveCollectionEvent_dates rate rewards C_star C_h u t z.val z.property
  have hlength : (t.val - ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h) -
      (u.val - ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h) = t.val - u.val := by omega
  have hcongr : ∀ n m (hn : n ≤ (t.val - ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h) -
      (u.val - ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h))
      (hm : m ≤ (t.val - ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h) -
      (u.val - ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h)), n = m →
      ∀ a : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p,
      ReferenceActualCollectionHiddenRefreshPath.sampledArrayPath rate rewards C_star C_h _ _ z.val hc n hn a (Fin.last n) =
      ReferenceActualCollectionHiddenRefreshPath.sampledArrayPath rate rewards C_star C_h _ _ z.val hc m hm a (Fin.last m) := by
    intro n m hn hm h a
    subst m
    rfl
  have hset : {a | path z a (Fin.last (t.val - u.val)) = U} =
      {a | ReferenceActualCollectionHiddenRefreshPath.sampledArrayPath rate rewards C_star C_h _ _ z.val hc _ le_rfl a
        (Fin.last ((t.val - ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h) -
          (u.val - ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h))) = U} := by
    ext a
    exact Iff.of_eq (congrArg (fun S => S = U) (hcongr _ _ (by omega) le_rfl hlength.symm a))
  rw [hset]
  exact hfibre U

/-- Integrating the existing fibre kernel over the actual auxiliary path
recovers the whole assignment cube on each original source, including null
`none` and null successful fibres. -/
public theorem auxiliary_endpointOutcome_mass
    (control0 : ContinuousLearningRows.TimeControl p)
    (z : EventSource rate rewards C_star C_h u t) (o : Outcome p) :
    ((ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p).map
      (fun a => some (path z a (Fin.last (t.val - u.val))))) {o} =
      fibreMass p (nextParameter rate rewards C_star C_h u t control0 z) o := by
  let theta := nextParameter rate rewards C_star C_h u t control0 z
  let F : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p → Outcome p :=
    fun a => some (path z a (Fin.last (t.val - u.val)))
  have hpath : Measurable (fun a : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p => path z a) := by
    intro S hS
    have hpre := measurable_collectionPath rate rewards C_star C_h u t hS
    exact (show Measurable (fun a : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p => (z, a)) from
      measurable_const.prodMk measurable_id) hpre
  have hend : Measurable (fun a : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p =>
      path z a (Fin.last (t.val - u.val))) := (measurable_pi_apply (Fin.last (t.val - u.val))).comp hpath
  have hF : Measurable F := (measurable_of_countable (some : SlowSet p → Outcome p)).comp hend
  let nu := (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p).map F
  change nu {o} = fibreMass p theta o
  rw [Measure.map_apply hF (measurableSet_singleton o)]
  cases o with
  | none =>
        change _ = fibreMass p (nextParameter rate rewards C_star C_h u t control0 z) none
        rw [(collectionPath_endpoint_fibreMass rate rewards C_star C_h u t control0 z).1]
        change (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p) {a | F a = none} = 0
        simp only [F, reduceCtorEq, Set.ofPred_false, measure_empty]
  | some U =>
        simpa only [F, Set.preimage, Set.mem_singleton_iff, Option.some.injEq] using
          (collectionPath_endpoint_fibreMass rate rewards C_star C_h u t control0 z).2 U

public theorem auxiliary_average_vectorKernel
    (control0 : ContinuousLearningRows.TimeControl p)
    (z : EventSource rate rewards C_star C_h u t)
    (B : Set (AssignmentVector p)) (_hB : MeasurableSet B) :
    (∫⁻ a, nonrenewedVectorKernel rate rewards C_star C_h u t control0 (z, a) B
      ∂ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p) = assignmentLaw p.K B := by
  let theta := nextParameter rate rewards C_star C_h u t control0 z
  let F : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p → Outcome p :=
    fun a => some (path z a (Fin.last (t.val - u.val)))
  have hpath : Measurable (fun a : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p => path z a) := by
    intro S hS
    have hpre := measurable_collectionPath rate rewards C_star C_h u t hS
    exact (show Measurable (fun a : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p => (z, a)) from
      measurable_const.prodMk measurable_id) hpre
  have hend : Measurable (fun a : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p =>
      path z a (Fin.last (t.val - u.val))) := (measurable_pi_apply (Fin.last (t.val - u.val))).comp hpath
  have hF : Measurable F := (measurable_of_countable (some : SlowSet p → Outcome p)).comp hend
  let nu := (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p).map F
  have hmass (o : Outcome p) : nu {o} = fibreMass p theta o :=
    auxiliary_endpointOutcome_mass rate rewards C_star C_h u t control0 z o
  have hsum := congrArg (fun mu : Measure (AssignmentVector p) => mu B)
    (sum_fibreMass_smul_fibreMeasure p theta)
  calc
    _ = ∫⁻ a, fibreMeasure p theta (F a) B
        ∂ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p := rfl
    _ = ∫⁻ o, fibreMeasure p theta o B ∂nu :=
      (lintegral_map (μ := ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p)
        (measurable_of_countable (fun o : Outcome p => fibreMeasure p theta o B)) hF).symm
    _ = ∑ o : Outcome p, fibreMeasure p theta o B * fibreMass p theta o := by
      rw [lintegral_fintype]
      simp only [hmass]
    _ = assignmentLaw p.K B := by
      simpa only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul, mul_comm] using hsum

/-- Forgetting only the auxiliary path recovers the original event source
jointly with an entire product-uniform candidate vector. This retains every
private source coordinate, including `J`, without normalizing the event. -/
public theorem nonrenewedLiftLaw_map_source_vector
    (control0 : ContinuousLearningRows.TimeControl p) :
    (nonrenewedLiftLaw rate rewards C_star C_h u t control0).map
      (fun wv => (wv.1.1, wv.2)) =
    (eventSourceLaw rate rewards C_star C_h u t).prod (assignmentLaw p.K) := by
  let k := nonrenewedVectorKernel rate rewards C_star C_h u t control0
  have hmap : Measurable (fun wv :
      (EventSource rate rewards C_star C_h u t × ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p) ×
        AssignmentVector p => (wv.1.1, wv.2)) := measurable_fst.fst.prodMk measurable_snd
  apply Measure.ext_prod
  intro A B hA hB
  rw [Measure.map_apply hmap (hA.prod hB)]
  have hpre : (fun wv :
      (EventSource rate rewards C_star C_h u t × ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p) ×
        AssignmentVector p => (wv.1.1, wv.2)) ⁻¹' (A ×ˢ B) = (A ×ˢ Set.univ) ×ˢ B := by
    ext wv
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, and_true]
  rw [hpre, nonrenewedLiftLaw, Measure.compProd_apply_prod (hA.prod MeasurableSet.univ) hB,
    nonrenewedBaseLaw, ← Measure.prod_restrict, Measure.restrict_univ]
  rw [lintegral_prod _ (k.measurable_coe hB).aemeasurable]
  change (∫⁻ z, ∫⁻ a, nonrenewedVectorKernel rate rewards C_star C_h u t control0 (z, a) B
    ∂ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p
    ∂(eventSourceLaw rate rewards C_star C_h u t).restrict A) = _
  simp_rw [auxiliary_average_vectorKernel rate rewards C_star C_h u t control0 _ B hB]
  rw [lintegral_const, Measure.restrict_apply_univ, Measure.prod_prod, mul_comm]

/-- Zero-mass endpoint strata have zero auxiliary mass; no unsupported row
is deleted from the definition of the kernel. -/
public theorem ae_endpoint_fibreMass_pos
    (control0 : ContinuousLearningRows.TimeControl p)
    (z : EventSource rate rewards C_star C_h u t) :
    ∀ᵐ a ∂ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p,
      0 < fibreMass p (nextParameter rate rewards C_star C_h u t control0 z)
        (some (path z a (Fin.last (t.val - u.val)))) := by
  have heach : ∀ U : SlowSet p,
      ∀ᵐ a ∂ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p,
        path z a (Fin.last (t.val - u.val)) = U →
          0 < fibreMass p (nextParameter rate rewards C_star C_h u t control0 z) (some U) := by
    intro U
    by_cases hp : 0 < fibreMass p (nextParameter rate rewards C_star C_h u t control0 z) (some U)
    · exact Filter.Eventually.of_forall (fun _ _ => hp)
    · have hz : fibreMass p (nextParameter rate rewards C_star C_h u t control0 z) (some U) = 0 :=
        le_antisymm (not_lt.mp hp) bot_le
      have hnull := (collectionPath_endpoint_fibreMass rate rewards C_star C_h u t control0 z).2 U
      rw [hz] at hnull
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with a ha
      exact fun h => (ha h).elim
  filter_upwards [Filter.eventually_all.mpr heach] with a ha
  exact ha _ rfl

/-- The actual inserted whole vector realizes the SAME generated incoming
endpoint almost surely on the original unnormalized event. -/
public theorem ae_nonrenewedLiftLaw_endpoint
    (control0 : ContinuousLearningRows.TimeControl p) :
    ∀ᵐ wv ∂nonrenewedLiftLaw rate rewards C_star C_h u t control0,
      successfulSlowSet p (nextParameter rate rewards C_star C_h u t control0 wv.1.1)
        (av t (insertedSource t wv.1.1.val wv.2)) =
        some (path wv.1.1 wv.1.2 (Fin.last (t.val - u.val))) := by
  simp_rw [insertedSource, ReferenceFirstCollectionRenewalVectorInsertion.av_insert]
  have htheta : Measurable (fun wv :
      (EventSource rate rewards C_star C_h u t × ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p) ×
        AssignmentVector p => nextParameter rate rewards C_star C_h u t control0 wv.1.1) :=
    (measurable_nextParameter rate rewards C_star C_h u t control0).comp
      (measurable_fst.comp measurable_fst)
  have hout : Measurable (fun wv :
      (EventSource rate rewards C_star C_h u t × ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p) ×
        AssignmentVector p => successfulSlowSet p
          (nextParameter rate rewards C_star C_h u t control0 wv.1.1) wv.2) :=
    (measurable_successfulSlowSet_joint p).comp (htheta.prodMk measurable_snd)
  have hlast : Measurable (fun wv :
      (EventSource rate rewards C_star C_h u t × ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p) ×
        AssignmentVector p => path wv.1.1 wv.1.2 (Fin.last (t.val - u.val))) :=
    (measurable_pi_apply (Fin.last (t.val - u.val))).comp
    ((measurable_collectionPath rate rewards C_star C_h u t).comp measurable_fst)
  have hsome := (measurable_of_countable (some : SlowSet p → Outcome p)).comp hlast
  apply Measure.ae_compProd_of_ae_ae (measurableSet_eq_fun hout hsome)
  have hpos : ∀ᵐ w ∂nonrenewedBaseLaw rate rewards C_star C_h u t,
      0 < fibreMass p (nextParameter rate rewards C_star C_h u t control0 w.1)
        (some (path w.1 w.2 (Fin.last (t.val - u.val)))) := by
    have hmass : Measurable (fun w : EventSource rate rewards C_star C_h u t ×
        ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p =>
        fibreMass p (nextParameter rate rewards C_star C_h u t control0 w.1)
          (some (path w.1 w.2 (Fin.last (t.val - u.val))))) := by
      have hend : Measurable (fun w : EventSource rate rewards C_star C_h u t ×
          ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p => path w.1 w.2 (Fin.last (t.val - u.val))) :=
        (measurable_pi_apply (Fin.last (t.val - u.val))).comp (measurable_collectionPath rate rewards C_star C_h u t)
      have hparam : Measurable (fun w : EventSource rate rewards C_star C_h u t ×
          ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p =>
          nextParameter rate rewards C_star C_h u t control0 w.1) :=
        (measurable_nextParameter rate rewards C_star C_h u t control0).comp measurable_fst
      have ho : Measurable (fun w : EventSource rate rewards C_star C_h u t ×
          ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p =>
          some (path w.1 w.2 (Fin.last (t.val - u.val))) : _ → Outcome p) :=
        (measurable_of_countable (some : SlowSet p → Outcome p)).comp hend
      intro S hS
      exact hparam.prodMk ho (measurable_fibreMass_joint p hS)
    change ∀ᵐ w ∂(eventSourceLaw rate rewards C_star C_h u t).prod
      (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p), _
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_lt measurable_const hmass)).mpr
    exact Filter.Eventually.of_forall (ae_endpoint_fibreMass_pos rate rewards C_star C_h u t control0)
  filter_upwards [hpos] with w hw
  change ∀ᵐ v ∂fibreMeasure p (nextParameter rate rewards C_star C_h u t control0 w.1)
    (some (path w.1 w.2 (Fin.last (t.val - u.val)))), _
  exact ae_successfulSlowSet_eq_of_fibreMass_pos p
    (nextParameter rate rewards C_star C_h u t control0 w.1)
    (some (path w.1 w.2 (Fin.last (t.val - u.val)))) hw

section SourceMarginal
open ReferenceFixedTimeSourceControlCoupling

private def replaceControlVector {p : ConstructorDimensions.Parameters}
    (control : ContinuousLearningRows.TimeControl p) (v : AssignmentParameterFibreKernel.AssignmentVector p) : ContinuousLearningRows.TimeControl p :=
  let e := LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p
  e.symm (v, (e control).2)

private theorem measurable_replaceControlVector {p : ConstructorDimensions.Parameters} :
    Measurable (fun z : ContinuousLearningRows.TimeControl p × AssignmentParameterFibreKernel.AssignmentVector p => replaceControlVector z.1 z.2) := by
  let e := LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p
  exact e.symm.measurable.comp
    (measurable_snd.prodMk (measurable_snd.comp (e.measurable.comp measurable_fst)))

private theorem insert_eq_split_controlReplacement
    {p : ConstructorDimensions.Parameters} (t : Fin p.T) (q : Fin (M p))
    (source : BootstrapPrivateRoundStreams.SourceInput p) (v : AssignmentParameterFibreKernel.AssignmentVector p)
    (hq : ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p source = q) :
    ReferenceFirstCollectionRenewalVectorInsertion.insert t source v =
      (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).symm
        (replaceControlVector
          (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t source).1 v,
          (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t source).2) := by
  let split := ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t
  have hselected : ActualInitializationPhysicalStep.selectedRowIndex p source = q := by
    rw [← ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex]
    exact hq
  have hcontrol : ReferenceFirstCollectionRenewalVectorInsertion.ctrl t source v =
      replaceControlVector (split source).1 v := by
    unfold ReferenceFirstCollectionRenewalVectorInsertion.ctrl
      ReferenceFirstCollectionRenewalVectorInsertion.c
      ReferenceFirstCollectionRenewalVectorInsertion.q replaceControlVector
    rw [hselected, ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_control]
  change ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t source
      (ReferenceFirstCollectionRenewalVectorInsertion.ctrl t source v) = _
  rw [ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_replaceSourceControl
    p q t source _ hq, hcontrol]

private theorem replaceControlVector_map
    {p : ConstructorDimensions.Parameters} :
    ((ContinuousLearningRows.timeControlLaw p).prod
      (ContinuousControlSlice.assignmentLaw p.K)).map
        (fun z : ContinuousLearningRows.TimeControl p × AssignmentParameterFibreKernel.AssignmentVector p => replaceControlVector z.1 z.2) =
      ContinuousLearningRows.timeControlLaw p := by
  let e := LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p
  let vectorLaw := ContinuousControlSlice.assignmentLaw p.K
  let remainderLaw :=
    (LaunchAssignmentCoordinateSplit.nonAssignmentScalarLaw p).prod
      (ContinuousLearningRows.affineSamplesLaw p)
  let splitLaw := LaunchAssignmentCoordinateSplit.measurePreserving_controlAssignmentSplitEquiv p
  have hsplit : (ContinuousLearningRows.timeControlLaw p).map e =
      vectorLaw.prod remainderLaw := splitLaw.map_eq
  have hdropReorder : MeasurePreserving
      (fun z : (AssignmentParameterFibreKernel.AssignmentVector p × (LaunchAssignmentCoordinateSplit.NonAssignmentScalars p ×
          ContinuousLearningRows.AffineSamples p)) × AssignmentParameterFibreKernel.AssignmentVector p =>
        (z.1.1, (z.2, z.1.2)))
      ((vectorLaw.prod remainderLaw).prod vectorLaw)
      (vectorLaw.prod (vectorLaw.prod remainderLaw)) := by
    exact ((MeasurePreserving.id vectorLaw).prod
      (Measure.measurePreserving_swap (μ := remainderLaw) (ν := vectorLaw))).comp
        (measurePreserving_prodAssoc vectorLaw remainderLaw vectorLaw)
  have hdrop :
      ((vectorLaw.prod remainderLaw).prod vectorLaw).map
        (fun z : (AssignmentParameterFibreKernel.AssignmentVector p × (LaunchAssignmentCoordinateSplit.NonAssignmentScalars p ×
          ContinuousLearningRows.AffineSamples p)) × AssignmentParameterFibreKernel.AssignmentVector p => (z.2, z.1.2)) =
        vectorLaw.prod remainderLaw := by
    calc
      _ = (Measure.map Prod.snd
          (Measure.map (fun z : (AssignmentParameterFibreKernel.AssignmentVector p ×
            (LaunchAssignmentCoordinateSplit.NonAssignmentScalars p ×
              ContinuousLearningRows.AffineSamples p)) × AssignmentParameterFibreKernel.AssignmentVector p =>
                (z.1.1, (z.2, z.1.2)))
            ((vectorLaw.prod remainderLaw).prod vectorLaw))) := by
        rw [Measure.map_map measurable_snd hdropReorder.measurable]
        rfl
      _ = (Measure.map Prod.snd (vectorLaw.prod (vectorLaw.prod remainderLaw))) := by
        rw [hdropReorder.map_eq]
      _ = vectorLaw.prod remainderLaw := by
        rw [Measure.map_snd_prod, measure_univ, one_smul]
  have hpush :
      ((ContinuousLearningRows.timeControlLaw p).prod vectorLaw).map
        (fun z : ContinuousLearningRows.TimeControl p × AssignmentParameterFibreKernel.AssignmentVector p => (z.2, (e z.1).2)) =
      vectorLaw.prod remainderLaw := by
    have hsplitProd :
        ((ContinuousLearningRows.timeControlLaw p).prod vectorLaw).map
            (Prod.map e id) =
      ((ContinuousLearningRows.timeControlLaw p).map e).prod vectorLaw := by
      simpa only [Measure.map_id] using
        (Measure.map_prod_map (ContinuousLearningRows.timeControlLaw p) vectorLaw
          e.measurable measurable_id).symm
    calc
      _ = (((ContinuousLearningRows.timeControlLaw p).map e).prod vectorLaw).map
          (fun z : (AssignmentParameterFibreKernel.AssignmentVector p × (LaunchAssignmentCoordinateSplit.NonAssignmentScalars p ×
            ContinuousLearningRows.AffineSamples p)) × AssignmentParameterFibreKernel.AssignmentVector p => (z.2, z.1.2)) := by
        rw [← hsplitProd]
        rw [Measure.map_map (by fun_prop) (by fun_prop)]
        rfl
      _ = vectorLaw.prod remainderLaw := by rw [hsplit, hdrop]
  calc
    _ = ((((ContinuousLearningRows.timeControlLaw p).prod vectorLaw).map
          (fun z : ContinuousLearningRows.TimeControl p × AssignmentParameterFibreKernel.AssignmentVector p => (z.2, (e z.1).2))).map e.symm) := by
        rw [Measure.map_map e.symm.measurable (by fun_prop)]
        rfl
    _ = ContinuousLearningRows.timeControlLaw p := by
        rw [hpush, ← hsplit]
        exact e.map_symm_map

private def controlRemainderVectorEquiv {p : ConstructorDimensions.Parameters}
    (q : Fin (M p)) (t : Fin p.T) :
    ((ContinuousLearningRows.TimeControl p ×
        ReferenceFixedTimeSourceControlCoupling.FixedControlRemainder p q t) × AssignmentParameterFibreKernel.AssignmentVector p) ≃ᵐ
      ((ContinuousLearningRows.TimeControl p × AssignmentParameterFibreKernel.AssignmentVector p) ×
        ReferenceFixedTimeSourceControlCoupling.FixedControlRemainder p q t) :=
  (MeasurableEquiv.prodAssoc).trans
    (((MeasurableEquiv.refl _).prodCongr MeasurableEquiv.prodComm).trans
      MeasurableEquiv.prodAssoc.symm)

private theorem controlRemainderVector_map
    {p : ConstructorDimensions.Parameters} (q : Fin (M p)) (t : Fin p.T)
    (remainderLaw : Measure (ReferenceFixedTimeSourceControlCoupling.FixedControlRemainder p q t))
    [SFinite remainderLaw] :
    MeasurePreserving (controlRemainderVectorEquiv (p := p) q t)
      (((ContinuousLearningRows.timeControlLaw p).prod remainderLaw).prod
        (ContinuousControlSlice.assignmentLaw p.K))
      (((ContinuousLearningRows.timeControlLaw p).prod
        (ContinuousControlSlice.assignmentLaw p.K)).prod remainderLaw) := by
  exact (measurePreserving_prodAssoc (ContinuousLearningRows.timeControlLaw p)
      (ContinuousControlSlice.assignmentLaw p.K) remainderLaw).symm.comp
    (((MeasurePreserving.id (ContinuousLearningRows.timeControlLaw p)).prod
      (Measure.measurePreserving_swap (μ := remainderLaw)
        (ν := ContinuousControlSlice.assignmentLaw p.K))).comp
      (measurePreserving_prodAssoc (ContinuousLearningRows.timeControlLaw p) remainderLaw
        (ContinuousControlSlice.assignmentLaw p.K)))

private theorem insertedSource_stationary_stratum
    {p : ConstructorDimensions.Parameters}
    (t : Fin p.T) (q : Fin (M p)) :
    (((BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
        (ReferenceFixedTimeSourceControlCoupling.fixedControlSourceStratum p q)).prod
      (ContinuousControlSlice.assignmentLaw p.K)).map
        (fun sv : BootstrapPrivateRoundStreams.SourceInput p × AssignmentParameterFibreKernel.AssignmentVector p =>
          ReferenceFirstCollectionRenewalVectorInsertion.insert t sv.1 sv.2) =
      ((BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
        (ReferenceFixedTimeSourceControlCoupling.fixedControlSourceStratum p q)) := by
  let split := ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t
  let stratum := ReferenceFixedTimeSourceControlCoupling.fixedControlSourceStratum p q
  let remainderEvent := ReferenceFixedTimeSourceControlCoupling.fixedControlRemainderStratum p q t
  let remainderLaw :=
    (ReferenceFixedTimeSourceControlCoupling.fixedControlRemainderLaw p q t).restrict remainderEvent
  let vectorLaw := ContinuousControlSlice.assignmentLaw p.K
  let replace := replaceControlVector (p := p)
  let replacePair := fun z : ContinuousLearningRows.TimeControl p × AssignmentParameterFibreKernel.AssignmentVector p => replace z.1 z.2
  let splitMap := fun sv : BootstrapPrivateRoundStreams.SourceInput p × AssignmentParameterFibreKernel.AssignmentVector p => (split sv.1, sv.2)
  let targetMap := fun z : (ContinuousLearningRows.TimeControl p ×
      ReferenceFixedTimeSourceControlCoupling.FixedControlRemainder p q t) × AssignmentParameterFibreKernel.AssignmentVector p =>
    split.symm (replace z.1.1 z.2, z.1.2)
  let reorderedTargetMap := fun z : (ContinuousLearningRows.TimeControl p × AssignmentParameterFibreKernel.AssignmentVector p) ×
      ReferenceFixedTimeSourceControlCoupling.FixedControlRemainder p q t =>
    split.symm (replace z.1.1 z.1.2, z.2)
  have hsplit := ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_privateStratum_map p q t
  have hsourceVector :
      (((BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
        stratum).prod vectorLaw).map splitMap =
        ((ContinuousLearningRows.timeControlLaw p).prod remainderLaw).prod vectorLaw := by
    calc
      _ = (((BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
            stratum).map split).prod vectorLaw := by
        change Measure.map (Prod.map split id)
          (((BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
            stratum).prod vectorLaw) = _
        have h := (Measure.map_prod_map
          ((BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
            stratum) vectorLaw
          split.measurable measurable_id).symm
        simpa only [Measure.map_id] using h
      _ = _ := by rw [hsplit]
  have hstratum : ∀ᵐ s ∂(BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
      stratum, s ∈ stratum := by
    have hmem := ae_restrict_mem (μ := BootstrapPrivateRoundStreams.sourceInputLaw p)
      (s := stratum)
      (ReferenceFixedTimeSourceControlCoupling.measurableSet_fixedControlSourceStratum p q)
    filter_upwards [hmem] with s hs
    exact hs
  have hstratumPair : ∀ᵐ sv ∂
      (((BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
        stratum).prod vectorLaw),
        sv.1 ∈ stratum := by
    have hrectangle : MeasurableSet (stratum ×ˢ (Set.univ : Set (AssignmentParameterFibreKernel.AssignmentVector p))) :=
      (ReferenceFixedTimeSourceControlCoupling.measurableSet_fixedControlSourceStratum p q).prod
        MeasurableSet.univ
    have hprod := (Measure.ae_prod_mem_iff_ae_ae_mem
      (μ := (BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
        stratum)
      (ν := vectorLaw) hrectangle).mpr (by
      filter_upwards [hstratum] with s hs
      filter_upwards [] with v
      exact ⟨hs, trivial⟩)
    filter_upwards [hprod] with sv h
    exact h.1
  have hinsert : ∀ᵐ sv ∂
      (((BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
        stratum).prod vectorLaw),
        ReferenceFirstCollectionRenewalVectorInsertion.insert t sv.1 sv.2 =
          targetMap (splitMap sv) := by
    filter_upwards [hstratumPair] with sv hq
    have hq' : ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p sv.1 = q := hq
    exact insert_eq_split_controlReplacement t q sv.1 sv.2 hq'
  have hmove := controlRemainderVector_map (p := p) q t remainderLaw
  have htargetMeasurable : Measurable targetMap := by
    exact split.symm.measurable.comp
      ((measurable_replaceControlVector.comp
          ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).prodMk
        (measurable_snd.comp measurable_fst))
  have hreorderedTargetMeasurable : Measurable reorderedTargetMap := by
    exact split.symm.measurable.comp
      ((measurable_replaceControlVector.comp
          ((measurable_fst.comp measurable_fst).prodMk (measurable_snd.comp measurable_fst))).prodMk
        measurable_snd)
  have hreplacePairMeasurable : Measurable replacePair := by
    exact measurable_replaceControlVector
  have hreplaceRemainderMeasurable : Measurable
      (Prod.map replacePair
        (id : ReferenceFixedTimeSourceControlCoupling.FixedControlRemainder p q t →
          ReferenceFixedTimeSourceControlCoupling.FixedControlRemainder p q t)) := by
    exact (hreplacePairMeasurable.comp measurable_fst).prodMk measurable_snd
  have hreplaceRemainderMap :
      Measure.map (Prod.map replacePair
          (id : ReferenceFixedTimeSourceControlCoupling.FixedControlRemainder p q t →
            ReferenceFixedTimeSourceControlCoupling.FixedControlRemainder p q t))
          (((ContinuousLearningRows.timeControlLaw p).prod vectorLaw).prod remainderLaw) =
        ((Measure.map replacePair ((ContinuousLearningRows.timeControlLaw p).prod vectorLaw)).prod
          remainderLaw) := by
    simpa only [Measure.map_id] using
      (Measure.map_prod_map
        ((ContinuousLearningRows.timeControlLaw p).prod vectorLaw) remainderLaw
        hreplacePairMeasurable measurable_id).symm
  calc
    _ = (((BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
          stratum).prod vectorLaw).map
          (targetMap ∘ splitMap) := by
        exact Measure.map_congr hinsert
    _ = ((((BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
          stratum).prod vectorLaw).map
          splitMap).map targetMap := by
        rw [Measure.map_map htargetMeasurable (by fun_prop)]
    _ = (((ContinuousLearningRows.timeControlLaw p).prod remainderLaw).prod vectorLaw).map
          targetMap := by rw [hsourceVector]
    _ = ((((ContinuousLearningRows.timeControlLaw p).prod remainderLaw).prod vectorLaw).map
          (controlRemainderVectorEquiv (p := p) q t)).map reorderedTargetMap := by
        rw [Measure.map_map hreorderedTargetMeasurable
          (controlRemainderVectorEquiv (p := p) q t).measurable]
        rfl
    _ = (((ContinuousLearningRows.timeControlLaw p).prod vectorLaw).prod remainderLaw).map
          reorderedTargetMap := by rw [hmove.map_eq]
    _ = Measure.map split.symm
          (Measure.map (Prod.map replacePair id)
            (((ContinuousLearningRows.timeControlLaw p).prod vectorLaw).prod remainderLaw)) := by
        rw [Measure.map_map split.symm.measurable hreplaceRemainderMeasurable]
        rfl
    _ = Measure.map split.symm
          ((((ContinuousLearningRows.timeControlLaw p).prod vectorLaw).map
            (fun z => replace z.1 z.2)).prod remainderLaw) := by
        rw [hreplaceRemainderMap]
    _ = ((ContinuousLearningRows.timeControlLaw p).prod remainderLaw).map split.symm := by
        rw [replaceControlVector_map]
    _ = (BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
          stratum := by
        rw [← hsplit]
        exact split.map_symm_map

private theorem insertedSource_stationary (t : Fin p.T) :
    ((BootstrapPrivateRoundStreams.sourceInputLaw p).prod (assignmentLaw p.K)).map
      (fun sv => insert t sv.1 sv.2) = BootstrapPrivateRoundStreams.sourceInputLaw p := by
  have hsum : Measure.sum (fun q : Fin (M p) =>
      (BootstrapPrivateRoundStreams.sourceInputLaw p).restrict (fixedControlSourceStratum p q)) =
      BootstrapPrivateRoundStreams.sourceInputLaw p := by
    rw [Measure.sum_fintype]
    exact FiniteFibreLift.sum_restrict_fibre _ (sourceCoordinatorIndex p)
      (BootstrapPrivateRoundStreams.measurable_sourceCoordinatorIndex p)
  calc
    _ = ((Measure.sum (fun q : Fin (M p) =>
        (BootstrapPrivateRoundStreams.sourceInputLaw p).restrict (fixedControlSourceStratum p q))).prod
          (assignmentLaw p.K)).map (fun sv => insert t sv.1 sv.2) := by rw [hsum]
    _ = Measure.sum (fun q : Fin (M p) =>
        (((BootstrapPrivateRoundStreams.sourceInputLaw p).restrict (fixedControlSourceStratum p q)).prod
          (assignmentLaw p.K)).map (fun sv => insert t sv.1 sv.2)) := by
      rw [Measure.prod_sum_left]
      exact Measure.map_sum (ReferenceFirstCollectionRenewalVectorInsertion.measurable_insert (t := t)).aemeasurable
    _ = _ := by
      simp_rw [insertedSource_stationary_stratum]
      exact hsum

/-- Literal source insertion preserves the unnormalized first nonrenewed
clear event, with the original private-index stratum masses intact. -/
public theorem insertedSource_event_stationary :
    (((BootstrapPrivateRoundStreams.sourceInputLaw p).restrict event).prod (assignmentLaw p.K)).map
      (fun sv => insertedSource t sv.1 sv.2) =
    (BootstrapPrivateRoundStreams.sourceInputLaw p).restrict event := by
  have hf : Measurable (fun sv : BootstrapPrivateRoundStreams.SourceInput p ×
      AssignmentParameterFibreKernel.AssignmentVector p => insertedSource t sv.1 sv.2) :=
    ReferenceFirstCollectionRenewalVectorInsertion.measurable_insert (p := p) (t := t)
  have hE := measurableSet_firstLiveCollectionEvent rate rewards C_star C_h u t
  have hpre : (fun sv : BootstrapPrivateRoundStreams.SourceInput p × AssignmentParameterFibreKernel.AssignmentVector p =>
      insertedSource t sv.1 sv.2) ⁻¹' event = event ×ˢ Set.univ := by
    ext sv
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, and_true]
    exact (firstLiveCollectionEvent_replace_current_iff rate rewards C_star C_h u t sv.1 (ctrl t sv.1 sv.2)).symm
  rw [← Measure.restrict_univ (μ := assignmentLaw p.K), Measure.prod_restrict,
    ← hpre, ← Measure.restrict_map hf hE]
  rw [show (((BootstrapPrivateRoundStreams.sourceInputLaw p).prod (assignmentLaw p.K)).map
    (fun sv => insertedSource t sv.1 sv.2)) = BootstrapPrivateRoundStreams.sourceInputLaw p from
      insertedSource_stationary t]

/-- The full inserted original-source marginal, obtained by integrating the
actual endpoint fibre law internally. All original rows and private arrays,
including `J`, have their original unnormalized event-restricted law. -/
public theorem nonrenewedLiftLaw_map_inserted_source
    (control0 : ContinuousLearningRows.TimeControl p) :
    (nonrenewedLiftLaw rate rewards C_star C_h u t control0).map
      (fun wv => insertedSource t wv.1.1.val wv.2) =
    (BootstrapPrivateRoundStreams.sourceInputLaw p).restrict event := by
  have hprojection : Measurable (fun wv : (EventSource rate rewards C_star C_h u t ×
      ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p) × AssignmentParameterFibreKernel.AssignmentVector p =>
      (wv.1.1, wv.2)) := measurable_fst.fst.prodMk measurable_snd
  have hsourceVector : (nonrenewedLiftLaw rate rewards C_star C_h u t control0).map
      (fun wv => (wv.1.1.val, wv.2)) =
      ((BootstrapPrivateRoundStreams.sourceInputLaw p).restrict event).prod (assignmentLaw p.K) := by
    calc
      _ = ((nonrenewedLiftLaw rate rewards C_star C_h u t control0).map
          (fun wv => (wv.1.1, wv.2))).map (Prod.map Subtype.val id) := by
        symm
        exact Measure.map_map (measurable_subtype_coe.prodMap measurable_id) hprojection
      _ = _ := by
        rw [nonrenewedLiftLaw_map_source_vector,
          ← Measure.map_prod_map _ _ measurable_subtype_coe measurable_id, Measure.map_id]
        exact congrArg (fun mu => mu.prod (assignmentLaw p.K))
          (ReferenceFirstLiveCollectionPathJoin.eventSourceLaw_map rate rewards C_star C_h u t)
  calc
    _ = ((nonrenewedLiftLaw rate rewards C_star C_h u t control0).map
        (fun wv => (wv.1.1.val, wv.2))).map (fun sv => insertedSource t sv.1 sv.2) := by
      symm
      exact Measure.map_map (ReferenceFirstCollectionRenewalVectorInsertion.measurable_insert (t := t))
        ((measurable_subtype_coe.prodMap measurable_id).comp hprojection)
    _ = _ := by
      rw [hsourceVector]
      exact insertedSource_event_stationary rate rewards C_star C_h u t

end SourceMarginal

/-- The literal event is determined by the strict source prefix. -/
public theorem event_sourcePrefix_iff (control0 : ContinuousLearningRows.TimeControl p)
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    sourcePrefix control0 t.val z ∈ event ↔ z ∈ event := by
  rw [sourcePrefix_eq_suffix control0 t.val t.isLt]
  exact (firstLiveCollectionEvent_suffix_iff rate rewards C_star C_h u t z (fun _ => control0)).symm

public def prefixEvent (control0 : ContinuousLearningRows.TimeControl p)
    (z : EventSource rate rewards C_star C_h u t) : EventSource rate rewards C_star C_h u t :=
  ⟨sourcePrefix control0 t.val z.val,
    (event_sourcePrefix_iff rate rewards C_star C_h u t control0 z.val).mpr z.property⟩

public theorem measurable_prefixEvent (control0 : ContinuousLearningRows.TimeControl p) :
    Measurable (prefixEvent rate rewards C_star C_h u t control0) :=
  ((measurable_sourcePrefix control0 t.val).comp measurable_subtype_coe).subtype_mk

public theorem nextInvocationObservation_prefixEvent
    (control0 : ContinuousLearningRows.TimeControl p)
    (z : EventSource rate rewards C_star C_h u t)
    (a : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p) :
    nextInvocationObservation rate rewards C_star C_h u t control0
      (prefixEvent rate rewards C_star C_h u t control0 z, a) =
    nextInvocationObservation rate rewards C_star C_h u t control0 (z, a) := by
  have hstate (n : ℕ) (hn : n ≤ p.T) (hnt : n ≤ t.val) :
      extendedPrefixStateAux rate rewards C_star C_h n hn (sourcePrefix control0 t.val z.val, a) =
      extendedPrefixStateAux rate rewards C_star C_h n hn (z.val, a) := by
    rw [extendedPrefixStateAux_sourcePrefix rate rewards C_star C_h control0 n hn
      (sourcePrefix control0 t.val z.val) a, sourcePrefix_sourcePrefix control0 n t.val hnt]
    exact (extendedPrefixStateAux_sourcePrefix rate rewards C_star C_h control0 n hn z.val a).symm
  apply Prod.ext
  · change (sourcePrefix control0 t.val (sourcePrefix control0 t.val z.val),
      (labelZero a, _)) = (sourcePrefix control0 t.val z.val, (labelZero a, _))
    rw [sourcePrefix_sourcePrefix control0 t.val t.val le_rfl]
    exact congrArg (fun L => (sourcePrefix control0 t.val z.val, (labelZero a, L.2)))
      (hstate t.val (Nat.le_of_lt t.isLt) le_rfl)
  · funext i
    have hl := generatedIncoming_eq_path rate rewards C_star C_h u t
      (prefixEvent rate rewards C_star C_h u t control0 z) a i
    have hr := generatedIncoming_eq_path rate rewards C_star C_h u t z a i
    have hd := firstLiveCollectionEvent_dates rate rewards C_star C_h u t z.val z.property
    have hi := i.isLt
    exact Option.some.inj (hl.symm.trans ((congrArg Prod.fst
      (hstate (u.val + i.val) (by have ht := t.isLt; omega) (by omega))).trans hr))

/-- Carry the actual parameter beside the complete retained observation.
It is determined by the observation's strict-prefix coordinate. -/
public def signature (control0 : ContinuousLearningRows.TimeControl p)
    (w : EventSource rate rewards C_star C_h u t × ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p) :
    (ReferenceFirstCollectionLogicalPrefixExtension.Observation rate × ReferenceFirstLiveCollectionPathJoin.Path u t) × Theta p :=
  (nextInvocationObservation rate rewards C_star C_h u t control0 w,
    nextParameter rate rewards C_star C_h u t control0 w.1)

public theorem measurable_signature (control0 : ContinuousLearningRows.TimeControl p) :
    Measurable (signature rate rewards C_star C_h u t control0) :=
  (measurable_nextInvocationObservation rate rewards C_star C_h u t control0).prodMk
    ((measurable_nextParameter rate rewards C_star C_h u t control0).comp measurable_fst)

private theorem signature_prefixEvent (control0 : ContinuousLearningRows.TimeControl p)
    (z : EventSource rate rewards C_star C_h u t)
    (a : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p) :
    signature rate rewards C_star C_h u t control0 (prefixEvent rate rewards C_star C_h u t control0 z, a) =
    signature rate rewards C_star C_h u t control0 (z, a) := by
  apply Prod.ext (nextInvocationObservation_prefixEvent rate rewards C_star C_h u t control0 z a)
  change nextParameter rate rewards C_star C_h u t control0 (prefixEvent rate rewards C_star C_h u t control0 z) =
    nextParameter rate rewards C_star C_h u t control0 z
  apply Option.some.inj
  rw [← nextParameter_spec, ← nextParameter_spec]
  exact congrArg (calendarParameters rate rewards C_star C_h t)
    (sourcePrefix_sourcePrefix control0 t.val t.val le_rfl z.val)

private theorem restricted_prefix_control_product (control0 : ContinuousLearningRows.TimeControl p) :
    ((BootstrapPrivateRoundStreams.sourceInputLaw p).restrict event).map
      (fun z => (sourcePrefix control0 t.val z, ReferenceSourceCurrentControlFreshness.u_t p t z)) =
    (((BootstrapPrivateRoundStreams.sourceInputLaw p).restrict event).map
      (sourcePrefix control0 t.val)).prod (ContinuousLearningRows.timeControlLaw p) := by
  have hE := measurableSet_firstLiveCollectionEvent rate rewards C_star C_h u t
  have hp := measurable_sourcePrefix control0 t.val
  have hf := hp.prodMk (ReferenceSourceCurrentControlFreshness.measurable_u_t t)
  have hpre : (sourcePrefix control0 t.val) ⁻¹' event = event := by
    ext z; exact event_sourcePrefix_iff rate rewards C_star C_h u t control0 z
  have hprePair : (fun z => (sourcePrefix control0 t.val z,
      ReferenceSourceCurrentControlFreshness.u_t p t z)) ⁻¹' (event ×ˢ Set.univ) = event := by
    ext z
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, and_true]
    exact event_sourcePrefix_iff rate rewards C_star C_h u t control0 z
  have h := congrArg (fun mu => mu.restrict (event ×ˢ Set.univ))
    (ReferenceFirstLiveCalendarMarkedTransition.sourcePrefix_currentControl_product control0 t)
  rw [Measure.restrict_map hf (hE.prod MeasurableSet.univ), hprePair,
    ← Measure.prod_restrict, Measure.restrict_univ, Measure.restrict_map hp hE, hpre] at h
  exact h

private theorem event_prefix_control_product (control0 : ContinuousLearningRows.TimeControl p) :
    (eventSourceLaw rate rewards C_star C_h u t).map
      (fun z => (prefixEvent rate rewards C_star C_h u t control0 z,
        ReferenceSourceCurrentControlFreshness.u_t p t z.val)) =
    ((eventSourceLaw rate rewards C_star C_h u t).map
      (prefixEvent rate rewards C_star C_h u t control0)).prod (ContinuousLearningRows.timeControlLaw p) := by
  have emb : MeasurableEmbedding (Prod.map
      (Subtype.val : EventSource rate rewards C_star C_h u t → BootstrapPrivateRoundStreams.SourceInput p)
      (id : ContinuousLearningRows.TimeControl p → ContinuousLearningRows.TimeControl p)) :=
    (MeasurableEmbedding.subtype_coe
    (measurableSet_firstLiveCollectionEvent rate rewards C_star C_h u t)).prodMap MeasurableEmbedding.id
  apply emb.map_injective
  have hval : (eventSourceLaw rate rewards C_star C_h u t).map Subtype.val =
      (BootstrapPrivateRoundStreams.sourceInputLaw p).restrict event :=
    ReferenceFirstLiveCollectionPathJoin.eventSourceLaw_map rate rewards C_star C_h u t
  have hG : Measurable (fun z : EventSource rate rewards C_star C_h u t =>
      (prefixEvent rate rewards C_star C_h u t control0 z, ReferenceSourceCurrentControlFreshness.u_t p t z.val)) :=
    (measurable_prefixEvent rate rewards C_star C_h u t control0).prodMk
      ((ReferenceSourceCurrentControlFreshness.measurable_u_t t).comp measurable_subtype_coe)
  have hF := (measurable_sourcePrefix control0 t.val).prodMk (ReferenceSourceCurrentControlFreshness.measurable_u_t t)
  have hleft : ((eventSourceLaw rate rewards C_star C_h u t).map
      (fun z => (prefixEvent rate rewards C_star C_h u t control0 z, ReferenceSourceCurrentControlFreshness.u_t p t z.val))).map
        (Prod.map Subtype.val id) = ((BootstrapPrivateRoundStreams.sourceInputLaw p).restrict event).map
          (fun z => (sourcePrefix control0 t.val z, ReferenceSourceCurrentControlFreshness.u_t p t z)) := by
    calc
      _ = (eventSourceLaw rate rewards C_star C_h u t).map
          ((fun z => (sourcePrefix control0 t.val z, ReferenceSourceCurrentControlFreshness.u_t p t z)) ∘ Subtype.val) :=
        by simpa only [Function.comp_def, Prod.map, prefixEvent, id_eq] using
          (Measure.map_map (μ := eventSourceLaw rate rewards C_star C_h u t) emb.measurable hG)
      _ = _ := by
        rw [← Measure.map_map hF measurable_subtype_coe,
          hval]
  have hright : (((eventSourceLaw rate rewards C_star C_h u t).map
      (prefixEvent rate rewards C_star C_h u t control0)).prod (ContinuousLearningRows.timeControlLaw p)).map
        (Prod.map Subtype.val id) = (((BootstrapPrivateRoundStreams.sourceInputLaw p).restrict event).map
          (sourcePrefix control0 t.val)).prod (ContinuousLearningRows.timeControlLaw p) := by
    rw [← Measure.map_prod_map _ _ measurable_subtype_coe measurable_id, Measure.map_id]
    congr 1
    calc
      _ = (eventSourceLaw rate rewards C_star C_h u t).map ((sourcePrefix control0 t.val) ∘ Subtype.val) :=
        by simpa only [Function.comp_def, prefixEvent] using
          (Measure.map_map (μ := eventSourceLaw rate rewards C_star C_h u t) measurable_subtype_coe
            (measurable_prefixEvent rate rewards C_star C_h u t control0))
      _ = _ := by
        rw [← Measure.map_map (measurable_sourcePrefix control0 t.val) measurable_subtype_coe,
          hval]
  exact hleft.trans ((restricted_prefix_control_product rate rewards C_star C_h u t control0).trans hright.symm)

/-- Fresh whole current controls jointly with the SAME path, full old list,
whole label-zero array, and actual sampler parameter. -/
public theorem signature_currentControl_product (control0 : ContinuousLearningRows.TimeControl p) :
    (nonrenewedBaseLaw rate rewards C_star C_h u t).map (fun w =>
      (signature rate rewards C_star C_h u t control0 w, ReferenceSourceCurrentControlFreshness.u_t p t w.1.val)) =
    ((nonrenewedBaseLaw rate rewards C_star C_h u t).map
      (signature rate rewards C_star C_h u t control0)).prod (ContinuousLearningRows.timeControlLaw p) := by
  let mu := eventSourceLaw rate rewards C_star C_h u t
  let pref := prefixEvent rate rewards C_star C_h u t control0
  let mup := mu.map pref
  let muc := ContinuousLearningRows.timeControlLaw p
  let mua := ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p
  let sig := signature rate rewards C_star C_h u t control0
  have hsource : MeasurePreserving (fun z => (pref z, ReferenceSourceCurrentControlFreshness.u_t p t z.val))
      mu (mup.prod muc) := ⟨(measurable_prefixEvent rate rewards C_star C_h u t control0).prodMk
        ((ReferenceSourceCurrentControlFreshness.measurable_u_t t).comp measurable_subtype_coe),
      event_prefix_control_product rate rewards C_star C_h u t control0⟩
  have horder : MeasurePreserving (fun w : (EventSource rate rewards C_star C_h u t ×
      ContinuousLearningRows.TimeControl p) × ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p =>
      ((w.1.1, w.2), w.1.2)) ((mup.prod muc).prod mua) ((mup.prod mua).prod muc) :=
    (measurePreserving_prodAssoc mup mua muc).symm.comp
      (((MeasurePreserving.id mup).prod (Measure.measurePreserving_swap (μ := muc) (ν := mua))).comp
        (measurePreserving_prodAssoc mup muc mua))
  have hsig : MeasurePreserving sig (mup.prod mua) ((mup.prod mua).map sig) :=
    ⟨measurable_signature rate rewards C_star C_h u t control0, rfl⟩
  have hfull := (hsig.prod (MeasurePreserving.id muc)).comp
    (horder.comp (hsource.prod (MeasurePreserving.id mua)))
  have hjoint : (nonrenewedBaseLaw rate rewards C_star C_h u t).map (fun w =>
      (sig w, ReferenceSourceCurrentControlFreshness.u_t p t w.1.val)) =
      ((mup.prod mua).map sig).prod muc := by
    convert hfull.map_eq using 1
    congr 1
    funext w
    exact Prod.ext (signature_prefixEvent rate rewards C_star C_h u t control0 w.1 w.2).symm rfl
  have hmarg := congrArg Measure.fst hjoint
  have hu : Measurable (fun w : EventSource rate rewards C_star C_h u t ×
      ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p => ReferenceSourceCurrentControlFreshness.u_t p t w.1.val) :=
    (ReferenceSourceCurrentControlFreshness.measurable_u_t t).comp (measurable_subtype_coe.comp measurable_fst)
  rw [Measure.fst_map_prodMk (X := sig) (measurable_signature rate rewards C_star C_h u t control0) hu,
    Measure.fst_prod] at hmarg
  rw [hmarg]
  exact hjoint

public def currentRemainder (z : BootstrapPrivateRoundStreams.SourceInput p) :
    LaunchAssignmentCoordinateSplit.NonAssignmentScalars p × ContinuousLearningRows.AffineSamples p :=
  (controlAssignmentSplitEquiv p (ReferenceSourceCurrentControlFreshness.u_t p t z)).2

public theorem measurable_currentRemainder : Measurable (currentRemainder (p := p) t) :=
  measurable_snd.comp ((controlAssignmentSplitEquiv p).measurable.comp
    (ReferenceSourceCurrentControlFreshness.measurable_u_t t))

/-- Current physical remainder freshness follows from the source-prefix
product and the original measure-preserving assignment/control split. -/
public theorem signature_currentRemainder_product (control0 : ContinuousLearningRows.TimeControl p) :
    (nonrenewedBaseLaw rate rewards C_star C_h u t).map (fun w =>
      (signature rate rewards C_star C_h u t control0 w, currentRemainder t w.1.val)) =
    ((nonrenewedBaseLaw rate rewards C_star C_h u t).map
      (signature rate rewards C_star C_h u t control0)).prod
      ((LaunchAssignmentCoordinateSplit.nonAssignmentScalarLaw p).prod (ContinuousLearningRows.affineSamplesLaw p)) := by
  have hrem : MeasurePreserving (fun c : ContinuousLearningRows.TimeControl p => (controlAssignmentSplitEquiv p c).2)
      (ContinuousLearningRows.timeControlLaw p)
      ((LaunchAssignmentCoordinateSplit.nonAssignmentScalarLaw p).prod (ContinuousLearningRows.affineSamplesLaw p)) := by
    refine ⟨measurable_snd.comp (controlAssignmentSplitEquiv p).measurable, ?_⟩
    calc
      _ = ((ContinuousLearningRows.timeControlLaw p).map (controlAssignmentSplitEquiv p)).map Prod.snd :=
        (Measure.map_map measurable_snd (controlAssignmentSplitEquiv p).measurable).symm
      _ = _ := by rw [(LaunchAssignmentCoordinateSplit.measurePreserving_controlAssignmentSplitEquiv p).map_eq,
        Measure.map_snd_prod, measure_univ, one_smul]
  have hsource : MeasurePreserving (fun w =>
      (signature rate rewards C_star C_h u t control0 w, ReferenceSourceCurrentControlFreshness.u_t p t w.1.val))
      (nonrenewedBaseLaw rate rewards C_star C_h u t)
      (((nonrenewedBaseLaw rate rewards C_star C_h u t).map
        (signature rate rewards C_star C_h u t control0)).prod (ContinuousLearningRows.timeControlLaw p)) :=
    ⟨(measurable_signature rate rewards C_star C_h u t control0).prodMk
      ((ReferenceSourceCurrentControlFreshness.measurable_u_t t).comp (measurable_subtype_coe.comp measurable_fst)),
      signature_currentControl_product rate rewards C_star C_h u t control0⟩
  exact ((MeasurePreserving.id _).prod hrem).comp hsource |>.map_eq

abbrev SignatureValue := (ReferenceFirstCollectionLogicalPrefixExtension.Observation rate ×
  ReferenceFirstLiveCollectionPathJoin.Path u t) × Theta p
abbrev Remainder (p : ConstructorDimensions.Parameters) :=
  LaunchAssignmentCoordinateSplit.NonAssignmentScalars p × ContinuousLearningRows.AffineSamples p

/-- The same fibre kernel written on its literal retained data. -/
public def signatureVectorKernel : ProbabilityTheory.Kernel (SignatureValue rate u t) (AssignmentVector p) :=
  (assignmentParameterFibreKernel p).comap
    (fun s => (s.2, some (s.1.2 (Fin.last (t.val - u.val)))))
    (measurable_snd.prodMk ((measurable_of_countable (some : SlowSet p → Outcome p)).comp
      ((measurable_pi_apply (Fin.last (t.val - u.val))).comp measurable_fst.snd)))

public instance signatureVectorKernel_markov :
    ProbabilityTheory.IsMarkovKernel (signatureVectorKernel rate u t) := by
  unfold signatureVectorKernel
  infer_instance

/-- Arbitrary bounded Borel JOINT tests of the retained complete observation,
inserted whole vector and current physical remainder. The vector kernel
carries the hidden endpoint; only the physical remainder has an independent
product law. The outer measure retains the original event mass. -/
public theorem nonrenewed_joint_test (control0 : ContinuousLearningRows.TimeControl p)
    (Phi : (ReferenceFirstCollectionLogicalPrefixExtension.Observation rate ×
      ReferenceFirstLiveCollectionPathJoin.Path u t) × (AssignmentVector p × Remainder p) → ℝ)
    (hPhi : Measurable Phi) (M : ℝ) (hbound : ∀ x, ‖Phi x‖ ≤ M) :
    (∫ wv, Phi (nextInvocationObservation rate rewards C_star C_h u t control0 wv.1,
      (wv.2, currentRemainder t wv.1.1.val)) ∂nonrenewedLiftLaw rate rewards C_star C_h u t control0) =
    ∫ sr, ∫ v, Phi (sr.1.1, (v, sr.2)) ∂signatureVectorKernel rate u t sr.1
      ∂((nonrenewedBaseLaw rate rewards C_star C_h u t).map
        (signature rate rewards C_star C_h u t control0)).prod
        ((LaunchAssignmentCoordinateSplit.nonAssignmentScalarLaw p).prod (ContinuousLearningRows.affineSamplesLaw p)) := by
  let k : ProbabilityTheory.Kernel (SignatureValue rate u t × Remainder p) (AssignmentVector p) :=
    (signatureVectorKernel rate u t).comap
    (Prod.fst : SignatureValue rate u t × Remainder p → SignatureValue rate u t) measurable_fst
  let F : (SignatureValue rate u t × Remainder p) × AssignmentVector p → ℝ :=
    fun w => Phi (w.1.1.1, (w.2, w.1.2))
  have hF : Measurable F := hPhi.comp
    (measurable_fst.fst.fst.prodMk (measurable_snd.prodMk measurable_fst.snd))
  let g : SignatureValue rate u t × Remainder p → ℝ := fun sr => ∫ v, F (sr, v) ∂k sr
  have hg : Measurable g := (hF.stronglyMeasurable.integral_kernel_prod_right' (κ := k)).measurable
  have hmap : Measurable (fun w : EventSource rate rewards C_star C_h u t ×
      ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p =>
      (signature rate rewards C_star C_h u t control0 w, currentRemainder t w.1.val)) :=
    (measurable_signature rate rewards C_star C_h u t control0).prodMk
      ((measurable_currentRemainder t).comp (measurable_subtype_coe.comp measurable_fst))
  let test := fun wv : (EventSource rate rewards C_star C_h u t ×
      ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p) × AssignmentVector p =>
    Phi (nextInvocationObservation rate rewards C_star C_h u t control0 wv.1,
      (wv.2, currentRemainder t wv.1.1.val))
  have htest : Measurable test := hPhi.comp
    (((measurable_nextInvocationObservation rate rewards C_star C_h u t control0).comp measurable_fst).prodMk
      (measurable_snd.prodMk ((measurable_currentRemainder t).comp
        (measurable_subtype_coe.comp measurable_fst.fst))))
  have hint : Integrable test (nonrenewedLiftLaw rate rewards C_star C_h u t control0) :=
    (integrable_const M).mono' htest.aestronglyMeasurable (Filter.Eventually.of_forall (fun wv => hbound _))
  calc
    _ = ∫ w, ∫ v, test (w, v) ∂nonrenewedVectorKernel rate rewards C_star C_h u t control0 w
        ∂nonrenewedBaseLaw rate rewards C_star C_h u t := Measure.integral_compProd hint
    _ = ∫ w, g (signature rate rewards C_star C_h u t control0 w, currentRemainder t w.1.val)
        ∂nonrenewedBaseLaw rate rewards C_star C_h u t := rfl
    _ = ∫ sr, g sr ∂(nonrenewedBaseLaw rate rewards C_star C_h u t).map
        (fun w => (signature rate rewards C_star C_h u t control0 w, currentRemainder t w.1.val)) :=
      (integral_map hmap.aemeasurable hg.aestronglyMeasurable).symm
    _ = _ := by rw [signature_currentRemainder_product]; rfl

/-- The retained first-event history is literally before the invocation's
killing test. Attaching the new draw does not normalize any killed mass. -/
public theorem event_noCallBefore (z : EventSource rate rewards C_star C_h u t) :
    NoCallBefore rate rewards C_star C_h t.castSucc z.val := by
  obtain ⟨theta, n, r, hfirst, _⟩ := firstLiveCollectionEvent_firstCall rate rewards C_star C_h u t z.val z.property
  intro q hq
  rw [noCallAt_iff_callAt_none]
  apply (ReferenceFirstCollectionPrecallCalendarSupport.before_cut_iff_no_call_through
    rate rewards C_star C_h q z.val).mp (by
      simpa only [ReferenceFirstCollectionPrecallCalendarSupport.firstCallBoundary, hfirst, Fin.val_castSucc] using hq) q le_rfl

/-- Reuse the accepted renewal pair itself. Causality attaches the SAME
complete old list and original label-zero array; its renewal scalar is
already consumed by the accepted pair construction. -/
public theorem renewal_pair_oldObservation (control0 : ContinuousLearningRows.TimeControl p)
    (wv : ReferenceFirstCollectionRenewalInstallationCoupling.RenewalLift rate rewards C_star C_h u t) :
    obs control0 t.castSucc ((ReferenceFirstCollectionRenewalInstallationCoupling.pair rate rewards C_star C_h u t wv).2.val, wv.1.2) =
      obs control0 t.castSucc (wv.1.1.val, wv.1.2) := by
  change obs control0 t.castSucc
    ((ReferenceFirstCollectionRenewalVectorInsertion.put rate rewards C_star C_h u t wv.1.1 wv.2).val, wv.1.2) = _
  rw [ReferenceFirstCollectionRenewalVectorInsertion.put_val]
  exact nextInvocationPrefix_insertVector rate rewards C_star C_h t control0 wv.1.1.val wv.1.2 wv.2

public theorem renewal_pair_marginals :
    (ReferenceFirstCollectionRenewalInstallationCoupling.pairLaw rate rewards C_star C_h u t).map Prod.fst =
      ReferenceFirstCollectionRenewalFibreExtension.renewalBaseLaw rate rewards C_star C_h u t ∧
    (ReferenceFirstCollectionRenewalInstallationCoupling.pairLaw rate rewards C_star C_h u t).map (fun b => b.2.val) =
      (BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
        (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent rate rewards C_star C_h u t) :=
  ⟨ReferenceFirstCollectionRenewalInstallationCoupling.pairLaw_map_fst rate rewards C_star C_h u t,
    ReferenceFirstCollectionRenewalInstallationCoupling.pairLaw_map_value rate rewards C_star C_h u t⟩

/-- Total physical insertion: a terminal boundary has no `Fin T` coordinate;
absence of either an actual call or its candidate leaves the source intact. -/
public def invocationInsertion (n : Fin (p.T + 1))
    (z : BootstrapPrivateRoundStreams.SourceInput p) (candidate : Option (AssignmentVector p)) :
    BootstrapPrivateRoundStreams.SourceInput p :=
  if hn : n.val < p.T then
    match ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h ⟨n.val, hn⟩ z, candidate with
    | some _, some v => insertedSource ⟨n.val, hn⟩ z v
    | _, _ => z
  else z

public theorem invocationInsertion_terminal (z : BootstrapPrivateRoundStreams.SourceInput p)
    (v : Option (AssignmentVector p)) :
    invocationInsertion rate rewards C_star C_h (Fin.last p.T) z v = z := by
  simp only [invocationInsertion, Fin.val_last, lt_self_iff_false, dite_false]

public theorem invocationInsertion_absent (n : Fin (p.T + 1)) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    invocationInsertion rate rewards C_star C_h n z none = z := by
  unfold invocationInsertion
  split
  · rename_i hn
    cases ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h ⟨n.val, hn⟩ z <;> rfl
  · rfl

public theorem invocationInsertion_noCall (z : BootstrapPrivateRoundStreams.SourceInput p)
    (v : Option (AssignmentVector p))
    (hcall : ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h t z = none) :
    invocationInsertion rate rewards C_star C_h t.castSucc z v = z := by
  simp only [invocationInsertion, Fin.val_castSucc, t.isLt, dite_true, hcall]

/-- On the actual event the total Option construction is precisely the
same whole-vector insertion used by the fibre lift. -/
public theorem invocationInsertion_event (z : EventSource rate rewards C_star C_h u t)
    (v : AssignmentVector p) :
    invocationInsertion rate rewards C_star C_h t.castSucc z.val (some v) = insertedSource t z.val v := by
  obtain ⟨e, b, r, cutoff, theta, call, hc, hr, hcall, _⟩ :=
    nonrenewedEndpointFibre rate rewards C_star C_h u t z
  simp only [invocationInsertion, Fin.val_castSucc, t.isLt, dite_true, hcall]

end Bandits.Support.ReferenceFirstNextInvocationJointLift

end
