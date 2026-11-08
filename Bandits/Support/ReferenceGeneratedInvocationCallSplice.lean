/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceNextInsertedSourceMarginal
public import Bandits.Support.ReferenceRankInstallationSourceKernelComposition

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
# Native next-invocation cells on the produced insertion sample

Sources: ZIP4 `06_interruptions.tex:391-426`,
`04_slow_fast_learner.tex:142-215,323-390`, and
`08_main_theorem.tex:78-109`.

The native cell below is extracted from the actual invocation at its original
calendar date and its source-derived rank. It uses the existing logical cell
and queue machine. The subsequent splice retains the entire previous observer.
This is the first-root next-call base, not arbitrary-rank generated-history
recurrence or an all-calendar logical-law or regret theorem.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ContinuousControlSlice (scalarLaw)
open scoped ENNReal Classical
open Bandits.Support ConstructorDimensions
open ReferenceFirstLiveChronologicalPrefixFoundation
open ReferenceFirstLiveCalendarMarkedTransition
open ReferenceFirstNextInstallationTransitionLaw
open ReferenceFirstNextInstallationCellFactors
open ReferencePostInvocationNoncallGeometry
open ReferencePostInvocationPrefixLocality
open ReferencePostInvocationSupportedDisintegration
open ReferencePostInvocationKilledJointLaw
open ReferenceNextRetainedEndpointFibreLaw
open ReferenceFirstLiveActualRefreshTestLaw (auxiliarySection scalarZero)

namespace Bandits.Support.ReferenceGeneratedInvocationCallSplice

variable {p : ConstructorDimensions.Parameters}

abbrev Source := BootstrapPrivateRoundStreams.SourceInput
abbrev Vector := AssignmentParameterFibreKernel.AssignmentVector
abbrev Scalar := ContinuousControlSlice.Scalar
abbrev Auxiliary := ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray

local instance sourceMeasurableSpace : MeasurableSpace (Source p) := by
  change MeasurableSpace (CompletePublicTable.PublishedOutput p ×
    BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

local instance controlMeasurableSpace : MeasurableSpace (ContinuousLearningRows.TimeControl p) :=
  ReferencePostInvocationSupportedDisintegration.controlMeasurableSpace

local instance optionMeasurableSpace {X : Type*} [MeasurableSpace X] :
    MeasurableSpace (Option X) := LaterAssignmentStartMeasurability.optionMeasurableSpace

local instance slowSetMeasurableSpace : MeasurableSpace (SlowSet p) := ⊤
local instance slowSetDiscrete : DiscreteMeasurableSpace (SlowSet p) := ⟨fun _ => trivial⟩

variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)

/-- The rank counts actual selectors strictly before this date, on this same
source. Failed subsequent draws still count as invocations. -/
def nativeRank (t : Fin p.T) (z : Source p) : ℕ :=
  ReferenceCollectionSamplerChronology.priorCallCount rate rewards C_star C_h t z

/-- Only the actual selector's presence is required. No numerical alignment,
sampler success, generated list or logical-law premise is supplied. -/
abbrev InvocationSource (t : Fin p.T) :=
  {z : Source p //
    (ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h t z).isSome = true}

theorem native_installation (t : Fin p.T)
    (z : InvocationSource rate rewards C_star C_h t) :
    z.val ∈ ReferenceRankInstallationRecorderFoundation.installationEvent
      rate rewards C_star C_h (nativeRank rate rewards C_star C_h t z.val) t := by
  obtain ⟨⟨u, theta⟩, hc⟩ := Option.isSome_iff_exists.mp z.property
  apply Set.mem_iUnion.mpr
  refine ⟨u, ?_⟩
  change (ReferenceCollectionSamplerChronology.nthAt rate rewards C_star C_h
    (nativeRank rate rewards C_star C_h t z.val) t z.val).map Prod.fst = some u
  unfold nativeRank
  rw [(ReferenceCollectionSamplerChronology.nthAt_eq_some_iff
    rate rewards C_star C_h _ t z.val u theta).mpr ⟨rfl, hc⟩]
  rfl

section NativeCell

variable (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T)

local notation "Z" => InvocationSource rate rewards C_star C_h t
local notation "records" z =>
  ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
local notation "recordAt" => ReferenceSourcePrefixHistoryFiltration.actualRecord
  rate rewards C_star C_h t
local notation "beforeAt" =>
  ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationNumericalBefore
    rate rewards C_star C_h control0 t

/-- The index is supplied by the accepted recorder on the actual native rank. -/
public def nativeRecordIndex (z : Z) : Fin (records z.val).length :=
  (ReferenceRankInstallationRecorderFoundation.installationEvent_recordingData
    rate rewards C_star C_h (nativeRank rate rewards C_star C_h t z.val) t z.val
      (native_installation rate rewards C_star C_h t z)).choose

public def nativeRecord (z : Z) : ReferenceFirstLiveChronologicalPrefixFoundation.Record rate :=
  (records z.val)[(nativeRecordIndex rate rewards C_star C_h t z).val]

/-- The native cell extracted from the actual dispatcher result. -/
public def nativeSourceCell (z : Z) : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell (nativeRecord rate rewards C_star C_h t z) :=
  (ReferenceRankInstallationRecorderFoundation.installationEvent_recordingData
    rate rewards C_star C_h (nativeRank rate rewards C_star C_h t z.val) t z.val
      (native_installation rate rewards C_star C_h t z)).choose_spec.choose

public theorem nativeSourceCell_spec (z : Z) :
    recordAt z.val = some (nativeRecord rate rewards C_star C_h t z) ∧
    (nativeRecord rate rewards C_star C_h t z).input.time = t ∧
    ReferenceLaterLiveNumericalReadout.laterLiveReadout 0
      (nativeRecord rate rewards C_star C_h t z) =
      some (nativeSourceCell rate rewards C_star C_h t z).input := by
  have h := (ReferenceRankInstallationRecorderFoundation.installationEvent_recordingData
    rate rewards C_star C_h (nativeRank rate rewards C_star C_h t z.val) t z.val
      (native_installation rate rewards C_star C_h t z)).choose_spec.choose_spec
  exact ⟨h.1, h.2.1, h.2.2.2.2.2.2.1⟩

/-- The PRE state extracted from the proved actual strict-past readout. -/
public def nativeBefore (z : Z) : RecordedQueueRun.RunState p.K :=
  (ReferenceRankInstallationPostUpdateProposalLaw.installationEvent_numericalUpdate_eq_step
    rate rewards C_star C_h control0 (nativeRank rate rewards C_star C_h t z.val) t z.val
      (native_installation rate rewards C_star C_h t z)).choose

public theorem nativeBefore_spec (z : Z) : beforeAt z.val = some
      ((nativeBefore rate rewards C_star C_h control0 t z).registers,
        (nativeBefore rate rewards C_star C_h control0 t z).overflow,
        (nativeBefore rate rewards C_star C_h control0 t z).records) :=
  (ReferenceRankInstallationPostUpdateProposalLaw.installationEvent_numericalUpdate_eq_step
    rate rewards C_star C_h control0 (nativeRank rate rewards C_star C_h t z.val) t z.val
      (native_installation rate rewards C_star C_h t z)).choose_spec.choose_spec.2.1

/-- The actual cell, with label 1 for nonrenewal or label 0 for renewal refresh. -/
public def nativeCell (z : Z) (x : ContinuousControlSlice.Scalar) : LogicalCell p rate :=
  let r := nativeRecord rate rewards C_star C_h t z
  appendLogicalCell r (nativeSourceCell rate rewards C_star C_h t z)
    (nativeBefore rate rewards C_star C_h control0 t z)
    (Function.update auxiliarySection (r.input.time, 1) x)

public theorem nativeCell_time (z : Z) (x : ContinuousControlSlice.Scalar) :
    (nativeCell rate rewards C_star C_h control0 t z x).time = t :=
  (nativeSourceCell_spec rate rewards C_star C_h t z).2.1

public theorem nativeCell_before (z : Z) (x : ContinuousControlSlice.Scalar) :
    beforeAt z.val = some
      ((nativeCell rate rewards C_star C_h control0 t z x).before.registers,
        (nativeCell rate rewards C_star C_h control0 t z x).before.overflow,
        (nativeCell rate rewards C_star C_h control0 t z x).before.records) :=
  nativeBefore_spec rate rewards C_star C_h control0 t z

public theorem nativeCell_numerical (z : Z) (x : ContinuousControlSlice.Scalar) :
    (ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualCell
      rate rewards C_star C_h t z.val).map
        ReferenceLaterLiveReadoutValuesMeasurability.numericalCoordinates =
      some (nativeCell rate rewards C_star C_h control0 t z x).numerical := by
  have h := nativeSourceCell_spec rate rewards C_star C_h t z
  change ((recordAt z.val).bind (ReferenceLaterLiveNumericalReadout.laterLiveReadout 0)).map _ = _
  rw [h.1]
  change (ReferenceLaterLiveNumericalReadout.laterLiveReadout 0
    (nativeRecord rate rewards C_star C_h t z)).map _ = _
  rw [h.2.2]
  rfl

/-- The produced cell performs the actual whole-arm numerical update,
including service on zero-arrival arms and the first overflow-detecting step.
The raw vector remains distinct from the accepted/frozen arrivals. -/
public theorem nativeCell_wholeUpdate (z : Z) (x : Scalar) :
    ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationNumericalUpdate
      rate rewards C_star C_h control0 t z.val =
      some (show ReferenceFirstLivePostUpdateProposalLaw.NumericalUpdateFields p from
        { raw := RecordedQueueRun.quantizedArrival
            (ReferenceFirstLaunchNumericalCell.queueParameters rate)
            (nativeSourceCell rate rewards C_star C_h t z).input
          beforeRegisters := (nativeCell rate rewards C_star C_h control0 t z x).before.registers
          beforeOverflow := (nativeCell rate rewards C_star C_h control0 t z x).before.overflow
          beforeRecords := (nativeCell rate rewards C_star C_h control0 t z x).before.records
          accepted := (nativeCell rate rewards C_star C_h control0 t z x).arrivals
          service := (nativeCell rate rewards C_star C_h control0 t z x).service
          afterRegisters := (nativeCell rate rewards C_star C_h control0 t z x).after.registers
          afterOverflow := (nativeCell rate rewards C_star C_h control0 t z x).after.overflow
          afterRecords := (nativeCell rate rewards C_star C_h control0 t z x).after.records }) := by
  have hraw : ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationRawArrivals
      rate rewards C_star C_h t z.val =
      some (RecordedQueueRun.quantizedArrival
        (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        (nativeSourceCell rate rewards C_star C_h t z).input) := by
    simp only [ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationRawArrivals,
      ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationRawCoordinates,
      (nativeSourceCell_spec rate rewards C_star C_h t z).1, Option.bind_some,
      (nativeSourceCell_spec rate rewards C_star C_h t z).2.2, Option.map_some]
    rfl
  rw [ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationNumericalUpdate,
    nativeBefore_spec rate rewards C_star C_h control0 t z, hraw]
  exact congrArg some (ReferenceFirstLivePostUpdateProposalLaw.numericalUpdateFields_eq_step
    rate (nativeBefore rate rewards C_star C_h control0 t z)
    (nativeSourceCell rate rewards C_star C_h t z).input
    (nativeSourceCell rate rewards C_star C_h t z).enabled)

include control0 in
public theorem nativeCell_view (z : Z) :
    ReferenceRankInstallationRecorderFoundation.actualInstallationView
      rate rewards C_star C_h t z.val =
      some (nativeSourceCell rate rewards C_star C_h t z).selected.view := by
  rw [ReferenceRankInstallationPostUpdateProposalLaw.installationEvent_actualView_dispatchProjection
    rate rewards C_star C_h control0 (nativeRank rate rewards C_star C_h t z.val) t z.val
      (native_installation rate rewards C_star C_h t z),
    (nativeSourceCell_spec rate rewards C_star C_h t z).1]
  change (ReferenceActivePhysicalStep.dispatch
    (nativeRecord rate rewards C_star C_h t z).input).downView = _
  have hprep : (nativeRecord rate rewards C_star C_h t z).output.preparation.coordinator =
      ReferenceActivePhysicalStep.dispatch (nativeRecord rate rewards C_star C_h t z).input := by
    rw [(nativeRecord rate rewards C_star C_h t z).output_eq]
    rfl
  rw [← hprep, ReferenceActivePhysicalStep.DispatchCut.downView,
    (nativeSourceCell rate rewards C_star C_h t z).selection_actual]
  rfl

/-- The produced cell's all-arm update is the deterministic readout of the
actual correlated recorder/FAST pair, at its own actual PRE state. This is a
pointwise identity, not a hidden-past conditional kernel assertion. -/
public theorem nativeCell_updateFromPair (z : Z) (x : Scalar) :
    ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationNumericalUpdate
      rate rewards C_star C_h control0 t z.val =
      ReferenceRankInstallationCommonUpdateJointLaw.updateFromPair rate rewards t
        (nativeSourceCell rate rewards C_star C_h t z).selected.view
        (some ((nativeCell rate rewards C_star C_h control0 t z x).before.registers,
          (nativeCell rate rewards C_star C_h control0 t z x).before.overflow,
          (nativeCell rate rewards C_star C_h control0 t z x).before.records))
        (ReferenceRankInstallationRecorderFastLaw.actualMarkerReservedFast
          rate rewards C_star C_h t z.val) := by
  rw [← nativeCell_before rate rewards C_star C_h control0 t z x]
  exact ReferenceRankInstallationCommonUpdateJointLaw.actualInstallationNumericalUpdate_eq_updateFromPair
    rate rewards C_star C_h control0 (nativeRank rate rewards C_star C_h t z.val) t z.val
      (native_installation rate rewards C_star C_h t z) _
      (nativeCell_view rate rewards C_star C_h control0 t z)

public theorem nativeRecord_control (z : Z) : CompletePublicTable.completeRowLearning p
      (nativeRecord rate rewards C_star C_h t z).input.row
      (nativeRecord rate rewards C_star C_h t z).input.time =
      ReferenceSourceCurrentControlFreshness.u_t p t z.val := by
  have h := ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields
    rate rewards C_star C_h t z.val (nativeRecord rate rewards C_star C_h t z)
    (nativeSourceCell_spec rate rewards C_star C_h t z).1
  change ((nativeRecord rate rewards C_star C_h t z).input.rows
    (nativeRecord rate rewards C_star C_h t z).input.selected).2
      (nativeRecord rate rewards C_star C_h t z).input.time = _
  rw [h.1, h.2.1, h.2.2.1]
  rfl

/-- The produced cell's proposal is the actual physical LIVE bit, gated by
PRE overflow. POST overflow does not suppress this detecting proposal. -/
public theorem nativeCell_proposal (z : Z) (x : Scalar) :
    (nativeCell rate rewards C_star C_h control0 t z x).proposal =
      (!(nativeCell rate rewards C_star C_h control0 t z x).before.overflow &&
        ReferenceFirstLivePostUpdateProposalLaw.physicalProposalBit rate
          (ReferenceSourceCurrentControlFreshness.u_t p t z.val)) := by
  change (!((nativeBefore rate rewards C_star C_h control0 t z).overflow) &&
    FollowerCutoffScan.completeRowProposalBit p rate.eta.val
      (nativeRecord rate rewards C_star C_h t z).input.row
      (nativeRecord rate rewards C_star C_h t z).input.time) = _
  rw [ReferenceFirstLivePostUpdateProposalLaw.completeRowProposalBit_eq_physicalProposalBit
    rate _ _ _ rfl, nativeRecord_control rate rewards C_star C_h t z]
  rfl

include control0 in
public theorem nativeSourceCell_fast (z : Z) :
    ReferenceRankInstallationRecorderFastLaw.actualReservedFast rate rewards C_star C_h t z.val =
      some (reservedFastArm (nativeRecord rate rewards C_star C_h t z)
        (nativeSourceCell rate rewards C_star C_h t z)).val := by
  let native := nativeSourceCell rate rewards C_star C_h t z
  have ht := (nativeSourceCell_spec rate rewards C_star C_h t z).2.1
  have valid : CoordinatorLocalArmChoice.ChoiceInputsValid native.selected.view.payload
      native.selected.view.cutoff t native.selected.view.complementWeights := by
    simpa only [ht] using native.choiceInputsValid
  rw [ReferenceRankInstallationRecorderFastLaw.actualReservedFast_eq_of_view
    rate rewards C_star C_h t z.val native.selected.view
      (nativeCell_view rate rewards C_star C_h control0 t z) valid]
  unfold reservedFastArm ReferenceRankInstallationRecorderFastLaw.reservedFastAtView
  have hc := nativeRecord_control rate rewards C_star C_h t z
  change CompletePublicTable.completeRowLearning p _ _ = _ at hc
  rw [← hc]
  rfl

section ActualCellBorel

local instance actualSlowSetMeasurableSpace : MeasurableSpace (SlowSet p) := ⊤
local instance actualSlowSetDiscreteMeasurableSpace : DiscreteMeasurableSpace (SlowSet p) :=
  ⟨fun _ => trivial⟩

private theorem measurable_of_some {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]
    (f : X → A) (hf : Measurable (fun x => some (f x))) : Measurable f := by
  have he : Measurable (Equiv.optionEquivSumPUnit A) := comap_measurable _
  have hinl : MeasurableEmbedding (@Sum.inl A PUnit) :=
    ⟨Sum.inl_injective, measurable_inl, fun _ hs => hs.inl_image⟩
  exact hinl.measurable_comp_iff.mp (he.comp hf)

attribute [local instance] ReferenceRankInstallationPostUpdateProposalLaw.sumMeasurableSingleton
  ReferenceRankInstallationPostUpdateProposalLaw.listMeasurableSingleton

private theorem measurable_nativePhysical : Measurable (fun z : Z =>
    ReferenceActiveHorizonMeasurability.roundRecordCode
      (nativeRecord rate rewards C_star C_h t z)) := by
  apply measurable_of_some
  have h := (ReferenceCalendarActualControlCallbackSections.measurable_codeAt
    rate rewards C_star C_h t).comp (measurable_subtype_coe (p := fun z =>
      (ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h t z).isSome = true))
  convert h using 1
  funext z
  simp only [Function.comp_apply, ReferenceCalendarActualControlCallbackSections.codeAt,
    (nativeSourceCell_spec rate rewards C_star C_h t z).1, Option.map_some]

include control0 in
private theorem measurable_nativeNumerical : Measurable (fun z : Z =>
    ReferenceLaterLiveReadoutValuesMeasurability.numericalCoordinates
      (nativeSourceCell rate rewards C_star C_h t z).input) := by
  apply measurable_of_some
  have h := (ReferenceOriginalCalendarContinuingLiveRecorderLaw.measurable_actualNumerical
    rate rewards C_star C_h t).comp (measurable_subtype_coe (p := fun z =>
      (ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h t z).isSome = true))
  convert h using 1
  funext z
  exact (nativeCell_numerical rate rewards C_star C_h control0 t z scalarZero).symm

private theorem measurable_nativeBefore :
    Measurable (nativeBefore rate rewards C_star C_h control0 t) := by
  have hc : Measurable (fun z : Z =>
      ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
        (nativeBefore rate rewards C_star C_h control0 t z)) := by
    apply measurable_of_some
    have h := (ReferenceRankInstallationPostUpdateProposalLaw.measurable_actualInstallationNumericalBefore
      rate rewards C_star C_h control0 t).comp (measurable_subtype_coe (p := fun z =>
        (ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h t z).isSome = true))
    convert h using 1
    funext z
    exact (nativeBefore_spec rate rewards C_star C_h control0 t z).symm
  exact (measurable_of_countable (fun b :
    ReferenceRankInstallationPostUpdateProposalLaw.NumericalState p =>
      (⟨b.1, b.2.1, b.2.2⟩ : RecordedQueueRun.RunState p.K))).comp hc

include control0 in
private theorem measurable_nativeView : Measurable (fun z : Z =>
    (nativeSourceCell rate rewards C_star C_h t z).selected.view) := by
  apply measurable_of_some
  have h := (ReferenceRankInstallationRecorderFoundation.measurable_actualInstallationView
    rate rewards C_star C_h t).comp (measurable_subtype_coe (p := fun z =>
      (ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h t z).isSome = true))
  convert h using 1
  funext z
  exact (nativeCell_view rate rewards C_star C_h control0 t z).symm

include control0 in
private theorem measurable_nativeAnchor : Measurable (fun z : Z =>
    (nativeSourceCell rate rewards C_star C_h t z).selected.view.payload.anchor) := by
  have hv := (comap_measurable
    (ReferenceDownReceptionMeasurability.choiceTimeViewObservation (p := p) (rate := rate))).comp
      (measurable_nativeView rate rewards C_star C_h control0 t)
  exact AssignmentPayloadDerivedMeasurability.measurable_inputAnchor.comp (measurable_fst.comp hv)

include control0 in
private theorem measurable_nativeSlowSet : Measurable (fun z : Z =>
    (nativeSourceCell rate rewards C_star C_h t z).selected.view.payload.slowSet) := by
  have hv := (comap_measurable
    (ReferenceDownReceptionMeasurability.choiceTimeViewObservation (p := p) (rate := rate))).comp
      (measurable_nativeView rate rewards C_star C_h control0 t)
  have hp := (comap_measurable
    (LaterAssignmentStartMeasurability.payloadObservation (p := p) (eta := rate.eta))).comp
      (measurable_fst.comp hv)
  have hs := measurable_fst.comp (measurable_snd.comp (measurable_snd.comp hp))
  apply measurable_to_countable'
  intro U
  have heq : {z : Z |
      (nativeSourceCell rate rewards C_star C_h t z).selected.view.payload.slowSet = U} =
      {z : Z |
      (nativeSourceCell rate rewards C_star C_h t z).selected.view.payload.slowSet.val = U.val} := by
    ext z
    exact Subtype.ext_iff
  change MeasurableSet {z : Z |
    (nativeSourceCell rate rewards C_star C_h t z).selected.view.payload.slowSet = U}
  rw [heq]
  exact (measurableSet_singleton U.val).preimage hs

include control0 in
private theorem measurable_nativeFast : Measurable (fun z : Z =>
    (reservedFastArm (nativeRecord rate rewards C_star C_h t z)
      (nativeSourceCell rate rewards C_star C_h t z)).val) := by
  apply measurable_to_countable'
  intro j
  have h := (ReferenceRankInstallationRecorderFastLaw.measurable_actualReservedFast
    rate rewards C_star C_h t).comp (measurable_subtype_coe (p := fun z =>
      (ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h t z).isSome = true))
  have hf := (measurableSet_singleton (some j)).preimage h
  convert hf using 1
  ext z
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Function.comp_apply]
  rw [nativeSourceCell_fast rate rewards C_star C_h control0 t z]
  simp only [Option.some.injEq]

/-- Joint Borel measurability in the actual source and its refresh scalar. -/
public theorem measurable_nativeCell : Measurable (fun v : Z × Scalar =>
    nativeCell rate rewards C_star C_h control0 t v.1 v.2) := by
  classical
  let X := Z × Scalar
  let native := fun v : X => nativeSourceCell rate rewards C_star C_h t v.1
  let before := fun v : X => nativeBefore rate rewards C_star C_h control0 t v.1
  let round := fun v : X => (native v).input
  let Q := ReferenceFirstLaunchNumericalCell.queueParameters rate
  have hb : Measurable before :=
    (measurable_nativeBefore rate rewards C_star C_h control0 t).comp measurable_fst
  have hn : Measurable (fun v : X =>
      ReferenceLaterLiveReadoutValuesMeasurability.numericalCoordinates (round v)) :=
    (measurable_nativeNumerical rate rewards C_star C_h control0 t).comp measurable_fst
  have ho : Measurable (fun v : X => (before v).overflow) :=
    (measurable_of_countable (fun S : RecordedQueueRun.RunState p.K => S.overflow)).comp hb
  have hcut := (measurableSet_singleton true).preimage ho
  have ha : Measurable (fun v : X => RecordedQueueRun.acceptedRecord Q (before v) (round v)) := by
    let accepted := fun v : RecordedQueueRun.RunState p.K × (Bool × (Fin p.K → ℕ)) =>
      fun a => if v.1.overflow then (false, 0) else if v.2.1 then (true, v.2.2 a) else (false, 0)
    exact (measurable_of_countable accepted).comp
      (hb.prodMk ((ReferenceLaterCollectionSourceReadoutMeasurability.measurable_arrivalsFromNumerical
        rate).comp hn))
  have hafter : Measurable (fun v : X => RecordedQueueRun.step Q (before v) (round v)) := by
    let update := fun v : RecordedQueueRun.RunState p.K × (Fin p.K → Bool × ℕ) =>
      let registers := fun a => QueueReplay.transition (4 * Q.n) (v.1.registers a) (v.2 a)
      (⟨registers, v.1.overflow || decide (∃ a, 32 * (registers a).2 > Q.D),
        fun a => v.1.records a ++ [v.2 a]⟩ : RecordedQueueRun.RunState p.K)
    exact (measurable_of_countable update).comp (hb.prodMk ha)
  have hservice : Measurable (fun v : X => fun a => RecordedQueueRun.recordService (4 * Q.n)
      ((before v).registers a) (RecordedQueueRun.acceptedRecord Q (before v) (round v) a)) :=
    (measurable_of_countable (fun v : RecordedQueueRun.RunState p.K × (Fin p.K → Bool × ℕ) =>
      fun a => RecordedQueueRun.recordService (4 * Q.n) (v.1.registers a) (v.2 a))).comp (hb.prodMk ha)
  have hs : Measurable (fun v : X => (native v).selected.view.payload.slowSet) :=
    (measurable_nativeSlowSet rate rewards C_star C_h control0 t).comp measurable_fst
  have hslow : Measurable (fun v : X => if (before v).overflow then frozenSlowSet p else
      (native v).selected.view.payload.slowSet) := measurable_const.ite hcut hs
  have hfast : Measurable (fun v : X => if (before v).overflow then frozenFastArm p else
      (reservedFastArm (nativeRecord rate rewards C_star C_h t v.1) (native v)).val) :=
    measurable_const.ite hcut
      ((measurable_nativeFast rate rewards C_star C_h control0 t).comp measurable_fst)
  let proposal := fun v : X => !(before v).overflow &&
    ReferenceFirstLivePostUpdateProposalLaw.physicalProposalBit rate
      (ReferenceSourceCurrentControlFreshness.u_t p t v.1.val)
  have hp : Measurable proposal :=
    (measurable_of_countable (fun b : Bool × Bool => !b.1 && b.2)).comp
      (ho.prodMk ((ReferenceFirstLivePostUpdateProposalLaw.measurable_physicalProposalBit rate).comp
        ((ReferenceSourceCurrentControlFreshness.measurable_u_t t).comp
          (measurable_subtype_coe.comp measurable_fst))))
  have hres := ReferenceFirstLiveChronologicalPrefixMeasurability.measurable_residualDraw_of_actualPrePost
    rate before (fun v => RecordedQueueRun.step Q (before v) (round v)) round hb hafter (fun _ => rfl)
    (fun v => (native v).selected.view.payload.anchor)
    ((measurable_nativeAnchor rate rewards C_star C_h control0 t).comp measurable_fst)
    (fun v => (native v).selected.view.payload.anchor_pos) (fun v => v.2) measurable_snd
  have hnext : Measurable (fun v : X => if (before v).overflow then frozenSlowSet p else
      if proposal v then residualDraw rate (before v) (round v)
        (native v).selected.view.payload.anchor (native v).selected.view.payload.anchor_pos v.2
      else (native v).selected.view.payload.slowSet) :=
    measurable_const.ite hcut (hres.ite ((measurableSet_singleton true).preimage hp) hs)
  have ht : Measurable (fun _ : X => t) := measurable_const
  have hcode := ht.prodMk
    (((measurable_nativePhysical rate rewards C_star C_h t).comp measurable_fst).prodMk
      (hn.prodMk (hb.prodMk (hafter.prodMk (ha.prodMk
        (hservice.prodMk (hslow.prodMk (hfast.prodMk (hp.prodMk hnext)))))))))
  apply measurable_comap_iff.mpr
  convert hcode using 1
  funext v
  dsimp only [Function.comp_def, ReferenceFirstLiveChronologicalPrefixMeasurability.logicalCellProductCode,
    nativeCell, appendLogicalCell]
  rw [ReferenceFirstLivePostUpdateProposalLaw.completeRowProposalBit_eq_physicalProposalBit
    rate _ _ _ rfl, nativeRecord_control rate rewards C_star C_h t v.1]
  simp only [Function.update_self, (nativeSourceCell_spec rate rewards C_star C_h t v.1).2.1]
  rfl

end ActualCellBorel

private theorem successfulStart_parameter_sample {eta : ReferencePrelaunchFollower.LearningRate}
    (old : AssignmentStartPayload.Input p eta) (ledger : LaterAssignmentStartOperation.LocalLedger old)
    (instruction : CoordinatorPhaseClock.AssignmentStartInstruction p)
    (row : CompletePublicTable.CompleteRow p) (consistent : LaterAssignmentStartOperation.LocalConsistency old ledger)
    (output : LaterAssignmentStartOperation.SuccessfulStart old ledger instruction row)
    (hlocal : output.localConsistency = consistent)
    (hresult : LaterAssignmentStartOperation.laterAssignmentStart old ledger instruction row consistent =
      .success output hlocal) :
    (LaterAssignmentStartMeasurability.selectedSamplerParameters? old ⟨ledger, instruction, consistent⟩).bind
      (fun theta => AssignmentParameterFibreKernel.successfulSlowSet p theta
        (LaterAssignmentStartOperation.ownAssignmentVector row instruction.time)) = some output.slowSet := by
  rw [LaterAssignmentJointCodeMeasurability.selectedSamplerParameters?_eq_match]
  cases hd : LaterAssignmentStartOperation.decideReconstruction old ledger instruction with
  | failure reason =>
      simp only [LaterAssignmentStartOperation.laterAssignmentStart, hd,
        LaterAssignmentStartOperation.runReconstructionDecision] at hresult
      cases hresult
  | success out hcall =>
      have hc := LaterAssignmentStartMeasurability.laterAssignmentStartCode_eq_reconstructedFirstCode
        old ⟨ledger, instruction, consistent⟩ row
      simp only [LaterAssignmentStartMeasurability.laterAssignmentStartCode, hresult,
        LaterAssignmentStartMeasurability.codeOfResult,
        LaterAssignmentStartMeasurability.reconstructedFirstCode, hd] at hc
      simp only [Option.bind_some]
      unfold AssignmentParameterFibreKernel.successfulSlowSet
      cases hs : CheckedAssignmentSample.checkedAssignmentSample p
          (LaterAssignmentStartMeasurability.selectedSamplerParameters old ledger instruction out hcall).1
          (LaterAssignmentStartMeasurability.selectedSamplerParameters old ledger instruction out hcall).2
          (LaterAssignmentStartOperation.ownAssignmentVector row instruction.time) with
      | prefixFailure arm reason =>
          simp only [hs, LaterAssignmentStartMeasurability.codeOfCheckedSample] at hc
          cases hc
      | orientationFailure set =>
          simp only [hs, LaterAssignmentStartMeasurability.codeOfCheckedSample] at hc
          cases hc
      | sampled outcome =>
          simp only [hs, LaterAssignmentStartMeasurability.codeOfCheckedSample,
            LaterAssignmentStartMeasurability.LaterAssignmentStartCode.sampled.injEq] at hc
          subst outcome
          exact congrArg some output.slowSet_eq_erasure.symm

include control0 in
/-- The actual installation payload is the outcome of the original whole
assignment sampler. No success, selected-set or numerical agreement input is
supplied: the actual invocation produces all the dispatch witnesses. -/
public theorem nativeCell_sampler (z : Z) :
    (ReferenceCalendarLaterSamplerPredictability.calendarParameters rate rewards C_star C_h t z.val).bind
      (fun theta => AssignmentParameterFibreKernel.successfulSlowSet p theta
        (ReferenceFirstCollectionSamplerOutputLaw.currentAssignmentVector t z.val)) =
      some (nativeSourceCell rate rewards C_star C_h t z).selected.view.payload.slowSet := by
  let b := nativeRecordIndex rate rewards C_star C_h t z
  let r := (records z.val)[b.val]
  have hdata := (ReferenceRankInstallationRecorderFoundation.installationEvent_recordingData
    rate rewards C_star C_h (nativeRank rate rewards C_star C_h t z.val) t z.val
      (native_installation rate rewards C_star C_h t z)).choose_spec.choose_spec
  have hchosen : ReferenceCollectionPhaseHistory.laterChosen r.input = true := hdata.2.2.1
  obtain ⟨P, l, saved, hstate, hempty⟩ := ReferenceCollectionPhaseHistory.laterChosen_pending_empty
    r.input hchosen
  have hstep := ReferenceCompleteEmptyInstallationNumericalStep.complete_empty_installation_current_numerical_step
    rate rewards C_star C_h z.val b
  dsimp only at hstep
  dsimp only [r] at hstate
  rw [hstate] at hstep
  obtain ⟨u, hu, core, started, hstart, instruction, hassignment, htime, hkind,
    consistent, output, hlocal, hresult, clockData, installed, arm, hinstall,
    hstarted, hdispatch, hprepared, hpayload, htail⟩ := hstep hempty
  change instruction.time = r.input.time at htime
  have hprep : r.output.preparation.coordinator = ReferenceActivePhysicalStep.dispatch r.input := by
    rw [r.output_eq]; rfl
  have hv := nativeCell_view rate rewards C_star C_h control0 t z
  rw [ReferenceRankInstallationPostUpdateProposalLaw.installationEvent_actualView_dispatchProjection
    rate rewards C_star C_h control0 (nativeRank rate rewards C_star C_h t z.val) t z.val
      (native_installation rate rewards C_star C_h t z),
    (nativeSourceCell_spec rate rewards C_star C_h t z).1] at hv
  change (ReferenceActivePhysicalStep.dispatch r.input).downView = _ at hv
  rw [← hprep, hprepared] at hv
  simp only [ReferenceActivePhysicalStep.DispatchCut.downView, ReferenceActivePhysicalStep.DispatchCut.selection,
    ReferenceActivePhysicalStep.selectionAt, dite_eq_left htime, Option.map_some] at hv
  have hvslow := congrArg (fun v : ReferenceDownReception.ChoiceTimeView p rate.eta => v.payload.slowSet)
    (Option.some.inj hv)
  have hscalar := nativeRecord_control rate rewards C_star C_h t z
  have hvector : ReferenceFirstCollectionSamplerOutputLaw.currentAssignmentVector t z.val =
      LaterAssignmentStartOperation.ownAssignmentVector r.input.row instruction.time := by
    rw [htime]
    exact congrArg (fun c : ContinuousLearningRows.TimeControl p =>
      ContinuousControlSlice.assignmentVector c.1) hscalar.symm
  rw [ReferenceCalendarLaterSamplerPredictability.calendarParameters,
    (nativeSourceCell_spec rate rewards C_star C_h t z).1, Option.bind_some]
  change (ReferenceLaterAssignmentFibreStep.parameters? r.input).bind _ = _
  rw [ReferenceLaterAssignmentFibreStep.parameters?_eq_physicalDispatch, ← hprep, hprepared]
  change (LaterAssignmentStartMeasurability.selectedSamplerParameters? P
    ⟨_, instruction, consistent⟩).bind _ = _
  rw [hvector]
  exact (successfulStart_parameter_sample P _ instruction r.input.row consistent output hlocal hresult).trans
    (congrArg some (output.payload_slowSet.symm.trans
      ((congrArg AssignmentStartPayload.Input.slowSet hpayload).symm.trans hvslow)))



/-- The native PRE is exactly the complete calendar PRE on its own source. -/
theorem nativeBefore_prefix (z : Z) :
    prefixNumerical rate rewards C_star C_h t.castSucc z.val =
      some (nativeBefore rate rewards C_star C_h control0 t z) := by
  let read := @ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout p.K
  let decode := fun b : ReferenceRankInstallationPostUpdateProposalLaw.NumericalState p =>
    (⟨b.1, b.2.1, b.2.2⟩ : RecordedQueueRun.RunState p.K)
  have hdecode (S : RecordedQueueRun.RunState p.K) : decode (read S) = S := by
    cases S
    rfl
  have h := nativeBefore_spec rate rewards C_star C_h control0 t z
  change beforeAt z.val = some (read (nativeBefore rate rewards C_star C_h control0 t z)) at h
  rw [ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationNumericalBefore_eq_original,
    ReferenceFirstCollectionCurrentRetainedGate.prefixReadout?,
    ← ReferenceFirstCollectionCorrectedFutureRetainedMoment.prefixInputs_eq_pastCells] at h
  have hd := congrArg (Option.map decode) h
  simp only [Option.map_map, Option.map_some, Function.comp_def, hdecode] at hd
  exact hd

/-- The actual source word appends precisely this native enabled input. This
retains the first detecting update even if its POST state has overflowed. -/
theorem nativeCell_after_prefix (z : Z) (x : Scalar) :
    prefixNumerical rate rewards C_star C_h t.succ z.val =
      some (nativeCell rate rewards C_star C_h control0 t z x).after := by
  have hb := nativeBefore_prefix rate rewards C_star C_h control0 t z
  obtain ⟨L, hL, hrun⟩ := Option.map_eq_some_iff.mp hb
  have hs := nativeSourceCell_spec rate rewards C_star C_h t z
  obtain ⟨k, hk, hr, _hstart⟩ :=
    ReferencePostInvocationGeneratedAlignment.actualRecord_index
      rate rewards C_star C_h t z.val _ hs.1
  have hlookup : (records z.val)[t.val -
      ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h]? =
        some (nativeRecord rate rewards C_star C_h t z) := by
    rw [← hk, List.getElem?_eq_getElem k.isLt, hr]
  have hc : ReferenceFirstCollectionCurrentRetainedGate.cell0 rate
      (nativeRecord rate rewards C_star C_h t z) =
        some (nativeSourceCell rate rewards C_star C_h t z).input := by
    rw [ReferenceFirstCollectionCurrentRetainedGate.cell0, hs.2.2, Option.some_or]
  have hn := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs_append_one
    rate rewards C_star C_h t.val z.val L hL _ _ hlookup hc
  change (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
    rate rewards C_star C_h (t.val + 1) z.val).map _ = _
  rw [hn, Option.map_some, RecordedSlowRefresh.run_append_singleton, hrun]
  rfl

include control0 in
/-- A selector supplies its own parameter, so the selected logical set is
identified from the actual full-vector sampler, without an assumed match. -/
theorem nativeCell_selected (z : Z) (u : Fin p.T)
    (theta : AssignmentParameterFibreKernel.Theta p)
    (hc : ReferenceCalendarCollectionCallControlLaw.callAt
      rate rewards C_star C_h t z.val = some (u, theta)) :
    AssignmentParameterFibreKernel.successfulSlowSet p theta
      (ReferenceFirstCollectionRenewalVectorInsertion.av t z.val) =
        some (nativeSourceCell rate rewards C_star C_h t z).selected.view.payload.slowSet := by
  obtain ⟨r, hr, hcall⟩ := Option.bind_eq_some_iff.mp hc
  obtain ⟨_payload, _ledger, _saved, _hcoord, _hcut, hparam⟩ :=
    (ReferenceFirstCollectionSamplerCall.collectionCallAt_spec r u theta).mp hcall
  have hp : ReferenceCalendarLaterSamplerPredictability.calendarParameters
      rate rewards C_star C_h t z.val = some theta := by
    rw [ReferenceCalendarLaterSamplerPredictability.calendarParameters, hr, Option.bind_some]
    exact hparam
  have h := nativeCell_sampler rate rewards C_star C_h control0 t z
  rw [hp, Option.bind_some] at h
  exact h

end NativeCell

section Splice

variable (control0 : ContinuousLearningRows.TimeControl p) (b : Bool) (u t q : Fin p.T)

/-- The unchanged domain of the accepted insertion law. -/
abbrev Sample := BranchLift rate rewards C_star C_h b u t × (Vector p × Source p)

local notation "X" => Sample rate rewards C_star C_h b u t
local notation "O" => branchObservation rate rewards C_star C_h control0 b u t q.castSucc
local notation "mu" => ReferenceNextInsertedSourceMarginal.nextInsertedLaw
  rate rewards C_star C_h control0 b u t q

private theorem measurable_isSome {A : Type*} [MeasurableSpace A] :
    Measurable (Option.isSome : Option A → Bool) := by
  convert ((measurable_const : Measurable (fun _ : A => true)).sumElim
    (measurable_const : Measurable (fun _ : PUnit => false))).comp
      (comap_measurable (Equiv.optionEquivSumPUnit A)) using 1
  funext o
  cases o <;> rfl

/-- The exceptional component is kept explicitly. Presence tests are literal
observations; their almost-everywhere coverage is proved below. -/
def activeSet : Set X :=
  {x | preClearFlag rate (t := t) q (O x.1) = true ∧
    (O x.1).2.2.2.isSome = true ∧
    (ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h q x.2.2).isSome = true}

theorem measurableSet_activeSet :
    MeasurableSet (activeSet rate rewards C_star C_h control0 b u t q) := by
  have hO := (measurable_branchObservation rate rewards C_star C_h control0 b u t q.castSucc).comp
    (measurable_fst : Measurable (Prod.fst : X → _))
  have hc := ((ReferenceCalendarCollectionCallControlLaw.callAt_measurable
    rate rewards C_star C_h control0 q).mono
      ((ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le (q.val + 1)) le_rfl).comp
        (measurable_snd.snd : Measurable (fun x : X => x.2.2))
  exact (measurableSet_eq_fun ((measurable_preClearFlag rate (t := t) q).comp hO)
    measurable_const).inter ((measurableSet_eq_fun (measurable_isSome.comp hO.snd.snd.snd)
      measurable_const).inter (measurableSet_eq_fun (measurable_isSome.comp hc) measurable_const))

abbrev ActiveSample := ↥(activeSet rate rewards C_star C_h control0 b u t q)

local notation "A" => ActiveSample rate rewards C_star C_h control0 b u t q

/-- The original generated PRE endpoint and entire PRE list. -/
def activePre (x : A) : SlowSet p × List (LogicalCell p rate) :=
  (O x.val.1).2.2.2.get x.property.2.1

theorem activePre_spec (x : A) :
    (O x.val.1).2.2.2 = some (activePre rate rewards C_star C_h control0 b u t q x) :=
  (Option.some_get _).symm

theorem measurable_activePre :
    Measurable (activePre rate rewards C_star C_h control0 b u t q) := by
  apply measurable_of_some
  have hO := (measurable_branchObservation rate rewards C_star C_h control0 b u t q.castSucc).comp
    (measurable_fst.comp (measurable_subtype_coe : Measurable (Subtype.val : A → X)))
  convert hO.snd.snd.snd using 1
  funext x
  exact (activePre_spec rate rewards C_star C_h control0 b u t q x).symm

/-- The source passed to the native recorder is the produced inserted source. -/
def activeSource (x : A) : InvocationSource rate rewards C_star C_h q :=
  ⟨x.val.2.2, x.property.2.2⟩

theorem measurable_activeSource :
    Measurable (activeSource rate rewards C_star C_h control0 b u t q) :=
  (measurable_snd.snd.comp measurable_subtype_coe).subtype_mk

/-- Renewal has already used ORIGINAL label one for its initial draw. The
q update uses original label zero; retention uses original label one. -/
def activeRefresh (x : A) : Scalar :=
  if renewalFlag rate rewards C_star C_h (t := t) q (O x.val.1) then
    x.val.1.1.2 (q, 0) else x.val.1.1.2 (q, 1)

theorem measurable_activeRefresh :
    Measurable (activeRefresh rate rewards C_star C_h control0 b u t q) := by
  have hO := (measurable_branchObservation rate rewards C_star C_h control0 b u t q.castSucc).comp
    (measurable_fst.comp (measurable_subtype_coe : Measurable (Subtype.val : A → X)))
  exact ((measurable_pi_apply (q, 0)).comp (measurable_fst.fst.snd.comp measurable_subtype_coe)).ite
    (measurableSet_eq_fun ((measurable_renewalFlag rate rewards C_star C_h (t := t) q).comp hO)
      measurable_const)
    ((measurable_pi_apply (q, 1)).comp (measurable_fst.fst.snd.comp measurable_subtype_coe))

/-- The actual q cell on exactly the source and original auxiliary array of
this extension sample. No new source, endpoint, numerical word or array is drawn. -/
def activeCell (x : A) : LogicalCell p rate :=
  nativeCell rate rewards C_star C_h control0 q
    (activeSource rate rewards C_star C_h control0 b u t q x)
    (activeRefresh rate rewards C_star C_h control0 b u t q x)

theorem measurable_activeCell :
    Measurable (activeCell rate rewards C_star C_h control0 b u t q) := by
  change Measurable ((fun v : InvocationSource rate rewards C_star C_h q × Scalar =>
    nativeCell rate rewards C_star C_h control0 q v.1 v.2) ∘
      (fun x : A => (activeSource rate rewards C_star C_h control0 b u t q x,
        activeRefresh rate rewards C_star C_h control0 b u t q x)))
  have hs : Measurable (activeSource rate rewards C_star C_h control0 b u t q) :=
    measurable_activeSource rate rewards C_star C_h control0 b u t q
  have hr : Measurable (activeRefresh rate rewards C_star C_h control0 b u t q) :=
    measurable_activeRefresh rate rewards C_star C_h control0 b u t q
  exact (measurable_nativeCell rate rewards C_star C_h control0 q).comp (hs.prodMk hr)

/-- Canonical transition data retains the same produced PRE list and uses
the native q cell. The branch-specific erasure retains renewal's used label. -/
def callTransition (x : A) : TransitionData rate q :=
  ((((O x.val.1).1.1.1.2,
      (futureAuxiliarySplit q (renewalFlag rate rewards C_star C_h (t := t) q (O x.val.1))
        x.val.1.1.2).1), x.val.2.1),
    ((activePre rate rewards C_star C_h control0 b u t q x).2,
      (x.val.2.2, activeCell rate rewards C_star C_h control0 b u t q x)))

theorem measurable_callTransition :
    Measurable (callTransition rate rewards C_star C_h control0 b u t q) := by
  have hx : Measurable (Subtype.val : A → X) := measurable_subtype_coe
  have hO := (measurable_branchObservation rate rewards C_star C_h control0 b u t q.castSucc).comp
    (measurable_fst.comp hx)
  have hs : Measurable (fun ba : Bool × Auxiliary p => (futureAuxiliarySplit q ba.1 ba.2).1) :=
    measurable_from_prod_countable_right fun c => (futureAuxiliarySplit q c).measurable.fst
  have he := hs.comp (((measurable_renewalFlag rate rewards C_star C_h (t := t) q).comp hO).prodMk
    (measurable_fst.fst.snd.comp hx))
  exact ((hO.fst.fst.fst.snd.prodMk he).prodMk (measurable_snd.fst.comp hx)).prodMk
    ((measurable_activePre rate rewards C_star C_h control0 b u t q).snd.prodMk
      ((measurable_snd.snd.comp hx).prodMk
        (measurable_activeCell rate rewards C_star C_h control0 b u t q)))

/-- The existing POST-q initializer; both original q labels remain in its
used auxiliary readout, and its history appends to the SAME produced PRE list. -/
def postInitializer (x : A) : InitialObservation rate q :=
  let d := callTransition rate rewards C_star C_h control0 b u t q x
  (((d.1.1.1, insertedPhysicalSource rate d), d.1.2),
    (usedAuxiliary q x.val.1.1.2, postHistory d))

theorem measurable_postInitializer :
    Measurable (postInitializer rate rewards C_star C_h control0 b u t q) := by
  have hd := measurable_callTransition rate rewards C_star C_h control0 b u t q
  exact ((hd.fst.fst.fst.prodMk hd.snd.snd.fst).prodMk hd.fst.snd).prodMk
    (((measurable_usedAuxiliary q).comp (measurable_fst.fst.snd.comp measurable_subtype_coe)).prodMk
      ((measurable_postHistory rate q).comp hd))

/-- The post-initializer's seed and numerical state come from its own actual
q cell, rather than the last cell of an independently supplied history. -/
theorem postInitializer_alignment (x : A) :
    (postInitializer rate rewards C_star C_h control0 b u t q x).2.2 =
      (activePre rate rewards C_star C_h control0 b u t q x).2 ++
        [activeCell rate rewards C_star C_h control0 b u t q x] ∧
    postSeed rate (callTransition rate rewards C_star C_h control0 b u t q x) =
      (activeCell rate rewards C_star C_h control0 b u t q x).nextSlowSet ∧
    prefixNumerical rate rewards C_star C_h q.succ x.val.2.2 =
      some (postNumerical rate (callTransition rate rewards C_star C_h control0 b u t q x)) := by
  exact ⟨rfl, rfl, nativeCell_after_prefix rate rewards C_star C_h control0 q
    (activeSource rate rewards C_star C_h control0 b u t q x)
    (activeRefresh rate rewards C_star C_h control0 b u t q x)⟩

/-- Unnormalized restriction of the accepted law to the literal active set. -/
def activeLaw : Measure A := (mu).comap Subtype.val

theorem activeLaw_map_sample :
    (activeLaw rate rewards C_star C_h control0 b u t q).map Subtype.val =
      (mu).restrict (activeSet rate rewards C_star C_h control0 b u t q) :=
  map_comap_subtype_coe (measurableSet_activeSet rate rewards C_star C_h control0 b u t q) mu

/-- Joint POST law: the complete prior observation is retained alongside
the canonical initializer. In particular this is more than a second marginal. -/
def jointPostLaw : Measure (PrefixObservation rate t q.castSucc × InitialObservation rate q) :=
  (activeLaw rate rewards C_star C_h control0 b u t q).map (fun x =>
    (O x.val.1, postInitializer rate rewards C_star C_h control0 b u t q x))

/-- Same-sample generated PRE and actual selector coverage. Thus the only
remaining component is exactly PRE-stopped/missing-PRE mass, almost surely. -/
theorem ae_activeSet_iff_preClear :
    ∀ᵐ x ∂mu, x ∈ activeSet rate rewards C_star C_h control0 b u t q ↔
      preClearFlag rate (t := t) q (O x.1) = true := by
  have hm := ae_restrict_mem (μ := branchLaw rate rewards C_star C_h control0 b u t)
    (measurableSet_firstNextEvent rate rewards C_star C_h control0 b u t q)
  rw [← ReferenceNextInsertedSourceMarginal.nextInsertedLaw_map_original
    rate rewards C_star C_h control0 b u t q] at hm
  have hx := ae_of_ae_map measurable_fst.aemeasurable hm
  filter_upwards [hx, ReferenceNextInsertedSourceMarginal.ae_nextInsertedLaw_pre_locality
    rate rewards C_star C_h control0 b u t q] with x hx hl
  have hp := (survival_iff_prefix rate rewards C_star C_h control0 b u t q.castSucc x.1).mp hx.1
  obtain ⟨_hbetween, cutoff, theta, hc⟩ :=
    (firstNextEvent_iff rate rewards C_star C_h control0 b u t q x.1).mp hx
  have hcall : (ReferenceCalendarCollectionCallControlLaw.callAt
      rate rewards C_star C_h q x.2.2).isSome = true := by
    rw [hl.2.2.2, hc]
    rfl
  exact ⟨fun h => h.1, fun h => ⟨h, hp, hcall⟩⟩


private theorem activeLaw_ae_of_ae {P : X → Prop} (h : ∀ᵐ x ∂mu, P x) :
    ∀ᵐ x ∂activeLaw rate rewards C_star C_h control0 b u t q, P x.val :=
  (ae_restrict_iff_subtype (measurableSet_activeSet rate rewards C_star C_h control0 b u t q)).mp
    (ae_restrict_of_ae h)

/-- Both actual PRE objects align on the very same extension sample. The
PRE list is not a supplied history or a last-cell approximation to the word. -/
theorem ae_active_pre_alignment :
    ∀ᵐ x ∂activeLaw rate rewards C_star C_h control0 b u t q,
      (O x.val.1).2.2.1 = some (activeCell rate rewards C_star C_h control0 b u t q x).before ∧
      (activeCell rate rewards C_star C_h control0 b u t q x).before.overflow = false ∧
      noncallCalendar rate rewards C_star C_h t x.val.2.2 x.val.1.1.2
        (postSeed rate (branchTransition rate rewards C_star C_h control0 b u t x.val.1),
          postHistory (branchTransition rate rewards C_star C_h control0 b u t x.val.1)) q.val =
        some (activePre rate rewards C_star C_h control0 b u t q x) := by
  filter_upwards [activeLaw_ae_of_ae rate rewards C_star C_h control0 b u t q
    (ReferenceNextInsertedSourceMarginal.ae_nextInsertedLaw_pre_locality
      rate rewards C_star C_h control0 b u t q)] with x hx
  have hb := nativeBefore_prefix rate rewards C_star C_h control0 q
    (activeSource rate rewards C_star C_h control0 b u t q x)
  have hbefore : (O x.val.1).2.2.1 =
      some (activeCell rate rewards C_star C_h control0 b u t q x).before := hx.1.symm.trans hb
  have hclear := x.property.1
  rw [preClearFlag, hbefore, Option.any_some] at hclear
  exact ⟨hbefore, Bool.eq_false_of_not_eq_true' hclear,
    hx.2.1.trans (activePre_spec rate rewards C_star C_h control0 b u t q x)⟩

/-- The original identity table, all private coordinates including J, and
strict physical source prefix are retained on the active sample. -/
theorem ae_active_source_coordinates :
    ∀ᵐ x ∂activeLaw rate rewards C_star C_h control0 b u t q,
      x.val.2.2.1.1 = (O x.val.1).1.1.1.2.1.1 ∧
      x.val.2.2.2 = (O x.val.1).1.1.1.2.2 ∧
      ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 q.val x.val.2.2 =
        ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 q.val (O x.val.1).1.1.1.2 ∧
      ReferenceFirstCollectionRenewalVectorInsertion.av q x.val.2.2 = x.val.2.1 := by
  filter_upwards [activeLaw_ae_of_ae rate rewards C_star C_h control0 b u t q
      (ReferenceNextInsertedSourceMarginal.ae_nextInsertedLaw_source_coordinates
        rate rewards C_star C_h control0 b u t q),
    activeLaw_ae_of_ae rate rewards C_star C_h control0 b u t q
      (ReferenceNextInsertedSourceMarginal.ae_nextInsertedLaw_sourcePrefix
        rate rewards C_star C_h control0 b u t q),
    activeLaw_ae_of_ae rate rewards C_star C_h control0 b u t q
      (ReferenceNextInsertedSourceMarginal.ae_nextInsertedLaw_readout
        rate rewards C_star C_h control0 b u t q)] with x hc hp hr
  refine ⟨hc.1, hc.2.1, hp, ?_⟩
  rw [hr, ReferenceFirstCollectionRenewalVectorInsertion.av_insert]

/-- The actual q proposal depends on PRE overflow, preserving a proposal at
the first detecting update. It reads the native source's physical scalar. -/
theorem activeCell_proposal (x : A) :
    (activeCell rate rewards C_star C_h control0 b u t q x).proposal =
      (!(activeCell rate rewards C_star C_h control0 b u t q x).before.overflow &&
        ReferenceFirstLivePostUpdateProposalLaw.physicalProposalBit rate
          (ReferenceSourceCurrentControlFreshness.u_t p q x.val.2.2)) :=
  nativeCell_proposal rate rewards C_star C_h control0 q
    (activeSource rate rewards C_star C_h control0 b u t q x)
    (activeRefresh rate rewards C_star C_h control0 b u t q x)

/-- The actual residual draw uses the correct original q label. POST overflow
is deliberately absent from the gate. This is a same-sample identity. -/
theorem activeCell_refresh (x : A) :
    let z := activeSource rate rewards C_star C_h control0 b u t q x
    let c := activeCell rate rewards C_star C_h control0 b u t q x
    c.nextSlowSet = if c.before.overflow then frozenSlowSet p else
      if c.proposal then residualDraw rate c.before
        (nativeSourceCell rate rewards C_star C_h q z).input
        (nativeSourceCell rate rewards C_star C_h q z).selected.view.payload.anchor
        (nativeSourceCell rate rewards C_star C_h q z).selected.view.payload.anchor_pos
        (activeRefresh rate rewards C_star C_h control0 b u t q x)
      else (nativeSourceCell rate rewards C_star C_h q z).selected.view.payload.slowSet := by
  dsimp only [activeCell, nativeCell, appendLogicalCell]
  rw [Function.update_self]

/-- The accepted sampler graph identifies the native installed slow set.
Retention keeps the produced varying PRE endpoint. Renewal initializes from
original q label one, leaving original label zero for the q residual update. -/
theorem ae_activeCell_endpoint (htq : t.val < q.val) :
    ∀ᵐ x ∂activeLaw rate rewards C_star C_h control0 b u t q,
      ∃ (cutoff : Fin p.T) (theta : AssignmentParameterFibreKernel.Theta p),
        ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h q x.val.2.2 =
          some (cutoff, theta) ∧
        installationEndpoint rate rewards C_star C_h (t := t) q
          (actualNextInput rate rewards C_star C_h control0 b u t q x.val.1, theta) =
            some (activeCell rate rewards C_star C_h control0 b u t q x).slowSet ∧
        (if renewalFlag rate rewards C_star C_h (t := t) q (O x.val.1) then
          freshEndpoint theta (x.val.1.1.2 (q, 1))
        else some (activePre rate rewards C_star C_h control0 b u t q x).1) =
          some (activeCell rate rewards C_star C_h control0 b u t q x).slowSet ∧
        0 < AssignmentParameterFibreKernel.fibreMass p theta
          (some (activeCell rate rewards C_star C_h control0 b u t q x).slowSet) ∧
        AssignmentParameterFibreKernel.fibreMass p theta none = 0 := by
  filter_upwards [activeLaw_ae_of_ae rate rewards C_star C_h control0 b u t q
    (ReferenceNextInsertedSourceMarginal.ae_nextInsertedLaw_sampler_graph
      rate rewards C_star C_h control0 b u t q htq),
    ae_active_pre_alignment rate rewards C_star C_h control0 b u t q] with x hgraph hpre
  obtain ⟨cutoff, theta, U, output, hc, _ho, _hp, _hcode, hs, he, hpos, hn⟩ := hgraph x.property.1
  have hselected := nativeCell_selected rate rewards C_star C_h control0 q
    (activeSource rate rewards C_star C_h control0 b u t q x) cutoff theta hc
  have hu : (nativeSourceCell rate rewards C_star C_h q
      (activeSource rate rewards C_star C_h control0 b u t q x)).selected.view.payload.slowSet = U :=
    Option.some.inj (hselected.symm.trans hs)
  have hslow : (activeCell rate rewards C_star C_h control0 b u t q x).slowSet = U := by
    change (if (activeCell rate rewards C_star C_h control0 b u t q x).before.overflow then
      frozenSlowSet p else _) = U
    simp only [hpre.2.1, Bool.false_eq_true, ite_false, hu]
  refine ⟨cutoff, theta, hc, he.trans (congrArg some hslow.symm), ?_, ?_, hn⟩
  · rw [hslow]
    simpa only [installationEndpoint, endpointChoice, actualNextInput,
      ReferenceFirstNextLiftFutureAuxiliaryPairLaw.auxiliaryPair, retainedEndpoint,
      activePre_spec, Option.map_some] using he
  · rw [hslow]
    exact hpos


/-- Retain all exceptional samples unchanged, including their complete
sources, original auxiliary array, both assignment vectors and PRE observer. -/
def fullSpliceLaw : Measure
    (PrefixObservation rate t q.castSucc × (InitialObservation rate q ⊕ X)) :=
  (jointPostLaw rate rewards C_star C_h control0 b u t q).map (Prod.map id Sum.inl) +
    ((mu).restrict (activeSet rate rewards C_star C_h control0 b u t q)ᶜ).map
      (fun x => (O x.1, Sum.inr x))

/-- The whole old observer is preserved jointly across active and unchanged
exceptional components, with its original unnormalized first-vector weight. -/
theorem fullSpliceLaw_map_prior :
    (fullSpliceLaw rate rewards C_star C_h control0 b u t q).map Prod.fst =
      ((branchLaw rate rewards C_star C_h control0 b u t).restrict
        (firstNextEvent rate rewards C_star C_h control0 b u t q)).map O := by
  let f : X → PrefixObservation rate t q.castSucc := fun x => O x.1
  have hf : Measurable f :=
    (measurable_branchObservation rate rewards C_star C_h control0 b u t q.castSucc).comp measurable_fst
  have hj : Measurable (fun x : A =>
      (O x.val.1, postInitializer rate rewards C_star C_h control0 b u t q x)) :=
    (hf.comp measurable_subtype_coe).prodMk
      (measurable_postInitializer rate rewards C_star C_h control0 b u t q)
  have hi : Measurable (Prod.map id Sum.inl :
      PrefixObservation rate t q.castSucc × InitialObservation rate q →
        PrefixObservation rate t q.castSucc × (InitialObservation rate q ⊕ X)) :=
    measurable_id.prodMap measurable_inl
  have he : Measurable (fun x : X => (O x.1, (Sum.inr x : InitialObservation rate q ⊕ X))) :=
    hf.prodMk measurable_inr
  have hleft : ((jointPostLaw rate rewards C_star C_h control0 b u t q).map
      (Prod.map id (Sum.inl : InitialObservation rate q → InitialObservation rate q ⊕ X))).map Prod.fst =
        ((mu).restrict (activeSet rate rewards C_star C_h control0 b u t q)).map f := by
    rw [Measure.map_map measurable_fst hi]
    change (jointPostLaw rate rewards C_star C_h control0 b u t q).map Prod.fst = _
    rw [jointPostLaw, Measure.map_map measurable_fst hj]
    change (activeLaw rate rewards C_star C_h control0 b u t q).map (f ∘ Subtype.val) = _
    rw [← Measure.map_map hf measurable_subtype_coe, activeLaw_map_sample]
  have hright : (((mu).restrict (activeSet rate rewards C_star C_h control0 b u t q)ᶜ).map
      (fun x => (O x.1, (Sum.inr x : InitialObservation rate q ⊕ X)))).map Prod.fst =
        ((mu).restrict (activeSet rate rewards C_star C_h control0 b u t q)ᶜ).map f := by
    rw [Measure.map_map measurable_fst he]
    rfl
  rw [fullSpliceLaw, Measure.map_add _ _ measurable_fst, hleft, hright,
    ← Measure.map_add _ _ hf, Measure.restrict_add_restrict_compl
      (measurableSet_activeSet rate rewards C_star C_h control0 b u t q)]
  exact ReferenceNextInsertedSourceMarginal.nextInsertedLaw_map_observer
    rate rewards C_star C_h control0 b u t q O
      (measurable_branchObservation rate rewards C_star C_h control0 b u t q.castSucc)

/-- Read the full produced source in either component. No physical
continuation is replaced by an analytical frozen continuation. -/
def outputSource (o : PrefixObservation rate t q.castSucc × (InitialObservation rate q ⊕ X)) :
    Source p := o.2.elim (fun i => i.1.1.2) (fun x => x.2.2)

theorem measurable_outputSource :
    Measurable (outputSource rate rewards C_star C_h b u t q) :=
  ((measurable_fst.fst.snd : Measurable (fun i : InitialObservation rate q => i.1.1.2)).sumElim
    (measurable_snd.snd : Measurable (fun x : X => x.2.2))).comp measurable_snd

/-- The full-source marginal is exactly the accepted original-source law on
the actual call event. All continuous rows, private arrays and J remain. -/
theorem fullSpliceLaw_map_source (htq : t.val < q.val) :
    (fullSpliceLaw rate rewards C_star C_h control0 b u t q).map
      (outputSource rate rewards C_star C_h b u t q) =
      (BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
        (branchEvent rate rewards C_star C_h b u t ∩
          ReferenceNextInsertedSourceMarginal.physicalNextEvent rate rewards C_star C_h t q) := by
  have hO := measurable_branchObservation rate rewards C_star C_h control0 b u t q.castSucc
  have hj : Measurable (fun x : A =>
      (O x.val.1, postInitializer rate rewards C_star C_h control0 b u t q x)) :=
    (hO.comp (measurable_fst.comp measurable_subtype_coe)).prodMk
      (measurable_postInitializer rate rewards C_star C_h control0 b u t q)
  have hi : Measurable (Prod.map id Sum.inl :
      PrefixObservation rate t q.castSucc × InitialObservation rate q →
        PrefixObservation rate t q.castSucc × (InitialObservation rate q ⊕ X)) :=
    measurable_id.prodMap measurable_inl
  have he : Measurable (fun x : X => (O x.1, (Sum.inr x : InitialObservation rate q ⊕ X))) :=
    (hO.comp measurable_fst).prodMk measurable_inr
  have hs := measurable_outputSource rate rewards C_star C_h b u t q
  have hleft : ((jointPostLaw rate rewards C_star C_h control0 b u t q).map
      (Prod.map id Sum.inl)).map (outputSource rate rewards C_star C_h b u t q) =
        ((mu).restrict (activeSet rate rewards C_star C_h control0 b u t q)).map
          (fun x => x.2.2) := by
    rw [Measure.map_map hs hi]
    change (jointPostLaw rate rewards C_star C_h control0 b u t q).map (fun o => o.2.1.1.2) = _
    rw [jointPostLaw, Measure.map_map measurable_snd.fst.fst.snd hj]
    change (activeLaw rate rewards C_star C_h control0 b u t q).map
      ((fun x : X => x.2.2) ∘ Subtype.val) = _
    rw [← Measure.map_map measurable_snd.snd measurable_subtype_coe, activeLaw_map_sample]
  have hright : (((mu).restrict (activeSet rate rewards C_star C_h control0 b u t q)ᶜ).map
      (fun x => (O x.1, (Sum.inr x : InitialObservation rate q ⊕ X)))).map
        (outputSource rate rewards C_star C_h b u t q) =
      ((mu).restrict (activeSet rate rewards C_star C_h control0 b u t q)ᶜ).map
        (fun x => x.2.2) := by
    rw [Measure.map_map hs he]
    rfl
  rw [fullSpliceLaw, Measure.map_add _ _ hs, hleft, hright,
    ← Measure.map_add _ _ measurable_snd.snd, Measure.restrict_add_restrict_compl
      (measurableSet_activeSet rate rewards C_star C_h control0 b u t q)]
  exact ReferenceNextInsertedSourceMarginal.nextInsertedLaw_map_sourceInputLaw
    rate rewards C_star C_h control0 b u t q htq

/-- No normalization or exceptional mass is lost. -/
theorem fullSpliceLaw_mass :
    fullSpliceLaw rate rewards C_star C_h control0 b u t q Set.univ =
      branchLaw rate rewards C_star C_h control0 b u t
        (firstNextEvent rate rewards C_star C_h control0 b u t q) := by
  have h := congrArg (fun m : Measure (PrefixObservation rate t q.castSucc) => m Set.univ)
    (fullSpliceLaw_map_prior rate rewards C_star C_h control0 b u t q)
  rw [Measure.map_apply measurable_fst MeasurableSet.univ,
    Measure.map_apply (measurable_branchObservation rate rewards C_star C_h control0 b u t q.castSucc)
      MeasurableSet.univ] at h
  simpa only [Set.preimage_univ, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter] using h

/-- Exceptional samples keep the canonical current-vector Dirac outcome
and the entire physical source, with every future physical coordinate. -/
theorem ae_exceptional_identity :
    ∀ᵐ x ∂(mu).restrict (activeSet rate rewards C_star C_h control0 b u t q)ᶜ,
      preClearFlag rate (t := t) q (O x.1) = false ∧
      x.2.2 = (O x.1).1.1.1.2 ∧
      x.2.1 = ReferenceFirstCollectionRenewalVectorInsertion.av q (O x.1).1.1.1.2 := by
  filter_upwards [ae_restrict_mem (μ := mu)
      (measurableSet_activeSet rate rewards C_star C_h control0 b u t q).compl,
    ae_restrict_of_ae (ae_activeSet_iff_preClear rate rewards C_star C_h control0 b u t q),
    ae_restrict_of_ae (ReferenceNextInsertedSourceMarginal.ae_nextInsertedLaw_stopped_identity
      rate rewards C_star C_h control0 b u t q),
    ae_restrict_of_ae (ReferenceNextInsertedSourceMarginal.ae_nextInsertedLaw_readout
      rate rewards C_star C_h control0 b u t q)] with x hx he hs hr
  have hfalse : preClearFlag rate (t := t) q (O x.1) = false := by
    cases hc : preClearFlag rate (t := t) q (O x.1) with
    | false => rfl
    | true => exact False.elim (hx (he.mpr hc))
  have hsource := hs hfalse
  have hv := congrArg (ReferenceFirstCollectionRenewalVectorInsertion.av q) hr
  rw [ReferenceFirstCollectionRenewalVectorInsertion.av_insert] at hv
  exact ⟨hfalse, hsource, hv.symm.trans
    (congrArg (ReferenceFirstCollectionRenewalVectorInsertion.av q) hsource)⟩

/-- Rebase only the initializer already present in the joint law. The new
seed is its actual q residual and its numerical PRE is the actual q update. -/
theorem postInitializer_rebase (x : A) :
    initialExtension rate rewards C_star C_h q
      (postInitializer rate rewards C_star C_h control0 b u t q x) =
    (postInitializer rate rewards C_star C_h control0 b u t q x,
      (fun i => x.val.1.1.2 i.val,
        (some (activeCell rate rewards C_star C_h control0 b u t q x).after,
          some ((activeCell rate rewards C_star C_h control0 b u t q x).nextSlowSet,
            (postInitializer rate rewards C_star C_h control0 b u t q x).2.2)))) := by
  dsimp only [initialExtension]
  apply Prod.ext
  · rfl
  apply Prod.ext
  · rfl
  apply Prod.ext
  · exact (postInitializer_alignment rate rewards C_star C_h control0 b u t q x).2.2
  · change (postHistory (callTransition rate rewards C_star C_h control0 b u t q x)).getLast?.map _ = _
    rw [postHistory_last]
    rfl

/-- Literal joint pushforward through the accepted rebasing map. The entire
old observer stays present; rebasing never passes through a second marginal. -/
theorem jointPostLaw_rebase :
    (jointPostLaw rate rewards C_star C_h control0 b u t q).map
      (Prod.map id (initialExtension rate rewards C_star C_h q)) =
    (activeLaw rate rewards C_star C_h control0 b u t q).map (fun x =>
      (O x.val.1,
        (postInitializer rate rewards C_star C_h control0 b u t q x,
          (fun i => x.val.1.1.2 i.val,
            (some (activeCell rate rewards C_star C_h control0 b u t q x).after,
              some ((activeCell rate rewards C_star C_h control0 b u t q x).nextSlowSet,
                (postInitializer rate rewards C_star C_h control0 b u t q x).2.2)))))) := by
  have hO := measurable_branchObservation rate rewards C_star C_h control0 b u t q.castSucc
  have hj : Measurable (fun x : A =>
      (O x.val.1, postInitializer rate rewards C_star C_h control0 b u t q x)) :=
    (hO.comp (measurable_fst.comp measurable_subtype_coe)).prodMk
      (measurable_postInitializer rate rewards C_star C_h control0 b u t q)
  rw [jointPostLaw, Measure.map_map
    (measurable_id.prodMap (measurable_initialExtension rate rewards C_star C_h q)) hj]
  apply Measure.map_congr
  exact Filter.Eventually.of_forall fun x =>
    Prod.ext rfl (postInitializer_rebase rate rewards C_star C_h control0 b u t q x)

end Splice

end Bandits.Support.ReferenceGeneratedInvocationCallSplice
