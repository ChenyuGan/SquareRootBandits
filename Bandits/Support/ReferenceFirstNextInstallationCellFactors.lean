/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstNextInvocationJointLift

import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Tactic

/-!
# Actual first next-installation cells and separate factors

The actual installationEvent-0 producers give Borel cells in the accepted
State/run/LogicalCell schema, sampler/support reconstruction for both branches,
physical joint tests, and separate unused-scalar splits.

Scope: physical tests still integrate the current remainder and do not factor
proposals. Per-source commonUpdateKernel and scalar splits do not compose a
retained-past transition. Numerical old-list endpoint alignment, proposal/refresh/
post-cell composition, insertion Option-law/event coverage and rank/all-calendar
reentry remain open. Option is only a Borel readout with a terminal identity.

Sources: ZIP4 `06_interruptions.tex:391-426`,
`04_slow_fast_learner.tex:142-215`, and `08_main_theorem.tex:78-109`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ContinuousControlSlice
open Bandits.Support.ReferenceFirstLiveChronologicalPrefixFoundation
open Bandits.Support.ReferenceFirstLiveCalendarMarkedTransition

open Bandits.Support.ReferenceFirstNextInvocationJointLift
open Bandits.Support.ReferenceFirstLiveActualRefreshTestLaw
  (ErasedAuxiliaryArray actualRefreshScalarSplit actualRefreshScalarSplit_symm_apply
    auxiliarySection erasedAuxiliaryLaw insertActualRefreshCoordinate
    measurable_insertActualRefreshCoordinate measurePreserving_actualRefreshScalarSplit scalarZero)

namespace Bandits.Support.ReferenceFirstNextInstallationCellFactors

variable {p : ConstructorDimensions.Parameters}

local instance sourceInputMeasurableSpace :
    MeasurableSpace (BootstrapPrivateRoundStreams.SourceInput p) := by
  change MeasurableSpace (CompletePublicTable.PublishedOutput p ×
    BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

local instance outcomeMeasurableSpace : MeasurableSpace (AssignmentParameterFibreKernel.Outcome p) := ⊤
local instance outcomeDiscreteMeasurableSpace :
    DiscreteMeasurableSpace (AssignmentParameterFibreKernel.Outcome p) :=
  ⟨fun _ => trivial⟩
local instance outcomeFintype : Fintype (AssignmentParameterFibreKernel.Outcome p) := inferInstance
local instance outcomeCountable : Countable (AssignmentParameterFibreKernel.Outcome p) := inferInstance
local instance outcomeSingletons : MeasurableSingletonClass
    (AssignmentParameterFibreKernel.Outcome p) := inferInstance
local instance slowSetFintype : Fintype (SlowSet p) := inferInstance
local instance slowSetCountable : Countable (SlowSet p) := inferInstance

abbrev AuxArray := ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray
abbrev Vector := AssignmentParameterFibreKernel.AssignmentVector
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev Record {p : ConstructorDimensions.Parameters} (rate : RateInput p) :=
  ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)
abbrev Cell {p : ConstructorDimensions.Parameters} (rate : RateInput p) := LogicalCell p rate
abbrev SourceCell {p : ConstructorDimensions.Parameters} {rate : RateInput p}
    (r : Record rate) := ReferenceFirstWindowNumericalStream.ActualLiveSourceCell r

/-- The current label-one scalar is not read by the complete retained old
observation or its sampled endpoint path. This is the pointwise locality
needed before splitting that scalar out of the literal auxiliary product. -/
public theorem nextInvocationObservation_refreshScalar_ext
    (rate : RateInput p) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T)
    (control0 : ContinuousLearningRows.TimeControl p)
    (z : EventSource rate rewards C_star C_h u t)
    (erased : ErasedAuxiliaryArray t)
    (x y : ContinuousControlSlice.Scalar) :
    nextInvocationObservation rate rewards C_star C_h u t control0
        (z, insertActualRefreshCoordinate t erased x) =
      nextInvocationObservation rate rewards C_star C_h u t control0
        (z, insertActualRefreshCoordinate t erased y) := by
  have hcoord : ∀ v : Fin p.T, v.val < t.val → ∀ l : Fin 2,
      insertActualRefreshCoordinate t erased x (v, l) =
        insertActualRefreshCoordinate t erased y (v, l) := by
    intro v hv l
    have hne : (v, l) ≠ (t, 1) := fun he =>
      (Nat.ne_of_lt hv) (congrArg (fun q : Fin p.T × Fin 2 => q.1.val) he)
    simp only [insertActualRefreshCoordinate, hne, dite_false]
  have hpast := ReferenceFirstCollectionLogicalPrefixExtension.extendedPrefixStateAux_auxiliary_ext
      rate rewards C_star C_h t.val (Nat.le_of_lt t.isLt) z.val
      (insertActualRefreshCoordinate t erased x)
      (insertActualRefreshCoordinate t erased y) hcoord
  have hlabel : ReferenceFirstLiveCalendarMarkedTransition.labelZero
      (insertActualRefreshCoordinate t erased x) =
      ReferenceFirstLiveCalendarMarkedTransition.labelZero
        (insertActualRefreshCoordinate t erased y) := by
    funext v
    simp [ReferenceFirstLiveCalendarMarkedTransition.labelZero, insertActualRefreshCoordinate]
  have hpath : ReferenceFirstLiveCollectionPathJoin.collectionPath rate rewards C_star C_h u t z
        (insertActualRefreshCoordinate t erased x) =
      ReferenceFirstLiveCollectionPathJoin.collectionPath rate rewards C_star C_h u t z
        (insertActualRefreshCoordinate t erased y) := by
    funext i
    have hi := i.isLt
    have hdates := ReferenceFirstLiveCollectionPathJoin.firstLiveCollectionEvent_dates
      rate rewards C_star C_h u t z.val z.property
    have hd : u.val + i.val ≤ t.val := by omega
    have hstate :=
      ReferenceFirstCollectionLogicalPrefixExtension.extendedPrefixStateAux_auxiliary_ext
        rate rewards C_star C_h (u.val + i.val) (by omega) z.val
        (insertActualRefreshCoordinate t erased x)
        (insertActualRefreshCoordinate t erased y)
        (fun v hv l => hcoord v (by omega) l)
    have hl := generatedIncoming_eq_path rate rewards C_star C_h u t z
      (insertActualRefreshCoordinate t erased x) i
    have hr := generatedIncoming_eq_path rate rewards C_star C_h u t z
      (insertActualRefreshCoordinate t erased y) i
    exact Option.some.inj (hl.symm.trans ((congrArg Prod.fst hstate).trans hr))
  have hobs :
      ReferenceFirstCollectionLogicalPrefixExtension.extendedObservation rate rewards C_star C_h
          control0 t.castSucc
          (z.val, insertActualRefreshCoordinate t erased x) =
        ReferenceFirstCollectionLogicalPrefixExtension.extendedObservation rate rewards C_star C_h
          control0 t.castSucc
          (z.val, insertActualRefreshCoordinate t erased y) := by
    have hlist := congrArg Prod.snd hpast
    exact Prod.ext rfl (Prod.ext hlabel hlist)
  exact Prod.ext hobs hpath

/-- The actual nonrenewed assignment fibre is unchanged when the current
refresh scalar is varied: its sampler parameter and SAME generated endpoint
are both read from the invariant signature. -/
public theorem nonrenewedVectorKernel_refreshScalar_ext
    (rate : RateInput p) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T)
    (control0 : ContinuousLearningRows.TimeControl p)
    (z : EventSource rate rewards C_star C_h u t)
    (erased : ErasedAuxiliaryArray t)
    (x y : ContinuousControlSlice.Scalar) :
    nonrenewedVectorKernel rate rewards C_star C_h u t control0
        (z, insertActualRefreshCoordinate t erased x) =
      nonrenewedVectorKernel rate rewards C_star C_h u t control0
        (z, insertActualRefreshCoordinate t erased y) := by
  have hpath := congrArg Prod.snd
    (nextInvocationObservation_refreshScalar_ext rate rewards C_star C_h u t control0 z erased x y)
  unfold nonrenewedVectorKernel
  rw [ProbabilityTheory.Kernel.comap_apply, ProbabilityTheory.Kernel.comap_apply]
  exact congrArg (fun D : ReferenceFirstLiveCollectionPathJoin.Path u t =>
    AssignmentParameterFibreKernel.assignmentParameterFibreKernel p
      (nextParameter rate rewards C_star C_h u t control0 z,
        some (D (Fin.last (t.val - u.val))))) hpath

/-- Fubini for a literal scalar erasure and an invariant insertion kernel.
This is used with the actual label-1 and label-0 erasures below. -/
private theorem splitKernel_joint_test {Z A E V : Type*}
    [MeasurableSpace Z] [MeasurableSpace A] [MeasurableSpace E] [MeasurableSpace V]
    (mu : Measure Z) [IsFiniteMeasure mu] (nu : Measure A) [IsFiniteMeasure nu]
    (erasedLaw : Measure E) [IsFiniteMeasure erasedLaw]
    (split : A ≃ᵐ E × Scalar)
    (hpres : MeasurePreserving split nu (erasedLaw.prod scalarLaw))
    (k : ProbabilityTheory.Kernel (Z × A) V) [ProbabilityTheory.IsMarkovKernel k]
    (hinvariant : ∀ z e x y, k (z, split.symm (e, x)) = k (z, split.symm (e, y)))
    (Phi : ((Z × E) × V) × Scalar → ℝ)
    (hPhi : Measurable Phi) (M : ℝ) (hbound : ∀ x, ‖Phi x‖ ≤ M) :
    (∫ wv, Phi (((wv.1.1, (split wv.1.2).1), wv.2), (split wv.1.2).2) ∂(mu.prod nu).compProd k) =
    ∫ bx, ∫ v, Phi ((bx.1, v), bx.2) ∂k (bx.1.1, split.symm (bx.1.2, scalarZero))
      ∂(mu.prod erasedLaw).prod scalarLaw := by
  let obs := fun w : Z × A => ((w.1, (split w.2).1), (split w.2).2)
  have hflat : MeasurePreserving obs (mu.prod nu) ((mu.prod erasedLaw).prod scalarLaw) :=
    (measurePreserving_prodAssoc mu erasedLaw scalarLaw).symm.comp
      ((MeasurePreserving.id mu).prod hpres)
  let restore := fun bx : (Z × E) × Scalar =>
    (bx.1.1, split.symm (bx.1.2, scalarZero))
  have hrestore : Measurable restore := measurable_fst.fst.prodMk
    (split.symm.measurable.comp (measurable_fst.snd.prodMk measurable_const))
  let kernel := k.comap restore hrestore
  let F := fun q : (((Z × E) × Scalar) × V) => Phi ((q.1.1, q.2), q.1.2)
  have hF : Measurable F := hPhi.comp
    ((measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd)
  let g := fun bx : (Z × E) × Scalar => ∫ v, F (bx, v) ∂kernel bx
  have hg : Measurable g :=
    (hF.stronglyMeasurable.integral_kernel_prod_right' (κ := kernel)).measurable
  let test := fun wv : (Z × A) × V => F (obs wv.1, wv.2)
  have htest : Measurable test := hF.comp
    ((hflat.measurable.comp measurable_fst).prodMk measurable_snd)
  have hint : Integrable test ((mu.prod nu).compProd k) :=
    (integrable_const M).mono' htest.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun _ => hbound _))
  have hk (w : Z × A) : k w = kernel (obs w) := by
    have hr : w.2 = split.symm ((split w.2).1, (split w.2).2) := (split.symm_apply_apply w.2).symm
    change k w = k (w.1, split.symm ((split w.2).1, scalarZero))
    exact (congrArg (fun a => k (w.1, a)) hr).trans
      (hinvariant w.1 (split w.2).1 (split w.2).2 scalarZero)
  change (∫ wv, test wv ∂(mu.prod nu).compProd k) = _
  calc
    _ = ∫ w, g (obs w) ∂mu.prod nu := by
      rw [Measure.integral_compProd hint]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun w => by dsimp [g, test]; rw [hk w]
    _ = ∫ bx, g bx ∂(mu.prod nu).map obs :=
      (integral_map hflat.measurable.aemeasurable hg.aestronglyMeasurable).symm
    _ = _ := by rw [hflat.map_eq]; rfl

/-- Under the actual nonrenewed lift, label 1 remains independent after
retaining the whole original source, all other auxiliary coordinates and the
inserted full vector. The complete old list is a Borel readout of these data. -/
public theorem nonrenewedRefreshScalar_vector_joint_test
    (rate : RateInput p) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T) (control0 : ContinuousLearningRows.TimeControl p)
    (Phi : (((EventSource rate rewards C_star C_h u t × ErasedAuxiliaryArray t) ×
      Vector p) × Scalar) → ℝ)
    (hPhi : Measurable Phi) (M : ℝ) (hbound : ∀ x, ‖Phi x‖ ≤ M) :
    (∫ wv, Phi (((wv.1.1, (actualRefreshScalarSplit t wv.1.2).1), wv.2),
        (actualRefreshScalarSplit t wv.1.2).2)
      ∂nonrenewedLiftLaw rate rewards C_star C_h u t control0) =
    ∫ bx, ∫ v, Phi ((bx.1, v), bx.2) ∂nonrenewedVectorKernel rate rewards C_star C_h u t control0
        (bx.1.1, insertActualRefreshCoordinate t bx.1.2 scalarZero)
      ∂((eventSourceLaw rate rewards C_star C_h u t).prod
        (erasedAuxiliaryLaw t)).prod scalarLaw := by
  have hi : ∀ z e x y, nonrenewedVectorKernel rate rewards C_star C_h u t control0
        (z, (actualRefreshScalarSplit t).symm (e, x)) =
      nonrenewedVectorKernel rate rewards C_star C_h u t control0
        (z, (actualRefreshScalarSplit t).symm (e, y)) := by
    intro z e x y
    simpa only [actualRefreshScalarSplit_symm_apply] using
      nonrenewedVectorKernel_refreshScalar_ext rate rewards C_star C_h u t control0 z e x y
  simpa only [nonrenewedLiftLaw, nonrenewedBaseLaw, actualRefreshScalarSplit_symm_apply] using
    splitKernel_joint_test (eventSourceLaw rate rewards C_star C_h u t)
      (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p)
      (erasedAuxiliaryLaw t)
      (actualRefreshScalarSplit t)
      (measurePreserving_actualRefreshScalarSplit t)
      (nonrenewedVectorKernel rate rewards C_star C_h u t control0)
      hi Phi hPhi M hbound

section ActualFirstInvocation

local instance optionMeasurableSpace {A : Type*} [MeasurableSpace A] :
    MeasurableSpace (Option A) := LaterAssignmentStartMeasurability.optionMeasurableSpace

variable (rate : RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
  (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T)

/-- The domain is the literal first actual invocation, independently of its
sampled outcome. No cell, numerical state, or generated-law certificate is an
input to this subtype. -/
abbrev FirstInvocationSource := {z : BootstrapPrivateRoundStreams.SourceInput p //
    z ∈ ReferenceRankInstallationRecorderFoundation.installationEvent rate rewards C_star C_h 0 t}

local notation "Z" => FirstInvocationSource rate rewards C_star C_h t
local notation "NonrenewedSample" u =>
  (EventSource rate rewards C_star C_h u t × AuxArray p) × Vector p
local notation "records" z =>
  ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
local notation "recordAt" => ReferenceSourcePrefixHistoryFiltration.actualRecord
  rate rewards C_star C_h t
local notation "beforeAt" =>
  ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationNumericalBefore
    rate rewards C_star C_h control0 t

/-- The index supplied by the actual first-invocation source producer. -/
public def firstRecordIndex (z : Z) : Fin (records z.val).length :=
  (ReferenceRankInstallationRecorderFoundation.installationEvent_recordingData
    rate rewards C_star C_h 0 t z.val z.property).choose

public def firstRecord (z : Z) : Record rate :=
  (records z.val)[(firstRecordIndex rate rewards C_star C_h t z).val]

/-- The native cell extracted from the actual dispatcher result. -/
public def firstSourceCell (z : Z) : SourceCell (firstRecord rate rewards C_star C_h t z) :=
  (ReferenceRankInstallationRecorderFoundation.installationEvent_recordingData
    rate rewards C_star C_h 0 t z.val z.property).choose_spec.choose

public theorem firstSourceCell_spec (z : Z) :
    recordAt z.val = some (firstRecord rate rewards C_star C_h t z) ∧
    (firstRecord rate rewards C_star C_h t z).input.time = t ∧
    ReferenceLaterLiveNumericalReadout.laterLiveReadout 0
      (firstRecord rate rewards C_star C_h t z) =
      some (firstSourceCell rate rewards C_star C_h t z).input := by
  have h := (ReferenceRankInstallationRecorderFoundation.installationEvent_recordingData
    rate rewards C_star C_h 0 t z.val z.property).choose_spec.choose_spec
  exact ⟨h.1, h.2.1, h.2.2.2.2.2.2.1⟩

/-- The PRE state extracted from the proved actual strict-past readout. -/
public def firstBefore (z : Z) : RecordedQueueRun.RunState p.K :=
  (ReferenceRankInstallationPostUpdateProposalLaw.installationEvent_numericalUpdate_eq_step
    rate rewards C_star C_h control0 0 t z.val z.property).choose

public theorem firstBefore_spec (z : Z) : beforeAt z.val = some
      ((firstBefore rate rewards C_star C_h control0 t z).registers,
        (firstBefore rate rewards C_star C_h control0 t z).overflow,
        (firstBefore rate rewards C_star C_h control0 t z).records) :=
  (ReferenceRankInstallationPostUpdateProposalLaw.installationEvent_numericalUpdate_eq_step
    rate rewards C_star C_h control0 0 t z.val z.property).choose_spec.choose_spec.2.1

/-- The actual cell, with label 1 for nonrenewal or label 0 for renewal refresh. -/
public def actualFirstCell (z : Z) (x : ContinuousControlSlice.Scalar) : Cell rate :=
  let r := firstRecord rate rewards C_star C_h t z
  appendLogicalCell r (firstSourceCell rate rewards C_star C_h t z)
    (firstBefore rate rewards C_star C_h control0 t z)
    (Function.update auxiliarySection (r.input.time, 1) x)

public theorem actualFirstCell_time (z : Z) (x : ContinuousControlSlice.Scalar) :
    (actualFirstCell rate rewards C_star C_h control0 t z x).time = t :=
  (firstSourceCell_spec rate rewards C_star C_h t z).2.1

public theorem actualFirstCell_before (z : Z) (x : ContinuousControlSlice.Scalar) :
    beforeAt z.val = some
      ((actualFirstCell rate rewards C_star C_h control0 t z x).before.registers,
        (actualFirstCell rate rewards C_star C_h control0 t z x).before.overflow,
        (actualFirstCell rate rewards C_star C_h control0 t z x).before.records) :=
  firstBefore_spec rate rewards C_star C_h control0 t z

public theorem actualFirstCell_numerical (z : Z) (x : ContinuousControlSlice.Scalar) :
    (ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualCell
      rate rewards C_star C_h t z.val).map
        ReferenceLaterLiveReadoutValuesMeasurability.numericalCoordinates =
      some (actualFirstCell rate rewards C_star C_h control0 t z x).numerical := by
  have h := firstSourceCell_spec rate rewards C_star C_h t z
  change ((recordAt z.val).bind (ReferenceLaterLiveNumericalReadout.laterLiveReadout 0)).map _ = _
  rw [h.1]
  change (ReferenceLaterLiveNumericalReadout.laterLiveReadout 0
    (firstRecord rate rewards C_star C_h t z)).map _ = _
  rw [h.2.2]
  rfl

/-- The produced cell performs the actual whole-arm numerical update,
including service on zero-arrival arms and the first overflow-detecting step.
The raw vector remains distinct from the accepted/frozen arrivals. -/
public theorem actualFirstCell_wholeUpdate (z : Z) (x : Scalar) :
    ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationNumericalUpdate
      rate rewards C_star C_h control0 t z.val =
      some (show ReferenceFirstLivePostUpdateProposalLaw.NumericalUpdateFields p from
        { raw := RecordedQueueRun.quantizedArrival
            (ReferenceFirstLaunchNumericalCell.queueParameters rate)
            (firstSourceCell rate rewards C_star C_h t z).input
          beforeRegisters := (actualFirstCell rate rewards C_star C_h control0 t z x).before.registers
          beforeOverflow := (actualFirstCell rate rewards C_star C_h control0 t z x).before.overflow
          beforeRecords := (actualFirstCell rate rewards C_star C_h control0 t z x).before.records
          accepted := (actualFirstCell rate rewards C_star C_h control0 t z x).arrivals
          service := (actualFirstCell rate rewards C_star C_h control0 t z x).service
          afterRegisters := (actualFirstCell rate rewards C_star C_h control0 t z x).after.registers
          afterOverflow := (actualFirstCell rate rewards C_star C_h control0 t z x).after.overflow
          afterRecords := (actualFirstCell rate rewards C_star C_h control0 t z x).after.records }) := by
  have hraw : ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationRawArrivals
      rate rewards C_star C_h t z.val =
      some (RecordedQueueRun.quantizedArrival
        (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        (firstSourceCell rate rewards C_star C_h t z).input) := by
    simp only [ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationRawArrivals,
      ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationRawCoordinates,
      (firstSourceCell_spec rate rewards C_star C_h t z).1, Option.bind_some,
      (firstSourceCell_spec rate rewards C_star C_h t z).2.2, Option.map_some]
    rfl
  rw [ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationNumericalUpdate,
    firstBefore_spec rate rewards C_star C_h control0 t z, hraw]
  exact congrArg some (ReferenceFirstLivePostUpdateProposalLaw.numericalUpdateFields_eq_step
    rate (firstBefore rate rewards C_star C_h control0 t z)
    (firstSourceCell rate rewards C_star C_h t z).input
    (firstSourceCell rate rewards C_star C_h t z).enabled)

include control0 in
public theorem actualFirstCell_view (z : Z) :
    ReferenceRankInstallationRecorderFoundation.actualInstallationView
      rate rewards C_star C_h t z.val =
      some (firstSourceCell rate rewards C_star C_h t z).selected.view := by
  rw [ReferenceRankInstallationPostUpdateProposalLaw.installationEvent_actualView_dispatchProjection
    rate rewards C_star C_h control0 0 t z.val z.property,
    (firstSourceCell_spec rate rewards C_star C_h t z).1]
  change (ReferenceActivePhysicalStep.dispatch
    (firstRecord rate rewards C_star C_h t z).input).downView = _
  have hprep : (firstRecord rate rewards C_star C_h t z).output.preparation.coordinator =
      ReferenceActivePhysicalStep.dispatch (firstRecord rate rewards C_star C_h t z).input := by
    rw [(firstRecord rate rewards C_star C_h t z).output_eq]
    rfl
  rw [← hprep, ReferenceActivePhysicalStep.DispatchCut.downView,
    (firstSourceCell rate rewards C_star C_h t z).selection_actual]
  rfl

/-- The produced cell's all-arm update is the deterministic readout of the
actual correlated recorder/FAST pair, at its own actual PRE state. This is a
pointwise identity, not a hidden-past conditional kernel assertion. -/
public theorem actualFirstCell_updateFromPair (z : Z) (x : Scalar) :
    ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationNumericalUpdate
      rate rewards C_star C_h control0 t z.val =
      ReferenceRankInstallationCommonUpdateJointLaw.updateFromPair rate rewards t
        (firstSourceCell rate rewards C_star C_h t z).selected.view
        (some ((actualFirstCell rate rewards C_star C_h control0 t z x).before.registers,
          (actualFirstCell rate rewards C_star C_h control0 t z x).before.overflow,
          (actualFirstCell rate rewards C_star C_h control0 t z x).before.records))
        (ReferenceRankInstallationRecorderFastLaw.actualMarkerReservedFast
          rate rewards C_star C_h t z.val) := by
  rw [← actualFirstCell_before rate rewards C_star C_h control0 t z x]
  exact ReferenceRankInstallationCommonUpdateJointLaw.actualInstallationNumericalUpdate_eq_updateFromPair
    rate rewards C_star C_h control0 0 t z.val z.property _
      (actualFirstCell_view rate rewards C_star C_h control0 t z)

public theorem firstRecord_control (z : Z) : CompletePublicTable.completeRowLearning p
      (firstRecord rate rewards C_star C_h t z).input.row
      (firstRecord rate rewards C_star C_h t z).input.time =
      ReferenceSourceCurrentControlFreshness.u_t p t z.val := by
  have h := ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields
    rate rewards C_star C_h t z.val (firstRecord rate rewards C_star C_h t z)
    (firstSourceCell_spec rate rewards C_star C_h t z).1
  change ((firstRecord rate rewards C_star C_h t z).input.rows
    (firstRecord rate rewards C_star C_h t z).input.selected).2
      (firstRecord rate rewards C_star C_h t z).input.time = _
  rw [h.1, h.2.1, h.2.2.1]
  rfl

/-- The produced cell's proposal is the actual physical LIVE bit, gated by
PRE overflow. POST overflow does not suppress this detecting proposal. -/
public theorem actualFirstCell_proposal (z : Z) (x : Scalar) :
    (actualFirstCell rate rewards C_star C_h control0 t z x).proposal =
      (!(actualFirstCell rate rewards C_star C_h control0 t z x).before.overflow &&
        ReferenceFirstLivePostUpdateProposalLaw.physicalProposalBit rate
          (ReferenceSourceCurrentControlFreshness.u_t p t z.val)) := by
  change (!((firstBefore rate rewards C_star C_h control0 t z).overflow) &&
    FollowerCutoffScan.completeRowProposalBit p rate.eta.val
      (firstRecord rate rewards C_star C_h t z).input.row
      (firstRecord rate rewards C_star C_h t z).input.time) = _
  rw [ReferenceFirstLivePostUpdateProposalLaw.completeRowProposalBit_eq_physicalProposalBit
    rate _ _ _ rfl, firstRecord_control rate rewards C_star C_h t z]
  rfl

/-- The true residual law at this cell's own actual PRE state and input. -/
public theorem actualFirstCell_refresh_law (z : Z) :
    scalarLaw.map (actualFirstCell rate rewards C_star C_h control0 t z) =
      (logicalCellResidualLaw rate (firstRecord rate rewards C_star C_h t z)
        (firstSourceCell rate rewards C_star C_h t z)
        (firstBefore rate rewards C_star C_h control0 t z)).map
        (logicalCellWithNext rate (firstRecord rate rewards C_star C_h t z)
          (firstSourceCell rate rewards C_star C_h t z)
          (firstBefore rate rewards C_star C_h control0 t z)) := by
  change scalarLaw.map (fun x => appendLogicalCell _ _ _
    (Function.update auxiliarySection (_, 1) x)) = _
  exact appendLogicalCell_residual_law rate (firstRecord rate rewards C_star C_h t z)
    (firstSourceCell rate rewards C_star C_h t z)
    (firstBefore rate rewards C_star C_h control0 t z)

include control0 in
public theorem firstSourceCell_fast (z : Z) :
    ReferenceRankInstallationRecorderFastLaw.actualReservedFast rate rewards C_star C_h t z.val =
      some (reservedFastArm (firstRecord rate rewards C_star C_h t z)
        (firstSourceCell rate rewards C_star C_h t z)).val := by
  let native := firstSourceCell rate rewards C_star C_h t z
  have ht := (firstSourceCell_spec rate rewards C_star C_h t z).2.1
  have valid : CoordinatorLocalArmChoice.ChoiceInputsValid native.selected.view.payload
      native.selected.view.cutoff t native.selected.view.complementWeights := by
    simpa only [ht] using native.choiceInputsValid
  rw [ReferenceRankInstallationRecorderFastLaw.actualReservedFast_eq_of_view
    rate rewards C_star C_h t z.val native.selected.view
      (actualFirstCell_view rate rewards C_star C_h control0 t z) valid]
  unfold reservedFastArm ReferenceRankInstallationRecorderFastLaw.reservedFastAtView
  have hc := firstRecord_control rate rewards C_star C_h t z
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

private theorem measurable_firstPhysical : Measurable (fun z : Z =>
    ReferenceActiveHorizonMeasurability.roundRecordCode
      (firstRecord rate rewards C_star C_h t z)) := by
  apply measurable_of_some
  have h := (ReferenceCalendarActualControlCallbackSections.measurable_codeAt
    rate rewards C_star C_h t).comp (measurable_subtype_coe (p := fun z =>
      z ∈ ReferenceRankInstallationRecorderFoundation.installationEvent
        rate rewards C_star C_h 0 t))
  convert h using 1
  funext z
  simp only [Function.comp_apply, ReferenceCalendarActualControlCallbackSections.codeAt,
    (firstSourceCell_spec rate rewards C_star C_h t z).1, Option.map_some]

include control0 in
private theorem measurable_firstNumerical : Measurable (fun z : Z =>
    ReferenceLaterLiveReadoutValuesMeasurability.numericalCoordinates
      (firstSourceCell rate rewards C_star C_h t z).input) := by
  apply measurable_of_some
  have h := (ReferenceOriginalCalendarContinuingLiveRecorderLaw.measurable_actualNumerical
    rate rewards C_star C_h t).comp (measurable_subtype_coe (p := fun z =>
      z ∈ ReferenceRankInstallationRecorderFoundation.installationEvent
        rate rewards C_star C_h 0 t))
  convert h using 1
  funext z
  exact (actualFirstCell_numerical rate rewards C_star C_h control0 t z scalarZero).symm

private theorem measurable_firstBefore :
    Measurable (firstBefore rate rewards C_star C_h control0 t) := by
  have hc : Measurable (fun z : Z =>
      ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
        (firstBefore rate rewards C_star C_h control0 t z)) := by
    apply measurable_of_some
    have h := (ReferenceRankInstallationPostUpdateProposalLaw.measurable_actualInstallationNumericalBefore
      rate rewards C_star C_h control0 t).comp (measurable_subtype_coe (p := fun z =>
        z ∈ ReferenceRankInstallationRecorderFoundation.installationEvent
          rate rewards C_star C_h 0 t))
    convert h using 1
    funext z
    exact (firstBefore_spec rate rewards C_star C_h control0 t z).symm
  exact (measurable_of_countable (fun b :
    ReferenceRankInstallationPostUpdateProposalLaw.NumericalState p =>
      (⟨b.1, b.2.1, b.2.2⟩ : RecordedQueueRun.RunState p.K))).comp hc

include control0 in
private theorem measurable_firstView : Measurable (fun z : Z =>
    (firstSourceCell rate rewards C_star C_h t z).selected.view) := by
  apply measurable_of_some
  have h := (ReferenceRankInstallationRecorderFoundation.measurable_actualInstallationView
    rate rewards C_star C_h t).comp (measurable_subtype_coe (p := fun z =>
      z ∈ ReferenceRankInstallationRecorderFoundation.installationEvent
        rate rewards C_star C_h 0 t))
  convert h using 1
  funext z
  exact (actualFirstCell_view rate rewards C_star C_h control0 t z).symm

include control0 in
private theorem measurable_firstAnchor : Measurable (fun z : Z =>
    (firstSourceCell rate rewards C_star C_h t z).selected.view.payload.anchor) := by
  have hv := (comap_measurable
    (ReferenceDownReceptionMeasurability.choiceTimeViewObservation (p := p) (rate := rate))).comp
      (measurable_firstView rate rewards C_star C_h control0 t)
  exact AssignmentPayloadDerivedMeasurability.measurable_inputAnchor.comp (measurable_fst.comp hv)

include control0 in
private theorem measurable_firstSlowSet : Measurable (fun z : Z =>
    (firstSourceCell rate rewards C_star C_h t z).selected.view.payload.slowSet) := by
  have hv := (comap_measurable
    (ReferenceDownReceptionMeasurability.choiceTimeViewObservation (p := p) (rate := rate))).comp
      (measurable_firstView rate rewards C_star C_h control0 t)
  have hp := (comap_measurable
    (LaterAssignmentStartMeasurability.payloadObservation (p := p) (eta := rate.eta))).comp
      (measurable_fst.comp hv)
  have hs := measurable_fst.comp (measurable_snd.comp (measurable_snd.comp hp))
  apply measurable_to_countable'
  intro U
  have heq : {z : Z |
      (firstSourceCell rate rewards C_star C_h t z).selected.view.payload.slowSet = U} =
      {z : Z |
      (firstSourceCell rate rewards C_star C_h t z).selected.view.payload.slowSet.val = U.val} := by
    ext z
    exact Subtype.ext_iff
  change MeasurableSet {z : Z |
    (firstSourceCell rate rewards C_star C_h t z).selected.view.payload.slowSet = U}
  rw [heq]
  exact (measurableSet_singleton U.val).preimage hs

include control0 in
private theorem measurable_firstFast : Measurable (fun z : Z =>
    (reservedFastArm (firstRecord rate rewards C_star C_h t z)
      (firstSourceCell rate rewards C_star C_h t z)).val) := by
  apply measurable_to_countable'
  intro j
  have h := (ReferenceRankInstallationRecorderFastLaw.measurable_actualReservedFast
    rate rewards C_star C_h t).comp (measurable_subtype_coe (p := fun z =>
      z ∈ ReferenceRankInstallationRecorderFoundation.installationEvent
        rate rewards C_star C_h 0 t))
  have hf := (measurableSet_singleton (some j)).preimage h
  convert hf using 1
  ext z
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Function.comp_apply]
  rw [firstSourceCell_fast rate rewards C_star C_h control0 t z]
  simp only [Option.some.injEq]

/-- Joint Borel measurability in the actual source and its refresh scalar. -/
public theorem measurable_actualFirstCell : Measurable (fun v : Z × Scalar =>
    actualFirstCell rate rewards C_star C_h control0 t v.1 v.2) := by
  classical
  let X := Z × Scalar
  let native := fun v : X => firstSourceCell rate rewards C_star C_h t v.1
  let before := fun v : X => firstBefore rate rewards C_star C_h control0 t v.1
  let round := fun v : X => (native v).input
  let Q := ReferenceFirstLaunchNumericalCell.queueParameters rate
  have hb : Measurable before :=
    (measurable_firstBefore rate rewards C_star C_h control0 t).comp measurable_fst
  have hn : Measurable (fun v : X =>
      ReferenceLaterLiveReadoutValuesMeasurability.numericalCoordinates (round v)) :=
    (measurable_firstNumerical rate rewards C_star C_h control0 t).comp measurable_fst
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
    (measurable_firstSlowSet rate rewards C_star C_h control0 t).comp measurable_fst
  have hslow : Measurable (fun v : X => if (before v).overflow then frozenSlowSet p else
      (native v).selected.view.payload.slowSet) := measurable_const.ite hcut hs
  have hfast : Measurable (fun v : X => if (before v).overflow then frozenFastArm p else
      (reservedFastArm (firstRecord rate rewards C_star C_h t v.1) (native v)).val) :=
    measurable_const.ite hcut
      ((measurable_firstFast rate rewards C_star C_h control0 t).comp measurable_fst)
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
    ((measurable_firstAnchor rate rewards C_star C_h control0 t).comp measurable_fst)
    (fun v => (native v).selected.view.payload.anchor_pos) (fun v => v.2) measurable_snd
  have hnext : Measurable (fun v : X => if (before v).overflow then frozenSlowSet p else
      if proposal v then residualDraw rate (before v) (round v)
        (native v).selected.view.payload.anchor (native v).selected.view.payload.anchor_pos v.2
      else (native v).selected.view.payload.slowSet) :=
    measurable_const.ite hcut (hres.ite ((measurableSet_singleton true).preimage hp) hs)
  have ht : Measurable (fun _ : X => t) := measurable_const
  have hcode := ht.prodMk
    (((measurable_firstPhysical rate rewards C_star C_h t).comp measurable_fst).prodMk
      (hn.prodMk (hb.prodMk (hafter.prodMk (ha.prodMk
        (hservice.prodMk (hslow.prodMk (hfast.prodMk (hp.prodMk hnext)))))))))
  apply measurable_comap_iff.mpr
  convert hcode using 1
  funext v
  dsimp only [Function.comp_def, ReferenceFirstLiveChronologicalPrefixMeasurability.logicalCellProductCode,
    actualFirstCell, appendLogicalCell]
  rw [ReferenceFirstLivePostUpdateProposalLaw.completeRowProposalBit_eq_physicalProposalBit
    rate _ _ _ rfl, firstRecord_control rate rewards C_star C_h t v.1]
  simp only [Function.update_self, (firstSourceCell_spec rate rewards C_star C_h t v.1).2.1]
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
public theorem actualFirstCell_sampler (z : Z) :
    (ReferenceCalendarLaterSamplerPredictability.calendarParameters rate rewards C_star C_h t z.val).bind
      (fun theta => AssignmentParameterFibreKernel.successfulSlowSet p theta
        (ReferenceFirstCollectionSamplerOutputLaw.currentAssignmentVector t z.val)) =
      some (firstSourceCell rate rewards C_star C_h t z).selected.view.payload.slowSet := by
  let b := firstRecordIndex rate rewards C_star C_h t z
  let r := (records z.val)[b.val]
  have hdata := (ReferenceRankInstallationRecorderFoundation.installationEvent_recordingData
    rate rewards C_star C_h 0 t z.val z.property).choose_spec.choose_spec
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
  have hv := actualFirstCell_view rate rewards C_star C_h control0 t z
  rw [ReferenceRankInstallationPostUpdateProposalLaw.installationEvent_actualView_dispatchProjection
    rate rewards C_star C_h control0 0 t z.val z.property,
    (firstSourceCell_spec rate rewards C_star C_h t z).1] at hv
  change (ReferenceActivePhysicalStep.dispatch r.input).downView = _ at hv
  rw [← hprep, hprepared] at hv
  simp only [ReferenceActivePhysicalStep.DispatchCut.downView, ReferenceActivePhysicalStep.DispatchCut.selection,
    ReferenceActivePhysicalStep.selectionAt, dite_eq_left htime, Option.map_some] at hv
  have hvslow := congrArg (fun v : ReferenceDownReception.ChoiceTimeView p rate.eta => v.payload.slowSet)
    (Option.some.inj hv)
  have hscalar := firstRecord_control rate rewards C_star C_h t z
  have hvector : ReferenceFirstCollectionSamplerOutputLaw.currentAssignmentVector t z.val =
      LaterAssignmentStartOperation.ownAssignmentVector r.input.row instruction.time := by
    rw [htime]
    exact congrArg (fun c : ContinuousLearningRows.TimeControl p =>
      ContinuousControlSlice.assignmentVector c.1) hscalar.symm
  rw [ReferenceCalendarLaterSamplerPredictability.calendarParameters,
    (firstSourceCell_spec rate rewards C_star C_h t z).1, Option.bind_some]
  change (ReferenceLaterAssignmentFibreStep.parameters? r.input).bind _ = _
  rw [ReferenceLaterAssignmentFibreStep.parameters?_eq_physicalDispatch, ← hprep, hprepared]
  change (LaterAssignmentStartMeasurability.selectedSamplerParameters? P
    ⟨_, instruction, consistent⟩).bind _ = _
  rw [hvector]
  exact (successfulStart_parameter_sample P _ instruction r.input.row consistent output hlocal hresult).trans
    (congrArg some (output.payload_slowSet.symm.trans
      ((congrArg AssignmentStartPayload.Input.slowSet hpayload).symm.trans hvslow)))

/-- Pointwise reconstruction of the actual source pair and whole-arm update.
The reconstruction retains the current vector and replaces only its physical
remainder; it supplies no conditional-law premise. -/
public theorem actualFirstCell_pairUpdate_reconstruction (z : Z) :
    (ReferenceRankInstallationRecorderFastLaw.actualMarkerReservedFast
        rate rewards C_star C_h t z.val,
      ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationNumericalUpdate
        rate rewards C_star C_h control0 t z.val) =
    ReferenceRankInstallationCommonUpdateJointLaw.reconstructedPairUpdate
      rate rewards C_star C_h control0 t
      (ReferenceRankInstallationRecorderFoundation.history rate rewards C_star C_h control0 0 t z.val)
      (currentRemainder t z.val) := by
  obtain ⟨v, valid, hv, hall⟩ :=
    ReferenceRankInstallationCommonUpdateJointLaw.reconstructedObserver_eq_commonReadout
      rate rewards C_star C_h control0 0 t z.val z.property
  have hp := ReferenceRankInstallationRecorderFastSourceLaw.actualPair_eq_historyRemainder_of_installation
    rate rewards C_star C_h control0 0 t z.val z.property
  have hu := ReferenceRankInstallationCommonUpdateJointLaw.actualInstallationNumericalUpdate_eq_updateFromPair
    rate rewards C_star C_h control0 0 t z.val z.property v hv
  have hr := congrArg (fun o : ReferenceRankInstallationPostUpdateProposalLaw.Observer p rate.eta => o.2.2)
    (hall (currentRemainder t z.val)).2
  change (_, _) = (_, _)
  apply Prod.ext hp
  exact hu.trans ((congrArg
    (ReferenceRankInstallationCommonUpdateJointLaw.updateFromPair rate rewards t v
      (ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationNumericalBefore
        rate rewards C_star C_h control0 t z.val)) hp).trans hr.symm)

/-- At the source-derived view and PRE state, the reconstructed remainder
law is exactly the correlated common-update kernel. In particular the two
finite coordinates are not replaced by a product of their marginals. -/
public theorem actualFirstCell_commonUpdateKernel (z : Z) :
    (ReferenceLaterOptionalControlResampling.controlRemainderLaw p).map
      (ReferenceRankInstallationCommonUpdateJointLaw.reconstructedPairUpdate
        rate rewards C_star C_h control0 t
        (ReferenceRankInstallationRecorderFoundation.history
          rate rewards C_star C_h control0 0 t z.val)) =
    ReferenceRankInstallationCommonUpdateJointLaw.commonUpdateKernel rate rewards t
      (firstSourceCell rate rewards C_star C_h t z).selected.view
      (ReferenceRankInstallationRecorderFastLaw.actualInstallationView_valid
        rate rewards C_star C_h t z.val _
        (actualFirstCell_view rate rewards C_star C_h control0 t z))
      (ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationNumericalBefore
        rate rewards C_star C_h control0 t z.val) := by
  classical
  let H := ReferenceRankInstallationRecorderFoundation.history
    rate rewards C_star C_h control0 0 t z.val
  let f := ReferenceRankInstallationCommonUpdateJointLaw.reconstructedPairUpdate
    rate rewards C_star C_h control0 t H
  have hrec : Measurable (fun q : ReferenceRankInstallationCommonUpdateJointLaw.History p ×
      ReferenceRankInstallationCommonUpdateJointLaw.Remainder p =>
      ReferenceRankInstallationCommonUpdateJointLaw.reconstructedPairUpdate
        rate rewards C_star C_h control0 t q.1 q.2) :=
    ReferenceRankInstallationCommonUpdateJointLaw.measurable_reconstructedPairUpdate
      rate rewards C_star C_h control0 t
  have hf : Measurable f := Measurable.of_uncurry_left
    (f := ReferenceRankInstallationCommonUpdateJointLaw.reconstructedPairUpdate
      rate rewards C_star C_h control0 t) (x := H) hrec
  apply Measure.ext
  intro B hB
  rw [Measure.map_apply hf hB]
  calc
    _ = ∫⁻ d, if f d ∈ B then 1 else 0
        ∂ReferenceLaterOptionalControlResampling.controlRemainderLaw p := by
      simpa only [Set.indicator_apply, Set.mem_preimage, Pi.one_apply] using
        (lintegral_indicator_one (hB.preimage hf)).symm
    _ = _ := ReferenceRankInstallationCommonUpdateJointLaw.sourceLawCommonUpdateTestCoefficient_eq_kernel
      rate rewards C_star C_h control0 0 t z.val z.property _ _
      (actualFirstCell_view rate rewards C_star C_h control0 t z) B hB

/-- The literal first-rank history reconstructed from the retained strict
source prefix and the inserted whole vector. -/
public def firstHistory (v : BootstrapPrivateRoundStreams.SourceInput p × Vector p) :
    ReferenceRankInstallationRecorderFoundation.History p := (v.1, ([], v.2))

public theorem measurable_firstHistory : Measurable (firstHistory (p := p)) :=
  measurable_fst.prodMk (measurable_const.prodMk measurable_snd)

/-- The inserted source remains the same actual first invocation. -/
public def nonrenewedFirstSource (u : Fin p.T) (z : EventSource rate rewards C_star C_h u t)
    (v : Vector p) : Z := by
  let z' := insertEvent rate rewards C_star C_h u t z v
  refine ⟨z'.val, Set.mem_iUnion.mpr ⟨u, ?_⟩⟩
  apply (ReferenceCollectionRankCellPhysicalTransport.mem_rankCell_iff_exists_call
    rate rewards C_star C_h 0 u t z'.val).mpr
  obtain ⟨theta, _, _, hcall, _⟩ :=
    ReferenceFirstLiveCollectionPathJoin.firstLiveCollectionEvent_firstCall
      rate rewards C_star C_h u t z'.val z'.property
  exact ⟨theta, (ReferenceCollectionSamplerChronology.nthCollectionCall_zero
    rate rewards C_star C_h z'.val).trans hcall⟩

/-- The actual nonrenewed cell on the literal insertion lift. -/
public def nonrenewedFirstCell (u : Fin p.T) (wv : NonrenewedSample u) : Cell rate :=
  actualFirstCell rate rewards C_star C_h control0 t
    (nonrenewedFirstSource rate rewards C_star C_h t u wv.1.1 wv.2) (wv.1.2 (t, 1))

public theorem measurable_nonrenewedFirstSource (u : Fin p.T) : Measurable (fun zv : EventSource
      rate rewards C_star C_h u t × Vector p =>
      nonrenewedFirstSource rate rewards C_star C_h t u zv.1 zv.2) := by
  exact (((measurable_insertEvent rate rewards C_star C_h u t).subtype_val)).subtype_mk

public theorem measurable_nonrenewedFirstCell (u : Fin p.T) :
    Measurable (fun wv : NonrenewedSample u =>
        nonrenewedFirstCell rate rewards C_star C_h control0 t u wv) := by
  change Measurable ((fun zx : Z × Scalar =>
    actualFirstCell rate rewards C_star C_h control0 t zx.1 zx.2) ∘
    (fun wv : NonrenewedSample u =>
      (nonrenewedFirstSource rate rewards C_star C_h t u wv.1.1 wv.2,
      wv.1.2 (t, 1))))
  have hinit : Measurable (fun wv : (EventSource rate rewards C_star C_h u t × AuxArray p) ×
        Vector p =>
      (nonrenewedFirstSource rate rewards C_star C_h t u wv.1.1 wv.2, wv.1.2 (t, 1))) :=
    ((measurable_nonrenewedFirstSource rate rewards C_star C_h t u).comp
    (measurable_fst.fst.prodMk measurable_snd)).prodMk
    ((measurable_pi_apply (t, 1)).comp measurable_fst.snd)
  exact (measurable_actualFirstCell rate rewards C_star C_h control0 t).comp hinit

/-- The actual selected nonrenewed slow set is the endpoint of the SAME
old generated list, by actual sampler reconstruction and accepted fibre support. -/
public theorem ae_nonrenewedFirstCell_installedSlowSet (u : Fin p.T) :
    ∀ᵐ wv ∂nonrenewedLiftLaw rate rewards C_star C_h u t control0,
      some (firstSourceCell rate rewards C_star C_h t
        (nonrenewedFirstSource rate rewards C_star C_h t u wv.1.1 wv.2)).selected.view.payload.slowSet =
      (ReferenceFirstCollectionLogicalPrefixExtension.extendedPrefixStateAux rate rewards C_star C_h
        t.val (Nat.le_of_lt t.isLt) (wv.1.1.val, wv.1.2)).1 := by
  filter_upwards [ae_nonrenewedLiftLaw_endpoint rate rewards C_star C_h u t control0] with wv hend
  let z := nonrenewedFirstSource rate rewards C_star C_h t u wv.1.1 wv.2
  have hp := actualFirstCell_sampler rate rewards C_star C_h control0 t z
  have hpre := congrArg Prod.fst (nextInvocationPrefix_insertVector
      rate rewards C_star C_h t control0 wv.1.1.val wv.1.2 wv.2)
  change ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z.val =
    ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val wv.1.1.val at hpre
  rw [ReferenceCalendarLaterSamplerPredictability.calendarParameters_factor
    rate rewards C_star C_h control0 t z.val, hpre,
    nextParameter_spec, Option.bind_some] at hp
  have heq := hp.symm.trans hend
  exact heq.trans (generatedEndpoint_eq_path rate rewards C_star C_h u t wv.1.1 wv.1.2).symm

/-- The same complete old list and original label-zero array accompany the
produced cell; the insertion has not regenerated an independent past. -/
public theorem nonrenewedFirstCell_oldObservation (u : Fin p.T) (wv : NonrenewedSample u) :
    ReferenceFirstCollectionLogicalPrefixExtension.extendedObservation rate rewards C_star C_h
      control0 t.castSucc
      ((nonrenewedFirstSource rate rewards C_star C_h t u wv.1.1 wv.2).val, wv.1.2) =
      (nextInvocationObservation rate rewards C_star C_h u t control0 wv.1).1 :=
  nextInvocationPrefix_insertVector rate rewards C_star C_h t control0 wv.1.1.val wv.1.2 wv.2

/-- The actual nonrenewed cell with the SAME complete old observation and
inserted full source, factoring only its unused label-1 refresh scalar. -/
public theorem nonrenewedFirstCell_joint_test (u : Fin p.T)
    (Phi : ReferenceFirstCollectionLogicalPrefixExtension.Observation rate ×
      (BootstrapPrivateRoundStreams.SourceInput p × Cell rate) → ℝ)
    (hPhi : Measurable Phi) (M : ℝ) (hbound : ∀ x, ‖Phi x‖ ≤ M) :
    (∫ wv, Phi ((nextInvocationObservation rate rewards C_star C_h u t control0 wv.1).1,
      ((nonrenewedFirstSource rate rewards C_star C_h t u wv.1.1 wv.2).val,
        nonrenewedFirstCell rate rewards C_star C_h control0 t u wv))
      ∂nonrenewedLiftLaw rate rewards C_star C_h u t control0) =
    ∫ bx, ∫ v, Phi ((nextInvocationObservation rate rewards C_star C_h u t control0
        (bx.1.1, insertActualRefreshCoordinate t bx.1.2 scalarZero)).1,
      ((nonrenewedFirstSource rate rewards C_star C_h t u bx.1.1 v).val,
        actualFirstCell rate rewards C_star C_h control0 t
          (nonrenewedFirstSource rate rewards C_star C_h t u bx.1.1 v) bx.2))
      ∂nonrenewedVectorKernel rate rewards C_star C_h u t control0
        (bx.1.1, insertActualRefreshCoordinate t bx.1.2 scalarZero)
      ∂((eventSourceLaw rate rewards C_star C_h u t).prod
        (erasedAuxiliaryLaw t)).prod scalarLaw := by
  let Z0 := EventSource rate rewards C_star C_h u t
  let E := ErasedAuxiliaryArray t
  let V := Vector p
  let X := ((Z0 × E) × V) × Scalar
  let restore := fun q : X => (q.1.1.1,
    insertActualRefreshCoordinate t q.1.1.2 scalarZero)
  let src := fun q : X => nonrenewedFirstSource rate rewards C_star C_h t u q.1.1.1 q.1.2
  let test := fun q : X => Phi
    ((nextInvocationObservation rate rewards C_star C_h u t control0
      (restore q)).1, ((src q).val, actualFirstCell rate rewards C_star C_h control0 t (src q) q.2))
  have hrestore : Measurable restore := measurable_fst.fst.fst.prodMk
    ((measurable_insertActualRefreshCoordinate t).comp
      (measurable_fst.fst.snd.prodMk measurable_const))
  have hsrc : Measurable src := (measurable_nonrenewedFirstSource rate rewards C_star C_h t u).comp
    (measurable_fst.fst.fst.prodMk measurable_fst.snd)
  have hcell := (measurable_actualFirstCell rate rewards C_star C_h control0 t).comp
    (hsrc.prodMk measurable_snd)
  have htest : Measurable test := hPhi.comp (((measurable_nextInvocationObservation
      rate rewards C_star C_h u t control0).comp hrestore).fst.prodMk
        ((measurable_subtype_coe.comp hsrc).prodMk hcell))
  have h := nonrenewedRefreshScalar_vector_joint_test rate rewards C_star C_h u t control0
    test htest M (fun _ => hbound _)
  refine Eq.trans ?_ h
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun wv => by
    let split := actualRefreshScalarSplit t wv.1.2
    have hr : wv.1.2 = insertActualRefreshCoordinate t split.1 split.2 := by
      exact ((actualRefreshScalarSplit t).symm_apply_apply wv.1.2).symm.trans
        (actualRefreshScalarSplit_symm_apply t split)
    have ho := nextInvocationObservation_refreshScalar_ext rate rewards C_star C_h u t control0
      wv.1.1 split.1 split.2 scalarZero
    have hs : split.2 = wv.1.2 (t, 1) := by
      rw [hr]
      simp only [insertActualRefreshCoordinate, dite_true]
    have hobs0 := (congrArg (fun a => nextInvocationObservation
        rate rewards C_star C_h u t control0 (wv.1.1, a)) hr).trans ho
    have hobs1 := congrArg Prod.fst hobs0
    have hcell0 := congrArg (actualFirstCell rate rewards C_star C_h control0 t
      (nonrenewedFirstSource rate rewards C_star C_h t u wv.1.1 wv.2)) hs.symm
    exact congrArg Phi (Prod.ext hobs1 (Prod.ext rfl hcell0))

/-- The physical common update at the produced nonrenewed cell, jointly
with the SAME complete old observation, collection path and inserted vector.
Only the current remainder is factored. The outer law retains the original
unnormalized first-event mass. -/
public theorem nonrenewedFirstCell_physical_joint_test (u : Fin p.T)
    (Phi : (ReferenceFirstCollectionLogicalPrefixExtension.Observation rate ×
      ReferenceFirstLiveCollectionPathJoin.Path u t) ×
      (Vector p × ReferenceRankInstallationCommonUpdateJointLaw.PairUpdate p) → ℝ)
    (hPhi : Measurable Phi) (M : ℝ) (hbound : ∀ x, ‖Phi x‖ ≤ M) :
    (∫ wv : NonrenewedSample u, Phi (nextInvocationObservation
        rate rewards C_star C_h u t control0 wv.1,
      (wv.2, (ReferenceRankInstallationRecorderFastLaw.actualMarkerReservedFast
          rate rewards C_star C_h t
          (nonrenewedFirstSource rate rewards C_star C_h t u wv.1.1 wv.2).val,
        ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationNumericalUpdate
          rate rewards C_star C_h control0 t
          (nonrenewedFirstSource rate rewards C_star C_h t u wv.1.1 wv.2).val)))
      ∂nonrenewedLiftLaw rate rewards C_star C_h u t control0) =
    ∫ sr, ∫ v, Phi (sr.1.1, (v,
      ReferenceRankInstallationCommonUpdateJointLaw.reconstructedPairUpdate
        rate rewards C_star C_h control0 t (firstHistory (sr.1.1.1.1, v)) sr.2))
      ∂signatureVectorKernel rate u t sr.1
      ∂((nonrenewedBaseLaw rate rewards C_star C_h u t).map
        (signature rate rewards C_star C_h u t control0)).prod
        ((LaunchAssignmentCoordinateSplit.nonAssignmentScalarLaw p).prod
          (ContinuousLearningRows.affineSamplesLaw p)) := by
  let O := ReferenceFirstCollectionLogicalPrefixExtension.Observation rate ×
    ReferenceFirstLiveCollectionPathJoin.Path u t
  let V := Vector p
  let R := Remainder p
  let test : O × (V × R) → ℝ := fun q => Phi (q.1, (q.2.1,
    ReferenceRankInstallationCommonUpdateJointLaw.reconstructedPairUpdate
      rate rewards C_star C_h control0 t (firstHistory (q.1.1.1, q.2.1)) q.2.2))
  have hH : Measurable (fun q : O × (V × R) => firstHistory (q.1.1.1, q.2.1)) :=
    measurable_firstHistory.comp (measurable_fst.fst.fst.prodMk measurable_snd.fst)
  have hrec : Measurable (fun q : ReferenceRankInstallationCommonUpdateJointLaw.History p × R =>
      ReferenceRankInstallationCommonUpdateJointLaw.reconstructedPairUpdate
        rate rewards C_star C_h control0 t q.1 q.2) :=
    ReferenceRankInstallationCommonUpdateJointLaw.measurable_reconstructedPairUpdate
      rate rewards C_star C_h control0 t
  have hin : Measurable (fun q : O × (V × R) =>
      (firstHistory (q.1.1.1, q.2.1), q.2.2)) := hH.prodMk measurable_snd.snd
  have hcomposed := Measurable.comp (f := fun q : O × (V × R) =>
    (firstHistory (q.1.1.1, q.2.1), q.2.2)) hrec hin
  have hout : Measurable (fun q : O × (V × R) =>
      (q.1, (q.2.1, ReferenceRankInstallationCommonUpdateJointLaw.reconstructedPairUpdate
        rate rewards C_star C_h control0 t (firstHistory (q.1.1.1, q.2.1)) q.2.2))) :=
    measurable_fst.prodMk (measurable_snd.fst.prodMk hcomposed)
  have htest : Measurable test := hPhi.comp hout
  have h := nonrenewed_joint_test
    rate rewards C_star C_h u t control0 test htest M (fun _ => hbound _)
  refine Eq.trans ?_ h
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro wv
  let z := nonrenewedFirstSource rate rewards C_star C_h t u wv.1.1 wv.2
  have hobs := nonrenewedFirstCell_oldObservation rate rewards C_star C_h control0 t u wv
  have hprefix : ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z.val =
      (nextInvocationObservation
        rate rewards C_star C_h u t control0 wv.1).1.1 := congrArg Prod.fst hobs
  have hvector : ReferenceFirstCollectionSamplerOutputLaw.currentAssignmentVector t z.val = wv.2 :=
    ReferenceFirstCollectionRenewalVectorInsertion.av_insert t wv.1.1.val wv.2
  have hHactual : ReferenceRankInstallationRecorderFoundation.history
      rate rewards C_star C_h control0 0 t z.val =
      firstHistory ((nextInvocationObservation
        rate rewards C_star C_h u t control0 wv.1).1.1, wv.2) := by
    change (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z.val,
      ([], ReferenceFirstCollectionSamplerOutputLaw.currentAssignmentVector t z.val)) = _
    rw [hvector, hprefix]
    rfl
  have hrem : currentRemainder t z.val = currentRemainder t wv.1.1.val := by
    have h := congrArg Prod.snd (insertedVector_preserves_remainder_and_private t wv.1.1.val wv.2).1
    exact h
  have hactual := actualFirstCell_pairUpdate_reconstruction rate rewards C_star C_h control0 t z
  rw [hHactual, hrem] at hactual
  exact congrArg (fun q => Phi
    (nextInvocationObservation rate rewards C_star C_h u t control0 wv.1, (wv.2, q))) hactual

/-- The accepted renewed source is an actual first invocation. -/
public def renewedFirstSource (u : Fin p.T)
    (z : ReferenceFirstCollectionRenewalInstallationCoupling.Source
      rate rewards C_star C_h u t) : Z := by
  refine ⟨z.val, Set.mem_iUnion.mpr ⟨u, ?_⟩⟩
  apply (ReferenceCollectionRankCellPhysicalTransport.mem_rankCell_iff_exists_call
    rate rewards C_star C_h 0 u t z.val).mpr
  exact ⟨ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallParameter
      rate rewards C_star C_h u t z,
    (ReferenceCollectionSamplerChronology.nthCollectionCall_zero
      rate rewards C_star C_h z.val).trans
      (ReferenceFirstCollectionRenewalAuxiliaryLaw.firstCollectionCall_eq
        rate rewards C_star C_h u t z)⟩

/-- The actual renewal cell; label 1 initializes and label 0 refreshes. -/
public def renewedFirstCell (u : Fin p.T)
    (wv : ReferenceFirstCollectionRenewalInstallationCoupling.RenewalLift
      rate rewards C_star C_h u t) : Cell rate :=
  actualFirstCell rate rewards C_star C_h control0 t (renewedFirstSource rate rewards C_star C_h t u
      (ReferenceFirstCollectionRenewalInstallationCoupling.pair
        rate rewards C_star C_h u t wv).2) (wv.1.2 (t, 0))

public theorem measurable_renewedFirstSource (u : Fin p.T) :
    Measurable (renewedFirstSource rate rewards C_star C_h t u) :=
  measurable_subtype_coe.subtype_mk

public theorem measurable_renewedFirstCell (u : Fin p.T) :
    Measurable (fun wv : ReferenceFirstCollectionRenewalInstallationCoupling.RenewalLift
      rate rewards C_star C_h u t => renewedFirstCell rate rewards C_star C_h control0 t u wv) := by
  change Measurable ((fun zx : Z × Scalar =>
    actualFirstCell rate rewards C_star C_h control0 t zx.1 zx.2) ∘
    (fun wv => (renewedFirstSource rate rewards C_star C_h t u
      (ReferenceFirstCollectionRenewalInstallationCoupling.pair rate rewards C_star C_h u t wv).2,
      wv.1.2 (t, 0))))
  have hinit : Measurable (fun wv :
      ReferenceFirstCollectionRenewalInstallationCoupling.RenewalLift rate rewards C_star C_h u t =>
      (renewedFirstSource rate rewards C_star C_h t u
        (ReferenceFirstCollectionRenewalInstallationCoupling.pair rate rewards C_star C_h u t wv).2,
        wv.1.2 (t, 0))) :=
    ((measurable_renewedFirstSource rate rewards C_star C_h t u).comp
    (measurable_snd.comp (ReferenceFirstCollectionRenewalInstallationCoupling.measurable_pair
      rate rewards C_star C_h u t))).prodMk
    ((measurable_pi_apply (t, 0)).comp measurable_fst.snd)
  exact (measurable_actualFirstCell rate rewards C_star C_h control0 t).comp hinit

public theorem renewedFirstCell_oldObservation (u : Fin p.T)
    (wv : ReferenceFirstCollectionRenewalInstallationCoupling.RenewalLift
      rate rewards C_star C_h u t) :
    ReferenceFirstCollectionLogicalPrefixExtension.extendedObservation rate rewards C_star C_h
      control0 t.castSucc
      ((renewedFirstSource rate rewards C_star C_h t u
        (ReferenceFirstCollectionRenewalInstallationCoupling.pair
          rate rewards C_star C_h u t wv).2).val, wv.1.2) =
      ReferenceFirstCollectionLogicalPrefixExtension.extendedObservation rate rewards C_star C_h
        control0 t.castSucc (wv.1.1.val, wv.1.2) :=
  renewal_pair_oldObservation rate rewards C_star C_h u t control0 wv

/-- The complete old observation is a Borel readout of the retained renewal
coordinates and is the SAME generated list as before insertion. -/
public theorem renewedRetained_oldObservation (u : Fin p.T)
    (wv : ReferenceFirstCollectionRenewalInstallationCoupling.RenewalLift rate rewards C_star C_h u t) :
    ReferenceFirstCollectionLogicalPrefixExtension.extendedObservation rate rewards C_star C_h control0 t.castSucc
      (ReferenceFirstCollectionRenewalControlFactor.retainedControlCoordinates
        rate rewards C_star C_h u t control0
        (ReferenceFirstCollectionRenewalInstallationCoupling.pair rate rewards C_star C_h u t wv)).1.1 =
    ReferenceFirstCollectionLogicalPrefixExtension.extendedObservation rate rewards C_star C_h control0 t.castSucc
      (wv.1.1.val, wv.1.2) := by
  have hs := ReferenceFirstCollectionLogicalPrefixExtension.extendedPrefixStateAux_sourcePrefix
    rate rewards C_star C_h control0 t.val (Nat.le_of_lt t.isLt) wv.1.1.val wv.1.2
  have hl := congrArg Prod.snd hs
  have hp := ReferenceSourcePrefixHistoryFiltration.sourcePrefix_sourcePrefix
    control0 t.val t.val le_rfl wv.1.1.val
  exact Prod.ext hp (Prod.ext rfl hl.symm)

/-- Renewal retains the full auxiliary array and both assignment vectors.
The complete old list is read from the actual erased prefix; only the current
physical remainder is integrated against its original law. -/
public theorem renewedFirstCell_physical_joint_test (u : Fin p.T)
    (Phi : ReferenceFirstCollectionRenewalControlFactor.RetainedCoordinates p ×
      ReferenceRankInstallationCommonUpdateJointLaw.PairUpdate p → ℝ)
    (hPhi : Measurable Phi) :
    (∫ wv, Phi
      (ReferenceFirstCollectionRenewalControlFactor.retainedControlCoordinates rate rewards C_star C_h u t control0
        (ReferenceFirstCollectionRenewalInstallationCoupling.pair rate rewards C_star C_h u t wv),
      (ReferenceRankInstallationRecorderFastLaw.actualMarkerReservedFast rate rewards C_star C_h t
        (ReferenceFirstCollectionRenewalInstallationCoupling.pair rate rewards C_star C_h u t wv).2.val,
        ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationNumericalUpdate rate rewards C_star C_h
          control0 t (ReferenceFirstCollectionRenewalInstallationCoupling.pair rate rewards C_star C_h u t wv).2.val))
      ∂ReferenceFirstCollectionRenewalInstallationCoupling.renewalLiftLaw rate rewards C_star C_h u t) =
    ∫ q, Phi (q.1, ReferenceRankInstallationCommonUpdateJointLaw.reconstructedPairUpdate
      rate rewards C_star C_h control0 t (firstHistory (q.1.1.1.1, q.1.2)) q.2)
      ∂((ReferenceFirstCollectionRenewalInstallationCoupling.pairLaw rate rewards C_star C_h u t).map
        (ReferenceFirstCollectionRenewalControlFactor.retainedControlCoordinates rate rewards C_star C_h u t control0)).prod
        ((LaunchAssignmentCoordinateSplit.nonAssignmentScalarLaw p).prod
          (ContinuousLearningRows.affineSamplesLaw p)) := by
  let H := ReferenceFirstCollectionRenewalControlFactor.RetainedCoordinates p
  let R := Remainder p
  let retained := ReferenceFirstCollectionRenewalControlFactor.retainedControlCoordinates
    rate rewards C_star C_h u t control0
  let rem := ReferenceFirstCollectionRenewalControlFactor.insertedControlRemainder rate rewards C_star C_h u t
  let law := ReferenceFirstCollectionRenewalInstallationCoupling.pairLaw rate rewards C_star C_h u t
  let pair := ReferenceFirstCollectionRenewalInstallationCoupling.pair rate rewards C_star C_h u t
  have hvec : Measurable (ReferenceFirstCollectionRenewalVectorInsertion.av (p := p) t) :=
    (ContinuousControlSlice.measurable_assignmentVector p.m p.K).comp
      (ReferenceSourceCurrentControlFreshness.measurable_u_t t).fst
  have hret : Measurable retained :=
    ((((ReferenceSourceCurrentControlFreshness.measurable_c_t (p := p) control0 t).comp
      (measurable_subtype_coe.comp measurable_fst.fst)).prodMk measurable_fst.snd).prodMk
      (hvec.comp (measurable_subtype_coe.comp measurable_fst.fst))).prodMk
      (hvec.comp (measurable_subtype_coe.comp measurable_snd))
  have hrem : Measurable rem := (measurable_currentRemainder t).comp
    (measurable_subtype_coe.comp measurable_snd)
  let test : H × R → ℝ := fun q => Phi (q.1,
    ReferenceRankInstallationCommonUpdateJointLaw.reconstructedPairUpdate
      rate rewards C_star C_h control0 t (firstHistory (q.1.1.1.1, q.1.2)) q.2)
  have hH : Measurable (fun q : H × R => firstHistory (q.1.1.1.1, q.1.2)) :=
    measurable_firstHistory.comp (measurable_fst.fst.fst.fst.prodMk measurable_fst.snd)
  have hrec := ReferenceRankInstallationCommonUpdateJointLaw.measurable_reconstructedPairUpdate
    rate rewards C_star C_h control0 t
  have hread := Measurable.comp (f := fun q : H × R =>
    (firstHistory (q.1.1.1.1, q.1.2), q.2)) hrec (hH.prodMk measurable_snd)
  have htest : Measurable test := hPhi.comp (measurable_fst.prodMk hread)
  have hpair := ReferenceFirstCollectionRenewalInstallationCoupling.measurable_pair rate rewards C_star C_h u t
  have hmap := integral_map (μ := law) (hret.prodMk hrem).aemeasurable htest.aestronglyMeasurable
  rw [ReferenceFirstCollectionRenewalControlFactor.pairLaw_retained_nonAssignment_product
    rate rewards C_star C_h u t control0] at hmap
  have hmapPair := integral_map (μ := ReferenceFirstCollectionRenewalInstallationCoupling.renewalLiftLaw
    rate rewards C_star C_h u t) hpair.aemeasurable
    (htest.comp (hret.prodMk hrem)).aestronglyMeasurable
  change (∫ wv, _ ∂ReferenceFirstCollectionRenewalInstallationCoupling.renewalLiftLaw
    rate rewards C_star C_h u t) = _
  calc
    _ = ∫ wv, test (retained (pair wv), rem (pair wv))
        ∂ReferenceFirstCollectionRenewalInstallationCoupling.renewalLiftLaw rate rewards C_star C_h u t := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun wv => by
        let z := renewedFirstSource rate rewards C_star C_h t u (pair wv).2
        have hp := actualFirstCell_pairUpdate_reconstruction rate rewards C_star C_h control0 t z
        have ho := renewedFirstCell_oldObservation rate rewards C_star C_h control0 t u wv
        have hprefix := congrArg Prod.fst ho
        have hHactual : ReferenceRankInstallationRecorderFoundation.history rate rewards C_star C_h control0 0 t z.val =
            firstHistory ((retained (pair wv)).1.1.1, (retained (pair wv)).2) := by
          change (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z.val,
            ([], ReferenceFirstCollectionRenewalVectorInsertion.av t z.val)) = _
          exact Prod.ext hprefix rfl
        rw [hHactual] at hp
        exact congrArg (fun q => Phi (retained (pair wv), q)) hp
    _ = ∫ b, test (retained b, rem b) ∂law := hmapPair.symm
    _ = _ := hmap.symm

include control0 in
/-- The accepted renewal fibre support identifies the actual selected
installation payload with the SAME original label-1 auxiliary initial draw.
This precedes the later label-0 residual refresh and is not the old endpoint. -/
public theorem ae_renewedFirstCell_installedSlowSet (u : Fin p.T) :
    ∀ᵐ wv ∂ReferenceFirstCollectionRenewalInstallationCoupling.renewalLiftLaw
        rate rewards C_star C_h u t,
      (firstSourceCell rate rewards C_star C_h t (renewedFirstSource rate rewards C_star C_h t u
          (ReferenceFirstCollectionRenewalInstallationCoupling.pair
            rate rewards C_star C_h u t wv).2)).selected.view.payload.slowSet =
      ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalAuxiliarySample
        rate rewards C_star C_h u t wv.1.1 wv.1.2 := by
  have hs := ae_of_ae_map (ReferenceFirstCollectionRenewalInstallationCoupling.measurable_pair
      rate rewards C_star C_h u t).aemeasurable
    (ReferenceFirstCollectionRenewalInstallationCoupling.ae_pairLaw_actual_installation
      rate rewards C_star C_h u t)
  filter_upwards [hs] with wv h
  dsimp only at h
  obtain ⟨d, consistent, output, hlocal, hresult, hvector, hrec, hsample,
    hslow, hpayloadSlow, hinstalledPayload, hinstalledVector, hinstalledRec,
    hanchor, hqueues, hbase, hinstalledSlow, selection, hchoice, hdispatch,
    hprep, hcoord, htail⟩ := h
  let z := renewedFirstSource rate rewards C_star C_h t u
    (ReferenceFirstCollectionRenewalInstallationCoupling.pair rate rewards C_star C_h u t wv).2
  obtain ⟨n, hn⟩ := List.mem_iff_getElem?.mp d.record_mem
  have hr := ReferenceFirstCollectionCurrentRemainderLaw.actualRecord_of_index
    rate rewards C_star C_h t z.val n d.record hn d.time_eq
  have hv := actualFirstCell_view rate rewards C_star C_h control0 t z
  rw [ReferenceRankInstallationPostUpdateProposalLaw.installationEvent_actualView_dispatchProjection
    rate rewards C_star C_h control0 0 t z.val z.property, hr] at hv
  change (ReferenceActivePhysicalStep.dispatch d.record.input).downView = _ at hv
  have hprepared : d.record.output.preparation.coordinator =
      ReferenceActivePhysicalStep.dispatch d.record.input := by
    rw [d.record.output_eq]
    rfl
  rw [← hprepared, hcoord, hdispatch] at hv
  simp only [ReferenceActivePhysicalStep.DispatchCut.downView,
    ReferenceActivePhysicalStep.DispatchCut.selection, ReferenceActivePhysicalStep.selectionAt,
    dite_eq_left d.instruction_time, Option.map_some] at hv
  have hp := congrArg (fun v : ReferenceDownReception.ChoiceTimeView p rate.eta =>
    v.payload.slowSet) (Option.some.inj hv)
  exact hp.symm.trans hinstalledSlow

/-- Reindex only the two current auxiliary coordinates before using the
accepted label-1 scalar split. Thus the scalar of this split is original
label 0; the retained array still contains original label 1. -/
public def renewalRefreshScalarSplit : AuxArray p ≃ᵐ ErasedAuxiliaryArray t × Scalar :=
  (MeasurableEquiv.piCongrLeft (fun _ : Fin p.T × Fin 2 => Scalar)
    (Equiv.swap (t, 0) (t, 1))).trans
    (actualRefreshScalarSplit t)

public theorem measurePreserving_renewalRefreshScalarSplit :
    MeasurePreserving (renewalRefreshScalarSplit (p := p) t)
      (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p)
      ((erasedAuxiliaryLaw t).prod scalarLaw) := by
  exact (measurePreserving_actualRefreshScalarSplit t).comp
    (measurePreserving_piCongrLeft (fun _ : Fin p.T × Fin 2 => scalarLaw)
      (Equiv.swap (t, 0) (t, 1)))

public def insertRenewalRefreshScalar (e : ErasedAuxiliaryArray t) (x : Scalar) : AuxArray p :=
  (renewalRefreshScalarSplit t).symm (e, x)

private theorem insertRenewalRefreshScalar_apply (e : ErasedAuxiliaryArray t) (x : Scalar)
    (q : Fin p.T × Fin 2) :
    insertRenewalRefreshScalar t e x q = insertActualRefreshCoordinate t e x
        (Equiv.swap (t, 0) (t, 1) q) := by
  change (Equiv.piCongrLeft (fun _ : Fin p.T × Fin 2 => Scalar)
    (Equiv.swap (t, 0) (t, 1))).symm ((actualRefreshScalarSplit t).symm (e, x)) q = _
  rw [Equiv.piCongrLeft_symm_apply, actualRefreshScalarSplit_symm_apply]

public theorem insertRenewalRefreshScalar_current (e : ErasedAuxiliaryArray t) (x : Scalar) :
    insertRenewalRefreshScalar t e x (t, 0) = x := by
  rw [insertRenewalRefreshScalar_apply]
  simp only [Equiv.swap_apply_left, insertActualRefreshCoordinate, dite_true]

/-- The complete old logical list uses only strictly earlier auxiliary
coordinates. In contrast, its whole label-zero array cannot be retained when
claiming freshness of `(t,0)`. -/
public theorem renewalPast_refreshScalar_ext (u : Fin p.T)
    (z : ReferenceFirstCollectionRenewalInstallationCoupling.Source rate rewards C_star C_h u t)
    (e : ErasedAuxiliaryArray t) (x y : Scalar) :
    ReferenceFirstCollectionLogicalPrefixExtension.extendedPast rate rewards C_star C_h
      t.castSucc (z.val, insertRenewalRefreshScalar t e x) =
      ReferenceFirstCollectionLogicalPrefixExtension.extendedPast rate rewards C_star C_h
        t.castSucc (z.val, insertRenewalRefreshScalar t e y) := by
  apply congrArg Prod.snd
    (ReferenceFirstCollectionLogicalPrefixExtension.extendedPrefixStateAux_auxiliary_ext
      rate rewards C_star C_h t.val (Nat.le_of_lt t.isLt) z.val _ _ ?_)
  intro v hv l
  rw [insertRenewalRefreshScalar_apply, insertRenewalRefreshScalar_apply]
  have hne : Equiv.swap (t, 0) (t, 1) (v, l) ≠ (t, 1) := by
    intro h
    have he := (Equiv.swap (t, 0) (t, 1)).injective
      (h.trans (Equiv.swap_apply_left (t, 0) (t, 1)).symm)
    have ht : v = t := congrArg Prod.fst he
    subst v
    omega
  simp only [insertActualRefreshCoordinate, hne, dite_false]

/-- The actual renewal fibre uses `(t,1)` for its initial draw and therefore
does not depend on `(t,0)`, the later refresh scalar. -/
public theorem renewalKernel_refreshScalar_ext (u : Fin p.T)
    (z : ReferenceFirstCollectionRenewalInstallationCoupling.Source rate rewards C_star C_h u t)
    (e : ErasedAuxiliaryArray t) (x y : Scalar) :
    ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalAssignmentFibreKernel
      rate rewards C_star C_h u t (z, insertRenewalRefreshScalar t e x) =
      ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalAssignmentFibreKernel
        rate rewards C_star C_h u t (z, insertRenewalRefreshScalar t e y) := by
  rw [ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalAssignmentFibreKernel_apply,
    ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalAssignmentFibreKernel_apply]
  have hscalar : insertRenewalRefreshScalar t e x (t, 1) =
      insertRenewalRefreshScalar t e y (t, 1) := by
    rw [insertRenewalRefreshScalar_apply, insertRenewalRefreshScalar_apply]
    simp only [Equiv.swap_apply_right]
    have hne : (t, (0 : Fin 2)) ≠ (t, 1) := by simp
    simp only [insertActualRefreshCoordinate, hne, dite_false]
  simp only [ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalAuxiliarySample, hscalar]

/-- Unused label 0 is product-uniform under the literal unnormalized renewal
insertion composition, retaining the whole source, every other auxiliary
coordinate, and the inserted full assignment vector. -/
public theorem renewalRefreshScalar_vector_joint_test (u : Fin p.T)
    (Phi : (((ReferenceFirstCollectionRenewalInstallationCoupling.Source
      rate rewards C_star C_h u t ×
      ErasedAuxiliaryArray t) ×
      Vector p) × Scalar) → ℝ)
    (hPhi : Measurable Phi) (M : ℝ) (hbound : ∀ x, ‖Phi x‖ ≤ M) :
    (∫ wv, Phi (((wv.1.1, (renewalRefreshScalarSplit t wv.1.2).1), wv.2),
        (renewalRefreshScalarSplit t wv.1.2).2)
      ∂ReferenceFirstCollectionRenewalInstallationCoupling.renewalLiftLaw
        rate rewards C_star C_h u t) =
    ∫ bx, ∫ v, Phi ((bx.1, v), bx.2)
      ∂ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalAssignmentFibreKernel
        rate rewards C_star C_h u t
        (bx.1.1, insertRenewalRefreshScalar t bx.1.2 scalarZero)
      ∂((ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
        rate rewards C_star C_h u t).prod
        (erasedAuxiliaryLaw t)).prod scalarLaw := by
  exact splitKernel_joint_test
    (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t)
    (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p)
    (erasedAuxiliaryLaw t) (renewalRefreshScalarSplit t)
    (measurePreserving_renewalRefreshScalarSplit t)
    (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalAssignmentFibreKernel rate rewards C_star C_h u t)
    (renewalKernel_refreshScalar_ext rate rewards C_star C_h t u) Phi hPhi M hbound

/-- Reconstruct the actual renewal observation from the erased auxiliary
array, original source, inserted vector, and independent label-0 scalar. -/
public def renewedErasedCellReadout (u : Fin p.T)
    (q : (((ReferenceFirstCollectionRenewalInstallationCoupling.Source
      rate rewards C_star C_h u t × ErasedAuxiliaryArray t) ×
      Vector p) × Scalar)) :
    List (Cell rate) × (BootstrapPrivateRoundStreams.SourceInput p × Cell rate) :=
  let z' := ReferenceFirstCollectionRenewalVectorInsertion.put rate rewards C_star C_h u t q.1.1.1 q.1.2
  (ReferenceFirstCollectionLogicalPrefixExtension.extendedPast rate rewards C_star C_h
    t.castSucc (q.1.1.1.val, insertRenewalRefreshScalar t q.1.1.2 scalarZero),
    (z'.val, actualFirstCell rate rewards C_star C_h control0 t
      (renewedFirstSource rate rewards C_star C_h t u z') q.2))

public theorem measurable_renewedErasedCellReadout (u : Fin p.T) :
    Measurable (fun q : (((ReferenceFirstCollectionRenewalInstallationCoupling.Source
      rate rewards C_star C_h u t × ErasedAuxiliaryArray t) ×
      Vector p) × Scalar) =>
      renewedErasedCellReadout rate rewards C_star C_h control0 t u q) := by
  let RZ := ReferenceFirstCollectionRenewalInstallationCoupling.Source rate rewards C_star C_h u t
  let E := ErasedAuxiliaryArray t
  let X := ((RZ × E) × Vector p) × Scalar
  let put := fun q : X => ReferenceFirstCollectionRenewalVectorInsertion.put
    rate rewards C_star C_h u t q.1.1.1 q.1.2
  let src := fun q : X => renewedFirstSource rate rewards C_star C_h t u (put q)
  let old := fun q : X => ReferenceFirstCollectionLogicalPrefixExtension.extendedPast
    rate rewards C_star C_h t.castSucc (q.1.1.1.val, insertRenewalRefreshScalar t q.1.1.2
      scalarZero)
  have hcoords : Measurable (fun q : X => (q.1.1.1, q.1.2)) :=
    measurable_fst.fst.fst.prodMk measurable_fst.snd
  have hput : Measurable put :=
    (ReferenceFirstCollectionRenewalVectorInsertion.measurable_put rate rewards C_star C_h u t).comp
      hcoords
  have hsrc : Measurable src :=
    (measurable_renewedFirstSource rate rewards C_star C_h t u).comp hput
  have hobs : Measurable (fun q : X => (q.1.1.1.val,
      insertRenewalRefreshScalar t q.1.1.2 scalarZero)) :=
    (measurable_subtype_coe.comp measurable_fst.fst.fst).prodMk
      ((renewalRefreshScalarSplit t).symm.measurable.comp
        (measurable_fst.fst.snd.prodMk measurable_const))
  have hold : Measurable old :=
    (ReferenceFirstCollectionLogicalPrefixExtension.measurable_extendedPast
      rate rewards C_star C_h control0 t.castSucc).comp hobs
  have hreadout := hold.prodMk ((measurable_subtype_coe.comp hput).prodMk
    ((measurable_actualFirstCell rate rewards C_star C_h control0 t).comp
      (hsrc.prodMk measurable_snd)))
  simpa only [renewedErasedCellReadout, old, put, src, Function.comp_apply] using hreadout

public theorem renewedErasedCellReadout_actual (u : Fin p.T)
    (wv : ReferenceFirstCollectionRenewalInstallationCoupling.RenewalLift
      rate rewards C_star C_h u t) :
    renewedErasedCellReadout rate rewards C_star C_h control0 t u
      (((wv.1.1, (renewalRefreshScalarSplit t wv.1.2).1), wv.2),
        (renewalRefreshScalarSplit t wv.1.2).2) =
      (ReferenceFirstCollectionLogicalPrefixExtension.extendedPast rate rewards C_star C_h
        t.castSucc (wv.1.1.val, wv.1.2),
        ((ReferenceFirstCollectionRenewalInstallationCoupling.pair
          rate rewards C_star C_h u t wv).2.val,
          renewedFirstCell rate rewards C_star C_h control0 t u wv)) := by
  let s := renewalRefreshScalarSplit t wv.1.2
  have hr : wv.1.2 = insertRenewalRefreshScalar t s.1 s.2 :=
    ((renewalRefreshScalarSplit t).symm_apply_apply wv.1.2).symm
  have hs : s.2 = wv.1.2 (t, 0) := by
    calc
      s.2 = insertRenewalRefreshScalar t s.1 s.2 (t, 0) :=
        (insertRenewalRefreshScalar_current t s.1 s.2).symm
      _ = _ := congrFun hr.symm (t, 0)
  have hpast : ReferenceFirstCollectionLogicalPrefixExtension.extendedPast rate rewards C_star C_h
      t.castSucc (wv.1.1.val, wv.1.2) =
      ReferenceFirstCollectionLogicalPrefixExtension.extendedPast rate rewards C_star C_h
        t.castSucc (wv.1.1.val, insertRenewalRefreshScalar t s.1 scalarZero) := by
    calc
      _ = ReferenceFirstCollectionLogicalPrefixExtension.extendedPast rate rewards C_star C_h
          t.castSucc (wv.1.1.val, insertRenewalRefreshScalar t s.1 s.2) :=
        congrArg (fun a => ReferenceFirstCollectionLogicalPrefixExtension.extendedPast
          rate rewards C_star C_h t.castSucc (wv.1.1.val, a)) hr
      _ = _ := renewalPast_refreshScalar_ext rate rewards C_star C_h t u wv.1.1 s.1 s.2 scalarZero
  dsimp only [renewedErasedCellReadout, renewedFirstCell,
    ReferenceFirstCollectionRenewalInstallationCoupling.pair]
  rw [← hpast, hs]

/-- The produced renewal cell jointly with the SAME complete old list and
inserted full source. The factored scalar is original `(t,0)`; the complete
label-zero array is deliberately absent from this retained observation. -/
public theorem renewedFirstCell_joint_test (u : Fin p.T)
    (Phi : List (Cell rate) × (BootstrapPrivateRoundStreams.SourceInput p × Cell rate) → ℝ)
    (hPhi : Measurable Phi) (M : ℝ) (hbound : ∀ x, ‖Phi x‖ ≤ M) :
    (∫ wv : ReferenceFirstCollectionRenewalInstallationCoupling.RenewalLift
      rate rewards C_star C_h u t, Phi
      (ReferenceFirstCollectionLogicalPrefixExtension.extendedPast rate rewards C_star C_h
        t.castSucc (wv.1.1.val, wv.1.2),
        ((ReferenceFirstCollectionRenewalInstallationCoupling.pair
          rate rewards C_star C_h u t wv).2.val,
          renewedFirstCell rate rewards C_star C_h control0 t u wv))
      ∂ReferenceFirstCollectionRenewalInstallationCoupling.renewalLiftLaw
        rate rewards C_star C_h u t) =
    ∫ bx : (ReferenceFirstCollectionRenewalInstallationCoupling.Source rate rewards C_star C_h u t ×
      ErasedAuxiliaryArray t) × Scalar,
      ∫ v : Vector p,
      Phi (renewedErasedCellReadout rate rewards C_star C_h control0 t u ((bx.1, v), bx.2))
      ∂ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalAssignmentFibreKernel
        rate rewards C_star C_h u t (bx.1.1, insertRenewalRefreshScalar t bx.1.2 scalarZero)
      ∂((ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
        rate rewards C_star C_h u t).prod
        (erasedAuxiliaryLaw t)).prod scalarLaw := by
  let test := Phi ∘ renewedErasedCellReadout rate rewards C_star C_h control0 t u
  have htest : Measurable test := hPhi.comp
    (measurable_renewedErasedCellReadout rate rewards C_star C_h control0 t u)
  have h := renewalRefreshScalar_vector_joint_test rate rewards C_star C_h t u
    test htest M (fun _ => hbound _)
  refine Eq.trans ?_ h
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun wv =>
    (congrArg Phi (renewedErasedCellReadout_actual rate rewards C_star C_h control0 t u wv)).symm

/-- A total calendar-boundary readout. At the terminal boundary no `Fin T`
coordinate is constructed. Off the actual first-invocation event it is absent. -/
public def actualFirstCell? (n : Fin (p.T + 1))
    (zx : BootstrapPrivateRoundStreams.SourceInput p × Scalar) : Option (Cell rate) := by
  classical
  exact if hn : n.val < p.T then
    if hz : zx.1 ∈ ReferenceRankInstallationRecorderFoundation.installationEvent
        rate rewards C_star C_h 0 ⟨n.val, hn⟩ then
      some (actualFirstCell rate rewards C_star C_h control0 ⟨n.val, hn⟩ ⟨zx.1, hz⟩ zx.2)
    else none
  else none

public theorem measurable_actualFirstCell? (n : Fin (p.T + 1)) :
    Measurable (actualFirstCell? rate rewards C_star C_h control0 n) := by
  classical
  change Measurable (fun zx : BootstrapPrivateRoundStreams.SourceInput p × Scalar =>
    actualFirstCell? rate rewards C_star C_h control0 n zx)
  by_cases hn : n.val < p.T
  · let q : Fin p.T := ⟨n.val, hn⟩
    let E : Set (BootstrapPrivateRoundStreams.SourceInput p × Scalar) :=
      {zx | zx.1 ∈ ReferenceRankInstallationRecorderFoundation.installationEvent
        rate rewards C_star C_h 0 q}
    have hE : MeasurableSet E :=
      (ReferenceRankInstallationRecorderFoundation.measurableSet_installationEvent
        rate rewards C_star C_h control0 0 q).preimage measurable_fst
    have hi : Measurable (fun w : E =>
        ((⟨w.val.1, w.property⟩ : FirstInvocationSource rate rewards C_star C_h q), w.val.2)) :=
      (measurable_fst.comp measurable_subtype_coe).subtype_mk.prodMk
        (measurable_snd.comp measurable_subtype_coe)
    have hc := LaterAssignmentFullOutputMeasurability.measurable_some_of_measurable _
      ((measurable_actualFirstCell rate rewards C_star C_h control0 q).comp hi)
    simpa only [actualFirstCell?, dite_eq_left hn, q, E, Function.comp_apply, Set.mem_ofPred_eq] using
      hc.dite (measurable_const (a := (none : Option (Cell rate)))) hE
  · simp only [actualFirstCell?, dite_eq_right hn]
    exact measurable_const

public theorem actualFirstCell?_terminal (n : Fin (p.T + 1)) (hn : p.T ≤ n.val)
    (zx : BootstrapPrivateRoundStreams.SourceInput p × Scalar) :
    actualFirstCell? rate rewards C_star C_h control0 n zx = none := by
  simp only [actualFirstCell?, dite_eq_right (not_lt_of_ge hn)]

end ActualFirstInvocation

end Bandits.Support.ReferenceFirstNextInstallationCellFactors

end
