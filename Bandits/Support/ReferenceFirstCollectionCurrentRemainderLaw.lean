/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionCurrentPhysicalConditionalLaw
public import Bandits.Support.ReferenceFirstCollectionRenewalSourceCurrentPrefix

/-!
# Actual first-call observations with the whole assignment vector fixed

The source is the original strict prefix with its current control rebuilt from
the entire assignment vector and the original remainder carrier. Optional
observations retain the distinction between absence and a present bottom mark.

Sources: `05_binary_transport.tex:354-431`, `06_interruptions.tex:391-426`,
`04_slow_fast_learner.tex:140-188`, and `appendix_a_local_protocol.tex:28-79`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped Classical ENNReal BigOperators

namespace Bandits.Support.ReferenceFirstCollectionCurrentRemainderLaw

open ConstructorDimensions (Parameters)
open ReferenceActivePhysicalStep (RateInput)
open ActualInitializationPhysicalStep (GridRewardTable selectedRowIndex)
open BootstrapPrivateRoundStreams (SourceInput)
open ContinuousLearningRows (TimeControl)
open AssignmentParameterFibreKernel (AssignmentVector)
open ReferenceLaterOptionalControlResampling (ControlRemainder)

local instance sourceInputMeasurableSpace (p : Parameters) :
    MeasurableSpace (SourceInput p) := by
  change MeasurableSpace
    (CompletePublicTable.PublishedOutput p ×
      BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

local instance startResultMeasurableSpace (p : Parameters) :
    MeasurableSpace (CoordinatorPhaseClock.StartRoundResult p) := ⊤

local instance startResultDiscrete (p : Parameters) :
    DiscreteMeasurableSpace (CoordinatorPhaseClock.StartRoundResult p) :=
  ⟨fun _ => trivial⟩

variable {p : Parameters}

/-- Reassemble the existing complete current control, without dropping any
assignment coordinate or any remainder coordinate. -/
def currentControl (v : AssignmentVector p) (w : ControlRemainder p) : TimeControl p :=
  (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p).symm (v, w)

/-- Replace the current control in the original strict prefix. -/
def currentSource (control0 : TimeControl p) (t : Fin p.T) (z : SourceInput p)
    (v : AssignmentVector p) (w : ControlRemainder p) : SourceInput p :=
  ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
    (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z)
    (currentControl v w)

/-- The actual selected view and clock result; only its chosen arm is omitted. -/
def currentParameters (rate : RateInput p) (rewards : GridRewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p) (t : Fin p.T)
    (z : SourceInput p) (v : AssignmentVector p) (w : ControlRemainder p) :
    Option (ReferenceDownReception.ChoiceTimeView p rate.eta ×
      CoordinatorPhaseClock.StartRoundResult p) :=
  (ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t
    (currentSource control0 t z v w)).bind fun r =>
      r.output.preparation.coordinator.selection.map fun s => (s.view, s.started)

/-- The actual later-chosen constructor test, retaining record absence. -/
def currentChosen (rate : RateInput p) (rewards : GridRewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p) (t : Fin p.T)
    (z : SourceInput p) (v : AssignmentVector p) (w : ControlRemainder p) : Option Bool :=
  (ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t
    (currentSource control0 t z v w)).map fun r =>
      ReferenceCollectionPhaseHistory.laterChosen r.input

/-- The literal actual optional current recording mark. The outer option
records numerical-cell presence; the inner option records the bottom outcome. -/
def currentMarker (rate : RateInput p) (rewards : GridRewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p) (t : Fin p.T)
    (z : SourceInput p) (v : AssignmentVector p) (w : ControlRemainder p) :
    Option (Option (Fin p.K)) :=
  let source := currentSource control0 t z v w
  (ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t
    source).bind fun r =>
      (ReferenceLaterLiveNumericalReadout.laterLiveReadout
        (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h) r).map
          fun cell => cell.recordedArm

theorem currentControl_measurable :
    Measurable (fun q : AssignmentVector p × ControlRemainder p =>
      currentControl q.1 q.2) :=
  (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p).symm.measurable

theorem currentSource_measurable (control0 : TimeControl p) (t : Fin p.T)
    (z : SourceInput p) :
    Measurable (fun q : AssignmentVector p × ControlRemainder p =>
      currentSource control0 t z q.1 q.2) :=
  (ReferenceSourcePhysicalFlagConditionalLaw.measurable_replaceSourceControl p t).comp
    (measurable_const.prodMk currentControl_measurable)

/-- The literal reconstruction is precisely a selected suffix replacement
with the original fixed continuation after the current time. -/
theorem currentSource_eq_suffix (control0 : TimeControl p) (t : Fin p.T)
    (z : SourceInput p) (v : AssignmentVector p) (w : ControlRemainder p) :
    currentSource control0 t z v w =
      ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix z t
        (fun s => if s = t then currentControl v w else control0) := by
  apply Prod.ext
  · refine Prod.ext rfl ?_
    funext q
    by_cases hq : q = selectedRowIndex p z
    · subst q
      simp only [currentSource, ReferenceFixedTimeSourceControlCoupling.replaceSourceControl,
        ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex,
        ReferenceSourcePrefixHistoryFiltration.sourcePrefix,
        ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix,
        selectedRowIndex, Function.update_self]
      refine Prod.ext rfl ?_
      funext s
      by_cases hs : s = t
      · subst s
        simp
      · simp only [Function.update_of_ne hs, hs, ite_false]
    · simp only [currentSource, ReferenceFixedTimeSourceControlCoupling.replaceSourceControl,
        ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex,
        ReferenceSourcePrefixHistoryFiltration.sourcePrefix,
        ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix,
        selectedRowIndex] at hq ⊢
      simp only [Function.update_of_ne hq]
  · rfl

/-- Every original private array and its original selecting scalar are retained. -/
theorem currentSource_private (control0 : TimeControl p) (t : Fin p.T)
    (z : SourceInput p) (v : AssignmentVector p) (w : ControlRemainder p) :
    (currentSource control0 t z v w).2 = z.2 := rfl

/-- All `K+1` actual assignment coordinates are exactly the fixed vector. -/
theorem currentSource_assignmentVector (control0 : TimeControl p) (t : Fin p.T)
    (z : SourceInput p) (v : AssignmentVector p) (w : ControlRemainder p) :
    ReferenceFirstCollectionSamplerOutputLaw.currentAssignmentVector t
      (currentSource control0 t z v w) = v := by
  have h := congrArg Prod.fst
    ((LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p).apply_symm_apply (v, w))
  change (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p
    (currentControl v w)).1 = v at h
  convert h using 1
  funext j
  simp [ReferenceFirstCollectionSamplerOutputLaw.currentAssignmentVector,
    ReferenceSourceCurrentControlFreshness.u_t, currentSource,
    ReferenceFixedTimeSourceControlCoupling.replaceSourceControl,
    ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex,
    ReferenceSourcePrefixHistoryFiltration.sourcePrefix, selectedRowIndex,
    LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv,
    LaunchAssignmentCoordinateSplit.sliceAssignmentSplitEquiv,
    LaunchAssignmentCoordinateSplit.assignmentLabelEquiv_apply_val,
    ContinuousControlSlice.assignmentVector, MeasurableEquiv.piEquivPiSubtypeProd,
    Equiv.piEquivPiSubtypeProd, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft,
    MeasurableEquiv.prodAssoc, MeasurableEquiv.prodCongr, Equiv.prodCongr_apply,
    Equiv.prodAssoc_apply]

variable (rate : RateInput p) (rewards : GridRewardTable p) (C_star C_h : ℝ)

/-- A first-call cell supplies a literal first invocation, with no success
or admissibility assertion. -/
theorem firstCell_call (u t : Fin p.T) (z : SourceInput p)
    (hz : z ∈ ReferenceCalendarCollectionCallControlLaw.firstCell
      rate rewards C_star C_h u t) :
    ∃ theta : AssignmentParameterFibreKernel.Theta p,
      ReferenceFirstCollectionSamplerCall.firstCollectionCall
        rate rewards C_star C_h z = some (u, (t, theta)) := by
  change (ReferenceFirstCollectionSamplerCall.firstCollectionCall
    rate rewards C_star C_h z).map (fun c => (c.1, c.2.1)) = some (u, t) at hz
  obtain ⟨⟨u', t', theta⟩, hcall, heq⟩ := Option.map_eq_some_iff.mp hz
  cases heq
  exact ⟨theta, hcall⟩

/-- The same actual first invocation and its full prechoice parameter survive
every remainder replacement, including all failed checked samples. -/
theorem currentSource_firstCall (control0 : TimeControl p) (u t : Fin p.T)
    (z : SourceInput p) (theta : AssignmentParameterFibreKernel.Theta p)
    (hcall : ReferenceFirstCollectionSamplerCall.firstCollectionCall
      rate rewards C_star C_h z = some (u, (t, theta)))
    (v : AssignmentVector p) (w : ControlRemainder p) :
    ReferenceFirstCollectionSamplerCall.firstCollectionCall rate rewards C_star C_h
      (currentSource control0 t z v w) = some (u, (t, theta)) := by
  rw [currentSource_eq_suffix]
  exact ReferenceFirstCollectionRenewalPastLocality.firstCollectionCall_eq_of_replaceSelectedControlSuffix
    rate rewards C_star C_h z u t theta _ hcall

theorem currentSource_firstCell (control0 : TimeControl p) (u t : Fin p.T)
    (z : SourceInput p)
    (hz : z ∈ ReferenceCalendarCollectionCallControlLaw.firstCell
      rate rewards C_star C_h u t)
    (v : AssignmentVector p) (w : ControlRemainder p) :
    currentSource control0 t z v w ∈
      ReferenceCalendarCollectionCallControlLaw.firstCell rate rewards C_star C_h u t := by
  obtain ⟨theta, hcall⟩ := firstCell_call rate rewards C_star C_h u t z hz
  change (ReferenceFirstCollectionSamplerCall.firstCollectionCall
    rate rewards C_star C_h _).map _ = _
  rw [currentSource_firstCall rate rewards C_star C_h control0 u t z theta hcall]
  rfl

/-- An indexed complete-suffix record at the requested calendar time is
the literal calendar lookup. -/
theorem actualRecord_of_index (t : Fin p.T) (z : SourceInput p) (n : ℕ)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[n]? = some r) (htime : r.input.time = t) :
    ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z = some r := by
  have hn : n < p.T - ReferenceCompletePhysicalHistory.physicalStart
      rate z rewards C_star C_h := by
    simpa only [ReferenceCompletePhysicalHistory.completeSuffixRecords_length] using
      (List.getElem?_eq_some_iff.mp hr).1
  have hget := congrArg (fun records : List ℕ => records[n]?)
    (ReferenceCompletePhysicalHistory.completeSuffixRecords_time_values
      rate z rewards C_star C_h)
  simp only [ReferenceActivePhysicalHorizon.calendar, List.getElem?_map,
    List.getElem?_range' hn, Nat.one_mul, hr, Option.map_some] at hget
  have htimeNat : t.val = ReferenceCompletePhysicalHistory.physicalStart
      rate z rewards C_star C_h + n := by
    simpa only [htime] using Option.some.inj hget
  have hstart : ReferenceCompletePhysicalHistory.physicalStart
      rate z rewards C_star C_h ≤ t.val := by omega
  unfold ReferenceSourcePrefixHistoryFiltration.actualRecord
  rw [ite_eq_left hstart]
  rw [show t.val - ReferenceCompletePhysicalHistory.physicalStart
    rate z rewards C_star C_h = n by omega, hr]

/-- The prechoice parameter belongs to the same literal first-call record. -/
theorem firstCall_calendarParameters (u t : Fin p.T) (z : SourceInput p)
    (theta : AssignmentParameterFibreKernel.Theta p)
    (hcall : ReferenceFirstCollectionSamplerCall.firstCollectionCall
      rate rewards C_star C_h z = some (u, (t, theta))) :
    ReferenceCalendarLaterSamplerPredictability.calendarParameters
      rate rewards C_star C_h t z = some theta := by
  obtain ⟨n, r, hr, ht, hl, _⟩ :=
    (ReferenceFirstCollectionSamplerCall.firstCollectionCall_spec
      rewards C_star C_h z u t theta).mp hcall
  obtain ⟨_, _, _, _, _, hp⟩ :=
    (ReferenceFirstCollectionSamplerCall.collectionCallAt_spec r u theta).mp hl
  rw [ReferenceCalendarLaterSamplerPredictability.calendarParameters,
    actualRecord_of_index rate rewards C_star C_h t z n r hr ht]
  exact hp

/-- The raw checked sampler code, with every prefix/orientation failure tag,
is the very same checked sample of the entire fixed vector for every remainder. -/
theorem currentRemainder_checkedSampler (control0 : TimeControl p) (u t : Fin p.T)
    (z : SourceInput p)
    (hz : z ∈ ReferenceCalendarCollectionCallControlLaw.firstCell
      rate rewards C_star C_h u t)
    (v : AssignmentVector p) :
    ∃ theta : AssignmentParameterFibreKernel.Theta p,
      ∀ w : ControlRemainder p,
        ∃ o : LaterAssignmentFullOutputMeasurability.FullOutputObservation p,
          ReferenceCalendarLaterSamplerPredictability.calendarParameters
            rate rewards C_star C_h t (currentSource control0 t z v w) = some theta ∧
          ReferenceCalendarLaterSamplerOutputSections.outputAt
            rate rewards C_star C_h t (currentSource control0 t z v w) = some o ∧
          o.1 = LaterAssignmentStartMeasurability.codeOfCheckedSample p
            (CheckedAssignmentSample.checkedAssignmentSample p theta.1 theta.2 v) := by
  obtain ⟨theta, hcall⟩ := firstCell_call rate rewards C_star C_h u t z hz
  refine ⟨theta, ?_⟩
  intro w
  have hnew := currentSource_firstCall rate rewards C_star C_h control0 u t z theta hcall v w
  obtain ⟨theta', o, hp, ho, _hot, _hv, hc, _⟩ :=
    ReferenceFirstCollectionSamplerFibreLaw.firstCell_actualSamplerTrace
      rate rewards C_star C_h u t (currentSource control0 t z v w)
      (currentSource_firstCell rate rewards C_star C_h control0 u t z hz v w)
  have heq : theta' = theta := Option.some.inj (hp.symm.trans
    (firstCall_calendarParameters rate rewards C_star C_h u t
      (currentSource control0 t z v w) theta hnew))
  subst theta'
  refine ⟨o, hp, ho, ?_⟩
  simpa only [currentSource_assignmentVector] using hc

/-- Read the selected view and start from the existing physical record code. -/
def parametersFromCode
    (code : ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate)) :
    Option (ReferenceDownReception.ChoiceTimeView p rate.eta ×
      CoordinatorPhaseClock.StartRoundResult p) :=
  code.2.2.1.1.map fun selected => (selected.1, selected.2.1)

theorem parametersFromCode_measurable : Measurable (parametersFromCode rate) := by
  exact LaterAssignmentFullOutputMeasurability.measurable_optionMap _
    (measurable_fst.prodMk (measurable_fst.comp measurable_snd)) _
    (measurable_fst.comp (measurable_fst.comp (measurable_snd.comp measurable_snd)))

/-- The parameter observation is a Borel projection of the SAME actual code. -/
theorem currentParameters_eq_code (control0 : TimeControl p) (t : Fin p.T)
    (z : SourceInput p) (v : AssignmentVector p) (w : ControlRemainder p) :
    currentParameters rate rewards C_star C_h control0 t z v w =
      ReferenceCollectionOutcomeMeasurability.optionalElim none (parametersFromCode rate)
        (ReferenceCalendarActualControlCallbackSections.codeAt rate rewards C_star C_h t
          (currentSource control0 t z v w)) := by
  unfold currentParameters ReferenceCalendarActualControlCallbackSections.codeAt
  cases hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t
      (currentSource control0 t z v w) with
  | none => rfl
  | some r =>
      simp only [Option.bind_some, Option.map_some,
        ReferenceCollectionOutcomeMeasurability.optionalElim]
      rw [r.output_eq]
      change (ReferenceActivePhysicalStep.dispatch r.input).selection.map
          (fun s => (s.view, s.started)) =
        ((ReferenceActivePhysicalStep.dispatch r.input).selection.map
          ReferenceLiveDispatchOutputMeasurability.encodeSelection).map
            (fun s => (s.1, s.2.1))
      rw [Option.map_map]
      rfl

/-- Joint measurability keeps the original Borel view, anchor, and weights. -/
theorem currentParameters_measurable (control0 : TimeControl p) (t : Fin p.T)
    (z : SourceInput p) :
    Measurable (fun q : AssignmentVector p × ControlRemainder p =>
      currentParameters rate rewards C_star C_h control0 t z q.1 q.2) := by
  have hcode := (ReferenceCalendarActualControlCallbackSections.measurable_codeAt
    rate rewards C_star C_h t).comp (currentSource_measurable control0 t z)
  have helim := ReferenceCollectionOutcomeMeasurability.measurable_optionalElim
    none (parametersFromCode rate) (parametersFromCode_measurable rate)
  convert helim.comp hcode using 1
  funext q
  exact currentParameters_eq_code rate rewards C_star C_h control0 t z q.1 q.2

/-- Success of the selected-view observation is Borel; it is not assumed. -/
theorem currentParameters_success_measurable (control0 : TimeControl p) (t : Fin p.T)
    (z : SourceInput p) :
    Measurable (fun q : AssignmentVector p × ControlRemainder p =>
      (currentParameters rate rewards C_star C_h control0 t z q.1 q.2).isSome) := by
  have hsome : Measurable (Option.isSome :
      Option (ReferenceDownReception.ChoiceTimeView p rate.eta ×
        CoordinatorPhaseClock.StartRoundResult p) → Bool) := by
    convert ReferenceCollectionOutcomeMeasurability.measurable_optionalElim false
      (fun _ : ReferenceDownReception.ChoiceTimeView p rate.eta ×
        CoordinatorPhaseClock.StartRoundResult p => true) measurable_const using 1
    funext q
    cases q <;> rfl
  exact hsome.comp (currentParameters_measurable rate rewards C_star C_h control0 t z)

/-- The inverse split recovers each original non-assignment label literally. -/
theorem currentControl_nonAssignment (v : AssignmentVector p) (w : ControlRemainder p)
    (l : LaunchAssignmentCoordinateSplit.NonAssignmentLabel p) :
    (currentControl v w).1 l.val = w.1 l := by
  simp [currentControl, LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv,
    LaunchAssignmentCoordinateSplit.sliceAssignmentSplitEquiv,
    MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd,
    MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft, MeasurableEquiv.prodAssoc,
    MeasurableEquiv.prodCongr, Equiv.prodCongr_apply, l.property]

section Recording

open ConstructorDimensions (K_pos)
open SnapshotRecordingKernel
open ContinuousControlSlice (Label coordinate)

variable (regime : Regime p) (anchor weights : Fin p.K → ℝ)
  (hanchor : ∀ j, 0 < anchor j) (hweights : ∀ j, 0 < weights j)
  (hlower : ∀ j, anchor j ≤ weights j) (hupper : ∀ j, weights j ≤ 2 * anchor j)

/-- The genuine recorder never reads the assignment-labelled scalars once
its actual payload and snapshot have been supplied. -/
theorem recordingMap_eq_of_nonAssignment
    (x y : ContinuousControlSlice.Slice p.m p.K)
    (hxy : ∀ l : LaunchAssignmentCoordinateSplit.NonAssignmentLabel p,
      x l.val = y l.val) :
    recordingMap p regime true rate.eta.val rate.eta.property rate.sourceCap
        anchor weights hanchor hweights hlower hupper x =
      recordingMap p regime true rate.eta.val rate.eta.property rate.sourceCap
        anchor weights hanchor hweights hlower hupper y := by
  have hslot : coordinate Label.slot x = coordinate Label.slot y :=
    hxy ⟨Label.slot, by simp [Label.slot, Label.assign]⟩
  have hrec : coordinate Label.rec x = coordinate Label.rec y :=
    hxy ⟨Label.rec, by simp [Label.rec, Label.assign]⟩
  have hthin : coordinate Label.thin x = coordinate Label.thin y :=
    hxy ⟨Label.thin, by simp [Label.thin, Label.assign]⟩
  have hfast : coordinate Label.fast x = coordinate Label.fast y :=
    hxy ⟨Label.fast, by simp [Label.fast, Label.assign]⟩
  have hpilot (i : Fin p.m) : PublicDiscreteDraws.pilotDraw (K_pos p) i x =
      PublicDiscreteDraws.pilotDraw (K_pos p) i y := by
    have h := hxy ⟨Label.pilot i, by simp [Label.pilot, Label.assign]⟩
    simpa only [PublicDiscreteDraws.pilotDraw, coordinate] using congrArg
      (PublicDiscreteDraws.pilotFromScalar p.K (K_pos p)) h
  have haction (i : Fin p.m) :
      dataAction p regime rate.eta.val rate.eta.property rate.sourceCap
        anchor weights hanchor hweights hlower hupper x i =
      dataAction p regime rate.eta.val rate.eta.property rate.sourceCap
        anchor weights hanchor hweights hlower hupper y i := by
    cases regime <;> simp only [dataAction, hfast, hpilot]
  have hmask (i : Fin p.m) (j : Fin p.K) :
      CanonicalRecordingSlice.recordingMask (K_pos p) i j x ↔
        CanonicalRecordingSlice.recordingMask (K_pos p) i j y := by
    simp only [CanonicalRecordingSlice.recordingMask, hpilot]
  simp only [recordingMap, hslot, hrec, hthin, haction, hmask]

/-- Fixing the whole assignment vector leaves only the original remainder
coordinates in the recorder. No assignment factor is conditioned away. -/
theorem recordingMap_currentControl_eq (v v' : AssignmentVector p)
    (w : ControlRemainder p) :
    recordingMap p regime true rate.eta.val rate.eta.property rate.sourceCap
        anchor weights hanchor hweights hlower hupper (currentControl v w).1 =
      recordingMap p regime true rate.eta.val rate.eta.property rate.sourceCap
        anchor weights hanchor hweights hlower hupper (currentControl v' w).1 := by
  apply recordingMap_eq_of_nonAssignment rate regime anchor weights
    hanchor hweights hlower hupper
  intro l
  rw [currentControl_nonAssignment, currentControl_nonAssignment]

/-- Each actual recording event pulls back to the whole assignment cube
times its remainder event. No fixed vector is removed from a sampler fibre. -/
theorem recordingMap_currentControl_event (v : AssignmentVector p) (o : Option (Fin p.K)) :
    {q : AssignmentVector p × ControlRemainder p |
      recordingMap p regime true rate.eta.val rate.eta.property rate.sourceCap
        anchor weights hanchor hweights hlower hupper (currentControl q.1 q.2).1 = o} =
      Set.univ ×ˢ {w : ControlRemainder p |
        recordingMap p regime true rate.eta.val rate.eta.property rate.sourceCap
          anchor weights hanchor hweights hlower hupper (currentControl v w).1 = o} := by
  ext q
  simp only [Set.mem_ofPred_eq, Set.mem_prod, Set.mem_univ, true_and]
  rw [recordingMap_currentControl_eq rate regime anchor weights hanchor hweights hlower hupper q.1 v q.2]

/-- With its actual payload and snapshot fixed, the genuine recording map
under all remaining original coordinates has the canonical arm-or-bottom law.
The full corrected weight vector is retained. -/
theorem map_recordingMap_currentRemainder (v : AssignmentVector p) :
    (ReferenceLaterOptionalControlResampling.controlRemainderLaw p).map
      (fun w => recordingMap p regime true rate.eta.val rate.eta.property rate.sourceCap
        anchor weights hanchor hweights hlower hupper (currentControl v w).1) =
      (RecordedRoundMoments.recordingOutcomePMF
        (recordingRates p rate.eta.val rate.eta.property rate.sourceCap anchor hanchor)).toMeasure := by
  let f : TimeControl p → Option (Fin p.K) := fun c =>
    recordingMap p regime true rate.eta.val rate.eta.property rate.sourceCap
      anchor weights hanchor hweights hlower hupper c.1
  let g : ControlRemainder p → Option (Fin p.K) := fun w => f (currentControl v w)
  have hf : Measurable f :=
    (measurable_recordingMap p regime rate.eta.val rate.eta.property rate.sourceCap
      anchor weights hanchor hweights hlower hupper true).comp measurable_fst
  have hg : Measurable g := hf.comp
    (currentControl_measurable.comp (measurable_const.prodMk measurable_id))
  have heq : f ∘ (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p).symm =
      g ∘ Prod.snd := by
    funext q
    exact recordingMap_currentControl_eq rate regime anchor weights hanchor hweights
      hlower hupper q.1 v q.2
  have hsplit :=
    LaunchAssignmentCoordinateSplit.measurePreserving_controlAssignmentSplitEquiv p
  have hsnd : ((ContinuousControlSlice.assignmentLaw p.K).prod
      (ReferenceLaterOptionalControlResampling.controlRemainderLaw p)).map Prod.snd =
        ReferenceLaterOptionalControlResampling.controlRemainderLaw p := by
    apply Measure.ext
    intro B hB
    rw [Measure.map_apply measurable_snd hB]
    have hpre : Prod.snd ⁻¹' B = (Set.univ : Set (AssignmentVector p)) ×ˢ B := by
      ext q
      simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, true_and]
    rw [hpre, Measure.prod_prod, measure_univ, one_mul]
  have hfull : (ContinuousLearningRows.timeControlLaw p).map f =
      (ReferenceLaterOptionalControlResampling.controlRemainderLaw p).map g := by
    rw [← hsplit.symm.map_eq, Measure.map_map hf hsplit.symm.measurable, heq,
      ← Measure.map_map hg measurable_snd]
    exact congrArg (Measure.map g) hsnd
  have hslice : (ContinuousLearningRows.timeControlLaw p).map f =
      (ContinuousControlSlice.sliceLaw p.m p.K).map
        (recordingMap p regime true rate.eta.val rate.eta.property rate.sourceCap
          anchor weights hanchor hweights hlower hupper) := by
    rw [ContinuousLearningRows.timeControlLaw, show f =
      (recordingMap p regime true rate.eta.val rate.eta.property rate.sourceCap
        anchor weights hanchor hweights hlower hupper) ∘ Prod.fst from rfl,
      ← Measure.map_map
        (measurable_recordingMap p regime rate.eta.val rate.eta.property rate.sourceCap
          anchor weights hanchor hweights hlower hupper true) measurable_fst,
      Measure.map_fst_prod]
    simp only [measure_univ, one_smul]
  exact hfull.symm.trans (hslice.trans (map_recordingMap p regime rate.eta.val
    rate.eta.property rate.sourceCap anchor weights hanchor hweights hlower hupper))

end Recording

section LocalDispatch

open ReferenceCollectionDispatchMeasurability
open ReferenceCollectionInstallOutputMeasurability
open ReferenceCollectionOutcomeMeasurability

/-- Changing a row can change the chosen arm, but never whether the checked
installed choice returns an arm. All original guard bits remain in force. -/
theorem installedSelectedArm_isSome_row {p : ConstructorDimensions.Parameters}
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (c : InstallationCoordinates p rate) (started : CoordinatorPhaseClock.StartRoundResult p)
    (left right : CompletePublicTable.CompleteRow p) :
    (installedSelectedArm c started left).isSome =
      (installedSelectedArm c started right).isSome := by
  unfold installedSelectedArm
  split_ifs with hg
  · have hchoice : CoordinatorLocalArmChoice.ChoiceInputsValid
        (installedView c started).payload (installedView c started).cutoff c.2.time
        (installedView c started).complementWeights := by
      have hc : installedChoiceInputsBit c started = true := by
        simp only [Bool.and_eq_true] at hg
        exact hg.1.1.2
      simpa only [installedChoiceInputsBit,
        ReferenceDownReceptionMeasurability.choiceInputsValidBit, decide_eq_true_eq] using hc
    by_cases hp : (installedView c started).pendingAtChoice.Nonempty
    · have hl := CoordinatorLiveChoiceRecorderStep.coordinatorArmChoice_ne_none
        (installedView c started).payload (installedView c started).pendingAtChoice
        (installedView c started).cutoff c.2.time
        (installedView c started).complementWeights left hchoice
      have hr := CoordinatorLiveChoiceRecorderStep.coordinatorArmChoice_ne_none
        (installedView c started).payload (installedView c started).pendingAtChoice
        (installedView c started).cutoff c.2.time
        (installedView c started).complementWeights right hchoice
      simp only [pendingChoice, ite_eq_left hp]
      exact (Option.isSome_iff_ne_none.mpr hl).trans
        (Option.isSome_iff_ne_none.mpr hr).symm
    · simp [pendingChoice, hp]
  · rfl

private theorem tagFromKey_arm_congr {p : ConstructorDimensions.Parameters}
    (started : CoordinatorPhaseClock.StartRoundResult p) (scores : Bool)
    (raw : Option (LaterAssignmentStartMeasurability.LaterAssignmentStartCode p))
    (b0 b1 b2 b3 : Bool) (a b : Option (Fin p.K))
    (h : a.isSome = b.isSome) :
    tagFromKey (started |> Sum.inr, true, false, scores, none, raw,
        some (b0, b1, b2, b3, a)) =
      tagFromKey (started |> Sum.inr, true, false, scores, none, raw,
        some (b0, b1, b2, b3, b)) := by
  cases a with
  | none =>
      cases b with
      | none => rfl
      | some b => cases h
  | some a =>
      cases b with
      | none => cases h
      | some b =>
          cases hi : started.assignmentStart with
          | none => simp only [tagFromKey, hi, ite_true, Bool.false_eq_true, ite_false]
          | some instruction =>
              cases raw with
              | none => simp only [tagFromKey, hi, ite_true, Bool.false_eq_true, ite_false]
              | some code =>
                  cases code <;>
                    cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;>
                    rfl

private theorem selection_arm_congr {p : ConstructorDimensions.Parameters}
    {rate : RateInput p} (view : ReferenceDownReception.ChoiceTimeView p rate.eta)
    (started : CoordinatorPhaseClock.StartRoundResult p) (a b : Option (Fin p.K))
    (h : a.isSome = b.isSome) :
    (selectionFromCandidate (view, started, a)).map (fun c => (c.1, c.2.1)) =
      (selectionFromCandidate (view, started, b)).map (fun c => (c.1, c.2.1)) := by
  cases a <;> cases b <;> first | rfl | cases h

/-- Internal local comparison of the actual dispatch observations. The
clock/core/instruction inputs are ordinary local helper inputs; the source
application obtains them from the actual prechoice selector. -/
theorem localDispatch_factor {p : ConstructorDimensions.Parameters}
    (rate : ReferenceActivePhysicalStep.RateInput p) (z : LocalInput p rate)
    (core : CoordinatorRoundDispatch.CollectionCoreValid (assemble z))
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (hs : CoordinatorPhaseClock.startRound p rate.eta.val (assemble z).time
      (assemble z).clock (assemble z).ledger.pending = .ok started)
    (hp : ¬ z.2.1.pending.Nonempty)
    (instruction : CoordinatorPhaseClock.AssignmentStartInstruction p)
    (hi : started.assignmentStart = some instruction)
    (row : CompletePublicTable.CompleteRow p)
    (hv : LaterAssignmentStartOperation.ownAssignmentVector z.1.2 instruction.time =
      LaterAssignmentStartOperation.ownAssignmentVector row instruction.time) :
    let z' : LocalInput p rate := ((z.1.1, row), z.2)
    collectionTag z = collectionTag z' ∧
      (collectionSelectionCode z).map (fun c => (c.1, c.2.1)) =
        (collectionSelectionCode z').map (fun c => (c.1, c.2.1)) := by
  let z' : LocalInput p rate := ((z.1.1, row), z.2)
  have core' : CoordinatorRoundDispatch.CollectionCoreValid (assemble z') :=
    (coreChecks_iff z').mp ((coreChecks_iff z).mpr core)
  let left : CoreInput p rate := ⟨z, core⟩
  let right : CoreInput p rate := ⟨z', core'⟩
  have hs' : CoordinatorPhaseClock.startRound p rate.eta.val (assemble z').time
      (assemble z').clock (assemble z').ledger.pending = .ok started := hs
  have hc : clockObservation z = .inr started := by
    simp only [clockObservation, hs]
  have hc' : clockObservation z' = .inr started := by
    simp only [clockObservation, hs']
  have hcontinuing (q : LocalInput p rate)
      (hq : ¬ q.2.1.pending.Nonempty) : continuingObservation? q = none := by
    unfold continuingObservation? pendingObservation?
    split_ifs <;> rfl
  have hcl := hcontinuing z hp
  have hcr := hcontinuing z' hp
  have hcode := LaterAssignmentStartMeasurability.laterAssignmentStartCode_eq_of_ownAssignmentVector_eq
    z.1.1 ⟨operationLedger left, instruction, localConsistency left⟩ z.1.2 row hv
  have hcodes : (laterObservation? z).map Prod.fst =
      (laterObservation? z').map Prod.fst := by
    rw [later_code_observed left started hs hp instruction hi,
      later_code_observed right started hs' hp instruction hi]
    exact congrArg some hcode
  have hps : laterPayloadScore? left instruction = laterPayloadScore? right instruction :=
    LaterAssignmentStartMeasurability.laterAssignmentStart_payloadAndBaseScore?_eq_of_ownAssignmentVector_eq
      z.1.1 ⟨operationLedger left, instruction, localConsistency left⟩ z.1.2 row hv
  have hil : laterInstalledObservation? z = (laterPayloadScore? left instruction).map
      (fun ps => installedObservation (installationCoordinates ps z.2.1 instruction started)
        started z.1.2) := by
    simp [laterInstalledObservation?, core, hc, laterInstalledAtClock,
      requestedInstructionAt, hp, hi, laterInstalledObservation, left]
  have hir : laterInstalledObservation? z' = (laterPayloadScore? right instruction).map
      (fun ps => installedObservation (installationCoordinates ps z.2.1 instruction started)
        started row) := by
    simp [laterInstalledObservation?, core', hc', laterInstalledAtClock,
      requestedInstructionAt, hp, hi, laterInstalledObservation, right, z']
  have hcorebit : coreCheck z = true := by simp [coreCheck, core]
  have hcorebit' : coreCheck z' = true := by simp [coreCheck, core']
  have hpend : (assemble z).ledger.pending = z.2.1.pending := rfl
  have hpend' : (assemble z').ledger.pending = z.2.1.pending := rfl
  have htag : collectionTag z = collectionTag z' := by
    simp only [collectionTag, tagKey, hc, hc', hcorebit, hcorebit', hpend, hpend',
      decide_eq_false hp, hcl, hcr, Option.map_none, hcodes, hil, hir, hps]
    cases hvalue : laterPayloadScore? right instruction with
    | none => rfl
    | some ps =>
        simp only [Option.map_some, installedObservation]
        exact tagFromKey_arm_congr started _ _ _ _ _ _ _ _
          (installedSelectedArm_isSome_row rate
            (installationCoordinates ps z.2.1 instruction started) started z.1.2 row)
  refine ⟨htag, ?_⟩
  simp only [collectionSelectionCode, htag, hcl, optionalElim]
  split_ifs
  · exact (congrArg (fun o => (optionalElim none selectionFromCandidate o).map
        (fun c => (c.1, c.2.1))) hcr).symm
  · rw [hil, hir, hps]
    cases hvalue : laterPayloadScore? right instruction with
    | none => rfl
    | some ps =>
        simp only [Option.map_some, installedCandidate, installedObservation]
        exact selection_arm_congr _ started _ _
          (installedSelectedArm_isSome_row rate
            (installationCoordinates ps z.2.1 instruction started) started z.1.2 row)
  · rfl

end LocalDispatch

/-- The actual collection dispatch constructor and its original later
failure-reason tag. No dependent row-bearing outcome is identified. -/
def collectionDispatchTag (x : ReferenceActivePhysicalStep.RoundInput p rate) :
    Option (ReferenceCollectionOutcomeMeasurability.CollectionTag p) :=
  match (ReferenceActivePhysicalStep.prepare x).coordinator with
  | .collection _ _ _ _ outcome =>
      some (ReferenceCollectionOutcomeMeasurability.outcomeTag outcome)
  | _ => none

section RoundDispatch

open ReferenceActivePhysicalStep
open ReferenceCollectionDispatchMeasurability
open ReferenceCollectionOutcomeMeasurability

private theorem localSelection_eq_dispatch {p : ConstructorDimensions.Parameters}
    (rate : RateInput p) (x : RoundInput p rate)
    (payload : Payload rate) (ledger : Ledger rate) (proposal : Option (Fin p.T × Bool))
    (hc : x.state.coordinator = .collection payload ledger proposal)
    (hd : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T) :
    let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
    let z : LocalInput p rate :=
      ((payload, x.row), ledger, proposal, x.state.upDecoderBank, x.time, cutoff)
    (collectionSelectionCode z).map (fun c => (c.1, c.2.1)) =
      (dispatch x).selection.map (fun s => (s.view, s.started)) := by
  let boundary : BoundaryInput p rate :=
    ((payload, x.row), ledger, proposal, x.state.upDecoderBank, x.time)
  have hcode := canonicalCollectionSelectionCode_eq_dispatch x payload ledger proposal hc
  rw [canonicalCollectionSelectionCode,
    canonicalCollectionFullObservation_collection x payload ledger proposal hc] at hcode
  have hd' : cutoffValid ((payload, x.row), ledger, proposal, x.state.upDecoderBank, x.time) := hd
  dsimp only [optionalElim, boundaryFullObservation] at hcode
  rw [dite_eq_left hd'] at hcode
  dsimp only [selectionFromBoundary, collectionFullObservation] at hcode
  have h := congrArg (Option.map (fun c => (c.1, c.2.1))) hcode
  simpa only [collectionFullObservation, boundaryLocal, Option.map_map,
    ReferenceLiveDispatchOutputMeasurability.encodeSelection,
    ReferenceCollectionDispatchMeasurability.encodeSelection, Function.comp_def] using h

/-- At two actual inputs with the same incoming state and time, fixing the
whole vector fixes the selected view/start and every collection failure tag.
The arm value is deliberately absent from this comparison. -/
theorem roundDispatch_factor {p : ConstructorDimensions.Parameters}
    (rate : RateInput p) (x y : RoundInput p rate)
    (hstate : x.state = y.state) (htime : x.time = y.time)
    (theta : AssignmentParameterFibreKernel.Theta p)
    (hparameter : ReferenceLaterSamplerParameterMeasurability.parameters? x = some theta)
    (hvector : LaterAssignmentStartOperation.ownAssignmentVector x.row x.time =
      LaterAssignmentStartOperation.ownAssignmentVector y.row y.time) :
    collectionDispatchTag rate x = collectionDispatchTag rate y ∧
      ReferenceCollectionPhaseHistory.laterChosen x =
        ReferenceCollectionPhaseHistory.laterChosen y ∧
      (dispatch x).selection.map (fun s => (s.view, s.started)) =
        (dispatch y).selection.map (fun s => (s.view, s.started)) := by
  rcases x with ⟨sx, rx, jx, tx, ax, wx⟩
  rcases y with ⟨sy, ry, jy, ty, ay, wy⟩
  dsimp only at hstate htime
  subst sy
  subst ty
  let x : RoundInput p rate := ⟨sx, rx, jx, tx, ax, wx⟩
  let y : RoundInput p rate := ⟨sx, ry, jy, tx, ay, wy⟩
  have hstate : x.state = y.state := rfl
  have htime : x.time = y.time := rfl
  obtain ⟨payload, ledger, proposal, hx⟩ :=
    ReferenceLaterOptionalControlResampling.parameters?_eq_some_implies_collection x theta hparameter
  have hy : y.state.coordinator = .collection payload ledger proposal := by
    rw [← hstate, hx]
  unfold ReferenceLaterSamplerParameterMeasurability.parameters?
    ReferenceLaterAssignmentFibreStep.parameters? at hparameter
  rw [hx] at hparameter
  dsimp only at hparameter
  have hd : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T := by
    by_contra hn
    simp only [dite_eq_right hn, reduceCtorEq] at hparameter
  rw [dite_eq_left hd] at hparameter
  let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
  let z : LocalInput p rate :=
    ((payload, x.row), ledger, proposal, x.state.upDecoderBank, x.time, cutoff)
  let z' : LocalInput p rate := ((payload, y.row), z.2)
  have hparameter' : ReferenceLaterAssignmentFibreStep.collectionParameters? (assemble z) =
      some theta := hparameter
  unfold ReferenceLaterAssignmentFibreStep.collectionParameters? at hparameter'
  cases hs : CoordinatorPhaseClock.startRound p (assemble z).etaReal (assemble z).time
      (assemble z).clock (assemble z).ledger.pending with
  | error reason => simp only [hs, reduceCtorEq] at hparameter'
  | ok started =>
      simp only [hs] at hparameter'
      split_ifs at hparameter' with core hp
      cases hi : started.assignmentStart with
        | none => simp only [hi, reduceCtorEq] at hparameter'
        | some instruction =>
            have hitime : instruction.time = x.time :=
              (CoordinatorPhaseClock.startRound_assignment_effect p rate.eta.val
                (assemble z).time (assemble z).clock (assemble z).ledger.pending started
                instruction core.clock_parameter_valid core.clock_registers_valid
                core.clock_start_time_valid hs hi).1
            have hv : LaterAssignmentStartOperation.ownAssignmentVector z.1.2 instruction.time =
                LaterAssignmentStartOperation.ownAssignmentVector y.row instruction.time := by
              rw [hitime]
              exact hvector
            obtain ⟨htag, hselection⟩ := localDispatch_factor rate z core started hs hp
              instruction hi y.row hv
            have hdx := dispatch_collection x payload ledger proposal hx hd
            have hdy := dispatch_collection y payload ledger proposal hy hd
            have hdy' : dispatch y = .collection payload ledger
                (collectionClock payload ledger proposal cutoff) cutoff
                  (CoordinatorRoundDispatch.dispatchCollection (assemble z')) := by
              simpa only [z', z, ← hstate, ← htime, boundaryLocal] using hdy
            have hdx' : dispatch x = .collection payload ledger
                (collectionClock payload ledger proposal cutoff) cutoff
                  (CoordinatorRoundDispatch.dispatchCollection (assemble z)) := hdx
            have htag' := htag
            rw [collectionTag_eq_actual, collectionTag_eq_actual] at htag'
            have htagSource : collectionDispatchTag rate x = collectionDispatchTag rate y := by
              unfold collectionDispatchTag
              change (match dispatch x with
                | .collection _ _ _ _ o => some (outcomeTag o) | _ => none) =
                (match dispatch y with
                | .collection _ _ _ _ o => some (outcomeTag o) | _ => none)
              rw [hdx', hdy']
              exact congrArg some htag'
            refine ⟨htagSource, ?_, ?_⟩
            · have chosenTag (q : RoundInput p rate) :
                  ReferenceCollectionPhaseHistory.laterChosen q =
                    decide (collectionDispatchTag rate q = some .laterChosen) := by
                unfold ReferenceCollectionPhaseHistory.laterChosen collectionDispatchTag
                cases (prepare q).coordinator <;> try rfl
                rename_i a b c d outcome
                cases outcome <;> rfl
              rw [chosenTag x, chosenTag y, htagSource]
            · rw [← localSelection_eq_dispatch rate x payload ledger proposal hx hd,
                ← localSelection_eq_dispatch rate y payload ledger proposal hy hd]
              simpa only [z', z, ← hstate, ← htime] using hselection

end RoundDispatch

/-- The current replacement retains exactly the original strict prefix. -/
theorem currentSource_prefix (control0 : TimeControl p) (t : Fin p.T)
    (z : SourceInput p) (v : AssignmentVector p) (w : ControlRemainder p) :
    ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val
        (currentSource control0 t z v w) =
      ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z := by
  unfold currentSource
  rw [ReferenceFirstLiveActualFlagSections.sourcePrefix_replace_current,
    ReferenceSourcePrefixHistoryFiltration.sourcePrefix_sourcePrefix
      control0 t.val t.val le_rfl]

/-- Incoming physical state codes are independent of every current coordinate. -/
theorem currentSource_incoming (control0 : TimeControl p) (t : Fin p.T)
    (z : SourceInput p) (v : AssignmentVector p) (w : ControlRemainder p) :
    ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t
        (currentSource control0 t z v w) =
      ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t z := by
  rw [ReferenceSourcePrefixHistoryFiltration.incoming_factor
      rate rewards C_star C_h control0 t (currentSource control0 t z v w),
    currentSource_prefix]
  exact (ReferenceSourcePrefixHistoryFiltration.incoming_factor
    rate rewards C_star C_h control0 t z).symm

/-- Literal fields of an actual calendar lookup, on the original whole source. -/
theorem actualRecord_input_fields (t : Fin p.T) (z : SourceInput p)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z = some r) :
    r.input.rows = z.1.2 ∧ r.input.selected = selectedRowIndex p z ∧
      r.input.rewards = rewards := by
  unfold ReferenceSourcePrefixHistoryFiltration.actualRecord at hr
  split_ifs at hr with hs
  obtain ⟨hk, hrecord⟩ := List.getElem?_eq_some_iff.mp hr
  have hf := ReferenceCompleteSuffixInputMeasurability.actualRoundInputAt_fields
    rate rewards C_star C_h _ ⟨z, hk⟩
  dsimp only [ReferenceCompleteSuffixInputMeasurability.actualRoundInputAt,
    ReferenceCompleteSuffixInputMeasurability.actualRecordCodeAt,
    List.get_eq_getElem] at hf
  rw [hrecord] at hf
  exact ⟨hf.1, hf.2.1, hf.2.2.1⟩

/-- The same first invocation supplies its own actual record and parameter. -/
theorem firstCall_record (u t : Fin p.T) (z : SourceInput p)
    (theta : AssignmentParameterFibreKernel.Theta p)
    (hcall : ReferenceFirstCollectionSamplerCall.firstCollectionCall
      rate rewards C_star C_h z = some (u, (t, theta))) :
    ∃ r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate),
      ReferenceSourcePrefixHistoryFiltration.actualRecord
        rate rewards C_star C_h t z = some r ∧ r.input.time = t ∧
      ReferenceLaterSamplerParameterMeasurability.parameters? r.input = some theta := by
  obtain ⟨n, r, hr, ht, hl, _⟩ :=
    (ReferenceFirstCollectionSamplerCall.firstCollectionCall_spec
      rewards C_star C_h z u t theta).mp hcall
  obtain ⟨_, _, _, _, _, hp⟩ :=
    (ReferenceFirstCollectionSamplerCall.collectionCallAt_spec r u theta).mp hl
  exact ⟨r, actualRecord_of_index rate rewards C_star C_h t z n r hr ht, ht, hp⟩

/-- Actual constructor/reason tags, with record absence preserved. -/
def currentDispatchTag (control0 : TimeControl p) (t : Fin p.T) (z : SourceInput p)
    (v : AssignmentVector p) (w : ControlRemainder p) :
    Option (Option (ReferenceCollectionOutcomeMeasurability.CollectionTag p)) :=
  (ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t
    (currentSource control0 t z v w)).map (fun r => collectionDispatchTag rate r.input)

/-- The literal actual selected-view/start, later-chosen test, and dispatch
constructor/reason tag are fixed by the WHOLE assignment vector. No successful
sample, installation, guard, or ordinary-state premise is supplied. -/
theorem currentRemainder_parameters_factor (control0 : TimeControl p) (u t : Fin p.T)
    (z : SourceInput p)
    (hz : z ∈ ReferenceCalendarCollectionCallControlLaw.firstCell
      rate rewards C_star C_h u t)
    (v : AssignmentVector p) (w : ControlRemainder p) :
    let w0 := (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p control0).2
    currentParameters rate rewards C_star C_h control0 t z v w =
        currentParameters rate rewards C_star C_h control0 t z v w0 ∧
      currentChosen rate rewards C_star C_h control0 t z v w =
        currentChosen rate rewards C_star C_h control0 t z v w0 ∧
      currentDispatchTag rate rewards C_star C_h control0 t z v w =
        currentDispatchTag rate rewards C_star C_h control0 t z v w0 := by
  let w0 := (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p control0).2
  obtain ⟨theta, hcall⟩ := firstCell_call rate rewards C_star C_h u t z hz
  obtain ⟨a, ha, hta, hpa⟩ := firstCall_record rate rewards C_star C_h u t
    (currentSource control0 t z v w) theta
    (currentSource_firstCall rate rewards C_star C_h control0 u t z theta hcall v w)
  obtain ⟨b, hb, htb, _hpb⟩ := firstCall_record rate rewards C_star C_h u t
    (currentSource control0 t z v w0) theta
    (currentSource_firstCall rate rewards C_star C_h control0 u t z theta hcall v w0)
  have hin := (currentSource_incoming rate rewards C_star C_h control0 t z v w).trans
    (currentSource_incoming rate rewards C_star C_h control0 t z v w0).symm
  simp only [ReferenceSourcePrefixHistoryFiltration.incoming, ha, hb,
    Option.map_some, Option.some.injEq] at hin
  have hstate : a.input.state = b.input.state := by
    simpa only [ReferenceActivePhysicalStepMeasurability.decodeState_encodeState] using
      congrArg ReferenceActivePhysicalStepMeasurability.decodeState hin
  obtain ⟨harows, haj, _⟩ := actualRecord_input_fields rate rewards C_star C_h t
    (currentSource control0 t z v w) a ha
  obtain ⟨hbrows, hbj, _⟩ := actualRecord_input_fields rate rewards C_star C_h t
    (currentSource control0 t z v w0) b hb
  have hva : LaterAssignmentStartOperation.ownAssignmentVector a.input.row a.input.time = v := by
    change ContinuousControlSlice.assignmentVector
      ((a.input.rows a.input.selected).2 a.input.time).1 = v
    rw [harows, haj, hta]
    exact currentSource_assignmentVector control0 t z v w
  have hvb : LaterAssignmentStartOperation.ownAssignmentVector b.input.row b.input.time = v := by
    change ContinuousControlSlice.assignmentVector
      ((b.input.rows b.input.selected).2 b.input.time).1 = v
    rw [hbrows, hbj, htb]
    exact currentSource_assignmentVector control0 t z v w0
  obtain ⟨htag, hchosen, hparameters⟩ := roundDispatch_factor rate a.input b.input hstate
    (hta.trans htb.symm) theta hpa (hva.trans hvb.symm)
  have hb' : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t
      (currentSource control0 t z v
        (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p control0).2) = some b := hb
  simp only [currentParameters, currentChosen, currentDispatchTag, ha, hb',
    Option.bind_some, Option.map_some]
  rw [ReferenceLaterLiveReadoutDomain.roundRecordSelection_eq_dispatch,
    ReferenceLaterLiveReadoutDomain.roundRecordSelection_eq_dispatch]
  exact ⟨hparameters, congrArg some hchosen, congrArg some htag⟩

private theorem takeWhile_length_le_at_false {A : Type*} (f : A → Bool)
    (xs : List A) (n : ℕ) (r : A) (hr : xs[n]? = some r) (hf : f r = false) :
    (xs.takeWhile f).length ≤ n := by
  induction xs generalizing n with
  | nil => simp only [List.getElem?_nil, reduceCtorEq] at hr
  | cons head tail ih =>
      cases n with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hr
          subst r
          simp only [List.takeWhile_cons, hf, Bool.false_eq_true, ite_false, List.length_nil]
          exact Nat.zero_le _
      | succ n =>
          by_cases hh : f head = true
          · simp only [List.takeWhile_cons, hh, ite_true, List.length_cons]
            exact Nat.add_le_add_right (ih n (by simpa using hr)) 1
          · simp only [List.takeWhile_cons, hh]
            exact Nat.zero_le _

private theorem takeWhile_length_at_first_false {A : Type*} (f : A → Bool)
    (xs : List A) (n : ℕ) (r : A) (hr : xs[n]? = some r) (hf : f r = false)
    (he : ∀ j < n, ∀ q, xs[j]? = some q → f q = true) :
    (xs.takeWhile f).length = n := by
  induction xs generalizing n with
  | nil => simp only [List.getElem?_nil, reduceCtorEq] at hr
  | cons head tail ih =>
      cases n with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hr
          subst r
          simp only [List.takeWhile_cons, hf, Bool.false_eq_true, ite_false, List.length_nil]
      | succ n =>
          have hh := he 0 (by omega) head rfl
          have ht := ih n (by simpa using hr)
            (fun j hj q hq => he (j + 1) (by omega) q (by simpa using hq))
          simpa only [List.takeWhile_cons, hh, ite_true, List.length_cons] using
            congrArg Nat.succ ht

/-- The actual first call, when chosen, is the first replacement record.
This uses the unrestricted source chronology, with no renewal hypothesis. -/
theorem firstCall_firstReplacementRecord (u t : Fin p.T) (source : SourceInput p)
    (theta : AssignmentParameterFibreKernel.Theta p)
    (hcall : ReferenceFirstCollectionSamplerCall.firstCollectionCall
      rate rewards C_star C_h source = some (u, (t, theta)))
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t source = some r)
    (hchosen : ReferenceCollectionPhaseHistory.laterChosen r.input = true) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
    R[w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length]? = some r := by
  obtain ⟨n, q, hq, ht, hl, he⟩ :=
    (ReferenceFirstCollectionSamplerCall.firstCollectionCall_spec
      rewards C_star C_h source u t theta).mp hcall
  have hqr : q = r := Option.some.inj
    ((actualRecord_of_index rate rewards C_star C_h t source n q hq ht).symm.trans hr)
  subst q
  obtain ⟨payload, ledger, proposal, hcoord, _hcut, _hp⟩ :=
    (ReferenceFirstCollectionSamplerCall.collectionCallAt_spec r u theta).mp hl
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
  let start := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
  have hn : n < R.length := (List.getElem?_eq_some_iff.mp hq).1
  have hget : R.get ⟨n, hn⟩ = r := by
    exact (List.getElem?_eq_some_iff.mp hq).2
  obtain ⟨hc, span, hprefix⟩ := ReferenceLaterLiveNumericalReadout.source_record_prefix
    rate rewards C_star C_h source ⟨n, hn⟩
  rw [hget] at hprefix
  change start + (n + 1) ≤ p.T at span
  let initial := ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hc
  let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
    rate source rewards C_star C_h hc
  have hstate : (ReferenceActivePhysicalHorizon.run initial source.1.2
      (selectedRowIndex p source) rewards start n (by omega) seed.activeAtStart).finalState.coordinator =
        .collection payload ledger proposal := by
    change (ReferenceAssignmentPayloadChronology.actualRunRecordAt initial source.1.2
      (selectedRowIndex p source) rewards start n span seed.activeAtStart).input.state.coordinator = _
    rw [← hprefix]
    exact hcoord
  have hfull := ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
    rate source rewards C_star C_h initial
    (ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
      rate source rewards C_star C_h hc)
  have hcount : n + (p.T - start - n) = p.T - start := by
    have hn' : n < p.T - start := by
      simpa only [R, ReferenceCompletePhysicalHistory.completeSuffixRecords_length] using hn
    omega
  obtain ⟨a, cutoff, han, hcutoff, hcut, _⟩ :=
    ReferenceCollectionPhaseHistory.run_collection_pending_exact_prefix initial source.1.2
      (selectedRowIndex p source) rewards start n (p.T - start - n) (by omega)
      seed.activeAtStart seed.coordinatorFirst payload ledger proposal hstate
  have hcutoff' : R[a]? = some cutoff := by
    change (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[a]? = some cutoff
    rw [hfull]
    simpa only [hcount] using hcutoff
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  have hwn : w < n := by
    have hw : w ≤ a := takeWhile_length_le_at_false
      (fun q : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) =>
        !ReferenceCollectionPhaseHistory.cutoffChosen q.input) R a cutoff hcutoff'
      (by simp only [hcut, Bool.not_true])
    omega
  have htail : (R.drop (w + 1))[n - (w + 1)]? = some r := by
    simpa only [List.getElem?_drop, Nat.add_sub_of_le (by omega : w + 1 ≤ n)] using hq
  have hscan : ((R.drop (w + 1)).takeWhile fun q =>
      !ReferenceCollectionPhaseHistory.laterChosen q.input).length = n - (w + 1) := by
    apply takeWhile_length_at_first_false _ _ _ r htail
    · simp only [hchosen, Bool.not_true]
    · intro k hk q hrecord
      have hrecord' : R[w + 1 + k]? = some q := by
        simpa only [List.getElem?_drop] using hrecord
      have hp := he (w + 1 + k) (by omega) q hrecord'
      have hfalse : ReferenceCollectionPhaseHistory.laterChosen q.input = false := by
        cases hb : ReferenceCollectionPhaseHistory.laterChosen q.input with
        | false => rfl
        | true =>
            have hsome := ReferenceFirstCollectionRenewalRecordingFeedback.laterChosen_parameters_present q.input hb
            rw [show ReferenceLaterAssignmentFibreStep.parameters? q.input = none from hp] at hsome
            cases hsome
      simp only [hfalse, Bool.not_false]
  have hhead : ((R.drop w).take 1).length = 1 := by
    simp only [List.length_take, List.length_drop]
    omega
  have hwindow : (ReferenceCollectionPhaseHistory.collectionWindow R w).length =
      1 + (n - (w + 1)) := by
    simp only [ReferenceCollectionPhaseHistory.collectionWindow, List.length_append, hhead]
    exact congrArg (1 + ·) hscan
  change R[w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length]? = some r
  rw [show w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length = n by omega]
  exact hq

/-- A present selection at an actual checked later-sampler call is the
actual later-chosen constructor. A successful raw sample alone is not used. -/
theorem selected_laterChosen (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (theta : AssignmentParameterFibreKernel.Theta p)
    (hp : ReferenceLaterSamplerParameterMeasurability.parameters? x = some theta)
    (selected : ReferenceActivePhysicalStep.Selection x)
    (hs : (ReferenceActivePhysicalStep.prepare x).coordinator.selection = some selected) :
    ReferenceCollectionPhaseHistory.laterChosen x = true := by
  have hparam : ReferenceLaterAssignmentFibreStep.dispatchParameters?
      (ReferenceActivePhysicalStep.prepare x).coordinator = some theta :=
    (ReferenceLaterAssignmentFibreStep.parameters?_eq_physicalDispatch x).symm.trans hp
  unfold ReferenceCollectionPhaseHistory.laterChosen
  cases he : (ReferenceActivePhysicalStep.prepare x).coordinator with
  | first outcome => simp only [he, ReferenceLaterAssignmentFibreStep.dispatchParameters?, reduceCtorEq] at hparam
  | live registers owned base outcome =>
      simp only [he, ReferenceLaterAssignmentFibreStep.dispatchParameters?, reduceCtorEq] at hparam
  | invalidCollectionCutoff =>
      simp only [he, ReferenceLaterAssignmentFibreStep.dispatchParameters?, reduceCtorEq] at hparam
  | dagger => simp only [he, ReferenceLaterAssignmentFibreStep.dispatchParameters?, reduceCtorEq] at hparam
  | collection payload ledger clock cutoff outcome =>
      rw [he] at hs hparam
      cases outcome <;>
        solve
        | rfl
        | simp only [ReferenceLaterAssignmentFibreStep.dispatchParameters?,
            ReferenceLaterAssignmentFibreStep.outcomeParameters?, reduceCtorEq] at hparam
        | simp only [ReferenceActivePhysicalStep.DispatchCut.selection, reduceCtorEq] at hs

/-- On a genuine chosen first call, the unrestricted source logging seed
produces ordinary unchanged PREPARE states. The same selected payload is live,
all confirmations are missing, and every follower is unoccupied. -/
theorem firstCall_selected_domain (u t : Fin p.T) (source : SourceInput p)
    (theta : AssignmentParameterFibreKernel.Theta p)
    (hcall : ReferenceFirstCollectionSamplerCall.firstCollectionCall
      rate rewards C_star C_h source = some (u, (t, theta)))
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t source = some r)
    (selected : ReferenceActivePhysicalStep.Selection r.input)
    (hselected : r.output.preparation.coordinator.selection = some selected) :
    ∃ ho : ReferenceLaterLiveNumericalReadout.preparedOrdinary r,
      ReferenceLaterLiveNumericalReadout.laterLiveDomain
        (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h) r ∧
      selected.view.pendingAtChoice = Finset.univ ∧
      ∀ i, (ReferenceLaterLiveNumericalReadout.preparedStates r ho i).status = .unoccupied ∧
        r.input.state.followers i = .ordinary
          (ReferenceLaterLiveNumericalReadout.preparedStates r ho i)
          (ReferenceLaterLiveNumericalReadout.preparedMemories r ho i) := by
  have hprep : r.output.preparation = ReferenceActivePhysicalStep.prepare r.input := by
    rw [r.output_eq]
    rfl
  have hparameter : ReferenceLaterSamplerParameterMeasurability.parameters? r.input = some theta := by
    have hp := firstCall_calendarParameters rate rewards C_star C_h u t source theta hcall
    simpa only [ReferenceCalendarLaterSamplerPredictability.calendarParameters,
      hr, Option.bind_some] using hp
  have hchosen := selected_laterChosen rate r.input theta hparameter selected
    (by rw [← hprep]; exact hselected)
  have halign := firstCall_firstReplacementRecord rate rewards C_star C_h
    u t source theta hcall r hr hchosen
  have seed := ReferenceFirstReplacementFollowerLoggingSeed.complete_first_replacement_follower_logging_seed
    rate source rewards C_star C_h
  dsimp only at seed halign
  rw [halign] at seed
  dsimp only at seed
  cases he : r.output.preparation.coordinator with
  | first outcome => simp only [ReferenceCollectionPhaseHistory.laterChosen, ← hprep, he, Bool.false_eq_true] at hchosen
  | live registers owned base outcome => simp only [ReferenceCollectionPhaseHistory.laterChosen, ← hprep, he, Bool.false_eq_true] at hchosen
  | invalidCollectionCutoff => simp only [ReferenceCollectionPhaseHistory.laterChosen, ← hprep, he, Bool.false_eq_true] at hchosen
  | dagger => simp only [ReferenceCollectionPhaseHistory.laterChosen, ← hprep, he, Bool.false_eq_true] at hchosen
  | collection old ledger clock cutoff outcome =>
      cases outcome <;> simp only [ReferenceCollectionPhaseHistory.laterChosen, ← hprep, he, Bool.false_eq_true] at hchosen
      rename_i core consistent started hstart instruction hi output hlocal clockData installed arm
      rw [he] at seed hselected
      dsimp only at seed
      obtain ⟨_hinstalled, hold, _ht, _hrows, _hselected, _hrewards, hsigma, followers⟩ := seed
      have frames := ReferenceCoordinatorRecorderCallCorrespondence.actual_call_frames r
      rw [he] at frames
      dsimp only at frames
      have hsel := ReferenceCoordinatorRecorderCallCorrespondence.selectionAt_eq r.input
        installed.registers.payload started instruction.time installed.registers.complementWeights
        arm frames.1
      simp only [ReferenceActivePhysicalStep.DispatchCut.selection, hsel, Option.some.injEq] at hselected
      subst selected
      have hex : ∀ i : Fin (p.m - 1), ∃ old memory,
          r.input.state.followers i = .ordinary old memory ∧ old.status = .unoccupied ∧
          (r.output.preparation.followers.followers i).configuration = .ordinary old memory := by
        intro i
        obtain ⟨old, memory, _logged, hin, hu, _hdomain, _hbuffer, _hdecoder, _hbatch,
          _hmass, _hsaved, _hkeys, _hgrid, _horder, _hbefore, _hold,
          _hstart, _hprepared, hconfiguration, _hrest⟩ := followers i
        exact ⟨old, memory, hin, hu, hconfiguration⟩
      choose states memories hstates using hex
      have ho : ReferenceLaterLiveNumericalReadout.preparedOrdinary r := by
        intro i
        simp only [ReferenceLaterLiveNumericalReadout.ordinaryData, (hstates i).2.2,
          Option.isSome_some]
      have hcanonical (i : Fin (p.m - 1)) :
          ReferenceLaterLiveNumericalReadout.preparedStates r ho i = states i ∧
          ReferenceLaterLiveNumericalReadout.preparedMemories r ho i = memories i := by
        simp only [ReferenceLaterLiveNumericalReadout.preparedStates,
          ReferenceLaterLiveNumericalReadout.preparedMemories,
          (hstates i).2.2, ReferenceLaterLiveNumericalReadout.ordinaryData, Option.get_some]
        exact ⟨trivial, trivial⟩
      have hclockSigma : clock.sigma = some old.sigma := core.clock_sigma_eq
      have hclockCutoff : clock.u = some cutoff := core.clock_cutoff_eq
      have htimeValid : CoordinatorPhaseClock.startRoundTimeValid p r.input.time clock :=
        core.clock_start_time_valid
      simp only [CoordinatorPhaseClock.startRoundTimeValid, hclockSigma, hclockCutoff] at htimeValid
      have hlt : ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h <
          installed.registers.payload.sigma.val := by
        rw [hsigma, ← hold]
        exact htimeValid.1
      have effects := CoordinatorPhaseClock.startRound_assignment_effect p rate.eta.val
        r.input.time clock ledger.pending started instruction core.clock_parameter_valid
        core.clock_registers_valid core.clock_start_time_valid hstart hi
      refine ⟨ho, ⟨ReferenceCoordinatorRecorderCallCorrespondence.selectionOfArm r.input
        installed.registers.payload started instruction.time installed.registers.complementWeights
        arm frames.1, ?_, hlt, frames.2.1, ho⟩, effects.2.2.2.2.2.2.1, ?_⟩
      · rw [he]
        exact hsel
      · intro i
        rw [(hcanonical i).1, (hcanonical i).2]
        exact ⟨(hstates i).2.1, (hstates i).1⟩

/-- The actual new-start snapshot, on the existing assignment carrier. -/
def firstSnapshot (assignment : ActiveRoundActions.Assignment p.m p.K) :
    ActiveRoundActions.Snapshot assignment :=
  { missing := Finset.univ, status := fun _ => .unoccupied }

/-- The genuine recording map with the actual selected view's full weights. -/
def viewRecordingMap (t : Fin p.T) (view : ReferenceDownReception.ChoiceTimeView p rate.eta)
    (valid : CoordinatorLocalArmChoice.ChoiceInputsValid view.payload view.cutoff t
      view.complementWeights) (v : AssignmentVector p) (w : ControlRemainder p) : Option (Fin p.K) :=
  SnapshotRecordingKernel.recordingMap p (.live view.payload.assignment (firstSnapshot view.payload.assignment))
    true rate.eta.val rate.eta.property rate.sourceCap view.payload.anchor
    (ReferenceFirstWindowNumericalStream.sourceWeights view.payload view.complementWeights)
    view.payload.anchor_pos
    (ReferenceFirstWindowNumericalStream.sourceWeights_pos _ _ _ _ valid)
    (ReferenceFirstWindowNumericalStream.sourceWeights_lower _ _ _ _ valid)
    (ReferenceFirstWindowNumericalStream.sourceWeights_upper _ _ _ _ valid)
    (currentControl v w).1

/-- Conditional branch helper: its sole extra premise is the literal actual
selected-view observation. Every ordinary state and validity fact is produced
from the same source, rather than supplied by the caller. -/
theorem currentRemainder_marker_on_present (control0 : TimeControl p) (u t : Fin p.T)
    (z : SourceInput p)
    (hz : z ∈ ReferenceCalendarCollectionCallControlLaw.firstCell rate rewards C_star C_h u t)
    (v : AssignmentVector p) (view : ReferenceDownReception.ChoiceTimeView p rate.eta)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (hphi : currentParameters rate rewards C_star C_h control0 t z v
      (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p control0).2 = some (view, started)) :
    ∃ valid : CoordinatorLocalArmChoice.ChoiceInputsValid view.payload view.cutoff t view.complementWeights,
      ∀ w : ControlRemainder p,
        currentMarker rate rewards C_star C_h control0 t z v w =
          some (viewRecordingMap rate t view valid v w) ∧
        ∃ (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
          (c : RecordedQueueRun.RoundInput p.K),
          ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t
            (currentSource control0 t z v w) = some r ∧
          ReferenceLaterLiveNumericalReadout.laterLiveReadout
            (ReferenceCompletePhysicalHistory.physicalStart rate
              (currentSource control0 t z v w) rewards C_star C_h) r = some c ∧
          c.recordedArm = viewRecordingMap rate t view valid v w ∧
          ReferenceContinuingRecordingFastPair.physicalMarkerOnRecord r view.payload true =
            viewRecordingMap rate t view valid v w ∧
          (∀ a, c.recordedArm = some a → ∃ owner : Fin p.m,
            SnapshotRecordingKernel.owns p
              (.live view.payload.assignment (firstSnapshot view.payload.assignment)) owner a ∧
            (∀ other, SnapshotRecordingKernel.owns p
              (.live view.payload.assignment (firstSnapshot view.payload.assignment)) other a → other = owner) ∧
            r.output.preparation.arms.actions owner = a ∧ r.gridFeedback owner = rewards t a) ∧
          (∀ i, PublicDiscreteDraws.slotDraw (r.input.row.2 r.input.time).1 = PublicDiscreteDraws.dataSlot →
            ∃ (state : ReferencePrelaunchFollower.State p rate.eta)
              (memory : ActiveFollowerLifecycle.LocalMemory p) (logged : ReferencePrelaunchFollower.State p rate.eta),
              r.input.state.followers i = .ordinary state memory ∧ state.status = .unoccupied ∧
              (r.output.preparation.followers.followers i).configuration = .ordinary state memory ∧
              ActiveFollowerLogging.checkedLogging i r.input.row (r.input.state.activations i) r.input.time
                (r.output.ownEntries (PublicDiscreteDraws.followerPlayer p.two_le_m i)) state = .ok logged ∧
              (r.output.followers i).downInput = some logged ∧
              logged.buffer = state.buffer ++ ReferenceFollowerBufferProvenance.logEmission i r ∧
              ∀ saved ∈ ReferenceFollowerBufferProvenance.logEmission i r, saved ∈ logged.buffer) := by
  obtain ⟨theta, hcall⟩ := firstCell_call rate rewards C_star C_h u t z hz
  have data (w : ControlRemainder p) :
      ∃ (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
        (selected : ReferenceActivePhysicalStep.Selection r.input),
        ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t
          (currentSource control0 t z v w) = some r ∧ r.input.time = t ∧
        r.output.preparation.coordinator.selection = some selected ∧ selected.view = view := by
    obtain ⟨r, hr, ht, _⟩ := firstCall_record rate rewards C_star C_h u t
      (currentSource control0 t z v w) theta
      (currentSource_firstCall rate rewards C_star C_h control0 u t z theta hcall v w)
    have hp := (currentRemainder_parameters_factor rate rewards C_star C_h control0 u t z hz v w).1.trans hphi
    simp only [currentParameters, hr, Option.bind_some] at hp
    obtain ⟨selected, hsel, hpair⟩ := Option.map_eq_some_iff.mp hp
    exact ⟨r, selected, hr, ht, hsel, congrArg Prod.fst hpair⟩
  obtain ⟨r0, s0, _hr0, ht0, _hs0, hv0⟩ :=
    data (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p control0).2
  have valid : CoordinatorLocalArmChoice.ChoiceInputsValid view.payload view.cutoff t
      view.complementWeights := by
    cases hv0
    simpa only [ht0] using ReferenceLaterLiveNumericalReadout.selection_choiceValid s0
  refine ⟨valid, ?_⟩
  intro w
  obtain ⟨r, selected, hr, ht, hsel, hv⟩ := data w
  have hcall' := currentSource_firstCall rate rewards C_star C_h control0 u t z theta hcall v w
  obtain ⟨ho, hdomain, hpending, hstates⟩ := firstCall_selected_domain rate rewards C_star C_h
    u t (currentSource control0 t z v w) theta hcall' r hr selected hsel
  obtain ⟨sel, hsel', hstart, hlive, _⟩ := hdomain
  have heq : sel = selected := Option.some.inj (hsel'.symm.trans hsel)
  subst sel
  let c := ReferenceFirstWindowNumericalStream.sourceCell r selected.view.payload
    selected.view.pendingAtChoice (ReferenceLaterLiveNumericalReadout.preparedStates r ho)
    selected.view.complementWeights selected.view.cutoff
    (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected)
  have hread : ReferenceLaterLiveNumericalReadout.laterLiveReadout
      (ReferenceCompletePhysicalHistory.physicalStart rate (currentSource control0 t z v w)
        rewards C_star C_h) r = some c := by
    simp only [ReferenceLaterLiveNumericalReadout.laterLiveReadout, hsel,
      ite_eq_left (And.intro hstart hlive), dite_eq_left ho]
    rfl
  obtain ⟨hrows, hj, _⟩ := actualRecord_input_fields rate rewards C_star C_h t
    (currentSource control0 t z v w) r hr
  have hrow : (r.input.row.2 r.input.time).1 = (currentControl v w).1 := by
    rw [ht]
    change ((r.input.rows r.input.selected).2 t).1 = _
    rw [hrows, hj]
    simp [currentSource, ReferenceFixedTimeSourceControlCoupling.replaceSourceControl,
      ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex,
      ReferenceSourcePrefixHistoryFiltration.sourcePrefix, selectedRowIndex]
  have hstatus : (fun i => (ReferenceLaterLiveNumericalReadout.preparedStates r ho i).status) =
      (fun _ => ActiveRoundActions.FollowerStatus.unoccupied) :=
    funext (fun i => (hstates i).1)
  have hsnapshot :
      (ActiveRoundActions.Snapshot.mk selected.view.pendingAtChoice
        (fun i => (ReferenceLaterLiveNumericalReadout.preparedStates r ho i).status) :
        ActiveRoundActions.Snapshot selected.view.payload.assignment) =
          firstSnapshot selected.view.payload.assignment :=
    congrArg₂ (fun missing status => (ActiveRoundActions.Snapshot.mk missing status :
      ActiveRoundActions.Snapshot selected.view.payload.assignment)) hpending hstatus
  have hmark : c.recordedArm = viewRecordingMap rate t view valid v w := by
    cases hv
    cases ht
    dsimp only [c, ReferenceFirstWindowNumericalStream.sourceCell,
      ReferenceFirstWindowNumericalStream.sourceArm, viewRecordingMap]
    rw [hsnapshot, hrow]
  have hM : currentMarker rate rewards C_star C_h control0 t z v w = some c.recordedArm := by
    simp only [currentMarker, hr, Option.bind_some, hread, Option.map_some]
  refine ⟨hM.trans (congrArg some hmark), r, c, hr, hread, hmark, ?_⟩
  have hr' := hr
  unfold ReferenceSourcePrefixHistoryFiltration.actualRecord at hr'
  split_ifs at hr' with hs
  obtain ⟨hk, hget⟩ := List.getElem?_eq_some_iff.mp hr'
  let k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords rate
      (currentSource control0 t z v w) rewards C_star C_h).length := ⟨_, hk⟩
  have hindex : (ReferenceCompletePhysicalHistory.completeSuffixRecords rate
      (currentSource control0 t z v w) rewards C_star C_h).get k = r := hget
  have hread' : ReferenceLaterLiveNumericalReadout.laterLiveReadout
      (ReferenceCompletePhysicalHistory.physicalStart rate (currentSource control0 t z v w) rewards C_star C_h)
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords rate
        (currentSource control0 t z v w) rewards C_star C_h).get k) = some c := by
    rw [hindex]
    exact hread
  have physical := ReferenceLaterLiveNumericalReadout.laterLiveReadout_physical
    rate rewards C_star C_h (currentSource control0 t z v w) k c hread'
  dsimp only at physical
  rw [hindex] at physical
  obtain ⟨cell, _hc, _hen, _hlive, _henabled, _hrows, _hj, _hrewards,
    hphysical, _hdown, howner, _hgate, _hunoccupied, hlogging, _hrecording, _hcollection⟩ := physical
  have hcellSel : cell.selected = selected := Option.some.inj
    (cell.selection_actual.symm.trans hsel)
  have hcellStates (i : Fin (p.m - 1)) :
      cell.states i = ReferenceLaterLiveNumericalReadout.preparedStates r ho i := by
    have h := (cell.ordinary i).symm.trans
      (ReferenceLaterLiveNumericalReadout.prepared_configuration r ho i)
    have h' := congrArg ReferenceLaterLiveNumericalReadout.ordinaryData h
    simp only [ReferenceLaterLiveNumericalReadout.ordinaryData, Option.some.injEq, Prod.mk.injEq] at h'
    exact h'.1
  rw [hcellSel, hv] at hphysical
  refine ⟨hphysical.symm.trans hmark, ?_, ?_⟩
  · cases hv
    have hsnapshot' : ReferenceActiveDataOwnership.choiceSnapshot selected cell.states =
        firstSnapshot selected.view.payload.assignment := by
      dsimp only [ReferenceActiveDataOwnership.choiceSnapshot]
      rw [show cell.states = ReferenceLaterLiveNumericalReadout.preparedStates r ho from funext hcellStates]
      rw [← selected.pending_eq]
      exact hsnapshot
    rw [hcellSel, hsnapshot'] at howner
    intro a ha
    obtain ⟨owner, hown, huniq, haction, hfeedback, _⟩ := howner a ha
    exact ⟨owner, hown, huniq, haction, by simpa only [ht] using hfeedback⟩
  · intro i hslot
    have hstatusCell : (cell.states i).status = .unoccupied := by
      rw [hcellStates]
      exact (hstates i).1
    obtain ⟨logged, hlog, hdown, hbuffer⟩ := hlogging i hstatusCell hslot
    have hbuffer' : logged.buffer =
        (ReferenceLaterLiveNumericalReadout.preparedStates r ho i).buffer ++
          ReferenceFollowerBufferProvenance.logEmission i r := by
      simpa only [hcellStates] using hbuffer
    refine ⟨_, _, logged, (hstates i).2, (hstates i).1,
      ReferenceLaterLiveNumericalReadout.prepared_configuration r ho i,
      ?_, hdown, hbuffer', ?_⟩
    · simpa only [hcellStates] using hlog
    · intro saved hsaved
      rw [hbuffer']
      exact List.mem_append_right _ hsaved

/-- Absence of the literal selected view is absence of the numerical cell,
and is distinct from the present bottom marker. -/
theorem currentMarker_none_of_parameters_none (control0 : TimeControl p) (t : Fin p.T)
    (z : SourceInput p) (v : AssignmentVector p) (w : ControlRemainder p)
    (hphi : currentParameters rate rewards C_star C_h control0 t z v w = none) :
    currentMarker rate rewards C_star C_h control0 t z v w = none := by
  unfold currentParameters at hphi
  unfold currentMarker
  dsimp only
  cases hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t
      (currentSource control0 t z v w) with
  | none => simp only [Option.bind_none]
  | some r =>
      simp only [hr, Option.bind_some, Option.map_eq_none_iff] at hphi
      simp only [Option.bind_some, ReferenceLaterLiveNumericalReadout.laterLiveReadout,
        hphi, Option.map_none]

theorem viewRecordingMap_measurable (t : Fin p.T)
    (view : ReferenceDownReception.ChoiceTimeView p rate.eta)
    (valid : CoordinatorLocalArmChoice.ChoiceInputsValid view.payload view.cutoff t view.complementWeights)
    (v : AssignmentVector p) : Measurable (viewRecordingMap rate t view valid v) := by
  exact (SnapshotRecordingKernel.measurable_recordingMap p
    (.live view.payload.assignment (firstSnapshot view.payload.assignment)) rate.eta.val
    rate.eta.property rate.sourceCap view.payload.anchor
    (ReferenceFirstWindowNumericalStream.sourceWeights view.payload view.complementWeights)
    view.payload.anchor_pos
    (ReferenceFirstWindowNumericalStream.sourceWeights_pos _ _ _ _ valid)
    (ReferenceFirstWindowNumericalStream.sourceWeights_lower _ _ _ _ valid)
    (ReferenceFirstWindowNumericalStream.sourceWeights_upper _ _ _ _ valid) true).comp
      (measurable_fst.comp (currentControl_measurable.comp
        (measurable_const.prodMk measurable_id)))

/-- The actual optional marker is Borel in ALL remaining current coordinates. -/
theorem currentMarker_measurable (control0 : TimeControl p) (u t : Fin p.T)
    (z : SourceInput p)
    (hz : z ∈ ReferenceCalendarCollectionCallControlLaw.firstCell rate rewards C_star C_h u t)
    (v : AssignmentVector p) :
    Measurable (currentMarker rate rewards C_star C_h control0 t z v) := by
  cases hp : currentParameters rate rewards C_star C_h control0 t z v
      (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p control0).2 with
  | none =>
      have heq : currentMarker rate rewards C_star C_h control0 t z v = fun _ => none := by
        funext w
        exact currentMarker_none_of_parameters_none rate rewards C_star C_h control0 t z v w
          ((currentRemainder_parameters_factor rate rewards C_star C_h control0 u t z hz v w).1.trans hp)
      rw [heq]
      exact measurable_const
  | some q =>
      obtain ⟨valid, hpoint⟩ := currentRemainder_marker_on_present rate rewards C_star C_h
        control0 u t z hz v q.1 q.2 hp
      have heq : currentMarker rate rewards C_star C_h control0 t z v =
          fun w => some (viewRecordingMap rate t q.1 valid v w) := funext (fun w => (hpoint w).1)
      rw [heq]
      exact (measurable_of_countable
        (some : Option (Fin p.K) → Option (Option (Fin p.K)))).comp
          (viewRecordingMap_measurable rate t q.1 valid v)

/-- The literal optional current recording law, at fixed WHOLE assignment
vector. Failed dispatches retain their absence mass; present bottom and real
marks, including zero quantized arrivals, retain separate outcomes. -/
theorem currentRemainder_optionalMarker_law (control0 : TimeControl p) (u t : Fin p.T)
    (z : SourceInput p)
    (hz : z ∈ ReferenceCalendarCollectionCallControlLaw.firstCell rate rewards C_star C_h u t)
    (v : AssignmentVector p) :
    (ReferenceLaterOptionalControlResampling.controlRemainderLaw p).map
        (currentMarker rate rewards C_star C_h control0 t z v) =
      match currentParameters rate rewards C_star C_h control0 t z v
          (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p control0).2 with
      | none => Measure.dirac none
      | some (view, _started) =>
          ((RecordedRoundMoments.recordingOutcomePMF
            (SnapshotRecordingKernel.recordingRates p rate.eta.val rate.eta.property rate.sourceCap
              view.payload.anchor view.payload.anchor_pos)).toMeasure).map some := by
  cases hp : currentParameters rate rewards C_star C_h control0 t z v
      (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p control0).2 with
  | none =>
      have heq : currentMarker rate rewards C_star C_h control0 t z v = fun _ => none := by
        funext w
        exact currentMarker_none_of_parameters_none rate rewards C_star C_h control0 t z v w
          ((currentRemainder_parameters_factor rate rewards C_star C_h control0 u t z hz v w).1.trans hp)
      rw [heq]
      simp
  | some q =>
      obtain ⟨valid, hpoint⟩ := currentRemainder_marker_on_present rate rewards C_star C_h
        control0 u t z hz v q.1 q.2 hp
      have heq : currentMarker rate rewards C_star C_h control0 t z v =
          some ∘ viewRecordingMap rate t q.1 valid v := funext (fun w => (hpoint w).1)
      have hsome : Measurable (some : Option (Fin p.K) → Option (Option (Fin p.K))) :=
        measurable_of_countable _
      rw [heq, ← Measure.map_map hsome (viewRecordingMap_measurable rate t q.1 valid v)]
      change ((ReferenceLaterOptionalControlResampling.controlRemainderLaw p).map
        (viewRecordingMap rate t q.1 valid v)).map some = _
      congr 1
      exact map_recordingMap_currentRemainder rate
        (.live q.1.payload.assignment (firstSnapshot q.1.payload.assignment))
        q.1.payload.anchor
        (ReferenceFirstWindowNumericalStream.sourceWeights q.1.payload q.1.complementWeights)
        q.1.payload.anchor_pos
        (ReferenceFirstWindowNumericalStream.sourceWeights_pos _ _ _ _ valid)
        (ReferenceFirstWindowNumericalStream.sourceWeights_lower _ _ _ _ valid)
        (ReferenceFirstWindowNumericalStream.sourceWeights_upper _ _ _ _ valid) v

end Bandits.Support.ReferenceFirstCollectionCurrentRemainderLaw
