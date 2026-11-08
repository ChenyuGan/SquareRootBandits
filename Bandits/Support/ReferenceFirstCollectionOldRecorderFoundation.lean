/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionCurrentExponentialQueueStep
public import Bandits.Support.ReferenceFirstLiveCalendarExponentialBound

/-!
# Original-source OLD recorder foundation

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:140-188,245-284`,
`05_binary_transport.tex:352-431`, and `06_interruptions.tex:35-100,355-426`.

This module extracts completed local OLD-recorder results from the original
physical history and source law. It retains the incoming payload, anchor, and
rates; distinguishes outer absence from a present bottom cell; and defines the
pre-call selector without inspecting any future first-call event. It proves the
actual recording-map identity and payload, rate, reward, and enabled-bit
identities; predictable incoming data and floor amplitude; fresh-control
follower-snapshot stability with its UP-admissibility producer; and raw
boundedness, measurability, integrability, and conditional floor-amplitude
factorization.

The conditional arm/bottom mass remains an explicit unresolved conditional
expectation. This module does not prove full selector factorization or prefix
measurability, arm/bottom mass evaluation, or calendar support, and makes no
claim of manuscript theorem closure.
-/


@[expose] public section

noncomputable section

open MeasureTheory
open scoped Classical BigOperators

namespace Bandits.Support.ReferenceFirstCollectionOldRecorderFoundation

open ConstructorDimensions (Parameters D D_pos)
open ReferenceActivePhysicalStep (RateInput Payload)
open ActualInitializationPhysicalStep (GridRewardTable)
open BootstrapPrivateRoundStreams (SourceInput sourceInputLaw)
open ContinuousLearningRows (TimeControl)
open ReferenceSourcePrefixHistoryFiltration
  (actualRecord incoming sourcePrefix sourcePrefixFiltration)
open ReferenceCalendarCollectionCallControlLaw (callAt)

variable {p : Parameters}

local instance optionMeasurableSpace {A : Type*} [MeasurableSpace A] :
    MeasurableSpace (Option A) := LaterAssignmentStartMeasurability.optionMeasurableSpace

private theorem measurable_option_map {X A B : Type*}
    [MeasurableSpace X] [MeasurableSpace A] [MeasurableSpace B]
    (o : X → Option A) (ho : Measurable o) (f : A → B) (hf : Measurable f) :
    Measurable (fun x => (o x).map f) := by
  have hs : Measurable (Sum.elim (fun a => some (f a))
      (fun _ : PUnit => (none : Option B))) :=
    (LaterAssignmentFullOutputMeasurability.measurable_some_of_measurable f hf).sumElim
      measurable_const
  have h := hs.comp ((comap_measurable (Equiv.optionEquivSumPUnit A)).comp ho)
  convert h using 1
  funext x
  dsimp only [Function.comp_apply]
  cases o x <;> rfl

private theorem measurable_option_bind {X A B : Type*}
    [MeasurableSpace X] [MeasurableSpace A] [MeasurableSpace B]
    (o : X → Option A) (ho : Measurable o)
    (f : A → Option B) (hf : Measurable f) :
    Measurable (fun x => (o x).bind f) := by
  have hs : Measurable (Sum.elim f (fun _ : PUnit => (none : Option B))) :=
    hf.sumElim measurable_const
  have h := hs.comp ((comap_measurable (Equiv.optionEquivSumPUnit A)).comp ho)
  convert h using 1
  funext x
  dsimp only [Function.comp_apply]
  cases o x <;> rfl

private theorem measurableSet_optionNone {A : Type*} [MeasurableSpace A] :
    MeasurableSet ({none} : Set (Option A)) := by
  change MeasurableSet[(inferInstance : MeasurableSpace (A ⊕ PUnit)).comap
    (Equiv.optionEquivSumPUnit A)] {none}
  rw [MeasurableSpace.measurableSet_comap]
  refine ⟨Set.range (Sum.inr : PUnit → A ⊕ PUnit), measurableSet_range_inr, ?_⟩
  ext value
  cases value <;> simp

/-- Literal payload projection from the accepted lossless coordinator code.
The payload carrier keeps its established continuous measurable space. -/
def payloadFromCode? (rate : RateInput p) :
    ReferenceActivePhysicalStepMeasurability.CoordinatorCode p rate → Option (Payload rate)
  | .inr (.inl (payload, _)) => some payload
  | .inr (.inr (.inl (payload, _))) => some payload
  | _ => none

theorem payloadFromCode_measurable (rate : RateInput p) :
    Measurable (payloadFromCode? rate) := by
  apply measurable_fun_sum measurable_const
  apply measurable_fun_sum
  · exact LaterAssignmentFullOutputMeasurability.measurable_some_of_measurable _
      measurable_fst
  · apply measurable_fun_sum
    · exact LaterAssignmentFullOutputMeasurability.measurable_some_of_measurable _
        measurable_fst
    · exact measurable_const

theorem payloadFromCode_encode (rate : RateInput p)
    (c : ReferenceActivePhysicalStep.CoordinatorConfiguration p rate) :
    payloadFromCode? rate (ReferenceActivePhysicalStepMeasurability.encodeCoordinator c) =
      ReferenceAssignmentPayloadPersistence.storedPayload c := by
  cases c <;> rfl

variable (rate : RateInput p) (rewards : GridRewardTable p) (C_star C_h : ℝ)

/-- The actual OLD candidate payload before this round's dispatch. This reads
the sole incoming store; it does not install or reconstruct another state. -/
def incomingPayload? (r : Fin p.T) (z : SourceInput p) : Option (Payload rate) :=
  (actualRecord rate rewards C_star C_h r z).bind fun record =>
    ReferenceAssignmentPayloadPersistence.storedPayload record.input.state.coordinator

/-- Original optional full anchor vector. -/
def incomingAnchor? (r : Fin p.T) (z : SourceInput p) : Option (Fin p.K → ℝ) :=
  (incomingPayload? rate rewards C_star C_h r z).map (fun payload => payload.anchor)

/-- Original optional full dyadic recording-rate vector. -/
def incomingRates? (r : Fin p.T) (z : SourceInput p) : Option (Fin p.K → ℝ) :=
  (incomingPayload? rate rewards C_star C_h r z).map (fun payload => payload.rate)

theorem incomingPayload_eq_code (r : Fin p.T) (z : SourceInput p) :
    incomingPayload? rate rewards C_star C_h r z =
      (incoming rate rewards C_star C_h r z).bind
        (fun code => payloadFromCode? rate code.1) := by
  unfold incomingPayload? incoming
  cases actualRecord rate rewards C_star C_h r z with
  | none => rfl
  | some record =>
      simpa only [Option.map_some, Option.bind_some,
        ReferenceActivePhysicalStepMeasurability.encodeState] using
        (payloadFromCode_encode rate record.input.state.coordinator).symm

theorem incomingPayload_measurable (control0 : TimeControl p) (r : Fin p.T) :
    Measurable[sourcePrefixFiltration control0 (r.val + 1)]
      (incomingPayload? rate rewards C_star C_h r) := by
  let : MeasurableSpace (SourceInput p) := sourcePrefixFiltration control0 (r.val + 1)
  have h := measurable_option_bind _
    (ReferenceSourcePrefixHistoryFiltration.incoming_measurable
      rate rewards C_star C_h control0 r) _
    ((payloadFromCode_measurable rate).comp measurable_fst)
  convert h using 1
  funext z
  exact incomingPayload_eq_code rate rewards C_star C_h r z

theorem incomingAnchor_measurable (control0 : TimeControl p) (r : Fin p.T) :
    Measurable[sourcePrefixFiltration control0 (r.val + 1)]
      (incomingAnchor? rate rewards C_star C_h r) := by
  let : MeasurableSpace (SourceInput p) := sourcePrefixFiltration control0 (r.val + 1)
  exact measurable_option_map _
    (incomingPayload_measurable rate rewards C_star C_h control0 r) _
    AssignmentPayloadDerivedMeasurability.measurable_inputAnchor

theorem incomingRates_measurable (control0 : TimeControl p) (r : Fin p.T) :
    Measurable[sourcePrefixFiltration control0 (r.val + 1)]
      (incomingRates? rate rewards C_star C_h r) := by
  let : MeasurableSpace (SourceInput p) := sourcePrefixFiltration control0 (r.val + 1)
  exact measurable_option_map _
    (incomingPayload_measurable rate rewards C_star C_h control0 r) _
    AssignmentPayloadDerivedMeasurability.measurable_inputRate

theorem incomingPayload_factor (control0 : TimeControl p) (r : Fin p.T)
    (z : SourceInput p) :
    incomingPayload? rate rewards C_star C_h r z =
      incomingPayload? rate rewards C_star C_h r (sourcePrefix control0 r.val z) := by
  rw [incomingPayload_eq_code, incomingPayload_eq_code,
    ReferenceSourcePrefixHistoryFiltration.incoming_factor
      rate rewards C_star C_h control0 r z]

/-- A whole current-control replacement leaves every earlier selected control,
all private coordinates, IDs, forwards and unselected rows in this prefix equal.
-/
theorem sourcePrefix_replaceCurrent (control0 : TimeControl p) (r : Fin p.T)
    (n : ℕ) (hn : n ≤ r.val) (z : SourceInput p) (fresh : TimeControl p) :
    sourcePrefix control0 n
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p r z fresh) =
      sourcePrefix control0 n z := by
  apply Prod.ext
  · refine Prod.ext rfl ?_
    funext q
    by_cases hq : q = ActualInitializationPhysicalStep.selectedRowIndex p z
    · subst q
      simp only [sourcePrefix,
        ReferenceFixedTimeSourceControlCoupling.replaceSourceControl,
        ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex,
        ActualInitializationPhysicalStep.selectedRowIndex, Function.update_self]
      refine Prod.ext rfl ?_
      funext v
      by_cases hv : v.val < n
      · have hvr : v ≠ r := by intro h; subst v; omega
        simp only [hv, ite_true, Function.update_of_ne hvr]
      · simp only [hv, ite_false]
    · have hq' : q ≠ PrivateSourceStreams.coordinatorIndex p z.2.1.2 := hq
      simp only [sourcePrefix,
        ReferenceFixedTimeSourceControlCoupling.replaceSourceControl,
        ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex,
        ActualInitializationPhysicalStep.selectedRowIndex,
        Function.update_of_ne hq']
  · rfl

/-- Stability of the genuine incoming payload under every complete control
replacement, without a stability or adaptedness premise. -/
theorem incomingPayload_replaceCurrent (control0 : TimeControl p) (r : Fin p.T)
    (z : SourceInput p) (fresh : TimeControl p) :
    incomingPayload? rate rewards C_star C_h r
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p r z fresh) =
      incomingPayload? rate rewards C_star C_h r z := by
  rw [incomingPayload_factor rate rewards C_star C_h control0 r,
    sourcePrefix_replaceCurrent control0 r r.val le_rfl,
    ← incomingPayload_factor rate rewards C_star C_h control0 r]

theorem incomingAnchor_replaceCurrent (control0 : TimeControl p) (r : Fin p.T)
    (z : SourceInput p) (fresh : TimeControl p) :
    incomingAnchor? rate rewards C_star C_h r
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p r z fresh) =
      incomingAnchor? rate rewards C_star C_h r z := by
  unfold incomingAnchor?
  rw [incomingPayload_replaceCurrent rate rewards C_star C_h control0]

theorem incomingRates_replaceCurrent (control0 : TimeControl p) (r : Fin p.T)
    (z : SourceInput p) (fresh : TimeControl p) :
    incomingRates? rate rewards C_star C_h r
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p r z fresh) =
      incomingRates? rate rewards C_star C_h r z := by
  unfold incomingRates?
  rw [incomingPayload_replaceCurrent rate rewards C_star C_h control0]

/-- No original later invocation before or at the present date. Failed and
absent calls are retained as their actual `none` observations. -/
def beforeCall (r : Fin p.T) : Set (SourceInput p) :=
  {z | ∀ v : Fin p.T, v.val ≤ r.val → callAt rate rewards C_star C_h v z = none}

theorem beforeCall_measurable (control0 : TimeControl p) (r : Fin p.T) :
    MeasurableSet[sourcePrefixFiltration control0 (r.val + 1)]
      (beforeCall rate rewards C_star C_h r) := by
  have heq : beforeCall rate rewards C_star C_h r =
      ⋂ v : Fin p.T, ⋂ (_ : v.val ≤ r.val),
        {z | callAt rate rewards C_star C_h v z = none} := by
    ext z
    simp only [beforeCall, Set.mem_ofPred_eq, Set.mem_iInter]
  rw [heq]
  apply MeasurableSet.iInter
  intro v
  apply MeasurableSet.iInter
  intro hv
  exact (sourcePrefixFiltration control0).mono (by omega : v.val + 1 ≤ r.val + 1)
    _ ((ReferenceCalendarCollectionCallControlLaw.callAt_measurable
      rate rewards C_star C_h control0 v) measurableSet_optionNone)

theorem beforeCall_replaceCurrent (control0 : TimeControl p) (r : Fin p.T)
    (z : SourceInput p) (fresh : TimeControl p) :
    ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p r z fresh ∈
        beforeCall rate rewards C_star C_h r ↔
      z ∈ beforeCall rate rewards C_star C_h r := by
  have hcall (v : Fin p.T) (hv : v.val ≤ r.val) :
      callAt rate rewards C_star C_h v
          (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p r z fresh) =
        callAt rate rewards C_star C_h v z := by
    rw [ReferenceCalendarCollectionCallControlLaw.callAt_factor
      rate rewards C_star C_h control0 v,
      sourcePrefix_replaceCurrent control0 r v.val hv,
      ← ReferenceCalendarCollectionCallControlLaw.callAt_factor
        rate rewards C_star C_h control0 v]
  constructor
  · intro hz v hv
    rw [← hcall v hv]
    exact hz v hv
  · intro hz v hv
    rw [hcall v hv]
    exact hz v hv

/-- Literal optional OLD cell: cutoff-head and continuing constructors of the
same original record, with the established ordinary/unoccupied follower test.
The zero boundary includes the first cutoff head. -/
def oldCell? (r : Fin p.T) (z : SourceInput p) :
    Option (RecordedQueueRun.RoundInput p.K) :=
  (actualRecord rate rewards C_star C_h r z).bind
    (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0)

/-- Computed local domain; chronological coverage of this domain is separate.
In particular this selector does not use a future collection endpoint. -/
def oldSelector (r : Fin p.T) : Set (SourceInput p) :=
  beforeCall rate rewards C_star C_h r ∩
    {z | (oldCell? rate rewards C_star C_h r z).isSome = true}

/-- Optional recording marker, keeping the two option layers. -/
def oldMarker? (r : Fin p.T) (z : SourceInput p) : Option (Option (Fin p.K)) :=
  (oldCell? rate rewards C_star C_h r z).map (fun c => c.recordedArm)

/-- Nominal normalized OLD raw arrival, before queue service or analytical stop.
-/
def oldRaw (r : Fin p.T) (a : Fin p.K) (z : SourceInput p) : ℝ :=
  match oldCell? rate rewards C_star C_h r z with
  | none => 0
  | some c => RecordedRoundMoments.normalizedQuantizedArrival
      (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a

theorem oldSelector_no_earlier_call (r : Fin p.T) (z : SourceInput p)
    (hz : z ∈ oldSelector rate rewards C_star C_h r) (v : Fin p.T)
    (hv : v.val < r.val) : callAt rate rewards C_star C_h v z = none :=
  hz.1 v hv.le

theorem oldSelector_current_call_absent (r : Fin p.T) (z : SourceInput p)
    (hz : z ∈ oldSelector rate rewards C_star C_h r) :
    callAt rate rewards C_star C_h r z = none := hz.1 r le_rfl

/-- The actual source supplies every physical recorder argument and the OLD
payload's rates, even when the cell is disabled or its floor is zero. -/
theorem oldCell_actual_call (r : Fin p.T) (z : SourceInput p)
    (hz : z ∈ oldSelector rate rewards C_star C_h r) :
    ∃ (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (c : RecordedQueueRun.RoundInput p.K) (payload : Payload rate)
      (ledger : ReferenceActivePhysicalStep.Ledger rate)
      (started : CoordinatorPhaseClock.StartRoundResult p)
      (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ)
      (out : CoordinatorRecordingOperation.Output p),
      actualRecord rate rewards C_star C_h r z = some record ∧
      oldCell? rate rewards C_star C_h r z = some c ∧
      ReferenceLaterCollectionArrivalReadout.laterCollectionCall 0 record =
        some ⟨payload, ledger, started, weights⟩ ∧
      record.coordinatorDiagnostics = ReferenceActivePhysicalStep.collectionPostChoice
        record.output.preparation payload ledger started weights ∧
      CoordinatorRecorderComplementBridge.run
        (ReferenceActivePhysicalStep.collectionRecordingInput record.output.preparation
          payload started weights) = some out ∧
      c.enabled = ReferenceActivePhysicalStep.collectionEnabled ledger record.input.time ∧
      c.enabled = decide (record.input.time.val + 1 < started.clock.g) ∧
      c.rate = payload.rate ∧
      c.reward = (fun a => ((rewards r a).val : ℝ) / (D p : ℝ)) ∧
      oldMarker? rate rewards C_star C_h r z = some out.gateArm ∧
      out.gateArm = c.recordedArm ∧
      (∀ a, CoordinatorCollectionLedger.localArrival
        (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder out) a =
          RecordedQueueRun.quantizedArrival
            (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a) := by
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hz.2
  obtain ⟨record, hr, hread⟩ := Option.bind_eq_some_iff.mp hc
  obtain ⟨payload, ledger, started, weights, out, hcall, hdiag, hrun,
    henabled, hclock, hrate, hreward, _hrecording, hgate, harrival⟩ :=
    ReferenceLaterCollectionArrivalReadout.laterCollectionReadout_call 0 record c hread
  have hf := ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields
    rate rewards C_star C_h r z record hr
  refine ⟨record, c, payload, ledger, started, weights, out, hr, hc,
    hcall, hdiag, hrun, henabled, hclock, hrate, ?_, ?_, hgate, harrival⟩
  · rw [hreward, hf.2.2.1, hf.2.2.2]
  · simp only [oldMarker?, hc, Option.map_some]
    exact congrArg some hgate.symm

private theorem dispatch_payload (x : ReferenceActivePhysicalStep.RoundInput p rate) :
    match ReferenceActivePhysicalStep.dispatch x with
    | .live registers _ _ _ =>
        ReferenceAssignmentPayloadPersistence.storedPayload x.state.coordinator =
          some registers.payload
    | .collection payload _ _ _ _ =>
        ReferenceAssignmentPayloadPersistence.storedPayload x.state.coordinator = some payload
    | _ => True := by
  cases hs : x.state.coordinator with
  | first =>
      simp only [ReferenceActivePhysicalStep.dispatch, hs, CoordinatorRoundDispatch.dispatch]
      trivial
  | live registers owned base =>
      simp only [ReferenceActivePhysicalStep.dispatch, hs, CoordinatorRoundDispatch.dispatch]
      rfl
  | collection payload ledger saved =>
      simp only [ReferenceActivePhysicalStep.dispatch, hs]
      by_cases hcut : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
      · simp only [dite_eq_left hcut, CoordinatorRoundDispatch.dispatch]
        rfl
      · simp only [dite_eq_right hcut]
  | dagger =>
      simp only [ReferenceActivePhysicalStep.dispatch, hs]

/-- Collection pilots and thinning do not read the current weight vector.
This is an equality of the existing recording maps with the same anchor. -/
theorem collectionMap_independent_currentWeights
    (enabled : Bool) (v w : Fin p.K → ℝ)
    (hv : ∀ a, 0 < v a) (hw : ∀ a, 0 < w a)
    (hvw : ∀ a, v a ≤ w a) (hwv : ∀ a, w a ≤ 2 * v a)
    (slice : CanonicalRecordingSlice.Slice p.m p.K) :
    SnapshotRecordingKernel.recordingMap p .collection enabled
        rate.eta.val rate.eta.property rate.sourceCap v w hv hw hvw hwv slice =
      SnapshotRecordingKernel.recordingMap p .collection enabled
        rate.eta.val rate.eta.property rate.sourceCap v v hv hv (fun _ => le_rfl)
        (fun a => by linarith [hv a]) slice := by
  rfl

private theorem readout_payload_snapshot
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (c : RecordedQueueRun.RoundInput p.K)
    (hread : ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 record = some c) :
    ∃ payload : Payload rate,
      ReferenceAssignmentPayloadPersistence.storedPayload record.input.state.coordinator =
        some payload ∧
      c.rate = payload.rate ∧
      c.recordedArm = SnapshotRecordingKernel.recordingMap p .collection c.enabled
        rate.eta.val rate.eta.property rate.sourceCap payload.anchor payload.anchor
        payload.anchor_pos payload.anchor_pos (fun _ => le_rfl)
        (fun a => by linarith [payload.anchor_pos a])
        (ContinuousLearningRows.sliceAt record.input.time record.input.row.2) := by
  have hp : (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 record).isSome =
      true := by rw [hread]; rfl
  obtain ⟨hf, hb⟩ :=
    (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout_domain 0 record).mp hp
  have hframe := dispatch_payload rate record.input
  have hprep : record.output.preparation.coordinator =
      ReferenceActivePhysicalStep.dispatch record.input := by
    rw [record.output_eq]
    rfl
  rw [← hprep] at hframe
  cases he : record.output.preparation.coordinator with
  | first outcome => simp only [he] at hb
  | invalidCollectionCutoff => simp only [he] at hb
  | dagger => simp only [he] at hb
  | collection payload ledger clock cutoff outcome =>
      cases outcome with
      | continuing core snapshot boundary scores =>
          have hc : ReferenceLaterCollectionArrivalReadout.continuingCollectionInput
              record payload ledger clock cutoff snapshot = c := by
            simpa only [ReferenceLaterCollectionArrivalReadout.laterCollectionReadout,
              dite_eq_left hf, he, Option.some.injEq] using hread
          subst c
          refine ⟨payload, ?_, rfl, ?_⟩
          · simpa only [he] using hframe
          · unfold ReferenceLaterCollectionArrivalReadout.continuingCollectionInput
            exact collectionMap_independent_currentWeights rate _ _ _ _ _ _ _ _
      | _ => simp only [he] at hb
  | live registers owned base outcome =>
      cases outcome with
      | cutoffChosen dispatched hstart ledger hinit hcand hdomain hclock hpending hnone selected =>
          have hpos : 0 < registers.payload.sigma.val := by simpa only [he] using hb
          have hc : ReferenceLaterCollectionArrivalReadout.laterCutoffCollectionInput
              record registers owned base dispatched selected = c := by
            simpa only [ReferenceLaterCollectionArrivalReadout.laterCollectionReadout,
              dite_eq_left hf, he, dite_eq_left hpos, Option.some.injEq] using hread
          subst c
          refine ⟨registers.payload, ?_, rfl, ?_⟩
          · simpa only [he] using hframe
          · unfold ReferenceLaterCollectionArrivalReadout.laterCutoffCollectionInput
            exact collectionMap_independent_currentWeights rate _ _ _ _ _ _ _ _
      | _ => simp only [he] at hb

/-- On the computed local OLD selector, the marker is the actual collection
map with precisely the payload already stored before dispatch. Its anchor is
not replaced by a constant or by a newly installed assignment. -/
theorem oldCell_recordingMap (r : Fin p.T) (z : SourceInput p)
    (hz : z ∈ oldSelector rate rewards C_star C_h r) :
    ∃ (payload : Payload rate) (c : RecordedQueueRun.RoundInput p.K),
      incomingPayload? rate rewards C_star C_h r z = some payload ∧
      oldCell? rate rewards C_star C_h r z = some c ∧
      c.rate = payload.rate ∧
      oldMarker? rate rewards C_star C_h r z = some
        (SnapshotRecordingKernel.recordingMap p .collection c.enabled
          rate.eta.val rate.eta.property rate.sourceCap payload.anchor payload.anchor
          payload.anchor_pos payload.anchor_pos (fun _ => le_rfl)
          (fun a => by linarith [payload.anchor_pos a])
          (ReferenceSourceCurrentControlFreshness.u_t p r z).1) := by
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hz.2
  obtain ⟨record, hr, hread⟩ := Option.bind_eq_some_iff.mp hc
  obtain ⟨payload, hp, hrate, hmarker⟩ := readout_payload_snapshot rate record c hread
  have hf := ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields
    rate rewards C_star C_h r z record hr
  refine ⟨payload, c, ?_, hc, hrate, ?_⟩
  · simp only [incomingPayload?, hr, Option.bind_some, hp]
  · simp only [oldMarker?, hc, Option.map_some]
    rw [hmarker]
    congr 2
    rw [ReferenceActivePhysicalStep.RoundInput.row, hf.1, hf.2.1, hf.2.2.1]
    rfl

/-- The actual cell's rates are the predictable original incoming rates. -/
theorem oldCell_rates_eq_incoming (r : Fin p.T) (z : SourceInput p)
    (hz : z ∈ oldSelector rate rewards C_star C_h r) :
    (oldCell? rate rewards C_star C_h r z).map (fun c => c.rate) =
      incomingRates? rate rewards C_star C_h r z := by
  obtain ⟨payload, c, hp, hc, hrate, _hm⟩ :=
    oldCell_recordingMap rate rewards C_star C_h r z hz
  simp only [incomingRates?, hp, hc, Option.map_some, hrate]

/-- Rounded reward at the original date, from the fixed whole reward table. -/
def roundedReward (r : Fin p.T) (a : Fin p.K) : ℝ :=
  ((rewards r a).val : ℝ) / (D p : ℝ)

theorem roundedReward_bounds (r : Fin p.T) (a : Fin p.K) :
    0 ≤ roundedReward rewards r a ∧ roundedReward rewards r a ≤ 1 := by
  refine ⟨div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _), ?_⟩
  apply (div_le_one (Nat.cast_pos.mpr (D_pos p))).2
  exact_mod_cast Nat.le_of_lt_succ (rewards r a).isLt

/-- The predictable floor amplitude uses the original incoming payload's
rate and the fixed whole reward table. Absence remains optional. -/
def incomingAmplitude? (r : Fin p.T) (a : Fin p.K) (z : SourceInput p) : Option ℝ :=
  (incomingPayload? rate rewards C_star C_h r z).map fun payload =>
    QuantizedRecordingMoments.quantizedValue (D p) rate.eta.val (payload.rate a)
      (roundedReward rewards r a)

private theorem measurable_payload_amplitude (r : Fin p.T) (a : Fin p.K) :
    Measurable (fun payload : Payload rate =>
      QuantizedRecordingMoments.quantizedValue (D p) rate.eta.val (payload.rate a)
        (roundedReward rewards r a)) := by
  have hrate : Measurable (fun payload : Payload rate => payload.rate a) :=
    (measurable_pi_apply a).comp AssignmentPayloadDerivedMeasurability.measurable_inputRate
  have harg : Measurable (fun payload : Payload rate =>
      ((D p : ℝ) * rate.eta.val * roundedReward rewards r a) / payload.rate a) :=
    measurable_const.div hrate
  have hfloor := (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp
    (Nat.measurable_floor.comp harg)
  exact hfloor.div_const _

theorem incomingAmplitude_measurable (control0 : TimeControl p)
    (r : Fin p.T) (a : Fin p.K) :
    Measurable[sourcePrefixFiltration control0 (r.val + 1)]
      (incomingAmplitude? rate rewards C_star C_h r a) := by
  let : MeasurableSpace (SourceInput p) := sourcePrefixFiltration control0 (r.val + 1)
  exact measurable_option_map _
    (incomingPayload_measurable rate rewards C_star C_h control0 r) _
    (measurable_payload_amplitude rate rewards r a)

theorem incomingAmplitude_replaceCurrent (control0 : TimeControl p)
    (r : Fin p.T) (a : Fin p.K) (z : SourceInput p) (fresh : TimeControl p) :
    incomingAmplitude? rate rewards C_star C_h r a
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p r z fresh) =
      incomingAmplitude? rate rewards C_star C_h r a z := by
  unfold incomingAmplitude?
  rw [incomingPayload_replaceCurrent rate rewards C_star C_h control0]

theorem oldCell_reward (r : Fin p.T) (z : SourceInput p)
    (c : RecordedQueueRun.RoundInput p.K)
    (hc : oldCell? rate rewards C_star C_h r z = some c) :
    c.reward = roundedReward rewards r := by
  obtain ⟨record, hr, hread⟩ := Option.bind_eq_some_iff.mp hc
  obtain ⟨_payload, _ledger, _started, _weights, _out, _hcall, _hdiag, _hrun,
    _henabled, _hclock, _hrate, hreward, _hrecording, _hgate, _harrival⟩ :=
    ReferenceLaterCollectionArrivalReadout.laterCollectionReadout_call 0 record c hread
  have hf := ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields
    rate rewards C_star C_h r z record hr
  rw [hreward, hf.2.2.1, hf.2.2.2]
  rfl

/-- Exact factorization of the nominal physical raw arrival. A recorded arm
with floor zero remains a recorded arm in this identity. -/
theorem oldRaw_eq_test_mul_amplitude (r : Fin p.T) (a : Fin p.K) (z : SourceInput p)
    (hz : z ∈ oldSelector rate rewards C_star C_h r) :
    oldRaw rate rewards C_star C_h r a z =
      (if oldMarker? rate rewards C_star C_h r z = some (some a) then 1 else 0) *
        (incomingAmplitude? rate rewards C_star C_h r a z).getD 0 := by
  obtain ⟨payload, c, hp, hc, hrate, _hm⟩ :=
    oldCell_recordingMap rate rewards C_star C_h r z hz
  have hreward := oldCell_reward rate rewards C_star C_h r z c hc
  by_cases ha : c.recordedArm = some a
  · simp only [oldRaw, hc]
    rw [RecordedRoundMoments.normalizedQuantizedArrival_eq_quantizedValue_of_recorded
      _ c a ha]
    simp only [oldMarker?, hc, Option.map_some, ha, ↓reduceIte,
      incomingAmplitude?, hp, Option.getD_some, one_mul, hrate, hreward]
    rfl
  · simp only [oldRaw, hc, RecordedRoundMoments.normalizedQuantizedArrival,
      RecordedQueueRun.quantizedArrival, ha, ite_false, Nat.cast_zero, zero_div]
    simp only [oldMarker?, hc, Option.map_some, Option.some.injEq, ha, ite_false, zero_mul]

/-- The floor amplitude is bounded on the actual OLD selector using the
actual original payload rate; no constant-rate assumption is supplied. -/
theorem incomingAmplitude_bounds_on_oldSelector (r : Fin p.T) (a : Fin p.K)
    (z : SourceInput p) (hz : z ∈ oldSelector rate rewards C_star C_h r) :
    0 ≤ (incomingAmplitude? rate rewards C_star C_h r a z).getD 0 ∧
      (incomingAmplitude? rate rewards C_star C_h r a z).getD 0 ≤
        1 / CanonicalRecordingRates.beta p rate.eta.val := by
  obtain ⟨payload, _c, hp, _hc, _hrate, _hm⟩ :=
    oldCell_recordingMap rate rewards C_star C_h r z hz
  simp only [incomingAmplitude?, hp, Option.map_some, Option.getD_some]
  have hbeta := CanonicalRecordingRates.beta_pos p rate.eta.property
  have hxi := hbeta.trans_le (AssignmentStartPayload.Input.beta_le_rate payload a)
  exact ⟨QuantizedRecordingMoments.quantizedValue_nonneg _ _ _ _ rate.eta.property,
    QuantizedRecordingMoments.quantizedValue_le_inv_of_beta_le _ _ _ _ _
      (D_pos p) rate.eta.property hxi (roundedReward_bounds rewards r a) hbeta
      (AssignmentStartPayload.Input.beta_le_rate payload a)⟩

/-- The local first-moment coefficient has the literal quantized expression
and is at most the original rounded reward, hence at most one. This is an
arithmetic coefficient bound, not yet a conditional recording-law assertion. -/
theorem oldCell_firstMean_le_reward (r : Fin p.T) (a : Fin p.K) (z : SourceInput p)
    (hz : z ∈ oldSelector rate rewards C_star C_h r) :
    ∃ payload : Payload rate,
      incomingPayload? rate rewards C_star C_h r z = some payload ∧
      0 ≤ payload.rate a * (incomingAmplitude? rate rewards C_star C_h r a z).getD 0 ∧
      payload.rate a * (incomingAmplitude? rate rewards C_star C_h r a z).getD 0 ≤
        roundedReward rewards r a ∧
      roundedReward rewards r a ≤ 1 := by
  obtain ⟨payload, _c, hp, _hc, _hrate, _hm⟩ :=
    oldCell_recordingMap rate rewards C_star C_h r z hz
  have hxi : 0 < payload.rate a :=
    (CanonicalRecordingRates.beta_pos p rate.eta.property).trans_le
      (AssignmentStartPayload.Input.beta_le_rate payload a)
  refine ⟨payload, hp, ?_, ?_, (roundedReward_bounds rewards r a).2⟩
  · exact mul_nonneg hxi.le
      (incomingAmplitude_bounds_on_oldSelector rate rewards C_star C_h r a z hz).1
  · simp only [incomingAmplitude?, hp, Option.map_some, Option.getD_some]
    exact QuantizedRecordingMoments.quantizedValue_firstMoment_le _ _ _ _
      (D_pos p) rate.eta.property hxi (roundedReward_bounds rewards r a)

/-- Every actual optional OLD raw value has the inverse-beta envelope,
including cells outside the pre-call selector and absent cells. -/
theorem oldRaw_bounds (r : Fin p.T) (a : Fin p.K) (z : SourceInput p) :
    0 ≤ oldRaw rate rewards C_star C_h r a z ∧
      oldRaw rate rewards C_star C_h r a z ≤
        1 / CanonicalRecordingRates.beta p rate.eta.val := by
  have hbeta := CanonicalRecordingRates.beta_pos p rate.eta.property
  cases hc : oldCell? rate rewards C_star C_h r z with
  | none =>
      simp only [oldRaw, hc]
      exact ⟨le_rfl, div_nonneg zero_le_one hbeta.le⟩
  | some c =>
      obtain ⟨record, _hr, hread⟩ := Option.bind_eq_some_iff.mp hc
      obtain ⟨payload, _hp, hrate, _hm⟩ := readout_payload_snapshot rate record c hread
      have hbetaxi : CanonicalRecordingRates.beta p rate.eta.val ≤ c.rate a := by
        rw [hrate]
        exact AssignmentStartPayload.Input.beta_le_rate payload a
      simp only [oldRaw, hc]
      by_cases ha : c.recordedArm = some a
      · rw [RecordedRoundMoments.normalizedQuantizedArrival_eq_quantizedValue_of_recorded
          _ c a ha]
        exact ⟨QuantizedRecordingMoments.quantizedValue_nonneg _ _ _ _ rate.eta.property,
          QuantizedRecordingMoments.quantizedValue_le_inv_of_beta_le _ _ _ _ _
            (D_pos p) rate.eta.property (hbeta.trans_le hbetaxi)
            ⟨c.reward_nonneg a, c.reward_le_one a⟩ hbeta hbetaxi⟩
      · simp only [RecordedRoundMoments.normalizedQuantizedArrival,
          RecordedQueueRun.quantizedArrival, ha, ite_false, Nat.cast_zero, zero_div]
        exact ⟨le_rfl, div_nonneg zero_le_one hbeta.le⟩

/-- Disabled present OLD cells record bottom and have zero nominal raw
arrivals on every arm. Outer absence is not used for this conclusion. -/
theorem oldCell_disabled (r : Fin p.T) (z : SourceInput p)
    (hz : z ∈ oldSelector rate rewards C_star C_h r)
    (c : RecordedQueueRun.RoundInput p.K)
    (hc : oldCell? rate rewards C_star C_h r z = some c) (he : c.enabled = false) :
    oldMarker? rate rewards C_star C_h r z = some none ∧
      ∀ a, oldRaw rate rewards C_star C_h r a z = 0 := by
  obtain ⟨payload, c', _hp, hc', _hrate, hm⟩ :=
    oldCell_recordingMap rate rewards C_star C_h r z hz
  have hcc : c' = c := Option.some.inj (hc'.symm.trans hc)
  subst c'
  rw [he] at hm
  have hbottom : oldMarker? rate rewards C_star C_h r z = some none := by
    simpa only [SnapshotRecordingKernel.recordingMap, Bool.false_eq_true,
      ↓reduceDIte] using hm
  refine ⟨hbottom, ?_⟩
  intro a
  have hnone : c.recordedArm = none := by
    simpa only [oldMarker?, hc, Option.map_some, Option.some.injEq] using hbottom
  simp only [oldRaw, hc, RecordedRoundMoments.normalizedQuantizedArrival,
    RecordedQueueRun.quantizedArrival, hnone, reduceCtorEq, ite_false,
    Nat.cast_zero, zero_div]

/-- Whole numerical coordinates of the same optional OLD cell. -/
def oldCoordinates? (r : Fin p.T) (z : SourceInput p) :=
  (oldCell? rate rewards C_star C_h r z).map
    ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates

private theorem measurable_of_countable_fibers {X A B : Type*}
    [MeasurableSpace X] [MeasurableSpace A] [MeasurableSpace B]
    [Countable A] [MeasurableSingletonClass A]
    (code : X → A) (hc : Measurable code) (f : X → B)
    (hf : ∀ a, Measurable (fun x : {x // code x = a} => f x.val)) :
    Measurable f := by
  intro s hs
  have heq : f ⁻¹' s = ⋃ a, Subtype.val ''
      ((fun x : {x // code x = a} => f x.val) ⁻¹' s) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_image]
    constructor
    · intro hx
      exact ⟨code x, ⟨x, rfl⟩, hx, rfl⟩
    · rintro ⟨_, y, hy, rfl⟩
      exact hy
  rw [heq]
  exact MeasurableSet.iUnion fun a => MeasurableSet.subtype_image
    ((measurableSet_singleton a).preimage hc) (hf a hs)

/-- Ambient Borelness of the OLD observation includes the first cutoff head,
using the accepted indexed readout with older-start argument literally zero.
-/
theorem oldCoordinates_measurable (r : Fin p.T) :
    Measurable (oldCoordinates? rate rewards C_star C_h r) := by
  apply measurable_of_countable_fibers
    (ReferenceCompletePhysicalHistory.physicalStart rate · rewards C_star C_h)
    (ReferenceCompleteSuffixInputMeasurability.measurable_physicalStart
      rate rewards C_star C_h)
  intro s
  by_cases hs : s ≤ r.val
  · let k := r.val - s
    let lift : {z : SourceInput p //
        ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h = s} →
        ReferenceCompleteSuffixInputMeasurability.IndexedSource rate rewards C_star C_h k :=
      fun z => ⟨z.val, by
        rw [ReferenceCompletePhysicalHistory.completeSuffixRecords_length, z.property]
        have hr := r.isLt
        dsimp only [k]
        omega⟩
    have hlift : Measurable lift := measurable_subtype_coe.subtype_mk
    have hm := (ReferenceLaterCollectionSourceReadoutMeasurability.measurable_actualReadout_numerical
      rate rewards C_star C_h k).comp ((measurable_const (a := (0 : ℕ))).prodMk hlift)
    convert hm using 1
    funext z
    have hstart : ReferenceCompletePhysicalHistory.physicalStart
        rate z.val rewards C_star C_h ≤ r.val := by rw [z.property]; exact hs
    have hindex : r.val - ReferenceCompletePhysicalHistory.physicalStart
        rate z.val rewards C_star C_h = k := by rw [z.property]
    simp only [oldCoordinates?, oldCell?, actualRecord, ite_eq_left hstart, hindex]
    rw [List.getElem?_eq_getElem (lift z).property]
    rfl
  · have heq : (fun z : {z : SourceInput p //
        ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h = s} =>
        oldCoordinates? rate rewards C_star C_h r z.val) = fun _ => none := by
      funext z
      have hstart : ¬ ReferenceCompletePhysicalHistory.physicalStart
          rate z.val rewards C_star C_h ≤ r.val := by rw [z.property]; exact hs
      simp only [oldCoordinates?, oldCell?, actualRecord, ite_eq_right hstart,
        Option.bind_none, Option.map_none]
    rw [heq]
    exact measurable_const

theorem oldMarker_measurable (r : Fin p.T) :
    Measurable (oldMarker? rate rewards C_star C_h r) := by
  have hm := measurable_option_map _
    (oldCoordinates_measurable rate rewards C_star C_h r)
    (fun c : Bool × (Option (Fin p.K) × ((Fin p.K → ℝ) × (Fin p.K → ℝ))) => c.2.1)
    (measurable_fst.comp measurable_snd)
  convert hm using 1
  funext z
  unfold oldMarker? oldCoordinates?
  cases oldCell? rate rewards C_star C_h r z <;> rfl

private theorem measurable_option_isSome {A : Type*} [MeasurableSpace A] :
    Measurable (Option.isSome : Option A → Bool) := by
  have hs : Measurable (Sum.elim (fun _ : A => true) (fun _ : PUnit => false)) :=
    measurable_const.sumElim measurable_const
  convert hs.comp (comap_measurable (Equiv.optionEquivSumPUnit A)) using 1
  funext o
  cases o <;> rfl

/-- Ambient Borelness is separate from the still stronger pre-choice
measurability of this computed selector. -/
theorem oldSelector_measurable_ambient (control0 : TimeControl p) (r : Fin p.T) :
    MeasurableSet (oldSelector rate rewards C_star C_h r) := by
  have hbefore : MeasurableSet (beforeCall rate rewards C_star C_h r) :=
    (sourcePrefixFiltration control0).le' (r.val + 1) _
      (beforeCall_measurable rate rewards C_star C_h control0 r)
  have hm := measurable_option_isSome.comp
    (oldCoordinates_measurable rate rewards C_star C_h r)
  have heq : {z : SourceInput p |
      (oldCell? rate rewards C_star C_h r z).isSome = true} =
      {z | (oldCoordinates? rate rewards C_star C_h r z).isSome = true} := by
    ext z
    change (oldCell? rate rewards C_star C_h r z).isSome = true ↔
      (oldCoordinates? rate rewards C_star C_h r z).isSome = true
    unfold oldCoordinates?
    cases oldCell? rate rewards C_star C_h r z <;> rfl
  apply hbefore.inter
  rw [heq]
  exact (hm.eq_const true).setOf

/-- Nominal OLD arrivals are Borel under the original law. The proof projects
the accepted full numerical tuple and its literal floor arithmetic. -/
theorem oldRaw_measurable (r : Fin p.T) (a : Fin p.K) :
    Measurable (oldRaw rate rewards C_star C_h r a) := by
  have hm := measurable_option_map _
    (oldCoordinates_measurable rate rewards C_star C_h r) _
    (ReferenceLaterCollectionSourceReadoutMeasurability.measurable_arrivalsFromNumerical rate)
  have hf : Measurable (fun o : Option (Bool × (Fin p.K → ℕ)) =>
      match o with
      | none => (0 : ℝ)
      | some c => (c.2 a : ℝ) /
          ((ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ)) :=
    by
      have hsome : Measurable (fun c : Bool × (Fin p.K → ℕ) => (c.2 a : ℝ) /
          ((ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ)) :=
        measurable_of_countable _
      have hsum : Measurable (Sum.elim
          (fun c : Bool × (Fin p.K → ℕ) => (c.2 a : ℝ) /
            ((ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ))
          (fun _ : PUnit => (0 : ℝ))) := hsome.sumElim measurable_const
      convert hsum.comp
        (comap_measurable (Equiv.optionEquivSumPUnit (Bool × (Fin p.K → ℕ)))) using 1
      funext o
      dsimp only [Function.comp_apply]
      cases o <;> rfl
  convert hf.comp hm using 1
  funext z
  dsimp only [Function.comp_apply]
  unfold oldRaw oldCoordinates?
  cases oldCell? rate rewards C_star C_h r z <;> rfl

/-- Integrability is produced from the actual raw range on the original
probability space, without a moment or regularity hypothesis. -/
theorem oldRaw_integrable (r : Fin p.T) (a : Fin p.K) :
    Integrable (oldRaw rate rewards C_star C_h r a) (sourceInputLaw p) := by
  have hconst : Integrable (fun _ : SourceInput p =>
      1 / CanonicalRecordingRates.beta p rate.eta.val) (sourceInputLaw p) :=
    integrable_const _
  refine hconst.mono' (oldRaw_measurable rate rewards C_star C_h r a).aestronglyMeasurable ?_
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_of_nonneg (oldRaw_bounds rate rewards C_star C_h r a z).1]
  exact (oldRaw_bounds rate rewards C_star C_h r a z).2

theorem oldMarker_absent_iff (r : Fin p.T) (z : SourceInput p) :
    oldMarker? rate rewards C_star C_h r z = none ↔
      oldCell? rate rewards C_star C_h r z = none := by
  cases hc : oldCell? rate rewards C_star C_h r z <;> simp only [oldMarker?, hc,
    Option.map_none, Option.map_some, reduceCtorEq]

private theorem prepare_inputDomain
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (activation : ReferencePrelaunchFollower.Activation p) (t : Fin p.T)
    (active : activation.val ≤ t.val + 1)
    (input : DeclaredFollowerLocalRound.LocalConfiguration p rate)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hprep : (DeclaredFollowerLocalRound.prepare rate i row activation t active input).configuration =
      .ordinary state memory) : ActiveFollowerQueueOperation.stateInputDomain state := by
  obtain ⟨before, beforeMemory, hi, hstart, _hr, _hu⟩ :=
    ReferenceFollowerReplyChronology.prepare_ordinary_inversion
      i row activation t active input state memory hprep
  by_contra hd
  have hoff : ActiveFollowerQueueOperation.checkedUpOffer
      rate.eta i row activation t state = .failure := by
    simp only [ActiveFollowerQueueOperation.checkedUpOffer, dite_eq_right hd]
  rw [hi] at hprep
  simp only [DeclaredFollowerLocalRound.prepare, hstart, hoff] at hprep
  cases hprep

/-- Actual ordinary preparation supplies the checked UP encoding domain.
When no DOWN has been accepted, the zero reply is derived from the genuine
launch seed and the original run's acceptance chronology. -/
theorem actualPrepared_upAdmissible (r : Fin p.T) (z : SourceInput p)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : actualRecord rate rewards C_star C_h r z = some record)
    (i : Fin (p.m - 1)) (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hprep : (record.output.preparation.followers.followers i).configuration =
      .ordinary state memory) :
    OrdinaryMessageCodec.upAdmissible (ReferencePrelaunchFollower.codecParams p rate.eta)
      (ActiveFollowerQueueOperation.upOfferFields state) := by
  have hp : record.output.preparation.followers.followers i =
      DeclaredFollowerLocalRound.prepare rate i record.input.row
        (record.input.state.activations i) record.input.time (record.input.active i)
        (record.input.state.followers i) := record.output.preparation.followers.followers_eq i
  have hdomain := prepare_inputDomain rate i record.input.row
    (record.input.state.activations i) record.input.time (record.input.active i)
    (record.input.state.followers i) state memory (hp ▸ hprep)
  cases hdown : state.lastDown with
  | some down =>
      have hsigma := down.property
      unfold OrdinaryMessageCodec.downAdmissible at hsigma
      exact Or.inr ⟨by simpa [ActiveFollowerQueueOperation.upOfferFields,
        ReferencePrelaunchFollower.acceptedStart, hdown] using hsigma.1,
        by simpa [ActiveFollowerQueueOperation.upOfferFields,
          ReferencePrelaunchFollower.acceptedStart, hdown] using hsigma.2.1,
        hdomain.1, hdomain.2.1, hdomain.2.2.1⟩
  | none =>
      have hrecord := hr
      unfold actualRecord at hrecord
      split_ifs at hrecord with hstart
      · obtain ⟨hn, hget⟩ := List.getElem?_eq_some_iff.mp hrecord
        let k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate z rewards C_star C_h).length :=
          ⟨r.val - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h, hn⟩
        obtain ⟨hc, _hspan, _hprefix⟩ :=
          ReferenceLaterLiveNumericalReadout.source_record_prefix rate rewards C_star C_h z k
        let initial := ReferenceFirstLaunchNumericalCell.launchState
          rate z rewards C_star C_h hc
        let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
          rate z rewards C_star C_h hc
        have hrecords := ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
          rate z rewards C_star C_h initial
          (ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
            rate z rewards C_star C_h hc)
        let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
        have hspan : s + (p.T - s) ≤ p.T := by
          have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T
            rate z rewards C_star C_h
          dsimp only [s]
          omega
        have hget' : (ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate z rewards C_star C_h)[k.val]? = some record := by
          rw [List.getElem?_eq_getElem k.isLt]
          exact congrArg some hget
        have hrunGet : (ReferenceActivePhysicalHorizon.run initial z.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s (p.T - s)
            hspan seed.activeAtStart).records[k.val]? = some record := by
          rw [← hrecords]
          exact hget'
        have hidx := (List.getElem?_eq_some_iff.mp hrunGet).1
        have hrun : (ReferenceActivePhysicalHorizon.run initial z.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s (p.T - s)
            hspan seed.activeAtStart).records[k.val] = record :=
          (List.getElem?_eq_some_iff.mp hrunGet).2
        have hchoice : (ReferenceFollowerFixedReply.actualChoice
            (ReferenceActivePhysicalHorizon.run initial z.1.2
              (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s (p.T - s)
              hspan seed.activeAtStart).records[k.val] i).configuration =
            .ordinary state memory := by rw [hrun]; exact hprep
        have hchron := ReferenceFollowerReplyChronology.run_initial_to_choice
          initial z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards
          s (p.T - s) hspan seed.activeAtStart i ⟨k.val, hidx⟩
          (seed.followers i) state (seed.memory i) memory (seed.configuration i) hchoice
        have hzero : ReferencePrelaunchFollower.acceptedStart state = 0 := by
          simp only [ReferencePrelaunchFollower.acceptedStart, hdown]
        have hreply := (hchron.2.1 (seed.unoccupied i)
          ((seed.acceptedStart_zero i).trans hzero.symm)).2
        have hS := congrArg (fun x => x.2.1) hreply
        have hd := congrArg (fun x => x.2.2.1) hreply
        have hb := congrArg (fun x => x.2.2.2) hreply
        apply Or.inl
        simp only [ActiveFollowerQueueOperation.upOfferFields,
          ReferencePrelaunchFollower.acceptedStart, hdown, OrdinaryMessageCodec.upPlaceholder]
        congr 1
        · exact hS.trans (seed.S_zero i)
        · exact hd.trans (seed.delta_zero i)
        · exact hb.trans (seed.backlog_zero i)

private theorem prepare_unoccupied_otherRow
    (i : Fin (p.m - 1)) (row row' : CompletePublicTable.CompleteRow p)
    (activation : ReferencePrelaunchFollower.Activation p) (t : Fin p.T)
    (active : activation.val ≤ t.val + 1)
    (input : DeclaredFollowerLocalRound.LocalConfiguration p rate)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hprep : (DeclaredFollowerLocalRound.prepare rate i row activation t active input).configuration =
      .ordinary state memory)
    (hu : state.status = .unoccupied)
    (hadm : OrdinaryMessageCodec.upAdmissible
      (ReferencePrelaunchFollower.codecParams p rate.eta)
      (ActiveFollowerQueueOperation.upOfferFields state)) :
    (DeclaredFollowerLocalRound.prepare rate i row' activation t active input).configuration =
      .ordinary state memory := by
  obtain ⟨before, beforeMemory, hi, hstart, _hr, _hu⟩ :=
    ReferenceFollowerReplyChronology.prepare_ordinary_inversion
      i row activation t active input state memory hprep
  have hd := prepare_inputDomain rate i row activation t active input state memory hprep
  let offered : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta) :=
    ⟨ActiveFollowerQueueOperation.upOfferFields state, hadm⟩
  by_cases hs : ActiveFollowerQueueOperation.selectedUpRound i row' activation t
  · have hoff : ActiveFollowerQueueOperation.checkedUpOffer rate.eta i row' activation t state =
        .offer offered := by
      have hselected : ActiveFollowerQueueOperation.selectedUpRound i row' activation t ∧
          state.status = .unoccupied := ⟨hs, hu⟩
      simp only [ActiveFollowerQueueOperation.checkedUpOffer, dite_eq_left hd,
        dite_eq_left hselected, dite_eq_left hadm]
      rfl
    have hvalid : ActiveFollowerArmChoice.upStateDomain state ∧
        ActiveFollowerArmChoice.offeredUpMatchesState state offered :=
      ⟨⟨hd.1, hd.2.1, hd.2.2.1⟩, rfl, rfl, rfl, rfl⟩
    have hchoice := ActiveFollowerArmChoice.followerArmChoiceCore_unoccupied_selected_up
      state (row'.2 t) i offered hu hs.2.1 hs.2.2 hvalid
    rw [← ActiveFollowerArmChoice.followerArmChoice_eq_core] at hchoice
    rw [hi]
    simp only [DeclaredFollowerLocalRound.prepare, hstart, hoff, hchoice]
  · have hoff := ActiveFollowerQueueOperation.checkedUpOffer_noOffer rate.eta i row'
      activation t state hd (fun h => hs h.1)
    by_cases hdata : PublicDiscreteDraws.slotDraw (row'.2 t).1 = PublicDiscreteDraws.dataSlot
    · have hchoice := ActiveFollowerArmChoice.followerArmChoiceCore_unoccupied_data
        state (row'.2 t) i none hu hdata
      rw [← ActiveFollowerArmChoice.followerArmChoice_eq_core] at hchoice
      rw [hi]
      simp only [DeclaredFollowerLocalRound.prepare, hstart, hoff, hchoice]
    · have hnot : ¬ (PublicDiscreteDraws.slotDraw (row'.2 t).1 = PublicDiscreteDraws.upSlot ∧
          PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K (row'.2 t).1 = i) :=
        fun h => hs ⟨active, h⟩
      have hchoice := ActiveFollowerArmChoice.followerArmChoiceCore_unoccupied_other
        state (row'.2 t) i none hu hdata hnot
      rw [← ActiveFollowerArmChoice.followerArmChoice_eq_core] at hchoice
      rw [hi]
      simp only [DeclaredFollowerLocalRound.prepare, hstart, hoff, hchoice]

private theorem preparation_otherInput
    (x y : ReferenceActivePhysicalStep.RoundInput p rate)
    (hstate : x.state = y.state) (htime : x.time = y.time)
    (i : Fin (p.m - 1)) (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hp : ((ReferenceActivePhysicalStep.prepare x).followers.followers i).configuration =
      .ordinary state memory) (hu : state.status = .unoccupied)
    (hadm : OrdinaryMessageCodec.upAdmissible
      (ReferencePrelaunchFollower.codecParams p rate.eta)
      (ActiveFollowerQueueOperation.upOfferFields state)) :
    ((ReferenceActivePhysicalStep.prepare y).followers.followers i).configuration =
      .ordinary state memory := by
  cases x with
  | mk store rows selected time active wholeRewards =>
    cases y with
    | mk store' rows' selected' time' active' wholeRewards' =>
      dsimp only at hstate htime
      subst store'
      subst time'
      exact prepare_unoccupied_otherRow rate i (rows selected) (rows' selected')
        (store.activations i) time (active i) (store.followers i) state memory hp hu hadm

/-- Genuine actual-source follower-snapshot stability. The same original
launch chronology produces UP admissibility, including the zero placeholder;
it is not a hypothesis. Every fresh whole control has the same ordinary,
unoccupied prepared follower configurations on this local OLD selector. -/
theorem oldSelector_followers_replaceCurrent (control0 : TimeControl p)
    (r : Fin p.T) (z : SourceInput p)
    (hz : z ∈ oldSelector rate rewards C_star C_h r) (fresh : TimeControl p) :
    ∃ (record replacement :
      ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)),
      actualRecord rate rewards C_star C_h r z = some record ∧
      actualRecord rate rewards C_star C_h r
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p r z fresh) =
          some replacement ∧
      record.input.state = replacement.input.state ∧
      ∀ i, (replacement.output.preparation.followers.followers i).configuration =
        (record.output.preparation.followers.followers i).configuration := by
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hz.2
  obtain ⟨record, hr, hread⟩ := Option.bind_eq_some_iff.mp hc
  have hsome : (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 record).isSome =
      true := by rw [hread]; rfl
  have hf := (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout_domain
    0 record).mp hsome
  have hin : incoming rate rewards C_star C_h r
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p r z fresh) =
      incoming rate rewards C_star C_h r z := by
    rw [ReferenceSourcePrefixHistoryFiltration.incoming_factor
      rate rewards C_star C_h control0 r,
      sourcePrefix_replaceCurrent control0 r r.val le_rfl,
      ← ReferenceSourcePrefixHistoryFiltration.incoming_factor
        rate rewards C_star C_h control0 r]
  cases hr' : actualRecord rate rewards C_star C_h r
      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p r z fresh) with
  | none =>
      simp only [incoming, hr, hr', Option.map_none, Option.map_some] at hin
      cases hin
  | some replacement =>
      have hcode : ReferenceActivePhysicalStepMeasurability.encodeState replacement.input.state =
          ReferenceActivePhysicalStepMeasurability.encodeState record.input.state := by
        exact Option.some.inj (by
          simpa only [incoming, hr, hr', Option.map_some] using hin)
      have hstate : record.input.state = replacement.input.state :=
        (ReferenceActivePhysicalStepMeasurability.encodeState_injective hcode).symm
      have hf₁ := ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields
        rate rewards C_star C_h r z record hr
      have hf₂ := ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields
        rate rewards C_star C_h r
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p r z fresh)
        replacement hr'
      have htime : record.input.time = replacement.input.time :=
        hf₁.2.2.1.trans hf₂.2.2.1.symm
      have hprep : record.output.preparation = ReferenceActivePhysicalStep.prepare record.input := by
        rw [record.output_eq]
        rfl
      have hprep' : replacement.output.preparation =
          ReferenceActivePhysicalStep.prepare replacement.input := by
        rw [replacement.output_eq]
        rfl
      refine ⟨record, replacement, hr, rfl, hstate, ?_⟩
      intro i
      obtain ⟨hconfiguration, hunoccupied⟩ :=
        ReferenceLaterCollectionArrivalReadout.actualFollowerParts_spec record hf.1 i
      have hadm := actualPrepared_upAdmissible rate rewards C_star C_h r z record hr i
        (ReferenceLaterCollectionArrivalReadout.actualFollowerParts record hf.1 i).1
        (ReferenceLaterCollectionArrivalReadout.actualFollowerParts record hf.1 i).2
        hconfiguration
      have hother := preparation_otherInput rate record.input replacement.input hstate htime i
        (ReferenceLaterCollectionArrivalReadout.actualFollowerParts record hf.1 i).1
        (ReferenceLaterCollectionArrivalReadout.actualFollowerParts record hf.1 i).2
        (hprep ▸ hconfiguration) hunoccupied hadm
      rw [hprep', hother, hconfiguration]

private theorem collection_continuing_otherRow
    (x : CoordinatorRoundDispatch.CollectionInput p)
    (core : CoordinatorRoundDispatch.CollectionCoreValid x)
    (snapshot : CoordinatorCollectionInteractive.PreparedSnapshot x)
    (hscores : CoordinatorRoundDispatch.collectionCurrentScoresCheck x = true)
    (row : CompletePublicTable.CompleteRow p) :
    ∃ (core' : CoordinatorRoundDispatch.CollectionCoreValid {x with row := row})
      (snapshot' : CoordinatorCollectionInteractive.PreparedSnapshot {x with row := row})
      (boundary : snapshot'.clockStarted.clock.g ≤ p.T + 1)
      (scores : CoordinatorRoundDispatch.collectionCurrentScoresCheck {x with row := row} = true),
      CoordinatorRoundDispatch.dispatchCollection {x with row := row} =
        .continuing core' snapshot' boundary scores ∧
      snapshot'.clockStarted = snapshot.clockStarted := by
  let y : CoordinatorRoundDispatch.CollectionInput p := {x with row := row}
  have hc : CoordinatorRoundDispatch.CollectionCoreValid y :=
    (ReferenceActiveDispatchTemporal.collectionCoreValid_row_iff x row).mp core
  have hp : y.ledger.pending.Nonempty := snapshot.inputsValid.pending_nonempty
  have hs : CoordinatorRoundDispatch.collectionCurrentScoresCheck y = true := hscores
  have hstart : CoordinatorPhaseClock.startRound p y.etaReal y.time y.clock y.ledger.pending =
      .ok snapshot.clockStarted := snapshot.clockStarted_eq
  let weights := CoordinatorCollectionInteractive.PreObservationInputs.weights
    y hc.ledger_valid hc.assignment_eq
  have hchoice : CoordinatorLocalArmChoice.ChoiceInputsValid y.payload
      (some (CoordinatorCollectionUpRoundStep.localCutoff y.cutoffIndex)) y.time weights :=
    snapshot.inputsValid.choice_valid
  have hcutoff : CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
      snapshot.clockStarted.clock.u =
        some (CoordinatorCollectionUpRoundStep.localCutoff y.cutoffIndex) := by
    rw [snapshot.clockStarted_frame.1, core.clock_cutoff_eq]
    rfl
  have hchoice' : CoordinatorLocalArmChoice.ChoiceInputsValid y.payload
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p snapshot.clockStarted.clock.u)
      y.time weights := by rw [hcutoff]; exact hchoice
  have hnonempty := CoordinatorLiveChoiceRecorderStep.coordinatorArmChoice_ne_none
    y.payload snapshot.clockStarted.pending
    (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p snapshot.clockStarted.clock.u)
    y.time weights y.row hchoice'
  change ∃ core' snapshot' boundary scores,
    CoordinatorRoundDispatch.dispatchCollection y =
      .continuing core' snapshot' boundary scores ∧
      snapshot'.clockStarted = snapshot.clockStarted
  unfold CoordinatorRoundDispatch.dispatchCollection
  split
  · rename_i failure hfailure
    have hbad := hstart.symm.trans hfailure
    cases hbad
  · rename_i started hclock
    have heq : started = snapshot.clockStarted := Except.ok.inj (hclock.symm.trans hstart)
    subst started
    simp only [dite_eq_left hc, dite_eq_left hp, dite_eq_left hs]
    split
    · split
      · rename_i hnone
        exact False.elim (hnonempty hnone)
      · rename_i arm hselected
        let snap : CoordinatorCollectionInteractive.PreparedSnapshot y := {
          inputsValid := { snapshot.inputsValid with }
          clockStarted := snapshot.clockStarted
          clockStarted_eq := hstart
          clockStarted_frame := snapshot.clockStarted_frame
          arm := arm
          armChoice_eq := by
            simpa only [hcutoff] using hselected }
        have hgrid := CoordinatorPhaseClock.clockRegistersValid_gridDomain
          p y.etaReal y.clock hc.clock_registers_valid
        simp only [CoordinatorPhaseClock.clockGridDomain, hc.clock_sigma_eq] at hgrid
        have hb : snap.clockStarted.clock.g ≤ p.T + 1 := by
          rw [snap.clockStarted_frame.1]
          exact hgrid.2
        exact ⟨hc, snap, hb, hs, rfl, rfl⟩
    · rename_i hbad
      exact False.elim (hbad hchoice)

/-- The incoming OLD learning bit, read only from the stored phase clock. -/
def enabledFromCoordinator? (r : Fin p.T) :
    ReferenceActivePhysicalStep.CoordinatorConfiguration p rate → Option Bool
  | .live registers _ _ => some (decide (r.val + 1 < registers.priorClock.g))
  | .collection _ ledger _ => some (ReferenceActivePhysicalStep.collectionEnabled ledger r)
  | _ => none

def enabledFromCode? (r : Fin p.T) :
    ReferenceActivePhysicalStepMeasurability.CoordinatorCode p rate → Option Bool
  | .inr (.inl (_, live)) => some (decide (r.val + 1 < live.clockBoundary))
  | .inr (.inr (.inl (_, ledger, _))) =>
      some (ReferenceActivePhysicalStep.collectionEnabled ledger r)
  | _ => none

theorem enabledFromCode_measurable (r : Fin p.T) :
    Measurable (enabledFromCode? rate r) := by
  have hl : Measurable (fun z : Payload rate ×
      ReferenceActivePhysicalStepMeasurability.LiveDiscrete p =>
      some (decide (r.val + 1 < z.2.clockBoundary))) :=
    (measurable_of_countable (fun d : ReferenceActivePhysicalStepMeasurability.LiveDiscrete p =>
      some (decide (r.val + 1 < d.clockBoundary)))).comp measurable_snd
  have hc : Measurable (fun z : Payload rate ×
      (ReferenceActivePhysicalStep.Ledger rate × Option (Fin p.T × Bool)) =>
      some (ReferenceActivePhysicalStep.collectionEnabled z.2.1 r)) :=
    (measurable_of_countable (fun ledger : ReferenceActivePhysicalStep.Ledger rate =>
      some (ReferenceActivePhysicalStep.collectionEnabled ledger r))).comp
        (measurable_fst.comp measurable_snd)
  exact measurable_const.sumElim (hl.sumElim (hc.sumElim measurable_const))

theorem enabledFromCode_encode (r : Fin p.T)
    (c : ReferenceActivePhysicalStep.CoordinatorConfiguration p rate) :
    enabledFromCode? rate r (ReferenceActivePhysicalStepMeasurability.encodeCoordinator c) =
      enabledFromCoordinator? rate r c := by cases c <;> rfl

/-- Literal optional incoming learning bit; absence remains separate from a
present disabled clock. Its equality with actual OLD cells is proved below. -/
def incomingEnabled? (r : Fin p.T) (z : SourceInput p) : Option Bool :=
  (actualRecord rate rewards C_star C_h r z).bind fun record =>
    enabledFromCoordinator? rate r record.input.state.coordinator

theorem incomingEnabled_eq_code (r : Fin p.T) (z : SourceInput p) :
    incomingEnabled? rate rewards C_star C_h r z =
      (incoming rate rewards C_star C_h r z).bind
        (fun code => enabledFromCode? rate r code.1) := by
  unfold incomingEnabled? incoming
  cases actualRecord rate rewards C_star C_h r z with
  | none => rfl
  | some record =>
      exact (enabledFromCode_encode rate r record.input.state.coordinator).symm

theorem incomingEnabled_measurable (control0 : TimeControl p) (r : Fin p.T) :
    Measurable[sourcePrefixFiltration control0 (r.val + 1)]
      (incomingEnabled? rate rewards C_star C_h r) := by
  let : MeasurableSpace (SourceInput p) := sourcePrefixFiltration control0 (r.val + 1)
  have hm := measurable_option_bind _
    (ReferenceSourcePrefixHistoryFiltration.incoming_measurable
      rate rewards C_star C_h control0 r) _
    ((enabledFromCode_measurable rate r).comp measurable_fst)
  convert hm using 1
  funext z
  exact incomingEnabled_eq_code rate rewards C_star C_h r z

theorem incomingEnabled_replaceCurrent (control0 : TimeControl p) (r : Fin p.T)
    (z : SourceInput p) (fresh : TimeControl p) :
    incomingEnabled? rate rewards C_star C_h r
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p r z fresh) =
      incomingEnabled? rate rewards C_star C_h r z := by
  rw [incomingEnabled_eq_code, incomingEnabled_eq_code,
    ReferenceSourcePrefixHistoryFiltration.incoming_factor
      rate rewards C_star C_h control0 r,
    sourcePrefix_replaceCurrent control0 r r.val le_rfl,
    ← ReferenceSourcePrefixHistoryFiltration.incoming_factor
      rate rewards C_star C_h control0 r]

private theorem dispatch_enabled (r : Fin p.T)
    (x : ReferenceActivePhysicalStep.RoundInput p rate) :
    match ReferenceActivePhysicalStep.dispatch x with
    | .live registers _ _ _ => enabledFromCoordinator? rate r x.state.coordinator =
        some (decide (r.val + 1 < registers.priorClock.g))
    | .collection _ ledger _ _ _ => enabledFromCoordinator? rate r x.state.coordinator =
        some (ReferenceActivePhysicalStep.collectionEnabled ledger r)
    | _ => True := by
  cases hs : x.state.coordinator with
  | first =>
      simp only [ReferenceActivePhysicalStep.dispatch, hs, CoordinatorRoundDispatch.dispatch]
      trivial
  | live registers owned base =>
      simp only [ReferenceActivePhysicalStep.dispatch, hs, CoordinatorRoundDispatch.dispatch]
      rfl
  | collection payload ledger saved =>
      simp only [ReferenceActivePhysicalStep.dispatch, hs]
      by_cases hcut : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
      · simp only [dite_eq_left hcut, CoordinatorRoundDispatch.dispatch]
        rfl
      · simp only [dite_eq_right hcut]
  | dagger => simp only [ReferenceActivePhysicalStep.dispatch, hs]

private theorem readout_enabled
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (c : RecordedQueueRun.RoundInput p.K)
    (hread : ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 record = some c) :
    enabledFromCoordinator? rate record.input.time record.input.state.coordinator =
      some c.enabled := by
  have hp : (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 record).isSome =
      true := by rw [hread]; rfl
  obtain ⟨hf, hb⟩ :=
    (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout_domain 0 record).mp hp
  have hframe := dispatch_enabled rate record.input.time record.input
  have hprep : record.output.preparation = ReferenceActivePhysicalStep.prepare record.input := by
    rw [record.output_eq]
    rfl
  have hcut : record.output.preparation.coordinator =
      ReferenceActivePhysicalStep.dispatch record.input := by rw [hprep]; rfl
  rw [← hcut] at hframe
  cases he : record.output.preparation.coordinator with
  | first outcome => simp only [he] at hb
  | invalidCollectionCutoff => simp only [he] at hb
  | dagger => simp only [he] at hb
  | collection payload ledger clock cutoff outcome =>
      cases outcome with
      | continuing core snapshot boundary scores =>
          have hc : ReferenceLaterCollectionArrivalReadout.continuingCollectionInput
              record payload ledger clock cutoff snapshot = c := by
            simpa only [ReferenceLaterCollectionArrivalReadout.laterCollectionReadout,
              dite_eq_left hf, he, Option.some.injEq] using hread
          have henabled := (ReferenceLaterCollectionArrivalReadout.continuingCollectionRecorderOutput
            record 0 payload ledger clock cutoff core snapshot boundary scores he hf).2
          have hnum : c.enabled = ReferenceActivePhysicalStep.collectionEnabled
              ledger record.input.time := by
            rw [← hc]
            simpa only [ReferenceLaterCollectionArrivalReadout.continuingCollectionInput,
              hprep] using henabled
          simpa only [he, hnum] using hframe
      | _ => simp only [he] at hb
  | live registers owned base outcome =>
      cases outcome with
      | cutoffChosen dispatched hstart ledger hinit hcand hdomain hclock hpending hnone selected =>
          dsimp only [ReferenceActivePhysicalStep.liveInput] at *
          have hpos : 0 < registers.payload.sigma.val := by simpa only [he] using hb
          have hc : ReferenceLaterCollectionArrivalReadout.laterCutoffCollectionInput
              record registers owned base dispatched selected = c := by
            simpa only [ReferenceLaterCollectionArrivalReadout.laterCollectionReadout,
              dite_eq_left hf, he, dite_eq_left hpos, Option.some.injEq] using hread
          have hboundary : dispatched.startResult.clock.g = registers.priorClock.g := by
            have h := congrArg CoordinatorPhaseClock.ClockRegisters.g hclock
            change dispatched.startResult.clock.g = registers.priorClock.g at h
            exact h
          have heq : c.enabled = decide (record.input.time.val + 1 < registers.priorClock.g) := by
            rw [← hc]
            simp [ReferenceLaterCollectionArrivalReadout.laterCutoffCollectionInput,
              CoordinatorRecordingOperation.isFrozen, CoordinatorRecorderComplementBridge.recorderInput,
              CoordinatorRecorderComplementBridge.recorderInputWithWeights,
              CoordinatorRecorderComplementBridge.sourceStart,
              ReferenceActivePhysicalStep.collectionRecordingInput,
              CoordinatorRecordingOperation.sourceCalendarRound, hboundary]
          simpa only [he, heq] using hframe
      | _ => simp only [he] at hb

/-- Actual OLD cells have exactly the incoming predictable enabled bit,
including the first cutoff-head constructor. -/
theorem oldCell_enabled_eq_incoming (r : Fin p.T) (z : SourceInput p)
    (c : RecordedQueueRun.RoundInput p.K)
    (hc : oldCell? rate rewards C_star C_h r z = some c) :
    incomingEnabled? rate rewards C_star C_h r z = some c.enabled := by
  obtain ⟨record, hr, hread⟩ := Option.bind_eq_some_iff.mp hc
  have he := readout_enabled rate record c hread
  have hf := ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields
    rate rewards C_star C_h r z record hr
  simpa only [incomingEnabled?, hr, Option.bind_some, hf.2.2.1] using he

private theorem measurable_option_getD_zero :
    Measurable (fun o : Option ℝ => o.getD 0) := by
  have hs : Measurable (Sum.elim (id : ℝ → ℝ) (fun _ : PUnit => (0 : ℝ))) :=
    measurable_id.sumElim measurable_const
  convert hs.comp (comap_measurable (Equiv.optionEquivSumPUnit ℝ)) using 1
  funext o
  dsimp only [Function.comp_apply]
  cases o <;> rfl

/-- The scalar floor amplitude, extended by zero only on absent incoming
payloads, is measurable in the original pre-choice source field. -/
theorem incomingAmplitudeValue_measurable (control0 : TimeControl p)
    (r : Fin p.T) (a : Fin p.K) :
    Measurable[sourcePrefixFiltration control0 (r.val + 1)]
      (fun z => (incomingAmplitude? rate rewards C_star C_h r a z).getD 0) :=
  measurable_option_getD_zero.comp
    (incomingAmplitude_measurable rate rewards C_star C_h control0 r a)

private theorem measurableSet_optionSome {A : Type*} [MeasurableSpace A]
    (s : Set A) (hs : MeasurableSet s) : MeasurableSet (some '' s : Set (Option A)) := by
  change MeasurableSet[(inferInstance : MeasurableSpace (A ⊕ PUnit)).comap
    (Equiv.optionEquivSumPUnit A)] (some '' s)
  rw [MeasurableSpace.measurableSet_comap]
  refine ⟨Sum.inl '' s, measurableSet_inl_image.mpr hs, ?_⟩
  ext value
  cases value <;> simp

/-- Pull out the actual predictable floor amplitude under the original
`mu/F_r`, with all integrability proved here. The unresolved OLD arm mass
remains inside its conditional expectation: this theorem does not assume or
assert selector predictability or the desired recording law. -/
theorem oldRaw_condExp_factor (control0 : TimeControl p) (r : Fin p.T) (a : Fin p.K) :
    (sourceInputLaw p)[
      (oldSelector rate rewards C_star C_h r).indicator
        (oldRaw rate rewards C_star C_h r a) |
      sourcePrefixFiltration control0 (r.val + 1)] =ᵐ[sourceInputLaw p]
      (fun z => (incomingAmplitude? rate rewards C_star C_h r a z).getD 0) *
        (sourceInputLaw p)[
          (oldSelector rate rewards C_star C_h r).indicator
            (fun z => if oldMarker? rate rewards C_star C_h r z = some (some a)
              then (1 : ℝ) else 0) | sourcePrefixFiltration control0 (r.val + 1)] := by
  let E := oldSelector rate rewards C_star C_h r
  let amp := fun z => (incomingAmplitude? rate rewards C_star C_h r a z).getD 0
  let test := fun z => if oldMarker? rate rewards C_star C_h r z = some (some a)
    then (1 : ℝ) else 0
  have hE : MeasurableSet E :=
    oldSelector_measurable_ambient rate rewards C_star C_h control0 r
  have hinner : MeasurableSet ({some a} : Set (Option (Fin p.K))) := by
    exact measurableSet_singleton (some a)
  have htarget : MeasurableSet ({some (some a)} : Set (Option (Option (Fin p.K)))) := by
    simpa only [Set.image_singleton] using measurableSet_optionSome {some a} hinner
  have htest : Measurable test :=
    Measurable.ite ((oldMarker_measurable rate rewards C_star C_h r) htarget)
      measurable_const measurable_const
  have htestI : Integrable (E.indicator test) (sourceInputLaw p) := by
    refine (integrable_const (1 : ℝ)).mono' (htest.indicator hE).aestronglyMeasurable ?_
    filter_upwards [] with z
    by_cases hz : z ∈ E <;>
      by_cases ha : oldMarker? rate rewards C_star C_h r z = some (some a) <;>
      simp [Set.indicator, hz, test, ha]
  have hprod : E.indicator (oldRaw rate rewards C_star C_h r a) =
      amp * E.indicator test := by
    funext z
    by_cases hz : z ∈ E
    · rw [Set.indicator_of_mem hz]
      change oldRaw rate rewards C_star C_h r a z = amp z * E.indicator test z
      rw [Set.indicator_of_mem hz,
        oldRaw_eq_test_mul_amplitude rate rewards C_star C_h r a z hz]
      exact mul_comm _ _
    · simp only [Pi.mul_apply, Set.indicator_of_notMem hz, mul_zero]
  have hprodI : Integrable (amp * E.indicator test) (sourceInputLaw p) :=
    ((oldRaw_integrable rate rewards C_star C_h r a).indicator hE).congr
      (Filter.Eventually.of_forall (fun z => congrFun hprod z))
  change (sourceInputLaw p)[E.indicator (oldRaw rate rewards C_star C_h r a) |
      sourcePrefixFiltration control0 (r.val + 1)] =ᵐ[sourceInputLaw p]
    amp * (sourceInputLaw p)[E.indicator test | sourcePrefixFiltration control0 (r.val + 1)]
  rw [hprod]
  exact condExp_mul_of_stronglyMeasurable_left
    (incomingAmplitudeValue_measurable rate rewards C_star C_h control0 r a).stronglyMeasurable
    hprodI htestI

/-- Literal finite cutoff-head tag of the existing checked dispatcher data. -/
def cutoffDataTag : ReferenceLiveDispatchOutputMeasurability.OutcomeData p → Bool
  | .cutoffChosen _ _ _ => true
  | _ => false

private theorem cutoffDataTag_continuingChoice (x : CoordinatorRoundDispatch.LiveInput p)
    (out : CoordinatorStartRoundCutoffDispatch.Output
      x.registers x.ownedRegisters x.followerBaseScore) :
    cutoffDataTag (ReferenceLiveDispatchOutputMeasurability.choiceData x out
      (.continuingChosen (ReferenceLiveDispatchOutputMeasurability.dispatchData out)
        out.startResult)) = false := by
  unfold ReferenceLiveDispatchOutputMeasurability.choiceData
  split_ifs <;> rfl

private theorem cutoffDataTag_cutoffChoice_otherRow (x : CoordinatorRoundDispatch.LiveInput p)
    (out : CoordinatorStartRoundCutoffDispatch.Output
      x.registers x.ownedRegisters x.followerBaseScore)
    (ledger : ReferenceLiveDispatchOutputMeasurability.LedgerData p)
    (row : CompletePublicTable.CompleteRow p) :
    cutoffDataTag (ReferenceLiveDispatchOutputMeasurability.choiceData {x with row := row} out
      (.cutoffChosen (ReferenceLiveDispatchOutputMeasurability.dispatchData out) ledger)) =
    cutoffDataTag (ReferenceLiveDispatchOutputMeasurability.choiceData x out
      (.cutoffChosen (ReferenceLiveDispatchOutputMeasurability.dispatchData out) ledger)) := by
  unfold ReferenceLiveDispatchOutputMeasurability.choiceData
  split_ifs <;> rfl

/-- The actual checked live dispatcher selects its cutoff-head branch
independently of the entire supplied row. The selected arm may vary. -/
theorem liveCutoffTag_otherRow (x : CoordinatorRoundDispatch.LiveInput p)
    (row : CompletePublicTable.CompleteRow p) :
    cutoffDataTag (ReferenceLiveDispatchOutputMeasurability.outcomeData
      (CoordinatorRoundDispatch.dispatchLive {x with row := row})) =
    cutoffDataTag (ReferenceLiveDispatchOutputMeasurability.outcomeData
      (CoordinatorRoundDispatch.dispatchLive x)) := by
  rw [ReferenceLiveDispatchOutputMeasurability.outcomeData_dispatchLive,
    ReferenceLiveDispatchOutputMeasurability.outcomeData_dispatchLive]
  unfold ReferenceLiveDispatchOutputMeasurability.dataFormula
  cases hd : CoordinatorStartRoundCutoffDispatch.dispatch x.registers
      x.ownedRegisters x.followerBaseScore with
  | error reason => rfl
  | ok out =>
      dsimp only
      cases hi : out.collectionInitialization with
      | invalid => rfl
      | rejected value => rfl
      | success value =>
          cases value with
          | some ledger =>
              dsimp only
              exact cutoffDataTag_cutoffChoice_otherRow x out
                (ReferenceLiveDispatchOutputMeasurability.ledgerData ledger) row
          | none =>
              dsimp only
              split_ifs <;> first
                | rfl
                | exact (cutoffDataTag_continuingChoice _ _).trans
                    (cutoffDataTag_continuingChoice _ _).symm

end Bandits.Support.ReferenceFirstCollectionOldRecorderFoundation
