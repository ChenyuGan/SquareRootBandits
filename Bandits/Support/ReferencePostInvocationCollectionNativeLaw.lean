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
# Native one-round law of the actual later COLLECTION cell

The physical OLD payload and the genuine incoming logical set remain separate.
The current whole control is replaced in the original source; auxiliary labels
zero and one supply proposal and same-update residual randomness respectively.

Sources: ZIP4 `06_interruptions.tex:391-426`,
`04_slow_fast_learner.tex:142-215,323-390`, and `08_main_theorem.tex:78-109`.
These are internal finite laws, not manuscript closure.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal Classical BigOperators
open Bandits.Support ConstructorDimensions
open ReferenceFixedTimeSourceControlCoupling
open ReferenceFirstLiveChronologicalPrefixFoundation
open ReferenceFirstLiveChronologicalPrefixMeasurability

namespace Bandits.Support.ReferencePostInvocationCollectionNativeLaw

variable {p : ConstructorDimensions.Parameters}
abbrev Auxiliary := ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray
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

local instance optionMeasurableSpace {X : Type*} [MeasurableSpace X] :
    MeasurableSpace (Option X) := LaterAssignmentStartMeasurability.optionMeasurableSpace

variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
  (control0 : Control p) (q : Fin p.T)

local notation "Q" => ReferenceFirstLaunchNumericalCell.queueParameters rate

/-- Literal finite output: absent cell, or effective marker/FAST/proposal/next
set. The physical source and numerical update remain in the joint readout. -/
abbrev Outcome (p : ConstructorDimensions.Parameters) : Type :=
  Unit ⊕ (Option (Fin p.K) × Fin p.K × Bool × SlowSet p)

instance outcomeFintype : Fintype (Outcome p) :=
  inferInstanceAs (Fintype (Unit ⊕ (Option (Fin p.K) × Fin p.K × Bool × SlowSet p)))


instance outcomeMeasurableSpace : MeasurableSpace (Outcome p) := ⊤
instance outcomeDiscrete : DiscreteMeasurableSpace (Outcome p) := ⟨fun _ => trivial⟩

def cellOutcome (e : LogicalCell p rate) : Outcome p :=
  Sum.inr (if e.before.overflow then none else e.numerical.2.1,
    e.fastArm, e.proposal, e.nextSlowSet)

theorem measurable_cellOutcome : Measurable (cellOutcome rate) := by
  let : MeasurableSpace (SlowSet p) := ⊤
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

open ReferenceContinuingLiveSlicePreparation ReferenceActivePhysicalStep
/-- The literal current physical record with only its whole control replaced. -/
def controlledRecord (r : Record rate) (c : Control p) : Record rate :=
  ⟨inputAtControl r.input c, ReferenceActivePhysicalStep.step (inputAtControl r.input c), rfl⟩

private theorem roundInput_eq {x y : ReferenceActivePhysicalStep.RoundInput p rate}
    (hs : x.state = y.state) (hr : x.rows = y.rows) (hj : x.selected = y.selected)
    (ht : x.time = y.time) (hw : x.rewards = y.rewards) : x = y := by
  cases x
  cases y
  cases hs
  cases hr
  cases hj
  cases ht
  cases hw
  rfl

include control0 in
/-- Whole-source current-control replacement produces this exact physical
record. Every other row, date and private coordinate remains in the source. -/
theorem actualRecord_replace_control
    (z : BootstrapPrivateRoundStreams.SourceInput p) (r : Record rate)
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h q z = some r) (c : Control p) :
    ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h q (replaceSourceControl p q z c) =
      some (controlledRecord rate r c) := by
  obtain ⟨r', hr', hs⟩ :=
    ReferenceFirstCorrectedCollectionCausalReadout.actualIncoming_replaceSourceControl
      rate rewards C_star C_h control0 q z r hr c
  have hf := ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields
    rate rewards C_star C_h q z r hr
  have hf' := ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields
    rate rewards C_star C_h q _ r' hr'
  have hx : r'.input = inputAtControl r.input c := by
    apply roundInput_eq rate
    · exact hs
    · simp only [inputAtControl, rowsAtControl, rowAtControl, RoundInput.row,
        hf.1, hf.2.1, hf.2.2.1, hf'.1, replaceSourceControl,
        sourceCoordinatorIndex_eq_selectedRowIndex]
    · exact hf'.2.1.trans hf.2.1.symm
    · exact hf'.2.2.1.trans hf.2.2.1.symm
    · exact hf'.2.2.2.trans hf.2.2.2.symm
  have he : r' = controlledRecord rate r c := by
    cases r' with
    | mk input output hout =>
      dsimp only at hx
      cases hout
      cases hx
      rfl
  exact he ▸ hr'


private theorem live_noncall_incoming
    (r : ReferenceFirstLiveChronologicalPrefixFoundation.Record rate)
    (hlive : ReferenceLaterLiveNumericalReadout.laterLiveDomain 0 r)
    (hnf : r.input.state.coordinator ≠ .first)
    (hnd : r.input.state.coordinator ≠ .dagger)
    (hparam : ReferenceLaterSamplerParameterMeasurability.parameters? r.input = none) :
    ∃ regs owned base, r.input.state.coordinator = .live regs owned base := by
  obtain ⟨selected, hsel, _hsigma, hactive, _ho⟩ := hlive
  cases hs : r.input.state.coordinator with
  | first => exact (hnf hs).elim
  | dagger => exact (hnd hs).elim
  | live regs owned base => exact ⟨regs, owned, base, rfl⟩
  | collection payload ledger saved =>
      by_cases hc : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
      · let u : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
        let clock := ReferenceActivePhysicalStep.collectionClock payload ledger saved u
        let x := ReferenceActivePhysicalStep.collectionInput r.input payload ledger clock u
        have hp : r.output.preparation.coordinator = .collection payload ledger clock u
            (CoordinatorRoundDispatch.dispatchCollection x) := by
          rw [r.output_eq]
          change ReferenceActivePhysicalStep.dispatch r.input = _
          simp only [ReferenceActivePhysicalStep.dispatch, hs, dite_eq_left hc,
            CoordinatorRoundDispatch.dispatch]
          rfl
        have hf := ReferenceCoordinatorRecorderCallCorrespondence.actual_call_frames r
        rw [hp] at hsel hf
        cases hd : CoordinatorRoundDispatch.dispatchCollection x <;> rw [hd] at hsel hf <;>
          try cases hsel
        · have he := Option.some.inj hsel
          exact (hf.1 (by simpa only [← he] using hactive)).elim
        · have hl : ReferenceCollectionPhaseHistory.laterChosen r.input = true := by
            unfold ReferenceCollectionPhaseHistory.laterChosen
            have hprep : (ReferenceActivePhysicalStep.prepare r.input).coordinator =
                r.output.preparation.coordinator := by rw [r.output_eq]; rfl
            rw [hprep, hp, hd]
          have hsome := ReferenceFirstCollectionRenewalRecordingFeedback.laterChosen_parameters_present
            r.input hl
          change (ReferenceLaterSamplerParameterMeasurability.parameters? r.input).isSome = true at hsome
          rw [hparam] at hsome
          cases hsome
      · have hp : r.output.preparation.coordinator = .invalidCollectionCutoff := by
          rw [r.output_eq]
          change ReferenceActivePhysicalStep.dispatch r.input = _
          simp only [ReferenceActivePhysicalStep.dispatch, hs, dite_eq_right hc]
        rw [hp] at hsel
        cases hsel

private theorem collection_parameters_absent
    (r : Record rate) (c : RecordedQueueRun.RoundInput p.K)
    (hc : ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 r = some c) :
    ReferenceLaterSamplerParameterMeasurability.parameters? r.input = none := by
  have hd := (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout_domain 0 r).mp
    (show (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 r).isSome = true by rw [hc]; rfl)
  have hp : ReferenceActivePhysicalStep.dispatch r.input = r.output.preparation.coordinator := by
    rw [r.output_eq]; rfl
  change ReferenceLaterAssignmentFibreStep.parameters? r.input = none
  rw [ReferenceLaterAssignmentFibreStep.parameters?_eq_physicalDispatch, hp]
  cases he : r.output.preparation.coordinator with
  | first outcome =>
    cases outcome <;> simp only [he] at hd <;> exact hd.2.elim
  | dagger => simp only [he] at hd; exact hd.2.elim
  | invalidCollectionCutoff => simp only [he] at hd; exact hd.2.elim
  | collection payload ledger clock cutoff outcome =>
    cases outcome <;> simp only [he] at hd
    all_goals first | exact hd.2.elim | rfl
  | live regs owned base outcome =>
    cases outcome <;> simp only [he] at hd
    all_goals first | exact hd.2.elim | rfl

include control0 in
/-- Collection membership is stable under replacement of the entire current
control, even after earlier invocations. Only the actual incoming state is used. -/
theorem collectionDateDomain_replace_control
    (z : ReferencePostInvocationNoncallGeometry.CollectionDateSource rate rewards C_star C_h q) (c : Control p) :
    replaceSourceControl p q z.val c ∈ ReferencePostInvocationNoncallGeometry.collectionDateDomain rate rewards C_star C_h q := by
  let r := ReferencePostInvocationNoncallGeometry.collectionRecord rate rewards C_star C_h q z
  have hr := (ReferencePostInvocationNoncallGeometry.collectionRecord_spec rate rewards C_star C_h q z).1
  have hc := ReferencePostInvocationPrefixLocality.collectionInput_spec rate rewards C_star C_h q z
  have hp := ReferencePostInvocationNoncallGeometry.collectionArguments_incoming rate rewards C_star C_h q z
  have hstored : ReferenceAssignmentPayloadPersistence.storedPayload r.input.state.coordinator =
      some (ReferencePostInvocationNoncallGeometry.collectionArguments rate rewards C_star C_h q z).1 := by
    simpa only [ReferenceFirstCollectionOldRecorderFoundation.incomingPayload?, hr,
      Option.bind_some] using hp
  have hnf : r.input.state.coordinator ≠ .first := by
    intro h; rw [h] at hstored; cases hstored
  have hnd : r.input.state.coordinator ≠ .dagger := by
    intro h; rw [h] at hstored; cases hstored
  let z' := replaceSourceControl p q z.val c
  let r' := controlledRecord rate r c
  have hr' : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h q z' = some r' :=
    actualRecord_replace_control rate rewards C_star C_h control0 q z.val r hr c
  have hin : ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h q z.val =
      ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h q z' := by
    simp only [ReferenceSourcePrefixHistoryFiltration.incoming, hr, hr', Option.map_some]
    rfl
  have hparam := collection_parameters_absent rate r _ hc
  have hparam' : ReferenceLaterSamplerParameterMeasurability.parameters? r'.input = none := by
    exact (ReferenceLaterSamplerParameterMeasurability.parameters?_eq_of_state_eq_time_eq
      r'.input r.input rfl rfl).trans hparam
  obtain ⟨k, hk⟩ : ∃ k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z' rewards C_star C_h).length,
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z' rewards C_star C_h)[k.val] = r' := by
    unfold ReferenceSourcePrefixHistoryFiltration.actualRecord at hr'
    split at hr'
    · exact ⟨⟨_, (List.getElem?_eq_some_iff.mp hr').1⟩, (List.getElem?_eq_some_iff.mp hr').2⟩
    · contradiction
  have hphases := (ReferenceCompleteOriginalCalendarCellPresence.complete_original_calendar_phase_exhaustion
    rate rewards C_star C_h z' k).2
  rw [hk] at hphases
  rcases hphases with hlive | ⟨d, hd⟩
  · have hlin := live_noncall_incoming rate r' hlive hnf hnd hparam'
    have hzlive : z' ∈ ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualDomain
        rate rewards C_star C_h q :=
      ⟨r', hr', hlin, (ReferenceLaterLiveNumericalReadout.laterLiveReadout_domain 0 r').mpr hlive⟩
    have hzlive0 := ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualDomain_of_incoming_eq
      rate rewards C_star C_h q z' z.val hin.symm hzlive
    obtain ⟨r0, hr0, _, hl⟩ := hzlive0
    have he : r0 = r := Option.some.inj (hr0.symm.trans hr)
    subst r0
    exact (ReferenceCompleteNumericalBranchObservation.readouts_disjoint rate 0 r
      ⟨hl, by rw [hc]; rfl⟩).elim
  · exact ReferencePostInvocationNoncallGeometry.collectionDateDomain_of_readout rate rewards C_star C_h q z' r' hr' d hd

/-- The literal whole-source family, with every other row/date/private array retained. -/
def replaceCollectionSource
    (z : ReferencePostInvocationNoncallGeometry.CollectionDateSource rate rewards C_star C_h q) (c : Control p) :
    ReferencePostInvocationNoncallGeometry.CollectionDateSource rate rewards C_star C_h q :=
  ⟨replaceSourceControl p q z.val c,
    collectionDateDomain_replace_control rate rewards C_star C_h control0 q z c⟩

theorem collectionRecord_replace_control
    (z : ReferencePostInvocationNoncallGeometry.CollectionDateSource rate rewards C_star C_h q) (c : Control p) :
    ReferencePostInvocationNoncallGeometry.collectionRecord rate rewards C_star C_h q
        (replaceCollectionSource rate rewards C_star C_h control0 q z c) =
      controlledRecord rate (ReferencePostInvocationNoncallGeometry.collectionRecord rate rewards C_star C_h q z) c := by
  apply Option.some.inj
  exact (ReferencePostInvocationNoncallGeometry.collectionRecord_spec rate rewards C_star C_h q _).1.symm.trans
    (actualRecord_replace_control rate rewards C_star C_h control0 q z.val _
      (ReferencePostInvocationNoncallGeometry.collectionRecord_spec rate rewards C_star C_h q z).1 c)

theorem collectionPayload_replace_control
    (z : ReferencePostInvocationNoncallGeometry.CollectionDateSource rate rewards C_star C_h q) (c : Control p) :
    (ReferencePostInvocationNoncallGeometry.collectionArguments rate rewards C_star C_h q
        (replaceCollectionSource rate rewards C_star C_h control0 q z c)).1 =
      (ReferencePostInvocationNoncallGeometry.collectionArguments rate rewards C_star C_h q z).1 := by
  apply Option.some.inj
  rw [← ReferencePostInvocationNoncallGeometry.collectionArguments_incoming, ← ReferencePostInvocationNoncallGeometry.collectionArguments_incoming]
  exact ReferenceFirstCollectionOldRecorderFoundation.incomingPayload_replaceCurrent
    rate rewards C_star C_h control0 q z.val c

theorem collectionBefore_replace_control
    (z : ReferencePostInvocationNoncallGeometry.CollectionDateSource rate rewards C_star C_h q) (c : Control p) :
    ReferencePostInvocationNoncallGeometry.collectionBefore rate rewards C_star C_h q
        (replaceCollectionSource rate rewards C_star C_h control0 q z c) =
      ReferencePostInvocationNoncallGeometry.collectionBefore rate rewards C_star C_h q z := by
  apply Option.some.inj
  rw [← ReferencePostInvocationPrefixLocality.collectionBefore_spec, ← ReferencePostInvocationPrefixLocality.collectionBefore_spec]
  change ReferencePostInvocationNoncallGeometry.prefixNumerical rate rewards C_star C_h q.castSucc
    (replaceSourceControl p q z.val c) = _
  rw [ReferencePostInvocationPrefixLocality.prefixNumerical_sourcePrefix rate rewards C_star C_h control0 q.castSucc q.val le_rfl,
    ReferenceFirstCollectionOldRecorderFoundation.sourcePrefix_replaceCurrent control0 q q.val le_rfl,
    ← ReferencePostInvocationPrefixLocality.prefixNumerical_sourcePrefix rate rewards C_star C_h control0 q.castSucc q.val le_rfl]

theorem collectionEnabled_replace_control
    (z : ReferencePostInvocationNoncallGeometry.CollectionDateSource rate rewards C_star C_h q) (c : Control p) :
    (ReferencePostInvocationNoncallGeometry.collectionInput rate rewards C_star C_h q
        (replaceCollectionSource rate rewards C_star C_h control0 q z c)).enabled =
      (ReferencePostInvocationNoncallGeometry.collectionInput rate rewards C_star C_h q z).enabled := by
  rw [(ReferencePostInvocationGeneratedAlignment.collectionInput_oldGrid rate rewards C_star C_h q _).2,
    collectionPayload_replace_control rate rewards C_star C_h control0 q z c,
    ← (ReferencePostInvocationGeneratedAlignment.collectionInput_oldGrid rate rewards C_star C_h q z).2]

/-- Every actual later COLLECTION recorder uses its retained OLD payload.
This applies after prior invocations and needs no global OLD-selector premise. -/
theorem laterCollectionInput_recordingMap
    (z : ReferencePostInvocationNoncallGeometry.CollectionDateSource rate rewards C_star C_h q) :
    let r := ReferencePostInvocationNoncallGeometry.collectionRecord rate rewards C_star C_h q z
    let c := ReferencePostInvocationNoncallGeometry.collectionInput rate rewards C_star C_h q z
    let P := (ReferencePostInvocationNoncallGeometry.collectionArguments rate rewards C_star C_h q z).1
    c.recordedArm = SnapshotRecordingKernel.recordingMap p .collection c.enabled
      rate.eta.val rate.eta.property rate.sourceCap P.anchor P.anchor P.anchor_pos P.anchor_pos
      (fun _ => le_rfl) (fun j => le_mul_of_one_le_left (P.anchor_pos j).le (by norm_num))
      (r.input.row.2 r.input.time).1 := by
  dsimp only
  have hc := ReferencePostInvocationPrefixLocality.collectionInput_spec rate rewards C_star C_h q z
  have ha := ReferencePostInvocationNoncallGeometry.collectionArguments_spec rate rewards C_star C_h q z
  generalize hr : ReferencePostInvocationNoncallGeometry.collectionRecord rate rewards C_star C_h q z = r at hc ha ⊢
  generalize hcin : ReferencePostInvocationNoncallGeometry.collectionInput rate rewards C_star C_h q z = c at hc ⊢
  generalize hargs : ReferencePostInvocationNoncallGeometry.collectionArguments rate rewards C_star C_h q z = args at ha ⊢
  have hd := (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout_domain 0 r).mp
    (show (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 r).isSome = true by rw [hc]; rfl)
  obtain ⟨hf, hb⟩ := hd
  cases he : r.output.preparation.coordinator with
  | first outcome => simp only [he] at hb
  | invalidCollectionCutoff => simp only [he] at hb
  | dagger => simp only [he] at hb
  | collection payload ledger clock cutoff outcome =>
    cases outcome <;> simp only [he] at hb
    case continuing core snapshot boundary scores =>
      simp only [ReferenceLaterCollectionArrivalReadout.laterCollectionReadout, dite_eq_left hf,
        he, Option.some.injEq] at hc
      simp only [ReferenceLaterCollectionArrivalReadout.laterCollectionCall, ite_eq_left hf,
        he, Option.some.injEq] at ha
      cases hc
      cases ha
      unfold ReferenceLaterCollectionArrivalReadout.continuingCollectionInput
      exact ReferenceFirstCollectionOldRecorderFoundation.collectionMap_independent_currentWeights rate _ _ _ _ _ _ _ _
  | live regs owned base outcome =>
    cases outcome <;> simp only [he] at hb
    case cutoffChosen dispatched hstart ledger hinit hledger hdomains hclock hpending hno arm =>
      have hpos : 0 < regs.payload.sigma.val := hb
      simp only [ReferenceLaterCollectionArrivalReadout.laterCollectionReadout, dite_eq_left hf,
        he, dite_eq_left hpos, Option.some.injEq] at hc
      simp only [ReferenceLaterCollectionArrivalReadout.laterCollectionCall, ite_eq_left hf,
        he, ite_eq_left hpos, Option.some.injEq] at ha
      cases hc
      cases ha
      unfold ReferenceLaterCollectionArrivalReadout.laterCutoffCollectionInput
      exact ReferenceFirstCollectionOldRecorderFoundation.collectionMap_independent_currentWeights rate _ _ _ _ _ _ _ _

/-- The physical recorder keeps the OLD anchor, independently of the evolving logical set. -/
def nativeRecorder (z : ReferencePostInvocationNoncallGeometry.CollectionDateSource rate rewards C_star C_h q)
    (c : Control p) : Option (Fin p.K) :=
  let P := (ReferencePostInvocationNoncallGeometry.collectionArguments rate rewards C_star C_h q z).1
  SnapshotRecordingKernel.recordingMap p .collection
    (ReferencePostInvocationNoncallGeometry.collectionInput rate rewards C_star C_h q z).enabled
    rate.eta.val rate.eta.property rate.sourceCap P.anchor P.anchor P.anchor_pos P.anchor_pos
    (fun _ => le_rfl) (fun j => le_mul_of_one_le_left (P.anchor_pos j).le (by norm_num)) c.1

theorem measurable_nativeRecorder
    (z : ReferencePostInvocationNoncallGeometry.CollectionDateSource rate rewards C_star C_h q) :
    Measurable (nativeRecorder rate rewards C_star C_h q z) :=
  (SnapshotRecordingKernel.measurable_recordingMap p .collection rate.eta.val rate.eta.property
    rate.sourceCap _ _ _ _ _ _ _).comp measurable_fst

/-- FAST-coordinate nonuse is an identity of the literal physical recorder,
proved before any independence or factorization claim. -/
theorem nativeRecorder_replaceFast
    (z : ReferencePostInvocationNoncallGeometry.CollectionDateSource rate rewards C_star C_h q)
    (c : Control p) (x : Scalar) :
    nativeRecorder rate rewards C_star C_h q z
      (ReferenceFirstCollectionFastErasure.replaceFastScalar c x) =
      nativeRecorder rate rewards C_star C_h q z c := by
  let y := ReferenceFirstCollectionFastErasure.replaceFastScalar c x
  have hslot : ContinuousControlSlice.coordinate ContinuousControlSlice.Label.slot y.1 =
      ContinuousControlSlice.coordinate ContinuousControlSlice.Label.slot c.1 := by
    simp [y, ReferenceFirstCollectionFastErasure.replaceFastScalar, ContinuousControlSlice.coordinate,
      ContinuousControlSlice.Label.slot, ContinuousControlSlice.Label.fast]
  have hrec : ContinuousControlSlice.coordinate ContinuousControlSlice.Label.rec y.1 =
      ContinuousControlSlice.coordinate ContinuousControlSlice.Label.rec c.1 := by
    simp [y, ReferenceFirstCollectionFastErasure.replaceFastScalar, ContinuousControlSlice.coordinate,
      ContinuousControlSlice.Label.rec, ContinuousControlSlice.Label.fast]
  have hthin : ContinuousControlSlice.coordinate ContinuousControlSlice.Label.thin y.1 =
      ContinuousControlSlice.coordinate ContinuousControlSlice.Label.thin c.1 := by
    simp [y, ReferenceFirstCollectionFastErasure.replaceFastScalar, ContinuousControlSlice.coordinate,
      ContinuousControlSlice.Label.thin, ContinuousControlSlice.Label.fast]
  have hpilot (i : Fin p.m) : PublicDiscreteDraws.pilotDraw (K_pos p) i y.1 =
      PublicDiscreteDraws.pilotDraw (K_pos p) i c.1 := by
    simp [y, ReferenceFirstCollectionFastErasure.replaceFastScalar, PublicDiscreteDraws.pilotDraw,
      ContinuousControlSlice.coordinate, ContinuousControlSlice.Label.pilot, ContinuousControlSlice.Label.fast]
  have hmask (i : Fin p.m) (j : Fin p.K) :
      CanonicalRecordingSlice.recordingMask (K_pos p) i j y.1 ↔
      CanonicalRecordingSlice.recordingMask (K_pos p) i j c.1 := by
    simp only [CanonicalRecordingSlice.recordingMask, hpilot]
  have hsome (j : Fin p.K) : nativeRecorder rate rewards C_star C_h q z y = some j ↔
      nativeRecorder rate rewards C_star C_h q z c = some j := by
    by_cases hen : (ReferencePostInvocationNoncallGeometry.collectionInput rate rewards C_star C_h q z).enabled = true
    · simp only [nativeRecorder, hen, SnapshotRecordingKernel.recordingMap_some_iff,
        hslot, hrec, hthin, SnapshotRecordingKernel.dataAction, hpilot, hmask]
    · have hf : (ReferencePostInvocationNoncallGeometry.collectionInput rate rewards C_star C_h q z).enabled = false :=
        Bool.eq_false_iff.mpr hen
      simp only [nativeRecorder, hf, SnapshotRecordingKernel.recordingMap_disabled]
  change nativeRecorder rate rewards C_star C_h q z y = _
  cases hy : nativeRecorder rate rewards C_star C_h q z y with
  | some j => exact ((hsome j).mp hy).symm
  | none =>
    cases hc : nativeRecorder rate rewards C_star C_h q z c with
    | none => rfl
    | some j => have h := (hsome j).mpr hc; rw [hy] at h; cases h

/-- Literal native categorical FAST distribution for any positive PRE weights. -/
def collectionFastPMF (anchor weight : Fin p.K → ℝ)
    (ha : ∀ j, 0 < anchor j) (hw : ∀ j, 0 < weight j) (U : SlowSet p) :
    PMF (CanonicalFastSampling.FastArm U) :=
  PMF.ofFintype (fun j => ENNReal.ofReal
    (ReferencePostInvocationNoncallGeometry.collectionFastMass rate anchor weight ha hw U j)) (by
      rw [← ENNReal.ofReal_sum_of_nonneg
        (fun j _ => ReferencePostInvocationNoncallGeometry.collectionFastMass_nonneg rate _ _ _ _ _ j),
        ReferencePostInvocationNoncallGeometry.collectionFastMass_sum, ENNReal.ofReal_one])

theorem collectionFastPMF_apply (anchor weight : Fin p.K → ℝ)
    (ha : ∀ j, 0 < anchor j) (hw : ∀ j, 0 < weight j) (U : SlowSet p)
    (j : CanonicalFastSampling.FastArm U) :
    collectionFastPMF rate anchor weight ha hw U j = ENNReal.ofReal
      (ReferencePostInvocationNoncallGeometry.collectionFastMass rate anchor weight ha hw U j) := rfl

theorem collectionFastDraw_map (anchor weight : Fin p.K → ℝ)
    (ha : ∀ j, 0 < anchor j) (hw : ∀ j, 0 < weight j) (U : SlowSet p) :
    ContinuousControlSlice.scalarLaw.map
      (ReferencePostInvocationNoncallGeometry.collectionFastDraw rate anchor weight ha hw U) =
      (collectionFastPMF rate anchor weight ha hw U).toMeasure := by
  let masses := fun k => ReferencePostInvocationNoncallGeometry.collectionFastMass rate anchor weight ha hw U
    (CanonicalFastSampling.fastArmOrderIso U k)
  have hsum : ∑ k, masses k = 1 := by
    dsimp only [masses]
    exact (Equiv.sum_comp (CanonicalFastSampling.fastArmOrderIso U).toEquiv _).trans
      (ReferencePostInvocationNoncallGeometry.collectionFastMass_sum rate _ _ _ _ _)
  have hm : Measurable (ReferencePostInvocationNoncallGeometry.collectionFastDraw rate anchor weight ha hw U) :=
    ReferencePostInvocationPrefixLocality.measurable_collectionFastDraw rate
      (fun _ => anchor) (fun _ => weight) measurable_const measurable_const (fun _ => ha) (fun _ => hw)
      U id measurable_id
  apply Measure.ext_of_singleton
  intro j
  rw [Measure.map_apply hm (measurableSet_singleton j), PMF.toMeasure_apply_singleton _ j
    (measurableSet_singleton j), collectionFastPMF_apply]
  have hfibre : ReferencePostInvocationNoncallGeometry.collectionFastDraw rate anchor weight ha hw U ⁻¹' {j} =
      ContinuousCategorical.sample (Nat.zero_lt_succ _) masses hsum ⁻¹'
        {(CanonicalFastSampling.fastArmOrderIso U).symm j} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff,
      ReferencePostInvocationNoncallGeometry.collectionFastDraw, ← OrderIso.eq_symm_apply]
    rfl
  rw [hfibre]
  change ContinuousCategorical.uniform (ContinuousCategorical.sample (Nat.zero_lt_succ _) masses hsum ⁻¹'
    {(CanonicalFastSampling.fastArmOrderIso U).symm j}) = _
  simpa only [masses, OrderIso.apply_symm_apply] using
    ContinuousCategorical.uniform_sample_singleton (Nat.zero_lt_succ _)
      (fun k => ReferencePostInvocationNoncallGeometry.collectionFastMass_nonneg rate _ _ _ _ _ _) hsum
      ((CanonicalFastSampling.fastArmOrderIso U).symm j)

/-- The existing recorder PMF at the retained OLD physical rates. -/
def recorderPMF
    (z : ReferencePostInvocationNoncallGeometry.CollectionDateSource rate rewards C_star C_h q) :
    PMF (Option (Fin p.K)) :=
  RecordedRoundMoments.recordingOutcomePMF
    (SnapshotRecordingKernel.recordingRates p rate.eta.val rate.eta.property rate.sourceCap
      (ReferencePostInvocationNoncallGeometry.collectionArguments rate rewards C_star C_h q z).1.anchor
      (ReferencePostInvocationNoncallGeometry.collectionArguments rate rewards C_star C_h q z).1.anchor_pos)

theorem nativeRecorder_map
    (z : ReferencePostInvocationNoncallGeometry.CollectionDateSource rate rewards C_star C_h q)
    (hen : (ReferencePostInvocationNoncallGeometry.collectionInput rate rewards C_star C_h q z).enabled = true) :
    (ContinuousLearningRows.timeControlLaw p).map (nativeRecorder rate rewards C_star C_h q z) =
      (recorderPMF rate rewards C_star C_h q z).toMeasure := by
  let P := (ReferencePostInvocationNoncallGeometry.collectionArguments rate rewards C_star C_h q z).1
  let f := SnapshotRecordingKernel.recordingMap p .collection true rate.eta.val rate.eta.property
    rate.sourceCap P.anchor P.anchor P.anchor_pos P.anchor_pos (fun _ => le_rfl)
    (fun j => le_mul_of_one_le_left (P.anchor_pos j).le (by norm_num))
  have he : nativeRecorder rate rewards C_star C_h q z = f ∘ Prod.fst := by
    funext c
    simp only [nativeRecorder, hen, f, P, Function.comp_apply]
  rw [he]
  have hf : Measurable f := SnapshotRecordingKernel.measurable_recordingMap p .collection rate.eta.val
    rate.eta.property rate.sourceCap _ _ _ _ _ _ true
  rw [ContinuousLearningRows.timeControlLaw, ← Measure.map_map hf measurable_fst,
    (measurePreserving_fst (μ := ContinuousControlSlice.sliceLaw p.m p.K)
      (ν := ContinuousLearningRows.affineSamplesLaw p)).map_eq]
  exact SnapshotRecordingKernel.map_recordingMap p .collection rate.eta.val
    rate.eta.property rate.sourceCap _ _ _ _ _ _

/-- The native pair uses a fixed OLD anchor/PRE and the genuine incoming logical complement. -/
def nativePair
    (z : ReferencePostInvocationNoncallGeometry.CollectionDateSource rate rewards C_star C_h q)
    (U : SlowSet p) (c : Control p) : Option (Fin p.K) × CanonicalFastSampling.FastArm U :=
  let P := (ReferencePostInvocationNoncallGeometry.collectionArguments rate rewards C_star C_h q z).1
  let S := ReferencePostInvocationNoncallGeometry.collectionBefore rate rewards C_star C_h q z
  (nativeRecorder rate rewards C_star C_h q z c,
    ReferencePostInvocationNoncallGeometry.collectionFastDraw rate P.anchor (RecordedQueueRun.scoreWeight Q S)
      P.anchor_pos (RecordedSlowRefresh.scoreWeight_pos Q S) U (c.1 ContinuousControlSlice.Label.fast))

theorem measurable_nativePair
    (z : ReferencePostInvocationNoncallGeometry.CollectionDateSource rate rewards C_star C_h q)
    (U : SlowSet p) : Measurable (nativePair rate rewards C_star C_h q z U) := by
  exact (measurable_nativeRecorder rate rewards C_star C_h q z).prodMk
    (ReferencePostInvocationPrefixLocality.measurable_collectionFastDraw rate
      (fun _ => _) (fun _ => _) measurable_const measurable_const (fun _ => _) (fun _ => _) U
      (fun c : Control p => c.1 ContinuousControlSlice.Label.fast)
      ((measurable_pi_apply _).comp measurable_fst))

include control0 in
/-- Recorder/FAST factorization is proved by splitting the ACTUAL FAST
coordinate and the recorder nonuse identity; no joint law is assumed. -/
theorem nativePair_map
    (z : ReferencePostInvocationNoncallGeometry.CollectionDateSource rate rewards C_star C_h q)
    (U : SlowSet p)
    (hen : (ReferencePostInvocationNoncallGeometry.collectionInput rate rewards C_star C_h q z).enabled = true) :
    (ContinuousLearningRows.timeControlLaw p).map (nativePair rate rewards C_star C_h q z U) =
      (recorderPMF rate rewards C_star C_h q z).toMeasure.prod
        (collectionFastPMF rate
          (ReferencePostInvocationNoncallGeometry.collectionArguments rate rewards C_star C_h q z).1.anchor
          (RecordedQueueRun.scoreWeight Q (ReferencePostInvocationNoncallGeometry.collectionBefore rate rewards C_star C_h q z))
          (ReferencePostInvocationNoncallGeometry.collectionArguments rate rewards C_star C_h q z).1.anchor_pos
          (RecordedSlowRefresh.scoreWeight_pos Q _) U).toMeasure := by
  let E := ReferenceSourceFastScalarDisintegration.fastScalarControlSplit p
  let R := (ReferenceSourceFastScalarDisintegration.OtherFast p → Scalar) × ContinuousLearningRows.AffineSamples p
  let ν : Measure R := (Measure.pi (fun _ : ReferenceSourceFastScalarDisintegration.OtherFast p =>
    ContinuousControlSlice.scalarLaw)).prod (ContinuousLearningRows.affineSamplesLaw p)
  let recorderRest : R → Option (Fin p.K) := fun y =>
    nativeRecorder rate rewards C_star C_h q z (E.symm (control0.1 ContinuousControlSlice.Label.fast, y))
  let P := (ReferencePostInvocationNoncallGeometry.collectionArguments rate rewards C_star C_h q z).1
  let S := ReferencePostInvocationNoncallGeometry.collectionBefore rate rewards C_star C_h q z
  let draw := ReferencePostInvocationNoncallGeometry.collectionFastDraw rate P.anchor
    (RecordedQueueRun.scoreWeight Q S) P.anchor_pos (RecordedSlowRefresh.scoreWeight_pos Q S) U
  have hr : Measurable recorderRest := (measurable_nativeRecorder rate rewards C_star C_h q z).comp
    (E.symm.measurable.comp (measurable_const.prodMk measurable_id))
  have hd : Measurable draw := ReferencePostInvocationPrefixLocality.measurable_collectionFastDraw rate
    (fun _ => _) (fun _ => _) measurable_const measurable_const (fun _ => _) (fun _ => _) U id measurable_id
  have hrec (c : Control p) : recorderRest (E c).2 = nativeRecorder rate rewards C_star C_h q z c := by
    have he : E.symm (control0.1 ContinuousControlSlice.Label.fast, (E c).2) =
        ReferenceFirstCollectionFastErasure.replaceFastScalar c (control0.1 ContinuousControlSlice.Label.fast) := by
      apply E.injective
      rw [E.apply_symm_apply]
      dsimp only [E]
      rw [ReferenceSourceFastScalarDisintegration.fastScalarControlSplit_apply,
        ReferenceSourceFastScalarDisintegration.fastScalarControlSplit_apply]
      simp only [ReferenceFirstCollectionFastErasure.replaceFastScalar, Function.update_self]
      congr 2
      funext i
      exact (Function.update_of_ne i.property _ _).symm
    dsimp only [recorderRest]
    rw [he]
    exact nativeRecorder_replaceFast rate rewards C_star C_h q z c _
  have hE : (ContinuousLearningRows.timeControlLaw p).map E =
      ContinuousControlSlice.scalarLaw.prod ν :=
    (ReferenceSourceFastScalarDisintegration.fastScalarControlSplit_measurePreserving p).map_eq
  have hrecMap : ν.map recorderRest = (recorderPMF rate rewards C_star C_h q z).toMeasure := by
    have hs := congrArg (fun μ : Measure (Scalar × R) => μ.map (recorderRest ∘ Prod.snd)) hE
    rw [Measure.map_map (hr.comp measurable_snd) E.measurable] at hs
    have hf : (recorderRest ∘ Prod.snd) ∘ E = nativeRecorder rate rewards C_star C_h q z := funext hrec
    rw [hf, nativeRecorder_map rate rewards C_star C_h q z hen,
      ← Measure.map_map hr measurable_snd,
      (measurePreserving_snd (μ := ContinuousControlSlice.scalarLaw) (ν := ν)).map_eq] at hs
    exact hs.symm
  let F : Scalar × R → Option (Fin p.K) × CanonicalFastSampling.FastArm U := fun y => (recorderRest y.2, draw y.1)
  have hF : Measurable F := (hr.comp measurable_snd).prodMk (hd.comp measurable_fst)
  have hfun : nativePair rate rewards C_star C_h q z U = F ∘ E := by
    funext c
    exact Prod.ext (hrec c).symm rfl
  rw [hfun, ← Measure.map_map hF E.measurable, hE,
    ← Measure.prod_swap (μ := ν) (ν := ContinuousControlSlice.scalarLaw),
    Measure.map_map hF measurable_swap]
  change (ν.prod ContinuousControlSlice.scalarLaw).map (Prod.map recorderRest draw) = _
  rw [← Measure.map_prod_map ν ContinuousControlSlice.scalarLaw hr hd, hrecMap,
    collectionFastDraw_map]

/-- The same round with a specified marker. This retains full rates/rewards and enablement. -/
def markerRound (z : ReferencePostInvocationNoncallGeometry.CollectionDateSource rate rewards C_star C_h q)
    (i : Option (Fin p.K)) : RecordedQueueRun.RoundInput p.K :=
  { ReferencePostInvocationNoncallGeometry.collectionInput rate rewards C_star C_h q z with recordedArm := i }

private theorem collectionInput_reward
    (z : ReferencePostInvocationNoncallGeometry.CollectionDateSource rate rewards C_star C_h q) :
    (ReferencePostInvocationNoncallGeometry.collectionInput rate rewards C_star C_h q z).reward =
      (fun a => ((rewards q a).val : ℝ) / (D p : ℝ)) := by
  have hr := (ReferencePostInvocationNoncallGeometry.collectionRecord_spec rate rewards C_star C_h q z).1
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hreward, _⟩ :=
    ReferenceLaterCollectionArrivalReadout.laterCollectionReadout_call 0 _ _
      (ReferencePostInvocationPrefixLocality.collectionInput_spec rate rewards C_star C_h q z)
  have hf := ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields
    rate rewards C_star C_h q z.val _ hr
  exact hreward.trans (by rw [hf.2.2.1, hf.2.2.2])

/-- The whole numerical input varies only through the literal physical marker. -/
theorem collectionInput_replace_control
    (z : ReferencePostInvocationNoncallGeometry.CollectionDateSource rate rewards C_star C_h q)
    (c : Control p) :
    ReferencePostInvocationNoncallGeometry.collectionInput rate rewards C_star C_h q
        (replaceCollectionSource rate rewards C_star C_h control0 q z c) =
      markerRound rate rewards C_star C_h q z (nativeRecorder rate rewards C_star C_h q z c) := by
  let z' := replaceCollectionSource rate rewards C_star C_h control0 q z c
  have he := collectionEnabled_replace_control rate rewards C_star C_h control0 q z c
  have hp := collectionPayload_replace_control rate rewards C_star C_h control0 q z c
  have hm := laterCollectionInput_recordingMap rate rewards C_star C_h q z'
  have hr := collectionRecord_replace_control rate rewards C_star C_h control0 q z c
  have ht := (ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields
    rate rewards C_star C_h q z.val _
    (ReferencePostInvocationNoncallGeometry.collectionRecord_spec rate rewards C_star C_h q z).1).2.2.1
  have hslice : ((ReferencePostInvocationNoncallGeometry.collectionRecord rate rewards C_star C_h q z').input.row.2
      (ReferencePostInvocationNoncallGeometry.collectionRecord rate rewards C_star C_h q z').input.time).1 = c.1 := by
    rw [hr]
    simp only [controlledRecord, inputAtControl_row, rowAtControl, inputAtControl_time, Function.update_self]
  dsimp only at hm
  rw [he, hp, hslice] at hm
  have hrate : (ReferencePostInvocationNoncallGeometry.collectionInput rate rewards C_star C_h q z').rate =
      (ReferencePostInvocationNoncallGeometry.collectionInput rate rewards C_star C_h q z).rate := by
    rw [(ReferencePostInvocationGeneratedAlignment.collectionInput_parameters rate rewards C_star C_h q z').1,
      hp, ← (ReferencePostInvocationGeneratedAlignment.collectionInput_parameters rate rewards C_star C_h q z).1]
  have hreward := (collectionInput_reward rate rewards C_star C_h q z').trans
    (collectionInput_reward rate rewards C_star C_h q z).symm
  have heq {x y : RecordedQueueRun.RoundInput p.K} (he : x.enabled = y.enabled)
      (hm : x.recordedArm = y.recordedArm) (hw : x.reward = y.reward) (hr : x.rate = y.rate) : x = y := by
    cases x
    cases y
    cases he
    cases hm
    cases hw
    cases hr
    rfl
  exact heq he hm hreward hrate

/-- The actual COLLECTION proposal uses label zero with the source hazard. -/
def auxiliaryProposal (rate : ReferenceActivePhysicalStep.RateInput p) (x : Scalar) : Bool :=
  decide (x.val < 4 * p.m * rate.eta.val)

theorem measurable_auxiliaryProposal : Measurable (auxiliaryProposal rate) := by
  have h : Measurable (fun x : Scalar =>
      if x.val < 4 * p.m * rate.eta.val then true else false) := (measurable_const (a := true)).ite
    (measurableSet_lt (measurable_subtype_coe : Measurable (Subtype.val : Scalar → ℝ))
      measurable_const) (measurable_const (a := false))
  convert h using 1
  funext x
  by_cases hx : x.val < 4 * p.m * rate.eta.val <;>
    simp only [auxiliaryProposal, hx, decide_true, decide_false, ite_true, ite_false]

theorem auxiliaryProposal_map :
    ContinuousControlSlice.scalarLaw.map (auxiliaryProposal rate) =
      ReferenceFirstLivePostUpdateProposalLaw.proposalBitLaw rate := rfl

/-- On a fixed actual later COLLECTION source, replace only the proposal and
refresh outcomes. The old physical payload, raw numerical input, FAST and
whole-arm numerical update remain exactly the original ones. -/
def collectionCellWithDraws
    (z : ReferencePostInvocationNoncallGeometry.CollectionDateSource rate rewards C_star C_h q)
    (U : SlowSet p) (draw : Bool × SlowSet p) : LogicalCell p rate :=
  let S := ReferencePostInvocationNoncallGeometry.collectionBefore rate rewards C_star C_h q z
  let c := ReferencePostInvocationNoncallGeometry.collectionInput rate rewards C_star C_h q z
  let proposed := c.enabled && !S.overflow && draw.1
  { ReferencePostInvocationNoncallGeometry.laterCollectionCell rate rewards C_star C_h q z U
      ReferenceFirstLiveActualRefreshTestLaw.auxiliarySection with
    proposal := proposed
    nextSlowSet := if S.overflow then frozenSlowSet p else if proposed then draw.2 else U }

/-- Exact later-COLLECTION auxiliary law using its ACTUAL old anchor and
actual numerical PRE/round. Inactive and PRE-overflow branches ignore the
draws internally. No POST-overflow test suppresses the detecting update. -/
theorem laterCollectionCell_auxiliary_pair_law
    (z : ReferencePostInvocationNoncallGeometry.CollectionDateSource rate rewards C_star C_h q)
    (U : SlowSet p) (a : Auxiliary p) :
    (ContinuousControlSlice.scalarLaw.prod ContinuousControlSlice.scalarLaw).map
      (fun x => ReferencePostInvocationNoncallGeometry.laterCollectionCell
        rate rewards C_star C_h q z U
          (ReferenceFirstNextLiftFutureAuxiliaryPairLaw.fillAuxiliaryPair q a x)) =
    ((ReferenceFirstLivePostUpdateProposalLaw.proposalBitLaw rate).prod
      (RecordedSlowRefresh.residualPMF p (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        (ReferencePostInvocationNoncallGeometry.collectionBefore rate rewards C_star C_h q z)
        (ReferencePostInvocationNoncallGeometry.collectionInput rate rewards C_star C_h q z)
        (ReferencePostInvocationNoncallGeometry.collectionArguments rate rewards C_star C_h q z).1.anchor
        (ReferencePostInvocationNoncallGeometry.collectionArguments rate rewards C_star C_h q z).1.anchor_pos).toMeasure).map
          (collectionCellWithDraws rate rewards C_star C_h q z U) := by
  let S := ReferencePostInvocationNoncallGeometry.collectionBefore rate rewards C_star C_h q z
  let c := ReferencePostInvocationNoncallGeometry.collectionInput rate rewards C_star C_h q z
  let P := (ReferencePostInvocationNoncallGeometry.collectionArguments rate rewards C_star C_h q z).1
  let residual := residualDraw rate S c P.anchor P.anchor_pos
  have hr : Measurable residual := by
    exact (measurable_residualDraw_of_measurable_residualMass rate
      (fun _ => S) (fun _ => c) (fun _ => P.anchor) (fun _ => P.anchor_pos)
      id measurable_id (fun _ => measurable_const)).mono le_rfl le_top
  have hdraw := Measure.map_prod_map ContinuousControlSlice.scalarLaw
    ContinuousControlSlice.scalarLaw (measurable_auxiliaryProposal rate) hr
  dsimp only [residual] at hdraw
  rw [auxiliaryProposal_map,
    ReferenceFirstLiveCalendarMarkedTransition.residualDraw_map rate S c P.anchor P.anchor_pos] at hdraw
  rw [hdraw, Measure.map_map (measurable_of_finite _)
    ((measurable_auxiliaryProposal rate).prodMap hr)]
  congr 1
  funext x
  rcases x with ⟨x0, x1⟩
  simp only [Function.comp_apply, Prod.map_apply, collectionCellWithDraws,
    ReferencePostInvocationNoncallGeometry.laterCollectionCell,
    ReferenceFirstNextLiftFutureAuxiliaryPairLaw.fillAuxiliaryPair,
    Function.update_self, Function.update_of_ne (show (q, (0 : Fin 2)) ≠ (q, (1 : Fin 2)) by simp),
    auxiliaryProposal, S, c, P, residual]
  rfl

/-- The native joint COLLECTION proposal/refresh law: true atoms have mass
`h * residualMass(V)`; false retains exactly the incoming set with mass `1-h`.
The old anchor and numerical POST are the SAME ones used by the actual cell. -/
theorem laterCollectionCell_proposal_refresh_joint_law
    (z : ReferencePostInvocationNoncallGeometry.CollectionDateSource rate rewards C_star C_h q)
    (U : SlowSet p) (a : Auxiliary p)
    (hpre : (ReferencePostInvocationNoncallGeometry.collectionBefore rate rewards C_star C_h q z).overflow = false)
    (hen : (ReferencePostInvocationNoncallGeometry.collectionInput rate rewards C_star C_h q z).enabled = true) :
    (ContinuousControlSlice.scalarLaw.prod ContinuousControlSlice.scalarLaw).map
      (fun x =>
        let e := ReferencePostInvocationNoncallGeometry.laterCollectionCell
          rate rewards C_star C_h q z U (ReferenceFirstNextLiftFutureAuxiliaryPairLaw.fillAuxiliaryPair q a x)
        (e.proposal, e.nextSlowSet)) =
    ((ReferenceFirstLivePostUpdateProposalLaw.proposalBitLaw rate).prod
      (RecordedSlowRefresh.residualPMF p (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        (ReferencePostInvocationNoncallGeometry.collectionBefore rate rewards C_star C_h q z)
        (ReferencePostInvocationNoncallGeometry.collectionInput rate rewards C_star C_h q z)
        (ReferencePostInvocationNoncallGeometry.collectionArguments rate rewards C_star C_h q z).1.anchor
        (ReferencePostInvocationNoncallGeometry.collectionArguments rate rewards C_star C_h q z).1.anchor_pos).toMeasure).map
          (fun x => (x.1, if x.1 then x.2 else U)) := by
  let S := ReferencePostInvocationNoncallGeometry.collectionBefore rate rewards C_star C_h q z
  let c := ReferencePostInvocationNoncallGeometry.collectionInput rate rewards C_star C_h q z
  let P := (ReferencePostInvocationNoncallGeometry.collectionArguments rate rewards C_star C_h q z).1
  let residual := residualDraw rate S c P.anchor P.anchor_pos
  have hr : Measurable residual :=
    (measurable_residualDraw_of_measurable_residualMass rate
      (fun _ => S) (fun _ => c) (fun _ => P.anchor) (fun _ => P.anchor_pos)
      id measurable_id (fun _ => measurable_const)).mono le_rfl le_top
  have hd := Measure.map_prod_map ContinuousControlSlice.scalarLaw
    ContinuousControlSlice.scalarLaw (measurable_auxiliaryProposal rate) hr
  dsimp only [residual] at hd
  rw [auxiliaryProposal_map,
    ReferenceFirstLiveCalendarMarkedTransition.residualDraw_map rate S c P.anchor P.anchor_pos] at hd
  rw [hd, Measure.map_map (measurable_of_finite _)
    ((measurable_auxiliaryProposal rate).prodMap hr)]
  congr 1
  funext x
  simp only [Function.comp_apply,
    ReferencePostInvocationNoncallGeometry.laterCollectionCell,
    ReferenceFirstNextLiftFutureAuxiliaryPairLaw.fillAuxiliaryPair,
    Function.update_self, Function.update_of_ne (show (q, (0 : Fin 2)) ≠ (q, (1 : Fin 2)) by simp),
    hpre, hen, Bool.not_false, Bool.true_and, Bool.false_eq_true, ite_false,
    residual, S, c, P]
  rfl

/-- PRE overflow freezes logical outputs and accepted updates, while the
original physical numerical readout and every date's false record remain. -/
theorem laterCollectionCell_pre_overflow
    (z : ReferencePostInvocationNoncallGeometry.CollectionDateSource rate rewards C_star C_h q)
    (U : SlowSet p) (a : Auxiliary p)
    (hpre : (ReferencePostInvocationNoncallGeometry.collectionBefore rate rewards C_star C_h q z).overflow = true) :
    let S := ReferencePostInvocationNoncallGeometry.collectionBefore rate rewards C_star C_h q z
    let c := ReferencePostInvocationNoncallGeometry.collectionInput rate rewards C_star C_h q z
    let e := ReferencePostInvocationNoncallGeometry.laterCollectionCell rate rewards C_star C_h q z U a
    e.slowSet = frozenSlowSet p ∧ e.fastArm = frozenFastArm p ∧
      e.proposal = false ∧ e.nextSlowSet = frozenSlowSet p ∧
      e.numerical = ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates c ∧
      ∀ j, e.arrivals j = (false, 0) ∧ e.service j = 0 ∧
        e.after.records j = S.records j ++ [(false, 0)] := by
  simp only [ReferencePostInvocationNoncallGeometry.laterCollectionCell, hpre,
    Bool.not_true, Bool.and_false, Bool.false_and, ite_true,
    RecordedQueueRun.acceptedRecord, RecordedQueueRun.recordService,
    RecordedQueueRun.step, Bool.false_eq_true, ite_false, and_self, implies_true]

/-- The native absent-cell atom on a disabled actual COLLECTION date is a
unit tag with mass one. Its physical numerical date is still present in the
full source observation used by `surviving_joint_integral`. -/
theorem laterCollection_disabled_outcome_law
    (z : ReferencePostInvocationNoncallGeometry.CollectionDateSource rate rewards C_star C_h q)
    (U : SlowSet p) (a : Auxiliary p)
    (hen : (ReferencePostInvocationNoncallGeometry.collectionInput rate rewards C_star C_h q z).enabled = false) :
    (ContinuousControlSlice.scalarLaw.prod ContinuousControlSlice.scalarLaw).map
      (fun x => optionalOutcome rate
        (ReferencePostInvocationNoncallGeometry.laterCollectionCell? rate rewards C_star C_h q z U
          (ReferenceFirstNextLiftFutureAuxiliaryPairLaw.fillAuxiliaryPair q a x))) =
      Measure.dirac (α := Outcome p) (Sum.inl ()) := by
  have hfun : (fun x : Scalar × Scalar => optionalOutcome rate
      (ReferencePostInvocationNoncallGeometry.laterCollectionCell? rate rewards C_star C_h q z U
        (ReferenceFirstNextLiftFutureAuxiliaryPairLaw.fillAuxiliaryPair q a x))) =
      fun _ => (Sum.inl () : Outcome p) := by
    funext x
    simp only [ReferencePostInvocationNoncallGeometry.laterCollectionCell?, hen,
      Bool.false_eq_true, ite_false, optionalOutcome]
  rw [hfun, Measure.map_const (β := Outcome p)
    (ContinuousControlSlice.scalarLaw.prod ContinuousControlSlice.scalarLaw) (Sum.inl ()),
    measure_univ, one_smul]

/-- The enabled PRE-overflow outcome has its prescribed single frozen atom.
The raw physical numerical cell is retained separately, rather than zeroed. -/
theorem laterCollection_overflow_outcome_law
    (z : ReferencePostInvocationNoncallGeometry.CollectionDateSource rate rewards C_star C_h q)
    (U : SlowSet p) (a : Auxiliary p)
    (hen : (ReferencePostInvocationNoncallGeometry.collectionInput rate rewards C_star C_h q z).enabled = true)
    (hpre : (ReferencePostInvocationNoncallGeometry.collectionBefore rate rewards C_star C_h q z).overflow = true) :
    (ContinuousControlSlice.scalarLaw.prod ContinuousControlSlice.scalarLaw).map
      (fun x => optionalOutcome rate
        (ReferencePostInvocationNoncallGeometry.laterCollectionCell? rate rewards C_star C_h q z U
          (ReferenceFirstNextLiftFutureAuxiliaryPairLaw.fillAuxiliaryPair q a x))) =
      Measure.dirac (α := Outcome p) (Sum.inr (none, frozenFastArm p, false, frozenSlowSet p)) := by
  have hfun : (fun x : Scalar × Scalar => optionalOutcome rate
      (ReferencePostInvocationNoncallGeometry.laterCollectionCell? rate rewards C_star C_h q z U
        (ReferenceFirstNextLiftFutureAuxiliaryPairLaw.fillAuxiliaryPair q a x))) =
      fun _ => (Sum.inr (none, frozenFastArm p, false, frozenSlowSet p) : Outcome p) := by
    funext x
    simp only [ReferencePostInvocationNoncallGeometry.laterCollectionCell?, hen, ite_true,
      optionalOutcome, cellOutcome, ReferencePostInvocationNoncallGeometry.laterCollectionCell,
      hpre, Bool.not_true, Bool.and_false, Bool.false_and, ite_true]
  rw [hfun, Measure.map_const (β := Outcome p)
    (ContinuousControlSlice.scalarLaw.prod ContinuousControlSlice.scalarLaw)
      (Sum.inr (none, frozenFastArm p, false, frozenSlowSet p)), measure_univ, one_smul]


/-- Whole original control and two independent genuine auxiliary labels. -/
def innovationLaw : Measure (Control p × Scalar × Scalar) :=
  (ContinuousLearningRows.timeControlLaw p).prod
    (ContinuousControlSlice.scalarLaw.prod ContinuousControlSlice.scalarLaw)

/-- The actual optional collection output of the whole-control source family. -/
def sourceOutcome
    (z : ReferencePostInvocationNoncallGeometry.CollectionDateSource rate rewards C_star C_h q)
    (U : SlowSet p) (a : Auxiliary p) (ω : Control p × Scalar × Scalar) : Outcome p :=
  optionalOutcome rate (ReferencePostInvocationNoncallGeometry.laterCollectionCell? rate rewards C_star C_h q
    (replaceCollectionSource rate rewards C_star C_h control0 q z ω.1) U
    (ReferenceFirstNextLiftFutureAuxiliaryPairLaw.fillAuxiliaryPair q a ω.2))

theorem measurable_replaceCollectionSource
    (z : ReferencePostInvocationNoncallGeometry.CollectionDateSource rate rewards C_star C_h q) :
    Measurable (replaceCollectionSource rate rewards C_star C_h control0 q z) := by
  apply Measurable.subtype_mk
  exact (ReferenceSourcePhysicalFlagConditionalLaw.measurable_replaceSourceControl p q).comp
    (measurable_const.prodMk measurable_id)

theorem measurable_sourceOutcome
    (z : ReferencePostInvocationNoncallGeometry.CollectionDateSource rate rewards C_star C_h q)
    (U : SlowSet p) (a : Auxiliary p) :
    Measurable (sourceOutcome rate rewards C_star C_h control0 q z U a) := by
  have hz := (measurable_replaceCollectionSource rate rewards C_star C_h control0 q z).comp
    (measurable_fst : Measurable (Prod.fst : Control p × Scalar × Scalar → _))
  have ha := (ReferenceFirstNextLiftFutureAuxiliaryPairLaw.measurable_fillAuxiliaryPair q).comp
    ((measurable_const (a := a)).prodMk (measurable_snd : Measurable (Prod.snd : Control p × Scalar × Scalar → _)))
  have he := (ReferencePostInvocationPrefixLocality.measurable_laterCollectionCell
    rate rewards C_star C_h control0 q U).comp (hz.prodMk ha)
  unfold sourceOutcome ReferencePostInvocationNoncallGeometry.laterCollectionCell?
  simp only [collectionEnabled_replace_control]
  split
  · exact (measurable_cellOutcome rate).comp he
  · exact measurable_const

/-- The clear enabled output is the actual recorder/FAST pair followed by
proposal label zero and SAME-marker/SAME-OLD-anchor residual label one. -/
theorem sourceOutcome_clear
    (z : ReferencePostInvocationNoncallGeometry.CollectionDateSource rate rewards C_star C_h q)
    (U : SlowSet p) (a : Auxiliary p)
    (hen : (ReferencePostInvocationNoncallGeometry.collectionInput rate rewards C_star C_h q z).enabled = true)
    (hpre : (ReferencePostInvocationNoncallGeometry.collectionBefore rate rewards C_star C_h q z).overflow = false)
    (ω : Control p × Scalar × Scalar) :
    sourceOutcome rate rewards C_star C_h control0 q z U a ω =
      let pair := nativePair rate rewards C_star C_h q z U ω.1
      let B := auxiliaryProposal rate ω.2.1
      let P := (ReferencePostInvocationNoncallGeometry.collectionArguments rate rewards C_star C_h q z).1
      Sum.inr (pair.1, pair.2.val, B, if B then residualDraw rate
        (ReferencePostInvocationNoncallGeometry.collectionBefore rate rewards C_star C_h q z)
        (markerRound rate rewards C_star C_h q z pair.1) P.anchor P.anchor_pos ω.2.2 else U) := by
  have hf : ReferenceSourceFastScalarDisintegration.sourceFastScalar p q
      (replaceCollectionSource rate rewards C_star C_h control0 q z ω.1).val =
      ω.1.1 ContinuousControlSlice.Label.fast := by
    simp only [replaceCollectionSource, ReferenceSourceFastScalarDisintegration.sourceFastScalar,
      replaceSourceControl, sourceCoordinatorIndex, Function.update_self]
  unfold sourceOutcome ReferencePostInvocationNoncallGeometry.laterCollectionCell?
  rw [collectionEnabled_replace_control, hen]
  simp only [ite_true, optionalOutcome, cellOutcome,
    ReferencePostInvocationNoncallGeometry.laterCollectionCell]
  simp only [collectionBefore_replace_control, collectionPayload_replace_control,
    collectionInput_replace_control, hf]
  simp only [hpre, Bool.not_false, Bool.false_eq_true, ite_false, markerRound, hen,
    Bool.true_and, ReferenceFirstNextLiftFutureAuxiliaryPairLaw.fillAuxiliaryPair,
    Function.update_self, Function.update_of_ne (show (q, (0 : Fin 2)) ≠ (q, (1 : Fin 2)) by simp)]
  rfl

include control0 in
/-- Native recorder/FAST atom, derived from coordinate nonuse and the proved factorization. -/
theorem nativePair_atom
    (z : ReferencePostInvocationNoncallGeometry.CollectionDateSource rate rewards C_star C_h q)
    (U : SlowSet p)
    (hen : (ReferencePostInvocationNoncallGeometry.collectionInput rate rewards C_star C_h q z).enabled = true)
    (i : Option (Fin p.K)) (j : CanonicalFastSampling.FastArm U) :
    (ContinuousLearningRows.timeControlLaw p) (nativePair rate rewards C_star C_h q z U ⁻¹' {(i,j)}) =
      recorderPMF rate rewards C_star C_h q z i * ENNReal.ofReal
        (ReferencePostInvocationNoncallGeometry.collectionFastMass rate
          (ReferencePostInvocationNoncallGeometry.collectionArguments rate rewards C_star C_h q z).1.anchor
          (RecordedQueueRun.scoreWeight Q (ReferencePostInvocationNoncallGeometry.collectionBefore rate rewards C_star C_h q z))
          (ReferencePostInvocationNoncallGeometry.collectionArguments rate rewards C_star C_h q z).1.anchor_pos
          (RecordedSlowRefresh.scoreWeight_pos Q _) U j) := by
  have h := congrArg (fun μ => μ {(i,j)})
    (nativePair_map rate rewards C_star C_h control0 q z U hen)
  rw [Measure.map_apply (measurable_nativePair rate rewards C_star C_h q z U)
    (measurableSet_singleton _), ← Set.singleton_prod_singleton, Measure.prod_prod,
    PMF.toMeasure_apply_singleton _ i (measurableSet_singleton i),
    PMF.toMeasure_apply_singleton _ j (measurableSet_singleton j), collectionFastPMF_apply] at h
  simpa only [Set.singleton_prod_singleton] using h

private theorem proposalBitLaw_false :
    ReferenceFirstLivePostUpdateProposalLaw.proposalBitLaw rate {false} =
      ENNReal.ofReal (1 - 4 * p.m * rate.eta.val) := by
  have hs : ({false} : Set Bool) = {true}ᶜ := by ext b; cases b <;> decide
  rw [hs, prob_compl_eq_one_sub (measurableSet_singleton true),
    ReferenceFirstLivePostUpdateProposalLaw.proposalBitLaw_true]
  change 1 - ENNReal.ofReal (FollowerCutoffScan.proposalHazard p rate.eta.val) =
    ENNReal.ofReal (1 - FollowerCutoffScan.proposalHazard p rate.eta.val)
  rw [ENNReal.ofReal_sub 1 (ReferenceFirstLivePostUpdateProposalLaw.physicalProposalThreshold_bounds rate).1.le,
    ENNReal.ofReal_one]

/-- Fixed-marker auxiliary readout, using distinct labels and the original residual draw. -/
def auxiliaryOutcome
    (z : ReferencePostInvocationNoncallGeometry.CollectionDateSource rate rewards C_star C_h q)
    (U : SlowSet p) (i : Option (Fin p.K)) (x : Scalar × Scalar) : Bool × SlowSet p :=
  let B := auxiliaryProposal rate x.1
  let P := (ReferencePostInvocationNoncallGeometry.collectionArguments rate rewards C_star C_h q z).1
  (B, if B then residualDraw rate
    (ReferencePostInvocationNoncallGeometry.collectionBefore rate rewards C_star C_h q z)
    (markerRound rate rewards C_star C_h q z i) P.anchor P.anchor_pos x.2 else U)

/-- Native Bernoulli/residual coefficients. POST overflow is absent from this expression. -/
def auxiliaryMass
    (z : ReferencePostInvocationNoncallGeometry.CollectionDateSource rate rewards C_star C_h q)
    (U : SlowSet p) (i : Option (Fin p.K)) (B : Bool) (V : SlowSet p) : ENNReal :=
  if B then ENNReal.ofReal (4 * p.m * rate.eta.val) * ENNReal.ofReal
    (RecordedSlowRefresh.residualMass p Q
      (ReferencePostInvocationNoncallGeometry.collectionBefore rate rewards C_star C_h q z)
      (markerRound rate rewards C_star C_h q z i)
      (ReferencePostInvocationNoncallGeometry.collectionArguments rate rewards C_star C_h q z).1.anchor
      (ReferencePostInvocationNoncallGeometry.collectionArguments rate rewards C_star C_h q z).1.anchor_pos V)
  else ENNReal.ofReal (1 - 4 * p.m * rate.eta.val) * (if V = U then 1 else 0)

theorem auxiliaryOutcome_atom
    (z : ReferencePostInvocationNoncallGeometry.CollectionDateSource rate rewards C_star C_h q)
    (U : SlowSet p) (i : Option (Fin p.K)) (B : Bool) (V : SlowSet p) :
    (ContinuousControlSlice.scalarLaw.prod ContinuousControlSlice.scalarLaw)
      (auxiliaryOutcome rate rewards C_star C_h q z U i ⁻¹' {(B,V)}) =
      auxiliaryMass rate rewards C_star C_h q z U i B V := by
  let P := (ReferencePostInvocationNoncallGeometry.collectionArguments rate rewards C_star C_h q z).1
  let S := ReferencePostInvocationNoncallGeometry.collectionBefore rate rewards C_star C_h q z
  let draw := residualDraw rate S (markerRound rate rewards C_star C_h q z i) P.anchor P.anchor_pos
  have hd : Measurable draw := (measurable_residualDraw_of_measurable_residualMass rate
    (fun _ => S) (fun _ => markerRound rate rewards C_star C_h q z i) (fun _ => P.anchor)
    (fun _ => P.anchor_pos) id measurable_id (fun _ => measurable_const)).mono le_rfl le_top
  have hr : ContinuousControlSlice.scalarLaw (draw ⁻¹' {V}) = ENNReal.ofReal
      (RecordedSlowRefresh.residualMass p Q S (markerRound rate rewards C_star C_h q z i) P.anchor P.anchor_pos V) := by
    have h := congrArg (fun μ => μ {V})
      (ReferenceFirstLiveCalendarMarkedTransition.residualDraw_map rate S
        (markerRound rate rewards C_star C_h q z i) P.anchor P.anchor_pos)
    rw [Measure.map_apply hd (measurableSet_singleton V),
      PMF.toMeasure_apply_singleton _ V (measurableSet_singleton V), RecordedSlowRefresh.residualPMF_apply] at h
    exact h
  have hb (b : Bool) : ContinuousControlSlice.scalarLaw (auxiliaryProposal rate ⁻¹' {b}) =
      ReferenceFirstLivePostUpdateProposalLaw.proposalBitLaw rate {b} := by
    rw [← auxiliaryProposal_map, Measure.map_apply (measurable_auxiliaryProposal rate) (measurableSet_singleton b)]
  cases B with
  | true =>
    have he : auxiliaryOutcome rate rewards C_star C_h q z U i ⁻¹' {(true,V)} =
        (auxiliaryProposal rate ⁻¹' {true}) ×ˢ (draw ⁻¹' {V}) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, auxiliaryOutcome, Prod.mk.injEq,
        Set.mem_prod, draw, P, S]
      by_cases h : auxiliaryProposal rate x.1 = true <;> simp [h]
    rw [he, Measure.prod_prod, hb, ReferenceFirstLivePostUpdateProposalLaw.proposalBitLaw_true, hr]
    rfl
  | false =>
    have he : auxiliaryOutcome rate rewards C_star C_h q z U i ⁻¹' {(false,V)} =
        (auxiliaryProposal rate ⁻¹' {false}) ×ˢ (if V = U then Set.univ else ∅) := by
      ext x
      cases h : auxiliaryProposal rate x.1 <;> simp [auxiliaryOutcome, h, eq_comm]
    rw [he, Measure.prod_prod, hb, proposalBitLaw_false]
    by_cases hv : V = U <;> simp only [auxiliaryMass, Bool.false_eq_true, ite_false, hv,
      ite_true, measure_univ, measure_empty, mul_one, mul_zero]

private theorem tuple_fibre (U : SlowSet p)
    (F : Option (Fin p.K) → Bool × SlowSet p)
    (k : Option (Fin p.K) × CanonicalFastSampling.FastArm U)
    (i : Option (Fin p.K)) (j : CanonicalFastSampling.FastArm U) (B : Bool) (V : SlowSet p) :
    (Sum.inr (k.1,k.2.val,(F k.1).1,(F k.1).2) : Outcome p) = Sum.inr (i,j.val,B,V) ↔
      k = (i,j) ∧ F i = (B,V) := by
  rcases k with ⟨i',j'⟩
  constructor
  · intro h
    have ht := Sum.inr.inj h
    simp only [Prod.mk.injEq] at ht
    have hi : i' = i := ht.1
    have hj : j' = j := Subtype.ext ht.2.1
    subst i'
    subst j'
    exact ⟨rfl, Prod.ext ht.2.2.1 ht.2.2.2⟩
  · rintro ⟨hk,hF⟩
    cases hk
    exact congrArg (fun d : Bool × SlowSet p => (Sum.inr (i,j.val,d.1,d.2) : Outcome p)) hF

/-- The finite mass of the actual whole-control collection source family.
The recorder/FAST coefficient was factored only after the nonuse proof. -/
theorem sourceOutcome_clear_atom
    (z : ReferencePostInvocationNoncallGeometry.CollectionDateSource rate rewards C_star C_h q)
    (U : SlowSet p) (a : Auxiliary p)
    (hen : (ReferencePostInvocationNoncallGeometry.collectionInput rate rewards C_star C_h q z).enabled = true)
    (hpre : (ReferencePostInvocationNoncallGeometry.collectionBefore rate rewards C_star C_h q z).overflow = false)
    (i : Option (Fin p.K)) (j : CanonicalFastSampling.FastArm U) (B : Bool) (V : SlowSet p) :
    (innovationLaw (p := p)).map (sourceOutcome rate rewards C_star C_h control0 q z U a)
      {(Sum.inr (i,j.val,B,V) : Outcome p)} =
      (recorderPMF rate rewards C_star C_h q z i * ENNReal.ofReal
        (ReferencePostInvocationNoncallGeometry.collectionFastMass rate
          (ReferencePostInvocationNoncallGeometry.collectionArguments rate rewards C_star C_h q z).1.anchor
          (RecordedQueueRun.scoreWeight Q (ReferencePostInvocationNoncallGeometry.collectionBefore rate rewards C_star C_h q z))
          (ReferencePostInvocationNoncallGeometry.collectionArguments rate rewards C_star C_h q z).1.anchor_pos
          (RecordedSlowRefresh.scoreWeight_pos Q _) U j)) *
      auxiliaryMass rate rewards C_star C_h q z U i B V := by
  rw [Measure.map_apply (measurable_sourceOutcome rate rewards C_star C_h control0 q z U a)
    (measurableSet_singleton _)]
  have he : sourceOutcome rate rewards C_star C_h control0 q z U a ⁻¹' {(Sum.inr (i,j.val,B,V) : Outcome p)} =
      (nativePair rate rewards C_star C_h q z U ⁻¹' {(i,j)}) ×ˢ
        (auxiliaryOutcome rate rewards C_star C_h q z U i ⁻¹' {(B,V)}) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_prod]
    rw [sourceOutcome_clear rate rewards C_star C_h control0 q z U a hen hpre]
    change (Sum.inr ((nativePair rate rewards C_star C_h q z U ω.1).1,
      (nativePair rate rewards C_star C_h q z U ω.1).2.val,
      (auxiliaryOutcome rate rewards C_star C_h q z U
        (nativePair rate rewards C_star C_h q z U ω.1).1 ω.2).1,
      (auxiliaryOutcome rate rewards C_star C_h q z U
        (nativePair rate rewards C_star C_h q z U ω.1).1 ω.2).2) : Outcome p) = _ ↔ _
    exact tuple_fibre U (fun k => auxiliaryOutcome rate rewards C_star C_h q z U k ω.2)
      (nativePair rate rewards C_star C_h q z U ω.1) i j B V
  rw [he, innovationLaw, Measure.prod_prod,
    nativePair_atom rate rewards C_star C_h control0 q z U hen i j,
    auxiliaryOutcome_atom rate rewards C_star C_h q z U i B V]

instance innovationLaw_probability : IsProbabilityMeasure (innovationLaw (p := p)) := by
  unfold innovationLaw
  infer_instance

/-- Disabled dates have the Unit atom under the SAME whole-control law. -/
theorem sourceOutcome_disabled_law
    (z : ReferencePostInvocationNoncallGeometry.CollectionDateSource rate rewards C_star C_h q)
    (U : SlowSet p) (a : Auxiliary p)
    (hen : (ReferencePostInvocationNoncallGeometry.collectionInput rate rewards C_star C_h q z).enabled = false) :
    (innovationLaw (p := p)).map (sourceOutcome rate rewards C_star C_h control0 q z U a) =
      Measure.dirac (α := Outcome p) (Sum.inl ()) := by
  have hf : sourceOutcome rate rewards C_star C_h control0 q z U a = fun _ => (Sum.inl () : Outcome p) := by
    funext ω
    simp only [sourceOutcome, ReferencePostInvocationNoncallGeometry.laterCollectionCell?,
      collectionEnabled_replace_control, hen, Bool.false_eq_true, ite_false, optionalOutcome]
  rw [hf, Measure.map_const (β := Outcome p), measure_univ, one_smul]

/-- PRE overflow has the single frozen tuple under the same whole-control law. -/
theorem sourceOutcome_overflow_law
    (z : ReferencePostInvocationNoncallGeometry.CollectionDateSource rate rewards C_star C_h q)
    (U : SlowSet p) (a : Auxiliary p)
    (hen : (ReferencePostInvocationNoncallGeometry.collectionInput rate rewards C_star C_h q z).enabled = true)
    (hpre : (ReferencePostInvocationNoncallGeometry.collectionBefore rate rewards C_star C_h q z).overflow = true) :
    (innovationLaw (p := p)).map (sourceOutcome rate rewards C_star C_h control0 q z U a) =
      Measure.dirac (α := Outcome p) (Sum.inr (none, frozenFastArm p, false, frozenSlowSet p)) := by
  have hf : sourceOutcome rate rewards C_star C_h control0 q z U a =
      fun _ => (Sum.inr (none, frozenFastArm p, false, frozenSlowSet p) : Outcome p) := by
    funext ω
    simp only [sourceOutcome, ReferencePostInvocationNoncallGeometry.laterCollectionCell?,
      collectionEnabled_replace_control, hen, ite_true, optionalOutcome, cellOutcome,
      ReferencePostInvocationNoncallGeometry.laterCollectionCell,
      collectionBefore_replace_control, hpre, Bool.not_true, Bool.and_false, Bool.false_and, ite_true]
  rw [hf, Measure.map_const (β := Outcome p), measure_univ, one_smul]

/-- Clear enabled collection outputs have no Unit atom. -/
theorem sourceOutcome_clear_unit
    (z : ReferencePostInvocationNoncallGeometry.CollectionDateSource rate rewards C_star C_h q)
    (U : SlowSet p) (a : Auxiliary p)
    (hen : (ReferencePostInvocationNoncallGeometry.collectionInput rate rewards C_star C_h q z).enabled = true)
    (hpre : (ReferencePostInvocationNoncallGeometry.collectionBefore rate rewards C_star C_h q z).overflow = false) :
    (innovationLaw (p := p)).map (sourceOutcome rate rewards C_star C_h control0 q z U a)
      {(Sum.inl () : Outcome p)} = 0 := by
  rw [Measure.map_apply (measurable_sourceOutcome rate rewards C_star C_h control0 q z U a)
    (measurableSet_singleton _)]
  have he : sourceOutcome rate rewards C_star C_h control0 q z U a ⁻¹' {(Sum.inl () : Outcome p)} = ∅ := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff,
      sourceOutcome_clear rate rewards C_star C_h control0 q z U a hen hpre, reduceCtorEq,
      Set.mem_empty_iff_false]
  rw [he, measure_empty]

/-- Clear enabled FAST outputs outside the genuine incoming complement have zero mass. -/
theorem sourceOutcome_clear_outside
    (z : ReferencePostInvocationNoncallGeometry.CollectionDateSource rate rewards C_star C_h q)
    (U : SlowSet p) (a : Auxiliary p)
    (hen : (ReferencePostInvocationNoncallGeometry.collectionInput rate rewards C_star C_h q z).enabled = true)
    (hpre : (ReferencePostInvocationNoncallGeometry.collectionBefore rate rewards C_star C_h q z).overflow = false)
    (i : Option (Fin p.K)) (j : Fin p.K) (hj : j ∉ CanonicalFastSampling.fastArmFinset U)
    (B : Bool) (V : SlowSet p) :
    (innovationLaw (p := p)).map (sourceOutcome rate rewards C_star C_h control0 q z U a)
      {(Sum.inr (i,j,B,V) : Outcome p)} = 0 := by
  rw [Measure.map_apply (measurable_sourceOutcome rate rewards C_star C_h control0 q z U a)
    (measurableSet_singleton _)]
  have he : sourceOutcome rate rewards C_star C_h control0 q z U a ⁻¹' {(Sum.inr (i,j,B,V) : Outcome p)} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro ω hω
    have h : sourceOutcome rate rewards C_star C_h control0 q z U a ω = Sum.inr (i,j,B,V) := hω
    rw [sourceOutcome_clear rate rewards C_star C_h control0 q z U a hen hpre] at h
    have ht := Sum.inr.inj h
    have hj' := congrArg (fun x : Option (Fin p.K) × Fin p.K × Bool × SlowSet p => x.2.1) ht
    change (nativePair rate rewards C_star C_h q z U ω.1).2.val = j at hj'
    have hmem := (nativePair rate rewards C_star C_h q z U ω.1).2.property
    rw [hj'] at hmem
    exact hj hmem
  rw [he, measure_empty]

/-- Actual generated old-episode prefixes supply their envelope internally.
The incoming logical set is arbitrary and need not equal the physical assignment. -/
theorem generated_collection_fastLaw
    (t : Fin p.T)
    (z : ReferenceFirstNextInstallationCellFactors.FirstInvocationSource rate rewards C_star C_h t)
    (htq : t.val < q.val)
    (hcall : ReferencePostInvocationNoncallGeometry.NoCallBetween rate rewards C_star C_h t q.castSucc z.val)
    (hc : z.val ∈ ReferencePostInvocationNoncallGeometry.collectionDateDomain rate rewards C_star C_h q)
    (hen : (ReferencePostInvocationNoncallGeometry.collectionInput rate rewards C_star C_h q ⟨z.val,hc⟩).enabled = true)
    (hpre : (ReferencePostInvocationNoncallGeometry.collectionBefore rate rewards C_star C_h q ⟨z.val,hc⟩).overflow = false) :
    let P := (ReferencePostInvocationNoncallGeometry.collectionArguments rate rewards C_star C_h q ⟨z.val,hc⟩).1
    let w := RecordedQueueRun.scoreWeight Q
      (ReferencePostInvocationNoncallGeometry.collectionBefore rate rewards C_star C_h q ⟨z.val,hc⟩)
    ∃ (hlo : ∀ j, P.anchor j ≤ w j) (hhi : ∀ j, w j ≤ 2 * P.anchor j), ∀ (U : SlowSet p) (j : CanonicalFastSampling.FastArm U),
      collectionFastPMF rate P.anchor w P.anchor_pos (RecordedSlowRefresh.scoreWeight_pos Q _) U j =
        ENNReal.ofReal (CanonicalFastSampling.qGamma p rate.eta.val rate.eta.property rate.sourceCap
          P.anchor w P.anchor_pos (RecordedSlowRefresh.scoreWeight_pos Q _) hlo hhi U j) := by
  have hboundary : q.val + 1 < FollowerCutoffScan.gridBoundary p rate.eta.val
      (ReferencePostInvocationNoncallGeometry.collectionArguments rate rewards C_star C_h q ⟨z.val,hc⟩).1.sigma := by
    have hg := (ReferencePostInvocationGeneratedAlignment.collectionInput_oldGrid rate rewards C_star C_h q ⟨z.val,hc⟩).2
    rw [hen] at hg
    exact of_decide_eq_true hg.symm
  obtain ⟨hlo,hhi,hlaw⟩ := ReferencePostInvocationGeneratedAlignment.firstInvocation_collection_fastLaw
    rate rewards C_star C_h t q z htq hcall hc hboundary hpre
  exact ⟨hlo,hhi, fun U j => (collectionFastPMF_apply rate _ _ _ _ U j).trans (congrArg ENNReal.ofReal (hlaw U j))⟩

/-- The recorder coefficient is the actual OLD rate, including its bottom mass. -/
theorem recorderPMF_apply
    (z : ReferencePostInvocationNoncallGeometry.CollectionDateSource rate rewards C_star C_h q)
    (i : Option (Fin p.K)) :
    recorderPMF rate rewards C_star C_h q z i = ENNReal.ofReal
      (match i with
      | none => 1 - ∑ j, (ReferencePostInvocationNoncallGeometry.collectionArguments rate rewards C_star C_h q z).1.rate j
      | some j => (ReferencePostInvocationNoncallGeometry.collectionArguments rate rewards C_star C_h q z).1.rate j) := by
  cases i <;> rfl

/-- All finite native coefficients, including absent and frozen branches.
These are explicit rates/FAST/residual coefficients, not a renamed pushforward. -/
def nativeMass
    (z : ReferencePostInvocationNoncallGeometry.CollectionDateSource rate rewards C_star C_h q)
    (U : SlowSet p) (o : Outcome p) : ENNReal :=
  if (ReferencePostInvocationNoncallGeometry.collectionInput rate rewards C_star C_h q z).enabled then
    if (ReferencePostInvocationNoncallGeometry.collectionBefore rate rewards C_star C_h q z).overflow then
      if o = Sum.inr (none, frozenFastArm p, false, frozenSlowSet p) then 1 else 0
    else match o with
      | .inl _ => 0
      | .inr (i,j,B,V) =>
        if hj : j ∈ CanonicalFastSampling.fastArmFinset U then
          (recorderPMF rate rewards C_star C_h q z i * ENNReal.ofReal
            (ReferencePostInvocationNoncallGeometry.collectionFastMass rate
              (ReferencePostInvocationNoncallGeometry.collectionArguments rate rewards C_star C_h q z).1.anchor
              (RecordedQueueRun.scoreWeight Q (ReferencePostInvocationNoncallGeometry.collectionBefore rate rewards C_star C_h q z))
              (ReferencePostInvocationNoncallGeometry.collectionArguments rate rewards C_star C_h q z).1.anchor_pos
              (RecordedSlowRefresh.scoreWeight_pos Q _) U ⟨j,hj⟩)) *
            auxiliaryMass rate rewards C_star C_h q z U i B V
        else 0
  else if o = Sum.inl () then 1 else 0

/-- Complete actual-root finite law. The only inputs are the actual collection
source, arbitrary incoming logical set, original auxiliary array, and tested atom. -/
theorem sourceOutcome_mass
    (z : ReferencePostInvocationNoncallGeometry.CollectionDateSource rate rewards C_star C_h q)
    (U : SlowSet p) (a : Auxiliary p) (o : Outcome p) :
    (innovationLaw (p := p)).map (sourceOutcome rate rewards C_star C_h control0 q z U a) {o} =
      nativeMass rate rewards C_star C_h q z U o := by
  cases hen : (ReferencePostInvocationNoncallGeometry.collectionInput rate rewards C_star C_h q z).enabled with
  | false =>
    rw [sourceOutcome_disabled_law rate rewards C_star C_h control0 q z U a hen]
    simp only [nativeMass, hen, Bool.false_eq_true, ite_false, Measure.dirac_apply,
      Set.mem_singleton_iff, Set.indicator_apply, Pi.one_apply]
    by_cases ho : o = Sum.inl () <;> simp [ho, eq_comm]
  | true =>
    cases hp : (ReferencePostInvocationNoncallGeometry.collectionBefore rate rewards C_star C_h q z).overflow with
    | true =>
      rw [sourceOutcome_overflow_law rate rewards C_star C_h control0 q z U a hen hp]
      simp only [nativeMass, hen, hp, ite_true, Measure.dirac_apply,
        Set.mem_singleton_iff, Set.indicator_apply, Pi.one_apply]
      by_cases ho : o = Sum.inr (none, frozenFastArm p, false, frozenSlowSet p) <;> simp [ho, eq_comm]
    | false =>
      cases o with
      | inl u =>
        cases u
        simpa only [nativeMass, hen, hp, ite_true, Bool.false_eq_true, ite_false] using
          sourceOutcome_clear_unit rate rewards C_star C_h control0 q z U a hen hp
      | inr tuple =>
        rcases tuple with ⟨i,j,B,V⟩
        by_cases hj : j ∈ CanonicalFastSampling.fastArmFinset U
        · simpa only [nativeMass, hen, hp, ite_true, Bool.false_eq_true, ite_false, dite_eq_left hj] using
            sourceOutcome_clear_atom rate rewards C_star C_h control0 q z U a hen hp i ⟨j,hj⟩ B V
        · simpa only [nativeMass, hen, hp, ite_true, Bool.false_eq_true, ite_false, dite_eq_right hj] using
            sourceOutcome_clear_outside rate rewards C_star C_h control0 q z U a hen hp i j hj B V

/-- Generated-prefix finite law with the prescribed qGamma. The OLD-anchor
all-arm envelope is produced internally from the actual first invocation,
call-free calendar localization, enablement, and numerical PRE clarity. -/
theorem generated_collection_clear_atom
    (t : Fin p.T)
    (z : ReferenceFirstNextInstallationCellFactors.FirstInvocationSource rate rewards C_star C_h t)
    (htq : t.val < q.val)
    (hcall : ReferencePostInvocationNoncallGeometry.NoCallBetween rate rewards C_star C_h t q.castSucc z.val)
    (hc : z.val ∈ ReferencePostInvocationNoncallGeometry.collectionDateDomain rate rewards C_star C_h q)
    (hen : (ReferencePostInvocationNoncallGeometry.collectionInput rate rewards C_star C_h q ⟨z.val,hc⟩).enabled = true)
    (hpre : (ReferencePostInvocationNoncallGeometry.collectionBefore rate rewards C_star C_h q ⟨z.val,hc⟩).overflow = false) :
    let zc : ReferencePostInvocationNoncallGeometry.CollectionDateSource rate rewards C_star C_h q := ⟨z.val,hc⟩
    let P := (ReferencePostInvocationNoncallGeometry.collectionArguments rate rewards C_star C_h q zc).1
    let w := RecordedQueueRun.scoreWeight Q (ReferencePostInvocationNoncallGeometry.collectionBefore rate rewards C_star C_h q zc)
    ∃ (hlo : ∀ j, P.anchor j ≤ w j) (hhi : ∀ j, w j ≤ 2 * P.anchor j),
      ∀ (U : SlowSet p) (a : Auxiliary p) (i : Option (Fin p.K))
        (j : CanonicalFastSampling.FastArm U) (B : Bool) (V : SlowSet p),
      (innovationLaw (p := p)).map (sourceOutcome rate rewards C_star C_h control0 q zc U a)
        {(Sum.inr (i,j.val,B,V) : Outcome p)} =
        (recorderPMF rate rewards C_star C_h q zc i * ENNReal.ofReal
          (CanonicalFastSampling.qGamma p rate.eta.val rate.eta.property rate.sourceCap P.anchor w
            P.anchor_pos (RecordedSlowRefresh.scoreWeight_pos Q _) hlo hhi U j)) *
          auxiliaryMass rate rewards C_star C_h q zc U i B V := by
  obtain ⟨hlo,hhi,hlaw⟩ := generated_collection_fastLaw rate rewards C_star C_h q t z htq hcall hc hen hpre
  refine ⟨hlo,hhi,?_⟩
  intro U a i j B V
  have h := sourceOutcome_clear_atom rate rewards C_star C_h control0 q ⟨z.val,hc⟩ U a hen hpre i j B V
  rw [← collectionFastPMF_apply rate _ _ _ _ U j, hlaw U j] at h
  exact h

/-- A clear enabled bottom marker still services every queue. The update
is retained whether or not its POST state detects the first overflow. -/
theorem laterCollection_enabled_bottom_service
    (z : ReferencePostInvocationNoncallGeometry.CollectionDateSource rate rewards C_star C_h q)
    (U : SlowSet p) (a : Auxiliary p)
    (hen : (ReferencePostInvocationNoncallGeometry.collectionInput rate rewards C_star C_h q z).enabled = true)
    (hpre : (ReferencePostInvocationNoncallGeometry.collectionBefore rate rewards C_star C_h q z).overflow = false)
    (hmarker : (ReferencePostInvocationNoncallGeometry.collectionInput rate rewards C_star C_h q z).recordedArm = none) :
    let S := ReferencePostInvocationNoncallGeometry.collectionBefore rate rewards C_star C_h q z
    let e := ReferencePostInvocationNoncallGeometry.laterCollectionCell rate rewards C_star C_h q z U a
    ∀ j, e.arrivals j = (true,0) ∧ e.service j = min (4 * (Q).n) (S.registers j).2 := by
  dsimp only
  intro j
  simp only [ReferencePostInvocationNoncallGeometry.laterCollectionCell,
    RecordedQueueRun.acceptedRecord, hpre, Bool.false_eq_true, ite_false, hen, ite_true,
    RecordedQueueRun.quantizedArrival, hmarker, reduceCtorEq,
    RecordedQueueRun.recordService, CappedService.service, Nat.add_zero, and_self]

/-- The physical source family copies every private coordinate and J, the
identification array, forward arrays, other rows, and other dates verbatim. -/
theorem replaceCollectionSource_frames
    (z : ReferencePostInvocationNoncallGeometry.CollectionDateSource rate rewards C_star C_h q)
    (c : Control p) :
    let zc := (replaceCollectionSource rate rewards C_star C_h control0 q z c).val
    let J := sourceCoordinatorIndex p z.val
    zc.2 = z.val.2 ∧ zc.1.1 = z.val.1.1 ∧ sourceCoordinatorIndex p zc = J ∧
      (zc.1.2 J).1 = (z.val.1.2 J).1 ∧
      (∀ k, k ≠ J → zc.1.2 k = z.val.1.2 k) ∧
      (∀ t, t ≠ q → (zc.1.2 J).2 t = (z.val.1.2 J).2 t) := by
  dsimp only [replaceCollectionSource]
  refine ⟨rfl, rfl, rfl, replaceSourceControl_forward p q z.val c, ?_, ?_⟩
  · intro k hk
    exact Function.update_of_ne hk _ _
  · intro t ht
    simp only [replaceSourceControl, Function.update_self, Function.update_of_ne ht]

/-- The auxiliary coefficient is exactly the source Bernoulli/residual
formula, with rho evaluated after the SAME marker update and at the OLD anchor. -/
theorem auxiliaryMass_eq_ofReal
    (z : ReferencePostInvocationNoncallGeometry.CollectionDateSource rate rewards C_star C_h q)
    (U : SlowSet p) (i : Option (Fin p.K)) (B : Bool) (V : SlowSet p) :
    auxiliaryMass rate rewards C_star C_h q z U i B V = ENNReal.ofReal
      (if B then (4 * p.m * rate.eta.val) *
        RecordedSlowRefresh.residualMass p Q
          (ReferencePostInvocationNoncallGeometry.collectionBefore rate rewards C_star C_h q z)
          (markerRound rate rewards C_star C_h q z i)
          (ReferencePostInvocationNoncallGeometry.collectionArguments rate rewards C_star C_h q z).1.anchor
          (ReferencePostInvocationNoncallGeometry.collectionArguments rate rewards C_star C_h q z).1.anchor_pos V
      else (1 - 4 * p.m * rate.eta.val) * (if V = U then 1 else 0)) := by
  cases B with
  | true =>
    simp only [auxiliaryMass, ite_true]
    exact (ENNReal.ofReal_mul
      (ReferenceFirstLivePostUpdateProposalLaw.physicalProposalThreshold_bounds rate).1.le).symm
  | false =>
    by_cases hv : V = U <;> simp only [auxiliaryMass, Bool.false_eq_true, ite_false, hv,
      ite_true, mul_one, mul_zero, ENNReal.ofReal_zero]

end Bandits.Support.ReferencePostInvocationCollectionNativeLaw

end
