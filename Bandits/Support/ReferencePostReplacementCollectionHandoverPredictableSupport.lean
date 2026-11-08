/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferencePostReplacementCollectionHandoverSourcePrefix
public import Bandits.Support.ReferenceCompleteDispatchTagPrefix

/-!
# Predictability of the original-source post-collection H task

The observable combines the strict dated dispatch-tag prefix with the existing
incoming LIVE/collection query. Its LIVE clock projection reruns only the
source `StartRound` test on the countable incoming clock fields.

Sources: `05_binary_transport.tex:244-289`,
`06_interruptions.tex:246-299,431-490`, and
`appendix_a_local_protocol.tex:28-79`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ReferencePostReplacementCollectionHandoverSourcePrefix
open scoped Classical

namespace Bandits.Support.ReferencePostReplacementCollectionHandoverPredictableSupport

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)

/-- The phase immediately before source date `t`, obtained by folding the
existing six-state transition over the strict dated dispatch-tag prefix. -/
def handoverPhaseBefore (t : Fin p.T) (z : SourceInput p) : HandoverPhase :=
  ((ReferenceCompleteDispatchTagPrefix.datedDispatchTags rate
      (ReferenceCompleteObservationPrefixInformation.datePrefix rate t.val
        (ReferenceCompleteNumericalBranchObservation.completeBranchObservation
          rate rewards C_star C_h z))).map Prod.snd).foldl
    (fun phase tags => handoverAdvance phase tags) .firstLive

/-- Read the actual LIVE clock result from its existing countable incoming
code. `true` means `StartRound` preserves the LIVE sentinel cutoff. -/
def handoverIncomingLiveContinuesCode (t : Fin p.T)
    (code : ReferenceActivePhysicalStepMeasurability.CoordinatorCode p rate) : Bool :=
  match code with
  | .inr (.inl (_, live)) =>
      let clock : CoordinatorPhaseClock.ClockRegisters p :=
        ⟨live.clockSigma, live.clockCutoff, live.clockBoundary, live.clockProposal⟩
      match CoordinatorPhaseClock.startRound p rate.eta.val t clock live.pending with
      | .error _ => false
      | .ok started => decide (started.clock.u = none)
  | _ => false

/-- The same LIVE clock projection applied to the original date-indexed
incoming state. Absence and non-LIVE states produce `false`. -/
def handoverIncomingLiveContinues (t : Fin p.T) (z : SourceInput p) : Bool :=
  ReferenceCollectionOutcomeMeasurability.optionalElim false
    (fun code : ReferenceActivePhysicalStepMeasurability.StateCode p rate =>
      handoverIncomingLiveContinuesCode rate t code.1)
    (ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t z)

/-- The finite/countable information available before `StartRound` at date
`t`: the folded strict tag prefix, the accepted incoming task code, and the
clock result computed from that same incoming code. -/
def handoverPreRoundObservable (t : Fin p.T) (z : SourceInput p) :=
  (handoverPhaseBefore rate rewards C_star C_h t z,
    (handoverIncomingData rate rewards C_star C_h t z,
      handoverIncomingLiveContinues rate rewards C_star C_h t z))

/-- Read whether follower `i` is requested by the current incoming H task. -/
def handoverPreRoundTask (i : Fin (p.m - 1)) :
    HandoverPhase ×
      (Option (Bool × Option (Finset (Fin (p.m - 1)))) × Bool) → Bool
  | (.replacementCollection, (some (true, none), _)) => true
  | (.handover, (some (false, some pending), true)) => decide (i ∈ pending)
  | _ => false

/-- The observable's phase component factors through the strict source prefix. -/
theorem handoverPhaseBefore_factor
    (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (z : SourceInput p) :
    handoverPhaseBefore rate rewards C_star C_h t z =
      handoverPhaseBefore rate rewards C_star C_h t
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z) := by
  unfold handoverPhaseBefore
  rw [ReferenceCompleteDispatchTagPrefix.datedDispatchTags_datePrefix_factor
    rate rewards C_star C_h control0 t.val (Nat.le_of_lt t.isLt) z]

/-- The LIVE clock projection factors through the existing incoming state. -/
theorem handoverIncomingLiveContinues_factor
    (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (z : SourceInput p) :
    handoverIncomingLiveContinues rate rewards C_star C_h t z =
      handoverIncomingLiveContinues rate rewards C_star C_h t
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z) := by
  unfold handoverIncomingLiveContinues
  rw [ReferenceSourcePrefixHistoryFiltration.incoming_factor
    rate rewards C_star C_h control0 t z]

/-- The complete pre-round observable has the actual source-prefix factor. -/
theorem handoverPreRoundObservable_factor
    (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (z : SourceInput p) :
    handoverPreRoundObservable rate rewards C_star C_h t z =
      handoverPreRoundObservable rate rewards C_star C_h t
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z) := by
  unfold handoverPreRoundObservable
  rw [handoverPhaseBefore_factor rate rewards C_star C_h control0 t z,
    handoverIncomingData_factor rate rewards C_star C_h control0 t z,
    handoverIncomingLiveContinues_factor rate rewards C_star C_h control0 t z]

/-- Borelness of the actual countable LIVE clock projection. -/
theorem handoverIncomingLiveContinuesCode_measurable (t : Fin p.T) :
    Measurable (handoverIncomingLiveContinuesCode rate t) := by
  change Measurable (Sum.elim (fun _ : Unit => false)
    (Sum.elim (fun pair : ReferenceActivePhysicalStep.Payload rate ×
        ReferenceActivePhysicalStepMeasurability.LiveDiscrete p =>
      match CoordinatorPhaseClock.startRound p rate.eta.val t
        ⟨pair.2.clockSigma, pair.2.clockCutoff, pair.2.clockBoundary,
          pair.2.clockProposal⟩ pair.2.pending with
      | .error _ => false
      | .ok started => decide (started.clock.u = none))
      (Sum.elim (fun _ : ReferenceActivePhysicalStep.Payload rate ×
          (ReferenceActivePhysicalStep.Ledger rate × Option (Fin p.T × Bool)) => false)
        (fun _ : Unit => false))))
  have hLive : Measurable (fun live : ReferenceActivePhysicalStepMeasurability.LiveDiscrete p =>
      match CoordinatorPhaseClock.startRound p rate.eta.val t
        ⟨live.clockSigma, live.clockCutoff, live.clockBoundary, live.clockProposal⟩
        live.pending with
      | .error _ => false
      | .ok started => decide (started.clock.u = none)) :=
    measurable_of_countable _
  exact measurable_const.sumElim
    ((hLive.comp measurable_snd).sumElim
      (measurable_const.sumElim measurable_const))

/-- Measurability of the LIVE clock result read from the existing incoming
state code, with the ordinary option encoding of absence. -/
theorem handoverIncomingLiveContinues_measurable
    (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T) :
    Measurable[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
      control0 (t.val + 1)]
      (handoverIncomingLiveContinues rate rewards C_star C_h t) := by
  have hcode : Measurable
      (fun code : ReferenceActivePhysicalStepMeasurability.StateCode p rate =>
        handoverIncomingLiveContinuesCode rate t code.1) :=
    (handoverIncomingLiveContinuesCode_measurable rate t).comp measurable_fst
  exact (ReferenceCollectionOutcomeMeasurability.measurable_optionalElim false
      (fun code : ReferenceActivePhysicalStepMeasurability.StateCode p rate =>
        handoverIncomingLiveContinuesCode rate t code.1) hcode).comp
    (ReferenceSourcePrefixHistoryFiltration.incoming_measurable
      rate rewards C_star C_h control0 t)

private theorem measurableSingleton_listObservation {α : Type*}
    [MeasurableSpace α] [MeasurableSingletonClass α] :
    MeasurableSingletonClass (List α) := by
  have hinj : Function.Injective
      (ReferenceActiveHorizonMeasurability.listObservationCoordinates (α := α)) := by
    intro left right h
    apply List.ext_getElem?
    intro n
    have hn := congrFun (congrArg Prod.snd h) n
    change ReferenceActiveHorizonMeasurability.listObservationAt left n =
      ReferenceActiveHorizonMeasurability.listObservationAt right n at hn
    unfold ReferenceActiveHorizonMeasurability.listObservationAt at hn
    cases hl : left[n]? <;> cases hr : right[n]? <;> simp_all
  constructor
  intro records
  have heq : ({records} : Set (List α)) =
      ReferenceActiveHorizonMeasurability.listObservationCoordinates ⁻¹'
        {ReferenceActiveHorizonMeasurability.listObservationCoordinates records} := by
    ext other
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    exact ⟨fun h => congrArg _ h, fun h => hinj h⟩
  let : MeasurableSingletonClass (Unit ⊕ α) := ⟨fun tag => by
    cases tag with
    | inl value =>
        simpa only [Set.image_singleton] using
          (measurableSet_singleton value).inl_image
    | inr value =>
        simpa only [Set.image_singleton] using
          (measurableSet_singleton value).inr_image⟩
  rw [heq]
  exact (measurableSet_singleton _).preimage
    ReferenceActiveHorizonMeasurability.measurable_listObservationCoordinates

/-- The strict dated prefix fold is Borel at the source pre-round field. -/
theorem handoverPhaseBefore_measurable
    (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T) :
    Measurable[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
      control0 (t.val + 1)]
      (handoverPhaseBefore rate rewards C_star C_h t) := by
  have htags := ReferenceCompleteDispatchTagPrefix.datedDispatchTags_datePrefix_measurable
    rate rewards C_star C_h control0 t.val (Nat.le_of_lt t.isLt)
  have hfold : Measurable
      (fun tags : List (Fin p.T × (Bool × Bool × Bool)) =>
        (tags.map Prod.snd).foldl
          (fun phase item => handoverAdvance phase item) .firstLive) := by
    let : MeasurableSingletonClass
        (List (Fin p.T × (Bool × Bool × Bool))) :=
      measurableSingleton_listObservation
    exact measurable_of_countable _
  change Measurable[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
      control0 (t.val + 1)] (fun source : SourceInput p =>
    ((ReferenceCompleteDispatchTagPrefix.datedDispatchTags rate
      (ReferenceCompleteObservationPrefixInformation.datePrefix rate t.val
        (ReferenceCompleteNumericalBranchObservation.completeBranchObservation
          rate rewards C_star C_h source))).map Prod.snd).foldl
      (fun phase item => handoverAdvance phase item) .firstLive)
  exact hfold.comp htags

/-- The whole current incoming query is Borel in the same pre-round field. -/
theorem handoverPreRoundObservable_measurable
    (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T) :
    Measurable[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
      control0 (t.val + 1)]
      (handoverPreRoundObservable rate rewards C_star C_h t) := by
  exact (handoverPhaseBefore_measurable rate rewards C_star C_h control0 t).prodMk
    ((handoverIncomingData_measurable rate rewards C_star C_h control0 t).prodMk
      (handoverIncomingLiveContinues_measurable
        rate rewards C_star C_h control0 t))

/-- The observable task test is Borel because its carrier is the existing
finite/countable phase, pending-set, and clock-code product. -/
theorem handoverPreRoundTask_measurable (i : Fin (p.m - 1)) :
    Measurable (handoverPreRoundTask (p := p) i) := by
  exact measurable_of_countable _

/-- A record at date `t` is its unique member of the actual completed suffix. -/
private theorem actualRecord_some_index
    (z : SourceInput p) (t : Fin p.T)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hrecord : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z = some record) :
    ∃ k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h).length,
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[k.val] = record ∧
        (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)[k.val].input.time = t := by
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  have hstart : s ≤ t.val := by
    by_contra hn
    have hnone := ReferenceSourcePrefixHistoryFiltration.actualRecord_eq_none_of_future_start
      rate rewards C_star C_h t z (Nat.lt_of_not_ge hn)
    rw [hnone] at hrecord
    cases hrecord
  have hlookup : R[t.val - s]? = some record := by
    unfold ReferenceSourcePrefixHistoryFiltration.actualRecord at hrecord
    rw [ite_eq_left hstart] at hrecord
    exact hrecord
  obtain ⟨hbound, hvalue⟩ := List.getElem?_eq_some_iff.mp hlookup
  let k : Fin R.length := ⟨t.val - s, hbound⟩
  have htime' : R[k.val].input.time.val = t.val := by
    have hrecordTime := ReferenceAssignmentFollowerMassSteps.complete_record_time
      rate rewards C_star C_h z
        (⟨t.val - s, hbound⟩ : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h).length)
    have hrecordTime' : R[t.val - s].input.time.val = s + (t.val - s) := by
      simpa [R, s] using hrecordTime
    calc
      R[k.val].input.time.val = R[t.val - s].input.time.val := by simp [k]
      _ = s + (t.val - s) := hrecordTime'
      _ = t.val := by omega
  refine ⟨k, hvalue, Fin.ext htime'⟩

/-- Every actual H support witness is an actual record at that same source
date. The scan characterization is used only for this source-side fact. -/
private theorem scannedHSegment_subset_local
    (phase : HandoverPhase)
    (R : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))) :
    scannedHSegment phase R ⊆ R := by
  induction R generalizing phase with
  | nil => simp only [scannedHSegment, List.Subset.refl]
  | cons record rest ih =>
      intro x hx
      simp only [scannedHSegment] at hx
      split at hx
      · rcases List.mem_cons.mp hx with rfl | htail
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem record (ih _ htail)
      · exact List.mem_cons_of_mem record (ih _ hx)

private theorem rawHTaskSupport_actualRecord_some
    (z : SourceInput p) (t : Fin p.T) (i : Fin (p.m - 1))
    (hsupport : rawHTaskSupport rate rewards C_star C_h t i z) :
    ∃ record, ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z = some record := by
  rcases (rawHTaskSupport_iff_scanned rate rewards C_star C_h z t i).mp hsupport with
    ⟨record, hmem, htime, _selected, _hselection, _hpending⟩
  have hmemSuffix : record ∈ ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h := by
    have hsubset := scannedHSegment_subset_local rate HandoverPhase.firstLive
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)
    exact hsubset hmem
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hmemSuffix
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  have htimeRecord := ReferenceAssignmentFollowerMassSteps.complete_record_time
    rate rewards C_star C_h z ⟨j, hj⟩
  have hstart : s ≤ t.val := by
    have ht := congrArg Fin.val htime
    dsimp only [R, s] at htimeRecord
    omega
  have hindex : t.val - s = j := by
    have ht := congrArg Fin.val htime
    dsimp only [R, s] at htimeRecord
    omega
  refine ⟨R[j], ?_⟩
  unfold ReferenceSourcePrefixHistoryFiltration.actualRecord
  rw [ite_eq_left hstart, hindex]
  exact List.getElem?_eq_getElem hj

/-- The fold over dated tags strictly before an actual record equals the
existing handoverAdvance fold over the corresponding chronological prefix. -/
private theorem handoverPhaseBefore_eq_recordPrefix
    (z : SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length) :
    handoverPhaseBefore rate rewards C_star C_h
        (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)[k.val].input.time z =
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h).take k.val).foldl
        (fun phase record => handoverAdvance phase (handoverRecordTags record)) .firstLive := by
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let t := R[k.val].input.time
  have hdate := ReferenceCompleteDispatchTagPrefix.datedDispatchTags_datePrefix_eq_take
    rate rewards C_star C_h t.val (Nat.le_of_lt t.isLt) z
  have hindex : t.val - ReferenceCompletePhysicalHistory.physicalStart
      rate z rewards C_star C_h = k.val := by
    have htime := ReferenceAssignmentFollowerMassSteps.complete_record_time
      rate rewards C_star C_h z k
    change t.val =
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + k.val at htime
    omega
  unfold handoverPhaseBefore
  rw [hdate, hindex]
  simp only [List.foldl_map, List.map_map, Function.comp_def,
    handoverRecordTags]

/-- On an actual collection input, the incoming birth query is exactly empty
collection pending, by the accepted collection-birth and complete-source
choice producers. -/
private theorem handoverIncomingData_birth_iff_empty
    (z : SourceInput p) (t : Fin p.T)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hrecord : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z = some record) :
    handoverIncomingData rate rewards C_star C_h t z = some (true, none) ↔
      ∃ payload' ledger' saved',
        record.input.state.coordinator = .collection payload' ledger' saved' ∧
          ledger'.pending = ∅ := by
  constructor
  · intro hdata
    unfold handoverIncomingData ReferenceSourcePrefixHistoryFiltration.incoming at hdata
    rw [hrecord] at hdata
    cases hcoord : record.input.state.coordinator with
    | first => simp [ReferenceActivePhysicalStepMeasurability.encodeState,
        ReferenceActivePhysicalStepMeasurability.encodeCoordinator,
        incomingHandoverData, hcoord] at hdata
    | live registers owned base =>
        simp [ReferenceActivePhysicalStepMeasurability.encodeState,
          ReferenceActivePhysicalStepMeasurability.encodeCoordinator,
          incomingHandoverData, hcoord] at hdata
    | collection payload ledger saved =>
        simp [ReferenceActivePhysicalStepMeasurability.encodeState,
          ReferenceActivePhysicalStepMeasurability.encodeCoordinator,
          incomingHandoverData, hcoord, decide_eq_true_eq] at hdata
        exact ⟨payload, ledger, saved, rfl, hdata⟩
    | dagger =>
        simp [ReferenceActivePhysicalStepMeasurability.encodeState,
          ReferenceActivePhysicalStepMeasurability.encodeCoordinator,
          incomingHandoverData, hcoord] at hdata
  · rintro ⟨payload, ledger, saved, hstate, hempty⟩
    unfold handoverIncomingData ReferenceSourcePrefixHistoryFiltration.incoming
    rw [hrecord]
    simp [ReferenceActivePhysicalStepMeasurability.encodeState,
      ReferenceActivePhysicalStepMeasurability.encodeCoordinator,
      incomingHandoverData, hstate, hempty]

/-- The current incoming LIVE code retains exactly the pending set tested by
the actual LIVE dispatcher. -/
private theorem handoverIncomingData_live_eq_pending
    (z : SourceInput p) (t : Fin p.T)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hrecord : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z = some record)
    (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
    (base : Fin (p.m - 1) → ℕ)
    (hstate : record.input.state.coordinator = .live registers owned base) :
    handoverIncomingData rate rewards C_star C_h t z =
      some (false, some registers.pendingAtChoice) := by
  unfold handoverIncomingData ReferenceSourcePrefixHistoryFiltration.incoming
  rw [hrecord]
  simp [ReferenceActivePhysicalStepMeasurability.encodeState,
    ReferenceActivePhysicalStepMeasurability.encodeCoordinator,
    ReferenceActivePhysicalStepMeasurability.encodeLive,
    incomingHandoverData, hstate]
  rfl

/-- A continuing output is sourced by the actual incoming LIVE phase. This is
read from the accepted complete dispatch-tag decoder. -/
private theorem continuingChosen_input_live
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hcontinuing :
      ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen record = true) :
    ∃ registers owned base,
      record.input.state.coordinator = .live registers owned base := by
  have htag := ReferenceCompleteDispatchTagPrefix.dispatchTagCode_eq_record rate record
  have hthird := congrArg (fun tags : Bool × Bool × Bool => tags.2.2) htag
  let code := ReferenceActiveHorizonMeasurability.roundRecordCode record
  cases hcoord : record.input.state.coordinator with
  | first | collection _ _ _ | dagger =>
      have hdecoded :
          (ReferenceCompleteDispatchTagPrefix.dispatchTagCode rate code).2.2 = false := by
        cases hselected :
            (ReferenceActiveStepCompositionMeasurability.wholeStepCode record.input).1.1 <;>
          simp [ReferenceCompleteDispatchTagPrefix.dispatchTagCode,
            ReferenceCompleteDispatchTagPrefix.selectedStartCode,
            ReferenceCompleteDispatchTagPrefix.dispatchTagFrom,
            ReferenceCompleteDispatchTagPrefix.coordinatorPhaseCode,
            ReferenceActiveHorizonMeasurability.roundRecordCode,
            ReferenceActivePhysicalStepMeasurability.encodeState,
            ReferenceActivePhysicalStepMeasurability.encodeCoordinator,
            code, hcoord, hselected]
      have hfalse : ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen record = false := by
        simpa [code] using hthird.symm.trans hdecoded
      rw [hfalse] at hcontinuing
      cases hcontinuing
  | live registers owned base => exact ⟨registers, owned, base, rfl⟩

/-- The clock projection agrees with the actual cutoff test on every
complete-source LIVE record. The successful StartRound, grid-boundary, and
triggered-cutoff cases come from the complete live dispatcher producer. -/
private theorem handoverIncomingLiveContinues_eq_notCutoff
    (z : SourceInput p) (t : Fin p.T)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (hrecord : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z =
        some (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)[k.val])
    (htime : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[k.val].input.time = t)
    (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
    (base : Fin (p.m - 1) → ℕ)
    (hstate : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[k.val].input.state.coordinator =
        .live registers owned base) :
    handoverIncomingLiveContinues rate rewards C_star C_h t z =
      decide (ReferenceCollectionPhaseHistory.cutoffChosen
        (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)[k.val].input = false) := by
  let record := (ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate z rewards C_star C_h)[k.val]
  have htimeRecord : record.input.time = t := by
    simpa [record] using htime
  let current := ReferenceActivePhysicalStep.liveInput record.input registers owned base
  have hcomplete := ReferenceCompleteLiveChoiceDomains.complete_live_dispatch_choice_exists
    rate rewards C_star C_h z k registers owned base hstate
  dsimp only at hcomplete
  obtain ⟨hprep, hbranches⟩ := hcomplete
  have hprojection (dispatched : CoordinatorStartRoundCutoffDispatch.Output
      current.registers current.ownedRegisters current.followerBaseScore)
      (hstart : CoordinatorPhaseClock.startRound p rate.eta.val t
        registers.priorClock registers.pendingAtChoice = .ok dispatched.startResult) :
      handoverIncomingLiveContinues rate rewards C_star C_h t z =
        decide (dispatched.startResult.clock.u = none) := by
    have hcode : handoverIncomingLiveContinuesCode rate t
        (ReferenceActivePhysicalStepMeasurability.encodeCoordinator
          record.input.state.coordinator) =
          decide (dispatched.startResult.clock.u = none) := by
      rw [hstate]
      simp only [ReferenceActivePhysicalStepMeasurability.encodeCoordinator,
        ReferenceActivePhysicalStepMeasurability.encodeLive,
        handoverIncomingLiveContinuesCode]
      have hclock :
          (⟨registers.priorClock.sigma, registers.priorClock.u,
            registers.priorClock.g, registers.priorClock.lastProposal⟩ :
              CoordinatorPhaseClock.ClockRegisters p) = registers.priorClock := by
        cases registers.priorClock
        rfl
      rw [hclock, hstart]
    unfold handoverIncomingLiveContinues
    unfold ReferenceSourcePrefixHistoryFiltration.incoming
    rw [hrecord]
    simp only [Option.map_some,
      ReferenceActivePhysicalStepMeasurability.encodeState]
    exact hcode
  cases hdispatch : CoordinatorRoundDispatch.dispatchLive current with
  | continuingChosen dispatched hstart continuation selection =>
      have hbranches' := hbranches
      rw [hdispatch] at hbranches'
      obtain ⟨_hframe, hu, _hchoice, _hgrid, _harm, _hselected⟩ := hbranches'
      have hstart' : CoordinatorPhaseClock.startRound p rate.eta.val t
          registers.priorClock registers.pendingAtChoice = .ok dispatched.startResult := by
        simpa [current, ReferenceActivePhysicalStep.liveInput,
          ReferenceActivePhysicalStep.liveRegistersAt,
          CoordinatorLiveChoiceRecorderStep.Registers.clockPending_eq,
          htimeRecord] using hstart
      have hcut : ReferenceCollectionPhaseHistory.cutoffChosen record.input = false := by
        unfold ReferenceCollectionPhaseHistory.cutoffChosen
        rw [hprep, hdispatch]
      rw [hprojection dispatched hstart', hu, hcut]
      rfl
  | cutoffChosen dispatched hstart ledger hinit hledger hdomains hclock hpending hnoStart selection =>
      have hbranches' := hbranches
      rw [hdispatch] at hbranches'
      obtain ⟨_hcommand, hbranchClock, _hpending, _hassignment, _hinit,
        _hledger, _hchoice, _hgrid, _harm, _hselected⟩ := hbranches'
      have hstart' : CoordinatorPhaseClock.startRound p rate.eta.val t
          registers.priorClock registers.pendingAtChoice = .ok dispatched.startResult := by
        simpa [current, ReferenceActivePhysicalStep.liveInput,
          ReferenceActivePhysicalStep.liveRegistersAt,
          CoordinatorLiveChoiceRecorderStep.Registers.clockPending_eq,
          htimeRecord] using hstart
      have hclock' : dispatched.startResult.clock =
          { registers.priorClock with u := some t } := by
        simpa [current, record, ReferenceActivePhysicalStep.liveInput,
          ReferenceActivePhysicalStep.liveRegistersAt, htimeRecord] using hbranchClock
      have hu : dispatched.startResult.clock.u = some t := by
        have h := congrArg (fun clock : CoordinatorPhaseClock.ClockRegisters p => clock.u)
          hclock'
        exact h
      have hcut : ReferenceCollectionPhaseHistory.cutoffChosen record.input = true := by
        unfold ReferenceCollectionPhaseHistory.cutoffChosen
        rw [hprep, hdispatch]
      rw [hprojection dispatched hstart', hu, hcut]
      rfl
  | clockFailure _ => rw [hdispatch] at hbranches; exact hbranches.elim
  | initializerFailure _ _ _ => rw [hdispatch] at hbranches; exact hbranches.elim
  | localFailure _ _ _ => rw [hdispatch] at hbranches; exact hbranches.elim

/-- The raw H support at an arbitrary original source date is exactly the
current incoming request after the strict dated tag-prefix fold. -/
theorem rawHTaskSupport_iff_handoverPreRoundTask
    (z : SourceInput p) (t : Fin p.T) (i : Fin (p.m - 1)) :
    rawHTaskSupport rate rewards C_star C_h t i z ↔
      handoverPreRoundTask i (handoverPreRoundObservable
        rate rewards C_star C_h t z) = true := by
  by_cases hactual : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z = none
  · have hnotSupport : ¬ rawHTaskSupport rate rewards C_star C_h t i z := by
      intro hsupport
      obtain ⟨record, hrecord⟩ := rawHTaskSupport_actualRecord_some
        rate rewards C_star C_h z t i hsupport
      rw [hactual] at hrecord
      cases hrecord
    constructor
    · exact False.elim ∘ hnotSupport
    · intro hquery
      have hfalse : handoverPreRoundTask i (handoverPreRoundObservable
          rate rewards C_star C_h t z) = false := by
        simp [handoverPreRoundTask, handoverPreRoundObservable,
          handoverIncomingData, handoverIncomingLiveContinues,
          ReferenceSourcePrefixHistoryFiltration.incoming, hactual]
      rw [hfalse] at hquery
      cases hquery
  · cases hrecord? : ReferenceSourcePrefixHistoryFiltration.actualRecord
        rate rewards C_star C_h t z with
    | none => exact False.elim (hactual hrecord?)
    | some record =>
      obtain ⟨k, hget, htime⟩ := actualRecord_some_index
        rate rewards C_star C_h z t record hrecord?
      let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h
      have hrecord : ReferenceSourcePrefixHistoryFiltration.actualRecord
          rate rewards C_star C_h t z = some R[k.val] := by
        rw [hget]
        exact hrecord?
      have htime' : R[k.val].input.time = t := by
        exact htime
      have hstrict := rawHTaskSupport_iff_strictPrefix_choice
        rate rewards C_star C_h z k i
      have hphaseFold := handoverPhaseBefore_eq_recordPrefix
        rate rewards C_star C_h z k
      have hraw : rawHTaskSupport rate rewards C_star C_h t i z ↔
          handoverEmit (handoverPhaseBefore rate rewards C_star C_h t z)
            (handoverRecordTags R[k.val]) = true ∧
          ∃ selected : ReferenceActivePhysicalStep.Selection R[k.val].input,
            R[k.val].output.preparation.coordinator.selection = some selected ∧
            i ∈ selected.view.pendingAtChoice := by
        simpa only [R, htime', ← hphaseFold] using hstrict
      cases hphase : handoverPhaseBefore rate rewards C_star C_h t z with
      | firstLive | firstCollection | replacementLive | closed =>
          rw [hphase] at hraw
          rw [hraw]
          simp [handoverPreRoundObservable, hphase, handoverPreRoundTask,
            handoverEmit]
      | replacementCollection =>
          rw [hphase] at hraw
          rw [hraw]
          have hbirth := actual_birth_task_iff_incoming_empty
            rate rewards C_star C_h z k i
          have hdata := handoverIncomingData_birth_iff_empty
            rate rewards C_star C_h z t R[k.val] hrecord
          have hsource :
              (handoverEmit .replacementCollection (handoverRecordTags R[k.val]) = true ∧
                ∃ selected : ReferenceActivePhysicalStep.Selection R[k.val].input,
                  R[k.val].output.preparation.coordinator.selection = some selected ∧
                    i ∈ selected.view.pendingAtChoice) ↔
              handoverIncomingData rate rewards C_star C_h t z = some (true, none) := by
            simpa only [R, handoverEmit, handoverRecordTags] using hbirth.trans hdata.symm
          have hquery :
              handoverPreRoundTask i (handoverPreRoundObservable
                rate rewards C_star C_h t z) = true ↔
                handoverIncomingData rate rewards C_star C_h t z = some (true, none) := by
            cases hcode : handoverIncomingData rate rewards C_star C_h t z with
            | none => simp [handoverPreRoundObservable, hphase, handoverPreRoundTask, hcode]
            | some code =>
                cases code with
                | mk birth pending =>
                    cases birth <;> cases pending <;>
                      simp [handoverPreRoundObservable, hphase, handoverPreRoundTask, hcode]
          exact hsource.trans hquery.symm
      | handover =>
          rw [hphase] at hraw
          rw [hraw]
          cases hcoord : R[k.val].input.state.coordinator with
          | live registers owned base =>
              have hstate : R[k.val].input.state.coordinator =
                  .live registers owned base := hcoord
              have hdata := handoverIncomingData_live_eq_pending
                rate rewards C_star C_h z t R[k.val] hrecord registers owned base hstate
              have hlive := actual_live_task_iff_incoming_pending
                rate rewards C_star C_h z k registers owned base hstate i
              have hcutoff := handoverIncomingLiveContinues_eq_notCutoff
                rate rewards C_star C_h z t k hrecord htime' registers owned base hstate
              have hsource :
                  (handoverEmit .handover (handoverRecordTags R[k.val]) = true ∧
                    ∃ selected : ReferenceActivePhysicalStep.Selection R[k.val].input,
                      R[k.val].output.preparation.coordinator.selection = some selected ∧
                        i ∈ selected.view.pendingAtChoice) ↔
                  ReferenceCollectionPhaseHistory.cutoffChosen R[k.val].input = false ∧
                    i ∈ registers.pendingAtChoice := by
                constructor
                · rintro ⟨hemit, selected, hselection, hi⟩
                  apply hlive.mp
                  refine ⟨?_, selected, hselection, hi⟩
                  simpa [handoverEmit, handoverRecordTags] using hemit
                · rintro ⟨hcutoff, hi⟩
                  rcases hlive.mpr ⟨hcutoff, hi⟩ with
                    ⟨hcontinue, selected, hselection, hi'⟩
                  refine ⟨?_, selected, hselection, hi'⟩
                  simpa [handoverEmit, handoverRecordTags] using hcontinue
              have hquery :
                  handoverPreRoundTask i (handoverPreRoundObservable
                    rate rewards C_star C_h t z) = true ↔
                    ReferenceCollectionPhaseHistory.cutoffChosen R[k.val].input = false ∧
                      i ∈ registers.pendingAtChoice := by
                cases hcut : ReferenceCollectionPhaseHistory.cutoffChosen
                    R[k.val].input <;>
                  simp [handoverPreRoundObservable, hphase, handoverPreRoundTask,
                    hdata, hcutoff, R, hcut]
                all_goals exact Iff.rfl
              exact hsource.trans hquery.symm
          | first =>
              have hnot :
                  ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen
                    R[k.val] = false := by
                cases htest : ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen
                    R[k.val] with
                | false => rfl
                | true =>
                    obtain ⟨registers, owned, base, hlive⟩ :=
                      continuingChosen_input_live rate R[k.val] htest
                    rw [hcoord] at hlive
                    cases hlive
              have hquery : handoverPreRoundTask i (handoverPreRoundObservable
                  rate rewards C_star C_h t z) = false := by
                simp [handoverPreRoundObservable, hphase, handoverPreRoundTask,
                  handoverIncomingData, handoverIncomingLiveContinues,
                  incomingHandoverData,
                  handoverIncomingLiveContinuesCode,
                  ReferenceSourcePrefixHistoryFiltration.incoming, hrecord, hcoord,
                  ReferenceActivePhysicalStepMeasurability.encodeState,
                  ReferenceActivePhysicalStepMeasurability.encodeCoordinator]
              constructor
              · intro htask
                have hcont := htask.1
                simp [handoverEmit, handoverRecordTags, hnot] at hcont
              · intro hresult
                rw [hquery] at hresult
                cases hresult
          | collection payload ledger saved =>
              have hnot :
                  ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen
                    R[k.val] = false := by
                cases htest : ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen
                    R[k.val] with
                | false => rfl
                | true =>
                    obtain ⟨registers, owned, base, hlive⟩ :=
                      continuingChosen_input_live rate R[k.val] htest
                    rw [hcoord] at hlive
                    cases hlive
              have hquery : handoverPreRoundTask i (handoverPreRoundObservable
                  rate rewards C_star C_h t z) = false := by
                simp [handoverPreRoundObservable, hphase, handoverPreRoundTask,
                  handoverIncomingData, handoverIncomingLiveContinues,
                  incomingHandoverData,
                  handoverIncomingLiveContinuesCode,
                  ReferenceSourcePrefixHistoryFiltration.incoming, hrecord, hcoord,
                  ReferenceActivePhysicalStepMeasurability.encodeState,
                  ReferenceActivePhysicalStepMeasurability.encodeCoordinator]
              constructor
              · intro htask
                have hcont := htask.1
                simp [handoverEmit, handoverRecordTags, hnot] at hcont
              · intro hresult
                rw [hquery] at hresult
                cases hresult
          | dagger =>
              have hnot :
                  ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen
                    R[k.val] = false := by
                cases htest : ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen
                    R[k.val] with
                | false => rfl
                | true =>
                    obtain ⟨registers, owned, base, hlive⟩ :=
                      continuingChosen_input_live rate R[k.val] htest
                    rw [hcoord] at hlive
                    cases hlive
              have hquery : handoverPreRoundTask i (handoverPreRoundObservable
                  rate rewards C_star C_h t z) = false := by
                simp [handoverPreRoundObservable, hphase, handoverPreRoundTask,
                  handoverIncomingData, handoverIncomingLiveContinues,
                  incomingHandoverData,
                  handoverIncomingLiveContinuesCode,
                  ReferenceSourcePrefixHistoryFiltration.incoming, hrecord, hcoord,
                  ReferenceActivePhysicalStepMeasurability.encodeState,
                  ReferenceActivePhysicalStepMeasurability.encodeCoordinator]
              constructor
              · intro htask
                have hcont := htask.1
                simp [handoverEmit, handoverRecordTags, hnot] at hcont
              · intro hresult
                rw [hquery] at hresult
                cases hresult

/-- The exact raw support is invariant under replacing source controls from
date `t` onward. -/
theorem rawHTaskSupport_factor
    (control0 : ContinuousLearningRows.TimeControl p)
    (z : SourceInput p) (t : Fin p.T) (i : Fin (p.m - 1)) :
    rawHTaskSupport rate rewards C_star C_h t i z =
      rawHTaskSupport rate rewards C_star C_h t i
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z) := by
  apply propext
  rw [rawHTaskSupport_iff_handoverPreRoundTask rate rewards C_star C_h z t i,
    rawHTaskSupport_iff_handoverPreRoundTask rate rewards C_star C_h
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z) t i,
    handoverPreRoundObservable_factor rate rewards C_star C_h control0 t z]

/-- The pre-round H support event is Borel in the original source-prefix
filtration. -/
theorem rawHTaskSupport_measurableSet
    (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (i : Fin (p.m - 1)) :
    MeasurableSet[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
      control0 (t.val + 1)]
      {z : SourceInput p | rawHTaskSupport rate rewards C_star C_h t i z} := by
  have hevent :
      {z : SourceInput p | rawHTaskSupport rate rewards C_star C_h t i z} =
        {z | handoverPreRoundTask i
          (handoverPreRoundObservable rate rewards C_star C_h t z) = true} := by
    ext z
    exact rawHTaskSupport_iff_handoverPreRoundTask rate rewards C_star C_h z t i
  rw [hevent]
  exact measurableSet_preimage
    ((handoverPreRoundTask_measurable (p := p) i).comp
      (handoverPreRoundObservable_measurable
        rate rewards C_star C_h control0 t))
    (measurableSet_singleton true)

/-- Intersecting raw H support with the two existing same-date diagnostic
gates preserves source-prefix Borel measurability. -/
theorem diagnosticHTaskSupport_measurableSet
    (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (i : Fin (p.m - 1)) :
    MeasurableSet[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
      control0 (t.val + 1)]
      (diagnosticHTaskSupport rate rewards C_star C_h t i) := by
  change MeasurableSet[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
      control0 (t.val + 1)]
      {z : SourceInput p | rawHTaskSupport rate rewards C_star C_h t i z ∧
        ReferenceFirstCollectionInclusiveDecoderStop.decoderDateKeptAt
          rate rewards C_star C_h z t ∧
        z ∈ ReferenceFirstCollectionCurrentRetainedGate.H rate rewards C_star C_h t}
  exact (rawHTaskSupport_measurableSet
      rate rewards C_star C_h control0 t i).inter
    (diagnosticGates_measurable rate rewards C_star C_h control0 t)

/-- Literal stopped source charge implies membership in the existing
same-date diagnostic envelope, using the accepted one-way domination only. -/
theorem literalStoppedHTaskSupport_mem_diagnostic
    (t : Fin p.T) (i : Fin (p.m - 1)) (z : SourceInput p)
    (h : literalStoppedHTaskSupport rate rewards C_star C_h t i z) :
    z ∈ diagnosticHTaskSupport rate rewards C_star C_h t i :=
  ReferencePostReplacementCollectionHandoverSourcePrefix.literalStoppedHTaskSupport_mem_diagnostic
    rate rewards C_star C_h t i z h

end Bandits.Support.ReferencePostReplacementCollectionHandoverPredictableSupport

end
