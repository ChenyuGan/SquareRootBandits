/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionCorrectedAssignedOverflowCover
public import Bandits.Support.ReferenceCompleteLaterCollectionCalendarReadout

import Mathlib.Tactic

/-!
# Causal readout of the first corrected collection

This module exposes the actual incoming collection branch at a post-birth
source date. The gate retains the corrected first-call localization and reads
the coordinator tag from the lossless incoming-state code. It does not inspect
the current action, recorder result, future UP acceptance, or segment endpoint.
The same actual payload identifies the first post-birth collection and its
dated numerical cell. Every complete current-control replacement produces the
literal continuous collection map, including present cells with no marker.

Sources: ZIP4 `06_interruptions.tex:40-100,192-233,246-299`,
`appendix_a_local_protocol.tex:28-64`, and
`04_slow_fast_learner.tex:157-187,256-290`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support
open Bandits.Support.ConstructorDimensions
open BootstrapPrivateRoundStreams (SourceInput)
open ContinuousLearningRows (TimeControl)
open ReferenceSourcePrefixHistoryFiltration
  (actualRecord incoming sourcePrefix sourcePrefixFiltration)
open ReferenceFixedTimeSourceControlCoupling (replaceSourceControl)
open scoped Classical

open ReferenceActivePhysicalStep ReferenceActivePhysicalHorizon
open ReferenceAssignmentPayloadPersistence ReferenceAssignmentPayloadChronology
open ReferenceCollectionSegmentExtraction

namespace Bandits.Support.ReferenceFirstCorrectedCollectionCausalReadout

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ)

local notation "Payload" => ReferenceActivePhysicalStep.Payload rate
local notation "Ledger" => ReferenceActivePhysicalStep.Ledger rate
local notation "Record" => ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)
local notation "StateCode" => ReferenceActivePhysicalStepMeasurability.StateCode p rate

local instance optionMeasurableSpace {α : Type*} [MeasurableSpace α] :
    MeasurableSpace (Option α) := LaterAssignmentStartMeasurability.optionMeasurableSpace

private theorem measurableSet_option_singleton_local {α : Type*}
    [MeasurableSpace α] [MeasurableSingletonClass α] (a : Option α) :
    MeasurableSet[LaterAssignmentStartMeasurability.optionMeasurableSpace] {a} := by
  let e := Equiv.optionEquivSumPUnit α
  have he : @Measurable (Option α) (α ⊕ PUnit)
      LaterAssignmentStartMeasurability.optionMeasurableSpace inferInstance e := comap_measurable _
  have hset : ({a} : Set (Option α)) = e ⁻¹' {e a} := by
    ext x
    exact ⟨fun h => congrArg e h, fun h => e.injective h⟩
  rw [hset]
  apply he
  cases h : e a with
  | inl value => simpa only [Set.image_singleton] using
      (measurableSet_singleton value).inl_image (β := PUnit)
  | inr value => simpa only [Set.image_singleton] using
      (measurableSet_singleton value).inr_image (α := α)

local instance : MeasurableSingletonClass (Option Bool) :=
  ⟨fun a => measurableSet_option_singleton_local a⟩

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

/-- The literal incoming source-state test for a continuing collection owned
by the original first assignment. The state is the `incoming` code of the
actual source record at the queried date. -/
def incomingCollectionTag (t : Fin p.T) (code : StateCode) : Bool :=
  match code.1 with
  | .inr (.inr (.inl (payload, (ledger, _saved)))) =>
      decide (payload.sigma = t ∧ ledger.pending.Nonempty)
  | _ => false

/-- The current incoming collection selector, retaining absence separately
from a present collection branch with an empty pending set. -/
def incomingCollectionTag? (t q : Fin p.T) (z : SourceInput p) : Option Bool :=
  (incoming rate rewards C_star C_h q z).map (incomingCollectionTag (rate := rate) t)

/-- The causal gate is the accepted first corrected source cell together with
the actual incoming `.collection P ledger saved` branch, with `P.sigma = t`
and literal nonempty `ledger.pending`. -/
def firstCollectionCausalGate (u t q : Fin p.T) (z : SourceInput p) : Prop :=
  z ∈ ReferenceFirstCollectionCorrectedSliceNumericalPrefix.correctedCell
      rate rewards C_star C_h u t ∧
    incomingCollectionTag? rate rewards C_star C_h t q z = some true

/-- The incoming code selector is precisely the actual state constructor,
including its original payload, ledger and saved proposal. -/
theorem incomingCollectionTag_spec (t q : Fin p.T) (z : SourceInput p) :
    incomingCollectionTag? rate rewards C_star C_h t q z = some true ↔
      ∃ (record : Record) (payload : Payload) (ledger : Ledger)
        (saved : Option (Fin p.T × Bool)),
        actualRecord rate rewards C_star C_h q z = some record ∧
        record.input.state.coordinator = .collection payload ledger saved ∧
        payload.sigma = t ∧ ledger.pending.Nonempty := by
  classical
  unfold incomingCollectionTag? incoming
  cases actualRecord rate rewards C_star C_h q z with
  | none => simp
  | some record =>
      cases hcoord : record.input.state.coordinator <;>
        simp [hcoord, incomingCollectionTag, ReferenceActivePhysicalStepMeasurability.encodeState,
          ReferenceActivePhysicalStepMeasurability.encodeCoordinator]

/-- On the causal gate, the selector's witness is the source's actual incoming
record and its matched collection payload and ledger. -/
theorem firstCollectionCausalGate_actualIncoming
    (u t q : Fin p.T) (z : SourceInput p)
    (hgate : firstCollectionCausalGate rate rewards C_star C_h u t q z) :
    z ∈ ReferenceFirstCollectionCorrectedSliceNumericalPrefix.correctedCell
        rate rewards C_star C_h u t ∧
      ∃ (record : Record) (payload : Payload) (ledger : Ledger)
        (saved : Option (Fin p.T × Bool)),
        actualRecord rate rewards C_star C_h q z = some record ∧
        record.input.state.coordinator = .collection payload ledger saved ∧
        payload.sigma = t ∧ ledger.pending.Nonempty := by
  exact ⟨hgate.1, (incomingCollectionTag_spec rate rewards C_star C_h t q z).mp hgate.2⟩

/-- The source-prefix filtration sees the incoming collection selector on
the pre-choice field. -/
theorem incomingCollectionTag_measurable (control0 : TimeControl p) (t q : Fin p.T) :
    Measurable[sourcePrefixFiltration control0 (q.val + 1)]
      (incomingCollectionTag? rate rewards C_star C_h t q) := by
  let tagMeasurable : Measurable (incomingCollectionTag (rate := rate) t) := by
    have hobs : Measurable (fun payload : Payload =>
        LaterAssignmentStartMeasurability.payloadObservation payload) :=
      comap_measurable _
    have hsigma : Measurable (fun payload : Payload => payload.sigma) := by
      have h :=
        (measurable_fst.comp (measurable_snd.comp hobs))
      exact h
    have hsigmaEq : Measurable (fun payload : Payload => decide (payload.sigma = t)) :=
      (measurable_of_countable (fun s : Fin p.T => decide (s = t))).comp hsigma
    have hpending : Measurable (fun ledger : Ledger => decide ledger.pending.Nonempty) :=
      measurable_of_countable _
    have hpair : Measurable (fun x : Payload × (Ledger × Option (Fin p.T × Bool)) =>
        decide (x.1.sigma = t ∧ x.2.1.pending.Nonempty)) := by
      have hleft : Measurable (fun x : Payload × (Ledger × Option (Fin p.T × Bool)) =>
          decide (x.1.sigma = t)) := hsigmaEq.comp measurable_fst
      have hright : Measurable (fun x : Payload × (Ledger × Option (Fin p.T × Bool)) =>
          decide x.2.1.pending.Nonempty) := hpending.comp (measurable_fst.comp measurable_snd)
      have hboth : Measurable (fun b : Bool × Bool => decide (b.1 = true ∧ b.2 = true)) :=
        measurable_of_countable _
      convert hboth.comp (hleft.prodMk hright) using 1
      funext x
      simp
    have htail : Measurable (fun z : Sum
        (Payload × (Ledger × Option (Fin p.T × Bool))) Unit =>
          Sum.elim
            (fun x : Payload × (Ledger × Option (Fin p.T × Bool)) =>
              decide (x.1.sigma = t ∧ x.2.1.pending.Nonempty))
            (fun _ : Unit => false) z) :=
      Measurable.sumElim hpair measurable_const
    have hmiddle : Measurable (fun z : Sum
        (Payload × ReferenceActivePhysicalStepMeasurability.LiveDiscrete p)
        (Sum (Payload × (Ledger × Option (Fin p.T × Bool))) Unit) =>
          Sum.elim (fun _ : Payload × ReferenceActivePhysicalStepMeasurability.LiveDiscrete p => false)
            (fun z => Sum.elim
              (fun x : Payload × (Ledger × Option (Fin p.T × Bool)) =>
                decide (x.1.sigma = t ∧ x.2.1.pending.Nonempty))
              (fun _ : Unit => false) z) z) :=
      Measurable.sumElim measurable_const htail
    let codeTag : ReferenceActivePhysicalStepMeasurability.CoordinatorCode p rate → Bool :=
      fun c => Sum.elim (fun _ : Unit => false)
        (fun z => Sum.elim
          (fun _ : Payload × ReferenceActivePhysicalStepMeasurability.LiveDiscrete p => false)
          (fun z => Sum.elim
            (fun x : Payload × (Ledger × Option (Fin p.T × Bool)) =>
              decide (x.1.sigma = t ∧ x.2.1.pending.Nonempty))
            (fun _ : Unit => false) z) z) c
    have hcoord : Measurable codeTag := by
      dsimp [codeTag]
      exact Measurable.sumElim measurable_const hmiddle
    have htagEq : incomingCollectionTag (rate := rate) t =
        fun code : StateCode => codeTag code.1 := by
      funext code
      rcases code with ⟨coord, _⟩
      cases coord with
      | inl _ => rfl
      | inr rest =>
          cases rest with
          | inl _ => rfl
          | inr tail =>
              cases tail with
              | inl _ => rfl
              | inr _ => rfl
    rw [htagEq]
    exact hcoord.comp measurable_fst
  let : MeasurableSpace (SourceInput p) :=
    sourcePrefixFiltration control0 (q.val + 1)
  have h : Measurable (fun z : SourceInput p =>
      (incoming rate rewards C_star C_h q z).map (incomingCollectionTag (rate := rate) t)) :=
    measurable_option_map (incoming rate rewards C_star C_h q)
      (ReferenceSourcePrefixHistoryFiltration.incoming_measurable
        rate rewards C_star C_h control0 q)
      (incomingCollectionTag (rate := rate) t) tagMeasurable
  convert h using 1
  funext z
  rfl

/-- The causal gate is measurable on the successor field, once the queried
date is strictly after the corrected birth round. -/
theorem firstCollectionCausalGate_measurable_of_postBirth
    (control0 : TimeControl p) (u t q : Fin p.T)
    (hfuture : t.val + 1 < q.val) :
    MeasurableSet[sourcePrefixFiltration control0 (q.val + 1)]
      (firstCollectionCausalGate rate rewards C_star C_h u t q) := by
  exact
    (ReferenceFirstCollectionCorrectedFutureRecordingView.correctedCell_prior_measurable
      rate rewards C_star C_h control0 u t q hfuture).inter
    ((incomingCollectionTag_measurable rate rewards C_star C_h control0 t q)
      (MeasurableSet.singleton (some true)))

/-- Incoming source replacement at the current date preserves the exact
coordinator payload, ledger and saved proposal. -/
theorem incomingCollectionTag_replaceSourceControl (control0 : TimeControl p)
    (t q : Fin p.T) (z : SourceInput p) (fresh : TimeControl p) :
    incomingCollectionTag? rate rewards C_star C_h t q
      (replaceSourceControl p q z fresh) = incomingCollectionTag? rate rewards C_star C_h t q z := by
  unfold incomingCollectionTag?
  rw [ReferenceSourcePrefixHistoryFiltration.incoming_factor
      rate rewards C_star C_h control0 q,
    ReferenceFirstCollectionOldRecorderFoundation.sourcePrefix_replaceCurrent
      control0 q q le_rfl z fresh,
    ← ReferenceSourcePrefixHistoryFiltration.incoming_factor
      rate rewards C_star C_h control0 q z]

/-- Complete current-control replacement preserves the full incoming state
code, including every payload, ledger, and saved-proposal coordinate. -/
theorem incomingState_replaceSourceControl (control0 : TimeControl p)
    (q : Fin p.T) (z : SourceInput p) (fresh : TimeControl p) :
    incoming rate rewards C_star C_h q (replaceSourceControl p q z fresh) =
      incoming rate rewards C_star C_h q z := by
  rw [ReferenceSourcePrefixHistoryFiltration.incoming_factor
      rate rewards C_star C_h control0 q,
    ReferenceFirstCollectionOldRecorderFoundation.sourcePrefix_replaceCurrent
      control0 q q le_rfl z fresh,
    ← ReferenceSourcePrefixHistoryFiltration.incoming_factor
      rate rewards C_star C_h control0 q z]

/-- Strict-past corrected localization and the incoming selector together
factor through the original source prefix at the queried date. -/
theorem firstCollectionCausalGate_factor_of_postBirth
    (control0 : TimeControl p) (u t q : Fin p.T)
    (hfuture : t.val + 1 < q.val) (z : SourceInput p) :
    firstCollectionCausalGate rate rewards C_star C_h u t q z ↔
      firstCollectionCausalGate rate rewards C_star C_h u t q
        (sourcePrefix control0 q.val z) := by
  have hcorrected :
      z ∈ ReferenceFirstCollectionCorrectedSliceNumericalPrefix.correctedCell
          rate rewards C_star C_h u t ↔
        sourcePrefix control0 q.val z ∈
          ReferenceFirstCollectionCorrectedSliceNumericalPrefix.correctedCell
            rate rewards C_star C_h u t := by
    have hm := ReferenceFirstCollectionCorrectedFutureRecordingView.correctedCell_prior_measurable
      rate rewards C_star C_h control0 u t q hfuture
    rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration_succ,
      MeasurableSpace.measurableSet_comap] at hm
    obtain ⟨A, _hA, hA⟩ := hm
    rw [← hA]
    simp only [Set.mem_preimage]
    rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefix_sourcePrefix
      control0 q.val q.val le_rfl z]
  have htag : incomingCollectionTag? rate rewards C_star C_h t q z =
      incomingCollectionTag? rate rewards C_star C_h t q
        (sourcePrefix control0 q.val z) := by
    unfold incomingCollectionTag?
    exact congrArg (Option.map (incomingCollectionTag (rate := rate) t))
      (ReferenceSourcePrefixHistoryFiltration.incoming_factor
        rate rewards C_star C_h control0 q z)
  simp only [firstCollectionCausalGate, hcorrected, htag]

/-- Every complete replacement of the queried source control preserves the
causal gate on the post-birth domain. -/
theorem firstCollectionCausalGate_replaceSourceControl_of_postBirth
    (control0 : TimeControl p) (u t q : Fin p.T)
    (hfuture : t.val + 1 < q.val) (z : SourceInput p) (fresh : TimeControl p) :
    firstCollectionCausalGate rate rewards C_star C_h u t q
      (replaceSourceControl p q z fresh) ↔
    firstCollectionCausalGate rate rewards C_star C_h u t q z := by
  rw [firstCollectionCausalGate_factor_of_postBirth rate rewards C_star C_h
      control0 u t q hfuture (replaceSourceControl p q z fresh),
    firstCollectionCausalGate_factor_of_postBirth rate rewards C_star C_h
      control0 u t q hfuture z,
    ReferenceFirstCollectionOldRecorderFoundation.sourcePrefix_replaceCurrent
      control0 q q le_rfl z fresh]

/-- The source round immediately after the first corrected birth cannot have
an incoming collection: its actual predecessor leaves LIVE or dagger. -/
theorem firstCollectionCausalGate_not_adjacent
    (u t q : Fin p.T) (hadj : q.val = t.val + 1) (z : SourceInput p) :
    ¬ firstCollectionCausalGate rate rewards C_star C_h u t q z := by
  intro hgate
  obtain ⟨record, payload, ledger, saved, hr, hcoord, _hsigma, _hpending⟩ :=
    (incomingCollectionTag_spec rate rewards C_star C_h t q z).mp hgate.2
  have hq : t.val + 1 < p.T := by omega
  have hqeq : q = ⟨t.val + 1, hq⟩ := Fin.ext hadj
  subst q
  have hphase :=
    ReferenceFirstCollectionCorrectedNextPhysicalReadout.firstCell_next_input_phase
      rate rewards C_star C_h u t hq z hgate.1.1 record hr
  rw [hcoord] at hphase
  exact hphase

/-- The literal incoming collection test supplies the strict post-birth gap;
no additional geometric premise is required on the causal gate. -/
theorem firstCollectionCausalGate_strict_postBirth
    (u t q : Fin p.T) (htq : t.val < q.val) (z : SourceInput p)
    (hgate : firstCollectionCausalGate rate rewards C_star C_h u t q z) :
    t.val + 1 < q.val := by
  have hne : q.val ≠ t.val + 1 := by
    intro h
    exact firstCollectionCausalGate_not_adjacent rate rewards C_star C_h u t q h z hgate
  omega

/-- The full causal gate is measurable for every strictly later query date,
including the empty immediate-successor case. -/
theorem firstCollectionCausalGate_measurable
    (control0 : TimeControl p) (u t q : Fin p.T) (htq : t.val < q.val) :
    MeasurableSet[sourcePrefixFiltration control0 (q.val + 1)]
      (firstCollectionCausalGate rate rewards C_star C_h u t q) := by
  by_cases hfuture : t.val + 1 < q.val
  · exact firstCollectionCausalGate_measurable_of_postBirth
      rate rewards C_star C_h control0 u t q hfuture
  · have hadj : q.val = t.val + 1 := by omega
    have hempty : firstCollectionCausalGate rate rewards C_star C_h u t q =
        (fun _ : SourceInput p => False) := by
      funext z
      exact propext (iff_false_intro
        (firstCollectionCausalGate_not_adjacent rate rewards C_star C_h u t q hadj z))
    rw [hempty]
    exact @MeasurableSet.empty (SourceInput p) (sourcePrefixFiltration control0 (q.val + 1))

/-- Strict-prefix factorization for every later date; adjacent gates are empty. -/
theorem firstCollectionCausalGate_factor
    (control0 : TimeControl p) (u t q : Fin p.T) (htq : t.val < q.val)
    (z : SourceInput p) :
    firstCollectionCausalGate rate rewards C_star C_h u t q z ↔
      firstCollectionCausalGate rate rewards C_star C_h u t q
        (sourcePrefix control0 q.val z) := by
  by_cases hfuture : t.val + 1 < q.val
  · exact firstCollectionCausalGate_factor_of_postBirth
      rate rewards C_star C_h control0 u t q hfuture z
  · have hadj : q.val = t.val + 1 := by omega
    exact iff_of_false
      (firstCollectionCausalGate_not_adjacent rate rewards C_star C_h u t q hadj z)
      (firstCollectionCausalGate_not_adjacent rate rewards C_star C_h u t q hadj _)

/-- Every complete current-control replacement preserves the full gate for
all strictly later dates, with no additional post-birth separation input. -/
theorem firstCollectionCausalGate_replaceSourceControl
    (control0 : TimeControl p) (u t q : Fin p.T) (htq : t.val < q.val)
    (z : SourceInput p) (fresh : TimeControl p) :
    firstCollectionCausalGate rate rewards C_star C_h u t q
      (replaceSourceControl p q z fresh) ↔
    firstCollectionCausalGate rate rewards C_star C_h u t q z := by
  rw [firstCollectionCausalGate_factor rate rewards C_star C_h
      control0 u t q htq (replaceSourceControl p q z fresh),
    firstCollectionCausalGate_factor rate rewards C_star C_h control0 u t q htq z,
    ReferenceFirstCollectionOldRecorderFoundation.sourcePrefix_replaceCurrent
      control0 q q le_rfl z fresh]

private theorem actualRecord_suffixIndex
    (q : Fin p.T) (z : SourceInput p) (record : Record)
    (hr : actualRecord rate rewards C_star C_h q z = some record) :
    ∃ k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h).length,
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[k.val]'k.isLt = record := by
  unfold actualRecord at hr
  split at hr
  · exact ⟨⟨_, (List.getElem?_eq_some_iff.mp hr).1⟩,
      (List.getElem?_eq_some_iff.mp hr).2⟩
  · contradiction

/-- Both scalar conditions of the accepted continuing-collection producer
follow from the original first-cell chronology and the actual incoming ledger. -/
theorem firstCollectionCausalGate_calendar_scalars
    (u t q : Fin p.T) (z : SourceInput p)
    (hgate : firstCollectionCausalGate rate rewards C_star C_h u t q z)
    (record : Record) (payload : Payload) (ledger : Ledger)
    (saved : Option (Fin p.T × Bool))
    (hr : actualRecord rate rewards C_star C_h q z = some record)
    (hcoord : record.input.state.coordinator = .collection payload ledger saved)
    (hsigma : payload.sigma = t) :
    ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h <
        payload.sigma.val ∧
      FollowerCutoffScan.firstCutoff p rate.eta.val payload.sigma
        (FollowerCutoffScan.completeRowProposalBit p rate.eta.val record.input.row) ≤
        record.input.time.val + 1 := by
  obtain ⟨birth, rout, qout, beta, _hb, _htime, _ht, _hrows, _hJ, _hrewards,
      _hborn, hbornSigma, hlater, _hnext, _hrest⟩ :=
    ReferenceFirstCorrectedReplacementCollectionReadout.firstCell_collection_readout_cover
      rate rewards C_star C_h u t z hgate.1
  have hlater' : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h <
      payload.sigma.val := by simpa only [hbornSigma, hsigma] using hlater
  obtain ⟨k, hk⟩ := actualRecord_suffixIndex rate rewards C_star C_h q z record hr
  have hspan := ReferenceCompleteCollectionIncrementSpan.complete_collection_input_increment_span
    rate rewards C_star C_h z k payload ledger saved (by rw [hk]; exact hcoord)
  dsimp only at hspan
  obtain ⟨_b, _hbk, _hbirth, _hbase, _ha, _hs, htrue, _hf, _hpos, _hle,
      _hT, hcutcursor, hcursor, _harrivals⟩ := hspan
  rw [hk] at hcursor
  have hf := ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields
    rate rewards C_star C_h q z record hr
  have hrow : record.input.row =
      z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) := by
    change record.input.rows record.input.selected = _
    rw [hf.1, hf.2.1]
  exact ⟨hlater', by rw [hrow, ← htrue]; omega⟩

/-- On the literal incoming first collection, the canonical numerical cell is
present and retains the actual recorder, whole reward row and all raw arrivals.
No successful later tail or pending-empty endpoint is an input. -/
theorem firstCollectionCausalGate_readout
    (u t q : Fin p.T) (z : SourceInput p)
    (hgate : firstCollectionCausalGate rate rewards C_star C_h u t q z)
    (record : Record) (payload : Payload) (ledger : Ledger)
    (saved : Option (Fin p.T × Bool))
    (hr : actualRecord rate rewards C_star C_h q z = some record)
    (hcoord : record.input.state.coordinator = .collection payload ledger saved)
    (hsigma : payload.sigma = t) (hpending : ledger.pending.Nonempty) :
    ∃ (c : RecordedQueueRun.RoundInput p.K)
      (started : CoordinatorPhaseClock.StartRoundResult p)
      (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ)
      (out : CoordinatorRecordingOperation.Output p),
      ReferenceFirstCollectionCurrentRetainedGate.cell0 rate record = some c ∧
      ReferenceLaterCollectionArrivalReadout.laterCollectionReadout
        (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) record = some c ∧
      ReferenceLaterCollectionArrivalReadout.preparedFollowersUnoccupied record ∧
      ReferenceLaterCollectionArrivalReadout.laterCollectionCall 0 record =
        some ⟨payload, ledger, started, weights⟩ ∧
      CoordinatorRecorderComplementBridge.run
        (ReferenceActivePhysicalStep.collectionRecordingInput record.output.preparation
          payload started weights) = some out ∧
      record.coordinatorDiagnostics.recording = some out ∧
      record.coordinatorDiagnostics = ReferenceActivePhysicalStep.collectionPostChoice
        record.output.preparation payload ledger started weights ∧
      ReferenceCollectionRawBufferHistory.rawDiagnostic record =
        out.gateArm.map (fun a => (a, out.rawArrival)) ∧
      out.gateArm = c.recordedArm ∧
      c.enabled = ReferenceActivePhysicalStep.collectionEnabled ledger q ∧
      c.rate = payload.rate ∧
      c.reward = (fun a => ((rewards q a).val : ℝ) / (D p : ℝ)) ∧
      (∀ a, CoordinatorCollectionLedger.localArrival
        (ReferenceCollectionRawBufferHistory.rawDiagnostic record) a =
          RecordedQueueRun.quantizedArrival
            (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a) ∧
      c.recordedArm = SnapshotRecordingKernel.recordingMap p .collection c.enabled
        rate.eta.val rate.eta.property rate.sourceCap payload.anchor payload.anchor
        payload.anchor_pos payload.anchor_pos (fun _ => le_rfl)
        (fun a => by linarith [payload.anchor_pos a])
        (ContinuousLearningRows.sliceAt q
          (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)).2) ∧
      (c.enabled = false → c.recordedArm = none ∧ ∀ a,
        RecordedQueueRun.quantizedArrival
          (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a = 0) := by
  obtain ⟨hlater, htrue⟩ := firstCollectionCausalGate_calendar_scalars
    rate rewards C_star C_h u t q z hgate record payload ledger saved hr hcoord hsigma
  obtain ⟨k, hk⟩ := actualRecord_suffixIndex rate rewards C_star C_h q z record hr
  subst record
  let record := (ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate z rewards C_star C_h)[k.val]
  change record.input.state.coordinator = .collection payload ledger saved at hcoord
  obtain ⟨cutoff, hcutoff, core, scores, started, _hstart, _hframe,
      _choiceInputs, snapshot, boundary, hdispatch, _hrest⟩ :=
    ReferenceCompleteContinuingCollectionChoiceDomains.complete_nonempty_continuing_collection_choice_domains
      rate rewards C_star C_h z k payload ledger saved hcoord hpending
  let clock := ReferenceActivePhysicalStep.collectionClock payload ledger saved cutoff
  have hprepared : record.output.preparation = ReferenceActivePhysicalStep.prepare record.input := by
    rw [record.output_eq]
    rfl
  have hbranch : record.output.preparation.coordinator =
      .collection payload ledger clock cutoff (.continuing core snapshot boundary scores) := by
    rw [hprepared]
    have hcutoffRange : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T := by
      have := cutoff.isLt
      omega
    have heq : (⟨ledger.cutoff - 1, by omega⟩ : Fin p.T) = cutoff := Fin.ext (by dsimp only; omega)
    simp only [ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch,
      hcoord, dite_eq_left hcutoffRange, CoordinatorRoundDispatch.dispatch]
    rw [heq]
    exact congrArg (ReferenceActivePhysicalStep.DispatchCut.collection payload ledger clock cutoff)
      hdispatch
  obtain ⟨c, hread, hfollowers, _callPayload, _callLedger, _callStarted, _callWeights,
      _out, _hpay, _hcall, _hrun, _hrecording, _hrate, _hreward, hraw, hdisabled⟩ :=
    ReferenceCompleteLaterCollectionCalendarReadout.complete_continuing_collection_calendar_readout
      rate rewards C_star C_h z k payload ledger clock cutoff core snapshot boundary scores
      hbranch hlater htrue
  change ReferenceLaterCollectionArrivalReadout.laterCollectionReadout
    (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) record = some c at hread
  change ReferenceLaterCollectionArrivalReadout.preparedFollowersUnoccupied record at hfollowers
  have hread0 : ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 record = some c := by
    simpa only [ReferenceLaterCollectionArrivalReadout.laterCollectionReadout,
      dite_eq_left hfollowers, hbranch] using hread
  have hcanonical : ReferenceLaterCollectionArrivalReadout.continuingCollectionInput
      record payload ledger clock cutoff snapshot = c := by
    simpa only [ReferenceLaterCollectionArrivalReadout.laterCollectionReadout,
      dite_eq_left hfollowers, hbranch, Option.some.injEq] using hread0
  have hcall : ReferenceLaterCollectionArrivalReadout.laterCollectionCall 0 record =
      some ⟨payload, ledger, snapshot.clockStarted,
        CoordinatorCollectionInteractive.PreObservationInputs.weights
          (ReferenceActivePhysicalStep.collectionInput record.input payload ledger clock cutoff)
          snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq⟩ := by
    simp only [ReferenceLaterCollectionArrivalReadout.laterCollectionCall,
      ite_eq_left hfollowers, hbranch]
  obtain ⟨callPayload, callLedger, callStarted, callWeights, out, hcall', hdiag,
      hrun, henabled, _hclock, hrate, hreward, hrecording, hgateArm, _hraw⟩ :=
    ReferenceLaterCollectionArrivalReadout.laterCollectionReadout_call 0 record c hread0
  have hargs := Option.some.inj (hcall'.symm.trans hcall)
  cases hargs
  have hf := ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields
    rate rewards C_star C_h q z record hr
  have hrow : record.input.row =
      z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) := by
    change record.input.rows record.input.selected = _
    rw [hf.1, hf.2.1]
  have hlive : ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 record = none := by
    cases hl : ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 record with
    | none => rfl
    | some d =>
      exact False.elim (ReferenceCompleteNumericalBranchObservation.readouts_disjoint
        rate 0 record ⟨by rw [hl]; rfl, by rw [hread0]; rfl⟩)
  refine ⟨c, snapshot.clockStarted, _, out, ?_, hread, hfollowers, hcall,
    hrun, hrecording, hdiag, ?_, hgateArm, ?_, hrate, ?_, hraw, ?_, ?_⟩
  · change ReferenceFirstCollectionCurrentRetainedGate.cell0 rate record = some c
    simp only [ReferenceFirstCollectionCurrentRetainedGate.cell0, hlive, Option.none_or, hread0]
  · unfold ReferenceCollectionRawBufferHistory.rawDiagnostic
    change record.coordinatorDiagnostics.recording.bind _ = _
    rw [hrecording]
    rfl
  · simpa only [hf.2.2.1] using henabled
  · simpa only [hf.2.2.1, hf.2.2.2] using hreward
  · rw [← hcanonical]
    dsimp only [ReferenceLaterCollectionArrivalReadout.continuingCollectionInput]
    rw [hf.2.2.1, hrow]
    exact ReferenceFirstCollectionOldRecorderFoundation.collectionMap_independent_currentWeights
      rate _ _ _ _ _ _ _ _
  · exact hdisabled

/-- A present incoming record stays present under whole current-control
replacement, with its full incoming state preserved literally. -/
theorem actualIncoming_replaceSourceControl
    (control0 : TimeControl p) (q : Fin p.T) (z : SourceInput p)
    (record : Record) (hr : actualRecord rate rewards C_star C_h q z = some record)
    (fresh : TimeControl p) :
    ∃ replacement : Record,
      actualRecord rate rewards C_star C_h q (replaceSourceControl p q z fresh) =
        some replacement ∧ replacement.input.state = record.input.state := by
  have hin := incomingState_replaceSourceControl rate rewards C_star C_h control0 q z fresh
  cases hr' : actualRecord rate rewards C_star C_h q (replaceSourceControl p q z fresh) with
  | none =>
    simp only [incoming, hr', hr, Option.map_none, Option.map_some, reduceCtorEq] at hin
  | some replacement =>
    refine ⟨replacement, rfl, ReferenceActivePhysicalStepMeasurability.encodeState_injective ?_⟩
    exact Option.some.inj (by simpa only [incoming, hr', hr, Option.map_some] using hin)

/-- The original actual payload, ledger, anchor and enabled bit determine the
current collection map under every complete fresh control. The outer SOME is
proved even when the marker is absent or every raw arrival is zero. -/
theorem firstCollectionCausalGate_recordingMap
    (control0 : TimeControl p) (u t q : Fin p.T) (htq : t.val < q.val)
    (z : SourceInput p)
    (hgate : firstCollectionCausalGate rate rewards C_star C_h u t q z) :
    ∃ (record : Record) (payload : Payload) (ledger : Ledger)
      (saved : Option (Fin p.T × Bool)),
      actualRecord rate rewards C_star C_h q z = some record ∧
      record.input.state.coordinator = .collection payload ledger saved ∧
      payload.sigma = t ∧ ledger.pending.Nonempty ∧
      ∀ fresh : TimeControl p,
        let z' := replaceSourceControl p q z fresh
        ((actualRecord rate rewards C_star C_h q z').bind
          (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate)).map (fun c => c.recordedArm) =
          some (SnapshotRecordingKernel.recordingMap p .collection
            (ReferenceActivePhysicalStep.collectionEnabled ledger q)
            rate.eta.val rate.eta.property rate.sourceCap payload.anchor payload.anchor
            payload.anchor_pos payload.anchor_pos (fun _ => le_rfl)
            (fun a => by linarith [payload.anchor_pos a]) fresh.1) ∧
        ∃ (replacement : Record) (c : RecordedQueueRun.RoundInput p.K)
          (started : CoordinatorPhaseClock.StartRoundResult p)
          (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ)
          (out : CoordinatorRecordingOperation.Output p),
          actualRecord rate rewards C_star C_h q z' = some replacement ∧
          replacement.input.state = record.input.state ∧
          replacement.input.state.coordinator = .collection payload ledger saved ∧
          ReferenceFirstCollectionCurrentRetainedGate.cell0 rate replacement = some c ∧
          c.enabled = ReferenceActivePhysicalStep.collectionEnabled ledger q ∧
          c.rate = payload.rate ∧
          c.reward = (fun a => ((rewards q a).val : ℝ) / (D p : ℝ)) ∧
          ReferenceLaterCollectionArrivalReadout.laterCollectionCall 0 replacement =
            some ⟨payload, ledger, started, weights⟩ ∧
          CoordinatorRecorderComplementBridge.run
            (ReferenceActivePhysicalStep.collectionRecordingInput replacement.output.preparation
              payload started weights) = some out ∧
          replacement.coordinatorDiagnostics.recording = some out ∧
          ReferenceCollectionRawBufferHistory.rawDiagnostic replacement =
            out.gateArm.map (fun a => (a, out.rawArrival)) ∧
          out.gateArm = c.recordedArm ∧
          (∀ a, CoordinatorCollectionLedger.localArrival
            (ReferenceCollectionRawBufferHistory.rawDiagnostic replacement) a =
              RecordedQueueRun.quantizedArrival
                (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a) ∧
          (c.enabled = false → c.recordedArm = none ∧ ∀ a,
            RecordedQueueRun.quantizedArrival
              (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a = 0) := by
  obtain ⟨record, payload, ledger, saved, hr, hcoord, hsigma, hpending⟩ :=
    (incomingCollectionTag_spec rate rewards C_star C_h t q z).mp hgate.2
  refine ⟨record, payload, ledger, saved, hr, hcoord, hsigma, hpending, ?_⟩
  intro fresh z'
  have hgate' : firstCollectionCausalGate rate rewards C_star C_h u t q z' :=
    (firstCollectionCausalGate_replaceSourceControl rate rewards C_star C_h
      control0 u t q htq z fresh).mpr hgate
  obtain ⟨replacement, hr', hstate⟩ := actualIncoming_replaceSourceControl
    rate rewards C_star C_h control0 q z record hr fresh
  have hcoord' : replacement.input.state.coordinator = .collection payload ledger saved := by
    rw [hstate, hcoord]
  obtain ⟨c, started, weights, out, hc, _hread, _hfollowers, hcall,
      hrun, hrecording, _hdiag, hrawDiagnostic, hmarker, henabled, hrate, hreward,
      hraw, hmap, hdisabled⟩ :=
    firstCollectionCausalGate_readout rate rewards C_star C_h u t q z' hgate'
      replacement payload ledger saved hr' hcoord' hsigma hpending
  constructor
  · rw [hr', Option.bind_some, hc, Option.map_some, hmap, henabled]
    have hslice : ContinuousLearningRows.sliceAt q
        (z'.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z')).2 = fresh.1 := by
      simp only [z', replaceSourceControl,
        ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex,
        ActualInitializationPhysicalStep.selectedRowIndex, ContinuousLearningRows.sliceAt,
        Function.update_self]
    rw [hslice]
  · exact ⟨replacement, c, started, weights, out, hr', hstate, hcoord', hc,
      henabled, hrate, hreward, hcall, hrun, hrecording, hrawDiagnostic, hmarker, hraw, hdisabled⟩

private theorem stored_between_first_birth_and_query
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (b k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (P : ReferenceActivePhysicalStep.Payload rate)
    (hbirth : InstallationBirth (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[b.val] P)
    (hcurrent : storedPayload (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val].input.state.coordinator = some P) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h
    ∀ (n : Fin R.length), b.val < n.val → n.val ≤ k.val →
      storedPayload R[n.val].input.state.coordinator = some P := by
  dsimp only
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h
  have hk : k.val < R.length := k.isLt
  have htime (n : Fin R.length) : R[n.val].input.time.val =
      ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h + n.val :=
    ReferenceAssignmentFollowerMassSteps.complete_record_time rate rewards C_star C_h source n
  have hbirthTime := ReferenceAssignmentPayloadChronology.installationBirth_time_eq
    R[b.val] P hbirth
  rw [htime b] at hbirthTime
  have hback : ∀ d, ∀ (hd : d ≤ k.val), b.val < k.val - d →
      storedPayload (R[k.val - d]'(by omega)).input.state.coordinator = some P := by
    intro d
    induction d with
    | zero => intro hd hb; simpa only [Nat.sub_zero] using hcurrent
    | succ d ih =>
        intro hd hb
        have hprev := ih (by omega) (by omega)
        let n : Fin R.length := ⟨k.val - (d + 1), by omega⟩
        have hnext : storedPayload R[n.val].output.next.coordinator = some P := by
          have ha := ReferenceCompleteLaterLiveComplementPrefixReplay.complete_adjacent (rate := rate) rewards C_star C_h source n.val
            (by dsimp [n]; omega)
          rw [← ha]
          have hindex : n.val + 1 = k.val - d := by dsimp [n]; omega
          simpa only [hindex] using hprev
        have hclass := ReferenceAssignmentPayloadChronology.actualStep_payload_classification
          R[n.val].input
        have houtput : ReferenceActivePhysicalStep.step R[n.val].input = R[n.val].output :=
          R[n.val].output_eq.symm
        rw [houtput] at hclass
        rcases hclass with hnone | ⟨old, hold, hout⟩ | ⟨fresh, hfresh, hout⟩
        · rw [hnext] at hnone
          cases hnone
        · have heq : old = P := Option.some.inj (hout.symm.trans hnext)
          simpa only [heq] using hold
        · have heq : fresh = P := Option.some.inj (hout.symm.trans hnext)
          have hfreshRecord : InstallationBirth R[n.val] P := by
            have hr : ReferenceAssignmentPayloadChronology.actualStepRecord R[n.val].input =
                R[n.val] := by
              cases hr : R[n.val] with
              | mk input output heq =>
                  dsimp only [ReferenceAssignmentPayloadChronology.actualStepRecord]
                  cases heq
                  rfl
            simpa only [heq, hr] using hfresh
          have hfreshTime := ReferenceAssignmentPayloadChronology.installationBirth_time_eq
            R[n.val] P hfreshRecord
          rw [htime n] at hfreshTime
          dsimp only [n] at hfreshTime
          omega
  intro n hbn hnk
  have h := hback (k.val - n.val) (by omega) (by omega)
  have hi : k.val - (k.val - n.val) = n.val := by omega
  simpa only [hi] using h

private theorem first_retained_collection_after_cutoff
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length) (P : ReferenceActivePhysicalStep.Payload rate)
    (hstored : storedPayload (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val].input.state.coordinator = some P)
    (htime : FollowerCutoffScan.firstCutoff p rate.eta.val P.sigma
      (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
        (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source))) ≤
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val].input.time.val) :
    ∃ l saved, (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val].input.state.coordinator = .collection P l saved := by
  let r := (ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h)[k.val]
  change storedPayload r.input.state.coordinator = some P at hstored
  change ∃ l saved, r.input.state.coordinator = .collection P l saved
  cases hstate : r.input.state.coordinator with
  | first => simp only [hstate, storedPayload, reduceCtorEq] at hstored
  | dagger => simp only [hstate, storedPayload, reduceCtorEq] at hstored
  | live registers owned base =>
      have hp : registers.payload = P := by
        simpa only [hstate, storedPayload, Option.some.injEq] using hstored
      have hlt := ReferenceAssignmentRetainedBirthProvenance.complete_coordinator_retained_birth
        rate rewards C_star C_h source k
      dsimp only at hlt
      rw [hstate] at hlt
      have hlt := hlt.2
      rw [hp] at hlt
      exact (not_lt_of_ge htime hlt).elim
  | collection payload l saved =>
      have hp : payload = P := by
        simpa only [hstate, storedPayload, Option.some.injEq] using hstored
      exact ⟨l, saved, by rw [hp]⟩

private theorem continuing_of_actual_collection_output
    (r : Record) (P : Payload) (l : Ledger) (saved : Option (Fin p.T × Bool))
    (hstate : r.input.state.coordinator = .collection P l saved)
    (Pout : Payload) (lout : Ledger) (savedout : Option (Fin p.T × Bool))
    (hout : r.output.next.coordinator = .collection Pout lout savedout) :
    continuing r = true := by
  obtain ⟨tail, htail, _hframe⟩ := ReferenceCollectionPhaseHistory.step_collection_frame
    r.input Pout lout savedout (by rw [← r.output_eq]; exact hout)
  have hchoice : ∃ c : Choice rate, choice r.input = some c := by
    unfold ReferenceCollectionPhaseHistory.executedTail at htail
    dsimp only at htail
    unfold choice
    split at htail
    · contradiction
    next hguard =>
      rw [ite_eq_right hguard]
      cases hd : (prepare r.input).coordinator with
      | first outcome => cases outcome <;> simp only [hd, reduceCtorEq] at htail
      | live registers owned base outcome =>
        cases outcome <;> simp only [hd, reduceCtorEq] at htail
        exact ⟨_, rfl⟩
      | collection payload ledger clock cutoff outcome =>
        cases outcome <;> simp only [hd, reduceCtorEq] at htail
        exact ⟨_, rfl⟩
      | invalidCollectionCutoff => simp only [hd, reduceCtorEq] at htail
      | dagger => simp only [hd, reduceCtorEq] at htail
  obtain ⟨c, hc⟩ := hchoice
  obtain ⟨done, hdone⟩ := actual_collection_round_complete r c Pout lout savedout hc hout
  have hcontext := (actual_collection_round_checked r done hdone).1
  have hnone := (choice_collection_pre r.input P l saved done.context hstate hcontext).2
  simp only [continuing, hdone, hnone, Option.isNone_none]

private theorem takeWhile_prefix_of_tests {α : Type} (xs : List α) (test : α → Bool)
    (n : ℕ) (hn : n ≤ xs.length)
    (hall : ∀ j, (hj : j < n) → test (xs[j]'(by omega)) = true) :
    n ≤ (xs.takeWhile test).length ∧
      (xs.takeWhile test).take n = xs.take n := by
  have ht : (xs.take n).takeWhile test = xs.take n := by
    apply List.takeWhile_eq_self_iff.mpr
    intro a ha
    obtain ⟨j, hj, heq⟩ := List.mem_iff_getElem.mp ha
    have hjn : j < n := by simpa only [List.length_take, Nat.min_eq_left hn] using hj
    have hget : (xs.take n)[j] = xs[j]'(by omega) := by simp only [List.getElem_take]
    rw [← heq, hget]
    exact hall j hjn
  have heq : (xs.takeWhile test).take n = xs.take n := by
    rw [List.take_takeWhile, ht]
  have hlen := congrArg List.length heq
  simp only [List.length_take, Nat.min_eq_left hn] at hlen
  exact ⟨by omega, heq⟩

private theorem segment_prefix_of_continuing
    (R : List (RoundRecord (p := p) (rate := rate))) (o k : ℕ)
    (hok : o ≤ k) (hk : k < R.length) (ho : o < R.length)
    (c0 : Choice rate) (I : Initializer p)
    (hc0 : choice R[o].input = some c0) (hI : c0.initializer = some I)
    (hentry : (extractRound R[o]).isSome = true)
    (hall : ∀ a : Fin R.length, o < a.val → a.val ≤ k → continuing R[a.val] = true) :
    ∃ seg : Segment rate,
      k - o < seg.records.length ∧ segmentAt R o = some seg ∧
      seg.entry = R[o] ∧ seg.context = c0 ∧
      (∀ hn : k - o < seg.records.length, seg.records[k - o]'hn = R[k]) ∧
      seg.records.take (k - o + 1) = (R.drop o).take (k - o + 1) := by
  classical
  let n := k - o
  let rest := R.drop (o + 1)
  let seg : Segment rate := ⟨R[o], c0, R[o] :: rest.takeWhile continuing,
    rest.dropWhile continuing⟩
  have hdrop : R.drop o = R[o] :: rest := List.drop_eq_getElem_cons ho
  have hsegment : segmentAt R o = some seg := by
    simp only [segmentAt, hdrop, ReferenceCollectionSegmentExtraction.segment, hc0, Option.map_some,
      hentry, ↓reduceIte, Option.bind_some]
    change (if o = 0 ∨ c0.initializer.isSome = true then some seg else none) = some seg
    exact ite_eq_left (Or.inr (by simp only [hI, Option.isSome_some]))
  have hnRest : n ≤ rest.length := by
    dsimp only [rest, n]
    simp only [List.length_drop]
    omega
  have hprefix := takeWhile_prefix_of_tests rest continuing n hnRest (by
    intro j hj
    have hbound : o + 1 + j < R.length := by dsimp only [n] at hj; omega
    have hget : rest[j]'(by omega) = R[o + 1 + j] := by
      simp only [rest, List.getElem_drop]
    rw [hget]
    exact hall ⟨o + 1 + j, hbound⟩ (by change o < o + 1 + j; omega)
      (by change o + 1 + j ≤ k; dsimp only [n] at hj; omega))
  have hn : n < seg.records.length := by
    change n < (R[o] :: rest.takeWhile continuing).length
    simp only [List.length_cons]
    omega
  have hprefixEq : seg.records.take (n + 1) = (R.drop o).take (n + 1) := by
    change (R[o] :: rest.takeWhile continuing).take (n + 1) = _
    rw [hdrop]
    simp only [List.take_succ_cons, hprefix.2]
  have hrecord : seg.records[n] = R[k] := by
    have hget := congrArg (fun xs : List (RoundRecord (p := p) (rate := rate)) => xs[n]?) hprefixEq
    have hdropBound : n < (R.drop o).length := by
      simp only [List.length_drop]
      dsimp only [n]
      omega
    simp only [List.getElem?_take, show n < n + 1 by omega, ↓reduceIte,
      List.getElem?_eq_getElem hn, List.getElem?_eq_getElem hdropBound] at hget
    have heq : o + n = k := by dsimp only [n]; omega
    simpa only [List.getElem_drop, heq] using Option.some.inj hget
  exact ⟨seg, hn, hsegment, rfl, rfl, fun _ => hrecord, hprefixEq⟩

private theorem first_query_collection_output
    (u t q : Fin p.T) (z : SourceInput p)
    (hgate : firstCollectionCausalGate rate rewards C_star C_h u t q z)
    (record : Record) (payload : Payload) (ledger : Ledger)
    (saved : Option (Fin p.T × Bool))
    (hr : actualRecord rate rewards C_star C_h q z = some record)
    (hcoord : record.input.state.coordinator = .collection payload ledger saved)
    (hsigma : payload.sigma = t) (hpending : ledger.pending.Nonempty) :
    ∃ P l saved, record.output.next.coordinator = .collection P l saved := by
  obtain ⟨c, started, weights, out, _hc, _hread, _hfollowers, _hcall,
      _hrun, _hrecording, hdiag, _hrawDiagnostic, _hmarker, _henabled,
      _hrate, _hreward, _hraw, _hmap, _hdisabled⟩ :=
    firstCollectionCausalGate_readout rate rewards C_star C_h u t q z hgate
      record payload ledger saved hr hcoord hsigma hpending
  have hphase := ReferenceCollectionPhaseHistory.collectionPostChoice_no_installation
    record.output.preparation payload ledger started weights
  change record.output.coordinator = _ at hdiag
  rw [← hdiag] at hphase
  have hnext : record.output.next.coordinator = record.output.coordinator.configuration := by
    rw [record.output_eq]
    rfl
  rw [← hnext] at hphase
  rcases hphase with hdagger | hcollection
  · obtain ⟨k, hk⟩ := actualRecord_suffixIndex rate rewards C_star C_h q z record hr
    have hnot := (ReferenceCompleteCoordinatorPhaseExhaustion.complete_coordinator_phase_exhaustion
      rate rewards C_star C_h z).1 k
    dsimp only at hnot
    rw [hk] at hnot
    exact False.elim (hnot.2.2.2.2 hdagger)
  · exact hcollection

private theorem first_collection_continuing_interval
    (z : SourceInput p) (b e : ℕ)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length) (payload : Payload)
    (hbe : b < e)
    (hbetween : ∀ a : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length, b < a.val → a.val ≤ k.val →
      storedPayload ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[a.val]'a.isLt).input.state.coordinator = some payload)
    (hcutDate : FollowerCutoffScan.firstCutoff p rate.eta.val payload.sigma
      (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
        (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z))) =
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + e + 1)
    (hfinalOut : ∃ P l saved, ((ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[k.val]'k.isLt).output.next.coordinator = .collection P l saved) :
    ∀ a : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length,
      e < a.val → a.val ≤ k.val → continuing
        ((ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)[a.val]'a.isLt) = true := by
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  have hkLt : k.val < R.length := k.isLt
  have hcollection (a : Fin R.length) (hea : e < a.val) (hak : a.val ≤ k.val) :
      ∃ l saved, (R[a.val]'a.isLt).input.state.coordinator = .collection payload l saved := by
    have hstored := hbetween a (hbe.trans hea) hak
    have htime := ReferenceAssignmentFollowerMassSteps.complete_record_time
      rate rewards C_star C_h z a
    apply first_retained_collection_after_cutoff rate rewards C_star C_h z a payload hstored
    rw [hcutDate, htime]
    omega
  intro a hea hak
  obtain ⟨l, saved, hin⟩ := hcollection a hea hak
  have hout : ∃ P l saved, (R[a.val]'a.isLt).output.next.coordinator = .collection P l saved := by
    by_cases heq : a.val = k.val
    · have heq' : a = k := Fin.ext heq
      subst a
      exact hfinalOut
    · have haklt : a.val < k.val := by omega
      have hbound : a.val + 1 < R.length := by omega
      obtain ⟨l, saved, hnextState⟩ := hcollection ⟨a.val + 1, hbound⟩
        (by change e < a.val + 1; omega) (by change a.val + 1 ≤ k.val; omega)
      have hadj := ReferenceCompleteLaterLiveComplementPrefixReplay.complete_adjacent
        (rate := rate) rewards C_star C_h z a.val hbound
      exact ⟨payload, l, saved, by rw [← hadj]; exact hnextState⟩
  obtain ⟨Pout, lout, savedout, hout⟩ := hout
  exact continuing_of_actual_collection_output rate (R[a.val]'a.isLt) payload l saved hin
    Pout lout savedout hout

private theorem segment_entry_choice
    (R : List Record) (e : ℕ) (he : e < R.length) (seg : Segment rate)
    (hseg : segmentAt R e = some seg) :
    choice (R[e]'he).input = some seg.context := by
  have hbranch := (segmentAt_branch R e seg hseg).1
  have hdrop : R.drop e = R[e]'he :: R.drop (e + 1) := List.drop_eq_getElem_cons he
  rw [hdrop] at hbranch
  simp only [ReferenceCollectionSegmentExtraction.segment] at hbranch
  cases hc : choice (R[e]'he).input with
  | none => simp only [hc, Option.map_none, reduceCtorEq] at hbranch
  | some c =>
    simp only [hc, Option.map_some] at hbranch
    split at hbranch <;> cases Option.some.inj hbranch <;> rfl

/-- The literal incoming record belongs to the first post-birth collection
of this same source. Its position and initializer are produced from the actual
birth, maximal LIVE prefix and persistent whole payload, never supplied as a
matching-segment assumption. -/
theorem firstCollectionCausalGate_firstSegment
    (u t q : Fin p.T) (htq : t.val < q.val) (z : SourceInput p)
    (hgate : firstCollectionCausalGate rate rewards C_star C_h u t q z)
    (record : Record) (payload : Payload) (ledger : Ledger)
    (saved : Option (Fin p.T × Bool))
    (hr : actualRecord rate rewards C_star C_h q z = some record)
    (hcoord : record.input.state.coordinator = .collection payload ledger saved)
    (hsigma : payload.sigma = t) (hpending : ledger.pending.Nonempty) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    let b := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex rate rewards C_star C_h z
    let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
      rate rewards C_star C_h z (b + 1)
    let e := b + 1 + W.length
    ∃ (birth : Record) (seg : Segment rate) (I : Initializer p),
      R[b]? = some birth ∧ InstallationBirth birth payload ∧
      segmentAt R e = some seg ∧ seg.context.payload = payload ∧
      seg.context.initializer = some I ∧ I.sigma = t.val + 1 ∧
      I.cutoff = s + e + 1 ∧
      I.cutoff = FollowerCutoffScan.firstCutoff p rate.eta.val payload.sigma
        (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
          (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z))) ∧
      seg.records ++ seg.remaining = R.drop e ∧
      q.val - s - e < seg.records.length ∧
      seg.records[q.val - s - e]? = some record ∧
      seg.records.take (q.val - s - e + 1) = (R.drop e).take (q.val - s - e + 1) := by
  intro R s b W e
  obtain ⟨birth, rout, qout, beta, hb, hbt, _hdate, _hrows, _hJ, _hrewards,
      hborn, hbornSigma, hlater, hnext, hcont⟩ :=
    ReferenceFirstCorrectedReplacementCollectionReadout.firstCell_collection_readout_cover
      rate rewards C_star C_h u t z hgate.1
  change R[b]? = some birth at hb
  change s + b = t.val at hbt
  have hbLt : b < R.length := (List.getElem?_eq_some_iff.mp hb).1
  have hbRecord : R[b]'hbLt = birth := (List.getElem?_eq_some_iff.mp hb).2
  obtain ⟨k, hk⟩ := actualRecord_suffixIndex rate rewards C_star C_h q z record hr
  change R[k.val] = record at hk
  have hkLt : k.val < R.length := k.isLt
  have hkdate := ReferenceAssignmentFollowerMassSteps.complete_record_time
    rate rewards C_star C_h z k
  change (R[k.val]'k.isLt).input.time.val = s + k.val at hkdate
  have hf := ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields
    rate rewards C_star C_h q z record hr
  have hkq : s + k.val = q.val := by rw [hk, hf.2.2.1] at hkdate; omega
  have hbk : b + 1 < k.val := by
    have hgap := firstCollectionCausalGate_strict_postBirth rate rewards C_star C_h
      u t q htq z hgate
    omega
  have hprovenance := ReferenceAssignmentRetainedBirthProvenance.complete_coordinator_retained_birth
    rate rewards C_star C_h z k
  dsimp only at hprovenance
  rw [hk, hcoord] at hprovenance
  obtain ⟨⟨bp, _hbp, hbornP, _hbase⟩, _ha, _hs, htrueCutoff⟩ := hprovenance
  have hbptime := installationBirth_time_eq _ payload hbornP
  have hbpdate := ReferenceAssignmentFollowerMassSteps.complete_record_time
    rate rewards C_star C_h z bp
  change (R[bp.val]'bp.isLt).input.time.val = s + bp.val at hbpdate
  change payload.sigma.val = (R[bp.val]'bp.isLt).input.time.val at hbptime
  have hbpEq : bp.val = b := by rw [hsigma, hbpdate] at hbptime; omega
  change InstallationBirth (R[bp.val]'bp.isLt) payload at hbornP
  have hbirthP : InstallationBirth birth payload := by
    simpa only [hbpEq, hbRecord] using hbornP
  have hpayload : payload = rout.payload :=
    installationBirth_payload_unique birth payload rout.payload hbirthP hborn
  have hstored : storedPayload (R[k.val]'k.isLt).input.state.coordinator = some payload := by
    rw [hk, hcoord]
    rfl
  have hbetween := stored_between_first_birth_and_query rate rewards C_star C_h z
    ⟨b, hbLt⟩ k payload (by change InstallationBirth (R[b]'hbLt) payload; rw [hbRecord]; exact hbirthP) hstored
  change ∀ a : Fin R.length, b < a.val → a.val ≤ k.val →
    storedPayload (R[a.val]'a.isLt).input.state.coordinator = some payload at hbetween
  have hfirstNext : b + 1 < R.length := by omega
  have hstate0 : (R[b + 1]).input.state.coordinator = .live rout qout beta := by
    have hadj := ReferenceCompleteLaterLiveComplementPrefixReplay.complete_adjacent
      (rate := rate) rewards C_star C_h z b hfirstNext
    change (R[b + 1]).input.state = (R[b]'(by omega)).output.next at hadj
    rw [hadj, hbRecord, hnext]
  have hq : t.val + 1 < p.T := by omega
  obtain ⟨helen, _hWtime, rE, qE, _hpayloadE, _hstateE, hcase⟩ := hcont hq
  change e ≤ R.length at helen
  have hek : e ≤ k.val := by
    by_contra hnot
    have hv : k.val - (b + 1) ≤ W.length := by dsimp only [e] at hnot; omega
    obtain ⟨rv, qv, _hpay, _hout, hin⟩ :=
      ReferenceCompleteLaterLiveComplementPrefixReplay.prefix_live
        (rate := rate) rewards C_star C_h z ⟨b + 1, hfirstNext⟩ rout qout beta
        hstate0 hlater (k.val - (b + 1)) hv
    have hindex : b + 1 + (k.val - (b + 1)) = k.val := by omega
    have hin' := hin (by change b + 1 + (k.val - (b + 1)) < R.length; omega)
    change (R[b + 1 + (k.val - (b + 1))]).input.state.coordinator = .live rv qv beta at hin'
    have hinK : (R[k.val]'k.isLt).input.state.coordinator = .live rv qv beta := by
      simpa only [hindex] using hin'
    rw [hk, hcoord] at hinK
    contradiction
  rcases hcase with hterminal | ⟨he, seg, I, l0, hseg, _hentry, hsegPayload,
    _hpreLedger, hinit, _hI, _hchecked, _hassignment, hIsigma, hIdate,
    hItrue, _hfreeze, _hbase, _hcutoffChosen, _hrecords, hpartition, _hrest⟩
  · change e = R.length at hterminal
    omega
  · change e < R.length at he
    change segmentAt R e = some seg at hseg
    have hcutDate : FollowerCutoffScan.firstCutoff p rate.eta.val payload.sigma
        (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
          (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z))) = s + e + 1 := by
      rw [hpayload]
      exact hItrue.symm.trans hIdate
    have hfinalOut := first_query_collection_output rate rewards C_star C_h u t q z
      hgate record payload ledger saved hr hcoord hsigma hpending
    have hfinalOut' : ∃ P l saved,
        (R[k.val]'k.isLt).output.next.coordinator = .collection P l saved := by
      rw [hk]
      exact hfinalOut
    have hall := first_collection_continuing_interval rate rewards C_star C_h z
      b e k payload (by dsimp only [e]; omega) hbetween hcutDate hfinalOut'
    obtain ⟨seg', hn, hseg', _hentry', _hcontext', hrecord', hprefix⟩ :=
      segment_prefix_of_continuing rate R e k.val hek k.isLt he seg.context I
        (segment_entry_choice rate R e he seg hseg)
        hinit
        (by
          have hmem : seg.entry ∈ seg.records := by
            obtain ⟨during, hrecords⟩ := _hrecords
            rw [hrecords]
            exact List.mem_cons_self
          have hc := segment_all_completed (R.drop e) seg (segmentAt_branch R e seg hseg).1
          change seg.entry = (R[e]'he) at _hentry
          rw [← _hentry]
          exact hc seg.entry hmem)
        hall
    have heqSeg : seg' = seg := Option.some.inj (hseg'.symm.trans hseg)
    subst seg'
    have hposition : q.val - s - e = k.val - e := by omega
    refine ⟨birth, seg, I, hb, hbirthP, hseg, ?_, hinit, hIsigma, hIdate,
      ?_, hpartition, ?_, ?_, ?_⟩
    · exact hsegPayload.trans hpayload.symm
    · exact hItrue.trans (congrArg (fun P : Payload => FollowerCutoffScan.firstCutoff
        p rate.eta.val P.sigma (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
          (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)))) hpayload.symm)
    · simpa only [hposition] using hn
    · rw [hposition, List.getElem?_eq_getElem hn, hrecord' hn, hk]
    · simpa only [hposition] using hprefix

end Bandits.Support.ReferenceFirstCorrectedCollectionCausalReadout

end
