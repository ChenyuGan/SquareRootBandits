/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingMoments

import Mathlib.Tactic
import Mathlib.MeasureTheory.Function.FactorsThrough

/-!
# Future dates of the first replacement assignment

Sources: `04_slow_fast_learner.tex:142-168`, `05_binary_transport.tex:354-431`,
`06_interruptions.tex:391-426`, and `appendix_a_local_protocol.tex:28-64`
in `sources/zip4/manuscript`.

All records and preparations below belong to the original renewal source.
The continuing window is the existing first replacement slice; its endpoint
is the next original record. No probability or moment assertion is made.
-/

@[expose] public section
noncomputable section

open MeasureTheory
open Bandits.Support ConstructorDimensions
open scoped Classical

namespace Bandits.Support.ReferenceFirstCollectionRenewalFutureFirstReplacementView

open ReferenceActivePhysicalStep ReferenceActivePhysicalHorizon
open ReferenceActivePhysicalStepMeasurability
open ReferenceFirstCollectionRenewalIncomingQueuePrefix
open ReferenceSourcePrefixHistoryFiltration

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ) (u t : Fin p.T)

local notation "Z" => ReferenceFirstCollectionRenewalNextControlLaw.Source
  rate rewards C_star C_h u t

/-- The exact pre-round field, retaining selected controls with index below `n`. -/
abbrev priorField (control0 : ContinuousLearningRows.TimeControl p) (n : ℕ) :
    MeasurableSpace Z :=
  MeasurableSpace.comap Subtype.val (sourcePrefixFiltration control0 (n + 1))

/-- The original calendar index in the original suffix. -/
def futureIndex (z : Z) (q : Fin p.T) (hfuture : t.val + 1 < q.val) :
    Fin (sourceRecords rate rewards C_star C_h u t z).length :=
  ⟨q.val - start rate rewards C_star C_h u t z, by
    rw [sourceRecords_length]
    have hb := actual_boundaries rate rewards C_star C_h u t z
    have hq := q.isLt
    omega⟩

def futureRecord (z : Z) (q : Fin p.T) (hfuture : t.val + 1 < q.val) :=
  (sourceRecords rate rewards C_star C_h u t z).get
    (futureIndex rate rewards C_star C_h u t z q hfuture)

def continuingRecords (z : Z) :=
  ReferenceFirstReplacementLiveFollowerPrefix.continuingTail
    (sourceRecords rate rewards C_star C_h u t z)
    (t.val - start rate rewards C_star C_h u t z)

theorem futureRecord_lookup (z : Z) (q : Fin p.T) (hfuture : t.val + 1 < q.val) :
    (sourceRecords rate rewards C_star C_h u t z)[
      q.val - start rate rewards C_star C_h u t z]? =
        some (futureRecord rate rewards C_star C_h u t z q hfuture) :=
  List.getElem?_eq_getElem (futureIndex rate rewards C_star C_h u t z q hfuture).isLt

/-- Calendar coverage retains the whole reward table, rows and original private J. -/
theorem futureRecord_fields (z : Z) (q : Fin p.T) (hfuture : t.val + 1 < q.val) :
    let r := futureRecord rate rewards C_star C_h u t z q hfuture
    r.input.time = q ∧ r.input.rows = z.val.1.2 ∧
      r.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p z.val ∧
      r.input.rewards = rewards := by
  obtain ⟨_, _, hr⟩ := ReferenceLaterLiveNumericalReadout.source_record_prefix
    rate rewards C_star C_h z.val (futureIndex rate rewards C_star C_h u t z q hfuture)
  change futureRecord rate rewards C_star C_h u t z q hfuture = _ at hr
  dsimp only
  rw [hr]
  refine ⟨Fin.ext ?_, rfl, rfl, rfl⟩
  have hb := actual_boundaries rate rewards C_star C_h u t z
  change start rate rewards C_star C_h u t z +
    (q.val - start rate rewards C_star C_h u t z) = q.val
  omega

theorem actualRecord_future (z : Z) (q : Fin p.T) (hfuture : t.val + 1 < q.val) :
    actualRecord rate rewards C_star C_h q z.val =
      some (futureRecord rate rewards C_star C_h u t z q hfuture) := by
  have hb := actual_boundaries rate rewards C_star C_h u t z
  have hs : ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h ≤
      q.val := by change start rate rewards C_star C_h u t z ≤ _; omega
  rw [actualRecord, ite_eq_left hs]
  exact futureRecord_lookup rate rewards C_star C_h u t z q hfuture

theorem incoming_future (z : Z) (q : Fin p.T) (hfuture : t.val + 1 < q.val) :
    incoming rate rewards C_star C_h q z.val = some (encodeState
      (futureRecord rate rewards C_star C_h u t z q hfuture).input.state) := by
  rw [ReferenceSourcePrefixHistoryFiltration.incoming,
    actualRecord_future rate rewards C_star C_h u t z q hfuture]
  rfl

/-- Equal strict prefixes fix the full incoming physical state at q. -/
theorem futureState_congr (control0 : ContinuousLearningRows.TimeControl p)
    (z z' : Z) (q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (hprefix : sourcePrefix control0 q.val z.val = sourcePrefix control0 q.val z'.val) :
    (futureRecord rate rewards C_star C_h u t z q hfuture).input.state =
      (futureRecord rate rewards C_star C_h u t z' q hfuture).input.state := by
  apply encodeState_injective
  apply Option.some.inj
  rw [← incoming_future rate rewards C_star C_h u t z q hfuture,
    ← incoming_future rate rewards C_star C_h u t z' q hfuture,
    incoming_factor rate rewards C_star C_h control0 q z.val,
    incoming_factor rate rewards C_star C_h control0 q z'.val, hprefix]

private theorem birth_shape (z : Z) :
    match (callRecord rate rewards C_star C_h u t z).output.preparation.coordinator with
    | .collection _ _ _ _ (.laterChosen ..) => True
    | _ => False := by
  obtain ⟨d, consistent, output, hlocal, _hstart, _hvector, _hreconstruction,
    _hslow, _hslowSet, _hinstalledPayload, _hinstalledVector, _hinstalledReconstruction,
    _hanchor, _hqueues, _hretained, selection, _hchoice, hdispatch, hprep, hcoord,
    _harm, _hpost⟩ :=
    ReferenceFirstCollectionRenewalSampleInstallation.actual_renewal_call_installation
      rate rewards C_star C_h u t z
  have heq := actual_call_record_eq rate rewards C_star C_h u t z d
  have hb : ReferenceCollectionPhaseHistory.laterChosen
      (callRecord rate rewards C_star C_h u t z).input = true := by
    rw [← heq]
    unfold ReferenceCollectionPhaseHistory.laterChosen
    rw [← hprep, hcoord, hdispatch]
  unfold ReferenceCollectionPhaseHistory.laterChosen at hb
  have hp : (callRecord rate rewards C_star C_h u t z).output.preparation =
      prepare (callRecord rate rewards C_star C_h u t z).input := by
    rw [(callRecord rate rewards C_star C_h u t z).output_eq]
    rfl
  rw [← hp] at hb
  cases h : (callRecord rate rewards C_star C_h u t z).output.preparation.coordinator
    <;> simp only [h] at hb ⊢ <;> try contradiction
  rename_i outcome
  cases outcome <;> simp_all

private theorem call_lookup (z : Z) :
    (sourceRecords rate rewards C_star C_h u t z)[
      t.val - start rate rewards C_star C_h u t z]? =
        some (callRecord rate rewards C_star C_h u t z) :=
  List.getElem?_eq_getElem (call_index_lt rate rewards C_star C_h u t z)

/-- Actual present readout on the entire continuing slice, with the installed
payload and full physical source cell. -/
theorem continuing_readout (z : Z)
    (k : Fin (continuingRecords rate rewards C_star C_h u t z).length) :
    let r := (continuingRecords rate rewards C_star C_h u t z).get k
    ∃ cell : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell r,
      ReferenceLaterLiveNumericalReadout.laterLiveReadout
        (start rate rewards C_star C_h u t z) r = some cell.input ∧
      cell.input.enabled = true ∧
      cell.selected.view.payload.sigma.val = t.val ∧
      (callRecord rate rewards C_star C_h u t z).output.preparation.coordinator.downView.map
        (fun view => view.payload) = some cell.selected.view.payload := by
  have h := ReferenceFirstReplacementFollowerBoundary.complete_first_replacement_continuing_live_readout
    rate z.val rewards C_star C_h
  have hg := ReferenceFirstReplacementLiveFollowerPrefix.complete_first_replacement_continuing_geometry
    rate z.val rewards C_star C_h
  have hb := birth_shape rate rewards C_star C_h u t z
  have hframes := ReferenceCoordinatorRecorderCallCorrespondence.actual_call_frames
    (callRecord rate rewards C_star C_h u t z)
  have hi := ReferenceFirstCollectionRenewalNextPhysicalPrefix.firstReplacementIndex_eq
    rate rewards C_star C_h u t z
  have h0 := call_lookup rate rewards C_star C_h u t z
  dsimp only [sourceRecords] at hi h0
  dsimp only at h hg
  simp only [hi, h0] at h hg
  cases hc : (callRecord rate rewards C_star C_h u t z).output.preparation.coordinator
    <;> simp only [hc] at hb h hg hframes
  rename_i outcome
  cases outcome <;> try contradiction
  dsimp only at h hg
  rw [hi] at h hg
  obtain ⟨_, cell, hpay, hread, henabled, _⟩ := h k
  refine ⟨cell, hread, henabled, ?_, ?_⟩
  · rw [hpay, hg.1]
    exact congrArg Fin.val (callRecord_time rate rewards C_star C_h u t z)
  · rw [hpay]
    simp only [DispatchCut.downView, DispatchCut.selection, selectionAt,
      dite_eq_left hframes.1, Option.map_some]

private theorem live_baseline_zero
    (r : RoundRecord (p := p) (rate := rate)) (s : ℕ)
    (c : RecordedQueueRun.RoundInput p.K)
    (hc : ReferenceLaterLiveNumericalReadout.laterLiveReadout s r = some c) :
    ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r = some c := by
  obtain ⟨selected, ho, hselection, hbase, hlive, hcell⟩ :=
    ReferenceLaterLiveNumericalReadout.laterLiveReadout_some s r c hc
  have hz : 0 < selected.view.payload.sigma.val := by omega
  unfold ReferenceLaterLiveNumericalReadout.laterLiveReadout
  simp only [hselection, hz, hlive, and_self, ite_true, dite_eq_left ho]
  exact congrArg some hcell.symm

/-- The original calendar record is a slice member at its original index. -/
theorem futureRecord_eq_continuing (z : Z) (q : Fin p.T)
    (hfuture : t.val + 1 < q.val)
    (hk : q.val - (t.val + 1) < (continuingRecords rate rewards C_star C_h u t z).length) :
    futureRecord rate rewards C_star C_h u t z q hfuture =
      (continuingRecords rate rewards C_star C_h u t z).get
        ⟨q.val - (t.val + 1), hk⟩ := by
  have h := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail_get
    (sourceRecords rate rewards C_star C_h u t z)
    (t.val - start rate rewards C_star C_h u t z) ⟨q.val - (t.val + 1), hk⟩
  have hb := actual_boundaries rate rewards C_star C_h u t z
  have hi : t.val - start rate rewards C_star C_h u t z + 1 +
      (q.val - (t.val + 1)) = q.val - start rate rewards C_star C_h u t z := by omega
  rw [hi, futureRecord_lookup rate rewards C_star C_h u t z q hfuture] at h
  exact Option.some.inj h

/-- A future continuing date has an actual SOME live cell, with its complete
prepared snapshot and the original whole-table reward. The zero-baseline
observation agrees with the physical readout at the original start. -/
theorem firstReplacement_future_live_readout (z : Z) (q : Fin p.T)
    (hfuture : t.val + 1 < q.val)
    (hk : q.val - (t.val + 1) < (continuingRecords rate rewards C_star C_h u t z).length) :
    let r := futureRecord rate rewards C_star C_h u t z q hfuture
    ∃ cell : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell r,
      ReferenceLaterLiveNumericalReadout.laterLiveReadout
        (start rate rewards C_star C_h u t z) r = some cell.input ∧
      ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r = some cell.input ∧
      cell.input.enabled = true ∧ cell.selected.view.payload.sigma.val = t.val ∧
      cell.input.rate = cell.selected.view.payload.rate ∧
      cell.input.reward = (fun a => ((rewards q a).val : ℝ) / (D p : ℝ)) ∧
      (∀ i, (r.output.preparation.followers.followers i).configuration =
        .ordinary (cell.states i) (cell.memories i)) ∧
      cell.input.recordedArm = ReferenceContinuingRecordingFastPair.physicalMarkerOnRecord
        r cell.selected.view.payload true ∧
      (callRecord rate rewards C_star C_h u t z).output.preparation.coordinator.downView.map
        (fun view => view.payload) = some cell.selected.view.payload := by
  have hr := futureRecord_eq_continuing rate rewards C_star C_h u t z q hfuture hk
  have h := continuing_readout rate rewards C_star C_h u t z ⟨q.val - (t.val + 1), hk⟩
  rw [← hr] at h
  obtain ⟨cell, hread, henabled, hsigma, hinstalled⟩ := h
  have hf := futureRecord_fields rate rewards C_star C_h u t z q hfuture
  have hp := ReferenceLaterLiveNumericalReadout.laterLiveReadout_physical
    rate rewards C_star C_h z.val (futureIndex rate rewards C_star C_h u t z q hfuture)
    cell.input hread
  obtain ⟨cell', heq, _, _, _, _, _, _, hmarker, _⟩ := hp
  have hcell : cell'.input = cell.input := heq
  refine ⟨cell, hread, live_baseline_zero rate _ _ _ hread, henabled, hsigma, ?_, ?_, ?_, ?_, hinstalled⟩
  · rw [cell.input_eq]; rfl
  · rw [cell.input_eq]
    change (fun a => (((futureRecord rate rewards C_star C_h u t z q hfuture).input.rewards
      (futureRecord rate rewards C_star C_h u t z q hfuture).input.time a).val : ℝ) / (D p : ℝ)) = _
    rw [hf.2.2.2, hf.1]
  · exact cell.ordinary
  · have hs : cell'.selected = cell.selected :=
      Option.some.inj (cell'.selection_actual.symm.trans cell.selection_actual)
    rw [hs] at hmarker
    exact hmarker

/-- At the first noncontinuing original record, an actual cutoff makes every
prepared follower ordinary and unoccupied. This conclusion includes all
followers, independently of their active ownership status before PREPARE. -/
theorem firstReplacement_future_cutoff_prepared (z : Z) (q : Fin p.T)
    (hfuture : t.val + 1 < q.val)
    (hend : q.val - (t.val + 1) = (continuingRecords rate rewards C_star C_h u t z).length) :
    let r := futureRecord rate rewards C_star C_h u t z q hfuture
    match r.output.preparation.coordinator with
    | .live registers _ _ (.cutoffChosen ..) =>
      registers.payload.sigma.val = t.val ∧
      start rate rewards C_star C_h u t z < registers.payload.sigma.val ∧
      r.input.time.val + 1 ≤ FollowerCutoffScan.gridBoundary p rate.eta.val registers.payload.sigma ∧
      (∀ i : Fin (p.m - 1), ∃ state memory,
        (r.output.preparation.followers.followers i).configuration = .ordinary state memory ∧
        state.status = .unoccupied) ∧
      (callRecord rate rewards C_star C_h u t z).output.preparation.coordinator.downView.map
        (fun view => view.payload) = some registers.payload
    | _ => True := by
  have h := ReferenceFirstReplacementCutoffPreparedBoundary.complete_first_replacement_cutoff_follower_boundary
    rate z.val rewards C_star C_h
  have hb := birth_shape rate rewards C_star C_h u t z
  have hframes := ReferenceCoordinatorRecorderCallCorrespondence.actual_call_frames
    (callRecord rate rewards C_star C_h u t z)
  have hi := ReferenceFirstCollectionRenewalNextPhysicalPrefix.firstReplacementIndex_eq
    rate rewards C_star C_h u t z
  have h0 := call_lookup rate rewards C_star C_h u t z
  dsimp only [sourceRecords] at hi h0
  dsimp only at h
  simp only [hi, h0] at h
  cases hc : (callRecord rate rewards C_star C_h u t z).output.preparation.coordinator
    <;> simp only [hc] at hb h hframes
  rename_i outcome
  cases outcome <;> try contradiction
  dsimp only at h
  have hbnd := actual_boundaries rate rewards C_star C_h u t z
  have hindex : t.val - start rate rewards C_star C_h u t z + 1 +
      (continuingRecords rate rewards C_star C_h u t z).length =
        q.val - start rate rewards C_star C_h u t z := by omega
  change (match (sourceRecords rate rewards C_star C_h u t z)[
    t.val - start rate rewards C_star C_h u t z + 1 +
      (continuingRecords rate rewards C_star C_h u t z).length]? with
    | none => True | some r => _) at h
  rw [hindex, futureRecord_lookup rate rewards C_star C_h u t z q hfuture] at h
  dsimp only at h ⊢
  cases hcoord : (futureRecord rate rewards C_star C_h u t z q hfuture).output.preparation.coordinator
    <;> try trivial
  rename_i registers owned base outcome
  cases outcome <;> try trivial
  simp only [hcoord] at h
  obtain ⟨_, hpay, _, _, _, _, _, hsigma, hbase, _, hgrid, _, selected,
    _, _, _, _, hf⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hpay, hsigma]
    exact congrArg Fin.val (callRecord_time rate rewards C_star C_h u t z)
  · rw [hpay]; exact hbase
  · rw [hpay]; exact hgrid
  · intro i
    obtain ⟨old, memory, _, _, _, _, _, _, _, _, hp, _⟩ := hf i
    exact ⟨{ old with status := .unoccupied }, memory, hp, rfl⟩
  · rw [hpay]
    simp only [DispatchCut.downView, DispatchCut.selection, selectionAt,
      dite_eq_left hframes.1, Option.map_some]

private theorem collection_baseline_zero
    (r : RoundRecord (p := p) (rate := rate)) (s : ℕ)
    (c : RecordedQueueRun.RoundInput p.K)
    (hc : ReferenceLaterCollectionArrivalReadout.laterCollectionReadout s r = some c) :
    ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 r = some c := by
  have hd := (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout_domain s r).mp
    (by rw [hc]; rfl)
  unfold ReferenceLaterCollectionArrivalReadout.laterCollectionReadout at hc ⊢
  simp only [dite_eq_left hd.1] at hc ⊢
  cases hcut : r.output.preparation.coordinator <;> simp only [hcut] at hd hc ⊢ <;> try contradiction
  · rename_i outcome
    cases outcome <;> simp_all
    omega
  · rename_i outcome
    cases outcome <;> simp_all

private theorem dispatch_live_origin (x : RoundInput p rate) :
    match dispatch x with
    | .live registers owned base _ => x.state.coordinator = .live registers owned base
    | _ => True := by
  unfold dispatch
  cases hs : x.state.coordinator with
  | first => trivial
  | live registers owned base =>
    simp only [CoordinatorRoundDispatch.dispatch]
    cases CoordinatorRoundDispatch.dispatchLive _ <;> rfl
  | collection payload ledger saved =>
    by_cases hc : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
    · simp only [dite_eq_left hc, CoordinatorRoundDispatch.dispatch]
      cases CoordinatorRoundDispatch.dispatchCollection _ <;> trivial
    · simp only [dite_eq_right hc]
  | dagger => trivial

/-- The endpoint cutoff has a present collection cell at both baselines,
retaining the old installed rate. The actual clock uses a strict boundary. -/
theorem firstReplacement_future_cutoff_readout (z : Z) (q : Fin p.T)
    (hfuture : t.val + 1 < q.val)
    (hend : q.val - (t.val + 1) = (continuingRecords rate rewards C_star C_h u t z).length) :
    let r := futureRecord rate rewards C_star C_h u t z q hfuture
    match r.output.preparation.coordinator with
    | .live registers owned base (.cutoffChosen dispatched _ _ _ _ _ _ _ _ selected) =>
      ∃ c : RecordedQueueRun.RoundInput p.K,
        ReferenceLaterCollectionArrivalReadout.laterCollectionReadout
          (start rate rewards C_star C_h u t z) r = some c ∧
        ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 r = some c ∧
        c = ReferenceLaterCollectionArrivalReadout.laterCutoffCollectionInput
          r registers owned base dispatched selected ∧
        c.rate = registers.payload.rate ∧
        c.enabled = decide (q.val + 1 <
          FollowerCutoffScan.gridBoundary p rate.eta.val registers.payload.sigma) ∧
        c.reward = (fun a => ((rewards q a).val : ℝ) / (D p : ℝ)) ∧
        ∃ (payload : Payload rate) (started : CoordinatorPhaseClock.StartRoundResult p)
          (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ)
          (out : CoordinatorRecordingOperation.Output p),
          CoordinatorRecorderComplementBridge.run
            (collectionRecordingInput r.output.preparation payload started weights) = some out ∧
          r.coordinatorDiagnostics.recording = some out ∧ out.gateArm = c.recordedArm ∧
          (∀ a, CoordinatorCollectionLedger.localArrival
            (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder out) a =
              RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a) ∧
          ∀ a, c.recordedArm = some a →
            r.actions (ActiveRoundActions.coordinator p.two_le_m) = a ∧
            r.gridFeedback (ActiveRoundActions.coordinator p.two_le_m) = rewards q a ∧
            out.rawArrival = Nat.floor ((D p : ℝ) * rate.eta.val *
              (((rewards q a).val : ℝ) / (D p : ℝ)) / c.rate a)
    | _ => True := by
  have h := firstReplacement_future_cutoff_prepared rate rewards C_star C_h u t z q hfuture hend
  dsimp only at h ⊢
  cases hcoord : (futureRecord rate rewards C_star C_h u t z q hfuture).output.preparation.coordinator
    <;> try trivial
  rename_i registers owned base outcome
  cases outcome <;> try trivial
  rename_i dispatched hstart ledger hinit hledger hdomain hclock hpending hnone selected
  simp only [hcoord] at h
  obtain ⟨hsigma, hbase, hgrid, hf, _⟩ := h
  have ho : ReferenceLaterCollectionArrivalReadout.preparedFollowersUnoccupied
      (futureRecord rate rewards C_star C_h u t z q hfuture) := by
    intro i
    obtain ⟨state, memory, hp, hu⟩ := hf i
    simp only [hp, hu]
  let c := ReferenceLaterCollectionArrivalReadout.laterCutoffCollectionInput
    (futureRecord rate rewards C_star C_h u t z q hfuture) registers owned base dispatched selected
  have hread : ReferenceLaterCollectionArrivalReadout.laterCollectionReadout
      (start rate rewards C_star C_h u t z)
      (futureRecord rate rewards C_star C_h u t z q hfuture) = some c := by
    simp only [ReferenceLaterCollectionArrivalReadout.laterCollectionReadout,
      dite_eq_left ho, hcoord, dite_eq_left hbase, c]
  obtain ⟨payload, _ledger, started, weights, out, _hcall, hrun, hdiag, hgate, hraw,
    hrate, hreward, howner⟩ := ReferenceLaterCollectionArrivalReadout.laterCollectionReadout_physical
      rate rewards C_star C_h z.val (futureIndex rate rewards C_star C_h u t z q hfuture) c hread
  have htime := (futureRecord_fields rate rewards C_star C_h u t z q hfuture).1
  change ((ReferenceCompletePhysicalHistory.completeSuffixRecords rate z.val rewards C_star C_h).get
    (futureIndex rate rewards C_star C_h u t z q hfuture)).input.time = q at htime
  refine ⟨c, hread, collection_baseline_zero rate _ _ _ hread, rfl, rfl, ?_, ?_, ?_⟩
  · have hdispatch : dispatch (futureRecord rate rewards C_star C_h u t z q hfuture).input =
        (futureRecord rate rewards C_star C_h u t z q hfuture).output.preparation.coordinator := by
      rw [(futureRecord rate rewards C_star C_h u t z q hfuture).output_eq]
      rfl
    have hstate := dispatch_live_origin rate
      (futureRecord rate rewards C_star C_h u t z q hfuture).input
    rw [hdispatch, hcoord] at hstate
    have hclockAt := ReferenceFirstReplacementNextFollowerStep.complete_suffix_record_clock
      rate z.val rewards C_star C_h (futureIndex rate rewards C_star C_h u t z q hfuture)
    change ReferenceCoordinatorClockDomains.clockAt _ _ _
      (futureRecord rate rewards C_star C_h u t z q hfuture).input.state at hclockAt
    simp only [ReferenceCoordinatorClockDomains.clockAt, hstate] at hclockAt
    have hboundary : registers.priorClock.g =
        FollowerCutoffScan.gridBoundary p rate.eta.val registers.payload.sigma := by
      simpa only [CoordinatorPhaseClock.boundaryFromSigma, hclockAt.2.2.1] using hclockAt.2.1.1
    have hg : dispatched.startResult.clock.g =
        FollowerCutoffScan.gridBoundary p rate.eta.val registers.payload.sigma := by
      exact (congrArg CoordinatorPhaseClock.ClockRegisters.g hclock).trans hboundary
    dsimp only [c, ReferenceLaterCollectionArrivalReadout.laterCutoffCollectionInput]
    simp only [CoordinatorRecordingOperation.isFrozen,
      CoordinatorRecordingOperation.sourceCalendarRound,
      CoordinatorRecorderComplementBridge.recorderInput,
      CoordinatorRecorderComplementBridge.recorderInputWithWeights,
      CoordinatorRecorderComplementBridge.sourceStart, collectionRecordingInput,
      hg, (futureRecord_fields rate rewards C_star C_h u t z q hfuture).1]
    have htimeRaw := congrArg Fin.val (futureRecord_fields rate rewards C_star C_h u t z q hfuture).1
    change ((ReferenceCompletePhysicalHistory.completeSuffixRecords rate z.val rewards C_star C_h).get
      (futureIndex rate rewards C_star C_h u t z q hfuture)).input.time.val = q.val at htimeRaw
    simp only [Nat.zero_lt_succ, true_and, not_le]
  · simpa only [htime] using hreward
  · refine ⟨payload, started, weights, out, hrun, hdiag, hgate, hraw, ?_⟩
    intro a ha
    obtain ⟨_valid, _, _, _, _, haction, _, _, hfeedback, hfloor⟩ := howner a ha
    refine ⟨haction, ?_, ?_⟩
    · simpa only [futureRecord, sourceRecords, htime] using hfeedback
    · simpa only [hrate, htime] using hfloor

private theorem measurable_option_elim {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    (f : A → B) (hf : Measurable f) (b : B) :
    Measurable (fun o : Option A => o.elim b f) := by
  have hsum : Measurable (fun o : Option A => Equiv.optionEquivSumPUnit A o) :=
    comap_measurable _
  convert (hf.sumElim measurable_const).comp hsum using 1
  funext o
  cases o <;> rfl

/-- A literal finite tag projection of the original full record code. -/
def continuingCode (code : ReferenceActiveHorizonMeasurability.RoundRecordCode
    (p := p) (rate := rate)) : Bool :=
  ReferenceCompleteNumericalBranchObservation.incomingLiveTag rate code &&
    (ReferenceCoordinatorRecorderCallTrace.cell code).elim false (fun c => c.2.1)

theorem measurable_continuingCode : Measurable (continuingCode rate) := by
  have htag : Measurable (fun c : CoordinatorCode p rate =>
      match c with | .inr (.inl _) => true | _ => false) :=
    measurable_const.sumElim
      (measurable_const.sumElim (measurable_const.sumElim measurable_const))
  have hi : Measurable (fun code : ReferenceActiveHorizonMeasurability.RoundRecordCode
      (p := p) (rate := rate) =>
      ReferenceCompleteNumericalBranchObservation.incomingLiveTag rate code) :=
    htag.comp (measurable_fst.comp (measurable_fst.comp measurable_snd))
  have hc := (measurable_option_elim (fun c => c.2.1)
    (measurable_fst.comp measurable_snd) false).comp
    (ReferenceCoordinatorRecorderCallTrace.measurable_cell (p := p) (rate := rate))
  exact (measurable_of_countable (fun v : Bool × Bool => v.1 && v.2)).comp (hi.prodMk hc)

private theorem incomingLiveTag_actual (r : RoundRecord (p := p) (rate := rate)) :
    ReferenceCompleteNumericalBranchObservation.incomingLiveTag rate
      (ReferenceActiveHorizonMeasurability.roundRecordCode r) =
      match r.output.preparation.coordinator with | .live .. => true | _ => false := by
  rw [r.output.preparation.coordinator_eq]
  cases hc : r.input.state.coordinator with
  | first =>
    rw [dispatch_first r.input hc]
    simp only [ReferenceCompleteNumericalBranchObservation.incomingLiveTag,
      ReferenceActiveHorizonMeasurability.roundRecordCode, encodeState, encodeCoordinator, hc]
  | dagger =>
    rw [dispatch_dagger r.input hc]
    simp only [ReferenceCompleteNumericalBranchObservation.incomingLiveTag,
      ReferenceActiveHorizonMeasurability.roundRecordCode, encodeState, encodeCoordinator, hc]
  | live registers owned base =>
    simp only [dispatch, hc, CoordinatorRoundDispatch.dispatch,
      ReferenceCompleteNumericalBranchObservation.incomingLiveTag,
      ReferenceActiveHorizonMeasurability.roundRecordCode, encodeState, encodeCoordinator]
    rfl
  | collection payload ledger proposal =>
    by_cases hv : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
    · simp only [dispatch, hc, dite_eq_left hv, CoordinatorRoundDispatch.dispatch,
        ReferenceCompleteNumericalBranchObservation.incomingLiveTag,
        ReferenceActiveHorizonMeasurability.roundRecordCode, encodeState, encodeCoordinator]
      rfl
    · simp only [dispatch, hc, dite_eq_right hv,
        ReferenceCompleteNumericalBranchObservation.incomingLiveTag,
        ReferenceActiveHorizonMeasurability.roundRecordCode, encodeState, encodeCoordinator]

theorem continuingCode_actual (r : RoundRecord (p := p) (rate := rate)) :
    continuingCode rate (ReferenceActiveHorizonMeasurability.roundRecordCode r) =
      ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen r := by
  have hframes := ReferenceCoordinatorRecorderCallCorrespondence.actual_call_frames r
  have hsel : ReferenceCoordinatorRecorderCallTrace.selection
      (ReferenceActiveHorizonMeasurability.roundRecordCode r) =
        r.output.preparation.coordinator.selection.map
          ReferenceLiveDispatchOutputMeasurability.encodeSelection := by
    rw [r.output.preparation.coordinator_eq]
    rfl
  unfold continuingCode ReferenceCoordinatorRecorderCallTrace.cell
  rw [incomingLiveTag_actual, hsel]
  cases hc : r.output.preparation.coordinator <;>
    simp only [hc, ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen,
      Bool.false_and]
  rename_i registers owned base outcome
  cases outcome <;> simp only [DispatchCut.selection, Option.map_none, Option.elim_none,
    Bool.and_false]
  all_goals
    simp only [hc] at hframes
    simp only [selectionAt, dite_true, Option.map_some, Option.elim_some,
      Bool.true_and, ReferenceCoordinatorRecorderCallTrace.live,
      ReferenceLiveDispatchOutputMeasurability.encodeSelection,
      ReferenceActiveHorizonMeasurability.roundRecordCode]
  · apply decide_eq_false
    exact hframes.1
  · apply decide_eq_true
    exact hframes.1

/-- The strict-past tag vector, on the unchanged original source. -/
def pastContinuing (q : Fin p.T) (z : Z) : Fin q.val → Bool := fun j =>
  (ReferenceInspectedPastRoundObservations.pastRoundObservations rate rewards C_star C_h
    q.val (Nat.le_of_lt q.isLt) z.val j).elim false (continuingCode rate)

theorem measurable_pastContinuing (control0 : ContinuousLearningRows.TimeControl p)
    (q : Fin p.T) : Measurable[priorField rate rewards C_star C_h u t control0 q.val]
      (pastContinuing rate rewards C_star C_h u t q) := by
  let : MeasurableSpace Z := priorField rate rewards C_star C_h u t control0 q.val
  have hp := (ReferenceInspectedPastRoundObservations.pastRoundObservations_measurable_in_inspectedHistorySpace
    rate rewards C_star C_h q.val (Nat.le_of_lt q.isLt)).mono
      (ReferenceSourceOwnHistoryContainment.inspectedHistorySpace_le_sourcePrefixFiltration
        rate rewards C_star C_h control0 q.val (Nat.le_of_lt q.isLt)) le_rfl
  have hz : @Measurable Z (BootstrapPrivateRoundStreams.SourceInput p)
      (priorField rate rewards C_star C_h u t control0 q.val)
      (sourcePrefixFiltration control0 (q.val + 1)) Subtype.val := comap_measurable _
  apply measurable_pi_iff.mpr
  intro j
  exact (measurable_option_elim _ (measurable_continuingCode rate) false).comp
    ((measurable_pi_apply j).comp (hp.comp hz))

/-- All original post-birth records strictly before q continue. This reads
only earlier dispatch codes and has no decoder-success or overflow mask. -/
def priorSlice (q : Fin p.T) (z : Z) : Bool :=
  decide (∀ j : Fin q.val, t.val + 1 ≤ j.val →
    pastContinuing rate rewards C_star C_h u t q z j = true)

theorem measurable_priorSlice (control0 : ContinuousLearningRows.TimeControl p)
    (q : Fin p.T) : Measurable[priorField rate rewards C_star C_h u t control0 q.val]
      (priorSlice rate rewards C_star C_h u t q) :=
  (measurable_of_countable (fun flags : Fin q.val → Bool =>
    decide (∀ j : Fin q.val, t.val + 1 ≤ j.val → flags j = true))).comp
      (measurable_pastContinuing rate rewards C_star C_h u t control0 q)

theorem priorSlice_congr (control0 : ContinuousLearningRows.TimeControl p)
    (z z' : Z) (q : Fin p.T)
    (hprefix : sourcePrefix control0 q.val z.val = sourcePrefix control0 q.val z'.val) :
    priorSlice rate rewards C_star C_h u t q z =
      priorSlice rate rewards C_star C_h u t q z' := by
  have hm := measurable_priorSlice rate rewards C_star C_h u t control0 q
  rw [priorField, sourcePrefixFiltration_succ, MeasurableSpace.comap_comp] at hm
  exact hm.factorsThrough hprefix

private theorem le_takeWhile_length_iff {A : Type*} (f : A → Bool)
    (xs : List A) (n : ℕ) (hn : n ≤ xs.length) :
    n ≤ (xs.takeWhile f).length ↔ ∀ k < n, (xs[k]?).any f = true := by
  induction xs generalizing n with
  | nil =>
    have hz : n = 0 := by simpa using hn
    subst n
    simp
  | cons a xs ih =>
    cases n with
    | zero => simp
    | succ n =>
      have hn' : n ≤ xs.length := by simpa using hn
      cases ha : f a with
      | false =>
        simp only [List.takeWhile, ha, List.length_nil]
        constructor
        · intro h
          omega
        · intro h
          have h0 := h 0 (Nat.zero_lt_succ n)
          simp only [List.getElem?_cons_zero, Option.any_some, ha, Bool.false_eq_true] at h0
      | true =>
        simp only [List.takeWhile, ha, List.length_cons, Nat.succ_le_succ_iff]
        rw [ih n hn']
        constructor
        · intro h k hk
          cases k with
          | zero => simpa only [List.getElem?_cons_zero, Option.any_some] using ha
          | succ k => simpa only [List.getElem?_cons_succ] using h k (by omega)
        · intro h k hk
          simpa only [List.getElem?_cons_succ] using h (k + 1) (by omega)

/-- The earlier-code test is exactly the existing slice's endpoint selector. -/
theorem priorSlice_eq (z : Z) (q : Fin p.T) (hfuture : t.val + 1 < q.val) :
    priorSlice rate rewards C_star C_h u t q z =
      decide (q.val - (t.val + 1) ≤ (continuingRecords rate rewards C_star C_h u t z).length) := by
  let R := sourceRecords rate rewards C_star C_h u t z
  let s := start rate rewards C_star C_h u t z
  let v := t.val - s
  let n := q.val - (t.val + 1)
  have hb := actual_boundaries rate rewards C_star C_h u t z
  have hlen := sourceRecords_length rate rewards C_star C_h u t z
  have hs : s ≤ t.val := by dsimp only [s]; omega
  have hspan : n ≤ (R.drop (v + 1)).length := by
    simp only [List.length_drop]
    dsimp only [n, R, v, s]
    rw [hlen]
    have hq := q.isLt
    omega
  have hequiv := le_takeWhile_length_iff
    ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen (R.drop (v + 1)) n hspan
  apply Bool.eq_iff_iff.mpr
  simp only [priorSlice, decide_eq_true_eq]
  change (∀ j : Fin q.val, t.val + 1 ≤ j.val →
    pastContinuing rate rewards C_star C_h u t q z j = true) ↔
      n ≤ ((R.drop (v + 1)).takeWhile
        ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen).length
  rw [hequiv]
  have hrecord (j : Fin q.val) (hj : t.val + 1 ≤ j.val) :
      pastContinuing rate rewards C_star C_h u t q z j =
        (R[j.val - s]?).any ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen := by
    have hjs : ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h ≤ j.val := by
      change s ≤ j.val; omega
    have hr : actualRecord rate rewards C_star C_h
        (Fin.castLE (Nat.le_of_lt q.isLt) j) z.val = R[j.val - s]? := by
      simp only [actualRecord, Fin.val_castLE, ite_eq_left hjs]
      rfl
    simp only [pastContinuing, ReferenceInspectedPastRoundObservations.pastRoundObservations, hr]
    cases hh : R[j.val - s]? with
    | none => rfl
    | some r => simpa only [Option.map_some, Option.elim_some, Option.any_some] using
        continuingCode_actual rate r
  constructor
  · intro h k hk
    let j : Fin q.val := ⟨t.val + 1 + k, by dsimp only [n] at hk; omega⟩
    have hj : t.val + 1 ≤ j.val := by dsimp only [j]; omega
    have he := hrecord j hj
    have hi : j.val - s = v + 1 + k := by dsimp only [j, v]; omega
    rw [List.getElem?_drop, ← hi, ← he]
    exact h j hj
  · intro h j hj
    have hk : j.val - (t.val + 1) < n := by dsimp only [n]; omega
    have hh := h (j.val - (t.val + 1)) hk
    rw [List.getElem?_drop] at hh
    have hi : v + 1 + (j.val - (t.val + 1)) = j.val - s := by dsimp only [v]; omega
    rw [hi, ← hrecord j hj] at hh
    exact hh

def futureTag (z : Z) (q : Fin p.T) (hfuture : t.val + 1 < q.val) :=
  ReferenceFirstCollectionRenewalNextRecordingPriorView.dispatchTag
    (futureRecord rate rewards C_star C_h u t z q hfuture).input

/-- The only exposed cases are the existing continuing slice and its first
noncontinuing endpoint when the actual dispatch chooses cutoff. -/
def sliceBranch (z : Z) (q : Fin p.T) (hfuture : t.val + 1 < q.val) : Option Bool :=
  if q.val - (t.val + 1) ≤ (continuingRecords rate rewards C_star C_h u t z).length then
    match futureTag rate rewards C_star C_h u t z q hfuture with
    | some (.inr (.inr (.inr (_, cutoff)))) => some cutoff
    | _ => none
  else none

private theorem dispatchTag_congr_all (left right : RoundInput p rate)
    (hstate : left.state = right.state) (htime : left.time = right.time) :
    ReferenceFirstCollectionRenewalNextRecordingPriorView.dispatchTag left =
      ReferenceFirstCollectionRenewalNextRecordingPriorView.dispatchTag right := by
  cases hs : left.state.coordinator with
  | live registers owned base =>
    exact ReferenceFirstCollectionRenewalNextRecordingPriorView.dispatchTag_congr
      left right hstate htime (by rw [hs]; trivial)
  | dagger =>
    exact ReferenceFirstCollectionRenewalNextRecordingPriorView.dispatchTag_congr
      left right hstate htime (by rw [hs]; trivial)
  | first =>
    simp only [ReferenceFirstCollectionRenewalNextRecordingPriorView.dispatchTag,
      dispatch, hs, ← hstate, CoordinatorRoundDispatch.dispatch]
    rfl
  | collection payload ledger saved =>
    by_cases hd : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
    · simp only [ReferenceFirstCollectionRenewalNextRecordingPriorView.dispatchTag,
        dispatch, hs, ← hstate, dite_eq_left hd, CoordinatorRoundDispatch.dispatch]
      rfl
    · simp only [ReferenceFirstCollectionRenewalNextRecordingPriorView.dispatchTag,
        dispatch, hs, ← hstate, dite_eq_right hd]

theorem futureTag_congr (control0 : ContinuousLearningRows.TimeControl p)
    (z z' : Z) (q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (hprefix : sourcePrefix control0 q.val z.val = sourcePrefix control0 q.val z'.val) :
    futureTag rate rewards C_star C_h u t z q hfuture =
      futureTag rate rewards C_star C_h u t z' q hfuture := by
  apply dispatchTag_congr_all
  · exact futureState_congr rate rewards C_star C_h u t control0 z z' q hfuture hprefix
  · exact (futureRecord_fields rate rewards C_star C_h u t z q hfuture).1.trans
      (futureRecord_fields rate rewards C_star C_h u t z' q hfuture).1.symm

theorem sliceBranch_congr (control0 : ContinuousLearningRows.TimeControl p)
    (z z' : Z) (q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (hprefix : sourcePrefix control0 q.val z.val = sourcePrefix control0 q.val z'.val) :
    sliceBranch rate rewards C_star C_h u t z q hfuture =
      sliceBranch rate rewards C_star C_h u t z' q hfuture := by
  have hp := priorSlice_congr rate rewards C_star C_h u t control0 z z' q hprefix
  rw [priorSlice_eq rate rewards C_star C_h u t z q hfuture,
    priorSlice_eq rate rewards C_star C_h u t z' q hfuture] at hp
  have hi : (q.val - (t.val + 1) ≤ (continuingRecords rate rewards C_star C_h u t z).length) ↔
      (q.val - (t.val + 1) ≤ (continuingRecords rate rewards C_star C_h u t z').length) := by
    exact decide_eq_decide.mp hp
  simp only [sliceBranch, hi, futureTag_congr rate rewards C_star C_h u t control0 z z' q hfuture hprefix]

/-- Replace the whole selected suffix at q on the SAME genuine renewal source.
The original t through q-1 controls, private arrays, and private J remain. -/
def withFutureSuffix (z : Z) (q : Fin p.T) (_hfuture : t.val + 1 < q.val)
    (suffix : Fin p.T → ContinuousLearningRows.TimeControl p) : Z :=
  ReferenceFirstCollectionRenewalPastLocality.renewalSourceWithSuffix
    rate rewards C_star C_h u t z (fun j => if j.val < q.val then
      (z.val.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z.val)).2 j else suffix j)

theorem withFutureSuffix_val (z : Z) (q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (suffix : Fin p.T → ContinuousLearningRows.TimeControl p) :
    (withFutureSuffix rate rewards C_star C_h u t z q hfuture suffix).val =
      ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix z.val q suffix := by
  apply Prod.ext
  · refine Prod.ext rfl ?_
    funext row
    by_cases hr : row = ActualInitializationPhysicalStep.selectedRowIndex p z.val
    · subst row
      simp only [withFutureSuffix, ReferenceFirstCollectionRenewalPastLocality.renewalSourceWithSuffix,
        ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix, Function.update_self]
      refine Prod.ext rfl ?_
      funext j
      by_cases hj : j.val < t.val
      · have hjq : j.val < q.val := by omega
        simp only [hj, hjq, ite_true]
      · simp only [hj, ite_false]
    · simp only [withFutureSuffix, ReferenceFirstCollectionRenewalPastLocality.renewalSourceWithSuffix,
        ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix, Function.update_of_ne hr]
  · rfl

def withFutureControl (z : Z) (q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (control : ContinuousLearningRows.TimeControl p) : Z :=
  withFutureSuffix rate rewards C_star C_h u t z q hfuture (fun j => if j = q then control
    else (z.val.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z.val)).2 j)

theorem withFutureControl_val (z : Z) (q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (control : ContinuousLearningRows.TimeControl p) :
    (withFutureControl rate rewards C_star C_h u t z q hfuture control).val =
      ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p q z.val control := by
  rw [withFutureControl, withFutureSuffix_val]
  apply Prod.ext
  · refine Prod.ext rfl ?_
    funext row
    by_cases hr : row = ActualInitializationPhysicalStep.selectedRowIndex p z.val
    · subst row
      simp only [ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix,
        ReferenceFixedTimeSourceControlCoupling.replaceSourceControl,
        ActualInitializationPhysicalStep.selectedRowIndex,
        ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex, Function.update_self]
      refine Prod.ext rfl ?_
      funext j
      by_cases hj : j = q
      · subst j
        simp
      · by_cases hlt : j.val < q.val <;> simp [hj, hlt]
    · have hr' : row ≠ PrivateSourceStreams.coordinatorIndex p z.val.2.1.2 := hr
      simp only [ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix,
        ReferenceFixedTimeSourceControlCoupling.replaceSourceControl,
        ActualInitializationPhysicalStep.selectedRowIndex,
        ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex,
        Function.update_of_ne hr']
  · rfl

theorem withFutureControl_private (z : Z) (q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (control : ContinuousLearningRows.TimeControl p) :
    let changed := withFutureControl rate rewards C_star C_h u t z q hfuture control
    changed.val.1.1 = z.val.1.1 ∧ changed.val.2 = z.val.2 ∧
      ActualInitializationPhysicalStep.selectedRowIndex p changed.val =
        ActualInitializationPhysicalStep.selectedRowIndex p z.val := by
  dsimp only
  rw [withFutureControl_val]
  exact ⟨rfl, rfl, rfl⟩

theorem withFutureSuffix_prefix (control0 : ContinuousLearningRows.TimeControl p)
    (z : Z) (q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (suffix : Fin p.T → ContinuousLearningRows.TimeControl p) :
    sourcePrefix control0 q.val
      (withFutureSuffix rate rewards C_star C_h u t z q hfuture suffix).val =
        sourcePrefix control0 q.val z.val := by
  rw [withFutureSuffix_val]
  apply Prod.ext
  · refine Prod.ext rfl ?_
    funext row
    by_cases hr : row = ActualInitializationPhysicalStep.selectedRowIndex p z.val
    · subst row
      simp only [sourcePrefix, ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix,
        ActualInitializationPhysicalStep.selectedRowIndex, Function.update_self]
      refine Prod.ext rfl ?_
      funext j
      by_cases hj : j.val < q.val <;> simp only [hj, ite_true, ite_false]
    · have hr' : row ≠ PrivateSourceStreams.coordinatorIndex p z.val.2.1.2 := hr
      simp only [sourcePrefix, ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix,
        ActualInitializationPhysicalStep.selectedRowIndex, Function.update_of_ne hr']
  · rfl

def priorObserver (control0 : ContinuousLearningRows.TimeControl p)
    (z : Z) (q : Fin p.T) (hfuture : t.val + 1 < q.val) : Z :=
  withFutureSuffix rate rewards C_star C_h u t z q hfuture (fun _ => control0)

theorem priorObserver_val (control0 : ContinuousLearningRows.TimeControl p)
    (z : Z) (q : Fin p.T) (hfuture : t.val + 1 < q.val) :
    (priorObserver rate rewards C_star C_h u t control0 z q hfuture).val =
      sourcePrefix control0 q.val z.val := by
  rw [priorObserver, withFutureSuffix_val, sourcePrefix_eq_suffix]

theorem measurable_priorObserver (control0 : ContinuousLearningRows.TimeControl p)
    (q : Fin p.T) (hfuture : t.val + 1 < q.val) :
    Measurable[priorField rate rewards C_star C_h u t control0 q.val]
      (fun z : Z => priorObserver rate rewards C_star C_h u t control0 z q hfuture) := by
  apply Measurable.subtype_mk
  change Measurable[priorField rate rewards C_star C_h u t control0 q.val]
    (fun z : Z => (priorObserver rate rewards C_star C_h u t control0 z q hfuture).val)
  have heq : (fun z : Z => (priorObserver rate rewards C_star C_h u t control0 z q hfuture).val) =
      sourcePrefix control0 q.val ∘ Subtype.val := funext fun z => priorObserver_val rate rewards C_star C_h u t control0 z q hfuture
  rw [heq]
  change @Measurable Z (BootstrapPrivateRoundStreams.SourceInput p)
    (MeasurableSpace.comap Subtype.val (sourcePrefixFiltration control0 (q.val + 1)))
    _ (sourcePrefix control0 q.val ∘ Subtype.val)
  rw [sourcePrefixFiltration_succ, MeasurableSpace.comap_comp]
  exact comap_measurable _

theorem futureTag_eq (z : Z) (q : Fin p.T) (hfuture : t.val + 1 < q.val) :
    futureTag rate rewards C_star C_h u t z q hfuture =
      match (futureRecord rate rewards C_star C_h u t z q hfuture).output.preparation.coordinator with
      | .live _ _ _ out => some (ReferenceFirstCollectionRenewalNextRecordingPriorView.eraseArm
          (ReferenceLiveDispatchOutputMeasurability.outcomeData out))
      | _ => none := by
  unfold futureTag ReferenceFirstCollectionRenewalNextRecordingPriorView.dispatchTag
  have hd : dispatch (futureRecord rate rewards C_star C_h u t z q hfuture).input =
      (futureRecord rate rewards C_star C_h u t z q hfuture).output.preparation.coordinator := by
    rw [(futureRecord rate rewards C_star C_h u t z q hfuture).output_eq]
    rfl
  rw [hd]
  cases (futureRecord rate rewards C_star C_h u t z q hfuture).output.preparation.coordinator <;> rfl

private theorem takeWhile_endpoint_false {A : Type*} (f : A → Bool)
    (xs : List A) (n : ℕ) (a : A) (hget : xs[n]? = some a)
    (hlen : (xs.takeWhile f).length = n) : f a = false := by
  induction xs generalizing n with
  | nil => simp at hget
  | cons head tail ih =>
    cases hh : f head with
    | false =>
      have hz : n = 0 := by simpa [List.takeWhile, hh] using hlen.symm
      rw [hz] at hget
      have heq : head = a := by simpa using hget
      simpa only [heq] using hh
    | true =>
      cases n with
      | zero => simp [List.takeWhile, hh] at hlen
      | succ n =>
        exact ih n (by simpa using hget) (by simpa [List.takeWhile, hh] using hlen)

private theorem continuing_at_future (z : Z) (q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (hk : q.val - (t.val + 1) < (continuingRecords rate rewards C_star C_h u t z).length) :
    ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen
      (futureRecord rate rewards C_star C_h u t z q hfuture) = true := by
  rw [futureRecord_eq_continuing rate rewards C_star C_h u t z q hfuture hk]
  exact ReferenceFirstReplacementLiveFollowerPrefix.continuingTail_mem _ _ _ (List.get_mem _ _)

private theorem noncontinuing_at_endpoint (z : Z) (q : Fin p.T)
    (hfuture : t.val + 1 < q.val)
    (hend : q.val - (t.val + 1) = (continuingRecords rate rewards C_star C_h u t z).length) :
    ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen
      (futureRecord rate rewards C_star C_h u t z q hfuture) = false := by
  apply takeWhile_endpoint_false _
    ((sourceRecords rate rewards C_star C_h u t z).drop
      (t.val - start rate rewards C_star C_h u t z + 1))
    (q.val - (t.val + 1))
  · rw [List.getElem?_drop]
    have hb := actual_boundaries rate rewards C_star C_h u t z
    have hi : t.val - start rate rewards C_star C_h u t z + 1 +
        (q.val - (t.val + 1)) = q.val - start rate rewards C_star C_h u t z := by omega
    rw [hi]
    exact futureRecord_lookup rate rewards C_star C_h u t z q hfuture
  · exact hend.symm

/-- Exact geometry of the two selected physical branches. -/
theorem sliceBranch_geometry (z : Z) (q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (b : Bool) (hb : sliceBranch rate rewards C_star C_h u t z q hfuture = some b) :
    (b = false → q.val - (t.val + 1) < (continuingRecords rate rewards C_star C_h u t z).length) ∧
    (b = true → q.val - (t.val + 1) = (continuingRecords rate rewards C_star C_h u t z).length) := by
  have hn : q.val - (t.val + 1) ≤ (continuingRecords rate rewards C_star C_h u t z).length := by
    by_contra hn
    simp only [sliceBranch, ite_eq_right hn] at hb
    cases hb
  have htag := hb
  simp only [sliceBranch, ite_eq_left hn, futureTag_eq] at htag
  cases hc : (futureRecord rate rewards C_star C_h u t z q hfuture).output.preparation.coordinator
    <;> simp only [hc] at htag <;> try contradiction
  rename_i out
  cases out <;> simp only [ReferenceFirstCollectionRenewalNextRecordingPriorView.eraseArm,
    ReferenceLiveDispatchOutputMeasurability.outcomeData] at htag <;> try contradiction
  · have he : b = true := (Option.some.inj htag).symm
    refine ⟨by intro h; simp only [he, Bool.true_eq_false] at h, fun _ => ?_⟩
    by_contra hne
    have hlt : q.val - (t.val + 1) < (continuingRecords rate rewards C_star C_h u t z).length := by omega
    have hf := continuing_at_future rate rewards C_star C_h u t z q hfuture hlt
    simp only [ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen, hc] at hf
    cases hf
  · have he : b = false := (Option.some.inj htag).symm
    refine ⟨fun _ => ?_, by intro h; simp only [he, Bool.false_eq_true] at h⟩
    by_contra hlt
    have hend : q.val - (t.val + 1) = (continuingRecords rate rewards C_star C_h u t z).length := by omega
    have hf := noncontinuing_at_endpoint rate rewards C_star C_h u t z q hfuture hend
    simp only [ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen, hc] at hf
    cases hf

/-- Both ordinary families are produced from the actual source, never supplied. -/
theorem slice_prepared (z : Z) (q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (b : Bool) (hb : sliceBranch rate rewards C_star C_h u t z q hfuture = some b) :
    ∃ states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta,
    ∃ memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p,
      (∀ i, ((futureRecord rate rewards C_star C_h u t z q hfuture).output.preparation.followers.followers i).configuration =
        .ordinary (states i) (memories i)) ∧
      (b = true → ∀ i, (states i).status = .unoccupied) := by
  have hg := sliceBranch_geometry rate rewards C_star C_h u t z q hfuture b hb
  cases b with
  | false =>
    have hk := hg.1 rfl
    have hr := futureRecord_eq_continuing rate rewards C_star C_h u t z q hfuture hk
    have h := continuing_readout rate rewards C_star C_h u t z ⟨q.val - (t.val + 1), hk⟩
    rw [← hr] at h
    obtain ⟨cell, _⟩ := h
    exact ⟨cell.states, cell.memories, cell.ordinary, by intro h; cases h⟩
  | true =>
    have hp := firstReplacement_future_cutoff_prepared rate rewards C_star C_h u t z q hfuture (hg.2 rfl)
    have ht := hb
    simp only [sliceBranch, futureTag_eq] at ht
    split_ifs at ht
    cases hc : (futureRecord rate rewards C_star C_h u t z q hfuture).output.preparation.coordinator
      <;> simp only [hc] at ht <;> try contradiction
    rename_i out
    cases out <;> simp only [ReferenceFirstCollectionRenewalNextRecordingPriorView.eraseArm,
      ReferenceLiveDispatchOutputMeasurability.outcomeData] at ht <;> try contradiction
    simp only [hc] at hp
    choose states memories hordinary hstatus using hp.2.2.2.1
    exact ⟨states, memories, hordinary, fun _ => hstatus⟩

/-- Equal strict prefixes give the complete SAME prepared states and memories
on the selected slice, including active and inactive followers. -/
theorem firstReplacement_future_snapshot_congr (control0 : ContinuousLearningRows.TimeControl p)
    (z z' : Z) (q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (hprefix : sourcePrefix control0 q.val z.val = sourcePrefix control0 q.val z'.val) :
    match sliceBranch rate rewards C_star C_h u t z q hfuture with
    | none => True
    | some b => ∃ states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta,
      ∃ memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p,
      (∀ i, ((futureRecord rate rewards C_star C_h u t z q hfuture).output.preparation.followers.followers i).configuration =
        .ordinary (states i) (memories i)) ∧
      (∀ i, ((futureRecord rate rewards C_star C_h u t z' q hfuture).output.preparation.followers.followers i).configuration =
        .ordinary (states i) (memories i)) ∧
      (b = true → ∀ i, (states i).status = .unoccupied) := by
  cases hb : sliceBranch rate rewards C_star C_h u t z q hfuture with
  | none => trivial
  | some b =>
    have hb' := (sliceBranch_congr rate rewards C_star C_h u t control0 z z' q hfuture hprefix).symm.trans hb
    obtain ⟨states, memories, ho, hu⟩ := slice_prepared rate rewards C_star C_h u t z q hfuture b hb
    obtain ⟨states', memories', ho', _⟩ := slice_prepared rate rewards C_star C_h u t z' q hfuture b hb'
    refine ⟨states, memories, ho, ?_, hu⟩
    intro i
    have hL := ho i
    have hR := ho' i
    rw [(futureRecord rate rewards C_star C_h u t z q hfuture).output_eq] at hL
    rw [(futureRecord rate rewards C_star C_h u t z' q hfuture).output_eq] at hR
    have he := ReferenceFirstCollectionRenewalNextRecordingPriorView.ordinary_preparation_congr _ _
      (futureState_congr rate rewards C_star C_h u t control0 z z' q hfuture hprefix)
      ((futureRecord_fields rate rewards C_star C_h u t z q hfuture).1.trans
        (futureRecord_fields rate rewards C_star C_h u t z' q hfuture).1.symm) i _ _ _ _ hL hR
    rw [he.1, he.2]
    exact ho' i

def futureDownView (z : Z) (q : Fin p.T) (hfuture : t.val + 1 < q.val) :=
  (futureRecord rate rewards C_star C_h u t z q hfuture).output.preparation.coordinator.downView

def futureStatuses (z : Z) (q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (i : Fin (p.m - 1)) : Option (Fin 3) :=
  ReferenceFirstCollectionRenewalNextRecordingPriorView.configurationStatus rate
    ((futureRecord rate rewards C_star C_h u t z q hfuture).output.preparation.followers.followers i).configuration

abbrev ViewData := Option (Bool × (Fin p.K → ℝ)) ×
  (ReferenceDownReception.ChoiceTimeView p rate.eta ×
    Option (Finset (Fin (p.m - 1)) × (Fin (p.m - 1) → Option (Fin 3))))

/-- Literal sender/input-code projections. Collection has no live status
snapshot; LIVE retains every prepared follower status and the full missing set. -/
def viewOnBranch (b : Bool) (z : Z) (q : Fin p.T) (hfuture : t.val + 1 < q.val) :
    Option (ViewData rate) :=
  (futureDownView rate rewards C_star C_h u t z q hfuture).map fun view =>
    (ReferenceFirstCollectionRenewalNextRecordingPriorView.parametersOfTag rate q
      (futureTag rate rewards C_star C_h u t z q hfuture) (some view), view,
      if b then none else some (view.pendingAtChoice,
        futureStatuses rate rewards C_star C_h u t z q hfuture))

/-- Mask only by the original first replacement slice and its cutoff endpoint. -/
def futureRecordingView (z : Z) (q : Fin p.T) (hfuture : t.val + 1 < q.val) :
    Option (ViewData rate) :=
  (sliceBranch rate rewards C_star C_h u t z q hfuture).elim none
    (fun b => viewOnBranch rate rewards C_star C_h u t b z q hfuture)

private theorem slice_phase (z : Z) (q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (b : Bool) (hb : sliceBranch rate rewards C_star C_h u t z q hfuture = some b) :
    match (futureRecord rate rewards C_star C_h u t z q hfuture).input.state.coordinator with
    | .live .. => True | .dagger => True | _ => False := by
  unfold sliceBranch futureTag ReferenceFirstCollectionRenewalNextRecordingPriorView.dispatchTag at hb
  split_ifs at hb
  have horigin := dispatch_live_origin rate (futureRecord rate rewards C_star C_h u t z q hfuture).input
  cases hd : dispatch (futureRecord rate rewards C_star C_h u t z q hfuture).input
    <;> simp only [hd] at hb horigin <;> try contradiction
  rw [horigin]
  trivial

theorem firstReplacement_future_view_congr (control0 : ContinuousLearningRows.TimeControl p)
    (z z' : Z) (q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (hprefix : sourcePrefix control0 q.val z.val = sourcePrefix control0 q.val z'.val) :
    futureRecordingView rate rewards C_star C_h u t z q hfuture =
      futureRecordingView rate rewards C_star C_h u t z' q hfuture := by
  have hbranch := sliceBranch_congr rate rewards C_star C_h u t control0 z z' q hfuture hprefix
  cases hb : sliceBranch rate rewards C_star C_h u t z q hfuture with
  | none => simp only [futureRecordingView, ← hbranch, hb, Option.elim_none]
  | some b =>
    have hstate := futureState_congr rate rewards C_star C_h u t control0 z z' q hfuture hprefix
    have htime := (futureRecord_fields rate rewards C_star C_h u t z q hfuture).1.trans
      (futureRecord_fields rate rewards C_star C_h u t z' q hfuture).1.symm
    have hv : futureDownView rate rewards C_star C_h u t z q hfuture =
        futureDownView rate rewards C_star C_h u t z' q hfuture := by
      unfold futureDownView
      rw [(futureRecord rate rewards C_star C_h u t z q hfuture).output.preparation.coordinator_eq,
        (futureRecord rate rewards C_star C_h u t z' q hfuture).output.preparation.coordinator_eq]
      exact ReferenceFirstCollectionRenewalNextRecordingPriorView.downView_congr _ _ hstate htime
        (slice_phase rate rewards C_star C_h u t z q hfuture b hb)
    have hs := firstReplacement_future_snapshot_congr rate rewards C_star C_h u t control0 z z' q hfuture hprefix
    rw [hb] at hs
    obtain ⟨states, memories, ho, ho', _⟩ := hs
    have hstatus : futureStatuses rate rewards C_star C_h u t z q hfuture =
        futureStatuses rate rewards C_star C_h u t z' q hfuture := by
      funext i
      simp only [futureStatuses, ho i, ho' i]
    simp only [futureRecordingView, ← hbranch, hb, Option.elim_some, viewOnBranch,
      hv, hstatus, futureTag_congr rate rewards C_star C_h u t control0 z z' q hfuture hprefix]

theorem firstReplacement_future_view_factor (control0 : ContinuousLearningRows.TimeControl p)
    (z : Z) (q : Fin p.T) (hfuture : t.val + 1 < q.val) :
    futureRecordingView rate rewards C_star C_h u t z q hfuture =
      futureRecordingView rate rewards C_star C_h u t
        (priorObserver rate rewards C_star C_h u t control0 z q hfuture) q hfuture := by
  apply firstReplacement_future_view_congr rate rewards C_star C_h u t control0
  rw [priorObserver_val, sourcePrefix_sourcePrefix control0 _ _ le_rfl]

private theorem measurable_of_some {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]
    (f : X → A) (hf : Measurable (fun x => some (f x))) : Measurable f := by
  let e : Option A ≃ A ⊕ PUnit := Equiv.optionEquivSumPUnit A
  have hs : Measurable (fun x => e (some (f x))) := measurable_comap_iff.mp hf
  intro v hv
  convert hs hv.inl_image using 1
  ext x
  change f x ∈ v ↔ (Sum.inl (f x) : A ⊕ PUnit) ∈ Sum.inl '' v
  simp only [Set.mem_image, Sum.inl.injEq, exists_eq_right]

theorem measurable_futureInput (q : Fin p.T) (hfuture : t.val + 1 < q.val) :
    Measurable (fun z : Z => (futureRecord rate rewards C_star C_h u t z q hfuture).input) := by
  have hc : Measurable (fun z : Z => encodeState
      (futureRecord rate rewards C_star C_h u t z q hfuture).input.state) := by
    apply measurable_of_some
    have h : Measurable (fun z : Z => incoming rate rewards C_star C_h q z.val) :=
      (measurable_incoming rate rewards C_star C_h q).comp measurable_subtype_coe
    convert h using 1
    funext z
    exact (incoming_future rate rewards C_star C_h u t z q hfuture).symm
  have hs : Measurable (fun z : Z => (futureRecord rate rewards C_star C_h u t z q hfuture).input.state) :=
    measurable_comap_iff.mpr hc
  apply measurable_comap_iff.mpr
  apply Measurable.subtype_mk
  have heq : (fun z : Z => (encodeRoundInput (futureRecord rate rewards C_star C_h u t z q hfuture).input).val) =
      fun z => ((futureRecord rate rewards C_star C_h u t z q hfuture).input.state,
        z.val.1.2, ActualInitializationPhysicalStep.selectedRowIndex p z.val, q, rewards) := by
    funext z
    have hf := futureRecord_fields rate rewards C_star C_h u t z q hfuture
    simp only [encodeRoundInput, hf.1, hf.2.1, hf.2.2.1, hf.2.2.2]
  change Measurable (fun z : Z => (encodeRoundInput (futureRecord rate rewards C_star C_h u t z q hfuture).input).val)
  rw [heq]
  exact hs.prodMk ((measurable_snd.comp (measurable_fst.comp measurable_subtype_coe)).prodMk
    (((BootstrapPrivateRoundStreams.measurable_sourceCoordinatorIndex p).comp measurable_subtype_coe).prodMk
      (measurable_const.prodMk measurable_const)))

theorem measurable_futureRecordingView_ambient (control0 : ContinuousLearningRows.TimeControl p)
    (q : Fin p.T) (hfuture : t.val + 1 < q.val) :
    Measurable (fun z : Z => futureRecordingView rate rewards C_star C_h u t z q hfuture) := by
  have hx := measurable_futureInput rate rewards C_star C_h u t q hfuture
  have ht : Measurable (fun z : Z => futureTag rate rewards C_star C_h u t z q hfuture) :=
    ReferenceFirstCollectionRenewalNextRecordingPriorView.measurable_dispatchTag.comp hx
  have hv : Measurable (fun z : Z => futureDownView rate rewards C_star C_h u t z q hfuture) := by
    convert ReferenceActiveStepCompositionMeasurability.measurable_downView.comp hx using 1
    funext z
    exact congrArg DispatchCut.downView (futureRecord rate rewards C_star C_h u t z q hfuture).output.preparation.coordinator_eq
  have hs : Measurable (fun z : Z => futureStatuses rate rewards C_star C_h u t z q hfuture) := by
    apply measurable_pi_iff.mpr
    intro i
    convert (ReferenceFirstCollectionRenewalNextRecordingPriorView.measurable_preparedStatusCode rate).comp
      ((ReferenceActivePhysicalStepMeasurability.measurable_preparedFollowerCode i).comp hx) using 1
    funext z
    dsimp only [Function.comp_def]
    rw [ReferenceFirstCollectionRenewalNextRecordingPriorView.preparedStatusCode_eq]
    unfold futureStatuses
    rw [(futureRecord rate rewards C_star C_h u t z q hfuture).output_eq]
    rfl
  have hm : Measurable (fun v : ReferenceDownReception.ChoiceTimeView p rate.eta => v.pendingAtChoice) :=
    measurable_fst.comp (measurable_snd.comp (comap_measurable
      (ReferenceDownReceptionMeasurability.choiceTimeViewObservation (p := p) (rate := rate))))
  have hb (b : Bool) : Measurable (fun z : Z => viewOnBranch rate rewards C_star C_h u t b z q hfuture) := by
    have hparams : Measurable (fun v : ReferenceDownReception.ChoiceTimeView p rate.eta × Z =>
        ReferenceFirstCollectionRenewalNextRecordingPriorView.parametersOfTag rate q
          (futureTag rate rewards C_star C_h u t v.2 q hfuture) (some v.1)) :=
      (ReferenceFirstCollectionRenewalNextRecordingPriorView.measurable_parametersOfTag rate q).comp
        ((ht.comp measurable_snd).prodMk
          (LaterAssignmentFullOutputMeasurability.measurable_some_of_measurable _ measurable_fst))
    have hsnap : Measurable (fun v : ReferenceDownReception.ChoiceTimeView p rate.eta × Z =>
        if b then (none : Option (Finset (Fin (p.m - 1)) × (Fin (p.m - 1) → Option (Fin 3))))
        else some (v.1.pendingAtChoice, futureStatuses rate rewards C_star C_h u t v.2 q hfuture)) := by
      exact (measurable_of_countable (fun key : Bool ×
        (Finset (Fin (p.m - 1)) × (Fin (p.m - 1) → Option (Fin 3))) =>
          if key.1 then none else some key.2)).comp
        (measurable_const.prodMk ((hm.comp measurable_fst).prodMk (hs.comp measurable_snd)))
    exact ReferenceCollectionInstallOutputMeasurability.measurable_optionMapDependent _
      (hparams.prodMk (measurable_fst.prodMk hsnap)) _ hv
  have hle : priorField rate rewards C_star C_h u t control0 q.val ≤ (inferInstance : MeasurableSpace Z) :=
    MeasurableSpace.comap_mono ((sourcePrefixFiltration control0).le' (q.val + 1))
  have hp := (measurable_priorSlice rate rewards C_star C_h u t control0 q).mono hle le_rfl
  have hbranch : Measurable (fun z : Z => sliceBranch rate rewards C_star C_h u t z q hfuture) := by
    have hcode : Measurable (fun v : Bool × Option (ReferenceFirstCollectionRenewalNextRecordingPriorView.LiveTag p) =>
        if v.1 then match v.2 with
          | some (.inr (.inr (.inr (_, cutoff)))) => some cutoff
          | _ => none
        else none) := measurable_of_countable _
    convert hcode.comp (hp.prodMk ht) using 1
    funext z
    simp only [sliceBranch, Function.comp_def, priorSlice_eq rate rewards C_star C_h u t z q hfuture,
      Bool.decide_iff]
    rfl
  have hformula : Measurable (fun v : Option Bool × Z => v.1.elim (none : Option (ViewData rate))
      (fun b => viewOnBranch rate rewards C_star C_h u t b v.2 q hfuture)) := by
    apply measurable_from_prod_countable_right
    intro ob
    cases ob with
    | none => exact measurable_const
    | some b => exact hb b
  exact hformula.comp (hbranch.prodMk measurable_id)

theorem measurable_futureRecordingView (control0 : ContinuousLearningRows.TimeControl p)
    (q : Fin p.T) (hfuture : t.val + 1 < q.val) :
    Measurable[priorField rate rewards C_star C_h u t control0 q.val]
      (fun z : Z => futureRecordingView rate rewards C_star C_h u t z q hfuture) := by
  have heq : (fun z : Z => futureRecordingView rate rewards C_star C_h u t z q hfuture) =
      fun z => futureRecordingView rate rewards C_star C_h u t
        (priorObserver rate rewards C_star C_h u t control0 z q hfuture) q hfuture :=
    funext fun z => firstReplacement_future_view_factor rate rewards C_star C_h u t control0 z q hfuture
  rw [heq]
  exact (measurable_futureRecordingView_ambient rate rewards C_star C_h u t control0 q hfuture).comp
    (measurable_priorObserver rate rewards C_star C_h u t control0 q hfuture)

theorem futureRecordingView_replaceControl (control0 : ContinuousLearningRows.TimeControl p)
    (z : Z) (q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (control : ContinuousLearningRows.TimeControl p) :
    futureRecordingView rate rewards C_star C_h u t
      (withFutureControl rate rewards C_star C_h u t z q hfuture control) q hfuture =
        futureRecordingView rate rewards C_star C_h u t z q hfuture :=
  firstReplacement_future_view_congr rate rewards C_star C_h u t control0 _ _ q hfuture
    (withFutureSuffix_prefix rate rewards C_star C_h u t control0 z q hfuture _)

/-- The actual complete-observation cell, masked solely by the original slice. -/
def futureCell (z : Z) (q : Fin p.T) (hfuture : t.val + 1 < q.val) :
    Option (RecordedQueueRun.RoundInput p.K) :=
  if (sliceBranch rate rewards C_star C_h u t z q hfuture).isSome then
    (ReferenceLaterLiveNumericalReadout.laterLiveReadout 0
      (futureRecord rate rewards C_star C_h u t z q hfuture)).or
    (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0
      (futureRecord rate rewards C_star C_h u t z q hfuture))
  else none

def futureMarker (z : Z) (q : Fin p.T) (hfuture : t.val + 1 < q.val) :=
  (futureCell rate rewards C_star C_h u t z q hfuture).map RecordedQueueRun.RoundInput.recordedArm

private theorem live_none_of_collection (r : RoundRecord (p := p) (rate := rate))
    (s : ℕ) (c : RecordedQueueRun.RoundInput p.K)
    (hc : ReferenceLaterCollectionArrivalReadout.laterCollectionReadout s r = some c) :
    ReferenceLaterLiveNumericalReadout.laterLiveReadout s r = none := by
  cases hl : ReferenceLaterLiveNumericalReadout.laterLiveReadout s r with
  | none => rfl
  | some other => exact False.elim (ReferenceCompleteNumericalBranchObservation.readouts_disjoint
      rate s r ⟨by rw [hl]; rfl, by rw [hc]; rfl⟩)

/-- Actual present physical readout, rate/reward and full ownership snapshot,
with its deterministic recording kernel. All ordinary preparations are produced
inside the proof on the genuine source. -/
theorem firstReplacement_future_readout (z : Z) (q : Fin p.T) (hfuture : t.val + 1 < q.val) :
    match futureRecordingView rate rewards C_star C_h u t z q hfuture with
    | none => sliceBranch rate rewards C_star C_h u t z q hfuture = none ∧
        futureCell rate rewards C_star C_h u t z q hfuture = none
    | some (parameters, view, code) =>
      ∃ (c : RecordedQueueRun.RoundInput p.K)
        (snapshot : Option (ActiveRoundActions.Snapshot view.payload.assignment))
        (valid : CoordinatorLocalArmChoice.ChoiceInputsValid view.payload view.cutoff q view.complementWeights),
        futureCell rate rewards C_star C_h u t z q hfuture = some c ∧
        parameters = some (c.enabled, c.rate) ∧ c.rate = view.payload.rate ∧
        c.reward = (fun a => ((rewards q a).val : ℝ) / (D p : ℝ)) ∧
        code = snapshot.map (fun s => (s.missing, fun i => some
          (FollowerDownMeasurability.followerStatusCode (s.status i)))) ∧
        c.recordedArm = SnapshotRecordingKernel.recordingMap p
          (snapshot.elim .collection (fun s => .live view.payload.assignment s)) c.enabled
          rate.eta.val rate.eta.property rate.sourceCap view.payload.anchor
          (ReferenceFirstWindowNumericalStream.sourceWeights view.payload view.complementWeights)
          view.payload.anchor_pos
          (ReferenceFirstWindowNumericalStream.sourceWeights_pos _ _ _ _ valid)
          (ReferenceFirstWindowNumericalStream.sourceWeights_lower _ _ _ _ valid)
          (ReferenceFirstWindowNumericalStream.sourceWeights_upper _ _ _ _ valid)
          (ContinuousLearningRows.sliceAt q
            (futureRecord rate rewards C_star C_h u t z q hfuture).input.row.2) := by
  cases hb : sliceBranch rate rewards C_star C_h u t z q hfuture with
  | none => simp [futureRecordingView, hb, futureCell]
  | some b =>
    have hgeometry := sliceBranch_geometry rate rewards C_star C_h u t z q hfuture b hb
    have ht := hb
    simp only [sliceBranch, futureTag_eq] at ht
    split_ifs at ht
    cases hd : (futureRecord rate rewards C_star C_h u t z q hfuture).output.preparation.coordinator
      <;> simp only [hd] at ht <;> try contradiction
    rename_i registers owned base out
    cases out <;> simp only [ReferenceFirstCollectionRenewalNextRecordingPriorView.eraseArm,
      ReferenceLiveDispatchOutputMeasurability.outcomeData] at ht <;> try contradiction
    · have he : b = true := (Option.some.inj ht).symm
      subst b
      have hc := firstReplacement_future_cutoff_readout rate rewards C_star C_h u t z q hfuture (hgeometry.2 rfl)
      simp only [hd] at hc
      obtain ⟨c, hC, hC0, hcdef, hrate, _henabled, hreward, _hphysical⟩ := hc
      rename_i dispatched hstart ledger hinit hledger hdomain hclock hpending hnone selected
      let view : ReferenceDownReception.ChoiceTimeView p rate.eta := {
        payload := registers.payload
        pendingAtChoice := dispatched.startResult.pending
        cutoff := CoordinatorLiveChoiceRecorderStep.cutoffFromClock p dispatched.startResult.clock.u
        complementWeights := (liveRegistersAt registers
          (futureRecord rate rewards C_star C_h u t z q hfuture).input.time).complementWeights }
      have hv : futureDownView rate rewards C_star C_h u t z q hfuture = some view := by
        simp only [futureDownView, hd, DispatchCut.downView, DispatchCut.selection,
          selectionAt, dite_true, Option.map_some]
        rfl
      have hvalid : CoordinatorLocalArmChoice.ChoiceInputsValid view.payload view.cutoff q view.complementWeights := by
        rw [← (futureRecord_fields rate rewards C_star C_h u t z q hfuture).1]
        exact selected.choiceInputsValid
      have hcell : futureCell rate rewards C_star C_h u t z q hfuture = some c := by
        simp only [futureCell, hb, Option.isSome_some, ite_true, hC0,
          live_none_of_collection rate _ 0 c hC0, Option.none_or]
      have henabled : c.enabled = decide (q.val + 1 < dispatched.startResult.clock.g) := by
        rw [hcdef]
        simp only [ReferenceLaterCollectionArrivalReadout.laterCutoffCollectionInput,
          CoordinatorRecordingOperation.isFrozen, CoordinatorRecordingOperation.sourceCalendarRound,
          CoordinatorRecorderComplementBridge.recorderInput, CoordinatorRecorderComplementBridge.recorderInputWithWeights,
          CoordinatorRecorderComplementBridge.sourceStart, collectionRecordingInput,
          Nat.zero_lt_succ, true_and, not_le]
        congr 1
        exact congrArg (fun j : Fin p.T => j.val + 1 < dispatched.startResult.clock.g)
          (futureRecord_fields rate rewards C_star C_h u t z q hfuture).1
      simp only [futureRecordingView, hb, Option.elim_some, viewOnBranch, hv, Option.map_some,
        futureTag_eq, hd, ReferenceFirstCollectionRenewalNextRecordingPriorView.eraseArm,
        ReferenceLiveDispatchOutputMeasurability.outcomeData,
        ReferenceFirstCollectionRenewalNextRecordingPriorView.parametersOfTag,
        Option.bind_some, Option.map_some, ite_true]
      refine ⟨c, none, hvalid, hcell, ?_, hrate, hreward, rfl, ?_⟩
      · simp only [henabled, hrate]; rfl
      · rw [hcdef]
        dsimp only [ReferenceLaterCollectionArrivalReadout.laterCutoffCollectionInput, view,
          Option.elim_none]
        have hslice := congrArg (fun j : Fin p.T => ContinuousLearningRows.sliceAt j
          (futureRecord rate rewards C_star C_h u t z q hfuture).input.row.2)
          (futureRecord_fields rate rewards C_star C_h u t z q hfuture).1
        rw [hslice]
    · have he : b = false := (Option.some.inj ht).symm
      subst b
      obtain ⟨cell, hL, hL0, henabled, _, hrate, hreward, _, _⟩ :=
        firstReplacement_future_live_readout rate rewards C_star C_h u t z q hfuture (hgeometry.1 rfl)
      have hv : futureDownView rate rewards C_star C_h u t z q hfuture = some cell.selected.view := by
        simp only [futureDownView, DispatchCut.downView, cell.selection_actual, Option.map_some]
      have hvalid : CoordinatorLocalArmChoice.ChoiceInputsValid cell.selected.view.payload
          cell.selected.view.cutoff q cell.selected.view.complementWeights := by
        simpa only [(futureRecord_fields rate rewards C_star C_h u t z q hfuture).1] using cell.choiceInputsValid
      have hcell : futureCell rate rewards C_star C_h u t z q hfuture = some cell.input := by
        simp only [futureCell, hb, Option.isSome_some, ite_true, hL0, Option.some_or]
      simp only [futureRecordingView, hb, Option.elim_some, viewOnBranch, hv, Option.map_some,
        futureTag_eq, hd, ReferenceFirstCollectionRenewalNextRecordingPriorView.eraseArm,
        ReferenceLiveDispatchOutputMeasurability.outcomeData,
        ReferenceFirstCollectionRenewalNextRecordingPriorView.parametersOfTag,
        Option.bind_some, Option.map_some, Bool.false_eq_true, ite_false]
      refine ⟨cell.input, some (ReferenceActiveDataOwnership.choiceSnapshot cell.selected cell.states),
        hvalid, hcell, ?_, hrate, hreward, ?_, ?_⟩
      · simp only [henabled, hrate]
      · simp only [Option.map_some, ReferenceActiveDataOwnership.choiceSnapshot]
        rw [cell.selected.pending_eq]
        congr 2
        funext i
        simp only [futureStatuses, cell.ordinary i,
          ReferenceFirstCollectionRenewalNextRecordingPriorView.configurationStatus]
      · rw [cell.recordedArm_eq]
        unfold ReferenceFirstWindowNumericalStream.sourceArm
        have hslice := congrArg (fun j : Fin p.T => ContinuousLearningRows.sliceAt j
          (futureRecord rate rewards C_star C_h u t z q hfuture).input.row.2)
          (futureRecord_fields rate rewards C_star C_h u t z q hfuture).1
        simp only [ContinuousLearningRows.sliceAt] at hslice
        simp only [cell.selected.pending_eq, hslice, henabled, Option.elim_some,
          ReferenceActiveDataOwnership.choiceSnapshot]
        rfl

theorem future_slice_replaceControl (z : Z) (q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (control : ContinuousLearningRows.TimeControl p) :
    ContinuousLearningRows.sliceAt q (futureRecord rate rewards C_star C_h u t
      (withFutureControl rate rewards C_star C_h u t z q hfuture control) q hfuture).input.row.2 = control.1 := by
  have hf := futureRecord_fields rate rewards C_star C_h u t
    (withFutureControl rate rewards C_star C_h u t z q hfuture control) q hfuture
  simp only [ContinuousLearningRows.sliceAt, RoundInput.row, hf.2.1, hf.2.2.1,
    withFutureControl_val, ReferenceFixedTimeSourceControlCoupling.replaceSourceControl,
    ActualInitializationPhysicalStep.selectedRowIndex,
    ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex, Function.update_self]

private theorem snapshot_code_injective (assignment : ActiveRoundActions.Assignment p.m p.K) :
    Function.Injective (fun snapshot : Option (ActiveRoundActions.Snapshot assignment) =>
      snapshot.map (fun s => (s.missing, fun i => some
        (FollowerDownMeasurability.followerStatusCode (s.status i))))) := by
  intro a b h
  cases a with
  | none => cases b with
    | none => rfl
    | some b => cases h
  | some a => cases b with
    | none => cases h
    | some b =>
      have he := Option.some.inj h
      have hm := congrArg Prod.fst he
      have hs : a.status = b.status := by
        funext i
        have hi := Option.some.inj (congrFun (congrArg Prod.snd he) i)
        have hd := congrArg FollowerDownMeasurability.followerStatusOfCode hi
        simpa only [FollowerDownMeasurability.followerStatusOfCode_code] using hd
      cases a
      cases b
      cases hm
      cases hs
      rfl

/-- Every changed WHOLE current control is evaluated on its own genuine
source member. Its actual marker uses the SAME prior sender and full snapshot. -/
theorem firstReplacement_future_marker_section (control0 : ContinuousLearningRows.TimeControl p)
    (z : Z) (q : Fin p.T) (hfuture : t.val + 1 < q.val) :
    match futureRecordingView rate rewards C_star C_h u t z q hfuture with
    | none => ∀ control, futureMarker rate rewards C_star C_h u t
        (withFutureControl rate rewards C_star C_h u t z q hfuture control) q hfuture = none
    | some (parameters, view, code) =>
      ∃ (enabled : Bool) (snapshot : Option (ActiveRoundActions.Snapshot view.payload.assignment))
        (valid : CoordinatorLocalArmChoice.ChoiceInputsValid view.payload view.cutoff q view.complementWeights),
        parameters = some (enabled, view.payload.rate) ∧
        code = snapshot.map (fun s => (s.missing, fun i => some
          (FollowerDownMeasurability.followerStatusCode (s.status i)))) ∧
        ∀ control, futureMarker rate rewards C_star C_h u t
          (withFutureControl rate rewards C_star C_h u t z q hfuture control) q hfuture = some
          (SnapshotRecordingKernel.recordingMap p
            (snapshot.elim .collection (fun s => .live view.payload.assignment s)) enabled
            rate.eta.val rate.eta.property rate.sourceCap view.payload.anchor
            (ReferenceFirstWindowNumericalStream.sourceWeights view.payload view.complementWeights)
            view.payload.anchor_pos
            (ReferenceFirstWindowNumericalStream.sourceWeights_pos _ _ _ _ valid)
            (ReferenceFirstWindowNumericalStream.sourceWeights_lower _ _ _ _ valid)
            (ReferenceFirstWindowNumericalStream.sourceWeights_upper _ _ _ _ valid) control.1) := by
  have hactual := firstReplacement_future_readout rate rewards C_star C_h u t z q hfuture
  cases hv : futureRecordingView rate rewards C_star C_h u t z q hfuture with
  | none =>
    intro control
    have h := firstReplacement_future_readout rate rewards C_star C_h u t
      (withFutureControl rate rewards C_star C_h u t z q hfuture control) q hfuture
    rw [futureRecordingView_replaceControl rate rewards C_star C_h u t control0 z q hfuture control, hv] at h
    simp only [futureMarker, h.2, Option.map_none]
  | some v =>
    rcases v with ⟨parameters, view, code⟩
    rw [hv] at hactual
    obtain ⟨c, snapshot, valid, _hc, hp, hr, _hreward, hs, _⟩ := hactual
    refine ⟨c.enabled, snapshot, valid, by rw [← hr]; exact hp, hs, ?_⟩
    intro control
    have h := firstReplacement_future_readout rate rewards C_star C_h u t
      (withFutureControl rate rewards C_star C_h u t z q hfuture control) q hfuture
    rw [futureRecordingView_replaceControl rate rewards C_star C_h u t control0 z q hfuture control, hv] at h
    obtain ⟨c', snapshot', valid', hc', hp', _hr', _hreward', hs', hy⟩ := h
    have he : c'.enabled = c.enabled := congrArg Prod.fst (Option.some.inj (hp'.symm.trans hp))
    have hsn : snapshot' = snapshot := snapshot_code_injective _ (hs'.symm.trans hs)
    subst snapshot'
    rw [future_slice_replaceControl rate rewards C_star C_h u t z q hfuture control, he] at hy
    simp only [futureMarker, hc', Option.map_some, hy]

/-- Disabled cutoff recording is bottom even though the actual cell is present. -/
theorem futureMarker_disabled (z : Z) (q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (parameters : Option (Bool × (Fin p.K → ℝ)))
    (view : ReferenceDownReception.ChoiceTimeView p rate.eta)
    (hview : futureRecordingView rate rewards C_star C_h u t z q hfuture = some (parameters, view, none))
    (hdisabled : parameters = some (false, view.payload.rate)) :
    futureMarker rate rewards C_star C_h u t z q hfuture = some none := by
  have h := firstReplacement_future_readout rate rewards C_star C_h u t z q hfuture
  rw [hview] at h
  obtain ⟨c, snapshot, valid, hc, hp, _, _, _, hm⟩ := h
  have he : c.enabled = false := congrArg Prod.fst (Option.some.inj (hp.symm.trans hdisabled))
  rw [he, SnapshotRecordingKernel.recordingMap_disabled] at hm
  simp only [futureMarker, hc, Option.map_some, hm]

/-- Actual actions, owner observations and all-arm numerical contributions on
the continuing slice, including saved contributions of unoccupied owners. -/
theorem future_live_physical (z : Z) (q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (hk : q.val - (t.val + 1) < (continuingRecords rate rewards C_star C_h u t z).length) :
    let r := futureRecord rate rewards C_star C_h u t z q hfuture
    ∃ cell : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell r,
      ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r = some cell.input ∧
      (∀ a, cell.input.recordedArm = some a → ∃ owner : Fin p.m,
        SnapshotRecordingKernel.owns p (.live cell.selected.view.payload.assignment
          (ReferenceActiveDataOwnership.choiceSnapshot cell.selected cell.states)) owner a ∧
        r.output.preparation.arms.actions owner = a ∧ r.gridFeedback owner = rewards q a ∧
        (r.output.ownEntries owner).2.val.val = ((rewards q a).val : ℝ) / (D p : ℝ)) ∧
      ∀ a, (∃! owner : Fin p.m, SnapshotRecordingKernel.owns p
        (.live cell.selected.view.payload.assignment
          (ReferenceActiveDataOwnership.choiceSnapshot cell.selected cell.states)) owner a) ∧
        ((a ∉ cell.selected.view.payload.slowSet.1 ∧ ∃ out,
          r.output.coordinator.recording = some out ∧
          ReferenceCoordinatorRecorderCallTrace.coordinatorRaw (ReferenceActiveHorizonMeasurability.roundRecordCode r) a =
            some (RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell.input a)) ∨
          ∃ i : Fin (p.m - 1), cell.selected.view.payload.assignment.assigned i = a ∧
            (∀ j, cell.selected.view.payload.assignment.assigned j = a → j = i) ∧
            (if (cell.states i).status = .unoccupied then
              ReferenceContinuingRecordingPhysicalReward.actualCurrentSavedContribution r cell.selected.view.payload i
            else ActiveFollowerQueueOperation.rawArrival rate.eta i r.input.row r.input.time
              (cell.selected.view.payload.downRecord i)
              (r.output.ownEntries (PublicDiscreteDraws.followerPlayer p.two_le_m i)).2) =
                RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell.input a) := by
  obtain ⟨cell0, hL, hL0, _⟩ := firstReplacement_future_live_readout rate rewards C_star C_h u t z q hfuture hk
  obtain ⟨cell, hcell, _, _, _, _, _, _, _, _, howner, hoccupied, hunoccupied, _, hcoordinator, _⟩ :=
    ReferenceLaterLiveNumericalReadout.laterLiveReadout_physical rate rewards C_star C_h z.val
      (futureIndex rate rewards C_star C_h u t z q hfuture) cell0.input hL
  rw [← hcell] at hL0 howner hoccupied hunoccupied hcoordinator
  have htime := (futureRecord_fields rate rewards C_star C_h u t z q hfuture).1
  change ((ReferenceCompletePhysicalHistory.completeSuffixRecords rate z.val rewards C_star C_h).get
    (futureIndex rate rewards C_star C_h u t z q hfuture)).input.time = q at htime
  refine ⟨cell, hL0, ?_, ?_⟩
  · intro a ha
    obtain ⟨owner, ho, _, haction, hfeedback, hobservation⟩ := howner a ha
    refine ⟨owner, ho, haction, ?_, ?_⟩
    · simpa only [futureRecord, sourceRecords, htime] using hfeedback
    · simpa only [futureRecord, sourceRecords, htime] using hobservation
  · intro a
    constructor
    · obtain ⟨owner, ho⟩ := SnapshotRecordingKernel.exists_ownerSource p
        (.live cell.selected.view.payload.assignment (ReferenceActiveDataOwnership.choiceSnapshot cell.selected cell.states)) a
      exact ⟨owner, ho, fun other hother => SnapshotRecordingKernel.owns_unique p _ a other owner hother ho⟩
    · by_cases ha : a ∈ cell.selected.view.payload.slowSet.1
      · rw [← cell.selected.view.payload.assignment_image] at ha
        obtain ⟨i, _, hi⟩ := Finset.mem_image.mp ha
        refine Or.inr ⟨i, hi, fun j hj => cell.selected.view.payload.assignment.injective (hj.trans hi.symm), ?_⟩
        split_ifs with hu
        · simpa only [futureRecord, sourceRecords, hi] using hunoccupied i hu
        · simpa only [futureRecord, sourceRecords, hi] using (hoccupied i hu).2
      · obtain ⟨out, hout, hraw⟩ := hcoordinator
        exact Or.inl ⟨ha, out, hout, hraw a ha⟩

end Bandits.Support.ReferenceFirstCollectionRenewalFutureFirstReplacementView
end
