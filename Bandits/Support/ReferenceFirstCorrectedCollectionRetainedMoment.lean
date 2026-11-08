/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCorrectedCollectionCausalReadout

import Mathlib.Tactic

/-!
# Incoming retained moment at the first corrected collection

This module localizes the actual first collection cell on the original source
law. Its marker is the recorder output from the same incoming payload and
ledger; its queue step continues the initialized prefix through the collection
date.

Sources: ZIP4 `04_slow_fast_learner.tex:157-187,256-290`,
`06_interruptions.tex:40-100,192-233,246-299,355-426`, and
`appendix_a_local_protocol.tex:28-64`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support ConstructorDimensions
open BootstrapPrivateRoundStreams (SourceInput sourceInputLaw)
open ContinuousLearningRows (TimeControl)
open ReferenceSourcePrefixHistoryFiltration (actualRecord sourcePrefix sourcePrefixFiltration)
open ReferenceFixedTimeSourceControlCoupling (replaceSourceControl)
open ReferenceFirstCorrectedCollectionCausalReadout
open ReferenceFirstCollectionCorrectedSliceNumericalPrefix
open ReferenceFirstCollectionCorrectedFutureRecordingLaw
open ReferenceFirstCollectionOldRecorderFoundation
open scoped Classical BigOperators

namespace Bandits.Support.ReferenceFirstCorrectedCollectionRetainedMoment

variable {p : Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ)

local notation "X" => SourceInput p
local notation "mu" => sourceInputLaw p
local notation "Q" => ReferenceFirstLaunchNumericalCell.queueParameters rate
local notation "beta" => CanonicalRecordingRates.beta p rate.eta.val
local notation "Record" => ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)

local instance optionMeasurableSpace {A : Type*} [MeasurableSpace A] :
    MeasurableSpace (Option A) := LaterAssignmentStartMeasurability.optionMeasurableSpace
local instance optionSingletonClass {A : Type*} [MeasurableSpace A]
    [MeasurableSingletonClass A] : MeasurableSingletonClass (Option A) where
  measurableSet_singleton o := by
    let e := Equiv.optionEquivSumPUnit A
    have he : Measurable e := comap_measurable _
    have hset : ({o} : Set (Option A)) = e ⁻¹' {e o} := by
      ext x
      exact ⟨fun h => congrArg e h, fun h => e.injective h⟩
    rw [hset]
    apply he
    cases h : e o with
    | inl value => simpa only [Set.image_singleton] using
        (measurableSet_singleton value).inl_image (β := PUnit)
    | inr value => simpa only [Set.image_singleton] using
        (measurableSet_singleton value).inr_image (α := A)

/-- Set form of the accepted causal selector. -/
def collectionGate (u t q : Fin p.T) : Set X :=
  {z | firstCollectionCausalGate rate rewards C_star C_h u t q z}
/-- The literal optional cell of the actual incoming first collection branch.
Absence is preserved; no default cell is inserted. -/
def collectionCell (u t q : Fin p.T) (z : X) :
    Option (RecordedQueueRun.RoundInput p.K) := by
  classical
  exact if z ∈ collectionGate rate rewards C_star C_h u t q then
    (actualRecord rate rewards C_star C_h q z).bind
      (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate)
  else none
/-- The enabled bit and rates are projections of the same actual cell. -/
def collectionParameters (u t q : Fin p.T) (z : X) :
    Option (Bool × (Fin p.K → ℝ)) :=
  (collectionCell rate rewards C_star C_h u t q z).map fun c => (c.enabled, c.rate)
/-- The marker is the projection of the same optional actual collection cell. -/
def collectionMarker (u t q : Fin p.T) (z : X) : Option (Option (Fin p.K)) :=
  (collectionCell rate rewards C_star C_h u t q z).map fun c => c.recordedArm
/-- A marker test localized to the actual causal collection gate. -/
def collectionTest (u t q : Fin p.T) (o : Option (Option (Fin p.K))) (z : X) : ℝ :=
  by
  classical
  exact (collectionGate rate rewards C_star C_h u t q).indicator
    (fun z => if collectionMarker rate rewards C_star C_h u t q z = o then 1 else 0) z

/-- The whole-control marker coefficient, computed from the actual cell
parameters and localized to the same causal gate. -/
def collectionCoefficient (u t q : Fin p.T) (o : Option (Option (Fin p.K))) (z : X) : ℝ :=
  by
  classical
  exact (collectionGate rate rewards C_star C_h u t q).indicator
    (fun z => ReferenceFirstCollectionRenewalNextRecordingLaw.coefficientOfParameters o
      (collectionParameters rate rewards C_star C_h u t q z)) z

/-- Incoming-only retention: the causal collection gate, a clear incoming
queue, and the actual enabled cell. No outgoing overflow test is present. -/
def collectionRetainedGate (u t q : Fin p.T) : Set X :=
  (collectionGate rate rewards C_star C_h u t q ∩
    {z | ∃ v, prefixReadout rate rewards C_star C_h q.val z = some v ∧ v.2.1 = false}) ∩
    {z | ∃ xi, collectionParameters rate rewards C_star C_h u t q z = some (true, xi)}

/-- The accepted normalized arrival is evaluated on the original stopped
prefix and the same actual collection cell, and is zero outside incoming
retention. -/
def collectionArrival (u t q : Fin p.T) (a : Fin p.K) : X → ℝ :=
  (collectionRetainedGate rate rewards C_star C_h u t q).indicator (fun z =>
    match prefixInputs rate rewards C_star C_h q.val z,
        collectionCell rate rewards C_star C_h u t q z with
    | some L, some c =>
        RecordedRoundMoments.rawEstimate Q (RecordedQueueRun.run Q L) c a
    | _, _ => 0)

/-- The predictable quantized arrival size from the actual optional cell
parameters. -/
def collectionAmplitudeOfParameters (q : Fin p.T) (a : Fin p.K)
    (parameters : Option (Bool × (Fin p.K → ℝ))) : ℝ :=
  parameters.elim 0 (fun v => QuantizedRecordingMoments.quantizedValue
    (Q).D (Q).eta (v.2 a) (((rewards q a).val : ℝ) / (D p : ℝ)))

/-- The actual amplitude includes the incoming-retained gate. -/
def collectionAmplitude (u t q : Fin p.T) (a : Fin p.K) : X → ℝ :=
  (collectionRetainedGate rate rewards C_star C_h u t q).indicator (fun z =>
    collectionAmplitudeOfParameters rate rewards q a
      (collectionParameters rate rewards C_star C_h u t q z))

/-- Original-source first conditional-moment candidate. -/
def collectionMomentOne (u t q : Fin p.T) (a : Fin p.K) (z : X) : ℝ :=
  collectionAmplitude rate rewards C_star C_h u t q a z *
    collectionCoefficient rate rewards C_star C_h u t q (some (some a)) z

/-- Original-source second conditional-moment candidate, for the same arm atom. -/
def collectionMomentTwo (u t q : Fin p.T) (a : Fin p.K) (z : X) : ℝ :=
  (collectionAmplitude rate rewards C_star C_h u t q a z) ^ 2 *
    collectionCoefficient rate rewards C_star C_h u t q (some (some a)) z

/-- The first collection's retained queue increment; enabled zero arrivals
still receive service. -/
def collectionRetainedIncrement (u t q : Fin p.T) (a : Fin p.K) : X → ℝ :=
  by
  classical
  exact (collectionRetainedGate rate rewards C_star C_h u t q).indicator
    (fun z => collectionArrival rate rewards C_star C_h u t q a z - 4)

theorem collectionCell_none_of_not_gate (u t q : Fin p.T) (z : X)
    (hg : ¬ firstCollectionCausalGate rate rewards C_star C_h u t q z) :
    collectionCell rate rewards C_star C_h u t q z = none := by
  classical
  simp [collectionCell, collectionGate, hg]

theorem collectionCell_none_adjacent (u t q : Fin p.T)
    (hadj : q.val = t.val + 1) (z : X) :
    collectionCell rate rewards C_star C_h u t q z = none := by
  apply collectionCell_none_of_not_gate
  exact firstCollectionCausalGate_not_adjacent rate rewards C_star C_h u t q hadj z

private theorem collection_readout_zero (start : ℕ) (record : Record)
    (c : RecordedQueueRun.RoundInput p.K)
    (hread : ReferenceLaterCollectionArrivalReadout.laterCollectionReadout
      start record = some c) :
    ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 record = some c := by
  have hp : (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout start record).isSome = true := by
    rw [hread]
    rfl
  obtain ⟨hf, hb⟩ :=
    (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout_domain start record).mp hp
  cases hcoord : record.output.preparation.coordinator with
  | collection payload ledger clock cutoff outcome =>
      cases outcome with
      | continuing core snapshot boundary scores =>
          simpa only [ReferenceLaterCollectionArrivalReadout.laterCollectionReadout,
            dite_eq_left hf, hcoord] using hread
      | _ => simp only [hcoord] at hb
  | live registers owned base outcome =>
      cases outcome with
      | cutoffChosen dispatched hstart ledger hinit hcand hdomain hclock hpending hnone selected =>
          have hg : start < registers.payload.sigma.val := by simpa only [hcoord] using hb
          have hg0 : 0 < registers.payload.sigma.val := by omega
          simpa only [ReferenceLaterCollectionArrivalReadout.laterCollectionReadout,
            dite_eq_left hf, hcoord, hg, hg0, ite_true] using hread
      | _ => simp only [hcoord] at hb
  | first outcome => cases outcome <;> simp only [hcoord] at hb
  | invalidCollectionCutoff => simp only [hcoord] at hb
  | dagger => simp only [hcoord] at hb

/-- On the causal gate, all identities below refer to the same actual record,
payload, ledger, cell, and current collection readout. -/
theorem collectionCell_data (u t q : Fin p.T) (z : X)
    (hgate : firstCollectionCausalGate rate rewards C_star C_h u t q z) :
    ∃ (record : Record) (payload : ReferenceActivePhysicalStep.Payload rate)
      (ledger : ReferenceActivePhysicalStep.Ledger rate)
      (saved : Option (Fin p.T × Bool)) (c : RecordedQueueRun.RoundInput p.K),
      actualRecord rate rewards C_star C_h q z = some record ∧
      record.input.state.coordinator = .collection payload ledger saved ∧
      payload.sigma = t ∧ ledger.pending.Nonempty ∧
      collectionCell rate rewards C_star C_h u t q z = some c ∧
      ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 record = some c ∧
      c.enabled = ReferenceActivePhysicalStep.collectionEnabled ledger q ∧
      c.rate = payload.rate ∧
      c.reward = (fun a => ((rewards q a).val : ℝ) / (D p : ℝ)) := by
  obtain ⟨record, payload, ledger, saved, hr, hcoord, hsigma, hpending⟩ :=
    (incomingCollectionTag_spec rate rewards C_star C_h t q z).mp hgate.2
  obtain ⟨c, _started, _weights, _out, hc, hread, _hunoccupied, _hcall,
      _hrun, _hrecording, _hdiag, _hraw, _hmarker, henabled, hrate,
      hreward, _hrawArrival, _hdisabled⟩ :=
    firstCollectionCausalGate_readout rate rewards C_star C_h u t q z hgate
      record payload ledger saved hr hcoord hsigma hpending
  have hread0 := collection_readout_zero rate
    (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
    record c hread
  have hcell : collectionCell rate rewards C_star C_h u t q z = some c := by
    simp [collectionCell, collectionGate, hgate, hr, hc]
  exact ⟨record, payload, ledger, saved, c, hr, hcoord, hsigma, hpending,
    hcell, hread0, henabled, hrate, hreward⟩

/-- Every complete current-control replacement reads the same actual
collection payload and ledger and applies the literal whole-control recording
map. The outer cell remains present, including when its marker is bottom. -/
theorem collectionMarker_replaceSourceControl_map (control0 : TimeControl p)
    (u t q : Fin p.T) (htq : t.val < q.val) (z : X)
    (hgate : firstCollectionCausalGate rate rewards C_star C_h u t q z) :
    ∃ (record : Record) (payload : ReferenceActivePhysicalStep.Payload rate)
      (ledger : ReferenceActivePhysicalStep.Ledger rate)
      (saved : Option (Fin p.T × Bool)),
      actualRecord rate rewards C_star C_h q z = some record ∧
      record.input.state.coordinator = .collection payload ledger saved ∧
      payload.sigma = t ∧ ledger.pending.Nonempty ∧
      ∀ fresh : TimeControl p,
        collectionMarker rate rewards C_star C_h u t q
          (replaceSourceControl p q z fresh) =
          some (SnapshotRecordingKernel.recordingMap p .collection
            (ReferenceActivePhysicalStep.collectionEnabled ledger q)
            rate.eta.val rate.eta.property rate.sourceCap payload.anchor payload.anchor
            payload.anchor_pos payload.anchor_pos (fun _ => le_rfl)
            (fun a => by linarith [payload.anchor_pos a]) fresh.1) := by
  obtain ⟨record, payload, ledger, saved, hr, hcoord, hsigma, hpending, hmap⟩ :=
    firstCollectionCausalGate_recordingMap rate rewards C_star C_h control0
      u t q htq z hgate
  refine ⟨record, payload, ledger, saved, hr, hcoord, hsigma, hpending, ?_⟩
  intro fresh
  let z' := replaceSourceControl p q z fresh
  have hg' : firstCollectionCausalGate rate rewards C_star C_h u t q z' :=
    (firstCollectionCausalGate_replaceSourceControl rate rewards C_star C_h
      control0 u t q htq z fresh).mpr hgate
  have hm := hmap fresh
  simpa [collectionMarker, collectionCell, collectionGate, z', hg'] using hm.1

/-- The complete current-control integral of each literal collection-marker
fiber equals the coefficient determined by this same incoming cell. This is
the local whole-control law; the original-source conditional law is a separate
step. -/
theorem collectionMarker_control_integral (control0 : TimeControl p)
    (u t q : Fin p.T) (htq : t.val < q.val) (z : X)
    (o : Option (Option (Fin p.K))) :
    (∫ fresh : TimeControl p,
      collectionTest rate rewards C_star C_h u t q o
        (replaceSourceControl p q z fresh)
      ∂ContinuousLearningRows.timeControlLaw p) =
      collectionCoefficient rate rewards C_star C_h u t q o z := by
  by_cases hg : firstCollectionCausalGate rate rewards C_star C_h u t q z
  · obtain ⟨record, payload, ledger, saved, c, _hr, _hcoord, _hsigma,
      _hpending, hcell, _hread, _henabled, hrate, _hreward⟩ :=
        collectionCell_data rate rewards C_star C_h u t q z hg
    have hmap := collectionMarker_replaceSourceControl_map rate rewards C_star C_h
      control0 u t q htq z hg
    obtain ⟨record', payload', ledger', saved', _hr', _hcoord', _hsigma',
      _hpending', hmap⟩ := hmap
    have hrecord : record' = record := Option.some.inj (_hr'.symm.trans _hr)
    subst record'
    have hcoordEq :
        ReferenceActivePhysicalStep.CoordinatorConfiguration.collection payload ledger saved =
        ReferenceActivePhysicalStep.CoordinatorConfiguration.collection payload' ledger' saved' :=
      _hcoord.symm.trans _hcoord'
    injection hcoordEq with hpayload hledger hsaved
    subst payload'
    subst ledger'
    subst saved'
    have hparams : collectionParameters rate rewards C_star C_h u t q z =
        some (c.enabled, c.rate) := by
      simp [collectionParameters, hcell]
    have hcoeff : collectionCoefficient rate rewards C_star C_h u t q o z =
        ReferenceFirstCollectionRenewalNextRecordingLaw.coefficientOfParameters o
          (some (c.enabled, c.rate)) := by
      simp [collectionCoefficient, collectionGate, hg, hparams]
    have hfun : (fun fresh : TimeControl p =>
        collectionTest rate rewards C_star C_h u t q o
          (replaceSourceControl p q z fresh)) = fun fresh =>
        if some (SnapshotRecordingKernel.recordingMap p .collection c.enabled
          rate.eta.val rate.eta.property rate.sourceCap payload.anchor payload.anchor
          payload.anchor_pos payload.anchor_pos (fun _ => le_rfl)
          (fun a => by linarith [payload.anchor_pos a]) fresh.1) = o then (1 : ℝ) else 0 := by
      funext fresh
      have hg' := (firstCollectionCausalGate_replaceSourceControl
        rate rewards C_star C_h control0 u t q htq z fresh).mpr hg
      simp [collectionTest, collectionGate, hg', hmap fresh, _henabled]
    rw [hfun, hcoeff, hrate]
    cases o with
    | none => simp [ReferenceFirstCollectionRenewalNextRecordingLaw.coefficientOfParameters]
    | some marker =>
        cases hEnabled : c.enabled with
        | false =>
            cases marker <;>
              simp [SnapshotRecordingKernel.recordingMap_disabled,
                ReferenceFirstCollectionRenewalNextRecordingLaw.coefficientOfParameters]
        | true =>
            simp only [Option.some.injEq]
            rw [ReferenceFirstCollectionOldSelectorRecordingLaw.collection_recordingMap_control_integral
              rate payload marker]
            cases marker <;>
              simp [ReferenceFirstCollectionRenewalNextRecordingLaw.coefficientOfParameters]
  · have hnot (fresh : TimeControl p) :
        ¬ firstCollectionCausalGate rate rewards C_star C_h u t q
          (replaceSourceControl p q z fresh) := by
      exact (firstCollectionCausalGate_replaceSourceControl rate rewards C_star C_h
        control0 u t q htq z fresh).not.mpr hg
    have hzero : (fun fresh : TimeControl p =>
        collectionTest rate rewards C_star C_h u t q o
          (replaceSourceControl p q z fresh)) = fun _ => 0 := by
      funext fresh
      simp [collectionTest, collectionGate, hnot fresh]
    rw [hzero, integral_zero]
    simp [collectionCoefficient, collectionGate, hg]

private theorem collectionParameters_eq_of_incoming (u t q : Fin p.T)
    (z z' : X) (hg : firstCollectionCausalGate rate rewards C_star C_h u t q z)
    (hg' : firstCollectionCausalGate rate rewards C_star C_h u t q z')
    (hin : ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h q z =
      ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h q z') :
    collectionParameters rate rewards C_star C_h u t q z =
      collectionParameters rate rewards C_star C_h u t q z' := by
  obtain ⟨record, payload, ledger, saved, c, hr, hcoord, _hsigma, _hpending,
    hcell, _hread, henabled, hrate, _hreward⟩ :=
      collectionCell_data rate rewards C_star C_h u t q z hg
  obtain ⟨record', payload', ledger', saved', c', hr', hcoord', _hsigma',
    _hpending', hcell', _hread', henabled', hrate', _hreward'⟩ :=
      collectionCell_data rate rewards C_star C_h u t q z' hg'
  have hcode : ReferenceActivePhysicalStepMeasurability.encodeState record.input.state =
      ReferenceActivePhysicalStepMeasurability.encodeState record'.input.state := by
    change (actualRecord rate rewards C_star C_h q z).map
        (fun r => ReferenceActivePhysicalStepMeasurability.encodeState r.input.state) =
      (actualRecord rate rewards C_star C_h q z').map
        (fun r => ReferenceActivePhysicalStepMeasurability.encodeState r.input.state) at hin
    rw [hr, hr'] at hin
    exact Option.some.inj hin
  have hstate := ReferenceActivePhysicalStepMeasurability.encodeState_injective hcode
  have hcoordEq :
      ReferenceActivePhysicalStep.CoordinatorConfiguration.collection payload ledger saved =
        ReferenceActivePhysicalStep.CoordinatorConfiguration.collection payload' ledger' saved' := by
    rw [← hcoord, hstate, hcoord']
  injection hcoordEq with _ _ _
  subst payload'
  subst ledger'
  simp [collectionParameters, hcell, hcell', henabled, henabled', hrate, hrate']

/-- The localized coefficient is determined by the incoming record alone. -/
theorem collectionCoefficient_factor (control0 : TimeControl p)
    (u t q : Fin p.T) (htq : t.val < q.val) (o : Option (Option (Fin p.K)))
    (z : X) :
    collectionCoefficient rate rewards C_star C_h u t q o z =
      collectionCoefficient rate rewards C_star C_h u t q o
        (sourcePrefix control0 q.val z) := by
  have hgate := firstCollectionCausalGate_factor rate rewards C_star C_h control0 u t q htq z
  by_cases hg : firstCollectionCausalGate rate rewards C_star C_h u t q z
  · have hg' := hgate.mp hg
    have hin := ReferenceSourcePrefixHistoryFiltration.incoming_factor
      rate rewards C_star C_h control0 q z
    have hp := collectionParameters_eq_of_incoming rate rewards C_star C_h
      u t q z (sourcePrefix control0 q.val z) hg hg' hin
    simp [collectionCoefficient, collectionGate, hg, hg', hp]
  · have hg' : ¬ firstCollectionCausalGate rate rewards C_star C_h u t q
        (sourcePrefix control0 q.val z) := fun h => hg (hgate.mpr h)
    simp [collectionCoefficient, collectionGate, hg, hg']

private theorem collectionMarker_replace_eq_of_incoming (control0 : TimeControl p)
    (u t q : Fin p.T) (htq : t.val < q.val) (z z' : X)
    (hg : firstCollectionCausalGate rate rewards C_star C_h u t q z)
    (hg' : firstCollectionCausalGate rate rewards C_star C_h u t q z')
    (hin : ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h q z =
      ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h q z')
    (fresh : TimeControl p) :
    collectionMarker rate rewards C_star C_h u t q
        (replaceSourceControl p q z fresh) =
      collectionMarker rate rewards C_star C_h u t q
        (replaceSourceControl p q z' fresh) := by
  obtain ⟨record, payload, ledger, saved, hr, hcoord, _hsigma, _hpending, hmap⟩ :=
    collectionMarker_replaceSourceControl_map rate rewards C_star C_h
      control0 u t q htq z hg
  obtain ⟨record', payload', ledger', saved', hr', hcoord', _hsigma',
      _hpending', hmap'⟩ := collectionMarker_replaceSourceControl_map rate rewards
    C_star C_h control0 u t q htq z' hg'
  have hcode : ReferenceActivePhysicalStepMeasurability.encodeState record.input.state =
      ReferenceActivePhysicalStepMeasurability.encodeState record'.input.state := by
    change (actualRecord rate rewards C_star C_h q z).map
        (fun r => ReferenceActivePhysicalStepMeasurability.encodeState r.input.state) =
      (actualRecord rate rewards C_star C_h q z').map
        (fun r => ReferenceActivePhysicalStepMeasurability.encodeState r.input.state) at hin
    rw [hr, hr'] at hin
    exact Option.some.inj hin
  have hstate := ReferenceActivePhysicalStepMeasurability.encodeState_injective hcode
  have hcoordEq :
      ReferenceActivePhysicalStep.CoordinatorConfiguration.collection payload ledger saved =
        ReferenceActivePhysicalStep.CoordinatorConfiguration.collection payload' ledger' saved' := by
    rw [← hcoord, hstate, hcoord']
  injection hcoordEq with _ _ _
  subst payload'
  subst ledger'
  rw [hmap fresh, hmap' fresh]

/-- The causal marker test is invariant under the source-control disintegration:
the source prefix, its incoming payload and ledger, and the complete current
control are preserved. -/
theorem collectionTest_sourceControlTest (control0 : TimeControl p)
    (u t q : Fin p.T) (htq : t.val < q.val)
    (o : Option (Option (Fin p.K))) :
    ReferenceSourceCurrentControlFreshness.sourceControlTest p control0 q
      {x : X × TimeControl p |
        firstCollectionCausalGate rate rewards C_star C_h u t q
          (replaceSourceControl p q x.1 x.2) ∧
        collectionMarker rate rewards C_star C_h u t q
          (replaceSourceControl p q x.1 x.2) = o} =
      collectionTest rate rewards C_star C_h u t q o := by
  funext z
  let B : Set (X × TimeControl p) := {x |
    firstCollectionCausalGate rate rewards C_star C_h u t q
      (replaceSourceControl p q x.1 x.2) ∧
    collectionMarker rate rewards C_star C_h u t q
      (replaceSourceControl p q x.1 x.2) = o}
  let seed := sourcePrefix control0 q.val z
  let fresh := ReferenceSourceCurrentControlFreshness.u_t p q z
  let restored := replaceSourceControl p q seed fresh
  have hseed : firstCollectionCausalGate rate rewards C_star C_h u t q seed ↔
      firstCollectionCausalGate rate rewards C_star C_h u t q z := by
    simpa [seed] using (firstCollectionCausalGate_factor rate rewards C_star C_h
      control0 u t q htq z).symm
  have hrestored : firstCollectionCausalGate rate rewards C_star C_h u t q restored ↔
      firstCollectionCausalGate rate rewards C_star C_h u t q seed :=
    firstCollectionCausalGate_replaceSourceControl rate rewards C_star C_h
      control0 u t q htq seed fresh
  have hinSeed : ReferenceSourcePrefixHistoryFiltration.incoming rate rewards
      C_star C_h q z = ReferenceSourcePrefixHistoryFiltration.incoming rate rewards
        C_star C_h q seed := by
    simpa [seed] using ReferenceSourcePrefixHistoryFiltration.incoming_factor
      rate rewards C_star C_h control0 q z
  have hinRestore := ReferenceFirstCorrectedCollectionCausalReadout.incomingState_replaceSourceControl
    rate rewards C_star C_h control0 q seed fresh
  have hrestoreTest : collectionTest rate rewards C_star C_h u t q o restored =
      collectionTest rate rewards C_star C_h u t q o z := by
    by_cases hg : firstCollectionCausalGate rate rewards C_star C_h u t q z
    · have hgs := hseed.mpr hg
      have hgr := hrestored.mpr hgs
      have hin : ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h q z =
          ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h q restored :=
        hinSeed.trans hinRestore.symm
      have hfixZ : replaceSourceControl p q z fresh = z :=
        ReferenceFixedTimeSourceControlCoupling.replaceSourceControl_original p q z
      have hfixRestored : replaceSourceControl p q restored fresh = restored := by
        simp [restored, fresh, ReferenceSourceCurrentControlFreshness.u_t,
          ReferenceFixedTimeSourceControlCoupling.replaceSourceControl,
          ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex,
          ActualInitializationPhysicalStep.selectedRowIndex,
          Function.update_self, Function.update_idem]
      have hmarker := collectionMarker_replace_eq_of_incoming rate rewards C_star C_h
        control0 u t q htq z restored hg hgr hin fresh
      rw [hfixZ, hfixRestored] at hmarker
      simp [collectionTest, collectionGate, hg, hgr, hmarker]
    · have hgs : ¬ firstCollectionCausalGate rate rewards C_star C_h u t q seed :=
        fun h => hg (hseed.mp h)
      have hgr : ¬ firstCollectionCausalGate rate rewards C_star C_h u t q restored :=
        fun h => hgs (hrestored.mp h)
      simp [collectionTest, collectionGate, hg, hgr]
  have hBtest (seed : X) (fresh : TimeControl p) :
      B.indicator (fun _ => (1 : ℝ)) (seed, fresh) =
        collectionTest rate rewards C_star C_h u t q o
          (replaceSourceControl p q seed fresh) := by
    by_cases he : firstCollectionCausalGate rate rewards C_star C_h u t q
        (replaceSourceControl p q seed fresh)
    · simp [B, collectionTest, collectionGate, Set.indicator, he]
    · simp [B, collectionTest, collectionGate, Set.indicator, he]
  calc
    ReferenceSourceCurrentControlFreshness.sourceControlTest p control0 q B z =
        B.indicator (fun _ => (1 : ℝ)) (seed, fresh) := by
          rw [ReferenceSourceCurrentControlFreshness.sourceControlTest,
            ReferenceSourcePhysicalFlagConditionalLaw.c_t_eq_sourcePrefix control0 q z]
    _ = collectionTest rate rewards C_star C_h u t q o restored := hBtest seed fresh
    _ = collectionTest rate rewards C_star C_h u t q o z := hrestoreTest

theorem collectionCell_eq_oldCell_on_gate (u t q : Fin p.T) (z : X)
    (hgate : firstCollectionCausalGate rate rewards C_star C_h u t q z) :
    collectionCell rate rewards C_star C_h u t q z =
      ReferenceFirstCollectionOldRecorderFoundation.oldCell? rate rewards C_star C_h q z := by
  obtain ⟨record, _payload, _ledger, _saved, c, hr, _hcoord, _hsigma,
    _hpending, hcell, hread0, _henabled, _hrate, _hreward⟩ :=
    collectionCell_data rate rewards C_star C_h u t q z hgate
  simp only [ReferenceFirstCollectionOldRecorderFoundation.oldCell?, hr,
    Option.bind_some, hread0]
  exact hcell

private theorem collectionMarker_eq_oldMarker (u t q : Fin p.T) (z : X) :
    collectionMarker rate rewards C_star C_h u t q z =
      if firstCollectionCausalGate rate rewards C_star C_h u t q z then
        ReferenceFirstCollectionOldRecorderFoundation.oldMarker? rate rewards C_star C_h q z
      else none := by
  by_cases hg : firstCollectionCausalGate rate rewards C_star C_h u t q z
  · rw [ite_eq_left hg, collectionMarker, collectionCell_eq_oldCell_on_gate
      rate rewards C_star C_h u t q z hg]
    rfl
  · simp [collectionMarker, collectionCell, collectionGate, hg]

theorem collectionMarker_measurable (control0 : TimeControl p) (u t q : Fin p.T)
    (htq : t.val < q.val) :
    Measurable (collectionMarker rate rewards C_star C_h u t q) := by
  have hgateF := firstCollectionCausalGate_measurable rate rewards C_star C_h control0 u t q htq
  have hgate : MeasurableSet (collectionGate rate rewards C_star C_h u t q) :=
    ((sourcePrefixFiltration control0).le' (q.val + 1)) _ hgateF
  have heq : collectionMarker rate rewards C_star C_h u t q = fun z =>
      if firstCollectionCausalGate rate rewards C_star C_h u t q z then
        ReferenceFirstCollectionOldRecorderFoundation.oldMarker? rate rewards C_star C_h q z
      else none := funext (collectionMarker_eq_oldMarker rate rewards C_star C_h u t q)
  rw [heq]
  exact Measurable.ite hgate
    (ReferenceFirstCollectionOldRecorderFoundation.oldMarker_measurable
      rate rewards C_star C_h q) measurable_const

/-- Original-source conditional marker coefficients under the complete
incoming source-prefix filtration. -/
theorem collectionTest_condExp (control0 : TimeControl p)
    (u t q : Fin p.T) (htq : t.val < q.val)
    (o : Option (Option (Fin p.K))) :
    mu[collectionTest rate rewards C_star C_h u t q o |
      sourcePrefixFiltration control0 (q.val + 1)] =ᵐ[mu]
      collectionCoefficient rate rewards C_star C_h u t q o := by
  let B : Set (X × TimeControl p) := {x |
    firstCollectionCausalGate rate rewards C_star C_h u t q
      (replaceSourceControl p q x.1 x.2) ∧
    collectionMarker rate rewards C_star C_h u t q
      (replaceSourceControl p q x.1 x.2) = o}
  have hfield : MeasurableSet[sourcePrefixFiltration control0 (q.val + 1)]
      (collectionGate rate rewards C_star C_h u t q) :=
    firstCollectionCausalGate_measurable rate rewards C_star C_h control0 u t q htq
  have hle : sourcePrefixFiltration control0 (q.val + 1) ≤
      (inferInstance : MeasurableSpace X) :=
    (sourcePrefixFiltration control0).le' (q.val + 1)
  have hgate : MeasurableSet (collectionGate rate rewards C_star C_h u t q) :=
    hle _ hfield
  have hmarker : MeasurableSet {z : X |
      collectionMarker rate rewards C_star C_h u t q z = o} :=
    (collectionMarker_measurable rate rewards C_star C_h control0 u t q htq)
      (measurableSet_singleton o)
  have hreplace : Measurable (fun x : X × TimeControl p =>
      replaceSourceControl p q x.1 x.2) :=
    ReferenceSourcePhysicalFlagConditionalLaw.measurable_replaceSourceControl p q
  have hB : MeasurableSet B :=
    (hgate.inter hmarker).preimage hreplace
  have hce := ReferenceSourceCurrentControlFreshness.source_control_test_condExp
    control0 q B hB
  rw [collectionTest_sourceControlTest rate rewards C_star C_h control0
    u t q htq o] at hce
  have hsection : (fun z : X =>
      ∫ fresh : TimeControl p,
        B.indicator (fun _ => (1 : ℝ))
          (ReferenceSourceCurrentControlFreshness.c_t p control0 q z, fresh)
        ∂ContinuousLearningRows.timeControlLaw p) =
      fun z => collectionCoefficient rate rewards C_star C_h u t q o z := by
    funext z
    rw [ReferenceSourcePhysicalFlagConditionalLaw.c_t_eq_sourcePrefix control0 q z]
    let seed := sourcePrefix control0 q.val z
    have hfun : (fun fresh : TimeControl p =>
        B.indicator (fun _ => (1 : ℝ)) (seed, fresh)) =
      fun fresh => collectionTest rate rewards C_star C_h u t q o
        (replaceSourceControl p q seed fresh) := by
      funext fresh
      by_cases hg : firstCollectionCausalGate rate rewards C_star C_h u t q
          (replaceSourceControl p q seed fresh)
      · simp [B, collectionTest, collectionGate, Set.indicator, hg]
      · simp [B, collectionTest, collectionGate, Set.indicator, hg]
    rw [hfun, collectionMarker_control_integral rate rewards C_star C_h
      control0 u t q htq seed o]
    exact (collectionCoefficient_factor rate rewards C_star C_h control0
      u t q htq o z).symm
  rw [hsection] at hce
  simpa only [ReferenceSourcePhysicalFlagConditionalLaw.sourcePrefixField_eq_m_t] using hce

private theorem measurable_option_map_local {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B] (f : A → B) (hf : Measurable f) :
    Measurable (fun o : Option A => o.map f) :=
  LaterAssignmentFullOutputMeasurability.measurable_optionMap f hf id measurable_id

private def pairOptionalParameters (x : Option Bool × Option (Fin p.K → ℝ)) :
    Option (Bool × (Fin p.K → ℝ)) :=
  match x.1, x.2 with
  | some enabled, some xi => some (enabled, xi)
  | _, _ => none

private theorem pairOptionalParameters_measurable :
    Measurable (pairOptionalParameters (p := p)) := by
  have htrue : Measurable (fun x : Option Bool × Option (Fin p.K → ℝ) =>
      (x.2.map fun xi => (true, xi))) :=
    (measurable_option_map_local (fun xi : Fin p.K → ℝ => (true, xi))
      (measurable_const.prodMk measurable_id)).comp measurable_snd
  have hfalse : Measurable (fun x : Option Bool × Option (Fin p.K → ℝ) =>
      (x.2.map fun xi => (false, xi))) :=
    (measurable_option_map_local (fun xi : Fin p.K → ℝ => (false, xi))
      (measurable_const.prodMk measurable_id)).comp measurable_snd
  have ht : MeasurableSet {x : Option Bool × Option (Fin p.K → ℝ) |
      x.1 = some true} := (measurableSet_singleton (some true)).preimage measurable_fst
  have hf : MeasurableSet {x : Option Bool × Option (Fin p.K → ℝ) |
      x.1 = some false} := (measurableSet_singleton (some false)).preimage measurable_fst
  have heq : pairOptionalParameters (p := p) = fun x =>
      if x.1 = some true then x.2.map (fun xi => (true, xi)) else
      if x.1 = some false then x.2.map (fun xi => (false, xi)) else none := by
    funext x
    rcases x with ⟨enabled, rates⟩
    cases enabled with
    | none => cases rates <;> simp [pairOptionalParameters]
    | some enabled => cases enabled <;> cases rates <;> simp [pairOptionalParameters]
  rw [heq]
  exact Measurable.ite ht htrue (Measurable.ite hf hfalse measurable_const)
/-- The predictable pair obtained from the actual incoming state. It is used
only to prove predictability; the public parameters remain projections of
`collectionCell`. -/
private def collectionParametersPredictor (u t q : Fin p.T) (z : X) :
    Option (Bool × (Fin p.K → ℝ)) := by
  classical
  exact if firstCollectionCausalGate rate rewards C_star C_h u t q z then
    pairOptionalParameters (p := p)
      (ReferenceFirstCollectionOldRecorderFoundation.incomingEnabled? rate rewards C_star C_h q z,
       ReferenceFirstCollectionOldRecorderFoundation.incomingRates? rate rewards C_star C_h q z)
  else none

private theorem collectionParameters_eq_predictor (u t q : Fin p.T) (z : X) :
    collectionParameters rate rewards C_star C_h u t q z =
      collectionParametersPredictor rate rewards C_star C_h u t q z := by
  classical
  by_cases hg : firstCollectionCausalGate rate rewards C_star C_h u t q z
  · obtain ⟨record, payload, ledger, saved, c, hr, hcoord, _hsigma,
      _hpending, hcell, _hread0, _henabled, _hrate, _hreward⟩ :=
        collectionCell_data rate rewards C_star C_h u t q z hg
    have he : ReferenceFirstCollectionOldRecorderFoundation.incomingEnabled?
        rate rewards C_star C_h q z = some c.enabled := by
      simp [ReferenceFirstCollectionOldRecorderFoundation.incomingEnabled?,
        ReferenceFirstCollectionOldRecorderFoundation.enabledFromCoordinator?, hr, hcoord,
        _henabled]
    have hxi : ReferenceFirstCollectionOldRecorderFoundation.incomingRates?
        rate rewards C_star C_h q z = some c.rate := by
      rw [ReferenceFirstCollectionOldRecorderFoundation.incomingRates?,
        ReferenceFirstCollectionOldRecorderFoundation.incomingPayload?, hr]
      simp only [Option.bind_some, hcoord,
        ReferenceAssignmentPayloadPersistence.storedPayload, Option.map_some]
      exact congrArg some _hrate.symm
    simp [collectionParameters, hcell, collectionParametersPredictor, hg, he, hxi,
      pairOptionalParameters]
  · have hc := collectionCell_none_of_not_gate rate rewards C_star C_h u t q z hg
    simp [collectionParameters, hc, collectionParametersPredictor, hg]

theorem collectionParameters_prior_measurable (control0 : TimeControl p)
    (u t q : Fin p.T) (htq : t.val < q.val) :
    Measurable[sourcePrefixFiltration control0 (q.val + 1)]
      (collectionParameters rate rewards C_star C_h u t q) := by
  have heq : collectionParameters rate rewards C_star C_h u t q =
      collectionParametersPredictor rate rewards C_star C_h u t q :=
    funext (collectionParameters_eq_predictor rate rewards C_star C_h u t q)
  rw [heq]
  unfold collectionParametersPredictor
  exact Measurable.ite
    (firstCollectionCausalGate_measurable rate rewards C_star C_h control0 u t q htq)
    (pairOptionalParameters_measurable.comp
      ((ReferenceFirstCollectionOldRecorderFoundation.incomingEnabled_measurable
        rate rewards C_star C_h control0 q).prodMk
        (ReferenceFirstCollectionOldRecorderFoundation.incomingRates_measurable
          rate rewards C_star C_h control0 q))) measurable_const

private theorem measurable_option_elim_local {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    (f : A → B) (hf : Measurable f) (b : B) :
    Measurable (fun o : Option A => o.elim b f) := by
  have hs : Measurable (Equiv.optionEquivSumPUnit A) := comap_measurable _
  convert (hf.sumElim measurable_const).comp hs using 1
  funext o
  cases o <;> rfl
/-- The incoming-retained gate is measurable in the original source prefix. -/
theorem collectionRetainedGate_measurable (control0 : TimeControl p)
    (u t q : Fin p.T) (htq : t.val < q.val) :
    MeasurableSet[sourcePrefixFiltration control0 (q.val + 1)]
      (collectionRetainedGate rate rewards C_star C_h u t q) := by
  unfold collectionRetainedGate
  have hclear := ReferenceFirstCollectionCorrectedFutureRetainedMoment.incoming_clear_measurable
    rate rewards C_star C_h control0 q
  have hxi : Measurable[sourcePrefixFiltration control0 (q.val + 1)]
      (fun z : X => (collectionParameters rate rewards C_star C_h u t q z).elim false Prod.fst) :=
    (measurable_option_elim_local Prod.fst measurable_fst false).comp
      (collectionParameters_prior_measurable rate rewards C_star C_h control0 u t q htq)
  have henabled : MeasurableSet[sourcePrefixFiltration control0 (q.val + 1)]
      {z : X | ∃ xi, collectionParameters rate rewards C_star C_h u t q z =
        some (true, xi)} := by
    have hset : {z : X | ∃ xi, collectionParameters rate rewards C_star C_h u t q z =
        some (true, xi)} =
        (fun z => (collectionParameters rate rewards C_star C_h u t q z).elim false Prod.fst) ⁻¹'
          ({true} : Set Bool) := by
      ext z
      cases hp : collectionParameters rate rewards C_star C_h u t q z with
      | none => simp [hp]
      | some v => rcases v with ⟨enabled, xi⟩; cases enabled <;> simp [hp]
    rw [hset]
    exact (measurableSet_singleton true).preimage hxi
  exact ((firstCollectionCausalGate_measurable rate rewards C_star C_h control0 u t q htq).inter
    hclear).inter henabled

private theorem collectionAmplitudeOfParameters_measurable (q : Fin p.T) (a : Fin p.K) :
    Measurable (collectionAmplitudeOfParameters rate rewards q a) := by
  apply measurable_option_elim_local
  have hr : Measurable (fun v : Bool × (Fin p.K → ℝ) =>
      (((Q).D : ℝ) * (Q).eta * (((rewards q a).val : ℝ) / (D p : ℝ))) / v.2 a) :=
    measurable_const.div ((measurable_pi_apply a).comp measurable_snd)
  have hf := Nat.measurable_floor.comp hr
  have hc : Measurable (fun v : Bool × (Fin p.K → ℝ) =>
      (Nat.floor ((((Q).D : ℝ) * (Q).eta * (((rewards q a).val : ℝ) /
        (D p : ℝ))) / v.2 a) : ℝ)) :=
    (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp hf
  exact hc.div_const _
/-- Predictability of the quantized incoming amplitude on the original law. -/
theorem collectionAmplitude_prior_measurable (control0 : TimeControl p)
    (u t q : Fin p.T) (htq : t.val < q.val) (a : Fin p.K) :
    Measurable[sourcePrefixFiltration control0 (q.val + 1)]
      (collectionAmplitude rate rewards C_star C_h u t q a) :=
  ((collectionAmplitudeOfParameters_measurable rate rewards q a).comp
    (collectionParameters_prior_measurable rate rewards C_star C_h control0 u t q htq)).indicator
      (collectionRetainedGate_measurable rate rewards C_star C_h control0 u t q htq)
/-- Incoming retention supplies the actual original stopped prefix, the same
collection cell, its clear pre-step queue state, and the chronological append.
No caller-provided prefix or outgoing-overflow condition is used. -/
theorem collectionRetained_prefix_step (u t q : Fin p.T) (z : X)
    (hg : z ∈ collectionRetainedGate rate rewards C_star C_h u t q) :
    ∃ L c, prefixInputs rate rewards C_star C_h q.val z = some L ∧
      collectionCell rate rewards C_star C_h u t q z = some c ∧
      c.enabled = true ∧
      (RecordedQueueRun.run Q L).overflow = false ∧
      prefixInputs rate rewards C_star C_h (q.val + 1) z = some (L ++ [c]) := by
  obtain ⟨v, hread, hclear⟩ := hg.1.2
  unfold prefixReadout at hread
  obtain ⟨L, hL, hv⟩ := Option.map_eq_some_iff.mp hread
  have hf : (RecordedQueueRun.run Q L).overflow = false := by
    simpa only [← hv, ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout]
      using hclear
  obtain ⟨xi, hparams⟩ := hg.2
  obtain ⟨c, hc, hpair⟩ := Option.map_eq_some_iff.mp hparams
  have he : c.enabled = true := congrArg Prod.fst hpair
  have hbind : (actualRecord rate rewards C_star C_h q z).bind
      (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate) = some c := by
    simpa only [collectionCell, ite_eq_left hg.1.1] using hc
  obtain ⟨record, hr, hcell⟩ := Option.bind_eq_some_iff.mp hbind
  have hs := (prefixInputs_launch rate rewards C_star C_h q.val z L hL).2
  have hlookup : (sourceRecords rate rewards C_star C_h z)[q.val -
      sourceStart rate rewards C_star C_h z]? = some record := by
    simpa only [actualRecord, ite_eq_left hs, sourceRecords, sourceStart] using hr
  exact ⟨L, c, hL, hc, he, hf,
    prefixInputs_append_one rate rewards C_star C_h q.val z L hL record c hlookup hcell⟩
/-- On incoming retention the accepted arrival is the normalized estimate of
the same cell appended to the actual stopped prefix. -/
theorem collectionArrival_on_gate (u t q : Fin p.T) (a : Fin p.K) (z : X)
    (hg : z ∈ collectionRetainedGate rate rewards C_star C_h u t q) :
    ∃ L c, prefixInputs rate rewards C_star C_h q.val z = some L ∧
      collectionCell rate rewards C_star C_h u t q z = some c ∧
      c.enabled = true ∧ (RecordedQueueRun.run Q L).overflow = false ∧
      prefixInputs rate rewards C_star C_h (q.val + 1) z = some (L ++ [c]) ∧
      collectionArrival rate rewards C_star C_h u t q a z =
        RecordedRoundMoments.normalizedQuantizedArrival Q c a := by
  obtain ⟨L, c, hL, hc, henabled, hclear, hnext⟩ :=
    collectionRetained_prefix_step rate rewards C_star C_h u t q z hg
  have hraw := RecordedRoundMoments.rawEstimate_eq_normalizedQuantizedArrival_of_enabled
    Q (RecordedQueueRun.run Q L) c a henabled hclear
  refine ⟨L, c, hL, hc, henabled, hclear, hnext, ?_⟩
  simp [collectionArrival, Set.indicator_of_mem hg, hL, hc, hraw]
/-- The accepted arrival factors into its predictable quantized size and the
actual current collection-marker atom. -/
theorem collectionArrival_eq_amplitude_mul_test (u t q : Fin p.T)
    (a : Fin p.K) (z : X) :
    collectionArrival rate rewards C_star C_h u t q a z =
      collectionAmplitude rate rewards C_star C_h u t q a z *
        collectionTest rate rewards C_star C_h u t q (some (some a)) z := by
  by_cases hg : z ∈ collectionRetainedGate rate rewards C_star C_h u t q
  · obtain ⟨L, c, hL, hc, henabled, hclear, _hnext, harr⟩ :=
      collectionArrival_on_gate rate rewards C_star C_h u t q a z hg
    have hretained : z ∈ collectionRetainedGate rate rewards C_star C_h u t q := hg
    rcases hg with ⟨⟨hgate, _hclear⟩, ⟨xi, hp⟩⟩
    change firstCollectionCausalGate rate rewards C_star C_h u t q z at hgate
    have hgateMem : z ∈ collectionGate rate rewards C_star C_h u t q := hgate
    obtain ⟨_record, _payload, _ledger, _saved, c', _hr, _hcoord, _hsigma,
      _hpending, hcellData, _hread, _henabledData, _hrate, hreward⟩ :=
      collectionCell_data rate rewards C_star C_h u t q z hgate
    have hsame : c' = c := Option.some.inj (hcellData.symm.trans hc)
    subst c'
    have hrate : c.rate = xi := by
      have hpc : collectionParameters rate rewards C_star C_h u t q z =
          some (c.enabled, c.rate) := by simp [collectionParameters, hc]
      have hpair := Option.some.inj (hpc.symm.trans hp)
      exact congrArg Prod.snd hpair
    have hmarker : collectionMarker rate rewards C_star C_h u t q z =
        some c.recordedArm := by simp [collectionMarker, hc]
    rw [harr]
    have hamp : collectionAmplitude rate rewards C_star C_h u t q a z =
        QuantizedRecordingMoments.quantizedValue (Q).D (Q).eta (xi a)
          (((rewards q a).val : ℝ) / (D p : ℝ)) := by
      simp [collectionAmplitude, Set.indicator_of_mem hretained,
        collectionAmplitudeOfParameters, hp]
    rw [hamp]
    simp only [collectionTest, Set.indicator_of_mem hgateMem,
      hmarker, Option.some.injEq]
    cases hrecorded : c.recordedArm with
    | none =>
        have hnot : c.recordedArm ≠ some a := by simp [hrecorded]
        rw [RecordedRoundMoments.normalizedQuantizedArrival,
          RecordedQueueRun.quantizedArrival_eq_zero Q c a hnot]
        simp
    | some b =>
        by_cases hba : b = a
        · subst b
          have hrewardA := congrFun hreward a
          rw [RecordedRoundMoments.normalizedQuantizedArrival_eq_quantizedValue_of_recorded
            Q c a hrecorded, hrate, hrewardA]
          simp
        · rw [RecordedRoundMoments.normalizedQuantizedArrival,
            RecordedQueueRun.quantizedArrival_eq_zero Q c a (by
              rw [hrecorded]
              intro he
              exact hba (Option.some.inj he))]
          simp [hba]
  · simp [collectionArrival, collectionAmplitude, Set.indicator_of_notMem hg]
/-- On the actual collection gate, an arm marker has its cell's canonical
recording-rate coefficient. -/
theorem collectionCoefficient_on_gate (u t q : Fin p.T) (a : Fin p.K) (z : X)
    (hgate : firstCollectionCausalGate rate rewards C_star C_h u t q z)
    (xi : Fin p.K → ℝ)
    (hp : collectionParameters rate rewards C_star C_h u t q z = some (true, xi)) :
    collectionCoefficient rate rewards C_star C_h u t q (some (some a)) z = xi a := by
  have hgateMem : z ∈ collectionGate rate rewards C_star C_h u t q := hgate
  simp [collectionCoefficient, hgateMem, hp,
    ReferenceFirstCollectionRenewalNextRecordingLaw.coefficientOfParameters]
/-- A present retained parameter vector has the canonical beta lower bound. -/
theorem collectionParameters_beta_le (u t q : Fin p.T) (z : X)
    (xi : Fin p.K → ℝ)
    (hp : collectionParameters rate rewards C_star C_h u t q z = some (true, xi)) :
    ∀ a, beta ≤ xi a := by
  have hgate : firstCollectionCausalGate rate rewards C_star C_h u t q z := by
    by_contra hn
    have hnone := collectionCell_none_of_not_gate rate rewards C_star C_h u t q z hn
    simp [collectionParameters, hnone] at hp
  obtain ⟨c, hc, hpair⟩ := Option.map_eq_some_iff.mp hp
  obtain ⟨_record, payload, _ledger, _saved, c', _hr, _hcoord, _hsigma,
    _hpending, hc', _hread, _henabled, hrate, _hreward⟩ :=
    collectionCell_data rate rewards C_star C_h u t q z hgate
  have hsame : c = c' := Option.some.inj (hc.symm.trans hc')
  subst c'
  have hxi : c.rate = xi := congrArg Prod.snd hpair
  intro a
  rw [← hxi, hrate, payload.rate_eq_canonical]
  exact CanonicalRecordingRates.beta_le_xi p rate.eta.property payload.anchor a
/-- Exact first and second scalar conditional-moment formulas on the actual
incoming-retained collection cell. -/
theorem collectionMoments_on_gate (u t q : Fin p.T) (a : Fin p.K) (z : X)
    (hg : z ∈ collectionRetainedGate rate rewards C_star C_h u t q)
    (xi : Fin p.K → ℝ)
    (hp : collectionParameters rate rewards C_star C_h u t q z = some (true, xi)) :
    collectionMomentOne rate rewards C_star C_h u t q a z =
      QuantizedRecordingMoments.quantizedValue (Q).D (Q).eta (xi a)
        (((rewards q a).val : ℝ) / (D p : ℝ)) * xi a ∧
    collectionMomentTwo rate rewards C_star C_h u t q a z =
      (QuantizedRecordingMoments.quantizedValue (Q).D (Q).eta (xi a)
        (((rewards q a).val : ℝ) / (D p : ℝ))) ^ 2 * xi a := by
  have hretained : z ∈ collectionRetainedGate rate rewards C_star C_h u t q := hg
  obtain ⟨⟨hgate, _hclear⟩, _henabled⟩ := hg
  change firstCollectionCausalGate rate rewards C_star C_h u t q z at hgate
  have hcoeff := collectionCoefficient_on_gate rate rewards C_star C_h u t q a z
    hgate xi hp
  simp [collectionMomentOne, collectionMomentTwo, collectionAmplitude,
    Set.indicator_of_mem hretained, collectionAmplitudeOfParameters, hp, hcoeff]
/-- Quantized rounding and second-moment bounds for the actual incoming
collection arrival. -/
theorem collectionMoments_retained_bounds (u t q : Fin p.T) (a : Fin p.K) (z : X)
    (hg : z ∈ collectionRetainedGate rate rewards C_star C_h u t q)
    (xi : Fin p.K → ℝ)
    (hp : collectionParameters rate rewards C_star C_h u t q z = some (true, xi)) :
    0 < xi a ∧
    (((rewards q a).val : ℝ) / (D p : ℝ)) - xi a / ((Q).eta * ((Q).D : ℝ)) ≤
      collectionMomentOne rate rewards C_star C_h u t q a z ∧
    collectionMomentOne rate rewards C_star C_h u t q a z ≤
      (((rewards q a).val : ℝ) / (D p : ℝ)) ∧
    0 ≤ collectionMomentTwo rate rewards C_star C_h u t q a z ∧
    collectionMomentTwo rate rewards C_star C_h u t q a z ≤
      ((((rewards q a).val : ℝ) / (D p : ℝ)) ^ 2) / xi a ∧
    ((((rewards q a).val : ℝ) / (D p : ℝ)) ^ 2) / xi a ≤ 1 / xi a := by
  have hbeta := CanonicalRecordingRates.beta_pos p rate.eta.property
  have hxi := hbeta.trans_le (collectionParameters_beta_le rate rewards C_star C_h
    u t q z xi hp a)
  have hr : (((rewards q a).val : ℝ) / (D p : ℝ)) ∈ Set.Icc (0 : ℝ) 1 := by
    have hD : 0 < (D p : ℝ) := by exact_mod_cast D_pos p
    have hv : ((rewards q a).val : ℝ) ≤ (D p : ℝ) := by
      exact_mod_cast Nat.le_of_lt_succ (rewards q a).isLt
    exact ⟨div_nonneg (Nat.cast_nonneg _) hD.le,
      (div_le_iff₀ hD).2 (by simpa only [one_mul] using hv)⟩
  obtain ⟨hfirst, hsecond⟩ := collectionMoments_on_gate rate rewards C_star C_h
    u t q a z hg xi hp
  rw [hfirst, hsecond]
  have hl := QuantizedRecordingMoments.quantizedValue_roundingError
    (Q).D (Q).eta (xi a) _ (Q).D_pos (Q).eta_pos hxi hr
  have hu := QuantizedRecordingMoments.quantizedValue_firstMoment_le
    (Q).D (Q).eta (xi a) _ (Q).D_pos (Q).eta_pos hxi hr
  have hs := QuantizedRecordingMoments.quantizedValue_secondMoment_le
    (Q).D (Q).eta (xi a) _ (Q).D_pos (Q).eta_pos hxi hr
  refine ⟨hxi, by simpa only [mul_comm] using hl, by simpa only [mul_comm] using hu,
    mul_nonneg (sq_nonneg _) hxi.le, by simpa only [mul_comm] using hs, ?_⟩
  exact div_le_div_of_nonneg_right (by nlinarith [hr.1, hr.2]) hxi.le
/-- The actual amplitude stays in the accepted range using the same canonical
rate vector as the collection payload. -/
theorem collectionAmplitude_bounds (u t q : Fin p.T) (a : Fin p.K) (z : X) :
    0 ≤ collectionAmplitude rate rewards C_star C_h u t q a z ∧
      collectionAmplitude rate rewards C_star C_h u t q a z ≤ 1 / beta := by
  have hbeta := CanonicalRecordingRates.beta_pos p rate.eta.property
  by_cases hg : z ∈ collectionRetainedGate rate rewards C_star C_h u t q
  · obtain ⟨xi, hp⟩ := hg.2
    have hxi := collectionParameters_beta_le rate rewards C_star C_h u t q z xi hp a
    have hr : (((rewards q a).val : ℝ) / (D p : ℝ)) ∈ Set.Icc (0 : ℝ) 1 := by
      have hD : 0 < (D p : ℝ) := by exact_mod_cast D_pos p
      have hv : ((rewards q a).val : ℝ) ≤ (D p : ℝ) := by
        exact_mod_cast Nat.le_of_lt_succ (rewards q a).isLt
      exact ⟨div_nonneg (Nat.cast_nonneg _) hD.le,
        (div_le_iff₀ hD).2 (by simpa only [one_mul] using hv)⟩
    simp only [collectionAmplitude, Set.indicator_of_mem hg,
      collectionAmplitudeOfParameters, hp, Option.elim_some]
    exact ⟨QuantizedRecordingMoments.quantizedValue_nonneg _ _ _ _ (Q).eta_pos,
      QuantizedRecordingMoments.quantizedValue_le_inv_of_beta_le
        (Q).D (Q).eta (xi a) _ beta (Q).D_pos (Q).eta_pos
        (hbeta.trans_le hxi) hr hbeta hxi⟩
  · simp only [collectionAmplitude, Set.indicator_of_notMem hg]
    exact ⟨le_rfl, (one_div_pos.mpr hbeta).le⟩
/-- Each marker test is a Borel zero-one variable. -/
theorem collectionTest_bounds (u t q : Fin p.T) (o : Option (Option (Fin p.K)))
    (z : X) : 0 ≤ collectionTest rate rewards C_star C_h u t q o z ∧
      collectionTest rate rewards C_star C_h u t q o z ≤ 1 := by
  by_cases hg : z ∈ collectionGate rate rewards C_star C_h u t q
  · rw [collectionTest, Set.indicator_of_mem hg]
    split_ifs <;> norm_num
  · rw [collectionTest, Set.indicator_of_notMem hg]
    exact ⟨le_rfl, by norm_num⟩

theorem collectionTest_measurable (control0 : TimeControl p) (u t q : Fin p.T)
    (htq : t.val < q.val) (o : Option (Option (Fin p.K))) :
    Measurable (collectionTest rate rewards C_star C_h u t q o) := by
  have hfield := firstCollectionCausalGate_measurable rate rewards C_star C_h control0 u t q htq
  have hgate : MeasurableSet (collectionGate rate rewards C_star C_h u t q) :=
    ((sourcePrefixFiltration control0).le' (q.val + 1)) _ hfield
  have hmarker : MeasurableSet {z : X |
      collectionMarker rate rewards C_star C_h u t q z = o} :=
    (collectionMarker_measurable rate rewards C_star C_h control0 u t q htq)
      (measurableSet_singleton o)
  change Measurable (fun z => if z ∈ collectionGate rate rewards C_star C_h u t q then
    (if collectionMarker rate rewards C_star C_h u t q z = o then (1 : ℝ) else 0) else 0)
  exact Measurable.ite hgate (Measurable.ite hmarker measurable_const measurable_const)
    measurable_const

theorem collectionTest_integrable (control0 : TimeControl p) (u t q : Fin p.T)
    (htq : t.val < q.val) (o : Option (Option (Fin p.K))) :
    Integrable (collectionTest rate rewards C_star C_h u t q o) mu := by
  apply (integrable_const (1 : ℝ)).mono'
    (collectionTest_measurable rate rewards C_star C_h control0 u t q htq o).aestronglyMeasurable
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_le]
  have hb := collectionTest_bounds rate rewards C_star C_h u t q o z
  exact ⟨by linarith, by linarith⟩
/-- The accepted raw arrival is pointwise nonnegative and at most 1/beta. -/
theorem collectionArrival_bounds (u t q : Fin p.T) (a : Fin p.K) (z : X) :
    0 ≤ collectionArrival rate rewards C_star C_h u t q a z ∧
      collectionArrival rate rewards C_star C_h u t q a z ≤ 1 / beta := by
  rw [collectionArrival_eq_amplitude_mul_test rate rewards C_star C_h u t q a z]
  have ha := collectionAmplitude_bounds rate rewards C_star C_h u t q a z
  have ht := collectionTest_bounds rate rewards C_star C_h u t q (some (some a)) z
  refine ⟨mul_nonneg ha.1 ht.1, ?_⟩
  calc
    _ ≤ collectionAmplitude rate rewards C_star C_h u t q a z * 1 :=
      mul_le_mul_of_nonneg_left ht.2 ha.1
    _ = collectionAmplitude rate rewards C_star C_h u t q a z := by ring
    _ ≤ 1 / beta := ha.2

theorem collectionArrival_measurable (control0 : TimeControl p)
    (u t q : Fin p.T) (htq : t.val < q.val) (a : Fin p.K) :
    Measurable (collectionArrival rate rewards C_star C_h u t q a) := by
  rw [funext (collectionArrival_eq_amplitude_mul_test rate rewards C_star C_h u t q a)]
  exact ((collectionAmplitude_prior_measurable rate rewards C_star C_h control0
    u t q htq a).mono ((sourcePrefixFiltration control0).le' (q.val + 1)) le_rfl).mul
      (collectionTest_measurable rate rewards C_star C_h control0 u t q htq _)

theorem collectionArrival_integrable (control0 : TimeControl p)
    (u t q : Fin p.T) (htq : t.val < q.val) (a : Fin p.K) :
    Integrable (collectionArrival rate rewards C_star C_h u t q a) mu := by
  apply (integrable_const (1 / beta)).mono'
    (collectionArrival_measurable rate rewards C_star C_h control0 u t q htq a).aestronglyMeasurable
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_of_nonneg
    (collectionArrival_bounds rate rewards C_star C_h u t q a z).1]
  exact (collectionArrival_bounds rate rewards C_star C_h u t q a z).2
/-- The first accepted-arrival conditional moment is the coefficient-weighted
quantized value on the original source law. -/
theorem collectionArrival_condExp (control0 : TimeControl p)
    (u t q : Fin p.T) (htq : t.val < q.val) (a : Fin p.K) :
    mu[collectionArrival rate rewards C_star C_h u t q a |
      sourcePrefixFiltration control0 (q.val + 1)] =ᵐ[mu]
        collectionMomentOne rate rewards C_star C_h u t q a := by
  have he : collectionArrival rate rewards C_star C_h u t q a =
      collectionAmplitude rate rewards C_star C_h u t q a *
        collectionTest rate rewards C_star C_h u t q (some (some a)) := by
    funext z
    exact collectionArrival_eq_amplitude_mul_test rate rewards C_star C_h u t q a z
  have hi := collectionArrival_integrable rate rewards C_star C_h control0 u t q htq a
  rw [he] at hi ⊢
  have hpull := condExp_mul_of_stronglyMeasurable_left
    (collectionAmplitude_prior_measurable rate rewards C_star C_h control0 u t q htq a).stronglyMeasurable
    hi (collectionTest_integrable rate rewards C_star C_h control0 u t q htq _)
  have hlaw := collectionTest_condExp rate rewards C_star C_h control0 u t q htq
    (some (some a))
  filter_upwards [hpull, hlaw] with z hp hl
  exact hp.trans (congrArg (fun v =>
    collectionAmplitude rate rewards C_star C_h u t q a z * v) hl)
/-- The squared accepted arrival uses the same single recorded-arm atom. -/
theorem collectionArrival_sq_eq (u t q : Fin p.T) (a : Fin p.K) (z : X) :
    (collectionArrival rate rewards C_star C_h u t q a z) ^ 2 =
      (collectionAmplitude rate rewards C_star C_h u t q a z) ^ 2 *
        collectionTest rate rewards C_star C_h u t q (some (some a)) z := by
  rw [collectionArrival_eq_amplitude_mul_test rate rewards C_star C_h u t q a z]
  by_cases hg : z ∈ collectionGate rate rewards C_star C_h u t q
  · rw [collectionTest, Set.indicator_of_mem hg]
    split_ifs <;> simp
  · rw [collectionTest, Set.indicator_of_notMem hg]
    simp

theorem collectionArrival_sq_integrable (control0 : TimeControl p)
    (u t q : Fin p.T) (htq : t.val < q.val) (a : Fin p.K) :
    Integrable (fun z => (collectionArrival rate rewards C_star C_h u t q a z) ^ 2) mu := by
  apply (integrable_const ((1 / beta) ^ 2)).mono'
    ((collectionArrival_measurable rate rewards C_star C_h control0 u t q htq a).pow_const 2).aestronglyMeasurable
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have ha := collectionArrival_bounds rate rewards C_star C_h u t q a z
  exact pow_le_pow_left₀ ha.1 ha.2 2
/-- The exact original-source second conditional moment of the same arm atom. -/
theorem collectionArrival_sq_condExp (control0 : TimeControl p)
    (u t q : Fin p.T) (htq : t.val < q.val) (a : Fin p.K) :
    mu[(fun z => (collectionArrival rate rewards C_star C_h u t q a z) ^ 2) |
      sourcePrefixFiltration control0 (q.val + 1)] =ᵐ[mu]
        collectionMomentTwo rate rewards C_star C_h u t q a := by
  have he : (fun z => (collectionArrival rate rewards C_star C_h u t q a z) ^ 2) =
      (fun z => (collectionAmplitude rate rewards C_star C_h u t q a z) ^ 2) *
        collectionTest rate rewards C_star C_h u t q (some (some a)) := by
    funext z
    exact collectionArrival_sq_eq rate rewards C_star C_h u t q a z
  have hi := collectionArrival_sq_integrable rate rewards C_star C_h control0 u t q htq a
  rw [he] at hi ⊢
  have hpull := condExp_mul_of_stronglyMeasurable_left
    ((collectionAmplitude_prior_measurable rate rewards C_star C_h control0 u t q htq a).pow_const 2).stronglyMeasurable
    hi (collectionTest_integrable rate rewards C_star C_h control0 u t q htq _)
  have hlaw := collectionTest_condExp rate rewards C_star C_h control0 u t q htq
    (some (some a))
  filter_upwards [hpull, hlaw] with z hp hl
  exact hp.trans (congrArg (fun v =>
    (collectionAmplitude rate rewards C_star C_h u t q a z) ^ 2 * v) hl)
/-- The first conditional moment is nonnegative and at most one everywhere. -/
theorem collectionMomentOne_bounds (u t q : Fin p.T) (a : Fin p.K) (z : X) :
    0 ≤ collectionMomentOne rate rewards C_star C_h u t q a z ∧
      collectionMomentOne rate rewards C_star C_h u t q a z ≤ 1 := by
  by_cases hg : z ∈ collectionRetainedGate rate rewards C_star C_h u t q
  · obtain ⟨xi, hp⟩ := hg.2
    have hxi := (CanonicalRecordingRates.beta_pos p rate.eta.property).trans_le
      (collectionParameters_beta_le rate rewards C_star C_h u t q z xi hp a)
    have hm := collectionMoments_on_gate rate rewards C_star C_h u t q a z hg xi hp
    have hn : 0 ≤ collectionMomentOne rate rewards C_star C_h u t q a z := by
      rw [hm.1]
      exact mul_nonneg
        (QuantizedRecordingMoments.quantizedValue_nonneg (Q).D (Q).eta (xi a)
          (((rewards q a).val : ℝ) / (D p : ℝ)) (Q).eta_pos) hxi.le
    have hb := collectionMoments_retained_bounds rate rewards C_star C_h u t q a z hg xi hp
    have hr : (((rewards q a).val : ℝ) / (D p : ℝ)) ≤ 1 := by
      have hD : 0 < (D p : ℝ) := by exact_mod_cast D_pos p
      have hv : ((rewards q a).val : ℝ) ≤ (D p : ℝ) := by
        exact_mod_cast Nat.le_of_lt_succ (rewards q a).isLt
      exact (div_le_iff₀ hD).2 (by simpa only [one_mul] using hv)
    exact ⟨hn, hb.2.2.1.trans hr⟩
  · simp [collectionMomentOne, collectionAmplitude, Set.indicator_of_notMem hg]
/-- Pointwise range of the retained first-collection queue increment. -/
theorem collectionRetainedIncrement_bounds (u t q : Fin p.T) (a : Fin p.K) (z : X) :
    -4 ≤ collectionRetainedIncrement rate rewards C_star C_h u t q a z ∧
      collectionRetainedIncrement rate rewards C_star C_h u t q a z ≤ 1 / beta := by
  by_cases hg : z ∈ collectionRetainedGate rate rewards C_star C_h u t q
  · rw [collectionRetainedIncrement, Set.indicator_of_mem hg]
    have ha := collectionArrival_bounds rate rewards C_star C_h u t q a z
    exact ⟨by linarith, by linarith⟩
  · rw [collectionRetainedIncrement, Set.indicator_of_notMem hg]
    exact ⟨by norm_num, (one_div_pos.mpr
      (CanonicalRecordingRates.beta_pos p rate.eta.property)).le⟩

theorem collectionRetainedIncrement_measurable (control0 : TimeControl p)
    (u t q : Fin p.T) (htq : t.val < q.val) (a : Fin p.K) :
    Measurable (collectionRetainedIncrement rate rewards C_star C_h u t q a) := by
  exact ((collectionArrival_measurable rate rewards C_star C_h control0 u t q htq a).sub
    measurable_const).indicator
      (((sourcePrefixFiltration control0).le' (q.val + 1)) _
        (collectionRetainedGate_measurable rate rewards C_star C_h control0 u t q htq))

/-- Integrability of the actual retained increment on the whole original law. -/
theorem collectionRetainedIncrement_integrable (control0 : TimeControl p)
    (u t q : Fin p.T) (htq : t.val < q.val) (a : Fin p.K) :
    Integrable (collectionRetainedIncrement rate rewards C_star C_h u t q a) mu :=
  ((collectionArrival_integrable rate rewards C_star C_h control0 u t q htq a).sub
    (integrable_const 4)).indicator
      (((sourcePrefixFiltration control0).le' (q.val + 1)) _
        (collectionRetainedGate_measurable rate rewards C_star C_h control0 u t q htq))

theorem collectionExpIncrement_integrable (control0 : TimeControl p)
    (u t q : Fin p.T) (htq : t.val < q.val) (a : Fin p.K) :
    Integrable (fun z => Real.exp (beta *
      collectionRetainedIncrement rate rewards C_star C_h u t q a z)) mu := by
  have hb := CanonicalRecordingRates.beta_pos p rate.eta.property
  apply (integrable_const (Real.exp 1)).mono'
    ((measurable_const.mul (collectionRetainedIncrement_measurable
      rate rewards C_star C_h control0 u t q htq a)).exp).aestronglyMeasurable
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
  apply Real.exp_le_exp_of_le
  calc
    beta * collectionRetainedIncrement rate rewards C_star C_h u t q a z ≤ beta * (1 / beta) :=
      mul_le_mul_of_nonneg_left
        (collectionRetainedIncrement_bounds rate rewards C_star C_h u t q a z).2 hb.le
    _ = 1 := by field_simp [ne_of_gt hb]

private theorem collectionExpIncrement_chord (u t q : Fin p.T)
    (a : Fin p.K) (z : X) (hg : z ∈ collectionRetainedGate rate rewards C_star C_h u t q) :
    Real.exp (beta * collectionRetainedIncrement rate rewards C_star C_h u t q a z) ≤
      Real.exp (-4 * beta) * (1 + (Real.exp 1 - 1) *
        (beta * collectionArrival rate rewards C_star C_h u t q a z)) := by
  have hb := CanonicalRecordingRates.beta_pos p rate.eta.property
  have ha := collectionArrival_bounds rate rewards C_star C_h u t q a z
  have hx0 : 0 ≤ beta * collectionArrival rate rewards C_star C_h u t q a z :=
    mul_nonneg hb.le ha.1
  have hx1 : beta * collectionArrival rate rewards C_star C_h u t q a z ≤ 1 := by
    calc
      _ ≤ beta * (1 / beta) := mul_le_mul_of_nonneg_left ha.2 hb.le
      _ = 1 := by field_simp [ne_of_gt hb]
  have hc := RecordedRoundMoments.exp_le_unit_chord hx0 hx1
  rw [collectionRetainedIncrement, Set.indicator_of_mem hg]
  have he : beta * (collectionArrival rate rewards C_star C_h u t q a z - 4) =
      -4 * beta + beta * collectionArrival rate rewards C_star C_h u t q a z := by ring
  rw [he, Real.exp_add]
  exact mul_le_mul_of_nonneg_left hc (Real.exp_nonneg _)
/-- Original-source conditional exponential bound for the actual first
post-cutoff collection update. -/
theorem condExp_exp_collectionRetainedIncrement_le_one (control0 : TimeControl p)
    (u t q : Fin p.T) (htq : t.val < q.val) (a : Fin p.K) :
    mu[(fun z => Real.exp (beta *
      collectionRetainedIncrement rate rewards C_star C_h u t q a z)) |
      sourcePrefixFiltration control0 (q.val + 1)] ≤ᵐ[mu] (fun _ => (1 : ℝ)) := by
  let Fq := sourcePrefixFiltration control0 (q.val + 1)
  let G := collectionRetainedGate rate rewards C_star C_h u t q
  let A := collectionArrival rate rewards C_star C_h u t q a
  let c := Real.exp (-4 * beta)
  let d := c * ((Real.exp 1 - 1) * beta)
  let b : X → ℝ := fun z => if z ∈ G then c else 1
  let B : X → ℝ := fun z => b z + d * A z
  have hle := (sourcePrefixFiltration control0).le' (q.val + 1)
  have hG : MeasurableSet[Fq] G :=
    collectionRetainedGate_measurable rate rewards C_star C_h control0 u t q htq
  have hb : Measurable[Fq] b := Measurable.ite hG measurable_const measurable_const
  have hbi : Integrable b mu := by
    apply (integrable_const (|c| + 1)).mono'
      (hb.mono hle le_rfl).aestronglyMeasurable
    filter_upwards [] with z
    dsimp only [b]
    split
    · simp only [Real.norm_eq_abs]
      nlinarith
    · simp only [Real.norm_eq_abs, abs_one]
      nlinarith [abs_nonneg c]
  have hAi : Integrable A mu :=
    collectionArrival_integrable rate rewards C_star C_h control0 u t q htq a
  have hBi : Integrable B mu := hbi.add (hAi.const_mul d)
  have hpoint : (fun z => Real.exp (beta *
      collectionRetainedIncrement rate rewards C_star C_h u t q a z)) ≤ B := by
    intro z
    change Real.exp (beta * collectionRetainedIncrement rate rewards C_star C_h u t q a z) ≤ B z
    by_cases hg : z ∈ G
    · have hc := collectionExpIncrement_chord rate rewards C_star C_h u t q a z hg
      simp only [B, b, ite_eq_left hg]
      convert hc using 1
      dsimp only [c, d, A]
      ring
    · have hinc : collectionRetainedIncrement rate rewards C_star C_h u t q a z = 0 := by
        rw [collectionRetainedIncrement, Set.indicator_of_notMem hg]
      have hAzero : A z = 0 := by
        dsimp only [A]
        rw [collectionArrival, Set.indicator_of_notMem hg]
      rw [hinc, mul_zero, Real.exp_zero]
      simp only [B, b, ite_eq_right hg, hAzero, mul_zero, add_zero, le_refl]
  have hmono := condExp_mono (m := Fq)
    (collectionExpIncrement_integrable rate rewards C_star C_h control0 u t q htq a)
    hBi (Filter.Eventually.of_forall hpoint)
  have hadd := condExp_add hbi (hAi.const_mul d) Fq
  have hscale := condExp_mul_of_stronglyMeasurable_left
    (stronglyMeasurable_const : StronglyMeasurable[Fq] (fun _ : X => d))
    (hAi.const_mul d) hAi
  have hbase := condExp_of_stronglyMeasurable hle hb.stronglyMeasurable hbi
  have hmean := collectionArrival_condExp rate rewards C_star C_h control0 u t q htq a
  have hd : 0 ≤ d := mul_nonneg (Real.exp_nonneg _)
    (mul_nonneg (by linarith [Real.exp_one_gt_two])
      (CanonicalRecordingRates.beta_pos p rate.eta.property).le)
  have hscalar : c + d ≤ 1 := by
    have h := ReferenceFirstCollectionRenewalExponentialIncrement.exp_neg_four_beta_chord_le_one rate
    dsimp only [c, d]
    nlinarith only [h]
  filter_upwards [hmono, hadd, hscale, hmean] with z hm ha hs hmean'
  apply hm.trans
  have he : mu[B | Fq] z = b z + d * collectionMomentOne rate rewards C_star C_h u t q a z := by
    calc
      _ = mu[b | Fq] z + mu[(fun z => d * A z) | Fq] z := ha
      _ = b z + d * mu[A | Fq] z := by
        rw [hbase]
        exact congrArg (fun v => b z + v) hs
      _ = _ := by rw [hmean']
  rw [he]
  by_cases hg : z ∈ G
  · simp only [b, ite_eq_left hg]
    calc
      _ ≤ c + d * 1 := add_le_add (le_refl c)
        (mul_le_mul_of_nonneg_left
          (collectionMomentOne_bounds rate rewards C_star C_h u t q a z).2 hd)
      _ = c + d := by ring
      _ ≤ 1 := hscalar
  · simp only [b, ite_eq_right hg]
    have hg' : z ∉ collectionRetainedGate rate rewards C_star C_h u t q := by
      simpa only [G] using hg
    have hmzero : collectionMomentOne rate rewards C_star C_h u t q a z = 0 := by
      simp [collectionMomentOne, collectionAmplitude,
        Set.indicator_of_notMem hg']
    rw [hmzero]
    simp
/-- Excluded branches have no accepted arrival. -/
theorem collectionArrival_off_gate (u t q : Fin p.T) (a : Fin p.K) (z : X)
    (hg : z ∉ collectionRetainedGate rate rewards C_star C_h u t q) :
    collectionArrival rate rewards C_star C_h u t q a z = 0 :=
  Set.indicator_of_notMem hg _

theorem collectionRetainedIncrement_off_gate (u t q : Fin p.T) (a : Fin p.K) (z : X)
    (hg : z ∉ collectionRetainedGate rate rewards C_star C_h u t q) :
    collectionRetainedIncrement rate rewards C_star C_h u t q a z = 0 :=
  Set.indicator_of_notMem hg _
/-- Enabled zero arrivals retain their negative service increment. -/
theorem collectionRetainedIncrement_zero_arrival (u t q : Fin p.T)
    (a : Fin p.K) (z : X)
    (hg : z ∈ collectionRetainedGate rate rewards C_star C_h u t q)
    (hz : collectionArrival rate rewards C_star C_h u t q a z = 0) :
    collectionRetainedIncrement rate rewards C_star C_h u t q a z = -4 := by
  simp [collectionRetainedIncrement, Set.indicator_of_mem hg, hz]

private theorem mapM_id_take {A : Type*} (slots : List (Option A)) (cells : List A)
    (h : slots.mapM id = some cells) (n : ℕ) :
    (slots.take n).mapM id = some (cells.take n) := by
  induction slots generalizing cells n with
  | nil =>
      have hc : cells = [] := (Option.some.inj h).symm
      subst cells
      simp
  | cons slot slots ih =>
      cases slot with
      | none => simp [List.mapM_cons] at h
      | some a =>
          cases ht : slots.mapM id with
          | none => simp [List.mapM_cons, ht] at h
          | some tail =>
              have hc : a :: tail = cells := by simpa [List.mapM_cons, ht] using h
              subst cells
              cases n with
              | zero => rfl
              | succ n => simp [List.mapM_cons, ih tail ht n]

private theorem prefixInputs_take (m n : ℕ) (z : X)
    (L : List (RecordedQueueRun.RoundInput p.K))
    (hL : prefixInputs rate rewards C_star C_h m z = some L)
    (hs : sourceStart rate rewards C_star C_h z ≤ n) (hn : n ≤ m) :
    prefixInputs rate rewards C_star C_h n z =
      some (L.take (n - sourceStart rate rewards C_star C_h z)) := by
  have hm := prefixInputs_launch rate rewards C_star C_h m z L hL
  have hlaunch : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
      rate rewards C_star C_h n z := ⟨hm.1, hs⟩
  simp only [prefixInputs, ite_eq_left hm] at hL
  have ht := mapM_id_take _ _ hL (n - sourceStart rate rewards C_star C_h z)
  simpa only [prefixInputs, ite_eq_left hlaunch, List.map_take, List.take_take,
    Nat.min_eq_left (Nat.sub_le_sub_right hn _)] using ht

/-- The actual stopped step uses the inherited prefix, including its first
outgoing crossing. Enabled zero arrivals still receive the same service. -/
theorem collectionRetained_queue_step (u t q : Fin p.T) (a : Fin p.K) (z : X)
    (hg : z ∈ collectionRetainedGate rate rewards C_star C_h u t q) :
    ∃ L c, prefixInputs rate rewards C_star C_h q.val z = some L ∧
      collectionCell rate rewards C_star C_h u t q z = some c ∧
      c.enabled = true ∧ (RecordedQueueRun.run Q L).overflow = false ∧
      prefixInputs rate rewards C_star C_h (q.val + 1) z = some (L ++ [c]) ∧
      prefixReadout rate rewards C_star C_h (q.val + 1) z = some
        (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
          (RecordedQueueRun.step Q (RecordedQueueRun.run Q L) c)) ∧
      collectionRetainedIncrement rate rewards C_star C_h u t q a z =
        RecordedRoundMoments.rawEstimate Q (RecordedQueueRun.run Q L) c a - 4 ∧
      StoppedQueueBound.normalizedBacklog Q (RecordedQueueRun.run Q (L ++ [c])) a =
        max (StoppedQueueBound.normalizedBacklog Q (RecordedQueueRun.run Q L) a +
          collectionRetainedIncrement rate rewards C_star C_h u t q a z) 0 ∧
      ((RecordedQueueRun.run Q (L ++ [c])).overflow = true →
        (∃ i, 32 * ((RecordedQueueRun.run Q (L ++ [c])).registers i).2 > (Q).D) ∧
        ∀ i, (RecordedQueueRun.run Q (L ++ [c])).registers i =
          QueueReplay.transition (4 * (Q).n) ((RecordedQueueRun.run Q L).registers i)
            (RecordedQueueRun.acceptedRecord Q (RecordedQueueRun.run Q L) c i)) := by
  obtain ⟨L, c, hL, hc, he, hf, hnext⟩ :=
    collectionRetained_prefix_step rate rewards C_star C_h u t q z hg
  have hrun : RecordedQueueRun.run Q (L ++ [c]) =
      RecordedQueueRun.step Q (RecordedQueueRun.run Q L) c := by
    simp only [RecordedQueueRun.run, CanonicalQueueProcess.execute_append, RecordedQueueRun.execute]
  have hx : collectionRetainedIncrement rate rewards C_star C_h u t q a z =
      RecordedRoundMoments.rawEstimate Q (RecordedQueueRun.run Q L) c a - 4 := by
    simp only [collectionRetainedIncrement, Set.indicator_of_mem hg, collectionArrival,
      hL, hc]
  refine ⟨L, c, hL, hc, he, hf, hnext, ?_, hx, ?_, ?_⟩
  · simp only [prefixReadout, hnext, Option.map_some, hrun]
  · rw [hrun, hx, ← add_sub_assoc]
    exact CanonicalQueueProcess.normalizedBacklog_step_of_retained Q _ c a hf he
  · rw [hrun]
    exact RecordedQueueRun.step_retains_first_overflow_update Q _ c hf

/-- The queried causal cell is a slot in the same initialized birth, LIVE,
and first collection word. Every collection slot is retained literally; the
prefix equations include the first cutoff cell at collection index zero. -/
theorem collectionCell_dated_word (u t q : Fin p.T) (htq : t.val < q.val)
    (z : X) (hg : firstCollectionCausalGate rate rewards C_star C_h u t q z) :
    let R := sourceRecords rate rewards C_star C_h z
    let s := sourceStart rate rewards C_star C_h z
    let b := birthIndex rate rewards C_star C_h z
    let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
      rate rewards C_star C_h z (b + 1)
    let e := b + 1 + W.length
    let j := q.val - s - e
    ∃ (L0 : List (RecordedQueueRun.RoundInput p.K))
      (c0 : RecordedQueueRun.RoundInput p.K)
      (B D : List (RecordedQueueRun.RoundInput p.K))
      (birth : Record) (payload : ReferenceActivePhysicalStep.Payload rate)
      (seg : ReferenceCollectionSegmentExtraction.Segment rate)
      (I : ReferenceCollectionSegmentExtraction.Initializer p),
      ReferenceFirstCollectionCurrentRetainedGate.pastCells? rate rewards C_star C_h t z = some L0 ∧
      ReferenceFirstCollectionCurrentNumericalCell.currentCell rate rewards C_star C_h t z = some c0 ∧
      prefixInputs rate rewards C_star C_h (t.val + 1) z = some (L0 ++ [c0]) ∧
      L0.length = b ∧ s + b = t.val ∧ R[b]? = some birth ∧
      ReferenceAssignmentPayloadPersistence.InstallationBirth birth payload ∧
      B.length = W.length ∧ (R.drop b).take (1 + W.length) = birth :: W ∧
      (∀ k : Fin W.length, ReferenceFirstCollectionCurrentRetainedGate.cell0 rate W[k.val] =
        B[k.val]?) ∧
      ReferenceCollectionSegmentExtraction.segmentAt R e = some seg ∧
      seg.context.payload = payload ∧ seg.context.initializer = some I ∧
      I.sigma = t.val + 1 ∧ I.cutoff = s + e + 1 ∧
      seg.records ++ seg.remaining = R.drop e ∧
      D.length = seg.records.length ∧ 0 < j ∧ j < D.length ∧ q.val = s + e + j ∧
      (∀ k : Fin D.length, (seg.records[k.val]?).bind
        (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate) = D[k.val]?) ∧
      (∀ h, h ≤ D.length → prefixInputs rate rewards C_star C_h (s + e + h) z =
        some (((L0 ++ [c0]) ++ B) ++ D.take h)) ∧
      collectionCell rate rewards C_star C_h u t q z = D[j]? ∧
      prefixInputs rate rewards C_star C_h q.val z =
        some (((L0 ++ [c0]) ++ B) ++ D.take j) ∧
      prefixInputs rate rewards C_star C_h (q.val + 1) z =
        some (((L0 ++ [c0]) ++ B) ++ D.take (j + 1)) ∧
      (∀ a, z ∈ collectionRetainedGate rate rewards C_star C_h u t q →
        ∃ c, D[j]? = some c ∧
          prefixReadout rate rewards C_star C_h (q.val + 1) z = some
            (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
              (RecordedQueueRun.step Q (RecordedQueueRun.run Q
                (((L0 ++ [c0]) ++ B) ++ D.take j)) c)) ∧
          collectionRetainedIncrement rate rewards C_star C_h u t q a z =
            RecordedRoundMoments.rawEstimate Q
              (RecordedQueueRun.run Q (((L0 ++ [c0]) ++ B) ++ D.take j)) c a - 4) := by
  intro R s b W e j
  obtain ⟨record, payload, ledger, saved, c, hr, hcoord, hsigma, hpending,
      hc, _hread, _henabled, _hrate, _hreward⟩ :=
    collectionCell_data rate rewards C_star C_h u t q z hg
  obtain ⟨birth, seg, I, hb, hborn, hseg, hpay, hinit, hIsigma, hIcut,
      _htrueCut, hpartition, hpos, hrecord, _hprefix⟩ :=
    firstCollectionCausalGate_firstSegment rate rewards C_star C_h u t q htq z hg
      record payload ledger saved hr hcoord hsigma hpending
  change ReferenceCollectionSegmentExtraction.segmentAt R e = some seg at hseg
  change seg.records ++ seg.remaining = R.drop e at hpartition
  change j < seg.records.length at hpos
  change seg.records[j]? = some record at hrecord
  have hlookup : R[e + j]? = some record := by
    have hd : (R.drop e)[j]? = some record := by
      rw [← hpartition, List.getElem?_append_left hpos]
      exact hrecord
    simpa only [List.getElem?_drop] using hd
  obtain ⟨hindex, hvalue⟩ := List.getElem?_eq_some_iff.mp hlookup
  have htime := ReferenceAssignmentFollowerMassSteps.complete_record_time
    rate rewards C_star C_h z ⟨e + j, hindex⟩
  change (R[e + j]'hindex).input.time.val = s + (e + j) at htime
  rw [hvalue] at htime
  have hfields := ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields
    rate rewards C_star C_h q z record hr
  have hdate : q.val = s + e + j := by rw [hfields.2.2.1] at htime; omega
  obtain ⟨L0, c0, birth', hL0, hc0, hbase, hLlen, hbt, hb', _ht,
      _hrows, _hJ, _hrewards, _he0, _hlive0, _hcell0, _hout, hnum⟩ :=
    ReferenceFirstCorrectedCollectionCalendarNumericalJoin.firstCell_collection_calendar_numerical_values
      rate rewards C_star C_h u t z hg.1
  have hbirthEq : birth' = birth := Option.some.inj (hb'.symm.trans hb)
  subst birth'
  obtain ⟨birth', rout, qout, base, hb'', _hbt, _hdate0, _hrows0, _hJ0,
      _hrewards0, _hborn0, _hsigma0, _hlater0, hnext, _htail0⟩ :=
    ReferenceFirstCorrectedReplacementCollectionReadout.firstCell_collection_readout_cover
      rate rewards C_star C_h u t z hg.1
  have hbirthEq : birth' = birth := Option.some.inj (hb''.symm.trans hb)
  subst birth'
  obtain ⟨_hsigmaNum, hnum⟩ := hnum rout qout base hnext
  obtain ⟨hk, hstate, hlater, hnum⟩ := hnum (by omega)
  let B := ReferenceCompleteLaterLiveComplementPrefixReplay.prefixCells
    rewards C_star C_h z ⟨b + 1, hk⟩ rout qout base hstate hlater
  obtain ⟨hB, _helen, _hT, hAlen, _hDate, _hA, hbirthW, hBcells,
      rE, qE, _hpE, _hinE, hcase⟩ := hnum
  change B.length = W.length at hB
  change ((L0 ++ [c0]) ++ B).length = e at hAlen
  rcases hcase with hterminal | ⟨he, seg', I', l0, hseg', _hentry,
      _hpay', _hpre, hinit', _hI', _hchecked, _harm, hIsigma', hIcut',
      _htrue', _hfreeze, _hbase, _hchosen, _hnonempty, _hpartition',
      D, hD, hDcells, _hraw, hG, hq, _hqT, _hRtake, hfull, _hrest⟩
  · change e = R.length at hterminal
    omega
  · have hsame : seg' = seg := Option.some.inj (hseg'.symm.trans hseg)
    subst seg'
    have hsameI : I' = I := Option.some.inj (hinit'.symm.trans hinit)
    subst I'
    have hjpos : 0 < j := by
      by_contra hn
      have hj : j = 0 := by omega
      have hin := _hinE he
      change (R[e]'he).input.state.coordinator = .live rE qE base at hin
      have hv : (R[e]'he) = record := (List.getElem?_eq_some_iff.mp
        (show R[e]? = some record by simpa only [hj, Nat.add_zero] using hlookup)).2
      rw [hv, hcoord] at hin
      contradiction
    have hprefixes (h : ℕ) (hh : h ≤ D.length) :
        prefixInputs rate rewards C_star C_h (s + e + h) z =
          some (((L0 ++ [c0]) ++ B) ++ D.take h) := by
      have hp := prefixInputs_take rate rewards C_star C_h
        (s + (e + seg.records.length)) (s + e + h) z
        (((L0 ++ [c0]) ++ B) ++ D) hfull (by omega) (by omega)
      have hn : s + e + h - sourceStart rate rewards C_star C_h z = e + h := by
        change s + e + h - s = e + h
        omega
      rw [hn] at hp
      rw [← hAlen, List.take_append, List.take_of_length_le (by omega),
        Nat.add_sub_cancel_left] at hp
      simpa only [hAlen] using hp
    have hDcurrent := (hDcells ⟨j, hpos⟩).1
    have hrec : (seg.records[j]'hpos) = record := (List.getElem?_eq_some_iff.mp hrecord).2
    rw [hrec] at hDcurrent
    have hcRecord : ReferenceFirstCollectionCurrentRetainedGate.cell0 rate record = some c := by
      simpa [collectionCell, collectionGate, hg, hr] using hc
    have hcellEq : c = D[j]'(by omega) := Option.some.inj (hcRecord.symm.trans hDcurrent)
    refine ⟨L0, c0, B, D, birth, payload, seg, I, hL0, hc0, hbase, hLlen,
      hbt, hb, hborn, hB, hbirthW, ?_, hseg, hpay, hinit, hIsigma, hIcut,
      hpartition, hD, hjpos, hD ▸ hpos, hdate, ?_, hprefixes, ?_, ?_, ?_, ?_⟩
    · intro k
      simpa only [List.getElem?_eq_getElem (show k.val < B.length by omega)] using (hBcells k).2.2
    · intro k
      simpa only [List.getElem?_eq_getElem (show k.val < seg.records.length by omega),
        List.getElem?_eq_getElem k.isLt, Option.bind_some] using (hDcells ⟨k.val, by omega⟩).1
    · rw [hc, hcellEq, List.getElem?_eq_getElem (show j < D.length by omega)]
    · rw [hdate]
      exact hprefixes j (by omega)
    · have hd : q.val + 1 = s + e + (j + 1) := by omega
      rw [hd]
      exact hprefixes (j + 1) (by omega)

    · intro a hret
      obtain ⟨L', c', hL', hc', _he, _hf, _hn, hread, hx, _hb, _hcross⟩ :=
        collectionRetained_queue_step rate rewards C_star C_h u t q a z hret
      have hbefore := hprefixes j (by omega)
      rw [← hdate] at hbefore
      have hsame : L' = ((L0 ++ [c0]) ++ B) ++ D.take j :=
        Option.some.inj (hL'.symm.trans hbefore)
      subst L'
      refine ⟨c', ?_, hread, hx⟩
      rw [List.getElem?_eq_getElem (show j < D.length by omega), ← hcellEq]
      exact hc.symm.trans hc'

end Bandits.Support.ReferenceFirstCorrectedCollectionRetainedMoment
