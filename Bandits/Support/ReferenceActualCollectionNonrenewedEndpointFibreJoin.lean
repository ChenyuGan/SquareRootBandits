/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceActualCollectionEnabledPrefixEndpoint

import Mathlib.Tactic

/-!
# Actual nonrenewed collection endpoint and assignment fibre

An actual present corrected collection invocation, together with its computed
pre-round nonoverflow readout, determines the literal retained prefix cell.
The accepted endpoint and checked-assignment APIs then identify the same
signed slow-set atom with the actual assignment-vector fibre mass.

Sources: ZIP4 `06_interruptions.tex:381-426`,
`04_slow_fast_learner.tex:176-215,323-366`, and
`appendix_a_local_protocol.tex:28-79` under `sources/zip4/manuscript/`.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceCompletePhysicalHistory
open Bandits.Support.ReferenceFirstCorrectedNextCalendarWordJoin (calendarReplay)
open Bandits.Support.ReferenceActualCollectionHiddenRefreshPath
open Bandits.Support.ReferenceActualCollectionEnabledPrefixEndpoint
open Bandits.Support.ReferenceCalendarCollectionCallControlLaw
open Bandits.Support.ReferenceLaterSamplerParameterMeasurability
open Bandits.Support.AssignmentParameterFibreKernel
open Bandits.Support.CheckedAssignmentSample
open Bandits.Support.DeferredRefreshWindow
open Bandits.Support.RecordedCorrectedWindow
open Bandits.Support.CorrectedAssignmentVector
open Bandits.Support.ReferenceFirstCollectionAuxiliarySeeds (AuxiliaryArray auxiliaryUniformLaw)
open Bandits.Support.ReferenceFirstLaunchNumericalCell (queueParameters)

namespace Bandits.Support.ReferenceActualCollectionNonrenewedEndpointFibreJoin

variable {p : ConstructorDimensions.Parameters}

/-- A present call whose incoming collection is strictly before its retained
old boundary. This is the intrinsic nonrenewed branch test, before sampling;
no successful sampled output is required. -/
def actualNonrenewedCollectionCall
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p) : Prop :=
  (ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h t z).isSome = true ∧
  ∃ record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate),
    ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some record ∧
    (match record.input.state.coordinator with
      | .collection _ ledger _ => record.input.time.val + 1 < ledger.freezeAt
      | _ => False)

private theorem collectionParameters_none_of_pending_nonempty
    (x : CoordinatorRoundDispatch.CollectionInput p)
    (hpending : x.ledger.pending.Nonempty) :
    ReferenceLaterAssignmentFibreStep.collectionParameters? x = none := by
  unfold ReferenceLaterAssignmentFibreStep.collectionParameters?
  cases CoordinatorPhaseClock.startRound p x.etaReal x.time x.clock x.ledger.pending with
  | error reason => rfl
  | ok started =>
      by_cases hcore : CoordinatorRoundDispatch.CollectionCoreValid x
      · simp only [dite_eq_left hcore, ite_eq_left hpending]
      · simp only [dite_eq_right hcore]

private theorem actualNonrenewedCollectionCall_successful
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hcall : actualNonrenewedCollectionCall rate rewards C_star C_h t z) :
    (ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h t z).isSome = true ∧
    ∃ record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate),
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some record ∧
      ReferenceCollectionPhaseHistory.laterChosen record.input = true ∧
      (match record.output.preparation.coordinator with
        | .collection _ _ _ _
            (.laterChosen _ _ _ _ instruction _ _ _ _ _ _) =>
            instruction.kind = CoordinatorPhaseClock.AssignmentStartKind.corrected
        | _ => False) := by
  classical
  rcases hcall with ⟨hpresent, chosenRecord, hrecord, hbefore⟩
  cases hvalue : ReferenceCalendarCollectionCallControlLaw.callAt
      rate rewards C_star C_h t z with
  | none => simp only [hvalue, Option.isSome_none, Bool.false_eq_true] at hpresent
  | some value =>
      obtain ⟨u, theta⟩ := value
      have hselector : ReferenceFirstCollectionSamplerCall.collectionCallAt chosenRecord =
          some (u, theta) := by
        change (ReferenceSourcePrefixHistoryFiltration.actualRecord
          rate rewards C_star C_h t z).bind
            ReferenceFirstCollectionSamplerCall.collectionCallAt = some (u, theta) at hvalue
        rw [hrecord] at hvalue
        exact hvalue
      obtain ⟨payload, ledger, saved, hstate, hcutoff, hparameters⟩ :=
        (ReferenceFirstCollectionSamplerCall.collectionCallAt_spec chosenRecord u theta).mp hselector
      have hpending : ledger.pending = ∅ := by
        by_contra hne
        have hnone : ReferenceLaterAssignmentFibreStep.parameters? chosenRecord.input = none := by
          unfold ReferenceLaterAssignmentFibreStep.parameters?
          have hvalid : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T := by
            have := u.isLt
            omega
          simp only [hstate, dite_eq_left hvalid]
          apply collectionParameters_none_of_pending_nonempty
          exact Finset.nonempty_iff_ne_empty.mpr hne
        change ReferenceLaterAssignmentFibreStep.parameters? chosenRecord.input = some theta at hparameters
        rw [hnone] at hparameters
        cases hparameters
      rw [hstate] at hbefore
      let R := completeSuffixRecords rate z rewards C_star C_h
      let s := physicalStart rate z rewards C_star C_h
      have hstart : s ≤ t.val := by
        by_contra hnot
        change (if s ≤ t.val then R[t.val - s]? else none) = some chosenRecord at hrecord
        rw [ite_eq_right hnot] at hrecord
        cases hrecord
      let b := t.val - s
      have hlookup : R[b]? = some chosenRecord := by
        change (if s ≤ t.val then R[t.val - s]? else none) = some chosenRecord at hrecord
        rw [ite_eq_left hstart] at hrecord
        exact hrecord
      have hb : b < R.length := (List.getElem?_eq_some_iff.mp hlookup).1
      have hrecordB : R[b]'hb = chosenRecord :=
        Option.some.inj ((List.getElem?_eq_getElem hb).symm.trans hlookup)
      subst chosenRecord
      let record := R[b]'hb
      change record.input.state.coordinator = .collection payload ledger saved at hstate
      obtain ⟨cutoff, hcutoffValue, core, started, hstartRound, instruction, hassignment,
          _htime, hkind, _hsigma, _hu, consistent, output, hlocal, _hlater,
          clockData, installed, selected, _hprior, _hresult, _hpending,
          _hinstalled, hdispatchCollection, _⟩ :=
        ReferenceCompleteEmptyCollectionCorrectedChoiceDomains.complete_empty_corrected_choice_domains
          rate rewards C_star C_h z ⟨b, hb⟩ payload ledger saved hstate hpending hbefore
      have hvalid : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T := by
        have := cutoff.isLt
        omega
      have hdispatch : ReferenceActivePhysicalStep.dispatch record.input =
          .collection payload ledger (ReferenceActivePhysicalStep.collectionClock
            payload ledger saved cutoff) cutoff
            (.laterChosen core consistent started hstartRound instruction hassignment
              output hlocal clockData installed selected) := by
        calc
          _ = .collection payload ledger (ReferenceActivePhysicalStep.collectionClock
              payload ledger saved cutoff) cutoff
              (CoordinatorRoundDispatch.dispatchCollection
                (ReferenceActivePhysicalStep.collectionInput record.input payload ledger
                  (ReferenceActivePhysicalStep.collectionClock payload ledger saved cutoff) cutoff)) := by
            unfold ReferenceActivePhysicalStep.dispatch
            simp only [hstate, dite_eq_left hvalid, CoordinatorRoundDispatch.dispatch]
            have hindex : (⟨ledger.cutoff - 1, by omega⟩ : Fin p.T) = cutoff := by
              apply Fin.ext
              dsimp only
              omega
            rw [hindex]
            rfl
          _ = _ := congrArg (ReferenceActivePhysicalStep.DispatchCut.collection
            payload ledger (ReferenceActivePhysicalStep.collectionClock payload ledger saved cutoff)
              cutoff) hdispatchCollection
      have hprepared : record.output.preparation.coordinator =
          ReferenceActivePhysicalStep.dispatch record.input :=
        record.output.preparation.coordinator_eq
      refine ⟨rfl, record, hrecord, ?_, ?_⟩
      · unfold ReferenceCollectionPhaseHistory.laterChosen
        rw [(ReferenceActivePhysicalStep.prepare record.input).coordinator_eq, hdispatch]
      · rw [hprepared, hdispatch]
        exact hkind

/-- A present invocation recovers its selector from the actual round record.
The returned parameter is the one produced by the existing pre-sampler
selector on that record's original input. -/
theorem actualNonrenewedCollectionCall_selector
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hcall : actualNonrenewedCollectionCall rate rewards C_star C_h t z) :
    ∃ (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (u : Fin p.T) (theta : AssignmentParameterFibreKernel.Theta p),
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z =
        some record ∧
      ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h t z =
        some (u, theta) ∧
      ∃ payload ledger proposal,
        record.input.state.coordinator = .collection payload ledger proposal ∧
        ledger.cutoff = u.val + 1 ∧
        ReferenceLaterSamplerParameterMeasurability.parameters? record.input = some theta ∧
        ReferenceCollectionPhaseHistory.laterChosen record.input = true ∧
        (match record.output.preparation.coordinator with
          | .collection _ _ _ _
              (.laterChosen _ _ _ _ instruction _ _ _ _ _ _) =>
              instruction.kind = CoordinatorPhaseClock.AssignmentStartKind.corrected
          | _ => False) := by
  rcases actualNonrenewedCollectionCall_successful rate rewards C_star C_h t z hcall with
    ⟨hpresent, record, hrecord, hlater, hcorrected⟩
  cases hvalue : ReferenceCalendarCollectionCallControlLaw.callAt
      rate rewards C_star C_h t z with
  | none =>
      have : (ReferenceCalendarCollectionCallControlLaw.callAt
          rate rewards C_star C_h t z).isSome = true := hpresent
      simp only [hvalue, Option.isSome_none, Bool.false_eq_true] at this
  | some value =>
      rcases value with ⟨u, theta⟩
      have hselector :
          ReferenceFirstCollectionSamplerCall.collectionCallAt record = some (u, theta) := by
        change (ReferenceSourcePrefixHistoryFiltration.actualRecord
          rate rewards C_star C_h t z).bind
            ReferenceFirstCollectionSamplerCall.collectionCallAt = some (u, theta) at hvalue
        rw [hrecord] at hvalue
        exact hvalue
      obtain ⟨payload, ledger, proposal, hstate, hcutoff, hparameters⟩ :=
        (ReferenceFirstCollectionSamplerCall.collectionCallAt_spec record u theta).mp hselector
      exact ⟨record, u, theta, hrecord, rfl, payload, ledger, proposal,
        hstate, hcutoff, hparameters, hlater, hcorrected⟩

/-- The selected parameter is the value of the existing actual-call
projection on the original input record. -/
theorem actualNonrenewedCollectionCall_actualParameter
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hcall : actualNonrenewedCollectionCall rate rewards C_star C_h t z) :
    ∃ (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (u : Fin p.T) (theta : AssignmentParameterFibreKernel.Theta p)
      (actualCall : ReferenceLaterSamplerParameterMeasurability.ActualSamplerCall
        (p := p) (rate := rate)),
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z =
        some record ∧
      ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h t z =
        some (u, theta) ∧
      actualCall.val = record.input ∧
      ReferenceLaterSamplerParameterMeasurability.actualParameter actualCall = theta := by
  obtain ⟨record, u, theta, hrecord, hcallAt, _payload, _ledger, _proposal,
      _hstate, _hcutoff, hparameters, _hlater, _hcorrected⟩ :=
    actualNonrenewedCollectionCall_selector rate rewards C_star C_h t z hcall
  have hsome :
      (ReferenceLaterSamplerParameterMeasurability.parameters? record.input).isSome = true := by
    rw [hparameters]
    rfl
  let actualCall : ReferenceLaterSamplerParameterMeasurability.ActualSamplerCall
      (p := p) (rate := rate) := ⟨record.input, hsome⟩
  refine ⟨record, u, theta, actualCall, hrecord, hcallAt, rfl, ?_⟩
  simp [actualCall,
    ReferenceLaterSamplerParameterMeasurability.actualParameter, hparameters]

/-- The actual call is located at its calendar record in the complete physical
suffix. The index is computed from the launch date and the supplied calendar
call; no physical-history coordinate is added to the hypotheses. -/
theorem actualNonrenewedCollectionCall_record_index
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hcall : actualNonrenewedCollectionCall rate rewards C_star C_h t z) :
    ∃ (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (b : ℕ),
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z =
        some record ∧
      b < (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h).length ∧
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[b]? =
        some record ∧
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + b = t.val ∧
      ReferenceCollectionPhaseHistory.laterChosen record.input = true ∧
      (match record.output.preparation.coordinator with
        | .collection _ _ _ _
            (.laterChosen _ _ _ _ instruction _ _ _ _ _ _) =>
            instruction.kind = CoordinatorPhaseClock.AssignmentStartKind.corrected
        | _ => False) := by
  obtain ⟨record, _u, _theta, hrecord, _hselector,
      _payload, _ledger, _proposal, _hstate, _hcutoff, _hparameters, hlater, hcorrected⟩ :=
    actualNonrenewedCollectionCall_selector rate rewards C_star C_h t z hcall
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  have hstart : s ≤ t.val := by
    by_contra hnot
    change (if s ≤ t.val then
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[t.val - s]? else none) = some record at hrecord
    rw [ite_eq_right hnot] at hrecord
    cases hrecord
  let b := t.val - s
  have hlookup : R[b]? = some record := by
    change (if s ≤ t.val then R[t.val - s]? else none) = some record at hrecord
    rw [ite_eq_left hstart] at hrecord
    simpa [b] using hrecord
  have hb : b < R.length := (List.getElem?_eq_some_iff.mp hlookup).1
  refine ⟨record, b, hrecord, hb, hlookup, ?_, hlater, hcorrected⟩
  dsimp [b, s]
  omega

/-- The present nonrenewed invocation has the predecessor cutoff and segment
from the complete installation theorem on this same original source. -/
theorem actualNonrenewedCollectionCall_predecessor
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hcall : actualNonrenewedCollectionCall rate rewards C_star C_h t z) :
    ∃ (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (u : Fin p.T) (theta : AssignmentParameterFibreKernel.Theta p)
      (b : ℕ) (a : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h).length)
      (r0 : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
      (e : ℕ) (seg : ReferenceCollectionSegmentExtraction.Segment rate)
      (initializer : ReferenceCollectionSegmentExtraction.Initializer p)
      (saved : Option (Fin p.T × Bool)),
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z =
        some record ∧
      ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h t z =
        some (u, theta) ∧
      b < (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h).length ∧
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[b]? =
        some record ∧
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + b = t.val ∧
      a.val < e ∧
      ReferenceAssignmentPayloadPersistence.InstallationBirth
        ((ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[a.val]'a.isLt)
        r0.payload ∧
      (∀ k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h).length,
        a.val < k.val → k.val < b → ∀ fresh,
          ¬ ReferenceAssignmentPayloadPersistence.InstallationBirth
            ((ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val]'k.isLt)
            fresh) ∧
      e < b ∧ b = e + seg.records.length ∧
      ReferenceCollectionSegmentExtraction.segmentAt
        (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h) e =
          some seg ∧
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[e]? =
        some seg.entry ∧
      ReferenceCollectionPhaseHistory.cutoffChosen seg.entry.input = true ∧
      seg.context.payload = r0.payload ∧
      seg.context.initializer = some initializer ∧
      record.input.state.coordinator = .collection r0.payload seg.final saved ∧
      ReferenceCollectionPhaseHistory.laterChosen record.input = true ∧
      (match record.output.preparation.coordinator with
        | .collection _ _ _ _
            (.laterChosen _ _ _ _ instruction _ _ _ _ _ _) =>
            instruction.kind = CoordinatorPhaseClock.AssignmentStartKind.corrected
        | _ => False) ∧
      initializer.cutoff = ReferenceCompletePhysicalHistory.physicalStart
        rate z rewards C_star C_h + e + 1 := by
  obtain ⟨record, u, theta, hrecord, hcallAt,
      _payload, _ledger, _proposal, _hstate, _hcutoff, _hparameters, hlater,
      hcorrected⟩ :=
    actualNonrenewedCollectionCall_selector rate rewards C_star C_h t z hcall
  obtain ⟨recordAt, b, hrecordAt, hb, hlookup, hdate, hlaterAt, hcorrectedAt⟩ :=
    actualNonrenewedCollectionCall_record_index rate rewards C_star C_h t z hcall
  have hrecordEq : recordAt = record := Option.some.inj (hrecordAt.symm.trans hrecord)
  subst recordAt
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  have hbR : b < R.length := by simpa [R] using hb
  have hrecordB : R[b]'hbR = record := by
    apply Option.some.inj
    exact (List.getElem?_eq_getElem hbR).symm.trans (by simpa [R] using hlookup)
  have hlaterB : ReferenceCollectionPhaseHistory.laterChosen
      (R[b]'hbR).input = true := by
    rw [hrecordB]
    exact hlaterAt
  obtain ⟨a, r0, q0, beta, e, seg, initializer, saved, hae, heb, _heLive, hbirth,
      _hsigma, _hnextLive, _hbase, hnoBirth, hsegment, _hne, hentry, hcut,
      hpayload, hinitializer, _hchecked, _harm, _hsigmaCutoff, _hcutoffValue, _hbaseValue,
      hlength, _htake, _hdrop, _hexit, _hstateB, hcoordB, _hpending, _hcursor,
      _hfirst⟩ :=
    ReferenceCompleteInstallationPredecessorInterval.internal_complete_installation_predecessor_interval
      rate rewards C_star C_h z ⟨b, hbR⟩ hlaterB
  have hbirth' :
      ReferenceAssignmentPayloadPersistence.InstallationBirth
        ((ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)[a.val]'a.isLt) r0.payload := by
    simpa [R] using hbirth
  have hnoBirth' : ∀ k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length, a.val < k.val → k.val < b → ∀ fresh,
      ¬ ReferenceAssignmentPayloadPersistence.InstallationBirth
        ((ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val]'k.isLt) fresh := by
    intro k hak hkb fresh
    exact hnoBirth k hak (by omega) fresh
  have hentry' :
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[e]? =
        some seg.entry := by simpa [R] using hentry
  have hcoordB' :
      record.input.state.coordinator = .collection r0.payload seg.final saved := by
    rw [← hrecordB]
    simpa only [R] using hcoordB
  exact ⟨record, u, theta, b, a, r0, e, seg, initializer, saved,
    hrecord, hcallAt, hb, hlookup, hdate, hae, hbirth', hnoBirth', heb,
    hlength, by simpa [R] using hsegment, hentry', hcut, hpayload, hinitializer,
    hcoordB', hlaterAt, hcorrectedAt, _hcutoffValue⟩

private def actualDispatchOrigin
    {rate : ReferenceActivePhysicalStep.RateInput p}
    {x : ReferenceActivePhysicalStep.RoundInput p rate} :
    ReferenceActivePhysicalStep.DispatchCut x → Prop
  | .first _ => x.state.coordinator = .first
  | .live r q base _ => x.state.coordinator = .live r q base
  | .collection payload ledger _ _ _ =>
      ∃ saved, x.state.coordinator = .collection payload ledger saved
  | .invalidCollectionCutoff =>
      ∃ payload ledger saved, x.state.coordinator = .collection payload ledger saved
  | .dagger => x.state.coordinator = .dagger

private theorem actualDispatchOrigin_prepared
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (x : ReferenceActivePhysicalStep.RoundInput p rate) :
    actualDispatchOrigin (ReferenceActivePhysicalStep.prepare x).coordinator := by
  change actualDispatchOrigin (ReferenceActivePhysicalStep.dispatch x)
  unfold ReferenceActivePhysicalStep.dispatch
  cases hs : x.state.coordinator with
  | first => simp only [CoordinatorRoundDispatch.dispatch]; exact hs
  | live r q base => simp only [CoordinatorRoundDispatch.dispatch]; exact hs
  | collection payload ledger saved =>
      simp only [CoordinatorRoundDispatch.dispatch]
      split
      · exact ⟨saved, hs⟩
      · exact ⟨payload, ledger, saved, hs⟩
  | dagger => exact hs

private theorem cutoffChosen_input_live
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (hcut : ReferenceCollectionPhaseHistory.cutoffChosen x = true) :
    ∃ (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
      (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
      (base : Fin (p.m - 1) → ℕ),
      x.state.coordinator = .live r q base := by
  cases hprep : (ReferenceActivePhysicalStep.prepare x).coordinator with
  | live r q base outcome =>
      have hstate : x.state.coordinator = .live r q base := by
        simpa [actualDispatchOrigin, hprep] using actualDispatchOrigin_prepared rate x
      exact ⟨r, q, base, hstate⟩
  | first outcome =>
      simp [ReferenceCollectionPhaseHistory.cutoffChosen, hprep] at hcut
  | collection payload ledger clock cutoff outcome =>
      simp [ReferenceCollectionPhaseHistory.cutoffChosen, hprep] at hcut
  | invalidCollectionCutoff =>
      simp [ReferenceCollectionPhaseHistory.cutoffChosen, hprep] at hcut
  | dagger =>
      simp [ReferenceCollectionPhaseHistory.cutoffChosen, hprep] at hcut

private theorem actual_cutoff_segment_freezeAt
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (active : ReferenceActivePhysicalStep.State p rate)
    (hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h = some active)
    (e : ℕ)
    (seg : ReferenceCollectionSegmentExtraction.Segment rate)
    (I : ReferenceCollectionSegmentExtraction.Initializer p)
    (hsegment : ReferenceCollectionSegmentExtraction.segmentAt
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)
      e = some seg)
    (hcut : ReferenceCollectionPhaseHistory.cutoffChosen seg.entry.input = true)
    (hinitializer : seg.context.initializer = some I) :
    ∃ (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
      (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
      (base : Fin (p.m - 1) → ℕ),
      seg.entry.input.state.coordinator = .live r q base ∧
      seg.final.freezeAt = r.gridBoundary ∧
      seg.final.cutoff = I.cutoff ∧ r.payload = seg.context.payload := by
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  have hsegment' :=
    (ReferenceCollectionSegmentExtraction.segmentAt_branch R e seg hsegment).1
  have hchoice : ReferenceCollectionSegmentExtraction.choice seg.entry.input =
      some seg.context := by
    cases hrecords : R.drop e with
    | nil =>
        rw [hrecords] at hsegment'
        change ReferenceCollectionSegmentExtraction.segment [] = some seg at hsegment'
        simp only [ReferenceCollectionSegmentExtraction.segment] at hsegment'
        cases hsegment'
    | cons entry rest =>
        rw [hrecords] at hsegment'
        change ((ReferenceCollectionSegmentExtraction.choice entry.input).map
          (fun c => if (ReferenceCollectionSegmentExtraction.extractRound entry).isSome then
            ⟨entry, c, entry :: rest.takeWhile ReferenceCollectionSegmentExtraction.continuing,
              rest.dropWhile ReferenceCollectionSegmentExtraction.continuing⟩
          else ⟨entry, c, [], entry :: rest⟩)) = some seg at hsegment'
        cases hc : ReferenceCollectionSegmentExtraction.choice entry.input with
        | none =>
            simp only [hc, Option.map_none] at hsegment'
            cases hsegment'
        | some c =>
            rw [hc] at hsegment'
            by_cases hextract : (ReferenceCollectionSegmentExtraction.extractRound entry).isSome
            · simp only [hextract] at hsegment'
              have hsegEq := Option.some.inj hsegment'
              have hentry := congrArg ReferenceCollectionSegmentExtraction.Segment.entry hsegEq
              have hcontext := congrArg ReferenceCollectionSegmentExtraction.Segment.context hsegEq
              rw [← hentry, ← hcontext]
              exact hc
            · simp only [hextract] at hsegment'
              have hsegEq := Option.some.inj hsegment'
              have hentry := congrArg ReferenceCollectionSegmentExtraction.Segment.entry hsegEq
              have hcontext := congrArg ReferenceCollectionSegmentExtraction.Segment.context hsegEq
              rw [← hentry, ← hcontext]
              exact hc
  have hsel : (ReferenceActivePhysicalStep.prepare seg.entry.input).coordinator.selection ≠ none := by
    intro hnone
    unfold ReferenceCollectionSegmentExtraction.choice at hchoice
    rw [hnone] at hchoice
    cases hchoice
  have hpreparedOrigin := actualDispatchOrigin_prepared rate seg.entry.input
  unfold ReferenceCollectionPhaseHistory.cutoffChosen at hcut
  cases hprep : (ReferenceActivePhysicalStep.prepare seg.entry.input).coordinator with
  | live r q base outcome =>
      cases outcome with
      | cutoffChosen dispatched hstart ledger hinit hcand hdomains hshape hpending hno selected =>
          have hstate : seg.entry.input.state.coordinator = .live r q base := by
            simpa [actualDispatchOrigin, hprep] using hpreparedOrigin
          have hchoice' :
              ReferenceCollectionSegmentExtraction.choiceOfCut
                (ReferenceActivePhysicalStep.prepare seg.entry.input).coordinator =
              some seg.context := by
            unfold ReferenceCollectionSegmentExtraction.choice at hchoice
            rw [ite_eq_right hsel] at hchoice
            exact hchoice
          have hcontext : seg.context =
              ⟨r.payload, ReferenceActivePhysicalStep.sharedLedger ledger,
                dispatched.startResult,
                (ReferenceActivePhysicalStep.liveRegistersAt r seg.entry.input.time).complementWeights,
                some (ReferenceCollectionSegmentExtraction.cutoffInitializer
                  (ReferenceActivePhysicalStep.liveRegistersAt r seg.entry.input.time)
                  (ReferenceActivePhysicalStep.liveOwnedAt r q seg.entry.input.time)
                  base seg.entry.input.time)⟩ := by
            exact (Option.some.inj (by
              simpa only [ReferenceCollectionSegmentExtraction.choiceOfCut, hprep] using hchoice')).symm
          have hIeq : I = ReferenceCollectionSegmentExtraction.cutoffInitializer
              (ReferenceActivePhysicalStep.liveRegistersAt r seg.entry.input.time)
              (ReferenceActivePhysicalStep.liveOwnedAt r q seg.entry.input.time)
              base seg.entry.input.time := by
            have hinit' : seg.context.initializer = some
                (ReferenceCollectionSegmentExtraction.cutoffInitializer
                  (ReferenceActivePhysicalStep.liveRegistersAt r seg.entry.input.time)
                  (ReferenceActivePhysicalStep.liveOwnedAt r q seg.entry.input.time)
                  base seg.entry.input.time) := by
              rw [hcontext]
            exact Option.some.inj (hinitializer.symm.trans hinit')
          have hconnected := ReferenceCompletePhysicalHistory.completeSuffix_connected_on_launch
            rate z rewards C_star C_h active hlaunch
          have hfold := ReferenceCollectionSegmentExtraction.connected_segment_checked _ _ _ seg
            (ReferenceCollectionSegmentExtraction.connected_drop R active _ e hconnected)
            hsegment'
          have hcontextRun := CollectionBufferProvenance.checkedRounds_success_preserves_context
            seg.context.preLedger seg.final seg.inputs seg.accepted hfold
          have hinitFields := CollectionBufferProvenance.startCollectionChecked_success_context
            I.assignment I.sigma I.cutoff I.freezeAt I.base I.outside seg.context.preLedger
              (by
                have hcheckedInit := ReferenceCollectionSegmentExtraction.choice_initializer
                  seg.entry.input seg.context I hchoice hinitializer
                simpa only [ReferenceCollectionSegmentExtraction.Initializer.checkedStart] using
                  hcheckedInit)
          have hfreeze : seg.final.freezeAt = I.freezeAt := by
            have hpre : seg.context.preLedger.freezeAt = I.freezeAt := hinitFields.2.2.2.2.1
            have hctxFreeze : seg.final.freezeAt = seg.context.preLedger.freezeAt := by
              have h := congrArg (fun c => c.2.2.2.1) hcontextRun
              simpa only [CollectionBufferProvenance.collectionContext] using h
            exact hctxFreeze.trans hpre
          refine ⟨r, q, base, hstate, ?_, ?_, ?_⟩
          · rw [hIeq] at hfreeze
            simpa [ReferenceCollectionSegmentExtraction.cutoffInitializer,
              ReferenceActivePhysicalStep.liveRegistersAt] using hfreeze
          · have hctxCutoff : seg.final.cutoff = seg.context.preLedger.cutoff := by
              have h := congrArg (fun c => c.2.2.1) hcontextRun
              simpa only [CollectionBufferProvenance.collectionContext] using h
            exact hctxCutoff.trans hinitFields.2.2.2.1
          · rw [hcontext]
      | clockFailure failure hstart => simp [hprep] at hcut
      | initializerFailure dispatched hstart checked hinitializer => simp [hprep] at hcut
      | localFailure dispatched hstart reason => simp [hprep] at hcut
      | continuingChosen dispatched hstart continuation selected => simp [hprep] at hcut
  | first outcome => simp [hprep] at hcut
  | collection payload ledger clock cutoff outcome => simp [hprep] at hcut
  | invalidCollectionCutoff => simp [hprep] at hcut
  | dagger => simp [hprep] at hcut

private theorem actual_corrected_call_before_freeze
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (saved : Option (Fin p.T × Bool))
    (hstate : record.input.state.coordinator = .collection payload ledger saved)
    (hcorrected : match record.output.preparation.coordinator with
      | .collection _ _ _ _ (.laterChosen _ _ _ _ instruction _ _ _ _ _ _) =>
          instruction.kind = CoordinatorPhaseClock.AssignmentStartKind.corrected
      | _ => False) :
    record.input.time.val + 1 < ledger.freezeAt := by
  have hactual : record.output.preparation.coordinator =
      ReferenceActivePhysicalStep.dispatch record.input := by
    rw [record.output_eq]
    exact (ReferenceActivePhysicalStep.prepare record.input).coordinator_eq
  cases hcoord : record.output.preparation.coordinator with
  | collection old localLedger clock cutoff outcome =>
      cases outcome with
      | laterChosen core consistent started hstart instruction hassignment output hlocal
          clockData installed selected =>
          have hkind : instruction.kind = CoordinatorPhaseClock.AssignmentStartKind.corrected := by
            simpa only [hcoord] using hcorrected
          have hdispatch : ReferenceActivePhysicalStep.dispatch record.input =
              .collection old localLedger clock cutoff
                (.laterChosen core consistent started hstart instruction hassignment output hlocal
                  clockData installed selected) := hactual.symm.trans hcoord
          have hledgerEq : localLedger = ledger := by
            have horigin := actualDispatchOrigin_prepared rate record.input
            change actualDispatchOrigin (ReferenceActivePhysicalStep.dispatch record.input) at horigin
            rw [hdispatch] at horigin
            obtain ⟨savedActual, hsource⟩ := horigin
            have hconfig := ReferenceActivePhysicalStep.CoordinatorConfiguration.collection.inj
              (hsource.symm.trans hstate)
            exact hconfig.2.1
          let operation := CoordinatorRoundDispatch.collectionOperationLedger
            (ReferenceActivePhysicalStep.collectionInput record.input old localLedger clock cutoff)
            core.payload_n_eq
          have hbefore :=
            (AssignmentScoreReconstruction.reconstructLaterStart_corrected_iff
              operation instruction output.reconstruction output.reconstruction_eq).mp hkind
          have htime := ReferenceActivePhysicalStep.later_instruction_time record.input old
            localLedger clock cutoff core started instruction hstart hassignment
          have hbeforeLocal : instruction.time.val + 1 < localLedger.freezeAt := by
            change instruction.time.val + 1 < localLedger.freezeAt at hbefore
            exact hbefore
          have hbeforeInput : instruction.time.val + 1 < ledger.freezeAt := by
            rw [← hledgerEq]
            exact hbeforeLocal
          simpa only [htime] using hbeforeInput
      | clockFailure failure hstart => simp [hcoord] at hcorrected
      | localFailure started hstart hcore reason => simp [hcoord] at hcorrected
      | coreFailure core started hstart reason => simp [hcoord] at hcorrected
      | continuing core prepared boundary checked => simp [hcoord] at hcorrected
      | laterReconstructionFailure core consistent started hstart instruction hassignment reason hlater =>
          simp [hcoord] at hcorrected
      | laterPrefixFailure core consistent started hstart instruction hassignment arm reason hlater =>
          simp [hcoord] at hcorrected
      | laterOrientationFailure core consistent started hstart instruction hassignment set hlater =>
          simp [hcoord] at hcorrected
      | laterChoiceFailure core consistent started hstart instruction hassignment output hlocal
          clockData installed reason => simp [hcoord] at hcorrected
  | first outcome => simp [hcoord] at hcorrected
  | live registers owned base outcome => simp [hcoord] at hcorrected
  | invalidCollectionCutoff => simp [hcoord] at hcorrected
  | dagger => simp [hcoord] at hcorrected

/-- A real corrected invocation before its computed clear pre-round readout
lies in the literal canonical collection prefix cell. The cutoff, segment,
old live boundary, no-intervening-birth condition, and date all come from the
same actual record on the original source. -/
theorem actualNonrenewedCollectionCall_prefixCell
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hcall : actualNonrenewedCollectionCall rate rewards C_star C_h t z)
    (hclear : ∃ o,
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout
        rate rewards C_star C_h t.val z = some o ∧ o.2.1 = false) :
    ∃ (e b : ℕ)
      (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (u : Fin p.T) (theta : AssignmentParameterFibreKernel.Theta p),
      ∃ hcell : z ∈ ReferenceActualCollectionHiddenRefreshPath.collectionPrefixCell
          rate rewards C_star C_h e b,
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z =
        some record ∧
      ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h t z =
        some (u, theta) ∧
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + b = t.val ∧
      ∃ (ledger : ReferenceActivePhysicalStep.Ledger rate) (saved : Option (Fin p.T × Bool)),
        record.input.state.coordinator = .collection
          (oldPayload rate rewards C_star C_h e b z hcell) ledger saved ∧
        ledger.cutoff = ReferenceCompletePhysicalHistory.physicalStart
          rate z rewards C_star C_h + e + 1 := by
  obtain ⟨record, u, theta, b, a, r0, e, seg, initializer, saved,
      hrecord, hcallAt, hb, hlookup, hdate, hae, hbirth, hnoBirth, hebeforeB,
      hlength, hsegment, hentry, hcut, hpayload, hinitializer, hcoord, hlater,
      hcorrected, hcutoffI⟩ :=
    actualNonrenewedCollectionCall_predecessor rate rewards C_star C_h t z hcall
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  have he : e < R.length := by
    have : e < b := hebeforeB
    simpa [R] using lt_trans this hb
  have hbR : b ≤ R.length := by simpa [R] using Nat.le_of_lt hb
  have hentryVal : R[e]'he = seg.entry := by
    apply Option.some.inj
    exact (List.getElem?_eq_getElem he).symm.trans (by simpa [R] using hentry)
  have hclearSpec := Classical.choose_spec hclear
  have hclearAt :
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout
        rate rewards C_star C_h (s + b) z = some (Classical.choose hclear) := by
    have hdate' : s + b = t.val := by simpa [s] using hdate
    calc
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout
          rate rewards C_star C_h (s + b) z =
        ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout
          rate rewards C_star C_h t.val z := by
            exact congrArg (fun n => ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout
              rate rewards C_star C_h n z) hdate'
      _ = some (Classical.choose hclear) := hclearSpec.1
  have hclearFlag : (Classical.choose hclear).2.1 = false := hclearSpec.2
  cases hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h with
  | none =>
      have hnil := (ReferenceCompletePhysicalHistory.no_launch_complete_history
        rate z rewards C_star C_h hlaunch).2.1
      have hb' : b < 0 := by simpa only [R, hnil, List.length_nil] using hb
      omega
  | some active =>
      obtain ⟨rE, qE, baseE, hstateE, hfreeze, hcutoffFinal, hpayloadE⟩ :=
        actual_cutoff_segment_freezeAt rate rewards C_star C_h z active hlaunch
          e seg initializer hsegment hcut hinitializer
      have hbefore := actual_corrected_call_before_freeze rate record r0.payload seg.final
        saved hcoord hcorrected
      have hbeforeBoundary : record.input.time.val + 1 < rE.gridBoundary := by
        rw [← hfreeze]
        exact hbefore
      have hrecordTime := ReferenceFirstCollectionRenewalRecordingFeedback.complete_record_time
        rate z rewards C_star C_h b record hlookup
      have hstrict : s + b + 1 < rE.gridBoundary := by
        rw [← hrecordTime]
        exact hbeforeBoundary
      have hnoLater : ∀ k : Fin R.length, e < k.val → k.val < b →
          ReferenceCollectionPhaseHistory.laterChosen (R[k.val]'k.isLt).input = false := by
        intro k hek hkb
        cases htag : ReferenceCollectionPhaseHistory.laterChosen (R[k.val]'k.isLt).input with
        | false => rfl
        | true =>
            let recordK := R[k.val]'k.isLt
            have hactualK : recordK.output.preparation.coordinator =
                (ReferenceActivePhysicalStep.prepare recordK.input).coordinator := by
              rw [recordK.output_eq]
              rfl
            unfold ReferenceCollectionPhaseHistory.laterChosen at htag
            rw [← hactualK] at htag
            cases hcoordK : recordK.output.preparation.coordinator with
            | collection payloadK ledgerK clockK cutoffK outcomeK =>
                cases outcomeK with
                | laterChosen coreK consistentK startedK hstartK instructionK hassignmentK
                    outputK hlocalK clockDataK installedK selectedK =>
                    have hbirthK := ReferenceLaterInstallationProvenance.record_laterChosen_birth
                      recordK
                    rw [hcoordK] at hbirthK
                    exact False.elim (hnoBirth k (by omega) hkb installedK.registers.payload hbirthK)
                | clockFailure failureK hstartK => simp [hcoordK] at htag
                | localFailure startedK hstartK hcoreK reasonK => simp [hcoordK] at htag
                | coreFailure coreK startedK hstartK reasonK => simp [hcoordK] at htag
                | continuing coreK preparedK boundaryK checkedK => simp [hcoordK] at htag
                | laterReconstructionFailure coreK consistentK startedK hstartK instructionK
                    hassignmentK reasonK hlaterK => simp [hcoordK] at htag
                | laterPrefixFailure coreK consistentK startedK hstartK instructionK hassignmentK
                    armK reasonK hlaterK => simp [hcoordK] at htag
                | laterOrientationFailure coreK consistentK startedK hstartK instructionK
                    hassignmentK setK hlaterK => simp [hcoordK] at htag
                | laterChoiceFailure coreK consistentK startedK hstartK instructionK hassignmentK
                    outputK hlocalK clockDataK installedK reasonK => simp [hcoordK] at htag
            | first outcomeK => simp [hcoordK] at htag
            | live registersK ownedK baseK outcomeK => simp [hcoordK] at htag
            | invalidCollectionCutoff => simp [hcoordK] at htag
            | dagger => simp [hcoordK] at htag
      have hcell : z ∈ ReferenceActualCollectionHiddenRefreshPath.collectionPrefixCell
          rate rewards C_star C_h e b := by
        change e ≤ b ∧ b ≤ R.length ∧ ∃ he : e < R.length,
          match (R[ e ]).input.state.coordinator with
          | .live r _ _ =>
              ReferenceCollectionPhaseHistory.cutoffChosen (R[e].input) = true ∧
              s + b + 1 < r.gridBoundary ∧
              (∀ k : Fin R.length, e < k.val → k.val < b →
                ReferenceCollectionPhaseHistory.laterChosen (R[k.val]'k.isLt).input = false) ∧
              ∃ o, ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout
                rate rewards C_star C_h (s + b) z = some o ∧ o.2.1 = false
          | _ => False
        refine ⟨by omega, hbR, he, ?_⟩
        rw [hentryVal, hstateE]
        exact ⟨hcut, hstrict, hnoLater, ⟨Classical.choose hclear, hclearAt, hclearFlag⟩⟩
      have hcanonicalPayload : oldPayload rate rewards C_star C_h e b z hcell = r0.payload := by
        have hp : cutoffPayload? rate rewards C_star C_h e z = some rE.payload := by
          simp only [cutoffPayload?, hentry, Option.bind_some, hstateE]
        rw [oldPayload_eq rate rewards C_star C_h e b z hcell rE.payload hp]
        exact hpayloadE.trans hpayload
      refine ⟨e, b, record, u, theta, hcell, hrecord, hcallAt,
        by simpa [s] using hdate, seg.final, saved, ?_, ?_⟩
      · rw [hcanonicalPayload]
        exact hcoord
      · exact hcutoffFinal.trans hcutoffI

/-- The supplied source cap at the literal canonical queue parameters. -/
theorem collectionQueue_sourceCap
    (rate : ReferenceActivePhysicalStep.RateInput p) :
    (queueParameters rate).eta ≤ 1 /
      (1024 * (p.m : ℝ) * (p.K : ℝ) * (CanonicalRecordingRates.L_stab p : ℝ)) :=
  rate.sourceCap

private theorem collectionWord_prefixWeight
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (e b : ℕ)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : z ∈ collectionPrefixCell rate rewards C_star C_h e b)
    (k : ℕ) (hk : k ≤ b) :
    RecordedCorrectedWindow.prefixScoreWeight p (queueParameters rate)
        (collectionWord rate rewards C_star C_h e b z hz) k =
      fun i => AssignmentScoreReconstruction.sourceWeightBase p ^
        (calendarReplay rate (collectionWord rate rewards C_star C_h e b z hz) i k).1 := by
  let L := collectionWord rate rewards C_star C_h e b z hz
  let Q := queueParameters rate
  have hb : b ≤ L.length := collectionWord_bound rate rewards C_star C_h e b z hz
  have hclear : (RecordedQueueRun.run Q (L.take b)).overflow = false :=
    collectionWord_retained rate rewards C_star C_h e b z hz
  have hfirst : b < UnstoppedRecordedQueueComparison.firstOverflowPrefix Q L := by
    by_contra hnot
    have hover :=
      (UnstoppedRecordedQueueComparison.prefix_overflow_iff_first_overflow_prefix_le
        Q L b hb).mpr (Nat.le_of_not_gt hnot)
    rw [hclear] at hover
    cases hover
  have hnum := actualOriginalWord_numericalPrefix rate rewards C_star C_h z
    (collectionPrefixCell_launch rate rewards C_star C_h e b z hz) k (hk.trans hb)
  have hweight := hnum.2.1
  change RecordedQueueRun.scoreWeight Q (RecordedQueueRun.run Q (L.take k)) =
    (fun i => AssignmentScoreReconstruction.sourceWeightBase p ^
      (calendarReplay rate L i
        (min k (UnstoppedRecordedQueueComparison.firstOverflowPrefix Q L))).1) at hweight
  rw [Nat.min_eq_left (hk.trans hfirst.le)] at hweight
  exact hweight

private theorem selectedParameters_of_success
    {eta : ReferencePrelaunchFollower.LearningRate}
    (old : AssignmentStartPayload.Input p eta)
    (ledger : LaterAssignmentStartOperation.LocalLedger old)
    (instruction : CoordinatorPhaseClock.AssignmentStartInstruction p)
    (row : CompletePublicTable.CompleteRow p)
    (consistent : LaterAssignmentStartOperation.LocalConsistency old ledger)
    (output : LaterAssignmentStartOperation.SuccessfulStart old ledger instruction row) :
    LaterAssignmentStartMeasurability.selectedSamplerParameters?
        old ⟨ledger, instruction, consistent⟩ =
      some (output.law.mass, output.law.anchor) := by
  rw [LaterAssignmentJointCodeMeasurability.selectedSamplerParameters?_eq_match]
  have hpair :
      (⟨AssignmentScoreReconstruction.reconstructLaterStart ledger instruction, rfl⟩ :
        LaterAssignmentStartOperation.ReconstructionCall old ledger instruction) =
      ⟨.success ledger instruction output.reconstruction, output.reconstruction_eq⟩ := by
    apply LaterAssignmentStartOperation.ReconstructionCall.ext
    exact output.reconstruction_eq
  unfold LaterAssignmentStartOperation.decideReconstruction
  rw [hpair]
  change some (LaterAssignmentStartMeasurability.selectedSamplerParameters old ledger
    instruction output.reconstruction output.reconstruction_eq) =
      some (output.law.mass, output.law.anchor)
  apply congrArg some
  let selection := LaterAssignmentStartMeasurability.successfulLawSelection old ledger
    instruction output.reconstruction output.reconstruction_eq
  have hlaw : selection.law = output.law :=
    Option.some.inj (selection.lawSelected.symm.trans output.law_selected)
  exact congrArg (fun law => (law.mass, law.anchor)) hlaw

/-- The actual selector on a present nonrenewed invocation is the corrected
mass of the canonical original word, with the same cutoff, endpoint and old
anchor. Restoration is consumed on that very source, before any assignment
coordinate is restricted to an output fibre. -/
theorem actualNonrenewedCollectionCall_parameters
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hcall : actualNonrenewedCollectionCall rate rewards C_star C_h t z)
    (hclear : ∃ o,
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout
        rate rewards C_star C_h t.val z = some o ∧ o.2.1 = false) :
    ∃ (e b : ℕ)
      (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (u : Fin p.T) (theta : AssignmentParameterFibreKernel.Theta p)
      (hz : z ∈ collectionPrefixCell rate rewards C_star C_h e b),
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z =
        some record ∧
      ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h t z =
        some (u, theta) ∧
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + b = t.val ∧
      theta.1 = (RecordedCorrectedWindow.actualPrefixSamplerMass p (queueParameters rate)
        (collectionQueue_sourceCap rate) (collectionWord rate rewards C_star C_h e b z hz) e b
        (collectionPrefixCell_trigger_positive rate rewards C_star C_h e b z hz)
        hz.1 (collectionWord_bound rate rewards C_star C_h e b z hz)).weight ∧
      theta.2 = (oldPayload rate rewards C_star C_h e b z hz).anchor := by
  classical
  obtain ⟨e, b, chosenRecord, u, theta, hz, hrecord, hcallAt, hdate,
      incomingLedger, saved, hstate, hcutoff⟩ :=
    actualNonrenewedCollectionCall_prefixCell rate rewards C_star C_h t z hcall hclear
  let R := completeSuffixRecords rate z rewards C_star C_h
  let s := physicalStart rate z rewards C_star C_h
  let L := collectionWord rate rewards C_star C_h e b z hz
  let Q := queueParameters rate
  let P := oldPayload rate rewards C_star C_h e b z hz
  have hparameters : ReferenceLaterSamplerParameterMeasurability.parameters? chosenRecord.input =
      some theta := by
    have hselector : ReferenceFirstCollectionSamplerCall.collectionCallAt chosenRecord =
        some (u, theta) := by
      change (ReferenceSourcePrefixHistoryFiltration.actualRecord
        rate rewards C_star C_h t z).bind
          ReferenceFirstCollectionSamplerCall.collectionCallAt = some (u, theta) at hcallAt
      rw [hrecord] at hcallAt
      exact hcallAt
    obtain ⟨_payload, _ledger, _saved, _hstate, _hcutoff, hparameters⟩ :=
      (ReferenceFirstCollectionSamplerCall.collectionCallAt_spec chosenRecord u theta).mp hselector
    exact hparameters
  obtain ⟨record0, hrecord0, _hlater, hcorrected0⟩ :=
    (actualNonrenewedCollectionCall_successful rate rewards C_star C_h t z hcall).2
  have hsameRecord : record0 = chosenRecord := Option.some.inj (hrecord0.symm.trans hrecord)
  subst record0
  have hlookup : R[b]? = some chosenRecord := by
    change (if s ≤ t.val then R[t.val - s]? else none) = some chosenRecord at hrecord
    have hstart : s ≤ t.val := by change s + b = t.val at hdate; omega
    rw [ite_eq_left hstart] at hrecord
    have hindex : t.val - s = b := by change s + b = t.val at hdate; omega
    simpa only [hindex] using hrecord
  have hb : b < R.length := (List.getElem?_eq_some_iff.mp hlookup).1
  have hrecordB : R[b]'hb = chosenRecord :=
    Option.some.inj ((List.getElem?_eq_getElem hb).symm.trans hlookup)
  subst chosenRecord
  let record := R[b]'hb
  have hlaunch := collectionPrefixCell_launch rate rewards C_star C_h e b z hz
  have hrestore :=
    ReferenceCompleteOriginalCalendarWeightMarginalRestoration.complete_original_installation_weight_marginal_restoration
      rate rewards C_star C_h z
  rw [Classical.choose_spec hlaunch] at hrestore
  obtain ⟨word, _hlen, _hprefix, hfull, _hunique, _hbirths, hbranches, _hstates⟩ := hrestore
  have hword : word = L := by
    apply Option.some.inj
    exact hfull.symm.trans (actualOriginalWord_spec rate rewards C_star C_h z hlaunch)
  subst word
  have hbranch := hbranches ⟨b, hb⟩
  have horigin : actualDispatchOrigin record.output.preparation.coordinator := by
    have hprepared := actualDispatchOrigin_prepared rate record.input
    have hprep : record.output.preparation = ReferenceActivePhysicalStep.prepare record.input := by
      rw [record.output_eq]
      rfl
    rw [← hprep] at hprepared
    exact hprepared
  have hselected : ReferenceLaterAssignmentFibreStep.dispatchParameters?
      record.output.preparation.coordinator = some theta := by
    have hparam := ReferenceLaterAssignmentFibreStep.parameters?_eq_physicalDispatch record.input
    change ReferenceLaterAssignmentFibreStep.parameters? record.input = some theta at hparameters
    rw [hparam] at hparameters
    have hdispatch : ReferenceActivePhysicalStep.dispatch record.input =
        record.output.preparation.coordinator := by rw [record.output_eq]; rfl
    rw [hdispatch] at hparameters
    exact hparameters
  dsimp only [record, R] at hcorrected0 horigin hselected
  cases hcoord : ((completeSuffixRecords rate z rewards C_star C_h)[b]'hb).output.preparation.coordinator with
  | collection payload ledger clock cutoff outcome =>
      cases outcome with
      | laterChosen core consistent started hstart instruction hassignment output hlocal
          clockData installed selected =>
          have hkind : instruction.kind = .corrected := by
            simpa only [hcoord] using hcorrected0
          obtain ⟨a, e0, seg, _hae, _heb, _hbirth, _hsegment, _hlength, _hfinal,
              _hpending, _htime, hcutoff0, _hregisters, hcurrent, hcut,
              _hmarginal, _hcutMarginal, hscale, hcases⟩ := by
            simpa only [hcoord] using hbranch
          obtain ⟨saved0, hstate0⟩ := by
            simpa only [actualDispatchOrigin, hcoord] using horigin
          have hident := ReferenceActivePhysicalStep.CoordinatorConfiguration.collection.inj
            (hstate0.symm.trans hstate)
          have hpayload : payload = P := hident.1
          have hledger : ledger = incomingLedger := hident.2.1
          have he0 : e0 = e := by
            rw [hledger] at hcutoff0
            change incomingLedger.cutoff = s + e0 + 1 at hcutoff0
            change incomingLedger.cutoff = s + e + 1 at hcutoff
            omega
          subst e0
          have hcorrected := hcases.resolve_right (by
            rintro ⟨hrenewal, _⟩
            rw [hkind] at hrenewal
            cases hrenewal)
          obtain ⟨_hkind, _hbefore, hprevious, _houtputAnchor, _hinstalledAnchor,
            hmass, hraw⟩ := hcorrected
          have htheta : theta = (output.law.mass, output.law.anchor) := by
            rw [hcoord] at hselected
            change LaterAssignmentStartMeasurability.selectedSamplerParameters?
              _ ⟨_, instruction, consistent⟩ = some theta at hselected
            rw [selectedParameters_of_success _ _ instruction _ consistent output] at hselected
            exact (Option.some.inj hselected).symm
          obtain ⟨previous, hprevious0, hanchor, _⟩ :=
            LaterAssignmentStartOperation.selectLaw?_corrected_spec _ _ instruction
              output.reconstruction output.cutoffReached output.currentWeight_pos
              output.law output.law_selected hkind
          have hpreviousEq := Option.some.inj (hprevious0.symm.trans hprevious)
          have hweight : output.law.mass =
              (RecordedCorrectedWindow.actualPrefixSamplerMass p Q (collectionQueue_sourceCap rate) L e b
                (collectionPrefixCell_trigger_positive rate rewards C_star C_h e b z hz)
                hz.1 (collectionWord_bound rate rewards C_star C_h e b z hz)).weight := by
            funext S
            rw [hmass S, hraw S, hscale]
            rw [RecordedCorrectedWindow.actualPrefixSamplerMass_weight,
              RecordedCorrectedWindow.actualPrefixCorrectedMass_formula]
            have hwB := collectionWord_prefixWeight rate rewards C_star C_h e b z hz b le_rfl
            have hwE := collectionWord_prefixWeight rate rewards C_star C_h e b z hz e hz.1
            have hwPrevious := collectionWord_prefixWeight rate rewards C_star C_h e b z hz
              (e - 1) (by omega)
            unfold RecordedCorrectedWindow.prefixQ
            rw [hwB, hwE, hwPrevious]
            rfl
          refine ⟨e, b, record, u, theta, hz, hrecord, hcallAt, hdate, ?_, ?_⟩
          · exact (congrArg Prod.fst htheta).trans hweight
          · exact (congrArg Prod.snd htheta).trans (hanchor.trans (congrArg (fun x => x.anchor) hpayload))
      | clockFailure failure hstart => simp only [hcoord] at hcorrected0
      | localFailure started hstart hcore reason => simp only [hcoord] at hcorrected0
      | coreFailure core started hstart reason => simp only [hcoord] at hcorrected0
      | continuing core prepared boundary checked => simp only [hcoord] at hcorrected0
      | laterReconstructionFailure core consistent started hstart instruction hassignment reason hlater =>
          simp only [hcoord] at hcorrected0
      | laterPrefixFailure core consistent started hstart instruction hassignment arm reason hlater =>
          simp only [hcoord] at hcorrected0
      | laterOrientationFailure core consistent started hstart instruction hassignment set hlater =>
          simp only [hcoord] at hcorrected0
      | laterChoiceFailure core consistent started hstart instruction hassignment output hlocal
          clockData installed reason => simp only [hcoord] at hcorrected0
  | first outcome => simp only [hcoord] at hcorrected0
  | live registers owned base outcome => simp only [hcoord] at hcorrected0
  | invalidCollectionCutoff => simp only [hcoord] at hcorrected0
  | dagger => simp only [hcoord] at hcorrected0

/-- The actual nonrenewed invocation consumes the accepted canonical endpoint
atom on its produced literal prefix cell, retaining the source's signed
finite-window correction and old anchor. -/
theorem actualNonrenewedCollectionCall_endpointAtom
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hcall : actualNonrenewedCollectionCall rate rewards C_star C_h t z)
    (hclear : ∃ o,
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout
        rate rewards C_star C_h t.val z = some o ∧ o.2.1 = false)
    (U : CanonicalOrientedSetLaw.SlowSet p.K p.m) :
    ∃ (e b : ℕ)
      (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (u : Fin p.T) (theta : AssignmentParameterFibreKernel.Theta p)
      (hcell : z ∈ ReferenceActualCollectionHiddenRefreshPath.collectionPrefixCell
        rate rewards C_star C_h e b),
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z =
        some record ∧
      ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h t z =
        some (u, theta) ∧
      (auxiliaryUniformLaw p).real
        {array : AuxiliaryArray p |
          sampledArrayPath rate rewards C_star C_h e b z hcell (b - e) (by omega) array
            (Fin.last (b - e)) = U} =
        DeferredRefreshWindow.slowMassAt p (queueParameters rate)
            (collectionWord rate rewards C_star C_h e b z hcell)
            (oldPayload rate rewards C_star C_h e b z hcell).anchor
            (oldPayload rate rewards C_star C_h e b z hcell).anchor_pos b U +
          (1 - 4 * (p.m : ℝ) * rate.eta.val) ^ (b - e + 1) /
            (4 * (p.m : ℝ) * rate.eta.val) *
            (DeferredRefreshWindow.slowMassAt p (queueParameters rate)
                (collectionWord rate rewards C_star C_h e b z hcell)
                (oldPayload rate rewards C_star C_h e b z hcell).anchor
                (oldPayload rate rewards C_star C_h e b z hcell).anchor_pos e U -
              DeferredRefreshWindow.slowMassAt p (queueParameters rate)
                (collectionWord rate rewards C_star C_h e b z hcell)
                (oldPayload rate rewards C_star C_h e b z hcell).anchor
                (oldPayload rate rewards C_star C_h e b z hcell).anchor_pos (e - 1) U) := by
  obtain ⟨e, b, record, u, theta, hcell, hrecord, hcallAt, _hdate, _hledger⟩ :=
    actualNonrenewedCollectionCall_prefixCell rate rewards C_star C_h t z hcall hclear
  exact ⟨e, b, record, u, theta, hcell, hrecord, hcallAt,
    actual_collection_endpoint_atom rate rewards C_star C_h e b z hcell U⟩

/-- One actual present nonrenewed invocation determines the canonical endpoint
and the literal fibre of its existing full `K + 1` assignment-vector sampler.
The `none` fibre is null, and every `some U` atom is retained, including zero
mass. The signed expression uses the unchanged old anchor throughout. -/
theorem actualNonrenewedCollectionCall_endpoint_fibre
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hcall : actualNonrenewedCollectionCall rate rewards C_star C_h t z)
    (hclear : ∃ o,
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout
        rate rewards C_star C_h t.val z = some o ∧ o.2.1 = false) :
    ∃ (e b : ℕ)
      (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (u : Fin p.T) (theta : AssignmentParameterFibreKernel.Theta p)
      (actualCall : ReferenceLaterSamplerParameterMeasurability.ActualSamplerCall
        (p := p) (rate := rate))
      (hz : z ∈ collectionPrefixCell rate rewards C_star C_h e b),
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z =
        some record ∧
      ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h t z =
        some (u, theta) ∧
      physicalStart rate z rewards C_star C_h + b = t.val ∧
      actualCall.val = record.input ∧
      ReferenceLaterSamplerParameterMeasurability.actualParameter actualCall = theta ∧
      let L := collectionWord rate rewards C_star C_h e b z hz
      let P := oldPayload rate rewards C_star C_h e b z hz
      let he := collectionPrefixCell_trigger_positive rate rewards C_star C_h e b z hz
      let hb := collectionWord_bound rate rewards C_star C_h e b z hz
      let mass := RecordedCorrectedWindow.actualPrefixSamplerMass p (queueParameters rate)
        (collectionQueue_sourceCap rate) L e b he hz.1 hb
      theta.1 = mass.weight ∧ theta.2 = P.anchor ∧
      (∀ vector : AssignmentParameterFibreKernel.AssignmentVector p,
        AssignmentParameterFibreKernel.successfulSlowSet p theta vector =
          some (CorrectedAssignmentVector.correctedSlowSampler p (queueParameters rate)
            (collectionQueue_sourceCap rate) L e b he hz.1 hb P.anchor P.anchor_pos vector)) ∧
      AssignmentParameterFibreKernel.fibreMass p theta none = 0 ∧
      ∀ U : CanonicalOrientedSetLaw.SlowSet p.K p.m,
        (auxiliaryUniformLaw p)
            {array : AuxiliaryArray p |
              sampledArrayPath rate rewards C_star C_h e b z hz (b - e) (by omega) array
                (Fin.last (b - e)) = U} =
          AssignmentParameterFibreKernel.fibreMass p theta (some U) ∧
        (AssignmentParameterFibreKernel.fibreMass p theta (some U)).toReal =
          DeferredRefreshWindow.slowMassAt p (queueParameters rate) L
              P.anchor P.anchor_pos b U +
            (1 - 4 * (p.m : ℝ) * rate.eta.val) ^ (b - e + 1) /
              (4 * (p.m : ℝ) * rate.eta.val) *
              (DeferredRefreshWindow.slowMassAt p (queueParameters rate) L
                  P.anchor P.anchor_pos e U -
                DeferredRefreshWindow.slowMassAt p (queueParameters rate) L
                  P.anchor P.anchor_pos (e - 1) U) := by
  obtain ⟨e, b, record, u, theta, hz, hrecord, hcallAt, hdate, hweight, hanchor⟩ :=
    actualNonrenewedCollectionCall_parameters rate rewards C_star C_h t z hcall hclear
  obtain ⟨record0, u0, theta0, actualCall, hrecord0, hcallAt0, hinput, hactual⟩ :=
    actualNonrenewedCollectionCall_actualParameter rate rewards C_star C_h t z hcall
  have hrecordEq : record0 = record := Option.some.inj (hrecord0.symm.trans hrecord)
  have hthetaEq : theta0 = theta :=
    congrArg Prod.snd (Option.some.inj (hcallAt0.symm.trans hcallAt))
  have hactualInput : actualCall.val = record.input :=
    hinput.trans (congrArg (fun r => r.input) hrecordEq)
  have hactualParameter :
      ReferenceLaterSamplerParameterMeasurability.actualParameter actualCall = theta :=
    hactual.trans hthetaEq
  let L := collectionWord rate rewards C_star C_h e b z hz
  let P := oldPayload rate rewards C_star C_h e b z hz
  let Q := queueParameters rate
  have he := collectionPrefixCell_trigger_positive rate rewards C_star C_h e b z hz
  have hb := collectionWord_bound rate rewards C_star C_h e b z hz
  let mass := RecordedCorrectedWindow.actualPrefixSamplerMass p Q
    (collectionQueue_sourceCap rate) L e b he hz.1 hb
  have htheta : theta = (mass.weight, P.anchor) := Prod.ext hweight hanchor
  have hsampler : ∀ vector : AssignmentParameterFibreKernel.AssignmentVector p,
      AssignmentParameterFibreKernel.successfulSlowSet p theta vector =
        some (CorrectedAssignmentVector.correctedSlowSampler p Q
          (collectionQueue_sourceCap rate) L e b he hz.1 hb P.anchor P.anchor_pos vector) := by
    intro vector
    rw [htheta]
    exact CheckedAssignmentSample.actualCorrected_successfulSlowSet_eq_sampler p Q
      (collectionQueue_sourceCap rate) L e b he hz.1 hb P.anchor P.anchor_pos vector
  have hnone : AssignmentParameterFibreKernel.fibreMass p theta none = 0 := by
    have hempty : FiniteFibreLift.fibre
        (AssignmentParameterFibreKernel.successfulSlowSet p theta) none = ∅ := by
      ext vector
      change AssignmentParameterFibreKernel.successfulSlowSet p theta vector = none ↔ False
      rw [hsampler vector]
      simp only [reduceCtorEq]
    change ContinuousControlSlice.assignmentLaw p.K
      (FiniteFibreLift.fibre (AssignmentParameterFibreKernel.successfulSlowSet p theta) none) = 0
    rw [hempty, MeasureTheory.measure_empty]
  refine ⟨e, b, record, u, theta, actualCall, hz, hrecord, hcallAt, hdate,
    hactualInput, hactualParameter, hweight, hanchor, hsampler, hnone, ?_⟩
  intro U
  have hfibre : AssignmentParameterFibreKernel.fibreMass p theta (some U) =
      ENNReal.ofReal (CorrectedAssignmentVector.slowFibreMass p Q
        (collectionQueue_sourceCap rate) L e b he hz.1 hb P.anchor P.anchor_pos U) := by
    rw [htheta]
    exact CheckedAssignmentSample.actualCorrected_checkedSlow_fibreMass p Q
      (collectionQueue_sourceCap rate) L e b he hz.1 hb P.anchor P.anchor_pos U
  have hendpoint : (auxiliaryUniformLaw p).real
      {array : AuxiliaryArray p |
        sampledArrayPath rate rewards C_star C_h e b z hz (b - e) (by omega) array
          (Fin.last (b - e)) = U} =
      CorrectedAssignmentVector.slowFibreMass p Q (collectionQueue_sourceCap rate)
        L e b he hz.1 hb P.anchor P.anchor_pos U :=
    actual_collection_endpoint_atom rate rewards C_star C_h e b z hz U
  constructor
  · calc
      _ = ENNReal.ofReal ((auxiliaryUniformLaw p).real
          {array : AuxiliaryArray p |
            sampledArrayPath rate rewards C_star C_h e b z hz (b - e) (by omega) array
              (Fin.last (b - e)) = U}) := (MeasureTheory.ofReal_measureReal).symm
      _ = _ := (congrArg ENNReal.ofReal hendpoint).trans hfibre.symm
  · rw [hfibre, ENNReal.toReal_ofReal
      (CorrectedAssignmentVector.slowFibreMass_nonneg p Q (collectionQueue_sourceCap rate)
        L e b he hz.1 hb P.anchor P.anchor_pos U)]
    rfl

end Bandits.Support.ReferenceActualCollectionNonrenewedEndpointFibreJoin

end
