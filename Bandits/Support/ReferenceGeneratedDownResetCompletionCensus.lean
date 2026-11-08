/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedDownCohortFiniteUnion
public import Bandits.Support.ReferenceGeneratedInheritedDownFirstCompletion

import Lean.Elab.Tactic.Omega

/-!
# Actual generated DOWN reset completion census

Sources: `sources/zip4/manuscript/05_binary_transport.tex:20-42`,
`sources/zip4/manuscript/07_public_setup.tex:127-164`,
`sources/zip4/manuscript/08_main_theorem.tex:29-47`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:92-157`.

This module concerns the actual full physical DOWN run generated from the
launch source. A completion is the literal decoder quota transition, including
failed or inconsistent decoding and later physical failure. It proves no
probability estimate or manuscript error-event coverage.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Bandits.Support.ReferenceGeneratedDownResetCompletionCensus

open Bandits.Support.ConstructorDimensions
open Bandits.Support.AffineBatchDecoder
open Bandits.Support.ReferenceGeneratedDownBatchCalendar
open Bandits.Support.ReferenceDownCompletedAmbiguityMeasurability
open Bandits.Support.ReferenceFollowerDownDecoderReplay
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ActiveFollowerDownAcceptance
open Bandits.Support.ReferencePrelaunchFollower

variable {p : ConstructorDimensions.Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}

private theorem finishFollower_downInput_none_of_occupied
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (prepared : DeclaredFollowerLocalRound.PreparedRound p rate)
    (observation : ReferencePrelaunchFollower.Observation p)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hconfiguration : prepared.configuration = .ordinary state memory)
    (hoccupied : state.status ≠ .unoccupied) :
    (ReferenceActivePhysicalStep.finishFollower view prepared observation).downInput = none := by
  simp only [ReferenceActivePhysicalStep.finishFollower, hconfiguration,
    ReferenceActivePhysicalStep.recordFollower, dite_eq_right hoccupied]
  cases hrecord : DeclaredFollowerLocalRound.recordOrServiceThenDown rate prepared.follower
      prepared.row prepared.activation prepared.time prepared.active prepared.arm observation state with
  | error failure => simp
  | ok postRecord =>
      cases hrelease : DeclaredFollowerLocalRound.releaseAndFinish rate
          prepared.follower prepared.row prepared.time observation state memory postRecord with
      | error failure => simp [hrelease]
      | ok next => simp [hrelease]

private theorem record_logged_choice
    (record : ReferenceFollowerDownDecoderReplay.Record p rate) (i : Fin (p.m - 1))
    (logged : ReferencePrelaunchFollower.State p rate.eta)
    (hlogged : (record.output.followers i).downInput = some logged) :
    ∃ state memory,
      ReferenceFollowerDownDecoderReplay.preparedChoiceConfiguration record i =
        .ordinary state memory ∧
      state.status = .unoccupied ∧ logged.status = state.status ∧
      logged.downBatch = state.downBatch := by
  classical
  let prepared := record.output.preparation.followers.followers i
  let observation := ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i
  have hdiagnostic := ReferenceDownCompletedAmbiguityMeasurability.record_preparationDiagnostics
    record i
  have hlogged' : (record.output.preparation.observeFollower i).downInput = some logged := by
    rw [hdiagnostic]
    exact hlogged
  have hfinish :
      (ReferenceActivePhysicalStep.finishFollower
        record.output.preparation.coordinator.downView prepared observation).downInput =
        some logged := by
    simpa only [prepared, observation,
      ReferenceFollowerDownDecoderReplay.preparedOwnObservation,
      ReferenceActivePhysicalStep.PreparedRound.observeFollower] using hlogged'
  cases hconfiguration : prepared.configuration with
  | dagger => simp [ReferenceActivePhysicalStep.finishFollower, hconfiguration] at hfinish
  | ordinary state memory =>
      by_cases hstatus : state.status = .unoccupied
      · cases hlogging : ActiveFollowerLogging.checkedLogging prepared.follower prepared.row
            prepared.activation prepared.time (prepared.arm, observation) state with
        | error failure =>
            simp [ReferenceActivePhysicalStep.finishFollower,
              ReferenceActivePhysicalStep.recordFollower, hconfiguration, hstatus,
              hlogging] at hfinish
        | ok actualLogged =>
            cases hresult : DeclaredFollowerLocalRound.consumeDownResult rate
                (ReferenceDownReception.referenceDownCut p
                  record.output.preparation.coordinator.downView prepared.follower prepared.row
                  prepared.time observation rate actualLogged).outcome with
            | error failure =>
                have hloggedEq : actualLogged = logged := by
                  simpa [ReferenceActivePhysicalStep.finishFollower,
                    ReferenceActivePhysicalStep.recordFollower, hconfiguration, hstatus,
                    hlogging, hresult] using hfinish
                subst actualLogged
                have hframe := ActiveFollowerLogging.checkedLogging_success_frame
                  prepared.follower prepared.row prepared.activation prepared.time
                  (prepared.arm, observation) state logged hlogging
                rcases hframe with ⟨_, _, _, _, hloggedStatus, hloggedBatch, _⟩
                exact ⟨state, memory, by simp [prepared,
                  ReferenceFollowerDownDecoderReplay.preparedChoiceConfiguration,
                  hconfiguration], hstatus, hloggedStatus, hloggedBatch⟩
            | ok post =>
                cases hrelease : DeclaredFollowerLocalRound.releaseAndFinish rate
                    prepared.follower prepared.row prepared.time observation state memory post with
                | error failure =>
                    have hloggedEq : actualLogged = logged := by
                      simpa [ReferenceActivePhysicalStep.finishFollower,
                        ReferenceActivePhysicalStep.recordFollower, hconfiguration, hstatus,
                        hlogging, hresult, hrelease] using hfinish
                    subst actualLogged
                    have hframe := ActiveFollowerLogging.checkedLogging_success_frame
                      prepared.follower prepared.row prepared.activation prepared.time
                      (prepared.arm, observation) state logged hlogging
                    rcases hframe with ⟨_, _, _, _, hloggedStatus, hloggedBatch, _⟩
                    exact ⟨state, memory, by simp [prepared,
                      ReferenceFollowerDownDecoderReplay.preparedChoiceConfiguration,
                      hconfiguration], hstatus, hloggedStatus, hloggedBatch⟩
                | ok result =>
                    cases result with
                    | mk final finalMemory =>
                        have hloggedEq : actualLogged = logged := by
                          simpa [ReferenceActivePhysicalStep.finishFollower,
                            ReferenceActivePhysicalStep.recordFollower, hconfiguration,
                            hstatus, hlogging, hresult, hrelease] using hfinish
                        subst actualLogged
                        have hframe := ActiveFollowerLogging.checkedLogging_success_frame
                          prepared.follower prepared.row prepared.activation prepared.time
                          (prepared.arm, observation) state logged hlogging
                        rcases hframe with ⟨_, _, _, _, hloggedStatus, hloggedBatch, _⟩
                        exact ⟨state, memory, by simp [prepared,
                          ReferenceFollowerDownDecoderReplay.preparedChoiceConfiguration,
                          hconfiguration], hstatus, hloggedStatus, hloggedBatch⟩
      · rw [finishFollower_downInput_none_of_occupied
          record.output.preparation.coordinator.downView prepared observation state memory
          hconfiguration hstatus] at hfinish
        cases hfinish

/-- A completed-batch diagnostic is exactly an actual executed DOWN call whose
same logged decoder state reaches quota. The equivalence retains the actual
record's time, selected row, own observation, and current-input extension. -/
theorem completedBatchAtRound_iff_executed_quota
    (record : ReferenceFollowerDownDecoderReplay.Record p rate) (i : Fin (p.m - 1)) :
    ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate
        (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation record.input i) ↔
      ∃ logged : ReferencePrelaunchFollower.State p rate.eta,
        ∃ cut : ReferenceDownReception.ReferenceDownCutOutput p rate,
          (record.output.followers i).downInput = some logged ∧
          (record.output.followers i).down = some cut ∧
          cut.rawComparison.isSome = true ∧
          AffineBatchDecoder.quota p ≤
            (logged.downBatch.pending ++ AffineBatchDecoder.positiveAt p
              (ActiveFollowerDownAcceptance.currentInputExtension p
                (ActiveFollowerDownAcceptance.currentRoundInput p i record.input.row
                  record.input.time
                  (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i)
                  rate logged)) record.input.time).length := by
  classical
  constructor
  · intro hcomplete
    obtain ⟨callCode, logged, cut, hcall, hlogged, hcut, hcomparison, hpositive, hquota⟩ :=
      ReferenceGeneratedDownBatchBankBridge.completedBatchAtRound_actual_fields
        record i hcomplete
    have hcutActual := ReferenceDownCompletedAmbiguityMeasurability.record_downCut_eq_actual
      record i logged cut hlogged hcut
    have hgateEq := ReferenceActiveAffinePositiveTest.referenceDownCut_has_call
      record.output.preparation.coordinator.downView i record.input.row record.input.time
      (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i) logged
    have hcomparison' :
        Option.isSome (ReferenceDownReception.referenceDownCut p
          record.output.preparation.coordinator.downView i record.input.row record.input.time
          (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i) rate logged).rawComparison =
          true := by
      rw [← hcutActual]
      exact hcomparison
    rw [hgateEq] at hcomparison'
    have hgate : ReferenceActiveAffinePositiveTest.downReceiverGate i record.input.row
        record.input.time logged := of_decide_eq_true hcomparison'
    let tr := ActiveFollowerDownAcceptance.currentInputExtension p
      (ActiveFollowerDownAcceptance.currentRoundInput p i record.input.row record.input.time
        (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i) rate logged)
    have helig : AffineBatchDecoder.eligible (tr record.input.time) :=
      (ActiveFollowerDownAcceptance.currentRoundInput_eligible_iff p i record.input.row
        record.input.time (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i)
        rate logged).2 ⟨hgate.1, hgate.2.1, hpositive⟩
    have hpositiveAt : AffineBatchDecoder.positiveAt p tr record.input.time =
        [AffineBatchDecoder.entry p tr record.input.time] := by
      simp [AffineBatchDecoder.positiveAt, helig]
    refine ⟨logged, cut, hlogged, hcut, hcomparison, ?_⟩
    have hlen : (logged.downBatch.pending ++
        AffineBatchDecoder.positiveAt p tr record.input.time).length =
        AffineBatchDecoder.quota p := by
      rw [hpositiveAt]
      simp only [List.length_append, List.length_singleton]
      omega
    exact hlen.ge
  · rintro ⟨logged, cut, hlogged, hcut, hcomparison, hquota⟩
    obtain ⟨state, memory, hconfiguration, hstatus, hloggedStatus, hloggedBatch⟩ :=
      record_logged_choice record i logged hlogged
    let prepared := record.output.preparation.followers.followers i
    have hrow : ReferenceFollowerDownDecoderReplay.preparedChoiceRow record i = record.input.row :=
      (record.output.preparation.follower_alignment i).1
    have htime : ReferenceFollowerDownDecoderReplay.preparedChoiceTime record i =
        record.input.time := (record.output.preparation.follower_alignment i).2.2.1
    let call : ReferenceFollowerDownDecoderReplay.Call p :=
      (record.input.time, ActiveFollowerDownAcceptance.currentRoundInput p i record.input.row
        record.input.time (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i)
        rate state)
    have hactualCall : ReferenceFollowerDownDecoderReplay.actualDownCall i record = some call := by
      simp [call, ReferenceFollowerDownDecoderReplay.actualDownCall,
        hconfiguration, hrow, htime]
    have hcallCode : ∃ callCode,
        ReferenceDownCompletedAmbiguityMeasurability.downCallObservation i record =
          some callCode := by
      cases hcode : ReferenceDownCompletedAmbiguityMeasurability.downCallObservation i record with
      | none =>
          have hrec := ReferenceDownCompletedAmbiguityMeasurability.downCallObservation_reconstructs
            i record
          rw [hcode, Option.map_none, hactualCall] at hrec
          contradiction
      | some callCode => exact ⟨callCode, rfl⟩
    obtain ⟨callCode, hcallCode⟩ := hcallCode
    have hdecodedCall :
        ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCode = call := by
      have hrec := ReferenceDownCompletedAmbiguityMeasurability.downCallObservation_reconstructs
        i record
      rw [hcallCode, Option.map_some, hactualCall] at hrec
      exact Option.some.inj hrec
    have hcallTime : callCode.1 = record.input.time := by
      have h := congrArg Prod.fst hdecodedCall
      exact h
    have hcutActual := ReferenceDownCompletedAmbiguityMeasurability.record_downCut_eq_actual
      record i logged cut hlogged hcut
    have hgateEq := ReferenceActiveAffinePositiveTest.referenceDownCut_has_call
      record.output.preparation.coordinator.downView i record.input.row record.input.time
      (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i) logged
    have hcomparison' :
        Option.isSome (ReferenceDownReception.referenceDownCut p
          record.output.preparation.coordinator.downView i record.input.row record.input.time
          (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i) rate logged).rawComparison =
          true := by
      rw [← hcutActual]
      exact hcomparison
    rw [hgateEq] at hcomparison'
    have hgate : ReferenceActiveAffinePositiveTest.downReceiverGate i record.input.row
        record.input.time logged := of_decide_eq_true hcomparison'
    let tr := ActiveFollowerDownAcceptance.currentInputExtension p
      (ActiveFollowerDownAcceptance.currentRoundInput p i record.input.row record.input.time
        (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i)
        rate logged)
    have hinput : ActiveFollowerDownAcceptance.currentRoundInput p i record.input.row
        record.input.time (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i)
        rate state =
      ActiveFollowerDownAcceptance.currentRoundInput p i record.input.row record.input.time
        (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i) rate logged := by
      simp [ActiveFollowerDownAcceptance.currentRoundInput, hloggedStatus]
    have hpendingLt : logged.downBatch.pending.length < AffineBatchDecoder.quota p :=
      hgate.2.2.2.1.1
    have helig : AffineBatchDecoder.eligible (tr record.input.time) := by
      by_contra hnot
      have hnone : AffineBatchDecoder.positiveAt p tr record.input.time = [] := by
        simp [AffineBatchDecoder.positiveAt, hnot]
      rw [hnone] at hquota
      simp only [List.append_nil] at hquota
      omega
    have hpositive :
        0 < (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i).val.val :=
      ((ActiveFollowerDownAcceptance.currentRoundInput_eligible_iff p i record.input.row
        record.input.time (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i)
        rate logged).mp (by simpa [tr, ActiveFollowerDownAcceptance.currentInputExtension] using helig)).2.2
    have hpositiveAt : AffineBatchDecoder.positiveAt p tr record.input.time =
        [AffineBatchDecoder.entry p tr record.input.time] := by
      simp [AffineBatchDecoder.positiveAt, helig]
    have hquotaEq : logged.downBatch.pending.length + 1 = AffineBatchDecoder.quota p := by
      have hlen := hquota
      rw [hpositiveAt] at hlen
      simp only [List.length_append, List.length_singleton] at hlen
      omega
    have hdecodeInput :
        (ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCode).2 =
          ActiveFollowerDownAcceptance.currentRoundInput p i record.input.row record.input.time
            (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i) rate logged := by
      have h := congrArg Prod.snd hdecodedCall
      simpa [call, hinput] using h
    have hdecodedBank :
        ReferenceDownCompletedAmbiguityMeasurability.decodedLoggedBank callCode
          (FollowerDownMeasurability.followerStateCode rate logged) =
        ⟨[], logged.downBatch.completed ++
          [logged.downBatch.pending ++
            [⟨record.input.time,
              (ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCode).2.sample⟩]]⟩ := by
      have hstep := AffineBatchDecoder.decodeStep_complete p
        (ActiveFollowerDownAcceptance.currentInputExtension p
          (ActiveFollowerDownAcceptance.currentRoundInput p i record.input.row record.input.time
            (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i) rate logged))
        logged.downBatch record.input.time helig hquotaEq
      have hentry : AffineBatchDecoder.entry p
          (ActiveFollowerDownAcceptance.currentInputExtension p
            (ActiveFollowerDownAcceptance.currentRoundInput p i record.input.row record.input.time
              (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i) rate logged))
          record.input.time =
            ⟨record.input.time,
              (ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCode).2.sample⟩ := by
        simp only [AffineBatchDecoder.entry, ActiveFollowerDownAcceptance.currentInputExtension]
        congr 1
        exact (congrArg (fun input => input.sample) hdecodeInput).symm
      have hfirst := congrArg Prod.fst hstep
      rw [hentry] at hfirst
      have hinputExt :
          ({(ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCode).2 with
            receiverEnabled := decide
              (FollowerDownMeasurability.followerStatusOfCode
                (FollowerDownMeasurability.followerStateCode rate logged).status =
                ActiveRoundActions.FollowerStatus.unoccupied)} :
              AffineBatchDecoder.RoundInput (AffineBatchDecoder.width p)) =
            ActiveFollowerDownAcceptance.currentRoundInput p i record.input.row
              record.input.time (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i)
              rate logged := by
        simp [hdecodeInput, FollowerDownMeasurability.followerStateCode,
          FollowerDownMeasurability.followerStatusOfCode_code,
          ActiveFollowerDownAcceptance.currentRoundInput]
      have hbatch : FollowerDownMeasurability.decoderBatchOfCode
          (FollowerDownMeasurability.followerStateCode rate logged).downBatch =
          logged.downBatch := by
        exact FollowerDownMeasurability.decoderBatchOfCode_code logged.downBatch
      have hdecoder := congrArg Prod.fst hstep
      rw [hentry] at hdecoder
      change ReferenceDownCompletedAmbiguityMeasurability.decodedLoggedBank callCode
          (FollowerDownMeasurability.followerStateCode rate logged) = _
      unfold ReferenceDownCompletedAmbiguityMeasurability.decodedLoggedBank
      rw [hinputExt, hbatch, hcallTime]
      simpa [hcallTime] using hdecoder
    have hpositiveGrid :
        0 < (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation
          record.input i).2.1.val := by
      have hgrid : ReferenceDownCompletedAmbiguityMeasurability.ownGrid record.input i =
          record.gridFeedback (PublicDiscreteDraws.followerPlayer p.two_le_m i) :=
        congrFun (ReferenceActiveHorizonMeasurability.roundRecordCode_front
          record).2.2.2 (PublicDiscreteDraws.followerPlayer p.two_le_m i)
      have hfeedback := record.output.preparation.feedback.observations_eq
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)
      have hobsValue :
          (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i).val.val =
            ((ReferenceDownCompletedAmbiguityMeasurability.ownGrid record.input i).val : ℝ) /
              (ConstructorDimensions.D p : ℝ) := by
        calc
          _ = (ActualInitializationPhysicalStep.observationOfGrid p
              (record.output.preparation.feedback.feedback
                (PublicDiscreteDraws.followerPlayer p.two_le_m i))).val.val := by
                exact congrArg (fun obs : ReferencePrelaunchFollower.Observation p => obs.val.val)
                  (by simpa only [ReferenceFollowerDownDecoderReplay.preparedOwnObservation] using hfeedback)
          _ = ((record.gridFeedback (PublicDiscreteDraws.followerPlayer p.two_le_m i)).val : ℝ) /
                (ConstructorDimensions.D p : ℝ) := by
                exact ActualInitializationPhysicalStep.observationOfGrid_value p _
          _ = ((ReferenceDownCompletedAmbiguityMeasurability.ownGrid record.input i).val : ℝ) /
                (ConstructorDimensions.D p : ℝ) := by rw [← hgrid]
      have hD : (0 : ℝ) < (ConstructorDimensions.D p : ℝ) := by
        exact_mod_cast ConstructorDimensions.D_pos p
      have hquot : 0 <
          ((ReferenceDownCompletedAmbiguityMeasurability.ownGrid record.input i).val : ℝ) /
            (ConstructorDimensions.D p : ℝ) := by
        rw [← hobsValue]
        exact hpositive
      have hy : 0 <
          ((ReferenceDownCompletedAmbiguityMeasurability.ownGrid record.input i).val : ℝ) :=
        (div_pos_iff_of_pos_right hD).mp hquot
      have hpositiveObs :
          0 < (ActualInitializationPhysicalStep.observationOfGrid p
            (ReferenceDownCompletedAmbiguityMeasurability.ownGrid record.input i)).val.val := by
        rw [ActualInitializationPhysicalStep.observationOfGrid_value]
        exact div_pos hy hD
      rw [ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation]
      exact_mod_cast hy
    have hpositiveGridNat :
        0 < (ReferenceDownCompletedAmbiguityMeasurability.ownGrid record.input i).val := by
      simpa [ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation] using hpositiveGrid
    have hpositiveGridReal :
        0 < ((ReferenceDownCompletedAmbiguityMeasurability.ownGrid record.input i).val : ℝ) := by
      exact_mod_cast hpositiveGridNat
    have hpositiveDen : 0 < (ConstructorDimensions.D p : ℝ) := by
      exact_mod_cast ConstructorDimensions.D_pos p
    have hpositiveObservation :
        0 < (ActualInitializationPhysicalStep.observationOfGrid p
          (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation
            record.input i).2.1).val.val := by
      rw [ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation,
        ActualInitializationPhysicalStep.observationOfGrid_value]
      exact div_pos hpositiveGridReal hpositiveDen
    have hdecodedBankForCode :
        ReferenceDownCompletedAmbiguityMeasurability.decodedLoggedBank callCode
          (FollowerDownMeasurability.followerStateCode rate logged) =
        ⟨[],
          (FollowerDownMeasurability.decoderBatchOfCode
            (FollowerDownMeasurability.followerStateCode rate logged).downBatch).completed ++
          [(FollowerDownMeasurability.decoderBatchOfCode
            (FollowerDownMeasurability.followerStateCode rate logged).downBatch).pending ++
            [⟨(ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation
              record.input i).1, callCode.2.2.2.1⟩]]⟩ := by
      simpa [FollowerDownMeasurability.followerStateCode,
        FollowerDownMeasurability.decoderBatchCode,
        FollowerDownMeasurability.decoderEntryCode,
        FollowerDownMeasurability.decoderBatchOfCode,
        FollowerDownMeasurability.decoderEntryOfCode,
        ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation,
        ReferenceDownCompletedAmbiguityMeasurability.decodeCall,
        Function.comp_def, List.map_id, hcallTime] using hdecodedBank
    have hquotaForCode :
        (FollowerDownMeasurability.decoderBatchOfCode
          (FollowerDownMeasurability.followerStateCode rate logged).downBatch).pending.length + 1 =
          AffineBatchDecoder.quota p := by
      simpa [FollowerDownMeasurability.followerStateCode,
        FollowerDownMeasurability.decoderBatchCode,
        FollowerDownMeasurability.decoderEntryCode,
        FollowerDownMeasurability.decoderBatchOfCode,
        FollowerDownMeasurability.decoderEntryOfCode] using hquotaEq
    have hdiagnostics :=
      ReferenceGeneratedDownBatchBankBridge.roundDownObservation_diagnostics_eq_actual record i
    dsimp only [ReferenceGeneratedDownBatchCalendar.completedBatchAtRound]
    refine ⟨callCode, FollowerDownMeasurability.followerStateCode rate logged,
      ReferenceDownCompletedAmbiguityMeasurability.cutFields cut, hcallCode, ?_, ?_,
      hcallTime, hcomparison, hpositiveObservation, hquotaForCode, hdecodedBankForCode⟩
    · simp [hdiagnostics, hlogged]
    · simp [hdiagnostics, hcut]

end Bandits.Support.ReferenceGeneratedDownResetCompletionCensus

end
