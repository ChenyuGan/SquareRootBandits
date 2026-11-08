/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteInstallationEpisodeScoreSpan

import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.NormNum

/-!
# Retained episode weight envelopes on the actual complete suffix

This module turns the source's actual installation score spans into the
retained LIVE complement and COLLECTION register weight envelopes. It uses the
literal installation vectors and the original source history. It does not
identify the physical scores with a logical learner or prove sampler
feasibility.

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:96-188,219-243`
and `sources/zip4/manuscript/06_interruptions.tex:9-100,246-299,355-390`.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceCompletePhysicalHistory
open Bandits.Support.ReferenceCompleteLiveComplementScoreSpan
open Bandits.Support.ReferenceCompleteEpisodeAnchorOrigin
open Bandits.Support.ReferenceCompleteInstallationEpisodeScoreSpan
open Bandits.Support.ReferenceCompleteCollectionAssignedScoreSpan
open Bandits.Support.ReferenceCompleteCollectionIncrementSpan
open Bandits.Support.ReferenceAssignmentPayloadPersistence
open Bandits.Support.AssignmentScoreReconstruction
open Bandits.Support.CoordinatorLiveChoiceRecorderStep
open Bandits.Support.CoordinatorLiveServiceFinish
open Bandits.Support.CoordinatorCollectionLedger
open Bandits.Support.CoordinatorRoundDispatch
open Bandits.Support.CoordinatorAssignmentRegisterInstall
open Bandits.Support.ReferenceCoordinatorClockDomains
open Bandits.Support.ReferenceCorrectedInitializationLaunch
open Bandits.Support.ReferenceFirstLaunchNumericalCell
open Bandits.Support.ReferenceFirstWindowNumericalStream
open Bandits.Support.ReferenceRunClockPreservation
open Bandits.Support.ActualInitializationPhysicalStep
open Bandits.Support.FollowerCutoffScan
open Bandits.Support.ReplayWeightStability
open Bandits.Support.ScoreWeights
open Bandits.Support.ScoreWeightLogBounds

namespace Bandits.Support.ReferenceCompleteEpisodeScoreGrowth

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

private abbrev CompleteRecords (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) :=
  ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h

/-- A real element of the actual complete suffix is represented by its
calendar index. This is used for a retained live installation, whose public
producer records membership in the actual prefix rather than an index. -/
private theorem prior_record_index
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (k : Fin records.length)
    (birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hmem : birth ∈ records.take k.val) :
    ∃ b : Fin records.length, b.val < k.val ∧ records[b.val] = birth := by
  obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp hmem
  have hjk : j < k.val := by
    have hj' := hj
    simp only [List.length_take] at hj'
    omega
  have hjRecord : records[j] = birth := by
    simpa only [List.getElem_take] using hget
  exact ⟨⟨j, hjk.trans k.isLt⟩, hjk, hjRecord⟩

private theorem join_episode_intervals (start middle endpoint : ℕ)
    (hstart : start ≤ middle) (hmiddle : middle + 1 ≤ endpoint) :
    (middle - start) + (endpoint - (middle + 1)) = endpoint - (start + 1) := by
  omega

private theorem join_collection_intervals
    (origin installation cutoff endpoint : ℕ)
    (horigin : origin ≤ installation)
    (hcutoff : installation + 1 ≤ cutoff)
    (hendpoint : cutoff ≤ endpoint) :
    (installation - origin) + (cutoff - (installation + 1)) +
      (endpoint - cutoff) = endpoint - (origin + 1) := by
  omega

/-- The physical calendar makes a retained birth's timestamp an injective
index for this exact suffix list. -/
private theorem complete_record_time
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (CompleteRecords rate source rewards C_star C_h).length) :
    (CompleteRecords rate source rewards C_star C_h)[k.val].input.time.val =
      ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h + k.val := by
  have htimes := ReferenceCompletePhysicalHistory.completeSuffixRecords_time_values
    rate source rewards C_star C_h
  have hindex : k.val < ((CompleteRecords rate source rewards C_star C_h).map
      (fun record => record.input.time.val)).length := by
    simpa only [List.length_map] using k.isLt
  have hindex' : k.val < (ReferenceActivePhysicalHorizon.calendar
      (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
      (p.T - ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)).length := by
    rw [← htimes]
    exact hindex
  have h := congrArg
    (fun records : List ℕ => records[k.val]?) htimes
  rw [List.getElem?_map, List.getElem?_eq_getElem k.isLt,
    Option.map_some, List.getElem?_eq_getElem hindex'] at h
  have htime := Option.some.inj h
  simpa only [CompleteRecords, ReferenceActivePhysicalHorizon.calendar,
    List.getElem_range', Nat.one_mul] using htime

/-- The timestamp carried by an actual installation is its physical record
time, with both coordinates represented by the same `Fin T`. -/
private theorem installation_time
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (hbirth : ReferenceAssignmentPayloadPersistence.InstallationBirth record payload) :
    payload.sigma.val = record.input.time.val := by
  cases hcoord : record.output.preparation.coordinator with
  | first outcome =>
      cases outcome <;> simp only [ReferenceAssignmentPayloadPersistence.InstallationBirth,
        hcoord] at hbirth
      exact hbirth.2
  | live registers owned base outcome =>
      simp [ReferenceAssignmentPayloadPersistence.InstallationBirth, hcoord] at hbirth
  | collection old ledger clock cutoff outcome =>
      cases outcome <;> simp only [ReferenceAssignmentPayloadPersistence.InstallationBirth,
        hcoord] at hbirth
      exact hbirth.2
  | invalidCollectionCutoff =>
      simp [ReferenceAssignmentPayloadPersistence.InstallationBirth, hcoord] at hbirth
  | dagger =>
      simp [ReferenceAssignmentPayloadPersistence.InstallationBirth, hcoord] at hbirth

/-- Two births of the same actual payload cannot be distinct records: their
installed start times agree, and the original source calendar has one record
at each physical time. -/
private theorem same_birth_record
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hmem : birth ∈ CompleteRecords rate source rewards C_star C_h)
    (hbirth : ReferenceAssignmentPayloadPersistence.InstallationBirth birth payload)
    (b : Fin (CompleteRecords rate source rewards C_star C_h).length)
    (hb : ReferenceAssignmentPayloadPersistence.InstallationBirth
      (CompleteRecords rate source rewards C_star C_h)[b.val] payload) :
    birth = (CompleteRecords rate source rewards C_star C_h)[b.val] := by
  obtain ⟨j, hj, heq⟩ := List.mem_iff_getElem.mp hmem
  have htimeEq :
      (CompleteRecords rate source rewards C_star C_h)[j].input.time.val =
        (CompleteRecords rate source rewards C_star C_h)[b.val].input.time.val := by
    calc
      _ = birth.input.time.val := congrArg (fun record => record.input.time.val) heq
      _ = payload.sigma.val := (installation_time birth payload hbirth).symm
      _ = _ := installation_time _ payload hb
  have hjtime := complete_record_time rewards C_star C_h source ⟨j, hj⟩
  have hbtime := complete_record_time rewards C_star C_h source b
  have hindex : j = b.val := by
    rw [hjtime, hbtime] at htimeEq
    exact Nat.add_left_cancel htimeEq
  subst j
  exact heq.symm

/-- Clock provenance for each actual input record in the complete physical
suffix. This reuses the public source-run clock fold and the actual launch
construction; it assumes no clock or grid relation on the queried record. -/
private theorem complete_record_clockAt
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (CompleteRecords rate source rewards C_star C_h).length) :
    ReferenceCoordinatorClockDomains.clockAt source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source)
      (CompleteRecords rate source rewards C_star C_h)[k.val].input.time.val
      (CompleteRecords rate source rewards C_star C_h)[k.val].input.state := by
  classical
  cases hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h with
  | none =>
      have hk := k.isLt
      simp [ReferenceCompletePhysicalHistory.completeSuffixRecords,
        CompleteRecords, hlaunch] at hk
  | some active =>
      have hc :=
        (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
          rate source rewards C_star C_h).mp (by rw [hlaunch]; rfl)
      let initial := ReferenceFirstLaunchNumericalCell.launchState
        rate source rewards C_star C_h hc
      let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
        rate source rewards C_star C_h hc
      have hcanonical := ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
        rate source rewards C_star C_h hc
      have hactive : active =
          ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hc :=
        Option.some.inj (hlaunch.symm.trans hcanonical)
      subst active
      have hrecords := ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
        rate source rewards C_star C_h
        (ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hc)
        hlaunch
      let hspan : ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h +
          (p.T - ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h) ≤ p.T := by
        have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T rate source rewards C_star C_h
        omega
      let hmode := ReferenceCompletePhysicalHistory.activeMode_of_launch_eq_some
        rate source rewards C_star C_h
        (ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hc)
        hlaunch
      let run := ReferenceActivePhysicalHorizon.run initial source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
        (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
        (p.T - ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
        hspan hmode
      have hseed : ReferenceCoordinatorClockDomains.clockAt source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source)
          (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
          initial := by
        have hfirst : initial.coordinator = .first := seed.coordinatorFirst
        simp [ReferenceCoordinatorClockDomains.clockAt, initial, hfirst]
      have hruns := ReferenceRunClockPreservation.run_clockAt initial source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
        (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
        (p.T - ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
        hspan hmode hseed
      have hmem :
          (CompleteRecords rate source rewards C_star C_h)[k.val] ∈ run.records := by
        rw [← hrecords]
        exact List.getElem_mem k.isLt
      exact (hruns.2.2.2 _ hmem).1

/-- The clipped episode endpoint is at most one source grid length after its
one-based assignment start, including the terminal `T+1` clipping. -/
private theorem grid_span_le_episode_horizon
    (sigma : Fin p.T) :
    FollowerCutoffScan.gridBoundary p rate.eta.val sigma - (sigma.val + 1) ≤
      ReplayWeightStability.episodeHorizon rate.eta.val := by
  let H := ReplayWeightStability.episodeHorizon rate.eta.val
  let start := sigma.val + 1
  have hH : 0 < H := FollowerCutoffScan.episodeHorizon_pos_of_source_cap
    p rate.eta.val rate.eta.property rate.sourceCap
  have hrem : start % H < H := Nat.mod_lt _ hH
  have hdiv : start % H + H * (start / H) = start := Nat.mod_add_div _ _
  have hraw : H * (start / H + 1) = start + (H - start % H) := by
    rw [Nat.mul_add, Nat.mul_one]
    omega
  have hgrid := FollowerCutoffScan.gridBoundary_bounds p rate.eta.val
    rate.eta.property rate.sourceCap sigma
  have hgridDef : FollowerCutoffScan.gridBoundary p rate.eta.val sigma =
      min (p.T + 1) (H * (start / H + 1)) := by
    simp [FollowerCutoffScan.gridBoundary, ReplayWeightStability.episodeHorizon,
      H, start]
  have hgridLeRaw : FollowerCutoffScan.gridBoundary p rate.eta.val sigma ≤
      H * (start / H + 1) := by
    rw [hgridDef]
    exact Nat.min_le_right _ _
  rw [hgridDef]
  rw [hraw]
  omega

/-- Convert an actual integer score span of at most one episode into the
source's factor-two weight envelope. The logarithm and exact `eta * D = n`
scaling are the accepted reusable scalar results. -/
private theorem score_weight_envelope_of_growth
    (startScore finishScore elapsed : ℕ)
    (hmono : startScore ≤ finishScore)
    (hgrowth : finishScore ≤ startScore + (4 * rate.n) * elapsed)
    (helapsed : elapsed ≤ ReplayWeightStability.episodeHorizon rate.eta.val) :
    ScoreWeights.scoreWeight (AssignmentScoreReconstruction.sourceWeightBase p) startScore ≤
      ScoreWeights.scoreWeight (AssignmentScoreReconstruction.sourceWeightBase p) finishScore ∧
    ScoreWeights.scoreWeight (AssignmentScoreReconstruction.sourceWeightBase p) finishScore ≤
      2 * ScoreWeights.scoreWeight (AssignmentScoreReconstruction.sourceWeightBase p) startScore := by
  let Dval := ConstructorDimensions.D p
  let delta := finishScore - startScore
  have hD : 0 < Dval := ConstructorDimensions.D_pos p
  have hetaD : rate.eta.val * (Dval : ℝ) = (rate.n : ℝ) := rate.n_scale.symm
  have hdelta : delta ≤ 4 * rate.n * elapsed := by
    dsimp [delta]
    omega
  have hdeltaReal : (delta : ℝ) ≤ ((4 * rate.n * elapsed : ℕ) : ℝ) :=
    Nat.cast_le.mpr hdelta
  have hbaseLog := ScoreWeightLogBounds.source_base_log_pow_le
    (Nat.cast_pos.mpr hD) delta
  let records : List (Bool × ℕ) := List.replicate elapsed (false, 0)
  have hrecords : records.length = elapsed := by simp [records]
  have hscale := ReplayWeightStability.replay_source_scale_identity
    hD rate.eta.val hetaD records
  have htime := ReplayWeightStability.four_eta_mul_length_le_one_sixteenth
    rate.eta.property records (by simpa [hrecords] using helapsed)
  have hlog : Real.log ((1 + 1 / (Dval : ℝ)) ^ delta) ≤ (1 : ℝ) / 16 := by
    calc
      Real.log ((1 + 1 / (Dval : ℝ)) ^ delta) ≤ (delta : ℝ) / (Dval : ℝ) := by
        simpa only [div_eq_mul_inv] using hbaseLog
      _ ≤ ((4 * rate.n * elapsed : ℕ) : ℝ) / (Dval : ℝ) :=
        div_le_div_of_nonneg_right hdeltaReal (Nat.cast_pos.mpr hD).le
      _ = 4 * rate.eta.val * (elapsed : ℝ) := by
        simpa [hrecords] using hscale
      _ ≤ (1 : ℝ) / 16 := by
        simpa only [hrecords] using htime
  have hratio :
      ScoreWeights.scoreWeight (1 + 1 / (Dval : ℝ)) finishScore /
        ScoreWeights.scoreWeight (1 + 1 / (Dval : ℝ)) startScore =
      (1 + 1 / (Dval : ℝ)) ^ delta := by
    have hadd : startScore + delta = finishScore := Nat.add_sub_of_le hmono
    rw [← hadd]
    exact ScoreWeights.scoreWeight_update_ratio (ScoreWeights.sourceBase_pos
      (Nat.cast_pos.mpr hD)) startScore delta
  have hpos : 0 <
      ScoreWeights.scoreWeight (1 + 1 / (Dval : ℝ)) finishScore /
        ScoreWeights.scoreWeight (1 + 1 / (Dval : ℝ)) startScore :=
    div_pos (ScoreWeights.scoreWeight_pos
      (ScoreWeights.sourceBase_pos (Nat.cast_pos.mpr hD)) finishScore)
      (ScoreWeights.scoreWeight_pos
        (ScoreWeights.sourceBase_pos (Nat.cast_pos.mpr hD)) startScore)
  have hlogRatio : Real.log
      (ScoreWeights.scoreWeight (1 + 1 / (Dval : ℝ)) finishScore /
        ScoreWeights.scoreWeight (1 + 1 / (Dval : ℝ)) startScore) ≤ Real.log 2 := by
    rw [hratio]
    exact hlog.trans ReplayWeightStability.one_sixteenth_lt_log_two.le
  have hratioLe :
      ScoreWeights.scoreWeight (1 + 1 / (Dval : ℝ)) finishScore /
        ScoreWeights.scoreWeight (1 + 1 / (Dval : ℝ)) startScore ≤ 2 :=
    (Real.log_le_log_iff hpos (by norm_num)).mp hlogRatio
  have hupper := (div_le_iff₀ (ScoreWeights.scoreWeight_pos
    (ScoreWeights.sourceBase_pos (Nat.cast_pos.mpr hD)) startScore)).mp hratioLe
  have hmonoWeight := ScoreWeights.sourceWeight_mono
    (Nat.cast_pos.mpr hD) hmono
  constructor
  · simpa [Dval, AssignmentScoreReconstruction.sourceWeightBase] using hmonoWeight
  · simpa [Dval, AssignmentScoreReconstruction.sourceWeightBase] using hupper

private theorem actual_firstChosen_installation_eq
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (installed : CoordinatorAssignmentRegisterInstall.FirstInstallation
      (CoordinatorRoundDispatch.firstLaunchInput (firstInput record.input)))
    (selected : CoordinatorRoundDispatch.ArmSelection installed.registers.payload
      installed.startRoundResult installed.registers.time
      installed.registers.complementWeights record.input.row)
    (hbranch : record.output.preparation.coordinator = .first (.chosen installed selected)) :
    installed = CoordinatorAssignmentRegisterInstall.installFirst
      (CoordinatorRoundDispatch.firstLaunchInput (firstInput record.input)) := by
  have hactual : record.output.preparation.coordinator =
      ReferenceActivePhysicalStep.dispatch record.input := by
    rw [record.output_eq]
    rfl
  have hdispatch := hactual.symm.trans hbranch
  have hstate : record.input.state.coordinator = .first := by
    cases hs : record.input.state.coordinator with
    | first => rfl
    | live r q base =>
        simp only [ReferenceActivePhysicalStep.dispatch, hs] at hdispatch
        cases hround : CoordinatorRoundDispatch.dispatch
            (.live (liveInput record.input r q base));
          simp [hround] at hdispatch
        all_goals cases hdispatch
    | collection payload ledger saved =>
        by_cases hc : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
        · let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
          let clock := collectionClock payload ledger saved cutoff
          cases hround : CoordinatorRoundDispatch.dispatch
              (.collection (collectionInput record.input payload ledger clock cutoff));
            simp [ReferenceActivePhysicalStep.dispatch, hs, hc, cutoff, clock, hround]
              at hdispatch
          all_goals cases hdispatch
        · simp [ReferenceActivePhysicalStep.dispatch, hs, hc] at hdispatch
    | dagger => simp [ReferenceActivePhysicalStep.dispatch, hs] at hdispatch
  have hcut := ReferenceActivePhysicalStep.dispatch_first record.input hstate
  rw [hcut] at hdispatch
  have hchosen : CoordinatorRoundDispatch.dispatchFirst (firstInput record.input) =
      .chosen installed selected := by
    injection hdispatch with hchosen
  exact ReferenceActivePhysicalStep.dispatchFirst_chosen_installation
    record.input installed selected hchosen

/-- The source installation's retained follower base vector is the same set
of assigned coordinates as the full literal installation score vector. -/
private theorem installed_base_score_coordinates
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (base : Fin (p.m - 1) → ℕ) (z : Fin p.K → ℕ)
    (hbirth : ReferenceAssignmentPayloadPersistence.InstallationBirth record payload)
    (hbase : ReferenceAssignmentCollectionMassSteps.installedBaseScore record = some base)
    (hvector : ReferenceCompleteLiveComplementScoreSpan.installationScoreVector
      record payload z) :
    ∀ i, base i = z (payload.assignment.assigned i) := by
  cases hcoord : record.output.preparation.coordinator with
  | first outcome =>
      cases outcome with
      | chosen installed selected =>
          simp only [ReferenceAssignmentPayloadPersistence.InstallationBirth,
            hcoord] at hbirth
          rcases hbirth with ⟨hpayload, _⟩
          have hactual := actual_firstChosen_installation_eq record installed selected hcoord
          have hvec := hvector
          simp only [ReferenceCompleteLiveComplementScoreSpan.installationScoreVector,
            hcoord] at hvec
          rcases hvec with ⟨_, hz, _⟩
          have hbase' :
              installed.followerBaseScore = base := by
            have h := hbase
            simp only [ReferenceAssignmentCollectionMassSteps.installedBaseScore,
              hcoord] at h
            exact Option.some.inj h
          cases hactual
          intro i
          rw [hpayload, ← hbase', hz]
          exact CoordinatorAssignmentRegisterInstall.first_follower_base_score _ i
      | choiceDomainFailure installed => simp [ReferenceAssignmentPayloadPersistence.InstallationBirth, hcoord] at hbirth
      | recorderBoundaryFailure installed => simp [ReferenceAssignmentPayloadPersistence.InstallationBirth, hcoord] at hbirth
      | choiceRejected installed => simp [ReferenceAssignmentPayloadPersistence.InstallationBirth, hcoord] at hbirth
  | live registers owned retained outcome =>
      simp [ReferenceAssignmentPayloadPersistence.InstallationBirth, hcoord] at hbirth
  | collection old ledger clock cutoff outcome =>
      cases outcome with
      | laterChosen core consistent started hstart instruction hinstruction output
          hlocal clockData installed selected =>
          simp only [ReferenceAssignmentPayloadPersistence.InstallationBirth,
            hcoord] at hbirth
          rcases hbirth with ⟨hpayload, _⟩
          have hactual : record.output.preparation.coordinator =
              ReferenceActivePhysicalStep.dispatch record.input := by
            rw [record.output_eq]
            rfl
          have hp := ReferenceLaterInstallationProvenance.dispatch_laterChosen_provenance
            record.input
          rw [← hactual, hcoord] at hp
          obtain ⟨hinstalled, _⟩ := hp
          have hvec := hvector
          simp only [ReferenceCompleteLiveComplementScoreSpan.installationScoreVector,
            hcoord] at hvec
          rcases hvec with ⟨_, hz, _⟩
          have hbase' : installed.retainedBaseScore = base := by
            have h := hbase
            simp only [ReferenceAssignmentCollectionMassSteps.installedBaseScore,
              hcoord] at h
            exact Option.some.inj h
          cases hinstalled
          intro i
          rw [hpayload, ← hbase', hz]
          exact CoordinatorAssignmentRegisterInstall.later_retained_base_score_eq_source
            output clockData i
      | clockFailure _ _ => simp [ReferenceAssignmentPayloadPersistence.InstallationBirth, hcoord] at hbirth
      | localFailure _ _ _ _ => simp [ReferenceAssignmentPayloadPersistence.InstallationBirth, hcoord] at hbirth
      | coreFailure _ _ _ _ => simp [ReferenceAssignmentPayloadPersistence.InstallationBirth, hcoord] at hbirth
      | continuing _ _ _ _ => simp [ReferenceAssignmentPayloadPersistence.InstallationBirth, hcoord] at hbirth
      | laterReconstructionFailure _ _ _ _ _ _ _ _ => simp [ReferenceAssignmentPayloadPersistence.InstallationBirth, hcoord] at hbirth
      | laterPrefixFailure _ _ _ _ _ _ _ _ _ => simp [ReferenceAssignmentPayloadPersistence.InstallationBirth, hcoord] at hbirth
      | laterOrientationFailure _ _ _ _ _ _ _ => simp [ReferenceAssignmentPayloadPersistence.InstallationBirth, hcoord] at hbirth
      | laterChoiceFailure _ _ _ _ _ _ _ _ _ _ => simp [ReferenceAssignmentPayloadPersistence.InstallationBirth, hcoord] at hbirth
  | invalidCollectionCutoff =>
      simp [ReferenceAssignmentPayloadPersistence.InstallationBirth, hcoord] at hbirth
  | dagger =>
      simp [ReferenceAssignmentPayloadPersistence.InstallationBirth, hcoord] at hbirth

private theorem live_input_weight_envelope
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (CompleteRecords rate source rewards C_star C_h).length)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ)
    (hlive : (CompleteRecords rate source rewards C_star C_h)[k.val].input.state.coordinator =
      .live r q base) :
    r.complementEnvelopeValid := by
  classical
  let R := CompleteRecords rate source rewards C_star C_h
  let now := R[k.val].input.time.val
  have hnow : (CompleteRecords rate source rewards C_star C_h)[k.val].input.time.val = now := rfl
  have hliveSpan := ReferenceCompleteLiveComplementScoreSpan.complete_live_complement_score_span
    rate rewards C_star C_h source k r q base hlive
  dsimp only [CompleteRecords] at hliveSpan
  obtain ⟨birth, hmem, hbirth, zLive, hvectorLive, hbirthTime, hstartLe,
    hliveScores⟩ := hliveSpan
  obtain ⟨b, hbk, hbirthIndex⟩ := prior_record_index R k birth hmem
  have hbirthB : ReferenceAssignmentPayloadPersistence.InstallationBirth R[b.val] r.payload := by
    rw [hbirthIndex]
    exact hbirth
  have hroot := ReferenceCompleteInstallationEpisodeScoreSpan.actual_installation_episode_score_span
    rate rewards C_star C_h source b r.payload hbirthB
  dsimp only [CompleteRecords] at hroot
  obtain ⟨rho, P_rho, zSigma, zRho, hrhoLe, hrootBirth, hrootOrigin,
    hvectorSigma, hvectorRho, hrootTime, hrootBefore, hanchor, hpow, hgrid,
    hrootScores⟩ := hroot
  have hvectorLiveAtB :
      ReferenceCompleteLiveComplementScoreSpan.installationScoreVector
        R[b.val] r.payload zLive := by
    rw [hbirthIndex]
    exact hvectorLive
  have hjoin := ReferenceCompleteEpisodeAnchorOrigin.installationScoreVector_unique
    R[b.val] r.payload zSigma zLive hvectorSigma hvectorLiveAtB
  have hclock := complete_record_clockAt rewards C_star C_h source k
  simp only [ReferenceCoordinatorClockDomains.clockAt, hlive] at hclock
  obtain ⟨_, hvalid, hsigma, _, hgridLive, _, hbeforeGrid, _⟩ := hclock
  have hgridPayload : r.gridBoundary =
      FollowerCutoffScan.gridBoundary p rate.eta.val r.payload.sigma := by
    calc
      r.gridBoundary = r.priorClock.g := hgridLive
      _ = CoordinatorPhaseClock.boundaryFromSigma p rate.eta.val r.priorClock.sigma := hvalid.1
      _ = FollowerCutoffScan.gridBoundary p rate.eta.val r.payload.sigma := by
        rw [hsigma]
        simp [CoordinatorPhaseClock.boundaryFromSigma]
  have hendpoint :
      (now + 1) ≤
        FollowerCutoffScan.gridBoundary p rate.eta.val P_rho.sigma := by
    calc
      now + 1 ≤ r.gridBoundary := by
        exact Nat.succ_le_of_lt (by simpa only [R, CompleteRecords, now] using hbeforeGrid)
      _ = FollowerCutoffScan.gridBoundary p rate.eta.val P_rho.sigma :=
        hgridPayload.trans hgrid.symm
  have hstartLe' : r.payload.sigma.val ≤ now := by
    simpa only [R, CompleteRecords, now] using hstartLe
  have hspanInterval :
      (r.payload.sigma.val - P_rho.sigma.val) +
        (now + 1 - (r.payload.sigma.val + 1)) =
        now + 1 - (P_rho.sigma.val + 1) := by
    exact join_episode_intervals P_rho.sigma.val r.payload.sigma.val
      (now + 1) hrootBefore (Nat.succ_le_succ hstartLe')
  let elapsed := now + 1 - (P_rho.sigma.val + 1)
  have helapsed : elapsed ≤ ReplayWeightStability.episodeHorizon rate.eta.val := by
    dsimp [elapsed]
    calc
      now + 1 - (P_rho.sigma.val + 1) ≤
          FollowerCutoffScan.gridBoundary p rate.eta.val P_rho.sigma -
            (P_rho.sigma.val + 1) := Nat.sub_le_sub_right hendpoint _
      _ ≤ ReplayWeightStability.episodeHorizon rate.eta.val :=
        grid_span_le_episode_horizon P_rho.sigma
  have hanchorPower (a : Fin p.K) :
      r.payload.anchor a = AssignmentScoreReconstruction.sourceWeightBase p ^ zRho a := by
    calc
      r.payload.anchor a = P_rho.anchor a := congrArg (fun f => f a) hanchor
      _ = AssignmentScoreReconstruction.sourceWeightBase p ^ zRho a := hpow a
  change ∀ j : CanonicalFastSampling.FastArm r.payload.slowSet,
    r.payload.anchor j.1 ≤ r.complementWeights j ∧
      r.complementWeights j ≤ 2 * r.payload.anchor j.1
  intro j
  have hlower : zRho j.1 ≤ r.complementScores j := by
    have hspan := hrootScores j.1
    have hcurrent := hliveScores j
    have hcurrent' : zSigma j.1 ≤ r.complementScores j ∧
        r.complementScores j ≤ zSigma j.1 +
          (4 * rate.n) * (now + 1 - (r.payload.sigma.val + 1)) := by
      simpa only [hnow, ← hjoin] using hcurrent
    exact hspan.1.trans hcurrent'.1
  have hupper : r.complementScores j ≤ zRho j.1 + (4 * rate.n) * elapsed := by
    have hspan := hrootScores j.1
    have hcurrent := hliveScores j
    have hcurrent' : zSigma j.1 ≤ r.complementScores j ∧
        r.complementScores j ≤ zSigma j.1 +
          (4 * rate.n) * (now + 1 - (r.payload.sigma.val + 1)) := by
      simpa only [hnow, ← hjoin] using hcurrent
    calc
      r.complementScores j ≤ zSigma j.1 + (4 * rate.n) *
          (now + 1 - (r.payload.sigma.val + 1)) := hcurrent'.2
      _ ≤ (zRho j.1 + (4 * rate.n) *
          (r.payload.sigma.val - P_rho.sigma.val)) + (4 * rate.n) *
          (now + 1 - (r.payload.sigma.val + 1)) :=
        Nat.add_le_add_right hspan.2
          ((4 * rate.n) * (now + 1 - (r.payload.sigma.val + 1)))
      _ = zRho j.1 + (4 * rate.n) * elapsed := by
        calc
          _ = zRho j.1 + (4 * rate.n) *
              ((r.payload.sigma.val - P_rho.sigma.val) +
                (now + 1 - (r.payload.sigma.val + 1))) := by
            rw [Nat.add_assoc]
            rw [← Nat.mul_add]
          _ = zRho j.1 + (4 * rate.n) * elapsed := by
            dsimp only [elapsed]
            rw [hspanInterval]
  have hweights := score_weight_envelope_of_growth (zRho j.1)
    (r.complementScores j) elapsed hlower hupper helapsed
  change r.payload.anchor j.1 ≤
      ScoreWeights.scoreWeight (AssignmentScoreReconstruction.sourceWeightBase p)
        (r.complementScores j) ∧
    ScoreWeights.scoreWeight (AssignmentScoreReconstruction.sourceWeightBase p)
      (r.complementScores j) ≤ 2 * r.payload.anchor j.1
  rw [hanchorPower j.1]
  exact hweights

private theorem collection_input_weight_envelope
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (CompleteRecords rate source rewards C_star C_h).length)
    (P : ReferenceActivePhysicalStep.Payload rate)
    (l : ReferenceActivePhysicalStep.Ledger rate)
    (saved : Option (Fin p.T × Bool))
    (hinput : (CompleteRecords rate source rewards C_star C_h)[k.val].input.state.coordinator =
      .collection P l saved) :
    ∀ (a : Fin p.K) (cut : CoordinatorCollectionLedger.CutoffRegister)
      (current : CoordinatorCollectionLedger.CurrentRegister),
      l.cutoffRegisters a = some cut → l.currentRegisters a = some current →
      P.anchor a ≤ AssignmentScoreReconstruction.sourceWeightBase p ^
          (cut.score + l.increment a) ∧
        AssignmentScoreReconstruction.sourceWeightBase p ^ (cut.score + l.increment a) ≤
          2 * P.anchor a := by
  classical
  let R := CompleteRecords rate source rewards C_star C_h
  have hcomplement :=
    ReferenceCompleteInstallationEpisodeScoreSpan.complete_collection_input_complement_cutoff_span
      rate rewards C_star C_h source k P l saved hinput
  dsimp only [CompleteRecords] at hcomplement
  obtain ⟨birth, hbirthMem, hbirth, zCut, hvectorCut, hcutSpan⟩ := hcomplement
  have hassigned :=
    ReferenceCompleteCollectionAssignedScoreSpan.complete_collection_input_assigned_score_span
      rate rewards C_star C_h source k P l saved hinput
  dsimp only [CompleteRecords] at hassigned
  obtain ⟨b, hbk, hbirthAssigned, hbaseInstalled, hassignment, hsigma, hcutoff,
    hfreeze, hcutoffPositive, hcutoffFreeze, hterminal, hcutoffCursor, hcursor,
    hincrement, hassignedSpan⟩ := hassigned
  have hsameBirth := same_birth_record rewards C_star C_h source P birth
    hbirthMem hbirth b hbirthAssigned
  have hvectorCutAtB :
      ReferenceCompleteLiveComplementScoreSpan.installationScoreVector
        R[b.val] P zCut := by
    have hsameBirth' : birth = R[b.val] := by
      simpa only [R, CompleteRecords] using hsameBirth
    rw [← hsameBirth']
    exact hvectorCut
  have hroot := ReferenceCompleteInstallationEpisodeScoreSpan.actual_installation_episode_score_span
    rate rewards C_star C_h source b P hbirthAssigned
  dsimp only [CompleteRecords] at hroot
  obtain ⟨rho, P_rho, zInstalled, zRho, hrhoLe, hrootBirth, hrootOrigin,
    hvectorInstalled, hvectorRho, hrootTime, hrootBefore, hanchor, hpow, hgrid,
    hrootScores⟩ := hroot
  have hjoin := ReferenceCompleteEpisodeAnchorOrigin.installationScoreVector_unique
    R[b.val] P zInstalled zCut hvectorInstalled hvectorCutAtB
  have hbaseCoordinates := installed_base_score_coordinates R[b.val] P l.baseScore
    zCut hbirthAssigned hbaseInstalled hvectorCutAtB
  have hfreezeOrigin : l.freezeAt =
      FollowerCutoffScan.gridBoundary p rate.eta.val P_rho.sigma := by
    calc
      l.freezeAt = FollowerCutoffScan.gridBoundary p rate.eta.val P.sigma := hfreeze
      _ = FollowerCutoffScan.gridBoundary p rate.eta.val P_rho.sigma := hgrid.symm
  have hfirst := FollowerCutoffScan.firstCutoff_bounds p rate.eta.val
    rate.eta.property rate.sourceCap P.sigma
    (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
      (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)))
  have hsigmaCut : P.sigma.val + 1 ≤ l.cutoff := by
    rw [hcutoff]
    exact le_of_lt hfirst.1
  have hcutMin : l.cutoff ≤ min l.cursor l.freezeAt :=
    Nat.le_min.mpr ⟨hcutoffCursor, hcutoffFreeze⟩
  have hinterval :
      (P.sigma.val - P_rho.sigma.val) +
        (l.cutoff - (P.sigma.val + 1)) +
        (min l.cursor l.freezeAt - l.cutoff) =
        min l.cursor l.freezeAt - (P_rho.sigma.val + 1) := by
    exact join_collection_intervals P_rho.sigma.val P.sigma.val l.cutoff
      (min l.cursor l.freezeAt) hrootBefore hsigmaCut hcutMin
  let elapsed := min l.cursor l.freezeAt - (P_rho.sigma.val + 1)
  have hminFreeze : min l.cursor l.freezeAt ≤
      FollowerCutoffScan.gridBoundary p rate.eta.val P_rho.sigma := by
    rw [← hfreezeOrigin]
    exact Nat.min_le_right _ _
  have helapsed : elapsed ≤ ReplayWeightStability.episodeHorizon rate.eta.val := by
    dsimp [elapsed]
    calc
      min l.cursor l.freezeAt - (P_rho.sigma.val + 1) ≤
          FollowerCutoffScan.gridBoundary p rate.eta.val P_rho.sigma -
            (P_rho.sigma.val + 1) := by
        exact Nat.sub_le_sub_right hminFreeze (P_rho.sigma.val + 1)
      _ ≤ ReplayWeightStability.episodeHorizon rate.eta.val :=
        grid_span_le_episode_horizon P_rho.sigma
  intro a cut current hcut hcurrent
  have hanchorPower :
      P.anchor a = AssignmentScoreReconstruction.sourceWeightBase p ^ zRho a := by
    calc
      P.anchor a = P_rho.anchor a := congrArg (fun f => f a) hanchor
      _ = AssignmentScoreReconstruction.sourceWeightBase p ^ zRho a := hpow a
  by_cases ha : a ∈ P.slowSet.1
  · have haImage : a ∈ Finset.univ.image P.assignment.assigned := by
      rw [P.assignment_image]
      exact ha
    obtain ⟨i, _hi, hassignedArm⟩ := Finset.mem_image.mp haImage
    have hledgerArm : l.assignment.arm i = a := by
      rw [hassignment, hassignedArm]
    have hcutArm : l.cutoffRegisters (l.assignment.arm i) = some cut := by
      rw [hledgerArm]
      exact hcut
    have hcurrentArm : l.currentRegisters (l.assignment.arm i) = some current := by
      rw [hledgerArm]
      exact hcurrent
    obtain ⟨hbaseCut, _hcutUpper, _hlastScore, _hlastCap, hcombined⟩ :=
      hassignedSpan i cut current hcutArm hcurrentArm
    have hbaseInstalledEq : l.baseScore i = zInstalled a := by
      calc
        l.baseScore i = zCut (P.assignment.assigned i) := hbaseCoordinates i
        _ = zCut a := by rw [hassignedArm]
        _ = zInstalled a := by rw [hjoin]
    have hmono : zRho a ≤ cut.score + l.increment a := by
      calc
        zRho a ≤ zInstalled a := (hrootScores a).1
        _ = l.baseScore i := hbaseInstalledEq.symm
        _ ≤ cut.score := hbaseCut
        _ ≤ cut.score + l.increment a := Nat.le_add_right _ _
    have hinstallInterval :
        (P.sigma.val - P_rho.sigma.val) +
          (min l.cursor l.freezeAt - (P.sigma.val + 1)) = elapsed := by
      change (P.sigma.val - P_rho.sigma.val) +
        (min l.cursor l.freezeAt - (P.sigma.val + 1)) =
          min l.cursor l.freezeAt - (P_rho.sigma.val + 1)
      exact join_episode_intervals P_rho.sigma.val P.sigma.val
        (min l.cursor l.freezeAt) hrootBefore (Nat.le_trans hsigmaCut hcutMin)
    have hupper : cut.score + l.increment a ≤ zRho a + (4 * rate.n) * elapsed := by
      have hcombined' : cut.score + l.increment a ≤
          zInstalled a + (4 * rate.n) *
            (min l.cursor l.freezeAt - (P.sigma.val + 1)) := by
        simpa [hledgerArm, hsigma, hbaseInstalledEq] using hcombined
      calc
        cut.score + l.increment a ≤ zInstalled a + (4 * rate.n) *
            (min l.cursor l.freezeAt - (P.sigma.val + 1)) := hcombined'
        _ ≤ (zRho a + (4 * rate.n) * (P.sigma.val - P_rho.sigma.val)) +
            (4 * rate.n) * (min l.cursor l.freezeAt - (P.sigma.val + 1)) :=
          Nat.add_le_add_right (hrootScores a).2
            ((4 * rate.n) * (min l.cursor l.freezeAt - (P.sigma.val + 1)))
        _ = zRho a + (4 * rate.n) *
            ((P.sigma.val - P_rho.sigma.val) +
              (min l.cursor l.freezeAt - (P.sigma.val + 1))) := by
          rw [Nat.add_assoc]
          rw [← Nat.mul_add]
        _ = zRho a + (4 * rate.n) * elapsed := by rw [hinstallInterval]
    have hweights := score_weight_envelope_of_growth (zRho a)
      (cut.score + l.increment a) elapsed hmono hupper helapsed
    change P.anchor a ≤
        ScoreWeights.scoreWeight (AssignmentScoreReconstruction.sourceWeightBase p)
          (cut.score + l.increment a) ∧
      ScoreWeights.scoreWeight (AssignmentScoreReconstruction.sourceWeightBase p)
        (cut.score + l.increment a) ≤ 2 * P.anchor a
    rw [hanchorPower]
    exact hweights
  · let j : CanonicalFastSampling.FastArm P.slowSet := ⟨a, by
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
      exact ha⟩
    obtain ⟨cutStored, currentStored, hcutStored, _hcurrentStored, hcutLower,
      hcutUpper⟩ := hcutSpan j
    have hcutEq : cutStored = cut := Option.some.inj (hcutStored.symm.trans hcut)
    subst cutStored
    have hinc := hincrement a cut current hcut hcurrent
    have hcutRoot : zCut a ≤ zRho a + (4 * rate.n) *
        (P.sigma.val - P_rho.sigma.val) := by
      rw [← hjoin]
      exact (hrootScores a).2
    have hmono : zRho a ≤ cut.score + l.increment a := by
      calc
        zRho a ≤ zInstalled a := (hrootScores a).1
        _ = zCut a := by rw [hjoin]
        _ ≤ cut.score := hcutLower
        _ ≤ cut.score + l.increment a := Nat.le_add_right _ _
    have hupper : cut.score + l.increment a ≤ zRho a + (4 * rate.n) * elapsed := by
      have hcombinedCut : cut.score + l.increment a ≤ zCut a + (4 * rate.n) *
          ((l.cutoff - (P.sigma.val + 1)) +
            (min l.cursor l.freezeAt - l.cutoff)) := by
        calc
          cut.score + l.increment a ≤
              (zCut a + (4 * rate.n) * (l.cutoff - (P.sigma.val + 1))) +
                (4 * rate.n) * (min l.cursor l.freezeAt - l.cutoff) :=
            Nat.add_le_add hcutUpper hinc
          _ = zCut a + ((4 * rate.n) * (l.cutoff - (P.sigma.val + 1)) +
              (4 * rate.n) * (min l.cursor l.freezeAt - l.cutoff)) := by
            rw [Nat.add_assoc]
          _ = zCut a + (4 * rate.n) *
              ((l.cutoff - (P.sigma.val + 1)) +
                (min l.cursor l.freezeAt - l.cutoff)) := by
            rw [← Nat.mul_add]
      calc
        cut.score + l.increment a ≤ zCut a + (4 * rate.n) *
            ((l.cutoff - (P.sigma.val + 1)) +
              (min l.cursor l.freezeAt - l.cutoff)) := hcombinedCut
        _ ≤ (zRho a + (4 * rate.n) * (P.sigma.val - P_rho.sigma.val)) +
            (4 * rate.n) *
              ((l.cutoff - (P.sigma.val + 1)) +
                (min l.cursor l.freezeAt - l.cutoff)) :=
          Nat.add_le_add_right hcutRoot
            ((4 * rate.n) *
              ((l.cutoff - (P.sigma.val + 1)) +
                (min l.cursor l.freezeAt - l.cutoff)))
        _ = zRho a + ((4 * rate.n) * (P.sigma.val - P_rho.sigma.val) +
            (4 * rate.n) *
              ((l.cutoff - (P.sigma.val + 1)) +
                (min l.cursor l.freezeAt - l.cutoff))) := by
          rw [Nat.add_assoc]
        _ = zRho a + (4 * rate.n) *
            ((P.sigma.val - P_rho.sigma.val) +
              ((l.cutoff - (P.sigma.val + 1)) +
                (min l.cursor l.freezeAt - l.cutoff))) := by
          rw [← Nat.mul_add]
        _ = zRho a + (4 * rate.n) * elapsed := by
          dsimp only [elapsed]
          rw [← Nat.add_assoc, hinterval]
    have hweights := score_weight_envelope_of_growth (zRho a)
      (cut.score + l.increment a) elapsed hmono hupper helapsed
    change P.anchor a ≤
        ScoreWeights.scoreWeight (AssignmentScoreReconstruction.sourceWeightBase p)
          (cut.score + l.increment a) ∧
      ScoreWeights.scoreWeight (AssignmentScoreReconstruction.sourceWeightBase p)
        (cut.score + l.increment a) ≤ 2 * P.anchor a
    rw [hanchorPower]
    exact hweights

/-- Every retained actual suffix record has the source factor-two envelope on
its literal live complement coordinates and every queried present collection
register. The common telescope is the original source, whole rewards and
unrestricted construction constants; only an actual suffix index is queried.
-/
theorem complete_retained_episode_weight_envelopes
    (p : ConstructorDimensions.Parameters)
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length) :
    match (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val].input.state.coordinator with
    | .live r _q _base => r.complementEnvelopeValid
    | .collection P l _ =>
        ∀ (a : Fin p.K) (cut : CoordinatorCollectionLedger.CutoffRegister)
          (current : CoordinatorCollectionLedger.CurrentRegister),
          l.cutoffRegisters a = some cut → l.currentRegisters a = some current →
          P.anchor a ≤ AssignmentScoreReconstruction.sourceWeightBase p ^
              (cut.score + l.increment a) ∧
            AssignmentScoreReconstruction.sourceWeightBase p ^
                (cut.score + l.increment a) ≤ 2 * P.anchor a
    | .first | .dagger => True := by
  classical
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
  cases hstate : R[k.val].input.state.coordinator with
  | first => trivial
  | dagger => trivial
  | live r _q _base =>
      exact live_input_weight_envelope (rate := rate) rewards C_star C_h source k r _q _base hstate
  | collection P l saved =>
      exact collection_input_weight_envelope (rate := rate) rewards C_star C_h source k
        P l saved hstate

end Bandits.Support.ReferenceCompleteEpisodeScoreGrowth

end

end
