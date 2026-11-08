/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteLiveComplementScoreSpan

/-!
# Episode anchor origins in the complete physical suffix

This module follows the installed anchor through actual corrected assignment
starts. It records the full installation score vector and the episode grid
boundary; it makes no score-growth or physical-calendar-score claim.

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:96-188,219-243`
and `sources/zip4/manuscript/06_interruptions.tex:9-100,246-299,355-390`.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceAssignmentPayloadPersistence
open Bandits.Support.ReferenceCompletePhysicalHistory
open Bandits.Support.ReferenceCompleteLiveComplementScoreSpan
open Bandits.Support.AssignmentScoreReconstruction
open Bandits.Support.CoordinatorAssignmentRegisterInstall
open Bandits.Support.CoordinatorRoundDispatch
open Bandits.Support.FollowerCutoffScan

namespace Bandits.Support.ReferenceCompleteEpisodeAnchorOrigin

variable {p : ConstructorDimensions.Parameters}

/-- Before the clipped endpoint of a positive source grid block, every later
start remains in that same block. The `min (T+1)` clipping is kept in the
literal grid definition. -/
theorem gridBoundary_eq_of_before
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (s t : Fin p.T) (hst : s.val ≤ t.val)
    (hbefore : t.val + 1 <
      FollowerCutoffScan.gridBoundary p rate.eta.val s) :
    FollowerCutoffScan.gridBoundary p rate.eta.val t =
      FollowerCutoffScan.gridBoundary p rate.eta.val s := by
  let H := ReplayWeightStability.episodeHorizon rate.eta.val
  have hH : 0 < H :=
    FollowerCutoffScan.episodeHorizon_pos_of_source_cap p rate.eta.val
      rate.eta.property rate.sourceCap
  let q := (s.val + 1) / H
  have hraw : t.val + 1 < H * (q + 1) := by
    have h := hbefore
    simp only [FollowerCutoffScan.gridBoundary] at h
    change t.val + 1 < min (p.T + 1) (H * (q + 1)) at h
    exact h.trans_le (Nat.min_le_right _ _)
  have hqlo : q * H ≤ t.val + 1 := by
    have hqbound : q * H ≤ s.val + 1 := by
      dsimp [q]
      exact Nat.div_mul_le_self _ _
    omega
  have hqle : q ≤ (t.val + 1) / H :=
    (Nat.le_div_iff_mul_le hH).2 hqlo
  have hqhi : (t.val + 1) / H < q + 1 := by
    apply (Nat.div_lt_iff_lt_mul hH).2
    simpa only [Nat.mul_comm] using hraw
  have hdiv : (t.val + 1) / H = q := by omega
  simp only [FollowerCutoffScan.gridBoundary, H, q, hdiv]

/-- The literal installation readout determines the same whole `Fin K` score
vector whenever the record and payload are fixed. -/
theorem installationScoreVector_unique
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (z z' : Fin p.K → ℕ)
    (hz : installationScoreVector record payload z)
    (hz' : installationScoreVector record payload z') :
    z = z' := by
  cases hcoord : record.output.preparation.coordinator with
  | first outcome =>
      cases outcome <;> simp_all [installationScoreVector]
  | live registers owned base outcome =>
      simp_all [installationScoreVector]
  | collection old ledger clock cutoff outcome =>
      cases outcome <;> simp_all [installationScoreVector]
  | invalidCollectionCutoff => simp_all [installationScoreVector]
  | dagger => simp_all [installationScoreVector]

private theorem complete_record_clockAt
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length) :
    ReferenceCoordinatorClockDomains.clockAt
        source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
        (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h)[k.val].input.time.val
        (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h)[k.val].input.state ∧
      ReferenceCoordinatorClockDomains.clockAt
        source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
        ((ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h)[k.val].input.time.val + 1)
        (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h)[k.val].output.next := by
  classical
  cases hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h with
  | none =>
      have hk := k.isLt
      simp [ReferenceCompletePhysicalHistory.completeSuffixRecords, hlaunch] at hk
  | some active =>
      have hc :=
        (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
          rate source rewards C_star C_h).mp (by rw [hlaunch]; rfl)
      let initial := ReferenceFirstLaunchNumericalCell.launchState
        rate source rewards C_star C_h hc
      let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
        rate source rewards C_star C_h hc
      have hcanonical :=
        ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
          rate source rewards C_star C_h hc
      have hactive : active =
          ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hc :=
        Option.some.inj (hlaunch.symm.trans hcanonical)
      subst active
      have hrecords := ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
        rate source rewards C_star C_h
        (ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hc)
        hlaunch
      let run := ReferenceActivePhysicalHorizon.run initial source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
        (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
        (p.T - ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
        (by have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T
              rate source rewards C_star C_h; omega)
        (ReferenceCompletePhysicalHistory.activeMode_of_launch_eq_some
          rate source rewards C_star C_h
          (ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hc)
          hlaunch)
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
        (by have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T
              rate source rewards C_star C_h; omega)
        (ReferenceCompletePhysicalHistory.activeMode_of_launch_eq_some
          rate source rewards C_star C_h
          (ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hc)
          hlaunch) hseed
      have hmem :
          (ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate source rewards C_star C_h)[k.val] ∈ run.records := by
        rw [← hrecords]
        exact List.getElem_mem k.isLt
      have hrecord := hruns.2.2.2
        (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h)[k.val] hmem
      exact ⟨hrecord.1, hrecord.2.1⟩

private abbrev CompleteRecords (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p) :=
  ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h

/-- A round is an episode anchor origin exactly at a chosen first install or
a chosen renewal install. Corrected installs preserve their earlier origin. -/
def IsEpisodeAnchorBirth {rate : ReferenceActivePhysicalStep.RateInput p}
    (record : ReferenceActivePhysicalHorizon.RoundRecord
    (p := p) (rate := rate)) : Prop :=
  match record.output.preparation.coordinator with
  | .first (.chosen _ _) => True
  | .collection _ _ _ _ (.laterChosen _ _ _ _ instruction _ _ _ _ _ _) =>
      instruction.kind = .renewal
  | _ => False

private theorem actual_firstChosen_installation_eq
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (installed : CoordinatorAssignmentRegisterInstall.FirstInstallation
      (CoordinatorRoundDispatch.firstLaunchInput
        (ReferenceActivePhysicalStep.firstInput record.input)))
    (selected : CoordinatorRoundDispatch.ArmSelection installed.registers.payload
      installed.startRoundResult installed.registers.time
      installed.registers.complementWeights record.input.row)
    (hbranch : record.output.preparation.coordinator = .first (.chosen installed selected)) :
    installed = CoordinatorAssignmentRegisterInstall.installFirst
      (CoordinatorRoundDispatch.firstLaunchInput
        (ReferenceActivePhysicalStep.firstInput record.input)) := by
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
            (.live (ReferenceActivePhysicalStep.liveInput record.input r q base));
          simp [hround] at hdispatch
        all_goals cases hdispatch
    | collection payload ledger saved =>
        by_cases hc : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
        · let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
          let clock := ReferenceActivePhysicalStep.collectionClock payload ledger saved cutoff
          cases hround : CoordinatorRoundDispatch.dispatch
              (.collection (ReferenceActivePhysicalStep.collectionInput
                record.input payload ledger clock cutoff));
            simp [ReferenceActivePhysicalStep.dispatch, hs, hc, cutoff, clock, hround]
              at hdispatch
          all_goals cases hdispatch
        · simp [ReferenceActivePhysicalStep.dispatch, hs, hc] at hdispatch
    | dagger =>
        simp [ReferenceActivePhysicalStep.dispatch, hs] at hdispatch
  have hcut := ReferenceActivePhysicalStep.dispatch_first record.input hstate
  rw [hcut] at hdispatch
  have hchosen : CoordinatorRoundDispatch.dispatchFirst
      (ReferenceActivePhysicalStep.firstInput record.input) = .chosen installed selected := by
    injection hdispatch with hchosen
  exact ReferenceActivePhysicalStep.dispatchFirst_chosen_installation
    record.input installed selected hchosen

private theorem laterChosen_input_payload_is_collection
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (clock : CoordinatorPhaseClock.ClockRegisters p) (cutoff : Fin p.T)
    (outcome : CoordinatorRoundDispatch.CollectionOutcome
      (ReferenceActivePhysicalStep.collectionInput record.input payload ledger clock cutoff))
    (hbranch : record.output.preparation.coordinator =
      .collection payload ledger clock cutoff outcome) :
    ∃ oldLedger saved,
      record.input.state.coordinator = .collection payload oldLedger saved := by
  have hactual : record.output.preparation.coordinator =
      ReferenceActivePhysicalStep.dispatch record.input := by
    rw [record.output_eq]
    rfl
  have hdispatch := hactual.symm.trans hbranch
  cases hstate : record.input.state.coordinator with
  | first =>
      simp [ReferenceActivePhysicalStep.dispatch, hstate] at hdispatch
      cases hdispatch
  | live r q base =>
      simp only [ReferenceActivePhysicalStep.dispatch, hstate] at hdispatch
      cases hround : CoordinatorRoundDispatch.dispatch
          (.live (ReferenceActivePhysicalStep.liveInput record.input r q base));
        simp [hround] at hdispatch
      all_goals cases hdispatch
  | collection old oldLedger saved =>
      by_cases hvalid : 1 ≤ oldLedger.cutoff ∧ oldLedger.cutoff ≤ p.T
      · let oldCutoff : Fin p.T := ⟨oldLedger.cutoff - 1, by omega⟩
        let oldClock := ReferenceActivePhysicalStep.collectionClock old oldLedger saved oldCutoff
        cases hround : CoordinatorRoundDispatch.dispatch
            (.collection (ReferenceActivePhysicalStep.collectionInput
              record.input old oldLedger oldClock oldCutoff));
          simp [ReferenceActivePhysicalStep.dispatch, hstate, hvalid,
            oldCutoff, oldClock, hround] at hdispatch
        all_goals
          cases hdispatch
          exact ⟨ledger, saved, rfl⟩
      · simp [ReferenceActivePhysicalStep.dispatch, hstate, hvalid] at hdispatch
  | dagger =>
      simp [ReferenceActivePhysicalStep.dispatch, hstate] at hdispatch

private theorem episode_origin_of_installation
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p) :
    ∀ n (hn : n < (CompleteRecords rate rewards C_star C_h source).length)
      (payload : ReferenceActivePhysicalStep.Payload rate),
      InstallationBirth ((CompleteRecords rate rewards C_star C_h source)[n]'hn) payload →
      ∃ rho : Fin (CompleteRecords rate rewards C_star C_h source).length,
        ∃ P_rho : ReferenceActivePhysicalStep.Payload rate,
          ∃ z_rho : Fin p.K → ℕ,
            rho.val ≤ n ∧
            InstallationBirth
              ((CompleteRecords rate rewards C_star C_h source)[rho.val]'rho.isLt) P_rho ∧
            installationScoreVector
              ((CompleteRecords rate rewards C_star C_h source)[rho.val]'rho.isLt)
              P_rho z_rho ∧
            IsEpisodeAnchorBirth
              ((CompleteRecords rate rewards C_star C_h source)[rho.val]'rho.isLt) ∧
            ((CompleteRecords rate rewards C_star C_h source)[rho.val]'rho.isLt).input.time =
              P_rho.sigma ∧
            P_rho.sigma.val ≤ payload.sigma.val ∧
            payload.anchor = P_rho.anchor ∧
            (∀ a, P_rho.anchor a =
              AssignmentScoreReconstruction.sourceWeightBase p ^ z_rho a) ∧
            FollowerCutoffScan.gridBoundary p rate.eta.val P_rho.sigma =
              FollowerCutoffScan.gridBoundary p rate.eta.val payload.sigma := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hn payload hbirth
      let R := CompleteRecords rate rewards C_star C_h source
      let record := R[n]'hn
      change InstallationBirth record payload at hbirth
      cases hcoord : record.output.preparation.coordinator with
      | first outcome =>
          cases outcome with
          | chosen installed selected =>
              simp only [InstallationBirth, hcoord] at hbirth
              rcases hbirth with ⟨rfl, _⟩
              have hsource := ReferenceCompleteLiveComplementScoreSpan.first_installation_source
                record installed selected hcoord
              have hinstalled := actual_firstChosen_installation_eq
                rate record installed selected hcoord
              refine ⟨⟨n, hn⟩, installed.registers.payload, (fun _ => 0), ?_⟩
              refine ⟨le_rfl, hsource.1, hsource.2.1, ?_, ?_, le_rfl, rfl, ?_, rfl⟩
              · simp [IsEpisodeAnchorBirth, record, R, hcoord]
              · apply Fin.ext
                exact hsource.2.2.symm
              · intro a
                have hone := CoordinatorAssignmentRegisterInstall.first_payload_anchor_one
                  (CoordinatorRoundDispatch.firstLaunchInput
                    (ReferenceActivePhysicalStep.firstInput record.input)) a
                rw [← hinstalled] at hone
                calc
                  installed.registers.payload.anchor a = 1 := hone
                  _ = AssignmentScoreReconstruction.sourceWeightBase p ^ (fun _ => 0) a := by simp
          | choiceDomainFailure installation => simp [InstallationBirth, hcoord] at hbirth
          | recorderBoundaryFailure installation => simp [InstallationBirth, hcoord] at hbirth
          | choiceRejected installation => simp [InstallationBirth, hcoord] at hbirth
      | live registers owned base => simp [InstallationBirth, hcoord] at hbirth
      | invalidCollectionCutoff => simp [InstallationBirth, hcoord] at hbirth
      | dagger => simp [InstallationBirth, hcoord] at hbirth
      | collection old ledger clock cutoff outcome =>
          cases outcome with
          | laterChosen core consistent started hstart instruction hinstruction output hlocal
              clockData installed selected =>
              simp only [InstallationBirth, hcoord] at hbirth
              rcases hbirth with ⟨rfl, _⟩
              have hsource := ReferenceCompleteLiveComplementScoreSpan.later_installation_source
                record old ledger clock cutoff core consistent started hstart instruction
                hinstruction output hlocal clockData installed selected hcoord
              have hactual : record.output.preparation.coordinator =
                  ReferenceActivePhysicalStep.dispatch record.input := by
                rw [record.output_eq]
                rfl
              have hprovenance :=
                ReferenceLaterInstallationProvenance.dispatch_laterChosen_provenance
                  record.input
              rw [← hactual, hcoord] at hprovenance
              rcases hprovenance with ⟨hinstalled, _, _, _⟩
              rcases CoordinatorAssignmentRegisterInstall.later_start_round_compatibility
                  output clockData with
                ⟨_, _, _, _, _, _, _, _, hkindExpected⟩
              cases hkind : instruction.kind with
              | renewal =>
                  have hanchor := CoordinatorAssignmentRegisterInstall.later_payload_anchor_renewal
                    output clockData hkind
                  have hinstalledAnchor : installed.registers.payload.anchor =
                      AssignmentScoreReconstruction.currentWeight output.reconstruction := by
                    rw [hinstalled]
                    exact hanchor
                  refine ⟨⟨n, hn⟩, installed.registers.payload,
                    (fun a => AssignmentScoreReconstruction.sourceScore output.reconstruction a),
                    ?_⟩
                  refine ⟨le_rfl, hsource.1, hsource.2.1, ?_, ?_, le_rfl, rfl, ?_, rfl⟩
                  · simp [IsEpisodeAnchorBirth, record, R, hcoord, hkind]
                  · apply Fin.ext
                    exact hsource.2.2.symm
                  · intro a
                    calc
                      installed.registers.payload.anchor a =
                          AssignmentScoreReconstruction.currentWeight output.reconstruction a :=
                        congrArg (fun f => f a) hinstalledAnchor
                      _ = AssignmentScoreReconstruction.sourceWeightBase p ^
                          AssignmentScoreReconstruction.sourceScore output.reconstruction a := rfl
              | corrected =>
                  have hstateData := laterChosen_input_payload_is_collection
                    rate record old ledger clock cutoff
                    (.laterChosen core consistent started hstart instruction hinstruction output
                      hlocal clockData installed selected) hcoord
                  rcases hstateData with ⟨oldLedger, saved, hstate⟩
                  have hclock := complete_record_clockAt rate rewards C_star C_h source
                    ⟨n, hn⟩
                  have hcollectionClock := hclock.1
                  change ReferenceCoordinatorClockDomains.clockAt source.1.2
                    (ActualInitializationPhysicalStep.selectedRowIndex p source)
                    record.input.time.val record.input.state at hcollectionClock
                  simp only [ReferenceCoordinatorClockDomains.clockAt, hstate]
                    at hcollectionClock
                  rcases hcollectionClock with
                    ⟨_, holdBeforeCutoff, _, _, hcutoffBeforeCurrent, _, _, _⟩
                  have hretained :=
                    ReferenceAssignmentRetainedBirthProvenance.complete_coordinator_retained_birth
                      rate rewards C_star C_h source ⟨n, hn⟩
                  simp only [record, R, hstate] at hretained
                  rcases hretained with
                    ⟨⟨prior, hpriorLt, hpriorBirth, _⟩, _, _, _⟩
                  have hpriorOrigin := ih prior.val hpriorLt prior.isLt old hpriorBirth
                  rcases hpriorOrigin with
                    ⟨rho, P_rho, z_rho, hrhoLe, hrootBirth, hrootVector, hrootBranch,
                      hrootTime, hrootBeforeOld, holdAnchor, hrootPow, hrootGrid⟩
                  have hcorrected :=
                    CoordinatorAssignmentRegisterInstall.later_corrected_branch
                      output clockData hkind
                  have hnewStart : installed.registers.payload.sigma = instruction.time := by
                    rw [hinstalled]
                    exact output.payload_start
                  have hnewTime : instruction.time.val = record.input.time.val := by
                    calc
                      instruction.time.val = installed.registers.payload.sigma.val :=
                        (congrArg Fin.val hnewStart).symm
                      _ = record.input.time.val := hsource.2.2
                  have holdBeforeNew : old.sigma.val ≤ instruction.time.val := by
                    omega
                  have hfreeze : output.localConsistency.oldFreezeAt =
                      FollowerCutoffScan.gridBoundary p rate.eta.val old.sigma := by
                    calc
                      output.localConsistency.oldFreezeAt = clockData.priorClock.g :=
                        clockData.priorGrid_eq_freezeAt.symm
                      _ = CoordinatorPhaseClock.boundaryFromSigma p rate.eta.val
                          clockData.priorClock.sigma := clockData.priorClockValid.1
                      _ = FollowerCutoffScan.gridBoundary p rate.eta.val old.sigma := by
                        simp [clockData.priorSigma_eq,
                          CoordinatorPhaseClock.boundaryFromSigma,
                          ReferenceActivePhysicalStep.collectionInput]
                  have hgridNew := gridBoundary_eq_of_before rate old.sigma instruction.time
                    holdBeforeNew (by rw [← hfreeze]; exact hcorrected.1)
                  have hanchor :=
                    CoordinatorAssignmentRegisterInstall.later_payload_anchor_corrected
                      output clockData hkind
                  have hinstalledAnchor : installed.registers.payload.anchor = old.anchor := by
                    rw [hinstalled]
                    exact hanchor
                  have hrootBeforeNew : P_rho.sigma.val ≤ installed.registers.payload.sigma.val := by
                    rw [hnewStart]
                    omega
                  have hrootAnchorCurrent : installed.registers.payload.anchor = P_rho.anchor := by
                    exact hinstalledAnchor.trans holdAnchor
                  have hrootGridCurrent :
                      FollowerCutoffScan.gridBoundary p rate.eta.val P_rho.sigma =
                        FollowerCutoffScan.gridBoundary p rate.eta.val installed.registers.payload.sigma := by
                    calc
                      FollowerCutoffScan.gridBoundary p rate.eta.val P_rho.sigma =
                          FollowerCutoffScan.gridBoundary p rate.eta.val old.sigma := hrootGrid
                      _ = FollowerCutoffScan.gridBoundary p rate.eta.val instruction.time :=
                        hgridNew.symm
                      _ = FollowerCutoffScan.gridBoundary p rate.eta.val
                          installed.registers.payload.sigma := by rw [hnewStart]
                  exact ⟨rho, P_rho, z_rho,
                    le_trans hrhoLe (Nat.le_of_lt hpriorLt), hrootBirth, hrootVector,
                    hrootBranch, hrootTime, hrootBeforeNew, hrootAnchorCurrent,
                    hrootPow, hrootGridCurrent⟩
              | first =>
                  have hnotfirst :
                      AssignmentScoreReconstruction.expectedLaterStartKind
                        output.localConsistency.oldFreezeAt instruction.time ≠ .first := by
                    by_cases hbefore : instruction.time.val + 1 <
                        output.localConsistency.oldFreezeAt
                    · simp [AssignmentScoreReconstruction.expectedLaterStartKind, hbefore]
                    · simp [AssignmentScoreReconstruction.expectedLaterStartKind, hbefore]
                  exact False.elim (hnotfirst (hkindExpected.symm.trans hkind))
          | clockFailure _ _ => simp [InstallationBirth, hcoord] at hbirth
          | localFailure _ _ _ _ => simp [InstallationBirth, hcoord] at hbirth
          | coreFailure _ _ _ _ => simp [InstallationBirth, hcoord] at hbirth
          | continuing _ _ _ _ => simp [InstallationBirth, hcoord] at hbirth
          | laterReconstructionFailure _ _ _ _ _ _ _ _ =>
              simp [InstallationBirth, hcoord] at hbirth
          | laterPrefixFailure _ _ _ _ _ _ _ _ _ =>
              simp [InstallationBirth, hcoord] at hbirth
          | laterOrientationFailure _ _ _ _ _ _ _ =>
              simp [InstallationBirth, hcoord] at hbirth
          | laterChoiceFailure _ _ _ _ _ _ _ _ _ _ =>
              simp [InstallationBirth, hcoord] at hbirth

/-- Every actual live input in the complete suffix retains an actual first or
renewal installation as the origin of its whole score vector and grid block. -/
theorem complete_live_episode_anchor_origin
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ)
    (hlive : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val].input.state.coordinator = .live r q base) :
    ∃ birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate),
      ∃ P_rho : ReferenceActivePhysicalStep.Payload rate,
        ∃ z_rho : Fin p.K → ℕ,
          birth ∈ (ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate source rewards C_star C_h).take k.val ∧
          InstallationBirth birth P_rho ∧
          IsEpisodeAnchorBirth birth ∧
          installationScoreVector birth P_rho z_rho ∧
          birth.input.time = P_rho.sigma ∧
          P_rho.sigma.val ≤ r.payload.sigma.val ∧
          r.payload.anchor = P_rho.anchor ∧
          (∀ a, P_rho.anchor a =
            AssignmentScoreReconstruction.sourceWeightBase p ^ z_rho a) ∧
          FollowerCutoffScan.gridBoundary p rate.eta.val P_rho.sigma =
            FollowerCutoffScan.gridBoundary p rate.eta.val r.payload.sigma ∧
          r.gridBoundary = FollowerCutoffScan.gridBoundary p rate.eta.val P_rho.sigma := by
  classical
  let R := CompleteRecords rate rewards C_star C_h source
  have hretained :=
    ReferenceAssignmentRetainedBirthProvenance.complete_coordinator_retained_birth
      rate rewards C_star C_h source k
  have hretainedLive := by simpa [R, hlive] using hretained
  rcases hretainedLive with ⟨⟨prior, hpriorLt, hpriorBirth, _⟩, _⟩
  have hpriorOrigin := episode_origin_of_installation rate rewards C_star C_h source
    prior.val prior.isLt r.payload hpriorBirth
  rcases hpriorOrigin with
    ⟨rho, P_rho, z_rho, hrhoLe, hrootBirth, hrootVector, hrootBranch,
      hrootTime, hrootBefore, hrootAnchor, hrootPow, hrootGrid⟩
  have hindex : rho.val < k.val := lt_of_le_of_lt hrhoLe hpriorLt
  have hmem : R[rho.val]'rho.isLt ∈ R.take k.val := by
    have htake : rho.val < (R.take k.val).length := by
      simp
      exact ⟨hindex, rho.isLt⟩
    simpa [List.getElem_take, hindex] using
      (List.getElem_mem (l := R.take k.val) (n := rho.val) htake)
  have hclock := complete_record_clockAt rate rewards C_star C_h source k
  have hinputClock := hclock.1
  change ReferenceCoordinatorClockDomains.clockAt source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source)
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val].input.time.val
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val].input.state at hinputClock
  simp only [ReferenceCoordinatorClockDomains.clockAt, hlive] at hinputClock
  rcases hinputClock with ⟨_, hvalid, hsigma, _, hgridBoundary, _, _, _⟩
  have hfreeze : r.gridBoundary = FollowerCutoffScan.gridBoundary p rate.eta.val r.payload.sigma := by
    calc
      r.gridBoundary = r.priorClock.g := hgridBoundary
      _ = CoordinatorPhaseClock.boundaryFromSigma p rate.eta.val r.priorClock.sigma := hvalid.1
      _ = FollowerCutoffScan.gridBoundary p rate.eta.val r.payload.sigma := by
        rw [hsigma]
        simp [CoordinatorPhaseClock.boundaryFromSigma]
  refine ⟨R[rho.val]'rho.isLt, P_rho, z_rho, hmem, hrootBirth, hrootBranch,
    hrootVector, hrootTime, hrootBefore, hrootAnchor, hrootPow, hrootGrid, ?_⟩
  exact hfreeze.trans hrootGrid.symm

private theorem complete_output_live_gridBoundary
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ)
    (houtput : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val].output.next.coordinator = .live r q base) :
    r.gridBoundary = FollowerCutoffScan.gridBoundary p rate.eta.val r.payload.sigma := by
  have hclock := complete_record_clockAt rate rewards C_star C_h source k
  have hnextClock := hclock.2
  simp only [ReferenceCoordinatorClockDomains.clockAt, houtput] at hnextClock
  rcases hnextClock with ⟨_, hvalid, hsigma, _, hgridBoundary, _, _, _⟩
  calc
    r.gridBoundary = r.priorClock.g := hgridBoundary
    _ = CoordinatorPhaseClock.boundaryFromSigma p rate.eta.val r.priorClock.sigma := hvalid.1
    _ = FollowerCutoffScan.gridBoundary p rate.eta.val r.payload.sigma := by
      rw [hsigma]
      simp [CoordinatorPhaseClock.boundaryFromSigma]

/-- The complete record's actual next-state live output has an origin among
the records through the current physical update, including a birth on this
round. -/
theorem complete_output_live_episode_anchor_origin
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ)
    (houtput : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val].output.next.coordinator = .live r q base) :
    ∃ birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate),
      ∃ P_rho : ReferenceActivePhysicalStep.Payload rate,
        ∃ z_rho : Fin p.K → ℕ,
          birth ∈ (ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate source rewards C_star C_h).take (k.val + 1) ∧
          InstallationBirth birth P_rho ∧
          IsEpisodeAnchorBirth birth ∧
          installationScoreVector birth P_rho z_rho ∧
          birth.input.time = P_rho.sigma ∧
          P_rho.sigma.val ≤ r.payload.sigma.val ∧
          r.payload.anchor = P_rho.anchor ∧
          (∀ a, P_rho.anchor a =
            AssignmentScoreReconstruction.sourceWeightBase p ^ z_rho a) ∧
          FollowerCutoffScan.gridBoundary p rate.eta.val P_rho.sigma =
            FollowerCutoffScan.gridBoundary p rate.eta.val r.payload.sigma ∧
          r.gridBoundary = FollowerCutoffScan.gridBoundary p rate.eta.val P_rho.sigma := by
  classical
  let R := CompleteRecords rate rewards C_star C_h source
  let record := R[k.val]'k.isLt
  have hstepLive :
      (ReferenceActivePhysicalStep.step record.input).next.coordinator = .live r q base := by
    rw [← record.output_eq]
    exact houtput
  have hcurrentStored :
      ReferenceAssignmentPayloadPersistence.storedPayload
        (ReferenceActivePhysicalStep.step record.input).next.coordinator = some r.payload := by
    rw [hstepLive]
    rfl
  have hclass :=
    ReferenceAssignmentPayloadChronology.actualStep_payload_classification record.input
  have hactualRecord :
      ReferenceAssignmentPayloadChronology.actualStepRecord record.input = record := by
    cases record with
    | mk input output hout =>
        cases hout
        rfl
  have hfreeze := complete_output_live_gridBoundary rate rewards C_star C_h source
    k r q base houtput
  rcases hclass with hnone | ⟨old, hstoredOld, hstoredNext⟩ |
      ⟨fresh, hfreshBirth, hstoredFresh⟩
  · rw [hcurrentStored] at hnone
    cases hnone
  · have holdEq : old = r.payload := Option.some.inj (hstoredNext.symm.trans hcurrentStored)
    have hprior :
        ∃ prior : Fin R.length, prior.val < k.val ∧
          InstallationBirth (R[prior.val]'prior.isLt) old := by
      have hretained :=
        ReferenceAssignmentRetainedBirthProvenance.complete_coordinator_retained_birth
          rate rewards C_star C_h source k
      cases hstate : record.input.state.coordinator with
      | first => simp [ReferenceAssignmentPayloadPersistence.storedPayload, hstate]
          at hstoredOld
      | dagger => simp [ReferenceAssignmentPayloadPersistence.storedPayload, hstate]
          at hstoredOld
      | live oldRegisters oldOwned oldBase =>
          simp [ReferenceAssignmentPayloadPersistence.storedPayload, hstate] at hstoredOld
          have hretained' := by simpa [record, R, hstate] using hretained
          rcases hretained' with ⟨⟨prior, hpriorLt, hpriorBirth, _⟩, _⟩
          have hold : oldRegisters.payload = old := hstoredOld
          exact ⟨prior, hpriorLt, by rw [← hold]; exact hpriorBirth⟩
      | collection payload ledger saved =>
          simp [ReferenceAssignmentPayloadPersistence.storedPayload, hstate] at hstoredOld
          have hretained' := by simpa [record, R, hstate] using hretained
          rcases hretained' with ⟨⟨prior, hpriorLt, hpriorBirth, _⟩, _, _, _⟩
          have hold : payload = old := hstoredOld
          exact ⟨prior, hpriorLt, by rw [← hold]; exact hpriorBirth⟩
    rcases hprior with ⟨prior, hpriorLt, hpriorBirth⟩
    have hpriorOrigin := episode_origin_of_installation rate rewards C_star C_h source
      prior.val prior.isLt old hpriorBirth
    rcases hpriorOrigin with
      ⟨rho, P_rho, z_rho, hrhoLe, hrootBirth, hrootVector, hrootBranch,
        hrootTime, hrootBefore, hrootAnchor, hrootPow, hrootGrid⟩
    have hindex : rho.val < k.val + 1 := by omega
    have hmem : R[rho.val]'rho.isLt ∈ R.take (k.val + 1) := by
      have htake : rho.val < (R.take (k.val + 1)).length := by
        simp
        exact ⟨by omega, rho.isLt⟩
      simpa [List.getElem_take, hindex] using
        (List.getElem_mem (l := R.take (k.val + 1)) (n := rho.val) htake)
    subst old
    refine ⟨R[rho.val]'rho.isLt, P_rho, z_rho, hmem, hrootBirth, hrootBranch,
      hrootVector, hrootTime, hrootBefore, hrootAnchor, hrootPow, hrootGrid, ?_⟩
    exact hfreeze.trans hrootGrid.symm
  · have hfreshEq : fresh = r.payload :=
      Option.some.inj (hstoredFresh.symm.trans hcurrentStored)
    have hfreshBirthRecord : InstallationBirth record fresh := by
      rw [← hactualRecord]
      exact hfreshBirth
    have hfreshOrigin := episode_origin_of_installation rate rewards C_star C_h source
      k.val k.isLt fresh hfreshBirthRecord
    rcases hfreshOrigin with
      ⟨rho, P_rho, z_rho, hrhoLe, hrootBirth, hrootVector, hrootBranch,
        hrootTime, hrootBefore, hrootAnchor, hrootPow, hrootGrid⟩
    have hindex : rho.val < k.val + 1 := by omega
    have hmem : R[rho.val]'rho.isLt ∈ R.take (k.val + 1) := by
      have htake : rho.val < (R.take (k.val + 1)).length := by
        simp
        exact ⟨by omega, rho.isLt⟩
      simpa [List.getElem_take, hindex] using
        (List.getElem_mem (l := R.take (k.val + 1)) (n := rho.val) htake)
    subst fresh
    refine ⟨R[rho.val]'rho.isLt, P_rho, z_rho, hmem, hrootBirth, hrootBranch,
      hrootVector, hrootTime, hrootBefore, hrootAnchor, hrootPow, hrootGrid, ?_⟩
    exact hfreeze.trans hrootGrid.symm

end Bandits.Support.ReferenceCompleteEpisodeAnchorOrigin

end
