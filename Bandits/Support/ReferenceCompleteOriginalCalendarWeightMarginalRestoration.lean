/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteOriginalCalendarCellPresence

import Mathlib.Tactic

/-!
# Original calendar installed weights and marginal restoration

Every actual installed score vector, episode anchor, and later reconstruction
is identified with the same zero-origin word of the complete original suffix.
The numerical stopped run is compared only at its own overflow cut.
-/

@[expose] public section

open Bandits.Support
open ConstructorDimensions
open ReferenceActivePhysicalStep
open ReferenceCompletePhysicalHistory
open ReferenceAssignmentPayloadPersistence
open ReferenceCompleteEpisodeAnchorOrigin
open ReferenceCompleteLiveComplementScoreSpan
open ReferenceCompleteInstallationEpisodeScoreSpan
open ReferenceFirstCorrectedNextCalendarWordJoin
open ReferenceFirstCollectionCorrectedSliceNumericalPrefix
open ReferenceFirstCollectionCurrentRetainedGate
open ReferenceCollectionPhaseHistory
open ReferenceCompleteOriginalCalendarCellPresence
open scoped Classical

namespace Bandits.Support.ReferenceCompleteOriginalCalendarWeightMarginalRestoration

variable {p : ConstructorDimensions.Parameters}

private theorem actual_birth_score_vector
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (L : List (RecordedQueueRun.RoundInput p.K))
    (hprefix : ∀ h : ℕ,
      h ≤ (completeSuffixRecords rate z rewards C_star C_h).length →
      prefixInputs rate rewards C_star C_h
        (physicalStart rate z rewards C_star C_h + h) z = some (L.take h))
    (k : Fin (completeSuffixRecords rate z rewards C_star C_h).length)
    (P : ReferenceActivePhysicalStep.Payload rate)
    (hbirth : InstallationBirth
      (completeSuffixRecords rate z rewards C_star C_h)[k.val] P) :
    ReferenceCompleteLiveComplementScoreSpan.installationScoreVector
      (completeSuffixRecords rate z rewards C_star C_h)[k.val] P
      (fun i => (calendarReplay rate L i k.val).1) := by
  classical
  let R := completeSuffixRecords rate z rewards C_star C_h
  let record := R[k.val]
  change InstallationBirth record P at hbirth
  cases hcoord : record.output.preparation.coordinator with
  | first outcome =>
      cases outcome with
      | chosen installed selected =>
          simp only [InstallationBirth, hcoord] at hbirth
          rcases hbirth with ⟨rfl, _⟩
          have hsource := ReferenceCompleteLiveComplementScoreSpan.first_installation_source
            record installed selected hcoord
          have hstate : record.input.state.coordinator = .first := by
            have hactual : record.output.preparation.coordinator =
                ReferenceActivePhysicalStep.dispatch record.input := by
              rw [record.output_eq]
              rfl
            have hdispatch := hactual.symm.trans hcoord
            cases hs : record.input.state.coordinator with
            | first => rfl
            | live r q base =>
                simp only [ReferenceActivePhysicalStep.dispatch, hs] at hdispatch
                cases hr : CoordinatorRoundDispatch.dispatch
                    (.live (ReferenceActivePhysicalStep.liveInput record.input r q base));
                  simp [hr] at hdispatch
                all_goals cases hdispatch
            | collection payload ledger saved =>
                by_cases hvalid : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
                · let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
                  let clock := ReferenceActivePhysicalStep.collectionClock
                    payload ledger saved cutoff
                  cases hr : CoordinatorRoundDispatch.dispatch
                      (.collection (ReferenceActivePhysicalStep.collectionInput
                        record.input payload ledger clock cutoff));
                    simp [ReferenceActivePhysicalStep.dispatch, hs, hvalid,
                      cutoff, clock, hr] at hdispatch
                  all_goals cases hdispatch
                · simp [ReferenceActivePhysicalStep.dispatch, hs, hvalid] at hdispatch
            | dagger => simp [ReferenceActivePhysicalStep.dispatch, hs] at hdispatch
          have hkzero : k.val = 0 := by
            by_contra hk
            have hkpos : 0 < k.val := Nat.pos_of_ne_zero hk
            let j : Fin R.length := ⟨k.val - 1, by dsimp [R]; omega⟩
            have hj : j.val + 1 < R.length := by dsimp [j, R]; omega
            have hadj := ReferenceCompleteLaterLiveComplementPrefixReplay.complete_adjacent
              (rate := rate) rewards C_star C_h z j.val hj
            have hphase :=
              (ReferenceCompleteCoordinatorPhaseExhaustion.complete_coordinator_phase_exhaustion
                rate rewards C_star C_h z).1
            have hout : R[j.val].output.next.coordinator ≠ .first :=
              (hphase j).2.2.2.1
            have hindex : j.val + 1 = k.val := by dsimp [j]; omega
            have hcurr :
                (completeSuffixRecords rate z rewards C_star C_h)[k.val].input.state.coordinator =
                  .first := by
              simpa [record, R] using hstate
            have hcurr' := congrArg
              (fun state : ReferenceActivePhysicalStep.State p rate => state.coordinator)
              hadj
            have hprev : R[j.val].output.next.coordinator = .first :=
              hcurr'.symm.trans (by simpa only [hindex] using hcurr)
            exact hout hprev
          have h0 : 0 < R.length := by
            rw [← hkzero]
            exact k.isLt
          have hkeq : k = ⟨0, h0⟩ := Fin.ext hkzero
          subst k
          have hvec : ReferenceCompleteLiveComplementScoreSpan.installationScoreVector record
              installed.registers.payload (fun _ => 0) := hsource.2.1
          have htarget : (fun i : Fin p.K => (calendarReplay rate L i 0).1) =
              (fun _ => 0) := by
            funext i
            change (QueueReplay.replay (4 * rate.n) (0, 0)
              (rawCalendar rate i (L.take 0))).1 = 0
            simp [rawCalendar, QueueReplay.replay]
          rw [htarget]
          simpa [record, R] using hvec
      | choiceDomainFailure _ => simp [InstallationBirth, hcoord] at hbirth
      | recorderBoundaryFailure _ => simp [InstallationBirth, hcoord] at hbirth
      | choiceRejected _ => simp [InstallationBirth, hcoord] at hbirth
  | live _ _ _ _ => simp [InstallationBirth, hcoord] at hbirth
  | invalidCollectionCutoff => simp [InstallationBirth, hcoord] at hbirth
  | dagger => simp [InstallationBirth, hcoord] at hbirth
  | collection payload ledger clock cutoff outcome =>
      cases outcome with
      | laterChosen core consistent started hstart instruction hassignment output hlocal
          clockData installed selected =>
          simp only [InstallationBirth, hcoord] at hbirth
          rcases hbirth with ⟨hpayload, _⟩
          subst P
          have hprep : record.output.preparation =
              ReferenceActivePhysicalStep.prepare record.input := by
            rw [record.output_eq]
            rfl
          have hlater : laterChosen record.input = true := by
            unfold laterChosen
            rw [← hprep, hcoord]
          obtain ⟨P0, hP0len, _hP0map, hP0prefix, hinit⟩ :=
            Bandits.Support.ReferenceCompleteInstallationCalendarInitializationInduction.internal_complete_later_installation_calendar_initialization
              rate rewards C_star C_h z k hlater
          have hP0eq : P0 = L.take k.val := by
            have hleft := hP0prefix k.val le_rfl
            have hright := hprefix k.val (by exact k.isLt.le)
            have htake : P0.take k.val = P0 := by
              rw [List.take_of_length_le (by omega : P0.length ≤ k.val)]
            have hleft' : prefixInputs rate rewards C_star C_h
                (physicalStart rate z rewards C_star C_h + k.val) z = some P0 := by
              simpa only [htake] using hleft
            exact Option.some.inj (hleft'.symm.trans hright)
          have hP0replay (i : Fin p.K) :
              ReferenceFirstReplacementCalendarInitialization.calendarReplay rate i P0 P0.length =
                calendarReplay rate L i k.val := by
            have htakeLen : (L.take k.val).length = k.val := by
              simpa only [hP0eq] using hP0len
            have htake : (L.take k.val).take k.val = L.take k.val :=
              List.take_of_length_le (by omega)
            rw [hP0eq]
            change QueueReplay.replay (4 * rate.n) (0, 0)
                (ReferenceFirstReplacementCalendarInitialization.rawCalendar rate i
                  ((L.take k.val).take ((L.take k.val).length))) =
              QueueReplay.replay (4 * rate.n) (0, 0)
                (ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar rate i (L.take k.val))
            rw [htakeLen, htake]
            rfl
          -- The initialization certificate names this same actual dispatch and
          -- its reconstruction, so its source score is the installed vector.
          have hrestored :
              (∀ i : Fin p.K,
                AssignmentScoreReconstruction.sourceScore output.reconstruction i =
                  (calendarReplay rate L i k.val).1) ∧
              (∀ j : CanonicalFastSampling.FastArm installed.registers.payload.slowSet,
                installed.registers.complementScores j =
                  (calendarReplay rate L j.val k.val).1) := by
            have hcertificate := hinit
            simp only [ReferenceFirstReplacementCalendarInitialization.initializes_calendar] at hcertificate
            rcases hcertificate with
              ⟨payload0, ledger0, saved0, cutoff0, hstate0, hpending0, hcutoff0,
                core0, started0, hstart0, instruction0, hassignment0, htime0,
                consistent0, output0, hlocal0, clockData0, installed0, selected0,
                hinstalled0, hsuccess0, hdispatch0, hbranch0, hpayload0, hsigma0,
                hassigned0, hreconstruction0, hsource0, hassignedArms0,
                hcomplement0, hcorrected0, hrenewal0⟩
            have heq := hcoord.symm.trans hbranch0
            cases heq
            constructor
            · intro i
              exact ((hsource0 i).1).trans (congrArg Prod.fst (hP0replay i))
            · intro j
              exact ((hcomplement0 j).1).trans (congrArg Prod.fst (hP0replay j.val))
          have hscore := hrestored.1
          have hcomplement0 := hrestored.2
          have hvec : ReferenceCompleteLiveComplementScoreSpan.installationScoreVector record
              installed.registers.payload
              (fun i => (calendarReplay rate L i k.val).1) := by
            simp only [ReferenceCompleteLiveComplementScoreSpan.installationScoreVector, hcoord]
            refine ⟨rfl, ?_, ?_⟩
            · funext i
              exact (hscore i).symm
            · intro j
              exact hcomplement0 j
          exact hvec
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
      | laterChoiceFailure _ _ _ _ _ _ _ _ _ _ _ =>
          simp [InstallationBirth, hcoord] at hbirth

/-- A branch-local derivation used only after an actual birth has been
obtained from the original record. -/
private theorem installation_score_anchor_from_word
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (L : List (RecordedQueueRun.RoundInput p.K))
    (hprefix : ∀ h : ℕ,
      h ≤ (completeSuffixRecords rate z rewards C_star C_h).length →
      prefixInputs rate rewards C_star C_h
        (physicalStart rate z rewards C_star C_h + h) z = some (L.take h))
    (k : Fin (completeSuffixRecords rate z rewards C_star C_h).length)
    (P : ReferenceActivePhysicalStep.Payload rate)
    (hbirth : InstallationBirth
      (completeSuffixRecords rate z rewards C_star C_h)[k.val] P) :
    ∃ rho : Fin (completeSuffixRecords rate z rewards C_star C_h).length,
        ∃ P_rho : ReferenceActivePhysicalStep.Payload rate,
          rho.val ≤ k.val ∧
          InstallationBirth
            (completeSuffixRecords rate z rewards C_star C_h)[rho.val] P_rho ∧
          IsEpisodeAnchorBirth
            (completeSuffixRecords rate z rewards C_star C_h)[rho.val] ∧
          ReferenceCompleteLiveComplementScoreSpan.installationScoreVector
            (completeSuffixRecords rate z rewards C_star C_h)[k.val] P
            (fun i => (calendarReplay rate L i k.val).1) ∧
          ReferenceCompleteLiveComplementScoreSpan.installationScoreVector
            (completeSuffixRecords rate z rewards C_star C_h)[rho.val] P_rho
            (fun i => (calendarReplay rate L i rho.val).1) ∧
          P.anchor = P_rho.anchor ∧
          ∀ i : Fin p.K,
            P_rho.anchor i = AssignmentScoreReconstruction.sourceWeightBase p ^
              (calendarReplay rate L i rho.val).1 := by
  classical
  let R := completeSuffixRecords rate z rewards C_star C_h
  obtain ⟨rho, P_rho, z_current, z_origin, hrho, hbirthOrigin,
    hroot, hvectorCurrent, hvectorOrigin, htime, htimeOrder, hanchor,
    hpow, _hgrid, _hspan⟩ :=
    ReferenceCompleteInstallationEpisodeScoreSpan.actual_installation_episode_score_span
      rate rewards C_star C_h z k P hbirth
  have hcurrent := actual_birth_score_vector rate rewards C_star C_h
    z L hprefix k P hbirth
  have horigin := actual_birth_score_vector rate rewards C_star C_h
    z L hprefix rho P_rho hbirthOrigin
  have hcurrentEq := Bandits.Support.ReferenceCompleteEpisodeAnchorOrigin.installationScoreVector_unique
    R[k.val] P z_current (fun i => (calendarReplay rate L i k.val).1)
    hvectorCurrent hcurrent
  have horiginEq := Bandits.Support.ReferenceCompleteEpisodeAnchorOrigin.installationScoreVector_unique
    R[rho.val] P_rho z_origin (fun i => (calendarReplay rate L i rho.val).1)
    hvectorOrigin horigin
  refine ⟨rho, P_rho, hrho, hbirthOrigin, hroot,
    hcurrent, horigin, hanchor, ?_⟩
  intro i
  rw [hpow i, congrFun horiginEq i]

private theorem initializationCalendarReplay_eq_original
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (P0 L : List (RecordedQueueRun.RoundInput p.K)) (b : ℕ)
    (hP0len : P0.length = b) (hP0eq : P0 = L.take b)
    (i : Fin p.K) :
    ReferenceFirstReplacementCalendarInitialization.calendarReplay
        rate i P0 P0.length = calendarReplay rate L i b := by
  have htakeLen : (L.take b).length = b := by
    simpa only [hP0eq] using hP0len
  have htake : (L.take b).take b = L.take b :=
    List.take_of_length_le (by omega)
  rw [hP0eq]
  change QueueReplay.replay (4 * rate.n) (0, 0)
      (ReferenceFirstReplacementCalendarInitialization.rawCalendar rate i
        ((L.take b).take ((L.take b).length))) =
    QueueReplay.replay (4 * rate.n) (0, 0)
      (ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar rate i (L.take b))
  rw [htakeLen, htake]
  rfl

/-- On a launch, the unique complete original word simultaneously restores
every actual installation score vector and its original first/renewal anchor.
No-launch retains the literal absent-prefix branch. -/
public theorem complete_original_installation_score_anchor_restoration
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    match ReferenceCorrectedInitializationLaunch.correctedLaunch
        rate z rewards C_star C_h with
    | none =>
        completeSuffixRecords rate z rewards C_star C_h = [] ∧
        physicalStart rate z rewards C_star C_h = p.T ∧
        (∀ n, prefixInputs rate rewards C_star C_h n z = none)
    | some _ =>
        ∃ L : List (RecordedQueueRun.RoundInput p.K),
          L.length = (completeSuffixRecords rate z rewards C_star C_h).length ∧
          (∀ h : ℕ, h ≤ (completeSuffixRecords rate z rewards C_star C_h).length →
            prefixInputs rate rewards C_star C_h
              (physicalStart rate z rewards C_star C_h + h) z = some (L.take h)) ∧
          (∀ k : Fin (completeSuffixRecords rate z rewards C_star C_h).length,
            ∀ P : ReferenceActivePhysicalStep.Payload rate,
              InstallationBirth
                (completeSuffixRecords rate z rewards C_star C_h)[k.val] P →
              ∃ rho : Fin (completeSuffixRecords rate z rewards C_star C_h).length,
                ∃ P_rho : ReferenceActivePhysicalStep.Payload rate,
                  rho.val ≤ k.val ∧
                  InstallationBirth
                    (completeSuffixRecords rate z rewards C_star C_h)[rho.val] P_rho ∧
                  IsEpisodeAnchorBirth
                    (completeSuffixRecords rate z rewards C_star C_h)[rho.val] ∧
                  ReferenceCompleteLiveComplementScoreSpan.installationScoreVector
                    (completeSuffixRecords rate z rewards C_star C_h)[k.val] P
                    (fun i => (calendarReplay rate L i k.val).1) ∧
                  ReferenceCompleteLiveComplementScoreSpan.installationScoreVector
                    (completeSuffixRecords rate z rewards C_star C_h)[rho.val] P_rho
                    (fun i => (calendarReplay rate L i rho.val).1) ∧
                  P.anchor = P_rho.anchor ∧
                  ∀ i : Fin p.K,
                    P_rho.anchor i = AssignmentScoreReconstruction.sourceWeightBase p ^
                      (calendarReplay rate L i rho.val).1) := by
  classical
  cases hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h with
  | none =>
      exact Bandits.Support.ReferenceCompleteOriginalCalendarCellPresence.no_launch_complete_original_calendar_cell_presence
        rate rewards C_star C_h z hlaunch
  | some _ =>
      have hcells := Bandits.Support.ReferenceCompleteOriginalCalendarCellPresence.complete_original_calendar_cells
        rate rewards C_star C_h z
      simp only [hlaunch] at hcells
      obtain ⟨L, hlen, _hmap, hprefix, _hbranches⟩ := hcells
      refine ⟨L, hlen, hprefix, ?_⟩
      intro k P hbirth
      exact installation_score_anchor_from_word
        rate rewards C_star C_h z L hprefix k P hbirth

/-- The actual successful later-start reconstruction has the full original
current weights and therefore the corresponding product-set inclusion
marginals. The same C word is used for every later installation. -/
public theorem actual_later_installation_current_weight_marginal_restoration
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    match ReferenceCorrectedInitializationLaunch.correctedLaunch
        rate z rewards C_star C_h with
    | none =>
        completeSuffixRecords rate z rewards C_star C_h = [] ∧
        physicalStart rate z rewards C_star C_h = p.T ∧
        (∀ n, prefixInputs rate rewards C_star C_h n z = none)
    | some _ =>
        ∃ L : List (RecordedQueueRun.RoundInput p.K),
          L.length = (completeSuffixRecords rate z rewards C_star C_h).length ∧
          (∀ h : ℕ, h ≤ (completeSuffixRecords rate z rewards C_star C_h).length →
            prefixInputs rate rewards C_star C_h
              (physicalStart rate z rewards C_star C_h + h) z = some (L.take h)) ∧
          (∀ b : Fin (completeSuffixRecords rate z rewards C_star C_h).length,
            match ((completeSuffixRecords rate z rewards C_star C_h)[b.val]'b.isLt).output.preparation.coordinator with
            | .collection _ _ _ _
                (.laterChosen _ _ _ _ _ _ output _ _ _ _) =>
                (∀ i : Fin p.K,
                  AssignmentScoreReconstruction.currentWeight output.reconstruction i =
                    ScoreWeights.scoreWeight (AssignmentScoreReconstruction.sourceWeightBase p)
                      (calendarReplay rate L i b.val).1) ∧
                ProductSetLaw.theta p.m
                    (fun i => AssignmentScoreReconstruction.currentWeight output.reconstruction i) =
                  ProductSetLaw.theta p.m
                    (fun i => ScoreWeights.scoreWeight
                      (AssignmentScoreReconstruction.sourceWeightBase p)
                      (calendarReplay rate L i b.val).1) ∧
                ∃ a : Fin (completeSuffixRecords rate z rewards C_star C_h).length,
                  ∃ e : ℕ,
                    ∃ seg : ReferenceCollectionSegmentExtraction.Segment rate,
                      a.val < e ∧ e < b.val ∧
                      ReferenceCollectionSegmentExtraction.segmentAt
                        (completeSuffixRecords rate z rewards C_star C_h) e = some seg ∧
                      b.val = e + seg.records.length ∧ seg.final.pending = ∅
            | _ => True) := by
  classical
  cases hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h with
  | none =>
      exact Bandits.Support.ReferenceCompleteOriginalCalendarCellPresence.no_launch_complete_original_calendar_cell_presence
        rate rewards C_star C_h z hlaunch
  | some _ =>
      have hcells := Bandits.Support.ReferenceCompleteOriginalCalendarCellPresence.complete_original_calendar_cells
        rate rewards C_star C_h z
      simp only [hlaunch] at hcells
      obtain ⟨L, hlen, _hmap, hprefix, _hbranches⟩ := hcells
      refine ⟨L, hlen, hprefix, ?_⟩
      intro b
      let record :=
        (completeSuffixRecords rate z rewards C_star C_h)[b.val]
      cases hcoord : record.output.preparation.coordinator with
      | collection payload ledger clock cutoff outcome =>
          cases outcome with
          | laterChosen core consistent started hstart instruction hassignment output hlocal
              clockData installed selected =>
              have hprep : record.output.preparation =
                  ReferenceActivePhysicalStep.prepare record.input := by
                rw [record.output_eq]
                rfl
              have hlater : laterChosen record.input = true := by
                unfold laterChosen
                rw [← hprep, hcoord]
              obtain ⟨P0, hP0len, _hP0map, hP0prefix, hinit⟩ :=
                Bandits.Support.ReferenceCompleteInstallationCalendarInitializationInduction.internal_complete_later_installation_calendar_initialization
                  rate rewards C_star C_h z b hlater
              have hP0eq : P0 = L.take b.val := by
                have hleft := hP0prefix b.val le_rfl
                have hright := hprefix b.val (by exact b.isLt.le)
                have htake : P0.take b.val = P0 := by
                  rw [List.take_of_length_le (by omega : P0.length ≤ b.val)]
                have hleft' : prefixInputs rate rewards C_star C_h
                    (physicalStart rate z rewards C_star C_h + b.val) z = some P0 := by
                  simpa only [htake] using hleft
                exact Option.some.inj (hleft'.symm.trans hright)
              have hscore : ∀ i : Fin p.K,
                  AssignmentScoreReconstruction.sourceScore output.reconstruction i =
                    (calendarReplay rate L i b.val).1 := by
                have hcertificate := hinit
                simp only [ReferenceFirstReplacementCalendarInitialization.initializes_calendar] at hcertificate
                rcases hcertificate with
                  ⟨payload0, ledger0, saved0, cutoff0, hstate0, hpending0, hcutoff0,
                    core0, started0, hstart0, instruction0, hassignment0, htime0,
                    consistent0, output0, hlocal0, clockData0, installed0, selected0,
                    hinstalled0, hsuccess0, hdispatch0, hbranch0, hpayload0, hsigma0,
                    hassigned0, hreconstruction0, hsource0, hassignedArms0,
                    hcomplement0, hcorrected0, hrenewal0⟩
                have heq := hcoord.symm.trans hbranch0
                cases heq
                intro i
                exact (hsource0 i).1.trans (congrArg Prod.fst
                  (initializationCalendarReplay_eq_original rate P0 L b.val
                    hP0len hP0eq i))
              have hweights :
                  (fun i : Fin p.K =>
                    AssignmentScoreReconstruction.currentWeight output.reconstruction i) =
                  (fun i : Fin p.K =>
                    ScoreWeights.scoreWeight
                      (AssignmentScoreReconstruction.sourceWeightBase p)
                      (calendarReplay rate L i b.val).1) := by
                funext i
                change ScoreWeights.scoreWeight
                    (AssignmentScoreReconstruction.sourceWeightBase p)
                    (AssignmentScoreReconstruction.sourceScore output.reconstruction i) = _
                rw [hscore i]
              have hprevious := Bandits.Support.ReferenceCompleteInstallationPredecessorInterval.internal_complete_installation_predecessor_interval
                  rate rewards C_star C_h z b hlater
              obtain ⟨a, r0, q0, beta, e, seg, I, saved, hbefore, hafter,
                _hdate, _hbirth, _hsigma, _hnext, _hbase, _hbetween, hsegment,
                _hnonempty, _hentry, _hchosen, _hpayload, _hinitializer, _hchecked,
                _harm, _hsigmaI, _hcutoff, _hbaseI, hbdate, _hprefix, _hdrop,
                _hexit, _hstate, _hstateCoord, hpendingEmpty, _hcursor, _hfirst⟩ :=
                hprevious
              exact ⟨fun i => congrFun hweights i,
                ⟨congrArg (ProductSetLaw.theta p.m) hweights,
                  ⟨a, e, seg, hbefore, hafter, hsegment, hbdate, hpendingEmpty⟩⟩⟩
          | clockFailure _ _ => simp
          | localFailure _ _ _ _ => simp
          | coreFailure _ _ _ _ => simp
          | continuing _ _ _ _ => simp
          | laterReconstructionFailure _ _ _ _ _ _ _ _ => simp
          | laterPrefixFailure _ _ _ _ _ _ _ _ _ => simp
          | laterOrientationFailure _ _ _ _ _ _ _ => simp
          | laterChoiceFailure _ _ _ _ _ _ _ _ _ _ _ => simp
      | first _ => simp
      | live _ _ _ _ => simp
      | invalidCollectionCutoff => simp
      | dagger => simp

private theorem rawCalendar_replay_eq_unstopped
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (xs : List (RecordedQueueRun.RoundInput p.K))
    (initial : ℕ × ℕ) (i : Fin p.K) :
    QueueReplay.replay (4 * rate.n) initial
        (ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar rate i xs) =
      QueueReplay.replay (4 * rate.n) initial
        (xs.map fun cell =>
          UnstoppedRecordedQueueComparison.unstoppedRecord
            (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell i) := by
  induction xs generalizing initial with
  | nil => rfl
  | cons cell xs ih =>
      change QueueReplay.replay (4 * rate.n)
          (QueueReplay.transition (4 * rate.n) initial
            (cell.enabled, RecordedQueueRun.quantizedArrival
              (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell i))
          (ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar rate i xs) =
        QueueReplay.replay (4 * rate.n)
          (QueueReplay.transition (4 * rate.n) initial
            (UnstoppedRecordedQueueComparison.unstoppedRecord
              (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell i))
          (xs.map fun nextCell =>
            UnstoppedRecordedQueueComparison.unstoppedRecord
              (ReferenceFirstLaunchNumericalCell.queueParameters rate) nextCell i)
      have hstep :
          QueueReplay.transition (4 * rate.n) initial
              (cell.enabled, RecordedQueueRun.quantizedArrival
                (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell i) =
            QueueReplay.transition (4 * rate.n) initial
              (UnstoppedRecordedQueueComparison.unstoppedRecord
                (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell i) := by
        cases henabled : cell.enabled <;>
          simp [UnstoppedRecordedQueueComparison.unstoppedRecord,
            QueueReplay.transition, henabled]
      rw [hstep]
      exact ih _

private theorem calendarReplay_eq_unstoppedReplay
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (xs : List (RecordedQueueRun.RoundInput p.K)) (n : ℕ) (i : Fin p.K) :
    calendarReplay rate xs i n =
      UnstoppedRecordedQueueComparison.unstoppedReplay
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) xs n i := by
  change QueueReplay.replay (4 * rate.n) (0, 0)
      (ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar rate i (xs.take n)) =
    QueueReplay.replay (4 * rate.n) (0, 0)
      ((xs.take n).map fun cell =>
        UnstoppedRecordedQueueComparison.unstoppedRecord
          (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell i)
  exact rawCalendar_replay_eq_unstopped rate (xs.take n) (0, 0) i

/-- The stopped numerical prefix agrees armwise with the same original
zero-origin calendar replay through the actual first-overflow cut. The
no-launch branch keeps its optional observations absent. -/
public theorem stopped_original_calendar_prefix_register_restoration
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    match ReferenceCorrectedInitializationLaunch.correctedLaunch
        rate z rewards C_star C_h with
    | none =>
        completeSuffixRecords rate z rewards C_star C_h = [] ∧
        physicalStart rate z rewards C_star C_h = p.T ∧
        (∀ n, prefixInputs rate rewards C_star C_h n z = none)
    | some _ =>
        ∃ L : List (RecordedQueueRun.RoundInput p.K),
          L.length = (completeSuffixRecords rate z rewards C_star C_h).length ∧
          (∀ h : ℕ, h ≤ (completeSuffixRecords rate z rewards C_star C_h).length →
            prefixInputs rate rewards C_star C_h
              (physicalStart rate z rewards C_star C_h + h) z = some (L.take h)) ∧
          (∀ h : ℕ, h ≤ L.length → ∀ i : Fin p.K,
            (RecordedQueueRun.run
              (ReferenceFirstLaunchNumericalCell.queueParameters rate) (L.take h)).registers i =
              calendarReplay rate L i
                (min h (UnstoppedRecordedQueueComparison.firstOverflowPrefix
                  (ReferenceFirstLaunchNumericalCell.queueParameters rate) L))) := by
  classical
  cases hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h with
  | none =>
      exact Bandits.Support.ReferenceCompleteOriginalCalendarCellPresence.no_launch_complete_original_calendar_cell_presence
          rate rewards C_star C_h z hlaunch
  | some _ =>
      have hcells := Bandits.Support.ReferenceCompleteOriginalCalendarCellPresence.complete_original_calendar_cells
        rate rewards C_star C_h z
      simp only [hlaunch] at hcells
      obtain ⟨L, hlen, _hmap, hprefix, _hcomplete⟩ := hcells
      refine ⟨L, hlen, hprefix, ?_⟩
      intro h hh i
      have hhR : h ≤ (completeSuffixRecords rate z rewards C_star C_h).length := by
        rw [← hlen]
        exact hh
      calc
        (RecordedQueueRun.run
            (ReferenceFirstLaunchNumericalCell.queueParameters rate) (L.take h)).registers i =
          UnstoppedRecordedQueueComparison.unstoppedReplay
            (ReferenceFirstLaunchNumericalCell.queueParameters rate) L
              (min h (UnstoppedRecordedQueueComparison.firstOverflowPrefix
                (ReferenceFirstLaunchNumericalCell.queueParameters rate) L)) i :=
          UnstoppedRecordedQueueComparison.prefix_registers_eq_unstopped_replay
            (ReferenceFirstLaunchNumericalCell.queueParameters rate) L h hh i
        _ = calendarReplay rate L i
            (min h (UnstoppedRecordedQueueComparison.firstOverflowPrefix
              (ReferenceFirstLaunchNumericalCell.queueParameters rate) L)) :=
          (calendarReplay_eq_unstoppedReplay rate L
            (min h (UnstoppedRecordedQueueComparison.firstOverflowPrefix
              (ReferenceFirstLaunchNumericalCell.queueParameters rate) L)) i).symm

private theorem actual_record_time
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (b : Fin (completeSuffixRecords rate z rewards C_star C_h).length) :
    (completeSuffixRecords rate z rewards C_star C_h)[b.val].input.time.val =
      physicalStart rate z rewards C_star C_h + b.val := by
  have htimes := completeSuffixRecords_time_values rate z rewards C_star C_h
  have hlen := completeSuffixRecords_length rate z rewards C_star C_h
  have hb : b.val < p.T - physicalStart rate z rewards C_star C_h := by omega
  have hget := congrArg (fun xs : List ℕ => xs[b.val]?) htimes
  simpa only [List.getElem?_map, List.getElem?_eq_getElem b.isLt,
    Option.map_some, ReferenceActivePhysicalHorizon.calendar,
    List.getElem?_range', hb, ite_true, one_mul, Option.some.injEq] using hget

private theorem pastCells_eq_prefixInputs
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (b : Fin (completeSuffixRecords rate z rewards C_star C_h).length)
    (t : Fin p.T) (ht : t.val = physicalStart rate z rewards C_star C_h + b.val) :
    pastCells? rate rewards C_star C_h t z =
      prefixInputs rate rewards C_star C_h t.val z := by
  have hsub : t.val - physicalStart rate z rewards C_star C_h = b.val := by omega
  have hslots : pastSlots rate rewards C_star C_h t z =
      ((completeSuffixRecords rate z rewards C_star C_h).take b.val).map (cell0 rate) := by
    apply List.ext_getElem
    · simp only [pastSlots, List.length_map, List.length_range, hsub, List.length_take,
        Nat.min_eq_left b.isLt.le]
    · intro k hk hk'
      have hkb : k < b.val := by
        simpa only [pastSlots, List.length_map, List.length_range, hsub] using hk
      have hkR : k < (completeSuffixRecords rate z rewards C_star C_h).length :=
        lt_trans hkb b.isLt
      simp only [pastSlots, List.getElem_map, List.getElem_range,
        List.getElem_take, List.getElem?_eq_getElem hkR, Option.bind_some]
  simp only [pastCells?, prefixInputs, sourceRecords, sourceStart, hsub, hslots]

private theorem calendarReplay_take
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (L : List (RecordedQueueRun.RoundInput p.K)) (v h : ℕ) (hh : h ≤ v)
    (i : Fin p.K) :
    calendarReplay rate (L.take v) i h = calendarReplay rate L i h := by
  simp only [calendarReplay, List.take_take, Nat.min_eq_left hh]

private theorem later_predecessor_final_registers
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (L : List (RecordedQueueRun.RoundInput p.K))
    (hprefix : ∀ h, h ≤ (completeSuffixRecords rate z rewards C_star C_h).length →
      prefixInputs rate rewards C_star C_h
        (physicalStart rate z rewards C_star C_h + h) z = some (L.take h))
    (a : Fin (completeSuffixRecords rate z rewards C_star C_h).length)
    (ha : laterChosen (completeSuffixRecords rate z rewards C_star C_h)[a.val].input = true)
    (e b : ℕ) (seg : ReferenceCollectionSegmentExtraction.Segment rate)
    (he : e = a.val + 1 +
      (ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
        rate rewards C_star C_h z (a.val + 1)).length)
    (heb : e < b) (hb : b < (completeSuffixRecords rate z rewards C_star C_h).length)
    (hseg : ReferenceCollectionSegmentExtraction.segmentAt
      (completeSuffixRecords rate z rewards C_star C_h) e = some seg)
    (hbdate : b = e + seg.records.length) (hempty : seg.final.pending = ∅) :
    ∀ i : Fin p.K,
      seg.final.cutoffRegisters i = some
        ⟨(calendarReplay rate L i e).1, (calendarReplay rate L i e).2,
          (calendarReplay rate L i e).1 - (calendarReplay rate L i (e - 1)).1⟩ ∧
      seg.final.currentRegisters i = some
        ⟨(calendarReplay rate L i b).2,
          (calendarReplay rate L i b).1 - (calendarReplay rate L i (b - 1)).1⟩ ∧
      (calendarReplay rate L i e).1 + seg.final.increment i =
        (calendarReplay rate L i b).1 := by
  classical
  let R := completeSuffixRecords rate z rewards C_star C_h
  obtain ⟨P0, rb, qb, beta, cell, native, hPlen, hPslots, hPprefix,
    hinit, hpost, hbirth, hstrict, hbase, hcell, hnative, hnativePayload,
    henabled, hbirthPrefix, hbirthSlots, hdown, hbranch⟩ :=
    ReferenceCompleteInstallationCollectionPrefixNumericalTruth.actual_later_installation_collection_prefix_numerical_truth
      rate rewards C_star C_h z a ha
  rcases hbranch with hterminal | ⟨k, C, hk, hstate, hClen, hWmap, hWtime,
    e', he', heR, rE, qE, hrPayload, hsegment⟩
  · have horder : a.val < e := by rw [he]; omega
    omega
  have heq : e' = e := by
    rw [hk] at he'
    omega
  rw [heq] at hsegment
  rcases hsegment with hterminal | ⟨heLt, seg', I, l0, Dword,
    hseg', hentry, hpay, hledger, hinitializer, hIeq, hstart, harm, hsigma,
    hcutoff, hscan, hfreeze, hbaseI, hchosen, hne, hpart, hrun, hDlen,
    hDmap, hqueues, hHlen, hGlen, hGtake, hvR, hprefixEvery, hRtake,
    hprefixAll, hlabels, hfinalPending, hfinalNodup, hchecked, hbirthTime,
    hinfoCount, hinfoFinalKnown, hinfoFinalPending⟩
  · omega
  have hsegeq : seg' = seg := Option.some.inj (hseg'.symm.trans hseg)
  subst seg'
  let G := (P0 ++ [cell] ++ C) ++ Dword
  have hG : G = L.take b := by
    have hleft := hprefixEvery b (by omega)
    have hright := hprefix b hb.le
    have hlen : G.length = b := by dsimp only [G]; omega
    have htake : G.take b = G := List.take_of_length_le hlen.le
    change prefixInputs rate rewards C_star C_h
      (physicalStart rate z rewards C_star C_h + b) z = some (G.take b) at hleft
    rw [htake] at hleft
    exact Option.some.inj (hleft.symm.trans hright)
  have hreplay (h : ℕ) (hh : h ≤ b) (i : Fin p.K) :
      calendarReplay rate G i h = calendarReplay rate L i h := by
    rw [hG]
    exact calendarReplay_take rate L b h hh i
  intro i
  have hnot : ¬ CoordinatorCollectionLedger.armPending seg.final i := by
    simp [CoordinatorCollectionLedger.armPending, hempty]
  have hi := hinfoFinalKnown i hnot
  change seg.final.cutoffRegisters i = some
      ⟨(calendarReplay rate G i e).1, (calendarReplay rate G i e).2,
        (calendarReplay rate G i e).1 - (calendarReplay rate G i (e - 1)).1⟩ ∧
    seg.final.currentRegisters i = some
      ⟨(calendarReplay rate G i (e + seg.records.length)).2,
        (calendarReplay rate G i (e + seg.records.length)).1 -
          (calendarReplay rate G i (e + seg.records.length - 1)).1⟩ ∧
    (calendarReplay rate G i e).1 + seg.final.increment i =
      (calendarReplay rate G i (e + seg.records.length)).1 at hi
  rw [← hbdate, hreplay e (by omega) i, hreplay (e - 1) (by omega) i,
    hreplay b le_rfl i, hreplay (b - 1) (by omega) i] at hi
  exact hi

section Alignment

variable {rate : ReferenceActivePhysicalStep.RateInput p}
    {source : BootstrapPrivateRoundStreams.SourceInput p} {rewards : ActualInitializationPhysicalStep.GridRewardTable p}
    {C_star C_h : ℝ} {count : ℕ}
    {hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true}
    {hspan : ReferenceFirstCollectionReadyStream.startTime (rate := rate)
      source rewards C_star C_h + count ≤ p.T}
    {hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
        source rewards C_star C_h hcross count hspan).records).length < count}

private theorem same_stream_output
    (f g : ReferenceFirstCollectionReadyStream.ActualInitializedStreamOutput
      source rewards C_star C_h count hcross hspan hshort)
    (i : Fin f.ell) (j : Fin g.ell) (hij : i.val = j.val) :
    f.payload = g.payload ∧ f.ledgers i = g.ledgers j ∧ f.saved = g.saved := by
  obtain ⟨r, hr, _, hc, _⟩ := f.output_properties i
  obtain ⟨r', hr', _, hc', _⟩ := g.output_properties j
  have hw : f.window = g.window := f.windowIsActual.trans g.windowIsActual.symm
  rw [hw, hij, hr'] at hr
  have he : r = r' := Option.some.inj hr.symm
  rw [he] at hc
  exact ReferenceActivePhysicalStep.CoordinatorConfiguration.collection.inj (hc.symm.trans hc')

/-- First empty pending is unique on this actual finite window, including the
alternative where another produced stream exhausts the window. -/
private theorem first_empty_alignment
    (f g : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
      source rewards C_star C_h count hcross hspan hshort)
    (hf : f.ledger.pending = ∅) :
    g.stream.ell = f.stream.ell ∧ g.record = f.record ∧
      g.stream.payload = f.stream.payload ∧ g.ledger = f.ledger ∧
      g.stream.saved = f.stream.saved := by
  have hw : f.stream.window = g.stream.window :=
    f.stream.windowIsActual.trans g.stream.windowIsActual.symm
  have hlength : g.stream.ell = f.stream.ell := by
    apply Nat.le_antisymm
    · by_contra hnot
      have hlt : f.stream.ell < g.stream.ell := by omega
      let j : Fin g.stream.ell := ⟨f.last.val, by have h := f.lastIsLast; omega⟩
      have heq := (same_stream_output f.stream g.stream f.last j rfl).2.1
      have hn := g.allEarlierNonempty j (by
        have h := f.lastIsLast
        change f.last.val + 1 < g.stream.ell
        omega)
      rw [← heq, ← f.ledgerIsLast, hf] at hn
      exact Finset.not_nonempty_empty hn
    · by_contra hnot
      have hlt : g.stream.ell < f.stream.ell := by omega
      cases g.outcome with
      | exhausted _ hex _ _ _ =>
          have hfwindow := f.stream.withinWindow
          rw [hw, ← hex] at hfwindow
          omega
      | empty e =>
          let i : Fin f.stream.ell := ⟨g.last.val, by have h := g.lastIsLast; omega⟩
          have heq := (same_stream_output f.stream g.stream i g.last rfl).2.1
          have hn := f.allEarlierNonempty i (by
            have h := g.lastIsLast
            change g.last.val + 1 < f.stream.ell
            omega)
          rw [heq, ← g.ledgerIsLast, e.pendingEmpty] at hn
          exact Finset.not_nonempty_empty hn
  have hlast : g.last.val = f.last.val := by
    have hg := g.lastIsLast
    have hf := f.lastIsLast
    omega
  have hrecord : g.record = f.record := by
    have hr := g.recordAt
    rw [← hw, hlast, f.recordAt] at hr
    exact Option.some.inj hr.symm
  obtain ⟨hp, hl, hs⟩ := same_stream_output g.stream f.stream g.last f.last hlast
  exact ⟨hlength, hrecord, hp, g.ledgerIsLast.trans (hl.trans f.ledgerIsLast.symm), hs⟩

end Alignment

private theorem first_predecessor_cutoff_registers
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (L : List (RecordedQueueRun.RoundInput p.K))
    (hprefix : ∀ h, h ≤ (completeSuffixRecords rate z rewards C_star C_h).length →
      prefixInputs rate rewards C_star C_h
        (physicalStart rate z rewards C_star C_h + h) z = some (L.take h))
    (b : Fin (completeSuffixRecords rate z rewards C_star C_h).length)
    (e : ℕ) (he : e < b.val)
    (payload : Payload rate) (ledger : Ledger rate) (saved : Option (Fin p.T × Bool))
    (hstate : (completeSuffixRecords rate z rewards C_star C_h)[b.val].input.state.coordinator =
      .collection payload ledger saved)
    (u : Fin p.T) (hu : u.val = physicalStart rate z rewards C_star C_h + e)
    (hcell : z ∈ ReferenceCalendarCollectionCallControlLaw.firstCell
      rate rewards C_star C_h u
        (completeSuffixRecords rate z rewards C_star C_h)[b.val].input.time) :
    ∀ i : Fin p.K, ledger.cutoffRegisters i = some
      ⟨(calendarReplay rate L i e).1, (calendarReplay rate L i e).2,
        (calendarReplay rate L i e).1 - (calendarReplay rate L i (e - 1)).1⟩ := by
  classical
  let R := completeSuffixRecords rate z rewards C_star C_h
  let s := physicalStart rate z rewards C_star C_h
  let t := R[b.val].input.time
  have ht : t.val = s + b.val := actual_record_time rate rewards C_star C_h z b
  obtain ⟨hc, hs, hshort, f, head, valid, D, G,
    hsu, hut, hufirst, htotal, hpending, hrecord, hchoice, hDlen,
    hDzero, hDread, hGD, hPast, hGlen, hcoverage, hprefixPast, hsplit, hstart⟩ :=
    ReferenceFirstCollectionOldPrefixCalendarReadout.firstCell_prefix_at_boundary
      rate rewards C_star C_h u t z hcell
  obtain ⟨d, head', initializer, valid', D', hhead', hpay', hinit', hchecked',
    hDlen', hzero', hcells', hqueuePrefix', hledgerPrefix', hfinal⟩ :=
    ReferenceFirstCollectionAllArmNumericalStream.actual_initialized_first_collection_all_arm_numerical_stream
      rate z rewards C_star C_h hc (p.T - s) hs hshort
  obtain ⟨hell, hrec, hpay, hled, hsave⟩ := first_empty_alignment f d hpending
  have hGeq : G = L.take b.val := by
    have hp := hprefix b.val b.isLt.le
    rw [← ht, ← pastCells_eq_prefixInputs rate rewards C_star C_h z b t ht] at hp
    exact Option.some.inj (hPast.symm.trans hp)
  have hGlen' : G.length = b.val := by change G.length = t.val - s at hGlen; omega
  let Cells := ReferenceFirstWindowNumericalStream.actualLiveSourceCells
    rate z rewards C_star C_h hc (p.T - s) hs
  have hCells : Cells = L.take e := by
    have hh := hsplit u le_rfl hut.le
    have hue : u.val - s = e := by dsimp only [s]; omega
    rw [Nat.sub_self, List.take_zero, List.append_nil, hue, hGeq,
      List.take_take, Nat.min_eq_left he.le] at hh
    exact hh.symm
  have hEL : e ≤ L.length := by
    have hh := congrArg List.length hGeq
    rw [List.length_take, hGlen'] at hh
    omega
  have hepoch := ReferenceCompleteFirstPhaseObservationRecovery.completeSuffixRecords_eq_actualFirstEpoch
    rate rewards C_star C_h z hc
  have hw : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate) z rewards C_star C_h
        hc (p.T - s) hs).records).length = e := by
    rw [← hepoch]
    dsimp only [s] at ht ⊢
    omega
  have hnum := hfinal (by rw [hled]; exact hpending)
  have hbpos : 0 < b.val := by omega
  have hprevIndex : t.val - s - 1 = b.val - 1 := by omega
  rw [hprevIndex] at hrecord
  have hbR : b.val < R.length := b.isLt
  have hprev : R[b.val - 1]'(by omega) = f.record :=
    Option.some.inj ((List.getElem?_eq_getElem (by omega)).symm.trans hrecord)
  have hadj := ReferenceCompleteLaterLiveComplementPrefixReplay.complete_adjacent
    (rate := rate) rewards C_star C_h z (b.val - 1) (by omega)
  have hindex : b.val - 1 + 1 = b.val := by omega
  have hadj' : R[b.val].input.state = (R[b.val - 1]'(by omega)).output.next := by
    simpa only [hindex] using hadj
  obtain ⟨r, hr, _, hfout, _⟩ := f.stream.output_properties f.last
  have hfrecord : r = f.record := Option.some.inj (hr.symm.trans f.recordAt)
  rw [hfrecord, ← f.ledgerIsLast] at hfout
  have hledger : f.ledger = ledger := by
    have hnext := congrArg ReferenceActivePhysicalStep.State.coordinator hadj'
    rw [hprev, hfout] at hnext
    exact (ReferenceActivePhysicalStep.CoordinatorConfiguration.collection.inj
      (hnext.symm.trans hstate)).2.1
  intro i
  have hi := (hnum i).1
  rw [hled, hledger] at hi
  change ledger.cutoffRegisters i = some
    ⟨(QueueReplay.replay (4 * rate.n) (0, 0)
        (ReferenceFirstCollectionAllArmNumericalStream.arrivals rate i Cells)).1,
      (QueueReplay.replay (4 * rate.n) (0, 0)
        (ReferenceFirstCollectionAllArmNumericalStream.arrivals rate i Cells)).2,
      (QueueReplay.replay (4 * rate.n) (0, 0)
        (ReferenceFirstCollectionAllArmNumericalStream.arrivals rate i Cells)).1 -
      (QueueReplay.replay (4 * rate.n) (0, 0)
        (ReferenceFirstCollectionAllArmNumericalStream.arrivals rate i (Cells.take _))).1⟩ at hi
  rw [hw, hCells, List.take_take, Nat.min_eq_left (by omega : e - 1 ≤ e)] at hi
  simpa only [calendarReplay, ReferenceFirstCollectionAllArmNumericalStream.arrivals,
    rawCalendar] using hi


private theorem actual_birth_later_of_pos
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (a : Fin (completeSuffixRecords rate z rewards C_star C_h).length)
    (P : Payload rate)
    (hbirth : InstallationBirth (completeSuffixRecords rate z rewards C_star C_h)[a.val] P)
    (ha : 0 < a.val) :
    laterChosen (completeSuffixRecords rate z rewards C_star C_h)[a.val].input = true := by
  classical
  let R := completeSuffixRecords rate z rewards C_star C_h
  let record := R[a.val]
  change InstallationBirth record P at hbirth
  have hprep : record.output.preparation = prepare record.input := by
    rw [record.output_eq]
    rfl
  cases hcoord : record.output.preparation.coordinator with
  | first outcome =>
      have hactual : record.output.preparation.coordinator = dispatch record.input := by
        rw [record.output_eq]
        rfl
      have hdispatch := hactual.symm.trans hcoord
      have hstate : record.input.state.coordinator = .first := by
        cases hs : record.input.state.coordinator with
        | first => rfl
        | live r q base =>
            simp only [dispatch, hs] at hdispatch
            cases hr : CoordinatorRoundDispatch.dispatch (.live (liveInput record.input r q base));
              simp [hr] at hdispatch
            all_goals cases hdispatch
        | collection payload ledger saved =>
            by_cases hvalid : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
            · let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
              let clock := collectionClock payload ledger saved cutoff
              cases hr : CoordinatorRoundDispatch.dispatch
                  (.collection (collectionInput record.input payload ledger clock cutoff));
                simp [dispatch, hs, hvalid, cutoff, clock, hr] at hdispatch
              all_goals cases hdispatch
            · simp [dispatch, hs, hvalid] at hdispatch
        | dagger => simp [dispatch, hs] at hdispatch
      let j : Fin R.length := ⟨a.val - 1, by have hh := a.isLt; dsimp [R]; omega⟩
      have hnext : j.val + 1 < R.length := by dsimp [j, R]; omega
      have hadj := ReferenceCompleteLaterLiveComplementPrefixReplay.complete_adjacent
        (rate := rate) rewards C_star C_h z j.val hnext
      have hindex : j.val + 1 = a.val := by dsimp [j]; omega
      have hcoordNext := congrArg ReferenceActivePhysicalStep.State.coordinator hadj
      have hprev : R[j.val].output.next.coordinator = .first :=
        hcoordNext.symm.trans (by simpa only [hindex] using hstate)
      exact ((ReferenceCompleteCoordinatorPhaseExhaustion.complete_coordinator_phase_exhaustion
        rate rewards C_star C_h z).1 j).2.2.2.1 hprev |>.elim
  | collection payload ledger clock cutoff outcome =>
      cases outcome with
      | laterChosen core consistent started hstart instruction hassignment output hlocal
          clockData installed selected =>
          unfold laterChosen
          rw [← hprep, hcoord]
      | _ => simp only [InstallationBirth, hcoord] at hbirth
  | _ => simp only [InstallationBirth, hcoord] at hbirth

private theorem calendarReplay_previous_score_le
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (L : List (RecordedQueueRun.RoundInput p.K)) (e : ℕ)
    (he : 0 < e) (heL : e ≤ L.length) (i : Fin p.K) :
    (calendarReplay rate L i (e - 1)).1 ≤ (calendarReplay rate L i e).1 := by
  have hi : e - 1 < L.length := by omega
  have hs : e - 1 + 1 = e := by omega
  have hstep : calendarReplay rate L i e =
      QueueReplay.transition (4 * rate.n) (calendarReplay rate L i (e - 1))
        ((L[e - 1]'hi).enabled, RecordedQueueRun.quantizedArrival
          (ReferenceFirstLaunchNumericalCell.queueParameters rate) (L[e - 1]'hi) i) := by
    unfold calendarReplay
    conv_lhs => rw [← hs]
    rw [← List.take_append_getElem hi, rawCalendar, List.map_append, QueueReplay.replay_append]
    rfl
  rw [hstep]
  cases (L[e - 1]'hi).enabled <;> simp [QueueReplay.transition]

/-- One complete original word restores every installation and episode origin,
the actual predecessor ledger and all three reconstructed weight vectors, and
the literal corrected/renewal raw masses. The final numerical observation is
stopped at its own overflow prefix; the physical replay remains unstopped.
This is an internal deterministic result, with no conditional-law assertion. -/
public theorem complete_original_installation_weight_marginal_restoration
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    let R := completeSuffixRecords rate z rewards C_star C_h
    let s := physicalStart rate z rewards C_star C_h
    let base := AssignmentScoreReconstruction.sourceWeightBase p
    let Q := ReferenceFirstLaunchNumericalCell.queueParameters rate
    match ReferenceCorrectedInitializationLaunch.correctedLaunch rate z rewards C_star C_h with
    | none => R = [] ∧ s = p.T ∧ (∀ n, prefixInputs rate rewards C_star C_h n z = none)
    | some _ => ∃ L : List (RecordedQueueRun.RoundInput p.K),
        L.length = R.length ∧
        (∀ h, h ≤ R.length → prefixInputs rate rewards C_star C_h (s + h) z = some (L.take h)) ∧
        prefixInputs rate rewards C_star C_h p.T z = some L ∧
        (∀ L', prefixInputs rate rewards C_star C_h p.T z = some L' → L' = L) ∧
        (∀ k : Fin R.length, ∀ P : Payload rate, InstallationBirth R[k.val] P →
          ∃ (rho : Fin R.length) (P_rho : Payload rate),
            rho.val ≤ k.val ∧ InstallationBirth R[rho.val] P_rho ∧
            IsEpisodeAnchorBirth R[rho.val] ∧
            installationScoreVector R[k.val] P (fun i => (calendarReplay rate L i k.val).1) ∧
            installationScoreVector R[rho.val] P_rho (fun i => (calendarReplay rate L i rho.val).1) ∧
            P.anchor = P_rho.anchor ∧
            (∀ i, P_rho.anchor i = base ^ (calendarReplay rate L i rho.val).1) ∧
            R[rho.val].input.time = P_rho.sigma ∧ P_rho.sigma.val ≤ P.sigma.val ∧
            FollowerCutoffScan.gridBoundary p rate.eta.val P_rho.sigma =
              FollowerCutoffScan.gridBoundary p rate.eta.val P.sigma ∧
            ∀ i, (calendarReplay rate L i rho.val).1 ≤ (calendarReplay rate L i k.val).1 ∧
              (calendarReplay rate L i k.val).1 ≤ (calendarReplay rate L i rho.val).1 +
                (4 * rate.n) * (P.sigma.val - P_rho.sigma.val)) ∧
        (∀ b : Fin R.length, match (R[b.val]'b.isLt).output.preparation.coordinator with
          | .collection payload ledger clock cutoff
              (.laterChosen core _consistent _started _hstart instruction _hassignment output _hlocal clockData installed _selected) =>
            let operation := CoordinatorRoundDispatch.collectionOperationLedger
              (collectionInput (p := p) (rate := rate) R[b.val].input payload ledger clock cutoff) core.payload_n_eq
            let W := fun h (i : Fin p.K) => base ^ (calendarReplay rate L i h).1
            ∃ (a : Fin R.length) (e : ℕ) (seg : ReferenceCollectionSegmentExtraction.Segment rate),
              a.val < e ∧ e < b.val ∧ InstallationBirth R[a.val] payload ∧
              ReferenceCollectionSegmentExtraction.segmentAt R e = some seg ∧
              b.val = e + seg.records.length ∧ seg.final = ledger ∧ ledger.pending = ∅ ∧
              instruction.time = R[b.val].input.time ∧ ledger.cutoff = s + e + 1 ∧
              (∀ i : Fin p.K, output.reconstruction.registers.cutoff i =
                CoordinatorCollectionLedger.CutoffRegister.mk
                  (calendarReplay rate L i e).1 (calendarReplay rate L i e).2
                  ((calendarReplay rate L i e).1 - (calendarReplay rate L i (e - 1)).1) ∧
                ledger.increment i = (calendarReplay rate L i b.val).1 - (calendarReplay rate L i e).1 ∧
                AssignmentScoreReconstruction.sourceScore output.reconstruction i =
                  (calendarReplay rate L i b.val).1) ∧
              AssignmentScoreReconstruction.currentWeight output.reconstruction = W b.val ∧
              AssignmentScoreReconstruction.cutoffWeight output.reconstruction = W e ∧
              ProductSetLaw.theta p.m (AssignmentScoreReconstruction.currentWeight output.reconstruction) =
                ProductSetLaw.theta p.m (W b.val) ∧
              ProductSetLaw.theta p.m (AssignmentScoreReconstruction.cutoffWeight output.reconstruction) =
                ProductSetLaw.theta p.m (W e) ∧
              LaterAssignmentStartOperation.correctionScale
                (collectionInput (p := p) (rate := rate) R[b.val].input payload ledger clock cutoff).payload
                operation instruction output.cutoffReached =
                  (1 - 4 * (p.m : ℝ) * rate.eta.val) ^ (b.val - e + 1) /
                    (4 * (p.m : ℝ) * rate.eta.val) ∧
              ((instruction.kind = CoordinatorPhaseClock.AssignmentStartKind.corrected ∧ instruction.time.val + 1 < operation.freezeAt ∧
                AssignmentScoreReconstruction.previousWeight output.reconstruction = some (W (e - 1)) ∧
                output.payload.anchor = payload.anchor ∧ installed.registers.payload.anchor = payload.anchor ∧
                (∀ S, output.law.mass S = LaterAssignmentStartOperation.correctedRawMass
                  (collectionInput (p := p) (rate := rate) R[b.val].input payload ledger clock cutoff).payload operation instruction
                  output.reconstruction (W (e - 1)) output.cutoffReached S) ∧
                ∀ S, LaterAssignmentStartOperation.correctedRawMass
                  (collectionInput (p := p) (rate := rate) R[b.val].input payload ledger clock cutoff).payload operation instruction
                  output.reconstruction (W (e - 1)) output.cutoffReached S =
                  LaterAssignmentStartOperation.productQOnPrefixCarrier (W b.val) S +
                    LaterAssignmentStartOperation.correctionScale
                      (collectionInput (p := p) (rate := rate) R[b.val].input payload ledger clock cutoff).payload operation instruction
                      output.cutoffReached *
                    (LaterAssignmentStartOperation.productQOnPrefixCarrier (W e) S -
                      LaterAssignmentStartOperation.productQOnPrefixCarrier (W (e - 1)) S)) ∨
               (instruction.kind = CoordinatorPhaseClock.AssignmentStartKind.renewal ∧ operation.freezeAt ≤ instruction.time.val + 1 ∧
                AssignmentScoreReconstruction.previousWeight output.reconstruction = none ∧
                output.payload.anchor = W b.val ∧ installed.registers.payload.anchor = W b.val ∧
                ∀ S, output.law.mass S = LaterAssignmentStartOperation.productQOnPrefixCarrier (W b.val) S))
          | _ => True) ∧
        (∀ h, h ≤ L.length →
          let cut := min h (UnstoppedRecordedQueueComparison.firstOverflowPrefix Q L)
          (∀ i, (RecordedQueueRun.run Q (L.take h)).registers i = calendarReplay rate L i cut) ∧
          RecordedQueueRun.scoreWeight Q (RecordedQueueRun.run Q (L.take h)) =
            (fun i => base ^ (calendarReplay rate L i cut).1) ∧
          (fun i => RecordedQueueSummation.runMarginal Q p.m L h i) =
            ProductSetLaw.theta p.m (fun i => base ^ (calendarReplay rate L i cut).1) ∧
          prefixReadout rate rewards C_star C_h (s + h) z =
            some (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
              (RecordedQueueRun.run Q (L.take h))) ∧
          (h ≤ UnstoppedRecordedQueueComparison.firstOverflowPrefix Q L →
            RecordedQueueRun.scoreWeight Q (RecordedQueueRun.run Q (L.take h)) =
              (fun i => base ^ (calendarReplay rate L i h).1))) := by
  classical
  dsimp only
  let R := completeSuffixRecords rate z rewards C_star C_h
  let s := physicalStart rate z rewards C_star C_h
  let base := AssignmentScoreReconstruction.sourceWeightBase p
  cases hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch rate z rewards C_star C_h with
  | none =>
      exact Bandits.Support.ReferenceCompleteOriginalCalendarCellPresence.no_launch_complete_original_calendar_cell_presence
        rate rewards C_star C_h z hlaunch
  | some active =>
      have hcells := Bandits.Support.ReferenceCompleteOriginalCalendarCellPresence.complete_original_calendar_cells
        rate rewards C_star C_h z
      simp only [hlaunch] at hcells
      obtain ⟨L, hlen, _hmap, hprefix, _hbranches⟩ := hcells
      have hT : s + R.length = p.T := by
        have hs := physicalStart_le_T rate z rewards C_star C_h
        have hRlen := completeSuffixRecords_length rate z rewards C_star C_h
        dsimp only [s, R]
        omega
      have hterminal : prefixInputs rate rewards C_star C_h p.T z = some L := by
        have hp : prefixInputs rate rewards C_star C_h (s + R.length) z =
            some (L.take R.length) := hprefix R.length le_rfl
        rw [hT, ← hlen, List.take_length] at hp
        exact hp
      refine ⟨L, hlen, hprefix, hterminal,
        fun L' hL' => Option.some.inj (hL'.symm.trans hterminal), ?_, ?_, ?_⟩
      · intro k P hbirth
        obtain ⟨rho, P_rho, z_current, z_origin, hrho, hbirthOrigin,
          hroot, hvectorCurrent, hvectorOrigin, htime, htimeOrder, hanchor,
          hpow, hgrid, hspan⟩ :=
          ReferenceCompleteInstallationEpisodeScoreSpan.actual_installation_episode_score_span
            rate rewards C_star C_h z k P hbirth
        have hcurrent := actual_birth_score_vector rate rewards C_star C_h z L hprefix k P hbirth
        have horigin := actual_birth_score_vector rate rewards C_star C_h z L hprefix rho P_rho hbirthOrigin
        have hcurrentEq := Bandits.Support.ReferenceCompleteEpisodeAnchorOrigin.installationScoreVector_unique
          R[k.val] P z_current (fun i => (calendarReplay rate L i k.val).1) hvectorCurrent hcurrent
        have horiginEq := Bandits.Support.ReferenceCompleteEpisodeAnchorOrigin.installationScoreVector_unique
          R[rho.val] P_rho z_origin (fun i => (calendarReplay rate L i rho.val).1) hvectorOrigin horigin
        refine ⟨rho, P_rho, hrho, hbirthOrigin, hroot, hcurrent, horigin, hanchor,
          ?_, htime, htimeOrder, hgrid, ?_⟩
        · intro i
          rw [hpow i, congrFun horiginEq i]
        · simpa only [hcurrentEq, horiginEq] using hspan
      · intro b
        let record := R[b.val]
        cases hcoord : record.output.preparation.coordinator with
        | collection payload ledger clock cutoff outcome =>
          cases outcome with
          | laterChosen core consistent started hstart instruction hassignment output hlocal
              clockData installed selected =>
            have hprep : record.output.preparation = prepare record.input := by rw [record.output_eq]; rfl
            have hlater : laterChosen record.input = true := by unfold laterChosen; rw [← hprep, hcoord]
            obtain ⟨P0, hP0len, _hP0map, hP0prefix, hinit⟩ :=
              Bandits.Support.ReferenceCompleteInstallationCalendarInitializationInduction.internal_complete_later_installation_calendar_initialization
                rate rewards C_star C_h z b hlater
            have hP0eq : P0 = L.take b.val := by
              have hleft := hP0prefix b.val le_rfl
              have hright := hprefix b.val b.isLt.le
              rw [List.take_of_length_le hP0len.le] at hleft
              exact Option.some.inj (hleft.symm.trans hright)
            rcases hinit with ⟨payload0, ledger0, saved0, cutoff0, hstate0, hpending0, hcutoff0,
              core0, started0, hstart0, instruction0, hassignment0, htime0,
              consistent0, output0, hlocal0, clockData0, installed0, selected0,
              hinstalled0, hsuccess0, hdispatch0, hbranch0, hpayload0, hsigma0,
              hassigned0, hreconstruction0, hsource0, hassignedArms0,
              hcomplement0, hcorrected0, hrenewal0⟩
            have heq := hcoord.symm.trans hbranch0
            cases heq
            have hscore (i : Fin p.K) : AssignmentScoreReconstruction.sourceScore output.reconstruction i =
                (calendarReplay rate L i b.val).1 :=
              (hsource0 i).1.trans (congrArg Prod.fst
                (initializationCalendarReplay_eq_original rate P0 L b.val hP0len hP0eq i))
            obtain ⟨a, r0, q0, beta, e, seg, I, saved, hbefore, hafter,
              hdate, hbirth, hsigma, hnext, hbase, hbetween, hsegment,
              hnonempty, hentry, hchosen, hpayload, hinitializer, hchecked,
              harm, hsigmaI, hcutoffI, hbaseI, hbdate, hprefixR, hdrop,
              hexit, hstate, hstateCoord, hpendingEmpty, hcursor, hfirst⟩ :=
              Bandits.Support.ReferenceCompleteInstallationPredecessorInterval.internal_complete_installation_predecessor_interval
                rate rewards C_star C_h z b hlater
            have hident := ReferenceActivePhysicalStep.CoordinatorConfiguration.collection.inj
              (hstateCoord.symm.trans hstate0)
            have hpay : r0.payload = payload := hident.1
            have hledger : seg.final = ledger := hident.2.1
            have hempty : ledger.pending = ∅ := by rw [← hledger]; exact hpendingEmpty
            have hcut : ∀ i : Fin p.K, ledger.cutoffRegisters i = some
                ⟨(calendarReplay rate L i e).1, (calendarReplay rate L i e).2,
                  (calendarReplay rate L i e).1 - (calendarReplay rate L i (e - 1)).1⟩ := by
              by_cases ha0 : a.val = 0
              · obtain ⟨u, hu, hcell⟩ := hfirst ha0
                exact first_predecessor_cutoff_registers rate rewards C_star C_h z L hprefix
                  b e hafter payload ledger saved0 hstate0 u hu hcell
              · have ha := actual_birth_later_of_pos rate rewards C_star C_h z a r0.payload hbirth
                  (Nat.pos_of_ne_zero ha0)
                have hnum := later_predecessor_final_registers rate rewards C_star C_h z L hprefix
                  a ha e b.val seg hdate hafter b.isLt hsegment hbdate hpendingEmpty
                intro i
                rw [← hledger]
                exact (hnum i).1
            have hreg (i : Fin p.K) : output.reconstruction.registers.cutoff i =
                ⟨(calendarReplay rate L i e).1, (calendarReplay rate L i e).2,
                  (calendarReplay rate L i e).1 - (calendarReplay rate L i (e - 1)).1⟩ := by
              have hh := output.reconstruction.registers.cutoff_eq i
              exact Option.some.inj (hh.symm.trans (hcut i))
            have hinc (i : Fin p.K) : ledger.increment i =
                (calendarReplay rate L i b.val).1 - (calendarReplay rate L i e).1 := by
              have hh := hscore i
              change (output.reconstruction.registers.cutoff i).score + ledger.increment i = _ at hh
              rw [hreg i] at hh
              exact (Nat.add_sub_cancel_left _ _).symm.trans
                (congrArg (fun n : ℕ => n - (calendarReplay rate L i e).1) hh)
            have hweights : AssignmentScoreReconstruction.currentWeight output.reconstruction =
                (fun i => base ^ (calendarReplay rate L i b.val).1) := by
              funext i
              change base ^ AssignmentScoreReconstruction.sourceScore output.reconstruction i = _
              rw [hscore i]
            have hcutweights : AssignmentScoreReconstruction.cutoffWeight output.reconstruction =
                (fun i => base ^ (calendarReplay rate L i e).1) := by
              funext i
              change base ^ (output.reconstruction.registers.cutoff i).score = _
              rw [hreg i]
            have hfold := ReferenceCollectionSegmentExtraction.connected_segment_checked _ _ _ seg
              (ReferenceCollectionSegmentExtraction.connected_drop _ _ _ e
                (completeSuffix_connected_on_launch rate z rewards C_star C_h active hlaunch))
              (ReferenceCollectionSegmentExtraction.segmentAt_branch R e seg hsegment).1
            have hcontext := CollectionBufferProvenance.checkedRounds_success_preserves_context
              seg.context.preLedger seg.final seg.inputs seg.accepted hfold
            have hinitContext := CollectionBufferProvenance.startCollectionChecked_success_context
              I.assignment I.sigma I.cutoff I.freezeAt I.base I.outside seg.context.preLedger hchecked
            have hcutdate : ledger.cutoff = s + e + 1 := by
              rw [← hledger]
              exact (congrArg (fun ctx => ctx.2.2.1) hcontext).trans
                (hinitContext.2.2.2.1.trans hcutoffI)
            have hscale : LaterAssignmentStartOperation.correctionScale
                (collectionInput record.input payload ledger (collectionClock payload ledger saved0 cutoff) cutoff).payload
                (CoordinatorRoundDispatch.collectionOperationLedger
                  (collectionInput record.input payload ledger (collectionClock payload ledger saved0 cutoff) cutoff)
                  core.payload_n_eq) instruction output.cutoffReached =
                    (1 - 4 * (p.m : ℝ) * rate.eta.val) ^ (b.val - e + 1) /
                      (4 * (p.m : ℝ) * rate.eta.val) := by
              unfold LaterAssignmentStartOperation.correctionScale
              have hdiff : instruction.time.val + 1 - ledger.cutoff + 1 = b.val - e + 1 := by
                rw [htime0, hcutdate]
                have hbtime := actual_record_time rate rewards C_star C_h z b
                change record.input.time.val = s + b.val at hbtime
                rw [hbtime]
                omega
              change (1 - 4 * (p.m : ℝ) * rate.eta.val) ^
                (instruction.time.val + 1 - ledger.cutoff + 1) / _ = _
              rw [hdiff]
              rfl
            refine ⟨a, e, seg, hbefore, hafter, hpay ▸ hbirth, hsegment, hbdate,
              hledger, hempty, htime0, hcutdate, fun i => ⟨hreg i, hinc i, hscore i⟩,
              hweights, hcutweights, congrArg (ProductSetLaw.theta p.m) hweights,
              congrArg (ProductSetLaw.theta p.m) hcutweights, hscale, ?_⟩
            rcases CoordinatorRoundDispatch.later_success_kind_cases output clockData with hc | hr
            · obtain ⟨hbefore, previous, hprevious, _hpositive, hanchor, hmass⟩ :=
                LaterAssignmentStartOperation.successful_corrected_law_spec output hc
              have htime : instruction.time.val + 1 <
                  (CoordinatorRoundDispatch.collectionOperationLedger
                    (collectionInput record.input payload ledger (collectionClock payload ledger saved0 cutoff) cutoff) core.payload_n_eq).freezeAt := by
                rw [← output.localConsistency.oldFreezeAt_eq]
                exact hbefore
              have hpw : AssignmentScoreReconstruction.previousWeight output.reconstruction =
                  some (fun i => base ^ (calendarReplay rate L i (e - 1)).1) := by
                have hps := (AssignmentScoreReconstruction.reconstructLaterStart_corrected_equations
                  _ _ output.reconstruction output.reconstruction_eq hc).1
                unfold AssignmentScoreReconstruction.previousWeight
                rw [hps, Option.map_some]
                congr 1
                funext i
                change base ^ ((output.reconstruction.registers.cutoff i).score -
                  (output.reconstruction.registers.cutoff i).lastService) = _
                rw [hreg i]
                change base ^ ((calendarReplay rate L i e).1 -
                    ((calendarReplay rate L i e).1 - (calendarReplay rate L i (e - 1)).1)) = _
                rw [Nat.sub_sub_self (calendarReplay_previous_score_le rate L e
                  (by omega) (by rw [hlen]; omega) i)]
              have hpweq := Option.some.inj (hprevious.symm.trans hpw)
              have hinstalledAnchor : installed.registers.payload.anchor = payload.anchor := by
                rw [hinstalled0]
                exact CoordinatorAssignmentRegisterInstall.later_payload_anchor_corrected output clockData hc
              refine Or.inl ⟨hc, htime, hpw, hanchor, hinstalledAnchor, ?_, ?_⟩
              · intro S
                simpa only [hpweq] using hmass S
              · intro S
                unfold LaterAssignmentStartOperation.correctedRawMass
                rw [hweights, hcutweights]
            · obtain ⟨hafter, hanchor, hmass⟩ :=
                LaterAssignmentStartOperation.successful_renewal_law_spec output hr
              have htime : (CoordinatorRoundDispatch.collectionOperationLedger
                  (collectionInput record.input payload ledger (collectionClock payload ledger saved0 cutoff) cutoff) core.payload_n_eq).freezeAt ≤
                    instruction.time.val + 1 := by
                rw [← output.localConsistency.oldFreezeAt_eq]
                exact hafter
              have hpw := (AssignmentScoreReconstruction.reconstructLaterStart_renewal_equations
                _ _ output.reconstruction output.reconstruction_eq hr).2
              have hinstalledAnchor : installed.registers.payload.anchor =
                  (fun i => base ^ (calendarReplay rate L i b.val).1) := by
                rw [hinstalled0, CoordinatorAssignmentRegisterInstall.later_payload_anchor_renewal output clockData hr,
                  hweights]
              refine Or.inr ⟨hr, htime, hpw, hanchor.trans hweights, hinstalledAnchor, ?_⟩
              intro S
              simpa only [LaterAssignmentStartOperation.renewalRawMass, hweights] using hmass S
          | _ => simp
        | _ => simp
      · intro h hh
        have hregisters (i : Fin p.K) :=
          ((UnstoppedRecordedQueueComparison.prefix_state_comparison
            (ReferenceFirstLaunchNumericalCell.queueParameters rate) L h hh).1 i).trans
              (calendarReplay_eq_unstoppedReplay rate L _ i).symm
        have hweights : RecordedQueueRun.scoreWeight
            (ReferenceFirstLaunchNumericalCell.queueParameters rate)
            (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate) (L.take h)) =
              (fun i => base ^ (calendarReplay rate L i
                (min h (UnstoppedRecordedQueueComparison.firstOverflowPrefix
                  (ReferenceFirstLaunchNumericalCell.queueParameters rate) L))).1) := by
          funext i
          change base ^ ((RecordedQueueRun.run
            (ReferenceFirstLaunchNumericalCell.queueParameters rate) (L.take h)).registers i).1 = _
          rw [hregisters i]
        refine ⟨hregisters, hweights, congrArg (ProductSetLaw.theta p.m) hweights, ?_, ?_⟩
        · unfold prefixReadout
          rw [hprefix h (by rw [← hlen]; exact hh)]
          rfl
        · intro hbefore
          simpa only [Nat.min_eq_left hbefore] using hweights

end Bandits.Support.ReferenceCompleteOriginalCalendarWeightMarginalRestoration

end
