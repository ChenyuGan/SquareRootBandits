/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteOriginalCalendarWeightMarginalRestoration

import Mathlib.Tactic

/-!
# Full-current recording-rate feasibility on the original calendar

Every retained enabled cell uses its actual installed payload and episode
origin in the same complete suffix. Its source grid bounds the elapsed age;
the incoming no-overflow gate identifies the actual anchor with the stopped
prefix. The canonical estimate therefore applies to all current coordinates,
including slow arms, on live, collection, and later-installation dates.
The result is deterministic internal feasibility, with no recording-law or
manuscript-closure assertion.

Source: ZIP4 `04_slow_fast_learner.tex:96-149,245-320` and
`06_interruptions.tex:355-426`.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions
open ReferenceActivePhysicalStep
open ReferenceCompletePhysicalHistory
open ReferenceAssignmentPayloadPersistence
open ReferenceFirstCollectionCurrentRetainedGate
open ReferenceFirstCollectionCorrectedSliceNumericalPrefix
open ReferenceCompleteOriginalCalendarCellPresence
open ReferenceCompleteOriginalCalendarWeightMarginalRestoration
open scoped Classical BigOperators

namespace Bandits.Support.ReferenceCompleteOriginalCalendarRateFeasibility

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev RewardTable := ActualInitializationPhysicalStep.GridRewardTable
abbrev Source := BootstrapPrivateRoundStreams.SourceInput
abbrev Cell := RecordedQueueRun.RoundInput

abbrev Records {p : Parameters} (rate : RateInput p)
    (rewards : RewardTable p) (C_star C_h : ℝ) (z : Source p) :=
  ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h

private theorem marginal_bound_from_actual_episode_envelope
    {p : Parameters} (rate : RateInput p) (past : List (Cell p.K))
    (a : ℕ) (anchor : Fin p.K → ℝ) (c : Cell p.K)
    (ha : a ≤ past.length)
    (hlen : past.length - a ≤ ReplayWeightStability.episodeHorizon rate.eta.val)
    (hanchor : anchor = RecordedQueueRun.scoreWeight
      (ReferenceFirstLaunchNumericalCell.queueParameters rate)
      (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        (past.take a)))
    (hrate : c.rate = CanonicalRecordingRates.xi p rate.eta.val anchor) :
    (∑ i : Fin p.K,
      ProductSetLaw.theta p.m
        (RecordedQueueRun.scoreWeight
          (ReferenceFirstLaunchNumericalCell.queueParameters rate)
          (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate) past)) i /
        c.rate i) ≤ CanonicalRecordingRates.R p := by
  let Q := ReferenceFirstLaunchNumericalCell.queueParameters rate
  have henvelope := RecordedWeightedDrift.actual_anchor_envelope Q past a ha hlen
  have hpositive : ∀ i : Fin p.K, 0 < anchor i := by
    intro i
    rw [hanchor]
    exact (henvelope i).1
  have hbounds : ∀ i : Fin p.K,
      anchor i ≤ RecordedQueueRun.scoreWeight Q (RecordedQueueRun.run Q past) i ∧
      RecordedQueueRun.scoreWeight Q (RecordedQueueRun.run Q past) i ≤ 2 * anchor i := by
    intro i
    rw [hanchor]
    exact ⟨(henvelope i).2.1, le_of_lt (henvelope i).2.2⟩
  have hsum := CanonicalRecordingRates.sum_theta_div_xi_le_R p rate.eta.property
    anchor (RecordedQueueRun.scoreWeight Q (RecordedQueueRun.run Q past))
    hpositive hbounds
  simpa [Q, hanchor, hrate] using hsum

private theorem actual_live_cell_payload_birth
    {p : Parameters} (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (z : Source p)
    (k : Fin (Records rate rewards C_star C_h z).length)
    (c : Cell p.K)
    (hreadout : ReferenceLaterLiveNumericalReadout.laterLiveReadout 0
      (Records rate rewards C_star C_h z)[k.val] = some c) :
    ∃ (payload : Payload rate) (b : Fin (Records rate rewards C_star C_h z).length),
      c.rate = payload.rate ∧ b.val ≤ k.val ∧
        InstallationBirth (Records rate rewards C_star C_h z)[b.val] payload := by
  classical
  let record := (Records rate rewards C_star C_h z)[k.val]
  change ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 record = some c at hreadout
  obtain ⟨_henabled, selected, hselection, _hreward, hrate, _hfloor⟩ :=
    ReferenceLaterLiveNumericalReadout.laterLiveReadout_numerical 0 record c hreadout
  have hlocal := ReferenceSelectedPayloadChronology.actualSelectedPayload_local_stored_or_birth
    record selected hselection
  cases hlocal with
  | inr hbirth =>
      refine ⟨selected.view.payload, k, hrate, le_rfl, ?_⟩
      simpa [record] using hbirth
  | inl hstored =>
      cases hstate : record.input.state.coordinator with
      | first => simp [ReferenceAssignmentPayloadPersistence.storedPayload, hstate] at hstored
      | dagger => simp [ReferenceAssignmentPayloadPersistence.storedPayload, hstate] at hstored
      | live registers owned base =>
          simp [ReferenceAssignmentPayloadPersistence.storedPayload, hstate] at hstored
          have hretained := ReferenceAssignmentRetainedBirthProvenance.complete_coordinator_retained_birth
            rate rewards C_star C_h z k
          dsimp only [Records] at hretained
          rw [hstate] at hretained
          obtain ⟨⟨b, hbk, hbirth, _hbase⟩, _hcutoff⟩ := hretained
          have hpayload : registers.payload = selected.view.payload := hstored
          refine ⟨registers.payload, b, hrate.trans
            (congrArg (fun payload : Payload rate => payload.rate) hpayload.symm),
            hbk.le, ?_⟩
          simpa [record, hpayload] using hbirth
      | collection payload ledger saved =>
          simp [ReferenceAssignmentPayloadPersistence.storedPayload, hstate] at hstored
          have hretained := ReferenceAssignmentRetainedBirthProvenance.complete_coordinator_retained_birth
            rate rewards C_star C_h z k
          dsimp only [Records] at hretained
          rw [hstate] at hretained
          obtain ⟨⟨b, hbk, hbirth, _hbase⟩, _hassignment, _hsigma, _hcutoff⟩ := hretained
          have hpayload : payload = selected.view.payload := hstored
          refine ⟨payload, b, hrate.trans
            (congrArg (fun payload : Payload rate => payload.rate) hpayload.symm),
            hbk.le, ?_⟩
          simpa [record, hpayload] using hbirth

/-- Every present actual live readout on the complete original suffix carries
the canonical rate vector of the selected payload, whose installation is in
that same suffix no later than the readout date. -/
public theorem actual_suffix_live_payload_birth
    {p : Parameters} (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (z : Source p)
    (k : Fin (Records rate rewards C_star C_h z).length) :
    match ReferenceLaterLiveNumericalReadout.laterLiveReadout 0
      (Records rate rewards C_star C_h z)[k.val] with
    | none => True
    | some c =>
        ∃ (payload : Payload rate) (b : Fin (Records rate rewards C_star C_h z).length),
          c.rate = CanonicalRecordingRates.xi p rate.eta.val payload.anchor ∧
          b.val ≤ k.val ∧
          InstallationBirth (Records rate rewards C_star C_h z)[b.val] payload := by
  classical
  cases hreadout : ReferenceLaterLiveNumericalReadout.laterLiveReadout 0
      (Records rate rewards C_star C_h z)[k.val] with
  | none => trivial
  | some c =>
      obtain ⟨payload, b, hrate, hbk, hbirth⟩ :=
        actual_live_cell_payload_birth rate rewards C_star C_h z k c hreadout
      refine ⟨payload, b, ?_, hbk, hbirth⟩
      calc
        c.rate = payload.rate := hrate
        _ = CanonicalRecordingRates.xi p rate.eta.val payload.anchor :=
          by
            funext i
            exact payload.rate_eq_canonical i

/-- The actual selected live payload's immutable anchor is tied to the
episode-anchor installation and original numerical word supplied by the
accepted whole-suffix restoration. -/
public theorem actual_suffix_live_payload_anchor_origin
    {p : Parameters} (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (z : Source p)
    (k : Fin (Records rate rewards C_star C_h z).length) :
    match ReferenceLaterLiveNumericalReadout.laterLiveReadout 0
      (Records rate rewards C_star C_h z)[k.val] with
    | none => True
    | some c =>
        ∃ (L : List (Cell p.K)) (payload : Payload rate)
          (b rho : Fin (Records rate rewards C_star C_h z).length)
          (P_rho : Payload rate),
          c.rate = CanonicalRecordingRates.xi p rate.eta.val payload.anchor ∧
          b.val ≤ k.val ∧
          InstallationBirth (Records rate rewards C_star C_h z)[b.val] payload ∧
          rho.val ≤ b.val ∧
          InstallationBirth (Records rate rewards C_star C_h z)[rho.val] P_rho ∧
          ReferenceCompleteEpisodeAnchorOrigin.IsEpisodeAnchorBirth
            (Records rate rewards C_star C_h z)[rho.val] ∧
          payload.anchor = P_rho.anchor ∧
          (∀ i, P_rho.anchor i =
            AssignmentScoreReconstruction.sourceWeightBase p ^
              (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay
                rate L i rho.val).1) ∧
          (Records rate rewards C_star C_h z)[rho.val].input.time = P_rho.sigma ∧
          P_rho.sigma.val ≤ payload.sigma.val ∧
          FollowerCutoffScan.gridBoundary p rate.eta.val P_rho.sigma =
            FollowerCutoffScan.gridBoundary p rate.eta.val payload.sigma ∧
          (∀ i, (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay
              rate L i rho.val).1 ≤
              (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay
                rate L i b.val).1 ∧
            (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay
              rate L i b.val).1 ≤
              (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay
                rate L i rho.val).1 +
              (4 * rate.n) * (payload.sigma.val - P_rho.sigma.val)) := by
  classical
  cases hreadout : ReferenceLaterLiveNumericalReadout.laterLiveReadout 0
      (Records rate rewards C_star C_h z)[k.val] with
  | none => trivial
  | some c =>
      cases hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
          rate z rewards C_star C_h with
      | none =>
          have hnone := ReferenceCompleteOriginalCalendarCellPresence.no_launch_complete_original_calendar_cell_presence
            rate rewards C_star C_h z hlaunch
          have hlength : (Records rate rewards C_star C_h z).length = 0 := by
            simp [Records, hnone.1]
          have hk0 : k.val < 0 := by
            simpa only [hlength] using k.isLt
          exact False.elim (by omega : False)
      | some active =>
          have hrest :=
            ReferenceCompleteOriginalCalendarWeightMarginalRestoration.complete_original_installation_weight_marginal_restoration
              rate rewards C_star C_h z
          simp only [hlaunch] at hrest
          obtain ⟨L, _hlen, _hprefix, _hterminal, _hunique, hbirths,
            _hcollections, _hqueue⟩ := hrest
          obtain ⟨payload, b, hrate, hbk, hbirth⟩ :=
            actual_live_cell_payload_birth rate rewards C_star C_h z k c hreadout
          have horigin := hbirths b payload hbirth
          obtain ⟨rho, P_rho, hrho, hbirthOrigin, hroot, _hscoreCurrent,
            _hscoreOrigin, hanchor, hpow, htime, htimeOrder, hgrid, hspan⟩ := horigin
          refine ⟨L, payload, b, rho, P_rho, ?_, hbk, hbirth, hrho,
            hbirthOrigin, hroot, hanchor, hpow, htime, htimeOrder, hgrid,
            hspan⟩
          calc
            c.rate = payload.rate := hrate
            _ = CanonicalRecordingRates.xi p rate.eta.val payload.anchor := by
              funext i
              exact payload.rate_eq_canonical i

private theorem complete_suffix_member_clockAt
    {p : Parameters}
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length) :
    let record := (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val]'k.isLt
    ReferenceCoordinatorClockDomains.clockAt record.input.rows record.input.selected
      record.input.time.val record.input.state := by
  classical
  cases hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h with
  | none =>
      have hlength := k.isLt
      simp only [ReferenceCompletePhysicalHistory.completeSuffixRecords,
        hlaunch, dite_true, List.length_nil] at hlength
      omega
  | some active =>
      let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h
      obtain ⟨seed, hseedLaunch, hfirst, _hbank, _hdisabled, _hlearner, _hzero⟩ :=
        ReferenceCorrectedInitializationLaunch.correctedLaunch_coordinator_provenance
          rate source rewards C_star C_h
          ((ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
            rate source rewards C_star C_h).mp (by rw [hlaunch]; rfl))
      have hseedEq : seed = active := Option.some.inj (hseedLaunch.symm.trans hlaunch)
      let start := ReferenceCompletePhysicalHistory.physicalStart
        rate source rewards C_star C_h
      have hspan : start + (p.T - start) ≤ p.T := by
        have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T
          rate source rewards C_star C_h
        omega
      have hmode := ReferenceCompletePhysicalHistory.activeMode_of_launch_eq_some
        rate source rewards C_star C_h active hlaunch
      have hrecords := ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
        rate source rewards C_star C_h active hlaunch
      generalize hR : ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h = records at k ⊢
      rw [hR] at hrecords
      subst records
      have hseedClock : ReferenceCoordinatorClockDomains.clockAt source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) start active := by
        have hcoord : active.coordinator = .first := by
          rw [← hseedEq]
          exact hfirst
        simp [ReferenceCoordinatorClockDomains.clockAt, hcoord]
      have hclock := ReferenceRunClockPreservation.run_clockAt active source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
        start (p.T - start) hspan hmode hseedClock
      have hmember : (ReferenceActivePhysicalHorizon.run active source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
          start (p.T - start) hspan hmode).records[k.val]'k.isLt ∈
            (ReferenceActivePhysicalHorizon.run active source.1.2
              (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
              start (p.T - start) hspan hmode).records :=
        List.getElem_mem k.isLt
      have hrecord := hclock.2.2.2 _ hmember
      dsimp only
      rw [hrecord.2.2.1, hrecord.2.2.2.1]
      exact hrecord.1

private theorem actual_record_time
    {p : Parameters} (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (z : Source p)
    (k : Fin (Records rate rewards C_star C_h z).length) :
    (Records rate rewards C_star C_h z)[k.val].input.time.val =
      physicalStart rate z rewards C_star C_h + k.val := by
  exact ReferenceFirstCollectionRenewalRecordingFeedback.complete_record_time
    rate z rewards C_star C_h k.val _ (List.getElem?_eq_getElem k.isLt)

private theorem cell0_live_rate
    {p : Parameters} {rate : RateInput p}
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r) (base : Fin (p.m - 1) → ℕ)
    (outcome : CoordinatorRoundDispatch.LiveOutcome (liveInput record.input r q base))
    (hcoord : record.output.preparation.coordinator = .live r q base outcome)
    (c : Cell p.K) (hc : cell0 rate record = some c) : c.rate = r.payload.rate := by
  classical
  cases hl : ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 record with
  | some live =>
      have heq : live = c := by simpa [cell0, hl] using hc
      subst live
      obtain ⟨_, selected, hs, _, hr, _⟩ :=
        ReferenceLaterLiveNumericalReadout.laterLiveReadout_numerical 0 record c hl
      have hselected : selected.view.payload = r.payload := by
        cases outcome <;> simp only [hcoord, DispatchCut.selection] at hs
        all_goals try contradiction
        all_goals
          unfold selectionAt at hs
          split at hs
          next ht => cases Option.some.inj hs; rfl
          next ht => contradiction
      exact hr.trans (congrArg (fun P : Payload rate => P.rate) hselected)
  | none =>
      have hcoll : ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 record = some c := by
        simpa [cell0, hl] using hc
      unfold ReferenceLaterCollectionArrivalReadout.laterCollectionReadout at hcoll
      split at hcoll
      next ho =>
        cases outcome <;> simp only [hcoord] at hcoll
        all_goals try contradiction
        split at hcoll
        next hp => cases Option.some.inj hcoll; rfl
        next hp => contradiction
      next ho => contradiction

private theorem cell0_birth_rate
    {p : Parameters} {rate : RateInput p}
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (P : Payload rate) (hb : InstallationBirth record P)
    (c : Cell p.K) (hc : cell0 rate record = some c) : c.rate = P.rate := by
  classical
  cases hl : ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 record with
  | some live =>
      have heq : live = c := by simpa [cell0, hl] using hc
      subst live
      obtain ⟨_, selected, hs, _, hr, _⟩ :=
        ReferenceLaterLiveNumericalReadout.laterLiveReadout_numerical 0 record c hl
      have hselected : selected.view.payload = P := by
        cases hcoord : record.output.preparation.coordinator with
        | first outcome =>
            cases outcome <;> simp only [InstallationBirth, hcoord] at hb
            rcases hb with ⟨rfl, _⟩
            simp only [hcoord, DispatchCut.selection] at hs
            unfold selectionAt at hs
            split at hs
            next ht => cases Option.some.inj hs; rfl
            next ht => contradiction
        | collection old ledger clock cutoff outcome =>
            cases outcome <;> simp only [InstallationBirth, hcoord] at hb
            rcases hb with ⟨rfl, _⟩
            simp only [hcoord, DispatchCut.selection] at hs
            unfold selectionAt at hs
            split at hs
            next ht => cases Option.some.inj hs; rfl
            next ht => contradiction
        | live r q base outcome => simp [InstallationBirth, hcoord] at hb
        | invalidCollectionCutoff => simp [InstallationBirth, hcoord] at hb
        | dagger => simp [InstallationBirth, hcoord] at hb
      exact hr.trans (congrArg (fun P : Payload rate => P.rate) hselected)
  | none =>
      have hcoll : ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 record = some c := by
        simpa [cell0, hl] using hc
      cases hcoord : record.output.preparation.coordinator with
      | first outcome =>
          cases outcome <;> simp_all [InstallationBirth,
            ReferenceLaterCollectionArrivalReadout.laterCollectionReadout]
      | collection old ledger clock cutoff outcome =>
          cases outcome <;> simp_all [InstallationBirth,
            ReferenceLaterCollectionArrivalReadout.laterCollectionReadout]
      | live r q base outcome => simp [InstallationBirth, hcoord] at hb
      | invalidCollectionCutoff => simp [InstallationBirth, hcoord] at hb
      | dagger => simp [InstallationBirth, hcoord] at hb

private theorem cell0_continuing_collection
    {p : Parameters} {rate : RateInput p}
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (P : Payload rate) (ledger : Ledger rate)
    (clock : CoordinatorPhaseClock.ClockRegisters p) (cutoff : Fin p.T)
    (core : CoordinatorRoundDispatch.CollectionCoreValid
      (collectionInput record.input P ledger clock cutoff))
    (snapshot : CoordinatorCollectionInteractive.PreparedSnapshot
      (collectionInput record.input P ledger clock cutoff))
    (boundary : snapshot.clockStarted.clock.g ≤ p.T + 1)
    (scores : CoordinatorRoundDispatch.collectionCurrentScoresCheck
      (collectionInput record.input P ledger clock cutoff) = true)
    (hcoord : record.output.preparation.coordinator =
      .collection P ledger clock cutoff (.continuing core snapshot boundary scores))
    (c : Cell p.K) (hc : cell0 rate record = some c) (he : c.enabled = true) :
    c.rate = P.rate ∧ record.input.time.val + 1 <
      FollowerCutoffScan.gridBoundary p rate.eta.val P.sigma := by
  classical
  have htime := core.clock_start_time_valid
  change CoordinatorPhaseClock.startRoundTimeValid p record.input.time clock at htime
  have hsigma : clock.sigma = some P.sigma := core.clock_sigma_eq
  have hu : clock.u = some cutoff := core.clock_cutoff_eq
  simp only [CoordinatorPhaseClock.startRoundTimeValid, hsigma, hu] at htime
  have hnoLive : ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 record = none := by
    unfold ReferenceLaterLiveNumericalReadout.laterLiveReadout
    simp only [hcoord, DispatchCut.selection]
    have hframe := snapshot.clockStarted_frame.1
    have hnot : ¬ CoordinatorLocalArmChoice.assignmentIsLive P
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p snapshot.clockStarted.clock.u)
        record.input.time := by
      rw [hframe]
      change ¬ CoordinatorLocalArmChoice.assignmentIsLive P
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p clock.u) record.input.time
      rw [hu]
      simp only [CoordinatorLocalArmChoice.assignmentIsLive,
        CoordinatorLocalArmChoice.sourceRound, CoordinatorLocalArmChoice.cutoffRound,
        CoordinatorLiveChoiceRecorderStep.cutoffFromClock, Option.map_some, Option.elim_some]
      omega
    simp only [hnot, and_false, ite_false]
  have hcoll : ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 record = some c := by
    simpa only [cell0, hnoLive, Option.or] using hc
  unfold ReferenceLaterCollectionArrivalReadout.laterCollectionReadout at hcoll
  split at hcoll
  next ho =>
    simp only [hcoord, Option.some.injEq] at hcoll
    have hcrate : c.rate = P.rate := by rw [← hcoll]; rfl
    have hen : (ReferenceLaterCollectionArrivalReadout.continuingCollectionInput
        record P ledger clock cutoff snapshot).enabled = true := by rw [hcoll]; exact he
    have hfreeze : snapshot.clockStarted.clock.g =
        FollowerCutoffScan.gridBoundary p rate.eta.val P.sigma := by
      rw [snapshot.clockStarted_frame.1]
      change clock.g = _
      have hg := core.clock_registers_valid.1
      change clock.g = CoordinatorPhaseClock.boundaryFromSigma p rate.eta.val clock.sigma at hg
      simpa only [hsigma, CoordinatorPhaseClock.boundaryFromSigma] using hg
    have heq : (ReferenceLaterCollectionArrivalReadout.continuingCollectionInput
        record P ledger clock cutoff snapshot).enabled =
        decide (record.input.time.val + 1 < snapshot.clockStarted.clock.g) := by
      simp only [ReferenceLaterCollectionArrivalReadout.continuingCollectionInput,
        CoordinatorRecordingOperation.isFrozen, CoordinatorRecorderComplementBridge.recorderInput,
        CoordinatorRecorderComplementBridge.recorderInputWithWeights, collectionRecordingInput,
        CoordinatorRecorderComplementBridge.sourceStart, CoordinatorRecordingOperation.sourceCalendarRound,
        Nat.succ_pos, true_and, not_le]
    exact ⟨hcrate, by rw [heq, hfreeze] at hen; exact of_decide_eq_true hen⟩
  next ho => contradiction

private theorem cell0_live_enabled_before_grid
    {p : Parameters} {rate : RateInput p}
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r) (base : Fin (p.m - 1) → ℕ)
    (outcome : CoordinatorRoundDispatch.LiveOutcome (liveInput record.input r q base))
    (hcoord : record.output.preparation.coordinator = .live r q base outcome)
    (hvalid : CoordinatorPhaseClock.clockRegistersValid p rate.eta.val r.priorClock)
    (hsigma : r.priorClock.sigma = some r.payload.sigma)
    (hu : r.priorClock.u = none) (hgrid : r.gridBoundary = r.priorClock.g)
    (hstart : r.payload.sigma.val < record.input.time.val)
    (hbefore : record.input.time.val < r.gridBoundary)
    (c : Cell p.K) (hc : cell0 rate record = some c) (he : c.enabled = true) :
    record.input.time.val + 1 < r.gridBoundary := by
  classical
  by_contra hn
  have heq : FollowerCutoffScan.calendarRound record.input.time = r.priorClock.g := by
    simp only [FollowerCutoffScan.calendarRound]
    omega
  have htime : CoordinatorPhaseClock.startRoundTimeValid p record.input.time r.priorClock := by
    simp only [CoordinatorPhaseClock.startRoundTimeValid, hsigma, hu]
    exact ⟨hstart, heq.le⟩
  obtain ⟨result, hresult, hframe, _hpending, _hcommand, _hassignment⟩ :=
    CoordinatorPhaseClock.startRound_grid_cutoff p rate.eta.val record.input.time r.payload.sigma
      r.priorClock r.clockPending (ReferenceCoordinatorClockDomains.proposalParameterValid_of_rate rate)
      hvalid htime hsigma hu heq
  have started_frame (started : CoordinatorPhaseClock.StartRoundResult p)
      (hcall : CoordinatorPhaseClock.startRound p rate.eta.val record.input.time
        r.priorClock r.clockPending = .ok started) :
      started.clock.u = some record.input.time ∧ started.clock.g = r.gridBoundary := by
    have hr : started = result := Except.ok.inj (hcall.symm.trans hresult)
    rw [hr, hframe]
    exact ⟨rfl, hgrid.symm⟩
  cases outcome
  case continuingChosen dispatched hcall continuation selected =>
    have hframe := started_frame dispatched.startResult hcall
    have hnoLive : ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 record = none := by
      cases hl : ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 record with
      | none => rfl
      | some live =>
          obtain ⟨v, _ho, hs, _hpos, hlive, _hcell⟩ :=
            ReferenceLaterLiveNumericalReadout.laterLiveReadout_some 0 record live hl
          simp only [hcoord, DispatchCut.selection] at hs
          unfold selectionAt at hs
          split at hs
          next ht =>
            cases Option.some.inj hs
            change CoordinatorLocalArmChoice.assignmentIsLive r.payload
              (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p dispatched.startResult.clock.u)
              record.input.time at hlive
            rw [hframe.1] at hlive
            simp [CoordinatorLocalArmChoice.assignmentIsLive, CoordinatorLocalArmChoice.sourceRound,
              CoordinatorLocalArmChoice.cutoffRound, CoordinatorLiveChoiceRecorderStep.cutoffFromClock] at hlive
          next ht => contradiction
    simp [cell0, hnoLive, ReferenceLaterCollectionArrivalReadout.laterCollectionReadout,
      hcoord] at hc
  case cutoffChosen dispatched hcall ledger hinit hcand hdomain hclock hpending hnone selected =>
    have hframe := started_frame dispatched.startResult hcall
    have hnoLive : ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 record = none := by
      cases hl : ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 record with
      | none => rfl
      | some live =>
          obtain ⟨v, _ho, hs, _hpos, hlive, _hcell⟩ :=
            ReferenceLaterLiveNumericalReadout.laterLiveReadout_some 0 record live hl
          simp only [hcoord, DispatchCut.selection] at hs
          unfold selectionAt at hs
          split at hs
          next ht =>
            cases Option.some.inj hs
            change CoordinatorLocalArmChoice.assignmentIsLive r.payload
              (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p dispatched.startResult.clock.u)
              record.input.time at hlive
            rw [hframe.1] at hlive
            simp [CoordinatorLocalArmChoice.assignmentIsLive, CoordinatorLocalArmChoice.sourceRound,
              CoordinatorLocalArmChoice.cutoffRound, CoordinatorLiveChoiceRecorderStep.cutoffFromClock] at hlive
          next ht => contradiction
    have hcoll : ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 record = some c := by
      simpa only [cell0, hnoLive, Option.or] using hc
    unfold ReferenceLaterCollectionArrivalReadout.laterCollectionReadout at hcoll
    split at hcoll
    next ho =>
      simp only [hcoord] at hcoll
      split at hcoll
      next hpos =>
        cases Option.some.inj hcoll
        have hdisabled : (ReferenceLaterCollectionArrivalReadout.laterCutoffCollectionInput
            record r q base dispatched selected).enabled = false := by
          simp only [ReferenceLaterCollectionArrivalReadout.laterCutoffCollectionInput,
            CoordinatorRecordingOperation.isFrozen, CoordinatorRecorderComplementBridge.recorderInput,
            CoordinatorRecorderComplementBridge.recorderInputWithWeights, collectionRecordingInput,
            CoordinatorRecorderComplementBridge.sourceStart, CoordinatorRecordingOperation.sourceCalendarRound]
          have hle : dispatched.startResult.clock.g ≤ record.input.time.val + 1 := by
            rw [hframe.2, hgrid, ← heq]
            rfl
          simp only [Nat.succ_pos, true_and, hle, not_true_eq_false, decide_false]
        rw [hdisabled] at he
        contradiction
      next hpos => contradiction
    next ho => contradiction
  all_goals
    simp [cell0, ReferenceLaterLiveNumericalReadout.laterLiveReadout,
      ReferenceLaterCollectionArrivalReadout.laterCollectionReadout,
      hcoord, DispatchCut.selection] at hc

private theorem actual_enabled_cell_payload_birth
    {p : Parameters} (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (z : Source p)
    (k : Fin (Records rate rewards C_star C_h z).length)
    (c : Cell p.K) (hc : cell0 rate (Records rate rewards C_star C_h z)[k.val] = some c)
    (he : c.enabled = true) :
    ∃ (P : Payload rate) (b : Fin (Records rate rewards C_star C_h z).length),
      c.rate = P.rate ∧ b.val ≤ k.val ∧
      InstallationBirth (Records rate rewards C_star C_h z)[b.val] P ∧
      (Records rate rewards C_star C_h z)[k.val].input.time.val + 1 <
        FollowerCutoffScan.gridBoundary p rate.eta.val P.sigma := by
  classical
  let record := (Records rate rewards C_star C_h z)[k.val]
  change cell0 rate record = some c at hc
  have hprep : record.output.preparation.coordinator = dispatch record.input := by
    rw [record.output_eq]
    rfl
  have hclock := complete_suffix_member_clockAt rate rewards C_star C_h z k
  change ReferenceCoordinatorClockDomains.clockAt record.input.rows record.input.selected
    record.input.time.val record.input.state at hclock
  have hretained := ReferenceAssignmentRetainedBirthProvenance.complete_coordinator_retained_birth
    rate rewards C_star C_h z k
  change match record.input.state.coordinator with
    | .live r _ beta => _
    | .collection P l _ => _
    | .first => True
    | .dagger => True at hretained
  cases hstate : record.input.state.coordinator with
  | dagger =>
      have hcoord : record.output.preparation.coordinator = .dagger := by
        rw [hprep]; simp only [dispatch, hstate]
      simp [cell0, ReferenceLaterLiveNumericalReadout.laterLiveReadout,
        ReferenceLaterCollectionArrivalReadout.laterCollectionReadout,
        hcoord, DispatchCut.selection] at hc
  | first =>
      have hfirstCoord : record.output.preparation.coordinator = .first
          (CoordinatorRoundDispatch.dispatchFirst (firstInput record.input)) := by
        rw [hprep]; simp only [dispatch, hstate, CoordinatorRoundDispatch.dispatch]; rfl
      cases hd : CoordinatorRoundDispatch.dispatchFirst (firstInput record.input) with
      | chosen installed selected =>
          have hcoord : record.output.preparation.coordinator = .first (.chosen installed selected) := by
            rw [hprep]; simp only [dispatch, hstate, CoordinatorRoundDispatch.dispatch, hd]; rfl
          have hb : InstallationBirth record installed.registers.payload := by
            simp only [InstallationBirth, hcoord]
            exact ⟨rfl, firstChosen_payload_time record.input installed selected hd⟩
          refine ⟨installed.registers.payload, k,
            cell0_birth_rate record _ hb c hc, le_rfl, hb, ?_⟩
          have ht := ReferenceAssignmentPayloadChronology.installationBirth_time_eq record _ hb
          have hg := FollowerCutoffScan.gridBoundary_bounds p rate.eta.val
            rate.eta.property rate.sourceCap installed.registers.payload.sigma
          change record.input.time.val + 1 < _
          omega
      | choiceDomainFailure installed | recorderBoundaryFailure installed | choiceRejected installed =>
          have hcoord := hfirstCoord
          rw [hd] at hcoord
          simp [cell0, ReferenceLaterLiveNumericalReadout.laterLiveReadout,
            ReferenceLaterCollectionArrivalReadout.laterCollectionReadout,
            hcoord, DispatchCut.selection] at hc
  | live r q base =>
      let outcome := CoordinatorRoundDispatch.dispatchLive (liveInput record.input r q base)
      have hcoord : record.output.preparation.coordinator = .live r q base outcome := by
        rw [hprep]; simp only [dispatch, hstate, CoordinatorRoundDispatch.dispatch]; rfl
      simp only [ReferenceCoordinatorClockDomains.clockAt, hstate] at hclock
      simp only [hstate] at hretained
      obtain ⟨⟨b, hbk, hb, _⟩, _⟩ := hretained
      obtain ⟨_, hvalid, hsigma, hu, hgrid, hstart, hbefore, _⟩ := hclock
      have hg : r.gridBoundary = FollowerCutoffScan.gridBoundary p rate.eta.val r.payload.sigma := by
        rw [hgrid, hvalid.1, hsigma]
        rfl
      refine ⟨r.payload, b, cell0_live_rate record r q base outcome hcoord c hc,
        hbk.le, hb, ?_⟩
      have hstrict := cell0_live_enabled_before_grid record r q base outcome hcoord
        hvalid hsigma hu hgrid hstart hbefore c hc he
      rw [hg] at hstrict
      exact hstrict
  | collection P ledger saved =>
      simp only [ReferenceCoordinatorClockDomains.clockAt, hstate] at hclock
      obtain ⟨_, _, hpositive, hbound, _, _hfreeze, _, _⟩ := hclock
      have hvalid : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T := ⟨hpositive, hbound⟩
      let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
      let clock := collectionClock P ledger saved cutoff
      have hcoord : record.output.preparation.coordinator = .collection P ledger clock cutoff
          (CoordinatorRoundDispatch.dispatchCollection (collectionInput record.input P ledger clock cutoff)) := by
        rw [hprep]
        simp only [dispatch, hstate, dite_eq_left hvalid, CoordinatorRoundDispatch.dispatch]
        rfl
      cases hd : CoordinatorRoundDispatch.dispatchCollection
          (collectionInput record.input P ledger clock cutoff)
      case continuing core snapshot boundary scores =>
          rw [hd] at hcoord
          have hcell := cell0_continuing_collection record P ledger clock cutoff
            core snapshot boundary scores hcoord c hc he
          simp only [hstate] at hretained
          obtain ⟨⟨b, hbk, hb, _⟩, _, _, _⟩ := hretained
          exact ⟨P, b, hcell.1, hbk.le, hb, hcell.2⟩
      case laterChosen core consistent started hstart instruction hinstruction output hlocal clockData installed selected =>
          rw [hd] at hcoord
          have hcut : (prepare record.input).coordinator = .collection P ledger clock cutoff
              (.laterChosen core consistent started hstart instruction hinstruction output hlocal clockData installed selected) := by
            change dispatch record.input = _
            exact hprep.symm.trans hcoord
          have hinstalled := ReferenceInstalledClockPreservation.step_clockAt_laterChosen
            record.input P ledger clock cutoff core consistent started hstart instruction
            hinstruction output hlocal clockData installed selected hcut
          have ht := congrArg Fin.val hinstalled.1
          have hb : InstallationBirth record installed.registers.payload := by
            simp only [InstallationBirth, hcoord]
            exact ⟨rfl, ht⟩
          have hg := FollowerCutoffScan.gridBoundary_bounds p rate.eta.val
            rate.eta.property rate.sourceCap installed.registers.payload.sigma
          refine ⟨installed.registers.payload, k, cell0_birth_rate record _ hb c hc,
            le_rfl, hb, ?_⟩
          change record.input.time.val + 1 < _
          omega
      all_goals
        rw [hd] at hcoord
        simp [cell0, ReferenceLaterLiveNumericalReadout.laterLiveReadout,
          ReferenceLaterCollectionArrivalReadout.laterCollectionReadout,
          hcoord, DispatchCut.selection] at hc

private theorem grid_span_le_episode_horizon
    {p : Parameters} (rate : RateInput p) (sigma : Fin p.T) :
    FollowerCutoffScan.gridBoundary p rate.eta.val sigma - (sigma.val + 1) ≤
      ReplayWeightStability.episodeHorizon rate.eta.val := by
  let H := ReplayWeightStability.episodeHorizon rate.eta.val
  have hH : 0 < H := FollowerCutoffScan.episodeHorizon_pos_of_source_cap
    p rate.eta.val rate.eta.property rate.sourceCap
  have hrem : (sigma.val + 1) % H < H := Nat.mod_lt _ hH
  have hdiv := Nat.mod_add_div (sigma.val + 1) H
  have hgrid : FollowerCutoffScan.gridBoundary p rate.eta.val sigma ≤
      H * ((sigma.val + 1) / H + 1) := Nat.min_le_right _ _
  rw [Nat.mul_add, Nat.mul_one] at hgrid
  change _ ≤ H
  omega

private theorem actual_suffix_enabled_marginal_bound
    {p : Parameters} (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (z : Source p)
    (k : Fin (Records rate rewards C_star C_h z).length)
    (past : List (Cell p.K))
    (hpast : prefixInputs rate rewards C_star C_h
      (physicalStart rate z rewards C_star C_h + k.val) z = some past)
    (c : Cell p.K) (hc : cell0 rate (Records rate rewards C_star C_h z)[k.val] = some c)
    (he : c.enabled = true)
    (hstop : (RecordedQueueRun.run
      (ReferenceFirstLaunchNumericalCell.queueParameters rate) past).overflow = false) :
    (∑ i : Fin p.K, ProductSetLaw.theta p.m
      (RecordedQueueRun.scoreWeight (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate) past)) i /
      c.rate i) ≤ CanonicalRecordingRates.R p := by
  classical
  cases hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h with
  | none =>
      have hnone := no_launch_complete_original_calendar_cell_presence
        rate rewards C_star C_h z hlaunch
      have hk := k.isLt
      simp only [Records, hnone.1, List.length_nil] at hk
      omega
  | some active =>
      have hrest := complete_original_installation_weight_marginal_restoration
        rate rewards C_star C_h z
      simp only [hlaunch] at hrest
      obtain ⟨L, hlen, hprefix, _hterminal, _hunique, hbirths, _hcollections, hqueue⟩ := hrest
      have hkL : k.val ≤ L.length := by rw [hlen]; exact k.isLt.le
      have hpasteq : past = L.take k.val := by
        exact Option.some.inj (hpast.symm.trans (hprefix k.val k.isLt.le))
      subst past
      obtain ⟨P, b, hrate, hbk, hbirth, hbefore⟩ :=
        actual_enabled_cell_payload_birth rate rewards C_star C_h z k c hc he
      obtain ⟨rho, P_rho, hrho, _hbirthOrigin, _hroot, _hscoreCurrent, _hscoreOrigin,
        hanchor, hpow, htimeOrigin, _htimeOrder, hgrid, _hspan⟩ := hbirths b P hbirth
      have hrhok : rho.val ≤ k.val := hrho.trans hbk
      have hrhoL : rho.val ≤ L.length := hrhok.trans hkL
      have hcut : k.val < UnstoppedRecordedQueueComparison.firstOverflowPrefix
          (ReferenceFirstLaunchNumericalCell.queueParameters rate) L := by
        have hiff := UnstoppedRecordedQueueComparison.prefix_overflow_iff_first_overflow_prefix_le
          (ReferenceFirstLaunchNumericalCell.queueParameters rate) L k.val hkL
        by_contra hnot
        have hover := hiff.mpr (Nat.le_of_not_gt hnot)
        rw [hstop] at hover
        contradiction
      have huncut := (hqueue rho.val hrhoL).2.2.2.2 (hrhok.trans hcut.le)
      have hactualAnchor : P.anchor = RecordedQueueRun.scoreWeight
          (ReferenceFirstLaunchNumericalCell.queueParameters rate)
          (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)
            ((L.take k.val).take rho.val)) := by
        rw [List.take_take, Nat.min_eq_left hrhok, huncut, hanchor]
        funext i
        exact hpow i
      have htimeCurrent := actual_record_time rate rewards C_star C_h z k
      have htimeRoot := actual_record_time rate rewards C_star C_h z rho
      have hrootTime : P_rho.sigma.val = physicalStart rate z rewards C_star C_h + rho.val :=
        (congrArg Fin.val htimeOrigin).symm.trans htimeRoot
      rw [← hgrid] at hbefore
      have horiginBefore : P_rho.sigma.val ≤
          (Records rate rewards C_star C_h z)[k.val].input.time.val := by
        rw [hrootTime, htimeCurrent]
        omega
      have hdateGrid := ReferenceCompleteEpisodeAnchorOrigin.gridBoundary_eq_of_before
        rate P_rho.sigma (Records rate rewards C_star C_h z)[k.val].input.time
        horiginBefore hbefore
      have hspan : FollowerCutoffScan.gridBoundary p rate.eta.val
          (Records rate rewards C_star C_h z)[k.val].input.time - (P_rho.sigma.val + 1) ≤
          ReplayWeightStability.episodeHorizon rate.eta.val := by
        rw [hdateGrid]
        exact grid_span_le_episode_horizon rate P_rho.sigma
      have hbeforeCurrent : (Records rate rewards C_star C_h z)[k.val].input.time.val + 1 <
          FollowerCutoffScan.gridBoundary p rate.eta.val
            (Records rate rewards C_star C_h z)[k.val].input.time := by
        rw [hdateGrid]
        exact hbefore
      have hage : k.val - rho.val ≤ ReplayWeightStability.episodeHorizon rate.eta.val := by
        rw [htimeCurrent] at hbeforeCurrent
        rw [hrootTime] at hspan
        omega
      have hlength : (L.take k.val).length = k.val := List.length_take_of_le hkL
      apply marginal_bound_from_actual_episode_envelope rate (L.take k.val) rho.val P.anchor c
      · rw [hlength]; exact hrhok
      · rw [hlength]; exact hage
      · exact hactualAnchor
      · calc
          c.rate = P.rate := hrate
          _ = CanonicalRecordingRates.xi p rate.eta.val P.anchor := by
            funext i
            exact P.rate_eq_canonical i

/-- At every original calendar coordinate, an enabled actual cell with a
present incoming numerical prefix and no earlier overflow satisfies the
canonical recording-rate bound for the full current marginal vector. The
update detecting the first overflow is retained by the incoming flag test.
Absent prefixes and cells remain absent. This is deterministic internal
feasibility and does not assert a recording law or manuscript closure. -/
public theorem actual_original_calendar_rate_feasibility
    {p : Parameters} (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (z : Source p) (q : Fin p.T) :
    match prefixInputs rate rewards C_star C_h q.val z with
    | none => True
    | some past =>
      match ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h q z with
      | none => True
      | some record =>
        match cell0 rate record with
        | none => True
        | some c => c.enabled = true →
          (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate) past).overflow = false →
          (∑ i : Fin p.K, ProductSetLaw.theta p.m
            (RecordedQueueRun.scoreWeight (ReferenceFirstLaunchNumericalCell.queueParameters rate)
              (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate) past)) i /
            c.rate i) ≤ CanonicalRecordingRates.R p := by
  classical
  cases hpast : prefixInputs rate rewards C_star C_h q.val z with
  | none => trivial
  | some past =>
      dsimp only
      have hby := prefixInputs_launch rate rewards C_star C_h q.val z past hpast
      have hs := hby.2
      have hlen := completeSuffixRecords_length rate z rewards C_star C_h
      let k : Fin (Records rate rewards C_star C_h z).length :=
        ⟨q.val - physicalStart rate z rewards C_star C_h, by dsimp only [Records]; omega⟩
      have hq : physicalStart rate z rewards C_star C_h + k.val = q.val := by
        dsimp only [k]; omega
      have hrecord : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h q z =
          some (Records rate rewards C_star C_h z)[k.val] := by
        simp only [ReferenceSourcePrefixHistoryFiltration.actualRecord, ite_eq_left hs]
        exact List.getElem?_eq_getElem k.isLt
      rw [hrecord]
      dsimp only
      cases hc : cell0 rate (Records rate rewards C_star C_h z)[k.val] with
      | none => trivial
      | some c =>
          dsimp only
          intro he hstop
          apply actual_suffix_enabled_marginal_bound rate rewards C_star C_h z k past
            (by rw [hq]; exact hpast) c hc he hstop

end Bandits.Support.ReferenceCompleteOriginalCalendarRateFeasibility

end
