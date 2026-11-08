/-
Copyright (c) 2026 The Bandits Lean regret formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveSourceReleaseSupport

/-!
# Actual first-live physical sentinel charge

The signed one-round release charge is from
`sources/zip4/manuscript/05_binary_transport.tex:293-325`, and its transfer
use is in `sources/zip4/manuscript/06_interruptions.tex:452-492`. This module
proves that deterministic charge on queried records of the original corrected
source run at a true first-live release gate. It does not prove the stopped
release-cost expectation or a source-stopped endpoint theorem.
-/

@[expose] public section

open scoped BigOperators

namespace Bandits.Support.ReferenceFirstLivePhysicalSentinelCost

open Bandits.Support.ActiveRoundActions
open Bandits.Support.ConstructorDimensions
open Bandits.Support.PublicDiscreteDraws
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceFirstLiveConfirmationHistory
open Bandits.Support.ReferenceFirstLiveReleaseGeometry
open Bandits.Support.ReferenceFirstLiveSourceReleaseSupport
open Bandits.Support.ReferenceLocalReleaseGateChronology
open Bandits.Support.ReferencePhysicalReleaseQuota
open Bandits.Support.ReferenceRetainedReleasePhaseObservation
open Bandits.Support.ReleaseRoundKernel

/-- The signed release deficit on every queried actual first-live gate record
is bounded by the sum of pending assigned-arm indicators and the separate
auxiliary-arm collision charge. The whole original reward row and the record's
actual own observations are retained.

Source: `sources/zip4/manuscript/05_binary_transport.tex:293-325` and
`sources/zip4/manuscript/06_interruptions.tex:452-492`.
-/
theorem actual_first_live_gate_sentinel_cost_bound
    {p : ConstructorDimensions.Parameters}
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (count : ℕ) :
    let I := ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
    let s := ReferenceInitializationRun.elapsed p I.completed
    (hcross : I.crossing.isSome = true) →
    (hspan : s + count ≤ p.T) →
    let R := ReferenceLocalReleaseGateChronology.sourceRun
      rate source rewards C_star C_h hcross s count rfl hspan
    (k : Fin count) →
    let r := R.records[k.val]'(by
      simpa only [R, ReferenceLocalReleaseGateChronology.sourceRun,
        ReferenceActivePhysicalHorizon.run_record_count] using k.isLt)
    ReferenceRetainedReleasePhaseObservation.localReleaseGate
      rate s r.input.time
      (ReferenceActivePhysicalStepMeasurability.encodeState r.input.state) = true →
    ∃ selected : ReferenceActivePhysicalStep.Selection (p := p) (rate := rate) r.input,
      r.output.preparation.coordinator.selection = some selected ∧
      ReferenceAssignmentPayloadPersistence.storedPayload r.input.state.coordinator =
        some selected.view.payload ∧
      selected.view.pendingAtChoice = (∅ : Finset (ActiveRoundActions.Follower p.m)) ∧
      let M := selected.view.payload
      ReleaseRoundKernel.slowReward
          (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow r.input.rewards r.input.time)
          M.slowSet +
        (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow r.input.rewards r.input.time).val
          selected.arm -
        (∑ player : Fin p.m, ((r.ownEntries player).2).val.val) ≤
        (∑ i ∈ ReferencePhysicalReleaseQuota.pendingSet M r,
          ReleaseRoundKernel.chi
            (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow r.input.rewards r.input.time)
            (M.assignment.assigned i)) +
        (if selected.arm = M.assignment.auxiliary ∧
            (ReferencePhysicalReleaseQuota.pendingSet M r).Nonempty then
          (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow r.input.rewards r.input.time).val
            M.assignment.auxiliary
        else 0) := by
  intro I s hcross hspan R k r hgate
  classical
  obtain ⟨selected, hselected, payload, hpayload, hempty, _hsigma⟩ :=
    ReferenceFirstLiveSourceReleaseSupport.actual_first_live_gate_selected_empty
      source rewards C_star C_h count hspan hcross k hgate
  have hindex :=
    ReferenceFirstLiveSourceReleaseSupport.actual_first_live_gate_in_window
      source rewards C_star C_h count hspan hcross k hgate
  have hbound : k.val < R.records.length := by
    simpa only [R, ReferenceLocalReleaseGateChronology.sourceRun,
      ReferenceActivePhysicalHorizon.run_record_count] using k.isLt
  have hprojection :=
    ReferenceFirstLiveReleaseGeometry.original_source_first_live_release_projection
      source rewards C_star C_h hcross s count rfl hspan
  obtain ⟨initial, seed, memory, hmode, hlaunch, hfirst, hseed, hS, hdelta,
      hbacklog, hnone, haccepted, hunoccupied, hbuffer, hpair, htime, hbatch,
      hsourceProofs⟩ := hprojection
  have hseedLaunch :=
    ReferenceLocalReleaseGateChronology.sourceSeed_launch rate source rewards C_star C_h hcross
  have hinitial : initial =
      ReferenceLocalReleaseGateChronology.sourceSeed rate source rewards C_star C_h hcross :=
    Option.some.inj (hlaunch.symm.trans hseedLaunch)
  subst initial
  rcases hsourceProofs with ⟨hselectors, _hterminal⟩
  let E := ReferenceActivePhysicalHorizon.run
    (ReferenceLocalReleaseGateChronology.sourceSeed rate source rewards C_star C_h hcross)
    source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
    rewards s count hspan hmode
  let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records
  have hrecordsEq : E.records = R.records := by
    dsimp only [E, R, ReferenceLocalReleaseGateChronology.sourceRun]
  have hindexR : k.val <
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R.records).length := by
    simpa only [I, s, R] using hindex
  have hW : k.val < W.length := by
    change k.val < (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length
    rw [hrecordsEq]
    exact hindexR
  have hboundE : k.val < E.records.length := by
    rw [hrecordsEq]
    exact hbound
  have hwindowPrefix : W.IsPrefix E.records := by
    simp only [W, ReferenceFirstLiveConfirmationHistory.firstLiveWindow]
    exact List.takeWhile_prefix _
  let hkWindow : Fin (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length :=
    ⟨k.val, by simpa only [W] using hW⟩
  let w := W[↑hkWindow]
  have hrecordEq : E.records[k.val]'hboundE = R.records[k.val]'hbound := by
    exact getElem_congr_coll (c := E.records) (d := R.records) (i := k.val)
      (w := hboundE) hrecordsEq
  have hwr : w = r := by
    calc
      w = E.records[↑hkWindow]'hboundE := hwindowPrefix.getElem hkWindow.isLt
      _ = R.records[k.val]'hbound := hrecordEq
      _ = r := by rfl
  have hselectionOnWindow :
      ∃ selectedWindow : ReferenceActivePhysicalStep.Selection w.input,
        w.output.preparation.coordinator.selection = some selectedWindow ∧
          selectedWindow.view.pendingAtChoice = ∅ := by
    exact hwr.symm ▸ ⟨selected, hselected, hempty⟩
  obtain ⟨selectedWindow, hselectedWindow, hemptyWindow⟩ := hselectionOnWindow
  obtain ⟨hvalid, states, memories, hprepared, hfields, hgeometry⟩ :=
    hselectors hkWindow selectedWindow hselectedWindow hemptyWindow
  obtain ⟨input, _hinput, hfast, _hfastOutside, _hactions, hfeedback, _hup, _hdata⟩ := hgeometry
  have hgateWindow :
      ReferenceRetainedReleasePhaseObservation.localReleaseGate rate s w.input.time
        (ReferenceActivePhysicalStepMeasurability.encodeState w.input.state) = true := by
    simpa only [hwr.symm] using hgate
  obtain ⟨gateRegs, gateOwned, gateBase, hgateLive, _hbirth, hgatePending,
      _hgateClock, _hgateClockU⟩ :=
    ReferenceLocalReleaseGateChronology.gate_live s w.input.time w.input.state hgateWindow
  have hgateLiveWindow :
      (W[↑hkWindow]).input.state.coordinator =
        CoordinatorConfiguration.live gateRegs gateOwned gateBase := by
    simpa only [w] using hgateLive
  obtain ⟨liveRegs, liveOwned, liveBase, hliveState, _hclockTime, _hpriorU,
      _hlivePending, _hnoCut, _hlive, _hvalidLive⟩ :=
    ReferenceFirstLiveReleaseGeometry.first_live_actual_choice_data
      (ReferenceLocalReleaseGateChronology.sourceSeed rate source rewards C_star C_h hcross)
      source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
      s count hspan hmode hfirst hkWindow selectedWindow hselectedWindow hemptyWindow
  have hpayloadWindow : selectedWindow.view.payload = gateRegs.payload := by
    have hprovenance :=
      ReferenceFirstLiveMissingSetProvenance.run_first_live_missing_set_provenance
        (ReferenceLocalReleaseGateChronology.sourceSeed rate source rewards C_star C_h hcross)
        source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
        rewards s count hspan hmode hfirst
    rcases hprovenance with hzero | ⟨_hW, firstSelected, firstInstalled, firstArm,
        _hfirstState, _hdispatch, _hinstalled, _hinitialPending, _hstartedPending,
        _hfirstSelected, _hfirstPayload, _hfirstPending, _hfirstStarted, hframes⟩
    · have hlength :
          (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R.records).length = 0 := by
        simpa only [W, E, hrecordsEq] using hzero
      rw [hlength] at hindexR
      omega
    · have hrowBound : k.val < W.length := by
        change k.val < (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length
        rw [hrecordsEq]
        exact hindexR
      obtain ⟨frameRecord, hframeRecord, frameSelected, hframeSelected,
          _hframePayload, hframePhase, _hnext⟩ :=
        hframes ⟨k.val, hrowBound⟩
      have hframeEq : frameRecord = w := by
        have h := hframeRecord
        change frameRecord = w at h
        exact h
      subst frameRecord
      have hframeSelection : w.output.preparation.coordinator.selection = some frameSelected := by
        have h := hframeSelected
        change w.output.preparation.coordinator.selection = some frameSelected at h
        exact h
      have hframeChoice : frameSelected = selectedWindow :=
        Option.some.inj (hframeSelection.symm.trans hselectedWindow)
      subst frameSelected
      have hphaseLive := hframePhase
      rw [hliveState] at hphaseLive
      have hregs : liveRegs = gateRegs := by
        have heq : CoordinatorConfiguration.live liveRegs liveOwned liveBase =
            CoordinatorConfiguration.live gateRegs gateOwned gateBase :=
          hliveState.symm.trans hgateLiveWindow
        cases heq
        rfl
      exact hphaseLive.1.trans (congrArg (fun registers => registers.payload) hregs)
  have hstoredWindow : ReferenceAssignmentPayloadPersistence.storedPayload
        w.input.state.coordinator = some selectedWindow.view.payload := by
    rw [hgateLive, ReferenceAssignmentPayloadPersistence.storedPayload_live]
    exact congrArg some hpayloadWindow.symm
  have hordinary : ∀ i,
      ((ReferenceActivePhysicalStep.prepare w.input).followers.followers i).configuration =
        .ordinary (states i) (memories i) := by
    intro i
    have h : ((w.output.preparation.followers.followers i).configuration) =
        .ordinary (states i) (memories i) := by
      have h' := hprepared i
      change ((w.output.preparation.followers.followers i).configuration) =
        .ordinary (states i) (memories i) at h'
      exact h'
    rw [w.output_eq] at h
    simpa only [ReferenceActivePhysicalStep.step] using h
  have hpending : ∀ i : Fin (p.m - 1),
      i ∈ ReferencePhysicalReleaseQuota.pendingSet selectedWindow.view.payload w ↔
        (states i).status = .pending := by
    intro i
    exact ReferencePhysicalReleaseQuota.pendingAtStart_ordinary_prepare
      selectedWindow.view.payload w.input gateRegs gateOwned gateBase hgateLive
      hpayloadWindow.symm hgatePending i (states i) (memories i) (hordinary i)
  let snapshot := ReferenceFirstLiveReleaseGeometry.actualChoiceSnapshot selectedWindow states
  let finToFollower : Fin (p.m - 1) → ActiveRoundActions.Follower p.m := fun i =>
    ⟨i.val, by
      simpa only [ActiveRoundActions.Follower, PublicDiscreteDraws.followerCount] using i.isLt⟩
  have hmissing : snapshot.missing = ∅ := by
    simp only [snapshot, ReferenceFirstLiveReleaseGeometry.actualChoiceSnapshot, hemptyWindow]
  have hstatus : ∀ i : ActiveRoundActions.Follower p.m,
      snapshot.status i = .pending ∨ snapshot.status i = .released := by
    intro i
    let j := ReferenceFirstLiveReleaseGeometry.followerToFin i
    change (states (ReferenceFirstLiveReleaseGeometry.followerToFin i)).status = .pending ∨
      (states (ReferenceFirstLiveReleaseGeometry.followerToFin i)).status = .released
    rcases hfields (ReferenceFirstLiveReleaseGeometry.followerToFin i) with ⟨hne, _⟩
    cases hs : (states j).status with
    | unoccupied => exact False.elim (hne hs)
    | pending => exact Or.inl rfl
    | released => exact Or.inr rfl
  let row := ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow w.input.rewards w.input.time
  have hU : selectedWindow.view.payload.slowSet.val =
      ReleaseRoundKernel.assignedImage selectedWindow.view.payload.assignment :=
    selectedWindow.view.payload.assignment_image.symm
  have hkernel := ReleaseRoundKernel.pathwise_sentinel_cost_bound
      p.two_le_m selectedWindow.view.payload.assignment selectedWindow.view.payload.slowSet hU
      snapshot hmissing hstatus input row
  have hownObs : ∀ player : Fin p.m,
      ((w.ownEntries player).2).val.val =
        ((ReferenceActivePhysicalStep.prepare w.input).feedback.observations player).val.val := by
    intro player
    rw [ReferenceActivePhysicalHorizon.RoundRecord.ownEntries_formula w player]
    simp only [ReferenceActivePhysicalHorizon.RoundRecord.actions, w.output_eq,
      ReferenceActiveFeedbackCut.FeedbackCut.observations_eq]
    rfl
  have htotal : ReleaseRoundKernel.physicalFeedbackTotal p.two_le_m snapshot input row =
      ∑ player : Fin p.m, ((w.ownEntries player).2).val.val := by
    have hfollowers (f : Fin p.m → ℝ) :
        (∑ i : ActiveRoundActions.Follower p.m,
          f (PublicDiscreteDraws.followerPlayer p.two_le_m i)) =
        ∑ player ∈ Finset.univ.erase (ActiveRoundActions.coordinator p.two_le_m), f player := by
      classical
      apply Finset.sum_bij (s := Finset.univ)
        (t := Finset.univ.erase (ActiveRoundActions.coordinator p.two_le_m))
        (fun i _ => PublicDiscreteDraws.followerPlayer p.two_le_m i)
      · intro i _
        exact Finset.mem_erase.mpr ⟨
          ActiveRoundActions.followerPlayer_ne_coordinator p.two_le_m i,
          Finset.mem_univ _⟩
      · intro i _ j _ hij
        exact ActiveRoundActions.followerPlayer_injective p.two_le_m hij
      · intro player hplayer
        rcases Finset.mem_erase.mp hplayer with ⟨hne, _⟩
        refine ⟨ActiveRoundActions.followerIndex p.two_le_m player hne,
          Finset.mem_univ _, ?_⟩
        exact ActiveRoundActions.followerPlayer_followerIndex p.two_le_m player hne
      · intro i _
        rfl
    have hsum (f : Fin p.m → ℝ) :
        (∑ player : Fin p.m, f player) = f (ActiveRoundActions.coordinator p.two_le_m) +
          ∑ i : ActiveRoundActions.Follower p.m,
            f (PublicDiscreteDraws.followerPlayer p.two_le_m i) := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ _), hfollowers]
    have hfb (player : Fin p.m) :
        ActiveRoundActions.feedback p.two_le_m snapshot input row player =
          ((w.ownEntries player).2).val.val := by
      calc
        ActiveRoundActions.feedback p.two_le_m snapshot input row player =
            ((ReferenceActivePhysicalStep.prepare w.input).feedback.observations player).val.val :=
          (hfeedback player).symm
        _ = ((w.ownEntries player).2).val.val := (hownObs player).symm
    calc
      ReleaseRoundKernel.physicalFeedbackTotal p.two_le_m snapshot input row =
          ActiveRoundActions.feedback p.two_le_m snapshot input row
              (ActiveRoundActions.coordinator p.two_le_m) +
            ∑ i : ActiveRoundActions.Follower p.m, ActiveRoundActions.feedback p.two_le_m snapshot input row
              (PublicDiscreteDraws.followerPlayer p.two_le_m i) := rfl
      _ = ((w.ownEntries (ActiveRoundActions.coordinator p.two_le_m)).2).val.val +
            ∑ i : Fin (p.m - 1),
              ((w.ownEntries (PublicDiscreteDraws.followerPlayer p.two_le_m i)).2).val.val := by
          rw [hfb (ActiveRoundActions.coordinator p.two_le_m)]
          apply congrArg
          apply Finset.sum_congr rfl
          intro i _
          exact hfb (PublicDiscreteDraws.followerPlayer p.two_le_m i)
      _ = ∑ player : Fin p.m, ((w.ownEntries player).2).val.val :=
        (hsum (fun player => ((w.ownEntries player).2).val.val)).symm
  have hpendingStatus (i : ActiveRoundActions.Follower p.m) :
      (ReferenceFirstLiveReleaseGeometry.followerToFin i) ∈
          ReferencePhysicalReleaseQuota.pendingSet selectedWindow.view.payload w ↔
        snapshot.status i = .pending := by
    have h := hpending (ReferenceFirstLiveReleaseGeometry.followerToFin i)
    have hstatusEq : snapshot.status i =
        (states (ReferenceFirstLiveReleaseGeometry.followerToFin i)).status := by
      change (states i).status =
        (states (ReferenceFirstLiveReleaseGeometry.followerToFin i)).status
      congr 1
    simpa only [hstatusEq] using h
  have hpendingSum :
      (∑ i : ActiveRoundActions.Follower p.m,
          if snapshot.status i = .pending then
          ReleaseRoundKernel.chi row (selectedWindow.view.payload.assignment.assigned i) else 0) =
      ∑ i ∈ ReferencePhysicalReleaseQuota.pendingSet selectedWindow.view.payload w,
        ReleaseRoundKernel.chi row (selectedWindow.view.payload.assignment.assigned i) := by
    classical
    calc
      _ = ∑ i : Fin (p.m - 1),
          if i ∈ ReferencePhysicalReleaseQuota.pendingSet selectedWindow.view.payload w then
            ReleaseRoundKernel.chi row
              (selectedWindow.view.payload.assignment.assigned (finToFollower i)) else 0 := by
          change (∑ i : Fin (p.m - 1),
            if snapshot.status (finToFollower i) = .pending then
              ReleaseRoundKernel.chi row
                (selectedWindow.view.payload.assignment.assigned (finToFollower i)) else 0) = _
          apply Finset.sum_congr rfl
          intro i _
          have hiff := hpendingStatus (finToFollower i)
          have hmem : i ∈ ReferencePhysicalReleaseQuota.pendingSet selectedWindow.view.payload w ↔
              (ReferenceFirstLiveReleaseGeometry.followerToFin (finToFollower i)) ∈
                ReferencePhysicalReleaseQuota.pendingSet selectedWindow.view.payload w := by
            simp only [finToFollower, ReferenceFirstLiveReleaseGeometry.followerToFin]
          have hiff' : i ∈ ReferencePhysicalReleaseQuota.pendingSet selectedWindow.view.payload w ↔
              snapshot.status (finToFollower i) = .pending := hmem.trans hiff
          exact if_congr hiff'.symm rfl rfl
      _ = ∑ i ∈ ReferencePhysicalReleaseQuota.pendingSet selectedWindow.view.payload w,
          ReleaseRoundKernel.chi row (selectedWindow.view.payload.assignment.assigned i) := by
          rw [Finset.sum_ite_mem]
          rw [Finset.univ_inter]
          apply Finset.sum_congr rfl
          intro i hi
          congr 1
  have hcollision :
      (∃ i : ActiveRoundActions.Follower p.m, snapshot.status i = .pending) ↔
        (ReferencePhysicalReleaseQuota.pendingSet selectedWindow.view.payload w).Nonempty := by
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨ReferenceFirstLiveReleaseGeometry.followerToFin i,
        (hpendingStatus i).mpr hi⟩
    · rintro ⟨i, hi⟩
      refine ⟨finToFollower i, ?_⟩
      have hround : ReferenceFirstLiveReleaseGeometry.followerToFin (finToFollower i) = i := by
        apply Fin.ext
        rfl
      simpa only [hround] using (hpendingStatus (finToFollower i)).mp hi
  have hgoal := hkernel
  rw [hfast, htotal, hpendingSum] at hgoal
  simp only [hcollision] at hgoal
  have hboundWindow := hgoal
  rw [← hwr]
  exact ⟨selectedWindow, hselectedWindow, hstoredWindow, hemptyWindow, hboundWindow⟩

end Bandits.Support.ReferenceFirstLivePhysicalSentinelCost

end
