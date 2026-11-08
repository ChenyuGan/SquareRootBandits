/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstReplacementCalendarInitialization
public import Bandits.Support.ReferenceCompleteInstallationPrefixPresence
public import Bandits.Support.ReferenceCompleteCollectionBoundaryHistory
public import Bandits.Support.ReferenceCompleteInitializedOutsideCalendarReplay
public import Bandits.Support.ReferenceCompleteAssignedCalendarWordAlignment

import Mathlib.Tactic

/-!
# Calendar initialization at later installations

This module is intended to join the original-index predecessor and accepted
calendar replay results into the full successful-installation output.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions ReferenceActivePhysicalStep ReferenceActivePhysicalHorizon

namespace Bandits.Support.ReferenceCompleteInstallationCalendarInitializationInduction

variable {p : ConstructorDimensions.Parameters}

private theorem first_cell_initialization_case
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (hb : ReferenceCollectionPhaseHistory.laterChosen
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[b.val].input = true)
    (hprefix : ∃ P0 : List (RecordedQueueRun.RoundInput p.K),
      P0.length = b.val ∧
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h).take b.val).map
          (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate) = P0.map some ∧
      ∀ h : ℕ, h ≤ b.val →
        ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
          rate rewards C_star C_h
          (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + h) z =
            some (P0.take h))
    (hfirst : ∃ u : Fin p.T,
      z ∈ ReferenceCalendarCollectionCallControlLaw.firstCell
        rate rewards C_star C_h u
          (ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate z rewards C_star C_h)[b.val].input.time) :
    ∃ P0 : List (RecordedQueueRun.RoundInput p.K),
      P0.length = b.val ∧
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h).take b.val).map
          (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate) = P0.map some ∧
      (∀ h : ℕ, h ≤ b.val →
        ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
          rate rewards C_star C_h
          (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + h) z =
            some (P0.take h)) ∧
      ReferenceFirstReplacementCalendarInitialization.initializes_calendar rate P0
        (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)[b.val] := by
  classical
  rcases hprefix with ⟨P, hPlen, hPmap, hPprefix⟩
  rcases hfirst with ⟨u, hz⟩
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  let t := R[b.val].input.time
  have ht : t.val = s + b.val := by
    have htimes := ReferenceCompletePhysicalHistory.completeSuffixRecords_time_values
      rate z rewards C_star C_h
    have hindex : b.val < p.T - s := by
      rw [← ReferenceCompletePhysicalHistory.completeSuffixRecords_length]
      exact b.isLt
    have hget := congrArg (fun values : List ℕ => values[b.val]?) htimes
    rw [List.getElem?_map, List.getElem?_eq_getElem b.isLt, Option.map_some,
      ReferenceActivePhysicalHorizon.calendar, List.getElem?_range' hindex, Nat.one_mul] at hget
    exact Option.some.inj hget
  obtain ⟨Q, hQlen, hQmap, hQprefix, hQinit⟩ :=
    ReferenceFirstReplacementCalendarInitialization.firstCell_actual_replacement_calendar_initialization
      rate rewards C_star C_h u t z hz
  have hQlen' : Q.length = t.val - s := by simpa only [s] using hQlen
  have hQlenB : Q.length = b.val := by rw [ht] at hQlen'; omega
  have hstart : s + b.val = t.val := ht.symm
  have hinit := hQinit b (by simpa only [s] using hstart) hb
  have hQfull : Q = P := by
    have hQlast := hQprefix b.val (by omega)
    have hPlast := hPprefix b (by omega)
    have htake : Q.take b.val = P.take b.val :=
      Option.some.inj (hQlast.symm.trans hPlast)
    calc
      Q = Q.take b.val := by rw [← hQlenB, List.take_length]
      _ = P.take b.val := htake
      _ = P := by rw [← hPlen, List.take_length]
  have hinitP :
      ReferenceFirstReplacementCalendarInitialization.initializes_calendar rate P
        (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)[b.val] := by
    rw [← hQfull]
    exact hinit
  exact ⟨P, hPlen, hPmap, hPprefix, hinitP⟩

private theorem installation_birth_later_chosen_of_not_first
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (hnotFirst : record.input.state.coordinator ≠ .first)
    (hbirth : ReferenceAssignmentPayloadPersistence.InstallationBirth record payload) :
    ReferenceCollectionPhaseHistory.laterChosen record.input = true := by
  have hprepared : record.output.preparation =
      ReferenceActivePhysicalStep.prepare record.input := by
    rw [record.output_eq]
    rfl
  have hpreparedCoordinator := congrArg
    (fun prepared : ReferenceActivePhysicalStep.PreparedRound record.input => prepared.coordinator)
    hprepared
  cases hpc : record.output.preparation.coordinator with
  | first outcome =>
      have hstateFirst : record.input.state.coordinator = .first := by
        have hpcPrep : (ReferenceActivePhysicalStep.prepare record.input).coordinator =
            .first outcome := hpreparedCoordinator.symm.trans hpc
        change ReferenceActivePhysicalStep.dispatch record.input = .first outcome at hpcPrep
        cases hstate : record.input.state.coordinator with
        | first => rfl
        | live registers owned base =>
            simp only [ReferenceActivePhysicalStep.dispatch, hstate,
              CoordinatorRoundDispatch.dispatch] at hpcPrep
            cases hpcPrep
        | collection payload ledger proposal =>
            simp only [ReferenceActivePhysicalStep.dispatch,
              CoordinatorRoundDispatch.dispatch, hstate] at hpcPrep
            split at hpcPrep <;> cases hpcPrep
        | dagger =>
            simp [ReferenceActivePhysicalStep.dispatch, hstate] at hpcPrep
      exact False.elim (hnotFirst hstateFirst)
  | live registers owned base =>
      simp [ReferenceAssignmentPayloadPersistence.InstallationBirth, hpc] at hbirth
  | collection payload ledger clock cutoff outcome =>
      cases outcome with
      | laterChosen core consistent started hstart instruction hassignment
          output hlocal clockData installed selected =>
          unfold ReferenceCollectionPhaseHistory.laterChosen
          rw [hpreparedCoordinator.symm, hpc]
      | _ => simp [ReferenceAssignmentPayloadPersistence.InstallationBirth, hpc] at hbirth
  | invalidCollectionCutoff =>
      simp [ReferenceAssignmentPayloadPersistence.InstallationBirth, hpc] at hbirth
  | dagger =>
      simp [ReferenceAssignmentPayloadPersistence.InstallationBirth, hpc] at hbirth

private theorem live_readout_cell0
    (rate : ReferenceActivePhysicalStep.RateInput p) (s : ℕ)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (cell : RecordedQueueRun.RoundInput p.K)
    (hread : ReferenceLaterLiveNumericalReadout.laterLiveReadout s record = some cell) :
    ReferenceFirstCollectionCurrentRetainedGate.cell0 rate record = some cell := by
  classical
  obtain ⟨selected, ho, hselection, hbase, hliveState, hcell⟩ :=
    ReferenceLaterLiveNumericalReadout.laterLiveReadout_some s record cell hread
  have hz : 0 < selected.view.payload.sigma.val := by omega
  have hzero : ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 record = some cell := by
    unfold ReferenceLaterLiveNumericalReadout.laterLiveReadout
    simp only [hselection, hz, hliveState, and_self, ite_true, dite_eq_left ho]
    exact congrArg some hcell.symm
  have hcollection : ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 record = none := by
    cases hc : ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 record with
    | none => rfl
    | some d =>
        exact False.elim (ReferenceCompleteNumericalBranchObservation.readouts_disjoint
          rate 0 record ⟨by rw [hzero]; rfl, by rw [hc]; rfl⟩)
  simp [ReferenceFirstCollectionCurrentRetainedGate.cell0, hcollection, hzero]

private theorem complete_suffix_input_not_first
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length) (hk : 0 < k.val) :
    (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[k.val].input.state.coordinator ≠ .first := by
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let j : Fin R.length := ⟨k.val - 1, by dsimp [R]; omega⟩
  have hj : j.val + 1 < R.length := by dsimp [j, R]; omega
  have hadj := ReferenceCompleteLaterLiveComplementPrefixReplay.complete_adjacent
    (rate := rate) rewards C_star C_h z j.val hj
  have hcoord := congrArg
    (fun state : ReferenceActivePhysicalStep.State p rate => state.coordinator) hadj
  have hphase :=
    (ReferenceCompleteCoordinatorPhaseExhaustion.complete_coordinator_phase_exhaustion
      rate rewards C_star C_h z).1
  have hout : R[j.val].output.next.coordinator ≠ .first := (hphase j).2.2.2.1
  have hindex : j.val + 1 = k.val := by dsimp [j]; omega
  intro hfirst
  apply hout
  exact hcoord.symm.trans (by simpa only [hindex] using hfirst)

private theorem calendarReplay_append_one
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (P : List (RecordedQueueRun.RoundInput p.K))
    (cell : RecordedQueueRun.RoundInput p.K) (arm : Fin p.K) :
    ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate (P ++ [cell]) arm
      (P.length + 1) =
    QueueReplay.transition (4 * rate.n)
      (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate P arm P.length)
      (cell.enabled, RecordedQueueRun.quantizedArrival
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell arm) := by
  have htake : (P ++ [cell]).take (P.length + 1) = P ++ [cell] := by simp
  unfold ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay
  rw [htake]
  simp only [ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar,
    List.map_append, List.map_cons, List.map_nil]
  rw [QueueReplay.replay_append]
  simp only [QueueReplay.replay, List.foldl_cons, List.foldl_nil]
  rw [List.take_length]

private theorem serviced_birth_matches_calendarReplay
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (P : List (RecordedQueueRun.RoundInput p.K))
    (cell : RecordedQueueRun.RoundInput p.K) (arm : Fin p.K)
    (score queue scoreNext queueNext : ℕ)
    (hscore : score =
      (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate P arm P.length).1)
    (hqueue : queue =
      (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate P arm P.length).2)
    (hservice : (scoreNext, queueNext) = QueueReplay.transition (4 * rate.n)
      (score, queue)
      (cell.enabled, RecordedQueueRun.quantizedArrival
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell arm)) :
    (scoreNext, queueNext) =
      ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate (P ++ [cell]) arm
        (P.length + 1) := by
  have hregisters : (score, queue) =
      ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate P arm P.length :=
    Prod.ext hscore hqueue
  rw [calendarReplay_append_one, ← hregisters]
  exact hservice

private theorem prefixInputs_list_eq
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (s n : ℕ) (P Q : List (RecordedQueueRun.RoundInput p.K))
    (hPlen : P.length = n)
    (hP : ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
      rate rewards C_star C_h (s + n) z = some (P.take n))
    (hQ : ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
      rate rewards C_star C_h (s + n) z = some Q) :
    P = Q := by
  have htake : P.take n = Q := Option.some.inj (hP.symm.trans hQ)
  calc
    P = P.take n := by rw [← hPlen, List.take_length]
    _ = Q := htake

private theorem original_prefix_append_record_cell
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (n : ℕ) (hn : n < (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (P : List (RecordedQueueRun.RoundInput p.K))
    (cell : RecordedQueueRun.RoundInput p.K)
    (hprefix : ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
      rate rewards C_star C_h
        (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + n) z = some P)
    (hcell : ReferenceFirstCollectionCurrentRetainedGate.cell0 rate
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[n] = some cell) :
    ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
      rate rewards C_star C_h
        (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + (n + 1)) z =
      some (P ++ [cell]) := by
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  have hindex : s + n -
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h = n := by
    dsimp [s]
    omega
  have hlookup :
      (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords
        rate rewards C_star C_h z)[s + n -
          ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart rate rewards C_star C_h z]? =
        some (R[n]'(by simpa only [R] using hn)) := by
    simp only [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords,
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart]
    rw [hindex]
    change R[n]? = some R[n]
    exact List.getElem?_eq_getElem (by simpa only [R] using hn)
  have happend :=
    ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs_append_one
      rate rewards C_star C_h (s + n) z P hprefix (R[n]'(by simpa only [R] using hn))
      cell hlookup hcell
  have hdate : (s + n) + 1 = s + (n + 1) := by omega
  simpa only [hdate] using happend

private theorem actual_later_installation_birth_cell0
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (hk : ReferenceCollectionPhaseHistory.laterChosen
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[k.val].input = true) :
    ∃ cell : RecordedQueueRun.RoundInput p.K,
      ReferenceLaterLiveNumericalReadout.laterLiveReadout
        (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
        (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)[k.val] = some cell ∧
      ReferenceFirstCollectionCurrentRetainedGate.cell0 rate
        (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)[k.val] = some cell := by
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let r := R[k.val]'k.isLt
  obtain ⟨payload, ledger, saved, hstate, hpending⟩ :=
    ReferenceCollectionPhaseHistory.laterChosen_pending_empty r.input hk
  have hstep := ReferenceCompleteEmptyInstallationNumericalStep.complete_empty_installation_current_numerical_step
    rate rewards C_star C_h z k
  dsimp only [R, r] at hstep
  rw [hstate] at hstep
  dsimp only at hstep
  rcases hstep hpending with ⟨u, hu, core, started, hstart, instruction,
    hassignment, htime, hkind, consistent, output, hlocal, hsuccess, clockData,
    installation, selected, hinstall, hresult, hdispatch, hprepared,
    hpayload, hvector, hassignmentVector, hbase, hqueues, hanchor,
    v, hselection, hvpayload, hvcutoff, hlive, hstrict, c, ho, cell, hreadout,
    hcell, hcellSelected, hstates, hmemories, hunoccupied, henabled, hrate,
    hreward, hmarker, hrows, hselectedRow, hrewards, harrival, hcontribution, hoccupiedArrival, howner,
    recording, serviced, pending, finished, hrecording, hrecorded, hservicedRecording,
    hrawAll, hservice, hconfirmation, hfinish, hpost, hcoordinator, hnext,
    hupBank⟩
  have hcell0 := live_readout_cell0 rate
    (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
    r c hreadout
  exact ⟨c, by simpa only [r, R] using hreadout,
    by simpa only [r, R] using hcell0⟩

private theorem first_cell_later_installation_initialization
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (hb : ReferenceCollectionPhaseHistory.laterChosen
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[b.val].input = true)
    (hfirst : ∃ u : Fin p.T,
      z ∈ ReferenceCalendarCollectionCallControlLaw.firstCell
        rate rewards C_star C_h u
          (ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate z rewards C_star C_h)[b.val].input.time) :
    ∃ P0 : List (RecordedQueueRun.RoundInput p.K),
      P0.length = b.val ∧
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h).take b.val).map
          (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate) = P0.map some ∧
      (∀ h : ℕ, h ≤ b.val →
        ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
          rate rewards C_star C_h
          (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + h) z =
            some (P0.take h)) ∧
      ReferenceFirstReplacementCalendarInitialization.initializes_calendar rate P0
        (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)[b.val] := by
  have hprefix :=
    ReferenceCompleteInstallationPrefixPresence.internal_complete_later_installation_prefix_inputs
      rate rewards C_star C_h z b hb
  exact first_cell_initialization_case rate rewards C_star C_h z b hb hprefix hfirst

private theorem initialized_birth_service_replay
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (a : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (Pa : List (RecordedQueueRun.RoundInput p.K))
    (hinitA : ReferenceFirstReplacementCalendarInitialization.initializes_calendar rate Pa
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[a.val]) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    ∃ (rb : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
      (qb : CoordinatorLiveServiceFinish.OwnedRegisters rb)
      (bb : Fin (p.m - 1) → ℕ) (c : RecordedQueueRun.RoundInput p.K),
      R[a.val].output.next.coordinator = .live rb qb bb ∧
      ReferenceAssignmentPayloadPersistence.InstallationBirth R[a.val] rb.payload ∧
      s < rb.payload.sigma.val ∧
      ReferenceCompleteInstallationPredecessorInterval.installationBase?
        R[a.val].output.preparation.coordinator = some bb ∧
      ReferenceFirstCollectionCurrentRetainedGate.cell0 rate R[a.val] = some c ∧
      (∀ j : CanonicalFastSampling.FastArm rb.payload.slowSet,
        (rb.complementScores j, qb.queue j) =
          ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate (Pa ++ [c]) j.val
            (Pa ++ [c]).length) ∧
      (∀ j : CanonicalFastSampling.FastArm rb.payload.slowSet,
        qb.previousService j =
          (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate (Pa ++ [c]) j.val
            (Pa ++ [c]).length).1 -
          (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate (Pa ++ [c]) j.val
            ((Pa ++ [c]).length - 1)).1) ∧
      (∀ i : Fin (p.m - 1),
        (rb.payload.downRecord i).val.q =
          (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate Pa
            (rb.payload.assignment.assigned i) Pa.length).2 ∧
        bb i = (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate Pa
          (rb.payload.assignment.assigned i) Pa.length).1) := by
  classical
  intro R s
  rcases hinitA with ⟨old, ledger, proposal, uA, hstateA, hpendingA, huA,
    coreA, startedA, hstartA, instructionA, hassignmentA, htimeA,
    consistentA, outputA, hlocalA, clockDataA, installedA, selectedA,
    hinstallA, hsuccessA, hdispatchA, hpreparedA,
    hpayloadA, hsigmaA, hvectorA, hrecA, hnumA, hretainedA,
    hcomplementA, hcorrectedA, hrenewalA⟩
  have hstep :=
    ReferenceCompleteEmptyInstallationNumericalStep.complete_empty_installation_current_numerical_step
      rate rewards C_star C_h z a
  dsimp only at hstep
  rw [hstateA] at hstep
  dsimp only at hstep
  rcases hstep hpendingA with ⟨u, hu, core, started, hstart, instruction,
    hassignment, htime, hkind, consistent, output, hlocal, hsuccess, clockData,
    installed, selected, hinstall, hresult, hdispatch, hprepared,
    hpayload, hvector, hassignmentVector, hbaseNew, hqueues, hanchor,
    v, hselection, hvpayload, hvcutoff, hlive, hstrict, c, ho, cell, hreadout,
    hcell, hcellSelected, hstates, hmemories, hunoccupied, henabled, hrate,
    hreward, hmarker, hrows, hselectedRow, hrewards, harrival, hcontribution, hoccupiedArrival, howner,
    recording, serviced, pending, finished, hrecording, hrecorded, hservicedRecording,
    hrawAll, hservice, hconfirmation, hfinish, hpostChoice, hcoordinator, hnext,
    hupBank⟩
  have huEq : uA = u := Fin.ext (by omega)
  cases huEq
  have hstartedEq : startedA = started := Except.ok.inj (hstartA.symm.trans hstart)
  cases hstartedEq
  have hinstructionEq : instructionA = instruction :=
    Option.some.inj (hassignmentA.symm.trans hassignment)
  cases hinstructionEq
  have hpreparedEq := hpreparedA.symm.trans hprepared
  have houtputEq : outputA = output := by
    cases hpreparedEq
    rfl
  subst outputA
  have hnum : ∀ arm : Fin p.K,
      AssignmentScoreReconstruction.sourceScore output.reconstruction arm =
        (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate Pa arm Pa.length).1 ∧
      AssignmentScoreReconstruction.initialQueue output.reconstruction arm =
        (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate Pa arm Pa.length).2 := by
    intro arm
    exact ⟨(hnumA arm).1, (hnumA arm).2.1⟩
  let rb : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta :=
    { payload := installed.registers.payload
      priorClock := finished.clock
      pendingAtChoice := finished.pending
      time := R[a.val].input.time
      gridBoundary := finished.clock.g
      complementScores := serviced.score }
  let qb : CoordinatorLiveServiceFinish.OwnedRegisters rb :=
    { queue := serviced.queue, previousService := serviced.previousService }
  have hseed : ∀ j : CanonicalFastSampling.FastArm rb.payload.slowSet,
      (rb.complementScores j, qb.queue j) =
        ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate (Pa ++ [c]) j.val
          (Pa ++ [c]).length := by
    intro j
    have hh := (hservice j).2.1
    rw [← henabled] at hh
    simpa only [List.length_append, List.length_singleton] using
      serviced_birth_matches_calendarReplay rate Pa c j.val _ _ _ _
        (hnum j.val).1 (hnum j.val).2 hh
  refine ⟨rb, qb, installed.retainedBaseScore, c, ?_, ?_, hstrict, ?_,
    live_readout_cell0 rate s R[a.val] c hreadout, hseed, ?_, ?_⟩
  · simpa only [hpostChoice] using hnext
  · rw [ReferenceAssignmentPayloadPersistence.InstallationBirth, hprepared]
    exact ⟨rfl, by
      change installed.registers.payload.sigma.val = R[a.val].input.time.val
      rw [hpayload, output.payload_start, htime]⟩
  · rw [hprepared]
    rfl
  · intro j
    change serviced.previousService j = _
    rw [(hservice j).2.2, (hnum j.val).1, ← hseed j]
    have ht : (Pa ++ [c]).take ((Pa ++ [c]).length - 1) = Pa := by
      simp only [List.length_append, List.length_singleton, Nat.add_sub_cancel, List.take_left]
    congr 1
    simp only [ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay, ht, List.take_length]
  · intro i
    exact ⟨(AssignmentStartPayload.Input.downRecord_initialQueue _ i).trans
      ((hqueues _).trans (hnum _).2), (hbaseNew i).trans (hnum _).1⟩

private theorem literal_replay_word_slots
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (R : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (seg : ReferenceCollectionSegmentExtraction.Segment rate)
    (Pa C Dword : List (RecordedQueueRun.RoundInput p.K)) (a e : ℕ)
    (hPa : Pa.length = a) (hPC : (Pa ++ C).length = e)
    (hDlen : Dword.length = seg.records.length)
    (hpart : seg.records ++ seg.remaining = R.drop e)
    (hV : ((Pa ++ C) ++ Dword).length ≤ R.length)
    (hslots : ∀ x : Fin ((Pa ++ C) ++ Dword).length,
      ReferenceFirstCollectionCurrentRetainedGate.cell0 rate
        (R[x.val]'(Nat.lt_of_lt_of_le x.isLt hV)) =
          some (((Pa ++ C) ++ Dword)[x.val]))
    (hraw : ∀ arm : Fin p.K,
      seg.records.map (ReferenceCollectionRawBufferHistory.physicalQueueRecord
        seg.context.preLedger arm) =
          ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar rate arm Dword) :
    (∀ x : Fin C.length,
      ∃ r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate),
        R[a + x.val]? = some r ∧
        ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r = some C[x.val]) ∧
    (∀ (arm : Fin p.K) (x : Fin seg.records.length),
      let d := Dword[x.val]'(Nat.lt_of_lt_of_eq x.isLt hDlen.symm)
      ReferenceFirstCollectionCurrentRetainedGate.cell0 rate seg.records[x.val] = some d ∧
      ReferenceCollectionRawBufferHistory.physicalQueueRecord seg.context.preLedger
        arm seg.records[x.val] =
          (d.enabled, RecordedQueueRun.quantizedArrival
            (ReferenceFirstLaunchNumericalCell.queueParameters rate) d arm)) := by
  have htotal : ((Pa ++ C) ++ Dword).length = e + seg.records.length := by
    rw [List.length_append, hPC, hDlen]
  have hPC' : a + C.length = e := by
    simpa only [List.length_append, hPa] using hPC
  constructor
  · intro x
    have hidx : a + x.val < ((Pa ++ C) ++ Dword).length := by omega
    have hR : a + x.val < R.length := Nat.lt_of_lt_of_le hidx hV
    refine ⟨R[a + x.val], List.getElem?_eq_getElem hR, ?_⟩
    have hh := hslots ⟨a + x.val, hidx⟩
    rw [List.getElem_append_left (by omega : a + x.val < (Pa ++ C).length),
      List.getElem_append_right (by omega : Pa.length ≤ a + x.val)] at hh
    simpa only [hPa, Nat.add_sub_cancel_left] using hh
  · intro arm x
    have hR : e + x.val < R.length := by omega
    have hrecord : seg.records[x.val] = R[e + x.val] := by
      have hh := congrArg (fun xs => xs[x.val]?) hpart
      rw [List.getElem?_append_left x.isLt, List.getElem?_drop] at hh
      simp only [List.getElem?_eq_getElem x.isLt,
        List.getElem?_eq_getElem hR] at hh
      exact Option.some.inj hh
    constructor
    · rw [hrecord]
      have hh := hslots ⟨e + x.val, by omega⟩
      rw [List.getElem_append_right (by omega : (Pa ++ C).length ≤ e + x.val)] at hh
      simpa only [hPC, Nat.add_sub_cancel_left] using hh
    · have hh := congrArg (fun xs => xs[x.val]?) (hraw arm)
      simp only [ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar,
        List.getElem?_map, List.getElem?_eq_getElem x.isLt,
        List.getElem?_eq_getElem (Nat.lt_of_lt_of_eq x.isLt hDlen.symm),
        Option.map_some] at hh
      exact Option.some.inj hh

private theorem actual_endpoint_initialization
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (P : List (RecordedQueueRun.RoundInput p.K)) (hPlen : P.length = b.val)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (saved : Option (Fin p.T × Bool))
    (hstate : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[b.val].input.state.coordinator =
        .collection payload ledger saved)
    (hempty : ledger.pending = ∅) (e : ℕ)
    (hvalues : ∀ arm : Fin p.K,
      ledger.cutoffRegisters arm = some ⟨
        (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate P arm e).1,
        (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate P arm e).2,
        (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate P arm e).1 -
          (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate P arm (e - 1)).1⟩ ∧
      ledger.currentRegisters arm = some ⟨
        (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate P arm b.val).2,
        (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate P arm b.val).1 -
          (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate P arm (b.val - 1)).1⟩ ∧
      (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate P arm e).1 +
        ledger.increment arm =
          (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate P arm b.val).1) :
    ReferenceFirstReplacementCalendarInitialization.initializes_calendar rate P
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[b.val] := by
  classical
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  have hstepB :=
    ReferenceCompleteEmptyInstallationNumericalStep.complete_empty_installation_current_numerical_step
      rate rewards C_star C_h z b
  dsimp only at hstepB
  rw [hstate] at hstepB
  dsimp only at hstepB
  rcases hstepB hempty with ⟨uB, huB, coreB, startedB, hstartB, instructionB,
    hassignmentB, htimeB, hkindB, consistentB, outputB, hlocalB, hsuccessB,
    clockDataB, installedB, selectedB, hinstallB, hresultB, hdispatchB, hpreparedB,
    hpayloadB, hvectorB, hassignmentVectorB, hbaseB, hqueuesB, hanchorB, _⟩
  subst installedB
  obtain ⟨_, hcutB, hcurrentB, hscoreB, hqueueB, _⟩ :=
    AssignmentScoreReconstruction.reconstructLaterStart_success_equations
      _ _ outputB.reconstruction outputB.reconstruction_eq
  let inputB := ReferenceActivePhysicalStep.collectionInput R[b.val].input payload ledger
    (ReferenceActivePhysicalStep.collectionClock payload ledger saved uB) uB
  obtain ⟨_, _, _, _, _, _, hcutFields, hcurrentFields, hincrementFields, _⟩ :=
    CoordinatorRoundDispatch.collectionOperationLedger_fields inputB coreB.payload_n_eq
  have hnumB : ∀ arm : Fin p.K,
      AssignmentScoreReconstruction.sourceScore outputB.reconstruction arm =
        (ReferenceFirstReplacementCalendarInitialization.calendarReplay rate arm P P.length).1 ∧
      AssignmentScoreReconstruction.initialQueue outputB.reconstruction arm =
        (ReferenceFirstReplacementCalendarInitialization.calendarReplay rate arm P P.length).2 ∧
      outputB.reconstruction.registers.current arm = ⟨
        (ReferenceFirstReplacementCalendarInitialization.calendarReplay rate arm P P.length).2,
        (ReferenceFirstReplacementCalendarInitialization.calendarReplay rate arm P P.length).1 -
          (ReferenceFirstReplacementCalendarInitialization.calendarReplay rate arm P (P.length - 1)).1⟩ := by
    intro arm
    have hcutActual : ledger.cutoffRegisters arm =
        some (outputB.reconstruction.registers.cutoff arm) :=
      (congrFun hcutFields arm).symm.trans (hcutB arm)
    have hcurrentActual : ledger.currentRegisters arm =
        some (outputB.reconstruction.registers.current arm) :=
      (congrFun hcurrentFields arm).symm.trans (hcurrentB arm)
    have hcutEq := Option.some.inj (hcutActual.symm.trans (hvalues arm).1)
    have hcurrentEq := Option.some.inj (hcurrentActual.symm.trans (hvalues arm).2.1)
    have hscore := (hscoreB arm).trans
      (congrArg (fun increment => (outputB.reconstruction.registers.cutoff arm).score + increment)
        (congrFun hincrementFields arm))
    rw [hcutEq] at hscore
    have hscore' := hscore.trans (hvalues arm).2.2
    have hqueue := (hqueueB arm).trans
      (congrArg CoordinatorCollectionLedger.CurrentRegister.queue hcurrentEq)
    exact ⟨by simpa only [hPlen,
        ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay,
        ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar,
        ReferenceFirstReplacementCalendarInitialization.calendarReplay,
        ReferenceFirstReplacementCalendarInitialization.rawCalendar] using hscore',
      by simpa only [hPlen,
        ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay,
        ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar,
        ReferenceFirstReplacementCalendarInitialization.calendarReplay,
        ReferenceFirstReplacementCalendarInitialization.rawCalendar] using hqueue,
      by simpa only [hPlen,
        ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay,
        ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar,
        ReferenceFirstReplacementCalendarInitialization.calendarReplay,
        ReferenceFirstReplacementCalendarInitialization.rawCalendar] using hcurrentEq⟩
  refine ⟨payload, ledger, saved, uB, hstate, hempty, huB, coreB, startedB, hstartB,
    instructionB, hassignmentB, htimeB, consistentB, outputB, hlocalB,
    clockDataB, CoordinatorAssignmentRegisterInstall.installLater outputB clockDataB,
    selectedB, rfl, hsuccessB, hdispatchB, hpreparedB, hpayloadB, ?_,
    hvectorB, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · exact outputB.payload_start.trans htimeB
  · intro arm
    exact ⟨(hnumB arm).1, (hnumB arm).2.1,
      (outputB.payload_queues arm).trans (hnumB arm).2.1,
      (hqueuesB arm).trans (hnumB arm).2.1, (hnumB arm).2.2⟩
  · intro i
    exact ⟨rfl, (hbaseB i).trans (hnumB _).1,
      (AssignmentStartPayload.Input.downRecord_initialQueue _ i).trans
        ((hqueuesB _).trans (hnumB _).2.1)⟩
  · intro j
    exact ⟨(hnumB j.val).1, (hnumB j.val).2.1,
      congrArg CoordinatorCollectionLedger.CurrentRegister.lastService (hnumB j.val).2.2⟩
  · intro hcorrected
    exact (AssignmentScoreReconstruction.reconstructLaterStart_corrected_equations
      _ _ outputB.reconstruction outputB.reconstruction_eq hcorrected).1
  · intro hrenewal
    exact AssignmentScoreReconstruction.reconstructLaterStart_renewal_equations
      _ _ outputB.reconstruction outputB.reconstruction_eq hrenewal

private theorem accepted_up_segment_endpoint
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (k b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (i : Fin (p.m - 1)) (reply : ReferenceCollectionPhaseHistory.UpRecord p rate)
    (hacc : ReferenceCollectionPhaseHistory.AcceptedUp
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[k.val].input i reply)
    (P : AssignmentStartPayload.Input p rate.eta)
    (base : Fin (p.m - 1) → ℕ)
    (hbirth : ReferenceAssignmentPayloadPersistence.InstallationBirth
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[b.val] P)
    (hbase : ReferenceCompleteInstallationPredecessorInterval.installationBase?
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[b.val]'b.isLt).output.preparation.coordinator = some base)
    (hselector : reply.val.sigma = P.sigma.val + 1)
    (hlater : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h <
      P.sigma.val)
    (P0 C Dword : List (RecordedQueueRun.RoundInput p.K)) (e : ℕ)
    (seg : ReferenceCollectionSegmentExtraction.Segment rate)
    (hP0 : ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
      rate rewards C_star C_h
        (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + b.val)
        z = some P0)
    (hscan : FollowerCutoffScan.firstCutoff p rate.eta.val P.sigma
      (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
        (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z))) =
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + e + 1)
    (hseg : ReferenceCollectionSegmentExtraction.segmentAt
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h) e =
        some seg)
    (hClen : C.length = e - b.val)
    (hDlen : Dword.length = seg.records.length)
    (hCslot : ∀ x : Fin C.length,
      let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h
      ∃ r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate), R[b.val + x.val]? = some r ∧
        ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r = some C[x.val])
    (hDslot : ∀ x : Fin seg.records.length,
      let c := Dword[x.val]'(Nat.lt_of_lt_of_eq x.isLt hDlen.symm)
      ReferenceFirstCollectionCurrentRetainedGate.cell0 rate seg.records[x.val] = some c ∧
      ReferenceCollectionRawBufferHistory.physicalQueueRecord seg.context.preLedger
        (P.assignment.assigned i) seg.records[x.val] =
        (c.enabled, RecordedQueueRun.quantizedArrival
          (ReferenceFirstLaunchNumericalCell.queueParameters rate) c
          (P.assignment.assigned i)))
    (hqueue : (P.downRecord i).val.q =
      (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate P0
        (P.assignment.assigned i) P0.length).2)
    (hscore : base i =
      (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate P0
        (P.assignment.assigned i) P0.length).1) :
    let G := (P0 ++ C) ++ Dword
    let v := e + seg.records.length
    let arm := P.assignment.assigned i
    seg.final.cutoffRegisters arm = some ⟨
      (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate G arm e).1,
      (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate G arm e).2,
      (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate G arm e).1 -
        (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate G arm (e - 1)).1⟩ ∧
    seg.final.currentRegisters arm = some ⟨
      (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate G arm v).2,
      (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate G arm v).1 -
        (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate G arm (v - 1)).1⟩ ∧
    (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate G arm e).1 +
      seg.final.increment arm =
        (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate G arm v).1 := by
  classical
  intro G v arm
  have hy :=
    ReferenceCompleteAssignedCalendarWordAlignment.complete_accepted_up_literal_calendar_replay
      rate rewards C_star C_h z k b i reply hacc P base hbirth
      (by
        cases hc : (ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate z rewards C_star C_h)[b.val].output.preparation.coordinator with
        | first outcome =>
            cases outcome <;>
              simpa only [ReferenceCompleteInstallationPredecessorInterval.installationBase?, hc]
                using hbase
        | collection old ledger clock cutoff outcome =>
            cases outcome <;>
              simpa only [ReferenceCompleteInstallationPredecessorInterval.installationBase?, hc]
                using hbase
        | _ =>
            simpa only [ReferenceCompleteInstallationPredecessorInterval.installationBase?, hc]
              using hbase)
      hselector hlater
      P0 C Dword e seg hP0 hscan hseg hClen hDlen hCslot hDslot hqueue hscore
  rcases hy with ⟨choiceN, bN, j, logged, after, cutN, raw, scan, registers, lastService,
    hchoiceN, hbj, hjk, hbirthN, hretained, hlogged, hdown, houtcome,
    hscanN, hcheckedN, hqN, hreplySigma, hdpos, hdle, htimes, hLlen, vN, hoN,
    hselectedN, hpreparedN, hQ, hEd, hAlen, hAenabled, hregisters, hlastService,
    segN, doneN, c0, IN, hok, hoR, hn, hsegmentN, hentryN, hsegContextN,
    hc0Pay, hc0Init, hentryChoiceN, hIcheckedN, hIarmN, hIsigmaN, hIcutoffN,
    hIbaseN, hbaseProv, hrecordN, hdoneN, hcontextN, hacceptedN, hparsedN,
    hsenderN, hfinalN, recordingN, startedN, decodedN, bankN, hrecordingN,
    hstartN, hreceiveN, hdecodeN, hfinishN, hassignmentN, hstartedNoneN,
    hgammaStartedN, hgammaDecodedN, hfinishIncrementN, hnextN, hcontinuationN,
    hbN, hpayN, hoEq, hsegNEq, hNEq, hAEq, hHEq, hGlenN, hGprefixN,
    hLedge, hcalendar⟩
  have hh := hcalendar seg.records.length
    (by simpa only [hsegNEq] using Nat.succ_le_of_lt hn) le_rfl
  rw [hLedge] at hh
  simpa only [G, List.append_assoc, hpayN] using hh

/-- Internal numerical initialization at an actual successful later start.
The prefix excludes the queried installation's own service round. -/
theorem internal_complete_later_installation_calendar_initialization
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (hb : ReferenceCollectionPhaseHistory.laterChosen
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[b.val].input = true) :
    ∃ P0 : List (RecordedQueueRun.RoundInput p.K),
      P0.length = b.val ∧
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h).take b.val).map
          (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate) = P0.map some ∧
      (∀ h : ℕ, h ≤ b.val →
        ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
          rate rewards C_star C_h
          (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + h) z =
            some (P0.take h)) ∧
      ReferenceFirstReplacementCalendarInitialization.initializes_calendar rate P0
        (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)[b.val] := by
  classical
  induction b using Fin.strong_induction_on with
  | h b ih =>
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    have hbR : b.val < R.length := b.isLt
    obtain ⟨P, hPlen, hPmap, hPprefix⟩ :=
      ReferenceCompleteInstallationPrefixPresence.internal_complete_later_installation_prefix_inputs
        rate rewards C_star C_h z b hb
    obtain ⟨a, r0, q0, beta, e, seg, I, saved, hae, heb, he,
      hbirth, hsigma, hpost, hbase, hnoBirth, hseg, hne, hentry, hcut,
      hsegPay, hsegInit, hchecked, harm, hIsigma, hIcutoff, hIbase,
      hbend, hsplit, hdrop, hexit, hendState, hend, hempty, hcursor, hfirst⟩ :=
      ReferenceCompleteInstallationPredecessorInterval.internal_complete_installation_predecessor_interval
        rate rewards C_star C_h z b hb
    by_cases ha0 : a.val = 0
    · obtain ⟨u, _, hz⟩ := hfirst ha0
      exact first_cell_initialization_case rate rewards C_star C_h z b hb
        ⟨P, hPlen, hPmap, hPprefix⟩ ⟨u, hz⟩
    have ha : ReferenceCollectionPhaseHistory.laterChosen R[a.val].input = true :=
      installation_birth_later_chosen_of_not_first rate R[a.val] r0.payload
        (complete_suffix_input_not_first rate rewards C_star C_h z a (by omega)) hbirth
    obtain ⟨Pa, hPalen, hPamap, hPaprefix, hinitA⟩ :=
      ih a (by change a.val < b.val; omega) ha
    have hPa : Pa = P.take a.val := by
      have hleft := hPaprefix a.val (by omega)
      have hright := hPprefix a.val (by omega)
      rw [List.take_of_length_le (by omega : Pa.length ≤ a.val)] at hleft
      exact Option.some.inj (hleft.symm.trans hright)
    obtain ⟨rb, qb, bb, c, hpostBorn, hbirthBorn, hstrict, hbaseBorn,
      hcell0, hseed, hprevious, hassignedSeed⟩ :=
      initialized_birth_service_replay rate rewards C_star C_h z a Pa hinitA
    have hpostEq := hpost.symm.trans hpostBorn
    have hr0 := (ReferenceActivePhysicalStep.CoordinatorConfiguration.live.inj hpostEq).1
    have hownedEq := (ReferenceActivePhysicalStep.CoordinatorConfiguration.live.inj hpostEq).2.1
    have hbetaEq := (ReferenceActivePhysicalStep.CoordinatorConfiguration.live.inj hpostEq).2.2
    have hbirthPayload : r0.payload = rb.payload := congrArg
      CoordinatorLiveChoiceRecorderStep.Registers.payload hr0
    rw [hbirthPayload] at hbirth hsigma hsegPay harm hIsigma hend
    have hPaFull : ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
        rate rewards C_star C_h (s + a.val) z = some Pa := by
      simpa only [List.take_of_length_le (by omega : Pa.length ≤ a.val)] using
        hPaprefix a.val (by omega)
    have hPaC := original_prefix_append_record_cell rate rewards C_star C_h z
      a.val a.isLt Pa c hPaFull hcell0
    have hPaCeq : Pa ++ [c] = P.take (a.val + 1) :=
      Option.some.inj (hPaC.symm.trans (hPprefix (a.val + 1) (by omega)))
    let a1 : Fin R.length := ⟨a.val + 1, by omega⟩
    have hstate1 : R[a1.val].input.state.coordinator = .live rb qb bb := by
      have hadj := ReferenceCompleteLaterLiveComplementPrefixReplay.complete_adjacent
        (rate := rate) rewards C_star C_h z a.val (by omega)
      exact (congrArg (fun state : ReferenceActivePhysicalStep.State p rate =>
        state.coordinator) hadj).trans hpostBorn
    have houtside :=
      ReferenceCompleteInitializedOutsideCalendarReplay.complete_later_live_initialized_outside_calendar_replay
        rate rewards C_star C_h z a1 rb qb bb hstate1 hstrict (Pa ++ [c]) hPaC
        hseed (fun _ j => by
          simpa only [List.length_append, List.length_singleton, hPalen, a1] using hprevious j)
    rcases houtside with ⟨hPClen, hBlen, heR, heT, hHlen, hHtake,
      hHprefix, hLiveSlots, hHslots, hHdisabled,
      rE, qE, hpE, hlast, hinE, hEvalues, halt⟩
    have heX : a1.val +
        (ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
          rate rewards C_star C_h z a1.val).length = e := by
      simpa only [a1] using he.symm
    rcases halt with hterminal | ⟨heBound, segX, IX, l0, Dword,
      hsegX, hentryX, hsegPayX, hpreLedgerX, hsegInitX, hIX, hcheckedX,
      harmX, hIsigmaX, hIcutoffX, hscanX, hfreezeX, hbaseX, hcutX,
      hheadX, hpartitionX, hexitX, hrunX, hDlen, hDread, hDqueues,
      hElen, hEtake, hEprefixTake, hvR, hvT, hRtake, hEprefix, hEslots,
      hBenabled, hDdisabled, hEdisabled, hOutsideNum⟩
    · omega
    have hsegX' : ReferenceCollectionSegmentExtraction.segmentAt R e = some segX := by
      simpa only [heX] using hsegX
    have hsegEq : segX = seg := Option.some.inj (hsegX'.symm.trans hseg)
    subst segX
    let B := ReferenceCompleteLaterLiveComplementPrefixReplay.prefixCells
      rewards C_star C_h z a1 rb qb bb hstate1 hstrict
    let C := [c] ++ B
    let G := (Pa ++ C) ++ Dword
    have hEG : ((Pa ++ [c]) ++ B) ++ Dword = G := by
      simp only [G, C, List.append_assoc]
    have hGlen : G.length = b.val := by
      simpa only [G, C, B, List.append_assoc, heX, ← hbend] using hElen
    have hGprefix : ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
        rate rewards C_star C_h (s + b.val) z = some G := by
      have hh := hEprefix b.val (by dsimp [a1]; omega) (by omega)
      have hh' : ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
          rate rewards C_star C_h (s + b.val) z = some (G.take b.val) := by
        simpa only [G, C, B, List.append_assoc, heX, ← hbend] using hh
      simpa only [List.take_of_length_le (by omega : G.length ≤ b.val)] using hh'
    have hGP : G = P := by
      exact (prefixInputs_list_eq rate rewards C_star C_h z s b.val P G hPlen
        (hPprefix b.val le_rfl) hGprefix).symm
    have ha1 : a1.val = a.val + 1 := rfl
    have hClen : C.length = e - a.val := by
      simp only [C, List.length_append, List.length_singleton]
      have hBlen' : B.length =
          (ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
            rate rewards C_star C_h z a1.val).length := hBlen
      rw [hBlen']
      omega
    have hPClen' : (Pa ++ C).length = e := by
      rw [List.length_append, hPalen, hClen]
      omega
    have hfullSlots : ∀ x : Fin b.val,
        ReferenceFirstCollectionCurrentRetainedGate.cell0 rate
          (R[x.val]'(by omega)) = some (G[x.val]'(by omega)) := by
      intro x
      have hh := hEslots hvR hElen ⟨x.val, by omega⟩
      simpa only [G, C, B, List.append_assoc, heX, ← hbend] using hh.1
    obtain ⟨hCslot, hDslot⟩ := literal_replay_word_slots rate R seg Pa C Dword
      a.val e hPalen hPClen' hDlen
      (by simpa only [heX] using hpartitionX)
      (by change G.length ≤ R.length; omega)
      (fun x => by
        have hh := hfullSlots ⟨x.val, by simpa only [← hGlen] using x.isLt⟩
        exact hh)
      (fun arm => by simpa only [hpreLedgerX] using (hDqueues arm).2)
    obtain ⟨acceptedX, hinitialX, hfoldX⟩ :=
      CollectionBufferProvenance.startAndRunChecked_success_components
        IX.assignment IX.sigma IX.cutoff IX.freezeAt IX.base IX.outside seg.inputs _ hrunX
    have hcontextX := CollectionBufferProvenance.checkedRounds_success_preserves_context
      l0 seg.final seg.inputs acceptedX hfoldX
    have hinitContextX := CollectionBufferProvenance.startCollectionChecked_success_context
      IX.assignment IX.sigma IX.cutoff IX.freezeAt IX.base IX.outside l0 hinitialX
    have hfinalSigma : seg.final.sigma = rb.payload.sigma.val + 1 := by
      exact (congrArg (fun context => context.2.1) hcontextX).trans
        (hinitContextX.2.1.trans hIsigmaX)
    obtain ⟨_, _, _, savedHistory, _, _, during, _, _, _, _, _, _, haccepted, _⟩ :=
      ReferenceCompleteCollectionBoundaryHistory.internal_complete_collection_boundary_history
        rate rewards C_star C_h z e seg hseg hne hcut
    have hAssignedNum : ∀ i : Fin (p.m - 1),
        let arm := rb.payload.assignment.assigned i
        seg.final.cutoffRegisters arm = some ⟨
          (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate G arm e).1,
          (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate G arm e).2,
          (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate G arm e).1 -
            (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate G arm (e - 1)).1⟩ ∧
        seg.final.currentRegisters arm = some ⟨
          (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate G arm b.val).2,
          (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate G arm b.val).1 -
            (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate G arm (b.val - 1)).1⟩ ∧
        (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate G arm e).1 +
          seg.final.increment arm =
            (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate G arm b.val).1 := by
      intro i
      obtain ⟨k, reply, hek, hkb, _, hacc, hselector⟩ := haccepted hempty i
      have hqueueSeed := (hassignedSeed i).1
      have hscoreSeed := (hassignedSeed i).2
      have hy :=
        accepted_up_segment_endpoint
          rate rewards C_star C_h z k a i reply hacc rb.payload bb hbirthBorn
          hbaseBorn (hselector.trans hfinalSigma) hstrict Pa C Dword e seg hPaFull
          (hscanX.symm.trans (by simpa only [heX] using hIcutoffX)) hseg hClen hDlen hCslot
          (hDslot (rb.payload.assignment.assigned i)) hqueueSeed hscoreSeed
      simpa only [G, ← hbend] using hy
    have hvalues : ∀ arm : Fin p.K,
        seg.final.cutoffRegisters arm = some ⟨
          (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate G arm e).1,
          (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate G arm e).2,
          (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate G arm e).1 -
            (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate G arm (e - 1)).1⟩ ∧
        seg.final.currentRegisters arm = some ⟨
          (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate G arm b.val).2,
          (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate G arm b.val).1 -
            (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate G arm (b.val - 1)).1⟩ ∧
        (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate G arm e).1 +
          seg.final.increment arm =
            (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate G arm b.val).1 := by
      intro arm
      by_cases hmem : arm ∈ rb.payload.slowSet.val
      · have himage : arm ∈ Finset.univ.image rb.payload.assignment.assigned := by
          rw [AssignmentStartPayload.Input.assignment_image]
          exact hmem
        obtain ⟨i, _, hi⟩ := Finset.mem_image.mp himage
        simpa only [hi] using hAssignedNum i
      · have hh := hOutsideNum ⟨arm, Finset.mem_sdiff.mpr ⟨Finset.mem_univ arm, hmem⟩⟩
        simpa only [G, C, B, List.append_assoc, heX, ← hbend,
          ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay] using hh
    have hinitB := actual_endpoint_initialization rate rewards C_star C_h z b P hPlen
      rb.payload seg.final saved hend hempty e (by simpa only [hGP] using hvalues)
    exact ⟨P, hPlen, hPmap, hPprefix, hinitB⟩

end Bandits.Support.ReferenceCompleteInstallationCalendarInitializationInduction

end
