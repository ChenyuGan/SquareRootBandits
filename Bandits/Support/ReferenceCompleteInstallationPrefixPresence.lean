/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteInstallationPredecessorInterval
public import Bandits.Support.ReferenceFirstCorrectedNextCalendarWordJoin

import Mathlib.Tactic

/-!
# Optional initialized prefixes at actual later installations

Source evidence: ZIP4 `appendix_a_local_protocol.tex:28-64`,
`06_interruptions.tex:40-100,192-233,246-299`, and
`04_slow_fast_learner.tex:157-174`.

This is an internal structural result about the literal optional cells on one
complete physical suffix. It does not establish numerical truth at every date.
-/

@[expose] public section
noncomputable section

open Bandits.Support
open ConstructorDimensions ReferenceActivePhysicalStep ReferenceActivePhysicalHorizon

namespace Bandits.Support.ReferenceCompleteInstallationPrefixPresence

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

private theorem mapM_id_eq_map_some {α : Type*} :
    ∀ {slots : List (Option α)} {cells : List α},
      slots.mapM id = some cells → slots = cells.map some := by
  intro slots
  induction slots with
  | nil =>
      intro cells h
      cases cells <;> simp [List.mapM_nil] at h ⊢
  | cons slot slots ih =>
      intro cells h
      cases slot with
      | none => simp [List.mapM_cons] at h
      | some cell =>
          cases ht : slots.mapM id with
          | none => simp [List.mapM_cons, ht] at h
          | some tail =>
              have hc : cell :: tail = cells := by
                simpa [List.mapM_cons, ht] using h
              cases hc
              have htail := ih ht
              simp [htail]

private theorem mapM_id_map_some {α : Type*} (cells : List α) :
    (cells.map some).mapM id = some cells := by
  induction cells with
  | nil => rfl
  | cons cell cells ih => simp [List.mapM_cons, ih]

private theorem mapM_id_take {α : Type*} (slots : List (Option α))
    (cells : List α) (h : slots.mapM id = some cells) (n : ℕ) :
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
              have hc : a :: tail = cells := by
                simpa [List.mapM_cons, ht] using h
              subst cells
              cases n with
              | zero => rfl
              | succ n => simp [List.mapM_cons, ih tail ht n]

private theorem prefixInputs_take
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (m n : ℕ) (L : List (RecordedQueueRun.RoundInput p.K))
    (hL : ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
      rate rewards C_star C_h m z = some L)
    (hs : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h ≤ n)
    (hnm : n ≤ m) :
    ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
      rate rewards C_star C_h n z =
      some (L.take (n - ReferenceCompletePhysicalHistory.physicalStart
        rate z rewards C_star C_h)) := by
  have hm := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs_launch
    rate rewards C_star C_h m z L hL
  have hnLaunch : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
      rate rewards C_star C_h n z := ⟨hm.1, hs⟩
  have hslots :
      (((ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords
        rate rewards C_star C_h z).take
          (m - ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart
            rate rewards C_star C_h z)).map
        (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate)).mapM id = some L := by
    have h := hL
    simp only [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs,
      ite_eq_left hm] at h
    exact h
  have ht := mapM_id_take _ _ hslots
    (n - ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart
      rate rewards C_star C_h z)
  simpa only [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs,
    ite_eq_left hnLaunch,
    ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart,
    List.map_take, List.take_take,
    Nat.min_eq_left (Nat.sub_le_sub_right hnm _)] using ht

private theorem prefixInputs_shape
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (k : ℕ) (L : List (RecordedQueueRun.RoundInput p.K))
    (hk : k ≤ (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (hL : ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
      rate rewards C_star C_h
      (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + k) z =
        some L) :
    L.length = k ∧
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h).take k).map
          (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate) = L.map some := by
  have hlaunch := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs_launch
    rate rewards C_star C_h
    (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + k) z L hL
  have hslots :
      (((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h).take k).map
        (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate)).mapM id = some L := by
    have h := hL
    simp only [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs,
      ite_eq_left hlaunch,
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords,
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart,
      show ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + k -
        ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h = k by omega] at h
    exact h
  have hmap := mapM_id_eq_map_some hslots
  have hlength := congrArg List.length hmap
  simp only [List.length_map, List.length_take, Nat.min_eq_left hk] at hlength
  exact ⟨hlength.symm, hmap⟩

private theorem prefix_map_eq_of_coverage {α β : Type*} (records : List α)
    (cell : α → Option β) (cells : List β)
    (hbound : cells.length ≤ records.length)
    (hcoverage : ∀ k : Fin cells.length,
      ∃ r, records[k.val]? = some r ∧ cell r = some cells[k.val]) :
    (records.take cells.length).map cell = cells.map some := by
  apply List.ext_getElem
  · simp only [List.length_map, List.length_take, Nat.min_eq_left hbound,
      List.length_map]
  · intro k hk hk'
    have hkCell : k < cells.length := by simpa only [List.length_map] using hk'
    obtain ⟨r, hr, hcell⟩ := hcoverage ⟨k, hkCell⟩
    have hr' : records[k]'(by omega) = r :=
      (List.getElem?_eq_some_iff.mp hr).2
    simpa only [List.getElem_map, List.getElem_take, hr'] using hcell

private theorem complete_suffix_record_time
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length) :
    (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[k.val].input.time.val =
        ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + k.val := by
  have hvalues := ReferenceCompletePhysicalHistory.completeSuffixRecords_time_values
    rate z rewards C_star C_h
  have hindex : k.val < p.T - ReferenceCompletePhysicalHistory.physicalStart
      rate z rewards C_star C_h := by
    rw [← ReferenceCompletePhysicalHistory.completeSuffixRecords_length
      rate z rewards C_star C_h]
    exact k.isLt
  have hget := congrArg (fun values : List ℕ => values[k.val]?) hvalues
  rw [List.getElem?_map, List.getElem?_eq_getElem k.isLt, Option.map_some,
    ReferenceActivePhysicalHorizon.calendar, List.getElem?_range' hindex,
    Nat.one_mul] at hget
  exact Option.some.inj hget

private theorem complete_suffix_input_not_first
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length) (hk : 0 < k.val) :
    (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[k.val].input.state.coordinator ≠ .first := by
  let j : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length := ⟨k.val - 1, by omega⟩
  have hj : j.val + 1 < (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length := by dsimp [j]; omega
  have hadj := ReferenceCompleteLaterLiveComplementPrefixReplay.complete_adjacent
    (rate := rate) rewards C_star C_h z j.val hj
  have hcoord := congrArg (fun state : ReferenceActivePhysicalStep.State p rate =>
    state.coordinator) hadj
  have hphase :=
    (ReferenceCompleteCoordinatorPhaseExhaustion.complete_coordinator_phase_exhaustion
      rate rewards C_star C_h z).1
  have hout : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[j.val].output.next.coordinator ≠ .first :=
    (hphase j).2.2.2.1
  have hindex : j.val + 1 = k.val := by dsimp [j]; omega
  intro hfirst
  apply hout
  exact hcoord.symm.trans (by simpa only [hindex] using hfirst)

private theorem live_readout_cell0
    (rate : ReferenceActivePhysicalStep.RateInput p) (s : ℕ)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (c : RecordedQueueRun.RoundInput p.K)
    (hread : ReferenceLaterLiveNumericalReadout.laterLiveReadout s r = some c) :
    ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r = some c := by
  classical
  obtain ⟨selected, ho, hselection, hbase, hliveState, hcell⟩ :=
    ReferenceLaterLiveNumericalReadout.laterLiveReadout_some s r c hread
  have hz : 0 < selected.view.payload.sigma.val := by omega
  have hzero : ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r = some c := by
    unfold ReferenceLaterLiveNumericalReadout.laterLiveReadout
    simp only [hselection, hz, hliveState, and_self, ite_true, dite_eq_left ho]
    exact congrArg some hcell.symm
  have hcollection : ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 r = none := by
    cases hc : ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 r with
    | none => rfl
    | some d =>
        exact False.elim (ReferenceCompleteNumericalBranchObservation.readouts_disjoint
          rate 0 r ⟨by rw [hzero]; rfl, by rw [hc]; rfl⟩)
  simp [ReferenceFirstCollectionCurrentRetainedGate.cell0, hcollection, hzero]

/-- Every actual later installation has the literal optional initialized
calendar prefix at that index, together with every earlier prefix on the same
original source records and whole reward table. -/
theorem internal_complete_later_installation_prefix_inputs
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
      ∀ h : ℕ, h ≤ b.val →
        ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
          rate rewards C_star C_h
          (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + h) z =
            some (P0.take h) := by
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  have target : ∀ n (hn : n < R.length),
      ReferenceCollectionPhaseHistory.laterChosen (R[n]'hn).input = true →
      ∃ P0 : List (RecordedQueueRun.RoundInput p.K),
        P0.length = n ∧ (R.take n).map
          (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate) = P0.map some ∧
        ∀ h : ℕ, h ≤ n →
          ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
            rate rewards C_star C_h (s + h) z = some (P0.take h) := by
    intro n hn
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro hlater
        let current : Fin R.length := ⟨n, hn⟩
        have hpred :=
          ReferenceCompleteInstallationPredecessorInterval.internal_complete_installation_predecessor_interval
            rate rewards C_star C_h z current hlater
        dsimp only at hpred
        obtain ⟨a, r0, q0, beta, e, seg, initializer, saved,
          hae, heb, he, hbirth, htime, hnext, hbase, hnobirth, hsegment,
          hsegmentNe, hentry, hcut, hpayload, hinitializer, hchecked, harm,
          hsigma, hcutoff, hbaseI, hbe, hwhole, hdrop, hexit, hendpointState,
          hendpointCoordinator, hpending, hcursor, hfirstCell⟩ := hpred
        by_cases ha0 : a.val = 0
        · obtain ⟨u, hu, hz⟩ := hfirstCell ha0
          let t := (R[current.val]'current.isLt).input.time
          have htimeCurrent := complete_suffix_record_time rate rewards C_star C_h z current
          have htimeCurrent' : t.val = s + n := by
            dsimp only [t, current, R, s] at htimeCurrent ⊢
            exact htimeCurrent
          obtain ⟨hc, _hspan, _hshort, _stream, _head, _valid, _D, L,
            _hsu, _hut, _hu, _hdate, _hpending0, _hrecord, _hchoice,
            _hDlen, _hDhead, _hDread, _hjoin, _hpast, hLlen, hcoverage⟩ :=
            ReferenceFirstCollectionCurrentRetainedGate.firstCell_prefix_coverage
              rate rewards C_star C_h u t z hz
          have hLlen' : L.length = n := by
            rw [htimeCurrent'] at hLlen
            omega
          have hcoverage' : ∀ k : Fin L.length,
              ∃ r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate),
                R[k.val]? = some r ∧
                  ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r = some L[k.val] := by
            intro k
            obtain ⟨r, hr, _hdate, hcell⟩ := hcoverage k
            exact ⟨r, by simpa only [R] using hr, hcell⟩
          have hmap := prefix_map_eq_of_coverage R
            (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate) L
            (by
              rw [hLlen']
              exact Nat.le_of_lt (by simpa only [current] using current.isLt))
            hcoverage'
          have hmap' : (R.take n).map
              (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate) = L.map some := by
            simpa only [hLlen'] using hmap
          have hlaunch : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
              rate rewards C_star C_h (s + n) z := by
            refine ⟨hc, ?_⟩
            have hsU : s ≤ u.val := by omega
            omega
          have hfinal :
              ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
                rate rewards C_star C_h (s + n) z = some L := by
            unfold ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
            rw [ite_eq_left hlaunch]
            simp only [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords,
              ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart]
            rw [show ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + n -
              ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h = n by omega]
            have hslots : ((R.take n).map
                (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate)).mapM id = some L := by
              rw [hmap']
              exact mapM_id_map_some L
            simpa only [R] using hslots
          have hshape := prefixInputs_shape rate rewards C_star C_h z n L
            (Nat.le_of_lt current.isLt) hfinal
          refine ⟨L, hshape.1, hshape.2, ?_⟩
          · intro h hh
            have hsmall := prefixInputs_take rate rewards C_star C_h z
              (s + n) (s + h) L hfinal (by omega) (by omega)
            have hindex : s + h -
                ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h = h := by
              dsimp only [s]
              omega
            simpa only [hindex] using hsmall
        · have hnotFirst := complete_suffix_input_not_first rate rewards C_star C_h z a
            (by omega)
          let hrecord := R[a.val]'a.isLt
          have hprepared : hrecord.output.preparation =
              ReferenceActivePhysicalStep.prepare hrecord.input := by
            rw [hrecord.output_eq]
            rfl
          have hpreparedCoordinator := congrArg
            (fun prep : ReferenceActivePhysicalStep.PreparedRound hrecord.input => prep.coordinator)
            hprepared
          have hnotFirstRecord : hrecord.input.state.coordinator ≠ .first := by
            change (ReferenceCompletePhysicalHistory.completeSuffixRecords
              rate z rewards C_star C_h)[a.val].input.state.coordinator ≠ .first
            exact hnotFirst
          have hbirthRecord :
              ReferenceAssignmentPayloadPersistence.InstallationBirth hrecord r0.payload := hbirth
          have hlaterA : ReferenceCollectionPhaseHistory.laterChosen hrecord.input = true := by
            cases hpc : hrecord.output.preparation.coordinator with
            | first outcome =>
                have hstateFirst : hrecord.input.state.coordinator = .first := by
                  have hpcPrep : (ReferenceActivePhysicalStep.prepare hrecord.input).coordinator =
                      .first outcome := hpreparedCoordinator.symm.trans hpc
                  change ReferenceActivePhysicalStep.dispatch hrecord.input = .first outcome at hpcPrep
                  cases hstate : hrecord.input.state.coordinator with
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
                exact False.elim (hnotFirstRecord hstateFirst)
            | live registers owned base =>
                simp [ReferenceAssignmentPayloadPersistence.InstallationBirth, hpc] at hbirthRecord
            | collection payload ledger clock cutoff outcome =>
                cases outcome with
                | laterChosen core consistent started hstart instruction hassignment
                    output hlocal clockData installed selected =>
                    unfold ReferenceCollectionPhaseHistory.laterChosen
                    rw [hpreparedCoordinator.symm, hpc]
                | _ =>
                    simp [ReferenceAssignmentPayloadPersistence.InstallationBirth, hpc] at hbirthRecord
            | invalidCollectionCutoff =>
                simp [ReferenceAssignmentPayloadPersistence.InstallationBirth, hpc] at hbirthRecord
            | dagger =>
                simp [ReferenceAssignmentPayloadPersistence.InstallationBirth, hpc] at hbirthRecord
          have hempty := ReferenceCollectionPhaseHistory.laterChosen_pending_empty
            hrecord.input hlaterA
          rcases hempty with ⟨payloadA, ledgerA, proposalA, hstateA, hpendingA⟩
          have hstateAOriginal := hstateA
          dsimp only [hrecord, R] at hstateAOriginal
          have houtside :=
            ReferenceCorrectedSuccessorOutsideNumericalStep.complete_actual_birth_outside_complement_prefix_replay
              rate rewards C_star C_h z a
          dsimp only at houtside
          rw [hstateAOriginal] at houtside
          obtain ⟨uA, huA, core, started, hstart, instruction, hassignment,
            htimeA, consistent, output, hlocal, clockData, installation,
            selected, hinstall, v, hselection, hpayloadV, hcutoffV, hlive,
            c, ho, cell, hreadout, hcell, hcellSelected, henabled, hrate,
            hreward, hrows, hrewards, recording, serviced, pending,
            finished, hrecording, hservicedRecording, hservice, hfinish,
            hnextA, _hstrictAndContinuations⟩ := houtside hpendingA
          have hcell0 := live_readout_cell0 rate s hrecord c hreadout
          have hlookup :
              (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords
                rate rewards C_star C_h z)[s + a.val -
                  ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart
                    rate rewards C_star C_h z]? = some hrecord := by
            have hindex : s + a.val -
                ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h =
                a.val := by dsimp [s]; omega
            simp only [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords,
              ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart]
            rw [hindex]
            change R[a.val]? = some R[a.val]
            exact List.getElem?_eq_getElem a.isLt
          have hane : a.val < n := lt_trans hae heb
          have hprefixA := ih a.val hane a.isLt (by simpa only [R] using hlaterA)
          obtain ⟨Pin, hPinLength, _hPinMap, hPinAll⟩ := hprefixA
          have hPinPrefix0 := hPinAll a.val le_rfl
          have hPinPrefix :
              ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
                rate rewards C_star C_h (s + a.val) z = some Pin := by
            have htaken : Pin.take a.val = Pin := by
              exact List.take_of_length_le (by rw [hPinLength])
            rw [htaken] at hPinPrefix0
            exact hPinPrefix0
          have happend :=
            ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs_append_one
              rate rewards C_star C_h (s + a.val) z Pin hPinPrefix hrecord c hlookup hcell0
          have hprefixA1 :
              ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
                rate rewards C_star C_h (s + (a.val + 1)) z = some (Pin ++ [c]) := by
            have hdate : s + a.val + 1 = s + (a.val + 1) := by omega
            simpa only [hdate] using happend
          have ha1 : a.val + 1 < R.length := by omega
          let a1 : Fin R.length := ⟨a.val + 1, ha1⟩
          have hadj := ReferenceCompleteLaterLiveComplementPrefixReplay.complete_adjacent
            (rate := rate) rewards C_star C_h z a.val (by omega)
          have hstateA1 : (R[a1.val]'a1.isLt).input.state.coordinator =
              .live r0 q0 beta := by
            have hcoord := congrArg
              (fun state : ReferenceActivePhysicalStep.State p rate => state.coordinator) hadj
            rw [hnext] at hcoord
            simpa only [a1] using hcoord
          have hstrict : s < r0.payload.sigma.val := by rw [htime]; omega
          have hext :=
            ReferenceCompleteLaterLiveCollectionPrefixExtension.complete_later_live_collection_prefix_extension
              rate rewards C_star C_h z a1 r0 q0 beta hstateA1 hstrict
              (Pin ++ [c]) hprefixA1
          dsimp only at hext
          rcases hext with ⟨_hPLength, _hextBound, _hTimeBound, _hHLength,
            _hHTake, _hLivePrefixes, _hLiveSlots, rE, qE, hpE, _hLast,
            _hAtEndpoint, _hValues, halt⟩
          have hExtEnd : a1.val +
              (ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
                rate rewards C_star C_h z a1.val).length = e := by
            simpa only [a1] using he.symm
          rcases halt with hterminal | ⟨hextIndex, chosen, _hDispatch,
            _hPreparation, hcutData⟩
          · have heq := hExtEnd
            omega
          · cases chosen with
            | cutoffChosen dispatched hstart ledger hinit hcand hdomain hclock
                hpendingCut hnone selected =>
                obtain ⟨_hdate, _hscan, segExt, initializerExt, Dword,
                  hDword, hsegmentExt, _hentryExt, _hpayloadExt, _hledgerExt,
                  _hIExt, _hIeqExt, _hcheckedExt, _harmExt, _hsigmaExt,
                  _hcutoffExt, _hscanExt, _hfreezeExt, _hbaseExt, _hchosenExt,
                  _hneExt, _hpartExt, _hexitExt, _hfoldExt, _hvExt, _htExt,
                  _hcoverExt, _hmapExt, _hsyncExt, _huniqueExt, hElen,
                  _hEtake, _hEtakeP, _hV, _hVtime, _hRtake, hprefixAll,
                  _hcoords, _henabled, _hdisabled⟩ := hcutData
                have hsegmentAtPred :
                    ReferenceCollectionSegmentExtraction.segmentAt R e = some segExt := by
                  rw [← hExtEnd]
                  exact hsegmentExt
                have hsegEq : segExt = seg :=
                  Option.some.inj (hsegmentAtPred.symm.trans hsegment)
                let A := ReferenceCompleteLaterLiveComplementPrefixReplay.prefixCells
                  rewards C_star C_h z a1 r0 q0 beta hstateA1 hstrict
                let Full := ((Pin ++ [c]) ++ A) ++ Dword
                have hVeq : a1.val +
                    (ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
                      rate rewards C_star C_h z a1.val).length +
                      segExt.records.length = n := by
                  calc
                    _ = e + seg.records.length := by rw [hExtEnd, hsegEq]
                    _ = n := hbe.symm
                have hFullLength : Full.length = n := by
                  dsimp only [Full, A]
                  calc
                    _ = a1.val +
                        (ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
                          rate rewards C_star C_h z a1.val).length +
                          segExt.records.length := hElen
                    _ = n := hVeq
                have hprefixFinal :
                    ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
                      rate rewards C_star C_h (s + n) z =
                        some (Full.take n) := by
                  dsimp only [Full, A]
                  refine hprefixAll n ?_ ?_
                  · dsimp [a1]
                    omega
                  · rw [← hVeq]
                have htakeE : Full.take n = Full := List.take_of_length_le (by rw [hFullLength])
                rw [htakeE] at hprefixFinal
                have hshape := prefixInputs_shape rate rewards C_star C_h z n
                  Full (Nat.le_of_lt current.isLt) hprefixFinal
                refine ⟨Full, hFullLength, hshape.2, ?_⟩
                intro h hh
                have hsmall := prefixInputs_take rate rewards C_star C_h z
                  (s + n) (s + h) Full hprefixFinal
                  (by dsimp [s]; omega) (by omega)
                have htakeIndex : s + h -
                    ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h = h := by
                  dsimp [s]
                  omega
                simpa only [htakeIndex] using hsmall
            | _ => exact False.elim hcutData

  obtain ⟨P0, hlength, hmap, hprefixes⟩ := target b.val b.isLt (by simpa only [R] using hb)
  exact ⟨P0, hlength, hmap, hprefixes⟩

end Bandits.Support.ReferenceCompleteInstallationPrefixPresence
