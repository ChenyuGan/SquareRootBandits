/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveComplementQueueReplay
public import Bandits.Support.ReferenceFirstLiveFollowerQueueReplay

import Lean.Elab.Tactic.Omega

/-!
# First-live physical and stopped numerical queue boundary

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:140-188`,
`sources/zip4/manuscript/05_binary_transport.tex:354-396,426-431`,
`sources/zip4/manuscript/06_interruptions.tex:192-233,246-295,391-408`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-64`, and
`sources/zip4/manuscript/08_main_theorem.tex:29-42`.

This internal theorem joins the actual whole-arm numerical cells, the existing
stopped queue machine, the coordinator's first-live complement registers, and
each follower's actual first-live state at one physical prefix. The only
physical coupling is through the inclusive first-live boundary at or before
the numerical first-overflow prefix. It makes no global stopping-time,
recording-law, or regret claim.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceFirstWindowNumericalStream
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceAssignmentPayloadPersistence
open Bandits.Support.CanonicalFastSampling

namespace Bandits.Support.ReferenceFirstLiveStoppedQueueComparison

variable {p : ConstructorDimensions.Parameters}

/-- One actual first-live physical boundary and its common stopped numerical
queue replay, including the inclusive first-overflow update. The input is the
original source, reward table, initialization crossing, and bounded calendar
length. All conditional physical facts are outputs from the two reviewed
first-live producers. -/
theorem actual_first_live_stopped_queue_common_boundary
    (rate : ReferenceFirstWindowNumericalStream.RateInput p)
    (source : ReferenceFirstWindowNumericalStream.SourceInput p)
    (rewards : ReferenceFirstWindowNumericalStream.RewardTable p)
    (C_star C_h : ℝ)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (count : ℕ)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed +
          count ≤ p.T)
    (b : ℕ)
    (hb : b ≤ (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
      rate source rewards C_star C_h hc count hspan).length) :
    let s := ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
    let I := ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hc
    let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
      rate source rewards C_star C_h hc
    let E := ReferenceFirstWindowNumericalStream.actualFirstLiveRun
      rate source rewards C_star C_h hc count hspan
    let W := ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
      rate source rewards C_star C_h hc count hspan
    let cells := ReferenceFirstWindowNumericalStream.actualLiveSourceCells
      rate source rewards C_star C_h hc count hspan
    let q := ReferenceFirstLaunchNumericalCell.queueParameters rate
    let κ := UnstoppedRecordedQueueComparison.firstOverflowPrefix q cells
    s + b ≤ p.T ∧
    (∀ a : Fin p.K,
      UnstoppedRecordedQueueComparison.unstoppedReplay q cells b a =
        QueueReplay.replay (4 * rate.n) (0, 0)
          ((cells.take b).map fun cell =>
            (cell.enabled, RecordedQueueRun.quantizedArrival q cell a))) ∧
    (∀ a : Fin p.K,
      (RecordedQueueRun.run q (cells.take b)).registers a =
        UnstoppedRecordedQueueComparison.unstoppedReplay q cells (min b κ) a) ∧
    ((RecordedQueueRun.run q (cells.take b)).overflow = true ↔ κ ≤ b) ∧
    (b ≤ κ →
      ∃ hprefix : s + b ≤ p.T,
        let boundary := ReferenceActivePhysicalHorizon.run I source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s b
          hprefix seed.activeAtStart;
        ((b = 0 →
          boundary.finalState = I ∧ boundary.finalState.coordinator = .first ∧
          (∀ i : Fin (p.m - 1),
            ∃ sb mb, boundary.finalState.followers i = .ordinary sb mb ∧
              sb = seed.followers i ∧ mb = seed.memory i ∧
              sb.lastDown = none ∧ sb.status = .unoccupied ∧ sb.S = 0 ∧
              sb.delta = 0 ∧ sb.backlog = 0 ∧
              sb.buffer = (seed.followers i).buffer)) ∧
        (0 < b →
          ∃ r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta,
          ∃ owned : CoordinatorLiveServiceFinish.OwnedRegisters r,
          ∃ base : Fin (p.m - 1) → ℕ,
            boundary.finalState.coordinator = .live r owned base ∧
            r.payload.sigma.val = s ∧ r.payload.n = rate.n ∧
            (∀ i, base i = 0) ∧
            (∃ birth : ReferenceActivePhysicalHorizon.RoundRecord
                (p := p) (rate := rate),
              birth ∈ boundary.records ∧
              ReferenceAssignmentPayloadPersistence.InstallationBirth birth r.payload ∧
              birth.input.time.val = s) ∧
            (∀ a : FastArm r.payload.slowSet,
              (r.complementScores a, owned.queue a) =
                (RecordedQueueRun.run q (cells.take b)).registers a.1 ∧
              owned.previousService a =
                (UnstoppedRecordedQueueComparison.unstoppedReplay q cells b a.1).1 -
                  (UnstoppedRecordedQueueComparison.unstoppedReplay q cells (b - 1) a.1).1) ∧
            (∀ i : Fin (p.m - 1),
              ∃ sb mb, boundary.finalState.followers i = .ordinary sb mb ∧
                ((sb.status ≠ .unoccupied →
                  sb.lastDown = some (r.payload.downRecord i) ∧
                  (sb.S, sb.backlog) =
                    (RecordedQueueRun.run q (cells.take b)).registers
                      (r.payload.assignment.assigned i) ∧
                  sb.delta =
                    (UnstoppedRecordedQueueComparison.unstoppedReplay q cells b
                      (r.payload.assignment.assigned i)).1 -
                    (UnstoppedRecordedQueueComparison.unstoppedReplay q cells (b - 1)
                      (r.payload.assignment.assigned i)).1 ∧
                  ∃ j : Fin W.length, j.val < b ∧
                    ReferenceAcceptedUpFollowerHistory.RetainedDown W[j.val] i
                      (r.payload.downRecord i)) ∧
                (sb.status = .unoccupied →
                  sb.lastDown = none ∧ sb.S = 0 ∧ sb.delta = 0 ∧ sb.backlog = 0 ∧
                  sb.buffer = (seed.followers i).buffer ++
                    (E.records.take b).flatMap
                      (ReferenceFollowerBufferProvenance.logEmission i) ∧
                  ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords
                    E.records i b (r.payload.downRecord i) b =
                    ((cells.take b).map fun cell =>
                      (cell.enabled, RecordedQueueRun.quantizedArrival q cell
                        (r.payload.assignment.assigned i))) ∧
                  QueueReplay.replay (4 * rate.n) (0, 0)
                    (ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords
                      E.records i b (r.payload.downRecord i) b) =
                    UnstoppedRecordedQueueComparison.unstoppedReplay q cells b
                      (r.payload.assignment.assigned i)))) ∧
            (∀ a : Fin p.K,
              a ∈ r.payload.slowSet.val ↔
                ∃ i : Fin (p.m - 1), r.payload.assignment.assigned i = a) ∧
            (∀ a : Fin p.K, a ∉ r.payload.slowSet.val →
              ∃ fast : FastArm r.payload.slowSet, fast.1 = a)))) ∧
    (κ ≤ cells.length →
      (∀ a : Fin p.K,
        (RecordedQueueRun.run q (cells.take κ)).registers a =
          UnstoppedRecordedQueueComparison.unstoppedReplay q cells κ a) ∧
      (∃ a : Fin p.K,
        32 * ((RecordedQueueRun.run q (cells.take κ)).registers a).2 > D p) ∧
      ∃ a : Fin p.K,
        (((RecordedQueueRun.run q (cells.take κ)).registers a).2 : ℝ) /
          (rate.n : ℝ) > 1 / (32 * rate.eta.val)) := by
  classical
  dsimp only
  let s := ReferenceInitializationRun.elapsed p
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
  let I := ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hc
  let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
    rate source rewards C_star C_h hc
  let E := ReferenceFirstWindowNumericalStream.actualFirstLiveRun
    rate source rewards C_star C_h hc count hspan
  let W := ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
    rate source rewards C_star C_h hc count hspan
  let cells := ReferenceFirstWindowNumericalStream.actualLiveSourceCells
    rate source rewards C_star C_h hc count hspan
  let q := ReferenceFirstLaunchNumericalCell.queueParameters rate
  let κ := UnstoppedRecordedQueueComparison.firstOverflowPrefix q cells
  let J := ActualInitializationPhysicalStep.selectedRowIndex p source
  have hcellsLength : cells.length = W.length := by
    exact ReferenceFirstWindowNumericalStream.actualLiveSourceCells_length
      rate source rewards C_star C_h hc count hspan
  have hwindowPrefix : W.IsPrefix E.records := List.takeWhile_prefix _
  have hcount : E.records.length = count :=
    ReferenceActivePhysicalHorizon.run_record_count I source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s count hspan
      seed.activeAtStart
  have hwindowBound : W.length ≤ count := hwindowPrefix.length_le.trans_eq hcount
  have hbcount : b ≤ count := hb.trans hwindowBound
  have hcellEnabled (k : Fin W.length) :
      (ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
        rate source rewards C_star C_h hc count hspan k).input.enabled = true := by
    rcases ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt_facts
        rate source rewards C_star C_h hc count hspan k with
      ⟨_, _, _, _, henabled, _, _, _, _⟩
    exact henabled
  have hsourceReplay (n : ℕ) (a : Fin p.K) :
      UnstoppedRecordedQueueComparison.unstoppedReplay q cells n a =
        QueueReplay.replay (4 * rate.n) (0, 0)
          ((cells.take n).map fun cell =>
            (cell.enabled, RecordedQueueRun.quantizedArrival q cell a)) := by
    have hmap :
        (cells.take n).map (fun cell =>
          UnstoppedRecordedQueueComparison.unstoppedRecord q cell a) =
        (cells.take n).map (fun cell =>
          (cell.enabled, RecordedQueueRun.quantizedArrival q cell a)) := by
      apply List.map_congr_left
      intro cell hmem
      have hmemCells : cell ∈ cells := List.mem_of_mem_take hmem
      obtain ⟨j, hj⟩ := List.getElem_of_mem hmemCells
      rcases hj with ⟨hjlen, hindexed⟩
      have hjwindow : j < W.length := by rw [← hcellsLength]; exact hjlen
      let k : Fin W.length := ⟨j, hjwindow⟩
      have hget := ReferenceFirstWindowNumericalStream.actualLiveSourceCells_get
        rate source rewards C_star C_h hc count hspan k
      have hget' : cells[j]'hjlen =
          (ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
            rate source rewards C_star C_h hc count hspan k).input := by
        simpa only [cells, k] using hget
      rw [hindexed.symm, hget']
      simp [UnstoppedRecordedQueueComparison.unstoppedRecord, hcellEnabled k]
    unfold UnstoppedRecordedQueueComparison.unstoppedReplay
    rw [hmap]
    rfl
  have hcellBound (n : ℕ) (hn : n ≤ W.length) : n ≤ cells.length := by
    rw [hcellsLength]
    exact hn
  have hstate := UnstoppedRecordedQueueComparison.prefix_state_comparison q cells b
    (hcellBound b hb)
  have hsourceAtB : ∀ a : Fin p.K,
      UnstoppedRecordedQueueComparison.unstoppedReplay q cells b a =
        QueueReplay.replay (4 * rate.n) (0, 0)
          ((cells.take b).map fun cell =>
            (cell.enabled, RecordedQueueRun.quantizedArrival q cell a)) := by
    intro a
    exact hsourceReplay b a
  have hstopAtB : ∀ a : Fin p.K,
      (RecordedQueueRun.run q (cells.take b)).registers a =
        UnstoppedRecordedQueueComparison.unstoppedReplay q cells (min b κ) a :=
    hstate.1
  have hoverflow :
      (RecordedQueueRun.run q (cells.take b)).overflow = true ↔ κ ≤ b := hstate.2
  have hC := ReferenceFirstLiveComplementQueueReplay.actual_first_live_complement_prefix_replay
    rate source rewards C_star C_h hc count hspan b hb
  dsimp only [s, I, seed, E, W, cells] at hC
  rcases hC with ⟨hprefix, hCzero, hCpositive⟩
  refine ⟨hprefix, hsourceAtB, hstopAtB, hoverflow, ?_, ?_⟩
  · intro hbκ
    refine ⟨hprefix, ?_⟩
    constructor
    · intro hbzero
      subst b
      have hFzero : ∀ i : Fin (p.m - 1),
          ∃ sb mb,
            (ReferenceActivePhysicalHorizon.run I source.1.2 J rewards s 0
              hprefix seed.activeAtStart).finalState.followers i = .ordinary sb mb ∧
            sb = seed.followers i ∧ mb = seed.memory i ∧
            sb.lastDown = none ∧ sb.status = .unoccupied ∧ sb.S = 0 ∧
            sb.delta = 0 ∧ sb.backlog = 0 ∧ sb.buffer = (seed.followers i).buffer := by
        intro i
        have hF := ReferenceFirstLiveFollowerQueueReplay.actual_first_live_follower_prefix_replay
          rate source rewards C_star C_h hc count hspan i 0 hb
        dsimp only at hF
        rcases hF with ⟨_, sb, mb, hstate, hzero, _⟩
        have hz := hzero rfl
        exact ⟨sb, mb, hstate,
          hz.1, hz.2.1, hz.2.2.1, hz.2.2.2.1, hz.2.2.2.2.1,
          hz.2.2.2.2.2.1, hz.2.2.2.2.2.2.1, hz.2.2.2.2.2.2.2⟩
      have hCzero' := hCzero rfl
      exact ⟨hCzero'.1, hCzero'.2, hFzero⟩
    · intro hbpos
      obtain ⟨r, owned, base, hlive, _hspanC, hsigma, hn, hbase, hbirthData,
        hcomplement⟩ :=
        hCpositive hbpos
      rcases hbirthData with ⟨birth, hbirthMem, hbirth, hbirthTime, _⟩
      have hCbirthSameBoundary : birth ∈
          (ReferenceActivePhysicalHorizon.run I source.1.2 J rewards s b
            hprefix seed.activeAtStart).records := hbirthMem
      have hpartition : ∀ a : Fin p.K,
          a ∈ r.payload.slowSet.val ↔
            ∃ i : Fin (p.m - 1), r.payload.assignment.assigned i = a := by
        intro a
        have hset :=
          CoordinatorRecorderComplementBridge.assignmentSlowSet_eq_payload r.payload
        have himage :
            (Finset.univ.image r.payload.assignment.assigned) = r.payload.slowSet.val :=
          congrArg Subtype.val hset
        rw [← himage]
        constructor
        · intro ha
          rcases Finset.mem_image.mp ha with ⟨i, _, hia⟩
          exact ⟨i, hia⟩
        · rintro ⟨i, hia⟩
          exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hia⟩
      have hfastCover : ∀ a : Fin p.K, a ∉ r.payload.slowSet.val →
          ∃ fast : FastArm r.payload.slowSet, fast.1 = a := by
        intro a ha
        refine ⟨⟨a, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ha⟩⟩, rfl⟩
      refine ⟨r, owned, base, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hpartition, hfastCover⟩
      · exact hlive
      · exact hsigma
      · exact hn
      · exact hbase
      · exact ⟨birth, hCbirthSameBoundary, hbirth, hbirthTime⟩
      · intro a
        rcases hcomplement a with
          ⟨_hrecords, _henabledRecords, hregs, hprev, _hscore, _hqueue, _hprevious, _hcells⟩
        have hregsStopped :
            (r.complementScores a, owned.queue a) =
              (RecordedQueueRun.run q (cells.take b)).registers a.1 := by
          calc
            (r.complementScores a, owned.queue a) =
                QueueReplay.replay (4 * rate.n) (0, 0)
                  ((cells.take b).map fun cell =>
                    (cell.enabled, RecordedQueueRun.quantizedArrival q cell a.1)) := hregs
            _ = UnstoppedRecordedQueueComparison.unstoppedReplay q cells b a.1 :=
              (hsourceReplay b a.1).symm
            _ = (RecordedQueueRun.run q (cells.take b)).registers a.1 := by
              have hmin : min b κ = b := Nat.min_eq_left hbκ
              simpa only [hmin] using (hstopAtB a.1).symm
        have hprevSource :
            owned.previousService a =
              (UnstoppedRecordedQueueComparison.unstoppedReplay q cells b a.1).1 -
                (UnstoppedRecordedQueueComparison.unstoppedReplay q cells (b - 1) a.1).1 := by
          have hcurrReplay := hsourceReplay b a.1
          have hprevReplay := hsourceReplay (b - 1) a.1
          simpa only [hcurrReplay, hprevReplay] using hprev
        exact ⟨hregsStopped, hprevSource⟩
      · intro i
        have hF := ReferenceFirstLiveFollowerQueueReplay.actual_first_live_follower_prefix_replay
          rate source rewards C_star C_h hc count hspan i b hb
        dsimp only [s, I, seed, E, W, cells] at hF
        rcases hF with ⟨hprefixF, sb, mb, hstate, hFzero, hFpositive⟩
        have hFboundary :
            (ReferenceActivePhysicalHorizon.run I source.1.2 J rewards s b
              hprefix seed.activeAtStart).finalState.followers i = .ordinary sb mb := by
          exact hstate
        obtain ⟨k0, _hk0, hbranches⟩ := hFpositive hbpos
        let cell0 := ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
          rate source rewards C_star C_h hc count hspan k0
        let P0 := cell0.selected.view.payload
        have hselection0 :
            W[k0.val].output.preparation.coordinator.selection = some cell0.selected :=
          cell0.selection_actual
        have hbirth0Result :=
          ReferenceFirstDownRecoveryBudget.run_first_selected_payload
            I source.1.2 J rewards s count hspan seed.activeAtStart seed.coordinatorFirst
        dsimp only [E, W] at hbirth0Result
        specialize hbirth0Result k0 cell0.selected hselection0
        rcases hbirth0Result with
          ⟨birth0, hbirth0Mem, _hbirth0Time, hbirth0, hsigma0, _⟩
        have hbirth0Full : birth0 ∈ E.records := by
          change birth0 ∈
            (ReferenceActivePhysicalHorizon.run I source.1.2 J rewards s count hspan
              seed.activeAtStart).records
          exact hbirth0Mem
        have hbirthFull : birth ∈ E.records := by
          obtain ⟨suffix, hrecords⟩ :=
            ReferenceCollectionPhaseHistory.run_records_prefix
              I source.1.2 J rewards s b (count - b) (by omega) seed.activeAtStart
          have hrecords' :
              (ReferenceActivePhysicalHorizon.run I source.1.2 J rewards s count hspan
                seed.activeAtStart).records =
              (ReferenceActivePhysicalHorizon.run I source.1.2 J rewards s b
                (by omega) seed.activeAtStart).records ++ suffix := by
            simpa only [Nat.add_sub_of_le hbcount] using hrecords
          change birth ∈
            (ReferenceActivePhysicalHorizon.run I source.1.2 J rewards s count hspan
              seed.activeAtStart).records
          rw [hrecords']
          exact List.mem_append_left _ hbirthMem
        have hP0Eq : P0 = r.payload :=
          ReferenceAssignmentPayloadChronology.run_birth_payload_eq_of_equal_sigma
            I source.1.2 J rewards s count hspan seed.activeAtStart
            birth0 birth P0 r.payload hbirth0Full hbirthFull hbirth0 hbirth
            (hsigma0.trans hsigma.symm)
        have hassigned0 : P0.assignment.assigned i = r.payload.assignment.assigned i :=
          congrArg (fun payload : AssignmentStartPayload.Input p rate.eta =>
            payload.assignment.assigned i) hP0Eq
        have hdown0 : P0.downRecord i = r.payload.downRecord i :=
          congrArg (fun payload : AssignmentStartPayload.Input p rate.eta =>
            payload.downRecord i) hP0Eq
        have hOccupied := hbranches.1
        have hUnoccupied := hbranches.2
        have hoccupiedTarget : sb.status ≠ .unoccupied →
            sb.lastDown = some (r.payload.downRecord i) ∧
            (sb.S, sb.backlog) =
              (RecordedQueueRun.run q (cells.take b)).registers
                (r.payload.assignment.assigned i) ∧
            sb.delta =
              (UnstoppedRecordedQueueComparison.unstoppedReplay q cells b
                (r.payload.assignment.assigned i)).1 -
              (UnstoppedRecordedQueueComparison.unstoppedReplay q cells (b - 1)
                (r.payload.assignment.assigned i)).1 ∧
            ∃ j : Fin W.length, j.val < b ∧
              ReferenceAcceptedUpFollowerHistory.RetainedDown W[j.val] i
                (r.payload.downRecord i) := by
          intro hoccupied
          rcases hOccupied hoccupied with
            ⟨hlast, hregs, hdelta, _hSbound, _hdbound, _hqbound, _hmass, hretained⟩
          have hregsStopped :
              (sb.S, sb.backlog) =
                (RecordedQueueRun.run q (cells.take b)).registers
                  (r.payload.assignment.assigned i) := by
            calc
              (sb.S, sb.backlog) =
                  QueueReplay.replay (4 * rate.n) (0, 0)
                    ((cells.take b).map fun cell =>
                      (cell.enabled, RecordedQueueRun.quantizedArrival q cell
                        (r.payload.assignment.assigned i))) := by
                simpa only [P0, cell0, hassigned0] using hregs
              _ = UnstoppedRecordedQueueComparison.unstoppedReplay q cells b
                    (r.payload.assignment.assigned i) :=
                (hsourceReplay b (r.payload.assignment.assigned i)).symm
              _ = (RecordedQueueRun.run q (cells.take b)).registers
                    (r.payload.assignment.assigned i) := by
                have hmin : min b κ = b := Nat.min_eq_left hbκ
                simpa only [hmin] using
                  (hstopAtB (r.payload.assignment.assigned i)).symm
          have hdeltaSource : sb.delta =
              (UnstoppedRecordedQueueComparison.unstoppedReplay q cells b
                (r.payload.assignment.assigned i)).1 -
              (UnstoppedRecordedQueueComparison.unstoppedReplay q cells (b - 1)
                (r.payload.assignment.assigned i)).1 := by
            simpa only [P0, cell0, hassigned0,
              hsourceReplay b (r.payload.assignment.assigned i),
              hsourceReplay (b - 1) (r.payload.assignment.assigned i)] using hdelta
          have hretained' : ∃ j : Fin W.length, j.val < b ∧
              ReferenceAcceptedUpFollowerHistory.RetainedDown W[j.val] i
                (r.payload.downRecord i) := by
            rcases hretained with ⟨j, hjb, hretained⟩
            exact ⟨j, hjb, by simpa only [P0, cell0, hdown0] using hretained⟩
          exact ⟨by simpa only [P0, cell0, hdown0] using hlast, hregsStopped, hdeltaSource,
            hretained'⟩
        have hunoccupiedTarget : sb.status = .unoccupied →
            sb.lastDown = none ∧ sb.S = 0 ∧ sb.delta = 0 ∧ sb.backlog = 0 ∧
            sb.buffer = (seed.followers i).buffer ++
              (E.records.take b).flatMap
                (ReferenceFollowerBufferProvenance.logEmission i) ∧
            ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords
              E.records i b (r.payload.downRecord i) b =
              ((cells.take b).map fun cell =>
                (cell.enabled, RecordedQueueRun.quantizedArrival q cell
                  (r.payload.assignment.assigned i))) ∧
            QueueReplay.replay (4 * rate.n) (0, 0)
              (ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords
                E.records i b (r.payload.downRecord i) b) =
              UnstoppedRecordedQueueComparison.unstoppedReplay q cells b
                (r.payload.assignment.assigned i) := by
          intro hunoccupied
          rcases hUnoccupied hunoccupied with
            ⟨hlast, hS, hdelta, hbacklog, hbuffer, hreplyRecords⟩
          have hreplyRecords' :
              ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords
                E.records i b (r.payload.downRecord i) b =
                (cells.take b).map fun cell =>
                  (cell.enabled, RecordedQueueRun.quantizedArrival q cell
                    (r.payload.assignment.assigned i)) := by
            simpa only [E, cells, P0, cell0, hdown0, hassigned0] using hreplyRecords
          have hvirtualReplay := congrArg
            (fun records : List (Bool × ℕ) => QueueReplay.replay (4 * rate.n) (0, 0) records)
            hreplyRecords'
          have hsourceReplay' := hsourceReplay b (r.payload.assignment.assigned i)
          exact ⟨hlast, hS, hdelta, hbacklog, by simpa only [E] using hbuffer,
            hreplyRecords', hvirtualReplay.trans hsourceReplay'.symm⟩
        exact ⟨sb, mb, hFboundary, hoccupiedTarget, hunoccupiedTarget⟩
  · intro hκ
    have hcrossAll := UnstoppedRecordedQueueComparison.replay_crosses_overflow_at_first
      q cells hκ
    have hnormalizedAll :=
      (UnstoppedRecordedQueueComparison.replay_crosses_overflow_iff_normalized q cells κ).mp
        hcrossAll
    rcases hcrossAll with ⟨a, hcross⟩
    rcases hnormalizedAll with ⟨aNorm, hnormalized⟩
    have hstopAtKappa (arm : Fin p.K) :
        (RecordedQueueRun.run q (cells.take κ)).registers arm =
          UnstoppedRecordedQueueComparison.unstoppedReplay q cells κ arm := by
      have hcomparison :=
        UnstoppedRecordedQueueComparison.prefix_state_comparison q cells κ hκ
      simpa only [κ, Nat.min_self] using hcomparison.1 arm
    have hintStopped :
        32 * ((RecordedQueueRun.run q (cells.take κ)).registers a).2 > D p := by
      rw [hstopAtKappa a]
      simpa [κ, q, ReferenceFirstLaunchNumericalCell.queueParameters] using hcross
    have hnormalizedStopped :
        (((RecordedQueueRun.run q (cells.take κ)).registers aNorm).2 : ℝ) /
            (rate.n : ℝ) > 1 / (32 * rate.eta.val) := by
      rw [hstopAtKappa aNorm]
      simpa [κ, q, ReferenceFirstLaunchNumericalCell.queueParameters] using hnormalized
    refine ⟨?_, ⟨a, hintStopped⟩, ⟨aNorm, hnormalizedStopped⟩⟩
    · intro arm
      exact hstopAtKappa arm

end Bandits.Support.ReferenceFirstLiveStoppedQueueComparison

end
