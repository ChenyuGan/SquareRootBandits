/-
Copyright (c) 2026 The Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionDownSecondPureBank

import Lean.Elab.Tactic.Omega

/-!
# Actual first-collection DOWN boundary producers

This module exposes the actual ordinary follower input at each positive
coordinate of the canonical first-collection window, along with the actual
cutoff input before its PREPARE reset.  These boundary producers are inputs to
the remaining local quota and physical-detection argument; they do not by
themselves assert threshold attainment or physical acceptance.

Sources: `sources/zip4/manuscript/06_interruptions.tex:476-481`,
`sources/zip4/manuscript/05_binary_transport.tex:27-53,100-124`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:139-157`.

These are internal deterministic results.  They assert no source-event
membership, stopping-time law, UP allowance, composite quota, waiting bound,
probability estimate, or manuscript theorem closure.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions
open ReferenceActivePhysicalStep (Selection)

namespace Bandits.Support.ReferenceFirstCollectionDownThresholdDetection

variable {p : Parameters}

private theorem generated_run_eq_actual
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (count : ℕ)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed + count ≤ p.T) :
    ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun
        rate source rewards C_star C_h hcross
        (ReferenceInitializationRun.elapsed p
          (ReferenceInitializationRun.output
            (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed)
        rfl count hspan =
      ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count hspan := by
  have hlaunch := ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
    rate source rewards C_star C_h hcross
  have hstate : ReferenceFirstCollectionEpochAlignment.actualLaunchState
      rate source rewards C_star C_h hcross =
        ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hcross := by
    unfold ReferenceFirstCollectionEpochAlignment.actualLaunchState
    exact (Option.get_of_eq_some
      ((ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
        rate source rewards C_star C_h).2 hcross) hlaunch).symm
  simp only [ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun,
    ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun]
  cases hstate
  rfl

private theorem actual_down_positive_step_length
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (n : Fin records.length) (i : Fin (p.m - 1)) :
    let before := ReferenceFollowerDownDecoderReplay.actualDownPositives i (records.take n.val)
    let after := ReferenceFollowerDownDecoderReplay.actualDownPositives i
      (records.take (n.val + 1))
    before.length ≤ after.length ∧ after.length ≤ before.length + 1 := by
  classical
  let record := records[n.val]
  let call := ReferenceFollowerDownDecoderReplay.actualDownCall i record
  let positives := ReferenceFollowerDownDecoderReplay.positiveCallEntries
    (call.toList)
  have htake : records.take (n.val + 1) = records.take n.val ++ [record] := by
    exact List.take_succ_eq_append_getElem n.isLt
  have hsplit : ReferenceFollowerDownDecoderReplay.actualDownPositives i
      (records.take (n.val + 1)) =
      ReferenceFollowerDownDecoderReplay.actualDownPositives i (records.take n.val) ++ positives := by
    change ReferenceFollowerDownDecoderReplay.positiveCallEntries
      (ReferenceFollowerDownDecoderReplay.actualDownCalls i (records.take (n.val + 1))) = _
    rw [htake]
    unfold ReferenceFollowerDownDecoderReplay.actualDownCalls
    rw [List.filterMap_append]
    simp only [List.filterMap_cons, List.filterMap_nil]
    unfold ReferenceFollowerDownDecoderReplay.positiveCallEntries
    rw [List.flatMap_append]
    rfl
  have hlen : positives.length ≤ 1 := by
    cases hc : ReferenceFollowerDownDecoderReplay.actualDownCall i record with
    | none => simp [positives, call, hc,
        ReferenceFollowerDownDecoderReplay.positiveCallEntries]
    | some current =>
        simp only [positives, call, hc, Option.toList_some,
          ReferenceFollowerDownDecoderReplay.positiveCallEntries,
          List.flatMap_cons, List.flatMap_nil, List.append_nil]
        unfold AffineBatchDecoder.positiveAt
        split <;> simp
  rw [hsplit]
  simp only [List.length_append]
  omega

private theorem first_crossing
    (total quota : ℕ) (count : ℕ → ℕ)
    (hzero : count 0 = 0)
    (hstep : ∀ n, n < total → count (n + 1) ≤ count n + 1)
    (hquota : 1 < quota) (hreach : quota ≤ count total) :
    ∃ rounds, 0 < rounds ∧ rounds ≤ total ∧ count rounds = quota ∧
      count (rounds - 1) < quota := by
  classical
  let rounds := Nat.find (show ∃ n, quota ≤ count n from ⟨total, hreach⟩)
  have hfound : quota ≤ count rounds := Nat.find_spec (show ∃ n, quota ≤ count n from ⟨total, hreach⟩)
  have hmin (n : ℕ) (hn : n < rounds) : count n < quota := by
    have hnot := Nat.find_min (show ∃ n, quota ≤ count n from ⟨total, hreach⟩) hn
    omega
  have hle : rounds ≤ total := by
    by_contra h
    have htotal : total < rounds := by omega
    have hnot := hmin total htotal
    omega
  have hpos : 0 < rounds := by
    by_contra h
    have : rounds = 0 := by omega
    simp [this, hzero] at hfound
    omega
  have hprev : count (rounds - 1) < quota := hmin (rounds - 1) (by omega)
  have hbound := hstep (rounds - 1) (by omega)
  have hprevSucc : rounds - 1 + 1 = rounds := by omega
  rw [hprevSucc] at hbound
  have heq : count rounds = quota := by omega
  exact ⟨rounds, hpos, hle, heq, hprev⟩

/-- Actual ordinary inputs at every positive focal coordinate of the canonical
first-collection window.  The incoming local state, occupied/unoccupied
branch, cutoff payload, batch bounds, and coordinator dagger alternative all
come from the generated-prefix boundary on the same original run. -/
theorem actual_first_collection_down_positive_boundary
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (count : ℕ)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed + count ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count hspan).records).length < count)
    (n : Fin (ReferenceCollectionPhaseHistory.collectionWindow
      (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count hspan).records
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
          rate source rewards C_star C_h hcross count hspan).records).length).length)
    (hn : 0 < n.val) (i : Fin (p.m - 1)) :
    ∃ cutoffPayload before memory,
      (ReferenceCollectionPhaseHistory.collectionWindow
        (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
          rate source rewards C_star C_h hcross count hspan).records
        (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
          (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
            rate source rewards C_star C_h hcross count hspan).records).length)[n.val].input.state.followers i =
          .ordinary before memory ∧
      before.status = .unoccupied ∧
      ActiveFollowerLifecycle.localStateDomainValid before ∧
      ActiveFollowerLifecycle.localBufferValid before ∧
      ActiveFollowerLifecycle.downDecoderStateValid before ∧
      before.S ≤ p.T * D p ∧
      before.delta ≤ D p ∧
      before.backlog ≤ p.T * D p ∧
      before.S + before.backlog ≤
        (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
          (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
            rate source rewards C_star C_h hcross count hspan).records).length * D p ∧
      (∀ saved ∈ before.buffer, 1 ≤ saved.calendarRound ∧
        saved.calendarRound ≤ p.T) ∧
      (before.buffer.map (fun saved => (saved.calendarRound, saved.pilot))).Nodup ∧
      (∀ saved ∈ before.buffer, ∃ q : ℕ, q ≤ D p ∧
        saved.observation.val = (q : ℝ) / (D p : ℝ)) ∧
      before.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) ∧
      (∀ saved ∈ before.buffer,
        saved.calendarRound <
          ReferenceInitializationRun.elapsed p
            (ReferenceInitializationRun.output
              (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed +
          (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
            (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
              rate source rewards C_star C_h hcross count hspan).records).length + n.val + 1) ∧
      before.downBatch.pending.length < AffineBatchDecoder.quota p ∧
      (∀ batch ∈ before.downBatch.completed,
        batch.length = AffineBatchDecoder.quota p) ∧
      (before.lastDown = none ∧ before.S = 0 ∧ before.delta = 0 ∧ before.backlog = 0 ∨
        before.lastDown = some (cutoffPayload.downRecord i)) ∧
      ((ReferenceCollectionPhaseHistory.collectionWindow
        (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
          rate source rewards C_star C_h hcross count hspan).records
        (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
          (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
            rate source rewards C_star C_h hcross count hspan).records).length)[n.val].input.state.coordinator =
          .dagger ∨
        ∃ ledger saved,
          (ReferenceCollectionPhaseHistory.collectionWindow
            (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
              rate source rewards C_star C_h hcross count hspan).records
            (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
              (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
                rate source rewards C_star C_h hcross count hspan).records).length)[n.val].input.state.coordinator =
            .collection cutoffPayload ledger saved) := by
  classical
  let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
    rate source rewards C_star C_h hcross count hspan
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length
  let B := ReferenceCollectionPhaseHistory.collectionWindow E.records w
  let generated := ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun
    rate source rewards C_star C_h hcross
    (ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed)
    rfl count hspan
  have hrun := generated_run_eq_actual rate source rewards C_star C_h hcross count hspan
  have hshortGenerated : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      generated.records).length < count := by
    simpa [generated, E, hrun] using hshort
  have hprefixRaw :=
    ReferenceGeneratedFirstCollectionFollowerPrefix.actual_first_collection_follower_prefix_boundary
      rate source rewards C_star C_h hcross
      (ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed)
      rfl count hspan hshortGenerated
  have hprefix := hprefixRaw
  simp only [hrun] at hprefix
  rcases hprefix with
    ⟨cutoffRegisters, cutoffOwned, cutoffBase, hcutCoordinator, _hcutSigma,
      _hcutQueue,
      ⟨_dispatched, _hstart, _ledger, _hinit, _hledger, _hdomain, _hclock,
        _hpending, _hnoAssignment, _selected, _hpreparedCoordinator,
        _hu, _huT, _huGrid, _hsigma, _hcutoff, _hscan,
        _hsuccessor, _hmoving, hboundaries, _hrecords⟩⟩
  let tail := (E.records.drop (w + 1)).takeWhile
    (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input)
  have hlenWindow : B.length = tail.length + 1 := by
    dsimp only [B, ReferenceCollectionPhaseHistory.collectionWindow]
    rw [List.length_append]
    have hcount : E.records.length = count := by
      simpa [E, ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun] using
        ReferenceActivePhysicalHorizon.run_record_count
          (ReferenceFirstCollectionEpochAlignment.actualLaunchState
            rate source rewards C_star C_h hcross)
          source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
          rewards _ count hspan
          (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
            rate source rewards C_star C_h hcross).1
    have hw : w < count := by simpa [E, w] using hshort
    have hhead : ((E.records.drop w).take 1).length = 1 := by
      simp only [List.length_take, List.length_drop]
      omega
    rw [hhead]
    exact Nat.add_comm 1 tail.length
  have hnTail : n.val - 1 < tail.length := by
    have hnB : n.val < B.length := n.isLt
    have hnWindow : n.val < tail.length + 1 := by
      have hnTransport : n.val < tail.length + 1 := hlenWindow ▸ hnB
      exact hnTransport
    omega
  have htailBound : w + 1 + tail.length ≤ count := by
    have htailPrefix : tail <+: E.records.drop (w + 1) := List.takeWhile_prefix _
    have htailLe := htailPrefix.length_le
    have hcount : E.records.length = count := by
      simpa [E, ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun] using
        ReferenceActivePhysicalHorizon.run_record_count
          (ReferenceFirstCollectionEpochAlignment.actualLaunchState
            rate source rewards C_star C_h hcross)
          source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
          rewards _ count hspan
          (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
            rate source rewards C_star C_h hcross).1
    have hdrop : (E.records.drop (w + 1)).length = count - (w + 1) := by
      simp [List.length_drop, hcount]
    rw [hdrop] at htailLe
    have hw : w + 1 ≤ count := by
      have hw' : w < count := by simpa [E, w] using hshort
      omega
    omega
  have hboundaryAt := hboundaries (n.val - 1) (Nat.le_of_lt hnTail)
  obtain ⟨incoming, memory, hstate, hstatus, hdomain, hbuffer, hdecoder,
    hS, hdelta, hbacklog, hmass, hcalendar, hnodup, hquantized,
    hpairwise, hchronology, hpending, hcompleted, hlast⟩ := hboundaryAt.2 i
  let prefixAt := fun (j : ℕ) (hj : j ≤ tail.length) =>
    ReferenceActivePhysicalHorizon.run
      (ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hcross)
      source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
      rewards
      (ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed)
      (w + 1 + j) (by omega)
      (ReferenceGeneratedFirstCutoffSurvival.generatedLaunchActive
        rate source rewards C_star C_h hcross
        (ReferenceInitializationRun.elapsed p
          (ReferenceInitializationRun.output
            (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed)
        rfl)
  let boundaryRun := prefixAt (n.val - 1) (Nat.le_of_lt hnTail)
  have hendpoints := ReferenceFirstCollectionReadyStep.actual_collection_window_prefix_endpoints
    rate source rewards C_star C_h count hcross hspan hshort n
  have hlaunch : ReferenceFirstCollectionEpochAlignment.actualLaunchState
      rate source rewards C_star C_h hcross =
        ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hcross := by
    have hgenerated := ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
      rate source rewards C_star C_h hcross
    have hactual : ReferenceCorrectedInitializationLaunch.correctedLaunch
        rate source rewards C_star C_h =
          some (ReferenceFirstCollectionEpochAlignment.actualLaunchState
            rate source rewards C_star C_h hcross) := by
      unfold ReferenceFirstCollectionEpochAlignment.actualLaunchState
      exact (Option.some_get _).symm
    exact Option.some.inj (hactual.symm.trans hgenerated)
  have hindex : w + 1 + (n.val - 1) = w + n.val := by omega
  have hboundaryState : B[n.val].input.state = boundaryRun.finalState := by
    have hgenerated := ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
      rate source rewards C_star C_h hcross
    simpa [E, B, w, boundaryRun, prefixAt, hindex,
      ReferenceFirstCollectionEpochAlignment.actualLaunchState,
      ReferenceFirstLaunchNumericalCell.launchState, hgenerated] using hendpoints.1
  have hboundaryCoordinator : B[n.val].input.state.coordinator = .dagger ∨
      ∃ ledger saved,
        B[n.val].input.state.coordinator = .collection cutoffRegisters.payload ledger saved := by
    rcases hboundaryAt.1 with hdagger | ⟨ledger, saved, hcollection⟩
    · exact Or.inl (by
        rw [hboundaryState]
        simpa only [boundaryRun, prefixAt] using hdagger)
    · exact Or.inr ⟨ledger, saved, by
        rw [hboundaryState]
        simpa only [boundaryRun, prefixAt] using hcollection⟩
  have hlast' : incoming.lastDown = none ∧ incoming.S = 0 ∧
      incoming.delta = 0 ∧ incoming.backlog = 0 ∨
      incoming.lastDown = some (cutoffRegisters.payload.downRecord i) := hlast
  refine ⟨cutoffRegisters.payload, incoming, memory, ?_, hstatus, hdomain,
    hbuffer, hdecoder, hS, hdelta, hbacklog, ?_, hcalendar, hnodup,
    hquantized, hpairwise, ?_, hpending, hcompleted, hlast', hboundaryCoordinator⟩
  · exact (congrArg (fun state => state.followers i) hboundaryState).trans hstate
  · simpa [E, w] using hmass
  · intro saved hsaved
    have h := hchronology saved hsaved
    omega

/-- The actual cutoff input is retained before PREPARE.  Its incoming status
may be occupied; the theorem exposes the literal PREPARE reset on this same
record and the generated cutoff payload. -/
theorem actual_first_collection_down_cutoff_seed
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (count : ℕ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed + count ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count hspan).records).length < count) :
    let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
      rate source rewards C_star C_h hcross count hspan
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length
    let B := ReferenceCollectionPhaseHistory.collectionWindow E.records w
    ∀ i : Fin (p.m - 1),
    ∃ hBlen : 0 < B.length,
    ∃ registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta,
      ∃ owned : CoordinatorLiveServiceFinish.OwnedRegisters registers,
      ∃ base : Fin (p.m - 1) → ℕ,
      ∃ old : ReferencePrelaunchFollower.State p rate.eta,
      ∃ memory : ActiveFollowerLifecycle.LocalMemory p,
        (B[0]'hBlen).input.state.coordinator = .live registers owned base ∧
        registers.payload.sigma.val =
          ReferenceInitializationRun.elapsed p
            (ReferenceInitializationRun.output
              (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed ∧
        (∀ j : Fin (p.m - 1), (registers.payload.downRecord j).val.q = 0) ∧
        (B[0]'hBlen).input.state.followers i = .ordinary old memory ∧
        (old.status = .unoccupied →
          old.lastDown = none ∧ old.S = 0 ∧ old.delta = 0 ∧ old.backlog = 0) ∧
        (old.status ≠ .unoccupied →
          old.lastDown = some (registers.payload.downRecord i)) ∧
        ActiveFollowerLifecycle.localStateDomainValid old ∧
        ActiveFollowerLifecycle.localBufferValid old ∧
        ActiveFollowerLifecycle.downDecoderStateValid old ∧
        ActiveFollowerLifecycle.startRound rate.eta (B[0]'hBlen).input.time old memory =
          .ok ({old with status := .unoccupied}, memory) := by
  classical
  dsimp only
  intro i
  let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
    rate source rewards C_star C_h hcross count hspan
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length
  let B := ReferenceCollectionPhaseHistory.collectionWindow E.records w
  let generated := ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun
    rate source rewards C_star C_h hcross
    (ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed)
    rfl count hspan
  have hrun := generated_run_eq_actual rate source rewards C_star C_h hcross count hspan
  have hshortGenerated : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      generated.records).length < count := by
    simpa [generated, E, hrun] using hshort
  have hseedRaw :=
    ReferenceGeneratedFirstCutoffFollowerSeed.actual_first_cutoff_follower_seed
      rate source rewards C_star C_h hcross
      (ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed)
      rfl count hspan hshortGenerated
  have hseed := hseedRaw
  simp only [hrun] at hseed
  rcases hseed with
    ⟨registers, owned, base, _hcutCoordinator, _hsigma, _hqueue,
      ⟨_dispatched, _hstartRound, _ledger, _hinit, _hledger, _hdomain,
        _hclock, _hpending, _hnoAssignment, _selected, _hprepared,
        _hu, _huT, _hfirstCutoff, hfollowers, _hsuccessor⟩⟩
  let tail := (E.records.drop (w + 1)).takeWhile
    (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input)
  have hcount : E.records.length = count := by
    simpa [E, ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun] using
      ReferenceActivePhysicalHorizon.run_record_count
        (ReferenceFirstCollectionEpochAlignment.actualLaunchState
          rate source rewards C_star C_h hcross)
        source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
        rewards _ count hspan
        (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
          rate source rewards C_star C_h hcross).1
  have hw : w < count := by simpa [E, w] using hshort
  have hhead : ((E.records.drop w).take 1).length = 1 := by
    simp only [List.length_take, List.length_drop]
    omega
  have hlenWindow : B.length = tail.length + 1 := by
    dsimp only [B, ReferenceCollectionPhaseHistory.collectionWindow]
    rw [List.length_append, hhead]
    exact Nat.add_comm 1 tail.length
  have hBzero : 0 < B.length := by rw [hlenWindow]; omega
  have hwindowTime := ReferenceFirstCollectionEpochAlignment.actual_first_collection_window_time
    rate source rewards C_star C_h count hcross hspan hshort
  have hlookup : E.records[w]? = some (B[0]'hBzero) := by
    simpa [E, B, w] using (hwindowTime ⟨0, hBzero⟩).1
  have hindex : w < E.records.length := by rw [hcount]; exact hw
  have hrecord : E.records[w]'hindex = B[0]'hBzero :=
    Option.some.inj ((List.getElem?_eq_getElem hindex).symm.trans hlookup)
  obtain ⟨old, memory, choice, logged, diagnostic, recordPost, post,
    hinput, hunoccupied, hoccupied, hdomain, hbuffer, hdecoder, _hpair, _hstamps,
    hreset, _hprepared, _hchoice, _hchoiceDomain, _⟩ := hfollowers i
  have hinputB : (B[0]'hBzero).input.state.followers i = .ordinary old memory := by
    have hinput' : (E.records[w]'hindex).input.state.followers i =
        .ordinary old memory := by simpa [E] using hinput
    rw [← hrecord]
    exact hinput'
  have hresetB : ActiveFollowerLifecycle.startRound rate.eta (B[0]'hBzero).input.time old memory =
      .ok ({old with status := .unoccupied}, memory) := by
    have hreset' : ActiveFollowerLifecycle.startRound rate.eta
        (E.records[w]'hindex).input.time old memory =
          .ok ({old with status := .unoccupied}, memory) := by
      simpa [E] using hreset
    rw [← hrecord]
    exact hreset'
  have hcoordB : (B[0]'hBzero).input.state.coordinator = .live registers owned base := by
    have hcoord' : (E.records[w]'hindex).input.state.coordinator =
        .live registers owned base := by
      simpa [E] using _hcutCoordinator
    rw [← hrecord]
    exact hcoord'
  exact ⟨hBzero, registers, owned, base, old, memory, hcoordB, _hsigma,
    _hqueue, hinputB, hunoccupied, hoccupied, hdomain, hbuffer, hdecoder, hresetB⟩

end Bandits.Support.ReferenceFirstCollectionDownThresholdDetection
