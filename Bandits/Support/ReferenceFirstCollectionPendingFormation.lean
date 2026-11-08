/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionUpConditionalService
public import Bandits.Support.ReferenceFirstCollectionStreamEmptyDispatch

import Lean.Elab.Tactic.Omega

/-!
# Actual pending first-collection follower formation

Sources: `sources/zip4/manuscript/06_interruptions.tex:477-481`,
`sources/zip4/manuscript/05_binary_transport.tex:48-53,70-88,100-124`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:44-64,100-108,157`.

This module joins the actual initialized collection stream to the public
generated follower-prefix boundary. The result is internal physical evidence
over the original source, reward table, and corrected launch.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions

namespace Bandits.Support.ReferenceFirstCollectionPendingFormation

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput
abbrev RewardTable := ActualInitializationPhysicalStep.GridRewardTable
abbrev Payload {p : Parameters} (rate : RateInput p) :=
  ReferenceActivePhysicalStep.Payload rate
abbrev Ledger {p : Parameters} (rate : RateInput p) :=
  ReferenceActivePhysicalStep.Ledger rate

variable {p : Parameters} {rate : RateInput p}

private theorem generated_pending_follower_boundary
    (source : SourceInput p) (rewards : RewardTable p)
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
    ∃ (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
      (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
      (base : Fin (p.m - 1) → ℕ)
      (cutRecord : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)),
      E.records[w]? = some cutRecord ∧
      cutRecord.input.state.coordinator = .live registers owned base ∧
      ∀ (n : Fin B.length), 0 < n.val →
        ∀ i : Fin (p.m - 1),
          ∃ state memory,
            B[n.val].input.state.followers i = .ordinary state memory ∧
            state.status = .unoccupied ∧
            ActiveFollowerLifecycle.localStateDomainValid state ∧
            state.S ≤ p.T * D p ∧ state.delta ≤ D p ∧ state.backlog ≤ p.T * D p ∧
            state.S + state.backlog ≤ w * D p ∧
            state.downBatch.pending.length < AffineBatchDecoder.quota p ∧
            (∀ batch ∈ state.downBatch.completed,
              batch.length = AffineBatchDecoder.quota p) ∧
            ((state.lastDown = none ∧ state.S = 0 ∧ state.delta = 0 ∧ state.backlog = 0) ∨
              state.lastDown = some (registers.payload.downRecord i)) := by
  classical
  let start := ReferenceInitializationRun.elapsed p
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
  let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
    rate source rewards C_star C_h hcross count hspan
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length
  let B := ReferenceCollectionPhaseHistory.collectionWindow E.records w
  let tail := (E.records.drop (w + 1)).takeWhile
    (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input)
  let launch := ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hcross
  let active := ReferenceGeneratedFirstCutoffSurvival.generatedLaunchActive
    rate source rewards C_star C_h hcross start rfl
  have hrunAlignment :
      ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun
          rate source rewards C_star C_h hcross start rfl count hspan = E := by
    have hgenerated := ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
      rate source rewards C_star C_h hcross
    have hactual : ReferenceCorrectedInitializationLaunch.correctedLaunch
        rate source rewards C_star C_h =
          some (ReferenceFirstCollectionEpochAlignment.actualLaunchState
            rate source rewards C_star C_h hcross) := by
      unfold ReferenceFirstCollectionEpochAlignment.actualLaunchState
      exact (Option.some_get _).symm
    have hlaunch : ReferenceFirstCollectionEpochAlignment.actualLaunchState
        rate source rewards C_star C_h hcross = launch := by
      dsimp only [launch]
      exact Option.some.inj (hactual.symm.trans hgenerated)
    change ReferenceActivePhysicalHorizon.run launch source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start count hspan active =
      ReferenceActivePhysicalHorizon.run
        (ReferenceFirstCollectionEpochAlignment.actualLaunchState
          rate source rewards C_star C_h hcross)
        source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
        rewards start count hspan
        (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
          rate source rewards C_star C_h hcross).1
    cases hlaunch
    rfl
  have hshortGenerated :
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun
          rate source rewards C_star C_h hcross start rfl count hspan).records).length < count := by
    simpa only [hrunAlignment] using hshort
  have htailLength : B.length = tail.length + 1 := by
    dsimp [B, tail, ReferenceCollectionPhaseHistory.collectionWindow]
    rw [List.length_append]
    have hfirst : ((E.records.drop w).take 1).length = 1 := by
      simp only [List.length_take, List.length_drop]
      have hcount : E.records.length = count := by
        simpa [E, ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun] using
          ReferenceActivePhysicalHorizon.run_record_count
            (ReferenceFirstCollectionEpochAlignment.actualLaunchState
              rate source rewards C_star C_h hcross)
            source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
            rewards start count hspan
            (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
              rate source rewards C_star C_h hcross).1
      have hw : w < count := by simpa [E, w] using hshort
      rw [hcount]
      rw [Nat.min_eq_left (by omega : 1 ≤ count - w)]
    rw [hfirst]
    simp [Nat.add_comm]
  have hcount : E.records.length = count := by
    simpa [E, ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun] using
      ReferenceActivePhysicalHorizon.run_record_count
        (ReferenceFirstCollectionEpochAlignment.actualLaunchState
          rate source rewards C_star C_h hcross)
        source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
        rewards start count hspan
        (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
          rate source rewards C_star C_h hcross).1
  let generated := ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun
    rate source rewards C_star C_h hcross start rfl count hspan
  have hgenIndex : w < generated.records.length := by
    have hw : w < E.records.length := by rw [hcount]; omega
    simpa [generated, hrunAlignment] using hw
  let cutoffRecord := generated.records[w]'hgenIndex
  have hcutIndex : E.records[w]? = some cutoffRecord := by
    have hlookup : generated.records[w]? = some cutoffRecord :=
      List.getElem?_eq_getElem _
    simpa [generated, hrunAlignment] using hlookup
  have htailPrefix : tail <+: E.records.drop (w + 1) := List.takeWhile_prefix _
  have htailLe : tail.length ≤ (E.records.drop (w + 1)).length := htailPrefix.length_le
  have hdropLength : (E.records.drop (w + 1)).length = count - (w + 1) := by
    simp [hcount]
  have htailBound : w + 1 + tail.length ≤ count := by
    rw [hdropLength] at htailLe
    calc
      w + 1 + tail.length ≤ w + 1 + (count - (w + 1)) := Nat.add_le_add_left htailLe _
      _ = count := Nat.add_sub_of_le (by
        have hw : w < count := by simpa [E, w] using hshort
        omega)
  have hprefixRaw :=
    ReferenceGeneratedFirstCollectionFollowerPrefix.actual_first_collection_follower_prefix_boundary
      rate source rewards C_star C_h hcross start rfl count hspan hshortGenerated
  have hprefix := hprefixRaw
  simp only [hrunAlignment] at hprefix
  rcases hprefix with
    ⟨cutoffRegisters, cutoffOwned, cutoffBase, hcutCoordinator, _hcutStart,
      _hcutQueue,
      ⟨_dispatched, _hstart, _ledger, _hinit, _hledger, _hdomain, _hclock,
        _hpending, _hnoAssignment, _selected, _hpreparedCoordinator,
        _hu, _huT, _huGrid, _hsigma, _hcutoff, _hscan,
        _hsuccessor, _hmoving, hboundaries, _hrecords⟩⟩
  have hwE : w < E.records.length := by rw [hcount]; omega
  have hgetE : E.records[w]? = some (E.records[w]'hwE) := List.getElem?_eq_getElem _
  have hcutEq : cutoffRecord = E.records[w]'hwE :=
    Option.some.inj (hcutIndex.symm.trans hgetE)
  have hcutState : cutoffRecord.input.state.coordinator =
      .live cutoffRegisters cutoffOwned cutoffBase := by
    rw [hcutEq]
    exact hcutCoordinator
  refine ⟨cutoffRegisters, cutoffOwned, cutoffBase, cutoffRecord,
    hcutIndex, hcutState, ?_⟩
  intro n hn i
  have hnWindow : n.val < tail.length + 1 := by
    rw [← htailLength]
    exact n.isLt
  have hnTail : n.val - 1 < tail.length := by omega
  let boundaryRun := ReferenceActivePhysicalHorizon.run launch source.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start
    (w + 1 + (n.val - 1)) (by omega) active
  have hboundaryAt := hboundaries (n.val - 1) (by
    change n.val - 1 ≤ tail.length
    exact Nat.le_of_lt hnTail)
  rcases hboundaryAt with ⟨_hcoordinator, hfollowers⟩
  obtain ⟨state, memory, hstate, hstatus, hdomain, _hbuffer, _hdownDomain,
    hS, hdelta, hbacklog, hmass, _hcalendar, _hnodup, _hquantized,
    _hpairwise, _hbefore, hpending, hcompleted, hlast⟩ := hfollowers i
  have hendpoints := ReferenceFirstCollectionReadyStep.actual_collection_window_prefix_endpoints
    rate source rewards C_star C_h count hcross hspan hshort ⟨n.val, n.isLt⟩
  have hstateAt : B[n.val].input.state = boundaryRun.finalState := by
    have hstateAt' := hendpoints.1
    have hlaunch : ReferenceFirstCollectionEpochAlignment.actualLaunchState
        rate source rewards C_star C_h hcross = launch := by
      rfl
    have hindex : w + 1 + (n.val - 1) = w + n.val := by omega
    have hrunEq :
        ReferenceActivePhysicalHorizon.run launch source.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start
            (w + n.val) (by omega) active =
          ReferenceActivePhysicalHorizon.run
            (ReferenceFirstCollectionEpochAlignment.actualLaunchState
              rate source rewards C_star C_h hcross)
            source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
            rewards start (w + n.val) (by omega)
            (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
              rate source rewards C_star C_h hcross).1 := by
      cases hlaunch
      rfl
    calc
      B[n.val].input.state =
          (ReferenceActivePhysicalHorizon.run
            (ReferenceFirstCollectionEpochAlignment.actualLaunchState
              rate source rewards C_star C_h hcross)
            source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
            rewards start (w + n.val) (by omega)
            (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
              rate source rewards C_star C_h hcross).1).finalState := hstateAt'
      _ = (ReferenceActivePhysicalHorizon.run launch source.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start
            (w + n.val) (by omega) active).finalState :=
          (congrArg ReferenceActivePhysicalHorizon.Run.finalState hrunEq).symm
      _ = boundaryRun.finalState := by
          simp [boundaryRun, hindex]
  refine ⟨state, memory, ?_, hstatus, hdomain, hS, hdelta, hbacklog, ?_, hpending,
    hcompleted, ?_⟩
  · exact (congrArg (fun st => st.followers i) hstateAt).trans hstate
  · exact hmass
  · rcases hlast with hnone | hsome
    · exact Or.inl hnone
    · exact Or.inr hsome

/-- The original-source dispatch and the actual pending follower branch at
each positive stream coordinate. The stream cell is the real service record;
the follower split is obtained from G on the same collection window. -/
theorem actual_initialized_first_collection_pending_formation
    (rate : RateInput p) (source : SourceInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (count : ℕ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed + count ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count hspan).records).length < count) :
    ∃ d : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
        source rewards C_star C_h count hcross hspan hshort,
      let out := d.stream
      let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count hspan
      let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length
      ∃ (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
        (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
        (base : Fin (p.m - 1) → ℕ)
        (cutRecord : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)),
        E.records[w]? = some cutRecord ∧
        cutRecord.input.state.coordinator = .live registers owned base ∧
        registers.payload = out.payload ∧
        out.cutoff.ledger.pending = Finset.univ ∧
        (∀ (n : Fin out.ell), 0 < n.val →
          ∀ i : Fin (p.m - 1),
            i ∈ (out.ledgers ⟨n.val - 1, by omega⟩).pending →
              ∃ (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
                (incoming : Ledger rate)
                (cell : ReferenceFirstCollectionReadyStream.ContinuingStreamCell
                  source rewards E.records (w + n.val) count
                  (ReferenceInitializationRun.elapsed p
                    (ReferenceInitializationRun.output
                      (ActualReferenceInitializationBlock.referenceInput
                        source rewards C_star C_h rate)).completed)
                  r out.payload incoming out.saved)
                (state : ReferencePrelaunchFollower.State p rate.eta)
                (memory : ActiveFollowerLifecycle.LocalMemory p),
                out.window[n.val]? = some r ∧
                r.input.time.val + 1 =
                  ReferenceInitializationRun.elapsed p
                    (ReferenceInitializationRun.output
                      (ActualReferenceInitializationBlock.referenceInput
                        source rewards C_star C_h rate)).completed +
                    w + 1 + n.val ∧
                r.input.rows = source.1.2 ∧
                r.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p source ∧
                r.input.rewards = rewards ∧
                incoming = out.ledgers ⟨n.val - 1, by omega⟩ ∧
                i ∈ incoming.pending ∧
                ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain
                  r.input out.payload incoming out.saved ∧
                cell.serviceLedger = out.ledgers n ∧
                r.input.state.followers i = .ordinary state memory ∧
                state.status = .unoccupied ∧
                ActiveFollowerLifecycle.localStateDomainValid state ∧
                state.S ≤ p.T * D p ∧ state.delta ≤ D p ∧ state.backlog ≤ p.T * D p ∧
                state.S + state.backlog ≤ w * D p ∧
                state.downBatch.pending.length < AffineBatchDecoder.quota p ∧
                (∀ batch ∈ state.downBatch.completed,
                  batch.length = AffineBatchDecoder.quota p) ∧
                ((state.lastDown = none ∧ state.S = 0 ∧ state.delta = 0 ∧ state.backlog = 0) ∨
                  state.lastDown = some (out.payload.downRecord i)) ∧
        (state.lastDown = some (out.payload.downRecord i) →
                  ∃ U : OrdinaryMessageCodec.UpRecord
                      (ReferencePrelaunchFollower.codecParams p rate.eta),
                    U.val = ActiveFollowerQueueOperation.upOfferFields state ∧
            1 ≤ U.val.sigma ∧
            (ReferenceActivePhysicalStep.upSenderIndex r.input = i →
              PublicDiscreteDraws.slotDraw
                  (r.input.row.2 r.input.time).1 = PublicDiscreteDraws.upSlot →
                ((ReferenceActivePhysicalStep.prepare r.input).followers.followers i).configuration =
                    .ordinary state memory ∧
                ActiveFollowerQueueOperation.checkedUpOffer rate.eta i r.input.row
                  (r.input.state.activations i) r.input.time state = .offer U ∧
                ReferenceFollowerFixedReply.actualUpExpected r =
                  some ((OrdinaryMessageCodec.wordEquivFlat
                    (CoordinatorCollectionLedger.codecParams p rate.eta.val))
                    (OrdinaryMessageCodec.encodeUp
                      (CoordinatorCollectionLedger.codecParams p rate.eta.val) U))))) := by
  classical
  obtain ⟨d⟩ :=
    ReferenceFirstCollectionStreamEmptyDispatch.actual_initialized_first_collection_stream_empty_dispatch
      rate source rewards C_star C_h count hcross hspan hshort
  refine ⟨d, ?_⟩
  dsimp only
  let out := d.stream
  let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
    rate source rewards C_star C_h hcross count hspan
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length
  have hwindowEq : out.window =
      ReferenceCollectionPhaseHistory.collectionWindow E.records w := by
    simpa [out, E, w, ReferenceFirstCollectionReadyStream.actualWindow,
      ReferenceFirstCollectionReadyStream.actualEpoch,
      ReferenceFirstCollectionReadyStream.startTime] using out.windowIsActual
  obtain ⟨registers, owned, base, cutRecord, hcutIndex, hcutState, hlocal⟩ :=
    generated_pending_follower_boundary source rewards C_star C_h count
      hcross hspan hshort
  have hcutEq : cutRecord = out.cutoff.cut := by
    exact Option.some.inj (hcutIndex.symm.trans out.cutoff.cutIndex)
  obtain ⟨cutExecution⟩ := out.cutoffExecution
  have hactualCutState : out.cutoff.cut.input.state.coordinator =
      .live registers owned base := by
    rw [← hcutEq]
    exact hcutState
  have hliveEq :
      ReferenceActivePhysicalStep.CoordinatorConfiguration.live registers owned base =
        .live cutExecution.live cutExecution.owned cutExecution.base :=
    hactualCutState.symm.trans cutExecution.actualLive
  have hregisters : registers = cutExecution.live := by
    injection hliveEq with hregisters _ _
  have hpayloadEq : registers.payload = out.payload := by
    calc
      registers.payload = cutExecution.live.payload := congrArg
        (fun live : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta => live.payload)
        hregisters
      _ = out.cutoff.payload := cutExecution.payloadIsLive.symm
      _ = out.payload := out.payloadMatchesCutoff.symm
  refine ⟨registers, owned, base, cutRecord, hcutIndex, hcutState, hpayloadEq,
    out.cutoffPendingUniv, ?_⟩
  intro n hn i hi
  obtain ⟨j, r, incoming, cell, hj, hr, hservice, hprevious⟩ := out.cell_at n hn
  have hj' : j = w + n.val := by
    simpa [E, w, ReferenceFirstCollectionReadyStream.actualEpoch] using hj
  subst j
  have hiIncoming : i ∈ incoming.pending := by
    rw [hprevious]
    exact hi
  have hwindowBound : n.val < out.window.length := Nat.lt_of_lt_of_le n.isLt out.withinWindow
  let nWindow : Fin out.window.length := ⟨n.val, hwindowBound⟩
  have hwindowElem : out.window[n.val]? =
      some (out.window[n.val]'hwindowBound) := List.getElem?_eq_getElem _
  have hwindowEq' : r = out.window[n.val]'hwindowBound :=
    Option.some.inj (hr.symm.trans hwindowElem)
  have horiginal := out.originalInputs nWindow
  have htime : r.input.time.val + 1 =
      ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput
            source rewards C_star C_h rate)).completed + w + 1 + n.val := by
    rw [hwindowEq']
    simpa [nWindow, w, E, ReferenceFirstCollectionReadyStream.actualEpoch,
      ReferenceFirstCollectionReadyStream.startTime] using
      (out.alignment nWindow).2
  have hrows : r.input.rows = source.1.2 := by
    rw [hwindowEq']
    exact horiginal.1
  have hselected : r.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p source := by
    rw [hwindowEq']
    exact horiginal.2.1
  have hrewards : r.input.rewards = rewards := by
    rw [hwindowEq']
    exact horiginal.2.2
  have hBbound : n.val < (ReferenceCollectionPhaseHistory.collectionWindow E.records w).length := by
    simpa [hwindowEq] using hwindowBound
  let nB : Fin (ReferenceCollectionPhaseHistory.collectionWindow E.records w).length :=
    ⟨n.val, hBbound⟩
  have hlocalAt := hlocal nB (by simpa [nB] using hn) i
  obtain ⟨state, memory, hstateB, hstatus, hdomain, hS, hdelta, hbacklog,
    hmass, hbankPending, hcompleted, hlastB⟩ := hlocalAt
  have hrecordLookup :
      (ReferenceCollectionPhaseHistory.collectionWindow E.records w)[n.val]? = some r := by
    simpa [hwindowEq] using hr
  have hBlookup :
      (ReferenceCollectionPhaseHistory.collectionWindow E.records w)[n.val]? =
        some ((ReferenceCollectionPhaseHistory.collectionWindow E.records w)[n.val]'hBbound) :=
    List.getElem?_eq_getElem _
  have hrecordEq : r =
      (ReferenceCollectionPhaseHistory.collectionWindow E.records w)[n.val]'hBbound :=
    Option.some.inj (hrecordLookup.symm.trans hBlookup)
  have hstateR : r.input.state.followers i = .ordinary state memory := by
    rw [hrecordEq]
    exact hstateB
  have hlast :
      (state.lastDown = none ∧ state.S = 0 ∧ state.delta = 0 ∧ state.backlog = 0) ∨
        state.lastDown = some (out.payload.downRecord i) := by
    simpa only [hpayloadEq] using hlastB
  have hreadyB :
      ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain
        (ReferenceCollectionPhaseHistory.collectionWindow E.records w)[n.val].input
        out.payload incoming out.saved := by
    simpa [hrecordEq] using cell.readyInput
  have hformed : state.lastDown = some (out.payload.downRecord i) →
      ∃ U : OrdinaryMessageCodec.UpRecord
          (ReferencePrelaunchFollower.codecParams p rate.eta),
        U.val = ActiveFollowerQueueOperation.upOfferFields state ∧
        1 ≤ U.val.sigma ∧
        (ReferenceActivePhysicalStep.upSenderIndex r.input = i →
          PublicDiscreteDraws.slotDraw
              (r.input.row.2 r.input.time).1 = PublicDiscreteDraws.upSlot →
            ((ReferenceActivePhysicalStep.prepare r.input).followers.followers i).configuration =
                .ordinary state memory ∧
            ActiveFollowerQueueOperation.checkedUpOffer rate.eta i r.input.row
              (r.input.state.activations i) r.input.time state = .offer U ∧
            ReferenceFollowerFixedReply.actualUpExpected r =
              some ((OrdinaryMessageCodec.wordEquivFlat
                (CoordinatorCollectionLedger.codecParams p rate.eta.val))
                (OrdinaryMessageCodec.encodeUp
                  (CoordinatorCollectionLedger.codecParams p rate.eta.val) U))) := by
    intro hlastSome
    have hdown := (out.payload.downRecord i).property
    unfold OrdinaryMessageCodec.downAdmissible at hdown
    have hpositive : 1 ≤ ReferencePrelaunchFollower.acceptedStart state := by
      simp [ReferencePrelaunchFollower.acceptedStart, hlastSome, hdown.1]
    have hgeometry :=
      ReferenceFirstCollectionControlGeometry.actual_first_collection_control_geometry
        rate source rewards C_star C_h count hcross
        (ReferenceInitializationRun.elapsed p
          (ReferenceInitializationRun.output
            (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed)
        rfl hspan
    have hcontrol := hgeometry hshort nB (by simpa [nB] using hn)
      out.payload incoming out.saved hreadyB
      i state memory hstateB hiIncoming hpositive
    rcases hcontrol with ⟨U, hfields, hsigma, hforall⟩
    refine ⟨U, hfields, hsigma, ?_⟩
    intro hsender hslot
    let x := (ReferenceCollectionPhaseHistory.collectionWindow E.records w)[nB.val].input
    have hrB : r = (ReferenceCollectionPhaseHistory.collectionWindow E.records w)[nB.val]'hBbound := by
      simpa [nB] using hrecordEq
    have hsenderX : ReferenceActivePhysicalStep.upSenderIndex x = i := by
      simpa [x, hrB] using hsender
    have hslotX : PublicDiscreteDraws.slotDraw (x.row.2 x.time).1 =
        PublicDiscreteDraws.upSlot := by
      simpa [x, hrB] using hslot
    have hselectedX : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
        (x.row.2 x.time).1 = i := by
      apply Fin.ext
      have hdraw := congrArg Fin.val
        (CoordinatorUpMeasurability.selectedFollowerIndex_eq_draw (x.row.2 x.time))
      rw [← hdraw]
      simpa [ReferenceActivePhysicalStep.upSenderIndex] using
        congrArg Fin.val hsenderX
    have hchoiceCond := (hforall (x.row.2 x.time)).2.2.1
    have hxc : ReferenceLaterOptionalControlResampling.withControl x (x.row.2 x.time) = x := by
      cases x
      simp [ReferenceLaterOptionalControlResampling.withControl,
        ReferenceActivePhysicalStep.RoundInput.row]
    have hchosen := hchoiceCond ⟨hslotX, hselectedX⟩
    rcases hchosen with ⟨_harm, hconfiguration, hoff, _hother⟩
    rw [hxc] at hconfiguration hoff
    have hinput : r.input = x := by
      dsimp only [x]
      exact congrArg (fun record : ReferenceActivePhysicalHorizon.RoundRecord => record.input) hrB
    have hconfigurationR :
        ((ReferenceActivePhysicalStep.prepare r.input).followers.followers i).configuration =
          .ordinary state memory := by
      rw [hinput]
      exact hconfiguration
    have hoffR : ActiveFollowerQueueOperation.checkedUpOffer rate.eta i r.input.row
        (r.input.state.activations i) r.input.time state = .offer U := by
      rw [hinput]
      exact hoff
    have hconfigurationChoice :
        (ReferenceFollowerFixedReply.actualChoice r i).configuration =
          .ordinary state memory := by
      unfold ReferenceFollowerFixedReply.actualChoice
      rw [r.output_eq]
      exact hconfigurationR
    have hoffChoice : ActiveFollowerQueueOperation.checkedUpOffer rate.eta
        (ReferenceFollowerFixedReply.actualChoice r i).follower
        (ReferenceFollowerFixedReply.actualChoice r i).row
        (ReferenceFollowerFixedReply.actualChoice r i).activation
        (ReferenceFollowerFixedReply.actualChoice r i).time state = .offer U := by
      have halign := ReferenceFollowerFixedReply.actualChoice_alignment r i
      have hactivation :
          (ReferenceFollowerFixedReply.actualChoice r i).activation =
            r.input.state.activations i := by
        unfold ReferenceFollowerFixedReply.actualChoice
        rw [r.output_eq]
        exact ((ReferenceActivePhysicalStep.step r.input).preparation.follower_alignment i).2.2.2
      rw [halign.2.1, halign.1, hactivation, halign.2.2]
      exact hoffR
    have hencoded := ReferenceFollowerFixedReply.actualUpExpected_eq_encoded_offer
      r i hsender state memory hconfigurationChoice U hoffChoice
    exact ⟨hconfigurationR, hoffR, hencoded⟩
  refine ⟨r, incoming, cell, state, memory, hr, htime, hrows, hselected, hrewards,
    hprevious, hiIncoming,
    cell.readyInput, hservice, hstateR, hstatus, hdomain, hS, hdelta, hbacklog,
    hmass, hbankPending, hcompleted, hlast, hformed⟩

end Bandits.Support.ReferenceFirstCollectionPendingFormation

end
