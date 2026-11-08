/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceReleaseStrictPastFactor
public import Bandits.Support.ReferencePhysicalReleaseQuota

/-!
# Actual local release pending predecessors

Sources: `sources/zip4/manuscript/05_binary_transport.tex:74-88,293-348`,
`sources/zip4/manuscript/06_interruptions.tex:246-297,435-492`,
`sources/zip4/manuscript/07_public_setup.tex:121-164`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-79`.

This module inverts one actual follower operation at a locally gated live
record. Its source theorem uses the corrected launch seed and the original
whole physical run. It does not produce a multi-round release interval,
quota, stopped support, conditional service estimate, or regret bound.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceLocalReleasePendingPredecessor

open ConstructorDimensions ReferenceActivePhysicalStep

variable {p : Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}

local instance propDecidable (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

abbrev Record := ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)

private theorem local_gate_live_fields
    (b : ℕ) (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (hgate : ReferenceRetainedReleasePhaseObservation.localReleaseGate rate b x.time
      (ReferenceActivePhysicalStepMeasurability.encodeState x.state) = true) :
    ∃ registers owned base started,
      x.state.coordinator = .live registers owned base ∧
      registers.payload.sigma.val = b ∧ registers.pendingAtChoice = ∅ ∧
      registers.priorClock.sigma = some registers.payload.sigma ∧
      registers.priorClock.u = none ∧
      CoordinatorPhaseClock.startRound p rate.eta.val x.time registers.priorClock
        registers.clockPending = .ok started ∧
      CoordinatorLiveChoiceRecorderStep.unchangedLiveClockFrame
        (ReferenceActivePhysicalStep.liveRegistersAt registers x.time) started := by
  cases hc : x.state.coordinator with
  | first => simp [ReferenceRetainedReleasePhaseObservation.localReleaseGate,
      ReferenceActivePhysicalStepMeasurability.encodeState,
      ReferenceActivePhysicalStepMeasurability.encodeCoordinator, hc] at hgate
  | collection payload ledger proposal =>
      simp [ReferenceRetainedReleasePhaseObservation.localReleaseGate,
        ReferenceActivePhysicalStepMeasurability.encodeState,
        ReferenceActivePhysicalStepMeasurability.encodeCoordinator, hc] at hgate
  | dagger =>
      simp [ReferenceRetainedReleasePhaseObservation.localReleaseGate,
        ReferenceActivePhysicalStepMeasurability.encodeState,
        ReferenceActivePhysicalStepMeasurability.encodeCoordinator, hc] at hgate
  | live registers owned base =>
      have hgate' := hgate
      simp only [ReferenceRetainedReleasePhaseObservation.localReleaseGate,
        ReferenceActivePhysicalStepMeasurability.encodeState,
        ReferenceActivePhysicalStepMeasurability.encodeCoordinator,
        ReferenceActivePhysicalStepMeasurability.encodeLive, hc] at hgate'
      have hdecoded : ReferenceActivePhysicalStepMeasurability.decodeLiveRegisters
          registers.payload (ReferenceActivePhysicalStepMeasurability.encodeLive
            registers owned base) = registers := by
        cases registers with
        | mk payload priorClock pending time boundary scores =>
            simp [ReferenceActivePhysicalStepMeasurability.decodeLiveRegisters,
              ReferenceActivePhysicalStepMeasurability.encodeLive,
              ReferenceActivePhysicalStepMeasurability.extendComplement_apply]
      cases hstart : CoordinatorPhaseClock.startRound p rate.eta.val x.time
          registers.priorClock registers.pendingAtChoice with
      | error failure => simp [ReferenceRetainedReleasePhaseObservation.localReleaseStartResult,
          hstart] at hgate'
      | ok started =>
          simp only [ReferenceRetainedReleasePhaseObservation.localReleaseStartResult,
            hstart] at hgate'
          rcases Bool.and_eq_true_iff.mp hgate' with ⟨hparts, hframeB⟩
          rcases Bool.and_eq_true_iff.mp hparts with ⟨hparts, hcutoffB⟩
          rcases Bool.and_eq_true_iff.mp hparts with ⟨hparts, hclockB⟩
          rcases Bool.and_eq_true_iff.mp hparts with ⟨hbB, hpendingB⟩
          have hb : registers.payload.sigma.val = b := of_decide_eq_true hbB
          have hpending : registers.pendingAtChoice = ∅ := of_decide_eq_true hpendingB
          have hclockSigma : registers.priorClock.sigma = some registers.payload.sigma :=
            of_decide_eq_true hclockB
          have hcutoff : registers.priorClock.u = none := of_decide_eq_true hcutoffB
          have hframeDecoded : CoordinatorLiveChoiceRecorderStep.unchangedLiveClockFrame
              (ReferenceActivePhysicalStepMeasurability.decodeLiveRegisters
                registers.payload (ReferenceActivePhysicalStepMeasurability.encodeLive
                  registers owned base)) started := of_decide_eq_true hframeB
          have hframe : CoordinatorLiveChoiceRecorderStep.unchangedLiveClockFrame
              registers started := by
            simpa only [hdecoded] using hframeDecoded
          have hstartActual : CoordinatorPhaseClock.startRound p rate.eta.val x.time
              registers.priorClock registers.clockPending = .ok started := by
            simpa only [CoordinatorLiveChoiceRecorderStep.Registers.clockPending_eq]
              using hstart
          refine ⟨registers, owned, base, started, rfl, hb, hpending,
            hclockSigma, hcutoff, hstartActual, ?_⟩
          exact ⟨hframe.1, hframe.2.1, hframe.2.2.1, hframe.2.2.2⟩

private theorem local_gate_no_cutoff
    (b : ℕ) (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (hgate : ReferenceRetainedReleasePhaseObservation.localReleaseGate rate b x.time
      (ReferenceActivePhysicalStepMeasurability.encodeState x.state) = true) :
    ReferenceCollectionPhaseHistory.cutoffChosen x = false := by
  obtain ⟨registers, owned, base, started, hc, _, _, _, hclockCutoff, hstart, hframe⟩ :=
    local_gate_live_fields b x hgate
  have hprepared : (ReferenceActivePhysicalStep.prepare x).coordinator =
      .live registers owned base
        (CoordinatorRoundDispatch.dispatchLive
          (ReferenceActivePhysicalStep.liveInput x registers owned base)) := by
    change ReferenceActivePhysicalStep.dispatch x = _
    simp only [ReferenceActivePhysicalStep.dispatch, hc,
      CoordinatorRoundDispatch.dispatch]
    rfl
  unfold ReferenceCollectionPhaseHistory.cutoffChosen
  rw [hprepared]
  cases hout : CoordinatorRoundDispatch.dispatchLive
      (ReferenceActivePhysicalStep.liveInput x registers owned base) with
  | clockFailure failure hdispatch => rfl
  | initializerFailure dispatched hdispatch checked hchecked => rfl
  | localFailure dispatched hdispatch failure => rfl
  | cutoffChosen dispatched hdispatch ledger hinitialized hledger hvalid hcutoff hpending hassignment selection =>
      have hresult : dispatched.startResult = started := by
        exact Except.ok.inj (hdispatch.symm.trans hstart)
      have hclockEq : registers.priorClock =
          {registers.priorClock with u := some x.time} := by
        calc
          registers.priorClock = started.clock := hframe.1.symm
          _ = dispatched.startResult.clock := congrArg
            CoordinatorPhaseClock.StartRoundResult.clock hresult.symm
          _ = {registers.priorClock with u := some x.time} := by
            change dispatched.startResult.clock =
              {registers.priorClock with u := some x.time}
            exact hcutoff
      have hbad := congrArg CoordinatorPhaseClock.ClockRegisters.u hclockEq
      rw [hclockCutoff] at hbad
      cases hbad
  | continuingChosen dispatched hdispatch continuation selection => rfl

private theorem continuing_pending
    (input : CoordinatorRoundDispatch.LiveInput p)
    (dispatched : CoordinatorStartRoundCutoffDispatch.Output
      input.registers input.ownedRegisters input.followerBaseScore)
    (hstart : CoordinatorPhaseClock.startRound p input.eta.val input.registers.time
      input.registers.priorClock input.registers.clockPending = .ok dispatched.startResult)
    (continuation : CoordinatorLiveChoiceRecorderStep.Continuation input.registers input.row)
    (selection : CoordinatorRoundDispatch.ArmSelection input.registers.payload
      dispatched.startResult input.registers.time input.registers.complementWeights input.row)
    (heq : CoordinatorRoundDispatch.dispatchLive input =
      .continuingChosen dispatched hstart continuation selection) :
    dispatched.startResult.pending = input.registers.pendingAtChoice := by
  unfold CoordinatorRoundDispatch.dispatchLive at heq
  dsimp only at heq
  split at heq
  · cases heq
  · rename_i actual hactual
    split at heq
    · cases heq
    · cases heq
    · by_cases hframe : CoordinatorLiveChoiceRecorderStep.unchangedLiveClockFrame
          input.registers actual.startResult
      · rw [dite_eq_left hframe] at heq
        have hp := hframe.2.1.trans
          (CoordinatorLiveChoiceRecorderStep.Registers.clockPending_eq input.registers)
        repeat' split at heq
        all_goals first
          | (cases heq; exact hp)
          | cases heq
          | (rename_i hchoice hboundary henvelope hselected
             exact ((CoordinatorLiveChoiceRecorderStep.coordinatorArmChoice_ne_none
               input.registers.payload actual.startResult.pending
               (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p actual.startResult.clock.u)
               input.registers.time input.registers.complementWeights input.row hchoice) hselected).elim)
      · rw [dite_eq_right hframe] at heq
        cases heq
    · repeat' split at heq
      all_goals first
        | cases heq
        | (rename_i hchoice hboundary henvelope hselected
           exact ((CoordinatorLiveChoiceRecorderStep.coordinatorArmChoice_ne_none
             input.registers.payload actual.startResult.pending
             (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p actual.startResult.clock.u)
             input.registers.time input.registers.complementWeights input.row hchoice) hselected).elim)

private theorem selectionAt_view
    (x : ReferenceActivePhysicalStep.RoundInput p rate) (payload : Payload rate)
    (started : CoordinatorPhaseClock.StartRoundResult p) (time : Fin p.T)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ)
    (arm : CoordinatorRoundDispatch.ArmSelection payload started time weights x.row)
    (selected : Selection x)
    (h : ReferenceActivePhysicalStep.selectionAt x payload started time weights arm = some selected) :
    selected.view.payload = payload ∧ selected.view.pendingAtChoice = started.pending ∧
      selected.view.cutoff = CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u := by
  unfold ReferenceActivePhysicalStep.selectionAt at h
  split at h
  · cases h
    exact ⟨rfl, rfl, rfl⟩
  · cases h

private theorem gate_live_empty_step
    (b : ℕ) (M : Payload rate) (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
    (base : Fin (p.m - 1) → ℕ)
    (hc : x.state.coordinator = .live registers owned base)
    (hp : registers.payload = M)
    (he : registers.pendingAtChoice = ∅)
    (hgate : ReferenceRetainedReleasePhaseObservation.localReleaseGate rate b x.time
      (ReferenceActivePhysicalStepMeasurability.encodeState x.state) = true) :
    ((ReferenceActivePhysicalStep.step x).next.coordinator = .dagger ∨
      ∃ next nextOwned, (ReferenceActivePhysicalStep.step x).next.coordinator =
        .live next nextOwned base ∧ next.payload = M ∧ next.pendingAtChoice = ∅) ∧
      ∀ i, ReferenceDownReception.expectedDownFlatWord
        (ReferenceActivePhysicalStep.prepare x).coordinator.downView i x.row x.time = none := by
  have hcut := local_gate_no_cutoff b x hgate
  have hd : (ReferenceActivePhysicalStep.prepare x).coordinator = .live registers owned base
      (CoordinatorRoundDispatch.dispatchLive (ReferenceActivePhysicalStep.liveInput x registers owned base)) := by
    change ReferenceActivePhysicalStep.dispatch x = _
    simp only [ReferenceActivePhysicalStep.dispatch, hc,
      CoordinatorRoundDispatch.dispatch]
    rfl
  have ho := ReferenceActivePhysicalStep.observeCoordinator_live_equation
    (ReferenceActivePhysicalStep.prepare x) registers owned base _ hd
  cases hx : CoordinatorRoundDispatch.dispatchLive
      (ReferenceActivePhysicalStep.liveInput x registers owned base) with
  | clockFailure failure hfailure =>
      constructor
      · left
        simp only [ReferenceActivePhysicalStep.step, ho, hx,
          ReferenceActivePhysicalStep.DispatchCut.selection, ite_true,
          ReferenceActivePhysicalStep.coordinatorFailure]
      · intro i
        simp only [hd, hx, ReferenceActivePhysicalStep.DispatchCut.downView,
          ReferenceActivePhysicalStep.DispatchCut.selection, Option.map_none,
          ReferenceDownReception.expectedDownFlatWord]
  | initializerFailure dispatched hstart checked hchecked =>
      constructor
      · left
        simp only [ReferenceActivePhysicalStep.step, ho, hx,
          ReferenceActivePhysicalStep.DispatchCut.selection, ite_true,
          ReferenceActivePhysicalStep.coordinatorFailure]
      · intro i
        simp only [hd, hx, ReferenceActivePhysicalStep.DispatchCut.downView,
          ReferenceActivePhysicalStep.DispatchCut.selection, Option.map_none,
          ReferenceDownReception.expectedDownFlatWord]
  | localFailure dispatched hstart failure =>
      constructor
      · left
        simp only [ReferenceActivePhysicalStep.step, ho, hx,
          ReferenceActivePhysicalStep.DispatchCut.selection, ite_true,
          ReferenceActivePhysicalStep.coordinatorFailure]
      · intro i
        simp only [hd, hx, ReferenceActivePhysicalStep.DispatchCut.downView,
          ReferenceActivePhysicalStep.DispatchCut.selection, Option.map_none,
          ReferenceDownReception.expectedDownFlatWord]
  | cutoffChosen dispatched hstart ledger hinitialized hledger hvalid hcutoff hpending hassignment selection =>
      simp only [ReferenceCollectionPhaseHistory.cutoffChosen, hd, hx,
        Bool.true_eq_false] at hcut
  | continuingChosen dispatched hstart continuation arm =>
      have hpend : dispatched.startResult.pending = ∅ :=
        (continuing_pending (ReferenceActivePhysicalStep.liveInput x registers owned base)
          dispatched hstart continuation arm hx).trans he
      cases hsel : (ReferenceActivePhysicalStep.DispatchCut.live registers owned base
          (.continuingChosen dispatched hstart continuation arm)).selection with
      | none =>
          constructor
          · left
            simp only [ReferenceActivePhysicalStep.step, ho, hx, hsel, ite_true,
              ReferenceActivePhysicalStep.coordinatorFailure]
          · intro i
            simp only [hd, hx, ReferenceActivePhysicalStep.DispatchCut.downView,
              hsel, Option.map_none, ReferenceDownReception.expectedDownFlatWord]
      | some selected =>
          have hs := selectionAt_view x registers.payload dispatched.startResult x.time
            (CoordinatorLiveChoiceRecorderStep.Registers.complementWeights
              (ReferenceActivePhysicalStep.liveRegistersAt registers x.time))
            arm selected hsel
          constructor
          · have hf := ReferenceFirstLiveConfirmationHistory.livePostChoice_frame x
              (ReferenceActivePhysicalStep.prepare x)
              (ReferenceActivePhysicalStep.liveRegistersAt registers x.time)
              (ReferenceActivePhysicalStep.liveOwnedAt registers owned x.time) base
              dispatched.startResult
            change (ReferenceActivePhysicalStep.prepare x).observeCoordinator.configuration = .dagger ∨
              ∃ next nextOwned, (ReferenceActivePhysicalStep.prepare x).observeCoordinator.configuration =
                .live next nextOwned base ∧ next.payload = M ∧ next.pendingAtChoice = ∅
            rw [ho, hx, hsel]
            rcases hf with hf | ⟨next, nextOwned, hout, hpay, hsub⟩
            · exact Or.inl hf
            · exact Or.inr ⟨next, nextOwned, hout, hpay.trans hp,
                Finset.eq_empty_iff_forall_notMem.mpr fun i hi => by
                  have hm := hsub hi
                  rw [hpend] at hm
                  exact Finset.notMem_empty i hm⟩
          · intro i
            have hsender : ¬ ReferenceDownReception.selectedDownSenderBranch selected.view i x.row x.time := by
              intro hsndr
              have hm := hsndr.2.2
              rw [hs.2.1, hpend] at hm
              exact Finset.notMem_empty i hm
            simp only [hd, hx, ReferenceActivePhysicalStep.DispatchCut.downView,
              hsel, Option.map_some, ReferenceDownReception.expectedDownFlatWord,
              hsender, and_false, ite_false]

private theorem local_gate_selection
    (b : ℕ) (M : Payload rate) (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
    (base : Fin (p.m - 1) → ℕ)
    (hc : x.state.coordinator = .live registers owned base)
    (hp : registers.payload = M)
    (he : registers.pendingAtChoice = ∅)
    (hgate : ReferenceRetainedReleasePhaseObservation.localReleaseGate rate b x.time
      (ReferenceActivePhysicalStepMeasurability.encodeState x.state) = true) :
    (ReferenceActivePhysicalStep.prepare x).coordinator.selection = none ∨
      ∃ selected,
        (ReferenceActivePhysicalStep.prepare x).coordinator.selection = some selected ∧
        selected.view.payload = M ∧ selected.view.pendingAtChoice = ∅ ∧
        selected.view.cutoff = none := by
  have hcut := local_gate_no_cutoff b x hgate
  have hd : (ReferenceActivePhysicalStep.prepare x).coordinator = .live registers owned base
      (CoordinatorRoundDispatch.dispatchLive (ReferenceActivePhysicalStep.liveInput x registers owned base)) := by
    change ReferenceActivePhysicalStep.dispatch x = _
    simp only [ReferenceActivePhysicalStep.dispatch, hc,
      CoordinatorRoundDispatch.dispatch]
    rfl
  cases hx : CoordinatorRoundDispatch.dispatchLive
      (ReferenceActivePhysicalStep.liveInput x registers owned base) with
  | clockFailure failure hfailure =>
      left
      simp only [hd, hx, ReferenceActivePhysicalStep.DispatchCut.selection]
  | initializerFailure dispatched hstart checked hchecked =>
      left
      simp only [hd, hx, ReferenceActivePhysicalStep.DispatchCut.selection]
  | localFailure dispatched hstart failure =>
      left
      simp only [hd, hx, ReferenceActivePhysicalStep.DispatchCut.selection]
  | cutoffChosen dispatched hstart ledger hinitialized hledger hvalid hcutoff hpending hassignment arm =>
      simp only [ReferenceCollectionPhaseHistory.cutoffChosen, hd, hx,
        Bool.true_eq_false] at hcut
  | continuingChosen dispatched hstart continuation arm =>
      have hpend : dispatched.startResult.pending = ∅ :=
        (continuing_pending (ReferenceActivePhysicalStep.liveInput x registers owned base)
          dispatched hstart continuation arm hx).trans he
      obtain ⟨gateRegisters, gateOwned, gateBase, gateStarted, hgateCoord, _, _, _,
        hgateCutoff, hgateStart, hgateFrame⟩ := local_gate_live_fields b x hgate
      have hcoord : ReferenceActivePhysicalStep.CoordinatorConfiguration.live
          registers owned base = .live gateRegisters gateOwned gateBase :=
        hc.symm.trans hgateCoord
      have hregisters : registers = gateRegisters := by
        injection hcoord with hregisters howned hbase
      have hgateStart' : CoordinatorPhaseClock.startRound p rate.eta.val x.time
          registers.priorClock registers.clockPending = .ok gateStarted := by
        simpa only [hregisters] using hgateStart
      have hstarted : dispatched.startResult = gateStarted :=
        Except.ok.inj (hstart.symm.trans hgateStart')
      have hcutoffResult : dispatched.startResult.clock.u = none := by
        have hgateClock : gateStarted.clock.u = none := by
          calc
            gateStarted.clock.u = gateRegisters.priorClock.u :=
              congrArg CoordinatorPhaseClock.ClockRegisters.u hgateFrame.1
            _ = none := hgateCutoff
        rw [hstarted]
        exact hgateClock
      have hselected : ReferenceActivePhysicalStep.selectionAt x registers.payload
          dispatched.startResult x.time
          (CoordinatorLiveChoiceRecorderStep.Registers.complementWeights
            (ReferenceActivePhysicalStep.liveRegistersAt registers x.time)) arm = none ∨
          ∃ selected, ReferenceActivePhysicalStep.selectionAt x registers.payload
            dispatched.startResult x.time
            (CoordinatorLiveChoiceRecorderStep.Registers.complementWeights
              (ReferenceActivePhysicalStep.liveRegistersAt registers x.time)) arm = some selected := by
        unfold ReferenceActivePhysicalStep.selectionAt
        split
        · right
          exact ⟨_, rfl⟩
        · exact Or.inl rfl
      rcases hselected with hnone | ⟨selected, hselected⟩
      · left
        simpa only [hd, hx, ReferenceActivePhysicalStep.DispatchCut.selection, hnone]
      · right
        have hv := selectionAt_view x registers.payload dispatched.startResult x.time
          (CoordinatorLiveChoiceRecorderStep.Registers.complementWeights
            (ReferenceActivePhysicalStep.liveRegistersAt registers x.time)) arm selected hselected
        refine ⟨selected, ?_, hv.1.trans hp, hv.2.1.trans hpend, ?_⟩
        · simpa only [hd, hx, ReferenceActivePhysicalStep.DispatchCut.selection,
            hselected]
        · rw [hv.2.2]
          simp only [CoordinatorLiveChoiceRecorderStep.cutoffFromClock, hcutoffResult]
          simp

private theorem startRound_pending_input
    (i : Fin (p.m - 1)) (t : Fin p.T)
    (before choice : ReferencePrelaunchFollower.State p rate.eta)
    (memory choiceMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hstart : ActiveFollowerLifecycle.startRound rate.eta t before memory =
      .ok (choice, choiceMemory)) (hpending : choice.status = .pending) :
    before.status = .pending := by
  rcases ReferenceActiveDataOwnership.startRound_status t before choice memory choiceMemory hstart with
    hu | hs
  · rw [hpending] at hu
    cases hu
  · exact hs.symm.trans hpending

private theorem service_inversion
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (activation : ReferencePrelaunchFollower.Activation p) (t : Fin p.T)
    (active : activation.val ≤ t.val + 1) (arm : Fin p.K)
    (own : ReferencePrelaunchFollower.Observation p)
    (choice post : ReferencePrelaunchFollower.State p rate.eta)
    (hunoccupied : choice.status ≠ .unoccupied)
    (h : (ReferenceActivePhysicalStep.recordFollower view i row activation t active arm own choice).result =
      .ok post) :
    ∃ result : ActiveFollowerQueueOperation.ServiceSuccess p rate.eta rate.n i row activation t own choice,
      ActiveFollowerQueueOperation.checkedService rate.eta rate.sourceCap rate.n rate.n_scale
        i row activation t own choice = .success result ∧ post = result.output := by
  simp only [ReferenceActivePhysicalStep.recordFollower, dite_eq_right hunoccupied,
    DeclaredFollowerLocalRound.recordOrServiceThenDown] at h
  split at h
  · cases h
  · rename_i result hservice
    cases h
    exact ⟨result, hservice, rfl⟩

private theorem pending_release_inversion
    (i : Fin (p.m - 1)) (t : Fin p.T)
    (row : ActiveFollowerLifecycle.FollowerPublicRow p.m p.K)
    (own : ReferencePrelaunchFollower.Observation p)
    (choice post out : ReferencePrelaunchFollower.State p rate.eta)
    (M : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hpending : choice.status = .pending) (hm : choice.lastDown = some M)
    (h : ActiveFollowerLifecycle.releaseAfterService rate.eta i t row own choice post = .ok out) :
    ActiveFollowerLifecycle.localStateDomainValid choice ∧ M.val.sigma ≤ t.val ∧
      ActiveFollowerLifecycle.localStateDomainValid post ∧
      out = if ActiveFollowerLifecycle.releaseCondition rate.eta i row own M then
        {post with status := .released} else post := by
  classical
  unfold ActiveFollowerLifecycle.releaseAfterService at h
  rw [dite_eq_left hpending] at h
  split at h
  · rename_i hpre
    simp only [hm] at h
    split at h
    · rename_i htime
      split at h
      · rename_i hpost
        by_cases htest : ActiveFollowerLifecycle.releaseCondition rate.eta i row own M
        · simp only [ite_eq_left htest] at h ⊢
          split at h
          · exact ⟨hpre, htime, hpost, (Except.ok.inj h).symm⟩
          · cases h
        · simp only [ite_eq_right htest] at h ⊢
          split at h
          · exact ⟨hpre, htime, hpost, (Except.ok.inj h).symm⟩
          · cases h
      · cases h
    · cases h
  · cases h

private theorem release_finish_inversion
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (t : Fin p.T) (own : ReferencePrelaunchFollower.Observation p)
    (choice post next : ReferencePrelaunchFollower.State p rate.eta)
    (memory nextMemory : ActiveFollowerLifecycle.LocalMemory p)
    (h : DeclaredFollowerLocalRound.releaseAndFinish rate i row t own choice memory post =
      .ok (next, nextMemory)) :
    ∃ released,
      ActiveFollowerLifecycle.releaseAfterService rate.eta i t
        (ActiveFollowerLifecycle.publicRowOfCompleteRow row t) own choice post = .ok released ∧
      ActiveFollowerLifecycle.finishRound rate.eta t row released memory =
        .ok (next, nextMemory) ∧ next = released := by
  unfold DeclaredFollowerLocalRound.releaseAndFinish at h
  split at h
  · cases h
  · rename_i released hrelease
    split at h
    · cases h
    · rename_i pair hfinish
      cases h
      exact ⟨released, hrelease, hfinish,
        ActiveFollowerLifecycle.finishRound_frame rate.eta t row released next memory nextMemory hfinish⟩

private theorem no_down_status_change
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p) (t : Fin p.T)
    (own : ReferencePrelaunchFollower.Observation p)
    (before after : ReferencePrelaunchFollower.State p rate.eta)
    (hnone : ReferenceDownReception.expectedDownFlatWord view i row t = none)
    (h : DeclaredFollowerLocalRound.consumeDownResult rate
      (ReferenceDownReception.referenceDownCut p view i row t own rate before).outcome =
        .ok after) : after.status = before.status := by
  unfold ReferenceDownReception.referenceDownCut at h
  split at h
  · split at h
    · split at h
      · split at h
        · split at h
          · dsimp only at h
            split at h
            · rename_i hmatch
              rw [hnone] at hmatch
              simp only [hmatch, ReferenceDownReception.ordinaryParse,
                DeclaredFollowerLocalRound.consumeDownResult] at h
              cases h
              rfl
            · cases h
              rfl
          · cases h
        · cases h
      · cases h
    · cases h
      rfl
  · cases h
    rfl

private theorem record_unoccupied_no_down
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (activation : ReferencePrelaunchFollower.Activation p) (t : Fin p.T)
    (active : activation.val ≤ t.val + 1) (arm : Fin p.K)
    (own : ReferencePrelaunchFollower.Observation p)
    (choice post : ReferencePrelaunchFollower.State p rate.eta)
    (hunoccupied : choice.status = .unoccupied)
    (hnone : ReferenceDownReception.expectedDownFlatWord view i row t = none)
    (h : (ReferenceActivePhysicalStep.recordFollower view i row activation t active arm own choice).result =
      .ok post) : post.status = .unoccupied := by
  rw [ReferenceActivePhysicalStep.recordFollower, dite_eq_left hunoccupied] at h
  cases hlogging : ActiveFollowerLogging.checkedLogging i row activation t (arm, own) choice with
  | error reason => simp only [hlogging] at h; cases h
  | ok logged =>
      simp only [hlogging] at h
      have hf := ActiveFollowerLogging.checkedLogging_success_frame i row activation t
        (arm, own) choice logged hlogging
      have hstatus := no_down_status_change view i row t own logged post hnone h
      exact hstatus.trans (hf.2.2.2.2.1.trans hunoccupied)

private theorem operation_pending_successor_inversion
    (M : Payload rate) (record : Record (p := p) (rate := rate))
    (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
    (base : Fin (p.m - 1) → ℕ)
    (hc : record.input.state.coordinator = .live registers owned base)
    (hp : registers.payload = M)
    (he : registers.pendingAtChoice = ∅)
    (hfields : ReferenceActiveDataOwnership.carriedOccupiedFields M record.input.state)
    (hnone : ∀ k, ReferenceDownReception.expectedDownFlatWord
      (ReferenceActivePhysicalStep.prepare record.input).coordinator.downView
        k record.input.row record.input.time = none)
    (i : Fin (p.m - 1)) (next : ReferencePrelaunchFollower.State p rate.eta)
    (nextMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hout : record.output.next.followers i = .ordinary next nextMemory)
    (hnext : next.status = .pending) :
    ∃ before beforeMemory choice choiceMemory post service released,
      record.input.state.followers i = .ordinary before beforeMemory ∧
      ActiveFollowerLifecycle.startRound rate.eta record.input.time before beforeMemory =
        .ok (choice, choiceMemory) ∧
      before.status = .pending ∧ choice.status = .pending ∧
      choice.lastDown = some (M.downRecord i) ∧
      ((ReferenceActivePhysicalStep.prepare record.input).followers.followers i).configuration =
        .ordinary choice choiceMemory ∧
      (ReferenceActivePhysicalStep.recordFollower
        (ReferenceActivePhysicalStep.prepare record.input).coordinator.downView i
        record.input.row (record.input.state.activations i) record.input.time
        (record.input.active i) ((ReferenceActivePhysicalStep.prepare record.input).followers.followers i).arm
        ((ReferenceActivePhysicalStep.prepare record.input).feedback.observations
          (PublicDiscreteDraws.followerPlayer p.two_le_m i)) choice).result = .ok post ∧
      ActiveFollowerQueueOperation.checkedService rate.eta rate.sourceCap rate.n rate.n_scale
        i record.input.row (record.input.state.activations i) record.input.time
        ((ReferenceActivePhysicalStep.prepare record.input).feedback.observations
          (PublicDiscreteDraws.followerPlayer p.two_le_m i)) choice = .success service ∧
      post = service.output ∧
      ActiveFollowerLifecycle.releaseAfterService rate.eta i record.input.time
        (ActiveFollowerLifecycle.publicRowOfCompleteRow record.input.row record.input.time)
        ((ReferenceActivePhysicalStep.prepare record.input).feedback.observations
          (PublicDiscreteDraws.followerPlayer p.two_le_m i)) choice post = .ok released ∧
      ActiveFollowerLifecycle.finishRound rate.eta record.input.time record.input.row released
        choiceMemory = .ok (next, nextMemory) ∧
      ¬ ActiveFollowerLifecycle.releaseCondition rate.eta i
        (ActiveFollowerLifecycle.publicRowOfCompleteRow record.input.row record.input.time)
        ((ReferenceActivePhysicalStep.prepare record.input).feedback.observations
          (PublicDiscreteDraws.followerPlayer p.two_le_m i)) (M.downRecord i) ∧
      i ∈ ReferencePhysicalReleaseQuota.pendingAtStart M record.input.time record.input.state := by
  have hstepOut : (ReferenceActivePhysicalStep.step record.input).next.followers i =
      .ordinary next nextMemory := by
    rw [← record.output_eq]
    exact hout
  have hfollower := ReferenceFollowerReplyChronology.finishFollower_ordinary_inversion
    _ _ _ next nextMemory hstepOut
  obtain ⟨choice, choiceMemory, post, hchoice, hrecord, hreleaseFinish, _, _⟩ := hfollower
  obtain ⟨rowEq, followerEq, timeEq, activeEq⟩ :=
    (ReferenceActivePhysicalStep.prepare record.input).follower_alignment i
  simp only [followerEq, rowEq, timeEq, activeEq] at hchoice hrecord hreleaseFinish
  have hpreparedInput := ReferenceFollowerReplyChronology.prepare_ordinary_inversion
    i record.input.row (record.input.state.activations i) record.input.time
    (record.input.active i) (record.input.state.followers i) choice choiceMemory hchoice
  obtain ⟨before, beforeMemory, hbefore, hstart, _, _⟩ := hpreparedInput
  have hchoicePending : choice.status = .pending := by
    cases hs : choice.status with
    | unoccupied =>
        have hpost := record_unoccupied_no_down
          (ReferenceActivePhysicalStep.prepare record.input).coordinator.downView i
          record.input.row (record.input.state.activations i) record.input.time
          (record.input.active i)
          ((ReferenceActivePhysicalStep.prepare record.input).followers.followers i).arm
          ((ReferenceActivePhysicalStep.prepare record.input).feedback.observations
            (PublicDiscreteDraws.followerPlayer p.two_le_m i)) choice post hs (hnone i) hrecord
        have hinversion := release_finish_inversion i record.input.row record.input.time
          ((ReferenceActivePhysicalStep.prepare record.input).feedback.observations
            (PublicDiscreteDraws.followerPlayer p.two_le_m i)) choice post next choiceMemory
          nextMemory hreleaseFinish
        obtain ⟨released, hrel, _, hframe⟩ := hinversion
        rw [ActiveFollowerLifecycle.releaseAfterService_unoccupied rate.eta i
          record.input.time
          (ActiveFollowerLifecycle.publicRowOfCompleteRow record.input.row record.input.time)
          ((ReferenceActivePhysicalStep.prepare record.input).feedback.observations
            (PublicDiscreteDraws.followerPlayer p.two_le_m i)) choice post hs] at hrel
        cases hrel
        rw [hframe, hpost] at hnext
        cases hnext
    | pending => rfl
    | released =>
        obtain ⟨service, _, hpostEq⟩ := service_inversion
          (ReferenceActivePhysicalStep.prepare record.input).coordinator.downView i
          record.input.row (record.input.state.activations i) record.input.time
          (record.input.active i)
          ((ReferenceActivePhysicalStep.prepare record.input).followers.followers i).arm
          ((ReferenceActivePhysicalStep.prepare record.input).feedback.observations
            (PublicDiscreteDraws.followerPlayer p.two_le_m i)) choice post
          (by rw [hs]; decide) hrecord
        have hstatus :=
          (LocalReleaseQuota.serviceSuccess_nonqueue_frame service).2.2.2.1
        obtain ⟨released, hrel, _, hframe⟩ := release_finish_inversion i
          record.input.row record.input.time
          ((ReferenceActivePhysicalStep.prepare record.input).feedback.observations
            (PublicDiscreteDraws.followerPlayer p.two_le_m i)) choice post next choiceMemory
          nextMemory hreleaseFinish
        rw [ActiveFollowerLifecycle.releaseAfterService_not_pending rate.eta i
          record.input.time
          (ActiveFollowerLifecycle.publicRowOfCompleteRow record.input.row record.input.time)
          ((ReferenceActivePhysicalStep.prepare record.input).feedback.observations
            (PublicDiscreteDraws.followerPlayer p.two_le_m i)) choice post
          (by rw [hs]; decide)] at hrel
        cases hrel
        rw [hframe, hpostEq, hstatus, hs] at hnext
        cases hnext
  have hbeforePending := startRound_pending_input i record.input.time before choice
    beforeMemory choiceMemory hstart hchoicePending
  have hlocal := ReferenceActiveDataOwnership.choice_occupied_fields_preserved M i
    record.input.row (record.input.state.activations i) record.input.time
    (record.input.active i) (record.input.state.followers i) (hfields i)
  change ReferenceActiveDataOwnership.occupiedFields M i
    ((ReferenceActivePhysicalStep.prepare record.input).followers.followers i).configuration at hlocal
  rw [hchoice] at hlocal
  have hm := hlocal (by rw [hchoicePending]; decide)
  obtain ⟨service, hservice, hpostEq⟩ := service_inversion
    (ReferenceActivePhysicalStep.prepare record.input).coordinator.downView i
    record.input.row (record.input.state.activations i) record.input.time
    (record.input.active i)
    ((ReferenceActivePhysicalStep.prepare record.input).followers.followers i).arm
    ((ReferenceActivePhysicalStep.prepare record.input).feedback.observations
      (PublicDiscreteDraws.followerPlayer p.two_le_m i)) choice post
    (by rw [hchoicePending]; decide) hrecord
  obtain ⟨released, hrel, hfinish, hframe⟩ := release_finish_inversion i
    record.input.row record.input.time
    ((ReferenceActivePhysicalStep.prepare record.input).feedback.observations
      (PublicDiscreteDraws.followerPlayer p.two_le_m i)) choice post next choiceMemory
    nextMemory hreleaseFinish
  obtain ⟨_, _, _, hreleaseEq⟩ := pending_release_inversion i record.input.time
    (ActiveFollowerLifecycle.publicRowOfCompleteRow record.input.row record.input.time)
    ((ReferenceActivePhysicalStep.prepare record.input).feedback.observations
      (PublicDiscreteDraws.followerPlayer p.two_le_m i)) choice post released
    (M.downRecord i) hchoicePending hm hrel
  have hnotReleased : ¬ ActiveFollowerLifecycle.releaseCondition rate.eta i
      (ActiveFollowerLifecycle.publicRowOfCompleteRow record.input.row record.input.time)
      ((ReferenceActivePhysicalStep.prepare record.input).feedback.observations
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)) (M.downRecord i) := by
    intro htest
    rw [hframe, hreleaseEq, ite_eq_left htest] at hnext
    simp at hnext
  have hmember :=
    (ReferencePhysicalReleaseQuota.pendingAtStart_ordinary_prepare M record.input
      registers owned base hc hp he i choice choiceMemory hchoice).2 hchoicePending
  refine ⟨before, beforeMemory, choice, choiceMemory, post, service, released,
    hbefore, hstart, hbeforePending, hchoicePending, hm, hchoice, hrecord,
    hservice, hpostEq, hrel, hfinish, hnotReleased, hmember⟩

private theorem foldRound_records_take_prefix
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start : ℕ) (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (entries : List (ReferenceActivePhysicalHorizon.CalendarEntry p start))
    (acc : ReferenceActivePhysicalHorizon.Run initial) (n : ℕ)
    (hn : n ≤ acc.records.length) :
    ((entries.foldl (ReferenceActivePhysicalHorizon.foldRound initial rows J rewards start active)
      acc).records).take n = acc.records.take n := by
  induction entries generalizing acc with
  | nil => rfl
  | cons entry rest ih =>
      rw [List.foldl_cons]
      have hn' : n ≤
          (ReferenceActivePhysicalHorizon.foldRound initial rows J rewards start active
            acc entry).records.length := by
        simp only [ReferenceActivePhysicalHorizon.foldRound,
          List.length_append, List.length_singleton]
        omega
      rw [ih _ hn']
      simp [ReferenceActivePhysicalHorizon.foldRound, hn]

private theorem connected_endpoint_unique
    {initial first second : ReferenceActivePhysicalHorizon.State p rate}
    {records : List (Record (p := p) (rate := rate))}
    (hfirst : ReferenceActivePhysicalHorizon.Connected initial records first)
    (hsecond : ReferenceActivePhysicalHorizon.Connected initial records second) :
    first = second := by
  induction records generalizing initial first second with
  | nil =>
      simp only [ReferenceActivePhysicalHorizon.Connected] at hfirst hsecond
      exact hfirst.trans hsecond.symm
  | cons record rest ih =>
      rcases hfirst with ⟨_, hfirst⟩
      rcases hsecond with ⟨_, hsecond⟩
      exact ih hfirst hsecond

private theorem run_records_take_prefix
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count pref : ℕ) (hspan : start + count ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hpref : pref ≤ count) :
    (ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan active).records.take pref =
      (ReferenceActivePhysicalHorizon.run initial rows J rewards start pref (by omega) active).records := by
  let tail := count - pref
  have hsum : pref + tail = count := Nat.add_sub_of_le hpref
  let prefixRun := ReferenceActivePhysicalHorizon.run initial rows J rewards start pref
    (by omega) active
  have happend := ReferenceActivePhysicalHorizon.run_append initial rows J rewards start
    pref tail (by omega) active
  have happend' :
      ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan active =
        ReferenceActivePhysicalHorizon.foldCalendar initial rows J rewards start
          (start + pref) tail (by omega) (by omega) active prefixRun := by
    simpa only [hsum, prefixRun] using happend
  have hrecords := congrArg (fun execution : ReferenceActivePhysicalHorizon.Run initial =>
    execution.records) happend'
  rw [hrecords]
  have hlen := ReferenceActivePhysicalHorizon.run_record_count initial rows J rewards start
    pref (by omega) active
  have htake := foldRound_records_take_prefix initial rows J rewards start active
    (ReferenceActivePhysicalHorizon.calendarEntries start (start + pref) tail
      (by omega) (by omega)) prefixRun pref (by rw [hlen])
  have hlen' : prefixRun.records.length = pref := by
    simpa [prefixRun] using hlen
  have hlenBound : prefixRun.records.length ≤ pref := by omega
  have htakeSelf : prefixRun.records.take pref = prefixRun.records :=
    List.take_of_length_le hlenBound
  simpa [ReferenceActivePhysicalHorizon.foldCalendar, prefixRun] using htake.trans htakeSelf

/-- One actual locally gated incoming record of the original source run. The
source launch is constructed by G and C, and F supplies the incoming payload
fields from the original run prefix. A pending ordinary successor is the
selector for this inversion; no success or no-release premise is supplied. -/
theorem originalSource_localReleasePendingSuccessor
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hselected : ActualInitializationPhysicalStep.selectedRowIndex p z = q)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (helapsed : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed = s)
    (b : ℕ) (j : Fin (t.val - s + 1)) (i : Fin (p.m - 1)) :
    let decomposition := ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t z
    let control := decomposition.1
    let remainder := decomposition.2
    let hremainder : remainder ∈
        ReferenceFixedTimeSourceControlCoupling.fixedControlRemainderStratum p q t := by
      change PrivateSourceStreams.coordinatorIndex p
        ((ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t z).2.2).1.2 = q
      rw [ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_private p q t z]
      change ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p z = q
      rw [ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex]
      exact hselected
    let hstart : remainder ∈ ReferenceInitializationControlRemainder.launchStartRemainderEvent
        rate rewards C_star C_h q t s control := by
      exact (ReferenceInitializationControlRemainder.launchStartRemainderEvent_iff_source
        rate rewards C_star C_h q t control z hselected s hs).mpr ⟨hcross, helapsed⟩
    let seed := ReferenceGeneratedActivePrefixFactor.generatedActiveSeed rate rewards C_star C_h
      q t control remainder hremainder s hs hstart
    let hmode := (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec rate rewards
      C_star C_h q t control remainder hremainder s hs hstart).2.1
    let count := t.val - s + 1
    let span : s + count ≤ p.T := by have ht := t.isLt; dsimp [count]; omega
    let execution := ReferenceActivePhysicalHorizon.run seed z.1.2 q rewards s count span hmode
    let index : Fin execution.records.length := ⟨j.val, by
      have hlen := ReferenceActivePhysicalHorizon.run_record_count seed z.1.2 q rewards s
        count span hmode
      rw [hlen]
      exact j.isLt⟩
    let record := execution.records[index.val]
    ∀ (hgate : ReferenceRetainedReleasePhaseObservation.localReleaseGate rate b record.input.time
      (ReferenceActivePhysicalStepMeasurability.encodeState record.input.state) = true)
      (next : ReferencePrelaunchFollower.State p rate.eta)
      (nextMemory : ActiveFollowerLifecycle.LocalMemory p),
      record.output.next.followers i = .ordinary next nextMemory →
      next.status = .pending →
      ∃ (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
          (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
          (base : Fin (p.m - 1) → ℕ),
        record.input.state.coordinator = .live registers owned base ∧
        registers.payload.sigma.val = b ∧
        registers.pendingAtChoice = ∅ ∧
        registers.priorClock.sigma = some registers.payload.sigma ∧
        registers.priorClock.u = none ∧
        (∃ started,
          CoordinatorPhaseClock.startRound p rate.eta.val record.input.time registers.priorClock
            registers.clockPending = .ok started ∧
          CoordinatorLiveChoiceRecorderStep.unchangedLiveClockFrame
            (ReferenceActivePhysicalStep.liveRegistersAt registers record.input.time) started) ∧
        ((ReferenceActivePhysicalStep.prepare record.input).coordinator.selection = none ∨
        ∃ selected,
          (ReferenceActivePhysicalStep.prepare record.input).coordinator.selection = some selected ∧
          selected.view.payload = registers.payload ∧
          selected.view.pendingAtChoice = ∅ ∧
          selected.view.cutoff = none) ∧
        (∀ k, ReferenceDownReception.expectedDownFlatWord
          (ReferenceActivePhysicalStep.prepare record.input).coordinator.downView
            k record.input.row record.input.time = none) ∧
        ReferenceActiveDataOwnership.carriedOccupiedFields registers.payload record.input.state ∧
        ((ReferenceActivePhysicalStep.step record.input).next.coordinator = .dagger ∨
          ∃ nextRegisters nextOwned,
            (ReferenceActivePhysicalStep.step record.input).next.coordinator =
              .live nextRegisters nextOwned base ∧
            nextRegisters.payload = registers.payload ∧ nextRegisters.pendingAtChoice = ∅) ∧
        ∃ before beforeMemory choice choiceMemory post service released,
          record.input.state.followers i = .ordinary before beforeMemory ∧
          ActiveFollowerLifecycle.startRound rate.eta record.input.time before beforeMemory =
            .ok (choice, choiceMemory) ∧
          before.status = .pending ∧ choice.status = .pending ∧
          choice.lastDown = some (registers.payload.downRecord i) ∧
          ((ReferenceActivePhysicalStep.prepare record.input).followers.followers i).configuration =
            .ordinary choice choiceMemory ∧
          (ReferenceActivePhysicalStep.recordFollower
            (ReferenceActivePhysicalStep.prepare record.input).coordinator.downView i
            record.input.row (record.input.state.activations i) record.input.time
            (record.input.active i)
            ((ReferenceActivePhysicalStep.prepare record.input).followers.followers i).arm
            ((ReferenceActivePhysicalStep.prepare record.input).feedback.observations
              (PublicDiscreteDraws.followerPlayer p.two_le_m i)) choice).result = .ok post ∧
          ActiveFollowerQueueOperation.checkedService rate.eta rate.sourceCap rate.n rate.n_scale
            i record.input.row (record.input.state.activations i) record.input.time
            ((ReferenceActivePhysicalStep.prepare record.input).feedback.observations
              (PublicDiscreteDraws.followerPlayer p.two_le_m i)) choice = .success service ∧
          post = service.output ∧
          ActiveFollowerLifecycle.releaseAfterService rate.eta i record.input.time
            (ActiveFollowerLifecycle.publicRowOfCompleteRow record.input.row record.input.time)
            ((ReferenceActivePhysicalStep.prepare record.input).feedback.observations
              (PublicDiscreteDraws.followerPlayer p.two_le_m i)) choice post = .ok released ∧
          ActiveFollowerLifecycle.finishRound rate.eta record.input.time record.input.row released
            choiceMemory = .ok (next, nextMemory) ∧
          ¬ ActiveFollowerLifecycle.releaseCondition rate.eta i
            (ActiveFollowerLifecycle.publicRowOfCompleteRow record.input.row record.input.time)
            ((ReferenceActivePhysicalStep.prepare record.input).feedback.observations
              (PublicDiscreteDraws.followerPlayer p.two_le_m i)) (registers.payload.downRecord i) ∧
          i ∈ ReferencePhysicalReleaseQuota.pendingAtStart registers.payload
            record.input.time record.input.state ∧
          ReferencePhysicalReleaseQuota.releaseFlag registers.payload record i = false ∧
          ReferencePhysicalReleaseQuota.upFlag registers.payload record i = false ∧
          ReferencePhysicalReleaseQuota.dataFlag registers.payload record i = false := by
  intro decomposition control remainder hremainder hstart seed hmode count span execution index record
    hgate next nextMemory hout hnext
  let initial := seed
  obtain ⟨actual, ⟨hlaunch, hfirst, _, _, _⟩, _⟩ :=
    ReferenceCorrectedInitializationLaunch.correctedLaunch_crossing_characterization
      rate z rewards C_star C_h hcross
  have hlaunchSeed : ReferenceCorrectedInitializationLaunch.correctedLaunch rate z rewards
      C_star C_h = some seed := by
    have hspec := ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec rate rewards
      C_star C_h q t control remainder hremainder s hs hstart
    have hsource : ReferenceGeneratedActivePrefixFactor.splitSource q t control remainder = z := by
      dsimp [ReferenceGeneratedActivePrefixFactor.splitSource, control, remainder, decomposition]
      exact (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).symm_apply_apply z
    have hlaunchGenerated := hspec.1
    change ReferenceCorrectedInitializationLaunch.correctedLaunch rate
      (ReferenceGeneratedActivePrefixFactor.splitSource q t control remainder) rewards
      C_star C_h = some seed at hlaunchGenerated
    rw [hsource] at hlaunchGenerated
    exact hlaunchGenerated
  have hactualEq : actual = seed := Option.some.inj (hlaunch.symm.trans hlaunchSeed)
  subst actual
  obtain ⟨fieldLaunch, hfieldLaunch, fieldFacts⟩ :=
    ReferenceCorrectedInitializationLaunch.correctedLaunch_follower_source_fields
      rate z rewards C_star C_h hcross
  have hfieldEq : fieldLaunch = seed := Option.some.inj (hfieldLaunch.symm.trans hlaunchSeed)
  subst fieldLaunch
  have hseed : ∀ k state memory, seed.followers k = .ordinary state memory →
      state.status = .unoccupied := by
    intro k state memory hconfig
    obtain ⟨hknown, _, _, _, _, _, hunoccupied, _⟩ := fieldFacts k
    have hstates := hknown.symm.trans hconfig
    injection hstates with hstate hmemory
    subst state
    exact hunoccupied
  have hprefixState :
      (ReferenceActivePhysicalHorizon.run seed z.1.2 q rewards s j.val (by omega) hmode).finalState =
        record.input.state := by
    have hchain := ReferenceFollowerReplyChronology.connected_take_to_input
      execution.connected index.val index.isLt
    have htake := run_records_take_prefix seed z.1.2 q rewards s count j.val span hmode (by omega)
    rw [htake] at hchain
    exact connected_endpoint_unique
      (ReferenceActivePhysicalHorizon.run seed z.1.2 q rewards s j.val (by omega) hmode).connected
      hchain
  obtain ⟨registers, owned, base, started, hc, hb, hpending, hclockSigma, hclockCutoff,
      hstartRound, hframe⟩ := local_gate_live_fields b record.input hgate
  have hstored : ReferenceAssignmentPayloadPersistence.storedPayload
      ((ReferenceActivePhysicalHorizon.run seed z.1.2 q rewards s j.val (by omega) hmode).finalState.coordinator) =
        some registers.payload := by
    rw [hprefixState, hc]
    rfl
  have hhistory := ReferenceOccupiedFieldHistory.run_prefix_occupied_field_history seed z.1.2 q
    rewards s count span hmode hfirst hseed j.val (by omega)
  have hfields : ReferenceActiveDataOwnership.carriedOccupiedFields registers.payload
      record.input.state := by
    have h := hhistory.1 registers.payload hstored
    simpa only [hprefixState] using h
  have hselection := local_gate_selection b registers.payload record.input registers owned base
    hc rfl hpending hgate
  have hcoordinator := gate_live_empty_step b registers.payload record.input registers owned base
    hc rfl hpending hgate
  have hnone := hcoordinator.2
  obtain ⟨before, beforeMemory, choice, choiceMemory, post, service, released,
    hbefore, hstartLocal, hbeforePending, hchoicePending, hdown, hchoice, hrecord,
    hservice, hpost, hrelease, hfinish, hnotReleased, hmember⟩ :=
      operation_pending_successor_inversion registers.payload record registers owned base
        hc rfl hpending hfields hnone i next nextMemory hout hnext
  have hreleaseFlag : ReferencePhysicalReleaseQuota.releaseFlag registers.payload record i = false := by
    unfold ReferencePhysicalReleaseQuota.releaseFlag
    rw [ReferencePhysicalReleaseQuota.own_observation_eq record i]
    exact decide_eq_false hnotReleased
  have hupFlag : ReferencePhysicalReleaseQuota.upFlag registers.payload record i = false := by
    simp [ReferencePhysicalReleaseQuota.upFlag, hreleaseFlag]
  have hdataFlag : ReferencePhysicalReleaseQuota.dataFlag registers.payload record i = false := by
    simp [ReferencePhysicalReleaseQuota.dataFlag, hreleaseFlag]
  refine ⟨registers, owned, base, hc, hb, hpending, hclockSigma, hclockCutoff,
    ⟨started, hstartRound, hframe⟩, ?_, hnone,
    hfields, hcoordinator.1, ?_⟩
  · rcases hselection with hnoneSelection | ⟨selected, hselected, hpayload, hselectedPending, hcutoff⟩
    · exact Or.inl hnoneSelection
    · exact Or.inr ⟨selected, hselected, hpayload, hselectedPending, hcutoff⟩
  · exact ⟨before, beforeMemory, choice, choiceMemory, post, service, released,
      hbefore, hstartLocal, hbeforePending, hchoicePending, hdown, hchoice, hrecord,
      hservice, hpost, hrelease, hfinish, hnotReleased, hmember,
      hreleaseFlag, hupFlag, hdataFlag⟩

/-- A pending PREPARE choice on the literal next record came from a pending
stored follower in this actual predecessor's successor state. The selector
requires `j+1` to be in range, so the horizon sentinel is never read. -/
theorem adjacentActualPreparePendingImpIncomingPending
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (j : Fin (ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan active).records.length)
    (hinRange : j.val + 1 <
      (ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan active).records.length)
    (i : Fin (p.m - 1)) (choice : ReferencePrelaunchFollower.State p rate.eta)
    (choiceMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hchoice :
      (((ReferenceActivePhysicalStep.prepare
        (ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan active).records[j.val + 1].input)
        ).followers.followers i).configuration = .ordinary choice choiceMemory)
    (hpending : choice.status = .pending) :
    ∃ before beforeMemory,
      (ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan active).records[j.val + 1].input.state.followers i =
        .ordinary before beforeMemory ∧
      before.status = .pending ∧
      (ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan active).records[j.val].output.next.followers i =
        .ordinary before beforeMemory ∧
      (ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan active).records[j.val + 1].input.state =
        (ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan active).records[j.val].output.next := by
  let execution := ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan active
  let record := execution.records[j.val]
  let nextRecord := execution.records[j.val + 1]
  have hconnected := ReferenceFollowerReplyChronology.connected_drop_from_output
    execution.connected j.val j.isLt
  rw [List.drop_eq_getElem_cons hinRange] at hconnected
  have hstate : nextRecord.input.state = record.output.next := hconnected.1
  rw [(ReferenceActivePhysicalStep.prepare nextRecord.input).followers.followers_eq i] at hchoice
  obtain ⟨before, beforeMemory, hbefore, hstart, _, _⟩ :=
    ReferenceFollowerReplyChronology.prepare_ordinary_inversion i nextRecord.input.row
      (nextRecord.input.state.activations i) nextRecord.input.time (nextRecord.input.active i)
      (nextRecord.input.state.followers i) choice choiceMemory hchoice
  have hbeforePending := startRound_pending_input i nextRecord.input.time before choice
    beforeMemory choiceMemory hstart hpending
  refine ⟨before, beforeMemory, ?_, hbeforePending, ?_, hstate⟩
  · simpa only [nextRecord, execution] using hbefore
  · rw [← hstate]
    simpa only [record, execution] using hbefore

/-- R's finite entry factor, specialized to the actual control replacement
`z_u`. It transports the literal R gate selector to the actual indexed source
record and returns the phase-factor and entry equations. All rows, rewards,
and private `J` remain those of `z_u`; current follower feedback is read from
that run. -/
theorem replacementControl_localReleasePendingSuccessor
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : ContinuousLearningRows.TimeControl p)
    (x : ReferenceRetainedReleasePhaseObservation.LaunchStart rate rewards
      C_star C_h q t s hs control0) (u : ContinuousLearningRows.TimeControl p)
    (j : Fin (t.val - s + 1)) :
    let remainder := x.val
    let hremainder := x.property.1
    let hstart :=
      (ReferenceInitializationControlRemainder.launchStartRemainderEvent_control_independent
        rate rewards C_star C_h q t s remainder hremainder control0 u).mp x.property.2
    let z_u := ReferenceGeneratedActivePrefixFactor.splitSource q t u remainder
    let sourceFacts := ReferenceGeneratedActivePrefixFactor.launchStart_source_facts
      rate rewards C_star C_h q t u remainder hremainder s hs hstart
    let hselected_u : ActualInitializationPhysicalStep.selectedRowIndex p z_u = q := by
      rw [← ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex]
      exact ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_symm_coordinatorIndex
        p q t u remainder hremainder
    let hcross_u := sourceFacts.1
    let helapsed_u := sourceFacts.2
    let decomposition_u := ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t z_u
    let control_u := decomposition_u.1
    let remainder_u := decomposition_u.2
    let hremainder_u : remainder_u ∈
        ReferenceFixedTimeSourceControlCoupling.fixedControlRemainderStratum p q t := by
      change PrivateSourceStreams.coordinatorIndex p
        ((ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t z_u).2.2).1.2 = q
      rw [ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_private p q t z_u]
      change ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p z_u = q
      rw [ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex]
      exact hselected_u
    let hstart_u : remainder_u ∈ ReferenceInitializationControlRemainder.launchStartRemainderEvent
        rate rewards C_star C_h q t s control_u := by
      exact (ReferenceInitializationControlRemainder.launchStartRemainderEvent_iff_source
        rate rewards C_star C_h q t control_u z_u hselected_u s hs).mpr
          ⟨hcross_u, helapsed_u⟩
    let seed_u := ReferenceGeneratedActivePrefixFactor.generatedActiveSeed rate rewards C_star C_h
      q t control_u remainder_u hremainder_u s hs hstart_u
    let hmode_u := (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec rate rewards
      C_star C_h q t control_u remainder_u hremainder_u s hs hstart_u).2.1
    let count := t.val - s + 1
    let span : s + count ≤ p.T := by have ht := t.isLt; dsimp [count]; omega
    let execution := ReferenceActivePhysicalHorizon.run seed_u z_u.1.2 q rewards s count span hmode_u
    let index : Fin execution.records.length := ⟨j.val, by
      have hlen := ReferenceActivePhysicalHorizon.run_record_count seed_u z_u.1.2 q rewards s
        count span hmode_u
      rw [hlen]
      exact j.isLt⟩
    let record := execution.records[index.val]
    ∀ (b : ℕ),
      (ReferenceReleaseStrictPastFactor.releaseEntries rate rewards C_star C_h q t s hs
        control0 b x j).1 = true →
      ∀ (i : Fin (p.m - 1)) (next : ReferencePrelaunchFollower.State p rate.eta)
          (nextMemory : ActiveFollowerLifecycle.LocalMemory p),
      (hout : record.output.next.followers i = .ordinary next nextMemory) →
      (hnext : next.status = .pending) →
      ∃ hgateRecord : ReferenceRetainedReleasePhaseObservation.localReleaseGate rate b
          record.input.time (ReferenceActivePhysicalStepMeasurability.encodeState record.input.state) = true,
        ReferenceReleaseStrictPastFactor.phaseFactor rate rewards C_star C_h q t s hs control0 x j =
          ReferenceActivePhysicalStepMeasurability.encodeState
            ((ReferenceActivePhysicalHorizon.run seed_u z_u.1.2 q rewards s j.val (by omega) hmode_u).finalState) ∧
        ReferenceReleaseStrictPastFactor.phaseFactor rate rewards C_star C_h q t s hs control0 x j =
          ReferenceRetainedReleasePhaseObservation.generatedPhaseBefore rate rewards C_star C_h q t s hs
            control0 x u j ∧
        ReferenceReleaseStrictPastFactor.releaseEntries rate rewards C_star C_h q t s hs control0 b x j =
          ReferenceRetainedReleasePhaseObservation.localReleaseEntry rate b
            (ReferenceRetainedAssignmentReleaseHistory.retainedHistoryTime s t hs j)
            (ReferenceActivePhysicalStepMeasurability.encodeState
              ((ReferenceActivePhysicalHorizon.run seed_u z_u.1.2 q rewards s j.val
                (by omega) hmode_u).finalState)) ∧
        ∃ (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
            (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
            (base : Fin (p.m - 1) → ℕ),
          record.input.state.coordinator = .live registers owned base ∧
          registers.payload.sigma.val = b ∧
          registers.pendingAtChoice = ∅ ∧
          registers.priorClock.sigma = some registers.payload.sigma ∧
          registers.priorClock.u = none ∧
          (∃ started,
            CoordinatorPhaseClock.startRound p rate.eta.val record.input.time registers.priorClock
              registers.clockPending = .ok started ∧
            CoordinatorLiveChoiceRecorderStep.unchangedLiveClockFrame
              (ReferenceActivePhysicalStep.liveRegistersAt registers record.input.time) started) ∧
          ((ReferenceActivePhysicalStep.prepare record.input).coordinator.selection = none ∨
            ∃ selected,
              (ReferenceActivePhysicalStep.prepare record.input).coordinator.selection = some selected ∧
              selected.view.payload = registers.payload ∧ selected.view.pendingAtChoice = ∅ ∧
              selected.view.cutoff = none) ∧
          (∀ k, ReferenceDownReception.expectedDownFlatWord
            (ReferenceActivePhysicalStep.prepare record.input).coordinator.downView
              k record.input.row record.input.time = none) ∧
          ReferenceActiveDataOwnership.carriedOccupiedFields registers.payload record.input.state ∧
          ((ReferenceActivePhysicalStep.step record.input).next.coordinator = .dagger ∨
            ∃ nextRegisters nextOwned,
              (ReferenceActivePhysicalStep.step record.input).next.coordinator =
                .live nextRegisters nextOwned base ∧
              nextRegisters.payload = registers.payload ∧ nextRegisters.pendingAtChoice = ∅) ∧
          ∃ before beforeMemory choice choiceMemory post service released,
            record.input.state.followers i = .ordinary before beforeMemory ∧
            ActiveFollowerLifecycle.startRound rate.eta record.input.time before beforeMemory =
              .ok (choice, choiceMemory) ∧
            before.status = .pending ∧ choice.status = .pending ∧
            choice.lastDown = some (registers.payload.downRecord i) ∧
            ((ReferenceActivePhysicalStep.prepare record.input).followers.followers i).configuration =
              .ordinary choice choiceMemory ∧
            (ReferenceActivePhysicalStep.recordFollower
              (ReferenceActivePhysicalStep.prepare record.input).coordinator.downView i
              record.input.row (record.input.state.activations i) record.input.time
              (record.input.active i)
              ((ReferenceActivePhysicalStep.prepare record.input).followers.followers i).arm
              ((ReferenceActivePhysicalStep.prepare record.input).feedback.observations
                (PublicDiscreteDraws.followerPlayer p.two_le_m i)) choice).result = .ok post ∧
            ActiveFollowerQueueOperation.checkedService rate.eta rate.sourceCap rate.n rate.n_scale
              i record.input.row (record.input.state.activations i) record.input.time
              ((ReferenceActivePhysicalStep.prepare record.input).feedback.observations
                (PublicDiscreteDraws.followerPlayer p.two_le_m i)) choice = .success service ∧
            post = service.output ∧
            ActiveFollowerLifecycle.releaseAfterService rate.eta i record.input.time
              (ActiveFollowerLifecycle.publicRowOfCompleteRow record.input.row record.input.time)
              ((ReferenceActivePhysicalStep.prepare record.input).feedback.observations
                (PublicDiscreteDraws.followerPlayer p.two_le_m i)) choice post = .ok released ∧
            ActiveFollowerLifecycle.finishRound rate.eta record.input.time record.input.row released
              choiceMemory = .ok (next, nextMemory) ∧
            ¬ ActiveFollowerLifecycle.releaseCondition rate.eta i
              (ActiveFollowerLifecycle.publicRowOfCompleteRow record.input.row record.input.time)
              ((ReferenceActivePhysicalStep.prepare record.input).feedback.observations
                (PublicDiscreteDraws.followerPlayer p.two_le_m i)) (registers.payload.downRecord i) ∧
            i ∈ ReferencePhysicalReleaseQuota.pendingAtStart registers.payload
              record.input.time record.input.state ∧
            ReferencePhysicalReleaseQuota.releaseFlag registers.payload record i = false ∧
            ReferencePhysicalReleaseQuota.upFlag registers.payload record i = false ∧
            ReferencePhysicalReleaseQuota.dataFlag registers.payload record i = false := by
  intro remainder hremainder hstart z_u sourceFacts hselected_u hcross_u helapsed_u
    decomposition_u control_u remainder_u hremainder_u hstart_u seed_u hmode_u count span execution index record
    b hselector i next nextMemory hout hnext
  have hsplit : ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t z_u =
      (u, remainder) := by
    dsimp [z_u, ReferenceGeneratedActivePrefixFactor.splitSource]
    exact (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).apply_symm_apply
      (u, remainder)
  let hsourceInput := ReferenceRetainedBoundaryMeasurability.retainedLaunchStartInputOfSource
    rate rewards C_star C_h q t s hs control0 z_u hselected_u hcross_u helapsed_u
  have hsourceInputEq : hsourceInput = x := by
    apply Subtype.ext
    dsimp only [hsourceInput]
    rw [ReferenceRetainedBoundaryMeasurability.retainedLaunchStartInputOfSource_val
      rate rewards C_star C_h q t s hs control0 z_u hselected_u hcross_u helapsed_u]
    rw [hsplit]
  have hphaseSource := ReferenceReleaseStrictPastFactor.phaseFactor_source_specialization
    rate rewards C_star C_h q t s hs control0 z_u hselected_u hcross_u helapsed_u
  have hphase : ReferenceReleaseStrictPastFactor.phaseFactor rate rewards C_star C_h q t s hs
      control0 x j =
      ReferenceActivePhysicalStepMeasurability.encodeState
        ((ReferenceActivePhysicalHorizon.run seed_u z_u.1.2 q rewards s j.val
          (by omega) hmode_u).finalState) := by
    have h := hphaseSource j
    change ReferenceReleaseStrictPastFactor.phaseFactor rate rewards C_star C_h q t s hs
      control0 hsourceInput j = _ at h
    rw [hsourceInputEq] at h
    exact h
  have hphaseEq := congrFun (ReferenceReleaseStrictPastFactor.phaseFactor_eq
    rate rewards C_star C_h q t s hs control0 x u) j
  have hentriesSource := ReferenceReleaseStrictPastFactor.releaseEntries_source_specialization
    rate rewards C_star C_h q t s hs control0 b z_u hselected_u hcross_u helapsed_u
  have hentries : ReferenceReleaseStrictPastFactor.releaseEntries rate rewards C_star C_h q t s hs
      control0 b x j =
      ReferenceRetainedReleasePhaseObservation.localReleaseEntry rate b
        (ReferenceRetainedAssignmentReleaseHistory.retainedHistoryTime s t hs j)
        (ReferenceActivePhysicalStepMeasurability.encodeState
          ((ReferenceActivePhysicalHorizon.run seed_u z_u.1.2 q rewards s j.val
            (by omega) hmode_u).finalState)) := by
    have h := hentriesSource j
    change ReferenceReleaseStrictPastFactor.releaseEntries rate rewards C_star C_h q t s hs
      control0 b hsourceInput j = _ at h
    rw [hsourceInputEq] at h
    exact h
  have hgateRetained : ReferenceRetainedReleasePhaseObservation.localReleaseGate rate b
      (ReferenceRetainedAssignmentReleaseHistory.retainedHistoryTime s t hs j)
      (ReferenceActivePhysicalStepMeasurability.encodeState
        ((ReferenceActivePhysicalHorizon.run seed_u z_u.1.2 q rewards s j.val
          (by omega) hmode_u).finalState)) = true := by
    have hfst := congrArg Prod.fst hentries
    unfold ReferenceRetainedReleasePhaseObservation.localReleaseEntry at hfst
    exact hfst.symm.trans hselector
  have hprefixState :
      (ReferenceActivePhysicalHorizon.run seed_u z_u.1.2 q rewards s j.val (by omega) hmode_u).finalState =
        record.input.state := by
    have hchain := ReferenceFollowerReplyChronology.connected_take_to_input
      execution.connected index.val index.isLt
    have htake := run_records_take_prefix seed_u z_u.1.2 q rewards s count j.val span hmode_u
      (by omega)
    rw [htake] at hchain
    exact connected_endpoint_unique
      (ReferenceActivePhysicalHorizon.run seed_u z_u.1.2 q rewards s j.val (by omega) hmode_u).connected
      hchain
  have htimeVal : record.input.time.val = s + j.val := by
    have htimes := ReferenceActivePhysicalHorizon.run_time_values seed_u z_u.1.2 q rewards s
      count span hmode_u
    have hrecordLength := ReferenceActivePhysicalHorizon.run_record_count seed_u z_u.1.2 q rewards s
      count span hmode_u
    have hjrecord : j.val < execution.records.length := by
      rw [hrecordLength]
      exact j.isLt
    have hmap := congrArg (fun times : List ℕ => times[j.val]?) htimes
    have hleft : (execution.records.map fun r => r.input.time.val)[j.val]? =
        some record.input.time.val := by
      rw [List.getElem?_map, List.getElem?_eq_getElem hjrecord]
      simp only [Option.map_some, record, index]
    rw [hleft] at hmap
    have hjrange : j.val < (List.range' s count 1).length := by
      simp only [List.length_range']
      simpa [count] using j.isLt
    have hcalendar : (ReferenceActivePhysicalHorizon.calendar s count)[j.val]? =
        some (s + j.val) := by
      change (List.range' s count 1)[j.val]? = some (s + j.val)
      rw [List.getElem?_eq_getElem hjrange]
      rw [List.getElem_range'_1 j.val hjrange]
    rw [hcalendar] at hmap
    exact Option.some.inj hmap
  have htime : record.input.time =
      ReferenceRetainedAssignmentReleaseHistory.retainedHistoryTime s t hs j := by
    apply Fin.ext
    simpa [ReferenceRetainedAssignmentReleaseHistory.retainedHistoryTime] using htimeVal
  have hcode : ReferenceActivePhysicalStepMeasurability.encodeState
      ((ReferenceActivePhysicalHorizon.run seed_u z_u.1.2 q rewards s j.val (by omega) hmode_u).finalState) =
        ReferenceActivePhysicalStepMeasurability.encodeState record.input.state :=
    congrArg ReferenceActivePhysicalStepMeasurability.encodeState hprefixState
  have hgateRecord : ReferenceRetainedReleasePhaseObservation.localReleaseGate rate b record.input.time
      (ReferenceActivePhysicalStepMeasurability.encodeState record.input.state) = true := by
    simpa only [htime, hcode] using hgateRetained
  have hroot := originalSource_localReleasePendingSuccessor rate rewards C_star C_h q t s hs z_u
    hselected_u hcross_u helapsed_u b j i hgateRecord next nextMemory hout hnext
  refine ⟨hgateRecord, hphase, hphaseEq, hentries, ?_⟩
  simpa only [record, execution] using hroot

end Bandits.Support.ReferenceLocalReleasePendingPredecessor

end noncomputable section
