/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstReplacementCutoffRetainedNumericalFields
import Bandits.Support.ReferenceFirstReplacementCutoffAcceptedNumericalReplay

import Lean.Elab.Tactic.Omega

/-!
# Current numerical outputs at the first replacement cutoff

Sources: `sources/zip4/manuscript/06_interruptions.tex:193-233,246-295`,
`sources/zip4/manuscript/05_binary_transport.tex:354-431`,
`sources/zip4/manuscript/04_slow_fast_learner.tex:157-188`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-79`.

This result assembles the actual retained cutoff fields and the actual
accepted-message replay at the same physical cutoff. It preserves the
choice-time UP offer and distinguishes an older register from a message
accepted during the current cutoff round.
-/

@[expose] public section
noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceFirstWindowNumericalStream
open Bandits.Support.ReferenceLaterLiveNumericalReadout
open Bandits.Support.ReferenceFirstReplacementLiveFollowerPrefix
open Bandits.Support.ActiveFollowerDownAcceptance
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.ActiveFollowerLifecycle
open Bandits.Support.ActiveFollowerLogging
open Bandits.Support.ReferenceDownReception
open Bandits.Support.DeclaredFollowerLocalRound
open Bandits.Support.ActiveFollowerQueueOperation
open Bandits.Support.ActiveFollowerArmChoice
open Bandits.Support.ReferenceAcceptedUpFollowerHistory
open Bandits.Support.RecordedQueueRun
open Bandits.Support.QueueReplay
open Bandits.Support.PublicDiscreteDraws
open Bandits.Support.OrdinaryMessageCodec
open Bandits.Support

namespace Bandits.Support.ReferenceFirstReplacementCutoffCurrentNumericalOutputs

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

private theorem complete_suffix_adjacent
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (k : ℕ)
    (hk : k + 1 < (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h
    (R.get ⟨k + 1, hk⟩).input.state =
      (R.get ⟨k, (Nat.lt_succ_self k).trans hk⟩).output.next ∧
    (R.get ⟨k + 1, hk⟩).input.time.val =
      (R.get ⟨k, (Nat.lt_succ_self k).trans hk⟩).input.time.val + 1 := by
  dsimp only
  obtain ⟨_, _, h0⟩ := ReferenceLaterLiveNumericalReadout.source_record_prefix
    rate rewards C_star C_h source ⟨k, by omega⟩
  obtain ⟨_, _, h1⟩ := ReferenceLaterLiveNumericalReadout.source_record_prefix
    rate rewards C_star C_h source ⟨k + 1, hk⟩
  rw [h0, h1]
  exact ⟨ReferenceAssignmentPayloadChronology.run_successor_finalState_eq_actualRunRecordAt
    _ source.1.2 _ rewards _ k _ _, rfl⟩

private theorem stateInputDomain_of_localStateDomainValid
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (h : ActiveFollowerLifecycle.localStateDomainValid state) :
    ActiveFollowerQueueOperation.stateInputDomain state := by
  rcases h with ⟨⟨hS, hdelta, hbacklog⟩, hbuffer, _⟩
  have htimestamps := ActiveFollowerLifecycle.localBufferValid_timestamp hbuffer
  have hkeys := ActiveFollowerLifecycle.localBufferValid_keys_nodup hbuffer
  change state.S ≤ p.T * D p ∧ state.delta ≤ D p ∧ state.backlog ≤ p.T * D p ∧
    (∀ record ∈ state.buffer, 1 ≤ record.calendarRound ∧
      record.calendarRound ≤ p.T) ∧
    (state.buffer.map ActiveFollowerQueueOperation.bufferKey).Nodup
  exact ⟨hS, hdelta, hbacklog, htimestamps, hkeys⟩

/-- At the actual first replacement cutoff, an incoming occupied follower
retains the numerical registers generated over every continuing date. The UP
offer and arm are the actual choice-time ones; a later DOWN acceptance in this
round is not used to change that offer. -/
theorem complete_first_replacement_cutoff_current_numerical_outputs
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h
    let s := ReferenceCompletePhysicalHistory.physicalStart
      rate source rewards C_star C_h
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
    let v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
    match R[v]? with
    | none => True
    | some birth =>
      match birth.output.preparation.coordinator with
      | .collection _ _ _ _ (.laterChosen _ _ _ _ _ _ _ _ _ installed _) =>
        let payload : ReferenceActivePhysicalStep.Payload rate :=
          installed.registers.payload
        let tail := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v
        let X := (R.drop v).take (1 + tail.length)
        let C := X.filterMap (ReferenceLaterLiveNumericalReadout.laterLiveReadout s)
        let L := X.length
        let cIndex := v + 1 + tail.length
        C.length = L ∧ X = birth :: tail ∧ 1 ≤ L ∧
        match R[cIndex]? with
        | none => True
        | some cut =>
          ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen cut = false ∧
          match cut.output.preparation.coordinator with
          | .live registers _ _ (.cutoffChosen _ _ _ _ _ _ _ _ _ _) =>
            registers.payload = payload ∧
            cut.input.time.val = birth.input.time.val + 1 + tail.length ∧
            cut.input.time.val = s + v + 1 + tail.length ∧
            cut.input.rows = source.1.2 ∧
            cut.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p source ∧
            cut.input.rewards = rewards ∧
            payload.sigma.val = birth.input.time.val ∧
            s < payload.sigma.val ∧
            FollowerCutoffScan.firstCutoff p rate.eta.val payload.sigma
              (FollowerCutoffScan.completeRowProposalBit p rate.eta.val cut.input.row) =
                cut.input.time.val + 1 ∧
            cut.input.time.val + 1 ≤
              FollowerCutoffScan.gridBoundary p rate.eta.val payload.sigma ∧
            (FollowerCutoffScan.gridBoundary p rate.eta.val payload.sigma =
                cut.input.time.val + 1 ∨
              ∃ stamp : Fin p.T,
                registers.priorClock.lastProposal = some (stamp, true) ∧
                stamp.val + 1 = cut.input.time.val ∧
                FollowerCutoffScan.completeRowProposalBit p rate.eta.val
                  cut.input.row stamp = true) ∧
            ∃ selected : ReferenceActivePhysicalStep.Selection cut.input,
              cut.output.preparation.coordinator.selection = some selected ∧
              selected.view.payload = payload ∧
              selected.view.pendingAtChoice = Finset.univ ∧
              selected.view.cutoff =
                some (CoordinatorCollectionUpRoundStep.localCutoff cut.input.time) ∧
              ∀ i : Fin (p.m - 1),
                let M := payload.downRecord i
                let a := payload.assignment.assigned i
                let A := fun b => (C.take b).map (fun z =>
                  (true, RecordedQueueRun.quantizedArrival
                    (ReferenceFirstLaunchNumericalCell.queueParameters rate) z a))
                let Q := fun b => QueueReplay.replay (4 * rate.n) (0, M.val.q) (A b)
                let prepared := cut.output.preparation.followers.followers i
                let own := cut.output.preparation.feedback.observations
                  (PublicDiscreteDraws.followerPlayer p.two_le_m i)
                let view := cut.output.preparation.coordinator.downView
                ∃ old : ReferencePrelaunchFollower.State p rate.eta,
                  ∃ memory : ActiveFollowerLifecycle.LocalMemory p,
                    cut.input.state.followers i = .ordinary old memory ∧
                    let choice : ReferencePrelaunchFollower.State p rate.eta :=
                      { old with status := .unoccupied }
                    (prepared.configuration = .ordinary choice memory ∧
                    ActiveFollowerLifecycle.startRound rate.eta cut.input.time old memory =
                      .ok (choice, memory) ∧
                    ∃ logged post,
                      ActiveFollowerLogging.checkedLogging i cut.input.row
                        (cut.input.state.activations i) cut.input.time
                        (prepared.arm, own) choice = .ok logged ∧
                      let diag := ReferenceDownReception.referenceDownCut p view i
                        cut.input.row cut.input.time own rate logged
                      (logged.lastDown = choice.lastDown ∧
                      logged.S = choice.S ∧
                      logged.delta = choice.delta ∧
                      logged.backlog = choice.backlog ∧
                      logged.initializationFailure = choice.initializationFailure ∧
                      logged.status = .unoccupied ∧
                      DeclaredFollowerLocalRound.consumeDownResult rate diag.outcome = .ok post ∧
                      post.status = .unoccupied ∧
                      post.initializationFailure = old.initializationFailure ∧
                      (ReferenceActivePhysicalStep.recordFollower view i cut.input.row
                        (cut.input.state.activations i) cut.input.time (cut.input.active i)
                        prepared.arm own choice).result = .ok post ∧
                      (ReferenceActivePhysicalStep.recordFollower view i cut.input.row
                        (cut.input.state.activations i) cut.input.time (cut.input.active i)
                        prepared.arm own choice).downInput = some logged ∧
                      (ReferenceActivePhysicalStep.recordFollower view i cut.input.row
                        (cut.input.state.activations i) cut.input.time (cut.input.active i)
                        prepared.arm own choice).down = some diag ∧
                      DeclaredFollowerLocalRound.releaseAndFinish rate i cut.input.row
                        cut.input.time own choice memory post = .ok (post, memory) ∧
                      cut.output.followers i =
                        ⟨.ordinary post memory, none, some logged, some diag⟩ ∧
                      post.initializationFailure = old.initializationFailure ∧
                    (ReferencePrelaunchFollower.acceptedStart choice = M.val.sigma ↔
                      old.status ≠ ActiveRoundActions.FollowerStatus.unoccupied) ∧
                    (old.status ≠ ActiveRoundActions.FollowerStatus.unoccupied →
                      old.lastDown = some M ∧
                      choice.lastDown = some M ∧
                      logged.lastDown = some M ∧
                      post.lastDown = some M ∧
                      (old.S, old.backlog) = Q L ∧
                      old.delta = (Q L).1 - (Q (L - 1)).1 ∧
                      (choice.S, choice.backlog) = Q L ∧
                      choice.delta = (Q L).1 - (Q (L - 1)).1 ∧
                      (logged.S, logged.backlog) = Q L ∧
                      logged.delta = (Q L).1 - (Q (L - 1)).1 ∧
                      (post.S, post.backlog) = Q L ∧
                      post.delta = (Q L).1 - (Q (L - 1)).1 ∧
                      ∃ k : Fin X.length,
                        ReferenceAcceptedUpFollowerHistory.RetainedDown (X.get k) i M) ∧
                    (ReferencePrelaunchFollower.acceptedStart post < M.val.sigma ∨
                      post.lastDown = some M) ∧
                    (ReferencePrelaunchFollower.acceptedStart post = M.val.sigma →
                      post.lastDown = some M ∧
                      (post.S, post.backlog) = Q L ∧
                      post.delta = (Q L).1 - (Q (L - 1)).1) ∧
                    (ActiveFollowerQueueOperation.selectedUpRound i cut.input.row
                      (cut.input.state.activations i) cut.input.time →
                      ∃ U : OrdinaryMessageCodec.UpRecord
                          (ReferencePrelaunchFollower.codecParams p rate.eta),
                        ActiveFollowerQueueOperation.checkedUpOffer rate.eta i cut.input.row
                          (cut.input.state.activations i) cut.input.time choice = .offer U ∧
                        U.val = ActiveFollowerQueueOperation.upOfferFields choice ∧
                        ActiveFollowerArmChoice.followerArmChoice choice cut.input.row
                          cut.input.time i (some U) = some prepared.arm ∧
                        prepared.arm = ActiveRoundActions.sendArm
                          (ActiveFollowerArmChoice.offeredUpBit rate.eta
                            (cut.input.row.2 cut.input.time) i U)
                          ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K
                            (cut.input.row.2 cut.input.time).1).val
                              (PublicDiscreteDraws.followerPlayer p.two_le_m i))
                          ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K
                            (cut.input.row.2 cut.input.time).1).val
                              (ActiveRoundActions.coordinator p.two_le_m)) ∧
                        ActiveFollowerArmChoice.offeredUpWord rate.eta U =
                          OrdinaryMessageCodec.wordEquivFlat
                            (ReferencePrelaunchFollower.codecParams p rate.eta)
                            (OrdinaryMessageCodec.encodeUp
                              (ReferencePrelaunchFollower.codecParams p rate.eta) U) ∧
                        ActiveFollowerArmChoice.offeredUpBit rate.eta
                          (cut.input.row.2 cut.input.time) i U =
                          AffineChannelLaw.affineHash
                            ((cut.input.row.2 cut.input.time).2 (1, i))
                            (ActiveFollowerArmChoice.offeredUpWord rate.eta U) ∧
                        (ReferencePrelaunchFollower.acceptedStart choice = M.val.sigma →
                          U.val.sigma = M.val.sigma ∧
                          U.val.S = (Q L).1 ∧
                          U.val.delta = (Q L).1 - (Q (L - 1)).1 ∧
                          U.val.q = (Q L).2)) ∧
                    (¬ ActiveFollowerQueueOperation.selectedUpRound i cut.input.row
                        (cut.input.state.activations i) cut.input.time →
                      ActiveFollowerQueueOperation.checkedUpOffer rate.eta i cut.input.row
                        (cut.input.state.activations i) cut.input.time choice = .noOffer)))
          | _ => True
      | _ => True := by
  classical
  have hN :=
    ReferenceFirstReplacementContinuingNumericalReplay.complete_first_replacement_continuing_follower_numerical_replay
      rate source rewards C_star C_h
  have hD :=
    ReferenceFirstReplacementCutoffDownRecovery.complete_first_replacement_cutoff_down_recovery_and_finish
      rate source rewards C_star C_h
  have hB :=
    ReferenceFirstReplacementCutoffAcceptedNumericalReplay.complete_first_replacement_cutoff_accepted_numerical_replay
      rate source rewards C_star C_h
  dsimp only at hN hD hB ⊢
  set R := ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h
  set s := ReferenceCompletePhysicalHistory.physicalStart
    rate source rewards C_star C_h
  set w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  set v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
  cases hb : R[v]? with
  | none => trivial
  | some birth =>
    simp only [hb] at hN hD hB ⊢
    cases hbirthCoord : birth.output.preparation.coordinator with
    | first _ => trivial
    | live _ _ _ _ => trivial
    | dagger => trivial
    | invalidCollectionCutoff => trivial
    | collection oldPayload ledger clock cutoff outcome =>
        simp only [hbirthCoord] at hN hD hB ⊢
        cases outcome <;> try trivial
        rename_i core consistent started hs instruction hinstruction output hcons
          clockData installed arm
        dsimp only [ReferenceActivePhysicalStep.collectionInput] at hN hD hB ⊢
        let payload : ReferenceActivePhysicalStep.Payload rate :=
          installed.registers.payload
        let tail := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v
        let X := (R.drop v).take (1 + tail.length)
        let C := X.filterMap (ReferenceLaterLiveNumericalReadout.laterLiveReadout s)
        let L := X.length
        let cIndex := v + 1 + tail.length
        rcases hN with ⟨hClength, hX, hsteps⟩
        have hLpos : 1 ≤ L := by
          dsimp only [L, X]
          rw [hX]
          simp
        cases hcutGet : R[v + 1 +
            (ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v).length]? with
        | none => exact ⟨hClength, hX, hLpos, trivial⟩
        | some cut =>
          simp only [hcutGet] at hD hB
          rcases hD with ⟨hnotContinuing, hDbranch⟩
          cases hcutCoord : cut.output.preparation.coordinator with
          | first _ =>
              refine ⟨hClength, hX, hLpos, hnotContinuing, ?_⟩
              simp [hcutCoord]
          | collection _ _ _ _ _ =>
              refine ⟨hClength, hX, hLpos, hnotContinuing, ?_⟩
              simp [hcutCoord]
          | dagger =>
              refine ⟨hClength, hX, hLpos, hnotContinuing, ?_⟩
              simp [hcutCoord]
          | invalidCollectionCutoff =>
              refine ⟨hClength, hX, hLpos, hnotContinuing, ?_⟩
              simp [hcutCoord]
          | live registers owned base outcome =>
              simp only [hcutCoord] at hDbranch hB ⊢
              cases outcome <;> try exact ⟨hClength, hX, hLpos, hnotContinuing, trivial⟩
              rename_i dispatched hs ledger hi he hd hc hp hn chosen
              dsimp only at hDbranch ⊢
              rcases hDbranch with ⟨hPayload, hTimeBirth, hTimeSource, hRows,
                hSelectedRow, hRewards, hSigma, hStart, hFirstCutoff, hGrid,
                hCause, hSelectedBlock⟩
              rcases hSelectedBlock with ⟨selected, hSelection, hSelectedPayload,
                hPending, hCutoff, hFollowers⟩
              dsimp only at hB
              rcases hB with ⟨_, _, _, _, hBfollowers⟩
              refine ⟨hClength, hX, hLpos, hnotContinuing, ?_⟩
              refine ⟨hPayload, hTimeBirth, hTimeSource, hRows, hSelectedRow,
                hRewards, hSigma, hStart, hFirstCutoff, hGrid, hCause,
                selected, hSelection, hSelectedPayload, hPending, hCutoff, ?_⟩
              have hcutLt : cIndex < R.length :=
                (List.getElem?_eq_some_iff.mp hcutGet).1
              have hprevLt : cIndex - 1 < R.length := by omega
              have hXlen : X.length = tail.length + 1 := by
                simpa only [List.length_cons] using congrArg List.length hX
              let j : Fin X.length := ⟨L - 1, by omega⟩
              have hjval : j.val = tail.length := by
                dsimp [j, L]
                omega
              have hprevRecord : X.get j = R.get ⟨cIndex - 1, hprevLt⟩ := by
                by_cases htailEmpty : tail = []
                · have hVlt : v < R.length := (List.getElem?_eq_some_iff.mp hb).1
                  have hBirthElem : R.get ⟨v, hVlt⟩ = birth := by
                    simpa only [List.get_eq_getElem] using
                      (List.getElem?_eq_some_iff.mp hb).2
                  have hIndex : cIndex - 1 = v := by
                    dsimp [cIndex]
                    simp [htailEmpty]
                  have hXElem : X.get j = birth := by
                    have hjzero : j.val = 0 := by simpa [htailEmpty] using hjval
                    have hXzero : X[0]? = some birth := by
                      calc
                        X[0]? = (birth :: tail)[0]? := congrArg (fun records : List
                          (ReferenceCompletePhysicalHistory.RoundRecord p rate) => records[0]?) hX
                        _ = some birth := by simp
                    have hXoption : X[j.val]? = some birth := by
                      simpa only [hjzero] using hXzero
                    simpa only [List.get_eq_getElem] using
                      (List.getElem?_eq_some_iff.mp hXoption).2
                  have hBirthOption : R[cIndex - 1]? = some birth := by
                    simpa only [hIndex] using hb
                  have hBirthPrev : R.get ⟨cIndex - 1, hprevLt⟩ = birth := by
                    simpa only [List.get_eq_getElem] using
                      (List.getElem?_eq_some_iff.mp hBirthOption).2
                  exact hXElem.trans hBirthPrev.symm
                · have htailPos : 0 < tail.length := by
                    have hne : tail.length ≠ 0 := by
                      intro hz
                      apply htailEmpty
                      simpa using hz
                    omega
                  let k : Fin tail.length := ⟨tail.length - 1, by omega⟩
                  have hkSucc : k.val + 1 = tail.length := by
                    dsimp [k]
                    omega
                  have hXElemOption : X[tail.length]? = some (tail.get k) := by
                    change ((R.drop v).take (1 + tail.length))[tail.length]? =
                      some (tail.get k)
                    rw [hX]
                    change (birth :: tail)[tail.length]? = some (tail.get k)
                    rw [← hkSucc]
                    simp [List.get_eq_getElem]
                  have hXElem : X.get j = tail.get k := by
                    have hvalue := (List.getElem?_eq_some_iff.mp hXElemOption).2
                    simpa only [List.get_eq_getElem, hjval] using hvalue
                  have htailOption :=
                    ReferenceFirstReplacementLiveFollowerPrefix.continuingTail_get R v k
                  have hindex : v + 1 + k.val = cIndex - 1 := by
                    dsimp [cIndex]
                    omega
                  have hRElemOption : R[cIndex - 1]? = some (tail.get k) := by
                    simpa only [hindex] using htailOption
                  have hRElem : R.get ⟨cIndex - 1, hprevLt⟩ = tail.get k := by
                    simpa only [List.get_eq_getElem] using
                      (List.getElem?_eq_some_iff.mp hRElemOption).2
                  exact hXElem.trans hRElem.symm
              have hcIndexPos : 1 ≤ cIndex := by
                dsimp [cIndex]
                omega
              have hprevStep : (cIndex - 1) + 1 < R.length := by
                rw [Nat.sub_add_cancel hcIndexPos]
                exact hcutLt
              have hadjacent := complete_suffix_adjacent rate source rewards C_star C_h
                (cIndex - 1) hprevStep
              have hactualAdjacent : cut.input.state =
                  (R.get ⟨cIndex - 1, hprevLt⟩).output.next := by
                have hcutElem : R.get ⟨cIndex, hcutLt⟩ = cut := by
                  simpa only [List.get_eq_getElem] using
                    (List.getElem?_eq_some_iff.mp hcutGet).2
                have hnextIndex :
                    (R.get ⟨cIndex, hcutLt⟩).input.state =
                      (R.get ⟨cIndex - 1, hprevLt⟩).output.next := by
                  simpa only [Nat.sub_add_cancel hcIndexPos] using hadjacent.1
                rw [hcutElem] at hnextIndex
                exact hnextIndex
              have hbirthElem : R.get ⟨v, (List.getElem?_eq_some_iff.mp hb).1⟩ = birth := by
                simpa only [List.get_eq_getElem] using
                  (List.getElem?_eq_some_iff.mp hb).2
              intro i
              let M := payload.downRecord i
              let a := payload.assignment.assigned i
              let A := fun b => (C.take b).map (fun z =>
                (true, RecordedQueueRun.quantizedArrival
                  (ReferenceFirstLaunchNumericalCell.queueParameters rate) z a))
              let Q := fun b => QueueReplay.replay (4 * rate.n) (0, M.val.q) (A b)
              let prepared := cut.output.preparation.followers.followers i
              let own := cut.output.preparation.feedback.observations
                (PublicDiscreteDraws.followerPlayer p.two_le_m i)
              let view := cut.output.preparation.coordinator.downView
              have hB_i := hBfollowers i
              obtain ⟨old, memory, hinput, hdomainOld, hmassOld, hzero,
                hstrict, hbusy, hdecision, hstartRound, hprepared, hdomainChoice,
                hmassChoice, hpair, hdates, hUpAdmissible, hMstarted,
                hMcredit, hresult⟩ := hFollowers i
              let choice : ReferencePrelaunchFollower.State p rate.eta :=
                { old with status := .unoccupied }
              have hchoiceStatus : choice.status = .unoccupied := by rfl
              have hchoiceDomain :
                  ActiveFollowerQueueOperation.stateInputDomain choice :=
                stateInputDomain_of_localStateDomainValid choice hdomainChoice
              have hchoiceAccepted :
                  ReferencePrelaunchFollower.acceptedStart choice = M.val.sigma ↔
                    old.status ≠ ActiveRoundActions.FollowerStatus.unoccupied := by
                constructor
                · intro hcurrent
                  by_contra hold
                  have hStartOld := hstrict hold
                  exact (Nat.ne_of_lt hStartOld) hcurrent
                · intro hold
                  have hLast : old.lastDown = some M := by
                    simpa only [M] using (hbusy hold).1
                  have hChoiceLast : choice.lastDown = some M := by
                    simpa only [choice] using hLast
                  simp [ReferencePrelaunchFollower.acceptedStart, hChoiceLast]
              rcases hresult with ⟨logged, post, hlogging, hbuffer, hoperation, hlast,
                hS, hdelta, hbacklog, hflag, hloggedStatus, hloggedPair,
                hloggedDates, hnoAppend, hconsume, hpostStatus, hpostDomain,
                hpostMass, hpostDeltaBound, hpostFlag, hbranches, hrecord,
                hrecordInput, hrecordDown, hreleaseAfter, hfinish, hrelease,
                houtput⟩
              obtain ⟨preN, preMemoryN, next, nextMemoryN, hNprepared,
                hNoutput, hNfailure, hNpreBusy, hNnextBusy⟩ := hsteps j i
              have hprevN : (R.get ⟨cIndex - 1, hprevLt⟩).output.followers i =
                  (X.get j).output.followers i := by
                exact congrArg (fun r => r.output.followers i) hprevRecord.symm
              have hNoutputPrev :
                  ((R.get ⟨cIndex - 1, hprevLt⟩).output.followers i).configuration =
                    .ordinary next nextMemoryN := by
                rw [← hprevRecord]
                exact hNoutput
              have hNobs :
                  ((ReferenceActivePhysicalStep.prepare
                    (R.get ⟨cIndex - 1, hprevLt⟩).input).observeFollower i).configuration =
                    .ordinary next nextMemoryN := by
                rw [(R.get ⟨cIndex - 1, hprevLt⟩).output_eq] at hNoutputPrev
                simpa only [ReferenceActivePhysicalStep.step] using hNoutputPrev
              have houtputNext :
                  (R.get ⟨cIndex - 1, hprevLt⟩).output.next.followers i =
                    .ordinary next nextMemoryN := by
                rw [(R.get ⟨cIndex - 1, hprevLt⟩).output_eq]
                exact (ReferenceActivePhysicalStep.step_next_fields
                  (R.get ⟨cIndex - 1, hprevLt⟩).input).2.2.2 i |>.trans hNobs
              have hinputNext : cut.input.state.followers i =
                  (R.get ⟨cIndex - 1, hprevLt⟩).output.next.followers i :=
                congrArg (fun st : ReferenceActivePhysicalStep.State p rate => st.followers i)
                  hactualAdjacent
              have hordinaryEq : DeclaredFollowerLocalRound.LocalConfiguration.ordinary
                    old memory =
                  DeclaredFollowerLocalRound.LocalConfiguration.ordinary next nextMemoryN := by
                calc
                  .ordinary old memory = cut.input.state.followers i := hinput.symm
                  _ = (R.get ⟨cIndex - 1, hprevLt⟩).output.next.followers i := hinputNext
                  _ = .ordinary next nextMemoryN := houtputNext
              obtain ⟨holdEq, hmemoryEq⟩ :=
                DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj hordinaryEq
              have hjplus : j.val + 1 = L := by omega
              have hjpred : j.val = L - 1 := by omega
              have hOldFacts : old.status ≠ .unoccupied →
                  old.lastDown = some M ∧
                    (old.S, old.backlog) = Q L ∧
                    old.delta = (Q L).1 - (Q (L - 1)).1 ∧
                    ∃ k : Fin X.length,
                      ReferenceAcceptedUpFollowerHistory.RetainedDown (X.get k) i M := by
                intro hOldBusy
                have hnextBusy : next.status ≠ .unoccupied := by
                  intro hnextUnoccupied
                  apply hOldBusy
                  rw [holdEq, hnextUnoccupied]
                obtain ⟨_, hNregisters, hNdelta, hNretained⟩ :=
                  hNnextBusy hnextBusy
                have hOldRegisters : (old.S, old.backlog) = Q L := by
                  simpa only [holdEq, hjplus] using hNregisters
                have hOldDelta : old.delta = (Q L).1 - (Q (L - 1)).1 := by
                  simpa only [holdEq, hjplus, hjpred, Q, A,
                    Nat.sub_add_cancel hLpos] using hNdelta
                rcases hNretained with ⟨retainedIndex, _, hRetained⟩
                exact ⟨(hbusy hOldBusy).1, hOldRegisters, hOldDelta,
                  ⟨retainedIndex, hRetained⟩⟩
              have hpostFrame : old.status ≠ .unoccupied →
                  post.lastDown = logged.lastDown ∧ post.S = logged.S ∧
                    post.delta = logged.delta ∧ post.backlog = logged.backlog := by
                intro hOldBusy
                rcases hbranches with hnotSelected | hmismatch | hparsed | haccepted
                · rcases hnotSelected with ⟨_, _, hpost⟩
                  rw [hpost]
                  simp
                · rcases hmismatch with ⟨_, _, _, _, _, _, _, _, _, hpost⟩
                  rw [hpost]
                  simp
                · rcases hparsed with ⟨_, _, _, _, _, _, _, _, hpost, _⟩
                  rw [hpost]
                  simp
                · rcases haccepted with ⟨_, _, _, _, _, _, _, hexists⟩
                  rcases hexists with ⟨hAcceptDown, _⟩
                  have hchoiceLast : choice.lastDown = some M := by
                    simpa only [choice] using (hbusy hOldBusy).1
                  have hloggedLast : logged.lastDown = some M := hlast.trans hchoiceLast
                  have hstartLogged :
                      ReferencePrelaunchFollower.acceptedStart logged = M.val.sigma := by
                    simp [ReferencePrelaunchFollower.acceptedStart, hloggedLast]
                  change ReferencePrelaunchFollower.acceptedStart logged < M.val.sigma ∧
                    M.val.sigma ≤ cut.input.time.val + 1 at hAcceptDown
                  rw [hstartLogged] at hAcceptDown
                  omega
              have hCurrent :
                  (ReferencePrelaunchFollower.acceptedStart post < M.val.sigma ∨
                    post.lastDown = some M) ∧
                  (ReferencePrelaunchFollower.acceptedStart post = M.val.sigma →
                    post.lastDown = some M ∧
                    (post.S, post.backlog) = Q L ∧
                    post.delta = (Q L).1 - (Q (L - 1)).1) := by
                by_cases hOldBusy : old.status ≠ .unoccupied
                · rcases hOldFacts hOldBusy with ⟨hOldLast, hOldRegs, hOldDelta, _⟩
                  have hchoiceLast' : choice.lastDown = some M := by
                    simpa only [choice] using hOldLast
                  have hchoiceRegs' : (choice.S, choice.backlog) = Q L := by
                    simpa only [choice] using hOldRegs
                  have hchoiceDelta' : choice.delta = (Q L).1 - (Q (L - 1)).1 := by
                    simpa only [choice] using hOldDelta
                  have hloggedLast' : logged.lastDown = some M := hlast.trans hchoiceLast'
                  have hloggedRegs' : (logged.S, logged.backlog) = Q L := by
                    rw [hS, hbacklog]
                    exact hchoiceRegs'
                  have hloggedDelta' :
                      logged.delta = (Q L).1 - (Q (L - 1)).1 := hdelta.trans hchoiceDelta'
                  rcases hpostFrame hOldBusy with ⟨hpostLastFrame, hpostSFrame,
                    hpostDeltaFrame, hpostBacklogFrame⟩
                  have hpostLast' : post.lastDown = some M :=
                    hpostLastFrame.trans hloggedLast'
                  have hpostRegs' : (post.S, post.backlog) = Q L := by
                    rw [hpostSFrame, hpostBacklogFrame]
                    exact hloggedRegs'
                  have hpostDelta' :
                      post.delta = (Q L).1 - (Q (L - 1)).1 :=
                    hpostDeltaFrame.trans hloggedDelta'
                  exact ⟨Or.inr hpostLast', fun _ =>
                    ⟨hpostLast', hpostRegs', hpostDelta'⟩⟩
                · have hOldUnoccupied : old.status = .unoccupied := by
                    by_contra h
                    exact hOldBusy h
                  have hOldStart := hstrict hOldUnoccupied
                  have hOldStart' :
                      ReferencePrelaunchFollower.acceptedStart old < M.val.sigma := by
                    simpa only [M, payload] using hOldStart
                  have hloggedStart :
                      ReferencePrelaunchFollower.acceptedStart logged =
                        ReferencePrelaunchFollower.acceptedStart old := by
                    unfold ReferencePrelaunchFollower.acceptedStart
                    have hchoiceLast : choice.lastDown = old.lastDown := by rfl
                    rw [hlast, hchoiceLast]
                  rcases hbranches with hnotSelected | hmismatch | hparsed | haccepted
                  · rcases hnotSelected with ⟨_, _, hpostEq⟩
                    have hpostStart :
                        ReferencePrelaunchFollower.acceptedStart post < M.val.sigma := by
                      rw [hpostEq]
                      rw [hloggedStart]
                      exact hOldStart'
                    refine ⟨Or.inl hpostStart, ?_⟩
                    intro hcurrent
                    exact False.elim ((Nat.ne_of_lt hpostStart) hcurrent)
                  · rcases hmismatch with ⟨_, _, _, _, _, _, _, _, _, hpostEq⟩
                    have hpostStart :
                        ReferencePrelaunchFollower.acceptedStart post < M.val.sigma := by
                      rw [hpostEq]
                      change ReferencePrelaunchFollower.acceptedStart logged < M.val.sigma
                      rw [hloggedStart]
                      exact hOldStart'
                    refine ⟨Or.inl hpostStart, ?_⟩
                    intro hcurrent
                    exact False.elim ((Nat.ne_of_lt hpostStart) hcurrent)
                  · rcases hparsed with ⟨_, _, _, _, _, _, _, _, hpostEq, _⟩
                    have hpostStart :
                        ReferencePrelaunchFollower.acceptedStart post < M.val.sigma := by
                      rw [hpostEq]
                      change ReferencePrelaunchFollower.acceptedStart logged < M.val.sigma
                      rw [hloggedStart]
                      exact hOldStart'
                    refine ⟨Or.inl hpostStart, ?_⟩
                    intro hcurrent
                    exact False.elim ((Nat.ne_of_lt hpostStart) hcurrent)
                  · rcases haccepted with ⟨_, _, _, _, _, _, _, hcheckedData⟩
                    rcases hcheckedData with ⟨_accepted, replayData⟩
                    rcases replayData with ⟨_recovered, _hchecked, _hscanEndpoint,
                      _hrounds, _hqueueRecords, _hrecordBits, _hregisters, _hprefix,
                      _hstarted, hcutOutcome, _hpostEq⟩
                    have hBactual := hB_i
                    rw [houtput] at hBactual
                    simp only [hcutOutcome] at hBactual
                    rcases hBactual with ⟨hBMessage, _, _, _, _, _, _, _, _,
                      _hBRegisters, hBLastService, hBAfterLast, hBAfterRegisters, hBAfterDelta,
                      _, _, hBActualState, _, _⟩
                    rcases hBActualState with ⟨_oldB, actualMemory, hinputB,
                      hconfigB, _, _, _⟩
                    have hinputSame := hinput.symm.trans hinputB
                    obtain ⟨_, hmemoryInput⟩ :=
                      DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj hinputSame
                    obtain ⟨hpostAfter, hmemoryOutput⟩ :=
                      DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj hconfigB
                    have hBMessagePayload : M = payload.downRecord i := by
                      simp only [M, payload]
                    have hpostLast : post.lastDown = some M := by
                      rw [hpostAfter]
                      simpa only [hBMessagePayload] using hBAfterLast
                    have hpostRegisters : (post.S, post.backlog) = Q L := by
                      rw [hpostAfter]
                      exact hBAfterRegisters
                    have hpostDelta : post.delta = (Q L).1 - (Q (L - 1)).1 := by
                      rw [hpostAfter]
                      exact hBAfterDelta.trans hBLastService
                    exact ⟨Or.inr hpostLast, fun _ =>
                      ⟨hpostLast, hpostRegisters, hpostDelta⟩⟩
              refine ⟨old, memory, hinput, ?_⟩
              refine ⟨hprepared, hstartRound, logged, post, hlogging, ?_⟩
              refine ⟨hlast, hS, hdelta, hbacklog, hflag, hloggedStatus,
                ?_, hpostStatus, hpostFlag, ?_, ?_, ?_, hrelease, houtput,
                hpostFlag, hchoiceAccepted, ?_, ?_⟩
              · simpa only using hconsume
              · simpa only using hrecord
              · simpa only using hrecordInput
              · simpa only using hrecordDown
              · intro hold
                rcases hOldFacts hold with ⟨hOldLast, hOldRegs, hOldDelta,
                  hOldRetained'⟩
                have hchoiceLast' : choice.lastDown = some M := by
                  simpa only [choice] using hOldLast
                have hchoiceRegs' : (choice.S, choice.backlog) = Q L := by
                  simpa only [choice] using hOldRegs
                have hchoiceDelta' : choice.delta = (Q L).1 - (Q (L - 1)).1 := by
                  simpa only [choice] using hOldDelta
                have hloggedLast' : logged.lastDown = some M := hlast.trans hchoiceLast'
                have hloggedRegs' : (logged.S, logged.backlog) = Q L := by
                  rw [hS, hbacklog]
                  exact hchoiceRegs'
                have hloggedDelta' :
                    logged.delta = (Q L).1 - (Q (L - 1)).1 := hdelta.trans hchoiceDelta'
                rcases hpostFrame hold with ⟨hpostLastFrame, hpostSFrame,
                  hpostDeltaFrame, hpostBacklogFrame⟩
                have hpostLast' : post.lastDown = some M :=
                  hpostLastFrame.trans hloggedLast'
                have hpostRegs' : (post.S, post.backlog) = Q L := by
                  rw [hpostSFrame, hpostBacklogFrame]
                  exact hloggedRegs'
                have hpostDelta' :
                    post.delta = (Q L).1 - (Q (L - 1)).1 :=
                  hpostDeltaFrame.trans hloggedDelta'
                exact ⟨hOldLast, hchoiceLast', hloggedLast', hpostLast',
                  hOldRegs, hOldDelta, hchoiceRegs', hchoiceDelta', hloggedRegs',
                  hloggedDelta', hpostRegs', hpostDelta', hOldRetained'⟩
              · refine ⟨hCurrent.1, hCurrent.2, ?_, ?_⟩
                · intro hselectedUp
                  let U : OrdinaryMessageCodec.UpRecord
                      (ReferencePrelaunchFollower.codecParams p rate.eta) :=
                    ⟨ActiveFollowerQueueOperation.upOfferFields choice, hUpAdmissible⟩
                  have hUvalue : U.val = ActiveFollowerQueueOperation.upOfferFields choice := rfl
                  have hoff : ActiveFollowerQueueOperation.checkedUpOffer rate.eta i
                      cut.input.row (cut.input.state.activations i) cut.input.time choice =
                        .offer U := by
                    unfold ActiveFollowerQueueOperation.checkedUpOffer
                    rw [dite_eq_left hchoiceDomain]
                    rw [dite_eq_left ⟨hselectedUp, hchoiceStatus⟩]
                    rw [dite_eq_left hUpAdmissible]
                  have hprepareActual : prepared =
                      DeclaredFollowerLocalRound.prepare rate i cut.input.row
                        (cut.input.state.activations i) cut.input.time
                        (cut.input.active i) (.ordinary old memory) := by
                    change cut.output.preparation.followers.followers i = _
                    rw [cut.output_eq]
                    change (ReferenceActiveFeedbackCut.prepare
                      (ReferenceActivePhysicalStep.followerInput cut.input)).followers i = _
                    have hprep := cut.output.preparation.followers.followers_eq i
                    rw [cut.output_eq] at hprep
                    simp only [ReferenceActivePhysicalStep.step,
                      ReferenceActivePhysicalStep.followerInput] at hprep
                    simp only [ReferenceActiveFeedbackCut.prepareFollowers_apply] at hprep
                    rw [hinput] at hprep
                    simpa only [ReferenceActivePhysicalStep.prepare,
                      ReferenceActiveFeedbackCut.prepareFollowers_apply,
                      ReferenceActivePhysicalStep.RoundInput.row] using hprep
                  have hchoiceArm : ActiveFollowerArmChoice.followerArmChoice choice
                      cut.input.row cut.input.time i (some U) = some prepared.arm := by
                    have hprepareOffer := DeclaredFollowerLocalRound.prepare_offer_arm_equation
                      rate i cut.input.row (cut.input.state.activations i) cut.input.time
                      (cut.input.active i) old choice memory memory hstartRound U hoff
                    cases harmChoice : ActiveFollowerArmChoice.followerArmChoice choice
                        cut.input.row cut.input.time i (some U) with
                    | none =>
                        have hdagger : prepared.configuration = .dagger := by
                          rw [hprepareActual]
                          exact (hprepareOffer.1 harmChoice).2
                        rw [hdagger] at hprepared
                        cases hprepared
                    | some arm =>
                        have hprepareArm := (hprepareOffer.2 arm harmChoice).1
                        have hactualArm := congrArg DeclaredFollowerLocalRound.PreparedRound.arm
                          hprepareActual
                        have hsameArm : arm = prepared.arm := hprepareArm.symm.trans hactualArm.symm
                        exact congrArg some hsameArm
                  rcases hselectedUp with ⟨hactive, hslot, hselectedDraw⟩
                  have hstateBounds : ActiveFollowerArmChoice.upStateDomain choice :=
                    ⟨hchoiceDomain.1, hchoiceDomain.2.1, hchoiceDomain.2.2.1⟩
                  have hmatches : ActiveFollowerArmChoice.offeredUpMatchesState choice U := by
                    simp [ActiveFollowerArmChoice.offeredUpMatchesState, hUvalue,
                      ActiveFollowerQueueOperation.upOfferFields]
                  have hcore := ActiveFollowerArmChoice.followerArmChoiceCore_unoccupied_selected_up
                    choice (cut.input.row.2 cut.input.time) i U hchoiceStatus hslot
                    hselectedDraw ⟨hstateBounds, hmatches⟩
                  have hchoiceCore : ActiveFollowerArmChoice.followerArmChoice choice
                      cut.input.row cut.input.time i (some U) =
                      ActiveFollowerArmChoice.followerArmChoiceCore choice
                        (cut.input.row.2 cut.input.time) i (some U) :=
                    ActiveFollowerArmChoice.followerArmChoice_eq_core choice
                      cut.input.row cut.input.time i (some U)
                  have hchoiceArmActual := hchoiceArm
                  rw [hchoiceCore, hcore] at hchoiceArm
                  have harmExpected : prepared.arm = ActiveRoundActions.sendArm
                      (ActiveFollowerArmChoice.offeredUpBit rate.eta
                        (cut.input.row.2 cut.input.time) i U)
                      ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K
                        (cut.input.row.2 cut.input.time).1).val
                          (PublicDiscreteDraws.followerPlayer p.two_le_m i))
                      ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K
                        (cut.input.row.2 cut.input.time).1).val
                          (ActiveRoundActions.coordinator p.two_le_m)) :=
                    (Option.some.inj hchoiceArm).symm
                  have hcurrentNumbers :
                      ReferencePrelaunchFollower.acceptedStart choice = M.val.sigma →
                      U.val.sigma = M.val.sigma ∧ U.val.S = (Q L).1 ∧
                        U.val.delta = (Q L).1 - (Q (L - 1)).1 ∧ U.val.q = (Q L).2 := by
                    intro hcurrent
                    have hold := hchoiceAccepted.mp hcurrent
                    rcases hOldFacts hold with ⟨_, hOldRegs, hOldDelta, _⟩
                    have hchoiceRegs : (choice.S, choice.backlog) = Q L := by
                      simpa only [choice] using hOldRegs
                    have hchoiceDelta :
                        choice.delta = (Q L).1 - (Q (L - 1)).1 := by
                      simpa only [choice] using hOldDelta
                    have hSvalue : choice.S = (Q L).1 := congrArg Prod.fst hchoiceRegs
                    have hqvalue : choice.backlog = (Q L).2 := congrArg Prod.snd hchoiceRegs
                    refine ⟨?_, ?_, ?_, ?_⟩
                    · simpa [ActiveFollowerQueueOperation.upOfferFields, hUvalue] using hcurrent
                    · simpa [ActiveFollowerQueueOperation.upOfferFields, hUvalue] using hSvalue
                    · simpa [ActiveFollowerQueueOperation.upOfferFields, hUvalue] using hchoiceDelta
                    · simpa [ActiveFollowerQueueOperation.upOfferFields, hUvalue] using hqvalue
                  exact ⟨U, hoff, hUvalue, hchoiceArmActual, harmExpected, rfl, rfl,
                    hcurrentNumbers⟩
                · intro hnotSelected
                  exact ActiveFollowerQueueOperation.checkedUpOffer_noOffer rate.eta i
                    cut.input.row (cut.input.state.activations i) cut.input.time choice
                    hchoiceDomain (fun h => hnotSelected h.1)
