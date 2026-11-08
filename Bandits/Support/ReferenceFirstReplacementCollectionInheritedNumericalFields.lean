/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstReplacementCutoffCurrentNumericalOutputs
public import Bandits.Support.ReferenceFirstReplacementCollectionPrefix

import Lean.Elab.Tactic.Omega

/-!
# Current DOWN numerical fields through the first replacement collection

Sources: `sources/zip4/manuscript/06_interruptions.tex:150-179,193-233,246-295`,
`sources/zip4/manuscript/04_slow_fast_learner.tex:157-188`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-79`.

This module follows the actual current DOWN installed by the first replacement
birth through its frozen collection. The cutoff's own UP choice remains tied
to its cutoff snapshot. No coordinator UP acceptance is asserted.
-/

@[expose] public section
noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.ActiveFollowerLifecycle
open Bandits.Support.ActiveFollowerQueueOperation
open Bandits.Support.ActiveFollowerArmChoice
open Bandits.Support.ActiveFollowerLogging
open Bandits.Support.ReferenceDownReception
open Bandits.Support.DeclaredFollowerLocalRound
open Bandits.Support.ReferenceFirstReplacementLiveFollowerPrefix
open Bandits.Support.ReferenceLaterLiveNumericalReadout
open Bandits.Support.RecordedQueueRun
open Bandits.Support.QueueReplay
open Bandits.Support.OrdinaryMessageCodec
open Bandits.Support.PublicDiscreteDraws
open Bandits.Support

namespace Bandits.Support.ReferenceFirstReplacementCollectionInheritedNumericalFields

variable {p : ConstructorDimensions.Parameters}

private theorem stateInputDomain_of_localStateDomainValid
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (h : ActiveFollowerLifecycle.localStateDomainValid state) :
    ActiveFollowerQueueOperation.stateInputDomain state := by
  rcases h with ⟨⟨hS, hdelta, hbacklog⟩, hbuffer, _⟩
  have htimestamps := ActiveFollowerLifecycle.localBufferValid_timestamp hbuffer
  have hkeys := ActiveFollowerLifecycle.localBufferValid_keys_nodup hbuffer
  change state.S ≤ p.T * D p ∧ state.delta ≤ D p ∧ state.backlog ≤ p.T * D p ∧
    (∀ record ∈ state.buffer, 1 ≤ record.calendarRound ∧ record.calendarRound ≤ p.T) ∧
    (state.buffer.map ActiveFollowerQueueOperation.bufferKey).Nodup
  exact ⟨hS, hdelta, hbacklog, htimestamps, hkeys⟩

private theorem actual_record_prepared_eq
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (r : ReferenceCompletePhysicalHistory.RoundRecord p rate)
    (i : Fin (p.m - 1)) (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hinput : r.input.state.followers i = .ordinary state memory) :
    r.output.preparation.followers.followers i =
      DeclaredFollowerLocalRound.prepare rate i r.input.row
        (r.input.state.activations i) r.input.time (r.input.active i)
        (.ordinary state memory) := by
  rw [r.output_eq]
  change (ReferenceActiveFeedbackCut.prepare
    (ReferenceActivePhysicalStep.followerInput r.input)).followers i = _
  have hprep := r.output.preparation.followers.followers_eq i
  rw [r.output_eq] at hprep
  simp only [ReferenceActivePhysicalStep.step,
    ReferenceActivePhysicalStep.followerInput] at hprep
  simp only [ReferenceActiveFeedbackCut.prepareFollowers_apply] at hprep
  rw [hinput] at hprep
  simpa only [ReferenceActivePhysicalStep.prepare,
    ReferenceActiveFeedbackCut.prepareFollowers_apply,
    ReferenceActivePhysicalStep.RoundInput.row] using hprep

private theorem actual_unoccupied_offer
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (r : ReferenceCompletePhysicalHistory.RoundRecord p rate)
    (i : Fin (p.m - 1)) (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hstatus : state.status = ActiveRoundActions.FollowerStatus.unoccupied)
    (hdomain : ActiveFollowerLifecycle.localStateDomainValid state)
    (hstart : ActiveFollowerLifecycle.startRound rate.eta r.input.time state memory =
      .ok (state, memory))
    (hprepared : (r.output.preparation.followers.followers i) =
      DeclaredFollowerLocalRound.prepare rate i r.input.row
        (r.input.state.activations i) r.input.time (r.input.active i)
        (.ordinary state memory))
    (hadmissible : OrdinaryMessageCodec.upAdmissible
      (ReferencePrelaunchFollower.codecParams p rate.eta)
      (ActiveFollowerQueueOperation.upOfferFields state)) :
    (∀ (_ : ActiveFollowerQueueOperation.selectedUpRound i r.input.row
        (r.input.state.activations i) r.input.time),
      ∃ U : OrdinaryMessageCodec.UpRecord
          (ReferencePrelaunchFollower.codecParams p rate.eta),
        ActiveFollowerQueueOperation.checkedUpOffer rate.eta i r.input.row
          (r.input.state.activations i) r.input.time state = .offer U ∧
        U.val = ActiveFollowerQueueOperation.upOfferFields state ∧
        ActiveFollowerArmChoice.followerArmChoice state r.input.row r.input.time i
          (some U) = some (r.output.preparation.followers.followers i).arm ∧
        (r.output.preparation.followers.followers i).arm =
          ActiveRoundActions.sendArm
            (ActiveFollowerArmChoice.offeredUpBit rate.eta
              (r.input.row.2 r.input.time) i U)
            ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K
              (r.input.row.2 r.input.time).1).val
                (PublicDiscreteDraws.followerPlayer p.two_le_m i))
            ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K
              (r.input.row.2 r.input.time).1).val
                (ActiveRoundActions.coordinator p.two_le_m)) ∧
        ActiveFollowerArmChoice.offeredUpWord rate.eta U =
          OrdinaryMessageCodec.wordEquivFlat
            (ReferencePrelaunchFollower.codecParams p rate.eta)
            (OrdinaryMessageCodec.encodeUp
              (ReferencePrelaunchFollower.codecParams p rate.eta) U) ∧
        ActiveFollowerArmChoice.offeredUpBit rate.eta
          (r.input.row.2 r.input.time) i U =
          AffineChannelLaw.affineHash ((r.input.row.2 r.input.time).2 (1, i))
            (ActiveFollowerArmChoice.offeredUpWord rate.eta U)) ∧
    (¬ ActiveFollowerQueueOperation.selectedUpRound i r.input.row
        (r.input.state.activations i) r.input.time →
      ActiveFollowerQueueOperation.checkedUpOffer rate.eta i r.input.row
        (r.input.state.activations i) r.input.time state = .noOffer) := by
  classical
  have hstateInput := stateInputDomain_of_localStateDomainValid state hdomain
  let U : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta) :=
    ⟨ActiveFollowerQueueOperation.upOfferFields state, hadmissible⟩
  have hoff : ∀ (_ : ActiveFollowerQueueOperation.selectedUpRound i r.input.row
      (r.input.state.activations i) r.input.time),
      ActiveFollowerQueueOperation.checkedUpOffer rate.eta i r.input.row
        (r.input.state.activations i) r.input.time state = .offer U := by
    intro hselected
    unfold ActiveFollowerQueueOperation.checkedUpOffer
    rw [dite_eq_left hstateInput, dite_eq_left ⟨hselected, hstatus⟩, dite_eq_left hadmissible]
  refine ⟨?_, ?_⟩
  · intro hselected
    have hoff' := hoff hselected
    have hmatches : ActiveFollowerArmChoice.upStateDomain state ∧
        ActiveFollowerArmChoice.offeredUpMatchesState state U := by
      constructor
      · exact ⟨hstateInput.1, hstateInput.2.1, hstateInput.2.2.1⟩
      · simp [ActiveFollowerArmChoice.offeredUpMatchesState, U,
          ActiveFollowerQueueOperation.upOfferFields]
    have hcore := ActiveFollowerArmChoice.followerArmChoiceCore_unoccupied_selected_up
      state (r.input.row.2 r.input.time) i U hstatus hselected.2.1 hselected.2.2 hmatches
    have hchoice : ActiveFollowerArmChoice.followerArmChoice state r.input.row
        r.input.time i (some U) =
        some (ActiveRoundActions.sendArm
          (ActiveFollowerArmChoice.offeredUpBit rate.eta
            (r.input.row.2 r.input.time) i U)
          ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K
            (r.input.row.2 r.input.time).1).val
              (PublicDiscreteDraws.followerPlayer p.two_le_m i))
          ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K
            (r.input.row.2 r.input.time).1).val
              (ActiveRoundActions.coordinator p.two_le_m))) := by
      rw [ActiveFollowerArmChoice.followerArmChoice_eq_core]
      exact hcore
    have hprepareOffer := DeclaredFollowerLocalRound.prepare_offer_arm_equation
      rate i r.input.row (r.input.state.activations i) r.input.time
      (r.input.active i) state state memory memory hstart U hoff'
    have harm := hprepareOffer.2 _ hchoice
    have hactualArm := congrArg DeclaredFollowerLocalRound.PreparedRound.arm hprepared
    have hsameArm : (r.output.preparation.followers.followers i).arm =
        ActiveRoundActions.sendArm
          (ActiveFollowerArmChoice.offeredUpBit rate.eta
            (r.input.row.2 r.input.time) i U)
          ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K
            (r.input.row.2 r.input.time).1).val
              (PublicDiscreteDraws.followerPlayer p.two_le_m i))
          ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K
            (r.input.row.2 r.input.time).1).val
              (ActiveRoundActions.coordinator p.two_le_m)) := by
      exact hactualArm.trans harm.1
    exact ⟨U, hoff', rfl,
      (hchoice.trans (congrArg some hsameArm.symm)), hsameArm, rfl, rfl⟩
  · intro hnot
    apply ActiveFollowerQueueOperation.checkedUpOffer_noOffer rate.eta i r.input.row
      (r.input.state.activations i) r.input.time state hstateInput
    intro h
    exact hnot h.1

private theorem current_down_not_accepted
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (t : Fin p.T) (state : ReferencePrelaunchFollower.State p rate.eta)
    (M : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hdown : state.lastDown = some M) :
    ¬ OrdinaryMessageCodec.acceptDown
      (ReferencePrelaunchFollower.codecParams p rate.eta)
      (ReferencePrelaunchFollower.acceptedStart state) (t.val + 1) M := by
  have hstart : ReferencePrelaunchFollower.acceptedStart state = M.val.sigma := by
    simp only [ReferencePrelaunchFollower.acceptedStart, hdown]
  intro haccepted
  exact Nat.lt_irrefl M.val.sigma (hstart ▸ haccepted.1)

private theorem current_up_numerical_fields
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (M : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (U : OrdinaryMessageCodec.UpRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (registers : ℕ × ℕ) (delta : ℕ)
    (hfields : U.val = ActiveFollowerQueueOperation.upOfferFields state)
    (hdown : state.lastDown = some M)
    (hregisters : (state.S, state.backlog) = registers)
    (hdelta : state.delta = delta) :
    U.val.sigma = M.val.sigma ∧ U.val.S = registers.1 ∧
      U.val.delta = delta ∧ U.val.q = registers.2 := by
  obtain ⟨hS, hbacklog⟩ := Prod.mk.inj hregisters
  rw [hfields]
  exact ⟨by simp only [ActiveFollowerQueueOperation.upOfferFields,
    ReferencePrelaunchFollower.acceptedStart, hdown], hS, hdelta, hbacklog⟩

/- The branch below follows the same birth, cutoff, window, and endpoint
selectors as the admitted roots. Only the already-stored-current-DOWN branch
asserts the frozen numerical fields. -/

/-- Propagate the current DOWN's actual cutoff replay through the subsequent
frozen collection. The public result retains the actual cutoff output and the
collection endpoint identities; the inherited branch identifies the same initial
configuration by constructor injectivity and carries its three numerical
fields through every frozen collection step. -/
theorem complete_first_replacement_collection_inherited_numerical_fields
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
    let tail := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v
    let c := v + 1 + tail.length
    match R[v]? with
    | none => True
    | some birth =>
      match birth.output.preparation.coordinator with
      | .collection _ _ _ _ (.laterChosen _ _ _ _ _ _ _ _ _ installed _) =>
        let payload := installed.registers.payload
        let X := (R.drop v).take
          (1 + (ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v).length)
        let C := X.filterMap (ReferenceLaterLiveNumericalReadout.laterLiveReadout s)
        let L := X.length
        C.length = L ∧
        X = birth :: tail ∧
        match R[c]? with
        | none => True
        | some cut =>
          match cut.output.preparation.coordinator with
          | .live _ _ _ (.cutoffChosen _ _ _ _ _ _ _ _ _ _) =>
            let u := cut.input.time.val + 1
            let W := (R.drop (c + 1)).takeWhile
              (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
            let E := fun j => ReferenceCollectionSegmentExtraction.endpointState
              cut.output.next (W.take j)
            ReferenceCollectionPhaseHistory.collectionWindow R c = cut :: W ∧
            E 0 = cut.output.next ∧
            (∀ j : ℕ, j ≤ W.length →
              match R[c + 1 + j]? with
              | some r => r.input.state = E j ∧
                  r.input.time.val = u + j ∧
                  r.input.rows = source.1.2 ∧
                  r.input.selected =
                    ActualInitializationPhysicalStep.selectedRowIndex p source ∧
                  r.input.rewards = rewards ∧
                  (j < W.length → W[j]? = some r ∧ E (j + 1) = r.output.next) ∧
                  (j = W.length →
                    ReferenceCollectionPhaseHistory.laterChosen r.input = true)
              | none => j = W.length ∧ c + 1 + j = R.length ∧
                  ReferenceCompletePhysicalHistory.completeTerminalState
                    rate source rewards C_star C_h = some (E j)) ∧
            ∀ i : Fin (p.m - 1),
              let M := payload.downRecord i
              let a := payload.assignment.assigned i
              let A := fun b => (C.take b).map (fun z =>
                (true, RecordedQueueRun.quantizedArrival
                  (ReferenceFirstLaunchNumericalCell.queueParameters rate) z a))
              let Q := fun b => QueueReplay.replay (4 * rate.n) (0, M.val.q) (A b)
              ∃ old initial : ReferencePrelaunchFollower.State p rate.eta,
                ∃ memory : ActiveFollowerLifecycle.LocalMemory p,
                  cut.input.state.followers i = .ordinary old memory ∧
                  (cut.output.followers i).configuration = .ordinary initial memory ∧
                  (E 0).followers i = .ordinary initial memory ∧
                  initial.status = ActiveRoundActions.FollowerStatus.unoccupied ∧
                  ActiveFollowerLifecycle.localStateDomainValid initial ∧
                  (ReferencePrelaunchFollower.acceptedStart initial < M.val.sigma ∨
                    initial.lastDown = some M) ∧
                  (initial.lastDown = some M →
                    (initial.S, initial.backlog) = Q L ∧
                    initial.delta = (Q L).1 - (Q (L - 1)).1 ∧
                    (∀ j : ℕ, j ≤ W.length →
                      ∃ state : ReferencePrelaunchFollower.State p rate.eta,
                        (E j).followers i = .ordinary state memory ∧
                        state.status = ActiveRoundActions.FollowerStatus.unoccupied ∧
                        state.lastDown = some M ∧
                        (state.S, state.backlog) = Q L ∧
                        state.delta = (Q L).1 - (Q (L - 1)).1 ∧
                        state.initializationFailure = initial.initializationFailure ∧
                        ActiveFollowerLifecycle.localStateDomainValid state) ∧
                    (∀ j : ℕ, (hj : j < W.length) →
                      let r := W.get ⟨j, hj⟩
                      ∃ state logged post,
                        R[c + 1 + j]? = some r ∧
                        r.input.state = E j ∧
                        r.input.time.val = u + j ∧
                        r.input.rows = source.1.2 ∧
                        r.input.selected =
                          ActualInitializationPhysicalStep.selectedRowIndex p source ∧
                        r.input.rewards = rewards ∧
                        r.input.state.followers i = .ordinary state memory ∧
                        state.status = ActiveRoundActions.FollowerStatus.unoccupied ∧
                        state.lastDown = some M ∧
                        (state.S, state.backlog) = Q L ∧
                        state.delta = (Q L).1 - (Q (L - 1)).1 ∧
                        state.initializationFailure = initial.initializationFailure ∧
                        ActiveFollowerLifecycle.localStateDomainValid state ∧
                        ActiveFollowerLifecycle.startRound rate.eta r.input.time
                          state memory = .ok (state, memory) ∧
                        let prepared := r.output.preparation.followers.followers i
                        let own := r.output.preparation.feedback.observations
                          (PublicDiscreteDraws.followerPlayer p.two_le_m i)
                        let view := r.output.preparation.coordinator.downView
                        let diag := ReferenceDownReception.referenceDownCut p
                          view i r.input.row
                          r.input.time own rate logged
                        let decoded := ActiveFollowerDownAcceptance.currentDecodeStep
                          p i r.input.row r.input.time own rate logged
                        let advanced := { logged with downBatch := decoded.1 }
                        ActiveFollowerLogging.checkedLogging i r.input.row
                          (r.input.state.activations i) r.input.time
                          (prepared.arm, own) state = .ok logged ∧
                        prepared.configuration = .ordinary state memory ∧
                        logged.lastDown = some M ∧
                        (logged.S, logged.backlog) = Q L ∧
                        logged.delta = (Q L).1 - (Q (L - 1)).1 ∧
                        logged.initializationFailure = initial.initializationFailure ∧
                        let localRecord := ReferenceActivePhysicalStep.recordFollower
                          view i r.input.row (r.input.state.activations i)
                          r.input.time (r.input.active i) prepared.arm own state
                        localRecord.result = .ok post ∧
                        localRecord.downInput = some logged ∧
                        localRecord.down = some diag ∧
                        DeclaredFollowerLocalRound.consumeDownResult rate
                          diag.outcome = .ok post ∧
                        r.output.followers i =
                          ⟨.ordinary post memory, none, some logged, some diag⟩ ∧
                        (E (j + 1)).followers i = .ordinary post memory ∧
                        post.status = ActiveRoundActions.FollowerStatus.unoccupied ∧
                        post.lastDown = some M ∧
                        (post.S, post.backlog) = Q L ∧
                        post.delta = (Q L).1 - (Q (L - 1)).1 ∧
                        post.initializationFailure = initial.initializationFailure ∧
                        ActiveFollowerLifecycle.localStateDomainValid post ∧
                        (diag.outcome = .skipped logged .notSelectedDown ∨
                          diag.outcome = .decodeOrParseRejected logged advanced decoded.2 ∨
                          diag.outcome = .parsedButUnaccepted logged advanced decoded.2 M) ∧
                        (ActiveFollowerQueueOperation.selectedUpRound i
                            r.input.row (r.input.state.activations i) r.input.time →
                          ∃ U : OrdinaryMessageCodec.UpRecord
                              (ReferencePrelaunchFollower.codecParams p rate.eta),
                            ActiveFollowerQueueOperation.checkedUpOffer rate.eta i
                              r.input.row (r.input.state.activations i) r.input.time state =
                                .offer U ∧
                            U.val = ActiveFollowerQueueOperation.upOfferFields state ∧
                            U.val.sigma = M.val.sigma ∧ U.val.S = (Q L).1 ∧
                            U.val.delta = (Q L).1 - (Q (L - 1)).1 ∧ U.val.q = (Q L).2 ∧
                            ActiveFollowerArmChoice.followerArmChoice state r.input.row
                              r.input.time i (some U) = some prepared.arm ∧
                            ActiveFollowerArmChoice.offeredUpWord rate.eta U =
                              OrdinaryMessageCodec.wordEquivFlat
                                (ReferencePrelaunchFollower.codecParams p rate.eta)
                                (OrdinaryMessageCodec.encodeUp
                                  (ReferencePrelaunchFollower.codecParams p rate.eta) U) ∧
                            ActiveFollowerArmChoice.offeredUpBit rate.eta
                              (r.input.row.2 r.input.time) i U =
                              AffineChannelLaw.affineHash
                                ((r.input.row.2 r.input.time).2 (1, i))
                                (ActiveFollowerArmChoice.offeredUpWord rate.eta U)) ∧
                        (¬ ActiveFollowerQueueOperation.selectedUpRound i r.input.row
                            (r.input.state.activations i) r.input.time →
                          ActiveFollowerQueueOperation.checkedUpOffer rate.eta i
                            r.input.row (r.input.state.activations i) r.input.time state =
                              .noOffer)) ∧
                    match R[c + 1 + W.length]? with
                    | none =>
                      c + 1 + W.length = R.length ∧
                      ReferenceCompletePhysicalHistory.completeTerminalState
                        rate source rewards C_star C_h = some (E W.length)
                    | some next =>
                      ∃ state : ReferencePrelaunchFollower.State p rate.eta,
                          (E W.length).followers i = .ordinary state memory ∧
                          state.status = ActiveRoundActions.FollowerStatus.unoccupied ∧
                          state.lastDown = some M ∧
                          (state.S, state.backlog) = Q L ∧
                          state.delta = (Q L).1 - (Q (L - 1)).1 ∧
                          state.initializationFailure = initial.initializationFailure ∧
                          ActiveFollowerLifecycle.localStateDomainValid state ∧
                          next.input.state = E W.length ∧
                          ReferenceCollectionPhaseHistory.laterChosen next.input = true ∧
                          ActiveFollowerLifecycle.startRound rate.eta next.input.time
                            state memory = .ok (state, memory) ∧
                          (next.output.preparation.followers.followers i).configuration =
                            .ordinary state memory ∧
                          OrdinaryMessageCodec.upAdmissible
                            (ReferencePrelaunchFollower.codecParams p rate.eta)
                            (ActiveFollowerQueueOperation.upOfferFields state) ∧
                          (ActiveFollowerQueueOperation.selectedUpRound i
                              next.input.row (next.input.state.activations i) next.input.time →
                            ∃ U : OrdinaryMessageCodec.UpRecord
                                (ReferencePrelaunchFollower.codecParams p rate.eta),
                              ActiveFollowerQueueOperation.checkedUpOffer rate.eta i
                                next.input.row (next.input.state.activations i) next.input.time
                                state = .offer U ∧
                              U.val = ActiveFollowerQueueOperation.upOfferFields state ∧
                              U.val.sigma = M.val.sigma ∧ U.val.S = (Q L).1 ∧
                              U.val.delta = (Q L).1 - (Q (L - 1)).1 ∧ U.val.q = (Q L).2 ∧
                              ActiveFollowerArmChoice.followerArmChoice state next.input.row
                                next.input.time i (some U) =
                                  some (next.output.preparation.followers.followers i).arm ∧
                              ActiveFollowerArmChoice.offeredUpWord rate.eta U =
                                OrdinaryMessageCodec.wordEquivFlat
                                  (ReferencePrelaunchFollower.codecParams p rate.eta)
                                  (OrdinaryMessageCodec.encodeUp
                                    (ReferencePrelaunchFollower.codecParams p rate.eta) U) ∧
                              ActiveFollowerArmChoice.offeredUpBit rate.eta
                                (next.input.row.2 next.input.time) i U =
                                AffineChannelLaw.affineHash
                                  ((next.input.row.2 next.input.time).2 (1, i))
                                  (ActiveFollowerArmChoice.offeredUpWord rate.eta U)) ∧
                          (¬ ActiveFollowerQueueOperation.selectedUpRound i next.input.row
                              (next.input.state.activations i) next.input.time →
                            ActiveFollowerQueueOperation.checkedUpOffer rate.eta i
                              next.input.row (next.input.state.activations i)
                              next.input.time state = .noOffer))
          | _ => True
      | _ => True := by
  classical
  have hCut :=
    Bandits.Support.ReferenceFirstReplacementCutoffCurrentNumericalOutputs.complete_first_replacement_cutoff_current_numerical_outputs
      rate source rewards C_star C_h
  have hPrefix :=
    Bandits.Support.ReferenceFirstReplacementCollectionPrefix.complete_first_replacement_collection_follower_prefix
      rate source rewards C_star C_h
  dsimp only at hCut hPrefix ⊢
  set R := ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h
  set s := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
  set w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  set v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
  set tail := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v
  set c := v + 1 + tail.length
  cases hb : R[v]? with
  | none =>
      simp only [hb] at hCut hPrefix ⊢
  | some birth =>
      simp only [hb] at hCut hPrefix ⊢
      cases hbirthCoord : birth.output.preparation.coordinator with
      | first _ => trivial
      | live _ _ _ _ => trivial
      | dagger => trivial
      | invalidCollectionCutoff => trivial
      | collection _ _ _ _ outcome =>
          simp only [hbirthCoord] at hCut hPrefix ⊢
          cases outcome <;> try trivial
          rename_i core consistent started hstart instruction hinstruction output hconsistent
            clockData installed birthArm
          dsimp only [ReferenceActivePhysicalStep.collectionInput] at hCut hPrefix ⊢
          let payload : ReferenceActivePhysicalStep.Payload rate :=
            installed.registers.payload
          set X := (R.drop v).take (1 + tail.length)
          let C := X.filterMap (ReferenceLaterLiveNumericalReadout.laterLiveReadout s)
          let L := X.length
          rcases hCut with ⟨hCutLength, hCutX, hCutPositive, hCutAt⟩
          refine ⟨hCutLength, hCutX, ?_⟩
          set cIndex := v + 1 + tail.length
          cases hcutGet : R[cIndex]? with
          | none => trivial
          | some cut =>
              simp only [tail, c, cIndex, hcutGet] at hCutAt hPrefix ⊢
              cases hcutCoord : cut.output.preparation.coordinator with
              | first _ => trivial
              | collection _ _ _ _ _ => trivial
              | dagger => trivial
              | invalidCollectionCutoff => trivial
              | live _ _ _ outcome =>
                  simp only [hcutCoord] at hCutAt hPrefix ⊢
                  cases outcome <;> try trivial
                  dsimp only at hCutAt hPrefix ⊢
                  let u := cut.input.time.val + 1
                  let W := (R.drop (cIndex + 1)).takeWhile
                    (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
                  let E := fun j => ReferenceCollectionSegmentExtraction.endpointState
                    cut.output.next (W.take j)
                  rcases hPrefix with ⟨hwindow, hEzero, hendpoints, hu, huT,
                    hfirst, hseed⟩
                  refine ⟨hwindow, hEzero, hendpoints, ?_⟩
                  rcases hCutAt with ⟨hnotContinuing, hCutBranch⟩
                  rcases hCutBranch with ⟨_, _, _, _, _, _, _, _, _, _, _, hSelectedBlock⟩
                  rcases hSelectedBlock with ⟨selected, hSelection, hSelectedPayload,
                    hPending, hCutoff, hCutFollowers⟩
                  intro i
                  let M := payload.downRecord i
                  let a := payload.assignment.assigned i
                  let A := fun b => (C.take b).map (fun z =>
                    (true, RecordedQueueRun.quantizedArrival
                      (ReferenceFirstLaunchNumericalCell.queueParameters rate) z a))
                  let Q := fun b => QueueReplay.replay (4 * rate.n) (0, M.val.q) (A b)
                  rcases hseed i with
                    ⟨hsigma, hcredit, old, initial, memory, hcutInput,
                      hcutConfiguration, hcutFailure, hinitialEndpoint, hstatus0,
                      hdomain0, hmass0, hdelta0, hzero0, horigin0, hinitialFailure,
                      hpair0, hdates0, hInvariant, hsteps, hterminal⟩
                  rcases hCutFollowers i with ⟨oldCut, memoryCut, hinputCut, hcutRest⟩
                  rcases hcutRest with ⟨hpreparedCut, hstartCut,
                    loggedCut, postCut, hloggingCut, hcutDiagRest⟩
                  rcases hcutDiagRest with
                    ⟨hloggedLastCut, hloggedSCut, hloggedDeltaCut,
                      hloggedBacklogCut, hloggedFailureCut, hloggedStatusCut,
                      hconsumeCut, hpostStatusCut, hpostFailureCut, hrecordCut,
                      hrecordInputCut, hrecordDownCut, hreleaseCut, houtputCut,
                      hpostFailureCut', hchoiceCurrentCut, hbusyCurrentCut,
                      hpostPartitionCut, hpostCurrentCut, hselectedOfferCut,
                      hnoOfferCut⟩
                  have hsameInput :
                      DeclaredFollowerLocalRound.LocalConfiguration.ordinary old memory =
                        .ordinary oldCut memoryCut := hcutInput.symm.trans hinputCut
                  obtain ⟨rfl, rfl⟩ :=
                    DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj hsameInput
                  have hcutOutputConfig : (cut.output.followers i).configuration =
                      .ordinary postCut memory := by
                    rw [houtputCut]
                  have hinitialPost : initial = postCut :=
                    (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
                      (hcutConfiguration.symm.trans hcutOutputConfig)).1
                  have hInitialNumbers : initial.lastDown = some M →
                      (initial.S, initial.backlog) = Q L ∧
                        initial.delta = (Q L).1 - (Q (L - 1)).1 := by
                    intro hcurrent
                    have hpostCurrent : postCut.lastDown = some M := by
                      rw [← hinitialPost]
                      exact hcurrent
                    have hacceptedStart :
                        ReferencePrelaunchFollower.acceptedStart postCut = M.val.sigma := by
                      simp [ReferencePrelaunchFollower.acceptedStart, hpostCurrent]
                    rcases hpostCurrentCut hacceptedStart with
                      ⟨_, hregisters, hdelta⟩
                    constructor
                    · simpa only [hinitialPost] using hregisters
                    · simpa only [hinitialPost] using hdelta
                  have hStepResult : ∀ (j : ℕ) (hj : j < W.length)
                      (state : ReferencePrelaunchFollower.State p rate.eta),
                      (E j).followers i = .ordinary state memory →
                      state.status = ActiveRoundActions.FollowerStatus.unoccupied →
                      state.lastDown = some M →
                      (state.S, state.backlog) = Q L →
                      state.delta = (Q L).1 - (Q (L - 1)).1 →
                      state.initializationFailure = initial.initializationFailure →
                      ActiveFollowerLifecycle.localStateDomainValid state →
                      ∃ logged post,
                        let r := W.get ⟨j, hj⟩
                        R[cIndex + 1 + j]? = some r ∧
                        r.input.state = E j ∧
                        r.input.time.val = u + j ∧
                        r.input.rows = source.1.2 ∧
                        r.input.selected =
                          ActualInitializationPhysicalStep.selectedRowIndex p source ∧
                        r.input.rewards = rewards ∧
                        r.input.state.followers i = .ordinary state memory ∧
                        ActiveFollowerLifecycle.startRound rate.eta r.input.time
                          state memory = .ok (state, memory) ∧
                        let prepared := r.output.preparation.followers.followers i
                        let own := r.output.preparation.feedback.observations
                          (PublicDiscreteDraws.followerPlayer p.two_le_m i)
                        let view := r.output.preparation.coordinator.downView
                        let decoded := ActiveFollowerDownAcceptance.currentDecodeStep
                          p i r.input.row r.input.time own rate logged
                        let diag := ReferenceDownReception.referenceDownCut p view i
                          r.input.row r.input.time own rate logged
                        let advanced := { logged with downBatch := decoded.1 }
                        ActiveFollowerLogging.checkedLogging i r.input.row
                          (r.input.state.activations i) r.input.time
                          (prepared.arm, own) state = .ok logged ∧
                        prepared.configuration = .ordinary state memory ∧
                        logged.lastDown = some M ∧
                        (logged.S, logged.backlog) = Q L ∧
                        logged.delta = (Q L).1 - (Q (L - 1)).1 ∧
                        logged.initializationFailure = initial.initializationFailure ∧
                        let localRecord := ReferenceActivePhysicalStep.recordFollower view i
                          r.input.row (r.input.state.activations i) r.input.time
                          (r.input.active i) prepared.arm own state
                        localRecord.result = .ok post ∧
                        localRecord.downInput = some logged ∧
                        localRecord.down = some diag ∧
                        DeclaredFollowerLocalRound.consumeDownResult rate diag.outcome =
                          .ok post ∧
                        r.output.followers i =
                          ⟨.ordinary post memory, none, some logged, some diag⟩ ∧
                        (E (j + 1)).followers i = .ordinary post memory ∧
                        post.status = ActiveRoundActions.FollowerStatus.unoccupied ∧
                        post.lastDown = some M ∧
                        (post.S, post.backlog) = Q L ∧
                        post.delta = (Q L).1 - (Q (L - 1)).1 ∧
                        post.initializationFailure = initial.initializationFailure ∧
                        ActiveFollowerLifecycle.localStateDomainValid post ∧
                        (diag.outcome = .skipped logged .notSelectedDown ∨
                          diag.outcome = .decodeOrParseRejected logged advanced decoded.2 ∨
                          diag.outcome = .parsedButUnaccepted logged advanced decoded.2 M) ∧
                        (ActiveFollowerQueueOperation.selectedUpRound i
                            r.input.row (r.input.state.activations i) r.input.time →
                          ∃ U : OrdinaryMessageCodec.UpRecord
                              (ReferencePrelaunchFollower.codecParams p rate.eta),
                            ActiveFollowerQueueOperation.checkedUpOffer rate.eta i
                              r.input.row (r.input.state.activations i) r.input.time state =
                                .offer U ∧
                            U.val = ActiveFollowerQueueOperation.upOfferFields state ∧
                            U.val.sigma = M.val.sigma ∧ U.val.S = (Q L).1 ∧
                            U.val.delta = (Q L).1 - (Q (L - 1)).1 ∧ U.val.q = (Q L).2 ∧
                            ActiveFollowerArmChoice.followerArmChoice state r.input.row
                              r.input.time i (some U) = some prepared.arm ∧
                            ActiveFollowerArmChoice.offeredUpWord rate.eta U =
                              OrdinaryMessageCodec.wordEquivFlat
                                (ReferencePrelaunchFollower.codecParams p rate.eta)
                                (OrdinaryMessageCodec.encodeUp
                                  (ReferencePrelaunchFollower.codecParams p rate.eta) U) ∧
                            ActiveFollowerArmChoice.offeredUpBit rate.eta
                              (r.input.row.2 r.input.time) i U =
                              AffineChannelLaw.affineHash
                                ((r.input.row.2 r.input.time).2 (1, i))
                                (ActiveFollowerArmChoice.offeredUpWord rate.eta U)) ∧
                        (¬ ActiveFollowerQueueOperation.selectedUpRound i r.input.row
                            (r.input.state.activations i) r.input.time →
                          ActiveFollowerQueueOperation.checkedUpOffer rate.eta i
                            r.input.row (r.input.state.activations i) r.input.time state =
                              .noOffer) := by
                    intro j hj state hstateEndpoint hstatus hdown hregisters hdelta
                      hfailure hdomain
                    let r := W.get ⟨j, hj⟩
                    have hRGet :=
                      ReferenceFirstReplacementCollectionFollowerPrefix.collectionWindow_get
                        R cIndex j hj
                    have hgeo := hendpoints j (Nat.le_of_lt hj)
                    rw [hRGet] at hgeo
                    rcases hgeo with ⟨hrecordState, htime, hrows, hselected,
                      hrewards, hadvance, _⟩
                    rcases hsteps j hj with
                      ⟨hRStep, stateStep, logged, post, hinputStep,
                        hstatusStep, hdomainStep, hmassStep, hdeltaStep,
                        hfailureStep, hzeroStep, horiginStep, hpairStep,
                        hdatesStep, hstartStep, hpreparedStep, hupStep,
                        hloggingStep, hbufferStep, hlastStep, hSStep,
                        hdeltaLogStep, hbacklogStep, hlogStatusStep,
                        hbatchStep, hinitStep, hlogDomainStep, hoperationStep,
                        hpairLogStep, hdatesLogStep, hrecordStep, hdownInputStep,
                        hdownStep, hreleaseStep, hfinishStep, hreleaseFinishStep,
                        houtputStep, hconsumeStep, hpostStatusStep,
                        hpostDomainStep, hpostMassStep, hpostDeltaStep,
                        hpostFailureStep, hpostZeroStep, hpostOriginStep,
                        hpostPairStep, hpostDatesStep, hexpectedStep,
                        hselectedWordStep, hpreserveStep, hbranchesStep,
                        hnextStep⟩
                    have hinputCurrent : r.input.state.followers i =
                        .ordinary state memory := by
                      rw [hrecordState]
                      exact hstateEndpoint
                    have hsameState :
                        DeclaredFollowerLocalRound.LocalConfiguration.ordinary state memory =
                          .ordinary stateStep memory := hinputCurrent.symm.trans hinputStep
                    have hstateEq :=
                      (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
                        hsameState).1
                    subst stateStep
                    have hloggedDown : logged.lastDown = some M := by
                      rw [hlastStep]
                      exact hdown
                    have hloggedRegisters : (logged.S, logged.backlog) = Q L := by
                      rw [hSStep, hbacklogStep]
                      exact hregisters
                    have hloggedDelta : logged.delta = (Q L).1 - (Q (L - 1)).1 :=
                      hdeltaLogStep.trans hdelta
                    have hloggedFailure :
                        logged.initializationFailure = initial.initializationFailure :=
                      hinitStep.trans hfailure
                    let own := r.output.preparation.feedback.observations
                      (PublicDiscreteDraws.followerPlayer p.two_le_m i)
                    let decoded := ActiveFollowerDownAcceptance.currentDecodeStep
                      p i r.input.row r.input.time own rate logged
                    let diag := ReferenceDownReception.referenceDownCut p
                      r.output.preparation.coordinator.downView i r.input.row
                      r.input.time own rate logged
                    let advanced := { logged with downBatch := decoded.1 }
                    have hpostEq : post = logged ∨ post = advanced := by
                      cases hbranchesStep with
                      | inl hskip =>
                        rcases hskip with ⟨_, _, hpost, _, _, _, _, _⟩
                        exact Or.inl hpost
                      | inr hafterSkip =>
                        cases hafterSkip with
                        | inl hreject =>
                          rcases hreject with ⟨_, _, hpost, _⟩
                          exact Or.inr hpost
                        | inr hafterReject =>
                          cases hafterReject with
                          | inl hunaccepted =>
                            rcases hunaccepted with ⟨_, _, _, _, _, _, _, _, hpost, _⟩
                            exact Or.inr hpost
                          | inr haccepted =>
                            exfalso
                            rcases haccepted with ⟨_, _, _, _, _, _, _, accepted, _⟩
                            exact current_down_not_accepted rate r.input.time logged M
                              hloggedDown accepted
                    obtain ⟨hpostLastFrame, hpostSFrame, hpostDeltaFrame,
                      hpostBacklogFrame⟩ := hpreserveStep hpostEq
                    have hpostDown : post.lastDown = some M := by
                      rw [hpostLastFrame]
                      exact hdown
                    have hpostRegisters : (post.S, post.backlog) = Q L := by
                      rw [hpostSFrame, hpostBacklogFrame]
                      exact hregisters
                    have hpostDelta :
                        post.delta = (Q L).1 - (Q (L - 1)).1 :=
                      hpostDeltaFrame.trans hdelta
                    have hpostFailure :
                        post.initializationFailure = initial.initializationFailure :=
                      hpostFailureStep.trans hfailureStep |>.trans hinitialFailure.symm
                    have hprepEq := actual_record_prepared_eq rate r i state memory
                      hinputCurrent
                    have hoffers := actual_unoccupied_offer rate r i state memory
                      hstatus hdomain hstartStep hprepEq hupStep
                    have hselectedOffer :
                        ActiveFollowerQueueOperation.selectedUpRound i
                            r.input.row (r.input.state.activations i) r.input.time →
                          ∃ U : OrdinaryMessageCodec.UpRecord
                              (ReferencePrelaunchFollower.codecParams p rate.eta),
                            ActiveFollowerQueueOperation.checkedUpOffer rate.eta i
                              r.input.row (r.input.state.activations i) r.input.time state =
                                .offer U ∧
                            U.val = ActiveFollowerQueueOperation.upOfferFields state ∧
                            U.val.sigma = M.val.sigma ∧ U.val.S = (Q L).1 ∧
                            U.val.delta = (Q L).1 - (Q (L - 1)).1 ∧ U.val.q = (Q L).2 ∧
                            ActiveFollowerArmChoice.followerArmChoice state r.input.row
                              r.input.time i (some U) =
                                some (r.output.preparation.followers.followers i).arm ∧
                            ActiveFollowerArmChoice.offeredUpWord rate.eta U =
                              OrdinaryMessageCodec.wordEquivFlat
                                (ReferencePrelaunchFollower.codecParams p rate.eta)
                                (OrdinaryMessageCodec.encodeUp
                                  (ReferencePrelaunchFollower.codecParams p rate.eta) U) ∧
                            ActiveFollowerArmChoice.offeredUpBit rate.eta
                              (r.input.row.2 r.input.time) i U =
                              AffineChannelLaw.affineHash
                                ((r.input.row.2 r.input.time).2 (1, i))
                                (ActiveFollowerArmChoice.offeredUpWord rate.eta U) := by
                      intro hselected
                      rcases hoffers.1 hselected with
                        ⟨U, hcheck, hfields, hchoice, _harm, hword, hbit⟩
                      have hfieldValues := current_up_numerical_fields rate state M U
                        (Q L) ((Q L).1 - (Q (L - 1)).1) hfields hdown hregisters hdelta
                      exact ⟨U, hcheck, hfields, hfieldValues.1, hfieldValues.2.1,
                        hfieldValues.2.2.1, hfieldValues.2.2.2, hchoice, hword, hbit⟩
                    have hnotOffer := hoffers.2
                    refine ⟨logged, post, hRStep, hrecordState, htime, hrows,
                      hselected, hrewards, hinputCurrent, hstartStep, ?_⟩
                    refine ⟨hloggingStep, hpreparedStep, hloggedDown,
                      hloggedRegisters, hloggedDelta, hloggedFailure, ?_⟩
                    refine ⟨hrecordStep, hdownInputStep, hdownStep, hconsumeStep,
                      houtputStep, hnextStep, hpostStatusStep, hpostDown,
                      hpostRegisters, hpostDelta, hpostFailure, hpostDomainStep,
                      ?_, hselectedOffer, hnotOffer⟩
                    cases hbranchesStep with
                    | inl hskip =>
                      rcases hskip with ⟨_, houtcome, _, _, _, _, _, _⟩
                      exact Or.inl houtcome
                    | inr hafterSkip =>
                      cases hafterSkip with
                      | inl hreject =>
                        rcases hreject with ⟨_, houtcome, _, _⟩
                        exact Or.inr (Or.inl houtcome)
                      | inr hafterReject =>
                        cases hafterReject with
                        | inl hunaccepted =>
                          rcases hunaccepted with ⟨_, _, _, _, _, _, _, houtcome, _, _⟩
                          exact Or.inr (Or.inr houtcome)
                        | inr haccepted =>
                          exfalso
                          rcases haccepted with ⟨_, _, _, _, _, _, _, accepted, _⟩
                          exact current_down_not_accepted rate r.input.time logged M
                            hloggedDown accepted
                  have hStrong : ∀ (hcurrent : initial.lastDown = some M),
                      ∀ j : ℕ, j ≤ W.length →
                      ∃ state : ReferencePrelaunchFollower.State p rate.eta,
                        (E j).followers i = .ordinary state memory ∧
                        state.status = ActiveRoundActions.FollowerStatus.unoccupied ∧
                        state.lastDown = some M ∧
                        (state.S, state.backlog) = Q L ∧
                        state.delta = (Q L).1 - (Q (L - 1)).1 ∧
                        state.initializationFailure = initial.initializationFailure ∧
                        ActiveFollowerLifecycle.localStateDomainValid state := by
                    intro hcurrent j
                    induction j with
                    | zero =>
                        intro hj
                        have hnumbers := hInitialNumbers hcurrent
                        exact ⟨initial, hinitialEndpoint, hstatus0, hcurrent,
                          hnumbers.1, hnumbers.2, rfl, hdomain0⟩
                    | succ j ih =>
                        intro hj
                        have hjlt : j < W.length := by omega
                        obtain ⟨state, hstateEndpoint, hstateStatus, hstateDown,
                          hstateRegisters, hstateDelta, hstateFailure, hstateDomain⟩ :=
                          ih (by omega)
                        rcases hStepResult j hjlt state hstateEndpoint hstateStatus
                          hstateDown hstateRegisters hstateDelta hstateFailure hstateDomain with
                          ⟨logged, post, hRStep, hrecordState, htime, hrows, hselected,
                            hrewards, hinput, hstartStep, hloggingStep, hpreparedStep,
                            hloggedDown, hloggedRegisters, hloggedDelta, hloggedFailure,
                            hrecordStep, hdownInputStep, hdownStep, hconsumeStep,
                            houtputStep, hnextEndpoint, hpostStatusStep, hpostDown,
                            hpostRegisters, hpostDelta, hpostFailure, hpostDomain,
                            hrestricted, hselectedOffer, hnotOffer⟩
                        exact ⟨post, hnextEndpoint, hpostStatusStep, hpostDown,
                          hpostRegisters, hpostDelta, hpostFailure, hpostDomain⟩
                  refine ⟨old, initial, memory, hcutInput, hcutConfiguration,
                    hinitialEndpoint, hstatus0, hdomain0, horigin0, ?_⟩
                  intro hcurrent
                  obtain ⟨hinitialRegisters, hinitialDelta⟩ := hInitialNumbers hcurrent
                  refine ⟨hinitialRegisters, hinitialDelta, hStrong hcurrent, ?_⟩
                  constructor
                  · intro j hj
                    obtain ⟨state, hstateEndpoint, hstateStatus, hstateDown,
                      hstateRegisters, hstateDelta, hstateFailure, hstateDomain⟩ :=
                      hStrong hcurrent j (Nat.le_of_lt hj)
                    rcases hStepResult j hj state hstateEndpoint hstateStatus hstateDown
                      hstateRegisters hstateDelta hstateFailure hstateDomain with
                      ⟨logged, post, hRStep, hrecordState, htime, hrows, hselected,
                        hrewards, hinput, hstartStep, hloggingStep, hpreparedStep,
                        hloggedDown, hloggedRegisters, hloggedDelta, hloggedFailure,
                        hrecordStep, hdownInputStep, hdownStep, hconsumeStep,
                        houtputStep, hnextStep, hpostStatusStep, hpostDown,
                        hpostRegisters, hpostDelta, hpostFailure, hpostDomain,
                        hrestricted, hselectedOffer, hnotOffer⟩
                    exact ⟨state, logged, post, hRStep, hrecordState, htime, hrows,
                      hselected, hrewards, hinput, hstateStatus, hstateDown,
                      hstateRegisters, hstateDelta, hstateFailure, hstateDomain,
                      hstartStep, hloggingStep, hpreparedStep, hloggedDown,
                      hloggedRegisters, hloggedDelta, hloggedFailure, hrecordStep,
                      hdownInputStep, hdownStep, hconsumeStep, houtputStep,
                      hnextStep, hpostStatusStep, hpostDown, hpostRegisters,
                      hpostDelta, hpostFailure, hpostDomain, hrestricted,
                      hselectedOffer, hnotOffer⟩
                  · cases hEndGet : R[cIndex + 1 + W.length]? with
                    | none =>
                        simpa only [tail, cIndex, W, hEndGet] using hterminal
                    | some next =>
                        obtain ⟨state, hstateEndpoint, hstateStatus, hstateDown,
                          hstateRegisters, hstateDelta, hstateFailure, hstateDomain⟩ :=
                          hStrong hcurrent W.length (Nat.le_refl _)
                        simp only [tail, cIndex, W, hEndGet] at hterminal ⊢
                        rcases hterminal with ⟨hEndGetP, hnextState, hnextTime,
                          hnextRows, hnextSelected, hnextRewards, hnextLater,
                          stateP, hstateP, hstartP, hpreparedP, hupP⟩
                        have hsameEnd :
                            DeclaredFollowerLocalRound.LocalConfiguration.ordinary
                              state memory = .ordinary stateP memory :=
                          hstateEndpoint.symm.trans hstateP
                        have hstatePEq :=
                          (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
                            hsameEnd).1
                        subst stateP
                        have hinputEnd : next.input.state.followers i =
                            .ordinary state memory := by
                          rw [hnextState]
                          exact hstateEndpoint
                        have hprepEnd := actual_record_prepared_eq rate next i state memory
                          hinputEnd
                        have hoffers := actual_unoccupied_offer rate next i state memory
                          hstateStatus hstateDomain hstartP hprepEnd hupP
                        have hselectedEnd :
                            ActiveFollowerQueueOperation.selectedUpRound i
                                next.input.row (next.input.state.activations i) next.input.time →
                              ∃ U : OrdinaryMessageCodec.UpRecord
                                  (ReferencePrelaunchFollower.codecParams p rate.eta),
                                ActiveFollowerQueueOperation.checkedUpOffer rate.eta i
                                  next.input.row (next.input.state.activations i)
                                  next.input.time state = .offer U ∧
                                U.val = ActiveFollowerQueueOperation.upOfferFields state ∧
                                U.val.sigma = M.val.sigma ∧ U.val.S = (Q L).1 ∧
                                U.val.delta = (Q L).1 - (Q (L - 1)).1 ∧
                                U.val.q = (Q L).2 ∧
                                ActiveFollowerArmChoice.followerArmChoice state
                                  next.input.row next.input.time i (some U) =
                                  some (next.output.preparation.followers.followers i).arm ∧
                                ActiveFollowerArmChoice.offeredUpWord rate.eta U =
                                  OrdinaryMessageCodec.wordEquivFlat
                                    (ReferencePrelaunchFollower.codecParams p rate.eta)
                                    (OrdinaryMessageCodec.encodeUp
                                      (ReferencePrelaunchFollower.codecParams p rate.eta) U) ∧
                                ActiveFollowerArmChoice.offeredUpBit rate.eta
                                  (next.input.row.2 next.input.time) i U =
                                  AffineChannelLaw.affineHash
                                    ((next.input.row.2 next.input.time).2 (1, i))
                                    (ActiveFollowerArmChoice.offeredUpWord rate.eta U) := by
                          intro hselected
                          rcases hoffers.1 hselected with
                            ⟨U, hcheck, hfields, hchoice, _harm, hword, hbit⟩
                          have hfieldValues := current_up_numerical_fields rate state M U
                            (Q L) ((Q L).1 - (Q (L - 1)).1) hfields hstateDown
                            hstateRegisters hstateDelta
                          exact ⟨U, hcheck, hfields, hfieldValues.1,
                            hfieldValues.2.1, hfieldValues.2.2.1,
                            hfieldValues.2.2.2, hchoice, hword, hbit⟩
                        exact ⟨state, hstateEndpoint, hstateStatus, hstateDown,
                          hstateRegisters, hstateDelta, hstateFailure, hstateDomain,
                          hnextState, hnextLater, hstartP, hpreparedP, hupP,
                          hselectedEnd, hoffers.2⟩

end Bandits.Support.ReferenceFirstReplacementCollectionInheritedNumericalFields
