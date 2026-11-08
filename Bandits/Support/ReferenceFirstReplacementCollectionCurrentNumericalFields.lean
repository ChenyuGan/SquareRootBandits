/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstReplacementCollectionDelayedNumericalReplay
public import Bandits.Support.ReferenceFirstReplacementCollectionInheritedNumericalFields

import Lean.Elab.Tactic.Omega

/-!
# Current cutoff numerical fields at every collection endpoint

Sources: `sources/zip4/manuscript/05_binary_transport.tex:354-431`,
`sources/zip4/manuscript/06_interruptions.tex:193-233,246-299`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-64`.

The same transmitted DOWN queue supplies the numerical replay at every actual
collection endpoint. An old word remains old; the numerical identity is asserted
only when the actual state carries the current word. Both an inherited current
word and its first delayed acceptance are covered. UP offers are local offers
at actual arm choice, including the next assignment boundary.
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

namespace Bandits.Support.ReferenceFirstReplacementCollectionCurrentNumericalFields

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

/-- The current transmitted DOWN's cutoff numerical fields hold at every
subsequent actual collection endpoint, whether inherited at cutoff or first
accepted during collection. The same actual incoming states generate the UP
offers before any next-assignment FINISH. This is a local replay identity. -/
theorem complete_first_replacement_collection_current_numerical_fields
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
        let X := (R.drop v).take (1 + tail.length)
        let C := X.filterMap (ReferenceLaterLiveNumericalReadout.laterLiveReadout s)
        let L := X.length
        C.length = L ∧ X = birth :: tail ∧
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
            1 ≤ L ∧
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
                  (cut.output.followers i).failure = none ∧
                  (E 0).followers i = .ordinary initial memory ∧
                  (∀ j : ℕ, j ≤ W.length →
                    ∃ state : ReferencePrelaunchFollower.State p rate.eta,
                      (E j).followers i = .ordinary state memory ∧
                      state.status = ActiveRoundActions.FollowerStatus.unoccupied ∧
                      ActiveFollowerLifecycle.localStateDomainValid state ∧
                      state.initializationFailure = old.initializationFailure ∧
                      (ReferencePrelaunchFollower.acceptedStart state < M.val.sigma ∨
                        state.lastDown = some M) ∧
                      (state.lastDown = some M →
                        (state.S, state.backlog) = Q L ∧
                        state.delta = (Q L).1 - (Q (L - 1)).1)) ∧
                  (∀ j : ℕ, (hj : j < W.length) →
                    let r := W.get ⟨j, hj⟩
                    ∃ state logged post : ReferencePrelaunchFollower.State p rate.eta,
                      R[c + 1 + j]? = some r ∧
                      r.input.state = E j ∧
                      r.input.state.followers i = .ordinary state memory ∧
                      (E j).followers i = .ordinary state memory ∧
                      state.status = ActiveRoundActions.FollowerStatus.unoccupied ∧
                      ActiveFollowerLifecycle.localStateDomainValid state ∧
                      (ReferencePrelaunchFollower.acceptedStart state < M.val.sigma ∨
                        state.lastDown = some M) ∧
                      (state.lastDown = some M →
                        (state.S, state.backlog) = Q L ∧
                        state.delta = (Q L).1 - (Q (L - 1)).1) ∧
                      ActiveFollowerLifecycle.startRound rate.eta r.input.time
                        state memory = .ok (state, memory) ∧
                      (r.output.preparation.followers.followers i).configuration =
                        .ordinary state memory ∧
                      OrdinaryMessageCodec.upAdmissible
                        (ReferencePrelaunchFollower.codecParams p rate.eta)
                        (ActiveFollowerQueueOperation.upOfferFields state) ∧
                      let prepared := r.output.preparation.followers.followers i
                      let own := r.output.preparation.feedback.observations
                        (PublicDiscreteDraws.followerPlayer p.two_le_m i)
                      let diag := ReferenceDownReception.referenceDownCut p
                        r.output.preparation.coordinator.downView i r.input.row
                        r.input.time own rate logged
                      ActiveFollowerLogging.checkedLogging i r.input.row
                        (r.input.state.activations i) r.input.time
                        (prepared.arm, own) state = .ok logged ∧
                      logged.lastDown = state.lastDown ∧ logged.S = state.S ∧
                      logged.delta = state.delta ∧ logged.backlog = state.backlog ∧
                      DeclaredFollowerLocalRound.consumeDownResult rate diag.outcome =
                        .ok post ∧
                      DeclaredFollowerLocalRound.releaseAndFinish rate i r.input.row
                        r.input.time own state memory post = .ok (post, memory) ∧
                      r.output.followers i =
                        ⟨.ordinary post memory, none, some logged, some diag⟩ ∧
                      (E (j + 1)).followers i = .ordinary post memory ∧
                      (state.lastDown = some M →
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
                            r.input.time i (some U) = some prepared.arm ∧
                          prepared.arm = ActiveRoundActions.sendArm
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
                      next.input.state = E W.length ∧
                      ReferenceCollectionPhaseHistory.laterChosen next.input = true ∧
                      state.status = ActiveRoundActions.FollowerStatus.unoccupied ∧
                      ActiveFollowerLifecycle.localStateDomainValid state ∧
                      (ReferencePrelaunchFollower.acceptedStart state < M.val.sigma ∨
                        state.lastDown = some M) ∧
                      (state.lastDown = some M →
                        (state.S, state.backlog) = Q L ∧
                        state.delta = (Q L).1 - (Q (L - 1)).1) ∧
                      ActiveFollowerLifecycle.startRound rate.eta next.input.time
                        state memory = .ok (state, memory) ∧
                      (next.output.preparation.followers.followers i).configuration =
                        .ordinary state memory ∧
                      OrdinaryMessageCodec.upAdmissible
                        (ReferencePrelaunchFollower.codecParams p rate.eta)
                        (ActiveFollowerQueueOperation.upOfferFields state) ∧
                      (state.lastDown = some M →
                        ActiveFollowerQueueOperation.selectedUpRound i next.input.row
                          (next.input.state.activations i) next.input.time →
                        ∃ U : OrdinaryMessageCodec.UpRecord
                            (ReferencePrelaunchFollower.codecParams p rate.eta),
                          ActiveFollowerQueueOperation.checkedUpOffer rate.eta i
                            next.input.row (next.input.state.activations i)
                            next.input.time state = .offer U ∧
                          U.val = ActiveFollowerQueueOperation.upOfferFields state ∧
                          U.val.sigma = M.val.sigma ∧ U.val.S = (Q L).1 ∧
                          U.val.delta = (Q L).1 - (Q (L - 1)).1 ∧ U.val.q = (Q L).2 ∧
                          ActiveFollowerArmChoice.followerArmChoice state next.input.row
                            next.input.time i (some U) =
                              some (next.output.preparation.followers.followers i).arm ∧
                          (next.output.preparation.followers.followers i).arm =
                            ActiveRoundActions.sendArm
                              (ActiveFollowerArmChoice.offeredUpBit rate.eta
                                (next.input.row.2 next.input.time) i U)
                              ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K
                                (next.input.row.2 next.input.time).1).val
                                  (PublicDiscreteDraws.followerPlayer p.two_le_m i))
                              ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K
                                (next.input.row.2 next.input.time).1).val
                                  (ActiveRoundActions.coordinator p.two_le_m)) ∧
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
                          next.input.row (next.input.state.activations i) next.input.time
                          state = .noOffer)
          | _ => True
      | _ => True := by
  classical
  have hI :=
    ReferenceFirstReplacementCollectionInheritedNumericalFields.complete_first_replacement_collection_inherited_numerical_fields
      rate source rewards C_star C_h
  have hD :=
    ReferenceFirstReplacementCollectionDelayedNumericalReplay.complete_first_replacement_collection_delayed_numerical_replay
      rate source rewards C_star C_h
  have hP :=
    ReferenceFirstReplacementCollectionPrefix.complete_first_replacement_collection_follower_prefix
      rate source rewards C_star C_h
  dsimp only at hI hD hP ⊢
  set R := ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h
  set s := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
  set w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  set v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
  set tail := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v
  set c := v + 1 + tail.length
  cases hb : R[v]? with
  | none => simp only [hb] at hI hD hP ⊢
  | some birth =>
    simp only [hb] at hI hD hP ⊢
    cases hbirthCoord : birth.output.preparation.coordinator with
    | first _ => trivial
    | live _ _ _ _ => trivial
    | dagger => trivial
    | invalidCollectionCutoff => trivial
    | collection _ _ _ _ outcome =>
      simp only [hbirthCoord] at hI hD hP ⊢
      cases outcome <;> try trivial
      rename_i core consistent started hstart instruction hinstruction output hconsistent
        clockData installed birthArm
      dsimp only [ReferenceActivePhysicalStep.collectionInput] at hI hD hP ⊢
      let payload : ReferenceActivePhysicalStep.Payload rate := installed.registers.payload
      let X := (R.drop v).take (1 + tail.length)
      let C := X.filterMap (ReferenceLaterLiveNumericalReadout.laterLiveReadout s)
      let L := X.length
      rcases hI with ⟨hClength, hX, hI⟩
      refine ⟨hClength, hX, ?_⟩
      cases hc : R[c]? with
      | none => trivial
      | some cut =>
        simp only [tail, c, hc] at hI hD hP ⊢
        cases hcutCoord : cut.output.preparation.coordinator with
        | first _ => trivial
        | collection _ _ _ _ _ => trivial
        | dagger => trivial
        | invalidCollectionCutoff => trivial
        | live _ _ _ outcome =>
          simp only [hcutCoord] at hI hD hP ⊢
          cases outcome <;> try trivial
          dsimp only at hI hD hP ⊢
          let u := cut.input.time.val + 1
          let W := (R.drop (c + 1)).takeWhile
            (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
          let E := fun j => ReferenceCollectionSegmentExtraction.endpointState
            cut.output.next (W.take j)
          rcases hI with ⟨hwindowI, hEzeroI, hendpointsI, hseedI⟩
          rcases hD with ⟨hClengthD, hXD, hLpositive, hdelayed⟩
          rcases hP with ⟨hwindow, hEzero, hendpoints, hu, huT, hfirst, hseed⟩
          refine ⟨hLpositive, hwindow, hEzero, hendpoints, ?_⟩
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
          rcases hseedI i with
            ⟨oldI, initialI, memoryI, hcutInputI, hcutConfigurationI,
              hinitialEndpointI, hstatusI, hdomainI, horiginI, hcurrentI⟩
          have hsameCutInput := hcutInput.symm.trans hcutInputI
          obtain ⟨rfl, rfl⟩ :=
            DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj hsameCutInput
          have hinitialEq :=
            (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
              (hcutConfiguration.symm.trans hcutConfigurationI)).1
          subst initialI
          have hInitialNumbers : initial.lastDown = some M →
              (initial.S, initial.backlog) = Q L ∧
              initial.delta = (Q L).1 - (Q (L - 1)).1 := by
            intro hcurrent
            exact ⟨(hcurrentI hcurrent).1, (hcurrentI hcurrent).2.1⟩
          have hNumbers : ∀ j : ℕ, j ≤ W.length →
              ∀ state : ReferencePrelaunchFollower.State p rate.eta,
                (E j).followers i = .ordinary state memory →
                state.lastDown = some M →
                (state.S, state.backlog) = Q L ∧
                state.delta = (Q L).1 - (Q (L - 1)).1 := by
            intro j
            induction j with
            | zero =>
              intro hj state hstate hcurrent
              have heq :=
                (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
                  (hstate.symm.trans hinitialEndpoint)).1
              subst state
              exact hInitialNumbers hcurrent
            | succ j ih =>
              intro hj state hstate hcurrent
              have hjlt : j < W.length := by omega
              let r := W.get ⟨j, hjlt⟩
              rcases hsteps j hjlt with
                ⟨hRStep, before, logged, post, hinputStep,
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
              have heq :=
                (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
                  (hstate.symm.trans hnextStep)).1
              subst state
              have hgeo := hendpoints j (Nat.le_of_lt hjlt)
              rw [hRStep] at hgeo
              have hrecordState : r.input.state = E j := hgeo.1
              have hbeforeEndpoint : (E j).followers i = .ordinary before memory := by
                rw [← hrecordState]
                exact hinputStep
              have hframe : post = logged ∨
                  post = { logged with downBatch :=
                    (ActiveFollowerDownAcceptance.currentDecodeStep p i r.input.row
                      r.input.time
                      (r.output.preparation.feedback.observations
                        (PublicDiscreteDraws.followerPlayer p.two_le_m i))
                      rate logged).1 } →
                  (post.S, post.backlog) = Q L ∧
                  post.delta = (Q L).1 - (Q (L - 1)).1 := by
                intro hpost
                obtain ⟨hlast, hS, hdelta, hbacklog⟩ := hpreserveStep hpost
                have hbeforeCurrent : before.lastDown = some M :=
                  hlast.symm.trans hcurrent
                have hbeforeNumbers := ih (by omega) before hbeforeEndpoint hbeforeCurrent
                constructor
                · rw [hS, hbacklog]
                  exact hbeforeNumbers.1
                · exact hdelta.trans hbeforeNumbers.2
              cases hbranchesStep with
              | inl hskip =>
                exact hframe (Or.inl hskip.2.2.1)
              | inr hrest =>
                cases hrest with
                | inl hreject =>
                  exact hframe (Or.inr hreject.2.2.1)
                | inr hrest =>
                  cases hrest with
                  | inl hunaccepted =>
                    rcases hunaccepted with
                      ⟨_, _, _, _, _, _, _, _, hpost, _⟩
                    exact hframe (Or.inr hpost)
                  | inr haccepted =>
                    rcases haccepted with
                      ⟨_, _, _, _, _, _, _, accepted, recovered,
                        hscan, hrecovery, houtcome, hpost, hrest⟩
                    have hDAt := hdelayed ⟨j, hjlt⟩
                    rcases hDAt with ⟨_, _, _, _, _, _, hDDown⟩
                    have hDDownAt := hDDown i
                    rw [houtputStep] at hDDownAt
                    simp only at hDDownAt
                    rw [houtcome] at hDDownAt
                    rcases hDDownAt with
                      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _,
                        hregistersD, hlastServiceD, _, hpostRegistersD,
                        hpostDeltaD, _⟩
                    exact ⟨hpostRegistersD, hpostDeltaD.trans hlastServiceD⟩
          refine ⟨old, initial, memory, hcutInput, hcutConfiguration,
            hcutFailure, hinitialEndpoint, ?_, ?_, ?_⟩
          · intro j hj
            rcases hInvariant j hj with
              ⟨state, hstate, hstatus, hdomain, hmass, hdelta, hfailure,
                hzero, horigin, hpair, hdates⟩
            exact ⟨state, hstate, hstatus, hdomain, hfailure, horigin,
              hNumbers j hj state hstate⟩
          · intro j hj
            let r := W.get ⟨j, hj⟩
            rcases hsteps j hj with
              ⟨hRStep, state, logged, post, hinputStep,
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
            have hgeo := hendpoints j (Nat.le_of_lt hj)
            rw [hRStep] at hgeo
            have hrecordState : r.input.state = E j := hgeo.1
            have hstateEndpoint : (E j).followers i = .ordinary state memory := by
              rw [← hrecordState]
              exact hinputStep
            have hnum := hNumbers j (Nat.le_of_lt hj) state hstateEndpoint
            have hprep := actual_record_prepared_eq rate r i state memory hinputStep
            have hoffers := actual_unoccupied_offer rate r i state memory
              hstatusStep hdomainStep hstartStep hprep hupStep
            refine ⟨state, logged, post, hRStep, hgeo.1, hinputStep,
              hstateEndpoint, hstatusStep, hdomainStep, horiginStep, hnum,
              hstartStep, hpreparedStep, hupStep, hloggingStep, hlastStep,
              hSStep, hdeltaLogStep, hbacklogStep, hconsumeStep,
              hreleaseFinishStep, houtputStep, hnextStep, ?_, hoffers.2⟩
            intro hcurrent hselected
            rcases hoffers.1 hselected with
              ⟨U, hcheck, hfields, hchoice, harm, hword, hbit⟩
            have hnumbers := hnum hcurrent
            have hvalues := current_up_numerical_fields rate state M U
              (Q L) ((Q L).1 - (Q (L - 1)).1) hfields hcurrent
              hnumbers.1 hnumbers.2
            exact ⟨U, hcheck, hfields, hvalues.1, hvalues.2.1,
              hvalues.2.2.1, hvalues.2.2.2, hchoice, harm, hword, hbit⟩
          · cases hEndGet : R[c + 1 + W.length]? with
            | none =>
              simpa only [tail, c, W, hEndGet] using hterminal
            | some next =>
              simp only [tail, c, W, hEndGet] at hterminal ⊢
              rcases hterminal with
                ⟨hEndGetP, hnextState, hnextTime, hnextRows, hnextSelected,
                  hnextRewards, hnextLater, state, hstate, hstart, hprepared, hup⟩
              rcases hInvariant W.length (Nat.le_refl _) with
                ⟨stateP, hstateP, hstatus, hdomain, hmass, hdelta, hfailure,
                  hzero, horigin, hpair, hdates⟩
              have heq :=
                (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
                  (hstate.symm.trans hstateP)).1
              subst stateP
              have hnum := hNumbers W.length (Nat.le_refl _) state hstate
              have hinput : next.input.state.followers i = .ordinary state memory := by
                rw [hnextState]
                exact hstate
              have hprep := actual_record_prepared_eq rate next i state memory hinput
              have hoffers := actual_unoccupied_offer rate next i state memory
                hstatus hdomain hstart hprep hup
              refine ⟨state, hstate, hnextState, hnextLater, hstatus, hdomain,
                horigin, hnum, hstart, hprepared, hup, ?_, hoffers.2⟩
              intro hcurrent hselected
              rcases hoffers.1 hselected with
                ⟨U, hcheck, hfields, hchoice, harm, hword, hbit⟩
              have hnumbers := hnum hcurrent
              have hvalues := current_up_numerical_fields rate state M U
                (Q L) ((Q L).1 - (Q (L - 1)).1) hfields hcurrent
                hnumbers.1 hnumbers.2
              exact ⟨U, hcheck, hfields, hvalues.1, hvalues.2.1,
                hvalues.2.2.1, hvalues.2.2.2, hchoice, harm, hword, hbit⟩

end Bandits.Support.ReferenceFirstReplacementCollectionCurrentNumericalFields
