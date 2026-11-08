/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstReplacementNumericalSourceRecovery

import Lean.Elab.Tactic.Omega
import Mathlib.Data.List.TakeDrop

/-!
# The first replacement birth's numerical replay

Sources: `sources/zip4/manuscript/06_interruptions.tex:193-233,246-295`,
`sources/zip4/manuscript/05_binary_transport.tex:354-431`,
`sources/zip4/manuscript/04_slow_fast_learner.tex:157-188`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-79`.

This result isolates the actual first replacement birth. Its replay starts at
the transmitted follower queue, which may be nonzero, and uses the actual
enabled birth record. It proves no continuing-round induction, cutoff fact,
global queue identity, or regret theorem.
-/

@[expose] public section
noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceFirstLiveConfirmationHistory
open Bandits.Support.ReferenceCollectionPhaseHistory
open Bandits.Support.ReferenceFirstReplacementLiveFollowerPrefix
open Bandits.Support.ReferenceLaterLiveNumericalReadout
open Bandits.Support.ReferenceFirstWindowNumericalStream
open Bandits.Support.ReferenceFirstLaunchNumericalCell
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.ActiveFollowerLifecycle
open Bandits.Support.ActiveFollowerDownAcceptance
open Bandits.Support.ActiveFollowerLogging
open Bandits.Support.RecordedQueueRun
open Bandits.Support.QueueReplay
open Bandits.Support.PublicDiscreteDraws
open Bandits.Support.ReferenceDownReception
open Bandits.Support.ReferenceAcceptedUpFollowerHistory
open Bandits.Support

namespace Bandits.Support.ReferenceFirstReplacementBirthNumericalReplay

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

private theorem first_replacement_stream_eq_cons
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (v : ℕ) (birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hbirth : records[v]? = some birth) :
    (records.drop v).take
        (1 + (ReferenceFirstReplacementLiveFollowerPrefix.continuingTail records v).length) =
      birth :: ReferenceFirstReplacementLiveFollowerPrefix.continuingTail records v := by
  have hv : v < records.length := (List.getElem?_eq_some_iff.mp hbirth).1
  have hvalue : records[v] = birth := (List.getElem?_eq_some_iff.mp hbirth).2
  have hdrop : records.drop v = birth :: records.drop (v + 1) := by
    rw [List.drop_eq_getElem_cons hv, hvalue]
  have htailPrefix :
      ReferenceFirstReplacementLiveFollowerPrefix.continuingTail records v <+:
        records.drop (v + 1) := List.takeWhile_prefix _
  have htail :
      (records.drop (v + 1)).take
          (ReferenceFirstReplacementLiveFollowerPrefix.continuingTail records v).length =
        ReferenceFirstReplacementLiveFollowerPrefix.continuingTail records v :=
    (List.prefix_iff_eq_take.mp htailPrefix).symm
  rw [hdrop, Nat.one_add, List.take_succ_cons, htail]

/-- At the actual first replacement birth, each follower's PREPARE state is
unoccupied. If the actual DOWN branch occupies it, its registers are exactly
the first enabled replay update from `(0, M.q)`, and that accepted DOWN is
retained on this same birth record. The stream and readout equations identify
the first numerical input with the birth's actual live readout. -/
theorem complete_first_replacement_birth_numerical_replay
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
        let payload := installed.registers.payload
        let tail := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v
        let X := (R.drop v).take (1 + tail.length)
        let C := X.filterMap (ReferenceLaterLiveNumericalReadout.laterLiveReadout s)
        C.length = X.length ∧
        X = birth :: tail ∧
        ∃ c : RecordedQueueRun.RoundInput p.K,
          C[0]? = some c ∧
          ReferenceLaterLiveNumericalReadout.laterLiveReadout s birth = some c ∧
          ∀ i : Fin (p.m - 1),
            let M := payload.downRecord i
            let a := payload.assignment.assigned i
            let A := fun b => (C.take b).map (fun c =>
              (true, RecordedQueueRun.quantizedArrival
                (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a))
            let Q := fun b => QueueReplay.replay (4 * rate.n) (0, M.val.q) (A b)
            ∃ pre preMemory next nextMemory,
              (birth.output.preparation.followers.followers i).configuration =
                .ordinary pre preMemory ∧
              (birth.output.followers i).configuration = .ordinary next nextMemory ∧
              (birth.output.followers i).failure = none ∧
              pre.status = ActiveRoundActions.FollowerStatus.unoccupied ∧
              (next.status ≠ ActiveRoundActions.FollowerStatus.unoccupied →
                next.lastDown = some M ∧
                (next.S, next.backlog) = Q 1 ∧
                next.delta = (Q 1).1 - (Q 0).1 ∧
                ReferenceAcceptedUpFollowerHistory.RetainedDown birth i M)
      | _ => True := by
  classical
  have hsource :=
    ReferenceFirstReplacementNumericalSourceRecovery.complete_first_replacement_numerical_source_stream
      rate source rewards C_star C_h
  have hbirth :=
    ReferenceFirstReplacementDownRecovery.complete_first_replacement_down_recovery_and_finish
      rate source rewards C_star C_h
  dsimp only at hsource hbirth ⊢
  set R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
  set s := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
  set w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  set v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
  cases hb : R[v]? with
  | none => trivial
  | some birth =>
    simp only [hb] at hsource hbirth ⊢
    cases hc : birth.output.preparation.coordinator with
    | first _ => trivial
    | live _ _ _ _ => trivial
    | dagger => trivial
    | invalidCollectionCutoff => trivial
    | collection oldPayload ledger clock cutoff outcome =>
      rw [hc] at hsource hbirth
      cases outcome <;> try trivial
      rename_i core consistent started hs instruction hinstruction output hcons clockData installed arm
      dsimp only [ReferenceActivePhysicalStep.collectionInput] at hsource hbirth ⊢
      let tail := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v
      let X := (R.drop v).take (1 + tail.length)
      let C := X.filterMap (ReferenceLaterLiveNumericalReadout.laterLiveReadout s)
      change C.length = X.length ∧ X = birth :: tail ∧ _
      have hstream : X = birth :: tail := by
        dsimp only [X, tail]
        exact first_replacement_stream_eq_cons R v birth hb
      obtain ⟨hClength, hcells, _hrecoveries⟩ := hsource
      have hXlength : X.length = tail.length + 1 := by rw [hstream]; simp
      have hzeroBound : 0 < X.length := by rw [hXlength]; omega
      have hXhead : X[0]? = some birth := by rw [hstream]; rfl
      have hXget : X.get ⟨0, hzeroBound⟩ = birth := by
        have hget := (List.getElem?_eq_some_iff.mp hXhead).2
        simpa only [List.get_eq_getElem] using hget
      have hcellAt := hcells ⟨0, hzeroBound⟩
      rw [hXget] at hcellAt
      obtain ⟨birthCell, hCget0, hreadBirth, hpayloadBirth, _henabledBirth,
        _hrewardBirth, _hrateBirth, _hmarkerBirth, _hownersBirth⟩ := hcellAt
      refine ⟨hClength, hstream, birthCell.input, hCget0, hreadBirth, ?_⟩
      obtain ⟨_hstartBirth, hbirthAll⟩ := hbirth
      intro i
      obtain ⟨old, birthMemory, logged, _hstateBirth, hbirthUnoccupied,
        hbirthPrepared, hlogging, _hdomain, _hacceptedStart, _hstamp, _hcredit,
        hdownSelected, next, htrace, hbranches⟩ := hbirthAll i
      rcases htrace with ⟨_, _, _, _, hactualFollower, _, _, _, _⟩
      let M := installed.registers.payload.downRecord i
      let a := installed.registers.payload.assignment.assigned i
      let A := fun b => (C.take b).map (fun c =>
        (true, RecordedQueueRun.quantizedArrival
          (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a))
      let Q := fun b => QueueReplay.replay (4 * rate.n) (0, M.val.q) (A b)
      let own := birth.output.preparation.feedback.observations
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)
      let decoded := ActiveFollowerDownAcceptance.currentDecodeStep p i
        birth.input.row birth.input.time own rate logged
      let afterDecode : ReferencePrelaunchFollower.State p rate.eta :=
        { logged with downBatch := decoded.1 }
      let cut := ReferenceDownReception.referenceDownCut p
        (ReferenceActivePhysicalStep.DispatchCut.collection oldPayload ledger clock cutoff
          (CoordinatorRoundDispatch.CollectionOutcome.laterChosen core consistent started hs
            instruction hinstruction output hcons clockData installed arm)).downView
        i birth.input.row birth.input.time own rate logged
      let service := min (4 * rate.n) M.val.q
      let accepted : ReferencePrelaunchFollower.State p rate.eta :=
        { afterDecode with
          lastDown := some M
          S := service
          delta := service
          backlog := M.val.q - service
          status := .pending
          buffer := [] }
      let birthNextMemory : ActiveFollowerLifecycle.LocalMemory p :=
        if next.status = .unoccupied then birthMemory else
          ⟨some ⟨birth.input.time, FollowerCutoffScan.completeRowProposalBit
            p rate.eta.val birth.input.row birth.input.time⟩⟩
      have hprepared :
          (birth.output.preparation.followers.followers i).configuration =
            .ordinary old birthMemory := hbirthPrepared
      have houtput :
          (birth.output.followers i).configuration = .ordinary next birthNextMemory := by
        dsimp only [birthNextMemory]
        rw [hactualFollower]
      have hfailure : (birth.output.followers i).failure = none := by
        rw [hactualFollower]
      by_cases hnextUnoccupied : next.status = ActiveRoundActions.FollowerStatus.unoccupied
      · refine ⟨old, birthMemory, next, birthNextMemory, hprepared, houtput, hfailure,
          hbirthUnoccupied, ?_⟩
        intro hbusy
        exact (hbusy hnextUnoccupied).elim
      · have hnextBusy : next.status ≠ ActiveRoundActions.FollowerStatus.unoccupied := by
          intro h
          exact hnextUnoccupied h
        rcases hbranches with hskip | hrest
        · have hnextLogged : next = logged := hskip.2.2
          have hloggedUnoccupied :
              logged.status = ActiveRoundActions.FollowerStatus.unoccupied := by
            have hframe := ActiveFollowerLogging.checkedLogging_success_frame
              i birth.input.row (birth.input.state.activations i) birth.input.time
              ((birth.output.preparation.followers.followers i).arm,
                birth.output.preparation.feedback.observations
                  (PublicDiscreteDraws.followerPlayer p.two_le_m i))
              old logged hlogging
            exact hbirthUnoccupied ▸ hframe.2.2.2.2.1
          exact (hnextBusy (hnextLogged ▸ hloggedUnoccupied)).elim
        · rcases hrest with hreject | haccepted
          · rcases hreject with ⟨_, _, _, _, _, hnextRejected⟩
            have hloggedUnoccupied :
                logged.status = ActiveRoundActions.FollowerStatus.unoccupied := by
              have hframe := ActiveFollowerLogging.checkedLogging_success_frame
                i birth.input.row (birth.input.state.activations i) birth.input.time
                ((birth.output.preparation.followers.followers i).arm,
                  birth.output.preparation.feedback.observations
                    (PublicDiscreteDraws.followerPlayer p.two_le_m i))
                old logged hlogging
              exact hbirthUnoccupied ▸ hframe.2.2.2.2.1
            have hnextStillUnoccupied :
                next.status = ActiveRoundActions.FollowerStatus.unoccupied := by
              cases hnextRejected
              simp [hloggedUnoccupied]
            exact (hnextBusy hnextStillUnoccupied).elim
          · rcases haccepted with ⟨hselectedBirth, _hdecode, _hraw,
              _hfiltered, _hcomparison, _hparse, _hordinaryAccepted,
              hcutAccepted, _hbufferZero, _hrecoveryRecords,
              _hcheckedRecovery, _hserviceSum, hnextAccepted⟩
            have hcellState : birthCell.states i = old := by
              have hconfig := (birthCell.ordinary i).symm.trans hbirthPrepared
              exact (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj hconfig).1
            have hcellUnoccupied :
                (birthCell.states i).status = ActiveRoundActions.FollowerStatus.unoccupied := by
              rw [hcellState]
              exact hbirthUnoccupied
            have hsourceArmNot :
                ReferenceFirstWindowNumericalStream.sourceArm birth
                  birthCell.selected.view.payload birthCell.selected.view.pendingAtChoice
                  birthCell.states birthCell.selected.view.complementWeights
                  birthCell.selected.view.cutoff birthCell.choiceInputsValid ≠
                    some (birthCell.selected.view.payload.assignment.assigned i) := by
              intro hsourceArm
              have hsourceEvent :=
                (ReferenceFirstLiveUnoccupiedEmission.sourceArm_eq_some_iff_unoccupied
                  birth birthCell i hcellUnoccupied).mp hsourceArm
              have hslotNe : PublicDiscreteDraws.downSlot ≠
                  PublicDiscreteDraws.dataSlot := by decide
              exact hslotNe (hselectedBirth.1.symm.trans hsourceEvent.2.1)
            have harrivalZeroCell :
                RecordedQueueRun.quantizedArrival
                  (ReferenceFirstLaunchNumericalCell.queueParameters rate)
                  birthCell.input
                  (birthCell.selected.view.payload.assignment.assigned i) = 0 := by
              have hquantized := birthCell.quantizedArrival_eq
                (birthCell.selected.view.payload.assignment.assigned i)
              simpa [hsourceArmNot] using hquantized
            have harrivalZero :
                RecordedQueueRun.quantizedArrival
                  (ReferenceFirstLaunchNumericalCell.queueParameters rate)
                  birthCell.input a = 0 := by
              change RecordedQueueRun.quantizedArrival
                (ReferenceFirstLaunchNumericalCell.queueParameters rate) birthCell.input
                (installed.registers.payload.assignment.assigned i) = 0
              rw [← hpayloadBirth]
              exact harrivalZeroCell
            have hCtake : C.take 1 = [birthCell.input] := by
              change C[0]? = some birthCell.input at hCget0
              cases hC : C with
              | nil =>
                  rw [hC] at hCget0
                  cases hCget0
              | cons head rest =>
                  rw [hC] at hCget0
                  have hhead : head = birthCell.input := by simpa using hCget0
                  subst head
                  rfl
            have hAone : A 1 = [(true, 0)] := by
              dsimp only [A]
              rw [hCtake]
              simp [harrivalZero]
            have hQzero : Q 0 = (0, M.val.q) := by
              simp [Q, A, QueueReplay.replay]
            have hQone : Q 1 = (service, M.val.q - service) := by
              change QueueReplay.replay (4 * rate.n) (0, M.val.q) (A 1) = _
              rw [hAone]
              simp [QueueReplay.replay, QueueReplay.transition, service]
            have hretainedBirth : RetainedDown birth i M := by
              refine ⟨logged, cut, accepted, decoded.2,
                ⟨birth.input.time.val + 2, []⟩, (service, M.val.q - service), service,
                ?_, ?_, ?_⟩
              · rw [hactualFollower]
              · rw [hactualFollower]
                rfl
              · exact hcutAccepted
            have hnextRegisters :
                next.lastDown = some M ∧
                  (next.S, next.backlog) = Q 1 ∧
                  next.delta = (Q 1).1 - (Q 0).1 := by
              rw [hnextAccepted]
              refine ⟨?_, ?_, ?_⟩
              · change some (installed.registers.payload.downRecord i) = some M
                rfl
              · change (service, M.val.q - service) = Q 1
                exact hQone.symm
              · change service = (Q 1).1 - (Q 0).1
                rw [hQone, hQzero]
                simp
            refine ⟨old, birthMemory, next, birthNextMemory,
              hprepared, houtput, hfailure, hbirthUnoccupied, ?_⟩
            intro _
            exact ⟨hnextRegisters.1, hnextRegisters.2.1,
              hnextRegisters.2.2, hretainedBirth⟩

end Bandits.Support.ReferenceFirstReplacementBirthNumericalReplay

end
