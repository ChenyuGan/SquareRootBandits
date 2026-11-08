/-
Copyright (c) 2026 Bandits Lean regret formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteUnoccupiedNonacceptingForward

import Lean.Elab.Tactic.Omega

/-!
# Actual complete-suffix accepted current DOWN transition

From an ordinary actual CHOICE with an unoccupied follower, derive the selected
current DOWN payload and its same-run installation birth, construct the
assignment mass credit at that birth, and apply the checked receiver transition.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ActiveFollowerLifecycle
open Bandits.Support.ActiveFollowerDownAcceptance
open Bandits.Support.ActiveFollowerLogging
open Bandits.Support.DeclaredFollowerLocalRound
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.ReferenceDownReception
open Bandits.Support.AffineBatchDecoder

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

namespace Bandits.Support.ReferenceCompleteAcceptedCurrentDownForward

/-- An actual unoccupied ordinary CHOICE whose decoded word is the selected
current DOWN word and passes the ordinary acceptance test is accepted by the
checked local receiver. The credit comes from the same selected payload's
installation birth in the original complete-suffix run. -/
theorem complete_ordinary_unoccupied_accepted_current_down_forward
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (source : BootstrapPrivateRoundStreams.SourceInput p) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h
    ∀ (k : Fin R.length),
    let r := R[k.val]
    ∀ (i : Fin (p.m - 1)),
    let f := ReferenceFollowerFixedReply.actualChoice r i
    ∀ (choice : ReferencePrelaunchFollower.State p rate.eta)
      (memory : ActiveFollowerLifecycle.LocalMemory p),
    (hprepared : f.configuration = .ordinary choice memory) →
    (hunoccupied : choice.status = .unoccupied) →
    let t := r.input.time
    let row := r.input.row
    let own := r.output.preparation.feedback.observations
      (PublicDiscreteDraws.followerPlayer p.two_le_m i)
    let view := r.output.preparation.coordinator.downView
    let decoded := ActiveFollowerDownAcceptance.currentDecodeStep p i row t own rate choice
    let expected := ReferenceDownReception.expectedDownFlatWord view i row t
    let parsed := ReferenceDownReception.ordinaryParse p rate decoded.2
    (ActiveFollowerDownAcceptance.downSelected p i row t ∧
      decoded.2 = expected ∧
      ReferenceDownReception.ordinaryLocalAcceptanceTest p rate t choice parsed) →
    ∃ selected : ReferenceActivePhysicalStep.Selection r.input,
      ∃ _hselection : r.output.preparation.coordinator.selection = some selected,
      view = some selected.view ∧
      ∃ _hbranch : ReferenceDownReception.selectedDownSenderBranch selected.view i row t,
      let P := selected.view.payload
      let M := P.downRecord i
      ∃ _hraw : decoded.2 = some (CoordinatorLocalArmChoice.storedDownFlatWord P i),
      ∃ _hparsed : parsed = some M,
      ∃ ha : OrdinaryMessageCodec.acceptDown
        (ReferencePrelaunchFollower.codecParams p rate.eta)
        (ReferencePrelaunchFollower.acceptedStart choice) (t.val + 1) M,
      ∃ (b : Fin R.length) (beta : Fin (p.m - 1) → ℕ),
        b.val ≤ k.val ∧
        ReferenceAssignmentPayloadPersistence.InstallationBirth R[b.val] P ∧
        ReferenceAssignmentCollectionMassSteps.installedBaseScore R[b.val] = some beta ∧
        beta i + M.val.q ≤ (M.val.sigma - 1) * ConstructorDimensions.D p ∧
        ∃ final : ActiveFollowerDownAcceptance.ReplayRegisters,
        let scan := ActiveFollowerDownAcceptance.acceptedCutoffScan p rate M t
          (ActiveFollowerDownAcceptance.acceptedDownStartLE p rate M t choice ha) row
        let ell := scan.endpoint
        let installed : ReferencePrelaunchFollower.State p rate.eta := {
          choice with
          lastDown := some M
          S := final.registers.1
          delta := final.lastService
          backlog := final.registers.2
          downBatch := decoded.1
          buffer := []
          status := if ell = t.val + 2 then .pending else .unoccupied }
        let nextMemory : ActiveFollowerLifecycle.LocalMemory p := if ell = t.val + 2 then
          { lastProposalRead := some {
            timestamp := t
            bit := FollowerCutoffScan.completeRowProposalBit p rate.eta.val row t } }
          else memory
        let cut := ReferenceDownReception.referenceDownCut p view i row t own rate choice
        ActiveFollowerLifecycle.localStateDomainValid choice ∧
        ActiveFollowerDownAcceptance.operationInputDomain p rate choice ∧
        ActiveFollowerLogging.checkedLogging i row (r.input.state.activations i) t
          (f.arm, own) choice = .ok choice ∧
        ActiveFollowerDownAcceptance.checkedRecovery p rate M choice ell = .ok final ∧
        final.registers = ActiveFollowerDownAcceptance.recoveredRegisters p rate M choice ell ∧
        ActiveFollowerDownAcceptance.replay_register_domain
          (ConstructorDimensions.D p) (p.T * ConstructorDimensions.D p) final ∧
        final.registers.1 + final.registers.2 ≤ M.val.q +
          (ell - M.val.sigma) * ConstructorDimensions.D p ∧
        final.registers.1 + final.registers.2 ≤
          (ell - 1) * ConstructorDimensions.D p ∧
        (ell - 1) * ConstructorDimensions.D p ≤ (t.val + 1) * ConstructorDimensions.D p ∧
        final.lastService ≤ ConstructorDimensions.D p ∧
        M.val.sigma < ell ∧
        ell ≤ t.val + 2 ∧
        ell ≤ p.T + 1 ∧
        final.lastService = ActiveFollowerDownAcceptance.recoveredLastService p rate M choice ell
          (ActiveFollowerDownAcceptance.acceptedCutoff_interval_bounds
            p rate M t row choice ha).1 ∧
        (∀ j : ℕ, ∃ middle : ActiveFollowerDownAcceptance.ReplayRegisters,
          ActiveFollowerDownAcceptance.checkedReplay
            (ConstructorDimensions.D p) (p.T * ConstructorDimensions.D p) (4 * rate.n) 0
            ⟨(0, M.val.q), 0⟩
            ((ActiveFollowerDownAcceptance.recoveryQueueRecords p rate M choice ell).take j) =
              .ok middle ∧
          ActiveFollowerDownAcceptance.replay_register_domain
            (ConstructorDimensions.D p) (p.T * ConstructorDimensions.D p) middle ∧
          middle.registers = QueueReplay.replay (4 * rate.n) (0, M.val.q)
            ((ActiveFollowerDownAcceptance.recoveryQueueRecords p rate M choice ell).take j) ∧
          middle.registers.1 + middle.registers.2 ≤
            M.val.q + (min j (ell - M.val.sigma)) * ConstructorDimensions.D p) ∧
        ActiveFollowerDownAcceptance.downTransition p i row t own rate choice =
          .accepted choice installed decoded.2 M scan final.registers final.lastService ∧
        cut.expectedWord = some (CoordinatorLocalArmChoice.storedDownFlatWord P i) ∧
        ReferenceDownReception.expectedDownFlatWord (some selected.view) i row t =
          some (CoordinatorLocalArmChoice.storedDownFlatWord P i) ∧
        decoded.2 = some (CoordinatorLocalArmChoice.storedDownFlatWord P i) ∧
        OrdinaryMessageCodec.parseDown (ReferencePrelaunchFollower.codecParams p rate.eta)
          (decoded.2.map (OrdinaryMessageCodec.wordEquivFlat
            (ReferencePrelaunchFollower.codecParams p rate.eta)).symm) = some M ∧
        cut.raw = decoded.2 ∧
        cut.filteredRaw = decoded.2 ∧
        cut.rawComparison = some true ∧
        cut.ordinaryParse = some M ∧
        cut.ordinaryAcceptance ∧
        cut.outcome = .accepted choice installed decoded.2 M scan final.registers final.lastService ∧
        (ReferenceActivePhysicalStep.recordFollower r.output.preparation.coordinator.downView
          i row (r.input.state.activations i) t (r.input.active i)
          (r.output.preparation.followers.followers i).arm own choice).result = .ok installed ∧
        ActiveFollowerLifecycle.localStateDomainValid installed ∧
        installed.initializationFailure = choice.initializationFailure ∧
        ReferenceFollowerDecoderChronology.downBatchWellFormed decoded.1 ∧
        decoded.1.pending = [] ∧
        ActiveFollowerLifecycle.releaseAfterService rate.eta i t
          (ActiveFollowerLifecycle.publicRowOfCompleteRow row t) own choice installed =
            .ok installed ∧
        ActiveFollowerLifecycle.finishRound rate.eta t row installed memory =
          .ok (installed, nextMemory) ∧
        DeclaredFollowerLocalRound.releaseAndFinish rate i row t own choice memory installed =
          .ok (installed, nextMemory) ∧
        r.output.followers i = {
          configuration := .ordinary installed nextMemory
          failure := none
          downInput := some choice
          down := some cut } ∧
        r.output.next.followers i = .ordinary installed nextMemory := by
  intro R k r i f choice memory hprepared hunoccupied
    t row own view decoded expected parsed hpositive
  rcases hpositive with ⟨hdownSelected, hdecodedExpected, hacceptance⟩
  have hpreparedActual :
      (r.output.preparation.followers.followers i).configuration = .ordinary choice memory := by
    simpa only [f, ReferenceFollowerFixedReply.actualChoice] using hprepared
  cases hparsed : parsed with
  | none =>
      simp [ReferenceDownReception.ordinaryLocalAcceptanceTest, hparsed] at hacceptance
  | some parsedRecord =>
      have hrawNotNone : decoded.2 ≠ none := by
        intro hnone
        have hparsedNone : parsed = none := by
          dsimp only [parsed, ReferenceDownReception.ordinaryParse]
          rw [hnone]
          rfl
        simp [hparsedNone] at hparsed
      cases hselection : r.output.preparation.coordinator.selection with
      | none =>
          have hs : (ReferenceActivePhysicalStep.prepare r.input).coordinator.selection = none := by
            rw [r.output_eq] at hselection
            change (ReferenceActivePhysicalStep.prepare r.input).coordinator.selection = none
              at hselection
            exact hselection
          have hviewNone : r.output.preparation.coordinator.downView = none := by
            rw [r.output_eq]
            change ((ReferenceActivePhysicalStep.prepare r.input).coordinator.selection.map
              ReferenceActivePhysicalStep.Selection.view) = none
            rw [hs]
            rfl
          have hviewNone' : view = none := by simpa [view] using hviewNone
          have hrawNone : decoded.2 = none := by
            calc
              decoded.2 = expected := hdecodedExpected
              _ = none := by
                simp [expected, hviewNone', ReferenceDownReception.expectedDownFlatWord]
          exact (hrawNotNone hrawNone).elim
      | some selected =>
          have hselectionActual :
              r.output.preparation.coordinator.selection = some selected := hselection
          have hview : r.output.preparation.coordinator.downView = some selected.view := by
            have hs : (ReferenceActivePhysicalStep.prepare r.input).coordinator.selection =
                some selected := by
              rw [r.output_eq] at hselectionActual
              change (ReferenceActivePhysicalStep.prepare r.input).coordinator.selection =
                some selected at hselectionActual
              exact hselectionActual
            rw [r.output_eq]
            change (ReferenceActivePhysicalStep.prepare r.input).coordinator.downView = some selected.view
            change ((ReferenceActivePhysicalStep.prepare r.input).coordinator.selection.map
              ReferenceActivePhysicalStep.Selection.view) = some selected.view
            rw [hs]
            rfl
          have hviewActual : view = some selected.view := by simpa [view] using hview
          let P := selected.view.payload
          let M := P.downRecord i
          have hword : ReferenceDownReception.expectedDownFlatWord
              (some selected.view) i row t =
              some (CoordinatorLocalArmChoice.storedDownFlatWord P i) := by
            by_cases hcondition :
                CoordinatorLocalArmChoice.coordinatorArmChoice P selected.view.pendingAtChoice
                  selected.view.cutoff t selected.view.complementWeights row ≠ none ∧
                ReferenceDownReception.selectedDownSenderBranch selected.view i row t
            · exact (ReferenceDownReception.expectedDownFlatWord_eq_some_iff
                selected.view i row t).mpr hcondition
            · have hnone : ReferenceDownReception.expectedDownFlatWord
                  (some selected.view) i row t = none := by
                simp only [ReferenceDownReception.expectedDownFlatWord]
                exact ite_eq_right hcondition
              have hexpectedNone : expected = none := by
                simpa [expected, view, hview] using hnone
              have hrawNone : decoded.2 = none := hdecodedExpected.trans hexpectedNone
              exact False.elim (hrawNotNone hrawNone)
          have hcondition := (ReferenceDownReception.expectedDownFlatWord_eq_some_iff
            selected.view i row t).mp hword
          have hbranch : ReferenceDownReception.selectedDownSenderBranch selected.view i row t := by
            rcases hcondition.2 with ⟨_, _, hpending⟩
            exact ⟨hdownSelected.1, hdownSelected.2, hpending⟩
          have hraw : decoded.2 =
              some (CoordinatorLocalArmChoice.storedDownFlatWord P i) := by
            have hexpected : expected =
                ReferenceDownReception.expectedDownFlatWord
                  (some selected.view) i row t := by
              change ReferenceDownReception.expectedDownFlatWord
                  r.output.preparation.coordinator.downView i r.input.row r.input.time =
                ReferenceDownReception.expectedDownFlatWord
                  (some selected.view) i r.input.row r.input.time
              rw [hview]
            exact hdecodedExpected.trans (hexpected.trans hword)
          have hparsedPayload : parsed = some M := by
            have hparse : ReferenceDownReception.ordinaryParse p rate decoded.2 = some M := by
              rw [hraw]
              change OrdinaryMessageCodec.parseDown
                (ReferencePrelaunchFollower.codecParams p rate.eta)
                (some ((OrdinaryMessageCodec.wordEquivFlat
                  (ReferencePrelaunchFollower.codecParams p rate.eta)).symm
                  (OrdinaryMessageCodec.wordEquivFlat
                    (ReferencePrelaunchFollower.codecParams p rate.eta)
                    (P.downWord i)))) = some M
              simp only [Equiv.symm_apply_apply]
              exact P.parseDown_downWord i
            simpa [parsed] using hparse
          have ha : OrdinaryMessageCodec.acceptDown
              (ReferencePrelaunchFollower.codecParams p rate.eta)
              (ReferencePrelaunchFollower.acceptedStart choice) (t.val + 1) M := by
            have h := hacceptance
            rw [hparsedPayload] at h
            simpa [ReferenceDownReception.ordinaryLocalAcceptanceTest] using h

          obtain ⟨hc, hprefixSpan, hprefix⟩ :=
            ReferenceLaterLiveNumericalReadout.source_record_prefix
              rate rewards C_star C_h source k
          let initial := ReferenceFirstLaunchNumericalCell.launchState
            rate source rewards C_star C_h hc
          let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
            rate source rewards C_star C_h hc
          let start := ReferenceCompletePhysicalHistory.physicalStart
            rate source rewards C_star C_h
          have hlaunch := ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
            rate source rewards C_star C_h hc
          have hrecords := ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
            rate source rewards C_star C_h initial hlaunch
          have hspan : start + (p.T - start) ≤ p.T := by
            dsimp only [start]
            have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T
              rate source rewards C_star C_h
            omega
          let execution := ReferenceActivePhysicalHorizon.run initial source.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start
            (p.T - start) hspan seed.activeAtStart
          have hRun : R = execution.records := by
            simpa [R, execution, start] using hrecords
          have hprefixRecord : r = ReferenceAssignmentPayloadChronology.actualRunRecordAt
              initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
              rewards start k.val hprefixSpan seed.activeAtStart := by
            simpa only [r, R, List.get_eq_getElem] using hprefix
          have hrecordInRun : r ∈ execution.records := by
            rw [← hRun]
            exact List.getElem_mem k.isLt
          have hcurrentTime : r.input.time.val = start + k.val := by
            rw [hprefixRecord]
            rfl
          obtain ⟨birthRecord, hbirthMem, hbirth, hbirthTime, hbirthBefore⟩ :=
            ReferenceSelectedPayloadChronology.actualRun_selectedPayload_has_birth
              initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
              rewards start (p.T - start) hspan seed.activeAtStart seed.coordinatorFirst
              r selected hrecordInRun hselectionActual
          rw [← hRun] at hbirthMem
          obtain ⟨bval, hbval, hbget⟩ := List.mem_iff_getElem.mp hbirthMem
          let b : Fin R.length := ⟨bval, hbval⟩
          have hbrecord : R[b.val] = birthRecord := by simpa [b] using hbget
          have hbirthR : ReferenceAssignmentPayloadPersistence.InstallationBirth R[b.val] P := by
            rw [hbrecord]
            exact hbirth
          have hbirthBeforeCurrent : P.sigma.val ≤ R[k.val].input.time.val := by
            simpa [r] using hbirthBefore
          have hbtime := ReferenceAssignmentFollowerMassSteps.complete_record_time
            rate rewards C_star C_h source b
          have htimeLe : R[b.val].input.time.val ≤ R[k.val].input.time.val := by
            rw [hbrecord]
            exact hbirthTime.trans_le hbirthBeforeCurrent
          have hcurrentTimeK : R[k.val].input.time.val = start + k.val := by
            simpa [r] using hcurrentTime
          have hbk : b.val ≤ k.val := by
            change R[b.val].input.time.val = start + b.val at hbtime
            have htimeIndex : start + b.val ≤ start + k.val := by
              calc
                start + b.val = R[b.val].input.time.val := hbtime.symm
                _ ≤ R[k.val].input.time.val := htimeLe
                _ = start + k.val := hcurrentTimeK
            exact Nat.le_of_add_le_add_left htimeIndex
          obtain ⟨beta, hbase, _hqueues, _hassigned, hdownMass⟩ :=
            ReferenceAssignmentMassComposer.complete_assignment_birth_mass
              rate rewards C_star C_h source b P hbirthR
          have hmass : beta i + M.val.q ≤ (M.val.sigma - 1) * D p := by
            simpa [M] using hdownMass i
          have hbetaNonnegative : 0 ≤ beta i := Nat.zero_le _
          have hcredit : M.val.q ≤ (M.val.sigma - 1) * D p := by
            have h := hmass
            omega
          have hforward := ReferenceCarriedDownForwardTransition.actual_new_current_down_forward
            rate r selected hselectionActual i choice memory hpreparedActual hunoccupied
            hbranch ha hcredit hraw
          have hparsedRecord : some parsedRecord = some M :=
            hparsed.symm.trans hparsedPayload
          rcases hforward with ⟨final, hforwardFacts⟩
          refine ⟨selected, ?_⟩
          refine ⟨rfl, ?_⟩
          refine ⟨hviewActual, ?_⟩
          refine ⟨hbranch, ?_⟩
          refine ⟨hraw, ?_⟩
          refine ⟨hparsedRecord, ?_⟩
          refine ⟨ha, ?_⟩
          refine ⟨b, beta, ?_⟩
          refine ⟨hbk, ?_⟩
          refine ⟨hbirthR, ?_⟩
          refine ⟨hbase, ?_⟩
          refine ⟨hmass, ?_⟩
          refine ⟨final, ?_⟩
          simpa only [t, row, own, view, f, ReferenceFollowerFixedReply.actualChoice, P, M]
            using hforwardFacts

end Bandits.Support.ReferenceCompleteAcceptedCurrentDownForward

end
