/-
Copyright (c) 2026 The Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteCoordinatorDiagnosticSupport
public import Bandits.Support.ReferenceGeneratedLiveStaleDownExclusion

/-!
# Actual all-phase current DOWN payload exclusion

Sources: `sources/zip4/manuscript/appendix_a_local_protocol.tex:92-109`,
`05_binary_transport.tex:60-124`, `06_interruptions.tex:9-14,40-61,164-177,246-295,327-348`,
and `08_main_theorem.tex:29-42`, all under `sources/zip4/manuscript/`.

These internal results retain the complete original generated physical suffix.
They compose accepted LIVE, COLLECTION and selected-successor results with the
literal pending resets. They do not assert event coverage or manuscript closure.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ReferenceActivePhysicalStep
open ReferenceGeneratedInheritedDownWrongCompletionWitness

namespace Bandits.Support.ReferenceGeneratedCurrentDownPayloadExclusion

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

private theorem selectionAt_fields
    (x : RoundInput p rate) (payload : Payload rate)
    (started : CoordinatorPhaseClock.StartRoundResult p) (time : Fin p.T)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ)
    (choice : CoordinatorRoundDispatch.ArmSelection payload started time weights x.row)
    (v : Selection x) (hv : selectionAt x payload started time weights choice = some v) :
    v.view.payload = payload ∧ v.view.pendingAtChoice = started.pending := by
  classical
  by_cases ht : time = x.time
  · simp only [selectionAt, dite_eq_left ht] at hv
    have heq := Option.some.inj hv
    exact ⟨(congrArg (fun a : Selection x => a.view.payload) heq).symm,
      (congrArg (fun a : Selection x => a.view.pendingAtChoice) heq).symm⟩
  · simp only [selectionAt, dite_eq_right ht] at hv
    cases hv

/-- Inverting a retained actual diagnostic uses only its receiver gate, even
when the subsequent follower recovery or finish fails. -/
private theorem wrong_cut_excluded_of_pending
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1))
    (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (current : Selection record.input)
    (hcurrent : record.output.preparation.coordinator.selection = some current)
    (hcut : (record.output.followers i).down = some cut)
    (hwrong : ReferenceDownReception.wrongUniqueAccepted cut)
    (hpending : i ∈ current.view.pendingAtChoice) :
    cut.raw ≠ some (CoordinatorLocalArmChoice.storedDownFlatWord current.view.payload i) := by
  classical
  intro hraw
  obtain ⟨_choice, _memory, logged, _, _, _, hlogged, _⟩ :=
    ReferenceFollowerSparseEmissionRecovery.actualDownDiagnostic_choice record i cut hcut
  have hactual := ReferenceDownCompletedAmbiguityMeasurability.record_downCut_eq_actual
    record i logged cut hlogged hcut
  have hfalse := hwrong.1
  rw [hactual] at hfalse
  have hcompared :
      (ReferenceDownReception.referenceDownCut p
        record.output.preparation.coordinator.downView i record.input.row record.input.time
        (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i)
        rate logged).rawComparison ≠ none := by
    rw [hfalse]
    decide
  have hsome :
      (ReferenceDownReception.referenceDownCut p
        record.output.preparation.coordinator.downView i record.input.row record.input.time
        (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i)
        rate logged).rawComparison.isSome = true := by
    rw [hfalse]
    rfl
  rw [ReferenceActiveAffinePositiveTest.referenceDownCut_has_call] at hsome
  have hgate : ReferenceActiveAffinePositiveTest.downReceiverGate i record.input.row
      record.input.time logged := of_decide_eq_true hsome
  have hdecode := ReferenceDownReception.referenceDownCut_raw_eq_currentDecodeStep_of_compared
    record.output.preparation.coordinator.downView i record.input.row record.input.time
    (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i) rate logged hcompared
  have hrawActual := hraw
  rw [hactual] at hrawActual
  have hview : record.output.preparation.coordinator.downView = some current.view := by
    simp only [DispatchCut.downView, hcurrent, Option.map_some]
  have hexpected := current.expected_down_word i ⟨hgate.1.1, hgate.1.2, hpending⟩
  have hdecoded :
      (ActiveFollowerDownAcceptance.currentDecodeStep p i record.input.row record.input.time
        (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i) rate logged).2 =
      ReferenceDownReception.expectedDownFlatWord
        record.output.preparation.coordinator.downView i record.input.row record.input.time := by
    rw [hview, hexpected]
    exact hdecode.symm.trans hrawActual
  simp [ReferenceDownReception.referenceDownCut, hgate.1, hgate.2.1,
    hgate.2.2.1, hgate.2.2.2.1, hgate.2.2.2.2, hdecoded] at hfalse

/-- Every actual wrong accepted DOWN cut excludes the currently selected
payload's complete stored word, on every coordinator phase. -/
theorem generated_wrong_down_current_payload_exclusion
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (x : ReferenceGeneratedDownBatchCalendar.LaunchSource rate rewards C_star C_h s hs)
    (i : Fin (p.m - 1)) (n : Fin (p.T - s))
    (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (hcut : ((generatedSourceRecordAt rate rewards C_star C_h s hs x n).output.followers i).down =
      some cut)
    (hwrong : ReferenceDownReception.wrongUniqueAccepted cut) :
    ∃ current : Selection (generatedSourceRecordAt rate rewards C_star C_h s hs x n).input,
      (generatedSourceRecordAt rate rewards C_star C_h s hs x n).output.preparation.coordinator.selection =
        some current ∧
      cut.raw ≠ some (CoordinatorLocalArmChoice.storedDownFlatWord current.view.payload i) := by
  classical
  let R := generatedSourceRecordAt rate rewards C_star C_h s hs x
  have hnonempty := (ReferenceCompleteCoordinatorDiagnosticSupport.generated_coordinator_diagnostic_support
    rate rewards C_star C_h s hs x n).2.1
  obtain ⟨current, hcurrent⟩ := Option.ne_none_iff_exists'.mp hnonempty
  refine ⟨current, hcurrent, ?_⟩
  have hv : (R n).output.preparation.coordinator.selection = some current := hcurrent
  cases hc : (R n).output.preparation.coordinator with
  | first outcome =>
      cases outcome with
      | chosen installed selected =>
          have hf := selectionAt_fields (R n).input _ _ _ _ selected current
            (by simpa only [hc, DispatchCut.selection, liveInput, liveRegistersAt] using hv)
          have heq := Except.ok.inj
            ((CoordinatorAssignmentRegisterInstall.first_start_round_success
              (CoordinatorRoundDispatch.firstLaunchInput (firstInput (R n).input))).symm.trans
                installed.startRound_eq)
          have hp : installed.startRoundResult.pending = Finset.univ := by
            rw [← heq]
            rfl
          apply wrong_cut_excluded_of_pending (R n) i cut current hcurrent hcut hwrong
          rw [hf.2, hp]
          exact Finset.mem_univ i
      | _ => simp [hc, DispatchCut.selection] at hv
  | live registers owned base outcome =>
      cases outcome with
      | continuingChosen dispatched hstart continuation selected =>
          have hl := ReferenceGeneratedLiveStaleDownExclusion.generated_live_current_payload_raw_down_excluded
            rate rewards C_star C_h s hs x n i
          dsimp only at hl
          rw [hc] at hl
          exact hl current (by simpa only [hc] using hv) cut hcut hwrong
      | cutoffChosen dispatched hstart ledger hi hl hd hclock hp ha selected =>
          have hf := selectionAt_fields (R n).input _ _ _ _ selected current
            (by simpa only [hc, DispatchCut.selection, liveInput, liveRegistersAt] using hv)
          apply wrong_cut_excluded_of_pending (R n) i cut current hcurrent hcut hwrong
          rw [hf.2, hp]
          exact Finset.mem_univ i
      | _ => simp [hc, DispatchCut.selection] at hv
  | collection payload ledger clock cutoff outcome =>
      cases outcome with
      | continuing core prepared boundary scores =>
          have hpay : current.view.payload = payload := by
            simp only [hc, DispatchCut.selection] at hv
            exact (congrArg (fun a : Selection (R n).input => a.view.payload)
              (Option.some.inj hv)).symm
          have hne :=
            ReferenceGeneratedRetainedCollectionStaleWordCut.generated_retained_collection_wrong_word
              rate rewards C_star C_h s hs x i n cut hcut hwrong
          have hc' :
              (generatedSourceRecordAt rate rewards C_star C_h s hs x n).output.preparation.coordinator =
                .collection payload ledger clock cutoff (.continuing core prepared boundary scores) := hc
          rw [hpay]
          simpa only [hc'] using hne
      | laterChosen core consistent started hstart instruction hassignment output hconsistent
          clockData installed selected =>
          have hf := selectionAt_fields (R n).input _ _ _ _ selected current
            (by simpa only [hc, DispatchCut.selection, liveInput, liveRegistersAt] using hv)
          have heffect := CoordinatorPhaseClock.startRound_assignment_effect
            p rate.eta.val (R n).input.time clock ledger.pending started instruction
            core.clock_parameter_valid core.clock_registers_valid core.clock_start_time_valid
            hstart hassignment
          rcases heffect with ⟨_, _, _, _, _, _, hp, _⟩
          apply wrong_cut_excluded_of_pending (R n) i cut current hcurrent hcut hwrong
          rw [hf.2, hp]
          exact Finset.mem_univ i
      | _ => simp [hc, DispatchCut.selection] at hv
  | invalidCollectionCutoff => simp [hc, DispatchCut.selection] at hv
  | dagger => simp [hc, DispatchCut.selection] at hv

/-- Every actual earlier expected word, including the current test, differs
from the raw word of a wrong accepted DOWN cut. -/
theorem generated_wrong_down_earlier_expected_ne_raw
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (x : ReferenceGeneratedDownBatchCalendar.LaunchSource rate rewards C_star C_h s hs)
    (i : Fin (p.m - 1)) (n : Fin (p.T - s))
    (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (hcut : ((generatedSourceRecordAt rate rewards C_star C_h s hs x n).output.followers i).down =
      some cut)
    (hwrong : ReferenceDownReception.wrongUniqueAccepted cut)
    (k : Fin (p.T - s)) (hkn : k.val ≤ n.val)
    (oldCut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (hold : ((generatedSourceRecordAt rate rewards C_star C_h s hs x k).output.followers i).down =
      some oldCut) :
    oldCut.expectedWord ≠ cut.raw := by
  classical
  intro hsent
  let R := generatedSourceRecordAt rate rewards C_star C_h s hs x
  obtain ⟨current, hcurrent, hne⟩ := generated_wrong_down_current_payload_exclusion
    rate rewards C_star C_h s hs x i n cut hcut hwrong
  cases hraw : cut.raw with
  | none => exact hwrong.2.1 hraw
  | some word =>
      have hexpected : oldCut.expectedWord = some word := hsent.trans hraw
      obtain ⟨old, holdSelection, _hbranch, hword, _hparse, _hencode⟩ :=
        ReferenceGeneratedInheritedDownCandidateOrigin.actual_expectedDownWord_origin
          (R k) i oldCut word hold hexpected
      have hpayload : old.view.payload = current.view.payload := by
        by_cases hlt : k.val < n.val
        · exact ReferenceGeneratedSelectedSuccessorStaleCut.generated_earlier_sent_wrong_cut_same_selected_payload
            rewards C_star C_h s hs x i n cut hcut hwrong k hlt old current
            holdSelection hcurrent oldCut hold hsent
        · have hindex : k = n := Fin.ext (Nat.le_antisymm hkn (Nat.le_of_not_gt hlt))
          subst k
          exact congrArg (fun a : Selection (R n).input => a.view.payload)
            (Option.some.inj (holdSelection.symm.trans hcurrent))
      apply hne
      rw [hraw, hword, hpayload]
      rfl

end Bandits.Support.ReferenceGeneratedCurrentDownPayloadExclusion

end
