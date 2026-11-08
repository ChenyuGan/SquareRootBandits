/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCarriedDownRecoveryBudget

import Lean.Elab.Tactic.Omega

/-!
# Actual accepted newer DOWN transition

This module constructs the ordinary local PREPARE-to-output transition for
one actual, current, selected newer DOWN word. The carried recovery credit and
the returned decoder option remain explicit local branch inputs.
-/

@[expose] public section

namespace Bandits.Support.ReferenceCarriedDownForwardTransition

open Bandits.Support
open ConstructorDimensions
open ReferenceActivePhysicalStep
open ReferenceActivePhysicalHorizon
open ReferencePrelaunchFollower
open ActiveFollowerLifecycle
open ActiveFollowerDownAcceptance
open ReferenceDownReception
open DeclaredFollowerLocalRound
open OrdinaryMessageCodec
open CoordinatorLocalArmChoice
open PublicDiscreteDraws
open CompletePublicTable

variable {p : ConstructorDimensions.Parameters}

variable (rate : ReferenceActivePhysicalStep.RateInput p)

/-- Re-type the actual carried local buffer checks to the DOWN operation's
slightly more explicit pre-call input predicate. -/
theorem operationInputDomain_of_localStateDomainValid
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (hstate : ActiveFollowerLifecycle.localStateDomainValid state) :
    ActiveFollowerDownAcceptance.operationInputDomain p rate state := by
  rcases hstate with ⟨hregisters, hbuffer, hdecoder⟩
  refine ⟨hregisters, hdecoder, ?_⟩
  refine ⟨?_, ActiveFollowerLifecycle.localBufferValid_keys_nodup hbuffer⟩
  intro record hrecord
  obtain ⟨hfirst, hlast⟩ :=
    ActiveFollowerLifecycle.localBufferValid_timestamp hbuffer record hrecord
  obtain ⟨q, hq, hgrid⟩ :=
    ActiveFollowerLifecycle.localBufferValid_observation_grid hbuffer record hrecord
  refine ⟨hfirst, hlast, ⟨⟨q, ?_⟩, ?_⟩⟩
  · exact Nat.lt_succ_of_le hq
  · exact hgrid

/-- The actual successful follower PREPARE supplies the full pre-call local
domains. Its StartRound guard is used before transporting the frame to CHOICE.
-/
theorem actual_prepare_local_domains
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1))
    (choice : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hprepared : (r.output.preparation.followers.followers i).configuration =
      .ordinary choice memory) :
    ActiveFollowerLifecycle.localStateDomainValid choice ∧
      ActiveFollowerDownAcceptance.operationInputDomain p rate choice := by
  have hprepare :
      (DeclaredFollowerLocalRound.prepare rate i r.input.row
        (r.input.state.activations i) r.input.time (r.input.active i)
        (r.input.state.followers i)).configuration = .ordinary choice memory := by
    rw [r.output_eq] at hprepared
    change (DeclaredFollowerLocalRound.prepare rate i r.input.row
      (r.input.state.activations i) r.input.time (r.input.active i)
      (r.input.state.followers i)).configuration = .ordinary choice memory at hprepared
    exact hprepared
  obtain ⟨before, beforeMemory, _, hstart, _, _⟩ :=
    ReferenceFollowerReplyChronology.prepare_ordinary_inversion i r.input.row
      (r.input.state.activations i) r.input.time (r.input.active i)
      (r.input.state.followers i) choice memory hprepare
  have hbefore : ActiveFollowerLifecycle.localStateDomainValid before := by
    by_contra hbad
    have herr := ActiveFollowerLifecycle.interruptionDecision_invalid_domain
      rate.eta r.input.time before beforeMemory hbad
    simp [ActiveFollowerLifecycle.startRound, herr] at hstart
  have hframe := ActiveFollowerLifecycle.startRound_frame rate.eta r.input.time
    before choice beforeMemory memory hstart
  rcases hbefore with ⟨hservice, hbuffer, hdecoder⟩
  rcases hframe with ⟨_, hscore, hlastService, hbacklog, hbatch, hlog, _, _⟩
  have hchoice : ActiveFollowerLifecycle.localStateDomainValid choice := by
    unfold ActiveFollowerLifecycle.localStateDomainValid
    refine ⟨?_, ?_, ?_⟩
    · simpa [ActiveFollowerLifecycle.serviceRegistersValid,
        hscore, hlastService, hbacklog] using hservice
    · simpa [ActiveFollowerLifecycle.localBufferValid, hlog] using hbuffer
    · simpa [ActiveFollowerLifecycle.downDecoderStateValid, hbatch] using hdecoder
  exact ⟨hchoice, operationInputDomain_of_localStateDomainValid rate choice hchoice⟩

/-- A returned word from the current actual decoder step clears its pending
suffix. This follows from the public decoder output and step definitions. -/
theorem currentDecodeStep_pending_empty_of_some
    (i : Fin (p.m - 1))
    (row : CompletePublicTable.CompleteRow p)
    (t : Fin p.T)
    (own : ReferencePrelaunchFollower.Observation p)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (word : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (hbatch : ReferenceFollowerDecoderChronology.downBatchWellFormed state.downBatch)
    (hword :
      (ActiveFollowerDownAcceptance.currentDecodeStep p i row t own rate state).2 = some word) :
    (ActiveFollowerDownAcceptance.currentDecodeStep p i row t own rate state).1.pending = [] := by
  let trace := ActiveFollowerDownAcceptance.currentInputExtension p
    (ActiveFollowerDownAcceptance.currentRoundInput p i row t own rate state)
  have houtput : AffineBatchDecoder.stepOutput p trace state.downBatch t = some word := by
    simpa [ActiveFollowerDownAcceptance.currentDecodeStep, trace,
      AffineBatchDecoder.decodeStep] using hword
  have hquota :=
    (AffineBatchDecoder.stepOutput_eq_some_iff p trace state.downBatch t word).mp houtput
  have hlength :
      (state.downBatch.pending ++ AffineBatchDecoder.positiveAt p trace t).length ≤
        AffineBatchDecoder.quota p := by
    obtain ⟨hpending, _⟩ := hbatch
    by_cases heligible : AffineBatchDecoder.eligible (trace t)
    · simp [AffineBatchDecoder.positiveAt, heligible]
      omega
    · simp [AffineBatchDecoder.positiveAt, heligible]
      exact hpending.le
  have hequal :
      (state.downBatch.pending ++ AffineBatchDecoder.positiveAt p trace t).length =
        AffineBatchDecoder.quota p := by
    omega
  change (AffineBatchDecoder.step p trace state.downBatch t).pending = []
  simp [AffineBatchDecoder.step, hequal]

/-- The actual PREPARE, feedback, checked logging, matching DOWN filter,
accepted cutoff scan, checked recovery, release, and finish form one connected
ordinary follower transition. The only branch data beyond actual PREPARE are
the current selected-DOWN branch, the literal current decoder option, local
acceptance, and the visible carried queue credit. -/
theorem actual_new_current_down_forward
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (selected : ReferenceActivePhysicalStep.Selection r.input)
    (hselection : r.output.preparation.coordinator.selection = some selected)
    (i : Fin (p.m - 1))
    (choice : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hprepared : (r.output.preparation.followers.followers i).configuration =
      .ordinary choice memory)
    (hunoccupied : choice.status = .unoccupied)
    (hbranch : ReferenceDownReception.selectedDownSenderBranch selected.view i
      r.input.row r.input.time)
    (ha : OrdinaryMessageCodec.acceptDown
      (ReferencePrelaunchFollower.codecParams p rate.eta)
      (ReferencePrelaunchFollower.acceptedStart choice) (r.input.time.val + 1)
      (selected.view.payload.downRecord i))
    (hcredit : (selected.view.payload.downRecord i).val.q ≤
      ((selected.view.payload.downRecord i).val.sigma - 1) * ConstructorDimensions.D p)
    (hraw : (ActiveFollowerDownAcceptance.currentDecodeStep p i r.input.row r.input.time
      (r.output.preparation.feedback.observations (PublicDiscreteDraws.followerPlayer
        p.two_le_m i)) rate choice).2 =
      some (CoordinatorLocalArmChoice.storedDownFlatWord selected.view.payload i)) :
    let t := r.input.time
    let row := r.input.row
    let own := r.output.preparation.feedback.observations
      (PublicDiscreteDraws.followerPlayer p.two_le_m i)
    let M := selected.view.payload.downRecord i
    let decoded := ActiveFollowerDownAcceptance.currentDecodeStep p i row t own rate choice
    let scan := ActiveFollowerDownAcceptance.acceptedCutoffScan p rate M t
      (ActiveFollowerDownAcceptance.acceptedDownStartLE p rate M t choice ha) row
    let ell := scan.endpoint
    let cut := ReferenceDownReception.referenceDownCut p
      r.output.preparation.coordinator.downView i row t own rate choice
    ∃ final : ActiveFollowerDownAcceptance.ReplayRegisters,
    let installed : ReferencePrelaunchFollower.State p rate.eta := {
      choice with
      lastDown := some M
      S := final.registers.1
      delta := final.lastService
      backlog := final.registers.2
      downBatch := decoded.1
      buffer := []
      status := if ell = t.val + 2 then .pending else .unoccupied };
    let nextMemory : ActiveFollowerLifecycle.LocalMemory p :=
      if ell = t.val + 2 then
        { lastProposalRead := some {
          timestamp := t
          bit := FollowerCutoffScan.completeRowProposalBit p rate.eta.val row t } }
      else memory;
      ActiveFollowerLifecycle.localStateDomainValid choice ∧
      ActiveFollowerDownAcceptance.operationInputDomain p rate choice ∧
      ActiveFollowerLogging.checkedLogging i row (r.input.state.activations i) t
        ((r.output.preparation.followers.followers i).arm, own) choice = .ok choice ∧
      ActiveFollowerDownAcceptance.checkedRecovery p rate M choice ell = .ok final ∧
      final.registers = ActiveFollowerDownAcceptance.recoveredRegisters p rate M choice ell ∧
      ActiveFollowerDownAcceptance.replay_register_domain (D p) (p.T * D p) final ∧
      final.registers.1 + final.registers.2 ≤ M.val.q + (ell - M.val.sigma) * D p ∧
      final.registers.1 + final.registers.2 ≤ (ell - 1) * D p ∧
      (ell - 1) * D p ≤ (t.val + 1) * D p ∧
      final.lastService ≤ D p ∧
      M.val.sigma < ell ∧
      ell ≤ t.val + 2 ∧
      ell ≤ p.T + 1 ∧
      final.lastService = ActiveFollowerDownAcceptance.recoveredLastService p rate M choice ell
        (ActiveFollowerDownAcceptance.acceptedCutoff_interval_bounds
          p rate M t row choice ha).1 ∧
      (∀ j : ℕ, ∃ middle : ActiveFollowerDownAcceptance.ReplayRegisters,
        ActiveFollowerDownAcceptance.checkedReplay (D p) (p.T * D p) (4 * rate.n) 0
          ⟨(0, M.val.q), 0⟩
          ((ActiveFollowerDownAcceptance.recoveryQueueRecords p rate M choice ell).take j) =
            .ok middle ∧
        ActiveFollowerDownAcceptance.replay_register_domain (D p) (p.T * D p) middle ∧
        middle.registers = QueueReplay.replay (4 * rate.n) (0, M.val.q)
          ((ActiveFollowerDownAcceptance.recoveryQueueRecords p rate M choice ell).take j) ∧
        middle.registers.1 + middle.registers.2 ≤
          M.val.q + (min j (ell - M.val.sigma)) * D p) ∧
      ActiveFollowerDownAcceptance.downTransition p i row t own rate choice =
        .accepted choice installed decoded.2 M scan final.registers final.lastService ∧
      cut.expectedWord = some
        (CoordinatorLocalArmChoice.storedDownFlatWord selected.view.payload i) ∧
      ReferenceDownReception.expectedDownFlatWord (some selected.view) i row t =
        some (CoordinatorLocalArmChoice.storedDownFlatWord selected.view.payload i) ∧
      decoded.2 = some (CoordinatorLocalArmChoice.storedDownFlatWord selected.view.payload i) ∧
      OrdinaryMessageCodec.parseDown (ReferencePrelaunchFollower.codecParams p rate.eta)
        (decoded.2.map (OrdinaryMessageCodec.wordEquivFlat
          (ReferencePrelaunchFollower.codecParams p rate.eta)).symm) = some M ∧
      cut.raw = decoded.2 ∧
      cut.filteredRaw = decoded.2 ∧
      cut.rawComparison = some true ∧
      cut.ordinaryParse = some M ∧
      cut.ordinaryAcceptance ∧
      cut.outcome = .accepted choice installed decoded.2 M scan final.registers
        final.lastService ∧
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
  let t : Fin p.T := r.input.time
  let row : CompletePublicTable.CompleteRow p := r.input.row
  let own : ReferencePrelaunchFollower.Observation p :=
    r.output.preparation.feedback.observations (PublicDiscreteDraws.followerPlayer p.two_le_m i)
  let M := selected.view.payload.downRecord i
  let decoded := ActiveFollowerDownAcceptance.currentDecodeStep p i row t own rate choice
  let scan := ActiveFollowerDownAcceptance.acceptedCutoffScan p rate M t
    (ActiveFollowerDownAcceptance.acceptedDownStartLE p rate M t choice ha) row
  let ell := scan.endpoint
  let cut := ReferenceDownReception.referenceDownCut p
    r.output.preparation.coordinator.downView i row t own rate choice
  rcases actual_prepare_local_domains rate r i choice memory hprepared with
    ⟨hchoiceDomain, hoperation⟩
  have hlocalBuffer : ActiveFollowerLifecycle.localBufferValid choice := hchoiceDomain.2.1
  have htests : ¬ SparseCalendarReplay.loggingTestsPass
      (ReferencePrelaunchFollower.loggingRound i row (r.input.state.activations i) t
        ((r.output.preparation.followers.followers i).arm, own)) := by
    intro hpass
    have hsource := (ActiveFollowerLogging.loggingTestsPass_iff_source_mask i row
      (r.input.state.activations i) t
      ((r.output.preparation.followers.followers i).arm, own)).mp hpass
    have hneq : PublicDiscreteDraws.downSlot ≠ PublicDiscreteDraws.dataSlot := by decide
    exact hneq (hbranch.1.symm.trans hsource.2.1)
  have hlogAt : ReferencePrelaunchFollower.logAt i row (r.input.state.activations i) t
      ((r.output.preparation.followers.followers i).arm, own) = [] :=
    ActiveFollowerLogging.logAt_eq_nil_of_not_tests i row
      (r.input.state.activations i) t
      ((r.output.preparation.followers.followers i).arm, own) htests
  have hlogging : ActiveFollowerLogging.checkedLogging i row
      (r.input.state.activations i) t
      ((r.output.preparation.followers.followers i).arm, own) choice = .ok choice := by
    simp [ActiveFollowerLogging.checkedLogging, hlocalBuffer,
      ActiveFollowerLogging.loggingUpdate, hlogAt]
  have hscanBounds := ActiveFollowerDownAcceptance.acceptedCutoff_interval_bounds
    p rate M t row choice ha
  have hrecovery := ReferenceCarriedDownRecoveryBudget.acceptedDown_checkedRecovery_with_prefix_budget
    rate M choice hlocalBuffer hcredit row t ha
  rcases hrecovery with
    ⟨final, hchecked, hregisters, hfinalDomain, hcarriedMass, htotalMass,
      hlastService, hserviceIdentity, hprefix⟩
  have hmassCurrent : (ell - 1) * D p ≤ (t.val + 1) * D p := by
    have hell : ell ≤ t.val + 2 := by
      simpa only [ell, scan] using hscanBounds.2.1
    have hrounds : ell - 1 ≤ t.val + 1 := by omega
    exact Nat.mul_le_mul_right (D p) hrounds
  have hview : r.output.preparation.coordinator.downView = some selected.view := by
    have hs : (ReferenceActivePhysicalStep.prepare r.input).coordinator.selection =
        some selected := by
      rw [r.output_eq] at hselection
      change (ReferenceActivePhysicalStep.prepare r.input).coordinator.selection =
        some selected at hselection
      exact hselection
    rw [r.output_eq]
    change (ReferenceActivePhysicalStep.prepare r.input).coordinator.downView = some selected.view
    change ((ReferenceActivePhysicalStep.prepare r.input).coordinator.selection.map
      ReferenceActivePhysicalStep.Selection.view) = some selected.view
    rw [hs]
    rfl
  have hselected : ActiveFollowerDownAcceptance.downSelected p i row t :=
    ⟨hbranch.1, hbranch.2.1⟩
  have hmatchesExpected : decoded.2 =
      ReferenceDownReception.expectedDownFlatWord (some selected.view) i row t := by
    rw [selected.expected_down_word i hbranch]
    exact hraw
  have hparse : ReferenceDownReception.ordinaryParse p rate decoded.2 = some M := by
    rw [hraw]
    change OrdinaryMessageCodec.parseDown
      (ReferencePrelaunchFollower.codecParams p rate.eta)
      (some ((OrdinaryMessageCodec.wordEquivFlat
        (ReferencePrelaunchFollower.codecParams p rate.eta)).symm
          (OrdinaryMessageCodec.wordEquivFlat
            (ReferencePrelaunchFollower.codecParams p rate.eta)
              (selected.view.payload.downWord i)))) = some M
    simp only [Equiv.symm_apply_apply]
    exact selected.view.payload.parseDown_downWord i
  have hparseCurrent : ReferenceDownReception.ordinaryParse p rate
      (ActiveFollowerDownAcceptance.currentDecodeStep p i row t own rate choice).2 =
        some M := by
    simpa [decoded] using hparse
  have hparsed : ActiveFollowerDownAcceptance.parsedCurrentOutput p i row t own rate choice =
      some M := by
    simpa [ActiveFollowerDownAcceptance.parsedCurrentOutput,
      ReferenceDownReception.ordinaryParse, decoded, row, t, own] using hparse
  let installed : ReferencePrelaunchFollower.State p rate.eta := {
    choice with
    lastDown := some M
    S := final.registers.1
    delta := final.lastService
    backlog := final.registers.2
    downBatch := decoded.1
    buffer := []
    status := if ell = t.val + 2 then .pending else .unoccupied }
  let nextMemory : ActiveFollowerLifecycle.LocalMemory p :=
    if ell = t.val + 2 then
      { lastProposalRead := some {
        timestamp := t
        bit := FollowerCutoffScan.completeRowProposalBit p rate.eta.val row t } }
    else memory
  have hcutDef : cut = ReferenceDownReception.referenceDownCut p (some selected.view)
      i row t own rate choice := by
    simp [cut, hview]
  have hcutExpected : cut.expectedWord =
      some (CoordinatorLocalArmChoice.storedDownFlatWord selected.view.payload i) := by
    rw [hcutDef]
    simp only [ReferenceDownReception.referenceDownCut, decoded, dite_eq_left hselected,
      dite_eq_left hunoccupied, dite_eq_left hoperation.1, dite_eq_left hoperation.2.1,
      dite_eq_left hoperation.2.2, dite_eq_left hmatchesExpected]
    simpa [row, t] using selected.expected_down_word i hbranch
  have hcutRaw : cut.raw = decoded.2 := by
    rw [hcutDef]
    simp [ReferenceDownReception.referenceDownCut, hselected, hunoccupied,
      hoperation.1, hoperation.2.1, hoperation.2.2, hmatchesExpected, decoded]
  have hcutFiltered : cut.filteredRaw = decoded.2 := by
    rw [hcutDef]
    simp [ReferenceDownReception.referenceDownCut, hselected, hunoccupied,
      hoperation.1, hoperation.2.1, hoperation.2.2, hmatchesExpected, decoded]
  have hcutComparison : cut.rawComparison = some true := by
    rw [hcutDef]
    simp [ReferenceDownReception.referenceDownCut, hselected, hunoccupied,
      hoperation.1, hoperation.2.1, hoperation.2.2, hmatchesExpected, decoded]
  have hcutParse : cut.ordinaryParse = some M := by
    rw [hcutDef]
    simp only [ReferenceDownReception.referenceDownCut, decoded, dite_eq_left hselected,
      dite_eq_left hunoccupied, dite_eq_left hoperation.1, dite_eq_left hoperation.2.1,
      dite_eq_left hoperation.2.2, dite_eq_left hmatchesExpected]
    exact hparse
  have hcutAcceptance : cut.ordinaryAcceptance := by
    rw [hcutDef]
    simp only [ReferenceDownReception.referenceDownCut, decoded, dite_eq_left hselected,
      dite_eq_left hunoccupied, dite_eq_left hoperation.1, dite_eq_left hoperation.2.1,
      dite_eq_left hoperation.2.2, dite_eq_left hmatchesExpected]
    rw [hparseCurrent]
    simp only [ReferenceDownReception.ordinaryLocalAcceptanceTest]
    simpa [t] using ha
  have hcutNoMismatch : ¬ ReferenceDownReception.rawMismatch cut := by
    simp [ReferenceDownReception.rawMismatch, hcutComparison]
  have hdownTransition : ActiveFollowerDownAcceptance.downTransition p i row t own rate choice =
      .accepted choice installed decoded.2 M scan final.registers final.lastService := by
    simpa only [decoded, scan] using
      (ActiveFollowerDownAcceptance.downTransition_accepted_equation p i row t own rate choice
        hselected hunoccupied hoperation.1 hoperation.2.1 hoperation.2.2 M hparsed ha
        final hchecked)
  have hcutOutcome : cut.outcome =
      .accepted choice installed decoded.2 M scan final.registers final.lastService := by
    have hnomismatch := hcutNoMismatch
    rw [hcutDef] at hnomismatch
    calc
      cut.outcome = ActiveFollowerDownAcceptance.downTransition p i row t own rate choice := by
        rw [hcutDef]
        exact ReferenceDownReception.referenceDownCut_outcome_eq_downTransition_of_no_raw_mismatch
          (some selected.view) i row t own rate choice hnomismatch
      _ = .accepted choice installed decoded.2 M scan final.registers final.lastService :=
        hdownTransition
  have hcutOutcomeActual :
      (ReferenceDownReception.referenceDownCut p
        r.output.preparation.coordinator.downView i row t own rate choice).outcome =
          .accepted choice installed decoded.2 M scan final.registers final.lastService := by
    rw [hview]
    rw [← hcutDef]
    exact hcutOutcome
  have hcutOutcomeSelected :
      (ReferenceDownReception.referenceDownCut p (some selected.view)
        i row t own rate choice).outcome =
          .accepted choice installed decoded.2 M scan final.registers final.lastService := by
    rw [← hcutDef]
    exact hcutOutcome
  have hdecodedBatch := ReferenceFollowerDecoderChronology.currentDecodeStep_batch_spec
    i row t own choice hoperation.2.1
  have hbatchWF : ReferenceFollowerDecoderChronology.downBatchWellFormed decoded.1 := by
    simpa only [decoded] using hdecodedBatch.1
  have hpending := currentDecodeStep_pending_empty_of_some rate i row t own choice
    (CoordinatorLocalArmChoice.storedDownFlatWord selected.view.payload i)
    hoperation.2.1 hraw
  have hinstalledDomain : ActiveFollowerLifecycle.localStateDomainValid installed := by
    change final.registers.1 ≤ p.T * D p ∧ final.lastService ≤ D p ∧
      final.registers.2 ≤ p.T * D p at hfinalDomain
    change decoded.1.pending.length < AffineBatchDecoder.quota p ∧
      ∀ completed ∈ decoded.1.completed, completed.length = AffineBatchDecoder.quota p
      at hbatchWF
    unfold ActiveFollowerLifecycle.localStateDomainValid
    refine ⟨?_, ?_, ?_⟩
    · change installed.S ≤ p.T * D p ∧ installed.delta ≤ D p ∧
        installed.backlog ≤ p.T * D p
      simpa [installed] using hfinalDomain
    · simp [ActiveFollowerLifecycle.localBufferValid, installed]
    · change ActiveFollowerDownAcceptance.decoderInputDomain p installed.downBatch
      simpa only [ActiveFollowerDownAcceptance.decoderInputDomain,
        ActiveFollowerLifecycle.downDecoderStateValid, installed] using hbatchWF
  have hinitializationFrame : installed.initializationFailure = choice.initializationFailure := by
    rfl
  have hrelease := ActiveFollowerLifecycle.releaseAfterService_unoccupied rate.eta i t
    (ActiveFollowerLifecycle.publicRowOfCompleteRow row t) own choice installed hunoccupied
  have hfinish : ActiveFollowerLifecycle.finishRound rate.eta t row installed memory =
      .ok (installed, nextMemory) := by
    by_cases hend : ell = t.val + 2
    · have hstatus : installed.status ≠ .unoccupied := by
        simp [installed, hend]
      have hrecord : installed.lastDown = some M := by rfl
      have htime : M.val.sigma ≤ t.val + 1 := ha.2
      simpa [nextMemory, hend] using
        (ActiveFollowerLifecycle.finishRound_occupied_read rate.eta t row installed memory
          hstatus hinstalledDomain M hrecord htime)
    · have hstatus : installed.status = .unoccupied := by
        simp [installed, hend]
      simpa [nextMemory, hend] using
        (ActiveFollowerLifecycle.finishRound_unoccupied rate.eta t row installed memory
          hinstalledDomain hstatus)
  have hreleaseFinish : DeclaredFollowerLocalRound.releaseAndFinish rate i row t own
      choice memory installed = .ok (installed, nextMemory) := by
    rw [DeclaredFollowerLocalRound.releaseAndFinish_final_equation rate i row t own choice
      memory installed installed hrelease]
    rw [hfinish]
  have hpreparedStep :
      ((ReferenceActivePhysicalStep.prepare r.input).followers.followers i).configuration =
        .ordinary choice memory := by
    have h := hprepared
    rw [r.output_eq] at h
    change ((ReferenceActivePhysicalStep.prepare r.input).followers.followers i).configuration =
      .ordinary choice memory at h
    exact h
  have hloggingStep : ActiveFollowerLogging.checkedLogging i row
      (r.input.state.activations i) t
      (((ReferenceActivePhysicalStep.prepare r.input).followers.followers i).arm, own)
      choice = .ok choice := by
    have h := hlogging
    rw [r.output_eq] at h
    change ActiveFollowerLogging.checkedLogging i row
      (r.input.state.activations i) t
      (((ReferenceActivePhysicalStep.prepare r.input).followers.followers i).arm, own)
      choice = .ok choice at h
    exact h
  have hviewStep : (ReferenceActivePhysicalStep.prepare r.input).coordinator.downView =
      some selected.view := by
    have h := hview
    rw [r.output_eq] at h
    exact h
  have hownStep : (ReferenceActivePhysicalStep.prepare r.input).feedback.observations
      (PublicDiscreteDraws.followerPlayer p.two_le_m i) = own := by
    dsimp [own]
    rw [r.output_eq]
    rfl
  have hloggedResultStep :
      (ReferenceActivePhysicalStep.recordFollower
        (ReferenceActivePhysicalStep.prepare r.input).coordinator.downView i row
        (r.input.state.activations i) t (r.input.active i)
        ((ReferenceActivePhysicalStep.prepare r.input).followers.followers i).arm own choice).result =
          .ok installed := by
    simp [ReferenceActivePhysicalStep.recordFollower, hunoccupied, hloggingStep,
      hviewStep, hcutOutcomeSelected, DeclaredFollowerLocalRound.consumeDownResult]
  have hloggedResultInput :
      (ReferenceActivePhysicalStep.recordFollower (some selected.view) i row
        (r.input.state.activations i) t (r.input.active i)
        ((ReferenceActivePhysicalStep.prepare r.input).followers.followers i).arm own choice).result =
          .ok installed := by
    simpa [hviewStep] using hloggedResultStep
  have hloggedResult :
      (ReferenceActivePhysicalStep.recordFollower
        r.output.preparation.coordinator.downView i row
        (r.input.state.activations i) t (r.input.active i)
        (r.output.preparation.followers.followers i).arm own choice).result =
          .ok installed := by
    rw [r.output_eq]
    change (ReferenceActivePhysicalStep.recordFollower
      (ReferenceActivePhysicalStep.prepare r.input).coordinator.downView i row
      (r.input.state.activations i) t (r.input.active i)
      ((ReferenceActivePhysicalStep.prepare r.input).followers.followers i).arm own choice).result =
        .ok installed
    exact hloggedResultStep
  have halignment := (ReferenceActivePhysicalStep.prepare r.input).follower_alignment i
  rcases halignment with ⟨hrow, hfollower, htime, hactivation⟩
  have hrecordPrepared :
      (ReferenceActivePhysicalStep.recordFollower
        (ReferenceActivePhysicalStep.prepare r.input).coordinator.downView
        ((ReferenceActivePhysicalStep.prepare r.input).followers.followers i).follower
        ((ReferenceActivePhysicalStep.prepare r.input).followers.followers i).row
        ((ReferenceActivePhysicalStep.prepare r.input).followers.followers i).activation
        ((ReferenceActivePhysicalStep.prepare r.input).followers.followers i).time
        ((ReferenceActivePhysicalStep.prepare r.input).followers.followers i).active
        ((ReferenceActivePhysicalStep.prepare r.input).followers.followers i).arm own choice).result =
          .ok installed := by
    simpa only [hfollower, hrow, hactivation, htime] using hloggedResultStep
  have hloggingPrepared : ActiveFollowerLogging.checkedLogging
      ((ReferenceActivePhysicalStep.prepare r.input).followers.followers i).follower
      ((ReferenceActivePhysicalStep.prepare r.input).followers.followers i).row
      ((ReferenceActivePhysicalStep.prepare r.input).followers.followers i).activation
      ((ReferenceActivePhysicalStep.prepare r.input).followers.followers i).time
      (((ReferenceActivePhysicalStep.prepare r.input).followers.followers i).arm, own) choice =
        .ok choice := by
    simpa only [hfollower, hrow, hactivation, htime] using hloggingStep
  have hreleaseFinishPrepared :
      DeclaredFollowerLocalRound.releaseAndFinish rate
        ((ReferenceActivePhysicalStep.prepare r.input).followers.followers i).follower
        ((ReferenceActivePhysicalStep.prepare r.input).followers.followers i).row
        ((ReferenceActivePhysicalStep.prepare r.input).followers.followers i).time own choice memory installed =
          .ok (installed, nextMemory) := by
    simpa only [hfollower, hrow, htime] using hreleaseFinish
  have hfollowers : r.output.followers i = {
      configuration := .ordinary installed nextMemory
      failure := none
      downInput := some choice
      down := some cut } := by
    rw [r.output_eq]
    change (ReferenceActivePhysicalStep.prepare r.input).observeFollower i = _
    have hrecordLogged := ReferenceActivePhysicalStep.recordFollower_logged
      (rate := rate) (some selected.view) i row (r.input.state.activations i) t
      (r.input.active i)
      ((ReferenceActivePhysicalStep.prepare r.input).followers.followers i).arm
      own choice choice hunoccupied hloggingStep
    simp [ReferenceActivePhysicalStep.PreparedRound.observeFollower,
      ReferenceActivePhysicalStep.finishFollower, hpreparedStep, hloggedResultInput,
      hreleaseFinish, hrecordLogged.1, hrecordLogged.2, hviewStep, hcutDef,
      hfollower, hrow, hactivation, htime, hownStep, row, t]
  have hnext : r.output.next.followers i = .ordinary installed nextMemory := by
    rw [r.output_eq]
    have hfollowersStep := hfollowers
    rw [r.output_eq] at hfollowersStep
    calc
      (ReferenceActivePhysicalStep.step r.input).next.followers i =
          ((ReferenceActivePhysicalStep.step r.input).followers i).configuration :=
        (ReferenceActivePhysicalStep.step_next_fields r.input).2.2.2 i
      _ = .ordinary installed nextMemory := by rw [hfollowersStep]
  refine ⟨final, hchoiceDomain, hoperation, hlogging, hchecked, hregisters,
    hfinalDomain, hcarriedMass, htotalMass, hmassCurrent, hlastService,
    hscanBounds.1, hscanBounds.2.1, hscanBounds.2.2.1,
    hserviceIdentity, hprefix, hdownTransition, hcutExpected,
    selected.expected_down_word i hbranch, hraw, ?_, hcutRaw, hcutFiltered,
    hcutComparison, hcutParse, hcutAcceptance, hcutOutcome, hloggedResult,
    hinstalledDomain, hinitializationFrame, hbatchWF, hpending, hrelease,
    hfinish, hreleaseFinish, hfollowers, hnext⟩
  simpa [ReferenceDownReception.ordinaryParse, decoded, row, t, own] using hparse

/-- The same connected branch theorem on the literal records of the canonical
complete suffix run. The branch telescope remains local and is not promoted to
a law about every source birth or every round. -/
def completeSuffix_get_actual_new_current_down_forward
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source
      rewards C_star C_h).length)
    (selected : ReferenceActivePhysicalStep.Selection
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards
        C_star C_h).get k).input)
    (hselection : ((ReferenceCompletePhysicalHistory.completeSuffixRecords rate source
      rewards C_star C_h).get k).output.preparation.coordinator.selection = some selected)
    (i : Fin (p.m - 1))
    (choice : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hprepared : (((ReferenceCompletePhysicalHistory.completeSuffixRecords rate source
      rewards C_star C_h).get k).output.preparation.followers.followers i).configuration =
        .ordinary choice memory)
    (hunoccupied : choice.status = .unoccupied)
    (hbranch : ReferenceDownReception.selectedDownSenderBranch selected.view i
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards
        C_star C_h).get k).input.row
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards
        C_star C_h).get k).input.time)
    (ha : OrdinaryMessageCodec.acceptDown
      (ReferencePrelaunchFollower.codecParams p rate.eta)
      (ReferencePrelaunchFollower.acceptedStart choice)
      (((ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards
        C_star C_h).get k).input.time.val + 1)
      (selected.view.payload.downRecord i))
    (hcredit : (selected.view.payload.downRecord i).val.q ≤
      ((selected.view.payload.downRecord i).val.sigma - 1) * ConstructorDimensions.D p)
    (hraw : (ActiveFollowerDownAcceptance.currentDecodeStep p i
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards
        C_star C_h).get k).input.row
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards
        C_star C_h).get k).input.time
      (((ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards
        C_star C_h).get k).output.preparation.feedback.observations
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)) rate choice).2 =
          some (CoordinatorLocalArmChoice.storedDownFlatWord selected.view.payload i)) :=
  actual_new_current_down_forward rate
    ((ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h).get k)
    selected hselection i choice memory hprepared hunoccupied hbranch ha hcredit hraw

end Bandits.Support.ReferenceCarriedDownForwardTransition

end
