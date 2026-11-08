/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceContinuingLiveSlicePreparation
public import Bandits.Support.ReferenceFollowerBufferProvenance

import Lean.Elab.Tactic.Omega

/-!
# Actual continuing DATA candidate logging

Sources: `sources/zip4/manuscript/05_binary_transport.tex:354-396` and
`sources/zip4/manuscript/06_interruptions.tex:195-233`.

The input below is the actual next input of the original finite physical run.
For each replacement of its complete current selected control whose slot is
DATA, the imported preparation theorem keeps the same ordinary follower
configurations. The imported buffer-provenance results establish prefix
chronology once, before the current control varies, and the actual checked
logger then produces its pre-DOWN diagnostic. This module proves no later
recovery outcome, final-buffer retention, recording law, or regret statement.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ContinuousControlSlice

namespace Bandits.Support.ReferenceContinuingDataCandidateLogging

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput

variable {p : Parameters} {rate : RateInput p}

/-- The actual next prefix input of `ReferenceActivePhysicalHorizon.run`.
Its state is that run's computed prefix endpoint; its rows, selected index,
and complete reward table are the original inputs. -/
def candidateInput (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + (count + 1) ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start) :
    ReferenceActivePhysicalStep.RoundInput p rate :=
  ReferenceActivePhysicalHorizon.roundInputAt initial rows selected rewards start hmode
    (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count
      (by omega) hmode)
    ⟨start + count, by omega, by omega⟩

/-- The literal physical round record at the current complete-control
replacement. -/
def candidateRecord (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + (count + 1) ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (u : ContinuousLearningRows.TimeControl p) :
    ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) := by
  let input := ReferenceContinuingLiveSlicePreparation.inputAtControl
    (candidateInput initial rows selected rewards start count hspan hmode) u
  exact ⟨input, ReferenceActivePhysicalStep.step input, rfl⟩

/-- The actual physical logger emission is exactly the existing `logAt`
singleton when its source/mask/DATA tests pass and empty otherwise. The test
predicate contains no positive-feedback or thinning-pass condition. -/
private theorem actual_logEmission_eq_tests
    (i : Fin (p.m - 1))
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (choice : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hprepared :
      (record.output.preparation.followers.followers i).configuration =
        .ordinary choice memory)
    (hunoccupied : choice.status = .unoccupied) :
    (SparseCalendarReplay.loggingTestsPass
      (ReferencePrelaunchFollower.loggingRound i record.input.row
        (record.input.state.activations i) record.input.time
        (record.output.ownEntries (PublicDiscreteDraws.followerPlayer p.two_le_m i))) →
      ReferenceFollowerBufferProvenance.logEmission i record =
        [SparseCalendarReplay.recordAt (record.input.time.val + 1)
          (ReferencePrelaunchFollower.loggingRound i record.input.row
            (record.input.state.activations i) record.input.time
            (record.output.ownEntries (PublicDiscreteDraws.followerPlayer p.two_le_m i)))]) ∧
    (¬ SparseCalendarReplay.loggingTestsPass
      (ReferencePrelaunchFollower.loggingRound i record.input.row
        (record.input.state.activations i) record.input.time
        (record.output.ownEntries (PublicDiscreteDraws.followerPlayer p.two_le_m i))) →
      ReferenceFollowerBufferProvenance.logEmission i record = []) := by
  have hemits : ReferenceFollowerBufferProvenance.logEmission i record =
      ReferencePrelaunchFollower.logAt i record.input.row
        (record.input.state.activations i) record.input.time
        (record.output.ownEntries (PublicDiscreteDraws.followerPlayer p.two_le_m i)) := by
    simp [ReferenceFollowerBufferProvenance.logEmission, hprepared, hunoccupied]
  constructor
  · intro htests
    rw [hemits]
    exact ActiveFollowerLogging.logAt_eq_singleton_of_tests i record.input.row
      (record.input.state.activations i) record.input.time
      (record.output.ownEntries (PublicDiscreteDraws.followerPlayer p.two_le_m i)) htests
  · intro htests
    rw [hemits]
    exact ActiveFollowerLogging.logAt_eq_nil_of_not_tests i record.input.row
      (record.input.state.activations i) record.input.time
      (record.output.ownEntries (PublicDiscreteDraws.followerPlayer p.two_le_m i)) htests

/-- The exact result contract for the continuing DATA candidate producer. -/
def candidateLoggingConclusion
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + (count + 1) ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (i : Fin (p.m - 1))
    (seed : ReferencePrelaunchFollower.State p rate.eta)
    (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta) : Prop :=
    ActiveFollowerLifecycle.localBufferValid (states i) ∧
      (states i).buffer = ReferenceFollowerBufferProvenance.bufferFold i seed.buffer
        (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count
          (by omega) hmode).records ∧
      (states i).buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) ∧
      (∀ saved ∈ (states i).buffer,
        saved.calendarRound < (candidateInput initial rows selected rewards start count
          hspan hmode).time.val + 1) ∧
      ∀ u : ContinuousLearningRows.TimeControl p,
        PublicDiscreteDraws.slotDraw u.1 = PublicDiscreteDraws.dataSlot →
        ∃ logged,
          ActiveFollowerLogging.checkedLogging i
            (candidateRecord initial rows selected rewards start count hspan hmode u).input.row
            ((candidateRecord initial rows selected rewards start count hspan hmode u).input.state.activations i)
            (candidateRecord initial rows selected rewards start count hspan hmode u).input.time
            ((candidateRecord initial rows selected rewards start count hspan hmode u).output.ownEntries
              (PublicDiscreteDraws.followerPlayer p.two_le_m i)) (states i) = .ok logged ∧
          ((candidateRecord initial rows selected rewards start count hspan hmode u).output.followers i).downInput =
            some logged ∧
          logged.buffer = (states i).buffer ++ ReferenceFollowerBufferProvenance.logEmission i
            (candidateRecord initial rows selected rewards start count hspan hmode u) ∧
          logged.buffer = ReferenceFollowerBufferProvenance.bufferFold i seed.buffer
            (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count
              (by omega) hmode).records ++ ReferenceFollowerBufferProvenance.logEmission i
                (candidateRecord initial rows selected rewards start count hspan hmode u) ∧
          ActiveFollowerLifecycle.localBufferValid logged ∧
          (SparseCalendarReplay.loggingTestsPass
              (ReferencePrelaunchFollower.loggingRound i
                (candidateRecord initial rows selected rewards start count hspan hmode u).input.row
                ((candidateRecord initial rows selected rewards start count hspan hmode u).input.state.activations i)
                (candidateRecord initial rows selected rewards start count hspan hmode u).input.time
                ((candidateRecord initial rows selected rewards start count hspan hmode u).output.ownEntries
                  (PublicDiscreteDraws.followerPlayer p.two_le_m i))) →
            ReferenceFollowerBufferProvenance.logEmission i
              (candidateRecord initial rows selected rewards start count hspan hmode u) =
              [SparseCalendarReplay.recordAt
                ((candidateRecord initial rows selected rewards start count hspan hmode u).input.time.val + 1)
                (ReferencePrelaunchFollower.loggingRound i
                  (candidateRecord initial rows selected rewards start count hspan hmode u).input.row
                  ((candidateRecord initial rows selected rewards start count hspan hmode u).input.state.activations i)
                  (candidateRecord initial rows selected rewards start count hspan hmode u).input.time
                  ((candidateRecord initial rows selected rewards start count hspan hmode u).output.ownEntries
                    (PublicDiscreteDraws.followerPlayer p.two_le_m i)))]) ∧
          (¬ SparseCalendarReplay.loggingTestsPass
              (ReferencePrelaunchFollower.loggingRound i
                (candidateRecord initial rows selected rewards start count hspan hmode u).input.row
                ((candidateRecord initial rows selected rewards start count hspan hmode u).input.state.activations i)
                (candidateRecord initial rows selected rewards start count hspan hmode u).input.time
                ((candidateRecord initial rows selected rewards start count hspan hmode u).output.ownEntries
                  (PublicDiscreteDraws.followerPlayer p.two_le_m i))) →
            ReferenceFollowerBufferProvenance.logEmission i
              (candidateRecord initial rows selected rewards start count hspan hmode u) = []) ∧
          (∀ saved ∈ ReferenceFollowerBufferProvenance.logEmission i
              (candidateRecord initial rows selected rewards start count hspan hmode u),
            ∃ own,
              saved.calendarRound = start + count + 1 ∧ saved.pilot = own.1 ∧
              saved.observation = own.2.val ∧
              saved.thinScalar = u.1 Label.thin ∧
              own = (candidateRecord initial rows selected rewards start count hspan hmode u).output.ownEntries
                (PublicDiscreteDraws.followerPlayer p.two_le_m i)) ∧
          (∀ reason : ActiveFollowerLogging.LoggingFailure,
            ActiveFollowerLogging.checkedLogging i
              (candidateRecord initial rows selected rewards start count hspan hmode u).input.row
              ((candidateRecord initial rows selected rewards start count hspan hmode u).input.state.activations i)
              (candidateRecord initial rows selected rewards start count hspan hmode u).input.time
              ((candidateRecord initial rows selected rewards start count hspan hmode u).output.ownEntries
                (PublicDiscreteDraws.followerPlayer p.two_le_m i)) (states i) ≠ .error reason)

/-- Prefix-derived chronological safety and successful actual logging on
every DATA replacement of the current selected control. `ho` is the actual
ordinary PREPARE result at the next prefix input. The focal state is required
to be unoccupied for the candidate logger. The saved thin coordinate and all
other continuous coordinates remain those of the complete replacement `u`.
-/
theorem continuing_data_candidate_logging
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + (count + 1) ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (i : Fin (p.m - 1))
    (seed : ReferencePrelaunchFollower.State p rate.eta)
    (seedMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hseed : initial.followers i = .ordinary seed seedMemory)
    (hseedValid : ActiveFollowerLifecycle.localBufferValid seed)
    (hseedPairwise : seed.buffer.Pairwise
      (fun a b => a.calendarRound < b.calendarRound))
    (hseedTime : ∀ saved ∈ seed.buffer, saved.calendarRound ≤ start)
    (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
    (memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p)
    (ho : ∀ k,
      ((ReferenceActivePhysicalStep.prepare
        (candidateInput initial rows selected rewards start count hspan hmode)).followers.followers k).configuration =
          .ordinary (states k) (memories k))
    (hunoccupied : (states i).status = .unoccupied) :
    candidateLoggingConclusion initial rows selected rewards start count hspan hmode i seed states := by
  have hprefix : start + count ≤ p.T := by omega
  let prior := ReferenceActivePhysicalHorizon.run initial rows selected rewards start count hprefix hmode
  let x := candidateInput initial rows selected rewards start count hspan hmode
  let sourceRecord : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) :=
    ⟨x, ReferenceActivePhysicalStep.step x, rfl⟩
  have hprepared :
      (sourceRecord.output.preparation.followers.followers i).configuration =
        .ordinary (states i) (memories i) := by
    simpa [sourceRecord, ReferenceActivePhysicalStep.step] using ho i
  rcases ReferenceFollowerBufferProvenance.prepared_choice_buffer_eq_input i
      sourceRecord (states i) (memories i) hprepared with
    ⟨before, beforeMemory, hinput, hbuffer⟩
  have hnext : prior.finalState.followers i = .ordinary before beforeMemory := by
    simpa [prior, sourceRecord, x, candidateInput,
      ReferenceActivePhysicalHorizon.roundInputAt] using hinput
  have hchron := ReferenceFollowerBufferProvenance.run_buffer_chronological i
    initial rows selected rewards start count hprefix hmode seed seedMemory hseed
    hseedValid hseedPairwise hseedTime before beforeMemory hnext
  have hvalidStates : ActiveFollowerLifecycle.localBufferValid (states i) := by
    simpa only [ActiveFollowerLifecycle.localBufferValid, hbuffer] using hchron.1
  have hpairStates : (states i).buffer.Pairwise
      (fun a b => a.calendarRound < b.calendarRound) := by
    rw [hbuffer]
    exact hchron.2.1
  have htimeStates : ∀ saved ∈ (states i).buffer,
      saved.calendarRound < (x.time.val + 1) := by
    intro saved hs
    rw [hbuffer] at hs
    simpa [x, candidateInput, ReferenceActivePhysicalHorizon.roundInputAt] using
      hchron.2.2 saved hs
  have hprovenance := ReferenceFollowerBufferProvenance.run_buffer_provenance i
    initial rows selected rewards start count hprefix hmode seed seedMemory hseed
    hseedValid hseedPairwise hseedTime before beforeMemory hnext
  have hbufferFold : (states i).buffer =
      ReferenceFollowerBufferProvenance.bufferFold i seed.buffer prior.records := by
    exact hbuffer.trans (by simpa [prior] using hprovenance)
  refine ⟨hvalidStates, hbufferFold, hpairStates, ?_, ?_⟩
  · intro saved hs
    simpa [x, candidateInput, ReferenceActivePhysicalHorizon.roundInputAt] using
      htimeStates saved hs
  · intro u hdata
    let xu := ReferenceContinuingLiveSlicePreparation.inputAtControl x u
    let ru := candidateRecord initial rows selected rewards start count hspan hmode u
    have hpreparedControl :=
      ReferenceContinuingLiveSlicePreparation.data_preparation_at_control
        x states memories ho u hdata i
    have hpreparedRu :
        (ru.output.preparation.followers.followers i).configuration =
          .ordinary (states i) (memories i) := by
      simpa [ru, candidateRecord, ReferenceActivePhysicalStep.step] using hpreparedControl
    have hbefore : ∀ saved ∈ (states i).buffer,
        saved.calendarRound < ru.input.time.val + 1 := by
      intro saved hs
      simpa [ru, candidateRecord, xu, x, candidateInput,
        ReferenceActivePhysicalHorizon.roundInputAt] using htimeStates saved hs
    rcases ReferenceFollowerBufferProvenance.actualPreparedLogging_success i ru
        (states i) (memories i) hpreparedRu hvalidStates hbefore hunoccupied with
      ⟨loggedByCheck, hcheck, _, _, _⟩
    have halign := ru.output.preparation.follower_alignment i
    have hown := ReferenceFollowerBufferProvenance.round_ownEntry_eq_prepared i ru
    have hloggingPrepared :
        ActiveFollowerLogging.checkedLogging i
          (ru.output.preparation.followers.followers i).row
          (ru.output.preparation.followers.followers i).activation
          (ru.output.preparation.followers.followers i).time
          ((ru.output.preparation.followers.followers i).arm,
            ru.output.preparation.feedback.observations
              (PublicDiscreteDraws.followerPlayer p.two_le_m i)) (states i) =
            .ok loggedByCheck := by
      rw [halign.1, halign.2.2.2, halign.2.2.1, ← hown]
      exact hcheck
    have hrecordLogged := ReferenceActivePhysicalStep.recordFollower_logged
      ru.output.preparation.coordinator.downView i
      (ru.output.preparation.followers.followers i).row
      (ru.output.preparation.followers.followers i).activation
      (ru.output.preparation.followers.followers i).time
      (ru.output.preparation.followers.followers i).active
      (ru.output.preparation.followers.followers i).arm
      (ru.output.preparation.feedback.observations
        (PublicDiscreteDraws.followerPlayer p.two_le_m i))
      (states i) loggedByCheck hunoccupied hloggingPrepared
    have hdownCheck : (ru.output.followers i).downInput = some loggedByCheck := by
      rw [ReferenceFollowerBufferProvenance.roundRecord_follower_eq_finishFollower i ru]
      cases hstage : (ReferenceActivePhysicalStep.recordFollower
          ru.output.preparation.coordinator.downView i
          (ru.output.preparation.followers.followers i).row
          (ru.output.preparation.followers.followers i).activation
          (ru.output.preparation.followers.followers i).time
          (ru.output.preparation.followers.followers i).active
          (ru.output.preparation.followers.followers i).arm
          (ru.output.preparation.feedback.observations
            (PublicDiscreteDraws.followerPlayer p.two_le_m i)) (states i)).result with
      | error failure =>
          simp [ReferenceActivePhysicalStep.finishFollower, hpreparedRu,
            halign.2.1, hrecordLogged.1, hstage]
      | ok postRecord =>
          cases hfinish : DeclaredFollowerLocalRound.releaseAndFinish rate i
              (ru.output.preparation.followers.followers i).row
              (ru.output.preparation.followers.followers i).time
              (ru.output.preparation.feedback.observations
                (PublicDiscreteDraws.followerPlayer p.two_le_m i))
              (states i) (memories i) postRecord with
          | error failure =>
              simp [ReferenceActivePhysicalStep.finishFollower, hpreparedRu,
                halign.2.1, hrecordLogged.1, hstage, hfinish]
          | ok result =>
              simp [ReferenceActivePhysicalStep.finishFollower, hpreparedRu,
                halign.2.1, hrecordLogged.1, hstage, hfinish]
    rcases ReferenceFollowerBufferProvenance.actualPrepared_downInput_buffer i ru
        (states i) (memories i) hpreparedRu hvalidStates hbefore hunoccupied with
      ⟨logged, hdown, hloggedBuffer, hloggedValid⟩
    have heq : loggedByCheck = logged := Option.some.inj (hdownCheck.symm.trans hdown)
    subst logged
    have hloggingEq := actual_logEmission_eq_tests i ru (states i) (memories i)
      hpreparedRu hunoccupied
    have hfields : ∀ saved ∈ ReferenceFollowerBufferProvenance.logEmission i ru,
        ∃ own,
          saved.calendarRound = start + count + 1 ∧ saved.pilot = own.1 ∧
          saved.observation = own.2.val ∧ saved.thinScalar = u.1 Label.thin ∧
          own = ru.output.ownEntries (PublicDiscreteDraws.followerPlayer p.two_le_m i) := by
      intro saved hs
      rcases ReferenceFollowerBufferProvenance.logEmission_member_fields i ru saved hs with
        ⟨own, hcalendar, hpilot, hobs, hthin, hown⟩
      refine ⟨own, ?_⟩
      refine ⟨?_, ?_⟩
      · simpa [ru, candidateRecord, xu, x, candidateInput,
          ReferenceActivePhysicalHorizon.roundInputAt] using hcalendar
      · refine ⟨hpilot, ?_⟩
        refine ⟨hobs, ?_⟩
        refine ⟨?_, hown⟩
        simpa [ru, candidateRecord, xu,
          ReferenceContinuingLiveSlicePreparation.inputAtControl_row,
          ReferenceContinuingLiveSlicePreparation.inputAtControl_time,
          ReferenceContinuingLiveSlicePreparation.rowAtControl_time] using hthin
    refine ⟨loggedByCheck, ?_⟩
    refine ⟨hcheck, ?_⟩
    refine ⟨hdownCheck, ?_⟩
    refine ⟨hloggedBuffer, ?_⟩
    refine ⟨?_, ?_⟩
    · simpa [hbufferFold, prior, ru, candidateRecord, candidateInput] using hloggedBuffer
    · refine ⟨hloggedValid, ?_⟩
      refine ⟨hloggingEq.1, ?_⟩
      refine ⟨hloggingEq.2, ?_⟩
      refine ⟨hfields, ?_⟩
      intro reason
      rw [hcheck]
      simp

/-! ### The exact actual-launch seed specialization -/

/-- This alias is definitionally the existing actual launched-boundary state;
it does not introduce a second physical state carrier. -/
def actualLaunchState
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (rate : RateInput p) (C_star C_h : ℝ)
    (b : ReferenceInitializationRun.Boundary p)
    (h : b.completed < BootstrapDimensions.n_boot p)
    (actual : ActualInitializationRun.BlockCarry p rate
      (ReferenceInitializationRun.nextBlock b h))
    (past : List (ActualInitializationRun.PhysicalRoundRecord p rate source rewards))
    (hr : ActualReferenceInitializationBlock.BlockStartRelated source rewards
      C_star C_h rate (ReferenceInitializationRun.nextBlock b h) actual b past)
    (hdown : ∀ i, ¬ InitializationFailureProvenance.generatedBlockDown
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
      b h i)
    (hclean : ∀ (i : Fin (p.m - 1))
      (hi : ActualReferenceInitializationBlock.refFollower i ∈
        (ReferenceInitializationRun.physical
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
          b h).uninformed),
      BootstrapAllCandidateController.cleanPrefix
        (ReferenceInitializationRun.physical
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
          b h)
        source.1.2 ⟨ActualReferenceInitializationBlock.refFollower i, hi⟩
        (ActualInitializationPhysicalStep.selectedRowIndex p source) p.T)
    (hforce : ∀ i, ReferenceInitializationRun.forced
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
      b h i = false)
    (launch : BootstrapCoordinatorLocalRound.LaunchedBlock p)
    (learnerSeed : ActualInitializationRun.CoordinatorLearnerZeroSeed p)
    (hlaunched : (ActualInitializationRun.combinedBoundaryHandoff p rate
      (ReferenceInitializationRun.nextBlock b h) source rewards actual.C_star actual.C_h
      (ActualInitializationRun.foldBlock p rate (ReferenceInitializationRun.nextBlock b h)
        source rewards actual)).disposition = .launched launch learnerSeed) :
    ReferenceActivePhysicalStep.State p rate :=
  ActualInitializationLaunchState.ofActualLaunchedBoundary source rewards rate C_star C_h
    b h actual past hr hdown hclean hforce launch learnerSeed hlaunched

/-- The existing launch API proves the exact launch boundary is active for
every converted follower. -/
theorem actualLaunch_allActiveAtStart
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (rate : RateInput p) (C_star C_h : ℝ)
    (b : ReferenceInitializationRun.Boundary p)
    (h : b.completed < BootstrapDimensions.n_boot p)
    (actual : ActualInitializationRun.BlockCarry p rate
      (ReferenceInitializationRun.nextBlock b h))
    (past : List (ActualInitializationRun.PhysicalRoundRecord p rate source rewards))
    (hr : ActualReferenceInitializationBlock.BlockStartRelated source rewards
      C_star C_h rate (ReferenceInitializationRun.nextBlock b h) actual b past)
    (hdown : ∀ i, ¬ InitializationFailureProvenance.generatedBlockDown
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
      b h i)
    (hclean : ∀ (i : Fin (p.m - 1))
      (hi : ActualReferenceInitializationBlock.refFollower i ∈
        (ReferenceInitializationRun.physical
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
          b h).uninformed),
      BootstrapAllCandidateController.cleanPrefix
        (ReferenceInitializationRun.physical
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
          b h)
        source.1.2 ⟨ActualReferenceInitializationBlock.refFollower i, hi⟩
        (ActualInitializationPhysicalStep.selectedRowIndex p source) p.T)
    (hforce : ∀ i, ReferenceInitializationRun.forced
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
      b h i = false)
    (launch : BootstrapCoordinatorLocalRound.LaunchedBlock p)
    (learnerSeed : ActualInitializationRun.CoordinatorLearnerZeroSeed p)
    (hlaunched : (ActualInitializationRun.combinedBoundaryHandoff p rate
      (ReferenceInitializationRun.nextBlock b h) source rewards actual.C_star actual.C_h
      (ActualInitializationRun.foldBlock p rate (ReferenceInitializationRun.nextBlock b h)
        source rewards actual)).disposition = .launched launch learnerSeed) :
    ReferenceActivePhysicalHorizon.allActiveAtStart
      (actualLaunchState source rewards rate C_star C_h b h actual past hr hdown hclean hforce
        launch learnerSeed hlaunched)
      (BootstrapObservedFollower.blockStop p (ReferenceInitializationRun.nextBlock b h)) := by
  intro i
  exact ActualInitializationLaunchState.ofActualLaunchedBoundary_activation_le_blockStop
    source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed
    hlaunched i

/-- The seed facts returned by the actual launch replay theorem, packaged so
they can be passed directly to the prefix producer. -/
structure ActualLaunchSeedWitness
    (initial : ReferenceActivePhysicalStep.State p rate)
    (i : Fin (p.m - 1)) (start : ℕ) where
  state : ReferencePrelaunchFollower.State p rate.eta
  memory : ActiveFollowerLifecycle.LocalMemory p
  ordinary : initial.followers i = .ordinary state memory
  valid : ActiveFollowerLifecycle.localBufferValid state
  pairwise : state.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound)
  saved_before_start : ∀ saved ∈ state.buffer, saved.calendarRound ≤ start

/-- Select the concrete source-derived focal seed supplied by the actual-launch
replay result. -/
noncomputable def actualLaunchSeedWitness
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (rate : RateInput p) (C_star C_h : ℝ)
    (b : ReferenceInitializationRun.Boundary p)
    (h : b.completed < BootstrapDimensions.n_boot p)
    (actual : ActualInitializationRun.BlockCarry p rate
      (ReferenceInitializationRun.nextBlock b h))
    (past : List (ActualInitializationRun.PhysicalRoundRecord p rate source rewards))
    (hr : ActualReferenceInitializationBlock.BlockStartRelated source rewards
      C_star C_h rate (ReferenceInitializationRun.nextBlock b h) actual b past)
    (hdown : ∀ i, ¬ InitializationFailureProvenance.generatedBlockDown
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
      b h i)
    (hclean : ∀ (i : Fin (p.m - 1))
      (hi : ActualReferenceInitializationBlock.refFollower i ∈
        (ReferenceInitializationRun.physical
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
          b h).uninformed),
      BootstrapAllCandidateController.cleanPrefix
        (ReferenceInitializationRun.physical
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
          b h)
        source.1.2 ⟨ActualReferenceInitializationBlock.refFollower i, hi⟩
        (ActualInitializationPhysicalStep.selectedRowIndex p source) p.T)
    (hforce : ∀ i, ReferenceInitializationRun.forced
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
      b h i = false)
    (launch : BootstrapCoordinatorLocalRound.LaunchedBlock p)
    (learnerSeed : ActualInitializationRun.CoordinatorLearnerZeroSeed p)
    (hlaunched : (ActualInitializationRun.combinedBoundaryHandoff p rate
      (ReferenceInitializationRun.nextBlock b h) source rewards actual.C_star actual.C_h
      (ActualInitializationRun.foldBlock p rate (ReferenceInitializationRun.nextBlock b h)
        source rewards actual)).disposition = .launched launch learnerSeed)
    (i : Fin (p.m - 1)) :
    ActualLaunchSeedWitness
      (actualLaunchState source rewards rate C_star C_h b h actual past hr hdown hclean hforce
        launch learnerSeed hlaunched)
      i (BootstrapObservedFollower.blockStop p (ReferenceInitializationRun.nextBlock b h)) := by
  have hseedFacts := ReferenceFollowerBufferProvenance.actualLaunchedBoundary_follower_buffer_seed
    source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed
    hlaunched i
  have hnonempty : Nonempty (ActualLaunchSeedWitness
      (actualLaunchState source rewards rate C_star C_h b h actual past hr hdown hclean hforce
        launch learnerSeed hlaunched)
      i (BootstrapObservedFollower.blockStop p (ReferenceInitializationRun.nextBlock b h))) := by
    rcases hseedFacts with ⟨seed, seedMemory, hseed, hvalid, hpair, htime⟩
    exact ⟨⟨seed, seedMemory, hseed, hvalid, hpair, htime⟩⟩
  exact Classical.choice hnonempty

/-- At the actual launch boundary, the source-derived focal ordinary seed and
all of its buffer-safety conditions are outputs. Applying the general
producer then gives the actual prefix chronology and every DATA replacement
diagnostic. The count may be zero; the strict span ensures the current
coordinate is a genuine `Fin p.T` round, never a terminal sentinel. -/
theorem actualLaunchedBoundary_candidate_logging
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (rate : RateInput p) (C_star C_h : ℝ)
    (b : ReferenceInitializationRun.Boundary p)
    (h : b.completed < BootstrapDimensions.n_boot p)
    (actual : ActualInitializationRun.BlockCarry p rate
      (ReferenceInitializationRun.nextBlock b h))
    (past : List (ActualInitializationRun.PhysicalRoundRecord p rate source rewards))
    (hr : ActualReferenceInitializationBlock.BlockStartRelated source rewards
      C_star C_h rate (ReferenceInitializationRun.nextBlock b h) actual b past)
    (hdown : ∀ i, ¬ InitializationFailureProvenance.generatedBlockDown
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
      b h i)
    (hclean : ∀ (i : Fin (p.m - 1))
      (hi : ActualReferenceInitializationBlock.refFollower i ∈
        (ReferenceInitializationRun.physical
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
          b h).uninformed),
      BootstrapAllCandidateController.cleanPrefix
        (ReferenceInitializationRun.physical
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
          b h)
        source.1.2 ⟨ActualReferenceInitializationBlock.refFollower i, hi⟩
        (ActualInitializationPhysicalStep.selectedRowIndex p source) p.T)
    (hforce : ∀ i, ReferenceInitializationRun.forced
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
      b h i = false)
    (launch : BootstrapCoordinatorLocalRound.LaunchedBlock p)
    (learnerSeed : ActualInitializationRun.CoordinatorLearnerZeroSeed p)
    (hlaunched : (ActualInitializationRun.combinedBoundaryHandoff p rate
      (ReferenceInitializationRun.nextBlock b h) source rewards actual.C_star actual.C_h
      (ActualInitializationRun.foldBlock p rate (ReferenceInitializationRun.nextBlock b h)
        source rewards actual)).disposition = .launched launch learnerSeed)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (count : ℕ)
    (hspan : BootstrapObservedFollower.blockStop p (ReferenceInitializationRun.nextBlock b h) +
      (count + 1) ≤ p.T)
    (i : Fin (p.m - 1))
    (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
    (memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p)
    (ho : ∀ k,
      ((ReferenceActivePhysicalStep.prepare
        (candidateInput
          (actualLaunchState source rewards rate C_star C_h b h actual past hr hdown hclean hforce
            launch learnerSeed hlaunched)
          rows selected rewards
          (BootstrapObservedFollower.blockStop p (ReferenceInitializationRun.nextBlock b h))
          count hspan
          (actualLaunch_allActiveAtStart source rewards rate C_star C_h b h actual past hr hdown
            hclean hforce launch learnerSeed hlaunched))).followers.followers k).configuration =
              .ordinary (states k) (memories k))
    (hunoccupied : (states i).status = .unoccupied) :
    let seedWitness := actualLaunchSeedWitness source rewards rate C_star C_h b h actual past hr hdown hclean
      hforce launch learnerSeed hlaunched i
    (actualLaunchState source rewards rate C_star C_h b h actual past hr hdown hclean hforce
      launch learnerSeed hlaunched).followers i = .ordinary seedWitness.state seedWitness.memory ∧
    ActiveFollowerLifecycle.localBufferValid seedWitness.state ∧
    seedWitness.state.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) ∧
    (∀ saved ∈ seedWitness.state.buffer,
      saved.calendarRound ≤ BootstrapObservedFollower.blockStop p (ReferenceInitializationRun.nextBlock b h)) ∧
    candidateLoggingConclusion
      (initial := actualLaunchState source rewards rate C_star C_h b h actual past hr hdown hclean hforce
        launch learnerSeed hlaunched)
      (rows := rows) (selected := selected) (rewards := rewards)
      (start := BootstrapObservedFollower.blockStop p (ReferenceInitializationRun.nextBlock b h))
      (count := count) (hspan := hspan)
      (hmode := actualLaunch_allActiveAtStart source rewards rate C_star C_h b h actual past hr hdown
        hclean hforce launch learnerSeed hlaunched)
      (i := i)
      (seed := (actualLaunchSeedWitness source rewards rate C_star C_h b h actual past hr hdown hclean hforce
        launch learnerSeed hlaunched i).state)
      (states := states) := by
  let seedWitness := actualLaunchSeedWitness source rewards rate C_star C_h b h actual past hr hdown hclean
    hforce launch learnerSeed hlaunched i
  change (actualLaunchState source rewards rate C_star C_h b h actual past hr hdown hclean hforce
      launch learnerSeed hlaunched).followers i = .ordinary seedWitness.state seedWitness.memory ∧
    ActiveFollowerLifecycle.localBufferValid seedWitness.state ∧
    seedWitness.state.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) ∧
    (∀ saved ∈ seedWitness.state.buffer,
      saved.calendarRound ≤ BootstrapObservedFollower.blockStop p (ReferenceInitializationRun.nextBlock b h)) ∧
    candidateLoggingConclusion
      (initial := actualLaunchState source rewards rate C_star C_h b h actual past hr hdown hclean hforce
        launch learnerSeed hlaunched)
      (rows := rows) (selected := selected) (rewards := rewards)
      (start := BootstrapObservedFollower.blockStop p (ReferenceInitializationRun.nextBlock b h))
      (count := count) (hspan := hspan)
      (hmode := actualLaunch_allActiveAtStart source rewards rate C_star C_h b h actual past hr hdown
        hclean hforce launch learnerSeed hlaunched)
      (i := i) (seed := seedWitness.state) (states := states)
  refine ⟨seedWitness.ordinary, seedWitness.valid, seedWitness.pairwise,
    seedWitness.saved_before_start, ?_⟩
  exact continuing_data_candidate_logging
    (initial := actualLaunchState source rewards rate C_star C_h b h actual past hr hdown hclean hforce
      launch learnerSeed hlaunched)
    (rows := rows) (selected := selected) (rewards := rewards)
    (start := BootstrapObservedFollower.blockStop p (ReferenceInitializationRun.nextBlock b h))
    (count := count) (hspan := hspan)
    (hmode := actualLaunch_allActiveAtStart source rewards rate C_star C_h b h actual past hr hdown
      hclean hforce launch learnerSeed hlaunched)
    (i := i)
    (seed := seedWitness.state)
    (seedMemory := seedWitness.memory)
    (hseed := seedWitness.ordinary)
    (hseedValid := seedWitness.valid)
    (hseedPairwise := seedWitness.pairwise)
    (hseedTime := seedWitness.saved_before_start)
    (states := states) (memories := memories) (ho := ho) (hunoccupied := hunoccupied)

end Bandits.Support.ReferenceContinuingDataCandidateLogging

end
